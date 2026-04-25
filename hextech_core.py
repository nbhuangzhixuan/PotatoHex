#!/usr/bin/env python3
"""
PotatoHex - 简化版
功能：
1. 检测英雄联盟大厅进程
2. 检测游戏启动
3. 基于模板匹配检测海克斯选择页面
4. 识别到海克斯后显示浮窗，按匹配度排名
"""
import os
import sys
import time
import io
import re
import json
import html
import ctypes
import subprocess
import threading
import traceback
import tempfile
import difflib
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk
from ctypes import wintypes
import cv2
import numpy as np
from PIL import Image, ImageGrab, ImageTk
import requests
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)


_CREATE_NO_WINDOW = 0x08000000 if os.name == "nt" else 0


def _hidden_subprocess_kwargs():
    kwargs = {}
    if os.name == "nt":
        kwargs["creationflags"] = _CREATE_NO_WINDOW
        startupinfo = subprocess.STARTUPINFO()
        startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        kwargs["startupinfo"] = startupinfo
    return kwargs


def _enable_dpi_awareness():
    """Make Windows return physical pixels for window bounds on HiDPI displays."""
    if os.name != "nt":
        return
    try:
        user32 = ctypes.windll.user32
        # Prefer the per-monitor v2 context when available.
        try:
            awareness = ctypes.c_void_p(-4)
            user32.SetProcessDpiAwarenessContext(awareness)
            return
        except Exception:
            pass
        try:
            shcore = ctypes.windll.shcore
            shcore.SetProcessDpiAwareness(2)
            return
        except Exception:
            pass
        try:
            user32.SetProcessDPIAware()
        except Exception:
            pass
    except Exception:
        pass


_enable_dpi_awareness()


def _app_base_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


APP_BASE_DIR = _app_base_dir()
RESOURCE_DIR = getattr(sys, "_MEIPASS", APP_BASE_DIR)


LOG_FILE_NAME = "hextech_assistant.log"
_LOG_FILE_HANDLE = None
_STATUS_LOG_CACHE = {}
_LCU_PROBE_CACHE = {}
_OCR_CARD_TEXT_STICKY_CACHE = {"values": ["", "", ""], "ts": 0.0}
_ACTIVE_SCROLL_CANVAS = None
LCU_PROCESS_NAMES = {
    "leagueclientux.exe",
    "leagueclient.exe",
    "leagueclientuxrender.exe",
}
GAME_PROCESS_NAMES = {
    "league of legends.exe",
    "league of legends(tm) client.exe",
    "league of legends tm client.exe",
}

HEXTECH_CACHE_FILE_NAME = "hextech_reco_cache.json"
HEXTECH_AUGMENT_INDEX_FILE_NAME = "hextech_augment_index.json"
APEX_BASE_URL = "https://apexlol.info"
APEX_CHAMPIONS_INDEX_URL = f"{APEX_BASE_URL}/zh/champions/"
HEXTECH_INDEX_REFRESH_INTERVAL = 12 * 60 * 60
HEXTECH_CHAMPION_REFRESH_INTERVAL = 6 * 60 * 60
HEXTECH_UPDATE_LOOP_INTERVAL = 2
HEXTECH_HTTP_TIMEOUT = 12
HEXTECH_STRONG_ONLY = True
HEXTECH_TIER_FILTER_ENABLED = True
HEXTECH_FETCH_ONLY_IF_MISSING = True
HEXTECH_MATCH_THRESHOLD = 0.18
HEXTECH_OCR_ONLY = True
HEXTECH_OCR_DEBUG_DIR = "ocr_debug"
HEXTECH_OCR_SAVE_CROPS = False
HEXTECH_OCR_GLOBAL_MATCH_RATIO = 0.56
HEXTECH_PREFETCH_ALL_AUGMENTS_ON_START = False
HEXTECH_OVERLAY_TOP_N = 8
HEXTECH_CHAMP_PREVIEW_TOP_N = 8
HEXTECH_ROI_DETECT_MIN_HITS = 2
HEXTECH_ROI_TEXT_SCORE_THRESHOLD = 6.2
HEXTECH_OCR_TEXT_STICKY_SECONDS = 2.8
HEXTECH_MAIN_LOOP_INTERVAL = 1.5
HEXTECH_IN_GAME_MAIN_LOOP_INTERVAL = 0.8
HEXTECH_HOTKEY_POLL_INTERVAL = 0.03
HEXTECH_ACTIVE_LOOP_INTERVAL = 0.4
HEXTECH_ACTIVE_OCR_REFRESH_INTERVAL = 0.5
HEXTECH_CLOSE_GRACE_SECONDS = 1.2
HEXTECH_CLOSE_MISS_LIMIT = 2
HEXTECH_PARSE_SCHEMA_VERSION = 3
HEXTECH_MANUAL_TRIGGER_VKS = (0xDC, 0xE2)
HEXTECH_MANUAL_TRIGGER_SCANCODES = (0x2B, 0x56)
HEXTECH_MANUAL_TRIGGER_NAME = "\\ 键"
HEXTECH_MANUAL_TRIGGER_COOLDOWN = 0.8
# OCR ROI tuning ratios (relative to full screenshot)
HEXTECH_CARD_PANEL_X1_RATIO = 0.04
HEXTECH_CARD_PANEL_X2_RATIO = 0.96
HEXTECH_CARD_PANEL_Y1_RATIO = 0.02
HEXTECH_CARD_PANEL_Y2_RATIO = 0.92

# Name band ratios (relative to the panel)
HEXTECH_NAME_BAND_Y1_RATIO = 0.39
HEXTECH_NAME_BAND_Y2_RATIO = 0.44
HEXTECH_NAME_BAND_X_MARGIN_RATIO = 0.37
HEXTECH_CARD_GAP_RATIO = -0.40


def normalize_name_key(value):
    if not value:
        return ""
    return re.sub(r"\s+", "", str(value)).strip().lower()


def chinese_to_slug_key(value):
    """Best-effort mapping for LCU Chinese champion names -> apexlol slug keys."""
    mapping = {
        "雪原双子": "Nunu",
        "虚空之女": "Kaisa",
        "荒漠屠夫": "Renekton",
        "披甲龙龟": "Rammus",
        "扭曲树精": "Maokai",
        "复仇焰魂": "Brand",
        "法外狂徒": "Graves",
        "符文法师": "Ryze",
        "无双剑姬": "Fiora",
        "德玛西亚皇子": "JarvanIV",
        "齐天大圣": "MonkeyKing",
        "虚空遁地兽": "RekSai",
        "远古恐惧": "Fiddlesticks",
        "河流之王": "TahmKench",
        "万花通灵": "Neeko",
        "铸星龙王": "AurelionSol",
        "不灭狂雷": "Volibear",
        "含羞蓓蕾": "Briar",
    }
    slug = mapping.get(str(value).strip())
    return normalize_name_key(slug) if slug else ""


def strip_html_to_text_lines(html_content):
    if not html_content:
        return []
    text = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", html_content)
    text = re.sub(r"(?is)<br\s*/?>", "\n", text)
    text = re.sub(r"(?is)</(p|div|li|h1|h2|h3|h4|h5|h6|tr|td|section|article)>", "\n", text)
    text = re.sub(r"(?is)<[^>]+>", " ", text)
    text = html.unescape(text)
    lines = []
    for line in text.splitlines():
        cleaned = re.sub(r"\s+", " ", line).strip()
        if cleaned:
            lines.append(cleaned)
    return lines


_DATETIME_RE = re.compile(r"^\d{4}/\d{1,2}/\d{1,2}(?:\s+\d{1,2}:\d{2})?$")


def is_aug_name_like(text):
    if not text:
        return False
    t = text.strip()
    if len(t) < 2 or len(t) > 26:
        return False
    if _DATETIME_RE.match(t):
        return False
    if re.match(r"^\d{1,2}:\d{2}$", t):
        return False
    if re.search(r"(?:\d{4}[/.-])|(?:\d{1,2}:\d{2})", t):
        return False
    return True


def contains_cjk(text):
    return bool(re.search(r"[\u4e00-\u9fff]", text or ""))


def is_virtual_key_down(vk_code):
    if os.name != "nt":
        return False
    try:
        return bool(ctypes.windll.user32.GetAsyncKeyState(int(vk_code)) & 0x8000)
    except Exception:
        return False


def is_any_virtual_key_down(vk_codes):
    for vk_code in vk_codes or []:
        if is_virtual_key_down(vk_code):
            return True
    return False


if os.name == "nt" and not hasattr(wintypes, "ULONG_PTR"):
    wintypes.ULONG_PTR = wintypes.WPARAM
if os.name == "nt" and not hasattr(wintypes, "LRESULT"):
    wintypes.LRESULT = ctypes.c_ssize_t


HEXTECH_MANUAL_TRIGGER_VK_SET = set(int(v) for v in HEXTECH_MANUAL_TRIGGER_VKS)
HEXTECH_MANUAL_TRIGGER_SCANCODE_SET = set(int(v) for v in HEXTECH_MANUAL_TRIGGER_SCANCODES)


class KBDLLHOOKSTRUCT(ctypes.Structure):
    _fields_ = [
        ("vkCode", wintypes.DWORD),
        ("scanCode", wintypes.DWORD),
        ("flags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", wintypes.ULONG_PTR),
    ]


def is_manual_trigger_key(vk_code=None, scan_code=None):
    try:
        if vk_code is not None and int(vk_code) in HEXTECH_MANUAL_TRIGGER_VK_SET:
            return True
    except Exception:
        pass
    try:
        if scan_code is not None and int(scan_code) in HEXTECH_MANUAL_TRIGGER_SCANCODE_SET:
            return True
    except Exception:
        pass
    return False


def is_running_as_admin():
    if os.name != "nt":
        return False
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def is_likely_augment_name(text):
    if not is_aug_name_like(text):
        return False
    t = (text or "").strip()
    if not contains_cjk(t):
        return False
    if len(t) > 12:
        return False
    low = t.lower()
    noise_tokens = ["强力联动", "娱乐", "陷阱", "bug", "作者", "评分", "标签", "版本"]
    return not any(token in low for token in noise_tokens)


def is_clean_augment_name_line(text):
    """Stricter augment-name line filter for web text parsing."""
    if not is_likely_augment_name(text):
        return False
    t = (text or "").strip()
    if len(t) > 12:
        return False
    # Narrative lines usually contain punctuation/percent markers.
    bad_tokens = ["。", "，", "、", "%", "http", "://", "作者", "推荐出装", "技能加点", "召唤师技能", "对局胜率"]
    low = t.lower()
    if any(tok in t for tok in bad_tokens if tok not in {"http", "://"}):
        return False
    if "http" in low or "://" in low:
        return False
    return True


_GRADE_RANK = {"SSS": 0, "SS": 1, "S": 2, "A": 3, "B": 4, "C": 5, "D": 6}


def grade_rank_value(grade):
    return _GRADE_RANK.get(str(grade or "").upper(), 99)


def extract_combo_names_from_note(note_text, pool_names, self_name=None, max_count=3):
    note_key = normalize_name_key(note_text)
    if not note_key:
        return []
    self_key = normalize_name_key(self_name)
    combos = []
    seen = set()
    # Longer names first to reduce short-substring false hits.
    for nm in sorted([str(x).strip() for x in (pool_names or []) if str(x).strip()], key=len, reverse=True):
        k = normalize_name_key(nm)
        if not k or k == self_key or k in seen:
            continue
        if k in note_key:
            combos.append(nm)
            seen.add(k)
            if len(combos) >= max_count:
                break
    return combos


def dedupe_best_recos_by_name(rows):
    by_name = {}
    for r in (rows or []):
        nm = str((r or {}).get("name", "")).strip()
        if not nm:
            continue
        key = normalize_name_key(nm)
        score = int((r or {}).get("score", 0) or 0)
        grade = str((r or {}).get("grade", "")).upper()
        tags = str((r or {}).get("tags", "")).strip()
        # Hard rule: for same augment name, "强力联动" variant wins first.
        is_strong = 1 if "强力联动" in tags else 0
        tie = (
            is_strong,
            -grade_rank_value(grade),
            score,
            len(str((r or {}).get("note", "")).strip()),
        )
        old = by_name.get(key)
        if old is None or tie > old[0]:
            by_name[key] = (tie, dict(r))
    return [v[1] for v in by_name.values()]


def build_preview_rows_with_combos(all_rows, top_n=8):
    dedup = dedupe_best_recos_by_name(all_rows or [])
    if not dedup:
        return []
    # Preserve original row order from the provider as much as possible.
    dedup.sort(
        key=lambda x: (
            int(x.get("website_rank", 9999) or 9999),
            -int(x.get("score", 0) or 0),
        )
    )
    pool_names = [str(x.get("name", "")).strip() for x in dedup if str(x.get("name", "")).strip()]
    out = []
    for r in dedup:
        nm = str(r.get("name", "")).strip()
        note = str(r.get("note", "")).strip()
        combos = extract_combo_names_from_note(note, pool_names, self_name=nm, max_count=3)
        row = dict(r)
        row["combo_text"] = " + ".join(combos) if combos else ""
        row["_combo_count"] = len(combos)
        out.append(row)
    out.sort(key=lambda x: (int(x.get("website_rank", 9999) or 9999), -int(x.get("score", 0) or 0)))
    return out[:max(1, int(top_n or 8))]


def _extract_real_items_from_text(text, max_count=4):
    """
    Match real item names from free text using Data Dragon item dictionary.
    Returns ordered item name list.
    """
    if not text:
        return []
    tk = normalize_name_key(text)
    if not tk:
        return []
    found = []
    seen = set()
    for chunk in re.split(r"[+、,/|·\s]+", str(text)):
        n = chunk.strip()
        nk = normalize_name_key(n)
        if not nk or nk in seen:
            continue
        seen.add(nk)
        found.append(n)
        if len(found) >= max_count:
            break
    return found


def build_items_for_row(base_row, all_rows, max_count=4):
    """
    Build item list for display:
    1) trusted direct item names in row.items
    2) parse from row.note
    3) parse from combo rows' notes
    """
    result = []
    seen = set()

    def _push(name):
        n = str(name or "").strip()
        if not n:
            return
        nk = normalize_name_key(n)
        if nk in seen:
            return
        seen.add(nk)
        result.append(n)

    # 1) direct item list
    for it in (base_row.get("items") or []):
        n = str(it).strip()
        _push(n)
        if len(result) >= max_count:
            return result[:max_count]

    # 2) parse from own note
    for n in _extract_real_items_from_text(base_row.get("note", ""), max_count=max_count):
        _push(n)
        if len(result) >= max_count:
            return result[:max_count]

    # 3) parse from combo rows
    combo_names = [x.strip() for x in str(base_row.get("combo_text", "")).split("+") if x.strip()]
    if combo_names:
        by_name = {normalize_name_key(str(r.get("name", ""))): r for r in (all_rows or [])}
        for cn in combo_names:
            rr = by_name.get(normalize_name_key(cn))
            if not rr:
                continue
            for n in _extract_real_items_from_text(rr.get("note", ""), max_count=max_count):
                _push(n)
                if len(result) >= max_count:
                    return result[:max_count]
            for it in (rr.get("items") or []):
                _push(it)
                if len(result) >= max_count:
                    return result[:max_count]

    return result[:max_count]


def build_scrollable_combo_box(parent, bg, accent, title_text, side="top"):
    outer = tk.Frame(
        parent,
        bg=bg,
        highlightbackground=accent,
        highlightthickness=1,
        padx=8,
        pady=6,
    )
    outer.pack(side=side, fill="x", expand=False, pady=(0, 6), padx=8)
    outer.pack_propagate(False)

    tk.Label(
        outer,
        text=title_text,
        bg=bg,
        fg="#dff3ff",
        font=("Microsoft YaHei", 11, "bold"),
        anchor="w",
    ).pack(fill="x", pady=(0, 4))

    body = tk.Frame(outer, bg=bg)
    body.pack(fill="both", expand=True, pady=(4, 0))
    canvas = tk.Canvas(body, bg=bg, highlightthickness=0, bd=0)
    scrollbar = ttk.Scrollbar(body, orient="vertical", command=canvas.yview)
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True)
    inner = tk.Frame(canvas, bg=bg)
    window_id = canvas.create_window((0, 0), window=inner, anchor="nw")

    def _sync_scrollbar_visibility():
        try:
            bbox = canvas.bbox("all")
            content_height = (bbox[3] - bbox[1]) if bbox else 0
            viewport_height = max(1, int(canvas.winfo_height() or 0))
            needs_scroll = content_height > (viewport_height + 2)
            if needs_scroll and not scrollbar.winfo_ismapped():
                scrollbar.pack(side="right", fill="y")
            elif (not needs_scroll) and scrollbar.winfo_ismapped():
                scrollbar.pack_forget()
        except Exception:
            pass

    def _sync_region(_event=None):
        try:
            canvas.configure(scrollregion=canvas.bbox("all"))
            _sync_scrollbar_visibility()
        except Exception:
            pass

    def _sync_width(event):
        try:
            canvas.itemconfigure(window_id, width=event.width)
            canvas.after_idle(_sync_scrollbar_visibility)
        except Exception:
            pass

    def _is_inside(widget):
        cur = widget
        while cur is not None:
            if cur is outer or cur is body or cur is canvas or cur is inner or cur is scrollbar:
                return True
            cur = getattr(cur, "master", None)
        return False

    def _wheel(event):
        try:
            if not _is_inside(getattr(event, "widget", None)):
                return
            delta = 0
            if hasattr(event, "delta") and event.delta:
                delta = -1 * int(event.delta / 120)
            elif getattr(event, "num", None) == 4:
                delta = -1
            elif getattr(event, "num", None) == 5:
                delta = 1
            if delta:
                canvas.yview_scroll(delta, "units")
        except Exception:
            pass

    inner.bind("<Configure>", _sync_region)
    canvas.bind("<Configure>", _sync_width)
    canvas.bind_all("<MouseWheel>", _wheel, add="+")
    canvas.bind_all("<Button-4>", _wheel, add="+")
    canvas.bind_all("<Button-5>", _wheel, add="+")
    return outer, inner


class ApexHextechProvider:
    def __init__(self, cache_path, augment_index_path=None):
        self.cache_path = cache_path
        self.augment_index_path = augment_index_path or os.path.join(
            os.path.dirname(os.path.abspath(cache_path)),
            HEXTECH_AUGMENT_INDEX_FILE_NAME,
        )
        self._lock = threading.Lock()
        self._stop_event = threading.Event()
        self._refresh_pending = set()
        self._data = {
            "meta": {
                "source": "apexlol.info",
                "last_index_refresh": 0,
                "last_data_refresh": 0,
                "parse_schema_version": HEXTECH_PARSE_SCHEMA_VERSION,
            },
            "slug_map": {},
            "name_to_slug": {},
            "champions": {},
        }
        self._augment_index = {
            "meta": {"source": "apexlol.info", "updated_at": 0},
            "items": {},
        }
        self._load_cache()
        self._load_augment_index()
        with self._lock:
            if not self._augment_index.get("items"):
                self._rebuild_augment_index_locked()
                self._save_augment_index_locked()

    def start(self):
        t = threading.Thread(target=self._update_loop, daemon=True)
        t.start()
        self.request_refresh(force_index=True)

    def stop(self):
        self._stop_event.set()

    def get_recommendations(self, champion_name, limit=6):
        return self.get_recommendations_for_tier(champion_name, tier=None, limit=limit)

    def _resolve_slug_locked(self, champion_name):
        if not champion_name:
            return None, None
        alias_key = ""
        display_name = champion_name
        if "|" in champion_name:
            left, right = champion_name.split("|", 1)
            display_name = left.strip() or champion_name
            alias_key = normalize_name_key(right)
        champion_key = normalize_name_key(display_name)
        slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
        if not slug:
            slug = self._data["name_to_slug"].get(champion_key)
        if not slug:
            slug = self._data["name_to_slug"].get(chinese_to_slug_key(display_name))
        return slug, display_name

    def has_champion_data(self, champion_name):
        with self._lock:
            slug, _ = self._resolve_slug_locked(champion_name)
            if not slug:
                return False
            entry = self._data.get("champions", {}).get(slug)
            return bool(entry and entry.get("recommendations"))

    def get_recommendations_for_tier(self, champion_name, tier=None, limit=6):
        tiers = {tier} if tier else None
        return self.get_recommendations_for_tiers(champion_name, tiers=tiers, limit=limit)

    def get_recommendations_for_tiers(self, champion_name, tiers=None, limit=6):
        if not champion_name or champion_name.startswith("ID:") or champion_name == "__no_cred__":
            return [{
                "name": "等待选中英雄...",
                "tier": "白银",
                "score": 0,
                "tags": "状态",
                "note": "当前未获取到可用英雄",
            }]

        alias_key = ""
        display_name = champion_name
        if "|" in champion_name:
            left, right = champion_name.split("|", 1)
            display_name = left.strip() or champion_name
            alias_key = normalize_name_key(right)

        champion_key = normalize_name_key(display_name)
        now = time.time()
        with self._lock:
            slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
            if not slug:
                slug = self._data["name_to_slug"].get(champion_key)
            if not slug:
                slug = self._data["name_to_slug"].get(chinese_to_slug_key(display_name))
            entry = self._data["champions"].get(slug) if slug else None
            if entry and entry.get("recommendations"):
                updated_at = float(entry.get("updated_at", 0))
                if (not HEXTECH_FETCH_ONLY_IF_MISSING) and (now - updated_at > HEXTECH_CHAMPION_REFRESH_INTERVAL):
                    self._refresh_pending.add(champion_name)
                recos = entry["recommendations"]
                all_recos = list(recos)
                strong_recos = [x for x in all_recos if "强力联动" in str(x.get("tags", ""))]
                filtered = strong_recos if (HEXTECH_STRONG_ONLY and strong_recos) else all_recos

                normalized_tiers = set()
                if tiers:
                    normalized_tiers = {t for t in tiers if t in {"棱彩", "黄金", "白银"}}

                if HEXTECH_TIER_FILTER_ENABLED and normalized_tiers:
                    tier_filtered = [x for x in filtered if str(x.get("tier", "")) in normalized_tiers]
                    if tier_filtered:
                        filtered = tier_filtered
                    else:
                        # fallback chain to avoid empty overlay
                        tier_all = [x for x in all_recos if str(x.get("tier", "")) in normalized_tiers]
                        if tier_all:
                            filtered = tier_all
                        elif strong_recos:
                            filtered = strong_recos
                        else:
                            filtered = all_recos

                return filtered[:limit]

            self._refresh_pending.add(champion_name)

        return [{
            "name": f"{display_name} 数据加载中",
            "tier": "白银",
            "score": 0,
            "tags": "加载中",
            "note": "正在后台抓取该英雄海克斯推荐",
        }]

    def request_refresh(self, champion_name=None, force_index=False):
        with self._lock:
            if force_index:
                self._data["meta"]["last_index_refresh"] = 0
            if champion_name:
                self._refresh_pending.add(champion_name)

    def get_champion_recommendation_pool(self, champion_name):
        """Return raw parsed recommendations for a champion (all tiers, unfiltered)."""
        if not champion_name:
            return []
        alias_key = ""
        display_name = champion_name
        if "|" in champion_name:
            left, right = champion_name.split("|", 1)
            display_name = left.strip() or champion_name
            alias_key = normalize_name_key(right)

        champion_key = normalize_name_key(display_name)
        with self._lock:
            slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
            if not slug:
                slug = self._data["name_to_slug"].get(champion_key)
            if not slug:
                slug = self._data["name_to_slug"].get(chinese_to_slug_key(display_name))
            entry = self._data["champions"].get(slug) if slug else None
            recos = entry.get("recommendations", []) if entry else []
            return list(recos)

    def get_reco_by_augment_name(self, champion_name, augment_name):
        """Fuzzy match augment name in local champion cache and return reco row."""
        if not champion_name or not augment_name:
            return None
        pool = self.get_champion_recommendation_pool(champion_name)
        if not pool:
            return None
        q = normalize_name_key(augment_name)
        if not q:
            return None
        # Hard rule: exact same augment name prefers "强力联动" tagged row.
        exact_rows = []
        for item in pool:
            nm = str(item.get("name", "")).strip()
            nn = normalize_name_key(nm)
            if nn == q:
                exact_rows.append(item)
        if exact_rows:
            exact_rows.sort(
                key=lambda x: (
                    1 if "强力联动" in str(x.get("tags", "")) else 0,
                    -grade_rank_value(str(x.get("grade", "")).upper()),
                    int(x.get("score", 0) or 0),
                ),
                reverse=True,
            )
            return dict(exact_rows[0])
        best_ratio = 0.0
        best = None
        for item in pool:
            nm = str(item.get("name", "")).strip()
            nn = normalize_name_key(nm)
            if not nn:
                continue
            ratio = difflib.SequenceMatcher(None, q, nn).ratio()
            if q in nn or nn in q:
                ratio = min(1.0, ratio + 0.12)
            if ratio > best_ratio:
                best_ratio = ratio
                best = item
        if best and best_ratio >= 0.52:
            return dict(best)
        return None

    def should_try_items_backfill(self, champion_name):
        """Whether this champion entry should be refreshed once to fill `items` field."""
        with self._lock:
            slug, _ = self._resolve_slug_locked(champion_name)
            if not slug:
                return False
            entry = self._data.get("champions", {}).get(slug) or {}
            recos = entry.get("recommendations", []) or []
            if not recos:
                return False
            if entry.get("items_backfill_checked"):
                return False
            has_any_items = any(bool(r.get("items")) for r in recos)
            return not has_any_items

    def should_refresh_due_to_parse_upgrade(self, champion_name):
        """Refresh champion once when parser schema has upgraded."""
        with self._lock:
            slug, _ = self._resolve_slug_locked(champion_name)
            if not slug:
                return False
            entry = (self._data.get("champions", {}) or {}).get(slug) or {}
            recos = entry.get("recommendations", []) or []
            if not recos:
                return False
            ver = int(entry.get("parse_schema_version", 0) or 0)
            return ver < HEXTECH_PARSE_SCHEMA_VERSION

    def get_global_augment_index(self):
        with self._lock:
            items = self._augment_index.get("items", {})
            return {k: {"name": v.get("name", ""), "tiers": list(v.get("tiers", []))} for k, v in items.items()}

    def prefetch_all_champions(self):
        """Smart prefetch: only fetch champions missing local recommendations."""
        with self._lock:
            slug_list = list(self._data.get("slug_map", {}).keys())
        if not slug_list:
            self._refresh_index()
            with self._lock:
                slug_list = list(self._data.get("slug_map", {}).keys())
        if not slug_list:
            print("[Hextech] 全量预抓取失败：英雄索引为空")
            return

        need_fetch = []
        with self._lock:
            champions = self._data.get("champions", {}) or {}
            for slug in slug_list:
                entry = champions.get(slug) or {}
                recos = entry.get("recommendations", []) or []
                parse_ver = int(entry.get("parse_schema_version", 0) or 0)
                if (not recos) or (parse_ver < HEXTECH_PARSE_SCHEMA_VERSION):
                    need_fetch.append(slug)

        total_all = len(slug_list)
        total_need = len(need_fetch)
        if total_need == 0:
            print(f"[Hextech] 本地数据完整，无需更新（{total_all} 个英雄）")
            return

        print(f"[Hextech] 智能补全启动: 总英雄={total_all}, 需更新={total_need}")
        ok_count = 0
        for i, slug in enumerate(need_fetch, 1):
            try:
                before = 0
                with self._lock:
                    old_entry = self._data.get("champions", {}).get(slug, {})
                    before = len(old_entry.get("recommendations", []) or [])
                self._refresh_champion_by_slug(slug, requested_name=None)
                with self._lock:
                    new_entry = self._data.get("champions", {}).get(slug, {})
                    after = len(new_entry.get("recommendations", []) or [])
                if after > 0 or before > 0:
                    ok_count += 1
                if i % 20 == 0 or i == total_need:
                    print(f"[Hextech] 智能补全进度: {i}/{total_need}, 有效={ok_count}")
            except Exception as e:
                log_status(f"hextech_prefetch_error_{slug}", f"[Hextech] 预抓取失败: {slug}, error={e}", interval=120)

        with self._lock:
            self._rebuild_augment_index_locked()
            self._save_cache_locked()
            self._save_augment_index_locked()
            aug_count = len(self._augment_index.get("items", {}))
        print(f"[Hextech] 全局海克斯索引已生成: {aug_count} 个海克斯名")

    def _update_loop(self):
        while not self._stop_event.is_set():
            try:
                self._run_update_cycle()
            except Exception as e:
                log_status("hextech_update_loop_error", f"[Hextech] 更新线程异常: {e}", interval=15)
            time.sleep(HEXTECH_UPDATE_LOOP_INTERVAL)

    def _run_update_cycle(self):
        now = time.time()
        with self._lock:
            last_index_refresh = float(self._data["meta"].get("last_index_refresh", 0))
        if now - last_index_refresh >= HEXTECH_INDEX_REFRESH_INTERVAL:
            self._refresh_index()

        with self._lock:
            pending = list(self._refresh_pending)
            self._refresh_pending.clear()

        if not pending:
            return

        for champion_name in pending:
            self._refresh_champion_by_name(champion_name)

    def _load_cache(self):
        if not os.path.exists(self.cache_path):
            return
        try:
            with open(self.cache_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                with self._lock:
                    self._data.update({
                        "meta": data.get("meta", self._data["meta"]),
                        "slug_map": data.get("slug_map", {}),
                        "name_to_slug": data.get("name_to_slug", {}),
                        "champions": data.get("champions", {}),
                    })
                    if not isinstance(self._data.get("meta"), dict):
                        self._data["meta"] = {}
                    self._data["meta"]["parse_schema_version"] = HEXTECH_PARSE_SCHEMA_VERSION
                print(f"[Hextech] 已加载本地缓存: {self.cache_path}")
        except Exception as e:
            print(f"[Hextech] 加载缓存失败: {e}")

    def _load_augment_index(self):
        if not os.path.exists(self.augment_index_path):
            return
        try:
            with open(self.augment_index_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict) and isinstance(data.get("items"), dict):
                with self._lock:
                    self._augment_index = data
                print(f"[Hextech] 已加载海克斯全局索引: {self.augment_index_path}")
        except Exception as e:
            print(f"[Hextech] 加载海克斯全局索引失败: {e}")

    def _save_cache_locked(self):
        tmp_path = self.cache_path + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(self._data, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, self.cache_path)

    def _save_augment_index_locked(self):
        tmp_path = self.augment_index_path + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(self._augment_index, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, self.augment_index_path)

    def _rebuild_augment_index_locked(self):
        items = {}
        champions = self._data.get("champions", {}) or {}
        for entry in champions.values():
            recos = entry.get("recommendations", []) or []
            for r in recos:
                name = str(r.get("name", "")).strip()
                tier = str(r.get("tier", "")).strip()
                if not name or tier not in {"棱彩", "黄金", "白银"}:
                    continue
                if not is_likely_augment_name(name):
                    continue
                key = normalize_name_key(name)
                row = items.setdefault(key, {"name": name, "tiers": set()})
                row["tiers"].add(tier)

        norm_items = {}
        for key, row in items.items():
            tiers = sorted(list(row["tiers"]))
            norm_items[key] = {"name": row["name"], "tiers": tiers}

        self._augment_index = {
            "meta": {
                "source": "apexlol.info",
                "updated_at": time.time(),
            },
            "items": norm_items,
        }

    def _http_get(self, url):
        headers = {
            "User-Agent": "hextech-assistant/1.0 (+local cache updater)",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        }
        for attempt in range(2):
            try:
                resp = requests.get(url, headers=headers, timeout=HEXTECH_HTTP_TIMEOUT)
                if resp.status_code == 200:
                    # Some environments mis-detect encoding and break Chinese keyword parsing.
                    try:
                        resp.encoding = resp.apparent_encoding or "utf-8"
                    except Exception:
                        resp.encoding = "utf-8"
                    text = resp.text
                    if text and not re.search(r"[\u4e00-\u9fff]", text):
                        try:
                            raw = resp.content.decode("utf-8", errors="replace")
                            if re.search(r"[\u4e00-\u9fff]", raw):
                                text = raw
                        except Exception:
                            pass
                    return text
                log_status(
                    "hextech_http_fail",
                    f"[Hextech] 抓取失败: {url}, HTTP {resp.status_code}",
                    interval=15,
                )
            except Exception as e:
                if attempt == 1:
                    log_status("hextech_http_error", f"[Hextech] 抓取异常: {url}, error={e}", interval=15)
        return None

    def _refresh_index(self):
        html_content = self._http_get(APEX_CHAMPIONS_INDEX_URL)
        if not html_content:
            return

        pattern = re.compile(
            r'<a[^>]+href=["\'](/zh/champions/([^"\'/?#]+))/?["\'][^>]*>(.*?)</a>',
            re.IGNORECASE | re.DOTALL,
        )
        slug_map = {}
        name_to_slug = {}

        for rel_path, slug, inner in pattern.findall(html_content):
            if not slug:
                continue
            abs_url = APEX_BASE_URL + rel_path
            slug_map[slug] = abs_url
            name_to_slug[normalize_name_key(slug)] = slug

            anchor_text = re.sub(r"(?is)<[^>]+>", " ", inner)
            anchor_text = html.unescape(anchor_text)
            anchor_text = re.sub(r"\s+", " ", anchor_text).strip()
            if anchor_text and len(anchor_text) <= 24 and "Image" not in anchor_text:
                name_to_slug[normalize_name_key(anchor_text)] = slug

        if not slug_map:
            return

        with self._lock:
            self._data["slug_map"] = slug_map
            self._data["name_to_slug"].update(name_to_slug)
            self._data["meta"]["last_index_refresh"] = time.time()
            self._save_cache_locked()
        print(f"[Hextech] 英雄索引已更新: {len(slug_map)} 个条目")

    def _refresh_champion_by_name(self, champion_name):
        if not champion_name:
            return

        alias_key = ""
        display_name = champion_name
        if "|" in champion_name:
            left, right = champion_name.split("|", 1)
            display_name = left.strip() or champion_name
            alias_key = normalize_name_key(right)

        champion_key = normalize_name_key(display_name)
        with self._lock:
            slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
            if not slug:
                slug = self._data["name_to_slug"].get(champion_key)
            if not slug:
                slug = self._data["name_to_slug"].get(chinese_to_slug_key(display_name))

        if not slug:
            self._refresh_index()
            with self._lock:
                slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
                if not slug:
                    slug = self._data["name_to_slug"].get(champion_key)
                if not slug:
                    slug = self._data["name_to_slug"].get(chinese_to_slug_key(display_name))

        if not slug:
            log_status(
                f"hextech_slug_missing_{champion_key}",
                f"[Hextech] 未在索引中匹配到英雄: {display_name}",
                interval=60,
            )
            return

        self._refresh_champion_by_slug(slug, display_name)

    @staticmethod
    def _normalize_tier(value):
        text = value.strip()
        if "棱彩" in text:
            return "棱彩"
        if "黄金" in text:
            return "黄金"
        if "白银" in text:
            return "白银"
        return "白银"

    @staticmethod
    def _calc_score(grade, tier, tags):
        grade_base = {
            "SSS": 98,
            "SS": 95,
            "S": 90,
            "A": 82,
            "B": 72,
            "C": 60,
            "D": 45,
        }
        tier_bonus = {"棱彩": 3, "黄金": 1, "白银": 0}
        score = grade_base.get(grade, 60) + tier_bonus.get(tier, 0)
        if "强力联动" in tags:
            score += 2
        if "陷阱" in tags:
            score -= 15
        if "娱乐" in tags:
            score -= 8
        return max(1, min(99, int(score)))

    def _extract_aliases(self, title_text, slug, text_lines):
        aliases = []
        if title_text:
            title_text = title_text.strip()
            m = re.match(r"(.+?)\s*\((.+?)\)", title_text)
            if m:
                aliases.append(m.group(1).strip())
                aliases.append(m.group(2).strip())
            else:
                aliases.append(title_text)

        if slug:
            aliases.append(slug)

        for line in text_lines:
            if line.startswith("# "):
                continue
            if len(line) <= 16 and ("之" in line or "者" in line or "女" in line or "刃" in line):
                aliases.append(line)
            if len(aliases) >= 6:
                break

        dedup = []
        seen = set()
        for item in aliases:
            key = normalize_name_key(item)
            if key and key not in seen:
                seen.add(key)
                dedup.append(item)
        return dedup

    def _extract_recommendations(self, text_lines, source_url):
        start_idx = -1
        for idx, line in enumerate(text_lines):
            if "海克斯联动分析" in line:
                start_idx = idx
                break
        if start_idx < 0:
            return []

        grade_re = re.compile(r"^(SSS|SS|S|A|B|C|D)\s*级(?:\s+(.*))?$", re.IGNORECASE)

        def is_tier_line(line):
            return "阶" in line and ("棱彩" in line or "黄金" in line or "白银" in line)

        def is_noise(line):
            if not line:
                return True
            if len(line) > 220:
                return True
            noise_tokens = [
                "筛选", "评分", "阶级", "标签", "Assist Me", "Enemy Missing",
                "No Worries", "Open Sidebar", "Image:", "版本", "对局胜率",
                "推荐符文", "推荐出装", "技能加点", "召唤师技能",
            ]
            return any(token in line for token in noise_tokens)

        result = []
        seen = set()
        i = start_idx + 1

        equip_stop_tokens = [
            "作者", "版本", "评分", "阶级", "标签", "推荐符文", "推荐出装", "技能加点", "召唤师技能"
        ]

        def looks_like_item_name(line):
            t = line.strip()
            if len(t) < 2 or len(t) > 14:
                return False
            if any(tok in t for tok in equip_stop_tokens):
                return False
            if "海克斯" in t or "联动分析" in t:
                return False
            if grade_re.match(t):
                return False
            if is_tier_line(t):
                return False
            return contains_cjk(t)
        while i < len(text_lines):
            line = text_lines[i].strip()
            if not line:
                i += 1
                continue

            # Find an augment name line first.
            if is_noise(line) or is_tier_line(line) or grade_re.match(line):
                i += 1
                continue
            if not is_aug_name_like(line):
                i += 1
                continue
            name = line

            tier = ""
            grade = ""
            tags = ""
            author = ""
            note = ""
            items = []

            j = i + 1
            while j < min(i + 14, len(text_lines)):
                probe = text_lines[j].strip()
                if not probe:
                    j += 1
                    continue
                if is_tier_line(probe) and not tier:
                    tier = self._normalize_tier(probe)
                m = grade_re.match(probe)
                if m and not grade:
                    grade = m.group(1).upper()
                    tags = (m.group(2) or "").strip()
                if probe.startswith("作者:"):
                    author = probe.replace("作者:", "", 1).strip()
                elif not note and not is_noise(probe) and not is_tier_line(probe) and not grade_re.match(probe):
                    if 4 <= len(probe) <= 220:
                        note = probe
                # Lightweight item extraction around current augment block.
                if looks_like_item_name(probe):
                    pkey = normalize_name_key(probe)
                    if pkey != normalize_name_key(name) and pkey not in {normalize_name_key(x) for x in items}:
                        items.append(probe)
                # Next augment likely starts, stop current block parsing.
                if j > i + 1 and is_clean_augment_name_line(probe):
                    break
                j += 1

            if tier and grade:
                row_key = (name, tier, grade, tags)
                if row_key not in seen:
                    seen.add(row_key)
                    result.append({
                        "name": name,
                        "tier": tier,
                        "grade": grade,
                        "tags": tags,
                        "score": self._calc_score(grade, tier, tags),
                        "author": author,
                        "note": note,
                        "items": items[:4],
                        "parse_schema_version": HEXTECH_PARSE_SCHEMA_VERSION,
                        "source": source_url,
                    })
            # Skip to parsed block end to avoid narrative lines becoming pseudo augment names.
            i = max(i + 1, j)

        result.sort(key=lambda x: x["score"], reverse=True)
        return result[:12]

    def _extract_recommendations_fallback(self, html_content, source_url):
        lines = strip_html_to_text_lines(html_content)
        if not lines:
            return []
        # fallback: find short augment-like lines and nearby tier/grade/tags
        grade_re = re.compile(r"^(SSS|SS|S|A|B|C|D)\s*级(?:\s+(.*))?$", re.IGNORECASE)
        result = []
        for idx, line in enumerate(lines):
            if len(line) < 2 or len(line) > 24:
                continue
            if not is_clean_augment_name_line(line):
                continue
            if line in {"筛选", "评分", "阶级", "标签"}:
                continue
            if "海克斯" in line or "联动分析" in line:
                continue
            tier = ""
            grade = ""
            tags = ""
            note = ""
            items = []
            for j in range(idx + 1, min(idx + 8, len(lines))):
                probe = lines[j]
                if not tier and ("棱彩阶" in probe or "黄金阶" in probe or "白银阶" in probe):
                    tier = self._normalize_tier(probe)
                m = grade_re.match(probe)
                if m and not grade:
                    grade = m.group(1).upper()
                    tags = (m.group(2) or "").strip()
                if probe.startswith("作者:"):
                    continue
                if not note and len(probe) >= 6 and len(probe) <= 120 and "阶" not in probe and not grade_re.match(probe):
                    note = probe
                if contains_cjk(probe) and 2 <= len(probe) <= 14 and "推荐出装" not in probe and "作者" not in probe:
                    pkey = normalize_name_key(probe)
                    if pkey and pkey != normalize_name_key(line) and pkey not in {normalize_name_key(x) for x in items}:
                        items.append(probe)
                if tier and grade:
                    break
            if not tier or not grade:
                continue
            result.append({
                "name": line,
                "tier": tier,
                "grade": grade,
                "tags": tags,
                "score": self._calc_score(grade, tier, tags),
                "author": "",
                "note": note,
                "items": items[:4],
                "parse_schema_version": HEXTECH_PARSE_SCHEMA_VERSION,
                "source": source_url,
            })
            if len(result) >= 16:
                break
        result.sort(key=lambda x: x["score"], reverse=True)
        dedup = []
        seen = set()
        for item in result:
            key = item["name"]
            if key in seen:
                continue
            seen.add(key)
            dedup.append(item)
        return dedup[:12]

    def _refresh_champion_by_slug(self, slug, requested_name):
        if not slug:
            return
        url = f"{APEX_BASE_URL}/zh/champions/{slug}"
        html_content = self._http_get(url)
        if not html_content:
            log_status(
                f"hextech_fetch_empty_{slug}",
                f"[Hextech] 英雄页抓取失败(网络/权限限制): {slug}",
                interval=30,
            )
            return

        text_lines = strip_html_to_text_lines(html_content)
        recommendations = self._extract_recommendations(text_lines, url)
        if not recommendations:
            recommendations = self._extract_recommendations_fallback(html_content, url)
        if not recommendations:
            log_status(
                f"hextech_parse_empty_{slug}",
                f"[Hextech] 解析失败或无推荐: {slug}, lines={len(text_lines)}",
                interval=60,
            )
            return

        title_match = re.search(r"(?is)<title>\s*([^<|]+?)\s*\|", html_content)
        title_text = html.unescape(title_match.group(1).strip()) if title_match else slug

        version = ""
        for line in text_lines:
            if line.startswith("版本"):
                version = line.split(":", 1)[-1].strip()
                break

        aliases = self._extract_aliases(title_text, slug, text_lines)
        if requested_name:
            aliases.append(requested_name)

        entry = {
            "slug": slug,
            "url": url,
            "title": title_text,
            "version": version,
            "aliases": aliases,
            "updated_at": time.time(),
            "parse_schema_version": HEXTECH_PARSE_SCHEMA_VERSION,
            "recommendations": recommendations,
            "items_backfill_checked": True,
        }

        with self._lock:
            self._data["champions"][slug] = entry
            self._data["slug_map"][slug] = url
            for alias in aliases:
                key = normalize_name_key(alias)
                if key:
                    self._data["name_to_slug"][key] = slug
            self._data["meta"]["last_data_refresh"] = time.time()
            self._rebuild_augment_index_locked()
            self._save_cache_locked()
            self._save_augment_index_locked()

        print(f"[Hextech] 推荐更新完成: {title_text} ({len(recommendations)} 条)")


class TeeStream:
    def __init__(self, *streams):
        self.streams = streams

    def write(self, data):
        for stream in self.streams:
            stream.write(data)
            stream.flush()
        return len(data)

    def flush(self):
        for stream in self.streams:
            stream.flush()


def setup_logging():
    global _LOG_FILE_HANDLE
    if _LOG_FILE_HANDLE is not None:
        return

    log_path = os.path.join(APP_BASE_DIR, LOG_FILE_NAME)
    _LOG_FILE_HANDLE = open(log_path, "a", encoding="utf-8", buffering=1)
    _LOG_FILE_HANDLE.write("\n" + "=" * 80 + "\n")
    _LOG_FILE_HANDLE.write(f"session_start={time.strftime('%Y-%m-%d %H:%M:%S')}\n")

    sys.stdout = TeeStream(sys.__stdout__, _LOG_FILE_HANDLE)
    sys.stderr = TeeStream(sys.__stderr__, _LOG_FILE_HANDLE)


def hotkey_log(message):
    text = str(message or "").strip()
    if not text:
        return
    print(text)


class QuietStream:
    def __init__(self, stream, allow_prefixes):
        self.stream = stream
        self.allow_prefixes = tuple(allow_prefixes or [])
        self._buffer = ""

    def write(self, data):
        if not data:
            return 0
        self._buffer += data
        while "\n" in self._buffer:
            line, self._buffer = self._buffer.split("\n", 1)
            self._emit_line(line)
        return len(data)

    def _emit_line(self, line):
        if not line:
            return
        if self._is_allowed(line):
            self.stream.write(line + "\n")
            self.stream.flush()

    def _is_allowed(self, line):
        if line.startswith("[Startup]"):
            return True
        if line.startswith("[Log]"):
            return True
        if line.startswith("[Hotkey]"):
            return True
        if line.startswith("[Error]") or line.startswith("[Fatal]"):
            return True
        if any(line.startswith(prefix) for prefix in self.allow_prefixes):
            return True
        error_tokens = ("Traceback", "Exception", "Error", "失败", "异常", "无法", "未找到", "未获取", "跳过无效", "连接失败")
        return any(tok in line for tok in error_tokens)

    def flush(self):
        if self._buffer:
            self._emit_line(self._buffer)
            self._buffer = ""
        self.stream.flush()


def log_status(key, message, interval=10):
    now = time.time()
    last_message, last_time = _STATUS_LOG_CACHE.get(key, (None, 0))
    if message != last_message or (now - last_time) >= interval:
        print(message)
        _STATUS_LOG_CACHE[key] = (message, now)


def response_snippet(resp, limit=160):
    try:
        text = resp.text.strip().replace("\r", " ").replace("\n", " ")
    except Exception:
        return "<no response body>"
    if len(text) > limit:
        return text[:limit] + "..."
    return text or "<empty>"


def probe_lcu_api(port, token, source="unknown", ttl=15):
    cache_key = (port, token)
    now = time.time()
    cached = _LCU_PROBE_CACHE.get(cache_key)
    if cached and (now - cached["time"]) < ttl:
        return cached["ok"]

    url = f"https://127.0.0.1:{port}/lol-gameflow/v1/gameflow-phase"
    try:
        resp = requests.get(url, auth=('riot', token), verify=False, timeout=2)
        ok = resp.status_code == 200
        if ok:
            phase = response_snippet(resp, limit=80)
            print(f"[LCU] 已连接 LCU: source={source}, port={port}, phase={phase}")
        _LCU_PROBE_CACHE[cache_key] = {"ok": ok, "time": now}
        return ok
    except Exception as e:
        _LCU_PROBE_CACHE[cache_key] = {"ok": False, "time": now}
        return False


def _extract_cli_value(command_line, key):
    patterns = [
        rf'--{re.escape(key)}=([^"\s]+)',
        rf'"--{re.escape(key)}=([^"]+)"',
    ]
    for pattern in patterns:
        match = re.search(pattern, command_line)
        if match:
            return match.group(1).strip()
    return None


def _get_process_ids_by_snapshot():
    if os.name != "nt":
        return []

    TH32CS_SNAPPROCESS = 0x00000002
    INVALID_HANDLE_VALUE = wintypes.HANDLE(-1).value
    MAX_PATH = 260

    class PROCESSENTRY32W(ctypes.Structure):
        _fields_ = [
            ("dwSize", wintypes.DWORD),
            ("cntUsage", wintypes.DWORD),
            ("th32ProcessID", wintypes.DWORD),
            ("th32DefaultHeapID", ctypes.c_size_t),
            ("th32ModuleID", wintypes.DWORD),
            ("cntThreads", wintypes.DWORD),
            ("th32ParentProcessID", wintypes.DWORD),
            ("pcPriClassBase", wintypes.LONG),
            ("dwFlags", wintypes.DWORD),
            ("szExeFile", wintypes.WCHAR * MAX_PATH),
        ]

    try:
        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

        create_snapshot = kernel32.CreateToolhelp32Snapshot
        create_snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
        create_snapshot.restype = wintypes.HANDLE

        process_first = kernel32.Process32FirstW
        process_first.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
        process_first.restype = wintypes.BOOL

        process_next = kernel32.Process32NextW
        process_next.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
        process_next.restype = wintypes.BOOL

        close_handle = kernel32.CloseHandle
        close_handle.argtypes = [wintypes.HANDLE]
        close_handle.restype = wintypes.BOOL

        snapshot = create_snapshot(TH32CS_SNAPPROCESS, 0)
        if snapshot == INVALID_HANDLE_VALUE:
            error_code = ctypes.get_last_error()
            log_status("process_snapshot_error", f"[LCU-Debug] 创建进程快照失败: error={error_code}", interval=15)
            return []

        processes = []
        try:
            entry = PROCESSENTRY32W()
            entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
            if not process_first(snapshot, ctypes.byref(entry)):
                return []

            while True:
                name = entry.szExeFile.lower()
                if name in LCU_PROCESS_NAMES:
                    processes.append((name, int(entry.th32ProcessID)))
                if not process_next(snapshot, ctypes.byref(entry)):
                    break
        finally:
            close_handle(snapshot)

        processes.sort(key=lambda item: 0 if item[0] == "leagueclientux.exe" else 1)
        return processes
    except Exception as e:
        log_status("process_snapshot_exception", f"[LCU-Debug] 枚举进程快照异常: {e}", interval=15)
        return []


def _read_process_command_line(pid):
    if os.name != "nt":
        return None

    PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
    ProcessCommandLineInformation = 60

    try:
        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        ntdll = ctypes.WinDLL("ntdll")

        open_process = kernel32.OpenProcess
        open_process.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        open_process.restype = wintypes.HANDLE

        close_handle = kernel32.CloseHandle
        close_handle.argtypes = [wintypes.HANDLE]
        close_handle.restype = wintypes.BOOL

        query_process = ntdll.NtQueryInformationProcess
        query_process.argtypes = [
            wintypes.HANDLE,
            wintypes.ULONG,
            wintypes.LPVOID,
            wintypes.ULONG,
            ctypes.POINTER(wintypes.ULONG),
        ]
        query_process.restype = wintypes.LONG

        handle = open_process(PROCESS_QUERY_LIMITED_INFORMATION, False, pid)
        if not handle:
            error_code = ctypes.get_last_error()
            log_status(f"open_process_{pid}", f"[LCU-Debug] 打开进程失败: pid={pid}, error={error_code}", interval=15)
            return None

        try:
            size = wintypes.ULONG(0)
            query_process(handle, ProcessCommandLineInformation, None, 0, ctypes.byref(size))
            if size.value <= 0:
                return None

            buffer = ctypes.create_string_buffer(size.value)
            status = query_process(handle, ProcessCommandLineInformation, buffer, size.value, ctypes.byref(size))
            if status < 0:
                log_status(f"query_process_{pid}", f"[LCU-Debug] 读取进程命令行失败: pid={pid}, status=0x{status & 0xffffffff:08x}", interval=15)
                return None

            class UNICODE_STRING(ctypes.Structure):
                _fields_ = [
                    ("Length", wintypes.USHORT),
                    ("MaximumLength", wintypes.USHORT),
                    ("Buffer", wintypes.LPWSTR),
                ]

            command = UNICODE_STRING.from_buffer_copy(buffer.raw[:ctypes.sizeof(UNICODE_STRING)]).Buffer
            return command
        finally:
            close_handle(handle)
    except Exception as e:
        log_status(f"read_cmdline_{pid}", f"[LCU-Debug] 读取进程命令行异常: pid={pid}, error={e}", interval=15)
        return None


def _find_lcu_credentials_from_processes():
    processes = _get_process_ids_by_snapshot()
    if not processes:
        log_status("lcu_process_missing", "[LCU-Debug] 未找到 LeagueClientUx/LeagueClient 进程", interval=10)
        return None, None

    for process_name, pid in processes:
        command_line = _read_process_command_line(pid)
        if not command_line:
            continue

        port = _extract_cli_value(command_line, "app-port")
        token = _extract_cli_value(command_line, "remoting-auth-token")
        if not port or not token:
            continue

        source = f"process:{process_name}:{pid}"
        if probe_lcu_api(port, token, source=source):
            print(f"[LCU-Debug] 从进程命令行获取 LCU 凭证成功: {source}, port={port}")
            return port, token

    log_status("lcu_process_credentials_missing", "[LCU-Debug] 客户端进程存在，但未从命令行提取到可用 LCU 凭证", interval=10)
    return None, None

# 如果自动查找 lockfile 失败，手动填写 LOL 安装目录（包含 lockfile 的那一层）
# 例如: r"D:\Riot Games\League of Legends"
# 留空则自动查找
# 留空让程序自动探测；手动填错会反复读到无效 lockfile。
LOL_INSTALL_DIR = ""
# 根据你的游戏分辨率调整这个值
FEATURE_POINT_X = 1809  # 海克斯特征点 X 坐标
FEATURE_POINT_Y = 858   # 海克斯特征点 Y 坐标
DETECTION_MARGIN = 150  # 检测区域的边距

# 自动搜索模式：设为 True 时会自动搜索模板位置并输出坐标
# 找到坐标后设为 False 并使用上方配置的坐标
AUTO_SEARCH_MODE = False

# ========== 海克斯模拟数据（待替换为真实识别结果） ==========
MOCK_HEXTECH_DATA = [
    {"name": "无尽火力", "tier": "黄金", "score": 92},
    {"name": "守护天使", "tier": "黄金", "score": 87},
    {"name": "魔法吸取", "tier": "白银", "score": 75},
    {"name": "巨人化", "tier": "白银", "score": 63},
    {"name": "穿甲弹", "tier": "青铜", "score": 51},
    {"name": "双重打击", "tier": "青铜", "score": 38},
]

TIER_COLORS = {
    "棱彩": "#b388ff",
    "黄金": "#FFD700",
    "白银": "#C0C0C0",
    "青铜": "#CD7F32",
}


# ========== LCU API：读取选角色信息 ==========

_champion_map = {}  # {id: {"name": str, "alias": str}}
_cached_lockfile = None
_cached_lockfile_mtime = None
_cached_credentials = (None, None)


def _is_valid_lockfile_content(content):
    """校验 lockfile 是否包含可用的 LCU 凭证。"""
    parsed = _parse_lockfile_content(content)
    return parsed is not None


def _parse_lockfile_content(content):
    if not content:
        return None

    parts = content.split(':')
    if len(parts) < 5:
        return None

    name, pid, port, token, protocol = parts[:5]
    if not port or not token or not protocol:
        return None

    return {
        "name": name.strip(),
        "pid": pid.strip(),
        "port": port.strip(),
        "token": token.strip(),
        "protocol": protocol.strip(),
    }


def _score_lockfile_candidate(candidate, parsed):
    path = os.path.normcase(os.path.normpath(candidate))
    name = parsed["name"].lower()
    score = 0

    if "leagueclient" in name:
        score += 100
    elif "riot client" in name:
        score += 10

    if "leagueclient\\lockfile" in path:
        score += 50
    if "league of legends\\lockfile" in path:
        score += 30
    if "riot client data" in path:
        score -= 20
    if "riot client\\lockfile" in path:
        score -= 10

    return score


def _read_lockfile_content(lockfile):
    """读取 lockfile 内容，失败时返回空字符串。"""
    try:
        with open(lockfile, 'r', encoding='utf-8', errors='ignore') as f:
            return f.read().strip()
    except Exception as e:
        print(f"[LCU-Debug] 读取 lockfile 失败: {lockfile}, {e}")
        return ""


def _find_lockfile():
    """通过注册表或常见路径定位 lockfile"""
    candidates = []

    # 0. 手动配置优先
    if LOL_INSTALL_DIR:
        candidate = os.path.join(LOL_INSTALL_DIR, 'lockfile')
        candidates.append(candidate)

        base_dir = os.path.dirname(LOL_INSTALL_DIR)
        candidates.extend([
            os.path.join(base_dir, 'lockfile'),
            os.path.join(base_dir, 'Riot Client Data', 'User Data', 'Config', 'lockfile'),
            os.path.join(base_dir, 'Riot Client Data', 'Metadata', 'riot client', 'lockfile'),
            os.path.join(base_dir, 'Riot Client', 'lockfile'),
        ])

    # 1. 尝试从注册表读取安装路径
    try:
        import winreg
        reg_keys = [
            (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Riot Games, Inc\League of Legends"),
            (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Riot Games, Inc\League of Legends"),
            (winreg.HKEY_CURRENT_USER,  r"SOFTWARE\Riot Games, Inc\League of Legends"),
        ]
        for hive, subkey in reg_keys:
            try:
                key = winreg.OpenKey(hive, subkey)
                install_dir, _ = winreg.QueryValueEx(key, "InstallLocation")
                winreg.CloseKey(key)
                lockfile = os.path.join(install_dir, 'lockfile')
                print(f"[LCU-Debug] 注册表找到安装目录: {install_dir}")
                candidates.append(lockfile)
            except (FileNotFoundError, OSError):
                continue
    except ImportError:
        pass

    # 2. 扫描常见安装路径
    drives = ['C:', 'D:', 'E:', 'F:']
    common_subdirs = [
        r'Riot Games\League of Legends',
        r'Program Files\Riot Games\League of Legends',
        r'Program Files (x86)\Riot Games\League of Legends',
        r'Games\League of Legends',
        r'LOL\League of Legends',
        r'WeGameApps\英雄联盟',
        r'WeGame\英雄联盟',
        r'WeGameApps\League of Legends',
        r'Riot Client Data\User Data\Config',
        r'Riot Client Data\Metadata\riot client',
        r'WeGameApps\英雄联盟\LeagueClient',
        r'WeGame\英雄联盟\LeagueClient',
        r'WeGameApps\League of Legends\LeagueClient',
    ]
    for drive in drives:
        for subdir in common_subdirs:
            candidate = os.path.join(drive + os.sep, subdir, 'lockfile')
            if os.path.exists(candidate):
                candidates.append(candidate)

    seen = set()
    best_candidate = None
    best_content = None
    best_score = -10**9

    for candidate in candidates:
        if not candidate:
            continue
        norm = os.path.normcase(os.path.normpath(candidate))
        if norm in seen:
            continue
        seen.add(norm)
        exists = os.path.exists(candidate)
        size = os.path.getsize(candidate) if exists else -1
        if not exists or size <= 0:
            continue
        content = _read_lockfile_content(candidate)
        parsed = _parse_lockfile_content(content)
        if parsed:
            if not probe_lcu_api(parsed["port"], parsed["token"], source=candidate):
                continue
            score = _score_lockfile_candidate(candidate, parsed)
            if score > best_score:
                best_candidate = candidate
                best_content = content
                best_score = score
            continue

    if best_candidate:
        parsed = _parse_lockfile_content(best_content)
        return best_candidate
    return None


def get_lcu_credentials():
    """读取 LCU 端口和 token，优先从客户端进程命令行读取，失败再回退到 lockfile。"""
    global _cached_lockfile, _cached_lockfile_mtime, _cached_credentials

    if _cached_credentials[0] and probe_lcu_api(_cached_credentials[0], _cached_credentials[1], source="cached"):
        return _cached_credentials

    port, token = _find_lcu_credentials_from_processes()
    if port:
        _cached_lockfile = None
        _cached_lockfile_mtime = None
        _cached_credentials = (port, token)
        return _cached_credentials

    lockfile = _find_lockfile()
    if not lockfile:
        _cached_lockfile = None
        _cached_lockfile_mtime = None
        _cached_credentials = (None, None)
        return None, None
    try:
        mtime = os.path.getmtime(lockfile)
        if lockfile == _cached_lockfile and _cached_lockfile_mtime == mtime and _cached_credentials[0]:
            return _cached_credentials

        content = _read_lockfile_content(lockfile)
        parsed = _parse_lockfile_content(content)
        if parsed:
            _cached_lockfile = lockfile
            _cached_lockfile_mtime = mtime
            _cached_credentials = (parsed["port"], parsed["token"])
            return _cached_credentials  # port, token
    except Exception as e:
        print(f"[LCU] 读取 lockfile 失败: {e}")
        traceback.print_exc()
    return None, None


def load_champion_map(port, token):
    """从 LCU 加载英雄 ID -> 中文名映射（只加载一次）"""
    global _champion_map
    if _champion_map:
        return
    try:
        url = f"https://127.0.0.1:{port}/lol-game-data/assets/v1/champion-summary.json"
        resp = requests.get(url, auth=('riot', token), verify=False, timeout=5)
        if resp.status_code != 200:
            log_status(
                "champion_map_http",
                f"[LCU] 加载英雄数据失败: HTTP {resp.status_code}, body={response_snippet(resp)}",
                interval=15,
            )
            return

        data = resp.json()
        if isinstance(data, list):
            for champ in data:
                if isinstance(champ, dict) and 'id' in champ and 'name' in champ:
                    _champion_map[champ['id']] = {
                        "name": champ.get('name'),
                        "alias": champ.get('alias') or "",
                    }
        elif isinstance(data, dict):
            for champ_id, champ_name in data.items():
                _champion_map[champ_id] = {
                    "name": str(champ_name),
                    "alias": "",
                }
        else:
            print(f"[LCU] 加载英雄数据失败: 未知 JSON 类型 {type(data).__name__}")
            return

        print(f"[LCU] 已加载 {len(_champion_map)} 个英雄数据")
    except Exception as e:
        print(f"[LCU] 加载英雄数据失败: {e}")
        traceback.print_exc()


def _champion_name_from_id(champ_id, include_alias=True):
    if not champ_id:
        return None
    info = _champion_map.get(champ_id)
    if isinstance(info, dict):
        name = info.get("name") or f"未知(ID:{champ_id})"
        alias = (info.get("alias") or "").strip()
        if include_alias and alias:
            return f"{name}|{alias}"
        return name
    if isinstance(info, str):
        return info
    return f"ID:{champ_id}"


def get_champ_select_details():
    """查询选人会话状态，返回当前英雄与待选英雄列表。"""
    port, token = _cached_credentials if _cached_credentials[0] else get_lcu_credentials()
    details = {
        "active": False,
        "current_champion": None,
        "bench_champions": [],
        "candidate_champions": [],
    }
    if not port:
        return details
    try:
        url = f"https://127.0.0.1:{port}/lol-champ-select/v1/session"
        resp = requests.get(url, auth=('riot', token), verify=False, timeout=3)
        if resp.status_code != 200:
            log_status(
                "champ_select_http",
                f"[LCU] 选人会话接口返回 HTTP {resp.status_code}, body={response_snippet(resp)}",
                interval=10,
            )
            return details
        session = resp.json()
        my_cell_id = session.get('localPlayerCellId', -1)
        team = session.get('myTeam', [])
        log_status(
            "champ_select_ok",
            f"[LCU] 已连接选人会话: localPlayerCellId={my_cell_id}, team_size={len(team)}",
            interval=15,
        )
        details["active"] = True

        for actor in team:
            if actor.get('cellId') == my_cell_id:
                champ_id = actor.get('championId') or actor.get('championPickIntent', 0)
                if champ_id:
                    details["current_champion"] = _champion_name_from_id(champ_id, include_alias=True)
                break

        bench_list = []
        for item in (session.get("benchChampions") or []):
            champ_id = 0
            if isinstance(item, dict):
                champ_id = item.get("championId") or 0
            elif isinstance(item, int):
                champ_id = item
            if not champ_id:
                continue
            bench_name = _champion_name_from_id(champ_id, include_alias=True)
            if bench_name:
                bench_list.append(bench_name)
        details["bench_champions"] = bench_list

        candidates = []
        seen = set()
        for raw in [details["current_champion"], *bench_list]:
            if not raw:
                continue
            label = str(raw).split("|", 1)[0].strip()
            key = normalize_name_key(label or raw)
            if not key or key in seen:
                continue
            seen.add(key)
            candidates.append(raw)
        details["candidate_champions"] = candidates

        if not details["current_champion"]:
            log_status("champ_select_empty", "[LCU] 已进入选人，但当前还没有悬停/锁定英雄", interval=10)
        return details
    except requests.exceptions.ConnectionError:
        log_status("champ_select_conn", f"[LCU] 无法连接选人接口: https://127.0.0.1:{port}/lol-champ-select/v1/session", interval=10)
    except Exception as e:
        print(f"[LCU] 查询失败: {e}")
        traceback.print_exc()
    return details


def get_champ_select_state():
    """查询选人会话状态，返回 (active, champion_name_or_none)。"""
    details = get_champ_select_details()
    return bool(details.get("active")), details.get("current_champion")


def get_my_selected_champion():
    """查询当前 Ban/Pick 阶段自己悬停或已选的英雄名，未选返回 None"""
    _, champion_name = get_champ_select_state()
    return champion_name


def is_league_client_running():
    """检查 LeagueClient.exe 是否在运行"""
    try:
        result = subprocess.run(
            ['tasklist'],
            capture_output=True,
            text=True,
            timeout=5
            , **_hidden_subprocess_kwargs()
        )
        return 'LeagueClient.exe' in result.stdout
    except Exception as e:
        print(f"[Error] 检查进程失败: {e}")
        return False


def is_game_running():
    """检查游戏是否在运行（兼容不同发行包的游戏进程名）"""
    try:
        result = subprocess.run(
            ['tasklist'],
            capture_output=True,
            text=True,
            timeout=5
            , **_hidden_subprocess_kwargs()
        )
        output = str(result.stdout or "").lower()
        return any(name in output for name in GAME_PROCESS_NAMES)
    except Exception:
        return False


def _get_process_exe_name(pid):
    if os.name != "nt" or not pid:
        return ""
    try:
        kernel32 = ctypes.windll.kernel32
        PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
        handle = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, int(pid))
        if not handle:
            return ""
        try:
            size = wintypes.DWORD(32768)
            buf = ctypes.create_unicode_buffer(size.value)
            if kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                return os.path.basename(buf.value).lower()
        finally:
            try:
                kernel32.CloseHandle(handle)
            except Exception:
                pass
    except Exception:
        return ""
    return ""


def _find_lol_window_hwnd():
    if os.name != "nt":
        return None
    try:
        user32 = ctypes.windll.user32
        found = {"hwnd": None}
        target_names = {
            "league of legends.exe",
            "leagueclientux.exe",
            "leagueclient.exe",
            "leagueclientuxrender.exe",
        }

        @ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
        def _enum_proc(hwnd, lparam):
            try:
                if not user32.IsWindowVisible(hwnd) or user32.IsIconic(hwnd):
                    return True
                length = user32.GetWindowTextLengthW(hwnd)
                title = ""
                if length > 0:
                    buf = ctypes.create_unicode_buffer(length + 1)
                    user32.GetWindowTextW(hwnd, buf, length + 1)
                    title = buf.value.strip()
                pid = wintypes.DWORD()
                user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
                exe_name = _get_process_exe_name(pid.value)
                title_l = title.lower()
                if exe_name in target_names or "league of legends" in title_l or "leagueclient" in title_l:
                    found["hwnd"] = hwnd
                    return False
            except Exception:
                pass
            return True

        user32.EnumWindows(_enum_proc, 0)
        return found["hwnd"]
    except Exception:
        return None


def _get_client_bbox(hwnd):
    if os.name != "nt" or not hwnd:
        return None
    try:
        user32 = ctypes.windll.user32
        rect = wintypes.RECT()
        if not user32.GetClientRect(hwnd, ctypes.byref(rect)):
            return None
        left_top = wintypes.POINT(0, 0)
        right_bottom = wintypes.POINT(rect.right, rect.bottom)
        if not user32.ClientToScreen(hwnd, ctypes.byref(left_top)):
            return None
        if not user32.ClientToScreen(hwnd, ctypes.byref(right_bottom)):
            return None
        if right_bottom.x <= left_top.x or right_bottom.y <= left_top.y:
            return None
        return (left_top.x, left_top.y, right_bottom.x, right_bottom.y)
    except Exception:
        return None


def capture_game_screen():
    """Capture the LoL client area when possible, otherwise fall back to the desktop."""
    try:
        bbox = None
        hwnd = _find_lol_window_hwnd()
        if hwnd:
            bbox = _get_client_bbox(hwnd)
        if bbox:
            screenshot = ImageGrab.grab(bbox=bbox)
            capture_src = f"lol_client:{bbox}"
        else:
            screenshot = ImageGrab.grab()
            capture_src = "desktop"
        img = cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)
        if bbox:
            log_status("capture_game_screen_bbox", f"[Debug] 客户端区域: {bbox}", interval=30)
        log_status(
            "capture_game_screen_ok",
            f"[Debug] 截图成功，来源={capture_src}，图像尺寸: {img.shape}",
            interval=10,
        )
        return img
    except Exception as e:
        log_status("capture_game_screen_fail", f"[Debug] 截图失败: {e}", interval=10)
        return None


def save_png_unicode(path, image):
    """Save image robustly on Windows paths with non-ASCII chars."""
    try:
        ok, buf = cv2.imencode(".png", image)
        if not ok:
            return False
        buf.tofile(path)
        return True
    except Exception:
        return False


def detect_hextech_screen(screenshot):
    """ROI-only: only trust the left-most card name box as page trigger."""
    ok, left_text, middle_text, right_text, _rois, _roi_boxes, debug = probe_hextech_screen_by_left_and_middle_cards(screenshot)
    if ok:
        print("[Debug] [OK] 左中卡命中，判定处于海克斯页面")
    else:
        print("[Debug] [FAIL] 左中卡未命中，判定不在海克斯页面")
    return ok


def detect_hextech_offer_tier(screenshot):
    """Backward-compatible single-tier wrapper."""
    tiers, debug = detect_hextech_offer_tiers(screenshot)
    if not tiers:
        return None
    # Prefer the most frequent tier among three cards.
    return sorted(tiers, key=lambda t: debug["counts"].get(t, 0), reverse=True)[0]


def detect_hextech_offer_tiers(screenshot):
    """
    Detect tiers from 3 augment cards by sampling each card's top accent strip.
    Returns (set(tiers), debug_dict). tiers can include multiple values.
    """
    if screenshot is None:
        return set(), {"counts": {}, "card_results": [], "confidence": 0.0}
    try:
        h, w = screenshot.shape[:2]
        # Expected 3 cards around lower-middle area.
        panel_x1, panel_x2 = int(w * 0.20), int(w * 0.80)
        panel_y1, panel_y2 = int(h * 0.56), int(h * 0.90)
        if panel_x2 <= panel_x1 or panel_y2 <= panel_y1:
            return set(), {"counts": {}, "card_results": [], "confidence": 0.0}

        panel = screenshot[panel_y1:panel_y2, panel_x1:panel_x2]
        ph, pw = panel.shape[:2]
        card_w = pw // 3
        card_results = []
        counts = {"棱彩": 0, "黄金": 0, "白银": 0}

        for i in range(3):
            cx1 = i * card_w
            cx2 = pw if i == 2 else (i + 1) * card_w
            # Sample top strip where tier color is most obvious.
            sy1 = int(ph * 0.10)
            sy2 = int(ph * 0.24)
            sx1 = cx1 + int((cx2 - cx1) * 0.10)
            sx2 = cx2 - int((cx2 - cx1) * 0.10)
            if sx2 <= sx1 or sy2 <= sy1:
                continue
            sample = panel[sy1:sy2, sx1:sx2]
            hsv = cv2.cvtColor(sample, cv2.COLOR_BGR2HSV)
            hch, sch, vch = hsv[:, :, 0], hsv[:, :, 1], hsv[:, :, 2]

            vivid = (sch > 70) & (vch > 80)
            gold_mask = vivid & (hch >= 16) & (hch <= 38)
            prism_mask = vivid & (((hch >= 112) & (hch <= 170)) | ((hch >= 95) & (hch <= 111)))
            silver_mask = (vch > 145) & (sch < 58)

            gold = int(np.count_nonzero(gold_mask))
            prism = int(np.count_nonzero(prism_mask))
            silver = int(np.count_nonzero(silver_mask))
            scores = {"棱彩": prism, "黄金": gold, "白银": silver}
            tier, score = max(scores.items(), key=lambda x: x[1])

            # low confidence card -> unknown
            if score < 120:
                card_results.append({"card": i, "tier": "未知", "score": score, "scores": scores})
                continue

            counts[tier] += 1
            card_results.append({"card": i, "tier": tier, "score": score, "scores": scores})

        tiers = {k for k, v in counts.items() if v > 0}
        # Anti-noise: a single prismatic hit is often false positive from VFX/UI.
        if counts.get("棱彩", 0) == 1 and (counts.get("黄金", 0) >= 1 or counts.get("白银", 0) >= 1):
            tiers.discard("棱彩")
            if not tiers:
                tiers = {"黄金"} if counts.get("黄金", 0) >= counts.get("白银", 0) else {"白银"}
        confidence = sum(v for v in counts.values()) / 3.0
        return tiers, {"counts": counts, "card_results": card_results, "confidence": confidence}
    except Exception as e:
        log_status("hextech_tier_detect_error", f"[Hextech] 阶级识别异常: {e}", interval=10)
        return set(), {"counts": {}, "card_results": [], "confidence": 0.0}


def _run_windows_ocr_on_image(image_path):
    """
    Run OCR via Windows built-in OCR engine through PowerShell.
    Returns plain text or empty string.
    """
    ps_script = r'''
param([string]$Path)
[Reflection.Assembly]::LoadWithPartialName('System.Runtime.WindowsRuntime') | Out-Null
$null = [Windows.Storage.StorageFile,Windows.Storage,ContentType=WindowsRuntime]
$null = [Windows.Graphics.Imaging.BitmapDecoder,Windows.Graphics.Imaging,ContentType=WindowsRuntime]
$null = [Windows.Media.Ocr.OcrEngine,Windows.Media.Ocr,ContentType=WindowsRuntime]

function Await([object]$Async, [Type]$ResultType) {
  $asTask = [System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.IsGenericMethodDefinition -and $_.GetGenericArguments().Count -eq 1 -and $_.GetParameters().Count -eq 1
  } | Select-Object -First 1
  $closed = $asTask.MakeGenericMethod($ResultType)
  $task = $closed.Invoke($null, @($Async))
  $task.Wait()
  return $task.Result
}

$fileAsync=[Windows.Storage.StorageFile]::GetFileFromPathAsync($Path)
$file = Await $fileAsync ([Windows.Storage.StorageFile])
$streamAsync = $file.OpenAsync([Windows.Storage.FileAccessMode]::Read)
$stream = Await $streamAsync ([Windows.Storage.Streams.IRandomAccessStream])
$decoderAsync = [Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)
$decoder = Await $decoderAsync ([Windows.Graphics.Imaging.BitmapDecoder])
$sbAsync = $decoder.GetSoftwareBitmapAsync()
$sb = Await $sbAsync ([Windows.Graphics.Imaging.SoftwareBitmap])
$engine=[Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages()
$resAsync = $engine.RecognizeAsync($sb)
$res = Await $resAsync ([Windows.Media.Ocr.OcrResult])
Write-Output $res.Text
'''
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".ps1", mode="w", encoding="utf-8") as fp:
            ps_path = fp.name
            fp.write(ps_script)
        try:
            cmd = [
                "powershell", "-NoProfile", "-ExecutionPolicy", "Bypass",
                "-File", ps_path, "-Path", image_path
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=8, **_hidden_subprocess_kwargs())
            if result.returncode == 0 and result.stdout:
                return result.stdout.strip()
            return ""
        finally:
            try:
                os.remove(ps_path)
            except Exception:
                pass
    except Exception:
        return ""


def _extract_three_card_name_rois(screenshot):
    """Return 3 cropped name regions for augment cards."""
    h, w = screenshot.shape[:2]
    panel_x1, panel_x2 = int(w * HEXTECH_CARD_PANEL_X1_RATIO), int(w * HEXTECH_CARD_PANEL_X2_RATIO)
    panel_y1, panel_y2 = int(h * HEXTECH_CARD_PANEL_Y1_RATIO), int(h * HEXTECH_CARD_PANEL_Y2_RATIO)
    panel = screenshot[panel_y1:panel_y2, panel_x1:panel_x2]
    ph, pw = panel.shape[:2]
    gap = int(pw * HEXTECH_CARD_GAP_RATIO)
    card_w = max(1, (pw - 2 * gap) // 3)
    rois = []
    roi_boxes = []
    for i in range(3):
        cx1 = i * (card_w + gap)
        cx2 = cx1 + card_w
        if i == 2:
            cx2 = min(cx2, pw)
        ny1 = int(ph * HEXTECH_NAME_BAND_Y1_RATIO)
        ny2 = int(ph * HEXTECH_NAME_BAND_Y2_RATIO)
        nx1 = cx1 + int((cx2 - cx1) * HEXTECH_NAME_BAND_X_MARGIN_RATIO)
        nx2 = cx2 - int((cx2 - cx1) * HEXTECH_NAME_BAND_X_MARGIN_RATIO)
        if nx2 <= nx1 or ny2 <= ny1:
            continue
        roi = panel[ny1:ny2, nx1:nx2]
        rois.append(roi)
        roi_boxes.append((panel_x1 + nx1, panel_y1 + ny1, panel_x1 + nx2, panel_y1 + ny2))
    return rois, roi_boxes


def _refine_title_strip_for_ocr(roi, already_upsampled=False):
    """Find a tighter title band to reduce card-center glow interference."""
    up = roi if already_upsampled else cv2.resize(roi, None, fx=2.0, fy=2.0, interpolation=cv2.INTER_CUBIC)
    hsv = cv2.cvtColor(up, cv2.COLOR_BGR2HSV)
    mask = cv2.inRange(hsv, (0, 0, 145), (180, 110, 255))
    uh, uw = mask.shape[:2]
    side = int(uw * 0.12)
    mask[:, :side] = 0
    mask[:, uw - side:] = 0
    row_sum = mask.sum(axis=1).astype(np.float32)
    if row_sum.max() <= 0:
        return up
    kernel = np.ones(21, dtype=np.float32) / 21.0
    sm = np.convolve(row_sum, kernel, mode="same")
    center = int(np.argmax(sm))
    band_h = max(54, int(uh * 0.42))
    band_h = min(band_h, uh)
    y1 = max(0, center - band_h // 2)
    y2 = min(uh, center + band_h // 2)
    if y2 <= y1 + 8:
        return up
    return up[y1:y2, :]


def _score_ocr_text_for_aug_name(text):
    t = re.sub(r"\s+", "", text or "")
    if not t:
        return 0
    if re.search(r"(?:\d{1,2}:\d{2})|(?:\d{4}[./-]\d{1,2})", t):
        return 0
    cjk = len(re.findall(r"[\u4e00-\u9fff]", t))
    return cjk * 3 + len(t)


def _normalize_ocr_name_text(text):
    """Normalize OCR output to likely augment-name text (single line, clean chars)."""
    t = str(text or "").strip()
    if not t:
        return ""
    parts = [p.strip() for p in re.split(r"[\r\n]+", t) if p.strip()]
    if not parts:
        return ""
    # Prefer shortest CJK-heavy line: augment names are usually short.
    parts.sort(key=lambda x: (0 if contains_cjk(x) else 1, len(x)))
    cand = parts[0]
    cand = re.sub(r"[^\u4e00-\u9fffA-Za-z0-9·]", "", cand)
    return cand.strip()


def _is_meaningful_chinese_text(text, min_cjk=2):
    """
    Strict trigger text check:
    - must contain Chinese
    - digits / latin letters are rejected
    - at least min_cjk Chinese characters
    """
    t = _normalize_ocr_name_text(text)
    if not t:
        return False
    if re.search(r"[A-Za-z0-9]", t):
        return False
    return len(re.findall(r"[\u4e00-\u9fff]", t)) >= int(min_cjk or 2)


def _is_valid_hextech_probe_hit(text, score, min_cjk=2):
    if not _is_meaningful_chinese_text(text, min_cjk=min_cjk):
        return False
    try:
        return float(score or 0.0) >= float(HEXTECH_ROI_TEXT_SCORE_THRESHOLD)
    except Exception:
        return False


def _cleanup_ocr_binary(bw):
    h, w = bw.shape[:2]
    side = int(w * 0.10)
    bw[:, :side] = 0
    bw[:, w - side:] = 0
    num, labels, stats, _ = cv2.connectedComponentsWithStats(bw, 8)
    clean = np.zeros_like(bw)
    max_area = int(h * w * 0.06)
    for i in range(1, num):
        x, y, ww, hh, area = stats[i]
        if area < 8 or area > max_area:
            continue
        if ww > int(w * 0.78) or hh > int(h * 0.92):
            continue
        clean[labels == i] = 255
    k2 = cv2.getStructuringElement(cv2.MORPH_RECT, (2, 2))
    clean = cv2.morphologyEx(clean, cv2.MORPH_OPEN, k2)
    clean = cv2.morphologyEx(clean, cv2.MORPH_CLOSE, k2)
    return clean


def _make_ocr_candidates_from_base(base):
    hsv = cv2.cvtColor(base, cv2.COLOR_BGR2HSV)
    gray = cv2.cvtColor(base, cv2.COLOR_BGR2GRAY)
    white_mask = cv2.inRange(hsv, (0, 0, 135), (180, 120, 255))
    k = cv2.getStructuringElement(cv2.MORPH_RECT, (17, 17))

    top = cv2.morphologyEx(gray, cv2.MORPH_TOPHAT, k)
    top = cv2.normalize(top, None, 0, 255, cv2.NORM_MINMAX)
    _, c_light = cv2.threshold(top, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    c_light = _cleanup_ocr_binary(cv2.bitwise_and(c_light, white_mask))
    # raw/gray fallback keeps slim strokes when binary cleanup over-prunes short names.
    return {"light": c_light, "raw": base, "gray": gray}


def _generate_ocr_candidates(roi):
    up_full = cv2.resize(roi, None, fx=2.0, fy=2.0, interpolation=cv2.INTER_CUBIC)
    cand_full = _make_ocr_candidates_from_base(up_full)
    candidates = {
        "light_full": cand_full["light"],
        "raw_full": cand_full["raw"],
        "gray_full": cand_full["gray"],
    }
    return up_full, up_full, candidates


def _ocr_best_text_from_card_roi(roi, label="card"):
    """OCR one card ROI and return the best cleaned text with score metadata."""
    try:
        _, _, candidates = _generate_ocr_candidates(roi)
        best_txt = ""
        best_score = -1
        best_name = ""

        def _run_candidate(name):
            bw = candidates.get(name)
            if bw is None:
                return "", -1
            if HEXTECH_OCR_SAVE_CROPS:
                debug_dir = os.path.join(APP_BASE_DIR, HEXTECH_OCR_DEBUG_DIR)
                os.makedirs(debug_dir, exist_ok=True)
                cand_path = os.path.join(debug_dir, f"{label}_{name}.png")
            else:
                with tempfile.NamedTemporaryFile(delete=False, suffix=f"_{label}_{name}.png") as tf:
                    cand_path = tf.name
            try:
                if not save_png_unicode(cand_path, bw):
                    return "", -1
                txt = _normalize_ocr_name_text(_run_windows_ocr_on_image(cand_path))
                return txt, _score_ocr_text_for_aug_name(txt)
            finally:
                if not HEXTECH_OCR_SAVE_CROPS:
                    try:
                        os.remove(cand_path)
                    except Exception:
                        pass

        for name in ("light_full",):
            txt, score = _run_candidate(name)
            if score > best_score:
                best_txt = txt
                best_score = score
                best_name = name

        if best_score < 6 or len(best_txt) < 2:
            for name in ("raw_full", "gray_full"):
                txt, score = _run_candidate(name)
                if score > best_score:
                    best_txt = txt
                    best_score = score
                    best_name = name
                if score >= 6 and len(txt) >= 2:
                    break

        return _normalize_ocr_name_text(best_txt), {"score": best_score, "candidate": best_name}
    except Exception:
        return "", {"score": -1, "candidate": ""}


def probe_hextech_screen_by_left_card(screenshot):
    """
    Fast probe for the hextech page using only the left-most card name area.
    Returns (ok, left_text, rois, roi_boxes, debug_dict).
    """
    if screenshot is None:
        print("[Debug] 截图为空，跳过检测")
        return False, "", [], [], {"score": -1, "candidate": "", "reason": "screenshot_none"}
    try:
        rois, roi_boxes = _extract_three_card_name_rois(screenshot)
        if not rois:
            print("[Debug] ROI-only 检测失败: 无有效卡片ROI")
            return False, "", [], [], {"score": -1, "candidate": "", "reason": "no_rois"}

        left_text, left_debug = _ocr_best_text_from_card_roi(rois[0], label="left_probe")
        score = float(left_debug.get("score", -1) or -1)
        ok = _is_meaningful_chinese_text(left_text, min_cjk=2)
        log_status(
            "hextech_left_probe_state",
            f"[Debug] 左卡探测: ok={ok}, score={score:.1f}, "
            f"candidate={left_debug.get('candidate')}, text={left_text}",
            interval=5,
        )
        left_debug = dict(left_debug)
        left_debug["text"] = left_text
        left_debug["ok"] = ok
        left_debug["roi_box"] = roi_boxes[0] if roi_boxes else None
        return ok, left_text, rois, roi_boxes, left_debug
    except Exception as e:
        log_status("hextech_left_probe_error", f"[Debug] 左卡探测异常: {e}", interval=10)
        return False, "", [], [], {"score": -1, "candidate": "", "reason": str(e)}


def probe_hextech_screen_by_left_and_middle_cards(screenshot):
    """
    Strong probe for the hextech page.
    Any two cards with stable Chinese OCR are enough to confirm the page.
    Returns (ok, left_text, middle_text, right_text, rois, roi_boxes, debug_dict).
    """
    if screenshot is None:
        print("[Debug] 截图为空，跳过检测")
        return False, "", "", "", [], [], {"score": -1, "candidate": "", "reason": "screenshot_none"}
    try:
        rois, roi_boxes = _extract_three_card_name_rois(screenshot)
        min_hits = max(1, int(HEXTECH_ROI_DETECT_MIN_HITS or 2))
        if len(rois) < min_hits:
            print("[Debug] ROI-only 检测失败: 有效卡片ROI不足")
            return False, "", "", "", [], [], {"score": -1, "candidate": "", "reason": "insufficient_rois"}
        texts = ["", "", ""]
        scores = [-1.0, -1.0, -1.0]
        ok_flags = [False, False, False]
        candidates = ["", "", ""]
        labels = ("left_probe", "middle_probe", "right_probe")
        for idx in range(min(3, len(rois))):
            text, info = _ocr_best_text_from_card_roi(rois[idx], label=labels[idx])
            score = float(info.get("score", -1) or -1)
            texts[idx] = text
            scores[idx] = score
            candidates[idx] = str(info.get("candidate", "") or "")
            ok_flags[idx] = _is_valid_hextech_probe_hit(text, score, min_cjk=2)

        hit_count = sum(1 for flag in ok_flags if flag)
        left_text, middle_text, right_text = texts
        left_score, middle_score, right_score = scores
        left_ok, middle_ok, right_ok = ok_flags
        ok = hit_count >= min_hits
        log_status(
            "hextech_three_probe_state",
            f"[Debug] 三卡探测: ok={ok}, hits={hit_count}/{min_hits}, left_ok={left_ok}, middle_ok={middle_ok}, right_ok={right_ok}, "
            f"left_score={left_score:.1f}, middle_score={middle_score:.1f}, right_score={right_score:.1f}, "
            f"left_candidate={candidates[0]}, middle_candidate={candidates[1]}, right_candidate={candidates[2]}, "
            f"left_text={left_text}, middle_text={middle_text}, right_text={right_text}",
            interval=5,
        )
        debug = {
            "score": left_score,
            "candidate": candidates[0],
        }
        debug["text"] = left_text
        debug["ok"] = ok
        debug["hit_count"] = hit_count
        debug["min_hits"] = min_hits
        debug["middle_text"] = middle_text
        debug["middle_ok"] = middle_ok
        debug["right_text"] = right_text
        debug["right_ok"] = right_ok
        debug["middle_score"] = middle_score
        debug["middle_candidate"] = candidates[1]
        debug["right_score"] = right_score
        debug["right_candidate"] = candidates[2]
        debug["roi_box"] = roi_boxes[0] if roi_boxes else None
        debug["middle_roi_box"] = roi_boxes[1] if len(roi_boxes) > 1 else None
        debug["right_roi_box"] = roi_boxes[2] if len(roi_boxes) > 2 else None
        return ok, left_text, middle_text, right_text, rois, roi_boxes, debug
    except Exception as e:
        log_status("hextech_left_middle_probe_error", f"[Debug] 三卡探测异常: {e}", interval=10)
        return False, "", "", "", [], [], {"score": -1, "candidate": "", "reason": str(e)}


def _ocr_texts_from_card_rois(rois):
    texts = []
    debug_paths = []
    for idx, roi in enumerate(rois):
        try:
            cleaned, _meta = _ocr_best_text_from_card_roi(roi, label=f"card_{idx}")
            texts.append(cleaned)
            debug_paths.append("")
        except Exception:
            texts.append("")
            debug_paths.append("")
    return texts, debug_paths


def detect_hextech_offer_tiers_by_ocr(screenshot, champion_recos, global_augment_index=None):
    """
    OCR 3 card names, fuzzy-match against current champion recos, infer tiers set.
    Returns (tiers_set, debug_dict).
    """
    if screenshot is None:
        return set(), {"ocr_texts": [], "matches": [], "roi_boxes": [], "debug_paths": []}
    try:
        rois, roi_boxes = _extract_three_card_name_rois(screenshot)
        ocr_texts, debug_paths = _ocr_texts_from_card_rois(rois)
        if not ocr_texts:
            return set(), {"ocr_texts": [], "matches": [], "roi_boxes": roi_boxes, "debug_paths": debug_paths}

        global_pool = []
        global_augment_index = global_augment_index or {}
        for _, info in global_augment_index.items():
            nm = str((info or {}).get("name", "")).strip()
            tiers = list((info or {}).get("tiers", []) or [])
            if not nm or not tiers:
                continue
            global_pool.append((normalize_name_key(nm), nm, tiers))

        local_pool = []
        for item in (champion_recos or []):
            nm = str(item.get("name", "")).strip()
            tier = str(item.get("tier", "")).strip()
            if not nm or tier not in {"棱彩", "黄金", "白银"}:
                continue
            local_pool.append((normalize_name_key(nm), nm, [tier]))

        tiers = set()
        matches = []
        for text in ocr_texts:
            if len(text) < 2:
                continue
            q = normalize_name_key(text)
            if not q:
                continue
            best_ratio = 0.0
            best_item = None
            best_from = ""

            for nn, raw_name, tier_list in global_pool:
                if not nn:
                    continue
                ratio = difflib.SequenceMatcher(None, q, nn).ratio()
                if ratio > best_ratio:
                    best_ratio = ratio
                    best_item = (raw_name, list(tier_list))
                    best_from = "global"

            local_best_ratio = 0.0
            local_best_item = None
            for nn, raw_name, tier_list in local_pool:
                if not nn:
                    continue
                ratio = difflib.SequenceMatcher(None, q, nn).ratio()
                if ratio > local_best_ratio:
                    local_best_ratio = ratio
                    local_best_item = (raw_name, list(tier_list))

            # Prefer global index; local pool can help when global data is still incomplete.
            if local_best_item and local_best_ratio >= max(0.72, best_ratio + 0.08):
                best_ratio = local_best_ratio
                best_item = local_best_item
                best_from = "local"

            if best_item and best_ratio >= HEXTECH_OCR_GLOBAL_MATCH_RATIO:
                for t in best_item[1]:
                    if t in {"棱彩", "黄金", "白银"}:
                        tiers.add(t)
                matches.append({
                    "ocr": text,
                    "name": best_item[0],
                    "tiers": best_item[1],
                    "ratio": round(best_ratio, 3),
                    "from": best_from,
                })

        return tiers, {"ocr_texts": ocr_texts, "matches": matches, "roi_boxes": roi_boxes, "debug_paths": debug_paths}
    except Exception as e:
        log_status("hextech_ocr_detect_error", f"[Hextech] OCR阶级识别异常: {e}", interval=10)
        return set(), {"ocr_texts": [], "matches": [], "roi_boxes": [], "debug_paths": []}


def detect_hextech_offers_by_ocr(screenshot, champion_recos, champion_name=None, screen_probe=None):
    """
    OCR current 3 augment names and map each to champion recommendation pool.
    Returns (offer_rows, debug_dict), where offer_rows keeps left->right card order.
    """
    empty_debug = {"ocr_texts": [], "rows": [], "roi_boxes": [], "debug_paths": []}
    if screenshot is None:
        return [], empty_debug
    try:
        if isinstance(screen_probe, dict) and screen_probe.get("rois"):
            rois = screen_probe.get("rois") or []
            roi_boxes = screen_probe.get("roi_boxes") or []
            left_text = _normalize_ocr_name_text(screen_probe.get("left_text", ""))
        else:
            _, left_text, rois, roi_boxes, _ = probe_hextech_screen_by_left_card(screenshot)
        if not rois:
            return [], empty_debug
        if not left_text:
            left_text, _ = _ocr_best_text_from_card_roi(rois[0], label="left_card")
        if not left_text:
            return [], empty_debug

        ocr_texts = [left_text]
        debug_paths = [""]
        if len(rois) > 1:
            tail_texts, tail_debug_paths = _ocr_texts_from_card_rois(rois[1:])
            ocr_texts.extend(tail_texts)
            debug_paths.extend(tail_debug_paths)
        while len(ocr_texts) < 3:
            ocr_texts.append("")
            debug_paths.append("")
        # Slot-level sticky fallback: reduce single-frame OCR drop on one card.
        now = time.time()
        sticky_sec = float(HEXTECH_OCR_TEXT_STICKY_SECONDS)
        try:
            cache_vals = _OCR_CARD_TEXT_STICKY_CACHE.get("values", ["", "", ""])
            cache_ts = float(_OCR_CARD_TEXT_STICKY_CACHE.get("ts", 0.0))
            out = []
            for i in range(3):
                cur = ocr_texts[i] if i < len(ocr_texts) else ""
                old = cache_vals[i] if i < len(cache_vals) else ""
                if cur:
                    out.append(cur)
                elif old and (now - cache_ts) <= sticky_sec:
                    out.append(old)
                else:
                    out.append("")
            _OCR_CARD_TEXT_STICKY_CACHE["values"] = list(out)
            _OCR_CARD_TEXT_STICKY_CACHE["ts"] = now
            ocr_texts = out
        except Exception:
            pass

        norm_pool = []
        for item in (champion_recos or []):
            nm = str(item.get("name", "")).strip()
            if not nm:
                continue
            norm_pool.append((normalize_name_key(nm), item))
        pool_name_set = {normalize_name_key(str(item.get("name", "")).strip()) for item in (champion_recos or [])}

        rows = []
        for i in range(max(3, len(ocr_texts))):
            raw = ocr_texts[i] if i < len(ocr_texts) else ""
            cleaned = re.sub(r"[^\u4e00-\u9fffA-Za-z0-9·]", "", str(raw or ""))
            cleaned = cleaned.strip()

            best_ratio = 0.0
            best_item = None
            if cleaned:
                q = normalize_name_key(cleaned)
                for nn, item in norm_pool:
                    if not nn:
                        continue
                    ratio = difflib.SequenceMatcher(None, q, nn).ratio()
                    if q and nn and (q in nn or nn in q):
                        ratio = min(1.0, ratio + 0.12)
                    if ratio > best_ratio:
                        best_ratio = ratio
                        best_item = item
                # Prefer local persisted cache lookup (hero + augment) when available.
                if champion_name:
                    local_item = hextech_provider.get_reco_by_augment_name(champion_name, cleaned)
                    if local_item:
                        best_item = local_item
                        best_ratio = max(best_ratio, 0.80)

            matched = best_item is not None and best_ratio >= 0.52
            grade_raw = str((best_item or {}).get("grade", "")).upper() if matched else ""
            grade_label = f"{grade_raw}级" if grade_raw in {"SSS", "SS", "S", "A", "B", "C", "D"} else "无评级"
            tier_label = str((best_item or {}).get("tier_label") or (best_item or {}).get("tier") or "").strip().upper()
            if tier_label not in {"T1", "T2", "T3", "T4", "T5"}:
                tier_label = ""
            win_rate = (best_item or {}).get("win_rate") if matched else None
            pick_rate = (best_item or {}).get("pick_rate") if matched else None
            match_pct = int(round(best_ratio * 100)) if cleaned else 0
            display_name = cleaned if cleaned else f"选项{i + 1} 未识别"
            matched_name = str((best_item or {}).get("name", "")).strip() if matched else ""
            tag_text = str((best_item or {}).get("tags", "")).strip() if matched else ""
            author_text = str((best_item or {}).get("author", "")).strip() if matched else ""
            items_text = ""
            items_list = []
            if matched:
                items = (best_item or {}).get("items") or []
                if isinstance(items, list) and items:
                    items_list = [str(x).strip() for x in items if str(x).strip()][:4]
                    items_text = " + ".join(items_list)
            note_text = str((best_item or {}).get("note", "")).strip() if matched else ""

            # Extract augment combo names from note text using local champion augment pool.
            combo_names = []
            if matched and note_text and pool_name_set:
                pool_names = [str(it.get("name", "")).strip() for _, it in norm_pool if str(it.get("name", "")).strip()]
                combo_names = extract_combo_names_from_note(
                    note_text,
                    pool_names,
                    self_name=(matched_name or display_name),
                    max_count=3,
                )
                # rebuild items using current row note + combo rows.
                try:
                    temp_row = dict(best_item or {})
                    temp_row["combo_text"] = " + ".join(combo_names[:3]) if combo_names else ""
                    items_list = build_items_for_row(temp_row, champion_recos or [], max_count=4)
                    items_text = " + ".join(items_list) if items_list else ""
                except Exception:
                    pass

            rows.append({
                "index": i + 1,
                "name": display_name,
                "matched_name": matched_name,
                "icon_url": str((best_item or {}).get("icon_url", "")).strip() if matched else "",
                "rarity": str((best_item or {}).get("rarity", "")).strip() if matched else "",
                "grade_label": grade_label,
                "tier_label": tier_label,
                "win_rate": win_rate,
                "pick_rate": pick_rate,
                "match_pct": match_pct,
                "score": match_pct,
                "tag_text": tag_text if tag_text else "无标签",
                "author_text": author_text,
                "combo_text": " + ".join(combo_names[:3]) if combo_names else "",
                "items_text": items_text,
                "items": items_list,
            })

        return rows[:3], {
            "ocr_texts": ocr_texts,
            "rows": rows[:3],
            "roi_boxes": roi_boxes,
            "debug_paths": debug_paths,
        }
    except Exception as e:
        log_status("hextech_ocr_offer_error", f"[Hextech] OCR选项识别异常: {e}", interval=10)
        return [], empty_debug


# ========== 步骤4：海克斯浮窗 ==========

class HextechOverlay:
    def __init__(self):
        self.root = None
        self.preview_root = None
        self.visible = False
        self.preview_visible = False
        self._lock = threading.Lock()
        self._last_show_signature = None
        self._last_preview_show_signature = None
        self.preview_canvas = None
        self.preview_scrollbar = None
        self.preview_inner_frame = None
        self._active_champion_name = None
        self._icon_cache = {}
        self._icon_failed = set()
        self._icon_pending = {}
        self._icon_loading = set()
        self._overlay_width = 680
        self._main_content_height = 360
        self._preview_content_height = 600

    def _build_show_signature(self, hextech_list, champion_name, loading=False, empty_title="", empty_subtitle=""):
        try:
            rows = []
            for row in (hextech_list or [])[:3]:
                if not isinstance(row, dict):
                    continue
                rows.append((
                    str(row.get("name", "")).strip(),
                    str(row.get("icon_url", "")).strip(),
                    str(row.get("rarity", "")).strip().lower(),
                    str(row.get("tier_label") or row.get("tier") or "").strip().upper(),
                    str(row.get("grade", "")).strip().upper(),
                    str(row.get("tags", "")).strip(),
                    str(row.get("author_text", "")).strip(),
                    str(row.get("combo_text", "")).strip(),
                    str(row.get("items_text", "")).strip(),
                ))
            return (
                str(champion_name or "").strip(),
                bool(loading),
                str(empty_title or "").strip(),
                str(empty_subtitle or "").strip(),
                tuple(rows),
                self._build_combo_signature(champion_name),
            )
        except Exception:
            return (str(champion_name or "").strip(), ())

    def _build_combo_signature(self, champion_name):
        try:
            combos = self._get_combo_recommendations_for_champion(champion_name)
            packed = []
            for item in combos or []:
                if not isinstance(item, dict):
                    continue
                members = item.get("members") if isinstance(item.get("members"), list) else []
                packed.append(
                    (
                        str(item.get("name", "")).strip(),
                        str(item.get("rating", "")).strip().upper(),
                        tuple(
                            (
                                str(member.get("augment_id", "")).strip(),
                                str(member.get("name", "")).strip(),
                                str(member.get("icon_url", "")).strip(),
                                str(member.get("rarity", "")).strip().lower(),
                            )
                            for member in members
                            if isinstance(member, dict)
                        ),
                    )
                )
            return tuple(packed)
        except Exception:
            return ()

    @staticmethod
    def _grade_label_and_style(grade_raw):
        g = str(grade_raw or "").upper()
        show = f"{g}级" if g in {"SSS", "SS", "S", "A", "B", "C", "D"} else "无评级"
        if show in {"SSS级", "SS级", "S级"}:
            return show, "#d6a63a", "#1a1200"
        if show == "A级":
            return show, "#8d5bff", "#ffffff"
        if show == "B级":
            return show, "#4a86ff", "#ffffff"
        if show == "C级":
            return show, "#3cb371", "#ffffff"
        return show, "#364c70", "#dce6ff"

    @staticmethod
    def _tier_badge_style(tier_raw):
        g = str(tier_raw or "").strip().upper()
        if g == "T1":
            return "T1", "#d6a63a", "#1a1200"
        if g == "T2":
            return "T2", "#8d5bff", "#ffffff"
        if g == "T3":
            return "T3", "#4a86ff", "#ffffff"
        if g == "T4":
            return "T4", "#3cb371", "#ffffff"
        if g == "T5":
            return "T5", "#2e1a1a", "#ff9a9a"
        return g or "未知", "#16345f", "#9ac0ff"

    @staticmethod
    def _tier_name_color(tier_raw):
        g = str(tier_raw or "").strip().upper()
        if g == "T1":
            return "#ffd56a"
        if g == "T2":
            return "#c7a0ff"
        if g == "T3":
            return "#74b9ff"
        if g == "T4":
            return "#7cffab"
        if g == "T5":
            return "#9aa4b2"
        return "#ecf5ff"

    @staticmethod
    def _rarity_name_color(rarity_raw):
        r = str(rarity_raw or "").strip().lower()
        if "棱彩" in r or "prismatic" in r:
            return "#b388ff"
        if "黄金" in r or "gold" in r:
            return "#ffd56a"
        if "白银" in r or "silver" in r:
            return "#c0c0c0"
        return "#ecf5ff"

    @staticmethod
    def _normalize_rarity_style(rarity_raw):
        r = str(rarity_raw or "").strip().lower()
        if "棱彩" in r or "prismatic" in r:
            return "prismatic"
        if "黄金" in r or "gold" in r:
            return "gold"
        if "白银" in r or "silver" in r:
            return "silver"
        return ""

    @classmethod
    def _rarity_icon_style(cls, rarity_raw):
        style = cls._normalize_rarity_style(rarity_raw)
        if style == "prismatic":
            return {"border": "#b366ff", "bg": "#1e1530", "fg": "#ddb7ff"}
        if style == "gold":
            return {"border": "#c29c6d", "bg": "#2e2518", "fg": "#f1d7a6"}
        if style == "silver":
            return {"border": "#5a5a5a", "bg": "#2a2a3a", "fg": "#d7d7df"}
        return {"border": "#274870", "bg": "#1a1a2e", "fg": "#7f9bc4"}

    def _combo_member_font(self):
        try:
            return tkfont.Font(font=("Microsoft YaHei", 11, "bold"))
        except Exception:
            return None

    def _estimate_combo_chip_width(self, text, icon_size=30):
        text = str(text or "").strip()
        font_obj = self._combo_member_font()
        try:
            text_width = font_obj.measure(text) if font_obj is not None else 0
        except Exception:
            text_width = 0
        if text_width <= 0:
            text_width = max(56, len(text) * 18)
        text_block_width = max(72, text_width)
        return icon_size + text_block_width + 32

    @staticmethod
    def _estimate_combo_panel_height(combos):
        combo_count = len([item for item in (combos or []) if isinstance(item, dict)])
        if combo_count <= 0:
            return 84
        return 560

    def _sync_combo_container_heights(self, combos):
        height = self._estimate_combo_panel_height(combos)
        for widget in (getattr(self, "combo_container", None), getattr(self, "preview_combo_container", None)):
            if widget is None:
                continue
            try:
                widget.configure(height=height)
            except Exception:
                pass
        self._resize_main_window()
        self._resize_preview_window()

    def _resize_window(self, window, width, anchor_fn=None):
        if window is None:
            return
        try:
            window.update_idletasks()
            height = max(1, int(window.winfo_reqheight() or 0))
            x = int(window.winfo_x() or 0)
            y = int(window.winfo_y() or 0)
            if x > 0 or y > 0:
                window.geometry(f"{width}x{height}+{x}+{y}")
            else:
                window.geometry(f"{width}x{height}")
                if anchor_fn is not None:
                    anchor_fn()
        except Exception:
            pass

    def _resize_main_window(self):
        self._resize_window(self.root, self._overlay_width, anchor_fn=self._anchor_top_right)

    def _resize_preview_window(self):
        self._resize_window(self.preview_root, self._overlay_width, anchor_fn=self._anchor_preview_top_right)

    def _set_icon_label_photo(self, label, photo):
        if label is None:
            return
        try:
            if not label.winfo_exists():
                return
            if photo is not None:
                label.configure(image=photo, text="")
                label.image = photo
            else:
                label.configure(image="", text="?", fg="#7f9bc4")
                label.image = None
        except Exception:
            pass

    def _icon_cache_key(self, icon_url, size):
        return (str(icon_url or "").strip(), int(size or 36))

    def _load_icon_worker(self, key):
        icon_url, size = key
        payload = None
        try:
            resp = requests.get(
                icon_url,
                headers={"User-Agent": "hextech-assistant/1.0"},
                timeout=6,
            )
            if resp.status_code == 200 and resp.content:
                payload = resp.content
        except Exception:
            payload = None

        root = self.root or self.preview_root
        if root is None:
            with self._lock:
                self._icon_loading.discard(key)
                self._icon_pending.pop(key, None)
                self._icon_failed.add(key)
            return

        def _finish():
            photo = None
            if payload:
                try:
                    img = Image.open(io.BytesIO(payload)).convert("RGBA")
                    resampling = getattr(getattr(Image, "Resampling", Image), "LANCZOS", Image.LANCZOS)
                    img = img.resize((size, size), resampling)
                    photo = ImageTk.PhotoImage(img)
                except Exception:
                    photo = None

            with self._lock:
                waiters = list(self._icon_pending.pop(key, []))
                self._icon_loading.discard(key)
                if photo is not None:
                    self._icon_cache[key] = photo
                    self._icon_failed.discard(key)
                else:
                    self._icon_failed.add(key)

            for label in waiters:
                self._set_icon_label_photo(label, photo)

        try:
            root.after(0, _finish)
        except Exception:
            with self._lock:
                self._icon_loading.discard(key)
                self._icon_pending.pop(key, None)
                self._icon_failed.add(key)

    def _bind_icon_label(self, label, icon_url, size=38):
        key = self._icon_cache_key(icon_url, size)
        if not key[0]:
            self._set_icon_label_photo(label, None)
            return

        cached_photo = None
        should_start_worker = False
        with self._lock:
            cached_photo = self._icon_cache.get(key)
            if cached_photo is None and key not in self._icon_failed:
                self._icon_pending.setdefault(key, []).append(label)
                if key not in self._icon_loading:
                    self._icon_loading.add(key)
                    should_start_worker = True

        if cached_photo is not None:
            self._set_icon_label_photo(label, cached_photo)
            return
        if key in self._icon_failed:
            self._set_icon_label_photo(label, None)
            return
        if should_start_worker:
            threading.Thread(target=self._load_icon_worker, args=(key,), daemon=True).start()

    def _make_augment_icon(self, parent, icon_url, rarity=None, bg="#14213d", size=38, padx=(0, 8)):
        style = self._rarity_icon_style(rarity)
        holder = tk.Frame(
            parent,
            bg=style["bg"],
            width=size,
            height=size,
            highlightbackground=style["border"],
            highlightthickness=2,
        )
        holder.pack(side="left", padx=padx, anchor="n")
        holder.pack_propagate(False)
        label = tk.Label(
            holder,
            text="?",
            bg=style["bg"],
            fg=style["fg"],
            font=("Microsoft YaHei", 9, "bold"),
        )
        label.pack(fill="both", expand=True)
        self._bind_icon_label(label, icon_url, size=size)
        return holder

    def _pin_window_topmost(self):
        """Use Win32 styles to keep overlay above normal/borderless game windows."""
        if os.name != "nt" or self.root is None:
            return
        try:
            hwnd = self.root.winfo_id()
            user32 = ctypes.windll.user32

            GWL_EXSTYLE = -20
            WS_EX_TOPMOST = 0x00000008
            WS_EX_TOOLWINDOW = 0x00000080
            HWND_TOPMOST = -1
            SWP_NOMOVE = 0x0002
            SWP_NOSIZE = 0x0001
            SWP_NOACTIVATE = 0x0010
            SWP_SHOWWINDOW = 0x0040

            exstyle = user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            user32.SetWindowLongW(
                hwnd,
                GWL_EXSTYLE,
                exstyle | WS_EX_TOPMOST | WS_EX_TOOLWINDOW
            )
            user32.SetWindowPos(
                hwnd,
                HWND_TOPMOST,
                0, 0, 0, 0,
                SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE
            )
        except Exception as e:
            log_status("overlay_topmost_error", f"[Overlay] 置顶样式设置失败: {e}", interval=20)

    def _topmost_keepalive(self):
        if self.root is None:
            if self.preview_root is None:
                return
        try:
            if self.root is not None and self.visible:
                self.root.attributes("-topmost", True)
                self._pin_window_topmost()
            if self.preview_root is not None and self.preview_visible:
                self.preview_root.attributes("-topmost", True)
            if self.root is not None:
                self.root.after(1000, self._topmost_keepalive)
            elif self.preview_root is not None:
                self.preview_root.after(1000, self._topmost_keepalive)
        except Exception:
            pass

    def _anchor_top_right(self, margin_right=8, margin_top=8):
        if self.root is None:
            return
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        ww = self.root.winfo_width()
        x = max(0, sw - ww - margin_right)
        y = max(0, margin_top)
        self.root.geometry(f"+{x}+{y}")

    def _build_window(self):
        self.root = tk.Tk()
        self.root.title("海克斯推荐")
        self.root.attributes("-topmost", True)       # 始终置顶
        self.root.attributes("-alpha", 0.86)         # 更透明
        self.root.overrideredirect(True)             # 去掉标题栏
        self.root.configure(bg="#05070e")

        # 拖动支持
        self.root.bind("<ButtonPress-1>", self._on_drag_start)
        self.root.bind("<B1-Motion>", self._on_drag_motion)
        self._drag_x = 0
        self._drag_y = 0

        panel = tk.Frame(
            self.root,
            bg="#10192f",
            highlightbackground="#43f0ff",
            highlightthickness=1,
            bd=0,
        )
        panel.pack(fill="both", expand=True)

        # 标题栏
        title_frame = tk.Frame(panel, bg="#142243", pady=5)
        title_frame.pack(fill="x")
        tk.Label(
            title_frame, text="HEXTECH OVERLAY",
            bg="#142243", fg="#98f7ff",
            font=("Microsoft YaHei", 11, "bold")
        ).pack(side="left", padx=10)
        tk.Button(
            title_frame, text="×", bg="#142243", fg="#ff76bb",
            activebackground="#24365f", activeforeground="#ffb5da",
            relief="flat", font=("Microsoft YaHei", 10, "bold"),
            command=self.hide
        ).pack(side="right", padx=6)

        self.combo_container, self.combo_frame = build_scrollable_combo_box(
            panel,
            bg="#0c1430",
            accent="#2b6b9e",
            title_text="推荐海克斯组合",
            side="bottom",
        )
        self.combo_container.configure(height=self._estimate_combo_panel_height([]))

        # 列表区域
        self.list_frame = tk.Frame(panel, bg="#10192f", padx=8, pady=6, height=self._main_content_height)
        self.list_frame.pack(fill="x", expand=False)
        self.list_frame.pack_propagate(False)

        # 初始位置：右上角
        self._resize_main_window()

        self.root.withdraw()  # 初始隐藏
        self._pin_window_topmost()
        self.root.after(1000, self._topmost_keepalive)

        # Champion preview window (draft phase).
        self.preview_root = tk.Toplevel(self.root)
        self.preview_root.title("选人海克斯预览")
        self.preview_root.attributes("-topmost", True)
        self.preview_root.attributes("-alpha", 0.86)
        self.preview_root.overrideredirect(True)
        self.preview_root.configure(bg="#05070e")
        self.preview_root.bind("<ButtonPress-1>", self._on_preview_drag_start)
        self.preview_root.bind("<B1-Motion>", self._on_preview_drag_motion)
        self._preview_drag_x = 0
        self._preview_drag_y = 0

        p_panel = tk.Frame(
            self.preview_root,
            bg="#10192f",
            highlightbackground="#43f0ff",
            highlightthickness=1,
            bd=0,
        )
        p_panel.pack(fill="both", expand=True)

        p_title = tk.Frame(p_panel, bg="#142243", pady=5)
        p_title.pack(fill="x")
        self.preview_title_var = tk.StringVar(value="选人预览")
        tk.Label(
            p_title, textvariable=self.preview_title_var,
            bg="#142243", fg="#98f7ff",
            font=("Microsoft YaHei", 11, "bold")
        ).pack(side="left", padx=8)
        tk.Button(
            p_title, text="×", bg="#142243", fg="#ff76bb",
            activebackground="#24365f", activeforeground="#ffb5da",
            relief="flat", font=("Microsoft YaHei", 10, "bold"),
            command=self.hide_preview
        ).pack(side="right", padx=6)

        tk.Label(
            p_panel,
            text=f"游戏内海克斯页面按{HEXTECH_MANUAL_TRIGGER_NAME}可打开/关闭识别悬浮窗",
            bg="#10192f",
            fg="#7ecfff",
            font=("Microsoft YaHei", 9, "bold"),
            anchor="w",
            padx=8,
            pady=6,
        ).pack(fill="x")

        self.preview_combo_container, self.preview_combo_frame = build_scrollable_combo_box(
            p_panel,
            bg="#0c1430",
            accent="#2b6b9e",
            title_text="推荐海克斯组合",
            side="bottom",
        )
        self.preview_combo_container.configure(height=self._estimate_combo_panel_height([]))

        body = tk.Frame(p_panel, bg="#10192f", height=self._preview_content_height)
        body.pack(fill="x", expand=False)
        body.pack_propagate(False)
        self.preview_canvas = tk.Canvas(body, bg="#10192f", highlightthickness=0, bd=0)
        self.preview_scrollbar = ttk.Scrollbar(body, orient="vertical", command=self.preview_canvas.yview)
        self.preview_canvas.configure(yscrollcommand=self.preview_scrollbar.set)
        self.preview_scrollbar.pack(side="right", fill="y")
        self.preview_canvas.pack(side="left", fill="both", expand=True)
        self.preview_inner_frame = tk.Frame(self.preview_canvas, bg="#10192f", padx=8, pady=6)
        self.preview_canvas_window = self.preview_canvas.create_window((0, 0), window=self.preview_inner_frame, anchor="nw")
        self.preview_inner_frame.bind(
            "<Configure>",
            lambda e: self.preview_canvas.configure(scrollregion=self.preview_canvas.bbox("all"))
        )
        self.preview_canvas.bind(
            "<Configure>",
            lambda e: self.preview_canvas.itemconfigure(self.preview_canvas_window, width=e.width)
        )
        for widget in (self.preview_root, p_panel, body, self.preview_canvas, self.preview_inner_frame):
            widget.bind("<MouseWheel>", self._on_preview_mousewheel, add="+")
            widget.bind("<Button-4>", self._on_preview_mousewheel, add="+")
            widget.bind("<Button-5>", self._on_preview_mousewheel, add="+")

        self._resize_preview_window()
        self.preview_root.withdraw()
        self.root.mainloop()

    def _on_drag_start(self, event):
        self._drag_x = event.x
        self._drag_y = event.y

    def _on_drag_motion(self, event):
        x = self.root.winfo_x() + event.x - self._drag_x
        y = self.root.winfo_y() + event.y - self._drag_y
        self.root.geometry(f"+{x}+{y}")

    def _on_preview_drag_start(self, event):
        self._preview_drag_x = event.x
        self._preview_drag_y = event.y

    def _on_preview_drag_motion(self, event):
        if self.preview_root is None:
            return
        x = self.preview_root.winfo_x() + event.x - self._preview_drag_x
        y = self.preview_root.winfo_y() + event.y - self._preview_drag_y
        self.preview_root.geometry(f"+{x}+{y}")

    def _anchor_preview_top_right(self, margin_right=8, margin_top=8):
        if self.preview_root is None:
            return
        self.preview_root.update_idletasks()
        sw = self.preview_root.winfo_screenwidth()
        ww = self.preview_root.winfo_width()
        x = max(0, sw - ww - margin_right)
        y = max(0, margin_top)
        self.preview_root.geometry(f"+{x}+{y}")

    def _on_preview_mousewheel(self, event):
        if self.preview_canvas is None or self.preview_root is None:
            return
        try:
            if not self.preview_visible:
                return
            cur = getattr(event, "widget", None)
            inside = False
            while cur is not None:
                if cur is self.preview_canvas or cur is self.preview_inner_frame or cur is self.preview_scrollbar:
                    inside = True
                    break
                cur = getattr(cur, "master", None)
            if not inside:
                return
            delta = 0
            if hasattr(event, "delta") and event.delta:
                delta = -1 * int(event.delta / 120) if event.delta != 0 else 0
            elif getattr(event, "num", None) == 4:
                delta = -1
            elif getattr(event, "num", None) == 5:
                delta = 1
            if delta != 0:
                self.preview_canvas.yview_scroll(delta, "units")
        except Exception:
            pass

    def _get_combo_recommendations_for_champion(self, champion_name):
        if not champion_name:
            return []
        provider = globals().get("hextech_provider")
        if provider is None:
            return []
        try:
            if hasattr(provider, "get_combo_recommendations"):
                combos = provider.get_combo_recommendations(champion_name)
                if isinstance(combos, list):
                    return [dict(x) for x in combos if isinstance(x, dict)]
        except Exception:
            pass
        try:
            slug = provider._resolve_slug_locked(champion_name)[0] if hasattr(provider, "_resolve_slug_locked") else None
            if not slug:
                return []
            entry = provider._data.get("champions", {}).get(str(slug), {}) if hasattr(provider, "_data") else {}
            extra = entry.get("provider_extra", {}) if isinstance(entry, dict) else {}
            combos = extra.get("combo_reco", [])
            if isinstance(combos, list):
                return [dict(x) for x in combos if isinstance(x, dict)]
        except Exception:
            pass
        return []

    def _get_candidate_strength_rows(self, candidate_champions):
        provider = globals().get("hextech_provider")
        if provider is None or not candidate_champions:
            return []
        try:
            if hasattr(provider, "get_champion_strengths"):
                rows = provider.get_champion_strengths(candidate_champions)
                if isinstance(rows, list):
                    return [dict(x) for x in rows if isinstance(x, dict)]
        except Exception:
            pass
        return []

    @staticmethod
    def _build_candidate_strength_signature(candidate_rows):
        packed = []
        for row in candidate_rows or []:
            if not isinstance(row, dict):
                continue
            packed.append(
                (
                    str(row.get("name", "")).strip(),
                    str(row.get("tier_label", "")).strip().upper(),
                    row.get("win_rate"),
                    row.get("pick_rate"),
                    str(row.get("champion_id", "")).strip(),
                )
            )
        return tuple(packed)

    def _render_candidate_strengths(self, container, candidate_rows):
        if container is None:
            return
        section = tk.Frame(
            container,
            bg="#0c1430",
            highlightbackground="#2b6b9e",
            highlightthickness=1,
            padx=10,
            pady=8,
        )
        section.pack(fill="x", pady=(0, 8))

        tk.Label(
            section,
            text="待选英雄强度",
            bg="#0c1430",
            fg="#98f7ff",
            font=("Microsoft YaHei", 10, "bold"),
            anchor="w",
        ).pack(fill="x")

        if not candidate_rows:
            tk.Label(
                section,
                text="等待待选英雄列表...",
                bg="#0c1430",
                fg="#7f9bc4",
                font=("Microsoft YaHei", 9),
                anchor="w",
            ).pack(fill="x", pady=(4, 0))
            return

        chips_host = tk.Frame(section, bg="#0c1430")
        chips_host.pack(fill="x", pady=(6, 0))
        try:
            chips_host.update_idletasks()
            available_width = max(240, int(chips_host.winfo_width() or container.winfo_width() or 620))
        except Exception:
            available_width = 620
        chip_width = 194
        per_row = max(1, available_width // (chip_width + 8))
        current_line = None

        for idx, row in enumerate(candidate_rows):
            if idx % per_row == 0:
                current_line = tk.Frame(chips_host, bg="#0c1430")
                current_line.pack(fill="x", anchor="w")

            tier = str(row.get("tier_label", "")).strip().upper()
            badge_show, badge_bg, badge_fg = self._tier_badge_style(tier if tier in {"T1", "T2", "T3", "T4", "T5"} else "")
            if tier not in {"T1", "T2", "T3", "T4", "T5"}:
                badge_show = "无评级"
            name_fg = self._tier_name_color(tier)
            border_color = badge_bg if tier in {"T1", "T2", "T3", "T4", "T5"} else "#234c7f"

            chip = tk.Frame(
                current_line,
                bg="#14213d",
                highlightbackground=border_color,
                highlightthickness=1,
                width=chip_width,
                height=62,
                padx=8,
                pady=6,
            )
            chip.pack(side="left", padx=(0, 8), pady=(0, 8))
            chip.pack_propagate(False)

            top_row = tk.Frame(chip, bg="#14213d")
            top_row.pack(fill="x")
            tk.Label(
                top_row,
                text=str(row.get("name", "")).strip() or "未知英雄",
                bg="#14213d",
                fg=name_fg,
                font=("Microsoft YaHei", 10, "bold"),
                anchor="w",
            ).pack(side="left", fill="x", expand=True)
            tk.Label(
                top_row,
                text=badge_show,
                bg=badge_bg,
                fg=badge_fg,
                font=("Microsoft YaHei", 8, "bold"),
                padx=6,
                pady=2,
            ).pack(side="right")

            wr = row.get("win_rate")
            pr = row.get("pick_rate")
            stat_parts = []
            if wr is not None:
                stat_parts.append(f"胜率 {float(wr):.2f}%")
            if pr is not None:
                stat_parts.append(f"登场 {float(pr):.2f}%")
            stat_text = "  ".join(stat_parts) if stat_parts else "暂无评级数据"
            tk.Label(
                chip,
                text=stat_text,
                bg="#14213d",
                fg="#b7cdf4" if stat_parts else "#7f9bc4",
                font=("Microsoft YaHei", 9, "bold" if stat_parts else "normal"),
                anchor="w",
            ).pack(fill="x", pady=(6, 0))

    def _render_combo_recommendations(self, container, champion_name, title_text="推荐海克斯组合"):
        if container is None:
            return
        for widget in container.winfo_children():
            widget.destroy()

        combos = self._get_combo_recommendations_for_champion(champion_name)
        self._sync_combo_container_heights(combos)
        if not combos:
            tk.Label(
                container,
                text="暂无组合推荐",
                bg="#0c1430",
                fg="#7f9bc4",
                font=("Microsoft YaHei", 9),
                anchor="w",
            ).pack(fill="x", pady=(3, 0))
            return

        for item in combos:
            name = str(item.get("name", "")).strip()
            if not name:
                continue
            rating = str(item.get("rating", "")).strip()
            members = item.get("members") if isinstance(item.get("members"), list) else []
            combo_font = self._combo_member_font() or ("Microsoft YaHei", 11, "bold")
            rating_u = rating.upper()
            if rating_u in {"T1", "T2", "T3", "T4", "T5"}:
                badge_show, badge_bg, badge_fg = self._tier_badge_style(rating_u)
            else:
                badge_show, badge_bg, badge_fg = self._grade_label_and_style(rating)
            row = tk.Frame(
                container,
                bg="#101c36",
                highlightbackground="#2c5aa0",
                highlightthickness=1,
                padx=10,
                pady=7,
            )
            row.pack(fill="x", pady=(5, 0))
            if members:
                content_row = tk.Frame(row, bg="#101c36")
                content_row.pack(fill="x")
                member_host = tk.Frame(content_row, bg="#101c36")
                member_host.pack(side="left", fill="x", expand=True)
                valid_members = [member for member in members[:4] if isinstance(member, dict)]
                content_row.update_idletasks()
                available_width = content_row.winfo_width() - 80
                if available_width <= 120:
                    available_width = 440
                current_line = tk.Frame(member_host, bg="#101c36")
                current_line.pack(fill="x", anchor="w")
                current_width = 0
                plus_width = 18

                for idx, member in enumerate(valid_members):
                    member_name = str(member.get("name", "")).strip() or str(member.get("augment_id", "")).strip()
                    chip_width = self._estimate_combo_chip_width(member_name, icon_size=32)
                    if idx > 0:
                        needs_break = current_width > 0 and (current_width + plus_width + 6 + chip_width) > available_width
                        if needs_break:
                            if current_width + plus_width <= available_width:
                                tk.Label(
                                    current_line,
                                    text="+",
                                    bg="#101c36",
                                    fg="#8fb9ff",
                                    font=("Microsoft YaHei", 12, "bold"),
                                ).pack(side="left", padx=(0, 6))
                            current_line = tk.Frame(member_host, bg="#101c36")
                            current_line.pack(fill="x", anchor="w", pady=(4, 0))
                            current_width = 0
                        else:
                            tk.Label(
                                current_line,
                                text="+",
                                bg="#101c36",
                                fg="#8fb9ff",
                                font=("Microsoft YaHei", 12, "bold"),
                            ).pack(side="left", padx=(0, 6))
                            current_width += plus_width + 6
                    elif current_width > 0 and (current_width + chip_width) > available_width:
                        current_line = tk.Frame(member_host, bg="#101c36")
                        current_line.pack(fill="x", anchor="w", pady=(4, 0))
                        current_width = 0
                    chip = tk.Frame(
                        current_line,
                        bg="#14274a",
                        highlightbackground="#24466d",
                        highlightthickness=1,
                        padx=6,
                        pady=5,
                    )
                    chip.pack(side="left", padx=(0, 6))
                    self._make_augment_icon(
                        chip,
                        str(member.get("icon_url", "")).strip(),
                        rarity=str(member.get("rarity", "")).strip(),
                        bg="#14274a",
                        size=32,
                        padx=(0, 6),
                    )
                    tk.Label(
                        chip,
                        text=member_name,
                        bg="#14274a",
                        fg=self._rarity_name_color(member.get("rarity")),
                        font=combo_font,
                        anchor="w",
                    ).pack(side="left")
                    current_width += chip_width + 6
                tk.Label(
                    content_row,
                    text=badge_show,
                    bg=badge_bg,
                    fg=badge_fg,
                    font=("Microsoft YaHei", 9, "bold"),
                    padx=6,
                    pady=2,
                ).pack(side="right", padx=(8, 0))
            else:
                fallback_row = tk.Frame(row, bg="#101c36")
                fallback_row.pack(fill="x")
                tk.Label(
                    fallback_row,
                    text=name,
                    bg="#101c36",
                    fg="#ecf5ff",
                    font=combo_font,
                    anchor="w",
                ).pack(side="left", fill="x", expand=True)
                tk.Label(
                    fallback_row,
                    text=badge_show,
                    bg=badge_bg,
                    fg=badge_fg,
                    font=("Microsoft YaHei", 9, "bold"),
                    padx=6,
                    pady=2,
                ).pack(side="right")

    def _refresh_list(self, hextech_list, loading=False, empty_title="", empty_subtitle=""):
        for widget in self.list_frame.winfo_children():
            widget.destroy()
        if hasattr(self, "combo_frame") and self.combo_frame is not None:
            for widget in self.combo_frame.winfo_children():
                widget.destroy()

        if not hextech_list:
            title_text = str(empty_title or "").strip()
            subtitle_text = empty_subtitle if empty_subtitle is not None else ""
            if loading:
                if not title_text:
                    title_text = "数据加载中..."
                if not subtitle_text:
                    subtitle_text = "正在OCR识别当前3个海克斯，请稍候..."
            else:
                if not title_text:
                    title_text = "当前暂无可显示的海克斯数据"
                if not subtitle_text:
                    subtitle_text = f"请在海克斯选择页面按{HEXTECH_MANUAL_TRIGGER_NAME}开始识别。"
            tk.Label(
                self.list_frame,
                text=title_text,
                bg="#0a1022",
                fg="#d8e3ff",
                font=("Microsoft YaHei", 10, "bold"),
                anchor="w",
                justify="left",
            ).pack(fill="x", pady=(8, 4))
            if subtitle_text:
                tk.Label(
                    self.list_frame,
                    text=subtitle_text,
                    bg="#0a1022",
                    fg="#7f8fb2",
                    font=("Microsoft YaHei", 8),
                    anchor="w",
                    justify="left",
                ).pack(fill="x", pady=(0, 6))
            return

        sorted_list = list(hextech_list)[:3]

        for i, item in enumerate(sorted_list):
            rank = int(item.get("index", i + 1))
            name_show = str(item.get("name", f"选项{rank} 未识别"))
            tag_text = str(item.get("tag_text", "")).strip()
            if tag_text.startswith("网站Top"):
                tag_text = ""
            combo_text = str(item.get("combo_text", "")).strip()
            wr = item.get("win_rate")
            pr = item.get("pick_rate")
            items_text = str(item.get("items_text", "")).strip()
            items_list = item.get("items") if isinstance(item.get("items"), list) else []
            if not items_list and items_text:
                items_list = [x.strip() for x in items_text.split("+") if x.strip()]
            icon_url = str(item.get("icon_url", "")).strip()
            rarity = str(item.get("rarity", "")).strip()

            tier = str(item.get("tier_label") or item.get("tier") or "").strip().upper()
            badge_show, badge_bg, badge_fg = self._tier_badge_style(tier if tier in {"T1", "T2", "T3", "T4", "T5"} else "T5")
            name_fg = self._rarity_name_color(item.get("rarity"))

            card = tk.Frame(self.list_frame, bg="#14213d", bd=0, padx=10, pady=7)
            card.pack(fill="x", pady=6)
            card.configure(highlightbackground="#234c7f", highlightthickness=1)

            head = tk.Frame(card, bg="#14213d")
            head.pack(fill="x")
            left = tk.Frame(head, bg="#14213d")
            left.pack(side="left", fill="x", expand=True)
            self._make_augment_icon(left, icon_url, rarity=rarity, bg="#14213d", size=38)
            tk.Label(
                left, text=f"{i + 1}. {name_show}",
                bg="#14213d", fg=name_fg, font=("Microsoft YaHei", 11, "bold"), anchor="w"
            ).pack(side="left", fill="x", expand=True)
            tk.Label(
                head, text=badge_show, bg=badge_bg, fg=badge_fg,
                font=("Microsoft YaHei", 8, "bold"), padx=6, pady=2
            ).pack(side="right")

            stat_row = tk.Frame(card, bg="#14213d")
            stat_row.pack(fill="x", pady=(4, 0))
            if wr is not None:
                tk.Label(
                    stat_row,
                    text=f"胜率 {float(wr):.2f}%",
                    bg="#14213d",
                    fg="#4DFF88",
                    font=("Microsoft YaHei", 9, "bold"),
                    anchor="w",
                ).pack(side="left", padx=(0, 8))
            if pr is not None:
                tk.Label(
                    stat_row,
                    text=f"选取率 {float(pr):.2f}%",
                    bg="#14213d",
                    fg="#4DA3FF",
                    font=("Microsoft YaHei", 9, "bold"),
                    anchor="w",
                ).pack(side="left")

            if tag_text:
                tk.Label(card, text=tag_text, bg="#14213d", fg="#73ecff", font=("Microsoft YaHei", 9, "bold"), anchor="w").pack(fill="x", pady=(3, 0))
            if combo_text:
                tk.Label(
                    card, text=f"推荐海克斯组合: {combo_text}",
                    bg="#14213d", fg="#ffc56f",
                    font=("Microsoft YaHei", 9, "bold"), anchor="w"
                ).pack(fill="x", pady=(3, 0))
            if items_list:
                tk.Label(
                    card, text=f"装备: {' + '.join(items_list[:4])}",
                    bg="#14213d", fg="#8ef0bf",
                    font=("Microsoft YaHei", 9, "bold"), anchor="w"
                ).pack(fill="x", pady=(3, 0))

        if hasattr(self, "combo_frame") and self.combo_frame is not None:
            self._render_combo_recommendations(
                self.combo_frame,
                getattr(self, "_active_champion_name", None),
                title_text="推荐海克斯组合",
            )

    def _refresh_preview_list(self, champion_name, rows, loading=False, candidate_rows=None):
        if self.preview_inner_frame is None:
            return
        for widget in self.preview_inner_frame.winfo_children():
            widget.destroy()

        title = f"选人预览 - {champion_name}" if champion_name else "选人预览"
        try:
            self.preview_title_var.set(title)
        except Exception:
            pass

        self._render_candidate_strengths(self.preview_inner_frame, candidate_rows or [])

        if not rows:
            msg = "数据加载中..."
            sub = "正在抓取并解析该英雄海克斯推荐"
            if not loading:
                msg = "当前英雄暂无高评级海克斯"
                sub = ""
            tk.Label(
                self.preview_inner_frame,
                text=msg,
                bg="#10192f", fg="#d8e4ff",
                font=("Microsoft YaHei", 10, "bold"),
                anchor="w",
            ).pack(fill="x", pady=(6, 4))
            if sub:
                tk.Label(
                    self.preview_inner_frame,
                    text=sub,
                    bg="#10192f", fg="#7f9bc4",
                    font=("Microsoft YaHei", 9),
                    anchor="w",
                ).pack(fill="x", pady=(0, 4))
            return

        for i, r in enumerate(rows, 1):
            nm = str(r.get("name", "")).strip() or f"推荐{i}"
            tier = str(r.get("tier_label") or r.get("tier") or "").strip().upper()
            tags = str(r.get("tags", "")).strip()
            if tags.startswith("网站Top"):
                tags = ""
            combo_text = str(r.get("combo_text", "")).strip()
            wr = r.get("win_rate")
            pr = r.get("pick_rate")
            icon_url = str(r.get("icon_url", "")).strip()
            rarity = str(r.get("rarity", "")).strip()
            badge_show, badge_bg, badge_fg = self._tier_badge_style(tier if tier in {"T1", "T2", "T3", "T4", "T5"} else "T5")
            name_fg = self._rarity_name_color(r.get("rarity"))

            row = tk.Frame(self.preview_inner_frame, bg="#14213d", highlightbackground="#234c7f", highlightthickness=1, padx=10, pady=7)
            row.pack(fill="x", pady=5)
            head = tk.Frame(row, bg="#14213d")
            head.pack(fill="x")
            left = tk.Frame(head, bg="#14213d")
            left.pack(side="left", fill="x", expand=True)
            self._make_augment_icon(left, icon_url, rarity=rarity, bg="#14213d", size=38)
            tk.Label(left, text=f"{i}. {nm}", bg="#14213d", fg=name_fg, font=("Microsoft YaHei", 11, "bold"), anchor="w").pack(side="left", fill="x", expand=True)
            tk.Label(head, text=badge_show, bg=badge_bg, fg=badge_fg, font=("Microsoft YaHei", 8, "bold"), padx=6, pady=2).pack(side="right")

            stat_row = tk.Frame(row, bg="#14213d")
            stat_row.pack(fill="x", pady=(4, 0))
            if wr is not None:
                tk.Label(
                    stat_row,
                    text=f"胜率 {float(wr):.2f}%",
                    bg="#14213d",
                    fg="#4DFF88",
                    font=("Microsoft YaHei", 9, "bold"),
                    anchor="w",
                ).pack(side="left", padx=(0, 8))
            if pr is not None:
                tk.Label(
                    stat_row,
                    text=f"选取率 {float(pr):.2f}%",
                    bg="#14213d",
                    fg="#4DA3FF",
                    font=("Microsoft YaHei", 9, "bold"),
                    anchor="w",
                ).pack(side="left")

            if tags:
                tk.Label(row, text=tags, bg="#14213d", fg="#73ecff", font=("Microsoft YaHei", 9, "bold"), anchor="w").pack(fill="x", pady=(3, 0))
            if combo_text:
                tk.Label(
                    row, text=f"推荐海克斯组合: {combo_text}",
                    bg="#14213d", fg="#ffc56f",
                    font=("Microsoft YaHei", 9, "bold"), anchor="w"
                ).pack(fill="x", pady=(3, 0))
            items_text = str(r.get("items_text", "")).strip()
            items_list = r.get("items") if isinstance(r.get("items"), list) else []
            if not items_list and items_text:
                items_list = [x.strip() for x in items_text.split("+") if x.strip()]
            if items_list:
                tk.Label(
                    row, text=f"装备: {' + '.join(items_list[:4])}",
                    bg="#14213d", fg="#8ef0bf",
                    font=("Microsoft YaHei", 9, "bold"), anchor="w"
                ).pack(fill="x", pady=(3, 0))

        if hasattr(self, "preview_combo_frame") and self.preview_combo_frame is not None:
            self._render_combo_recommendations(
                self.preview_combo_frame,
                champion_name,
                title_text="推荐海克斯组合",
            )

    def show(self, hextech_list=None, champion_name=None, loading=False, empty_title="", empty_subtitle=""):
        if hextech_list is None:
            hextech_list = MOCK_HEXTECH_DATA
        if self.root is None:
            return
        signature = self._build_show_signature(
            hextech_list,
            champion_name,
            loading=loading,
            empty_title=empty_title,
            empty_subtitle=empty_subtitle,
        )
        self.root.after(
            0,
            lambda: self._show_impl(
                hextech_list,
                champion_name,
                signature,
                loading=loading,
                empty_title=empty_title,
                empty_subtitle=empty_subtitle,
            ),
        )

    def _show_impl(self, hextech_list, champion_name=None, signature=None, loading=False, empty_title="", empty_subtitle=""):
        if self.visible and signature is not None and signature == self._last_show_signature:
            return
        self._active_champion_name = champion_name
        self._refresh_list(
            hextech_list,
            loading=loading,
            empty_title=empty_title,
            empty_subtitle=empty_subtitle,
        )
        self._anchor_top_right()
        # 先强制隐藏预览窗口，再显示海克斯窗口
        if self.preview_root is not None:
            self.preview_root.withdraw()
            self.preview_visible = False
            self._last_preview_show_signature = None
        self.root.deiconify()
        self.root.lift()
        self.root.attributes("-topmost", True)
        self._pin_window_topmost()
        self.visible = True
        if signature is not None:
            self._last_show_signature = signature

    def hide(self):
        if self.root is None:
            return
        self.root.after(0, self._hide_impl)

    def _hide_impl(self):
        self.root.withdraw()
        self.visible = False
        self._last_show_signature = None

    def show_preview(self, champion_name, reco_rows, loading=False, candidate_champions=None):
        if self.root is None:
            return
        candidate_rows = self._get_candidate_strength_rows(candidate_champions)
        self.root.after(
            0,
            lambda: self._show_preview_impl(
                champion_name,
                reco_rows,
                loading,
                candidate_rows=candidate_rows,
            ),
        )

    def _show_preview_impl(self, champion_name, reco_rows, loading=False, candidate_rows=None):
        if self.preview_root is None:
            return
        # 构建预览签名用于去重，避免重复刷新和位置重置
        preview_sig = (
            str(champion_name or "").strip(),
            bool(loading),
            tuple(
                (
                    str(r.get("name", "")).strip(),
                    str(r.get("icon_url", "")).strip(),
                    str(r.get("rarity", "")).strip().lower(),
                    str(r.get("grade", "")).upper(),
                    str(r.get("tier", "")).strip(),
                    str(r.get("tags", "")).strip(),
                    str(r.get("combo_text", "")).strip(),
                )
                for r in (reco_rows or [])
            ),
            self._build_candidate_strength_signature(candidate_rows),
            self._build_combo_signature(champion_name),
        )
        if self.preview_visible and preview_sig == self._last_preview_show_signature:
            return
        self._refresh_preview_list(
            champion_name,
            reco_rows or [],
            loading=loading,
            candidate_rows=candidate_rows,
        )
        if not self.preview_visible:
            self._anchor_preview_top_right()
        if self.preview_canvas is not None:
            try:
                self.preview_canvas.yview_moveto(0.0)
            except Exception:
                pass
        # 先强制隐藏海克斯窗口，再显示预览窗口
        self.root.withdraw()
        self.visible = False
        self._last_show_signature = None
        self.preview_root.deiconify()
        self.preview_root.lift()
        self.preview_root.attributes("-topmost", True)
        self.preview_visible = True
        self._last_preview_show_signature = preview_sig

    def hide_preview(self):
        if self.root is None:
            return
        self.root.after(0, self._hide_preview_impl)

    def _hide_preview_impl(self):
        if self.preview_root is None:
            return
        self.preview_root.withdraw()
        self.preview_visible = False
        self._last_preview_show_signature = None

    def start(self):
        t = threading.Thread(target=self._build_window, daemon=True)
        t.start()
        time.sleep(0.5)  # 等待窗口初始化


# 全局浮窗实例
overlay = HextechOverlay()
BASE_DIR = APP_BASE_DIR
HEXTECH_CACHE_PATH = os.path.join(BASE_DIR, HEXTECH_CACHE_FILE_NAME)
HEXTECH_AUGMENT_INDEX_PATH = os.path.join(BASE_DIR, HEXTECH_AUGMENT_INDEX_FILE_NAME)
hextech_provider = ApexHextechProvider(HEXTECH_CACHE_PATH, augment_index_path=HEXTECH_AUGMENT_INDEX_PATH)


def main():
    setup_logging()
    sys.stdout = QuietStream(sys.stdout, allow_prefixes=("[LCU] 当前悬停/选择英雄:", "[Startup]", "[Source]", "[Log]"))
    sys.stderr = QuietStream(sys.stderr, allow_prefixes=("[LCU] 当前悬停/选择英雄:", "[Startup]", "[Source]", "[Log]"))
    print("=" * 50)
    print("PotatoHex - 简化版")
    print(f"功能：大厅选人预览 + 游戏内按{HEXTECH_MANUAL_TRIGGER_NAME}手动识别海克斯")
    print("=" * 50)
    print()
    if not is_running_as_admin():
        print("[Startup] 当前未以管理员权限运行。游戏内热键可能被 LoL 拦截。")
    print("[Startup] 如需在游戏画面上稳定显示悬浮窗，建议将 LoL 调整为无边框或窗口模式。")
    # 启动浮窗线程
    hextech_provider.start()
    overlay.start()
    hextech_provider.request_refresh(force_index=True)
    if HEXTECH_PREFETCH_ALL_AUGMENTS_ON_START:
        threading.Thread(target=hextech_provider.prefetch_all_champions, daemon=True).start()
    client_was_running = False
    game_was_running = False
    last_champ = None
    last_valid_champ = None
    last_lobby_heartbeat = 0
    last_preview_champ = None
    last_preview_signature = None
    last_champ_select_active = False
    last_hotkey_enabled = None
    manual_scan_state = {
        "running": False,
        "hotkey_down": False,
        "last_trigger_ts": 0.0,
        "epoch": 0,
    }
    hotkey_runtime = {
        "enabled": False,
        "last_valid_champ": None,
    }

    def _normalize_live_rows(rows):
        live_rows = list(rows or [])[:3]
        while len(live_rows) < 3:
            ix = len(live_rows) + 1
            live_rows.append({
                "index": ix,
                "name": f"选项{ix} 未识别",
                "grade_label": "无评级",
                "match_pct": 0,
                "tag_text": "无标签",
                "author_text": "",
            })
        return live_rows

    def _invalidate_manual_scan():
        manual_scan_state["epoch"] += 1
        manual_scan_state["running"] = False
        manual_scan_state["hotkey_down"] = False
        manual_scan_state["last_trigger_ts"] = 0.0

    def _start_manual_hextech_scan(champion_name):
        if manual_scan_state["running"]:
            hotkey_log("[Hotkey] 忽略触发：当前已有识别任务正在运行")
            return
        manual_scan_state["running"] = True
        scan_epoch = manual_scan_state["epoch"]
        champion_snapshot = champion_name
        display_name = champion_snapshot.split("|", 1)[0] if isinstance(champion_snapshot, str) and "|" in champion_snapshot else champion_snapshot
        hotkey_log(f"[Hotkey] 检测到{HEXTECH_MANUAL_TRIGGER_NAME}，开始手动识别海克斯" + (f"（当前英雄：{display_name}）" if display_name else ""))
        overlay.hide_preview()
        overlay.show(
            [],
            champion_name=champion_snapshot,
            loading=True,
            empty_title="海克斯识别中...",
            empty_subtitle="已捕获触发，正在OCR识别当前3个海克斯，请稍候...",
        )

        def _worker():
            try:
                screenshot = capture_game_screen()
                if scan_epoch != manual_scan_state["epoch"]:
                    return
                if screenshot is None:
                    hotkey_log("[Hotkey] 手动识别失败：截图为空")
                    overlay.show(
                        [],
                        champion_name=champion_snapshot,
                        loading=False,
                        empty_title="截图失败",
                        empty_subtitle="未能截取到游戏画面，请重试。",
                    )
                    return

                champion_pool = hextech_provider.get_champion_recommendation_pool(champion_snapshot)
                live_rows, _ocr_offer_debug = detect_hextech_offers_by_ocr(
                    screenshot,
                    champion_pool,
                    champion_name=champion_snapshot,
                )
                if scan_epoch != manual_scan_state["epoch"]:
                    return
                if not live_rows:
                    hotkey_log("[Hotkey] 手动识别完成：未识别到海克斯")
                    overlay.show(
                        [],
                        champion_name=champion_snapshot,
                        loading=False,
                        empty_title="未识别到海克斯",
                        empty_subtitle=f"请在海克斯选择页面按{HEXTECH_MANUAL_TRIGGER_NAME}触发识别。",
                    )
                    return

                hotkey_log(f"[Hotkey] 手动识别完成：识别到 {len(live_rows)} 个海克斯")
                overlay.show(_normalize_live_rows(live_rows), champion_name=champion_snapshot)
            except Exception as e:
                hotkey_log(f"[Hotkey] 手动海克斯识别异常: {e}")
                if scan_epoch == manual_scan_state["epoch"]:
                    overlay.show(
                        [],
                        champion_name=champion_snapshot,
                        loading=False,
                        empty_title="识别失败",
                        empty_subtitle=str(e),
                    )
            finally:
                if scan_epoch == manual_scan_state["epoch"]:
                    manual_scan_state["running"] = False

        threading.Thread(target=_worker, daemon=True).start()

    def _toggle_manual_hextech_overlay():
        if manual_scan_state["running"] or overlay.visible:
            hotkey_log(f"[Hotkey] 检测到{HEXTECH_MANUAL_TRIGGER_NAME}，关闭海克斯悬浮窗")
            _invalidate_manual_scan()
            overlay.hide()
            return
        _start_manual_hextech_scan(hotkey_runtime["last_valid_champ"])

    def _manual_hotkey_loop():
        prev_down = False
        while True:
            try:
                key_down = is_any_virtual_key_down(HEXTECH_MANUAL_TRIGGER_VKS)
                manual_scan_state["hotkey_down"] = key_down
                if not hotkey_runtime["enabled"]:
                    prev_down = key_down
                    time.sleep(HEXTECH_HOTKEY_POLL_INTERVAL)
                    continue
                if key_down and not prev_down:
                    now = time.time()
                    if (now - float(manual_scan_state["last_trigger_ts"] or 0.0)) >= HEXTECH_MANUAL_TRIGGER_COOLDOWN:
                        manual_scan_state["last_trigger_ts"] = now
                        _toggle_manual_hextech_overlay()
                prev_down = key_down
            except Exception as e:
                hotkey_log(f"[Hotkey] 轮询监听线程异常: {e}")
            time.sleep(HEXTECH_HOTKEY_POLL_INTERVAL)

    def _manual_hotkey_low_level_hook_loop():
        if os.name != "nt":
            return
        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
        WH_KEYBOARD_LL = 13
        WM_KEYDOWN = 0x0100
        WM_KEYUP = 0x0101
        WM_SYSKEYDOWN = 0x0104
        WM_SYSKEYUP = 0x0105
        hook_handle = None
        hook_state = {"down": False}
        LowLevelKeyboardProc = ctypes.WINFUNCTYPE(
            wintypes.LRESULT,
            ctypes.c_int,
            wintypes.WPARAM,
            wintypes.LPARAM,
        )

        @LowLevelKeyboardProc
        def _hook_proc(n_code, w_param, l_param):
            try:
                if n_code >= 0:
                    message = int(w_param)
                    kb_info = ctypes.cast(l_param, ctypes.POINTER(KBDLLHOOKSTRUCT)).contents
                    matched = is_manual_trigger_key(vk_code=kb_info.vkCode, scan_code=kb_info.scanCode)
                    if matched and message in (WM_KEYUP, WM_SYSKEYUP):
                        hook_state["down"] = False
                        manual_scan_state["hotkey_down"] = False
                    elif matched and message in (WM_KEYDOWN, WM_SYSKEYDOWN):
                        manual_scan_state["hotkey_down"] = True
                        if not hook_state["down"]:
                            hook_state["down"] = True
                            if hotkey_runtime["enabled"]:
                                now = time.time()
                                if (now - float(manual_scan_state["last_trigger_ts"] or 0.0)) >= HEXTECH_MANUAL_TRIGGER_COOLDOWN:
                                    manual_scan_state["last_trigger_ts"] = now
                                    _toggle_manual_hextech_overlay()
            except Exception as e:
                hotkey_log(f"[Hotkey] 低层键盘钩子异常: {e}")
            return user32.CallNextHookEx(hook_handle, n_code, w_param, l_param)

        try:
            module_handle = kernel32.GetModuleHandleW(None)
            hook_handle = user32.SetWindowsHookExW(WH_KEYBOARD_LL, _hook_proc, module_handle, 0)
            if not hook_handle:
                err = ctypes.get_last_error()
                hotkey_log(f"[Hotkey] 低层键盘钩子注册失败: error={err}")
                return
            hotkey_log(f"[Hotkey] 已注册低层键盘钩子监听: {HEXTECH_MANUAL_TRIGGER_NAME}")
            msg = wintypes.MSG()
            while True:
                result = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if result == 0:
                    break
                if result == -1:
                    err = ctypes.get_last_error()
                    hotkey_log(f"[Hotkey] 低层键盘钩子消息循环失败: error={err}")
                    break
        except Exception as e:
            hotkey_log(f"[Hotkey] 低层键盘钩子监听异常: {e}")
        finally:
            if hook_handle:
                try:
                    user32.UnhookWindowsHookEx(hook_handle)
                except Exception:
                    pass

    def _manual_hotkey_message_loop():
        if os.name != "nt":
            return
        user32 = ctypes.windll.user32
        WM_HOTKEY = 0x0312
        registered = []
        try:
            for idx, vk_code in enumerate(HEXTECH_MANUAL_TRIGGER_VKS, 1):
                try:
                    ok = bool(user32.RegisterHotKey(None, idx, 0, int(vk_code)))
                except Exception:
                    ok = False
                if ok:
                    registered.append((idx, vk_code))
                    hotkey_log(f"[Hotkey] 已注册系统热键监听: {HEXTECH_MANUAL_TRIGGER_NAME}, vk=0x{int(vk_code):02X}")
                else:
                    err = ctypes.get_last_error()
                    hotkey_log(f"[Hotkey] 系统热键注册失败: vk=0x{int(vk_code):02X}, error={err}")

            if not registered:
                hotkey_log("[Hotkey] 未注册到任何系统热键，继续使用轮询监听回退。")
                return

            msg = wintypes.MSG()
            while True:
                result = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if result == 0:
                    break
                if result == -1:
                    err = ctypes.get_last_error()
                    hotkey_log(f"[Hotkey] GetMessageW 失败: error={err}")
                    break
                if msg.message == WM_HOTKEY:
                    if not hotkey_runtime["enabled"]:
                        continue
                    now = time.time()
                    if (now - float(manual_scan_state["last_trigger_ts"] or 0.0)) >= HEXTECH_MANUAL_TRIGGER_COOLDOWN:
                        manual_scan_state["last_trigger_ts"] = now
                        _toggle_manual_hextech_overlay()
        except Exception as e:
            hotkey_log(f"[Hotkey] 系统热键监听异常: {e}")
        finally:
            for hotkey_id, _vk in registered:
                try:
                    user32.UnregisterHotKey(None, int(hotkey_id))
                except Exception:
                    pass

    threading.Thread(target=_manual_hotkey_loop, daemon=True).start()
    threading.Thread(target=_manual_hotkey_low_level_hook_loop, daemon=True).start()
    threading.Thread(target=_manual_hotkey_message_loop, daemon=True).start()

    try:
        while True:
            client_running = is_league_client_running()
            game_running = is_game_running()
            hotkey_runtime["enabled"] = bool(client_running or game_running)
            hotkey_runtime["last_valid_champ"] = last_valid_champ
            if hotkey_runtime["enabled"] != last_hotkey_enabled:
                hotkey_log(
                    f"[Hotkey] 热键启用状态变更: enabled={hotkey_runtime['enabled']}, "
                    f"client_running={client_running}, game_running={game_running}"
                )
                last_hotkey_enabled = hotkey_runtime["enabled"]
            def _reset_match_state():
                nonlocal last_champ, last_valid_champ, last_preview_champ, last_preview_signature, last_champ_select_active, last_hotkey_enabled
                last_champ = None
                last_valid_champ = None
                last_preview_champ = None
                last_preview_signature = None
                last_champ_select_active = False
                hotkey_runtime["last_valid_champ"] = None
                last_hotkey_enabled = None

            # 大厅状态变化
            if client_running:
                if not client_was_running:
                    print("[Startup] 找到大厅！LeagueClient.exe 已启动")
                    client_was_running = True
            else:
                if client_was_running:
                    client_was_running = False
                    game_was_running = False
                    hotkey_runtime["enabled"] = False
                    _invalidate_manual_scan()
                    _reset_match_state()
                    overlay.hide()
                    overlay.hide_preview()
                    last_lobby_heartbeat = 0
                time.sleep(2)
                continue
            # 大厅选角色阶段：轮询 LCU API
            if not game_running:
                if game_was_running:
                    game_was_running = False
                    _invalidate_manual_scan()
                    _reset_match_state()
                    overlay.hide()
                    overlay.hide_preview()
                    last_lobby_heartbeat = 0
                port, token = get_lcu_credentials()
                if not port:
                    last_champ = "__no_cred__"
                else:
                    load_champion_map(port, token)
                    champ_select_details = get_champ_select_details()
                    champ_select_active = bool(champ_select_details.get("active"))
                    champ = champ_select_details.get("current_champion")
                    candidate_champs = list(champ_select_details.get("candidate_champions") or [])
                    if champ_select_active and not last_champ_select_active:
                        overlay.show_preview("", [], loading=True, candidate_champions=candidate_champs)
                        last_preview_signature = "__loading__"
                        last_preview_champ = None
                    last_champ_select_active = champ_select_active
                    if champ:
                        if champ != last_champ:
                            display_champ = champ.split("|", 1)[0] if "|" in champ else champ
                            print(f"[LCU] 当前悬停/选择英雄: {display_champ}")
                            if not display_champ.startswith("ID:"):
                                if (not HEXTECH_FETCH_ONLY_IF_MISSING) or (not hextech_provider.has_champion_data(champ)):
                                    hextech_provider.request_refresh(champion_name=champ)
                                elif hextech_provider.should_refresh_due_to_parse_upgrade(champ):
                                    hextech_provider.request_refresh(champion_name=champ)
                                elif hextech_provider.should_try_items_backfill(champ):
                                    hextech_provider.request_refresh(champion_name=champ)
                                hextech_provider.get_recommendations(champ, limit=HEXTECH_OVERLAY_TOP_N)
                        # Draft preview: refresh not only on hero change, but also when data changes.
                        display_champ = champ.split("|", 1)[0] if "|" in champ else champ
                        has_cached = hextech_provider.has_champion_data(champ)
                        all_rows = hextech_provider.get_champion_recommendation_pool(champ)
                        preview_pool = build_preview_rows_with_combos(all_rows, top_n=max(len(all_rows or []), 1))
                        for rr in preview_pool:
                            rr["items"] = build_items_for_row(rr, preview_pool, max_count=4)
                            rr["items_text"] = " + ".join(rr["items"]) if rr.get("items") else ""
                        top_rows = [
                            x for x in preview_pool
                            if str(x.get("tier_label") or x.get("tier") or "").strip().upper() == "T1"
                        ]
                        if not top_rows:
                            top_rows = [x for x in preview_pool if str(x.get("grade", "")).upper() in {"SSS", "SS", "S", "A"}]
                        top_rows = sorted(
                            top_rows,
                            key=lambda x: (
                                int(x.get("website_rank", 9999) or 9999),
                                -int(x.get("score", 0) or 0),
                            ),
                        )
                        sig = (
                            champ,
                            tuple(str(x).strip() for x in candidate_champs),
                            tuple(
                                (
                                    str(r.get("name", "")).strip(),
                                    str(r.get("grade", "")).upper(),
                                    str(r.get("tier", "")).strip(),
                                    str(r.get("tags", "")).strip(),
                                    str(r.get("combo_text", "")).strip(),
                                )
                                for r in top_rows
                            ),
                        )
                        if top_rows and sig != last_preview_signature:
                            overlay.show_preview(
                                display_champ,
                                top_rows,
                                loading=(not has_cached),
                                candidate_champions=candidate_champs,
                            )
                            last_preview_signature = sig
                            last_preview_champ = champ
                        elif has_cached and sig != last_preview_signature:
                            overlay.show_preview(
                                display_champ,
                                top_rows,
                                loading=False,
                                candidate_champions=candidate_champs,
                            )
                            last_preview_signature = sig
                            last_preview_champ = champ
                        last_champ = champ
                        last_valid_champ = champ
                        hotkey_runtime["last_valid_champ"] = champ
                    else:
                        if last_champ != "__no_champ__":
                            if last_valid_champ:
                                keep_name = last_valid_champ.split("|", 1)[0]
                                print(f"[LCU] 当前未选择任何英雄，沿用最近英雄: {keep_name}")
                            else:
                                print("[LCU] 当前未选择任何英雄")
                        last_champ = "__no_champ__"
                        last_preview_champ = None
                        if not champ_select_active:
                            last_preview_signature = None
                        if champ_select_active:
                            overlay.show_preview("", [], loading=True, candidate_champions=candidate_champs)
                        else:
                            overlay.hide_preview()
                time.sleep(1)
                continue
            if game_running:
                if not game_was_running:
                    print("[OK] 游戏已启动！")
                    print(f"[Hotkey] 在海克斯选择页面按{HEXTECH_MANUAL_TRIGGER_NAME}即可手动识别当前3个海克斯")
                    game_was_running = True
                    _invalidate_manual_scan()
                    overlay.hide_preview()
                    last_preview_signature = None
                    last_champ_select_active = False
            idle_interval = HEXTECH_IN_GAME_MAIN_LOOP_INTERVAL if game_running else HEXTECH_MAIN_LOOP_INTERVAL
            time.sleep(idle_interval)
    except KeyboardInterrupt:
        print("\n[*] 程序已中断")
        sys.exit(0)
    except Exception as e:
        print(f"[Fatal] 主循环异常退出: {e}")
        traceback.print_exc()
        raise


if __name__ == "__main__":
    main()
