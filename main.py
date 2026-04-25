#!/usr/bin/env python3
"""
PotatoHex (provider source)

Reuse hextech_core OCR/LCU/overlay pipeline, but swap provider to the web data source.
"""

import contextlib
import difflib
import html
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from urllib.parse import quote


def _ensure_runtime_dependencies():
    required_modules = {
        "cv2": "opencv-python",
        "numpy": "numpy",
        "PIL": "Pillow",
        "requests": "requests",
        "urllib3": "urllib3",
    }
    missing = [pkg for mod, pkg in required_modules.items() if importlib.util.find_spec(mod) is None]
    if not missing:
        return True

    if getattr(sys, "frozen", False):
        print(f"[Fatal] 打包环境缺少模块: {', '.join(missing)}")
        return False

    print("[Startup] 检测到环境包缺失，正在安装环境包...")
    print(f"[Startup] 缺失模块: {', '.join(missing)}")
    req_path = Path(__file__).resolve().with_name("requirements.txt")
    if not req_path.exists():
        print(f"[Fatal] 找不到 requirements.txt: {req_path}")
        return False

    cmd = [sys.executable, "-m", "pip", "install", "-r", str(req_path)]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
    except Exception as e:
        print(f"[Fatal] 环境包安装启动失败: {e}")
        return False

    if result.returncode != 0:
        tail = "\n".join((result.stdout or "").splitlines()[-20:] + (result.stderr or "").splitlines()[-20:])
        if tail.strip():
            print(tail)
        print("[Fatal] 环境包安装失败")
        return False

    print("[Startup] 环境包安装完成")
    return True


if not _ensure_runtime_dependencies():
    raise SystemExit(1)

import requests

with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    import hextech_core as app


SOURCE_BASE_URL = "https://aramgg.com"
ARAMGG_BASE_URL = SOURCE_BASE_URL
SOURCE_CHAMPION_STATS_JSON = f"{SOURCE_BASE_URL}/data/champions-stats.json"
SOURCE_AUGMENT_META_JSON = f"{SOURCE_BASE_URL}/data/aram-mayhem-augments.zh_cn.json"
SOURCE_AUGMENT_ICON_BASE_URL = "https://cdn.dtodo.cn/hextech/augment-icons"

__author__ = "则暮"
__version__ = "1.0.0"


def _to_float_safe(v, mul=1.0):
    try:
        return float(v) * float(mul)
    except Exception:
        return None


def _normalize_percent_value(v):
    try:
        num = float(v)
    except Exception:
        return None
    if abs(num) <= 1.0:
        num *= 100.0
    return num


def _build_augment_icon_url(icon_filename):
    raw = os.path.basename(str(icon_filename or "").strip().replace("\\", "/"))
    if not raw:
        return ""
    file_name = raw.lower()
    if "." not in file_name:
        file_name = f"{file_name}.png"
    return f"{SOURCE_AUGMENT_ICON_BASE_URL}/{quote(file_name)}"


def _augment_rarity_label(rarity_value):
    try:
        value = int(rarity_value)
    except Exception:
        value = -1
    if value == 2:
        return "prismatic"
    if value == 1:
        return "gold"
    if value == 0:
        return "silver"
    return ""


def _extract_lines_text(html_content):
    text = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", html_content)
    text = re.sub(r"(?is)<br\s*/?>", "\n", text)
    text = re.sub(r"(?is)</(p|div|li|h1|h2|h3|h4|h5|h6|tr|td|section|article|span)>", "\n", text)
    text = re.sub(r"(?is)<[^>]+>", " ", text)
    text = html.unescape(text)
    out = []
    for ln in text.splitlines():
        c = re.sub(r"\s+", " ", ln).strip()
        if c:
            out.append(c)
    return out


def _extract_next_flight_json_objects(html_content):
    """
    Extract self.__next_f.push payload chunks from the RSC/flight stream.
    Returns decoded JSON objects/arrays when possible.
    """
    if not html_content:
        return []
    results = []
    for m in re.finditer(r'self\.__next_f\.push\(\[1,"((?:\\.|[^"\\])*)"\]\)</script>', html_content):
        raw = m.group(1)
        try:
            decoded = bytes(raw, "utf-8").decode("unicode_escape")
        except Exception:
            continue
        try:
            obj = json.loads(decoded)
        except Exception:
            continue
        results.append(obj)
    return results


def _extract_next_flight_chunks(html_content):
    if not html_content:
        return []
    chunks = []
    for m in re.finditer(r'self\.__next_f\.push\(\[1,"((?:\\.|[^"\\])*)"\]\)</script>', html_content):
        raw = m.group(1)
        try:
            decoded = bytes(raw, "utf-8").decode("unicode_escape")
        except Exception:
            continue
        chunks.append(decoded)
    return chunks


def _find_rsc_reference_payload(html_content, ref_token):
    """
    Best-effort resolver for $24-like references inside Next.js flight payloads.
    """
    if not html_content or not ref_token:
        return None
    token = str(ref_token).strip()
    if not token.startswith("$"):
        token = f"${token}"

    for obj in _extract_next_flight_json_objects(html_content):
        text = json.dumps(obj, ensure_ascii=False)
        if token not in text:
            continue
        # Fast path: return the raw object text and let the caller mine the augments field.
        return obj
    return None


def _extract_augments_map_from_rsc_payload(html_content):
    """
    Return the per-champion augments map embedded in the Next.js flight payload.
    """
    if not html_content:
        return {}
    for chunk in _extract_next_flight_chunks(html_content):
        if '{"augments":{' not in chunk:
            continue
        start = chunk.find('{"augments":{')
        if start < 0:
            continue
        payload_text = chunk[start:]
        end = payload_text.rfind("}")
        if end < 0:
            continue
        try:
            payload = json.loads(payload_text[: end + 1])
        except Exception:
            continue
        if isinstance(payload, dict) and isinstance(payload.get("augments"), dict):
            return payload.get("augments", {})
    return {}


_TIER_RANK = {"T1": 1, "T2": 2, "T3": 3, "T4": 4, "T5": 5}


def _tier_badge_style(grade_raw):
    g = str(grade_raw or "").strip().upper()
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
    if re.match(r"^TOP\d+$", g):
        return g, "#16345f", "#9ac0ff"
    return g or "未知", "#16345f", "#9ac0ff"


def _combo_rating_label(member_rows):
    ranks = []
    for r in member_rows or []:
        tier = str(r.get("tier_label") or "").strip().upper()
        if tier in _TIER_RANK:
            ranks.append(_TIER_RANK[tier])
    if not ranks:
        return "T3"
    avg = sum(ranks) / len(ranks)
    idx = int(round(avg))
    idx = max(1, min(5, idx))
    for k, v in _TIER_RANK.items():
        if v == idx:
            return k
    return "T3"


def _make_scrollable_combo_box(parent, bg, accent, title_text, title_fg="#dff3ff"):
    outer = app.tk.Frame(
        parent,
        bg=bg,
        highlightbackground=accent,
        highlightthickness=1,
        padx=8,
        pady=6,
    )
    outer.pack(fill="both", expand=True, pady=(0, 6), padx=8)
    outer.pack_propagate(False)

    title = app.tk.Label(
        outer,
        text=title_text,
        bg=bg,
        fg=title_fg,
        font=("Microsoft YaHei", 9, "bold"),
        anchor="w",
    )
    title.pack(fill="x")

    body = app.tk.Frame(outer, bg=bg)
    body.pack(fill="both", expand=True, pady=(4, 0))
    canvas = app.tk.Canvas(body, bg=bg, highlightthickness=0, bd=0)
    scrollbar = app.ttk.Scrollbar(body, orient="vertical", command=canvas.yview)
    canvas.configure(yscrollcommand=scrollbar.set)
    scrollbar.pack(side="right", fill="y")
    canvas.pack(side="left", fill="both", expand=True)
    inner = app.tk.Frame(canvas, bg=bg)
    window_id = canvas.create_window((0, 0), window=inner, anchor="nw")

    def _sync_scrollregion(_event=None):
        try:
            canvas.configure(scrollregion=canvas.bbox("all"))
        except Exception:
            pass

    def _sync_width(event):
        try:
            canvas.itemconfigure(window_id, width=event.width)
        except Exception:
            pass

    def _is_inside(widget):
        cur = widget
        while cur is not None:
            if cur is outer:
                return True
            cur = getattr(cur, "master", None)
        return False

    inner.bind("<Configure>", _sync_scrollregion)
    canvas.bind("<Configure>", _sync_width)

    def _mousewheel(event):
        try:
            if not _is_inside(getattr(event, "widget", None)):
                return
            delta = 0
            if hasattr(event, "delta") and event.delta:
                delta = -1 * int(event.delta / 120) if event.delta != 0 else 0
            elif getattr(event, "num", None) == 4:
                delta = -1
            elif getattr(event, "num", None) == 5:
                delta = 1
            if delta != 0:
                canvas.yview_scroll(delta, "units")
        except Exception:
            pass

    canvas.bind_all("<MouseWheel>", _mousewheel, add="+")
    canvas.bind_all("<Button-4>", _mousewheel, add="+")
    canvas.bind_all("<Button-5>", _mousewheel, add="+")
    return outer, inner


class SourceHextechProvider(app.ApexHextechProvider):
    def __init__(self, cache_path, augment_index_path=None):
        self.cache_path = cache_path
        self.augment_index_path = augment_index_path or os.path.join(
            os.path.dirname(os.path.abspath(cache_path)),
            app.HEXTECH_AUGMENT_INDEX_FILE_NAME,
        )
        self._lock = app.threading.Lock()
        self._stop_event = app.threading.Event()
        self._refresh_pending = set()
        self._data = {
            "meta": {
                "source": "aramgg.com",
                "last_index_refresh": 0,
                "last_data_refresh": 0,
                "parse_schema_version": app.HEXTECH_PARSE_SCHEMA_VERSION,
            },
            "slug_map": {},
            "name_to_slug": {},
            "champions": {},
        }
        self._augment_index = {
            "meta": {"source": "aramgg.com", "updated_at": 0},
            "items": {},
        }
        self._champion_stats = {}
        self._augment_meta = {}
        self._augment_name_meta = {}
        self._live_cache_ttl = 300
        self._data["meta"]["source"] = "aramgg.com"
        self._augment_index["meta"]["source"] = "aramgg.com"

    def _save_cache_locked(self):
        # Intentionally disabled: champion recommendations are fetched live per session.
        return

    def _save_augment_index_locked(self):
        # Intentionally disabled: augment index stays in memory only.
        return

    def _http_get_json(self, url):
        headers = {
            "User-Agent": "hextech-assistant/1.0 (source provider)",
            "Accept": "application/json,text/plain,*/*",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
            "Referer": f"{ARAMGG_BASE_URL}/zh-CN",
        }
        try:
            resp = requests.get(url, headers=headers, timeout=app.HEXTECH_HTTP_TIMEOUT)
            if resp.status_code == 200:
                return resp.json()
            app.log_status("source_http_json_fail", f"[Source] JSON失败: {url}, HTTP {resp.status_code}", interval=15)
        except Exception as e:
            app.log_status("source_http_json_err", f"[Source] JSON异常: {url}, error={e}", interval=15)
        return None

    def _load_augment_name_meta(self):
        payload = self._http_get_json(SOURCE_AUGMENT_META_JSON)
        if not isinstance(payload, dict) or not payload:
            return {}
        meta = {}
        for k, v in payload.items():
            if not isinstance(v, dict):
                continue
            aug_id = str(v.get("id", k)).strip()
            if not aug_id:
                continue
            name = str(v.get("displayName") or v.get("name") or "").strip()
            icon_large_url = _build_augment_icon_url(v.get("iconLarge"))
            icon_small_url = _build_augment_icon_url(v.get("iconSmall"))
            rarity_value = v.get("rarity")
            meta[aug_id] = {
                "name": name,
                "icon_url": icon_large_url or icon_small_url,
                "icon_small_url": icon_small_url,
                "icon_large_url": icon_large_url,
                "rarity_value": rarity_value,
                "rarity": _augment_rarity_label(rarity_value),
            }
        return meta

    def _dump_debug_page(self, slug, title_text, html_content, reco_rows, combo_rows):
        try:
            base_dir = os.path.dirname(os.path.abspath(self.cache_path))
            debug_dir = os.path.join(base_dir, "source_debug")
            os.makedirs(debug_dir, exist_ok=True)
            lines = _extract_lines_text(html_content)
            path = os.path.join(debug_dir, f"champion_{slug}.txt")
            with open(path, "w", encoding="utf-8") as f:
                f.write(f"title: {title_text}\n")
                f.write(f"url: {SOURCE_BASE_URL}/zh-CN/champion-stats/{slug}\n")
                f.write("\n[RAW LINES]\n")
                for ln in lines[:1200]:
                    f.write(ln + "\n")
                f.write("\n[RECOMMENDATION ROWS]\n")
                for row in reco_rows:
                    f.write(json.dumps(row, ensure_ascii=False) + "\n")
                f.write("\n[COMBO ROWS]\n")
                for row in combo_rows:
                    f.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(f"[Source] 调试页已导出: {path}")
        except Exception as e:
            app.log_status("source_dump_debug_error", f"[Source] 导出调试页失败: {e}", interval=30)

    def _seed_name_to_slug_from_lcu_locked(self):
        champ_map = getattr(app, "_champion_map", {}) or {}
        if not isinstance(champ_map, dict):
            return
        for champ_id, info in champ_map.items():
            slug = str(champ_id)
            if slug not in self._data.get("slug_map", {}):
                continue
            if isinstance(info, dict):
                for raw in (info.get("name", ""), info.get("alias", "")):
                    k = app.normalize_name_key(raw)
                    if k:
                        self._data["name_to_slug"][k] = slug

    def _refresh_index(self):
        payload = self._http_get_json(SOURCE_CHAMPION_STATS_JSON)
        if not isinstance(payload, list) or not payload:
            return

        slug_map = {}
        name_to_slug = {}
        stats_map = {}
        for row in payload:
            if not isinstance(row, dict):
                continue
            champ_id = str(row.get("championId", "")).strip()
            if not champ_id.isdigit():
                continue
            slug_map[champ_id] = f"{ARAMGG_BASE_URL}/zh-CN/champion-stats/{champ_id}"
            name_to_slug[app.normalize_name_key(champ_id)] = champ_id
            stats_map[champ_id] = row

        if not slug_map:
            return

        with self._lock:
            self._data["slug_map"] = slug_map
            self._data["name_to_slug"].update(name_to_slug)
            self._seed_name_to_slug_from_lcu_locked()
            self._champion_stats = stats_map
            self._data["meta"]["last_index_refresh"] = time.time()
            self._data["meta"]["source"] = "aramgg.com"
            self._save_cache_locked()
        print(f"[Source] 英雄索引已更新: {len(slug_map)} 个")

    def _try_resolve_slug_from_lcu(self, display_name, alias_key):
        champ_map = getattr(app, "_champion_map", {}) or {}
        display_key = app.normalize_name_key(display_name)
        alias_key = app.normalize_name_key(alias_key)
        for champ_id, info in champ_map.items():
            slug = str(champ_id)
            if slug not in self._data.get("slug_map", {}):
                continue
            if not isinstance(info, dict):
                continue
            name_key = app.normalize_name_key(info.get("name", ""))
            eng_key = app.normalize_name_key(info.get("alias", ""))
            if alias_key and alias_key in {name_key, eng_key}:
                return slug
            if display_key and display_key in {name_key, eng_key}:
                return slug
        return None

    def _refresh_champion_by_name(self, champion_name):
        if not champion_name:
            return
        alias_key = ""
        display_name = champion_name
        if "|" in champion_name:
            left, right = champion_name.split("|", 1)
            display_name = left.strip() or champion_name
            alias_key = app.normalize_name_key(right)
        display_key = app.normalize_name_key(display_name)

        with self._lock:
            slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
            if not slug:
                slug = self._data["name_to_slug"].get(display_key)
            if not slug:
                self._seed_name_to_slug_from_lcu_locked()
                slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
                if not slug:
                    slug = self._data["name_to_slug"].get(display_key)
            if not slug:
                slug = self._try_resolve_slug_from_lcu(display_name, alias_key)
                if slug:
                    if alias_key:
                        self._data["name_to_slug"][alias_key] = slug
                    if display_key:
                        self._data["name_to_slug"][display_key] = slug

        if not slug:
            self._refresh_index()
            with self._lock:
                slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
                if not slug:
                    slug = self._data["name_to_slug"].get(display_key)
                if not slug:
                    slug = self._try_resolve_slug_from_lcu(display_name, alias_key)
        if not slug:
            app.log_status(f"source_slug_missing_{display_key}", f"[Source] 未匹配英雄: {display_name}", interval=30)
            return
        self._refresh_champion_by_slug(slug, display_name)

    def _get_live_entry(self, champion_name):
        if not champion_name:
            return None
        with self._lock:
            slug, _ = self._resolve_slug_locked(champion_name)
            entry = self._data.get("champions", {}).get(str(slug), {}) if slug else {}
            updated_at = float(entry.get("updated_at", 0) or 0)
            if entry and entry.get("recommendations") and (time.time() - updated_at) <= self._live_cache_ttl:
                return dict(entry)
        self._refresh_champion_by_name(champion_name)
        with self._lock:
            slug, _ = self._resolve_slug_locked(champion_name)
            entry = self._data.get("champions", {}).get(str(slug), {}) if slug else {}
            return dict(entry) if entry else None

    def has_champion_data(self, champion_name):
        entry = self._get_live_entry(champion_name)
        return bool(entry and entry.get("recommendations"))

    def get_champion_strength(self, champion_name):
        if not champion_name or str(champion_name).startswith("ID:"):
            return None
        display_name = str(champion_name).split("|", 1)[0].strip() or str(champion_name).strip()
        slug = None
        stat_row = {}
        with self._lock:
            try:
                slug, _ = self._resolve_slug_locked(champion_name)
            except Exception:
                slug = None
            if slug:
                stat_row = dict(self._champion_stats.get(str(slug), {}))
        if not stat_row:
            self._refresh_index()
            with self._lock:
                try:
                    slug, _ = self._resolve_slug_locked(champion_name)
                except Exception:
                    slug = None
                if slug:
                    stat_row = dict(self._champion_stats.get(str(slug), {}))
        if not stat_row:
            return {
                "name": display_name,
                "tier_label": "",
                "win_rate": None,
                "pick_rate": None,
                "champion_id": str(slug or ""),
            }

        tier_raw = str(stat_row.get("tier", "")).strip()
        tier_label = f"T{tier_raw}" if tier_raw.isdigit() else ""
        win_rate = _normalize_percent_value(stat_row.get("winRate"))
        pick_rate = _normalize_percent_value(stat_row.get("pickRate"))
        return {
            "name": display_name,
            "tier_label": tier_label,
            "win_rate": win_rate,
            "pick_rate": pick_rate,
            "champion_id": str(slug or stat_row.get("championId", "") or ""),
        }

    def get_champion_strengths(self, champion_names):
        rows = []
        seen = set()
        for champion_name in champion_names or []:
            display_name = str(champion_name).split("|", 1)[0].strip() or str(champion_name).strip()
            key = app.normalize_name_key(display_name)
            if not key or key in seen:
                continue
            seen.add(key)
            info = self.get_champion_strength(champion_name)
            if isinstance(info, dict):
                rows.append(dict(info))
        return rows

    def get_champion_recommendation_pool(self, champion_name):
        entry = self._get_live_entry(champion_name)
        return list(entry.get("recommendations", []) or []) if entry else []

    def get_recommendations(self, champion_name, limit=6):
        return self.get_recommendations_for_tiers(champion_name, tiers=None, limit=limit)

    def get_recommendations_for_tiers(self, champion_name, tiers=None, limit=6):
        if not champion_name or champion_name.startswith("ID:") or champion_name == "__no_cred__":
            return [{
                "name": "等待选中英雄...",
                "tier": "白银",
                "score": 0,
                "tags": "状态",
                "note": "当前未获取到可用英雄",
            }]

        rows = self.get_champion_recommendation_pool(champion_name)
        if not rows:
            return [{
                "name": "数据加载中",
                "tier": "白银",
                "score": 0,
                "tags": "加载中",
                "note": "正在抓取当前英雄页面",
            }]

        allowed = {t for t in (tiers or set()) if t in {"棱彩", "黄金", "白银"}}
        if allowed:
            filtered = [x for x in rows if str(x.get("tier", "")) in allowed]
            if filtered:
                rows = filtered
        return rows[:limit]

    def _extract_top_augments_from_jsonld(self, html_content):
        rows = []
        seen = set()
        for m in re.finditer(r'(?is)<script[^>]*type=["\']application/ld\+json["\'][^>]*>(.*?)</script>', html_content):
            body = (m.group(1) or "").strip()
            if not body:
                continue
            try:
                obj = json.loads(body)
            except Exception:
                continue
            graph = []
            if isinstance(obj, dict) and isinstance(obj.get("@graph"), list):
                graph = obj.get("@graph", [])
            elif isinstance(obj, list):
                graph = obj
            elif isinstance(obj, dict):
                graph = [obj]
            for node in graph:
                if not isinstance(node, dict):
                    continue
                if str(node.get("@type", "")).strip() != "ItemList":
                    continue
                arr = node.get("itemListElement", [])
                if not isinstance(arr, list):
                    continue
                for it in arr:
                    if not isinstance(it, dict):
                        continue
                    url = str(it.get("url", "")).strip()
                    if "/augments/" not in url:
                        continue
                    name = str(it.get("name", "")).strip()
                    if not name:
                        continue
                    key = app.normalize_name_key(name)
                    if key in seen:
                        continue
                    seen.add(key)
                    mm = re.search(r"/augments/(\d+)", url)
                    aug_id = mm.group(1) if mm else ""
                    pos = it.get("position", len(rows) + 1)
                    try:
                        pos = int(pos)
                    except Exception:
                        pos = len(rows) + 1
                    rows.append({"name": name, "augment_id": aug_id, "position": pos, "url": url})
        rows.sort(key=lambda x: int(x.get("position", 999)))
        return rows[:12]

    def _extract_all_recommendation_rows_from_table(self, html_content):
        """
        Parse the full visible recommendation table from the SSR HTML.
        The page renders the whole table server-side; names are recovered from the
        augment detail pages because the table only exposes #ID, tier, win and pick rates.
        """
        if not html_content:
            return []

        # The page also contains a separate "推荐海克斯组合" table.
        # Keep the main recommendation parser scoped to the section before that table,
        # otherwise combo rows can be mistaken for normal recommendations.
        cutoff = html_content.find("推荐海克斯组合")
        if cutoff > 0:
            html_content = html_content[:cutoff]

        row_htmls = re.findall(r'(?is)<tr[^>]*data-slot="table-row"[^>]*>(.*?)</tr>', html_content)
        if not row_htmls:
            return []

        rows = []
        seen_ids = set()
        detail_cache = {}

        def _extract_tier_from_block(block):
            cleaned = re.sub(r"(?is)<!--.*?-->", " ", block or "")
            cleaned = re.sub(r"(?is)<[^>]+>", " ", cleaned)
            cleaned = html.unescape(re.sub(r"\s+", " ", cleaned)).strip()
            m = re.search(r"\bT\s*([1-5])\b", cleaned, re.I)
            if not m:
                m = re.search(r"\bT([1-5])\b", cleaned, re.I)
            if m:
                return f"T{m.group(1)}"
            return ""

        for row_html in row_htmls:
            rank_match = re.search(r'(?is)<span[^>]*class="[^"]*\bfont-bold\b[^"]*"[^>]*>\s*(\d+)\s*</span>', row_html)
            aug_match = re.search(r'(?is)href=["\']/zh-CN/augments/(\d+)["\']', row_html)
            if not aug_match:
                continue

            if rank_match:
                website_rank = int(rank_match.group(1))
            else:
                rank_fallback = re.search(r'(?is)<td[^>]*>\s*<span[^>]*>\s*(\d+)\s*</span>', row_html)
                if rank_fallback:
                    website_rank = int(rank_fallback.group(1))
                else:
                    raw_text = re.sub(r"(?is)<[^>]+>", " ", row_html)
                    raw_text = re.sub(r"\s+", " ", html.unescape(raw_text)).strip()
                    m = re.search(r"\b(\d{1,3})\b", raw_text)
                    if not m:
                        continue
                    website_rank = int(m.group(1))
            augment_id = aug_match.group(1)
            if augment_id in seen_ids:
                continue
            seen_ids.add(augment_id)

            tier_label = _extract_tier_from_block(row_html) or "T3"

            percents = [float(x) for x in re.findall(r'([0-9]+(?:\.[0-9]+)?)%', row_html)]
            win_rate = percents[0] if percents else None
            pick_rate = percents[-1] if len(percents) >= 2 else None

            meta = detail_cache.get(augment_id)
            if meta is None:
                meta = self._parse_augment_detail_page(augment_id)
                detail_cache[augment_id] = meta
            name = str((meta or {}).get("name", "")).strip()
            if not name:
                link_text = re.search(r'(?is)<a[^>]*href=["\']/zh-CN/augments/\d+["\'][^>]*>(.*?)</a>', row_html)
                if link_text:
                    raw = re.sub(r"(?is)<[^>]+>", " ", link_text.group(1))
                    raw = html.unescape(re.sub(r"\s+", " ", raw)).strip()
                    if raw and not re.fullmatch(r"#\s*\d+", raw):
                        name = raw
            if not name:
                name = f"#{augment_id}"

            rows.append(
                {
                    "name": name,
                    "augment_id": augment_id,
                    "url": f"{ARAMGG_BASE_URL}/zh-CN/augments/{augment_id}",
                    "icon_url": str((meta or {}).get("icon_url", "")).strip(),
                    "rarity": str((meta or {}).get("rarity", "")).strip(),
                    "website_rank": website_rank,
                    "tier_label": tier_label,
                    "win_rate": win_rate,
                    "pick_rate": pick_rate,
                }
            )

        rows.sort(key=lambda x: int(x.get("website_rank", 9999) or 9999))
        return rows

    def _extract_all_recommendation_rows_from_rsc(self, html_content, champion_id):
        """
        Parse the full champion augment stats from Next.js flight payload.
        This is the stable source for the hidden "显示全部" dataset.
        """
        augments = _extract_augments_map_from_rsc_payload(html_content)
        if not isinstance(augments, dict) or not augments:
            return []

        rows = []
        with self._lock:
            if not self._augment_name_meta:
                self._augment_name_meta = self._load_augment_name_meta()
            augment_meta = dict(self._augment_name_meta)

        sorted_items = sorted(
            augments.items(),
            key=lambda kv: (
                int(str(kv[1].get("tier", 9999) or 9999)),
                -float(_to_float_safe(kv[1].get("win_rate")) or 0.0),
            ),
        )
        for rank, (augment_id, stat) in enumerate(sorted_items, 1):
            if not isinstance(stat, dict):
                continue
            augment_id = str(augment_id).strip()
            if not augment_id:
                continue
            aug_meta = augment_meta.get(augment_id, {})
            rows.append(
                {
                    "augment_id": augment_id,
                    "name": str(aug_meta.get("name", "") or "").strip(),
                    "icon_url": str(aug_meta.get("icon_url", "") or "").strip(),
                    "rarity": str(aug_meta.get("rarity", "") or "").strip(),
                    "website_rank": rank,
                    "tier_label": f"T{str(stat.get('tier', '')).strip()}" if str(stat.get("tier", "")).strip().isdigit() else "T3",
                    "win_rate": _to_float_safe(stat.get("win_rate")),
                    "pick_rate": _to_float_safe(stat.get("pick_rate")),
                    "num_games": int(stat.get("num_games", 0) or 0),
                }
            )

        return rows

    def _extract_champion_reco_stats_from_text(self, html_content):
        """
        Parse the visible champion-page recommendation table.
        Returns a list of rows in table order: rank, augment_id, tier_label, win_rate, pick_rate.
        """
        lines = _extract_lines_text(html_content)
        if not lines:
            return []

        start_idx = -1
        for idx, ln in enumerate(lines):
            if "海克斯推荐" in ln and "组合" not in ln:
                start_idx = idx
                break
        if start_idx < 0:
            return []

        rows = []
        i = start_idx + 1
        while i < len(lines):
            if lines[i].strip() == "显示全部":
                i += 1
                continue
            if "推荐海克斯组合" in lines[i] or "相似英雄推荐" in lines[i]:
                break
            if not re.fullmatch(r"\d+", str(lines[i]).strip()):
                i += 1
                continue

            rank = int(lines[i].strip())
            aug_id = ""
            tier_label = ""
            win_rate = None
            pick_rate = None
            seen_name = False
            j = i + 1
            while j < len(lines):
                probe = str(lines[j]).strip()
                if not probe:
                    j += 1
                    continue
                if re.fullmatch(r"\d+", probe):
                    break
                if "推荐海克斯组合" in probe or "相似英雄推荐" in probe:
                    break
                if probe.startswith("#") and not aug_id:
                    aug_id = re.sub(r"\D", "", probe)
                elif re.fullmatch(r"T[1-5]", probe.replace(" ", "").upper()):
                    tier_label = probe.replace(" ", "").upper()
                else:
                    mm = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", probe)
                    if mm:
                        if win_rate is None:
                            win_rate = _to_float_safe(mm.group(1))
                        elif pick_rate is None:
                            pick_rate = _to_float_safe(mm.group(1))
                    elif not seen_name and not probe.startswith("全部") and probe not in {"排名", "强化", "层级", "胜率", "选取率"}:
                        seen_name = True
                j += 1

            rows.append({
                "website_rank": rank,
                "augment_id": aug_id,
                "tier_label": tier_label or "T3",
                "win_rate": win_rate,
                "pick_rate": pick_rate,
            })
            i = j

        return rows

    def _extract_all_recommendation_rows_from_next_data(self, html_content):
        """
        Parse the hidden Next.js payload to recover the full recommendation list.
        This avoids relying on the visible table's truncated rows / "显示全部".
        """
        if not html_content:
            return []
        text = html_content
        rows = []
        seen = set()

        # Prefer anchor data embedded in the React payload. This is broader than the visible table.
        anchor_pat = re.compile(
            r'(?is)<a[^>]+href=["\'](?:https://aramgg\.com)?/zh-CN/augments/(\d+)["\'][^>]*title=["\']([^"\']+)["\']',
        )
        for idx, (aug_id, name) in enumerate(anchor_pat.findall(text), 1):
            key = app.normalize_name_key(f"{aug_id}:{name}")
            if not aug_id or not name or key in seen:
                continue
            seen.add(key)
            rows.append({
                "augment_id": aug_id,
                "name": html.unescape(name).strip(),
                "url": f"{ARAMGG_BASE_URL}/zh-CN/augments/{aug_id}",
                "website_rank": idx,
            })

        if rows:
            rows.sort(key=lambda x: int(x.get("website_rank", 9999) or 9999))
            return rows

        # Fallback: JSON-LD ItemList when anchors are not enough.
        raw = html_content.replace('\\"', '"')
        for m in re.finditer(r'(?is)"itemListElement"\s*:\s*(\[[^\]]+\])', raw):
            block = m.group(1)
            if "/augments/" not in block:
                continue
            try:
                arr = json.loads(block)
            except Exception:
                continue
            if not isinstance(arr, list):
                continue
            for obj in arr:
                if not isinstance(obj, dict):
                    continue
                url = str(obj.get("url", "")).strip()
                if "/augments/" not in url:
                    continue
                mm = re.search(r"/augments/(\d+)", url)
                aug_id = mm.group(1) if mm else ""
                name = str(obj.get("name", "")).strip()
                if not aug_id or not name:
                    continue
                key = app.normalize_name_key(f"{aug_id}:{name}")
                if key in seen:
                    continue
                seen.add(key)
                rows.append({
                    "augment_id": aug_id,
                    "name": name,
                    "url": url,
                    "website_rank": int(obj.get("position", len(rows) + 1) or len(rows) + 1),
                })
        rows.sort(key=lambda x: int(x.get("website_rank", 9999) or 9999))
        return rows

    def _extract_combo_rows_from_text(self, html_content):
        lines = _extract_lines_text(html_content)
        if not lines:
            return []
        start_idx = -1
        for idx, ln in enumerate(lines):
            if "推荐海克斯组合" in ln:
                start_idx = idx
                break
        if start_idx < 0:
            return []

        rows = []
        i = start_idx + 1
        no_data_tokens = {"新版本尚未有数据", "暂无数据", "没有数据", "暂无推荐海克斯组合"}
        while i < len(lines):
            cur = str(lines[i]).strip()
            if not cur or cur == "显示全部":
                i += 1
                continue
            if cur in no_data_tokens:
                return []
            if "相似英雄推荐" in cur or "海克斯推荐" in cur or "装备配置" in cur or "相关文章" in cur:
                break
            if "推荐海克斯组合" in cur and i > start_idx + 1:
                break
            if not re.fullmatch(r"\d+", cur):
                i += 1
                continue

            rank = int(cur)
            combo_parts = []
            tier_label = ""
            j = i + 1
            while j < len(lines):
                probe = str(lines[j]).strip()
                if not probe:
                    j += 1
                    continue
                if re.fullmatch(r"\d+", probe):
                    break
                if probe in no_data_tokens:
                    return []
                if "相似英雄推荐" in probe or "海克斯推荐" in probe or "装备配置" in probe or "相关文章" in probe:
                    break
                if probe.startswith("#"):
                    combo_parts.append(re.sub(r"\D", "", probe))
                elif probe.startswith("推荐海克斯组合"):
                    break
                else:
                    cleaned = re.sub(r"(?is)<!--.*?-->", " ", probe)
                    cleaned = re.sub(r"\s+", " ", html.unescape(cleaned)).strip().upper().replace(" ", "")
                    m = re.search(r"T\s*([1-5])", cleaned)
                    if m:
                        tier_label = f"T{m.group(1)}"
                        break
                j += 1

            if not combo_parts:
                i = j
                continue
            rows.append({
                "website_rank": rank,
                "combo_token": " + ".join([f"#{x}" for x in combo_parts if x]),
                "tier_label": tier_label or "",
            })
            i = j

        return rows

    def _parse_augment_detail_page(self, augment_id):
        if not augment_id:
            return {}
        cache = self._augment_meta.get(str(augment_id))
        now = time.time()
        if cache and (now - float(cache.get("ts", 0))) < 12 * 60 * 60:
            return dict(cache.get("data") or {})

        with self._lock:
            if not self._augment_name_meta:
                self._augment_name_meta = self._load_augment_name_meta()
            base_meta = dict(self._augment_name_meta.get(str(augment_id), {}) or {})

        url = f"{ARAMGG_BASE_URL}/zh-CN/augments/{augment_id}"
        html_content = self._http_get(url)
        if not html_content:
            return dict(base_meta)
        lines = _extract_lines_text(html_content)

        def _clean_name_candidate(raw):
            txt = html.unescape(str(raw or "")).strip()
            if not txt:
                return ""
            txt = re.sub(r"\s+", " ", txt)
            if re.fullmatch(r"#?\s*Augment#?\d+", txt, flags=re.I):
                return ""
            txt = re.split(r"\s*\|\s*", txt, maxsplit=1)[0].strip()
            txt = re.sub(r"\s*[-–—]\s*胜率.*$", "", txt).strip()
            txt = re.sub(r"^(?:#\s*)?Augment#\d+\s*", "", txt, flags=re.I).strip()
            # Common source titles keep the augment name in front of these keywords.
            for token in ("海克斯强化详情", "海克斯强化推荐", "增幅装置详情", "增幅装置推荐", "海克斯强化", "增幅装置"):
                if token in txt:
                    prefix = txt.split(token, 1)[0].strip()
                    if prefix:
                        txt = prefix
                    break
            txt = re.sub(r"(?:详情|推荐|攻略)$", "", txt).strip()
            txt = re.sub(r"\s+", " ", txt).strip()
            return txt

        name = ""
        candidates = []
        for pat in (
            r'(?is)<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)["\']',
            r'(?is)<meta[^>]+name=["\']twitter:title["\'][^>]+content=["\']([^"\']+)["\']',
            r'(?is)<title>\s*([^<]+?)\s*</title>',
            r'(?is)<h1[^>]*>([^<]+)</h1>',
        ):
            m = re.search(pat, html_content.replace("<!-- -->", ""))
            if m:
                candidates.append(m.group(1))
        for cand in candidates:
            name = _clean_name_candidate(cand)
            if name:
                break
        if not name:
            for ln in lines[:40]:
                cand = _clean_name_candidate(ln)
                if cand and not re.fullmatch(r"T[1-5]", cand.upper()):
                    name = cand
                    break
        if not name:
            name = str(base_meta.get("name", "")).strip()

        win = None
        pick = None
        games = None
        tier = ""
        stages = []

        # Prefer the page header tier badge (T1-T5) instead of stage stats.
        header_tier = ""
        for ln in lines[:80]:
            if re.fullmatch(r"T[1-5]", str(ln).strip().upper()):
                header_tier = str(ln).strip().upper()
                break

        for i, ln in enumerate(lines):
            if ln == "胜率" and i + 1 < len(lines):
                m = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", lines[i + 1])
                if m:
                    win = _normalize_percent_value(m.group(1))
            if ln == "选取率" and i + 1 < len(lines):
                m = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", lines[i + 1])
                if m:
                    pick = _normalize_percent_value(m.group(1))
            if ln == "场次" and i + 1 < len(lines):
                m = re.search(r"([0-9,]+)", lines[i + 1])
                if m:
                    try:
                        games = int(m.group(1).replace(",", ""))
                    except Exception:
                        games = None
            if ln.startswith("阶段 ") and i + 4 < len(lines):
                t = lines[i + 1] if re.match(r"^T[1-5]$", lines[i + 1]) else ""
                wr = None
                pr = None
                m1 = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", lines[i + 2] if i + 2 < len(lines) else "")
                m2 = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", lines[i + 3] if i + 3 < len(lines) else "")
                if m1:
                    wr = _normalize_percent_value(m1.group(1))
                if m2:
                    pr = _normalize_percent_value(m2.group(1))
                if t:
                    stages.append({"tier": t, "win_rate": wr, "pick_rate": pr})

        if header_tier:
            tier = header_tier
        elif stages:
            stages_sorted = sorted(
                [x for x in stages if x.get("win_rate") is not None],
                key=lambda x: float(x.get("win_rate") or 0.0),
                reverse=True,
            )
            if stages_sorted:
                tier = stages_sorted[0].get("tier", "")
        if not tier:
            tier = "T3"

        data = {
            "name": name,
            "icon_url": str(base_meta.get("icon_url", "")).strip(),
            "icon_small_url": str(base_meta.get("icon_small_url", "")).strip(),
            "icon_large_url": str(base_meta.get("icon_large_url", "")).strip(),
            "rarity": str(base_meta.get("rarity", "")).strip(),
            "rarity_value": base_meta.get("rarity_value"),
            "tier": tier,
            "win_rate": win,
            "pick_rate": pick,
            "games": games,
            "stage_stats": stages[:5],
        }
        self._augment_meta[str(augment_id)] = {"ts": now, "data": dict(data)}
        return data

    def get_combo_recommendations(self, champion_name):
        """Return combo recommendations from cached champion data."""
        if not champion_name:
            return []
        slug = None
        alias_key = ""
        display_name = champion_name
        if "|" in champion_name:
            left, right = champion_name.split("|", 1)
            display_name = left.strip() or champion_name
            alias_key = app.normalize_name_key(right)
        display_key = app.normalize_name_key(display_name)
        with self._lock:
            slug = self._data["name_to_slug"].get(alias_key) if alias_key else None
            if not slug:
                slug = self._data["name_to_slug"].get(display_key)
            if not slug:
                slug = self._data["name_to_slug"].get(app.normalize_name_key(str(display_name)))
            entry = self._data.get("champions", {}).get(slug) if slug else None
            extra = (entry or {}).get("provider_extra", {}) if isinstance(entry, dict) else {}
            combos = extra.get("combo_reco") if isinstance(extra, dict) else None
            if not isinstance(combos, list) or not combos:
                return []
            return [dict(x) for x in combos if isinstance(x, dict)]

    def find_best_recommendation_by_name(self, augment_name, champion_name=None):
        """Find a recommendation row by augment name, preferring the current champion pool."""
        if not augment_name:
            return None
        query = app.normalize_name_key(augment_name)
        if not query:
            return None

        def _scan(rows):
            best = None
            best_ratio = 0.0
            for item in rows or []:
                nm = str(item.get("name", "")).strip()
                if not nm:
                    continue
                key = app.normalize_name_key(nm)
                if not key:
                    continue
                if key == query:
                    return dict(item)
                ratio = difflib.SequenceMatcher(None, query, key).ratio()
                if query in key or key in query:
                    ratio = min(1.0, ratio + 0.16)
                if ratio > best_ratio:
                    best_ratio = ratio
                    best = item
            if best is not None and best_ratio >= 0.68:
                return dict(best)
            return None

        local_rows = []
        all_rows = []
        with self._lock:
            if champion_name:
                slug, _ = self._resolve_slug_locked(champion_name)
                entry = self._data.get("champions", {}).get(slug) if slug else None
                recos = entry.get("recommendations", []) if isinstance(entry, dict) else []
                if recos:
                    local_rows = list(recos)
            if not local_rows:
                for entry in self._data.get("champions", {}).values():
                    recos = entry.get("recommendations", []) if isinstance(entry, dict) else []
                    if recos:
                        all_rows.extend(recos)

        found = _scan(local_rows)
        if found:
            return found
        return _scan(all_rows)

    def _refresh_champion_by_slug(self, slug, requested_name):
        if not slug:
            return
        with self._lock:
            stat_row = dict(self._champion_stats.get(str(slug), {}))
        if not stat_row:
            self._refresh_index()
            with self._lock:
                stat_row = dict(self._champion_stats.get(str(slug), {}))

        url = f"{ARAMGG_BASE_URL}/zh-CN/champion-stats/{slug}"
        html_content = self._http_get(url)
        if not html_content:
            app.log_status(f"source_fetch_empty_{slug}", f"[Source] 英雄页失败: {slug}", interval=30)
            return

        top_augments = self._extract_all_recommendation_rows_from_rsc(html_content, slug)
        if not top_augments:
            top_augments = self._extract_all_recommendation_rows_from_table(html_content)
        if not top_augments:
            top_augments = self._extract_all_recommendation_rows_from_next_data(html_content)
        if not top_augments:
            top_augments = self._extract_top_augments_from_jsonld(html_content)
        if not top_augments:
            app.log_status(f"source_parse_empty_{slug}", f"[Source] 无推荐: {slug}", interval=60)
            return
        combo_rows = self._extract_combo_rows_from_text(html_content)

        title_match = re.search(r"(?is)<h1[^>]*>([^<]+)</h1>", html_content.replace("<!-- -->", ""))
        title_text = html.unescape(title_match.group(1).strip()) if title_match else (requested_name or str(slug))
        champ_tier = f"T{str(stat_row.get('tier', '')).strip()}" if str(stat_row.get("tier", "")).strip().isdigit() else ""
        champ_wr = _normalize_percent_value(stat_row.get("winRate"))
        champ_pr = _normalize_percent_value(stat_row.get("pickRate"))

        id_to_name = {
            str(x.get("augment_id", "")).strip(): str(x.get("name", "")).strip()
            for x in top_augments
            if str(x.get("augment_id", "")).strip()
        }
        with self._lock:
            if not self._augment_name_meta:
                self._augment_name_meta = self._load_augment_name_meta()
            augment_name_meta = dict(self._augment_name_meta)

        def _build_combo_members(token):
            members = []
            seen_member_ids = set()
            for part in re.findall(r"\d+", str(token or "")):
                augment_id = str(part).strip()
                if not augment_id or augment_id in seen_member_ids:
                    continue
                seen_member_ids.add(augment_id)
                meta = dict(augment_name_meta.get(augment_id, {}) or {})
                if not meta:
                    meta = self._parse_augment_detail_page(augment_id)
                member_name = id_to_name.get(augment_id, "") or str(meta.get("name", "")).strip()
                members.append(
                    {
                        "augment_id": augment_id,
                        "name": member_name or f"#{augment_id}",
                        "icon_url": str(meta.get("icon_url", "")).strip(),
                        "rarity": str(meta.get("rarity", "")).strip(),
                    }
                )
            return members

        def _format_combo_token(token):
            parts = [p for p in re.findall(r"\d+", str(token or "")) if p]
            named = []
            for p in parts:
                nm = id_to_name.get(p, "")
                if not nm:
                    meta = self._parse_augment_detail_page(p)
                    nm = str(meta.get("name", "")).strip()
                named.append(nm or f"#{p}")
            return " + ".join([x for x in named if x]) if named else str(token or "").strip()

        recos = []
        for idx, row in enumerate(top_augments, 1):
            augment_id = str(row.get("augment_id", "")).strip()
            aug_meta = augment_name_meta.get(augment_id, {}) if augment_id else {}
            website_rank = int(row.get("website_rank", idx) or idx)
            website_tier = str(row.get("tier_label") or "").strip().upper()
            if website_tier not in {"T1", "T2", "T3", "T4", "T5"}:
                website_tier = "T5" if int(row.get("website_rank", idx) or idx) > 20 else "T3"
            aug_wr = _normalize_percent_value(row.get("win_rate"))
            aug_pr = _normalize_percent_value(row.get("pick_rate"))
            aug_url = row.get("url", "")
            if aug_url.startswith("/"):
                aug_url = ARAMGG_BASE_URL + aug_url
            aug_name = str(row.get("name", "")).strip() or str(aug_meta.get("name", "")).strip()
            icon_url = str(row.get("icon_url", "")).strip() or str(aug_meta.get("icon_url", "")).strip()
            rarity = str(row.get("rarity", "")).strip() or str(aug_meta.get("rarity", "")).strip()

            recos.append(
                {
                    "augment_id": augment_id,
                    "name": aug_name,
                    "icon_url": icon_url,
                    "rarity": rarity,
                    "tier": website_tier,
                    "tier_label": website_tier,
                    "grade": "S",
                    "tags": f"网站Top{website_rank}",
                    "score": max(1, 1000 - idx),
                    "author": "Source",
                    "note": "",
                    "items": [],
                    "parse_schema_version": app.HEXTECH_PARSE_SCHEMA_VERSION,
                    "source": aug_url or url,
                    "website_rank": website_rank,
                    "win_rate": aug_wr,
                    "pick_rate": aug_pr,
                    "champ_win_rate": champ_wr,
                    "champ_tier": champ_tier,
                }
            )

        aliases = [str(slug)]
        if requested_name:
            aliases.append(requested_name)
        champ_map = getattr(app, "_champion_map", {}) or {}
        info = champ_map.get(int(slug)) if str(slug).isdigit() else None
        if isinstance(info, dict):
            aliases.extend([info.get("name", ""), info.get("alias", "")])
        if title_text:
            aliases.append(title_text)
        dedup_alias = []
        seen = set()
        for a in aliases:
            a = str(a or "").strip()
            k = app.normalize_name_key(a)
            if k and k not in seen:
                seen.add(k)
                dedup_alias.append(a)

        entry = {
            "slug": str(slug),
            "url": url,
            "title": title_text,
            "version": str(stat_row.get("version", "") or ""),
            "aliases": dedup_alias,
            "updated_at": time.time(),
            "parse_schema_version": app.HEXTECH_PARSE_SCHEMA_VERSION,
            "recommendations": recos,
            "items_backfill_checked": True,
            "provider_extra": {
                "champion_tier": champ_tier,
                "champion_win_rate": champ_wr,
                "champion_pick_rate": champ_pr,
                "date": stat_row.get("date"),
                "combo_reco": [
                    {
                        "name": " + ".join(
                            [
                                str(member.get("name", "")).strip()
                                for member in _build_combo_members(row.get("combo_token", ""))
                                if str(member.get("name", "")).strip()
                            ]
                        ) or _format_combo_token(row.get("combo_token", "")),
                        "rating": str(row.get("tier_label") or "").strip().upper(),
                        "members": _build_combo_members(row.get("combo_token", "")),
                        "website_rank": row.get("website_rank"),
                    }
                    for row in combo_rows[:10]
                    if str(row.get("combo_token", "")).strip()
                ],
            },
        }

        with self._lock:
            self._data["champions"][str(slug)] = entry
            self._data["slug_map"][str(slug)] = url
            for a in dedup_alias:
                k = app.normalize_name_key(a)
                if k:
                    self._data["name_to_slug"][k] = str(slug)
            self._data["meta"]["last_data_refresh"] = time.time()
            self._data["meta"]["source"] = "aramgg.com"
            self._rebuild_augment_index_locked()
            self._save_cache_locked()
            self._save_augment_index_locked()
        self._dump_debug_page(slug, title_text, html_content, recos, combo_rows)
        print(f"[Source] 推荐更新完成: {title_text} ({len(recos)} 条)")


def configure_provider():
    base_dir = os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))
    cache_path = os.path.join(base_dir, "hextech_reco_cache.json")
    augment_index_path = os.path.join(base_dir, "hextech_augment_index.json")

    # Force a one-time refresh after parser/source fixes.
    app.HEXTECH_PARSE_SCHEMA_VERSION = max(int(getattr(app, "HEXTECH_PARSE_SCHEMA_VERSION", 0) or 0), 9)

    app.HEXTECH_CACHE_PATH = cache_path
    app.HEXTECH_AUGMENT_INDEX_PATH = augment_index_path
    app.hextech_provider = SourceHextechProvider(cache_path, augment_index_path=augment_index_path)


def main():
    configure_provider()
    app.main()


if __name__ == "__main__":
    main()
