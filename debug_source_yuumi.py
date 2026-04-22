import json
import os

from main import SourceHextechProvider


BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CACHE_PATH = os.path.join(BASE_DIR, "hextech_reco_cache.json")
INDEX_PATH = os.path.join(BASE_DIR, "hextech_augment_index.json")


def main():
    prov = SourceHextechProvider(CACHE_PATH, augment_index_path=INDEX_PATH)
    prov._refresh_champion_by_slug("350", "悠米")

    entry = prov._data.get("champions", {}).get("350", {}) or {}
    recos = entry.get("recommendations", []) or []
    combos = (entry.get("provider_extra", {}) or {}).get("combo_reco", []) or []

    print("[TITLE]", entry.get("title"))
    print("[RECOS]", len(recos))
    for i, r in enumerate(recos[:20], 1):
        print(i, r.get("website_rank"), r.get("name"), r.get("tier_label"), r.get("win_rate"), r.get("pick_rate"))
    print("[COMBOS]", len(combos))
    for i, r in enumerate(combos[:10], 1):
        print(i, r.get("website_rank"), r.get("name"), r.get("rating"))

    out_path = os.path.join(BASE_DIR, "debug_source_yuumi.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(entry, f, ensure_ascii=False, indent=2)
    print("[SAVED]", out_path)


if __name__ == "__main__":
    main()
