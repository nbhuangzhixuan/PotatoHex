#!/usr/bin/env python3
import argparse
import os
import re
import subprocess
import tempfile

import cv2
import numpy as np


def save_png_unicode(path, image):
    ok, buf = cv2.imencode(".png", image)
    if not ok:
        return False
    buf.tofile(path)
    return True


def run_windows_ocr_on_image(image_path):
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
    with tempfile.NamedTemporaryFile(delete=False, suffix=".ps1", mode="w", encoding="utf-8") as fp:
        ps_path = fp.name
        fp.write(ps_script)
    try:
        cmd = [
            "powershell", "-NoProfile", "-ExecutionPolicy", "Bypass",
            "-File", ps_path, "-Path", image_path
        ]
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
        if res.returncode == 0:
            return re.sub(r"\s+", "", (res.stdout or ""))
        return ""
    finally:
        try:
            os.remove(ps_path)
        except Exception:
            pass


def extract_rois(
    image,
    panel_x1,
    panel_x2,
    panel_y1,
    panel_y2,
    name_y1,
    name_y2,
    name_x_margin,
    card_gap_ratio,
):
    h, w = image.shape[:2]
    px1, px2 = int(w * panel_x1), int(w * panel_x2)
    py1, py2 = int(h * panel_y1), int(h * panel_y2)
    panel = image[py1:py2, px1:px2]
    ph, pw = panel.shape[:2]
    gap = int(pw * card_gap_ratio)
    card_w = max(1, (pw - 2 * gap) // 3)
    rois = []
    boxes = []
    for i in range(3):
        cx1 = i * (card_w + gap)
        cx2 = cx1 + card_w
        if i == 2:
            cx2 = min(cx2, pw)
        ny1 = int(ph * name_y1)
        ny2 = int(ph * name_y2)
        nx1 = cx1 + int((cx2 - cx1) * name_x_margin)
        nx2 = cx2 - int((cx2 - cx1) * name_x_margin)
        roi = panel[ny1:ny2, nx1:nx2]
        rois.append(roi)
        boxes.append((px1 + nx1, py1 + ny1, px1 + nx2, py1 + ny2))
    return rois, boxes


def refine_title_strip(roi, already_upsampled=False):
    """
    Find best title-text band inside card ROI by scanning horizontal density.
    Returns a tighter sub-ROI that should contain the title line.
    """
    up = roi if already_upsampled else cv2.resize(roi, None, fx=2.0, fy=2.0, interpolation=cv2.INTER_CUBIC)
    hsv = cv2.cvtColor(up, cv2.COLOR_BGR2HSV)
    mask = cv2.inRange(hsv, (0, 0, 145), (180, 110, 255))
    # suppress side frame
    uh, uw = mask.shape[:2]
    side = int(uw * 0.12)
    mask[:, :side] = 0
    mask[:, uw - side:] = 0
    row_sum = mask.sum(axis=1).astype(np.float32)
    if row_sum.max() <= 0:
        return roi

    # Smooth and find densest band
    k = 21
    kernel = np.ones(k, dtype=np.float32) / k
    sm = np.convolve(row_sum, kernel, mode="same")
    center = int(np.argmax(sm))
    # Keep band generous; too-thin strips cause unreadable OCR.
    band_h = max(54, int(uh * 0.42))
    band_h = min(band_h, uh)
    y1 = max(0, center - band_h // 2)
    y2 = min(uh, center + band_h // 2)
    if y2 <= y1 + 8:
        return roi

    return up[y1:y2, :]


def cleanup_binary(bw):
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
        k = cv2.getStructuringElement(cv2.MORPH_RECT, (2, 2))
        clean = cv2.morphologyEx(clean, cv2.MORPH_OPEN, k)
        clean = cv2.morphologyEx(clean, cv2.MORPH_CLOSE, k)
        return clean


def make_ocr_candidates(base):
    hsv = cv2.cvtColor(base, cv2.COLOR_BGR2HSV)
    gray = cv2.cvtColor(base, cv2.COLOR_BGR2GRAY)
    white_mask = cv2.inRange(hsv, (0, 0, 135), (180, 120, 255))

    k = cv2.getStructuringElement(cv2.MORPH_RECT, (17, 17))
    top = cv2.morphologyEx(gray, cv2.MORPH_TOPHAT, k)
    top = cv2.normalize(top, None, 0, 255, cv2.NORM_MINMAX)
    _, c_light = cv2.threshold(top, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    c_light = cleanup_binary(cv2.bitwise_and(c_light, white_mask))

    clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
    eq = clahe.apply(gray)
    c_adp = cv2.adaptiveThreshold(
        eq, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY_INV, 31, 4
    )
    c_adp = cleanup_binary(c_adp)
    return {"light": c_light, "adp": c_adp}


def preprocess_for_ocr(roi):
    up_full = cv2.resize(roi, None, fx=2.0, fy=2.0, interpolation=cv2.INTER_CUBIC)
    up_strip = refine_title_strip(up_full, already_upsampled=True)
    cand_full = make_ocr_candidates(up_full)
    cand_strip = make_ocr_candidates(up_strip)
    candidates = {}
    for name, img in cand_full.items():
        candidates[f"{name}_full"] = img
    for name, img in cand_strip.items():
        candidates[f"{name}_strip"] = img
    return up_full, up_strip, candidates


def score_ocr_text(text):
    t = re.sub(r"\s+", "", text or "")
    if not t:
        return 0
    if re.search(r"(?:\d{1,2}:\d{2})|(?:\d{4}[./-]\d{1,2})", t):
        return 0
    cjk = len(re.findall(r"[\u4e00-\u9fff]", t))
    return cjk * 3 + len(t)


def main():
    ap = argparse.ArgumentParser(description="Test OCR ROI for 3 augment card names")
    ap.add_argument("--image", default="debug_screenshot.png")
    ap.add_argument("--out", default="ocr_test_out")
    ap.add_argument("--panel-x1", type=float, default=0.04)
    ap.add_argument("--panel-x2", type=float, default=0.96)
    ap.add_argument("--panel-y1", type=float, default=0.02)
    ap.add_argument("--panel-y2", type=float, default=0.92)
    ap.add_argument("--name-y1", type=float, default=0.39)
    ap.add_argument("--name-y2", type=float, default=0.44)
    ap.add_argument("--name-x-margin", type=float, default=0.37)
    ap.add_argument("--card-gap-ratio", type=float, default=-0.4, help="gap ratio between cards inside panel")
    args = ap.parse_args()

    img = cv2.imdecode(np.fromfile(args.image, dtype=np.uint8), cv2.IMREAD_COLOR)
    if img is None:
        raise SystemExit(f"Cannot read image: {args.image}")

    os.makedirs(args.out, exist_ok=True)
    rois, boxes = extract_rois(
        img,
        args.panel_x1, args.panel_x2, args.panel_y1, args.panel_y2,
        args.name_y1, args.name_y2, args.name_x_margin, args.card_gap_ratio
    )

    vis = img.copy()
    for i, (x1, y1, x2, y2) in enumerate(boxes):
        cv2.rectangle(vis, (x1, y1), (x2, y2), (0, 255, 255), 3)
        cv2.putText(vis, f"card{i}", (x1, max(20, y1 - 8)), cv2.FONT_HERSHEY_SIMPLEX, 0.9, (0, 255, 255), 2)
    save_png_unicode(os.path.join(args.out, "roi_overlay.png"), vis)

    for i, roi in enumerate(rois):
        up_full, up_strip, cands = preprocess_for_ocr(roi)
        roi_path = os.path.join(args.out, f"card_{i}_roi.png")
        raw_path = os.path.join(args.out, f"card_{i}_raw.png")
        strip_path = os.path.join(args.out, f"card_{i}_strip.png")
        save_png_unicode(roi_path, roi)
        save_png_unicode(raw_path, up_full)
        save_png_unicode(strip_path, up_strip)

        best_txt = ""
        best_score = -1
        best_name = ""
        best_img = None
        priority = [
            "light_full",
            "adp_full",
            "light_strip",
            "adp_strip",
        ]

        for name in priority:
            bw = cands.get(name)
            if bw is None:
                continue
            path = os.path.join(args.out, f"card_{i}_{name}.png")
            save_png_unicode(path, bw)
            txt = run_windows_ocr_on_image(path)
            score = score_ocr_text(txt)
            if score > best_score:
                best_score = score
                best_txt = txt
                best_name = name
                best_img = bw

        if best_img is None:
            best_img = np.zeros_like(up_full[:, :, 0])
        save_png_unicode(os.path.join(args.out, f"card_{i}_bin.png"), best_img)
        print(f"card_{i}: {re.sub(r'\\s+', '', best_txt)}  (best={best_name}, score={best_score})")

    print(f"saved: {os.path.abspath(args.out)}")
    print("Note: card_i_roi.png matches roi_overlay boxes; card_i_raw.png is full upsampled ROI; card_i_strip.png is refined title strip.")
    print("Try adjusting --name-y1/--name-y2 first, then --name-x-margin.")


if __name__ == "__main__":
    main()
