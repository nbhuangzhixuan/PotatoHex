#!/usr/bin/env python3
"""
全屏搜索模板位置，输出坐标并保存标记图。
用法：直接运行，3秒倒计时后截屏搜索。
"""
import os
import time
import cv2
import numpy as np
from PIL import ImageGrab

TEMPLATE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "特征图.png")

def main():
    # 加载模板
    if not os.path.exists(TEMPLATE_PATH):
        print(f"[Error] 找不到模板文件: {TEMPLATE_PATH}")
        return

    template = cv2.imdecode(np.fromfile(TEMPLATE_PATH, dtype=np.uint8), cv2.IMREAD_COLOR)
    h_t, w_t = template.shape[:2]
    print(f"[Info] 模板尺寸: {w_t} x {h_t}")

    # 倒计时，方便切换到游戏窗口
    for i in range(3, 0, -1):
        print(f"[Info] {i} 秒后截屏...")
        time.sleep(1)

    print("[Info] 截屏中...")
    screenshot = ImageGrab.grab()
    img = cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)
    print(f"[Info] 屏幕尺寸: {img.shape[1]} x {img.shape[0]}")

    # 全屏模板匹配
    result = cv2.matchTemplate(img, template, cv2.TM_CCOEFF_NORMED)
    _, max_val, _, max_loc = cv2.minMaxLoc(result)

    top_left = max_loc
    center_x = top_left[0] + w_t // 2
    center_y = top_left[1] + h_t // 2

    print()
    print("=" * 45)
    print(f"  匹配度    : {max_val:.4f}  (>0.2 即可用)")
    print(f"  左上角    : x={top_left[0]}, y={top_left[1]}")
    print(f"  中心坐标  : x={center_x}, y={center_y}")
    print()
    print("  请把 main.py 里这两行改为：")
    print(f"  FEATURE_POINT_X = {center_x}")
    print(f"  FEATURE_POINT_Y = {center_y}")
    print("=" * 45)

    # 在截图上画红框并保存
    marked = img.copy()
    cv2.rectangle(marked, top_left, (top_left[0] + w_t, top_left[1] + h_t), (0, 0, 255), 3)
    cv2.circle(marked, (center_x, center_y), 8, (0, 255, 0), -1)
    out_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "found_position.png")
    cv2.imencode(".png", marked)[1].tofile(out_path)
    print(f"\n[Info] 标记图已保存: {out_path}")

    if max_val < 0.2:
        print("[Warning] 匹配度过低，可能游戏没有显示海克斯页面，或模板不匹配")

if __name__ == "__main__":
    main()
