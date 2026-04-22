#!/usr/bin/env python3
"""
辅助工具：找到特征点的屏幕坐标
运行此脚本，将鼠标移到特征点上，按 Ctrl+C 停止
"""
import sys
from pynput import mouse

def on_move(x, y):
    sys.stdout.write(f'\r鼠标位置: X={x}, Y={y}')
    sys.stdout.flush()

print("将鼠标移到特征点上，然后按 Ctrl+C 停止")
print("=" * 50)

try:
    with mouse.Listener(on_move=on_move) as listener:
        listener.join()
except KeyboardInterrupt:
    print("\n\n已停止")
    print("将上面的坐标填入 main.py 中的 FEATURE_POINT_X 和 FEATURE_POINT_Y")
