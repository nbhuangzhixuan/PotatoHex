#!/usr/bin/env python3
import os
import importlib.util
import subprocess
import sys
import threading
import tkinter as tk
from tkinter import scrolledtext
from tkinter import messagebox


FROZEN = getattr(sys, "frozen", False)
BASE_DIR = os.path.dirname(os.path.abspath(sys.executable if FROZEN else __file__))
SCRIPT_PATH = os.path.join(BASE_DIR, "main.py")
APP_DIR = BASE_DIR
MAIN_EXE_PATH = os.path.join(APP_DIR, "main.exe")
REQUIREMENTS_PATH = os.path.join(BASE_DIR, "requirements.txt")
CREATE_NO_WINDOW = 0x08000000 if os.name == "nt" else 0
REQUIRED_MODULES = [
    ("requests", "requests"),
    ("cv2", "opencv-python"),
    ("numpy", "numpy"),
    ("PIL", "Pillow"),
    ("urllib3", "urllib3"),
]


class LauncherUI:
    def __init__(self, root):
        self.root = root
        self.proc = None
        self._log_queue = []
        self._log_lock = threading.Lock()

        self.root.title("PotatoHex")
        self.root.geometry("560x500")
        self.root.resizable(False, False)
        self.root.configure(bg="#07111f")
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        self._build_ui()
        self._refresh_state()
        self.root.after(500, self._poll_child)

    def _check_runtime_environment(self):
        if FROZEN:
            return []
        missing = []
        for module_name, package_name in REQUIRED_MODULES:
            if importlib.util.find_spec(module_name) is None:
                missing.append(package_name)
        return missing

    def _install_missing_packages(self, packages):
        if not packages:
            return True, ""
        if not os.path.exists(REQUIREMENTS_PATH):
            return False, "找不到 requirements.txt"
        cmd = [sys.executable, "-m", "pip", "install", "-r", REQUIREMENTS_PATH]
        try:
            self._append_log("[launcher] 正在安装缺失依赖...")
            proc = subprocess.run(
                cmd,
                cwd=BASE_DIR,
                capture_output=True,
                text=True,
            )
            if proc.stdout:
                self._append_log(proc.stdout.strip())
            if proc.stderr:
                self._append_log(proc.stderr.strip())
            if proc.returncode != 0:
                return False, f"pip 安装失败，退出码 {proc.returncode}"
            return True, ""
        except Exception as e:
            return False, str(e)

    def _build_start_command(self):
        if FROZEN:
            candidates = [
                MAIN_EXE_PATH,
                os.path.join(BASE_DIR, "main", "main.exe"),
                os.path.join(os.path.dirname(BASE_DIR), "main.exe"),
            ]
            for path in candidates:
                if os.path.exists(path):
                    return [path]
            return None
        return [sys.executable, SCRIPT_PATH]

    def _build_ui(self):
        bg = "#07111f"
        card = "#0d1b30"
        card2 = "#12233d"
        accent = "#36d8ff"
        text = "#eef5ff"
        muted = "#9bb0d1"

        root = tk.Frame(self.root, bg=bg)
        root.pack(fill="both", expand=True)

        header = tk.Frame(root, bg=bg, padx=20, pady=18)
        header.pack(fill="x")
        tk.Label(header, text="PotatoHex", bg=bg, fg=text, font=("Microsoft YaHei", 22, "bold")).pack(anchor="w")
        tk.Label(header, text="启动器", bg=bg, fg=accent, font=("Microsoft YaHei", 11, "bold")).pack(anchor="w", pady=(2, 0))

        body = tk.Frame(root, bg=bg, padx=20)
        body.pack(fill="both", expand=True)

        panel = tk.Frame(body, bg=card, highlightbackground="#1f3556", highlightthickness=1)
        panel.pack(fill="both", expand=True)

        title_bar = tk.Frame(panel, bg=card2, padx=14, pady=10)
        title_bar.pack(fill="x")
        tk.Label(title_bar, text="启动控制", bg=card2, fg=text, font=("Microsoft YaHei", 11, "bold")).pack(side="left")

        center = tk.Frame(panel, bg=card, padx=16, pady=16)
        center.pack(fill="both", expand=True)

        self.status_var = tk.StringVar(value="状态：未启动")
        tk.Label(center, textvariable=self.status_var, bg=card, fg=text, font=("Microsoft YaHei", 11, "bold"), anchor="w").pack(fill="x", pady=(0, 14))

        tk.Label(
            center,
            text="点击启动后，将运行识别主程序；关闭会结束后台进程。",
            bg=card,
            fg=muted,
            font=("Microsoft YaHei", 9),
            justify="left",
            wraplength=440,
            anchor="w",
        ).pack(fill="x", pady=(0, 18))

        hotkey_tip = tk.Frame(center, bg="#0a1730", highlightbackground="#24466f", highlightthickness=1, padx=12, pady=10)
        hotkey_tip.pack(fill="x", pady=(0, 16))
        tk.Label(
            hotkey_tip,
            text="使用说明",
            bg="#0a1730",
            fg=accent,
            font=("Microsoft YaHei", 10, "bold"),
            anchor="w",
        ).pack(fill="x")
        tk.Label(
            hotkey_tip,
            text="选人阶段会自动显示海克斯预览；进入游戏海克斯页面后，按 \\ 键可打开或关闭海克斯识别悬浮窗。",
            bg="#0a1730",
            fg="#dce8ff",
            font=("Microsoft YaHei", 9),
            justify="left",
            wraplength=430,
            anchor="w",
        ).pack(fill="x", pady=(6, 0))

        btn_row = tk.Frame(center, bg=card)
        btn_row.pack(fill="x", pady=(0, 12))

        self.start_btn = tk.Button(btn_row, text="启动", command=self.start_app, bg="#1dbf73", fg="#ffffff", activebackground="#28d785", activeforeground="#ffffff", relief="flat", font=("Microsoft YaHei", 11, "bold"), padx=20, pady=10, width=10)
        self.start_btn.pack(side="left")

        self.stop_btn = tk.Button(btn_row, text="关闭", command=self.stop_app, bg="#d94b4b", fg="#ffffff", activebackground="#f05d5d", activeforeground="#ffffff", relief="flat", font=("Microsoft YaHei", 11, "bold"), padx=20, pady=10, width=10)
        self.stop_btn.pack(side="left", padx=12)

        exit_btn = tk.Button(btn_row, text="退出", command=self.on_close, bg="#32415f", fg="#ffffff", activebackground="#41567d", activeforeground="#ffffff", relief="flat", font=("Microsoft YaHei", 11, "bold"), padx=20, pady=10, width=10)
        exit_btn.pack(side="right")

        log_title = tk.Label(center, text="运行日志", bg=card, fg=text, font=("Microsoft YaHei", 10, "bold"), anchor="w")
        log_title.pack(fill="x", pady=(0, 6))

        self.log_box = scrolledtext.ScrolledText(
            center,
            height=6,
            bg="#08111d",
            fg="#dce8ff",
            insertbackground="#dce8ff",
            relief="flat",
            font=("Consolas", 9),
            wrap="word",
        )
        self.log_box.pack(fill="both", expand=True, pady=(0, 12))
        self.log_box.configure(state="disabled")

        footer = tk.Frame(root, bg=bg, padx=20, pady=4)
        footer.pack(fill="x", side="bottom")
        tk.Label(footer, text="个人自娱自乐 | 作者B站：柠萌黄叔", bg=bg, fg="#6f86ab", font=("Microsoft YaHei", 9)).pack(anchor="w")

    def _refresh_state(self):
        running = self.proc is not None and self.proc.poll() is None
        if running:
            self.status_var.set(f"状态：运行中 (PID {self.proc.pid})")
            self.start_btn.configure(state="disabled")
            self.stop_btn.configure(state="normal")
        else:
            self.status_var.set("状态：未启动")
            self.start_btn.configure(state="normal")
            self.stop_btn.configure(state="disabled")

    def _append_log(self, text):
        if not text:
            return
        def _do():
            self.log_box.configure(state="normal")
            self.log_box.insert("end", text)
            if not text.endswith("\n"):
                self.log_box.insert("end", "\n")
            self.log_box.see("end")
            self.log_box.configure(state="disabled")
        self.root.after(0, _do)

    def _reader_thread(self, stream):
        try:
            for line in iter(stream.readline, ""):
                if not line:
                    break
                self._append_log(line.rstrip("\n"))
        except Exception as e:
            self._append_log(f"[launcher] 日志读取失败: {e}")
        finally:
            try:
                stream.close()
            except Exception:
                pass

    def start_app(self):
        if self.proc is not None and self.proc.poll() is None:
            return
        if not FROZEN and not os.path.exists(SCRIPT_PATH):
            messagebox.showerror("错误", "找不到 main.py")
            return
        missing = self._check_runtime_environment()
        if missing:
            ok = messagebox.askyesno(
                "依赖缺失",
                "当前电脑缺少运行环境：\n\n"
                + "\n".join(f"- {pkg}" for pkg in missing)
                + "\n\n是否自动安装？"
            )
            if not ok:
                return
            success, err = self._install_missing_packages(missing)
            if not success:
                messagebox.showerror("安装失败", err)
                return
        cmd = self._build_start_command()
        if not cmd:
            messagebox.showerror(
                "启动失败",
                "未找到 main.exe。\n请确认 launcher.exe 和 main.exe 在同一目录，或重新运行打包脚本。"
            )
            return
        try:
            self.log_box.configure(state="normal")
            self.log_box.delete("1.0", "end")
            self.log_box.configure(state="disabled")
            self.proc = subprocess.Popen(
                cmd,
                cwd=BASE_DIR,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                universal_newlines=True,
                creationflags=CREATE_NO_WINDOW,
            )
            threading.Thread(target=self._reader_thread, args=(self.proc.stdout,), daemon=True).start()
            self._refresh_state()
        except Exception as e:
            self.proc = None
            self._refresh_state()
            messagebox.showerror("启动失败", str(e))

    def stop_app(self):
        if self.proc is None or self.proc.poll() is not None:
            self.proc = None
            self._refresh_state()
            return
        try:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=4)
            except subprocess.TimeoutExpired:
                self.proc.kill()
        finally:
            self.proc = None
            self._refresh_state()

    def _poll_child(self):
        if self.proc is not None and self.proc.poll() is not None:
            try:
                if self.proc.stdout:
                    self.proc.stdout.close()
            except Exception:
                pass
            self.proc = None
            self._refresh_state()
        self.root.after(500, self._poll_child)

    def on_close(self):
        self.stop_app()
        self.root.destroy()


def main():
    root = tk.Tk()
    LauncherUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()
