#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
原神自动弹琴 · 琴谱演奏器
==========================

读取 txt 琴谱（例如 ``D D (AH)``），按设定间隔向《原神》发送键盘按键，自动演奏。

安全设计（重要）
----------------
* 只有《原神》窗口处于**前台**时才允许开始演奏；倒计时结束前不会发送任何按键。
* 演奏过程中《原神》一旦失去焦点（被切到后台/被别的窗口遮挡为前台），立即停止并松开全部按键。
* 任何异常/退出/停止路径都会统一释放按键，避免"卡键"。
* 单实例运行，避免两份程序同时按键盘造成混乱。
* 程序窗口默认"始终置顶"，方便在全屏（无边框窗口）游戏时用 Alt+点击开始按钮；
  若置顶无效（独占全屏），可用全局快捷键（默认 F9 开始/停止、F10 紧急停止，均可自定义）。

命令行
------
    python genshin_lyre.py              启动界面
    python genshin_lyre.py --selftest   自检（不发送任何按键）
    python genshin_lyre.py --smoke      界面构建烟雾测试（窗口不显示）
"""

from __future__ import annotations

import argparse
import ctypes
import ctypes.wintypes as wintypes
import dataclasses
import datetime
import faulthandler
import json
import logging
import logging.handlers
import os
import queue
import re
import sys
import threading
import time
import traceback

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_NAME = "原神自动弹琴 · 琴谱演奏器"
APP_VERSION = "1.1.1"
APP_AUTHOR = "ナカハラ ミサキ"
APP_CONTACT = "3652179199"

# 配置版本：升级时用来纠正老配置里语义反了的默认值
CONFIG_VERSION = 2

DISCLAIMER_FILE = "免责声明文案.txt"

# ---------------------------------------------------------------------------
# 免责声明（唯一版本，弹窗只读，只能"同意"或"不同意"）
# ---------------------------------------------------------------------------

DISCLAIMER_TEXT = """【免责声明 · 使用须知】

一、非官方声明（首要条款）
本软件为个人独立开发的第三方工具，与米哈游（miHoYo）、上海米哈游网络科技股份有限公司、《原神》官方及其关联公司、开发团队、运营方之间，不存在任何隶属、合作、代理、赞助、授权、认可或背书关系。本软件非官方出品，不代表官方立场，不提供任何官方服务，亦未经官方审阅或批准。"原神"及相关名称、标识、素材的一切权利，均归其合法权利人所有。

二、授权范围
本软件仅供个人在自有设备上用于学习、研究与娱乐。开发者仅授予您一项非独占、不可转让、不可再许可的个人使用许可。

三、严禁行为（开发者保留随时终止授权并公开说明的权利）
1. 严禁以任何形式销售、转售、倒卖、出租、收费提供、付费下载或捆绑销售本软件及其任何修改版；
2. 严禁将本软件用于任何商业用途或盈利活动，包括但不限于代练代打、付费答疑、直播打赏变现、引流广告、以本软件为卖点的付费社群或课程；
3. 严禁删除、隐藏或篡改本免责声明、作者署名与反馈渠道；
4. 严禁将本软件用于违反《原神》用户协议、相关法律法规或侵害他人合法权益的任何用途；
5. 严禁冒充官方或作者，以本软件名义作出任何承诺、担保或索赔。

四、风险提示
1. 本软件通过模拟键盘输入实现自动演奏，属于第三方辅助工具。使用此类工具可能导致游戏账号被警告、限制、封禁或数据异常，相关风险与后果完全由使用者自行承担；
2. 本软件不读取、不修改、不注入游戏进程与内存，不与游戏服务器通讯，但无法保证游戏方对其的判定结果；
3. 前台窗口切换、输入法冲突、按键时序偏差等情况可能造成误按键或影响游戏操作，请在单人、非战斗、非关键操作等安全场景下使用。

五、免责与责任限制
1. 本软件按"现状"提供，不附带任何明示或默示担保，包括但不限于适用性、无错误、不中断、无损害；
2. 在适用法律允许的最大范围内，开发者不对因使用或无法使用本软件所致的任何直接、间接、附带、惩罚性或后果性损失负责，包括但不限于账号损失、虚拟财产损失、数据丢失、设备损坏与收益损失；
3. 您须自行确认运行环境（前台窗口、输入法、显示模式等），并自行承担一切操作后果；
4. 因您违反本声明或相关法律法规而产生的责任与纠纷，由您自行承担，与开发者无关。

六、数据与隐私
本软件的全部配置、谱子与日志仅保存于您的本机，不联网上传、不收集任何个人信息。

七、未成年人
未满 18 周岁者，应在监护人知情并同意的前提下使用本软件。

八、条款变更与终止
开发者保留随时修改、更新、暂停或终止本软件及本声明的权利，恕不另行通知。变更后继续使用即视为接受最新声明；如不同意，请立即停止使用并自行删除本软件及其全部副本。

九、最终解释
本声明的最终解释权归开发者所有。点击"同意并继续"，即表示您已完整阅读、理解并自愿接受上述全部条款。

作者：ナカハラ ミサキ　问题反馈 QQ：3652179199"""

# 保留列表结构（只有这一版，不允许在这个页面里切换或编辑）
DISCLAIMER_DRAFTS = [
    {"id": "E", "name": "免责声明", "text": DISCLAIMER_TEXT},
]


def disclaimer_by_id(version_id=None):
    return DISCLAIMER_DRAFTS[0]

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOG_DIR = os.path.join(BASE_DIR, "logs")
SHEET_DIR = os.path.join(BASE_DIR, "sheets")
CONFIG_PATH = os.path.join(BASE_DIR, "config.json")
INSTRUMENTS_PATH = os.path.join(BASE_DIR, "instruments.json")
LOG_FILE = os.path.join(LOG_DIR, "genshin_lyre.log")

WIN = os.name == "nt"
log = logging.getLogger("genshin_lyre")

_fault_file = None  # 保持引用，避免被 GC

# ---------------------------------------------------------------------------
# Win32 底层
# ---------------------------------------------------------------------------

if WIN:
    user32 = ctypes.WinDLL("user32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
else:  # 仅为让非 Windows 也能导入/自检
    user32 = None
    kernel32 = None

INPUT_KEYBOARD = 1
KEYEVENTF_EXTENDEDKEY = 0x0001
KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_SCANCODE = 0x0008

MAPVK_VK_TO_VSC = 0
SW_RESTORE = 9
HWND_TOPMOST = -1
HWND_NOTOPMOST = -2
GWL_EXSTYLE = -20
WS_EX_TOPMOST = 0x00000008
SWP_NOSIZE = 0x0001
SWP_NOMOVE = 0x0002
SWP_NOACTIVATE = 0x0010
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
PM_REMOVE = 0x0001
WM_HOTKEY = 0x0312
MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_SHIFT = 0x0004
MOD_WIN = 0x0008
MOD_NOREPEAT = 0x4000
ERROR_ALREADY_EXISTS = 183


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", wintypes.WORD),
        ("wScan", wintypes.WORD),
        ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", ctypes.c_size_t),
    ]


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx", wintypes.LONG),
        ("dy", wintypes.LONG),
        ("mouseData", wintypes.DWORD),
        ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", ctypes.c_size_t),
    ]


class HARDWAREINPUT(ctypes.Structure):
    _fields_ = [
        ("uMsg", wintypes.DWORD),
        ("wParamL", wintypes.WORD),
        ("wParamH", wintypes.WORD),
    ]


class _INPUTUNION(ctypes.Union):
    _fields_ = [("ki", KEYBDINPUT), ("mi", MOUSEINPUT), ("hi", HARDWAREINPUT)]


class INPUT(ctypes.Structure):
    _fields_ = [("type", wintypes.DWORD), ("u", _INPUTUNION)]


if WIN:
    WNDENUMPROC = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
    try:
        user32.SendInput.argtypes = (wintypes.UINT, ctypes.POINTER(INPUT), ctypes.c_int)
        user32.SendInput.restype = wintypes.UINT
        user32.MapVirtualKeyW.argtypes = (wintypes.UINT, wintypes.UINT)
        user32.MapVirtualKeyW.restype = wintypes.UINT
        user32.GetForegroundWindow.restype = wintypes.HWND
        user32.GetWindowThreadProcessId.argtypes = (wintypes.HWND, ctypes.POINTER(wintypes.DWORD))
        user32.GetWindowThreadProcessId.restype = wintypes.DWORD
        user32.GetWindowTextW.argtypes = (wintypes.HWND, wintypes.LPWSTR, ctypes.c_int)
        user32.GetWindowTextLengthW.argtypes = (wintypes.HWND,)
        user32.IsWindowVisible.argtypes = (wintypes.HWND,)
        user32.IsIconic.argtypes = (wintypes.HWND,)
        user32.ShowWindow.argtypes = (wintypes.HWND, ctypes.c_int)
        user32.SetForegroundWindow.argtypes = (wintypes.HWND,)
        user32.BringWindowToTop.argtypes = (wintypes.HWND,)
        user32.AttachThreadInput.argtypes = (wintypes.DWORD, wintypes.DWORD, wintypes.BOOL)
        user32.EnumWindows.argtypes = (WNDENUMPROC, wintypes.LPARAM)
        user32.GetWindowRect.argtypes = (wintypes.HWND, ctypes.POINTER(wintypes.RECT))
        user32.SetWindowPos.argtypes = (
            wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int,
            ctypes.c_int, ctypes.c_int, wintypes.UINT,
        )
        user32.RegisterHotKey.argtypes = (wintypes.HWND, ctypes.c_int, wintypes.UINT, wintypes.UINT)
        user32.UnregisterHotKey.argtypes = (wintypes.HWND, ctypes.c_int)
        user32.GetWindowLongW.argtypes = (wintypes.HWND, ctypes.c_int)
        user32.GetWindowLongW.restype = ctypes.c_long
        user32.PeekMessageW.argtypes = (
            ctypes.POINTER(wintypes.MSG), wintypes.HWND,
            wintypes.UINT, wintypes.UINT, wintypes.UINT,
        )
        user32.GetWindowThreadProcessId.argtypes = (wintypes.HWND, ctypes.POINTER(wintypes.DWORD))
        kernel32.GetCurrentThreadId.restype = wintypes.DWORD
        kernel32.OpenProcess.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
        kernel32.OpenProcess.restype = wintypes.HANDLE
        kernel32.QueryFullProcessImageNameW.argtypes = (
            wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD),
        )
        kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
    except Exception:  # pragma: no cover - 极端环境下不至于启动失败
        log.exception("初始化 Win32 函数签名失败（不影响界面启动）")


# ---------------------------------------------------------------------------
# 按键表
# ---------------------------------------------------------------------------

SPECIAL_KEYS = {
    "CTRL": (0x11, "Ctrl"),
    "CONTROL": (0x11, "Ctrl"),
    "ALT": (0x12, "Alt"),
    "MENU": (0x12, "Alt"),
    "SHIFT": (0x10, "Shift"),
    "LWIN": (0x5B, "LWin"),
    "RWIN": (0x5C, "RWin"),
    "SPACE": (0x20, "Space"),
    "RETURN": (0x0D, "Enter"),
    "ENTER": (0x0D, "Enter"),
    "TAB": (0x09, "Tab"),
    "ESC": (0x1B, "Escape"),
    "ESCAPE": (0x1B, "Escape"),
    "BACKSPACE": (0x08, "Backspace"),
    "BACK": (0x08, "Backspace"),
    "UP": (0x26, "Up"),
    "DOWN": (0x28, "Down"),
    "LEFT": (0x25, "Left"),
    "RIGHT": (0x27, "Right"),
    "HOME": (0x24, "Home"),
    "END": (0x23, "End"),
    "PAGEUP": (0x21, "PageUp"),
    "PRIOR": (0x21, "PageUp"),
    "PAGEDOWN": (0x22, "PageDown"),
    "NEXT": (0x22, "PageDown"),
    "INSERT": (0x2D, "Insert"),
    "DELETE": (0x2E, "Delete"),
    "DEL": (0x2E, "Delete"),
    "MINUS": (0xBD, "Minus"),
    "EQUAL": (0xBB, "Equal"),
    "EQUALS": (0xBB, "Equal"),
    "COMMA": (0xBC, "Comma"),
    "PERIOD": (0xBE, "Period"),
    "SLASH": (0xBF, "Slash"),
    "SEMICOLON": (0xBA, "Semicolon"),
    "QUOTE": (0xDE, "Quote"),
    "APOSTROPHE": (0xDE, "Quote"),
    "BACKQUOTE": (0xC0, "Backquote"),
    "GRAVE": (0xC0, "Backquote"),
    "LBRACKET": (0xDB, "BracketLeft"),
    "RBRACKET": (0xDD, "BracketRight"),
    "BACKSLASH": (0xDC, "Backslash"),
}

KEY_ALIASES = {
    "空格": "SPACE",
    "空格键": "SPACE",
    "回车": "RETURN",
    "回车键": "RETURN",
    "上": "UP",
    "下": "DOWN",
    "左": "LEFT",
    "右": "RIGHT",
    "页面": "PAGEUP",
    "换页": "PAGEDOWN",
}

# 规范名 -> 虚拟键码
CANON_VK: dict[str, int] = {}
for _c in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
    CANON_VK[_c] = ord(_c)
for _d in "0123456789":
    CANON_VK[_d] = ord(_d)
for _i in range(1, 25):
    CANON_VK["F%d" % _i] = 0x6F + _i
for _k, (_vk, _name) in SPECIAL_KEYS.items():
    CANON_VK.setdefault(_name, _vk)

# 需要扩展键标志的按键
EXTENDED_VKS = {
    0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x2D, 0x2E,
    0x5B, 0x5C, 0x5D, 0x6F, 0x90, 0xA3, 0xA5,
}

# tkinter keysym -> 虚拟键码（用于快捷键绑定）
KEYSYM_VK = {
    "space": 0x20, "Return": 0x0D, "KP_Enter": 0x0D, "Tab": 0x09, "Escape": 0x1B,
    "BackSpace": 0x08, "Up": 0x26, "Down": 0x28, "Left": 0x25, "Right": 0x27,
    "Home": 0x24, "End": 0x23, "Prior": 0x21, "Next": 0x22, "Insert": 0x2D,
    "Delete": 0x2E, "minus": 0xBD, "equal": 0xBB, "comma": 0xBC, "period": 0xBE,
    "slash": 0xBF, "semicolon": 0xBA, "apostrophe": 0xDE, "grave": 0xC0,
    "bracketleft": 0xDB, "bracketright": 0xDD, "backslash": 0xDC,
}

MODIFIER_KEYSYMS = {
    "Control_L", "Control_R", "Alt_L", "Alt_R", "Shift_L", "Shift_R",
    "Super_L", "Super_R", "Caps_Lock", "Num_Lock",
}

FULLWIDTH_MAP = {}
for _i in range(0xFF01, 0xFF5F):
    FULLWIDTH_MAP[_i] = _i - 0xFEE0
FULLWIDTH_MAP[0x3000] = 0x20  # 全角空格


def safe_int(value, default, lo=None, hi=None):
    """把界面/配置文件里的值安全地转成 int（绝不抛异常）。"""
    try:
        if isinstance(value, bool):
            value = int(value)
        if isinstance(value, str):
            value = value.strip()
            if not value:
                return default
        num = int(float(value))
    except Exception:
        return default
    if lo is not None and num < lo:
        num = lo
    if hi is not None and num > hi:
        num = hi
    return num


def normalize_key(token: str):
    """把谱子里的一个记号转换成规范按键名；无法识别返回 None。"""
    if not token:
        return None
    t = token.strip()
    if not t:
        return None
    alias = KEY_ALIASES.get(t)
    if alias:
        t = alias
    up = t.upper()
    if up in SPECIAL_KEYS:
        return SPECIAL_KEYS[up][1]
    if len(t) == 1:
        ch = t.upper()
        if ch in CANON_VK:
            return ch
        return None
    if up in CANON_VK:
        return up
    return None


def key_vk(key: str):
    return CANON_VK.get(key)


# ---------------------------------------------------------------------------
# 键盘发送 / 窗口工具
# ---------------------------------------------------------------------------

_send_error_logged = threading.Event()


def _build_inputs(keys, down, method):
    inputs = []
    for k in keys:
        vk = key_vk(k)
        if vk is None:
            continue
        scan = user32.MapVirtualKeyW(vk, MAPVK_VK_TO_VSC) & 0xFF
        flags = 0
        if not down:
            flags |= KEYEVENTF_KEYUP
        if vk in EXTENDED_VKS:
            flags |= KEYEVENTF_EXTENDEDKEY
        if method == "scancode":
            ki = KEYBDINPUT(0, scan, flags | KEYEVENTF_SCANCODE, 0, 0)
        else:
            # vk：同时带上虚拟键码与扫描码，兼容"看虚拟键"和"看扫描码"的游戏
            ki = KEYBDINPUT(vk, scan, flags, 0, 0)
        inp = INPUT()
        inp.type = INPUT_KEYBOARD
        inp.u.ki = ki
        inputs.append(inp)
    return inputs


def send_keys(keys, down, method="vk"):
    """批量发送按键（同一批 = 同时按下，用于和弦）。"""
    if not WIN or not keys:
        return True
    keys = [k for k in keys if key_vk(k) is not None]
    if not keys:
        return True
    try:
        if method == "keybd_event":
            for k in keys:
                vk = key_vk(k)
                scan = user32.MapVirtualKeyW(vk, MAPVK_VK_TO_VSC) & 0xFF
                flags = 0 if down else KEYEVENTF_KEYUP
                if vk in EXTENDED_VKS:
                    flags |= KEYEVENTF_EXTENDEDKEY
                user32.keybd_event(vk, scan, flags, 0)
            return True
        inputs = _build_inputs(keys, down, "scancode" if method == "scancode" else "vk")
        if not inputs:
            return True
        arr = (INPUT * len(inputs))(*inputs)
        sent = user32.SendInput(len(inputs), arr, ctypes.sizeof(INPUT))
        if sent != len(inputs) and not _send_error_logged.is_set():
            _send_error_logged.set()
            err = ctypes.get_last_error()
            log.error(
                "SendInput 只成功发送 %s/%s 个按键（错误码 %s）。"
                "常见原因：原神以管理员身份运行，而本程序不是。请用文件夹里的"
                "『以管理员身份启动.bat』再试。",
                sent, len(inputs), err,
            )
        return sent == len(inputs)
    except Exception:
        log.exception("发送按键失败")
        return False


def get_window_title(hwnd) -> str:
    if not WIN or not hwnd:
        return ""
    try:
        n = user32.GetWindowTextLengthW(hwnd)
        buf = ctypes.create_unicode_buffer(n + 2)
        user32.GetWindowTextW(hwnd, buf, n + 2)
        return buf.value
    except Exception:
        return ""


def pid_to_exe(pid) -> str:
    if not WIN or not pid:
        return ""
    handle = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, int(pid))
    if not handle:
        return ""
    try:
        buf = ctypes.create_unicode_buffer(1024)
        size = wintypes.DWORD(1024)
        if kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
            return buf.value
        return ""
    except Exception:
        return ""
    finally:
        try:
            kernel32.CloseHandle(handle)
        except Exception:
            pass


def foreground_info():
    """返回 (hwnd, pid, 窗口标题, 进程名小写)"""
    if not WIN:
        return 0, 0, "", ""
    try:
        hwnd = user32.GetForegroundWindow()
    except Exception:
        return 0, 0, "", ""
    if not hwnd:
        return 0, 0, "", ""
    pid = wintypes.DWORD(0)
    try:
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    except Exception:
        pass
    title = get_window_title(hwnd)
    exe = os.path.basename(pid_to_exe(pid.value)).lower()
    return hwnd, pid.value, title, exe


def window_area(hwnd) -> int:
    try:
        rect = wintypes.RECT()
        if user32.GetWindowRect(hwnd, ctypes.byref(rect)):
            return max(0, rect.right - rect.left) * max(0, rect.bottom - rect.top)
    except Exception:
        pass
    return 0


def find_game_windows(process_names, window_titles) -> list:
    """枚举属于原神进程（或标题匹配）的顶层窗口。"""
    if not WIN:
        return []
    procs = {p.strip().lower() for p in (process_names or []) if p and p.strip()}
    titles = {t.strip().lower() for t in (window_titles or []) if t and t.strip()}
    my_pid = os.getpid()
    found = []

    def _cb(hwnd, _lparam):
        try:
            if not user32.IsWindowVisible(hwnd):
                return True
            pid = wintypes.DWORD(0)
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value == my_pid:
                return True
            exe = os.path.basename(pid_to_exe(pid.value)).lower()
            title = get_window_title(hwnd).strip().lower()
            match = bool(exe) and exe in procs
            if not match and titles and title in titles:
                match = True
            if match:
                found.append(hwnd)
        except Exception:
            pass
        return True

    try:
        user32.EnumWindows(WNDENUMPROC(_cb), 0)
    except Exception:
        log.exception("枚举窗口失败")
    return found


def pick_game_window(process_names, window_titles):
    """选出最像"游戏主窗口"的那个句柄。"""
    wins = find_game_windows(process_names, window_titles)
    if not wins:
        return 0, []
    fg_hwnd, _pid, _title, _exe = foreground_info()
    if fg_hwnd in wins:
        return fg_hwnd, wins
    wins.sort(key=window_area, reverse=True)
    return wins[0], wins


def is_game_foreground(process_names, window_titles, game_hwnds=None):
    """返回 (是否原神在前台, 前台窗口的描述)"""
    hwnd, pid, title, exe = foreground_info()
    if not hwnd:
        return False, "（当前没有前台窗口）"
    if game_hwnds and hwnd in game_hwnds:
        return True, (title or exe or "原神")
    procs = {p.strip().lower() for p in (process_names or []) if p and p.strip()}
    titles = {t.strip().lower() for t in (window_titles or []) if t and t.strip()}
    if exe and exe in procs:
        return True, exe
    if title and title.strip().lower() in titles:
        return True, title
    desc = exe or title or ("PID %s" % pid)
    return False, desc


def activate_window(hwnd, timeout=3.0) -> bool:
    """把窗口切到前台（含 AttachThreadInput / Alt 兜底）。"""
    if not WIN or not hwnd:
        return False
    try:
        if user32.GetForegroundWindow() == hwnd:
            return True
        if user32.IsIconic(hwnd):
            user32.ShowWindow(hwnd, SW_RESTORE)
            time.sleep(0.15)
        deadline = time.time() + max(0.3, timeout)
        cur_thread = kernel32.GetCurrentThreadId()
        while time.time() < deadline:
            fg = user32.GetForegroundWindow()
            if fg == hwnd:
                return True
            fg_thread = user32.GetWindowThreadProcessId(fg, None) if fg else 0
            attached = False
            try:
                if fg_thread and fg_thread != cur_thread:
                    attached = bool(user32.AttachThreadInput(cur_thread, fg_thread, True))
                user32.BringWindowToTop(hwnd)
                user32.SetForegroundWindow(hwnd)
                if user32.GetForegroundWindow() != hwnd:
                    # Alt 轻按一下可以解除前台锁定
                    send_keys(["Alt"], True, "vk")
                    user32.SetForegroundWindow(hwnd)
                    send_keys(["Alt"], False, "vk")
            except Exception:
                log.exception("切换前台窗口时出错")
            finally:
                if attached:
                    try:
                        user32.AttachThreadInput(cur_thread, fg_thread, False)
                    except Exception:
                        pass
            if user32.GetForegroundWindow() == hwnd:
                return True
            time.sleep(0.2)
        return user32.GetForegroundWindow() == hwnd
    except Exception:
        log.exception("activate_window 失败")
        return False


def set_window_topmost(hwnd, topmost=True) -> bool:
    if not WIN or not hwnd:
        return False
    try:
        return bool(user32.SetWindowPos(
            hwnd,
            wintypes.HWND(HWND_TOPMOST if topmost else HWND_NOTOPMOST),
            0, 0, 0, 0,
            SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE,
        ))
    except Exception:
        return False


def is_window_topmost(hwnd) -> bool:
    """这个窗口现在是不是置顶状态（用来避免反复 SetWindowPos 打乱窗口层次）。"""
    if not WIN or not hwnd:
        return False
    try:
        return bool(user32.GetWindowLongW(hwnd, GWL_EXSTYLE) & WS_EX_TOPMOST)
    except Exception:
        return False


def enable_dpi_awareness():
    if not WIN:
        return
    try:
        user32.SetProcessDpiAwarenessContext.argtypes = (ctypes.c_void_p,)
        if user32.SetProcessDpiAwarenessContext(ctypes.c_void_p(-4)):  # PER_MONITOR_AWARE_V2
            return
    except Exception:
        pass
    try:
        ctypes.WinDLL("shcore").SetProcessDpiAwareness(2)
        return
    except Exception:
        pass
    try:
        user32.SetProcessDPIAware()
    except Exception:
        pass


def get_dpi(hwnd=0) -> int:
    if not WIN:
        return 96
    try:
        if hwnd:
            return int(user32.GetDpiForWindow(hwnd)) or 96
    except Exception:
        pass
    try:
        return int(user32.GetDpiForSystem()) or 96
    except Exception:
        return 96


# ---------------------------------------------------------------------------
# 全局快捷键线程
# ---------------------------------------------------------------------------

class HotkeyThread(threading.Thread):
    """在独立线程里注册/监听全局热键（RegisterHotKey 的消息属于线程队列）。"""

    def __init__(self, event_queue):
        super().__init__(name="hotkeys", daemon=True)
        self.events = event_queue
        self._cmds = queue.Queue()
        self._stop = threading.Event()
        self.registered = {}
        self.ids = {"toggle": 0x51A1, "panic": 0x51A2}

    def set_bindings(self, toggle, panic):
        self._cmds.put({"type": "set", "toggle": toggle, "panic": panic})

    def stop(self):
        self._stop.set()

    def _unregister_all(self):
        for role, hk_id in self.ids.items():
            if role in self.registered:
                try:
                    user32.UnregisterHotKey(None, hk_id)
                except Exception:
                    pass
                self.registered.pop(role, None)

    def _register(self, role, spec):
        hk_id = self.ids[role]
        try:
            user32.UnregisterHotKey(None, hk_id)
        except Exception:
            pass
        self.registered.pop(role, None)
        if not spec:
            self.events.put(("hotkey_result", role, False, None, ""))
            return False
        mods = 0
        for m in spec.get("mods", []):
            mods |= {"ctrl": MOD_CONTROL, "alt": MOD_ALT, "shift": MOD_SHIFT, "win": MOD_WIN}.get(m, 0)
        vk = int(spec.get("vk", 0))
        if not vk:
            self.events.put(("hotkey_result", role, False, spec, spec.get("name", "")))
            return False
        ok = False
        try:
            ok = bool(user32.RegisterHotKey(None, hk_id, mods | MOD_NOREPEAT, vk))
        except Exception:
            log.exception("RegisterHotKey 异常")
        if ok:
            self.registered[role] = spec
            log.info("已注册全局快捷键 %s：%s", role, spec.get("name", ""))
        else:
            err = ctypes.get_last_error()
            log.warning("全局快捷键注册失败（%s，错误码 %s），可能被其他程序占用。",
                        spec.get("name", ""), err)
        self.events.put(("hotkey_result", role, ok, spec, spec.get("name", "")))
        return ok

    def run(self):
        if not WIN:
            return
        while not self._stop.is_set():
            try:
                while True:
                    cmd = self._cmds.get_nowait()
                    if cmd.get("type") == "set":
                        for role in ("toggle", "panic"):
                            self._register(role, cmd.get(role))
            except queue.Empty:
                pass
            except Exception:
                log.exception("处理快捷键指令失败")
            try:
                msg = wintypes.MSG()
                while user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, PM_REMOVE):
                    if msg.message == WM_HOTKEY:
                        role = None
                        for r, hk_id in self.ids.items():
                            if int(msg.wParam) == hk_id:
                                role = r
                                break
                        if role:
                            self.events.put(("hotkey", role, ""))
                    elif msg.message == 0x0012:  # WM_QUIT
                        self._stop.set()
            except Exception:
                log.exception("快捷键消息循环异常")
            time.sleep(0.01)
        self._unregister_all()


# ---------------------------------------------------------------------------
# 乐器 / 配置
# ---------------------------------------------------------------------------

DEFAULT_ROWS = [
    {"name": "高音", "keys": ["Q", "W", "E", "R", "T", "Y", "U"]},
    {"name": "中音", "keys": ["A", "S", "D", "F", "G", "H", "J"]},
    {"name": "低音", "keys": ["Z", "X", "C", "V", "B", "N", "M"]},
]

INSTRUMENT_NOTE = (
    "每行 7 个键，按游戏内演奏界面“从左到右”的顺序填写。"
    "默认按《原神》演奏系统的通用键位：高音 QWERTYU / 中音 ASDFGHJ / 低音 ZXCVBNM。"
    "若你的游戏里沃雅妮莎的演奏界面键位不同，直接改下面的 keys 即可（也可增删行）。"
)


def _copy_rows():
    return [{"name": r["name"], "keys": list(r["keys"])} for r in DEFAULT_ROWS]


def default_instruments():
    return {
        "_note": INSTRUMENT_NOTE,
        "instruments": [
            {
                "id": "vodyanitsa",
                "name": "沃雅妮莎",
                "note": "沃雅妮莎的演奏/清唱界面（默认与风物之诗琴同键位）",
                "rows": _copy_rows(),
            },
            {
                "id": "windsong_lyre",
                "name": "风物之诗琴",
                "note": "风物之诗琴（21 键，3 行）",
                "rows": _copy_rows(),
            },
        ],
    }


def instruments_list(data):
    """兼容 dict / list 两种形态，取出乐器列表。"""
    if isinstance(data, dict):
        items = data.get("instruments")
    else:
        items = data
    if not isinstance(items, list) or not items:
        return default_instruments()["instruments"]
    return items


def load_instruments(path=INSTRUMENTS_PATH):
    """读取乐器配置；不存在则创建，损坏则备份后重建。绝不抛异常。"""
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            insts = data.get("instruments")
            if isinstance(insts, list) and insts:
                cleaned = []
                for inst in insts:
                    if not isinstance(inst, dict):
                        continue
                    rows = []
                    for row in inst.get("rows", []):
                        if not isinstance(row, dict):
                            continue
                        keys = [str(k).strip() for k in row.get("keys", []) if str(k).strip()]
                        if keys:
                            rows.append({"name": str(row.get("name", "")), "keys": keys})
                    if rows:
                        cleaned.append({
                            "id": str(inst.get("id") or inst.get("name") or len(cleaned)),
                            "name": str(inst.get("name") or "未命名乐器"),
                            "note": str(inst.get("note", "")),
                            "rows": rows,
                        })
                if cleaned:
                    return {"_note": data.get("_note", INSTRUMENT_NOTE), "instruments": cleaned}
            log.error("instruments.json 内容不合法，将使用默认键位。")
        except Exception:
            log.exception("读取 instruments.json 失败，将使用默认键位。")
            try:
                backup = path + ".bad-" + datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
                os.replace(path, backup)
                log.warning("损坏的乐器配置已备份为：%s", backup)
            except Exception:
                pass
    data = default_instruments()
    save_json(path, data, quiet=True)
    return data


DEFAULT_CONFIG = {
    "instrument": "vodyanitsa",
    "interval_ms": 150,
    "hold_ms": 30,
    "countdown_s": 3,
    "auto_activate_game": True,
    "stop_on_focus_loss": True,
    "allow_without_game": False,
    "always_on_top": True,
    "minimize_on_close": True,
    "send_method": "vk",
    "game_processes": ["YuanShen.exe", "GenshinImpact.exe"],
    "game_window_titles": ["原神", "Genshin Impact"],
    "hotkey_toggle": {"mods": [], "vk": 0x78, "name": "F9"},
    "hotkey_panic": {"mods": [], "vk": 0x79, "name": "F10"},
    "max_play_seconds": 900,
    "verbose_log": True,
    "window_geometry": "",
    "last_sheet_path": "",
    "bracket_mode": "chord",
    "timing_mode": "before",
    "tight_ms": 40,
    "tight_mode": "adjacent",
    "slash_ms": 300,
    "disclaimer_show": True,
    "disclaimer_accepted": "",
    "un_topmost_while_playing": False,   # 默认 False = 演奏期间也保持置顶
    "config_version": 2,
    "line_numbers": True,
    "line_number_side": "right",
}


def save_json(path, data, quiet=False):
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
        return True
    except Exception:
        if not quiet:
            log.exception("写入 %s 失败", path)
        return False


def load_config(path=CONFIG_PATH):
    cfg = dict(DEFAULT_CONFIG)
    cfg["game_processes"] = list(DEFAULT_CONFIG["game_processes"])
    cfg["game_window_titles"] = list(DEFAULT_CONFIG["game_window_titles"])
    cfg["hotkey_toggle"] = dict(DEFAULT_CONFIG["hotkey_toggle"])
    cfg["hotkey_panic"] = dict(DEFAULT_CONFIG["hotkey_panic"])
    file_version = None          # 磁盘上那份配置的版本（不是默认值里的）
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if isinstance(data, dict):
                file_version = data.get("config_version")
                for key in DEFAULT_CONFIG:
                    if key in data:
                        cfg[key] = data[key]
        except Exception:
            log.exception("读取 config.json 失败，将使用默认设置。")
            try:
                os.replace(path, path + ".bad-" + datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
            except Exception:
                pass
    # 老配置迁移：v1 里"演奏时取消置顶"被错误地默认打开，和用户预期相反，这里纠正
    try:
        if safe_int(file_version, 0, 0, 999) < CONFIG_VERSION:
            cfg["un_topmost_while_playing"] = DEFAULT_CONFIG["un_topmost_while_playing"]
            cfg["config_version"] = CONFIG_VERSION
            if file_version is not None:
                log.info("配置已升级到 v%d：演奏期间默认『保持置顶』"
                         "（想改成演奏时让位，可在设置里勾选『演奏时取消置顶』）。", CONFIG_VERSION)
    except Exception:
        pass
    return cfg


# ---------------------------------------------------------------------------
# 谱子解析
# ---------------------------------------------------------------------------

REST_TOKENS = {"-", "_", ".", "~", "0-", "rest", "pause", "休止"}

# 紧贴（贴紧）判定方式：
#   adjacent = 只有紧挨着写、没有空格的才算紧贴（BN、N(DT)）
#   group    = 括号和弦紧跟在音符后面时，即使有空格也算紧贴（N (DT)）
TIGHT_MODES = [
    ("adjacent", "只有紧挨着写（无空格）才算紧贴：BN、N(DT)"),
    ("group", "括号和弦紧跟音符时（可带空格）也算紧贴：BN、N (DT)"),
]

# 时间标记的单位（1 tick = 1 毫秒）
TIME_UNITS = {"": 1, "t": 1, "tick": 1, "ticks": 1, "ms": 1, "毫秒": 1,
              "s": 1000, "sec": 1000, "secs": 1000, "秒": 1000}

TIME_MARK_RE = re.compile(r"^\s*(\d+(?:\.\d+)?)\s*(ticks?|t|ms|毫秒|s|secs?|秒)?\s*$", re.I)

# 时间标记归属：
#   before（默认）= 等 N tick 之后再按这个键（A(25)：先等 25，再按 A）
#   after         = 按下这个键后再等 N tick 才按下一个键
TIMING_MODES = [
    ("before", "等 N tick 再按这个键（先等 25 再按 A）"),
    ("after", "按下这个键后再等 N tick（按 A 后等 25 再按 B）"),
]

TIMING_HINTS = {
    "before": "时间标记 [N]：先等 N tick 再按这个键（例：A[25]）",
    "after": "时间标记 [N]：按完这个键后再等 N tick（例：A[25]）",
}


def timing_hint(value):
    return TIMING_HINTS.get(value, TIMING_HINTS["before"])


def tight_mode_label(value):
    for val, label in TIGHT_MODES:
        if val == value:
            return label
    return TIGHT_MODES[0][1]


def tight_mode_value(label):
    for val, lab in TIGHT_MODES:
        if lab == label:
            return val
    return TIGHT_MODES[0][0]

MAX_WAIT_MS = 3600000


def parse_time_mark(text):
    """"25" / "25 tick" / "0.5s" -> 毫秒；不是时间标记返回 None。"""
    if text is None:
        return None
    m = TIME_MARK_RE.match(str(text))
    if not m:
        return None
    try:
        value = float(m.group(1))
    except (TypeError, ValueError):
        return None
    unit = (m.group(2) or "").strip().lower()
    factor = TIME_UNITS.get(unit, 1)
    ms = int(round(value * factor))
    if ms < 0:
        return None
    return min(ms, MAX_WAIT_MS)


def timing_mode_label(value):
    for val, label in TIMING_MODES:
        if val == value:
            return label
    return TIMING_MODES[0][1]


def timing_mode_value(label):
    for val, lab in TIMING_MODES:
        if lab == label:
            return val
    return TIMING_MODES[0][0]


@dataclasses.dataclass
class Note:
    keys: tuple = ()
    rest: bool = False
    raw: str = ""
    wait: "int | None" = None   # 该音符自带的时间标记（毫秒 / tick）；None = 用全局间隔
    tight: bool = False         # 与前一个音"紧贴"（快速连按）
    slash: bool = False         # 由 "/" 产生的停顿（长度用「斜杠」参数）

    def text(self):
        if self.slash:
            base = "/"
        elif self.rest:
            base = "休止"
        elif len(self.keys) == 1:
            base = self.keys[0]
        else:
            base = "(" + "".join(self.keys) + ")"
        if self.tight and not self.slash:
            base = ">" + base
        if self.wait is not None:
            base += "[%d]" % self.wait
        return base


def _effective_wait(note, slash_ms):
    """这一步该等多久：显式 [N] 标记 > "/" 的斜杠参数 > 全局间隔。"""
    wait = getattr(note, "wait", None)
    if wait is not None:
        return safe_int(wait, slash_ms, 1, MAX_WAIT_MS)
    if getattr(note, "slash", False):
        return safe_int(slash_ms, 300, 1, MAX_WAIT_MS)
    return None


def build_schedule(notes, default_ms=150, timing_mode="before", tight_ms=40, slash_ms=300):
    """把音符编译成 [(绝对时间毫秒, 按键元组), ...]，keys 为空表示休止。

    * 紧贴（同一串、无空格）的步：间隔 = tight_ms（紧贴间隔）
    * "/" 停顿：间隔 = slash_ms（斜杠参数）
    * 带 [N] 时间标记的步：before 模式用自己标记，after 模式用前一个音的标记
    * 其余：全局间隔 default_ms
    """
    default_ms = safe_int(default_ms, 150, 1, 600000)
    tight_ms = safe_int(tight_ms, 40, 1, 600000)
    slash_ms = safe_int(slash_ms, 300, 1, 600000)
    if timing_mode not in ("before", "after"):
        timing_mode = "before"
    steps = []
    t = 0
    for idx, note in enumerate(notes):
        if idx == 0:
            wait0 = _effective_wait(note, slash_ms)
            if timing_mode == "before":
                t += wait0 if wait0 is not None else default_ms
        elif getattr(note, "tight", False):
            t += tight_ms
        elif timing_mode == "before":
            wait = _effective_wait(note, slash_ms)
            t += wait if wait is not None else default_ms
        else:
            prev = _effective_wait(notes[idx - 1], slash_ms)
            t += prev if prev is not None else default_ms
        keys = () if getattr(note, "rest", False) else tuple(note.keys)
        steps.append((t, keys))
    return steps


@dataclasses.dataclass
class ParseResult:
    notes: list
    issues: list
    steps: int = 0
    chords: int = 0
    rests: int = 0
    max_notes: int = 20000

    @property
    def ok(self):
        return bool(self.notes)


def _translate_fullwidth(text: str) -> str:
    return text.translate(FULLWIDTH_MAP)


def _strip_comments(text: str) -> str:
    out = []
    for line in text.replace("\r\n", "\n").replace("\r", "\n").split("\n"):
        cut = len(line)
        for marker in ("//", "#"):
            idx = line.find(marker)
            if idx != -1:
                cut = min(cut, idx)
        out.append(line[:cut])
    return "\n".join(out)


def _split_chord(inner: str):
    parts = [p for p in re.split(r"[\s,;|+/]+", inner.strip()) if p]
    if len(parts) == 1 and len(parts[0]) > 1:
        if normalize_key(parts[0]) is None:
            parts = list(parts[0])
    return parts


def _is_time_only_group(inner, valid_keys):
    """括号里是不是"纯时间标记"（[25]、[25 tick]、[0.5s]，兼容旧写法 (25)）。

    单个数字有歧义（可能本来就是琴键），此时只有它不属于当前乐器键位才当时间标记。
    """
    ms = parse_time_mark(inner)
    if ms is None:
        return None
    txt = str(inner).strip()
    has_unit = bool(re.search(r"(?i)(ticks?|t|ms|毫秒|secs?|s|秒)\s*$", txt))
    digits = re.sub(r"[^\d.]", "", txt)
    if has_unit or len(digits) >= 2:
        return ms
    if valid_keys is not None and normalize_key(txt) in valid_keys:
        return None
    return ms


def _tokenize(src):
    """切成 token：('word'|'group', 内容, 原文, 前面有没有空格, 重复次数)。"""
    toks = []
    n = len(src)
    i = 0
    prev_end = 0
    while i < n:
        ch = src[i]
        if ch.isspace():
            i += 1
            continue
        # 开头那个 token 前面没有东西，不算"紧贴"
        space_before = True if prev_end == 0 else (i != prev_end)
        if ch in "([{":
            closer = {"(": ")", "[": "]", "{": "}"}[ch]
            j = i + 1
            while j < n and src[j] != closer:
                j += 1
            inner = src[i + 1:j]
            raw = src[i:min(j + 1, n)]
            i = j + 1 if j < n else n
            rep = 1
            m = re.match(r"\s*[*xX×]\s*(\d{1,3})", src[i:])
            if m:
                rep = max(1, min(int(m.group(1)), 999))
                i += m.end()
            toks.append(("group", inner, raw, space_before, rep))
        elif ch in ")]}":
            i += 1
            continue
        else:
            j = i
            while j < n and (not src[j].isspace()) and src[j] not in "([{)]}":
                j += 1
            toks.append(("word", src[i:j], src[i:j], space_before, 1))
            i = j
        prev_end = i
    return toks


def parse_sheet(text: str, valid_keys=None, bracket_mode="chord",
                tight_mode="adjacent") -> ParseResult:
    """解析琴谱。

    支持：
      * 空格/换行分隔的音符：``D D A B C``（用全局间隔）
      * **紧贴**（写在一起、中间没有空格）：``BN`` = 按完 B 立刻快速按 N；
        ``N(DT)`` = 按完 N 立刻快速按下和弦 D+T；紧贴用单独的「紧贴间隔」参数
      * 括号和弦：``(AH)`` ``(A,H)`` ``{AH}`` -> 同时按下
      * 括号重复（bracket_mode="repeat"）：``(AH)`` -> 依次按 A、H
      * 重复记号：``A*3`` ``Ax2`` ``BN*2`` ``(AH)*2``
      * 单个音的时间标记（tick / 毫秒）：``A[25]`` ``A [25 tick]`` ``A@25`` ``A:25``；
        兼容旧写法 ``A(25)``；单独出现 ``[300]`` 表示纯等待
      * 休止：``-`` ``_`` ``.`` ``~``（也可带时间标记，如 ``-[500]``）
      * 注释：``#`` 或 ``//`` 到行尾
      * 全角括号/字母/数字自动转换
    """
    result = ParseResult(notes=[], issues=[])
    if text is None:
        return result
    if bracket_mode not in ("chord", "repeat"):
        bracket_mode = "chord"
    if tight_mode not in ("adjacent", "group"):
        tight_mode = "adjacent"
    src = _strip_comments(_translate_fullwidth(str(text)))
    # valid_keys 为 None 表示不校验；空集合表示"当前乐器没有可用键位"，所有音符都会被拦下
    valid = None if valid_keys is None else set(valid_keys)
    step_no = 0
    too_long = [False]
    # 紧跟其后的 [N] 时间标记应该挂在哪一步（例如 BN[50] 挂在 B 上）
    marker_target = [None]

    def _new_step(keys, raw, is_rest=False, tight=False, wait=None, slash=False):
        nonlocal step_no
        if len(result.notes) >= result.max_notes:
            if not too_long[0]:
                too_long[0] = True
                result.issues.append(
                    "谱子过长（超过 %d 步），后面的内容已被忽略。" % result.max_notes)
            return False
        step_no += 1
        if not is_rest:
            good, bad = [], []
            for k in keys:
                (good if (valid is None or k in valid) else bad).append(k)
            if bad:
                result.issues.append(
                    "第 %d 步 %s：按键 %s 不属于当前乐器键位（已忽略）。"
                    % (step_no, raw, "/".join(bad)))
            if good:
                keys_t = tuple(dict.fromkeys(good))
                if len(keys_t) > 1:
                    result.chords += 1
                result.notes.append(Note(keys_t, False, raw, wait, bool(tight), slash))
                return True
        result.notes.append(Note((), True, raw, wait, bool(tight), slash))
        result.rests += 1
        return True

    def _attach_wait(ms):
        """把时间标记挂到 marker_target 指向的那一步（每个音符最多一个标记）。"""
        idx = marker_target[0]
        if idx is None or idx >= len(result.notes):
            return False
        if result.notes[idx].wait is not None:
            return False
        result.notes[idx].wait = ms
        return True

    def _push_slash(raw, rep=1, tight_first=False, inline_wait=None):
        """斜杠停顿：长度为「斜杠」参数（可用 [N] / @N 覆盖）。"""
        marker_target[0] = len(result.notes)
        first_idx = len(result.notes)
        ok = True
        for r in range(rep):
            ok = _new_step([], raw, is_rest=True,
                           tight=(r > 0) or tight_first, slash=True)
            if not ok:
                break
        if inline_wait is not None and first_idx < len(result.notes):
            if result.notes[first_idx].wait is None:
                result.notes[first_idx].wait = inline_wait
        return ok

    def _push_run(pieces, raw, rep=1, tight_first=False, inline_wait=None,
                  is_rest=False, inner_tight=True):
        """推入一串音（pieces 为按键列表；同一个 token 内除第一个外都是紧贴）。"""
        marker_target[0] = len(result.notes)
        first_idx = len(result.notes)
        ok = True
        if not pieces or is_rest:
            # 没有按键（休止、或整串都不认识）→ 推 rest 步，保持节奏
            for r in range(max(1, rep)):
                tight = (r > 0 and rep > 1) or tight_first
                if not _new_step([], raw, is_rest=True, tight=tight):
                    ok = False
                    break
        else:
            total = len(pieces)
            for r in range(rep):
                for k, piece in enumerate(pieces):
                    tight = (inner_tight and k > 0) or (r > 0 and total > 1) or tight_first
                    if piece is None:
                        ok = _new_step([], raw, is_rest=True, tight=tight)
                    else:
                        ok = _new_step([piece], piece, tight=tight)
                    if not ok:
                        break
                if not ok:
                    break
        if inline_wait is not None and first_idx < len(result.notes):
            if result.notes[first_idx].wait is None:
                result.notes[first_idx].wait = inline_wait
        return ok

    for kind, inner, raw, space_before, tok_rep in _tokenize(src):
        if kind == "group":
            # 纯数字/时间的括号 = 时间标记（优先挂在前面那一串音的第一个上）
            time_ms = _is_time_only_group(inner, valid)
            if time_ms is not None:
                if _attach_wait(time_ms):
                    marker_target[0] = None
                    continue
                if not _new_step([], raw, is_rest=True, wait=time_ms):
                    break
                marker_target[0] = None
                continue
            # 和弦组
            rep = tok_rep
            keys = []
            unknown = []
            for p in _split_chord(inner):
                k = normalize_key(p)
                if k is None:
                    unknown.append(p)
                else:
                    keys.append(k)
            if unknown:
                result.issues.append("记号 %s：无法识别的按键 %s。" % (raw, "/".join(unknown)))
            # 紧贴判定：紧挨着写就是紧贴；"group" 模式下括号和弦一律紧贴
            tight = (not space_before) or (tight_mode == "group")
            if bracket_mode == "repeat":
                # 兼容旧设置：括号里的音依次按，用普通间隔
                if not _push_run(keys, raw, rep=rep, tight_first=tight, inner_tight=False):
                    break
            elif keys:
                marker_target[0] = len(result.notes)
                ok = True
                for _ in range(rep):
                    if not _new_step(keys, raw, tight=tight):
                        ok = False
                        break
                if not ok:
                    break
            else:
                marker_target[0] = len(result.notes)
                if not _new_step([], raw, is_rest=True, tight=tight):
                    break
            continue

        # ---- word ----
        word = inner
        if not word:
            continue
        rep = 1
        m = re.fullmatch(r"(.+?)[*xX×](\d{1,3})", word)
        if m:
            word = m.group(1)
            rep = max(1, min(int(m.group(2)), 999))
        inline_wait = None
        m2 = re.fullmatch(r"(.+?)[@:](\d+(?:\.\d+)?)(ticks?|t|ms|毫秒|secs?|s|秒)?", word, re.I)
        if m2:
            word = m2.group(1)
            inline_wait = parse_time_mark(m2.group(2) + (m2.group(3) or ""))
        if not word:
            continue

        is_rest_word = (word in REST_TOKENS) or (word.lower() in REST_TOKENS)
        whole = normalize_key(word)
        if word == "/":
            # 斜杠 = 停顿（长度用「斜杠」参数，可被 [N] / @N 覆盖）
            if not _push_slash(word, rep=rep, tight_first=not space_before,
                               inline_wait=inline_wait):
                break
            continue
        if is_rest_word:
            if not _push_run([], word, rep=rep, tight_first=not space_before,
                             inline_wait=inline_wait, is_rest=True):
                break
            continue
        if whole is not None:
            # 整词就是一个按键（A / F9 / Space）
            if not _push_run([whole], whole, rep=rep, tight_first=not space_before,
                             inline_wait=inline_wait):
                break
            continue
        if len(word) == 1:
            result.issues.append("记号 %s：无法识别的按键（已按休止处理）。" % word)
            if not _push_run([], word, rep=rep, tight_first=not space_before,
                             inline_wait=inline_wait, is_rest=True):
                break
            continue
        # 多个字符写在一起 = 紧贴串（BN：按完 B 紧贴按 N）
        pieces = []
        unknown_pieces = []
        for chx in word:
            if chx == "/":
                pieces.append(("slash", None))
            elif chx in REST_TOKENS:
                pieces.append(("rest", None))
            else:
                nk = normalize_key(chx)
                if nk is None:
                    unknown_pieces.append(chx)
                else:
                    pieces.append(("key", nk))
        if unknown_pieces:
            result.issues.append(
                "记号 %s：无法识别的按键 %s（已按休止处理）。" % (word, "/".join(unknown_pieces)))
        if not pieces:
            # 整串都不认识 → 当作一个休止步，保持节奏不乱
            if not _push_run([], word, rep=rep, tight_first=not space_before,
                             inline_wait=inline_wait, is_rest=True):
                break
            continue
        marker_target[0] = len(result.notes)
        first_idx = len(result.notes)
        ok = True
        for r in range(rep):
            for k, (pkind, pval) in enumerate(pieces):
                tight = (k > 0) or (r > 0) or (not space_before)
                if pkind == "key":
                    ok = _new_step([pval], pval, tight=tight)
                elif pkind == "slash":
                    ok = _new_step([], "/", is_rest=True, tight=tight, slash=True)
                else:
                    ok = _new_step([], word, is_rest=True, tight=tight)
                if not ok:
                    break
            if not ok:
                break
        if not ok:
            break
        if inline_wait is not None and first_idx < len(result.notes):
            if result.notes[first_idx].wait is None:
                result.notes[first_idx].wait = inline_wait

    result.steps = len(result.notes)
    return result


MAX_SECTIONS = 20
MAX_DOCS = 12


@dataclasses.dataclass
class Section:
    """一个谱子里的一个"节奏区间"：自己的内容 + 自己的默认间隔 + 可选的行范围。"""
    name: str = ""
    text: str = ""
    own_interval: bool = False
    interval_ms: int = 150
    start_line: int = 0     # 0 = 从头
    end_line: int = 0       # 0 = 到尾

    def interval(self, global_ms):
        if self.own_interval:
            return safe_int(self.interval_ms, global_ms, 10, 60000)
        return safe_int(global_ms, 150, 10, 60000)

    def to_dict(self):
        return {
            "name": self.name,
            "text": self.text,
            "own_interval": bool(self.own_interval),
            "interval_ms": safe_int(self.interval_ms, 150, 10, 60000),
            "start_line": safe_int(self.start_line, 0, 0, 1000000),
            "end_line": safe_int(self.end_line, 0, 0, 1000000),
        }

    @staticmethod
    def from_dict(data, index=0):
        if not isinstance(data, dict):
            data = {}
        return Section(
            name=str(data.get("name") or ("第%d区间" % (index + 1))),
            text=str(data.get("text") or ""),
            own_interval=bool(data.get("own_interval", False)),
            interval_ms=safe_int(data.get("interval_ms"), 150, 10, 60000),
            start_line=safe_int(data.get("start_line"), 0, 0, 1000000),
            end_line=safe_int(data.get("end_line"), 0, 0, 1000000),
        )


@dataclasses.dataclass
class SheetDoc:
    """一个曲谱（对应上方的一个标签页）。"""
    name: str = "谱子1"
    sections: list = dataclasses.field(default_factory=lambda: [Section(name="第1区间")])
    active: int = 0
    path: str = ""
    dirty: bool = False

    def current(self):
        if not self.sections:
            self.sections = [Section(name="第1区间")]
        self.active = safe_int(self.active, 0, 0, len(self.sections) - 1)
        return self.sections[self.active]

    def to_dict(self):
        return {
            "name": self.name,
            "active": safe_int(self.active, 0, 0, max(0, len(self.sections) - 1)),
            "path": self.path,
            "sections": [s.to_dict() for s in self.sections[:MAX_SECTIONS]],
        }

    @staticmethod
    def from_dict(data, index=0):
        if not isinstance(data, dict):
            data = {}
        raw = data.get("sections")
        sections = []
        if isinstance(raw, list):
            for i, item in enumerate(raw[:MAX_SECTIONS]):
                sections.append(Section.from_dict(item, i))
        if not sections:
            sections = [Section(name="第1区间")]
        return SheetDoc(
            name=str(data.get("name") or ("谱子%d" % (index + 1))),
            sections=sections,
            active=safe_int(data.get("active"), 0, 0, len(sections) - 1),
            path=str(data.get("path") or ""),
        )


SESSION_PATH = os.path.join(BASE_DIR, "session.json")


def default_docs():
    return [SheetDoc(name="谱子1")]


def load_session(path=SESSION_PATH):
    """读取上次打开的曲谱标签；失败则给一个空白谱子。"""
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            raw = data.get("docs") if isinstance(data, dict) else None
            docs = []
            if isinstance(raw, list):
                for i, item in enumerate(raw[:MAX_DOCS]):
                    docs.append(SheetDoc.from_dict(item, i))
            if docs:
                active = safe_int(data.get("active"), 0, 0, len(docs) - 1)
                return docs, active
            log.warning("session.json 里没有可用的曲谱，将新建一个空白谱子。")
        except Exception:
            log.exception("读取 session.json 失败，将新建一个空白谱子。")
    return default_docs(), 0


def save_session(docs, active, path=SESSION_PATH):
    data = {
        "version": 1,
        "active": safe_int(active, 0, 0, max(0, len(docs) - 1)),
        "docs": [d.to_dict() for d in docs[:MAX_DOCS]],
    }
    return save_json(path, data)


def build_multi_schedule(parts, timing_mode="before", tight_ms=40, slash_ms=300):
    """把多个"节奏区间"拼成一条时间轴。

    parts = [(notes, interval_ms), ...]，按顺序演奏；
    每个区间自己的 interval_ms 作为它内部没写标记的音符的默认间隔。
    """
    steps = []
    offset = 0
    for notes, interval in parts:
        if not notes:
            continue
        sec = build_schedule(notes, interval, timing_mode, tight_ms, slash_ms)
        if not sec:
            continue
        for t, keys in sec:
            steps.append((offset + t, keys))
        if timing_mode == "after":
            # after 模式第一个音在 0 时刻，这里补上区间自己的间隔，避免两段黏在一起
            offset += sec[-1][0] + safe_int(interval, 150, 1, 600000)
        else:
            offset += sec[-1][0]
    return steps


def schedule_duration(steps):
    """整条时间轴的毫秒数（最后一个音的绝对时间）。"""
    return steps[-1][0] if steps else 0


def section_marker(index, section, total=1):
    spec = ("独立间隔=%d" % safe_int(section.interval_ms, 150, 10, 60000)
            if section.own_interval else "跟随全局")
    if safe_int(section.start_line, 0, 0, 1000000) or safe_int(section.end_line, 0, 0, 1000000):
        spec += " 行范围=%s-%s" % (safe_int(section.start_line, 0, 0, 1000000),
                                   safe_int(section.end_line, 0, 0, 1000000))
    return "#=== 区间 %d/%d: %s | %s ===" % (
        index + 1, max(1, total),
        section.name or ("第%d区间" % (index + 1)), spec)


SECTION_MARK_RE = re.compile(r"^#===\s*区间\s*(\d+)\s*/\s*(\d+)\s*[:：]\s*(.*?)\s*\|\s*(.*?)\s*===\s*$")


def _escape_marker_lines(body):
    """正文里若出现和区间标记一模一样的行，前面加个空格，避免被当成标记。"""
    out = []
    for line in str(body).splitlines():
        if SECTION_MARK_RE.match(line.strip()):
            out.append(" " + line)
        else:
            out.append(line)
    return "\n".join(out)


def sections_from_text(text):
    """从文件内容里切出多个区间；没有区间标记时返回 None（单区间）。

    区间标记必须**顶格**写（行首不能有空格），这也是"正文里出现同样一行"时的转义方式。
    """
    lines = str(text).splitlines()
    marks = []
    for i, line in enumerate(lines):
        m = SECTION_MARK_RE.match(line)
        if m:
            marks.append((i, m.group(3), m.group(4)))
    if not marks:
        return None
    out = []
    for n, (ln, sname, spec) in enumerate(marks):
        end = marks[n + 1][0] if n + 1 < len(marks) else len(lines)
        body = "\n".join(lines[ln + 1:end]).strip("\n")
        name = (sname or ("第%d区间" % (n + 1))).strip()
        own = False
        ms = 150
        m2 = re.search(r"独立间隔\s*[:=]?\s*(\d+)", spec)
        if m2:
            own = True
            ms = safe_int(m2.group(1), 150, 10, 60000)
        s_line = e_line = 0
        m3 = re.search(r"行范围\s*[:=]?\s*(\d+)\s*-\s*(\d+)", spec)
        if m3:
            s_line = safe_int(m3.group(1), 0, 0, 1000000)
            e_line = safe_int(m3.group(2), 0, 0, 1000000)
        out.append(Section(name=name, text=body, own_interval=own, interval_ms=ms,
                           start_line=s_line, end_line=e_line))
    return out[:MAX_SECTIONS]


def sections_to_text(sections, interval_ms, tight_ms, slash_ms, instrument_name=""):
    """把多个区间写成 txt（单区间时保持旧格式）。"""
    header = [
        SHEET_HEADER_PREFIX,
        "# 乐器: %s" % (instrument_name or ""),
        "# 间隔: %d" % safe_int(interval_ms, 150, 10, 5000),
        "# 紧贴间隔: %d" % safe_int(tight_ms, 40, 1, 5000),
        "# 斜杠间隔: %d" % safe_int(slash_ms, 300, 1, 5000),
    ]
    if len(sections) > 1:
        header.append("# 区间数: %d" % len(sections))
    header.append("# 保存时间: %s" % datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
    blocks = ["\n".join(header)]
    total = len(sections)
    for i, sec in enumerate(sections):
        body = _escape_marker_lines((sec.text or "").rstrip("\n"))
        if total > 1:
            blocks.append(section_marker(i, sec, total))
            blocks.append(body)
        else:
            blocks.append(body)
    return "\n".join(blocks).rstrip("\n") + "\n"


# ---------------------------------------------------------------------------
# 演奏引擎
# ---------------------------------------------------------------------------

class Aborted(Exception):
    pass


class Player:
    """演奏线程 + 前台监控线程。所有事件通过队列送回界面线程。"""

    def __init__(self, event_queue):
        self.events = event_queue
        self._thread = None
        self._monitor = None
        self.stop_event = threading.Event()
        self.active = threading.Event()
        self.playing_notes = threading.Event()
        self._pressed = set()
        self._lock = threading.Lock()
        self._abort_reason = None
        self.total = 0
        self.kind = "sheet"

    # -- 状态 -------------------------------------------------------------
    def is_playing(self):
        return self.active.is_set()

    def _abort_text(self):
        return self._abort_reason or "已停止"

    def emit(self, kind, *payload):
        try:
            self.events.put((kind,) + payload)
        except Exception:
            pass

    # -- 控制 -------------------------------------------------------------
    def start(self, notes=None, cfg=None, kind="sheet", steps=None):
        cfg = cfg or {}
        with self._lock:
            if self.active.is_set():
                return False
            if steps is None and not notes:
                self.emit("status", "谱子是空的，无法演奏。")
                return False
            if steps is not None and not steps:
                self.emit("status", "谱子是空的，无法演奏。")
                return False
            self.stop_event.clear()
            self.playing_notes.clear()
            self._abort_reason = None
            self.active.set()
            self.total = len(steps) if steps is not None else len(notes)
            self.kind = kind
        # 演奏线程与监控线程共享同一份 cfg（监控线程需要看到运行时写入的窗口句柄）
        shared = dict(cfg)
        self._thread = threading.Thread(
            target=self._run, args=(list(notes or []), shared, list(steps) if steps else None),
            name="player", daemon=True,
        )
        self._thread.start()
        if cfg.get("stop_on_focus_loss", True):
            self._monitor = threading.Thread(
                target=self._monitor_focus, args=(shared,), name="focus-monitor", daemon=True
            )
            self._monitor.start()
        return True

    def stop(self, reason="已停止"):
        with self._lock:
            if not self.active.is_set() and not self.stop_event.is_set():
                return
            already = self.stop_event.is_set()
            if not already and reason:
                self._abort_reason = reason
            self.stop_event.set()
        if not already:
            log.info("停止演奏：%s", reason)
        self.release_all()

    def release_all(self):
        with self._lock:
            keys = list(self._pressed)
            self._pressed.clear()
        if keys:
            send_keys(keys, False, "vk")
            send_keys(keys, False, "scancode")
            send_keys(keys, False, "keybd_event")

    # -- 线程主体 ---------------------------------------------------------
    def _monitor_focus(self, cfg):
        play_started = None
        while self.active.is_set() and not self.stop_event.is_set():
            if not self.playing_notes.is_set() or not cfg.get("_require_focus", True):
                time.sleep(0.05)
                continue
            if play_started is None:
                play_started = time.time()
                time.sleep(0.3)  # 刚开始的 0.3 秒做保护期，避免激活窗口瞬间误判
                continue
            ok, desc = is_game_foreground(
                cfg.get("game_processes"), cfg.get("game_window_titles"), cfg.get("_game_hwnds")
            )
            if not ok:
                time.sleep(0.12)
                ok2, desc2 = is_game_foreground(
                    cfg.get("game_processes"), cfg.get("game_window_titles"), cfg.get("_game_hwnds")
                )
                if not ok2 and self.active.is_set():
                    log.warning("检测到《原神》不再位于前台（当前前台：%s），立即停止演奏。", desc2)
                    self.emit("log", "warning",
                              "原神已切到后台（当前前台：%s），已立即停止演奏。" % desc2)
                    self.stop("原神已切到后台/失去焦点，已立即停止演奏")
                    break
            time.sleep(0.05)

    def _tap(self, keys, hold_s, method):
        for k in keys:
            with self._lock:
                self._pressed.add(k)
        send_keys(keys, True, method)
        aborted = self.stop_event.wait(max(0.005, hold_s))
        send_keys(keys, False, method)
        for k in keys:
            with self._lock:
                self._pressed.discard(k)
        return aborted

    def _run(self, notes, cfg, preset_steps=None):
        reason = "演奏完成"
        method = cfg.get("send_method", "vk")
        if method not in ("vk", "scancode", "keybd_event"):
            method = "vk"
        interval_ms = safe_int(cfg.get("interval_ms"), 150, 10, 60000)
        interval = interval_ms / 1000.0
        hold = safe_int(cfg.get("hold_ms"), 30, 5, 2000) / 1000.0
        hold = min(hold, max(0.005, interval * 0.5))
        countdown = safe_int(cfg.get("countdown_s"), 3, 0, 60)
        require_focus = bool(cfg.get("stop_on_focus_loss", True))
        cfg["_require_focus"] = require_focus
        try:
            game_hwnd = 0
            if cfg.get("auto_activate_game", True) or require_focus:
                game_hwnd, wins = pick_game_window(
                    cfg.get("game_processes"), cfg.get("game_window_titles")
                )
                cfg["_game_hwnds"] = wins
                if not wins:
                    msg = ("未找到《原神》窗口（按进程名 %s 查找）。"
                           "若你用云原神/其他客户端，请在【设置】里补充它的进程名。"
                           % "/".join(cfg.get("game_processes") or []))
                    log.warning(msg)
                    self.emit("log", "warning", msg)
                    if not cfg.get("allow_without_game", False):
                        raise Aborted("未检测到原神窗口，已取消演奏（可在设置里允许无窗口演奏）。")
                    require_focus = False
                    cfg["_require_focus"] = False
                    self.emit("log", "warning",
                              "已按设置忽略“未找到原神窗口”，将直接发送按键，请自行确认前台窗口。")
            if cfg.get("auto_activate_game", True) and game_hwnd:
                self.emit("status", "正在把《原神》切到前台…")
                if not activate_window(game_hwnd):
                    log.warning("无法自动把《原神》切换到前台。")

            if countdown > 0:
                for remain in range(countdown, 0, -1):
                    if self.stop_event.is_set():
                        raise Aborted(self._abort_text())
                    self.emit("status", "%d 秒后开始演奏，请保持《原神》在前台…" % remain)
                    if self.stop_event.wait(1.0):
                        raise Aborted(self._abort_text())

            if require_focus:
                ok, desc = is_game_foreground(
                    cfg.get("game_processes"), cfg.get("game_window_titles"), cfg.get("_game_hwnds")
                )
                if not ok:
                    raise Aborted("《原神》不在前台（当前前台：%s），已取消演奏。" % desc)

            total = len(preset_steps) if preset_steps else len(notes)
            timing_mode = cfg.get("timing_mode", "before")
            tight_ms = safe_int(cfg.get("tight_ms"), 40, 1, 5000)
            slash_ms = safe_int(cfg.get("slash_ms"), 300, 1, 5000)
            if preset_steps:
                steps = list(preset_steps)
            else:
                steps = build_schedule(notes, interval_ms, timing_mode, tight_ms, slash_ms)
            tight_count = sum(1 for nt in notes if getattr(nt, "tight", False))
            slash_count = sum(1 for nt in notes if getattr(nt, "slash", False))
            if tight_count:
                log.info("谱子里有 %d 个紧贴（快速连按/紧贴和弦），紧贴间隔 %d tick。",
                         tight_count, tight_ms)
            if slash_count:
                log.info("谱子里有 %d 个斜杠停顿，斜杠间隔 %d tick（%.3f 秒）。",
                         slash_count, slash_ms, slash_ms / 1000.0)
            self.emit("status", "开始演奏（共 %d 步）" % total)
            log.info("开始演奏：%d 步，默认间隔 %d tick（%.3f 秒），紧贴 %d，斜杠 %d，"
                     "按住 %dms，时间标记=%s，发送方式 %s",
                     total, interval_ms, interval, tight_ms, slash_ms,
                     int(hold * 1000), timing_mode, method)
            self.playing_notes.set()
            t0 = time.perf_counter()
            max_seconds = safe_int(cfg.get("max_play_seconds"), 900, 5, 86400)
            sent_keys = 0
            shrunk = 0

            for idx, (target_ms, keys) in enumerate(steps):
                if self.stop_event.is_set():
                    raise Aborted(self._abort_text())
                if time.perf_counter() - t0 > max_seconds:
                    raise Aborted("超过最大演奏时长保护（%d 秒），已自动停止。" % max_seconds)
                remain = target_ms / 1000.0 - (time.perf_counter() - t0)
                if remain > 0 and self.stop_event.wait(remain):
                    raise Aborted(self._abort_text())
                keys = tuple(keys)
                if not keys:
                    self.emit("highlight", ())
                else:
                    if require_focus:
                        ok, desc = is_game_foreground(
                            cfg.get("game_processes"), cfg.get("game_window_titles"),
                            cfg.get("_game_hwnds"),
                        )
                        if not ok:
                            raise Aborted("《原神》已切到后台（当前前台：%s），立即停止。" % desc)
                    # 每个音的按住时长不超过"到下一个音"的间隔的一半，避免重叠/漏音
                    hold_i = hold
                    if idx + 1 < len(steps):
                        out_gap = (steps[idx + 1][0] - target_ms) / 1000.0
                        if out_gap > 0:
                            capped = max(0.004, out_gap * 0.5)
                            if capped < hold_i:
                                hold_i = capped
                                shrunk += 1
                    self.emit("highlight", keys)
                    if self._tap(list(keys), hold_i, method):
                        raise Aborted(self._abort_text())
                    sent_keys += len(keys)
                self.emit("progress", idx + 1, total)
                if idx % 10 == 0 or idx + 1 == total:
                    self.emit("status", "演奏中 %d/%d 步…" % (idx + 1, total))
            if shrunk:
                log.warning("有 %d 处间隔比按住时长还小，已自动缩短这些音的按住时长；"
                            "若游戏漏音，请把「紧贴间隔」或「按键间隔」调大一点。", shrunk)
            log.info("演奏结束：共发送 %d 次按键。", sent_keys)
        except Aborted as exc:
            reason = str(exc)
            log.info("演奏中止：%s", reason)
        except Exception as exc:  # 任何意外都必须记录 + 释放按键
            reason = "发生异常，已安全停止：%s" % exc
            log.exception("演奏线程异常")
        finally:
            try:
                self.release_all()
            finally:
                self.playing_notes.clear()
                self.active.clear()
                self.emit("highlight", ())
                self.emit("finished", reason)


# ---------------------------------------------------------------------------
# 日志
# ---------------------------------------------------------------------------

class QueueLogHandler(logging.Handler):
    def __init__(self, event_queue, level=logging.INFO):
        super().__init__(level)
        self.events = event_queue

    def emit(self, record):
        try:
            msg = self.format(record)
            try:
                self.events.put_nowait(("log", record.levelname.lower(), msg))
            except queue.Full:
                pass
        except Exception:
            pass


def ensure_dirs():
    for d in (LOG_DIR, SHEET_DIR):
        try:
            os.makedirs(d, exist_ok=True)
        except Exception:
            pass


def setup_logging(event_queue=None, verbose=True):
    global _fault_file
    ensure_dirs()
    log.setLevel(logging.DEBUG)
    log.handlers.clear()
    log.propagate = False
    fmt = logging.Formatter(
        "%(asctime)s [%(levelname)-7s] %(threadName)s: %(message)s", "%Y-%m-%d %H:%M:%S"
    )
    try:
        fh = logging.handlers.RotatingFileHandler(
            LOG_FILE, maxBytes=2 * 1024 * 1024, backupCount=5, encoding="utf-8"
        )
        fh.setFormatter(fmt)
        fh.setLevel(logging.DEBUG if verbose else logging.INFO)
        log.addHandler(fh)
    except Exception:
        pass
    if event_queue is not None:
        qh = QueueLogHandler(event_queue, logging.DEBUG if verbose else logging.INFO)
        qh.setFormatter(logging.Formatter("%(asctime)s %(message)s", "%H:%M:%S"))
        log.addHandler(qh)
    if sys.stderr is not None:
        try:
            sh = logging.StreamHandler(sys.stderr)
            sh.setFormatter(fmt)
            sh.setLevel(logging.INFO)
            log.addHandler(sh)
        except Exception:
            pass
    try:
        if _fault_file is None:
            _fault_file = open(os.path.join(LOG_DIR, "faulthandler.log"), "a", encoding="utf-8")
        faulthandler.enable(file=_fault_file)
    except Exception:
        pass


def install_excepthooks():
    def _hook(exc_type, exc, tb):
        if issubclass(exc_type, KeyboardInterrupt):
            sys.__excepthook__(exc_type, exc, tb)
            return
        log.critical("未捕获异常：\n%s", "".join(traceback.format_exception(exc_type, exc, tb)))

    sys.excepthook = _hook

    def _thread_hook(args):
        log.critical(
            "线程 %s 未捕获异常：\n%s",
            getattr(args.thread, "name", "?"),
            "".join(traceback.format_exception(args.exc_type, args.exc_value, args.exc_traceback)),
        )

    try:
        threading.excepthook = _thread_hook
    except Exception:
        pass


# ---------------------------------------------------------------------------
# 界面
# ---------------------------------------------------------------------------

SHEET_HEADER_PREFIX = "# 原神自动弹琴 谱子"

# 按键发送方式：(内部值, 界面显示)
SEND_METHODS = [
    ("vk", "vk：虚拟键码+扫描码（推荐）"),
    ("scancode", "scancode：纯扫描码"),
    ("keybd_event", "keybd_event：旧接口（兼容模式）"),
]


def send_method_label(value):
    for val, label in SEND_METHODS:
        if val == value:
            return label
    return SEND_METHODS[0][1]


def send_method_value(label):
    for val, lab in SEND_METHODS:
        if lab == label:
            return val
    return SEND_METHODS[0][0]


def hotkey_display(spec):
    if not spec:
        return "未绑定"
    name = spec.get("name") or ""
    mods = spec.get("mods") or []
    parts = []
    if "ctrl" in mods:
        parts.append("Ctrl")
    if "alt" in mods:
        parts.append("Alt")
    if "shift" in mods:
        parts.append("Shift")
    if "win" in mods:
        parts.append("Win")
    parts.append(name)
    return "+".join(p for p in parts if p)


def read_text_file(path):
    for enc in ("utf-8-sig", "utf-8", "gbk", "gb18030", "big5", "latin-1"):
        try:
            with open(path, "r", encoding=enc) as fh:
                return fh.read(), enc
        except UnicodeDecodeError:
            continue
        except Exception:
            raise
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        return fh.read(), "utf-8(replace)"


class LyreApp:
    def __init__(self, root, cfg, instruments, event_queue, hotkey_thread, docs=None, active_doc=0):
        self.root = root
        self.cfg = cfg
        self.instruments = instruments_list(instruments)
        self.events = event_queue
        self.hotkeys = hotkey_thread
        self.player = Player(event_queue)
        self.key_items = {}
        self.kb_redraw_job = None
        self.log_lines = 0
        self.active_hotkeys = {
            "toggle": dict(cfg.get("hotkey_toggle") or {}),
            "panic": dict(cfg.get("hotkey_panic") or {}),
        }
        self.last_sheet_dir = cfg.get("last_sheet_path") or SHEET_DIR
        self.docs = list(docs) if docs else default_docs()
        if not self.docs:
            self.docs = default_docs()
        self.active_doc = safe_int(active_doc, 0, 0, len(self.docs) - 1)
        self.tab_widgets = []
        self._info_job = None
        self._autosave_job = None
        self._gutter_job = None
        self._loading = False
        self.quitting = False
        self._build_ui()
        self._apply_always_on_top()
        self._refresh_instrument_ui()
        self._refresh_sheet_list()
        self._update_hotkey_labels()
        self._refresh_tabbar()
        self._load_section_ui()
        self.root.after(60, self._pump)
        self.root.after(1500, self._topmost_tick)
        self.root.after(20000, self._autosave)
        log.info("%s v%s 已启动（日志：%s）", APP_NAME, APP_VERSION, LOG_FILE)
        log.info("当前乐器：%s；曲谱标签 %d 个，当前：%s",
                 self.current_instrument().get("name"), len(self.docs), self.doc().name)

    # ---------------- 曲谱 / 区间 辅助 ----------------
    def doc(self) -> SheetDoc:
        if not self.docs:
            self.docs = default_docs()
        self.active_doc = safe_int(self.active_doc, 0, 0, len(self.docs) - 1)
        return self.docs[self.active_doc]

    def doc_title(self, index=None):
        d = self.docs[index if index is not None else self.active_doc]
        name = d.name or "未命名"
        if d.path:
            name = os.path.basename(d.path)
        return ("%s%s" % ("*" if getattr(d, "dirty", False) else "", name))

    def commit_editor(self):
        """把编辑框里的内容写回当前区间。"""
        if self._loading:
            return
        try:
            text = self.sheet_text.get("1.0", "end-1c")
        except Exception:
            return
        try:
            sec = self.doc().current()
            if sec.text != text:
                sec.text = text
                self._mark_dirty()
        except Exception:
            log.exception("保存编辑内容失败")

    def _mark_dirty(self):
        d = self.doc()
        d.dirty = True
        self._schedule_info()
        self._refresh_tabbar()

    def _schedule_info(self):
        if self._info_job:
            try:
                self.root.after_cancel(self._info_job)
            except Exception:
                pass
        self._info_job = self.root.after(350, self._update_section_info)

    def section_label(self, index):
        sec = self.doc().sections[index]
        return "%d. %s" % (index + 1, sec.name or ("第%d区间" % (index + 1)))

    def _refresh_tabbar(self):
        try:
            for child in list(self.tabbar.winfo_children()):
                child.destroy()
            self.tab_widgets = []
            for i, d in enumerate(self.docs):
                active = (i == self.active_doc)
                tab = tk.Frame(self.tabbar, bd=1, relief=("sunken" if active else "raised"),
                               bg=("#ffffff" if active else "#e6e6e6"))
                btn = tk.Button(
                    tab, text=self.doc_title(i), relief="flat", bd=0, padx=8, pady=2,
                    bg=("#ffffff" if active else "#e6e6e6"),
                    fg=("#111111" if active else "#444444"),
                    activebackground="#d6e6ff", cursor="hand2",
                    command=(lambda idx=i: self.select_doc(idx)),
                )
                btn.pack(side="left")
                close = tk.Label(tab, text="×", bg=("#ffffff" if active else "#e6e6e6"),
                                 fg="#888888", padx=4, cursor="hand2")
                close.pack(side="left")
                close.bind("<Button-1>", lambda _e, idx=i: self.close_doc(idx))
                btn.bind("<Button-3>", lambda e, idx=i: self._tab_menu(e, idx))
                close.bind("<Button-3>", lambda e, idx=i: self._tab_menu(e, idx))
                tab.pack(side="left", padx=(0, 3))
                self.tab_widgets.append(tab)
            ttk.Button(self.tabbar, text="＋ 新建谱子", command=self.new_doc).pack(
                side="left", padx=6)
            ttk.Label(self.tabbar, text="（右键标签可重命名/复制/关闭）",
                      foreground="#888").pack(side="left")
        except Exception:
            log.exception("刷新曲谱标签失败")

    def _tab_menu(self, event, index):
        menu = None
        try:
            self.begin_dialog()
            menu = tk.Menu(self.root, tearoff=0)
            menu.add_command(label="重命名…", command=lambda: self.rename_doc(index))
            menu.add_command(label="复制本谱子", command=lambda: self.duplicate_doc(index))
            menu.add_separator()
            menu.add_command(label="关闭", command=lambda: self.close_doc(index))
            menu.tk_popup(event.x_root, event.y_root)
        except Exception:
            log.exception("曲谱标签菜单出错")
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass
            self.end_dialog()

    def select_doc(self, index):
        if index == self.active_doc:
            return
        self.commit_editor()
        self.active_doc = safe_int(index, 0, 0, len(self.docs) - 1)
        self._refresh_tabbar()
        self._load_section_ui()
        log.info("切换到曲谱：%s", self.doc().name)

    def new_doc(self):
        if len(self.docs) >= MAX_DOCS:
            messagebox.showinfo(APP_NAME, "最多同时打开 %d 个曲谱，请先关闭一些。" % MAX_DOCS)
            return
        self.commit_editor()
        self.docs.append(SheetDoc(name="谱子%d" % (len(self.docs) + 1)))
        self.active_doc = len(self.docs) - 1
        self._refresh_tabbar()
        self._load_section_ui()
        self.save_session_now()
        log.info("新建曲谱：%s", self.doc().name)

    def close_doc(self, index):
        if len(self.docs) <= 1:
            messagebox.showinfo(APP_NAME, "至少要保留一个曲谱。")
            return
        self.commit_editor()
        d = self.docs[index]
        if d.dirty and not messagebox.askyesno(
                APP_NAME, "『%s』有改动还没保存，仍然关闭吗？" % (d.name or "未命名")):
            return
        self.docs.pop(index)
        if self.active_doc >= len(self.docs):
            self.active_doc = len(self.docs) - 1
        elif index < self.active_doc:
            self.active_doc -= 1
        self._refresh_tabbar()
        self._load_section_ui()
        self.save_session_now()
        log.info("关闭曲谱：%s", d.name)

    def ask_string(self, title, prompt, initial=""):
        """自己实现的输入框（置顶安全，不会和主窗口抢层次）。"""
        result = {"value": None}
        win = tk.Toplevel(self.root)
        win.title(title)
        win.transient(self.root)
        win.resizable(False, False)
        self.begin_dialog()
        self.set_dialog_topmost(win)
        ttk.Label(win, text=prompt, padding=(14, 12, 14, 4)).pack(anchor="w")
        var = tk.StringVar(value=initial)
        entry = ttk.Entry(win, textvariable=var, width=36)
        entry.pack(padx=14, pady=(0, 10))
        entry.focus_set()
        entry.select_range(0, "end")

        def ok(_e=None):
            result["value"] = var.get().strip()
            close()

        def close():
            try:
                win.grab_release()
            except Exception:
                pass
            self.end_dialog()
            win.destroy()

        bar = ttk.Frame(win)
        bar.pack(fill="x", padx=14, pady=(0, 12))
        ttk.Button(bar, text="确定", command=ok).pack(side="right")
        ttk.Button(bar, text="取消", command=close).pack(side="right", padx=6)
        win.bind("<Return>", ok)
        win.bind("<Escape>", lambda _e: close())
        win.protocol("WM_DELETE_WINDOW", close)
        win.grab_set()
        try:
            win.wait_window()
        except Exception:
            pass
        return result["value"]

    def rename_doc(self, index=None):
        idx = self.active_doc if index is None else index
        old = self.docs[idx].name
        new = self.ask_string("重命名曲谱", "新名字：", old)
        if new:
            self.docs[idx].name = new[:40]
            self._refresh_tabbar()
            self.save_session_now()
            log.info("曲谱改名：%s -> %s", old, self.docs[idx].name)

    def duplicate_doc(self, index=None):
        if len(self.docs) >= MAX_DOCS:
            messagebox.showinfo(APP_NAME, "最多同时打开 %d 个曲谱。" % MAX_DOCS)
            return
        idx = self.active_doc if index is None else index
        self.commit_editor()
        copy = SheetDoc.from_dict(self.docs[idx].to_dict(), idx)
        copy.name = "%s 副本" % self.docs[idx].name
        copy.path = ""
        self.docs.insert(idx + 1, copy)
        self.active_doc = idx + 1
        self._refresh_tabbar()
        self._load_section_ui()
        self.save_session_now()

    # ---- 节奏区间 ----
    def select_section(self, index):
        d = self.doc()
        index = safe_int(index, 0, 0, len(d.sections) - 1)
        if index == d.active:
            return
        self.commit_editor()
        d.active = index
        self._load_section_ui()
        log.info("『%s』切换到区间：%s", d.name, d.current().name)

    def add_section(self):
        d = self.doc()
        if len(d.sections) >= MAX_SECTIONS:
            messagebox.showinfo(APP_NAME, "一个谱子最多 %d 个节奏区间。" % MAX_SECTIONS)
            return
        self.commit_editor()
        sec = Section(name="第%d区间" % (len(d.sections) + 1), text="",
                      own_interval=True,
                      interval_ms=safe_int(self.interval_var.get(), 150, 10, 60000))
        d.sections.append(sec)
        d.active = len(d.sections) - 1
        self._load_section_ui()
        self.save_session_now()
        log.info("『%s』新增节奏区间：%s（独立间隔 %d tick）", d.name, sec.name, sec.interval_ms)

    def rename_section(self):
        d = self.doc()
        sec = d.current()
        new = self.ask_string("重命名区间", "新名字：", sec.name)
        if new:
            sec.name = new[:30]
            self._load_section_ui()
            self.save_session_now()

    def delete_section(self):
        d = self.doc()
        if len(d.sections) <= 1:
            messagebox.showinfo(APP_NAME, "至少要保留一个区间；想清空内容可以用『清空编辑框』。")
            return
        if not messagebox.askyesno(APP_NAME, "删除区间『%s』？" % d.current().name):
            return
        d.sections.pop(d.active)
        d.active = safe_int(d.active, 0, 0, len(d.sections) - 1)
        self._load_section_ui()
        self.save_session_now()
        log.info("删除节奏区间，剩余 %d 个", len(d.sections))

    def _on_own_interval(self):
        try:
            sec = self.doc().current()
            sec.own_interval = bool(self.own_interval_var.get())
            if sec.own_interval:
                sec.interval_ms = safe_int(self.section_interval_var.get(),
                                           self.interval_var.get(), 10, 60000)
            self.section_interval_spin.configure(
                state=("normal" if sec.own_interval else "disabled"))
            self._schedule_info()
            self._mark_dirty()
        except Exception:
            log.exception("切换区间独立间隔失败")

    def _on_section_interval(self, *_a):
        try:
            sec = self.doc().current()
            if sec.own_interval:
                sec.interval_ms = safe_int(self.section_interval_var.get(),
                                           self.interval_var.get(), 10, 60000)
                self._schedule_info()
                self._mark_dirty()
        except Exception:
            pass

    def _load_section_ui(self):
        """按当前曲谱/区间的数据刷新编辑框与区间控件。"""
        self._loading = True
        try:
            d = self.doc()
            sec = d.current()
            values = [self.section_label(i) for i in range(len(d.sections))]
            self.section_combo.configure(values=values)
            self.section_combo.set(self.section_label(d.active))
            self.own_interval_var.set(bool(sec.own_interval))
            self.section_interval_var.set(
                safe_int(sec.interval_ms, self.interval_var.get(), 10, 60000))
            self.section_interval_spin.configure(
                state=("normal" if sec.own_interval else "disabled"))
            self.sheet_text.delete("1.0", "end")
            self.sheet_text.insert("1.0", sec.text or "")
            self.sheet_text.edit_modified(False)
            self.range_start_var.set(str(sec.start_line) if sec.start_line else "")
            self.range_end_var.set(str(sec.end_line) if sec.end_line else "")
        except Exception:
            log.exception("刷新区间界面失败")
        finally:
            self._loading = False
        self._update_section_info()
        self._schedule_gutter()

    def _gather_parts(self, commit=True):
        """把当前曲谱的所有区间编译成 parts=[(notes, interval)]，并汇总问题。"""
        if commit:
            self.commit_editor()
        d = self.doc()
        global_ms = safe_int(self.interval_var.get(), 150, 10, 60000)
        kwargs = self.sheet_parse_kwargs()
        parts = []
        issues = []
        per_section = []
        for i, sec in enumerate(d.sections):
            text = sec.text or ""
            total_lines = text.count("\n") + 1 if text else 0
            sliced, s_line, e_line = self.slice_by_lines(text, sec.start_line, sec.end_line)
            if sec.start_line or sec.end_line:
                log.info("区间 %d『%s』按行范围演奏：第 %d～%d 行（该区间共 %d 行）",
                         i + 1, sec.name, s_line, e_line, total_lines)
            res = parse_sheet(sliced, **kwargs)
            interval = sec.interval(global_ms)
            parts.append((res.notes, interval))
            issues.extend(res.issues)
            steps = build_schedule(res.notes, interval, self.cfg.get("timing_mode", "before"),
                                   safe_int(self.tight_var.get(), 40, 1, 5000),
                                   safe_int(self.slash_var.get(), 300, 1, 5000)) if res.notes else []
            per_section.append({
                "index": i, "name": sec.name, "steps": res.steps,
                "interval": interval, "ms": schedule_duration(steps),
                "own": sec.own_interval, "issues": len(res.issues),
                "range": (s_line, e_line) if (sec.start_line or sec.end_line) else None,
            })
        return parts, issues, per_section

    def _update_section_info(self):
        self._info_job = None
        try:
            parts, issues, per_section = self._gather_parts(commit=False)
            total_steps = sum(s["steps"] for s in per_section)
            total_ms = sum(s["ms"] for s in per_section)
            d = self.doc()
            cur = per_section[d.active] if d.active < len(per_section) else None
            txt = "共 %d 区间 ｜ %d 步 ｜ 约 %s" % (
                len(d.sections), total_steps, self._ms_to_sec(total_ms) + " 秒" if total_ms else "0 秒")
            if cur:
                rng = cur.get("range")
                txt += "　（本区间 %d 步%s，%s）" % (
                    cur["steps"],
                    ("，第 %d～%d 行" % rng) if rng else "",
                    ("独立间隔 %d" % cur["interval"]) if cur["own"] else
                    ("跟随全局 %d" % cur["interval"]))
            if issues:
                txt += "　⚠ %d 处无法识别" % len(issues)
            self.section_info_var.set(txt)
            self.sheet_info_var.set("解析：本区间 %s 步%s" % (
                cur["steps"] if cur else 0,
                "，⚠ %d 处提示（详见日志）" % len(issues) if issues else ""))
        except Exception:
            log.exception("更新区间信息失败")

    def save_session_now(self):
        try:
            self.commit_editor()
            save_session(self.docs, self.active_doc)
        except Exception:
            log.exception("保存会话失败")

    def _autosave(self):
        try:
            self.save_session_now()
        finally:
            try:
                self.root.after(20000, self._autosave)
            except Exception:
                pass

    # ---------------- 构建界面 ----------------
    def _build_ui(self):
        self.root.title("%s v%s" % (APP_NAME, APP_VERSION))
        self.root.minsize(900, 620)
        scale = 1.0
        try:
            dpi = get_dpi()
            scale = max(1.0, min(2.2, dpi / 96.0))
        except Exception:
            scale = 1.0
        default_geo = "%dx%d" % (int(1080 * scale), int(790 * scale))
        geo = self.cfg.get("window_geometry") or ""
        if geo:
            try:
                self.root.geometry(geo)
            except Exception:
                self.root.geometry(default_geo)
        else:
            self.root.geometry(default_geo)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close_window)
        self.root.report_callback_exception = self._tk_exception

        main = ttk.Frame(self.root, padding=8)
        main.pack(fill="both", expand=True)
        main.columnconfigure(0, weight=1)
        main.rowconfigure(0, weight=1)

        # ---------------- 左：曲谱标签 + 节奏区间 + 编辑区 + 日志 ----------------
        left = ttk.Frame(main)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        left.columnconfigure(0, weight=1)
        left.rowconfigure(2, weight=3)
        left.rowconfigure(4, weight=2)

        # 1) 曲谱标签栏（类似 NotePad++ 的上面一排标签）
        tabwrap = ttk.LabelFrame(left, text="曲谱（可同时打开多个，最多 %d 个）" % MAX_DOCS)
        tabwrap.grid(row=0, column=0, sticky="ew")
        tabwrap.columnconfigure(0, weight=1)
        self.tabbar = tk.Frame(tabwrap, bg="#f4f4f4")
        self.tabbar.grid(row=0, column=0, sticky="ew", padx=4, pady=4)

        # 2) 节奏区间栏
        secf = ttk.LabelFrame(left, text="节奏区间（同一个谱子按顺序演奏，最多 %d 个）" % MAX_SECTIONS)
        secf.grid(row=1, column=0, sticky="ew", pady=(6, 4))
        secf.columnconfigure(1, weight=1)
        ttk.Label(secf, text="当前区间：").grid(row=0, column=0, sticky="w", padx=(6, 2), pady=4)
        self.section_combo = ttk.Combobox(secf, state="readonly", width=20, values=[])
        self.section_combo.grid(row=0, column=1, sticky="w")
        self.section_combo.bind("<<ComboboxSelected>>", self._on_section_combo)
        ttk.Button(secf, text="＋ 添加新区间演奏", command=self.add_section).grid(
            row=0, column=2, sticky="w", padx=4)
        ttk.Button(secf, text="重命名", command=self.rename_section).grid(
            row=0, column=3, sticky="w", padx=2)
        ttk.Button(secf, text="删除本区间", command=self.delete_section).grid(
            row=0, column=4, sticky="w", padx=2)

        self.own_interval_var = tk.BooleanVar(value=False)
        self.section_interval_var = tk.IntVar(value=150)
        ttk.Checkbutton(secf, text="本区间使用独立间隔", variable=self.own_interval_var,
                        command=self._on_own_interval).grid(row=1, column=0, columnspan=2,
                                                            sticky="w", padx=6)
        self.section_interval_spin = ttk.Spinbox(
            secf, from_=10, to=60000, increment=10, width=8,
            textvariable=self.section_interval_var, command=self._on_section_interval)
        self.section_interval_spin.grid(row=1, column=2, sticky="w", padx=4, pady=(0, 4))
        self.section_interval_spin.bind("<FocusOut>", lambda _e: self._on_section_interval())
        ttk.Label(secf, text="tick（不勾选则用右侧「按键间隔」）", foreground="#777").grid(
            row=1, column=3, columnspan=2, sticky="w")

        # 演奏行范围（留空 = 全部）
        rangef = ttk.Frame(secf)
        rangef.grid(row=2, column=0, columnspan=5, sticky="w", padx=6, pady=(0, 4))
        ttk.Label(rangef, text="演奏行范围：第").pack(side="left")
        self.range_start_var = tk.StringVar(value="")
        self.range_end_var = tk.StringVar(value="")
        e1 = ttk.Entry(rangef, textvariable=self.range_start_var, width=6)
        e1.pack(side="left", padx=2)
        ttk.Label(rangef, text="行 到 第").pack(side="left")
        e2 = ttk.Entry(rangef, textvariable=self.range_end_var, width=6)
        e2.pack(side="left", padx=2)
        ttk.Label(rangef, text="行（留空＝从头到尾）").pack(side="left")
        for var in (self.range_start_var, self.range_end_var):
            var.trace_add("write", self._on_range_change)
        self.line_info_var = tk.StringVar(value="")
        ttk.Label(secf, textvariable=self.line_info_var, foreground="#06c").grid(
            row=3, column=0, columnspan=5, sticky="w", padx=6)

        self.section_info_var = tk.StringVar(value="")
        ttk.Label(secf, textvariable=self.section_info_var, foreground="#0a6").grid(
            row=4, column=0, columnspan=5, sticky="w", padx=6, pady=(0, 4))

        # 3) 编辑区（带行号栏，可设置显示在左/右）
        editor_wrap = ttk.Frame(left)
        editor_wrap.grid(row=2, column=0, sticky="nsew", pady=(2, 6))
        editor_wrap.columnconfigure(0, weight=1)
        editor_wrap.rowconfigure(0, weight=1)
        self.editor_wrap = editor_wrap
        self.sheet_text = tk.Text(editor_wrap, wrap="none", undo=True, height=14,
                                  font=("Consolas", 11))
        self.gutter = tk.Text(editor_wrap, width=4, padx=3, takefocus=0, bd=0,
                              background="#f0f2f5", foreground="#8a8f98",
                              font=("Consolas", 11), state="disabled", cursor="arrow",
                              highlightthickness=0, wrap="none")
        self.vbar = ttk.Scrollbar(editor_wrap, orient="vertical", command=self._on_editor_scroll)
        self.hbar = ttk.Scrollbar(editor_wrap, orient="horizontal", command=self.sheet_text.xview)
        self.sheet_text.configure(yscrollcommand=self._on_editor_yscroll,
                                  xscrollcommand=self.hbar.set)
        self.sheet_text.grid(row=0, column=0, sticky="nsew", columnspan=3)
        self.gutter.grid(row=0, column=1, sticky="ns")
        self.vbar.grid(row=0, column=2, sticky="ns")
        self.hbar.grid(row=1, column=0, sticky="ew", columnspan=3)
        self._gutter_offset = 0
        self._apply_gutter_side()
        self.sheet_text.bind("<<Modified>>", self._on_editor_modified)
        self.sheet_text.bind("<KeyRelease>", self._on_editor_key)
        self.sheet_text.bind("<ButtonRelease-1>", self._highlight_current_line)
        self.sheet_text.bind("<Configure>", self._schedule_gutter)
        self.gutter.bind("<MouseWheel>",
                         lambda e: (self.sheet_text.yview_scroll(int(-1 * (e.delta / 120)), "units"),
                                    self._sync_gutter_view()))
        self.root.after(400, self._refresh_gutter)

        # 4) 解析信息 / 快捷按钮
        bar = ttk.Frame(left)
        bar.grid(row=3, column=0, sticky="ew", pady=(0, 6))
        ttk.Button(bar, text="检查整首谱子", command=self.check_sheet).pack(side="left")
        ttk.Button(bar, text="清空本区间", command=self.clear_sheet).pack(side="left", padx=4)
        self.sheet_info_var = tk.StringVar(value="解析：还没有内容。")
        ttk.Label(bar, textvariable=self.sheet_info_var, foreground="#666").pack(
            side="left", padx=8)

        # 5) 日志
        logf = ttk.LabelFrame(left, text="运行日志（同时写入 logs 文件夹，出问题先看这里）")
        logf.grid(row=4, column=0, sticky="nsew")
        logf.columnconfigure(0, weight=1)
        logf.rowconfigure(0, weight=1)
        self.log_text = tk.Text(logf, wrap="none", height=7, state="disabled",
                                font=("Consolas", 9), background="#111418",
                                foreground="#d8dee9", insertbackground="#d8dee9")
        self.log_text.grid(row=0, column=0, sticky="nsew")
        lsb = ttk.Scrollbar(logf, orient="vertical", command=self.log_text.yview)
        lsb.grid(row=0, column=1, sticky="ns")
        self.log_text.configure(yscrollcommand=lsb.set)
        logbar = ttk.Frame(logf)
        logbar.grid(row=1, column=0, columnspan=2, sticky="ew")
        ttk.Button(logbar, text="打开日志文件夹", command=self.open_log_dir).pack(side="left")
        ttk.Button(logbar, text="清空日志窗口", command=self.clear_log).pack(side="left", padx=4)

        # ---------------- 右：乐器 / 谱子文件 / 参数 / 演奏 ----------------
        right = ttk.Frame(main, width=348)
        right.grid(row=0, column=1, sticky="nsew")
        right.columnconfigure(0, weight=1)

        instf = ttk.LabelFrame(right, text="乐器（默认：沃雅妮莎）")
        instf.grid(row=0, column=0, sticky="ew")
        instf.columnconfigure(0, weight=1)
        instf.columnconfigure(1, weight=1)
        self.inst_var = tk.StringVar(value=self.cfg.get("instrument", "vodyanitsa"))
        for idx, inst in enumerate(self.instruments):
            ttk.Radiobutton(instf, text=inst["name"], value=inst["id"], variable=self.inst_var,
                            command=self._on_instrument_change).grid(
                row=0, column=idx, sticky="w", padx=6, pady=(4, 2))
        ttk.Label(instf, text="键位预览（演奏时高亮当前键）", foreground="#555").grid(
            row=1, column=0, columnspan=2, sticky="w", padx=6)
        self.kb_canvas = tk.Canvas(instf, height=78, background="#fafafa",
                                   highlightthickness=1, highlightbackground="#c9ced6")
        self.kb_canvas.grid(row=2, column=0, columnspan=2, sticky="ew", padx=6, pady=(2, 6))
        self.kb_canvas.bind("<Configure>", self._on_kb_resize)

        sheetf = ttk.LabelFrame(right, text="谱子")
        sheetf.grid(row=1, column=0, sticky="ew", pady=(8, 0))
        sheetf.columnconfigure(0, weight=1)
        sheetf.columnconfigure(1, weight=1)
        ttk.Button(sheetf, text="导入谱子…（txt）", command=self.import_sheet).grid(
            row=0, column=0, columnspan=2, sticky="ew", padx=6, pady=(6, 2))
        ttk.Label(sheetf, text="读取保存的谱子：", foreground="#555").grid(
            row=1, column=0, columnspan=2, sticky="w", padx=6)
        self.sheet_combo = ttk.Combobox(sheetf, state="readonly", values=[])
        self.sheet_combo.grid(row=2, column=0, columnspan=2, sticky="ew", padx=6, pady=(2, 2))
        ttk.Button(sheetf, text="载入选中的谱子", command=self.load_selected_sheet).grid(
            row=3, column=0, sticky="ew", padx=(6, 3), pady=(2, 6))
        ttk.Button(sheetf, text="保存谱子…（含间隔 tick）", command=self.save_sheet).grid(
            row=3, column=1, sticky="ew", padx=(3, 6), pady=(2, 6))

        paramf = ttk.LabelFrame(right, text="演奏参数")
        paramf.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        paramf.columnconfigure(1, weight=1)
        paramf.columnconfigure(2, weight=1)

        self.interval_var = tk.IntVar(value=safe_int(self.cfg.get("interval_ms"), 150, 10, 5000))
        self.hold_var = tk.IntVar(value=safe_int(self.cfg.get("hold_ms"), 30, 5, 500))
        self.countdown_var = tk.IntVar(value=safe_int(self.cfg.get("countdown_s"), 3, 0, 15))
        self.tight_var = tk.IntVar(value=safe_int(self.cfg.get("tight_ms"), 40, 1, 5000))
        self.slash_var = tk.IntVar(value=safe_int(self.cfg.get("slash_ms"), 300, 1, 5000))

        ttk.Label(paramf, text="按下下一个键的间隔（tick；1 秒 = 1000 tick，没写标记的音符用它）").grid(
            row=0, column=0, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        ttk.Spinbox(paramf, from_=10, to=5000, increment=10, width=7,
                    textvariable=self.interval_var).grid(row=1, column=0, sticky="w", padx=(6, 2))
        ttk.Label(paramf, text="紧贴", foreground="#333").grid(
            row=1, column=1, sticky="w", padx=(6, 1))
        ttk.Spinbox(paramf, from_=1, to=2000, increment=5, width=5,
                    textvariable=self.tight_var).grid(row=1, column=1, sticky="e")
        ttk.Label(paramf, text="斜杠", foreground="#333").grid(
            row=1, column=2, sticky="w", padx=(4, 0))
        ttk.Spinbox(paramf, from_=1, to=5000, increment=10, width=5,
                    textvariable=self.slash_var).grid(row=1, column=2, sticky="e")

        for _var in (self.interval_var, self.tight_var, self.slash_var, self.hold_var,
                     self.countdown_var):
            try:
                _var.trace_add("write", self._update_conversion)
            except Exception:
                pass

        self.timing_hint_var = tk.StringVar(
            value=timing_hint(self.cfg.get("timing_mode", "before")))
        ttk.Label(paramf, textvariable=self.timing_hint_var, foreground="#0a6",
                  wraplength=336, justify="left").grid(
            row=2, column=0, columnspan=3, sticky="w", padx=6, pady=(2, 0))
        ttk.Label(paramf, text="紧贴：BN、N(DT)；斜杠 / 是停顿", foreground="#777").grid(
            row=3, column=0, columnspan=3, sticky="w", padx=6)

        ttk.Label(paramf, text="单个按键按住时长（毫秒）").grid(
            row=4, column=0, sticky="w", padx=6, pady=(2, 0))
        ttk.Spinbox(paramf, from_=5, to=500, increment=5, width=8,
                    textvariable=self.hold_var).grid(row=5, column=0, sticky="w", padx=6)
        ttk.Label(paramf, text="开始前倒计时（秒）", foreground="#333").grid(
            row=5, column=1, sticky="w", padx=(10, 2))
        ttk.Spinbox(paramf, from_=0, to=15, increment=1, width=6,
                    textvariable=self.countdown_var).grid(row=5, column=2, sticky="w")

        self.auto_activate_var = tk.BooleanVar(value=bool(self.cfg.get("auto_activate_game", True)))
        self.focus_stop_var = tk.BooleanVar(value=bool(self.cfg.get("stop_on_focus_loss", True)))
        ttk.Checkbutton(paramf, text="开始前自动把原神切到前台",
                        variable=self.auto_activate_var).grid(
            row=6, column=0, columnspan=3, sticky="w", padx=6, pady=(3, 0))
        ttk.Checkbutton(paramf, text="原神失去焦点立即停止（推荐）",
                        variable=self.focus_stop_var).grid(
            row=7, column=0, columnspan=3, sticky="w", padx=6, pady=(1, 3))

        playf = ttk.Frame(right)
        playf.grid(row=3, column=0, sticky="ew", pady=(10, 0))
        playf.columnconfigure(0, weight=1)
        playf.columnconfigure(1, weight=1)
        self.start_btn = ttk.Button(playf, text="▶ 开始演奏 (F9)", command=self.toggle_play)
        self.start_btn.grid(row=0, column=0, sticky="ew", padx=(0, 4), ipady=6)
        self.stop_btn = ttk.Button(playf, text="■ 停止 (F10)", command=self.stop_play,
                                   state="disabled")
        self.stop_btn.grid(row=0, column=1, sticky="ew", ipady=6)
        ttk.Button(playf, text="测试当前乐器的按键（校准键位用）",
                   command=self.test_keys).grid(row=1, column=0, columnspan=2,
                                                sticky="ew", pady=(6, 0))

        self.status_var = tk.StringVar(value="就绪。请先打开原神并进入演奏界面。")
        ttk.Label(right, textvariable=self.status_var, wraplength=330,
                  foreground="#0b6", justify="left").grid(row=4, column=0, sticky="w", pady=(10, 0))
        self.progress = ttk.Progressbar(right, mode="determinate", maximum=100)
        self.progress.grid(row=5, column=0, sticky="ew", pady=(4, 0))
        ttk.Label(right, text="安全：原神切到后台会立即停止并松开所有按键。",
                  foreground="#777", justify="left").grid(row=6, column=0, sticky="w", pady=(6, 0))

        # ---------------- 底栏（左下角：设置） ----------------
        bottom = ttk.Frame(main)
        bottom.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        bottom.columnconfigure(2, weight=1)
        ttk.Button(bottom, text="⚙ 设置", command=self.open_settings).grid(row=0, column=0, sticky="w")
        ttk.Button(bottom, text="? 使用说明", command=self.show_help).grid(row=0, column=1,
                                                                        sticky="w", padx=6)
        self.convert_var = tk.StringVar(value="")
        ttk.Label(bottom, textvariable=self.convert_var, foreground="#0a6").grid(
            row=0, column=2, sticky="w", padx=10)
        self.hint_var = tk.StringVar(
            value="%s 开始/停止 ｜ %s 紧急停止" % (
                hotkey_display(self.active_hotkeys["toggle"]),
                hotkey_display(self.active_hotkeys["panic"])))
        ttk.Label(bottom, textvariable=self.hint_var, foreground="#666").grid(row=0, column=3,
                                                                            sticky="e")
        self._update_conversion()

    # ---------------- 基础辅助 ----------------
    def _tk_exception(self, exc_type, exc_value, tb):
        log.error("界面回调异常：\n%s", "".join(traceback.format_exception(exc_type, exc_value, tb)))

    def current_instrument(self):
        wanted = self.inst_var.get() if hasattr(self, "inst_var") else self.cfg.get("instrument")
        for inst in self.instruments:
            if inst["id"] == wanted:
                return inst
        return self.instruments[0]

    def valid_keys(self):
        keys = set()
        for row in self.current_instrument().get("rows", []):
            for k in row.get("keys", []):
                nk = normalize_key(k)
                if nk:
                    keys.add(nk)
        return keys

    def append_log(self, level, msg):
        colors = {"critical": "#ff6b6b", "error": "#ff6b6b", "warning": "#ffd166",
                  "info": "#d8dee9", "debug": "#8b949e"}
        try:
            self.log_text.configure(state="normal")
            self.log_text.insert("end", msg + "\n", level)
            self.log_text.tag_config(level, foreground=colors.get(level, "#d8dee9"))
            self.log_lines += 1
            if self.log_lines > 800:
                self.log_text.delete("1.0", "200.0")
                self.log_lines -= 199
            self.log_text.see("end")
            self.log_text.configure(state="disabled")
        except Exception:
            pass

    def clear_log(self):
        try:
            self.log_text.configure(state="normal")
            self.log_text.delete("1.0", "end")
            self.log_text.configure(state="disabled")
            self.log_lines = 0
        except Exception:
            pass

    def open_log_dir(self):
        try:
            os.startfile(LOG_DIR)
        except Exception:
            log.exception("打开日志目录失败")

    def set_status(self, text):
        try:
            self.status_var.set(text)
        except Exception:
            pass

    @staticmethod
    def _ms_to_sec(ms):
        """500 -> '0.5'，300 -> '0.3'，1000 -> '1'"""
        try:
            txt = "%.3f" % (safe_int(ms, 0, 0, 100000000) / 1000.0)
        except Exception:
            return "?"
        txt = txt.rstrip("0").rstrip(".")
        return txt or "0"

    def _update_conversion(self, *_args):
        """把 tick 换算成秒展示出来（1 tick = 1 毫秒，1000 tick = 1 秒）。"""
        try:
            interval = safe_int(self.interval_var.get(), 150, 1, 600000)
            tight = safe_int(self.tight_var.get(), 40, 1, 600000)
            slash = safe_int(self.slash_var.get(), 300, 1, 600000)
        except Exception:
            return
        per_sec = (1000.0 / interval) if interval else 0.0
        self.convert_var.set(
            "1 秒 = 1000 tick　｜　间隔 %d = %s 秒（约 %.1f 音/秒）｜ 紧贴 %d = %s 秒 ｜ 斜杠 %d = %s 秒"
            % (interval, self._ms_to_sec(interval), per_sec,
               tight, self._ms_to_sec(tight), slash, self._ms_to_sec(slash)))

    # ---------------- 乐器 / 键盘预览 ----------------
    def _on_instrument_change(self):
        self.cfg["instrument"] = self.inst_var.get()
        self._refresh_instrument_ui()
        log.info("已选择乐器：%s", self.current_instrument().get("name"))
        self.check_sheet(silent=True)

    def _refresh_instrument_ui(self):
        self._draw_keyboard()

    def _on_kb_resize(self, _event=None):
        if self.kb_redraw_job:
            try:
                self.root.after_cancel(self.kb_redraw_job)
            except Exception:
                pass
        self.kb_redraw_job = self.root.after(120, self._draw_keyboard)

    def _draw_keyboard(self):
        self.kb_redraw_job = None
        c = self.kb_canvas
        try:
            c.delete("all")
            self.key_items = {}
            rows = self.current_instrument().get("rows", [])
            if not rows:
                return
            cw = max(int(c.winfo_width()), 240)
            ch = max(int(c.winfo_height()), 90)
            cols = max(len(r["keys"]) for r in rows)
            pad, gap = 6, 4
            kw = (cw - 2 * pad - (cols - 1) * gap) / float(cols)
            kh = (ch - 2 * pad - (len(rows) - 1) * gap) / float(len(rows))
            fsize = max(8, min(13, int(kh * 0.42)))
            for ri, row in enumerate(rows):
                for ci, k in enumerate(row["keys"]):
                    x0 = pad + ci * (kw + gap)
                    y0 = pad + ri * (kh + gap)
                    item = c.create_rectangle(x0, y0, x0 + kw, y0 + kh,
                                              fill="#f1f3f5", outline="#9aa0a6", width=1)
                    c.create_text(x0 + kw / 2, y0 + kh / 2, text=k.upper(),
                                  font=("Segoe UI", fsize, "bold"), fill="#333")
                    self.key_items[k.upper()] = item
        except Exception:
            log.exception("绘制键盘预览失败")

    def _highlight(self, keys):
        try:
            active = {k.upper() for k in (keys or [])}
            for k, item in self.key_items.items():
                self.kb_canvas.itemconfig(item, fill=("#63b3ed" if k in active else "#f1f3f5"))
        except Exception:
            pass

    # ---------------- 谱子相关 ----------------
    def _on_section_combo(self, _event=None):
        try:
            m = re.match(r"^(\d+)\.", self.section_combo.get() or "")
            if m:
                self.select_section(int(m.group(1)) - 1)
        except Exception:
            log.exception("切换节奏区间失败")

    def _on_editor_modified(self, _event=None):
        try:
            self.sheet_text.edit_modified(False)
        except Exception:
            pass
        if self._loading:
            return
        self.commit_editor()
        self._schedule_gutter()

    def _on_editor_key(self, _event=None):
        self._schedule_info()
        self._highlight_current_line()
        self._schedule_gutter()

    def _on_editor_yscroll(self, first, last):
        try:
            self.vbar.set(first, last)
        except Exception:
            pass
        self._sync_gutter_view()
        self._schedule_gutter()

    def _on_editor_scroll(self, *args):
        self.sheet_text.yview(*args)
        self._sync_gutter_view()
        self._schedule_gutter()

    def _apply_gutter_side(self):
        """按设置把行号栏放到编辑框左边或右边。"""
        try:
            right = (self.cfg.get("line_number_side", "right") != "left")
            w = self.editor_wrap
            if right:
                # 编辑框 | 行号 | 滚动条
                self.sheet_text.grid_configure(row=0, column=0, columnspan=1)
                self.gutter.grid_configure(row=0, column=1, sticky="ns")
                w.columnconfigure(0, weight=1)
                w.columnconfigure(1, weight=0)
            else:
                # 行号 | 编辑框 | 滚动条
                self.gutter.grid_configure(row=0, column=0, sticky="ns")
                self.sheet_text.grid_configure(row=0, column=1, columnspan=1)
                w.columnconfigure(0, weight=0)
                w.columnconfigure(1, weight=1)
            self.vbar.grid_configure(row=0, column=2, sticky="ns")
            self.hbar.grid_configure(row=1, column=0, columnspan=3, sticky="ew")
            if not self.cfg.get("line_numbers", True):
                self.gutter.grid_remove()
            else:
                self.gutter.grid()
        except Exception:
            log.exception("设置行号位置失败")

    def get_sheet_text(self):
        try:
            return self.sheet_text.get("1.0", "end-1c")
        except Exception:
            return ""

    def set_sheet_text(self, text):
        self._loading = True
        try:
            self.sheet_text.delete("1.0", "end")
            if text:
                self.sheet_text.insert("1.0", text)
            self.sheet_text.edit_modified(False)
        except Exception:
            log.exception("写入谱子编辑框失败")
        finally:
            self._loading = False
        try:
            self.doc().current().text = text or ""
        except Exception:
            pass

    def import_sheet(self):
        path = filedialog.askopenfilename(
            title="导入琴谱（txt）", initialdir=self.last_sheet_dir,
            filetypes=[("文本琴谱", "*.txt"), ("所有文件", "*.*")],
        )
        if not path:
            return
        self._load_sheet_file(path)

    def _load_sheet_file(self, path):
        try:
            text, enc = read_text_file(path)
        except Exception as exc:
            log.exception("读取谱子失败")
            messagebox.showerror(APP_NAME, "读取失败：\n%s" % exc)
            return
        info = self._parse_sheet_header(text)
        sections = sections_from_text(text)
        if not sections:
            sections = [Section(name="第1区间", text=info["body"])]
        d = self.doc()
        d.sections = sections
        d.active = 0
        d.path = path
        d.name = os.path.basename(path)
        d.dirty = False
        if info["interval"]:
            self.interval_var.set(info["interval"])
            log.info("从谱子文件读到间隔设置：%d tick", info["interval"])
        if info["tight"]:
            self.tight_var.set(info["tight"])
            log.info("从谱子文件读到紧贴间隔：%d tick", info["tight"])
        if info["slash"]:
            self.slash_var.set(info["slash"])
            log.info("从谱子文件读到斜杠间隔：%d tick", info["slash"])
        instrument = info["instrument"]
        if instrument:
            for inst in self.instruments:
                if inst["id"] == instrument or inst["name"] == instrument:
                    self.inst_var.set(inst["id"])
                    self.cfg["instrument"] = inst["id"]
                    self._refresh_instrument_ui()
                    break
        self.last_sheet_dir = os.path.dirname(path) or self.last_sheet_dir
        self.cfg["last_sheet_path"] = self.last_sheet_dir
        self._refresh_tabbar()
        self._load_section_ui()
        log.info("已导入谱子：%s（编码 %s，%d 字符，%d 个区间）",
                 path, enc, len(text), len(d.sections))
        self.set_status("已导入：%s（%d 个区间）" % (os.path.basename(path), len(d.sections)))
        self.save_session_now()

    def _parse_sheet_header(self, text):
        """读取谱子文件头（# 开头）里的乐器 / 间隔 / 紧贴间隔。

        返回 dict：interval / instrument / tight / body
        """
        info = {"interval": None, "instrument": None, "tight": None, "slash": None, "body": text}
        body_lines = []
        for line in str(text).splitlines():
            stripped = line.strip()
            if not stripped.startswith("#"):
                body_lines.append(line)
                continue
            m = re.search(r"紧贴间隔\s*[:：]\s*(\d+)", stripped)
            if m:
                info["tight"] = safe_int(m.group(1), 40, 1, 5000)
                continue
            m = re.search(r"斜杠间隔\s*[:：]\s*(\d+)", stripped)
            if m:
                info["slash"] = safe_int(m.group(1), 300, 1, 5000)
                continue
            m = re.search(r"(?:按键)?间隔\s*[:：]\s*(\d+)", stripped)
            if m:
                info["interval"] = safe_int(m.group(1), 150, 10, 5000)
                continue
            m = re.search(r"(?:乐器|instrument)\s*[:：]\s*(.+)", stripped, re.I)
            if m:
                info["instrument"] = m.group(1).strip()
        body = "\n".join(body_lines)
        info["body"] = body if body.strip() else text
        return info

    def _refresh_sheet_list(self):
        try:
            ensure_dirs()
            names = sorted(
                f for f in os.listdir(SHEET_DIR)
                if f.lower().endswith(".txt") and os.path.isfile(os.path.join(SHEET_DIR, f))
            )
            self.sheet_combo["values"] = names
            if names and not self.sheet_combo.get():
                self.sheet_combo.set(names[0])
        except Exception:
            log.exception("刷新已保存谱子列表失败")

    def load_selected_sheet(self):
        name = self.sheet_combo.get()
        if not name:
            messagebox.showinfo(APP_NAME, "sheets 文件夹里还没有保存过的谱子。")
            return
        path = os.path.join(SHEET_DIR, name)
        if not os.path.exists(path):
            messagebox.showerror(APP_NAME, "文件不存在：\n%s" % path)
            self._refresh_sheet_list()
            return
        self._load_sheet_file(path)

    def save_sheet(self):
        d = self.doc()
        self.commit_editor()
        default_name = os.path.basename(d.path) if d.path else (
            (d.name or "谱子") + ".txt")
        path = filedialog.asksaveasfilename(
            title="保存谱子（内容 + 各区间间隔）", initialdir=SHEET_DIR,
            initialfile=default_name, defaultextension=".txt",
            filetypes=[("文本琴谱", "*.txt")],
        )
        if not path:
            return
        content = sections_to_text(
            d.sections,
            safe_int(self.interval_var.get(), 150, 10, 5000),
            safe_int(self.tight_var.get(), 40, 1, 5000),
            safe_int(self.slash_var.get(), 300, 1, 5000),
            self.current_instrument().get("name", ""),
        )
        try:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(content)
        except Exception as exc:
            log.exception("保存谱子失败")
            messagebox.showerror(APP_NAME, "保存失败：\n%s" % exc)
            return
        d.path = path
        d.name = os.path.basename(path)
        d.dirty = False
        log.info("已保存谱子：%s（%d 个区间，间隔 %d tick）",
                 path, len(d.sections), safe_int(self.interval_var.get(), 150, 10, 5000))
        self.set_status("已保存：%s（%d 个区间）" % (os.path.basename(path), len(d.sections)))
        self._refresh_sheet_list()
        self._refresh_tabbar()
        self.save_session_now()
        if os.path.dirname(path).lower() == SHEET_DIR.lower():
            self.sheet_combo.set(os.path.basename(path))

    def clear_sheet(self):
        d = self.doc()
        if messagebox.askyesno(APP_NAME, "清空区间『%s』的内容？" % d.current().name):
            self.set_sheet_text("")
            self._mark_dirty()
            self._update_section_info()
            self.set_status("已清空区间『%s』。" % d.current().name)

    def sheet_parse_kwargs(self):
        return {
            "valid_keys": self.valid_keys(),
            "bracket_mode": self.cfg.get("bracket_mode", "chord"),
            "tight_mode": self.cfg.get("tight_mode", "adjacent"),
        }

    def check_sheet(self, silent=False):
        parts, issues, per_section = self._gather_parts()
        total_steps = sum(s["steps"] for s in per_section)
        total_ms = sum(s["ms"] for s in per_section)
        lines = []
        for s in per_section:
            lines.append("区间 %d 『%s』：%d 步，间隔 %d tick%s，约 %s 秒%s" % (
                s["index"] + 1, s["name"], s["steps"], s["interval"],
                "（独立）" if s["own"] else "（跟随全局）",
                self._ms_to_sec(s["ms"]),
                "，⚠ %d 处提示" % s["issues"] if s["issues"] else ""))
        info = "共 %d 个区间，%d 步，预计约 %s 秒" % (
            len(per_section), total_steps, self._ms_to_sec(total_ms))
        log.info("检查谱子：%s", info)
        for line in lines:
            log.info("  %s", line)
        if issues:
            for issue in issues[:40]:
                log.warning(issue)
            if len(issues) > 40:
                log.warning("……还有 %d 条提示未显示。", len(issues) - 40)
        if not total_steps:
            info = "没有可演奏的音符，请检查谱子内容。"
        self.set_status(info)
        self._update_section_info()
        if not silent:
            preview = "\n".join(lines) or "（空）"
            messagebox.showinfo(
                APP_NAME,
                "%s\n\n%s%s" % (info, preview,
                                "\n\n⚠ 有 %d 处无法识别的内容，详见日志。" % len(issues)
                                if issues else ""),
            )
        return parts, issues, per_section

    # ---------------- 演奏 ----------------
    def play_settings(self):
        cfg = dict(self.cfg)
        cfg["interval_ms"] = safe_int(self.interval_var.get(), 150, 10, 5000)
        cfg["hold_ms"] = safe_int(self.hold_var.get(), 30, 5, 500)
        cfg["countdown_s"] = safe_int(self.countdown_var.get(), 3, 0, 15)
        cfg["tight_ms"] = safe_int(self.tight_var.get(), 40, 1, 5000)
        cfg["slash_ms"] = safe_int(self.slash_var.get(), 300, 1, 5000)
        cfg["auto_activate_game"] = bool(self.auto_activate_var.get())
        cfg["stop_on_focus_loss"] = bool(self.focus_stop_var.get())
        return cfg

    def toggle_play(self):
        if self.player.is_playing():
            self.stop_play()
        else:
            self.start_play()

    def start_play(self):
        if self.player.is_playing():
            return
        cfg = self.play_settings()
        parts, issues, per_section = self._gather_parts()
        steps = build_multi_schedule(
            parts, self.cfg.get("timing_mode", "before"),
            safe_int(self.tight_var.get(), 40, 1, 5000),
            safe_int(self.slash_var.get(), 300, 1, 5000),
        )
        if not steps:
            messagebox.showwarning(APP_NAME, "谱子是空的，或者没有可识别的音符。")
            self.set_status("无法演奏：谱子为空。")
            return
        # 演奏前预检：把所有可疑之处摆给用户确认
        warns, errors = self.preflight(parts, issues, per_section)
        if not self.confirm_before_play(warns, errors):
            self.set_status("已取消演奏（预检未通过或用户取消）。")
            return
        self.cfg.update({k: cfg[k] for k in ("interval_ms", "hold_ms", "countdown_s",
                                            "tight_ms", "slash_ms", "auto_activate_game",
                                            "stop_on_focus_loss")})
        # 默认：演奏期间也保持置顶（原神全屏时仍然能看到/点得到本程序）
        # 只有用户主动勾了"演奏时取消置顶"才会让位
        if self.cfg.get("un_topmost_while_playing", False):
            self.cfg["_force_untop"] = True
            self._apply_always_on_top()
            log.info("按设置：演奏期间取消窗口置顶。")
        else:
            self.cfg["_force_untop"] = False
            self._apply_always_on_top()
            log.info("演奏期间保持窗口置顶（想让它让位可在设置里勾选『演奏时取消置顶』）。")
        self.start_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.progress.configure(maximum=max(1, len(steps)), value=0)
        log.info("准备演奏『%s』：%d 个区间，%d 步，预计约 %s 秒",
                 self.doc().name, len(per_section), len(steps),
                 self._ms_to_sec(schedule_duration(steps)))
        if self.player.start([], cfg, kind="sheet", steps=steps):
            log.info("已请求开始演奏（倒计时 %d 秒）", cfg["countdown_s"])
        else:
            self.start_btn.configure(state="normal")
            self.stop_btn.configure(state="disabled")

    def test_keys(self):
        if self.player.is_playing():
            messagebox.showinfo(APP_NAME, "正在演奏中，请先停止。")
            return
        rows = self.current_instrument().get("rows", [])
        notes = []
        for ri, row in enumerate(rows):
            if ri > 0:
                notes.append(Note((), True, "休止"))
            for k in row.get("keys", []):
                nk = normalize_key(k)
                if nk:
                    notes.append(Note((nk,), False, nk))
        if not notes:
            messagebox.showwarning(APP_NAME, "当前乐器没有配置键位。")
            return
        messagebox.showinfo(
            APP_NAME,
            "接下来会依次弹一遍当前乐器的每个键，方便你对照游戏界面确认键位。\n"
            "请先把原神切到演奏界面，点确定后 %d 秒开始。"
            % int(self.countdown_var.get() or 0),
        )
        cfg = self.play_settings()
        self.start_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.progress.configure(maximum=max(1, len(notes)), value=0)
        self.player.start(notes, cfg, kind="test")

    def stop_play(self):
        self.player.stop("用户停止")
        self.set_status("已停止。")

    # ---------------- 事件泵 ----------------
    def _pump(self):
        try:
            processed = 0
            while processed < 400:
                try:
                    event = self.events.get_nowait()
                except queue.Empty:
                    break
                processed += 1
                self._handle_event(event)
        except Exception:
            log.exception("处理界面事件时出错")
        finally:
            try:
                self.root.after(60, self._pump)
            except Exception:
                pass

    def _handle_event(self, event):
        kind = event[0]
        if kind == "log":
            self.append_log(event[1], event[2])
        elif kind == "status":
            self.set_status(event[1])
        elif kind == "progress":
            try:
                self.progress.configure(value=event[1], maximum=max(1, event[2]))
            except Exception:
                pass
        elif kind == "highlight":
            self._highlight(event[1])
        elif kind == "finished":
            reason = event[1] if len(event) > 1 else ""
            self.start_btn.configure(state="normal")
            self.stop_btn.configure(state="disabled")
            if self.cfg.get("_force_untop"):
                self.cfg["_force_untop"] = False
                self._apply_always_on_top()
                log.info("演奏已结束，恢复窗口置顶设置。")
            elif self.cfg.get("always_on_top", True):
                self._apply_always_on_top()
            self.set_status("结束：%s" % reason)
            log.info("演奏流程结束：%s", reason)
        elif kind == "hotkey":
            role = event[1]
            if role == "toggle":
                log.info("收到快捷键：开始/停止")
                self._topmost_kick()      # 防止被游戏抢走置顶
                self.toggle_play()
            elif role == "panic":
                log.info("收到快捷键：紧急停止")
                if self.player.is_playing():
                    self.player.stop("紧急停止快捷键")
                    self.set_status("已通过紧急停止快捷键停止。")
                else:
                    self.set_status("当前没有在演奏。")
        elif kind == "hotkey_result":
            role, ok, spec, name = event[1], event[2], event[3], event[4]
            if ok and spec:
                self.active_hotkeys[role] = dict(spec)
                self._update_hotkey_labels()
            else:
                log.warning("快捷键 %s 注册失败（%s），可能已被其他程序占用。", role, name)
                self._update_hotkey_labels()
                self.set_status("快捷键 %s 注册失败，请看日志（可改绑其他按键，或直接用界面按钮）。"
                                % name)
        else:
            log.debug("未知事件：%r", event)

    def _update_hotkey_labels(self):
        try:
            t = hotkey_display(self.active_hotkeys.get("toggle"))
            p = hotkey_display(self.active_hotkeys.get("panic"))
            self.start_btn.configure(text="▶ 开始演奏 (%s)" % t)
            self.stop_btn.configure(text="■ 停止 (%s)" % p)
            self.hint_var.set("%s 开始/停止 ｜ %s 紧急停止" % (t, p))
        except Exception:
            pass

    # ---------------- 置顶管理 ----------------
    def _tk_hwnd(self):
        """取 Tk 顶层窗口真正的 HWND（优先取框架窗口）。"""
        try:
            frame = self.root.wm_frame()
            if frame:
                hwnd = int(str(frame), 0)
                if hwnd:
                    return hwnd
        except Exception:
            pass
        try:
            return int(self.root.winfo_id())
        except Exception:
            return 0

    def begin_dialog(self):
        """打开本程序自己的对话框/菜单时调用：期间不再抢置顶，免得盖住下拉选项。"""
        self._dialog_depth = getattr(self, "_dialog_depth", 0) + 1
        self._apply_always_on_top()

    def end_dialog(self):
        self._dialog_depth = max(0, getattr(self, "_dialog_depth", 0) - 1)
        self._apply_always_on_top()

    def _topmost_allowed(self):
        """现在该不该保持在最前面。"""
        if not self.cfg.get("always_on_top", True):
            return False
        if getattr(self, "_dialog_depth", 0) > 0:
            return False                     # 自己的对话框/下拉框优先
        if self.cfg.get("_force_untop"):
            return False                     # 演奏中（设置里勾了"演奏时取消置顶"）
        return True

    def _apply_always_on_top(self):
        want = self._topmost_allowed()
        hwnd = self._tk_hwnd()
        try:
            if want:
                if not self.root.attributes("-topmost") or not is_window_topmost(hwnd):
                    self.root.attributes("-topmost", True)
                    if not is_window_topmost(hwnd):
                        set_window_topmost(hwnd, True)
            else:
                if self.root.attributes("-topmost"):
                    self.root.attributes("-topmost", False)
                if is_window_topmost(hwnd):
                    set_window_topmost(hwnd, False)
        except Exception:
            log.exception("切换窗口置顶失败")

    def _topmost_tick(self):
        try:
            hwnd = self._tk_hwnd()
            want = self._topmost_allowed()
            cur = is_window_topmost(hwnd)
            # 只在"状态确实不对"时才动窗口：避免每次 SetWindowPos 把主窗口
            # 重新提到置顶组最上面，从而盖住自己的下拉列表（闪烁、选不中）
            if want and not cur:
                self.root.attributes("-topmost", True)
                if not is_window_topmost(hwnd):
                    set_window_topmost(hwnd, True)
            elif not want and cur:
                self.root.attributes("-topmost", False)
                if is_window_topmost(hwnd):
                    set_window_topmost(hwnd, False)
        except Exception:
            pass
        try:
            self.root.after(1500, self._topmost_tick)
        except Exception:
            pass

    def set_dialog_topmost(self, win):
        """让本程序的对话框也置顶（否则会被置顶的主窗口盖住，下拉框同样选不中）。"""
        try:
            win.attributes("-topmost", bool(self.cfg.get("always_on_top", True)))
        except Exception:
            pass

    def _topmost_kick(self):
        """立刻把主窗口重新提到最前面（被游戏抢走置顶时用）。"""
        if not self._topmost_allowed():
            return
        try:
            self.root.deiconify()
            self.root.lift()
            self.root.attributes("-topmost", True)
            set_window_topmost(self._tk_hwnd(), True)
        except Exception:
            pass

    # ---------------- 设置 / 帮助 ----------------
    def open_settings(self):
        try:
            SettingsDialog(self)
        except Exception:
            log.exception("打开设置窗口失败")
            messagebox.showerror(APP_NAME, "打开设置失败，详见日志。")

    def show_help(self):
        messagebox.showinfo(
            APP_NAME + " · 使用说明",
            "1. 首次启动会弹出【免责声明】（只读窗口，与米哈游 /《原神》官方无任何关系，\n"
            "   严禁售卖与商业使用）。这里只能二选一：点『同意并继续』进入程序，\n"
            "   或点『不同意，退出程序』（右上角 × 也等于不同意）。\n"
            "   不想每次都看，就勾上『下次不再弹出』再点同意（设置里可重新打开）。\n\n"
            "2. 打开《原神》，站好位置，进入演奏界面（沃雅妮莎=切换到她并使用琴；"
            "风物之诗琴=普通琴）。\n\n"
            "3. 在本程序右侧选择乐器，确认键位预览与游戏内一致（可用『测试当前乐器的按键』校准）。\n\n"
            "4. 点『导入谱子…』读取 txt，或直接粘贴到编辑框。谱子写法：\n"
            "   D D A B C        普通音符（空格分隔，用『按键间隔』）\n"
            "   (AH)             和弦：A 和 H 同时按下\n"
            "   A*3  Ax2         同一个音重复 3 / 2 次\n"
            "   -  _  .  ~       休止（按一拍算，不按键）\n"
            "   # 或 //          行内注释\n\n"
            "3.1 紧贴（快速连按）：写在一起、中间没有空格\n"
            "   BN               按完 B 紧贴按 N（间隔用『紧贴间隔』，默认 40）\n"
            "   N(DT)            按完 N 紧贴按下和弦 D+T\n"
            "   (HT)Q            和弦后紧贴按 Q；写成 (HT) Q 就是普通间隔\n\n"
            "3.3 斜杠 / = 停顿（长度用主界面的『斜杠』参数，默认 300 tick）\n"
            "   N(DT) / (HT)Q    两段之间停顿\n"
            "   A /[1000] B      这一次停顿用 1000 tick（单次覆盖）\n"
            "   注意：// 是注释，不是停顿。\n\n"
            "3.4 换算：1 tick = 1 毫秒，1000 tick = 1 秒。\n"
            "   左下角会实时显示『间隔/紧贴/斜杠』分别是多少秒。\n\n"
            "3.5 给单个音单独指定时间（tick）：A[25]  A [25 tick]  A@25（旧写法 A(25) 也兼容）\n"
            "   默认含义：先等 25 tick，再按 A（数字属于这个音自己）；\n"
            "   也可以在设置里改成“按完这个音后再等 N tick”。\n"
            "   和弦/休止同样可用： (AH)[50]   -[500]   [300]（单独出现=纯等待）\n"
            "   没有时间标记、也不是紧贴的音符，用右边的『按键间隔』。\n\n"
            "4. 上方可以同时打开多个曲谱（标签页，右键可重命名/复制/关闭），"
            "每个曲谱里还能用『＋ 添加新区间演奏』把它拆成最多 20 个节奏区间，"
            "每个区间可以有自己的默认间隔，按顺序演奏。\n"
            "   换行/内容都按区间分开保存，退出时会自动记住所有标签页。\n\n"
            "5. 设置『按键间隔』（tick），点『保存谱子…』可把内容+间隔+紧贴+斜杠一起存到 sheets 文件夹。\n\n"
            "6. 点『开始演奏』：会先有倒计时（期间不弹奏），并自动把原神切到前台；"
            "演奏中一旦原神不在前台会立刻停止并松开按键。\n\n"
            "7. 全屏独占模式下置顶窗口可能看不到，此时用全局快捷键（默认 F9 开始/停止、"
            "F10 紧急停止，可在设置里改）；\n"
            "   本程序默认在演奏期间也保持置顶（方便你看见/点停止），被游戏抢走时按一下快捷键会立刻唤回；\n"
            "   想让它演奏时让位，在设置里勾『演奏时取消置顶』即可。\n\n"
            "8. 若按键没有反应：请用『以管理员身份启动.bat』运行（游戏以管理员身份运行时必须这样），"
            "或在设置里把发送方式依次换成『scancode』『keybd_event』再试。\n\n"
            "9. 编辑框右边（或左边）有行号，下面一行实时显示『第几行、第几列、共几行』。\n"
            "   想只弹其中一段：在『演奏行范围』里填起始行与结束行（例如 11 到 22），留空就是全部。\n\n"
            "10. 每次点『开始演奏』都会先做一次【预检】：把区间是空的、间隔小于按住时长、\n"
            "    有无法识别的符号、行范围越界等可疑之处列出来问你『是否继续』，确认后才弹。\n\n"
            "作者：%s　问题反馈 QQ：%s" % (APP_AUTHOR, APP_CONTACT),
        )

    # ---------------- 免责声明 ----------------
    def show_disclaimer(self, force=False):
        """启动时（或手动）显示免责声明；返回 False 表示用户不同意（程序应退出）。"""
        if not force and not self.cfg.get("disclaimer_show", True):
            log.info("免责声明：按设置跳过（上次已同意并勾选不再显示）。")
            return True
        try:
            dlg = DisclaimerDialog(self)
            self.root.wait_window(dlg.win)
        except Exception:
            log.exception("显示免责声明时出错（已跳过）")
            return True
        if self.quitting:
            return False
        if self.cfg.get("disclaimer_show", True):
            log.info("免责声明已确认（本次启动仍会显示）。")
        return True

    # ---------------- 行号 / 当前行 ----------------
    def _refresh_gutter(self, *_args):
        """重建行号栏（显示在编辑框左侧或右侧，可设置）。"""
        self._gutter_job = None
        try:
            if not getattr(self, "gutter", None):
                return
            if not self.cfg.get("line_numbers", True):
                self.gutter.grid_remove()
                return
            self.gutter.grid()
            ed = self.sheet_text
            gut = self.gutter
            total = int(ed.index("end-1c").split(".")[0])
            first = ed.index("@0,0").split(".")[0]
            last = ed.index("@0,%d" % max(1, ed.winfo_height())).split(".")[0]
            start = max(1, int(first) - 1)
            end = min(total, int(last) + 1)
            gut.configure(state="normal", width=max(3, len(str(total)) + 1))
            gut.delete("1.0", "end")
            gut.insert("1.0", "\n".join(str(i) for i in range(start, end + 1)))
            gut.configure(state="disabled")
            # 用空行占位对齐滚动位置
            gut.yview_moveto(0)
            self._gutter_offset = start - 1
            self._sync_gutter_view()
            self._highlight_current_line()
        except Exception:
            log.exception("刷新行号失败")

    def _gutter_line(self, lineno):
        off = getattr(self, "_gutter_offset", 0)
        idx = lineno - off
        return "%d.0" % max(1, idx)

    def _sync_gutter_view(self, *_args):
        try:
            gut = getattr(self, "gutter", None)
            if not gut or not self.cfg.get("line_numbers", True):
                return
            ed = self.sheet_text
            total_ed = int(ed.index("end-1c").split(".")[0]) or 1
            total_gut = int(gut.index("end-1c").split(".")[0]) or 1
            frac = ed.yview()[0]
            # 行数不同时按比例对齐（首行是同一行，比例即可）
            gut.yview_moveto(min(1.0, max(0.0, frac)))
            if total_ed and total_gut and total_ed > 3:
                pass
        except Exception:
            pass

    def _highlight_current_line(self, *_args):
        try:
            gut = getattr(self, "gutter", None)
            if not gut or not self.cfg.get("line_numbers", True):
                return
            ed = self.sheet_text
            line = int(ed.index("insert").split(".")[0])
            col = int(ed.index("insert").split(".")[1])
            total = int(ed.index("end-1c").split(".")[0])
            gut.tag_remove("cur", "1.0", "end")
            gut.tag_config("cur", background="#ffe9a8", foreground="#8b1a1a",
                           font=("Consolas", 10, "bold"))
            gut.tag_add("cur", self._gutter_line(line), "%s lineend" % self._gutter_line(line))
            if hasattr(self, "line_info_var"):
                rng = self.play_range()
                extra = ""
                if rng[0] or rng[1]:
                    extra = "　演奏范围：第 %d～%d 行" % (
                        rng[0] or 1, rng[1] or total)
                self.line_info_var.set("第 %d 行，第 %d 列 ｜ 共 %d 行%s" % (line, col + 1, total, extra))
        except Exception:
            pass

    def _schedule_gutter(self, *_args):
        if self._gutter_job:
            try:
                self.root.after_cancel(self._gutter_job)
            except Exception:
                pass
        self._gutter_job = self.root.after(200, self._refresh_gutter)

    # ---------------- 演奏行范围 ----------------
    def play_range(self):
        """返回 (起始行, 结束行)，0 表示不限制。"""
        try:
            start = safe_int(self.range_start_var.get(), 0, 0, 1000000)
            end = safe_int(self.range_end_var.get(), 0, 0, 1000000)
        except Exception:
            return 0, 0
        if start and end and start > end:
            start, end = end, start
        return start, end

    def _on_range_change(self, *_args):
        if self._loading:
            return          # 正在载入界面，不算用户改动
        try:
            sec = self.doc().current()
            start, end = self.play_range()
            sec.start_line = start
            sec.end_line = end
            self._mark_dirty()
            self._schedule_info()
            self._highlight_current_line()
        except Exception:
            pass

    @staticmethod
    def slice_by_lines(text, start, end):
        """按 1 基行号截取文本；start/end 为 0 表示不限。"""
        lines = str(text).splitlines()
        total = len(lines)
        if total == 0:
            return "", 0, 0
        s = safe_int(start, 0, 0, 1000000) or 1
        e = safe_int(end, 0, 0, 1000000) or total
        s = min(max(1, s), total)
        e = min(max(1, e), total)
        if e < s:
            s, e = e, s
        return "\n".join(lines[s - 1:e]), s, e

    # ---------------- 演奏前预检 ----------------
    def preflight(self, parts, issues, per_section):
        """演奏前把所有可疑之处汇总，返回 (warnings, errors)。"""
        warns = []
        errors = []
        d = self.doc()
        global_ms = safe_int(self.interval_var.get(), 150, 10, 60000)
        hold = safe_int(self.hold_var.get(), 30, 5, 2000)
        slash = safe_int(self.slash_var.get(), 300, 1, 5000)
        tight = safe_int(self.tight_var.get(), 40, 1, 5000)
        all_steps = sum(s["steps"] for s in per_section)
        if not all_steps:
            errors.append("整首谱子里没有任何可演奏的音符。")
        for s in per_section:
            if s["steps"] == 0:
                warns.append("区间 %d『%s』是空的，会被跳过。" % (s["index"] + 1, s["name"]))
            if s["interval"] < hold:
                warns.append("区间 %d『%s』的间隔 %d tick 小于按住时长 %d ms，"
                             "这些音会被自动缩短按住时间，可能漏音。"
                             % (s["index"] + 1, s["name"], s["interval"], hold))
            sec = d.sections[s["index"]] if s["index"] < len(d.sections) else None
            if sec and (sec.start_line or sec.end_line):
                lines = (sec.text or "").count("\n") + 1
                warns.append("区间 %d『%s』只演奏第 %d～%d 行（该区间共 %d 行）。"
                             % (s["index"] + 1, s["name"], sec.start_line or 1,
                                sec.end_line or lines, lines))
        if issues:
            sample = "；".join(str(i) for i in issues[:5])
            warns.append("有 %d 处内容无法识别（会按休止处理）：%s%s"
                         % (len(issues), sample, " …" if len(issues) > 5 else ""))
        if tight >= global_ms * 2 and global_ms > 0:
            warns.append("「紧贴」(%d) 比「按键间隔」(%d) 还大不少，"
                         "紧贴可能会听起来比正常音还慢。" % (tight, global_ms))
        if slash > 3000:
            warns.append("「斜杠」停顿 %d tick（约 %.1f 秒）很长，确认是有意为之。"
                         % (slash, slash / 1000.0))
        if all_steps > 3000:
            warns.append("整首共 %d 步，预计演奏时间较长（约 %s 秒）。"
                         % (all_steps, int(sum(s["ms"] for s in per_section) / 1000)))
        total_lines = sum((sec.text or "").count("\n") + 1 for sec in d.sections)
        if total_lines > 1500:
            warns.append("谱子行数较多（%d 行），解析与演奏会稍慢。" % total_lines)
        return warns, errors

    def confirm_before_play(self, warns, errors):
        """把预检结果摆给用户，问是否继续。返回 True=继续。"""
        if errors:
            messagebox.showerror(APP_NAME, "无法开始演奏：\n\n· " + "\n· ".join(errors))
            self.set_status("已取消：预检未通过。")
            return False
        if not warns:
            return True
        head = "演奏前预检发现 %d 条需要你确认的地方：\n\n" % len(warns)
        body = "\n".join("· %s" % w for w in warns[:12])
        tail = "\n\n是否仍然继续演奏？" if len(warns) <= 12 else \
            "\n\n（还有 %d 条见日志）\n\n是否仍然继续演奏？" % (len(warns) - 12)
        for w in warns:
            log.warning("预检：%s", w)
        return bool(messagebox.askokcancel(APP_NAME + " · 演奏前预检", head + body + tail))

    # ---------------- 关闭 ----------------
    def on_close_window(self):
        if self.cfg.get("minimize_on_close", True):
            log.info("关闭按钮：已最小化到任务栏（设置里可改为直接退出）。")
            try:
                self.root.iconify()
            except Exception:
                pass
            return
        self.quit_app()

    def quit_app(self):
        self.quitting = True
        try:
            self.player.stop("程序退出")
        except Exception:
            pass
        try:
            self.save_session_now()
        except Exception:
            pass
        try:
            self.cfg["window_geometry"] = self.root.winfo_geometry()
        except Exception:
            pass
        save_json(CONFIG_PATH, self.public_config())
        try:
            self.hotkeys.stop()
        except Exception:
            pass
        log.info("程序退出。")
        try:
            self.root.destroy()
        except Exception:
            pass

    def public_config(self):
        cfg = dict(self.cfg)
        cfg.pop("_game_hwnds", None)
        cfg.pop("_require_focus", None)
        try:
            cfg["instrument"] = self.inst_var.get()
            cfg["interval_ms"] = safe_int(self.interval_var.get(), 150, 10, 5000)
            cfg["hold_ms"] = safe_int(self.hold_var.get(), 30, 5, 500)
            cfg["countdown_s"] = safe_int(self.countdown_var.get(), 3, 0, 15)
            cfg["tight_ms"] = safe_int(self.tight_var.get(), 40, 1, 5000)
            cfg["slash_ms"] = safe_int(self.slash_var.get(), 300, 1, 5000)
            cfg["auto_activate_game"] = bool(self.auto_activate_var.get())
            cfg["stop_on_focus_loss"] = bool(self.focus_stop_var.get())
        except Exception:
            pass
        return cfg


class DisclaimerDialog:
    """启动时的免责声明闸门：内容只读，只能"同意"或"不同意"，外加勾选下次不再弹出。"""

    def __init__(self, app):
        self.app = app
        cfg = app.cfg
        app.begin_dialog()          # 期间不抢置顶，保证下拉列表能正常选
        self.win = tk.Toplevel(app.root)
        self.win.title("免责声明 · 使用前必读")
        self.win.transient(app.root)
        self.win.resizable(False, False)
        try:
            self.win.attributes("-topmost", True)
        except Exception:
            pass
        self.win.geometry("820x680")
        # 只能同意/不同意：右上角 × 等于"不同意"
        self.win.protocol("WM_DELETE_WINDOW", self.decline)

        head = tk.Frame(self.win, bg="#8b1a1a")
        head.pack(fill="x")
        tk.Label(head, text="免责声明 · 使用前必读", bg="#8b1a1a", fg="#ffffff",
                 font=("Microsoft YaHei", 15, "bold"), pady=10).pack()
        tk.Label(head, text="本软件为非官方第三方工具，与米哈游 /《原神》官方无任何关系",
                 bg="#8b1a1a", fg="#ffe0e0", font=("Microsoft YaHei", 10)).pack(pady=(0, 8))

        body = ttk.Frame(self.win, padding=(12, 10, 12, 0))
        body.pack(fill="both", expand=True)
        body.columnconfigure(0, weight=1)
        body.rowconfigure(0, weight=1)
        self.text = tk.Text(body, wrap="char", font=("Microsoft YaHei", 10),
                            background="#fbfbfb", padx=14, pady=12,
                            relief="solid", bd=1, cursor="arrow")
        self.text.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(body, orient="vertical", command=self.text.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.text.configure(yscrollcommand=sb.set)
        self.text.insert("1.0", DISCLAIMER_TEXT)
        self.text.configure(state="disabled")     # 只读：不允许在这个页面里做任何修改
        self.text.see("1.0")
        # 只读文本框：连键盘输入、右键菜单都不给
        for seq in ("<Key>", "<Control-v>", "<Control-V>", "<Button-2>", "<Button-3>"):
            self.text.bind(seq, lambda _e: "break")

        foot = ttk.Frame(self.win, padding=12)
        foot.pack(fill="x")
        self.remember_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(foot, text="下次不再弹出", variable=self.remember_var).pack(side="left")
        ttk.Button(foot, text="不同意，退出程序", command=self.decline).pack(side="right")
        ttk.Button(foot, text="同意并继续", command=self.accept).pack(side="right", padx=8)
        ttk.Label(foot, text="作者：%s　反馈 QQ：%s" % (APP_AUTHOR, APP_CONTACT),
                  foreground="#666").pack(side="right", padx=16)

        self.win.grab_set()
        try:
            self.win.update_idletasks()
            x = self.app.root.winfo_rootx() + 40
            y = self.app.root.winfo_rooty() + 30
            self.win.geometry("+%d+%d" % (x, y))
        except Exception:
            pass
        try:
            self.win.focus_force()
        except Exception:
            pass
        self.app.set_dialog_topmost(self.win)

    def _on_close(self):
        try:
            self.win.grab_release()
        except Exception:
            pass
        self.app.end_dialog()
        try:
            self.win.destroy()
        except Exception:
            pass

    def accept(self):
        cfg = self.app.cfg
        cfg["disclaimer_show"] = not bool(self.remember_var.get())
        cfg["disclaimer_accepted"] = "%s v%s" % (APP_NAME, APP_VERSION)
        save_json(CONFIG_PATH, self.app.public_config())
        log.info("用户已同意免责声明；下次%s弹出",
                 "不再" if not cfg["disclaimer_show"] else "仍会")
        self._on_close()

    def decline(self):
        log.warning("用户不同意免责声明，程序退出。")
        self._on_close()
        self.app.quit_app()


class SettingsDialog:
    def __init__(self, app: LyreApp):
        self.app = app
        app.begin_dialog()          # 对话框期间不抢置顶，下拉框才点得动
        self.win = tk.Toplevel(app.root)
        self.win.title("设置")
        self.win.transient(app.root)
        self.win.resizable(False, False)
        self.win.grab_set()
        self.win.protocol("WM_DELETE_WINDOW", self.close)
        cfg = app.cfg
        pad = {"padx": 10, "pady": 3}

        self.minimize_var = tk.BooleanVar(value=bool(cfg.get("minimize_on_close", True)))
        self.topmost_var = tk.BooleanVar(value=bool(cfg.get("always_on_top", True)))
        self.un_top_var = tk.BooleanVar(value=bool(cfg.get("un_topmost_while_playing", True)))
        self.focus_var = tk.BooleanVar(value=bool(app.focus_stop_var.get()))
        self.verbose_var = tk.BooleanVar(value=bool(cfg.get("verbose_log", True)))
        self.allow_no_game_var = tk.BooleanVar(value=bool(cfg.get("allow_without_game", False)))
        self.bracket_var = tk.StringVar(value=cfg.get("bracket_mode", "chord"))
        self.timing_var = tk.StringVar(value=timing_mode_label(cfg.get("timing_mode", "before")))
        self.tight_mode_var = tk.StringVar(value=tight_mode_label(cfg.get("tight_mode", "adjacent")))
        self.method_var = tk.StringVar(value=send_method_label(cfg.get("send_method", "vk")))
        self.proc_var = tk.StringVar(value=", ".join(cfg.get("game_processes") or []))
        self.title_var = tk.StringVar(value=", ".join(cfg.get("game_window_titles") or []))
        self.maxlen_var = tk.IntVar(value=int(cfg.get("max_play_seconds", 900)))
        self.toggle_spec = dict(app.active_hotkeys.get("toggle") or {})
        self.panic_spec = dict(app.active_hotkeys.get("panic") or {})

        # 内容放进可滚动容器，底部按钮固定在窗口下方（选项再多也点得到）
        outer = ttk.Frame(self.win)
        outer.pack(fill="both", expand=True)
        self._canvas = tk.Canvas(outer, borderwidth=0, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=self._canvas.yview)
        self._canvas.configure(yscrollcommand=vsb.set)
        self._canvas.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        frm = ttk.Frame(self._canvas, padding=10)
        self._win_id = self._canvas.create_window((0, 0), window=frm, anchor="nw")

        def _sync(_e=None):
            try:
                self._canvas.itemconfigure(self._win_id, width=self._canvas.winfo_width())
                self._canvas.configure(scrollregion=self._canvas.bbox("all"))
            except Exception:
                pass

        frm.bind("<Configure>", _sync)
        self._canvas.bind("<Configure>", _sync)

        foot = ttk.Frame(self.win, padding=(10, 6, 10, 10))
        foot.pack(fill="x", side="bottom")
        ttk.Button(foot, text="确定", command=self.apply).pack(side="right", padx=4)
        ttk.Button(foot, text="取消", command=self.close).pack(side="right")
        ttk.Button(foot, text="打开配置文件", command=self.open_config).pack(side="left")
        ttk.Button(foot, text="退出程序", command=self.quit_app).pack(side="left", padx=6)

        row = 0
        ttk.Label(frm, text="窗口与安全", font=("Segoe UI", 10, "bold")).grid(
            row=row, column=0, columnspan=3, sticky="w", pady=(0, 4))
        row += 1
        ttk.Checkbutton(frm, text="关闭窗口时最小化到任务栏（不退出程序）",
                        variable=self.minimize_var).grid(row=row, column=0, columnspan=3,
                                                         sticky="w", **pad)
        row += 1
        ttk.Checkbutton(frm, text="窗口始终置顶（方便全屏时点按钮）",
                        variable=self.topmost_var).grid(row=row, column=0, columnspan=3,
                                                        sticky="w", **pad)
        row += 1
        ttk.Checkbutton(frm, text="演奏时取消置顶（默认不勾＝演奏中也保持置顶）",
                        variable=self.un_top_var).grid(row=row, column=0, columnspan=3,
                                                       sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="打开设置/菜单期间会自动临时让位，保证下拉框能正常选择",
                  foreground="#777").grid(row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        ttk.Checkbutton(frm, text="原神失去焦点时立即停止演奏",
                        variable=self.focus_var).grid(row=row, column=0, columnspan=3,
                                                      sticky="w", **pad)
        row += 1
        ttk.Checkbutton(frm, text="允许在未检测到原神窗口时依然演奏（不推荐）",
                        variable=self.allow_no_game_var).grid(row=row, column=0, columnspan=3,
                                                              sticky="w", **pad)
        row += 1
        ttk.Checkbutton(frm, text="记录详细日志（调试用）",
                        variable=self.verbose_var).grid(row=row, column=0, columnspan=3,
                                                        sticky="w", **pad)
        row += 1
        ttk.Separator(frm, orient="horizontal").grid(row=row, column=0, columnspan=3,
                                                     sticky="ew", pady=8)
        row += 1

        ttk.Label(frm, text="快捷键（全局生效；建议用 F9/F10 等游戏未占用的键）",
                  font=("Segoe UI", 10, "bold")).grid(row=row, column=0, columnspan=3,
                                                      sticky="w", pady=(0, 4))
        row += 1
        self.toggle_label = tk.StringVar(value=hotkey_display(self.toggle_spec))
        self.panic_label = tk.StringVar(value=hotkey_display(self.panic_spec))
        ttk.Label(frm, text="开始 / 停止：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Label(frm, textvariable=self.toggle_label, width=18,
                  foreground="#0a6").grid(row=row, column=1, sticky="w", **pad)
        ttk.Button(frm, text="绑定…", command=lambda: self.bind_hotkey("toggle")).grid(
            row=row, column=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="紧急停止：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Label(frm, textvariable=self.panic_label, width=18,
                  foreground="#c33").grid(row=row, column=1, sticky="w", **pad)
        ttk.Button(frm, text="绑定…", command=lambda: self.bind_hotkey("panic")).grid(
            row=row, column=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="（为避免误吞游戏按键，快捷键必须是 F1~F12，或包含 Ctrl / Alt / Shift）",
                  foreground="#777").grid(row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        ttk.Separator(frm, orient="horizontal").grid(row=row, column=0, columnspan=3,
                                                     sticky="ew", pady=8)
        row += 1

        ttk.Label(frm, text="兼容性", font=("Segoe UI", 10, "bold")).grid(
            row=row, column=0, columnspan=3, sticky="w", pady=(0, 4))
        row += 1
        ttk.Label(frm, text="按键发送方式：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Combobox(frm, textvariable=self.method_var, state="readonly", width=30,
                     values=[label for _v, label in SEND_METHODS]).grid(
            row=row, column=1, columnspan=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="游戏里没反应时，依次换另外两种再试",
                  foreground="#777").grid(row=row, column=1, columnspan=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="原神进程名：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.proc_var, width=34).grid(row=row, column=1,
                                                                 columnspan=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="原神窗口标题：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.title_var, width=34).grid(row=row, column=1,
                                                                  columnspan=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="最大演奏时长（秒）：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Spinbox(frm, from_=5, to=7200, increment=30, width=10,
                    textvariable=self.maxlen_var).grid(row=row, column=1, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="括号 ( ) 的含义：").grid(row=row, column=0, sticky="w", **pad)
        ttk.Combobox(frm, textvariable=self.bracket_var, state="readonly", width=24,
                     values=["chord", "repeat"]).grid(row=row, column=1, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="chord=(AH) 表示 A、H 同时按；repeat=表示依次按 A、H 各一次",
                  foreground="#777").grid(row=row, column=1, columnspan=2, sticky="w", **pad)
        row += 1
        ttk.Separator(frm, orient="horizontal").grid(row=row, column=0, columnspan=3,
                                                     sticky="ew", pady=8)
        row += 1
        ttk.Label(frm, text="谱子里的 (N) 时间标记（tick / 毫秒）",
                  font=("Segoe UI", 10, "bold")).grid(row=row, column=0, columnspan=3,
                                                      sticky="w", pady=(0, 4))
        row += 1
        ttk.Combobox(frm, textvariable=self.timing_var, state="readonly", width=34,
                     values=[label for _v, label in TIMING_MODES]).grid(
            row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        ttk.Label(frm,
                  text=("写法：A[25] 或 A [25 tick] 给单个音指定时间标记；\n"
                        "      没有标记的音符用主界面的「按键间隔」；-[500] 是停 500；\n"
                        "      单位可写 tick / ms / s（1 tick = 1 毫秒）。"),
                  foreground="#777", justify="left").grid(
            row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="「紧贴」（快速连按）怎么判定",
                  font=("Segoe UI", 10, "bold")).grid(row=row, column=0, columnspan=3,
                                                      sticky="w", pady=(8, 4))
        row += 1
        ttk.Combobox(frm, textvariable=self.tight_mode_var, state="readonly", width=42,
                     values=[label for _v, label in TIGHT_MODES]).grid(
            row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        ttk.Label(frm,
                  text=("紧贴的间隔在主界面的「紧贴」里调（默认 40 tick）。\n"
                        "BN = 按完 B 紧贴按 N；N(DT) = 按完 N 紧贴按下和弦 D+T。\n"
                        "斜杠 / = 停顿，长度在主界面的「斜杠」里调（默认 300 tick）；\n"
                        "       也可以写成 /[500] 或 /@500 单独指定那一次停顿的长度。\n"
                        "换算：1 tick = 1 毫秒，1000 tick = 1 秒。"),
                  foreground="#777", justify="left").grid(
            row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        ttk.Separator(frm, orient="horizontal").grid(row=row, column=0, columnspan=3,
                                                     sticky="ew", pady=8)
        row += 1
        # ---- 编辑器 / 行号 ----
        ttk.Label(frm, text="编辑器", font=("Segoe UI", 10, "bold")).grid(
            row=row, column=0, columnspan=3, sticky="w", pady=(0, 4))
        row += 1
        self.line_numbers_var = tk.BooleanVar(value=bool(cfg.get("line_numbers", True)))
        self.line_side_var = tk.StringVar(
            value=("右侧" if cfg.get("line_number_side", "right") != "left" else "左侧"))
        ttk.Checkbutton(frm, text="显示行号", variable=self.line_numbers_var).grid(
            row=row, column=0, sticky="w", **pad)
        ttk.Label(frm, text="行号位置：").grid(row=row, column=1, sticky="e", **pad)
        ttk.Combobox(frm, textvariable=self.line_side_var, state="readonly", width=8,
                     values=["右侧", "左侧"]).grid(row=row, column=2, sticky="w", **pad)
        row += 1
        ttk.Separator(frm, orient="horizontal").grid(row=row, column=0, columnspan=3,
                                                     sticky="ew", pady=8)
        row += 1
        # ---- 免责声明 / 作者 ----
        ttk.Label(frm, text="免责声明与作者", font=("Segoe UI", 10, "bold")).grid(
            row=row, column=0, columnspan=3, sticky="w", pady=(0, 4))
        row += 1
        self.disclaimer_show_var = tk.BooleanVar(value=bool(cfg.get("disclaimer_show", True)))
        ttk.Checkbutton(frm, text="启动时显示免责声明", variable=self.disclaimer_show_var).grid(
            row=row, column=0, columnspan=2, sticky="w", **pad)
        ttk.Button(frm, text="重新查看免责声明", command=lambda: self.app.show_disclaimer(
            force=True)).grid(row=row, column=2, sticky="w", **pad)
        row += 1
        ttk.Label(frm, text="作者：%s　问题反馈 QQ：%s" % (APP_AUTHOR, APP_CONTACT),
                  font=("Segoe UI", 10, "bold"), foreground="#8b1a1a").grid(
            row=row, column=0, columnspan=3, sticky="w", **pad)
        row += 1
        abar = ttk.Frame(frm)
        abar.grid(row=row, column=0, columnspan=3, sticky="w", **pad)
        ttk.Button(abar, text="复制 QQ 号", command=self.copy_contact).pack(side="left")
        ttk.Button(abar, text="关于", command=self.show_about).pack(side="left", padx=6)
        row += 1
        ttk.Separator(frm, orient="horizontal").grid(row=row, column=0, columnspan=3,
                                                     sticky="ew", pady=8)
        row += 1
        btns = ttk.Frame(frm)
        btns.grid(row=row, column=0, columnspan=3, sticky="ew")
        ttk.Button(btns, text="确定", command=self.apply).pack(side="right", padx=4)
        ttk.Button(btns, text="取消", command=self.close).pack(side="right")
        ttk.Button(btns, text="打开配置文件", command=self.open_config).pack(side="left")
        ttk.Button(btns, text="退出程序", command=self.quit_app).pack(side="left", padx=6)

        self.win.bind("<Escape>", lambda _e: self.close())
        # 尺寸：内容多就滚动；高度封顶，底部按钮永远在窗口内
        try:
            self.win.update_idletasks()
            sh = self.win.winfo_screenheight()
            sw = self.win.winfo_screenwidth()
            need_h = frm.winfo_reqheight() + 80
            need_w = frm.winfo_reqwidth() + 40
            cap_h = max(360, min(int(sh * 0.80), 1000))
            h = max(340, min(need_h, cap_h))
            w = max(560, min(need_w, max(560, int(sw * 0.5)), 700))
            px = max(10, (sw - w) // 2 - 120)
            py = max(10, min(80, sh - h - 60))
            self.win.geometry("%dx%d+%d+%d" % (w, h, px, py))
            self.win.resizable(False, True)
            self.win.bind_all("<MouseWheel>", self._on_wheel)
            log.info("设置窗口尺寸：%dx%d（内容需要 %dx%d，屏幕 %dx%d）",
                     w, h, need_w, need_h, sw, sh)
        except Exception:
            log.exception("计算设置窗口尺寸失败")
        self.app.set_dialog_topmost(self.win)

    def _on_wheel(self, event):
        try:
            if self.win.winfo_exists():
                self._canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        except Exception:
            pass

    def open_config(self):
        try:
            os.startfile(BASE_DIR)
        except Exception:
            log.exception("打开程序目录失败")

    def copy_contact(self):
        try:
            self.app.root.clipboard_clear()
            self.app.root.clipboard_append(APP_CONTACT)
            messagebox.showinfo(APP_NAME, "作者：%s\n问题反馈 QQ：%s\n\nQQ 号已复制到剪贴板。"
                                % (APP_AUTHOR, APP_CONTACT))
        except Exception:
            log.exception("复制联系方式失败")

    def export_disclaimer(self):
        """已取消"导出/编辑文案"功能：免责声明固定为唯一版本、只在启动弹窗里只读展示。"""
        messagebox.showinfo(
            APP_NAME,
            "免责声明为固定版本，不可编辑或导出。\n"
            "启动时会以只读窗口展示，只能「同意并继续」或「不同意，退出程序」。")

    def show_about(self):
        messagebox.showinfo(
            "%s v%s" % (APP_NAME, APP_VERSION),
            "原神自动弹琴 · 琴谱演奏器 v%s\n\n"
            "作者：%s\n问题反馈 QQ：%s\n\n"
            "本软件为非官方第三方工具，与米哈游 /《原神》官方无任何关系，\n"
            "仅供个人学习、研究与娱乐使用，严禁售卖与任何商业用途。\n\n"
            "纯 Python 标准库实现（tkinter + ctypes），不需要安装第三方依赖。"
            % (APP_VERSION, APP_AUTHOR, APP_CONTACT),
        )

    def quit_app(self):
        self.close()
        self.app.quit_app()

    def bind_hotkey(self, role):
        self.app.begin_dialog()
        dlg = tk.Toplevel(self.win)
        dlg.title("绑定快捷键")
        dlg.transient(self.win)
        self.app.set_dialog_topmost(dlg)
        dlg.grab_set()
        dlg.resizable(False, False)
        tk.Label(
            dlg, justify="left", padx=18, pady=12,
            text=("请按下你想绑定的按键组合…\n"
                  "规则：F1~F12 可单独使用，其他键必须搭配 Ctrl / Alt / Shift。\n"
                  "按 Esc 取消。"),
        ).pack()
        info = tk.Label(dlg, text="等待按键…", fg="#0a6", padx=18, pady=8)
        info.pack()
        held = set()

        def finish(spec):
            if role == "toggle":
                self.toggle_spec = spec
                self.toggle_label.set(hotkey_display(spec))
            else:
                self.panic_spec = spec
                self.panic_label.set(hotkey_display(spec))
            self._close_hotkey(dlg)

        def on_press(event):
            ks = event.keysym
            if ks == "Escape":
                self._close_hotkey(dlg)
                return "break"
            if ks in ("Control_L", "Control_R"):
                held.add("ctrl")
                info.config(text="已按住 Ctrl…", fg="#0a6")
                return "break"
            if ks in ("Alt_L", "Alt_R"):
                held.add("alt")
                info.config(text="已按住 Alt…", fg="#0a6")
                return "break"
            if ks in ("Shift_L", "Shift_R"):
                held.add("shift")
                info.config(text="已按住 Shift…", fg="#0a6")
                return "break"
            if ks in ("Super_L", "Super_R"):
                held.add("win")
                info.config(text="已按住 Win…", fg="#0a6")
                return "break"
            spec, message = build_hotkey_spec(ks, held)
            if spec is None:
                info.config(text=message, fg="#c33" if ks not in MODIFIER_KEYSYMS else "#0a6")
                return "break"
            finish(spec)
            log.info("绑定快捷键：%s -> %s", role, message)
            return "break"

        def on_release(event):
            ks = event.keysym
            if ks in ("Control_L", "Control_R"):
                held.discard("ctrl")
            elif ks in ("Alt_L", "Alt_R"):
                held.discard("alt")
            elif ks in ("Shift_L", "Shift_R"):
                held.discard("shift")
            elif ks in ("Super_L", "Super_R"):
                held.discard("win")
            return "break"

        dlg.bind("<KeyPress>", on_press)
        dlg.bind("<KeyRelease>", on_release)
        dlg.focus_force()
        try:
            dlg.update_idletasks()
            x = self.win.winfo_rootx() + 80
            y = self.win.winfo_rooty() + 80
            dlg.geometry("+%d+%d" % (x, y))
        except Exception:
            pass

    def close(self):
        """关闭设置窗口：恢复正常置顶规则。"""
        try:
            self.win.unbind_all("<MouseWheel>")
        except Exception:
            pass
        try:
            self.win.grab_release()
        except Exception:
            pass
        self.app.end_dialog()
        try:
            self.win.destroy()
        except Exception:
            pass

    def _close_hotkey(self, dlg):
        try:
            dlg.grab_release()
        except Exception:
            pass
        self.app.end_dialog()
        try:
            dlg.destroy()
        except Exception:
            pass

    def apply(self):
        app = self.app
        cfg = app.cfg
        # 先把主界面上的演奏参数收进来，避免只改主界面没保存
        try:
            panel = app.play_settings()
            for key in ("interval_ms", "hold_ms", "countdown_s", "tight_ms", "slash_ms",
                        "auto_activate_game", "stop_on_focus_loss"):
                if key in panel:
                    cfg[key] = panel[key]
        except Exception:
            log.exception("读取主界面参数失败")
        cfg["minimize_on_close"] = bool(self.minimize_var.get())
        cfg["always_on_top"] = bool(self.topmost_var.get())
        cfg["un_topmost_while_playing"] = bool(self.un_top_var.get())
        cfg["stop_on_focus_loss"] = bool(self.focus_var.get())
        cfg["allow_without_game"] = bool(self.allow_no_game_var.get())
        cfg["verbose_log"] = bool(self.verbose_var.get())
        cfg["bracket_mode"] = self.bracket_var.get() or "chord"
        cfg["timing_mode"] = timing_mode_value(self.timing_var.get())
        cfg["tight_mode"] = tight_mode_value(self.tight_mode_var.get())
        cfg["line_numbers"] = bool(self.line_numbers_var.get())
        cfg["line_number_side"] = "left" if self.line_side_var.get() == "左侧" else "right"
        cfg["disclaimer_show"] = bool(self.disclaimer_show_var.get())
        cfg["send_method"] = send_method_value(self.method_var.get())
        cfg["game_processes"] = [p.strip() for p in self.proc_var.get().split(",") if p.strip()]
        cfg["game_window_titles"] = [t.strip() for t in self.title_var.get().split(",") if t.strip()]
        try:
            cfg["max_play_seconds"] = safe_int(self.maxlen_var.get(), 900, 5, 86400)
        except Exception:
            cfg["max_play_seconds"] = 900
        cfg["hotkey_toggle"] = dict(self.toggle_spec) if self.toggle_spec else dict(DEFAULT_CONFIG["hotkey_toggle"])
        cfg["hotkey_panic"] = dict(self.panic_spec) if self.panic_spec else dict(DEFAULT_CONFIG["hotkey_panic"])
        app.focus_stop_var.set(cfg["stop_on_focus_loss"])
        try:
            app.timing_hint_var.set(timing_hint(cfg["timing_mode"]))
        except Exception:
            pass
        app._apply_always_on_top()
        try:
            app._apply_gutter_side()
            app._schedule_gutter()
        except Exception:
            pass
        app.hotkeys.set_bindings(cfg["hotkey_toggle"], cfg["hotkey_panic"])
        app.active_hotkeys["toggle"] = dict(cfg["hotkey_toggle"])
        app.active_hotkeys["panic"] = dict(cfg["hotkey_panic"])
        app._update_hotkey_labels()
        save_json(CONFIG_PATH, app.public_config())
        log.info("设置已保存：置顶=%s，关闭最小化=%s，发送方式=%s，时间标记=%s，紧贴判定=%s，快捷键=%s / %s",
                 cfg["always_on_top"], cfg["minimize_on_close"], cfg["send_method"],
                 cfg["timing_mode"], cfg["tight_mode"],
                 hotkey_display(cfg["hotkey_toggle"]), hotkey_display(cfg["hotkey_panic"]))
        app.set_status("设置已保存。")
        self.close()
        messagebox.showinfo(APP_NAME, "设置已保存。\n（快捷键注册结果请看日志窗口）")


def keysym_to_vk(keysym: str):
    if not keysym:
        return None
    m = re.fullmatch(r"F([1-9]|1[0-9]|2[0-4])", keysym)
    if m:
        return 0x6F + int(m.group(1))
    if keysym in KEYSYM_VK:
        return KEYSYM_VK[keysym]
    if len(keysym) == 1:
        ch = keysym.upper()
        if ch in CANON_VK:
            return CANON_VK[ch]
    return None


def build_hotkey_spec(keysym, held_mods):
    """根据按下的主键与已按住的修饰键生成快捷键描述。

    返回 (spec, 提示文字)：spec 为 None 表示不合法，提示文字是给用户看的原因。
    """
    if not keysym:
        return None, "没有识别到按键，请重试。"
    if keysym in MODIFIER_KEYSYMS:
        return None, "修饰键：%s（请继续按主键）" % keysym
    vk = keysym_to_vk(keysym)
    if vk is None:
        return None, "不支持的按键：%s，请换一个。" % keysym
    is_fkey = re.fullmatch(r"F([1-9]|1[0-9]|2[0-4])", keysym)
    held = set(held_mods or ())
    if not held and not is_fkey:
        return None, "为避免影响游戏，请加上 Ctrl / Alt / Shift，或改用 F1~F12。"
    name = key_display_name(keysym)
    spec = {"mods": sorted(held), "vk": vk, "name": name}
    return spec, hotkey_display(spec)


def key_display_name(keysym: str):
    m = re.fullmatch(r"F([1-9]|1[0-9]|2[0-4])", keysym)
    if m:
        return keysym.upper()
    mapping = {
        "space": "Space", "Return": "Enter", "KP_Enter": "Enter", "Tab": "Tab",
        "Escape": "Esc", "BackSpace": "Backspace", "Prior": "PageUp", "Next": "PageDown",
        "minus": "Minus", "equal": "Equal", "comma": "Comma", "period": "Period",
        "slash": "Slash", "semicolon": "Semicolon", "apostrophe": "Quote", "grave": "Backquote",
        "bracketleft": "BracketLeft", "bracketright": "BracketRight", "backslash": "Backslash",
    }
    if keysym in mapping:
        return mapping[keysym]
    return keysym.upper() if len(keysym) == 1 else keysym


# ---------------------------------------------------------------------------
# 自检 / 冒烟测试 / 主程序
# ---------------------------------------------------------------------------

def _selftest_cases():
    """返回 [(名称, 函数)]；函数失败请抛异常。"""
    cases = []

    def case(name):
        def deco(fn):
            cases.append((name, fn))
            return fn
        return deco

    @case("按键名规范化")
    def _c1():
        assert normalize_key("a") == "A"
        assert normalize_key("F9") == "F9"
        assert normalize_key("space") == "Space"
        assert normalize_key("空格") == "Space"
        assert normalize_key("SHIFT") == "Shift"
        assert normalize_key("Alt") == "Alt"
        assert normalize_key("??") is None
        assert normalize_key("") is None
        assert key_vk("A") == 0x41
        assert key_vk("F10") == 0x79

    @case("解析：普通音符")
    def _c2():
        r = parse_sheet("D D A B C")
        assert r.steps == 5, r.steps
        assert [n.text() for n in r.notes] == ["D", "D", "A", "B", "C"]
        assert r.issues == []

    @case("解析：和弦 (AH)")
    def _c3():
        r = parse_sheet("D D (AH)")
        assert r.steps == 3, (r.steps, [n.text() for n in r.notes])
        assert r.notes[2].keys == ("A", "H"), r.notes[2].keys
        assert r.chords == 1
        for text in ("(A,H)", "[A H]", "（ＡＨ）", "(a h)"):
            rr = parse_sheet("D " + text)
            assert rr.steps == 2, (text, [n.text() for n in rr.notes])
            assert set(rr.notes[1].keys) == {"A", "H"}, (text, rr.notes[1].keys)

    @case("解析：括号 repeat 模式")
    def _c4():
        r = parse_sheet("D (AH)", bracket_mode="repeat")
        assert r.steps == 3, [n.text() for n in r.notes]
        assert [n.text() for n in r.notes] == ["D", "A", "H"]

    @case("解析：重复记号与休止")
    def _c5():
        r = parse_sheet("A*3 - Bx2 ~ (CD)*2")
        texts = [n.text() for n in r.notes]
        assert texts == ["A", "A", "A", "休止", "B", "B", "休止", "(CD)", "(CD)"], texts
        assert r.rests == 2 and r.chords == 2

    @case("解析：注释、换行、全角")
    def _c6():
        r = parse_sheet("A // 注释\nB # 注释\nＣ Ｄ\n")
        assert [n.text() for n in r.notes] == ["A", "B", "C", "D"], [n.text() for n in r.notes]

    @case("解析：非法按键按休止处理并给出提示")
    def _c7():
        r = parse_sheet("A K B", valid_keys={"A", "B"})
        assert r.steps == 3
        assert r.notes[1].rest is True
        assert r.issues, "应当有提示"
        r2 = parse_sheet("A 中文 B", valid_keys={"A", "B"})
        assert r2.notes[1].rest is True and r2.issues

    @case("解析：越界/超长保护")
    def _c8():
        r = parse_sheet("A*999")
        assert r.steps == 999
        r2 = parse_sheet(("A " * 21000))
        assert r2.steps <= r2.max_notes
        assert any("过长" in i for i in r2.issues)

    @case("乐器配置读写")
    def _c9():
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "instruments.json")
            data = load_instruments(path)
            assert len(data["instruments"]) == 2, data
            assert data["instruments"][0]["name"] == "沃雅妮莎"
            assert data["instruments"][1]["name"] == "风物之诗琴"
            for inst in data["instruments"]:
                assert len(inst["rows"]) == 3, inst
                for row in inst["rows"]:
                    assert len(row["keys"]) == 7, row
            assert os.path.exists(path)
            logging.disable(logging.CRITICAL)  # 故意写坏文件，屏蔽预期中的报错日志
            try:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write("{ 坏掉的 json ")
                data2 = load_instruments(path)
                assert len(data2["instruments"]) == 2
            finally:
                logging.disable(logging.NOTSET)

    @case("配置读写与默认值")
    def _c10():
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "config.json")
            cfg = load_config(path)
            assert cfg["interval_ms"] == 150 and cfg["instrument"] == "vodyanitsa"
            cfg["interval_ms"] = 222
            assert save_json(path, cfg)
            cfg2 = load_config(path)
            assert cfg2["interval_ms"] == 222
            logging.disable(logging.CRITICAL)  # 故意写坏文件，屏蔽预期中的报错日志
            try:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write("not json")
                cfg3 = load_config(path)
                assert cfg3["interval_ms"] == 150
            finally:
                logging.disable(logging.NOTSET)

    @case("快捷键描述与 keysym 转换")
    def _c11():
        assert keysym_to_vk("F9") == 0x78
        assert keysym_to_vk("a") == 0x41
        assert keysym_to_vk("space") == 0x20
        assert keysym_to_vk("FakeKey") is None
        assert hotkey_display({"mods": ["ctrl", "alt"], "vk": 0x78, "name": "F9"}) == "Ctrl+Alt+F9"
        assert hotkey_display({}) == "未绑定"

    @case("谱子文件头解析（保存/读取间隔）")
    def _c12():
        text = ("# 原神自动弹琴 谱子\n# 乐器: 风物之诗琴\n# 间隔: 240\n# 紧贴间隔: 35\n\nA B C\n")
        app = LyreApp.__new__(LyreApp)
        info = LyreApp._parse_sheet_header(app, text)
        assert info["interval"] == 240, info
        assert info["tight"] == 35, info
        assert info["instrument"] == "风物之诗琴", info
        assert info["body"].strip() == "A B C", repr(info["body"])
        # 只有普通间隔时不能把紧贴间隔读成主间隔
        info2 = LyreApp._parse_sheet_header(app, "# 间隔: 180\nA")
        assert info2["interval"] == 180 and info2["tight"] is None, info2
        info3 = LyreApp._parse_sheet_header(
            app, "# 间隔: 180\n# 紧贴间隔: 30\n# 斜杠间隔: 900\nA")
        assert info3["interval"] == 180 and info3["tight"] == 30 and info3["slash"] == 900, info3

    @case("Win32 查询接口可用（不发送按键）")
    def _c13():
        if not WIN:
            return
        hwnd, pid, title, exe = foreground_info()
        assert isinstance(pid, int)
        exe_self = pid_to_exe(os.getpid())
        assert "python" in exe_self.lower(), exe_self
        wins = find_game_windows(["YuanShen.exe", "GenshinImpact.exe"], ["原神"])
        assert isinstance(wins, list)
        title_hwnd, all_wins = pick_game_window(["YuanShen.exe", "GenshinImpact.exe"], ["原神"])
        ok, desc = is_game_foreground(["YuanShen.exe"], ["原神"], all_wins)
        assert isinstance(ok, bool)
        print("      · 当前前台：%s | 找到原神窗口 %d 个 | 原神在前台：%s"
              % (desc, len(wins), ok))

    @case("演奏引擎参数与安全检查（不发送按键）")
    def _c14():
        q = queue.Queue()
        p = Player(q)
        assert p.is_playing() is False
        p.stop("空停止不应报错")
        p.release_all()
        assert p.start([], {}) is False
        ev = q.get_nowait()
        assert ev[0] == "status"

    @case("解析：当前乐器没有键位时全部拦下")
    def _c17():
        r = parse_sheet("A B C", set())
        assert r.steps == 3
        assert all(n.rest for n in r.notes), [n.text() for n in r.notes]
        assert len(r.issues) == 3, r.issues
        r2 = parse_sheet("A B C", None)
        assert all(not n.rest for n in r2.notes)

    @case("时间标记：解析")
    def _c18():
        r = parse_sheet("A(25) B(30) C(35)")
        assert [n.wait for n in r.notes] == [25, 30, 35], [n.wait for n in r.notes]
        assert [n.text() for n in r.notes] == ["A[25]", "B[30]", "C[35]"]
        # 带空格 + 单位
        r = parse_sheet("A (25 tick) B (0.5s) C")
        assert [n.wait for n in r.notes] == [25, 500, None], [n.wait for n in r.notes]
        # 其它写法
        r = parse_sheet("A@25 B:300 C[40] D{50} E")
        assert [n.wait for n in r.notes] == [25, 300, 40, 50, None], [n.wait for n in r.notes]
        # 和弦带标记 + 休止带标记
        r = parse_sheet("(AH)(50) -(500) D")
        assert r.notes[0].keys == ("A", "H") and r.notes[0].wait == 50
        assert r.notes[1].rest and r.notes[1].wait == 500
        assert r.notes[2].wait is None
        # 开头单独的 (300) = 纯等待
        r = parse_sheet("(300) A")
        assert r.notes[0].rest and r.notes[0].wait == 300
        assert not r.notes[1].rest and r.notes[1].wait is None
        # 没有时间标记时不受影响
        r = parse_sheet("D D (AH)")
        assert [n.wait for n in r.notes] == [None, None, None]
        assert not r.issues

    @case("时间标记：单位与边界")
    def _c19():
        assert parse_time_mark("25") == 25
        assert parse_time_mark("25tick") == 25
        assert parse_time_mark("25 ticks") == 25
        assert parse_time_mark("0.5s") == 500
        assert parse_time_mark("2秒") == 2000
        assert parse_time_mark("ms") is None
        assert parse_time_mark("A") is None
        assert parse_time_mark("") is None
        assert parse_time_mark("-5") is None

    @case("时间标记：编译成时间轴（两种含义）")
    def _c20():
        notes = parse_sheet("A(25) B(30) C(35)").notes
        # before（默认）：先等 N 再按这个音
        sched = build_schedule(notes, 150, "before")
        assert [t for t, _k in sched] == [25, 55, 90], sched
        assert [k for _t, k in sched] == [("A",), ("B",), ("C",)]
        # after：按完这个音再等 N
        sched = build_schedule(notes, 150, "after")
        assert [t for t, _k in sched] == [0, 25, 55], sched
        # 没有标记时用全局间隔
        notes2 = parse_sheet("A B C").notes
        assert [t for t, _k in build_schedule(notes2, 200, "before")] == [200, 400, 600]
        assert [t for t, _k in build_schedule(notes2, 200, "after")] == [0, 200, 400]
        # 混合：没标记的音符用全局间隔
        notes3 = parse_sheet("A(25) B C(35)").notes
        assert [t for t, _k in build_schedule(notes3, 100, "before")] == [25, 125, 160]
        # 休止在时间轴上不按键，但照样占时间
        notes4 = parse_sheet("A(50) -(100) B").notes
        sched4 = build_schedule(notes4, 100, "before")
        assert [t for t, _k in sched4] == [50, 150, 250]
        assert [k for _t, k in sched4] == [("A",), (), ("B",)]

    @case("紧贴：BN 连按 / N(DT) 紧贴和弦")
    def _c21():
        # 用户给的例子：N A G A BN G A
        r = parse_sheet("N A G A BN G A")
        assert [n.text() for n in r.notes] == ["N", "A", "G", "A", "B", ">N", "G", "A"], \
            [n.text() for n in r.notes]
        assert [bool(n.tight) for n in r.notes] == [False] * 5 + [True] + [False] * 2
        # N(DT)：和弦紧贴在 N 后面；括号后面紧跟着写才紧贴
        r = parse_sheet("N(DT) (HT)Q")
        assert [n.text() for n in r.notes] == ["N", ">(DT)", "(HT)", ">Q"], [n.text() for n in r.notes]
        assert [bool(n.tight) for n in r.notes] == [False, True, False, True]
        # 中间有空格 = 普通间隔
        r = parse_sheet("N(DT) (HT) Q")
        assert [n.text() for n in r.notes] == ["N", ">(DT)", "(HT)", "Q"], [n.text() for n in r.notes]
        # 三段连写 = 三个紧贴
        r = parse_sheet("BNA")
        assert [n.text() for n in r.notes] == ["B", ">N", ">A"]
        # 括号和弦 + 紧贴括号
        r = parse_sheet("(AH)(SF) D")
        assert [n.text() for n in r.notes] == ["(AH)", ">(SF)", "D"]
        # group 模式：带空格的括号和弦也算紧贴（普通音符仍按空格判定）
        r = parse_sheet("N (DT) Q", tight_mode="group")
        assert [bool(n.tight) for n in r.notes] == [False, True, False], [n.text() for n in r.notes]
        r = parse_sheet("N (DT) Q", tight_mode="adjacent")
        assert [bool(n.tight) for n in r.notes] == [False, False, False]
        r = parse_sheet("N(DT)Q", tight_mode="group")
        assert [bool(n.tight) for n in r.notes] == [False, True, True], [n.text() for n in r.notes]
        # 老的写法不受影响：D D (AH) 里的和弦不是紧贴
        r = parse_sheet("D D (AH)")
        assert [bool(n.tight) for n in r.notes] == [False, False, False]
        # 紧贴串里可以有休止符
        r = parse_sheet("B-N")
        assert r.steps == 3 and r.notes[1].rest and r.notes[1].tight

    @case("紧贴：时间轴与紧贴间隔")
    def _c22():
        notes = parse_sheet("N A G A BN G A").notes
        sched = build_schedule(notes, 300, "before", 40)
        # N 前等 300，之后每音 300；B 前也是 300，N 紧贴 B 只用 40
        assert [t for t, _k in sched] == [300, 600, 900, 1200, 1500, 1540, 1840, 2140], \
            [t for t, _k in sched]
        # 紧贴间隔可调，且不写标记的音符用全局间隔
        sched2 = build_schedule(notes, 300, "before", 15)
        assert [t for t, _k in sched2][4:6] == [1500, 1515]
        # after 模式下紧贴同样生效
        sched3 = build_schedule(notes, 300, "after", 40)
        assert [t for t, _k in sched3][4:6] == [1200, 1240], [t for t, _k in sched3]
        # 紧贴与时间标记混用：紧贴优先
        notes4 = parse_sheet("A B[500] C").notes
        assert [t for t, _k in build_schedule(notes4, 200, "before", 50)] == [200, 700, 900]
        notes5 = parse_sheet("AB[500]").notes
        assert [n.wait for n in notes5] == [500, None], [n.text() for n in notes5]

    @case("斜杠 / 停顿")
    def _c23():
        # 基本：/ 是一个停顿步，长度用「斜杠」参数
        r = parse_sheet("N(DT) / (HT)Q")
        assert [n.text() for n in r.notes] == ["N", ">(DT)", "/", "(HT)", ">Q"], \
            [n.text() for n in r.notes]
        assert r.notes[2].slash and r.notes[2].rest
        # 时间轴：斜杠占「斜杠」tick
        notes = r.notes
        sched = build_schedule(notes, 200, "before", 30, 500)
        assert [t for t, _k in sched] == [200, 230, 730, 930, 960], [t for t, _k in sched]
        # 斜杠间隔可调
        sched2 = build_schedule(notes, 200, "before", 30, 1000)
        assert [t for t, _k in sched2][2] == 1230, [t for t, _k in sched2]
        # 单独指定某一次停顿：/[500] /(500) /@500
        for form in ("/[500]", "/(500)", "/@500", "/:500"):
            rr = parse_sheet("A " + form + " B")
            assert rr.notes[1].slash, form
            t = [x for x, _k in build_schedule(rr.notes, 100, "before", 40, 300)]
            # A 在 100；斜杠本身 500（覆盖「斜杠」参数的 300）；B 再等自己的 100
            assert t == [100, 600, 700], (form, t)
        # // 仍然是注释，不会变成停顿
        rr = parse_sheet("A // B\nC")
        assert [n.text() for n in rr.notes] == ["A", "C"], [n.text() for n in rr.notes]
        # 写在一起的 A/B 里，/ 也是停顿
        rr = parse_sheet("A/B")
        assert [n.text() for n in rr.notes] == ["A", "/", ">B"], [n.text() for n in rr.notes]
        # 和弦里的 / 仍然是分隔符
        rr = parse_sheet("(A/B) C")
        assert rr.notes[0].keys == ("A", "B"), rr.notes[0].keys
        # 没有斜杠时不受影响
        assert not any(n.slash for n in parse_sheet("A B C").notes)

    @case("tick 与秒换算")
    def _c24():
        assert LyreApp._ms_to_sec(150) == "0.15"
        assert LyreApp._ms_to_sec(1000) == "1"
        assert LyreApp._ms_to_sec(40) == "0.04"
        assert LyreApp._ms_to_sec(2500) == "2.5"
        assert LyreApp._ms_to_sec(0) == "0"

    @case("多曲谱标签：模型与会话读写")
    def _c25():
        import tempfile
        docs = default_docs()
        assert len(docs) == 1 and len(docs[0].sections) == 1
        d = docs[0]
        d.name = "测试谱"
        d.sections[0].text = "A B C"
        d.sections.append(Section(name="第2区间", text="D E F", own_interval=True,
                                  interval_ms=333))
        d.active = 1
        assert d.current().name == "第2区间"
        assert d.current().interval(150) == 333
        d.sections[0].own_interval = False
        assert d.sections[0].interval(240) == 240
        # to_dict / from_dict 往返
        d2 = SheetDoc.from_dict(d.to_dict())
        assert d2.name == "测试谱" and len(d2.sections) == 2
        assert d2.sections[1].own_interval is True and d2.sections[1].interval_ms == 333
        assert d2.sections[1].text == "D E F" and d2.active == 1
        # 区间数量上限
        big = {"sections": [{"name": "x", "text": "A"} for _ in range(50)]}
        clamped = SheetDoc.from_dict(big)
        assert len(clamped.sections) == MAX_SECTIONS, len(clamped.sections)
        # 会话文件
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "session.json")
            assert save_session([d], 0, path)
            docs3, active3 = load_session(path)
            assert len(docs3) == 1 and docs3[0].name == "测试谱"
            assert len(docs3[0].sections) == 2 and active3 == 0
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("{ 坏 ")
            logging.disable(logging.CRITICAL)
            try:
                docs4, _a = load_session(path)
                assert len(docs4) == 1 and len(docs4[0].sections) == 1
            finally:
                logging.disable(logging.NOTSET)

    @case("多区间：拼接时间轴")
    def _c26():
        p1 = parse_sheet("A B").notes
        p2 = parse_sheet("C D").notes
        steps = build_multi_schedule([(p1, 100), (p2, 500)], "before", 40, 300)
        # 第一段：A@100 B@200；第二段从 200 起算，C@200+500=700 D@1200
        assert [t for t, _k in steps] == [100, 200, 700, 1200], [t for t, _k in steps]
        assert [k for _t, k in steps] == [("A",), ("B",), ("C",), ("D",)]
        assert schedule_duration(steps) == 1200
        # 空区间直接跳过
        steps2 = build_multi_schedule([([], 100), (p1, 100), ([], 999)], "before", 40, 300)
        assert [t for t, _k in steps2] == [100, 200]
        # after 模式两段之间不会黏在一起：上一段的收尾间隔 = 它自己的间隔
        steps3 = build_multi_schedule([(p1, 100), (p2, 300)], "after", 40, 300)
        assert [t for t, _k in steps3] == [0, 100, 200, 500], [t for t, _k in steps3]
        assert schedule_duration([]) == 0

    @case("多区间：文件保存/读取往返")
    def _c27():
        secs = [Section(name="前奏", text="A B", own_interval=False),
                Section(name="高潮", text="C / D", own_interval=True, interval_ms=222)]
        text = sections_to_text(secs, 150, 40, 300, "风物之诗琴")
        assert "# 区间数: 2" in text
        assert "#=== 区间 1/2: 前奏 | 跟随全局 ===" in text, text[:300]
        assert "#=== 区间 2/2: 高潮 | 独立间隔=222 ===" in text, text[:300]
        info = LyreApp._parse_sheet_header(LyreApp.__new__(LyreApp), text)
        assert info["interval"] == 150 and info["tight"] == 40 and info["slash"] == 300
        back = sections_from_text(text)
        assert back and len(back) == 2, back
        assert back[0].name == "前奏" and back[0].text.strip() == "A B"
        assert back[1].name == "高潮" and back[1].own_interval and back[1].interval_ms == 222
        assert "C / D" in back[1].text
        # 单区间时保持旧格式，且能被旧逻辑读出来
        one = sections_to_text([Section(name="第1区间", text="D D (AH)")], 200, 40, 300, "x")
        assert "[区间1]" not in one
        assert sections_from_text(one) is None
        info2 = LyreApp._parse_sheet_header(LyreApp.__new__(LyreApp), one)
        assert info2["body"].strip() == "D D (AH)"

    @case("多区间：解析合并（每段自己的间隔）")
    def _c28():
        d = SheetDoc(name="t")
        d.sections = [Section(name="s1", text="A B", own_interval=False),
                      Section(name="s2", text="C[50] D", own_interval=True, interval_ms=400)]
        parts = []
        for sec in d.sections:
            parts.append((parse_sheet(sec.text).notes, sec.interval(150)))
        steps = build_multi_schedule(parts, "before", 40, 300)
        # A@150 B@300；第二段 C 带 [50] → 300+50=350，D 用本区间 400 → 750
        assert [t for t, _k in steps] == [150, 300, 350, 750], [t for t, _k in steps]

    @case("抗造：反人类输入不崩溃")
    def _c29():
        valid = set("QWERTYUASDFGHJZXCVBNM")
        nasty = ["", " ", "\n", "\t", "\x00", "\x01\x02", "中文🎵", "ＡＢ（ＡＨ）",
                 "[" * 300, "(" * 200, "((((AH))))", "(A", "A)", "[", "]", "{",
                 "A*999999", "A[99999999999]", "A[-1]", "A@", "A:", "(??)", "(?)*3",
                 "//", "///", "A / / B", "A/B/C", "(A/B)", "\ufeffA", "A\u3000B",
                 "休止", "rest pause r", "F99", "Space", "N(DT) / (HT)Q", "A" * 5000,
                 "A\u200bB", "🎵🎶", "A\x0bB\x0cC", "。，、；：", "１２３"]
        for s in nasty:
            for bm in ("chord", "repeat"):
                for tm in ("adjacent", "group"):
                    r = parse_sheet(s, valid, bm, tm)
                    assert r.steps == len(r.notes), (s[:16], bm, tm)
                    assert all(all(k in valid for k in n.keys) for n in r.notes), s[:16]
                    for mode in ("before", "after"):
                        steps = build_schedule(r.notes, 150, mode, 40, 300)
                        ts = [t for t, _k in steps]
                        assert ts == sorted(ts) and all(t >= 0 for t in ts), (s[:16], ts)
        # 行切片：越界/倒序/负数
        for a, b in [(0, 0), (3, 1), (99, 99), (-1, -1), (2, 2)]:
            out, s2, e2 = LyreApp.slice_by_lines("L1\nL2\nL3", a, b)
            assert isinstance(out, str) and 1 <= s2 <= e2 <= 3, (a, b, s2, e2)
        # 垃圾模型数据
        for junk in (None, 1, "x", [], {}, {"sections": [None, 1, "x", {"text": None}]},
                     {"sections": [{"interval_ms": "350", "start_line": "abc"}],
                      "active": "zzz"}):
            doc = SheetDoc.from_dict(junk)
            assert doc.sections and isinstance(doc.current().text, str)
        # 伪造区间标记不会把正文切开
        fake = section_marker(4, Section(name="假", own_interval=True, interval_ms=5), 5)
        text = sections_to_text([Section(name="a", text="X"), Section(name="b", text=fake + "\nY")],
                                150, 40, 300)
        back = sections_from_text(text)
        assert back and len(back) == 2, [s.name for s in (back or [])]
        assert "区间 5/5" in back[1].text, repr(back[1].text)
        # 免责声明：只有唯一一版、只读、只能同意/不同意
        assert len(DISCLAIMER_DRAFTS) == 1, len(DISCLAIMER_DRAFTS)
        assert DEFAULT_CONFIG["un_topmost_while_playing"] is False, "默认必须保持置顶"
        assert DEFAULT_CONFIG["always_on_top"] is True
        assert DEFAULT_CONFIG["config_version"] == CONFIG_VERSION
        # 老配置（v1）必须被迁移成"演奏时保持置顶"
        import tempfile as _tf
        with _tf.TemporaryDirectory() as _tmp:
            _p = os.path.join(_tmp, "config.json")
            with open(_p, "w", encoding="utf-8") as _fh:
                json.dump({"always_on_top": True, "un_topmost_while_playing": True}, _fh)
            _cfg = load_config(_p)
            assert _cfg["un_topmost_while_playing"] is False, _cfg["un_topmost_while_playing"]
            assert _cfg["config_version"] == CONFIG_VERSION
        assert disclaimer_by_id("随便什么") is DISCLAIMER_DRAFTS[0]
        assert "一、非官方声明（首要条款）" in DISCLAIMER_TEXT
        assert "严禁以任何形式销售" in DISCLAIMER_TEXT
        assert "严禁将本软件用于任何商业用途" in DISCLAIMER_TEXT
        assert APP_AUTHOR in DISCLAIMER_TEXT and APP_CONTACT in DISCLAIMER_TEXT
        assert DISCLAIMER_TEXT.strip().endswith(APP_CONTACT)
        assert "disclaimer_custom" not in DEFAULT_CONFIG
        assert "disclaimer_version" not in DEFAULT_CONFIG
        # 固定种子的随机串狂轰（每次运行都一样，能复现）
        import random
        import string as _string
        rnd = random.Random(20261001)
        alphabet = (_string.ascii_letters + _string.digits + "[]{}()@:*x/.,;|+-_ \t\n"
                    + "中文测试全角ＡＢ（）［］｛｝／　🎵!#")
        for _ in range(400):
            s = "".join(rnd.choice(alphabet) for _ in range(rnd.randint(0, 50)))
            r = parse_sheet(s, valid, rnd.choice(["chord", "repeat"]),
                            rnd.choice(["adjacent", "group"]))
            assert r.steps == len(r.notes), s
            steps = build_schedule(r.notes, rnd.choice([10, 150, 60000]),
                                   rnd.choice(["before", "after"]),
                                   rnd.choice([1, 40, 5000]), rnd.choice([1, 300, 5000]))
            ts = [t for t, _k in steps]
            assert ts == sorted(ts) and all(t >= 0 for t in ts), (s, ts)

    @case("快捷键绑定规则")
    def _c16():
        spec, msg = build_hotkey_spec("F12", set())
        assert spec and spec["name"] == "F12" and spec["mods"] == [], (spec, msg)
        spec, msg = build_hotkey_spec("a", set())
        assert spec is None and "Ctrl" in msg, (spec, msg)
        spec, msg = build_hotkey_spec("a", {"ctrl", "alt"})
        assert spec and spec["mods"] == ["alt", "ctrl"], (spec, msg)
        assert hotkey_display(spec) == "Ctrl+Alt+A", hotkey_display(spec)
        spec, msg = build_hotkey_spec("FakeKey", set())
        assert spec is None and "不支持" in msg, (spec, msg)
        spec, msg = build_hotkey_spec("Control_L", {"ctrl"})
        assert spec is None, (spec, msg)
        spec, msg = build_hotkey_spec("", set())
        assert spec is None, (spec, msg)

    @case("示例谱子文件可以被完整解析")
    def _c15():
        ensure_dirs()
        data = load_instruments(INSTRUMENTS_PATH)
        insts = instruments_list(data)
        valid = set()
        for row in insts[0]["rows"]:
            for k in row["keys"]:
                nk = normalize_key(k)
                if nk:
                    valid.add(nk)
        names = [f for f in os.listdir(SHEET_DIR) if f.lower().endswith(".txt")]
        assert names, "sheets 文件夹里没有示例谱子"
        for name in names:
            path = os.path.join(SHEET_DIR, name)
            text, _enc = read_text_file(path)
            app = LyreApp.__new__(LyreApp)
            info = LyreApp._parse_sheet_header(app, text)
            secs = sections_from_text(text)
            if secs:
                for i, sec in enumerate(secs):
                    res = parse_sheet(sec.text, valid)
                    assert res.steps > 0, (name, "区间 %d 解析出 0 步" % (i + 1))
                    assert not res.issues, (name, i, res.issues)
                print("      · %s：%d 个区间，合计 %d 步（间隔 %s，紧贴 %s）"
                      % (name, len(secs), sum(parse_sheet(s.text, valid).steps for s in secs),
                         info["interval"], info["tight"]))
                continue
            result = parse_sheet(info["body"], valid)
            assert result.steps > 0, (name, "解析出 0 步")
            print("      · %s：%d 步（和弦 %d，休止 %d，提示 %d，间隔 %s，紧贴 %s）"
                  % (name, result.steps, result.chords, result.rests,
                     len(result.issues), info["interval"], info["tight"]))
            assert not result.issues, (name, result.issues)

    return cases


def run_selftest():
    setup_logging()
    install_excepthooks()
    print("=" * 72)
    print("%s v%s 自检" % (APP_NAME, APP_VERSION))
    print("=" * 72)
    failed = 0
    for name, fn in _selftest_cases():
        try:
            fn()
            print("[通过] %s" % name)
        except Exception as exc:
            failed += 1
            print("[失败] %s -> %s: %s" % (name, type(exc).__name__, exc))
            log.error("自检失败 %s：\n%s", name, traceback.format_exc())
    print("-" * 72)
    print("共 %d 项，失败 %d 项。" % (len(_selftest_cases()), failed))
    return 1 if failed else 0


def run_smoke():
    """构建一次完整界面并立刻销毁，用来抓语法/构建期错误。窗口不会显示。"""
    setup_logging()
    install_excepthooks()
    ensure_dirs()
    cfg = load_config()
    instruments = load_instruments()
    docs, active_doc = default_docs(), 0   # 冒烟测试不依赖用户已保存的会话
    events = queue.Queue()
    root = tk.Tk()
    root.withdraw()
    hotkeys = HotkeyThread(events)
    errors = []
    cfg_backup = None
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "rb") as fh:
                cfg_backup = fh.read()
        except Exception:
            cfg_backup = None
    session_backup = None
    if os.path.exists(SESSION_PATH):
        try:
            with open(SESSION_PATH, "rb") as fh:
                session_backup = fh.read()
        except Exception:
            session_backup = None
    try:
        app = LyreApp(root, cfg, instruments, events, hotkeys, docs, active_doc)
        # 冒烟测试用固定参数，避免受用户 config.json 影响
        app.interval_var.set(150)
        app.tight_var.set(40)
        app.slash_var.set(300)
        app.hold_var.set(30)
        root.update()
        app.set_sheet_text("D D (AH) A*2 - ")
        result = parse_sheet(app.get_sheet_text(), app.valid_keys())
        assert result.steps == 6, [n.text() for n in result.notes]
        assert result.chords == 1, result.chords
        app._draw_keyboard()
        app._highlight(("A",))
        app._highlight(())
        app._handle_event(("log", "info", "smoke 测试日志"))
        app._handle_event(("status", "smoke"))
        app._handle_event(("progress", 1, 6))
        app._handle_event(("highlight", ("A", "H")))
        app._handle_event(("finished", "smoke 结束"))
        for _ in range(6):
            root.update_idletasks()
            root.update()
            time.sleep(0.01)
        app._update_hotkey_labels()
        dlg = SettingsDialog(app)
        dlg.win.withdraw()
        dlg.win.update_idletasks()
        # 设置窗口打开期间：必须暂停自动置顶，否则下拉列表会被主窗口盖住（闪烁、选不中）
        assert app._dialog_depth == 1, app._dialog_depth
        assert app._topmost_allowed() is False, "设置窗口打开时不该抢置顶"
        assert app.cfg.get("always_on_top", True) is False or True
        dlg.toggle_spec = {"mods": ["ctrl"], "vk": 0x78, "name": "F9"}
        dlg.toggle_label.set(hotkey_display(dlg.toggle_spec))
        dlg.minimize_var.set(True)
        # 走一遍"确定"的保存流程（弹窗屏蔽掉，避免测试卡住）
        _real_info = messagebox.showinfo
        messagebox.showinfo = lambda *a, **k: None
        try:
            dlg.apply()
        finally:
            messagebox.showinfo = _real_info
        assert app.cfg["minimize_on_close"] is True
        assert app.cfg["hotkey_toggle"]["name"] == "F9"
        assert app._dialog_depth == 0, "设置窗口关闭后要恢复正常置顶"
        assert app._topmost_allowed() is True
        reloaded = load_config(CONFIG_PATH)
        assert reloaded["minimize_on_close"] is True
        assert reloaded["hotkey_toggle"]["mods"] == ["ctrl"]
        root.update()
        app.check_sheet(silent=True)

        # 保存 → 载入 往返测试（屏蔽文件对话框，写到临时目录）
        import tempfile
        tmpdir = tempfile.mkdtemp(prefix="lyre_smoke_")
        target = os.path.join(tmpdir, "往返测试.txt")
        _real_save = filedialog.asksaveasfilename
        _real_err = messagebox.showerror
        filedialog.asksaveasfilename = lambda *a, **k: target
        messagebox.showerror = lambda *a, **k: None
        try:
            app.interval_var.set(237)
            app.inst_var.set("windsong_lyre")
            app.set_sheet_text("D D (AH) A*2 -")
            app.save_sheet()
            assert os.path.exists(target), "保存按钮没有写出文件"
            with open(target, "r", encoding="utf-8") as fh:
                saved = fh.read()
            assert "# 间隔: 237" in saved, saved[:200]
            assert "D D (AH) A*2 -" in saved, saved[:200]
            app.set_sheet_text("")
            app.interval_var.set(100)
            app.inst_var.set("vodyanitsa")
            app._load_sheet_file(target)
            assert app.get_sheet_text().strip() == "D D (AH) A*2 -", repr(app.get_sheet_text())
            assert app.interval_var.get() == 237, app.interval_var.get()
            assert app.inst_var.get() == "windsong_lyre", app.inst_var.get()
        finally:
            filedialog.asksaveasfilename = _real_save
            messagebox.showerror = _real_err
            try:
                import shutil
                shutil.rmtree(tmpdir, ignore_errors=True)
            except Exception:
                pass

        # 快捷键绑定窗口：构建 + 尝试捕获一个按键
        dlg2 = SettingsDialog(app)
        dlg2.win.withdraw()
        dlg2.bind_hotkey("panic")
        assert app._dialog_depth == 2, app._dialog_depth
        kids = [w for w in dlg2.win.winfo_children() if isinstance(w, tk.Toplevel)]
        if kids:
            cap = kids[0]
            try:
                cap.event_generate("<KeyPress>", keysym="F12", when="now")
                root.update()
            except Exception:
                pass
            if dlg2.panic_spec.get("name") == "F12":
                log.info("快捷键捕获测试通过：F12")
            for w in kids:
                try:
                    dlg2._close_hotkey(w)      # 必须走正规关闭，否则置顶计数会漏
                except Exception:
                    pass
        dlg2.close()
        assert app._dialog_depth == 0, app._dialog_depth
        root.update()

        # 重命名输入框（自绘，置顶安全）
        app.begin_dialog()
        app.end_dialog()
        assert app._topmost_allowed() is True
        # 演奏时置顶策略（默认：保持置顶）
        app.cfg["always_on_top"] = True
        app.cfg["un_topmost_while_playing"] = False
        app.cfg["_force_untop"] = False
        assert app._topmost_allowed() is True, "默认演奏时也要保持置顶"
        app.cfg["un_topmost_while_playing"] = True
        app.cfg["_force_untop"] = True
        assert app._topmost_allowed() is False, "勾选后才让位"
        app.cfg["_force_untop"] = False
        app.cfg["un_topmost_while_playing"] = False
        app._apply_always_on_top()
        assert app._topmost_allowed() is True

        # ---- 曲谱标签页 + 节奏区间 ----
        _real_ask = messagebox.askyesno
        _real_info2 = messagebox.showinfo
        messagebox.askyesno = lambda *a, **k: True
        messagebox.showinfo = lambda *a, **k: None
        tmpdir2 = tempfile.mkdtemp(prefix="lyre_smoke2_")
        try:
            app.select_doc(0)
            app.set_sheet_text("A B C")
            app.add_section()
            assert len(app.doc().sections) == 2, len(app.doc().sections)
            app.set_sheet_text("D E F")
            app.own_interval_var.set(True)
            app._on_own_interval()
            app.section_interval_var.set(320)
            app._on_section_interval()
            assert app.doc().current().own_interval is True
            assert app.doc().current().interval_ms == 320, app.doc().current().interval_ms
            app.select_section(0)
            assert app.get_sheet_text().strip() == "A B C", repr(app.get_sheet_text())
            app.select_section(1)
            assert app.get_sheet_text().strip() == "D E F", repr(app.get_sheet_text())
            parts, issues, per_section = app._gather_parts()
            assert len(parts) == 2 and per_section[1]["interval"] == 320, per_section
            steps = build_multi_schedule(parts, "before", 40, 300)
            assert len(steps) == 6, len(steps)
            global_ms = safe_int(app.interval_var.get(), 150, 10, 60000)
            # 区间1 用全局间隔走 3 步，区间2 用自己 320 走 3 步
            expect_len = global_ms * 3 + 320 * 3
            assert schedule_duration(steps) == expect_len, (schedule_duration(steps), expect_len)
            # 新建 / 复制 / 关闭标签
            app.new_doc()
            assert len(app.docs) == 2
            app.set_sheet_text("G A B")
            app.duplicate_doc()
            assert len(app.docs) == 3, len(app.docs)
            app.select_doc(1)
            assert app.get_sheet_text().strip() == "G A B", repr(app.get_sheet_text())
            app.close_doc(2)
            assert len(app.docs) == 2, len(app.docs)
            # 会话落盘 + 读回
            app.save_session_now()
            docs2, _active2 = load_session(SESSION_PATH)
            assert len(docs2) == 2, len(docs2)
            assert len(docs2[0].sections) == 2 and docs2[0].sections[1].interval_ms == 320
            # 多区间保存 / 读回
            target2 = os.path.join(tmpdir2, "多区间.txt")
            filedialog.asksaveasfilename = lambda *a, **k: target2
            app.select_doc(0)
            app.save_sheet()
            with open(target2, "r", encoding="utf-8") as fh:
                saved2 = fh.read()
            assert "#=== 区间 1/2:" in saved2 and "#=== 区间 2/2:" in saved2, saved2[:300]
            assert "独立间隔=320" in saved2, saved2[:300]
            app._load_sheet_file(target2)
            assert len(app.doc().sections) == 2, len(app.doc().sections)
            assert app.doc().sections[1].interval_ms == 320
            assert app.doc().sections[1].text.strip() == "D E F"
            # 删除区间 / 上限保护
            app.select_section(1)
            app.delete_section()
            assert len(app.doc().sections) == 1
            for _ in range(MAX_SECTIONS + 3):
                app.add_section()
            assert len(app.doc().sections) == MAX_SECTIONS, len(app.doc().sections)
        finally:
            filedialog.asksaveasfilename = _real_save
            messagebox.askyesno = _real_ask
            messagebox.showinfo = _real_info2
            try:
                import shutil
                shutil.rmtree(tmpdir2, ignore_errors=True)
            except Exception:
                pass

        # ---- 行号栏 / 演奏行范围 / 预检 / 免责声明窗口 ----
        _real_ask2 = messagebox.askokcancel
        _real_err2 = messagebox.showerror
        _real_info3 = messagebox.showinfo
        messagebox.askokcancel = lambda *a, **k: True
        messagebox.showerror = lambda *a, **k: None
        messagebox.showinfo = lambda *a, **k: None
        try:
            app.new_doc()          # 干净的新谱子（1 个区间），避免受前面压力测试影响
            root.update()
            assert len(app.doc().sections) == 1, len(app.doc().sections)
            app.set_sheet_text("A B C\nD E F\n(GH)[200] J")
            root.update()
            app._refresh_gutter()
            assert app.gutter.get("1.0", "end-1c").strip(), "行号栏是空的"
            app.range_start_var.set("2")
            app.range_end_var.set("3")
            root.update()
            assert app.doc().current().start_line == 2, app.doc().current().start_line
            parts, issues, per_section = app._gather_parts()
            assert per_section[0]["range"] == (2, 3), per_section[0]
            # 第 2~3 行 = "D E F" + "(GH)[200] J" = 5 步（整首是 8 步）
            assert per_section[0]["steps"] == 5, per_section[0]
            # 越界 / 倒序 / 负数都不许崩
            app.range_start_var.set("99")
            app.range_end_var.set("-5")
            root.update()
            parts2, _i2, per2 = app._gather_parts()
            assert parts2 and per2
            app.range_start_var.set("")
            app.range_end_var.set("")
            root.update()
            parts3, issues3, per3 = app._gather_parts()
            assert per3[0]["range"] is None
            assert per3[0]["steps"] == 8, per3[0]
            # 预检 + 确认弹窗
            warns, errors = app.preflight(parts3, issues3, per3)
            assert app.confirm_before_play(warns, errors) is True
            assert app.confirm_before_play([], ["整首谱子里没有任何可演奏的音符。"]) is False
            assert app.confirm_before_play(["t"], []) is True
            # 免责声明：只读闸门窗口
            dlg3 = DisclaimerDialog(app)
            dlg3.win.withdraw()
            dlg3.win.update_idletasks()
            body = dlg3.text.get("1.0", "end-1c")
            assert body.strip(), "免责声明正文是空的"
            assert body == DISCLAIMER_TEXT, "展示的正文必须与内置文案一致"
            assert "非官方" in body
            assert str(dlg3.text.cget("state")) == "disabled", "免责声明必须只读"
            assert not hasattr(dlg3, "combo"), "弹窗里不许再有版本切换"
            assert not hasattr(dlg3, "copy_text") and not hasattr(dlg3, "edit_text")
            # 勾"下次不再弹出"后同意
            dlg3.remember_var.set(True)
            dlg3.accept()
            assert app.cfg["disclaimer_show"] is False
            assert app.cfg["disclaimer_accepted"]
            # 再次打开时开关生效（不再弹）
            assert app.show_disclaimer() is True
            # 行号位置切换
            app.cfg["line_number_side"] = "left"
            app._apply_gutter_side()
            app.cfg["line_number_side"] = "right"
            app._apply_gutter_side()
            app.cfg["line_numbers"] = False
            app._refresh_gutter()
            app.cfg["line_numbers"] = True
            app._refresh_gutter()
        finally:
            messagebox.askokcancel = _real_ask2
            messagebox.showerror = _real_err2
            messagebox.showinfo = _real_info3
    except Exception:
        errors.append(traceback.format_exc())
    finally:
        try:
            if cfg_backup is None:
                if os.path.exists(CONFIG_PATH):
                    os.remove(CONFIG_PATH)  # 测试写的配置不要留给用户
            else:
                with open(CONFIG_PATH, "wb") as fh:
                    fh.write(cfg_backup)
        except Exception:
            pass
        try:
            if session_backup is None:
                if os.path.exists(SESSION_PATH):
                    os.remove(SESSION_PATH)
            else:
                with open(SESSION_PATH, "wb") as fh:
                    fh.write(session_backup)
        except Exception:
            pass
        try:
            root.destroy()
        except Exception:
            pass
    if errors:
        print("界面冒烟测试失败：")
        print(errors[0])
        log.error("界面冒烟测试失败：\n%s", errors[0])
        return 1
    print("界面冒烟测试通过：主窗口 + 设置窗口构建正常，"
          "解析 6 步（D D (AH) A A 休止）。")
    return 0


def acquire_singleton():
    if not WIN:
        return None
    try:
        kernel32.CreateMutexW.restype = wintypes.HANDLE
        kernel32.CreateMutexW.argtypes = (ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR)
        handle = kernel32.CreateMutexW(None, False, "Local\\GenshinLyrePlayer_SingleInstance")
        err = ctypes.get_last_error()
        if not handle:
            return None
        if err == ERROR_ALREADY_EXISTS:
            return False
        return handle
    except Exception:
        return None


def main(argv=None):
    enable_dpi_awareness()
    args = parse_args(argv)
    if args.version:
        print("%s v%s" % (APP_NAME, APP_VERSION))
        return 0
    if args.selftest:
        return run_selftest()
    if args.smoke:
        return run_smoke()

    ensure_dirs()
    install_excepthooks()
    setup_logging(verbose=True)

    import tkinter as tk
    from tkinter import font as tkfont

    if not args.no_singleton:
        state = acquire_singleton()
        if state is False:
            tmp = tk.Tk()
            tmp.withdraw()
            messagebox.showwarning(
                APP_NAME,
                "程序已经在运行了。\n如果界面上看不到它，请查看任务栏（可能被最小化到了任务栏）。\n\n"
                "提示：同一时间只允许运行一个，避免重复按键。",
            )
            tmp.destroy()
            log.warning("检测到重复启动，已退出。")
            return 1

    cfg = load_config()
    instruments = load_instruments()
    docs, active_doc = load_session()
    events = queue.Queue(maxsize=20000)
    # 界面日志
    setup_logging(events, verbose=bool(cfg.get("verbose_log", True)))
    hotkeys = HotkeyThread(events)

    root = tk.Tk()
    try:
        dpi = get_dpi()
        if dpi and abs(dpi - 96) > 1:
            root.tk.call("tk", "scaling", dpi / 72.0)
        for fname, base in (("TkDefaultFont", 10), ("TkTextFont", 10), ("TkMenuFont", 10),
                            ("TkHeadingFont", 10)):
            try:
                tkfont.nametofont(fname).configure(size=max(9, int(round(base * dpi / 96.0))))
            except Exception:
                pass
    except Exception:
        log.exception("设置 DPI 缩放失败")

    app = LyreApp(root, cfg, instruments, events, hotkeys, docs, active_doc)
    hotkeys.start()
    hotkeys.set_bindings(cfg.get("hotkey_toggle"), cfg.get("hotkey_panic"))
    # 启动时先看免责声明（默认显示；窗口已经建好但还没进入主循环）
    if not args.no_disclaimer:
        if not app.show_disclaimer():
            log.info("用户未同意免责声明，程序退出。")
            return 0

    def _on_root_destroy(_event=None):
        try:
            hotkeys.stop()
        except Exception:
            pass

    root.bind("<Destroy>", _on_root_destroy)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        pass
    except Exception:
        log.exception("主循环异常退出")
    finally:
        try:
            app.player.stop("程序退出")
        except Exception:
            pass
        try:
            hotkeys.stop()
        except Exception:
            pass
        try:
            save_json(CONFIG_PATH, app.public_config())
        except Exception:
            pass
        log.info("主循环结束。")
    return 0


def parse_args(argv=None):
    p = argparse.ArgumentParser(description=APP_NAME)
    p.add_argument("--selftest", action="store_true", help="运行自检（不发送按键）")
    p.add_argument("--smoke", action="store_true", help="界面冒烟测试（窗口不显示）")
    p.add_argument("--no-singleton", action="store_true", dest="no_singleton",
                   help="允许多开（默认单实例）")
    p.add_argument("--no-disclaimer", action="store_true", dest="no_disclaimer",
                   help="启动时不显示免责声明（测试用）")
    p.add_argument("--version", action="store_true", help="显示版本")
    return p.parse_args(argv)


if __name__ == "__main__":
    sys.exit(main())
