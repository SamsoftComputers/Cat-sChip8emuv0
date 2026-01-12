#!/usr/bin/env python3
"""
Cat's Chip-8 Emulator
Complete CHIP-8 emulator with Tkinter GUI
Project64-style interface
"""

import os
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import random
import time
import threading

# =========================
# CHIP-8 CONSTANTS
# =========================

FONTSET = [
    0xF0, 0x90, 0x90, 0x90, 0xF0,
    0x20, 0x60, 0x20, 0x20, 0x70,
    0xF0, 0x10, 0xF0, 0x80, 0xF0,
    0xF0, 0x10, 0xF0, 0x10, 0xF0,
    0x90, 0x90, 0xF0, 0x10, 0x10,
    0xF0, 0x80, 0xF0, 0x10, 0xF0,
    0xF0, 0x80, 0xF0, 0x90, 0xF0,
    0xF0, 0x10, 0x20, 0x40, 0x40,
    0xF0, 0x90, 0xF0, 0x90, 0xF0,
    0xF0, 0x90, 0xF0, 0x10, 0xF0,
    0xF0, 0x90, 0xF0, 0x90, 0x90,
    0xE0, 0x90, 0xE0, 0x90, 0xE0,
    0xF0, 0x80, 0x80, 0x80, 0xF0,
    0xE0, 0x90, 0x90, 0x90, 0xE0,
    0xF0, 0x80, 0xF0, 0x80, 0xF0,
    0xF0, 0x80, 0xF0, 0x80, 0x80,
]

KEY_MAP = {
    '1': 0x1, '2': 0x2, '3': 0x3, '4': 0xC,
    'q': 0x4, 'w': 0x5, 'e': 0x6, 'r': 0xD,
    'a': 0x7, 's': 0x8, 'd': 0x9, 'f': 0xE,
    'z': 0xA, 'x': 0x0, 'c': 0xB, 'v': 0xF,
}

# =========================
# CHIP-8 CPU
# =========================

class Chip8CPU:
    def __init__(self):
        self.reset()

    def reset(self):
        self.memory = [0] * 4096
        self.V = [0] * 16
        self.I = 0
        self.PC = 0x200
        self.SP = 0
        self.stack = [0] * 16
        self.delay_timer = 0
        self.sound_timer = 0
        self.display = [[0] * 64 for _ in range(32)]
        self.keys = [0] * 16

        self.draw_flag = False
        self.sound_flag = False
        self.waiting_for_key = False
        self.key_register = 0

        # Quirks
        self.shift_quirk = True        # COSMAC VIP behavior
        self.increment_i = True        # FX55 / FX65 increment I

        # Safety
        self.max_pc = 4094

        for i, b in enumerate(FONTSET):
            self.memory[i] = b

    def load_rom(self, data: bytes) -> bool:
        if len(data) > 3584:
            return False
        self.reset()
        for i, b in enumerate(data):
            self.memory[0x200 + i] = b
        return True

    def cycle(self):
        if self.waiting_for_key:
            return
        if self.PC >= self.max_pc:
            return
        opcode = (self.memory[self.PC] << 8) | self.memory[self.PC + 1]
        self.execute(opcode)

    def execute(self, opcode: int):
        nnn = opcode & 0x0FFF
        nn = opcode & 0x00FF
        n = opcode & 0x000F
        x = (opcode >> 8) & 0xF
        y = (opcode >> 4) & 0xF
        op = opcode >> 12

        if opcode == 0x00E0:
            self.display = [[0]*64 for _ in range(32)]
            self.draw_flag = True
            self.PC += 2

        elif opcode == 0x00EE:
            self.SP -= 1
            self.PC = self.stack[self.SP] + 2

        elif op == 0x1:
            self.PC = nnn

        elif op == 0x2:
            self.stack[self.SP] = self.PC
            self.SP += 1
            self.PC = nnn

        elif op == 0x3:
            self.PC += 4 if self.V[x] == nn else 2

        elif op == 0x4:
            self.PC += 4 if self.V[x] != nn else 2

        elif op == 0x5 and n == 0:
            self.PC += 4 if self.V[x] == self.V[y] else 2

        elif op == 0x6:
            self.V[x] = nn
            self.PC += 2

        elif op == 0x7:
            self.V[x] = (self.V[x] + nn) & 0xFF
            self.PC += 2

        elif op == 0x8:
            if n == 0x6:
                val = self.V[y] if self.shift_quirk else self.V[x]
                self.V[0xF] = val & 1
                self.V[x] = val >> 1
            elif n == 0xE:
                val = self.V[y] if self.shift_quirk else self.V[x]
                self.V[0xF] = (val >> 7) & 1
                self.V[x] = (val << 1) & 0xFF
            elif n == 0x4:
                s = self.V[x] + self.V[y]
                self.V[x] = s & 0xFF
                self.V[0xF] = 1 if s > 255 else 0
            elif n == 0x5:
                self.V[0xF] = 1 if self.V[x] >= self.V[y] else 0
                self.V[x] = (self.V[x] - self.V[y]) & 0xFF
            elif n == 0x7:
                self.V[0xF] = 1 if self.V[y] >= self.V[x] else 0
                self.V[x] = (self.V[y] - self.V[x]) & 0xFF
            elif n == 0x0:
                self.V[x] = self.V[y]
            elif n == 0x1:
                self.V[x] |= self.V[y]
                self.V[0xF] = 0
            elif n == 0x2:
                self.V[x] &= self.V[y]
                self.V[0xF] = 0
            elif n == 0x3:
                self.V[x] ^= self.V[y]
                self.V[0xF] = 0
            self.PC += 2

        elif op == 0x9 and n == 0:
            self.PC += 4 if self.V[x] != self.V[y] else 2

        elif op == 0xA:
            self.I = nnn
            self.PC += 2

        elif op == 0xB:
            self.PC = nnn + self.V[0]

        elif op == 0xC:
            self.V[x] = random.randint(0,255) & nn
            self.PC += 2

        elif op == 0xD:
            self.V[0xF] = 0
            for row in range(n):
                sprite = self.memory[self.I + row]
                for col in range(8):
                    if sprite & (0x80 >> col):
                        px = (self.V[x] + col) % 64
                        py = (self.V[y] + row) % 32
                        if self.display[py][px]:
                            self.V[0xF] = 1
                        self.display[py][px] ^= 1
            self.draw_flag = True
            self.PC += 2

        elif op == 0xE:
            if nn == 0x9E:
                self.PC += 4 if self.keys[self.V[x]] else 2
            elif nn == 0xA1:
                self.PC += 4 if not self.keys[self.V[x]] else 2

        elif op == 0xF:
            if nn == 0x07:
                self.V[x] = self.delay_timer
            elif nn == 0x0A:
                self.waiting_for_key = True
                self.key_register = x
            elif nn == 0x15:
                self.delay_timer = self.V[x]
            elif nn == 0x18:
                self.sound_timer = self.V[x]
            elif nn == 0x1E:
                self.I += self.V[x]
            elif nn == 0x29:
                self.I = (self.V[x] & 0xF) * 5
            elif nn == 0x33:
                v = self.V[x]
                self.memory[self.I:self.I+3] = [v//100, (v//10)%10, v%10]
            elif nn == 0x55:
                for i in range(x+1):
                    self.memory[self.I+i] = self.V[i]
                if self.increment_i:
                    self.I += x + 1
            elif nn == 0x65:
                for i in range(x+1):
                    self.V[i] = self.memory[self.I+i]
                if self.increment_i:
                    self.I += x + 1
            self.PC += 2

    def update_timers(self):
        if self.delay_timer > 0:
            self.delay_timer -= 1
        if self.sound_timer > 0:
            self.sound_timer -= 1
            self.sound_flag = True
        else:
            self.sound_flag = False

    def key_press(self, k):
        self.keys[k] = 1
        if self.waiting_for_key:
            self.V[self.key_register] = k
            self.waiting_for_key = False

    def key_release(self, k):
        self.keys[k] = 0

# =========================
# GUI / EMULATOR
# =========================

class Chip8Emulator:
    def __init__(self):
        self.cpu = Chip8CPU()
        self.cycles_per_frame = 10
        self.running = False
        self.sound_pending = False

        self.root = tk.Tk()
        self.root.title("Cat's CHIP-8 Emulator")
        self.root.configure(bg="#2D2D30")

        self.canvas = tk.Canvas(self.root, width=512, height=256, bg="#001100")
        self.canvas.pack(expand=True)

        self.pixels = [[
            self.canvas.create_rectangle(x*8, y*8, x*8+8, y*8+8, fill="#001100", outline="")
            for x in range(64)
        ] for y in range(32)]

        self.root.bind("<KeyPress>", self.on_key_press)
        self.root.bind("<KeyRelease>", self.on_key_release)
        self.root.protocol("WM_DELETE_WINDOW", self.root.quit)

        self.thread = threading.Thread(target=self.loop, daemon=True)
        self.thread.start()

    def loop(self):
        while True:
            if self.running:
                for _ in range(self.cycles_per_frame):
                    self.cpu.cycle()
                self.cpu.update_timers()
                if self.cpu.draw_flag:
                    self.root.after(0, self.draw)
                    self.cpu.draw_flag = False
                if self.cpu.sound_flag:
                    self.sound_pending = True
            if self.sound_pending:
                self.root.after(0, self.root.bell)
                self.sound_pending = False
            time.sleep(1/60)

    def draw(self):
        for y in range(32):
            for x in range(64):
                self.canvas.itemconfig(
                    self.pixels[y][x],
                    fill="#00FF00" if self.cpu.display[y][x] else "#001100"
                )

    def on_key_press(self, e):
        if e.keysym.lower() in KEY_MAP:
            self.cpu.key_press(KEY_MAP[e.keysym.lower()])

    def on_key_release(self, e):
        if e.keysym.lower() in KEY_MAP:
            self.cpu.key_release(KEY_MAP[e.keysym.lower()])

    def run(self):
        self.running = True
        self.root.mainloop()

# =========================
# MAIN
# =========================

if __name__ == "__main__":
    Chip8Emulator().run()
