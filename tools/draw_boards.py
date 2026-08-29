#!/usr/bin/env python3
# draw_boards.py — render 7x7 draw-position board diagrams as PNG images and
# a Markdown gallery.  Reads the solver position files
# (cpp/examples/draw_7x7*.txt) and writes docs/boards/*.png + docs/DRAW_GALLERY.md.
import os
import re
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Rectangle

SIZE = 7
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXAMPLES = os.path.join(ROOT, "cpp", "examples")
OUT_DIR = os.path.join(ROOT, "docs", "boards")


def parse_position(path):
    """Return (turn, board) where board[y][x] in {'B','W','.'}."""
    turn = None
    rows = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            m = re.match(r"^(turn|target)\s*=?\s*(\w+)", line)
            if m:
                if m.group(1) == "turn":
                    turn = m.group(2)
                continue
            if re.fullmatch(r"[BWo.]+", line) and len(line) == SIZE:
                rows.append(line)
    assert len(rows) == SIZE, f"{path}: expected {SIZE} rows, got {len(rows)}"
    return turn, rows


def ascii_board(rows):
    lines = []
    lines.append("      x=0 1 2 3 4 5 6")
    for y, row in enumerate(rows):
        cells = " ".join(c if c in "BW" else "·" for c in row)
        lines.append(f"  y={y}   {cells}")
    return "\n".join(lines)


def render_png(rows, title, subtitle, out_path):
    fig, ax = plt.subplots(figsize=(6.4, 6.8), dpi=150)
    ax.set_xlim(-0.7, 6.7)
    ax.set_ylim(-0.9, 6.7)
    ax.set_aspect("equal")
    ax.axis("off")

    # Board background.
    ax.add_patch(Rectangle((-0.62, -0.62), 7.24, 7.24, facecolor="#e8c07a",
                           edgecolor="#5a3a1a", linewidth=2.5, zorder=0))
    # Grid lines.
    for i in range(SIZE):
        ax.plot([i - 0.5, i - 0.5], [-0.5, SIZE - 0.5], color="#8a5a2a",
                linewidth=1.0, zorder=1)
        ax.plot([-0.5, SIZE - 0.5], [i - 0.5, i - 0.5], color="#8a5a2a",
                linewidth=1.0, zorder=1)
    # Star points at 1,3,5 (like a Go board).
    for sx, sy in [(1, 1), (3, 3), (5, 5)]:
        ax.plot(sx, sy, "o", color="#5a3a1a", markersize=3.5, zorder=2)

    # Stones (matplotlib y axis grows upward; board row 0 at bottom).
    for y, row in enumerate(rows):
        for x, ch in enumerate(row):
            py = SIZE - 1 - y
            if ch == "B":
                ax.add_patch(Circle((x, py), 0.42, facecolor="#1a1a1a",
                                    edgecolor="#000000", linewidth=1.2, zorder=3))
            elif ch == "W":
                ax.add_patch(Circle((x, py), 0.42, facecolor="#f5f5f5",
                                    edgecolor="#000000", linewidth=1.2, zorder=3))
            elif ch == ".":
                ax.plot(x, py, ".", color="#7a5a2a", markersize=2.0, zorder=2)

    # Coordinates.
    for x in range(SIZE):
        ax.text(x, -0.95, str(x), ha="center", va="top", fontsize=9,
                color="#3a2a1a")
    for y in range(SIZE):
        ax.text(-0.95, SIZE - 1 - y, str(y), ha="right", va="center",
                fontsize=9, color="#3a2a1a")

    ax.set_title(title, fontsize=13, pad=14, color="#1a1a1a")
    ax.text(0.0, -1.65, subtitle, ha="left", va="top", fontsize=9,
            color="#444444", transform=ax.transData)
    fig.tight_layout()
    fig.savefig(out_path, bbox_inches="tight", facecolor="white")
    plt.close(fig)


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    entries = []
    # Deterministic order: the original then s2..s9.
    names = [("draw_7x7.txt", "Draw7x7", "seed 1 (original)")]
    for s in range(2, 10):
        names.append((f"draw_7x7_s{s}.txt", f"Draw7x7s{s}", f"seed {s}"))
    for fname, lean_name, label in names:
        path = os.path.join(EXAMPLES, fname)
        if not os.path.exists(path):
            print(f"skip {path}")
            continue
        turn, rows = parse_position(path)
        counts = {"B": 0, "W": 0, ".": 0}
        for row in rows:
            for ch in row:
                counts[ch] += 1
        title = f"{lean_name} — StandardDraw (7×7)"
        subtitle = (f"{counts['B']} black + {counts['W']} white, "
                    f"{counts['.']} empty, {turn} to move")
        png = os.path.join(OUT_DIR, f"{lean_name}.png")
        render_png(rows, title, subtitle, png)
        entries.append((lean_name, label, turn, rows, counts, png))
        print(f"rendered {png}")

    # Gallery markdown.
    md = [
        "# 7×7 和棋局面图集 (Draw Gallery)",
        "",
        "下列 9 个局面均已在 Lean 中机器验证 `StandardDraw`(每个长度 5 窗口",
        "同时含黑子和白子,任何一方都无法成五;两侧防守证书由 C++ 搜索生成,",
        "Lean 检查器验证后组合出和棋)。",
        "",
        "| 定理 | 局面 | 黑 | 白 | 空 | 轮到 |",
        "|---|---|---|---|---|---|",
    ]
    for lean_name, label, turn, rows, counts, png in entries:
        md.append(
            f"| `{lean_name}.lean` | {label} | {counts['B']} | {counts['W']} | "
            f"{counts['.']} | {turn} |"
        )
    md.append("")
    for lean_name, label, turn, rows, counts, png in entries:
        md.append(f"## {lean_name} ({label})")
        md.append("")
        md.append(f"`StandardDraw <{lean_name} 根局面>` — {counts['B']} 黑 + "
                  f"{counts['W']} 白, {counts['.']} 空, {turn} 走。")
        md.append("")
        md.append("![board](boards/" + os.path.basename(png) + ")")
        md.append("")
        md.append("```text")
        md.append(ascii_board(rows))
        md.append("```")
        md.append("")
    gallery = os.path.join(ROOT, "docs", "DRAW_GALLERY.md")
    with open(gallery, "w", encoding="utf-8") as f:
        f.write("\n".join(md))
    print(f"wrote {gallery}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
