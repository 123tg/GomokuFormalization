# GomokuFormalization 项目指南

## 1. 当前固定规则

项目主线只考虑：

```text
board size = 7 × 7
win length = 5
first player = Black
rule = unrestricted Gomoku
```

`Coord`、`Board`、`Position`、搜索器、缓存键、证书和 C++ 导出器全部直接使用
这一套固定定义。主线中没有 `Coord7`、`Board7`、`Position7` 或另一套证书类型。

## 2. 依赖结构

```text
Basic
  ↓
Geometry
  ↓
Rules
  ↓
Game
  ├─→ Tactics
  └─→ Certificate
          ↓
        Search
        ├─→ Bounded
        └─→ Engine
```

`Gomoku.RuleAudit` 是精简验收层，`Gomoku.Generated.CppSmoke` 是 C++ 到 Lean
的最小导出回归。

## 3. 基础类型

```lean
abbrev Coord := Fin 7 × Fin 7

structure Board where
  cell : Coord → Cell

structure Position where
  board : Board
  turn : Player
```

`Fin 7` 从类型上保证坐标只能是 0 到 6。`Position.initial` 的棋盘为空且
`turn = .black`。

## 4. 几何与胜负

`Direction` 保留四个方向：水平、竖直、主对角线、副对角线。
`step` 只在新坐标仍满足

\[
0 \le x < 7, \qquad 0 \le y < 7
\]

时返回坐标。棋盘边界不被当作空点。

获胜长度仍为 5。`hasAtLeastFive` 存在当且存在起点和方向，使连续五个坐标
都是同一玩家的棋子。六连、七连也包含五连窗口，因此仍判胜。

`terminal` 的顺序保持不变：

1. 黑方五连：`some .blackWin`；
2. 白方五连：`some .whiteWin`；
3. 无胜者且棋盘满：`some .draw`；
4. 否则：`none`。

## 5. 坐标编码

`Gomoku.Search` 使用固定的行主序编码：

```text
index = y * 7 + x
x = index % 7
y = index / 7
```

Lean 类型为：

```lean
coordAtIndex : Fin 49 → Coord
coordIndex : Coord → Fin 49
allCoords : Array Coord
```

`coordAtIndex_coordIndex` 与 `coordIndex_coordAtIndex` 证明两个映射互逆。
`PositionKey` 保存轮次和完整 `Vector Cell 49`，所以它不会因为棋盘迁移而丢失局面信息。

## 6. 证书可信边界

`CompactCertificate` 直接引用当前的 7×7 `Position`。它的主要节点是：

```lean
.terminal position outcome
.proverMove position move child
.opponentMoves position children
```

`checkCertificate` 额外要求目标为黑方且根为 7×7 空棋盘。
`checkLocalCertificateAt` 允许局部根，但不削弱以下检查：

- 根和子节点编号有效；
- `parent < child`，因此自环、回边和循环被拒绝；
- 每步合法；
- 子局面等于 `play parent move`；
- 终局标签由 Lean 重新计算；
- 对手节点覆盖全部合法应手。

`compact_certificate_sound` 与 `local_certificate_at_sound` 是从可执行检查到
`CanForceWin` 定理的信任桥。C++ 搜索、启发式、缓存和证书预检都不属于这条信任链。

## 7. 搜索语义

搜索器只生成候选必胜树：

- 目标方回合是 OR 节点，找到一个成功子节点即可；
- 对手回合是 AND 节点，每个合法应手都必须成功；
- 只有目标方真实获胜的局面能作为胜利叶子。

搜索深度或资源上限耗尽必须返回 `none`、`depthLimit`、`nodeLimit` 等未知状态，
不能写成和棋。本阶段没有实现完整 7×7 minimax 或和棋证书。

## 8. C++ 主线

`cpp/include/gomoku_solver.hpp` 定义：

```cpp
constexpr int boardSize = 7;
constexpr int winLength = 5;
constexpr int boardCells = boardSize * boardSize;
```

旧的四个 `uint64_t` bitboard word 仍保留；只使用前 49 bit，这在语义上正确。
单词 bitboard 可以作为以后的小型优化，不属于本次迁移。

C++ 输入必须是 7 行、每行 7 格。导出器使用 `Coord`、`Position` 和
`CompactCertificate`，不显式生成旧尺寸的有限坐标类型。

## 9. 验收与构建

主线只保留精简验收：

- 49 个坐标、49 个初始合法着、黑先、初始非终局；
- 横、竖、主/副对角线五连，黑白胜利，长连，满盘和棋；
- 局部证书通过；
- 错子局面、错终局标签、非法着、错编号、循环、漏对手应手被拒绝；
- C++ 导出的 `CppSmoke` 被 Lean 重新检查。

构建命令：

```powershell
lake build
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```

## 10. 当前结论边界

已完成的是“固定 7×7 基础定义与证书检查链”。当前没有：

- 从 7×7 空棋盘开始的完整必胜证书；
- 标准五子棋的完整和棋证书；
- 在 Lean 中经检查的全局 7×7 求解结论。

必须继续区分“C++ 计算结果”和“Lean 已检查定理”。
