# 7×7 GomokuFormalization 学习指南

这份文档按“问题建立 → 建模 → 规则 → 博弈语义 → 证书 → 搜索器”的顺序
说明当前本地主线。

## 1. 问题是什么

形式化对象是固定 7×7 无禁手五子棋：

- 坐标范围为 0 到 6；
- 黑方先手；
- 任一方沿水平、竖直或两种对角方向连续至少五子即胜；
- 无人获胜且 49 格全满时为和棋。

当前阶段的目标是让 Lean 和 C++ 在同一个 7×7 模型上工作，而不是已经
完成空棋盘的必胜或和棋求解。

## 2. 基础建模：`Basic.lean`

```lean
inductive Player where
  | black
  | white

inductive Cell where
  | empty
  | stone (player : Player)

abbrev Coord := Fin 7 × Fin 7

structure Board where
  cell : Coord → Cell
```

`Fin 7` 不只是一个整数，它同时带有“该整数小于 7”的证明。因此一个
`Coord` 值不可能越界。

`Board` 是从坐标到格子的函数，`Board.place b c p` 返回一个新棋盘：坐标
`c` 变为玩家 `p` 的棋子，其他坐标保持不变。

`Board.count`、`Board.emptyCount` 基于有限坐标全集。空棋盘的空点数是

\[
7 \times 7 = 49.
\]

## 3. 几何：`Geometry.lean`

`Direction` 包含四个值：

```text
horizontal    = (1, 0)
vertical      = (0, 1)
diagonalUp    = (1, 1)
diagonalDown  = (1, -1)
```

`step c d n` 表示从 `c` 沿 `d` 移动 `n` 步。它先在整数上计算，再检查

\[
0 \le x < 7 \quad\text{and}\quad 0 \le y < 7.
\]

越界时返回 `none`。这条规则对五连扫描和开放端检查都很重要：棋盘外不是空点。

`consecutive b p c d n` 表示从 `c` 开始沿 `d` 的 `n` 个坐标全是 `p` 的棋子。
`hasAtLeastFive` 就是查找长度为 5 的这种窗口。棋盘边长是 7，但获胜长度没有改成 7。

## 4. 规则与局面：`Rules.lean`

```lean
structure Position where
  board : Board
  turn : Player
```

`Position.initial = ⟨Board.empty, .black⟩`。

`legalMove s c` 由两个条件组成：

1. `s` 还没有终局；
2. `c` 是空点。

`play s c` 在 `c` 放入 `s.turn` 的棋子，然后用 `Player.other` 切换行棋方。

`terminal` 是可执行函数，它按以下顺序返回：

```text
black five  -> some blackWin
white five  -> some whiteWin
full board  -> some draw
otherwise   -> none
```

`Reachable` 只允许从 `Position.initial` 开始，经过合法着法构造局面。这使 Lean 能证明
黑白棋子数、轮次和胜者之间的不变量。

## 5. 博弈语义：`Game.lean`

`CanForceWin s p` 不是“搜索器说能赢”，而是形式化的 AND/OR 树语义：

- 已是 `p` 胜的终局，则成功；
- 轮到 `p` 时，存在一个合法着法使子局面继续成功；
- 轮到对手时，对手的每个合法着法都必须有成功子局面。

这解释了为什么搜索器在对手节点不能只保留“相关”应手。

## 6. 战术层：`Tactics.lean`

`WinningCells s p` 是几何制胜点集合：在该空点放入 `p` 后形成五连。
`HasDoubleThreat` 表示制胜点至少有两个。活三、活四、断三和跳四是帮助搜索排序的
几何定义；只有完整前提的定理才能把它们提升为 `CanForceWin`。

## 7. 证书：`Certificate.lean`

`CompactCertificate` 把策略树序列化为数组：

```lean
structure CompactCertificate where
  target : Player
  root : Nat
  nodes : Array CertificateNode
```

三种节点分别表示目标方胜利叶子、目标方选择一步、对手的全部应手。

检查器不信任证书中的局面或标签，而是验证：

- 节点 id 在范围内；
- `parent < child`；
- 着法合法；
- 子局面确实是 `play`的结果；
- 终局类型重新计算正确；
- 对手的每个合法应手都被覆盖。

`checkCertificate` 还要求根是空 7×7 棋盘、黑方先手。
`checkLocalCertificateAt` 用于局部根。两者分别通过
`compact_certificate_sound` 和 `local_certificate_at_sound` 连接到形式定理。

## 8. 49 点索引与搜索：`Search.lean`

```lean
coordAtIndex : Fin 49 → Coord
coordIndex : Coord → Fin 49
allCoords : Array Coord
```

编码规则是

\[
\operatorname{index}(x,y)=7y+x,
\qquad
x=i\bmod 7,
\qquad
y=\lfloor i/7\rfloor.
\]

`coordAtIndex_coordIndex` 和 `coordIndex_coordAtIndex` 证明它们互逆。
`PositionKey = Player × Vector Cell 49` 保存完整棋盘和轮次，不是可能碰撞的短哈希。

`candidateMoves`、`orderedCandidateMoves`、`firstWinningMove` 等函数只帮助寻找候选树。
`CheckedDepthResult` 区分：

```text
noCandidate = 当前资源下未找到
rejected    = 候选证书被检查器拒绝
accepted    = 候选证书通过检查
```

只有 `accepted` 有 soundness 定理。

## 9. Lean 引擎和 C++ 导出

`Engine.lean` 在 `Search` 之上增加迭代加深、节点上限、威胁排序和缓存。它的缓存键包含
完整搜索配置、剩余深度、目标方、轮次和完整棋盘。

C++ 主程序使用同样的 7×7 规则和行主序索引。它输出 Lean 源文件，其中根棋盘
用 `(Coord × Player)` 数组表示，证书直接使用 `CompactCertificate`。C++ 预检可以早发现
导出错误，但只有 Lean 检查才能产生数学结论。

## 10. 当前保留的测试

`RuleAudit.lean` 只保留迁移验收所需的小型用例：

- 49 个 `Coord`；
- 初始空点和合法着都是 49；
- 黑先、初始 `terminal = none`；
- 四个方向五连、黑白胜利、长连、满盘和棋；
- 一个通过的局部证书；
- 错子局面、错标签、非法着、错 id、循环、漏应手被拒绝；
- C++ 生成的 `CppSmoke` 通过 Lean 检查。

## 11. 如何阅读项目

建议顺序：

1. `Gomoku/Basic.lean`；
2. `Gomoku/Geometry.lean`；
3. `Gomoku/Rules.lean`；
4. `Gomoku/Game.lean`；
5. `Gomoku/Tactics.lean`；
6. `Gomoku/Certificate.lean`；
7. `Gomoku/Search.lean`；
8. `Gomoku/Bounded.lean` 与 `Gomoku/Engine.lean`；
9. `Gomoku/RuleAudit.lean`；
10. `cpp/include/gomoku_solver.hpp` 和 `cpp/src/gomoku_solver.cpp`。

## 12. 不能越过的结论边界

当前可以说：固定 7×7 棋盘、五连、黑先的类型、规则、证书检查器和
Lean/C++ 局部导出链已建立。

当前不能说：

- 7×7 空棋盘已被求解；
- C++ 日志里的 `draw` 已经是 Lean 和棋定理；
- 资源上限耗尽证明了必败或和棋；
- 局部战术证书就是空棋盘的全局证明。

下一阶段若要做完整和棋证明，需要先设计双方结果证书及 soundness，然后再考虑
大型搜索。这不属于当前的 7×7 基础迁移。
