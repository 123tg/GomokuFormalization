# 7×7 无禁手五子棋形式化

本项目使用 Lean 4 形式化固定规则的五子棋：

```text
board size = 7 × 7
win length = 5
first player = Black
```

无禁手；横、竖、两种对角线上连续至少五子即胜，因此长连也算获胜。
无人获胜且棋盘填满时为和棋。

详细的项目结构见 [`PROJECT_GUIDE.md`](PROJECT_GUIDE.md)，搜索器与 Lean
检查器协议见 [`SEARCHER_INTERFACE.md`](SEARCHER_INTERFACE.md)。

## 主要模块

- `Gomoku.Basic`：`Player`、`Cell`、`Coord = Fin 7 × Fin 7`、`Board`。
- `Gomoku.Geometry`：7×7 边界内的四个方向、连续棋形与开放端。
- `Gomoku.Rules`：`Position`、黑先初始局面、`legalMove`、`play`、`terminal`。
- `Gomoku.Game`：策略与 `CanForceWin` 博弈语义。
- `Gomoku.Tactics`：立即胜着、活三、活四和双威胁定义及定理。
- `Gomoku.Certificate`：`CompactCertificate`、全局/局部检查器和 soundness 定理。
- `Gomoku.Stealing`：纯策略级证明——策略偷换（strategy stealing），从空棋盘证明
  `BlackCanPreventWhiteWin initialPosition`（先手至少和棋），不依赖搜索证书。
- `Gomoku.Search`：49 点行主序坐标、候选生成、有限深度搜索与证书转换。
- `Gomoku.Bounded`：可执行的有界 AND/OR 博弈语义。
- `Gomoku.Engine`：带资源上限、缓存和威胁排序的 Lean 候选搜索引擎。
- `Gomoku.RuleAudit`：精简的 7×7 验收测试与证书反例。
- `Gomoku.Generated.CppSmoke`：C++ 导出、Lean 重新检查的最小局部证书。
- `cpp/`：不可信的 C++17 DFPN/VCF 候选搜索器和 Lean 源码导出器。

## 关键约定

Lean 与 C++ 都使用：

```text
index = y * 7 + x
x = index % 7
y = index / 7
```

其中 `x` 是列，`y` 是行。`allCoords` 不重不漏地枚举 49 个坐标。

`CompactCertificate` 不信任搜索器的胜负标签。Lean 会重新检查根局面、轮次、
合法着、子局面、终局结果、节点编号与对手全部合法应手。有限搜索返回
`none`、`depthLimit` 或 `nodeLimit` 只表示本次没找到证书，不是和棋定理。

当前没有导入从 7×7 空棋盘开始的完整策略证书，因此项目不宣称
`initial_black_wins` 或完整和棋定理。但 `Gomoku.Stealing` 通过纯策略级
（策略偷换）论证证明了空棋盘上黑方（先手）能阻止白方获胜：
`BlackCanPreventWhiteWin initialPosition`（先手至少和棋，不等同于先手必胜）。

旧的 5×5--8×8 参数化实验、结果日志和重复 smoke 脚本已删除；仓库只保留
固定 7×7 主程序及其最小验收测试。

## 构建

```powershell
lake build
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```
