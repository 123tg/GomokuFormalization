# 对抗性审计报告

本文件记录无禁手五子棋形式化项目的反例审计。审计的目的不是证明当前代码“看起来合理”，而是主动寻找能够让定义或定理偏离规则语义的局面。

## 审计基线

- Lean toolchain：`leanprover/lean4:v4.33.0`
- mathlib：`v4.33.0`
- 基线提交：`main` 分支当前提交
- 基线构建：`lake build` 成功
- 目标棋盘：固定 15×15
- 信任策略：关键定理不依赖 `native_decide`；测试文件可以使用它

## 已检查项目

| 区域 | 检查内容 | 当前结论 |
| --- | --- | --- |
| 棋盘更新 | 落子点更新、其他点保持不变、空点计数 | 已有定理，继续补负例 |
| 合法着法 | 终局、占点和轮次限制 | `legalMove` 正确拒绝；`play` 本身是无检查的原始更新，必须由调用者提供合法性 |
| 终局 | 五连、长连、满盘和棋 | 可达局面规则一致；任意同时含双方五连的位置采用黑胜优先，须保持文档说明 |
| 几何 | 四方向、边界、活三和活四 | 直线模式、`MaximalRun` 和可比较重叠起点唯一性已证明；断三/跳四以独立模式加入 |
| 战术谓词 | 活三/活四是否误把非法 `play` 当作合法落子 | 已拆分纯几何谓词与要求 `legalMove` 的公开谓词 |
| 战术定理 | 单活四的对手无立即胜着前提 | 当前证明不使用 `hnoWhite`；该前提是业务约束而非数学必要条件，应拆成最小定理和安全包装定理 |
| 博弈语义 | 目标胜、对手胜、和棋、对手分支 | `ForceWin` 结构正确；策略树与 `CanForceWin` 已有双向 `Nonempty` 等价，非终局合法着法存在性已证明 |
| 紧凑证书 | 根、边、索引、覆盖、循环 | 已完成结构检查、命题化引理和到 `CertificateTree` 的可信重建；尚无真实 15×15 证书 |

双活三的安全条件现在明确区分两个层次：`SafeDoubleOpenThree` 要求第一步后非终局、对手没有立即胜着，并对每个合法防守给出目标方的 `CanForceWin`；更强的
`ImmediateSafeDoubleOpenThree` 才要求每个防守后都有目标方立即胜着。两者都由
`ForceWin` 语义连接到 `CanForceWin`。`Gomoku/Adversarial.lean` 中的十字反例证明，纯几何
`GeometricDoubleOpenThree` 不能自动推出后者；因此不能把“双活三”直接当成完整必胜定理。

为避免把“活三扩展点”和“立即成五点”混为一谈，当前还定义了 `FourExtensionCells`。
`straightOpenThree_has_fourExtension` 证明每个直线活三至少有一个落子后形成四连的
扩展点，`HasDoubleFourThreat` 表示至少有两个这样的点。它是几何活三与
`WinningCells`/`HasDoubleThreat` 之间的中间层，不能单独推出 `CanForceWin`；十字反例
验证了存在多个四连扩展点时立即胜着集合仍可能为空。

博弈接口的审计状态也已更新：`Position.exists_legalMove_of_terminal_none` 证明非终局局面不会因为“无棋可走”而卡住；`defaultStrategy` 只保证返回合法着法。`certificateTree_iff_canForceWin` 证明依赖策略树与 `CanForceWin` 的双向等价，反向构造以 `Nonempty` 命题包装承载，避免从命题直接消去到数据。

## 第一批反例和回归测试

这些反例保存在 `Gomoku/Adversarial.lean`，并随主库构建：

1. 已占据位置不能作为合法着法。
2. 原始 `play` 会覆盖位置，因此任何“某一步产生图形”的谓词都必须明确是否要求合法性。
3. 边界端点不是开放端。
4. 六连仍然满足“至少五连”。
5. 终局位置没有后续合法着法。
6. 错误目标玩家、空根节点和错误证书被拒绝。
7. 两节点合法 `proverMove` 到终局的证书可以通过节点检查并由 `compact_reify_at` 重建策略树。
8. 五节点 `opponentMoves` 证书列出局面的全部两个合法应对，并分别重建为黑棋胜利子树；
9. 同一两空点局面直接满足 `HasDoubleThreat`，并由 `doubleThreat_forces_win` 证明黑棋
   可以强制获胜；这验证了“两个独立立即胜点”到有限博弈语义的连接。
10. 中心交叉局面验证 `doubleThreat_move_forces_win`：合法落子后出现横、竖两个四连
    方向的立即胜点，且非终局、对手无立即胜着时，原局面可强制获胜。
11. 黑棋几何双活三与白棋已有立即胜着可以同时存在；新增通用排除引理，验证
    `SafeDoubleOpenThree` 和 `ImmediateSafeDoubleOpenThree` 都会拒绝该局面。
12. `winningCell_ne_of_hasDoubleThreat` 在两空点局面上验证：无论防守坐标取其中
    一个胜点，都能选出另一个仍为空的胜点；终局保持性和强制性证明现在共同复用该引理。
13. `Gomoku.Search` 的 225 点坐标表、合法候选过滤和首个立即胜着扫描均通过执行测试；
    局部立即胜着候选只通过 `checkNodeAt` 验证，故不会被误认为满足要求空棋盘根的
    全局 `checkCertificate`。
14. `mem_candidateMoves_iff` 将候选数组成员转换为明确命题，并回归验证已占中心不会
    再次出现在白棋候选列表中。
15. `immediateCertificateNodesChecked_sound` 将局部候选证书的两个节点检查连接到
    `CanForceWin`；测试局面通过该定理，而全局 `checkCertificate` 的初始根限制保持不变。
16. `generatedForkCertificate` 由通用两层构造器生成五节点证书，并通过
    `checkLocalCertificate`；`twoPlyImmediateCertificate_sound` 随后推出局部
    `CanForceWin`。这直接回归测试了合法性、覆盖性、严格索引和子局面匹配。
17. `twoPlyCertificateFor` 在同一双威胁局面自动枚举两个合法对手应手，并为每个
    分支找到另一端的立即胜着。
18. 几何双活三与“防守后立即胜着”的强语义被十字局面明确区分。
19. 跳四的三个冻结模式都能通过 `jumpFour_black_immediate` 连接到黑棋立即胜着；
    一个实际跳四局面还回归测试了 `CanForceWin`。
20. `candidateMovesFast` 把终局检查从 225 个单元格过滤谓词中提到位置级别，且
    `mem_candidateMovesFast_iff_mem_candidateMoves` 证明它与参考候选枚举保持相同成员关系；
    两空点局面的深度 2 `checkedDepthCertificateFor` smoke test 通过。
21. `orderedCandidateMoves` 将相邻棋子附近的候选点提前，但通过
    `mem_orderedCandidateMoves_iff` 保证没有丢失任何合法着法；初始局面和中心首着的
    顺序/大小回归测试均通过。
22. `tacticalCandidateMoves` 定义了立即胜着、对手立即胜着防守和安静着法三组候选，
    并保留全部合法点；审计发现逐候选重复计算 `WinningCells` 会造成显著的整盘扫描
    开销，因此实现改为每局面构造一次固定长度 `winningCellsMask`。默认深搜仍保持更轻量的
    立即胜着排序；防守分组作为可选接口保留，不改变证书检查器的 soundness。
23. `coordIndex` 与 `coordAtIndex` 组成经证明的 225 点行主序双射；
    `winningCellsMask_get_iff` 证明掩码直接查询与 `WinningCells` 一致，
    `mem_tacticalCandidateMovesFast_iff` 证明快速防守分组与候选全集一致。掩码目前仍从
    整盘重算，进一步扩展前应加入增量威胁缓存。
24. 紧凑证书的负向回归新增四种变异：遗漏一个合法对手应手、引用越界、子局面与
    着法结果不匹配、终局胜负标签错误；`checkLocalCertificate` 对四者均返回 `false`。
    这组测试与既有的循环引用、错误全局根和空证书拒绝测试共同覆盖证书可信边界。
25. 原 `reachable_not_both_winners` 需要额外的非终局前提，因而没有覆盖刚结束的可达
    局面。现已把“落下另一颜色棋子不会新造本色五连”提升为几何公共引理，并证明
    `play_not_both_winners` 及无额外前提的 `reachable_not_both_winners`；终局优先级
    不再仅靠“正常棋局应该不会双方都赢”的注释解释。
26. 原 `Strategy` 只保证返回合法着法，未形式化“这个具体函数沿全部对手分支获胜”。
    新增 `StrategyRealizes`、`StrategyRealizes.sound` 和规范获胜策略提取；
    `strategyRealizes_iff_canForceWin` 与 `strategyRealizes_iff_certificateTree` 现已把
    策略函数、策略树和归纳博弈语义连接起来。规范策略使用经典选择，只服务于数学
    等价性，不冒充可执行求解算法。
27. `createsFiveFast` 的局部窗口优化已通过四方向和边界回归：横、竖、两种斜线的成五
    着法均返回 `true`，边界窗口不会因起点在 0 而漏检，只有三子且落子后仍不足五子的
    反例返回 `false`。`createsFiveFast_sound`/`createsFiveFast_complete` 给出父局面
    无五连时的双向等价，`createsFiveFast_terminal_iff` 在合法轮次下与完整终局胜负一致。
    这验证了搜索器的局部加速没有改变规则语义，但不代表搜索已达到可处理 15×15 全局
    树的规模。
28. `firstWinningMove` 已从逐候选完整 `terminal` 扫描切换为 `createsFiveFast`；旧实现
    保留为 `firstWinningMoveReference`，并在立即成五样例上执行结果相等回归。
    `immediateWinningMovesFirst_mem_legal` 证明扫描数组中的每个候选都满足当前轮次和
    `legalMove`，`createsFiveFast_terminal_of_immediateCandidate` 再证明快速命中对应
    真实终局胜着。因此该优化只影响不可信搜索器的运行时间，不扩大证书检查器的信任边界。
29. 为后续置换表加入 `PositionKey` 精确键：轮次和固定长度 225 的 `Vector Cell` 均被
    保留，`boardKey_eq_iff` 与 `positionKey_eq_iff` 排除了键碰撞；
    `containsPositionKey_true_iff` 把数组扫描结果对应到明确的索引见证。当前只验证键和
    命中接口，尚未将其用于搜索剪枝，因此不会引入缓存错误传播。
30. 新增 `SearchMemo`/`SearchKey` 缓存适配层。键包含剩余深度、目标玩家和完整
    `PositionKey`；`memoLookup_insert_same` 与 `memoLookup_insert_other_of_ne` 验证命中和
    未命中行为，`checkedDepthCertificateForCached_sound` 证明缓存返回的结果仍必须通过
    局部证书检查才能推出 `CanForceWin`。这一步没有把缓存直接接入递归搜索，也没有把
    缓存内容提升为可信证明。

## 待处理问题

### A1：图形谓词和合法落子语义混合（已修正）

`play` 是数据层原始更新，允许覆盖已有格子；这是为了让 `Board.place` 易于证明而有意采用的设计。审计发现如果把这种原始更新直接用于战术名字，会把非法覆盖误当成合法着法。原接口已按以下方式修正：

```lean
s.turn = p ∧ legalMove s m
```

当前已采用分层接口：

- `GeometricMoveCreatesSingleOpenFour` 和 `GeometricDoubleOpenThree` 保留原始 `play` 后的纯几何含义。
- `MoveCreatesSingleOpenFour` 和 `DoubleOpenThree` 额外要求 `s.turn = p ∧ legalMove s m`。
- 两层谓词都具有可计算的 `Decidable` 实例，反例可以直接进入测试套件。

这样原始 `Board.place` 的覆盖行为仍可用于底层证明，但公开战术接口不会把非法覆盖误当成合法着法。

### A2：单活四定理的前提冗余（已修正）

黑棋当前有直线型活四且轮到黑棋时，可以立即填充一端形成五连；对方是否有立即胜着不影响这一事实，因为对方尚未行动。旧版 `singleOpenFour_forces_win` 保留了 `hnoWhite`，但证明没有使用它。

当前已拆为：

- `singleOpenFour_forces_win_minimal`：最小数学前提；
- `singleOpenFour_forces_win`：保留对手无立即胜着的业务接口，并证明它由前者直接推出。

### A3：规范化见证需要定理保证（部分完成）

目前活三/活四通过 `(起点, 方向)` 过滤得到。已加入 `canonicalRunStart`、
`normalizedStraightOpenThree` 和 `normalizedStraightOpenFour`，并证明开放端条件蕴含规范起点；见证集合已改用规范化谓词。新增 `StartShiftConflict`、`ComparableRunStarts`，并证明当两个起点沿同一段发生可比较正偏移时，直线型活三/活四起点不能重复。分离的同方向模式允许同时存在，不能被这个局部唯一性结论排除。

`MaximalRun` 现在显式表达连续段左右端都不能再延伸；`straightOpenThree_maximalRun` 和
`straightOpenFour_maximalRun` 证明开放三/四都是这种最大段。对一般长度，
`maximalRun_unique_of_comparable` 在 `ComparableRunStarts` 条件下给出起点唯一性；
这仍然有意不排除同方向上的分离段。

断三和跳四当前由 `brokenOpenThree`、`jumpFour` 以有限析取模式表表示。回归测试确认：
模式可识别、不会自动落入 `straightOpenThree`/`straightOpenFour`，且边界封闭端会使模式失败。
`jumpFour_black_immediate` 已把三个跳四析取模式连接到黑棋的立即胜着语义；
`brokenOpenThree_has_fourExtension` 已把两个断三析取模式连接到“填补内部缺口后形成
四连扩展点”的中间语义；`OpenFourExtensionCells`、
`straightOpenFour_has_winningCell` 和 `openFourExtension_has_winningCell` 进一步
证明方向性开放四至少有一个立即成五点。新增 `BrokenOpenThreeMove` 和
`SafeBrokenOpenThree`：前者要求当前回合、合法着法和方向性断三扩展，后者要求对手
无立即胜着并为每个合法防守提供 `CanForceWin`；`safeBrokenOpenThree_forces_win`
将该安全谓词连接到 `ForceWin`。新增 `ImmediateSafeBrokenOpenThree`，并证明它
蕴含 `SafeBrokenOpenThree` 和 `CanForceWin`。这仍然不是几何断三自动必胜定理。
审计测试还加入了 `forcedBrokenThreePosition`：该局面只有内部缺口和两个端点为空，
黑填缺口后白只有两个合法应对；Lean 直接验证 `ImmediateSafeBrokenOpenThree`，
再由安全特例得到 `CanForceWin`。这是局部语义回归证书，不是全局 15×15 结论。

### A4：双活三的几何条件不能冒充完整强制性（已修正接口）

审计构造了一个十字局面：黑棋落在中心后同时产生横向和纵向直线型活三，
但白棋可以先堵住一个端点；这说明几何上的两个活三不等于“对手防守后黑棋
立即成五”。因此原先过强的语义被拆分为：

- `SafeDoubleOpenThree`：防守后仍有 `CanForceWin`，允许多回合继续证明；
- `ImmediateSafeDoubleOpenThree`：防守后已有 `HasImmediateWin`，是更强的特例。

已证明 `ImmediateSafeDoubleOpenThree` 蕴含 `SafeDoubleOpenThree`，并保留两者的
`CanForceWin` 推论。几何到安全谓词的充分性仍未证明，断三、跳四和反击四也
没有被隐式纳入。新增的 `FourExtensionCells`/`HasDoubleFourThreat` 只提供严格的
中间威胁语义，不改变这一审计结论。

### A5：紧凑证书 soundness（已修正）

该问题已经完成可信转换。当前实现包含：

- `allRefsValid_true_iff`、`allMovesLegal_true_iff` 和
  `allLegalMovesCovered_true_iff`，把数组布尔检查转换为明确的命题；
- `checkNodeAt_terminal_iff`、`checkNodeAt_proverMove_iff` 和
  `checkNodeAt_opponentMoves_iff`，把节点检查转换为终局、合法着法、引用顺序和完整应对覆盖；
- `mapIdx_all_true_iff` 和 `checkCertificate_nodes_checked`，把全局 `mapIdx.all` 检查转换为每个节点的命题事实；
- `compact_reify_at`，以 `nodes.size - index` 为严格下降量，在 Lean 内重建依赖类型
  `CertificateTree`；
- `compact_certificate_sound`，从 `checkCertificate c = true` 推出
  `CanForceWin initialPosition .black`。

这并不等于已经证明真实 15×15 先手必胜：目前还没有可存储、可通过检查的真实全局策略证书。

### A6：搜索器到局部证书的边界（新增）

已增加 `checkLocalCertificate`，它复用全局证书的所有节点、边、索引和
对手分支覆盖检查，但不强制根节点是空棋盘黑先。这一差异是有意的：局部
战术证书必须能够以任意局面为根，而 `checkCertificate` 仍专门服务于最终
的 `initial_black_wins`。

`twoPlyImmediateCertificate` 可由有限应手表生成两层证书，
`immediateResponseTable` 会枚举全部合法对手应手，并为每一分支调用
`firstWinningMove` 寻找目标方的立即胜着。通过检查的局部证书由
`local_certificate_sound`/`twoPlyImmediateCertificate_sound` 连接到
`CanForceWin`。测试中还验证了完整双威胁局面和自动应手表。

当前限制仍然明确：若某个对手应手没有立即胜着，二层生成器返回 `none`；
这不是失败的数学证明，而只是搜索深度不足，后续必须递归生成更深的
`CompactCertificate`，直到所有分支到达终局叶子。

### A7：有限深度搜索的执行性能（已记录，未视为 soundness 缺陷）

`searchCandidateTree` 的递归定义已经通过 Lean 类型检查，并且其结果始终要经过
`checkLocalCertificateAt`。最初对一个只有两个空点的局部局面直接执行深度搜索时，
每个节点都会反复扫描完整的 225 点坐标表并重算终局，导致回归耗时过长。加入
`candidateMovesFast`、把终局检查提到棋盘级别后，深度 2 smoke test 已恢复并通过；
它仍只覆盖这个很小的局面，不能代表一般 15×15 搜索已经可行。

这不是可信证明链的漏洞：搜索器只是产生候选树，证书检查器仍会重新验证每条边、
所有合法对手应手、严格递增索引和终局标签。当前同时保留固定五节点候选树测试和两空点
深度 2 smoke test；前者验证编译器和检查器接口，后者验证递归搜索的最小闭环。扩展
自动深搜前仍应依次完成：

1. 在当前邻近着法和立即胜着优先之上，用增量威胁缓存实现必须防守优先的排序；
2. 局面键和置换表，避免重复扫描相同子局面；
3. 增量维护空点数和终局信息；
4. 将大规模搜索移到外部程序，只把生成的 Lean `CompactCertificate` 导入可信侧。

快速终局路径本身不改变可信边界：搜索器可用 `createsFiveFast` 排序或剪枝，但导入的
证书仍由 `checkNodeAt`/`checkCertificate` 重新计算并验证。后续若加入增量缓存，必须为
缓存更新与 `hasAtLeastFive`、`WinningCells` 的对应关系增加独立定理和回归测试。

### A8：缓存尚未成为递归搜索状态（已记录，未视为 soundness 缺陷）

`SearchMemo` 目前是安全的适配层：它能按“剩余深度 + 目标方 + 完整局面”查找候选树，
命中结果随后仍交给证书检查器。现有 `searchCandidateTree` 仍是原始的无缓存递归函数，
所以尚未获得实际的重复局面剪枝收益；下一步需要实现返回“结果 + 新缓存”的递归搜索，
并证明命中路径与未命中路径产生相同的候选树/证书语义。

## 审计完成标准

- 每个已发现问题都有明确的修复状态。
- 每个反例都有 Lean 回归测试。
- 对定义做临时错误变异时，至少一个测试必然失败。
- 未解决的语义问题不得被更高层战术定理隐藏。
- 审计报告与源码 API 保持同步。
