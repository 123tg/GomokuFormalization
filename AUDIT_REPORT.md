# 对抗性审计报告

本文件记录无禁手五子棋形式化项目的反例审计。审计的目的不是证明当前代码“看起来合理”，而是主动寻找能够让定义或定理偏离规则语义的局面。

## 审计基线

- Lean toolchain：`leanprover/lean4:v4.33.0`
- mathlib：`v4.33.0`
- 基线分支：`codex/current-baselin`
- 基线提交：`9291f60 Audit rules and certificate interfaces`
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
29. 为置换表加入 `PositionKey` 精确键：轮次和固定长度 225 的 `Vector Cell` 均被保留，
    `boardKey_eq_iff` 与 `positionKey_eq_iff` 排除了键碰撞；`containsPositionKey_true_iff`
    把数组扫描结果对应到明确的索引见证。
30. `SearchMemo`/`SearchKey` 已接入带状态的有限深度递归参考搜索。键包含剩余深度、目标
   玩家和完整 `PositionKey`；`memoLookup_insert_same` 与 `memoLookup_insert_other_of_ne`
   验证命中和未命中行为；新增 `searchKey_eq_iff` 证明剩余深度、目标方和完整局面任一不同都会
   产生不同键。`searchCandidateTreeMemoized` 返回候选树及更新后的缓存，
   `checkedDepthCertificateForCached_sound` 证明缓存结果仍必须通过局部证书检查才能推出
   `CanForceWin`。缓存内容仍是不可信候选数据，不会直接成为定理。
31. `Gomoku.InteropAudit` 固定了外部搜索器常用的棋子数组根局面适配：
   `positionFromStones` 将数组折叠成 Lean 棋盘，`checkExternalLocalCertificate` 再调用
   当前可信的局部证书检查器。一个 C++ 导出器形状的两节点证书通过并推出局部
   `CanForceWin`；子节点位置故意写错的同形证书被拒绝。这验证了搜索器和 Lean 之间的
   数据边界，但不把棋子数组的历史来源或 C++ 算法纳入可信基础。
32. 对 `origin/feature/cpp-vcf-search` 的隔离实测已完成：C++ 单元测试通过，
   `immediate_win`、`opponent_fork` 和 `open_four_vcf` 三个样例均生成证书，且生成的
   Lean 文件在当前主线下全部编译通过。详细命令、输出和限制见
   `TEAM_SEARCHER_COMPATIBILITY.md`；这确认了接口兼容性，但仍不是全局先手必胜证明。
33. `Gomoku.Engine` 已接入当前主线，提供带节点预算、迭代加深、威胁排序、目标节点选择性
   剪枝和精确局面缓存的 Lean 端候选搜索器。`runCheckedEngine_sound` 明确规定只有通过
   `checkLocalCertificateAt` 的结果才能推出 `CanForceWin`；`Gomoku.EngineAudit` 对真实可达的
   一步胜、对手立即胜和节点预算截止分别做了回归。该引擎仍是有限资源候选生成器，不是完整
   15×15 求解器。另证明了 `mem_engineProverCandidateMoves_legal`，确保威胁筛选和宽度截断
   不会把非法坐标送入搜索。
34. 队友 C++ 搜索器生成的 `CppSmoke`、`CppFork` 和 `CppVcf` 三个局部证书已保存到
    `Gomoku/Generated/` 并纳入主库构建；它们分别覆盖一步胜、多个对手应手和连续威胁。
    三个文件均通过当前 Lean 检查器，但根局面是局部样例，不能推出空棋盘黑棋必胜；
    C++ 搜索器源码和运行资源限制仍需单独维护。
35. 对 Lean 端引擎的对手分支增加了显式覆盖定理 `mem_engineCandidateMoves_of_legal`：
    只要着法合法，它就一定出现在对手节点的候选数组中。`Gomoku.EngineAudit` 用只有两个
    空点的双威胁局面验证引擎生成的证书访问两个应手并通过；将其中一个应手删掉后，
    `checkLocalCertificateAt` 明确返回 `false`。这不限制目标方的宽度剪枝，但保证剪枝不会
    被误用于对手的全称分支。
36. 队友 C++ 搜索器新增 `reachable_immediate.txt` 样例并生成 `CppReachable.lean`：
    根局面由黑白双方各四手的合法历史构造。`InteropAudit` 用有限位置比较器证明该数组
    根局面与 `auditReachableImmediatePosition` 相同，再复用 `Reachable` 定理；生成证书仍
    由 `checkLocalCertificateAt` 独立检查。这是第一个同时具备“外部生成”和“规则层可达性”
    连接的回归，但仍只是一步局部胜势。
37. 队友 C++ 搜索器新增 `reachable_double_threat.txt` 样例并生成 `CppReachableDoubleThreat.lean`：
    根局面由 17 手合法交替历史构造，黑棋有两条独立四连，白棋轮到行动。Lean 检查了生成的 417
    节点证书，并分别执行了合法白棋应手数与证书应手数的回归断言，二者均为 208；故意删除一个
    应手后，`checkLocalCertificateAt` 返回 `false`。这证明了当前接口能承接“真实可达双威胁”的
    局部证书，但不扩展为从空棋盘开始的全局结论。
38. 新增 `Gomoku.MutationAudit` 作为规则变异审查模块。它不修改正式定义，而是定义四个故意
    错误的替代规则，并由 Lean 具体证明：六连会被“恰好五子”错误规则漏掉，竖线会被“只查横线”
    错误规则漏掉，边界四子会被“出界即开放”错误规则误报为活四，终局后的空点会被“忽略终局”
    错误规则误报为合法。该模块已加入 `Gomoku.lean`，随主库构建。
39. 规则层新增 `Position.reachable_winner_turn`，将“终局赢家必须是最后落子者”从口头约定
    提升为正式不变量；`RuleAudit` 用真实可达黑胜和白胜历史分别回归，证明赢家后的轮次一定
    属于另一方。这一结论可用于审查外部搜索器导入的终局节点。

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

1. 把当前逐局面重算的立即胜着/强制防守分组升级为增量威胁缓存；
2. 为已有硬条目上限的哈希置换表增加替换/淘汰策略，并让生成证书共享重复子树；
3. 增量维护空点数和终局信息；
4. 扩展现有 C++ 有界 VCF，加入 VCT、并行和更大局面基准，只把生成的 Lean
   `CompactCertificate` 导入可信侧。

快速终局路径本身不改变可信边界：搜索器可用 `createsFiveFast` 排序或剪枝，但导入的
证书仍由 `checkNodeAt`/`checkCertificate` 重新计算并验证。后续若加入增量缓存，必须为
缓存更新与 `hasAtLeastFive`、`WinningCells` 的对应关系增加独立定理和回归测试。

### A8：递归搜索缓存状态（已修正）

基础 `SearchMemo` 已能由递归搜索携带；新增 `Gomoku.Engine` 又把生产型试验入口升级为
`Std.HashMap EngineSearchKey (Option CandidateTree)`。`EngineSearchKey` 保留“完整搜索配置 +
剩余深度 + 目标方 + 完整局面”，并把 225 格对象向量压缩为轮次和双方共八个 `UInt64` 占位字；根棋盘
只扫描一次，递归落子增量更新。哈希表命中仍做精确键比较。引擎明确区分找到候选、完整深度内未找到和节点
预算截断三种结果，预算截断不会写入负向缓存。缓存中的正向树可能来自不可信搜索状态，
因此 `runCheckedEngine` 仍会把它编译为紧凑证书并调用 `checkLocalCertificateAt`；只有检查
通过后，`runCheckedEngine_sound` 才推出 `CanForceWin`。第二轮优化增加 `maxMemoEntries`
硬写入上限；饱和时跳过新键并统计 `memoStoreSkips`，但尚无替换/淘汰策略。
`EngineCacheLookup` 还明确区分未命中、已搜索失败和已找到候选树，避免诊断上混淆。目标方节点会
优先并剪枝到立即胜着或强制防守点，也可用 `maxProverMoves` 做选择性宽度限制；对手节点仍
完整枚举合法应手。一步成五直接构造终局叶子，最终仍由同一检查器复核。选择性宽度可能
漏解，所以受限搜索的 `notFound` 不是不可胜证明。紧凑键边界回归验证增量编码与重新扫描
结果一致；20,000 次一步子键构造与哈希的原生微基准从约 2.79–2.82 秒降到
0.037–0.039 秒，约快 72–75 倍，但该数字不代表端到端搜索性能或实际内存降幅。即使搜索器键实现有缺陷，候选树
仍必须通过独立证书检查。剩余性能问题是终局和
威胁信息尚未增量维护、证书树尚未做 DAG 共享，以及完整 15×15 搜索规模仍远超常规构建测试。

### A9：C++ 搜索器与当前证书格式（新增）

`cpp/gomoku_solver` 已建立外部搜索原型，但没有修改 `CompactCertificate` 或可信检查器。
C++ 使用双方 bitboard、增量 Zobrist 哈希和迭代深度 DFPN；置换表键同时保留完整双方
bitboard、轮次、目标方和剩余深度，所以 Zobrist 碰撞只影响哈希桶，不会把不同局面合并。
节点预算、置换表容量和证书节点容量分别产生独立状态。目标方可做强制着法剪枝和选择性
宽度限制；对手节点不使用宽度剪枝，输出的 `opponentMoves` 仍列出全部合法应手。

新增的 VCF 预搜索有独立深度和节点预算，只识别立即胜与连续冲四链。单一胜点时递归检查
唯一有效封堵，至少两个胜点时利用“一手最多占一个点”结束探测；若防守方有立即胜着则拒绝
该攻击候选。探测结果只把一个目标方着法移到 DFPN 候选首位，预算耗尽不会终止 DFPN。
同时修正了 DFPN 在多个子节点 proof/disproof 数并列时的过早退出：现在依据被选子节点自身
是否变化判断进展。开放四回归中，启用 VCF 时展开 7 个 DFPN 节点，关闭或耗尽 VCF 时展开
13 个节点，三种情况最终都得到同一六节点证明。

搜索器、C++ 规则实现和导出器全部是不可信组件。当前回归让 C++ 分别生成两节点立即胜
证书、五节点对手全应手证书和六节点开放四 VCF 证书；`Gomoku.Generated.CppSmoke`、
`Gomoku.Generated.CppFork` 与 `Gomoku.Generated.CppVcf` 随后调用未改动的
`checkLocalCertificateAt`，并仅通过
`local_certificate_at_sound` 得到 `CanForceWin`。因此错误坐标、错误轮次、遗漏应手、
错误子局面或错误终局仍会被 Lean 拒绝。

当前不足包括：VCF 尚未扩展到 VCT/开放三威胁空间；没有多线程、置换表淘汰和证书 DAG
共享；根棋盘仍以 Lean 落子数组导出；示例检查为与仓库回归一致而使用 `native_decide`，
会信任 Lean 原生编译执行路径。核心 soundness 定理本身仍不依赖 C++ 或 `native_decide`，
但真实大证书在最终可信度和构建成本上仍需单独选择检查执行方式。

### A10：带缓存的参考递归搜索（已完成，仍非高性能求解器）

`SearchMemo` 现在已经接入有限深度递归搜索。`searchCandidateTreeMemoized` 返回候选树和
搜索过程中学习到的新缓存；缓存命中直接复用同一键对应的结果，未命中则递归计算并把结果写回缓存。
`searchCandidateTree` 保留为空缓存的兼容入口，`searchCandidateTreeCached` 允许调用者提供已有缓存。

缓存仍然只保存不可信的 `CandidateTree`。无论结果来自递归计算还是缓存命中，
`checkedDepthCertificateForCached` 都会重新编译并交给 `checkLocalCertificateAt`；因此缓存不会扩大
可信基础。现有 `memoLookup_insert_same`、`memoLookup_insert_other_of_ne`、命中/未命中引理，
以及 SearchAudit 中的真实局面、错误目标和恶意候选树测试，固定了当前边界。

尚未完成的是性能和更强语义层：缓存键无碰撞已经由完整局面键保证，但还需要测量命中率，
证明带缓存和空缓存搜索在所有结果上的更强等价关系，并加入增量威胁/终局信息后再尝试更大局面。

### A11：有限深度搜索结果的状态区分（已完成）

`checkedDepthCertificateFor` 适合给程序使用，但它把“没有生成候选树”和“生成的证书没有通过
检查”都压成 `none`。本轮在 `Gomoku.Search` 中新增 `CheckedDepthResult` 与
`checkedDepthResultFor`，明确返回三种状态：

- `noCandidate`：搜索器在给定燃料下没有生成候选策略树；
- `rejected certificate`：搜索器生成了候选证书，但 Lean 检查器拒绝了它；
- `accepted certificate`：候选证书通过了局部根、节点、边、终局和对手应对覆盖检查。

`checkedDepthResultFor_accepted_iff`、`checkedDepthResultFor_noCandidate_iff` 和
`checkedDepthResultFor_rejected_iff` 分别刻画三种结果；只有 `accepted` 分支有
`checkedDepthResultFor_sound`，它通过已有的
`checkedDepthCertificateFor_sound` 和 `local_certificate_at_sound` 得到 `CanForceWin`。
因此，`noCandidate` 只说明当前搜索资源或深度没有给出证据，不能解释成目标方不存在必胜策略。

`Gomoku.SearchAudit` 增加了搜索和缓存回归：

1. 黑白双方各走四手后，黑棋有一步合法胜着；深度 1 参考搜索返回 `accepted`，并由 Lean
   证明该局面 `CanForceWin`。
2. 一条合法交替历史使白棋在其回合拥有立即胜着；以黑棋为目标的深度 1 搜索返回
   `noCandidate`，普通 Option 接口返回 `none`。这验证了搜索器不会忽略对手的立即胜利分支。
3. 空缓存搜索会返回学习到的缓存；错误目标、错误深度和错误局面的缓存键不会被复用；正确键下的
   恶意候选树即使命中缓存也会被证书检查器拒绝。

4. `Gomoku.Tactics` 新增颜色无关的 `straightOpenFour_immediate` 和
   `singleOpenFour_forces_win_any_player`：白棋直线活四样例也通过了同一套立即胜和博弈语义证明，
   因此局部定理不再只对黑棋可复用。

这些回归仍然是局部/有限深度测试，不是从空棋盘开始的全局证明，也不替代外部 C++ 搜索器的性能测试。

### A12：引擎对手分支的完整覆盖（已完成）

`engineCandidateMoves` 只改变合法着法的排列顺序，因此 `mem_engineCandidateMoves_of_legal`
给出了对手节点的覆盖保证：任何满足 `legalMove s c` 的着法都出现在候选数组中。目标方一侧的
`engineProverCandidateMoves` 可以按立即胜着、必须防守着法和宽度预算进行选择性剪枝；这会使搜索
结果变得不完备，但不会让通过证书的结论变得不可靠。

`Gomoku.EngineAudit` 在人工构造的双威胁局面中检查了两个白棋分支，并把漏掉一个分支的证书作为
反例。当前还没有证明剪枝搜索与未剪枝搜索在所有成功结果上的完备性等价，也没有进行大规模
局面性能评测。

### A13：有限深度语义与空位数上界（已完成）

新增的 `Gomoku.Bounded` 把“最多再走多少步”直接定义成可执行的布尔语义，且只使用
`candidateMovesFast` 所代表的合法着法。`boundedCanForceWin_sound` 证明布尔结果为 `true`
时一定能构造 `CanForceWin`；反方向的 `canForceWin_bounded_complete` 以每次合法落子恰好
减少一个空点为归纳依据，证明任何 `CanForceWin s p` 都会在
`Board.emptyCount s.board + 1` 深度内返回 `true`。因此：

- 固定深度的 `false` 只表示深度不足，不能解释为目标方必败；
- `boundedCanForceWin_mono` 和 `boundedCanForceWin_mono_of_le` 证明如果某个深度返回 `true`，
  任意更大深度仍返回 `true`，为迭代加深提供了数学依据；
- `boundedCanForceWin_terminal_iff` 和 `boundedCanForceWin_false_of_terminal_ne` 统一刻画
  终局节点，保证和棋或对手胜利不会因增加燃料而变成目标方胜利；
- 在空位数加一的充分深度上，有限语义与 `CanForceWin` 完全等价；
- 该定理是数学基准，不声称 15×15 的计算在实际资源内可完成。

`Gomoku.BoundedAudit` 用两空点双威胁局面验证深度 0 返回 `false`、深度 2 和 3 返回 `true`，
并把同一局面的有限语义与候选树搜索的 `accepted` 状态进行对照；终局和棋及对手已有立即
胜着的局面在不同燃料下均保持 `false`。它没有把有限计算结果直接提升为全局定理，仍然
要求候选证书通过现有检查器。

## 审计完成标准

- 每个已发现问题都有明确的修复状态。
- 每个反例都有 Lean 回归测试。
- 对定义做临时错误变异时，至少一个测试必然失败。
- 未解决的语义问题不得被更高层战术定理隐藏。
- 审计报告与源码 API 保持同步。

## 本轮主线审查（2026-08-27）

本轮在不改动工作树中既有 `Gomoku/Search.lean` 修改的前提下，新增了
`Gomoku/RuleAudit.lean` 和 `BASELINE_STATUS.md`。新增回归覆盖四方向五连、边界长连、
满盘无五连和棋、首着与其他点保持、错误轮次/数量不可达，以及和棋、非终局、对手胜利、
非法落子和错误轮次证书拒绝。

规则层新增 `Position.terminal_draw_iff`，把和棋精确刻画为“双方都没有至少五连且棋盘已满”。
博弈层新增 `canForceWin_terminal_iff` 与 `not_canForceWin_of_terminal_ne`，明确禁止把
和棋或对手胜利局面当作目标方的强制胜利。满盘着色的昂贵判定只在一个命名定理中执行，
其余测试复用该定理，避免回归构建重复扫描棋盘。

全工程使用已安装的 Lean 4.33.0 工具链直接运行 `lake build` 已通过（8732 个目标）。
PowerShell 中通过 elan 包装器运行时会额外尝试联网检查更新；网络不可用时会在真正构建前失败，
这不是 Lean 源码错误。输出仍有既有的文件头、长行和测试模块使用 `native_decide` 警告；
未发现 `sorry`、`admit`、`axiom` 或 `unsafe`。这些警告不影响本轮 Lean 类型检查，
但后续可以作为代码清理任务处理。

审查过程中发现并修正了一个反例构造错误：原“对手立即获胜”棋盘因周期着色填满其余位置，
实际上已经终局；现改为只含四枚白子和一个空获胜端点，非终局前提与测试语义一致。
此外，一步胜回归明确检查了合法胜着、落子后立即终局、轮次切换、棋子计数，以及终局后
所有后续着法均不合法。

博弈层新增 `canForceWin_target_iff` 和 `canForceWin_opponent_iff`。前者把目标方节点严格刻画为
“存在一个合法且保持胜势的子局面”，后者把对手节点严格刻画为“每个合法应对都保持胜势”。
这两条定理与立即威胁反例一起，直接验证了存在分支和全称分支没有混淆。

### 本轮证书检查器补充审查

新增的正确证书由一个黑棋着法节点和一个黑胜终局节点组成，
`checkLocalCertificateAt` 接受它，`local_certificate_at_sound` 将其转换为
`CanForceWin`。同时增加了 `compact_certificate_sound` 的通用使用示例：只有从空棋盘开始、
目标为黑棋且通过全局检查的证书，才能得到 `CanForceWin initialPosition .black`。

新增错误证书覆盖：和棋伪装成黑胜、白胜伪装成黑胜、根索引越界、自循环、后向引用，
以及在黑棋轮次伪造对手节点。它们均被拒绝。已有 `Gomoku.Adversarial` 还覆盖缺少合法应对、
越界子引用、子局面不匹配、错误终局标签和全局根局面错误。

计划中“含和棋叶子的正确证书”需要作语义澄清：本项目检查的是“目标方必胜证书”，
而不是任意完整对局树；对手只要能走到和棋，该分支就足以否定目标方必胜。因此正确的
必胜证书不可能含有可达和棋叶。本项目保留和棋叶的拒绝测试，这正是应有行为。

## 本轮追加审查（2026-08-27）

### 可达历史回放

规则层新增了 `Position.playMoves`、`Position.LegalMoveSequence` 和
`reachable_playMoves`。它们把“每一步都合法”与“最终局面来自空棋盘”明确连接起来。
`auditDrawPosition` 不再是任意写入的满盘棋盘，而是 `auditDrawMoves` 经过 225 步合法
交替落子的回放结果。Lean 检查了整条序列、最终棋盘的满盘性质以及双方均无五连，因而
该局面是一个真正可达的和棋例子。另有九步交替历史形成真实可达的黑棋五连，验证终局后
不能继续落子。

### 规则边界与终局优先级

新增了右边界横向五连、上边界斜线五连和含一个空格的“伪五连”反例。还构造了同时含
黑、白五连的任意棋盘，以及满盘同时含黑五连的棋盘；测试固定了当前总规则的优先级：
先返回黑胜，再检查白胜，最后才返回和棋。可达局面不会触发这些非法组合，但总函数的
行为必须明确，不能靠注释猜测。

### 证书检查器隔离性

局部证书审查现在分别测试：根局面不匹配、prover 非法占点、prover 错误轮次、越界引用、
单一空点对手节点的轮次错误，以及 prover/opponent 子节点局面与 `play` 结果不匹配。
其中直接调用 `checkNode` 或 `checkNodeAt` 的测试尽量只破坏一个检查条件，避免某个测试
因为同时存在第二个错误而失去审计价值。所有这些反例都由 `native_decide` 验证为拒绝。

### 仍需注意

`native_decide` 适合把具体反例执行一遍，但它不是核心 soundness 证明的替代品。真正的
可靠性链仍是 `checkNodeAt_*_iff`、`compact_reify_at` 和 `compact_certificate_sound`。
当前没有从空棋盘开始的完整证书，因此本报告不声称 `initial_black_wins` 已经成立。

### 博弈状态双向刻画与共享子树

规则层现在同时提供 `terminal_none_iff` 和 `terminal_ne_none_iff`，因此“非终局”与“终局”
之间的转换不再依赖调用者手工展开 `terminal` 的条件分支。审计还增加了一个符合交替
历史的白棋立即胜着局面，验证对手威胁定理不依赖不可能的棋子计数。

证书审计加入共享子树正例：一个 `opponentMoves` 节点可以让重复的应手引用同一个子树，
但每条边仍须满足严格递增的节点编号和 `play` 后局面匹配，且全部合法应手仍须被覆盖。
这明确了 DAG 证书与树语义之间的边界；重复应手不是遗漏分支的方式。

### 空位数的序列不变量

`playMoves_emptyCount_add_length` 证明任意合法着法序列都满足：最终空位数加上序列长度
等于初始空位数。满盘和棋例调用该定理并单独执行检查，确认 225 步回放后空位数为零；
这比只检查最终棋盘的 `full` 谓词更直接地审计了“每一步恰好占用一个空点”。

## 本轮几何补充（2026-08-29）

为补齐活四到立即胜点之间的几何桥接，本轮在 `Gomoku.Geometry` 增加了两个不依赖棋盘内容
的引理：`step_compose` 证明同一方向的两个合法步进可以复合，
`step_left_endpoint_shift` 证明从左端点重新编号时五个位置的坐标保持一致；同时，
`step_neg_one_ne_four` 排除了两个端点落到同一坐标的可能性。

在 `Gomoku.Tactics` 中，原有的 `straightOpenFour_has_winningCell` 接口保持不变，内部补充了
`straightOpenFour_left_has_winningCell` 和 `straightOpenFour_right_has_winningCell`，并由
`straightOpenFour_has_two_distinct_winningCells` 汇总为正式定理：每条直线型活四的两个端点
都是不同的 `WinningCells`。`Gomoku.PatternAudit` 对中心横向活四增加了定理级回归。

这项补充修复了“只证明至少一个端点可赢、但没有证明两个端点不同”的几何缺口；它仍然只说明
局部活四有两个立即胜点，不涉及轮到谁、对手是否已有更快胜势，也不构成 15×15 全局必胜结论。

## 本轮有限语义桥接（2026-08-29）

`Gomoku.Bounded` 新增 `checkedDepthCertificateFor_bounded` 和
`checkedDepthCertificateForCached_bounded`。它们先使用已有的证书检查可靠性定理得到
`CanForceWin`，再由 `canForceWin_bounded_complete` 和深度单调性推出：在
`Board.emptyCount position.board + 1 ≤ fuel` 时，独立的 `boundedCanForceWin fuel`
也返回 `true`。这把“候选证书通过检查”和“完整有限 AND/OR 参考语义”连接起来，同时保留
两者职责差异：较浅的候选搜索可能因深度或启发式而返回 `none`，而任意深度的候选搜索与
有限语义的完备等价仍是后续工作。`BoundedAudit` 增加了普通缓存和空缓存两条具体回归；
原有两空点局面的深度 2 成功测试仍保留，因为 `emptyCount + 1` 是保守充分上界而不是最小深度。

## 本轮引擎缓存审计（2026-08-29）

审查发现 `EngineMemo` 原先只按局面、目标和剩余深度索引，但引擎配置会改变候选搜索：
例如选择性宽度限制可能返回 `none`，而完整候选配置仍能找到证书。若直接复用这种失败结果，
会产生不必要的假阴性。现已引入 `EngineSearchKey`，在查询键之外保存完整 `EngineConfig`，
并让递归引擎按该键读写缓存。`EngineAudit` 构造了一个选择性配置下的失败条目，验证普通
配置不会命中它而会重新找到一步胜证书。该修复保护的是搜索结果的配置一致性；证书的数学
可靠性仍然只来自 `checkLocalCertificateAt` 和 `runCheckedEngine_sound`。

在同一审查中又把缓存查询的三种情况显式化为 `EngineCacheLookup`：`miss`（没有查过）、
`notFound`（已在当前配置/深度下搜索但没有候选树）和 `found tree`（缓存了候选树）。
`EngineAudit` 对三种状态分别做了回归测试。这样调试输出不会把“没有缓存”误读成“搜索失败”，
也不会把缓存的 `found` 结果绕过证书检查器；这项分类仍不改变搜索器本身不完备的事实。

## 本轮外部输入审查（2026-08-29）

`boardFromStones` 的基础适配会按数组顺序写入棋盘，若数组重复某个坐标，后一次记录会覆盖前一次。
这对任意局部根是兼容行为，但不能作为导出器数据质量保证。本轮新增
`externalStoneCoordsNodup` 和 `checkExternalLocalCertificateStrict`：严格入口先用可执行的去重长度
检查拒绝重复坐标，再复用原有局部证书检查器。`InteropAudit` 同时保留同一重复数组在普通入口下
通过、严格入口下拒绝的反例，确认两种接口的信任边界没有混淆。

## 本轮增量终局接口（2026-08-29）

搜索引擎原先在不同位置分别检查“快速成五”和完整 `terminal`。本轮新增
`terminalAfterMoveFast`，将一次候选着法的四种结果统一为一个可执行分类：非法着法返回
`none`，合法落子成五返回当前落子方胜利，合法落子填满棋盘且无人胜返回和棋，其余情况
返回 `none`。这不是把任意棋盘都当成合法历史；它只是一个总函数，合法性和非终局前提
仍由调用者或证书检查器负责。

定理 `terminalAfterMoveFast_eq_terminal` 证明：若父局面非终局且着法合法，快速分类与
完整规则 `terminal (play s m)` 相等。证明显式排除了父局面的旧胜势、另一方在落子后
凭空获得胜势以及“成五”和“和棋”同时发生的歧义。引擎的目标方和对手立即胜短路现在
统一调用该接口，减少了搜索器与规则层之间的重复判断。

`Gomoku.TerminalAudit` 增加四类回归：一步成五、最后一格和棋、终局后非法着法，以及
两个正常非终局局面上的快速/完整终局结果相等。它们验证了这次接口重构没有改变证书
检查器的信任边界，也没有把资源不足的搜索结果解释成必败。

引擎的 `EngineStats` 现在另外记录 `terminalChecks` 和 `candidateMoves`。前者统计缓存
未命中后实际做的局面终局分类，后者统计交给递归扫描器的候选着法总数；缓存命中不会
虚增这两个数字。`EngineAudit` 在双应手局面上验证成功搜索的两个计数均为正。它们是
性能和调试指标，不参与 `runCheckedEngine_sound`，也不把“访问了很多节点”误作数学证明。

限制：该缓存目前没有改写 `Gomoku.Engine` 的默认搜索路径，也没有提供运行时加速数字。
因此本审查只确认“如果以后接入，缓存值不会改变数学结果”，不声称搜索器已经具备完整
增量威胁维护或能够解决 15×15 全局棋局。
