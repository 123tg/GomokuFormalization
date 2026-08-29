# 当前基线状态表

本文件记录第一轮主线审查完成后的工程状态。它不是最终成果宣称，而是帮助团队区分“已经由 Lean 证明”“只是可执行检查”和“仍然是计划”的工作台账。

## 构建基线

| 项目 | 当前值 |
|---|---|
| 工作目录 | `D:\LeanProjects` |
| 分支 | `codex/current-baselin`（对应内容已由用户合并到 GitHub `main`；本地仍保留该工作分支） |
| 基线提交 | `9291f60 Audit rules and certificate interfaces` |
| Lean | `leanprover/lean4:v4.33.0` |
| mathlib | `v4.33.0` |
| `lake build` | 通过（直接调用已安装的 Lean 4.33.0 工具链，8732 个目标）；仅有风格和测试模块使用 `native_decide` 的警告 |
| 全局黑棋必胜定理 | 尚未声明；没有真实 15×15 策略证书 |

## 模块状态

| 模块 | 数学含义 | 正式证明 | 可执行测试 | 当前限制 |
|---|---|---|---|---|
| `Gomoku.Basic` | 玩家、棋子、15×15 坐标、棋盘更新、棋子数和空位数 | 有；包括落子点/其他点和计数变化 | 有 | `Board.place` 本身允许覆盖，必须由 `legalMove` 约束 |
| `Gomoku.Geometry` | 四个方向、边界步进、连续线段、至少五连、活三/活四及冻结断三/跳四模式 | 有多项几何引理和规范化起点引理；新增 `step_compose`、`step_left_endpoint_shift` | 有 | 民间棋形变体不会自动归入 v1 模式 |
| `Gomoku.Rules` | 局面、合法着法、终局、和棋、可达性和轮次/数量不变量 | 有；新增 `terminal_draw_iff`、`terminal_none_iff`、`terminal_ne_none_iff`、`LegalMoveSequence` 和 `reachable_playMoves` | 有 | 同时存在双方胜利的不可达位置仍按终局定义中的黑优先顺序计算 |
| `Gomoku.Game` | 强制获胜、具体策略、策略树等价性 | 有；新增 `canForceWin_terminal_iff` 和否定推论 | 有 | 只定义了博弈语义，没有解决 15×15 搜索 |
| `Gomoku.Tactics` | 立即胜着、胜点、活三/活四扩展和局部强制胜势 | 有；颜色无关的直线活四立即胜、单活四、双威胁、安全断三等 | 有；含黑棋和白棋活四正例 | 安全双活三等谓词仍把必要的防守后结论作为前提 |
| `Gomoku.Certificate` | 依赖类型策略树、紧凑证书、节点/边/覆盖检查和 soundness | 有；`compact_certificate_sound` | 有 | 没有真实的全局证书输入 |
| `Gomoku.Search` | 候选着法、快速成五、有限深度候选树、递归搜索和搜索器接口 | 有局部等价引理、证书连接定理、状态诊断、`searchKey_eq_iff` 和带缓存搜索入口 | 有；含错误目标/深度/局面缓存回归 | 缓存已接入递归参考搜索，但仍不是高性能完整求解器 |
| `Gomoku.Bounded` | 以剩余深度为参数的可执行 AND/OR 博弈语义 | `boundedCanForceWin_sound`、`boundedCanForceWin_terminal_iff`、`boundedCanForceWin_false_of_terminal_ne`、`boundedCanForceWin_mono`、`boundedCanForceWin_mono_of_le`、`canForceWin_bounded_complete`、`checkedDepthCertificateFor_bounded`、`checkedDepthCertificateForCached_bounded` 及空位数等价定理 | 有；两空点局面与候选树结果对照，另有和棋、对手立即胜的多深度反例 | 这是语义审计和有限求解基准，不替代大规模搜索器 |
| `Gomoku.Engine` | 带节点预算、威胁排序、选择性目标节点剪枝和置换表的 Lean 端 AND/OR 候选搜索器 | `runCheckedEngine_sound`；`mem_engineProverCandidateMoves_legal`；`mem_engineCandidateMoves_of_legal`；缓存三状态接口；`EngineStats` 工作量计数 | 有；模块内 smoke test 和 `Gomoku.EngineAudit` | 资源限制或选择性宽度会使结果不完备；不是 15×15 完整求解器 |
| `Gomoku.TerminalAudit` | 统一的落子后终局分类回归 | 复用 `terminalAfterMoveFast_eq_terminal` | 有；一步成五、最后一格和棋、终局后非法着法 | 只负责单步终局分类，不是搜索算法 |
| `Gomoku.Examples` | 基本 API 的示例局面 | 示例由 Lean 检查 | 有 | 示例不是独立的全局定理 |
| `Gomoku.Adversarial` | 已有几何、战术和证书错误反例 | 反例目标由 Lean 检查 | 有 | 主要使用 `native_decide`，用于回归而非 trusted soundness |
| `Gomoku.RuleAudit` | 本轮新增的规则、终局、可达性和证书负例审查 | 新增的通用规则/博弈定理被正式检查；满盘和棋还由 225 步合法历史证明可达 | 有；四方向五连、长连、边界、满盘和棋、真实交替胜局、错误轮次和证书 | 满盘着色和整局回放的昂贵计算只在命名定理中执行一次 |
| `Gomoku.SearchAudit` | 有限深度搜索与 Lean 检查器之间的正常局面回归 | `checkedDepthResultFor_sound` 连接“接受”状态和 `CanForceWin` | 有；正常可达一步胜、对手立即胜着导致 `noCandidate`，并与 `boundedCanForceWin` 对照 | 只验证小局面和有限深度；不代表完整 15×15 求解 |
| `Gomoku.InteropAudit` | 外部搜索器棋子数组和 `CompactCertificate` 的 Lean 适配层 | `checkExternalLocalCertificate_sound`、严格入口复用同一 soundness | 有；C++ 导出器形状的正确证书、错误子位置和重复坐标 | 普通入口不验证数组历史来源；严格入口只保证坐标不重复，不自动证明可达性 |
| `Gomoku.EngineAudit` | Lean 端引擎的独立正反例回归 | 复用 `runCheckedEngine_sound` | 有；可达一步胜、对手立即胜和节点预算截止 | 仅为小局面和有限资源测试 |
| `Gomoku.MutationAudit` | 故意错误规则的反例审查 | 反例直接由 Lean 检查 | 有；六连、只查横线、边界端点和终局后落子 | 只验证已列出的错误变体，不等同于穷尽所有实现错误 |
| `Gomoku.Generated.Cpp*` | C++ 搜索器输出的五个局部证书样例 | 由 `checkLocalCertificateAt` 和 `local_certificate_at_sound` 检查 | 有；立即胜、双应手、连续威胁、真实可达一步胜和真实可达双威胁 | 不是空棋盘根；C++ 源码仍在队友分支 |

队友分支的隔离构建和兼容性结果见 [`TEAM_SEARCHER_COMPATIBILITY.md`](TEAM_SEARCHER_COMPATIBILITY.md)。

## 未提交文件和处理原则

当前工作区包含以下未提交内容：

- `Gomoku/Search.lean`：已有本地搜索/缓存路线修改；本轮在其上新增了
  `CheckedDepthResult` 诊断结果和对应 soundness 接口。
- `Gomoku/Engine.lean`：接入带预算、威胁排序、选择性剪枝和缓存的 Lean 端候选搜索器；
  本轮增加 `EngineCacheLookup`，显式区分缓存未命中、已缓存失败和已缓存候选树。
- `Gomoku/SearchAudit.lean`：本轮新增的正常局面搜索回归模块。
- `Gomoku/Bounded.lean`：新增的有限深度可执行语义，以及与 `CanForceWin` 的 soundness/
  completeness 桥接。
- `Gomoku/BoundedAudit.lean`：有限深度不足与空位数充分深度的对照回归。
  本次又增加了它与候选树 `accepted` 结果的对照，以及和棋、对手立即胜着的多深度反例。
- `Gomoku/SearchAudit.lean`：有限深度搜索与检查器的回归；本次增加了与
  `boundedCanForceWin` 的同局面比较。
- `Gomoku/EngineAudit.lean`：新增引擎成功、对手立即胜、资源截止、双应手覆盖和漏应手拒绝回归，
  以及缓存三状态和配置隔离回归。
- `Gomoku/TerminalAudit.lean`：新增统一落子后终局分类的正反例和等价性回归。
- `Gomoku/Engine.lean`：新增 `terminalChecks` 和 `candidateMoves` 工作量计数；
  计数只记录缓存未命中时的实际扫描。
- `Gomoku/Generated/CppReachableDoubleThreat.lean`：C++ 搜索器生成的 417 节点证书，覆盖
  一个真实可达双威胁局面的全部 208 个白棋合法应手。
- `Gomoku/MutationAudit.lean`：四种故意错误规则的可执行反例审查。
- `Gomoku/Rules.lean`、`Gomoku/Game.lean`、`Gomoku/Tactics.lean`、`Gomoku/RuleAudit.lean`：
  前置规则、博弈、战术和审查改动。
- `Gomoku.lean`：加入 `Gomoku.Engine`、`Gomoku.SearchAudit`、
  `Gomoku.InteropAudit`、`Gomoku.EngineAudit` 和 `Gomoku.TerminalAudit` 导入。
- `AUDIT_REPORT.md`、`BASELINE_STATUS.md`、`SEARCHER_INTERFACE.md`、
  `TEAM_SEARCHER_COMPATIBILITY.md`：同步本轮审查和协作接口文档。
- `Check.lean`：未跟踪的临时检查文件，尚未纳入项目入口。
- `search-test.olean`：未跟踪的构建产物，不作为源码成果。
- `_team_searcher_tmp/`：队友分支的隔离副本和 C++ 编译产物，不作为主线成果。
- 上述临时文件和目录已加入根目录 `.gitignore`，不会被 `git add -A` 纳入上传。
- `LOCAL_PROJECT_ACHIEVEMENTS.md`、`LOCAL_PROJECT_LEARNING_GUIDE.md`：已有项目说明文档。

合并队友分支前，应先单独保存或提交这些本地修改，再比较搜索器版本；不应使用强制覆盖命令清理工作区。

## 本轮审查结论

本轮（2026-08-29）新增了直线活四端点的几何桥接：`step_compose` 证明同一方向的步长
可以复合，`step_left_endpoint_shift` 证明把连续段起点移到左端点时五个窗口位置保持一致。
基于这两个引理，`straightOpenFour_left_has_winningCell`、
`straightOpenFour_right_has_winningCell` 和 `straightOpenFour_has_two_distinct_winningCells`
正式证明：一条直线型活四的两个端点都是不同的立即胜点。`PatternAudit` 增加了定理级回归，
但该结果仍只描述局部几何胜势，不等于空棋盘的全局必胜证明。

已补上的可检查内容：

1. 横、竖、两种斜线的五连正例。
2. 六连满足“至少五连”，且不是错误的“恰好五连”。
3. 满盘、双方无五连时的和棋判定。
4. 和棋或对手胜利局面不能推出目标方 `CanForceWin`。
5. 首着的轮次、落子点和其他点不变。
6. 错误轮次和错误棋子数量的局面不可达。
7. 和棋叶、非终局叶、对手胜利叶、非法落子和错误轮次证书均被拒绝。
8. 一步胜着会立即终局，随后所有着法均被拒绝。
9. `CanForceWin` 的目标方节点是存在一个胜势子节点，对手节点要求覆盖所有合法应对。
10. 正确的一步策略证书通过并推出 `CanForceWin`；和棋伪装、对手胜伪装、坏根索引、
    自循环、后向引用和错误对手节点均被拒绝。
11. `LegalMoveSequence` 和 `reachable_playMoves` 将一串合法着法正式回放为可达局面；
    `auditDrawPosition` 现在由 225 步交替历史定义，且回放结果被 Lean 检查为满盘和棋。
12. 终局优先级（黑胜优先于白胜，胜利优先于和棋）、右/上边界五连和含间隔的非五连均有
    独立回归；另有九步交替历史形成真实可达的黑棋五连。
13. 证书审查增加局部根不匹配、非法落子、错误轮次、越界引用、单一空点的对手轮次错误，
    以及 prover/opponent 子节点位置不匹配的直接节点级反例。
14. `terminal_none_iff` 与 `terminal_ne_none_iff` 双向刻画终局状态；新增真实可达的白棋
    立即胜着历史，避免只用棋子数不符合交替规则的孤立棋盘测试。
15. 证书允许共享同一子树；重复的对手着法不会绕过合法性、边覆盖或子局面匹配检查，
    共享子树正例已通过 `checkLocalCertificateAt` 并连接到 `CanForceWin`。
16. `playMoves_emptyCount_add_length` 将逐步“空位减少”提升为整串合法历史的不变量；
    满盘和棋回放额外验证最终空位数为零。
17. 新增 `auditReachableImmediatePosition`：黑白双方各走四手、局面从空棋盘合法回放得到，
    轮到黑棋且存在一步合法胜着；对应的两节点 `CompactCertificate` 已通过
    `checkLocalCertificateAt` 并推出 `CanForceWin`。这为外部搜索器提供了第一个正常局面基准。
18. 新增 `CheckedDepthResult`、`checkedDepthResultFor` 及其可靠性接口，将有限深度搜索结果区分为：
    没有候选树（`noCandidate`）、候选证书被检查器拒绝（`rejected`）和检查通过（`accepted`）。
    `checkedDepthResultFor_sound` 只对 `accepted` 分支给出 `CanForceWin`，避免把搜索资源不足误读为数学反例。
19. 新增 `Gomoku.SearchAudit`：在真实交替历史形成的黑棋一步胜局面上，有限深度搜索结果被检查器接受并
    通过 soundness 定理；在白棋有立即胜着的真实可达局面上，黑棋结果为 `noCandidate`，对应的普通
    `checkedDepthCertificateFor` 返回 `none`。这两类测试固定了搜索器和可信 Lean 侧之间的边界。
20. 新增 `mem_allCoords` 和 `mem_engineCandidateMoves_of_legal`：形式化说明引擎的对手节点保留
    每一个合法应手；`Gomoku.EngineAudit` 在只有两个合法应手的双威胁局面上验证引擎证书通过，
    并验证故意漏掉其中一个应手的证书被拒绝。迭代加深的六次节点访问统计也作为回归记录。
21. C++ 搜索器新增 `CppReachable.lean` 生成样例：输入由 `auditReachableImmediateMoves` 产生的
    真实可达局面，程序在深度 1 找到 `(7,8)` 的立即胜着；`InteropAudit` 用
    `samePosition_true_iff` 将其数组根局面连接到 `Reachable auditReachableImmediatePosition`，
    并由 Lean 检查证书后推出同一局面的 `CanForceWin`。
22. C++ 搜索器又生成 `CppReachableDoubleThreat.lean`：根局面由 17 手合法交替历史构造，黑棋有
    两条相互独立的四连，白棋轮到行动。证书包含 417 个节点，并明确覆盖全部 208 个合法白棋应手；
    `Gomoku.InteropAudit` 还分别检查合法应手数和证书应手数均为 208，并验证删去一个应手会被拒绝。
23. 新增 `Gomoku.MutationAudit`，把“测试确实能抓住错误”落实为四个可执行反例：恰好五子的
    错误规则拒绝六连，只查横线的错误规则漏掉竖线胜利，把边界当开放端点的错误规则误报活四，
    以及忽略终局条件的错误合法着法接受胜后落子；正式定义对这些局面的结果均保持正确。
24. 规则层新增 `Position.reachable_winner_turn`：对可达终局，Lean 证明记录的赢家必然是刚刚
   落子的一方，当前轮次必然已经切换到另一方；真实黑胜和真实白胜历史都覆盖了这个不变量。
25. 新增 `Gomoku.Bounded`：`boundedCanForceWin` 用显式剩余深度计算有限棋局，
    `boundedCanForceWin_sound` 证明通过有限计算不会产生假胜利；`canForceWin_bounded_complete`
    证明任何 `CanForceWin` 局面在 `Board.emptyCount + 1` 深度内都会被该语义识别，二者在该
    深度上完全等价；`boundedCanForceWin_mono` 证明增加燃料不会撤销已找到的胜势。
    `Gomoku.BoundedAudit` 用两空点双威胁局面验证深度 0 失败、深度 2 成功，
    并把同一局面的有限语义结果与候选树搜索的 `accepted` 状态对照；终局和棋与对手已有
    立即胜着的局面在不同深度下均保持 `false`。这些测试明确说明有限深度的 `false` 不能
    当作数学上的必败证明。
26. 新增 `checkedDepthCertificateFor_bounded` 和
    `checkedDepthCertificateForCached_bounded`：候选证书一旦通过 Lean 检查，就能在
    不小于 `Board.emptyCount + 1` 的理论深度上推出独立有限语义返回 `true`；这是一条
    充分深度桥接，不声称候选搜索与有限语义在任意深度、任意缓存状态下已经完备等价。
27. 修正 `Gomoku.Engine` 的缓存键：`EngineSearchKey` 现在同时保存引擎配置和搜索查询，
    因而选择性剪枝、威胁排序或宽度限制不同的配置不会复用彼此的失败结果；
    `EngineAudit` 增加了跨配置缓存回归。

构建说明：elan 包装器有时会先联网检查更新；当前网络不可用时该检查会在构建前失败。
使用已安装的 Lean 4.33.0 工具链中的 `lake.exe` 运行全工程构建，8732 个目标全部通过。
这一区别已记录，避免把工具链联网失败误认为源码失败。

本轮还新增 `terminalAfterMoveFast`：它把“非法着法、落子成五、落子后和棋、继续进行”
四种结果集中在一个可执行接口中。`terminalAfterMoveFast_eq_terminal` 正式证明：从非终局
局面出发执行合法着法时，该快速分类与完整 `terminal (play s m)` 完全相同。引擎的目标方
立即胜和对手立即胜短路均改用此接口；`Gomoku.TerminalAudit` 覆盖一步成五、最后一格和棋
以及终局后非法着法。

本轮审查还发现并修正了一个测试局面错误：原“对手立即获胜”棋盘实际上已经终局，
现改为只含四枚白子和一个空获胜端点，使非终局前提和测试目的完全一致。

本轮新增的满盘和棋不再是任意填写的终局棋盘：棋盘由 `auditDrawMoves` 从空棋盘逐步
交替填满，`auditDraw_moves_legal` 与 `auditDraw_reachable_position` 分别证明每一步合法
以及最终局面可达。由于 225 步后轮到白棋，局面的计数为黑 113、白 112；该构造在四个
方向都没有五连，因此终局分类严格为和棋。

注意：正确的“必胜证书”不能含和棋叶。若对手有一条合法路线能到和棋，目标方就不能称为
强制获胜；因此测试目标应是“和棋叶被拒绝”，而不是“和棋叶能够出现在正确必胜证书中”。

仍未完成的内容：

- 活三/活四全部民间变体的统一形式化。
- 更深的局部威胁链定理。
- 面向大局面的高效缓存搜索器（当前只有正确性导向的有限深度缓存参考实现）。
- 为带缓存递归搜索补充任意深度的更强语义等价定理，并用增量威胁信息、置换表和性能基准减少重复扫描。
- 从空棋盘开始的完整 15×15 `CompactCertificate`。
- `initial_black_wins`。
