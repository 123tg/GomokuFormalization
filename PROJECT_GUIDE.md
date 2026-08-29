# 无禁手五子棋规则与必胜策略形式化：项目总说明

## 1. 项目目标

本项目用 Lean 4.33.0 和 mathlib 形式化 15×15 无禁手五子棋。

“形式化”不是编写一个普通的五子棋程序，而是把规则、局面、着法、终局、局部战术和全局策略都写成 Lean 能够检查的定义与证明。最终目标是证明：

~~~lean
theorem initial_black_wins :
  CanForceWin initialPosition .black
~~~

目前这个最终定理还没有实现。项目明确区分：

- 已经由 Lean 内核检查的规则和战术定理。
- 仅完成数据结构或结构性检查的接口。
- 依赖实际 15×15 策略证书、目前尚未获得的最终结论。

因此，当前成果是一个可信的规则与策略形式化基础，而不是未经证实地声称黑棋必胜。

## 当前进度（截至本次审计）

项目按实施阶段编号管理，目标模式的 `active` 只表示最终目标尚未闭合，
不表示已经完成的阶段会重新执行。

- 阶段 1--4：规则、几何基础、可达性、不变量和有限博弈语义，已完成。
- 阶段 5：直线型活三/活四、立即胜着和安全双活三语义，已完成。后续扩展的
  `MaximalRun`、冻结断三模式和跳四模式也已完成；这不表示所有民间命名的断三
  变体都被自动纳入，新增变体仍必须逐个冻结并证明。
- 阶段 6：`CertificateTree`、`CompactCertificate`、节点检查器和
  `compact_certificate_sound`，已完成。
- 阶段 7：人工证书、错误证书拒绝、几何双活三反例和对抗性审计，已完成。
  当前还包含一个覆盖 `opponentMoves` 全部合法应对的五节点局部正向证书，并加入
  遗漏应手、越界引用、错误子局面和错误终局标签四种负向证书回归。
- 阶段 8（核心接口已完成，模式扩展继续）：已补齐 `MaximalRun`、独立的 `brokenOpenThree`/`jumpFour`
  模式表和跳四立即胜着定理；已建立不依赖轮次的 `WinningCells`/`HasDoubleThreat`
  以及 `doubleThreat_forces_win` 统一博弈接口。新增 `FourExtensionCells`、
  `straightOpenThree_has_fourExtension` 和 `HasDoubleFourThreat`，明确区分“落子后
  形成四连的扩展点”和“立即成五的 `WinningCells`”；几何双活三到两个独立强制
  胜点的 soundness 证明、更多断三变体和反击排除条件仍待完成。新增
  `brokenOpenThree_has_fourExtension`，证明两个冻结断三模式填补内部缺口后至少
  形成一个四连扩展点；新增 `OpenFourExtensionCells`、
  `straightOpenFour_has_winningCell` 和 `openFourExtension_has_winningCell`，把
  方向性开放四扩展连接到至少一个立即成五点；新增 `BrokenOpenThreeMove`、
  `SafeBrokenOpenThree` 和 `safeBrokenOpenThree_forces_win`，将断三包装接入
  `ForceWin`；新增 `ImmediateSafeBrokenOpenThree` 及其到安全谓词和
  `CanForceWin` 的推论，但安全谓词仍要求显式提供所有防守后的 `CanForceWin`。
  `Gomoku/Adversarial.lean` 现在包含一个仅有三个空点的有限断三安全局面，
  由 `native_decide` 验证立即安全条件并通过该推论得到 `CanForceWin`；另有一个仅有
  两个空点的黑棋双威胁局面，直接验证 `HasDoubleThreat` 并通过
  `doubleThreat_forces_win` 得到 `CanForceWin`；另有一个黑棋填中心后产生横、竖
  双四的局面，验证 `doubleThreat_move_forces_win` 的落子级桥接。上述局面都是局部
  回归测试，不是全局 15×15 证书。另加入“黑棋几何双活三但白棋已有立即胜着”的
  反例，并用 `not_safeDoubleOpenThree_of_opponentImmediate` 和
  `not_immediateSafeDoubleOpenThree_of_opponentImmediate` 验证安全谓词不会误触发；
  `winningCell_ne_of_hasDoubleThreat` 把“单步防守最多占一个胜点”的公共逻辑抽成
  可复用定理。
- 阶段 9（搜索引擎骨架已完成，规模扩展继续）：`Gomoku.Search` 现在提供可执行的 225 点坐标表、
  合法候选着法过滤、首个立即胜着扫描，以及局部立即胜着证书候选生成器。候选着法有
  一个参考实现和一个把终局检查提到棋盘级别的 `candidateMovesFast` 实现；
  `mem_candidateMovesFast_iff_mem_candidateMoves` 证明两者的成员关系一致。新增的
  `orderedCandidateMoves` 只把有相邻棋子的空点提前，保留所有候选点；
  `mem_orderedCandidateMoves_iff` 证明该排序不改变集合。
  `tacticalCandidateMoves` 还定义了“立即胜着、必须防守、安静着法”三组候选的
  分组接口，但当前默认搜索仍使用较轻量的 `immediateWinningMovesFirst`；必须防守
  分组待增量威胁缓存后再启用。`winningCellsArray` 提供逐点数组接口；新增的
  `coordIndex`/`coordAtIndex` 是经证明的 225 点行主序双射，`winningCellsMask` 使用固定
  长度 225 的布尔向量缓存威胁，并有 `winningCellsMask_get_iff` 证明索引查询与
  `WinningCells` 等价。`tacticalCandidateMovesFast` 使用该掩码并有
  `mem_tacticalCandidateMovesFast_iff` 成员保持定理；它目前作为实验接口保留，尚未切换
  默认搜索。新增 `createsFiveFast` 只检查包含新落子点的四个方向、五个窗口位置，最多
  检查 20 个窗口；`createsFiveFast_sound` 和 `createsFiveFast_complete` 证明：在原局面
  没有目标方五连时，它与落子后形成五连等价，`createsFiveFast_terminal_iff` 进一步把
  合法轮次下的快速结果与 `terminal` 胜负标签对应起来。Search 文件中的回归例子覆盖
  横、竖、两种斜线、边界窗口和不足五子的反例。
  同一阶段还定义了无碰撞的 `PositionKey`（轮次加 225 格 `Vector Cell`）、
  `boardKey_eq_iff`/`positionKey_eq_iff` 和 `containsPositionKey`。`SearchMemo`/`SearchKey`
  适配层的键同时记录剩余深度、目标方和完整局面；基础递归搜索已能携带并更新数组缓存，
  缓存得到的候选树仍会重新经过局部证书检查，因此缓存不是可信证明来源。
  新增 `Gomoku.Engine` 后，生产型试验入口改用 `Std.HashMap` 置换表。第三轮纯 Lean 优化
  又把引擎键从 225 格 `Vector Cell` 换成双方各四个 `UInt64` 的 `EnginePositionKey`；根棋盘
  只编码一次，递归落子通过设置一个 bit 并切换轮次增量更新。标准哈希表在桶内精确比较
  `EngineSearchKey`；哈希冲突只影响性能，不会把不同紧凑键当作同一键。
  `checkLocalCertificate` 不改变全局根约束，而是允许任意局面作为局部证书根；
  `twoPlyImmediateCertificate` 可从有限的“对手应手 -> 我方立即胜着”表生成完整
  `opponentMoves` 证书，`immediateResponseTable` 则枚举所有合法对手应手并尝试自动
  填表。新增的 `CandidateTree`/`searchCandidateTree` 支持有限深度的目标方选择、
  对手全分支覆盖和终局叶子，并通过 `candidateTreeCertificate` 编译为紧凑证书；
  `checkedDepthCertificateFor_sound` 只在局部根检查通过后给出 `CanForceWin`。
  `firstWinningMove` 现在使用 `createsFiveFast` 扫描，`firstWinningMoveReference` 保留
  完整 `terminal` 扫描以便回归比较；`immediateWinningMovesFirst_mem_legal` 和
  `createsFiveFast_terminal_of_immediateCandidate` 证明快速命中只接受合法着法并对应
  真实终局胜着。
  `Gomoku.Engine` 进一步提供迭代加深、硬节点预算、`found`/`notFound`/`cutoff` 三态递归
  结果、缓存命中和节点访问统计。预算耗尽产生的 `cutoff` 不会写成失败缓存；缓存可设置
  硬条目上限，饱和后跳过新键并记录 `memoStoreSkips`。目标方节点只需找到一个成功子树，
  对手节点仍完整展开每个合法应手。新的
  `engineTacticalCandidateMoves` 用 `createsFiveFast` 将立即胜着、必须防守点和安静着法
  排序，并由 `mem_engineTacticalCandidateMoves_iff` 证明没有删除候选着法。引擎在目标方
  节点启用强制着法剪枝：有立即胜着时只搜索胜着；否则若对手下一手可成五，只搜索对应
  防守点。`maxProverMoves` 还能选择性限制目标方分支宽度；正值可能漏掉深层胜解，所以
  `notFound` 只表示当前配置没有找到证明。一步成五分支直接生成终局叶子，省去一次递归访问。
  紧凑键回归覆盖 63/64、127/128、191/192 和末端索引 224，验证增量结果等于重新扫描棋盘；
  同一原生 Lean 进程的 20,000 次一步子键“构造 + 哈希”微基准中，旧向量路径约为
  2.79–2.82 秒，增量 bitboard 路径约为 0.037–0.039 秒（约 72–75 倍）；这只衡量换位表键热路径，
  不是整棵搜索树的端到端加速比，也不是实际堆内存测量。
  可用 `lake env lean --run bench/LeanEngineKeyBenchmark.lean` 在当前机器上重新测量。
  `runCheckedEngine` 只返回通过 `checkLocalCertificateAt` 的证书，
  `runCheckedEngine_sound` 将任何被接受结果连接到 `CanForceWin`。
  同一阶段现已增加独立的 `cpp/gomoku_solver` 原型：它以双方各四个 `uint64_t` bitboard
  保存棋盘，增量维护确定性 Zobrist 哈希，使用精确 bitboard 相等性消除哈希碰撞风险，
  并执行迭代深度 DFPN。目标方是 OR 节点，对手方是 AND 节点；目标方可使用立即胜着/
  强制防守剪枝和可选宽度限制，对手节点始终生成全部合法着法。C++ 输出仍是现有
  `CompactCertificate`，没有修改证书表示，也不通过 FFI 进入可信基础。
  `Gomoku.Generated.CppSmoke` 和 `Gomoku.Generated.CppFork` 分别检查 C++ 生成的两节点
  立即胜证书和五节点全应手证书；新增的有界 VCF 预搜索只提供目标方着法提示，
  `Gomoku.Generated.CppVcf` 用六节点证书覆盖开放四的两个合法防守。三者都由
  `local_certificate_at_sound` 得到 `CanForceWin`，对手分支没有因 VCF 而省略。
  `Gomoku/Adversarial.lean` 还用一个固定的五节点双威胁候选树回归测试了
  `CandidateTree -> CompactCertificate -> checkLocalCertificateAt -> CanForceWin`
  的完整链路；该测试覆盖对手节点的全部两个合法应手。真实 15×15 策略证书尚未导入，
  因此 `initial_black_wins` 仍未声明。

  接口同步步骤已完成：GitHub `main` 的规则审计、模式审计和 `SEARCHER_INTERFACE.md`
  已合入本地搜索分支，同时保留已有中文注释、Lean 搜索引擎、C++ DFPN/VCF 和小棋盘
  搜索工具。C++ 导出器现在先用 `validateCertificate` 预检胜局标签、轮次、合法着法、
  对手全应手覆盖、严格向后引用和子局面一致性；空 15×15 初始局面的黑方证书自动连接
  `checkCertificate`/`compact_certificate_sound`，局部局面继续连接
  `checkLocalCertificateAt`/`local_certificate_at_sound`。该 C++ 预检只用于尽早发现接口错误，
  不进入可信基础，最终结论仍以 Lean 检查结果为准。

最近一次验证：C++17 版本已用 GCC 10.3 在 `-O3 -DNDEBUG` 下构建，
`gomoku_tests.exe` 的几何、解析、OR/AND/VCF 证明和资源上限回归全部通过；立即胜、
对手全应手和开放四 VCF 示例分别生成 2、5、6 节点证书。VCF 开启时该开放四回归的
DFPN 展开节点从 13 降到 7；VCF 节点预算耗尽或关闭时，完整 DFPN 仍生成同一证明。
本次接口同步后又重新执行了完整 `lake build`，合并后的 8723 个构建任务全部成功；
新版 C++ 导出器生成的临时两节点局部证书也已单独通过 `lake env lean` 检查。
新增的 C++ 负向回归确认预检会拒绝非向后子引用和遗漏对手合法应手。
`lake build Gomoku.Generated.CppSmoke`、`lake build Gomoku.Generated.CppFork` 和
`lake build Gomoku.Generated.CppVcf` 均通过；先顺序构建内存占用较高的模块后，
`lake build` 全工程通过（8721 jobs）。预算、选择性分支、强制防守、缓存上限和证书回归
均通过。构建输出中的
linter 警告（文件头注释、测试模块使用 `native_decide`）不等同于 Lean 类型检查失败；
核心 soundness 定理仍不
依赖 `native_decide`。固定候选树回归已在单独构建中通过；在把终局检查提到棋盘级别后，
  两空点局面的 `checkedDepthCertificateFor 2` smoke test 也已通过。快速成五判定的四方向
  和边界回归，以及它和完整 `terminal` 的合法着法等价性也已通过。Lean 引擎换位表键已经
  避免在每个递归节点重新扫描并保存 225 格对象；更深或更宽的搜索仍会为终局、候选和威胁
  反复扫描棋盘，暂不作为常规构建目标，待加入增量终局/威胁维护、缓存替换/淘汰策略和证书
  DAG 共享后再扩展。

新增的 `Gomoku.Parametric` 把方形棋盘边长和获胜连珠长度分别保存为
`GameSpec.boardSize` 与 `GameSpec.winLength`，不修改原有 15×15 API。当前
`fiveByFiveSpec` 是真正的 5×5、五子连珠实例。其双威胁回归根局面有 18 个白方合法应手，
`searchTwoPly` 为每个应手生成黑方一步胜着，`checkTwoPlyCertificate_sound` 证明检查器
通过即可推出参数化 `ForceWin`，最终定理为 `fiveByFive_black_forces_win`。这只是局部
两层必胜结论。独立的 `cpp/tools/solve5x5.cpp` 随后从空 5×5 棋盘执行精确三值
negamax，使用 D4 对称归一化、带上下界的 alpha-beta 和固定扁平置换表；本地完整运行
510,652,639 个递归节点、最大深度 25，计算结论为和棋。这个结论目前是可复现的原生
计算结果，还不是 Lean 定理：现有 `ForceWin` 只表达一方强制获胜，要形式化和棋还需
参数化的结果证书、双方不败语义及相应 checker soundness。
另新增 `cpp/tools/solve_small_draws.cpp`，把 Maker--Breaker 五连超图搜索参数化到
5×5--8×8，并实现配对证书、部分配对、双方着法支配、Breaker r-zone、势函数终止、
D4 对称和四路组相联置换表。本地已用静态配对证明空 5×5 和棋；用“白方首应 + 配对”
覆盖 6×6 的全部 6 个首着对称类；用深度 8 的闭合 AND/OR 树证明 7×7 和棋。
8×8 的 20,000,000 节点、深度 40 运行仍因节点预算耗尽而返回 `unknown`，所以只作为
性能基准保留，不能写成项目证明。完整命令和记录见 `cpp/tools/README.md` 与
`cpp/results/`。

---

## 2. 给完全初学者的 Lean 说明

### 2.1 定义对象

~~~lean
inductive Player where
  | black
  | white
~~~

这表示 Player 只有两个值：black 和 white。

~~~lean
structure Board where
  cell : Coord → Cell
~~~

这表示棋盘本质上是一个函数：输入坐标，输出这个位置的格子内容。

### 2.2 定义命题

~~~lean
def legalMove (s : Position) (c : Coord) : Prop :=
  ¬ IsTerminal s ∧ s.board.cell c = .empty
~~~

Prop 表示一个需要证明的命题。上面的命题说：局面 s 还没有结束，并且坐标 c 是空点。

### 2.3 定理和证明

~~~lean
theorem play_emptyCount_lt {s : Position} {c : Coord}
    (hlegal : legalMove s c) :
    Board.emptyCount (play s c).board < Board.emptyCount s.board := by
  ...
~~~

冒号后面是定理内容，hlegal 是前提，by 后面是证明。Lean 会检查证明是否真的推出结论。

### 2.4 example 是测试

~~~lean
example : initialPosition.turn = .black := rfl
~~~

example 也会被检查，但不会产生供其他文件引用的正式定理名。项目用它们做局面测试和回归测试。

---

## 3. 已冻结的规则

正式棋盘固定为 15×15：

~~~lean
abbrev Coord := Fin 15 × Fin 15
~~~

Fin 15 只允许 0 到 14，因此坐标不会越界。

规则约定：

1. 黑棋先手。
2. 双方交替落子。
3. 一步只能把当前玩家的棋子放在空点。
4. 横、竖、两条对角线上连续五子或更多子即获胜。
5. 六连、七连等长连也算胜利。
6. 形成五连后立即终局，不能继续落子。
7. 棋盘填满且无人五连时为和棋。
8. 不实现三三、四四、长连禁手。
9. 棋盘边界对活三和活四的开放端属于封闭端。
10. 完整博弈只讨论从空棋盘按合法着法走出来的可达局面。
11. 活三、活四等局部图形另外定义；使用局部战术定理时要明确写出合法性、轮次和非终局前提。

“无禁手”通过 legalMove 没有附加禁手条件来实现；“至少五连即胜”通过 hasAtLeastFive 来实现。

---

## 4. 源码结构

建议按以下顺序阅读：

| 文件 | 内容 |
|---|---|
| Gomoku/Basic.lean | 玩家、格子、坐标、棋盘、落子、计数 |
| Gomoku/Geometry.lean | 四个方向、边界步进、连续线段、活三/活四几何 |
| Gomoku/Rules.lean | Position、合法着法、终局、可达性、规则不变量 |
| Gomoku/Game.lean | Strategy、ForceWin、CanForceWin |
| Gomoku/Tactics.lean | WinningMoves、活三/活四和局部必胜定理 |
| Gomoku/Certificate.lean | 依赖类型策略树和紧凑证书检查器 |
| Gomoku/Search.lean | 候选生成、基础有限深度搜索和候选证书编译 |
| Gomoku/Engine.lean | 哈希置换表、节点预算、迭代加深和受检搜索入口 |
| cpp/ | C++17 bitboard/DFPN 必胜搜索器，以及 C++20 参数化小棋盘和棋证明搜索器 |
| Gomoku/Generated/*.lean | C++ 生成并由现有检查器接受的局部回归证书 |
| Gomoku/Examples.lean | 构造局面、正反例和 API 测试 |
| Gomoku/Adversarial.lean | 对抗性反例、语义审计和证书拒绝测试 |
| Gomoku.lean | 统一导入所有模块 |

配置文件：

- lakefile.toml：项目名、mathlib 依赖和 Lean 选项。
- lean-toolchain：Lean 4.33.0。
- README.md：快速说明。
- PROJECT_GUIDE.md：本完整方案和执行手册。
- AUDIT_REPORT.md：对抗性审计发现、已修正问题和未解决风险。

验证命令：

~~~text
lake build
~~~

---

## 5. Basic：棋盘和落子

### 5.1 基本类型

~~~lean
inductive Player where
  | black
  | white

inductive Cell where
  | empty
  | stone (player : Player)

abbrev Coord := Fin 15 × Fin 15

structure Board where
  cell : Coord → Cell
~~~

Cell.stone p 直接记录棋子颜色，避免一个格子同时拥有黑白两个布尔状态。

### 5.2 空棋盘和落子

~~~lean
def Board.empty : Board := ⟨fun _ => .empty⟩

def Board.place (b : Board) (c : Coord) (p : Player) : Board :=
  ⟨fun d => if d = c then .stone p else b.cell d⟩
~~~

place 只负责更新数据，不负责检查合法性；合法性由 Rules 中的 legalMove 检查。这样的分层使定义和证明更简单。

### 5.3 已完成定理

已经证明：

- place_same：落子点变成指定棋子。
- place_other：其他坐标不变。
- count_place_same_of_empty：在空点落子后，目标颜色数量增加 1。
- count_place_other_of_empty：另一颜色数量不变。
- emptyCount_place_of_empty：空点数量减少 1。

这些定理是后面轮次和有限博弈终止性证明的基础。

---

## 6. Geometry：方向、连续线段和图形

### 6.1 四个方向

~~~lean
inductive Direction where
  | horizontal
  | vertical
  | diagonalUp
  | diagonalDown
~~~

step c d n 沿方向 d 走 n 步，越界返回 none，合法坐标返回 some 坐标。

### 6.2 连续线段和五连

核心定义：

~~~lean
def occupiedAt ... : Prop := ...
def consecutive ... (length : Nat) : Prop := ...
def hasRun ... (length : Nat) : Prop := ...
def hasAtLeastFive (b : Board) (p : Player) : Prop := hasRun b p 5
~~~

consecutive 检查从起点开始连续若干个偏移位置是否都是同色棋子。hasAtLeastFive 对起点和方向取存在量词。

六连或更长连自动成立，因为它们包含一个连续五子子段。

### 6.3 活三和活四

~~~lean
def straightOpenThree ... :=
  consecutive ... 3 ∧ openEnd ... (-1) ∧ openEnd ... 3

def straightOpenFour ... :=
  consecutive ... 4 ∧ openEnd ... (-1) ∧ openEnd ... 4

def canonicalRunStart ... :=
  ¬ occupiedAt ... (-1)

def normalizedStraightOpenFour ... :=
  straightOpenFour ... ∧ canonicalRunStart ...
~~~

v1 只包含明确的直线型模式：连续三子或四子，两端都是空点。断三、跳四等变体没有默认并入，未来要作为独立模式加入。

`canonicalRunStart` 把线段起点前不是同色棋子写成显式谓词，
`normalizedStraightOpenThree` 和 `normalizedStraightOpenFour` 将其加入模式定义。
由于现有活三/活四左端已经要求为空，Lean 已证明这些模式自动满足规范起点条件。
见证集合使用规范化模式；边界端点通过 `step` 得到 `none`，所以不能满足 `openEnd`，自然被视为封闭端。
`StartShiftConflict` 和 `ComparableRunStarts` 进一步明确了“同一连续段内的起点可比较”
条件，并证明在该条件下直线型活三/活四起点唯一。这个结果不声称同一方向上
所有分离的活三/活四只有一个见证；完整最大连续段关系仍需以后单独定义。

---

## 7. Rules：局面、合法着法、终局和可达性

### 7.1 局面和结果

~~~lean
inductive Outcome where
  | blackWin
  | whiteWin
  | draw

structure Position where
  board : Board
  turn : Player

def Position.initial : Position := ⟨Board.empty, .black⟩
~~~

### 7.2 终局

~~~lean
def Position.isTerminal (s : Position) : Prop :=
  hasAtLeastFive s.board .black ∨
  hasAtLeastFive s.board .white ∨
  Board.full s.board

def Position.terminal (s : Position) : Option Outcome :=
  if hasAtLeastFive s.board .black then some .blackWin
  else if hasAtLeastFive s.board .white then some .whiteWin
  else if Board.full s.board then some .draw
  else none
~~~

黑胜检查在白胜之前；`reachable_not_both_winners` 已证明任何可达局面都不会出现双方
同时胜利，包括最后一步刚形成胜局的终局。落子形成黑五连后立即结束，不会进入白棋的后续回合。

### 7.3 合法着法和可达性

~~~lean
def Position.legalMove (s : Position) (c : Coord) : Prop :=
  ¬ Position.isTerminal s ∧ s.board.cell c = .empty

def Position.play (s : Position) (c : Coord) : Position :=
  ⟨s.board.place c s.turn, s.turn.other⟩

inductive Position.Reachable : Position → Prop where
  | initial : Reachable Position.initial
  | step : Reachable s → legalMove s c → Reachable (play s c)
~~~

Reachable 排除了“随便写出的、不符合轮次或棋子数的棋盘”。

### 7.4 已完成规则不变量

已经证明：

- 终局局面没有合法后续着法。
- terminal s = some outcome 能推出 s 是终局。
- 合法落子后目标坐标是当前玩家的棋子，其他坐标不变。
- 合法落子严格减少空点数。
- 可达局面轮到黑时，黑白棋子数相等。
- 可达局面轮到白时，黑子数比白子数多 1。
- 任意可达局面不能同时有黑五连和白五连；该结论也覆盖终局。

---

## 8. Game：博弈语义

### 8.1 策略接口

~~~lean
def Strategy (target : Player) : Type :=
  ∀ s, Reachable s → s.turn = target → terminal s = none →
    {m : Coord // legalMove s m}
~~~

这是“位置策略”：给定局面，只依赖当前棋盘和轮次选择着法。为了区分“任意合法策略”
和“确实获胜的策略”，项目进一步定义 `StrategyRealizes σ s hs`：目标玩家节点必须走
`σ` 返回的坐标，对手节点必须覆盖每个合法应手，叶子必须是目标玩家获胜。

### 8.2 ForceWin

~~~lean
inductive ForceWin (target : Player) : Position → Prop where
  | terminal ...
  | choose ...
  | respond ...
~~~

三种情况分别表示：

1. 当前已经是目标玩家胜利。
2. 轮到目标玩家，存在一个合法着法，使子局面继续可强制获胜。
3. 轮到对手，对手的每个合法着法都无法阻止目标玩家获胜。

公开接口：

~~~lean
def CanForceWin (s : Position) (target : Player) : Prop :=
  ForceWin target s
~~~

由于每一步都减少一个空点，博弈树是有限的。当前直接用归纳类型表达树，不依赖一个可能不终止的递归函数。

已完成：

- canForceWin_terminal：目标玩家已胜时可强制获胜。
- canForceWin_immediate：存在立即胜着时可强制获胜。
- `StrategyRealizes.sound`：具体策略实现胜利时推出 `CanForceWin`。
- `canonicalWinningStrategy`：在可强制获胜区域选择保持胜势的着法；这是使用经典选择
  构造的数学对象，不是可执行搜索器。
- `canonicalWinningStrategy_realizes`：以空位数严格下降做强归纳，证明规范策略确实实现胜利。
- `strategyRealizes_iff_canForceWin`：对可达根局面，存在获胜位置策略当且仅当
  `CanForceWin`。
- `strategyRealizes_iff_certificateTree`：把具体位置策略、依赖类型策略树和
  `CanForceWin` 三个接口闭合为等价语义。

---

## 9. Tactics：局部战术

### 9.1 威胁和立即胜着

~~~lean
def WinningMoves (s : Position) (p : Player) : Finset Coord := ...
def HasImmediateWin (s : Position) (p : Player) : Prop :=
  (WinningMoves s p).Nonempty
def OpponentHasImmediateWin ...
def ForcesWinAfter ...
~~~

这些谓词将“对方无四”“对方不能反击”等自然语言条件变成明确的 Lean 命题。

### 9.2 活三和活四接口

~~~lean
def GeometricDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop := ...
def GeometricMoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop := ...
def DoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop := ...
def MoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop := ...
def SingleOpenFour (s : Position) (p : Player) : Prop := ...
def SafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop := ...
def ImmediateSafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop := ...
~~~

需要区分：

- GeometricMoveCreatesSingleOpenFour：只描述原始 `play` 后的几何图形，不假设着法合法。
- MoveCreatesSingleOpenFour：在几何条件之外，明确要求轮到该玩家且着法合法。
- SingleOpenFour：描述当前局面中的图形。
- GeometricDoubleOpenThree：只描述原始 `play` 后至少两个活三见证。
- DoubleOpenThree：在几何条件之外，明确要求轮到该玩家且着法合法。
- SafeDoubleOpenThree：在严格双活三条件之外，排除第一步后的对手立即胜着，并要求对手每个合法防守后目标方仍满足 `CanForceWin`。这是多回合语义接口，不把“下一步立即成五”写成必要条件。
- ImmediateSafeDoubleOpenThree：把上面的防守后条件加强为 `HasImmediateWin`，是一个更强的、便于小型战术验证的特例；已证明它蕴含 `SafeDoubleOpenThree`。

### 9.3 已完成的核心局部定理

straightOpenFour_black_immediate 已完成。其内容是：

- 当前轮到黑棋。
- 当前局面不是终局。
- 存在一条直线型黑活四。
- 取该活四一端的空点落子。
- 原四颗黑子加新落子构成连续五子。
- 该着法合法，且落子后 terminal 等于 blackWin。

singleOpenFour_forces_win 已提供严格接口：

~~~lean
theorem singleOpenFour_forces_win
    (hturn : s.turn = .black)
    (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFour s .black)
    (hnoWhite : ¬ HasImmediateWin s .white) :
    CanForceWin s .black
~~~

审计后增加了 `singleOpenFour_forces_win_minimal`。它去掉了数学上不必要的
`¬ HasImmediateWin s .white` 前提；原 `singleOpenFour_forces_win` 保留该前提作为
面向战术分类的安全包装接口。两者目前都只覆盖直线型活四。

当前 v1 的图形含义只覆盖直线型活四；断三和跳四必须以后独立添加。

---

## 10. Certificate：策略证书

### 10.1 为什么需要证书

15×15 完整博弈树极大。不能把普通搜索器输出直接当作数学证明。采用：

1. 外部搜索器寻找策略。
2. 输出有限证书。
3. Lean 检查局面、轮次、边和全部对手分支。
4. 通过检查后转换为 CanForceWin。

外部搜索器不属于可信基础；Lean 内核和经过证明的校验器才属于可信基础。

### 10.2 可信策略树

~~~lean
inductive CertificateTree (target : Player) : Position → Type where
  | terminal ...
  | proverMove ...
  | opponentMoves ...
~~~

这是依赖类型树。子节点类型直接写成 play s move，因此错误的子局面很难被构造出来。

已完成：

~~~lean
theorem CertificateTree.sound ...
theorem certificate_sound (c : Certificate) :
  CanForceWin c.root c.target
~~~

已经在 Examples 中用人工终局局面构造了最小证书，验证了接口用法。

### 10.3 紧凑证书

~~~lean
inductive CertificateNode where
  | terminal ...
  | proverMove ...
  | opponentMoves ...

structure CompactCertificate where
  target : Player
  root : Nat
  nodes : Array CertificateNode
~~~

checkCertificate 当前检查：

- 目标玩家为黑棋。
- 根索引有效，根局面为空棋盘黑先。
- 终局标签正确。
- 节点轮次正确。
- 着法合法。
- 子索引有效。
- 子局面等于落子后的局面。
- 子索引严格大于父索引，排除循环。
- 对手节点覆盖全部合法应对。

checkCertificate_header 能从检查成功中提取目标、根索引和根位置事实。

审计后已补充用于可信转换的命题级引理：

- `samePosition_true_iff`：布尔位置比较为真当且仅当两个 `Position` 相等。
- `moveInBool_true_iff`：数组成员布尔判断为真当且仅当对应坐标出现在子着法数组中。
- `checkNode_terminal_iff` 与 `checkNode_terminal_reify`：终局节点的布尔检查可以转换成
  `CertificateTree` 的终局构造。
- `checkNode_proverMove_iff`、`childPositionMatches_true_iff` 和
  `checkNodeAt_proverMove_iff`：为合法着法、严格递增索引和子局面相等性提供命题形式。
- `allRefsValid_true_iff`、`allMovesLegal_true_iff` 和
  `allLegalMovesCovered_true_iff`：把数组布尔检查转换为引用有效性、合法性和完整覆盖。
- `checkNodeAt_terminal_iff` 与 `checkNodeAt_opponentMoves_iff`：覆盖终局节点和对手分支。
- `mapIdx_all_true_iff` 与 `checkCertificate_nodes_checked`：把全局数组检查转换为每个节点的检查事实。
- `compact_reify_at`：以 `nodes.size - index` 为严格下降量，在 Lean 内重建依赖类型的策略树。
- `compact_certificate_sound`：把通过检查的紧凑证书连接到 `CanForceWin initialPosition .black`。
- `certificateTree_iff_canForceWin`：在 `Nonempty` 形式下证明策略树与统一博弈语义等价；
  `ForceWin.nonemptyCertificateTree` 通过命题级递归完成反向转换。
- `Gomoku.Search`：定义 `Searcher`、`CheckedSearchResult` 和
  `acceptCertificate`，明确外部搜索算法不属于可信基础；另外提供
  `immediateWinCertificate` 原型及其节点检查、策略树重建和 soundness 定理。
- `Position.not_isTerminal_of_terminal_none` 与
  `Position.exists_legalMove_of_terminal_none`：证明非终局局面一定存在合法着法；
  `defaultStrategy` 提供只保证合法性的基线策略，不能替代胜利策略。

双活三的安全语义现在明确写成 `SafeDoubleOpenThree`：除合法双活三外，第一步后的局面必须非终局、对手没有立即胜着，并且对手的每一个合法防守后目标方仍有 `CanForceWin`。`ImmediateSafeDoubleOpenThree` 是把这项条件加强为立即胜着的特例。两个谓词都与纯几何的 `GeometricDoubleOpenThree` 分离；因此“对手不能同时堵住两个威胁”等自然语言不再承担形式化含义。

### 10.4 当前限制

紧凑检查器到策略树的可信转换已经完成：

~~~text
checkCertificate c = true
    -> compact_reify_at 重建 CertificateTree
    -> 使用 CertificateTree.sound
    -> 得到 CanForceWin initialPosition .black
~~~

因此，未来的真实全局证书可以直接使用 `compact_certificate_sound`。当前仍不能声明
`initial_black_wins`，因为项目尚未导入一个实际覆盖全部白棋应对的 15×15 策略证书。

---

## 11. 已完成成果

- [x] Lean 工程、Gomoku 命名空间和 15×15 坐标。
- [x] 黑白玩家、空格、棋子、空棋盘和落子。
- [x] 落子点/其他点性质。
- [x] 棋子数量和空点数量变化定理。
- [x] 四个方向和边界安全步进。
- [x] 连续线段、五连和长连。
- [x] 直线型活三、活四。
- [x] Position、合法着法、终局、和棋和 Reachable。
- [x] 终局后无合法着法。
- [x] 轮次/棋子数量不变量。
- [x] 每步严格减少空点。
- [x] ForceWin 和 CanForceWin。
- [x] 立即胜着定理。
- [x] 直线型活四产生黑棋立即胜着的证明。
- [x] CertificateTree 及其 soundness。
- [x] CompactCertificate 和结构性检查器。
- [x] 第一批对抗性反例、证书拒绝测试和战术合法性包装。
- [x] 两节点正向证书、`compact_reify_at` 重建回归测试，以及立即胜着证书生成器原型。
- [x] 横向、斜线、边界、六连、终局和非法着法测试。
- [x] lake build 全工程构建成功。

尚未完成：

- [x] 规范化见证及可比较起点下的唯一活三/活四定理。
- [x] 完整最大连续段关系及其可比较重叠起点的唯一性定理。
- [x] 断三、跳四的独立几何模式表和边界/直线反例。
- [x] 跳四填补缺口的立即胜着定理（`jumpFour_black_immediate`）。
- [ ] 完整双活三强制性定理。
- [x] 双活三多回合安全谓词和立即响应特例的博弈 soundness 定理。
- [x] 紧凑证书到 CertificateTree 的可信转换。
- [x] 外部搜索器与 Lean 校验器之间的最小适配接口。
- [x] 带硬节点预算、哈希置换表、迭代加深和统计信息的 Lean 搜索引擎。
- [x] 独立参数化棋盘/连珠规格，以及 5×5 五子棋两层搜索、检查和 soundness 闭环。
- [x] 空 5×5 五子棋的本地精确三值完整求解（计算结果：和棋）。
- [x] 5×5 静态配对证书和 6×6 全部首着对称类的“白方首应 + 配对”证书。
- [x] 7×7 Maker--Breaker AND/OR 搜索闭合（本地计算结果：和棋）。
- [x] 8×8 完成 20,000,000 节点受限基准并明确记录为 `unknown`。
- [x] 目标方立即胜着/强制防守剪枝、可选分支宽度和一步成五短路。
- [x] 置换表条目硬上限及饱和写入统计（尚无替换/淘汰策略）。
- [x] 搜索引擎候选树重新通过局部证书检查，并给出 `runCheckedEngine_sound`。
- [x] C++17 bitboard/DFPN 外部搜索器原型及不改变 `CompactCertificate` 的 Lean 导出器。
- [x] C++ OR/AND 两类生成证书通过 `checkLocalCertificateAt` 和 soundness 回归。
- [x] 有独立深度/节点预算的 C++ VCF 预搜索、DFPN 提示集成和六节点 Lean 回归。
- [x] 非终局合法着法存在性与默认合法策略接口。
- [x] CertificateTree 与 CanForceWin 的双向等价接口。
- [ ] 对称性压缩的独立正确性证明。
- [ ] 实际 15×15 策略证书。
- [ ] 空 5×5 和棋结果的 Lean 可检查证书与 soundness 定理。
- [ ] 8×8 本地完整闭合证明，以及小棋盘和棋树的 Lean 可检查证书格式。
- [ ] initial_black_wins。

---

## 12. 接下来怎么做

后续必须遵循“先基础、后战术、再证书、最后搜索”的顺序。

### 阶段 A：规范化几何

目标：同一条线只被统计一次，SingleOpenFour 和 DoubleOpenThree 的 card 有明确含义。

做法：

1. 定义连续段的规范起点，例如前一格不是同色或已经到边界。
2. 对起点沿同一段发生正偏移的情形定义 `StartShiftConflict`，证明可比较起点唯一；
   `MaximalRun` 现在显式记录连续性和两端不可延伸性，并有
   `maximalRun_unique_of_comparable`。
3. 修改 openThreeWitnesses/openFourWitnesses，只收集规范见证。
4. 将 `step` 的前一格和偏移关系写成可复用引理。
5. 对四个方向分别补正例、边界反例和长连测试。

完成标准：重复起点不会重复计数，边界行为由定理而不是注释决定。该标准已达到；
分离的同方向连续段仍被允许同时存在。

### 阶段 B：逐级完成局部战术

目标：把“看起来必胜”变成显式前提和可检查证明。

顺序：

1. 保持立即胜着定理作为最底层战术。
2. 为直线型活四补充白棋和四方向的对称版本。
3. 明确单活四的当前回合、非终局、对手立即胜着排除条件。
4. 证明一次落子产生两个不同活三见证。
5. 证明一次对手落子不能同时堵住两个独立胜点。
6. 排除对手防守时同时产生立即胜着或反击四。
7. 将这些引理组合成 `SafeDoubleOpenThree` 的完整定理（多回合安全谓词和
   `safeDoubleOpenThree_forces_win` 已完成；立即胜着特例
   `ImmediateSafeDoubleOpenThree` 及其蕴含关系也已完成）。
8. 继续证明几何双活三到安全谓词的充分性；若标准直线活三不足以支持该结论，
   必须新增独立的威胁/反击模式，而不能把断三或跳四隐式并入当前定义。

当前已增加 `FourExtensionCells` 作为中间威胁层。`straightOpenThree_has_fourExtension`
证明每个直线活三至少有一个形成四连的扩展点；`HasDoubleFourThreat` 只表达存在
两个扩展点，不能单独推出 `CanForceWin`。十字双活三反例同时验证：该局面有多个
四连扩展点，但没有立即成五的 `WinningCells`，因此几何双活三不能被错误提升为
立即双威胁。

当前已加入 `brokenOpenThree` 和 `jumpFour` 两个独立模式。`jumpFour` 已有
`jumpFour_black_immediate`：在黑棋回合、非终局且模式成立时，填补唯一缺口立即形成
五连。`brokenOpenThree_has_fourExtension` 证明断三的内部缺口可以形成四连；
`OpenFourExtensionCells` 和 `openFourExtension_has_winningCell` 进一步记录方向性
开放四并给出至少一个立即成五点。`BrokenOpenThreeMove`、`SafeBrokenOpenThree`、
`safeBrokenOpenThree_forces_win` 以及 `ImmediateSafeBrokenOpenThree` 已把断三接入
合法着法和显式防守后博弈语义；剩余工作是继续冻结更多断三变体并为它们补齐独立的
反击排除条件，不能因为存在任意几何断三就直接宣称必胜。

每一个战术都要有正例、边界反例、断三反例，以及对手已有立即胜着时不触发的语义反例。

### 阶段 C：小型策略证书（可信转换已完成）

目标：先验证证书 soundness，不直接搜索 15×15。

做法：

1. 手工构造浅层 CertificateTree。
2. 构造错误终局、错误边、非法着法、缺分支和循环的 CompactCertificate。
3. 确认错误证书被 Bool 检查器拒绝。
4. 实现按节点索引逆序的 DAG 递归：子节点索引必须大于父节点，所以构造父节点时子树已经可用。
5. 让递归函数返回 CertificateTree，而不只是 Bool。
6. 证明小证书的 compact soundness（已由 `compact_certificate_sound` 覆盖）。
7. 使用 `immediateWinCertificate` 生成两节点候选，验证“外部生成、Lean 检查、策略树重建”的最小闭环。

完成标准：能够从通过检查的紧凑证书得到 `CanForceWin`；当前统一接口
`compact_certificate_sound` 已达到这一标准。

### 阶段 D：完成紧凑证书可信转换（已完成）

目标：把结构检查升级为真正的 soundness。该阶段已完成，关键结果是
`compact_certificate_sound`。

需要证明：

1. 引用索引都在数组范围内。
2. 子索引大于父索引，因此没有循环。
3. childPositionMatches 可转换为位置相等式。
4. terminal 节点标签正确。
5. proverMove 节点的着法合法且子树成立。
6. opponentMoves 节点覆盖全部合法对手着法。
7. 根节点是 initialPosition，目标是黑棋。

实现采用以下思路：

- 对节点索引或剩余节点数量做归纳。
- 使用 Fin 表示已经证明有效的数组索引。
- 对每个节点返回依赖类型 CertificateTree。
- 把 Bool 检查结果拆成一组显式等式和 forall 证明。
- 直接按严格递增索引处理数组 DAG；共享子树通过索引复用，不需要复制证明对象。

最终接口已经是：

~~~lean
theorem compact_certificate_sound
    (h : checkCertificate c = true) :
    CanForceWin initialPosition .black
~~~

下一阶段不再修改这条 soundness 链，而是生成并导入真实的策略证书。

### 阶段 E：外部搜索器

目标：让搜索器生成候选证书，但不把搜索器本身作为可信基础。

当前已提供 `Gomoku.Search` 适配层、最小可执行搜索原语和 C++ DFPN 原型，但尚未实现
完整的 15×15 策略搜索。Lean 侧现有原语包括：

- `coordAtIndex`/`allCoords`：用 `Fin 225` 构造完整棋盘坐标，避免依赖
  `Finset.toList` 的不可执行路径。
- `candidateMoves`：只在轮到目标玩家且局面非终局时返回合法空点。
  `mem_candidateMoves_iff` 将数组成员精确对应为轮次、完整坐标表成员和 `legalMove`；
  `candidateMovesFast` 复用一次位置级终局检查，`mem_candidateMovesFast_iff` 及其与参考
  实现的等价引理保证优化不改变候选集合；`orderedCandidateMoves` 在搜索中优先尝试
  局部邻近点，但不删除远处着法；`immediateWinningMovesFirst` 再把直接成五的着法
  提到最前；`tacticalCandidateMovesFast` 则在同一候选全集中把对手立即胜点防守提前。
- `firstWinningMove`：扫描候选着法寻找立即胜着。
- `immediateCertificateFor`：把局部立即胜着包装成候选 `CompactCertificate`。
  该候选的根可以是局部位置，所以只能用 `checkNodeAt` 做局部检查；全局
  `checkCertificate` 仍要求根是空棋盘黑先。
- `immediateCertificateNodesChecked_sound`：从两个局部节点的 Bool 检查结果提取
  合法落子和终局胜负事实，并推出该局面的 `CanForceWin`；它不放宽全局证书的根约束。

后续完整搜索仍应遵循：

1. 优先生成 Lean 源码中的 `CompactCertificate` 值，避免未经验证的文本解析器；
   搜索器可以实现为 `Searcher`，结果通过 `CheckedSearchResult` 或
   `acceptCertificate` 进入 Lean。
2. 搜索器优先处理立即胜着和必须防守的对手威胁。
3. 使用置换表和局面缓存减少重复局面。
4. 先不把旋转/反射压缩放入可信内核。
5. 如果加入对称性压缩，必须另外证明坐标变换保持合法着法、终局和 CanForceWin。
6. 搜索器输出后，所有可信结论仍由 Lean 重新检查。

本阶段新增的最小可复用接口：

```lean
def checkLocalCertificate (c : CompactCertificate) : Bool
def twoPlyImmediateCertificate (s : Position) (p : Player)
    (responses : Array (Coord × Coord)) : CompactCertificate
def immediateResponseTable (s : Position) (p : Player) :
    Option (Array (Coord × Coord))
def twoPlyCertificateFor (s : Position) (p : Player) :
    Option CompactCertificate
```

`twoPlyImmediateCertificate_sound` 和 `checkedTwoPlyCertificateFor_sound`
把通过检查的局部两层证书连接到 `CanForceWin`。生成器只负责提出候选表；
合法性、终局、索引严格递增、子位置匹配以及对手应手全覆盖仍由 Lean
检查器负责。`Adversarial.lean` 中的 `generatedForkCertificate` 是这一接口
的回归样例。

有限深度搜索接口为：

```lean
inductive CandidateTree
def searchCandidateTree (fuel : Nat) (s : Position) (target : Player) :
    Option CandidateTree
def checkedDepthCertificateFor (fuel : Nat) (s : Position) (target : Player) :
    Option CompactCertificate
theorem checkedDepthCertificateFor_sound ... : CanForceWin s target
```

`fuel` 是搜索深度上限，不是可信证明的假设；深度不足时搜索返回 `none`。
每个成功结果仍要通过 `checkLocalCertificateAt`，因此搜索树的递归实现和启发式
可以以后替换，而不改变可信证明层。

在上述基础接口之上，`Gomoku.Engine` 提供面向实际试验的入口：

```lean
structure EngineConfig where
  maxDepth : Nat
  maxNodes : Nat
  maxMemoEntries : Nat
  memoCapacity : Nat
  maxProverMoves : Nat
  useThreatOrdering : Bool
  useForcedMovePruning : Bool

def runEngine (cfg : EngineConfig) (s : Position)
    (target : Player) : EngineReport
def runCheckedEngine (cfg : EngineConfig) (s : Position)
    (target : Player) : CheckedEngineResult
theorem runCheckedEngine_sound ... : CanForceWin s target
```

迭代深度从 0 增长到 `maxDepth`。`maxNodes = 0` 表示不设节点上限；其他值是跨所有
迭代共享的硬预算。置换表只缓存已经得到 `found` 或 `notFound` 的完整搜索结果，不缓存
因预算耗尽产生的 `cutoff`。`EngineSearchKey` 仍包含“剩余深度 + 目标方 + 完整局面”，但
完整局面由轮次和双方共八个 64 位占位字表示；根局面扫描一次，递归落子增量更新。命中后的
候选树最终还要重新编译并通过 `checkLocalCertificateAt`。`memoCapacity` 仅是哈希表初始
容量；`maxMemoEntries = 0` 表示不限制，否则是新建引擎缓存的条目硬上限。缓存饱和时已有
键仍可更新，新键写入被跳过并累计到 `memoStoreSkips`；当前尚未实现替换或淘汰策略。

`useForcedMovePruning` 只作用于目标方节点：目标方已有一步胜着时只需搜索这些胜着；目标方
没有一步胜着而对手已有一步胜点时，任何获胜策略都必须占据防守点，因此只搜索这些点。
对手节点始终使用包含全部合法着法的 `engineCandidateMoves`，以满足证书的全应手覆盖。
`maxProverMoves = 0` 不限制目标方宽度；正值在上述分组后截取前若干着法，是可能漏解但保持
soundness 的选择性搜索开关。搜索器的 `found` 只有通过证书检查才进入定理层；受限配置的
`notFound` 不能解释为局面不可胜。

当前回归覆盖三个层次：固定五节点对手分支树验证编译器和检查器，两个空点局面的
深度 2 搜索验证递归搜索的最小闭环。`tacticalCandidateMovesFast` 已把对手立即胜点
预先扫描为固定长度掩码，并由成员等价性定理保证不改变候选集合；掩码构造目前仍会
重新计算整盘威胁，且尚无增量威胁缓存，所以它目前作为可选实验接口，不接入默认深搜。这不意味着
已经有可扩展的 15×15 求解器，也不改变外部搜索器不属于可信基础的约定。
`Gomoku.Engine` 另用一手立即胜局面验证：深度 1、2 个节点可找到并接受证书；1 个节点
会准确报告 `nodeLimit`；`maxProverMoves = 1` 只保留首个立即胜着；轮到白棋的镜像局面
只返回两个强制防守点，而未剪枝的对手候选仍有 221 个。置换表上限为 1 时保持 1 个条目并
记录 1 次跳过写入；复用首次运行的置换表后可用 0 个新节点、2 次缓存命中返回结果。新增
紧凑键回归跨越全部四个 64 位分块，并验证八步增量更新与从最终棋盘重新编码完全一致。
这些测试验证控制流、剪枝和缓存行为，不等同于完整开局求解。

外部搜索器位于 `cpp/`。位置文件明确给出 `turn`、`target` 和按 `y = 0..14` 排列的
15 行棋盘，使用 `X`/`O`/`.` 表示黑/白/空。第一版算法和接口为：

1. 双方各用四个 64 位字保存 225 个棋盘点，落子时增量更新 Zobrist 哈希；
2. 置换表键仍保存完整双方 bitboard、轮次、目标方和剩余深度，哈希只影响桶选择；
3. 迭代深度 DFPN 使用 proof/disproof number 引导 AND/OR 展开；
4. 有界 VCF 预搜索识别立即胜和连续冲四链，结果只用于目标方着法排序；VCF 深度与节点数
   独立设限，耗尽时 DFPN 继续运行；
5. DFPN 节点数、置换表条目数和输出证书节点数分别设限，并报告不同退出状态；
6. 输出器把根棋盘写成落子数组，把每个后继位置写成前一位置的 `play`，最后生成现有
   `terminal`/`proverMove`/`opponentMoves` 节点和 Lean 检查定理。

构建、输入格式和命令行参数见 `cpp/README.md`。当前 C++ 单元测试覆盖成五几何、位置解析、
两节点 OR 证书、五节点 AND 证书、六节点 VCF 证书以及节点/置换表/证书/VCF 资源上限。
开放四回归中，VCF 提示把 DFPN 展开节点从 13 降到 7；VCF 预算耗尽或关闭时，完整 DFPN
仍能生成同一证明。尚未加入 VCT、并行搜索、置换表替换策略和证书 DAG 共享；因此这是可验证接口和性能数据结构原型，
还不是完整开局求解器。C++ 的 `depthLimit` 或资源上限只表示没有找到证明，不能推出不可胜。

参数化小棋盘和棋搜索器是与上述 15×15 DFPN/Lean 导出器分开的实验工具，详见
`cpp/tools/README.md`。它已经给出 5×5、6×6、7×7 的可复现本地和棋计算结果；其中
配对证书会在 C++ 内部重新验证，7×7 的 r-zone 树仍未序列化成 Lean 证书。8×8 当前记录
为预算耗尽的 `unknown`，不能据此推断黑胜或和棋。

### 阶段 F：导入证书并证明最终定理

当真实证书已经产生并可存储时：

1. 将证书作为 Lean 源码中的常量导入。
2. 运行并证明 checkCertificate。
3. 使用 compact_certificate_sound。
4. 证明根节点等于空棋盘黑先。
5. 最后声明 initial_black_wins。

在此之前不能用以下内容代替正式定理：

- 普通程序搜索得到黑胜。
- 启发式搜索没有找到反例。
- 人类棋谱或经验。
- 只检查一条黑棋主线而没有覆盖所有白棋应对。
- 只检查证书格式但没有构造 CertificateTree。

---

## 13. 验收标准

### 规则层

必须覆盖：

- 空棋盘首着、轮次和棋子数量。
- 横、竖、两种斜线五连。
- 六连和更长连。
- 落子后立即终局。
- 终局后禁止继续走棋。
- 满盘无胜为和棋。
- 已占用点、错误轮次和错误棋子数量。
- 可达局面不变量。
- 空点数严格减少。

### 图形层

必须覆盖：

- 直线型活三正例。
- 直线型活四正例。
- 边界封闭端反例。
- 断三不自动识别为直线型活三。
- 同一线段不重复计数。
- 对手已有立即胜着时安全定理不能误触发。

### 证书层

错误证书必须拒绝：

- 根索引越界。
- 根位置不是空棋盘黑先。
- 终局标签错误。
- 非法落子。
- 子位置不匹配。
- 缺少合法防守分支。
- 索引循环。
- 引用不存在的节点。
- proverMove 没有合法目标着法。

---

## 14. 如何运行和验证

在项目根目录 D:\LeanProjects 运行：

~~~text
lake build
~~~

只要本地 Lean 和 mathlib 已安装，网络自更新检查失败不影响本地构建。成功标志是：

~~~text
Build completed successfully.
~~~

也可以单独编译：

~~~text
lake env lean Gomoku/Basic.lean
lake env lean Gomoku/Rules.lean
lake env lean Gomoku/Tactics.lean
lake env lean Gomoku/Certificate.lean
lake env lean Gomoku/Examples.lean
~~~

---

## 15. 当前结论

项目已经完成可信的规则与局部战术基础：棋盘、规则、终局、可达性、有限博弈语义、活四证明和策略树接口都已经在 Lean 中存在并通过构建。

项目没有提前夸大结论：

- 没有实际 15×15 必胜策略证书。
- 没有 initial_black_wins。
- 紧凑证书检查器已经通过 `compact_reify_at` 连接到 `CertificateTree`，并由
  `compact_certificate_sound` 给出可信的全局 soundness。
- v1 活三/活四只覆盖冻结的直线型模式。

项目已经完成规则、几何、博弈、证书和对抗性审计的核心工作；当前处于阶段 9，正在
扩展可验证的搜索器并优化候选生成。完整路线是：

~~~text
规范化几何（已完成 v1）
  -> 局部战术和反例审计（核心已完成，模式继续扩展）
  -> 小型证书 soundness（已完成）
  -> 紧凑证书可信转换（已完成）
  -> 外部搜索器生成更深证书（当前）
  -> 外部搜索器生成 15×15 证书
  -> Lean 检查证书
  -> 证明 initial_black_wins
~~~

每一个中间阶段都可以独立验收；任何尚未获得的结论都不会被提前写成定理。
