# 五子棋形式化建模与证明逻辑导读

本文按“问题建立 → 数学建模 → Lean 形式化 → 战术证明 → 证书检查 → 搜索生成”的顺序解释项目。
源码中的每个定义、函数、定理和回归 `example` 后面已有中文注释；本文负责说明它们为什么按这个顺序出现，以及各层如何共同组成可信证明。

## 1. 问题建立：究竟要证明什么

项目研究 15×15 无禁手五子棋，规则冻结为：

- 黑方先行，双方交替在空点落子；
- 任一方向出现连续至少五颗同色棋子时，该玩家获胜；
- 六连及更长连仍算胜利；
- 没有三三、四四、长连等禁手；
- 无人获胜而棋盘填满时为和棋；
- 终局之后不能继续合法落子。

最终希望建立的命题是：

```lean
CanForceWin initialPosition .black
```

它表示黑方从空棋盘初始局面出发，存在一个对所有白方合法应手都能获胜的策略。

当前项目**尚未**声明 `initial_black_wins`，因为还没有导入覆盖完整 15×15 对局树的实际策略证书。已经完成的是规则、局部战术、搜索器边界和证书检查器的可靠性：一旦将来有证书 `c` 满足

```lean
checkCertificate c = true
```

Lean 已能严格推出：

```lean
CanForceWin initialPosition .black
```

因此，项目当前证明的是“检查通过的证书必然正确”，而不是在没有证书时提前断言先手必胜。

## 2. 整体分层与依赖关系

核心依赖链如下：

```text
Basic（棋盘数据）
  ↓
Geometry（方向、连子和棋形）
  ↓
Rules（局面、合法落子、终局、可达性）
  ↓
Game（策略与 AND/OR 强制胜语义）
  ↓
Tactics（立即胜、双威胁、安全棋形）
  ↓
Certificate（可执行检查器及 soundness）
  ↑
Search / Engine / C++（不可信地寻找候选证明）
```

各模块职责如下：

| 模块 | 主要问题 | 关键输出 |
| --- | --- | --- |
| [`Basic`](Gomoku/Basic.lean) | 棋盘和落子数据怎样表示？ | `Player`、`Cell`、`Coord`、`Board` |
| [`Geometry`](Gomoku/Geometry.lean) | 怎样定义方向、连子和局部棋形？ | `step`、`consecutive`、`hasAtLeastFive`、开放三/四等 |
| [`Rules`](Gomoku/Rules.lean) | 什么是局面、合法着法和终局？ | `Position`、`legalMove`、`play`、`Reachable` |
| [`Game`](Gomoku/Game.lean) | “无论对手如何走都能赢”怎样表达？ | `Strategy`、`ForceWin`、`CanForceWin` |
| [`Tactics`](Gomoku/Tactics.lean) | 局部棋形怎样连接到强制胜？ | `WinningMoves`、`WinningCells`、安全战术定理 |
| [`Certificate`](Gomoku/Certificate.lean) | 怎样检查外部生成的有限证明？ | `CompactCertificate`、`checkCertificate`、soundness |
| [`Search`](Gomoku/Search.lean) | Lean 内怎样生成候选证明？ | 候选枚举、快速五连、有限深度搜索 |
| [`Engine`](Gomoku/Engine.lean) | 怎样加入预算、换位表和迭代加深？ | 可观测的预算搜索与已检查结果 |
| [`Generated`](Gomoku/Generated) | C++ 生成的数据能否被 Lean 接收？ | 2、5、6 节点局部证书回归 |
| [`Examples`](Gomoku/Examples.lean) | 基本 API 是否符合预期？ | 正向小例子 |
| [`Adversarial`](Gomoku/Adversarial.lean) | 错误证书和过强语义是否会被拒绝？ | 正反例与语义边界审计 |

## 3. 基础数据建模：玩家、坐标与棋盘

### 3.1 玩家和棋盘格

`Player` 只有 `.black` 和 `.white` 两个构造子。`Player.other` 交换双方，定理 `other_other` 保证：

```text
other (other p) = p
```

`Cell` 是空格 `.empty` 或棋子 `.stone p`。`Cell.owner` 把格子投影为 `Option Player`。

### 3.2 有界坐标

```lean
abbrev Coord := Fin 15 × Fin 15
```

`Fin 15` 把每个坐标分量限制在 `0` 到 `14`。越界坐标无法构造，因此大部分边界合法性直接由类型系统承担。

### 3.3 函数式棋盘

```lean
structure Board where
  cell : Coord → Cell
```

棋盘不是可变数组，而是从坐标到格子的纯函数。`Board.empty` 在每个坐标返回空格；`Board.place b c p` 返回一个新棋盘：坐标 `c` 为玩家 `p` 的棋子，其余坐标与 `b` 相同。

这里有一个重要设计边界：`Board.place` 本身允许覆盖已有棋子，它只是数据更新函数。是否允许在 `c` 落子由更高层的 `legalMove` 决定。这样底层函数简单可证，同时规则层不会把覆盖当作合法对局。

关键基础定理包括：

- `place_same`：更新后目标格是新棋子；
- `place_other`：其他格保持不变；
- `place_commute_of_ne`：不同坐标上的两次更新可交换；
- `count_place_same_of_empty`：在空点给 `p` 落子后，`p` 的棋子数增加一；
- `count_place_other_of_empty`：另一玩家的棋子数不变；
- `emptyCount_place_of_empty`：空点数恰好减少一。

最后一条后来成为策略递归和证书树证明的良基度量。

## 4. 几何形式化：从步进到棋形

### 4.1 四个方向与有界步进

`Direction` 固定四个无向连线方向：横、竖、上升对角线和下降对角线。每个方向由 `dx`、`dy` 给出单位向量。

从坐标 `c = (x,y)` 沿方向 `d` 移动整数 `n` 步，目标坐标为：

```text
(x + n · dx(d), y + n · dy(d))
```

`step c d n : Option Coord` 只在结果仍位于棋盘内时返回 `some q`，否则返回 `none`。`step_reverse` 证明有效步进可以用 `-n` 撤销。

### 4.2 连续棋子和胜利线

`occupiedAt b p c d n` 表示从 `c` 沿 `d` 偏移 `n` 的有效坐标上有玩家 `p` 的棋子。

```lean
consecutive b p c d length :=
  ∀ n : Fin length, occupiedAt b p c d n.1
```

于是：

```lean
hasRun b p length := ∃ c d, consecutive b p c d length
hasAtLeastFive b p := hasRun b p 5
```

尽管名字是“至少五连”，实现只寻找任意五格连续窗口；六连或更长连必然包含五格窗口，因此自然被判为获胜。

`hasAtLeastFive_of_place_other` 是后续规则证明的重要单调性引理：给另一玩家落子不可能凭空为 `p` 新建五连，所以更新后若有 `p` 的五连，更新前已经存在。

### 4.3 开放端与冻结棋形

`openEnd b c d n` 表示对应偏移位置在棋盘内且为空。

在此基础上定义：

- `straightOpenThree`：连续三子，前后两端都为空；
- `straightOpenFour`：连续四子，前后两端都为空；
- `brokenOpenThree`：三个棋子带一个内部缺口，且缺口与相关端点为空；
- `jumpFour`：五格窗口已有四子和一个内部缺口，同时两端为空。

断三和跳四是显式有限析取的“冻结模式”。这意味着定义只覆盖源码列出的变体；若要纳入新的民间棋形命名，必须增加明确模式并单独证明，而不会被模糊地自动归入。

### 4.4 规范化和重复计数

`canonicalRunStart` 要求起点前一格不是同色棋子。`normalizedStraightOpenThree` 和 `normalizedStraightOpenFour` 把棋形与规范起点结合，供有限见证集合使用。

`MaximalRun`、`StartShiftConflict`、`ComparableRunStarts` 及相关唯一性定理排除同一连续段因平移起点而重复计数，但允许同方向上真正分离的两条棋线同时存在。

## 5. 规则层：局面、终局、合法性和可达性

### 5.1 局面和初始状态

```lean
structure Position where
  board : Board
  turn : Player
```

`initialPosition` 是空棋盘且轮到黑方。

### 5.2 终局

命题形式的终局定义是：

```text
IsTerminal(s)
  ⇔ black 有至少五连
   ∨ white 有至少五连
   ∨ 棋盘已满
```

可执行函数 `terminal` 依次检查黑胜、白胜和满盘和棋，非终局返回 `none`。

表面上黑胜检查在白胜之前，但 `reachable_not_both_winners` 已证明任何合法可达局面不可能双方同时五连，因此该优先次序不会在合法对局中任意选择胜者。

### 5.3 合法落子和状态转移

```lean
legalMove s c := ¬ IsTerminal s ∧ s.board.cell c = .empty
```

```lean
play s c := ⟨s.board.place c s.turn, Player.other s.turn⟩
```

再次强调，`play` 是原始状态更新；定理若要把它解释为真实对局一步，必须携带 `legalMove s c`。`Adversarial.lean` 专门保存“覆盖已有棋子后几何上看似成四”的反例，防止以后遗漏这个前提。

### 5.4 可达性和不变量

`Reachable` 是归纳谓词：初始局面可达；从可达局面执行合法落子得到的局面仍可达。

主要不变量是：

```text
s.turn = black  ⇒ countBlack(s) = countWhite(s)
s.turn = white  ⇒ countBlack(s) = countWhite(s) + 1
```

另有：

- `play_not_both_winners`：一次合法落子后不会双方同时五连；
- `reachable_not_both_winners`：任意可达局面都不会双方同时五连；
- `exists_legalMove_of_terminal_none`：非终局局面至少有一个合法落子；
- `play_emptyCount_lt`：合法落子后空格数严格下降。

因此游戏树最大深度有限，后续可用空格数证明递归终止。

## 6. 博弈语义：把“必胜”写成 AND/OR 树

### 6.1 策略接口

`Strategy target` 要求在任一可达、轮到 `target` 且未终局的局面返回一个带合法性证明的坐标：

```lean
∀ s, Reachable s → s.turn = target → terminal s = none →
  {m : Coord // legalMove s m}
```

`defaultStrategy` 只利用“非终局必有合法步”选择任意一步。它是合法性基线，不是获胜策略。

### 6.2 `ForceWin` 的三个构造子

`CanForceWin s target` 是 `ForceWin target s` 的包装。其证明树有三种节点：

1. `terminal`：当前局面已经是 `target` 获胜；
2. `choose`：轮到 `target`，存在一个合法着法，其子局面仍能强制胜；
3. `respond`：轮到对手，对手的**每一个**合法着法对应的子局面都能强制胜。

所以证明方节点是 OR：找到一个成功分支即可；对手节点是 AND：必须覆盖全部合法应手。

```text
target 回合：∃ 合法 m, 子局面获胜
对手回合：  ∀ 合法 m, 子局面获胜
```

`canForceWin_immediate` 是最常用的局部桥：如果轮到目标玩家且有一步合法着法直接形成目标玩家获胜终局，则当前局面可强制胜。

### 6.3 抽象获胜树与具体策略等价

`canonicalWinningStrategy` 从 `CanForceWin` 中非计算地选择保持获胜的着法；不在获胜区域时退回 `defaultStrategy`。

`StrategyRealizes σ s hs` 要求目标方节点严格采用策略 `σ` 给出的落子，对手节点仍覆盖全部合法回复。

最终得到：

```lean
(∃ σ : Strategy target, StrategyRealizes σ s hs)
  ↔ CanForceWin s target
```

正向由 `StrategyRealizes.sound` 遗忘具体策略信息；反向用 `Board.emptyCount` 严格下降，对 `CanForceWin` 树递归构造规范策略的实现证明。

## 7. 战术层：从几何威胁到游戏结论

### 7.1 三种容易混淆的集合

| 名称 | 是否要求轮到 `p` | 落子后的目标 | 用途 |
| --- | --- | --- | --- |
| `WinningMoves s p` | 是 | `terminal (play s c) = winner p` | 当前回合的一步胜着 |
| `WinningCells s p` | 否 | 假设放入 `p` 后形成五连 | 对手回合仍存在的几何制胜点 |
| `FourExtensionCells b p` | 否 | 放入 `p` 后形成四连 | 开放三到四威胁的中间层 |

这个区分非常关键：黑方刚制造双威胁后轮到白方，此时 `WinningMoves s .black` 会因轮次不符而为空，但 `WinningCells s .black` 仍应记录白方必须防守的两个点。

### 7.2 双威胁强制胜

```lean
HasDoubleThreat s p := 2 ≤ (WinningCells s p).card
```

核心证明 `doubleThreat_forces_win` 的逻辑是：

1. 由至少两个不同制胜点，对任意对手防守坐标 `r` 选出另一个点 `m ≠ r`；
2. `play_preserves_other_cells` 保证对手在 `r` 落子后 `m` 仍为空；
3. 在排除对手立即胜的前提下，`terminal_none_after_doubleThreat` 证明防守后的局面仍可继续；
4. 目标玩家在 `m` 合法落子并形成五连；
5. 对每个对手合法应手都构造一个 `canForceWin_immediate`；
6. 用 `ForceWin.respond` 组合为对手节点的完整强制胜树。

`doubleThreat_move_forces_win` 再在外层增加目标玩家制造双威胁的第一步，对应一个 `ForceWin.choose` 节点。

### 7.3 开放三、开放四和安全包装

几何定理逐级建立：

```text
straightOpenThree
  → 存在 FourExtensionCells

brokenOpenThree
  → 存在 FourExtensionCells

straightOpenFour
  → 存在 WinningCells
```

但几何双开放三本身不自动推出强制胜。项目把接口拆为：

- `GeometricDoubleOpenThree`：只看落子后有两个开放三见证；
- `DoubleOpenThree`：增加正确轮次和落子合法性；
- `SafeDoubleOpenThree`：再要求落子后非终局、对手没有立即胜，且每个防守后的局面仍有 `CanForceWin`；
- `ImmediateSafeDoubleOpenThree`：更强，要求每个防守后已经有 `HasImmediateWin`。

断三有平行的 `GeometricBrokenOpenThree`、`BrokenOpenThreeMove`、`SafeBrokenOpenThree` 和 `ImmediateSafeBrokenOpenThree` 接口。

`safeDoubleOpenThree_forces_win` 与 `safeBrokenOpenThree_forces_win` 的本质不是从名称猜测必胜，而是把谓词中已经显式提供的“所有对手应手均获胜”装配为 `ForceWin.respond`。这避免把民间棋形直觉当作未证明的数学结论。

## 8. 证书层：把不可信数据变成可信定理

### 8.1 依赖类型证书树

`CertificateTree target s` 与 `ForceWin target s` 结构对应，但类型索引直接记录当前局面。它的 `terminal`、`proverMove`、`opponentMoves` 三类节点携带所有证明义务。

```lean
Nonempty (CertificateTree target s) ↔ CanForceWin s target
```

正向由 `CertificateTree.sound` 给出；反向由 `ForceWin.nonemptyCertificateTree` 给出。使用 `Nonempty` 是因为从命题证明中提取数据需要保持 Lean 的 Prop 消去限制。

### 8.2 紧凑可执行表示

真实搜索器不能方便地直接构造依赖类型证明，因此另定义：

```lean
inductive CertificateNode
  | terminal (position) (winner)
  | proverMove (position) (move) (childIndex)
  | opponentMoves (position) (Array (move × childIndex))

structure CompactCertificate where
  target : Player
  root : Nat
  nodes : Array CertificateNode
```

这只是普通数据，可能包含遗漏应手、非法落子、伪造终局、错误局面、越界引用或循环引用，因此不能直接信任。

### 8.3 检查器验证什么

`checkNode` 检查单节点语义：

- 终局节点的实际结果与目标胜者一致；
- 证明方节点处于非终局、轮到目标玩家、落子合法且引用有效；
- 对手节点处于非终局、轮到对手、每个列出的落子合法，并覆盖所有合法落子。

`checkEdgesAt` 另外检查：

- 每个子引用严格大于父索引，排除自环和回边；
- 子节点记录的局面等于执行父边落子后的实际局面。

`samePosition` 对轮次和全部 225 个格子进行精确比较。`checkLocalCertificateAt s c` 还要求证书根局面等于指定的 `s`。

全局 `checkCertificate` 比局部检查多两个要求：目标必须是黑方，根局面必须是 `initialPosition`。

### 8.4 从布尔检查到证明树

可靠性链按以下顺序建立：

```text
布尔数组检查为 true
  ↓  allRefsValid_true_iff / allMovesLegal_true_iff / ...
每个节点的命题条件成立
  ↓  checkNodeAt_*_iff
节点语义、边顺序和子局面匹配成立
  ↓  compact_reify_at
Nonempty (CertificateTree target rootPosition)
  ↓  CertificateTree.sound
CanForceWin rootPosition target
```

`compact_reify_at` 以 `nodes.size - index` 为严格下降量。因为检查器要求 `parent < child`，沿证书边向下时该度量严格减小，所以重构不会陷入循环。

最终两个边界定理是：

```lean
checkLocalCertificateAt s c = true
  → CanForceWin s c.target

checkCertificate c = true
  → CanForceWin initialPosition .black
```

搜索器、哈希、剪枝和序列化都可以出错；只要检查器及上述 soundness 证明正确，错误候选只会被拒绝，不能变成假定理。

## 9. Lean 搜索层：生成候选树，但不扩大可信基

### 9.1 坐标枚举与精确局面键

`coordAtIndex` 与 `coordIndex` 在 `Fin 225` 和 `Coord` 之间按行优先顺序转换，两个逆定理保证它们构成双射。

`PositionKey` 保存行棋方和完整的 225 格 `Vector Cell`。`boardKey_eq_iff` 与 `positionKey_eq_iff` 证明键相等当且仅当原棋盘或局面相等，所以换位表逻辑不依赖可能碰撞的简化状态。

### 9.2 候选生成只允许重排，不允许漏掉对手应手

`candidateMoves` 是直接参考实现。`candidateMovesFast` 把局面级终局检查移出逐格过滤；`mem_candidateMovesFast_iff_mem_candidateMoves` 证明二者成员完全一致。

排序层依次加入：

- `orderedCandidateMoves`：邻近已有棋子的着法优先；
- `immediateWinningMovesFirst`：立即胜着优先；
- `tacticalCandidateMovesFast`：胜着、防守点、普通步分组。

每一层都有 `mem_*_iff` 定理证明成员集合不变。尤其在对手节点，证书要求全部合法回复，不能因启发式排序而删除分支。

### 9.3 快速五连检测

`createsFiveFast b p m` 只检查包含新落子 `m` 的窗口：4 个方向，每个方向至多 5 个起点，共至多 20 个五格窗口。

在原棋盘没有玩家 `p` 的旧五连时：

```lean
createsFiveFast b p m = true
  ↔ hasAtLeastFive (b.place m p) p
```

再加上轮次和合法落子前提，`createsFiveFast_terminal_iff` 把它连接到 `terminal (play s m) = some (winner p)`。因此快速函数适合搜索排序；最终证书检查仍重新验证真实终局。

### 9.4 从一步到有限深度

搜索构造逐级扩展：

1. `immediateWinCertificate`：一步胜着的两节点证书；
2. `twoPlyImmediateCertificate`：对手全部应手后，我方每条分支立即获胜；
3. `CandidateTree`：一般的终局、证明方选择和对手全分支树；
4. `candidateTreeCertificate`：把树以前序方式展平为父节点在前、子引用严格向后的数组；
5. `searchCandidateTreeMemoized`：有限深度 AND/OR 递归并携带记忆表；
6. `checkedDepthCertificateFor`：编译候选树并调用 `checkLocalCertificateAt`。

`SearchKey` 包含剩余深度、目标玩家和完整局面。缓存中保存的失败 `none` 与“没有该键”分开表示；但无论缓存命中与否，找到的候选树都必须再次经过证书检查。

## 10. Lean 引擎层：预算、换位表和迭代加深

`Engine` 在基础搜索上增加：

- `maxDepth` 和 `maxNodes`；
- `maxMemoEntries` 与初始哈希表容量；
- 双方各四个 `UInt64` 的紧凑换位表局面键；
- 可选的证明方宽度 `maxProverMoves`；
- 战术排序和强制着法剪枝；
- 迭代加深；
- 节点数、缓存命中和跳过写入等统计。

递归结果明确分为：

```text
found     找到候选证明树
notFound  当前完整深度内未找到
cutoff    节点预算耗尽，搜索不完整
```

`cutoff` 不会被缓存为失败，避免资源不足污染后续搜索。证明方节点只需一个成功子树；对手节点必须让每个合法应手都成功。

基础 `SearchKey` 仍是便于证明的 225 格精确向量；生产型 `Engine` 使用等价信息布局的
`EngineSearchKey`：轮次、双方各四个 64 位占位字、目标玩家和剩余深度。迭代加深开始前只
扫描一次根棋盘，之后每次合法落子只设置一个 bit 并切换轮次。这样消除了递归换位表键的
225 格对象负担；它优化的是 Lean 内部数据布局，并不是消除当前并不存在的 FFI 共享缓冲区。

证明方的强制剪枝规则是：有立即胜着时只试胜着；否则若对手下一步可成五，优先只试防守点；再考虑普通步。`maxProverMoves > 0` 还可能主动限制证明方宽度，所以 `notFound` 可能只是“当前配置未找到”，不能推出不可胜。

安全边界不依赖搜索完备性：`runCheckedEngine` 把候选树重新编译并检查，`runCheckedEngine_sound` 只对检查通过的证书给出 `CanForceWin`。

## 11. C++ 搜索器：性能层与 Lean 接口

[`cpp/gomoku_solver`](cpp/README.md) 是不可信的 C++17 搜索器，采用：

- 双方 bitboard；
- 增量 Zobrist 哈希和精确 bitboard 键比较；
- 迭代深度 DFPN；
- 目标方 OR 节点、对手方 AND 节点；
- 立即胜和强制防守排序；
- 有界 VCF 预搜索作为目标方着法提示；
- 节点、换位表和导出证书的独立资源上限。

它不通过 FFI 进入 Lean，也没有新建另一套可信证书格式。接口就是：C++ 把搜索树导出成一个 `.lean` 文件，其中仍然是现有的 `CompactCertificate`；随后 Lean 编译该文件并运行原检查器。

因此性能优化与逻辑可信性分离：

```text
C++ / Lean 搜索器找到候选树
  → 导出 CompactCertificate
  → Lean 检查全部节点和全部对手应手
  → soundness 定理给出 CanForceWin
```

三个生成回归模块分别覆盖：

- `CppSmoke`：两节点立即胜；
- `CppFork`：五节点、对手两种应手全部覆盖；
- `CppVcf`：六节点连续冲四分支。

这些都是局部局面证书，不是空棋盘全局证书。

## 12. 正例与对抗性审计

`Examples.lean` 验证初始轮次、合法落子、四个方向、边界、长连、棋子计数、策略语义和基础证书接口。

`Adversarial.lean` 更重要的作用是防止不正确的概念升级：

- 原始 `play` 覆盖已有棋子后可能制造几何假象，但 `legalMove` 会拒绝该步；
- 几何双开放三不保证每个防守后都有立即胜；
- 几何好形可与对手已经存在的立即胜同时出现，所以安全谓词必须显式排除反击；
- `WinningCells` 与 `WinningMoves` 的轮次语义不能混用；
- 遗漏对手应手、越界引用、错误子局面、错误胜者标签和循环引用都被检查器拒绝；
- 局部根上的有效黑胜证书不能冒充以 `initialPosition` 为根的全局证书。

测试模块大量使用 `native_decide` 进行可执行回归。核心的 `compact_reify_at`、`compact_certificate_sound`、`local_certificate_at_sound` 等 soundness 定理本身不依赖 `native_decide` 或 C++。

## 13. 两条完整证明主线

### 13.1 数学策略主线

```text
棋盘与规则
  → Reachable 和合法落子不变量
  → ForceWin / CanForceWin
  → canonicalWinningStrategy
  → StrategyRealizes
  → “存在具体实现策略”与 CanForceWin 等价
```

这条线回答“`CanForceWin` 是否真的等价于存在一个对所有对手应手有效的策略”。

### 13.2 计算证书主线

```text
搜索器产生 CandidateTree 或 CompactCertificate
  → 检查合法落子、终局、全部对手应手、索引和子局面
  → compact_reify_at 重构 CertificateTree
  → CertificateTree.sound
  → CanForceWin
```

这条线回答“怎样让高性能但不可信的程序帮助 Lean 找证明”。

两条线在 `CanForceWin` 汇合：它既有标准策略语义，也是证书检查器的最终逻辑输出。

## 14. 当前完成度和剩余工作

| 状态 | 内容 |
| --- | --- |
| 已完成 | 15×15 无禁手规则、至少五连胜、合法落子与终局 |
| 已完成 | 可达性、棋子数/轮次不变量、空格数严格下降 |
| 已完成 | AND/OR 强制胜语义与具体策略语义等价 |
| 已完成 | 直开放三/四、冻结断三、跳四、双威胁和安全战术接口 |
| 已完成 | 紧凑证书的节点、边、根和对手覆盖检查 |
| 已完成 | 紧凑证书到 `CanForceWin` 的 Lean 内可靠性证明 |
| 已完成 | Lean 有限深度引擎和 C++ DFPN/VCF 原型的局部证书闭环 |
| 部分完成 | 棋形库只覆盖已经冻结并证明的模式，不代表所有命名变体 |
| 部分完成 | 搜索性能仍缺增量终局/威胁维护、缓存淘汰、多线程和证书 DAG 共享 |
| 未完成 | 真实空棋盘 15×15 黑方完整策略证书 |
| 未完成 | `initial_black_wins` 最终定理 |

下一阶段的正确完成条件不是搜索器打印 `found`，而是它产生一张以 `initialPosition` 为根、目标为黑方且能通过 `checkCertificate` 的完整证书。届时只需应用现有的 `compact_certificate_sound` 即可闭合最终定理。

## 15. 推荐阅读和验证顺序

建议依次阅读：

1. `Basic.lean`：理解函数式棋盘与落子更新；
2. `Geometry.lean`：理解 `step`、`consecutive` 和棋形；
3. `Rules.lean`：理解 `legalMove`、`play`、`Reachable`；
4. `Game.lean`：抓住证明方 OR、对手方 AND；
5. `Tactics.lean`：观察局部几何如何经过安全前提连接到 `CanForceWin`；
6. `Certificate.lean`：重点阅读 `checkNodeAt_*_iff`、`compact_reify_at` 和 soundness；
7. `Search.lean`、`Engine.lean`：把它们视为候选证明生成器；
8. `Adversarial.lean`：用反例检查自己是否混淆了几何、规则、搜索和证明。

验证整个 Lean 项目：

```powershell
lake build
```

验证 C++ 搜索器回归：

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```

项目总入口是 [`Gomoku.lean`](Gomoku.lean)，更详细的阶段规划见 [`PROJECT_GUIDE.md`](PROJECT_GUIDE.md)，已发现的语义风险及修复状态见 [`AUDIT_REPORT.md`](AUDIT_REPORT.md)。
