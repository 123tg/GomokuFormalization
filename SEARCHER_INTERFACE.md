# 搜索器与 Lean 检查器协作规范

本文档规定外部搜索器如何把候选结果交给本项目的 Lean 内核。搜索器可以使用任意语言、算法、启发式和缓存；但搜索器输出的内容只有在 Lean 中通过检查后，才可以成为数学结论。

## 1. 先理解目标

搜索器要寻找的是一棵“必胜策略树”。树中的每个节点都记录一个完整棋局面：棋盘上每个格子的状态，以及下一手轮到黑棋还是白棋。

- 轮到目标方（通常是黑棋）时，只需要给出一个能继续获胜的着法。
- 轮到对手时，必须列出对手的每一个合法着法，并为每个着法给出一个仍然获胜的子树。
- 已经是目标方胜利的节点才可以作为胜利叶子。
- 和棋、对手胜利或搜索深度耗尽都不能伪装成目标方胜利。

这正是 `CanForceWin` 的数学含义。搜索器不需要证明这层含义；它只需要生成数据，Lean 检查器会重新检查。

## 2. Lean 侧的输入输出类型

核心类型在 `Gomoku/Search.lean` 和 `Gomoku/Certificate.lean` 中：

```lean
structure SearchConfig where
  target : Player := .black
  maxNodes : Nat := 0

abbrev Searcher := SearchConfig -> Option CompactCertificate
```

`Searcher` 返回 `Option CompactCertificate`：

- `some c`：找到一个候选证书。它必须继续交给 `checkCertificate`。
- `none`：在当前深度、时间、内存或节点限制下没有生成证书。

`none` **不表示数学上不存在必胜策略**，也不表示目标方必败。它只表示本次搜索没有给出足够的证据。

### 落子后的终局分类

Lean 侧提供 `terminalAfterMoveFast s m` 作为搜索器实现可复用的单步分类函数。它只是一个
总计算：非法坐标返回 `none`；合法落子形成五连时返回当前落子方胜利；没有五连但填满
棋盘时返回和棋；否则返回 `none`。在父局面 `terminal s = none` 且 `legalMove s m` 时，
定理 `terminalAfterMoveFast_eq_terminal` 保证它与 `terminal (play s m)` 完全一致。外部
搜索器可以采用同样的分类逻辑，但外部结果仍必须交给证书检查器，不能只凭这个函数跳过
边合法性、对手分支覆盖或根局面检查。

`EngineStats.terminalChecks` 和 `EngineStats.candidateMoves` 是 Lean 引擎提供的可比性能
指标。它们分别表示实际进行的终局分类次数，以及交给递归扫描器的候选着法数量；缓存
命中不会重复计数。外部 C++ 搜索器应至少记录等价的节点数、证书节点数和检查时间，
但这些数字只能用于性能比较，不能替代证书检查。

证书定义为：

```lean
inductive CertificateNode where
  | terminal (position : Position) (winner : Outcome)
  | proverMove (position : Position) (move : Coord) (child : Nat)
  | opponentMoves (position : Position) (children : Array (Coord × Nat))

structure CompactCertificate where
  target : Player
  root : Nat
  nodes : Array CertificateNode
```

实际 Lean 代码使用乘积类型 `Coord × Nat`；以仓库中的声明为准。

## 3. 节点编号规则

`nodes` 是一个数组，数组下标就是节点编号。为了让 Lean 能在有限步骤内重建整棵树，当前版本要求所有边都向后指向更大的编号：

```text
parent < child
```

因此：

1. 根节点通常是 `0`。
2. 根节点的子节点编号必须大于 `0`。
3. 子节点可以继续有更大的编号。
4. 自循环和向前回指都被拒绝。
5. 允许共享子树，但共享节点必须仍然满足每条边的局面匹配和编号递增。
6. 未使用的节点目前也会被逐个检查；不要把无关的坏节点附在数组末尾。

推荐采用深度优先先序布局：先写父节点，再为第一棵子树分配连续编号，然后写后面的兄弟子树。`candidateTreeCertificate` 和 C++ 的 `emitProof` 都使用这种布局。这里必须是“先序”，因为检查器要求 `parent < child`。

## 4. 三种节点如何编码

### 4.1 `terminal`

```lean
.terminal s .blackWin
```

只有当 `terminal s = some .blackWin`（目标为黑棋时）时才通过。检查器会从棋盘重新计算胜负，不信任搜索器提供的标签。

不能使用以下方式表示“搜索到这里暂时没有继续”：

```lean
.terminal s .draw
.terminal s .whiteWin
```

这些都会被拒绝为黑棋必胜证书的叶子。

### 4.2 `proverMove`

```lean
.proverMove s m child
```

它表示当前节点轮到目标方，目标方选择合法着法 `m`，然后进入 `child`。检查器会验证：

- `terminal s = none`；
- `s.turn = target`；
- `legalMove s m`；
- `child < nodes.size`；
- `parent < child`；
- 子节点记录的局面等于 `play s m`。

### 4.3 `opponentMoves`

```lean
.opponentMoves s #[(reply1, child1), (reply2, child2)]
```

它表示当前轮到对手。检查器会验证：

- `terminal s = none`；
- `s.turn = Player.other target`；
- 每个列出的着法都合法；
- 每个引用都在数组范围内且严格向后；
- 对 `s` 的每个合法着法，都能在数组中找到同样的坐标；
- 对应子节点的局面等于 `play s reply`。

最容易犯的错误是只列出“搜索器认为重要的”应手。对于必胜证明，这不够；漏掉一个合法应手，整个证书必须被拒绝。

## 5. 全局检查和局部检查

有两个入口：

```lean
checkCertificate c
checkLocalCertificateAt s c
```

`checkCertificate` 是最终 15x15 定理的入口。它额外要求：

- `c.target = .black`；
- 根编号有效；
- 根节点的局面是空棋盘、黑棋先手。

通过它后可以使用：

```lean
compact_certificate_sound c h
```

得到：

```lean
CanForceWin initialPosition .black
```

`checkLocalCertificateAt s c` 复用完全相同的节点、边、索引和对手覆盖检查，但允许根节点是任意指定局面。它适合测试局部战术和两层证书；局部证书不能因此被解释为空棋盘的全局证明。

这里的 `CompactCertificate` 固定使用 15×15 的 `Position`。`Gomoku.Parametric` 和 `cpp/tools/solve_small_draws.cpp` 的 5×5--8×8 实验属于另一套参数化模型，不能把它们的和棋搜索结果直接交给本检查器。要形式化这些和棋结果，需要单独的参数化和棋证书类型及其 soundness 定理。

主线还提供了 `boardFromStones`、`positionFromStones` 和
`checkExternalLocalCertificate`。它们固定了“外部程序用棋子数组描述根局面”的
最小适配格式。数组本身是不可信输入，折叠得到的棋盘会直接交给
`checkLocalCertificateAt`；因此错误的子局面、非法着法、错误终局标签仍会被拒绝。
`Gomoku.InteropAudit` 中的通过/拒绝样例与队友 C++ 导出的文件形状一致。
如果导出器承诺每个占用坐标只出现一次，可以使用
`checkExternalLocalCertificateStrict`；它先检查数组坐标去重，再执行相同的证书检查。
普通 `checkExternalLocalCertificate` 保留为兼容接口，但会像 `Board.place` 一样对重复记录
采取后写覆盖，因此不应把它当作外部历史合法性的证明。

## 6. 坐标与棋盘表示

正式坐标是：

```lean
abbrev Coord := Fin 15 × Fin 15
```

因此搜索器不应生成越界坐标。`Gomoku.Search` 提供固定的行优先表：

```lean
coordAtIndex : Fin 225 -> Coord
coordIndex : Coord -> Fin 225
allCoords : Array Coord
```

已有定理证明两者互为逆。建议搜索器使用 `coordIndex` 作为数组掩码和缓存键，而向证书写入实际 `Coord`。

当前 C++ 搜索器中的 `Coord {x, y}` 原样导出为 Lean 的 `(x, y)`：`x` 是列，`y` 是行；输入文件按 `y = 0` 到 `14` 逐行读取。C++ bitboard 的线性索引为

```text
index = y * 15 + x
```

这与 Lean 的 `coordIndex` 行主序一致。不要交换两个坐标分量。

局面键 `PositionKey` 同时保存轮到谁和完整的 225 格棋盘向量。它是无损键，不是可能碰撞的哈希值；缓存不能把两个不同局面合并。

## 7. 推荐的搜索流程

每个搜索节点建议按下面顺序处理：

1. 计算 `terminal s`。
2. 若目标方胜利，返回 `.terminal s (winner target)`。
3. 若对手胜利或为和棋，返回 `none`。
4. 若燃料/深度为零，返回 `none`。
5. 枚举当前一方的全部合法着法。
6. 目标方节点尝试着法，找到一个子树成功即可返回 `.proverMove`。
7. 对手节点必须让每个合法应手都成功，才能返回 `.opponentMoves`。
8. 将候选树编译成 `CompactCertificate`。
9. 在 Lean 中调用 `checkLocalCertificateAt` 或 `checkCertificate`。

当前仓库中的 `searchCandidateTree`、`candidateTreeCertificate`、`checkedDepthCertificateFor` 是有限深度参考实现。它们不是完整 15x15 求解器，也不能绕过检查器。

当前 `cpp/gomoku_solver` 与上述接口的对应关系如下：

| C++ | Lean | 接口约束 |
|---|---|---|
| `Certificate::target` | `CompactCertificate.target` | 原样导出 |
| `CertificateNode::terminal` | `CertificateNode.terminal` | 必须是目标方的实际胜局 |
| `CertificateNode::proverMove` | `CertificateNode.proverMove` | 只保留一个已证明子节点 |
| `CertificateNode::opponentMoves` | `CertificateNode.opponentMoves` | 必须完整且无重复地枚举所有合法应手 |
| `sourceParent`、`sourceMove` | 不进入证书 | 只用于生成每个 Lean `Position` 定义 |
| DFPN/VCF/置换表 | 不进入可信基础 | 只负责寻找候选树 |

导出前，`validateCertificate` 会在 C++ 侧预检目标胜局、轮次、合法着法、对手全应手、向后引用和子局面重建。这是尽早发现生成错误的防线，不是数学证明；最终可信结论仍只来自 Lean 检查器。

主线还包含 `Gomoku.Engine`。它提供带节点预算、迭代加深、威胁排序、目标方强制防守剪枝和
精确局面缓存的可执行候选搜索。它仍然只生成 `CandidateTree`；`runCheckedEngine` 会把结果
编译成 `CompactCertificate`，并通过 `checkLocalCertificateAt` 后才允许使用
`runCheckedEngine_sound`。当设置了正的 `maxProverMoves` 或资源预算耗尽时，返回结果是不完备的，
不能把 `depthLimit`、`nodeLimit` 或 `none` 当成数学上的必败证明。

引擎还证明了 `mem_engineProverCandidateMoves_legal`：即使候选经过威胁分组或宽度截断，
其中每个留下的坐标仍满足当前局面的 `legalMove`。这是候选列表的安全不变量，不表示
选择性搜索已经完备。

有限深度参考实现还提供了一个诊断入口：

```lean
checkedDepthResultFor fuel position target
```

它把结果分成三类：

- `noCandidate`：给定燃料下没有找到候选策略树；
- `rejected certificate`：找到了候选树，但编译后的证书没有通过 Lean 检查；
- `accepted certificate`：证书通过检查，可以使用 `checkedDepthResultFor_sound` 得到
  `CanForceWin position target`。

Lean 中的 `checkedDepthResultFor_accepted_iff`、`checkedDepthResultFor_noCandidate_iff` 和
`checkedDepthResultFor_rejected_iff` 对这三种状态给出精确定义；其中只有 `accepted` 能推出
数学上的强制获胜。

这三类状态只描述本次有限搜索的输出。尤其是 `noCandidate`，不能解释为“目标方没有必胜策略”；
它可能只是搜索深度、时间或内存不够。

## 8. 有限语义基准与搜索器结果的关系

`Gomoku.Bounded` 还提供了独立的参考计算：

```lean
boundedCanForceWin fuel position target
```

它不使用搜索器的启发式，只按给定步数检查目标方节点的“存在一个成功着法”和对手节点的
“所有合法应手都成功”。Lean 已证明：返回 `true` 一定可以推出 `CanForceWin`；反方向在
`Board.emptyCount position.board + 1` 这个理论上限内也成立。这个定义适合审查搜索器，
但在完整 15×15 棋盘上通常不可直接穷举。

另外，`boundedCanForceWin_terminal_iff` 统一刻画了所有燃料下的终局结果，
`boundedCanForceWin_mono` 和 `boundedCanForceWin_mono_of_le` 证明：若某个深度返回
`true`，再增加一层或任意更多深度仍返回 `true`。
因此迭代加深可以安全地保留已找到的成功结果；这不改变 `noCandidate` 或深度截止状态的
含义，也不把有限搜索失败解释成必败。

`boundedCanForceWin`、`searchCandidateTree` 和 `runCheckedEngine` 的职责不同：

| 组件 | 作用 | 是否直接产生定理 |
|---|---|---|
| `boundedCanForceWin` | 小深度的完整 AND/OR 参考计算 | 只有返回 `true` 时，通过 `boundedCanForceWin_sound` 得到定理 |
| `searchCandidateTree` | 生成候选策略树，可使用排序和缓存 | 否；候选树必须经过证书检查 |
| `runCheckedEngine` | 带节点预算的候选搜索并立即调用检查器 | 只有 `found` 且证书通过时，通过 `runCheckedEngine_sound` 得到定理 |

因此，搜索器返回 `none`、`noCandidate`、`depthLimit` 或 `nodeLimit` 都只是“本次资源下没有
找到证书”。它们不能被写成“不存在必胜策略”。

若候选证书已经通过 `checkedDepthCertificateFor` 或
`checkedDepthCertificateForCached`，并且调用者另外知道
`Board.emptyCount position.board + 1 ≤ fuel`，可以使用
`checkedDepthCertificateFor_bounded` 或 `checkedDepthCertificateForCached_bounded`，
把该结果连接到独立的 `boundedCanForceWin fuel position target = true`。这只是
“理论上足够深度”的充分性桥接；它不把较浅搜索的 `none` 解释为必败，也不声称启发式搜索
在所有深度上都完备。

## 9. 缓存约束

当前 `SearchMemo` 已接入 Lean 侧的有限深度递归参考搜索，但还不是完整的高性能搜索器。缓存键至少必须包含：

- 剩余深度/燃料；
- 目标玩家；
- 完整局面（包括轮次）。

`SearchMemo` 使用的 `SearchKey` 正好包含上述三项。`Gomoku.Engine` 的候选策略还会受
选择性剪枝、威胁排序和宽度限制影响，因此 `EngineMemo` 使用更强的 `EngineSearchKey`，
在 `SearchKey` 之外再保存完整 `EngineConfig`。不同配置生成的 `none` 不能互相复用，
否则较窄的搜索可能错误地阻止较宽的搜索继续尝试。缓存命中仍须经过证书检查器。

`engineCacheLookup` 把底层的嵌套 `Option` 展开成三个明确状态：`miss` 表示从未缓存过
这个查询，`notFound` 表示该配置和深度已经搜索过但没有候选树，`found tree` 表示缓存了
候选树。三种状态都不是数学证明；`found` 仍必须交给证书检查器，`notFound` 也不能解释成
目标方必败。

Lean 中的 `searchKey_eq_iff` 已经把这条约束写成定理：两个键相等，当且仅当剩余深度、目标方和
完整局面同时相等。`SearchAudit` 还用不同深度、不同目标方和不同棋盘的恶意缓存条目做了回归，
确认这些条目不会被错误复用。

缓存命中后仍必须把返回树交给证书检查器。不要把“缓存中存在结果”直接当作 `CanForceWin` 证明。
当前的 `searchCandidateTreeMemoized` 会返回候选树和更新后的缓存；`searchCandidateTree` 是从空缓存
开始的兼容入口，`searchCandidateTreeCached` 则允许调用者提供已有缓存。

如果以后继续扩展当前“搜索结果 + 新缓存”的递归版本，需要补充：

- 命中和未命中路径在候选树结果上的更强语义等价定理；
- 共享子树的编号和局面匹配测试；
- 清空缓存与非空缓存结果一致的回归测试；
- 缓存命中率、内存占用和搜索时间的性能记录。

## 10. 阶段性验收任务

队友不应一开始就尝试生成完整 15x15 证书。按以下顺序提交：

### 第一步：一步胜

- 输入一个有四连且轮到目标方的局面；
- 输出两个节点：`proverMove` 和黑胜 `terminal`；
- 在 Lean 中通过 `checkLocalCertificateAt`；
- 记录节点数和检查时间。

### 第二步：两个合法应手

- 构造只有两个空点的局面；
- 输出一个 `opponentMoves` 根节点；
- 两个应手都要有目标方获胜子树；
- Lean 检查通过后再记录性能。

### 第三步：有限深度搜索

- 使用 `searchCandidateTree` 或自己的搜索器；
- 记录深度、是否返回 `none`、节点数、证书字节/源码大小和 Lean 检查时间；
- 明确 `none` 只是深度不足或资源不足。

### 第四步：外部搜索器导出 Lean 源码

首选输出 Lean 文件中的 `def certificate : CompactCertificate := ...`，而不是先发明未经证明的自定义二进制解析器。导入后运行：

```lean
#eval checkCertificate certificate
example : checkCertificate certificate = true := by native_decide
example : CanForceWin initialPosition .black :=
  compact_certificate_sound certificate (by native_decide)
```

`native_decide` 只适合测试模块；正式 soundness 定理仍来自 `compact_certificate_sound`。

当前 C++ 导出器会自动选择检查入口：空 15×15 棋盘、黑方先手且证明目标为黑方时生成 `checkCertificate` 与 `compact_certificate_sound`；其他局部根生成 `checkLocalCertificateAt` 与 `local_certificate_at_sound`。两种路径都不会信任 C++ 自己的胜负判断。

## 11. 每次提交必须附带的信息

```text
搜索配置：目标方、深度/燃料、节点上限、时间上限
搜索结果：some/none（若 none，说明资源限制）
证书节点数：
证书源码或文件大小：
Lean 检查结果：checkLocalCertificateAt/checkCertificate
检查耗时：
是否共享子树：
是否有缓存：缓存键字段和命中数
是否使用 sorry/admit/axiom/unsafe：
已经由 Lean 证明：
尚未证明：
```

`cpp/gomoku_solver` 的标准输出已经使用稳定字段报告上述主要信息，包括 `search_target`、各项资源上限、`status`、`certificate`、节点数、源码字节数、缓存统计以及实际选择的 `lean_checker`。`status` 为资源上限或深度上限时，必须同时报告 `certificate=none` 和 `lean_checker=not-run`。

搜索器的算法性能属于实验结果；只有通过 Lean 检查的证书才属于形式化证明成果。

这项缓存是搜索器可以采用的正确性基础，但当前尚未接入 `Gomoku.Engine` 默认递归流程。
接入时仍须维护合法落子、终局优先级和证书检查；缓存命中或性能提升都不能替代
`checkCertificate`。
