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

推荐采用深度优先后序布局：先为一个子树分配连续编号，再分配后面的兄弟子树。`candidateTreeCertificate` 已经提供了这种布局的参考实现。

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

`checkLocalCertificateAt s c` 复用完全相同的节点、边、索引和对手覆盖检查，但允许根节点是任意指定局面。它适合测试局部战术、两层证书和小棋盘实验；局部证书不能因此被解释为空棋盘的全局证明。

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

## 8. 缓存约束

当前 `SearchMemo` 是适配接口，不是已经完成的高性能搜索器。缓存键至少必须包含：

- 剩余深度/燃料；
- 目标玩家；
- 完整局面（包括轮次）。

缓存命中后仍必须把返回树交给证书检查器。不要把“缓存中存在结果”直接当作 `CanForceWin` 证明。

如果以后实现“搜索结果 + 新缓存”的递归版本，需要补充：

- 命中和未命中路径语义相同的定理；
- 缓存键无碰撞的定理；
- 共享子树的编号和局面匹配测试；
- 清空缓存与非空缓存结果一致的回归测试。

## 9. 阶段性验收任务

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

## 10. 每次提交必须附带的信息

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

搜索器的算法性能属于实验结果；只有通过 Lean 检查的证书才属于形式化证明成果。
