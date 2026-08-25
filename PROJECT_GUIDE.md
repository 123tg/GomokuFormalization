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
| Gomoku/Examples.lean | 构造局面、正反例和 API 测试 |
| Gomoku.lean | 统一导入所有模块 |

配置文件：

- lakefile.toml：项目名、mathlib 依赖和 Lean 选项。
- lean-toolchain：Lean 4.33.0。
- README.md：快速说明。
- PROJECT_GUIDE.md：本完整方案和执行手册。

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
~~~

v1 只包含明确的直线型模式：连续三子或四子，两端都是空点。断三、跳四等变体没有默认并入，未来要作为独立模式加入。

边界端点通过 step 得到 none，所以不能满足 openEnd，自然被视为封闭端。

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

黑胜检查在白胜之前，但可达非终局局面不会出现双方同时胜利。落子形成黑五连后立即结束，不会进入白棋的后续回合。

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
- 可达非终局局面不能同时有黑五连和白五连。

---

## 8. Game：博弈语义

### 8.1 策略接口

~~~lean
def Strategy (target : Player) : Type :=
  ∀ s, Reachable s → s.turn = target → terminal s = none →
    {m : Coord // legalMove s m}
~~~

这是“位置策略”：给定局面，只依赖当前棋盘和轮次选择着法。历史策略可以以后作为等价性研究，但 v1 不需要它。

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
def DoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop := ...
def MoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop := ...
def SingleOpenFour (s : Position) (p : Player) : Prop := ...
def SafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop := ...
~~~

需要区分：

- MoveCreatesSingleOpenFour：描述某一步之后的图形。
- SingleOpenFour：描述当前局面中的图形。
- DoubleOpenThree：一次落子后产生至少两个活三见证。
- SafeDoubleOpenThree：在双活三几何条件之外，再加入对手立即胜着排除条件。

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

### 10.4 当前限制

紧凑检查器还没有完成：

~~~text
checkCertificate c = true
    -> 重建 CertificateTree
    -> 使用 CertificateTree.sound
    -> 得到 CanForceWin initialPosition .black
~~~

所以现在不能把 checkCertificate 通过直接写成全局必胜定理。必须先实现经过 Lean 检查的 DAG 重建递归。

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
- [x] 横向、斜线、边界、六连、终局和非法着法测试。
- [x] lake build 全工程构建成功。

尚未完成：

- [ ] 规范化线段和唯一活三/活四见证。
- [ ] 断三、跳四等变体。
- [ ] 完整双活三强制性定理。
- [ ] 紧凑证书到 CertificateTree 的可信转换。
- [ ] 对称性压缩的独立正确性证明。
- [ ] 实际 15×15 策略证书。
- [ ] initial_black_wins。

---

## 12. 接下来怎么做

后续必须遵循“先基础、后战术、再证书、最后搜索”的顺序。

### 阶段 A：规范化几何

目标：同一条线只被统计一次，SingleOpenFour 和 DoubleOpenThree 的 card 有明确含义。

做法：

1. 定义连续段的规范起点，例如前一格不是同色或已经到边界。
2. 证明规范起点唯一。
3. 修改 openThreeWitnesses/openFourWitnesses，只收集规范见证。
4. 补 step 在 -1、0、3、4 偏移下的引理。
5. 对四个方向分别补正例、边界反例和长连测试。

完成标准：重复起点不会重复计数，边界行为由定理而不是注释决定。

### 阶段 B：逐级完成局部战术

目标：把“看起来必胜”变成显式前提和可检查证明。

顺序：

1. 保持立即胜着定理作为最底层战术。
2. 为直线型活四补充白棋和四方向的对称版本。
3. 明确单活四的当前回合、非终局、对手立即胜着排除条件。
4. 证明一次落子产生两个不同活三见证。
5. 证明一次对手落子不能同时堵住两个独立胜点。
6. 排除对手防守时同时产生立即胜着或反击四。
7. 将这些引理组合成 SafeDoubleOpenThree 的完整定理。

每一个战术都要有正例、边界反例、断三反例，以及对手已有立即胜着时不触发的语义反例。

### 阶段 C：小型策略证书

目标：先验证证书 soundness，不直接搜索 15×15。

做法：

1. 手工构造浅层 CertificateTree。
2. 构造错误终局、错误边、非法着法、缺分支和循环的 CompactCertificate。
3. 确认错误证书被 Bool 检查器拒绝。
4. 实现按节点索引逆序的 DAG 递归：子节点索引必须大于父节点，所以构造父节点时子树已经可用。
5. 让递归函数返回 CertificateTree，而不只是 Bool。
6. 证明小证书的 compact soundness。

完成标准：

~~~lean
theorem compact_certificate_sound_small ...
~~~

能够从通过检查的紧凑证书得到 CanForceWin。

### 阶段 D：完成紧凑证书可信转换

目标：把结构检查升级为真正的 soundness。

需要证明：

1. 引用索引都在数组范围内。
2. 子索引大于父索引，因此没有循环。
3. childPositionMatches 可转换为位置相等式。
4. terminal 节点标签正确。
5. proverMove 节点的着法合法且子树成立。
6. opponentMoves 节点覆盖全部合法对手着法。
7. 根节点是 initialPosition，目标是黑棋。

建议的实现思路：

- 对节点索引或剩余节点数量做归纳。
- 使用 Fin 表示已经证明有效的数组索引。
- 对每个节点返回依赖类型 CertificateTree。
- 把 Bool 检查结果拆成一组显式等式和 forall 证明。
- 先做只包含树、不含共享子树的版本，再扩展到 DAG。

最终接口应接近：

~~~lean
theorem compact_certificate_sound
    (h : checkCertificate c = true) :
    CanForceWin initialPosition .black
~~~

### 阶段 E：外部搜索器

目标：让搜索器生成候选证书，但不把搜索器本身作为可信基础。

建议：

1. 优先生成 Lean 源码中的 CompactCertificate 值，避免未经验证的文本解析器。
2. 搜索器优先处理立即胜着和必须防守的对手威胁。
3. 使用置换表和局面缓存减少重复局面。
4. 先不把旋转/反射压缩放入可信内核。
5. 如果加入对称性压缩，必须另外证明坐标变换保持合法着法、终局和 CanForceWin。
6. 搜索器输出后，所有可信结论仍由 Lean 重新检查。

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
- 紧凑证书检查器尚未连接到 CertificateTree。
- v1 活三/活四只覆盖冻结的直线型模式。

正确的后续顺序是：

~~~text
规范化几何
  -> 完成双活三等局部定理
  -> 小型证书 soundness
  -> 紧凑证书可信转换
  -> 外部搜索器生成 15×15 证书
  -> Lean 检查证书
  -> 证明 initial_black_wins
~~~

每一个中间阶段都可以独立验收；任何尚未获得的结论都不会被提前写成定理。
