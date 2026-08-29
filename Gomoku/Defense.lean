import Gomoku.Certificate

/-!
防御证书层：定义“防守方阻止攻击方获胜”的博弈语义、可执行紧凑防御证书、独立检查器
与可靠性定理，并把两张防守证书组合为标准双方规则下的和棋 `StandardDraw`。

设计要点：
* `CanPreventWin defender s` 是一个归纳命题：终局为和棋或防守方获胜时成功闭合；
  防守方回合只需一个保持防守的合法着法；攻击方回合必须覆盖全部合法着法。
  攻击方获胜的终局没有任何闭合构造子，因此该命题精确刻画“防守方阻止攻击方获胜”。
* `StandardDraw s` 采用经典博弈论定义：黑方不能强制黑胜，且白方不能强制白胜
  （双方均无强制胜策略的和棋区域）。`standardDraw_of_mutualDefense` 证明两张
  防守证书的组合蕴含该定义。
* 紧凑证书 `DefenseCertificate` 与现有 `CompactCertificate` 风格一致：扁平节点数组、
  根索引、`parent < child` 严格向后引用、可执行布尔检查器。检查器不信任外部搜索器，
  对每个节点重新计算局面、轮次、终局、合法性与攻击方全部合法应手。
-/

namespace Gomoku

/-! ## 防守博弈语义 -/

/-- 防守方 `defender` 从局面 `s` 出发存在策略使攻击方（`defender.other`）最终无法获胜。 -/
inductive CanPreventWin (defender : Player) : Position → Prop where
  | terminal {s : Position} (h : terminal s = some (winner defender)) :
      CanPreventWin defender s
  | draw {s : Position} (h : terminal s = some .draw) :
      CanPreventWin defender s
  | defenderMove {s : Position} (hterm : terminal s = none)
      (hturn : s.turn = defender) (m : Coord) (hm : legalMove s m)
      (hchild : CanPreventWin defender (play s m)) : CanPreventWin defender s
  | attackerMoves {s : Position} (hterm : terminal s = none)
      (hturn : s.turn = Player.other defender)
      (children : ∀ m, legalMove s m → CanPreventWin defender (play s m)) :
      CanPreventWin defender s
-- 终局为和棋或防守方获胜时闭合；防守方回合为存在量词，攻击方回合为全称量词；
-- 攻击方获胜的终局无法闭合，因此该归纳命题就是“防守方阻止攻击方获胜”。

/-- 白方存在策略使黑棋最终无法获胜（允许结果为白胜或和棋）。 -/
def WhiteCanPreventBlackWin (s : Position) : Prop := CanPreventWin .white s

/-- 黑方存在策略使白棋最终无法获胜（允许结果为黑胜或和棋）。 -/
def BlackCanPreventWhiteWin (s : Position) : Prop := CanPreventWin .black s

/-- 依赖类型防御树：与 `CanPreventWin` 同构，但每个节点携带完整的证明数据，
供紧凑证书重构时使用。 -/
inductive DefenseTree (defender : Player) : Position → Type where
  | terminal {s : Position} (h : terminal s = some (winner defender)) :
      DefenseTree defender s
  | draw {s : Position} (h : terminal s = some .draw) :
      DefenseTree defender s
  | defenderMove {s : Position} (hterm : terminal s = none)
      (hturn : s.turn = defender) (m : Coord) (hm : legalMove s m)
      (child : DefenseTree defender (play s m)) : DefenseTree defender s
  | attackerMoves {s : Position} (hterm : terminal s = none)
      (hturn : s.turn = Player.other defender)
      (children : ∀ m, legalMove s m → DefenseTree defender (play s m)) :
      DefenseTree defender s

/-- 遗忘防御树的证明数据，将其转换为 `CanPreventWin` 命题证明。 -/
theorem DefenseTree.sound {defender : Player} {s : Position} :
    DefenseTree defender s → CanPreventWin defender s
  | .terminal h => .terminal h
  | .draw h => .draw h
  | .defenderMove hterm hturn m hm child =>
      .defenderMove hterm hturn m hm (DefenseTree.sound child)
  | .attackerMoves hterm hturn children =>
      .attackerMoves hterm hturn (fun m hm => DefenseTree.sound (children m hm))

/-- 标准双方规则（黑先、交替落子、双方五连均判胜、满盘和棋）下的和棋区域：
黑方不能强制黑胜，且白方不能强制白胜。这是有限完全信息零和博弈中“和棋”
的经典博弈论刻画。 -/
def StandardDraw (s : Position) : Prop :=
  ¬ CanForceWin s .black ∧ ¬ CanForceWin s .white

/-- 防守策略与强制胜策略不可能同时存在：若防守方（攻击方的对手）能阻止攻击方获胜，
则攻击方不可能从同一局面强制获胜。证明对强制胜树做结构递归，在每个节点把两棵树对齐，
在终局节点利用终局结果的唯一性得到矛盾。 -/
theorem canPrevent_not_canForceWin {s : Position} {defender : Player} :
    CanPreventWin defender s → CanForceWin s defender.other → False
  | hprev, .terminal hwin => by
      cases hprev with
      | terminal hw =>
          have hwinj : winner defender.other = winner defender :=
            Option.some.inj (hwin.symm.trans hw)
          cases defender <;> simp [winner] at hwinj
      | draw hd =>
          have hdj : some .draw = some (winner defender.other) := hd.symm.trans hwin
          cases defender <;> simp [winner] at hdj
      | defenderMove hterm _ _ _ _ =>
          rw [hterm] at hwin
          simp at hwin
      | attackerMoves hterm _ _ =>
          rw [hterm] at hwin
          simp at hwin
  | hprev, .choose hterm hturn m hm hchild => by
      cases hprev with
      | terminal hw => rw [hterm] at hw; simp at hw
      | draw hd => rw [hterm] at hd; simp at hd
      | defenderMove _ hturn' _ _ _ =>
          exact (Player.self_ne_other defender (hturn'.symm.trans hturn)).elim
      | attackerMoves _ _ children =>
          exact canPrevent_not_canForceWin (children m hm) hchild
  | hprev, .respond hterm hturn children => by
      cases hprev with
      | terminal hw => rw [hterm] at hw; simp at hw
      | draw hd => rw [hterm] at hd; simp at hd
      | defenderMove _ _ m hm hchild =>
          exact canPrevent_not_canForceWin hchild (children m hm)
      | attackerMoves _ hturn' _ =>
          exact (Player.other_ne_self defender
            (hturn'.symm.trans (by simpa using hturn))).elim

/-- 两张防守证书（白方阻止黑胜、黑方阻止白胜）共同蕴含标准和棋。 -/
theorem standardDraw_of_mutualDefense {s : Position}
    (hWhite : WhiteCanPreventBlackWin s) (hBlack : BlackCanPreventWhiteWin s) :
    StandardDraw s := by
  unfold StandardDraw
  constructor
  · exact canPrevent_not_canForceWin hWhite
  · exact canPrevent_not_canForceWin hBlack

/-! ## 可执行紧凑防御证书 -/

/-- 可序列化的扁平防御证书节点，子树用数组索引引用。 -/
inductive DefenseCertificateNode where
  | terminal (position : Position) (outcome : Outcome)
  | defenderMove (position : Position) (move : Coord) (child : Nat)
  | attackerMoves (position : Position) (children : Array (Coord × Nat))
-- 终局节点记录结果；防守方节点记录一步着法；攻击方节点记录全部应手。

/-- 用防守方、根索引和节点数组组成紧凑防御证书，供外部搜索器生成和 Lean 检查。 -/
structure DefenseCertificate where
  defender : Player
  root : Nat
  nodes : Array DefenseCertificateNode

/-- 从任意紧凑防御证书节点中提取其记录的父局面。 -/
def defenseNodePosition : DefenseCertificateNode → Position
  | .terminal s _ => s
  | .defenderMove s _ _ => s
  | .attackerMoves s _ => s

/-- 检查引用存在且对应子节点记录的局面等于预期的落子后局面。 -/
def defenseChildPositionMatches (nodes : Array DefenseCertificateNode) (ref : Nat)
    (expected : Position) : Bool :=
  match nodes[ref]? with
  | some node => samePosition (defenseNodePosition node) expected
  | none => false

theorem defenseChildPositionMatches_true_iff (nodes : Array DefenseCertificateNode)
    (ref : Nat) (expected : Position) :
    defenseChildPositionMatches nodes ref expected = true ↔
      ∃ node, nodes[ref]? = some node ∧ defenseNodePosition node = expected := by
  cases hnode : nodes[ref]? with
  | none => simp [defenseChildPositionMatches, hnode]
  | some node =>
      simp [defenseChildPositionMatches, hnode, samePosition_true_iff]

/-- 在已知引用有效时，将子局面匹配简化为数组取值节点的局面相等。 -/
theorem defenseChildPositionMatches_at_iff (nodes : Array DefenseCertificateNode)
    (ref : Nat) (href : ref < nodes.size) (expected : Position) :
    defenseChildPositionMatches nodes ref expected = true ↔
      defenseNodePosition nodes[ref] = expected := by
  have hlookup : nodes[ref]? = some nodes[ref] := by simp [href]
  simp [defenseChildPositionMatches, hlookup, samePosition_true_iff]

/-- 检查攻击方应手数组中的坐标两两不同（拒绝重复应手）。 -/
def movesDistinct (children : Array (Coord × Nat)) : Bool :=
  decide ((children.map (fun x => x.1)).toList.eraseDups.length = children.size)

/-- 检查单个防御证书节点的局部语义：终局重新计算、轮次、合法性、引用范围、
攻击方全应手覆盖与无重复应手。 -/
def checkDefenseNode (defender : Player) (size : Nat) : DefenseCertificateNode → Bool
  | .terminal s out =>
      decide (terminal s = some out) &&
        (decide (out = winner defender) || decide (out = .draw))
  | .defenderMove s m child =>
      decide (terminal s = none) && decide (s.turn = defender) &&
        decide (legalMove s m) && refValid size child
  | .attackerMoves s children =>
      decide (terminal s = none) && decide (s.turn = Player.other defender) &&
        allRefsValid size children && allMovesLegal s children &&
        allLegalMovesCovered s children && movesDistinct children
-- 终局结果必须是防守方获胜或和棋；攻击方获胜的终局（如 defender=White 时 BlackWin）
-- 会被拒绝。攻击方节点要求合法应手集合与全部合法着法集合完全相等。

/-- 检查每条防御证书边引用的子节点局面精确等于执行相应着法后的局面，
并要求所有子引用严格向后（parent < child），排除自环、回边与环。 -/
def checkDefenseEdgesAt (nodes : Array DefenseCertificateNode) (parent : Nat) :
    DefenseCertificateNode → Bool
  | .terminal _ _ => true
  | .defenderMove s m child =>
      refAfter parent child && defenseChildPositionMatches nodes child (play s m)
  | .attackerMoves s children =>
      children.all (fun x =>
        refAfter parent x.2 && defenseChildPositionMatches nodes x.2 (play s x.1))

/-- 在指定父索引处完整检查节点语义、子引用顺序和子局面一致性。 -/
def checkDefenseNodeAt (defender : Player) (nodes : Array DefenseCertificateNode)
    (parent : Nat) (node : DefenseCertificateNode) : Bool :=
  checkDefenseNode defender nodes.size node && checkDefenseEdgesAt nodes parent node

theorem checkDefenseNode_terminal_iff {defender : Player} {size : Nat}
    {s : Position} {out : Outcome} :
    checkDefenseNode defender size (.terminal s out) = true ↔
      terminal s = some out ∧ (out = winner defender ∨ out = .draw) := by
  constructor
  · intro h
    simp only [checkDefenseNode, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
    have hterm : terminal s = some out := of_decide_eq_true h.1
    have hout : out = winner defender ∨ out = .draw := by
      by_cases hw : out = winner defender
      · exact Or.inl hw
      · right
        have hd : decide (out = .draw) = true := by
          simpa [hw] using h.2
        exact of_decide_eq_true hd
    exact ⟨hterm, hout⟩
  · rintro ⟨hterm, hout⟩
    cases hout with
    | inl hw => simp [checkDefenseNode, hterm, hw]
    | inr hd => simp [checkDefenseNode, hterm, hd]

theorem checkDefenseNodeAt_terminal_iff {defender : Player}
    (nodes : Array DefenseCertificateNode) (parent : Nat) (s : Position)
    (out : Outcome) :
    checkDefenseNodeAt defender nodes parent (.terminal s out) = true ↔
      terminal s = some out ∧ (out = winner defender ∨ out = .draw) := by
  simp only [checkDefenseNodeAt, checkDefenseEdgesAt, Bool.and_true]
  exact checkDefenseNode_terminal_iff

theorem checkDefenseNodeAt_defenderMove_iff (defender : Player)
    (nodes : Array DefenseCertificateNode) (parent : Nat) (s : Position)
    (m : Coord) (child : Nat) :
    checkDefenseNodeAt defender nodes parent (.defenderMove s m child) = true ↔
      terminal s = none ∧ s.turn = defender ∧ legalMove s m ∧ parent < child ∧
        child < nodes.size ∧
        defenseChildPositionMatches nodes child (play s m) = true := by
  constructor
  · intro h
    simp [checkDefenseNodeAt, checkDefenseNode, checkDefenseEdgesAt, refValid, refAfter] at h
    aesop
  · rintro ⟨hterm, hturn, hm, hafter, hchild, hmatch⟩
    simp [checkDefenseNodeAt, checkDefenseNode, checkDefenseEdgesAt, refValid, refAfter,
      hterm, hturn, hm, hafter, hchild, hmatch]

theorem checkDefenseNodeAt_attackerMoves_iff (defender : Player)
    (nodes : Array DefenseCertificateNode) (parent : Nat) (s : Position)
    (children : Array (Coord × Nat)) :
    checkDefenseNodeAt defender nodes parent (.attackerMoves s children) = true ↔
      terminal s = none ∧ s.turn = Player.other defender ∧
        (∀ x, x ∈ children → x.2 < nodes.size) ∧
        (∀ x, x ∈ children → legalMove s x.1) ∧
        (∀ c, legalMove s c → moveIn children c) ∧
        movesDistinct children = true ∧
        (∀ x, x ∈ children → parent < x.2 ∧
          defenseChildPositionMatches nodes x.2 (play s x.1) = true) := by
  constructor
  · intro h
    have hparts :
        checkDefenseNode defender nodes.size (.attackerMoves s children) = true ∧
          checkDefenseEdgesAt nodes parent (.attackerMoves s children) = true := by
      simpa only [checkDefenseNodeAt, Bool.and_eq_true_eq_eq_true_and_eq_true] using h
    have hnode := hparts.1
    simp only [checkDefenseNode, Bool.and_eq_true_eq_eq_true_and_eq_true] at hnode
    have htermB : decide (terminal s = none) = true := by aesop
    have hturnB : decide (s.turn = Player.other defender) = true := by aesop
    have hrefsB : allRefsValid nodes.size children = true := by aesop
    have hmovesB : allMovesLegal s children = true := by aesop
    have hcoverB : allLegalMovesCovered s children = true := by aesop
    have hdistinctB : movesDistinct children = true := by aesop
    have hterm : terminal s = none := of_decide_eq_true htermB
    have hturn : s.turn = Player.other defender := of_decide_eq_true hturnB
    have hrefs := (allRefsValid_true_iff nodes.size children).mp hrefsB
    have hmoves := (allMovesLegal_true_iff s children).mp hmovesB
    have hcover := (allLegalMovesCovered_true_iff s children).mp hcoverB
    have hedge := hparts.2
    simp only [checkDefenseEdgesAt, Array.all_eq_true'] at hedge
    have hedge' : ∀ x, x ∈ children → parent < x.2 ∧
        defenseChildPositionMatches nodes x.2 (play s x.1) = true := by
      intro x hx
      simpa [refAfter, Bool.and_eq_true_eq_eq_true_and_eq_true] using hedge x hx
    exact ⟨hterm, hturn, hrefs, hmoves, hcover, hdistinctB, hedge'⟩
  · rintro ⟨hterm, hturn, hrefs, hmoves, hcover, hdistinct, hedge⟩
    have hrefsB : allRefsValid nodes.size children = true :=
      (allRefsValid_true_iff nodes.size children).mpr hrefs
    have hmovesB : allMovesLegal s children = true :=
      (allMovesLegal_true_iff s children).mpr hmoves
    have hcoverB : allLegalMovesCovered s children = true :=
      (allLegalMovesCovered_true_iff s children).mpr hcover
    have hedgeB : checkDefenseEdgesAt nodes parent (.attackerMoves s children) = true := by
      simp only [checkDefenseEdgesAt, Array.all_eq_true']
      intro x hx
      have hx' := hedge x hx
      simpa [refAfter, Bool.and_eq_true_eq_eq_true_and_eq_true] using hx'
    have hnodeB : checkDefenseNode defender nodes.size (.attackerMoves s children) = true := by
      simp [checkDefenseNode, hterm, hturn, hrefsB, hmovesB, hcoverB, hdistinct]
    simpa only [checkDefenseNodeAt, Bool.and_eq_true_eq_eq_true_and_eq_true]
      using And.intro hnodeB hedgeB

/-- 检查防御证书根引用存在且根节点局面等于调用方指定的局面 s。 -/
def defenseRootPositionMatches (s : Position) (c : DefenseCertificate) : Bool :=
  match c.nodes[c.root]? with
  | some node => samePosition (defenseNodePosition node) s
  | none => false

/-- 组合防御证书结构检查（根引用、全部节点）与指定根局面匹配检查。 -/
def checkDefenseCertificateAt (s : Position) (c : DefenseCertificate) : Bool :=
  decide (c.root < c.nodes.size) && defenseRootPositionMatches s c &&
    (c.nodes.mapIdx (fun i node => checkDefenseNodeAt c.defender c.nodes i node)).all id

/-- 标准初始局面根上的防御证书检查（生成的 7×7 全局定理使用）。 -/
def checkDefenseCertificate (c : DefenseCertificate) : Bool :=
  checkDefenseCertificateAt initialPosition c

theorem defenseMapIdx_all_true_iff (nodes : Array DefenseCertificateNode)
    (f : Nat → DefenseCertificateNode → Bool) :
    (nodes.mapIdx f).all id = true ↔
      ∀ i (hi : i < nodes.size), f i nodes[i] = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have hi' : i < (nodes.mapIdx f).size := by simpa using hi
    simpa using h i hi'
  · intro h i hi
    have hi' : i < nodes.size := by simpa using hi
    simpa using h i hi'

theorem checkDefenseCertificateAt_header (s : Position) (c : DefenseCertificate)
    (h : checkDefenseCertificateAt s c = true) :
    c.root < c.nodes.size ∧ defenseRootPositionMatches s c = true := by
  simp only [checkDefenseCertificateAt, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, h.1.2⟩

theorem checkDefenseCertificateAt_nodes_checked (s : Position) (c : DefenseCertificate)
    (h : checkDefenseCertificateAt s c = true) :
    ∀ i (hi : i < c.nodes.size),
      checkDefenseNodeAt c.defender c.nodes i c.nodes[i] = true := by
  have hmap :
      (c.nodes.mapIdx (fun i node =>
        checkDefenseNodeAt c.defender c.nodes i node)).all id = true := by
    simp only [checkDefenseCertificateAt, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
    exact h.2
  exact (defenseMapIdx_all_true_iff c.nodes
    (fun i node => checkDefenseNodeAt c.defender c.nodes i node)).mp hmap

theorem defenseRootPositionMatches_at_iff (s : Position) (c : DefenseCertificate)
    (hroot : c.root < c.nodes.size) :
    defenseRootPositionMatches s c = true ↔
      defenseNodePosition c.nodes[c.root] = s := by
  have hlookup : c.nodes[c.root]? = some c.nodes[c.root] := by simp [hroot]
  simp [defenseRootPositionMatches, hlookup, samePosition_true_iff]

/-- 利用子引用严格向后的度量，对紧凑防御节点数组做良基递归并重建依赖类型
`DefenseTree`。每个节点都重新计算局面、轮次、终局、合法性与子局面一致性。 -/
theorem defense_reify_at (c : DefenseCertificate) (defender : Player) :
    ∀ (i : Nat) (hi : i < c.nodes.size),
      (∀ j (hj : j < c.nodes.size),
        checkDefenseNodeAt defender c.nodes j c.nodes[j] = true) →
      Nonempty (DefenseTree defender (defenseNodePosition c.nodes[i])) := by
  intro i
  induction hmeasure : c.nodes.size - i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    intro hi hall
    cases hnode : c.nodes[i] with
    | terminal s out =>
        have hcheck := hall i hi
        rw [hnode] at hcheck
        have hvalid :=
          (checkDefenseNodeAt_terminal_iff (defender := defender)
            c.nodes i s out).mp hcheck
        rcases hvalid with ⟨hterm, hout⟩
        cases hout with
        | inl houtW =>
            change Nonempty (DefenseTree defender s)
            exact ⟨.terminal (by simpa [houtW] using hterm)⟩
        | inr houtD =>
            change Nonempty (DefenseTree defender s)
            exact ⟨.draw (by simpa [houtD] using hterm)⟩
    | defenderMove s m child =>
        have hcheck := hall i hi
        rw [hnode] at hcheck
        have hvalid :=
          (checkDefenseNodeAt_defenderMove_iff defender c.nodes i s m child).mp hcheck
        rcases hvalid with ⟨hterm, hturn, hm, hafter, hchild, hmatch⟩
        have hchildTree := ih (c.nodes.size - child) (by omega) child (by rfl) hchild hall
        have hpos := (defenseChildPositionMatches_at_iff c.nodes child hchild
          (play s m)).mp hmatch
        have hchildTree' : Nonempty (DefenseTree defender (play s m)) := by
          refine ⟨?_⟩
          rw [← hpos]
          exact Classical.choice hchildTree
        change Nonempty (DefenseTree defender s)
        exact ⟨.defenderMove hterm hturn m hm (Classical.choice hchildTree')⟩
    | attackerMoves s children =>
        have hcheck := hall i hi
        rw [hnode] at hcheck
        have hvalid :=
          (checkDefenseNodeAt_attackerMoves_iff defender c.nodes i s children).mp hcheck
        rcases hvalid with ⟨hterm, hturn, hrefs, hmoves, hcover, _hdistinct, hedge⟩
        change Nonempty (DefenseTree defender s)
        refine ⟨.attackerMoves hterm hturn ?_⟩
        intro m hm
        have hm' : legalMove s m := by simpa using hm
        have hmove : moveIn children m := hcover m hm'
        let k : Fin children.size := Classical.choose hmove
        have hk : children[k].1 = m := Classical.choose_spec hmove
        let x : Coord × Nat := children[k]
        have hx : x ∈ children := by
          dsimp [x]
          exact Array.getElem_mem k.isLt
        have hxmove : x.1 = m := by simpa [x] using hk
        have href : x.2 < c.nodes.size := hrefs x hx
        have hafter : i < x.2 := (hedge x hx).1
        have hmatch := (hedge x hx).2
        have hchildTree := ih (c.nodes.size - x.2) (by omega) x.2 (by rfl) href hall
        have hpos := (defenseChildPositionMatches_at_iff c.nodes x.2 href
          (play s x.1)).mp hmatch
        have hchildTree' : Nonempty (DefenseTree defender (play s m)) := by
          refine ⟨?_⟩
          rw [← hxmove, ← hpos]
          exact Classical.choice hchildTree
        exact Classical.choice hchildTree'

/-- 可靠性定理：任何通过 `checkDefenseCertificateAt` 的防御证书都证明
防守方 `c.defender` 从局面 `s` 能阻止攻击方获胜。 -/
theorem defense_certificate_sound (s : Position) (c : DefenseCertificate)
    (h : checkDefenseCertificateAt s c = true) :
    CanPreventWin c.defender s := by
  have hheader := checkDefenseCertificateAt_header s c h
  have hall := checkDefenseCertificateAt_nodes_checked s c h
  have htree := defense_reify_at c c.defender c.root hheader.1 hall
  have hrootpos := (defenseRootPositionMatches_at_iff s c hheader.1).mp hheader.2
  have htree' : Nonempty (DefenseTree c.defender s) := by
    refine ⟨?_⟩
    rw [← hrootpos]
    exact Classical.choice htree
  exact DefenseTree.sound (Classical.choice htree')

/-- 白方防守证书的可靠性：证书通过检查且 defender 为白方时，
推出 `WhiteCanPreventBlackWin`。 -/
theorem white_defense_certificate_sound (s : Position) (c : DefenseCertificate)
    (hdef : c.defender = .white) (h : checkDefenseCertificateAt s c = true) :
    WhiteCanPreventBlackWin s := by
  simpa [WhiteCanPreventBlackWin, hdef] using defense_certificate_sound s c h

/-- 黑方防守证书的可靠性：证书通过检查且 defender 为黑方时，
推出 `BlackCanPreventWhiteWin`。 -/
theorem black_defense_certificate_sound (s : Position) (c : DefenseCertificate)
    (hdef : c.defender = .black) (h : checkDefenseCertificateAt s c = true) :
    BlackCanPreventWhiteWin s := by
  simpa [BlackCanPreventWhiteWin, hdef] using defense_certificate_sound s c h

end Gomoku
