import Gomoku.Tactics

/-!
可信证书层：定义依赖类型证明树与可执行紧凑证书，检查节点、边和根局面，并证明检查通过即可重构强制胜证明。
-/

namespace Gomoku

inductive CertificateTree (target : Player) : Position → Type where
  | terminal {s : Position}
      (h : terminal s = some (winner target)) : CertificateTree target s
  | proverMove {s : Position}
      (hterm : terminal s = none)
      (hturn : s.turn = target)
      (m : Coord)
      (hm : legalMove s m)
      (child : CertificateTree target (play s m)) : CertificateTree target s
  | opponentMoves {s : Position}
      (hterm : terminal s = none)
      (hturn : s.turn = Player.other target)
      (children : ∀ m, legalMove s m → CertificateTree target (play s m)) :
      CertificateTree target s
-- 以依赖类型保存完整获胜证书树，使终局、己方选择和对手全应手都携带相应证明。

theorem CertificateTree.sound {target : Player} {s : Position} :
    CertificateTree target s → CanForceWin s target
  | .terminal h => .terminal h
  | .proverMove hterm hturn m hm child =>
      .choose hterm hturn m hm (CertificateTree.sound child)
  | .opponentMoves hterm hturn children =>
      .respond hterm hturn (fun m hm => CertificateTree.sound (children m hm))
-- 递归解释证书树，把每个节点转换为 ForceWin，从而证明证书树的可靠性。

theorem ForceWin.nonemptyCertificateTree {target : Player} {s : Position} :
    ForceWin target s → Nonempty (CertificateTree target s)
  | .terminal h => ⟨.terminal h⟩
  | .choose hterm hturn m hm hchild =>
      match ForceWin.nonemptyCertificateTree hchild with
      | ⟨child⟩ => ⟨.proverMove hterm hturn m hm child⟩
  | .respond hterm hturn children =>
      ⟨.opponentMoves hterm hturn (fun m hm =>
        Classical.choice (ForceWin.nonemptyCertificateTree (children m hm)))⟩
-- 反向把抽象 ForceWin 证明转换为至少存在一棵对应的依赖类型证书树。

theorem certificateTree_iff_canForceWin {target : Player} {s : Position} :
    Nonempty (CertificateTree target s) ↔ CanForceWin s target := by
  constructor
  · intro h
    exact CertificateTree.sound (Classical.choice h)
  · intro h
    exact ForceWin.nonemptyCertificateTree h
-- 建立证书树存在性与 CanForceWin 的双向等价。

theorem strategyRealizes_iff_certificateTree
    {target : Player} {s : Position} (hs : Reachable s) :
    (∃ σ : Strategy target, StrategyRealizes σ s hs) ↔
      Nonempty (CertificateTree target s) := by
  rw [strategyRealizes_iff_canForceWin hs, certificateTree_iff_canForceWin]
-- 连接具体策略语义与证书树语义：可达局面存在实现策略当且仅当存在证书树。

structure Certificate where
  target : Player
  root : Position
  proof : CertificateTree target root
-- 封装目标玩家、根局面及其依赖类型证书树，形成直接携带证明的证书。

theorem certificate_sound (c : Certificate) :
    CanForceWin c.root c.target :=
  CertificateTree.sound c.proof
-- 从 Certificate 中保存的证书树直接得到根局面的 CanForceWin。

inductive CertificateNode where
  | terminal (position : Position) (winner : Outcome)
  | proverMove (position : Position) (move : Coord) (child : Nat)
  | opponentMoves (position : Position) (children : Array (Coord × Nat))
-- 定义可序列化的扁平证书节点，子树改用数组索引引用。

structure CompactCertificate where
  target : Player
  root : Nat
  nodes : Array CertificateNode
-- 用目标玩家、根索引和节点数组组成紧凑证书，供外部搜索器生成和 Lean 检查。

def refValid (size ref : Nat) : Bool := decide (ref < size)
-- 检查子节点引用是否落在节点数组范围内。

def moveIn (children : Array (Coord × Nat)) (c : Coord) : Prop :=
  ∃ i : Fin children.size, children[i].1 = c
-- 表示子节点数组中至少有一条边对应着法 c。

instance moveInDecidable (children : Array (Coord × Nat)) (c : Coord) :
    Decidable (moveIn children c) := by
  unfold moveIn
  exact Fintype.decidableExistsFintype
-- 通过有限数组索引穷举判定着法 c 是否出现在子边数组中。

def allRefsValid (size : Nat) (children : Array (Coord × Nat)) : Bool :=
  children.all (fun x => x.2 < size)
-- 检查对手子边数组中的每个节点引用是否都在给定范围内。

def allMovesLegal (s : Position) (children : Array (Coord × Nat)) : Bool :=
  children.all (fun x => decide (legalMove s x.1))
-- 检查子边数组列出的每个着法在父局面中是否合法。

def moveInBool (children : Array (Coord × Nat)) (c : Coord) : Bool :=
  decide (moveIn children c)
-- 把 moveIn 命题包装成可执行布尔检查。

theorem moveInBool_true_iff (children : Array (Coord × Nat)) (c : Coord) :
    moveInBool children c = true ↔ moveIn children c := by
  simp [moveInBool]
-- 证明布尔成员检查返回 true 与命题形式的 moveIn 完全等价。

def allLegalMovesCovered (s : Position) (children : Array (Coord × Nat)) : Bool :=
  (((Finset.univ : Finset Coord).filter
      (fun c => decide (legalMove s c) = true ∧ moveInBool children c = false)).card == 0)
-- 检查父局面的每个合法着法是否都被对手节点的子边数组覆盖。

theorem allRefsValid_true_iff (size : Nat) (children : Array (Coord × Nat)) :
    allRefsValid size children = true ↔
      ∀ x, x ∈ children → x.2 < size := by
  unfold allRefsValid
  rw [Array.all_eq_true']
  constructor
  · intro h x hx
    exact of_decide_eq_true (h x hx)
  · intro h x hx
    exact decide_eq_true_eq.mpr (h x hx)
-- 把 allRefsValid 的布尔结果展开为每条子边引用均小于数组大小的全称命题。

theorem allMovesLegal_true_iff (s : Position) (children : Array (Coord × Nat)) :
    allMovesLegal s children = true ↔
      ∀ x, x ∈ children → legalMove s x.1 := by
  unfold allMovesLegal
  rw [Array.all_eq_true']
  constructor
  · intro h x hx
    exact of_decide_eq_true (h x hx)
  · intro h x hx
    exact decide_eq_true_eq.mpr (h x hx)
-- 把 allMovesLegal 的布尔结果展开为数组中每个着法都合法的命题。

theorem allLegalMovesCovered_true_iff (s : Position)
    (children : Array (Coord × Nat)) :
    allLegalMovesCovered s children = true ↔
      ∀ c, legalMove s c → moveIn children c := by
  classical
  unfold allLegalMovesCovered
  constructor
  · intro h c hlegal
    by_contra hmissing
    have hmb : moveInBool children c = false := by
      cases hvalue : moveInBool children c with
      | false => simpa using hvalue
      | true => exact False.elim (hmissing ((moveInBool_true_iff children c).mp hvalue))
    have hc : c ∈ (Finset.univ : Finset Coord).filter
        (fun d => decide (legalMove s d) = true ∧ moveInBool children d = false) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true_eq.mpr hlegal, hmb⟩
    have hcard : ((Finset.univ : Finset Coord).filter
        (fun d => decide (legalMove s d) = true ∧ moveInBool children d = false)).card = 0 := by
      simpa using h
    have hempty := Finset.card_eq_zero.mp hcard
    rw [hempty] at hc
    exact False.elim (by simpa using hc)
  · intro h
    have hempty : (Finset.univ : Finset Coord).filter
        (fun c => decide (legalMove s c) = true ∧ moveInBool children c = false) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ hc
      have hlegal : legalMove s c := of_decide_eq_true hc.1
      have hcovered : moveIn children c := h c hlegal
      have hbool : moveInBool children c = true := (moveInBool_true_iff children c).mpr hcovered
      exact Bool.noConfusion (hc.2.symm.trans hbool)
    rw [hempty]
    rfl
-- 证明覆盖检查返回 true 当且仅当每个合法着法都能在子边数组中找到。

def checkNode (target : Player) (size : Nat) : CertificateNode → Bool
  | .terminal s out =>
      decide (terminal s = some out) && decide (out = winner target)
  | .proverMove s m child =>
      decide (terminal s = none) && decide (s.turn = target) &&
        decide (legalMove s m) &&
        refValid size child
  | .opponentMoves s children =>
      decide (terminal s = none) && decide (s.turn = Player.other target) &&
        allRefsValid size children && allMovesLegal s children &&
        allLegalMovesCovered s children
-- 检查单个证书节点的局部语义、轮次、合法性、引用范围及对手全应手覆盖。

def checkNode_terminal_reify {target : Player} {size : Nat} {s : Position} {out : Outcome}
    (h : checkNode target size (.terminal s out) = true) :
    CertificateTree target s := by
  simp [checkNode] at h
  exact .terminal (by simpa [h.2] using h.1)
-- 从通过局部检查的终局节点直接重建依赖类型 CertificateTree 终局节点。

theorem checkNode_terminal_iff {target : Player} {size : Nat} {s : Position} {out : Outcome} :
    checkNode target size (.terminal s out) = true ↔
      terminal s = some (winner target) ∧ out = winner target := by
  constructor
  · intro h
    simp only [checkNode, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
    have hterm : terminal s = some out := of_decide_eq_true h.1
    have hout : out = winner target := of_decide_eq_true h.2
    exact ⟨by simpa [hout] using hterm, hout⟩
  · rintro ⟨hterm, hout⟩
    simp [checkNode, hterm, hout]
-- 精确刻画终局节点通过检查的条件：局面胜者和节点记录结果都等于目标玩家胜利。

theorem checkNode_proverMove_iff {target : Player} {size : Nat} {s : Position}
    {m : Coord} {child : Nat} :
    checkNode target size (.proverMove s m child) = true ↔
      terminal s = none ∧ s.turn = target ∧ legalMove s m ∧ child < size := by
  simp [checkNode, refValid, and_comm, and_left_comm, and_assoc]
-- 精确刻画己方着法节点通过局部检查所需的非终局、轮次、合法性和引用范围条件。

def nodePosition : CertificateNode → Position
  | .terminal s _ => s
  | .proverMove s _ _ => s
  | .opponentMoves s _ => s
-- 从任意紧凑证书节点中提取其记录的父局面。

def samePosition (s t : Position) : Bool :=
  decide (s.turn = t.turn) &&
    (((Finset.univ : Finset Coord).filter
      (fun c => s.board.cell c ≠ t.board.cell c)).card == 0)
-- 逐格比较棋盘并比较轮次，以布尔值判断两个局面是否完全相同。

theorem samePosition_self (s : Position) : samePosition s s = true := by
  simp [samePosition]
-- 证明任意局面与自身的可执行比较必返回 true。

theorem samePosition_true_iff (s t : Position) :
    samePosition s t = true ↔ s = t := by
  classical
  constructor
  · intro h
    simp only [samePosition, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
    have hturn : s.turn = t.turn := of_decide_eq_true h.1
    have hcard :
        ((Finset.univ : Finset Coord).filter
          (fun c => s.board.cell c ≠ t.board.cell c)).card = 0 := by
      simpa using h.2
    have hfilter :
        (Finset.univ : Finset Coord).filter
          (fun c => s.board.cell c ≠ t.board.cell c) = ∅ :=
      Finset.card_eq_zero.mp hcard
    have hcell : ∀ c, s.board.cell c = t.board.cell c := by
      intro c
      by_contra hne
      have hc : c ∈ (Finset.univ : Finset Coord).filter
          (fun c => s.board.cell c ≠ t.board.cell c) := by
        simp [hne]
      rw [hfilter] at hc
      simp at hc
    cases s with
    | mk sb st =>
      cases t with
      | mk tb tt =>
        cases hturn
        cases sb with
        | mk sb =>
          cases tb with
          | mk tb =>
            congr
            funext c
            exact hcell c
  · intro h
    cases h
    exact samePosition_self _
-- 证明可执行局面比较返回 true 当且仅当两个 Position 在 Lean 中相等。

def childPositionMatches (nodes : Array CertificateNode) (ref : Nat) (expected : Position) : Bool :=
  match nodes[ref]? with
  | some node => samePosition (nodePosition node) expected
  | none => false
-- 检查引用存在且对应子节点记录的局面等于预期的落子后局面。

theorem childPositionMatches_true_iff (nodes : Array CertificateNode) (ref : Nat)
    (expected : Position) :
    childPositionMatches nodes ref expected = true ↔
      ∃ node, nodes[ref]? = some node ∧ nodePosition node = expected := by
  cases hnode : nodes[ref]? with
  | none => simp [childPositionMatches, hnode]
  | some node =>
      simp [childPositionMatches, hnode, samePosition_true_iff]
-- 把子局面匹配检查展开为存在被引用节点且其局面等于预期局面。

theorem childPositionMatches_at_iff (nodes : Array CertificateNode) (ref : Nat)
    (href : ref < nodes.size) (expected : Position) :
    childPositionMatches nodes ref expected = true ↔
      nodePosition nodes[ref] = expected := by
  have hlookup : nodes[ref]? = some nodes[ref] := by simp [href]
  simp [childPositionMatches, hlookup, samePosition_true_iff]
-- 在已知引用有效时，将子局面匹配简化为数组取值节点的局面相等。

def checkEdges (nodes : Array CertificateNode) : CertificateNode → Bool
  | .terminal _ _ => true
  | .proverMove s m child =>
      childPositionMatches nodes child (play s m)
  | .opponentMoves s children =>
      children.all (fun x => childPositionMatches nodes x.2 (play s x.1))
-- 检查每条证书边引用的子节点局面是否精确等于执行相应着法后的局面。

def refAfter (parent child : Nat) : Bool := decide (parent < child)
-- 检查子节点索引是否严格位于父节点之后，为逆序重建提供良基顺序。

def checkEdgesAt (nodes : Array CertificateNode) (parent : Nat) : CertificateNode → Bool
  | .terminal _ _ => true
  | .proverMove s m child =>
      refAfter parent child && childPositionMatches nodes child (play s m)
  | .opponentMoves s children =>
      children.all (fun x =>
        refAfter parent x.2 && childPositionMatches nodes x.2 (play s x.1))
-- 在局面匹配之外要求所有子引用严格向后，排除环和反向边。

def checkNodeWithEdges (target : Player) (nodes : Array CertificateNode)
    (node : CertificateNode) : Bool :=
  checkNode target nodes.size node && checkEdges nodes node
-- 组合节点局部语义检查与不含父索引顺序要求的边局面检查。

def checkNodeAt (target : Player) (nodes : Array CertificateNode)
    (parent : Nat) (node : CertificateNode) : Bool :=
  checkNode target nodes.size node && checkEdgesAt nodes parent node
-- 在指定父索引处完整检查节点语义、子引用顺序和子局面一致性。

theorem checkNodeAt_proverMove_iff (target : Player) (nodes : Array CertificateNode)
    (parent : Nat) (s : Position) (m : Coord) (child : Nat) :
    checkNodeAt target nodes parent (.proverMove s m child) = true ↔
      terminal s = none ∧ s.turn = target ∧ legalMove s m ∧ parent < child ∧
        child < nodes.size ∧
        childPositionMatches nodes child (play s m) = true := by
  constructor
  · intro h
    simp [checkNodeAt, checkNode, checkEdgesAt, refValid, refAfter] at h
    aesop
  · rintro ⟨hterm, hturn, hlegal, hafter, hchild, hmatch⟩
    simp [checkNodeAt, checkNode, checkEdgesAt, refValid, refAfter,
      hterm, hturn, hlegal, hafter, hchild, hmatch]
-- 完整展开己方节点通过 checkNodeAt 的所有必要充分条件。

theorem checkNodeAt_terminal_iff (target : Player) (nodes : Array CertificateNode)
    (parent : Nat) (s : Position) (out : Outcome) :
    checkNodeAt target nodes parent (.terminal s out) = true ↔
      terminal s = some (winner target) ∧ out = winner target := by
  simp only [checkNodeAt, checkEdgesAt, Bool.and_true]
  exact checkNode_terminal_iff
-- 说明终局节点没有子边，因此带索引检查退化为终局局部检查。

theorem checkNodeAt_opponentMoves_iff (target : Player) (nodes : Array CertificateNode)
    (parent : Nat) (s : Position) (children : Array (Coord × Nat)) :
    checkNodeAt target nodes parent (.opponentMoves s children) = true ↔
      terminal s = none ∧ s.turn = Player.other target ∧
        (∀ x, x ∈ children → x.2 < nodes.size) ∧
        (∀ x, x ∈ children → legalMove s x.1) ∧
        (∀ c, legalMove s c → moveIn children c) ∧
        (∀ x, x ∈ children → parent < x.2 ∧
          childPositionMatches nodes x.2 (play s x.1) = true) := by
  constructor
  · intro h
    have hparts :
        checkNode target nodes.size (.opponentMoves s children) = true ∧
          checkEdgesAt nodes parent (.opponentMoves s children) = true := by
      simpa only [checkNodeAt, Bool.and_eq_true_eq_eq_true_and_eq_true] using h
    have hnode := hparts.1
    simp only [checkNode, Bool.and_eq_true_eq_eq_true_and_eq_true] at hnode
    have htermB : decide (terminal s = none) = true := by aesop
    have hturnB : decide (s.turn = Player.other target) = true := by aesop
    have hrefsB : allRefsValid nodes.size children = true := by aesop
    have hmovesB : allMovesLegal s children = true := by aesop
    have hcoverB : allLegalMovesCovered s children = true := by aesop
    have hterm : terminal s = none := of_decide_eq_true htermB
    have hturn : s.turn = Player.other target := of_decide_eq_true hturnB
    have hrefs := (allRefsValid_true_iff nodes.size children).mp hrefsB
    have hmoves := (allMovesLegal_true_iff s children).mp hmovesB
    have hcover := (allLegalMovesCovered_true_iff s children).mp hcoverB
    have hedge := hparts.2
    simp only [checkEdgesAt, Array.all_eq_true'] at hedge
    have hedge' : ∀ x, x ∈ children → parent < x.2 ∧
        childPositionMatches nodes x.2 (play s x.1) = true := by
      intro x hx
      simpa [refAfter, Bool.and_eq_true_eq_eq_true_and_eq_true] using hedge x hx
    exact ⟨hterm, hturn, hrefs, hmoves, hcover, hedge'⟩
  · rintro ⟨hterm, hturn, hrefs, hmoves, hcover, hedge⟩
    have hrefsB : allRefsValid nodes.size children = true :=
      (allRefsValid_true_iff nodes.size children).mpr hrefs
    have hmovesB : allMovesLegal s children = true :=
      (allMovesLegal_true_iff s children).mpr hmoves
    have hcoverB : allLegalMovesCovered s children = true :=
      (allLegalMovesCovered_true_iff s children).mpr hcover
    have hedgeB : checkEdgesAt nodes parent (.opponentMoves s children) = true := by
      simp only [checkEdgesAt, Array.all_eq_true']
      intro x hx
      have hx' := hedge x hx
      simpa [refAfter, Bool.and_eq_true_eq_eq_true_and_eq_true] using hx'
    have hnodeB : checkNode target nodes.size (.opponentMoves s children) = true := by
      simp [checkNode, hterm, hturn, hrefsB, hmovesB, hcoverB]
    simpa only [checkNodeAt, Bool.and_eq_true_eq_eq_true_and_eq_true] using And.intro hnodeB hedgeB
-- 完整展开对手节点检查条件，包括非终局、正确轮次、合法全覆盖及每条向后边的局面匹配。

def rootPositionMatches (c : CompactCertificate) : Bool :=
  match c.nodes[c.root]? with
  | some node => samePosition (nodePosition node) initialPosition
  | none => false
-- 检查紧凑证书的根引用存在且根节点局面等于标准初始局面。

def checkCertificate (c : CompactCertificate) : Bool :=
  decide (c.target = .black) && c.root < c.nodes.size && rootPositionMatches c &&
    (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id
-- 检查用于全局定理的证书：目标必须为黑方、根为初始局面且全部节点通过完整检查。

/- A local certificate uses the same trusted node and edge checks as a global
   certificate, but deliberately does not require the root to be the empty
   board with Black to move.  This is the interface for tactic certificates
   and for small search results rooted at an arbitrary reachable position.
   It does not weaken `checkCertificate`, whose root convention is part of the
   statement of the fixed 7×7 theorem. -/
def checkLocalCertificate (c : CompactCertificate) : Bool :=
  c.root < c.nodes.size &&
    (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id
-- 检查任意根局面的局部证书，复用全部节点与边检查但不固定目标或初始根。

def localRootPositionMatches (s : Position) (c : CompactCertificate) : Bool :=
  match c.nodes[c.root]? with
  | some node => samePosition (nodePosition node) s
  | none => false
-- 检查局部证书根节点记录的局面是否等于调用方指定的局面 s。

def checkLocalCertificateAt (s : Position) (c : CompactCertificate) : Bool :=
  checkLocalCertificate c && localRootPositionMatches s c
-- 组合局部证书结构检查与指定根局面匹配检查。

def initialCertificateRoot (c : CompactCertificate) : Prop :=
  c.root < c.nodes.size ∧
    match c.nodes[c.root]? with
    | some (.terminal s _) => s = initialPosition
    | some (.proverMove s _ _) => s = initialPosition
    | some (.opponentMoves s _) => s = initialPosition
    | none => False
-- 以命题形式描述证书根引用有效且任意种类根节点都记录标准初始局面。

theorem checkCertificate_header (c : CompactCertificate) (h : checkCertificate c = true) :
    c.target = .black ∧ c.root < c.nodes.size ∧ rootPositionMatches c = true := by
  simp [checkCertificate] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
-- 从全局证书检查结果中提取黑方目标、有效根索引和初始根匹配三个头部条件。

theorem mapIdx_all_true_iff (nodes : Array CertificateNode)
    (f : Nat → CertificateNode → Bool) :
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
-- 将 mapIdx 后数组全部为 true 的条件转换为对每个有效索引逐点检查为 true。

theorem checkLocalCertificate_header (c : CompactCertificate)
    (h : checkLocalCertificate c = true) :
    c.root < c.nodes.size := by
  simp only [checkLocalCertificate, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true h.1
-- 从局部证书检查结果中提取根索引有效性。

theorem checkLocalCertificate_nodes_checked (c : CompactCertificate)
    (h : checkLocalCertificate c = true) :
    ∀ i (hi : i < c.nodes.size),
      checkNodeAt c.target c.nodes i c.nodes[i] = true := by
  have hmap :
      (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id = true := by
    simp only [checkLocalCertificate, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
    exact h.2
  exact (mapIdx_all_true_iff c.nodes
    (fun i node => checkNodeAt c.target c.nodes i node)).mp hmap
-- 从局部证书整体检查中提取每个有效节点均通过 checkNodeAt 的事实。

theorem checkCertificate_nodes_checked (c : CompactCertificate)
    (h : checkCertificate c = true) :
    ∀ i (hi : i < c.nodes.size),
      checkNodeAt c.target c.nodes i c.nodes[i] = true := by
  have hmap :
      (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id = true := by
    simp only [checkCertificate, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
    aesop
  exact (mapIdx_all_true_iff c.nodes
    (fun i node => checkNodeAt c.target c.nodes i node)).mp hmap
-- 从全局证书整体检查中提取全部节点的逐点检查结论。

theorem compact_reify_at (c : CompactCertificate) (target : Player) :
    ∀ (i : Nat) (hi : i < c.nodes.size),
      (∀ j (hj : j < c.nodes.size),
        checkNodeAt target c.nodes j c.nodes[j] = true) →
      Nonempty (CertificateTree target (nodePosition c.nodes[i])) := by
  intro i
  induction hmeasure : c.nodes.size - i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    intro hi hall
    cases hnode : c.nodes[i] with
    | terminal s out =>
        have hcheck := hall i hi
        rw [hnode] at hcheck
        have hvalid := (checkNodeAt_terminal_iff target c.nodes i s out).mp hcheck
        change Nonempty (CertificateTree target s)
        exact ⟨.terminal hvalid.1⟩
    | proverMove s m child =>
        have hcheck := hall i hi
        rw [hnode] at hcheck
        have hvalid := (checkNodeAt_proverMove_iff target c.nodes i s m child).mp hcheck
        rcases hvalid with ⟨hterm, hturn, hm, hafter, hchild, hmatch⟩
        have hchildTree := ih (c.nodes.size - child) (by omega) child (by rfl) hchild hall
        have hpos := (childPositionMatches_at_iff c.nodes child hchild
          (play s m)).mp hmatch
        have hchildTree' : Nonempty (CertificateTree target (play s m)) := by
          refine ⟨?_⟩
          rw [← hpos]
          exact Classical.choice hchildTree
        change Nonempty (CertificateTree target s)
        exact ⟨.proverMove hterm hturn m hm (Classical.choice hchildTree')⟩
    | opponentMoves s children =>
        have hcheck := hall i hi
        rw [hnode] at hcheck
        have hvalid :=
          (checkNodeAt_opponentMoves_iff target c.nodes i s children).mp hcheck
        rcases hvalid with ⟨hterm, hturn, hrefs, hmoves, hcover, hedge⟩
        change Nonempty (CertificateTree target s)
        refine ⟨.opponentMoves hterm hturn ?_⟩
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
        have hpos := (childPositionMatches_at_iff c.nodes x.2 href
          (play s x.1)).mp hmatch
        have hchildTree' : Nonempty (CertificateTree target (play s m)) := by
          refine ⟨?_⟩
          rw [← hxmove, ← hpos]
          exact Classical.choice hchildTree
        exact Classical.choice hchildTree'
-- 利用子引用严格向后的度量，对紧凑数组节点做良基递归并重建依赖类型 CertificateTree。

theorem local_certificate_sound (c : CompactCertificate)
    (hroot : c.root < c.nodes.size)
    (h : checkLocalCertificate c = true) :
    CanForceWin (nodePosition c.nodes[c.root]) c.target := by
  have hchecked := checkLocalCertificate_nodes_checked c h
  have htree := compact_reify_at c c.target c.root hroot hchecked
  exact CertificateTree.sound (Classical.choice htree)
-- 证明通过检查的局部紧凑证书可在其记录的根局面推出目标玩家 CanForceWin。

theorem localRootPositionMatches_at_iff (s : Position) (c : CompactCertificate)
    (hroot : c.root < c.nodes.size) :
    localRootPositionMatches s c = true ↔
      nodePosition c.nodes[c.root] = s := by
  have hlookup : c.nodes[c.root]? = some c.nodes[c.root] := by simp [hroot]
  simp [localRootPositionMatches, hlookup, samePosition_true_iff]
-- 在根引用有效时，把局部根匹配布尔值等价化为根节点局面与 s 相等。

theorem local_certificate_at_sound (s : Position) (c : CompactCertificate)
    (h : checkLocalCertificateAt s c = true) :
    CanForceWin s c.target := by
  have hparts : checkLocalCertificate c = true ∧
      localRootPositionMatches s c = true := by
    simpa only [checkLocalCertificateAt, Bool.and_eq_true_eq_eq_true_and_eq_true] using h
  have hroot := checkLocalCertificate_header c hparts.1
  have hrootpos := (localRootPositionMatches_at_iff s c hroot).mp hparts.2
  have hwin := local_certificate_sound c hroot hparts.1
  simpa [hrootpos] using hwin
-- 证明通过指定根检查的局部证书可以直接推出调用方局面 s 上的 CanForceWin。

theorem rootPositionMatches_at_iff (c : CompactCertificate)
    (hroot : c.root < c.nodes.size) :
    rootPositionMatches c = true ↔
      nodePosition c.nodes[c.root] = initialPosition := by
  have hlookup : c.nodes[c.root]? = some c.nodes[c.root] := by simp [hroot]
  simp [rootPositionMatches, hlookup, samePosition_true_iff]
-- 在根引用有效时，把全局根匹配检查等价化为根节点局面等于 initialPosition。

theorem compact_certificate_sound (c : CompactCertificate)
    (h : checkCertificate c = true) :
    CanForceWin initialPosition .black := by
  have hheader := checkCertificate_header c h
  have hall := checkCertificate_nodes_checked c h
  have hallBlack :
      ∀ j (hj : j < c.nodes.size),
        checkNodeAt .black c.nodes j c.nodes[j] = true := by
    intro j hj
    simpa [hheader.1] using hall j hj
  have hrootpos := (rootPositionMatches_at_iff c hheader.2.1).mp hheader.2.2
  have htree := compact_reify_at c .black c.root hheader.2.1 hallBlack
  have hrootTree : CertificateTree .black initialPosition := by
    simpa [hrootpos] using Classical.choice htree
  exact CertificateTree.sound hrootTree
-- 全局可靠性定理：任何通过 checkCertificate 的紧凑证书都证明黑方从初始局面可强制获胜。

end Gomoku
