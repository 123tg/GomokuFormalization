import Gomoku.Tactics

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

theorem CertificateTree.sound {target : Player} {s : Position} :
    CertificateTree target s → CanForceWin s target
  | .terminal h => .terminal h
  | .proverMove hterm hturn m hm child =>
      .choose hterm hturn m hm (CertificateTree.sound child)
  | .opponentMoves hterm hturn children =>
      .respond hterm hturn (fun m hm => CertificateTree.sound (children m hm))

theorem ForceWin.nonemptyCertificateTree {target : Player} {s : Position} :
    ForceWin target s → Nonempty (CertificateTree target s)
  | .terminal h => ⟨.terminal h⟩
  | .choose hterm hturn m hm hchild =>
      match ForceWin.nonemptyCertificateTree hchild with
      | ⟨child⟩ => ⟨.proverMove hterm hturn m hm child⟩
  | .respond hterm hturn children =>
      ⟨.opponentMoves hterm hturn (fun m hm =>
        Classical.choice (ForceWin.nonemptyCertificateTree (children m hm)))⟩

theorem certificateTree_iff_canForceWin {target : Player} {s : Position} :
    Nonempty (CertificateTree target s) ↔ CanForceWin s target := by
  constructor
  · intro h
    exact CertificateTree.sound (Classical.choice h)
  · intro h
    exact ForceWin.nonemptyCertificateTree h

theorem strategyRealizes_iff_certificateTree
    {target : Player} {s : Position} (hs : Reachable s) :
    (∃ σ : Strategy target, StrategyRealizes σ s hs) ↔
      Nonempty (CertificateTree target s) := by
  rw [strategyRealizes_iff_canForceWin hs, certificateTree_iff_canForceWin]

structure Certificate where
  target : Player
  root : Position
  proof : CertificateTree target root

theorem certificate_sound (c : Certificate) :
    CanForceWin c.root c.target :=
  CertificateTree.sound c.proof

inductive CertificateNode where
  | terminal (position : Position) (winner : Outcome)
  | proverMove (position : Position) (move : Coord) (child : Nat)
  | opponentMoves (position : Position) (children : Array (Coord × Nat))

structure CompactCertificate where
  target : Player
  root : Nat
  nodes : Array CertificateNode

def refValid (size ref : Nat) : Bool := decide (ref < size)

def moveIn (children : Array (Coord × Nat)) (c : Coord) : Prop :=
  ∃ i : Fin children.size, children[i].1 = c

instance moveInDecidable (children : Array (Coord × Nat)) (c : Coord) :
    Decidable (moveIn children c) := by
  unfold moveIn
  exact Fintype.decidableExistsFintype

def allRefsValid (size : Nat) (children : Array (Coord × Nat)) : Bool :=
  children.all (fun x => x.2 < size)

def allMovesLegal (s : Position) (children : Array (Coord × Nat)) : Bool :=
  children.all (fun x => decide (legalMove s x.1))

def moveInBool (children : Array (Coord × Nat)) (c : Coord) : Bool :=
  decide (moveIn children c)

theorem moveInBool_true_iff (children : Array (Coord × Nat)) (c : Coord) :
    moveInBool children c = true ↔ moveIn children c := by
  simp [moveInBool]

def allLegalMovesCovered (s : Position) (children : Array (Coord × Nat)) : Bool :=
  (((Finset.univ : Finset Coord).filter
      (fun c => decide (legalMove s c) = true ∧ moveInBool children c = false)).card == 0)

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

def checkNode_terminal_reify {target : Player} {size : Nat} {s : Position} {out : Outcome}
    (h : checkNode target size (.terminal s out) = true) :
    CertificateTree target s := by
  simp [checkNode] at h
  exact .terminal (by simpa [h.2] using h.1)

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

theorem checkNode_proverMove_iff {target : Player} {size : Nat} {s : Position}
    {m : Coord} {child : Nat} :
    checkNode target size (.proverMove s m child) = true ↔
      terminal s = none ∧ s.turn = target ∧ legalMove s m ∧ child < size := by
  simp [checkNode, refValid, and_comm, and_left_comm, and_assoc]

def nodePosition : CertificateNode → Position
  | .terminal s _ => s
  | .proverMove s _ _ => s
  | .opponentMoves s _ => s

def samePosition (s t : Position) : Bool :=
  decide (s.turn = t.turn) &&
    (((Finset.univ : Finset Coord).filter
      (fun c => s.board.cell c ≠ t.board.cell c)).card == 0)

theorem samePosition_self (s : Position) : samePosition s s = true := by
  simp [samePosition]

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

def childPositionMatches (nodes : Array CertificateNode) (ref : Nat) (expected : Position) : Bool :=
  match nodes[ref]? with
  | some node => samePosition (nodePosition node) expected
  | none => false

theorem childPositionMatches_true_iff (nodes : Array CertificateNode) (ref : Nat)
    (expected : Position) :
    childPositionMatches nodes ref expected = true ↔
      ∃ node, nodes[ref]? = some node ∧ nodePosition node = expected := by
  cases hnode : nodes[ref]? with
  | none => simp [childPositionMatches, hnode]
  | some node =>
      simp [childPositionMatches, hnode, samePosition_true_iff]

theorem childPositionMatches_at_iff (nodes : Array CertificateNode) (ref : Nat)
    (href : ref < nodes.size) (expected : Position) :
    childPositionMatches nodes ref expected = true ↔
      nodePosition nodes[ref] = expected := by
  have hlookup : nodes[ref]? = some nodes[ref] := by simp [href]
  simp [childPositionMatches, hlookup, samePosition_true_iff]

def checkEdges (nodes : Array CertificateNode) : CertificateNode → Bool
  | .terminal _ _ => true
  | .proverMove s m child =>
      childPositionMatches nodes child (play s m)
  | .opponentMoves s children =>
      children.all (fun x => childPositionMatches nodes x.2 (play s x.1))

def refAfter (parent child : Nat) : Bool := decide (parent < child)

def checkEdgesAt (nodes : Array CertificateNode) (parent : Nat) : CertificateNode → Bool
  | .terminal _ _ => true
  | .proverMove s m child =>
      refAfter parent child && childPositionMatches nodes child (play s m)
  | .opponentMoves s children =>
      children.all (fun x =>
        refAfter parent x.2 && childPositionMatches nodes x.2 (play s x.1))

def checkNodeWithEdges (target : Player) (nodes : Array CertificateNode)
    (node : CertificateNode) : Bool :=
  checkNode target nodes.size node && checkEdges nodes node

def checkNodeAt (target : Player) (nodes : Array CertificateNode)
    (parent : Nat) (node : CertificateNode) : Bool :=
  checkNode target nodes.size node && checkEdgesAt nodes parent node

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

theorem checkNodeAt_terminal_iff (target : Player) (nodes : Array CertificateNode)
    (parent : Nat) (s : Position) (out : Outcome) :
    checkNodeAt target nodes parent (.terminal s out) = true ↔
      terminal s = some (winner target) ∧ out = winner target := by
  simp only [checkNodeAt, checkEdgesAt, Bool.and_true]
  exact checkNode_terminal_iff

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

def rootPositionMatches (c : CompactCertificate) : Bool :=
  match c.nodes[c.root]? with
  | some node => samePosition (nodePosition node) initialPosition
  | none => false

def checkCertificate (c : CompactCertificate) : Bool :=
  decide (c.target = .black) && c.root < c.nodes.size && rootPositionMatches c &&
    (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id

/- A local certificate uses the same trusted node and edge checks as a global
   certificate, but deliberately does not require the root to be the empty
   board with Black to move.  This is the interface for tactic certificates
   and for small search results rooted at an arbitrary reachable position.
   It does not weaken `checkCertificate`, whose root convention is part of the
   statement of the 15x15 theorem. -/
def checkLocalCertificate (c : CompactCertificate) : Bool :=
  c.root < c.nodes.size &&
    (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id

def localRootPositionMatches (s : Position) (c : CompactCertificate) : Bool :=
  match c.nodes[c.root]? with
  | some node => samePosition (nodePosition node) s
  | none => false

def checkLocalCertificateAt (s : Position) (c : CompactCertificate) : Bool :=
  checkLocalCertificate c && localRootPositionMatches s c

def initialCertificateRoot (c : CompactCertificate) : Prop :=
  c.root < c.nodes.size ∧
    match c.nodes[c.root]? with
    | some (.terminal s _) => s = initialPosition
    | some (.proverMove s _ _) => s = initialPosition
    | some (.opponentMoves s _) => s = initialPosition
    | none => False

theorem checkCertificate_header (c : CompactCertificate) (h : checkCertificate c = true) :
    c.target = .black ∧ c.root < c.nodes.size ∧ rootPositionMatches c = true := by
  simp [checkCertificate] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

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

theorem checkLocalCertificate_header (c : CompactCertificate)
    (h : checkLocalCertificate c = true) :
    c.root < c.nodes.size := by
  simp only [checkLocalCertificate, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  exact of_decide_eq_true h.1

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

theorem local_certificate_sound (c : CompactCertificate)
    (hroot : c.root < c.nodes.size)
    (h : checkLocalCertificate c = true) :
    CanForceWin (nodePosition c.nodes[c.root]) c.target := by
  have hchecked := checkLocalCertificate_nodes_checked c h
  have htree := compact_reify_at c c.target c.root hroot hchecked
  exact CertificateTree.sound (Classical.choice htree)

theorem localRootPositionMatches_at_iff (s : Position) (c : CompactCertificate)
    (hroot : c.root < c.nodes.size) :
    localRootPositionMatches s c = true ↔
      nodePosition c.nodes[c.root] = s := by
  have hlookup : c.nodes[c.root]? = some c.nodes[c.root] := by simp [hroot]
  simp [localRootPositionMatches, hlookup, samePosition_true_iff]

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

theorem rootPositionMatches_at_iff (c : CompactCertificate)
    (hroot : c.root < c.nodes.size) :
    rootPositionMatches c = true ↔
      nodePosition c.nodes[c.root] = initialPosition := by
  have hlookup : c.nodes[c.root]? = some c.nodes[c.root] := by simp [hroot]
  simp [rootPositionMatches, hlookup, samePosition_true_iff]

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

end Gomoku
