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
  ∃ x ∈ children.toList, x.1 = c

def allRefsValid (size : Nat) (children : Array (Coord × Nat)) : Bool :=
  children.all (fun x => x.2 < size)

def allMovesLegal (s : Position) (children : Array (Coord × Nat)) : Bool :=
  children.all (fun x => decide (legalMove s x.1))

def moveInBool (children : Array (Coord × Nat)) (c : Coord) : Bool :=
  children.any (fun x => x.1 == c)

def allLegalMovesCovered (s : Position) (children : Array (Coord × Nat)) : Bool :=
  (((Finset.univ : Finset Coord).filter
      (fun c => decide (legalMove s c) = true ∧ moveInBool children c = false)).card == 0)

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

def nodePosition : CertificateNode → Position
  | .terminal s _ => s
  | .proverMove s _ _ => s
  | .opponentMoves s _ => s

def samePosition (s t : Position) : Bool :=
  decide (s.turn = t.turn) &&
    (((Finset.univ : Finset Coord).filter
      (fun c => s.board.cell c ≠ t.board.cell c)).card == 0)

def childPositionMatches (nodes : Array CertificateNode) (ref : Nat) (expected : Position) : Bool :=
  match nodes[ref]? with
  | some node => samePosition (nodePosition node) expected
  | none => false

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

def rootPositionMatches (c : CompactCertificate) : Bool :=
  match c.nodes[c.root]? with
  | some node => samePosition (nodePosition node) initialPosition
  | none => false

def checkCertificate (c : CompactCertificate) : Bool :=
  decide (c.target = .black) && c.root < c.nodes.size && rootPositionMatches c &&
    (c.nodes.mapIdx (fun i node => checkNodeAt c.target c.nodes i node)).all id

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

end Gomoku
