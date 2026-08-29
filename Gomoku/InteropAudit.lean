import Gomoku.Certificate
import Gomoku.RuleAudit
import Gomoku.Generated.CppReachable
import Gomoku.Generated.CppReachableDoubleThreat

namespace Gomoku

/-!
Interoperability regression for external searchers.

The C++ searcher writes a root position as an array of `(Coord × Player)`
stones and writes the proof as a `CompactCertificate`.  This module freezes the
small Lean-side adapter for that format.  The array is untrusted input: its
folding behavior is deliberately simple, and the certificate checker remains
responsible for validating every recorded move and child position.
-/

def boardFromStones (stones : Array (Coord × Player)) : Board :=
  stones.foldl (fun board stone => Board.place board stone.1 stone.2) Board.empty

def positionFromStones (stones : Array (Coord × Player)) (turn : Player) : Position :=
  ⟨boardFromStones stones, turn⟩

def checkExternalLocalCertificate (stones : Array (Coord × Player))
    (turn : Player) (certificate : CompactCertificate) : Bool :=
  checkLocalCertificateAt (positionFromStones stones turn) certificate

/- A serializer should not silently overwrite a coordinate that it emitted
   twice.  The permissive adapter above remains useful for arbitrary local
   roots; this stricter entry point is for exporters that promise one record
   per occupied cell. -/
def externalStoneCoordsNodup (stones : Array (Coord × Player)) : Bool :=
  (stones.toList.map Prod.fst).eraseDups.length == stones.size

def checkExternalLocalCertificateStrict (stones : Array (Coord × Player))
    (turn : Player) (certificate : CompactCertificate) : Bool :=
  externalStoneCoordsNodup stones &&
    checkExternalLocalCertificate stones turn certificate

theorem checkExternalLocalCertificate_sound
    (stones : Array (Coord × Player)) (turn : Player)
    (certificate : CompactCertificate)
    (h : checkExternalLocalCertificate stones turn certificate = true) :
    CanForceWin (positionFromStones stones turn) certificate.target := by
  exact local_certificate_at_sound (positionFromStones stones turn)
    certificate h

theorem checkExternalLocalCertificateStrict_sound
    (stones : Array (Coord × Player)) (turn : Player)
    (certificate : CompactCertificate)
    (h : checkExternalLocalCertificateStrict stones turn certificate = true) :
    CanForceWin (positionFromStones stones turn) certificate.target := by
  have hparts : externalStoneCoordsNodup stones = true ∧
      checkExternalLocalCertificate stones turn certificate = true := by
    simpa [checkExternalLocalCertificateStrict] using h
  exact checkExternalLocalCertificate_sound stones turn certificate hparts.2

/- This fixture has exactly the shape emitted by the teammate's C++ exporter:
   four black stones, Black to move, and a two-node immediate-win proof. -/
def externalStyleRootStones : Array (Coord × Player) := #[
  ((5, 7), .black),
  ((6, 7), .black),
  ((7, 7), .black),
  ((8, 7), .black)
]

def externalStyleRootPosition : Position :=
  positionFromStones externalStyleRootStones .black

def externalStyleWinningMove : Coord := (9, 7)

def externalStyleCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove externalStyleRootPosition externalStyleWinningMove 1,
      .terminal (play externalStyleRootPosition externalStyleWinningMove)
        .blackWin
    ] }

def externalStyleDuplicateRootStones : Array (Coord × Player) :=
  externalStyleRootStones.push ((5, 7), .black)

set_option linter.style.nativeDecide false in
theorem externalStyleCertificate_checked :
    checkExternalLocalCertificate externalStyleRootStones .black
      externalStyleCertificate = true := by
  native_decide

theorem externalStyleCertificate_sound :
    CanForceWin externalStyleRootPosition .black := by
  exact checkExternalLocalCertificate_sound externalStyleRootStones .black
    externalStyleCertificate externalStyleCertificate_checked

/- The permissive adapter folds the duplicate away, so this certificate still
   passes there.  The strict adapter rejects the same input before checking the
   certificate, exposing the exporter bug instead of silently accepting it. -/
set_option linter.style.nativeDecide false in
example : externalStoneCoordsNodup externalStyleDuplicateRootStones = False := by
  native_decide

set_option linter.style.nativeDecide false in
example : checkExternalLocalCertificate externalStyleDuplicateRootStones .black
    externalStyleCertificate = true := by
  native_decide

set_option linter.style.nativeDecide false in
example : checkExternalLocalCertificateStrict externalStyleDuplicateRootStones .black
    externalStyleCertificate = false := by
  native_decide

/- A wrong child position is rejected even though the surrounding data has the
   same shape.  This protects the boundary against a serializer bug. -/
def externalStyleMalformedCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove externalStyleRootPosition externalStyleWinningMove 1,
      .terminal externalStyleRootPosition .blackWin
    ] }

set_option linter.style.nativeDecide false in
example :
    checkExternalLocalCertificate externalStyleRootStones .black
      externalStyleMalformedCertificate = false := by
  native_decide

example :
    (positionFromStones externalStyleRootStones .black).board.count .black = 4 := by
  native_decide

/- This certificate was generated from a position that is also constructed by
   the trusted legal move history in `RuleAudit`.  The equality is checked via
   the finite extensional boolean comparator; it connects the external array
   representation to the formal reachability theorem without trusting the
   generator's history claims. -/
theorem cppReachableRoot_matches_audit :
    Generated.cppReachableRootPosition = auditReachableImmediatePosition := by
  apply (samePosition_true_iff _ _).mp
  native_decide

theorem cppReachableRoot_reachable :
    Reachable Generated.cppReachableRootPosition := by
  rw [cppReachableRoot_matches_audit]
  exact auditReachableImmediate_reachable

theorem cppReachableCertificate_reachable_sound :
    CanForceWin Generated.cppReachableRootPosition .black := by
  exact Generated.cppReachableCertificate_sound

/- The larger generated certificate has a sparse but genuinely reachable root:
   each side has eight stones, White is to move, and Black has two independent
   four-lines.  Every one of White's 208 legal replies is represented in the
   generated opponent node. -/
def cppReachableDoubleThreatMoves : List Coord :=
  [ (10, 4), (0, 0), (10, 5), (2, 0),
    (10, 6), (4, 0), (10, 7), (6, 0),
    (3, 8), (0, 2), (4, 8), (2, 2),
    (5, 8), (4, 2), (6, 8), (6, 2),
    (14, 14) ]

def cppReachableDoubleThreatPosition : Position :=
  Position.playMoves Position.initial cppReachableDoubleThreatMoves

theorem cppReachableDoubleThreat_moves_legal :
    Position.LegalMoveSequence Position.initial
      cppReachableDoubleThreatMoves := by
  native_decide

theorem cppReachableDoubleThreat_reachable :
    Reachable cppReachableDoubleThreatPosition := by
  exact Position.reachable_playMoves Position.Reachable.initial
    cppReachableDoubleThreatMoves cppReachableDoubleThreat_moves_legal

theorem cppReachableDoubleThreatRoot_matches_history :
    Generated.cppReachableDoubleThreatRootPosition =
      cppReachableDoubleThreatPosition := by
  apply (samePosition_true_iff _ _).mp
  native_decide

theorem cppReachableDoubleThreatRoot_reachable :
    Reachable Generated.cppReachableDoubleThreatRootPosition := by
  rw [cppReachableDoubleThreatRoot_matches_history]
  exact cppReachableDoubleThreat_reachable

theorem cppReachableDoubleThreatCertificate_reachable_sound :
    CanForceWin Generated.cppReachableDoubleThreatRootPosition .black := by
  exact Generated.cppReachableDoubleThreatCertificate_sound

def cppReachableDoubleThreatLegalReplyCount : Nat :=
  ((Finset.univ : Finset Coord).filter
    (fun c => decide (legalMove Generated.cppReachableDoubleThreatRootPosition c))).card

def cppReachableDoubleThreatCertificateReplyCount : Nat :=
  match Generated.cppReachableDoubleThreatCertificate.nodes[0]? with
  | some (CertificateNode.opponentMoves _ children) => children.size
  | _ => 0

set_option linter.style.nativeDecide false in
example : cppReachableDoubleThreatLegalReplyCount = 208 := by
  native_decide

set_option linter.style.nativeDecide false in
example : cppReachableDoubleThreatCertificateReplyCount = 208 := by
  native_decide

/- The generated certificate's root must cover every legal reply.  Removing
   even one reply is rejected by the same trusted checker. -/
def cppReachableDoubleThreatMissingReply : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves Generated.cppReachableDoubleThreatRootPosition
        #[((7, 8), 1)],
      .proverMove Generated.cppReachableDoubleThreatPosition1 (10, 8) 2,
      .terminal Generated.cppReachableDoubleThreatPosition2 .blackWin
    ] }

set_option linter.style.nativeDecide false in
example :
    checkLocalCertificateAt Generated.cppReachableDoubleThreatRootPosition
      cppReachableDoubleThreatMissingReply = false := by
  native_decide

end Gomoku
