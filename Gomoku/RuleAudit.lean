import Gomoku.Search
import Gomoku.Generated.CppSmoke

namespace Gomoku

/-!
Minimal acceptance suite for the fixed 7×7 main program. It keeps only the
board-size, rule, terminal, and certificate-boundary checks needed by the
migration; older duplicate tactical and performance fixtures were removed.
-/

private def boardWithStones (p : Player) (stones : List Coord) : Board :=
  stones.foldl (fun b c => b.place c p) Board.empty

/- The coordinate universe and the empty opening have exactly 49 points. -/
example : Fintype.card Coord = 49 := by
  native_decide

example : allCoords.size = 49 := by
  native_decide

example : Board.emptyCount initialPosition.board = 49 := by
  native_decide

example : initialPosition.turn = .black := by
  rfl

example : terminal initialPosition = none := by
  native_decide

example :
    ((Finset.univ : Finset Coord).filter
      (fun c => decide (legalMove initialPosition c))).card = 49 := by
  native_decide

/- Five remains the winning length in every direction; an overline also wins. -/
def auditHorizontalFive : Board :=
  boardWithStones .black [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]

def auditVerticalFive : Board :=
  boardWithStones .black [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def auditDiagonalUpFive : Board :=
  boardWithStones .black [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]

def auditDiagonalDownFive : Board :=
  boardWithStones .black [(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)]

def auditSixInRow : Board :=
  boardWithStones .black [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)]

def auditWhiteFive : Board :=
  boardWithStones .white [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

example : terminal ⟨auditHorizontalFive, .white⟩ = some .blackWin := by
  native_decide

example : hasAtLeastFive auditVerticalFive .black := by
  native_decide

example : hasAtLeastFive auditDiagonalUpFive .black := by
  native_decide

example : hasAtLeastFive auditDiagonalDownFive .black := by
  native_decide

example : hasAtLeastFive auditSixInRow .black := by
  native_decide

example : terminal ⟨auditWhiteFive, .black⟩ = some .whiteWin := by
  native_decide

/- A period-four full board has no five for either side and is a draw. -/
def auditDrawBoard : Board :=
  ⟨fun c => if (c.1.1 + 2 * c.2.1) % 4 < 2
    then .stone .black else .stone .white⟩

def auditDrawPosition : Position := ⟨auditDrawBoard, .white⟩

example : Board.full auditDrawBoard := by
  native_decide

example : terminal auditDrawPosition = some .draw := by
  native_decide

/- Small accepted local certificate. -/
def auditImmediateWinBoard : Board :=
  boardWithStones .black [(1, 3), (2, 3), (3, 3), (4, 3)]

def auditImmediateWinPosition : Position :=
  ⟨auditImmediateWinBoard, .black⟩

def auditImmediateWinningMove : Coord := (0, 3)

def auditImmediateWinCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove auditImmediateWinPosition auditImmediateWinningMove 1,
      .terminal (play auditImmediateWinPosition auditImmediateWinningMove) .blackWin
    ] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditImmediateWinCertificate = true := by
  native_decide

theorem auditImmediateWinCertificate_sound :
    CanForceWin auditImmediateWinPosition .black := by
  exact local_certificate_at_sound auditImmediateWinPosition
    auditImmediateWinCertificate (by native_decide)

/- The global checker still binds the root to the empty 7×7 Black opening. -/
example : checkCertificate auditImmediateWinCertificate = false := by
  native_decide

/- Malformed child position, terminal label, id, illegal move, and cycle are
   all rejected by the unchanged checker invariants. -/
def auditWrongChildCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove auditImmediateWinPosition auditImmediateWinningMove 1,
      .terminal auditImmediateWinPosition .blackWin
    ] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditWrongChildCertificate = false := by
  native_decide

def auditWrongTerminalCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove auditImmediateWinPosition auditImmediateWinningMove 1,
      .terminal (play auditImmediateWinPosition auditImmediateWinningMove) .whiteWin
    ] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditWrongTerminalCertificate = false := by
  native_decide

def auditBadChildIdCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.proverMove auditImmediateWinPosition auditImmediateWinningMove 99] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditBadChildIdCertificate = false := by
  native_decide

def auditCycleCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[.proverMove auditImmediateWinPosition auditImmediateWinningMove 0] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditCycleCertificate = false := by
  native_decide

def auditIllegalMoveCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .proverMove auditImmediateWinPosition (1, 3) 1,
      .terminal (play auditImmediateWinPosition (1, 3)) .blackWin
    ] }

example : checkLocalCertificateAt auditImmediateWinPosition
    auditIllegalMoveCertificate = false := by
  native_decide

/- A two-empty opponent node must contain both legal replies. -/
def auditForkBoard : Board :=
  ⟨fun c =>
    if c = (0, 3) ∨ c = (5, 3) then .empty
    else if c = (1, 3) ∨ c = (2, 3) ∨ c = (3, 3) ∨ c = (4, 3) then
      .stone .black
    else if (c.1.1 + 2 * c.2.1) % 4 < 2 then .stone .black
    else .stone .white⟩

def auditForkPosition : Position := ⟨auditForkBoard, .white⟩

def auditMissingReplyCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves auditForkPosition #[((0, 3), 1)],
      .proverMove (play auditForkPosition (0, 3)) (5, 3) 2,
      .terminal (play (play auditForkPosition (0, 3)) (5, 3)) .blackWin
    ] }

example : checkLocalCertificateAt auditForkPosition
    auditMissingReplyCertificate = false := by
  native_decide

/- The retained C++ smoke artifact is generated from the fixed 7×7 solver
   and is independently accepted by Lean. -/
example : checkLocalCertificateAt Generated.cppSmokeRootPosition
    Generated.cppSmokeCertificate = true := by
  exact Generated.cppSmokeCertificate_checked

end Gomoku
