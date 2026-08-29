import Gomoku.Tactics

namespace Gomoku

/-!
Executable audit for the frozen v1 pattern table.

The v1 straight patterns are intentionally narrow:

* a straight open three is exactly three consecutive stones with two empty,
  in-board endpoints;
* a straight open four is exactly four consecutive stones with two empty,
  in-board endpoints;
* the two broken-three shapes and the three jump-four shapes are separate
  named predicates and never count as straight patterns automatically.

These tests exercise every direction and the main near-miss cases. They are
regressions for the definitions, not assumptions used by tactical soundness.
-/

private def patternBoard (p : Player) (stones : List Coord) : Board :=
  stones.foldl (fun b c => b.place c p) Board.empty

def patternHorizontalThree : Board :=
  patternBoard .black [(6, 7), (7, 7), (8, 7)]

def patternVerticalThree : Board :=
  patternBoard .black [(7, 6), (7, 7), (7, 8)]

def patternDiagonalUpThree : Board :=
  patternBoard .black [(6, 6), (7, 7), (8, 8)]

def patternDiagonalDownThree : Board :=
  patternBoard .black [(6, 8), (7, 7), (8, 6)]

example : straightOpenThree patternHorizontalThree .black (6, 7) .horizontal := by
  native_decide

example : straightOpenThree patternVerticalThree .black (7, 6) .vertical := by
  native_decide

example : straightOpenThree patternDiagonalUpThree .black (6, 6) .diagonalUp := by
  native_decide

example : straightOpenThree patternDiagonalDownThree .black (6, 8) .diagonalDown := by
  native_decide

def patternHorizontalFour : Board :=
  patternBoard .black [(6, 7), (7, 7), (8, 7), (9, 7)]

def patternWhiteHorizontalFour : Board :=
  patternBoard .white [(6, 7), (7, 7), (8, 7), (9, 7)]

def patternVerticalFour : Board :=
  patternBoard .black [(7, 6), (7, 7), (7, 8), (7, 9)]

def patternDiagonalUpFour : Board :=
  patternBoard .black [(6, 6), (7, 7), (8, 8), (9, 9)]

def patternDiagonalDownFour : Board :=
  patternBoard .black [(6, 9), (7, 8), (8, 7), (9, 6)]

example : straightOpenFour patternHorizontalFour .black (6, 7) .horizontal := by
  native_decide

example : SingleOpenFour ⟨patternWhiteHorizontalFour, .white⟩ .white := by
  native_decide

example : CanForceWin ⟨patternWhiteHorizontalFour, .white⟩ .white := by
  exact singleOpenFour_forces_win_any_player (by rfl)
    (Position.not_isTerminal_of_terminal_none (by native_decide)) (by
    native_decide)

example : straightOpenFour patternVerticalFour .black (7, 6) .vertical := by
  native_decide

example : straightOpenFour patternDiagonalUpFour .black (6, 6) .diagonalUp := by
  native_decide

example : straightOpenFour patternDiagonalDownFour .black (6, 9) .diagonalDown := by
  native_decide

/- The witness set contains one canonical description of a single straight
   run; shifting the start into the same run does not add a duplicate. -/
example : (openThreeWitnesses patternHorizontalThree .black).card = 1 := by
  native_decide

example : (openFourWitnesses patternHorizontalFour .black).card = 1 := by
  native_decide

/- The board boundary is a closed endpoint. -/
def patternBoundaryThree : Board :=
  patternBoard .black [(0, 7), (1, 7), (2, 7)]

def patternBoundaryFour : Board :=
  patternBoard .black [(0, 7), (1, 7), (2, 7), (3, 7)]

example : ¬ straightOpenThree patternBoundaryThree .black (0, 7) .horizontal := by
  native_decide

example : ¬ straightOpenFour patternBoundaryFour .black (0, 7) .horizontal := by
  native_decide

/- An opponent stone closes an endpoint. -/
def patternOpponentBlockedThree : Board :=
  (patternBoard .black [(5, 7), (6, 7), (7, 7)]).place (4, 7) .white

example : ¬ straightOpenThree patternOpponentBlockedThree .black (5, 7) .horizontal := by
  native_decide

/- A same-colour stone immediately before the proposed start means the
   segment is really part of a four, not a maximal open three. -/
def patternOwnExtendedThree : Board :=
  patternBoard .black [(4, 7), (5, 7), (6, 7), (7, 7)]

example : ¬ straightOpenThree patternOwnExtendedThree .black (5, 7) .horizontal := by
  native_decide

example : straightOpenFour patternOwnExtendedThree .black (4, 7) .horizontal := by
  native_decide

/- A four with only one available endpoint is a winning threat, but it is not
   the v1 open-four pattern and has only one geometric winning cell. -/
def patternHalfOpenFour : Board :=
  (patternBoard .black [(5, 7), (6, 7), (7, 7), (8, 7)]).place (4, 7) .white

example : ¬ straightOpenFour patternHalfOpenFour .black (5, 7) .horizontal := by
  native_decide

example : (WinningCells ⟨patternHalfOpenFour, .black⟩ .black).card = 1 := by
  native_decide

example : (WinningCells ⟨patternHorizontalFour, .black⟩ .black).card = 2 := by
  native_decide

/- The general theorem identifies the two endpoint cells independently of the
   executable card computation above. -/
example : ∃ left right,
    left ∈ WinningCells ⟨patternHorizontalFour, .black⟩ .black ∧
    right ∈ WinningCells ⟨patternHorizontalFour, .black⟩ .black ∧
    left ≠ right := by
  exact straightOpenFour_has_two_distinct_winningCells
    (b := patternHorizontalFour) (p := .black)
    (c := (6, 7)) (d := .horizontal) (by native_decide)

example : 2 ≤ (WinningCells ⟨patternHorizontalFour, .black⟩ .black).card := by
  refine (card_ge_two_iff_exists_distinct (WinningCells ⟨patternHorizontalFour, .black⟩ .black)).2 ?_
  rcases straightOpenFour_has_two_distinct_winningCells
      (b := patternHorizontalFour) (p := .black)
      (c := (6, 7)) (d := .horizontal) (by native_decide) with
    ⟨left, right, hleft, hright, hne⟩
  exact ⟨left, hleft, right, hright, hne⟩

example : HasDoubleThreat ⟨patternHorizontalFour, .black⟩ .black := by
  exact straightOpenFour_hasDoubleThreat
    (b := patternHorizontalFour) (p := .black)
    (c := (6, 7)) (d := .horizontal) (by native_decide)

/- Both frozen broken-three variants are recognized separately and are not
   silently included in `straightOpenThree`. -/
def patternBrokenThreeLeft : Board :=
  patternBoard .black [(5, 7), (6, 7), (8, 7)]

def patternBrokenThreeRight : Board :=
  patternBoard .black [(5, 7), (7, 7), (8, 7)]

example : brokenOpenThree patternBrokenThreeLeft .black (5, 7) .horizontal := by
  native_decide

example : brokenOpenThree patternBrokenThreeRight .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenThree patternBrokenThreeLeft .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenThree patternBrokenThreeRight .black (5, 7) .horizontal := by
  native_decide

/- The three frozen jump-four gaps are likewise exhaustive for v1. -/
def patternJumpFourGapThree : Board :=
  patternBoard .black [(5, 7), (6, 7), (7, 7), (9, 7)]

def patternJumpFourGapTwo : Board :=
  patternBoard .black [(5, 7), (6, 7), (8, 7), (9, 7)]

def patternJumpFourGapOne : Board :=
  patternBoard .black [(5, 7), (7, 7), (8, 7), (9, 7)]

example : jumpFour patternJumpFourGapThree .black (5, 7) .horizontal := by
  native_decide

example : jumpFour patternJumpFourGapTwo .black (5, 7) .horizontal := by
  native_decide

example : jumpFour patternJumpFourGapOne .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenFour patternJumpFourGapThree .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenFour patternJumpFourGapTwo .black (5, 7) .horizontal := by
  native_decide

example : ¬ straightOpenFour patternJumpFourGapOne .black (5, 7) .horizontal := by
  native_decide

/- An open three is not an immediate five. Its two endpoints are four-making
   extensions, whereas an open four has two immediate winning cells. -/
example : (WinningCells ⟨patternHorizontalThree, .black⟩ .black).card = 0 := by
  native_decide

example : (FourExtensionCells patternHorizontalThree .black).card = 2 := by
  native_decide

/- A finite positive example for the non-circular staged safety predicate.
   The periodic background has no five-in-a-row; only the centre and the
   eight relevant arm cells are empty.  Lean therefore checks every legal
   White defense and finds a Black extension which creates two winning cells. -/
def patternStagedCrossBoard : Board :=
  ⟨fun c =>
    if c = (7, 7) ∨
        c = (4, 7) ∨ c = (5, 7) ∨ c = (9, 7) ∨ c = (10, 7) ∨
        c = (7, 4) ∨ c = (7, 5) ∨ c = (7, 9) ∨ c = (7, 10) then
      .empty
    else if c = (6, 7) ∨ c = (8, 7) ∨ c = (7, 6) ∨ c = (7, 8) then
      .stone .black
    else if (c.1.1 + 2 * c.2.1) % 5 < 2 then
      .stone .black
    else
      .stone .white⟩

def patternStagedCrossPosition : Position :=
  ⟨patternStagedCrossBoard, .black⟩

def patternStagedCrossMove : Coord := (7, 7)

example : StagedSafeDoubleOpenThree
    patternStagedCrossPosition .black patternStagedCrossMove := by
  native_decide

example : CanForceWin patternStagedCrossPosition .black := by
  exact stagedSafeDoubleOpenThree_forces_win (m := patternStagedCrossMove)
    (by native_decide)

end Gomoku
