import Gomoku.RuleAudit
import Gomoku.Examples

namespace Gomoku

/-!
This module contains deliberately wrong alternative definitions.  They are not
part of the game model; each one is paired with a concrete counterexample so a
future refactor cannot silently reintroduce the same mistake.
-/

/- A mistaken implementation of unrestricted Gomoku may require exactly five
   stones and therefore reject an overline. -/
def wrongExactlyFive (b : Board) (p : Player) : Prop :=
  hasAtLeastFive b p ∧ ¬ hasRun b p 6

instance wrongExactlyFiveDecidable (b : Board) (p : Player) :
    Decidable (wrongExactlyFive b p) := by
  unfold wrongExactlyFive
  infer_instance

example : hasAtLeastFive auditSixInRow .black := by
  native_decide

example : ¬ wrongExactlyFive auditSixInRow .black := by
  native_decide

/- Checking only horizontal lines misses vertical wins. -/
def wrongHorizontalFive (b : Board) (p : Player) : Prop :=
  ∃ c, consecutive b p c .horizontal 5

instance wrongHorizontalFiveDecidable (b : Board) (p : Player) :
    Decidable (wrongHorizontalFive b p) := by
  unfold wrongHorizontalFive
  infer_instance

example : hasAtLeastFive auditVerticalFive .black := by
  native_decide

example : ¬ wrongHorizontalFive auditVerticalFive .black := by
  native_decide

/- Treating an out-of-board endpoint as an empty cell incorrectly turns a
   boundary four into an open four. -/
def wrongOpenEnd (b : Board) (c : Coord) (d : Direction) (n : Int) : Prop :=
  match step c d n with
  | some q => b.cell q = .empty
  | none => True

instance wrongOpenEndDecidable (b : Board) (c : Coord) (d : Direction) (n : Int) :
    Decidable (wrongOpenEnd b c d n) := by
  unfold wrongOpenEnd
  split <;> infer_instance

def wrongStraightOpenFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  consecutive b p c d 4 ∧ wrongOpenEnd b c d (-1) ∧ wrongOpenEnd b c d 4

instance wrongStraightOpenFourDecidable (b : Board) (p : Player)
    (c : Coord) (d : Direction) : Decidable (wrongStraightOpenFour b p c d) := by
  unfold wrongStraightOpenFour
  infer_instance

example : ¬ straightOpenFour boundaryFourBoard .black (0, 7) .horizontal := by
  native_decide

example : wrongStraightOpenFour boundaryFourBoard .black (0, 7) .horizontal := by
  native_decide

/- Ignoring the terminal condition allows a move after a win. -/
def wrongLegalMoveIgnoringTerminal (s : Position) (c : Coord) : Prop :=
  s.board.cell c = .empty

instance wrongLegalMoveIgnoringTerminalDecidable (s : Position) (c : Coord) :
    Decidable (wrongLegalMoveIgnoringTerminal s c) := by
  unfold wrongLegalMoveIgnoringTerminal
  infer_instance

def mutationPostWinCell : Coord := (14, 14)

example : terminal auditReachableWinPosition = some .blackWin := by
  exact auditReachableWin_terminal

example : wrongLegalMoveIgnoringTerminal auditReachableWinPosition mutationPostWinCell := by
  native_decide

example : ¬ legalMove auditReachableWinPosition mutationPostWinCell := by
  exact Position.terminal_outcome_no_legal auditReachableWin_terminal mutationPostWinCell

end Gomoku
