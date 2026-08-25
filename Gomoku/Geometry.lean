import Gomoku.Basic

namespace Gomoku

inductive Direction where
  | horizontal
  | vertical
  | diagonalUp
  | diagonalDown
  deriving DecidableEq, Repr

namespace Direction

def dx : Direction → Int
  | .horizontal => 1
  | .vertical => 0
  | .diagonalUp => 1
  | .diagonalDown => 1

def dy : Direction → Int
  | .horizontal => 0
  | .vertical => 1
  | .diagonalUp => 1
  | .diagonalDown => -1

end Direction

def directions : Finset Direction :=
  {.horizontal, .vertical, .diagonalUp, .diagonalDown}

instance : Fintype Direction :=
  ⟨directions, by
    intro d
    cases d <;> simp [directions]⟩

private def toFin15 (x : Int) (h : 0 ≤ x ∧ x < 15) : Fin 15 :=
  ⟨x.toNat, by omega⟩

def step (c : Coord) (d : Direction) (n : Int) : Option Coord :=
  let x := (c.1 : Int) + n * Direction.dx d
  let y := (c.2 : Int) + n * Direction.dy d
  if h : 0 ≤ x ∧ x < 15 ∧ 0 ≤ y ∧ y < 15 then
    some (toFin15 x ⟨h.1, h.2.1⟩, toFin15 y ⟨h.2.2.1, h.2.2.2⟩)
  else
    none

def lineCells (c : Coord) (d : Direction) (length : Nat) : List Coord :=
  (List.range length).filterMap (fun n => step c d n)

def occupiedAt (b : Board) (p : Player) (c : Coord) (d : Direction) (n : Int) : Prop :=
  ∃ q, step c d n = some q ∧ b.cell q = .stone p

instance occupiedAtDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) (n : Int) :
    Decidable (occupiedAt b p c d n) := by
  unfold occupiedAt
  infer_instance

def consecutive (b : Board) (p : Player) (c : Coord) (d : Direction) (length : Nat) : Prop :=
  ∀ n : Fin length, occupiedAt b p c d n.1

instance consecutiveDecidable (b : Board) (p : Player) (c : Coord) (d : Direction)
    (length : Nat) : Decidable (consecutive b p c d length) := by
  unfold consecutive
  infer_instance

def hasRun (b : Board) (p : Player) (length : Nat) : Prop :=
  ∃ c d, consecutive b p c d length

instance hasRunDecidable (b : Board) (p : Player) (length : Nat) :
    Decidable (hasRun b p length) := by
  exact Fintype.decidableExistsFintype

def hasAtLeastFive (b : Board) (p : Player) : Prop := hasRun b p 5

instance hasAtLeastFiveDecidable (b : Board) (p : Player) :
    Decidable (hasAtLeastFive b p) := by
  exact hasRunDecidable b p 5

def openEnd (b : Board) (c : Coord) (d : Direction) (n : Int) : Prop :=
  ∃ q, step c d n = some q ∧ b.cell q = .empty

instance openEndDecidable (b : Board) (c : Coord) (d : Direction) (n : Int) :
    Decidable (openEnd b c d n) := by
  unfold openEnd
  infer_instance

def straightOpenThree (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  consecutive b p c d 3 ∧ openEnd b c d (-1) ∧ openEnd b c d 3

instance straightOpenThreeDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (straightOpenThree b p c d) := by
  unfold straightOpenThree
  infer_instance

def straightOpenFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  consecutive b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 4

instance straightOpenFourDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (straightOpenFour b p c d) := by
  unfold straightOpenFour
  infer_instance

def StraightOpenThree (b : Board) (p : Player) : Prop :=
  ∃ c d, straightOpenThree b p c d

def StraightOpenFour (b : Board) (p : Player) : Prop :=
  ∃ c d, straightOpenFour b p c d

@[simp] theorem directions_horizontal : Direction.dx .horizontal = 1 := rfl

end Gomoku
