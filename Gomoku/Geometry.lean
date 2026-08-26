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

theorem step_reverse {c q : Coord} {d : Direction} {n : Int}
    (h : step c d n = some q) : step q d (-n) = some c := by
  rcases c with ⟨⟨cx, hcx⟩, ⟨cy, hcy⟩⟩
  rcases q with ⟨⟨qx, hqx⟩, ⟨qy, hqy⟩⟩
  cases d <;>
    simp [step, Direction.dx, Direction.dy, toFin15] at h ⊢ <;>
    omega

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

/- Placing the other player's stone cannot create a run for `p`.  No
   emptiness assumption is needed: even an overwrite at `r` cannot turn that
   cell into a stone owned by `p`. -/
theorem hasAtLeastFive_of_place_other
    {b : Board} {p q : Player} {r : Coord}
    (hq : q ≠ p) (h : hasAtLeastFive (b.place r q) p) :
    hasAtLeastFive b p := by
  rcases h with ⟨start, d, hcon⟩
  refine ⟨start, d, ?_⟩
  intro n
  rcases hcon n with ⟨x, hxstep, hxcell⟩
  have hxr : x ≠ r := by
    intro hxr
    subst x
    simp [Board.place, hq] at hxcell
  refine ⟨x, hxstep, ?_⟩
  simpa [Board.place, hxr] using hxcell

def openEnd (b : Board) (c : Coord) (d : Direction) (n : Int) : Prop :=
  ∃ q, step c d n = some q ∧ b.cell q = .empty

instance openEndDecidable (b : Board) (c : Coord) (d : Direction) (n : Int) :
    Decidable (openEnd b c d n) := by
  unfold openEnd
  infer_instance

/- These predicates are deliberately separate from the straight patterns
   above.  Each disjunct is one frozen finite pattern; adding another
   Gomoku convention later must add another named disjunct or predicate. -/
def brokenOpenThree (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  (occupiedAt b p c d 0 ∧ occupiedAt b p c d 1 ∧ occupiedAt b p c d 3 ∧
      openEnd b c d (-1) ∧ openEnd b c d 2 ∧ openEnd b c d 4) ∨
    (occupiedAt b p c d 0 ∧ occupiedAt b p c d 2 ∧ occupiedAt b p c d 3 ∧
      openEnd b c d (-1) ∧ openEnd b c d 1 ∧ openEnd b c d 4)

instance brokenOpenThreeDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (brokenOpenThree b p c d) := by
  unfold brokenOpenThree
  infer_instance

def jumpFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  (occupiedAt b p c d 0 ∧ occupiedAt b p c d 1 ∧ occupiedAt b p c d 2 ∧
      occupiedAt b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 3 ∧
      openEnd b c d 5) ∨
    (occupiedAt b p c d 0 ∧ occupiedAt b p c d 1 ∧ occupiedAt b p c d 3 ∧
      occupiedAt b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 2 ∧
      openEnd b c d 5) ∨
    (occupiedAt b p c d 0 ∧ occupiedAt b p c d 2 ∧ occupiedAt b p c d 3 ∧
      occupiedAt b p c d 4 ∧ openEnd b c d (-1) ∧ openEnd b c d 1 ∧
      openEnd b c d 5)

instance jumpFourDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (jumpFour b p c d) := by
  unfold jumpFour
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

def canonicalRunStart (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  ¬ occupiedAt b p c d (-1)

def normalizedStraightOpenThree (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  straightOpenThree b p c d ∧ canonicalRunStart b p c d

def normalizedStraightOpenFour (b : Board) (p : Player) (c : Coord) (d : Direction) : Prop :=
  straightOpenFour b p c d ∧ canonicalRunStart b p c d

instance canonicalRunStartDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (canonicalRunStart b p c d) := by
  unfold canonicalRunStart
  infer_instance

instance normalizedStraightOpenThreeDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (normalizedStraightOpenThree b p c d) := by
  unfold normalizedStraightOpenThree
  infer_instance

instance normalizedStraightOpenFourDecidable (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Decidable (normalizedStraightOpenFour b p c d) := by
  unfold normalizedStraightOpenFour
  infer_instance

theorem straightOpenThree_canonical {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenThree b p c d) : canonicalRunStart b p c d := by
  intro hstone
  rcases h.2.1 with ⟨q, hq, hempty⟩
  rcases hstone with ⟨q', hq', hstone⟩
  have hqq : q = q' := by
    exact Option.some.inj (hq.symm.trans hq')
  subst q'
  rw [hempty] at hstone
  cases hstone

theorem straightOpenFour_canonical {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenFour b p c d) : canonicalRunStart b p c d := by
  intro hstone
  rcases h.2.1 with ⟨q, hq, hempty⟩
  rcases hstone with ⟨q', hq', hstone⟩
  have hqq : q = q' := by
    exact Option.some.inj (hq.symm.trans hq')
  subst q'
  rw [hempty] at hstone
  cases hstone

theorem normalizedStraightOpenThree_iff {b : Board} {p : Player} {c : Coord} {d : Direction} :
    normalizedStraightOpenThree b p c d ↔ straightOpenThree b p c d := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, straightOpenThree_canonical h⟩

theorem normalizedStraightOpenFour_iff {b : Board} {p : Player} {c : Coord} {d : Direction} :
    normalizedStraightOpenFour b p c d ↔ straightOpenFour b p c d := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, straightOpenFour_canonical h⟩

/- A maximal run is a finite consecutive segment that cannot be extended by
   another stone of the same player at either endpoint.  Boundary cells are
   handled by `occupiedAt`: an out-of-board step simply has no witness. -/
def MaximalRun (b : Board) (p : Player) (c : Coord) (d : Direction)
    (length : Nat) : Prop :=
  consecutive b p c d length ∧
    ¬ occupiedAt b p c d (-1) ∧
    ¬ occupiedAt b p c d (length : Int)

instance maximalRunDecidable (b : Board) (p : Player) (c : Coord) (d : Direction)
    (length : Nat) : Decidable (MaximalRun b p c d length) := by
  unfold MaximalRun
  infer_instance

theorem not_occupiedAt_of_openEnd {b : Board} {p : Player} {c : Coord} {d : Direction}
    {n : Int} (hopen : openEnd b c d n) : ¬ occupiedAt b p c d n := by
  intro hocc
  rcases hopen with ⟨q, hstep, hempty⟩
  rcases hocc with ⟨q', hstep', hstone⟩
  have hqq : q = q' := Option.some.inj (hstep.symm.trans hstep')
  subst q'
  rw [hempty] at hstone
  cases hstone

theorem straightOpenThree_maximalRun {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenThree b p c d) : MaximalRun b p c d 3 := by
  refine ⟨h.1, ?_, ?_⟩
  · exact not_occupiedAt_of_openEnd h.2.1
  · exact not_occupiedAt_of_openEnd h.2.2

theorem straightOpenFour_maximalRun {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenFour b p c d) : MaximalRun b p c d 4 := by
  refine ⟨h.1, ?_, ?_⟩
  · exact not_occupiedAt_of_openEnd h.2.1
  · exact not_occupiedAt_of_openEnd h.2.2

/- `StartShiftConflict` is the precise overlap condition needed for a
   uniqueness statement.  It says that `c'` is a positive-offset cell of the
   run starting at `c`, and that the cell immediately before `c'` is the
   previous cell of that same run.  Separate runs in the same direction do
   not satisfy this relation, so no false global uniqueness claim is made. -/
def StartShiftConflict (length : Nat) (c c' : Coord) (d : Direction) : Prop :=
  ∃ i : Fin length, 0 < i.1 ∧ ∃ q,
    step c d (i.1 : Int) = some c' ∧
      step c d ((i.1 : Int) - 1) = some q ∧
        step c' d (-1) = some q

instance startShiftConflictDecidable (length : Nat) (c c' : Coord) (d : Direction) :
    Decidable (StartShiftConflict length c c' d) := by
  unfold StartShiftConflict
  infer_instance

theorem consecutive_not_startShiftConflict
    {b : Board} {p : Player} {length : Nat}
    {c c' : Coord} {d : Direction}
    (hcon : consecutive b p c d length)
    (hleft : openEnd b c' d (-1))
    (hconf : StartShiftConflict length c c' d) : False := by
  rcases hconf with ⟨i, hi, q, hstart, hprev, hback⟩
  have hprevBound : i.1 - 1 < length := by omega
  rcases hcon ⟨i.1 - 1, hprevBound⟩ with ⟨q', hq', hstone⟩
  have hq'coord : step c d ((i.1 : Int) - 1) = some q' := by
    have hiNat : 1 ≤ i.1 := by omega
    have hcast : ((i.1 - 1 : Nat) : Int) = (i.1 : Int) - 1 := by
      rw [Nat.cast_sub hiNat]
      norm_num
    simpa [hcast] using hq'
  have hqq : q' = q := by
    exact Option.some.inj (hq'coord.symm.trans hprev)
  subst q'
  rcases hleft with ⟨q'', hleftStep, hempty⟩
  have hqq' : q'' = q := by
    exact Option.some.inj (hleftStep.symm.trans hback)
  subst q''
  rw [hempty] at hstone
  cases hstone

theorem consecutive_not_startShiftConflict_of_not_occupied
    {b : Board} {p : Player} {length : Nat}
    {c c' : Coord} {d : Direction}
    (hcon : consecutive b p c d length)
    (hleft : ¬ occupiedAt b p c' d (-1))
    (hconf : StartShiftConflict length c c' d) : False := by
  rcases hconf with ⟨i, hi, q, hstart, hprev, hback⟩
  have hprevBound : i.1 - 1 < length := by omega
  rcases hcon ⟨i.1 - 1, hprevBound⟩ with ⟨q', hq', hstone⟩
  have hq'coord : step c d ((i.1 : Int) - 1) = some q' := by
    have hiNat : 1 ≤ i.1 := by omega
    have hcast : ((i.1 - 1 : Nat) : Int) = (i.1 : Int) - 1 := by
      rw [Nat.cast_sub hiNat]
      norm_num
    simpa [hcast] using hq'
  have hqq : q' = q := Option.some.inj (hq'coord.symm.trans hprev)
  subst q'
  exact hleft ⟨q, hback, hstone⟩

theorem straightOpenThree_not_startShiftConflict
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : straightOpenThree b p c d)
    (h' : straightOpenThree b p c' d)
    (hconf : StartShiftConflict 3 c c' d) : False := by
  exact consecutive_not_startShiftConflict h.1 h'.2.1 hconf

theorem straightOpenFour_not_startShiftConflict
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : straightOpenFour b p c d)
    (h' : straightOpenFour b p c' d)
    (hconf : StartShiftConflict 4 c c' d) : False := by
  exact consecutive_not_startShiftConflict h.1 h'.2.1 hconf

def ComparableRunStarts (length : Nat) (c c' : Coord) (d : Direction) : Prop :=
  c = c' ∨ StartShiftConflict length c c' d ∨ StartShiftConflict length c' c d

theorem normalizedStraightOpenThree_unique_of_comparable
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : normalizedStraightOpenThree b p c d)
    (h' : normalizedStraightOpenThree b p c' d)
    (hcompare : ComparableRunStarts 3 c c' d) : c = c' := by
  rcases hcompare with hsame | hconf | hconf
  · exact hsame
  · exact False.elim (straightOpenThree_not_startShiftConflict h.1 h'.1 hconf)
  · exact False.elim (straightOpenThree_not_startShiftConflict h'.1 h.1 hconf)

theorem normalizedStraightOpenFour_unique_of_comparable
    {b : Board} {p : Player} {c c' : Coord} {d : Direction}
    (h : normalizedStraightOpenFour b p c d)
    (h' : normalizedStraightOpenFour b p c' d)
    (hcompare : ComparableRunStarts 4 c c' d) : c = c' := by
  rcases hcompare with hsame | hconf | hconf
  · exact hsame
  · exact False.elim (straightOpenFour_not_startShiftConflict h.1 h'.1 hconf)
  · exact False.elim (straightOpenFour_not_startShiftConflict h'.1 h.1 hconf)

theorem maximalRun_unique_of_comparable
    {b : Board} {p : Player} {length : Nat}
    {c c' : Coord} {d : Direction}
    (h : MaximalRun b p c d length)
    (h' : MaximalRun b p c' d length)
    (hcompare : ComparableRunStarts length c c' d) : c = c' := by
  rcases hcompare with hsame | hconf | hconf
  · exact hsame
  · exact False.elim
      (consecutive_not_startShiftConflict_of_not_occupied h.1 h'.2.1 hconf)
  · exact False.elim
      (consecutive_not_startShiftConflict_of_not_occupied h'.1 h.2.1 hconf)

def StraightOpenThree (b : Board) (p : Player) : Prop :=
  ∃ c d, straightOpenThree b p c d

def StraightOpenFour (b : Board) (p : Player) : Prop :=
  ∃ c d, straightOpenFour b p c d

@[simp] theorem directions_horizontal : Direction.dx .horizontal = 1 := rfl

end Gomoku
