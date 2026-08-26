import Mathlib

namespace Gomoku

inductive Player where
  | black
  | white
  deriving DecidableEq, Repr

namespace Player

def other : Player → Player
  | .black => .white
  | .white => .black

@[simp] theorem other_black : other .black = .white := rfl
@[simp] theorem other_white : other .white = .black := rfl

@[simp] theorem other_other (p : Player) : other (other p) = p := by
  cases p <;> rfl

@[simp] theorem other_ne_self (p : Player) : other p ≠ p := by
  cases p <;> simp

@[simp] theorem self_ne_other (p : Player) : p ≠ other p := by
  cases p <;> simp

end Player

inductive Cell where
  | empty
  | stone (player : Player)
  deriving DecidableEq, Repr

namespace Cell

def owner : Cell → Option Player
  | .empty => none
  | .stone p => some p

@[simp] theorem owner_empty : owner .empty = none := rfl
@[simp] theorem owner_stone (p : Player) : owner (.stone p) = some p := rfl

end Cell

abbrev Coord := Fin 15 × Fin 15

structure Board where
  cell : Coord → Cell

namespace Board

def empty : Board := ⟨fun _ => .empty⟩

instance : Inhabited Board := ⟨empty⟩

def place (b : Board) (c : Coord) (p : Player) : Board :=
  ⟨fun d => if d = c then .stone p else b.cell d⟩

@[simp] theorem empty_cell (c : Coord) : empty.cell c = .empty := rfl

theorem place_same (b : Board) (c : Coord) (p : Player) :
    (place b c p).cell c = .stone p := by
  simp [place]

theorem place_other (b : Board) {c d : Coord} (h : d ≠ c) (p : Player) :
    (place b c p).cell d = b.cell d := by
  simp [place, h]

theorem place_commute_of_ne (b : Board) {c d : Coord} {p q : Player}
    (h : c ≠ d) :
    (place (place b c p) d q) = place (place b d q) c p := by
  cases b with
  | mk f =>
    apply congrArg (fun g : Coord → Cell => Board.mk g)
    funext x
    by_cases hxc : x = c
    · subst x
      simp [place, h]
    · by_cases hxd : x = d
      · subst x
        have hdc : d ≠ c := hxc
        simp [place, h, hdc]
      · simp [place, hxc, hxd]

def count (b : Board) (p : Player) : Nat :=
  ((Finset.univ : Finset Coord).filter (fun c => b.cell c = .stone p)).card

def emptyCount (b : Board) : Nat :=
  ((Finset.univ : Finset Coord).filter (fun c => b.cell c = .empty)).card

def full (b : Board) : Prop := ∀ c, b.cell c ≠ .empty

private theorem filter_place_eq_insert (b : Board) (c : Coord) (p : Player)
    (P : Cell → Prop) [DecidablePred P]
    (hnew : P (.stone p)) (hold : ¬ P (b.cell c)) :
    (Finset.univ : Finset Coord).filter (fun d => P ((place b c p).cell d)) =
      insert c (((Finset.univ : Finset Coord).erase c).filter (fun d => P (b.cell d))) := by
  ext d
  by_cases hd : d = c
  · subst d
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
    simpa [place] using hnew
  · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_univ, true_and, and_true]
    simp [place, hd]

private theorem filter_erase_of_not (P : Coord → Prop) [DecidablePred P]
    (c : Coord) (h : ¬ P c) :
    (Finset.univ : Finset Coord).filter P =
      ((Finset.univ : Finset Coord).erase c).filter P := by
  rw [← Finset.insert_erase (by simp : c ∈ (Finset.univ : Finset Coord))]
  rw [Finset.filter_insert]
  simp [h]

theorem count_place_same_of_empty (b : Board) (c : Coord) (p : Player)
    (h : b.cell c = .empty) :
    (place b c p).count p = b.count p + 1 := by
  classical
  let P : Coord → Prop := fun d => b.cell d = .stone p
  have hnew : (fun x : Cell => x = .stone p) (.stone p) := rfl
  have hold : ¬ (fun x : Cell => x = .stone p) (b.cell c) := by simp [h]
  have heq := filter_place_eq_insert b c p (fun x : Cell => x = .stone p) hnew hold
  have herase := filter_erase_of_not P c (by simp [P, h])
  unfold count
  change (Finset.univ.filter (fun d => (place b c p).cell d = .stone p)).card = _
  rw [heq]
  rw [← herase]
  simp [P, h, Nat.add_comm]

theorem count_place_other_of_empty (b : Board) (c : Coord) (p q : Player)
    (h : b.cell c = .empty) (hq : q ≠ p) :
    (place b c p).count q = b.count q := by
  classical
  let P : Coord → Prop := fun d => b.cell d = .stone q
  have hpq : p ≠ q := by intro hpq; exact hq hpq.symm
  have hnew : ¬ ((fun x : Cell => x = .stone q) (.stone p)) := by simp [hpq]
  have hold : ¬ (fun x : Cell => x = .stone q) (b.cell c) := by simp [h]
  have heq :
      (Finset.univ : Finset Coord).filter (fun d => (place b c p).cell d = .stone q) =
        ((Finset.univ : Finset Coord).erase c).filter P := by
    rw [← Finset.insert_erase (by simp : c ∈ (Finset.univ : Finset Coord))]
    rw [Finset.filter_insert]
    have hcnew : ¬ ((fun d => (place b c p).cell d = .stone q) c) := by
      simpa [place] using hnew
    rw [if_neg hcnew]
    rw [Finset.erase_insert (by simp : c ∉ (Finset.univ : Finset Coord).erase c)]
    apply Finset.filter_congr
    intro d hd
    have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
    simp [place, hdc, P]
  unfold count
  rw [heq]
  exact (congrArg Finset.card (filter_erase_of_not P c (by simp [P, h]))).symm

theorem emptyCount_place_of_empty (b : Board) (c : Coord) (p : Player)
    (h : b.cell c = .empty) :
    (place b c p).emptyCount + 1 = b.emptyCount := by
  classical
  let P : Coord → Prop := fun d => b.cell d = .empty
  have heq :
      (Finset.univ : Finset Coord).filter (fun d => (place b c p).cell d = .empty) =
        ((Finset.univ : Finset Coord).erase c).filter P := by
    rw [← Finset.insert_erase (by simp : c ∈ (Finset.univ : Finset Coord))]
    rw [Finset.filter_insert]
    have hcnew : ¬ ((fun d => (place b c p).cell d = .empty) c) := by
      simpa [place] using h
    rw [if_neg hcnew]
    rw [Finset.erase_insert (by simp : c ∉ (Finset.univ : Finset Coord).erase c)]
    apply Finset.filter_congr
    intro d hd
    have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
    simp [place, hdc, P]
  unfold emptyCount
  rw [heq]
  rw [Finset.filter_erase]
  exact Finset.card_erase_add_one (by simp [P, h])

instance fullDecidable (b : Board) : Decidable (full b) := by
  exact Fintype.decidableForallFintype

end Board

end Gomoku
