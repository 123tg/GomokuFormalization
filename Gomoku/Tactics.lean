import Gomoku.Game

namespace Gomoku

abbrev PatternWitness := Coord × Direction

def openThreeWitnesses (b : Board) (p : Player) : Finset PatternWitness :=
  ((Finset.univ : Finset Coord).product directions).filter
    (fun w => normalizedStraightOpenThree b p w.1 w.2)

def openFourWitnesses (b : Board) (p : Player) : Finset PatternWitness :=
  ((Finset.univ : Finset Coord).product directions).filter
    (fun w => normalizedStraightOpenFour b p w.1 w.2)

theorem mem_openThreeWitnesses (b : Board) (p : Player) (c : Coord) (d : Direction) :
    (c, d) ∈ openThreeWitnesses b p ↔ straightOpenThree b p c d := by
  classical
  cases d <;> simp [openThreeWitnesses, directions, normalizedStraightOpenThree_iff]

theorem mem_openFourWitnesses (b : Board) (p : Player) (c : Coord) (d : Direction) :
    (c, d) ∈ openFourWitnesses b p ↔ straightOpenFour b p c d := by
  classical
  cases d <;> simp [openFourWitnesses, directions, normalizedStraightOpenFour_iff]

theorem card_ge_two_iff_exists_distinct {α : Type} [DecidableEq α] (s : Finset α) :
    2 ≤ s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  constructor
  · intro h
    apply Finset.one_lt_card.mp
    omega
  · intro h
    have h' : 1 < s.card := Finset.one_lt_card.mpr h
    omega

def WinningMoves (s : Position) (p : Player) : Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun c => s.turn = p ∧ legalMove s c ∧
      terminal (play s c) = some (winner p))

def HasImmediateWin (s : Position) (p : Player) : Prop :=
  (WinningMoves s p).Nonempty

instance hasImmediateWinDecidable (s : Position) (p : Player) :
    Decidable (HasImmediateWin s p) := by
  unfold HasImmediateWin
  infer_instance

def OpponentHasImmediateWin (s : Position) (p : Player) : Prop :=
  HasImmediateWin s (Player.other p)

instance opponentHasImmediateWinDecidable (s : Position) (p : Player) :
    Decidable (OpponentHasImmediateWin s p) := by
  unfold OpponentHasImmediateWin
  infer_instance

/- `WinningCells` is independent of whose turn it is.  This is needed for a
   double threat: after Black creates two winning points, it is White's turn,
   so `WinningMoves` (which intentionally includes a turn check) would be
   empty even though the two geometric winning cells remain present. -/
def WinningCells (s : Position) (p : Player) : Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun c => s.board.cell c = .empty ∧
      hasAtLeastFive (s.board.place c p) p)

def HasDoubleThreat (s : Position) (p : Player) : Prop :=
  2 ≤ (WinningCells s p).card

instance winningCellsDecidable (s : Position) (p : Player) :
    DecidablePred (fun c => c ∈ WinningCells s p) := by
  intro c
  simp only [WinningCells]
  infer_instance

instance hasDoubleThreatDecidable (s : Position) (p : Player) :
    Decidable (HasDoubleThreat s p) := by
  unfold HasDoubleThreat
  infer_instance

theorem mem_winningCells_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ WinningCells s p ↔
      s.board.cell c = .empty ∧ hasAtLeastFive (s.board.place c p) p := by
  simp [WinningCells]

/- A straight open three is a one-ply threat to create a four, not an
   immediate five.  Keeping this set separate from `WinningCells` prevents
   the geometric pattern from being silently promoted to an immediate win. -/
def FourExtensionCells (b : Board) (p : Player) : Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun m => b.cell m = .empty ∧ hasRun (b.place m p) p 4)

theorem mem_fourExtensionCells_iff (b : Board) (p : Player) (m : Coord) :
    m ∈ FourExtensionCells b p ↔
      b.cell m = .empty ∧ hasRun (b.place m p) p 4 := by
  simp [FourExtensionCells]

theorem straightOpenThree_has_fourExtension
    {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenThree b p c d) :
    ∃ m, m ∈ FourExtensionCells b p := by
  rcases h.2.2 with ⟨m, hmstep, hmempty⟩
  refine ⟨m, (mem_fourExtensionCells_iff b p m).2 ?_⟩
  refine ⟨hmempty, c, d, ?_⟩
  intro n
  fin_cases n
  · rcases h.1 ⟨0, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · rcases h.1 ⟨1, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · rcases h.1 ⟨2, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · refine ⟨m, ?_, ?_⟩
    · simpa using hmstep
    · exact Board.place_same _ _ _

def OpenFourExtensionCells (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun m => b.cell m = .empty ∧
      straightOpenFour (b.place m p) p c d)

theorem mem_openFourExtensionCells_iff
    (b : Board) (p : Player) (c : Coord) (d : Direction) (m : Coord) :
    m ∈ OpenFourExtensionCells b p c d ↔
      b.cell m = .empty ∧ straightOpenFour (b.place m p) p c d := by
  simp [OpenFourExtensionCells]

theorem straightOpenFour_has_winningCell
    {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : straightOpenFour b p c d) :
    ∃ m, m ∈ WinningCells ⟨b, p⟩ p := by
  rcases h.2.2 with ⟨m, hmstep, hmempty⟩
  refine ⟨m, (mem_winningCells_iff ⟨b, p⟩ p m).2 ⟨hmempty, ?_⟩⟩
  refine ⟨c, d, ?_⟩
  intro n
  fin_cases n
  · rcases h.1 ⟨0, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · rcases h.1 ⟨1, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · rcases h.1 ⟨2, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · rcases h.1 ⟨3, by omega⟩ with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (b.place m p).cell q = b.cell q := Board.place_other b hqm p
      _ = .stone p := hqcell
  · exact ⟨m, by simpa using hmstep, Board.place_same _ _ _⟩

theorem openFourExtension_has_winningCell
    {b : Board} {p : Player} {c : Coord} {d : Direction} {m : Coord}
    (hm : m ∈ OpenFourExtensionCells b p c d) :
    ∃ w, w ∈ WinningCells ⟨b.place m p, Player.other p⟩ p := by
  have hm' := (mem_openFourExtensionCells_iff b p c d m).mp hm
  rcases straightOpenFour_has_winningCell hm'.2 with ⟨w, hw⟩
  exact ⟨w, hw⟩

theorem brokenOpenThree_has_fourExtension
    {b : Board} {p : Player} {c : Coord} {d : Direction}
    (h : brokenOpenThree b p c d) :
    ∃ m, m ∈ FourExtensionCells b p := by
  rcases h with hcase | hcase
  · rcases hcase with ⟨h0, h1, h3, _hleft, hgap, _hright⟩
    rcases hgap with ⟨m, hmstep, hmempty⟩
    refine ⟨m, (mem_fourExtensionCells_iff b p m).2 ⟨hmempty, c, d, ?_⟩⟩
    intro n
    fin_cases n
    · rcases h0 with ⟨q, hqstep, hqcell⟩
      have hqm : q ≠ m := by
        intro hqm
        subst q
        rw [hmempty] at hqcell
        cases hqcell
      refine ⟨q, hqstep, ?_⟩
      calc
        (b.place m p).cell q = b.cell q := Board.place_other b hqm p
        _ = .stone p := hqcell
    · rcases h1 with ⟨q, hqstep, hqcell⟩
      have hqm : q ≠ m := by
        intro hqm
        subst q
        rw [hmempty] at hqcell
        cases hqcell
      refine ⟨q, hqstep, ?_⟩
      calc
        (b.place m p).cell q = b.cell q := Board.place_other b hqm p
        _ = .stone p := hqcell
    · exact ⟨m, by simpa using hmstep, Board.place_same _ _ _⟩
    · rcases h3 with ⟨q, hqstep, hqcell⟩
      have hqm : q ≠ m := by
        intro hqm
        subst q
        rw [hmempty] at hqcell
        cases hqcell
      refine ⟨q, hqstep, ?_⟩
      calc
        (b.place m p).cell q = b.cell q := Board.place_other b hqm p
        _ = .stone p := hqcell
  · rcases hcase with ⟨h0, h2, h3, _hleft, hgap, _hright⟩
    rcases hgap with ⟨m, hmstep, hmempty⟩
    refine ⟨m, (mem_fourExtensionCells_iff b p m).2 ⟨hmempty, c, d, ?_⟩⟩
    intro n
    fin_cases n
    · rcases h0 with ⟨q, hqstep, hqcell⟩
      have hqm : q ≠ m := by
        intro hqm
        subst q
        rw [hmempty] at hqcell
        cases hqcell
      refine ⟨q, hqstep, ?_⟩
      calc
        (b.place m p).cell q = b.cell q := Board.place_other b hqm p
        _ = .stone p := hqcell
    · exact ⟨m, by simpa using hmstep, Board.place_same _ _ _⟩
    · rcases h2 with ⟨q, hqstep, hqcell⟩
      have hqm : q ≠ m := by
        intro hqm
        subst q
        rw [hmempty] at hqcell
        cases hqcell
      refine ⟨q, hqstep, ?_⟩
      calc
        (b.place m p).cell q = b.cell q := Board.place_other b hqm p
        _ = .stone p := hqcell
    · rcases h3 with ⟨q, hqstep, hqcell⟩
      have hqm : q ≠ m := by
        intro hqm
        subst q
        rw [hmempty] at hqcell
        cases hqcell
      refine ⟨q, hqstep, ?_⟩
      calc
        (b.place m p).cell q = b.cell q := Board.place_other b hqm p
        _ = .stone p := hqcell

def HasDoubleFourThreat (s : Position) (p : Player) : Prop :=
  2 ≤ (FourExtensionCells s.board p).card

instance hasDoubleFourThreatDecidable (s : Position) (p : Player) :
    Decidable (HasDoubleFourThreat s p) := by
  unfold HasDoubleFourThreat
  infer_instance

theorem hasDoubleFourThreat_iff_exists_distinct
    (s : Position) (p : Player) :
    HasDoubleFourThreat s p ↔
      ∃ m₁ ∈ FourExtensionCells s.board p,
        ∃ m₂ ∈ FourExtensionCells s.board p, m₁ ≠ m₂ := by
  unfold HasDoubleFourThreat
  exact card_ge_two_iff_exists_distinct _

theorem hasAtLeastFive_place_preserves_empty_other
    {b : Board} {p q : Player} {c r : Coord}
    (hr : b.cell r = .empty) (hcr : r ≠ c)
    (h : hasAtLeastFive (b.place c p) p) :
    hasAtLeastFive ((b.place c p).place r q) p := by
  rcases h with ⟨start, d, hcon⟩
  refine ⟨start, d, ?_⟩
  intro n
  rcases hcon n with ⟨x, hxstep, hxcell⟩
  have hxr : x ≠ r := by
    intro hxr
    subst x
    have hsame : (b.place c p).cell r = b.cell r :=
      Board.place_other b hcr p
    rw [hsame, hr] at hxcell
    cases hxcell
  refine ⟨x, hxstep, ?_⟩
  calc
    ((b.place c p).place r q).cell x = (b.place c p).cell x :=
      Board.place_other (b.place c p) hxr q
    _ = .stone p := hxcell

/- A single defensive move can occupy at most one coordinate.  Therefore a
   position with two distinct immediate winning cells always retains one
   winning cell after any chosen defense coordinate.  This is intentionally
   stated independently of turn and terminality so it can be reused by both
   the local threat lemmas and the game-semantic proof. -/
theorem winningCell_ne_of_hasDoubleThreat
    {s : Position} {p : Player} (hthreat : HasDoubleThreat s p) (r : Coord) :
    ∃ m, m ∈ WinningCells s p ∧ m ≠ r := by
  have hcard : 1 < (WinningCells s p).card := by
    unfold HasDoubleThreat at hthreat
    omega
  rcases Finset.one_lt_card.mp hcard with ⟨a, ha, b, hb, hab⟩
  by_cases hra : r = a
  · refine ⟨b, hb, ?_⟩
    intro hba
    apply hab
    exact hra.symm.trans hba.symm
  · exact ⟨a, ha, fun har => hra har.symm⟩

theorem terminal_none_after_doubleThreat
    {s : Position} {p : Player} {r : Coord}
    (hturn : s.turn = Player.other p)
    (hterm : terminal s = none)
    (hnoopp : ¬ HasImmediateWin s (Player.other p))
    (hthreat : HasDoubleThreat s p)
    (hr : legalMove s r) :
    terminal (play s r) = none := by
  obtain ⟨m, hm, hmr⟩ := winningCell_ne_of_hasDoubleThreat hthreat r
  have hmdata := (mem_winningCells_iff s p m).mp hm
  have hm_after : (play s r).board.cell m = .empty := by
    calc
      (play s r).board.cell m = s.board.cell m :=
        Position.play_preserves_other_cells hr hmr
      _ = .empty := hmdata.1
  have hnotfull : ¬ Board.full (play s r).board := by
    intro hfull
    exact (hfull m) (hm_after)
  have htargetnone : ¬ hasAtLeastFive (play s r).board p := by
    intro hp
    have hback := hasAtLeastFive_of_place_other
      (b := s.board) (p := p) (q := s.turn) (r := r)
      (by
        rw [hturn]
        cases p <;> simp) hp
    have hsnoterm := Position.not_isTerminal_of_terminal_none hterm
    cases p with
    | black => exact hsnoterm (Or.inl hback)
    | white => exact hsnoterm (Or.inr (Or.inl hback))
  have hoppnone : ¬ hasAtLeastFive (play s r).board (Player.other p) := by
    intro hopp
    have htermr : terminal (play s r) = some (winner (Player.other p)) := by
      cases p with
      | black =>
          have hopp' : hasAtLeastFive (play s r).board .white := by
            simpa using hopp
          simp [terminal, Position.terminal, htargetnone, hopp', winner]
      | white =>
          have hopp' : hasAtLeastFive (play s r).board .black := by
            simpa using hopp
          simp [terminal, Position.terminal, htargetnone, hopp', winner]
    have hmem : r ∈ WinningMoves s (Player.other p) := by
      simp only [WinningMoves, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hturn, hr, htermr⟩
    exact hnoopp ⟨r, hmem⟩
  unfold terminal Position.terminal
  cases p with
  | black =>
      have hwhite : ¬ hasAtLeastFive (play s r).board .white := by
        simpa using hoppnone
      simp [htargetnone, hwhite, hnotfull]
  | white =>
      have hblack : ¬ hasAtLeastFive (play s r).board .black := by
        simpa using hoppnone
      simp [htargetnone, hblack, hnotfull]

theorem doubleThreat_forces_win
    {s : Position} {p : Player}
    (hturn : s.turn = Player.other p)
    (hterm : terminal s = none)
    (hnoopp : ¬ HasImmediateWin s (Player.other p))
    (hthreat : HasDoubleThreat s p) :
    CanForceWin s p := by
  apply ForceWin.respond hterm hturn
  intro r hr
  obtain ⟨m, hm, hmr⟩ := winningCell_ne_of_hasDoubleThreat hthreat r
  have hmdata := (mem_winningCells_iff s p m).mp hm
  have htermr := terminal_none_after_doubleThreat hturn hterm hnoopp hthreat hr
  have hm_after : (play s r).board.cell m = .empty := by
    calc
      (play s r).board.cell m = s.board.cell m :=
        Position.play_preserves_other_cells hr hmr
      _ = .empty := hmdata.1
  have hmlegal : legalMove (play s r) m :=
    ⟨Position.not_isTerminal_of_terminal_none htermr, hm_after⟩
  have hturnAfter : (play s r).turn = p := by
    change s.turn.other = p
    rw [hturn]
    exact Player.other_other p
  have hfive_order := hasAtLeastFive_place_preserves_empty_other
    (b := s.board) (p := p) (q := s.turn) (c := m) (r := r)
    hr.2 hmr.symm hmdata.2
  have hcomm := Board.place_commute_of_ne (b := s.board)
    (c := m) (d := r) (p := p) (q := s.turn) hmr
  rw [hcomm] at hfive_order
  have hfive : hasAtLeastFive (play (play s r) m).board p := by
    change hasAtLeastFive ((play s r).board.place m (play s r).turn) p
    rw [hturnAfter]
    exact hfive_order
  have hnoopp_after : ¬ hasAtLeastFive (play (play s r) m).board
      (Player.other p) := by
    intro h
    change hasAtLeastFive ((play s r).board.place m (play s r).turn)
      (Player.other p) at h
    rw [hturnAfter] at h
    have hback := hasAtLeastFive_of_place_other
      (b := (play s r).board) (p := Player.other p) (q := p) (r := m)
      (by cases p <;> simp) h
    have hsnoterm := Position.not_isTerminal_of_terminal_none htermr
    cases p with
    | black => exact hsnoterm (Or.inr (Or.inl hback))
    | white => exact hsnoterm (Or.inl hback)
  have hwin : terminal (play (play s r) m) = some (winner p) := by
    cases p with
    | black =>
        have hwhite : ¬ hasAtLeastFive (play (play s r) m).board .white := by
          simpa using hnoopp_after
        simp [terminal, Position.terminal, hfive, hwhite, winner]
    | white =>
        have hblack : ¬ hasAtLeastFive (play (play s r) m).board .black := by
          simpa using hnoopp_after
        simp [terminal, Position.terminal, hfive, hblack, winner]
  exact canForceWin_immediate hmlegal hwin hturnAfter

/- A move-level wrapper for the semantic double-threat theorem.  The
   post-move position is deliberately required to be non-terminal and to
   exclude an opponent immediate win; these are game conditions, not geometric
   consequences of merely seeing two winning cells. -/
theorem doubleThreat_move_forces_win
    {s : Position} {p : Player} {m : Coord}
    (hturn : s.turn = p) (hlegal : legalMove s m)
    (hchildterm : terminal (play s m) = none)
    (hnoopp : ¬ HasImmediateWin (play s m) (Player.other p))
    (hthreat : HasDoubleThreat (play s m) p) :
    CanForceWin s p := by
  have hterm : terminal s = none :=
    Position.terminal_none_of_not_isTerminal hlegal.1
  have hchildturn : (play s m).turn = Player.other p := by
    change s.turn.other = p.other
    rw [hturn]
  have hchild : CanForceWin (play s m) p :=
    doubleThreat_forces_win
      (s := play s m) (p := p) hchildturn hchildterm hnoopp hthreat
  exact ForceWin.choose hterm hturn m hlegal hchild

def ForcesWinAfter (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ CanForceWin (play s m) p

def GeometricDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  let after := play s m
  2 ≤ (openThreeWitnesses after.board p).card

def GeometricMoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop :=
  let after := play s m
  (openFourWitnesses after.board p).card = 1

def DoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ GeometricDoubleOpenThree s p m

def GeometricBrokenOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  ∃ c d, brokenOpenThree s.board p c d ∧
    m ∈ OpenFourExtensionCells s.board p c d

def BrokenOpenThreeMove (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ GeometricBrokenOpenThree s p m

def MoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ GeometricMoveCreatesSingleOpenFour s p m

instance geometricDoubleOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (GeometricDoubleOpenThree s p m) := by
  unfold GeometricDoubleOpenThree
  infer_instance

theorem geometricDoubleOpenThree_iff (s : Position) (p : Player) (m : Coord) :
    GeometricDoubleOpenThree s p m ↔
      ∃ w₁ ∈ openThreeWitnesses (play s m).board p,
        ∃ w₂ ∈ openThreeWitnesses (play s m).board p, w₁ ≠ w₂ := by
  unfold GeometricDoubleOpenThree
  exact card_ge_two_iff_exists_distinct _

instance geometricMoveCreatesSingleOpenFourDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (GeometricMoveCreatesSingleOpenFour s p m) := by
  unfold GeometricMoveCreatesSingleOpenFour
  infer_instance

instance doubleOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (DoubleOpenThree s p m) := by
  unfold DoubleOpenThree
  infer_instance

instance geometricBrokenOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (GeometricBrokenOpenThree s p m) := by
  unfold GeometricBrokenOpenThree
  infer_instance

instance brokenOpenThreeMoveDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (BrokenOpenThreeMove s p m) := by
  unfold BrokenOpenThreeMove
  infer_instance

instance moveCreatesSingleOpenFourDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (MoveCreatesSingleOpenFour s p m) := by
  unfold MoveCreatesSingleOpenFour
  infer_instance

def SingleOpenFour (s : Position) (p : Player) : Prop :=
  (openFourWitnesses s.board p).card = 1

instance singleOpenFourDecidable (s : Position) (p : Player) :
    Decidable (SingleOpenFour s p) := by
  unfold SingleOpenFour
  infer_instance

abbrev SingleOpenFourPosition := SingleOpenFour

/- `SafeDoubleOpenThree` records the semantic (multi-ply) safety condition:
   after the first move, every legal opponent reply still leaves the target
   with a forcing strategy.  The separate `ImmediateSafeDoubleOpenThree`
   predicate below is intentionally stronger and is useful for tiny tactical
   positions where the reply already exposes a one-move win. -/
def SafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  DoubleOpenThree s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      CanForceWin (play (play s m) r) p

def SafeBrokenOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  BrokenOpenThreeMove s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      CanForceWin (play (play s m) r) p

def ImmediateSafeBrokenOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  BrokenOpenThreeMove s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      HasImmediateWin (play (play s m) r) p

instance immediateSafeBrokenOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (ImmediateSafeBrokenOpenThree s p m) := by
  unfold ImmediateSafeBrokenOpenThree
  infer_instance

def ImmediateSafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  DoubleOpenThree s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      HasImmediateWin (play (play s m) r) p

theorem not_safeDoubleOpenThree_of_opponentImmediate
    {s : Position} {p : Player} {m : Coord}
    (hopp : OpponentHasImmediateWin (play s m) p) :
    ¬ SafeDoubleOpenThree s p m := by
  intro hsafe
  exact hsafe.2.2.1 hopp

theorem not_immediateSafeDoubleOpenThree_of_opponentImmediate
    {s : Position} {p : Player} {m : Coord}
    (hopp : OpponentHasImmediateWin (play s m) p) :
    ¬ ImmediateSafeDoubleOpenThree s p m := by
  intro hsafe
  exact hsafe.2.2.1 hopp

theorem brokenOpenThreeMove_creates_winningCell
    {s : Position} {p : Player} {m : Coord}
    (hmove : BrokenOpenThreeMove s p m) :
    ∃ w, w ∈ WinningCells (play s m) p := by
  rcases hmove with ⟨hturn, _hlegal, ⟨c, d, _hbroken, hline⟩⟩
  have hw := openFourExtension_has_winningCell hline
  change ∃ w, w ∈ WinningCells
    ⟨s.board.place m s.turn, s.turn.other⟩ p
  rw [hturn]
  exact hw

theorem immediateWin_canForceWin {s : Position} {p : Player}
    (h : HasImmediateWin s p) : CanForceWin s p := by
  classical
  rcases h with ⟨m, hm⟩
  have hm' : s.turn = p ∧ legalMove s m ∧
      terminal (play s m) = some (winner p) := by
    simpa [WinningMoves] using hm
  rcases hm' with ⟨hturn, hlegal, hwin⟩
  exact canForceWin_immediate hlegal hwin hturn

/- Fill a single gap in a five-cell line.  The helper is intentionally
   geometric: callers must provide the turn and non-terminal premises before
   the move is interpreted as a legal game action. -/
theorem fillGapFive_black_immediate
    {s : Position} {c m : Coord} {d : Direction} {gap : Fin 5}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hmstep : step c d gap.1 = some m)
    (hmempty : s.board.cell m = .empty)
    (hstones : ∀ n : Fin 5, n.1 ≠ gap.1 →
      occupiedAt s.board .black c d n.1) :
    ∃ m, legalMove s m ∧ terminal (play s m) = some .blackWin := by
  have hlegal : legalMove s m := ⟨hnoterm, hmempty⟩
  have hcarry : ∀ {n : Fin 5},
      occupiedAt s.board .black c d n.1 →
        occupiedAt (play s m).board .black c d n.1 := by
    intro n hn
    rcases hn with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (play s m).board.cell q = s.board.cell q := by
        change (s.board.place m s.turn).cell q = s.board.cell q
        rw [hturn]
        exact Board.place_other s.board (c := m) (d := q) hqm .black
      _ = .stone .black := hqcell
  have hrun : hasAtLeastFive (play s m).board .black := by
    refine ⟨c, d, ?_⟩
    intro n
    by_cases hng : n.1 = gap.1
    · refine ⟨m, ?_, ?_⟩
      · simpa [hng] using hmstep
      · change (s.board.place m s.turn).cell m = .stone .black
        rw [hturn]
        exact Board.place_same _ _ _
    · exact hcarry (hstones n hng)
  refine ⟨m, hlegal, ?_⟩
  change Position.terminal (play s m) = some .blackWin
  simp [Position.terminal, hrun]

theorem jumpFour_black_immediate
    {s : Position} {c : Coord} {d : Direction}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : jumpFour s.board .black c d) :
    ∃ m, legalMove s m ∧ terminal (play s m) = some .blackWin := by
  rcases hpattern with hcase | hcase | hcase
  · rcases hcase with ⟨h0, h1, h2, h4, _hleft, hgap, _hright⟩
    rcases hgap with ⟨m, hmstep, hmempty⟩
    apply fillGapFive_black_immediate (c := c) (d := d) (m := m)
      (gap := ⟨3, by omega⟩) hturn hnoterm hmstep hmempty
    intro n hneq
    fin_cases n
    · exact h0
    · exact h1
    · exact h2
    · exact (hneq (by rfl)).elim
    · exact h4
  · rcases hcase with ⟨h0, h1, h3, h4, _hleft, hgap, _hright⟩
    rcases hgap with ⟨m, hmstep, hmempty⟩
    apply fillGapFive_black_immediate (c := c) (d := d) (m := m)
      (gap := ⟨2, by omega⟩) hturn hnoterm hmstep hmempty
    intro n hneq
    fin_cases n
    · exact h0
    · exact h1
    · exact (hneq (by rfl)).elim
    · exact h3
    · exact h4
  · rcases hcase with ⟨h0, h2, h3, h4, _hleft, hgap, _hright⟩
    rcases hgap with ⟨m, hmstep, hmempty⟩
    apply fillGapFive_black_immediate (c := c) (d := d) (m := m)
      (gap := ⟨1, by omega⟩) hturn hnoterm hmstep hmempty
    intro n hneq
    fin_cases n
    · exact h0
    · exact (hneq (by rfl)).elim
    · exact h2
    · exact h3
    · exact h4

theorem straightOpenFour_black_immediate
    {s : Position} {c : Coord} {d : Direction}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : straightOpenFour s.board .black c d) :
    ∃ m, legalMove s m ∧ terminal (play s m) = some .blackWin := by
  rcases hpattern with ⟨hcon, _hleft, hright⟩
  rcases hright with ⟨m, hmstep, hmempty⟩
  have hlegal : legalMove s m := by
    exact ⟨hnoterm, hmempty⟩
  have hcarry : ∀ {n : Fin 4},
      occupiedAt s.board .black c d n.1 →
        occupiedAt (play s m).board .black c d n.1 := by
    intro n hn
    rcases hn with ⟨q, hqstep, hqcell⟩
    have hqm : q ≠ m := by
      intro hqm
      subst q
      rw [hmempty] at hqcell
      cases hqcell
    refine ⟨q, hqstep, ?_⟩
    calc
      (play s m).board.cell q = s.board.cell q := by
        change (s.board.place m s.turn).cell q = s.board.cell q
        rw [hturn]
        exact Board.place_other s.board (c := m) (d := q) hqm .black
      _ = .stone .black := hqcell
  have hrun : hasAtLeastFive (play s m).board .black := by
    refine ⟨c, d, ?_⟩
    intro n
    fin_cases n
    · exact hcarry (hcon ⟨0, by omega⟩)
    · exact hcarry (hcon ⟨1, by omega⟩)
    · exact hcarry (hcon ⟨2, by omega⟩)
    · exact hcarry (hcon ⟨3, by omega⟩)
    · refine ⟨m, ?_, ?_⟩
      · simpa using hmstep
      · change (s.board.place m s.turn).cell m = .stone .black
        rw [hturn]
        exact Board.place_same _ _ _
  refine ⟨m, hlegal, ?_⟩
  change Position.terminal (play s m) = some .blackWin
  simp [Position.terminal, hrun]

set_option maxRecDepth 100000 in
theorem singleOpenFourPosition_forces_win
    {s : Position} (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFourPosition s .black) :
    CanForceWin s .black := by
  classical
  change (openFourWitnesses s.board .black).card = 1 at hpattern
  have hcard : 0 < (openFourWitnesses s.board .black).card := by
    omega
  rcases Finset.card_pos.mp hcard with ⟨w, hw⟩
  rcases w with ⟨c, d⟩
  have hstraight : straightOpenFour s.board .black c d := by
    exact (mem_openFourWitnesses s.board .black c d).mp hw
  rcases straightOpenFour_black_immediate hturn hnoterm hstraight with
    ⟨m, hm, hwin⟩
  exact canForceWin_immediate hm hwin hturn

theorem singleOpenFour_forces_win_minimal {s : Position}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFour s .black) :
    CanForceWin s .black :=
  singleOpenFourPosition_forces_win hturn hnoterm hpattern

theorem singleOpenFour_forces_win {s : Position}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFour s .black)
  (hnoWhite : ¬ HasImmediateWin s .white) :
  CanForceWin s .black := by
  have _ := hnoWhite
  exact singleOpenFour_forces_win_minimal hturn hnoterm hpattern

theorem opponent_no_immediate_win_of_not
    {s : Position} {p : Player} (h : ¬ OpponentHasImmediateWin s p) :
    ¬ HasImmediateWin s (Player.other p) := h

theorem safeDoubleOpenThree_forces_win {s : Position} {p : Player} {m : Coord}
    (hsafe : SafeDoubleOpenThree s p m) :
  CanForceWin s p := by
  rcases hsafe with ⟨hdouble, hchildterm, hnoopp, hdefenses⟩
  have hturn : s.turn = p := hdouble.1
  have hlegal : legalMove s m := hdouble.2.1
  have hterm : terminal s = none :=
    Position.terminal_none_of_not_isTerminal hlegal.1
  have hchildturn : (play s m).turn = Player.other p := by
    change s.turn.other = p.other
    rw [hturn]
  have _ := hnoopp
  exact ForceWin.choose hterm hturn m hlegal
    (ForceWin.respond hchildterm hchildturn hdefenses)

theorem safeBrokenOpenThree_forces_win {s : Position} {p : Player} {m : Coord}
    (hsafe : SafeBrokenOpenThree s p m) :
    CanForceWin s p := by
  rcases hsafe with ⟨hmove, hchildterm, hnoopp, hdefenses⟩
  have hturn : s.turn = p := hmove.1
  have hlegal : legalMove s m := hmove.2.1
  have hterm : terminal s = none :=
    Position.terminal_none_of_not_isTerminal hlegal.1
  have hchildturn : (play s m).turn = Player.other p := by
    change s.turn.other = p.other
    rw [hturn]
  have _ := hnoopp
  exact ForceWin.choose hterm hturn m hlegal
    (ForceWin.respond hchildterm hchildturn hdefenses)

theorem immediateSafeBrokenOpenThree_implies_safe
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeBrokenOpenThree s p m) :
    SafeBrokenOpenThree s p m := by
  rcases hstrong with ⟨hmove, hchildterm, hnoopp, hdefenses⟩
  refine ⟨hmove, hchildterm, hnoopp, ?_⟩
  intro r hr
  exact immediateWin_canForceWin (hdefenses r hr)

theorem immediateSafeBrokenOpenThree_forces_win
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeBrokenOpenThree s p m) :
    CanForceWin s p :=
  safeBrokenOpenThree_forces_win
    (immediateSafeBrokenOpenThree_implies_safe hstrong)

theorem immediateSafeDoubleOpenThree_implies_safe
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeDoubleOpenThree s p m) :
    SafeDoubleOpenThree s p m := by
  rcases hstrong with ⟨hdouble, hchildterm, hnoopp, hdefenses⟩
  refine ⟨hdouble, hchildterm, hnoopp, ?_⟩
  intro r hr
  exact immediateWin_canForceWin (hdefenses r hr)

theorem immediateSafeDoubleOpenThree_forces_win
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeDoubleOpenThree s p m) :
    CanForceWin s p :=
  safeDoubleOpenThree_forces_win
    (immediateSafeDoubleOpenThree_implies_safe hstrong)

end Gomoku
