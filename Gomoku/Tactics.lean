import Gomoku.Game

namespace Gomoku

abbrev PatternWitness := Coord × Direction

noncomputable def openThreeWitnesses (b : Board) (p : Player) : Finset PatternWitness :=
  by
    classical
    exact ((Finset.univ : Finset Coord).product directions).filter
      (fun w => straightOpenThree b p w.1 w.2)

noncomputable def openFourWitnesses (b : Board) (p : Player) : Finset PatternWitness :=
  by
    classical
    exact ((Finset.univ : Finset Coord).product directions).filter
      (fun w => straightOpenFour b p w.1 w.2)

theorem mem_openFourWitnesses (b : Board) (p : Player) (c : Coord) (d : Direction) :
    (c, d) ∈ openFourWitnesses b p ↔ straightOpenFour b p c d := by
  classical
  cases d <;> simp [openFourWitnesses, directions]

noncomputable def WinningMoves (s : Position) (p : Player) : Finset Coord :=
  by
    classical
    exact (Finset.univ : Finset Coord).filter
      (fun c => s.turn = p ∧ legalMove s c ∧
        terminal (play s c) = some (winner p))

def HasImmediateWin (s : Position) (p : Player) : Prop :=
  (WinningMoves s p).Nonempty

def OpponentHasImmediateWin (s : Position) (p : Player) : Prop :=
  HasImmediateWin s (Player.other p)

def ForcesWinAfter (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ CanForceWin (play s m) p

def DoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  let after := play s m
  2 ≤ (openThreeWitnesses after.board p).card

def MoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop :=
  let after := play s m
  (openFourWitnesses after.board p).card = 1

def SingleOpenFour (s : Position) (p : Player) : Prop :=
  (openFourWitnesses s.board p).card = 1

abbrev SingleOpenFourPosition := SingleOpenFour

def SafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  DoubleOpenThree s p m ∧
    ∀ r, legalMove (play s m) r →
      ¬ OpponentHasImmediateWin (play (play s m) r) p

theorem immediateWin_canForceWin {s : Position} {p : Player}
    (h : HasImmediateWin s p) : CanForceWin s p := by
  classical
  rcases h with ⟨m, hm⟩
  have hm' : s.turn = p ∧ legalMove s m ∧
      terminal (play s m) = some (winner p) := by
    simpa [WinningMoves] using hm
  rcases hm' with ⟨hturn, hlegal, hwin⟩
  exact canForceWin_immediate hlegal hwin hturn

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

theorem singleOpenFour_forces_win {s : Position}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFour s .black)
    (hnoWhite : ¬ HasImmediateWin s .white) :
    CanForceWin s .black := by
  have _ := hnoWhite
  exact singleOpenFourPosition_forces_win hturn hnoterm hpattern

theorem opponent_no_immediate_win_of_not
    {s : Position} {p : Player} (h : ¬ OpponentHasImmediateWin s p) :
    ¬ HasImmediateWin s (Player.other p) := h

end Gomoku
