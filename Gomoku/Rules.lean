import Gomoku.Geometry

namespace Gomoku

inductive Outcome where
  | blackWin
  | whiteWin
  | draw
  deriving DecidableEq, Repr

def winner : Player → Outcome
  | .black => .blackWin
  | .white => .whiteWin

structure Position where
  board : Board
  turn : Player

namespace Position

def initial : Position := ⟨Board.empty, .black⟩

def isTerminal (s : Position) : Prop :=
  hasAtLeastFive s.board .black ∨ hasAtLeastFive s.board .white ∨ Board.full s.board

instance isTerminalDecidable (s : Position) : Decidable (isTerminal s) := by
  unfold isTerminal
  infer_instance

def terminal (s : Position) : Option Outcome :=
  if hasAtLeastFive s.board .black then some .blackWin
  else if hasAtLeastFive s.board .white then some .whiteWin
  else if Board.full s.board then some .draw
  else none

def legalMove (s : Position) (c : Coord) : Prop :=
  ¬ isTerminal s ∧ s.board.cell c = .empty

instance legalMoveDecidable (s : Position) (c : Coord) : Decidable (legalMove s c) := by
  unfold legalMove
  infer_instance

def play (s : Position) (c : Coord) : Position :=
  ⟨s.board.place c s.turn, s.turn.other⟩

inductive Reachable : Position → Prop where
  | initial : Reachable Position.initial
  | step {s : Position} {c : Coord} :
      Reachable s → legalMove s c → Reachable (play s c)

def countBlack (s : Position) : Nat := s.board.count .black
def countWhite (s : Position) : Nat := s.board.count .white

theorem legalMove_empty {s : Position} {c : Coord} (h : legalMove s c) :
    s.board.cell c = .empty := h.2

theorem play_turn (s : Position) (c : Coord) : (play s c).turn = s.turn.other := rfl

theorem play_legal_cell {s : Position} {c : Coord} (h : legalMove s c) :
    (play s c).board.cell c = .stone s.turn := by
  exact Board.place_same _ _ _

theorem terminal_no_legal {s : Position} (hs : isTerminal s) (c : Coord) :
    ¬ legalMove s c := by
  intro h
  exact h.1 hs

theorem terminal_outcome_isTerminal {s : Position} {o : Outcome}
    (h : terminal s = some o) : isTerminal s := by
  unfold terminal at h
  split at h
  · exact Or.inl ‹hasAtLeastFive s.board .black›
  · split at h
    · exact Or.inr (Or.inl ‹hasAtLeastFive s.board .white›)
    · split at h
      · exact Or.inr (Or.inr ‹Board.full s.board›)
      · simp at h

theorem terminal_outcome_no_legal {s : Position} {o : Outcome}
    (h : terminal s = some o) (c : Coord) : ¬ legalMove s c := by
  exact terminal_no_legal (terminal_outcome_isTerminal h) c

theorem full_no_legal {s : Position} (hfull : Board.full s.board) (c : Coord) :
    ¬ legalMove s c := by
  intro h
  exact (hfull c) h.2

theorem terminal_none_of_not_isTerminal {s : Position} (h : ¬ isTerminal s) :
    terminal s = none := by
  unfold terminal
  split <;> simp_all [isTerminal]

theorem initial_not_terminal : ¬ isTerminal initial := by
  intro h
  rcases h with h | h | h
  · rcases h with ⟨c, d, hc⟩
    have hstone : (Position.initial.board).cell c = .stone .black := by
      rcases hc ⟨0, by omega⟩ with ⟨q, hq, hcell⟩
      simpa [initial, Board.empty] using hcell
    simp [initial, Board.empty] at hstone
  · rcases h with ⟨c, d, hc⟩
    have hstone : (Position.initial.board).cell c = .stone .white := by
      rcases hc ⟨0, by omega⟩ with ⟨q, hq, hcell⟩
      simpa [initial, Board.empty] using hcell
    simp [initial, Board.empty] at hstone
  · have hempty : Position.initial.board.cell (0, 0) = .empty := by
      rfl
    exact h (0, 0) hempty

theorem play_preserves_other_cells {s : Position} {c d : Coord}
    (hlegal : legalMove s c) (hne : d ≠ c) :
    (play s c).board.cell d = s.board.cell d := by
  change (s.board.place c s.turn).cell d = s.board.cell d
  exact Board.place_other s.board hne s.turn

theorem play_target_cell {s : Position} {c : Coord} (hlegal : legalMove s c) :
    (play s c).board.cell c = .stone s.turn :=
  Board.place_same _ _ _

theorem play_emptyCount_succ {s : Position} {c : Coord} (hlegal : legalMove s c) :
    Board.emptyCount (play s c).board + 1 = Board.emptyCount s.board := by
  simpa [play] using Board.emptyCount_place_of_empty s.board c s.turn hlegal.2

theorem play_emptyCount_lt {s : Position} {c : Coord} (hlegal : legalMove s c) :
    Board.emptyCount (play s c).board < Board.emptyCount s.board := by
  have h := play_emptyCount_succ hlegal
  omega

theorem reachable_count_invariant {s : Position} (h : Reachable s) :
    (match s.turn with
    | .black => countBlack s = countWhite s
    | .white => countBlack s = countWhite s + 1) := by
  induction h with
  | initial => rfl
  | @step s c hs hlegal ih =>
      cases hturn : s.turn with
      | black =>
          have hblack :
              (play s c).board.count .black = s.board.count .black + 1 := by
            simpa [play, hturn] using Board.count_place_same_of_empty s.board c .black hlegal.2
          have hwhite :
              (play s c).board.count .white = s.board.count .white := by
            simpa [play, hturn] using Board.count_place_other_of_empty s.board c .black .white hlegal.2 (by simp)
          have hchildturn : (play s c).turn = .white := by
            simp [play_turn, hturn]
          rw [hchildturn]
          simp [countBlack, countWhite, hblack, hwhite]
          have ih' : s.board.count .black = s.board.count .white := by
            simpa [countBlack, countWhite, hturn] using ih
          rw [ih']
      | white =>
          have hblack :
              (play s c).board.count .black = s.board.count .black := by
            simpa [play, hturn] using Board.count_place_other_of_empty s.board c .white .black hlegal.2 (by simp)
          have hwhite :
              (play s c).board.count .white = s.board.count .white + 1 := by
            simpa [play, hturn] using Board.count_place_same_of_empty s.board c .white hlegal.2
          have hchildturn : (play s c).turn = .black := by
            simp [play_turn, hturn]
          rw [hchildturn]
          simp [countBlack, countWhite, hblack, hwhite]
          have ih' : s.board.count .black = s.board.count .white + 1 := by
            simpa [countBlack, countWhite, hturn] using ih
          exact ih'

theorem reachable_not_both_winners {s : Position} (h : Reachable s)
    (hnterm : ¬ isTerminal s) :
    ¬ (hasAtLeastFive s.board .black ∧ hasAtLeastFive s.board .white) := by
  intro hboth
  exact hnterm (Or.inl hboth.1)

end Position

def IsTerminal (s : Position) : Prop := Position.isTerminal s
def legalMove (s : Position) (c : Coord) : Prop := Position.legalMove s c
def play (s : Position) (c : Coord) : Position := Position.play s c
def terminal (s : Position) : Option Outcome := Position.terminal s
def initialPosition : Position := Position.initial
def Reachable (s : Position) : Prop := Position.Reachable s

instance legalMoveDecidableGlobal (s : Position) (c : Coord) : Decidable (legalMove s c) := by
  exact Position.legalMoveDecidable s c

end Gomoku
