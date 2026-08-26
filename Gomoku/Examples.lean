import Gomoku.Certificate

namespace Gomoku

def center : Coord := (7, 7)

def horizontalFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (5, 7) .black) (6, 7) .black)
      (7, 7) .black)
    (8, 7) .black

def diagonalFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (3, 3) .black) (4, 4) .black)
      (5, 5) .black)
    (6, 6) .black

def boundaryFourBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place Board.empty (0, 7) .black) (1, 7) .black)
      (2, 7) .black)
    (3, 7) .black

def overlineBoard : Board :=
  Board.place
    (Board.place
      (Board.place
        (Board.place
          (Board.place
            (Board.place Board.empty (4, 7) .black) (5, 7) .black)
          (6, 7) .black)
        (7, 7) .black)
      (8, 7) .black)
    (9, 7) .black

example : initialPosition.turn = .black := rfl

example : initialPosition.board.cell center = .empty := by
  rfl

example : legalMove initialPosition center := by
  constructor
  · exact Position.initial_not_terminal
  · rfl

example : ∃ c, legalMove initialPosition c := by
  exact Position.exists_legalMove_of_terminal_none (by
    exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)

example : legalMove initialPosition
    ((defaultStrategy .black initialPosition Position.Reachable.initial rfl (by
      exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)).1) := by
  exact defaultStrategy_legal .black initialPosition Position.Reachable.initial rfl
    (Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)

example : (play initialPosition center).turn = .white := by
  rfl

example : (play initialPosition center).board.cell center = .stone .black := by
  exact Board.place_same _ _ _

example : straightOpenFour horizontalFourBoard .black (5, 7) .horizontal := by
  native_decide

example : straightOpenFour diagonalFourBoard .black (3, 3) .diagonalUp := by
  native_decide

example : ¬ straightOpenFour boundaryFourBoard .black (0, 7) .horizontal := by
  native_decide

example : hasAtLeastFive overlineBoard .black := by
  native_decide

example : terminal ⟨overlineBoard, .white⟩ = some .blackWin := by
  native_decide

example : ¬ legalMove ⟨overlineBoard, .white⟩ center := by
  native_decide

example : ¬ legalMove (play initialPosition center) center := by
  native_decide

example : Board.emptyCount (Board.place Board.empty center .black) + 1 =
    Board.emptyCount Board.empty := by
  exact Board.emptyCount_place_of_empty _ _ _ rfl

example : Position.countBlack (Position.play initialPosition center) = 1 := by
  native_decide

example {s : Position} (h : Reachable s) :
    ¬ (hasAtLeastFive s.board .black ∧ hasAtLeastFive s.board .white) := by
  exact Position.reachable_not_both_winners h

example {s : Position} {p : Player} (hs : Reachable s) :
    (∃ σ : Strategy p, StrategyRealizes σ s hs) ↔ CanForceWin s p := by
  exact strategyRealizes_iff_canForceWin hs

example {s : Position} {p : Player}
    (h : terminal s = some (winner p)) : CanForceWin s p :=
  canForceWin_terminal h

example {s : Position} {p : Player} {m : Coord}
    (hm : legalMove s m)
    (hwin : terminal (play s m) = some (winner p))
    (hturn : s.turn = p) : CanForceWin s p :=
  canForceWin_immediate hm hwin hturn

example :
    CanForceWin ⟨overlineBoard, .white⟩ .black := by
  exact certificate_sound
    { target := .black
      root := ⟨overlineBoard, .white⟩
      proof := .terminal (by native_decide) }

example :
    checkCertificate { target := .black, root := 0, nodes := #[] } = false := by
  rfl

end Gomoku
