import Gomoku.Rules

namespace Gomoku

def Strategy (target : Player) : Type :=
  ∀ s, Reachable s → s.turn = target → terminal s = none →
    {m : Coord // legalMove s m}

inductive ForceWin (target : Player) : Position → Prop where
  | terminal {s : Position} (h : terminal s = some (winner target)) : ForceWin target s
  | choose {s : Position} (hterm : terminal s = none) (hturn : s.turn = target)
      (m : Coord) (hm : legalMove s m)
      (hchild : ForceWin target (play s m)) : ForceWin target s
  | respond {s : Position} (hterm : terminal s = none)
      (hturn : s.turn = Player.other target)
      (children : ∀ m, legalMove s m → ForceWin target (play s m)) :
      ForceWin target s

def CanForceWin (s : Position) (target : Player) : Prop := ForceWin target s

def StrategyTree (target : Player) (s : Position) : Prop :=
  CanForceWin s target

theorem canForceWin_terminal {s : Position} {target : Player}
    (h : terminal s = some (winner target)) : CanForceWin s target :=
  ForceWin.terminal h

theorem canForceWin_immediate {s : Position} {target : Player} {m : Coord}
    (hm : legalMove s m)
    (hwin : terminal (play s m) = some (winner target))
    (hturn : s.turn = target) :
    CanForceWin s target := by
  exact ForceWin.choose (by
    exact Position.terminal_none_of_not_isTerminal hm.1) hturn m hm
      (ForceWin.terminal hwin)

end Gomoku
