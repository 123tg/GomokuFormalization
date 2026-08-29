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

noncomputable def defaultStrategy (target : Player) : Strategy target :=
  fun s _ _ hterm =>
    ⟨Classical.choose (Position.exists_legalMove_of_terminal_none hterm),
      Classical.choose_spec (Position.exists_legalMove_of_terminal_none hterm)⟩

theorem defaultStrategy_legal (target : Player) (s : Position)
    (hs : Reachable s) (hturn : s.turn = target) (hterm : terminal s = none) :
    legalMove s ((defaultStrategy target s hs hturn hterm).1) :=
  (defaultStrategy target s hs hturn hterm).2

theorem canForceWin_terminal {s : Position} {target : Player}
    (h : terminal s = some (winner target)) : CanForceWin s target :=
  ForceWin.terminal h

/- At a position which is already terminal, `ForceWin` has exactly one
   possible constructor: the recorded outcome must be the target player's
   win.  In particular, neither a draw nor an opponent win can be skipped by
   continuing the game tree. -/
theorem canForceWin_terminal_iff {s : Position} {target : Player} {out : Outcome}
    (hterm : terminal s = some out) :
    CanForceWin s target ↔ out = winner target := by
  constructor
  · intro hwin
    cases hwin with
    | terminal hwin =>
        rw [hterm] at hwin
        exact Option.some.inj hwin
    | choose hnone _ _ _ _ =>
        rw [hterm] at hnone
        simp at hnone
    | respond hnone _ _ =>
        rw [hterm] at hnone
        simp at hnone
  · intro hout
    subst out
    exact canForceWin_terminal hterm

theorem not_canForceWin_of_terminal_ne
    {s : Position} {target : Player} {out : Outcome}
    (hterm : terminal s = some out) (hne : out ≠ winner target) :
    ¬ CanForceWin s target := by
  intro hwin
  exact hne ((canForceWin_terminal_iff hterm).mp hwin)

theorem not_canForceWin_of_draw {s : Position}
    (hdraw : terminal s = some .draw) (target : Player) :
    ¬ CanForceWin s target := by
  apply not_canForceWin_of_terminal_ne hdraw
  cases target <;> decide

/- If it is the opponent's turn and one of their legal moves ends the game in
   their favour, the target cannot have a forcing win.  This is the game-level
   form of the usual "must answer an immediate threat" rule and is useful for
   auditing tactical premises. -/
theorem not_canForceWin_of_opponent_immediate
    {s : Position} {target : Player} {m : Coord}
    (hterm : terminal s = none)
    (hturn : s.turn = Player.other target)
    (hm : legalMove s m)
    (hwin : terminal (play s m) = some (winner (Player.other target))) :
    ¬ CanForceWin s target := by
  intro hforce
  cases hforce with
  | terminal htarget =>
      rw [hterm] at htarget
      simp at htarget
  | choose _ htargetTurn _ _ _ =>
      exact (Player.self_ne_other target (htargetTurn.symm.trans hturn)).elim
  | respond _ _ children =>
      have hchild : CanForceWin (play s m) target := children m hm
      exact not_canForceWin_of_terminal_ne hwin (by
        cases target <;> decide) hchild

theorem canForceWin_immediate {s : Position} {target : Player} {m : Coord}
    (hm : legalMove s m)
    (hwin : terminal (play s m) = some (winner target))
    (hturn : s.turn = target) :
    CanForceWin s target := by
  exact ForceWin.choose (by
    exact Position.terminal_none_of_not_isTerminal hm.1) hturn m hm
      (ForceWin.terminal hwin)

theorem canForceWin_move_exists {s : Position} {target : Player}
    (hwin : CanForceWin s target) (hterm : terminal s = none)
    (hturn : s.turn = target) :
    ∃ m, legalMove s m ∧ CanForceWin (play s m) target := by
  cases hwin with
  | terminal h =>
      rw [hterm] at h
      simp at h
  | choose _ _ m hm hchild =>
      exact ⟨m, hm, hchild⟩
  | respond _ hturn' _ =>
      exact (Player.self_ne_other target (hturn.symm.trans hturn')).elim

/- At a non-terminal target-player node, the inductive game semantics is
   exactly existential: one legal child which remains winning is enough. -/
theorem canForceWin_target_iff
    {s : Position} {target : Player}
    (hterm : terminal s = none) (hturn : s.turn = target) :
    CanForceWin s target ↔
      ∃ m, legalMove s m ∧ CanForceWin (play s m) target := by
  constructor
  · intro hwin
    exact canForceWin_move_exists hwin hterm hturn
  · rintro ⟨m, hm, hchild⟩
    exact ForceWin.choose hterm hturn m hm hchild

/- At a non-terminal opponent node, the semantics is universal: omitting
   even one legal reply is insufficient for a forcing-win proof. -/
theorem canForceWin_opponent_iff
    {s : Position} {target : Player}
    (hterm : terminal s = none)
    (hturn : s.turn = Player.other target) :
    CanForceWin s target ↔
      ∀ m, legalMove s m → CanForceWin (play s m) target := by
  constructor
  · intro hwin
    cases hwin with
    | terminal htarget =>
        rw [hterm] at htarget
        simp at htarget
    | choose _ htargetTurn _ _ _ =>
        exact (Player.self_ne_other target
          (htargetTurn.symm.trans hturn)).elim
    | respond _ _ children =>
        exact children
  · intro children
    exact ForceWin.respond hterm hturn children

/- This strategy chooses a force-preserving move whenever the current
   position is winning for `target`; outside the winning region it falls back
   to an arbitrary legal move.  It is noncomputable because its purpose is the
   mathematical equivalence between strategies and `CanForceWin`, not search. -/
noncomputable def canonicalWinningStrategy (target : Player) : Strategy target :=
  by
    classical
    intro s hs hturn hterm
    if hwin : CanForceWin s target then
      let witness := Classical.choose
        (canForceWin_move_exists hwin hterm hturn)
      exact ⟨witness,
        (Classical.choose_spec
          (canForceWin_move_exists hwin hterm hturn)).1⟩
    else
      exact defaultStrategy target s hs hturn hterm

theorem canonicalWinningStrategy_child
    {target : Player} {s : Position} (hs : Reachable s)
    (hturn : s.turn = target) (hterm : terminal s = none)
    (hwin : CanForceWin s target) :
    CanForceWin
      (play s ((canonicalWinningStrategy target s hs hturn hterm).1)) target := by
  simp only [canonicalWinningStrategy, dif_pos hwin]
  exact (Classical.choose_spec
    (canForceWin_move_exists hwin hterm hturn)).2

/- `StrategyRealizes σ s hs` says that the concrete position strategy `σ`
   wins from the reachable position `s`: at target nodes the tree follows
   exactly the move returned by `σ`, while opponent nodes contain every legal
   reply. -/
inductive StrategyRealizes {target : Player} (σ : Strategy target) :
    (s : Position) → Reachable s → Prop where
  | terminal {s : Position} (hs : Reachable s)
      (hwin : terminal s = some (winner target)) :
      StrategyRealizes σ s hs
  | choose {s : Position} (hs : Reachable s)
      (hterm : terminal s = none) (hturn : s.turn = target)
      (m : Coord) (hm : legalMove s m)
      (hagrees : (σ s hs hturn hterm).1 = m)
      (child : StrategyRealizes σ (play s m)
        (Position.Reachable.step hs hm)) :
      StrategyRealizes σ s hs
  | respond {s : Position} (hs : Reachable s)
      (hterm : terminal s = none)
      (hturn : s.turn = Player.other target)
      (children : ∀ m (hm : legalMove s m),
        StrategyRealizes σ (play s m) (Position.Reachable.step hs hm)) :
      StrategyRealizes σ s hs

theorem StrategyRealizes.sound {target : Player} {σ : Strategy target}
    {s : Position} {hs : Reachable s} :
    StrategyRealizes σ s hs → CanForceWin s target
  | .terminal _ hwin => ForceWin.terminal hwin
  | .choose _ hterm hturn m hm _ child =>
      ForceWin.choose hterm hturn m hm (StrategyRealizes.sound child)
  | .respond _ hterm hturn children =>
      ForceWin.respond hterm hturn
        (fun m hm => StrategyRealizes.sound (children m hm))

theorem canonicalWinningStrategy_realizes
    {target : Player} {s : Position} (hs : Reachable s)
    (hwin : CanForceWin s target) :
    StrategyRealizes (canonicalWinningStrategy target) s hs := by
  induction hmeasure : Board.emptyCount s.board using Nat.strong_induction_on
      generalizing s with
  | h n ih =>
      cases hwin with
      | terminal hterminal =>
          exact StrategyRealizes.terminal hs hterminal
      | choose hterm hturn original hm horiginalChild =>
          let selected := canonicalWinningStrategy target s hs hturn hterm
          have hselectedWin : CanForceWin (play s selected.1) target :=
            canonicalWinningStrategy_child hs hturn hterm
              (ForceWin.choose hterm hturn original hm horiginalChild)
          have hlt : Board.emptyCount (play s selected.1).board < n := by
            change Board.emptyCount (Position.play s selected.1).board < n
            have hdesc := Position.play_emptyCount_lt selected.2
            omega
          have hchild := ih _ hlt
            (Position.Reachable.step hs selected.2) hselectedWin (by rfl)
          exact StrategyRealizes.choose hs hterm hturn selected.1 selected.2 rfl hchild
      | respond hterm hturn children =>
          apply StrategyRealizes.respond hs hterm hturn
          intro m hm
          have hlt : Board.emptyCount (play s m).board < n := by
            change Board.emptyCount (Position.play s m).board < n
            have hdesc := Position.play_emptyCount_lt hm
            omega
          exact ih _ hlt (Position.Reachable.step hs hm) (children m hm) (by rfl)

theorem strategyRealizes_iff_canForceWin
    {target : Player} {s : Position} (hs : Reachable s) :
    (∃ σ : Strategy target, StrategyRealizes σ s hs) ↔
      CanForceWin s target := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact StrategyRealizes.sound hσ
  · intro hwin
    exact ⟨canonicalWinningStrategy target,
      canonicalWinningStrategy_realizes hs hwin⟩

end Gomoku
