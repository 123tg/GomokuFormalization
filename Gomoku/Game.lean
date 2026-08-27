import Gomoku.Rules

namespace Gomoku

def Strategy (target : Player) : Type :=
  ∀ s, Reachable s → s.turn = target → terminal s = none →
    {m : Coord // legalMove s m}
-- 定义目标玩家的局面策略：在任一可达、轮到自己且未终局的局面选择一个合法落子。

inductive ForceWin (target : Player) : Position → Prop where
  | terminal {s : Position} (h : terminal s = some (winner target)) : ForceWin target s
  | choose {s : Position} (hterm : terminal s = none) (hturn : s.turn = target)
      (m : Coord) (hm : legalMove s m)
      (hchild : ForceWin target (play s m)) : ForceWin target s
  | respond {s : Position} (hterm : terminal s = none)
      (hturn : s.turn = Player.other target)
      (children : ∀ m, legalMove s m → ForceWin target (play s m)) :
      ForceWin target s
-- 归纳定义强制获胜树：终局获胜、己方选择一个获胜子局面、对手所有合法应手均获胜。

def CanForceWin (s : Position) (target : Player) : Prop := ForceWin target s
-- 将强制获胜树包装为“目标玩家能从局面 s 强制获胜”的核心命题。

def StrategyTree (target : Player) (s : Position) : Prop :=
  CanForceWin s target
-- 提供强调树形策略语义的别名，与 CanForceWin 定义等价。

noncomputable def defaultStrategy (target : Player) : Strategy target :=
  fun s _ _ hterm =>
    ⟨Classical.choose (Position.exists_legalMove_of_terminal_none hterm),
      Classical.choose_spec (Position.exists_legalMove_of_terminal_none hterm)⟩
-- 用经典选择从任一未终局局面取一个合法落子，构造不保证获胜的默认总策略。

theorem defaultStrategy_legal (target : Player) (s : Position)
    (hs : Reachable s) (hturn : s.turn = target) (hterm : terminal s = none) :
    legalMove s ((defaultStrategy target s hs hturn hterm).1) :=
  (defaultStrategy target s hs hturn hterm).2
-- 说明默认策略返回值的依赖类型证明了所选落子必然合法。

theorem canForceWin_terminal {s : Position} {target : Player}
    (h : terminal s = some (winner target)) : CanForceWin s target :=
  ForceWin.terminal h
-- 把已经由目标玩家获胜的终局直接提升为 CanForceWin。

theorem canForceWin_immediate {s : Position} {target : Player} {m : Coord}
    (hm : legalMove s m)
    (hwin : terminal (play s m) = some (winner target))
    (hturn : s.turn = target) :
    CanForceWin s target := by
  exact ForceWin.choose (by
    exact Position.terminal_none_of_not_isTerminal hm.1) hturn m hm
      (ForceWin.terminal hwin)
-- 说明目标玩家若有一步合法落子立即获胜，则当前局面可强制获胜。

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
-- 从己方回合的 CanForceWin 证明中提取一个保持强制获胜的合法着法。

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
-- 构造规范获胜策略：在获胜区域选择保持获胜的着法，其他局面退回默认合法策略。

theorem canonicalWinningStrategy_child
    {target : Player} {s : Position} (hs : Reachable s)
    (hturn : s.turn = target) (hterm : terminal s = none)
    (hwin : CanForceWin s target) :
    CanForceWin
      (play s ((canonicalWinningStrategy target s hs hturn hterm).1)) target := by
  simp only [canonicalWinningStrategy, dif_pos hwin]
  exact (Classical.choose_spec
    (canForceWin_move_exists hwin hterm hturn)).2
-- 说明规范获胜策略在己方获胜局面所选的子局面仍满足 CanForceWin。

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
-- 归纳描述具体策略 σ 如何实现获胜树：己方节点服从 σ，对手节点覆盖全部合法应手。

theorem StrategyRealizes.sound {target : Player} {σ : Strategy target}
    {s : Position} {hs : Reachable s} :
    StrategyRealizes σ s hs → CanForceWin s target
  | .terminal _ hwin => ForceWin.terminal hwin
  | .choose _ hterm hturn m hm _ child =>
      ForceWin.choose hterm hturn m hm (StrategyRealizes.sound child)
  | .respond _ hterm hturn children =>
      ForceWin.respond hterm hturn
        (fun m hm => StrategyRealizes.sound (children m hm))
-- 遗忘具体策略一致性信息，把 StrategyRealizes 证明转换为抽象的 CanForceWin 证明。

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
-- 以空点数严格下降为良基度量，证明规范获胜策略确实实现任意可达的 CanForceWin 树。

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
-- 建立策略语义与归纳获胜语义的等价：存在实现策略当且仅当 CanForceWin 成立。

end Gomoku
