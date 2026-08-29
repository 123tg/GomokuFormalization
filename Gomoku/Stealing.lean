import Gomoku.Defense

/-!
# 纯策略级证明：策略偷换（strategy stealing）

本文件不依赖 C++ 搜索器，不依赖任何证书；证明完全在策略与博弈树层面进行。

## 结论

从 7×7 空棋盘出发，先手（黑方）能阻止白方获胜（结果至少为和棋）：

```
theorem black_can_prevent_white_initial : BlackCanPreventWhiteWin initialPosition
```

这是五子棋“先手不可能输”的经典论证，也是本项目第一个不经过搜索的
空棋盘定理。它不能推出先手必胜（`CanForceWin initialPosition .black`），
也不涉及 `StandardDraw`（白方是否也能阻止黑胜是另一个问题）。

## 论证思路（影子对局）

反设白方（后手）有强制获胜策略 σ。黑方“偷”σ：

1. 黑方第一着任意落子 c0。
2. 此后黑方维持一个“影子对局”：影子局中的白方（σ 玩家）与真实黑方同色，
   每一步照 σ 落子；影子局中的黑方（σ 对手）与真实白方同色，照搬真实白方
   的每一步。真实黑方在影子局 σ 玩家落子的同时，若该点尚未被占则照走，
   否则改走任意其他合法点（多出来的黑子只可能帮助黑方）。
3. 真实白方的棋子与影子局中 σ 对手的棋子完全一致；σ 的获胜树保证
   σ 对手永远不能成五，因此真实白方永远不能获胜：黑方至少和棋。

`ShadowSim` 归纳刻画真实局面 R 与影子局面 S 的同步关系；主要引理
`steal_core` 沿真实局面的空格数递减，对照 σ 的 `StrategyRealizes` 树逐节点
构造 `CanPreventWin .black` 防守树：白方回合覆盖全部合法应手，黑方回合
选择保持防守的着法。`not_canForceWin_implies_canPreventWin` 是有限博弈的
确定性引理，把“白方无强制胜”提升为正向的 `BlackCanPreventWhiteWin`。

注意：偷换策略天然依赖历史（需要知道影子局面才能决定当前着法），
因此这里把结论表述为 `CanPreventWin`（存在策略的博弈树语义），
而不是位置型 `Strategy` 函数。

另注：本仓库的 `Gomoku.Pairing` 提供了“配对策略”框架，但 7×7 棋盘上
不存在能覆盖全部 60 个五连窗口的静态配对（穷举回溯验证），
因此空棋盘的白方防守不能走配对策略路线，这正是本文件选择策略偷换的原因。
-/

namespace Gomoku

namespace Stealing

/-! ## 确定性：不能强制获胜 ⇒ 对方能阻止获胜 -/

/-- 有限完全信息博弈的确定性引理：若目标玩家 `target` 从局面 `s` 不能强制获胜，
则其对手存在策略使 `target` 最终无法获胜（即对手能阻止 target 获胜）。
对空点数做强归纳：target 回合需要覆盖全部合法应手，对手回合只需存在一步
保持防守的着法。 -/
theorem not_canForceWin_implies_canPreventWin {s : Position} {target : Player} :
    ¬ CanForceWin s target → CanPreventWin (Player.other target) s := by
  classical
  induction hmeasure : Board.emptyCount s.board using Nat.strong_induction_on
      generalizing s with
  | h n ih =>
    intro hnot
    by_cases hterm : terminal s = none
    · by_cases hturn : s.turn = target
      · -- target 回合：target 不能强制胜 ⇒ 每个合法着法后都不能强制胜
        refine CanPreventWin.attackerMoves hterm (by simpa using hturn) ?_
        intro m hm
        have hchild : ¬ CanForceWin (play s m) target := by
          intro hc
          exact hnot (ForceWin.choose hterm hturn m hm hc)
        have hlt : Board.emptyCount (play s m).board < n := by
          change Board.emptyCount (Position.play s m).board < n
          have hdesc := Position.play_emptyCount_lt hm
          omega
        exact ih (Board.emptyCount (play s m).board) hlt (by rfl) hchild
      · -- 对手回合：若每个合法着法后 target 都能强制胜，则 target 现在就能强制胜
        have hturn' : s.turn = Player.other target := by
          cases target <;> cases ht : s.turn
          · exact (hturn ht).elim
          · rfl
          · rfl
          · exact (hturn ht).elim
        have hnotall : ¬ ∀ m, legalMove s m → CanForceWin (play s m) target := by
          intro hall
          exact hnot (ForceWin.respond hterm hturn' hall)
        have hex : ∃ m, legalMove s m ∧ ¬ CanForceWin (play s m) target := by
          by_contra hnone
          apply hnotall
          intro m hm
          by_contra hchild
          exact hnone ⟨m, hm, hchild⟩
        rcases hex with ⟨m, hm, hchild⟩
        have hlt : Board.emptyCount (play s m).board < n := by
          change Board.emptyCount (Position.play s m).board < n
          have hdesc := Position.play_emptyCount_lt hm
          omega
        refine CanPreventWin.defenderMove hterm hturn' m hm ?_
        exact ih (Board.emptyCount (play s m).board) hlt (by rfl) hchild
    · -- 终局：target 获胜不可能，只能是对方获胜或和棋
      cases ht : terminal s with
      | none => exact (hterm ht).elim
      | some out =>
          have hout : terminal s = some out := ht
          have hne : out ≠ winner target := by
            intro hw
            subst out
            exact hnot ((canForceWin_terminal_iff hout).mpr rfl)
          have hout' : out = winner (Player.other target) ∨ out = .draw := by
            cases target <;> cases out <;> simp [Player.other, winner] at hne ⊢
          cases hout' with
          | inl hw =>
              exact CanPreventWin.terminal (by simpa [hw] using hout)
          | inr hd =>
              exact CanPreventWin.draw (by simpa [hd] using hout)

/-! ## 影子对局：真实局面与 σ 玩家局面的同步 -/

/-- 黑方（先手）的第一着：棋盘中心。偷换论证对第一着的位置没有要求。 -/
def c0 : Coord := (3, 3)

/-- 落子后目标格为当前玩家的棋子（用全局 `play` 别名表述，便于重写）。 -/
private theorem play_same_cell {s : Position} {c : Coord} (hlegal : legalMove s c) :
    (play s c).board.cell c = .stone s.turn := by
  exact Position.play_target_cell hlegal

/-- 落子不改变其他格子（用全局 `play` 别名表述，便于重写）。 -/
private theorem play_other_cell {s : Position} {c d : Coord}
    (hlegal : legalMove s c) (hne : d ≠ c) :
    (play s c).board.cell d = s.board.cell d := by
  exact Position.play_preserves_other_cells hlegal hne

/-- 影子对局同步关系：真实局面 `R` 与影子局面 `S` 沿对局同步推进。
影子局中 σ 玩家（白方）与真实黑方同色，σ 对手（黑方）与真实白方同色。
* `start`：黑方先落子 c0 后，影子局面为空棋盘（黑方先手、轮到黑方）。
* `whiteStep`：真实白方落子 `w` 时，影子局中 σ 对手照搬 `w`。
* `blackStep`：真实黑方落子 `wR` 时，影子局中 σ 玩家落子 `wS`；
  `hsync` 表示 `wS = wR`（正常情形），或 `wS` 已是真实黑方的棋子
  （σ 指示已占点时改走其他点的偷换情形）。 -/
inductive ShadowSim : Position → Position → Prop where
  | start : ShadowSim (play initialPosition c0) initialPosition
  | whiteStep {R S : Position} {w : Coord} (hsim : ShadowSim R S)
      (hturnR : R.turn = .white) (hturnS : S.turn = .black)
      (hlegalR : legalMove R w) (hlegalS : legalMove S w) :
      ShadowSim (play R w) (play S w)
  | blackStep {R S : Position} {wR wS : Coord} (hsim : ShadowSim R S)
      (hturnR : R.turn = .black) (hturnS : S.turn = .white)
      (hlegalR : legalMove R wR) (hlegalS : legalMove S wS)
      (hsync : wS = wR ∨ R.board.cell wS = .stone .black) :
      ShadowSim (play R wR) (play S wS)

namespace ShadowSim

/-- 轮次镜像：影子局的轮次始终是真实局轮次的对手。 -/
theorem turn_other {R S : Position} (hsim : ShadowSim R S) :
    S.turn = R.turn.other := by
  induction hsim with
  | start =>
      rfl
  | @whiteStep R S w hsim hturnR hturnS _ _ =>
      change S.turn.other = R.turn.other.other
      simp [hturnS, hturnR]
  | @blackStep R S wR wS hsim hturnR hturnS _ _ _ =>
      change S.turn.other = R.turn.other.other
      simp [hturnS, hturnR]

/-- 镜像引理（白棋侧）：真实白棋 ↔ 影子黑棋，两边棋子完全一致。 -/
theorem white_iff_black {R S : Position} (hsim : ShadowSim R S) (c : Coord) :
    R.board.cell c = .stone .white ↔ S.board.cell c = .stone .black := by
  induction hsim generalizing c with
  | start =>
      constructor
      · intro h
        by_cases hc : c = c0
        · subst c
          have hb : (play initialPosition c0).board.cell c0 = .stone .black := by
            change (initialPosition.board.place c0 .black).cell c0 = .stone .black
            exact Board.place_same initialPosition.board c0 .black
          rw [hb] at h
          cases h
        · have hb : (play initialPosition c0).board.cell c = .empty := by
            change (initialPosition.board.place c0 .black).cell c = .empty
            exact Board.place_other initialPosition.board hc .black
          rw [hb] at h
          cases h
      · intro h
        simp [initialPosition, Position.initial, Board.empty] at h
  | @whiteStep R S w hsim hturnR hturnS hlegalR hlegalS ih =>
      constructor
      · intro h
        by_cases hc : c = w
        · subst c
          simpa [hturnS] using play_same_cell hlegalS
        · have hR : R.board.cell c = .stone .white := by
            rw [← play_other_cell hlegalR hc]
            exact h
          have hS : S.board.cell c = .stone .black := (ih c).mp hR
          rw [play_other_cell hlegalS hc]
          exact hS
      · intro h
        by_cases hc : c = w
        · subst c
          simpa [hturnR] using play_same_cell hlegalR
        · have hS : S.board.cell c = .stone .black := by
            rw [← play_other_cell hlegalS hc]
            exact h
          have hR : R.board.cell c = .stone .white := (ih c).mpr hS
          rw [play_other_cell hlegalR hc]
          exact hR
  | @blackStep R S wR wS hsim hturnR hturnS hlegalR hlegalS hsync ih =>
      constructor
      · intro h
        have hne : c ≠ wR := by
          intro hc
          subst c
          have hb : (play R wR).board.cell wR = .stone .black := by
            simpa [hturnR] using play_same_cell hlegalR
          rw [hb] at h
          cases h
        have hR : R.board.cell c = .stone .white := by
          rw [← play_other_cell hlegalR hne]
          exact h
        have hS : S.board.cell c = .stone .black := (ih c).mp hR
        have hneS : c ≠ wS := by
          intro hc
          subst c
          have hEmpty : S.board.cell wS = .empty := Position.legalMove_empty hlegalS
          rw [hEmpty] at hS
          cases hS
        rw [play_other_cell hlegalS hneS]
        exact hS
      · intro h
        have hneS : c ≠ wS := by
          intro hc
          subst c
          have hw : (play S wS).board.cell wS = .stone .white := by
            simpa [hturnS] using play_same_cell hlegalS
          rw [hw] at h
          cases h
        have hS : S.board.cell c = .stone .black := by
          rw [← play_other_cell hlegalS hneS]
          exact h
        have hR : R.board.cell c = .stone .white := (ih c).mpr hS
        have hneR : c ≠ wR := by
          intro hc
          subst c
          have hEmpty : R.board.cell wR = .empty := Position.legalMove_empty hlegalR
          rw [hEmpty] at hR
          cases hR
        rw [play_other_cell hlegalR hneR]
        exact hR

/-- 影子白棋 ⊆ 真实黑棋：σ 玩家的每一步棋都出现在真实黑方的棋子上。 -/
theorem white_subset_black {R S : Position} (hsim : ShadowSim R S) (c : Coord) :
    S.board.cell c = .stone .white → R.board.cell c = .stone .black := by
  induction hsim generalizing c with
  | start =>
      intro h
      simp [initialPosition, Position.initial, Board.empty] at h
  | @whiteStep R S w hsim hturnR hturnS hlegalR hlegalS ih =>
      intro h
      by_cases hc : c = w
      · subst c
        have hS : (play S w).board.cell w = .stone .black := by
          simpa [hturnS] using play_same_cell hlegalS
        rw [hS] at h
        cases h
      · have hS : S.board.cell c = .stone .white := by
          rw [← play_other_cell hlegalS hc]
          exact h
        have hR : R.board.cell c = .stone .black := ih c hS
        rw [play_other_cell hlegalR hc]
        exact hR
  | @blackStep R S wR wS hsim hturnR hturnS hlegalR hlegalS hsync ih =>
      intro h
      by_cases hc : c = wS
      · subst c
        rcases hsync with hsame | hocc
        · rw [hsame]
          simpa [hturnR] using play_same_cell hlegalR
        · -- wS 已是真实黑棋：落子后保持
          have hne : wS ≠ wR := by
            intro hwr
            subst wS
            have hEmptyR : R.board.cell wR = .empty := Position.legalMove_empty hlegalR
            rw [hEmptyR] at hocc
            cases hocc
          rw [play_other_cell hlegalR hne]
          exact hocc
      · have hS : S.board.cell c = .stone .white := by
          rw [← play_other_cell hlegalS hc]
          exact h
        have hR : R.board.cell c = .stone .black := ih c hS
        have hneR : c ≠ wR := by
          intro hwr
          subst c
          have hEmpty : R.board.cell wR = .empty := Position.legalMove_empty hlegalR
          rw [hEmpty] at hR
          cases hR
        rw [play_other_cell hlegalR hneR]
        exact hR

/-- 五连镜像：真实白棋成五 ↔ 影子黑棋成五。 -/
theorem white_five_iff_black_five {R S : Position} (hsim : ShadowSim R S) :
    hasAtLeastFive R.board .white ↔ hasAtLeastFive S.board .black := by
  constructor
  · rintro ⟨c, d, hcon⟩
    refine ⟨c, d, ?_⟩
    intro n
    rcases hcon n with ⟨q, hqstep, hqcell⟩
    refine ⟨q, hqstep, ?_⟩
    exact (white_iff_black hsim q).mp hqcell
  · rintro ⟨c, d, hcon⟩
    refine ⟨c, d, ?_⟩
    intro n
    rcases hcon n with ⟨q, hqstep, hqcell⟩
    refine ⟨q, hqstep, ?_⟩
    exact (white_iff_black hsim q).mpr hqcell

/-- 影子白棋成五 ⇒ 真实黑棋成五：σ 玩家的五连全部落在真实黑方的棋子上。 -/
theorem white_five_implies_black_five {R S : Position} (hsim : ShadowSim R S) :
    hasAtLeastFive S.board .white → hasAtLeastFive R.board .black := by
  rintro ⟨c, d, hcon⟩
  refine ⟨c, d, ?_⟩
  intro n
  rcases hcon n with ⟨q, hqstep, hqcell⟩
  refine ⟨q, hqstep, ?_⟩
  exact white_subset_black hsim q hqcell

end ShadowSim

/-! ## 偷换核心：影子局面在 σ 获胜树中 ⇒ 真实局面黑方阻止白胜 -/

/-- 偷换核心引理：若影子局面 `S` 与真实局面 `R` 同步，且 `S` 处于白方策略 σ 的
获胜树中，则从真实局面 `R` 出发黑方（先手）能阻止白方获胜。
沿真实局面的空格数做强归纳，对照 σ 树逐节点构造 `CanPreventWin .black`
防守树：白方回合覆盖全部合法应手，黑方回合选择保持防守的着法
（σ 指示的点已被黑方占据时改走任意合法点）。 -/
theorem steal_core (σ : Strategy .white) :
    ∀ {R S : Position}, ShadowSim R S →
      (∃ hs : Reachable S, StrategyRealizes σ S hs) → CanPreventWin .black R := by
  classical
  intro R S hsim htree
  induction hmeasure : Board.emptyCount R.board using Nat.strong_induction_on
      generalizing R S with
  | h n ih =>
    rcases htree with ⟨hs, htree⟩
    cases hterm : terminal R with
    | none =>
        -- 非终局：对照 σ 树分情况构造防守树
        cases htree with
        | terminal _ hwinS =>
            -- 影子白方已成五 ⇒ 真实黑方已成五 ⇒ R 是终局，矛盾
            have hS5 : hasAtLeastFive S.board .white :=
              Position.terminal_winner_hasAtLeastFive hwinS
            have hR5 : hasAtLeastFive R.board .black :=
              ShadowSim.white_five_implies_black_five hsim hS5
            have hRterm : terminal R = some .blackWin := by
              change Position.terminal R = some .blackWin
              simp [Position.terminal, hR5]
            rw [hterm] at hRterm
            simp at hRterm
        | choose _ htermS hturnS m hm _hagrees child =>
            -- 影子白方回合：真实黑方回合，黑方按 σ 的着法（或改走）防守
            have hturnR : R.turn = .black := by
              have ht := ShadowSim.turn_other hsim
              cases hturnR' : R.turn with
              | black => rfl
              | white =>
                  rw [hturnR'] at ht
                  simp [Player.other] at ht
                  rw [hturnS] at ht
                  cases ht
            by_cases hmR : legalMove R m
            · -- 正常情形：照搬 σ 的着法
              refine CanPreventWin.defenderMove hterm hturnR m hmR ?_
              have hsim' : ShadowSim (play R m) (play S m) :=
                ShadowSim.blackStep hsim hturnR hturnS hmR hm (Or.inl rfl)
              have hlt : Board.emptyCount (play R m).board < n := by
                change Board.emptyCount (Position.play R m).board < n
                have hdesc := Position.play_emptyCount_lt hmR
                omega
              exact ih (Board.emptyCount (play R m).board) hlt hsim'
                ⟨Position.Reachable.step hs hm, child⟩ (by rfl)
            · -- 偷换情形：σ 指示的点已被真实黑方占据，改走任意合法点
              have hmblack : R.board.cell m = .stone .black := by
                have hnotEmpty : R.board.cell m ≠ .empty := by
                  intro he
                  exact hmR ⟨Position.not_isTerminal_of_terminal_none hterm, he⟩
                cases hcell : R.board.cell m with
                | empty => exact (hnotEmpty hcell).elim
                | stone p =>
                    cases p with
                    | black => rfl
                    | white =>
                        have hSm : S.board.cell m = .stone .black :=
                          (ShadowSim.white_iff_black hsim m).mp hcell
                        have hmEmpty : S.board.cell m = .empty := Position.legalMove_empty hm
                        rw [hmEmpty] at hSm
                        cases hSm
              let f := Classical.choose (Position.exists_legalMove_of_terminal_none hterm)
              have hf : legalMove R f :=
                Classical.choose_spec (Position.exists_legalMove_of_terminal_none hterm)
              refine CanPreventWin.defenderMove hterm hturnR f hf ?_
              have hsim' : ShadowSim (play R f) (play S m) :=
                ShadowSim.blackStep hsim hturnR hturnS hf hm (Or.inr hmblack)
              have hlt : Board.emptyCount (play R f).board < n := by
                change Board.emptyCount (Position.play R f).board < n
                have hdesc := Position.play_emptyCount_lt hf
                omega
              exact ih (Board.emptyCount (play R f).board) hlt hsim'
                ⟨Position.Reachable.step hs hm, child⟩ (by rfl)
        | respond _ htermS hturnS children =>
            -- 影子黑方回合：真实白方回合，覆盖全部合法应手
            have hturnR : R.turn = .white := by
              have ht := ShadowSim.turn_other hsim
              cases hturnR' : R.turn with
              | black =>
                  rw [hturnR'] at ht
                  simp [Player.other] at ht
                  rw [hturnS] at ht
                  cases ht
              | white => rfl
            refine CanPreventWin.attackerMoves hterm hturnR ?_
            intro w hw
            have hwS : legalMove S w := by
              constructor
              · exact Position.not_isTerminal_of_terminal_none htermS
              · by_contra hne
                cases hcell : S.board.cell w with
                | empty => exact hne hcell
                | stone p =>
                    cases p with
                    | black =>
                        have hRw : R.board.cell w = .stone .white :=
                          (ShadowSim.white_iff_black hsim w).mpr hcell
                        have hwEmpty : R.board.cell w = .empty := Position.legalMove_empty hw
                        rw [hwEmpty] at hRw
                        cases hRw
                    | white =>
                        have hRw : R.board.cell w = .stone .black :=
                          ShadowSim.white_subset_black hsim w hcell
                        have hwEmpty : R.board.cell w = .empty := Position.legalMove_empty hw
                        rw [hwEmpty] at hRw
                        cases hRw
            have hsim' : ShadowSim (play R w) (play S w) :=
              ShadowSim.whiteStep hsim hturnR hturnS hw hwS
            have hlt : Board.emptyCount (play R w).board < n := by
              change Board.emptyCount (Position.play R w).board < n
              have hdesc := Position.play_emptyCount_lt hw
              omega
            exact ih (Board.emptyCount (play R w).board) hlt hsim'
              ⟨Position.Reachable.step hs hwS, children w hwS⟩ (by rfl)
    | some out =>
        -- 终局：黑胜或和棋闭合；白胜与 σ 的获胜树矛盾
        cases out with
        | blackWin =>
            exact CanPreventWin.terminal (by simpa [winner] using hterm)
        | draw =>
            exact CanPreventWin.draw hterm
        | whiteWin =>
            have htermW : Position.terminal R = some (winner .white) := by
              change terminal R = some .whiteWin
              exact hterm
            have hR5 : hasAtLeastFive R.board .white :=
              Position.terminal_winner_hasAtLeastFive htermW
            have hS5 : hasAtLeastFive S.board .black :=
              (ShadowSim.white_five_iff_black_five hsim).mp hR5
            have hSterm : terminal S = some .blackWin := by
              change Position.terminal S = some .blackWin
              simp [Position.terminal, hS5]
            cases htree with
            | terminal _ hwinS =>
                have hEq : some .blackWin = some (winner .white) := hSterm.symm.trans hwinS
                cases (Option.some.inj hEq)
            | choose _ htermS _ _ _ _ _ =>
                rw [htermS] at hSterm
                simp at hSterm
            | respond _ htermS _ _ =>
                rw [htermS] at hSterm
                simp at hSterm

/-! ## 空棋盘定理 -/

/-- 偷换策略定理：若白方（后手）存在强制获胜策略 σ，则黑方（先手）从空棋盘
出发能阻止白方获胜：黑方第一着落 c0，此后按影子对局偷换 σ。 -/
theorem steal_defends_initial (σ : Strategy .white)
    {hs : Reachable initialPosition} (hσ : StrategyRealizes σ initialPosition hs) :
    CanPreventWin .black initialPosition := by
  have hc0 : legalMove initialPosition c0 := by
    constructor
    · exact Position.initial_not_terminal
    · rfl
  refine CanPreventWin.defenderMove
    (by exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal)
    (by rfl) c0 hc0 ?_
  exact steal_core σ (R := play initialPosition c0) (S := initialPosition)
    ShadowSim.start ⟨hs, hσ⟩

/-- 策略偷换推论：白方（后手）从空棋盘不能强制获胜，即黑方至少和棋。 -/
theorem white_cannot_force_win_initial : ¬ CanForceWin initialPosition .white := by
  intro hwin
  rcases ((strategyRealizes_iff_canForceWin (s := initialPosition)
    (hs := Position.Reachable.initial)).mpr hwin) with ⟨σ, hσ⟩
  exact canPrevent_not_canForceWin (defender := .black) (steal_defends_initial σ hσ) hwin

/-- 正向定理：从 7×7 空棋盘出发，先手（黑方）能阻止白方获胜（至少和棋）。
这是纯策略级（策略偷换）证明，不依赖任何搜索证书。 -/
theorem black_can_prevent_white_initial : BlackCanPreventWhiteWin initialPosition := by
  unfold BlackCanPreventWhiteWin
  exact not_canForceWin_implies_canPreventWin (target := .white) white_cannot_force_win_initial

end Stealing

end Gomoku
