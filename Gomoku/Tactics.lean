import Gomoku.Game

/-!
战术层：把开放三、开放四、断三、跳四和制胜点提升为带轮次、合法性与安全条件的强制胜引理。
-/

namespace Gomoku

abbrev PatternWitness := Coord × Direction
-- 用起点坐标和方向组成棋形见证。

def openThreeWitnesses (b : Board) (p : Player) : Finset PatternWitness :=
  ((Finset.univ : Finset Coord).product directions).filter
    (fun w => normalizedStraightOpenThree b p w.1 w.2)
-- 穷举并收集棋盘上玩家 p 的全部规范化直线活三见证。

def openFourWitnesses (b : Board) (p : Player) : Finset PatternWitness :=
  ((Finset.univ : Finset Coord).product directions).filter
    (fun w => normalizedStraightOpenFour b p w.1 w.2)
-- 穷举并收集棋盘上玩家 p 的全部规范化直线活四见证。

theorem mem_openThreeWitnesses (b : Board) (p : Player) (c : Coord) (d : Direction) :
    (c, d) ∈ openThreeWitnesses b p ↔ straightOpenThree b p c d := by
  classical
  cases d <;> simp [openThreeWitnesses, directions, normalizedStraightOpenThree_iff]
-- 刻画活三见证集合的成员条件，它恰好等价于相应起点和方向上的直线活三。

theorem mem_openFourWitnesses (b : Board) (p : Player) (c : Coord) (d : Direction) :
    (c, d) ∈ openFourWitnesses b p ↔ straightOpenFour b p c d := by
  classical
  cases d <;> simp [openFourWitnesses, directions, normalizedStraightOpenFour_iff]
-- 刻画活四见证集合的成员条件，它恰好等价于相应起点和方向上的直线活四。

theorem card_ge_two_iff_exists_distinct {α : Type} [DecidableEq α] (s : Finset α) :
    2 ≤ s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  constructor
  · intro h
    apply Finset.one_lt_card.mp
    omega
  · intro h
    have h' : 1 < s.card := Finset.one_lt_card.mpr h
    omega
-- 说明有限集合至少有两个元素，当且仅当其中存在两个互不相同的成员。

def WinningMoves (s : Position) (p : Player) : Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun c => s.turn = p ∧ legalMove s c ∧
      terminal (play s c) = some (winner p))
-- 收集轮到玩家 p 时所有合法且能一步结束为 p 获胜的着法。

def HasImmediateWin (s : Position) (p : Player) : Prop :=
  (WinningMoves s p).Nonempty
-- 表示玩家 p 在当前局面至少拥有一个立即获胜着法。

instance hasImmediateWinDecidable (s : Position) (p : Player) :
    Decidable (HasImmediateWin s p) := by
  unfold HasImmediateWin
  infer_instance
-- 说明立即获胜着法是否存在可以判定。

def OpponentHasImmediateWin (s : Position) (p : Player) : Prop :=
  HasImmediateWin s (Player.other p)
-- 表示玩家 p 的对手在当前局面拥有立即获胜着法。

instance opponentHasImmediateWinDecidable (s : Position) (p : Player) :
    Decidable (OpponentHasImmediateWin s p) := by
  unfold OpponentHasImmediateWin
  infer_instance
-- 说明对手是否拥有立即获胜着法可以判定。

/- `WinningCells` is independent of whose turn it is.  This is needed for a
   double threat: after Black creates two winning points, it is White's turn,
   so `WinningMoves` (which intentionally includes a turn check) would be
   empty even though the two geometric winning cells remain present. -/
def WinningCells (s : Position) (p : Player) : Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun c => s.board.cell c = .empty ∧
      hasAtLeastFive (s.board.place c p) p)
-- 收集所有几何制胜点，不要求当前轮到 p，因此可用于对手回合中的威胁分析。

def HasDoubleThreat (s : Position) (p : Player) : Prop :=
  2 ≤ (WinningCells s p).card
-- 表示玩家 p 至少有两个不同的几何制胜点。

instance winningCellsDecidable (s : Position) (p : Player) :
    DecidablePred (fun c => c ∈ WinningCells s p) := by
  intro c
  simp only [WinningCells]
  infer_instance
-- 为“坐标属于制胜点集合”提供可判定谓词实例。

instance hasDoubleThreatDecidable (s : Position) (p : Player) :
    Decidable (HasDoubleThreat s p) := by
  unfold HasDoubleThreat
  infer_instance
-- 说明双威胁条件可以通过有限制胜点集合判定。

theorem mem_winningCells_iff (s : Position) (p : Player) (c : Coord) :
    c ∈ WinningCells s p ↔
      s.board.cell c = .empty ∧ hasAtLeastFive (s.board.place c p) p := by
  simp [WinningCells]
-- 展开制胜点集合成员资格：该点为空且假设放入 p 的棋子后形成五连。

/- A straight open three is a one-ply threat to create a four, not an
   immediate five.  Keeping this set separate from `WinningCells` prevents
   the geometric pattern from being silently promoted to an immediate win. -/
def FourExtensionCells (b : Board) (p : Player) : Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun m => b.cell m = .empty ∧ hasRun (b.place m p) p 4)
-- 收集玩家 p 落子后能形成四连的全部空坐标，用于区分四威胁与立即五连。

theorem mem_fourExtensionCells_iff (b : Board) (p : Player) (m : Coord) :
    m ∈ FourExtensionCells b p ↔
      b.cell m = .empty ∧ hasRun (b.place m p) p 4 := by
  simp [FourExtensionCells]
-- 刻画四连扩展点的集合成员条件。

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
-- 证明直线活三至少有一个空端点可落子形成四连。

def OpenFourExtensionCells (b : Board) (p : Player) (c : Coord) (d : Direction) :
    Finset Coord :=
  (Finset.univ : Finset Coord).filter
    (fun m => b.cell m = .empty ∧
      straightOpenFour (b.place m p) p c d)
-- 收集能把指定起点和方向上的棋形扩展为直线活四的空坐标。

theorem mem_openFourExtensionCells_iff
    (b : Board) (p : Player) (c : Coord) (d : Direction) (m : Coord) :
    m ∈ OpenFourExtensionCells b p c d ↔
      b.cell m = .empty ∧ straightOpenFour (b.place m p) p c d := by
  simp [OpenFourExtensionCells]
-- 刻画指定直线活四扩展点集合的成员条件。

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
-- 证明直线活四至少有一个端点是下一手即可成五的制胜点。

theorem openFourExtension_has_winningCell
    {b : Board} {p : Player} {c : Coord} {d : Direction} {m : Coord}
    (hm : m ∈ OpenFourExtensionCells b p c d) :
    ∃ w, w ∈ WinningCells ⟨b.place m p, Player.other p⟩ p := by
  have hm' := (mem_openFourExtensionCells_iff b p c d m).mp hm
  rcases straightOpenFour_has_winningCell hm'.2 with ⟨w, hw⟩
  exact ⟨w, hw⟩
-- 说明完成一次活四扩展后，所得局面至少保留一个立即成五的制胜点。

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
-- 分别填补两种断三模式的内部缺口，证明断三至少能扩展成一个四连。

def HasDoubleFourThreat (s : Position) (p : Player) : Prop :=
  2 ≤ (FourExtensionCells s.board p).card
-- 表示玩家 p 至少有两个不同的四连扩展点。

instance hasDoubleFourThreatDecidable (s : Position) (p : Player) :
    Decidable (HasDoubleFourThreat s p) := by
  unfold HasDoubleFourThreat
  infer_instance
-- 说明双四威胁可以通过有限扩展点集合判定。

theorem hasDoubleFourThreat_iff_exists_distinct
    (s : Position) (p : Player) :
    HasDoubleFourThreat s p ↔
      ∃ m₁ ∈ FourExtensionCells s.board p,
        ∃ m₂ ∈ FourExtensionCells s.board p, m₁ ≠ m₂ := by
  unfold HasDoubleFourThreat
  exact card_ge_two_iff_exists_distinct _
-- 把双四威胁的基数定义改写为存在两个不同四连扩展点。

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
-- 说明在不同的原空点放置任意棋子，不会破坏已经由 p 在另一点形成的五连。

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
-- 说明面对任意单个防守坐标，双威胁中总能选出另一个未被占用的制胜点。

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
-- 证明在无对手立即胜的双威胁局面中，对手任一合法防守后仍为非终局。

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
-- 证明双制胜点可强制获胜：对手一手至多封住一点，目标方随后在另一点立即成五。

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
-- 把子局面的双威胁结论提升到落子前局面，构造己方选择节点及其获胜子树。

def ForcesWinAfter (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ CanForceWin (play s m) p
-- 表示轮到 p 时，着法 m 合法且落子后的局面可由 p 强制获胜。

def GeometricDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  let after := play s m
  2 ≤ (openThreeWitnesses after.board p).card
-- 仅从落子后的棋盘几何判断是否出现至少两个不同的直线活三见证。

def GeometricMoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop :=
  let after := play s m
  (openFourWitnesses after.board p).card = 1
-- 仅从落子后棋盘判断是否恰好形成一个直线活四见证。

def DoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ GeometricDoubleOpenThree s p m
-- 在几何双活三之外加入轮次和合法性，得到可用于游戏语义的落子谓词。

def GeometricBrokenOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  ∃ c d, brokenOpenThree s.board p c d ∧
    m ∈ OpenFourExtensionCells s.board p c d
-- 表示 m 是某个断三棋形的扩展点，落子后会形成对应方向的直线活四。

def BrokenOpenThreeMove (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ GeometricBrokenOpenThree s p m
-- 在断三几何扩展条件之外加入正确轮次和合法落子要求。

def MoveCreatesSingleOpenFour (s : Position) (p : Player) (m : Coord) : Prop :=
  s.turn = p ∧ legalMove s m ∧ GeometricMoveCreatesSingleOpenFour s p m
-- 表示玩家 p 的合法着法 m 恰好创造一个直线活四见证。

instance geometricDoubleOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (GeometricDoubleOpenThree s p m) := by
  unfold GeometricDoubleOpenThree
  infer_instance
-- 说明落子后的几何双活三条件可以判定。

theorem geometricDoubleOpenThree_iff (s : Position) (p : Player) (m : Coord) :
    GeometricDoubleOpenThree s p m ↔
      ∃ w₁ ∈ openThreeWitnesses (play s m).board p,
        ∃ w₂ ∈ openThreeWitnesses (play s m).board p, w₁ ≠ w₂ := by
  unfold GeometricDoubleOpenThree
  exact card_ge_two_iff_exists_distinct _
-- 把几何双活三的基数条件改写为存在两个不同活三见证。

instance geometricMoveCreatesSingleOpenFourDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (GeometricMoveCreatesSingleOpenFour s p m) := by
  unfold GeometricMoveCreatesSingleOpenFour
  infer_instance
-- 说明落子后恰有一个几何活四见证的条件可以判定。

instance doubleOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (DoubleOpenThree s p m) := by
  unfold DoubleOpenThree
  infer_instance
-- 说明带轮次和合法性约束的双活三落子谓词可以判定。

instance geometricBrokenOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (GeometricBrokenOpenThree s p m) := by
  unfold GeometricBrokenOpenThree
  infer_instance
-- 说明指定落子是否为某个断三的几何扩展点可以判定。

instance brokenOpenThreeMoveDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (BrokenOpenThreeMove s p m) := by
  unfold BrokenOpenThreeMove
  infer_instance
-- 说明带游戏条件的断三扩展着法谓词可以判定。

instance moveCreatesSingleOpenFourDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (MoveCreatesSingleOpenFour s p m) := by
  unfold MoveCreatesSingleOpenFour
  infer_instance
-- 说明合法着法是否恰好创造一个活四可以判定。

def SingleOpenFour (s : Position) (p : Player) : Prop :=
  (openFourWitnesses s.board p).card = 1
-- 表示当前棋盘上玩家 p 恰好有一个规范化直线活四见证。

instance singleOpenFourDecidable (s : Position) (p : Player) :
    Decidable (SingleOpenFour s p) := by
  unfold SingleOpenFour
  infer_instance
-- 说明单活四位置条件可以通过有限见证集合判定。

abbrev SingleOpenFourPosition := SingleOpenFour
-- 为单活四谓词提供强调“局面”含义的兼容别名。

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
-- 定义语义安全的双活三：排除对手立即胜，且每个合法防守后的局面仍可强制获胜。

def SafeBrokenOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  BrokenOpenThreeMove s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      CanForceWin (play (play s m) r) p
-- 定义语义安全的断三扩展：落子后非终局、对手无立即胜且全部防守后仍可获胜。

def ImmediateSafeBrokenOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  BrokenOpenThreeMove s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      HasImmediateWin (play (play s m) r) p
-- 定义更强的立即安全断三：每个对手防守后目标方都已有一步胜着。

instance immediateSafeBrokenOpenThreeDecidable (s : Position) (p : Player) (m : Coord) :
    Decidable (ImmediateSafeBrokenOpenThree s p m) := by
  unfold ImmediateSafeBrokenOpenThree
  infer_instance
-- 说明立即安全断三只含有限可执行条件，因此可以判定。

def ImmediateSafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  DoubleOpenThree s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      HasImmediateWin (play (play s m) r) p
-- 定义更强的立即安全双活三：每个合法防守后目标方都可一步获胜。

/- A non-circular, two-stage sufficient condition for a geometric double open
   three. After every legal defense `r`, the target has a legal extension `q`
   which creates two distinct immediate winning cells. -/
def StagedSafeDoubleOpenThree (s : Position) (p : Player) (m : Coord) : Prop :=
  DoubleOpenThree s p m ∧
    terminal (play s m) = none ∧
    ¬ OpponentHasImmediateWin (play s m) p ∧
    ∀ r, legalMove (play s m) r →
      ∃ q, legalMove (play (play s m) r) q ∧
        terminal (play (play (play s m) r) q) = none ∧
        ¬ HasImmediateWin (play (play (play s m) r) q) (Player.other p) ∧
        HasDoubleThreat (play (play (play s m) r) q) p

instance stagedSafeDoubleOpenThreeDecidable
    (s : Position) (p : Player) (m : Coord) :
    Decidable (StagedSafeDoubleOpenThree s p m) := by
  unfold StagedSafeDoubleOpenThree
  infer_instance

theorem not_safeDoubleOpenThree_of_opponentImmediate
    {s : Position} {p : Player} {m : Coord}
    (hopp : OpponentHasImmediateWin (play s m) p) :
    ¬ SafeDoubleOpenThree s p m := by
  intro hsafe
  exact hsafe.2.2.1 hopp
-- 说明若对手在首步后已有立即胜着，则该双活三不满足安全条件。

theorem not_immediateSafeDoubleOpenThree_of_opponentImmediate
    {s : Position} {p : Player} {m : Coord}
    (hopp : OpponentHasImmediateWin (play s m) p) :
    ¬ ImmediateSafeDoubleOpenThree s p m := by
  intro hsafe
  exact hsafe.2.2.1 hopp
-- 说明对手存在立即胜着时，更强的立即安全双活三同样不可能成立。

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
-- 证明合法断三扩展着法会在落子后的局面产生至少一个几何制胜点。

theorem immediateWin_canForceWin {s : Position} {p : Player}
    (h : HasImmediateWin s p) : CanForceWin s p := by
  classical
  rcases h with ⟨m, hm⟩
  have hm' : s.turn = p ∧ legalMove s m ∧
      terminal (play s m) = some (winner p) := by
    simpa [WinningMoves] using hm
  rcases hm' with ⟨hturn, hlegal, hwin⟩
  exact canForceWin_immediate hlegal hwin hturn
-- 把 HasImmediateWin 的有限集合见证转换为游戏语义上的 CanForceWin。

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
-- 证明黑方填入五格线中的唯一空缺后形成五连，从而得到合法的一步胜着。

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
-- 对跳四的三种内部缺口分别应用填缺定理，得到黑方的一步胜着。

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
-- 证明黑方直线活四可在开放右端补成五连，因此存在合法立即胜着。

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
-- 从唯一活四见证提取直线活四及其立即胜着，证明黑方可以强制获胜。

theorem singleOpenFour_forces_win_minimal {s : Position}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFour s .black) :
    CanForceWin s .black :=
  singleOpenFourPosition_forces_win hturn hnoterm hpattern
-- 给出单活四强制获胜定理的最小前提版本。

theorem singleOpenFour_forces_win {s : Position}
    (hturn : s.turn = .black) (hnoterm : ¬ IsTerminal s)
    (hpattern : SingleOpenFour s .black)
  (hnoWhite : ¬ HasImmediateWin s .white) :
  CanForceWin s .black := by
  have _ := hnoWhite
  exact singleOpenFour_forces_win_minimal hturn hnoterm hpattern
-- 保留带“白方无立即胜”参数的兼容接口；核心证明实际只需黑方单活四。

theorem opponent_no_immediate_win_of_not
    {s : Position} {p : Player} (h : ¬ OpponentHasImmediateWin s p) :
    ¬ HasImmediateWin s (Player.other p) := h
-- 展开 OpponentHasImmediateWin 别名，直接得到对手没有立即胜着的命题。

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
-- 按安全双活三定义直接构造己方选择节点和覆盖全部防守的对手响应节点。

theorem stagedSafeDoubleOpenThree_defense_forces_win
    {s : Position} {p : Player} {m r : Coord}
    (hstage : StagedSafeDoubleOpenThree s p m)
    (hr : legalMove (play s m) r) :
    CanForceWin (play (play s m) r) p := by
  rcases hstage with ⟨hdouble, _hchildterm, _hnoopp, hresponses⟩
  rcases hresponses r hr with ⟨q, hq, htermq, hnooppq, hthreatq⟩
  have hturn : s.turn = p := hdouble.1
  have htermr : terminal (play (play s m) r) = none :=
    Position.terminal_none_of_not_isTerminal hq.1
  have hturnr : (play (play s m) r).turn = p := by
    change s.turn.other.other = p
    rw [hturn]
    exact Player.other_other p
  have hturnq :
      (play (play (play s m) r) q).turn = Player.other p := by
    change (play (play s m) r).turn.other = p.other
    rw [hturnr]
  exact ForceWin.choose htermr hturnr q hq
    (doubleThreat_forces_win hturnq htermq hnooppq hthreatq)

theorem stagedSafeDoubleOpenThree_implies_safe
    {s : Position} {p : Player} {m : Coord}
    (hstage : StagedSafeDoubleOpenThree s p m) :
    SafeDoubleOpenThree s p m := by
  refine ⟨hstage.1, hstage.2.1, hstage.2.2.1, ?_⟩
  intro r hr
  exact stagedSafeDoubleOpenThree_defense_forces_win hstage hr

theorem stagedSafeDoubleOpenThree_forces_win
    {s : Position} {p : Player} {m : Coord}
    (hstage : StagedSafeDoubleOpenThree s p m) :
    CanForceWin s p :=
  safeDoubleOpenThree_forces_win
    (stagedSafeDoubleOpenThree_implies_safe hstage)

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
-- 按安全断三定义构造完整两层 ForceWin 树，从而得到 CanForceWin。

theorem immediateSafeBrokenOpenThree_implies_safe
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeBrokenOpenThree s p m) :
    SafeBrokenOpenThree s p m := by
  rcases hstrong with ⟨hmove, hchildterm, hnoopp, hdefenses⟩
  refine ⟨hmove, hchildterm, hnoopp, ?_⟩
  intro r hr
  exact immediateWin_canForceWin (hdefenses r hr)
-- 把每个防守后的立即胜着逐一提升为 CanForceWin，证明立即安全断三蕴含语义安全断三。

theorem immediateSafeBrokenOpenThree_forces_win
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeBrokenOpenThree s p m) :
    CanForceWin s p :=
  safeBrokenOpenThree_forces_win
    (immediateSafeBrokenOpenThree_implies_safe hstrong)
-- 由“立即安全蕴含安全”和安全断三获胜定理推出立即安全断三可强制获胜。

theorem immediateSafeDoubleOpenThree_implies_safe
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeDoubleOpenThree s p m) :
    SafeDoubleOpenThree s p m := by
  rcases hstrong with ⟨hdouble, hchildterm, hnoopp, hdefenses⟩
  refine ⟨hdouble, hchildterm, hnoopp, ?_⟩
  intro r hr
  exact immediateWin_canForceWin (hdefenses r hr)
-- 把每个防守后的立即胜着提升为 CanForceWin，证明立即安全双活三蕴含语义安全双活三。

theorem immediateSafeDoubleOpenThree_forces_win
    {s : Position} {p : Player} {m : Coord}
    (hstrong : ImmediateSafeDoubleOpenThree s p m) :
    CanForceWin s p :=
  safeDoubleOpenThree_forces_win
    (immediateSafeDoubleOpenThree_implies_safe hstrong)
-- 由安全性桥接定理推出立即安全双活三可以强制获胜。

end Gomoku
