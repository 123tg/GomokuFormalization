import Gomoku.Defense

/-!
Pairing 策略层：把“配对策”形式化为防守策略的证据。

一个配对 `Pairing` 是互不相交的格子对集合。若满足：
* 覆盖性：每个不含白棋的长度 5 窗口都包含至少一个完整配对；
* 不变式：任一配对两格不同、黑棋至多一子，且黑棋所在配对的伙伴不是空格；
那么防守方（白棋）的策略是：黑棋落在配对 (a, b) 的 a 上且 b 为空时，白棋立即
占 b；否则白棋任意走一个合法着法。不变式保证黑棋永远无法让任一配对两格全黑，
从而永远无法在任一被覆盖的窗口成五，最终局面必为和棋或白胜。

轮次结构：完整不变式只在黑棋回合局面成立；黑棋落子后（白棋回合）仅“无黑配对”
分量成立，白棋回应（优先占伙伴格）后完整不变式恢复。本文件先给出配对结构、
覆盖性、有效性与不变式的定义及两步保持引理；soundness 定理在此基础上构造。
-/

namespace Gomoku

/-- 一个配对：互不相交的格子对数组。 -/
structure Pairing where
  pairs : Array (Coord × Coord)
  deriving DecidableEq, Repr

namespace Pairing

/-- 配对数组中的格子是否两两不同（同一格至多出现在一个配对中）。 -/
def disjoint (p : Pairing) : Bool :=
  let cells : List Coord := p.pairs.toList.flatMap (fun pair => [pair.1, pair.2])
  decide (cells.eraseDups.length = cells.length)

/-- 配对是否无退化配对（配对两格不同）。 -/
def pairProper (p : Pairing) : Bool :=
  p.pairs.all (fun pair => decide (pair.1 ≠ pair.2))

theorem pairProper_true_iff (p : Pairing) :
    pairProper p = true ↔ ∀ pair, pair ∈ p.pairs → pair.1 ≠ pair.2 := by
  unfold pairProper
  rw [Array.all_eq_true']
  constructor
  · intro h pair hp
    exact of_decide_eq_true (h pair hp)
  · intro h pair hp
    exact decide_eq_true_eq.mpr (h pair hp)

/-- 查询格子 c 的配对比邻；不在任何配对中返回 none。 -/
def partner (p : Pairing) (c : Coord) : Option Coord :=
  match p.pairs.find? (fun pair => pair.1 == c || pair.2 == c) with
  | some (a, b) => if a == c then some b else some a
  | none => none

/-- 白棋回应性质：若黑棋刚走 m 且其伙伴格为空，则白棋必须占伙伴格。 -/
def respondsTo (p : Pairing) (s : Position) (m r : Coord) : Prop :=
  match partner p m with
  | some d => (play s m).board.cell d = .empty → r = d
  | none => True

/-- 窗口 w（长度 5 的格子列表）是否包含一个完整配对。 -/
def windowCovered (p : Pairing) (w : List Coord) : Bool :=
  decide (∃ pair, pair ∈ p.pairs ∧ pair.1 ∈ w ∧ pair.2 ∈ w)

theorem windowCovered_true_iff (p : Pairing) (w : List Coord) :
    windowCovered p w = true ↔
      ∃ pair, pair ∈ p.pairs ∧ pair.1 ∈ w ∧ pair.2 ∈ w := by
  simp [windowCovered]

/-- 窗口是否已经含有白棋（这样的窗口黑棋永远无法成五，无需覆盖）。 -/
def windowHasWhite (s : Position) (w : List Coord) : Bool :=
  w.any (fun q => decide (s.board.cell q = .stone .white))

/-- 长度 5 窗口列表：从 c 沿 d 的前 5 个在界内坐标。 -/
def fiveWindow (c : Coord) (d : Direction) : List Coord :=
  lineCells c d 5

/-- 覆盖性（命题形式，可判定）：所有不含白棋的长度 5 窗口都包含一个完整配对。 -/
def CoversWindows (s : Position) (p : Pairing) : Prop :=
  ∀ c d, ¬ windowHasWhite s (fiveWindow c d) → windowCovered p (fiveWindow c d) = true

instance coversWindowsDecidable (s : Position) (p : Pairing) :
    Decidable (CoversWindows s p) := by
  unfold CoversWindows
  infer_instance

/-- 配对在当前局面下有效：无退化配对、格子两两不同且覆盖所有不含白棋的窗口。 -/
def ValidAt (s : Position) (p : Pairing) : Prop :=
  pairProper p = true ∧ disjoint p = true ∧ CoversWindows s p

instance validAtDecidable (s : Position) (p : Pairing) :
    Decidable (ValidAt s p) := by
  unfold ValidAt
  infer_instance

theorem proper_of_validAt {p : Pairing} {s : Position} (h : ValidAt s p) :
    ∀ pair, pair ∈ p.pairs → pair.1 ≠ pair.2 :=
  (pairProper_true_iff p).mp h.1

/-- 覆盖性的单调性：落子后（白棋更多）覆盖要求更弱。 -/
theorem coversWindows_mono {p : Pairing} {s t : Position}
    (hval : ValidAt s p) (hmono : ∀ c, s.board.cell c = .stone .white →
      t.board.cell c = .stone .white) :
    CoversWindows t p := by
  intro c d hnoWhiteT
  apply hval.2.2
  intro hwhiteS
  exact hnoWhiteT (by
    -- 窗口含白棋（在 s 中）→ 在 t 中也含白棋
    rcases (List.any_eq_true.mp hwhiteS) with ⟨q, hqmem, hqwhite⟩
    have hqw : s.board.cell q = .stone .white := of_decide_eq_true hqwhite
    have hqt : t.board.cell q = .stone .white := hmono q hqw
    exact List.any_eq_true.mpr ⟨q, hqmem, decide_eq_true_eq.mpr hqt⟩)

/-- 无黑配对：任一配对中黑棋至多一子（不变式的核心动态分量）。 -/
def NoBlackPair (p : Pairing) (s : Position) : Prop :=
  ∀ pair, pair ∈ p.pairs →
    ¬ (s.board.cell pair.1 = .stone .black ∧
       s.board.cell pair.2 = .stone .black)

/-- 配对不变式：任一配对两格不同、黑棋至多一子，且黑棋所在配对的伙伴不是空格。
完整不变式只在黑棋回合局面要求成立。 -/
def Invariant (p : Pairing) (s : Position) : Prop :=
  (∀ pair, pair ∈ p.pairs → pair.1 ≠ pair.2) ∧ NoBlackPair p s ∧
  (∀ pair, pair ∈ p.pairs →
    s.board.cell pair.1 = .stone .black → s.board.cell pair.2 ≠ .empty) ∧
  (∀ pair, pair ∈ p.pairs →
    s.board.cell pair.2 = .stone .black → s.board.cell pair.1 ≠ .empty)

theorem noBlackPair_of_invariant {p : Pairing} {s : Position}
    (h : Invariant p s) : NoBlackPair p s :=
  h.2.1

theorem invariant_pair_ne {p : Pairing} {s : Position}
    (h : Invariant p s) {a b : Coord} (hp : (a, b) ∈ p.pairs) :
    a ≠ b :=
  h.1 (a, b) hp

theorem invariant_black_not_both {p : Pairing} {s : Position}
    (h : Invariant p s) {a b : Coord} (hp : (a, b) ∈ p.pairs)
    (ha : s.board.cell a = .stone .black) :
    s.board.cell b ≠ .stone .black := by
  intro hb
  exact h.2.1 (a, b) hp ⟨ha, hb⟩

theorem invariant_black_partner_not_empty {p : Pairing} {s : Position}
    (h : Invariant p s) {a b : Coord} (hp : (a, b) ∈ p.pairs)
    (ha : s.board.cell a = .stone .black) :
    s.board.cell b ≠ .empty := by
  exact h.2.2.1 (a, b) hp ha

theorem invariant_sym {p : Pairing} {s : Position}
    (h : Invariant p s) {a b : Coord} (hp : (b, a) ∈ p.pairs)
    (ha : s.board.cell a = .stone .black) :
    s.board.cell b ≠ .empty := by
  exact h.2.2.2 (b, a) hp ha

/-- 黑棋落子后目标格为黑。 -/
theorem play_cell_black {s : Position} {m : Coord} (hm : legalMove s m)
    (hturn : s.turn = .black) :
    (play s m).board.cell m = .stone .black := by
  change (s.board.place m s.turn).cell m = .stone .black
  rw [hturn]
  exact Board.place_same s.board m .black

/-- 白棋落子后目标格为白。 -/
theorem play_cell_white {s : Position} {m : Coord} (hm : legalMove s m)
    (hturn : s.turn = .white) :
    (play s m).board.cell m = .stone .white := by
  change (s.board.place m s.turn).cell m = .stone .white
  rw [hturn]
  exact Board.place_same s.board m .white

/-- 白棋落子不会产生新的黑子：落子后的黑格在落子前已是黑格。 -/
theorem black_persists_under_white_move {s : Position} {m : Coord}
    (hm : legalMove s m) (hturn : s.turn = .white) {x : Coord}
    (h : (play s m).board.cell x = .stone .black) :
    s.board.cell x = .stone .black := by
  by_cases hxm : x = m
  · rw [hxm] at h
    have hcell : (play s m).board.cell m = .stone .white := play_cell_white hm hturn
    simp [hcell] at h
  · have hkeep : (play s m).board.cell x = s.board.cell x := by
      change (s.board.place m s.turn).cell x = s.board.cell x
      exact Board.place_other s.board (by simpa [hxm]) s.turn
    simpa [hkeep] using h

/-- 黑棋落子保持“无黑配对”（需要完整不变式排除黑棋占据伙伴格）。 -/
theorem noBlackPair_play_black {p : Pairing} {s : Position}
    (hinv : Invariant p s) {m : Coord} (hm : legalMove s m)
    (hturn : s.turn = .black) :
    NoBlackPair p (play s m) := by
  intro pair hp hboth
  rcases hboth with ⟨hb1, hb2⟩
  by_cases h1 : s.board.cell pair.1 = .stone .black
  · by_cases h2 : s.board.cell pair.2 = .stone .black
    · exact (hinv.2.1 pair hp ⟨h1, h2⟩).elim
    · have hpm2 : pair.2 = m := by
        by_cases hpm : pair.2 = m
        · exact hpm
        · have hkeep : (play s m).board.cell pair.2 = s.board.cell pair.2 := by
            change (s.board.place m s.turn).cell pair.2 = s.board.cell pair.2
            exact Board.place_other s.board (by simpa [hpm]) s.turn
          exact False.elim (h2 (by simpa [hkeep] using hb2))
      have hne : s.board.cell pair.2 ≠ .empty := hinv.2.2.1 pair hp h1
      exact False.elim (hne (by simpa [hpm2] using hm.2))
  · have hpm1 : pair.1 = m := by
      by_cases hpm : pair.1 = m
      · exact hpm
      · have hkeep : (play s m).board.cell pair.1 = s.board.cell pair.1 := by
          change (s.board.place m s.turn).cell pair.1 = s.board.cell pair.1
          exact Board.place_other s.board (by simpa [hpm]) s.turn
        exact False.elim (h1 (by simpa [hkeep] using hb1))
    by_cases hpm2 : pair.2 = m
    · exact (hinv.1 pair hp (hpm1.trans hpm2.symm)).elim
    · have hb2' : s.board.cell pair.2 = .stone .black := by
        have hkeep : (play s m).board.cell pair.2 = s.board.cell pair.2 := by
          change (s.board.place m s.turn).cell pair.2 = s.board.cell pair.2
          exact Board.place_other s.board (by simpa [hpm2]) s.turn
        simpa [hkeep] using hb2
      have hne : s.board.cell pair.1 ≠ .empty := hinv.2.2.2 pair hp hb2'
      rw [hpm1] at hne
      exact False.elim (hne hm.2)

/-- 白棋落子保持“无黑配对”。 -/
theorem noBlackPair_play_white {p : Pairing} {s : Position}
    (hnbp : NoBlackPair p s) {m : Coord} (hm : legalMove s m)
    (hturn : s.turn = .white) :
    NoBlackPair p (play s m) := by
  intro pair hp hboth
  rcases hboth with ⟨hb1, hb2⟩
  have hb1' : s.board.cell pair.1 = .stone .black :=
    black_persists_under_white_move hm hturn hb1
  have hb2' : s.board.cell pair.2 = .stone .black :=
    black_persists_under_white_move hm hturn hb2
  exact hnbp pair hp ⟨hb1', hb2'⟩

end Pairing

/-- 黑方五连给出一个全黑的长度 5 窗口（借助 hasAtLeastFive 的证据结构）。 -/
theorem five_implies_window_all_black {b : Board} {p : Player}
    (h : hasAtLeastFive b p) :
    ∃ c d, ∃ qs : Fin 5 → Coord,
      (∀ n : Fin 5, b.cell (qs n) = .stone p) ∧
      (∀ n : Fin 5, qs n ∈ lineCells c d 5) := by
  rcases h with ⟨c, d, hcon⟩
  refine ⟨c, d, ?_⟩
  refine ⟨fun n => Classical.choose (hcon n), ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (hcon n)).2
  · intro n
    have hspec := Classical.choose_spec (hcon n)
    exact List.mem_filterMap.mpr
      ⟨n.1, ⟨List.mem_range.mpr n.isLt, hspec.1⟩⟩

/-- 配对覆盖所有无白窗口且“无黑配对”成立时，局面不可能有黑方五连。 -/
theorem no_black_five_of_noBlackPair_and_valid {p : Pairing} {s : Position}
    (hnbp : Pairing.NoBlackPair p s) (hval : Pairing.ValidAt s p) :
    ¬ hasAtLeastFive s.board .black := by
  intro hfive
  rcases five_implies_window_all_black hfive with ⟨c, d, qs, hqblack, hqmem⟩
  have hnoWhite : ¬ Pairing.windowHasWhite s (Pairing.fiveWindow c d) := by
    intro hwhite
    rcases (List.any_eq_true.mp hwhite) with ⟨q, hqmem, hqwhite⟩
    have hqwhite' : s.board.cell q = .stone .white := of_decide_eq_true hqwhite
    rcases (List.mem_filterMap.mp hqmem) with ⟨n, hn⟩
    have hn5 : n < 5 := List.mem_range.mp hn.1
    have hspec := Classical.choose_spec (hcon ⟨n, hn5⟩)
    have hsame : qs ⟨n, hn5⟩ = q := Option.some.inj (hspec.1.symm.trans hn.2)
    have hqb : s.board.cell q = .stone .black := by
      simpa [hsame] using hqblack ⟨n, hn5⟩
    simp [hqb, hqwhite'] at *
  have hcovered := hval.2.2 c d hnoWhite
  have hpair := (Pairing.windowCovered_true_iff p (Pairing.fiveWindow c d)).mp hcovered
  rcases hpair with ⟨pair, hppair, hmem1, hmem2⟩
  rcases (List.mem_filterMap.mp hmem1) with ⟨i, hi⟩
  rcases (List.mem_filterMap.mp hmem2) with ⟨j, hj⟩
  have hi5 : i < 5 := List.mem_range.mp hi.1
  have hj5 : j < 5 := List.mem_range.mp hj.1
  have hspec1 := Classical.choose_spec (hcon ⟨i, hi5⟩)
  have hspec2 := Classical.choose_spec (hcon ⟨j, hj5⟩)
  have hq1 : s.board.cell pair.1 = .stone .black := by
    have hsame : qs ⟨i, hi5⟩ = pair.1 :=
      Option.some.inj (hspec1.1.symm.trans hi.2)
    simpa [hsame] using hqblack ⟨i, hi5⟩
  have hq2 : s.board.cell pair.2 = .stone .black := by
    have hsame : qs ⟨j, hj5⟩ = pair.2 :=
      Option.some.inj (hspec2.1.symm.trans hj.2)
    simpa [hsame] using hqblack ⟨j, hj5⟩
  exact hnbp pair hppair ⟨hq1, hq2⟩

end Gomoku
