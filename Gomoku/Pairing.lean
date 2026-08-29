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
分量成立，白棋回应（优先占伙伴格）后完整不变式恢复。
-/

namespace Gomoku

/-- 一个配对：互不相交的格子对数组。 -/
structure Pairing where
  pairs : Array (Coord × Coord)
  deriving DecidableEq, Repr

namespace Pairing

/-- 配对数组中的格子是否两两不同：任何两个不同配对之间四格全不同。
位置化检查（O(n²)），便于证明“同一格至多出现在一个配对中”。 -/
def disjoint (p : Pairing) : Bool :=
  decide (∀ i : Fin p.pairs.size, ∀ j : Fin p.pairs.size, i ≠ j →
    p.pairs[i].1 ≠ p.pairs[j].1 ∧ p.pairs[i].1 ≠ p.pairs[j].2 ∧
    p.pairs[i].2 ≠ p.pairs[j].1 ∧ p.pairs[i].2 ≠ p.pairs[j].2)

theorem disjoint_iff {p : Pairing} :
    disjoint p = true ↔
      ∀ i j : Fin p.pairs.size, i ≠ j →
        p.pairs[i].1 ≠ p.pairs[j].1 ∧ p.pairs[i].1 ≠ p.pairs[j].2 ∧
        p.pairs[i].2 ≠ p.pairs[j].1 ∧ p.pairs[i].2 ≠ p.pairs[j].2 := by
  simp [disjoint]

/-- 两个不同配对不能共享任何格子：共享任一格子 ⟹ 同一配对。 -/
theorem pair_cells_disjoint_of_ne {p : Pairing} (hdisj : disjoint p = true)
    {a b c d : Coord} (hp1 : (a, b) ∈ p.pairs) (hp2 : (c, d) ∈ p.pairs)
    (hshare : a = c ∨ a = d ∨ b = c ∨ b = d) :
    (a, b) = (c, d) := by
  rcases (List.mem_iff_get.mp hp1.val) with ⟨i, hi⟩
  rcases (List.mem_iff_get.mp hp2.val) with ⟨j, hj⟩
  by_cases hij : i = j
  · subst hij
    rw [← hi, hj]
  · have hdi := (disjoint_iff.mp hdisj) i j hij
    rcases hshare with hac | had | hbc | hbd
    · have ha : p.pairs[i].1 = p.pairs[j].1 := by
        have h1 : p.pairs[i] = (a, b) := by simpa using hi
        have h2 : p.pairs[j] = (c, d) := by simpa using hj
        rw [h1, h2, hac]
      exact False.elim (hdi.1 ha)
    · have ha : p.pairs[i].1 = p.pairs[j].2 := by
        have h1 : p.pairs[i] = (a, b) := by simpa using hi
        have h2 : p.pairs[j] = (c, d) := by simpa using hj
        rw [h1, h2, had]
      exact False.elim (hdi.2.1 ha)
    · have ha : p.pairs[i].2 = p.pairs[j].1 := by
        have h1 : p.pairs[i] = (a, b) := by simpa using hi
        have h2 : p.pairs[j] = (c, d) := by simpa using hj
        rw [h1, h2, hbc]
      exact False.elim (hdi.2.2.1 ha)
    · have ha : p.pairs[i].2 = p.pairs[j].2 := by
        have h1 : p.pairs[i] = (a, b) := by simpa using hi
        have h2 : p.pairs[j] = (c, d) := by simpa using hj
        rw [h1, h2, hbd]
      exact False.elim (hdi.2.2.2 ha)

/-- 同一格至多出现在一个配对中：含 a 的两个配对必为同一对。 -/
theorem pair_containing_unique {p : Pairing} (hdisj : disjoint p = true)
    {a b c : Coord} (hp1 : (a, b) ∈ p.pairs) (hp2 : (a, c) ∈ p.pairs) :
    b = c := by
  rcases (List.mem_iff_get.mp hp1.val) with ⟨i, hi⟩
  rcases (List.mem_iff_get.mp hp2.val) with ⟨j, hj⟩
  by_cases hij : i = j
  · subst hij
    have hpair : (a, b) = (a, c) := by
      rw [← hi, hj]
    exact congrArg Prod.snd hpair
  · have hdi := (disjoint_iff.mp hdisj) i j hij
    have ha : p.pairs[i].1 = p.pairs[j].1 := by
      have h1 : p.pairs[i] = (a, b) := by simpa using hi
      have h2 : p.pairs[j] = (a, c) := by simpa using hj
      rw [h1, h2]
    exact False.elim (hdi.1 ha)

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

/-- 白棋回应性质：对每个含黑棋刚走 m 的配对，若其伙伴格为空，则白棋必须占伙伴格。 -/
def respondsTo (p : Pairing) (s : Position) (m r : Coord) : Prop :=
  ∀ pair, pair ∈ p.pairs →
    (pair.1 = m → (play s m).board.cell pair.2 = .empty → r = pair.2) ∧
    (pair.2 = m → (play s m).board.cell pair.1 = .empty → r = pair.1)

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

/-- 长度 5 窗口列表：从 c 沿 d 的前 5 个在界内坐标。
注意 `step` 的偏移参数是 Int，这里显式标注，避免 filterMap 域被推断成 Int。 -/
def fiveWindow (c : Coord) (d : Direction) : List Coord :=
  (List.range 5).filterMap (fun n : Nat => step c d (↑n : Int))

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

theorem invariant_empty_board (p : Pairing)
    (hproper : ∀ pair, pair ∈ p.pairs → pair.1 ≠ pair.2) :
    Invariant p initialPosition := by
  unfold Invariant
  constructor
  · exact hproper
  · constructor
    · intro pair hp hboth
      have hcell : Board.empty.cell pair.1 = .stone .black := by
        exact hboth.1
      simp at hcell
    · constructor
      · intro pair hp hblack
        have hcell : Board.empty.cell pair.1 = .stone .black := by
          exact hblack
        simp at hcell
      · intro pair hp hblack
        have hcell : Board.empty.cell pair.2 = .stone .black := by
          exact hblack
        simp at hcell

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

/-- 任意合法落子保持白格（黑棋落子不改白格；落子格原本为空，不可能已是白）。 -/
theorem white_persists_under_move {s : Position} {m : Coord}
    (hm : legalMove s m) {x : Coord}
    (h : s.board.cell x = .stone .white) :
    (play s m).board.cell x = .stone .white := by
  by_cases hxm : x = m
  · rw [hxm] at h
    exact False.elim (by simpa [h] using hm.2)
  · have hkeep : (play s m).board.cell x = s.board.cell x := by
      change (s.board.place m s.turn).cell x = s.board.cell x
      exact Board.place_other s.board (by simpa [hxm]) s.turn
    simpa [hkeep] using h

/-- 合法落子后配对仍有效（覆盖要求更弱，静态分量不变）。 -/
theorem validAt_play {p : Pairing} {s : Position} (hval : ValidAt s p)
    {m : Coord} (hm : legalMove s m) :
    ValidAt (play s m) p := by
  unfold ValidAt
  constructor
  · exact hval.1
  · constructor
    · exact hval.2.1
    · exact coversWindows_mono hval (fun c hw => white_persists_under_move hm hw)

/-- 白棋回应存在：若黑棋落子后局面未终局，则存在合法回应 r 满足 respondsTo。
有可用配对（伙伴格为空）时取伙伴格；否则任意合法着法（respondsTo 前提空洞）。 -/
theorem respondsTo_exists {p : Pairing} {s : Position} (hval : ValidAt s p)
    {m : Coord} (hm : legalMove s m)
    (htermChild : terminal (play s m) = none) :
    ∃ r, legalMove (play s m) r ∧ respondsTo p s m r := by
  by_cases hcase : ∃ pair, pair ∈ p.pairs ∧
      ((pair.1 = m ∧ (play s m).board.cell pair.2 = .empty) ∨
       (pair.2 = m ∧ (play s m).board.cell pair.1 = .empty))
  · rcases hcase with ⟨pair, hppair, hcasePair⟩
    refine ⟨if h : pair.1 = m then pair.2 else pair.1, ?_, ?_⟩
    · by_cases h1 : pair.1 = m
      · have hempty : (play s m).board.cell pair.2 = .empty := by
          rcases hcasePair with hc | hc
          · exact hc.2
          · exact False.elim (by
              have hne : pair.1 ≠ pair.2 := Pairing.proper_of_validAt hval pair hppair
              exact hne (h1.trans hc.1.symm))
        exact ⟨Position.terminal_none_iff.mp htermChild, by simpa [h1] using hempty⟩
      · have hempty : (play s m).board.cell pair.1 = .empty := by
          rcases hcasePair with hc | hc
          · exact False.elim (h1 hc.1)
          · exact hc.2
        exact ⟨Position.terminal_none_iff.mp htermChild, by simpa [h1] using hempty⟩
    · intro q hq
      constructor
      · intro hq1 hemptyQ
        by_cases hpair1 : pair.1 = m
        · have hrpair : (if h : pair.1 = m then pair.2 else pair.1) = pair.2 := by
            simp [hpair1]
          have hqq : q.2 = pair.2 := by
            have hshare : q.1 = pair.1 ∨ q.1 = pair.2 ∨ q.2 = pair.1 ∨ q.2 = pair.2 :=
              Or.inl (hq1.trans hpair1.symm)
            have hpairEq : q = pair :=
              Pairing.pair_cells_disjoint_of_ne hval.2.1 hq hppair hshare
            exact congrArg Prod.snd hpairEq
          exact hrpair.trans hqq.symm
        · have hpair2 : pair.2 = m := by
            rcases hcasePair with hc | hc
            · exact False.elim (hpair1 hc.1)
            · exact hc.1
          have hcontra : False := by
            have hshare : q.1 = pair.1 ∨ q.1 = pair.2 ∨ q.2 = pair.1 ∨ q.2 = pair.2 :=
              Or.inr (Or.inl (hq1.trans hpair2.symm))
            have hpairEq : q = pair :=
              Pairing.pair_cells_disjoint_of_ne hval.2.1 hq hppair hshare
            have hm1 : q.1 = pair.1 := congrArg Prod.fst hpairEq
            exact hpair1 (hm1.symm.trans hq1)
          exact False.elim hcontra
      · intro hq2 hemptyQ
        by_cases hpair1 : pair.1 = m
        · have hcontra : False := by
            have hshare : q.1 = pair.1 ∨ q.1 = pair.2 ∨ q.2 = pair.1 ∨ q.2 = pair.2 :=
              Or.inr (Or.inr (Or.inl (hq2.trans hpair1.symm)))
            have hpairEq : q = pair :=
              Pairing.pair_cells_disjoint_of_ne hval.2.1 hq hppair hshare
            have hne : q.1 ≠ q.2 := Pairing.proper_of_validAt hval q hq
            have hqq : q.1 = q.2 := by
              have hm1 : q.1 = pair.1 := congrArg Prod.fst hpairEq
              exact (hm1.trans hpair1).trans hq2.symm
            exact hne hqq
          exact False.elim hcontra
        · have hpair2 : pair.2 = m := by
            rcases hcasePair with hc | hc
            · exact False.elim (hpair1 hc.1)
            · exact hc.1
          have hrpair : (if h : pair.1 = m then pair.2 else pair.1) = pair.1 := by
            simp [hpair1]
          have hqq : q.1 = pair.1 := by
            have hshare : q.1 = pair.1 ∨ q.1 = pair.2 ∨ q.2 = pair.1 ∨ q.2 = pair.2 :=
              Or.inr (Or.inr (Or.inr (hq2.trans hpair2.symm)))
            have hpairEq : q = pair :=
              Pairing.pair_cells_disjoint_of_ne hval.2.1 hq hppair hshare
            exact congrArg Prod.fst hpairEq
          exact hrpair.trans hqq.symm
  · rcases Position.exists_legalMove_of_terminal_none (s := play s m) htermChild with ⟨r, hr⟩
    refine ⟨r, hr, ?_⟩
    intro q hq
    constructor
    · intro hq1 hemptyQ
      exact False.elim (hcase ⟨q, hq, Or.inl ⟨hq1, hemptyQ⟩⟩)
    · intro hq2 hemptyQ
      exact False.elim (hcase ⟨q, hq, Or.inr ⟨hq2, hemptyQ⟩⟩)

/-- 黑棋落子、白棋回应后，完整不变式恢复（黑棋回合局面）。
关键论证：新黑子 m 若在配对 (m, d) 中，则白棋回应（hresp）保证 d 非空
（d 空时白棋必占 d）；其余配对的黑子来自 s，其伙伴在 s 已非空。 -/
theorem invariant_after_black_response {p : Pairing} {s : Position}
    (hinv : Invariant p s) {m r : Coord}
    (hm : legalMove s m) (hturn : s.turn = .black)
    (hr : legalMove (play s m) r)
    (hresp : respondsTo p s m r) :
    Invariant p (play (play s m) r) := by
  unfold Invariant
  have hturn2 : (play s m).turn = .white := by
    change s.turn.other = .white
    rw [hturn, Player.other_black]
  constructor
  · intro pair hp
    exact hinv.1 pair hp
  · constructor
    · exact noBlackPair_play_white (noBlackPair_play_black hinv hm hturn)
        hr hturn2
    · constructor
      · intro pair hp hblack hpartner
        by_cases hpm1 : pair.1 = m
        · rw [hpm1] at hblack
          by_cases hpr : r = pair.2
          · let hcell := play_cell_white hr hturn2
            rw [hpr] at hpartner hcell
            simp [hcell] at hpartner
          · have hdNotEmpty : (play s m).board.cell pair.2 ≠ .empty := by
              intro hempty
              have hrespH : r = pair.2 := (hresp pair hp).1 hpm1 hempty
              exact False.elim (hpr hrespH)
            have hkeep : (play (play s m) r).board.cell pair.2 =
                (play s m).board.cell pair.2 := by
              change ((play s m).board.place r (play s m).turn).cell pair.2 =
                (play s m).board.cell pair.2
              rw [hturn2]
              exact Board.place_other (play s m).board (by intro h; exact hpr h.symm) .white
            exact hdNotEmpty (by simpa [hkeep] using hpartner)
        · by_cases hpr1 : r = pair.1
          · let hcell := play_cell_white hr hturn2
            rw [hpr1] at hblack hcell
            simp [hcell] at hblack
          · have hblackS : s.board.cell pair.1 = .stone .black := by
              have hk1 : (play s m).board.cell pair.1 = s.board.cell pair.1 := by
                change (s.board.place m s.turn).cell pair.1 = s.board.cell pair.1
                exact Board.place_other s.board (by simpa [hpm1]) s.turn
              have hk2 : (play (play s m) r).board.cell pair.1 =
                  (play s m).board.cell pair.1 := by
                change ((play s m).board.place r (play s m).turn).cell pair.1 =
                  (play s m).board.cell pair.1
                rw [hturn2]
                exact Board.place_other (play s m).board (by intro h; exact hpr1 h.symm) .white
              simpa [hk1, hk2] using hblack
            have hnbS : s.board.cell pair.2 ≠ .empty := hinv.2.2.1 pair hp hblackS
            by_cases hpm2 : pair.2 = m
            · rw [hpm2] at hnbS
              exact False.elim (hnbS hm.2)
            · by_cases hpr2 : r = pair.2
              · let hcell := play_cell_white hr hturn2
                rw [hpr2] at hpartner hcell
                simp [hcell] at hpartner
              · have hkeep : (play (play s m) r).board.cell pair.2 =
                    s.board.cell pair.2 := by
                  have hk1 : (play s m).board.cell pair.2 = s.board.cell pair.2 := by
                    change (s.board.place m s.turn).cell pair.2 = s.board.cell pair.2
                    exact Board.place_other s.board (by simpa [hpm2]) s.turn
                  have hk2 : (play (play s m) r).board.cell pair.2 =
                      (play s m).board.cell pair.2 := by
                    change ((play s m).board.place r (play s m).turn).cell pair.2 =
                      (play s m).board.cell pair.2
                    rw [hturn2]
                    exact Board.place_other (play s m).board (by intro h; exact hpr2 h.symm) .white
                  simpa [hk1, hk2]
                exact hnbS (by simpa [hkeep] using hpartner)
      · intro pair hp hblack hpartner
        by_cases hpm2 : pair.2 = m
        · rw [hpm2] at hblack
          by_cases hpr : r = pair.1
          · let hcell := play_cell_white hr hturn2
            rw [hpr] at hpartner hcell
            simp [hcell] at hpartner
          · have hdNotEmpty : (play s m).board.cell pair.1 ≠ .empty := by
              intro hempty
              have hrespH : r = pair.1 := (hresp pair hp).2 hpm2 hempty
              exact False.elim (hpr hrespH)
            have hkeep : (play (play s m) r).board.cell pair.1 =
                (play s m).board.cell pair.1 := by
              change ((play s m).board.place r (play s m).turn).cell pair.1 =
                (play s m).board.cell pair.1
              rw [hturn2]
              exact Board.place_other (play s m).board (by intro h; exact hpr h.symm) .white
            exact hdNotEmpty (by simpa [hkeep] using hpartner)
        · by_cases hpr2 : r = pair.2
          · let hcell := play_cell_white hr hturn2
            rw [hpr2] at hblack hcell
            simp [hcell] at hblack
          · have hblackS : s.board.cell pair.2 = .stone .black := by
              have hk1 : (play s m).board.cell pair.2 = s.board.cell pair.2 := by
                change (s.board.place m s.turn).cell pair.2 = s.board.cell pair.2
                exact Board.place_other s.board (by simpa [hpm2]) s.turn
              have hk2 : (play (play s m) r).board.cell pair.2 =
                  (play s m).board.cell pair.2 := by
                change ((play s m).board.place r (play s m).turn).cell pair.2 =
                  (play s m).board.cell pair.2
                rw [hturn2]
                exact Board.place_other (play s m).board (by intro h; exact hpr2 h.symm) .white
              simpa [hk1, hk2] using hblack
            have hnbS : s.board.cell pair.1 ≠ .empty := hinv.2.2.2 pair hp hblackS
            by_cases hpm1 : pair.1 = m
            · rw [hpm1] at hnbS
              exact False.elim (hnbS hm.2)
            · by_cases hpr1 : r = pair.1
              · let hcell := play_cell_white hr hturn2
                rw [hpr1] at hpartner hcell
                simp [hcell] at hpartner
              · have hkeep : (play (play s m) r).board.cell pair.1 =
                    s.board.cell pair.1 := by
                  have hk1 : (play s m).board.cell pair.1 = s.board.cell pair.1 := by
                    change (s.board.place m s.turn).cell pair.1 = s.board.cell pair.1
                    exact Board.place_other s.board (by simpa [hpm1]) s.turn
                  have hk2 : (play (play s m) r).board.cell pair.1 =
                      (play s m).board.cell pair.1 := by
                    change ((play s m).board.place r (play s m).turn).cell pair.1 =
                      (play s m).board.cell pair.1
                    rw [hturn2]
                    exact Board.place_other (play s m).board (by intro h; exact hpr1 h.symm) .white
                  simpa [hk1, hk2]
                exact hnbS (by simpa [hkeep] using hpartner)

end Pairing

/-- 黑方五连给出一个全黑的长度 5 窗口（借助 hasAtLeastFive 的证据结构）。 -/
theorem five_implies_window_all_black {b : Board} {p : Player}
    (h : hasAtLeastFive b p) :
    ∃ c d, ∃ qs : Fin 5 → Coord,
      (∀ n : Fin 5, step c d (↑n.1 : Int) = some (qs n)) ∧
      (∀ n : Fin 5, b.cell (qs n) = .stone p) ∧
      (∀ n : Fin 5, qs n ∈ Pairing.fiveWindow c d) := by
  rcases h with ⟨c, d, hcon⟩
  refine ⟨c, d, ?_⟩
  refine ⟨fun n => Classical.choose (hcon n), ?_, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (hcon n)).1
  · intro n
    exact (Classical.choose_spec (hcon n)).2
  · intro n
    have hspec := Classical.choose_spec (hcon n)
    unfold Pairing.fiveWindow
    exact List.mem_filterMap.mpr
      ⟨n.1, ⟨List.mem_range.mpr n.isLt, hspec.1⟩⟩

/-- 配对覆盖所有无白窗口且“无黑配对”成立时，局面不可能有黑方五连。 -/
theorem no_black_five_of_noBlackPair_and_valid {p : Pairing} {s : Position}
    (hnbp : Pairing.NoBlackPair p s) (hval : Pairing.ValidAt s p) :
    ¬ hasAtLeastFive s.board .black := by
  intro hfive
  rcases five_implies_window_all_black hfive with
    ⟨c, d, qs, hstep, hqblack, hqmem⟩
  have hnoWhite : ¬ Pairing.windowHasWhite s (Pairing.fiveWindow c d) := by
    intro hwhite
    rcases (List.any_eq_true.mp hwhite) with ⟨q, hqwin, hqwhite⟩
    have hqwhite' : s.board.cell q = .stone .white := of_decide_eq_true hqwhite
    rcases (List.mem_filterMap.mp hqwin) with ⟨n, hn⟩
    have hn5 : n < 5 := List.mem_range.mp hn.1
    have hsame : qs ⟨n, hn5⟩ = q :=
      Option.some.inj ((hstep ⟨n, hn5⟩).symm.trans hn.2)
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
  have hq1 : s.board.cell pair.1 = .stone .black := by
    have hsame : qs ⟨i, hi5⟩ = pair.1 :=
      Option.some.inj ((hstep ⟨i, hi5⟩).symm.trans hi.2)
    simpa [hsame] using hqblack ⟨i, hi5⟩
  have hq2 : s.board.cell pair.2 = .stone .black := by
    have hsame : qs ⟨j, hj5⟩ = pair.2 :=
      Option.some.inj ((hstep ⟨j, hj5⟩).symm.trans hj.2)
    simpa [hsame] using hqblack ⟨j, hj5⟩
  exact hnbp pair hppair ⟨hq1, hq2⟩

/-- 配对策略可靠性：若配对 p 在局面 s 有效且不变式成立（黑棋回合），
则白棋能阻止黑棋获胜。证明对空点数做良基递归：黑棋回合展开全部合法着法
（攻击方节点），白棋按 respondsTo 回应（防守方节点），终局由
“无黑配对 + 窗口覆盖”排除黑胜，只可能为和棋或白胜。 -/
noncomputable def pairingStrategySound (s : Position) (p : Pairing) :
    s.turn = .black → Pairing.Invariant p s → Pairing.ValidAt s p →
      CanPreventWin .white s
  | hturn, hinv, hval => by
      by_cases hterm : terminal s = none
      · refine CanPreventWin.attackerMoves hterm hturn ?_
        intro m hm
        have hNoBlackChild : Pairing.NoBlackPair p (play s m) :=
          Pairing.noBlackPair_play_black hinv hm hturn
        have hvalChild : Pairing.ValidAt (play s m) p := Pairing.validAt_play hval hm
        have hnoFiveChild : ¬ hasAtLeastFive (play s m).board .black :=
          no_black_five_of_noBlackPair_and_valid hNoBlackChild hvalChild
        by_cases htermChild : terminal (play s m) = none
        · rcases (Pairing.respondsTo_exists hval hm htermChild) with ⟨r, hr, hresp⟩
          have hchildInv : Pairing.Invariant p (play (play s m) r) :=
            Pairing.invariant_after_black_response hinv hm hturn hr hresp
          have hvalGrand : Pairing.ValidAt (play (play s m) r) p :=
            Pairing.validAt_play hvalChild hr
          have hturnWhite : (play s m).turn = .white := by
            change s.turn.other = .white
            rw [hturn, Player.other_black]
          have hturnGrand : (play (play s m) r).turn = .black := by
            change s.turn.other.other = .black
            rw [hturn, Player.other_black, Player.other_white]
          exact CanPreventWin.defenderMove htermChild hturnWhite r hr
            (pairingStrategySound (play (play s m) r) p hturnGrand hchildInv hvalGrand)
        · rcases (Option.ne_none_iff_exists.mp htermChild) with ⟨out, hout⟩
          cases out with
          | blackWin =>
              have hfive : hasAtLeastFive (play s m).board .black :=
                Position.terminal_winner_hasAtLeastFive hout.symm
              exact False.elim (hnoFiveChild hfive)
          | whiteWin =>
              exact CanPreventWin.terminal hout.symm
          | draw =>
              exact CanPreventWin.draw hout.symm
      · rcases (Option.ne_none_iff_exists.mp hterm) with ⟨out, hout⟩
        cases out with
        | blackWin =>
            have hfive : hasAtLeastFive s.board .black :=
              Position.terminal_winner_hasAtLeastFive hout.symm
            exact False.elim (no_black_five_of_noBlackPair_and_valid
              (Pairing.noBlackPair_of_invariant hinv) hval hfive)
        | whiteWin =>
            exact CanPreventWin.terminal hout.symm
        | draw =>
            exact CanPreventWin.draw hout.symm
termination_by Board.emptyCount s.board
decreasing_by
  all_goals
    exact lt_trans (Position.play_emptyCount_lt hr) (Position.play_emptyCount_lt hm)

/-- 配对策略可靠性（定理形式）：空棋盘初始局面 + 有效配对 ⟹ 白方阻止黑胜。 -/
theorem pairing_strategy_sound_empty (p : Pairing)
    (hproper : ∀ pair, pair ∈ p.pairs → pair.1 ≠ pair.2)
    (hval : Pairing.ValidAt initialPosition p) :
    WhiteCanPreventBlackWin initialPosition := by
  unfold WhiteCanPreventBlackWin
  exact pairingStrategySound initialPosition p rfl
    (Pairing.invariant_empty_board p hproper) hval

end Gomoku
