import Gomoku.Search

namespace Gomoku

/-!
`boundedCanForceWin` is the small executable game semantics used to audit the
finite-depth search boundary.  The number passed as `fuel` is the maximum
number of further moves that may be played.  A terminal win is accepted at any
positive depth; a non-terminal node consumes one unit before inspecting its
children.

This predicate is deliberately independent of the untrusted candidate-tree
searcher.  It quantifies over exactly the legal moves supplied by
`candidateMovesFast`, whose membership theorem is proved in `Gomoku.Search`.
-/

def boundedCanForceWin : Nat → Position → Player → Bool
  | 0, s, target => decide (terminal s = some (winner target))
  | fuel + 1, s, target =>
      match terminal s with
      | some out => decide (out = winner target)
      | none =>
          if s.turn = target then
            (candidateMovesFast s target).any
              (fun m => boundedCanForceWin fuel (play s m) target)
          else
            (candidateMovesFast s (Player.other target)).all
              (fun m => boundedCanForceWin fuel (play s m) target)

theorem boundedCanForceWin_zero_iff (s : Position) (target : Player) :
    boundedCanForceWin 0 s target = true ↔
      terminal s = some (winner target) := by
  simp [boundedCanForceWin]

theorem boundedCanForceWin_succ_terminal
    (fuel : Nat) (s : Position) (target : Player) (out : Outcome)
    (hterm : terminal s = some out) :
    boundedCanForceWin (fuel + 1) s target = true ↔
      out = winner target := by
  simp [boundedCanForceWin, hterm]

theorem boundedCanForceWin_succ_nonterminal_target_iff
    (fuel : Nat) (s : Position) (target : Player)
    (hterm : terminal s = none) (hturn : s.turn = target) :
    boundedCanForceWin (fuel + 1) s target = true ↔
      ∃ m, legalMove s m ∧ boundedCanForceWin fuel (play s m) target = true := by
  constructor
  · intro h
    simp only [boundedCanForceWin, hterm, hturn, ↓reduceIte] at h
    rw [Array.any_eq_true'] at h
    rcases h with ⟨m, hm, hchild⟩
    have hm' : s.turn = target ∧ m ∈ allCoords ∧ legalMove s m :=
      (mem_candidateMovesFast_iff s target m).mp hm
    exact ⟨m, hm'.2.2, hchild⟩
  · rintro ⟨m, hm, hchild⟩
    simp only [boundedCanForceWin, hterm, hturn, ↓reduceIte]
    rw [Array.any_eq_true']
    have hmem : m ∈ candidateMovesFast s target :=
      (mem_candidateMovesFast_iff s target m).mpr ⟨hturn, mem_allCoords m, hm⟩
    exact ⟨m, hmem, hchild⟩

theorem boundedCanForceWin_succ_nonterminal_opponent_iff
    (fuel : Nat) (s : Position) (target : Player)
    (hterm : terminal s = none) (hturn : s.turn = Player.other target) :
    boundedCanForceWin (fuel + 1) s target = true ↔
      ∀ m, legalMove s m → boundedCanForceWin fuel (play s m) target = true := by
  have hneq : s.turn ≠ target := by
    intro heq
    rw [hturn] at heq
    exact (Player.other_ne_self target) heq
  constructor
  · intro h m hm
    simp only [boundedCanForceWin, hterm] at h
    rw [if_neg hneq] at h
    rw [Array.all_eq_true'] at h
    have hmem : m ∈ candidateMovesFast s (Player.other target) :=
      (mem_candidateMovesFast_iff s (Player.other target) m).mpr
        ⟨by simpa [hturn] using hturn.symm, mem_allCoords m, hm⟩
    exact h m hmem
  · intro h
    simp only [boundedCanForceWin, hterm]
    rw [if_neg hneq]
    rw [Array.all_eq_true']
    intro m hm
    have hm' : s.turn = Player.other target ∧ m ∈ allCoords ∧ legalMove s m :=
      (mem_candidateMovesFast_iff s (Player.other target) m).mp hm
    exact h m hm'.2.2

theorem boundedCanForceWin_terminal_iff
    (fuel : Nat) (s : Position) (target : Player) (out : Outcome)
    (hterm : terminal s = some out) :
    boundedCanForceWin fuel s target = true ↔ out = winner target := by
  cases fuel with
  | zero =>
      simpa [hterm] using boundedCanForceWin_zero_iff s target
  | succ fuel =>
      exact boundedCanForceWin_succ_terminal fuel s target out hterm

theorem boundedCanForceWin_false_of_terminal_ne
    (fuel : Nat) (s : Position) (target : Player) (out : Outcome)
    (hterm : terminal s = some out) (hne : out ≠ winner target) :
    boundedCanForceWin fuel s target = false := by
  cases hvalue : boundedCanForceWin fuel s target with
  | false => rfl
  | true =>
      exact (hne ((boundedCanForceWin_terminal_iff fuel s target out hterm).mp hvalue)).elim

/- Increasing the fuel cannot destroy an already discovered forcing win.  This
   is the semantic fact used by iterative-deepening drivers: a result found at
   depth `fuel` remains valid when one more ply is allowed. -/
theorem boundedCanForceWin_mono
    {fuel : Nat} {s : Position} {target : Player}
    (h : boundedCanForceWin fuel s target = true) :
    boundedCanForceWin (fuel + 1) s target = true := by
  induction fuel generalizing s target with
  | zero =>
      have hterm : terminal s = some (winner target) :=
        (boundedCanForceWin_zero_iff s target).mp h
      simp [boundedCanForceWin, hterm]
  | succ fuel ih =>
      cases hterm : terminal s with
      | some out =>
          have hout : out = winner target :=
            (boundedCanForceWin_succ_terminal fuel s target out hterm).mp h
          simp [boundedCanForceWin, hterm, hout]
      | none =>
          cases hturn : s.turn with
          | black =>
              by_cases htarget : target = .black
              · subst target
                have hex :=
                  (boundedCanForceWin_succ_nonterminal_target_iff fuel s .black
                    hterm hturn).mp h
                rcases hex with ⟨m, hm, hchild⟩
                apply (boundedCanForceWin_succ_nonterminal_target_iff (fuel + 1)
                  s .black hterm hturn).2
                exact ⟨m, hm, ih hchild⟩
              · have htarget' : target = .white := by
                  cases target <;> simp_all
                subst target
                have hturn' : s.turn = Player.other .white := by
                  simpa [hturn]
                have hall :=
                  (boundedCanForceWin_succ_nonterminal_opponent_iff fuel s .white
                    hterm hturn').mp h
                apply (boundedCanForceWin_succ_nonterminal_opponent_iff (fuel + 1)
                  s .white hterm hturn').2
                intro m hm
                exact ih (hall m hm)
          | white =>
              by_cases htarget : target = .white
              · subst target
                have hex :=
                  (boundedCanForceWin_succ_nonterminal_target_iff fuel s .white
                    hterm hturn).mp h
                rcases hex with ⟨m, hm, hchild⟩
                apply (boundedCanForceWin_succ_nonterminal_target_iff (fuel + 1)
                  s .white hterm hturn).2
                exact ⟨m, hm, ih hchild⟩
              · have htarget' : target = .black := by
                  cases target <;> simp_all
                subst target
                have hturn' : s.turn = Player.other .black := by
                  simpa [hturn]
                have hall :=
                  (boundedCanForceWin_succ_nonterminal_opponent_iff fuel s .black
                    hterm hturn').mp h
                apply (boundedCanForceWin_succ_nonterminal_opponent_iff (fuel + 1)
                  s .black hterm hturn').2
                intro m hm
                exact ih (hall m hm)

theorem boundedCanForceWin_mono_of_le
    {fuel largerFuel : Nat} {s : Position} {target : Player}
    (hle : fuel ≤ largerFuel)
  (h : boundedCanForceWin fuel s target = true) :
    boundedCanForceWin largerFuel s target = true := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simpa
  | succ extra ih =>
      simpa [Nat.add_assoc] using boundedCanForceWin_mono ih

/- A positive bounded result is a genuine game-theoretic forcing win.  This is
   the soundness direction used whenever an executable finite-depth search is
   interpreted as a theorem. -/
theorem boundedCanForceWin_sound
    {fuel : Nat} {s : Position} {target : Player}
    (h : boundedCanForceWin fuel s target = true) :
    CanForceWin s target := by
  induction fuel generalizing s with
  | zero =>
      exact canForceWin_terminal ((boundedCanForceWin_zero_iff s target).mp h)
  | succ fuel ih =>
      cases hterm : terminal s with
      | some out =>
          have hout : out = winner target :=
            (boundedCanForceWin_succ_terminal fuel s target out hterm).mp h
          exact canForceWin_terminal (by simpa [hterm, hout])
      | none =>
          cases hturn : s.turn with
          | black =>
              by_cases htarget : target = .black
              · subst target
                have hex :=
                  (boundedCanForceWin_succ_nonterminal_target_iff fuel s .black
                    hterm hturn).mp h
                rcases hex with ⟨m, hm, hchild⟩
                exact (canForceWin_target_iff hterm
                  (by simpa [hturn])).2 ⟨m, hm, ih hchild⟩
              · have htarget' : target = .white := by
                  cases target <;> simp_all
                subst target
                have hturn' : s.turn = Player.other .white := by
                  simpa [hturn]
                have hall :=
                  (boundedCanForceWin_succ_nonterminal_opponent_iff fuel s .white
                    hterm hturn').mp h
                apply (canForceWin_opponent_iff hterm hturn').2
                intro m hm
                exact ih (hall m hm)
          | white =>
              by_cases htarget : target = .white
              · subst target
                have hex :=
                  (boundedCanForceWin_succ_nonterminal_target_iff fuel s .white
                    hterm hturn).mp h
                rcases hex with ⟨m, hm, hchild⟩
                exact (canForceWin_target_iff hterm
                  (by simpa [hturn])).2 ⟨m, hm, ih hchild⟩
              · have htarget' : target = .black := by
                  cases target <;> simp_all
                subst target
                have hturn' : s.turn = Player.other .black := by
                  simpa [hturn]
                have hall :=
                  (boundedCanForceWin_succ_nonterminal_opponent_iff fuel s .black
                    hterm hturn').mp h
                apply (canForceWin_opponent_iff hterm hturn').2
                intro m hm
                exact ih (hall m hm)

/- The converse uses the exact empty-cell count as a decreasing measure.  A
   legal move changes that count by one, so a real finite forcing strategy
   cannot need more than one unit per remaining empty point (the extra unit
   lets a terminal leaf be recognized). -/
set_option maxRecDepth 100000 in
theorem canForceWin_bounded_complete
    {s : Position} {target : Player} (hwin : CanForceWin s target) :
    boundedCanForceWin (Board.emptyCount s.board + 1) s target = true := by
  induction hmeasure : Board.emptyCount s.board using Nat.strong_induction_on
      generalizing s with
  | h n ih =>
      cases hterm : terminal s with
      | some out =>
          have hout : out = winner target :=
            (canForceWin_terminal_iff hterm).mp hwin
          cases n with
          | zero => simp [boundedCanForceWin, hterm, hout]
          | succ k => simp [boundedCanForceWin, hterm, hout]
      | none =>
          have hnoterm : ¬ IsTerminal s :=
            Position.not_isTerminal_of_terminal_none hterm
          cases hturn : s.turn with
          | black =>
              by_cases htarget : target = .black
              · subst target
                have hmove := (canForceWin_target_iff hterm hturn).mp hwin
                rcases hmove with ⟨m, hm, hchild⟩
                have hdesc0 := Position.play_emptyCount_lt hm
                change Board.emptyCount (play s m).board <
                  Board.emptyCount s.board at hdesc0
                have hdesc : Board.emptyCount (play s m).board < n := by
                  simpa [hmeasure] using hdesc0
                have hsum : Board.emptyCount (play s m).board + 1 = n := by
                  have hs := Position.play_emptyCount_succ hm
                  change Board.emptyCount (play s m).board + 1 =
                    Board.emptyCount s.board at hs
                  omega
                have hchildBound := ih _ hdesc (s := play s m) hchild rfl
                rw [hsum] at hchildBound
                have hmem : m ∈ candidateMovesFast s .black :=
                  (mem_candidateMovesFast_iff s .black m).mpr
                    ⟨hturn, mem_allCoords m, hm⟩
                simp only [boundedCanForceWin, hterm, hturn, ↓reduceIte]
                rw [Array.any_eq_true']
                exact ⟨m, hmem, hchildBound⟩
              · have htarget' : target = .white := by
                  cases target <;> simp_all
                subst target
                have hall := (canForceWin_opponent_iff hterm
                  (by simpa [hturn] : s.turn = Player.other .white)).mp hwin
                have hneq : s.turn ≠ .white := by simp [hturn]
                simp only [boundedCanForceWin, hterm]
                rw [if_neg hneq]
                rw [Array.all_eq_true']
                intro m hm
                have hmlegal : legalMove s m :=
                  ((mem_candidateMovesFast_iff s (Player.other .white) m).mp hm).2.2
                have hdesc0 := Position.play_emptyCount_lt hmlegal
                change Board.emptyCount (play s m).board <
                  Board.emptyCount s.board at hdesc0
                have hdesc : Board.emptyCount (play s m).board < n := by
                  simpa [hmeasure] using hdesc0
                have hchildBound := ih _ hdesc (s := play s m)
                  (hall m hmlegal) rfl
                have hsum : Board.emptyCount (play s m).board + 1 = n := by
                  have hs := Position.play_emptyCount_succ hmlegal
                  change Board.emptyCount (play s m).board + 1 =
                    Board.emptyCount s.board at hs
                  omega
                rw [hsum] at hchildBound
                exact hchildBound
          | white =>
              by_cases htarget : target = .white
              · subst target
                have hmove := (canForceWin_target_iff hterm hturn).mp hwin
                rcases hmove with ⟨m, hm, hchild⟩
                have hdesc0 := Position.play_emptyCount_lt hm
                change Board.emptyCount (play s m).board <
                  Board.emptyCount s.board at hdesc0
                have hdesc : Board.emptyCount (play s m).board < n := by
                  simpa [hmeasure] using hdesc0
                have hsum : Board.emptyCount (play s m).board + 1 = n := by
                  have hs := Position.play_emptyCount_succ hm
                  change Board.emptyCount (play s m).board + 1 =
                    Board.emptyCount s.board at hs
                  omega
                have hchildBound := ih _ hdesc (s := play s m) hchild rfl
                rw [hsum] at hchildBound
                have hmem : m ∈ candidateMovesFast s .white :=
                  (mem_candidateMovesFast_iff s .white m).mpr
                    ⟨hturn, mem_allCoords m, hm⟩
                simp only [boundedCanForceWin, hterm, hturn, ↓reduceIte]
                rw [Array.any_eq_true']
                exact ⟨m, hmem, hchildBound⟩
              · have htarget' : target = .black := by
                  cases target <;> simp_all
                subst target
                have hall := (canForceWin_opponent_iff hterm
                  (by simpa [hturn] : s.turn = Player.other .black)).mp hwin
                have hneq : s.turn ≠ .black := by simp [hturn]
                simp only [boundedCanForceWin, hterm]
                rw [if_neg hneq]
                rw [Array.all_eq_true']
                intro m hm
                have hmlegal : legalMove s m :=
                  ((mem_candidateMovesFast_iff s (Player.other .black) m).mp hm).2.2
                have hdesc0 := Position.play_emptyCount_lt hmlegal
                change Board.emptyCount (play s m).board <
                  Board.emptyCount s.board at hdesc0
                have hdesc : Board.emptyCount (play s m).board < n := by
                  simpa [hmeasure] using hdesc0
                have hchildBound := ih _ hdesc (s := play s m)
                  (hall m hmlegal) rfl
                have hsum : Board.emptyCount (play s m).board + 1 = n := by
                  have hs := Position.play_emptyCount_succ hmlegal
                  change Board.emptyCount (play s m).board + 1 =
                    Board.emptyCount s.board at hs
                  omega
                rw [hsum] at hchildBound
                exact hchildBound

theorem boundedCanForceWin_iff_canForceWin_at_emptyCount
    {s : Position} {target : Player} :
    boundedCanForceWin (Board.emptyCount s.board + 1) s target = true ↔
      CanForceWin s target := by
  constructor
  · exact boundedCanForceWin_sound
  · exact canForceWin_bounded_complete

/- A checked candidate certificate and the independent bounded semantics agree
   once the supplied fuel is at least the theoretical number of remaining
   moves.  This theorem deliberately goes through `CanForceWin`: the candidate
   generator may use ordering, caching, or external heuristics, while the
   bounded definition remains the reference AND/OR semantics. -/
theorem checkedDepthCertificateFor_bounded
    {fuel : Nat} {s : Position} {target : Player} {c : CompactCertificate}
    (hcert : checkedDepthCertificateFor fuel s target = some c)
    (hfuel : Board.emptyCount s.board + 1 ≤ fuel) :
    boundedCanForceWin fuel s target = true := by
  have hwin : CanForceWin s target := checkedDepthCertificateFor_sound hcert
  have hbase : boundedCanForceWin (Board.emptyCount s.board + 1) s target = true :=
    canForceWin_bounded_complete hwin
  exact boundedCanForceWin_mono_of_le hfuel hbase

/- Cached candidate results have the same bridge.  The cache is not trusted as
   a proof source; `checkedDepthCertificateForCached_sound` still supplies the
   only game-theoretic premise used here. -/
theorem checkedDepthCertificateForCached_bounded
    {memo : SearchMemo} {fuel : Nat} {s : Position} {target : Player}
    {c : CompactCertificate}
    (hcert : checkedDepthCertificateForCached memo fuel s target = some c)
    (hfuel : Board.emptyCount s.board + 1 ≤ fuel) :
    boundedCanForceWin fuel s target = true := by
  have hwin : CanForceWin s target := checkedDepthCertificateForCached_sound hcert
  have hbase : boundedCanForceWin (Board.emptyCount s.board + 1) s target = true :=
    canForceWin_bounded_complete hwin
  exact boundedCanForceWin_mono_of_le hfuel hbase

end Gomoku
