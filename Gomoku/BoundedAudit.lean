import Gomoku.Bounded
import Gomoku.Adversarial
import Gomoku.RuleAudit

namespace Gomoku

/-!
Executable regressions for the rank-bounded game semantics.  The examples use
the two-empty-point fork from `Gomoku.Adversarial`, so they remain small enough
to evaluate during a normal build while still exercising both target and
opponent branches.
-/

example : boundedCanForceWin 0 opponentForkPosition .black = false := by
  native_decide

example : boundedCanForceWin 2 opponentForkPosition .black = true := by
  native_decide

example : boundedCanForceWin 3 opponentForkPosition .black = true := by
  apply boundedCanForceWin_mono
  native_decide

example : boundedCanForceWin 4 opponentForkPosition .black = true := by
  apply boundedCanForceWin_mono_of_le (fuel := 2) (largerFuel := 4)
  · decide
  · native_decide

/- The same small position is evaluated by both the executable bounded
   semantics and the candidate-tree search.  The former is the mathematical
   finite-depth reference; the latter is a candidate generator whose output
   still has to pass the certificate checker. -/
def opponentForkCheckedResult : CheckedDepthResult :=
  checkedDepthResultFor 2 opponentForkPosition .black

example : opponentForkCheckedResult.isAccepted = true := by
  native_decide

theorem opponentFork_checked_search_sound :
    CanForceWin opponentForkPosition .black := by
  have haccepted : opponentForkCheckedResult.isAccepted = true := by
    native_decide
  cases hresult : opponentForkCheckedResult with
  | noCandidate =>
      simp [CheckedDepthResult.isAccepted, hresult] at haccepted
  | rejected c =>
      simp [CheckedDepthResult.isAccepted, hresult] at haccepted
  | accepted c =>
      apply checkedDepthResultFor_sound
      simpa [opponentForkCheckedResult, hresult]

/- A terminal draw is rejected at every inspected depth.  This guards against
   accidentally treating a full board as a successful leaf merely because no
   further moves are available. -/
example : boundedCanForceWin 0 auditDrawPosition .black = false := by
  exact boundedCanForceWin_false_of_terminal_ne 0 auditDrawPosition .black .draw
    auditDraw_terminal (by decide)

example : boundedCanForceWin 1 auditDrawPosition .black = false := by
  exact boundedCanForceWin_false_of_terminal_ne 1 auditDrawPosition .black .draw
    auditDraw_terminal (by decide)

example : boundedCanForceWin 2 auditDrawPosition .white = false := by
  exact boundedCanForceWin_false_of_terminal_ne 2 auditDrawPosition .white .draw
    auditDraw_terminal (by decide)

/- If the opponent already has a legal immediate win, increasing the local
   fuel does not manufacture a forcing win for the target. -/
example : boundedCanForceWin 1 auditReachableOpponentThreatPosition .black = false := by
  native_decide

example : boundedCanForceWin 2 auditReachableOpponentThreatPosition .black = false := by
  native_decide

theorem opponentFork_bounded_sound :
    CanForceWin opponentForkPosition .black := by
  apply boundedCanForceWin_sound (fuel := 2)
  native_decide

theorem opponentFork_bounded_complete :
    boundedCanForceWin
      (Board.emptyCount opponentForkPosition.board + 1)
      opponentForkPosition .black = true := by
  exact canForceWin_bounded_complete opponentFork_bounded_sound

example :
    boundedCanForceWin
      (Board.emptyCount opponentForkPosition.board + 1)
      opponentForkPosition .black = true ↔
      CanForceWin opponentForkPosition .black := by
  exact boundedCanForceWin_iff_canForceWin_at_emptyCount

/- The accepted candidate certificate and the independent finite semantics
   agree at a sufficient fuel.  This is a bridge theorem regression, not a
   claim that the candidate generator is practical on the full board. -/
theorem opponentFork_checked_search_bounded :
    boundedCanForceWin 3 opponentForkPosition .black = true := by
  have hcert : checkedDepthCertificateFor 3 opponentForkPosition .black |>.isSome := by
    native_decide
  cases hresult : checkedDepthCertificateFor 3 opponentForkPosition .black with
  | none => simp [hresult] at hcert
  | some certificate =>
      apply checkedDepthCertificateFor_bounded
        (c := certificate) (hcert := by simpa [hresult])
      native_decide

theorem opponentFork_cached_search_bounded :
    boundedCanForceWin 3 opponentForkPosition .black = true := by
  have hcert : checkedDepthCertificateForCached #[] 3
      opponentForkPosition .black |>.isSome := by
    native_decide
  cases hresult : checkedDepthCertificateForCached #[] 3
      opponentForkPosition .black with
  | none => simp [hresult] at hcert
  | some certificate =>
      apply checkedDepthCertificateForCached_bounded
        (c := certificate) (hcert := by simpa [hresult])
      native_decide

/- A finite-depth `false` is only a depth result, not a refutation of the
   unbounded game proposition.  The same position is false at depth zero and
   true at its sufficient depth above. -/
example : boundedCanForceWin 0 opponentForkPosition .black = false := by
  native_decide

end Gomoku
