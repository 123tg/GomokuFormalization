import Gomoku.Search
import Gomoku.Bounded
import Gomoku.RuleAudit

/-!
Search-side regressions for the finite-depth reference search.

The reference search is deliberately small and untrusted.  These examples do
not claim that the 15x15 opening has been solved: they check that a normal
reachable position can produce an accepted certificate, while an opponent
immediate win is not silently treated as a Black win.  The soundness theorem
below goes through the same checker as an externally generated certificate.
-/

namespace Gomoku

def reachableImmediateDepthResult : CheckedDepthResult :=
  checkedDepthResultFor 1 auditReachableImmediatePosition .black

/- The independent bounded semantics agrees on this one-move position.  This
   is a regression comparison, not a theorem that the heuristic search is
   complete at arbitrary depths. -/
example : boundedCanForceWin 1 auditReachableImmediatePosition .black = true := by
  native_decide

/- The generated result is accepted by the local certificate checker. -/
example : reachableImmediateDepthResult.isAccepted = true := by
  native_decide

/- This is a theorem, rather than only an executable test: the accepted result
   is converted into the game-theoretic statement by the trusted bridge. -/
theorem reachableImmediateDepthResult_sound :
    CanForceWin auditReachableImmediatePosition .black := by
  have haccepted : reachableImmediateDepthResult.isAccepted = true := by
    native_decide
  cases hresult : reachableImmediateDepthResult with
  | noCandidate =>
      simp [CheckedDepthResult.isAccepted, hresult] at haccepted
  | rejected c =>
      simp [CheckedDepthResult.isAccepted, hresult] at haccepted
  | accepted c =>
      apply checkedDepthResultFor_sound
      simpa [reachableImmediateDepthResult, hresult]

/- The stateful entry point starts from an empty table, discovers a candidate,
   and returns the learned entries together with it.  The wrapper used by the
   older API is definitionally this same tree component. -/
def reachableImmediateMemoSearch : MemoSearchResult :=
  searchCandidateTreeMemoized #[] 1 auditReachableImmediatePosition .black

example :
    reachableImmediateMemoSearch.tree =
      searchCandidateTree 1 auditReachableImmediatePosition .black := by
  rfl

example : reachableImmediateMemoSearch.tree.isSome := by
  native_decide

example : 0 < reachableImmediateMemoSearch.memo.size := by
  native_decide

example :
    (memoLookup reachableImmediateMemoSearch.memo
      (searchKey 1 auditReachableImmediatePosition .black)).isSome := by
  native_decide

/- A pre-populated cache hit returns the stored result without re-running the
   search.  The cache key contains fuel, target, turn, and the full board. -/
def opponentImmediateMemo : SearchMemo :=
  #[{ key := searchKey 1 auditReachableOpponentThreatPosition .black
      result := none }]

example :
    searchCandidateTreeCached opponentImmediateMemo 1
      auditReachableOpponentThreatPosition .black = none := by
  native_decide

example :
    checkedDepthCertificateForCached opponentImmediateMemo 1
      auditReachableOpponentThreatPosition .black = none := by
  native_decide

/- A cache entry for another target cannot be reused: the target player is a
   part of the exact key. -/
def wrongTargetMemo : SearchMemo :=
  #[{ key := searchKey 1 auditReachableWinPosition .black
      result := some (.terminal auditReachableWinPosition) }]

example :
    searchCandidateTreeCached wrongTargetMemo 1
      auditReachableWinPosition .white = none := by
  native_decide

/- Remaining depth is part of the key as well.  A failed search at depth one
   must not suppress a fresh depth-two search of the same position. -/
def wrongFuelMemo : SearchMemo :=
  #[{ key := searchKey 1 auditReachableImmediatePosition .black
      result := none }]

example :
    (searchKey 1 auditReachableImmediatePosition .black =
      searchKey 2 auditReachableImmediatePosition .black) = false := by
  native_decide

example :
    (searchCandidateTreeCached wrongFuelMemo 2
      auditReachableImmediatePosition .black).isSome := by
  native_decide

/- The complete board is also part of the key.  A miss for a different
   position must run the search instead of reusing the stored failure. -/
def wrongPositionMemo : SearchMemo :=
  #[{ key := searchKey 1 auditReachableOpponentThreatPosition .black
      result := none }]

example :
    (searchCandidateTreeCached wrongPositionMemo 1
      auditReachableImmediatePosition .black).isSome := by
  native_decide

example :
    searchKey 1 auditReachableImmediatePosition .black =
      searchKey 1 auditReachableImmediatePosition .black := by
  exact (searchKey_eq_iff 1 1 auditReachableImmediatePosition
    auditReachableImmediatePosition .black .black).mpr ⟨rfl, rfl, rfl⟩

/- The stateful result includes entries learned below the root.  This checks
   that the recursive child entry is returned to the caller, not discarded. -/
example :
    (memoLookup reachableImmediateMemoSearch.memo
      (searchKey 0
        (play auditReachableImmediatePosition (2, 8))
        .black)).isSome := by
  native_decide

/- The cached checked interface has the same soundness boundary as the plain
   interface: an accepted certificate can be converted into CanForceWin, but
   an empty cache result is not a refutation. -/
def cachedReachableImmediateCertificate : Option CompactCertificate :=
  checkedDepthCertificateForCached #[] 1 auditReachableImmediatePosition .black

example : cachedReachableImmediateCertificate.isSome := by
  native_decide

theorem cachedReachableImmediateCertificate_sound :
    CanForceWin auditReachableImmediatePosition .black := by
  apply checkedDepthCertificateForCached_isSome_sound
    (memo := #[]) (fuel := 1)
    (s := auditReachableImmediatePosition) (p := .black)
  native_decide

/- A reachable position in which White is to move and has a winning endpoint.
   At depth one, the Black search must reject the branch when White chooses
   that legal winning move. -/
def opponentImmediateDepthResult : CheckedDepthResult :=
  checkedDepthResultFor 1 auditReachableOpponentThreatPosition .black

example : boundedCanForceWin 1 auditReachableOpponentThreatPosition .black = false := by
  native_decide

example : opponentImmediateDepthResult.isNoCandidate = true := by
  native_decide

example :
    checkedDepthCertificateFor 1 auditReachableOpponentThreatPosition .black =
      none := by
  native_decide

/- The diagnostic result distinguishes a search failure from a certificate
   rejection.  This theorem records the exact meaning of the no-candidate
   branch, so callers cannot read `none` as a mathematical refutation. -/
theorem opponentImmediateDepthResult_is_noCandidate :
    opponentImmediateDepthResult.isNoCandidate = true := by
  native_decide

/- A malformed candidate tree lets the audit exercise the third diagnostic
   branch directly: a tree exists, but its child is not the position obtained
   by playing the recorded move, so the trusted checker rejects it. -/
def malformedCandidateTree : CandidateTree :=
  .proverMove auditReachableImmediatePosition
    auditReachableImmediateWinningMove
    (.terminal auditReachableImmediatePosition)

def malformedCandidateResult : CheckedDepthResult :=
  checkedCandidateTreeResult auditReachableImmediatePosition .black
    malformedCandidateTree

example : malformedCandidateResult.isRejected = true := by
  native_decide

/- Even a cache hit is not trusted as a theorem.  A malformed tree stored under
   the correct key is returned by the cache adapter, then rejected by the
   certificate checker. -/
def malformedMemo : SearchMemo :=
  #[{ key := searchKey 1 auditReachableImmediatePosition .black
      result := some malformedCandidateTree }]

example :
    checkedDepthCertificateForCached malformedMemo 1
      auditReachableImmediatePosition .black = none := by
  native_decide

end Gomoku
