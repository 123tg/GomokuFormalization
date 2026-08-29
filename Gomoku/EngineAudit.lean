import Gomoku.Engine
import Gomoku.RuleAudit
import Gomoku.Adversarial

namespace Gomoku

/-!
Independent regressions for the bounded Lean-side AND/OR engine.

The engine is an executable candidate generator.  The only theorem-producing
step below is `runCheckedEngine_sound`, which requires the certificate returned
by the engine to pass the trusted local checker.
-/

def reachableEngineConfig : EngineConfig :=
  { maxDepth := 1
    maxNodes := 10
    useThreatOrdering := true
    useForcedMovePruning := true }

def reachableEngineResult : CheckedEngineResult :=
  runCheckedEngine reachableEngineConfig
    auditReachableImmediatePosition .black

set_option linter.style.nativeDecide false in
example :
    reachableEngineResult.report.status = .found ∧
    reachableEngineResult.report.depth = some 1 ∧
    reachableEngineResult.certificate.isSome := by
  native_decide

theorem reachableEngineResult_sound :
    CanForceWin auditReachableImmediatePosition .black := by
  have hcert : reachableEngineResult.certificate.isSome = true := by
    native_decide
  cases hresult : reachableEngineResult.certificate with
  | none => simp [hresult] at hcert
  | some certificate =>
      apply runCheckedEngine_sound
      simpa [reachableEngineResult, hresult]

/- At this root White is to move and has an immediate winning endpoint.  A
   complete opponent branch therefore prevents a Black certificate. -/
def reachableEngineOpponentResult : CheckedEngineResult :=
  runCheckedEngine reachableEngineConfig
    auditReachableOpponentThreatPosition .black

set_option linter.style.nativeDecide false in
example : reachableEngineOpponentResult.certificate = none := by
  native_decide

/- A one-node budget is observable as a cutoff.  It is not interpreted as a
   mathematical statement about the position. -/
def reachableEngineCutoffConfig : EngineConfig :=
  { maxDepth := 1
    maxNodes := 1
    useThreatOrdering := true }

set_option linter.style.nativeDecide false in
example :
    (runEngine reachableEngineCutoffConfig
      auditReachableImmediatePosition .black).status = .nodeLimit := by
  native_decide

/- Engine configuration belongs to the cache key.  A failed result recorded
   under a selective configuration must not suppress a fresh search under the
   ordinary configuration, even when the board, target, and fuel are equal. -/
def selectiveFailureMemo : EngineMemo :=
  (emptyEngineMemo 1).insert
    (engineSearchKey engineSelectiveConfig 1 searchImmediatePosition .black) none

def cacheStateKey : EngineSearchKey :=
  engineSearchKey engineSmokeConfig 1 searchImmediatePosition .black

def cachedSuccessMemo : EngineMemo :=
  (emptyEngineMemo 1).insert cacheStateKey
    (some (.terminal (play searchImmediatePosition (4, 7))))

/- The outer lookup distinguishes an untouched key, a cached finite-search
   failure, and a cached candidate tree.  This prevents diagnostics from
   treating "not found" as if the position had never been searched. -/
set_option linter.style.nativeDecide false in
example : (engineCacheLookup (emptyEngineMemo 1) cacheStateKey).isMiss = true := by
  native_decide

set_option linter.style.nativeDecide false in
example : (engineCacheLookup selectiveFailureMemo
    (engineSearchKey engineSelectiveConfig 1 searchImmediatePosition .black)).isNotFound =
    true := by
  native_decide

set_option linter.style.nativeDecide false in
example : (engineCacheLookup cachedSuccessMemo cacheStateKey).isFound = true := by
  native_decide

def crossConfigEngineResult : EngineReport :=
  runEngineFrom engineSmokeConfig selectiveFailureMemo
    searchImmediatePosition .black

set_option linter.style.nativeDecide false in
example : crossConfigEngineResult.status = .found := by
  native_decide

example :
    engineSearchKey engineSelectiveConfig 1 searchImmediatePosition .black ≠
      engineSearchKey engineSmokeConfig 1 searchImmediatePosition .black := by
  intro h
  have hcfg := (engineSearchKey_eq_iff engineSelectiveConfig engineSmokeConfig
    1 1 searchImmediatePosition searchImmediatePosition .black .black).mp h
  have hne : engineSelectiveConfig ≠ engineSmokeConfig := by
    native_decide
  exact hne hcfg.1

/- The opponent side is checked on a tiny position with exactly two legal
   replies.  Both replies must be present before the certificate can pass. -/
def opponentForkEngineConfig : EngineConfig :=
  { maxDepth := 2
    maxNodes := 10
    useThreatOrdering := true
    useForcedMovePruning := true }

def opponentForkEngineResult : CheckedEngineResult :=
  runCheckedEngine opponentForkEngineConfig
    opponentForkPosition .black

set_option linter.style.nativeDecide false in
example :
    (engineCandidateMoves opponentForkEngineConfig opponentForkPosition).size = 2 := by
  native_decide

example {c : Coord} (hlegal : legalMove opponentForkPosition c) :
    c ∈ engineCandidateMoves opponentForkEngineConfig opponentForkPosition := by
  exact mem_engineCandidateMoves_of_legal opponentForkEngineConfig hlegal

set_option linter.style.nativeDecide false in
example :
    opponentForkEngineResult.report.status = .found ∧
    opponentForkEngineResult.report.depth = some 2 ∧
    opponentForkEngineResult.certificate.isSome ∧
    opponentForkEngineResult.report.stats.nodes = 6 := by
  native_decide

/- The counters are diagnostics only, but they must reflect actual work: a
   successful uncached search performs terminal classification and hands at
   least one nonempty candidate list to the recursive scanner. -/
set_option linter.style.nativeDecide false in
example : opponentForkEngineResult.report.stats.terminalChecks > 0 := by
  native_decide

set_option linter.style.nativeDecide false in
example : opponentForkEngineResult.report.stats.candidateMoves > 0 := by
  native_decide

theorem opponentForkEngineResult_sound :
    CanForceWin opponentForkPosition .black := by
  have hcert : opponentForkEngineResult.certificate.isSome = true := by
    native_decide
  cases hresult : opponentForkEngineResult.certificate with
  | none => simp [hresult] at hcert
  | some certificate =>
      apply runCheckedEngine_sound
      simpa [opponentForkEngineResult, hresult]

/- Omitting one of the two legal White replies makes the same shape an invalid
   certificate.  This is the concrete negative test for the universal branch
   requirement, rather than merely a test of the serialized node format. -/
def opponentForkMissingReplyCertificate : CompactCertificate :=
  { target := .black
    root := 0
    nodes := #[
      .opponentMoves opponentForkPosition #[((4, 7), 1)],
      .proverMove (play opponentForkPosition (4, 7)) (9, 7) 2,
      .terminal (play (play opponentForkPosition (4, 7)) (9, 7)) .blackWin
    ] }

set_option linter.style.nativeDecide false in
example :
    checkLocalCertificateAt opponentForkPosition
      opponentForkMissingReplyCertificate = false := by
  native_decide

end Gomoku
