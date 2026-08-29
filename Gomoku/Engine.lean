import Gomoku.Search

/-!
`Gomoku.Engine` is an executable, untrusted AND/OR searcher.  It improves the
small reference search in `Gomoku.Search` with:

* a hard node budget;
* an explicit distinction between an exhausted search and a budget cutoff;
* tactical move ordering and target-side forced-move pruning;
* an optional target-side selective width limit;
* immediate-win terminal short-circuits;
* a size-bounded transposition table carried through the recursive search;
* iterative deepening and observable search statistics.

The engine never turns its own result directly into a theorem.  A candidate
tree is compiled to `CompactCertificate` and checked by
`checkLocalCertificateAt`; `runCheckedEngine_sound` is the trusted boundary.
-/

namespace Gomoku

structure EngineConfig where
  maxDepth : Nat := 4
  /-- `0` means that the search has no node limit. -/
  maxNodes : Nat := 50000
  /-- `0` keeps every completed transposition-table entry. -/
  maxMemoEntries : Nat := 200000
  /-- Initial allocation only; `maxMemoEntries` is the hard size bound. -/
  memoCapacity : Nat := 4096
  /-- `0` tries every target-player move; a positive value is a selective
      width bound after forced tactical moves have been identified. -/
  maxProverMoves : Nat := 0
  useThreatOrdering : Bool := true
  useForcedMovePruning : Bool := true
  deriving DecidableEq, Repr

inductive EngineStatus where
  | found
  | depthLimit
  | nodeLimit
  | rejected
  deriving DecidableEq, Repr

structure EngineStats where
  nodes : Nat := 0
  cacheHits : Nat := 0
  memoEntries : Nat := 0
  memoStoreSkips : Nat := 0
  /-- Number of position-level terminal classifications performed on cache misses. -/
  terminalChecks : Nat := 0
  /-- Total number of candidate moves handed to a recursive move scanner. -/
  candidateMoves : Nat := 0
  deriving DecidableEq, Repr

def enginePlayerHash : Player → UInt64
  | .black => 1
  | .white => 2

def engineCellHash : Cell → UInt64
  | .empty => 3
  | .stone .black => 5
  | .stone .white => 7

def enginePositionHash (key : PositionKey) : UInt64 :=
  key.2.toArray.foldl
    (fun value cell => mixHash value (engineCellHash cell))
    (enginePlayerHash key.1)

def engineSearchKeyHash (key : SearchKey) : UInt64 :=
  mixHash (hash key.fuel)
    (mixHash (enginePlayerHash key.target) (enginePositionHash key.position))

/- The recursive engine is configuration-sensitive: selective width limits,
   forced-move pruning, and threat ordering can change a negative result.  Keep
   the configuration in the cache key so a `none` found under one policy cannot
   suppress a search under another policy. -/
structure EngineSearchKey where
  config : EngineConfig
  query : SearchKey
  deriving DecidableEq, Repr

def engineConfigHash (cfg : EngineConfig) : UInt64 :=
  mixHash (hash cfg.maxDepth)
    (mixHash (hash cfg.maxNodes)
      (mixHash (hash cfg.maxMemoEntries)
        (mixHash (hash cfg.memoCapacity)
          (mixHash (hash cfg.maxProverMoves)
            (mixHash (hash cfg.useThreatOrdering) (hash cfg.useForcedMovePruning))))))

def engineSearchKey (cfg : EngineConfig) (fuel : Nat) (s : Position)
    (target : Player) : EngineSearchKey :=
  { config := cfg, query := searchKey fuel s target }

theorem engineSearchKey_eq_iff (cfg₁ cfg₂ : EngineConfig)
    (fuel₁ fuel₂ : Nat) (s t : Position) (p q : Player) :
    engineSearchKey cfg₁ fuel₁ s p = engineSearchKey cfg₂ fuel₂ t q ↔
      cfg₁ = cfg₂ ∧ fuel₁ = fuel₂ ∧ p = q ∧ s = t := by
  constructor
  · intro h
    have hcfg : cfg₁ = cfg₂ := congrArg EngineSearchKey.config h
    have hquery : searchKey fuel₁ s p = searchKey fuel₂ t q :=
      congrArg EngineSearchKey.query h
    have hparts := (searchKey_eq_iff fuel₁ fuel₂ s t p q).mp hquery
    exact ⟨hcfg, hparts.1, hparts.2.1, hparts.2.2⟩
  · rintro ⟨hcfg, hfuel, htarget, hposition⟩
    cases hcfg
    have hquery := (searchKey_eq_iff fuel₁ fuel₂ s t p q).mpr
      ⟨hfuel, htarget, hposition⟩
    exact congrArg (fun query =>
      ({ config := cfg₁, query := query } : EngineSearchKey)) hquery

instance : Hashable EngineSearchKey where
  hash key := mixHash (engineConfigHash key.config) (engineSearchKeyHash key.query)

/- Hash lookup is followed by the standard map's exact `BEq EngineSearchKey`
   comparison.  Hash collisions therefore affect performance, not which
   position is returned. -/
/- The value type deliberately keeps a cached finite-search failure (`none`)
   distinct from a missing table entry (the outer `get? = none`).  The
   `EngineCacheLookup` view below exposes all three states explicitly to
   callers and tests. -/
abbrev EngineMemo := Std.HashMap EngineSearchKey (Option CandidateTree)

inductive EngineCacheLookup where
  | miss
  | notFound
  | found (tree : CandidateTree)

def EngineCacheLookup.isFound : EngineCacheLookup → Bool
  | .found _ => true
  | _ => false

def EngineCacheLookup.isNotFound : EngineCacheLookup → Bool
  | .notFound => true
  | _ => false

def EngineCacheLookup.isMiss : EngineCacheLookup → Bool
  | .miss => true
  | _ => false

def engineCacheLookup (memo : EngineMemo) (key : EngineSearchKey) :
    EngineCacheLookup :=
  match memo.get? key with
  | none => .miss
  | some none => .notFound
  | some (some tree) => .found tree

theorem engineCacheLookup_insert_found
    (memo : EngineMemo) (key : EngineSearchKey) (tree : CandidateTree) :
    engineCacheLookup (memo.insert key (some tree)) key = .found tree := by
  simp [engineCacheLookup]

theorem engineCacheLookup_insert_notFound
    (memo : EngineMemo) (key : EngineSearchKey) :
    engineCacheLookup (memo.insert key none) key = .notFound := by
  simp [engineCacheLookup]

theorem engineCacheLookup_miss_iff
    (memo : EngineMemo) (key : EngineSearchKey) :
    engineCacheLookup memo key = .miss ↔ memo[key]? = none := by
  unfold engineCacheLookup
  cases h : memo[key]? with
  | none => simp [h]
  | some result =>
      cases result <;> simp [h]

theorem engineCacheLookup_notFound_iff
    (memo : EngineMemo) (key : EngineSearchKey) :
    engineCacheLookup memo key = .notFound ↔ memo[key]? = some none := by
  unfold engineCacheLookup
  cases h : memo[key]? with
  | none => simp [h]
  | some result =>
      cases result <;> simp [h]

theorem engineCacheLookup_found_iff
    (memo : EngineMemo) (key : EngineSearchKey) (tree : CandidateTree) :
    engineCacheLookup memo key = .found tree ↔
      memo[key]? = some (some tree) := by
  unfold engineCacheLookup
  cases h : memo[key]? with
  | none => simp [engineCacheLookup, h]
  | some result =>
      cases result with
      | none => simp [engineCacheLookup, h]
      | some cachedTree =>
          simp [engineCacheLookup, h]

def emptyEngineMemo (capacity : Nat := 4096) : EngineMemo :=
  Std.HashMap.emptyWithCapacity capacity

structure EngineState where
  memo : EngineMemo := emptyEngineMemo
  nodes : Nat := 0
  cacheHits : Nat := 0
  memoStoreSkips : Nat := 0
  terminalChecks : Nat := 0
  candidateMoves : Nat := 0

def EngineState.stats (state : EngineState) : EngineStats :=
  { nodes := state.nodes
    cacheHits := state.cacheHits
    memoEntries := state.memo.size
    memoStoreSkips := state.memoStoreSkips
    terminalChecks := state.terminalChecks
    candidateMoves := state.candidateMoves }

def engineHasBudget (cfg : EngineConfig) (state : EngineState) : Bool :=
  decide (cfg.maxNodes = 0 ∨ state.nodes < cfg.maxNodes)

def engineRecordVisit (state : EngineState) : EngineState :=
  { state with nodes := state.nodes + 1 }

def engineRecordCacheHit (state : EngineState) : EngineState :=
  { state with cacheHits := state.cacheHits + 1 }

def engineRecordTerminalCheck (state : EngineState) : EngineState :=
  { state with terminalChecks := state.terminalChecks + 1 }

def engineRecordCandidateMoves (state : EngineState) (count : Nat) : EngineState :=
  { state with candidateMoves := state.candidateMoves + count }

def engineMemoCanInsert (cfg : EngineConfig) (state : EngineState) : Bool :=
  decide (cfg.maxMemoEntries = 0 ∨ state.memo.size < cfg.maxMemoEntries)

def engineMemoInsert (cfg : EngineConfig) (key : EngineSearchKey)
    (result : Option CandidateTree) (state : EngineState) : EngineState :=
  if state.memo.contains key || engineMemoCanInsert cfg state then
    { state with memo := state.memo.insert key result }
  else
    { state with memoStoreSkips := state.memoStoreSkips + 1 }

/- The existing tactical ordering is intentionally proof-oriented and builds
   a full `WinningCells` mask.  The engine can use the cheaper local detector:
   for each empty point it inspects only the five-cell windows containing that
   point.  Winning moves come first, then blocks, then quiet moves. -/
structure EngineMoveGroups where
  winning : Array Coord
  defense : Array Coord
  quiet : Array Coord

def engineMoveGroups (s : Position) : EngineMoveGroups :=
  let moves := orderedCandidateMoves s s.turn
  let winning := moves.filter (createsFiveFast s.board s.turn)
  let defense := moves.filter (fun m =>
    !(createsFiveFast s.board s.turn m) &&
      createsFiveFast s.board (Player.other s.turn) m)
  let quiet := moves.filter (fun m =>
    !(createsFiveFast s.board s.turn m) &&
      !(createsFiveFast s.board (Player.other s.turn) m))
  { winning := winning, defense := defense, quiet := quiet }

def engineTacticalCandidateMoves (s : Position) : Array Coord :=
  let groups := engineMoveGroups s
  groups.winning ++ groups.defense ++ groups.quiet

theorem mem_engineTacticalCandidateMoves_iff (s : Position) (c : Coord) :
    c ∈ engineTacticalCandidateMoves s ↔
      c ∈ orderedCandidateMoves s s.turn := by
  simp only [engineTacticalCandidateMoves, engineMoveGroups,
    Array.mem_append, Array.mem_filter]
  cases hwin : createsFiveFast s.board s.turn c <;>
    cases hdef : createsFiveFast s.board (Player.other s.turn) c <;>
    simp_all

/- Threat ordering changes only the order.  In particular, the opponent side
   is still expanded over every legal reply, as required by the certificate
   checker. -/
def engineCandidateMoves (cfg : EngineConfig) (s : Position) : Array Coord :=
  if cfg.useThreatOrdering then
    engineTacticalCandidateMoves s
  else
    immediateWinningMovesFirst s s.turn

theorem mem_engineCandidateMoves_iff (cfg : EngineConfig) (s : Position)
    (c : Coord) :
    c ∈ engineCandidateMoves cfg s ↔ c ∈ candidateMovesFast s s.turn := by
  by_cases h : cfg.useThreatOrdering
  · simp only [engineCandidateMoves, if_pos h]
    rw [mem_engineTacticalCandidateMoves_iff,
      mem_orderedCandidateMoves_iff]
  · simp only [engineCandidateMoves, if_neg h]
    rw [mem_immediateWinningMovesFirst_iff,
      mem_orderedCandidateMoves_iff]

/- Opponent nodes must retain every legal reply.  The engine's ordering only
   permutes the complete candidate array, so this theorem is the explicit
   coverage obligation used by the AND side of the search. -/
theorem mem_engineCandidateMoves_of_legal (cfg : EngineConfig)
    {s : Position} {c : Coord} (hlegal : legalMove s c) :
    c ∈ engineCandidateMoves cfg s := by
  rw [mem_engineCandidateMoves_iff, mem_candidateMovesFast_iff]
  exact ⟨rfl, mem_allCoords c, hlegal⟩

def engineLimitProverMoves (cfg : EngineConfig)
    (moves : Array Coord) : Array Coord :=
  if cfg.maxProverMoves = 0 then moves
  else (moves.toList.take cfg.maxProverMoves).toArray

theorem mem_engineLimitProverMoves_implies
    {cfg : EngineConfig} {moves : Array Coord} {m : Coord}
    (h : m ∈ engineLimitProverMoves cfg moves) :
    m ∈ moves := by
  by_cases hzero : cfg.maxProverMoves = 0
  · simpa [engineLimitProverMoves, hzero] using h
  · have htake : m ∈ moves.toList.take cfg.maxProverMoves := by
      simpa [engineLimitProverMoves, hzero] using h
    have hlist : m ∈ moves.toList := List.mem_of_mem_take htake
    simpa using hlist

/- Selective pruning is used only at target-player nodes.  Immediate wins are
   sufficient by themselves.  If the opponent already has a one-move win and
   the target has none, only cells that block such a win are searched.  At an
   opponent node the engine still calls `engineCandidateMoves`, so certificate
   coverage is never weakened. -/
def engineProverCandidateMoves (cfg : EngineConfig)
    (s : Position) : Array Coord :=
  if cfg.useForcedMovePruning then
    let groups := engineMoveGroups s
    if !groups.winning.isEmpty then
      engineLimitProverMoves cfg groups.winning
    else if !groups.defense.isEmpty then
      engineLimitProverMoves cfg groups.defense
    else
      engineLimitProverMoves cfg groups.quiet
  else
    engineLimitProverMoves cfg (engineCandidateMoves cfg s)

theorem mem_engineProverCandidateMoves_legal
    (cfg : EngineConfig) (s : Position) {m : Coord}
    (h : m ∈ engineProverCandidateMoves cfg s) :
    legalMove s m := by
  have hcandidate : m ∈ orderedCandidateMoves s s.turn := by
    unfold engineProverCandidateMoves at h
    by_cases hprune : cfg.useForcedMovePruning
    · simp only [if_pos hprune] at h
      unfold engineMoveGroups at h
      split at h
      · have hgroup := mem_engineLimitProverMoves_implies h
        exact (Array.mem_filter.mp hgroup).1
      · split at h
        · have hgroup := mem_engineLimitProverMoves_implies h
          exact (Array.mem_filter.mp hgroup).1
        · have hgroup := mem_engineLimitProverMoves_implies h
          exact (Array.mem_filter.mp hgroup).1
    · simp only [if_neg hprune] at h
      have hengine := mem_engineLimitProverMoves_implies h
      exact (mem_engineCandidateMoves_iff cfg s m).mp hengine |>
        (mem_orderedCandidateMoves_iff s s.turn m).mpr
  exact ((mem_orderedCandidateMoves_iff s s.turn m).mp hcandidate |> 
    (mem_candidateMovesFast_iff s s.turn m).mp).2.2

inductive EngineOutcome where
  | found (tree : CandidateTree)
  | notFound
  | cutoff

structure EngineStep where
  outcome : EngineOutcome
  state : EngineState

instance : Nonempty EngineStep :=
  ⟨{ outcome := .notFound, state := {} }⟩

inductive EngineForestOutcome where
  | found (children : List (Coord × CandidateTree))
  | notFound
  | cutoff

structure EngineForestStep where
  outcome : EngineForestOutcome
  state : EngineState

instance : Nonempty EngineForestStep :=
  ⟨{ outcome := .notFound, state := {} }⟩

mutual
  partial def searchWithEngine (cfg : EngineConfig) (state : EngineState)
      (fuel : Nat) (s : Position) (target : Player) : EngineStep :=
    let key := engineSearchKey cfg fuel s target
    match engineCacheLookup state.memo key with
    | .found tree =>
        { outcome := .found tree
          state := engineRecordCacheHit state }
    | .notFound =>
        { outcome := .notFound
          state := engineRecordCacheHit state }
    | .miss =>
        if engineHasBudget cfg state then
          let computed := searchWithEngineMiss cfg
            (engineRecordVisit state) fuel s target
          match computed.outcome with
          | .found tree =>
              { outcome := .found tree
                state := engineMemoInsert cfg key (some tree) computed.state }
          | .notFound =>
              { outcome := .notFound
                state := engineMemoInsert cfg key none computed.state }
          | .cutoff => computed
        else
          { outcome := .cutoff, state := state }

  partial def searchWithEngineMiss (cfg : EngineConfig) (state : EngineState)
      (fuel : Nat) (s : Position) (target : Player) : EngineStep :=
    let state := engineRecordTerminalCheck state
    match terminal s with
    | some out =>
        if out = winner target then
          { outcome := .found (.terminal s), state := state }
        else
          { outcome := .notFound, state := state }
    | none =>
        match fuel with
        | 0 =>
            { outcome := .notFound, state := state }
        | depth + 1 =>
            if s.turn = target then
              let moves := engineProverCandidateMoves cfg s
              searchEngineProver cfg (engineRecordCandidateMoves state moves.size)
                depth s target moves.toList
            else
              let moves := engineCandidateMoves cfg s
              let forest := searchEngineOpponent cfg
                (engineRecordCandidateMoves state moves.size) depth s target moves.toList
              match forest.outcome with
              | .found children =>
                  { outcome := .found (.opponentMoves s children)
                    state := forest.state }
              | .notFound =>
                  { outcome := .notFound, state := forest.state }
              | .cutoff =>
                  { outcome := .cutoff, state := forest.state }

  partial def searchEngineProver (cfg : EngineConfig) (state : EngineState)
      (depth : Nat) (s : Position) (target : Player) :
      List Coord → EngineStep
    | [] =>
        { outcome := .notFound, state := state }
    | m :: rest =>
        if terminalAfterMoveFast s m = some (winner s.turn) then
          { outcome := .found (.proverMove s m (.terminal (play s m)))
            state := state }
        else
          let child := searchWithEngine cfg state depth (play s m) target
          match child.outcome with
          | .found subtree =>
              { outcome := .found (.proverMove s m subtree)
                state := child.state }
          | .notFound =>
              searchEngineProver cfg child.state depth s target rest
          | .cutoff => child

  partial def searchEngineOpponent (cfg : EngineConfig) (state : EngineState)
      (depth : Nat) (s : Position) (target : Player) :
      List Coord → EngineForestStep
    | [] =>
        { outcome := .found [], state := state }
    | m :: rest =>
        if terminalAfterMoveFast s m = some (winner s.turn) then
          { outcome := .notFound, state := state }
        else
          let child := searchWithEngine cfg state depth (play s m) target
          match child.outcome with
          | .found subtree =>
              let remaining := searchEngineOpponent cfg child.state depth s target rest
              match remaining.outcome with
              | .found children =>
                  { outcome := .found ((m, subtree) :: children)
                    state := remaining.state }
              | .notFound =>
                  { outcome := .notFound, state := remaining.state }
              | .cutoff =>
                  { outcome := .cutoff, state := remaining.state }
          | .notFound =>
              { outcome := .notFound, state := child.state }
          | .cutoff =>
              { outcome := .cutoff, state := child.state }
end

structure EngineReport where
  tree : Option CandidateTree
  depth : Option Nat
  status : EngineStatus
  state : EngineState

def EngineReport.stats (report : EngineReport) : EngineStats :=
  report.state.stats

def runEngineDepths (cfg : EngineConfig) (s : Position) (target : Player) :
    EngineState → Nat → Nat → EngineReport
  | state, depth, 0 =>
      let step := searchWithEngine cfg state depth s target
      match step.outcome with
      | .found tree =>
          { tree := some tree, depth := some depth
            status := .found, state := step.state }
      | .notFound =>
          { tree := none, depth := none
            status := .depthLimit, state := step.state }
      | .cutoff =>
          { tree := none, depth := none
            status := .nodeLimit, state := step.state }
  | state, depth, remaining + 1 =>
      let step := searchWithEngine cfg state depth s target
      match step.outcome with
      | .found tree =>
          { tree := some tree, depth := some depth
            status := .found, state := step.state }
      | .notFound =>
          runEngineDepths cfg s target step.state (depth + 1) remaining
      | .cutoff =>
          { tree := none, depth := none
            status := .nodeLimit, state := step.state }

def runEngineFrom (cfg : EngineConfig) (memo : EngineMemo)
    (s : Position) (target : Player) : EngineReport :=
  runEngineDepths cfg s target { memo := memo } 0 cfg.maxDepth

def runEngine (cfg : EngineConfig) (s : Position)
    (target : Player) : EngineReport :=
  runEngineFrom cfg (emptyEngineMemo cfg.memoCapacity) s target

structure CheckedEngineResult where
  report : EngineReport
  certificate : Option CompactCertificate

def checkEngineReport (s : Position) (target : Player)
    (report : EngineReport) : CheckedEngineResult :=
  match report.tree with
  | none =>
      { report := report, certificate := none }
  | some tree =>
      if checkLocalCertificateAt s (candidateTreeCertificate target tree) then
        { report := report
          certificate := some (candidateTreeCertificate target tree) }
      else
        { report := { report with status := .rejected }, certificate := none }

theorem checkEngineReport_sound {s : Position} {target : Player}
    {report : EngineReport} {c : CompactCertificate}
    (h : (checkEngineReport s target report).certificate = some c) :
    CanForceWin s target := by
  unfold checkEngineReport at h
  split at h
  · simp at h
  · rename_i tree htree
    split at h
    · rename_i hchecked
      have hc : c = candidateTreeCertificate target tree := by
        simpa using h.symm
      subst c
      exact local_certificate_at_sound s
        (candidateTreeCertificate target tree) hchecked
    · simp at h

def runCheckedEngine (cfg : EngineConfig) (s : Position)
    (target : Player) : CheckedEngineResult :=
  checkEngineReport s target (runEngine cfg s target)

theorem runCheckedEngine_sound {cfg : EngineConfig} {s : Position}
    {target : Player} {c : CompactCertificate}
    (h : (runCheckedEngine cfg s target).certificate = some c) :
    CanForceWin s target := by
  exact checkEngineReport_sound
    (report := runEngine cfg s target) h

/- Small executable regressions.  They intentionally use a local tactical
   position; a complete 15x15 opening search is not part of a regular build. -/
def engineSmokeConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 2, useThreatOrdering := true }

def engineSmokeResult : CheckedEngineResult :=
  runCheckedEngine engineSmokeConfig searchImmediatePosition .black

def engineCutoffConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 1, useThreatOrdering := true }

def engineSelectiveConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 2, maxProverMoves := 1
    useThreatOrdering := true, useForcedMovePruning := true }

def engineBoundedMemoConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 2, maxMemoEntries := 1
    useThreatOrdering := true }

def engineBoundedMemoResult : EngineReport :=
  runEngine engineBoundedMemoConfig searchImmediatePosition .black

def engineDefensePosition : Position :=
  ⟨searchImmediateBoard, .white⟩

def engineCachedSmokeResult : EngineReport :=
  runEngineFrom engineSmokeConfig engineSmokeResult.report.state.memo
    searchImmediatePosition .black

set_option linter.style.nativeDecide false in
example :
    engineSmokeResult.report.status = .found ∧
    engineSmokeResult.report.depth = some 1 ∧
    engineSmokeResult.certificate.isSome ∧
    engineSmokeResult.report.stats.nodes = 2 ∧
    (runEngine engineCutoffConfig searchImmediatePosition .black).status =
      .nodeLimit ∧
    (engineProverCandidateMoves engineSelectiveConfig
      searchImmediatePosition).size = 1 ∧
    (engineProverCandidateMoves engineSelectiveConfig
      searchImmediatePosition)[0]? = some ((4, 7) : Coord) ∧
    (engineProverCandidateMoves engineSmokeConfig
      engineDefensePosition).size = 2 ∧
    ((4, 7) : Coord) ∈
      engineProverCandidateMoves engineSmokeConfig engineDefensePosition ∧
    ((9, 7) : Coord) ∈
      engineProverCandidateMoves engineSmokeConfig engineDefensePosition ∧
    (engineCandidateMoves engineSmokeConfig engineDefensePosition).size = 221 ∧
    engineBoundedMemoResult.status = .found ∧
    engineBoundedMemoResult.stats.memoEntries = 1 ∧
    engineBoundedMemoResult.stats.memoStoreSkips = 1 ∧
    engineCachedSmokeResult.status = .found ∧
    engineCachedSmokeResult.stats.nodes = 0 ∧
    engineCachedSmokeResult.stats.cacheHits = 2 := by
  native_decide

example {c : CompactCertificate}
    (h : engineSmokeResult.certificate = some c) :
    CanForceWin searchImmediatePosition .black := by
  exact runCheckedEngine_sound h

end Gomoku
