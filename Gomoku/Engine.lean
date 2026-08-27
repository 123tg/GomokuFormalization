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

instance : Hashable SearchKey where
  hash := engineSearchKeyHash

/- Hash lookup is followed by the standard map's exact `BEq SearchKey`
   comparison.  Hash collisions therefore affect performance, not which
   position is returned. -/
abbrev EngineMemo := Std.HashMap SearchKey (Option CandidateTree)

def emptyEngineMemo (capacity : Nat := 4096) : EngineMemo :=
  Std.HashMap.emptyWithCapacity capacity

structure EngineState where
  memo : EngineMemo := emptyEngineMemo
  nodes : Nat := 0
  cacheHits : Nat := 0
  memoStoreSkips : Nat := 0

def EngineState.stats (state : EngineState) : EngineStats :=
  { nodes := state.nodes
    cacheHits := state.cacheHits
    memoEntries := state.memo.size
    memoStoreSkips := state.memoStoreSkips }

def engineHasBudget (cfg : EngineConfig) (state : EngineState) : Bool :=
  decide (cfg.maxNodes = 0 ∨ state.nodes < cfg.maxNodes)

def engineRecordVisit (state : EngineState) : EngineState :=
  { state with nodes := state.nodes + 1 }

def engineRecordCacheHit (state : EngineState) : EngineState :=
  { state with cacheHits := state.cacheHits + 1 }

def engineMemoCanInsert (cfg : EngineConfig) (state : EngineState) : Bool :=
  decide (cfg.maxMemoEntries = 0 ∨ state.memo.size < cfg.maxMemoEntries)

def engineMemoInsert (cfg : EngineConfig) (key : SearchKey)
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

def engineLimitProverMoves (cfg : EngineConfig)
    (moves : Array Coord) : Array Coord :=
  if cfg.maxProverMoves = 0 then moves
  else (moves.toList.take cfg.maxProverMoves).toArray

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
    let key := searchKey fuel s target
    match state.memo.get? key with
    | some result =>
        { outcome :=
            match result with
            | some tree => .found tree
            | none => .notFound
          state := engineRecordCacheHit state }
    | none =>
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
              searchEngineProver cfg state depth s target
                (engineProverCandidateMoves cfg s).toList
            else
              let forest := searchEngineOpponent cfg state depth s target
                (engineCandidateMoves cfg s).toList
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
        if createsFiveFast s.board s.turn m then
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
        if createsFiveFast s.board s.turn m then
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
