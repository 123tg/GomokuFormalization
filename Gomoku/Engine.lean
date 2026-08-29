import Gomoku.Search

/-!
`Gomoku.Engine` is an executable, untrusted AND/OR searcher.  It improves the
small reference search in `Gomoku.Search` with:

* a hard node budget;
* an explicit distinction between an exhausted search and a budget cutoff;
* tactical move ordering and target-side forced-move pruning;
* an optional target-side selective width limit;
* immediate-win terminal short-circuits;
* a size-bounded transposition table with incrementally updated bitboard keys;
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
-- 汇总引擎的深度、节点、换位表、选择性宽度与战术启发式配置。

inductive EngineStatus where
  | found
  | depthLimit
  | nodeLimit
  | rejected
  deriving DecidableEq, Repr
-- 区分搜索成功、深度不足、节点预算耗尽以及候选证书被检查器拒绝四种结束状态。

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
-- 记录节点、缓存、终局判定与递归扫描候选数，用于定位搜索时间和空间瓶颈。

def enginePlayerHash : Player → UInt64
  | .black => 1
  | .white => 2
-- 为两名玩家分配不同的 64 位基础哈希值。

structure EngineBitboard where
  word0 : UInt64 := 0
  word1 : UInt64 := 0
  word2 : UInt64 := 0
  word3 : UInt64 := 0
  deriving DecidableEq, Repr
-- 用四个 64 位字保存一个玩家在 49 个坐标上的占位信息；迁移阶段暂不重构既有键结构。

def EngineBitboard.insert (bits : EngineBitboard) (index : Nat) : EngineBitboard :=
  let mask := (1 : UInt64) <<< UInt64.ofNat (index % 64)
  match index / 64 with
  | 0 => { bits with word0 := bits.word0 ||| mask }
  | 1 => { bits with word1 := bits.word1 ||| mask }
  | 2 => { bits with word2 := bits.word2 ||| mask }
  | 3 => { bits with word3 := bits.word3 ||| mask }
  | _ => bits
-- 按行主序索引设置对应 64 位分块中的占位位；合法棋盘索引只会落入前四块。

structure EnginePositionKey where
  turn : Player
  black : EngineBitboard := {}
  white : EngineBitboard := {}
  deriving DecidableEq, Repr
-- 用轮次和双方各四个 64 位字保存完整 49 格局面，替代换位表中的对象向量。

def enginePositionKey (s : Position) : EnginePositionKey :=
  allCoords.foldl (fun key c =>
    let index := (coordIndex c).1
    match s.board.cell c with
    | .empty => key
    | .stone .black => { key with black := key.black.insert index }
    | .stone .white => { key with white := key.white.insert index })
    { turn := s.turn }
-- 初次进入搜索时扫描棋盘一次，把函数式棋盘压缩为精确的双方 bitboard 键。

def EnginePositionKey.play (key : EnginePositionKey) (m : Coord) : EnginePositionKey :=
  let index := (coordIndex m).1
  match key.turn with
  | .black =>
      { turn := .white, black := key.black.insert index, white := key.white }
  | .white =>
      { turn := .black, black := key.black, white := key.white.insert index }
-- 对合法落子增量设置当前玩家占位位并切换轮次，避免每个递归节点重新扫描 49 个格子。

structure EngineSearchKey where
  config : EngineConfig
  fuel : Nat
  target : Player
  position : EnginePositionKey
  deriving DecidableEq, Repr
-- 把搜索配置、剩余深度、目标玩家和紧凑局面组合为 Lean 引擎换位表键。

def engineSearchKey (cfg : EngineConfig) (fuel : Nat) (s : Position)
    (target : Player) : EngineSearchKey :=
  { config := cfg, fuel := fuel, target := target, position := enginePositionKey s }
-- 为外部调用者构造完整缓存键；递归搜索则直接复用增量紧凑局面。

theorem engineSearchKey_eq_iff (cfg₁ cfg₂ : EngineConfig)
    (fuel₁ fuel₂ : Nat) (s t : Position) (p q : Player) :
    engineSearchKey cfg₁ fuel₁ s p = engineSearchKey cfg₂ fuel₂ t q ↔
      cfg₁ = cfg₂ ∧ fuel₁ = fuel₂ ∧ p = q ∧
        enginePositionKey s = enginePositionKey t := by
  simp only [engineSearchKey, EngineSearchKey.mk.injEq]
-- 缓存键相等必须同时保持配置、深度、目标与 bitboard 局面相等。

def engineBitboardHash (bits : EngineBitboard) : UInt64 :=
  mixHash (mixHash bits.word0 bits.word1) (mixHash bits.word2 bits.word3)
-- 混合四个分块，为单方 bitboard 计算哈希值。

def enginePositionHash (key : EnginePositionKey) : UInt64 :=
  mixHash (enginePlayerHash key.turn)
    (mixHash (engineBitboardHash key.black) (engineBitboardHash key.white))
-- 综合轮次和双方 bitboard 计算紧凑局面哈希。

def engineConfigHash (cfg : EngineConfig) : UInt64 :=
  mixHash (hash cfg.maxDepth)
    (mixHash (hash cfg.maxNodes)
      (mixHash (hash cfg.maxMemoEntries)
        (mixHash (hash cfg.memoCapacity)
          (mixHash (hash cfg.maxProverMoves)
            (mixHash (hash cfg.useThreatOrdering) (hash cfg.useForcedMovePruning))))))
-- 将所有会影响搜索结果或资源边界的配置字段纳入缓存键哈希。

def engineSearchKeyHash (key : EngineSearchKey) : UInt64 :=
  mixHash (engineConfigHash key.config)
    (mixHash (hash key.fuel)
      (mixHash (enginePlayerHash key.target) (enginePositionHash key.position)))
-- 综合配置、剩余深度、目标玩家和紧凑局面计算搜索键哈希。

instance : Hashable EngineSearchKey where
  hash := engineSearchKeyHash
-- 让标准哈希表能够使用紧凑搜索键。

/- Hash lookup is followed by the standard map's exact `BEq EngineSearchKey`
   comparison.  Hash collisions therefore affect performance, not which
   packed position is returned. -/
abbrev EngineMemo := Std.HashMap EngineSearchKey (Option CandidateTree)
-- 用标准哈希表保存紧凑搜索键到成功候选树或失败结果的映射。

inductive EngineCacheLookup where
  | miss
  | notFound
  | found (tree : CandidateTree)
-- 显式区分从未搜索、有限搜索已失败和已找到候选树三种缓存状态。

def EngineCacheLookup.isFound : EngineCacheLookup → Bool
  | .found _ => true
  | _ => false
-- 判断显式缓存查询是否携带候选树。

def EngineCacheLookup.isNotFound : EngineCacheLookup → Bool
  | .notFound => true
  | _ => false
-- 判断显式缓存查询是否记录了当前边界内未找到结果。

def EngineCacheLookup.isMiss : EngineCacheLookup → Bool
  | .miss => true
  | _ => false
-- 判断查询键是否在换位表中不存在。

def engineCacheLookup (memo : EngineMemo) (key : EngineSearchKey) :
    EngineCacheLookup :=
  match memo.get? key with
  | none => .miss
  | some none => .notFound
  | some (some tree) => .found tree
-- 将嵌套的 `Option` 查询结果转换为不会混淆的三值视图。

theorem engineCacheLookup_insert_found
    (memo : EngineMemo) (key : EngineSearchKey) (tree : CandidateTree) :
    engineCacheLookup (memo.insert key (some tree)) key = .found tree := by
  simp [engineCacheLookup]
-- 证明插入成功树后，同键查询必然返回该树。

theorem engineCacheLookup_insert_notFound
    (memo : EngineMemo) (key : EngineSearchKey) :
    engineCacheLookup (memo.insert key none) key = .notFound := by
  simp [engineCacheLookup]
-- 证明插入搜索失败后，同键查询不会被解读成未搜索。

theorem engineCacheLookup_miss_iff
    (memo : EngineMemo) (key : EngineSearchKey) :
    engineCacheLookup memo key = .miss ↔ memo[key]? = none := by
  unfold engineCacheLookup
  cases h : memo[key]? with
  | none => simp [h]
  | some result =>
      cases result <;> simp [h]
-- 刻画显式未命中与底层哈希表缺失条目的等价性。

theorem engineCacheLookup_notFound_iff
    (memo : EngineMemo) (key : EngineSearchKey) :
    engineCacheLookup memo key = .notFound ↔ memo[key]? = some none := by
  unfold engineCacheLookup
  cases h : memo[key]? with
  | none => simp [h]
  | some result =>
      cases result <;> simp [h]
-- 刻画显式失败与底层哈希表存储 `some none` 的等价性。

theorem engineCacheLookup_found_iff
    (memo : EngineMemo) (key : EngineSearchKey) (tree : CandidateTree) :
    engineCacheLookup memo key = .found tree ↔
      memo[key]? = some (some tree) := by
  unfold engineCacheLookup
  cases h : memo[key]? with
  | none => simp [h]
  | some result =>
      cases result with
      | none => simp [h]
      | some cachedTree => simp [h]
-- 刻画显式成功与底层哈希表存储具体候选树的等价性。

def emptyEngineMemo (capacity : Nat := 4096) : EngineMemo :=
  Std.HashMap.emptyWithCapacity capacity
-- 按给定初始容量创建空引擎换位表；容量只影响预分配，不是硬上限。

structure EngineState where
  memo : EngineMemo := emptyEngineMemo
  nodes : Nat := 0
  cacheHits : Nat := 0
  memoStoreSkips : Nat := 0
  terminalChecks : Nat := 0
  candidateMoves : Nat := 0
-- 保存递归搜索期间共享的换位表以及累计运行计数器。

def EngineState.stats (state : EngineState) : EngineStats :=
  { nodes := state.nodes
    cacheHits := state.cacheHits
    memoEntries := state.memo.size
    memoStoreSkips := state.memoStoreSkips
    terminalChecks := state.terminalChecks
    candidateMoves := state.candidateMoves }
-- 从可变式引擎状态提取对外报告所需的只读统计信息。

def engineHasBudget (cfg : EngineConfig) (state : EngineState) : Bool :=
  decide (cfg.maxNodes = 0 ∨ state.nodes < cfg.maxNodes)
-- 判断还能否访问一个新节点，其中 `maxNodes = 0` 表示不限制节点数。

def engineRecordVisit (state : EngineState) : EngineState :=
  { state with nodes := state.nodes + 1 }
-- 把已访问节点计数增加一，并保持状态的其余字段不变。

def engineRecordCacheHit (state : EngineState) : EngineState :=
  { state with cacheHits := state.cacheHits + 1 }
-- 把换位表命中计数增加一。

def engineRecordTerminalCheck (state : EngineState) : EngineState :=
  { state with terminalChecks := state.terminalChecks + 1 }
-- 记录一次只在缓存未命中时执行的局面终局分类。

def engineRecordCandidateMoves (state : EngineState) (count : Nat) : EngineState :=
  { state with candidateMoves := state.candidateMoves + count }
-- 累加交给证明方或对手递归扫描器的候选落子数。

def engineMemoCanInsert (cfg : EngineConfig) (state : EngineState) : Bool :=
  decide (cfg.maxMemoEntries = 0 ∨ state.memo.size < cfg.maxMemoEntries)
-- 判断换位表是否允许新增键，其中零上限表示不限制条目数。

def engineMemoInsert (cfg : EngineConfig) (key : EngineSearchKey)
    (result : Option CandidateTree) (state : EngineState) : EngineState :=
  if state.memo.contains key || engineMemoCanInsert cfg state then
    { state with memo := state.memo.insert key result }
  else
    { state with memoStoreSkips := state.memoStoreSkips + 1 }
-- 更新已有键或在容量允许时插入新键；容量已满时只记录一次跳过写入。

/- The existing tactical ordering is intentionally proof-oriented and builds
   a full `WinningCells` mask.  The engine can use the cheaper local detector:
   for each empty point it inspects only the five-cell windows containing that
   point.  Winning moves come first, then blocks, then quiet moves. -/
structure EngineMoveGroups where
  winning : Array Coord
  defense : Array Coord
  quiet : Array Coord
-- 把当前玩家的合法候选分为立即胜着、防守对手立即胜点和普通步三组。

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
-- 利用局部五连检测将局面的全部候选一次划分为三个互斥战术组。

def engineTacticalCandidateMoves (s : Position) : Array Coord :=
  let groups := engineMoveGroups s
  groups.winning ++ groups.defense ++ groups.quiet
-- 按胜着、防守、普通步的优先级重新拼接战术候选。

theorem mem_engineTacticalCandidateMoves_iff (s : Position) (c : Coord) :
    c ∈ engineTacticalCandidateMoves s ↔
      c ∈ orderedCandidateMoves s s.turn := by
  simp only [engineTacticalCandidateMoves, engineMoveGroups,
    Array.mem_append, Array.mem_filter]
  cases hwin : createsFiveFast s.board s.turn c <;>
    cases hdef : createsFiveFast s.board (Player.other s.turn) c <;>
    simp_all
-- 证明引擎的战术分组只改变候选顺序，不改变 `orderedCandidateMoves` 的成员集合。

/- Threat ordering changes only the order.  In particular, the opponent side
   is still expanded over every legal reply, as required by the certificate
   checker. -/
def engineCandidateMoves (cfg : EngineConfig) (s : Position) : Array Coord :=
  if cfg.useThreatOrdering then
    engineTacticalCandidateMoves s
  else
    immediateWinningMovesFirst s s.turn
-- 根据配置在完整战术排序与仅将立即胜着前置的排序之间选择。

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
-- 证明无论采用哪种排序，引擎候选都与当前玩家的全部快速合法候选等价。

theorem mem_engineCandidateMoves_of_legal (cfg : EngineConfig)
    {s : Position} {c : Coord} (hlegal : legalMove s c) :
    c ∈ engineCandidateMoves cfg s := by
  rw [mem_engineCandidateMoves_iff, mem_candidateMovesFast_iff]
  exact ⟨rfl, mem_allCoords c, hlegal⟩
-- 证明对手节点的引擎候选覆盖每一个合法应手，战术排序不会破坏 AND 分支完备性。

def engineLimitProverMoves (cfg : EngineConfig)
    (moves : Array Coord) : Array Coord :=
  if cfg.maxProverMoves = 0 then moves
  else (moves.toList.take cfg.maxProverMoves).toArray
-- 在证明方节点应用可选宽度上限；零表示保留传入数组的全部落子。

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
-- 证明宽度截断只删除候选，绝不会生成原数组中不存在的落子。

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
-- 为目标玩家选择搜索分支：优先胜着，其次被迫防守，最后普通步，并可施加选择性宽度限制。

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
-- 证明证明方经战术剪枝和宽度限制后保留的每个候选仍然是合法落子。

inductive EngineOutcome where
  | found (tree : CandidateTree)
  | notFound
  | cutoff
-- 表示单节点搜索的三值结果：找到树、在当前深度未找到、或因节点预算中断。

structure EngineStep where
  outcome : EngineOutcome
  state : EngineState
-- 将单节点搜索结果与更新后的共享引擎状态一起返回。

instance : Nonempty EngineStep :=
  ⟨{ outcome := .notFound, state := {} }⟩
-- 提供默认的非空 `EngineStep`，便于 Lean 处理部分递归定义。

inductive EngineForestOutcome where
  | found (children : List (Coord × CandidateTree))
  | notFound
  | cutoff
-- 表示对手分支森林的三值结果，其中成功必须包含所有应手的候选子树。

structure EngineForestStep where
  outcome : EngineForestOutcome
  state : EngineState
-- 将森林搜索结果与更新后的引擎状态组合返回。

instance : Nonempty EngineForestStep :=
  ⟨{ outcome := .notFound, state := {} }⟩
-- 提供默认的非空森林搜索步骤。

mutual
  partial def searchWithEngineKeyed (cfg : EngineConfig) (state : EngineState)
      (fuel : Nat) (s : Position) (target : Player)
      (positionKey : EnginePositionKey) : EngineStep :=
    let key : EngineSearchKey :=
      { config := cfg, fuel := fuel, target := target, position := positionKey }
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
            (engineRecordVisit state) fuel s target positionKey
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
  -- 紧凑键递归入口：先查换位表，再检查节点预算，并仅缓存完整完成的成功或失败结果。

  partial def searchWithEngineMiss (cfg : EngineConfig) (state : EngineState)
      (fuel : Nat) (s : Position) (target : Player)
      (positionKey : EnginePositionKey) : EngineStep :=
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
              searchEngineProver cfg
                (engineRecordCandidateMoves state moves.size)
                depth s target positionKey moves.toList
            else
              let moves := engineCandidateMoves cfg s
              let forest := searchEngineOpponent cfg
                (engineRecordCandidateMoves state moves.size)
                depth s target positionKey moves.toList
              match forest.outcome with
              | .found children =>
                  { outcome := .found (.opponentMoves s children)
                    state := forest.state }
              | .notFound =>
                  { outcome := .notFound, state := forest.state }
              | .cutoff =>
                  { outcome := .cutoff, state := forest.state }
  -- 处理缓存未命中的局面：检查终局与深度，并按当前行棋方分派存在分支或全称分支搜索。

  partial def searchEngineProver (cfg : EngineConfig) (state : EngineState)
      (depth : Nat) (s : Position) (target : Player)
      (positionKey : EnginePositionKey) :
      List Coord → EngineStep
    | [] =>
        { outcome := .notFound, state := state }
    | m :: rest =>
        if terminalAfterMoveFast s m = some (winner s.turn) then
          { outcome := .found (.proverMove s m (.terminal (play s m)))
            state := state }
        else
          let child := searchWithEngineKeyed cfg state depth (play s m) target
            (positionKey.play m)
          match child.outcome with
          | .found subtree =>
              { outcome := .found (.proverMove s m subtree)
                state := child.state }
          | .notFound =>
              searchEngineProver cfg child.state depth s target positionKey rest
          | .cutoff => child
  -- 依次尝试目标玩家候选；立即胜着直接成树，否则找到任一成功子树即可返回。

  partial def searchEngineOpponent (cfg : EngineConfig) (state : EngineState)
      (depth : Nat) (s : Position) (target : Player)
      (positionKey : EnginePositionKey) :
      List Coord → EngineForestStep
    | [] =>
        { outcome := .found [], state := state }
    | m :: rest =>
        if terminalAfterMoveFast s m = some (winner s.turn) then
          { outcome := .notFound, state := state }
        else
          let child := searchWithEngineKeyed cfg state depth (play s m) target
            (positionKey.play m)
          match child.outcome with
          | .found subtree =>
              let remaining := searchEngineOpponent cfg child.state depth s target
                positionKey rest
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
  -- 枚举对手的每个合法应手；对手有立即胜着或任一子分支失败时，目标玩家的证明树即失败。
end

def searchWithEngine (cfg : EngineConfig) (state : EngineState)
    (fuel : Nat) (s : Position) (target : Player) : EngineStep :=
  searchWithEngineKeyed cfg state fuel s target (enginePositionKey s)
-- 公开入口只在根局面扫描一次棋盘，递归调用随后使用增量更新的紧凑位置键。

structure EngineReport where
  tree : Option CandidateTree
  depth : Option Nat
  status : EngineStatus
  state : EngineState
-- 汇总候选树、首次成功深度、结束状态和最终搜索状态。

def EngineReport.stats (report : EngineReport) : EngineStats :=
  report.state.stats
-- 从引擎报告中便捷提取统计信息。

def runEngineDepthsKeyed (cfg : EngineConfig) (s : Position) (target : Player)
    (positionKey : EnginePositionKey) : EngineState → Nat → Nat → EngineReport
  | state, depth, 0 =>
      let step := searchWithEngineKeyed cfg state depth s target positionKey
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
      let step := searchWithEngineKeyed cfg state depth s target positionKey
      match step.outcome with
      | .found tree =>
          { tree := some tree, depth := some depth
            status := .found, state := step.state }
      | .notFound =>
          runEngineDepthsKeyed cfg s target positionKey step.state
            (depth + 1) remaining
      | .cutoff =>
          { tree := none, depth := none
            status := .nodeLimit, state := step.state }
-- 复用同一个根紧凑键执行迭代加深，直到找到候选树、达到最大深度或耗尽节点预算。

def runEngineDepths (cfg : EngineConfig) (s : Position) (target : Player) :
    EngineState → Nat → Nat → EngineReport :=
  runEngineDepthsKeyed cfg s target (enginePositionKey s)
-- 在迭代加深开始前只扫描一次根棋盘，并保留原有无显式键的调用接口。

def runEngineFrom (cfg : EngineConfig) (memo : EngineMemo)
    (s : Position) (target : Player) : EngineReport :=
  runEngineDepths cfg s target { memo := memo } 0 cfg.maxDepth
-- 从调用者提供的换位表和深度零开始运行完整迭代加深搜索。

def runEngine (cfg : EngineConfig) (s : Position)
    (target : Player) : EngineReport :=
  runEngineFrom cfg (emptyEngineMemo cfg.memoCapacity) s target
-- 按配置创建空换位表并运行引擎，是常规的无预热缓存入口。

structure CheckedEngineResult where
  report : EngineReport
  certificate : Option CompactCertificate
-- 同时保存原始搜索报告和经过 Lean 检查后才可能存在的可信证书。

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
-- 把候选树编译为紧凑证书并检查其根局面；检查失败时将报告状态改为 `rejected`。

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
-- 证明报告检查器返回的任何证书都蕴含目标玩家从局面 `s` 强制获胜。

def runCheckedEngine (cfg : EngineConfig) (s : Position)
    (target : Player) : CheckedEngineResult :=
  checkEngineReport s target (runEngine cfg s target)
-- 组合引擎搜索和可信证书检查，形成推荐的对外执行入口。

theorem runCheckedEngine_sound {cfg : EngineConfig} {s : Position}
    {target : Player} {c : CompactCertificate}
    (h : (runCheckedEngine cfg s target).certificate = some c) :
    CanForceWin s target := by
  exact checkEngineReport_sound
    (report := runEngine cfg s target) h
-- 证明推荐入口一旦返回证书，就能在 Lean 中得到 `CanForceWin s target`。

/- Small executable regressions.  They intentionally use a local tactical
   position; a complete 7×7 opening search is not part of a regular build. -/
def enginePackedKeyRegressionMoves : List Coord :=
  [(0, 0), (6, 0), (0, 1), (6, 1),
    (0, 5), (6, 5), (0, 6), (6, 6)]
-- 选择覆盖首尾行和索引 0/48 的八个互异坐标，供紧凑键增量更新回归使用。

def enginePackedKeyRegressionPosition : Position :=
  enginePackedKeyRegressionMoves.foldl (fun s m => play s m) initialPosition
-- 从初始局面依次执行边界测试落子，得到用于重新扫描棋盘的参考局面。

def enginePackedKeyRegressionIncremental : EnginePositionKey :=
  enginePackedKeyRegressionMoves.foldl (fun key m => key.play m)
    (enginePositionKey initialPosition)
-- 从初始紧凑键逐步设置相同坐标，用于和完整棋盘重新编码结果比较。

set_option linter.style.nativeDecide false in
example :
    enginePackedKeyRegressionIncremental =
      enginePositionKey enginePackedKeyRegressionPosition ∧
    enginePackedKeyRegressionIncremental.black.word0 =
      ((1 : UInt64) ||| ((1 : UInt64) <<< 7) |||
        ((1 : UInt64) <<< 35) ||| ((1 : UInt64) <<< 42)) ∧
    enginePackedKeyRegressionIncremental.white.word0 =
      (((1 : UInt64) <<< 6) ||| ((1 : UInt64) <<< 13) |||
        ((1 : UInt64) <<< 41) ||| ((1 : UInt64) <<< 48)) ∧
    enginePackedKeyRegressionIncremental.black.word1 = 0 ∧
    enginePackedKeyRegressionIncremental.black.word2 = 0 ∧
    enginePackedKeyRegressionIncremental.black.word3 = 0 ∧
    enginePackedKeyRegressionIncremental.white.word1 = 0 ∧
    enginePackedKeyRegressionIncremental.white.word2 = 0 ∧
    enginePackedKeyRegressionIncremental.white.word3 = 0 := by
  native_decide
-- 验证增量键等于重新扫描所得键，并检查 7×7 的索引 0 至 48 均落在首个分块。

set_option linter.style.nativeDecide false in
example :
    enginePositionKey initialPosition ≠
      enginePositionKey (play initialPosition (3, 3)) := by
  native_decide
-- 验证紧凑键能区分空棋盘和黑方中心首着后的局面。

def engineSmokeConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 2, useThreatOrdering := true }
-- 为立即获胜局面设置深度一、最多访问两个节点的冒烟测试配置。

def engineSmokeResult : CheckedEngineResult :=
  runCheckedEngine engineSmokeConfig searchImmediatePosition .black
-- 在黑方连续四子局面上执行冒烟配置并保存已检查结果。

def engineCutoffConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 1, useThreatOrdering := true }
-- 设置只允许访问一个节点的预算截断测试配置。

def engineSelectiveConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 2, maxProverMoves := 1
    useThreatOrdering := true, useForcedMovePruning := true }
-- 设置证明方只搜索一个最高优先级候选的选择性宽度测试配置。

def engineBoundedMemoConfig : EngineConfig :=
  { maxDepth := 1, maxNodes := 2, maxMemoEntries := 1
    useThreatOrdering := true }
-- 设置换位表最多保存一个条目的容量边界测试配置。

def engineBoundedMemoResult : EngineReport :=
  runEngine engineBoundedMemoConfig searchImmediatePosition .black
-- 在立即获胜局面运行受限换位表配置，以检查跳过写入统计。

def engineDefensePosition : Position :=
  ⟨searchImmediateBoard, .white⟩
-- 复用黑方连续四子棋盘，但令白方行棋，用于测试被迫防守候选。

def engineCachedSmokeResult : EngineReport :=
  runEngineFrom engineSmokeConfig engineSmokeResult.report.state.memo
    searchImmediatePosition .black
-- 复用第一次冒烟搜索的换位表再次搜索同一局面，用于验证缓存命中行为。

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
      searchImmediatePosition)[0]? = some ((0, 3) : Coord) ∧
    (engineProverCandidateMoves engineSmokeConfig
      engineDefensePosition).size = 2 ∧
    ((0, 3) : Coord) ∈
      engineProverCandidateMoves engineSmokeConfig engineDefensePosition ∧
    ((5, 3) : Coord) ∈
      engineProverCandidateMoves engineSmokeConfig engineDefensePosition ∧
    (engineCandidateMoves engineSmokeConfig engineDefensePosition).size = 45 ∧
    engineBoundedMemoResult.status = .found ∧
    engineBoundedMemoResult.stats.memoEntries = 1 ∧
    engineBoundedMemoResult.stats.memoStoreSkips = 1 ∧
    engineCachedSmokeResult.status = .found ∧
    engineCachedSmokeResult.stats.nodes = 0 ∧
    engineCachedSmokeResult.stats.cacheHits = 2 := by
  native_decide
-- 综合回归检查搜索成功、预算截断、选择性候选、防守完备性、换位表容量与缓存复用统计。

example {c : CompactCertificate}
    (h : engineSmokeResult.certificate = some c) :
    CanForceWin searchImmediatePosition .black := by
  exact runCheckedEngine_sound h
-- 从冒烟搜索实际返回的证书实例化引擎可靠性定理，得到该测试局面的黑方强制胜证明。

end Gomoku
