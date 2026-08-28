import Gomoku.Engine

/-!
纯 Lean 换位表键微基准。它比较旧的“每个子局面重新生成并哈希 225 格向量”路径与
`Gomoku.Engine` 当前的“根局面压缩一次、每步增量设置 bit”路径。

该程序只测量键构造和哈希，不代表完整搜索时间，也不属于证书可信基础。
-/

namespace Gomoku.EngineKeyBenchmark

def oldCellHash : Cell → UInt64
  | .empty => 3
  | .stone .black => 5
  | .stone .white => 7
-- 复现紧凑键优化前用于三种棋盘格的基础哈希常量。

def oldPositionHash (key : PositionKey) : UInt64 :=
  key.2.toArray.foldl
    (fun value cell => mixHash value (oldCellHash cell))
    (enginePlayerHash key.1)
-- 复现旧引擎逐个混合 225 个 `Cell` 的完整局面哈希路径。

def oldKeyHash (fuel : Nat) (target : Player) (s : Position) : UInt64 :=
  mixHash (hash fuel)
    (mixHash (enginePlayerHash target) (oldPositionHash (positionKey s)))
-- 复现旧搜索键从深度、目标玩家和完整向量局面计算哈希的过程。

def coordinateForRound (i : Nat) : Coord :=
  coordAtIndex ⟨i % 225, Nat.mod_lt _ (by decide)⟩
-- 把基准轮次循环映射到 225 个合法坐标，使输入不会被编译器视为单一常量。

partial def oldLoop : Nat → UInt64 → UInt64
  | 0, value => value
  | n + 1, value =>
      let c := coordinateForRound n
      oldLoop n (mixHash value (oldKeyHash 4 .black (play initialPosition c)))
-- 重复构造一步子局面、完整 225 格旧键及其哈希，并累计校验值以强制执行计算。

partial def packedLoop (base : EnginePositionKey) : Nat → UInt64 → UInt64
  | 0, value => value
  | n + 1, value =>
      let c := coordinateForRound n
      let key : EngineSearchKey :=
        { fuel := 4, target := .black, position := base.play c }
      packedLoop base n (mixHash value (engineSearchKeyHash key))
-- 从同一个根紧凑键增量生成一步子键、计算新哈希并累计校验值。

def run (rounds : Nat := 20000) : IO Unit := do
  let startOld ← IO.monoNanosNow
  let oldResult := oldLoop rounds 0
  IO.println s!"old checksum={oldResult}"
  let stopOld ← IO.monoNanosNow
  let base := enginePositionKey initialPosition
  let startPacked ← IO.monoNanosNow
  let packedResult := packedLoop base rounds 0
  IO.println s!"packed checksum={packedResult}"
  let stopPacked ← IO.monoNanosNow
  IO.println s!"rounds={rounds}"
  IO.println s!"old_ns={stopOld - startOld}"
  IO.println s!"packed_ns={stopPacked - startPacked}"
-- 顺序运行两条键路径并打印校验值、轮次和各自耗时，默认执行 20,000 轮。

end Gomoku.EngineKeyBenchmark

def main : IO Unit :=
  Gomoku.EngineKeyBenchmark.run
-- 提供 `lake env lean --run bench/LeanEngineKeyBenchmark.lean` 命令行入口。
