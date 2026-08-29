import Gomoku.Pairing

namespace Gomoku.Generated

/-! 7x7 中盘配对叶定理: 黑 (0,0) 白 (3,3) 后, 黑再走 m2, 白回应 r2,
剩余格子的覆盖配对给出白方阻止黑胜的策略 (pairingStrategySound)。 -/

def case1Position3 : Position := play (play (play Position.initial (0, 0)) (3, 3)) (5, 2)

def case1Position4 : Position := play case1Position3 (4, 3)

def case1Pairing : Pairing :=
  { pairs := #[
    ((2, 0), (3, 0)),
    ((2, 2), (3, 2)),
    ((2, 3), (2, 4)),
    ((1, 4), (4, 1)),
    ((3, 4), (4, 4)),
    ((1, 2), (4, 5)),
    ((1, 1), (1, 3)),
    ((1, 5), (1, 6)),
    ((2, 1), (3, 1)),
    ((4, 0), (0, 4)),
    ((2, 5), (3, 5)),
    ((0, 2), (4, 6)),
    ((0, 1), (0, 3)),
    ((0, 5), (0, 6)),
    ((2, 6), (3, 6)),
    ((6, 2), (5, 3)),
    ((4, 2), (6, 4)),
    ((5, 1), (5, 4)),
    ((5, 5), (5, 6)),
    ((6, 1), (6, 3)),
    ((6, 5), (6, 6))
  ] }

set_option linter.style.nativeDecide false in
theorem case1ValidAt4 : Pairing.ValidAt case1Position4 case1Pairing := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case1NoBlackInPairs :
    ∀ pair, pair ∈ case1Pairing.pairs →
      case1Position4.board.cell pair.1 ≠ .stone .black ∧
      case1Position4.board.cell pair.2 ≠ .stone .black := by
  native_decide

theorem case1Invariant4 : Pairing.Invariant case1Pairing case1Position4 :=
  Pairing.invariant_of_validAt_unpaired case1ValidAt4 case1NoBlackInPairs

theorem case1WhiteCanPrevent4 : WhiteCanPreventBlackWin case1Position4 :=
  pairingStrategySound case1Position4 case1Pairing rfl case1Invariant4 case1ValidAt4

set_option linter.style.nativeDecide false in
theorem case1Terminal3 : terminal case1Position3 = none := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case1Turn3 : case1Position3.turn = .white := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case1LegalR2 : legalMove case1Position3 (4, 3) := by
  native_decide

theorem case1WhiteCanPrevent3 : WhiteCanPreventBlackWin case1Position3 :=
  CanPreventWin.defenderMove case1Terminal3 case1Turn3 (4, 3) case1LegalR2 case1WhiteCanPrevent4

def case2Position3 : Position := play (play (play Position.initial (0, 0)) (3, 3)) (6, 2)

def case2Position4 : Position := play case2Position3 (3, 4)

def case2Pairing : Pairing :=
  { pairs := #[
    ((2, 0), (3, 0)),
    ((2, 2), (3, 2)),
    ((2, 3), (2, 4)),
    ((1, 4), (4, 1)),
    ((2, 1), (3, 1)),
    ((4, 3), (5, 4)),
    ((4, 2), (4, 4)),
    ((5, 3), (6, 4)),
    ((3, 5), (2, 6)),
    ((2, 5), (4, 5)),
    ((5, 1), (5, 2)),
    ((5, 5), (5, 6)),
    ((3, 6), (4, 6)),
    ((0, 2), (1, 3)),
    ((4, 0), (0, 4)),
    ((0, 1), (0, 3)),
    ((0, 5), (0, 6)),
    ((1, 1), (1, 2)),
    ((1, 5), (1, 6)),
    ((6, 1), (6, 3)),
    ((6, 5), (6, 6))
  ] }

set_option linter.style.nativeDecide false in
theorem case2ValidAt4 : Pairing.ValidAt case2Position4 case2Pairing := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case2NoBlackInPairs :
    ∀ pair, pair ∈ case2Pairing.pairs →
      case2Position4.board.cell pair.1 ≠ .stone .black ∧
      case2Position4.board.cell pair.2 ≠ .stone .black := by
  native_decide

theorem case2Invariant4 : Pairing.Invariant case2Pairing case2Position4 :=
  Pairing.invariant_of_validAt_unpaired case2ValidAt4 case2NoBlackInPairs

theorem case2WhiteCanPrevent4 : WhiteCanPreventBlackWin case2Position4 :=
  pairingStrategySound case2Position4 case2Pairing rfl case2Invariant4 case2ValidAt4

set_option linter.style.nativeDecide false in
theorem case2Terminal3 : terminal case2Position3 = none := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case2Turn3 : case2Position3.turn = .white := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case2LegalR2 : legalMove case2Position3 (3, 4) := by
  native_decide

theorem case2WhiteCanPrevent3 : WhiteCanPreventBlackWin case2Position3 :=
  CanPreventWin.defenderMove case2Terminal3 case2Turn3 (3, 4) case2LegalR2 case2WhiteCanPrevent4

def case3Position3 : Position := play (play (play Position.initial (0, 0)) (3, 3)) (1, 4)

def case3Position4 : Position := play case3Position3 (3, 2)

def case3Pairing : Pairing :=
  { pairs := #[
    ((2, 0), (3, 0)),
    ((2, 4), (3, 4)),
    ((2, 2), (2, 3)),
    ((1, 2), (4, 5)),
    ((1, 1), (1, 3)),
    ((1, 5), (1, 6)),
    ((2, 5), (3, 5)),
    ((0, 2), (4, 6)),
    ((5, 2), (4, 3)),
    ((4, 2), (4, 4)),
    ((2, 1), (4, 1)),
    ((2, 6), (3, 6)),
    ((6, 2), (5, 3)),
    ((3, 1), (6, 4)),
    ((4, 0), (0, 4)),
    ((0, 1), (0, 3)),
    ((0, 5), (0, 6)),
    ((5, 1), (5, 4)),
    ((5, 5), (5, 6)),
    ((6, 1), (6, 3)),
    ((6, 5), (6, 6))
  ] }

set_option linter.style.nativeDecide false in
theorem case3ValidAt4 : Pairing.ValidAt case3Position4 case3Pairing := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case3NoBlackInPairs :
    ∀ pair, pair ∈ case3Pairing.pairs →
      case3Position4.board.cell pair.1 ≠ .stone .black ∧
      case3Position4.board.cell pair.2 ≠ .stone .black := by
  native_decide

theorem case3Invariant4 : Pairing.Invariant case3Pairing case3Position4 :=
  Pairing.invariant_of_validAt_unpaired case3ValidAt4 case3NoBlackInPairs

theorem case3WhiteCanPrevent4 : WhiteCanPreventBlackWin case3Position4 :=
  pairingStrategySound case3Position4 case3Pairing rfl case3Invariant4 case3ValidAt4

set_option linter.style.nativeDecide false in
theorem case3Terminal3 : terminal case3Position3 = none := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case3Turn3 : case3Position3.turn = .white := by
  native_decide

set_option linter.style.nativeDecide false in
theorem case3LegalR2 : legalMove case3Position3 (3, 2) := by
  native_decide

theorem case3WhiteCanPrevent3 : WhiteCanPreventBlackWin case3Position3 :=
  CanPreventWin.defenderMove case3Terminal3 case3Turn3 (3, 2) case3LegalR2 case3WhiteCanPrevent4

end Gomoku.Generated
