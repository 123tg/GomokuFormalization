import Gomoku.Search
import Gomoku.RuleAudit

namespace Gomoku

/-!
Regression tests for the single move-to-outcome boundary used by the engine.
These examples intentionally include both legal and illegal calls: the
executable function is total, while `terminalAfterMoveFast_eq_terminal`
explains its result under the normal game premises.
-/

example :
    terminalAfterMoveFast searchImmediatePosition (4, 7) = some .blackWin := by
  native_decide

example :
    terminalAfterMoveFast auditSingleEmptyPosition (14, 14) = some .draw := by
  native_decide

example :
    terminalAfterMoveFast searchTerminalPosition (0, 0) = none := by
  native_decide

example :
    terminalAfterMoveFast searchTerminalPosition (0, 0) = none := by
  apply terminalAfterMoveFast_of_not_legal
  native_decide

example :
    terminalAfterMoveFast initialPosition (7, 7) =
      terminal (play initialPosition (7, 7)) := by
  apply terminalAfterMoveFast_eq_terminal
  · exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal
  · native_decide

example :
    terminalAfterMoveFast auditSingleEmptyPosition (14, 14) =
      terminal (play auditSingleEmptyPosition (14, 14)) := by
  apply terminalAfterMoveFast_eq_terminal
  · native_decide
  · native_decide

example :
    terminalAfterMoveFast initialPosition (7, 7) = none ↔
      terminal (play initialPosition (7, 7)) = none := by
  apply terminalAfterMoveFast_none_iff
  · exact Position.terminal_none_of_not_isTerminal Position.initial_not_terminal
  · native_decide

example :
    terminalAfterMoveFast searchImmediatePosition (4, 7) =
        some (winner searchImmediatePosition.turn) ↔
      terminal (play searchImmediatePosition (4, 7)) =
        some (winner searchImmediatePosition.turn) := by
  apply terminalAfterMoveFast_win_iff <;> native_decide

example :
    terminalAfterMoveFast auditSingleEmptyPosition (14, 14) = some .draw ↔
      terminal (play auditSingleEmptyPosition (14, 14)) = some .draw := by
  apply terminalAfterMoveFast_draw_iff <;> native_decide

end Gomoku
