import Gomoku.Basic
import Gomoku.Geometry
import Gomoku.Rules
import Gomoku.Game
import Gomoku.Tactics
import Gomoku.Certificate
import Gomoku.Search
import Gomoku.SearchRegression
import Gomoku.Bounded
import Gomoku.Parametric
import Gomoku.Engine
import Gomoku.Generated.CppSmoke
import Gomoku.Generated.CppFork
import Gomoku.Generated.CppVcf
import Gomoku.Generated.CppReachable
import Gomoku.Generated.CppReachableDoubleThreat
import Gomoku.Examples
import Gomoku.Adversarial
import Gomoku.RuleAudit
import Gomoku.PatternAudit
import Gomoku.SearchAudit
import Gomoku.BoundedAudit
import Gomoku.InteropAudit
import Gomoku.EngineAudit
import Gomoku.MutationAudit
import Gomoku.TerminalAudit

/-!
`Gomoku` 是项目的总入口，按依赖顺序汇集基础棋盘、几何、规则、博弈语义、战术、
证书检查、Lean/C++ 搜索接口、有界语义以及正反例审计模块。导入本文件即可访问完整形式化接口。
-/
