import Gomoku.Basic
import Gomoku.Geometry
import Gomoku.Rules
import Gomoku.Game
import Gomoku.Tactics
import Gomoku.Certificate
import Gomoku.Defense
import Gomoku.Pairing
import Gomoku.Search
import Gomoku.Bounded
import Gomoku.Engine
import Gomoku.Generated.CppSmoke
import Gomoku.RuleAudit
import Gomoku.DefenseAudit

/-!
`Gomoku` 是项目的总入口，按依赖顺序汇集基础棋盘、几何、规则、博弈语义、战术、
证书检查、Lean/C++ 搜索接口、有界语义以及精简的迁移验收模块。主线固定为 7×7、五连、黑先。
导入本文件即可访问完整形式化接口。
-/
