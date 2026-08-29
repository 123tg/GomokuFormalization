# 当前困难说明 (Difficulties)

> 目标回顾:在固定 7×7、五连胜、黑先手的标准双方规则下,让 C++ 搜索输出 Lean 能独立
> 检查的证明证书,最终证明 `WhiteCanPreventBlackWin initialPosition`、
> `BlackCanPreventWhiteWin initialPosition` 与 `StandardDraw initialPosition`。
> 当前状态:防御证书全链路(Lean checker + soundness + 负测试 + C++ 导出)已完成并通过
> 验证;空棋盘三个定理尚未完成。

困难分三类:**本质性困难(数学规模)**、**信任边界问题(不能走捷径)**、
**工程/形式化困难(可解决,在推进中)**。

---

## 一、本质性困难:空棋盘证明的规模(无法靠加大预算解决)

防御证书的语义要求:**攻击方(黑棋)节点必须覆盖全部合法应手**。空棋盘 7×7 的完整
博弈树约为 **10^62 个节点**,而实测:

| 尝试 | 预算 | 结果 |
|---|---|---|
| 防御搜索 prevent-black-win(白防守) | 40M 节点 / 50M 表项 / 约 4 分钟 | `unknown`(表满) |
| 防御搜索 prevent-white-win(黑防守) | 40M 节点 / 50M 表项 / 约 4 分钟 | `unknown`(表满) |
| DFPN 强制胜 target=black(带 VCF) | 20M 表项 / 37 秒 | `table-limit`,未找到黑胜 |
| DFPN 强制胜 target=white | 20M 表项 / 37 秒 | `table-limit`,未找到白胜 |
| 小局面(白四连两空点,闭环) | 默认 | `found`(秒出,Lean 验证通过) |

搜索深度已到达 49(整局),但树的宽度是天文数字。**这不是实现 bug,是数学规模问题**:
完整博弈树证书对空棋盘在物理上不可行,再翻 100 倍预算也是 `unknown`。

## 二、信任边界问题:两条"看似省事"的路都走不通

1. **"DFPN 双方都搜不出 = 证明和棋"?不行。**
   DFPN 返回 `table-limit`(被截断),搜索不完整。"预算内没找到强制胜" ≠ "不存在
   强制胜"。不能把 C++ 的未知当定理——这是本项目明确拒绝的信任边界。
   "空棋盘和棋"目前是**高度可信的猜想**(旧记录 + 两侧 DFPN 无胜 + 深度 49 搜索无
   结果三方一致),但还不是 Lean 定理。

2. **"把旧求解器的 8259 节点树带回 Lean 验证"?也不行。**
   那棵树依赖了大量 Lean 不信任的剪枝:
   - **对称合并**(`tree_symmetry_collapses=6516`)——Lean 证书要求攻击方节点列出
     全部合法应手,对称合并后的树覆盖不完整,除非另行形式化 D4 对称(新的一大块工作);
   - **pairing 闭合**(16004 次配对调用)——Lean 目前不理解配对论证;
   - dominance / partial-pairing 等其他启发式。
   而且它是 Maker–Breaker 语义(只防黑五),不能直接给出黑防白。
   因此"带回去验证"只有一条可行路:把 pairing 论证在 Lean 里形式化,让搜索器只把
   pairing 作为"找到策略的线索",按 Lean 可检查的格式重新导出。

## 三、Pairing 路线(唯一可行路径)自身的困难

1. **7×7 空棋盘不存在"根 pairing"。**
   已实现 pairing 查找器并做 500M 节点完整搜索:5×5 秒出覆盖全部窗口的配对(12 对,
   机制验证通过),**7×7 搜不到**。这与旧记录 `tree_depth=8` 一致——旧求解器也不是在
   根节点直接配对成功,而是靠"树 + 配对"。所以即使 pairing soundness 形式化完成,
   也不能直接套在空棋盘根节点,必须做**混合证书:小博弈树 + 局面相关配对叶**。

2. **Pairing.lean 形式化的技术困难**(可解决,在推进):
   - `lineCells`/`List.filterMap` 的类型推断问题:`step` 参数是 `Int`,导致
     `List.mem_filterMap` 的见证类型被推断成 `Int`(已定位,正在修);
   - 不变式的**两步结构**:完整不变式只在黑棋回合成立;黑棋落子后(白棋回合)只有
     "无黑配对"分量成立,白棋回应后恢复——引理必须按两 ply 设计;
   - 配对唯一性引理(同一格至多出现在一个配对中)需要 List 去重论证。

## 结论与出路

- **已完成**:DefenseCertificate 全链路(语义、checker、soundness、负测试)、C++
  防御搜索(`--prove` 模式、found/refuted/unknown 严格传播)、小局面 C++→Lean 闭环
  (`PreventWhiteFour.lean`、`PreventBlackTwoGaps.lean` 均通过 Lean 验证)、DFPN 双侧
  实验、pairing 查找器(5×5 验证 / 7×7 根配对否定)。
- **本质困难**:空棋盘和棋的 Lean 证明无法靠全树搜索完成(规模 10^62)。
- **出路**:混合证书(小树 + pairing 叶)+ `pairing_strategy_sound` 定理——这是多轮
  工程,不是死路,但**短期内拿不到 `StandardDraw initialPosition` 这个最终定理**。
