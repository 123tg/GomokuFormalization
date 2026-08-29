# 搜索器方法详解(讲稿参考)

> 项目:Gomoku Formalization — 7×7 五子棋,五连即胜,黑先,标准规则
> 代码:`cpp/src/gomoku_solver.cpp` / `cpp/include/gomoku_solver.hpp`
> 本文按"讲稿"组织:每个方法先一句话概括,再讲原理、为什么需要、工程细节、以及与 Lean 验证的关系。

---

## 目录

1. [总览:两个搜索器,两条流水线](#1-总览)
2. [DFPN 证明数搜索(模式 A 主搜索)](#2-dfpn-证明数搜索)
3. [VCF 连续冲四快攻(模式 A 加速)](#3-vcf-连续冲四快攻)
4. [威胁排序与强制防守剪枝](#4-威胁排序与强制防守剪枝)
5. [Zobrist 哈希与置换表](#5-zobrist-哈希与置换表)
6. [迭代加深与资源控制](#6-迭代加深与资源控制)
7. [DefenseSearcher 完整 AND/OR 防守搜索(模式 B)](#7-defensesearcher-完整-andor-防守搜索)
8. [局面评估:neighborhoodScore 与 createsFive](#8-局面评估)
9. [证书生成与 Lean 导出](#9-证书生成与-lean-导出)
10. [辅助工具方法](#10-辅助工具方法)
11. [与 Lean 验证的关系(讲稿收尾)](#11-与-lean-验证的关系)

---

## 1. 总览

搜索器是 C++17 写的,核心是一个可执行文件 `gomoku_solver`,内部有**两条独立的搜索流水线**:

| | 模式 A:强制胜搜索 | 模式 B:防守证明搜索 |
|---|---|---|
| 类 | `DfpnSolver` | `DefenseSearcher` |
| 目标 | 证明"某方能强制获胜" | 证明"防守方能阻止对方获胜" |
| 语义 | `CanForceWin` | `CanPreventWin` |
| 输出 | `CompactCertificate` | `DefenseCertificate` |
| 命令行 | `--input ...` | `--prove prevent-black-win \| prevent-white-win` |
| 核心算法 | DFPN + VCF | 完整 AND/OR 深度优先 + 三值传播 |

**贯穿全局的设计纪律**:两条流水线产出的都只是**候选数据(certificate)**,任何算法、启发式、缓存都不能直接当结论——最终由 Lean 检查器逐节点重算,通过才是定理。

---

## 2. DFPN 证明数搜索

### 一句话
DFPN(Depth-First Proof-Number Search,深度优先证明数搜索)用两个数——证明数 pn 和反证数 dn——指导搜索把预算花在"最可能证明成功"的分支上。

### 核心概念
每个节点维护两个数:

- **证明数 pn(proof number)**:证明"这个局面是目标方必胜"还需要展开的叶子数下界。pn = 0 表示已证明必胜。
- **反证数 dn(disproof number)**:证明"这个局面不是目标方必胜"还需要展开的叶子数下界。dn = 0 表示已证明非必胜。

计算规则(见 `recompute`):

- **目标方回合(OR 节点)**:pn = min(子节点 pn),dn = Σ(子节点 dn)。
  - 解释:目标方只要有一个子节点能赢,整个节点就赢,所以证明数取最小;要证明它不能赢,必须所有子节点都不能赢,所以反证数求和。
- **对手回合(AND 节点)**:pn = Σ(子节点 pn),dn = min(子节点 dn)。
  - 解释:目标方要赢必须赢过所有对手应手,所以证明数求和;对手只要有一个应手能防住,整个节点就防住了,所以反证数取最小。

终局赋值(`ensureEntry`):
- 目标方已获胜:pn = 0,dn = ∞;
- 目标方已失败或深度耗尽:pn = ∞,dn = 0。

### 选择策略(见 `dfpn` 主循环)
每一轮:
1. 从当前节点出发,沿着"pn/dn 最小"的孩子一路向下(深度优先);
2. 递归调用时传入**阈值**:
   - 对 OR 节点:子节点的 pn 阈值 = min(父阈值, 第二小 pn + 1);dn 阈值 = 父 dn − 当前 dn + 子 dn;
   - 对 AND 节点对称;
3. 子节点返回后,若其 pn/dn 未变化说明阈值内无法推进,则停止这条线;否则 `recompute` 父节点并继续。

这正是经典 DFPN 的"阈值传递 + 选择性深入"思想:大多数搜索时间花在最有可能出结果的那条路径上,而不是盲目遍历。

### 为什么用 DFPN 而不是普通 Alpha-Beta
- 五子棋的证明目标是"是否存在必胜策略",不是"最优着法"——证明数直接对应"离证明还有多远",比局面估值更贴近证明任务;
- 深度优先 + 置换表,内存友好,能跑很深的局部搜索;
- 输出的证明路径可以直接重放成证书。

### 与 Lean 的关系
DFPN 的 pn/dn、剪枝、缓存全部**不可信**。它只负责"找到一条看起来能证明的路径",真正成立与否由 Lean 检查器重算。

---

## 3. VCF 连续冲四快攻

### 一句话
VCF(Victory by Continuous Four,连续冲四)是五子棋特有的"杀棋路线"检测:我方不断冲四,对手被迫防守,直到成五。

### 冲四的定义
**冲四**:下一子就能成五的着法,对手必须立刻堵。代码用 `createsFive(move, player)` 判定:在 move 落子后,该玩家是否形成至少五连。

### 算法流程(见 `probeVcf`)
给定一个局面和剩余深度 `remaining`:
1. 查 VCF 置换表,命中直接返回;
2. 若轮到目标方且深度足够:
   a. 找**一步成五**(直接 `createsFive`),找到即返回该着法;
   b. 否则对每个候选着法模拟:目标方落子后——
      - 若对手已有成五着法,这个进攻着法无效,跳过;
      - 若目标方形成**双冲四**(两个以上成五威胁,`targetThreats.size() >= 2`),对手堵不过来,直接返回——这是杀棋;
      - 若只有一个威胁,对手被迫堵住,然后递归 `probeVcf` 继续(深度减 2,因为一攻一防两步);
3. 全程有独立预算 `maxVcfNodes`,超了就停。

### 为什么有用
- 攻击端:五子棋大量杀棋是"连续冲四"形态,VCF 能**快速找到杀棋**,比 DFPN 的通用搜索快得多;
- 防守端:对手被冲四时合法应手骤减(通常只有 1 个),AND 分支急剧缩小;
- VCF 结果作为**着法提示(vcfHints)**:DFPN 在目标方回合把 VCF 找到的着法排到第一位(`std::rotate`),引导主搜索先试杀棋。

### 工程细节
- 独立的表 `vcfTable`、独立预算 `maxVcfNodes`/`maxVcfDepth`,与 DFPN 互不干扰;
- 攻不下来就退回 DFPN 做全局面搜索——VCF 是"快攻",不是主流程;
- `--no-forced-pruning` 可关闭相关剪枝,用于对照实验。

---

## 4. 威胁排序与强制防守剪枝

### 威胁排序(Threat Ordering)
所有候选着法先打分再排序(见 `orderedMoves` / `sortedEmptyMoves`):

1. **成五着法**(`createsFive(move, 当前方)`):+1,000,000;
2. **防守着法**(不成五但能堵住对方的成五):+500,000;
3. **邻域得分**(`neighborhoodScore`):该点 5×5 邻域内的棋子加权——相邻 8 格每子 +8,其余 16 格每子 +2,再减去到棋盘中心的曼哈顿距离(鼓励靠中)。

排序稳定:同分按 y 再按 x,保证可复现。

### 强制防守剪枝(Forced-Move Pruning)
在目标方回合(prover)且开启 `forcedMovePruning` 时:
- 若有成五着法,**只搜成五着法**(其他一律跳过);
- 若没有成五但有防守着法,**只搜防守着法**。

直觉:对方已经形成冲四/活四时,你不去堵就是送死,其他着法不可能更好。这能大幅缩小 OR 分支。

### 与 Lean 的关系
剪枝只影响"哪些着法被搜索",**不影响证明的正确性**:证书导出时,攻击方节点仍然必须列出**全部合法应手**(见 DefenseSearcher 的 `attackerMoves`),Lean 检查器会验证"全应手覆盖",漏一个就整张被拒。所以剪枝是安全的加速,不改变可信边界。

---

## 5. Zobrist 哈希与置换表

### Zobrist 哈希
`Board` 里维护一个 64 位 Zobrist 键:
- 每个 (坐标, 颜色) 组合分配一个随机 64 位数;
- 落子时 `zobrist ^= stoneHash(move, player)`,异或增量更新(O(1));
- 棋子移动/撤销时再异或一次即可还原。

### 置换表(Transposition Table)
`StateKey` = 黑棋位图(4×64)+ 白棋位图 + zobrist + 深度 + 轮次 + 目标方;哈希函数把 zobrist 与深度/轮次/目标混合,减少碰撞。

作用:
- 不同路径到达同一局面(置换)时,直接复用结果,避免重复搜索;
- DFPN 的 pn/dn、VCF 的杀棋提示都缓存;
- 受 `maxTableEntries` 限制,满表即停(`tableLimit`),绝不无限增长。

### 与 Lean 的关系
置换表命中直接返回结果——这是**典型的不可信缓存**:同一局面在不同搜索上下文里结论可能不同(深度/目标不同),所以缓存结果只用于加速,证书导出时仍按完整树重放。

---

## 6. 迭代加深与资源控制

### 迭代加深
`solve` 入口对深度 `1..maxDepth` 逐层调用 DFPN(`dfpn(root, depth, ∞, ∞)`),每层完整搜索,成功即返回。好处:
- 浅层先给出"这层有/没有证明"的快速反馈;
- 与置换表配合,深层的搜索能复用浅层结果;
- 预算(节点/时间)被自然分配,浅层失败不会浪费太多资源。

### 资源上限(全部可配置)
| 参数 | 含义 | 触发状态 |
|---|---|---|
| `maxDepth` | 迭代加深深度上限 | `depth-limit` |
| `maxNodes` | DFPN 展开节点预算 | `node-limit` |
| `maxTableEntries` | 置换表项数上限 | `table-limit` |
| `maxVcfNodes` / `maxVcfDepth` | VCF 预算 | (VCF 静默放弃) |
| `maxCertificateNodes` | 证书节点数上限 | `certificate-limit` |
| `maxProverMoves` | 目标方回合选择性宽度(0=完整) | — |

### 诚实的状态语义(重要!)
- `found`:找到候选证书;
- `depth-limit / node-limit / table-limit / certificate-limit`:搜索被资源截断,**无证书**;
- **"搜不到" ≠ "不存在"**:有限搜索失败只能说明"本次预算内没找到证据",绝不能写成和棋或必败。

---

## 7. DefenseSearcher 完整 AND/OR 防守搜索

### 一句话
模式 B 用**完整 AND/OR 深度优先搜索**证明"防守方(defender)能阻止攻击方获胜",结果严格三值:found / refuted / unknown,unknown 永不缓存。

### 语义(见 `proveDefense`)
对节点 `(position, defender)`:

- **终局**:
  - 攻击方获胜 → `refuted`(防守失败);
  - 防守方获胜或和棋 → `found`(防守成功)。
- **防守方回合**(OR,`position.turn == defender`):
  - 按排序依次尝试每个合法着法;
  - 第一个返回 `found` 的孩子 → 本节点 `found`,并记录该着法(`chosenMove`);
  - 全部孩子 `refuted` → 本节点 `refuted`;
  - 只要有一个孩子 `unknown` → 本节点 `unknown`。
- **攻击方回合**(AND,对手走):
  - 必须遍历**全部**合法着法;
  - 任何一个孩子 `refuted` → 本节点 `refuted`(攻击方找到了破绽);
  - 全部孩子 `found` → 本节点 `found`;
  - 只要有一个 `unknown` → 本节点 `unknown`。

### 为什么"完整"
攻击方节点的 `moves` 来自 `orderedEmptyMoves`(全部空格),一个不漏;并且 `unknown` 永不写缓存、向上传播到根——所以**只要返回 found,就确实存在完整的防守策略树**;被预算截断时只可能是 unknown,不可能伪造出证明。

### 与模式 A 的区别
- 模式 A 的 DFPN 是"找一条必胜路径",可以靠剪枝缩小范围;
- 模式 B 的 AND/OR 是"证明防守覆盖所有攻击应手",攻击方节点必须全展开——这正是 Lean `CanPreventWin` 归纳定义里的 `attackerMoves : ∀ m, ...` 全称量词的对应物。

### 与 Lean 的关系
`proveDefense` 的 found 结果通过 `emitDefenseProof` 重放成 `DefenseCertificate`(terminal / defenderMove / attackerMoves 三种节点),由 Lean 的 `checkDefenseCertificateAt` 逐节点重算:终局重算、轮次核对、合法性核对、攻击方全应手覆盖核对。

---

## 8. 局面评估

### createsFive(落子后是否成五)
在 (move, player) 处落子后,沿横、竖、两条对角线各检查是否出现连续 ≥5 同色。这是所有威胁判断的基础:`winningMoves`(找所有成五着法)、VCF、强制防守剪枝都靠它。

### neighborhoodScore(邻域启发分)
```
对 move 的 5×5 邻域内每个棋子:
  相邻 8 格(切比雪夫距离 ≤1):+8
  其余 16 格:+2
减去 |x−3| + |y−3|(到中心的曼哈顿距离)
```
直觉:五子棋的好点通常在已有棋子的旁边(有发展潜力),且靠中更好(四个方向都能延伸)。它只用于**排序**,不影响正确性。

---

## 9. 证书生成与 Lean 导出

### 模式 A:CompactCertificate
`emitProof` 从 DFPN 表中 pn=0 的节点出发重放:
- 目标方回合:`proverMove`(选一个已证明的着法);
- 对手回合:`opponentMoves`(列出全部合法应手);
- 终局:`terminal`。
节点带 `sourceParent`/`sourceMove` 元数据,导出时用 `play parent move` 精确定义子局面,保证 Lean 端能独立重算。

### 模式 B:DefenseCertificate
`emitDefenseProof` 按表里记录的 found 路径重放:
- `defenderMove`:防守方回合,取 `chosenMove`;
- `attackerMoves`:攻击方回合,展开**全部**合法应手;
- `terminal`:终局结果。
导出时同样用 `sourceParent` 定位,检查器端 `defenseChildPositionMatches` 验证子局面 = `play s m`。

### 导出格式
`writeLeanDefenseCertificate` / `writeLeanCertificate` 生成 `.lean` 文件:
- 石头数组 → `Board.foldl place` 构造根局面;
- 每个节点一条 `def`(局面用 `play` 推导);
- 证书结构体 + `native_decide` 的检查定理;
- 最后给出 `white_defense_certificate_sound ...` 得到 `WhiteCanPreventBlackWin` 等最终定理。

---

## 10. 辅助工具方法

| 工具 | 方法 | 用途 |
|---|---|---|
| `find_pairing` | 配对搜索(forced-pair / MRV / equalFreeEdge) | 找"覆盖所有窗口"的防守配对,验证 5×5 机制、探测 7×7 根配对不可行 |
| `threat_sim` | 威胁-回应模拟器 | 检验"简单白方防守"能否挡住黑方(结果:3/3 开局都挡不住,说明需要真正的策略) |
| `solve_775` | 三值 AND/OR + D4 对称 + 配对剪枝 | 经验性探测空棋盘 7×7 的胜负值(文献:和棋) |
| `make_draw_position` | 双色窗口构造器 | 生成"每个 5-窗口都含黑白两子"的必和局面,供 9 个 StandardDraw 定理使用 |
| `extract_pairing` | 配对提取 | 输出指定局面的覆盖配对,供 Lean 配对叶定理使用 |

这些工具都是**探测/辅助**性质,结论一律以 Lean 验证为准。

---

## 11. 与 Lean 验证的关系

讲稿收尾可以这样讲:

1. **分工**:C++ 搜索器负责"找"(候选),Lean 负责"证"(定理);
2. **不可信清单**:DFPN 的 pn/dn、VCF 杀棋、威胁排序、强制剪枝、Zobrist、置换表、各种预算——全部只影响搜索效率,不产生任何结论;
3. **可信清单**:Lean 的 `checkCertificate` / `checkDefenseCertificateAt` 逐节点重算(终局、合法性、子局面、攻击方全应手覆盖)+ soundness 定理(`defense_certificate_sound`、`white/black_defense_certificate_sound`、`standardDraw_of_mutualDefense`);
4. **成果**:9 个中盘局面的 `StandardDraw` 已机器验证;空棋盘只差 `WhiteCanPreventBlackWin initialPosition` 一环(黑防白已由策略偷取证明)。

> 一句话总结:搜索器可以犯错,检查器不放错;通过检查的证书才是定理。
