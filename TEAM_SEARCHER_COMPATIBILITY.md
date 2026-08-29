# 队友搜索器兼容性实测

本文件记录对远程分支 `feature/cpp-vcf-search` 的一次隔离实测。测试使用的
分支提交为 `9058efb`，不会把队友分支的源文件自动合并到当前主线。

## 结论

队友的 C++ 搜索器与当前 Lean 主线的证书接口兼容；其同一分支中的 Lean 端有限搜索引擎
也已经接入当前主线：

- C++ 程序可以成功编译；
- C++ 单元测试全部通过；
- 五个样例都能生成 `CompactCertificate` 形状的 Lean 文件；
- 其中两个样例从真实可达规则历史导出，分别覆盖一步胜和双威胁；
- 五个生成文件都能在当前主线的 Lean 4.33.0 + mathlib 环境下编译通过；
- `Gomoku.Engine` 和独立的 `Gomoku.EngineAudit` 在当前主线下构建通过；
- 因而暂时不需要修改 `Gomoku.Certificate` 或 `Gomoku.Search` 的证书接口。

这不等于已经证明 15x15 空棋盘黑棋必胜。样例是人为构造的局部局面，生成的文件使用
`checkLocalCertificateAt`，只能证明对应样例局面可强制获胜。

## 实测环境

- 工程目录：`D:\LeanProjects`
- Lean：`leanprover/lean4:v4.33.0`
- C++ 编译器：`D:\c++\mingw64\bin\g++.exe`，版本 11.4.0
- C++ 分支：`origin/feature/cpp-vcf-search`，提交 `9058efb`

由于 GCC 不在默认 `PATH`，构建时需要临时加入：

```powershell
$env:PATH = 'D:\c++\mingw64\bin;' + $env:PATH
```

## C++ 实测结果

在队友分支的隔离副本中执行：

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\cpp\build.ps1 -Clean
.\cpp\build\gomoku_tests.exe
```

结果：

```text
Built ...\cpp\build\gomoku_solver.exe
Built ...\cpp\build\gomoku_tests.exe
all C++ solver tests passed
```

五个输入样例的搜索结果如下：

| 样例 | 深度 | 证书节点数 | 搜索状态 |
|---|---:|---:|---|
| `immediate_win.txt` | 1 | 2 | `found` |
| `opponent_fork.txt` | 2 | 5 | `found` |
| `open_four_vcf.txt` | 3 | 6 | `found` |
| `reachable_immediate.txt` | 1 | 2 | `found` |
| `reachable_double_threat.txt` | 2 | 417 | `found` |

第三个样例还报告了 VCF 引导成功；这只是搜索顺序优化，Lean 不信任 C++ 的 VCF 判断，
仍会检查证书中的每一条合法应对。

## Lean 实测结果

用 C++ 生成的五个文件分别运行：

```powershell
lake env lean .\Gomoku\Generated\CppSmoke.lean
lake env lean .\Gomoku\Generated\CppFork.lean
lake env lean .\Gomoku\Generated\CppVcf.lean
lake env lean .\Gomoku\Generated\CppReachable.lean
lake env lean .\Gomoku\Generated\CppReachableDoubleThreat.lean
```

五个命令均以退出码 `0` 结束。生成文件的结构与主线约定一致：

1. 用 `Array (Coord × Player)` 描述根局面的棋子；
2. 用 `Board.place` 折叠出 Lean 棋盘；
3. 用 `CompactCertificate` 保存 `terminal`、`proverMove` 和 `opponentMoves` 节点；
4. 用 `checkLocalCertificateAt` 检查根局面和全部证书边；
5. 用 `local_certificate_at_sound` 把通过检查的证书转成 `CanForceWin`。

当前主线已经保存这五个生成文件作为 `Gomoku.Generated.CppSmoke`、
`Gomoku.Generated.CppFork`、`Gomoku.Generated.CppVcf`、
`Gomoku.Generated.CppReachable` 和 `Gomoku.Generated.CppReachableDoubleThreat` 回归样例。另有
`Gomoku.InteropAudit` 用同样的导出器形状做了一个通过样例和一个错误子局面拒绝样例，
并提供 `checkExternalLocalCertificate_sound` 作为统一适配定理。
真实可达样例保存在 `Gomoku.Generated.CppReachable`，并在 `Gomoku.InteropAudit` 中与
`auditReachableImmediatePosition` 的合法历史连接起来。

新增的 `CppReachableDoubleThreat` 来自 17 手合法历史：根局面有 9 枚黑子、8 枚白子，
轮到白棋，黑棋在两条不同方向各有一条四连。生成证书有 417 个节点，根节点的 208 个
白棋合法应手全部展开；Lean 还单独断言了合法应手数和证书应手数都为 208，并拒绝删去任一
应手的错误证书。

## 当前边界

队友搜索器目前已经是“可以运行并生成可检查局部证书”的搜索器，但还不是完整求解器：

- 没有从空棋盘开始的 15x15 黑棋必胜证书；
- VCF 只覆盖有限的连续四威胁，不是完整的 VCT/威胁空间搜索；
- 证书导出仍是树形展开，没有 DAG 共享压缩；
- 搜索的哈希、剪枝和 C++ 规则实现都在 Lean 可信边界之外；
- `depthLimit`、节点限制或内存限制导致的 `none` 不能解释为数学上的必败。

因此，后续合并队友 C++ 源码时仍需让新生成文件逐个通过当前 Lean 检查器；不能只相信
C++ 程序打印的 `found`。

## 合并建议

当前主线先上传本分支的审查、接口、Lean 引擎和五个生成证书改动。队友仍应针对自己的
`feature/cpp-vcf-search` 创建 Pull Request，主要合并 C++ 搜索器和生成器；合并后重新执行
本文件中的 C++/Lean 实测。
只有在生成文件通过当前主线检查器后，才把它记录为正式局部成果。
