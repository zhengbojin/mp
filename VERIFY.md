# VERIFY —— 独立验证指南

本指南用于让第三方在**不依赖作者自述**的前提下，独立验证本仓库的终态声明。

## 0. 声明（待你验证）

1. 全库可编译：`lake build` 通过、0 error；
2. **0 条声明公理**：全库源码无任何公理声明；
3. **0 缺口**：无 `sorry` / `admit`；
4. 主定理 `P_F_neq_NP_F`（及别名、障碍版）的**核验级公理足迹**恰为
   `propext` / `Classical.choice` / `Quot.sound`（数学库标准三件）
   + `native_decide` 机制信任面（定量披露，见 §3）。
5. **符号层分离结论** `P_sym0 ≠ NP_sym0`（框架内：P 侧 = 受限字母表机器类（CBTM0 承载）/
   NP 侧 = NTM2 承载；判定域 = 符号对齐串）——核验级足迹同为标准三件 + `native_decide` 披露（见 §3）；
   精确定位（含多项式时间条件与限制）见 `Spec.md` §7.7、约定 29/31。

## 1. 环境

- 安装 [elan](https://github.com/leanprover/elan)（Lean 工具链管理器，跨平台）；
- 工具链由 `lean-toolchain` **自动固定**（Lean `v4.32.2` / mathlib `v4.32.2`）——无需手工选版本；
- 首次构建建议先 `lake exe cache get` 拉取 mathlib 预编译缓存（否则全量编译 mathlib 需数小时）。

## 2. 步骤一：构建 + 公理/缺口扫描

```bash
lake build
# 预期：Build completed successfully (8712 jobs)，0 error
# 警告状态：5 条（2026-09-15 警告修理后由 498 → 5；均不影响正确性）
#   · 风格类 9 项（longLine/header/show/emptyLine/setOption/maxHeartbeats/whitespace/openClassical/missingEnd）
#     已全局豁免 —— 见 lakefile.toml [leanOptions]；
#   · 战术类与自动生成声明类（unusedTactic/unreachableTactic/unnecessarySimpa/auxLemma）
#     已按文件豁免 —— 见 Reverse10/Q10/CBTM2/CBTM3/CBTM6/Reverse5/L3a 文件头 set_option；
#   · 残留 5 条信号保留：3 条 `Try this: intro …`（intro 链写法建议）+ 1 条 Fintype 参数未用
#     （PrimeSqrtLinearIndep）+ 1 条变量未引用（Reverse11）。

# 声明公理扫描（预期：无输出 = 0 条）
grep -rnE '^[[:space:]]*(private |protected )*axiom ' Mp/

# 缺口扫描（预期：无输出）
grep -rnE '\bsorry\b|\badmit\b' Mp/
```

## 3. 步骤二：核验级公理足迹（`#print axioms`）

创建 `verify_check.lean`：

```lean
import Mp
#print axioms Mp.P_F_neq_NP_F
#print axioms Mp.P_cb_neq_NP_cb
#print axioms Mp.P_neq_NP_with_barriers
#print axioms Mp.subsetSumNTM2_canonical
#print axioms Mp.subsetSum_in_NP_F
#print axioms Mp.subsetSum_kappa_lower_bound
#print axioms Mp.subsetSum_not_in_P_F
#print axioms Mp.P_sym0_neq_NP_sym0
#print axioms Mp.subsetSum_in_NP_sym0
#print axioms Mp.subsetSum_not_in_P_sym0
#print axioms Mp.P_sym0_eq_P_F
```

运行并汇总：

```bash
lake env lean verify_check.lean > verify_out.txt

# ① 非 native 项（预期恰为三行：propext / Classical.choice / Quot.sound）
grep -oE "'(propext|Classical\.choice|Quot\.sound)'" verify_out.txt | sort -u

# ② native_decide 处数计数（登记口径 = 处数，可直接核验）
#    预期合计 764 处（全库逐文件 `grep -c` 之和；2026-09-15 优化前为 1471 处）
grep -c "native_decide" Mp/*.lean | awk -F: '{s+=$2} END {print s}'
```

**关于 `native_decide`（透明披露 · 2026-09-15 更新）**：本工程在有限状态表类证明中
使用 `native_decide`（编译期求值验证；核验级依赖逐调用证书常数
`Mp.<引理>._native.native_decide.ax_*`，属标准三件之外的机制信任）。
本次优化累计把 **707 处**改为内核 `decide`（`of_decide_eq_true rfl`，**不引入额外信任**），
全库处数 **1471 → 764（-48.0%）**（其中第一步「单点查询类」682 处；R3b/S2「严格形态类」
25 处——`∀r∈T` 全体改写 + 逐项内核判定，另有若干变体因超时/编译错误回退）；
保留的 764 处全部是**「全称 / 大表枚举」类**（形如 `∀ q : Fin 102, ∀ s : Sym, … := by native_decide`），
此类查询要求内核展开整张转移表——实测改用 `decide` 会触发
`maximum recursion depth has been reached`（调大 `maxRecDepth` 只是把爆栈换成超时），
故保留本机求值。

**登记口径说明**：本版起采用**处数口径**（`grep -c` 可独立复核）；
原「项数」口径（16753 项 = 11 个受检定理的证书分项之和，随重构变动）自本版起不再作为登记口径。
除上述机制信任外，主定理的核验级依赖**恰为标准三件公理**。

## 4. 步骤三（可选）：结构导览

| 内容 | 位置 |
|---|---|
| 分离主定理（CBTM 框架 + 障碍版） | `Mp/FinalProof.lean`（`P_F_neq_NP_F` :93、`P_cb_neq_NP_cb` :102、`P_neq_NP_with_barriers` :105） |
| 求解链（子集和 ∈ NP） | `Mp/SubsetSumInNP.lean` |
| 下界（κ 界 / 素数平方根线性无关） | `Mp/SubsetSumReal.lean` / `Mp/PrimeSqrtLinearIndep.lean` |
| 验证器最坏步数界 O((\|x\|+1)²) 与 Q10 装配 | `Mp/SubsetSumVerifierQ10.lean`、`Mp/SubsetSumVerifierReverse*.lean` 族 |
| 计算模型与障碍（NTM2 / CBTM / IVM / Barriers） | `Mp/Basic.lean`、`Mp/CBTM.lean`、`Mp/IVM.lean`、`Mp/EssentialDimension.lean`、`Mp/Barriers.lean` |
| 符号层（ATM/NTM2）类与分离结论 | `Mp/ATMAssembly.lean`（`P_sym0_neq_NP_sym0`）；`Mp/ATMBasic.lean`、`Mp/ATMBridge.lean`、`Mp/ATMTransfer.lean`（均已由 `Mp.lean` 导入） |

## 5. 备注

- 任何一步与预期不符 = **可复核的否证材料**，欢迎提交 Issue；
- 规格与约定总纲见 `Spec.md`；构建矩阵与终验口径见 README「终态快照」。
