/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/



import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.EssentialDimension
import Mp.Barriers
import Mp.LowerBound
import Mp.ClassicalFramework
import Mp.SubsetSumReal
import Mp.PrimeSqrtLinearIndep
import Mp.SubsetSumInNP

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.style.nativeDecide false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false


/-!
# 最终证明：P_F ≠ NP_F（CBTM/F4 框架内闭合）

最终结论：`P_F ≠ NP_F`（本文件定理 `P_cb_neq_NP_cb`）。
「经典（集合论层）P ≠ NP」的传递路线已按 2026-08-28 裁决终止，详见文末
「重定位裁决记录」——它不是待办。

证明路线（对应论文 measure.C.0.7.tex 第 5-6 节）：

1. 子集和语言 `subsetSumLanguageF4Real`（带固定虚部的 F4 编码）属于 `NP_F`
   —— `subsetSum_in_NP_F`（定理，组装于 Mp.SubsetSumInNP，见证 = subsetSumCBTM）。
2. 点态下界（论文 thm:subset-sum-lower 的核心）：对任意正确验证器 M 与任意
   YES 实例 inst，`kappa_M M (encode inst) ≥ 元素个数`（`subsetSum_kappa_lower_bound`）。
   依据：每个元素编码为一个虚部 = 1 的分支标记，而 ReachablePath 语义强制
   每条接受路径逐符号消费整个输入，故每条路径至少触发「元素个数」次非确定性
   分支，分支-激活引理将其转化为同等数量的生成元激活。
3. 故子集和 ∉ P_F（`subsetSum_not_in_P_F`）：restricted 验证器的 kappa 恒为 0，
   与点态下界 κ ≥ 1 矛盾。
4. 反证：若 P_F = NP_F，由 1 知子集和 ∈ P_F，与 3 矛盾。故 P_F ≠ NP_F。

语义定位（论文第 7 节；以下均为定位结论，非待办）：

- **F4/CBTM 框架内**：`P_F ≠ NP_F` 可证（本文件）。这一证明依赖 CBTM 内建的
  「不可公度性」语义——虚部标记使非确定性分支在代数上不可归约，从而 κ 可定义
  且可累积。
- **NTM2 ↔ CBTM 语义差异（论文定位第 3 点，声明）**：`StructIsoNTM2CBTM`/
  `NTM2.toCBTM` 是结构同构——保持状态/转移表/字母表与**语言外延**
  （`StructIso_preserves_accepts`），但两模型语义不同：CBTM 中虚部是符号的内建
  语义位，分支经生成元激活在代数上必然不同（√p_k ∉ ℚ，不可公度性）；NTM2 无虚部
  语义（vb 是位置的函数），`h_branch_rule` 只保证结果集基数为 2，不排除两条分支
  语义相同/汇合。κ、激活生成元、本质维度定义在 CBTM 路径的读符号虚部上，
  **不随结构同构传递**；同构桥只传语言外延。（NTM2 悖论及其 CBTM/IVM 双层消解
  详见 routine.md §2.4。）
重定位裁决记录（2026-08-28 裁决；以下事项均已终止，不是待办）：

- **经典（集合论层）P ≠ NP 的传递：终止**。原计划经「参数化等价定理」
  （`P_cb = P`、`NP_cb = NP`，见 models.C.0.6.tex）把 `P_F ≠ NP_F` 传递为经典
  `P ≠ NP`。P 侧等价在母项目 pvsnp 已形式化（`PvsNP/ParamEquiv.lean`：
  `P_cb0_eq_P_classic`、`P_Bool_eq_P_classic_poly`，含多项式时间对接）；但 NP 侧
  等价（`NP_Bool = NP_classic`）因上述语义差异只能做语言层外延（κ 下界不可随其
  传递），且 Bool 层分离结论 `P_Bool ≠ NP_Bool` 已按裁决取消。本仓库不引入该路线。
- **框架内替代（已闭合）**：pvsnp `PNPClosure`：
  `no_dtm_recognizes_subsetSumF4`——不存在经典 DTM 经 toCBTM 识别 F4 层语言。
- **经典 DTM 操作语义内部**：`P ≠ NP` 不可证——经典 DTM 缺乏「不可公度性作为
  操作语义内在属性」的概念资源（不可公度性元定理），故本质维度 κ 在经典模型中
  不可定义，代数分离论证无法在经典语境内复制。这是定位结论，不是待解决问题。
-/

namespace Mp

open CBTM
open IVM

-- P_F、NP_F、subsetSum_kappa_lower_bound、subsetSum_not_in_P_F 定义于 Mp.SubsetSumReal；
-- subsetSum_in_NP_F 定理化于 Mp.SubsetSumInNP（见证 = subsetSumCBTM）。

/-- CBTM（F4）框架内的分离：子集和 ∈ NP_F 但 ∉ P_F，故 P_F ≠ NP_F。
    反证法：若 P_F = NP_F，由 subsetSum_in_NP_F 得子集和 ∈ P_F，
    与 subsetSum_not_in_P_F' 矛盾。 -/
theorem P_F_neq_NP_F : P_F ≠ NP_F := by
  intro h_eq
  have hSS_in_NP : subsetSumLanguageF4Real ∈ NP_F := subsetSum_in_NP_F
  have hSS_in_P : subsetSumLanguageF4Real ∈ P_F := by
    rw [← h_eq] at hSS_in_NP
    exact hSS_in_NP
  exact subsetSum_not_in_P_F' hSS_in_P

/-- CBTM（F4）框架内的分离结论（别名）。 -/
theorem P_cb_neq_NP_cb : P_F ≠ NP_F := P_F_neq_NP_F

-- 综合定理（含障碍无关）
theorem P_neq_NP_with_barriers :
    P_F ≠ NP_F ∧
    (∀ O : Oracle, FessentialDimension (languageWithOracle subsetSumLanguageF4Real O) 100 =
      FessentialDimension subsetSumLanguageF4Real 100) ∧
    (∀ A : AlgebraicOracle, FessentialDimension
      (languageWithAlgebraicOracle subsetSumLanguageF4Real A) 100 =
      FessentialDimension subsetSumLanguageF4Real 100) := by
  constructor
  · exact P_F_neq_NP_F
  · constructor
    · intro O; exact relativizationInvariance subsetSumLanguageF4Real 100 O
    · intro A; exact algebrizationInvariance subsetSumLanguageF4Real 100 A

end Mp
