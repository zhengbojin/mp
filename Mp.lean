/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng
-/


import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.ClassicalFramework
import Mp.EssentialDimension
import Mp.LowerBound
import Mp.Barriers
import Mp.FinalProof
import Mp.SubsetSumVerifierCore
import Mp.SubsetSumVerifierCBTM
import Mp.SubsetSumVerifierCBTM2
import Mp.SubsetSumVerifierCBTM3
import Mp.SubsetSumVerifierCBTM4
import Mp.SubsetSumVerifierCBTM6
import Mp.SubsetSumCompile
import Mp.SubsetSumInNP
import Mp.SubsetSumVerifierPosBound4
import Mp.SubsetSumVerifierPosBound5
import Mp.SubsetSumVerifierT16
import Mp.ATMBasic
import Mp.ATMBridge
import Mp.ATMTransfer
import Mp.ATMAssembly

set_option linter.style.header false

/-!
# PvsNP 项目主入口

按依赖顺序导入各模块：
1. Basic.lean                   — 基础定义（F₄、素数平方根、图灵机组件、语言、复杂度类）
2. InterfaceBridge.lean        — 共享引理与公理集中管理（必须先于 CBTM/IVM）
3. CBTM.lean                    — 复布尔图灵机（分支触发公理、投影约束、伽罗瓦作用）
4. IVM.lean                     — 虚部验证机（动态生成元管理、分支-激活引理、语义展开）
5. EssentialDimension.lean      — 本质维度 κ(L)（良定性、实现无关性、P 类零维定理）
6. Barriers.lean                — 障碍无关性论证（相对化、自然证明、代数化）
7. LowerBound.lean              — NP 完全问题的维度下界（子集和、验证敏感性、归约）
8. ClassicalFramework.lean      — 与经典框架的关系（不可公度性元定理、操作不自足、ZFC 可证性）
9. FinalProof.lean              — P≠NP 的最终证明（反证法、障碍无关性综合、ZFC 可证性）
10. ATMBasic/ATMBridge/ATMTransfer/ATMAssembly — 符号层（ATM/NTM2）类与分离结论
    （P_sym0 ≠ NP_sym0，集合论意义，对齐域；见 Spec §7.7、约定 29/31）

开始做决策：使用四位编码表示子集和示例。

-/
