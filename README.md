# mp —— P ≠ NP 形式化验证工程（Lean 4）

> **版本 v2.3**（交付包 `mp.ver2.3.zip`；版本谱系：v0.1.0 → v1.0 → v2.0 → v2.1 → v2.2 → v2.3）

> **English.** This repository is a complete formalization, in Lean 4 (mathlib), of a proof of **P ≠ NP within the CBTM/IVM framework** (a custom machine model — the separation is framework-internal; see the honest-boundary note below): computational models (canonical non-deterministic Turing machine "NTM2", composite-tape machine "CBTM", essential dimension "IVM"), encodings, the worst-case step bound of the subset-sum verifier (O((|x|+1)²)), and the final separation theorems, including a barriers-refined variant. It additionally formalizes the **symbol-layer (ATM/NTM2) extension**: the classes `P_sym0` / `NP_sym0` with the **set-theoretic separation `P_sym0 ≠ NP_sym0`** (aligned domain; P carried by CBTM0 via the DTM≅CBTM0 isomorphism, NP by NTM2). Terminal state: **0 declared 公理, 0 `sorry`, 0 errors**; the whole library builds with `lake build`.

本工程在 Lean 4（mathlib）中形式化验证一条 **P ≠ NP** 证明链（**框架内**：CBTM/IVM 自定义机器模型下的分离——诚实边界见下文「符号层」一节）：从计算模型与编码、子集和语言下界，到验证器最坏步数界（O((|x|+1)²)），直至分离主定理及其障碍版。所有推理链以 `def`/`lemma`/`theorem` 全程机器验证。

## 终态快照（2026-09-14）

| 项 | 状态 |
|---|---|
| 全库构建 | ✅ `lake build` —— 8712 jobs，0 error |
| 声明公理 | ✅ **0**（全库 `Mp/*.lean` 无任何公理声明） |
| 缺口 | ✅ **0**（无 `sorry` / `admit`） |
| 公理足迹 | `propext` / `Classical.choice` / `Quot.sound` + `native_decide` 标准信任面（既有账，逐件量化记录） |
| 交叉复核 | ✅ 构建矩阵（Q10 / Reverse15 / Reverse13A / T16）+ 全库构建 + 声明公理/缺口扫描——经独立脚本与独立复编两通道通过 |
| 符号层分离结论 | ✅ **`P_sym0 ≠ NP_sym0`**（集合论意义，对齐域）——`Mp/ATMAssembly.lean` |

规模：**57 个 Lean 文件 / 99,818 行**（`Mp/` 56 个源文件 + 顶层 `Mp.lean`）。

## 符号层：P_sym0 ≠ NP_sym0（集合论意义，对齐域）

**结论**：在符号输入图灵机层（ATM / NTM2）上，符号层多项式类满足

> **`P_sym0 ≠ NP_sym0`** —— 集合论意义：两个语言类的集合不相等。

见证语言 = **子集和**（`subsetSumLanguageF4Real`）：它**属于** `NP_sym0`（见证机 = `subsetSumNTM2`，即 CBTM1≅NTM2 同构解机），而**不属于** `P_sym0`。

**两类如何承载**（`Mp/ATMAssembly.lean`）：

- **P 类（CBTM0 承载）**：`IsP_sym0 L := ∃ M : CBTM, IsRestricted M ∧ isPolynomialTimeAligned M ∧ (∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))`。
  即：受限 CBTM（字母表 ⊆ {zero,one}，虚部=0 层）—— 正是 **「DTM ≅ CBTM0 ⇒ κ=0 传递」的类层形式**（同构双向均已定理化：`exists_CBTM0_iso_DTM` / `exists_ClassicDTM_iso_restrictedCBTM`）。
- **NP 类（NTM2 承载）**：`IsNP_sym0 L := ∃ A : NTM2, NTM2.isPolynomialTimeAligned A ∧ (∀ w, IsSymbolAligned w → (NTM2.acceptsTape A w ↔ L w))`。

**「对齐域」的含义**：判定域 = 符号对齐串（`IsSymbolAligned w := ∃ wS, w = flat4F4 wS`，即 4F4 计算符号串）。类成员资格与机器性质只在该域内断言——非对齐串上语言与机器均无约束（4 带机无半符号，缺项输入语义已失；数计一体口径）。

**分离链（自顶向下，均有代码锚点）**：

1. CBTM1 多项式求解子集和（`subsetSumCBTM` 族）；
2. CBTM1 ≅ NTM2 ⇒ ∃ NTM2 求解（`subsetSumNTM2`；iso + 输入桥：两层编码同词）；
3. 分支语义相异证书（桥件）：
   - **T2**：`pathValue_separated`（`Mp/ATMTransfer.lean`）——激活模式不同 ⇒ 路径值不同（素数平方根 ℚ-线性独立）——「两条路径完全分开」的代数形式；
   - **T1**：`iso_path_forward_forkCount` + `iso_vbAt_iff_card_two` —— iso 路径对应下 NTM2 分叉计数 = CBTM 分支计数（读符号恒等翻译）；
4. DTM ≅ CBTM0 ⇒ κ=0 传递（`subsetSum_not_in_P_sym0`）：受限机（无虚部读取能力）⇒ 可达读全 im-false ⇒ **κ = 0**；而子集和的任何正确机须读每个虚部标记格 ⇒ **κ ≥ n**（`subsetSum_kappa_lower_bound`）⇒ 取 n = 1 的实例矛盾 ⇒ 子集和 ∉ P 类；
5. 组装：子集和 ∈ NP 类 且 ∉ P 类 ⇒ **`P_sym0_neq_NP_sym0`**（`Mp/ATMAssembly.lean`）。

**诚实边界**：结论的语义基础是 CBTM/IVM 框架的内建语义（虚部 = 分支；不可公度性 √p_i ∉ ℚ 保证两条路径在 IVM 中完全分开）。**脱离框架、仅在经典框架下无法证明**：NTM2 的分支可能是假分支（形式两分支、语义一分支）——语义超越语法，假分支不可排除。这正是本结论必须经由框架的原因。（与 Spec 约定 22、§7.7 一致。）

**与经典 P≠NP 的距离**：本结论**弱于**经典 P ≠ NP——受限机类 ⊆ 一般确定性机类（`P_sym0` ⊆ 经典 P 类）；且经典 P 类定义中的机器**只读符号串，sep/# 与数据不可区分**（结构身份为外部命名；区分结构需表示能力，|Σ| ≥ 4——信息论，Spec 约定 20），故与经典层的对比须经编码桥。另注：**一般确定性机可在指数时间内解出子集和**——对一般确定性机，「解不了」只在多项式时间约束下成立；该口径下的分离不在本工程已证范围。

**与 F 层的关系**：本结论与 F 层 `P_F ≠ NP_F` 是**同一定理的两种表述**（`isP_sym0_iff_isP_F` 为定义级相等，`subsetSum_not_in_P_sym0` 即 `subsetSum_not_in_P_F`）——同一分离的两种命名（符号层 / F 层）；定位细则见 Spec 约定 29、§7.7。

## 证明链（自顶向下）

- **分离主定理**（`Mp/FinalProof.lean`）：`P_F_neq_NP_F`（:93）、`P_cb_neq_NP_cb`（:102）、`P_neq_NP_with_barriers`（:105，障碍版）
- **符号层分离**（`Mp/ATMAssembly.lean`）：`P_sym0_neq_NP_sym0`（集合论意义，对齐域）；类定义 `IsP_sym0`/`IsNP_sym0`；成员 `subsetSum_in_NP_sym0`、`subsetSum_not_in_P_sym0`
- **符号层机器与桥**：`Mp/ATMBasic.lean`（ATM 谓词、运行语义、格移计量、多带视图）、`Mp/ATMBridge.lean`（2bit 码转换、DTM≅CBTM0 双向同构）、`Mp/ATMTransfer.lean`（T1 位置桥 + T2 代数分开）
- **求解链**：`Mp/SubsetSumInNP.lean` —— `subsetSum_in_NP_F`；A2 同构桥 `NTM2_solve_implies_IsNP_F`
- **下界**：`Mp/SubsetSumReal.lean` —— `subsetSum_kappa_lower_bound`；`Mp/PrimeSqrtLinearIndep.lean`
- **验证器最坏步数界**：`Mp/SubsetSumVerifier*.lean` 族 —— Q10 装配（三条款规范化 `NTM2.Canonical`）、T16 尾缀无关性，以及 Core / Reverse / PosBound / StepBound / CBTM 系列段级引理
- **计算模型与障碍**：`Mp/Basic.lean`（NTM2）、`Mp/CBTM.lean`（复合带图灵机）、`Mp/IVM.lean`（本质维度 κ）、`Mp/EssentialDimension.lean`、`Mp/Barriers.lean`

## 构建

需要 [elan](https://github.com/leanprover/elan)（Lean 4 工具链管理器）；工具链版本由 `lean-toolchain` 固定（Lean `v4.32.2`，mathlib `v4.32.2`）。

```bash
lake exe cache get   # mathlib 预编译缓存（可选，强烈建议）
lake build
```

## 文档

- `Spec.md` —— 项目规格与约定总纲（符号层类与分离结论见约定 31、§7.7）

## 配套论文

`measure.C.0.7.tex`（测度篇）、`models.C.0.6.tex`（模型篇）、`MultiType.C1.2.tex`（理念篇）等（另库发布）。

## 作者与许可

Authors: **Bojin Zheng, Jingwen Zheng** · 许可：**Apache-2.0**（见 `LICENSE`）。
