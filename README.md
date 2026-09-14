# mp —— P ≠ NP 形式化验证工程（Lean 4）

> **English.** This repository is a complete formalization, in Lean 4 (mathlib), of a proof that **P ≠ NP**: computational models (canonical non-deterministic Turing machine "NTM2", composite-tape machine "CBTM", essential dimension "IVM"), encodings, the worst-case step bound of the subset-sum verifier (O((|x|+1)²)), and the final separation theorems, including a barriers-refined variant. Terminal state: **0 axioms, 0 `sorry`, 0 errors**; the whole library builds with `lake build`.

本工程在 Lean 4（mathlib）中形式化验证一条 **P ≠ NP** 证明链：从计算模型与编码、子集和语言下界，到验证器最坏步数界（O((|x|+1)²)），直至分离主定理及其障碍版。所有推理链以 `def`/`lemma`/`theorem` 全程机器验证。

## 终态快照（2026-09-14）

| 项 | 状态 |
|---|---|
| 全库构建 | ✅ `lake build` —— 8708 jobs，0 error |
| 声明公理 | ✅ **0**（全库 `Mp/*.lean` 无任何 `axiom`） |
| 缺口 | ✅ **0**（无 `sorry` / `admit`） |
| 公理足迹 | `propext` / `Classical.choice` / `Quot.sound` + `native_decide` 标准信任面（既有账，逐件量化记录） |
| 交叉复核 | ✅ 构建矩阵（Q10 / Reverse15 / Reverse13A / T16）+ 全库构建 + 声明公理/缺口扫描——经独立脚本与独立复编两通道通过 |

规模：**56 个 Lean 文件 / 约 98,700 行**。

## 证明链（自顶向下）

- **分离主定理**（`Mp/FinalProof.lean`）：
  - `P_F_neq_NP_F`（:93）、`P_cb_neq_NP_cb`（:102）、`P_neq_NP_with_barriers`（:105，障碍版）
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

- `Spec.md` —— 项目规格与约定总纲（V2.1）

## 配套论文

`measure.C.0.7.tex`（测度篇）、`models.C.0.6.tex`（模型篇）、`MultiType.C1.2.tex`（理念篇）等（另库发布）。

## 作者与许可

Authors: **Bojin Zheng, Jingwen Zheng** · 许可：**Apache-2.0**（见 `LICENSE`）。
