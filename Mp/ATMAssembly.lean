/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

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
# Mp.ATMAssembly —— 符号层 P≠NP 组装（β1：符号层 P 类以 CBTM0 承载）

2026-09-14 用户裁决：**符号层 P 类以「CBTM0 承载」**——
「DTM≅CBTM0 ⇒ κ=0 传递」的类层落实（对应组装链第 4 步）：

- §1 `IsP_sym0`/`P_sym0`：符号层 P 类（CBTM0 承载；判定域 = 符号对齐串，与 `IsP_F` 同口径）。
- §2 `subsetSum_not_in_P_sym0`：子集和 ∉ 符号层 P 类（F 层定理适配；
  restricted ⇒ κ=0 × 正确 ⇒ κ≥n 的矛盾即为分离引擎）。
- §3 `iso_accepts_forward`：NTM2 → CBTM 接受前向桥（无 hwf 前提——供负载拒绝用）。
- §4 `subsetSumNTM2_correct_on_encodings`：NTM2 侧（subsetSumNTM2）在实例形输入上的判定正确性
  （经同构桥自 CBTM 像搬运；尾缀消去 = hrel2）。
- §5 `subsetSumNTM2_rejects_aligned_nonencoding`：NTM2 侧对对齐非编码串的拒绝。
- §6 `subsetSumNTM2_correct_aligned`：§4+§5 合并 = NTM2 侧对齐域全正确性
  （→ NP 侧成员资格素材；全输入域 ∀x 的余项待裁）。
-/

namespace Mp

open CBTM
open IVM
open SymToF4

-- ============================================================================
-- §1 符号层 P 类（CBTM0 承载）
-- ============================================================================

/-- 符号层 P 类（**CBTM0 承载**；2026-09-14 用户裁决）。
    存在受限 CBTM（= CBTM0，虚部=0 层同构类）在符号对齐域上多项式判定。
    「DTM≅CBTM0 ⇒ CBTM0 的 κ=0 传递到 DTM」的类层形式。 -/
def IsP_sym0 (L : Set (List F4)) : Prop :=
  ∃ M : CBTM, CBTM.IsRestricted M ∧ CBTM.isPolynomialTimeAligned M ∧
    (∀ w : List F4, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))

/-- 符号层 P 类（集合）。 -/
def P_sym0 : Set (Set (List F4)) := { L | IsP_sym0 L }

/-- 与 F 层 `IsP_F` 定义级一致（承载不变，命名区分符号层角色）。 -/
theorem isP_sym0_iff_isP_F (L : Set (List F4)) : IsP_sym0 L ↔ IsP_F L :=
  Iff.rfl

theorem P_sym0_eq_P_F : P_sym0 = P_F :=
  rfl

-- ============================================================================
-- §2 子集和 ∉ 符号层 P 类（CBTM0 承载）
-- ============================================================================

/-- 子集和 ∉ 符号层 P 类（CBTM0 承载）——F 层分离定理的直接适配：
    restricted（无虚部读取能力）⇒ κ=0（`kappa_zero_of_restricted`）
    × 正确性 ⇒ κ≥n（`subsetSum_kappa_lower_bound`）⇒ 矛盾。 -/
theorem subsetSum_not_in_P_sym0 : ¬ IsP_sym0 subsetSumLanguageF4Real :=
  subsetSum_not_in_P_F

-- ============================================================================
-- §3 NTM2 → CBTM 接受前向桥（无 hwf 前提）
-- ============================================================================

/-- NTM2 接受 ⇒ 同构 CBTM 接受（规范 NTM2；(→) 方向不需实例形前提）。 -/
theorem iso_accepts_forward (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M)
    (hcan : NTM2.Canonical A) (x : List F4)
    (h : A.acceptsTape x) : M.tapeAccepts x := by
  rcases h with ⟨π, cfg, hr, hacc⟩
  rcases (iso_path_forward A M iso x hcan π cfg hr) with ⟨π', cfg', hrc', hcfg'⟩
  exact ⟨π', cfg', hrc', by rw [hcfg', iso.h_accept]; exact hacc⟩

-- ============================================================================
-- §4 NTM2 侧判定正确性（实例形输入域；经同构桥自 CBTM 像搬运）
-- ============================================================================

/-- subsetSumNTM2 在实例形输入上的判定正确性：
    x = 编码 ++ 尾缀（任意实例、任意尾缀）⇒ accepts ↔ x ∈ L。
    链：接受 ⇒ CBTM 像接受（iso 前向）⇒ hrel 分解（n≤1）⇒ hrel2 尾缀消去
    ⇒ A 侧接受（iso 反向）⇒ holds（solves_of_canonical）⇒ L；反向对称。 -/
theorem subsetSumNTM2_correct_on_encodings :
    ∀ x : List F4,
      (∃ inst : SubsetSumInstance, ∃ gS : List Sym,
        x = encodeInstanceF4 inst ++ flat4F4 gS) →
      (NTM2.acceptsTape subsetSumNTM2 x ↔ subsetSumLanguageF4Real x) := by
  intro x hx
  rcases exists_CBTM_iso_NTM2 subsetSumNTM2 with ⟨M, hM, ⟨iso⟩⟩
  subst M
  have hal : IsSymbolAligned x := by
    rcases hx with ⟨inst, gS, hw⟩
    exact ⟨encodeInstanceSym inst ++ gS, by
      rw [hw]
      simp [encodeInstanceF4, flat4F4, List.flatMap_append]⟩
  constructor
  · -- 接受 ⇒ L
    intro haccA
    have haccC : (NTM2.toCBTM subsetSumNTM2).tapeAccepts x :=
      iso_accepts_forward subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
        subsetSumNTM2_canonical x haccA
    rcases subsetSumNTM2_hrel (NTM2.toCBTM subsetSumNTM2) ⟨iso⟩ x hal haccC with
      ⟨inst, gS, hw, hne, hpos, htarget⟩
    have hacc_enc : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst) := by
      have hacc' : (NTM2.toCBTM subsetSumNTM2).tapeAccepts
          (encodeInstanceF4 inst ++ flat4F4 gS) := by
        simpa [hw] using haccC
      exact (subsetSumNTM2_hrel2 inst hne (encodeElementsSym_nonempty hne) htarget gS).2 hacc'
    have hacc_A : subsetSumNTM2.acceptsTape (encodeInstBits inst) := by
      apply (StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
        subsetSumNTM2_canonical (encodeInstBits inst)
        (by
          refine ⟨inst, ([] : List Sym), ?_⟩
          simp [encodeInstBits, encodeInstanceF4, flat4F4])).2
      simpa [encodeInstBits, ← hw] using hacc_enc
    have hholds : subsetSumHolds inst :=
      (subsetSumNTM2_solves_of_canonical subsetSumNTM2_canonical inst hne hpos htarget).2 hacc_A
    exact ⟨inst, gS, hw, hne, hpos, htarget, hholds⟩
  · -- L ⇒ 接受
    intro hL
    rcases hL with ⟨inst, gS, hw, hne, hpos, htarget, hholds⟩
    have hA : subsetSumNTM2.acceptsTape (encodeInstBits inst) :=
      (subsetSumNTM2_solves_of_canonical subsetSumNTM2_canonical inst hne hpos htarget).1 hholds
    have hb := StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
      subsetSumNTM2_canonical (encodeInstBits inst)
      (by
        refine ⟨inst, ([] : List Sym), ?_⟩
        simp [encodeInstBits, encodeInstanceF4, flat4F4])
    have hcbtm : (NTM2.toCBTM subsetSumNTM2).tapeAccepts
        (ntm2InputToCBTM subsetSumNTM2 (encodeInstBits inst)) :=
      hb.1 hA
    have hcbtm_enc : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst) := by
      simpa [encodeInstBits, ntm2InputToCBTM] using hcbtm
    have hcbtm_w : (NTM2.toCBTM subsetSumNTM2).tapeAccepts x := by
      simpa [hw] using
        (subsetSumNTM2_hrel2 inst hne (encodeElementsSym_nonempty hne) htarget gS).1 hcbtm_enc
    exact (StructIso_preserves_accepts subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
      subsetSumNTM2_canonical x hx).2 hcbtm_w

-- ============================================================================
-- §5 NTM2 侧对齐非编码拒绝
-- ============================================================================

/-- subsetSumNTM2 对对齐非编码串的拒绝（经 iso 前向桥 + CBTM 像拒绝件）。 -/
theorem subsetSumNTM2_rejects_aligned_nonencoding :
    ∀ x : List F4, IsSymbolAligned x →
      (∀ inst : SubsetSumInstance, inst.elements ≠ [] →
        ∀ gS : List Sym, x ≠ encodeInstanceF4 inst ++ flat4F4 gS) →
      ¬ NTM2.acceptsTape subsetSumNTM2 x := by
  intro x hal hnon hacc
  rcases exists_CBTM_iso_NTM2 subsetSumNTM2 with ⟨M, hM, ⟨iso⟩⟩
  subst M
  have haccC : (NTM2.toCBTM subsetSumNTM2).tapeAccepts x :=
    iso_accepts_forward subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) iso
      subsetSumNTM2_canonical x hacc
  exact subsetSumNTM2_rejects_nonencoding x hal hnon haccC

-- ============================================================================
-- §6 NTM2 侧对齐域全正确性（合并）
-- ============================================================================

/-- subsetSumNTM2 对齐域判定正确性（accepts ↔ L；对齐串二分：实例形 / 非编码）。 -/
theorem subsetSumNTM2_correct_aligned :
    ∀ x : List F4, IsSymbolAligned x →
      (NTM2.acceptsTape subsetSumNTM2 x ↔ subsetSumLanguageF4Real x) := by
  intro x hal
  by_cases hdec : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
      x = encodeInstanceF4 inst ++ flat4F4 gS
  · exact subsetSumNTM2_correct_on_encodings x hdec
  · constructor
    · intro hacc
      exact absurd hacc (subsetSumNTM2_rejects_aligned_nonencoding x hal
        (fun inst _ gS hw => hdec ⟨inst, gS, hw⟩))
    · intro hL
      rcases hL with ⟨inst, gS, hw, _hne, _hpos, _htgt, _hholds⟩
      exact absurd ⟨inst, gS, hw⟩ hdec

end Mp
