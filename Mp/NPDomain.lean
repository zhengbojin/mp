import Mp.ATMAssembly

/-!
# NP 两版的关系：全输入域 vs 对齐域

- `IsNP_sym`（`Mp/ATMBasic.lean:175`）：`NTM2` 在**所有** `F4` 串上正确且在多项式界内；
- `IsNP_sym0`（`Mp/ATMAssembly.lean:313`）：`NTM2` 只在 `IsSymbolAligned`（= `flat4F4` 像）上
  保证正确性与时间界，非对齐串上不作任何断言。

本文件给出两件事：

1. **自由方向**：`IsNP_sym L → IsNP_sym0 L`（全域条件限制到子域）——直接可证。
2. **域扩张**（反向）：需要两条显式前提
   - `hL`：`L` 在非对齐域为空；
   - `AlignGuardExtends A A'`：存在一台机器 `A'`，在对齐域上重放 `A`，在非对齐域上恒拒绝，
     且 `A'` 有全域多项式界。
   给定这两条，`IsNP_sym0 L → IsNP_sym L` 成立。

**诚实边界**：去掉 `hL` 时反向**不成立**（`L` 在非对齐域可以任意，而对齐域假设对此无约束）。
`AlignGuardExtends` 的存在性是纯语法构造（前导对齐自检段 + 停机拒收），本文件不构造，
把它作为显式前提列出——这就是「域扩张」剩余的全部工作。
-/

namespace Mp

open SymToF4

-- ============================================================================
-- §1 自由方向：全域 ⇒ 对齐域
-- ============================================================================

/-- NTM2 版：全域多项式界 ⇒ 对齐域多项式界。 -/
theorem ntm2IsPolynomialTimeAligned_of_isPolynomialTime (A : NTM2)
    (h : NTM2.isPolynomialTime A) : NTM2.isPolynomialTimeAligned A := by
  rcases h with ⟨p, hp, hbound⟩
  exact ⟨p, hp, fun x _ π cfg hr ha hno => hbound x π cfg hr ha hno⟩

/-- `NP_sym ⊆ NP_sym0`：全输入域版蕴含对齐域版。 -/
theorem isNP_sym0_of_isNP_sym {L : Set (List F4)} (h : IsNP_sym L) : IsNP_sym0 L := by
  rcases h with ⟨A, hpoly, hcorr⟩
  exact ⟨A, ntm2IsPolynomialTimeAligned_of_isPolynomialTime A hpoly, fun w _ => hcorr w⟩

-- ============================================================================
-- §2 反向：域扩张（带显式前提）
-- ============================================================================

/-- 「对齐自检扩张」：`A'` 在对齐域上与 `A` 判定一致，在非对齐域上恒拒绝。 -/
def AlignGuardExtends (A A' : NTM2) : Prop :=
  (∀ w : List F4, IsSymbolAligned w → (NTM2.acceptsTape A' w ↔ NTM2.acceptsTape A w)) ∧
  (∀ w : List F4, ¬ IsSymbolAligned w → ¬ NTM2.acceptsTape A' w)

/-- **域扩张定理**：`L` 在非对齐域为空 + 存在自检扩张机 ⇒ 对齐域版提升为全输入域版。 -/
theorem isNP_sym_of_isNP_sym0 {L : Set (List F4)}
    (hL : ∀ w : List F4, ¬ IsSymbolAligned w → ¬ L w)
    {A : NTM2} (_hA : NTM2.isPolynomialTimeAligned A)
    (hcorr : ∀ w : List F4, IsSymbolAligned w → (NTM2.acceptsTape A w ↔ L w))
    {A' : NTM2} (hpoly : NTM2.isPolynomialTime A') (hext : AlignGuardExtends A A') :
    IsNP_sym L := by
  refine ⟨A', hpoly, ?_⟩
  intro w
  by_cases hw : IsSymbolAligned w
  · rw [hext.1 w hw, hcorr w hw]
  · constructor
    · intro hacc
      exact absurd hacc (hext.2 w hw)
    · intro hLw
      exact absurd hLw (hL w hw)

/-- 子集和语言的非对齐域为空——这是 `hL` 的候选实例化（该语言由编码像定义）。 -/
theorem subsetSumLanguage_empty_off_aligned :
    ∀ w : List F4, ¬ IsSymbolAligned w → ¬ subsetSumLanguageF4Real w := by
  intro w hw hmem
  obtain ⟨inst, gS, hweq, -⟩ := hmem
  apply hw
  refine ⟨encodeInstanceSym inst ++ gS, ?_⟩
  rw [hweq]
  simp [encodeInstanceF4, flat4F4, List.flatMap_append]


-- ============================================================================
-- §3 全输入域口径下的子集和（唯一前提：自检扩张机存在）
-- ============================================================================

/-- 子集和 ∈ `NP_sym`（全输入域），前提 = 存在对齐自检扩张机。 -/
theorem subsetSum_in_NP_sym_of_guard
    (hguard : ∃ A' : NTM2, NTM2.isPolynomialTime A' ∧ AlignGuardExtends subsetSumNTM2 A') :
    IsNP_sym subsetSumLanguageF4Real := by
  obtain ⟨A', hpoly, hext⟩ := hguard
  exact isNP_sym_of_isNP_sym0 subsetSumLanguage_empty_off_aligned
    subsetSumNTM2_polynomialTimeAligned subsetSumNTM2_correct_aligned hpoly hext

/-- 全输入域口径的 NP 见证：`∃ L, L ∈ NP_sym ∧ L ∉ P_sym0`（P 侧仍为对齐域口径）。 -/
theorem exists_NP_sym_not_P_sym0
    (hguard : ∃ A' : NTM2, NTM2.isPolynomialTime A' ∧ AlignGuardExtends subsetSumNTM2 A') :
    ∃ L : Set (List F4), IsNP_sym L ∧ ¬ IsP_sym0 L :=
  ⟨subsetSumLanguageF4Real, subsetSum_in_NP_sym_of_guard hguard, subsetSum_not_in_P_sym0⟩


-- ============================================================================
-- §4 自足特例：`A' = A`，缺口收敛为「A 在非对齐域恒拒绝」一条
-- ============================================================================

/-- `A' = A` 时，自检扩张退化为「对齐域上自反 + 非对齐域恒拒绝」。 -/
theorem alignGuardExtends_self {A : NTM2}
    (hrej : ∀ w : List F4, ¬ IsSymbolAligned w → ¬ NTM2.acceptsTape A w) :
    AlignGuardExtends A A :=
  ⟨fun _ _ => Iff.rfl, hrej⟩

/-- **自足版域扩张**：若 `A` 本身有全域多项式界、且对非对齐串恒拒绝，
    则 `A` 就是自己的自检扩张机，`IsNP_sym` 直接得到。

    对本工程：`subsetSumNTM2` 的全域多项式界由对齐域界 + 「非对齐串上不存在接受路径」
    即得（`isPolynomialTime` 只约束**接受路径**）；所以剩下的唯一事实是
    `hrej : ∀ w, ¬ IsSymbolAligned w → ¬ NTM2.acceptsTape subsetSumNTM2 w`。 -/
theorem isNP_sym_of_rejects_off_domain {L : Set (List F4)}
    (hL : ∀ w : List F4, ¬ IsSymbolAligned w → ¬ L w)
    {A : NTM2} (hpoly : NTM2.isPolynomialTime A)
    (hcorr : ∀ w : List F4, IsSymbolAligned w → (NTM2.acceptsTape A w ↔ L w))
    (hrej : ∀ w : List F4, ¬ IsSymbolAligned w → ¬ NTM2.acceptsTape A w) :
    IsNP_sym L :=
  isNP_sym_of_isNP_sym0 hL (ntm2IsPolynomialTimeAligned_of_isPolynomialTime A hpoly) hcorr
    hpoly (alignGuardExtends_self hrej)

end Mp
