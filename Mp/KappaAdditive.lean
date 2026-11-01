import Mp.IVM

/-!
# 两段记账可加（论文 `lem:kappa-additive` 的机器层形式化）
-/

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Mp

open List

-- ============================================================================
-- §1 激活索引的基本性质
-- ============================================================================

/-- 激活索引不小于起始编号（索引即步位置，单调）。 -/
lemma activatedGenIndicesOnPathAux_ge (π : ComputationPath) (k : ℕ) :
    ∀ x ∈ activatedGenIndicesOnPathAux π k, k ≤ x := by
  induction π generalizing k with
  | nil =>
      intro x hx
      simp [activatedGenIndicesOnPathAux] at hx
  | cons step rest ih =>
      intro x hx
      cases h : F4.im step.readSym
      · simp only [activatedGenIndicesOnPathAux, h, Bool.false_eq_true, if_false] at hx
        have := ih (k + 1) x hx
        omega
      · simp only [activatedGenIndicesOnPathAux, h, if_true] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact le_rfl
        · have := ih (k + 1) x hx'
          omega

/-- 激活索引无重复（步位置互异）。 -/
lemma activatedGenIndicesOnPathAux_nodup (π : ComputationPath) (k : ℕ) :
    (activatedGenIndicesOnPathAux π k).Nodup := by
  induction π generalizing k with
  | nil => simp [activatedGenIndicesOnPathAux]
  | cons step rest ih =>
      cases h : F4.im step.readSym
      · simp only [activatedGenIndicesOnPathAux, h, Bool.false_eq_true, if_false]
        exact ih (k + 1)
      · simp only [activatedGenIndicesOnPathAux, h, if_true]
        refine List.nodup_cons.mpr ⟨?_, ih (k + 1)⟩
        intro hmem
        have hge := activatedGenIndicesOnPathAux_ge rest (k + 1) k hmem
        omega

/-- 激活索引的个数 = 路径中"读到虚部为真"的步数。 -/
lemma activatedGenIndicesOnPathAux_length (π : ComputationPath) (k : ℕ) :
    (activatedGenIndicesOnPathAux π k).length
      = (π.filter (fun s => F4.im s.readSym)).length := by
  induction π generalizing k with
  | nil => simp [activatedGenIndicesOnPathAux]
  | cons step rest ih =>
      cases h : F4.im step.readSym
      · simp [activatedGenIndicesOnPathAux, h, ih (k + 1)]
      · simp [activatedGenIndicesOnPathAux, h, ih (k + 1)]

-- ============================================================================
-- §2 路径记账：基数 = 标记步数
-- ============================================================================

/-- 路径上激活集合的基数 = 该路径"读到标记格"的步数（论文口径）。 -/
theorem activatedGenSetOnPath_card (π : ComputationPath) :
    (activatedGenSetOnPath π).card
      = (π.filter (fun s => F4.im s.readSym)).length := by
  unfold activatedGenSetOnPath activatedGenIndicesOnPath
  rw [List.toFinset_card_of_nodup (activatedGenIndicesOnPathAux_nodup π 1)]
  exact activatedGenIndicesOnPathAux_length π 1

/-- 路径上无标记步 ⇒ 激活数为 `0`。 -/
theorem activatedGenSetOnPath_card_eq_zero (π : ComputationPath)
    (h : ∀ s ∈ π, F4.im s.readSym = false) :
    (activatedGenSetOnPath π).card = 0 := by
  rw [activatedGenSetOnPath_card]
  have hnil : π.filter (fun s => F4.im s.readSym) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    simp [h s hs]
  simp [hnil]

-- ============================================================================
-- §3 两段记账可加（论文 lem:kappa-additive）
-- ============================================================================

/-- 拼接路径的激活数 = 两段激活数之和（索引为步位置，故不重叠）。 -/
theorem activatedGenSetOnPath_card_append (π₁ π₂ : ComputationPath) :
    (activatedGenSetOnPath (π₁ ++ π₂)).card
      = (activatedGenSetOnPath π₁).card + (activatedGenSetOnPath π₂).card := by
  rw [activatedGenSetOnPath_card, activatedGenSetOnPath_card, activatedGenSetOnPath_card,
      List.filter_append, List.length_append]

/-- **两段记账可加**：若第一段（归约段，受限机、`ι_0` 呈现）读到的符号虚部全假，
    则它不激活任何生成元，整段激活数 = 验证段的激活数。 -/
theorem two_phase_additive (π₁ π₂ : ComputationPath)
    (h₁ : ∀ s ∈ π₁, F4.im s.readSym = false) :
    (activatedGenSetOnPath (π₁ ++ π₂)).card = (activatedGenSetOnPath π₂).card := by
  rw [activatedGenSetOnPath_card_append,
      activatedGenSetOnPath_card_eq_zero π₁ h₁, Nat.zero_add]

end Mp
