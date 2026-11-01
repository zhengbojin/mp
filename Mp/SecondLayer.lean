import Mp.ATMDom
import Mp.MachineIso
import Mp.ATMAssembly

/-!
# 第二层：`P_A ⊆ P_cb`、`P_cb ≠ NP_sym0`、`P_A ≠ NP_A`

计时口径已统一为移动数（2026-11-01 裁决 A）：`CBTM.isPolynomialTimeMoves`
与 `CBTM.isPolynomialTimeAligned` 同形（`cbtmMoveCount` 即 filter 长度），
故 `P_cb ⊆ P_sym0` 直接成立；`P_A ⊆ P_cb` 由机器同构（`MachineIso`）搬运：
接受性（`accepts_iff_p`）、停机（`halts_of_dtm`）、移动数与首达性（`path_bwd`
的加强结论：移动数相同 + `fromState` 序列相同）、空白（`hblank`）、域
（`noMarkDomain ⊆ alignedDomain`）。

**本文件独立于 ATMDom/MachineIso**：后两者不依赖 `ATMAssembly`，层序不冲突。
-/

namespace Mp

open SymToF4

-- ============================================================================
-- §1 `P_cb ⊆ P_sym0` 与 `P_cb ≠ NP_sym0`
-- ============================================================================

/-- `P_cb ⊆ P_sym0`（P_cb 的移动数多项式 ⇒ `isPolynomialTimeAligned`）。 -/
theorem P_cb_subset_P_sym0 : P_cb ⊆ P_sym0 := by
  intro L hL
  rcases hL with ⟨M, hM0, hpoly, _halg, hcorr⟩
  refine ⟨M, hM0.toIsRestricted, ?_, hcorr⟩
  simpa [CBTM.isPolynomialTimeMoves, CBTM.isPolynomialTimeAligned, cbtmMoveCount] using hpoly

/-- 子集和 ∉ `P_cb`（由 `subsetSum_not_in_P_sym0` 与上面的包含）。 -/
theorem subsetSum_not_in_P_cb : ¬ IsP_cb subsetSumLanguageF4Real := by
  intro h
  exact subsetSum_not_in_P_sym0 (P_cb_subset_P_sym0 h)

/-- **第二层分离（CBTM|0 侧）**：`P_cb ≠ NP_sym0`。 -/
theorem P_cb_neq_NP_sym0 : P_cb ≠ NP_sym0 := by
  intro h
  have hNP : subsetSumLanguageF4Real ∈ NP_sym0 := subsetSum_in_NP_sym0
  have hP : subsetSumLanguageF4Real ∈ P_cb := by rw [h]; exact hNP
  exact subsetSum_not_in_P_cb hP

-- ============================================================================
-- §2 `P_A ⊆ P_cb` 与 `P_A ≠ NP_A`
-- ============================================================================

/-- `M.toCBTM hwrite` 与 `M` 的语法同构（状态/转移一致；空白由 `hblank` 对齐）。 -/
noncomputable def toCBTM_iso (M : ClassicDTM)
    (hwrite : ∀ q s, F4.im (M.transition (q, s)).writeSym = false) :
    StructIsoClassicDTM M (M.toCBTM hwrite) where
  h_restricted := (isCBTM0_toCBTM M hwrite).toIsRestricted
  h_states_eq := rfl
  h_start := rfl
  h_accept := rfl
  h_reject := rfl
  h_transition := by
    intro q s hs i
    have hmem : s = F4.zero ∨ s = F4.one := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hs
    rcases hmem with rfl | rfl
    · exact ClassicDTM.toCBTMTrans_zero M q i
    · exact ClassicDTM.toCBTMTrans_one M q i

/-- **`P_A ⊆ P_cb`**：DTM 的 CBTM|0 投影搬运（接受性 / 停机 / 移动数 + 首达性 / 域）。 -/
theorem P_A_subset_P_cb : P_A ⊆ P_cb := by
  intro L hL
  rcases hL with ⟨M, hwrite, hblank, halg, hpoly, hcorrAndAnti⟩
  obtain ⟨hcorr, hAnti⟩ := hcorrAndAnti
  let N : CBTM := M.toCBTM hwrite
  have hiso : StructIsoClassicDTM M N := toCBTM_iso M hwrite
  have hbN : N.blankSym = M.blankSym := by
    simp [N, ClassicDTM.toCBTM, hblank]
  refine ⟨N, isCBTM0_toCBTM M hwrite, ?_, ?_, ?_⟩
  · -- 移动数多项式（首达性由 fromState 序列对应搬运）
    rcases hpoly with ⟨p, hp, hbound⟩
    refine ⟨p, hp, ?_⟩
    intro x _hx π' cfg' hr' hacc' hno'
    obtain ⟨π, cfg, hdtm, hrel, _hlen, hmove, hstates⟩ := path_bwd hiso x hbN π' cfg' hr'
    have haccM : cfg.state ∈ M.acceptStates := by
      rw [hrel.1, ← hiso.h_accept]
      exact hacc'
    have hnoM : ∀ step ∈ π, step.fromState ∉ M.acceptStates := by
      intro step hstep
      have hmem : step.fromState ∈ π'.map (fun s => s.fromState) := by
        rw [← hstates]
        exact List.mem_map_of_mem hstep
      obtain ⟨step', hstep', hfe⟩ := List.mem_map.mp hmem
      rw [← hfe, ← hiso.h_accept]
      exact hno' step' hstep'
    have hb := hbound x π cfg hdtm haccM hnoM
    calc cbtmMoveCount π' = dtmMoveCount π := hmove.symm
      _ ≤ p x.length := hb
  · -- 域内停机
    exact halts_of_dtm hiso hwrite hblank hbN halg
  · -- 正确性（对齐域；含标记输入上双方都拒绝）
    intro w hw
    by_cases hnm : ∀ c ∈ w, F4.im c = false
    · exact (accepts_iff_p hiso hwrite w hnm hblank hbN).symm.trans (hcorr w hw)
    · have hneg : ∃ c ∈ w, F4.im c = true := by
        by_contra h
        apply hnm
        intro c hc
        by_cases hc' : F4.im c = true
        · exact absurd ⟨c, hc, hc'⟩ h
        · simpa using hc'
      have hM : ¬ M.acceptsTape w := hAnti w hw hneg
      constructor
      · intro hN
        exact absurd (accepts_of_cbtm hiso w hbN hN) hM
      · intro hL
        exact absurd ((hcorr w hw).mpr hL) hM

/-- **第二层分离（`P_A ≠ NP_A`）**：子集和 ∈ NP 但 ∉ P_A（`P_A ⊆ P_cb` 且 ∉ P_cb）。 -/
theorem P_A_neq_NP_sym0 : P_A ≠ NP_sym0 := by
  intro h
  have hNP : subsetSumLanguageF4Real ∈ NP_sym0 := subsetSum_in_NP_sym0
  have hPA : subsetSumLanguageF4Real ∈ P_A := by rw [h]; exact hNP
  exact subsetSum_not_in_P_cb (P_A_subset_P_cb hPA)

end Mp
