/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierCore
import Mp.SubsetSumVerifierCore1
import Mp.SubsetSumVerifierCore2

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
# 子集和验证器：可靠性方向（逆向唯一性 + 最终正确性）

从 borrow_scan14 起的借位链、分支阶段、编码结构、det 唯一性
与 symVerifier_correct 可靠性方向最终拼接。
-/

namespace Mp

open CBTM
open IVM
open F4

/-- 借位右传扫描：状态 14 从 p 起右扫 n 个 data0（逐个翻 1）后读 boundary → 101。 -/
lemma borrow_scan14 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℕ, i < n → (tape (p + (i : ℤ))).1 = SymKind.data0)
    (hbound : tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg, SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) π cfg ∧ cfg.state = 101 := by
  induction n generalizing p tape with
  | zero =>
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      let r : SymTransResult := { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.R }
      let step : SymStep := { fromState := 14, readSym := Sym.boundary, result := r }
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) [step]
          (symStepConfig (SymConfig.mk 14 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 14 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (14, tape p)
          rw [hbound']
          decide
      refine ⟨[step], symStepConfig (SymConfig.mk 14 tape p) step.result, hstep, ?_⟩
      rfl
  | succ n ih =>
      have hdata0 : (tape p).1 = SymKind.data0 := by
        simpa using hdata 0 (by omega : 0 < n + 1)
      cases hsym : tape p with
      | mk k mk' =>
          have hk : k = SymKind.data0 := by
            rw [hsym] at hdata0
            simpa using hdata0
          subst k
          let tape₁ : ℤ → Sym := fun i => if i = p then Sym.data1 mk' else tape i
          let r : SymTransResult := { nextState := 14, writeSym := Sym.data1 mk', moveDir := Dir.R }
          let step : SymStep := { fromState := 14, readSym := Sym.mk SymKind.data0 mk', result := r }
          have hstep : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) [step]
              (symStepConfig (SymConfig.mk 14 tape p) step.result) := by
            refine SymSteps.cons [] step (SymConfig.mk 14 tape p) SymSteps.nil ?_ ?_ ?_
            · rfl
            · change Sym.mk SymKind.data0 mk' = tape p
              rw [hsym]
              simp [Sym.mk]
            · change step.result ∈ VerifierSym.transition (14, tape p)
              rw [hsym]
              rcases mk' with h | h <;> decide
          have hcfg : symStepConfig (SymConfig.mk 14 tape p) step.result = SymConfig.mk 14 tape₁ (p + 1) := by
            simp [symStepConfig, SymConfig.mk, step, r, tape₁, Dir.toInt]
          have hdata₁ : ∀ i : ℕ, i < n → (tape₁ (p + 1 + (i : ℤ))).1 = SymKind.data0 := by
            intro i hi
            rw [show tape₁ (p + 1 + (i : ℤ)) = tape (p + 1 + (i : ℤ)) from by
              dsimp [tape₁]
              rw [if_neg (by omega : p + 1 + (i : ℤ) ≠ p)]]
            have hd := hdata (i + 1) (by omega)
            rw [show p + ((i + 1 : ℕ) : ℤ) = p + 1 + (i : ℤ) from by omega] at hd
            exact hd
          have hbound₁ : tape₁ (p + 1 + (n : ℤ)) = Sym.boundary := by
            rw [show tape₁ (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by
              dsimp [tape₁]
              rw [if_neg (by omega : p + 1 + (n : ℤ) ≠ p)]]
            have hb := hbound
            rw [show p + ((n + 1 : ℕ) : ℤ) = p + 1 + (n : ℤ) from by omega] at hb
            exact hb
          rcases ih (p + 1) tape₁ hdata₁ hbound₁ with ⟨π', cfg', hπ', hs101⟩
          refine ⟨[step] ++ π', cfg', ?_, hs101⟩
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 14 tape p)
            (SymConfig.mk 14 tape₁ (p + 1)) cfg' [step] π' (hcfg ▸ hstep) hπ'

/-- 单比特借位穿出：v_j = 1 且 2^j > 剩余 target 值 → 路径 5→6→7→10→14→101。 -/
lemma process_one_bit_borrow (k j : ℕ) (tbits ebits : List Bool)
    (p_t p_e : ℤ) (tape : ℤ → Sym)
    (htlen : tbits.length = k) (helen : ebits.length = k)
    (hj : j < k)
    (hp_t_le : p_t + (k : ℤ) ≤ p_e)
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (k : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (hvj : tape (p_e + 1 + (j : ℤ)) = Sym.data1)
    (helem_rest : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))))
    (hborrow : 2 ^ j > bitsValue tbits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 101 := by
  have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := hvj
  have hp_t_lt : p_t + (k : ℤ) < p_e := boundary_after_target k j p_t p_e tape tbits (by omega) hj hp_t_le htarget hbound
  have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
  have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
  let r5 : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
  let step5 : SymStep := { fromState := 5, readSym := Sym.data1, result := r5 }
  have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
    rw [hvj']
    decide
  let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
  have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
      (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
    refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.data1 = tape (p_e + 1 + (j : ℤ))
      rw [hvj']
    · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
      rw [hvj']
      decide
  have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
      SymConfig.mk 76 tape1 (p_e + (j : ℤ)) := by
    simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
    omega
  -- 2. 状态 76 左移 j+1 格到 #₀
  have hkeep76 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
      { nextState := 76, writeSym := tape1 i, moveDir := Dir.L } ∈ VerifierSym.transition (76, tape1 i) := by
    intro i h
    have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
    by_cases heq : i = p_e
    · subst i
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      rcases hsel with hd0 | hd1
      · exact trans76_keep (tape p_e) (Or.inr (Or.inl hd0))
      · exact trans76_keep (tape p_e) (Or.inr (Or.inr hd1))
    · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
        refine ⟨(i - (p_e + 1)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
      rcases ioff with ⟨io, hio⟩
      have hio_le : io ≤ j := by omega
      by_cases heqio : io = j
      · subst io
        have hidx : i = p_e + 1 + (j : ℤ) := by omega
        rw [hidx]
        simp [tape1]
        exact trans76_keep Sym.consumed (Or.inl rfl)
      · have hio_lt : io < j := by omega
        have ht := helem_pre io hio_lt
        have hidx : p_e + 1 + (io : ℤ) = i := by omega
        have ht' : tape i = Sym.consumed := by
          rw [hidx] at ht
          exact ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht']
        exact trans76_keep Sym.consumed (Or.inl rfl)
  have hbound6 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
    have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
    rw [hpos]
    rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
    exact hbound
  have hend6 : { nextState := 77, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (76, Sym.boundary) := by decide
  rcases scanLeftKeepPos 76 77 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1 hkeep76 hend6 hbound6
    with ⟨π6, cfg6, hπ6, hs6, hhead6, htape6⟩
  -- 3. 状态 77 左移 (p_e - p_t - 1) 格到 #ₗ
  let n7 : ℕ := (p_e - p_t - 1).toNat
  have hn7 : (n7 : ℤ) = p_e - p_t - 1 := by
    change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
    exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
  have hkeep77 : ∀ i : ℤ, (p_e - 2) - (n7 : ℤ) < i ∧ i ≤ p_e - 2 →
      { nextState := 77, writeSym := tape1 i, moveDir := Dir.L } ∈ VerifierSym.transition (77, tape1 i) := by
    intro i h
    rw [hn7] at h
    have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
    by_cases hlt_target : i < p_t + (k : ℤ)
    · have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = k := by
          simp [targetTape, bitsToSym, htlen, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hj)]
          omega
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_tbits : io < tbits.length := by rw [htlen]; omega
      have hkind : ((targetTape j tbits)[io]).1 = SymKind.data0 ∨ ((targetTape j tbits)[io]).1 = SymKind.data1 := by
        by_cases hioj : io < j
        · have hg := targetTape_getElem_lt j io tbits hio_tbits hioj
          by_cases hb : tbits[io] <;> simp [hg, hb, Sym.data0, Sym.data1, Sym.mk]
        · have hg := targetTape_getElem_ge j io tbits hio_tbits (Nat.le_of_not_gt hioj)
          by_cases hb : tbits[io] <;> simp [hg, hb, Sym.data0, Sym.data1, Sym.mk]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [← ht] at hkind
      exact trans77_keep (tape i) hkind
    · have hpad_i := hpad i (by constructor <;> omega)
      rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
      rw [hpad_i]
      exact trans77_keep Sym.data0 (Or.inl rfl)
  have hbound7 : tape1 ((p_e - 2) - (n7 : ℤ)) = Sym.boundary := by
    have hpos : (p_e - 2) - (n7 : ℤ) = p_t - 1 := by rw [hn7]; omega
    rw [hpos]
    rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
    exact hhashL
  have hend7 : { nextState := 10, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (77, Sym.boundary) := by decide
  rcases scanLeftKeepPos 77 10 Sym.boundary Dir.R n7 (p_e - 2) tape1 hkeep77 hend7 hbound7
    with ⟨π7, cfg7, hπ7, hs7, hhead7, htape7⟩
  -- 4. 状态 10 右移 j 格（4F4.4 前缀）
  have hkeep10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape1 i) := by
    intro i h
    have hi : p_t ≤ i ∧ i < p_t + (k : ℤ) := by constructor <;> omega
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
      refine ⟨(i - p_t).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < (targetTape j tbits).length := by
      have hlen : (targetTape j tbits).length = k := by
        simp [targetTape, bitsToSym, htlen, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hj)]
        omega
      rw [hlen]
      omega
    have ht := htarget io hio_lt
    have hio_j : io < j := by omega
    have hio_tbits : io < tbits.length := by rw [htlen]; omega
    have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
      simp [targetTape, bitsToSym, hio_j, hio_tbits]
    have hidx : p_t + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
    rw [ht, hsym]
    have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
        (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
      by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    exact trans10_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
  rcases scanRightKeep 10 j p_t tape1 hkeep10 with ⟨π10, cfg10, hπ10, hs10, hhead10, htape10⟩
  -- 5. 借位步：10 读 (data0, false) → 14（t_j = 0，因 2^j > bitsValue tbits）
  have hfalse_j : tbits[j] = false := by
    have hdf := drop_all_false_of_lt_pow tbits j (by omega : bitsValue tbits < 2 ^ j)
    have h0lt : 0 < (tbits.drop j).length := by rw [List.length_drop]; omega
    have hdf0 : (tbits.drop j)[0] = false := hdf ((tbits.drop j)[0]) (List.getElem_mem h0lt)
    simpa [List.getElem_drop] using hdf0
  have hj_lt : j < tbits.length := by rw [htlen]; exact hj
  have hlen_tt : (targetTape j tbits).length = tbits.length := by
    dsimp [targetTape, bitsToSym]
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (Nat.le_of_lt hj_lt)]
    omega
  have htape_j : tape (p_t + (j : ℤ)) = Sym.data0 := by
    have ht := htarget j (by rw [hlen_tt]; exact hj_lt)
    simpa [targetTape_getElem_j j tbits hj_lt, hfalse_j] using ht
  have htape1_j : tape1 (p_t + (j : ℤ)) = Sym.data0 := by
    rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by
      dsimp [tape1]
      rw [if_neg (by omega : p_t + (j : ℤ) ≠ p_e + 1 + (j : ℤ))]]
    exact htape_j
  -- 5a. 定位步：10 读 (data0, false) → 11 写 (data0, true) S（t_j = 0，标 m=1，进减法判定）
  -- 5b. 借位步：11 读 (data0, true) → 14 写 (data1, true) R（0-1 借位）
  let r11 : SymTransResult := { nextState := 11, writeSym := Sym.data0 true, moveDir := Dir.S }
  let step11 : SymStep := { fromState := 10, readSym := Sym.data0, result := r11 }
  let r14 : SymTransResult := { nextState := 14, writeSym := Sym.data1 true, moveDir := Dir.R }
  let step14 : SymStep := { fromState := 11, readSym := Sym.data0 true, result := r14 }
  let tape11 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data0 true else tape1 i
  let tape14 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data1 true else tape11 i
  have hstep11 : SymSteps VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) [step11]
      (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step11.result) := by
    refine SymSteps.cons [] step11 (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.data0 = tape1 (p_t + (j : ℤ))
      rw [htape1_j]
    · change step11.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ)))
      rw [htape1_j]
      decide
  have hcfg11 : symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step11.result =
      SymConfig.mk 11 tape11 (p_t + (j : ℤ)) := by
    simp [symStepConfig, SymConfig.mk, step11, r11, tape11, Dir.toInt]
  have hstep14' : SymSteps VerifierSym.transition (SymConfig.mk 11 tape11 (p_t + (j : ℤ))) [step14]
      (symStepConfig (SymConfig.mk 11 tape11 (p_t + (j : ℤ))) step14.result) := by
    refine SymSteps.cons [] step14 (SymConfig.mk 11 tape11 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.data0 true = tape11 (p_t + (j : ℤ))
      simp [tape11]
    · change step14.result ∈ VerifierSym.transition (11, tape11 (p_t + (j : ℤ)))
      simp [tape11]
      decide
  have hcfg14 : symStepConfig (SymConfig.mk 11 tape11 (p_t + (j : ℤ))) step14.result =
      SymConfig.mk 14 tape14 (p_t + (j : ℤ) + 1) := by
    simp [symStepConfig, SymConfig.mk, step14, r14, tape14, Dir.toInt]
  have hstep14 : SymSteps VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) [step11, step14]
      (SymConfig.mk 14 tape14 (p_t + (j : ℤ) + 1)) := by
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ)))
      (SymConfig.mk 11 tape11 (p_t + (j : ℤ))) (SymConfig.mk 14 tape14 (p_t + (j : ℤ) + 1))
      [step11] [step14] (hcfg11 ▸ hstep11) (hcfg14 ▸ hstep14')
  -- 6. 状态 14 右扫穿 #₀ → 101
  let n14 : ℕ := (p_e - p_t - (j : ℤ) - 2).toNat
  have hdata14 : ∀ i : ℕ, i < n14 → (tape14 (p_t + (j : ℤ) + 1 + (i : ℤ))).1 = SymKind.data0 := by
    intro i hi
    have hpos : p_t + (j : ℤ) + 1 + (i : ℤ) < p_e - 1 := by
      have hn14 : (n14 : ℤ) = p_e - p_t - (j : ℤ) - 2 := by
        change ((p_e - p_t - (j : ℤ) - 2).toNat : ℤ) = p_e - p_t - (j : ℤ) - 2
        exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ) - 2)
      omega
    have hne : p_t + (j : ℤ) + 1 + (i : ℤ) ≠ p_t + (j : ℤ) := by omega
    have hne2 : p_t + (j : ℤ) + 1 + (i : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
    rw [show tape14 (p_t + (j : ℤ) + 1 + (i : ℤ)) = tape (p_t + (j : ℤ) + 1 + (i : ℤ)) from by
      dsimp [tape14, tape11, tape1]
      rw [if_neg hne, if_neg hne, if_neg hne2]]
    by_cases hlt_target : p_t + (j : ℤ) + 1 + (i : ℤ) < p_t + (k : ℤ)
    · -- target 位（≥ j+1，全 false → data0）
      have ioff : ∃ io : ℕ, (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t := by
        refine ⟨(p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ p_t + (j : ℤ) + 1 + (i : ℤ) - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_ge : j + 1 ≤ io := by omega
      have hio_lt : io < tbits.length := by
        have : io < k := by omega
        rw [htlen]
        exact this
      have hdf := drop_all_false_of_lt_pow tbits j (by omega : bitsValue tbits < 2 ^ j)
      have hioj_lt : io - j < (tbits.drop j).length := by rw [List.length_drop]; omega
      have hdf_io : (tbits.drop j)[io - j] = false := hdf ((tbits.drop j)[io - j]) (List.getElem_mem hioj_lt)
      have ht := htarget io (by
        rw [hlen_tt]
        exact hio_lt)
      have hidx : p_t + (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) := by omega
      rw [hidx] at ht
      have hioj_bits : io - j < (bitsToSym (tbits.drop j)).length := by
        dsimp [bitsToSym]
        rw [List.length_map]
        exact hioj_lt
      have hio_tt : io < (targetTape j tbits).length := by
        rw [hlen_tt]
        exact hio_lt
      have hsplit : (targetTape j tbits)[io]'hio_tt = (bitsToSym (tbits.drop j))[io - j]'hioj_bits := by
        dsimp [targetTape] at hio_tt
        change ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++ bitsToSym (tbits.drop j))[io]'hio_tt
            = (bitsToSym (tbits.drop j))[io - j]'hioj_bits
        have hlen1 : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj_lt)]
        have hpre : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length ≤ io := by
          rw [hlen1]
          omega
        rw [List.getElem_append_right hpre]
        simp only [show io - ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = io - j from by
          rw [hlen1]]
      have hcell0 : (bitsToSym (tbits.drop j))[io - j]'hioj_bits = Sym.data0 := by
        dsimp [bitsToSym] at hioj_bits ⊢
        have hmap : (List.map (fun b => if b = true then Sym.data1 else Sym.data0) (tbits.drop j))[io - j]'hioj_bits
            = if (tbits.drop j)[io - j]'hioj_lt = true then Sym.data1 else Sym.data0 := by
          rw [List.getElem_map (f := fun b => if b = true then Sym.data1 else Sym.data0)]
        rw [hmap]
        simp [hdf_io]
      rw [hsplit, hcell0] at ht
      rw [ht]
      simp [Sym.data0]
    · -- data0 填充
      have hpad_i := hpad (p_t + (j : ℤ) + 1 + (i : ℤ)) (by constructor <;> omega)
      rw [hpad_i]
      simp [Sym.data0]
  have hbound14 : tape14 (p_t + (j : ℤ) + 1 + (n14 : ℤ)) = Sym.boundary := by
    have hn14 : (n14 : ℤ) = p_e - p_t - (j : ℤ) - 2 := by
      change ((p_e - p_t - (j : ℤ) - 2).toNat : ℤ) = p_e - p_t - (j : ℤ) - 2
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ) - 2)
    have hpos : p_t + (j : ℤ) + 1 + (n14 : ℤ) = p_e - 1 := by rw [hn14]; omega
    rw [hpos]
    rw [show tape14 (p_e - 1) = tape (p_e - 1) from by
      dsimp [tape14, tape11, tape1]
      rw [if_neg (by omega : p_e - 1 ≠ p_t + (j : ℤ)), if_neg (by omega : p_e - 1 ≠ p_t + (j : ℤ)),
        if_neg (by omega : p_e - 1 ≠ p_e + 1 + (j : ℤ))]]
    exact hbound
  rcases borrow_scan14 n14 (p_t + (j : ℤ) + 1) tape14 hdata14 hbound14
    with ⟨π14, cfg14, hπ14, hs101⟩
  -- 7. 拼接路径
  have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
  have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 :=
    SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
  have hhead6' : cfg6.headPos = p_e - 2 := by
    rw [hhead6]
    simp [Dir.toInt]
    omega
  have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
    rw [← hs6, ← htape6, ← hhead6']
  have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
    rw [hcfg6_eq]
    exact hπ7
  have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
  have hhead7' : cfg7.headPos = p_t := by
    rw [hhead7, hn7]
    simp [Dir.toInt]
    omega
  have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
    rw [← hs7, ← htape7, ← hhead7']
  have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
    rw [hcfg7_eq]
    exact hπ10
  have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
  have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
    rw [← hs10, ← htape10, ← hhead10]
  have hstep14'' : SymSteps VerifierSym.transition cfg10 [step11, step14] (SymConfig.mk 14 tape14 (p_t + (j : ℤ) + 1)) := by
    rw [hcfg10_eq]
    exact hstep14
  have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ [step11, step14]) (SymConfig.mk 14 tape14 (p_t + (j : ℤ) + 1)) :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) [step11, step14] h567'' hstep14''
  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ [step11, step14] ++ π14) cfg14 :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step11, step14]) π14 h567''' hπ14
  refine ⟨[step5] ++ π6 ++ π7 ++ π10 ++ [step11, step14] ++ π14, cfg14, htotal, hs101⟩

/-- 减法循环借位版本：bitsValue tbits < 2^j * bitsValue ebits 时，逐位减必在某位借位穿出 → 101。 -/
lemma subtract_loop_borrow (tbits ebits : List Bool) (j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (htlen : tbits.length = j + ebits.length)
    (hp_t_le : p_t + (j + ebits.length : ℤ) ≤ p_e)
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (j + ebits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (helem : tapeAgrees tape (p_e + 1 + (j : ℤ)) (bitsToSym ebits))
    (hsep : tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) = Sym.boundary ∨
            tape (p_e + 1 + ((j + ebits.length : ℕ) : ℤ)) = Sym.data0)
    (hgt : bitsValue tbits < 2 ^ j * bitsValue ebits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 101 := by
  induction ebits generalizing tbits j p_t p_e tape with
  | nil =>
      exfalso
      have hzero : 2 ^ j * bitsValue ([] : List Bool) = 0 := by simp
      rw [hzero] at hgt
      omega
  | cons b rest ih =>
      let ebits_full : List Bool := List.replicate j false ++ (b :: rest)
      have helen_full : ebits_full.length = tbits.length := by
        dsimp [ebits_full]
        rw [List.length_append, List.length_replicate, htlen]
      have hj : j < tbits.length := by
        rw [htlen]
        rw [List.length_cons]
        omega
      have hvj : tape (p_e + 1 + (j : ℤ)) = if b then Sym.data1 else Sym.data0 := by
        have hel := helem 0 (by
          dsimp [bitsToSym]
          exact Nat.zero_lt_succ _)
        simp [bitsToSym] at hel
        exact hel
      have helem_rest_full : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits_full.drop (j + 1))) := by
        have hdrop : ebits_full.drop (j + 1) = rest := by
          dsimp [ebits_full]
          rw [List.drop_append]
          rw [show List.drop (j + 1) (List.replicate j false) = [] from by
            rw [List.drop_eq_nil_of_le (by simp)]]
          rw [show j + 1 - (List.replicate j false).length = 1 from by
            simp [List.length_replicate]]
          rfl
        intro i hi
        have hi' : i < (bitsToSym rest).length := by
          rw [hdrop] at hi
          exact hi
        have hlen_bits : (bitsToSym (b :: rest)).length = 1 + (bitsToSym rest).length := by
          dsimp [bitsToSym]
          simp [List.length_map]
          omega
        have hel := helem (i + 1) (by
          rw [hlen_bits]
          omega)
        have hidx : p_e + 1 + (j : ℤ) + ((i : ℤ) + 1) = p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ) := by omega
        have hidx_b : i + 1 < (bitsToSym (b :: rest)).length := by
          rw [hlen_bits]
          omega
        have hdrop_b : (bitsToSym (b :: rest))[i + 1] = (bitsToSym rest)[i] := by
          simp [bitsToSym, List.getElem_map]
        simpa [hidx, hdrop, hdrop_b] using hel
      have hpad_full : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0 := by
        intro i hi
        have hi' : p_t + (↑j + ↑((b :: rest).length)) ≤ i ∧ i < p_e - 1 := by
          constructor
          · rw [htlen, Nat.cast_add] at hi
            exact hi.1
          · exact hi.2
        exact hpad i hi'
      by_cases hfail : b = true ∧ 2 ^ j > bitsValue tbits
      · -- 本位借位穿出
        rcases hfail with ⟨hb, hborrow⟩
        have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hb] using hvj
        have hgt' : bitsValue tbits < 2 ^ j := by omega
        rcases process_one_bit_borrow tbits.length j tbits ebits_full p_t p_e tape rfl helen_full hj (by simpa [htlen] using hp_t_le)
            hbound hpad_full htarget hhashL hsel helem_pre hvj' helem_rest_full hgt'
          with ⟨π, cfg', hπ, hs101⟩
        exact ⟨π, cfg', hπ, hs101⟩
      · -- 本位成功：hgt 推出 rest ≠ []，递归
        have hsub : (if b then 2 ^ j else 0) ≤ bitsValue tbits := by
          by_cases hb : b
          · have hle' : 2 ^ j ≤ bitsValue tbits := by
              have hnot : ¬(2 ^ j > bitsValue tbits) := by intro h'; exact hfail ⟨hb, h'⟩
              omega
            simpa [hb] using hle'
          · simp [hb]
        have hrest_ne : rest ≠ [] := by
          intro hrest'
          subst rest
          have hgt'' : bitsValue tbits < 2 ^ j * bitsValue [b] := hgt
          by_cases hb : b
          · have hle' : 2 ^ j ≤ bitsValue tbits := by simpa [hb] using hsub
            simp [hb] at hgt''
            omega
          · simp [hb] at hgt''
        rcases process_one_bit tbits.length j b tbits ebits_full p_t p_e tape rfl helen_full hj (by simpa [htlen] using hp_t_le)
            hbound hpad_full htarget hhashL hsel helem_pre hvj helem_rest_full
            (by simpa [htlen] using hsep) hsub
          with ⟨π₁, cfg₁, hπ₁, hstate₁, hta₁, hcons₁, hrest₁, hsel₁, hhashL₁, hbound₁, hkeep₁, hpe_eq₁, hpad_keep₁, hright₁⟩
        let tbits' : List Bool := if b then (subOneAt j tbits).getD tbits else tbits
        have htbits'_eq : tbits' = subAllBitsAt tbits [b] j := by
          simp [tbits', subAllBitsAt]
        have htlen' : tbits'.length = (j + 1) + rest.length := by
          have hlen_t : tbits'.length = tbits.length := by
            rw [htbits'_eq]
            exact subAllBitsAt_length tbits [b] j
          rw [hlen_t, htlen]
          rw [show (b :: rest).length = rest.length + 1 from rfl]
          omega
        have hgt' : bitsValue tbits' < 2 ^ (j + 1) * bitsValue rest := by
          have hval : bitsValue tbits' = bitsValue tbits - (if b then 2 ^ j else 0) := by
            by_cases hb : b
            · have hval' := subAllBitsAt_value tbits [b] j (by simpa [hb, bitsValue] using hsub)
              rw [← htbits'_eq] at hval'
              have hb_val : bitsValue [b] = 1 := by simp [hb]
              simpa [hb, hb_val] using hval'
            · have hval' := subAllBitsAt_value tbits [b] j (by simp [hb])
              rw [← htbits'_eq] at hval'
              have hb_val : bitsValue [b] = 0 := by simp [hb]
              simpa [hb, hb_val] using hval'
          by_cases hb : b
          · -- b = true
            have hbval : bitsValue (b :: rest) = 1 + 2 * bitsValue rest := by simp [hb]
            have hgt0 : bitsValue tbits < 2 ^ j * (1 + 2 * bitsValue rest) := by
              simpa [hbval] using hgt
            have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
              rw [pow_succ]
              ring
            rw [hval]
            simp [hb]
            rw [← hpow]
            have hgt0' : bitsValue tbits < 2 ^ j + 2 ^ j * (2 * bitsValue rest) := by
              simpa [mul_add] using hgt0
            have hle' : 2 ^ j ≤ bitsValue tbits := by simpa [hb] using hsub
            omega
          · -- b = false
            have hbval : bitsValue (b :: rest) = 2 * bitsValue rest := by simp [hb]
            have hgt0 : bitsValue tbits < 2 ^ j * (2 * bitsValue rest) := by
              simpa [hbval] using hgt
            have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
              rw [pow_succ]
              ring
            rw [hval]
            simp [hb]
            rw [← hpow]
            exact hgt0
        have htarget' : tapeAgrees cfg₁.tape p_t (targetTape (j + 1) tbits') := by
          simpa [tbits'] using hta₁
        have helem_pre' : ∀ i : ℕ, i < j + 1 → cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
          intro i hi
          exact hcons₁ i (by omega)
        have helem_rest' : tapeAgrees cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym rest) := by
          have hdrop : ebits_full.drop (j + 1) = rest := by
            dsimp [ebits_full]
            rw [List.drop_append]
            rw [show List.drop (j + 1) (List.replicate j false) = [] from by
              rw [List.drop_eq_nil_of_le (by simp)]]
            rw [show j + 1 - (List.replicate j false).length = 1 from by
              simp [List.length_replicate]]
            rfl
          simpa [hdrop] using hrest₁
        have hsep' : cfg₁.tape (p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ)) = Sym.boundary ∨
            cfg₁.tape (p_e + 1 + ((j + 1 + rest.length : ℕ) : ℤ)) = Sym.data0 := by
          have hlen_eq : ((j + 1 + rest.length : ℕ) : ℤ) = (tbits.length : ℤ) := by
            rw [htlen]
            norm_num
            ring
          rw [hlen_eq]
          rw [hkeep₁]
          simpa [htlen] using hsep
        have hp_t_le' : p_t + ((j + 1) + rest.length : ℤ) ≤ p_e := by
          rw [List.length_cons, Nat.cast_add] at hp_t_le
          omega
        have hbound' : cfg₁.tape (p_e - 1) = Sym.boundary := hbound₁
        have hpad' : ∀ i : ℤ, p_t + ((j + 1) + rest.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg₁.tape i = Sym.data0 := by
          intro i hi
          have hlen : tbits'.length = tbits.length := by
            rw [htbits'_eq]
            exact subAllBitsAt_length tbits [b] j
          have hi' : p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 := by
            constructor
            · rw [htlen', Nat.cast_add]
              exact hi.1
            · exact hi.2
          rw [hlen] at hi'
          exact hpad_keep₁ i hi'
        have hhashL' : cfg₁.tape (p_t - 1) = Sym.boundary := hhashL₁
        rcases ih (tbits := tbits') (j := j + 1) (p_t := p_t) (p_e := p_e) (tape := cfg₁.tape)
            (htlen := htlen') (hp_t_le := hp_t_le') (hbound := hbound') (hpad := hpad')
            (htarget := htarget') (hhashL := hhashL') (hsel := hsel₁)
            (helem_pre := helem_pre') (helem := helem_rest') (hsep := hsep') (hgt := hgt')
          with ⟨π₂, cfg₂, hπ₂, hs101₂⟩
        have hstate₁5 : cfg₁.state = 5 := by
          rcases hstate₁ with h84 | h5
          · exfalso
            rcases h84 with ⟨hst84, hhp84, hb84⟩
            rcases List.ne_nil_iff_exists_cons.mp hrest_ne with ⟨w, ws, rfl⟩
            have h0 : cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (if w then Sym.data1 else Sym.data0) := by
              have h := helem_rest' 0 (by dsimp [bitsToSym]; exact Nat.zero_lt_succ _)
              simpa [bitsToSym] using h
            rw [h0] at hb84
            by_cases hw : w <;> simp [hw, Sym.boundary, Sym.data1, Sym.data0, Sym.mk] at hb84
          · exact h5.1
        have hhead₁5 : cfg₁.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) := by
          rcases hstate₁ with h84 | h5
          · exfalso
            rcases h84 with ⟨hst84, hhp84, hb84⟩
            rcases List.ne_nil_iff_exists_cons.mp hrest_ne with ⟨w, ws, rfl⟩
            have h0 : cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (if w then Sym.data1 else Sym.data0) := by
              have h := helem_rest' 0 (by dsimp [bitsToSym]; exact Nat.zero_lt_succ _)
              simpa [bitsToSym] using h
            rw [h0] at hb84
            by_cases hw : w <;> simp [hw, Sym.boundary, Sym.data1, Sym.data0, Sym.mk] at hb84
          · exact h5.2.1
        have hcfg₁ : cfg₁ = SymConfig.mk 5 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
          cases cfg₁ with
          | mk s t hp =>
              dsimp [SymConfig.mk]
              rw [show s = 5 from by simpa using hstate₁5]
              rw [show hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) from by simpa using hhead₁5]
              congr 1
        have hπ₂' : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
          rw [hcfg₁]
          exact hπ₂
        refine ⟨π₁ ++ π₂, cfg₂, ?_, hs101₂⟩
        exact SymSteps_trans VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) cfg₁ cfg₂ π₁ π₂ hπ₁ hπ₂'

/-- 单元素减法借位穿出：v > target 剩余 → 路径 4→5→…→14→101。 -/
lemma subtract_element_borrow_reject (tbits ebits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (htlen : tbits.length = ebits.length)
    (hgt : bitsValue tbits < bitsValue ebits)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : tape p_e = Sym.sel)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hsep : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.boundary ∨
            tape (p_e + 1 + (ebits.length : ℤ)) = Sym.data0) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧ cfg'.state = 101 := by
  let r4 : SymTransResult := { nextState := 5, writeSym := Sym.data0, moveDir := Dir.R }
  let step4 : SymStep := { fromState := 4, readSym := Sym.sel, result := r4 }
  have hstep4 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step4]
      (symStepConfig (SymConfig.mk 4 tape p_e) step4.result) := by
    refine SymSteps.cons [] step4 (SymConfig.mk 4 tape p_e) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.sel = tape p_e
      rw [hsel]
    · change step4.result ∈ VerifierSym.transition (4, tape p_e)
      rw [hsel]
      decide
  let tape4 : ℤ → Sym := fun i => if i = p_e then Sym.data0 else tape i
  have hcfg4 : symStepConfig (SymConfig.mk 4 tape p_e) step4.result = SymConfig.mk 5 tape4 (p_e + 1) := by
    simp [symStepConfig, SymConfig.mk, step4, r4, tape4, Dir.toInt]
  have hsel4 : (tape4 p_e).1 = SymKind.data0 := by
    simp [tape4]
  have helem4 : tapeAgrees tape4 (p_e + 1) (bitsToSym ebits) := by
    intro i hi
    have h := helem i hi
    rw [show tape4 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by
      dsimp [tape4]
      rw [if_neg (by omega : p_e + 1 + (i : ℤ) ≠ p_e)]]
    exact h
  have hsep4 : tape4 (p_e + 1 + (ebits.length : ℤ)) = Sym.boundary ∨
      tape4 (p_e + 1 + (ebits.length : ℤ)) = Sym.data0 := by
    rw [show tape4 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
      dsimp [tape4]
      rw [if_neg (by omega : p_e + 1 + (ebits.length : ℤ) ≠ p_e)]]
    exact hsep
  have hgt4 : bitsValue tbits < 2 ^ 0 * bitsValue ebits := by simpa using hgt
  have hp_t_le4 : p_t + (0 + ebits.length : ℤ) ≤ p_e := by
    simpa [htlen] using hp_t_le
  have hpad4 : ∀ i : ℤ, p_t + (0 + ebits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape4 i = Sym.data0 := by
    intro i hi
    rw [show tape4 i = tape i from by
      dsimp [tape4]
      rw [if_neg (by omega : i ≠ p_e)]]
    exact hpad i ⟨(by omega : p_t + (tbits.length : ℤ) ≤ i), hi.2⟩
  have hlen_tt : (targetTape 0 tbits).length = tbits.length := by
    dsimp [targetTape, bitsToSym]
    simp
  have htarget4 : tapeAgrees tape4 p_t (targetTape 0 tbits) := by
    intro i hi
    have hik : i < tbits.length := by rw [hlen_tt] at hi; exact hi
    have h := htarget i hi
    rw [show tape4 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
      dsimp [tape4]
      rw [if_neg (by omega : p_t + (i : ℤ) ≠ p_e)]]
    exact h
  have hbound4 : tape4 (p_e - 1) = Sym.boundary := by
    rw [show tape4 (p_e - 1) = tape (p_e - 1) from by
      dsimp [tape4]
      rw [if_neg (by omega : p_e - 1 ≠ p_e)]]
    exact hbound
  have hhashL4 : tape4 (p_t - 1) = Sym.boundary := by
    rw [show tape4 (p_t - 1) = tape (p_t - 1) from by
      dsimp [tape4]
      rw [if_neg (by omega : p_t - 1 ≠ p_e)]]
    exact hhashL
  have hcfg4' : symStepConfig (SymConfig.mk 4 tape p_e) step4.result = SymConfig.mk 5 tape4 (p_e + 1 + (0 : ℤ)) := by
    simp [symStepConfig, SymConfig.mk, step4, r4, tape4, Dir.toInt]
  rcases subtract_loop_borrow tbits ebits 0 p_t p_e tape4 (by simpa using htlen) hp_t_le4 hbound4 hpad4 htarget4 hhashL4 (Or.inl hsel4)
    (by intro i hi; omega) (by simpa using helem4) (by simpa using hsep4) hgt4
    with ⟨π5, cfg', hπ5, hs101⟩
  refine ⟨[step4] ++ π5, cfg', ?_, hs101⟩
  exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 5 tape4 (p_e + 1 + (0 : ℤ))) cfg' [step4] π5 (hcfg4' ▸ hstep4) hπ5

lemma trans1_next1 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (1, s))
    (hnext : r.nextState = 1) : s.1 ≠ SymKind.boundary ∧ r = SymTransResult.mk 1 s Dir.R := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (1, s) → r.nextState = 1 →
      s.1 ≠ SymKind.boundary ∧ r = SymTransResult.mk 1 s Dir.R := by
    native_decide
  exact hdec s r hr hnext

/-- 状态 1 读 boundary → 2。 -/
lemma trans1_next2 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (1, s))
    (hnext : r.nextState = 2) : s.1 = SymKind.boundary ∧ r = SymTransResult.mk 2 s Dir.R := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (1, s) → r.nextState = 2 →
      s.1 = SymKind.boundary ∧ r = SymTransResult.mk 2 s Dir.R := by
    native_decide
  exact hdec s r hr hnext

/-- 状态 2 的下一步：2（写回/分支）或 3（读 boundary）。 -/
lemma trans2_next2_or_3 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (2, s)) :
    r.nextState = 2 ∨ r.nextState = 3 ∨ r.nextState = 101 := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (2, s) →
      r.nextState = 2 ∨ r.nextState = 3 ∨ r.nextState = 101 := by
    native_decide
  exact hdec s r hr

/-- 状态 2 保持步（写回右移，或 α/β 双分支写 sel/nosel）。 -/
lemma trans2_next2 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (2, s))
    (hnext : r.nextState = 2) :
    (r = SymTransResult.mk 2 s Dir.R ∧ s.1 ≠ SymKind.alpha ∧ s.1 ≠ SymKind.beta ∧ s.1 ≠ SymKind.boundary) ∨
    (r = SymTransResult.mk 2 Sym.sel Dir.R ∧ (s.1 = SymKind.alpha ∨ s.1 = SymKind.beta)) ∨
    (r = SymTransResult.mk 2 Sym.nosel Dir.R ∧ (s.1 = SymKind.alpha ∨ s.1 = SymKind.beta)) := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (2, s) → r.nextState = 2 →
      (r = SymTransResult.mk 2 s Dir.R ∧ s.1 ≠ SymKind.alpha ∧ s.1 ≠ SymKind.beta ∧ s.1 ≠ SymKind.boundary) ∨
      (r = SymTransResult.mk 2 Sym.sel Dir.R ∧ (s.1 = SymKind.alpha ∨ s.1 = SymKind.beta)) ∨
      (r = SymTransResult.mk 2 Sym.nosel Dir.R ∧ (s.1 = SymKind.alpha ∨ s.1 = SymKind.beta)) := by
    native_decide
  exact hdec s r hr hnext

/-- 状态 2 读 boundary → 3。 -/
lemma trans2_next3 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (2, s))
    (hnext : r.nextState = 3) : s.1 = SymKind.boundary ∧ r = SymTransResult.mk 3 s Dir.S := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (2, s) → r.nextState = 3 →
      s.1 = SymKind.boundary ∧ r = SymTransResult.mk 3 s Dir.S := by
    native_decide
  exact hdec s r hr hnext

/-- 状态 3 保持步（写回左移）。 -/
lemma trans3_next3 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (3, s))
    (hnext : r.nextState = 3) : s.1 ≠ SymKind.boundary ∧ r = SymTransResult.mk 3 s Dir.L := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (3, s) → r.nextState = 3 →
      s.1 ≠ SymKind.boundary ∧ r = SymTransResult.mk 3 s Dir.L := by
    native_decide
  exact hdec s r hr hnext

/-- 状态 3 读 boundary → 4。 -/
lemma trans3_next4 (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (3, s))
    (hnext : r.nextState = 4) : s.1 = SymKind.boundary ∧ r = SymTransResult.mk 4 Sym.boundary Dir.R := by
  have hdec : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (3, s) → r.nextState = 4 →
      s.1 = SymKind.boundary ∧ r = SymTransResult.mk 4 Sym.boundary Dir.R := by
    native_decide
  exact hdec s r hr hnext

/-- encodeElementsSymChosen 的所有单元非 boundary。 -/
lemma encodeElementsSymChosen_nonboundary (elems : List ℕ) (sel : List Bool) :
    ∀ s ∈ encodeElementsSymChosen elems sel, s.1 ≠ SymKind.boundary := by
  intro s hs
  unfold encodeElementsSymChosen at hs
  rw [mem_joinLists] at hs
  rcases hs with ⟨l, hl, hs_l⟩
  rw [List.mem_filterMap] at hl
  rcases hl with ⟨x, hx, hl'⟩
  have hx2 : x.2 = true := by
    by_cases hx2 : x.2 = true
    · exact hx2
    · simp [hx2] at hl'
  have hl_eq : l = encodeBitsSymNative x.1 := by
    simpa [hx2] using hl'.symm
  subst l
  have hk : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
    unfold encodeBitsSymNative at hs_l
    rcases List.mem_map.mp hs_l with ⟨d, hd, rfl⟩
    by_cases hd0 : d = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]
  rcases hk with hk | hk <;> rw [hk] <;> decide

/-- encodeBitsSym 的单元 kind ∈ {data0, data1}。 -/
lemma encodeBitsSym_kind (n : ℕ) (j : ℕ) (hj : j < (encodeBitsSym n).length) :
    ((encodeBitsSym n)[j]).1 = SymKind.data0 ∨ ((encodeBitsSym n)[j]).1 = SymKind.data1 := by
  have hj' : j < (Nat.digits 2 n).length := by simpa [encodeBitsSym] using hj
  have hcell : (encodeBitsSym n)[j] =
      (fun d => if d = 0 then Sym.data0 else Sym.data1) ((Nat.digits 2 n)[j]'hj') := by
    unfold encodeBitsSym
    exact List.getElem_map (fun d => if d = 0 then Sym.data0 else Sym.data1)
  rw [hcell]
  by_cases hd0 : (Nat.digits 2 n)[j]'hj' = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]

/-- encodeElementsSym 的分支单元只出现在块开头（前缀长度处；原生可变长编码）。 -/
lemma encodeElementsSym_branch_pos (elems : List ℕ) (i : ℕ)
    (hi : i < (encodeElementsSym elems).length)
    (hbranch : ((encodeElementsSym elems)[i]).1 = SymKind.alpha ∨
      ((encodeElementsSym elems)[i]).1 = SymKind.beta) :
    ∃ j₀ : ℕ, j₀ < elems.length ∧ i = (encodeElementsSym (elems.take j₀)).length := by
  induction elems generalizing i with
  | nil => exfalso; simp [encodeElementsSym] at hi
  | cons v rest ih =>
      cases rest with
      | nil =>
          by_cases hi0 : i = 0
          · refine ⟨0, by simp, by rw [hi0]; rfl⟩
          · exfalso
            have hlen : (encodeElementsSym [v]).length = 1 + (encodeBitsSymNative v).length := by
              unfold encodeElementsSym
              simp
              omega
            have hioj : i - 1 < (encodeBitsSymNative v).length := by
              rw [hlen] at hi
              omega
            have hcell : (encodeElementsSym [v])[i] = (encodeBitsSymNative v)[i - 1] := by
              unfold encodeElementsSym at hi
              change ([Sym.alpha] ++ encodeBitsSymNative v)[i]'hi = (encodeBitsSymNative v)[i - 1]
              have hlen1 : [Sym.alpha].length = 1 := by simp
              have hpre : [Sym.alpha].length ≤ i := by rw [hlen1]; omega
              rw [List.getElem_append_right hpre]
              simp only [show i - [Sym.alpha].length = i - 1 from by rw [hlen1]]
            rw [hcell] at hbranch
            have hk : ((encodeBitsSymNative v)[i - 1]).1 = SymKind.data0 ∨
                ((encodeBitsSymNative v)[i - 1]).1 = SymKind.data1 := by
              have hj' : i - 1 < (Nat.digits 2 v).length := by
                unfold encodeBitsSymNative at hioj
                simpa using hioj
              have hcell' : (encodeBitsSymNative v)[i - 1] =
                  (fun d => if d = 0 then Sym.data0 else Sym.data1) ((Nat.digits 2 v)[i - 1]'hj') := by
                unfold encodeBitsSymNative
                exact List.getElem_map (fun d => if d = 0 then Sym.data0 else Sym.data1)
              rw [hcell']
              by_cases hd0 : (Nat.digits 2 v)[i - 1]'hj' = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]
            rcases hbranch with hα | hβ
            · rcases hk with hd0 | hd1
              · cases hα.symm.trans hd0
              · cases hα.symm.trans hd1
            · rcases hk with hd0 | hd1
              · cases hβ.symm.trans hd0
              · cases hβ.symm.trans hd1
      | cons w rest' =>
          by_cases hi0 : i = 0
          · refine ⟨0, by simp, by rw [hi0]; rfl⟩
          · have hlen : (encodeElementsSym (v :: w :: rest')).length =
                1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest')).length := by
              simp [encodeElementsSym]
              ac_rfl
            by_cases hile : i ≤ (encodeBitsSymNative v).length
            · have hioj : i - 1 < (encodeBitsSymNative v).length := by omega
              have hcell : (encodeElementsSym (v :: w :: rest'))[i] = (encodeBitsSymNative v)[i - 1] := by
                unfold encodeElementsSym at hi
                change ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest'))[i]'hi =
                  (encodeBitsSymNative v)[i - 1]
                have hlt : i < ([Sym.alpha] ++ encodeBitsSymNative v).length := by
                  have h2 : ([Sym.alpha] ++ encodeBitsSymNative v).length = 1 + (encodeBitsSymNative v).length := by
                    simp [List.length_append]
                    ac_rfl
                  rw [h2]
                  omega
                have hcell₁ : ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest'))[i]'hi =
                    ([Sym.alpha] ++ encodeBitsSymNative v)[i] := by
                  simpa [List.append_assoc] using
                    ((List.getElem_append_left' hlt (encodeElementsSym (w :: rest'))).symm)
                rw [hcell₁]
                have hpre : [Sym.alpha].length ≤ i := by
                  have h1 : [Sym.alpha].length = 1 := rfl
                  rw [h1]
                  omega
                rw [List.getElem_append_right hpre]
                congr
              rw [hcell] at hbranch
              have hk : ((encodeBitsSymNative v)[i - 1]).1 = SymKind.data0 ∨
                  ((encodeBitsSymNative v)[i - 1]).1 = SymKind.data1 := by
                have hj' : i - 1 < (Nat.digits 2 v).length := by
                  unfold encodeBitsSymNative at hioj
                  simpa using hioj
                have hcell' : (encodeBitsSymNative v)[i - 1] =
                    (fun d => if d = 0 then Sym.data0 else Sym.data1) ((Nat.digits 2 v)[i - 1]'hj') := by
                  unfold encodeBitsSymNative
                  exact List.getElem_map (fun d => if d = 0 then Sym.data0 else Sym.data1)
                rw [hcell']
                by_cases hd0 : (Nat.digits 2 v)[i - 1]'hj' = 0 <;> simp [hd0, Sym.data0, Sym.data1, Sym.mk]
              rcases hbranch with hα | hβ
              · rcases hk with hd0 | hd1
                · cases hα.symm.trans hd0
                · cases hα.symm.trans hd1
              · rcases hk with hd0 | hd1
                · cases hβ.symm.trans hd0
                · cases hβ.symm.trans hd1
            · have hirest : i - (1 + (encodeBitsSymNative v).length) < (encodeElementsSym (w :: rest')).length := by
                rw [hlen] at hi
                omega
              have hcell : (encodeElementsSym (v :: w :: rest'))[i] =
                  (encodeElementsSym (w :: rest'))[i - (1 + (encodeBitsSymNative v).length)] := by
                unfold encodeElementsSym at hi
                change ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest'))[i]'hi =
                  (encodeElementsSym (w :: rest'))[i - (1 + (encodeBitsSymNative v).length)]
                have hpre : ([Sym.alpha] ++ encodeBitsSymNative v).length ≤ i := by
                  simp [List.length_append]
                  omega
                rw [List.getElem_append_right hpre]
                congr
                simp [List.length_append]
                omega
              have hbr' : ((encodeElementsSym (w :: rest'))[i - (1 + (encodeBitsSymNative v).length)]).1 =
                  SymKind.alpha ∨ ((encodeElementsSym (w :: rest'))[i - (1 + (encodeBitsSymNative v).length)]).1 =
                  SymKind.beta := by
                rw [hcell] at hbranch
                exact hbranch
              rcases ih (i - (1 + (encodeBitsSymNative v).length)) hirest hbr' with ⟨j₀, hj₀, hj₀eq⟩
              refine ⟨j₀ + 1, by rw [List.length_cons]; exact Nat.succ_lt_succ hj₀, ?_⟩
              rw [show (v :: w :: rest').take (j₀ + 1) = v :: (w :: rest').take j₀ from by
                rw [List.take_succ_cons]]
              rw [show i = 1 + (encodeBitsSymNative v).length +
                  (i - (1 + (encodeBitsSymNative v).length)) from by omega]
              rw [hj₀eq]
              rw [encodeElementsSym_cons_eq v (List.take j₀ (w :: rest'))]
              simp [List.length_append]
              by_cases ht : List.take j₀ (w :: rest') = []
              · simp [ht, encodeElementsSym]
                omega
              · omega

end Mp
