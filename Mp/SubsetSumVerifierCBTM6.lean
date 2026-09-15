/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/



import Mp.SubsetSumVerifierCBTM4

set_option linter.auxLemma false

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

set_option maxRecDepth 200000

/-!
# 12 步块分解定理（从 CBTM4 迁出，独立编译迭代）

- `twelve_steps_good_block`：起点相位 0、无陷阱的 12 步路径是好块；
- `accept_path_is_good_block_path`：无陷阱的接受路径按 12 步块分解为 GoodBlockPath。
-/

namespace Mp
open CBTM
namespace SymToF4

/-- symOf4F4 在 symTo4F4 的像上单射：解码回原符号（m 分立：任意 mark 均可解码）。 -/
lemma symOf4F4_symTo4F4_getD_some (s : Sym) {t : Sym}
    (h : symOf4F4 ((symTo4F4 s).getD 0 F4.zero) ((symTo4F4 s).getD 1 F4.zero)
      ((symTo4F4 s).getD 2 F4.zero) ((symTo4F4 s).getD 3 F4.zero) = some t) :
    t = s := by
  rcases s with ⟨k, mk⟩
  cases k <;> cases mk
  all_goals
    simp [symTo4F4, Sym.kindBits, symOf4F4, Sym.data0, Sym.data1, Sym.alpha, Sym.beta,
      Sym.consumed, Sym.boundary, Sym.sel, Sym.nosel, Sym.mk] at h ⊢
  all_goals
    first | done | exact h.symm

/-- Sym 转移表的有效起点状态集合（35个有意义的状态；catch-all 默认 → 101 使所有 0-101 状态都有转移）。 -/
def validStates : Finset ℕ := {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100, 101}

/-- Sym 转移表：起点状态必 ≤ 101（含 catch-all 默认）。 -/
lemma symTransition_q_mem_of_ne101 {q : ℕ} {s : Sym} {r : SymTransResult}
    (hr : r ∈ VerifierSym.transition (q, s)) (hne : r.nextState ≠ 101) :
    q ≤ 101 := by
  by_contra hq
  push Not at hq
  unfold VerifierSym.transition at hr
  dsimp at hr
  have hqnot : q ∉ VerifierSym.legalStates := by
    intro hqin
    have hqle : q ≤ 101 := by
      have hdec : ∀ q ∈ VerifierSym.legalStates, q ≤ 101 := by
        decide
      exact hdec q hqin
    omega
  rw [if_neg hqnot] at hr
  simp only [Finset.mem_singleton] at hr
  subst r
  exact hne rfl


lemma twelve_steps_good_block {w : List F4} {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} (h : TapeSteps subsetSumCBTM w cfgc π cfgc')
    (hlen : π.length = 12)
    (hph0 : (decodeState cfgc.state).2.1 = 0)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    {cfgs : SymConfig} (hcorr : blockCorrespond cfgc cfgs)
    {q : ℕ} (hq : cfgc.state = encodeState q 0 0) (hqle : q ≤ 101)
    {p : ℤ} (hp : cfgc.headPos = 4 * p) :
    ∃ sym : Sym, ∃ r : SymTransResult,
      GoodBlock w cfgc π cfgc' cfgs p q sym r := by
  let sym : Sym := cfgs.tape p
  let cells := symTo4F4 sym
  let c0 := cells.getD 0 F4.zero
  let c1 := cells.getD 1 F4.zero
  let c2 := cells.getD 2 F4.zero
  let c3 := cells.getD 3 F4.zero
  let b01 := bufOf3 c0 F4.zero F4.zero
  let b12 := bufOf3 c0 c1 F4.zero
  let b3 := bufOf3 c0 c1 c2
  -- 1. 拆出 12 步
  rcases tapeSteps_split_last h (by intro h0; simp [h0] at hlen) with
    ⟨step11, π10, cfg11, hπe11, h10, hf11, hr11, ht11, hc11⟩
  rcases tapeSteps_split_last h10 (by
      intro h0
      have : (π10 ++ [step11]).length = 12 := by simpa [hπe11] using hlen
      simp [h0] at this) with
    ⟨step10, π9, cfg10, hπe10, h9, hf10, hr10, ht10, hc10⟩
  rcases tapeSteps_split_last h9 (by
      intro h0
      have : (π9 ++ [step10, step11]).length = 12 := by simpa [hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step9, π8, cfg9, hπe9, h8, hf9, hr9, ht9, hc9⟩
  rcases tapeSteps_split_last h8 (by
      intro h0
      have : (π8 ++ [step9, step10, step11]).length = 12 := by simpa [hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step8, π7, cfg8, hπe8, h7, hf8, hr8, ht8, hc8⟩
  rcases tapeSteps_split_last h7 (by
      intro h0
      have : (π7 ++ [step8, step9, step10, step11]).length = 12 := by simpa [hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step7, π6, cfg7, hπe7, h6, hf7, hr7, ht7, hc7⟩
  rcases tapeSteps_split_last h6 (by
      intro h0
      have : (π6 ++ [step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step6, π5, cfg6, hπe6, h5, hf6, hr6, ht6, hc6⟩
  rcases tapeSteps_split_last h5 (by
      intro h0
      have : (π5 ++ [step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step5, π4, cfg5, hπe5, h4, hf5, hr5, ht5, hc5⟩
  rcases tapeSteps_split_last h4 (by
      intro h0
      have : (π4 ++ [step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step4, π3, cfg4, hπe4, h3, hf4, hr4, ht4, hc4⟩
  rcases tapeSteps_split_last h3 (by
      intro h0
      have : (π3 ++ [step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step3, π2, cfg3, hπe3, h2, hf3, hr3, ht3, hc3⟩
  rcases tapeSteps_split_last h2 (by
      intro h0
      have : (π2 ++ [step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step2, π1, cfg2, hπe2, h1, hf2, hr2, ht2, hc2⟩
  rcases tapeSteps_split_last h1 (by
      intro h0
      have : (π1 ++ [step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step1, π0, cfg1, hπe1, h0, hf1, hr1, ht1, hc1⟩
  rcases tapeSteps_split_last h0 (by
      intro h0
      have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0] at this) with
    ⟨step0, πn, cfgc0, hπen, hn, hf0, hr0, ht0, hc0⟩
  -- 2. πn = []、cfgc0 = cfgc
  have hπn : πn = [] := by
    have hsum : (πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by
      simpa [hπen, hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
    have hsum' : πn.length + 12 = 12 := by simpa using hsum
    have hlen0 : πn.length = 0 := by omega
    cases πn with
    | nil => rfl
    | cons x xs => simp at hlen0
  have hcfg0 : cfgc0 = cfgc := by
    exact tapeSteps_empty hn hπn
  subst πn
  subst cfgc0
  -- 全块路径形式与各步取出
  have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
    rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
    rfl
  have hg3 : π.get ⟨3, by omega⟩ = step3 := by simpa [hπ']
  have hg9 : π.get ⟨9, by omega⟩ = step9 := by simpa [hπ']
  have hg10 : π.get ⟨10, by omega⟩ = step10 := by simpa [hπ']
  have hg11 : π.get ⟨11, by omega⟩ = step11 := by simpa [hπ']
  -- 起点 4 格取值与虚部
  have hc0v : cfgc.tapeAt (4 * p) = c0 := by
    have hc := hcorr.2.2 p 0 (by norm_num)
    simpa [c0, cells] using hc
  have hc1v : cfgc.tapeAt (4 * p + 1) = c1 := by
    have hc := hcorr.2.2 p 1 (by norm_num)
    simpa [c1, cells] using hc
  have hc2v : cfgc.tapeAt (4 * p + 2) = c2 := by
    have hc := hcorr.2.2 p 2 (by norm_num)
    simpa [c2, cells] using hc
  have hc3v : cfgc.tapeAt (4 * p + 3) = c3 := by
    have hc := hcorr.2.2 p 3 (by norm_num)
    simpa [c3, cells] using hc
  have him0 : F4.im c0 = false := by simpa [c0, cells] using (symTo4F4_im_false_012 sym).1
  have him1 : F4.im c1 = false := by simpa [c1, cells] using (symTo4F4_im_false_012 sym).2.1
  have him2 : F4.im c2 = false := by simpa [c2, cells] using (symTo4F4_im_false_012 sym).2.2
  -- 编码与缓冲恒等式
  have hminq : min q 101 = q := Nat.min_eq_left hqle
  have hb01lt : b01 < regBound := by
    have hb : b01 ≤ 63 := by
      dsimp [b01, bufOf3]
      rcases c0 with ⟨r0, i0⟩
      cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
    exact lt_of_le_of_lt hb (by norm_num)
  have hb12lt : b12 < regBound := by
    have hb : b12 ≤ 63 := by
      dsimp [b12, bufOf3]
      rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
      cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
    exact lt_of_le_of_lt hb (by norm_num)
  have hb3lt : b3 < regBound := by
    have hb : b3 ≤ 63 := by
      dsimp [b3, bufOf3]
      rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
      cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
        simp [F4.zero, F4.one, F4.alpha, F4.beta]
    exact lt_of_le_of_lt hb (by norm_num)
  have hdec0 : decodeState (encodeState q 0 0) = (q, 0, 0) :=
    decodeState_encodeState q 0 0 (by norm_num) (by norm_num)
  have hdec1' : decodeState (encodeState q 1 b01) = (q, 1, b01) :=
    decodeState_encodeState q 1 b01 (by norm_num) hb01lt
  have hdec2' : decodeState (encodeState q 2 b12) = (q, 2, b12) :=
    decodeState_encodeState q 2 b12 (by norm_num) hb12lt
  have hdec3' : decodeState (encodeState q 3 b3) = (q, 3, b3) :=
    decodeState_encodeState q 3 b3 (by norm_num) hb3lt
  have hb01 : b01 = bufOf3s 0 c0 0 := by
    dsimp [b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩
    cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb12 : b12 = b01 + bufOf3s 1 c1 b01 := by
    dsimp [b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
  have hb3 : b3 = b12 + bufOf3s 2 c2 b12 := by
    dsimp [b3, b12, b01, bufOf3, bufOf3s]
    rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
    cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta]
  -- 第 0 步：读 c0（im=false）→ 结果唯一
  have hst0 : step0.fromState = encodeState q 0 0 := by simpa [hq] using hf0
  have hrd0 : step0.readSym = c0 := by
    simpa [hc0v, hp] using hr0
  have hmem0 : step0.result ∈ transition4 (encodeState q 0 0) c0 := by
    have ht0' : step0.result ∈ subsetSumCBTM.transition (cfgc.state, cfgc.tapeAt cfgc.headPos, cfgc.headPos) := ht0
    rw [hq, hp, hc0v] at ht0'
    simpa [subsetSumCBTM] using ht0'
  have hres0 : step0.result = CBTMTransResult.mk (encodeState q 1 b01) c0 Dir.R := by
    dsimp [transition4] at hmem0
    rw [hdec0] at hmem0
    simp [him0, hminq] at hmem0
    simpa [hb01] using hmem0
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
    dsimp
    rw [hp]
    simp [Dir.toInt]
  -- 第 1 步：读 c1
  have hst1 : step1.fromState = encodeState q 1 b01 := by
    have hst1' : step1.fromState = cfg1.state := by simpa using hf1
    rw [hst1']
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
  have hrd1 : step1.readSym = c1 := by
    have hrd1' : step1.readSym = cfg1.tapeAt cfg1.headPos := by simpa using hr1
    rw [hrd1', hp1]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 1) (by rw [hp]; omega)]
    rw [hc1v]
  have hmem1 : step1.result ∈ transition4 (encodeState q 1 b01) c1 := by
    have ht1' : step1.result ∈ subsetSumCBTM.transition (cfg1.state, cfg1.tapeAt cfg1.headPos, cfg1.headPos) := ht1
    rw [show cfg1.state = encodeState q 1 b01 from by simpa [hf1] using hst1] at ht1'
    rw [hp1] at ht1'
    rw [show cfg1.tapeAt (4 * p + 1) = c1 from by simpa [hr1, hp1] using hrd1] at ht1'
    simpa [subsetSumCBTM] using ht1'
  have hres1 : step1.result = CBTMTransResult.mk (encodeState q 2 (b01 + bufOf3s 1 c1 b01)) c1 Dir.R := by
    dsimp [transition4] at hmem1
    rw [hdec1'] at hmem1
    simp [him1, hminq] at hmem1
    simpa using hmem1
  have hp2 : cfg2.headPos = 4 * p + 2 := by
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [hp1]
    simp [Dir.toInt]
    omega
  -- 第 2 步：读 c2
  have hst2 : step2.fromState = encodeState q 2 b12 := by
    have hst2' : step2.fromState = cfg2.state := by simpa using hf2
    rw [hst2']
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [← hb12]
  have hrd2 : step2.readSym = c2 := by
    have hrd2' : step2.readSym = cfg2.tapeAt cfg2.headPos := by simpa using hr2
    rw [hrd2', hp2]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 2) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 2) (by rw [hp]; omega)]
    rw [hc2v]
  have hmem2 : step2.result ∈ transition4 (encodeState q 2 b12) c2 := by
    have ht2' : step2.result ∈ subsetSumCBTM.transition (cfg2.state, cfg2.tapeAt cfg2.headPos, cfg2.headPos) := ht2
    rw [show cfg2.state = encodeState q 2 b12 from by simpa [hf2] using hst2] at ht2'
    rw [hp2] at ht2'
    rw [show cfg2.tapeAt (4 * p + 2) = c2 from by simpa [hr2, hp2] using hrd2] at ht2'
    simpa [subsetSumCBTM] using ht2'
  have hres2 : step2.result = CBTMTransResult.mk (encodeState q 3 (b12 + bufOf3s 2 c2 b12)) c2 Dir.R := by
    dsimp [transition4] at hmem2
    rw [hdec2'] at hmem2
    simp [him2, hminq] at hmem2
    simpa using hmem2
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [hp2]
    simp [Dir.toInt]
    omega
  -- 第 3 步（合成步）
  have hst3 : step3.fromState = encodeState q 3 b3 := by
    have hst3' : step3.fromState = cfg3.state := by simpa using hf3
    rw [hst3']
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [← hb3]
  have hrd3 : step3.readSym = c3 := by
    have hrd3' : step3.readSym = cfg3.tapeAt cfg3.headPos := by simpa using hr3
    rw [hrd3', hp3]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 3) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 3) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + 3) (by rw [hp]; omega)]
    rw [hc3v]
  have hmem3 : step3.result ∈ transition4 (encodeState q 3 b3) c3 := by
    have ht3' : step3.result ∈ subsetSumCBTM.transition (cfg3.state, cfg3.tapeAt cfg3.headPos, cfg3.headPos) := ht3
    rw [show cfg3.state = encodeState q 3 b3 from by simpa [hf3] using hst3] at ht3'
    rw [hp3] at ht3'
    rw [show cfg3.tapeAt (4 * p + 3) = c3 from by simpa [hr3, hp3] using hrd3] at ht3'
    simpa [subsetSumCBTM] using ht3'
  -- symOf4F4 可解码（不可解 → trap → htrap 矛盾）
  have hso : symOf4F4 c0 c1 c2 c3 = some sym := by
    rcases hsymc : symOf4F4 c0 c1 c2 c3 with _ | symc
    · exfalso
      have hmem3n := hmem3
      dsimp [transition4] at hmem3n
      rw [hdec3'] at hmem3n
      simp [b3, hsymc, f4ofBuf_bufOf3] at hmem3n
      by_cases him3 : F4.im c3 <;> simp [him3] at hmem3n
      · rcases hmem3n with h1 | h1
        all_goals
          have htr := htrap 3 (by omega)
          rw [hg3] at htr
          rw [h1] at htr
          have h101 : (decodeState (encodeState 101 4 0)).1 = 101 := by
            rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
          exact (htr h101).elim
      · have htr := htrap 3 (by omega)
        rw [hg3] at htr
        rw [hmem3n] at htr
        have h101 : (decodeState (encodeState 101 4 0)).1 = 101 := by
          rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
        exact (htr h101).elim
    · have hcs := symOf4F4_symTo4F4_getD_some sym (by simpa [c0, c1, c2, c3, cells] using hsymc)
      simpa [hcs] using hsymc
  have hvalid_sym : sym.2 = true → sym.1 = SymKind.data0 ∨ sym.1 = SymKind.data1 ∨ sym.1 = SymKind.alpha ∨
      sym.1 = SymKind.consumed ∨ sym.1 = SymKind.boundary ∨ sym.1 = SymKind.sel ∨
      sym.1 = SymKind.nosel ∨ sym.1 = SymKind.beta := by
    intro _
    cases sym.1 <;> native_decide
  -- 第 3 步的结果包：r、hres3、hr、hqmem、hbranch、hmk
  have hpack : ∃ r : SymTransResult,
      step3.result = CBTMTransResult.mk (encodeState r.nextState 4 (encodeResult r))
        ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L ∧
      r ∈ VerifierSym.transition (q, sym) ∧
      (q ≤ 101) ∧
      (Sym.isBranch sym → q = 2) ∧
      (r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
        r.writeSym.1 = SymKind.alpha ∨ r.writeSym.1 = SymKind.consumed ∨ r.writeSym.1 = SymKind.boundary ∨
        r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨ r.writeSym.1 = SymKind.beta) := by
    by_cases him3 : F4.im c3
    · -- 分支读：q = 2 的 sel/nosel 双结果（q≠2 为 trap，htrap 排除）
      have hbr : Sym.isBranch sym := by
        dsimp [Sym.isBranch]
        rw [← symTo4F4_getD3_im_eq_isBranch sym]
        simpa [c3, cells] using him3
      have hmem3b := hmem3
      dsimp [transition4] at hmem3b
      rw [hdec3'] at hmem3b
      simp [b3, him3, hso, f4ofBuf_bufOf3] at hmem3b
      by_cases hqs2 : min q 101 = 2
      · have hq2 : q = 2 := by
          rw [hminq] at hqs2
          exact hqs2
        simp [hqs2] at hmem3b
        split at hmem3b
        · -- α:sel/nosel 双结果
          rename_i hcond
          have hc0' : c0 = F4.zero := by
            have hfab : f4ofBuf b3 = (c0, c1, c2) := f4ofBuf_bufOf3 c0 c1 c2
            simpa [hfab] using hcond.1
          have hm : sym.2 = false := by
            have hc3re : F4.re ((symTo4F4 sym)[3]) = false := by
              simpa [c3, cells] using hcond.2
            simpa [symTo4F4, F4.re] using hc3re
          have hα : sym.1 = SymKind.alpha := by
            rcases sym with ⟨sk, mk⟩
            have hdec : ∀ a b c d : F4, ∀ sk : SymKind, ∀ mk : Bool,
                symOf4F4 a b c d = some (sk, mk) → Sym.isBranch (sk, mk) → a = F4.zero →
                sk = SymKind.alpha := by
              native_decide
            exact hdec c0 c1 c2 c3 sk mk (by simpa [c0, c1, c2, c3, cells] using hso) hbr hc0'
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem3b
          rcases hmem3b with hsel | hnosel
          · refine ⟨SymTransResult.mk 2 Sym.sel Dir.R, ?_, ?_, ?_, ?_, ?_⟩
            · simpa using hsel
            · rw [hq2]
              simp [transition2_branch_eq sym hα hm]
            · omega
            · intro _
              exact hq2
            · intro hw
              simp [Sym.sel] at hw
          · refine ⟨SymTransResult.mk 2 Sym.nosel Dir.R, ?_, ?_, ?_, ?_, ?_⟩
            · simpa using hnosel
            · rw [hq2]
              simp [transition2_branch_eq sym hα hm]
            · omega
            · intro _
              exact hq2
            · intro hw
              simp [Sym.nosel] at hw
        · -- β:陷阱,与 htrap 矛盾
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem3b
          rcases hmem3b with h1 | h1
          all_goals
            have htr := htrap 3 (by omega)
            rw [hg3] at htr
            rw [h1] at htr
            have h101 : (decodeState (encodeState 101 4 0)).1 = 101 := by
              rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
            exact (htr h101).elim
      · exfalso
        simp [hqs2] at hmem3b
        rcases hmem3b with h1 | h1
        all_goals
          have htr := htrap 3 (by omega)
          rw [hg3] at htr
          rw [h1] at htr
          have h101 : (decodeState (encodeState 101 4 0)).1 = 101 := by
            rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
          exact (htr h101).elim
    · -- 非分支读：rs.image 提取 r
      have hnb : ¬ Sym.isBranch sym := by
        intro hb
        have him3' : F4.im ((symTo4F4 sym).getD 3 F4.zero) = false := by
          simpa [c3, cells] using him3
        rw [symTo4F4_getD3_im_eq_isBranch sym] at him3'
        dsimp [Sym.isBranch] at hb
        rw [hb] at him3'
        cases him3'
      have hmem3b := hmem3
      dsimp [transition4] at hmem3b
      rw [hdec3'] at hmem3b
      simp [b3, him3, hso, f4ofBuf_bufOf3] at hmem3b
      rw [hminq] at hmem3b
      rcases hmem3b with ⟨r, hr, hres3'⟩
      have hres3 : step3.result = CBTMTransResult.mk (encodeState r.nextState 4 (encodeResult r))
          ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L := hres3'.symm
      have hne : r.nextState ≠ 101 := by
        intro hq101
        have htr := htrap 3 (by omega)
        rw [hg3] at htr
        rw [hres3] at htr
        rw [hq101] at htr
        have hregr' : encodeResult r < regBound := by
          dsimp [encodeResult, regBound]
          have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
            rcases r.writeSym with ⟨k, mk⟩
            cases k <;> cases mk <;> simp [skOf]
          have hdir : dirOf r.moveDir < 3 := by
            cases r.moveDir <;> simp [dirOf]
          have hq' : r.nextState ≤ 101 := transition_nextState_le101 q sym hqle r hr
          omega
        have h101 : (decodeState (encodeState 101 4 (encodeResult r))).1 = 101 := by
          rw [decodeState_encodeState 101 4 (encodeResult r) (by norm_num) (by simpa [regBound] using hregr')]
        exact (htr h101).elim
      refine ⟨r, hres3, hr, symTransition_q_mem_of_ne101 hr hne, ?_, ?_⟩
      · intro hb
        exact (hnb hb).elim
      · intro hw
        -- hmk：m 分立（kind 编码不含 m），mark=true 时 kind 只需落在 8 种 kind 之一（恒真）
        have : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 101 →
            r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
              r.writeSym.1 = SymKind.alpha ∨ r.writeSym.1 = SymKind.consumed ∨ r.writeSym.1 = SymKind.boundary ∨
              r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨ r.writeSym.1 = SymKind.beta := by decide
        exact this ⟨q, by omega⟩ sym r hr hne hw
  rcases hpack with ⟨r, hres3, hr, hqmem, hbranch, hmk⟩
  have hstep4 : (π.get ⟨3, by omega⟩).result = CBTMTransResult.mk (encodeState r.nextState 4 (encodeResult r)) ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L := by
    rw [hg3]
    exact hres3
  have hp4 : cfg4.headPos = 4 * p + 2 := by
    rw [hc3]
    dsimp [stepConfig]
    rw [hres3]
    dsimp
    rw [hp3]
    simp [Dir.toInt]
    omega
  -- r 相关的本地缩写与事实
  let nrs := symTo4F4 r.writeSym
  let w0 := nrs.getD 0 F4.zero
  let w1 := nrs.getD 1 F4.zero
  let w2 := nrs.getD 2 F4.zero
  let w3 := nrs.getD 3 F4.zero
  let d := r.moveDir
  let qn := min r.nextState 101
  let regr := encodeResult r
  let tprev := symTo4F4 (cfgs.tape (p - 1))
  let s8 := w0
  let s9 := match d with | Dir.R => w1 | Dir.L => tprev.getD 3 F4.zero | Dir.S => w0
  let s10 := match d with | Dir.R => w2 | Dir.L => tprev.getD 2 F4.zero | Dir.S => w0
  let s11 := match d with | Dir.R => w3 | Dir.L => tprev.getD 1 F4.zero | Dir.S => w0
  have hqle_r : r.nextState ≤ 101 := transition_nextState_le101 q sym hqle r hr
  -- v2：接受路径无 101 步（htrap 3 + hstep4）→ r.nextState ≠ 101
  have hne : r.nextState ≠ 101 := by
    intro hq101
    have htr := htrap 3 (by omega)
    rw [hstep4] at htr
    rw [hq101] at htr
    have hregr' : encodeResult r < regBound := by
      dsimp [encodeResult, regBound]
      have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
        rcases r.writeSym with ⟨k, mk⟩
        cases k <;> cases mk <;> simp [skOf]
      have hdir : dirOf r.moveDir < 3 := by
        cases r.moveDir <;> simp [dirOf]
      have hq' : r.nextState ≤ 101 := hqle_r
      omega
    have h101 : (decodeState (encodeState 101 4 (encodeResult r))).1 = 101 := by
      rw [decodeState_encodeState 101 4 (encodeResult r) (by norm_num) (by simpa [regBound] using hregr')]
    exact (htr h101).elim
  have hregr : regr < 8192 := by
    dsimp [regr, encodeResult]
    have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
      rcases r.writeSym with ⟨k, mk⟩
      cases k <;> cases mk <;> simp [skOf]
    have hdir : dirOf r.moveDir < 3 := by
      cases r.moveDir <;> simp [dirOf]
    omega
  have hdec4' : decodeState (encodeState r.nextState 4 regr) = (r.nextState, 4, regr) := by
    apply decodeState_encodeState
    · norm_num
    · simpa [regBound] using hregr
  have hdecph (ph : ℕ) (hphl : ph < 12) :
      decodeState (encodeState qn ph regr) = (qn, ph, regr) := by
    apply decodeState_encodeState
    · simpa [stepsPerSym] using hphl
    · simpa [regBound] using hregr
  have hqnn : min qn 101 = qn := by
    dsimp [qn]
    exact Nat.min_eq_left (Nat.min_le_right r.nextState 101)
  -- v2：接受路径无 101 步（hne）→ qn = min r.nextState 101 ≠ 101，
  -- 排除 transition4 移动阶段的 q=101 陷阱吸收分支（ad97191 引入）。
  have hqne : qn ≠ 101 := by
    dsimp [qn]
    rw [Nat.min_eq_left hqle_r]
    intro h101
    exact hne h101
  have hmin_r : min r.nextState 101 = r.nextState := Nat.min_eq_left hqle_r
  have hw0 : F4.im w0 = false := by simpa [w0, nrs] using (symTo4F4_im_false_012 r.writeSym).1
  have hw1 : F4.im w1 = false := by simpa [w1, nrs] using (symTo4F4_im_false_012 r.writeSym).2.1
  have hw2 : F4.im w2 = false := by simpa [w2, nrs] using (symTo4F4_im_false_012 r.writeSym).2.2
  -- 第 4 步：写回阶段 phase 4 —— 读 c2（im=false）写 w2 移 L
  have hst4 : step4.fromState = encodeState r.nextState 4 regr := by
    have hst4' : step4.fromState = cfg4.state := by simpa using hf4
    rw [hst4']
    rw [hc3]
    dsimp [stepConfig]
    rw [hres3]
  have hrd4 : step4.readSym = c2 := by
    have hrd4' : step4.readSym = cfg4.tapeAt cfg4.headPos := by simpa using hr4
    rw [hrd4', hp4]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + 2) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_eq cfg2 step2.result (4 * p + 2) (by rw [hp2])]
    rw [hres2]
  have hmem4 : step4.result ∈ transition4 (encodeState r.nextState 4 regr) c2 := by
    have ht4' : step4.result ∈ subsetSumCBTM.transition (cfg4.state, cfg4.tapeAt cfg4.headPos, cfg4.headPos) := ht4
    rw [show cfg4.state = encodeState r.nextState 4 regr from by simpa [hf4] using hst4] at ht4'
    rw [hp4] at ht4'
    rw [show cfg4.tapeAt (4 * p + 2) = c2 from by simpa [hr4, hp4] using hrd4] at ht4'
    simpa [subsetSumCBTM] using ht4'
  have hres4 : step4.result = CBTMTransResult.mk (encodeState qn 5 regr) w2 Dir.L := by
    dsimp [transition4] at hmem4
    rw [hdec4'] at hmem4
    simp [him2] at hmem4
    rw [decodeResult_encodeResult_ok r hmk] at hmem4
    dsimp [qn]
    simpa [w2, nrs] using hmem4
  have hp5 : cfg5.headPos = 4 * p + 1 := by
    rw [hc4]
    dsimp [stepConfig]
    rw [hres4]
    dsimp
    rw [hp4]
    simp [Dir.toInt]
    omega
  -- 第 5 步：phase 5 —— 读 c1 写 w1 移 L
  have hst5 : step5.fromState = encodeState qn 5 regr := by
    have hst5' : step5.fromState = cfg5.state := by simpa using hf5
    rw [hst5']
    rw [hc4]
    dsimp [stepConfig]
    rw [hres4]
  have hrd5 : step5.readSym = c1 := by
    have hrd5' : step5.readSym = cfg5.tapeAt cfg5.headPos := by simpa using hr5
    rw [hrd5', hp5]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + 1) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + 1) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 1) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_eq cfg1 step1.result (4 * p + 1) (by rw [hp1])]
    rw [hres1]
  have hmem5 : step5.result ∈ transition4 (encodeState qn 5 regr) c1 := by
    have ht5' : step5.result ∈ subsetSumCBTM.transition (cfg5.state, cfg5.tapeAt cfg5.headPos, cfg5.headPos) := ht5
    rw [show cfg5.state = encodeState qn 5 regr from by simpa [hf5] using hst5] at ht5'
    rw [hp5] at ht5'
    rw [show cfg5.tapeAt (4 * p + 1) = c1 from by simpa [hr5, hp5] using hrd5] at ht5'
    change step5.result ∈ transition4 (encodeState qn 5 regr) c1 at ht5'
    exact ht5'
  have hres5 : step5.result = CBTMTransResult.mk (encodeState qn 6 regr) ((symTo4F4 r.writeSym).getD 1 F4.zero) Dir.L := by
    dsimp [transition4] at hmem5
    rw [hdecph 5 (by norm_num)] at hmem5
    simp [him1] at hmem5
    rw [decodeResult_encodeResult_ok r hmk] at hmem5
    rw [hqnn] at hmem5
    exact hmem5
  have hp6 : cfg6.headPos = 4 * p := by
    rw [hc5]
    dsimp [stepConfig]
    rw [hres5]
    dsimp
    rw [hp5]
    simp [Dir.toInt]
  -- 第 6 步：phase 6 —— 读 c0 写 w0 移 S
  have hst6 : step6.fromState = encodeState qn 6 regr := by
    have hst6' : step6.fromState = cfg6.state := by simpa using hf6
    rw [hst6']
    rw [hc5]
    dsimp [stepConfig]
    rw [hres5]
  have hrd6 : step6.readSym = c0 := by
    have hrd6' : step6.readSym = cfg6.tapeAt cfg6.headPos := by simpa using hr6
    rw [hrd6', hp6]
    rw [hc5]
    rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p) (by rw [hp5]; omega)]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p) (by rw [hp3]; omega)]
    rw [hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_eq cfgc step0.result (4 * p) (by rw [hp])]
    rw [hres0]
  have hmem6 : step6.result ∈ transition4 (encodeState qn 6 regr) c0 := by
    have ht6' : step6.result ∈ subsetSumCBTM.transition (cfg6.state, cfg6.tapeAt cfg6.headPos, cfg6.headPos) := ht6
    rw [show cfg6.state = encodeState qn 6 regr from by simpa [hf6] using hst6] at ht6'
    rw [hp6] at ht6'
    rw [show cfg6.tapeAt (4 * p) = c0 from by simpa [hr6, hp6] using hrd6] at ht6'
    change step6.result ∈ transition4 (encodeState qn 6 regr) c0 at ht6'
    exact ht6'
  have hres6 : step6.result = CBTMTransResult.mk (encodeState qn 7 regr) ((symTo4F4 r.writeSym).getD 0 F4.zero) Dir.S := by
    dsimp [transition4] at hmem6
    rw [hdecph 6 (by norm_num)] at hmem6
    simp [him0] at hmem6
    rw [decodeResult_encodeResult_ok r hmk] at hmem6
    rw [hqnn] at hmem6
    exact hmem6
  have hp7 : cfg7.headPos = 4 * p := by
    rw [hc6]
    dsimp [stepConfig]
    rw [hres6]
    dsimp
    rw [hp6]
    simp [Dir.toInt]
  -- 第 7 步：phase 7 —— 读 w0 写原符号移 S
  have hst7 : step7.fromState = encodeState qn 7 regr := by
    have hst7' : step7.fromState = cfg7.state := by simpa using hf7
    rw [hst7']
    rw [hc6]
    dsimp [stepConfig]
    rw [hres6]
  have hrd7 : step7.readSym = w0 := by
    have hrd7' : step7.readSym = cfg7.tapeAt cfg7.headPos := by simpa using hr7
    rw [hrd7', hp7]
    rw [hc6]
    rw [stepConfig_tapeAt_eq_of_eq cfg6 step6.result (4 * p) (by rw [hp6])]
    rw [hres6]
  have hmem7 : step7.result ∈ transition4 (encodeState qn 7 regr) w0 := by
    have ht7' : step7.result ∈ subsetSumCBTM.transition (cfg7.state, cfg7.tapeAt cfg7.headPos, cfg7.headPos) := ht7
    rw [show cfg7.state = encodeState qn 7 regr from by simpa [hf7] using hst7] at ht7'
    rw [hp7] at ht7'
    rw [show cfg7.tapeAt (4 * p) = w0 from by simpa [hr7, hp7] using hrd7] at ht7'
    change step7.result ∈ transition4 (encodeState qn 7 regr) w0 at ht7'
    exact ht7'
  have hres7 : step7.result = CBTMTransResult.mk (encodeState qn 8 regr) w0 Dir.S := by
    dsimp [transition4] at hmem7
    rw [hdecph 7 (by norm_num)] at hmem7
    simp [hw0] at hmem7
    rw [hqnn] at hmem7
    rw [hmem7]
  have hp8 : cfg8.headPos = 4 * p := by
    rw [hc7]
    dsimp [stepConfig]
    rw [hres7]
    dsimp
    rw [hp7]
    simp [Dir.toInt]
  -- 第 8 步：移动阶段 phase 8 —— 读 s8 = w0（im=false）→ 唯一，移 d
  have hst8 : step8.fromState = encodeState qn 8 regr := by
    have hst8' : step8.fromState = cfg8.state := by simpa using hf8
    rw [hst8']
    rw [hc7]
    dsimp [stepConfig]
    rw [hres7]
  have hrd8 : step8.readSym = s8 := by
    have hrd8' : step8.readSym = cfg8.tapeAt cfg8.headPos := by simpa using hr8
    rw [hrd8', hp8]
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_eq cfg7 step7.result (4 * p) (by rw [hp7])]
    rw [hres7]
  have hmem8 : step8.result ∈ transition4 (encodeState qn 8 regr) s8 := by
    have ht8' : step8.result ∈ subsetSumCBTM.transition (cfg8.state, cfg8.tapeAt cfg8.headPos, cfg8.headPos) := ht8
    rw [show cfg8.state = encodeState qn 8 regr from by simpa [hf8] using hst8] at ht8'
    rw [hp8] at ht8'
    rw [show cfg8.tapeAt (4 * p) = s8 from by simpa [hr8, hp8] using hrd8] at ht8'
    change step8.result ∈ transition4 (encodeState qn 8 regr) s8 at ht8'
    exact ht8'
  have hres8 : step8.result = CBTMTransResult.mk (encodeState qn 9 regr) w0 (SymToF4.dirOf.match_1 (fun _ : Dir => Dir) r.moveDir (fun _ => Dir.R) (fun _ => Dir.L) (fun _ => Dir.S)) := by
    dsimp [transition4] at hmem8
    rw [hdecph 8 (by norm_num)] at hmem8
    simp [hw0, s8, hqne] at hmem8
    rw [decodeResult_encodeResult_ok r hmk] at hmem8
    rw [hqnn] at hmem8
    rw [hmem8]
  have hp9 : cfg9.headPos = 4 * p + d.toInt := by
    rw [hc8]
    dsimp [stepConfig]
    rw [hres8]
    dsimp
    rw [hp8]
    dsimp [d]
    rcases hd : r.moveDir with _ | _ | _ <;> simp [hd, Dir.toInt]
  -- 块内格值不变量（第 8 步之后）：cfg8 的 4p..4p+3 格 = w0..w3
  have hc8'0 : cfg8.tapeAt (4 * p) = w0 := by
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_eq cfg7 step7.result (4 * p) (by rw [hp7])]
    rw [hres7]
  have hc8'1 : cfg8.tapeAt (4 * p + 1) = w1 := by
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 1) (by rw [hp7]; omega)]
    rw [hc6]
    rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 1) (by rw [hp6]; omega)]
    rw [hc5]
    rw [stepConfig_tapeAt_eq_of_eq cfg5 step5.result (4 * p + 1) (by rw [hp5])]
    rw [hres5]
  have hc8'2 : cfg8.tapeAt (4 * p + 2) = w2 := by
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 2) (by rw [hp7]; omega)]
    rw [hc6]
    rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 2) (by rw [hp6]; omega)]
    rw [hc5]
    rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + 2) (by rw [hp5]; omega)]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_eq cfg4 step4.result (4 * p + 2) (by rw [hp4])]
    rw [hres4]
  have hc8'3 : cfg8.tapeAt (4 * p + 3) = w3 := by
    rw [hc7]
    rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + 3) (by rw [hp7]; omega)]
    rw [hc6]
    rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + 3) (by rw [hp6]; omega)]
    rw [hc5]
    rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + 3) (by rw [hp5]; omega)]
    rw [hc4]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + 3) (by rw [hp4]; omega)]
    rw [hc3]
    rw [stepConfig_tapeAt_eq_of_eq cfg3 step3.result (4 * p + 3) (by rw [hp3])]
    rw [hres3]
    dsimp [w3, nrs]
    rw [← symTo4F4_getD3_eq_lastD r.writeSym]
  -- 第 9-11 步：移动阶段——按 d 分情况（陷阱支用 htrap 排除）
  rcases hd : r.moveDir with _ | _ | _
  · -- d = L
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = s9 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -1) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -1) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -1) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -1) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -1) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -1) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -1) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -1) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -1) (by rw [hp]; omega)]
      rw [show 4 * p + -1 = 4 * (p - 1) + (3 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 3 (by norm_num)]
      dsimp [s9, d, tprev]
      simp [hd]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) s9 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p + -1) = s9 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9' : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L ∨
        step9.result = CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      by_cases him9 : F4.im s9 <;> simp [him9, hqne] at hmem9
      · simpa [hd] using hmem9
      · left
        simpa [hd] using hmem9
    have hnotrap9 : step9.result ≠ CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
      intro h
      have htr := htrap 9 (by omega)
      rw [hg9] at htr
      rw [h] at htr
      have h101 : (decodeState (encodeState 101 10 0)).1 = 101 := by
        rw [decodeState_encodeState 101 10 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L := by
      rcases hres9' with hg | ht
      · exact hg
      · exfalso
        exact hnotrap9 ht
    have hp10 : cfg10.headPos = 4 * p + -2 := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      first | done | omega
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = s10 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + -2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -2) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -2) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -2) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -2) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -2) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -2) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -2) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -2) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -2) (by rw [hp]; omega)]
      rw [show 4 * p + -2 = 4 * (p - 1) + (2 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 2 (by norm_num)]
      dsimp [s10, d, tprev]
      simp [hd]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) s10 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p + -2) = s10 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10' : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L ∨
        step10.result = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      by_cases him10 : F4.im s10 <;> simp [him10, hqne] at hmem10
      · simpa [hd] using hmem10
      · left
        simpa [hd] using hmem10
    have hnotrap10 : step10.result ≠ CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
      intro h
      have htr := htrap 10 (by omega)
      rw [hg10] at htr
      rw [h] at htr
      have h101 : (decodeState (encodeState 101 11 0)).1 = 101 := by
        rw [decodeState_encodeState 101 11 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L := by
      rcases hres10' with hg | ht
      · exact hg
      · exfalso
        exact hnotrap10 ht
    have hp11 : cfg11.headPos = 4 * p + -3 := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
      first | done | omega
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = s11 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + -3) (by rw [hp10]; omega)]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + -3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + -3) (by rw [hp8]; omega)]
      rw [hc7]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * p + -3) (by rw [hp7]; omega)]
      rw [hc6]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * p + -3) (by rw [hp6]; omega)]
      rw [hc5]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * p + -3) (by rw [hp5]; omega)]
      rw [hc4]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * p + -3) (by rw [hp4]; omega)]
      rw [hc3]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * p + -3) (by rw [hp3]; omega)]
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + -3) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + -3) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * p + -3) (by rw [hp]; omega)]
      rw [show 4 * p + -3 = 4 * (p - 1) + (1 : ℕ) by omega]
      rw [hcorr.2.2 (p - 1) 1 (by norm_num)]
      dsimp [s11, d, tprev]
      simp [hd]
    have hmem11 : step11.result ∈ transition4 (encodeState qn 11 regr) s11 := by
      have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
      rw [show cfg11.state = encodeState qn 11 regr from by simpa [hf11] using hst11] at ht11'
      rw [hp11] at ht11'
      rw [show cfg11.tapeAt (4 * p + -3) = s11 from by simpa [hr11, hp11] using hrd11] at ht11'
      simpa [subsetSumCBTM] using ht11'
    have hres11' : step11.result = CBTMTransResult.mk (encodeState qn 0 0) s11 Dir.L ∨
        step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      dsimp [transition4] at hmem11
      rw [hdecph 11 (by norm_num)] at hmem11
      rw [decodeResult_encodeResult_ok r hmk] at hmem11
      by_cases him11 : F4.im s11 <;> simp [him11, hqne] at hmem11
      · simpa [qn, hd] using hmem11
      · left
        simpa [qn, hd] using hmem11
    have hnotrap11 : step11.result ≠ CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      intro h
      have htr := htrap 11 (by omega)
      rw [hg11] at htr
      rw [h] at htr
      have h101 : (decodeState (encodeState 101 0 0)).1 = 101 := by
        rw [decodeState_encodeState 101 0 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
    have hres11 : step11.result = CBTMTransResult.mk (encodeState qn 0 0) s11 Dir.L := by
      rcases hres11' with hg | ht
      · exact hg
      · exfalso
        exact hnotrap11 ht
    have hst_final : cfgc'.state = encodeState r.nextState 0 0 := by
      rw [hc11]
      dsimp [stepConfig]
      rw [hres11]
      dsimp [qn]
      rw [hmin_r]
    have hhead_final : cfgc'.headPos = 4 * p + 4 * (r.moveDir).toInt := by
      rw [hc11]
      dsimp [stepConfig]
      rw [hres11]
      dsimp
      rw [hp11]
      rw [hd]
      simp [Dir.toInt]
      omega
    refine ⟨sym, r, ⟨h, hlen, ⟨hq, ⟨hp, ⟨hcorr, ⟨rfl, ⟨hqmem, ⟨hbranch, ⟨hvalid_sym, hstep4, ⟨hmk, ⟨hr, ⟨hst_final, hhead_final⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · -- d = R
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = w1 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 1) (by rw [hp8]; omega)]
      rw [hc8'1]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) w1 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p + 1) = w1 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) w1 Dir.R := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      simp [hw1, hqne] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      simpa [hd] using hmem9
    have hp10 : cfg10.headPos = 4 * p + 2 := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      omega
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = w2 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 2) (by rw [hp8]; omega)]
      rw [hc8'2]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) w2 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p + 2) = w2 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) w2 Dir.R := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      simp [hw2, hqne] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      simpa [hd] using hmem10
    have hp11 : cfg11.headPos = 4 * p + 3 := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
      omega
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = w3 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 3) (by rw [hp10]; omega)]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 3) (by rw [hp8]; omega)]
      rw [hc8'3]
    have hmem11 : step11.result ∈ transition4 (encodeState qn 11 regr) w3 := by
      have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
      rw [show cfg11.state = encodeState qn 11 regr from by simpa [hf11] using hst11] at ht11'
      rw [hp11] at ht11'
      rw [show cfg11.tapeAt (4 * p + 3) = w3 from by simpa [hr11, hp11] using hrd11] at ht11'
      simpa [subsetSumCBTM] using ht11'
    have hnotrap11 : step11.result ≠ CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      intro h
      have htr := htrap 11 (by omega)
      rw [hg11] at htr
      rw [h] at htr
      have h101 : (decodeState (encodeState 101 0 0)).1 = 101 := by
        rw [decodeState_encodeState 101 0 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
    have hres11' : step11.result = CBTMTransResult.mk (encodeState qn 0 0) w3 Dir.R ∨
        step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      dsimp [transition4] at hmem11
      rw [hdecph 11 (by norm_num)] at hmem11
      rw [decodeResult_encodeResult_ok r hmk] at hmem11
      by_cases him3 : F4.im w3 <;> simp [him3, hqne] at hmem11
      · simpa [qn, hd] using hmem11
      · left
        simpa [qn, hd] using hmem11
    have hres11 : step11.result = CBTMTransResult.mk (encodeState qn 0 0) w3 Dir.R := by
      rcases hres11' with hg | ht
      · exact hg
      · exfalso
        exact hnotrap11 ht
    have hst_final : cfgc'.state = encodeState r.nextState 0 0 := by
      rw [hc11]
      dsimp [stepConfig]
      rw [hres11]
      dsimp [qn]
      rw [hmin_r]
    have hhead_final : cfgc'.headPos = 4 * p + 4 * (r.moveDir).toInt := by
      rw [hc11]
      dsimp [stepConfig]
      rw [hres11]
      dsimp
      rw [hp11]
      rw [hd]
      simp [Dir.toInt]
      omega
    refine ⟨sym, r, ⟨h, hlen, ⟨hq, ⟨hp, ⟨hcorr, ⟨rfl, ⟨hqmem, ⟨hbranch, ⟨hvalid_sym, hstep4, ⟨hmk, ⟨hr, ⟨hst_final, hhead_final⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · -- d = S
    have hst9 : step9.fromState = encodeState qn 9 regr := by
      have hst9' : step9.fromState = cfg9.state := by simpa using hf9
      rw [hst9']
      rw [hc8]
      dsimp [stepConfig]
      rw [hres8]
    have hrd9 : step9.readSym = w0 := by
      have hrd9' : step9.readSym = cfg9.tapeAt cfg9.headPos := by simpa using hr9
      rw [hrd9', hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
      rw [hc8]
      rw [stepConfig_tapeAt_eq_of_eq cfg8 step8.result (4 * p) (by rw [hp8])]
      rw [hres8]
    have hmem9 : step9.result ∈ transition4 (encodeState qn 9 regr) w0 := by
      have ht9' : step9.result ∈ subsetSumCBTM.transition (cfg9.state, cfg9.tapeAt cfg9.headPos, cfg9.headPos) := ht9
      rw [show cfg9.state = encodeState qn 9 regr from by simpa [hf9] using hst9] at ht9'
      rw [hp9] at ht9'
      dsimp [d] at ht9'
      simp [hd, Dir.toInt] at ht9'
      rw [show cfg9.tapeAt (4 * p) = w0 from by simpa [hr9, hp9, d, hd, Dir.toInt] using hrd9] at ht9'
      simpa [subsetSumCBTM] using ht9'
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) w0 Dir.S := by
      dsimp [transition4] at hmem9
      rw [hdecph 9 (by norm_num)] at hmem9
      simp [hw0, hqne] at hmem9
      rw [decodeResult_encodeResult_ok r hmk] at hmem9
      rw [hqnn] at hmem9
      simpa [hd] using hmem9
    have hp10 : cfg10.headPos = 4 * p := by
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
      dsimp
      rw [hp9]
      dsimp [d]
      simp [hd, Dir.toInt]
    have hst10 : step10.fromState = encodeState qn 10 regr := by
      have hst10' : step10.fromState = cfg10.state := by simpa using hf10
      rw [hst10']
      rw [hc9]
      dsimp [stepConfig]
      rw [hres9]
    have hrd10 : step10.readSym = w0 := by
      have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
      rw [hrd10', hp10]
      rw [hc9]
      rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt])]
      rw [hres9]
    have hmem10 : step10.result ∈ transition4 (encodeState qn 10 regr) w0 := by
      have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
      rw [show cfg10.state = encodeState qn 10 regr from by simpa [hf10] using hst10] at ht10'
      rw [hp10] at ht10'
      rw [show cfg10.tapeAt (4 * p) = w0 from by simpa [hr10, hp10] using hrd10] at ht10'
      simpa [subsetSumCBTM] using ht10'
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) w0 Dir.S := by
      dsimp [transition4] at hmem10
      rw [hdecph 10 (by norm_num)] at hmem10
      simp [hw0, hqne] at hmem10
      rw [decodeResult_encodeResult_ok r hmk] at hmem10
      rw [hqnn] at hmem10
      simpa [hd] using hmem10
    have hp11 : cfg11.headPos = 4 * p := by
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
      dsimp
      rw [hp10]
      simp [Dir.toInt]
    have hst11 : step11.fromState = encodeState qn 11 regr := by
      have hst11' : step11.fromState = cfg11.state := by simpa using hf11
      rw [hst11']
      rw [hc10]
      dsimp [stepConfig]
      rw [hres10]
    have hrd11 : step11.readSym = w0 := by
      have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
      rw [hrd11', hp11]
      rw [hc10]
      rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p) (by rw [hp10])]
      rw [hres10]
    have hmem11 : step11.result ∈ transition4 (encodeState qn 11 regr) w0 := by
      have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
      rw [show cfg11.state = encodeState qn 11 regr from by simpa [hf11] using hst11] at ht11'
      rw [hp11] at ht11'
      rw [show cfg11.tapeAt (4 * p) = w0 from by simpa [hr11, hp11] using hrd11] at ht11'
      simpa [subsetSumCBTM] using ht11'
    have hres11 : step11.result = CBTMTransResult.mk (encodeState qn 0 0) w0 Dir.S := by
      dsimp [transition4] at hmem11
      rw [hdecph 11 (by norm_num)] at hmem11
      simp [hw0, hqne] at hmem11
      rw [decodeResult_encodeResult_ok r hmk] at hmem11
      simpa [qn, hd] using hmem11
    have hst_final : cfgc'.state = encodeState r.nextState 0 0 := by
      rw [hc11]
      dsimp [stepConfig]
      rw [hres11]
      dsimp [qn]
      rw [hmin_r]
    have hhead_final : cfgc'.headPos = 4 * p + 4 * (r.moveDir).toInt := by
      rw [hc11]
      dsimp [stepConfig]
      rw [hres11]
      dsimp
      rw [hp11]
      rw [hd]
      simp [Dir.toInt]
      first | done | norm_num
    refine ⟨sym, r, ⟨h, hlen, ⟨hq, ⟨hp, ⟨hcorr, ⟨rfl, ⟨hqmem, ⟨hbranch, ⟨hvalid_sym, hstep4, ⟨hmk, ⟨hr, ⟨hst_final, hhead_final⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- 逐块 GoodBlock 归纳组装：无陷阱的接受路径是 GoodBlockPath。
证明计划：
1. accept_path_length_mod12 → π.length % 12 = 0（终点相位 0 由 hacc 给出）。
2. 对 π.length 做强归纳（Nat.strong_induction_on π.length），归纳谓词携带
   初始块对应 hcorr0 与起点状态界 hq0。
3. n = 0：π = []，直接 GoodBlockPath.nil。
4. n ≥ 1：split_last 12 次拆末块 πb（12 步）+ 前缀 πn；前缀长度 12(n-1)，
   归纳假设给 GoodBlockPath；前缀末对应由 project_path_gen 提取；末块用
   twelve_steps_good_block（起点相位 0 = path_phase_at_phase、htrap 继承）。
5. GoodBlockPath_append 组装。

注意：F4 层主定理的磁带 w 为任意 List F4，块对应的起点需显式给定——未访问
区域（如右边界之外的垃圾格）无法解码为 Sym 编码，故原计划注释中的声明不可证，
本声明相对原计划增加了 hcorr0 / hq0 两个前提。 -/
theorem accept_path_is_good_block_path {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w} {cfgs0 : SymConfig}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (hacc : cfg.state ∈ acceptStates4)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (hcorr0 : blockCorrespond (initialConfig subsetSumCBTM w) cfgs0)
    (hq0 : cfgs0.state ≤ 101) :
    GoodBlockPath w (initialConfig subsetSumCBTM w) π cfg := by
  have hph_end : (decodeState cfg.state).2.1 = 0 := by
    rcases Finset.mem_image.mp hacc with ⟨reg, hreg, h⟩
    rw [← h]
    dsimp [decodeState, encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept]
    simp [Finset.mem_range] at hreg
    dsimp [regBound] at hreg
    omega
  let P (n : ℕ) : Prop := ∀ (π : ComputationPath) (cfg : CBTMConfig subsetSumCBTM w) (cfgs0 : SymConfig),
    π.length = n →
    TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg →
    (decodeState cfg.state).2.1 = 0 →
    (∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) →
    blockCorrespond (initialConfig subsetSumCBTM w) cfgs0 → cfgs0.state ≤ 101 →
    GoodBlockPath w (initialConfig subsetSumCBTM w) π cfg
  have hmain : P π.length := by
    refine Nat.strong_induction_on π.length ?_
    intro n ih
    intro π cfg cfgs0 hlen_n h hph0 htrap' hcorr0' hq0'
    by_cases hn0 : n = 0
    · have hπ0 : π = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst π
      have hcfg : cfg = initialConfig subsetSumCBTM w := tapeSteps_empty h rfl
      subst cfg
      exact GoodBlockPath.nil _
    · have hlen_mod : π.length % 12 = 0 := by
        have hph := (path_phase_at h).1.1
        rw [hph0] at hph
        exact hph.symm
      have hnm : n % 12 = 0 := by simpa [← hlen_n] using hlen_mod
      have hn12 : 12 ≤ n := by omega
      rcases tapeSteps_split_last h (by
          intro h0
          have : π.length = 0 := by simpa using congrArg List.length h0
          omega) with
        ⟨step11, π10, cfg11, hπe11, h10, hf11, hr11, ht11, hc11⟩
      rcases tapeSteps_split_last h10 (by
          intro h0
          have : (π10 ++ [step11]).length = n := by simpa [hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step10, π9, cfg10, hπe10, h9, hf10, hr10, ht10, hc10⟩
      rcases tapeSteps_split_last h9 (by
          intro h0
          have : (π9 ++ [step10, step11]).length = n := by simpa [hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step9, π8, cfg9, hπe9, h8, hf9, hr9, ht9, hc9⟩
      rcases tapeSteps_split_last h8 (by
          intro h0
          have : (π8 ++ [step9, step10, step11]).length = n := by simpa [hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step8, π7, cfg8, hπe8, h7, hf8, hr8, ht8, hc8⟩
      rcases tapeSteps_split_last h7 (by
          intro h0
          have : (π7 ++ [step8, step9, step10, step11]).length = n := by simpa [hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step7, π6, cfg7, hπe7, h6, hf7, hr7, ht7, hc7⟩
      rcases tapeSteps_split_last h6 (by
          intro h0
          have : (π6 ++ [step7, step8, step9, step10, step11]).length = n := by simpa [hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step6, π5, cfg6, hπe6, h5, hf6, hr6, ht6, hc6⟩
      rcases tapeSteps_split_last h5 (by
          intro h0
          have : (π5 ++ [step6, step7, step8, step9, step10, step11]).length = n := by simpa [hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step5, π4, cfg5, hπe5, h4, hf5, hr5, ht5, hc5⟩
      rcases tapeSteps_split_last h4 (by
          intro h0
          have : (π4 ++ [step5, step6, step7, step8, step9, step10, step11]).length = n := by simpa [hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step4, π3, cfg4, hπe4, h3, hf4, hr4, ht4, hc4⟩
      rcases tapeSteps_split_last h3 (by
          intro h0
          have : (π3 ++ [step4, step5, step6, step7, step8, step9, step10, step11]).length = n := by simpa [hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step3, π2, cfg3, hπe3, h2, hf3, hr3, ht3, hc3⟩
      rcases tapeSteps_split_last h2 (by
          intro h0
          have : (π2 ++ [step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = n := by simpa [hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step2, π1, cfg2, hπe2, h1, hf2, hr2, ht2, hc2⟩
      rcases tapeSteps_split_last h1 (by
          intro h0
          have : (π1 ++ [step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = n := by simpa [hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step1, π0, cfg1, hπe1, h0, hf1, hr1, ht1, hc1⟩
      rcases tapeSteps_split_last h0 (by
          intro h0
          have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = n := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen_n
          simp [h0] at this
          omega) with
        ⟨step0, πn, cfgc0, hπen, hn, hf0, hr0, ht0, hc0⟩
      have hπall : π = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
        rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
        simp
      have hlen_nm : πn.length = n - 12 := by
        have := congrArg List.length hπall
        simp at this
        omega
      have hlt : πn.length < n := by omega
      have hmod0 : (n - 12) % 12 = 0 := by
        rcases Nat.dvd_of_mod_eq_zero hnm with ⟨k, hk⟩
        have hkge : 1 ≤ k := by omega
        cases k with
        | zero => omega
        | succ k' =>
            rw [hk]
            rw [show 12 * (k' + 1) - 12 = 12 * k' by omega]
            exact Nat.mul_mod_right 12 k'
      have hg0 : π.get ⟨πn.length, by rw [hπall]; simp⟩ = step0 := by
        simpa [hπall] using (List.getElem_append_right (α := TransitionStep) (as := πn)
          (bs := [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11])
          (i := πn.length) (Nat.le_refl _) (by simp))
      have hph0b : (decodeState cfgc0.state).2.1 = 0 := by
        have hph' := path_phase_at_phase h πn.length (by rw [hπall]; simp)
        rw [hg0] at hph'
        rw [hf0] at hph'
        rw [show πn.length % 12 = 0 from by simpa [hlen_nm] using hmod0] at hph'
        exact hph'
      have htrapn : ∀ k (hk : k < πn.length), (decodeState (πn.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
        intro k hk h
        have hk' : k < π.length := by
          rw [hπall]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have hg : π.get ⟨k, hk'⟩ = πn.get ⟨k, hk⟩ := by
          simpa [hπall] using (List.getElem_append_left (α := TransitionStep) (as := πn)
            (bs := [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]) (i := k) hk)
        have hres : (π.get ⟨k, hk'⟩).result = (πn.get ⟨k, hk⟩).result := by
          rw [hg]
        exact htrap' k hk' (by rw [hres]; exact h)
      let πb : ComputationPath := [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]
      have htrapb : ∀ k (hk : k < 12), (decodeState ((πb.get ⟨k, hk⟩)).result.nextState).1 ≠ 101 := by
        intro k hk h
        have hk' : πn.length + k < π.length := by
          rw [hπall]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have hg : π.get ⟨πn.length + k, hk'⟩ = πb.get ⟨k, hk⟩ := by
          simpa [hπall, πb] using (List.getElem_append_right (α := TransitionStep) (as := πn)
            (bs := [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11])
            (i := πn.length + k) (by omega) (by simpa using hk))
        have hres : (π.get ⟨πn.length + k, hk'⟩).result = (πb.get ⟨k, hk⟩).result := by
          rw [hg]
        exact htrap' (πn.length + k) hk' (by rw [hres]; exact h)
      have hb1 : TapeSteps subsetSumCBTM w cfgc0 [step0] (stepConfig cfgc0 step0.result) :=
        TapeSteps.cons [] step0 cfgc0 (TapeSteps.nil) hf0 hr0 ht0
      have hb2 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1]
          (stepConfig (stepConfig cfgc0 step0.result) step1.result) :=
        TapeSteps.cons [step0] step1 (stepConfig cfgc0 step0.result) hb1
          (by simpa [hc0] using hf1) (by simpa [hc0] using hr1) (by simpa [hc0] using ht1)
      have hb3 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2]
          (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) :=
        TapeSteps.cons [step0, step1] step2 (stepConfig (stepConfig cfgc0 step0.result) step1.result) hb2
          (by simpa [hc0, hc1] using hf2) (by simpa [hc0, hc1] using hr2) (by simpa [hc0, hc1] using ht2)
      have hb4 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3]
          (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) :=
        TapeSteps.cons [step0, step1, step2] step3 (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) hb3
          (by simpa [hc0, hc1, hc2] using hf3) (by simpa [hc0, hc1, hc2] using hr3) (by simpa [hc0, hc1, hc2] using ht3)
      have hb5 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) :=
        TapeSteps.cons [step0, step1, step2, step3] step4 (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) hb4
          (by simpa [hc0, hc1, hc2, hc3] using hf4) (by simpa [hc0, hc1, hc2, hc3] using hr4) (by simpa [hc0, hc1, hc2, hc3] using ht4)
      have hb6 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4] step5 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) hb5
          (by simpa [hc0, hc1, hc2, hc3, hc4] using hf5) (by simpa [hc0, hc1, hc2, hc3, hc4] using hr5) (by simpa [hc0, hc1, hc2, hc3, hc4] using ht5)
      have hb7 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5, step6]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5] step6 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) hb6
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5] using hf6) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5] using hr6) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5] using ht6)
      have hb8 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6] step7 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) hb7
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6] using hf7) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6] using hr7) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6] using ht7)
      have hb9 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7] step8 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) hb8
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] using hf8) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] using hr8) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] using ht8)
      have hb10 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7, step8] step9 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) hb9
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] using hf9) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] using hr9) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] using ht9)
      have hb11 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9] step10 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) hb10
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9] using hf10) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9] using hr10) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9] using ht10)
      have hb12 : TapeSteps subsetSumCBTM w cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) step11.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10] step11 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) hb11
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10] using hf11) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10] using hr11) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10] using ht11)
      have hb : TapeSteps subsetSumCBTM w cfgc0 πb cfg := by
        rw [show cfg = (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) step11.result) from by
          rw [hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0]]
        simpa [πb] using hb12
      have hbp_prefix : GoodBlockPath w (initialConfig subsetSumCBTM w) πn cfgc0 :=
        ih πn.length hlt πn cfgc0 cfgs0 rfl hn hph0b htrapn hcorr0' hq0'
      rcases project_path_gen w (initialConfig subsetSumCBTM w) cfgs0 πn cfgc0 hcorr0' hbp_prefix htrapn with
        ⟨πs, cfgs', hsteps, hcorr_end, hlenp⟩
      have hqle0 : cfgs'.state ≤ 101 := by
        -- SymSteps preserves state ≤ 101
        have aux : ∀ {cfgs cfgs' : SymConfig} {π : List SymStep},
            SymSteps VerifierSym.transition cfgs π cfgs' → cfgs.state ≤ 101 → cfgs'.state ≤ 101 := by
          intro cfgs cfgs' π hs hle
          induction hs with
          | nil => exact hle
          | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
              have hle1 := transition_nextState_le101 cfg₁.state (cfg₁.tape cfg₁.headPos) ih step.result htrans
              dsimp [symStepConfig] at hle1 ⊢
              exact hle1
        exact aux hsteps hq0'
      rcases twelve_steps_good_block (h := hb) (hlen := by simp [πb]) hph0b htrapb hcorr_end
          hcorr_end.1 hqle0 hcorr_end.2.1 with ⟨sym, r, hblock⟩
      have hsingle : GoodBlockPath w cfgc0 πb cfg :=
        GoodBlockPath.cons cfgc0 cfg cfg πb [] cfgs' cfgs'.headPos cfgs'.state sym r hblock (GoodBlockPath.nil cfg)
      rw [hπall]
      exact GoodBlockPath_append w (initialConfig subsetSumCBTM w) cfgc0 cfg πn πb hbp_prefix hsingle
  exact hmain π cfg cfgs0 rfl h hph_end htrap hcorr0 hq0

end SymToF4

end Mp
