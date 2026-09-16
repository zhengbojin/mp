/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumCompile

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
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

namespace Mp
open CBTM
namespace SymToF4

-- q11b:subsetSumCBTM 接受路径逐块解码(级 A:no_trap_path_decodes_prefix)
/-- 初始磁带相等的两个输入上,TapeSteps 可重放(逐字段一致)。 -/
lemma tapeSteps_lift_input {w w' : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (htape : (initialConfig subsetSumCBTM w).tape = (initialConfig subsetSumCBTM w').tape) :
    ∃ cfg' : CBTMConfig subsetSumCBTM w',
      TapeSteps subsetSumCBTM w' (initialConfig subsetSumCBTM w') π cfg' ∧
      cfg'.state = cfg.state ∧ cfg'.tape = cfg.tape ∧ cfg'.headPos = cfg.headPos := by
  induction h with
  | nil =>
      refine ⟨initialConfig subsetSumCBTM w', TapeSteps.nil, rfl, ?_, rfl⟩
      · -- initialConfig w'.tape = initialConfig w.tape(此时 cfg = initialConfig w):
        rw [← htape]
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨cfg₁', hsteps', hs, ht, hp⟩
      refine ⟨stepConfig cfg₁' step.result,
        TapeSteps.cons π₀ step cfg₁' hsteps' ?_ ?_ ?_, ?_, ?_, ?_⟩
      · -- step.fromState = cfg₁'.state:
        rw [hfrom, ← hs]
      · -- step.readSym = cfg₁'.tapeAt cfg₁'.headPos:
        rw [hread]
        unfold CBTMConfig.tapeAt
        rw [ht, hp]
      · -- step.result ∈ subsetSumCBTM.transition (cfg₁'.state, cfg₁'.tapeAt cfg₁'.headPos, cfg₁'.headPos):
        unfold CBTMConfig.tapeAt
        rw [hs, ht, hp]
        exact htrans
      · -- (stepConfig cfg₁' step.result).state = (stepConfig cfg₁ step.result).state:
        rfl
      · -- tape:
        unfold stepConfig
        rw [ht, hp]
      · -- headPos:
        unfold stepConfig
        rw [hp]

-- ============================================================
-- q11b-1 引理 2:初始 tape 于 w 与 w ++ replicate k zero 相同
-- ============================================================

/-- 前缀截取对 replicate 尾部长度不敏感(界 ≤ 两侧尾部)。 -/
lemma take_replicate_eq {α : Type} {x : α} {w : List α} {m k n : ℕ}
    (h₁ : n ≤ w.length + m) (h₂ : n ≤ w.length + k) :
    List.take n (w ++ List.replicate m x) = List.take n (w ++ List.replicate k x) := by
  rw [List.take_append, List.take_replicate]
  rw [List.take_append, List.take_replicate]
  rw [Nat.min_eq_left (show n - w.length ≤ m by omega)]
  rw [Nat.min_eq_left (show n - w.length ≤ k by omega)]

/-- w 的前缀截取 = 扩展列表截取再截 w.length。 -/

lemma take_w_take_append {α : Type} {w r : List α} {n : ℕ} :
    ((w ++ r).take n).take w.length = w.take n := by
  rw [List.take_take]
  by_cases hn : n ≤ w.length
  · rw [Nat.min_eq_right hn]
    rw [List.take_append_of_le_length (l₁ := w) (l₂ := r) (i := n) hn]
  · rw [Nat.min_eq_left (by omega)]
    rw [List.take_append_of_le_length (l₁ := w) (l₂ := r) (i := w.length) (Nat.le_refl _)]
    rw [List.take_of_length_le (Nat.le_refl w.length)]
    rw [List.take_of_length_le (by omega : w.length ≤ n)]

lemma initialTape_append_replicate_zero (w : List F4) (k : ℕ) :
    (initialConfig subsetSumCBTM w).tape =
      (initialConfig subsetSumCBTM (w ++ List.replicate k F4.zero)).tape := by
  unfold initialConfig initialTapeOf
  funext i
  change (if h : 0 ≤ i ∧ i.toNat < w.length then w.get ⟨i.toNat, h.2⟩ else subsetSumCBTM.blankSym) =
    (if h : 0 ≤ i ∧ i.toNat < (w ++ List.replicate k F4.zero).length then
      (w ++ List.replicate k F4.zero).get ⟨i.toNat, h.2⟩ else subsetSumCBTM.blankSym)
  by_cases hpos : 0 ≤ i
  · by_cases hlt : i.toNat < w.length
    · have hlt2 : i.toNat < (w ++ List.replicate k F4.zero).length := by
        simp [List.length_append]
        omega
      rw [dif_pos (And.intro hpos hlt), dif_pos (And.intro hpos hlt2)]
      exact (@List.getElem_append_left F4 i.toNat w (List.replicate k F4.zero) hlt hlt2).symm
    · by_cases hlt2 : i.toNat < (w ++ List.replicate k F4.zero).length
      · rw [dif_neg (by intro h; exact hlt h.2), dif_pos (And.intro hpos hlt2)]
        have hg : (w ++ List.replicate k F4.zero)[i.toNat]'(And.intro hpos hlt2).2 = F4.zero := by
          exact (@List.getElem_append_right F4 w (List.replicate k F4.zero) i.toNat
            (by omega : w.length ≤ i.toNat) (And.intro hpos hlt2).2).trans
            (List.getElem_replicate (n := k) (a := F4.zero) (i := i.toNat - w.length)
              (by
                have hlt2' : i.toNat < w.length + k := by
                  simpa [List.length_append, List.length_replicate] using hlt2
                simp [List.length_replicate]
                omega : i.toNat - w.length < (List.replicate k F4.zero).length))
        simpa [subsetSumCBTM] using hg.symm
      · rw [dif_neg (by intro h; exact hlt h.2), dif_neg (by intro h; exact hlt2 h.2)]
  · simp [hpos]

-- ============================================================
-- q11b-1b:弱对应(Near)与好块变体
-- ============================================================

/-- 一步写只改带头处:非带头处磁带值不变(tape 版)。 -/
lemma stepConfig_tape_eq_of_ne {M : CBTM} {input : List F4} {cfg : CBTMConfig M input}
    (r : CBTMTransResult) (z : ℤ) (hne : z ≠ cfg.headPos) :
    (stepConfig cfg r).tape z = cfg.tape z := by
  simp [stepConfig, hne]

/-- 弱块对应:state/headPos + 块 p 与块 p-1 的 4 格对应(不要求全带)。 -/
def blockCorrespondNear {w : List F4} (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ) : Prop :=
  cfgc.state = encodeState cfgs.state 0 0 ∧
  cfgc.headPos = 4 * p ∧
  (∀ j : ℕ, j < 4 → cfgc.tapeAt (4 * (p - 1) + j) = (symTo4F4 (cfgs.tape (p - 1))).getD j F4.zero)

/-- 已解码位置的全称块对应(位置 i ≤ M)。 -/
def blockCorrespondUpto {w : List F4} (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (M : ℕ) : Prop :=
  cfgc.state = encodeState cfgs.state 0 0 ∧
  cfgc.headPos = 4 * cfgs.headPos ∧
  ∀ i : ℤ, i < M → ∀ j : ℕ, j < 4 →
    cfgc.tapeAt (4 * i + j) = (symTo4F4 (cfgs.tape i)).getD j F4.zero

/-- 好块变体:块对应弱化为 Near。 -/
def GoodBlockNear (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (π : ComputationPath)
    (cfgc' : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (q : ℕ) (sym : Sym) (r : SymTransResult) : Prop :=
  ∃ hpath : TapeSteps subsetSumCBTM w cfgc π cfgc',
  ∃ hlen : π.length = 12,
    cfgc.state = encodeState q 0 0 ∧
    cfgc.headPos = 4 * p ∧
    blockCorrespondNear cfgc cfgs p ∧
    (q ≤ 101) ∧
    (Sym.isBranch sym → q = 2) ∧
    (sym.2 = true → sym.1 = SymKind.data0 ∨ sym.1 = SymKind.data1 ∨ sym.1 = SymKind.alpha ∨
      sym.1 = SymKind.consumed ∨ sym.1 = SymKind.boundary ∨ sym.1 = SymKind.sel ∨
      sym.1 = SymKind.nosel ∨ sym.1 = SymKind.beta) ∧
    (π.get ⟨3, by omega⟩).result = CBTMTransResult.mk
      (encodeState r.nextState 4 (encodeResult r)) ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L ∧
    (r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
      r.writeSym.1 = SymKind.alpha ∨ r.writeSym.1 = SymKind.consumed ∨ r.writeSym.1 = SymKind.boundary ∨
      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨ r.writeSym.1 = SymKind.beta) ∧
    r ∈ VerifierSym.transition (q, sym) ∧
    cfgc'.state = encodeState r.nextState 0 0 ∧
    cfgc'.headPos = 4 * p + 4 * (r.moveDir).toInt ∧
    (∀ z : ℤ, z < 4 * p - 4 ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z) ∧
    (r.moveDir = Dir.S → ∀ z : ℤ, z < 4 * p ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z) ∧
    (∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * (p - 1) + j) = cfgc.tapeAt (4 * (p - 1) + j)) ∧
    (∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * p + j) = (symTo4F4 r.writeSym).getD j F4.zero) ∧
    symOf4F4 (cfgc.tapeAt (4 * p)) (cfgc.tapeAt (4 * p + 1))
      (cfgc.tapeAt (4 * p + 2)) (cfgc.tapeAt (4 * p + 3)) = some sym

/-- 单步:z 处若写回同值则不变,否则 z ≠ 写位置也不变。 -/
lemma stepConfig_tapeAt_keeps_or_ne {M : CBTM} {input : List F4} {cfga : CBTMConfig M input}
    {step : TransitionStep} (z : ℤ)
    (hcase : z = cfga.headPos → step.result.writeSym = step.readSym ∧
      step.readSym = cfga.tapeAt cfga.headPos) :
    (stepConfig cfga step.result).tapeAt z = cfga.tapeAt z := by
  rw [stepConfig_tapeAt_apply]
  by_cases hz : z = cfga.headPos
  · rcases hcase hz with ⟨hw, hr⟩
    simp [hz, hw, hr]
  · simp [hz]

lemma twelve_steps_good_block_upto {w : List F4} {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} (h : TapeSteps subsetSumCBTM w cfgc π cfgc')
    (hlen : π.length = 12)
    (hph0 : (decodeState cfgc.state).2.1 = 0)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    {cfgs : SymConfig} {p : ℤ} (hcorr : blockCorrespondNear cfgc cfgs p)
    {sym : Sym}
    (hpCells : ∀ j : ℕ, j < 4 → cfgc.tapeAt (4 * p + j) = (symTo4F4 sym).getD j F4.zero)
    {q : ℕ} (hq : cfgc.state = encodeState q 0 0) (hqle : q ≤ 101)
    (hp : cfgc.headPos = 4 * p) :
    ∃ sym : Sym, ∃ r : SymTransResult,
      GoodBlockNear w cfgc π cfgc' cfgs p q sym r := by
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
    have hc := hpCells 0 (by norm_num)
    simpa [c0, cells] using hc
  have hc1v : cfgc.tapeAt (4 * p + 1) = c1 := by
    have hc := hpCells 1 (by norm_num)
    simpa [c1, cells] using hc
  have hc2v : cfgc.tapeAt (4 * p + 2) = c2 := by
    have hc := hpCells 2 (by norm_num)
    simpa [c2, cells] using hc
  have hc3v : cfgc.tapeAt (4 * p + 3) = c3 := by
    have hc := hpCells 3 (by norm_num)
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
  have hso_read : symOf4F4 (cfgc.tapeAt (4 * p)) (cfgc.tapeAt (4 * p + 1))
      (cfgc.tapeAt (4 * p + 2)) (cfgc.tapeAt (4 * p + 3)) = some sym := by
    have hp0 : cfgc.tapeAt (4 * p) = (symTo4F4 sym).getD 0 F4.zero := by
      simpa using hpCells 0 (by omega)
    have hp1 : cfgc.tapeAt (4 * p + 1) = (symTo4F4 sym).getD 1 F4.zero := by
      simpa using hpCells 1 (by omega)
    have hp2 : cfgc.tapeAt (4 * p + 2) = (symTo4F4 sym).getD 2 F4.zero := by
      simpa using hpCells 2 (by omega)
    have hp3 : cfgc.tapeAt (4 * p + 3) = (symTo4F4 sym).getD 3 F4.zero := by
      simpa using hpCells 3 (by omega)
    rw [hp0, hp1, hp2, hp3]
    simpa [c0, c1, c2, c3, cells] using hso
  have hvalid_sym : sym.2 = true → sym.1 = SymKind.data0 ∨ sym.1 = SymKind.data1 ∨ sym.1 = SymKind.alpha ∨
      sym.1 = SymKind.consumed ∨ sym.1 = SymKind.boundary ∨ sym.1 = SymKind.sel ∨
      sym.1 = SymKind.nosel ∨ sym.1 = SymKind.beta := by
    intro _
    cases sym.1 <;> decide
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
              r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨ r.writeSym.1 = SymKind.beta := by native_decide
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
      rw [hcorr.2.2 3 (by norm_num)]
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
      rw [hcorr.2.2 2 (by norm_num)]
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
      rw [hcorr.2.2 1 (by norm_num)]
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
    have hstep_keeps {cfga : CBTMConfig subsetSumCBTM w} {step : TransitionStep}
        (hread : step.readSym = cfga.tapeAt cfga.headPos)
        (hweq : step.result.writeSym = step.readSym) (z : ℤ) :
        (stepConfig cfga step.result).tapeAt z = cfga.tapeAt z := by
      dsimp [CBTMConfig.tapeAt, stepConfig]
      change (if z = cfga.headPos then step.result.writeSym else cfga.tape z) = cfga.tape z
      by_cases hz : z = cfga.headPos
      · simp [hz, hweq, hread, CBTMConfig.tapeAt]
      · simp [hz]
    have hweq7 : step7.result.writeSym = step7.readSym := by
      rw [hres7, hrd7]
    have hweq8 : step8.result.writeSym = step8.readSym := by
      rw [hres8, hrd8]
    have hweq9 : step9.result.writeSym = step9.readSym := by
      rw [hres9, hrd9]
    have hweq10 : step10.result.writeSym = step10.readSym := by
      rw [hres10, hrd10]
    have hweq11 : step11.result.writeSym = step11.readSym := by
      rw [hres11, hrd11]
    have hwrite : ∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * p + j) = (symTo4F4 r.writeSym).getD j F4.zero := by
      intro j hj
      interval_cases j
      · calc
          cfgc'.tapeAt (4 * p + 0) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 0) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 0) := hstep_keeps hr11 hweq11 (4 * p + 0)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 0) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 0) := hstep_keeps hr10 hweq10 (4 * p + 0)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 0) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 0) := hstep_keeps hr9 hweq9 (4 * p + 0)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 0) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 0) := hstep_keeps hr8 hweq8 (4 * p + 0)
          _ = w0 := by simpa using hc8'0
      · calc
          cfgc'.tapeAt (4 * p + 1) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 1) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 1) := hstep_keeps hr11 hweq11 (4 * p + 1)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 1) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 1) := hstep_keeps hr10 hweq10 (4 * p + 1)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 1) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 1) := hstep_keeps hr9 hweq9 (4 * p + 1)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 1) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 1) := hstep_keeps hr8 hweq8 (4 * p + 1)
          _ = w1 := hc8'1
      · calc
          cfgc'.tapeAt (4 * p + 2) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 2) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 2) := hstep_keeps hr11 hweq11 (4 * p + 2)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 2) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 2) := hstep_keeps hr10 hweq10 (4 * p + 2)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 2) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 2) := hstep_keeps hr9 hweq9 (4 * p + 2)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 2) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 2) := hstep_keeps hr8 hweq8 (4 * p + 2)
          _ = w2 := hc8'2
      · calc
          cfgc'.tapeAt (4 * p + 3) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 3) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 3) := hstep_keeps hr11 hweq11 (4 * p + 3)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 3) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 3) := hstep_keeps hr10 hweq10 (4 * p + 3)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 3) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 3) := hstep_keeps hr9 hweq9 (4 * p + 3)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 3) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 3) := hstep_keeps hr8 hweq8 (4 * p + 3)
          _ = w3 := hc8'3
    have htail : ∀ z : ℤ, z < 4 * p - 4 ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro z hz
      have hd_toInt : -1 ≤ (r.moveDir).toInt ∧ (r.moveDir).toInt ≤ 1 := by
        cases r.moveDir <;> simp [Dir.toInt]
      rw [hc11]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg11) step11.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp11] <;> omega)]
      rw [hc10]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg10) step10.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp10] <;> omega)]
      rw [hc9]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg9) step9.result z (by
        rw [hp9]
        dsimp [d]
        rcases hz with hz1 | hz2 <;> omega)]
      rw [hc8]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg8) step8.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp8] <;> omega)]
      rw [hc7]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg7) step7.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp7] <;> omega)]
      rw [hc6]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg6) step6.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp6] <;> omega)]
      rw [hc5]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg5) step5.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp5] <;> omega)]
      rw [hc4]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg4) step4.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp4] <;> omega)]
      rw [hc3]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg3) step3.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp3] <;> omega)]
      rw [hc2]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg2) step2.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp2] <;> omega)]
      rw [hc1]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg1) step1.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp1] <;> omega)]
      rw [hc0]
      rw [stepConfig_tape_eq_of_ne (cfg := cfgc) step0.result z (by
        rcases hz with hz1 | hz2 <;> omega)]
    have htailS_L : r.moveDir = Dir.S → ∀ z : ℤ, z < 4 * p ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro hs
      rw [hs] at hd
      cases hd
    have htailP1_L : ∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * (p - 1) + j) = cfgc.tapeAt (4 * (p - 1) + j) := by
      have hdL : d = Dir.L := by
        dsimp [d]
        exact hd
      intro j hj
      interval_cases j
      · -- j = 0
        calc
          cfgc'.tapeAt (4 * (p - 1) + 0) = (stepConfig cfg11 step11.result).tapeAt (4 * (p - 1) + 0) := by rw [hc11]
          _ = cfg11.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp11] at hz; omega)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * (p - 1) + 0) := by rw [hc10]
          _ = cfg10.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp10] at hz; omega)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * (p - 1) + 0) := by rw [hc9]
          _ = cfg9.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp9] at hz; rw [hdL] at hz; simp [Dir.toInt] at hz; omega)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * (p - 1) + 0) := by rw [hc8]
          _ = cfg8.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp8] at hz; omega)
          _ = (stepConfig cfg7 step7.result).tapeAt (4 * (p - 1) + 0) := by rw [hc7]
          _ = cfg7.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp7] at hz; omega)
          _ = (stepConfig cfg6 step6.result).tapeAt (4 * (p - 1) + 0) := by rw [hc6]
          _ = cfg6.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp6] at hz; omega)
          _ = (stepConfig cfg5 step5.result).tapeAt (4 * (p - 1) + 0) := by rw [hc5]
          _ = cfg5.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp5] at hz; omega)
          _ = (stepConfig cfg4 step4.result).tapeAt (4 * (p - 1) + 0) := by rw [hc4]
          _ = cfg4.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp4] at hz; omega)
          _ = (stepConfig cfg3 step3.result).tapeAt (4 * (p - 1) + 0) := by rw [hc3]
          _ = cfg3.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp3] at hz; omega)
          _ = (stepConfig cfg2 step2.result).tapeAt (4 * (p - 1) + 0) := by rw [hc2]
          _ = cfg2.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp2] at hz; omega)
          _ = (stepConfig cfg1 step1.result).tapeAt (4 * (p - 1) + 0) := by rw [hc1]
          _ = cfg1.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp1] at hz; omega)
          _ = (stepConfig cfgc step0.result).tapeAt (4 * (p - 1) + 0) := by rw [hc0]
          _ = cfgc.tapeAt (4 * (p - 1) + 0) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 0)
              (by intro hz; rw [hp] at hz; omega)
      · -- j = 1
        calc
          cfgc'.tapeAt (4 * (p - 1) + 1) = (stepConfig cfg11 step11.result).tapeAt (4 * (p - 1) + 1) := by rw [hc11]
          _ = cfg11.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; exact ⟨hweq11, hr11⟩)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * (p - 1) + 1) := by rw [hc10]
          _ = cfg10.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp10] at hz; omega)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * (p - 1) + 1) := by rw [hc9]
          _ = cfg9.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp9] at hz; rw [hdL] at hz; simp [Dir.toInt] at hz; omega)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * (p - 1) + 1) := by rw [hc8]
          _ = cfg8.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp8] at hz; omega)
          _ = (stepConfig cfg7 step7.result).tapeAt (4 * (p - 1) + 1) := by rw [hc7]
          _ = cfg7.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp7] at hz; omega)
          _ = (stepConfig cfg6 step6.result).tapeAt (4 * (p - 1) + 1) := by rw [hc6]
          _ = cfg6.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp6] at hz; omega)
          _ = (stepConfig cfg5 step5.result).tapeAt (4 * (p - 1) + 1) := by rw [hc5]
          _ = cfg5.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp5] at hz; omega)
          _ = (stepConfig cfg4 step4.result).tapeAt (4 * (p - 1) + 1) := by rw [hc4]
          _ = cfg4.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp4] at hz; omega)
          _ = (stepConfig cfg3 step3.result).tapeAt (4 * (p - 1) + 1) := by rw [hc3]
          _ = cfg3.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp3] at hz; omega)
          _ = (stepConfig cfg2 step2.result).tapeAt (4 * (p - 1) + 1) := by rw [hc2]
          _ = cfg2.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp2] at hz; omega)
          _ = (stepConfig cfg1 step1.result).tapeAt (4 * (p - 1) + 1) := by rw [hc1]
          _ = cfg1.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp1] at hz; omega)
          _ = (stepConfig cfgc step0.result).tapeAt (4 * (p - 1) + 1) := by rw [hc0]
          _ = cfgc.tapeAt (4 * (p - 1) + 1) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 1)
              (by intro hz; rw [hp] at hz; omega)
      · -- j = 2
        calc
          cfgc'.tapeAt (4 * (p - 1) + 2) = (stepConfig cfg11 step11.result).tapeAt (4 * (p - 1) + 2) := by rw [hc11]
          _ = cfg11.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp11] at hz; omega)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * (p - 1) + 2) := by rw [hc10]
          _ = cfg10.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; exact ⟨hweq10, hr10⟩)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * (p - 1) + 2) := by rw [hc9]
          _ = cfg9.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp9] at hz; rw [hdL] at hz; simp [Dir.toInt] at hz; omega)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * (p - 1) + 2) := by rw [hc8]
          _ = cfg8.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp8] at hz; omega)
          _ = (stepConfig cfg7 step7.result).tapeAt (4 * (p - 1) + 2) := by rw [hc7]
          _ = cfg7.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp7] at hz; omega)
          _ = (stepConfig cfg6 step6.result).tapeAt (4 * (p - 1) + 2) := by rw [hc6]
          _ = cfg6.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp6] at hz; omega)
          _ = (stepConfig cfg5 step5.result).tapeAt (4 * (p - 1) + 2) := by rw [hc5]
          _ = cfg5.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp5] at hz; omega)
          _ = (stepConfig cfg4 step4.result).tapeAt (4 * (p - 1) + 2) := by rw [hc4]
          _ = cfg4.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp4] at hz; omega)
          _ = (stepConfig cfg3 step3.result).tapeAt (4 * (p - 1) + 2) := by rw [hc3]
          _ = cfg3.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp3] at hz; omega)
          _ = (stepConfig cfg2 step2.result).tapeAt (4 * (p - 1) + 2) := by rw [hc2]
          _ = cfg2.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp2] at hz; omega)
          _ = (stepConfig cfg1 step1.result).tapeAt (4 * (p - 1) + 2) := by rw [hc1]
          _ = cfg1.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp1] at hz; omega)
          _ = (stepConfig cfgc step0.result).tapeAt (4 * (p - 1) + 2) := by rw [hc0]
          _ = cfgc.tapeAt (4 * (p - 1) + 2) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 2)
              (by intro hz; rw [hp] at hz; omega)
      · -- j = 3
        calc
          cfgc'.tapeAt (4 * (p - 1) + 3) = (stepConfig cfg11 step11.result).tapeAt (4 * (p - 1) + 3) := by rw [hc11]
          _ = cfg11.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp11] at hz; omega)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * (p - 1) + 3) := by rw [hc10]
          _ = cfg10.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp10] at hz; omega)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * (p - 1) + 3) := by rw [hc9]
          _ = cfg9.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; exact ⟨hweq9, hr9⟩)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * (p - 1) + 3) := by rw [hc8]
          _ = cfg8.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp8] at hz; omega)
          _ = (stepConfig cfg7 step7.result).tapeAt (4 * (p - 1) + 3) := by rw [hc7]
          _ = cfg7.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp7] at hz; omega)
          _ = (stepConfig cfg6 step6.result).tapeAt (4 * (p - 1) + 3) := by rw [hc6]
          _ = cfg6.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp6] at hz; omega)
          _ = (stepConfig cfg5 step5.result).tapeAt (4 * (p - 1) + 3) := by rw [hc5]
          _ = cfg5.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp5] at hz; omega)
          _ = (stepConfig cfg4 step4.result).tapeAt (4 * (p - 1) + 3) := by rw [hc4]
          _ = cfg4.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp4] at hz; omega)
          _ = (stepConfig cfg3 step3.result).tapeAt (4 * (p - 1) + 3) := by rw [hc3]
          _ = cfg3.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp3] at hz; omega)
          _ = (stepConfig cfg2 step2.result).tapeAt (4 * (p - 1) + 3) := by rw [hc2]
          _ = cfg2.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp2] at hz; omega)
          _ = (stepConfig cfg1 step1.result).tapeAt (4 * (p - 1) + 3) := by rw [hc1]
          _ = cfg1.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp1] at hz; omega)
          _ = (stepConfig cfgc step0.result).tapeAt (4 * (p - 1) + 3) := by rw [hc0]
          _ = cfgc.tapeAt (4 * (p - 1) + 3) := stepConfig_tapeAt_keeps_or_ne (4 * (p - 1) + 3)
              (by intro hz; rw [hp] at hz; omega)
    refine ⟨sym, r, h, hlen, hq, hp, hcorr, hqmem, hbranch, hvalid_sym, hstep4, hmk, hr, hst_final, hhead_final, htail, htailS_L, htailP1_L, hwrite, hso_read⟩
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
    have hstep_keeps {cfga : CBTMConfig subsetSumCBTM w} {step : TransitionStep}
        (hread : step.readSym = cfga.tapeAt cfga.headPos)
        (hweq : step.result.writeSym = step.readSym) (z : ℤ) :
        (stepConfig cfga step.result).tapeAt z = cfga.tapeAt z := by
      dsimp [CBTMConfig.tapeAt, stepConfig]
      change (if z = cfga.headPos then step.result.writeSym else cfga.tape z) = cfga.tape z
      by_cases hz : z = cfga.headPos
      · simp [hz, hweq, hread, CBTMConfig.tapeAt]
      · simp [hz]
    have hweq7 : step7.result.writeSym = step7.readSym := by
      rw [hres7, hrd7]
    have hweq8 : step8.result.writeSym = step8.readSym := by
      rw [hres8, hrd8]
    have hweq9 : step9.result.writeSym = step9.readSym := by
      rw [hres9, hrd9]
    have hweq10 : step10.result.writeSym = step10.readSym := by
      rw [hres10, hrd10]
    have hweq11 : step11.result.writeSym = step11.readSym := by
      rw [hres11, hrd11]
    have hwrite : ∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * p + j) = (symTo4F4 r.writeSym).getD j F4.zero := by
      intro j hj
      interval_cases j
      · calc
          cfgc'.tapeAt (4 * p + 0) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 0) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 0) := hstep_keeps hr11 hweq11 (4 * p + 0)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 0) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 0) := hstep_keeps hr10 hweq10 (4 * p + 0)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 0) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 0) := hstep_keeps hr9 hweq9 (4 * p + 0)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 0) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 0) := hstep_keeps hr8 hweq8 (4 * p + 0)
          _ = w0 := by simpa using hc8'0
      · calc
          cfgc'.tapeAt (4 * p + 1) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 1) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 1) := hstep_keeps hr11 hweq11 (4 * p + 1)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 1) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 1) := hstep_keeps hr10 hweq10 (4 * p + 1)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 1) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 1) := hstep_keeps hr9 hweq9 (4 * p + 1)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 1) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 1) := hstep_keeps hr8 hweq8 (4 * p + 1)
          _ = w1 := hc8'1
      · calc
          cfgc'.tapeAt (4 * p + 2) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 2) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 2) := hstep_keeps hr11 hweq11 (4 * p + 2)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 2) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 2) := hstep_keeps hr10 hweq10 (4 * p + 2)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 2) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 2) := hstep_keeps hr9 hweq9 (4 * p + 2)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 2) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 2) := hstep_keeps hr8 hweq8 (4 * p + 2)
          _ = w2 := hc8'2
      · calc
          cfgc'.tapeAt (4 * p + 3) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 3) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 3) := hstep_keeps hr11 hweq11 (4 * p + 3)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 3) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 3) := hstep_keeps hr10 hweq10 (4 * p + 3)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 3) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 3) := hstep_keeps hr9 hweq9 (4 * p + 3)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 3) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 3) := hstep_keeps hr8 hweq8 (4 * p + 3)
          _ = w3 := hc8'3
    have htail : ∀ z : ℤ, z < 4 * p - 4 ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro z hz
      have hd_toInt : -1 ≤ (r.moveDir).toInt ∧ (r.moveDir).toInt ≤ 1 := by
        cases r.moveDir <;> simp [Dir.toInt]
      rw [hc11]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg11) step11.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp11] <;> omega)]
      rw [hc10]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg10) step10.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp10] <;> omega)]
      rw [hc9]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg9) step9.result z (by
        rw [hp9]
        dsimp [d]
        rcases hz with hz1 | hz2 <;> omega)]
      rw [hc8]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg8) step8.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp8] <;> omega)]
      rw [hc7]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg7) step7.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp7] <;> omega)]
      rw [hc6]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg6) step6.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp6] <;> omega)]
      rw [hc5]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg5) step5.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp5] <;> omega)]
      rw [hc4]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg4) step4.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp4] <;> omega)]
      rw [hc3]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg3) step3.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp3] <;> omega)]
      rw [hc2]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg2) step2.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp2] <;> omega)]
      rw [hc1]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg1) step1.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp1] <;> omega)]
      rw [hc0]
      rw [stepConfig_tape_eq_of_ne (cfg := cfgc) step0.result z (by
        rcases hz with hz1 | hz2 <;> omega)]
    have htailS_R : r.moveDir = Dir.S → ∀ z : ℤ, z < 4 * p ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro hs
      rw [hs] at hd
      cases hd
    have htailR : ∀ z : ℤ, z < 4 * p ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro z hzR
      have hd_toInt : -1 ≤ (r.moveDir).toInt ∧ (r.moveDir).toInt ≤ 1 := by
        cases r.moveDir <;> simp [Dir.toInt]
      rw [hc11]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg11) step11.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp11] <;> omega)]
      rw [hc10]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg10) step10.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp10] <;> omega)]
      rw [hc9]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg9) step9.result z (by
        rw [hp9]
        dsimp [d]
        rw [hd]
        simp [Dir.toInt]
        rcases hzR with hz1 | hz2 <;> omega)]
      rw [hc8]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg8) step8.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp8] <;> omega)]
      rw [hc7]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg7) step7.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp7] <;> omega)]
      rw [hc6]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg6) step6.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp6] <;> omega)]
      rw [hc5]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg5) step5.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp5] <;> omega)]
      rw [hc4]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg4) step4.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp4] <;> omega)]
      rw [hc3]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg3) step3.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp3] <;> omega)]
      rw [hc2]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg2) step2.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp2] <;> omega)]
      rw [hc1]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg1) step1.result z (by
        rcases hzR with hz1 | hz2 <;> rw [hp1] <;> omega)]
      rw [hc0]
      rw [stepConfig_tape_eq_of_ne (cfg := cfgc) step0.result z (by
        rcases hzR with hz1 | hz2 <;> omega)]


    have htailP1_R : ∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * (p - 1) + j) = cfgc.tapeAt (4 * (p - 1) + j) := by
      intro j hj
      unfold CBTMConfig.tapeAt
      have hz : 4 * (p - 1) + j < 4 * p := by omega
      exact htailR (4 * (p - 1) + j) (Or.inl hz)

    refine ⟨sym, r, h, hlen, hq, hp, hcorr, hqmem, hbranch, hvalid_sym, hstep4, hmk, hr, hst_final, hhead_final, htail, htailS_R, htailP1_R, hwrite, hso_read⟩
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
    have hstep_keeps {cfga : CBTMConfig subsetSumCBTM w} {step : TransitionStep}
        (hread : step.readSym = cfga.tapeAt cfga.headPos)
        (hweq : step.result.writeSym = step.readSym) (z : ℤ) :
        (stepConfig cfga step.result).tapeAt z = cfga.tapeAt z := by
      dsimp [CBTMConfig.tapeAt, stepConfig]
      change (if z = cfga.headPos then step.result.writeSym else cfga.tape z) = cfga.tape z
      by_cases hz : z = cfga.headPos
      · simp [hz, hweq, hread, CBTMConfig.tapeAt]
      · simp [hz]
    have hweq7 : step7.result.writeSym = step7.readSym := by
      rw [hres7, hrd7]
    have hweq8 : step8.result.writeSym = step8.readSym := by
      rw [hres8, hrd8]
    have hweq9 : step9.result.writeSym = step9.readSym := by
      rw [hres9, hrd9]
    have hweq10 : step10.result.writeSym = step10.readSym := by
      rw [hres10, hrd10]
    have hweq11 : step11.result.writeSym = step11.readSym := by
      rw [hres11, hrd11]
    have hwrite : ∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * p + j) = (symTo4F4 r.writeSym).getD j F4.zero := by
      intro j hj
      interval_cases j
      · calc
          cfgc'.tapeAt (4 * p + 0) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 0) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 0) := hstep_keeps hr11 hweq11 (4 * p + 0)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 0) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 0) := hstep_keeps hr10 hweq10 (4 * p + 0)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 0) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 0) := hstep_keeps hr9 hweq9 (4 * p + 0)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 0) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 0) := hstep_keeps hr8 hweq8 (4 * p + 0)
          _ = w0 := by simpa using hc8'0
      · calc
          cfgc'.tapeAt (4 * p + 1) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 1) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 1) := hstep_keeps hr11 hweq11 (4 * p + 1)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 1) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 1) := hstep_keeps hr10 hweq10 (4 * p + 1)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 1) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 1) := hstep_keeps hr9 hweq9 (4 * p + 1)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 1) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 1) := hstep_keeps hr8 hweq8 (4 * p + 1)
          _ = w1 := hc8'1
      · calc
          cfgc'.tapeAt (4 * p + 2) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 2) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 2) := hstep_keeps hr11 hweq11 (4 * p + 2)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 2) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 2) := hstep_keeps hr10 hweq10 (4 * p + 2)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 2) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 2) := hstep_keeps hr9 hweq9 (4 * p + 2)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 2) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 2) := hstep_keeps hr8 hweq8 (4 * p + 2)
          _ = w2 := hc8'2
      · calc
          cfgc'.tapeAt (4 * p + 3) = (stepConfig cfg11 step11.result).tapeAt (4 * p + 3) := by rw [hc11]
          _ = cfg11.tapeAt (4 * p + 3) := hstep_keeps hr11 hweq11 (4 * p + 3)
          _ = (stepConfig cfg10 step10.result).tapeAt (4 * p + 3) := by rw [hc10]
          _ = cfg10.tapeAt (4 * p + 3) := hstep_keeps hr10 hweq10 (4 * p + 3)
          _ = (stepConfig cfg9 step9.result).tapeAt (4 * p + 3) := by rw [hc9]
          _ = cfg9.tapeAt (4 * p + 3) := hstep_keeps hr9 hweq9 (4 * p + 3)
          _ = (stepConfig cfg8 step8.result).tapeAt (4 * p + 3) := by rw [hc8]
          _ = cfg8.tapeAt (4 * p + 3) := hstep_keeps hr8 hweq8 (4 * p + 3)
          _ = w3 := hc8'3
    have htail : ∀ z : ℤ, z < 4 * p - 4 ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro z hz
      have hd_toInt : -1 ≤ (r.moveDir).toInt ∧ (r.moveDir).toInt ≤ 1 := by
        cases r.moveDir <;> simp [Dir.toInt]
      rw [hc11]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg11) step11.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp11] <;> omega)]
      rw [hc10]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg10) step10.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp10] <;> omega)]
      rw [hc9]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg9) step9.result z (by
        rw [hp9]
        dsimp [d]
        rcases hz with hz1 | hz2 <;> omega)]
      rw [hc8]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg8) step8.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp8] <;> omega)]
      rw [hc7]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg7) step7.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp7] <;> omega)]
      rw [hc6]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg6) step6.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp6] <;> omega)]
      rw [hc5]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg5) step5.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp5] <;> omega)]
      rw [hc4]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg4) step4.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp4] <;> omega)]
      rw [hc3]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg3) step3.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp3] <;> omega)]
      rw [hc2]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg2) step2.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp2] <;> omega)]
      rw [hc1]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg1) step1.result z (by
        rcases hz with hz1 | hz2 <;> rw [hp1] <;> omega)]
      rw [hc0]
      rw [stepConfig_tape_eq_of_ne (cfg := cfgc) step0.result z (by
        rcases hz with hz1 | hz2 <;> omega)]
    have htailS : r.moveDir = Dir.S → ∀ z : ℤ, z < 4 * p ∨ 4 * p + 3 < z → cfgc'.tape z = cfgc.tape z := by
      intro hmS z hzS
      have hd_toInt : -1 ≤ (r.moveDir).toInt ∧ (r.moveDir).toInt ≤ 1 := by
        cases r.moveDir <;> simp [Dir.toInt]
      rw [hc11]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg11) step11.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp11] <;> omega)]
      rw [hc10]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg10) step10.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp10] <;> omega)]
      rw [hc9]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg9) step9.result z (by
        rw [hp9]
        dsimp [d]
        rw [hmS]
        simp [Dir.toInt]
        rcases hzS with hz1 | hz2 <;> omega)]
      rw [hc8]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg8) step8.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp8] <;> omega)]
      rw [hc7]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg7) step7.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp7] <;> omega)]
      rw [hc6]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg6) step6.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp6] <;> omega)]
      rw [hc5]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg5) step5.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp5] <;> omega)]
      rw [hc4]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg4) step4.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp4] <;> omega)]
      rw [hc3]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg3) step3.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp3] <;> omega)]
      rw [hc2]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg2) step2.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp2] <;> omega)]
      rw [hc1]
      rw [stepConfig_tape_eq_of_ne (cfg := cfg1) step1.result z (by
        rcases hzS with hz1 | hz2 <;> rw [hp1] <;> omega)]
      rw [hc0]
      rw [stepConfig_tape_eq_of_ne (cfg := cfgc) step0.result z (by
        rcases hzS with hz1 | hz2 <;> omega)]

    have htailP1_S : ∀ j : ℕ, j < 4 → cfgc'.tapeAt (4 * (p - 1) + j) = cfgc.tapeAt (4 * (p - 1) + j) := by
      intro j hj
      unfold CBTMConfig.tapeAt
      have hz : 4 * (p - 1) + j < 4 * p := by omega
      exact htailS hd (4 * (p - 1) + j) (Or.inl hz)
    refine ⟨sym, r, h, hlen, hq, hp, hcorr, hqmem, hbranch, hvalid_sym, hstep4, hmk, hr, hst_final, hhead_final, htail, htailS, htailP1_S, hwrite, hso_read⟩

-- ============================================================
-- q11b-1c:读格解码引理
-- ============================================================

/-- symOf4F4 解码成功 ⟹ 四格恰为 symTo4F4 sym 的编码。 -/
lemma cells_eq_of_symOf4F4 {a b c d : F4} {sym : Sym} (h : symOf4F4 a b c d = some sym) :
    a = (symTo4F4 sym).getD 0 F4.zero ∧ b = (symTo4F4 sym).getD 1 F4.zero ∧
    c = (symTo4F4 sym).getD 2 F4.zero ∧ d = (symTo4F4 sym).getD 3 F4.zero := by
  rcases a with ⟨ar, ai⟩
  rcases b with ⟨br, bi⟩
  rcases c with ⟨cr, ci⟩
  rcases d with ⟨dr, di⟩
  cases ar <;> cases ai <;> cases br <;> cases bi <;> cases cr <;> cases ci <;> cases dr <;> cases di
  all_goals
    simp [symOf4F4, F4.zero, F4.one, F4.alpha, F4.beta, Sym.data0, Sym.data1, Sym.alpha, Sym.beta,
      Sym.consumed, Sym.boundary, Sym.sel, Sym.nosel, Sym.mk] at h
    first | done |
      rw [← h]
      unfold symTo4F4
      simp [Sym.kindBits, F4.zero, F4.one, F4.alpha, F4.beta]

set_option maxRecDepth 20000 in
/-- 无陷阱 12 步块的读格可解码(块首 4 格解码为某 Sym)。 -/
lemma decode_read_cells_of_no_trap {w : List F4} {cfgc0 cfgc' : CBTMConfig subsetSumCBTM w}
    {πb : ComputationPath} {p : ℤ} {q : ℕ}
    (hb : TapeSteps subsetSumCBTM w cfgc0 πb cfgc')
    (hlen : πb.length = 12)
    (hph0 : (decodeState cfgc0.state).2.1 = 0)
    (hq : cfgc0.state = encodeState q 0 0) (hqle : q ≤ 101)
    (hp : cfgc0.headPos = 4 * p)
    (htrap : ∀ k (hk : k < πb.length), (decodeState (πb.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∃ sym : Sym, symOf4F4 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1))
      (cfgc0.tapeAt (4 * p + 2)) (cfgc0.tapeAt (4 * p + 3)) = some sym := by
  -- 拆出前 4 步
  rcases tapeSteps_split_last hb (by intro h0; simp [h0] at hlen) with
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
    ⟨step0, πn, cfgc0', hπen, hn, hf0, hr0, ht0, hc0⟩
  have hπn : πn = [] := by
    have hsum : (πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by
      simpa [hπen, hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
    have hsum' : πn.length + 12 = 12 := by simpa using hsum
    have hlen0 : πn.length = 0 := by omega
    cases πn with
    | nil => rfl
    | cons x xs => simp at hlen0
  have hcfg0 : cfgc0' = cfgc0 := tapeSteps_empty hn hπn
  subst πn
  subst cfgc0'
  have hπall : πb = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
    rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
    simp
  -- 前 3 步移动:step0 读 4p 移 R(im=false 由 trap 排除)
  have hst0 : step0.fromState = encodeState q 0 0 := by simpa [hq] using hf0
  have hrd0 : step0.readSym = cfgc0.tapeAt (4 * p) := by simpa [hp] using hr0
  have hmem0 : step0.result ∈ transition4 (encodeState q 0 0) (cfgc0.tapeAt (4 * p)) := by
    have ht0' : step0.result ∈ subsetSumCBTM.transition (cfgc0.state, cfgc0.tapeAt cfgc0.headPos, cfgc0.headPos) := ht0
    rw [hq, hp] at ht0'
    simpa [subsetSumCBTM] using ht0'
  have hdec0 : decodeState (encodeState q 0 0) = (q, 0, 0) :=
    decodeState_encodeState q 0 0 (by norm_num) (by norm_num)
  have him0 : F4.im (cfgc0.tapeAt (4 * p)) = false := by
    by_contra hfalse
    dsimp [transition4] at hmem0
    rw [hdec0] at hmem0
    simp [hfalse] at hmem0
    rcases hmem0 with h1 | h1
    all_goals
      have htr := htrap 0 (by simp [hlen])
      have hg0 : πb.get ⟨0, by simp [hlen]⟩ = step0 := by
        simp [hπall]
      rw [hg0] at htr
      rw [h1] at htr
      have h101 : (decodeState (encodeState 101 1 0)).1 = 101 := by
        rw [decodeState_encodeState 101 1 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
  have hres0 : step0.result = CBTMTransResult.mk (encodeState (min q 101) 1 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))
      (cfgc0.tapeAt (4 * p)) Dir.R := by
    dsimp [transition4] at hmem0
    rw [hdec0] at hmem0
    simp [him0] at hmem0
    exact hmem0
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
    dsimp
    rw [hp]
    simp [Dir.toInt]
  -- step1 读 4p+1 移 R
  have hrd1 : step1.readSym = cfgc0.tapeAt (4 * p + 1) := by
    have hrd1' : step1.readSym = cfg1.tapeAt cfg1.headPos := by simpa using hr1
    rw [hrd1', hp1, hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc0 step0.result (4 * p + 1) (by rw [hp]; omega)]
  have hmem1 : step1.result ∈ transition4 (encodeState (min q 101) 1 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0)) (cfgc0.tapeAt (4 * p + 1)) := by
    have ht1' : step1.result ∈ subsetSumCBTM.transition (cfg1.state, cfg1.tapeAt cfg1.headPos, cfg1.headPos) := ht1
    rw [show cfg1.state = encodeState (min q 101) 1 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) by
      rw [hc0]
      dsimp [stepConfig]
      rw [hres0]] at ht1'
    rw [hp1] at ht1'
    rw [show cfg1.tapeAt (4 * p + 1) = cfgc0.tapeAt (4 * p + 1) by
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc0 step0.result (4 * p + 1) (by rw [hp]; omega)]] at ht1'
    simpa [subsetSumCBTM] using ht1'
  have him1 : F4.im (cfgc0.tapeAt (4 * p + 1)) = false := by
    by_contra hfalse
    dsimp [transition4] at hmem1
    rw [decodeState_encodeState (min q 101) 1 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) (by norm_num) (by
        dsimp [bufOf3s, bufOf3]
        rcases cfgc0.tapeAt (4 * p) with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> norm_num [bufOf3s, bufOf3, F4.zero, F4.one, F4.alpha, F4.beta])] at hmem1
    simp [hfalse] at hmem1
    rcases hmem1 with h1r | h1r
    all_goals
      have htr := htrap 1 (by simp [hlen])
      have hg1 : πb.get ⟨1, by simp [hlen]⟩ = step1 := by
        simp [hπall]
      rw [hg1] at htr
      rw [h1r] at htr
      have h101 : (decodeState (encodeState 101 2 0)).1 = 101 := by
        rw [decodeState_encodeState 101 2 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
  have hres1 : step1.result = CBTMTransResult.mk
      (encodeState (min q 101) 2 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0)))
      (cfgc0.tapeAt (4 * p + 1)) Dir.R := by
    dsimp [transition4] at hmem1
    rw [decodeState_encodeState (min q 101) 1 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) (by norm_num) (by
        dsimp [bufOf3s, bufOf3]
        rcases cfgc0.tapeAt (4 * p) with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> norm_num [bufOf3s, bufOf3, F4.zero, F4.one, F4.alpha, F4.beta])] at hmem1
    simp [him1] at hmem1
    exact hmem1
  have hp2 : cfg2.headPos = 4 * p + 2 := by
    rw [hc1]
    dsimp [stepConfig]
    rw [hres1]
    dsimp
    rw [hp1]
    simp [Dir.toInt]
    omega
  -- step2 读 4p+2 移 R
  have hrd2 : step2.readSym = cfgc0.tapeAt (4 * p + 2) := by
    have hrd2' : step2.readSym = cfg2.tapeAt cfg2.headPos := by simpa using hr2
    rw [hrd2', hp2, hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 2) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc0 step0.result (4 * p + 2) (by rw [hp]; omega)]
  have hmem2 : step2.result ∈ transition4
      (encodeState (min q 101) 2 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0)))
      (cfgc0.tapeAt (4 * p + 2)) := by
    have ht2' : step2.result ∈ subsetSumCBTM.transition (cfg2.state, cfg2.tapeAt cfg2.headPos, cfg2.headPos) := ht2
    rw [show cfg2.state = encodeState (min q 101) 2
        (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0)) by
      rw [hc1]
      dsimp [stepConfig]
      rw [hres1]] at ht2'
    rw [hp2] at ht2'
    rw [show cfg2.tapeAt (4 * p + 2) = cfgc0.tapeAt (4 * p + 2) by
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 2) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc0 step0.result (4 * p + 2) (by rw [hp]; omega)]] at ht2'
    simpa [subsetSumCBTM] using ht2'
  have him2 : F4.im (cfgc0.tapeAt (4 * p + 2)) = false := by
    by_contra hfalse
    dsimp [transition4] at hmem2
    rw [decodeState_encodeState (min q 101) 2
        (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))
        (by norm_num) (by
        dsimp [bufOf3s, bufOf3]
        rcases cfgc0.tapeAt (4 * p) with ⟨r0, i0⟩ <;> rcases cfgc0.tapeAt (4 * p + 1) with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> norm_num [bufOf3s, bufOf3, F4.zero, F4.one, F4.alpha, F4.beta])] at hmem2
    simp [hfalse] at hmem2
    rcases hmem2 with h2r | h2r
    all_goals
      have htr := htrap 2 (by simp [hlen])
      have hg2 : πb.get ⟨2, by simp [hlen]⟩ = step2 := by
        simp [hπall]
      rw [hg2] at htr
      rw [h2r] at htr
      have h101 : (decodeState (encodeState 101 3 0)).1 = 101 := by
        rw [decodeState_encodeState 101 3 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
  have hres2 : step2.result = CBTMTransResult.mk
      (encodeState (min q 101) 3 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) +
        bufOf3s 2 (cfgc0.tapeAt (4 * p + 2)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))))
      (cfgc0.tapeAt (4 * p + 2)) Dir.R := by
    dsimp [transition4] at hmem2
    rw [decodeState_encodeState (min q 101) 2
        (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))
        (by norm_num) (by
        dsimp [bufOf3s, bufOf3]
        rcases cfgc0.tapeAt (4 * p) with ⟨r0, i0⟩ <;> rcases cfgc0.tapeAt (4 * p + 1) with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> norm_num [bufOf3s, bufOf3, F4.zero, F4.one, F4.alpha, F4.beta])] at hmem2
    simp [him2] at hmem2
    exact hmem2
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [hp2]
    simp [Dir.toInt]
    omega
  -- step3 读 4p+3,phase 3 合成:不可解码 → trap
  have hrd3 : step3.readSym = cfgc0.tapeAt (4 * p + 3) := by
    have hrd3' : step3.readSym = cfg3.tapeAt cfg3.headPos := by simpa using hr3
    rw [hrd3', hp3, hc2]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 3) (by rw [hp2]; omega)]
    rw [hc1]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 3) (by rw [hp1]; omega)]
    rw [hc0]
    rw [stepConfig_tapeAt_eq_of_ne cfgc0 step0.result (4 * p + 3) (by rw [hp]; omega)]
  have hmem3 : step3.result ∈ transition4
      (encodeState (min q 101) 3 (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) +
        bufOf3s 2 (cfgc0.tapeAt (4 * p + 2)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))))
      (cfgc0.tapeAt (4 * p + 3)) := by
    have ht3' : step3.result ∈ subsetSumCBTM.transition (cfg3.state, cfg3.tapeAt cfg3.headPos, cfg3.headPos) := ht3
    rw [show cfg3.state = encodeState (min q 101) 3
        (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) +
        bufOf3s 2 (cfgc0.tapeAt (4 * p + 2)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))) by
      rw [hc2]
      dsimp [stepConfig]
      rw [hres2]] at ht3'
    rw [hp3] at ht3'
    rw [show cfg3.tapeAt (4 * p + 3) = cfgc0.tapeAt (4 * p + 3) by
      rw [hc2]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * p + 3) (by rw [hp2]; omega)]
      rw [hc1]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * p + 3) (by rw [hp1]; omega)]
      rw [hc0]
      rw [stepConfig_tapeAt_eq_of_ne cfgc0 step0.result (4 * p + 3) (by rw [hp]; omega)]] at ht3'
    simpa [subsetSumCBTM] using ht3'
  by_contra hnone
  push Not at hnone
  have hso4 : symOf4F4 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1))
      (cfgc0.tapeAt (4 * p + 2)) (cfgc0.tapeAt (4 * p + 3)) = none ∨
      ∃ s : Sym, symOf4F4 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1))
        (cfgc0.tapeAt (4 * p + 2)) (cfgc0.tapeAt (4 * p + 3)) = some s := by
    rcases symOf4F4 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1))
        (cfgc0.tapeAt (4 * p + 2)) (cfgc0.tapeAt (4 * p + 3)) with _ | s <;> simp
  rcases hso4 with hnone' | hsome'
  · -- symOf4F4 none → phase 3 的 trap 分支 → htrap 3 矛盾
    have hmem3n := hmem3
    dsimp [transition4] at hmem3n
    rw [decodeState_encodeState (min q 101) 3
        (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) +
          bufOf3s 2 (cfgc0.tapeAt (4 * p + 2)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0)))
        (by norm_num) (by
        dsimp [bufOf3s, bufOf3]
        rcases cfgc0.tapeAt (4 * p) with ⟨r0, i0⟩ <;> rcases cfgc0.tapeAt (4 * p + 1) with ⟨r1, i1⟩ <;>
          rcases cfgc0.tapeAt (4 * p + 2) with ⟨r2, i2⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;> norm_num [bufOf3s, bufOf3, F4.zero, F4.one, F4.alpha, F4.beta])] at hmem3n
    have hreg3b : bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) +
          bufOf3s 2 (cfgc0.tapeAt (4 * p + 2)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0)) =
        bufOf3 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1)) (cfgc0.tapeAt (4 * p + 2)) := by
      rcases cfgc0.tapeAt (4 * p) with ⟨r0, i0⟩ <;> rcases cfgc0.tapeAt (4 * p + 1) with ⟨r1, i1⟩ <;>
        rcases cfgc0.tapeAt (4 * p + 2) with ⟨r2, i2⟩
      cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
        norm_num [bufOf3s, bufOf3, F4.zero, F4.one, F4.alpha, F4.beta]
    have hfab : f4ofBuf (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0) +
          bufOf3s 2 (cfgc0.tapeAt (4 * p + 2)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0 + bufOf3s 1 (cfgc0.tapeAt (4 * p + 1)) (bufOf3s 0 (cfgc0.tapeAt (4 * p)) 0))) =
        (cfgc0.tapeAt (4 * p), cfgc0.tapeAt (4 * p + 1), cfgc0.tapeAt (4 * p + 2)) := by
      rw [hreg3b]
      exact f4ofBuf_bufOf3 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1)) (cfgc0.tapeAt (4 * p + 2))
    rw [hfab, hnone'] at hmem3n
    simp at hmem3n
    have htr3 : step3.result = CBTMTransResult.mk (encodeState 101 4 0) (cfgc0.tapeAt (4 * p + 3)) Dir.S ∨
        step3.result = CBTMTransResult.mk (encodeState 101 4 0) (cfgc0.tapeAt (4 * p + 3)) Dir.R := by
      by_cases him3 : F4.im (cfgc0.tapeAt (4 * p + 3))
      · simp [him3, Finset.mem_insert, Finset.mem_singleton] at hmem3n
        rcases hmem3n with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      · simp [him3, Finset.mem_insert, Finset.mem_singleton] at hmem3n
        exact Or.inl hmem3n
    rcases htr3 with h3r | h3r
    · have htr := htrap 3 (by simp [hlen])
      have hg3 : πb.get ⟨3, by simp [hlen]⟩ = step3 := by
        simp [hπall]
      rw [hg3] at htr
      rw [h3r] at htr
      have h101 : (decodeState (encodeState 101 4 0)).1 = 101 := by
        rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim
    · have htr := htrap 3 (by simp [hlen])
      have hg3 : πb.get ⟨3, by simp [hlen]⟩ = step3 := by
        simp [hπall]
      rw [hg3] at htr
      rw [h3r] at htr
      have h101 : (decodeState (encodeState 101 4 0)).1 = 101 := by
        rw [decodeState_encodeState 101 4 0 (by norm_num) (by norm_num)]
      exact (htr h101).elim


  · rcases hsome' with ⟨s, hs⟩
    exfalso
    exact hnone s hs

-- ============================================================
-- q11b-1c:Sym 层输入扩展的重放引理
-- ============================================================

/-- symInitialConfig 于 w 与 w ++ [s] 在 i < |w| 处相同。 -/
lemma symInitialConfig_extend_lt {w : List Sym} {s : Sym} (i : ℤ) (hi : i < w.length) :
    (symInitialConfig (w ++ [s])).tape i = (symInitialConfig w).tape i := by
  unfold symInitialConfig
  by_cases h0 : 0 ≤ i
  · have hi' : i.toNat < w.length := by
      have h1 : (i.toNat : ℤ) < (w.length : ℤ) := by
        rw [Int.toNat_of_nonneg h0]
        exact hi
      exact_mod_cast h1
    have hi2 : i.toNat < (w ++ [s]).length := by
      simp [List.length_append]
      omega
    have hci : i ≤ (w.length : ℤ) := by omega
    have hL : (if h : 0 ≤ i ∧ i.toNat < (w ++ [s]).length then (w ++ [s]).get ⟨i.toNat, h.2⟩ else Sym.blank) =
        (w ++ [s]).get ⟨i.toNat, hi2⟩ := by
      simp [h0, hi2, hci]
    have hR : (if h : 0 ≤ i ∧ i.toNat < w.length then w.get ⟨i.toNat, h.2⟩ else Sym.blank) =
        w.get ⟨i.toNat, hi'⟩ := by
      simp [h0, hi']
    change (if h : 0 ≤ i ∧ i.toNat < (w ++ [s]).length then (w ++ [s]).get ⟨i.toNat, h.2⟩ else Sym.blank) =
      (if h : 0 ≤ i ∧ i.toNat < w.length then w.get ⟨i.toNat, h.2⟩ else Sym.blank)
    rw [hL, hR]
    exact List.getElem_append_left hi'
  · simp [h0]

lemma symSteps_lift_extend {w : List Sym} {s : Sym} {πs : List SymStep} {cfgs : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig w) πs cfgs)
    (hheads : ∀ (πs₀ : List SymStep) (cfgm : SymConfig),
      πs₀ <+: πs → πs₀ ≠ πs →
      SymSteps VerifierSym.transition (symInitialConfig w) πs₀ cfgm → cfgm.headPos < w.length) :
    ∃ cfgs' : SymConfig, SymSteps VerifierSym.transition (symInitialConfig (w ++ [s])) πs cfgs' ∧
      cfgs'.state = cfgs.state ∧ (∀ i : ℤ, i < w.length → cfgs'.tape i = cfgs.tape i) ∧
      cfgs'.headPos = cfgs.headPos ∧ cfgs'.tape ↑w.length = s := by
  induction h with
  | nil =>
      refine ⟨symInitialConfig (w ++ [s]), SymSteps.nil, rfl, ?_, rfl, ?_⟩
      · intro i hi
        exact symInitialConfig_extend_lt i hi
      · simp [symInitialConfig]
  | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hheads₀ : ∀ (πs₀' : List SymStep) (cfgm : SymConfig),
          πs₀' <+: πs₀ → πs₀' ≠ πs₀ →
          SymSteps VerifierSym.transition (symInitialConfig w) πs₀' cfgm → cfgm.headPos < w.length := by
        intro πs₀' cfgm hpre hne hh
        exact hheads πs₀' cfgm (List.IsPrefix.trans hpre ⟨[step], rfl⟩) (by
          intro heq
          have hlen2 : πs₀'.length = πs₀.length + 1 := by
            simpa using congrArg List.length heq
          rcases hpre with ⟨r, hr⟩
          have hlenr : πs₀'.length ≤ πs₀.length := by
            have : πs₀'.length + r.length = πs₀.length := by
              simpa using congrArg List.length hr
            omega
          omega) hh
      have hhead₀ : cfg₁.headPos < w.length := hheads πs₀ cfg₁ ⟨[step], rfl⟩ (by
        intro heq
        have : (πs₀ ++ [step]).length = πs₀.length := by
          simpa using congrArg List.length heq
        simp at this) hprev
      rcases ih hheads₀ with ⟨cfg₁', hprev', hs₁, ht₁, hp₁, ht₁'⟩
      refine ⟨symStepConfig cfg₁' step.result, SymSteps.cons πs₀ step cfg₁' hprev' ?_ ?_ ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs₁]
        exact hfrom
      · rw [hp₁, ht₁ cfg₁.headPos hhead₀]
        exact hread
      · rw [hs₁, hp₁, ht₁ cfg₁.headPos hhead₀]
        exact htrans
      · dsimp [symStepConfig]
      · intro i hi
        dsimp [symStepConfig]
        by_cases hz : i = cfg₁'.headPos
        · simp [hz, hp₁]
        · have hz' : i ≠ cfg₁.headPos := by
            intro heq
            apply hz
            rw [← hp₁] at heq
            exact heq
          simp [hz, hz', ht₁ i hi]
      · dsimp [symStepConfig]
        rw [hp₁]
      · dsimp [symStepConfig]
        have hnz : ↑w.length ≠ cfg₁'.headPos := by
          intro heq
          have hlt : cfg₁'.headPos < w.length := by
            rw [hp₁]
            exact hhead₀
          omega
        simp [hnz, ht₁']


lemma symSteps_split_last {M : ℕ × Sym → Finset SymTransResult} {cfg₀ : SymConfig}
    {πs : List SymStep} {cfgs : SymConfig}
    (h : SymSteps M cfg₀ πs cfgs) (hπ : πs ≠ []) :
    ∃ step : SymStep, ∃ πs₀ : List SymStep, ∃ cfg₁ : SymConfig,
      πs = πs₀ ++ [step] ∧ SymSteps M cfg₀ πs₀ cfg₁ ∧
      step.fromState = cfg₁.state ∧ step.readSym = cfg₁.tape cfg₁.headPos ∧
      step.result ∈ M (cfg₁.state, cfg₁.tape cfg₁.headPos) ∧
      cfgs = symStepConfig cfg₁ step.result := by
  cases h with
  | nil => exact (hπ rfl).elim
  | cons πs₀ step cfg₁ hprev hfrom hread htrans =>
      exact ⟨step, πs₀, cfg₁, rfl, hprev, hfrom, hread, htrans, rfl⟩

/-- SymSteps 于空路径的终点 = 起点。 -/
lemma symSteps_empty {M : ℕ × Sym → Finset SymTransResult} {cfg₀ : SymConfig}
    {πs : List SymStep} {cfgs : SymConfig}
    (h : SymSteps M cfg₀ πs cfgs) (hπ : πs = []) : cfgs = cfg₀ := by
  have h' : πs = [] → cfgs = cfg₀ := by
    induction h with
    | nil => intro _; rfl
    | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
        intro heq
        have : (πs₀ ++ [step]).length = 0 := by simpa using congrArg List.length heq
        simp at this
  exact h' hπ

/-- SymSteps 步数 ≥ 终点头(头从 0 起,每步移动 ≤ 1)。 -/
lemma symSteps_length_ge_headPos {M : ℕ × Sym → Finset SymTransResult} {input : List Sym}
    {πs : List SymStep} {cfgs : SymConfig}
    (h : SymSteps M (symInitialConfig input) πs cfgs) :
    cfgs.headPos ≤ πs.length := by
  induction h with
  | nil => simp [symInitialConfig]
  | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hd : (step.result.moveDir).toInt ≤ 1 := by
        cases step.result.moveDir <;> simp [Dir.toInt]
      dsimp [symStepConfig]
      simp [List.length_append]
      omega

/-- take 4 (drop n) = symTo4F4(逐格 getElem 一致)。 -/
lemma take4_drop_eq {wExt : List F4} {wS : List Sym} {sym' : Sym}
    (hlen : 4 * wS.length + 4 ≤ wExt.length)
    (hg : ∀ j : ℕ, (hj : j < 4) → wExt[4 * wS.length + j]'(by omega) =
      (symTo4F4 sym')[j]'(by simpa [symTo4F4_length] using hj)) :
    List.take 4 (List.drop (4 * wS.length) wExt) = symTo4F4 sym' := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, symTo4F4_length]
    omega
  · intro n h1 h2
    have hn : n < 4 := by
      have : n < (symTo4F4 sym').length := h2
      simpa [symTo4F4_length] using this
    rw [List.getElem_take (xs := List.drop (4 * wS.length) wExt) (j := 4) (i := n)]
    rw [List.getElem_drop (xs := wExt) (i := 4 * wS.length) (j := n)]
    exact hg n hn

/-- 扩展带路径(头不越 w.length,由 w 带头界保证)可截断回 w 带。 -/
lemma symSteps_restrict' {w : List Sym} {s : Sym} {πs πsFull : List SymStep} {cfgm : SymConfig}
    (hpre : πs <+: πsFull)
    (h : SymSteps VerifierSym.transition (symInitialConfig (w ++ [s])) πs cfgm)
    (hheads : ∀ (πs₁ : List SymStep) (cfgm₁ : SymConfig),
      πs₁ <+: πsFull → πs₁ ≠ πsFull →
      SymSteps VerifierSym.transition (symInitialConfig w) πs₁ cfgm₁ → cfgm₁.headPos < w.length) :
    ∃ cfgm₀ : SymConfig,
      SymSteps VerifierSym.transition (symInitialConfig w) πs cfgm₀ ∧
      cfgm₀.state = cfgm.state ∧ cfgm₀.headPos = cfgm.headPos ∧
      (∀ i : ℤ, i < w.length → cfgm₀.tape i = cfgm.tape i) := by
  induction h with
  | nil =>
      refine ⟨symInitialConfig w, SymSteps.nil, rfl, rfl, ?_⟩
      · intro i hi
        exact (symInitialConfig_extend_lt i hi).symm
  | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hpre₀ : πs₀ <+: πsFull := List.IsPrefix.trans ⟨[step], rfl⟩ hpre
      rcases ih hpre₀ with ⟨cfg₁₀, hprev₀, hs₀, hp₀, ht₀⟩
      have hne₀ : πs₀ ≠ πsFull := by
        intro heq
        rcases hpre with ⟨r, hr⟩
        have hlen := congrArg List.length hr
        simp [List.length_append] at hlen
        rw [heq] at hlen
        omega
      have hhead₀ : cfg₁.headPos < w.length := by
        have : cfg₁₀.headPos < w.length := hheads πs₀ cfg₁₀ hpre₀ hne₀ hprev₀
        rw [← hp₀]
        exact this
      refine ⟨symStepConfig cfg₁₀ step.result, SymSteps.cons πs₀ step cfg₁₀ hprev₀ ?_ ?_ ?_, ?_, ?_, ?_⟩
      · rw [hs₀]
        exact hfrom
      · rw [hp₀, ht₀ cfg₁.headPos hhead₀]
        exact hread
      · rw [hs₀, hp₀, ht₀ cfg₁.headPos hhead₀]
        exact htrans
      · dsimp [symStepConfig]
      · dsimp [symStepConfig]
        rw [hp₀]
      · intro i hi
        dsimp [symStepConfig]
        by_cases hz : i = cfg₁₀.headPos
        · simp [hz, hp₀]
        · have hz' : i ≠ cfg₁.headPos := by
            intro heq
            apply hz
            rw [← hp₀] at heq
            exact heq
          simp [hz, hz', ht₀ i hi]

/-- 尾消:π₀ ++ [s] = π₁ ++ [t] ⟹ π₀ = π₁ ∧ s = t。 -/
lemma append_tail_unique {α : Type} {a b : List α} {s t : α}
    (h : a ++ [s] = b ++ [t]) : a = b ∧ s = t := by
  have hl : a.length = b.length := by
    have := congrArg List.length h
    simpa [List.length_append] using this
  have ht1 : a = b := by
    calc
      a = List.take a.length (a ++ [s]) := by simp [List.take_append_of_le_length]
      _ = List.take a.length (b ++ [t]) := by rw [h]
      _ = List.take b.length (b ++ [t]) := by rw [hl]
      _ = b := by simp [List.take_append_of_le_length]
  have ht2 : s = t := by
    have hdrop : List.drop a.length (a ++ [s]) = List.drop a.length (b ++ [t]) := by
      rw [h]
    have hdL : List.drop a.length (a ++ [s]) = [s] := by
      rw [List.drop_append_of_le_length (l₁ := a) (l₂ := [s]) (i := a.length) (Nat.le_refl _)]
      simp
    have hdR : List.drop a.length (b ++ [t]) = [t] := by
      rw [List.drop_append_of_le_length (l₁ := b) (l₂ := [t]) (i := a.length) (by omega : a.length ≤ b.length)]
      have hdropb : List.drop a.length b = [] := by
        rw [hl]
        simp
      rw [hdropb]
      simp
    rw [hdL, hdR] at hdrop
    injection hdrop with hs
  exact ⟨ht1, ht2⟩

/-- SymSteps 于同路径的终点唯一。 -/
lemma symSteps_end_unique {M : ℕ × Sym → Finset SymTransResult} {cfg₀ : SymConfig}
    {πs : List SymStep} {cfgs : SymConfig} (h : SymSteps M cfg₀ πs cfgs) :
    ∀ {cfgs' : SymConfig}, SymSteps M cfg₀ πs cfgs' → cfgs = cfgs' := by
  induction h with
  | nil =>
      intro cfgs' h'
      exact (symSteps_empty h' rfl).symm
  | cons πs₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro cfgs' h'
      rcases symSteps_split_last h' (by
        intro he
        have : (πs₀ ++ [step]).length = 0 := by
          rw [he]
          rfl
        simp at this) with ⟨step', πs₁, cfg₁', hπe', hprev', hfrom', hread', htrans', hcfgs'⟩
      have htail : πs₀ = πs₁ ∧ step = step' := by
        exact append_tail_unique hπe'
      rcases htail with ⟨hπeq, hsteq⟩
      subst πs₁
      subst step'
      have hcfg₁ : cfg₁ = cfg₁' := ih hprev'
      subst cfg₁'
      exact hcfgs'.symm

-- ============================================================
-- q11b-1 级 A:无 trap 接受路径逐块解码出 Sym 串
-- ============================================================

/-- 好块路径变体(Near 块)。 -/
inductive GoodBlockPathNear (w : List F4) :
    CBTMConfig subsetSumCBTM w → ComputationPath → CBTMConfig subsetSumCBTM w → Prop
  | nil : ∀ (cfgc : CBTMConfig subsetSumCBTM w), GoodBlockPathNear w cfgc [] cfgc
  | cons : ∀ (cfgc cfgm cfgc' : CBTMConfig subsetSumCBTM w) (πm π : ComputationPath)
      (cfgs : SymConfig) (p : ℤ) (q : ℕ) (sym : Sym) (r : SymTransResult),
      GoodBlockNear w cfgc πm cfgm cfgs p q sym r →
      GoodBlockPathNear w cfgm π cfgc' →
      GoodBlockPathNear w cfgc (πm ++ π) cfgc'

/-- GoodBlockPathNear 的串联。 -/
lemma GoodBlockPathNear_append (w : List F4) (cfgc cfgm cfgc' : CBTMConfig subsetSumCBTM w)
    (πm π : ComputationPath)
    (hm : GoodBlockPathNear w cfgc πm cfgm) (ht : GoodBlockPathNear w cfgm π cfgc') :
    GoodBlockPathNear w cfgc (πm ++ π) cfgc' := by
  induction hm generalizing cfgc' with
  | nil => simpa using ht
  | cons cfgc cfgm' cfgc'' πm' π' cfgs p q sym r hblock htail ih =>
      rw [List.append_assoc]
      exact GoodBlockPathNear.cons cfgc cfgm' cfgc' πm' (π' ++ π) cfgs p q sym r hblock (ih cfgc' ht)

lemma isPrefix_append_singleton {α : Type} {l l' : List α} {x : α}
    (h : l' <+: l ++ [x]) : l' <+: l ∨ l' = l ++ [x] := by
  rcases h with ⟨r, hr⟩
  by_cases hr' : r = []
  · right
    simpa [hr'] using hr
  · left
    have htake : List.take l'.length (l' ++ r) = List.take l'.length (l ++ [x]) := by
      rw [hr]
    have ht1 : List.take l'.length (l' ++ r) = l' := by
      rw [List.take_append_of_le_length (l₁ := l') (l₂ := r) (i := l'.length) (Nat.le_refl _)]
      simp
    have hrlen : 1 ≤ r.length := by
      cases r with
      | nil => exact (hr' rfl).elim
      | cons x rs => simp
    have hlen0 : l'.length ≤ l.length := by
      have := congrArg List.length hr
      simp [List.length_append] at this
      omega
    have htake' : l' = List.take l'.length l := by
      calc
        l' = List.take l'.length (l' ++ r) := ht1.symm
        _ = List.take l'.length (l ++ [x]) := htake
        _ = List.take l'.length l := by
          rw [List.take_append_of_le_length (l₁ := l) (l₂ := [x]) (i := l'.length) hlen0]
    refine ⟨List.drop l'.length l, ?_⟩
    rw [show l' ++ List.drop l'.length l = List.take l'.length l ++ List.drop l'.length l by
      exact congrArg (fun a => a ++ List.drop l'.length l) htake']
    exact List.take_append_drop l'.length l

lemma no_trap_path_phase {w : List F4} {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (hph0 : (decodeState cfg.state).2.1 = 0)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    π.length % 12 = 0 := by
  have hph := (path_phase_at h).1.1
  rw [hph0] at hph
  exact hph.symm

theorem no_trap_path_decodes_prefix {w : List F4} {π : ComputationPath}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (hacc : cfg.state ∈ acceptStates4)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∃ wS : List Sym, ∃ πs : List SymStep, ∃ cfgsEnd : SymConfig,
      w.take (4 * wS.length) = (flat4F4 wS).take w.length ∧
      SymSteps VerifierSym.transition (symInitialConfig wS) πs cfgsEnd ∧
      cfgsEnd.state = 100 ∧
      (∀ (πs₀ : List SymStep) (cfgm : SymConfig),
        πs₀ <+: πs → πs₀ ≠ πs →
        SymSteps VerifierSym.transition (symInitialConfig wS) πs₀ cfgm →
        cfgm.headPos < wS.length) ∧
      (∀ i : ℕ, 4 * i ≥ w.length → i < wS.length → wS.getD i Sym.blank = Sym.data0 false) ∧
      πs.length * 12 = π.length ∧
      cfgsEnd.headPos ≤ wS.length ∧
      blockCorrespondNear cfg cfgsEnd (cfgsEnd.headPos) ∧
      blockCorrespondUpto cfg cfgsEnd wS.length ∧
      (∀ z : ℤ, 4 * wS.length ≤ z → cfg.tape z =
        (initialConfig subsetSumCBTM w).tape z) := by
  let wExt := w ++ List.replicate (4 * π.length) F4.zero
  have htape : (initialConfig subsetSumCBTM w).tape = (initialConfig subsetSumCBTM wExt).tape :=
    initialTape_append_replicate_zero w (4 * π.length)
  rcases tapeSteps_lift_input h htape with ⟨cfgE, hE, hsE, htE, hpE⟩
  have haccE : cfgE.state ∈ acceptStates4 := by
    rw [hsE]
    exact hacc
  have hph0 : (decodeState cfgE.state).2.1 = 0 := by
    rcases Finset.mem_image.mp haccE with ⟨reg, hreg, hacc'⟩
    rw [← hacc']
    dsimp [decodeState, encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept]
    simp [Finset.mem_range] at hreg
    dsimp [regBound] at hreg
    omega
  have htrapE : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := htrap
  -- 强归纳不变式
  let P (n : ℕ) : Prop := ∀ (π : ComputationPath) (cfg : CBTMConfig subsetSumCBTM wExt),
    π.length = n →
    TapeSteps subsetSumCBTM wExt (initialConfig subsetSumCBTM wExt) π cfg →
    (decodeState cfg.state).2.1 = 0 →
    (∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) →
    ∃ wS : List Sym, ∃ πs : List SymStep, ∃ cfgsEnd : SymConfig,
      πs.length * 12 = π.length ∧
      (w ++ List.replicate (4 * π.length) F4.zero).take (4 * wS.length) = flat4F4 wS ∧
      GoodBlockPathNear wExt (initialConfig subsetSumCBTM wExt) π cfg ∧
      SymSteps VerifierSym.transition (symInitialConfig wS) πs cfgsEnd ∧
      cfgsEnd.state ≤ 101 ∧
      cfgsEnd.headPos ≤ wS.length ∧
      blockCorrespondNear cfg cfgsEnd (cfgsEnd.headPos) ∧
      blockCorrespondUpto cfg cfgsEnd wS.length ∧
      (∀ (z : ℤ), 4 * wS.length ≤ z → cfg.tape z =
        (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape z) ∧
      (∀ (πs₀ : List SymStep) (cfgm : SymConfig),
        πs₀ <+: πs → πs₀ ≠ πs →
        SymSteps VerifierSym.transition (symInitialConfig wS) πs₀ cfgm → cfgm.headPos < wS.length) ∧
      (∀ i : ℕ, 4 * i ≥ w.length → i < wS.length → wS.getD i Sym.blank = Sym.data0 false)
  have hmain : P π.length := by
    refine Nat.strong_induction_on π.length ?_
    intro n ih
    intro π cfg hlen_n h hph0' htrap'
    by_cases hn0 : n = 0
    · have hπ0 : π = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst π
      have hcfg : cfg = initialConfig subsetSumCBTM wExt := tapeSteps_empty h rfl
      subst cfg
      refine ⟨[], [], symInitialConfig [], ?hlen0, ?htake0, GoodBlockPathNear.nil _,
        SymSteps.nil, ?hle1, ?hle2, ?hnear0, ?hupto0, ?htail0, ?hreach0, ?hzeroTail0⟩
      · simp
      · simp [flat4F4]
      · simp [symInitialConfig]
      · simp [symInitialConfig]
      · -- Near (initialConfig wExt) (symInitialConfig []) 0:
        constructor
        · rfl
        constructor
        · rfl
        · intro j hj
          unfold CBTMConfig.tapeAt
          have hnz : ¬ (0 : ℤ) ≤ 4 * (0 - 1) + (j : ℤ) := by omega
          have hneg : ¬ (0 : ℤ) ≤ (0 : ℤ) - 1 := by norm_num
          simp [initialConfig, initialTapeOf, subsetSumCBTM, hnz, symInitialConfig, hneg]
          interval_cases j <;> simp [symTo4F4, Sym.blank, Sym.kindBits, F4.zero] <;> try rfl
      · -- Upto 0:
        constructor
        · rfl
        constructor
        · rfl
        · intro i hi j hj
          have hnz : ¬ (0 : ℤ) ≤ 4 * i + (j : ℤ) := by
            have hi0 : i < 0 := by simpa using hi
            omega
          unfold CBTMConfig.tapeAt
          simp [initialConfig, initialTapeOf, subsetSumCBTM, hnz]
          rw [show (symInitialConfig []).tape i = Sym.blank by
            simp [symInitialConfig]]
          interval_cases j <;> simp [symTo4F4, Sym.blank, Sym.kindBits, F4.zero] <;> try rfl
      · intro z hz
        rw [show w ++ List.replicate (4 * [].length) F4.zero = w by simp]
        exact (congrFun htape z).symm
      · intro πs₀ cfgm hpre hne hh
        have hπs0 : πs₀ = [] := by
          rcases hpre with ⟨r, hr⟩
          have : πs₀.length = 0 := by
            have hlen : (πs₀ ++ r).length = 0 := by simpa using congrArg List.length hr
            have hlen' : πs₀.length + r.length = 0 := by
              simpa [List.length_append] using hlen
            omega
          exact List.eq_nil_of_length_eq_zero this
        exact (hne hπs0).elim
      · intro i hge hil
        omega
    · have hlen_mod : π.length % 12 = 0 := by
        exact no_trap_path_phase h hph0' htrap'
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
      have hb1 : TapeSteps subsetSumCBTM wExt cfgc0 [step0] (stepConfig cfgc0 step0.result) :=
        TapeSteps.cons [] step0 cfgc0 (TapeSteps.nil) hf0 hr0 ht0
      have hb2 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1]
          (stepConfig (stepConfig cfgc0 step0.result) step1.result) :=
        TapeSteps.cons [step0] step1 (stepConfig cfgc0 step0.result) hb1
          (by simpa [hc0] using hf1) (by simpa [hc0] using hr1) (by simpa [hc0] using ht1)
      have hb3 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2]
          (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) :=
        TapeSteps.cons [step0, step1] step2 (stepConfig (stepConfig cfgc0 step0.result) step1.result) hb2
          (by simpa [hc0, hc1] using hf2) (by simpa [hc0, hc1] using hr2) (by simpa [hc0, hc1] using ht2)
      have hb4 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3]
          (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) :=
        TapeSteps.cons [step0, step1, step2] step3 (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) hb3
          (by simpa [hc0, hc1, hc2] using hf3) (by simpa [hc0, hc1, hc2] using hr3) (by simpa [hc0, hc1, hc2] using ht3)
      have hb5 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) :=
        TapeSteps.cons [step0, step1, step2, step3] step4 (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) hb4
          (by simpa [hc0, hc1, hc2, hc3] using hf4) (by simpa [hc0, hc1, hc2, hc3] using hr4) (by simpa [hc0, hc1, hc2, hc3] using ht4)
      have hb6 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4] step5 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) hb5
          (by simpa [hc0, hc1, hc2, hc3, hc4] using hf5) (by simpa [hc0, hc1, hc2, hc3, hc4] using hr5) (by simpa [hc0, hc1, hc2, hc3, hc4] using ht5)
      have hb7 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5, step6]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5] step6 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) hb6
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5] using hf6) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5] using hr6) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5] using ht6)
      have hb8 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6] step7 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) hb7
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6] using hf7) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6] using hr7) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6] using ht7)
      have hb9 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7] step8 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) hb8
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] using hf8) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] using hr8) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] using ht8)
      have hb10 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7, step8] step9 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) hb9
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] using hf9) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] using hr9) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8] using ht9)
      have hb11 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9] step10 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) hb10
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9] using hf10) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9] using hr10) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9] using ht10)
      have hb12 : TapeSteps subsetSumCBTM wExt cfgc0 [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]
          (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) step11.result) :=
        TapeSteps.cons [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10] step11 (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) hb11
          (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10] using hf11) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10] using hr11) (by simpa [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10] using ht11)
      have hb : TapeSteps subsetSumCBTM wExt cfgc0 πb cfg := by
        rw [show cfg = (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig (stepConfig cfgc0 step0.result) step1.result) step2.result) step3.result) step4.result) step5.result) step6.result) step7.result) step8.result) step9.result) step10.result) step11.result) from by
          rw [hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0]]
        simpa [πb] using hb12

      rcases ih πn.length hlt πn cfgc0 rfl hn hph0b htrapn with
        ⟨wS, πs, cfgsEnd, hlenS, htakeS, hgbp, hsteps, hqEnd, hheadEnd, hnear, hupto, htail0,
          hreach0, hzeroTailE⟩
      let p : ℤ := cfgsEnd.headPos
      have hq0 : cfgc0.state = encodeState cfgsEnd.state 0 0 := hnear.1
      have hhp0 : cfgc0.headPos = 4 * p := by
        dsimp [p]
        exact hnear.2.1
      have hqle0 : cfgsEnd.state ≤ 101 := hqEnd
      by_cases hpK : p < wS.length
      · -- 重读块
        have hpCellsA : ∀ j : ℕ, j < 4 → cfgc0.tapeAt (4 * p + j) =
            (symTo4F4 (cfgsEnd.tape p)).getD j F4.zero := by
          intro j hj
          exact hupto.2.2 p hpK j hj
        rcases twelve_steps_good_block_upto (h := hb) (hlen := by simp [πb]) hph0b htrapb hnear
            (sym := cfgsEnd.tape p) hpCellsA hq0 hqle0 hhp0 with ⟨symA, r, hblockA⟩
        have hbA_full : GoodBlockNear wExt cfgc0 πb cfg cfgsEnd p cfgsEnd.state symA r := hblockA
        rcases hblockA with ⟨hpathA, hlenA, hstA, hpA, hcorrBA, hqleA, hbranchA, hvalidA,
          hstep4A, hmkA, hrA, hst'A, hhead'A, htailBA, htailSA, htailP1A, hwriteA, hsoA⟩
        let stepA : SymStep := { fromState := cfgsEnd.state, readSym := cfgsEnd.tape p, result := r }
        have hsymA : symA = cfgsEnd.tape p := by
          exact symOf4F4_symTo4F4_getD_some (cfgsEnd.tape p) (by
            rw [← hpCellsA 0 (by omega), ← hpCellsA 1 (by omega), ← hpCellsA 2 (by omega),
              ← hpCellsA 3 (by omega)]
            simpa [p] using hsoA)
        have hrA' : r ∈ VerifierSym.transition (cfgsEnd.state, cfgsEnd.tape p) := by
          simpa [hsymA] using hrA
        have hgbpA : GoodBlockPathNear wExt (initialConfig subsetSumCBTM wExt) π cfg := by
          rw [hπall]
          exact GoodBlockPathNear_append wExt (initialConfig subsetSumCBTM wExt) cfgc0 cfg πn πb hgbp
            (GoodBlockPathNear.cons cfgc0 cfg cfg πb [] cfgsEnd p cfgsEnd.state symA r hbA_full (GoodBlockPathNear.nil cfg))
        refine ⟨wS, πs ++ [stepA], symStepConfig cfgsEnd r, ?hlenA', ?htakeA', ?hgbpA'', ?hstepsA',
          ?hqleA1', ?hheadA2', ?hnearA', ?huptoA', ?htailA', ?hreachA', ?hzeroTailA'⟩
        · rw [hπall]
          simp [List.length_append]
          nlinarith [hlenS]
        · have htakeS' : (w ++ List.replicate (4 * π.length) F4.zero).take (4 * wS.length) =
              (w ++ List.replicate (4 * πn.length) F4.zero).take (4 * wS.length) := by
            apply take_replicate_eq
            · have hlenT := congrArg List.length htakeS
              simp [flat4F4] at hlenT
              omega
            · have hlenT := congrArg List.length htakeS
              simp [flat4F4] at hlenT
              have hlenπ : 4 * πn.length ≤ 4 * π.length := by
                rw [hπall]
                simp [List.length_append]
              omega
          rw [htakeS']
          exact htakeS
        · exact hgbpA
        · exact SymSteps.cons πs stepA cfgsEnd hsteps rfl rfl hrA'
        · dsimp [symStepConfig]
          exact symTransition_nextState_le101 cfgsEnd.state (cfgsEnd.tape p) r hrA'
        · dsimp [symStepConfig]
          have hd : -1 ≤ (r.moveDir).toInt ∧ (r.moveDir).toInt ≤ 1 := by
            cases r.moveDir <;> simp [Dir.toInt]
          omega
        · constructor
          · exact hst'A
          constructor
          · dsimp [symStepConfig]
            rw [hhead'A]
            omega
          · intro j hj
            rw [show (symStepConfig cfgsEnd r).headPos = p + (r.moveDir).toInt by
              simp [symStepConfig, p]]
            rcases hd_r : r.moveDir with _ | _ | _
            · have hAr : p + Dir.L.toInt - 1 = p - 2 := by
                simp [Dir.toInt]
                ring
              rw [hAr]
              have hz : 4 * (p - 2) + j < 4 * p - 4 := by omega
              unfold CBTMConfig.tapeAt
              rw [htailBA (4 * (p - 2) + j) (Or.inl hz)]
              have hne : p - 2 ≠ cfgsEnd.headPos := by
                dsimp [p]
                omega
              have hstep : (symStepConfig cfgsEnd r).tape (p - 2) = cfgsEnd.tape (p - 2) := by
                simp [symStepConfig, hne]
              rw [hstep]
              have hp2 : p - 2 < wS.length := by
                dsimp [p] at hpK
                omega
              exact (by simpa [CBTMConfig.tapeAt] using hupto.2.2 (p - 2) hp2 j hj)
            · have hAr : p + Dir.R.toInt - 1 = p := by
                simp [Dir.toInt]
              rw [hAr]
              have hwrite : (symStepConfig cfgsEnd r).tape p = r.writeSym := by
                simp [symStepConfig, p]
              rw [hwrite]
              exact hwriteA j hj
            · have hAr : p + Dir.S.toInt - 1 = p - 1 := by
                simp [Dir.toInt]
              rw [hAr]
              have hz : 4 * (p - 1) + j < 4 * p := by omega
              unfold CBTMConfig.tapeAt
              rw [htailSA hd_r (4 * (p - 1) + j) (Or.inl hz)]
              have hne : p - 1 ≠ cfgsEnd.headPos := by
                dsimp [p]
                omega
              have hstep : (symStepConfig cfgsEnd r).tape (p - 1) = cfgsEnd.tape (p - 1) := by
                simp [symStepConfig, hne]
              rw [hstep]
              exact hnear.2.2 j hj
        · constructor
          · exact hst'A
          constructor
          · dsimp [symStepConfig]
            rw [hhead'A]
            omega
          · intro i hi j hj
            by_cases hip : i = p
            · subst i
              have hw : (symStepConfig cfgsEnd r).tape p = r.writeSym := by
                simp [symStepConfig, p]
              rw [hw]
              exact hwriteA j hj
            · have hne : i ≠ cfgsEnd.headPos := by
                intro hz
                apply hip
                dsimp [p]
                exact hz
              have hstep : (symStepConfig cfgsEnd r).tape i = cfgsEnd.tape i := by
                simp [symStepConfig, hne]
              rw [hstep]
              by_cases hip1 : i = p - 1
              · subst i
                dsimp [p]
                rw [htailP1A j hj]
                exact hnear.2.2 j hj
              · by_cases hilt : i < p - 1
                · have hz : 4 * i + j < 4 * p - 4 := by omega
                  unfold CBTMConfig.tapeAt
                  rw [htailBA (4 * i + j) (Or.inl hz)]
                  exact (by simpa [CBTMConfig.tapeAt] using hupto.2.2 i hi j hj)
                · have hz : 4 * p + 3 < 4 * i + j := by
                    have hgt : p + 1 ≤ i := by
                      dsimp [p] at hip hip1 hilt
                      omega
                    omega
                  unfold CBTMConfig.tapeAt
                  rw [htailBA (4 * i + j) (Or.inr hz)]
                  exact (by simpa [CBTMConfig.tapeAt] using hupto.2.2 i hi j hj)
        · intro z hz
          have hzout : 4 * p + 3 < z := by
            dsimp [p] at hpK
            omega
          rw [htailBA z (Or.inr hzout)]
          have ht0 := htail0 z hz
          have hchain : (initialConfig subsetSumCBTM (w ++ List.replicate (4 * πn.length) F4.zero)).tape z =
              (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape z := by
            have htape2 := initialTape_append_replicate_zero (w ++ List.replicate (4 * πn.length) F4.zero)
              (4 * (π.length - πn.length))
            have hrep : (w ++ List.replicate (4 * πn.length) F4.zero) ++
                List.replicate (4 * (π.length - πn.length)) F4.zero =
                w ++ List.replicate (4 * π.length) F4.zero := by
              rw [List.append_assoc, ← List.replicate_add]
              congr 1
              congr 2
              rw [hπall]
              simp [List.length_append]
              omega
            rw [hrep] at htape2
            exact congrFun htape2 z
          rw [ht0]
          exact hchain
        · intro πs₀' cfgm' hpre hne hh
          rcases isPrefix_append_singleton hpre with hpre_old | hfull
          · by_cases hEq : πs₀' = πs
            · subst πs₀'
              have hcfg : cfgm' = cfgsEnd := (symSteps_end_unique hsteps hh).symm
              rw [hcfg]
              dsimp [p] at hpK
              omega
            · exact hreach0 πs₀' cfgm' hpre_old hEq hh
          · exact (hne hfull).elim
        · intro i hge hil
          exact hzeroTailE i hge hil
      · -- 新块:p = wS.length:读格为新符号,扩展 wS
        have hpEq : cfgsEnd.headPos = ↑wS.length := by
          dsimp [p] at hpK
          have hle : cfgsEnd.headPos ≤ wS.length := hheadEnd
          omega
        have hdecB : ∃ sym' : Sym, symOf4F4 (cfgc0.tapeAt (4 * p)) (cfgc0.tapeAt (4 * p + 1))
            (cfgc0.tapeAt (4 * p + 2)) (cfgc0.tapeAt (4 * p + 3)) = some sym' := by
          exact decode_read_cells_of_no_trap hb (by simp [πb]) hph0b hq0 hqle0 hhp0 htrapb
        rcases hdecB with ⟨sym', hso'⟩
        have hcellsB : ∀ j : ℕ, j < 4 → cfgc0.tapeAt (4 * p + j) = (symTo4F4 sym').getD j F4.zero := by
          intro j hj
          have heq := cells_eq_of_symOf4F4 hso'
          rcases heq with ⟨h0, h1, h2, h3⟩
          interval_cases j
          · simpa using h0
          · simpa using h1
          · simpa using h2
          · simpa using h3
        rcases twelve_steps_good_block_upto (h := hb) (hlen := by simp [πb]) hph0b htrapb hnear
            (sym := sym') hcellsB hq0 hqle0 hhp0 with ⟨symB, rB, hblockB⟩
        have hbB_full : GoodBlockNear wExt cfgc0 πb cfg cfgsEnd p cfgsEnd.state symB rB := hblockB
        rcases hblockB with ⟨hpathB, hlenB, hstB, hpB, hcorrBB, hqleB, hbranchB, hvalidB,
          hstep4B, hmkB, hrB, hst'B, hhead'B, htailBB, htailSB, htailP1B, hwriteB, hsoB⟩
        have hsymB : symB = sym' := by
          exact symOf4F4_symTo4F4_getD_some sym' (by
            rw [← hcellsB 0 (by omega), ← hcellsB 1 (by omega), ← hcellsB 2 (by omega),
              ← hcellsB 3 (by omega)]
            simpa [p] using hsoB)
        have hrB' : rB ∈ VerifierSym.transition (cfgsEnd.state, sym') := by
          simpa [hsymB] using hrB
        have hlift : ∃ cfgsEndL : SymConfig,
            SymSteps VerifierSym.transition (symInitialConfig (wS ++ [sym'])) πs cfgsEndL ∧
            cfgsEndL.state = cfgsEnd.state ∧
            (∀ i : ℤ, i < wS.length → cfgsEndL.tape i = cfgsEnd.tape i) ∧
            cfgsEndL.headPos = cfgsEnd.headPos ∧ cfgsEndL.tape ↑wS.length = sym' := by
          exact symSteps_lift_extend (w := wS) (s := sym') hsteps hreach0
        rcases hlift with ⟨cfgsEndL, hstepsL, hsL, htL, hhpL, htapeL⟩
        let stepB : SymStep := { fromState := cfgsEnd.state, readSym := sym', result := rB }
        have hfromB : stepB.fromState = cfgsEndL.state := by
          dsimp [stepB]
          exact hsL.symm
        have hreadB : stepB.readSym = cfgsEndL.tape cfgsEndL.headPos := by
          dsimp [stepB]
          rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
          exact htapeL.symm
        have htransB : rB ∈ VerifierSym.transition (cfgsEndL.state, cfgsEndL.tape cfgsEndL.headPos) := by
          rw [hsL, hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
          rw [htapeL]
          rw [hsymB] at hrB
          exact hrB
        have hstepsB : SymSteps VerifierSym.transition (symInitialConfig (wS ++ [sym']))
            (πs ++ [stepB]) (symStepConfig cfgsEndL rB) := by
          exact SymSteps.cons πs stepB cfgsEndL hstepsL hfromB hreadB htransB
        have hlen_ext : 4 * wS.length + 4 ≤ (w ++ List.replicate (4 * π.length) F4.zero).length := by
          have hπs : wS.length ≤ πs.length := by
            have hhead : cfgsEnd.headPos ≤ πs.length := symSteps_length_ge_headPos hsteps
            omega
          rw [hπall]
          simp [List.length_append]
          omega
        have hchain : ∀ j : ℕ, (initialConfig subsetSumCBTM (w ++ List.replicate (4 * πn.length) F4.zero)).tape
              (4 * wS.length + j) =
            (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape
              (4 * wS.length + j) := by
          intro j
          have htape2 := initialTape_append_replicate_zero (w ++ List.replicate (4 * πn.length) F4.zero)
            (4 * (π.length - πn.length))
          have hrep : (w ++ List.replicate (4 * πn.length) F4.zero) ++
              List.replicate (4 * (π.length - πn.length)) F4.zero =
              w ++ List.replicate (4 * π.length) F4.zero := by
            rw [List.append_assoc, ← List.replicate_add]
            congr 1
            congr 2
            rw [hπall]
            simp [List.length_append]
            omega
          rw [hrep] at htape2
          exact congrFun htape2 (4 * wS.length + j)
        have hg : ∀ j : ℕ, (hj : j < 4) →
            (w ++ List.replicate (4 * π.length) F4.zero)[4 * wS.length + j]'(by omega) =
              (symTo4F4 sym')[j]'(by simpa [symTo4F4_length] using hj) := by
          intro j hj
          calc
            (w ++ List.replicate (4 * π.length) F4.zero)[4 * wS.length + j]'(by omega) =
                (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape
                  (4 * wS.length + j) := by
              have hcond : 0 ≤ (4 * wS.length + (j : ℤ)) ∧ (4 * wS.length + (j : ℤ)).toNat <
                  (w ++ List.replicate (4 * π.length) F4.zero).length := by
                constructor
                · omega
                · rw [show (4 * wS.length + (j : ℤ)).toNat = 4 * wS.length + j by omega]
                  simp at hlen_ext
                  simp
                  omega
              dsimp [initialConfig, initialTapeOf]
              split <;> rename_i hif
              · simp [show (4 * wS.length + (j : ℤ)).toNat = 4 * wS.length + j by omega]
              · exfalso
                exact hif hcond
            _ = cfgc0.tape (4 * wS.length + j) := by
              rw [← hchain j]
              exact (htail0 (4 * wS.length + j) (by omega)).symm
            _ = (symTo4F4 sym')[j] := by
              have hc := hcellsB j hj
              unfold CBTMConfig.tapeAt at hc
              rw [show 4 * p + (j : ℤ) = 4 * wS.length + (j : ℤ) by
                dsimp [p]
                rw [hpEq]] at hc
              simpa [symTo4F4_length, hj] using hc
        have hzeroTailNew : 4 * wS.length ≥ w.length → sym' = Sym.data0 false := by
          intro hge
          have hall : ∀ j : ℕ, j < 4 → (symTo4F4 sym').getD j F4.zero = F4.zero := by
            intro j hj
            have hc := hcellsB j hj
            unfold CBTMConfig.tapeAt at hc
            rw [show 4 * p + (j : ℤ) = 4 * wS.length + (j : ℤ) by
              dsimp [p]
              rw [hpEq]] at hc
            have hz : (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape
                (4 * wS.length + j) = F4.zero := by
              rw [← initialTape_append_replicate_zero w (4 * π.length)]
              dsimp [initialConfig, initialTapeOf]
              split <;> rename_i hif
              · exfalso
                omega
              · rfl
            rw [← hc]
            have ht1 : cfgc0.tape (4 * wS.length + j) =
                (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape
                (4 * wS.length + j) := by
              calc
                cfgc0.tape (4 * wS.length + j) =
                    (initialConfig subsetSumCBTM (w ++ List.replicate (4 * πn.length) F4.zero)).tape
                    (4 * wS.length + j) := htail0 (4 * wS.length + j) (by omega)
                _ = (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape
                    (4 * wS.length + j) := hchain j
            exact ht1.trans hz
          have hsym0 : symTo4F4 sym' = symTo4F4 (Sym.data0 false) := by
            apply List.ext_getElem?
            intro j
            by_cases hj4 : j < 4
            · have hs1 : (symTo4F4 sym')[j]? = some F4.zero := by
                rw [List.getElem?_eq_some_iff]
                refine ⟨by simpa [symTo4F4_length] using hj4, ?_⟩
                have hd : (symTo4F4 sym').getD j F4.zero = F4.zero := hall j hj4
                rw [List.getD_eq_getElem?_getD] at hd
                have hsome' : (symTo4F4 sym')[j]? =
                    some ((symTo4F4 sym')[j]'(by simpa [symTo4F4_length] using hj4)) := by
                  rw [List.getElem?_eq_some_iff]
                  exact ⟨by simpa [symTo4F4_length] using hj4, rfl⟩
                rw [hsome'] at hd
                simpa using hd
              have hs2 : (symTo4F4 (Sym.data0 false))[j]? = some F4.zero := by
                rw [List.getElem?_eq_some_iff]
                refine ⟨by simpa [symTo4F4_length] using hj4, ?_⟩
                dsimp [Sym.data0, symTo4F4, Sym.kindBits]
                interval_cases j <;> rfl
              rw [hs1, hs2]
            · rw [List.getElem?_eq_none (by simpa [symTo4F4_length] using hj4),
                List.getElem?_eq_none (by simpa [symTo4F4_length] using hj4)]
          exact symTo4F4_injective hsym0
        refine ⟨wS ++ [sym'], πs ++ [stepB], symStepConfig cfgsEndL rB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hπall]
          simp [List.length_append]
          nlinarith [hlenS]
        · rw [List.length_append, List.length_singleton]
          rw [show 4 * (wS.length + 1) = 4 * wS.length + 4 by omega]
          rw [List.take_add]
          have htakeS' : (w ++ List.replicate (4 * π.length) F4.zero).take (4 * wS.length) =
              (w ++ List.replicate (4 * πn.length) F4.zero).take (4 * wS.length) := by
            apply take_replicate_eq
            · have hlenT := congrArg List.length htakeS
              simp [flat4F4] at hlenT
              omega
            · have hlenT := congrArg List.length htakeS
              simp [flat4F4] at hlenT
              have hlenπ : 4 * πn.length ≤ 4 * π.length := by
                rw [hπall]
                simp [List.length_append]
              omega
          rw [htakeS']
          rw [htakeS]
          rw [show flat4F4 (wS ++ [sym']) = flat4F4 wS ++ symTo4F4 sym' by
            dsimp [flat4F4]
            rw [List.flatMap_append]
            simp]
          have h4 := take4_drop_eq hlen_ext hg
          rw [h4]
        · rw [hπall]
          exact GoodBlockPathNear_append wExt (initialConfig subsetSumCBTM wExt) cfgc0 cfg πn πb hgbp
            (GoodBlockPathNear.cons cfgc0 cfg cfg πb [] cfgsEnd p cfgsEnd.state symB rB hbB_full (GoodBlockPathNear.nil cfg))
        · exact hstepsB
        · dsimp [symStepConfig]
          exact symTransition_nextState_le101 cfgsEnd.state sym' rB hrB'
        · dsimp [symStepConfig]
          rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
          have hd : -1 ≤ (rB.moveDir).toInt ∧ (rB.moveDir).toInt ≤ 1 := by
            cases rB.moveDir <;> simp [Dir.toInt]
          simp
          omega
        · constructor
          · exact hst'B
          constructor
          · dsimp [symStepConfig]
            rw [hhead'B]
            rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
            omega
          · intro j hj
            rw [show (symStepConfig cfgsEndL rB).headPos = cfgsEndL.headPos + (rB.moveDir).toInt by
              simp [symStepConfig]]
            rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
            rcases hd_rB : rB.moveDir with _ | _ | _
            · have hAr : ↑wS.length + Dir.L.toInt - 1 = (wS.length : ℤ) - 2 := by
                simp [Dir.toInt]
                ring
              rw [hAr]
              have hz : 4 * ((wS.length : ℤ) - 2) + j < 4 * p - 4 := by
                dsimp [p]
                omega
              unfold CBTMConfig.tapeAt
              rw [htailBB (4 * ((wS.length : ℤ) - 2) + j) (Or.inl hz)]
              have hne : (wS.length : ℤ) - 2 ≠ cfgsEndL.headPos := by
                rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
                omega
              have hstep : (symStepConfig cfgsEndL rB).tape ((wS.length : ℤ) - 2) =
                  cfgsEndL.tape ((wS.length : ℤ) - 2) := by
                simp [symStepConfig, hne]
              rw [hstep]
              have ht : cfgsEndL.tape ((wS.length : ℤ) - 2) = cfgsEnd.tape ((wS.length : ℤ) - 2) := by
                exact htL ((wS.length : ℤ) - 2) (by omega)
              rw [ht]
              exact (by simpa [CBTMConfig.tapeAt] using hupto.2.2 ((wS.length : ℤ) - 2) (by omega) j hj)
            · have hAr : ↑wS.length + Dir.R.toInt - 1 = (wS.length : ℤ) := by
                simp [Dir.toInt]
              rw [hAr]
              have hwrite : (symStepConfig cfgsEndL rB).tape ↑wS.length = rB.writeSym := by
                simp [symStepConfig, hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
              rw [hwrite]
              unfold CBTMConfig.tapeAt
              exact (by simpa [CBTMConfig.tapeAt, hpEq] using hwriteB j hj)
            · have hAr : ↑wS.length + Dir.S.toInt - 1 = (wS.length : ℤ) - 1 := by
                simp [Dir.toInt]
              rw [hAr]
              have hz : 4 * ((wS.length : ℤ) - 1) + j < 4 * p := by
                dsimp [p]
                omega
              unfold CBTMConfig.tapeAt
              rw [htailSB hd_rB (4 * ((wS.length : ℤ) - 1) + j) (Or.inl hz)]
              have hne : (wS.length : ℤ) - 1 ≠ cfgsEndL.headPos := by
                rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
                omega
              have hstep : (symStepConfig cfgsEndL rB).tape ((wS.length : ℤ) - 1) =
                  cfgsEndL.tape ((wS.length : ℤ) - 1) := by
                simp [symStepConfig, hne]
              rw [hstep]
              have ht : cfgsEndL.tape ((wS.length : ℤ) - 1) = cfgsEnd.tape ((wS.length : ℤ) - 1) := by
                exact htL ((wS.length : ℤ) - 1) (by omega)
              rw [ht]
              exact (by simpa [p, hpEq, CBTMConfig.tapeAt] using hnear.2.2 j hj)
        · constructor
          · exact hst'B
          constructor
          · dsimp [symStepConfig]
            rw [hhead'B]
            rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
            omega
          · intro i hi j hj
            by_cases hip : i = p
            · subst i
              have hw : (symStepConfig cfgsEndL rB).tape p = rB.writeSym := by
                simp [symStepConfig, hhpL, p]
              rw [hw]
              exact hwriteB j hj
            · have hne : i ≠ cfgsEndL.headPos := by
                intro hz
                apply hip
                rw [hhpL] at hz
                dsimp [p]
                exact hz
              have hstep : (symStepConfig cfgsEndL rB).tape i = cfgsEndL.tape i := by
                simp [symStepConfig, hne]
              rw [hstep]
              by_cases hip1 : i = p - 1
              · subst i
                dsimp [p]
                rw [htailP1B j hj]
                have ht : cfgsEndL.tape (cfgsEnd.headPos - 1) = cfgsEnd.tape (cfgsEnd.headPos - 1) := by
                  exact htL (cfgsEnd.headPos - 1) (by omega)
                rw [ht]
                exact (by simpa [p, hpEq] using hnear.2.2 j hj)
              · have hilt : i < p - 1 := by
                  have hpu : p = ↑wS.length := by
                    dsimp [p]
                    exact hpEq
                  rw [hpu] at hip hip1 ⊢
                  have hi' : i < ↑wS.length + 1 := by
                    simpa using hi
                  have hle1 : i ≤ ↑wS.length - 1 := by omega
                  rcases lt_or_eq_of_le hle1 with hlt' | heq'
                  · exact hlt'
                  · exfalso
                    exact hip1 heq'
                have hz : 4 * i + j < 4 * p - 4 := by omega
                unfold CBTMConfig.tapeAt
                rw [htailBB (4 * i + j) (Or.inl hz)]
                have ht : cfgsEndL.tape i = cfgsEnd.tape i := by
                  exact htL i (by omega)
                rw [ht]
                exact (by simpa [CBTMConfig.tapeAt] using hupto.2.2 i (by omega) j hj)
        · intro z hz
          have hzout : 4 * p + 3 < z := by
            dsimp [p]
            rw [hpEq]
            have hz'' : (4 * ↑wS.length + 4 : ℤ) ≤ z := by
              simp at hz
              ring_nf
              ring_nf at hz
              exact hz
            exact (by
              have h1 : (4 * ↑wS.length + 3 : ℤ) < 4 * ↑wS.length + 4 := by omega
              exact lt_of_lt_of_le h1 hz'')
          rw [htailBB z (Or.inr hzout)]
          have ht0 := htail0 z (by omega)
          have hchain : (initialConfig subsetSumCBTM (w ++ List.replicate (4 * πn.length) F4.zero)).tape z =
              (initialConfig subsetSumCBTM (w ++ List.replicate (4 * π.length) F4.zero)).tape z := by
            have htape2 := initialTape_append_replicate_zero (w ++ List.replicate (4 * πn.length) F4.zero)
              (4 * (π.length - πn.length))
            have hrep : (w ++ List.replicate (4 * πn.length) F4.zero) ++
                List.replicate (4 * (π.length - πn.length)) F4.zero =
                w ++ List.replicate (4 * π.length) F4.zero := by
              rw [List.append_assoc, ← List.replicate_add]
              congr 1
              congr 2
              rw [hπall]
              simp [List.length_append]
              omega
            rw [hrep] at htape2
            exact congrFun htape2 z
          rw [ht0]
          exact hchain
        · intro πs₀' cfgm' hpre hne hh
          rcases isPrefix_append_singleton hpre with hpre_old | hfull
          · by_cases hEq : πs₀' = πs
            · subst πs₀'
              have hcfg : cfgsEndL = cfgm' := symSteps_end_unique hstepsL hh
              rw [← hcfg]
              rw [hhpL, show cfgsEnd.headPos = ↑wS.length by exact_mod_cast hpEq]
              simp
            · rcases symSteps_restrict' (πs := πs₀') (πsFull := πs) hpre_old hh hreach0 with
                ⟨cfgm₀, hh₀, hs₀', hp₀', ht₀'⟩
              have hlt : cfgm₀.headPos < wS.length := hreach0 πs₀' cfgm₀ hpre_old hEq hh₀
              rw [← hp₀']
              exact (by
                have h1 : (wS.length : ℤ) < (wS ++ [sym']).length := by
                  simp
                exact lt_trans hlt h1)
          · exact (hne hfull).elim
        · intro i hge hil
          by_cases hi : i < wS.length
          · have hget : wS.getD i Sym.blank = (wS ++ [sym']).getD i Sym.blank := by
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by simpa using hi)]
            rw [← hget]
            exact hzeroTailE i hge hi
          · have hi' : i = wS.length := by
              simp at hil
              omega
            rw [hi']
            rw [hi'] at hge
            simp
            exact hzeroTailNew hge
  -- ============================================================
  -- 收尾:应用 hmain 于主定理实例,转主定理结论
  -- ============================================================
  rcases hmain π cfgE rfl hE hph0 htrapE with
    ⟨wS, πs, cfgsEnd, hlenS, htakeS, hgbp, hsteps, hqEnd, hheadEnd, hnear, hupto, htail0,
      hreach0, hzeroTailE⟩
  have hq100 : cfgsEnd.state = VerifierSym.qAccept := by
    rcases Finset.mem_image.mp haccE with ⟨reg, hreg, hacc'⟩
    simp [Finset.mem_range] at hreg
    have hstE : cfgE.state = encodeState VerifierSym.qAccept 0 reg := hacc'.symm
    have hqE : (decodeState cfgE.state).1 = VerifierSym.qAccept := by
      rw [hstE]
      exact decodeState_encodeState_q_eq VerifierSym.qAccept 0 reg (by
        dsimp [stepsPerSym, regBound]
        nlinarith)
    have hqS : (decodeState cfgE.state).1 = cfgsEnd.state := by
      rw [hnear.1]
      exact decodeState_encodeState_q_eq cfgsEnd.state 0 0 (by
        dsimp [stepsPerSym, regBound]
        norm_num)
    exact hqS.symm.trans hqE
  have htakeW : w.take (4 * wS.length) = (flat4F4 wS).take w.length := by
    rw [← htakeS]
    rw [← take_w_take_append (w := w) (r := List.replicate (4 * π.length) F4.zero) (n := 4 * wS.length)]
  have hnearW : blockCorrespondNear cfg cfgsEnd (cfgsEnd.headPos) := by
    dsimp [blockCorrespondNear] at hnear ⊢
    rcases hnear with ⟨hst, hhp, htape⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hsE]; exact hst
    · rw [← hpE]; exact hhp
    · intro j hj
      rw [CBTMConfig.tapeAt]
      rw [← htE]
      simpa [CBTMConfig.tapeAt] using htape j hj
  have huptoW : blockCorrespondUpto cfg cfgsEnd wS.length := by
    dsimp [blockCorrespondUpto] at hupto ⊢
    rcases hupto with ⟨hst, hhp, htape⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hsE]; exact hst
    · rw [← hpE]; exact hhp
    · intro i hi j hj
      rw [CBTMConfig.tapeAt]
      rw [← htE]
      simpa [CBTMConfig.tapeAt] using htape i hi j hj
  have htailW : ∀ z : ℤ, 4 * wS.length ≤ z → cfg.tape z =
      (initialConfig subsetSumCBTM w).tape z := by
    intro z hz
    rw [← htE]
    rw [htape]
    exact htail0 z hz
  have hzeroTail : ∀ i : ℕ, 4 * i ≥ w.length → i < wS.length → wS.getD i Sym.blank = Sym.data0 false := by
    intro i hge hil
    exact hzeroTailE i hge hil
  exact ⟨wS, πs, cfgsEnd, htakeW, hsteps, (by simpa [VerifierSym.qAccept] using hq100), hreach0,
    hzeroTail, hlenS, hheadEnd, hnearW, huptoW, htailW⟩






end SymToF4

end Mp

