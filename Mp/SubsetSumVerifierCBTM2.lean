/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierCBTM

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



namespace Mp
open CBTM
namespace SymToF4

/-- 陷阱态 101 吸收（Sym 层单步）：状态 101 读任意符号的转移 nextState 恒 101。 -/
lemma symTransition_absorb_101 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (101, s)) : r.nextState = 101 := by
  have hb : ∀ s : Sym, ∀ r' : SymTransResult,
      r' ∈ VerifierSym.transition (101, s) → r'.nextState = 101 := by
    native_decide
  exact hb s r hr

/-- 状态 101 的路径吸收：起点状态 101 的 Sym 路径终点状态恒 101。 -/
lemma symSteps_state101_absorb {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) (h0 : cfg₀.state = 101) :
    cfg.state = 101 := by
  induction h with
  | nil => exact h0
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hst1 : cfg₁.state = 101 := ih
      have htr' : step.result ∈ VerifierSym.transition (101, step.readSym) := by
        rw [hread]
        simpa [hfrom, hst1] using htrans
      have hns : step.result.nextState = 101 := symTransition_absorb_101 step.readSym step.result htr'
      simpa [symStepConfig, hns]

/-- 路径二分：要么每一步的 nextState ≠ 101，要么终点状态 = 101。 -/
lemma symSteps_no_101_or_end {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) :
    (∀ step ∈ π, step.result.nextState ≠ 101) ∨ cfg.state = 101 := by
  induction h with
  | nil =>
      left
      intro step hstep
      simp at hstep
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      cases ih with
      | inl h₁ =>
          by_cases h101 : step.result.nextState = 101
          · right
            simpa [symStepConfig, h101]
          · left
            intro st hstm
            rw [List.mem_append] at hstm
            rcases hstm with hpre | hlast
            · exact h₁ st hpre
            · rw [List.mem_singleton] at hlast
              subst st
              exact h101
      | inr h₁ =>
          right
          have htr' : step.result ∈ VerifierSym.transition (101, step.readSym) := by
            rw [hread]
            simpa [hfrom, h₁] using htrans
          have hns : step.result.nextState = 101 := symTransition_absorb_101 step.readSym step.result htr'
          simpa [symStepConfig, hns]

/-- 接受路径（终点 qAccept = 100）上无 101 步：每一步的 nextState ≠ 101。 -/
lemma symSteps_accept_no_101 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hacc : cfg.state = VerifierSym.qAccept) :
    ∀ step ∈ π, step.result.nextState ≠ 101 := by
  rcases symSteps_no_101_or_end h with h₁ | h₂
  · exact h₁
  · exfalso
    rw [hacc] at h₂
    norm_num [VerifierSym.qAccept] at h₂

set_option maxHeartbeats 800000 in
/-- 一个 Sym 步展开成 12 个 CBTM 步（磁带语义中段路径）。
    v2：删除 hvalid_sym/hvalid_r 前提（往返引理对任意符号成立，见 symOf4F4_symTo4F4_all）。
    v3：加前提 r.nextState < 101（接受路径上无 101 步——陷阱态 101 吸收后无法到达 qAccept=100，
        见 symSteps_accept_no_101；该前提用于排除 transition4 移动阶段的 q=101 陷阱吸收分支）。 -/
theorem expand_sym_step (q : ℕ) (sym : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, sym)) (hqle : q ≤ 101)
    (hbranch : Sym.isBranch sym → q = 2) (hrs : r.nextState < 101)
    (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (hcorr : blockCorrespond cfgc cfgs)
    (hst : cfgc.state = encodeState q 0 0)
    (hp : cfgc.headPos = 4 * p)
    (hread : cfgs.tape p = sym) :
    ∃ πb : ComputationPath, ∃ cfgc' : CBTMConfig subsetSumCBTM w,
      TapeSteps subsetSumCBTM w cfgc πb cfgc' ∧
      πb.length = 12 ∧
      blockCorrespond cfgc' (symStepConfig cfgs r) ∧
      ((πb.getD 3 (TransitionStep.mk (encodeState r.nextState 4 (encodeResult r))
        ((symTo4F4 r.writeSym).getLastD F4.zero)
        (CBTMTransResult.mk (encodeState r.nextState 4 (encodeResult r))
          ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L))).result) = CBTMTransResult.mk
        (encodeState r.nextState 4 (encodeResult r)) ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L := by
  let R := Dir.R; let L := Dir.L; let S := Dir.S
  let cells := symTo4F4 sym
  let c0 := cells.getD 0 F4.zero
  let c1 := cells.getD 1 F4.zero
  let c2 := cells.getD 2 F4.zero
  let c3 := cells.getD 3 F4.zero
  let nrs := symTo4F4 r.writeSym
  let w0 := nrs.getD 0 F4.zero
  let w1 := nrs.getD 1 F4.zero
  let w2 := nrs.getD 2 F4.zero
  let w3 := nrs.getD 3 F4.zero
  let d := r.moveDir
  let qn := min r.nextState 101
  let b01 := bufOf3 c0 F4.zero F4.zero
  let b12 := bufOf3 c0 c1 F4.zero
  let b3 := bufOf3 c0 c1 c2
  let regr := encodeResult r
  let tprev := symTo4F4 (cfgs.tape (p - 1))
  let s8 := w0
  let s9 := match d with | Dir.R => w1 | Dir.L => tprev.getD 3 F4.zero | Dir.S => w0
  let s10 := match d with | Dir.R => w2 | Dir.L => tprev.getD 2 F4.zero | Dir.S => w0
  let s11 := match d with | Dir.R => w3 | Dir.L => tprev.getD 1 F4.zero | Dir.S => w0
  let st0 : TransitionStep := ⟨encodeState q 0 0, c0,
    CBTMTransResult.mk (encodeState (min q 101) 1 b01) c0 Dir.R⟩
  let st1 : TransitionStep := ⟨encodeState (min q 101) 1 b01, c1,
    CBTMTransResult.mk (encodeState (min q 101) 2 b12) c1 Dir.R⟩
  let st2 : TransitionStep := ⟨encodeState (min q 101) 2 b12, c2,
    CBTMTransResult.mk (encodeState (min q 101) 3 b3) c2 Dir.R⟩
  let st3 : TransitionStep := ⟨encodeState (min q 101) 3 b3, c3,
    CBTMTransResult.mk (encodeState r.nextState 4 regr) w3 Dir.L⟩
  let st4 : TransitionStep := ⟨encodeState r.nextState 4 regr, c2,
    CBTMTransResult.mk (encodeState qn 5 regr) w2 Dir.L⟩
  let st5 : TransitionStep := ⟨encodeState qn 5 regr, c1,
    CBTMTransResult.mk (encodeState qn 6 regr) w1 Dir.L⟩
  let st6 : TransitionStep := ⟨encodeState qn 6 regr, c0,
    CBTMTransResult.mk (encodeState qn 7 regr) w0 Dir.S⟩
  let st7 : TransitionStep := ⟨encodeState qn 7 regr, w0,
    CBTMTransResult.mk (encodeState qn 8 regr) w0 Dir.S⟩
  let st8 : TransitionStep := ⟨encodeState qn 8 regr, s8,
    CBTMTransResult.mk (encodeState qn 9 regr) s8 d⟩
  let st9 : TransitionStep := ⟨encodeState qn 9 regr, s9,
    CBTMTransResult.mk (encodeState qn 10 regr) s9 d⟩
  let st10 : TransitionStep := ⟨encodeState qn 10 regr, s10,
    CBTMTransResult.mk (encodeState qn 11 regr) s10 d⟩
  let st11 : TransitionStep := ⟨encodeState qn 11 regr, s11,
    CBTMTransResult.mk (encodeState qn 0 0) s11 d⟩
  let cfg1 := stepConfig cfgc st0.result
  let cfg2 := stepConfig cfg1 st1.result
  let cfg3 := stepConfig cfg2 st2.result
  let cfg4 := stepConfig cfg3 st3.result
  let cfg5 := stepConfig cfg4 st4.result
  let cfg6 := stepConfig cfg5 st5.result
  let cfg7 := stepConfig cfg6 st6.result
  let cfg8 := stepConfig cfg7 st7.result
  let cfg9 := stepConfig cfg8 st8.result
  let cfg10 := stepConfig cfg9 st9.result
  let cfg11 := stepConfig cfg10 st10.result
  let cfgAfter := stepConfig cfg11 st11.result
  -- 状态往返与转移事实
  have hns : r.nextState ≤ 101 := transition_nextState_le101 q sym hqle r hr
  have hdec0 : decodeState (encodeState q 0 0) = (q, 0, 0) := by
    apply decodeState_encodeState
    · norm_num
    · norm_num
  have hdec0' : decodeState (encodeState (min q 101) 1 b01) = (min q 101, 1, b01) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b01 ≤ 63 := by
        dsimp [b01, bufOf3]
        rcases sym with ⟨sk, mk⟩
        rcases c0 with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec1' : decodeState (encodeState (min q 101) 2 b12) = (min q 101, 2, b12) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b12 ≤ 63 := by
        dsimp [b12, bufOf3]
        rcases sym with ⟨sk, mk⟩
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec2' : decodeState (encodeState (min q 101) 3 b3) = (min q 101, 3, b3) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b3 ≤ 63 := by
        dsimp [b3, bufOf3]
        rcases sym with ⟨sk, mk⟩
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
          simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hreg : regr < 8192 := by
    dsimp [regr, encodeResult]
    have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
      rcases r.writeSym with ⟨k, mk⟩
      cases k <;> cases mk <;> simp [skOf]
    have hdir : dirOf r.moveDir < 3 := by
      cases r.moveDir <;> simp [dirOf]
    omega
  have hdec3' : decodeState (encodeState r.nextState 4 regr) = (r.nextState, 4, regr) := by
    apply decodeState_encodeState
    · norm_num
    · exact hreg
  have hdec4' : decodeState (encodeState qn 5 regr) = (qn, 5, regr) := by
    apply decodeState_encodeState
    · norm_num
    · exact hreg
  have hdecph (ph : ℕ) (hphl : ph < 12) :
      decodeState (encodeState qn ph regr) = (qn, ph, regr) := by
    apply decodeState_encodeState
    · simpa [stepsPerSym] using hphl
    · exact hreg
  -- 虚部事实
  have him_c0 : F4.im c0 = false := by
    dsimp [c0, cells, F4.im]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨0, by rw [symTo4F4_length]; norm_num⟩]
    exact (symTo4F4_im_false_012 sym).1
  have him_c1 : F4.im c1 = false := by
    dsimp [c1, cells, F4.im]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨1, by rw [symTo4F4_length]; norm_num⟩]
    exact (symTo4F4_im_false_012 sym).2.1
  have him_c2 : F4.im c2 = false := by
    dsimp [c2, cells, F4.im]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨2, by rw [symTo4F4_length]; norm_num⟩]
    exact (symTo4F4_im_false_012 sym).2.2
  have him_c3 : F4.im c3 = Sym.isBranch sym := by
    dsimp [c3, cells]
    rcases sym with ⟨sk, mk⟩
    cases sk <;> simp [symTo4F4, Sym.kindBits, Sym.isBranch, SymKind.isBranch, F4.im]
  have him_w0 : F4.im w0 = false := by
    dsimp [w0, nrs, F4.im]
    rw [List.getD_eq_get (symTo4F4 r.writeSym) F4.zero ⟨0, by rw [symTo4F4_length]; norm_num⟩]
    exact (symTo4F4_im_false_012 r.writeSym).1
  -- symTo4F4/symOf4F4 往返与 encodeResult/decodeResult 往返
  have hsymOf : symOf4F4 c0 c1 c2 c3 = some sym := by
    dsimp [cells, c0, c1, c2, c3]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨0, by rw [symTo4F4_length]; norm_num⟩]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨1, by rw [symTo4F4_length]; norm_num⟩]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨2, by rw [symTo4F4_length]; norm_num⟩]
    rw [List.getD_eq_get (symTo4F4 sym) F4.zero ⟨3, by rw [symTo4F4_length]; norm_num⟩]
    have h := symOf4F4_symTo4F4_all sym
    rcases sym with ⟨sk, mk⟩
    cases sk <;> simp [symTo4F4, Sym.kindBits] at h ⊢
    all_goals exact h
  have hdecRes : decodeResult regr = r := decodeResult_encodeResult_all r
  have hdmatch : (SymToF4.dirOf.match_1 (fun _ : Dir => Dir) r.moveDir (fun _ => Dir.R) (fun _ => Dir.L) (fun _ => Dir.S)) = r.moveDir := by
    cases r.moveDir <;> rfl
  -- 缓冲增量恒等式
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
  have hqnn : min qn 101 = qn := by
    dsimp [qn]
    exact Nat.min_eq_left (Nat.min_le_right r.nextState 101)
  -- 12 个转移步的合法性
  have htr0 : (st0 : TransitionStep).result ∈ transition4 (st0 : TransitionStep).fromState c0 := by
    dsimp [st0, transition4]
    rw [hdec0]
    dsimp
    rw [him_c0]
    dsimp
    rw [hb01]
    simp [Finset.mem_singleton]
  have htr1 : (st1 : TransitionStep).result ∈ transition4 (st1 : TransitionStep).fromState c1 := by
    dsimp [st1, transition4]
    rw [hdec0']
    dsimp
    rw [him_c1]
    dsimp
    rw [hb12]
    simp [Finset.mem_singleton]
  have htr2 : (st2 : TransitionStep).result ∈ transition4 (st2 : TransitionStep).fromState c2 := by
    dsimp [st2, transition4]
    rw [hdec1']
    dsimp
    rw [him_c2]
    dsimp
    rw [hb3]
    simp [Finset.mem_singleton]
  have htr3 : (st3 : TransitionStep).result ∈ transition4 (st3 : TransitionStep).fromState c3 := by
    dsimp [st3, transition4]
    rw [hdec2']
    dsimp
    have hfab : f4ofBuf b3 = (c0, c1, c2) := f4ofBuf_bufOf3 c0 c1 c2
    rw [hfab]
    dsimp
    rw [hsymOf]
    dsimp
    cases h : F4.im c3 with
    | true =>
        dsimp
        have hbr : Sym.isBranch sym = true := by
          simpa [him_c3] using h
        have hq2 : q = 2 := hbranch hbr
        have hqs : min (min q 101) 101 = 2 := by omega
        rw [hqs]
        by_cases hβ : sym.1 = SymKind.beta
        · -- β:转移表已改陷阱,与 hrs(r.nextState < 101)矛盾
          exfalso
          have htb' : VerifierSym.transition (q, sym) = {SymTransResult.mk 101 sym Dir.S} := by
            rw [hq2]
            rcases sym with ⟨k, mk⟩
            have hk : k = SymKind.beta := by simpa using hβ
            subst k
            cases mk <;> rw [VerifierSym.transition, if_pos (by decide : 2 ∈ VerifierSym.legalStates)] <;> decide
          have hr' : r = SymTransResult.mk 101 sym Dir.S := by
            simpa [htb', Finset.mem_singleton] using hr
          have hns : r.nextState = 101 := by
            rw [hr']
          omega
        · -- α:re₁ = false → c0 = F4.zero,块判别走 sel/nosel
          have hα : sym.1 = SymKind.alpha := by
            rcases sym with ⟨k, mk⟩
            have hk : k = SymKind.alpha ∨ k = SymKind.beta := by
              simpa [Sym.isBranch, SymKind.isBranch] using hbr
            rcases hk with hkα | hkβ
            · simpa using hkα
            · exfalso
              exact hβ (by simpa using hkβ)
          by_cases hm : sym.2
          · -- 带标记 α:表给 101,与 hrs(r.nextState < 101)矛盾
            exfalso
            have htb' : VerifierSym.transition (q, sym) = {SymTransResult.mk 101 sym Dir.S} := by
              rw [hq2]
              rcases sym with ⟨k, mk⟩
              have hk : k = SymKind.alpha := by simpa using hα
              subst k
              have hmk : mk = true := by simpa using hm
              subst mk
              rw [VerifierSym.transition, if_pos (by decide : 2 ∈ VerifierSym.legalStates)]
            have hr' : r = SymTransResult.mk 101 sym Dir.S := by
              simpa [htb', Finset.mem_singleton] using hr
            have hns : r.nextState = 101 := by rw [hr']
            omega
          · -- 无标记 α
            have hm' : sym.2 = false := by
              cases h : sym.2 <;> simp [h] at hm ⊢
            have hc0 : c0 = F4.zero := by
              dsimp [c0, cells]
              rcases sym with ⟨k, mk⟩
              have hk : k = SymKind.alpha := by simpa using hα
              subst k
              cases mk <;> simp [symTo4F4, Sym.kindBits, F4.zero]
            have htrans : r = SymTransResult.mk 2 Sym.sel Dir.R ∨ r = SymTransResult.mk 2 Sym.nosel Dir.R := by
              have htb : VerifierSym.transition (q, sym) = {SymTransResult.mk 2 Sym.sel Dir.R,
                  SymTransResult.mk 2 Sym.nosel Dir.R} := by
                rw [hq2]
                exact transition2_branch_eq sym hα hm'
              simpa [htb, Finset.mem_insert, Finset.mem_singleton] using hr
            rcases htrans with hsel | hnosel
            · simp [List.getD, st3, regr, w3, nrs, hfab, hc0]
              rw [hsel]
              have hc3re : F4.re c3 = false := by
                dsimp [c3, cells, F4.re]
                rw [symTo4F4_getD3_eq_lastD sym]
                simp [symTo4F4, Sym.isBranch, SymKind.isBranch, hm']
              simp [hc3re, Finset.mem_insert, Finset.mem_singleton]
              left
              simp [symTo4F4, Sym.sel, Sym.kindBits, F4.zero]
            · simp [List.getD, st3, regr, w3, nrs, hfab, hc0]
              rw [hnosel]
              have hc3re : F4.re c3 = false := by
                dsimp [c3, cells, F4.re]
                rw [symTo4F4_getD3_eq_lastD sym]
                simp [symTo4F4, Sym.isBranch, SymKind.isBranch, hm']
              simp [hc3re, Finset.mem_insert, Finset.mem_singleton]
              right; rfl
    | false =>
        dsimp
        have hqmin2 : min (min q 101) 101 = q := by
          rw [Nat.min_eq_left hqle, Nat.min_eq_left hqle]
        rw [hqmin2]
        refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
        dsimp [regr, w3, nrs]
        rw [symTo4F4_getD3_eq_lastD r.writeSym]
  have htr4 : (st4 : TransitionStep).result ∈ transition4 (st4 : TransitionStep).fromState c2 := by
    dsimp [st4, transition4]
    rw [hdec3']
    dsimp
    rw [him_c2, hdecRes]
    simp [qn, w2, nrs, Finset.mem_singleton]
  have htr5 : (st5 : TransitionStep).result ∈ transition4 (st5 : TransitionStep).fromState c1 := by
    dsimp [st5, transition4]
    rw [hdecph 5 (by norm_num)]
    dsimp
    rw [him_c1, hdecRes]
    simp [qn, hqnn, w1, nrs, Finset.mem_singleton]
  have htr6 : (st6 : TransitionStep).result ∈ transition4 (st6 : TransitionStep).fromState c0 := by
    dsimp [st6, transition4]
    rw [hdecph 6 (by norm_num)]
    dsimp
    rw [him_c0, hdecRes]
    simp [qn, hqnn, w0, nrs, Finset.mem_singleton]
  have htr7 : (st7 : TransitionStep).result ∈ transition4 (st7 : TransitionStep).fromState w0 := by
    dsimp [st7, transition4]
    rw [hdecph 7 (by norm_num)]
    dsimp
    rw [him_w0]
    simp [qn, hqnn, Finset.mem_singleton]
  have htr8 : (st8 : TransitionStep).result ∈ transition4 (st8 : TransitionStep).fromState s8 := by
    dsimp [st8, transition4]
    rw [hdecph 8 (by norm_num)]
    dsimp
    rw [hdecRes, hdmatch]
    cases h : F4.im s8 with
    | true =>
        simp [qn, d, Finset.mem_insert, Finset.mem_singleton]
    | false =>
        have hnot101 : ¬ 101 ≤ r.nextState := by omega
        simp [qn, d, Finset.mem_singleton, hnot101]
  have htr9 : (st9 : TransitionStep).result ∈ transition4 (st9 : TransitionStep).fromState s9 := by
    dsimp [st9, transition4]
    rw [hdecph 9 (by norm_num)]
    dsimp
    rw [hdecRes, hdmatch]
    cases h : F4.im s9 with
    | true =>
        simp [qn, d, Finset.mem_insert, Finset.mem_singleton]
    | false =>
        have hnot101 : ¬ 101 ≤ r.nextState := by omega
        simp [qn, d, Finset.mem_singleton, hnot101]
  have htr10 : (st10 : TransitionStep).result ∈ transition4 (st10 : TransitionStep).fromState s10 := by
    dsimp [st10, transition4]
    rw [hdecph 10 (by norm_num)]
    dsimp
    rw [hdecRes, hdmatch]
    cases h : F4.im s10 with
    | true =>
        simp [qn, d, Finset.mem_insert, Finset.mem_singleton]
    | false =>
        have hnot101 : ¬ 101 ≤ r.nextState := by omega
        simp [qn, d, Finset.mem_singleton, hnot101]
  have htr11 : (st11 : TransitionStep).result ∈ transition4 (st11 : TransitionStep).fromState s11 := by
    dsimp [st11, transition4]
    rw [hdecph 11 (by norm_num)]
    dsimp
    rw [hdecRes, hdmatch]
    cases h : F4.im s11 with
    | true =>
        have hqnne : qn ≠ 101 := by dsimp [qn]; omega
        simp [qn, d, hqnne, Finset.mem_insert, Finset.mem_singleton]
    | false =>
        have hnot101 : ¬ 101 ≤ r.nextState := by omega
        simp [qn, d, Finset.mem_singleton, hnot101]
  -- 带头位置序列
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    dsimp [cfg1, stepConfig, st0]
    rw [hp]
    simp [Dir.toInt]
  have hp2 : cfg2.headPos = 4 * p + 2 := by
    dsimp [cfg2, stepConfig, st1]
    rw [hp1]
    norm_num [Dir.toInt] <;> ring
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    dsimp [cfg3, stepConfig, st2]
    rw [hp2]
    norm_num [Dir.toInt] <;> ring
  have hp4 : cfg4.headPos = 4 * p + 2 := by
    dsimp [cfg4, stepConfig, st3]
    rw [hp3]
    norm_num [Dir.toInt] <;> ring
  have hp5 : cfg5.headPos = 4 * p + 1 := by
    dsimp [cfg5, stepConfig, st4]
    rw [hp4]
    norm_num [Dir.toInt] <;> ring
  have hp6 : cfg6.headPos = 4 * p := by
    dsimp [cfg6, stepConfig, st5]
    rw [hp5]
    norm_num [Dir.toInt] <;> ring
  have hp7 : cfg7.headPos = 4 * p := by
    dsimp [cfg7, stepConfig, st6]
    rw [hp6]
    simp [Dir.toInt]
  have hp8 : cfg8.headPos = 4 * p := by
    dsimp [cfg8, stepConfig, st7]
    rw [hp7]
    simp [Dir.toInt]
  have hp9 : cfg9.headPos = 4 * p + d.toInt := by
    dsimp [cfg9, stepConfig, st8]
    rw [hp8]
  have hp10 : cfg10.headPos = 4 * p + d.toInt + d.toInt := by
    dsimp [cfg10, stepConfig, st9]
    rw [hp9]
  have hp11 : cfg11.headPos = 4 * p + d.toInt + d.toInt + d.toInt := by
    dsimp [cfg11, stepConfig, st10]
    rw [hp10]
  -- 每步读到的符号
  have hread0 : cfgc.tapeAt cfgc.headPos = c0 := by
    rw [hp]
    have hc := hcorr.2.2 p 0 (by norm_num)
    dsimp [c0, cells]
    simpa [hread] using hc
  have hread1 : cfg1.tapeAt cfg1.headPos = c1 := by
    rw [hp1]
    dsimp [cfg1]
    rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result (4 * p + 1) (by rw [hp]; omega)]
    have hc := hcorr.2.2 p 1 (by norm_num)
    dsimp [c1, cells]
    simpa [hread] using hc
  have hread2 : cfg2.tapeAt cfg2.headPos = c2 := by
    rw [hp2]
    dsimp [cfg2]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result (4 * p + 2) (by rw [hp1]; omega)]
    dsimp [cfg1]
    rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result (4 * p + 2) (by rw [hp]; omega)]
    have hc := hcorr.2.2 p 2 (by norm_num)
    dsimp [c2, cells]
    simpa [hread] using hc
  have hread3 : cfg3.tapeAt cfg3.headPos = c3 := by
    rw [hp3]
    dsimp [cfg3]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result (4 * p + 3) (by rw [hp2]; omega)]
    dsimp [cfg2]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result (4 * p + 3) (by rw [hp1]; omega)]
    dsimp [cfg1]
    rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result (4 * p + 3) (by rw [hp]; omega)]
    have hc := hcorr.2.2 p 3 (by norm_num)
    dsimp [c3, cells]
    simpa [hread] using hc
  have hread4 : cfg4.tapeAt cfg4.headPos = c2 := by
    rw [hp4]
    dsimp [cfg4]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result (4 * p + 2) (by rw [hp3]; omega)]
    dsimp [cfg3]
    rw [stepConfig_tapeAt_eq_of_eq cfg2 st2.result (4 * p + 2) (by rw [hp2])]
  have hread5 : cfg5.tapeAt cfg5.headPos = c1 := by
    rw [hp5]
    dsimp [cfg5]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p + 1) (by rw [hp4]; omega)]
    dsimp [cfg4]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result (4 * p + 1) (by rw [hp3]; omega)]
    dsimp [cfg3]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result (4 * p + 1) (by rw [hp2]; omega)]
    dsimp [cfg2]
    rw [stepConfig_tapeAt_eq_of_eq cfg1 st1.result (4 * p + 1) (by rw [hp1])]
  have hread6 : cfg6.tapeAt cfg6.headPos = c0 := by
    rw [hp6]
    dsimp [cfg6]
    rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p) (by rw [hp5]; omega)]
    dsimp [cfg5]
    rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p) (by rw [hp4]; omega)]
    dsimp [cfg4]
    rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result (4 * p) (by rw [hp3]; omega)]
    dsimp [cfg3]
    rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result (4 * p) (by rw [hp2]; omega)]
    dsimp [cfg2]
    rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result (4 * p) (by rw [hp1]; omega)]
    dsimp [cfg1]
    rw [stepConfig_tapeAt_eq_of_eq cfgc st0.result (4 * p) (by rw [hp])]
  have hread7 : cfg7.tapeAt cfg7.headPos = w0 := by
    rw [hp7]
    dsimp [cfg7]
    rw [stepConfig_tapeAt_eq_of_eq cfg6 st6.result (4 * p) (by rw [hp6])]
  have hread8 : cfg8.tapeAt cfg8.headPos = w0 := by
    rw [hp8]
    dsimp [cfg8]
    rw [stepConfig_tapeAt_eq_of_eq cfg7 st7.result (4 * p) (by rw [hp7])]
  have hread9 : cfg9.tapeAt cfg9.headPos = s9 := by
    rw [hp9]
    rcases hd : r.moveDir with _ | _ | _
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.L.toInt = 4 * p - 1 by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p - 1) (by rw [hp8]; omega)]
      dsimp [cfg8]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p - 1) (by rw [hp7]; omega)]
      dsimp [cfg7]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p - 1) (by rw [hp6]; omega)]
      dsimp [cfg6]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p - 1) (by rw [hp5]; omega)]
      dsimp [cfg5]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p - 1) (by rw [hp4]; omega)]
      dsimp [cfg4]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result (4 * p - 1) (by rw [hp3]; omega)]
      dsimp [cfg3]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result (4 * p - 1) (by rw [hp2]; omega)]
      dsimp [cfg2]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result (4 * p - 1) (by rw [hp1]; omega)]
      dsimp [cfg1]
      rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result (4 * p - 1) (by rw [hp]; omega)]
      simp [s9, d, hd]
      have hc := hcorr.2.2 (p - 1) 3 (by norm_num)
      simpa [tprev, show 4 * (p - 1) + 3 = 4 * p - 1 by ring] using hc
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.R.toInt = 4 * p + 1 by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 1) (by rw [hp8]; omega)]
      dsimp [cfg8]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 1) (by rw [hp7]; omega)]
      dsimp [cfg7]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 1) (by rw [hp6]; omega)]
      dsimp [cfg6]
      rw [stepConfig_tapeAt_eq_of_eq cfg5 st5.result (4 * p + 1) (by rw [hp5])]
      simp [st5, s9, d, hd]
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.S.toInt = 4 * p by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_eq cfg8 st8.result (4 * p) (by rw [hp8])]
      simp [st8, s8, s9, d, hd]
  have hread10 : cfg10.tapeAt cfg10.headPos = s10 := by
    rw [hp10]
    rcases hd : r.moveDir with _ | _ | _
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.L.toInt + Dir.L.toInt = 4 * p - 2 by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg10]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p - 2) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p - 2) (by rw [hp8]; omega)]
      dsimp [cfg8]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p - 2) (by rw [hp7]; omega)]
      dsimp [cfg7]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p - 2) (by rw [hp6]; omega)]
      dsimp [cfg6]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p - 2) (by rw [hp5]; omega)]
      dsimp [cfg5]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p - 2) (by rw [hp4]; omega)]
      dsimp [cfg4]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result (4 * p - 2) (by rw [hp3]; omega)]
      dsimp [cfg3]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result (4 * p - 2) (by rw [hp2]; omega)]
      dsimp [cfg2]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result (4 * p - 2) (by rw [hp1]; omega)]
      dsimp [cfg1]
      rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result (4 * p - 2) (by rw [hp]; omega)]
      simp [s10, d, hd]
      have hc := hcorr.2.2 (p - 1) 2 (by norm_num)
      simpa [tprev, show 4 * (p - 1) + 2 = 4 * p - 2 by ring] using hc
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.R.toInt + Dir.R.toInt = 4 * p + 2 by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg10]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 2) (by rw [hp8]; omega)]
      dsimp [cfg8]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 2) (by rw [hp7]; omega)]
      dsimp [cfg7]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 2) (by rw [hp6]; omega)]
      dsimp [cfg6]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p + 2) (by rw [hp5]; omega)]
      dsimp [cfg5]
      rw [stepConfig_tapeAt_eq_of_eq cfg4 st4.result (4 * p + 2) (by rw [hp4])]
      simp [st4, s10, d, hd]
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.S.toInt + Dir.S.toInt = 4 * p by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg10]
      rw [stepConfig_tapeAt_eq_of_eq cfg9 st9.result (4 * p) (by rw [hp9]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
      simp [st9, s9, s10, d, hd]
  have hread11 : cfg11.tapeAt cfg11.headPos = s11 := by
    rw [hp11]
    rcases hd : r.moveDir with _ | _ | _
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.L.toInt + Dir.L.toInt + Dir.L.toInt = 4 * p - 3 by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg11]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p - 3) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
      dsimp [cfg10]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p - 3) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p - 3) (by rw [hp8]; omega)]
      dsimp [cfg8]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p - 3) (by rw [hp7]; omega)]
      dsimp [cfg7]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p - 3) (by rw [hp6]; omega)]
      dsimp [cfg6]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p - 3) (by rw [hp5]; omega)]
      dsimp [cfg5]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p - 3) (by rw [hp4]; omega)]
      dsimp [cfg4]
      rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result (4 * p - 3) (by rw [hp3]; omega)]
      dsimp [cfg3]
      rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result (4 * p - 3) (by rw [hp2]; omega)]
      dsimp [cfg2]
      rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result (4 * p - 3) (by rw [hp1]; omega)]
      dsimp [cfg1]
      rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result (4 * p - 3) (by rw [hp]; omega)]
      simp [s11, d, hd]
      have hc := hcorr.2.2 (p - 1) 1 (by norm_num)
      simpa [tprev, show 4 * (p - 1) + 1 = 4 * p - 3 by ring] using hc
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.R.toInt + Dir.R.toInt + Dir.R.toInt = 4 * p + 3 by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg11]
      rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 3) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
      dsimp [cfg10]
      rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
      dsimp [cfg9]
      rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 3) (by rw [hp8]; omega)]
      dsimp [cfg8]
      rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 3) (by rw [hp7]; omega)]
      dsimp [cfg7]
      rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 3) (by rw [hp6]; omega)]
      dsimp [cfg6]
      rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p + 3) (by rw [hp5]; omega)]
      dsimp [cfg5]
      rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p + 3) (by rw [hp4]; omega)]
      dsimp [cfg4]
      rw [stepConfig_tapeAt_eq_of_eq cfg3 st3.result (4 * p + 3) (by rw [hp3])]
      simp [st3, s11, d, hd]
    · dsimp [d]
      rw [hd]
      rw [show 4 * p + Dir.S.toInt + Dir.S.toInt + Dir.S.toInt = 4 * p by norm_num [Dir.toInt] <;> ring]
      dsimp [cfg11]
      rw [stepConfig_tapeAt_eq_of_eq cfg10 st10.result (4 * p) (by rw [hp10]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
      simp [st10, s10, s11, d, hd]
  -- 12 步路径
  have hs0 : TapeSteps subsetSumCBTM w cfgc [st0] cfg1 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [] st0 cfgc TapeSteps.nil ?_ ?_ ?_
    · dsimp [st0]
      rw [hst]
    · dsimp [st0]
      rw [hread0]
    · rw [hread0]
      simpa [subsetSumCBTM, hst, hread0, st0] using htr0
  have hs1 : TapeSteps subsetSumCBTM w cfgc [st0, st1] cfg2 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0] st1 cfg1 hs0 ?_ ?_ ?_
    · dsimp [cfg1, stepConfig, st0, st1]
    · dsimp [st1]
      rw [hread1]
    · rw [hread1]
      simpa [subsetSumCBTM, cfg1, stepConfig, st0, st1, hread1] using htr1
  have hs2 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2] cfg3 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1] st2 cfg2 hs1 ?_ ?_ ?_
    · dsimp [cfg2, stepConfig, st1, st2]
    · dsimp [st2]
      rw [hread2]
    · rw [hread2]
      simpa [subsetSumCBTM, cfg2, stepConfig, st1, st2, hread2] using htr2
  have hs3 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3] cfg4 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2] st3 cfg3 hs2 ?_ ?_ ?_
    · dsimp [cfg3, stepConfig, st2, st3]
    · dsimp [st3]
      rw [hread3]
    · rw [hread3]
      simpa [subsetSumCBTM, cfg3, stepConfig, st2, st3, hread3] using htr3
  have hs4 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4] cfg5 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3] st4 cfg4 hs3 ?_ ?_ ?_
    · dsimp [cfg4, stepConfig, st3, st4]
    · dsimp [st4]
      rw [hread4]
    · rw [hread4]
      simpa [subsetSumCBTM, cfg4, stepConfig, st3, st4, hread4] using htr4
  have hs5 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5] cfg6 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4] st5 cfg5 hs4 ?_ ?_ ?_
    · dsimp [cfg5, stepConfig, st4, st5]
    · dsimp [st5]
      rw [hread5]
    · rw [hread5]
      simpa [subsetSumCBTM, cfg5, stepConfig, st4, st5, hread5] using htr5
  have hs6 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5, st6] cfg7 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4, st5] st6 cfg6 hs5 ?_ ?_ ?_
    · dsimp [cfg6, stepConfig, st5, st6]
    · dsimp [st6]
      rw [hread6]
    · rw [hread6]
      simpa [subsetSumCBTM, cfg6, stepConfig, st5, st6, hread6] using htr6
  have hs7 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5, st6, st7] cfg8 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4, st5, st6] st7 cfg7 hs6 ?_ ?_ ?_
    · dsimp [cfg7, stepConfig, st6, st7]
    · dsimp [st7]
      rw [hread7]
    · rw [hread7]
      simpa [subsetSumCBTM, cfg7, stepConfig, st6, st7, hread7] using htr7
  have hs8 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5, st6, st7, st8] cfg9 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4, st5, st6, st7] st8 cfg8 hs7 ?_ ?_ ?_
    · dsimp [cfg8, stepConfig, st7, st8]
    · dsimp [st8]
      rw [hread8]
    · rw [hread8]
      simpa [subsetSumCBTM, cfg8, stepConfig, st7, st8, hread8] using htr8
  have hs9 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5, st6, st7, st8, st9] cfg10 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4, st5, st6, st7, st8] st9 cfg9 hs8 ?_ ?_ ?_
    · dsimp [cfg9, stepConfig, st8, st9]
    · dsimp [st9]
      rw [hread9]
    · rw [hread9]
      simpa [subsetSumCBTM, cfg9, stepConfig, st8, st9, hread9] using htr9
  have hs10 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5, st6, st7, st8, st9, st10] cfg11 := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4, st5, st6, st7, st8, st9] st10 cfg10 hs9 ?_ ?_ ?_
    · dsimp [cfg10, stepConfig, st9, st10]
    · dsimp [st10]
      rw [hread10]
    · rw [hread10]
      simpa [subsetSumCBTM, cfg10, stepConfig, st9, st10, hread10] using htr10
  have hs11 : TapeSteps subsetSumCBTM w cfgc [st0, st1, st2, st3, st4, st5, st6, st7, st8, st9, st10, st11] cfgAfter := by
    refine TapeSteps.cons (M := subsetSumCBTM) (input := w) (cfg₀ := cfgc) [st0, st1, st2, st3, st4, st5, st6, st7, st8, st9, st10] st11 cfg11 hs10 ?_ ?_ ?_
    · dsimp [cfg11, stepConfig, st10, st11]
    · dsimp [st11]
      rw [hread11]
    · rw [hread11]
      simpa [subsetSumCBTM, cfg11, stepConfig, st10, st11, hread11] using htr11
  -- 末格局的磁带特征
  have htapeFinal (z : ℤ) :
      cfgAfter.tapeAt z =
        (if z = 4 * p then w0 else if z = 4 * p + 1 then w1
         else if z = 4 * p + 2 then w2 else if z = 4 * p + 3 then w3
         else cfgc.tapeAt z) := by
    by_cases hz0 : z = 4 * p
    · subst z
      rw [if_pos rfl]
      dsimp [cfgAfter]
      rcases hd : r.moveDir with _ | _ | _
      · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
        dsimp [cfg11]
        rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
        dsimp [cfg10]
        rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
        dsimp [cfg9]
        rw [stepConfig_tapeAt_eq_of_eq cfg8 st8.result (4 * p) (by rw [hp8])]
      · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
        dsimp [cfg11]
        rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
        dsimp [cfg10]
        rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
        dsimp [cfg9]
        rw [stepConfig_tapeAt_eq_of_eq cfg8 st8.result (4 * p) (by rw [hp8])]
      · rw [stepConfig_tapeAt_eq_of_eq cfg11 st11.result (4 * p) (by rw [hp11]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
        simp [st11, s11, d, hd]
    · by_cases hz1 : z = 4 * p + 1
      · subst z
        rw [if_neg hz0, if_pos rfl]
        dsimp [cfgAfter]
        rcases hd : r.moveDir with _ | _ | _
        · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 1) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
          dsimp [cfg11]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 1) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
          dsimp [cfg10]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 1) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
          dsimp [cfg9]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 1) (by rw [hp8]; omega)]
          dsimp [cfg8]
          rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 1) (by rw [hp7]; omega)]
          dsimp [cfg7]
          rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 1) (by rw [hp6]; omega)]
          dsimp [cfg6]
          rw [stepConfig_tapeAt_eq_of_eq cfg5 st5.result (4 * p + 1) (by rw [hp5])]
        · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 1) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
          dsimp [cfg11]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 1) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
          dsimp [cfg10]
          rw [stepConfig_tapeAt_eq_of_eq cfg9 st9.result (4 * p + 1) (by rw [hp9]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
          simp [st9, s9, d, hd]
        · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 1) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
          dsimp [cfg11]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 1) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
          dsimp [cfg10]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 1) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
          dsimp [cfg9]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 1) (by rw [hp8]; omega)]
          dsimp [cfg8]
          rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 1) (by rw [hp7]; omega)]
          dsimp [cfg7]
          rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 1) (by rw [hp6]; omega)]
          dsimp [cfg6]
          rw [stepConfig_tapeAt_eq_of_eq cfg5 st5.result (4 * p + 1) (by rw [hp5])]
      · by_cases hz2 : z = 4 * p + 2
        · subst z
          rw [if_neg hz0, if_neg hz1, if_pos rfl]
          dsimp [cfgAfter]
          rcases hd : r.moveDir with _ | _ | _
          · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 2) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
            dsimp [cfg11]
            rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 2) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
            dsimp [cfg10]
            rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
            dsimp [cfg9]
            rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 2) (by rw [hp8]; omega)]
            dsimp [cfg8]
            rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 2) (by rw [hp7]; omega)]
            dsimp [cfg7]
            rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 2) (by rw [hp6]; omega)]
            dsimp [cfg6]
            rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p + 2) (by rw [hp5]; omega)]
            dsimp [cfg5]
            rw [stepConfig_tapeAt_eq_of_eq cfg4 st4.result (4 * p + 2) (by rw [hp4])]
          · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 2) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
            dsimp [cfg11]
            rw [stepConfig_tapeAt_eq_of_eq cfg10 st10.result (4 * p + 2) (by rw [hp10]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
            simp [st10, s10, d, hd]
          · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 2) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
            dsimp [cfg11]
            rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 2) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
            dsimp [cfg10]
            rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
            dsimp [cfg9]
            rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 2) (by rw [hp8]; omega)]
            dsimp [cfg8]
            rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 2) (by rw [hp7]; omega)]
            dsimp [cfg7]
            rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 2) (by rw [hp6]; omega)]
            dsimp [cfg6]
            rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p + 2) (by rw [hp5]; omega)]
            dsimp [cfg5]
            rw [stepConfig_tapeAt_eq_of_eq cfg4 st4.result (4 * p + 2) (by rw [hp4])]
        · by_cases hz3 : z = 4 * p + 3
          · subst z
            rw [if_neg hz0, if_neg hz1, if_neg hz2, if_pos rfl]
            dsimp [cfgAfter]
            rcases hd : r.moveDir with _ | _ | _
            · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 3) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg11]
              rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 3) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg10]
              rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
              dsimp [cfg9]
              rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 3) (by rw [hp8]; omega)]
              dsimp [cfg8]
              rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 3) (by rw [hp7]; omega)]
              dsimp [cfg7]
              rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 3) (by rw [hp6]; omega)]
              dsimp [cfg6]
              rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p + 3) (by rw [hp5]; omega)]
              dsimp [cfg5]
              rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p + 3) (by rw [hp4]; omega)]
              dsimp [cfg4]
              rw [stepConfig_tapeAt_eq_of_eq cfg3 st3.result (4 * p + 3) (by rw [hp3])]
            · rw [stepConfig_tapeAt_eq_of_eq cfg11 st11.result (4 * p + 3) (by rw [hp11]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
              simp [st11, s11, d, hd]
            · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p + 3) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
              dsimp [cfg11]
              rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p + 3) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
              dsimp [cfg10]
              rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt])]
              dsimp [cfg9]
              rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result (4 * p + 3) (by rw [hp8]; omega)]
              dsimp [cfg8]
              rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result (4 * p + 3) (by rw [hp7]; omega)]
              dsimp [cfg7]
              rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result (4 * p + 3) (by rw [hp6]; omega)]
              dsimp [cfg6]
              rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result (4 * p + 3) (by rw [hp5]; omega)]
              dsimp [cfg5]
              rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result (4 * p + 3) (by rw [hp4]; omega)]
              dsimp [cfg4]
              rw [stepConfig_tapeAt_eq_of_eq cfg3 st3.result (4 * p + 3) (by rw [hp3])]
          · rw [if_neg hz0, if_neg hz1, if_neg hz2, if_neg hz3]
            dsimp [cfgAfter]
            rcases hd : r.moveDir with _ | _ | _
            · by_cases hzL3 : z = 4 * p - 3
              · subst z
                rw [stepConfig_tapeAt_eq_of_eq cfg11 st11.result (4 * p - 3) (by rw [hp11]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
                simp [st11, s11, d, hd]
                have hc := hcorr.2.2 (p - 1) 1 (by norm_num)
                simpa [tprev, show 4 * (p - 1) + 1 = 4 * p - 3 by ring] using hc.symm
              · by_cases hzL2 : z = 4 * p - 2
                · subst z
                  rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p - 2) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
                  dsimp [cfg11]
                  rw [stepConfig_tapeAt_eq_of_eq cfg10 st10.result (4 * p - 2) (by rw [hp10]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
                  simp [st10, s10, d, hd]
                  have hc := hcorr.2.2 (p - 1) 2 (by norm_num)
                  simpa [tprev, show 4 * (p - 1) + 2 = 4 * p - 2 by ring] using hc.symm
                · by_cases hzL1 : z = 4 * p - 1
                  · subst z
                    rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result (4 * p - 1) (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
                    dsimp [cfg11]
                    rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result (4 * p - 1) (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
                    dsimp [cfg10]
                    rw [stepConfig_tapeAt_eq_of_eq cfg9 st9.result (4 * p - 1) (by rw [hp9]; dsimp [d]; rw [hd]; norm_num [Dir.toInt] <;> ring)]
                    simp [st9, s9, d, hd]
                    have hc := hcorr.2.2 (p - 1) 3 (by norm_num)
                    simpa [tprev, show 4 * (p - 1) + 3 = 4 * p - 1 by ring] using hc.symm
                  · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result z (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
                    dsimp [cfg11]
                    rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result z (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
                    dsimp [cfg10]
                    rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result z (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
                    dsimp [cfg9]
                    rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result z (by rw [hp8]; omega)]
                    dsimp [cfg8]
                    rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result z (by rw [hp7]; omega)]
                    dsimp [cfg7]
                    rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result z (by rw [hp6]; omega)]
                    dsimp [cfg6]
                    rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result z (by rw [hp5]; omega)]
                    dsimp [cfg5]
                    rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result z (by rw [hp4]; omega)]
                    dsimp [cfg4]
                    rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result z (by rw [hp3]; omega)]
                    dsimp [cfg3]
                    rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result z (by rw [hp2]; omega)]
                    dsimp [cfg2]
                    rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result z (by rw [hp1]; omega)]
                    dsimp [cfg1]
                    rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result z (by rw [hp]; omega)]
            · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result z (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg11]
              rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result z (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg10]
              rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result z (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg9]
              rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result z (by rw [hp8]; omega)]
              dsimp [cfg8]
              rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result z (by rw [hp7]; omega)]
              dsimp [cfg7]
              rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result z (by rw [hp6]; omega)]
              dsimp [cfg6]
              rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result z (by rw [hp5]; omega)]
              dsimp [cfg5]
              rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result z (by rw [hp4]; omega)]
              dsimp [cfg4]
              rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result z (by rw [hp3]; omega)]
              dsimp [cfg3]
              rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result z (by rw [hp2]; omega)]
              dsimp [cfg2]
              rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result z (by rw [hp1]; omega)]
              dsimp [cfg1]
              rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result z (by rw [hp]; omega)]
            · rw [stepConfig_tapeAt_eq_of_ne cfg11 st11.result z (by rw [hp11]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg11]
              rw [stepConfig_tapeAt_eq_of_ne cfg10 st10.result z (by rw [hp10]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg10]
              rw [stepConfig_tapeAt_eq_of_ne cfg9 st9.result z (by rw [hp9]; dsimp [d]; rw [hd]; simp [Dir.toInt]; omega)]
              dsimp [cfg9]
              rw [stepConfig_tapeAt_eq_of_ne cfg8 st8.result z (by rw [hp8]; omega)]
              dsimp [cfg8]
              rw [stepConfig_tapeAt_eq_of_ne cfg7 st7.result z (by rw [hp7]; omega)]
              dsimp [cfg7]
              rw [stepConfig_tapeAt_eq_of_ne cfg6 st6.result z (by rw [hp6]; omega)]
              dsimp [cfg6]
              rw [stepConfig_tapeAt_eq_of_ne cfg5 st5.result z (by rw [hp5]; omega)]
              dsimp [cfg5]
              rw [stepConfig_tapeAt_eq_of_ne cfg4 st4.result z (by rw [hp4]; omega)]
              dsimp [cfg4]
              rw [stepConfig_tapeAt_eq_of_ne cfg3 st3.result z (by rw [hp3]; omega)]
              dsimp [cfg3]
              rw [stepConfig_tapeAt_eq_of_ne cfg2 st2.result z (by rw [hp2]; omega)]
              dsimp [cfg2]
              rw [stepConfig_tapeAt_eq_of_ne cfg1 st1.result z (by rw [hp1]; omega)]
              dsimp [cfg1]
              rw [stepConfig_tapeAt_eq_of_ne cfgc st0.result z (by rw [hp]; omega)]

  -- Sym 与 CBTM 的带头一致
  have hps : cfgs.headPos = p := by
    have h1 := hcorr.2.1
    rw [hp] at h1
    omega
  -- 末格局对应
  have hcorr' : blockCorrespond cfgAfter (symStepConfig cfgs r) := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [cfgAfter, stepConfig, st11, symStepConfig]
      have hqn : qn = r.nextState := by
        dsimp [qn]
        exact Nat.min_eq_left hns
      rw [hqn]
    · dsimp [cfgAfter, stepConfig, st11, symStepConfig]
      rw [hp11, hps]
      ring
    · intro i j hj
      by_cases hi0 : i = p
      · subst i
        have htap : (symStepConfig cfgs r).tape p = r.writeSym := by
          dsimp [symStepConfig]
          rw [if_pos (by rw [hps])]
        rw [htap]
        rw [htapeFinal (4 * p + ↑j)]
        dsimp [w0, w1, w2, w3, nrs]
        interval_cases j <;> simp [add_left_cancel_iff]
      · have htap : (symStepConfig cfgs r).tape i = cfgs.tape i := by
          dsimp [symStepConfig]
          rw [if_neg]
          intro h
          apply hi0
          rw [hps] at h
          exact h
        rw [htap]
        rw [htapeFinal (4 * i + ↑j)]
        have hc := hcorr.2.2 i j hj
        have hne0 : 4 * i + ↑j ≠ 4 * p := by intro h; apply hi0; omega
        have hne1 : 4 * i + ↑j ≠ 4 * p + 1 := by intro h; apply hi0; omega
        have hne2 : 4 * i + ↑j ≠ 4 * p + 2 := by intro h; apply hi0; omega
        have hne3 : 4 * i + ↑j ≠ 4 * p + 3 := by intro h; apply hi0; omega
        simp [hne0, hne1, hne2, hne3, hc]
  refine ⟨[st0, st1, st2, st3, st4, st5, st6, st7, st8, st9, st10, st11], cfgAfter, hs11, ?_, hcorr', ?_⟩
  · norm_num
  · simp [List.getD]
    simp [st3, regr, w3, nrs]
    simpa [List.getD] using (symTo4F4_getD3_eq_lastD r.writeSym)

end SymToF4
end Mp
