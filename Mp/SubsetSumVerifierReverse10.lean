/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierReverse9
import Mp.A2Bridge
import Mp.SubsetSumCompile
import Mp.SubsetSumVerifierReverse6

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-!
# Reverse10:q10 主证明(1/2)— 无 Canonical 前提的路径桥

A1 条款 3(q10 = 证 `NTM2.Canonical subsetSumNTM2`,SubsetSumVerifierCBTM:972)
的装配起点。Canonical 的量词在 NTM2 层,而全部行为素材(Sym 层验证器 /
F4 层块模拟)在 CBTM 层——需要**不依赖 Canonical** 的路径桥
(TapeReachablePathNTM2 ↔ TapeSteps),避免 q10 证明循环自用 Canonical。

事实:iso_path_forward(A2Bridge:149)的证明体不使用 hcan 参数
(纯步进镜像:NTM2 步经 ntm2ResultToCBTM 映到 CBTM 步)——去参数即可。
-/

open Mp SymToF4

namespace Mp

lemma iso_path_forward_noCan (A : NTM2) (M : CBTM) (iso : StructIsoNTM2CBTM A M) (x : List F4)
 :
    ∀ π, ∀ cfg : NTM2Config A x, TapeReachablePathNTM2 A x π cfg →
      ∃ π' : ComputationPath, ∃ cfg' : CBTMConfig M x,
        TapeReachablePath M x π' cfg' ∧
        cfg' = ntm2CfgToCBTM A M iso cfg := by
  intro π cfg hr
  induction hr with
  | nil =>
      refine ⟨[], initialConfig M x, TapeReachablePath.nil, ?_⟩
      exact (iso_initial_corresp A M iso x).symm
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      rcases ih with ⟨π', cfg', hrc', hcfg'⟩
      have hs_in : step.readSym ∈ A.alphabet := by
        by_contra hsnot
        have hout := A.h_transition_outside cfg₀.state step.readSym cfg₀.headPos hsnot
        rw [← hread] at htrans
        rw [hout] at htrans
        simpa using htrans
      let step' : TransitionStep :=
        { fromState := step.fromState,
          readSym := step.readSym,
          result := ntm2ResultToCBTM step.result }
      refine ⟨π' ++ [step'], stepConfig cfg' step'.result,
        TapeReachablePath.cons π' step' cfg' hrc' ?_ ?_ ?_, ?_⟩
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        rw [← hfrom]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        dsimp [step']
        rw [hread]
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM, CBTMConfig.tapeAt]
        dsimp [step']
        rw [← hread, ← hpos] at htrans ⊢
        have hstepfwd := iso_step_forward A M iso cfg₀.state step.readSym step.pos step.result hs_in htrans
        rw [iso.h_φ_id step.readSym] at hstepfwd
        exact hstepfwd
      · rw [hcfg']
        dsimp [ntm2CfgToCBTM]
        dsimp [step']
        exact (iso_step_config A M iso cfg₀ step.result).symm

-- ==============================================================================
-- q10 ① NTM2 层(S1:相位-位置引理,设计 _q10-pos-bound-design.md)
-- 相位 = 状态编码 phase 分量(st/8192 % 12);相位 0-2(读阶段,读 im=false)
-- 的转移方向恒 R(缓冲读——4 条计算带间的顺序切换,线性化坐标 +1)。
-- ==============================================================================

/-- 相位 0-2 读 im=false 的转移方向恒 R。 -/
lemma trans4_phase_lt3_dir_R (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hph : (st / 8192) % 12 < 3) (him : ¬ F4.im s) :
    r.moveDir = Dir.R := by
  unfold transition4 at hr
  dsimp [decodeState] at hr
  rw [if_pos hph] at hr
  rw [if_neg him] at hr
  simp at hr
  rw [hr]

-- ==============================================================================
-- q10 ① NTM2 层(S1-B:101 吸收段锁定)
-- 表行 | 101, _ => {ret 101 s S}:读任意符号 → 自环、写回原符号、方向 S。
-- 段内位置与磁带不变 → 101 段位置锁定于进入点(带内)。
-- ==============================================================================

/-- 101 吸收:读任意符号 → 自环(态 101)、写回原符号、方向 S。 -/
lemma sym_absorb_101 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (101, s)) :
    r.nextState = 101 ∧ r.writeSym = s ∧ r.moveDir = Dir.S := by
  revert s r hr
  decide

/-- 100 吸收(同上;100 出发步被 hnoTerm 排除,此处备用)。 -/
lemma sym_absorb_100 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (100, s)) :
    r.nextState = 100 ∧ r.writeSym = s ∧ r.moveDir = Dir.S := by
  revert s r hr
  decide

-- ==============================================================================
-- q10 ① NTM2 层(S1-B 续:101 段锁定 — SymSteps 级)
-- 从 101 态出发的任何路径:每步转移 = 吸收(101 读任意 → 101 写回 S),
-- 位置与磁带不变 → 101 段锁定于进入点。
-- ==============================================================================

/-- 从 101 态出发的 SymSteps 段:终点位置/磁带/状态与起点相同(吸收锁定)。 -/
lemma symSteps_absorb101_locked {π : List SymStep} {cfg₀ cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) (h0 : cfg₀.state = 101) :
    cfg.headPos = cfg₀.headPos ∧ cfg.tape = cfg₀.tape ∧ cfg.state = 101 := by
  induction h with
  | nil => simp [h0]
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨ihp, iht, ihs⟩
      have hres := sym_absorb_101 (cfg₁.tape cfg₁.headPos) step.result (by simpa [ihs] using htrans)
      rcases hres with ⟨hn, hw, hd⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [symStepConfig, ihp, hd, Dir.toInt]
      · funext i
        by_cases hi : i = cfg₁.headPos
        · simp [hi, symStepConfig, hw, iht, ihp]
        · simp [hi, symStepConfig, iht]
      · simp [symStepConfig, hn]

-- ==============================================================================
-- q10 ① Sym 层表级支持:越界态集 Y(读带外格可 R 的态)
-- 验证(探针 _chkY):L1/L2 绿;L3/L4 假 ⟹ 组合定理需域论证(非简单闭包)。
-- ==============================================================================

/-- Y = 读带外格(Sym.blank = data0 false)存在 R 转移的态:漂出候选。 -/
def symYset : Finset ℕ := {1, 2, 11, 12, 14, 21, 28, 51, 81, 87}

/-- L1: 读 blank R ⟹ q ∈ symYset。 -/
theorem sym_blank_R_mem_Y : ∀ q : Fin 102, ∀ r : SymTransResult,
    r ∈ VerifierSym.transition ((q : ℕ), Sym.blank) → r.moveDir = Dir.R →
    (q : ℕ) ∈ symYset := by
  native_decide

/-- L2: q ∉ symYset → 读 blank 不 R(带头 = |enc| 处读带外不漂的必要件)。 -/
theorem sym_blank_notR_of_not_Y : ∀ q : Fin 102, (q : ℕ) ∉ symYset → ∀ r : SymTransResult,
    r ∈ VerifierSym.transition ((q : ℕ), Sym.blank) → r.moveDir ≠ Dir.R := by
  native_decide

-- ==============================================================================
-- q10 ① 任意路径束(Sym 层域论证族,样板:Reverse6 q12suffix_state23_inside)
-- 0 态/1 态域:0 无入边(仅初始);1 态域 = target 区(带头 ≤ bits+1)且 #₁ 未被覆盖。
-- 坑:symInitialConfig 的 if(toNat 条件)用 split 处理(if_pos/if_neg 于 Decidable 参数 mismatch)。
-- ==============================================================================

theorem sym_no_into_0 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : r.nextState ≠ 0 := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ≠ 0 := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr

lemma sym_domain_state0 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 0 → cfg.headPos = 0 := by
  intro h0
  induction h with
  | nil => simp [symInitialConfig] at h0 ⊢
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hns : step.result.nextState ≠ 0 := by
        have hq : cfg₁.state < 102 := q12_path_state_lt102 input π₀ cfg₁ hprev
        exact sym_no_into_0 cfg₁.state hq step.readSym step.result (by simpa [hread] using htrans)
      have hns0 : step.result.nextState = 0 := by
        simpa [symStepConfig] using h0
      exact False.elim (hns hns0)

theorem sym_into_1_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h1 : r.nextState = 1) :
    (q = 0 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
    (q = 1 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.R ∧
      r.writeSym.1 = s.1) := by
  have hbb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 1 →
        ((q : ℕ) = 0 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 1 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.R ∧
          r.writeSym.1 = s.1) := by
    native_decide
  exact hbb ⟨q, hq⟩ s r hr h1

-- 1 态域(联合):1 态可达 ⟹ 带头 ≤ bits+1 且 tape(bits+1) = boundary(#₁ 未被覆盖)

lemma sym_path_state0_initial {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition input π cfg) :
    cfg.state = 0 → cfg = symInitialConfig input := by
  intro h0
  induction h with
  | nil => rfl
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hns : step.result.nextState ≠ 0 := by
        have hq : cfg₁.state < 102 := q12_path_state_lt102 input π₀ cfg₁ hprev
        exact sym_no_into_0 cfg₁.state hq step.readSym step.result (by simpa [hread] using htrans)
      have hns0 : step.result.nextState = 0 := by
        simpa [symStepConfig] using h0
      exact False.elim (hns hns0)


/-- 初始配置的带在位置 bits+1(#₁)处 = boundary。 -/
lemma symInitial_tape_ofNat {input : List Sym} (i : ℕ) (hi : i < input.length) :
    (symInitialConfig input).tape (i : ℤ) = input[i] := by
  dsimp [symInitialConfig]
  split
  · rfl
  · exfalso
    rename_i h
    apply h
    exact ⟨by omega, hi⟩

lemma symInitial_tape_mid_boundary (inst : SubsetSumInstance) :
    (symInitialConfig (encodeInstanceSym inst)).tape
      (((encodeBitsSym inst.target).length : ℤ) + 1) = Sym.boundary := by
  have hmid : 1 + (encodeBitsSym inst.target).length < (encodeInstanceSym inst).length := by
    unfold encodeInstanceSym
    simp []
    omega
  rw [show ((encodeBitsSym inst.target).length : ℤ) + 1 =
      ((1 + (encodeBitsSym inst.target).length : ℕ) : ℤ) by omega]
  rw [symInitial_tape_ofNat (1 + (encodeBitsSym inst.target).length) hmid]
  rw [← List.getD_eq_getElem (encodeInstanceSym inst) Sym.blank hmid]
  exact enc_getD_boundary_mid inst

lemma sym_domain_state1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 1 → cfg.headPos ≤ ((encodeBitsSym inst.target).length : ℤ) + 1 ∧
      cfg.tape (((encodeBitsSym inst.target).length : ℤ) + 1) = Sym.boundary := by
  intro h1
  induction h with
  | nil => simp [symInitialConfig] at h1
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hns1 : step.result.nextState = 1 := by simpa [symStepConfig] using h1
      have hq : cfg₁.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg₁ hprev
      have htrans' : step.result ∈ VerifierSym.transition (cfg₁.state, step.readSym) := by
        simpa [hread] using htrans
      rcases sym_into_1_class cfg₁.state hq step.readSym step.result htrans' hns1 with h01 | h11
      · rcases h01 with ⟨hq0, hb, hR⟩
        have hpos0 : cfg₁.headPos = 0 := sym_domain_state0 hprev hq0
        -- 步前 cfg₁ 是 0 态 ⟹ 必为初始(带头 0,带 = 初始 enc)——由 hprev 的 0 态域 + 0 态无写步?
        -- 0 态 cfg₁:其路径上无写(0 只初始——nextState=0 无入边 ⟹ cfg₁ 就是初始配置)
        -- ⟹ tape = symInitialConfig 的带 = enc 内容
        constructor
        · rw [symStepConfig, hR, hpos0]
          simp [Dir.toInt]
        · -- tape(bits+1) = #₁:cfg₁ = 初始(0 态无入边)⟹ 步写于带头 0(bits+1 ≠ 0)
          have hinit : cfg₁ = symInitialConfig (encodeInstanceSym inst) := by
            exact sym_path_state0_initial hprev hq0
          rw [symStepConfig]
          dsimp
          have hne0 : ((encodeBitsSym inst.target).length : ℤ) + 1 ≠ cfg₁.headPos := by
            rw [hpos0]
            omega
          rw [if_neg hne0]
          simp [hinit]
          exact symInitial_tape_mid_boundary inst
      · rcases h11 with ⟨hq1, hd, hR, hw⟩
        rcases ih hq1 with ⟨hle, hbnd⟩
        have hne : cfg₁.headPos ≠ ((encodeBitsSym inst.target).length : ℤ) + 1 := by
          intro heq
          -- 读处 = data(hd)但带形给 #₁(boundary)
          have hsym : step.readSym = Sym.boundary := by
            rw [hread, heq]
            exact hbnd
          rcases hd with hd0 | hd1
          · have hbad : SymKind.boundary = SymKind.data0 := by
              simpa [Sym.boundary, hsym] using hd0
            exact (by decide : SymKind.boundary ≠ SymKind.data0) hbad
          · have hbad : SymKind.boundary = SymKind.data1 := by
              simpa [Sym.boundary, hsym] using hd1
            exact (by decide : SymKind.boundary ≠ SymKind.data1) hbad
        constructor
        · -- 步后带头 = cfg₁.headPos + 1 ≤ bits+1(带头 ≤ bits 因 ≠ bits+1)
          rw [symStepConfig, hR]
          simp [Dir.toInt]
          omega
        · -- tape(bits+1) 保持:步写于带头(≠ bits+1)
          rw [symStepConfig]
          dsimp
          rw [if_neg (Ne.symm hne)]
          exact hbnd


namespace SymToF4

-- D. transition4 相位 moveDir 分类(好块步版:nontrap = (decodeState r.nextState).1 ≠ 101)

/-- 陷阱双结果的 nextState 解码 = 101。 -/
lemma trap_mem_nextState_decode (ph : ℕ) (s : F4) (r : CBTMTransResult)
    (h : r = CBTMTransResult.mk (encodeState 101 ph 0) s Dir.S ∨
         r = CBTMTransResult.mk (encodeState 101 ph 0) s Dir.R)
    (hph : ph < 12) :
    (decodeState r.nextState).1 = 101 := by
  rcases h with h | h <;> rw [h]
  · apply decodeState_encodeState_q_eq 101 ph 0
    have hrb : 0 < regBound := by norm_num [regBound]
    norm_num [stepsPerSym]
    nlinarith
  · apply decodeState_encodeState_q_eq 101 ph 0
    have hrb : 0 < regBound := by norm_num [regBound]
    norm_num [stepsPerSym]
    nlinarith

/-- 陷阱单结果(S)的 nextState 解码 = 101。 -/
lemma trap1_mem_nextState_decode (ph : ℕ) (s : F4) (r : CBTMTransResult)
    (h : r = CBTMTransResult.mk (encodeState 101 ph 0) s Dir.S) (hph : ph < 12) :
    (decodeState r.nextState).1 = 101 := by
  rw [h]
  apply decodeState_encodeState_q_eq 101 ph 0
  have hrb : 0 < regBound := by norm_num [regBound]
  norm_num [stepsPerSym]
  nlinarith

lemma trans4_phase_lt3_dir_R_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) :
    (decodeState st).2.1 < 3 → (decodeState r.nextState).1 ≠ 101 → r.moveDir = Dir.R := by
  intro hph hnt
  unfold transition4 at hr
  dsimp at hr
  split_ifs at hr <;> simp_all []
    ; try (exfalso; exact (hnt (trap_mem_nextState_decode _ _ _ hr (by omega))).elim)

lemma trans4_phase4_dir_L_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) :
    (decodeState st).2.1 = 4 → (decodeState r.nextState).1 ≠ 101 → r.moveDir = Dir.L := by
  intro hph hnt
  unfold transition4 at hr
  dsimp at hr
  split_ifs at hr <;> simp_all []
    ; try (exfalso; exact (hnt (trap_mem_nextState_decode _ _ _ hr (by omega))).elim)

lemma trans4_phase5_dir_L_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) :
    (decodeState st).2.1 = 5 → (decodeState r.nextState).1 ≠ 101 → r.moveDir = Dir.L := by
  intro hph hnt
  unfold transition4 at hr
  dsimp at hr
  split_ifs at hr <;> simp_all []
    ; try (exfalso; exact (hnt (trap_mem_nextState_decode _ _ _ hr (by omega))).elim)

lemma trans4_phase6_dir_S_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) :
    (decodeState st).2.1 = 6 → (decodeState r.nextState).1 ≠ 101 → r.moveDir = Dir.S := by
  intro hph hnt
  unfold transition4 at hr
  dsimp at hr
  split_ifs at hr <;> simp_all []
    ; try (exfalso; exact (hnt (trap_mem_nextState_decode _ _ _ hr (by omega))).elim)

lemma trans4_phase7_dir_S_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) :
    (decodeState st).2.1 = 7 → (decodeState r.nextState).1 ≠ 101 → r.moveDir = Dir.S := by
  intro hph hnt
  unfold transition4 at hr
  dsimp at hr
  split_ifs at hr <;> simp_all []
    ; try (exfalso; exact (hnt (trap_mem_nextState_decode _ _ _ hr (by omega))).elim)

lemma trans4_phase_ge8_dir_bounded_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (_hr : r ∈ transition4 st s) :
    8 ≤ (decodeState st).2.1 → (decodeState st).2.1 < 12 → (decodeState r.nextState).1 ≠ 101 →
    (decodeState st).1 ≠ 101 →
    r.moveDir.toInt = 1 ∨ r.moveDir.toInt = 0 ∨ r.moveDir.toInt = -1 := by
  intro _ _ _ _
  cases r.moveDir <;> simp [Dir.toInt]

end SymToF4
namespace SymToF4

-- C. F4 层 TapeSteps 步位置求和(终点头 = 起点头 + ΣmoveDir)
lemma tapeSteps_headPos_sum {M : CBTM} {input : List F4} {cfg₀ cfg : CBTMConfig M input}
    {π : ComputationPath} (h : TapeSteps M input cfg₀ π cfg) :
    cfg.headPos = cfg₀.headPos + (π.map (fun s => s.result.moveDir.toInt)).sum := by
  induction h with
  | nil =>
      simp
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      calc
        (stepConfig cfg₁ step.result).headPos = cfg₁.headPos + step.result.moveDir.toInt := by
          simp [stepConfig]
        _ = cfg₀.headPos + (π₀.map (fun s => s.result.moveDir.toInt)).sum + step.result.moveDir.toInt := by
          rw [ih]
        _ = cfg₀.headPos + ((π₀ ++ [step]).map (fun s => s.result.moveDir.toInt)).sum := by
          simp [List.sum_append, Int.add_assoc]

end SymToF4
namespace SymToF4

lemma tapeSteps_prefix_end {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) :
    ∀ m (_hm : m ≤ π.length),
      ∃ cfgm : CBTMConfig M input,
        TapeSteps M input cfg₀ (π.take m) cfgm := by
  induction h with
  | nil =>
      intro m hm
      have hm0 : m = 0 := by simpa using hm
      subst m
      refine ⟨cfg₀, ?_⟩
      simpa using TapeSteps.nil
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro m hm
      rw [List.length_append] at hm
      by_cases hmle : m ≤ π₀.length
      · rcases ih m hmle with ⟨cfgm, hpfx⟩
        refine ⟨cfgm, ?_⟩
        -- (π₀ ++ [step]).take m = π₀.take m(m ≤ π₀.length)
        have htake : (π₀ ++ [step]).take m = π₀.take m := by
          rw [List.take_append]
          simp [hmle]
        simpa [htake] using hpfx
      · have hm' : m = π₀.length + 1 := by
          simp at hm
          omega
        subst m
        refine ⟨stepConfig cfg₁ step.result, ?_⟩
        have htake : (π₀ ++ [step]).take (π₀.length + 1) = π₀ ++ [step] := by
          simp [List.take_append]
        simpa [htake] using (TapeSteps.cons π₀ step cfg₁ hprev hfrom hread htrans)

/-- 通用漂移:每步 ±1 前提下,每前缀终点 cfg 的 headPos ∈ [lo-m, hi+m],终点 cfg 界同。 -/
lemma tapeSteps_prefix_headPos_drift {M : CBTM} {input : List F4}
    {cfg₀ cfg : CBTMConfig M input} {π : ComputationPath}
    (h : TapeSteps M input cfg₀ π cfg) {lo hi : ℤ}
    (hbounds : ∀ step ∈ π, step.result.moveDir.toInt = -1 ∨ step.result.moveDir.toInt = 0 ∨
        step.result.moveDir.toInt = 1)
    (hfirst : cfg₀.headPos ∈ Set.Icc lo hi) :
    (∀ m (_hm : m ≤ π.length),
      ∃ cfgm : CBTMConfig M input,
        TapeSteps M input cfg₀ (π.take m) cfgm ∧
        cfgm.headPos ∈ Set.Icc (lo - (m : ℤ)) (hi + (m : ℤ))) ∧
    cfg.headPos ∈ Set.Icc (lo - (π.length : ℤ)) (hi + (π.length : ℤ)) := by
  induction h with
  | nil =>
      constructor
      · intro m hm
        have hm0 : m = 0 := by simpa using hm
        subst m
        refine ⟨cfg₀, ?_, ?_⟩
        · simpa using TapeSteps.nil
        · simpa using hfirst
      · simpa using hfirst
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hb₀ : ∀ step ∈ π₀, step.result.moveDir.toInt = -1 ∨ step.result.moveDir.toInt = 0 ∨
          step.result.moveDir.toInt = 1 := by
        intro st hs
        exact hbounds st (by simp [hs])
      constructor
      · intro m hm
        rw [List.length_append] at hm
        by_cases hmle : m ≤ π₀.length
        · rcases (ih hb₀).1 m hmle with ⟨cfgm, hpfx, hbnd⟩
          refine ⟨cfgm, ?_, ?_⟩
          · have htake : (π₀ ++ [step]).take m = π₀.take m := by
              rw [List.take_append]
              simp [hmle]
            simpa [htake] using hpfx
          · simpa using hbnd
        · have hm' : m = π₀.length + 1 := by
            simp at hm
            omega
          subst m
          refine ⟨stepConfig cfg₁ step.result, ?_, ?_⟩
          · have htake : (π₀ ++ [step]).take (π₀.length + 1) = π₀ ++ [step] := by
              simp [List.take_append]
            simpa [htake] using (TapeSteps.cons π₀ step cfg₁ hprev hfrom hread htrans)
          · have hcfg₁b := (ih hb₀).2
            rcases hcfg₁b with ⟨hlo₁, hhi₁⟩
            have hdir : step.result.moveDir.toInt = -1 ∨ step.result.moveDir.toInt = 0 ∨
                step.result.moveDir.toInt = 1 := hbounds step (by simp)
            have hhh : (stepConfig cfg₁ step.result).headPos = cfg₁.headPos + step.result.moveDir.toInt := by
              simp [stepConfig]
            rw [hhh]
            rcases hdir with hd | hd | hd
            · rw [hd]
              constructor <;> simp <;> omega
            · rw [hd]
              constructor <;> simp <;> omega
            · rw [hd]
              constructor <;> simp <;> omega
      · -- 终点界:cfg = stepConfig cfg₁ step.result;cfg₁ 界 = ih.2(前缀 π₀ 的终点)
        have hcfg₁ := (ih hb₀).2
        rcases hcfg₁ with ⟨hlo₁, hhi₁⟩
        have hdir : step.result.moveDir.toInt = -1 ∨ step.result.moveDir.toInt = 0 ∨
            step.result.moveDir.toInt = 1 := hbounds step (by simp)
        have hhh : (stepConfig cfg₁ step.result).headPos = cfg₁.headPos + step.result.moveDir.toInt := by
          simp [stepConfig]
        rw [hhh]
        rcases hdir with hd | hd | hd
        · rw [hd]
          constructor <;> simp <;> omega
        · rw [hd]
          constructor <;> simp <;> omega
        · rw [hd]
          constructor <;> simp <;> omega


end SymToF4
lemma tapeSteps_phase_at {w : List F4} {cfgc0 cfg : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {q : ℕ}
    (h : TapeSteps subsetSumCBTM w cfgc0 π cfg)
    (hq0 : cfgc0.state = encodeState q 0 0) :
    ((decodeState cfg.state).2.1 = π.length % 12 ∧
     (decodeState cfg.state).2.2 < regBound ∧
     ((decodeState cfg.state).2.1 < 3 →
      (decodeState cfg.state).2.2 < 4 ^ (decodeState cfg.state).2.1)) ∧
    (∀ m (hm : m < π.length),
      (decodeState (π.get ⟨m, hm⟩).fromState).2.1 = m % 12 ∧
      (decodeState (π.get ⟨m, hm⟩).fromState).2.2 < regBound ∧
      ((decodeState (π.get ⟨m, hm⟩).fromState).2.1 < 3 →
       (decodeState (π.get ⟨m, hm⟩).fromState).2.2 <
         4 ^ (decodeState (π.get ⟨m, hm⟩).fromState).2.1)) := by
  induction h with
  | nil =>
      constructor
      · rw [hq0]
        simp [decodeState, encodeState, stepsPerSym, regBound]
      · intro m hm
        have hm' : m < 0 := by simpa using hm
        linarith
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      rcases ih with ⟨ihEnd, ihMid⟩
      have htrans' : step.result ∈ transition4 cfg₁.state step.readSym := by
        rw [hread]
        exact htrans
      have hbufOK : (cfg₁.state / regBound) % stepsPerSym < 3 →
          cfg₁.state % regBound +
            bufOf3s ((cfg₁.state / regBound) % stepsPerSym) step.readSym (cfg₁.state % regBound) < regBound := by
        intro hlt3
        dsimp [decodeState, stepsPerSym, regBound] at ihEnd
        have h64 : cfg₁.state % regBound < 4 ^ ((cfg₁.state / regBound) % stepsPerSym) :=
          ihEnd.2.2 hlt3
        have hp012 : (cfg₁.state / regBound) % stepsPerSym = 0 ∨
            (cfg₁.state / regBound) % stepsPerSym = 1 ∨
            (cfg₁.state / regBound) % stepsPerSym = 2 := by
          have hlt' : (cfg₁.state / 8192) % 12 < 3 := by
            dsimp [stepsPerSym, regBound] at hlt3
            exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hlt3) (by norm_num)
          simpa [stepsPerSym, regBound] using mod12_lt3_eq (cfg₁.state / 8192) hlt'
        have hpow : 4 ^ ((cfg₁.state / regBound) % stepsPerSym) ≤ 16 := by
          rcases hp012 with h2 | h1 | h0
          · rw [h2]; norm_num
          · rw [h1]; norm_num
          · rw [h0]; norm_num
        have hbuf : bufOf3s ((cfg₁.state / regBound) % stepsPerSym) step.readSym
              (cfg₁.state % regBound) ≤ 48 := by
          unfold bufOf3s
          have hle2 : (cfg₁.state / regBound) % stepsPerSym ≤ 2 := by
            dsimp [stepsPerSym] at hlt3
            omega
          rcases step.readSym with ⟨rs, is⟩
          cases rs <;> cases is <;> simp [F4.zero, F4.one, F4.alpha]
          all_goals first | done | nlinarith [hpow]
        dsimp [regBound, stepsPerSym] at h64 hpow hbuf ⊢
        omega
      have hstep := transition4_phase_succ cfg₁.state step.readSym step.result htrans'
        (by rw [ihEnd.1]; exact Nat.mod_lt _ (by decide : 0 < 12)) hbufOK
      have hend : (decodeState (stepConfig cfg₁ step.result).state).2.1 = (π₀ ++ [step]).length % 12 ∧
          (decodeState (stepConfig cfg₁ step.result).state).2.2 < regBound ∧
          ((decodeState (stepConfig cfg₁ step.result).state).2.1 < 3 →
           (decodeState (stepConfig cfg₁ step.result).state).2.2 <
             4 ^ (decodeState (stepConfig cfg₁ step.result).state).2.1) := by
        dsimp [stepConfig]
        rw [hstep]
        rw [ihEnd.1]
        constructor
        · -- 第一分量：相位等式
          simp [Nat.add_mod]
        · constructor
          · -- reg 分量 < regBound：恒真
            dsimp [decodeState, stepsPerSym, regBound]
            exact Nat.mod_lt _ (by decide : 0 < regBound)
          · -- 相位 < 3 ⟹ reg < 4^相位（新状态维持）
            intro hlt3'
            rw [Nat.add_mod] at hlt3'
            by_cases hlt3 : (decodeState cfg₁.state).2.1 < 3
            · have h64 : (decodeState cfg₁.state).2.2 < 4 ^ (decodeState cfg₁.state).2.1 :=
                ihEnd.2.2 hlt3
              have hreg := transition4_read_phase_reg_lt cfg₁.state step.readSym step.result
                htrans' hlt3 h64
              rw [← ihEnd.1, ← hstep]
              exact hreg
            · have hlt12 : (decodeState cfg₁.state).2.1 < 12 := by
                rw [ihEnd.1]
                exact Nat.mod_lt _ (by decide : 0 < 12)
              by_cases h11 : (decodeState cfg₁.state).2.1 = 11
              · have hz := transition4_phase11_reg_eq_zero cfg₁.state step.readSym step.result
                  htrans' h11
                rw [← ihEnd.1, ← hstep]
                rw [hz.1, hz.2]
                norm_num
              · have hge := transition4_phase_ge3_ne11_next_ge3 cfg₁.state step.readSym step.result
                  htrans' hlt12 (by omega) h11
                rw [← ihEnd.1, ← hstep]
                first | done | omega
      constructor
      · exact hend
      · intro m hm
        have hm' : m < (π₀ ++ [step]).length := by simpa using hm
        have hlt_or : m < π₀.length ∨ m = π₀.length := by
          simp at hm'
          omega
        rcases hlt_or with hlt | heq
        · have hg : (π₀ ++ [step]).get ⟨m, hm⟩ = π₀.get ⟨m, hlt⟩ := by
            exact List.getElem_append_left hlt
          rw [hg]
          exact ihMid m hlt
        · subst m
          have hg : (π₀ ++ [step]).get ⟨π₀.length, hm⟩ = step := by
            simpa using (List.getElem_append_right (α := TransitionStep) (as := π₀)
              (bs := [step]) (i := π₀.length) (Nat.le_refl π₀.length))
          simpa [hg, hfrom] using ihEnd

/-- 相位 3(合成步)的 nontrap 版:moveDir = L。 -/
lemma trans4_phase3_dir_L_of_nontrap (st : ℕ) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 st s) :
    (decodeState st).2.1 = 3 → (decodeState r.nextState).1 ≠ 101 → r.moveDir = Dir.L := by
  intro hph hnt
  unfold transition4 at hr
  dsimp at hr
  -- symOf4F4 match 先拆(none/some)
  by_cases hso : symOf4F4 (f4ofBuf (decodeState st).2.2).1 (f4ofBuf (decodeState st).2.2).2.1
      (f4ofBuf (decodeState st).2.2).2.2 s = none
  · rw [hso] at hr
    -- none 支:if F4.im s then trap 双 else trap1
    split_ifs at hr <;> simp_all []
    all_goals
      first
      | (exfalso; apply hnt;
          exact decodeState_encodeState_q_eq 101 4 0 (by norm_num [stepsPerSym, regBound]))
      | (rcases hr with rfl | rfl <;> exfalso <;> apply hnt <;>
          exact decodeState_encodeState_q_eq 101 4 0 (by norm_num [stepsPerSym, regBound]))
  · have hso' : ∃ sym : Sym, symOf4F4 (f4ofBuf (decodeState st).2.2).1
          (f4ofBuf (decodeState st).2.2).2.1 (f4ofBuf (decodeState st).2.2).2.2 s = some sym := by
      cases h : symOf4F4 (f4ofBuf (decodeState st).2.2).1 (f4ofBuf (decodeState st).2.2).2.1
          (f4ofBuf (decodeState st).2.2).2.2 s
      · exfalso
        exact hso h
      · refine ⟨_, rfl⟩
    rcases hso' with ⟨sym, hsym⟩
    rw [hsym] at hr
    -- some 支:if F4.im s then (if qs=2∧… then sel/nosel else trap) else image
    split_ifs at hr <;> simp_all []
    all_goals
      first
      | (exfalso; apply hnt;
          exact decodeState_encodeState_q_eq 101 4 0 (by norm_num [stepsPerSym, regBound]))
      | (rcases hr with rfl | rfl <;> exfalso <;> apply hnt <;>
          exact decodeState_encodeState_q_eq 101 4 0 (by norm_num [stepsPerSym, regBound]))
      | (rcases hr with rfl; exfalso; apply hnt;
          exact decodeState_encodeState_q_eq 101 4 0 (by norm_num [stepsPerSym, regBound]))
      | (exfalso; apply hnt; rw [hr];
          exact decodeState_encodeState_q_eq 101 4 0 (by norm_num [stepsPerSym, regBound]))
      | (rw [hr]; rfl)
      | (rcases hr with rfl | rfl <;> rfl)
      | (rcases hr with ⟨t, ht, heq⟩; rw [← heq]; try rfl)

-- 段级 dir 分类:从 fromState 相位推 moveDir(0-2 R / 3-5 L / 6-7 S / 8-11 ±1∨0)
lemma step_dir_phase_lt3 (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hph : (decodeState st).2.1 < 3)
    (hnt : (decodeState r.nextState).1 ≠ 101) : r.moveDir = Dir.R := by
  exact trans4_phase_lt3_dir_R_of_nontrap st s r hr hph hnt

lemma step_dir_phase3_5 (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hph : 3 ≤ (decodeState st).2.1)
    (hph2 : (decodeState st).2.1 ≤ 5) (hnt : (decodeState r.nextState).1 ≠ 101) : r.moveDir = Dir.L := by
  have h3 : (decodeState st).2.1 = 3 ∨ (decodeState st).2.1 = 4 ∨ (decodeState st).2.1 = 5 := by omega
  rcases h3 with h3 | h4 | h5
  · exact trans4_phase3_dir_L_of_nontrap st s r hr h3 hnt
  · exact trans4_phase4_dir_L_of_nontrap st s r hr h4 hnt
  · exact trans4_phase5_dir_L_of_nontrap st s r hr h5 hnt

lemma step_dir_phase6_7 (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hph : (decodeState st).2.1 = 6 ∨ (decodeState st).2.1 = 7)
    (hnt : (decodeState r.nextState).1 ≠ 101) : r.moveDir = Dir.S := by
  rcases hph with h6 | h7
  · exact trans4_phase6_dir_S_of_nontrap st s r hr h6 hnt
  · exact trans4_phase7_dir_S_of_nontrap st s r hr h7 hnt

lemma step_dir_phase_ge8 (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) (hph : 8 ≤ (decodeState st).2.1)
    (hph2 : (decodeState st).2.1 < 12) (hnt : (decodeState r.nextState).1 ≠ 101)
    (hne101q : (decodeState st).1 ≠ 101) :
    r.moveDir.toInt = 1 ∨ r.moveDir.toInt = 0 ∨ r.moveDir.toInt = -1 := by
  exact trans4_phase_ge8_dir_bounded_of_nontrap st s r hr hph hph2 hnt hne101q
def delta8 (m : ℕ) : ℤ :=
  if m ≤ 3 then (m : ℤ) else if m ≤ 6 then ((6 - m : ℕ) : ℤ) else 0

/-- 步进:位置 delta8 m + dir(m) = delta8 (m+1)(m<8;dir 由相位分类给)。 -/
lemma delta8_step (m : ℕ) (hm : m < 8) (d : ℤ)
    (hR : m ≤ 2 → d = 1) (hL : 3 ≤ m → m ≤ 5 → d = -1) (hS : 6 ≤ m → d = 0) :
    delta8 m + d = delta8 (m + 1) := by
  interval_cases m
  · -- m=0:R
    rw [hR (by norm_num)]
    norm_num [delta8]
  · rw [hR (by norm_num)]
    norm_num [delta8]
  · rw [hR (by norm_num)]
    norm_num [delta8]
  · -- m=3:L
    rw [hL (by norm_num) (by norm_num)]
    norm_num [delta8]
  · rw [hL (by norm_num) (by norm_num)]
    norm_num [delta8]
  · rw [hL (by norm_num) (by norm_num)]
    norm_num [delta8]
  · -- m=6:S
    rw [hS (by norm_num)]
    norm_num [delta8]
  · rw [hS (by norm_num)]
    norm_num [delta8]

/-- 漂移段的区间扩张:8 ≤ m 时前缀 m ∈ [4p-(m-8), 4p+(m-8)],±1 步后 ∈ [4p-((m+1)-8), 4p+((m+1)-8)]。 -/
lemma drift_interval_step (p : ℤ) (m : ℕ) (hm8 : 8 ≤ m) (x d : ℤ)
    (hx : x ∈ Set.Icc (4 * p - ((m - 8 : ℕ) : ℤ)) (4 * p + ((m - 8 : ℕ) : ℤ)))
    (hd : d = 1 ∨ d = 0 ∨ d = -1) :
    x + d ∈ Set.Icc (4 * p - (((m + 1) - 8 : ℕ) : ℤ)) (4 * p + (((m + 1) - 8 : ℕ) : ℤ)) := by
  rcases hx with ⟨hlo, hhi⟩
  rcases hd with hd | hd | hd
  · rw [hd]
    constructor <;> omega
  · rw [hd]
    constructor <;> omega
  · rw [hd]
    constructor <;> omega

/-- 位置好集:前缀 m 的位置(≤8 精确回摆;≥8 区间扩张)。 -/
def inGoodPos (p : ℤ) (m : ℕ) (x : ℤ) : Prop :=
  (m ≤ 8 → x = 4 * p + delta8 m) ∧
  (8 ≤ m → x ∈ Set.Icc (4 * p - ((m - 8 : ℕ) : ℤ)) (4 * p + ((m - 8 : ℕ) : ℤ)))

/-- 步的 fromState q ≠ 101(nontrap 的转移在非 101 态)。 -/
lemma step_fromState_q_ne101 {st : ℕ} {s : F4} {r : CBTMTransResult}
    (hr : r ∈ transition4 st s) (hnt : (decodeState r.nextState).1 ≠ 101) :
    (decodeState st).1 ≠ 101 := by
  intro hq
  apply hnt
  exact transition4_trap_q101 st s r hq hr

/-- 12 步段内路径(长度 ≤ 12)终点位置的好集断言(归纳核心)。 -/
lemma tapeSteps12_len_pos {w : List F4} {cfgc0 cfg : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {p : ℤ} {q : ℕ}
    (h : TapeSteps subsetSumCBTM w cfgc0 π cfg)
    (hlen : π.length ≤ 12)
    (hq0 : cfgc0.state = encodeState q 0 0)
    (hp0 : cfgc0.headPos = 4 * p)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    inGoodPos p π.length cfg.headPos := by
  induction h with
  | nil =>
      constructor
      · intro hm
        simp [hp0, delta8]
      · intro hm
        simp at hm
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hlen₀ : π₀.length ≤ 12 := by
        simp [List.length_append] at hlen
        omega
      have htrap₀ : ∀ k (hk : k < π₀.length),
          (decodeState (π₀.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
        intro k hk
        have hk' : k < (π₀ ++ [step]).length := by
          simp
          omega
        have hg : (π₀ ++ [step]).get ⟨k, hk'⟩ = π₀.get ⟨k, hk⟩ := List.getElem_append_left hk
        have ht' : (decodeState (π₀.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
          rw [← hg]
          exact htrap k hk'
        exact ht'
      have hpos₁ : inGoodPos p π₀.length cfg₁.headPos := by
        exact ih hlen₀ htrap₀
      -- 当前步的相位 = π₀.length(≤ 11)
      have hph : (decodeState cfg₁.state).2.1 = π₀.length := by
        have hpa := (tapeSteps_phase_at hprev hq0).1.1
        rw [hpa]
        have hlt : π₀.length % 12 = π₀.length := Nat.mod_eq_of_lt (by
          simp [List.length_append] at hlen
          omega)
        rw [hlt]
      have htrans' : step.result ∈ transition4 cfg₁.state step.readSym := by
        rw [hread]
        exact htrans
      have hnt : (decodeState step.result.nextState).1 ≠ 101 := by
        have hm' : π₀.length < (π₀ ++ [step]).length := by
          simp
        have hg' : (π₀ ++ [step]).get ⟨π₀.length, hm'⟩ = step := by
          simp
        have ht : (decodeState ((π₀ ++ [step]).get ⟨π₀.length, hm'⟩).result.nextState).1 ≠ 101 :=
          htrap π₀.length hm'
        rw [hg'] at ht
        exact ht
      have hne101q : (decodeState cfg₁.state).1 ≠ 101 :=
        step_fromState_q_ne101 htrans' hnt
      have hhh : (stepConfig cfg₁ step.result).headPos = cfg₁.headPos + step.result.moveDir.toInt := by
        simp [stepConfig]
      rw [hhh]
      -- 分 π₀.length ≤ 7 与 8 ≤ π₀.length
      by_cases h8 : π₀.length ≤ 7
      · -- 回摆段:位置 = 4p + delta8 m₀(ih 的 ≤8 支);dir 分类;delta8_step
        have hpos₁' := hpos₁.1 (by omega)
        rw [hpos₁']
        have hle : (decodeState cfg₁.state).2.1 ≤ 7 := by omega
        rcases (le_or_gt (decodeState cfg₁.state).2.1 2) with hlt2 | hge3
        · have hd : step.result.moveDir = Dir.R :=
            step_dir_phase_lt3 cfg₁.state step.readSym step.result htrans'
              (by omega) hnt
          rw [hd]
          simp [Dir.toInt]
          constructor
          · intro hm1
            have hstep := delta8_step π₀.length (by omega) 1
              (by intro; rfl)
              (by intro hm3 hm5; exfalso; omega)
              (by intro hm6; exfalso; omega)
            rw [← hstep]
            simp [add_assoc]
          · intro hm1
            exfalso
            omega
        · rcases (le_or_gt (decodeState cfg₁.state).2.1 5) with hlt5 | hge6
          · have hd : step.result.moveDir = Dir.L :=
              step_dir_phase3_5 cfg₁.state step.readSym step.result htrans'
                (by omega) (by omega) hnt
            rw [hd]
            simp [Dir.toInt]
            constructor
            · intro hm1
              have hstep := delta8_step π₀.length (by omega) (-1)
                (by intro hm2; exfalso; omega)
                (by intro hm3 hm5; rfl)
                (by intro hm6; exfalso; omega)
              rw [← hstep]
              simp [add_assoc]
            · intro hm1
              exfalso
              omega
          · have hd : step.result.moveDir = Dir.S :=
              step_dir_phase6_7 cfg₁.state step.readSym step.result htrans'
                (by omega) hnt
            rw [hd]
            simp [Dir.toInt]
            constructor
            · intro hm1
              have hstep := delta8_step π₀.length (by omega) 0
                (by intro hm2; exfalso; omega)
                (by intro hm3 hm5; exfalso; omega)
                (by intro; rfl)
              rw [← hstep]
              simp []
            · intro hm1
              have hm7 : π₀.length = 7 := by omega
              have hx7 : 4 * p + delta8 π₀.length = 4 * p := by
                simp [delta8, hm7]
              rw [hx7]
              simp [Set.Icc, hm7]
      · -- 漂移段:8 ≤ π₀.length;位置区间;±1 扩张
        have h8' : 8 ≤ π₀.length := by omega
        have h8b : 8 ≤ π₀.length := h8'
        have hdir : step.result.moveDir.toInt = 1 ∨ step.result.moveDir.toInt = 0 ∨
            step.result.moveDir.toInt = -1 :=
          step_dir_phase_ge8 cfg₁.state step.readSym step.result htrans'
            (by rw [hph]; exact h8') (by rw [hph]; simp [List.length_append] at hlen; omega) hnt hne101q
        rcases hpos₁.2 h8b with ⟨hlo₁, hhi₁⟩
        have hdrift : cfg₁.headPos + step.result.moveDir.toInt ∈ Set.Icc (4 * p - (((π₀.length + 1) - 8 : ℕ) : ℤ)) (4 * p + (((π₀.length + 1) - 8 : ℕ) : ℤ)) := by
          rcases hdir with hd | hd | hd
          · rw [hd]
            constructor <;> omega
          · rw [hd]
            constructor <;> omega
          · rw [hd]
            constructor <;> omega
        constructor
        · intro hm1
          exfalso
          have hm1' : π₀.length.succ ≤ 8 := by simpa [Nat.succ_eq_add_one] using hm1
          exact (not_lt_of_ge h8') (Nat.lt_of_succ_le hm1')
        · intro hm1
          simpa using hdrift

/-- 12 步段内每前缀(含终点)headPos ∈ [4p-4, 4p+4]。 -/
lemma tapeSteps12_headPos_inside {w : List F4} {cfgc0 cfgc' : CBTMConfig subsetSumCBTM w}
    {πb : ComputationPath} {p : ℤ} {q : ℕ}
    (hb : TapeSteps subsetSumCBTM w cfgc0 πb cfgc')
    (hlen : πb.length = 12)
    (hq0 : cfgc0.state = encodeState q 0 0)
    (hp0 : cfgc0.headPos = 4 * p)
    (htrap : ∀ k (hk : k < πb.length), (decodeState (πb.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    (∀ m (_hm : m < πb.length),
      ∃ cfgm : CBTMConfig subsetSumCBTM w,
        TapeSteps subsetSumCBTM w cfgc0 (πb.take m) cfgm ∧
        cfgm.headPos ∈ Set.Icc (4 * p - 4) (4 * p + 4)) ∧
    cfgc'.headPos ∈ Set.Icc (4 * p - 4) (4 * p + 4) := by
  have hlen' : πb.length ≤ 12 := by omega
  constructor
  · intro m hm
    rcases tapeSteps_prefix_end hb m (by omega) with ⟨cfgm, hpfx⟩
    refine ⟨cfgm, hpfx, ?_⟩
    have hlenm : (πb.take m).length ≤ 12 := by
      simp [List.length_take]
      omega
    have htrm : ∀ k (hk : k < (πb.take m).length), (decodeState ((πb.take m).get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
      intro k hk
      have hk' : k < πb.length := by
        have : (πb.take m).length ≤ πb.length := by simp [List.length_take]
        omega
      have hg : (πb.take m).get ⟨k, hk⟩ = πb.get ⟨k, hk'⟩ := by
        simp [List.getElem_take]
      rw [hg]
      exact htrap k hk'
    have hpos := tapeSteps12_len_pos hpfx hlenm hq0 hp0 htrm
    by_cases hle8 : m ≤ 8
    · -- 回摆:位置 = 4p + delta8 m,delta8 m ∈ [0,4]
      have htm : (πb.take m).length ≤ 8 := by simp [List.length_take]; omega
      have htl : (πb.take m).length = m := by
        simp [List.length_take, Nat.min_eq_left (le_of_lt hm)]
      have hx : cfgm.headPos = 4 * p + delta8 m := by
        rw [hpos.1 htm]
        rw [htl]
      have hd : 0 ≤ delta8 m ∧ delta8 m ≤ 4 := by
        unfold delta8
        split_ifs <;> omega
      rw [hx]
      constructor <;> omega
    · -- 漂移:m ≥ 8,区间 [4p-(m-8), 4p+(m-8)] ⊆ [4p-4, 4p+4]
      have hm8' : 8 ≤ m := by omega
      have htm8 : 8 ≤ (πb.take m).length := by simp [List.length_take]; omega
      have htl : (πb.take m).length = m := by
        simp [List.length_take, Nat.min_eq_left (le_of_lt hm)]
      rcases hpos.2 htm8 with ⟨hlo₂, hhi₂⟩
      rw [htl] at hlo₂ hhi₂
      have hm8n : m - 8 ≤ 4 := by omega
      have hm8z : ((m - 8 : ℕ) : ℤ) ≤ 4 := by exact_mod_cast hm8n
      constructor
      · -- 4p-4 ≤ cfgm.headPos:由 hlo₂(4p-(m-8) ≤ x)与 -(m-8) ≥ -4
        omega
      · omega
  · -- 终点
    have hpos' := tapeSteps12_len_pos hb hlen' hq0 hp0 htrap
    have h12 : 8 ≤ πb.length := by omega
    rcases hpos'.2 h12 with ⟨hlo₂, hhi₂⟩
    have hm8n : πb.length - 8 ≤ 4 := by omega
    have hm8z : ((πb.length - 8 : ℕ) : ℤ) ≤ 4 := by exact_mod_cast hm8n
    constructor <;> omega
end Mp
