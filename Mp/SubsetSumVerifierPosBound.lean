/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

/-
# q10 ① 位置界装配（T4-T6，canonical_pos_bound）

NTM2.Canonical ①（收窄版）对 A = subsetSumNTM2：
∀ x π cfg 合法（∃ inst g', x = encodeInstanceF4 inst ++ g'）→ hnoTerm → 可达 → 可延拓到
acceptStates4 → ∀ step ∈ π: 0 ≤ step.pos ∧ step.pos ≤ |x| ∧ 0 ≤ 步后 ∧ 步后 ≤ |x|。

装配链（f4-block-inner-pos 参考）：
  可延拓 π → CBTM 镜像（无 hcan 的 iso_path_forward 副本）→ 接受全长 accept_path_no_trap
  → accept_path_is_good_block_path（g' = [] 情形）→ project_path_gen →
  r7_accept_path_prefix_inside（块首 p < L'）→ 块内相位表（12 步 ∈ [4p-4, 4p+4]）→
  每步 pos ∈ [0, 4L'] ⊆ [0, |x|]。
g' ≠ [] 的推广：4|wS| ≤ |w| 论证（no_trap 路线的 wS 截断 + flat4F4 前缀唯一），第二里程碑。
-/

import Mp.Basic
import Mp.CBTM
import Mp.IVM
import Mp.SubsetSumVerifierCBTM
import Mp.SubsetSumCompile
import Mp.A2Bridge
import Mp.SubsetSumVerifierCBTM4
import Mp.SubsetSumVerifierCBTM6
import Mp.SubsetSumVerifierReverse5
import Mp.SubsetSumVerifierReverse7L3
import Mp.SubsetSumVerifierReverse10
import Mp.SubsetSumReal

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
open SymToF4

/-! A-1 镜像件(吸收自 _probe_iso.lean):NTM2↔CBTM 结构同构实例。 -/
namespace SymToF4

-- φ:F4 → alphabet 子类型(恒等;alphabet = 全集)
noncomputable def isoPhi : F4 ≃ {s : F4 // s ∈ subsetSumCBTM.alphabet} where
  toFun := fun s => ⟨s, by
    rcases s with ⟨b1, b2⟩
    fin_cases b1 <;> fin_cases b2 <;>
      simp [subsetSumCBTM, F4.zero, F4.one, F4.alpha, F4.beta, Finset.mem_insert]⟩
  invFun := fun s => s.val
  left_inv := by intro s; rfl
  right_inv := by intro s; rcases s with ⟨s, hs⟩; rfl

/-- transition 的位置无关性(subsetSumCBTM.transition 忽略 pos)。 -/
lemma subsetSumCBTM_transition_pos_indep (q : ℕ) (s : F4) (i : ℤ) :
    subsetSumCBTM.transition (q, s, i) = transition4 q s := by
  rfl

/-- h_transition 的核心:NTM2 化后镜像回 CBTM 转移(翻译往返恒等 + 位置无关)。 -/
lemma iso_transition_core (q : ℕ) (s : F4) (i : ℤ) :
    subsetSumCBTM.transition (q, s, i) =
      (subsetSumNTM2.transition (q, s, i)).image ntm2ResultToCBTM := by
  rw [subsetSumCBTM_transition_pos_indep]
  unfold subsetSumNTM2
  dsimp
  rw [Finset.image_image]
  have hcomp : ntm2ResultToCBTM ∘ cbtmResultToTriple = id := by
    funext r
    exact ntm2ResultToCBTM_comp_cbtmResultToTriple r
  rw [hcomp]
  simp
  rw [subsetSumCBTM_transition_pos_indep]

-- 完整 iso
noncomputable def subsetSumIso : StructIsoNTM2CBTM subsetSumNTM2 subsetSumCBTM where
  h_states_eq := rfl
  h_start := rfl
  h_accept := rfl
  h_reject := rfl
  φ_symbol := isoPhi
  h_φ_id := by intro s; rfl
  h_blank := rfl
  h_transition := by
    intro q s i hs
    change subsetSumCBTM.transition (q, s, i) =
      (subsetSumNTM2.transition (q, s, i)).image ntm2ResultToCBTM
    exact iso_transition_core q s i

/-- ①线 A-1 镜像件需要的实例(经 iso_path_forward_noCan / iso_path_backward 使用)。 -/
theorem subsetSumIsoNonempty : Nonempty (StructIsoNTM2CBTM subsetSumNTM2 subsetSumCBTM) :=
  ⟨subsetSumIso⟩


/-! A-1 装配核心件(吸收自 _probe_a1.lean):单块内前缀头界 + GoodBlockPath 装配骨架。
   F4 层「步位置」= 步前 cfg.headPos(TapeSteps cons:readSym = cfg'.tapeAt cfg'.headPos)。 -/

/-- 单块内(含终点)每前缀 cfg 头 ∈ [0, 4p+4](块首头 = 4p,p ≥ 1)。
    ← tapeSteps12_headPos_inside 的 [4p-4, 4p+4] + p ≥ 1 收紧下界。 -/
lemma a1_block_head_bounds {w : List F4} {cfgc0 cfgc' : CBTMConfig subsetSumCBTM w}
    {πb : ComputationPath} {p : ℤ} {q : ℕ}
    (hb : TapeSteps subsetSumCBTM w cfgc0 πb cfgc')
    (hlen : πb.length = 12)
    (hq0 : cfgc0.state = encodeState q 0 0)
    (hp0 : cfgc0.headPos = 4 * p)
    (htrap : ∀ k (hk : k < πb.length), (decodeState (πb.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (hplo : p ≥ 1) :
    (∀ m (hm : m ≤ πb.length), ∃ cfgm : CBTMConfig subsetSumCBTM w,
        TapeSteps subsetSumCBTM w cfgc0 (πb.take m) cfgm ∧
        cfgm.headPos ∈ Set.Icc 0 (4 * p + 4)) ∧
    cfgc'.headPos ∈ Set.Icc 0 (4 * p + 4) := by
  have h4 : 0 ≤ 4 * p - 4 := by omega
  have hinside := tapeSteps12_headPos_inside hb hlen hq0 hp0 htrap
  constructor
  · intro m hm
    by_cases hml : m < πb.length
    · rcases hinside.1 m hml with ⟨cfgm, hpfx, hIcc⟩
      refine ⟨cfgm, hpfx, ?_⟩
      rcases hIcc with ⟨hlo, hhi⟩
      constructor
      · omega
      · simpa using hhi
    · have hm' : m = πb.length := by omega
      subst m
      rw [List.take_length]
      refine ⟨cfgc', hb, ?_⟩
      rcases hinside.2 with ⟨hlo, hhi⟩
      constructor
      · omega
      · simpa using hhi
  · rcases hinside.2 with ⟨hlo, hhi⟩
    constructor <;> omega

/-- 装配骨架(演示):GoodBlockPath 上逐块调用核心件。
    块首 p 的来源(接口,由 A-3 提供):
      · 块首 headPos = 4p(GoodBlock 参数,rfl 用 hp0)
      · p ≥ 1:初始块(头 0,态 0,读 #ₗ,R)之后每块 p ≥ 1 —— 由布局/状态串行 + A-3 左界
      · p ≤ L'-1:r7_accept_path_prefix_inside(Sym 头 < L')镜像
    骨架尾部为 A 待填的 p 界来源(标注)。 -/
lemma a1_blockpath_skel {w : List F4} {π : ComputationPath}
    {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    (hbp : GoodBlockPath w cfgc π cfgc') : True := by
  trivial


end SymToF4

/-!
# §1 镜像件（现成，勿重造）
- `iso_path_forward_noCan`（Reverse10:28）：TapeReachablePathNTM2 → TapeReachablePath，
  无 Canonical 前提（证明体不用 hcan），cfg' = 镜像 cfg。
- 延拓拼接：`ntm2TapeSteps_append`（A2Bridge:219 区）/ `tapeSteps_append`。
- 空延拓包装：⟨[], cfg', by simpa using hrc', hacc⟩（tape-steps-extend 参考 §3）。
-/
/-!
# §2 T6a：块内 12 步位置界（tapeSteps12_headPos_inside）

相位表（transition4，CBTM:207）：相位 0-2 读 R、3 合成 L、4-5 写回 L、6-7 S、
8-11 移动段（每步方向 ∈ {±1,0}）。前缀偏移 Δ_j = Σ_{i<j} dir_i ∈ {0,1,2,3,2,1,0,0}（j≤8）
∪ {Σd}（j≥9）⇒ 每前缀头 ∈ [4p-4, 4p+4]。
-/

/-- 块内每前缀头的位置界：块首态 = encodeState q 0 0、头 = 4p、12 步无陷阱 ⇒
    每个 j ≤ 12 的前缀终点头 ∈ [4p-4, 4p+4]。 -/
lemma block12_prefix_pos_inside {w : List F4} {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {p : ℤ} {q : ℕ}
    (h : TapeSteps subsetSumCBTM w cfgc π cfgc')
    (hlen : π.length = 12)
    (hq0 : cfgc.state = encodeState q 0 0)
    (hp : cfgc.headPos = 4 * p)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∀ j : ℕ, j ≤ 12 →
      ∃ cfgj : CBTMConfig subsetSumCBTM w,
        TapeSteps subsetSumCBTM w cfgc (π.take j) cfgj ∧
        4 * p - 4 ≤ cfgj.headPos ∧ cfgj.headPos ≤ 4 * p + 4 := by
  intro j hj
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
      intro h0'
      have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h0'] at this) with
    ⟨step0, πn, cfg0, hπe0, hn, hf0, hr0, ht0, hc0⟩
  have hπall : π = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
    rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0]
    simp
  have hlen_n : πn.length = 0 := by
    have := congrArg List.length hπall
    simp at this
    omega
  have hπn0 : πn = [] := List.eq_nil_of_length_eq_zero hlen_n
  have hcfg0 : cfg0 = cfgc := by
    subst hπn0
    exact tapeSteps_empty hn rfl
  have hph_all := tapeSteps_phase_at h hq0
  have hnt0 : (decodeState step0.result.nextState).1 ≠ 101 := by
    have hh := htrap 0 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt1 : (decodeState step1.result.nextState).1 ≠ 101 := by
    have hh := htrap 1 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt2 : (decodeState step2.result.nextState).1 ≠ 101 := by
    have hh := htrap 2 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt3 : (decodeState step3.result.nextState).1 ≠ 101 := by
    have hh := htrap 3 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt4 : (decodeState step4.result.nextState).1 ≠ 101 := by
    have hh := htrap 4 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt5 : (decodeState step5.result.nextState).1 ≠ 101 := by
    have hh := htrap 5 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt6 : (decodeState step6.result.nextState).1 ≠ 101 := by
    have hh := htrap 6 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt7 : (decodeState step7.result.nextState).1 ≠ 101 := by
    have hh := htrap 7 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt8 : (decodeState step8.result.nextState).1 ≠ 101 := by
    have hh := htrap 8 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt9 : (decodeState step9.result.nextState).1 ≠ 101 := by
    have hh := htrap 9 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt10 : (decodeState step10.result.nextState).1 ≠ 101 := by
    have hh := htrap 10 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hnt11 : (decodeState step11.result.nextState).1 ≠ 101 := by
    have hh := htrap 11 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa [hπall, hlen_n] using hh
  have hph0 : (decodeState step0.fromState).2.1 = 0 := by
    have hh := (hph_all.2 0 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph1 : (decodeState step1.fromState).2.1 = 1 := by
    have hh := (hph_all.2 1 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph2 : (decodeState step2.fromState).2.1 = 2 := by
    have hh := (hph_all.2 2 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph3 : (decodeState step3.fromState).2.1 = 3 := by
    have hh := (hph_all.2 3 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph4 : (decodeState step4.fromState).2.1 = 4 := by
    have hh := (hph_all.2 4 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph5 : (decodeState step5.fromState).2.1 = 5 := by
    have hh := (hph_all.2 5 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph6 : (decodeState step6.fromState).2.1 = 6 := by
    have hh := (hph_all.2 6 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph7 : (decodeState step7.fromState).2.1 = 7 := by
    have hh := (hph_all.2 7 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph8 : (decodeState step8.fromState).2.1 = 8 := by
    have hh := (hph_all.2 8 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph9 : (decodeState step9.fromState).2.1 = 9 := by
    have hh := (hph_all.2 9 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph10 : (decodeState step10.fromState).2.1 = 10 := by
    have hh := (hph_all.2 10 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have hph11 : (decodeState step11.fromState).2.1 = 11 := by
    have hh := (hph_all.2 11 (by rw [hπall]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)).1
    simpa [hπall, hlen_n] using hh
  have ht0' : step0.result ∈ transition4 step0.fromState step0.readSym := by
    rw [hf0, hr0]
    simpa [subsetSumCBTM] using ht0
  have ht1' : step1.result ∈ transition4 step1.fromState step1.readSym := by
    rw [hf1, hr1]
    simpa [subsetSumCBTM] using ht1
  have ht2' : step2.result ∈ transition4 step2.fromState step2.readSym := by
    rw [hf2, hr2]
    simpa [subsetSumCBTM] using ht2
  have ht3' : step3.result ∈ transition4 step3.fromState step3.readSym := by
    rw [hf3, hr3]
    simpa [subsetSumCBTM] using ht3
  have ht4' : step4.result ∈ transition4 step4.fromState step4.readSym := by
    rw [hf4, hr4]
    simpa [subsetSumCBTM] using ht4
  have ht5' : step5.result ∈ transition4 step5.fromState step5.readSym := by
    rw [hf5, hr5]
    simpa [subsetSumCBTM] using ht5
  have ht6' : step6.result ∈ transition4 step6.fromState step6.readSym := by
    rw [hf6, hr6]
    simpa [subsetSumCBTM] using ht6
  have ht7' : step7.result ∈ transition4 step7.fromState step7.readSym := by
    rw [hf7, hr7]
    simpa [subsetSumCBTM] using ht7
  have ht8' : step8.result ∈ transition4 step8.fromState step8.readSym := by
    rw [hf8, hr8]
    simpa [subsetSumCBTM] using ht8
  have ht9' : step9.result ∈ transition4 step9.fromState step9.readSym := by
    rw [hf9, hr9]
    simpa [subsetSumCBTM] using ht9
  have ht10' : step10.result ∈ transition4 step10.fromState step10.readSym := by
    rw [hf10, hr10]
    simpa [subsetSumCBTM] using ht10
  have ht11' : step11.result ∈ transition4 step11.fromState step11.readSym := by
    rw [hf11, hr11]
    simpa [subsetSumCBTM] using ht11
  have hdir0 : step0.result.moveDir = Dir.R :=
    step_dir_phase_lt3 step0.fromState step0.readSym step0.result ht0' (by rw [hph0]; omega) hnt0
  have hdir1 : step1.result.moveDir = Dir.R :=
    step_dir_phase_lt3 step1.fromState step1.readSym step1.result ht1' (by rw [hph1]; omega) hnt1
  have hdir2 : step2.result.moveDir = Dir.R :=
    step_dir_phase_lt3 step2.fromState step2.readSym step2.result ht2' (by rw [hph2]; omega) hnt2
  have hdir3 : step3.result.moveDir = Dir.L :=
    step_dir_phase3_5 step3.fromState step3.readSym step3.result ht3' (by omega) (by omega) hnt3
  have hdir4 : step4.result.moveDir = Dir.L :=
    step_dir_phase3_5 step4.fromState step4.readSym step4.result ht4' (by omega) (by omega) hnt4
  have hdir5 : step5.result.moveDir = Dir.L :=
    step_dir_phase3_5 step5.fromState step5.readSym step5.result ht5' (by omega) (by omega) hnt5
  have hdir6 : step6.result.moveDir = Dir.S :=
    step_dir_phase6_7 step6.fromState step6.readSym step6.result ht6' (by left; rw [hph6]) hnt6
  have hdir7 : step7.result.moveDir = Dir.S :=
    step_dir_phase6_7 step7.fromState step7.readSym step7.result ht7' (by right; rw [hph7]) hnt7
  have hq101_8 : (decodeState step8.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt8 (transition4_trap_q101 _ _ _ hqj ht8')
  have hdir8 : step8.result.moveDir.toInt = 1 ∨ step8.result.moveDir.toInt = 0 ∨
      step8.result.moveDir.toInt = -1 :=
    step_dir_phase_ge8 step8.fromState step8.readSym step8.result ht8' (by omega) (by omega) hnt8 hq101_8
  have hq101_9 : (decodeState step9.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt9 (transition4_trap_q101 _ _ _ hqj ht9')
  have hdir9 : step9.result.moveDir.toInt = 1 ∨ step9.result.moveDir.toInt = 0 ∨
      step9.result.moveDir.toInt = -1 :=
    step_dir_phase_ge8 step9.fromState step9.readSym step9.result ht9' (by omega) (by omega) hnt9 hq101_9
  have hq101_10 : (decodeState step10.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt10 (transition4_trap_q101 _ _ _ hqj ht10')
  have hdir10 : step10.result.moveDir.toInt = 1 ∨ step10.result.moveDir.toInt = 0 ∨
      step10.result.moveDir.toInt = -1 :=
    step_dir_phase_ge8 step10.fromState step10.readSym step10.result ht10' (by omega) (by omega) hnt10 hq101_10
  have hq101_11 : (decodeState step11.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt11 (transition4_trap_q101 _ _ _ hqj ht11')
  have hdir11 : step11.result.moveDir.toInt = 1 ∨ step11.result.moveDir.toInt = 0 ∨
      step11.result.moveDir.toInt = -1 :=
    step_dir_phase_ge8 step11.fromState step11.readSym step11.result ht11' (by omega) (by omega) hnt11 hq101_11
  have hhead0 : cfg1.headPos = cfg0.headPos + step0.result.moveDir.toInt := by
    rw [hc0]
    simp [stepConfig]
  have hhead1 : cfg2.headPos = cfg1.headPos + step1.result.moveDir.toInt := by
    rw [hc1]
    simp [stepConfig]
  have hhead2 : cfg3.headPos = cfg2.headPos + step2.result.moveDir.toInt := by
    rw [hc2]
    simp [stepConfig]
  have hhead3 : cfg4.headPos = cfg3.headPos + step3.result.moveDir.toInt := by
    rw [hc3]
    simp [stepConfig]
  have hhead4 : cfg5.headPos = cfg4.headPos + step4.result.moveDir.toInt := by
    rw [hc4]
    simp [stepConfig]
  have hhead5 : cfg6.headPos = cfg5.headPos + step5.result.moveDir.toInt := by
    rw [hc5]
    simp [stepConfig]
  have hhead6 : cfg7.headPos = cfg6.headPos + step6.result.moveDir.toInt := by
    rw [hc6]
    simp [stepConfig]
  have hhead7 : cfg8.headPos = cfg7.headPos + step7.result.moveDir.toInt := by
    rw [hc7]
    simp [stepConfig]
  have hhead8 : cfg9.headPos = cfg8.headPos + step8.result.moveDir.toInt := by
    rw [hc8]
    simp [stepConfig]
  have hhead9 : cfg10.headPos = cfg9.headPos + step9.result.moveDir.toInt := by
    rw [hc9]
    simp [stepConfig]
  have hhead10 : cfg11.headPos = cfg10.headPos + step10.result.moveDir.toInt := by
    rw [hc10]
    simp [stepConfig]
  have hhead11 : cfgc'.headPos = cfg11.headPos + step11.result.moveDir.toInt := by
    rw [hc11]
    simp [stepConfig]
  interval_cases j
  · refine ⟨cfgc, ?_, ?_⟩
    · exact TapeSteps.nil
    · rw [hp]
      omega
  · refine ⟨cfg1, ?_, ?_⟩
    · have htake : π.take 1 = πn ++ [step0] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe0] using h0
    · rw [hhead0, hcfg0, hp, hdir0]
      norm_num [Dir.toInt]
      omega
  · refine ⟨cfg2, ?_, ?_⟩
    · have htake : π.take 2 = πn ++ [step0, step1] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe1, hπe0] using h1
    · rw [hhead1, hhead0, hcfg0, hp, hdir1, hdir0]
      norm_num [Dir.toInt]
      omega
  · refine ⟨cfg3, ?_, ?_⟩
    · have htake : π.take 3 = πn ++ [step0, step1, step2] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe2, hπe1, hπe0] using h2
    · rw [hhead2, hhead1, hhead0, hcfg0, hp, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
      omega
  · refine ⟨cfg4, ?_, ?_⟩
    · have htake : π.take 4 = πn ++ [step0, step1, step2, step3] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe3, hπe2, hπe1, hπe0] using h3
    · rw [hhead3, hhead2, hhead1, hhead0, hcfg0, hp, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
      omega
  · refine ⟨cfg5, ?_, ?_⟩
    · have htake : π.take 5 = πn ++ [step0, step1, step2, step3, step4] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe4, hπe3, hπe2, hπe1, hπe0] using h4
    · rw [hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
      omega
  · refine ⟨cfg6, ?_, ?_⟩
    · have htake : π.take 6 = πn ++ [step0, step1, step2, step3, step4, step5] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h5
    · rw [hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg7, ?_, ?_⟩
    · have htake : π.take 7 = πn ++ [step0, step1, step2, step3, step4, step5, step6] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h6
    · rw [hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg8, ?_, ?_⟩
    · have htake : π.take 8 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h7
    · rw [hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp, hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg9, ?_, ?_⟩
    · have htake : π.take 9 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h8
    · rw [hhead8, hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp,
        hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      rcases hdir8 with h8 | h8 | h8 <;> rw [h8] <;> norm_num [Dir.toInt] <;> omega
  · refine ⟨cfg10, ?_, ?_⟩
    · have htake : π.take 10 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h9
    · rw [hhead9, hhead8, hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp,
        hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      rcases hdir8 with h8 | h8 | h8 <;> rw [h8] <;>
        rcases hdir9 with h9 | h9 | h9 <;> rw [h9] <;> norm_num [Dir.toInt] <;> omega
  · refine ⟨cfg11, ?_, ?_⟩
    · have htake : π.take 11 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h10
    · rw [hhead10, hhead9, hhead8, hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp,
        hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      rcases hdir8 with h8 | h8 | h8 <;> rw [h8] <;>
        rcases hdir9 with h9 | h9 | h9 <;> rw [h9] <;>
        rcases hdir10 with h10 | h10 | h10 <;> rw [h10] <;> norm_num [Dir.toInt] <;> omega
  · refine ⟨cfgc', ?_, ?_⟩
    · have htake : π.take 12 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      rw [htake]
      rw [← hπall]
      exact h
    · rw [hhead11, hhead10, hhead9, hhead8, hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp,
        hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      rcases hdir8 with h8 | h8 | h8 <;> rw [h8] <;>
        rcases hdir9 with h9 | h9 | h9 <;> rw [h9] <;>
        rcases hdir10 with h10 | h10 | h10 <;> rw [h10] <;>
        rcases hdir11 with h11 | h11 | h11 <;> rw [h11] <;> norm_num [Dir.toInt] <;> omega

/-!
# §3 T6.3/T6.4 桥：好块路径 → Sym 路径 + 逐块头对应

project_path_gen（CBTM3:1810）骨架 + 附加分量：每个 k ≤ πs.length，
块 k 首（π.take (12k) 终点）的头 = 4 ×（πs.take k 终点）的头。
-/

/-- 好块路径投影 + 块首头对应：第 k 块首 F4 头 = 4 × Sym 前缀头。 -/
lemma good_block_path_head_corresp (w : List F4) (input : List Sym)
    (cfgc : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (π : ComputationPath)
    (cfgc' : CBTMConfig subsetSumCBTM w)
    (hcorr : blockCorrespond cfgc cfgs)
    (hbp : GoodBlockPath w cfgc π cfgc')
    (hno101 : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∃ πs : List SymStep, ∃ cfgs' : SymConfig,
      SymSteps VerifierSym.transition cfgs πs cfgs' ∧
      blockCorrespond cfgc' cfgs' ∧ πs.length * 12 = π.length ∧
      ∀ k : ℕ, k ≤ πs.length →
        ∃ cfgsm : SymConfig, ∃ cfgcm : CBTMConfig subsetSumCBTM w,
          SymSteps VerifierSym.transition cfgs (πs.take k) cfgsm ∧
          TapeSteps subsetSumCBTM w cfgc (π.take (12 * k)) cfgcm ∧
          cfgcm.headPos = 4 * cfgsm.headPos ∧
          cfgcm.state = encodeState cfgsm.state 0 0 := by
  induction hbp generalizing cfgs with
  | nil cfgc =>
      refine ⟨[], cfgs, SymSteps.nil, hcorr, rfl, ?_⟩
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      refine ⟨cfgs, cfgc, SymSteps.nil, TapeSteps.nil, hcorr.2.1, hcorr.1⟩
  | cons cfgc cfgm cfgc' πm π cfgsb p q sym r hblock htail ih =>
      have hproj : blockCorrespond cfgm (symStepConfig cfgsb r) := by
        have hrs : r.nextState < 101 := by
          rcases hblock with
            ⟨hpath, hlenm, hst, hp, hcorrB, hread, hq, hbranch, hvalid, hstep4, hmk, hr, hst', hhead'⟩
          have hle : r.nextState ≤ 101 := transition_nextState_le101 q sym hq r hr
          have hne : r.nextState ≠ 101 := by
            intro h101
            have hnt := hno101 3 (by
              have hlenm' : πm.length = 12 := hlenm
              simp [List.length_append] at *
              omega)
            have hget : (πm ++ π).get ⟨3, by
                have hlenm' : πm.length = 12 := hlenm
                simp [List.length_append] at *
                omega⟩ = πm.get ⟨3, by omega⟩ := by
              apply List.getElem_append_left
            have hregok : encodeResult r < 8192 := by
              dsimp [encodeResult]
              have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
                rcases r.writeSym with ⟨k, mk⟩
                cases k <;> cases mk <;> simp [skOf]
              have hdir : dirOf r.moveDir < 3 := by
                cases r.moveDir <;> simp [dirOf]
              omega
            have hdec : decodeState (encodeState r.nextState 4 (encodeResult r)) = (r.nextState, 4, encodeResult r) := by
              exact decodeState_encodeState r.nextState 4 (encodeResult r) (by norm_num) hregok
            have hnt' : r.nextState ≠ 101 := by
              intro h
              apply hnt
              change (decodeState ((πm ++ π)[3]'(by
                have hlenm' : πm.length = 12 := hlenm
                simp [List.length_append] at *
                omega)).result.nextState).1 = 101
              rw [List.getElem_append_left (show 3 < πm.length from by
                have hlenm' : πm.length = 12 := hlenm
                omega)]
              change (decodeState (List.get πm ⟨3, by omega⟩).result.nextState).1 = 101
              rw [hstep4]
              dsimp
              rw [hdec]
              simp [h]
            exact hnt' h101
          omega
        exact project_block w cfgc πm cfgm cfgsb p q sym r hblock hrs
      have hlenm0 : πm.length = 12 := by
        rcases hblock with ⟨_, hlenm, _⟩
        exact hlenm
      have hno101_tail : ∀ k (hk : k < π.length),
          (decodeState ((π.get ⟨k, hk⟩).result.nextState)).1 ≠ 101 := by
        intro k hk
        have hk' : πm.length + k < (πm ++ π).length := by
          simp [List.length_append, hlenm0, hk]
        have hget : (πm ++ π).get ⟨πm.length + k, hk'⟩ = π.get ⟨k, hk⟩ := by
          change (πm ++ π)[πm.length + k] = π[k]
          rw [List.getElem_append_right (by omega)]
          simp [Nat.add_sub_cancel]
        have hnt := hno101 (πm.length + k) hk'
        rwa [hget] at hnt
      rcases ih (symStepConfig cfgsb r) hproj hno101_tail with
        ⟨πs, cfgs', hsteps, hcorr', hlen, hcorr_k⟩
      rcases hblock with
        ⟨hpath, hlenm, hst, hp, hcorrB, hread, hq, hbranch, hvalid, hstep4, hmk, hr, hst', hhead'⟩
      have hstate : cfgs.state = cfgsb.state := by
        have heq : encodeState cfgs.state 0 0 = encodeState cfgsb.state 0 0 := by
          rw [← hcorr.1, hcorrB.1]
        have hdec := congrArg decodeState heq
        rw [decodeState_encodeState cfgs.state 0 0 (by norm_num) (by norm_num),
          decodeState_encodeState cfgsb.state 0 0 (by norm_num) (by norm_num)] at hdec
        exact congrArg Prod.fst hdec
      have hhead : cfgs.headPos = cfgsb.headPos := by
        have h1 := hcorr.2.1
        have h2 := hcorrB.2.1
        rw [h2] at h1
        nlinarith
      have htape : cfgs.tape = cfgsb.tape := by
        funext i
        apply sym_eq_of_symTo4F4_getD_eq
        intro j hj
        exact (hcorr.2.2 i j hj).symm.trans (hcorrB.2.2 i j hj)
      have hcfgs : cfgs = cfgsb := by
        rcases cfgs with ⟨s1, t1, h1⟩
        rcases cfgsb with ⟨s2, t2, h2⟩
        simp only at *
        subst s1
        subst t1
        subst h1
        rfl
      subst cfgs
      have hstateB : cfgsb.state = q := by
        have heq : encodeState cfgsb.state 0 0 = encodeState q 0 0 := by
          rw [hcorrB.1] at hst
          exact hst
        have hdec := congrArg decodeState heq
        rw [decodeState_encodeState cfgsb.state 0 0 (by norm_num) (by norm_num),
          decodeState_encodeState q 0 0 (by norm_num) (by norm_num)] at hdec
        exact congrArg Prod.fst hdec
      have hheadB : cfgsb.headPos = p := by
        have hh := hcorrB.2.1
        rw [hp] at hh
        nlinarith
      have hreadB : cfgsb.tape cfgsb.headPos = sym := by
        rw [hheadB, hread]
      have htrans : r ∈ VerifierSym.transition (cfgsb.state, cfgsb.tape cfgsb.headPos) := by
        rw [hstateB, hreadB]
        exact hr
      let step : SymStep := SymStep.mk cfgsb.state (cfgsb.tape cfgsb.headPos) r
      have hstep1 : SymSteps VerifierSym.transition cfgsb [step] (symStepConfig cfgsb r) := by
        exact SymSteps.cons [] step cfgsb SymSteps.nil rfl rfl htrans
      refine ⟨[step] ++ πs, cfgs', ?_, hcorr', ?_, ?_⟩
      · exact SymSteps_trans _ _ _ _ _ _ hstep1 hsteps
      · simp only [List.length_append, List.length_cons, List.length_nil]
        nlinarith
      · intro k hk
        by_cases hk0 : k = 0
        · subst hk0
          refine ⟨cfgsb, cfgc, SymSteps.nil, TapeSteps.nil, hcorr.2.1, hcorr.1⟩
        · rcases hcorr_k (k - 1) (by
            have hlenfull : ([step] ++ πs).length = πs.length + 1 := by simp
            rw [hlenfull] at hk
            omega) with ⟨cfgsm, cfgcm, hsm, htm, hcorrk, hstatek⟩
          refine ⟨cfgsm, cfgcm, ?_, ?_, hcorrk, hstatek⟩
          · have htakek : ([step] ++ πs).take k = [step] ++ πs.take (k - 1) := by
              rw [List.take_append]
              have h1 : [step].take k = [step] := by
                rw [List.take_of_length_le (by simp; omega)]
              rw [h1]
              congr 1
            rw [htakek]
            exact SymSteps_trans _ _ _ _ _ _ hstep1 hsm
          · have htakek' : (πm ++ π).take (12 * k) = πm ++ π.take (12 * (k - 1)) := by
              rw [List.take_append]
              have hπm : πm.take (12 * k) = πm := by
                rw [List.take_of_length_le (by rw [hlenm0]; omega)]
              rw [hπm, hlenm0]
              congr 1
              have hsub : 12 * k - 12 = 12 * (k - 1) := by omega
              rw [hsub]
            rw [htakek']
            exact tapeSteps_append hpath htm

/-!
# §4 头非负（Sym 层，接受路径域）

表级：读 boundary-false 移 L 的态只有 26（Core :432）；26 头 = 标记位左邻 ≥ n+1
（29 读 sel/nosel → 26 L，标记位 ≥ n+2）。故头 0 无 L 步，头 ≥ 0 归纳闭合。
带 0 恒 #ₗ 的联合分量：写位 0 ⟹ 头 0 ⟹ 读 #ₗ ⟹ 写符 boundary（表级：读 boundary-false
写 data0 的唯一态 20 的头 ≥ n+1 ≠ 0）。
-/

/-- 表级：读 boundary-false 且移 L 的态集合 {3, 5, 8, 10, 13, 26}（探针枚举全表）。 -/
lemma sym_step_boundary_false_L_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hs : s = Sym.boundary)
    (hd : r.moveDir = Dir.L) :
    q = 3 ∨ q = 5 ∨ q = 8 ∨ q = 10 ∨ q = 13 ∨ q = 26 ∨ q = 76 ∨ q = 84 := by
  interval_cases q
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (0, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (1, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 3 = 3 ∨ 3 = 5 ∨ 3 = 8 ∨ 3 = 10 ∨ 3 = 13 ∨ 3 = 26 ∨ 3 = 76 ∨ 3 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (4, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 5 = 3 ∨ 5 = 5 ∨ 5 = 8 ∨ 5 = 10 ∨ 5 = 13 ∨ 5 = 26 ∨ 5 = 76 ∨ 5 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (6, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (7, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 8 = 3 ∨ 8 = 5 ∨ 8 = 8 ∨ 8 = 10 ∨ 8 = 13 ∨ 8 = 26 ∨ 8 = 76 ∨ 8 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (9, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 10 = 3 ∨ 10 = 5 ∨ 10 = 8 ∨ 10 = 10 ∨ 10 = 13 ∨ 10 = 26 ∨ 10 = 76 ∨ 10 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (11, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (12, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 13 = 3 ∨ 13 = 5 ∨ 13 = 8 ∨ 13 = 10 ∨ 13 = 13 ∨ 13 = 26 ∨ 13 = 76 ∨ 13 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (14, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (15, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (16, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (17, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (18, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (19, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (20, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (21, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (22, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (23, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (24, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (25, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 26 = 3 ∨ 26 = 5 ∨ 26 = 8 ∨ 26 = 10 ∨ 26 = 13 ∨ 26 = 26 ∨ 26 = 76 ∨ 26 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (27, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (28, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (29, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (30, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (31, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (32, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (33, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (34, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (35, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (36, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (37, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (38, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (39, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (40, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (41, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (42, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (43, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (44, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (45, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (46, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (47, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (48, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (49, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (50, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (51, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (52, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (53, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (54, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (55, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (56, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (57, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (58, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (59, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (60, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (61, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (62, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (63, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (64, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (65, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (66, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (67, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (68, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (69, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (70, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (71, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (72, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (73, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (74, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (75, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 76 = 3 ∨ 76 = 5 ∨ 76 = 8 ∨ 76 = 10 ∨ 76 = 13 ∨ 76 = 26 ∨ 76 = 76 ∨ 76 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (77, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (78, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (79, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (80, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (81, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (82, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (83, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exact (by simp : 84 = 3 ∨ 84 = 5 ∨ 84 = 8 ∨ 84 = 10 ∨ 84 = 13 ∨ 84 = 26 ∨ 84 = 76 ∨ 84 = 84)
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (85, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (86, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (87, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (88, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (89, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (90, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (91, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (92, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (93, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (94, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (95, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (96, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (97, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (98, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (99, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (100, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
  · exfalso
    have hb : ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (101, s) → s = Sym.boundary → r.moveDir = Dir.L → False := by native_decide
    exact hb s r hr hs hd
/- ============================================================
§4 头非负（Sym 层）：三分类 + 候选态归约（2026-09-09 用户框架）

用户分类:
  1. R 态:头单调增,不越 #ₗ
  2. L 且识别 boundary-false 的态(读 boundary-false → R/S/101):头 0 处转向
  3. L 且读 boundary-false → L 的 8 态 {3,5,8,10,13,26,76,84}:唯一越界候选
     归约(逐态入边,照 r7l3_86_head 模板):
       3 ← 2 读 #₁ S(2 R 链:1 读 #₀ R@n+2 入)
       10 ← 77 读 #ₗ R(77 识别——头 ≥ 0(neg_no_boundary) → R@1)
       26 ← 29 读 sel/nosel L(r7l3_marker_pos:格 ≥ n+2 → 26 ≥ n+1)
       5/8/13/76/84(元素族)← 元素区入边(下一里程碑:E 族联合归纳)
  头 0 的 L 步 ⟹ 态 ∈ 8 态 ⟹ 头 ≥ 1 矛盾 ⟹ 头 ≥ 0 归纳闭合。
============================================================ -/

/-- 2 入边:1 读 boundary R(1 头 ≥ 0——负头格非 boundary)或 2 自环 R(读 data)。 -/
lemma sym_into_2 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h2 : r.nextState = 2) :
    (q = 1 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
      (q = 2 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 2 →
      ((q : ℕ) = 1 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 2 ∧ r.moveDir = Dir.R) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h2

/-- 2 态头 ≥ 1(2 从 1 读 boundary R 入(1 头 ≥ 0)或 2 自环 R 保持)。 -/
lemma sym_state2_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 2 → (1 : ℤ) ≤ cfg.headPos := by
  intro h2
  induction h with
  | nil => simp [symInitialConfig] at h2
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_2 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h2)
      rcases hsrc with h1src | h2src
      · rcases h1src with ⟨hq1, hrdb, hdR⟩
        have hge0 : (0 : ℤ) ≤ cfg'.headPos := by
          by_contra hlt
          have hnb := r7l3_neg_no_boundary inst hprev cfg'.headPos (by omega)
          have hrd' : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
            rw [← hread]
            exact hrdb
          exact hnb hrd'
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h2src with ⟨hq2s, hdR⟩
        have hge1 := ih hq2s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 3 入边:2 读 boundary S(标 #₁——2 头 ≥ 1)。 -/
lemma sym_into_3 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h3 : r.nextState = 3) :
    q = 2 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.S := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 3 →
      (q : ℕ) = 2 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.S := by native_decide
  exact hb ⟨q, hq⟩ s r hr h3

/-- 3 态头 ≥ 1(3 从 2 读 #₁ S 入(2 头 ≥ 1)——3 只触达 #₁@L-1)。 -/
lemma sym_state3_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 3 → (1 : ℤ) ≤ cfg.headPos := by
  intro h3
  induction h with
  | nil => simp [symInitialConfig] at h3
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_3 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h3)
      rcases hsrc with ⟨hq2, hrdb, hdS⟩
      have hge1 := sym_state2_head_ge1 inst hprev hq2
      simp [symStepConfig, hdS, Dir.toInt]
      omega

/-- 10 入边:77 读 boundary R(77 在 #ₗ 处右移定位)或 10 自环 R(扫 m 前缀)。 -/
lemma sym_into_10 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h10 : r.nextState = 10) :
    (q = 77 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
      (q = 10 ∧ s.1 = SymKind.data1 ∧ r.moveDir = Dir.R) ∨
        (q = 10 ∧ s.1 = SymKind.data0 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 10 →
      ((q : ℕ) = 77 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 10 ∧ s.1 = SymKind.data1 ∧ r.moveDir = Dir.R) ∨
          ((q : ℕ) = 10 ∧ s.1 = SymKind.data0 ∧ r.moveDir = Dir.R) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h10

/-- 10 态头 ≥ 1(10 从 77 读 #ₗ R 入@1(77 头 ≥ 0)或 10 自环 R 保持)。 -/
lemma sym_state10_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 10 → (1 : ℤ) ≤ cfg.headPos := by
  intro h10
  induction h with
  | nil => simp [symInitialConfig] at h10
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_10 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h10)
      rcases hsrc with h77 | h10a | h10b
      · rcases h77 with ⟨hq77, hrdb, hdR⟩
        have hge0 : (0 : ℤ) ≤ cfg'.headPos := by
          by_contra hlt
          have hnb := r7l3_neg_no_boundary inst hprev cfg'.headPos (by omega)
          have hrd' : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
            rw [← hread]
            exact hrdb
          exact hnb hrd'
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h10a with ⟨hq10s, hrd, hdR⟩
        have hge1 := ih hq10s
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h10b with ⟨hq10s, hrd, hdR⟩
        have hge1 := ih hq10s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 26 入边:29 读 sel/nosel L(配对——29 在元素头选择符位)。 -/
lemma sym_into_26 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h26 : r.nextState = 26) :
    q = 29 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧ r.moveDir = Dir.L := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 26 →
      (q : ℕ) = 29 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧ r.moveDir = Dir.L := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h26

/-- 26 态头 ≥ n+1(26 从 29 读 sel/nosel L 入——标记格 ≥ n+2(r7l3_marker_pos))。 -/
lemma sym_state26_head_ge_n1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 26 → (((encodeBitsSym inst.target).length + 1 : ℕ) : ℤ) ≤ cfg.headPos := by
  intro h26
  induction h with
  | nil => simp [symInitialConfig] at h26
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_26 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h26)
      rcases hsrc with ⟨hq29, hrd, hdL⟩
      have hmp := r7l3_marker_pos inst hprev cfg'.headPos (by
        rcases hrd with hsel | hnosel
        · rw [← hread]
          exact Or.inr (Or.inl hsel)
        · rw [← hread]
          exact Or.inr (Or.inr hnosel))
      simp [symStepConfig, hdL, Dir.toInt]
      rw [r7_enc_len] at hmp
      omega

/- E 族支撑(target 区 R/S 链态头 ≥ 0:负头格写者分类的前置)。 -/

/-- 11 入边:10 读 data0/1-false S(定位 t_j 标 m)。 -/
lemma sym_into_11 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h11 : r.nextState = 11) :
    q = 10 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.S := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 11 →
      (q : ℕ) = 10 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.S := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h11

/-- 11 态头 ≥ 1(10 ≥ 1 S 保持——11 在 t_j 上只读一次)。 -/
lemma sym_state11_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 11 → (1 : ℤ) ≤ cfg.headPos := by
  intro h11
  induction h with
  | nil => simp [symInitialConfig] at h11
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_11 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h11)
      rcases hsrc with ⟨hq10, hrd, hdS⟩
      have hge := sym_state10_head_ge1 inst hprev hq10
      simp [symStepConfig, hdS, Dir.toInt]
      omega

/-- 12 入边:9 读 boundary R(到 #ₗ 右移)或 12 自环 R(扫 m=1 前缀)。 -/
lemma sym_into_12 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h12 : r.nextState = 12) :
    (q = 9 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
      (q = 12 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 12 →
      ((q : ℕ) = 9 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 12 ∧ r.moveDir = Dir.R) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h12

/-- 12 态头 ≥ 1(9 读 boundary R(9 头 ≥ 0——负头格非 boundary)或 12 自环 R 保持)。 -/
lemma sym_state12_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 12 → (1 : ℤ) ≤ cfg.headPos := by
  intro h12
  induction h with
  | nil => simp [symInitialConfig] at h12
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_12 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h12)
      rcases hsrc with h9src | h12src
      · rcases h9src with ⟨hq9, hrdb, hdR⟩
        have hge0 : (0 : ℤ) ≤ cfg'.headPos := by
          by_contra hlt
          have hnb := r7l3_neg_no_boundary inst hprev cfg'.headPos (by omega)
          have hrd' : (cfg'.tape cfg'.headPos).1 = SymKind.boundary := by
            rw [← hread]
            exact hrdb
          exact hnb hrd'
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h12src with ⟨hq12s, hdR⟩
        have hge1 := ih hq12s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 14 入边:11 读 data0 R(借位发起)或 14 自环 R(借位右传)。 -/
lemma sym_into_14 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h14 : r.nextState = 14) :
    (q = 11 ∧ r.moveDir = Dir.R) ∨ (q = 14 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 14 →
      ((q : ℕ) = 11 ∧ r.moveDir = Dir.R) ∨ ((q : ℕ) = 14 ∧ r.moveDir = Dir.R) := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h14

/-- 14 态头 ≥ 1(11 ≥ 1 R 入(借位)或 14 自环 R 保持)。 -/
lemma sym_state14_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 14 → (1 : ℤ) ≤ cfg.headPos := by
  intro h14
  induction h with
  | nil => simp [symInitialConfig] at h14
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_14 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h14)
      rcases hsrc with h11src | h14src
      · rcases h11src with ⟨hq11, hdR⟩
        have hge1 := sym_state11_head_ge1 inst hprev hq11
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h14src with ⟨hq14s, hdR⟩
        have hge1 := ih hq14s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 81 入边:11/12/14 读 data0/1-false R(减法回程)或 81 自环 R(穿透 #₀/扫 data)。 -/
lemma sym_into_81 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h81 : r.nextState = 81) :
    ((q = 11 ∨ q = 12 ∨ q = 14) ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧
      r.moveDir = Dir.R) ∨ (q = 81 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 81 →
      (((q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14) ∧
        (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 81 ∧ r.moveDir = Dir.R) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h81

/-- 81 态头 ≥ 1(11/12/14 ≥ 1 R 入或 81 自环 R 保持——81 只在减法回程行走)。 -/
lemma sym_state81_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 81 → (1 : ℤ) ≤ cfg.headPos := by
  intro h81
  induction h with
  | nil => simp [symInitialConfig] at h81
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_81 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h81)
      rcases hsrc with htrg | h81s
      · rcases htrg with ⟨hqt, hrd, hdR⟩
        have hge1 : (1 : ℤ) ≤ cfg'.headPos := by
          rcases hqt with hq11 | hq12 | hq14
          · exact sym_state11_head_ge1 inst hprev hq11
          · exact sym_state12_head_ge1 inst hprev hq12
          · exact sym_state14_head_ge1 inst hprev hq14
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h81s with ⟨hq81s, hdR⟩
        have hge1 := ih hq81s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 13 入边:81 读 consumed R(回已消耗区开头)或 13 自环 R(扫 consumed)。 -/
lemma sym_into_13 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h13 : r.nextState = 13) :
    (q = 81 ∧ s.1 = SymKind.consumed ∧ r.moveDir = Dir.R) ∨
      (q = 13 ∧ r.moveDir = Dir.R) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 13 →
      ((q : ℕ) = 81 ∧ s.1 = SymKind.consumed ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 13 ∧ r.moveDir = Dir.R) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h13

/-- 13 态头 ≥ 1(81 读 consumed ≥ 1 R 入或 13 自环 R 保持)。 -/
lemma sym_state13_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 13 → (1 : ℤ) ≤ cfg.headPos := by
  intro h13
  induction h with
  | nil => simp [symInitialConfig] at h13
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_13 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h13)
      rcases hsrc with h81src | h13src
      · rcases h81src with ⟨hq81, hrdc, hdR⟩
        have hge1 := sym_state81_head_ge1 inst hprev hq81
        simp [symStepConfig, hdR, Dir.toInt]
        omega
      · rcases h13src with ⟨hq13s, hdR⟩
        have hge1 := ih hq13s
        simp [symStepConfig, hdR, Dir.toInt]
        omega

/-- 5 入边:4 读 sel R(选中元素——清选择位)或 13 读 data S(下一未消费位)。 -/
lemma sym_into_5 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h5 : r.nextState = 5) :
    (q = 4 ∧ s.1 = SymKind.sel ∧ r.moveDir = Dir.R) ∨
      (q = 13 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.S) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 5 →
      ((q : ℕ) = 4 ∧ s.1 = SymKind.sel ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 13 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ r.moveDir = Dir.S) := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr h5

/-- 5 态头 ≥ 1(4 读 sel R 入(标记格 ≥ n+2)或 13 读 data S 入(13 ≥ 1))。 -/
lemma sym_state5_head_ge1 (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.state = 5 → (1 : ℤ) ≤ cfg.headPos := by
  intro h5
  induction h with
  | nil => simp [symInitialConfig] at h5
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hsrc := sym_into_5 cfg'.state
        (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
        step.readSym step.result (by simpa [hread] using htrans) (by simpa [symStepConfig] using h5)
      rcases hsrc with h4src | h13src
      · rcases h4src with ⟨hq4, hrd, hdR⟩
        have hmp := r7l3_marker_pos inst hprev cfg'.headPos (by
          rw [← hread]
          exact Or.inr (Or.inl hrd))
        simp [symStepConfig, hdR, Dir.toInt]
        rw [r7_enc_len] at hmp
        omega
      · rcases h13src with ⟨hq13, hrd, hdS⟩
        have hge1 := sym_state13_head_ge1 inst hprev hq13
        simp [symStepConfig, hdS, Dir.toInt]
        omega

/- 主引理前置件:tape 0 完整符号、负头格恒 blank、路径唯一、101/漂移吸收。 -/

/-- 读 (boundary, false) 写 boundary-true 的态只有 3(#₁ 标 m=1;3 头 = L-1 不写 0 位)。 -/
lemma sym_read_bndF_write_bndT (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : s = Sym.boundary)
    (hw : r.writeSym = Sym.mk SymKind.boundary true) : q = 3 := by
  have hb2 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s = Sym.boundary →
      r.writeSym = Sym.mk SymKind.boundary true → (q : ℕ) = 3 := by native_decide
  exact hb2 ⟨q, hq⟩ s r hr hb hw

/-- tape 0 恒 = #ₗ((boundary, false)——完整符号;P6l 只给 kind,m 分量在此补)。 -/
lemma sym_tape0_boundary_full (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    cfg.tape 0 = Sym.boundary := by
  induction h with
  | nil =>
      dsimp [symInitialConfig]
      -- 初始带 0 位 = [Sym.boundary](encodeInstanceSym 头)——getD 0
      simp [symInitialConfig]
      rfl
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      dsimp [symStepConfig]
      by_cases hw : cfg'.headPos = 0
      · rw [hw]
        have hrd : step.readSym = Sym.boundary := by
          rw [hread, hw]
          exact ih
        by_cases hbw : step.result.writeSym = Sym.mk SymKind.boundary true
        · have hq3 := sym_read_bndF_write_bndT cfg'.state
            (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
            step.readSym step.result (by simpa [hread] using htrans) hrd hbw
          exfalso
          have hge := sym_state3_head_ge1 inst hprev hq3
          omega
        · -- 写回(读 boundary-false 保符号)或 20 写 data0——20 头 ≥ 1(r7l3_20_head)不写 0 位
          have hwcls : step.result.writeSym = Sym.boundary ∨ step.result.writeSym = Sym.mk SymKind.data0 false := by
            have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                r ∈ VerifierSym.transition ((q : ℕ), s) → s = Sym.boundary →
                r.writeSym ≠ Sym.mk SymKind.boundary true →
                r.writeSym = Sym.boundary ∨ r.writeSym = Sym.mk SymKind.data0 false := by
              native_decide
            exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
              step.readSym step.result (by simpa [hread] using htrans) hrd hbw
          rcases hwcls with hws | hwd
          · exact hws
          · exfalso
            have hq20 : cfg'.state = 20 := by
              have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition ((q : ℕ), s) → s = Sym.boundary →
                  r.writeSym = Sym.mk SymKind.data0 false → (q : ℕ) = 20 := by native_decide
              exact hb ⟨cfg'.state, q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev⟩
                step.readSym step.result (by simpa [hread] using htrans) hrd hwd
            have hge := r7l3_20_head inst hprev hq20
            omega
      · simpa [Ne.symm hw] using ih

/-- 读 data0-false 写非 data0-false 的态集 G = {5,10,11,12,14,51}(负位写者分类)。 -/
lemma sym_blank_writer_class (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : s = Sym.mk SymKind.data0 false)
    (hw : r.writeSym ≠ Sym.mk SymKind.data0 false) :
    q = 5 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 14 ∨ q = 51 := by
  have hb2 : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s = Sym.mk SymKind.data0 false →
      r.writeSym ≠ Sym.mk SymKind.data0 false →
      (q : ℕ) = 5 ∨ (q : ℕ) = 10 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨
        (q : ℕ) = 51 := by native_decide
  exact hb2 ⟨q, hq⟩ s r hr hb hw

/-- 负头格恒 = blank(data0-false):写 boundary 者(读 boundary ∨ 51)与 G 族态的头域排除。 -/
lemma sym_neg_head_blank (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg) :
    ∀ j : ℤ, j < 0 → cfg.tape j = Sym.mk SymKind.data0 false := by
  induction h with
  | nil =>
      intro j hj
      dsimp [symInitialConfig]
      split
      · rename_i hc
        exfalso
        omega
      · decide
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro j hj
      dsimp [symStepConfig]
      by_cases hw : j = cfg'.headPos
      · have hnb : cfg'.tape j = Sym.mk SymKind.data0 false := ih j hj
        have hrd : step.readSym = Sym.mk SymKind.data0 false := by
          simpa [hread, hw.symm] using hnb
        by_cases hbw : step.result.writeSym = Sym.mk SymKind.data0 false
        · simp [hw, hbw]
        · have hcls := sym_blank_writer_class cfg'.state
            (q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg' hprev)
            step.readSym step.result (by simpa [hread] using htrans) hrd hbw
          rcases hcls with h5 | h10 | h11 | h12 | h14 | h51
          · exfalso
            have hge := sym_state5_head_ge1 inst hprev h5
            omega
          · exfalso
            have hge := sym_state10_head_ge1 inst hprev h10
            omega
          · exfalso
            have hge := sym_state11_head_ge1 inst hprev h11
            omega
          · exfalso
            have hge := sym_state12_head_ge1 inst hprev h12
            omega
          · exfalso
            have hge := sym_state14_head_ge1 inst hprev h14
            omega
          · exfalso
            have hdom := r7l3_51_domain inst hprev h51
            omega
      · simpa [hw] using ih j hj

/-- snoc 分解唯一(π₁ ++ [a] = π₂ ++ [b] → 前缀等 ∧ 尾等)。 -/
lemma snoc_eq_snoc {α : Type} {π₁ π₂ : List α} {a b : α}
    (h : π₁ ++ [a] = π₂ ++ [b]) : π₁ = π₂ ∧ a = b := by
  have hrev : (π₁ ++ [a]).reverse = (π₂ ++ [b]).reverse := by rw [h]
  have hcons : a :: π₁.reverse = b :: π₂.reverse := by simpa using hrev
  have ha : a = b := by simpa using (List.cons.inj hcons).1
  have hπr : π₁.reverse = π₂.reverse := (List.cons.inj hcons).2
  have hπ : π₁ = π₂ := by
    rw [← List.reverse_reverse π₁, hπr, List.reverse_reverse]
  exact ⟨hπ, ha⟩

/-- SymSteps 同路径同终点(步序列确定)。 -/
lemma symSteps_nil_cfg {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg : SymConfig}
    (h : SymSteps M cfg₀ [] cfg) : cfg = cfg₀ := by
  exact (SymSteps.recOn h (motive := fun π cfg _ => π = [] → cfg = cfg₀)
    (fun hπ => rfl)
    (fun π₀ step cfg' hprev hfrom hread htrans ih hπ => False.elim (by
      have hlen : (π₀ ++ [step]).length = 0 := by simpa using congrArg List.length hπ
      have hlen' : π₀.length + 1 = 0 := by simpa using hlen
      exact Nat.succ_ne_zero π₀.length hlen'))) rfl

lemma sym_steps_det {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg₁ cfg₂ : SymConfig}
    (π : List SymStep) (h₁ : SymSteps M cfg₀ π cfg₁) (h₂ : SymSteps M cfg₀ π cfg₂) :
    cfg₁ = cfg₂ := by
  revert cfg₂
  induction h₁ with
  | nil =>
      intro cfg₂ h₂
      exact (symSteps_nil_cfg h₂).symm
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro cfg₂ h₂
      have hne₂ : π₀ ++ [step] ≠ [] := by simp
      have hsp₂ := Mp.SymToF4.symSteps_split_last h₂ hne₂
      rcases hsp₂ with ⟨step₂, π₂, cfg₂₀, hs₂, hprev₂, hfrom₂, hread₂, htrans₂, hcfg₂⟩
      have hsnoc := snoc_eq_snoc (hs₂.symm : π₂ ++ [step₂] = π₀ ++ [step])
      rcases hsnoc with ⟨hπ, hst⟩
      subst π₂
      subst step₂
      have hcfg' : cfg' = cfg₂₀ := ih hprev₂
      subst cfg'
      rw [hcfg₂]

/- 主引理组:101 吸收、漂移排除、8 类 next、头 ≥ 0 主引理。 -/

/-- SymSteps 拼接。 -/
lemma symSteps_append_concat {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg₁ cfg₂ : SymConfig}
    (π₁ π₂ : List SymStep) (h₁ : SymSteps M cfg₀ π₁ cfg₁) (h₂ : SymSteps M cfg₁ π₂ cfg₂) :
    SymSteps M cfg₀ (π₁ ++ π₂) cfg₂ := by
  induction h₂ with
  | nil => simpa using h₁
  | cons π₂₀ step₂ cfg₂' hprev₂ hfrom₂ hread₂ htrans₂ ih =>
      simpa [List.append_assoc] using
        (SymSteps.cons (π₁ ++ π₂₀) step₂ cfg₂' ih hfrom₂ hread₂ htrans₂ :
          SymSteps M cfg₀ ((π₁ ++ π₂₀) ++ [step₂]) (symStepConfig cfg₂' step₂.result))

/-- 漂移态 {9,77,84,85} 读 blank(data0-false)→ 同态 L 写回。 -/
lemma sym_drift_read_blank (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : s = Sym.mk SymKind.data0 false)
    (hdrift : q = 9 ∨ q = 77 ∨ q = 84 ∨ q = 85) :
    r.nextState = q ∧ r.moveDir = Dir.L ∧ r.writeSym = s := by
  rcases hdrift with h9 | h77 | h84 | h85
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (9, s) →
        s = Sym.mk SymKind.data0 false → r.nextState = 9 ∧ r.moveDir = Dir.L ∧ r.writeSym = s := by
      native_decide
    exact hb2 s r hr hb
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (77, s) →
        s = Sym.mk SymKind.data0 false → r.nextState = 77 ∧ r.moveDir = Dir.L ∧ r.writeSym = s := by
      native_decide
    exact hb2 s r hr hb
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (84, s) →
        s = Sym.mk SymKind.data0 false → r.nextState = 84 ∧ r.moveDir = Dir.L ∧ r.writeSym = s := by
      native_decide
    exact hb2 s r hr hb
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (85, s) →
        s = Sym.mk SymKind.data0 false → r.nextState = 85 ∧ r.moveDir = Dir.L ∧ r.writeSym = s := by
      native_decide
    exact hb2 s r hr hb

/-- 101 出发的任意 SymSteps 终点恒 101(101 读任意 → 101 S 吸收)。 -/
lemma sym_steps_from_101 {cfg₀ cfg : SymConfig} (π : List SymStep)
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) (h0 : cfg₀.state = 101) :
    cfg.state = 101 := by
  induction h with
  | nil => exact h0
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hns : step.result.nextState = 101 := by
        have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (101, s) →
            r.nextState = 101 := by native_decide
        exact hb (cfg'.tape cfg'.headPos) step.result (by simpa [ih] using htrans)
      dsimp [symStepConfig]
      simpa [hns] using ih

/-- 漂移态 + 负头出发的任意 SymSteps:终点恒(漂移态 ∧ 负头 ∧ 负位 blank)(每步读负位 blank——写回保持)。 -/
lemma sym_steps_drift_neg {cfg₀ cfg : SymConfig} (π : List SymStep)
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hblank₀ : ∀ j : ℤ, j < 0 → cfg₀.tape j = Sym.mk SymKind.data0 false)
    (hneg : cfg₀.headPos < 0)
    (hdrift : cfg₀.state = 9 ∨ cfg₀.state = 77 ∨ cfg₀.state = 84 ∨ cfg₀.state = 85) :
    (cfg.state = 9 ∨ cfg.state = 77 ∨ cfg.state = 84 ∨ cfg.state = 85) ∧ cfg.headPos < 0 ∧
      (∀ j : ℤ, j < 0 → cfg.tape j = Sym.mk SymKind.data0 false) := by
  induction h with
  | nil => exact ⟨hdrift, hneg, hblank₀⟩
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      rcases ih with ⟨hdrift', hneg', hblank'⟩
      have hq' : cfg'.state < 102 := by
        rcases hdrift' with h9' | h77' | h84' | h85'
        · rw [h9']; norm_num
        · rw [h77']; norm_num
        · rw [h84']; norm_num
        · rw [h85']; norm_num
      have hrd : step.readSym = Sym.mk SymKind.data0 false := by
        rw [hread]
        exact hblank' cfg'.headPos hneg'
      have hdr := sym_drift_read_blank cfg'.state hq' step.readSym step.result
        (by simpa [hfrom, hread] using htrans) hrd hdrift'
      rcases hdr with ⟨hns, hdL, hws⟩
      constructor
      · -- 漂移保持(态不变——nextState = cfg'.state)
        rcases hdrift' with h9' | h77' | h84' | h85'
        · left; simpa [symStepConfig, h9'] using hns
        · right; left; simpa [symStepConfig, h77'] using hns
        · right; right; left; simpa [symStepConfig, h84'] using hns
        · right; right; right; simpa [symStepConfig, h85'] using hns
      · constructor
        · -- 负头保持(头 - 1)
          dsimp [symStepConfig]
          rw [hdL]
          simp [Dir.toInt]
          omega
        · -- 负位 blank 保持
          intro j hj
          dsimp [symStepConfig]
          by_cases hw : j = cfg'.headPos
          · rw [hw]
            simpa [hws, hrd]
          · simpa [hw] using hblank' j hj

/- no_ext 引理与 8 类 next(主引理支撑)。 -/

/-- 漂移态 {9,77,84,85} + 负头不可延拓到 100。 -/
lemma sym_drift_no_ext (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hneg : cfg.headPos < 0)
    (hdrift : cfg.state = 9 ∨ cfg.state = 77 ∨ cfg.state = 84 ∨ cfg.state = 85) :
    ¬ ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100 := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, h₂, hq₂⟩
  have h₂s : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂).mpr h₂
  have hdec := symSteps_append_decomp (M := VerifierSym.transition)
    (cfg₀ := symInitialConfig (encodeInstanceSym inst)) π π₂ h₂s
  rcases hdec with ⟨cfg₁', h₁₀, h₁₁⟩
  have hs : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
    (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π cfg).mpr h
  have hdet := sym_steps_det π hs h₁₀
  subst cfg₁'
  have hblank : ∀ j : ℤ, j < 0 → cfg.tape j = Sym.mk SymKind.data0 false :=
    sym_neg_head_blank inst h
  have hres := sym_steps_drift_neg π₂ h₁₁ hblank hneg hdrift
  rcases hres.1 with h9 | h77 | h84 | h85
  · rw [h9] at hq₂
    simp at hq₂
  · rw [h77] at hq₂
    simp at hq₂
  · rw [h84] at hq₂
    simp at hq₂
  · rw [h85] at hq₂
    simp at hq₂

/-- 拒态 {101,24,27} + 负头不可延拓到 100(24/27 读负位 blank → 101 吸收)。 -/
lemma sym_rej_cfg_no_ext (inst : SubsetSumInstance) {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hneg : cfg.headPos < 0)
    (hrej : cfg.state = 101 ∨ cfg.state = 24 ∨ cfg.state = 27) :
    ¬ ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100 := by
  intro hext
  rcases hext with ⟨π₂, cfg₂, h₂, hq₂⟩
  have h₂s : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (π ++ π₂) cfg₂ :=
    (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂).mpr h₂
  have hdec := symSteps_append_decomp (M := VerifierSym.transition)
    (cfg₀ := symInitialConfig (encodeInstanceSym inst)) π π₂ h₂s
  rcases hdec with ⟨cfg₁', h₁₀, h₁₁⟩
  have hs : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
    (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π cfg).mpr h
  have hdet := sym_steps_det π hs h₁₀
  subst cfg₁'
  by_cases hπ₂ : π₂ = []
  · subst π₂
    have hcfg₂ : cfg₂ = cfg := symSteps_nil_cfg h₁₁
    subst cfg₂
    rcases hrej with h101 | h24 | h27
    · rw [h101] at hq₂; simp at hq₂
    · rw [h24] at hq₂; simp at hq₂
    · rw [h27] at hq₂; simp at hq₂
  · -- π₂ 非空：第一步 cfg 态 ∈ {101,24,27} → 101(24/27 读负位 blank)——之后 101 吸收
    rcases (List.exists_cons_of_ne_nil hπ₂) with ⟨step₂, rest₂, hπ₂eq⟩
    subst π₂
    -- h₁₁ : SymSteps cfg (step₂ :: rest₂) cfg₂ = SymSteps cfg ([step₂] ++ rest₂) cfg₂
    have hdec₂ := symSteps_append_decomp (M := VerifierSym.transition) (cfg₀ := cfg) [step₂] rest₂
      (by simpa using h₁₁)
    rcases hdec₂ with ⟨cfg₀₁, h₂₀, h₂₁⟩
    -- 单步 h₂₀ : SymSteps cfg [step₂] cfg₀₁——展开（cons [] step₂ cfg₀'' ...）
    have h₀₁s : cfg₀₁.state = 101 := by
      -- 单步：cfg 态 ∈ {101,24,27}——101 读任意 → 101；24/27 读负位(blank) → 101
      rcases hrej with h101 | h24 | h27
      · -- cfg 态 101——101 读任意 → 101——用 from_101 于 [step₂]
        have h101' : cfg₀₁.state = 101 := sym_steps_from_101 [step₂] h₂₀ h101
        exact h101'
      · -- cfg 态 24——读负位 blank → 101
        have hq' : cfg.state < 102 := by rw [h24]; norm_num
        have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (24, s) →
            s = Sym.mk SymKind.data0 false → r.nextState = 101 := by native_decide
        -- h₂₀ 的单步：cons [] step₂ cfg₀'' hprev₂ ... ——cfg₀'' = cfg（nil_cfg）
        -- 从 h₂₀ 提取 step₂ 的转移
        have hsp := Mp.SymToF4.symSteps_split_last h₂₀ (by simp : [step₂] ≠ [])
        rcases hsp with ⟨step₃, π₃, cfg₃, hs₃, hprev₃, hfrom₃, hread₃, htrans₃, hcfg₃⟩
        -- hs₃ : π₃ ++ [step₃] = [step₂]——snoc 唯一 → π₃ = [] ∧ step₃ = step₂
        have hlen₃ : π₃.length = 0 := by
          have hlen : 1 = π₃.length + 1 := by simpa using congrArg List.length hs₃
          omega
        have hπ₃ : π₃ = [] := by
          cases π₃ with
          | nil => rfl
          | cons a rest => simp at hlen₃
        subst π₃
        have hst₃ : step₃ = step₂ := by simpa using hs₃.symm
        subst step₃
        have hcfg₃₀ : cfg₃ = cfg := symSteps_nil_cfg hprev₃
        subst cfg₃
        -- htrans₃ : step₂.result ∈ transition (cfg.state, cfg.tape cfg.headPos)——cfg 态 24（h24）——读负位（hneg——blank
        have hbnd : step₂.result.nextState = 101 := by
          have hnb : cfg.tape cfg.headPos = Sym.mk SymKind.data0 false := by
            exact sym_neg_head_blank inst h cfg.headPos hneg
          exact hb (cfg.tape cfg.headPos) step₂.result (by simpa [h24, hfrom₃, hread₃] using htrans₃) hnb
        -- cfg₀₁ = symStepConfig cfg₃ step₂.result（hcfg₃——cfg₀₁.state = 101
        rw [hcfg₃]
        simpa [symStepConfig, hbnd] using hbnd.symm
      · -- cfg 态 27——同 24
        have hq' : cfg.state < 102 := by rw [h27]; norm_num
        have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (27, s) →
            s = Sym.mk SymKind.data0 false → r.nextState = 101 := by native_decide
        have hsp := Mp.SymToF4.symSteps_split_last h₂₀ (by simp : [step₂] ≠ [])
        rcases hsp with ⟨step₃, π₃, cfg₃, hs₃, hprev₃, hfrom₃, hread₃, htrans₃, hcfg₃⟩
        have hlen₃ : π₃.length = 0 := by
          have hlen : 1 = π₃.length + 1 := by simpa using congrArg List.length hs₃
          omega
        have hπ₃ : π₃ = [] := by
          cases π₃ with
          | nil => rfl
          | cons a rest => simp at hlen₃
        subst π₃
        have hst₃ : step₃ = step₂ := by simpa using hs₃.symm
        subst step₃
        have hcfg₃₀ : cfg₃ = cfg := symSteps_nil_cfg hprev₃
        subst cfg₃
        have hbnd : step₂.result.nextState = 101 := by
          have hnb : cfg.tape cfg.headPos = Sym.mk SymKind.data0 false := by
            exact sym_neg_head_blank inst h cfg.headPos hneg
          exact hb (cfg.tape cfg.headPos) step₂.result (by simpa [h27, hfrom₃, hread₃] using htrans₃) hnb
        rw [hcfg₃]
        simpa [symStepConfig, hbnd] using hbnd.symm
    -- 101 吸收于 rest₂ → cfg₂ 态 101 ≠ 100
    have h101₂ : cfg₂.state = 101 := sym_steps_from_101 rest₂ h₂₁ h₀₁s
    rw [h101₂] at hq₂
    simp at hq₂

/-- 8 类态读 boundary-false 移 L 的 nextState 分类。 -/
lemma sym_8class_next (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hb : s = Sym.boundary) (hd : r.moveDir = Dir.L)
    (hcls : q = 3 ∨ q = 5 ∨ q = 8 ∨ q = 10 ∨ q = 13 ∨ q = 26 ∨ q = 76 ∨ q = 84) :
    r.nextState = 24 ∨ r.nextState = 101 ∨ r.nextState = 9 ∨ r.nextState = 84 ∨
      r.nextState = 27 ∨ r.nextState = 77 ∨ r.nextState = 85 := by
  rcases hcls with h3 | h5 | h8 | h10 | h13 | h26 | h76 | h84
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (3, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 24 := by native_decide
    exact Or.inl (hb2 s r hr hb hd)
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (5, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 101 := by native_decide
    exact Or.inr (Or.inl (hb2 s r hr hb hd))
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (8, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 9 := by native_decide
    exact Or.inr (Or.inr (Or.inl (hb2 s r hr hb hd)))
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (10, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 101 := by native_decide
    exact Or.inr (Or.inl (hb2 s r hr hb hd))
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (13, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 84 := by native_decide
    exact Or.inr (Or.inr (Or.inr (Or.inl (hb2 s r hr hb hd))))
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (26, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 27 := by native_decide
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hb2 s r hr hb hd)))))
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (76, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 77 := by native_decide
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hb2 s r hr hb hd))))))
  · subst q
    have hb2 : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (84, s) →
        s = Sym.boundary → r.moveDir = Dir.L → r.nextState = 85 := by native_decide
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hb2 s r hr hb hd))))))

/-- 100 入边:23 读 boundary R(#ₗ 判定完成)或 100 自环 S(吸收)。 -/
lemma sym_into_100 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (h100 : r.nextState = 100) :
    (q = 23 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
      (q = 100 ∧ r.moveDir = Dir.S) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState = 100 →
      ((q : ℕ) = 23 ∧ s.1 = SymKind.boundary ∧ r.moveDir = Dir.R) ∨
        ((q : ℕ) = 100 ∧ r.moveDir = Dir.S) := by native_decide
  exact hb ⟨q, hq⟩ s r hr h100

/- A-3 主引理:接受路径每前缀头 ≥ 0(左界——r7_accept_path_prefix_inside 的下界配对)。
   归纳(前缀路径)——cons 越界分支:源头 0 读 #ₗ L → 8 类态 → next ∈ {24,101,9,84,27,77,85}
   → 101/24/27(拒类)与 9/77/84/85(漂移类)均不可延拓(hext₀ 矛盾)。 -/
/- A-3 主引理:接受路径每前缀头 ≥ 0(左界——r7_accept_path_prefix_inside 的下界配对)。
   归纳(前缀路径)——cons 越界分支:源头 0 读 #ₗ L → 8 类态 → next ∈ {24,101,9,84,27,77,85}
   → 101/24/27(拒类)与 9/77/84/85(漂移类)均不可延拓(从 h 全长重建的 hext₀ 矛盾)。 -/
/- A-3 主引理辅助:可延拓前缀的头 ≥ 0(归纳——hext 为参数)。
   cons 越界分支:源头 0 读 #ₗ L → 8 类态 → next ∈ {24,101,9,84,27,77,85}
   → 101/24/27(拒类)与 9/77/84/85(漂移类)均不可延拓(hext 矛盾)。 -/
/- A-3 主引理:接受路径每前缀头 ≥ 0(左界——r7_accept_path_prefix_inside 的下界配对)。
   对全长路径 h 归纳:cons(最后步进入 100)的前缀 = hprev 的前缀(ih)∪ {全长}
   (前缀拆分:π₀ ++ rest = π_hprev ++ [step]——rest = [] 或 snoc 拆——真前缀归 ih)。
   全长终点 cfg(态 100):头 ≥ 0(100 入边表级:23 读 #ₗ R@1——cfg' 头 ≥ 0(ih) + R)。 -/
/- A-3 主引理:接受路径每前缀头 ≥ 0(r7_accept_path_prefix_inside 的下界配对)。
   照 symAccepts_no_101(Reverse3:7923)内部引理模式:hmain 参数化 cfg'.state ≠ 101(反证可
   向后构造:cfg₁ 态 101 ⟹ state101_absorb ⟹ 步后 101 ⟹ hne101 矛盾),终点 100 条件不进归纳
   (hmain 的 hext' 参数从 cfg 的延拓给)。cons 越界分支:源头 0 读 #ₗ L → 8 类态 →
   next ∈ {24,101,9,84,27,77,85} → 拒类(101/24/27)/漂移类(9/77/84/85)不可延拓(hext 矛盾)。 -/
lemma sym_accept_prefix_head_nonneg (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v)
    (htarget : 0 < inst.target) :
    ∀ π cfg, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg →
      cfg.state = 100 →
      ∀ π₀ cfg₀, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₀ →
        List.IsPrefix π₀ π → (0 : ℤ) ≤ cfg₀.headPos := by
  intro π cfg h hq
  have hext_full : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π ++ π₂) cfg₂ ∧
      cfg₂.state = 100 := by
    refine ⟨[], cfg, ?_, hq⟩
    simpa using h
  have hmain : ∀ {π' : List SymStep} {cfg' : SymConfig},
      SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π' cfg' →
      cfg'.state ≠ 101 →
      (∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π' ++ π₂) cfg₂ ∧
        cfg₂.state = 100) →
      ∀ π₀ cfg₀, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π₀ cfg₀ →
        List.IsPrefix π₀ π' → (0 : ℤ) ≤ cfg₀.headPos := by
    intro π' cfg' h' hne101 hext'
    induction h' with
    | nil =>
        intro π₀ cfg₀ h₀ hpfix
        rcases hpfix with ⟨rest, hπ⟩
        have hπ₀ : π₀ = [] := by
          cases π₀ with
          | nil => rfl
          | cons a rest' =>
              exfalso
              simp at hπ
        subst π₀
        have h₀s : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) [] cfg₀ :=
          (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) [] cfg₀).mpr h₀
        have hcfg₀ : cfg₀ = symInitialConfig (encodeInstanceSym inst) := symSteps_nil_cfg h₀s
        subst cfg₀
        simp [symInitialConfig]
    | cons π₁ step cfg₁ hprev hfrom hread htrans ih =>
        -- hne₁:cfg₁.state ≠ 101(反证——101 吸收——两分支共用)
        have hne₁ : cfg₁.state ≠ 101 := by
          intro h101
          have hnext : step.result.nextState = 101 := by
            have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (101, s) →
                r.nextState = 101 := by native_decide
            exact hb step.readSym step.result (by
              have htrans' : step.result ∈ VerifierSym.transition (101, step.readSym) := by
                rw [h101] at htrans
                rw [← hread] at htrans
                exact htrans
              exact htrans')
          apply hne101
          simpa [symStepConfig, hnext]
        -- hext₁:cfg₁ 延拓(step :: hext' 的 π₂)
        rcases hext' with ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
        have hext₁ : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst) (π₁ ++ π₂) cfg₂ ∧
            cfg₂.state = 100 := by
          refine ⟨step :: π₂₀, cfg₂₀, ?_, hq₂₀⟩
          simpa [List.append_assoc] using h₂₀
        intro π₀ cfg₀ h₀ hpfix
        rcases hpfix with ⟨rest, hπ⟩
        by_cases hrest : rest = []
        · subst rest
          have hπ₀ : π₀ = π₁ ++ [step] := by simpa using hπ
          subst π₀
          have h₀s : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (π₁ ++ [step]) cfg₀ :=
            (symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) (π₁ ++ [step]) cfg₀).mpr h₀
          have hs : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (π₁ ++ [step]) (symStepConfig cfg₁ step.result) :=
            SymSteps.cons π₁ step cfg₁
              ((symSteps_initial_iff VerifierSym.transition (encodeInstanceSym inst) π₁ cfg₁).mpr hprev)
              hfrom hread htrans
          have hcfg₀ : cfg₀ = symStepConfig cfg₁ step.result := sym_steps_det (π₁ ++ [step]) h₀s hs
          subst cfg₀
          -- cfg₁ 头 ≥ 0:ih(hne₁ hext₁ 于 hprev——π₁ 前缀自身)
          have hih : (0 : ℤ) ≤ cfg₁.headPos := ih hne₁ hext₁ π₁ cfg₁ hprev ⟨[], by simp⟩
          -- 当前步:cfg₀ = symStepConfig cfg₁ step.result——cfg₀ 头 = cfg₁ 头 + dir
          by_cases hnn : (0 : ℤ) ≤ (symStepConfig cfg₁ step.result).headPos
          · exact hnn
          · have hdL : step.result.moveDir = Dir.L := by
              cases h : step.result.moveDir with
              | L => rfl
              | S =>
                  exfalso
                  dsimp [symStepConfig] at hnn
                  rw [h] at hnn
                  simp [Dir.toInt] at hnn
                  omega
              | R =>
                  exfalso
                  dsimp [symStepConfig] at hnn
                  rw [h] at hnn
                  simp [Dir.toInt] at hnn
                  omega
            have hcfg₁₀ : cfg₁.headPos = 0 := by
              dsimp [symStepConfig] at hnn
              rw [hdL] at hnn
              simp [Dir.toInt] at hnn
              omega
            have hneg₀ : (symStepConfig cfg₁ step.result).headPos < 0 := by omega
            have hrd : step.readSym = Sym.boundary := by
              rw [hread, hcfg₁₀]
              exact sym_tape0_boundary_full inst hprev
            have hq' : cfg₁.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₁ cfg₁ hprev
            have hcls := sym_step_boundary_false_L_class cfg₁.state hq'
              step.readSym step.result (by simpa [hread] using htrans) hrd hdL
            have hnxt := sym_8class_next cfg₁.state hq'
              step.readSym step.result (by simpa [hread] using htrans) hrd hdL hcls
            rcases hnxt with h24 | h101 | h9 | h84 | h27 | h77 | h85
            · exfalso
              apply sym_rej_cfg_no_ext inst
              · exact h₀
              · omega
              · exact Or.inr (Or.inl (by simpa [symStepConfig] using h24))
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
            · exfalso
              apply sym_rej_cfg_no_ext inst
              · exact h₀
              · omega
              · exact Or.inl (by simpa [symStepConfig] using h101)
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
            · exfalso
              apply sym_drift_no_ext inst
              · exact h₀
              · omega
              · exact Or.inl (by simpa [symStepConfig] using h9)
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
            · exfalso
              apply sym_drift_no_ext inst
              · exact h₀
              · omega
              · exact Or.inr (Or.inr (Or.inl (by simpa [symStepConfig] using h84)))
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
            · exfalso
              apply sym_rej_cfg_no_ext inst
              · exact h₀
              · omega
              · exact Or.inr (Or.inr (by simpa [symStepConfig] using h27))
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
            · exfalso
              apply sym_drift_no_ext inst
              · exact h₀
              · omega
              · exact Or.inr (Or.inl (by simpa [symStepConfig] using h77))
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
            · exfalso
              apply sym_drift_no_ext inst
              · exact h₀
              · omega
              · exact Or.inr (Or.inr (Or.inr (by simpa [symStepConfig] using h85)))
              · exact ⟨π₂₀, cfg₂₀, h₂₀, hq₂₀⟩
        · -- rest 非空:snoc 拆 rest = rest₀ ++ [x]——snoc_eq_snoc → π₀ ++ rest₀ = π₁——归 ih
          rcases list_snoc_decomp hrest with ⟨rest₀, x, hresteq⟩
          subst rest
          have hsnoc := snoc_eq_snoc (by simpa [List.append_assoc] using hπ :
            (π₀ ++ rest₀) ++ [x] = π₁ ++ [step])
          rcases hsnoc with ⟨hπ₀, hx⟩
          exact ih hne₁ hext₁ π₀ cfg₀ h₀ ⟨rest₀, hπ₀⟩
  intro π₀ cfg₀ h₀ hpfix
  exact hmain h (by rw [hq]; norm_num) hext_full π₀ cfg₀ h₀ hpfix



/-! # A-1 装配(T6.4 主体):CBTM 层接受路径每前缀头 ∈ [0, 4L'](g' = [] 情形)。
   链:接受 TapeSteps + noTerm → accept_path_no_trap(no101) → accept_path_is_good_block_path
   (GoodBlockPath) → 桥(§3)逐块首对应(头 = 4·Sym头) → Sym 头界(r7_accept_path_prefix_inside
   排 100 后 < L';A-3 下界 ≥ 0) → 块内 block12/a1(12 步 ∈ [4p-4, 4p+4],p ≥ 1 抬下界 0)。
   下界分工:块内前缀负头 ⇔ 块尾 dir = L(相位 8-11 同向单调)——p = 0 且 dir = L 的块
   由链级排除(块末头 -4:后续块首 blockCorrespond 与 A-3 Sym 头 ≥ 0 矛盾;末块态 100 无
   L 入边——q12suffix 23 读 #ₗ R)。块级引理两件:
     · a1_block12_head_bound_all(p 任意):12 步块前缀头 ∈ [-4, 4p+4] ∩ 上界(block12 现成)
     · a1_block12_head_ge0_if(p ≥ 1):前缀头 ≥ 0(a1_block_head_bounds 现成)
   链级装配件见 §6(GoodBlockPath 归纳 + 桥 + r7/A-3 Sym 界)。 -/

/-- 12 步块(相位 0 起)前缀头下界:p ≥ 1 时 ≥ 0(a1 版)。 -/
lemma a1_block_prefix_nonneg {w : List F4} {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {p : ℤ} {q : ℕ}
    (h : TapeSteps subsetSumCBTM w cfgc π cfgc')
    (hlen : π.length = 12)
    (hq0 : cfgc.state = encodeState q 0 0)
    (hp : cfgc.headPos = 4 * p)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (hp1 : p ≥ 1) :
    ∀ j : ℕ, j ≤ 12 →
      ∃ cfgj : CBTMConfig subsetSumCBTM w,
        TapeSteps subsetSumCBTM w cfgc (π.take j) cfgj ∧
        (0 : ℤ) ≤ cfgj.headPos ∧ cfgj.headPos ≤ 4 * p + 4 := by
  intro j hj
  have hj' : j ≤ π.length := by simpa [hlen] using hj
  rcases (a1_block_head_bounds h hlen hq0 hp htrap hp1).1 j hj' with ⟨cfgj, hpfx, hIcc⟩
  refine ⟨cfgj, hpfx, ?_, ?_⟩
  · exact hIcc.1
  · exact hIcc.2






/-! §6a TapeSteps 拼接分解(逆向):全长路径按 π₁ 切出中间 cfg(照抄 symSteps_append_decomp)。 -/

lemma tapeSteps_append_decomp {M : CBTM} {input : List F4} {cfg₀ cfg₂ : CBTMConfig M input}
    (π₁ π₂ : ComputationPath)
    (h : TapeSteps M input cfg₀ (π₁ ++ π₂) cfg₂) :
    ∃ cfg₁ : CBTMConfig M input, TapeSteps M input cfg₀ π₁ cfg₁ ∧ TapeSteps M input cfg₁ π₂ cfg₂ := by
  have main : ∀ (n : ℕ), ∀ (π₂ : ComputationPath), π₂.length = n →
      ∀ {cfg₂ : CBTMConfig M input}, TapeSteps M input cfg₀ (π₁ ++ π₂) cfg₂ →
        ∃ cfg₁ : CBTMConfig M input, TapeSteps M input cfg₀ π₁ cfg₁ ∧ TapeSteps M input cfg₁ π₂ cfg₂ := by
    intro n
    induction n with
    | zero =>
        intro π₂ hlen cfg₂ hsteps
        have hπ₂ : π₂ = [] := by simpa using hlen
        subst π₂
        exact ⟨cfg₂, by simpa using hsteps, TapeSteps.nil⟩
    | succ n ih =>
        intro π₂ hlen cfg₂ hsteps
        by_cases hπ : π₂ = []
        · subst π₂
          exact ⟨cfg₂, by simpa using hsteps, TapeSteps.nil⟩
        · rcases list_snoc_decomp hπ with ⟨π₂₀, last₂, hπeq⟩
          have hne : π₁ ++ π₂ ≠ [] := by
            intro hc
            exact hπ (list_append_eq_nil hc).2
          have hsplit := Mp.SymToF4.tapeSteps_split_last hsteps hne
          rcases hsplit with ⟨step₂, πₜ, cfg₁₂, hs, hprev₂, hfrom₂, hread₂, htrans₂, hcfg₂⟩
          have hpi : πₜ = π₁ ++ π₂₀ := by
            have hfull : (π₁ ++ π₂₀) ++ [last₂] = πₜ ++ [step₂] := by
              simpa [List.append_assoc, hπeq] using hs
            simpa using (list_snoc_inj hfull).1.symm
          have hlen₂₀ : π₂₀.length = n := by
            have hlen' : (π₂₀ ++ [last₂]).length = n + 1 := by
              simpa [hπeq] using hlen
            simpa using hlen'
          rcases ih π₂₀ hlen₂₀ (by simpa [hpi] using hprev₂) with ⟨cfg₁, hseg₁, hseg₂⟩
          have hlast' : last₂ = step₂ := by
            have hfull : (π₁ ++ π₂₀) ++ [last₂] = (π₁ ++ π₂₀) ++ [step₂] := by
              simpa [List.append_assoc, hπeq, hpi] using hs
            have hsing := list_append_left_cancel hfull
            injection hsing
          have hπ₂eq : π₂ = π₂₀ ++ [step₂] := by
            simpa [hlast'] using hπeq
          have hstep : TapeSteps M input cfg₁₂ [step₂] (stepConfig cfg₁₂ step₂.result) := by
            exact Mp.SymToF4.TapeSteps.cons [] step₂ cfg₁₂ (Mp.SymToF4.TapeSteps.nil)
              hfrom₂ hread₂ htrans₂
          refine ⟨cfg₁, hseg₁, ?_⟩
          rw [hπ₂eq, hcfg₂]
          exact Mp.tapeSteps_append hseg₂ hstep
  exact main π₂.length π₂ rfl h



/-- TapeSteps 确定性(同路径同起点 → 同终点)。照抄 sym_steps_det。 -/
lemma tapeSteps_det {M : CBTM} {input : List F4} {cfg₀ cfg₁ cfg₂ : CBTMConfig M input}
    (π : ComputationPath) (h₁ : TapeSteps M input cfg₀ π cfg₁) (h₂ : TapeSteps M input cfg₀ π cfg₂) :
    cfg₁ = cfg₂ := by
  revert cfg₂
  induction h₁ with
  | nil =>
      intro cfg₂ h₂
      exact (tapeSteps_empty h₂ rfl).symm
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      intro cfg₂ h₂
      have hne₂ : π₀ ++ [step] ≠ [] := by simp
      have hsp₂ := Mp.SymToF4.tapeSteps_split_last h₂ hne₂
      rcases hsp₂ with ⟨step₂, π₂, cfg₂₀, hs₂, hprev₂, hfrom₂, hread₂, htrans₂, hcfg₂⟩
      have hsnoc := snoc_eq_snoc (hs₂.symm : π₂ ++ [step₂] = π₀ ++ [step])
      rcases hsnoc with ⟨hπ, hst⟩
      subst π₂
      subst step₂
      have hcfg' : cfg' = cfg₂₀ := ih hprev₂
      subst cfg'
      rw [hcfg₂]


end Mp
