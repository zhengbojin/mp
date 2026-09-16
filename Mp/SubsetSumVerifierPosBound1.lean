/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierPosBound
import Mp.SubsetSumVerifierReverse10
import Mp.SubsetSumVerifierReverse7L3
import Mp.SubsetSumVerifierCBTM6
import Mp.SubsetSumCompile

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
# PosBound1：A-1 主定理（主控接管，2026-09-09）

目标：CBTM 层接受路径的每前缀头 ∈ [0, 4L']（g' = [] 情形；x = encodeInstanceF4 inst）。

装配链（素材全部就绪，见 PosBound §1-§6a）：
  接受 TapeSteps h + hacc
  → htrap := accept_path_no_trap（Compile:733）
  → hbp := accept_path_is_good_block_path（CBTM6:1286，hcorr0 := initialBlockCorrespond，
     hq0 := symInitialConfig 态 ≤ 101）
  → project_path（CBTM3:1946）⟹ ⟨πs, cfgs', hreach, hcorr', hlen12⟩（Sym 接受路径）
  → good_block_path_head_corresp（PosBound:556）⟹ 逐 k 块首对应
     （cfgcm.headPos = 4·cfgsm.headPos、cfgcm.state = encodeState cfgsm.state 0 0、相位 0）
  → Sym 头界：cfgsm 头 ≥ 0（A-3 sym_accept_prefix_head_nonneg）；cfgsm 头 < L' 或态 = 100
     （r7_accept_path_prefix_inside R7L3:3145）；态 = 100 分支用 q12_head_invariant 直接推论
     （本文件 L1：100 态可达 cfg 头 ≤ |input|）。
  → 块内（π₀ 落在块 k 的 j 段）：a1_block_prefix_nonneg（p ≥ 1）给 [0, 4p+4]；
     p = 0 块 = 初始块（k = 0）——块首头 0 的唯一性 + 初始块 12 相位无负头（子引理 L2，待相位表验证）。
  → 收尾代数：0 ≤ 4p+4 ≤ 4L' = |x|。

L2（初始块无负头）待办：初始块 = 0 态读 #ₗ 的 12 相位编译，相位 0-7 前缀偏移 ∈ {0,1,2,3,2,1,0,0}
（已绿素材），相位 8-11 净位移 = 符号步方向 R（0 态读 boundary → R）⟹ 前缀头 ≥ 0。

M1（上界）装配步骤（2026-09-09 定稿，待实施）：
  h：接受 TapeSteps（x = encodeInstanceF4 inst，wS = encodeInstanceSym inst，x = flat4F4 wS）
  1. htrap := accept_path_no_trap h hacc
  2. hbp := accept_path_is_good_block_path h hacc htrap
       (initialBlockCorrespond wS)（hq0: (symInitialConfig wS).state ≤ 101 by dsimp/norm_num）
  3. hbridge := good_block_path_head_corresp x wS (initialConfig…) (symInitialConfig wS)
       π cfg hcorr0 hbp htrap ⟹ ⟨πs, cfgs', hsSym, hcorr', hlen12, hhead⟩
     （hsSym : SymSteps init πs cfgs'；hhead k : 块首 cfgcm，SymSteps (πs.take k) cfgsm ∧
       TapeSteps (π.take (12k)) cfgcm ∧ cfgcm.headPos = 4·cfgsm.headPos ∧
       cfgcm.state = encodeState cfgsm.state 0 0）
  4. hreach := (symSteps_initial_iff …).1 hsSym（SymReachablePath πs cfgs'）
     haccS : cfgs'.state = 100（hcorr'.1 + hacc 的 mem_image 拆解，照 Compile:800 模板）
  5. 前缀 π₀ cfg₀（h₀ : TapeSteps initial π₀ cfg₀、hp : IsPrefix π₀ π）：
     a. π₀ = π：tapeSteps_det π h h₀ ⟹ cfg₀ = cfg ⟹ 头 = 4·cfgs'.headPos（hcorr'.2）
        ≤ 4L'（q12_weak wS πs cfgs' hreach haccS，flat4F4_length: |x| = 4·|wS|）
     b. π₀ ⊊ π：n₀ := π₀.length、k := n₀/12、j := n₀%12；n₀ < 12·πs.length
        ⟹ k+1 ≤ πs.length（hhead k 与 hhead (k+1) 可用）
        · 块首：rcases hhead k ⟹ cfgsm/cfgcm/hSym_k/hTap_k/hpk（头 = 4·cfgsm.headPos）
        · cfg₀ 连接：π₀ = π₀.take(12k) ++ π₀.drop(12k)；tapeSteps_append_decomp h₀
          ⟹ ⟨cfg₁, h₁, h₂⟩；π₀.take(12k) = π.take(12k)（prefix_eq_take + take_take）
          ⟹ tapeSteps_det h₁ hTap_k ⟹ cfg₁ = cfgcm；h₂ : TapeSteps cfgcm mid cfg₀
          （mid := π₀.drop(12k)，mid.length = j ≤ 12）
        · 块 k+1 全长：rcases hhead (k+1) ⟹ 块首 cfgcm₁；decomp hTap_{k+1}
          （π.take(12(k+1)) = π.take(12k) ++ 后 12 步，drop_take_add/block_drop_length）
          ⟹ hb12 : TapeSteps cfgcm（后 12 步段）cfgcm₁（12 步、相位 0（hstk）、头 4p（hpk））
        · block12_prefix_pos_inside hb12（htrap 块内：block_step_mem + trap_mem_of_get）于 m = j：
          ⟨cfgj, …, 4p-4 ≤ cfgj.headPos ≤ 4p+4⟩；mid = (块 k+1).take j
          （drop_take_add/take_take 化简）⟹ det h₂ hpfx ⟹ cfg₀ = cfgj
        · p 界：cfgsm 头 ≤ L'-1：
          r7_accept_path_prefix_inside inst …（πs, cfgs' 接受）于前缀 (πs.take k, cfgsm)：
          cfgsm.state = 100 ∨ cfgsm.headPos < L'
          — 100 分支：ext_path_state100_head_le_enc（L2b）⟹ ≤ L'-1
          — < L' 分支：omega ⟹ ≤ L'-1
        · 收尾：cfg₀.headPos ≤ 4p+4 ≤ 4L' = |x|（flat4F4_length；omega）
  M1 上界已绿（d6a4f9d：a1_accept_path_prefix_head_le）。

M2（下界 0 ≤ 头）设计（待实施）：
  对前缀 π₀（k = n₀/12 ≥ 1 块内）：块首 Sym 头 p = cfgsm.headPos——
    · p ≥ 1 块：a1_block_prefix_nonneg（p ≥ 1 前提）给块内前缀头 ∈ [0, 4p+4]；
    · p = 0 块（k ≥ 1）：块首头 0 的态只可能 ∈ {0（初始，k=0 排除）, 23, 9, 77, 85, …}（头 0 可达态，
      读 #ₗ boundary false 转向 R/100）——块内负头唯一候选 = 相位 8-11 的 L 前缀；
      表级验证（decide）：这些态在头 0 读 #ₗ 的块（12 相位）无负前缀头（L2'）。
  初始块（k = 0，块首 = initialConfig 头 0 态 0）：L2 待表级验证（0 态读 #ₗ 块无负头）。
  合并后：0 ≤ cfg₀.headPos（块内 ≥ 0 或 = 4p+偏移 ≥ 0）。
-/

namespace Mp

open SymToF4

-- ==============================================================================
-- 辅助件 A：flat4F4 长度 / IsPrefix 的 take 形式 / htrap 的下标↔mem 转换
-- ==============================================================================

/-- IsPrefix 的 take 形式：π₀ ⊆ π ⟹ π₀ = π.take π₀.length。 -/
lemma prefix_eq_take {α : Type} {π₀ π : List α} (hp : List.IsPrefix π₀ π) :
    π₀ = π.take π₀.length := by
  rcases hp with ⟨rest, hπ⟩
  rw [← hπ]
  simp [List.take_append_of_le_length]

/-- 下标版 no-101 前提 ⟹ mem 版。 -/
lemma trap_mem_of_get {π : ComputationPath}
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∀ step ∈ π, (decodeState step.result.nextState).1 ≠ 101 := by
  intro step hmem
  rcases (List.mem_iff_get.mp hmem) with ⟨k, hk⟩
  rw [← hk]
  exact htrap k.1 k.2

/-- mem 版 no-101 前提 ⟹ 下标版。 -/
lemma trap_get_of_mem {π : ComputationPath}
    (htrap : ∀ step ∈ π, (decodeState step.result.nextState).1 ≠ 101) :
    ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := by
  intro k hk
  exact htrap (π.get ⟨k, hk⟩) (List.getElem_mem hk)

/-- take/drop 嵌套：drop n (take (n+m) l) = take m (drop n l)。 -/
lemma drop_take_add {α : Type} (l : List α) (n m : ℕ) :
    (l.take (n + m)).drop n = (l.drop n).take m := by
  rw [List.drop_take]
  congr 1
  omega

/-- 块内（12(k+1) 前缀的 drop(12k) 段）长度 = 12。 -/
lemma block_drop_length {π : ComputationPath} {k : ℕ}
    (hlen : 12 * (k + 1) ≤ π.length) :
    ((π.take (12 * (k + 1))).drop (12 * k)).length = 12 := by
  rw [List.length_drop, List.length_take]
  have hmin : min (12 * (k + 1)) π.length = 12 * (k + 1) := by
    exact Nat.min_eq_left hlen
  rw [hmin]
  omega

/-- 12·k ≤ 12·(k+1) ≤ π.length 时,drop(12k)(take(12(k+1)) π) 的元素第 i 步 =
    π 的第 12k+i 步(仅 mem 版使用:块内步 ∈ π)。 -/
lemma block_step_mem {π : ComputationPath} {k : ℕ} :
    ∀ step ∈ (π.take (12 * (k + 1))).drop (12 * k), step ∈ π := by
  intro step hs
  exact List.mem_of_mem_take (List.mem_of_mem_drop hs)

-- ==============================================================================
-- 辅助件 B：可延拓路径上 100 态配置的头 ≤ |enc| - 1（M1 的 100 分支块首 p 界）
--   100 入边 = 23 读 boundary R ∨ 100 S（sym_into_100，PosBound:1902）；
--   23 态头 ≤ |enc|-2（束 P23，Reverse7L3:1148 链第 8 分量）⟹ R 后 ≤ |enc|-1；
--   100 S 自环保持头（ih）。块内上界（block12 4p+4）要求 p ≤ |enc|-1 ✓
--   （非 100 分支用 r7_accept_path_prefix_inside：头 < |enc| ⟹ p ≤ |enc|-1）。
-- ==============================================================================

/-- 束 P23 提取：可延拓路径上 23 态配置的头 ≤ |enc| - 2。 -/
lemma pb1_bundle_23_head (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hext : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
      (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) :
    cfg.state = 23 → cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 2 : ℤ) := by
  intro h23
  have hb := (r7_path_bundle inst hm hpos htarget π cfg h hext).2.2.2.2.2.2.2.1
  exact hb h23

/-- L2b：可延拓路径上 100 态配置的头 ≤ |enc| - 1（M1 的 100 分支块首 p 界）。
    100 入边两分支：23 读 boundary R（P23 头 ≤ L-2 → R 后 ≤ L-1）∨ 100 S（ih 头保持）。 -/
lemma ext_path_state100_head_le_enc (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : List SymStep} {cfg : SymConfig}
    (h : SymReachablePath VerifierSym.transition (encodeInstanceSym inst) π cfg)
    (hq : cfg.state = 100)
    (hext : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
      (π ++ π₂) cfg₂ ∧ cfg₂.state = 100) :
    cfg.headPos ≤ (((encodeInstanceSym inst).length : ℕ) - 1 : ℤ) := by
  induction h with
  | nil => simp [symInitialConfig, VerifierSym.qStart] at hq
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      have hnext : step.result.nextState = 100 := by
        dsimp [symStepConfig] at hq
        exact hq
      have hq' : cfg₁.state < 102 := q12_path_state_lt102 (encodeInstanceSym inst) π₀ cfg₁ hprev
      have htrans' : step.result ∈ VerifierSym.transition (cfg₁.state, step.readSym) := by
        simpa [hread] using htrans
      have hinto := sym_into_100 cfg₁.state hq' step.readSym step.result htrans' hnext
      have hext₁ : ∃ π₂' cfg₂', SymReachablePath VerifierSym.transition (encodeInstanceSym inst)
          (π₀ ++ π₂') cfg₂' ∧ cfg₂'.state = 100 := by
        rcases hext with ⟨π₂, cfg₂, hfull, hq₂⟩
        refine ⟨[step] ++ π₂, cfg₂, ?_, hq₂⟩
        simpa [List.append_assoc] using hfull
      rcases hinto with h23 | h100
      · have hle23 := pb1_bundle_23_head inst hm hpos htarget (π := π₀) (cfg := cfg₁) hprev hext₁ h23.1
        have hpos1 : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos + 1 := by
          dsimp [symStepConfig]
          rw [h23.2.2]
          simp [Dir.toInt]
        rw [hpos1]
        omega
      · have hih := ih h100.1 hext₁
        have hpos1 : (symStepConfig cfg₁ step.result).headPos = cfg₁.headPos := by
          dsimp [symStepConfig]
          rw [h100.2]
          simp [Dir.toInt]
        rw [hpos1]
        exact hih

-- ==============================================================================
-- M1：接受路径每前缀头 ≤ |x|（上界；x = encodeInstanceF4 inst，g' = [] 情形）
-- ==============================================================================

/-- M1 主定理：接受路径（CBTM 层）的每前缀终点头 ≤ |x| = 4·|wS|。
    装配：accept_path_no_trap → accept_path_is_good_block_path（initialBlockCorrespond）
    → good_block_path_head_corresp（逐 k 块首对应）→ 前缀切块（k = n₀/12、j = n₀%12）
    → 块内 block12（上界 4p+4）→ 块首 Sym 头 p ≤ |wS|-1（r7 或 L2b）。 -/
lemma a1_accept_path_prefix_head_le (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst)},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π cfg →
      cfg.state ∈ acceptStates4 →
      ∀ π₀ cfg₀,
        TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
          (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π₀ cfg₀ →
        List.IsPrefix π₀ π →
        cfg₀.headPos ≤ ((encodeInstanceF4 inst).length : ℤ) := by
  let wS := encodeInstanceSym inst
  have hx : encodeInstanceF4 inst = flat4F4 wS := by rfl
  intro π cfg h hacc π₀ cfg₀ h₀ hp
  have htrap : ∀ k (hk : k < π.length),
      (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := accept_path_no_trap h hacc
  have hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (encodeInstanceF4 inst))
      (symInitialConfig wS) := by
    change blockCorrespond (initialConfig subsetSumCBTM (flat4F4 wS)) (symInitialConfig wS)
    exact initialBlockCorrespond wS
  have hq0 : (symInitialConfig wS).state ≤ 101 := by
    dsimp [symInitialConfig, SymConfig.mk, VerifierSym.qStart]
    norm_num
  have hbp : GoodBlockPath (encodeInstanceF4 inst)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π cfg :=
    accept_path_is_good_block_path h hacc htrap hcorr0 hq0
  have hbridge := good_block_path_head_corresp (encodeInstanceF4 inst) wS
    (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) (symInitialConfig wS)
    π cfg hcorr0 hbp htrap
  rcases hbridge with ⟨πs, cfgs', hsSym, hcorr', hlen12, hhead⟩
  have hreach : SymReachablePath VerifierSym.transition wS πs cfgs' :=
    (symSteps_initial_iff VerifierSym.transition wS πs cfgs').1 hsSym
  have haccS : cfgs'.state = VerifierSym.qAccept := by
    rcases Finset.mem_image.mp hacc with ⟨reg, hreg, hacc'⟩
    have hst : cfg.state = encodeState cfgs'.state 0 0 := hcorr'.1
    have hdec := decodeState_encodeState VerifierSym.qAccept 0 reg (by norm_num)
      (by simpa [regBound] using Finset.mem_range.mp hreg)
    have hdec2 := decodeState_encodeState cfgs'.state 0 0 (by norm_num) (by norm_num)
    have hcong := congrArg decodeState (show cfg.state = encodeState VerifierSym.qAccept 0 reg by
      rw [← hacc'])
    rw [hst] at hcong
    rw [hdec, hdec2] at hcong
    exact congrArg Prod.fst hcong
  have hendSym : cfgs'.headPos ≤ (wS.length : ℤ) := by
    exact q12_weak wS πs cfgs' hreach haccS
  by_cases hfull : π₀ = π
  · subst π₀
    have hdet : cfg₀ = cfg := (tapeSteps_det π h h₀).symm
    subst cfg₀
    rw [hcorr'.2.1]
    have hlenx : (encodeInstanceF4 inst).length = 4 * wS.length := by
      change (flat4F4 wS).length = 4 * wS.length
      simp [flat4F4_length]
    rw [hlenx]
    have h4 : (0 : ℤ) ≤ 4 := by norm_num
    exact mul_le_mul_of_nonneg_left hendSym h4
  · let n₀ := π₀.length
    let k := n₀ / 12
    have htake₀ : π₀ = π.take n₀ := by simpa [n₀] using (prefix_eq_take hp)
    have hn₀_le : n₀ ≤ π.length := by
      dsimp [n₀]
      rw [htake₀]
      simp [List.length_take]
    have hn₀_lt : n₀ < π.length := by
      by_contra hge
      have htake_all : π.take n₀ = π := by
        exact (List.take_eq_self_iff π).2 (Nat.le_of_not_gt hge)
      apply hfull
      rw [htake₀, htake_all]
    have hlen12' : π.length = 12 * πs.length := by
      rw [← hlen12]
      simp [Nat.mul_comm]
    have hn₀_lt12 : n₀ < 12 * πs.length := by
      rw [← hlen12']
      exact hn₀_lt
    have hk_lt : k < πs.length := by
      have hd := (Nat.div_lt_iff_lt_mul (k := 12) (y := πs.length) (by norm_num : 0 < 12)).2 (by
        simpa [Nat.mul_comm] using hn₀_lt12)
      simpa [k] using hd
    have hk1 : k + 1 ≤ πs.length := by omega
    rcases hhead k (by omega) with ⟨cfgsm, cfgcm, hSym_k, hTap_k, hpk, hstk⟩
    rcases hhead (k + 1) hk1 with ⟨cfgsm1, cfgcm1, hSym_k1, hTap_k1, hpk1, hstk1⟩
    have hreach_k : SymReachablePath VerifierSym.transition wS (πs.take k) cfgsm :=
      (symSteps_initial_iff VerifierSym.transition wS (πs.take k) cfgsm).1 hSym_k
    have hp_le : cfgsm.headPos ≤ ((wS.length : ℕ) - 1 : ℤ) := by
      have hr7 := r7_accept_path_prefix_inside inst hm hpos htarget πs cfgs' hreach haccS
        (πs.take k) cfgsm hreach_k (by
          refine ⟨πs.drop k, ?_⟩
          simp [List.take_append_drop])
      rcases hr7 with h100 | hlt
      · have hextm : ∃ π₂ cfg₂, SymReachablePath VerifierSym.transition wS
            ((πs.take k) ++ π₂) cfg₂ ∧ cfg₂.state = 100 := by
          refine ⟨πs.drop k, cfgs', ?_, ?_⟩
          · simpa [List.take_append_drop] using hreach
          · change cfgs'.state = VerifierSym.qAccept
            exact haccS
        have hle := ext_path_state100_head_le_enc inst hm hpos htarget (π := πs.take k)
          (cfg := cfgsm) hreach_k h100 hextm
        exact hle
      · have hLpos : 0 < (wS.length : ℤ) := by
          change 0 < ((encodeInstanceSym inst).length : ℤ)
          have hL : 0 < (encodeInstanceSym inst).length := by
            rw [r7_enc_len inst]
            omega
          exact_mod_cast hL
        have hw : 1 ≤ wS.length := by
          have hw0 : 0 < wS.length := by exact_mod_cast hLpos
          omega
        have hcast : ((wS.length : ℕ) - 1 : ℤ) = (wS.length : ℤ) - 1 := by
          simpa using (Int.ofNat_sub (m := 1) (n := wS.length) hw)
        rw [hcast]
        have h1 : (1 : ℤ) ≤ (wS.length : ℤ) := by exact_mod_cast hw
        nlinarith
    have h12k_le : 12 * k ≤ n₀ := by
      have hd := Nat.div_mul_le_self n₀ 12
      simpa [k, Nat.mul_comm] using hd
    have htake_eq : π₀.take (12 * k) = π.take (12 * k) := by
      rw [htake₀, List.take_take]
      rw [Nat.min_eq_left h12k_le]
    have hdec₀ := tapeSteps_append_decomp (π₁ := π₀.take (12 * k))
      (π₂ := π₀.drop (12 * k))
      (by simpa [List.take_append_drop] using h₀)
    rcases hdec₀ with ⟨cfg₁, h₁, h₂⟩
    have hdet₁ : cfg₁ = cfgcm := by
      exact tapeSteps_det (π.take (12 * k)) (by simpa [htake_eq] using h₁) hTap_k
    have h₂' : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
        (π₀.drop (12 * k)) cfg₀ := by
      simpa [hdet₁] using h₂
    -- 块 k+1 全长（12 步从 cfgcm）
    have htt : (π.take (12 * (k + 1))).take (12 * k) = π.take (12 * k) := by
      rw [List.take_take]
      rw [Nat.min_eq_left (by omega : 12 * k ≤ 12 * (k + 1))]
    have hdec₁ := tapeSteps_append_decomp (π₁ := π.take (12 * k))
      (π₂ := (π.take (12 * (k + 1))).drop (12 * k))
      (by
        rw [← htt]
        simpa [List.take_append_drop] using hTap_k1)
    rcases hdec₁ with ⟨cfg₂, h₂a, h₂b⟩
    have hdet₂ : cfg₂ = cfgcm := tapeSteps_det (π.take (12 * k)) h₂a hTap_k
    have hb12 : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
        ((π.take (12 * (k + 1))).drop (12 * k)) cfgcm1 := by
      rw [← hdet₂]
      exact h₂b
    have hblen : ((π.take (12 * (k + 1))).drop (12 * k)).length = 12 := by
      have hle : 12 * (k + 1) ≤ π.length := by
        have hle' : 12 * (k + 1) ≤ 12 * πs.length := Nat.mul_le_mul_left 12 hk1
        simpa [hlen12', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle'
      exact block_drop_length hle
    have htr12 : ∀ m (hm : m < ((π.take (12 * (k + 1))).drop (12 * k)).length),
        (decodeState (((π.take (12 * (k + 1))).drop (12 * k)).get ⟨m, hm⟩).result.nextState).1 ≠ 101 := by
      intro m hm
      have hmem : ∀ step ∈ (π.take (12 * (k + 1))).drop (12 * k),
          (decodeState step.result.nextState).1 ≠ 101 := by
        intro step hs
        exact (trap_mem_of_get htrap) step (block_step_mem (π := π) (k := k) step hs)
      exact trap_get_of_mem hmem m hm
    have hblk := block12_prefix_pos_inside (p := cfgsm.headPos) hb12 hblen hstk hpk htr12
    have hmidlen : (π₀.drop (12 * k)).length ≤ 12 := by
      rw [List.length_drop]
      have hjk : 12 * k + n₀ % 12 = n₀ := by
        simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
      have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
      omega
    rcases hblk (π₀.drop (12 * k)).length hmidlen with ⟨cfgj, hpfxj, hIcc⟩
    -- mid 与块前缀同一（cfg₀ = cfgj）
    have hmid_eq : π₀.drop (12 * k) =
        ((π.take (12 * (k + 1))).drop (12 * k)).take (π₀.drop (12 * k)).length := by
      rw [htake₀]
      have hlen' : ((π.take n₀).drop (12 * k)).length = n₀ - 12 * k := by
        rw [List.length_drop, List.length_take]
        rw [Nat.min_eq_left hn₀_le]
      rw [hlen']
      have hA : 12 * (k + 1) - 12 * k = 12 := by omega
      have hx : n₀ - 12 * k ≤ 12 := by
        have hjk : 12 * k + n₀ % 12 = n₀ := by
          simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
        have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
        omega
      calc
        (π.take n₀).drop (12 * k)
            = (π.drop (12 * k)).take (n₀ - 12 * k) := by
                rw [List.drop_take]
        _ = ((π.take (12 * (k + 1))).drop (12 * k)).take (n₀ - 12 * k) := by
                rw [List.drop_take]
                rw [List.take_take]
                rw [hA]
                rw [Nat.min_eq_left hx]
    have hdet₀ : cfg₀ = cfgj := by
      have hsame : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
          (π₀.drop (12 * k)) cfgj := by
        rw [hmid_eq]
        exact hpfxj
      exact tapeSteps_det (π₀.drop (12 * k)) h₂' hsame
    rw [hdet₀]
    rcases hIcc with ⟨hlo, hhi⟩
    -- cfgj ≤ 4p+4 ≤ 4L' = |x|
    have hlenx : (encodeInstanceF4 inst).length = 4 * wS.length := by
      change (flat4F4 wS).length = 4 * wS.length
      simp [flat4F4_length]
    rw [hlenx]
    simp [Nat.cast_mul]
    have h4p : 4 * cfgsm.headPos + 4 ≤ 4 * (wS.length : ℤ) := by
      have hpz : cfgsm.headPos ≤ ((wS.length : ℕ) : ℤ) - 1 := hp_le
      have hwpos : (0 : ℤ) ≤ (wS.length : ℕ) := by simp
      nlinarith
    -- hhi : cfgj.headPos ≤ 4·cfgsm.headPos + 4（注意 hpk : cfgcm.headPos = 4·cfgsm.headPos，
    -- block12 的输出用 p（cfgcm.headPos = 4p 的 p）——hIcc 的 4p+4 = 4·cfgsm.headPos+4？
    -- block12 的 p 是参数（hp0 : cfgcm.headPos = 4*p）——我们传入的 p 未显式给出——hblk 的 p 是隐式?
    -- block12_prefix_pos_inside 的 {p} 隐式——从 hpk(4p = 4·cfgsm.headPos)推 p = cfgsm.headPos?
    -- 实际上我们调用 hblk 时 p 是隐式（由 hp0 : cfgcm.headPos = 4*p 统一）——hIcc : 4p-4 ≤ … ≤ 4p+4
    -- 其中 p 已被统一为?——hpk : cfgcm.headPos = 4 * cfgsm.headPos——block12 的 hp0 : cfgcm.headPos = 4*p——
    -- 我传的 hpk 意味着 p := cfgsm.headPos（统一）——hIcc 的上界 = 4·cfgsm.headPos + 4 ✓
    nlinarith
-- ==============================================================================
-- M2 辅助件 T1/T2：移动段（相位 8-11）的方向 = reg 中存储的符号步方向，
--   且相位 8-10 的步保持 reg 不变 ⟹ 块内移动段 4 步位移相同（= e）。
--   表级，照 Reverse10 trans4_phase*_of_nontrap 的 split_ifs 模式。
-- ==============================================================================

/-- 相位 8-11 的 nphase（陷阱态相位）< 12。 -/
lemma ge8_nphase_lt12 (ph : ℕ) (hph1 : 8 ≤ ph) (hph2 : ph < 12) :
    (if ph = 11 then 0 else ph + 1) < 12 := by
  by_cases h11 : ph = 11 <;> simp [h11] <;> omega

/-- 陷阱结果（相位 8-11 双例第二肢 / 单例）的 nextState 解码 = 101。 -/
lemma trap_next_decode_101_ge8 (ph : ℕ) (s : F4) (r : CBTMTransResult)
    (h : r = CBTMTransResult.mk (encodeState 101 (if ph = 11 then 0 else ph + 1) 0) s Dir.S ∨
         r = CBTMTransResult.mk (encodeState 101 (if ph = 11 then 0 else ph + 1) 0) s Dir.R)
    (hph1 : 8 ≤ ph) (hph2 : ph < 12) : (decodeState r.nextState).1 = 101 := by
  rcases h with h | h <;> rw [h]
  · apply decodeState_encodeState_q_eq
    have hn : (if ph = 11 then 0 else ph + 1) * regBound + 0 < stepsPerSym * regBound := by
      have hlt := ge8_nphase_lt12 ph hph1 hph2
      have hm : (if ph = 11 then 0 else ph + 1) * regBound < 12 * regBound :=
        Nat.mul_lt_mul_of_pos_right hlt (by norm_num [regBound])
      simpa [stepsPerSym] using hm
    exact hn
  · apply decodeState_encodeState_q_eq
    have hn : (if ph = 11 then 0 else ph + 1) * regBound + 0 < stepsPerSym * regBound := by
      have hlt := ge8_nphase_lt12 ph hph1 hph2
      have hm : (if ph = 11 then 0 else ph + 1) * regBound < 12 * regBound :=
        Nat.mul_lt_mul_of_pos_right hlt (by norm_num [regBound])
      simpa [stepsPerSym] using hm
    exact hn

/-- T1：相位 8-11（移动段）的 nontrap 非-101 步，方向 = (decodeResult reg).moveDir
    （reg = st % regBound；transition4 移动段分支 d := match r.moveDir，match 恒等）。 -/
lemma trans4_ge8_moveDir_of_reg (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) :
    8 ≤ (decodeState st).2.1 → (decodeState st).2.1 < 12 →
    (decodeState r.nextState).1 ≠ 101 → (decodeState st).1 ≠ 101 →
    r.moveDir = (decodeResult (st % regBound)).moveDir := by
  intro hph1 hph2 hnt hq
  have hge3 : ¬ (decodeState st).2.1 < 3 := by omega
  have hne3 : (decodeState st).2.1 ≠ 3 := by omega
  have hge8 : ¬ (decodeState st).2.1 < 8 := by omega
  unfold transition4 at hr
  dsimp at hr
  rw [if_neg hge3] at hr
  rw [if_neg (by intro h; exact hne3 h)] at hr
  rw [if_neg hge8] at hr
  rw [if_pos hph2] at hr
  by_cases him : F4.im s
  · -- im=true：双例 {好路径肢, 陷阱肢(S)}
    simp [him] at hr
    rcases hr with hr | hr
    · rw [hr]
      dsimp
      simp [decodeState]
      cases hd : (decodeResult (st % regBound)).moveDir <;> rfl
    · exfalso
      exact hnt (trap_next_decode_101_ge8 (decodeState st).2.1 F4.zero r
        (Or.inl hr) hph1 hph2)
  · by_cases hq101 : (decodeState st).1 = 101
    · exfalso
      exact hq hq101
    · -- im=false、q≠101：单例好路径
      simp [him, hq101] at hr
      rw [hr]
      dsimp
      simp [decodeState]
      cases hd : (decodeResult (st % regBound)).moveDir <;> rfl

/-- T2：相位 8-10 的 nontrap 非-101 步，步后 reg（st % regBound）不变。 -/
lemma trans4_ge8_nextState_reg_preserved (st : ℕ) (s : F4) (r : CBTMTransResult)
    (hr : r ∈ transition4 st s) :
    8 ≤ (decodeState st).2.1 → (decodeState st).2.1 < 11 →
    (decodeState r.nextState).1 ≠ 101 → (decodeState st).1 ≠ 101 →
    (decodeState r.nextState).2.2 = (decodeState st).2.2 := by
  intro hph1 hph2 hnt hq
  have hge3 : ¬ (decodeState st).2.1 < 3 := by omega
  have hne3 : (decodeState st).2.1 ≠ 3 := by omega
  have hge8 : ¬ (decodeState st).2.1 < 8 := by omega
  have hlt12 : (decodeState st).2.1 < 12 := by omega
  have hne11 : (decodeState st).2.1 ≠ 11 := by omega
  have hph' : (decodeState st).2.1 + 1 < stepsPerSym := by
    dsimp [stepsPerSym]
    omega
  have hreg : (decodeState st).2.2 < regBound := by
    dsimp [decodeState]
    exact Nat.mod_lt st (by norm_num [regBound])
  unfold transition4 at hr
  dsimp at hr
  rw [if_neg hge3] at hr
  rw [if_neg (by intro h; exact hne3 h)] at hr
  rw [if_neg hge8] at hr
  rw [if_pos hlt12] at hr
  by_cases him : F4.im s
  · -- im=true：双例 {好路径肢, 陷阱肢(S)}——好路径肢 reg 不变
    simp [him] at hr
    rcases hr with hr | hr
    · rw [hr]
      simp [hne11]
      rw [decodeState_encodeState _ _ _ hph' hreg]
    · exfalso
      exact hnt (trap_next_decode_101_ge8 (decodeState st).2.1 F4.zero r
        (Or.inl hr) hph1 (by omega))
  · by_cases hq101 : (decodeState st).1 = 101
    · exfalso
      exact hq hq101
    · -- im=false、q≠101：单例好路径
      simp [him, hq101] at hr
      rw [hr]
      simp [hne11]
      rw [decodeState_encodeState _ _ _ hph' hreg]

-- ==============================================================================
-- M2 块级下界引理（p = 0 块）：12 步块从 (encodeState q 0 0, 头 0) 出发、无陷阱、
--   块尾头 ≥ 0 ⟹ 块内每前缀头 ≥ 0。
--   结构：相位 0-7 精确回摆（R,R,R,L,L,L,S,S → 前缀偏移 ∈ {1,2,3,2,1,0,0} ≥ 0，
--   相位 8 前回到 0）；相位 8-11 移动段方向 = e0（T1/T2：reg 不变 + 方向由 reg 决定），
--   块尾头 = 4·e0.toInt ≥ 0（htail）⟹ e0.toInt ≥ 0 ⟹ 移动段前缀 ≥ 0。
--   照抄 block12_prefix_pos_inside（PosBound:176）的 12 层 split_last 枚举骨架。
-- ==============================================================================

/-- p = 0 块（块首头 0）的块内前缀非负：htail（块尾头 ≥ 0）排除移动段 L。
    前提同 block12_prefix_pos_inside（hp0 : cfgc.headPos = 0 特化）。 -/
lemma p0_block_prefix_nonneg {w : List F4} {cfgc cfgc' : CBTMConfig subsetSumCBTM w}
    {π : ComputationPath} {q : ℕ}
    (h : TapeSteps subsetSumCBTM w cfgc π cfgc')
    (hlen : π.length = 12)
    (hq0 : cfgc.state = encodeState q 0 0)
    (hp0 : cfgc.headPos = 0)
    (htrap : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (htail : 0 ≤ cfgc'.headPos) :
    ∀ j : ℕ, j ≤ 12 →
      ∃ cfgj : CBTMConfig subsetSumCBTM w,
        TapeSteps subsetSumCBTM w cfgc (π.take j) cfgj ∧
        (0 : ℤ) ≤ cfgj.headPos := by
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
  have hq101_9 : (decodeState step9.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt9 (transition4_trap_q101 _ _ _ hqj ht9')
  have hq101_10 : (decodeState step10.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt10 (transition4_trap_q101 _ _ _ hqj ht10')
  have hq101_11 : (decodeState step11.fromState).1 ≠ 101 := by
    intro hqj
    exact hnt11 (transition4_trap_q101 _ _ _ hqj ht11')
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
  -- 移动段 4 步方向相同（T1 + T2：相位 8-11 reg 不变，方向由 reg 决定）
  let e0 : Dir := (decodeResult (cfg8.state % regBound)).moveDir
  have hd8₀ : step8.result.moveDir = (decodeResult (step8.fromState % regBound)).moveDir := by
    have h1 : 8 ≤ (decodeState step8.fromState).2.1 := by omega
    have h2 : (decodeState step8.fromState).2.1 < 12 := by omega
    exact trans4_ge8_moveDir_of_reg step8.fromState step8.readSym step8.result ht8' h1 h2 hnt8 hq101_8
  have hd8 : step8.result.moveDir = e0 := by
    dsimp [e0]
    simpa [hf8] using hd8₀
  have hreg9 : cfg9.state % regBound = cfg8.state % regBound := by
    have h1 : 8 ≤ (decodeState step8.fromState).2.1 := by omega
    have h2 : (decodeState step8.fromState).2.1 < 11 := by omega
    have ht2 := trans4_ge8_nextState_reg_preserved step8.fromState step8.readSym step8.result ht8' h1 h2 hnt8 hq101_8
    have hst9 : step8.result.nextState = cfg9.state := by
      rw [hc8]
      simp [stepConfig]
    rw [hst9] at ht2
    rw [hf8] at ht2
    simpa [decodeState] using ht2
  have hd9₀ : step9.result.moveDir = (decodeResult (step9.fromState % regBound)).moveDir := by
    have h1 : 8 ≤ (decodeState step9.fromState).2.1 := by omega
    have h2 : (decodeState step9.fromState).2.1 < 12 := by omega
    exact trans4_ge8_moveDir_of_reg step9.fromState step9.readSym step9.result ht9' h1 h2 hnt9 hq101_9
  have hd9 : step9.result.moveDir = e0 := by
    dsimp [e0]
    simpa [hf9, hreg9] using hd9₀
  have hreg10 : cfg10.state % regBound = cfg8.state % regBound := by
    have h1 : 8 ≤ (decodeState step9.fromState).2.1 := by omega
    have h2 : (decodeState step9.fromState).2.1 < 11 := by omega
    have ht2 := trans4_ge8_nextState_reg_preserved step9.fromState step9.readSym step9.result ht9' h1 h2 hnt9 hq101_9
    have hst10 : step9.result.nextState = cfg10.state := by
      rw [hc9]
      simp [stepConfig]
    rw [hst10] at ht2
    rw [hf9] at ht2
    have h2' : cfg10.state % regBound = cfg9.state % regBound := by
      simpa [decodeState] using ht2
    rw [h2']
    exact hreg9
  have hd10₀ : step10.result.moveDir = (decodeResult (step10.fromState % regBound)).moveDir := by
    have h1 : 8 ≤ (decodeState step10.fromState).2.1 := by omega
    have h2 : (decodeState step10.fromState).2.1 < 12 := by omega
    exact trans4_ge8_moveDir_of_reg step10.fromState step10.readSym step10.result ht10' h1 h2 hnt10 hq101_10
  have hd10 : step10.result.moveDir = e0 := by
    dsimp [e0]
    simpa [hf10, hreg10] using hd10₀
  have hreg11 : cfg11.state % regBound = cfg8.state % regBound := by
    have h1 : 8 ≤ (decodeState step10.fromState).2.1 := by omega
    have h2 : (decodeState step10.fromState).2.1 < 11 := by omega
    have ht2 := trans4_ge8_nextState_reg_preserved step10.fromState step10.readSym step10.result ht10' h1 h2 hnt10 hq101_10
    have hst11 : step10.result.nextState = cfg11.state := by
      rw [hc10]
      simp [stepConfig]
    rw [hst11] at ht2
    rw [hf10] at ht2
    have h3' : cfg11.state % regBound = cfg10.state % regBound := by
      simpa [decodeState] using ht2
    rw [h3']
    exact hreg10
  have hd11₀ : step11.result.moveDir = (decodeResult (step11.fromState % regBound)).moveDir := by
    have h1 : 8 ≤ (decodeState step11.fromState).2.1 := by omega
    have h2 : (decodeState step11.fromState).2.1 < 12 := by omega
    exact trans4_ge8_moveDir_of_reg step11.fromState step11.readSym step11.result ht11' h1 h2 hnt11 hq101_11
  have hd11 : step11.result.moveDir = e0 := by
    dsimp [e0]
    simpa [hf11, hreg11] using hd11₀
  -- 相位 0-7 净回摆到 0；块尾 = 4·e0.toInt ≥ 0 ⟹ e0 非 L
  have hpos8 : cfg8.headPos = 0 := by
    rw [hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp0]
    rw [hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
    norm_num [Dir.toInt]
  have htail_e : cfgc'.headPos = 4 * e0.toInt := by
    rw [hhead11, hhead10, hhead9, hhead8, hpos8]
    rw [hd11, hd10, hd9, hd8]
    ring
  have he0_ge0 : 0 ≤ e0.toInt := by
    have h4 : 0 ≤ 4 * e0.toInt := by
      rw [← htail_e]
      exact htail
    cases he0 : e0 with
    | R => norm_num [Dir.toInt]
    | L => exfalso
           rw [he0] at h4
           norm_num [Dir.toInt] at h4
    | S => norm_num [Dir.toInt]
  interval_cases j
  · refine ⟨cfgc, ?_, ?_⟩
    · exact TapeSteps.nil
    · rw [hp0]
  · refine ⟨cfg1, ?_, ?_⟩
    · have htake : π.take 1 = πn ++ [step0] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe0] using h0
    · rw [hhead0, hcfg0, hp0, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg2, ?_, ?_⟩
    · have htake : π.take 2 = πn ++ [step0, step1] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe1, hπe0] using h1
    · rw [hhead1, hhead0, hcfg0, hp0, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg3, ?_, ?_⟩
    · have htake : π.take 3 = πn ++ [step0, step1, step2] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe2, hπe1, hπe0] using h2
    · rw [hhead2, hhead1, hhead0, hcfg0, hp0, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg4, ?_, ?_⟩
    · have htake : π.take 4 = πn ++ [step0, step1, step2, step3] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe3, hπe2, hπe1, hπe0] using h3
    · rw [hhead3, hhead2, hhead1, hhead0, hcfg0, hp0, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg5, ?_, ?_⟩
    · have htake : π.take 5 = πn ++ [step0, step1, step2, step3, step4] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe4, hπe3, hπe2, hπe1, hπe0] using h4
    · rw [hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp0, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg6, ?_, ?_⟩
    · have htake : π.take 6 = πn ++ [step0, step1, step2, step3, step4, step5] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h5
    · rw [hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp0, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg7, ?_, ?_⟩
    · have htake : π.take 7 = πn ++ [step0, step1, step2, step3, step4, step5, step6] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h6
    · rw [hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp0, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg8, ?_, ?_⟩
    · have htake : π.take 8 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h7
    · rw [hhead7, hhead6, hhead5, hhead4, hhead3, hhead2, hhead1, hhead0, hcfg0, hp0, hdir7, hdir6, hdir5, hdir4, hdir3, hdir2, hdir1, hdir0]
      norm_num [Dir.toInt]
  · refine ⟨cfg9, ?_, ?_⟩
    · have htake : π.take 9 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h8
    · rw [hhead8, hpos8, hd8]
      simpa using he0_ge0
  · refine ⟨cfg10, ?_, ?_⟩
    · have htake : π.take 10 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h9
    · rw [hhead9, hhead8, hpos8, hd9, hd8]
      omega
  · refine ⟨cfg11, ?_, ?_⟩
    · have htake : π.take 11 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      simpa [htake, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπe0] using h10
    · rw [hhead10, hhead9, hhead8, hpos8, hd10, hd9, hd8]
      omega
  · refine ⟨cfgc', ?_, ?_⟩
    · have htake : π.take 12 = πn ++ [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
        rw [hπall]
        simp [List.take_append, hlen_n]
      rw [htake]
      rw [← hπall]
      exact h
    · exact htail


-- ==============================================================================
-- M2 主定理（下界）：CBTM 层接受路径的每前缀终点头 ≥ 0。
--   装配同 M1；块内下界分 p：
--     · p ≥ 1：a1_block_prefix_nonneg（PosBound:2103，p ≥ 1 → 块内前缀 ∈ [0, 4p+4]）
--     · p = 0：p0_block_prefix_nonneg（本文件；htail = 块尾头 ≥ 0 由 A-3 + hpk1 提供）
--   全长分支：头 = 4·cfgs'.headPos ≥ 0（A-3 于全长终点）。
-- ==============================================================================

/-- M2 主定理：接受路径（CBTM 层）的每前缀终点头 ≥ 0（g' = [] 情形）。
    装配：accept_path_no_trap → accept_path_is_good_block_path（initialBlockCorrespond）
    → good_block_path_head_corresp（逐 k 块首对应）→ 前缀切块（k = n₀/12、j = n₀%12）
    → 块内下界（p ≥ 1：a1_block_prefix_nonneg；p = 0：p0_block_prefix_nonneg + A-3 块尾非负）。 -/
lemma a1_accept_path_prefix_head_nonneg (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target) :
    ∀ {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst)},
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π cfg →
      cfg.state ∈ acceptStates4 →
      ∀ π₀ cfg₀,
        TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
          (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π₀ cfg₀ →
        List.IsPrefix π₀ π →
        (0 : ℤ) ≤ cfg₀.headPos := by
  let wS := encodeInstanceSym inst
  have hx : encodeInstanceF4 inst = flat4F4 wS := by rfl
  intro π cfg h hacc π₀ cfg₀ h₀ hp
  have htrap : ∀ k (hk : k < π.length),
      (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101 := accept_path_no_trap h hacc
  have hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (encodeInstanceF4 inst))
      (symInitialConfig wS) := by
    change blockCorrespond (initialConfig subsetSumCBTM (flat4F4 wS)) (symInitialConfig wS)
    exact initialBlockCorrespond wS
  have hq0 : (symInitialConfig wS).state ≤ 101 := by
    dsimp [symInitialConfig, SymConfig.mk, VerifierSym.qStart]
    norm_num
  have hbp : GoodBlockPath (encodeInstanceF4 inst)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π cfg :=
    accept_path_is_good_block_path h hacc htrap hcorr0 hq0
  have hbridge := good_block_path_head_corresp (encodeInstanceF4 inst) wS
    (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) (symInitialConfig wS)
    π cfg hcorr0 hbp htrap
  rcases hbridge with ⟨πs, cfgs', hsSym, hcorr', hlen12, hhead⟩
  have hreach : SymReachablePath VerifierSym.transition wS πs cfgs' :=
    (symSteps_initial_iff VerifierSym.transition wS πs cfgs').1 hsSym
  have haccS : cfgs'.state = VerifierSym.qAccept := by
    rcases Finset.mem_image.mp hacc with ⟨reg, hreg, hacc'⟩
    have hst : cfg.state = encodeState cfgs'.state 0 0 := hcorr'.1
    have hdec := decodeState_encodeState VerifierSym.qAccept 0 reg (by norm_num)
      (by simpa [regBound] using Finset.mem_range.mp hreg)
    have hdec2 := decodeState_encodeState cfgs'.state 0 0 (by norm_num) (by norm_num)
    have hcong := congrArg decodeState (show cfg.state = encodeState VerifierSym.qAccept 0 reg by
      rw [← hacc'])
    rw [hst] at hcong
    rw [hdec, hdec2] at hcong
    exact congrArg Prod.fst hcong
  by_cases hfull : π₀ = π
  · subst π₀
    have hdet : cfg₀ = cfg := (tapeSteps_det π h h₀).symm
    subst cfg₀
    rw [hcorr'.2.1]
    -- A-3 于全长终点：0 ≤ cfgs'.headPos
    have hgeS' : (0 : ℤ) ≤ cfgs'.headPos := by
      exact sym_accept_prefix_head_nonneg inst hm hpos htarget πs cfgs' hreach haccS
        πs cfgs' hreach (by refine ⟨[], ?_⟩; simp)
    exact mul_nonneg (by norm_num) hgeS'
  · let n₀ := π₀.length
    let k := n₀ / 12
    have htake₀ : π₀ = π.take n₀ := by simpa [n₀] using (prefix_eq_take hp)
    have hn₀_le : n₀ ≤ π.length := by
      dsimp [n₀]
      rw [htake₀]
      simp [List.length_take]
    have hn₀_lt : n₀ < π.length := by
      by_contra hge
      have htake_all : π.take n₀ = π := by
        exact (List.take_eq_self_iff π).2 (Nat.le_of_not_gt hge)
      apply hfull
      rw [htake₀, htake_all]
    have hlen12' : π.length = 12 * πs.length := by
      rw [← hlen12]
      simp [Nat.mul_comm]
    have hn₀_lt12 : n₀ < 12 * πs.length := by
      rw [← hlen12']
      exact hn₀_lt
    have hk_lt : k < πs.length := by
      have hd := (Nat.div_lt_iff_lt_mul (k := 12) (y := πs.length) (by norm_num : 0 < 12)).2 (by
        simpa [Nat.mul_comm] using hn₀_lt12)
      simpa [k] using hd
    have hk1 : k + 1 ≤ πs.length := by omega
    rcases hhead k (by omega) with ⟨cfgsm, cfgcm, hSym_k, hTap_k, hpk, hstk⟩
    rcases hhead (k + 1) hk1 with ⟨cfgsm1, cfgcm1, hSym_k1, hTap_k1, hpk1, hstk1⟩
    have hreach_k : SymReachablePath VerifierSym.transition wS (πs.take k) cfgsm :=
      (symSteps_initial_iff VerifierSym.transition wS (πs.take k) cfgsm).1 hSym_k
    have h12k_le : 12 * k ≤ n₀ := by
      have hd := Nat.div_mul_le_self n₀ 12
      simpa [k, Nat.mul_comm] using hd
    have htake_eq : π₀.take (12 * k) = π.take (12 * k) := by
      rw [htake₀, List.take_take]
      rw [Nat.min_eq_left h12k_le]
    have hdec₀ := tapeSteps_append_decomp (π₁ := π₀.take (12 * k))
      (π₂ := π₀.drop (12 * k))
      (by simpa [List.take_append_drop] using h₀)
    rcases hdec₀ with ⟨cfg₁, h₁, h₂⟩
    have hdet₁ : cfg₁ = cfgcm := by
      exact tapeSteps_det (π.take (12 * k)) (by simpa [htake_eq] using h₁) hTap_k
    have h₂' : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
        (π₀.drop (12 * k)) cfg₀ := by
      simpa [hdet₁] using h₂
    -- 块 k+1 全长（12 步从 cfgcm）
    have htt : (π.take (12 * (k + 1))).take (12 * k) = π.take (12 * k) := by
      rw [List.take_take]
      rw [Nat.min_eq_left (by omega : 12 * k ≤ 12 * (k + 1))]
    have hdec₁ := tapeSteps_append_decomp (π₁ := π.take (12 * k))
      (π₂ := (π.take (12 * (k + 1))).drop (12 * k))
      (by
        rw [← htt]
        simpa [List.take_append_drop] using hTap_k1)
    rcases hdec₁ with ⟨cfg₂, h₂a, h₂b⟩
    have hdet₂ : cfg₂ = cfgcm := tapeSteps_det (π.take (12 * k)) h₂a hTap_k
    have hb12 : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
        ((π.take (12 * (k + 1))).drop (12 * k)) cfgcm1 := by
      rw [← hdet₂]
      exact h₂b
    have hblen : ((π.take (12 * (k + 1))).drop (12 * k)).length = 12 := by
      have hle : 12 * (k + 1) ≤ π.length := by
        have hle' : 12 * (k + 1) ≤ 12 * πs.length := Nat.mul_le_mul_left 12 hk1
        simpa [hlen12', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle'
      exact block_drop_length hle
    have htr12 : ∀ m (hm : m < ((π.take (12 * (k + 1))).drop (12 * k)).length),
        (decodeState (((π.take (12 * (k + 1))).drop (12 * k)).get ⟨m, hm⟩).result.nextState).1 ≠ 101 := by
      intro m hm
      have hmem : ∀ step ∈ (π.take (12 * (k + 1))).drop (12 * k),
          (decodeState step.result.nextState).1 ≠ 101 := by
        intro step hs
        exact (trap_mem_of_get htrap) step (block_step_mem (π := π) (k := k) step hs)
      exact trap_get_of_mem hmem m hm
    have hmidlen : (π₀.drop (12 * k)).length ≤ 12 := by
      rw [List.length_drop]
      have hjk : 12 * k + n₀ % 12 = n₀ := by
        simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
      have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
      omega
    -- 下界分 p：cfgsm 头 ≥ 0（A-3 于块首 Sym 前缀）⟹ p ≥ 1 或 p = 0
    have hgeS : (0 : ℤ) ≤ cfgsm.headPos := by
      exact sym_accept_prefix_head_nonneg inst hm hpos htarget πs cfgs' hreach haccS
        (πs.take k) cfgsm hreach_k (by refine ⟨πs.drop k, ?_⟩; simp [List.take_append_drop])
    by_cases hp0s : cfgsm.headPos = 0
    · -- p = 0：块尾头 ≥ 0（A-3 于 (k+1) 前缀 + hpk1）⟹ p0_block_prefix_nonneg
      have htail0 : (0 : ℤ) ≤ cfgcm1.headPos := by
        have hgeS1 : (0 : ℤ) ≤ cfgsm1.headPos := by
          have hreach_k1 : SymReachablePath VerifierSym.transition wS (πs.take (k + 1)) cfgsm1 :=
            (symSteps_initial_iff VerifierSym.transition wS (πs.take (k + 1)) cfgsm1).1 hSym_k1
          exact sym_accept_prefix_head_nonneg inst hm hpos htarget πs cfgs' hreach haccS
            (πs.take (k + 1)) cfgsm1 hreach_k1 (by
              refine ⟨πs.drop (k + 1), ?_⟩
              simp [List.take_append_drop])
        rw [hpk1]
        exact mul_nonneg (by norm_num) hgeS1
      have hpp0 : cfgcm.headPos = 0 := by
        rw [hpk, hp0s]
        norm_num
      rcases (p0_block_prefix_nonneg hb12 hblen hstk hpp0 htr12 htail0)
        (π₀.drop (12 * k)).length hmidlen with ⟨cfgj, hpfxj, hge0⟩
      have hmid_eq : π₀.drop (12 * k) =
          ((π.take (12 * (k + 1))).drop (12 * k)).take (π₀.drop (12 * k)).length := by
        rw [htake₀]
        have hlen' : ((π.take n₀).drop (12 * k)).length = n₀ - 12 * k := by
          rw [List.length_drop, List.length_take]
          rw [Nat.min_eq_left hn₀_le]
        rw [hlen']
        have hA : 12 * (k + 1) - 12 * k = 12 := by omega
        have hx : n₀ - 12 * k ≤ 12 := by
          have hjk : 12 * k + n₀ % 12 = n₀ := by
            simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
          have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
          omega
        calc
          (π.take n₀).drop (12 * k)
              = (π.drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
          _ = ((π.take (12 * (k + 1))).drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
                  rw [List.take_take]
                  rw [hA]
                  rw [Nat.min_eq_left hx]
      have hdet₀ : cfg₀ = cfgj := by
        have hsame : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
            (π₀.drop (12 * k)) cfgj := by
          rw [hmid_eq]
          exact hpfxj
        exact tapeSteps_det (π₀.drop (12 * k)) h₂' hsame
      rw [hdet₀]
      exact hge0
    · -- p ≥ 1：a1_block_prefix_nonneg
      have hpge1 : 1 ≤ cfgsm.headPos := by omega
      rcases (a1_block_prefix_nonneg hb12 hblen hstk hpk htr12 hpge1)
        (π₀.drop (12 * k)).length hmidlen with ⟨cfgj, hpfxj, hge0, hhi⟩
      have hmid_eq : π₀.drop (12 * k) =
          ((π.take (12 * (k + 1))).drop (12 * k)).take (π₀.drop (12 * k)).length := by
        rw [htake₀]
        have hlen' : ((π.take n₀).drop (12 * k)).length = n₀ - 12 * k := by
          rw [List.length_drop, List.length_take]
          rw [Nat.min_eq_left hn₀_le]
        rw [hlen']
        have hA : 12 * (k + 1) - 12 * k = 12 := by omega
        have hx : n₀ - 12 * k ≤ 12 := by
          have hjk : 12 * k + n₀ % 12 = n₀ := by
            simpa [k, Nat.mul_comm] using (Nat.div_add_mod n₀ 12)
          have hnmod : n₀ % 12 < 12 := Nat.mod_lt n₀ (by norm_num)
          omega
        calc
          (π.take n₀).drop (12 * k)
              = (π.drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
          _ = ((π.take (12 * (k + 1))).drop (12 * k)).take (n₀ - 12 * k) := by
                  rw [List.drop_take]
                  rw [List.take_take]
                  rw [hA]
                  rw [Nat.min_eq_left hx]
      have hdet₀ : cfg₀ = cfgj := by
        have hsame : TapeSteps subsetSumCBTM (encodeInstanceF4 inst) cfgcm
            (π₀.drop (12 * k)) cfgj := by
          rw [hmid_eq]
          exact hpfxj
        exact tapeSteps_det (π₀.drop (12 * k)) h₂' hsame
      rw [hdet₀]
      exact hge0




-- ==============================================================================
-- A-1 组合主定理：CBTM 层接受路径的每前缀头 ∈ [0, 4·|wS|]（g' = [] 情形）。
--   下界 = M2（a1_accept_path_prefix_head_nonneg）；上界 = M1（a1_accept_path_prefix_head_le）。
-- ==============================================================================

/-- A-1 成品：接受路径（CBTM 层）每前缀 m 步终点头 ∈ [0, 4·|encodeInstanceSym inst|]
    （= [0, |encodeInstanceF4 inst|]，flat4F4_length 换算）。 -/
lemma a1_cbtm_accept_path_prefix_bound (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst)}
    (h : TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π cfg)
    (hacc : cfg.state ∈ acceptStates4) :
    ∀ m (hm : m ≤ π.length), ∃ cfgm : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst),
      TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
        (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) (π.take m) cfgm ∧
      (0 : ℤ) ≤ cfgm.headPos ∧
      cfgm.headPos ≤ 4 * (encodeInstanceSym inst).length := by
  intro m hm'
  rcases tapeSteps_prefix_end h m hm' with ⟨cfgm, hpfx⟩
  refine ⟨cfgm, hpfx, ?_, ?_⟩
  · exact a1_accept_path_prefix_head_nonneg inst hm hpos htarget h hacc (π.take m) cfgm hpfx
      (by refine ⟨π.drop m, ?_⟩; simp [List.take_append_drop])
  · have hle := a1_accept_path_prefix_head_le inst hm hpos htarget h hacc (π.take m) cfgm hpfx
      (by refine ⟨π.drop m, ?_⟩; simp [List.take_append_drop])
    have hlenx : ((encodeInstanceF4 inst).length : ℤ) =
        (4 * (encodeInstanceSym inst).length : ℤ) := by
      simp [encodeInstanceF4, flat4F4_length]
    rw [hlenx] at hle
    exact hle


-- ==============================================================================
-- M2 实现记录（2026-09-09）：块内前缀下界的正式路线（取代早期 L2 表级设计）——
--   transition4 表结构（SubsetSumVerifierCBTM:207-249）：
--     · 相位 0-2（读阶段）：读 im=false 格恒 R 且写回原值（im=true 格 → trap 101）；
--     · 相位 3（合成）：symOf4F4 合成整符号 → VerifierSym.transition 查表 → 写回第 4 格、移 L
--       （结果存 reg = encodeResult r）；
--     · 相位 4-7（写回）：依次写第 2/1/0 格（S/L），相位 7 写回原符号 S；
--     · 相位 8-11（移动段）：按 reg 的 r.moveDir = d 执行（全 R/全 L/全 S，每相位 ±1，
--       写回原值），相位 11 到 encodeState (min r.nextState 101) 0 0。
--   ⟹ 块内前缀偏移（从块首 4p）：相位 0-7 ∈ {1,2,3,2,1,0,0}（精确回摆 ≥ 0，相位 7 末回到 4p）；
--     相位 8-11 移动段 4 步位移相同 = e0（T1 trans4_ge8_moveDir_of_reg：方向由 reg 决定 +
--     T2 trans4_ge8_nextState_reg_preserved：相位 8-10 reg 不变）。负头 ⟺ p = 0 ∧ e0 = L。
--   p0_block_prefix_nonneg：p = 0 块（块首头 0）内每前缀 ≥ 0——htail（块尾头 ≥ 0，
--   装配处由 A-3 sym_accept_prefix_head_nonneg + hpk1 提供）排除 e0 = L（块尾 = 4·e0.toInt）。
--   M2 = a1_accept_path_prefix_head_nonneg（下界）；p ≥ 1 块直接 a1_block_prefix_nonneg
--   （PosBound:2103）。A-1 组合成品 = a1_cbtm_accept_path_prefix_bound（每前缀 ∈ [0, 4|wS|]）。
-- ==============================================================================

end Mp
