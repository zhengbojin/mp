import Mp.SubsetSumVerifierReverse11
import Mp.SubsetSumVerifierPosBound4
import Mp.SubsetSumVerifierPosBound5
import Mp.SubsetSumVerifierReverse8
import Mp.A1StepBoundBridge
import Mp.SubsetSumCompile
import Mp.SubsetSumVerifierReverse15

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-!
# q10 装配：`NTM2.Canonical subsetSumNTM2`（S1 里程碑）

本文件把三条款的**已证件**接线为 `NTM2.Canonical subsetSumNTM2`：

* **条款 (a) 位置界**：NTM2 每步 `pos ∈ [0, |x|]` 且步后不越
  - 素材：`a2_cbtm_accept_path_prefix_bound`（PosBound5，F4 层，输入含 gS，
    接受路径每前缀头 ∈ [0, |x|]）+ 镜像桥 `ntm2_path_mirror`（Reverse11，头位保持）
    + 确定性 `tapeSteps_det` + ④ 正性供给 `iso_accepts_implies_encoding`（Reverse8）
* **条款 (b) 标记读同位唯一（前缀口径）**：`ntm2_canonical_clause2`（Reverse11:1236）
* **条款 (c) 长界**：A3 欠条 `subsetSumNTM2_canonical_clauseC`（兄弟线还债后定理化）

## 接线纪律
* 每条件的签名在此逐字引用；接口不符处新证 glue 引理（不留缺口）。
* 装配归宿：本文件；不修改只读共享文件。
-/

open Mp
open Mp.SymToF4

namespace Mp

set_option maxRecDepth 200000
set_option linter.unusedVariables false

/-- 条款 (b) 的装配：直接把 `NTM2.Canonical` 字面口径交给 Reverse11 的已证定理。 -/
theorem subsetSumNTM2_clauseB {inst : SubsetSumInstance} {gS : List Sym} {x : List F4}
    (hx : x = encodeInstanceF4 inst ++ flat4F4 gS)
    {π : NTM2ComputationPath} {cfg : NTM2Config subsetSumNTM2 x}
    (hr : TapeReachablePathNTM2 subsetSumNTM2 x π cfg)
    (hext : ∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 x),
        TapeReachablePathNTM2 subsetSumNTM2 x (π ++ π₂) cfg₂ ∧
        cfg₂.state ∈ subsetSumNTM2.acceptStates) :
    ∀ (π₀ : NTM2ComputationPath) (step : NTM2TransitionStep) (π₁ : NTM2ComputationPath),
      π = π₀ ++ step :: π₁ → F4.im step.readSym = true →
      ∀ s ∈ π₀, s.pos ≠ step.pos :=
  ntm2_canonical_clause2 hx hr hext

/-- 元素列表非空 ⟹ 其 Sym 编码非空（编码首格 = α 元素标记）。 -/
lemma encodeElementsSym_nonempty {l : List ℕ} (hne : l ≠ []) : 0 < (encodeElementsSym l).length := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons v rest =>
      cases rest with
      | nil => simp [encodeElementsSym]
      | cons w tl => simp [encodeElementsSym]

/-- NTM2 可达路径的前缀末配置提取（take 形态）。 -/
lemma ntm2_reachable_take_end {A : NTM2} {x : List F4} {π : NTM2ComputationPath}
    {cfg : NTM2Config A x} (h : TapeReachablePathNTM2 A x π cfg) :
    ∀ m (hm : m ≤ π.length), ∃ cfgm : NTM2Config A x, TapeReachablePathNTM2 A x (π.take m) cfgm := by
  induction h with
  | nil =>
      intro m hm
      have : m = 0 := by simpa using hm
      subst m
      refine ⟨NTM2InitialConfig A x, TapeReachablePathNTM2.nil⟩
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      intro m hm
      simp at hm
      by_cases hmle : m ≤ π₀.length
      · rcases ih m hmle with ⟨cfgm, hpfx⟩
        refine ⟨cfgm, ?_⟩
        have ht : (π₀ ++ [step]).take m = π₀.take m := List.take_append_of_le_length hmle
        simpa [ht] using hpfx
      · have hm' : m = π₀.length + 1 := by omega
        subst m
        refine ⟨NTM2StepConfig cfg₀ step.result, ?_⟩
        have ht : (π₀ ++ [step]).take (π₀.length + 1) = π₀ ++ [step] := by
          induction π₀ with
          | nil => simp
          | cons a t ih => simp []
        simpa [ht] using (TapeReachablePathNTM2.cons π₀ step cfg₀ hrc hfrom hread hpos htrans)

/-- 左拼接的 get：前缀内取元等于前缀自身取元。 -/
lemma ntm2_getElem_append_left {α : Type*} {l₁ l₂ : List α} {i : ℕ}
    (hi : i < l₁.length) (h : i < (l₁ ++ l₂).length) :
    (l₁ ++ l₂).get ⟨i, h⟩ = l₁.get ⟨i, hi⟩ := by
  induction l₁ generalizing i with
  | nil => simp at hi
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < t.length := Nat.lt_of_succ_lt_succ hi
          have h' : i < (t ++ l₂).length := by
            rw [List.length_append]
            rw [List.length_append] at h
            omega
          simpa using (ih hi' h')

/-- 右拼接取末元素：`(l ++ [a]).get ⟨|l|, _⟩ = a`。 -/
lemma ntm2_get_append_last {α : Type*} {l : List α} {a : α} (h : l.length < (l ++ [a]).length) :
    (l ++ [a]).get ⟨l.length, h⟩ = a := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      have h' : t.length < (t ++ [a]).length := by
        rw [List.length_append, List.length_singleton]
        rw [List.length_append, List.length_singleton] at h
        omega
      simpa using (ih h')

/-- NTM2 可达路径的第 i 步 cons 分解：`π[i] = step` 且前缀末配置 `cfgpre` 与 step 的全部
    cons 字段齐备（含 `step.pos = cfgpre.headPos`）。 -/
lemma ntm2_reachable_take_succ_cons {A : NTM2} {x : List F4} {π : NTM2ComputationPath}
    {cfg : NTM2Config A x} (h : TapeReachablePathNTM2 A x π cfg) :
    ∀ i (hlt : i < π.length),
      ∃ (cfgpre : NTM2Config A x) (step : NTM2TransitionStep),
        π.get ⟨i, hlt⟩ = step ∧
        TapeReachablePathNTM2 A x (π.take i) cfgpre ∧
        step.fromState = cfgpre.state ∧ step.readSym = cfgpre.tape cfgpre.headPos ∧
        step.pos = cfgpre.headPos ∧
        step.result ∈ A.transition (cfgpre.state, cfgpre.tape cfgpre.headPos, cfgpre.headPos) ∧
        TapeReachablePathNTM2 A x (π.take (i + 1)) (NTM2StepConfig cfgpre step.result) := by
  induction h with
  | nil => intro i hlt; exact (Nat.not_lt_zero i (by simpa using hlt)).elim
  | cons π₀ step cfg₀ hrc hfrom hread hpos htrans ih =>
      intro i hlt
      simp at hlt
      by_cases hlt' : i < π₀.length
      · rcases ih i hlt' with ⟨cfgpre, step', hget, hrc', hfrom', hread', hpos', htrans', hcons'⟩
        refine ⟨cfgpre, step', ?_, ?_, hfrom', hread', hpos', htrans', ?_⟩
        · simpa using (ntm2_getElem_append_left (by omega : i < π₀.length) (by simpa using hlt)).trans hget
        · have ht : (π₀ ++ [step]).take i = π₀.take i :=
            List.take_append_of_le_length (by omega : i ≤ π₀.length)
          simpa [ht] using hrc'
        · have ht₁ : (π₀ ++ [step]).take (i + 1) = π₀.take (i + 1) :=
            List.take_append_of_le_length (by omega : i + 1 ≤ π₀.length)
          simpa [ht₁] using hcons'
      · have hi : i = π₀.length := by omega
        subst i
        refine ⟨cfg₀, step, ?_, ?_, hfrom, hread, hpos, htrans, ?_⟩
        · simpa using (ntm2_get_append_last (l := π₀) (a := step) (by simpa using hlt))
        · have ht : (π₀ ++ [step]).take π₀.length = π₀ := by
            induction π₀ with
            | nil => simp
            | cons a t ih => simp []
          simpa [ht] using hrc
        · have ht₁ : (π₀ ++ [step]).take (π₀.length + 1) = π₀ ++ [step] := by
            induction π₀ with
            | nil => simp
            | cons a t ih => simp []
          simpa [ht₁] using (TapeReachablePathNTM2.cons π₀ step cfg₀ hrc hfrom hread hpos htrans)

/-- 条款 (a) 位置界的逐步本体：对 π 的每一步（= π[i]，i < |π|）证明
    `pos` 与 `pos + dir` 均落在 [0, |x|]（x = encodeInstanceF4 inst ++ flat4F4 gS）。
    力量来源：镜像桥（头位保持）+ 确定性（`tapeSteps_det`）+ A-2 成品
    `a2_cbtm_accept_path_prefix_bound`（接受路径每前缀头 ∈ [0, |x|]）。 -/
theorem subsetSumNTM2_clauseA_aux (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length) (ht : 0 < inst.target) (gS : List Sym) :
    ∀ (x' : List F4) (hx' : x' = encodeInstanceF4 inst ++ flat4F4 gS)
      (π : NTM2ComputationPath) (cfg : NTM2Config subsetSumNTM2 x')
      (πext : NTM2ComputationPath) (cfge : NTM2Config subsetSumNTM2 x'),
      TapeReachablePathNTM2 subsetSumNTM2 x' (π ++ πext) cfge →
      cfge.state ∈ subsetSumNTM2.acceptStates →
      ∀ step ∈ π,
        0 ≤ step.pos ∧ step.pos ≤ ((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) ∧
        0 ≤ step.pos + step.result.2.2.toInt ∧
        step.pos + step.result.2.2.toInt ≤ ((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) := by
  intro x' hx' π cfg πext cfge hfullN hacc step hs
  subst x'
  have hmir : TapeReachablePath subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      ((π ++ πext).map ntm2StepToCBTM) (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfge) :=
    ntm2_path_mirror subsetSumNTM2 subsetSumCBTM subsetSumIso (encodeInstanceF4 inst ++ flat4F4 gS)
      (π ++ πext) cfge hfullN
  have haccC : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfge).state ∈ acceptStates4 := by
    have hmem : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfge).state ∈
        subsetSumCBTM.acceptStates := by
      rw [subsetSumIso.h_accept]
      exact hacc
    exact hmem
  have hsteps : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      ((π ++ πext).map ntm2StepToCBTM) (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfge) :=
    (tapeSteps_initial_iff subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      ((π ++ πext).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfge)).mpr hmir
  have hmain := a2_cbtm_accept_path_prefix_bound inst hm ht gS hsteps haccC
  -- step = π[i]；前缀末配置由第 i 步 cons 分解给出
  rcases List.mem_iff_getElem.mp hs with ⟨i, hlt, hstep⟩
  rcases ntm2_reachable_take_succ_cons hfullN i (by rw [List.length_append]; omega) with
    ⟨cfgpre, step', hget, hrc, hfrom, hread, hpos, htrans, hcons⟩
  have hstep' : step' = step := by
    rw [← hget]
    rw [ntm2_getElem_append_left (by omega : i < π.length) (by rw [List.length_append]; omega)]
    exact hstep
  rw [hstep'] at hpos hfrom hread htrans hcons
  -- 前缀 m = i：末配置头 = step.pos（镜像 take 形前缀，不做索引重写）
  rcases hmain i (by rw [List.length_map, List.length_append]; omega) with ⟨cfgm₁, hpfx₁, hlo₁, hhi₁⟩
  have htakei : ((π ++ πext).map ntm2StepToCBTM).take i = ((π ++ πext).take i).map ntm2StepToCBTM := by
    rw [← List.map_take]
  rw [htakei] at hpfx₁
  have hmir_p : TapeReachablePath subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (((π ++ πext).take i).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfgpre) :=
    ntm2_path_mirror subsetSumNTM2 subsetSumCBTM subsetSumIso (encodeInstanceF4 inst ++ flat4F4 gS)
      ((π ++ πext).take i) cfgpre hrc
  have hsteps_p : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (((π ++ πext).take i).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfgpre) :=
    (tapeSteps_initial_iff subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (((π ++ πext).take i).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfgpre)).mpr hmir_p
  have hcfg₁ : cfgm₁ = ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfgpre :=
    tapeSteps_det (((π ++ πext).take i).map ntm2StepToCBTM) hpfx₁ hsteps_p
  have hcfg₁h : cfgm₁.headPos = step.pos := by
    rw [hcfg₁]
    exact hpos.symm
  -- 前缀 m = i+1：末配置头 = step.pos + dir（步后位置）
  rcases hmain (i + 1) (by rw [List.length_map, List.length_append]; omega) with ⟨cfgm₂, hpfx₂, hlo₂, hhi₂⟩
  have htakei₁ : ((π ++ πext).map ntm2StepToCBTM).take (i + 1) =
      ((π ++ πext).take (i + 1)).map ntm2StepToCBTM := by
    rw [← List.map_take]
  rw [htakei₁] at hpfx₂
  have hmir_p1 : TapeReachablePath subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (((π ++ πext).take (i + 1)).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso (NTM2StepConfig cfgpre step.result)) :=
    ntm2_path_mirror subsetSumNTM2 subsetSumCBTM subsetSumIso (encodeInstanceF4 inst ++ flat4F4 gS)
      ((π ++ πext).take (i + 1)) (NTM2StepConfig cfgpre step.result) hcons
  have hsteps_p1 : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (((π ++ πext).take (i + 1)).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso (NTM2StepConfig cfgpre step.result)) :=
    (tapeSteps_initial_iff subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (((π ++ πext).take (i + 1)).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso (NTM2StepConfig cfgpre step.result))).mpr hmir_p1
  have hcfg₂ : cfgm₂ = ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso
      (NTM2StepConfig cfgpre step.result) :=
    tapeSteps_det (((π ++ πext).take (i + 1)).map ntm2StepToCBTM) hpfx₂ hsteps_p1
  have hcfg₂h : cfgm₂.headPos = step.pos + step.result.2.2.toInt := by
    rw [hcfg₂]
    change cfgpre.headPos + step.result.2.2.toInt = step.pos + step.result.2.2.toInt
    rw [hpos.symm]
  exact ⟨by rw [← hcfg₁h]; exact hlo₁, by rw [← hcfg₁h]; exact hhi₁,
    by rw [← hcfg₂h]; exact hlo₂, by rw [← hcfg₂h]; exact hhi₂⟩

/-- 条款 (a) 装配：NTM2 层位置界（`NTM2.Canonical` ① 的字面口径）。
    正性供给：接受可延拓 + 输入形状 ⟹ 镜像 CBTM 接受 ⟹ ④（`iso_accepts_implies_encoding`）
    给出合法实例（elements ≠ [] 且 0 < target），再喂 A-2 成品。 -/
theorem subsetSumNTM2_clauseA {x : List F4} {π : NTM2ComputationPath}
    {cfg : NTM2Config subsetSumNTM2 x}
    (hx : ∃ inst : SubsetSumInstance, ∃ gS : List Sym,
      x = encodeInstanceF4 inst ++ flat4F4 gS)
    (_hnoTerm : ∀ step ∈ π, step.fromState ∉ subsetSumNTM2.acceptStates)
    (hr : TapeReachablePathNTM2 subsetSumNTM2 x π cfg)
    (hext : ∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 x),
      TapeReachablePathNTM2 subsetSumNTM2 x (π ++ π₂) cfg₂ ∧
      cfg₂.state ∈ subsetSumNTM2.acceptStates) :
    ∀ step ∈ π,
      0 ≤ step.pos ∧ step.pos ≤ (x.length : ℤ) ∧
      0 ≤ step.pos + step.result.2.2.toInt ∧
      step.pos + step.result.2.2.toInt ≤ (x.length : ℤ) := by
  rcases hx with ⟨inst₀, gS₀, hx₀⟩
  subst x
  rcases hext with ⟨π₂, cfg₂, hr₂, hacc₂⟩
  have hmirF : TapeReachablePath subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)
      ((π ++ π₂).map ntm2StepToCBTM) (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂) :=
    ntm2_path_mirror subsetSumNTM2 subsetSumCBTM subsetSumIso (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)
      (π ++ π₂) cfg₂ hr₂
  have haccC : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂).state ∈ acceptStates4 := by
    have hmem : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂).state ∈
        subsetSumCBTM.acceptStates := by
      rw [subsetSumIso.h_accept]
      exact hacc₂
    exact hmem
  have haccM : (NTM2.toCBTM subsetSumNTM2).tapeAccepts (encodeInstanceF4 inst₀ ++ flat4F4 gS₀) := by
    refine ⟨(π ++ π₂).map ntm2StepToCBTM,
      { state := cfg₂.state, tape := cfg₂.tape, headPos := cfg₂.headPos }, ?_, ?_⟩
    · rw [toCBTM_subsetSumNTM2_eq]
      exact hmirF
    · rw [toCBTM_subsetSumNTM2_eq]
      exact haccC
  have hal : IsSymbolAligned (encodeInstanceF4 inst₀ ++ flat4F4 gS₀) :=
    ⟨encodeInstanceSym inst₀ ++ gS₀, by
      rw [flat4F4_append]
      simp [encodeInstanceF4]⟩
  have hiso : StructIsoNTM2CBTM subsetSumNTM2 (NTM2.toCBTM subsetSumNTM2) := by
    simpa [toCBTM_subsetSumNTM2_eq] using subsetSumIso
  have henc := iso_accepts_implies_encoding (NTM2.toCBTM subsetSumNTM2) hiso
    (encodeInstanceF4 inst₀ ++ flat4F4 gS₀) hal haccM
  rcases henc with ⟨inst, gS, hw, hne, _hpos, htarget⟩
  rw [hw] at ⊢
  have hm : 0 < (encodeElementsSym inst.elements).length := encodeElementsSym_nonempty hne
  exact subsetSumNTM2_clauseA_aux inst hm htarget gS (encodeInstanceF4 inst₀ ++ flat4F4 gS₀) hw
    π cfg π₂ cfg₂ hr₂ hacc₂

set_option maxHeartbeats 1600000 in
/-- [T-P5.3 预接线] C3-κ 装配链骨架（C-5/G7 接口）：镜像（`ntm2_path_mirror`）→ 首达截断
    （`truncate_keeps_prefix`，hnoT 直供 `hclean`）→ 块对应 → δ-16b（`a1_cbtm_path_length_bound_canonical`，
    gS 通形）→ |x| 口径对齐（`canonical_bound_enlarge`）⇒ **A3 全形**（∨ 左支；K = 1997568）。
    唯一供给槽 = `hsup`（hseg 供给件 = P1 四阶段段界折算）；T-P5.4 定理化时以真实供给实例化并入。 -/
theorem subsetSumNTM2_clauseC_wiring
    (hsup : ∀ (inst : SubsetSumInstance) (gS : List Sym) (πs : List SymStep) (cfgs' : SymConfig),
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs' →
      (∀ s ∈ πs, s.fromState ≠ 100) → cfgs'.state = 100 →
      (πs.length : ℤ) ≤ (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1)
        * (((encodeInstanceSym inst ++ gS).length : ℤ) + 102)) :
    ∃ K : ℕ,
      ∀ (x : List F4) (π : NTM2ComputationPath) (cfg : NTM2Config subsetSumNTM2 x),
        (∃ (inst : SubsetSumInstance) (gS : List Sym), x = encodeInstanceF4 inst ++ flat4F4 gS) →
        (∀ step ∈ π, step.fromState ∉ subsetSumNTM2.acceptStates) →
        TapeReachablePathNTM2 subsetSumNTM2 x π cfg →
        (∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 x),
            TapeReachablePathNTM2 subsetSumNTM2 x (π ++ π₂) cfg₂ ∧
            cfg₂.state ∈ subsetSumNTM2.acceptStates) →
          π.length ≤ K * ((π.filter (fun step => F4.im step.readSym = true)).length + 1) *
              (x.length + 1) * (x.length + 1) ∨
            ∃ (π₁ π₂ : NTM2ComputationPath), π = π₁ ++ π₂ ∧ π₂ ≠ [] ∧
              (∀ step ∈ π₂, step.fromState ∈ subsetSumNTM2.rejectStates ∧
                step.result.1 ∈ subsetSumNTM2.rejectStates ∧ step.result.2.2 = Dir.S) := by
  refine ⟨1997568, ?_⟩
  intro x π cfg hx hnoTerm hr hext
  rcases hx with ⟨inst₀, gS₀, hx₀⟩
  subst x
  rcases hext with ⟨π₂, cfg₂, hr₂, hacc₂⟩
  have hmirF : TapeReachablePath subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)
      ((π ++ π₂).map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂) :=
    ntm2_path_mirror subsetSumNTM2 subsetSumCBTM subsetSumIso (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)
      (π ++ π₂) cfg₂ hr₂
  have haccC : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂).state ∈ acceptStates4 := by
    have hmem : (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂).state ∈
        subsetSumCBTM.acceptStates := by
      rw [subsetSumIso.h_accept]
      exact hacc₂
    exact hmem
  have hnoMap : ∀ s ∈ π.map ntm2StepToCBTM, s.fromState ∉ subsetSumCBTM.acceptStates := by
    intro s hs hmem
    rcases List.mem_map.mp hs with ⟨s₀, hs₀, rfl⟩
    exact hnoTerm s₀ hs₀ hmem
  have hmirF' : TapeReachablePath subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)
      (π.map ntm2StepToCBTM ++ π₂.map ntm2StepToCBTM)
      (ntm2CfgToCBTM subsetSumNTM2 subsetSumCBTM subsetSumIso cfg₂) := by
    rw [← List.map_append]
    exact hmirF
  obtain ⟨πt, cfgt, hrt, hacct, hnoT, hlenπ⟩ := truncate_keeps_prefix hmirF' haccC hnoMap
  have hsteps : TapeSteps subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀)) πt cfgt :=
    (tapeSteps_initial_iff subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀) πt cfgt).mpr hrt
  have htrap := accept_path_no_trap hsteps hacct
  have hcorr0 : blockCorrespond
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst₀ ++ flat4F4 gS₀))
      (symInitialConfig (encodeInstanceSym inst₀ ++ gS₀)) := by
    have h1 := initialBlockCorrespond (encodeInstanceSym inst₀ ++ gS₀)
    have h2 : flat4F4 (encodeInstanceSym inst₀ ++ gS₀) =
        encodeInstanceF4 inst₀ ++ flat4F4 gS₀ := by
      rw [flat4F4_append]
      rfl
    rwa [h2] at h1
  have hq0 : (symInitialConfig (encodeInstanceSym inst₀ ++ gS₀)).state ≤ 101 := by
    dsimp [symInitialConfig, SymConfig.mk]
    norm_num
  have hbp := accept_path_is_good_block_path hsteps hacct htrap hcorr0 hq0
  have hclean : ∀ step ∈ πt, step.fromState ∉ acceptStates4 := hnoT
  set M0 := (π.filter (fun step => F4.im step.readSym = true)).length with hM0
  set XX := (encodeInstanceF4 inst₀ ++ flat4F4 gS₀).length with hXX
  have hcn := a1_cbtm_path_length_bound_canonical inst₀ gS₀ hsteps hacct hcorr0 hbp htrap
    hclean (hsup inst₀ gS₀) M0
  have henl := canonical_bound_enlarge inst₀ gS₀ M0
  left
  have hZ : (π.length : ℤ)
      ≤ ((1997568 * (M0 + 1) * (XX + 1) * (XX + 1) : ℕ) : ℤ) := by
    calc (π.length : ℤ) ≤ (πt.length : ℤ) := by
          have h := hlenπ
          simp only [List.length_map] at h
          exact_mod_cast h
      _ ≤ (1997568 : ℤ) * ((M0 : ℤ) + 1)
            * (4 * ((encodeInstanceSym inst₀ ++ gS₀).length : ℤ) + 1) ^ 2 := hcn
      _ ≤ (1997568 : ℤ) * ((M0 : ℤ) + 1) * ((XX : ℤ) + 1) ^ 2 := henl
      _ = ((1997568 * (M0 + 1) * (XX + 1) * (XX + 1) : ℕ) : ℤ) := by
          push_cast
          ring
  exact_mod_cast hZ

/-- [C2 · T-P5.4] A3 欠条定理化（公理 → 同名定理，消费点零改动）：
    `hsup` 槽以真实供给实例化 = `wf_of_accept`（④ ⟹ hne/hpos/htarget）+ `hconf_of_accept`（② ⟹ hconf）
    + `sym_run_le_1632_fold`（运行形 hseg，`a269fd8`）。 -/
theorem subsetSumNTM2_canonical_clauseC :
  ∃ K : ℕ,
    ∀ (x : List F4) (π : NTM2ComputationPath) (cfg : NTM2Config subsetSumNTM2 x),
      (∃ (inst : SubsetSumInstance) (gS : List Sym),
        x = encodeInstanceF4 inst ++ flat4F4 gS) →
      (∀ step ∈ π, step.fromState ∉ subsetSumNTM2.acceptStates) →
      TapeReachablePathNTM2 subsetSumNTM2 x π cfg →
      (∃ (π₂ : NTM2ComputationPath) (cfg₂ : NTM2Config subsetSumNTM2 x),
          TapeReachablePathNTM2 subsetSumNTM2 x (π ++ π₂) cfg₂ ∧
          cfg₂.state ∈ subsetSumNTM2.acceptStates) →
        π.length ≤ K * ((π.filter (fun step => F4.im step.readSym = true)).length + 1) *
            (x.length + 1) * (x.length + 1) ∨
          ∃ (π₁ π₂ : NTM2ComputationPath), π = π₁ ++ π₂ ∧ π₂ ≠ [] ∧
            (∀ step ∈ π₂, step.fromState ∈ subsetSumNTM2.rejectStates ∧
              step.result.1 ∈ subsetSumNTM2.rejectStates ∧ step.result.2.2 = Dir.S)
  := subsetSumNTM2_clauseC_wiring (hsup := fun inst gS πs cfgs' hrun hclean h100 => by
      obtain ⟨hne, hpos, htarget⟩ := wf_of_accept (inst := inst) (gS := gS) hrun h100
      have hm : 0 < (encodeElementsSym inst.elements).length :=
        (encodeElementsSym_length_pos_iff (elems := inst.elements)).mpr hne
      have hconf := hconf_of_accept (inst := inst) (gS := gS) hm htarget hrun h100
      exact sym_run_le_1632_fold inst gS hne hpos htarget hconf hrun hclean h100)


/-- q10 主定理（S1 里程碑）：`subsetSumNTM2` 是规范的（NTM2.Canonical）。
    条款 (a) = `subsetSumNTM2_clauseA`（位置界，A-2 成品 + 镜像 + ④ 正性供给）；
    条款 (b) = `subsetSumNTM2_clauseB`（标记读同位唯一，Reverse11）；
    条款 (c) = A3 欠条 `subsetSumNTM2_canonical_clauseC`（兄弟线还债后定理化）。 -/
theorem subsetSumNTM2_canonical : NTM2.Canonical subsetSumNTM2 := by
  rcases subsetSumNTM2_canonical_clauseC with ⟨K, hC⟩
  refine ⟨K, ?_⟩
  intro x π cfg hx hnoTerm hr hext
  rcases hx with ⟨inst, gS, hx'⟩
  constructor
  · exact subsetSumNTM2_clauseA ⟨inst, gS, hx'⟩ hnoTerm hr hext
  · constructor
    · exact subsetSumNTM2_clauseB hx' hr hext
    · exact hC x π cfg ⟨inst, gS, hx'⟩ hnoTerm hr hext


end Mp
