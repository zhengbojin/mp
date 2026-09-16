import Mp.SubsetSumVerifierPosBound1
import Mp.SubsetSumVerifierStepBound

/-!
# A1StepBoundBridge：T15 —— ① A-1 窗口 × ③ 步长界 的汇合层

本文件把 **③ 线成品**（`Mp.SubsetSumVerifierStepBound`）与 **① A-1 窗口**（`Mp.SubsetSumVerifierPosBound1`）
连接起来：由 `SymSteps`（真实 Sym 层运行）逐位读出 δ-11 所需的运行级逐步事实（链、步前态界、
非 101、表成员），再调 `symSteps_length_le_of_run_facts` 得到 Sym 层接受路径步数界。

## 定理
* `mem_transition_of_symSteps` / `SymChained_of_symSteps`：`SymSteps` ⇒ 运行级逐步事实
* `a1_sym_path_length_bound`（**T15**）：窗口 + 转向预算（`hturn ≤ 1632L`，δ-19-15 口径）+ 首达接受 ⇒ `p.length ≤ (1632L+1)(L+102)`
* `a1_cbtm_path_length_bound`（δ-14）：① A-1 窗口 ⇒ hwin ⇒ T15 ⇒ ×12 CBTM 层长界
* `sym_state_ne_101_of_accept` / `sym_state_eq100_of_accept` / `a1_cbtm_path_length_bound_of_accept`（δ-15）
* **C-5 接口修正（T-P5.2，2026-09-13）**：删不可满足的 `hfact` ∀-形；两定理改「`hclean` 洁净条件 + `hseg` 段界供给」形
  （直证件 `encodeState_zero_mem_acceptStates4_iff` / `bridge_run_fromState_ne100`；装配端 `truncate_keeps_prefix` 可直供 hclean）
* **T-Q3（2026-09-13）**：`hm/hpos/htarget` 退役（clauseC 无正性前提 ⇒ 不可导；C-5 后零消费）——两定理签名删三参
* **G7（2026-09-13）**：`gS` 参数化——两定理输入改 `encF4 inst ++ flat4F4 gS` / `encS inst ++ gS`（终装配前置；零消费签名手术）
* 窗口上界 `L` 由 A-1 的 `headPos ≤ 4·|wS|` 配「逐前缀头对应 `cfgcm.headPos = 4 * cfgsm.headPos`」除 4 得到。
-/

open Mp

set_option maxRecDepth 100000

namespace Mp


/-- [T15-a] SymSteps ⇒ 每步 `result ∈ transition (fromState, readSym)`。 -/
theorem mem_transition_of_symSteps {cfg0 : SymConfig} {p : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg0 p cfg) :
    ∀ s ∈ p, s.result ∈ VerifierSym.transition (s.fromState, s.readSym) := by
  induction h with
  | nil => intro s hs; simp at hs
  | cons p0 step cfg1 hprev hfrom hread htrans ih =>
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact ih s hs
      · rcases List.mem_singleton.mp hs with rfl
        rw [hfrom, hread]
        exact htrans

/-- [T15-b] 100 吸收的姊妹件：末态 ≠ 100 ⇒ 全程 `nextState ≠ 100`。 -/
theorem symSteps_next_ne100_of_end_ne100 {cfg0 cfg : SymConfig} {p : List SymStep}
    (h : SymSteps VerifierSym.transition cfg0 p cfg) (hne : cfg.state ≠ 100) :
    ∀ step ∈ p, step.result.nextState ≠ 100 := by
  induction h with
  | nil => intro step hs; simp at hs
  | cons p0 step cfg1 hprev hfrom hread htrans ih =>
      have hne_step : step.result.nextState ≠ 100 := by
        intro h100
        apply hne
        dsimp [symStepConfig]
        exact h100
      have hne1 : cfg1.state ≠ 100 := by
        intro h1
        have habs := sym_absorb_100 (cfg1.tape cfg1.headPos) step.result
          (by simpa [h1] using htrans)
        apply hne
        dsimp [symStepConfig]
        exact habs.1
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with (hs | hs)
      · exact ih hne1 s hs
      · rcases (List.mem_singleton.mp hs) with rfl
        exact hne_step


lemma getLast?_append_single {a : Type*} (l : List a) (x : a) :
    (l ++ [x]).getLast? = some x := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      cases t with
      | nil => rfl
      | cons c u => simpa using ih

lemma SymChained_snoc {l : List SymStep} {x : SymStep} (hl : SymChained l)
    (h : ∀ y : SymStep, l.getLast? = some y → x.fromState = y.result.nextState) :
    SymChained (l ++ [x]) := by
  induction l with
  | nil => trivial
  | cons a t ih =>
      cases t with
      | nil =>
          refine ⟨?_, trivial⟩
          exact h a (by rfl)
      | cons b u =>
          obtain ⟨h1, h2⟩ := hl
          exact ⟨h1, ih h2 (by intro y hy; exact h y (by simpa using hy))⟩

/-- [T15-c] SymSteps ⇒ `SymChained`（+ 末态 = 末步 `nextState` 的不变量）。 -/
theorem SymChained_of_symSteps {cfg0 : SymConfig} {p : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg0 p cfg) :
    SymChained p ∧ ∀ y : SymStep, p.getLast? = some y → cfg.state = y.result.nextState := by
  induction h with
  | nil =>
      refine ⟨trivial, ?_⟩
      intro y hy
      simp at hy
  | cons p0 step cfg1 hprev hfrom hread htrans ih =>
      obtain ⟨hc, hlast⟩ := ih
      refine ⟨SymChained_snoc hc ?_, ?_⟩
      · intro y hy
        rw [hfrom]
        exact hlast y hy
      · intro y hy
        have hys : y = step := by
          have h1 := getLast?_append_single p0 step
          rw [hy] at h1
          exact Option.some.inj h1
        subst hys
        dsimp [symStepConfig]


/-- [T15] ③ 线成品实例化：Sym 层接受路径的步数界。 -/
theorem a1_sym_path_length_bound (inst : SubsetSumInstance) (L : ℕ)
    {p : List SymStep} {cfgs : SymConfig}
    (hs : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) p cfgs)
    (haccS : cfgs.state ≠ 101)
    (hfirst : ∀ s ∈ p, s.fromState ≠ 100)
    (hturn : symTurnCount (p.map (fun st => st.result.moveDir)) ≤ 1632 * L)
    (hwin : ∀ x ∈ symPositions 0 p ++ [symEnd 0 p], 0 ≤ x ∧ x ≤ (L : ℤ))
    (h102 : ∀ x ∈ symStepPairs 0 (symInitialConfig (encodeInstanceSym inst)).state p,
      x.2 < 102 ∧ x.2 ≠ 100) :
    (p.length : ℤ) ≤ ((L : ℤ) * 1632 + 1) * ((L : ℤ) + 102) := by
  have h0 : (symInitialConfig (encodeInstanceSym inst)).state ≤ 101 := by
    dsimp [symInitialConfig]; norm_num
  have hle := (symSteps_state_le101 hs h0).2
  exact symSteps_length_le_of_run_facts_turnBudget 0 (L : ℤ) p 0
    (symInitialConfig (encodeInstanceSym inst)).state L hturn hwin h102
    (SymChained_of_symSteps hs).1
    (fun s hsmem => ⟨by have := hle s hsmem; omega, hfirst s hsmem⟩)
    (symSteps_next_ne101_of_end_ne101 hs haccS)
    (mem_transition_of_symSteps hs)

/-
  ==============================================================================
  [T15-δ-14] 最终合龙：① A-1 窗口 ⇒ CBTM 层路径长界（×12）
  ------------------------------------------------------------------------------
  · `hprefix`（= Compile `good_block_path_head_corresp` 的逐前缀头对应交付）
    + A-1 `a1_accept_path_prefix_head_nonneg/_le` ⇒ Sym 层逐前缀头位界；
  · δ-13 `hwin_of_prefix_head_facts` ⇒ T15 的 `hwin`（窗口 [0, |encodeInstanceSym inst|]）；
  · 调 `a1_sym_path_length_bound`（T15）⇒ `πs.length ≤ (1632L+1)(L+102)`；
  · `πs.length * 12 = π.length` ⇒ **CBTM 层步数界**。
  （C-5 后：本件不再被 `of_accept` 消费——供给改 `hseg`；留档备用。）
  公理足迹：仅 propext / Classical.choice / Quot.sound（0 新增）。
-/

open SymToF4

/-- [T15-δ-14] 接受路径的 CBTM 层步数界（经 Sym 层窗口）。 -/
theorem a1_cbtm_path_length_bound (inst : SubsetSumInstance)
    (hm : 0 < (encodeElementsSym inst.elements).length)
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst)}
    (h : TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) π cfg)
    (hacc : cfg.state ∈ acceptStates4)
    {πs : List SymStep} {cfgs' : SymConfig}
    (hs : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) πs cfgs')
    (hlen : πs.length * 12 = π.length)
    (hprefix : ∀ k ≤ πs.length, ∃ cfgsm : SymConfig,
        ∃ cfgcm : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst),
        SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
          (πs.take k) cfgsm ∧
        TapeSteps subsetSumCBTM (encodeInstanceF4 inst)
          (initialConfig subsetSumCBTM (encodeInstanceF4 inst)) (π.take (12 * k)) cfgcm ∧
        cfgcm.headPos = 4 * cfgsm.headPos)
    (haccS : cfgs'.state ≠ 101)
    (hfirst : ∀ s ∈ πs, s.fromState ≠ 100)
    (hturn : symTurnCount (πs.map (fun st => st.result.moveDir))
      ≤ 1632 * (encodeInstanceSym inst).length)
    (h102 : ∀ x ∈ symStepPairs 0 (symInitialConfig (encodeInstanceSym inst)).state πs,
      x.2 < 102 ∧ x.2 ≠ 100) :
    (π.length : ℤ) ≤ 12 * ((((encodeInstanceSym inst).length : ℤ) * 1632 + 1)
      * (((encodeInstanceSym inst).length : ℤ) + 102)) := by
  -- 1) 逐前缀头位界（Sym 层）
  have hbind : ∀ k ≤ πs.length, ∃ cfgm : SymConfig,
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (πs.take k) cfgm ∧
      0 ≤ cfgm.headPos ∧ cfgm.headPos ≤ ((encodeInstanceSym inst).length : ℤ) := by
    intro k hk
    obtain ⟨ cfgsm, cfgcm, hrun, hcbtm, hhead⟩ := hprefix k hk
    have hnn := a1_accept_path_prefix_head_nonneg inst hm hpos htarget h hacc
      (π.take (12 * k)) cfgcm hcbtm
      (by refine ⟨π.drop (12 * k), ?_⟩; simp [List.take_append_drop])
    have hle := a1_accept_path_prefix_head_le inst hm hpos htarget h hacc
      (π.take (12 * k)) cfgcm hcbtm
      (by refine ⟨π.drop (12 * k), ?_⟩; simp [List.take_append_drop])
    have hlenx : (((encodeInstanceF4 inst).length : ℤ))
        = (4 * ((encodeInstanceSym inst).length : ℤ)) := by
      simp [encodeInstanceF4, flat4F4_length]
    rw [hlenx] at hle
    refine ⟨ cfgsm, hrun, ?_, ?_⟩
    · omega
    · omega
  -- 2) T15 的 hwin
  have hwin := hwin_of_prefix_head_facts (encodeInstanceSym inst) hbind
  -- 3) 调 T15
  have hT15 := a1_sym_path_length_bound inst (encodeInstanceSym inst).length hs haccS hfirst
    hturn hwin h102
  -- 4) ×12 换回 CBTM 步数
  have hlen' : (π.length : ℤ) = 12 * (πs.length : ℤ) := by
    have : (πs.length * 12 : ℕ) = π.length := hlen
    omega
  rw [hlen']
  linarith

/-
  ==============================================================================
  [T15-δ-15] 合龙收口：消去 haccS + 典范路径事实族接口
  ------------------------------------------------------------------------------
  · `sym_state_ne_101_of_accept`：`blockCorrespond` + 接受态 ⇒ Sym 末态 ≠ 101（消去δ-14 的 haccS）。
  · `sym_state_eq100_of_accept`（C-5）：`blockCorrespond` + 接受态 ⇒ Sym 末态 = 100。
  · `A1CanonicalPathFacts`：典范路径事实族（hfirst / 转向预算 / h102）——【C-5 后已无消费：hturn 路线废弃，留档备用】。
  · `a1_cbtm_path_length_bound_of_accept`：好块路径 + 桥 + 供给 ⇒ CBTM 层步数界（无 haccS）。
  ==============================================================================
  【C-5 接口修正（T-P5.2，2026-09-13）】
  原 `hfact : ∀ πs cfgs', SymSteps … → A1CanonicalPathFacts …` 为**不可满足**的 ∀-形
  （「接受路径 + 100 自环」即反例；更一般地：100 吸收 ⇒ 无条件 ∀-形长界一律为假）。
  修正 = 删 `hfact`；接口改「洁净条件 + 段界供给」：
  · `hclean`：`π` 各步来态 ∉ acceptStates4 —— 装配端 `truncate_keeps_prefix` 输出（hnoT）的逐字形
    （即 R3「截断纪律」的接口化：不得对含 100 后续步的路径直接套长界）；
  · `hseg`：对**洁净、终达 100** 的桥产出运行给长度供给 —— 槽位 = v5 链段界经「位移（`symMoves`）+ S 吸收」
    折算后的产物；本文件因 R13 反向 import 约束不引用位移件（口径=位移、接口=长度）。
  直证件：`encodeState_zero_mem_acceptStates4_iff`、`bridge_run_fromState_ne100`（桥产出洁净性）。
  【T-Q3（2026-09-13）：`hm/hpos/htarget` 退役】clauseC 签名（Q10:306）无正性前提 ⇒ 终装配中不可导出；
  且 C-5 后本链零消费（构建 warning 即证、全仓零消费）⇒ 两定理签名删三参。
  【G7（2026-09-13）：`gS` 参数化】输入通形化：`encodeInstanceF4 inst ++ flat4F4 gS` / `encodeInstanceSym inst ++ gS`
  （h/corr/GoodBlockPath/hseg/结论 同步；`hseg` 界取 `E := |encS inst ++ gS|`）；`canonical_bound_enlarge` 左因子
  同步通形（`4·|encS++gS| + 1 = |x| + 1` 实为等式）。终装配（T-P5.3）按 gS 任意形接线；零消费签名手术。
  公理足迹：仅 propext / Classical.choice / Quot.sound（0 新增）。
-/

/-- [T15-δ-15a] `blockCorrespond` + 接受态 ⇒ Sym 末态 ≠ 101。 -/
lemma sym_state_ne_101_of_accept {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {cfgs : SymConfig} (hcorr : blockCorrespond cfgc cfgs) (hacc : cfgc.state ∈ acceptStates4) :
    cfgs.state ≠ 101 := by
  intro h101
  have hmem : encodeState 101 0 0 ∈ acceptStates4 := by
    have hh := hacc
    rw [hcorr.1, h101] at hh
    exact hh
  dsimp [acceptStates4] at hmem
  rcases Finset.mem_image.mp hmem with ⟨reg0, hreg0, h⟩
  have hreg0' : reg0 < 8192 := by simpa [regBound] using Finset.mem_range.mp hreg0
  dsimp [encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept] at h
  omega

/-- [C-5 直证] 0 号寄存器态刻画：`encodeState q 0 0 ∈ acceptStates4 ↔ q = 100`。 -/
lemma encodeState_zero_mem_acceptStates4_iff (q : ℕ) :
    encodeState q 0 0 ∈ acceptStates4 ↔ q = 100 := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨reg0, hreg0, h⟩
    have hreg0' : reg0 < 8192 := by simpa [regBound] using Finset.mem_range.mp hreg0
    dsimp [encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept] at h
    omega
  · intro h
    subst h
    refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
    · simp [regBound]
    · rfl

/-- [T15-δ-15a′ · C-5] `blockCorrespond` + 接受态 ⇒ Sym 末态 = 100。 -/
lemma sym_state_eq100_of_accept {w : List F4} {cfgc : CBTMConfig subsetSumCBTM w}
    {cfgs : SymConfig} (hcorr : blockCorrespond cfgc cfgs) (hacc : cfgc.state ∈ acceptStates4) :
    cfgs.state = 100 :=
  (encodeState_zero_mem_acceptStates4_iff cfgs.state).mp (by
    have hh := hacc
    rw [hcorr.1] at hh
    exact hh)

/-- [C-5 工具] `l.take (k+1) = l.take k ++ [l[k]]`（mathlib 无 `take_succ`）。 -/
lemma take_succ_eq_take_append_getElem {α : Type*} {l : List α} {k : ℕ} (hk : k < l.length) :
    l.take (k+1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k < t.length := by simpa using hk
      simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
      rw [ih hk']

/-- [C-5 工具] `TapeSteps` 前缀分解（照 `symSteps_append_split` 模式）。 -/
lemma tapeSteps_append_split {M : CBTM} {input : List F4} {cfg₀ cfg' : CBTMConfig M input}
    {π₀ rest : ComputationPath} (h : TapeSteps M input cfg₀ (π₀ ++ rest) cfg') :
    ∃ cfg₁ : CBTMConfig M input, TapeSteps M input cfg₀ π₀ cfg₁ ∧ TapeSteps M input cfg₁ rest cfg' := by
  revert h
  revert cfg'
  induction rest using List.reverseRecOn with
  | nil =>
      intro cfg' h
      refine ⟨cfg', ?_, ?_⟩
      · simpa using h
      · exact TapeSteps.nil
  | append_singleton rest' step ih =>
      intro cfg' h
      rw [← List.append_assoc] at h
      generalize hL : (π₀ ++ rest') ++ [step] = L at h
      induction h with
      | nil => simp at hL
      | cons πs step' cfg₁ hprev hfrom hread htrans _ =>
          have hsnoc := snoc_eq_snoc (α := TransitionStep) (π₁ := π₀ ++ rest') (π₂ := πs)
            (a := step) (b := step') (by simpa [List.append_assoc] using hL)
          rcases hsnoc with ⟨hπs, hstep'⟩
          subst hstep'
          have hprev' : TapeSteps M input cfg₀ (π₀ ++ rest') cfg₁ := by simpa [hπs] using hprev
          rcases ih hprev' with ⟨cfg₂, h₁, h₂⟩
          refine ⟨cfg₂, h₁, ?_⟩
          have hlast : TapeSteps M input cfg₁ [step] (stepConfig cfg₁ step.result) := by
            exact TapeSteps.cons (M := M) (input := input) (cfg₀ := cfg₁) [] step cfg₁
              TapeSteps.nil hfrom hread htrans
          simpa [List.append_assoc] using
            (tapeSteps_append (M := M) (input := input) (π₁ := rest') (π₂ := [step]) h₂ hlast)

/-- [C-5 工具] `TapeSteps` 单步路径的来态（照 `symSteps_singleton_fromState` 模式）。 -/
lemma tapeSteps_singleton_fromState {M : CBTM} {input : List F4} {cfg₀ cfg' : CBTMConfig M input}
    {step : TransitionStep} (h : TapeSteps M input cfg₀ [step] cfg') :
    step.fromState = cfg₀.state := by
  generalize hL : [step] = L at h
  induction h with
  | nil => simp at hL
  | cons πs step' cfg₁ hprev hfrom hread htrans _ =>
      have hsnoc := snoc_eq_snoc (α := TransitionStep) (π₁ := []) (π₂ := πs)
        (a := step) (b := step') (by simpa using hL)
      rcases hsnoc with ⟨hπs, hstep'⟩
      subst hstep'
      have hcfg₁ : cfg₁ = cfg₀ := tapeSteps_empty (by simpa [hπs] using hprev) rfl
      rw [hfrom, hcfg₁]

/-- [C-5·直证] 桥产出运行洁净性：`π` 无接受态起步 + 逐块前缀对应 ⇒ πs 每步来态 ≠ 100。
    手法：Link-1（Sym 侧：`symSteps_split`-系 `sym_steps_det` + `symSteps_singleton_fromState`）、
    Link-2（CBTM 侧：`tapeSteps_append_split` + `tapeSteps_det` + `tapeSteps_singleton_fromState`）、
    汇合（`encodeState_zero_mem_acceptStates4_iff` 逆否）。 -/
lemma bridge_run_fromState_ne100 {w : List F4} {input : List Sym}
    {π : ComputationPath} {πs : List SymStep}
    {cfg : CBTMConfig subsetSumCBTM w}
    (h : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) π cfg)
    (hlen : πs.length * 12 = π.length)
    (hprefix : ∀ k ≤ πs.length, ∃ cfgsm : SymConfig, ∃ cfgcm : CBTMConfig subsetSumCBTM w,
      SymSteps VerifierSym.transition (symInitialConfig input) (πs.take k) cfgsm ∧
      TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w) (π.take (12 * k)) cfgcm ∧
      cfgcm.headPos = 4 * cfgsm.headPos ∧
      cfgcm.state = encodeState cfgsm.state 0 0)
    (hclean : ∀ step ∈ π, step.fromState ∉ acceptStates4) :
    ∀ s ∈ πs, s.fromState ≠ 100 := by
  intro s hs
  obtain ⟨k, hk, hk_eq⟩ := List.mem_iff_getElem.mp hs
  subst hk_eq
  obtain ⟨cfgsm, cfgcm, hsym, htap, _hhead, hst6⟩ := hprefix k (Nat.le_of_lt hk)
  -- (a) Sym 侧：fromState(πs[k]) = cfgsm.state
  obtain ⟨cfgsm', _cfgcm', hsym', _hrest'⟩ := hprefix (k + 1) (by omega)
  have htake : πs.take (k + 1) = πs.take k ++ [πs[k]] := take_succ_eq_take_append_getElem hk
  have hsplitS : ∃ cm : SymConfig,
      SymSteps VerifierSym.transition (symInitialConfig input) (πs.take k) cm ∧
      SymSteps VerifierSym.transition cm [πs[k]] cfgsm' := by
    have h' := hsym'
    rw [htake] at h'
    exact symSteps_append_split h'
  obtain ⟨cmS, hcmS₁, hcmS₂⟩ := hsplitS
  have hcmS_eq : cmS = cfgsm := sym_steps_det (πs.take k) hcmS₁ hsym
  have hfromS : (πs[k]).fromState = cfgsm.state := by
    rw [← hcmS_eq]
    exact (symSteps_singleton_fromState hcmS₂).1
  -- (b) Tape 侧：fromState(π[12k]) = cfgcm.state
  have h12k : 12 * k < π.length := by omega
  have hsplitT : TapeSteps subsetSumCBTM w (initialConfig subsetSumCBTM w)
      (π.take (12 * k) ++ π.drop (12 * k)) cfg := by
    rw [List.take_append_drop]
    exact h
  obtain ⟨cmT, hcmT₁, hcmT₂⟩ := tapeSteps_append_split hsplitT
  have hcmT_eq : cmT = cfgcm := tapeSteps_det (π.take (12 * k)) hcmT₁ htap
  have hdrop : π.drop (12 * k) = [π[12 * k]] ++ π.drop (12 * k + 1) := by
    rw [List.drop_eq_getElem_cons h12k]
    rw [List.singleton_append]
  have hcmT₂' : TapeSteps subsetSumCBTM w cmT (π.drop (12 * k)) cfg := hcmT₂
  rw [hdrop] at hcmT₂'
  obtain ⟨cmT2, hsingleT, _hrestT⟩ := tapeSteps_append_split hcmT₂'
  have hfromT : (π[12 * k]).fromState = cfgcm.state := by
    rw [← hcmT_eq]
    exact tapeSteps_singleton_fromState hsingleT
  -- (c) 汇合：hclean + B
  have hnotmem : cfgcm.state ∉ acceptStates4 := by
    have hcc := hclean (π[12 * k]) (List.getElem_mem h12k)
    rwa [hfromT] at hcc
  have hnotmem' : encodeState cfgsm.state 0 0 ∉ acceptStates4 := by
    rwa [hst6] at hnotmem
  have hstne : cfgsm.state ≠ 100 := fun h100 =>
    hnotmem' ((encodeState_zero_mem_acceptStates4_iff cfgsm.state).mpr h100)
  rw [hfromS]
  exact hstne

/-- [T15-δ-15b] 典范路径事实族（Canonical 条款 3 供给）。
    δ-19-15 口径重述：H_triple(`Nodup`) 已实测为假 ⇒ 改为**转向预算**字段。
    【C-5 后已无消费：hturn 路线废弃；留档备用——勿据此重建 `hfact` 形。】 -/
def A1CanonicalPathFacts (inst : SubsetSumInstance) (L : ℕ) (πs : List SymStep) : Prop :=
  (∀ s ∈ πs, s.fromState ≠ 100) ∧
  (symTurnCount (πs.map (fun st => st.result.moveDir)) ≤ 1632 * L) ∧
  (∀ x ∈ symStepPairs 0 (symInitialConfig (encodeInstanceSym inst)).state πs,
    x.2 < 102 ∧ x.2 ≠ 100)

/-- [T15-δ-15c · C-5/T-Q3/G7 修正] 最终形式：好块路径 + 桥 + **洁净条件 + 段界供给** ⇒ CBTM 层步数界（gS 任意）。
    （删原不可满足 `hfact`；`hclean` 供洁净、`hseg` 供长度——槽位 = v5 链段界产物，见上方 C-5 块注；
    `hm/hpos/htarget` 已退役：clauseC 无正性前提 ⇒ 不可导 + 本链零消费；G7：输入 = `encF4 inst ++ flat4F4 gS`。） -/
theorem a1_cbtm_path_length_bound_of_accept (inst : SubsetSumInstance) (gS : List Sym)
    {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)}
    (h : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg)
    (hacc : cfg.state ∈ acceptStates4)
    (hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (symInitialConfig (encodeInstanceSym inst ++ gS)))
    (hbp : GoodBlockPath (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg)
    (hno101 : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (hclean : ∀ step ∈ π, step.fromState ∉ acceptStates4)
    (hseg : ∀ (πs : List SymStep) (cfgs' : SymConfig),
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs' →
      (∀ s ∈ πs, s.fromState ≠ 100) → cfgs'.state = 100 →
      (πs.length : ℤ) ≤ (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1)
        * (((encodeInstanceSym inst ++ gS).length : ℤ) + 102)) :
    (π.length : ℤ) ≤ 12 * ((((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1)
      * (((encodeInstanceSym inst ++ gS).length : ℤ) + 102)) := by
  obtain ⟨πs, cfgs', hs, hcorr', hlen, hprefix⟩ :=
    good_block_path_head_corresp (encodeInstanceF4 inst ++ flat4F4 gS) (encodeInstanceSym inst ++ gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (symInitialConfig (encodeInstanceSym inst ++ gS)) π cfg hcorr0 hbp hno101
  have hst : cfgs'.state = 100 := sym_state_eq100_of_accept hcorr' hacc
  have hcleanS : ∀ s ∈ πs, s.fromState ≠ 100 :=
    bridge_run_fromState_ne100 (input := encodeInstanceSym inst ++ gS) h hlen hprefix hclean
  have hb := hseg πs cfgs' hs hcleanS hst
  have hlen' : (π.length : ℤ) = 12 * (πs.length : ℤ) := by
    have := hlen
    omega
  rw [hlen']
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-
  ==============================================================================
  [T15-δ-16] (c) 左支算术提升：O(L²) 长界 ⇒ `NTM2.Canonical` 口径
  ------------------------------------------------------------------------------
  · `twelve_bound_le_canonical_form`：`12·(1632L+1)(L+102) ≤ 1997568·(m+1)·(4L+1)²`
    （h1: 1632L+1 ≤ 1632(L+1)；h2: L+102 ≤ 102(L+1)；h3: (L+1)² ≤ (4L+1)²；再用 m+1 ≥ 1）
  · `a1_cbtm_path_length_bound_canonical`：（c）左支的 **K·(m+1)·(4|wS|+1)²** 口径版
    （K = 1997568 = 12·1632·102）——与 `NTM2.Canonical` 第三枚断句逐字对齐。
  公理足迹：δ-16a 仅 3 标准；δ-16b 继承(①②线表级公理)。
-/

/-- [δ-16a] 算术：12·(1632L+1)(L+102) ≤ 1997568·(m+1)·(4L+1)²。 -/
theorem twelve_bound_le_canonical_form (L m : ℕ) :
    (12 : ℤ) * (((L : ℤ) * 1632 + 1) * ((L : ℤ) + 102)) ≤
      (1997568 : ℤ) * ((m : ℤ) + 1) * (4 * (L : ℤ) + 1) ^ 2 := by
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  have hm : (1 : ℤ) ≤ (m : ℤ) + 1 := by omega
  have h1 : (L : ℤ) * 1632 + 1 ≤ 1632 * ((L : ℤ) + 1) := by linarith
  have h2 : (L : ℤ) + 102 ≤ 102 * ((L : ℤ) + 1) := by linarith
  have h3 : ((L : ℤ) + 1) ^ 2 ≤ (4 * (L : ℤ) + 1) ^ 2 := by nlinarith [hL]
  nlinarith [h1, h2, h3, hm, hL, sq_nonneg ((L : ℤ) + 1), sq_nonneg (4 * (L : ℤ) + 1)]

/-- [δ-16b · C-5/T-Q3/G7] 最终长界的 `NTM2.Canonical` (c) 左支口径版本（接口同上：`hclean` + `hseg` + gS 任意）。 -/
theorem a1_cbtm_path_length_bound_canonical (inst : SubsetSumInstance) (gS : List Sym)
    {π : ComputationPath} {cfg : CBTMConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)}
    (h : TapeSteps subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg)
    (hacc : cfg.state ∈ acceptStates4)
    (hcorr0 : blockCorrespond (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS))
      (symInitialConfig (encodeInstanceSym inst ++ gS)))
    (hbp : GoodBlockPath (encodeInstanceF4 inst ++ flat4F4 gS)
      (initialConfig subsetSumCBTM (encodeInstanceF4 inst ++ flat4F4 gS)) π cfg)
    (hno101 : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101)
    (hclean : ∀ step ∈ π, step.fromState ∉ acceptStates4)
    (hseg : ∀ (πs : List SymStep) (cfgs' : SymConfig),
      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst ++ gS)) πs cfgs' →
      (∀ s ∈ πs, s.fromState ≠ 100) → cfgs'.state = 100 →
      (πs.length : ℤ) ≤ (((encodeInstanceSym inst ++ gS).length : ℤ) * 1632 + 1)
        * (((encodeInstanceSym inst ++ gS).length : ℤ) + 102))
    (m : ℕ) :
    (π.length : ℤ) ≤ (1997568 : ℤ) * ((m : ℤ) + 1)
      * (4 * ((encodeInstanceSym inst ++ gS).length : ℤ) + 1) ^ 2 := by
  refine le_trans
    (a1_cbtm_path_length_bound_of_accept inst gS h hacc hcorr0 hbp hno101 hclean hseg) ?_
  exact twelve_bound_le_canonical_form (encodeInstanceSym inst ++ gS).length m

/-
  ==============================================================================
  [T15-δ-17] 宽度换算：迁到 `NTM2.Canonical` 定义所用的 |x| 尺度
  ------------------------------------------------------------------------------
  δ-16b（G7 后）给出 `K·(m+1)·(4|wS ++ gS|+1)²`，而定义的第三枚断句用
  `K·(m+1)·(|x|+1)²`（x = encodeInstanceF4 inst ++ flat4F4 gS）。
  由 `|encF4 inst| = 4|wS|` 与 `|x| = |encF4 inst| + 4|gS|` 得 **`4|wS ++ gS| + 1 = |x| + 1`（等式）**
  ⇒ 直接改写对齐（两侧因子恒等）。
  公理足迹：仅 propext / Classical.choice / Quot.sound。
-/

/-- [δ-17 · G7] 将 δ-16b 的 `K·(m+1)·(4|wS ++ gS|+1)²` 对齐到 `NTM2.Canonical`
    所用的 `K·(m+1)·(|x|+1)²`（x = encodeInstanceF4 inst ++ flat4F4 gS；两侧因子恒等）。 -/
theorem canonical_bound_enlarge (inst : SubsetSumInstance) (gS : List Sym) (m : ℕ) :
    (1997568 : ℤ) * ((m : ℤ) + 1)
        * (4 * (((encodeInstanceSym inst) ++ gS).length : ℤ) + 1) ^ 2
      ≤ (1997568 : ℤ) * ((m : ℤ) + 1)
        * (((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) + 1) ^ 2 := by
  have hlen : (((encodeInstanceSym inst) ++ gS).length : ℤ)
      = ((encodeInstanceSym inst).length : ℤ) + (gS.length : ℤ) := by
    simp [List.length_append]
  have h1 : ((encodeInstanceF4 inst).length : ℤ) = 4 * ((encodeInstanceSym inst).length : ℤ) := by
    simp [encodeInstanceF4, flat4F4_length]
  have h2 : ((flat4F4 gS).length : ℤ) = 4 * (gS.length : ℤ) := by
    simp [flat4F4_length]
  have hx : (((encodeInstanceF4 inst) ++ flat4F4 gS).length : ℤ)
      = 4 * ((encodeInstanceSym inst).length : ℤ) + 4 * (gS.length : ℤ) := by
    simp [List.length_append, h1, h2]
  have heq : 4 * (((encodeInstanceSym inst) ++ gS).length : ℤ) + 1
      = (((encodeInstanceF4 inst ++ flat4F4 gS).length : ℤ) + 1) := by
    rw [hlen, hx]
    ring
  rw [heq]

end Mp
