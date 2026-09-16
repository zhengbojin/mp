/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierCore
import Mp.SubsetSumVerifierCBTM2

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
set_option linter.style.emptyLine false
set_option linter.style.setOption false

set_option maxHeartbeats 4000000

/-!
# 任务5：投影（CBTM 磁带路径 → Sym 路径）

把 subsetSumCBTM 的 12 步块路径投影回 Sym 层：每 12 个 CBTM 步
（一个 4F4 展开块）对应一个 Sym 步。核心概念：

- `GoodBlock`：一个 12 步块的第 4 步（phase 3 合成步）可解码为合法
  Sym 转移 r ∈ VerifierSym.transition (q, sym)，块末态（状态 + 带头）
  回到块起点 + 一个 Sym 步的位移；
- `project_block`：好块 + 首块对应 ⟹ 末块对应（块的逐步唯一性）；
- `GoodBlockPath` / `project_path_gen` / `project_path`：沿块路径归纳，
  把好块路径投影为 SymReachablePath（起点固定为初始配置）；
- 辅助：状态 101（陷阱态）在 transition4 下封闭（trap 不可在
  接受路径中恢复），供任务6 的"接受路径 ⟹ 全好块"使用。

-/
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.style.nativeDecide false
namespace Mp
open CBTM
namespace SymToF4

-- ======================================================================
-- §1 TapeSteps 的拆分引理
-- ======================================================================

/-- 非空 TapeSteps 路径拆出末步与其前缀。 -/
lemma tapeSteps_split_last {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) (hπ : π ≠ []) :
    ∃ step : TransitionStep, ∃ π₀ : ComputationPath, ∃ cfg₁ : CBTMConfig M input,
      π = π₀ ++ [step] ∧ TapeSteps M input cfg₀ π₀ cfg₁ ∧
      step.fromState = cfg₁.state ∧ step.readSym = cfg₁.tapeAt cfg₁.headPos ∧
      step.result ∈ M.transition (cfg₁.state, cfg₁.tapeAt cfg₁.headPos, cfg₁.headPos) ∧
      cfg = stepConfig cfg₁ step.result := by
  cases h with
  | nil => exact (hπ rfl).elim
  | cons π₀ step cfg₁ hprev hfrom hread htrans =>
      exact ⟨step, π₀, cfg₁, rfl, hprev, hfrom, hread, htrans, rfl⟩

/-- TapeSteps 的末步取出：末步的转移合法性（按 step 自身字段表述）与末格局。 -/
lemma tapeSteps_last_step {M : CBTM} {input : List F4} {cfg₀ : CBTMConfig M input}
    {π : ComputationPath} {cfg : CBTMConfig M input}
    (h : TapeSteps M input cfg₀ π cfg) (hπ : π ≠ []) :
    ∃ step : TransitionStep, ∃ π₀ : ComputationPath, ∃ cfg₁ : CBTMConfig M input,
      π = π₀ ++ [step] ∧ TapeSteps M input cfg₀ π₀ cfg₁ ∧
      step.result ∈ M.transition (step.fromState, step.readSym, cfg₁.headPos) ∧
      cfg = stepConfig cfg₁ step.result := by
  rcases tapeSteps_split_last h hπ with ⟨step, π₀, cfg₁, hπe, hprev, hfrom, hread, htrans, hcfg⟩
  exact ⟨step, π₀, cfg₁, hπe, hprev, by simpa [hfrom, hread] using htrans, hcfg⟩

-- ======================================================================
-- §2 陷阱态 101 的封闭性
-- ======================================================================

/-- 从状态 101 出发，transition4 的所有结果仍以 101 为状态前缀
（phase ≠ 11 的情形；phase = 11 时以 min (decodeResult reg).nextState 101 重启）。 -/
lemma transition4_state101_closed (ph reg : ℕ) (hph : ph < 12) (hreg : reg < regBound)
    (s : F4) (r : CBTMTransResult) (hr : r ∈ transition4 (encodeState 101 ph reg) s) :
    (∃ ph' reg', r.nextState = encodeState 101 ph' reg') ∨
    (ph = 11 ∧ r.nextState = encodeState (min (decodeResult reg).nextState 101) 0 0) := by
  simp only [transition4] at hr
  rw [decodeState_encodeState 101 ph reg (by simpa [stepsPerSym] using hph)
    (by simpa [regBound] using hreg)] at hr
  have hqs : min 101 101 = 101 := rfl
  by_cases hph3 : ph < 3
  · by_cases him : F4.im s <;> simp [hph3, him, hqs] at hr
    · rcases hr with h1 | h1 <;> rw [h1] <;> left <;> refine ⟨_, _, rfl⟩
    · rw [hr] at *
      left
      refine ⟨_, _, rfl⟩
  · by_cases hphE : ph = 3
    · by_cases him : F4.im s <;> simp [hph3, hphE, him, hqs] at hr
      · split at hr
        · change r ∈ ({CBTMTransResult.mk (encodeState 101 4 0) s Dir.S,
            CBTMTransResult.mk (encodeState 101 4 0) s Dir.R} : Finset CBTMTransResult) at hr
          rcases (by simpa using hr) with h1 | h1 <;> rw [h1] <;> left <;> refine ⟨_, _, rfl⟩
        · change r ∈ ({CBTMTransResult.mk (encodeState 101 4 0) s Dir.S,
            CBTMTransResult.mk (encodeState 101 4 0) s Dir.R} : Finset CBTMTransResult) at hr
          rcases (by simpa using hr) with h1 | h1 <;> rw [h1] <;> left <;> refine ⟨_, _, rfl⟩
      · split at hr
        · change r ∈ ({CBTMTransResult.mk (encodeState 101 4 0) s Dir.S} : Finset CBTMTransResult) at hr
          have h1 : r = CBTMTransResult.mk (encodeState 101 4 0) s Dir.S := by simpa using hr
          rw [h1]
          left
          refine ⟨_, _, rfl⟩
        · simp [Finset.mem_image] at hr
          rcases hr with ⟨r0, hr0, hf⟩
          rw [← hf]
          left
          refine ⟨4, encodeResult r0, ?_⟩
          have h101 : r0.nextState = 101 := by
            -- hr0 : r0 ∈ VerifierSym.transition (101, sym)，sym 由类型推断
            have hb : ∀ s : Sym, ∀ r' : SymTransResult,
                r' ∈ VerifierSym.transition (101, s) → r'.nextState = 101 := by
              native_decide
            exact hb _ r0 hr0
          simp [h101]
    · by_cases hph8 : ph < 8
      · by_cases him : F4.im s <;> simp [hph3, hphE, hph8, him, hqs] at hr
        · rcases hr with h1 | h1 <;> rw [h1] <;> left <;> refine ⟨_, _, rfl⟩
        · by_cases h4 : ph = 4 <;> by_cases h5 : ph = 5 <;> by_cases h6 : ph = 6 <;>
            (simp [h4, h5, h6] at hr; rw [hr] at *; left;
             refine ⟨(if ph = 4 then 5 else if ph = 5 then 6 else if ph = 6 then 7 else 8), reg,
               by simp [h4, h5, h6]⟩)
      · by_cases hph12 : ph < 12
        · by_cases h11 : ph = 11
          · by_cases him : F4.im s <;> simp [hph3, hphE, hph8, hph12, h11, him, hqs] at hr
            · rcases hr with h1 | h1
              · rw [h1] at *
                left
                refine ⟨0, 0, rfl⟩
              · left
                simpa [h1]
            · rw [hr] at *
              left
              refine ⟨0, 0, rfl⟩
          · by_cases him : F4.im s <;> simp [hph3, hphE, hph8, hph12, h11, him, hqs] at hr
            · rcases hr with h1 | h1 <;> rw [h1] <;> left <;> refine ⟨_, _, rfl⟩
            · rw [hr] at *
              left
              refine ⟨_, _, rfl⟩
        · exfalso
          exact hph12 (by simpa [stepsPerSym] using hph)

/-- 相位 ≥ 4 的 101 态保持 reg 安全（decodeResult reg .nextState ≠ 100）：
    写回阶段 4-7 与移动阶段 8-10 均保持 reg（或陷阱复位为 0）；
    phase = 11 ∧ im=true 的「好路径」重启为 (min (decodeResult reg).nextState 101, 0, 0)，
    由 hregs 排除重启到接受态的可能。 -/
lemma transition4_state101_closed_reg_safe (ph reg : ℕ) (hph4 : 4 ≤ ph) (hph : ph < 12)
    (hreg : reg < regBound) (hregs : (decodeResult reg).nextState ≠ 100)
    (s : F4) (r : CBTMTransResult) (hr : r ∈ transition4 (encodeState 101 ph reg) s) :
    (∃ ph' reg', r.nextState = encodeState 101 ph' reg' ∧ (decodeResult reg').nextState ≠ 100) ∨
    (ph = 11 ∧ r.nextState = encodeState (min (decodeResult reg).nextState 101) 0 0) := by
  simp only [transition4] at hr
  rw [decodeState_encodeState 101 ph reg (by simpa [stepsPerSym] using hph)
    (by simpa [regBound] using hreg)] at hr
  have hqs : min 101 101 = 101 := rfl
  have hph3 : ¬ ph < 3 := by omega
  have hphE : ph ≠ 3 := by omega
  by_cases hph8 : ph < 8
  · -- 写回阶段 4-7：im=true 进陷阱（reg=0）；否则单结果，reg 保持
    have hphne : ph ≠ 11 := by omega
    by_cases him : F4.im s <;> simp [hph3, hphE, hph8, him, hqs] at hr
    · rcases hr with h1 | h1
      · rw [h1] at *
        left
        refine ⟨ph + 1, 0, ?_⟩
        · constructor
          · simp [hphne]
          · norm_num [decodeResult]
      · rw [h1] at *
        left
        refine ⟨ph + 1, 0, ?_⟩
        · constructor
          · simp [hphne]
          · norm_num [decodeResult]
    · by_cases h4 : ph = 4 <;> by_cases h5 : ph = 5 <;> by_cases h6 : ph = 6 <;>
        (simp [h4, h5, h6] at hr; rw [hr] at *; left;
         refine ⟨(if ph = 4 then 5 else if ph = 5 then 6 else if ph = 6 then 7 else 8), reg,
           by simp [h4, h5, h6, hqs], by exact hregs⟩)
  · -- 移动阶段 8-11
    by_cases hph12 : ph < 12
    · by_cases h11 : ph = 11
      · by_cases him : F4.im s <;> simp [hph3, hphE, hph8, hph12, h11, him, hqs] at hr
        · rcases hr with h1 | h1
          · rw [h1] at *
            left
            refine ⟨0, 0, ?_⟩
            · constructor
              · rfl
              · norm_num [decodeResult]
          · rw [h1] at *
            left
            refine ⟨0, 0, ?_⟩
            · constructor
              · rfl
              · norm_num [decodeResult]
        · rw [hr] at *
          left
          refine ⟨0, 0, ?_⟩
          · constructor
            · rfl
            · norm_num [decodeResult]
      · have hphne' : ph ≠ 11 := h11
        by_cases him : F4.im s <;> simp [hph3, hphE, hph8, hph12, h11, him, hqs] at hr
        · rcases hr with h1 | h1
          · rw [h1] at *
            left
            refine ⟨ph + 1, reg, ?_⟩
            · constructor
              · simp [hphne']
              · exact hregs
          · rw [h1] at *
            left
            refine ⟨ph + 1, 0, ?_⟩
            · constructor
              · simp [hphne']
              · norm_num [decodeResult]
        · rw [hr] at *
          left
          refine ⟨ph + 1, 0, ?_⟩
          · constructor
            · simp [hphne']
            · norm_num [decodeResult]
    · exfalso
      exact hph12 (by simpa [stepsPerSym] using hph)

/-- 从陷阱态 101 出发的任意步都不进入接受态。
前提 hregq 记录 reg 的真实可达形态（nextState ∈ {0,101} 的推论）：
phase-11 重启行 min (decodeResult reg).nextState 101 对任意 reg 并不封闭
（如 reg = 5400 时重启到 encodeState 100 0 0 ∈ acceptStates4），
但真实路径中 reg 只能取 0 或 encodeResult(101 转移) 两类值。 -/
lemma transition4_state101_not_accept (ph reg : ℕ) (hph : ph < 12) (hreg : reg < regBound)
    (hregq : (decodeResult reg).nextState ≠ 100)
    (s : F4) (r : CBTMTransResult) (hr : r ∈ transition4 (encodeState 101 ph reg) s) :
    r.nextState ∉ acceptStates4 := by
  rcases transition4_state101_closed ph reg hph hreg s r hr with h | h
  · rcases h with ⟨ph', reg', hst⟩
    rw [hst]
    dsimp [acceptStates4]
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨reg0, hreg0, h⟩
    have hreg0' : reg0 < 8192 := by simpa [regBound] using (Finset.mem_range.mp hreg0)
    dsimp [encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept] at h
    omega
  · rcases h with ⟨hph11, hst⟩
    rw [hst]
    dsimp [acceptStates4]
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨reg0, hreg0, h⟩
    have hreg0' : reg0 < 8192 := by simpa [regBound] using (Finset.mem_range.mp hreg0)
    dsimp [encodeState, qBound, stepsPerSym, regBound, VerifierSym.qAccept] at h
    by_cases hx : (decodeResult reg).nextState ≤ 101
    · have hm := Nat.min_eq_left hx
      rw [hm] at h
      omega
    · have hm := Nat.min_eq_right (by omega : 101 ≤ (decodeResult reg).nextState)
      rw [hm] at h
      omega

/-- im=false 的读转移结果唯一（card = 1）。供 project_block 的逐步唯一性使用。 -/
lemma transition4_unique_of_im_false (st : ℕ) (s : F4) (him : F4.im s = false)
    {r r' : CBTMTransResult} (hr : r ∈ transition4 st s) (hr' : r' ∈ transition4 st s) :
    r = r' := by
  have hcard := transition4_card_one_of_im_false st s him
  rcases Finset.card_eq_one.mp hcard with ⟨r₀, hr₀⟩
  have : r = r₀ := by
    have : r ∈ ({r₀} : Finset CBTMTransResult) := by simpa [hr₀] using hr
    simpa using this
  rw [this]
  have : r' = r₀ := by
    have : r' ∈ ({r₀} : Finset CBTMTransResult) := by simpa [hr₀] using hr'
    simpa using this
  rw [this]

-- ======================================================================
-- §3 好块的定义与块路径
-- ======================================================================

/-- 一个 12 步块是好块：第 4 步（phase 3 合成步）携带合法 Sym 转移结果
r ∈ VerifierSym.transition (q, sym)，块末态回到块起点（状态 phase 0、
带头 = 起点 + 4·moveDir），且 Sym 侧满足验证器的良构性前提
（q ≤ 101、分支读仅出现在 q = 2、读入符号的值位合法）。
v2：加 hrs : r.nextState < 101 前提——接受路径上无 101 步（陷阱态 101 吸收后
无法到达 qAccept=100），该前提排除 transition4 移动阶段的 q=101 陷阱吸收分支
（ad97191 引入），使块内第 8-11 步的转移结果与旧语义一致。 -/
def GoodBlock (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (π : ComputationPath)
    (cfgc' : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (q : ℕ) (sym : Sym) (r : SymTransResult) : Prop :=
  ∃ hpath : TapeSteps subsetSumCBTM w cfgc π cfgc',
  ∃ hlen : π.length = 12,
    cfgc.state = encodeState q 0 0 ∧
    cfgc.headPos = 4 * p ∧
    blockCorrespond cfgc cfgs ∧
    cfgs.tape p = sym ∧
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
    cfgc'.headPos = 4 * p + 4 * (r.moveDir).toInt

/-- 好块依次串联成的块路径。 -/
inductive GoodBlockPath (w : List F4) :
    CBTMConfig subsetSumCBTM w → ComputationPath → CBTMConfig subsetSumCBTM w → Prop
  | nil : ∀ (cfgc : CBTMConfig subsetSumCBTM w), GoodBlockPath w cfgc [] cfgc
  | cons : ∀ (cfgc cfgm cfgc' : CBTMConfig subsetSumCBTM w) (πm π : ComputationPath)
      (cfgs : SymConfig) (p : ℤ) (q : ℕ) (sym : Sym) (r : SymTransResult),
      GoodBlock w cfgc πm cfgm cfgs p q sym r →
      GoodBlockPath w cfgm π cfgc' →
      GoodBlockPath w cfgc (πm ++ π) cfgc'

-- ======================================================================
-- §4 投影
-- ======================================================================

/-- 空路径 TapeSteps 的终点必是起点（归纳 + 长度矛盾，避开依赖消元）。 -/
lemma tapeSteps_empty {M : CBTM} {input : List F4} {cfg₀ cfg : CBTMConfig M input}
    {π : ComputationPath} (h : TapeSteps M input cfg₀ π cfg) (hπ : π = []) : cfg = cfg₀ := by
  have h' : π = [] → cfg = cfg₀ := by
    induction h with
    | nil => intro _; rfl
    | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
        intro h
        have : π₀.length + 1 = 0 := by simpa using congrArg List.length h
        omega
  exact h' hπ

/-- 101 态（reg=0，phase≥9）的移动方向恒 ∈ {S, R}：陷阱链的带头单调不减。 -/
lemma state101_zero_moveDir (ph : ℕ) (hph9 : 9 ≤ ph) (hph : ph < 12) (s : F4)
    (r : CBTMTransResult) (hr : r ∈ transition4 (encodeState 101 ph 0) s) :
    r.moveDir = Dir.S ∨ r.moveDir = Dir.R := by
  dsimp [transition4] at hr
  rw [decodeState_encodeState 101 ph 0 (by omega) (by norm_num)] at hr
  have h1 : ¬ ph < 3 := by omega
  have h2 : ph ≠ 3 := by omega
  have h3 : ¬ ph < 8 := by omega
  by_cases h11 : ph = 11
  · subst ph
    by_cases him : F4.im s
    · simp [h1, h2, h3, him] at hr
      rcases hr with hr | hr
      · right
        rw [hr]
        dsimp [decodeResult]
        rfl
      · left
        rw [hr]
    · simp [h1, h2, h3, him] at hr
      -- q=101 陷阱吸收：im=false 的移动阶段单结果 moveDir = S（transition4 的 q101 分支）
      left
      rw [hr]
  · have h12 : ph < 12 := by omega
    by_cases him : F4.im s
    · simp [h1, h2, h3, h11, h12, him] at hr
      rcases hr with hr | hr
      · right
        rw [hr]
        dsimp [decodeResult]
        rfl
      · left
        rw [hr]
    · simp [h1, h2, h3, h11, h12, him] at hr
      left
      rw [hr]

lemma decodeResult_encodeResult_ok (r : SymTransResult)
    (hmk : r.writeSym.2 = true → r.writeSym.1 = SymKind.data0 ∨ r.writeSym.1 = SymKind.data1 ∨
      r.writeSym.1 = SymKind.alpha ∨ r.writeSym.1 = SymKind.consumed ∨ r.writeSym.1 = SymKind.boundary ∨
      r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨ r.writeSym.1 = SymKind.beta) :
    decodeResult (encodeResult r) = r := by
  rcases r with ⟨n, w, d⟩
  rcases w with ⟨k, mk⟩
  have hsk : skOf k + (if mk then 9 else 0) < 18 := by
    cases k <;> cases mk <;> simp [skOf]
  have hdir : dirOf d < 3 := by
    cases d <;> simp [dirOf]
  have hq : (encodeResult ⟨n, (k, mk), d⟩) / 54 = n := by
    change (n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) / 54 = n
    omega
  have hsk2 : ((encodeResult ⟨n, (k, mk), d⟩) / 3) % 18 = skOf k + (if mk then 9 else 0) := by
    change ((n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) / 3) % 18 =
      skOf k + (if mk then 9 else 0)
    omega
  have hdir2 : (encodeResult ⟨n, (k, mk), d⟩) % 3 = dirOf d := by
    change (n * 54 + (skOf k + (if mk then 9 else 0)) * 3 + dirOf d) % 3 = dirOf d
    omega
  cases mk with
  | false =>
      cases k <;> cases d
      all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data0, Sym.data1,
        Sym.consumed, Sym.boundary, Sym.sel, Sym.nosel, Sym.alpha, Sym.beta, Sym.mk]
  | true =>
      cases k <;> cases d
      all_goals simp [decodeResult, hq, hsk2, hdir2, skOf, dirOf, Sym.data0, Sym.data1,
        Sym.consumed, Sym.boundary, Sym.sel, Sym.nosel, Sym.alpha, Sym.beta, Sym.mk]

/-- 陷阱态 (101, 10, 0) 读 zero 的强制结果（q101 吸收：写回原符号、moveDir = S）。 -/
lemma trap_step10_forced (r : CBTMTransResult)
    (hr : r ∈ transition4 (encodeState 101 10 0) F4.zero) :
    r = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
  dsimp [transition4] at hr
  rw [decodeState_encodeState 101 10 0 (by norm_num) (by norm_num)] at hr
  simp [F4.zero, decodeResult] at hr
  simpa [F4.zero] using hr

/-- 陷阱态 (101, 11, 0) 读 zero 的强制结果（q101 吸收：不重启到 0，保持 101）。 -/
lemma trap_step11_forced (r : CBTMTransResult)
    (hr : r ∈ transition4 (encodeState 101 11 0) F4.zero) :
    r = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
  dsimp [transition4] at hr
  rw [decodeState_encodeState 101 11 0 (by norm_num) (by norm_num)] at hr
  simp [F4.zero, decodeResult] at hr
  simpa [F4.zero] using hr

/-- 不同 Sym 格（i ≠ p，j,k < 4）的 F4 格位置不相交。 -/
lemma cell_ne_of_ne_pos (i p : ℤ) (j k : ℕ) (hj : j < 4) (hk : k < 4) (hip : i ≠ p) :
    4 * i + (j : ℤ) ≠ 4 * p + (k : ℤ) := by
  intro h
  interval_cases j <;> interval_cases k <;> first | done | omega

/-- 不同 Sym 格（i ∉ {p-1, p}，j < 4）与左移写回位置 4p-k（1 ≤ k ≤ 3）不相交。 -/
lemma cell_ne_of_ne_pos_back (i p : ℤ) (j k : ℕ) (hj : j < 4) (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hip : i ≠ p) (hip1 : i ≠ p - 1) :
    4 * i + (j : ℤ) ≠ 4 * p - (k : ℤ) := by
  intro h
  interval_cases j <;> interval_cases k <;> omega

/-- 好块 + 首块对应 ⟹ 末块对应（块内 12 步的逐步唯一性 + 末格局组装）。 -/
theorem project_block (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w) (π : ComputationPath)
    (cfgc' : CBTMConfig subsetSumCBTM w) (cfgs : SymConfig) (p : ℤ)
    (q : ℕ) (sym : Sym) (r : SymTransResult)
    (hblock : GoodBlock w cfgc π cfgc' cfgs p q sym r) (hrs : r.nextState < 101) :
    blockCorrespond cfgc' (symStepConfig cfgs r) := by
  rcases hblock with ⟨hpath, hlen, hst, hp, hcorr, hread, hq, hbranch, hvalid_sym, hstep4, hmk, hr, hst', hhead'⟩
  -- 本地 let（与 expand_sym_step 内部一致）
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
  -- 1. 拆出 12 步
  rcases tapeSteps_split_last hpath (by intro h; simp [h] at hlen) with
    ⟨step11, π10, cfg11, hπe11, h10, hf11, hr11, ht11, hc11⟩
  rcases tapeSteps_split_last h10 (by
      intro h
      have : (π10 ++ [step11]).length = 12 := by simpa [hπe11] using hlen
      simp [h] at this) with
    ⟨step10, π9, cfg10, hπe10, h9, hf10, hr10, ht10, hc10⟩
  rcases tapeSteps_split_last h9 (by
      intro h
      have : (π9 ++ [step10, step11]).length = 12 := by simpa [hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step9, π8, cfg9, hπe9, h8, hf9, hr9, ht9, hc9⟩
  rcases tapeSteps_split_last h8 (by
      intro h
      have : (π8 ++ [step9, step10, step11]).length = 12 := by simpa [hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step8, π7, cfg8, hπe8, h7, hf8, hr8, ht8, hc8⟩
  rcases tapeSteps_split_last h7 (by
      intro h
      have : (π7 ++ [step8, step9, step10, step11]).length = 12 := by simpa [hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step7, π6, cfg7, hπe7, h6, hf7, hr7, ht7, hc7⟩
  rcases tapeSteps_split_last h6 (by
      intro h
      have : (π6 ++ [step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step6, π5, cfg6, hπe6, h5, hf6, hr6, ht6, hc6⟩
  rcases tapeSteps_split_last h5 (by
      intro h
      have : (π5 ++ [step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step5, π4, cfg5, hπe5, h4, hf5, hr5, ht5, hc5⟩
  rcases tapeSteps_split_last h4 (by
      intro h
      have : (π4 ++ [step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step4, π3, cfg4, hπe4, h3, hf4, hr4, ht4, hc4⟩
  rcases tapeSteps_split_last h3 (by
      intro h
      have : (π3 ++ [step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step3, π2, cfg3, hπe3, h2, hf3, hr3, ht3, hc3⟩
  rcases tapeSteps_split_last h2 (by
      intro h
      have : (π2 ++ [step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step2, π1, cfg2, hπe2, h1, hf2, hr2, ht2, hc2⟩
  rcases tapeSteps_split_last h1 (by
      intro h
      have : (π1 ++ [step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
    ⟨step1, π0, cfg1, hπe1, h0, hf1, hr1, ht1, hc1⟩
  rcases tapeSteps_split_last h0 (by
      intro h
      have : (π0 ++ [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]).length = 12 := by simpa [hπe1, hπe2, hπe3, hπe4, hπe5, hπe6, hπe7, hπe8, hπe9, hπe10, hπe11] using hlen
      simp [h] at this) with
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
  -- 3. 逐步强制
  -- 读出前 4 格的取值
  have hc0v : cfgc.tapeAt (4 * p) = c0 := by
    have hc := hcorr.2.2 p 0 (by norm_num)
    simpa [hread, c0, cells] using hc
  have hc1v : cfgc.tapeAt (4 * p + 1) = c1 := by
    have hc := hcorr.2.2 p 1 (by norm_num)
    simpa [hread, c1, cells] using hc
  have hc2v : cfgc.tapeAt (4 * p + 2) = c2 := by
    have hc := hcorr.2.2 p 2 (by norm_num)
    simpa [hread, c2, cells] using hc
  have hc3v : cfgc.tapeAt (4 * p + 3) = c3 := by
    have hc := hcorr.2.2 p 3 (by norm_num)
    simpa [hread, c3, cells] using hc
  have him0 : F4.im c0 = false := by simpa [c0, cells] using (symTo4F4_im_false_012 sym).1
  have him1 : F4.im c1 = false := by simpa [c1, cells] using (symTo4F4_im_false_012 sym).2.1
  have him2 : F4.im c2 = false := by simpa [c2, cells] using (symTo4F4_im_false_012 sym).2.2
  have hw0 : F4.im w0 = false := by simpa [w0, nrs] using (symTo4F4_im_false_012 r.writeSym).1
  have hw1 : F4.im w1 = false := by simpa [w1, nrs] using (symTo4F4_im_false_012 r.writeSym).2.1
  have hw2 : F4.im w2 = false := by simpa [w2, nrs] using (symTo4F4_im_false_012 r.writeSym).2.2
  have hqle : q ≤ 101 := hq
  have hns : r.nextState ≤ 101 := transition_nextState_le101 q sym hqle r hr
  have hqnn : min qn 101 = qn := by
    dsimp [qn]
    rw [Nat.min_eq_left]
    exact Nat.min_le_right _ _
  -- v2：接受路径上无 101 步（hrs）→ qn = min r.nextState 101 ≠ 101，
  -- 排除 transition4 移动阶段的 q=101 陷阱吸收分支（ad97191 引入）。
  have hqne : qn ≠ 101 := by
    dsimp [qn]
    rw [Nat.min_eq_left (le_of_lt hrs)]
    exact ne_of_lt hrs
  have hregr : regr < 8192 := by
    dsimp [regr, encodeResult]
    have hsk : skOf r.writeSym.1 + (if r.writeSym.2 then 9 else 0) < 18 := by
      rcases r.writeSym with ⟨k, mk⟩
      cases k <;> cases mk <;> simp [skOf]
    have hdir : dirOf r.moveDir < 3 := by
      cases r.moveDir <;> simp [dirOf]
    omega
  have hdec1' : decodeState (encodeState (min q 101) 1 b01) = (min q 101, 1, b01) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b01 ≤ 63 := by
        dsimp [b01, bufOf3]
        rcases c0 with ⟨r0, i0⟩
        cases r0 <;> cases i0 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec2' : decodeState (encodeState (min q 101) 2 b12) = (min q 101, 2, b12) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b12 ≤ 63 := by
        dsimp [b12, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec3' : decodeState (encodeState (min q 101) 3 b3) = (min q 101, 3, b3) := by
    apply decodeState_encodeState
    · norm_num
    · have hb : b3 ≤ 63 := by
        dsimp [b3, bufOf3]
        rcases c0 with ⟨r0, i0⟩ <;> rcases c1 with ⟨r1, i1⟩ <;> rcases c2 with ⟨r2, i2⟩
        cases r0 <;> cases i0 <;> cases r1 <;> cases i1 <;> cases r2 <;> cases i2 <;>
          simp [F4.zero, F4.one, F4.alpha, F4.beta]
      exact lt_of_le_of_lt hb (by norm_num)
  have hdec4' : decodeState (encodeState r.nextState 4 regr) = (r.nextState, 4, regr) := by
    apply decodeState_encodeState
    · norm_num
    · simpa [regBound] using hregr
  have hdecph (ph : ℕ) (hphl : ph < 12) :
      decodeState (encodeState qn ph regr) = (qn, ph, regr) := by
    apply decodeState_encodeState
    · simpa [stepsPerSym] using hphl
    · simpa [regBound] using hregr
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
  have hst0 : step0.fromState = encodeState q 0 0 := by simpa [hst] using hf0
  have hrd0 : step0.readSym = c0 := by
    simpa [hc0v, hp, c0] using hr0
  have hmem0 : step0.result ∈ transition4 (encodeState q 0 0) c0 := by
    have ht0' : step0.result ∈ subsetSumCBTM.transition (cfgc.state, cfgc.tapeAt cfgc.headPos, cfgc.headPos) := ht0
    rw [hst, hp, hc0v] at ht0'
    simpa [subsetSumCBTM] using ht0'
  have hres0 : step0.result = CBTMTransResult.mk (encodeState (min q 101) 1 b01) c0 Dir.R := by
    dsimp [transition4] at hmem0
    rw [decodeState_encodeState q 0 0 (by norm_num) (by norm_num)] at hmem0
    simp [him0] at hmem0
    simpa [hb01] using hmem0
  have hp1 : cfg1.headPos = 4 * p + 1 := by
    rw [hc0]
    dsimp [stepConfig]
    rw [hres0]
    dsimp
    rw [hp]
    simp [Dir.toInt]
  -- 第 1 步：读 c1
  have hst1 : step1.fromState = encodeState (min q 101) 1 b01 := by
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
  have hmem1 : step1.result ∈ transition4 (encodeState (min q 101) 1 b01) c1 := by
    have ht1' : step1.result ∈ subsetSumCBTM.transition (cfg1.state, cfg1.tapeAt cfg1.headPos, cfg1.headPos) := ht1
    rw [show cfg1.state = encodeState (min q 101) 1 b01 from by simpa [hf1] using hst1] at ht1'
    rw [hp1] at ht1'
    rw [show cfg1.tapeAt (4 * p + 1) = c1 from by simpa [hr1, hp1] using hrd1] at ht1'
    simpa [subsetSumCBTM] using ht1'
  have hres1 : step1.result = CBTMTransResult.mk (encodeState (min q 101) 2 (b01 + bufOf3s 1 c1 b01)) c1 Dir.R := by
    dsimp [transition4] at hmem1
    rw [hdec1'] at hmem1
    simp [him1] at hmem1
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
  have hst2 : step2.fromState = encodeState (min q 101) 2 b12 := by
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
  have hmem2 : step2.result ∈ transition4 (encodeState (min q 101) 2 b12) c2 := by
    have ht2' : step2.result ∈ subsetSumCBTM.transition (cfg2.state, cfg2.tapeAt cfg2.headPos, cfg2.headPos) := ht2
    rw [show cfg2.state = encodeState (min q 101) 2 b12 from by simpa [hf2] using hst2] at ht2'
    rw [hp2] at ht2'
    rw [show cfg2.tapeAt (4 * p + 2) = c2 from by simpa [hr2, hp2] using hrd2] at ht2'
    simpa [subsetSumCBTM] using ht2'
  have hres2 : step2.result = CBTMTransResult.mk (encodeState (min q 101) 3 (b12 + bufOf3s 2 c2 b12)) c2 Dir.R := by
    dsimp [transition4] at hmem2
    rw [hdec2'] at hmem2
    simp [him2] at hmem2
    simpa using hmem2
  have hp3 : cfg3.headPos = 4 * p + 3 := by
    rw [hc2]
    dsimp [stepConfig]
    rw [hres2]
    dsimp
    rw [hp2]
    simp [Dir.toInt]
    omega
  -- 第 3 步（合成步）：hstep4 直接钉死
  have hst3 : step3.fromState = encodeState (min q 101) 3 b3 := by
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
  have hstep3' : step3.result = CBTMTransResult.mk (encodeState r.nextState 4 regr) ((symTo4F4 r.writeSym).getLastD F4.zero) Dir.L := by
    have hπ' : π = [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11] := by
      rw [hπe11, hπe10, hπe9, hπe8, hπe7, hπe6, hπe5, hπe4, hπe3, hπe2, hπe1, hπen]
      rfl
    have hg : π.get ⟨3, by omega⟩ = step3 := by
      simpa [hπ']
    rw [hg] at hstep4
    simpa [regr] using hstep4
  have hp4 : cfg4.headPos = 4 * p + 2 := by
    rw [hc3]
    dsimp [stepConfig]
    rw [hstep3']
    dsimp
    rw [hp3]
    simp [Dir.toInt]
    omega
  -- 第 4 步：写回阶段 phase 4 —— 读 c2（im=false）写 w2 移 L
  have hst4 : step4.fromState = encodeState r.nextState 4 regr := by
    have hst4' : step4.fromState = cfg4.state := by simpa using hf4
    rw [hst4']
    rw [hc3]
    dsimp [stepConfig]
    rw [hstep3']
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
    rw [hstep3']
    dsimp [w3, nrs]
    rw [← symTo4F4_getD3_eq_lastD r.writeSym]
  -- 第 9-11 步：移动阶段——按 d = R / L / S 分情况（陷阱支用 hhead' 排除）
  rcases hd : r.moveDir with _ | _ | _
  · -- d = L：读前一格（im 未知），陷阱支经 trap_step10/11_forced 链排除
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
    -- 陷阱支 9：trap_step10_forced 续 → step11 读 w0 强制 R → 带头 4p+1 ≠ 4p-4
    have hnotrap9 : step9.result ≠ CBTMTransResult.mk (encodeState 101 10 0) F4.zero Dir.S := by
      intro htr9
      have hp10t : cfg10.headPos = 4 * p + -1 := by
        rw [hc9]
        dsimp [stepConfig]
        rw [htr9]
        dsimp
        rw [hp9]
        dsimp [d]
        simp [hd, Dir.toInt]
        first | done | omega
      have hrd10t : step10.readSym = F4.zero := by
        have hrd10' : step10.readSym = cfg10.tapeAt cfg10.headPos := by simpa using hr10
        rw [hrd10', hp10t]
        rw [hc9]
        rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p + -1) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt])]
        rw [htr9]
      have hmem10t : step10.result ∈ transition4 (encodeState 101 10 0) F4.zero := by
        have ht10' : step10.result ∈ subsetSumCBTM.transition (cfg10.state, cfg10.tapeAt cfg10.headPos, cfg10.headPos) := ht10
        rw [show cfg10.state = encodeState 101 10 0 from by simpa [stepConfig, hc9, htr9]] at ht10'
        rw [hp10t] at ht10'
        rw [show cfg10.tapeAt (4 * p + -1) = F4.zero from by simpa [hr10, hp10t] using hrd10t] at ht10'
        simpa [subsetSumCBTM] using ht10'
      have hres10t : step10.result = CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S :=
        trap_step10_forced step10.result hmem10t
      have hp11t : cfg11.headPos = 4 * p + -1 := by
        rw [hc10]
        dsimp [stepConfig]
        rw [hres10t]
        dsimp
        rw [hc9]
        dsimp [stepConfig]
        rw [htr9]
        dsimp
        rw [hp9]
        dsimp [d]
        simp [hd, Dir.toInt]
        first | done | omega
      have hrd11t : step11.readSym = F4.zero := by
        have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
        rw [hrd11', hp11t]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + -1) (by rw [hp10t])]
        rw [hres10t]
      have hmem11t : step11.result ∈ transition4 (encodeState 101 11 0) F4.zero := by
        have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
        rw [show cfg11.state = encodeState 101 11 0 from by simpa [stepConfig, hc10, hres10t]] at ht11'
        rw [hp11t] at ht11'
        rw [show cfg11.tapeAt (4 * p + -1) = F4.zero from by simpa [hr11, hp11t] using hrd11t] at ht11'
        simpa [subsetSumCBTM] using ht11'
      have hres11t : step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S :=
        trap_step11_forced step11.result hmem11t
      have hhead_trap : cfgc'.headPos = 4 * p + -1 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [hres11t]
        dsimp
        rw [hp11t]
        simp [Dir.toInt]
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
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
    have hres9 : step9.result = CBTMTransResult.mk (encodeState qn 10 regr) s9 Dir.L := by
      rcases hres9' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap9 htrap
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
    -- 陷阱支 10：trap_step11_forced → 带头 4p-1 ≠ 4p-4
    have hnotrap10 : step10.result ≠ CBTMTransResult.mk (encodeState 101 11 0) F4.zero Dir.S := by
      intro htr10
      have hp11t : cfg11.headPos = 4 * p + -2 := by
        rw [hc10]
        dsimp [stepConfig]
        rw [htr10]
        dsimp
        rw [hp10]
        simp [Dir.toInt]
        first | done | omega
      have hrd11t : step11.readSym = F4.zero := by
        have hrd11' : step11.readSym = cfg11.tapeAt cfg11.headPos := by simpa using hr11
        rw [hrd11', hp11t]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + -2) (by rw [hp10])]
        rw [htr10]
      have hmem11t : step11.result ∈ transition4 (encodeState 101 11 0) F4.zero := by
        have ht11' : step11.result ∈ subsetSumCBTM.transition (cfg11.state, cfg11.tapeAt cfg11.headPos, cfg11.headPos) := ht11
        rw [show cfg11.state = encodeState 101 11 0 from by simpa [stepConfig, hc10, htr10]] at ht11'
        rw [hp11t] at ht11'
        rw [show cfg11.tapeAt (4 * p + -2) = F4.zero from by simpa [hr11, hp11t] using hrd11t] at ht11'
        simpa [subsetSumCBTM] using ht11'
      have hres11t : step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S :=
        trap_step11_forced step11.result hmem11t
      have hhead_trap : cfgc'.headPos = 4 * p + -2 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [hres11t]
        dsimp
        rw [hp11t]
        simp [Dir.toInt]
        first | done | omega
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
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
    have hres10 : step10.result = CBTMTransResult.mk (encodeState qn 11 regr) s10 Dir.L := by
      rcases hres10' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap10 htrap
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
    -- 陷阱支 11：带头停 4p-3 ≠ 4p-4
    have hnotrap11 : step11.result ≠ CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      intro htr11
      have hhead_trap : cfgc'.headPos = 4 * p + -3 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [htr11]
        dsimp
        rw [hp11]
        simp [Dir.toInt]
        first | done | omega
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
    have hres11' : step11.result = CBTMTransResult.mk (encodeState qn 0 0) s11 Dir.L ∨
        step11.result = CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      dsimp [transition4] at hmem11
      rw [hdecph 11 (by norm_num)] at hmem11
      rw [decodeResult_encodeResult_ok r hmk] at hmem11
      by_cases him11 : F4.im s11 <;> simp [him11, hqne] at hmem11
      · simpa [qn, hd] using hmem11
      · left
        simpa [qn, hd] using hmem11
    have hres11 : step11.result = CBTMTransResult.mk (encodeState qn 0 0) s11 Dir.L := by
      rcases hres11' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap11 htrap
    -- 末格局组装
    have hhead_sym : cfgs.headPos = p := by
      have hh := hcorr.2.1
      rw [hp] at hh
      omega
    refine ⟨?_, ?_, ?_⟩
    · simpa [symStepConfig] using hst'
    · rw [symStepConfig, hhead_sym, hhead', Int.mul_add]
    · intro i j hj
      dsimp [symStepConfig]
      by_cases hi : i = p
      · subst i
        simp [hhead_sym]
        interval_cases j
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_eq cfg8 step8.result (4 * p) (by rw [hp8])]
          rw [hres8]
          simp [w0, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 1) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 1) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 1) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 1) (by rw [hp8]; omega)]
          rw [hc8'1]
          simp [w1, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 2) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 2) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 2) (by rw [hp8]; omega)]
          rw [hc8'2]
          simp [w2, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 3) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 3) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 3) (by rw [hp8]; omega)]
          rw [hc8'3]
          simp [w3, nrs]
      · simp [hhead_sym, hi]
        by_cases hip1 : i = p - 1
        · -- i = p-1：第 9-11 步的写回保持原值（s9/s10/s11 = tprev 格）
          subst i
          interval_cases j
          · norm_num
            rw [hc11]
            rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * (p - 1)) (by rw [hp11]; omega)]
            rw [hc10]
            rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * (p - 1)) (by rw [hp10]; omega)]
            rw [hc9]
            rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * (p - 1)) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
            rw [hc8]
            rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * (p - 1)) (by rw [hp8]; omega)]
            rw [hc7]
            rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * (p - 1)) (by rw [hp7]; omega)]
            rw [hc6]
            rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * (p - 1)) (by rw [hp6]; omega)]
            rw [hc5]
            rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * (p - 1)) (by rw [hp5]; omega)]
            rw [hc4]
            rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * (p - 1)) (by rw [hp4]; omega)]
            rw [hc3]
            rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * (p - 1)) (by rw [hp3]; omega)]
            rw [hc2]
            rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * (p - 1)) (by rw [hp2]; omega)]
            rw [hc1]
            rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * (p - 1)) (by rw [hp1]; omega)]
            rw [hc0]
            rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * (p - 1)) (by rw [hp]; omega)]
            rw [show 4 * (p - 1) = 4 * (p - 1) + (0 : ℕ) by omega]
            rw [hcorr.2.2 (p - 1) 0 (by norm_num)]
            simp
          · norm_num
            rw [hc11]
            rw [stepConfig_tapeAt_eq_of_eq cfg11 step11.result (4 * (p - 1) + 1) (by rw [hp11]; omega)]
            rw [hres11]
            dsimp [s11, d, tprev]
            simp [hd]
          · norm_num
            rw [hc11]
            rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * (p - 1) + 2) (by rw [hp11]; omega)]
            rw [hc10]
            rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * (p - 1) + 2) (by rw [hp10]; omega)]
            rw [hres10]
            dsimp [s10, d, tprev]
            simp [hd]
          · norm_num
            rw [hc11]
            rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * (p - 1) + 3) (by rw [hp11]; omega)]
            rw [hc10]
            rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * (p - 1) + 3) (by rw [hp10]; omega)]
            rw [hc9]
            rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * (p - 1) + 3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; omega)]
            rw [hres9]
            dsimp [s9, d, tprev]
            simp [hd]
        · -- i ∉ {p-1, p}：12 步全不相交
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * i + (j : ℤ)) (by rw [hp11]; exact cell_ne_of_ne_pos_back i p j 3 hj (by norm_num) (by norm_num) hi hip1)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * i + (j : ℤ)) (by rw [hp10]; exact cell_ne_of_ne_pos_back i p j 2 hj (by norm_num) (by norm_num) hi hip1)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * i + (j : ℤ)) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; exact cell_ne_of_ne_pos_back i p j 1 hj (by norm_num) (by norm_num) hi hip1)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * i + (j : ℤ)) (by rw [hp8]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
          rw [hc7]
          rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * i + (j : ℤ)) (by rw [hp7]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
          rw [hc6]
          rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * i + (j : ℤ)) (by rw [hp6]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
          rw [hc5]
          rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * i + (j : ℤ)) (by rw [hp5]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
          rw [hc4]
          rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * i + (j : ℤ)) (by rw [hp4]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
          rw [hc3]
          rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * i + (j : ℤ)) (by rw [hp3]; exact cell_ne_of_ne_pos i p j 3 hj (by norm_num) hi)]
          rw [hc2]
          rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * i + (j : ℤ)) (by rw [hp2]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
          rw [hc1]
          rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * i + (j : ℤ)) (by rw [hp1]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
          rw [hc0]
          rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * i + (j : ℤ)) (by rw [hp]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
          simpa [List.getD] using (hcorr.2.2 i j hj)
  · -- d = R：读 w1 / w2 / w3（w1、w2 im 恒 false；w3 的 im = 标记位，双结果时排除陷阱支）
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
    -- 陷阱支（im w3 = true 时出现）带头发散于 hhead'，先行排除
    have hnotrap11 : step11.result ≠ CBTMTransResult.mk (encodeState 101 0 0) F4.zero Dir.S := by
      intro htr11
      have hhead_trap : cfgc'.headPos = 4 * p + 3 := by
        rw [hc11]
        dsimp [stepConfig]
        rw [htr11]
        dsimp
        rw [hp11]
        simp [Dir.toInt]
      rw [hhead_trap] at hhead'
      simp [hd, Dir.toInt] at hhead'
      first | done | omega
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
      rcases hres11' with hg | htrap
      · exact hg
      · exfalso
        exact hnotrap11 htrap
    -- 末格局组装
    have hhead_sym : cfgs.headPos = p := by
      have hh := hcorr.2.1
      rw [hp] at hh
      omega
    refine ⟨?_, ?_, ?_⟩
    · simpa [symStepConfig] using hst'
    · rw [symStepConfig, hhead_sym, hhead', Int.mul_add]
    · intro i j hj
      dsimp [symStepConfig]
      by_cases hi : i = p
      · subst i
        simp [hhead_sym]
        interval_cases j
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_eq cfg8 step8.result (4 * p) (by rw [hp8])]
          rw [hres8]
          simp [w0, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 1) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 1) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_eq cfg9 step9.result (4 * p + 1) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt])]
          rw [hres9]
          simp [w1, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 2) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_eq cfg10 step10.result (4 * p + 2) (by rw [hp10])]
          rw [hres10]
          simp [w2, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_eq cfg11 step11.result (4 * p + 3) (by rw [hp11])]
          rw [hres11]
          simp [w3, nrs]
      · simp [hhead_sym, hi]
        rw [hc11]
        rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * i + (j : ℤ)) (by rw [hp11]; exact cell_ne_of_ne_pos i p j 3 hj (by norm_num) hi)]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * i + (j : ℤ)) (by rw [hp10]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
        rw [hc9]
        rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * i + (j : ℤ)) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
        rw [hc8]
        rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * i + (j : ℤ)) (by rw [hp8]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc7]
        rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * i + (j : ℤ)) (by rw [hp7]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc6]
        rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * i + (j : ℤ)) (by rw [hp6]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc5]
        rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * i + (j : ℤ)) (by rw [hp5]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
        rw [hc4]
        rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * i + (j : ℤ)) (by rw [hp4]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
        rw [hc3]
        rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * i + (j : ℤ)) (by rw [hp3]; exact cell_ne_of_ne_pos i p j 3 hj (by norm_num) hi)]
        rw [hc2]
        rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * i + (j : ℤ)) (by rw [hp2]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
        rw [hc1]
        rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * i + (j : ℤ)) (by rw [hp1]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
        rw [hc0]
        rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * i + (j : ℤ)) (by rw [hp]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        simpa [List.getD] using (hcorr.2.2 i j hj)
  · -- d = S：读 w0（im=false），全强制
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
    -- 末格局组装
    have hhead_sym : cfgs.headPos = p := by
      have hh := hcorr.2.1
      rw [hp] at hh
      omega
    refine ⟨?_, ?_, ?_⟩
    · simpa [symStepConfig] using hst'
    · rw [symStepConfig, hhead_sym, hhead', Int.mul_add]
    · intro i j hj
      dsimp [symStepConfig]
      by_cases hi : i = p
      · subst i
        simp [hhead_sym]
        interval_cases j
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_eq cfg11 step11.result (4 * p) (by rw [hp11])]
          rw [hres11]
          simp [w0, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 1) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 1) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 1) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 1) (by rw [hp8]; omega)]
          rw [hc8'1]
          simp [w1, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 2) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 2) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 2) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 2) (by rw [hp8]; omega)]
          rw [hc8'2]
          simp [w2, nrs]
        · norm_num
          rw [hc11]
          rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * p + 3) (by rw [hp11]; omega)]
          rw [hc10]
          rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * p + 3) (by rw [hp10]; omega)]
          rw [hc9]
          rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * p + 3) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; first | done | omega)]
          rw [hc8]
          rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * p + 3) (by rw [hp8]; omega)]
          rw [hc8'3]
          simp [w3, nrs]
      · simp [hhead_sym, hi]
        rw [hc11]
        rw [stepConfig_tapeAt_eq_of_ne cfg11 step11.result (4 * i + (j : ℤ)) (by rw [hp11]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc10]
        rw [stepConfig_tapeAt_eq_of_ne cfg10 step10.result (4 * i + (j : ℤ)) (by rw [hp10]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc9]
        rw [stepConfig_tapeAt_eq_of_ne cfg9 step9.result (4 * i + (j : ℤ)) (by rw [hp9]; dsimp [d]; simp [hd, Dir.toInt]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc8]
        rw [stepConfig_tapeAt_eq_of_ne cfg8 step8.result (4 * i + (j : ℤ)) (by rw [hp8]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc7]
        rw [stepConfig_tapeAt_eq_of_ne cfg7 step7.result (4 * i + (j : ℤ)) (by rw [hp7]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc6]
        rw [stepConfig_tapeAt_eq_of_ne cfg6 step6.result (4 * i + (j : ℤ)) (by rw [hp6]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        rw [hc5]
        rw [stepConfig_tapeAt_eq_of_ne cfg5 step5.result (4 * i + (j : ℤ)) (by rw [hp5]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
        rw [hc4]
        rw [stepConfig_tapeAt_eq_of_ne cfg4 step4.result (4 * i + (j : ℤ)) (by rw [hp4]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
        rw [hc3]
        rw [stepConfig_tapeAt_eq_of_ne cfg3 step3.result (4 * i + (j : ℤ)) (by rw [hp3]; exact cell_ne_of_ne_pos i p j 3 hj (by norm_num) hi)]
        rw [hc2]
        rw [stepConfig_tapeAt_eq_of_ne cfg2 step2.result (4 * i + (j : ℤ)) (by rw [hp2]; exact cell_ne_of_ne_pos i p j 2 hj (by norm_num) hi)]
        rw [hc1]
        rw [stepConfig_tapeAt_eq_of_ne cfg1 step1.result (4 * i + (j : ℤ)) (by rw [hp1]; exact cell_ne_of_ne_pos i p j 1 hj (by norm_num) hi)]
        rw [hc0]
        rw [stepConfig_tapeAt_eq_of_ne cfgc step0.result (4 * i + (j : ℤ)) (by rw [hp]; simpa using (cell_ne_of_ne_pos i p j 0 hj (by norm_num) hi))]
        simpa [List.getD] using (hcorr.2.2 i j hj)

/-- symTo4F4 逐格相等 ⟹ 符号相等（编码单射）。 -/
lemma sym_eq_of_symTo4F4_getD_eq (s t : Sym)
    (h : ∀ j : ℕ, j < 4 → (symTo4F4 s).getD j F4.zero = (symTo4F4 t).getD j F4.zero) :
    s = t := by
  rcases s with ⟨ks, ms⟩ <;> rcases t with ⟨kt, mt⟩
  cases ks <;> cases kt <;> cases ms <;> cases mt <;>
    simp only [symTo4F4, Sym.kindBits, F4.zero, F4.re, F4.im] at h ⊢
  all_goals try rfl
  all_goals have h0 := h 0 (by norm_num)
  all_goals have h1 := h 1 (by norm_num)
  all_goals have h2 := h 2 (by norm_num)
  all_goals have h3 := h 3 (by norm_num)
  all_goals simp at h0 h1 h2 h3

/-- 投影（一般起点）：从任意对应起点出发的块路径投影为 SymSteps，
且保持末块对应与长度换算（πs.length * 12 = π.length）。
v2：加 hno101 前提（路径上无 101 陷阱步），以排除 transition4 移动阶段的
q=101 陷阱吸收分支（ad97191 引入）对块内 step8-11 的干扰。 -/
theorem project_path_gen (w : List F4) (cfgc : CBTMConfig subsetSumCBTM w)
    (cfgs : SymConfig) (π : ComputationPath) (cfgc' : CBTMConfig subsetSumCBTM w)
    (hcorr : blockCorrespond cfgc cfgs)
    (hbp : GoodBlockPath w cfgc π cfgc')
    (hno101 : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∃ πs : List SymStep, ∃ cfgs' : SymConfig,
      SymSteps VerifierSym.transition cfgs πs cfgs' ∧
      blockCorrespond cfgc' cfgs' ∧ πs.length * 12 = π.length := by
  induction hbp generalizing cfgs with
  | nil cfgc =>
      refine ⟨[], cfgs, SymSteps.nil, hcorr, rfl⟩
  | cons cfgc cfgm cfgc' πm π cfgsb p q sym r hblock htail ih =>
      have hproj : blockCorrespond cfgm (symStepConfig cfgsb r) := by
        -- 从 hno101 对块第 4 步（index 3，携带 r）的应用推出 r.nextState < 101
        have hrs : r.nextState < 101 := by
          rcases hblock with
            ⟨hpath, hlenm, hst, hp, hcorrB, hread, hq, hbranch, hvalid, hstep4, hmk, hr, hst', hhead'⟩
          have hle : r.nextState ≤ 101 := transition_nextState_le101 q sym hq r hr
          have hne : r.nextState ≠ 101 := by
            intro h101
            -- 块的第 4 步（index 3）在整条路径 πm ++ π 中，
            -- hstep4 给出该步 result 的 nextState = encodeState r.nextState 4 (encodeResult r)
            have hnt := hno101 3 (by
              have hlenm' : πm.length = 12 := hlenm
              simp [List.length_append] at *
              omega)
            -- (πm ++ π).get ⟨3, ...⟩ = πm.get ⟨3, ...⟩（3 < 12 = πm.length）
            have hget : (πm ++ π).get ⟨3, by
                have hlenm' : πm.length = 12 := hlenm
                simp [List.length_append] at *
                omega⟩ = πm.get ⟨3, by omega⟩ := by
              apply List.getElem_append_left
            -- hstep4 的 result 携带 encodeState r.nextState 4 (encodeResult r)
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
            -- hnt 中 decodeState ... .1 ≠ 101，与 r.nextState = 101 矛盾
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
      -- 尾路径 π 上的无 101 前提（从整条路径 hno101 平移下标）
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
        ⟨πs, cfgs', hsteps, hcorr', hlen⟩
      rcases hblock with
        ⟨hpath, hlenm, hst, hp, hcorrB, hread, hq, hbranch, hvalid, hstep4, hmk, hr, hst', hhead'⟩
      -- 起点配置 cfgs 与块内配置 cfgsb 一致（state / head / tape 三分量）
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
      -- 本块的一步：fromState / readSym / result 的合法性
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
      refine ⟨[step] ++ πs, cfgs', ?_, hcorr', ?_⟩
      · exact SymSteps_trans _ _ _ _ _ _ hstep1 hsteps
      · simp only [List.length_append, List.length_cons, List.length_nil]
        nlinarith

/-- 投影（初始起点）：从初始配置出发的好块路径投影为 SymReachablePath。
v2：加 hno101 前提（路径上无 101 陷阱步）。 -/
theorem project_path (input : List Sym) (π : ComputationPath)
    (cfgc' : CBTMConfig subsetSumCBTM (flat4F4 input))
    (hbp : GoodBlockPath (flat4F4 input) (initialConfig subsetSumCBTM (flat4F4 input)) π cfgc')
    (hno101 : ∀ k (hk : k < π.length), (decodeState (π.get ⟨k, hk⟩).result.nextState).1 ≠ 101) :
    ∃ πs : List SymStep, ∃ cfgs' : SymConfig,
      SymReachablePath VerifierSym.transition input πs cfgs' ∧
      blockCorrespond cfgc' cfgs' ∧ πs.length * 12 = π.length := by
  rcases project_path_gen (flat4F4 input) (initialConfig subsetSumCBTM (flat4F4 input))
      (symInitialConfig input) π cfgc' (initialBlockCorrespond input) hbp hno101 with
    ⟨πs, cfgs', hsteps, hcorr', hlen⟩
  refine ⟨πs, cfgs', ?_, hcorr', hlen⟩
  exact (symSteps_initial_iff VerifierSym.transition input πs cfgs').1 hsteps

end SymToF4
end Mp
