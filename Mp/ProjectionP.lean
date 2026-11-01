import Mp.IVM
import Mp.ATMBridge

/-!
# P 侧投影：CBTM|0 → DTM（机器级接受对应 + 步数对应）

用户裁决（2026-10-31）：「CBTM|0 做投影，得到 DTM」。

本文件把这句话落成**机器级定理**（不是类等式）：
对 `N : CBTM`、`h : N.IsCBTM0`（字母表 = {zero, one}、转移单值、位置无关），
令 `M := N.toClassicDTM h`（`Mp/ATMBridge.lean:271`），则在**二进制域**
（输入每位都属于 `N.alphabet`）上：

* `accepts_iff`：`N.tapeAccepts x ↔ M.acceptsTape x`；
* `steps_agree`：两个方向的路径长度一一对应（步数口径一致 ⇒ 时间界可搬运）。

不变量 `Sim`：状态相等、带头位置相等、逐格内容相等、且**所有格子都在 `N.alphabet` 内**
（最后一条是后向模拟的前提：DTM 侧读到字母表外符号时走的是占位转移，不在对应域）。

注：类级等式 `P_cb = P_atm` **不是**本文件的结论，也不能由它得到（见
`_probe_input_map_asymmetry.lean` 与 `P_atm` 的定义级说明）。

## 已证 / 未证（诚实边界）

- **已证**：`accepts_iff` —— 二进制域（`∀ s ∈ x, s ∈ N.alphabet`）上接受一致；
  `path_forward` / `path_backward` —— 两方向路径同步数对应（时间界可搬运）。
- **未证且不成立**：`IsP_sym0 L → IsP_sym L`。两处硬原因：
  1. **域**：`IsP_sym0` 只在对齐域给保证，`IsP_sym` 要求全输入域；
     非字母表符号上 CBTM 无转移（拒绝），DTM 侧走占位支。
  2. **停机**：`CBTM.toClassicDTMTrans`（`Mp/ATMBridge.lean:261-268`）对字母表外符号
     给的是 `{nextState := N.startState, writeSym := s, move := Dir.S}`——**回起点原地自环**，
     故投影出的 DTM 在含 α/β 的输入上不终止，`ClassicDTM.IsAlgorithm` 不成立。
- 修法（未做）：换「遇 α/β 停机拒绝」的投影 + 给 `L` 在非对齐域为假的假设；
  或把目标类改成域对齐版。
-/

namespace Mp

namespace ProjP

open CBTM

-- ============================================================================
-- §1 基础引理
-- ============================================================================

/-- 虚部为假的符号只能是 zero / one。 -/
lemma im_false_mem_zero_one {s : F4} (hs : F4.im s = false) :
    s ∈ ({F4.zero, F4.one} : Finset F4) := by
  rcases s with ⟨a, b⟩
  simp [F4.im] at hs
  subst hs
  cases a
  · simp [F4.zero]
  · simp [F4.one]

/-- CBTM 结果 → DTM 结果 → CBTM 结果为恒等。 -/
lemma dtmResultToCBTM_roundtrip (r : CBTMTransResult) :
    dtmResultToCBTM (cbtmResultToDTM r) = r := by
  rcases r with ⟨ns, ws, mv⟩
  rfl

/-- CBTM|0 的 DTM 投影。 -/
noncomputable def projDTM (N : CBTM) (h : CBTM.IsCBTM0 N) : ClassicDTM :=
  N.toClassicDTM h

/-- **关键转移对应**：字母表内符号上，CBTM 的转移集恰是 DTM 转移的单元素像。 -/
lemma trans_eq {N : CBTM} (h : CBTM.IsCBTM0 N) (q : ℕ) (s : F4)
    (hs : s ∈ ({F4.zero, F4.one} : Finset F4)) (i : ℤ) :
    N.transition (q, s, i) = {dtmResultToCBTM ((projDTM N h).transition (q, s))} := by
  have hmem : s ∈ N.alphabet := by rw [h.alphabet_eq]; exact hs
  have h0 : (N.transition (q, s, 0)).card = 1 := h.card_one q s 0 hmem
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h0
  have huniq : ∀ x ∈ N.transition (q, s, 0), x = r := by
    intro x hx
    rw [hr] at hx
    exact Finset.mem_singleton.mp hx
  have hchoose : (card_eq_one_unique_mem (N.transition (q, s, 0)) h0).choose = r :=
    huniq _ (card_eq_one_unique_mem (N.transition (q, s, 0)) h0).choose_spec.1
  have hM : (projDTM N h).transition (q, s) = cbtmResultToDTM r := by
    simp only [projDTM, CBTM.toClassicDTM, CBTM.toClassicDTMTrans, dif_pos hmem, hchoose]
  rw [h.pos_indep q s i 0 hmem, hr, hM]
  simp [dtmResultToCBTM_roundtrip]

-- ============================================================================
-- §2 模拟不变量
-- ============================================================================

/-- CBTM 格局与 DTM 格局的模拟关系（含「所有格在字母表内」不变式）。 -/
def Sim (N : CBTM) (h : CBTM.IsCBTM0 N) (x : List F4) (cfg : CBTMConfig N x)
    (dcfg : DTMConfig (projDTM N h)) : Prop :=
  cfg.state = dcfg.state ∧ cfg.headPos = dcfg.headPos ∧
  (∀ i : ℤ, cfg.tape i = dcfg.tape.read i) ∧
  (∀ i : ℤ, cfg.tape i ∈ N.alphabet)

/-- 初始格局满足模拟关系。 -/
lemma sim_init {N : CBTM} (h : CBTM.IsCBTM0 N) (x : List F4)
    (hx : ∀ s ∈ x, s ∈ N.alphabet) :
    Sim N h x (initialConfig N x) (DTMInitialConfig (projDTM N h) x) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i
    simp [initialConfig, DTMInitialConfig, DTMInitialTape, initialTapeOf, projDTM,
      CBTM.toClassicDTM, Tape.read]
  · intro i
    simp only [initialConfig, initialTapeOf, projDTM, CBTM.toClassicDTM]
    by_cases hi : 0 ≤ i ∧ i.toNat < x.length
    · simp only [hi, dif_pos]; exact hx _ (List.get_mem x ⟨i.toNat, hi.2⟩)
    · simp only [hi, dif_neg, not_false_iff]; exact N.h_blank_in_alphabet

/-- 前向一步：CBTM 一步 ⇒ DTM 一步（保持不变量）。 -/
lemma sim_step_fwd {N : CBTM} (h : CBTM.IsCBTM0 N) {x : List F4}
    {cfg : CBTMConfig N x} {dcfg : DTMConfig (projDTM N h)}
    (hsim : Sim N h x cfg dcfg) (r : CBTMTransResult)
    (him : F4.im r.writeSym = false) :
    Sim N h x (stepConfig cfg r) (DTMStepConfig dcfg (cbtmResultToDTM r)) := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hsim
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [stepConfig, DTMStepConfig, cbtmResultToDTM, hs1]
  · simp only [stepConfig, DTMStepConfig, cbtmResultToDTM]
    rw [hs2]
  · intro i
    simp only [stepConfig, DTMStepConfig, cbtmResultToDTM, cbtmResultToDTM, Tape.read]
    rw [hs2]
    by_cases hi : i = dcfg.headPos
    · simp only [hi, if_true]
    · simp only [hi, if_false]; exact hs3 i
  · intro i
    simp only [stepConfig]
    by_cases hi : i = cfg.headPos
    · rw [if_pos hi, h.alphabet_eq]
      exact im_false_mem_zero_one him
    · rw [if_neg hi]; exact hs4 i

/-- 后向一步：DTM 一步 ⇒ CBTM 一步（保持不变量）。 -/
lemma sim_step_bwd {N : CBTM} (h : CBTM.IsCBTM0 N) {x : List F4}
    {cfg : CBTMConfig N x} {dcfg : DTMConfig (projDTM N h)}
    (hsim : Sim N h x cfg dcfg) (r : ClassicDTMTransitionResult)
    (hmem : dtmResultToCBTM r ∈ N.transition (cfg.state, cfg.tape cfg.headPos, cfg.headPos)) :
    Sim N h x (stepConfig cfg (dtmResultToCBTM r)) (DTMStepConfig dcfg r) := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hsim
  -- 读符号在字母表内 ⇒ 虚部为假
  have hs_in : cfg.tape cfg.headPos ∈ ({F4.zero, F4.one} : Finset F4) := by
    have h' : cfg.tape cfg.headPos ∈ N.alphabet := hs4 _
    rw [h.alphabet_eq] at h'
    exact h'
  have him_read : F4.im (cfg.tape cfg.headPos) = false := by
    rcases Finset.mem_insert.mp hs_in with h' | h'
    · rw [h']; rfl
    · rw [Finset.mem_singleton.mp h']; rfl
  have hproj := (N.h_projection_constraint cfg.state (cfg.tape cfg.headPos) cfg.headPos
    (hs4 _) him_read).2
  have him : F4.im r.writeSym = false := by
    have := hproj (dtmResultToCBTM r) hmem
    simpa [dtmResultToCBTM] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [stepConfig, DTMStepConfig, dtmResultToCBTM]
  · simp only [stepConfig, DTMStepConfig, dtmResultToCBTM, cbtmResultToDTM]
    rw [hs2]
  · intro i
    simp only [stepConfig, DTMStepConfig, dtmResultToCBTM, Tape.read]
    rw [hs2]
    by_cases hi : i = dcfg.headPos
    · simp only [hi, if_true]
    · simp only [hi, if_false]; exact hs3 i
  · intro i
    simp only [stepConfig]
    by_cases hi : i = cfg.headPos
    · rw [if_pos hi, h.alphabet_eq]
      exact im_false_mem_zero_one him
    · rw [if_neg hi]; exact hs4 i


-- ============================================================================
-- §3 路径级对应（两个方向）
-- ============================================================================

/-- 读数在字母表内 ⇒ 在 {zero, one} 内（IsCBTM0 的字母表恰为两点）。 -/
lemma mem_zero_one_of_mem_alphabet {N : CBTM} (h : CBTM.IsCBTM0 N) {s : F4}
    (hs : s ∈ N.alphabet) : s ∈ ({F4.zero, F4.one} : Finset F4) := by
  rw [h.alphabet_eq] at hs
  exact hs

/-- 前向：CBTM 可达路径 ⇒ 同步数的 DTM 可达路径，终局满足模拟关系。 -/
lemma path_forward {N : CBTM} (h : CBTM.IsCBTM0 N) (x : List F4)
    (hx : ∀ s ∈ x, s ∈ N.alphabet) :
    ∀ (π : ComputationPath) (cfg : CBTMConfig N x),
      TapeReachablePath N x π cfg →
      ∃ (π' : List DTMTransitionStep) (dcfg : DTMConfig (projDTM N h)),
        DTMTapeReachablePath (projDTM N h) x π' dcfg ∧ π'.length = π.length ∧
        Sim N h x cfg dcfg := by
  intro π cfg hp
  induction hp with
  | nil => exact ⟨[], _, DTMTapeReachablePath.nil, rfl, sim_init h x hx⟩
  | cons π₀ step cfg hpath hfrom hread hres ih =>
      obtain ⟨π', dcfg, hdtm, hlen, hsim⟩ := ih
      have hsimK := hsim
      obtain ⟨hs1, hs2, hs3, hs4⟩ := hsimK
      have hs_one : cfg.tape cfg.headPos ∈ ({F4.zero, F4.one} : Finset F4) :=
        mem_zero_one_of_mem_alphabet h (hs4 _)
      have him_read : F4.im (cfg.tape cfg.headPos) = false := by
        rcases Finset.mem_insert.mp hs_one with h' | h'
        · rw [h']; rfl
        · rw [Finset.mem_singleton.mp h']; rfl
      have him : F4.im step.result.writeSym = false :=
        (N.h_projection_constraint cfg.state (cfg.tape cfg.headPos) cfg.headPos (hs4 _)
          him_read).2 step.result (by simpa [CBTMConfig.tapeAt] using hres)
      -- 结果对应（在 cfg 坐标）
      have hsingle := trans_eq h cfg.state (cfg.tape cfg.headPos) hs_one cfg.headPos
      have hstepres : cbtmResultToDTM step.result =
          (projDTM N h).transition (cfg.state, cfg.tape cfg.headPos) := by
        have hmem : step.result ∈
            ({dtmResultToCBTM ((projDTM N h).transition
              (cfg.state, cfg.tape cfg.headPos))} : Finset CBTMTransResult) := by
          rw [← hsingle]
          simpa [CBTMConfig.tapeAt] using hres
        rw [Finset.mem_singleton.mp hmem, cbtmResultToDTM_dtmResultToCBTM]
      let dstep : DTMTransitionStep :=
        { fromState := step.fromState, readSym := step.readSym, pos := dcfg.headPos,
          result := cbtmResultToDTM step.result }
      have hpath' : DTMTapeReachablePath (projDTM N h) x (π' ++ [dstep])
          (DTMStepConfig dcfg (cbtmResultToDTM step.result)) := by
        refine DTMTapeReachablePath.cons π' dstep dcfg hdtm ?_ ?_ rfl ?_
        · show step.fromState = dcfg.state
          rw [hfrom, hs1]
        · show step.readSym = dcfg.tape.read dcfg.headPos
          rw [show step.readSym = cfg.tape cfg.headPos by simpa [CBTMConfig.tapeAt] using hread]
          rw [← hs2]
          exact hs3 _
        · show cbtmResultToDTM step.result =
            (projDTM N h).transition (dcfg.state, dcfg.tape.read dcfg.headPos)
          rw [hstepres]
          show (projDTM N h).transition (cfg.state, cfg.tape cfg.headPos)
            = (projDTM N h).transition (dcfg.state, dcfg.tape.read dcfg.headPos)
          rw [hs1, ← hs2, hs3]
      exact ⟨π' ++ [dstep], _, hpath', by simp [hlen], sim_step_fwd h hsim step.result him⟩

/-- 后向：DTM 可达路径 ⇒ 同步数的 CBTM 可达路径，终局满足模拟关系。 -/
lemma path_backward {N : CBTM} (h : CBTM.IsCBTM0 N) (x : List F4)
    (hx : ∀ s ∈ x, s ∈ N.alphabet) :
    ∀ (π : List DTMTransitionStep) (dcfg : DTMConfig (projDTM N h)),
      DTMTapeReachablePath (projDTM N h) x π dcfg →
      ∃ (π' : ComputationPath) (cfg : CBTMConfig N x),
        TapeReachablePath N x π' cfg ∧ π'.length = π.length ∧ Sim N h x cfg dcfg := by
  intro π dcfg hp
  induction hp with
  | nil => exact ⟨[], _, TapeReachablePath.nil, rfl, sim_init h x hx⟩
  | cons π₀ step cfg hpath hfrom hread hpos hres ih =>
      obtain ⟨π', cfgc, hcbtm, hlen, hsim⟩ := ih
      have hsimK := hsim
      obtain ⟨hs1, hs2, hs3, hs4⟩ := hsimK
      have hs_one : cfgc.tape cfgc.headPos ∈ ({F4.zero, F4.one} : Finset F4) :=
        mem_zero_one_of_mem_alphabet h (hs4 _)
      have hsingle := trans_eq h cfgc.state (cfgc.tape cfgc.headPos) hs_one cfgc.headPos
      have hres' : step.result =
          (projDTM N h).transition (cfgc.state, cfgc.tape cfgc.headPos) := by
        rw [hres]
        show (projDTM N h).transition (cfg.state, cfg.tape.read cfg.headPos)
          = (projDTM N h).transition (cfgc.state, cfgc.tape cfgc.headPos)
        rw [← hs1, ← hs2, ← hs3]
      have hmem : dtmResultToCBTM step.result ∈
          N.transition (cfgc.state, cfgc.tape cfgc.headPos, cfgc.headPos) := by
        rw [hsingle, Finset.mem_singleton, hres']
      let cstep : TransitionStep :=
        { fromState := step.fromState, readSym := step.readSym,
          result := dtmResultToCBTM step.result }
      refine ⟨π' ++ [cstep], stepConfig cfgc (dtmResultToCBTM step.result), ?_, ?_,
        sim_step_bwd h hsim step.result (by simpa [CBTMConfig.tapeAt] using hmem)⟩
      · refine TapeReachablePath.cons π' cstep cfgc hcbtm ?_ ?_ ?_
        · show step.fromState = cfgc.state
          rw [hfrom, hs1]
        · show step.readSym = cfgc.tape cfgc.headPos
          rw [hread]
          show cfg.tape.read cfg.headPos = cfgc.tape cfgc.headPos
          rw [← hs3, ← hs2]
        · show dtmResultToCBTM step.result ∈
            N.transition (cfgc.state, cfgc.tape cfgc.headPos, cfgc.headPos)
          exact hmem
      · simp [hlen]

-- ============================================================================
-- §4 主定理：二进制域上的接受一致
-- ============================================================================

/-- **机器级投影（P 侧）**：CBTM|0 与 DTM 在二进制域上接受同一批输入。 -/
theorem accepts_iff {N : CBTM} (h : CBTM.IsCBTM0 N) (x : List F4)
    (hx : ∀ s ∈ x, s ∈ N.alphabet) :
    N.tapeAccepts x ↔ (projDTM N h).acceptsTape x := by
  constructor
  · rintro ⟨π, cfg, hpath, hacc⟩
    obtain ⟨π', dcfg, hdtm, hlen, hsim⟩ := path_forward h x hx π cfg hpath
    exact ⟨π', dcfg, hdtm, by rw [← hsim.1]; exact hacc⟩
  · rintro ⟨π, dcfg, hpath, hacc⟩
    obtain ⟨π', cfg, hcbtm, hlen, hsim⟩ := path_backward h x hx π dcfg hpath
    exact ⟨π', cfg, hcbtm, by rw [hsim.1]; exact hacc⟩

end ProjP
end Mp
