/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.CBTM

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
# Mp.ATMBasic —— 算法 TM（ATM）与符号输入上的 P/NP 定义

设计要点（用户裁决已落，2026-09-14）：
- **ATM = `ClassicDTM` 的谓词式修改**（不改名）：`ClassicDTM.IsAlgorithm` 承载「能处理输入」的算法性约定；
  不新建机器类。
- **直读层四值**（Spec 约定 20 位对）：`0↔F4.zero(0,0)`、`1↔F4.one(1,0)`、`sep↔F4.alpha(0,1)`、`#↔F4.beta(1,1)`；
  输入字母表恰为这 4 值（`ClassicDTM.alphabet` 已就位）。
- **DTM 侧口径（用户裁决）**：`ClassicDTM.transition : ℕ × F4 → …` 中的 **F4 按 `Bool × Bool` 理解**——
  机器只读一对 bit，**不带虚部语义**（与 CBTM 側的内建虚部语义分层）。
- **CBTM 侧口径（用户裁决）**：`ℕ × F4 × ℤ → Finset CBTMTransResult` 中的 F4 = **bool（数据）＋虚部**；
  **就输入（数据）而言只占 1 个 bit**——虚部不承载输入数据（虚部＝分支语义）。
- **DTM≅CBTM0 同构条件（用户裁决）**：**取 2F4 的实部（数据分量）、且虚部全为 0**，才恰好与 DTM 同构——
  同构发生在「虚部 = 0 层」上（数据子层）；虚部非零处对应分支语义，不在同构域内。
- **多带版（用户裁决 2026-09-14：ATM 与 CBTM 均改多带版描述）**：DTM = 两带（第 1 输入带：数据，sep→0、#→1；第 2 指示带：数据0、分隔与分界1）；
  CBTM = **2F4 编码**（两带各一个 F4 = 位＋虚部；讨论位 = 第 1 带虚部标志）。见 §7。
- **规范输入形**：`# e₁ sep ⋯ sep e_m #`（`IsInputWord`）——参数以 sep 分隔、# 包裹起止，输入自终结。
- **blankSym = F4.alpha**（= sep）；带外亦可写 alpha（无第 5 符号）。
- **时间计量 = 格子移动数**（S 步不计；与 R13 位移口径一致）；输入长度 = 符号数（bit 长 = ×2）。
- **类**：`IsP_sym`（DTM 承载）/ `IsNP_sym`（NTM2 承载）；集合 `P_sym`/`NP_sym`。
-/

namespace Mp

-- ============================================================================
-- §1 直读层记号与规范输入形
-- ============================================================================

/-- 数据位符号（0 或 1 的直读值）。 -/
def IsDataSym (s : F4) : Prop := s = F4.zero ∨ s = F4.one

/-- 分隔符符号 sep（直读值 alpha）。 -/
def IsSepSym (s : F4) : Prop := s = F4.alpha

/-- 边界/输入终止符 #（直读值 beta）。 -/
def IsEndSym (s : F4) : Prop := s = F4.beta

/-- 规范输入形（ATM 输入骨架）：`# e₁ sep ⋯ sep e_m #`；
    元素 = 非空 {0,1} 位串（值规范「无前导 0」为机器自检项，见 ATMBridge 系）。 -/
def IsInputWord (x : List F4) : Prop :=
  ∃ parts : List (List F4),
    (∀ p ∈ parts, p ≠ [] ∧ ∀ s ∈ p, IsDataSym s) ∧
    x = F4.beta :: (List.intercalate [F4.alpha] parts ++ [F4.beta])

-- ============================================================================
-- §2 DTM 运行语义（磁带语义；确定性：步结果由 δ 唯一给出）
-- ============================================================================

/-- DTM 一步记录：起态、读符号、磁头位置、结果（由 δ 唯一确定）。 -/
structure DTMTransitionStep where
  fromState : ℕ
  readSym : F4
  pos : ℤ
  result : ClassicDTMTransitionResult

/-- DTM 初始磁带：输入直铺 [0, n)，空白区 = blankSym 常数。 -/
def DTMInitialTape (M : ClassicDTM) (input : List F4) : ℤ → F4 :=
  fun i => if h : 0 ≤ i ∧ i.toNat < input.length then
      input.get ⟨i.toNat, h.2⟩
    else M.blankSym

/-- DTM 初始配置。 -/
def DTMInitialConfig (M : ClassicDTM) (input : List F4) : DTMConfig M :=
  { state := M.startState,
    tape := { tape := DTMInitialTape M input, default := M.blankSym },
    headPos := 0 }

/-- DTM 一步格局：写 writeSym 到带头位置，移动带头，更新状态。 -/
def DTMStepConfig {M : ClassicDTM} (cfg : DTMConfig M) (r : ClassicDTMTransitionResult) : DTMConfig M :=
  { state := r.nextState,
    tape := { tape := fun i => if i = cfg.headPos then r.writeSym else cfg.tape.read i,
              default := cfg.tape.default },
    headPos := cfg.headPos + r.move.toInt }

/-- DTM 磁带语义的可达路径：每步读 headPos 处的符号；步结果 = δ 唯一值（确定性）。 -/
inductive DTMTapeReachablePath (M : ClassicDTM) (input : List F4) :
    List DTMTransitionStep → DTMConfig M → Prop
  | nil : DTMTapeReachablePath M input [] (DTMInitialConfig M input)
  | cons : ∀ (π₀ : List DTMTransitionStep) (step : DTMTransitionStep) (cfg : DTMConfig M),
      DTMTapeReachablePath M input π₀ cfg →
      step.fromState = cfg.state →
      step.readSym = cfg.tape.read cfg.headPos →
      step.pos = cfg.headPos →
      step.result = M.transition (cfg.state, cfg.tape.read cfg.headPos) →
      DTMTapeReachablePath M input (π₀ ++ [step]) (DTMStepConfig cfg step.result)

/-- DTM 磁带语义的接受：存在一条可达路径，其末端状态在接受态。 -/
def ClassicDTM.acceptsTape (M : ClassicDTM) (x : List F4) : Prop :=
  ∃ (π : List DTMTransitionStep) (cfg : DTMConfig M),
    DTMTapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates

/-- DTM 磁带语义的拒绝。 -/
def ClassicDTM.rejectsTape (M : ClassicDTM) (x : List F4) : Prop :=
  ∃ (π : List DTMTransitionStep) (cfg : DTMConfig M),
    DTMTapeReachablePath M x π cfg ∧ cfg.state ∈ M.rejectStates

-- ============================================================================
-- §3 格子移动数（时间计量；S 步不计）
-- ============================================================================

/-- 该方向是否为移动步（L/R 移动一格；S 不动）。 -/
def isMovingDir : Dir → Bool
  | Dir.S => false
  | _ => true

/-- DTM 路径的格子移动数。 -/
def dtmMoveCount (π : List DTMTransitionStep) : ℕ :=
  (π.filter (fun st => isMovingDir st.result.move)).length

/-- NTM2 路径的格子移动数。 -/
def ntm2MoveCount (π : NTM2ComputationPath) : ℕ :=
  (π.filter (fun st => isMovingDir st.result.2.2)).length

-- ============================================================================
-- §4 多项式时间（格子移动数计；首达判态语义——排除判态自环尾巴）
-- ============================================================================

/-- DTM 的多项式时间：∃ 多项式界 p，任意首达接受路径的格子移动数 ≤ p(输入符号数)。 -/
def ClassicDTM.isPolynomialTime (M : ClassicDTM) : Prop :=
  ∃ p : ℕ → ℕ, IsPolynomialBound p ∧
    ∀ (x : List F4) (π : List DTMTransitionStep) (cfg : DTMConfig M),
      DTMTapeReachablePath M x π cfg → cfg.state ∈ M.acceptStates →
      (∀ step ∈ π, step.fromState ∉ M.acceptStates) →
      dtmMoveCount π ≤ p x.length

/-- NTM2 的多项式时间（同口径：格子移动数 + 首达接受）。 -/
def NTM2.isPolynomialTime (A : NTM2) : Prop :=
  ∃ p : ℕ → ℕ, IsPolynomialBound p ∧
    ∀ (x : List F4) (π : NTM2ComputationPath) (cfg : NTM2Config A x),
      TapeReachablePathNTM2 A x π cfg → cfg.state ∈ A.acceptStates →
      (∀ step ∈ π, step.fromState ∉ A.acceptStates) →
      ntm2MoveCount π ≤ p x.length

-- ============================================================================
-- §5 算法性（谓词式 ATM）
-- ============================================================================

/-- 算法性（"能处理输入"）：对任意符号串，运行最终进入判态（接受或拒绝）。
    确定性 ⇒ 该判态路径即机器的唯一运行结局。 -/
def ClassicDTM.IsAlgorithm (M : ClassicDTM) : Prop :=
  ∀ x : List F4, ∃ (π : List DTMTransitionStep) (cfg : DTMConfig M),
    DTMTapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates ∪ M.rejectStates

-- ============================================================================
-- §6 符号输入上的 P / NP
-- ============================================================================

/-- 符号输入上的 P：存在算法处置的 DTM，多项式（格移计）判定全输入。 -/
structure IsP_sym (L : Set (List F4)) : Prop where
  exists_machine : ∃ M : ClassicDTM, M.IsAlgorithm ∧ M.isPolynomialTime ∧
    (∀ x : List F4, M.acceptsTape x ↔ L x)

/-- 符号输入上的 NP：存在多项式（格移计）NTM2 判定全输入。 -/
def IsNP_sym (L : Set (List F4)) : Prop :=
  ∃ A : NTM2, A.isPolynomialTime ∧ (∀ x : List F4, NTM2.acceptsTape A x ↔ L x)

/-- 符号输入上的 P 类（语言集合）。 -/
def P_sym : Set (Set (List F4)) := { L | IsP_sym L }

/-- 符号输入上的 NP 类（语言集合）。 -/
def NP_sym : Set (Set (List F4)) := { L | IsNP_sym L }

-- ============================================================================
-- §7 多带版视图（用户裁决 2026-09-14：ATM 与 CBTM 均改多带版描述）
-- ============================================================================

-- （一）DTM（ATM）两带：输入带 + 指示带（2bit 表输入）

/-- 带 1（输入带）投影：第 1 分量。
    数据位 0/1；结构位置 sep 记 0、分界（#）记 1。 -/
def inpTape (x : List F4) : List Bool := x.map F4.re

/-- 带 2（指示带）投影：第 2 分量。
    数据位置 0 = 数据；1 = 分隔与分界。 -/
def indTape (x : List F4) : List Bool := x.map F4.im

@[simp] theorem inpTape_nil : inpTape ([] : List F4) = [] := rfl
@[simp] theorem indTape_nil : indTape ([] : List F4) = [] := rfl
@[simp] theorem inpTape_cons (s : F4) (t : List F4) : inpTape (s :: t) = F4.re s :: inpTape t := rfl
@[simp] theorem indTape_cons (s : F4) (t : List F4) : indTape (s :: t) = F4.im s :: indTape t := rfl
theorem inpTape_length (x : List F4) : (inpTape x).length = x.length := by simp [inpTape]
theorem indTape_length (x : List F4) : (indTape x).length = x.length := by simp [indTape]

-- 四个输入符号的两带逐值表（约定 20）
@[simp] theorem re_zero : F4.re F4.zero = false := rfl
@[simp] theorem im_zero : F4.im F4.zero = false := rfl
@[simp] theorem re_one : F4.re F4.one = true := rfl
@[simp] theorem im_one : F4.im F4.one = false := rfl
@[simp] theorem re_alpha : F4.re F4.alpha = false := rfl
@[simp] theorem im_alpha : F4.im F4.alpha = true := rfl
@[simp] theorem re_beta : F4.re F4.beta = true := rfl
@[simp] theorem im_beta : F4.im F4.beta = true := rfl

-- （二）CBTM：2F4 编码（两带各一个 F4 = 位＋虚部）
--
-- 对应链（用户裁决 2026-09-14）：NTM2 = DTM 增加分支语法；分支语法 ↔ vb = 1；
--   **vb 的值 ↔ 2F4 虚部是否有 1（一一映射）**。
--   意义（补正 2026-09-14）：NTM2 内部排除不了假分支（语义超越语法）；
--   排除机制在 CBTM 的不可公度性——在 IVM 里才把两条路径完全分开；
--   vb ↔ 虚部双射 = 装载通道（分离性本身是 CBTM/IVM 侧定理）。
--   形式目标（待落）：vbAt A i = true ↔ (2F4 格 i).1.2 = true。

/-- CBTM 的 2F4 格（多带版）：((t₁,v₁),(t₂,v₂))——
    两条带各一格 F4 = 位＋虚部维度。 -/
abbrev CBTMCell2 := F4 × F4

/-- 第 1 带虚部标志（讨论位）。 -/
def cellV1 (c : CBTMCell2) : Bool := c.1.2

/-- 第 2 带虚部标志。 -/
def cellV2 (c : CBTMCell2) : Bool := c.2.2

/-- 虚部全 0 层：与 DTM 同构的域（DTM≅CBTM0）。 -/
def cellZeroVirt (c : CBTMCell2) : Prop := c.1.2 = false ∧ c.2.2 = false

/-- 数据读出（实部层）：(t₁,t₂) = Bool×Bool——DTM 的输入位对。 -/
def cellData (c : CBTMCell2) : F4 := (c.1.1, c.2.1)

/-- 输入位对（Bool×Bool）的 2F4 提升：虚部全 0。 -/
def liftInput (s : F4) : CBTMCell2 := ((F4.re s, false), (F4.im s, false))

@[simp] theorem cellData_liftInput (s : F4) : cellData (liftInput s) = s := by
  cases s with
  | mk a b => rfl

@[simp] theorem cellV1_liftInput (s : F4) : cellV1 (liftInput s) = false := rfl
@[simp] theorem cellV2_liftInput (s : F4) : cellV2 (liftInput s) = false := rfl
theorem cellZeroVirt_liftInput (s : F4) : cellZeroVirt (liftInput s) := ⟨rfl, rfl⟩

end Mp
