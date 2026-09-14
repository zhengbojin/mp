/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mathlib
import Mp.Basic

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

open NTM2
open ClassicDTM

-- F₄ 的实例需置于所有依赖它的结构之前
instance : DecidableEq F4 := inferInstanceAs (DecidableEq (Bool × Bool))
instance : Fintype F4 := inferInstanceAs (Fintype (Bool × Bool))

-- ===========================================================================
-- 基本辅助函数
-- ===========================================================================

/-- 将布尔值映射到实部 F₄ 符号。 -/
def boolToF4 (b : Bool) : F4 := (b, false)

/-- 将虚部为 false 的 F₄ 符号映射回布尔值。 -/
def f4ToBool (s : F4) : Bool := s.1

/-- boolToF4 的虚部恒为 false。 -/
@[simp] theorem boolToF4_im_false (b : Bool) : F4.im (boolToF4 b) = false := rfl

/-- f4ToBool 与 boolToF4 互逆（在实部符号上）。 -/
theorem f4ToBool_boolToF4 (b : Bool) : f4ToBool (boolToF4 b) = b := rfl

@[simp] theorem boolToF4_false : boolToF4 false = F4.zero := rfl
@[simp] theorem boolToF4_true : boolToF4 true = F4.one := rfl

-- ===========================================================================
-- §1. CBTM 转移结果
-- ===========================================================================

structure CBTMTransResult : Type where
  nextState : ℕ
  writeSym  : F4
  moveDir   : Dir
  deriving DecidableEq

-- ===========================================================================
-- §2. CBTM 结构体
-- ===========================================================================

structure CBTM : Type where
  states      : Finset ℕ
  startState  : ℕ
  acceptStates : Finset ℕ
  rejectStates : Finset ℕ
  alphabet    : Finset F4
  /-- 转移依赖磁头位置：(q, 读符号, 磁头位置) → 结果集。 -/
  transition  : ℕ × F4 × ℤ → Finset CBTMTransResult
  blankSym    : F4
  h_blank_in_alphabet : blankSym ∈ alphabet
  h_start_in_states   : startState ∈ states
  h_accept_subset     : acceptStates ⊆ states
  h_reject_subset     : rejectStates ⊆ states
  h_accept_reject_disjoint : acceptStates ∩ rejectStates = ∅
  /-- 严格分支公理：虚部 false → 1 个结果；虚部 true → 恰好 2 个结果（与位置无关）。 -/
  h_branch_rule : ∀ q s i, s ∈ alphabet →
    if F4.im s then (transition (q, s, i)).card = 2 else (transition (q, s, i)).card = 1
  /-- 投影约束：虚部 false 的读符号 → 写回符号虚部也为 false。 -/
  h_projection_constraint : ∀ q s i, s ∈ alphabet → F4.im s = false →
    (transition (q, s, i)).card = 1 ∧
    ∀ r ∈ (transition (q, s, i)), F4.im r.writeSym = false
  /-- 良构性：转移结果状态属于状态集。 -/
  isValid : ∀ q s i, s ∈ alphabet → ∀ r ∈ (transition (q, s, i)), r.nextState ∈ states
  /-- 字母表外的读符号无转移。 -/
  h_transition_outside : ∀ q s i, s ∉ alphabet → transition (q, s, i) = ∅

-- ===========================================================================
-- §2.5 CBTM 计算语义
-- ===========================================================================

/-- CBTM 转移步：读符号与选定的转移结果。 -/
structure TransitionStep : Type where
  fromState : ℕ
  readSym   : F4
  result    : CBTMTransResult

instance : Inhabited TransitionStep :=
  ⟨{ fromState := 0, readSym := F4.zero, result := ⟨0, F4.zero, Dir.S⟩ }⟩

/-- CBTM 计算路径 = 转移步列表。 -/
abbrev ComputationPath := List TransitionStep

namespace ComputationPath

/-- 路径末端状态（空路径为初始状态）。 -/
def endState (M : CBTM) (π : ComputationPath) : ℕ :=
  π.foldl (fun _ step => step.result.nextState) M.startState

end ComputationPath

/-- CBTM 的可达路径：读符号序列恰为输入，每一步都是合法转移（含磁头位置追踪）。 -/
inductive ReachablePath (M : CBTM) : List F4 → ℤ → ComputationPath → Prop
  | nil : ReachablePath M [] 0 []
  | cons : ∀ (xs : List F4) (a : F4) (pos : ℤ) (π₀ : ComputationPath) (step : TransitionStep),
      ReachablePath M xs pos π₀ →
      step.fromState = ComputationPath.endState M π₀ →
      step.readSym = a →
      step.result ∈ M.transition (ComputationPath.endState M π₀, a, pos) →
      ReachablePath M (xs ++ [a]) (pos + step.result.moveDir.toInt) (π₀ ++ [step])

namespace ReachablePath

/-- 路径是否在接受状态结束。 -/
def isAccepting (M : CBTM) (π : ComputationPath) : Bool :=
  decide (ComputationPath.endState M π ∈ M.acceptStates)

end ReachablePath

/-- CBTM 接受一个 F4 串。 -/
def CBTM.accepts (M : CBTM) (x : List F4) : Prop :=
  ∃ π, ∃ pos, ReachablePath M x pos π ∧ ReachablePath.isAccepting M π = true

-- ===========================================================================
-- §2.6 复杂度类辅助谓词
-- ===========================================================================

/-- 受限 CBTM：字母表仅含实部符号，转移确定（无分支）。 -/
structure CBTM.IsRestricted (M : CBTM) : Prop where
  h_alphabet_subset : M.alphabet ⊆ {F4.zero, F4.one}
  h_alphabet_im_false : ∀ s, s ∈ M.alphabet → F4.im s = false
  h_card_one : ∀ q s i, s ∈ M.alphabet → (M.transition (q, s, i)).card = 1
  h_blank_in_alphabet : M.blankSym ∈ M.alphabet

/-- 多项式界：存在 k，∀ n，p n ≤ n^k + k（标准多项式形态，足够宽松）。
    真实多项式时间定义（替换旧占位 `= True`）见 Mp.IVM（依赖磁带语义 TapeReachablePath，
    定义于 TapeReachablePath 之后）；此处仅保留多项式界谓词。 -/
def IsPolynomialBound (p : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, p n ≤ n ^ k + k

-- ===========================================================================
-- 辅助：基数 1 的有限集恰有唯一元素
-- ===========================================================================

lemma card_eq_one_unique_mem {α : Type*} (s : Finset α) (h : s.card = 1) :
    ∃! a : α, a ∈ s := by
  classical
  rcases Finset.card_eq_one.mp h with ⟨a, ha⟩
  subst ha
  exact ⟨a, by simp, by intro b hb; simpa using hb⟩

-- ===========================================================================
-- NTM2 ↔ CBTM 同构（符号驱动：两机器同字母表 F4，恒等翻译）
-- ===========================================================================

/-- NTM2 转移结果 → CBTM 转移结果：恒等翻译（符号不变，虚部随符号走）。 -/
def ntm2ResultToCBTM (r : ℕ × F4 × Dir) : CBTMTransResult :=
  CBTMTransResult.mk r.1 r.2.1 r.2.2

/-- 恒等翻译是单射（三字段逐一对应）。 -/
lemma ntm2ResultToCBTM_injective :
    Function.Injective (ntm2ResultToCBTM) := by
  intro r1 r2 h
  rcases r1 with ⟨n1, w1, d1⟩
  rcases r2 with ⟨n2, w2, d2⟩
  have hn : n1 = n2 := congrArg CBTMTransResult.nextState h
  have hw : w1 = w2 := congrArg CBTMTransResult.writeSym h
  have hd : d1 = d2 := congrArg CBTMTransResult.moveDir h
  subst n1
  subst w1
  subst d1
  rfl

/-- NTM2 → CBTM 的转移函数：字母表内恒等翻译（符号驱动分支完全保留）；
    字母表外无转移（非法计算，不影响语言）。 -/
def NTM2.toCBTMTrans (A : NTM2) : ℕ × F4 × ℤ → Finset CBTMTransResult :=
  fun (q, s, i) =>
    if hc : s ∈ A.alphabet then
      (A.transition (q, s, i)).image ntm2ResultToCBTM
    else ∅

/-- 字母表内转移的恒等翻译展开。 -/
lemma toCBTMTrans_eq (A : NTM2) (q : ℕ) (s : F4) (i : ℤ) (hs : s ∈ A.alphabet) :
    NTM2.toCBTMTrans A (q, s, i) =
      (A.transition (q, s, i)).image ntm2ResultToCBTM := by
  simp [NTM2.toCBTMTrans, hs]

/-- NTM2 → CBTM：结构恒等（一一映射：状态/起止/字母表/空白符/转移全部对应；
    符号驱动分支由 h_branch_rule 直接继承）。 -/
def NTM2.toCBTM (A : NTM2) : CBTM :=
{
  states      := A.states
  startState  := A.startState
  acceptStates := A.acceptStates
  rejectStates := A.rejectStates
  alphabet    := {F4.zero, F4.one, F4.alpha, F4.beta}
  transition  := NTM2.toCBTMTrans A
  blankSym    := A.blankSym
  h_blank_in_alphabet := by
    rcases A.blankSym with ⟨r, im⟩ <;> cases r <;> cases im <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta]
  h_start_in_states   := A.h_start_in_states
  h_accept_subset     := A.h_accept_subset
  h_reject_subset     := A.h_reject_subset
  h_accept_reject_disjoint := A.h_accept_reject_disjoint
  h_branch_rule := by
    intro q s i hs
    unfold NTM2.toCBTMTrans
    have hc : s ∈ A.alphabet := by
      rw [A.h_alphabet_all]
      exact hs
    simp [hc]
    rw [Finset.card_image_of_injective (A.transition (q, s, i)) ntm2ResultToCBTM_injective]
    have hb := A.h_branch_rule q s i hc
    by_cases him : F4.im s <;> simp [him] at hb ⊢
    · exact hb
    · exact hb
  h_projection_constraint := by
    intro q s i hs him
    have hc : s ∈ A.alphabet := by
      rw [A.h_alphabet_all]
      exact hs
    constructor
    · unfold NTM2.toCBTMTrans
      simp [hc]
      rw [Finset.card_image_of_injective (A.transition (q, s, i)) ntm2ResultToCBTM_injective]
      have hb := A.h_branch_rule q s i hc
      simp [him] at hb
      exact hb
    · intro r hr
      have hr' : r ∈ (A.transition (q, s, i)).image ntm2ResultToCBTM := by
        simpa [NTM2.toCBTMTrans, hc] using hr
      rcases Finset.mem_image.mp hr' with ⟨r0, hr0, hf⟩
      rw [← hf]
      exact A.h_write_projection q s i hc him r0 hr0
  isValid := by
    intro q s i hs r hr
    have hc : s ∈ A.alphabet := by
      rw [A.h_alphabet_all]
      exact hs
    have hr' : r ∈ (A.transition (q, s, i)).image ntm2ResultToCBTM := by
      simpa [NTM2.toCBTMTrans, hc] using hr
    rcases Finset.mem_image.mp hr' with ⟨r0, hr0, hf⟩
    rw [← hf]
    exact A.h_transition_state_mem q s i hc r0 hr0
  h_transition_outside := by
    intro q s i hs_not
    exfalso
    rcases s with ⟨r, im⟩ <;> cases r <;> cases im <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta] at hs_not
}

@[simp] theorem toCBTM_states (A : NTM2) : (NTM2.toCBTM A).states = A.states := rfl
@[simp] theorem toCBTM_startState (A : NTM2) : (NTM2.toCBTM A).startState = A.startState := rfl
@[simp] theorem toCBTM_acceptStates (A : NTM2) : (NTM2.toCBTM A).acceptStates = A.acceptStates := rfl
@[simp] theorem toCBTM_rejectStates (A : NTM2) : (NTM2.toCBTM A).rejectStates = A.rejectStates := rfl
@[simp] theorem toCBTM_transition (A : NTM2) : (NTM2.toCBTM A).transition = NTM2.toCBTMTrans A := rfl
@[simp] theorem toCBTM_blankSym (A : NTM2) : (NTM2.toCBTM A).blankSym = A.blankSym := rfl

-- ===========================================================================
-- 结构同构：NTM2 ↔ CBTM（一一映射：符号恒等，转移恒等翻译）
-- ===========================================================================

/-- NTM2 与 CBTM 的结构同构：同一状态/起止/接受/拒绝 + 符号恒等 + 转移对应（字母表内）。 -/
structure StructIsoNTM2CBTM (A : NTM2) (M : CBTM) : Type where
  h_states_eq : M.states = A.states
  h_start : M.startState = A.startState
  h_accept : M.acceptStates = A.acceptStates
  h_reject : M.rejectStates = A.rejectStates
  φ_symbol : Equiv F4 { s : F4 // s ∈ M.alphabet }
  h_φ_id : ∀ s : F4, (φ_symbol s).val = s
  h_blank : M.blankSym = A.blankSym
  h_transition : ∀ (q : ℕ) (s : F4) (i : ℤ), s ∈ A.alphabet →
    M.transition (q, (φ_symbol s).val, i) =
      (A.transition (q, s, i)).image ntm2ResultToCBTM

/-- 字母表为全集时的恒等嵌入。 -/
def alphabetSubtypeEquiv (M : CBTM) (h_alphabet : M.alphabet = {F4.zero, F4.one, F4.alpha, F4.beta}) :
    Equiv F4 { s : F4 // s ∈ M.alphabet } := {
  toFun := fun s => ⟨s, by
    rw [h_alphabet]
    rcases s with ⟨r, i⟩ <;> cases r <;> cases i <;>
      simp [F4.zero, F4.one, F4.alpha, F4.beta]⟩
  invFun := fun s => s.1
  left_inv := by intro s; rfl
  right_inv := by
    intro s
    rcases s with ⟨val, prop⟩
    apply Subtype.ext
    rfl
}

/-- 方向 1：每个 NTM2 都同构于某个 CBTM（无条件，恒等嵌入；M = NTM2.toCBTM A）。 -/
theorem exists_CBTM_iso_NTM2 (A : NTM2) :
    ∃ M : CBTM, M = NTM2.toCBTM A ∧ Nonempty (StructIsoNTM2CBTM A M) := by
  let M := NTM2.toCBTM A
  let φ_symbol : Equiv F4 { s : F4 // s ∈ M.alphabet } := {
    toFun := fun s => ⟨s, by
      rcases s with ⟨r, i⟩ <;> cases r <;> cases i <;>
        simp [M, NTM2.toCBTM, F4.zero, F4.one, F4.alpha, F4.beta]⟩
    invFun := fun s => s.1
    left_inv := by intro s; rfl
    right_inv := by
      intro s
      rcases s with ⟨val, prop⟩
      apply Subtype.ext
      rfl
  }
  refine ⟨M, rfl, ⟨{
    h_states_eq := rfl
    h_start := rfl
    h_accept := rfl
    h_reject := rfl
    φ_symbol := φ_symbol
    h_φ_id := by intro s; rfl
    h_blank := rfl
    h_transition := by
      intro q s i hs
      have hφ : ((φ_symbol s).val) = s := rfl
      rw [hφ]
      unfold M
      rw [toCBTM_transition]
      exact toCBTMTrans_eq A q s i hs
  }⟩⟩

-- 输入虚部计数（上移自 SubsetSumReal：Core/编译层/下界层共用）
-- ======================================================================
/-- 输入中虚部为 true 的符号数。 -/
def imTrueCount (w : List F4) : ℕ :=
  (w.filter (fun s => F4.im s)).length

lemma imTrueCount_append (w₁ w₂ : List F4) :
    imTrueCount (w₁ ++ w₂) = imTrueCount w₁ + imTrueCount w₂ := by
  unfold imTrueCount
  rw [List.filter_append, List.length_append]

end Mp
