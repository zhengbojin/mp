/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.ATMBasic

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
# Mp.ATMBridge —— 符号层 ↔ bit 层转换与桥

- **bit 转换**：直读位对即 2bit 码——`codeBits s = [F4.re s, F4.im s]`；
  0↦00、1↦10、sep↦01、#↦11；`toBits`/`ofBits` 互逆，长度 ×2。
- **确定性（DTM）单卡事实**：DTM 转移结果唯一 ⇒ 对应 CBTM 结果集恒单元素（card = 1）——
  为 DTM≅CBTM0 桥与 κ 传递备料（接口见 design 纸面件 §6；带外写 alpha、blank=alpha 已裁）。
- **DTM 侧 F4 口径（用户裁决）**：F4 按 `Bool × Bool` 理解——机器只读一对 bit，不带虚部语义。
- **CBTM 侧口径（用户裁决）**：F4 = bool（数据）＋虚部；就输入数据而言只占 1 个 bit。
- 时间计量 = 格子移动数（`dtmMoveCount`/`ntm2MoveCount`，见 ATMBasic）。
-/

namespace Mp

-- ============================================================================
-- §1 bit 转换（直读位对 = 2bit 码；长度 ×2）
-- ============================================================================

/-- 2bit 码：直读位对 (re, im)。0↦00、1↦10、sep↦01、#↦11。 -/
def codeBits (s : F4) : List Bool := [F4.re s, F4.im s]

/-- 码长恒 2。 -/
theorem codeBits_length (s : F4) : (codeBits s).length = 2 := rfl

/-- 符号串 → bit 串（逐符号 2bit）。 -/
def toBits : List F4 → List Bool
  | [] => []
  | s :: t => codeBits s ++ toBits t

/-- cons 展开。 -/
theorem toBits_cons (s : F4) (t : List F4) : toBits (s :: t) = codeBits s ++ toBits t := rfl

/-- bit 串 → 符号串（2bit 配对；奇尾补一位 false——偶长为主定理域，奇长按此约定）。 -/
def ofBits : List Bool → List F4
  | [] => []
  | b :: [] => [(b, false)]
  | b₁ :: b₂ :: rest => (b₁, b₂) :: ofBits rest

/-- 编码长度 ×2。 -/
theorem toBits_length (x : List F4) : (toBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons s t ih =>
    rw [toBits_cons, List.length_append, ih, codeBits_length, List.length_cons]
    ring

/-- 互逆（符号 → bit → 符号）。 -/
theorem ofBits_toBits (x : List F4) : ofBits (toBits x) = x := by
  induction x with
  | nil => rfl
  | cons s t ih =>
    obtain ⟨r, i⟩ := s
    cases r <;> cases i <;> simp [toBits_cons, codeBits, ofBits, ih]

-- ============================================================================
-- §2 DTM 确定性单卡（为 DTM≅CBTM0 桥备料）
-- ============================================================================

/-- DTM 转移结果 → CBTM 转移结果（同名翻译）。 -/
def dtmResultToCBTM (r : ClassicDTMTransitionResult) : CBTMTransResult :=
  { nextState := r.nextState, writeSym := r.writeSym, moveDir := r.move }

/-- DTM 的转移集（单元素；确定性 ⇒ 无分支）。 -/
def dtmTransitionSet (M : ClassicDTM) (q : ℕ) (s : F4) : Finset CBTMTransResult :=
  {dtmResultToCBTM (M.transition (q, s))}

/-- 单卡：DTM 的转移集基数恒 1。 -/
theorem dtmTransitionSet_card_one (M : ClassicDTM) (q : ℕ) (s : F4) :
    (dtmTransitionSet M q s).card = 1 :=
  Finset.card_singleton _

/-- DTM 一步记录 → CBTM 一步（结果翻译）。 -/
def dtmStepToCBTM (st : DTMTransitionStep) : TransitionStep :=
  { fromState := st.fromState, readSym := st.readSym, result := dtmResultToCBTM st.result }

end Mp
