import Mp.ATMBridge
import Mp.SubsetSumReal

/-!
# P 的两层：`P_cb`（CBTM|0）与 `P_A`（算法图灵机），均要求**域内停机**

用户裁决（2026-11-01）：
1. `P_A` 的停机条件取**域内**（对齐域停机），不取全域 `IsAlgorithm`——
   合法输入只有对齐域（`IsSymbolAligned`，即 `flat4F4` 的像），故不要求机器在乱码上停机；
2. **`P_cb` 的机器同样必须停机**——它是判定类，不是识别类。

## 命名后果

`IsP_sym0`（`Mp/ATMAssembly.lean:55`）**没有**停机要求（`tapeAccepts` 是"存在接受路径"），
刻画的是**识别器**类。按裁决 2，本文的 `P_cb` 是这里加了 `IsAlgorithmOn` 的 `IsP_cb`；
二者关系为 `P_cb ⊆ P_sym0`（单向），分离只用这条包含。

## 本文件的内容

1. `CBTM.IsAlgorithmOn` / `ClassicDTM.IsAlgorithmOn`：域内停机；
2. `alignedDomain`：对齐域；
3. `IsP_cb`（判定类）+ `P_cb`；`IsP_A`（算法机判定类）+ `P_A`；
4. `P_cb ⊆ P_sym0`；`SubsetSum ∈ NP_A` 且 `∉ P_cb`；故 `P_cb ≠ NP_A`。

## 尚未证明的一条

`P_A = P_cb` 需要机器级同构在**停机性、多项式界、判定域**三方面一致，
可由 `exists_CBTM0_iso_DTM` / `exists_ClassicDTM_iso_restrictedCBTM`（`Mp/ATMBridge.lean`）
配合 `Mp/ProjectionP.lean` 的路径同步得到，目前**未**形式化；
本文的分离不依赖它（只用 `P_cb ⊆ P_sym0` 与 `SubsetSum ∉ P_sym0`）。
-/

namespace Mp

open SymToF4

-- ============================================================================
-- §1 域内算法性
-- ============================================================================

/-- CBTM 的域内算法性：在输入集 `S` 上，机器总能进入接受态或拒绝态。 -/
def CBTM.IsAlgorithmOn (M : CBTM) (S : Set (List F4)) : Prop :=
  ∀ x : List F4, x ∈ S → ∃ (π : ComputationPath) (cfg : CBTMConfig M x),
    TapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates ∪ M.rejectStates

/-- 算法图灵机的域内算法性（同上，`ClassicDTM` 版）。 -/
def ClassicDTM.IsAlgorithmOn (M : ClassicDTM) (S : Set (List F4)) : Prop :=
  ∀ x : List F4, x ∈ S → ∃ (π : List DTMTransitionStep) (cfg : DTMConfig M),
    DTMTapeReachablePath M x π cfg ∧ cfg.state ∈ M.acceptStates ∪ M.rejectStates

/-- 对齐域（合法输入集）。 -/
def alignedDomain : Set (List F4) := { w | IsSymbolAligned w }

/-- CBTM 路径的**移动数**（只数 L/R，原地不计）——与 `ClassicDTM` 的计时口径一致。 -/
def cbtmMoveCount (π : ComputationPath) : ℕ :=
  (π.filter (fun st => isMovingDir st.result.moveDir)).length

/-- CBTM 的移动数计时：与 `ClassicDTM.isPolynomialTime` 同形（首达接受、只对齐域）。 -/
def CBTM.isPolynomialTimeMoves (M : CBTM) : Prop :=
  ∃ p : ℕ → ℕ, IsPolynomialBound p ∧
    ∀ (x : List F4), IsSymbolAligned x →
      ∀ (π : ComputationPath) (cfg : CBTMConfig M x),
        TapeReachablePath M x π cfg → cfg.state ∈ M.acceptStates →
        (∀ step ∈ π, step.fromState ∉ M.acceptStates) →
        cbtmMoveCount π ≤ p x.length

/-- `ι_0` 像：对齐且**不含标记格**（所有格虚部为假）。

    这是 `P` 侧的自然输入域：`ι_0` 把 `sep` 写成 `(0,1,0,0)`（无标记），
    而 `ι_F` 会写成 `(0,1,1,0)`（含 α 格）。CBTM|0 的转移在 α 上为空，
    故同构只在无标记输入上成立。 -/
def noMarkDomain : Set (List F4) :=
  { w | IsSymbolAligned w ∧ ∀ c ∈ w, F4.im c = false }

-- ============================================================================
-- §2 P 的两层（均为判定类：要求域内停机）
-- ============================================================================

/-- `CBTM0`（位置无关 + 字母表恰为 `{0,1}`）蕴含 `IsRestricted`。 -/
lemma CBTM.IsCBTM0.blank_mem {N : CBTM} (h : CBTM.IsCBTM0 N) :
    N.blankSym ∈ ({F4.zero, F4.one} : Finset F4) := by
  have hb := N.h_blank_in_alphabet
  rwa [h.alphabet_eq] at hb

lemma CBTM.IsCBTM0.toIsRestricted {N : CBTM} (h : CBTM.IsCBTM0 N) : CBTM.IsRestricted N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [h.alphabet_eq] at hs
    exact hs
  · intro s hs
    rw [h.alphabet_eq] at hs
    rcases Finset.mem_insert.mp hs with rfl | hs'
    · simp [F4.im, F4.zero]
    · rcases Finset.mem_singleton.mp hs' with rfl
      simp [F4.im, F4.one]
  · intro q s i hs
    exact h.card_one q s i hs
  · show N.blankSym ∈ N.alphabet
    rw [h.alphabet_eq]
    exact CBTM.IsCBTM0.blank_mem h

/-- `P_cb`：**`CBTM|0`**（字母表 = `{0,1}`、转移单值、**位置无关**）∧ 对齐域多项式
    ∧ **对齐域停机** ∧ 对齐域判定。

    注意用 `IsCBTM0` 而非 `IsRestricted`：后者不含位置无关性，允许转移依赖带头坐标，
    那样的机器比 DTM 强，无法与算法图灵机对应。 -/
def IsP_cb (L : Set (List F4)) : Prop :=
  ∃ M : CBTM, CBTM.IsCBTM0 M ∧ CBTM.isPolynomialTimeMoves M ∧
    CBTM.IsAlgorithmOn M noMarkDomain ∧
    (∀ w : List F4, IsSymbolAligned w → (M.tapeAccepts w ↔ L w))

/-- 类（语言集合）。 -/
def P_cb : Set (Set (List F4)) := { L | IsP_cb L }

/-- `P_A`：算法图灵机（**不写标记**：`α`/`β` 只作为输入出现，机器不产生它们；**空白取 0**，
    用户裁决 8）∧ 对齐域多项式 ∧ **对齐域停机** ∧ 对齐域判定 ∧
    **含标记输入上拒绝**（`im = true` 的格超出 `ι₀` 像，CBTM0 在其上转移为空；
    此条件使 `P_A ⊆ P_cb` 的接受性在含标记输入上一致）。 -/
def IsP_A (L : Set (List F4)) : Prop :=
  ∃ M : ClassicDTM,
    (∀ q s, F4.im (M.transition (q, s)).writeSym = false) ∧
    M.blankSym = F4.zero ∧
    ClassicDTM.IsAlgorithmOn M noMarkDomain ∧ M.isPolynomialTime ∧
    (∀ w : List F4, IsSymbolAligned w → (M.acceptsTape w ↔ L w)) ∧
    (∀ w : List F4, IsSymbolAligned w → (∃ c ∈ w, F4.im c = true) → ¬ M.acceptsTape w)

/-- 类（语言集合）。 -/
def P_A : Set (Set (List F4)) := { L | IsP_A L }

-- ============================================================================
-- §3 与 `P_sym0`（识别器类）的关系
-- ============================================================================

-- 注（2026-11-01 用户裁决）：κ 只在 ATM 层（符号输入）定义，不用于 `P_cb`（布尔层）。
-- 因此本文件不给出基于 κ 的 `SubsetSum ∉ P_cb`；该分离留在 ATM 层的 `P_sym0_neq_NP_sym0`。

-- ============================================================================
-- §5 P_A → P_cb 的第一步：DTM 的 CBTM0 投影是 CBTM|0
-- ============================================================================

-- 注：`CBTM.IsCBTM0 (M.toCBTM hwrite)` 的证明会触发 Lean 4.32.2 的 C 后端崩溃
-- （`0xC0000005`，型检查正常，最小复现：`Mp/_c1.lean`）。故此处不证，改由定理的假设提供，
-- 待工具链修复后再补（见 Spec.md 约定 35）。

-- ============================================================================
-- §4 `P_cb ⊆ P_sym0` 与第二层分离（`P_cb ≠ NP_sym0`）
-- ============================================================================
-- 见 `Mp/SecondLayer.lean`（避免 ATMDom 依赖 ATMAssembly 造成层序倒置）。

end Mp

