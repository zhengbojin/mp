import Mp.SubsetSumReal
import Mp.ATMAssembly

/-!
# 公理：sep 的纸带像 = α（Im = 1）

用户裁决（2026-10-31）：**按公理处理**。

- FULL CBTM：`α = sep * {Im = 1}` —— 参数边界在纸带上取 α，**读即分支**
  （承载于 `CBTM.h_branch_rule`：`Im = 1 ⇒ card = 2`）。
- CBTM|0：`sep = sep * {Im = 0}` —— |0 层没有 α，也**没有可承载 sep 的符号**：
  鸽笼事实 `plain_layer_two_symbols`：`F4` 中 `Im = false` 的符号只有 `zero`/`one`，
  装不下「4 个输入符号 + α/β」。

于是（两条都在库里，本文件把它们与公理接上）：

1. `P_cb` 侧机器读不到参数边界（`CBTM.h_transition_outside`：读字母表外符号 ⇒ 转移 = ∅）
   ⇒ `kappa_M ≡ 0`（`kappa_zero_of_restricted`）；
2. 任何正确机 `κ ≥ n`（`subsetSum_kappa_lower_bound`，其载荷是
   `imTrueCount_encodeInstanceF4 = elements.length`）。

两者相撞 ⇒ **不存在正确的受限机**（`no_correct_restricted_machine`）⇒ `P_cb ≠ NP_cb`
⇒ 经定义级刻画 `P_atm ≠ NP_atm`（`Mp/ClassicalProjection.lean`）。
-/

namespace Mp

open SymToF4

-- ============================================================================
-- §1 公理本体
-- ============================================================================

/-- **公理（sep 的纸带像）**：参数边界符在纸带上是 α，即 `Im = 1`。 -/
def ParamSep : F4 := F4.alpha

@[simp] theorem ParamSep_im : F4.im ParamSep = true := rfl

/-- 公理的直接后果：字母表含 `ParamSep` 的 CBTM，读到它必给两个后继。 -/
theorem ParamSep_forces_branch (M : CBTM) (q : ℕ) (i : ℤ)
    (h : ParamSep ∈ M.alphabet) : (M.transition (q, ParamSep, i)).card = 2 := by
  have hb := M.h_branch_rule q ParamSep i h
  simpa [ParamSep] using hb

/-- |0 侧：`Im = false` 的纸带符号只有 `zero`/`one`——
    「sep 在 |0 层是普通符号」在 `F4` 里无处安放（鸽笼）。 -/
theorem plain_layer_two_symbols {s : F4} (hs : F4.im s = false) :
    s = F4.zero ∨ s = F4.one := by
  rcases s with ⟨a, b⟩
  simp [F4.im] at hs
  subst hs
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

-- ============================================================================
-- §2 公理下的分离引擎：正确的受限机不存在
-- ============================================================================

/-- **分离引擎（公理版）**：在满足 `hholds` 等前提的实例上，
    不存在既受限（`IsRestricted`，即 |0 层、「sep→α」公理下读不到参数边界）
    又在符号对齐域上正确的 CBTM。

    证明 = 下界（`κ ≥ n`）× 受限机（`κ = 0`）。**不引用任何时间界**。 -/
theorem no_correct_restricted_machine (inst : SubsetSumInstance)
    (hholds : subsetSumHolds inst) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htgt : 0 < inst.target)
    (M : CBTM) (hrest : CBTM.IsRestricted M)
    (hM : ∀ w, IsSymbolAligned w → (M.tapeAccepts w ↔ subsetSumLanguageF4Real w)) : False := by
  have hlow := subsetSum_kappa_lower_bound M inst hholds hne hpos htgt hM
  have hzero := kappa_zero_of_restricted M (encodeInstanceF4 inst) hrest
  rw [hzero] at hlow
  have hposn : 0 < inst.elements.length := by
    cases h : inst.elements with
    | nil => exact absurd h hne
    | cons _ _ => simp
  omega

/-- 公理版分离的成品陈述（符号层）：`P_sym0 ≠ NP_sym0`。
    `P_atm`/`NP_atm` 的定义级刻画见 `Mp/ClassicalProjection.lean`（`IsP_atm := IsP_sym0`）。 -/
theorem separation_under_sep_axiom : P_sym0 ≠ NP_sym0 := P_sym0_neq_NP_sym0


-- ============================================================================
-- §3 「α 放回数据维」的识别碰撞（形式化）
-- ============================================================================

/-- Sym 的数据码：去掉分支位 i₁ 后剩下的 `(r₁, r₂, r₃)`。 -/
def dataCode (k : SymKind) : Bool × Bool × Bool :=
  let b := Sym.kindBits k
  (b.1, b.2.2.1, b.2.2.2)

/-- Sym 的分支位（4F4 第 4 格的虚部 i₁）。 -/
def branchBit (k : SymKind) : Bool := (Sym.kindBits k).2.1

/-- **识别碰撞**：α 与 data0 的**数据码完全相同**，唯一区别是分支位。 -/
theorem alpha_dataCode_eq_data0 : dataCode SymKind.alpha = dataCode SymKind.data0 := rfl

/-- α 的分支位为 true。 -/
theorem alpha_branchBit_true : branchBit SymKind.alpha = true := rfl

/-- data0 的分支位为 false。 -/
theorem data0_branchBit_false : branchBit SymKind.data0 = false := rfl

/-- 因此「把 α 放回数据维」（抹掉分支位）⇒ 分隔符与数据 0 撞码：
    任何只看数据码的判据都无法把二者分开。 -/
theorem alpha_erase_branch_collides :
    dataCode SymKind.alpha = dataCode SymKind.data0 ∧
    branchBit SymKind.alpha ≠ branchBit SymKind.data0 :=
  ⟨rfl, by rw [alpha_branchBit_true, data0_branchBit_false]; simp⟩

end Mp
