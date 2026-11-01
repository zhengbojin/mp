import Mp.ATMAssembly

/-!
# 经典 P/NP 的符号语义（ATM）刻画与分离 —— 定义级

用户裁决（2026-10-31）：`P_atm` 取**定义级**——经典 P 在符号语义下的刻画
= **CBTM|0 层**（虚部 ≡ 0 的受限机）。本文件只做两件事：

1. **定义**（不是定理）：`IsP_atm := IsP_sym0`，`IsNP_atm := IsNP_sym0`。
   这是「ATM 的符号读带分支位 ⇒ 确定性 ATM 不消费分支维 ⇒ 正好是 CBTM|0」
   这一判断的形式落点。
2. **定理**（已有、机器核验、0 axiom / 0 sorry）：`P_atm ≠ NP_atm`，
   见证 = 子集和：`∈ NP_atm` 且 `∉ P_atm`。

## 三条限定（必须与结论同时出现，防误读）

- **(a) P 侧的定义**：`P_atm` 的承载机 = 虚部 ≡ 0 层（`IsRestricted`），
  **不是**任意 `ClassicDTM`。能读 α/β 的经典机不在承载域
  （`ClassicDTM.toCBTMTrans` 对 α/β 返回 ∅，`Mp/ATMBridge.lean:104-109`）。
- **(b) 判定域**：两侧都只在**对齐域** `IsSymbolAligned` 上断言（4F4 编译像）。
- **(c) 引擎**：分离的引擎是**能力缺口**（受限机读不到元素标记 α ⇒ κ=0；
  正确性 ⇒ κ ≥ n），**证明不引用时间界**（`subsetSum_not_in_P_sym0` 未用 `_hpoly`）。
  即：本结论说的是"结构/分支维不可省"，不是"多项式时间不够"。

## 因此本文件的读法

`P_atm ≠ NP_atm` 是定理；「`P_atm` 就是经典 P」是**刻画判断**（定义），
不是定理。二者相加 = 「符号语义基础上经典 P ≠ NP」，其中判断部分须显式声明。
-/

namespace Mp

/-- 经典 P 的符号语义刻画（定义级）：CBTM|0 层。 -/
def IsP_atm (L : Set (List F4)) : Prop := IsP_sym0 L

/-- 经典 NP 的符号语义刻画（定义级）：NTM2 层（分支维可用）。 -/
def IsNP_atm (L : Set (List F4)) : Prop := IsNP_sym0 L

/-- 类（语言集合）。 -/
def P_atm : Set (Set (List F4)) := { L | IsP_atm L }

/-- 类（语言集合）。 -/
def NP_atm : Set (Set (List F4)) := { L | IsNP_atm L }

/-- 定义级恒等：`P_atm` 就是 CBTM|0 层。 -/
theorem P_atm_eq_P_sym0 : P_atm = P_sym0 := rfl

/-- 定义级恒等：`NP_atm` 就是 NTM2 层。 -/
theorem NP_atm_eq_NP_sym0 : NP_atm = NP_sym0 := rfl

/-- **经典 P ≠ NP（符号语义/ATM 基础，定义级）**。 -/
theorem P_atm_neq_NP_atm : P_atm ≠ NP_atm := by
  rw [P_atm_eq_P_sym0, NP_atm_eq_NP_sym0]
  exact P_sym0_neq_NP_sym0

/-- 分离见证：子集和 ∈ NP_atm 且 ∉ P_atm。 -/
theorem subsetSum_separates_atm :
    IsNP_atm subsetSumLanguageF4Real ∧ ¬ IsP_atm subsetSumLanguageF4Real :=
  ⟨subsetSum_in_NP_sym0, subsetSum_not_in_P_sym0⟩

end Mp
