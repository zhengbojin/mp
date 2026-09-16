/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/

import Mp.SubsetSumVerifierCBTM4
import Mp.SubsetSumCompile


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


/-!
# Reverse9:q10 条款 1a(Sym 层)素材正式化 — 验证器路径带头合法的前置引理

A1 条款 3(q10 = 证 `NTM2.Canonical subsetSumNTM2`)的 Sym 层素材,
自探针 `_probe_q10h.lean`(EXIT:0)移植。目标:合法输入
`w = encodeInstanceSym inst ++ g` 上验证器路径的每个配置带头都在 `[0, |w|]`
(归纳不变量,条款 1a = Canonical ① 位置界在 Sym 层的一半)。

内容分段:
1. 编码格式长度事实(Enc/elems/target 长度链);
2. 种类分类(bits/elems 每格 kind);
3. 单元格式(cell0/hash/marker/target/elem 的符号值);
4. 初始带事实(init_cell 系列 + 带外空白);
5. 表级闭包(读 boundary 的 R/L 转移、吸收态、写值分类、
   phase/fmt/SE/SUB 状态集闭包)——全部 decide 机械验证。
-/

open Mp

namespace Mp

abbrev Enc (inst : SubsetSumInstance) : List Sym := encodeInstanceSym inst
abbrev NT (inst : SubsetSumInstance) : ℕ := (encodeBitsSym inst.target).length

-- ============================================================================
-- 编码格式事实
-- ============================================================================

/-- encodeElementsSym 的 cons 展开（对任意 rest，含单元素情形）。 -/
lemma q10h_encodeElementsSym_cons (v : ℕ) (rest : List ℕ) :
    encodeElementsSym (v :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym rest := by
  induction rest with
  | nil =>
      simp [encodeElementsSym]
  | cons v' rest' ih =>
      simp [encodeElementsSym, ih]

/-- 元素区长度 = Σ(1 + 位宽)。 -/
lemma q10h_elems_length (elems : List ℕ) :
    (encodeElementsSym elems).length =
      (elems.map (fun v => (encodeBitsSymNative v).length + 1)).sum := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      rw [q10h_encodeElementsSym_cons]
      simp [List.length_append, ih, List.map, List.sum_cons]
      ac_rfl

/-- 编码总长度 = 3 + |target 位| + Σ(1 + 位宽)。 -/
lemma q10h_enc_length (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).length = 3 + (encodeBitsSym inst.target).length +
      (inst.elements.map (fun v => (encodeBitsSymNative v).length + 1)).sum := by
  simp [encodeInstanceSym, List.length_append, q10h_elems_length]
  omega

lemma q10h_enc_ge3 (inst : SubsetSumInstance) : 3 ≤ (encodeInstanceSym inst).length := by
  rw [q10h_enc_length]
  omega

lemma q10h_nt1_le_n2 (inst : SubsetSumInstance) :
    (encodeBitsSym inst.target).length + 1 ≤ (encodeInstanceSym inst).length - 2 := by
  rw [q10h_enc_length]
  omega

lemma q10h_nelems_nt1_le_n3 (inst : SubsetSumInstance) (h : inst.elements ≠ []) :
    (encodeBitsSym inst.target).length + 1 ≤ (encodeInstanceSym inst).length - 3 := by
  rw [q10h_enc_length]
  have hs : 1 ≤ (inst.elements.map (fun v => (encodeBitsSymNative v).length + 1)).sum := by
    rcases hinst : inst.elements with _ | ⟨v, rest⟩
    · exact (h hinst).elim
    · simp [List.map, List.sum_cons]
      omega
  exact Nat.le_sub_of_add_le (by nlinarith)

lemma q10h_nelems_nt3_le_n1 (inst : SubsetSumInstance) (h : inst.elements ≠ []) :
    (encodeBitsSym inst.target).length + 3 ≤ (encodeInstanceSym inst).length - 1 := by
  rw [q10h_enc_length]
  have hs : 1 ≤ (inst.elements.map (fun v => (encodeBitsSymNative v).length + 1)).sum := by
    rcases hinst : inst.elements with _ | ⟨v, rest⟩
    · exact (h hinst).elim
    · simp [List.map, List.sum_cons]
      omega
  exact Nat.le_sub_of_add_le (by nlinarith)

lemma q10h_nt2_le_n1 (inst : SubsetSumInstance) :
    (encodeBitsSym inst.target).length + 2 ≤ (encodeInstanceSym inst).length - 1 := by
  rw [q10h_enc_length]
  exact Nat.le_sub_of_add_le (Nat.le_trans
    (by omega : (encodeBitsSym inst.target).length + 3 ≤ 3 + (encodeBitsSym inst.target).length)
    (Nat.le_add_right (3 + (encodeBitsSym inst.target).length) (inst.elements.map (fun v => (encodeBitsSymNative v).length + 1)).sum))

-- ============================================================================
-- List.getD 桥
-- ============================================================================

/-- 前缀内取格：i < l.length 时 (l ++ m).getD i d = l.getD i d。 -/
lemma q10h_getD_of_append_left {α : Type} (l m : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ m).getD i d = l.getD i d := by
  have h' : i < (l ++ m).length := by
    rw [List.length_append]
    exact Nat.lt_add_right _ h
  rw [List.getD_eq_get (l ++ m) d (Fin.mk i h'), List.getD_eq_get l d (Fin.mk i h)]
  exact List.getElem_append_left (as := l) (bs := m) (i := i) h

/-- 位串格子都是 data0/data1。 -/
lemma q10h_bits_kind (m : ℕ) : ∀ p : ℕ, p < (encodeBitsSym m).length →
    ((encodeBitsSym m).getD p Sym.blank).1 = SymKind.data0 ∨
    ((encodeBitsSym m).getD p Sym.blank).1 = SymKind.data1 := by
  intro p hp
  unfold encodeBitsSym
  change (((Nat.digits 2 m).map (fun d => if d = 0 then Sym.data0 else Sym.data1)).getD p
    (if 0 = 0 then Sym.data0 else Sym.data1)).1 = SymKind.data0 ∨
    (((Nat.digits 2 m).map (fun d => if d = 0 then Sym.data0 else Sym.data1)).getD p
    (if 0 = 0 then Sym.data0 else Sym.data1)).1 = SymKind.data1
  rw [@List.getD_map ℕ Sym (Nat.digits 2 m) 0 p (fun d => if d = 0 then Sym.data0 else Sym.data1)]
  by_cases h0 : (Nat.digits 2 m).getD p 0 = 0
  · left
    rw [h0]
    simp [Sym.data0]
  · right
    rw [if_neg h0]
    simp [Sym.data1]

/-- 元素区格子都是 alpha/data0/data1。 -/
lemma q10h_elems_kind (elems : List ℕ) : ∀ p : ℕ, p < (encodeElementsSym elems).length →
    ((encodeElementsSym elems).getD p Sym.blank).1 = SymKind.alpha ∨
    ((encodeElementsSym elems).getD p Sym.blank).1 = SymKind.data0 ∨
    ((encodeElementsSym elems).getD p Sym.blank).1 = SymKind.data1 := by
  intro p hp
  induction elems generalizing p with
  | nil => cases hp
  | cons v rest ih =>
      cases p with
      | zero =>
          rw [q10h_encodeElementsSym_cons]
          simp [Sym.alpha]
      | succ p' =>
          rw [q10h_encodeElementsSym_cons]
          have hget : ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym rest).getD (p' + 1) Sym.blank =
              (encodeBitsSymNative v ++ encodeElementsSym rest).getD p' Sym.blank := by
            simp
          rw [hget]
          by_cases hb : p' < (encodeBitsSymNative v).length
          · have hk := q10h_bits_kind v p' (by simpa [encodeBitsSym, encodeBitsSymNative, List.length_map] using hb)
            rw [q10h_getD_of_append_left (encodeBitsSymNative v) (encodeElementsSym rest) Sym.blank p' hb]
            rcases hk with hk | hk
            · right; left; exact hk
            · right; right; exact hk
          · have hp'' : p' - (encodeBitsSymNative v).length < (encodeElementsSym rest).length := by
              have hlen : (encodeElementsSym (v :: rest)).length =
                  (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                rw [q10h_encodeElementsSym_cons]
                simp [List.length_append]
                ac_rfl
              have hp' : p' + 1 < (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                rw [hlen] at hp
                exact hp
              omega
            have hrec := ih (p' - (encodeBitsSymNative v).length) hp''
            rw [@List.getD_append_right Sym (encodeBitsSymNative v) (encodeElementsSym rest) Sym.blank p' (by omega)]
            exact hrec

/-- 编码 0 格 = #ₗ。 -/
lemma q10h_cell0 (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD 0 Sym.blank = Sym.boundary := by
  simp [encodeInstanceSym]

/-- 编码末格 = #₁。 -/
lemma q10h_cell_hash1 (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD ((encodeInstanceSym inst).length - 1) Sym.blank = Sym.boundary := by
  let A : List Sym := [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements
  have henc : encodeInstanceSym inst = A ++ [Sym.boundary] := by
    dsimp [A]
    rw [encodeInstanceSym]
    rfl
  have hA : A.length = (encodeInstanceSym inst).length - 1 := by
    rw [henc]
    simp [List.length_append]
  rw [henc]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [@List.getD_append_right Sym A [Sym.boundary] Sym.blank A.length (by omega)]
  simp

/-- #₀ 格（|target|+1）= boundary。 -/
lemma q10h_cell_hash0 (inst : SubsetSumInstance) :
    (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 1) Sym.blank = Sym.boundary := by
  rw [encodeInstanceSym]
  rw [show [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
      ([Sym.boundary] ++ encodeBitsSym inst.target) ++ ([Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary]) from by
    rw [← List.append_assoc, ← List.append_assoc]]
  rw [@List.getD_append_right Sym ([Sym.boundary] ++ encodeBitsSym inst.target)
    ([Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary]) Sym.blank
    ((encodeBitsSym inst.target).length + 1) (by simp [List.length_append])]
  simp

/-- 首元素标记格（|target|+2）= alpha（元素非空时）。 -/
lemma q10h_cell_marker0_alpha (inst : SubsetSumInstance) (h : inst.elements ≠ []) :
    (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 2) Sym.blank = Sym.alpha := by
  rw [encodeInstanceSym]
  rw [show [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
      ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary]) ++ (encodeElementsSym inst.elements ++ [Sym.boundary]) from by
    rw [← List.append_assoc]]
  rw [@List.getD_append_right Sym ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary])
    (encodeElementsSym inst.elements ++ [Sym.boundary]) Sym.blank
    ((encodeBitsSym inst.target).length + 2) (by simp [List.length_append])]
  rw [show (encodeBitsSym inst.target).length + 2 - ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary]).length = 0 from by
    simp [List.length_append]]
  rw [q10h_getD_of_append_left (encodeElementsSym inst.elements) [Sym.boundary] Sym.blank 0 (by
    rcases hinst : inst.elements with _ | ⟨v, rest⟩
    · exact (h hinst).elim
    · simp [q10h_elems_length, List.map, List.sum_cons])]
  rcases hinst : inst.elements with _ | ⟨v, rest⟩
  · exact (h hinst).elim
  · rw [q10h_encodeElementsSym_cons]
    simp [Sym.alpha]

/-- 元素为空时 |target|+2 格 = #₁ = boundary。 -/
lemma q10h_cell_marker0_boundary (inst : SubsetSumInstance) (h : inst.elements = []) :
    (encodeInstanceSym inst).getD ((encodeBitsSym inst.target).length + 2) Sym.blank = Sym.boundary := by
  rcases inst with ⟨elems, target⟩
  have h' : elems = [] := h
  rw [h']
  rw [encodeInstanceSym]
  rw [show [Sym.boundary] ++ encodeBitsSym target ++ [Sym.boundary] ++ encodeElementsSym [] ++ [Sym.boundary] =
      ([Sym.boundary] ++ encodeBitsSym target ++ [Sym.boundary]) ++ (encodeElementsSym [] ++ [Sym.boundary]) from by
    rw [← List.append_assoc]]
  rw [@List.getD_append_right Sym ([Sym.boundary] ++ encodeBitsSym target ++ [Sym.boundary])
    (encodeElementsSym [] ++ [Sym.boundary]) Sym.blank
    ((encodeBitsSym target).length + 2) (by simp [List.length_append])]
  simp [encodeElementsSym]

/-- target 区格（[1, |target|]）= 位串格。 -/
lemma q10h_cell_target (inst : SubsetSumInstance) : ∀ p : ℕ, 1 ≤ p → p ≤ (encodeBitsSym inst.target).length →
    (encodeInstanceSym inst).getD p Sym.blank = (encodeBitsSym inst.target).getD (p - 1) Sym.blank := by
  intro p hp1 hp2
  rw [encodeInstanceSym]
  have hp1' : p = (p - 1) + 1 := by omega
  rw [hp1']
  simp
  exact q10h_getD_of_append_left (encodeBitsSym inst.target)
    ([Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary]) Sym.blank (p - 1) (by omega)

/-- 元素区格（[|target|+2, n-2]）= 元素区 getD。 -/
lemma q10h_cell_elem (inst : SubsetSumInstance) : ∀ p : ℕ,
    (encodeBitsSym inst.target).length + 2 ≤ p → p ≤ (encodeInstanceSym inst).length - 2 →
    (encodeInstanceSym inst).getD p Sym.blank =
      (encodeElementsSym inst.elements ++ [Sym.boundary]).getD (p - ((encodeBitsSym inst.target).length + 2)) Sym.blank := by
  intro p hp1 hp2
  rw [encodeInstanceSym]
  rw [show [Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary] ++ encodeElementsSym inst.elements ++ [Sym.boundary] =
      ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary]) ++ (encodeElementsSym inst.elements ++ [Sym.boundary]) from by
    rw [← List.append_assoc]]
  rw [@List.getD_append_right Sym ([Sym.boundary] ++ encodeBitsSym inst.target ++ [Sym.boundary])
    (encodeElementsSym inst.elements ++ [Sym.boundary]) Sym.blank p
    (by simp [List.length_append, hp1])]
  simp only [List.length_append, List.length_singleton]
  congr 1
  omega

/-- 元素区格子都不是 boundary。 -/
lemma q10h_cell_elem_kind (inst : SubsetSumInstance) : ∀ p : ℕ,
    (encodeBitsSym inst.target).length + 2 ≤ p → p ≤ (encodeInstanceSym inst).length - 2 →
    ((encodeInstanceSym inst).getD p Sym.blank).1 = SymKind.alpha ∨
    ((encodeInstanceSym inst).getD p Sym.blank).1 = SymKind.data0 ∨
    ((encodeInstanceSym inst).getD p Sym.blank).1 = SymKind.data1 := by
  intro p hp1 hp2
  rw [q10h_cell_elem inst p hp1 hp2]
  have hlt : p - ((encodeBitsSym inst.target).length + 2) < (encodeElementsSym inst.elements).length := by
    rw [q10h_elems_length]
    rw [q10h_enc_length] at hp2
    omega
  rw [q10h_getD_of_append_left (encodeElementsSym inst.elements) [Sym.boundary] Sym.blank
    (p - ((encodeBitsSym inst.target).length + 2)) hlt]
  exact q10h_elems_kind inst.elements (p - ((encodeBitsSym inst.target).length + 2)) hlt

/-- 元素区初始 data1 格必在 |target|+3 之后。 -/
lemma q10h_init_data1_ge_nt3 (inst : SubsetSumInstance) : ∀ p : ℕ,
    (encodeBitsSym inst.target).length + 2 ≤ p → p ≤ (encodeInstanceSym inst).length - 2 →
    ((encodeInstanceSym inst).getD p Sym.blank).1 = SymKind.data1 →
    (encodeBitsSym inst.target).length + 3 ≤ p := by
  intro p hp1 hp2 hd
  by_contra hge
  have hp3 : p = (encodeBitsSym inst.target).length + 2 := by omega
  subst p
  by_cases hel : inst.elements = []
  · have hb := q10h_cell_marker0_boundary inst hel
    have hne : SymKind.boundary ≠ SymKind.data1 := by decide
    exact hne (by rw [hb] at hd; exact hd)
  · have ha := q10h_cell_marker0_alpha inst hel
    have hne : SymKind.alpha ≠ SymKind.data1 := by decide
    exact hne (by rw [ha] at hd; exact hd)

-- ============================================================================
-- 初始 tape 事实（nil 基）
-- ============================================================================

/-- 初始 tape 的 j 格 = w.getD j（0 ≤ j）。 -/
lemma q10h_init_tape_getD (w : List Sym) (j : ℤ) (h0 : 0 ≤ j) :
    (symInitialConfig w).tape j = w.getD j.toNat Sym.blank := by
  rw [symInitialConfig]
  change (if h : 0 ≤ j ∧ j.toNat < w.length then w.get ⟨j.toNat, h.2⟩ else Sym.blank) = w.getD j.toNat Sym.blank
  by_cases h : 0 ≤ j ∧ j.toNat < w.length
  · rw [dif_pos h]
    rw [List.getD_eq_get w Sym.blank ⟨j.toNat, h.2⟩]
  · rw [dif_neg h]
    have hge : w.length ≤ j.toNat := by
      rw [not_and] at h
      exact Nat.le_of_not_gt (h h0)
    rw [show w.getD j.toNat Sym.blank = (w ++ []).getD j.toNat Sym.blank from by
      rw [List.append_nil]]
    rw [@List.getD_append_right Sym w [] Sym.blank j.toNat hge]
    rfl

lemma q10h_toNat_le {p : ℤ} {m : ℕ} (hp0 : 0 ≤ p) (h : p ≤ (m : ℤ)) : p.toNat ≤ m := by
  have hpz : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp0
  have h' : (p.toNat : ℤ) ≤ (m : ℤ) := by
    rw [hpz]
    exact h
  exact_mod_cast h'

lemma q10h_toNat_ge {p : ℤ} {m : ℕ} (hp0 : 0 ≤ p) (h : (m : ℤ) ≤ p) : m ≤ p.toNat := by
  have hpz : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp0
  have h' : (m : ℤ) ≤ (p.toNat : ℤ) := by
    rw [hpz]
    exact h
  exact_mod_cast h'

lemma q10h_init_cell0 (inst : SubsetSumInstance) (g : List Sym) :
    (symInitialConfig (Enc inst ++ g)).tape 0 = Sym.boundary := by
  dsimp [Enc]
  rw [q10h_init_tape_getD (encodeInstanceSym inst ++ g) 0 (by omega)]
  change (encodeInstanceSym inst ++ g).getD 0 Sym.blank = Sym.boundary
  have hge := q10h_enc_ge3 inst
  rw [q10h_getD_of_append_left (encodeInstanceSym inst) g Sym.blank 0 (by omega)]
  exact q10h_cell0 inst

lemma q10h_init_cell_hash1 (inst : SubsetSumInstance) (g : List Sym) :
    (symInitialConfig (Enc inst ++ g)).tape (((Enc inst).length : ℤ) - 1) = Sym.boundary := by
  dsimp [Enc]
  have h0 : 0 ≤ ((encodeInstanceSym inst).length : ℤ) - 1 := by
    have hz := q10h_enc_ge3 inst
    omega
  rw [q10h_init_tape_getD (encodeInstanceSym inst ++ g) (((encodeInstanceSym inst).length : ℤ) - 1) h0]
  have hcast : (((encodeInstanceSym inst).length : ℤ) - 1).toNat = (encodeInstanceSym inst).length - 1 := by
    have hz := q10h_enc_ge3 inst
    rw [show ((encodeInstanceSym inst).length : ℤ) - 1 = (((encodeInstanceSym inst).length - 1 : ℕ) : ℤ) from by omega]
    rfl
  rw [hcast]
  rw [q10h_getD_of_append_left (encodeInstanceSym inst) g Sym.blank ((encodeInstanceSym inst).length - 1) (by omega)]
  exact q10h_cell_hash1 inst

lemma q10h_init_cell_target (inst : SubsetSumInstance) (g : List Sym) :
    ∀ p : ℤ, 1 ≤ p → p ≤ (NT inst : ℤ) →
    ((symInitialConfig (Enc inst ++ g)).tape p).1 = SymKind.data0 ∨
    ((symInitialConfig (Enc inst ++ g)).tape p).1 = SymKind.data1 := by
  intro p hp1 hp2
  dsimp [NT, Enc]
  rw [q10h_init_tape_getD (encodeInstanceSym inst ++ g) p (by omega : 0 ≤ p)]
  have hpn : p.toNat ≤ (encodeBitsSym inst.target).length := q10h_toNat_le (by omega : 0 ≤ p) hp2
  have hlt : p.toNat < (encodeInstanceSym inst).length := by
    rw [q10h_enc_length]
    omega
  rw [q10h_getD_of_append_left (encodeInstanceSym inst) g Sym.blank p.toNat hlt]
  have hp1n : 1 ≤ p.toNat := q10h_toNat_ge (by omega : 0 ≤ p) hp1
  have hc := q10h_cell_target inst p.toNat hp1n hpn
  rw [hc]
  have hb : p.toNat - 1 < (encodeBitsSym inst.target).length := by omega
  exact q10h_bits_kind inst.target (p.toNat - 1) hb

lemma q10h_init_cell_elem (inst : SubsetSumInstance) (g : List Sym) :
    ∀ p : ℤ, (NT inst : ℤ) + 2 ≤ p → p ≤ ((Enc inst).length : ℤ) - 2 →
    ((symInitialConfig (Enc inst ++ g)).tape p).1 = SymKind.alpha ∨
    ((symInitialConfig (Enc inst ++ g)).tape p).1 = SymKind.data0 ∨
    ((symInitialConfig (Enc inst ++ g)).tape p).1 = SymKind.data1 := by
  intro p hp1 hp2
  dsimp [NT, Enc]
  dsimp [NT, Enc] at hp1 hp2
  rw [q10h_init_tape_getD (encodeInstanceSym inst ++ g) p (by omega : 0 ≤ p)]
  have hp2' : p ≤ (((encodeInstanceSym inst).length - 2 : ℕ) : ℤ) := by
    have hz := q10h_enc_ge3 inst
    omega
  have hlt : p.toNat < (encodeInstanceSym inst).length := by
    have hpn : p.toNat ≤ (encodeInstanceSym inst).length - 2 :=
      q10h_toNat_le (by omega : 0 ≤ p) hp2'
    omega
  rw [q10h_getD_of_append_left (encodeInstanceSym inst) g Sym.blank p.toNat hlt]
  exact q10h_cell_elem_kind inst p.toNat
    (q10h_toNat_ge (by omega : 0 ≤ p) hp1)
    (q10h_toNat_le (by omega : 0 ≤ p) hp2')

lemma q10h_init_cell_hash0 (inst : SubsetSumInstance) (g : List Sym) :
    (symInitialConfig (Enc inst ++ g)).tape ((NT inst : ℤ) + 1) = Sym.boundary := by
  dsimp [NT, Enc]
  rw [q10h_init_tape_getD (encodeInstanceSym inst ++ g) ((encodeBitsSym inst.target).length + 1 : ℤ) (by omega)]
  have hcast : ((↑(encodeBitsSym inst.target).length + 1 : ℤ)).toNat = (encodeBitsSym inst.target).length + 1 := by
    simp
  rw [hcast]
  have hlt : (encodeBitsSym inst.target).length + 1 < (encodeInstanceSym inst).length := by
    rw [q10h_enc_length]
    omega
  rw [q10h_getD_of_append_left (encodeInstanceSym inst) g Sym.blank ((encodeBitsSym inst.target).length + 1) hlt]
  exact q10h_cell_hash0 inst

lemma q10h_init_cell_marker0 (inst : SubsetSumInstance) (g : List Sym) :
    ((symInitialConfig (Enc inst ++ g)).tape ((NT inst : ℤ) + 2)).1 = SymKind.alpha ∨
    ((symInitialConfig (Enc inst ++ g)).tape ((NT inst : ℤ) + 2)).1 = SymKind.boundary := by
  dsimp [NT, Enc]
  rw [q10h_init_tape_getD (encodeInstanceSym inst ++ g) ((encodeBitsSym inst.target).length + 2 : ℤ) (by omega)]
  have hcast : ((↑(encodeBitsSym inst.target).length + 2 : ℤ)).toNat = (encodeBitsSym inst.target).length + 2 := by
    rw [show ((encodeBitsSym inst.target).length : ℤ) + 2 = (((encodeBitsSym inst.target).length + 2 : ℕ) : ℤ) from rfl]
    rfl
  rw [hcast]
  have hlt : (encodeBitsSym inst.target).length + 2 < (encodeInstanceSym inst).length := by
    rw [q10h_enc_length]
    omega
  rw [q10h_getD_of_append_left (encodeInstanceSym inst) g Sym.blank ((encodeBitsSym inst.target).length + 2) hlt]
  by_cases hel : inst.elements = []
  · right
    rw [q10h_cell_marker0_boundary inst hel]
    rfl
  · left
    rw [q10h_cell_marker0_alpha inst hel]
    rfl

lemma q10h_init_interior (inst : SubsetSumInstance) (g : List Sym) :
    ∀ p : ℤ, (NT inst : ℤ) + 1 ≤ p → p ≤ ((Enc inst).length : ℤ) - 3 →
    (symInitialConfig (Enc inst ++ g)).tape p = Sym.boundary → p = (NT inst : ℤ) + 1 := by
  intro p hp1 hp2 hpB
  dsimp [NT, Enc]
  have hge : (encodeBitsSym inst.target).length + 2 ≤ p.toNat ∨ p.toNat = (encodeBitsSym inst.target).length + 1 := by
    have hpn : (encodeBitsSym inst.target).length + 1 ≤ p.toNat :=
      q10h_toNat_ge (by omega : 0 ≤ p) hp1
    rcases Nat.eq_or_lt_of_le hpn with h | h
    · right
      exact h.symm
    · left
      exact Nat.succ_le_of_lt h
  rcases hge with hge2 | heq
  · have hp1' : (NT inst : ℤ) + 2 ≤ p := by
      dsimp [NT]
      have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega : 0 ≤ p)
      rw [← hcast]
      exact_mod_cast hge2
    have hp2' : p ≤ ((Enc inst).length : ℤ) - 2 := by omega
    have hk := q10h_init_cell_elem inst g p hp1' hp2'
    rcases hk with ha | hd0 | hd1
    · have hne : SymKind.alpha ≠ SymKind.boundary := by decide
      have hbad : SymKind.alpha = SymKind.boundary := by
        rw [← ha]
        rw [hpB]
        rfl
      exact (hne hbad).elim
    · have hne : SymKind.data0 ≠ SymKind.boundary := by decide
      have hbad : SymKind.data0 = SymKind.boundary := by
        rw [← hd0]
        rw [hpB]
        rfl
      exact (hne hbad).elim
    · have hne : SymKind.data1 ≠ SymKind.boundary := by decide
      have hbad : SymKind.data1 = SymKind.boundary := by
        rw [← hd1]
        rw [hpB]
        rfl
      exact (hne hbad).elim
  · have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega : 0 ≤ p)
    rw [← hcast]
    exact_mod_cast heq

-- ============================================================================
-- 表级分类（decide）
-- ============================================================================

/-- q10a ①：读 (boundary, false) 且 R 的转移分类。 -/
lemma q10a_boundary_R_false : (List.range 102).all (fun q =>
    ∀ r : SymTransResult, r ∈ VerifierSym.transition (q, (SymKind.boundary, false)) → r.moveDir = Dir.R →
    q = 0 ∨ q = 1 ∨ q = 38 ∨ q = 28 ∨ q = 77 ∨ q = 9 ∨ q = 12 ∨ q = 11 ∨ q = 14 ∨
      q = 81 ∨ q = 85 ∨ q = 20 ∨ q = 23 ∨ r.nextState = 100 ∨ r.nextState = 101) := by
  native_decide

/-- q10a ②：读 (boundary, true) 且 R 的转移分类。 -/
lemma q10a_boundary_R_true : (List.range 102).all (fun q =>
    ∀ r : SymTransResult, r ∈ VerifierSym.transition (q, (SymKind.boundary, true)) → r.moveDir = Dir.R →
    q = 0 ∨ q = 1 ∨ q = 28 ∨ q = 77 ∨ q = 9 ∨ q = 11 ∨ q = 14 ∨ q = 81 ∨ q = 85 ∨
      q = 20 ∨ q = 23 ∨ r.nextState = 100 ∨ r.nextState = 101) := by
  native_decide

/-- 读 boundary 且 R 的转移：q ∈ Rset ∨ 吸收。 -/
lemma q10h_boundary_R (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hs : s.1 = SymKind.boundary) (hr : r ∈ VerifierSym.transition (q, s)) (hd : r.moveDir = Dir.R) :
    q = 0 ∨ q = 1 ∨ q = 38 ∨ q = 28 ∨ q = 77 ∨ q = 9 ∨ q = 12 ∨ q = 11 ∨ q = 14 ∨
      q = 81 ∨ q = 85 ∨ q = 20 ∨ q = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.boundary := hs
  subst k
  have hb : ∀ q : Fin 102, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk SymKind.boundary m) → r.moveDir = Dir.R →
      (q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 38 ∨ (q : ℕ) = 28 ∨ (q : ℕ) = 77 ∨ (q : ℕ) = 9 ∨
        (q : ℕ) = 12 ∨ (q : ℕ) = 11 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81 ∨ (q : ℕ) = 85 ∨ (q : ℕ) = 20 ∨
        (q : ℕ) = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
    native_decide
  exact hb ⟨q, hq⟩ m r hr hd

/-- 读 boundary 且 L 的转移：q ∈ Lset。 -/
lemma q10h_boundary_L (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hs : s.1 = SymKind.boundary) (hr : r ∈ VerifierSym.transition (q, s)) (hd : r.moveDir = Dir.L) :
    q = 3 ∨ q = 26 ∨ q = 5 ∨ q = 10 ∨ q = 76 ∨ q = 8 ∨ q = 84 ∨ q = 22 ∨ q = 13 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary → r.moveDir = Dir.L →
      (q : ℕ) = 3 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 5 ∨ (q : ℕ) = 10 ∨ (q : ℕ) = 76 ∨
        (q : ℕ) = 8 ∨ (q : ℕ) = 84 ∨ (q : ℕ) = 22 ∨ (q : ℕ) = 13 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hs hd

/-- 吸收态只 S 自环。 -/
lemma q10h_absorb_S (q : ℕ) (hq : q = 100 ∨ q = 101) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) : r.moveDir = Dir.S ∧ r.nextState = q := by
  rcases hq with rfl | rfl <;>
  have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (100, s) →
      r.moveDir = Dir.S ∧ r.nextState = 100 := by
    native_decide
  · exact hb s r hr
  · have hb' : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (101, s) →
        r.moveDir = Dir.S ∧ r.nextState = 101 := by
      native_decide
    exact hb' s r hr

/-- 读 boundary 的写值：非 boundary 写必为 q = 20。 -/
lemma q10h_boundary_write (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hs : s.1 = SymKind.boundary) (hr : r ∈ VerifierSym.transition (q, s))
    (hb : (r.writeSym).1 = SymKind.boundary) (hne : r.writeSym ≠ s) : q = 51 ∨ q = 3 := by
  have hb' : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary →
      (r.writeSym).1 = SymKind.boundary → r.writeSym ≠ s → (q : ℕ) = 51 ∨ (q : ℕ) = 3 := by
    native_decide
  exact hb' ⟨q, hq⟩ s r hr hs hb hne

/-- 相位 1 闭包：nextState ∈ {0,1,2,3} ⟹ q ∈ {0,1,2,3}。 -/
lemma q10h_phase1_closure (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hn : r.nextState = 0 ∨ r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 3) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      r.nextState = 0 ∨ r.nextState = 1 ∨ r.nextState = 2 ∨ r.nextState = 3 →
      (q : ℕ) = 0 ∨ (q : ℕ) = 1 ∨ (q : ℕ) = 2 ∨ (q : ℕ) = 3 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hn

/-- 格式检查相位闭包：nextState ∈ {24,29,26} ⟹ q ∈ {24,29,26,3}。 -/
lemma q10h_fmt_closure (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hn : r.nextState = 24 ∨ r.nextState = 29 ∨ r.nextState = 26) :
    q = 24 ∨ q = 29 ∨ q = 26 ∨ q = 3 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      r.nextState = 24 ∨ r.nextState = 29 ∨ r.nextState = 26 →
      (q : ℕ) = 24 ∨ (q : ℕ) = 29 ∨ (q : ℕ) = 26 ∨ (q : ℕ) = 3 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hn

/-- SE 状态集（相位 4+ 需要元素非空的状态）。 -/
def q10h_SE : Finset ℕ := {5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100, 4}

set_option maxRecDepth 100000 in
/-- SE 闭包：nextState ∈ SE ⟹ q ∈ SE ∨ q=4@sel/nosel ∨ q=24@data1。 -/
lemma q10h_SE_closure (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hn : r.nextState ∈ q10h_SE) :
    q ∈ q10h_SE ∨ (q = 4 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel)) ∨
      (q = 24 ∧ s.1 = SymKind.data1) := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → r.nextState ∈ q10h_SE →
      (q : ℕ) ∈ q10h_SE ∨ ((q : ℕ) = 4 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel)) ∨
        ((q : ℕ) = 24 ∧ s.1 = SymKind.data1) := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hn

/-- SUB 闭包：nextState ∈ SUB ⟹ q ∈ SUB ∨ q = 5。 -/
lemma q10h_SUB_closure (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s))
    (hn : r.nextState = 76 ∨ r.nextState = 77 ∨ r.nextState = 8 ∨ r.nextState = 9 ∨
      r.nextState = 10 ∨ r.nextState = 11 ∨ r.nextState = 12 ∨ r.nextState = 14 ∨
      r.nextState = 81 ∨ r.nextState = 13) :
    q = 76 ∨ q = 77 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 14 ∨
    q = 81 ∨ q = 13 ∨ q = 5 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      r.nextState = 76 ∨ r.nextState = 77 ∨ r.nextState = 8 ∨ r.nextState = 9 ∨
      r.nextState = 10 ∨ r.nextState = 11 ∨ r.nextState = 12 ∨ r.nextState = 14 ∨
      r.nextState = 81 ∨ r.nextState = 13 →
      (q : ℕ) = 76 ∨ (q : ℕ) = 77 ∨ (q : ℕ) = 8 ∨ (q : ℕ) = 9 ∨ (q : ℕ) = 10 ∨
      (q : ℕ) = 11 ∨ (q : ℕ) = 12 ∨ (q : ℕ) = 14 ∨ (q : ℕ) = 81 ∨ (q : ℕ) = 13 ∨ (q : ℕ) = 5 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hn

/-- 写值分类：数据/consumed 写 / 回写 / 特殊写状态。 -/
lemma q10h_write_kind (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    (r.writeSym).1 = SymKind.data0 ∨ (r.writeSym).1 = SymKind.data1 ∨
    (r.writeSym).1 = SymKind.consumed ∨ r.writeSym = s ∨
    q = 2 ∨ q = 51 ∨ q = 3 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      (r.writeSym).1 = SymKind.data0 ∨ (r.writeSym).1 = SymKind.data1 ∨
      (r.writeSym).1 = SymKind.consumed ∨ r.writeSym = s ∨
      (q : ℕ) = 2 ∨ (q : ℕ) = 51 ∨ (q : ℕ) = 3 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr

/-- sel/nosel/alpha 写必为回写或 q = 2。 -/
lemma q10h_write_sel (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    (r.writeSym).1 = SymKind.sel ∨ (r.writeSym).1 = SymKind.nosel ∨ (r.writeSym).1 = SymKind.alpha →
    r.writeSym = s ∨ q = 2 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      (r.writeSym).1 = SymKind.sel ∨ (r.writeSym).1 = SymKind.nosel ∨ (r.writeSym).1 = SymKind.alpha →
      r.writeSym = s ∨ (q : ℕ) = 2 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr

/-- consumed 写必为回写或 q = 5。 -/
lemma q10h_write_consumed (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) :
    (r.writeSym).1 = SymKind.consumed → s.1 = SymKind.consumed ∨ q = 5 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) →
      (r.writeSym).1 = SymKind.consumed → s.1 = SymKind.consumed ∨ (q : ℕ) = 5 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr

/-- 读 boundary 的写值恒为 boundary（除 q = 20）。 -/
lemma q10h_boundary_write2 (q : ℕ) (hq : q < 102) (s : Sym) (r : SymTransResult)
    (hs : s.1 = SymKind.boundary) (hr : r ∈ VerifierSym.transition (q, s)) :
    (r.writeSym).1 = SymKind.boundary ∨ q = 20 := by
  have hb : ∀ q : Fin 102, ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), s) → s.1 = SymKind.boundary →
      (r.writeSym).1 = SymKind.boundary ∨ (q : ℕ) = 20 := by
    native_decide
  exact hb ⟨q, hq⟩ s r hr hs

-- ======================================================================
-- q10 ③ 素材:步数分析表级分类(并行线 A,2026-09-07)
-- S 步 = 流程停驻点:非吸收态的 S 步全为状态改变(无自环、不达 100),
-- 100/101 的 S 步为吸收自环。路径长度 = 移动段 + S 步,S 步是段边界。
-- =======================================================================

/-- 非吸收态 S 步的 nextState 分类(无自环、无 100;S 步 = 流程里程碑:
    2→3 停 #₁、10→11 标 m、13→5 回扫、86→87 停、87→20 占位、21→22 判定)。 -/
lemma q10h_S_step_nextState (q : ℕ) (hq : q < 102) (hq100 : q ≠ 100) (hq101 : q ≠ 101)
    (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (q, s))
    (hs : r.moveDir = Dir.S) :
    r.nextState = 3 ∨ r.nextState = 11 ∨ r.nextState = 5 ∨ r.nextState = 87 ∨
    r.nextState = 20 ∨ r.nextState = 22 ∨ r.nextState = 101 := by
  have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → (q : ℕ) ≠ 101 → ∀ s : Sym,
      ∀ r : SymTransResult, r ∈ VerifierSym.transition ((q : ℕ), s) →
      r.moveDir = Dir.S →
      r.nextState = 3 ∨ r.nextState = 11 ∨ r.nextState = 5 ∨ r.nextState = 87 ∨
      r.nextState = 20 ∨ r.nextState = 22 ∨ r.nextState = 101 := by
    native_decide
  exact hb ⟨q, hq⟩ hq100 hq101 s r hr hs

/-- 非吸收态 S 步非自环:同态连续 S 不可能(每次 S 必离开当前态)。 -/
lemma q10h_S_step_not_self (q : ℕ) (hq : q < 102) (hq100 : q ≠ 100) (hq101 : q ≠ 101)
    (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (q, s))
    (hs : r.moveDir = Dir.S) : r.nextState ≠ q := by
  have hb : ∀ q : Fin 102, (q : ℕ) ≠ 100 → (q : ℕ) ≠ 101 → ∀ s : Sym,
      ∀ r : SymTransResult, r ∈ VerifierSym.transition ((q : ℕ), s) →
      r.moveDir = Dir.S → r.nextState ≠ (q : ℕ) := by
    native_decide
  exact hb ⟨q, hq⟩ hq100 hq101 s r hr hs

/-- 100 吸收自环:100 的 S 步留在 100。 -/
lemma q10h_100_S_self (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (100, s))
    (hs : r.moveDir = Dir.S) : r.nextState = 100 := by
  have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (100, s) →
      r.moveDir = Dir.S → r.nextState = 100 := by
    native_decide
  exact hb s r hr hs

/-- 101 吸收自环:101 的 S 步留在 101。 -/
lemma q10h_101_S_self (s : Sym) (r : SymTransResult) (hr : r ∈ VerifierSym.transition (101, s))
    (hs : r.moveDir = Dir.S) : r.nextState = 101 := by
  have hb : ∀ s : Sym, ∀ r : SymTransResult, r ∈ VerifierSym.transition (101, s) →
      r.moveDir = Dir.S → r.nextState = 101 := by
    native_decide
  exact hb s r hr hs

-- ==============================================================================
-- q10 ③ 素材(并行线 A,第 2 批):步数结构引理(SymSteps 级,纯结构)
-- 头位移恒等式:cfg.headPos = cfg₀.headPos + Σ(dir);同向段长 = 位置差。
-- ==============================================================================

/-- 头位移恒等式:SymSteps 路径的终点头 = 起点头 + 全步 dir 之和。 -/
lemma symSteps_headPos_sum (M : ℕ × Sym → Finset SymTransResult) (cfg₀ : SymConfig)
    {π : List SymStep} {cfg : SymConfig} (h : SymSteps M cfg₀ π cfg) :
    cfg.headPos = cfg₀.headPos + (π.map (fun st => st.result.moveDir.toInt)).sum := by
  induction h with
  | nil => simp
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      simp [symStepConfig, List.map_append, List.sum_append]
      rw [ih]
      ring

/-- 全 R 段:终点头 = 起点头 + 段长(每步 +1,无 S/L)。 -/
lemma symSteps_allR_headPos (M : ℕ × Sym → Finset SymTransResult) (cfg₀ : SymConfig)
    {π : List SymStep} {cfg : SymConfig} (h : SymSteps M cfg₀ π cfg)
    (hR : ∀ st ∈ π, st.result.moveDir = Dir.R) :
    cfg.headPos = cfg₀.headPos + π.length := by
  rw [symSteps_headPos_sum M cfg₀ h]
  have hmap : (π.map (fun st => st.result.moveDir.toInt)).sum = π.length := by
    have hmap' : π.map (fun st => st.result.moveDir.toInt) = π.map (fun _ : SymStep => 1) := by
      apply List.map_congr_left
      intro st hst
      rw [hR st hst]
      rfl
    rw [hmap']
    simp [List.map_const, List.sum_replicate]
  rw [hmap]

/-- 全 L 段:终点头 = 起点头 - 段长(每步 -1,无 S/R)。 -/
lemma symSteps_allL_headPos (M : ℕ × Sym → Finset SymTransResult) (cfg₀ : SymConfig)
    {π : List SymStep} {cfg : SymConfig} (h : SymSteps M cfg₀ π cfg)
    (hL : ∀ st ∈ π, st.result.moveDir = Dir.L) :
    cfg.headPos = cfg₀.headPos - π.length := by
  rw [symSteps_headPos_sum M cfg₀ h]
  have hmap : (π.map (fun st => st.result.moveDir.toInt)).sum = -π.length := by
    have hmap' : π.map (fun st => st.result.moveDir.toInt) = π.map (fun _ : SymStep => -1) := by
      apply List.map_congr_left
      intro st hst
      rw [hL st hst]
      rfl
    rw [hmap']
    simp [List.map_const, List.sum_replicate]
  rw [hmap]
  omega
end Mp
