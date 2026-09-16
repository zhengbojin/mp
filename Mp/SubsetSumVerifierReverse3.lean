/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierState
import Mp.SubsetSumVerifierReverse2
import Mp.SubsetSumVerifierCoreA
import Mp.SubsetSumVerifierTop

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
set_option linter.style.emptyLine false


set_option maxHeartbeats 8000000

namespace Mp
open CBTM

/-- 元素区前缀长度：前 n 个元素（每元素 [标记] ++ 原生位串）的总格子数。 -/
def elemsPrefixLen (elems : List ℕ) (n : ℕ) : ℕ :=
  ((elems.take n).map (fun v => 1 + (encodeBitsSymNative v).length)).sum


lemma elemsPrefixLen_zero (elems : List ℕ) : elemsPrefixLen elems 0 = 0 := by
  simp [elemsPrefixLen]

lemma elemsPrefixLen_succ (elems : List ℕ) (n : ℕ) (hn : n < elems.length) :
    elemsPrefixLen elems (n + 1) =
      elemsPrefixLen elems n + 1 + (encodeBitsSymNative (elems[n])).length := by
  induction elems generalizing n with
  | nil => simp at hn
  | cons v vs ih =>
      cases n with
      | zero =>
          simp [elemsPrefixLen]
      | succ n =>
          have hn' : n < vs.length := by
            simp at hn
            omega
          have h := ih n hn'
          simp [elemsPrefixLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h ⊢
          omega

lemma elemsPrefixLen_le_len (elems : List ℕ) (n : ℕ) :
    elemsPrefixLen elems n ≤ (encodeElementsSym elems).length := by
  unfold elemsPrefixLen
  let f : ℕ → ℕ := fun v => 1 + (encodeBitsSymNative v).length
  have hsplit : (elems.take n).map f ++ (elems.drop n).map f = elems.map f := by
    rw [← List.map_append]
    rw [List.take_append_drop]
  have hsum : ((elems.take n).map f).sum + ((elems.drop n).map f).sum = (elems.map f).sum := by
    rw [← List.sum_append, hsplit]
  have hle : ((elems.take n).map f).sum ≤ (elems.map f).sum := by
    omega
  have hlen : (elems.map f).sum = (encodeElementsSym elems).length := by
    clear hsplit hsum hle
    induction elems with
    | nil => simp [encodeElementsSym, f]
    | cons v vs ih =>
        cases vs with
        | nil => simp [encodeElementsSym, f, Nat.add_comm]
        | cons w rest =>
            calc
              ((v :: w :: rest).map f).sum = f v + ((w :: rest).map f).sum := by
                simp [List.map_cons, List.sum_cons]
              _ = f v + (encodeElementsSym (w :: rest)).length := by
                rw [ih]
              _ = (1 + (encodeBitsSymNative v).length) + (encodeElementsSym (w :: rest)).length := by
                simp [f]
              _ = (encodeElementsSym (v :: w :: rest)).length := by
                rw [show encodeElementsSym (v :: w :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest) from by
                  simp only [encodeElementsSym]]
                rw [List.length_append, List.length_append]
                simp [List.length_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [f] using (hle.trans (by rw [hlen]))

/-- 前缀长度移位：cons 头元素后，n+1 前缀 = 头块长 + 尾部 n 前缀。 -/
lemma elemsPrefixLen_cons_shift (v : ℕ) (vs : List ℕ) (n : ℕ) :
    elemsPrefixLen (v :: vs) (n + 1) = 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n := by
  unfold elemsPrefixLen
  rw [List.take_succ_cons]
  simp only [List.map_cons, List.sum_cons]

/-- 前缀长度严格小于全长（元素存在时）。 -/
lemma elemsPrefixLen_lt_len (elems : List ℕ) (n : ℕ) (hn : n < elems.length) :
    elemsPrefixLen elems n < (encodeElementsSym elems).length := by
  have hsucc := elemsPrefixLen_succ elems n hn
  have hle2 := elemsPrefixLen_le_len elems (n + 1)
  rw [hsucc] at hle2
  omega

/-- 前缀右端严格小于全长（下一元素存在时）。 -/
lemma elemsPrefixLen_lt_len_of_lt (elems : List ℕ) (n : ℕ) (hn : n + 1 < elems.length) :
    elemsPrefixLen elems (n + 1) < (encodeElementsSym elems).length := by
  have hsucc := elemsPrefixLen_succ elems (n + 1) (by omega)
  have hle2 := elemsPrefixLen_le_len elems (n + 2)
  have hlt : elemsPrefixLen elems (n + 1) < elemsPrefixLen elems (n + 1) + 1 + (encodeBitsSymNative (elems[n + 1])).length := by
    omega
  have hle3 : elemsPrefixLen elems (n + 1) + 1 + (encodeBitsSymNative (elems[n + 1])).length = elemsPrefixLen elems (n + 2) := hsucc.symm
  rw [hle3] at hlt
  exact lt_of_lt_of_le hlt hle2

/-- 前缀和取满元素数 = 全长。 -/
lemma elemsPrefixLen_eq_len_of_eq (elems : List ℕ) (n : ℕ) (hn : n = elems.length) :
    elemsPrefixLen elems n = (encodeElementsSym elems).length := by
  subst n
  have htake : elems.take elems.length = elems := List.take_length
  rw [elemsPrefixLen, htake]
  let f : ℕ → ℕ := fun v => 1 + (encodeBitsSymNative v).length
  clear htake
  induction elems with
  | nil => rfl
  | cons v vs ih =>
      cases vs with
      | nil => simp [encodeElementsSym, f, Nat.add_comm]
      | cons w rest =>
          calc
            ((v :: w :: rest).map (fun v => 1 + (encodeBitsSymNative v).length)).sum =
                (1 + (encodeBitsSymNative v).length) + ((w :: rest).map (fun v => 1 + (encodeBitsSymNative v).length)).sum := by
              simp
            _ = (1 + (encodeBitsSymNative v).length) + (encodeElementsSym (w :: rest)).length := by
              rw [ih]
            _ = (encodeElementsSym (v :: w :: rest)).length := by
              rw [show encodeElementsSym (v :: w :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest) from by
                simp only [encodeElementsSym]]
              rw [List.length_append, List.length_append]
              simp [List.length_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 原串符号的 kind ∈ {alpha, beta, data0, data1}。 -/
lemma encodeElementsSym_kind_range (elems : List ℕ) :
    ∀ s ∈ encodeElementsSym elems,
      s.1 = SymKind.alpha ∨ s.1 = SymKind.beta ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  induction elems with
  | nil => simp [encodeElementsSym] at hs
  | cons v vs ih =>
      cases vs with
      | nil =>
          rw [show encodeElementsSym (v :: []) = [Sym.alpha] ++ encodeBitsSymNative v from by
            simp only [encodeElementsSym]] at hs
          rw [List.mem_append] at hs
          rcases hs with h | h
          · simp at h
            subst h
            left; rfl
          · have hk := encodeBitsSymNative_kind v s h
            rcases hk with hk | hk
            · right; right; left; exact hk
            · right; right; right; exact hk
      | cons w rest =>
          have hget : encodeElementsSym (v :: w :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest) := by
            simp only [encodeElementsSym]
          rw [hget] at hs
          rw [List.mem_append] at hs
          rcases hs with h | h
          · rw [List.mem_append] at h
            rcases h with h | h
            · simp at h
              subst h
              left; rfl
            · have hk := encodeBitsSymNative_kind v s h
              rcases hk with hk | hk
              · right; right; left; exact hk
              · right; right; right; exact hk
          · exact ih h

/-- data 位处 WithSel 串 = 原串（非标记格不变换）。 -/
lemma encodeElementsSymWithSel_cell_of_data (elems : List ℕ) (sel : List Bool)
    (hsel : sel.length = elems.length) (i : ℕ) (hi : i < (encodeElementsSym elems).length)
    (hk : ((encodeElementsSym elems)[i]'hi).1 = SymKind.data0 ∨ ((encodeElementsSym elems)[i]'hi).1 = SymKind.data1) :
    (encodeElementsSymWithSel elems sel)[i]'(by
      rw [WithSel_length elems sel hsel]
      exact hi) = (encodeElementsSym elems)[i]'hi := by
  induction elems generalizing sel i with
  | nil =>
      exfalso
      have hi' : i < ([] : List Sym).length := by
        simpa only [encodeElementsSym] using hi
      simp at hi'
  | cons v vs ih =>
      cases sel with
      | nil => simp at hsel
      | cons b sel' =>
          have hsel' : sel'.length = vs.length := by simp at hsel; omega
          cases vs with
          | nil =>
              have hsel'' : sel' = [] := List.eq_nil_of_length_eq_zero hsel'
              subst sel'
              by_cases hi0 : i = 0
              · subst i
                exfalso
                have hb : ((encodeElementsSym [v])[0]'(by simp [encodeElementsSym])).1 = SymKind.alpha := by
                  simp [encodeElementsSym]
                  rfl
                rcases hk with hk | hk <;> cases (hk.symm.trans hb)
              · have hget : (encodeElementsSym [v])[i]'(by simpa [encodeElementsSym] using hi) =
                    (encodeBitsSymNative v)[i - 1]'(by
                      have hi'' : i ≤ (encodeBitsSymNative v).length := by
                        simpa [encodeElementsSym] using hi
                      omega) := by
                  simp only [show encodeElementsSym [v] = [Sym.alpha] ++ encodeBitsSymNative v from by
                    simp only [encodeElementsSym]]
                  rw [List.getElem_append_right (by omega : 1 ≤ i)]
                  rfl
                have hgetws : (encodeElementsSymWithSel [v] [b])[i]'(by
                    rw [WithSel_length [v] [b] hsel]
                    simpa [encodeElementsSym] using hi) =
                    (encodeBitsSymNative v)[i - 1]'(by
                      have hi'' : i ≤ (encodeBitsSymNative v).length := by
                        simpa [encodeElementsSym] using hi
                      omega) := by
                  simp only [show encodeElementsSymWithSel [v] [b] = [if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v from by
                    rw [encodeElementsSymWithSel]
                    simp [joinLists]]
                  rw [List.getElem_append_right (by omega : 1 ≤ i)]
                  rfl
                rw [hget, hgetws]
          | cons w rest =>
              by_cases hi0 : i = 0
              · subst i
                exfalso
                have ha : ((encodeElementsSym (v :: w :: rest))[0]'(by
                    simp [encodeElementsSym, List.length_append])).1 = SymKind.alpha := by
                  simp [encodeElementsSym]
                  rfl
                rcases hk with hk | hk <;> cases (hk.symm.trans ha)
              · by_cases hilt : i < 1 + (encodeBitsSymNative v).length
                · have hget : (encodeElementsSym (v :: w :: rest))[i]'(hi) =
                      (encodeBitsSymNative v)[i - 1]'(by omega) := by
                    change (([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest))[i]'(hi)) =
                      (encodeBitsSymNative v)[i - 1]'(by omega)
                    have hv₁ := List.getElem_append_right (as := [Sym.alpha])
                      (bs := encodeBitsSymNative v ++ encodeElementsSym (w :: rest)) (i := i) (by omega : 1 ≤ i) (h₂ := hi)
                    have hv₂ := List.getElem_append_left (as := encodeBitsSymNative v)
                      (bs := encodeElementsSym (w :: rest)) (i := i - 1) (by omega : i - 1 < (encodeBitsSymNative v).length)
                      (h' := by
                        have hlen : i < 1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by
                          simpa [encodeElementsSym, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
                        have hlt : i - 1 < (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by omega
                        simpa [List.length_append] using hlt)
                    exact (hv₁.trans hv₂)
                  have hgetws : (encodeElementsSymWithSel (v :: w :: rest) (b :: sel'))[i]'(by
                      rw [WithSel_length (v :: w :: rest) (b :: sel') hsel]
                      exact hi) =
                      (encodeBitsSymNative v)[i - 1]'(by omega) := by
                    change ((([if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v) ++ encodeElementsSymWithSel (w :: rest) sel')[i]'(by
                        rw [List.length_append, List.length_append, WithSel_length (w :: rest) sel' hsel']
                        simp
                        have hb : i < 1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by
                          simpa [encodeElementsSym, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
                        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)) =
                      (encodeBitsSymNative v)[i - 1]'(by omega)
                    have hv₁ := List.getElem_append_left (as := [if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v)
                      (bs := encodeElementsSymWithSel (w :: rest) sel') (i := i)
                      (by
                        rw [List.length_append]
                        simp
                        exact hilt)
                      (h' := by
                        rw [List.length_append, List.length_append, WithSel_length (w :: rest) sel' hsel']
                        simp
                        have hb : i < 1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by
                          simpa [encodeElementsSym, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
                        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)
                    have hv₂ := List.getElem_append_right (as := [if b then Sym.sel else Sym.nosel])
                      (bs := encodeBitsSymNative v) (i := i) (by omega : 1 ≤ i)
                      (h₂ := by
                        rw [List.length_append]
                        simp
                        exact hilt)
                    exact (hv₁.trans hv₂)
                  rw [hget]
                  exact hgetws
                · have hi' : i - (1 + (encodeBitsSymNative v).length) < (encodeElementsSym (w :: rest)).length := by
                    have hi₁ : i < 1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by
                      simpa [encodeElementsSym, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
                    omega
                  have hget0 : (encodeElementsSym (v :: w :: rest))[i]'hi = (encodeElementsSym (w :: rest))[i - (1 + (encodeBitsSymNative v).length)]'hi' := by
                    change ((([Sym.alpha] ++ encodeBitsSymNative v) ++ encodeElementsSym (w :: rest))[i]'(hi)) =
                      (encodeElementsSym (w :: rest))[i - (1 + (encodeBitsSymNative v).length)]'hi'
                    have hv := List.getElem_append_right (as := [Sym.alpha] ++ encodeBitsSymNative v)
                      (bs := encodeElementsSym (w :: rest)) (i := i)
                      (by
                        rw [List.length_append, List.length_singleton]
                        exact (by omega : 1 + (encodeBitsSymNative v).length ≤ i))
                      (h₂ := hi)
                    rw [hv]
                    simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
                  have hk' : ((encodeElementsSym (w :: rest))[i - (1 + (encodeBitsSymNative v).length)]'hi').1 = SymKind.data0 ∨
                      ((encodeElementsSym (w :: rest))[i - (1 + (encodeBitsSymNative v).length)]'hi').1 = SymKind.data1 := by
                    simpa [hget0] using hk
                  have h := ih sel' hsel' (i - (1 + (encodeBitsSymNative v).length)) hi' hk'
                  have hgetws : (encodeElementsSymWithSel (v :: w :: rest) (b :: sel'))[i]'(by
                      rw [WithSel_length (v :: w :: rest) (b :: sel') hsel]
                      exact hi) =
                      (encodeElementsSymWithSel (w :: rest) sel')[i - (1 + (encodeBitsSymNative v).length)]'(by
                        rw [WithSel_length (w :: rest) sel' hsel']
                        exact hi') := by
                    change ((([if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v) ++ encodeElementsSymWithSel (w :: rest) sel')[i]'(by
                        rw [List.length_append, List.length_append, WithSel_length (w :: rest) sel' hsel']
                        simp
                        have hb : i < 1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by
                          simpa [encodeElementsSym, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
                        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)) =
                      (encodeElementsSymWithSel (w :: rest) sel')[i - (1 + (encodeBitsSymNative v).length)]'(by
                        rw [WithSel_length (w :: rest) sel' hsel']
                        exact hi')
                    have hv := List.getElem_append_right (as := [if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v)
                      (bs := encodeElementsSymWithSel (w :: rest) sel') (i := i)
                      (by
                        rw [List.length_append, List.length_singleton]
                        exact (by omega : 1 + (encodeBitsSymNative v).length ≤ i))
                      (h₂ := by
                        rw [List.length_append, List.length_append, WithSel_length (w :: rest) sel' hsel']
                        simp
                        have hb : i < 1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: rest)).length := by
                          simpa [encodeElementsSym, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
                        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)
                    rw [hv]
                    simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
                  rw [hget0]
                  exact hgetws.trans h

/-- 原串在第 n 前缀右端（下一元素标记格）处的 kind 是 alpha 或 beta。 -/
lemma encodeElementsSym_kind_at_prefixEnd (elems : List ℕ) (n : ℕ) (hn : n + 1 < elems.length) :
    ((encodeElementsSym elems)[elemsPrefixLen elems (n + 1)]'(elemsPrefixLen_lt_len_of_lt elems n hn)).1 = SymKind.alpha ∨
      ((encodeElementsSym elems)[elemsPrefixLen elems (n + 1)]'(elemsPrefixLen_lt_len_of_lt elems n hn)).1 = SymKind.beta := by
  induction elems generalizing n with
  | nil => simp at hn
  | cons v vs ih =>
      cases n with
      | zero =>
          have hvs : vs ≠ [] := by
            intro h
            subst vs
            simp at hn
          rcases vs with _ | ⟨w, rest⟩
          · exfalso; exact hvs rfl
          · by_cases hrest : rest = []
            · subst rest
              have hget : (encodeElementsSym (v :: [w]))[1 + (encodeBitsSymNative v).length]'(by
                  change 1 + (encodeBitsSymNative v).length < ([Sym.alpha] ++ encodeBitsSymNative v ++ ([Sym.alpha] ++ encodeBitsSymNative w)).length
                  simp [List.length_append, List.length_singleton]
                  omega) = Sym.alpha := by
                simp only [show encodeElementsSym (v :: [w]) = [Sym.alpha] ++ encodeBitsSymNative v ++ ([Sym.alpha] ++ encodeBitsSymNative w) from by
                  simp only [encodeElementsSym]]
                rw [List.getElem_append_right (by
                  rw [List.length_append, List.length_singleton])]
                simp only [List.length_append, List.length_singleton, Nat.sub_self]
                rw [List.getElem_append_left (by simp)]
                rw [List.getElem_cons_zero]
              have hpos : 1 + (encodeBitsSymNative v).length = elemsPrefixLen (v :: [w]) (0 + 1) := by
                rw [elemsPrefixLen_succ (v :: [w]) 0 (by simp)]
                simp [elemsPrefixLen]
              simp only [← hpos]
              left
              simpa [Sym.alpha] using (congrArg (fun s : Sym => s.1) hget)
            · have hget : (encodeElementsSym (v :: w :: rest))[1 + (encodeBitsSymNative v).length]'(by
                  change 1 + (encodeBitsSymNative v).length < ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest)).length
                  simp [List.length_append, List.length_singleton]
                  cases rest <;> unfold encodeElementsSym <;> simp <;> omega) = Sym.alpha := by
                simp only [show encodeElementsSym (v :: w :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest) from by
                  simp only [encodeElementsSym]]
                rw [List.getElem_append_right (by
                  rw [List.length_append, List.length_singleton])]
                simp only [List.length_append, List.length_singleton, Nat.sub_self]
                simp only [show encodeElementsSym (w :: rest) = [Sym.alpha] ++ encodeBitsSymNative w ++ encodeElementsSym rest from by
                  cases rest with
                  | nil => contradiction
                  | cons x xs => simp only [encodeElementsSym]]
                rw [List.getElem_append_left (by
                  rw [List.length_append, List.length_singleton]
                  omega)]
                rw [List.getElem_append_left (by simp)]
                rw [List.getElem_cons_zero]
              have hpos : 1 + (encodeBitsSymNative v).length = elemsPrefixLen (v :: w :: rest) (0 + 1) := by
                rw [elemsPrefixLen_succ (v :: w :: rest) 0 (by simp)]
                simp [elemsPrefixLen]
              simp only [← hpos]
              left
              simpa [Sym.alpha] using (congrArg (fun s : Sym => s.1) hget)
      | succ n =>
          have hn' : n + 1 < vs.length := by simp at hn; omega
          have h := ih n hn'
          by_cases hvs : vs = []
          · subst vs
            simp at hn
          · rcases vs with _ | ⟨w, rest⟩
            · exfalso; exact hvs rfl
            · have hlenidx : 1 + (encodeBitsSymNative v).length + elemsPrefixLen (w :: rest) (n + 1) < (encodeElementsSym (v :: w :: rest)).length := by
                have hlt := elemsPrefixLen_lt_len_of_lt (w :: rest) n (by omega)
                change 1 + (encodeBitsSymNative v).length + elemsPrefixLen (w :: rest) (n + 1) <
                  ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest)).length
                simp [List.length_append, List.length_singleton]
                omega
              have hget : (encodeElementsSym (v :: w :: rest))[1 + (encodeBitsSymNative v).length + elemsPrefixLen (w :: rest) (n + 1)]'hlenidx =
                      (encodeElementsSym (w :: rest))[elemsPrefixLen (w :: rest) (n + 1)]'(elemsPrefixLen_lt_len_of_lt (w :: rest) n hn') := by
                simp only [show encodeElementsSym (v :: w :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest) from by
                  simp only [encodeElementsSym]]
                rw [List.getElem_append_right (by
                  rw [List.length_append, List.length_singleton]
                  omega)]
                congr 1
                rw [List.length_append, List.length_singleton]
                omega
              have hpos : 1 + (encodeBitsSymNative v).length + elemsPrefixLen (w :: rest) (n + 1) = elemsPrefixLen (v :: w :: rest) (n + 1 + 1) :=
                elemsPrefixLen_cons_shift v (w :: rest) (n + 1)
              have hk : ((encodeElementsSym (v :: w :: rest))[elemsPrefixLen (v :: w :: rest) (n + 1 + 1)]'(elemsPrefixLen_lt_len_of_lt (v :: w :: rest) (n + 1) (by omega))).1 = SymKind.alpha ∨
                  ((encodeElementsSym (v :: w :: rest))[elemsPrefixLen (v :: w :: rest) (n + 1 + 1)]'(elemsPrefixLen_lt_len_of_lt (v :: w :: rest) (n + 1) (by omega))).1 = SymKind.beta := by
                rw [← hget] at h
                simp only [hpos.symm]
                exact h
              exact hk

/-- WithSel 串在左界(n)（元素 n 的标记格）处的值 = sel[n] 标记。 -/
lemma encodeElementsSymWithSel_mark_val (elems : List ℕ) (sel : List Bool)
    (hsel : sel.length = elems.length) (n : ℕ) (hn : n < elems.length) :
    (encodeElementsSymWithSel elems sel)[elemsPrefixLen elems n]'(by
      have h := elemsPrefixLen_lt_len elems n hn
      rw [← WithSel_length elems sel hsel] at h
      exact h) = (if sel[n]'(by rw [hsel]; exact hn) then Sym.sel else Sym.nosel) := by
  induction elems generalizing sel n with
  | nil => simp at hn
  | cons v vs ih =>
      cases sel with
      | nil => simp at hsel
      | cons b sel' =>
          have hsel' : sel'.length = vs.length := by simp at hsel; omega
          cases n with
          | zero =>
              have hget : (encodeElementsSymWithSel (v :: vs) (b :: sel'))[0]'(by
                  rw [WithSel_length (v :: vs) (b :: sel') hsel]
                  cases vs <;> simp only [encodeElementsSym, List.length_append, List.length_singleton] <;> omega) = (if b then Sym.sel else Sym.nosel) := by
                simp only [encodeElementsSymWithSel, List.zip_cons_cons, List.map_cons, joinLists_cons]
                change ((if b then Sym.sel else Sym.nosel) :: encodeBitsSymNative v)[0] = if b then Sym.sel else Sym.nosel
                rfl
              have hpos : 0 = elemsPrefixLen (v :: vs) 0 := by simp [elemsPrefixLen]
              simp only [hpos.symm]
              rw [hget]
              rw [List.getElem_cons_zero]
          | succ n =>
              have hn' : n < vs.length := by simp at hn; omega
              have h := ih sel' hsel' n hn'
              have hidx_tail : elemsPrefixLen vs n < (encodeElementsSymWithSel vs sel').length := by
                have h' := elemsPrefixLen_lt_len vs n hn'
                rw [← WithSel_length vs sel' hsel'] at h'
                exact h'
              have hidx_head : 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n < (encodeElementsSymWithSel (v :: vs) (b :: sel')).length := by
                rw [WithSel_length (v :: vs) (b :: sel') hsel]
                have hlen : (encodeElementsSym (v :: vs)).length = 1 + (encodeBitsSymNative v).length + (encodeElementsSym vs).length := by
                  cases vs <;> simp [encodeElementsSym] <;> omega
                rw [hlen]
                exact Nat.add_lt_add_left (elemsPrefixLen_lt_len vs n hn') _
              have hget : (encodeElementsSymWithSel (v :: vs) (b :: sel'))[1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n]'hidx_head =
                      (encodeElementsSymWithSel vs sel')[elemsPrefixLen vs n]'hidx_tail := by
                simp only [encodeElementsSymWithSel, List.zip_cons_cons, List.map_cons, joinLists_cons]
                rw [List.getElem_append_right (show ([if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v).length ≤ 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n from by
                  rw [List.length_append, List.length_singleton]
                  omega)]
                congr 1
                rw [List.length_append, List.length_singleton]
                omega
              have hpos : 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n = elemsPrefixLen (v :: vs) (n + 1) :=
                elemsPrefixLen_cons_shift v vs n
              simp only [hpos.symm]
              rw [List.getElem_cons_succ]
              exact hget.trans h

/-- sel 在 n 处 set 后，前左界(n) 格的值不变。 -/
lemma encodeElementsSymWithSel_set_eq_of_lt (elems : List ℕ) (sel : List Bool)
    (hsel : sel.length = elems.length) (n : ℕ) (b : Bool) (j : ℕ) (hj : j < elemsPrefixLen elems n) :
    (encodeElementsSymWithSel elems (sel.set n b))[j]'(by
      have hsetlen : (sel.set n b).length = elems.length := by rw [List.length_set, hsel]
      have hlen := WithSel_length elems (sel.set n b) hsetlen
      have hle := elemsPrefixLen_le_len elems n
      rw [← hlen] at hle
      exact Nat.lt_of_lt_of_le hj hle) = (encodeElementsSymWithSel elems sel)[j]'(by
      have hlen := WithSel_length elems sel hsel
      have hle := elemsPrefixLen_le_len elems n
      rw [← hlen] at hle
      exact Nat.lt_of_lt_of_le hj hle) := by
  induction elems generalizing sel n j with
  | nil => simp [elemsPrefixLen] at hj
  | cons v vs ih =>
      cases sel with
      | nil => simp at hsel
      | cons s sel' =>
          have hsel' : sel'.length = vs.length := by simp at hsel; omega
          cases n with
          | zero => simp [elemsPrefixLen] at hj
          | succ n =>
              have hshift : elemsPrefixLen (v :: vs) (n + 1) = 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n :=
                elemsPrefixLen_cons_shift v vs n
              have hj2 : j < 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n := by
                simpa [hshift] using hj
              have hsetlen : ((s :: sel').set (n + 1) b).length = (v :: vs).length := by
                rw [List.length_set, hsel]
              have hidx_set : j < (encodeElementsSymWithSel (v :: vs) ((s :: sel').set (n + 1) b)).length := by
                rw [WithSel_length (v :: vs) ((s :: sel').set (n + 1) b) hsetlen]
                have hle := elemsPrefixLen_le_len (v :: vs) (n + 1)
                exact Nat.lt_of_lt_of_le hj hle
              have hidx_sel : j < (encodeElementsSymWithSel (v :: vs) (s :: sel')).length := by
                rw [WithSel_length (v :: vs) (s :: sel') hsel]
                have hle := elemsPrefixLen_le_len (v :: vs) (n + 1)
                exact Nat.lt_of_lt_of_le hj hle
              have hget1 : (encodeElementsSymWithSel (v :: vs) ((s :: sel').set (n + 1) b))[j]'hidx_set =
                    (if hjv_in : j < 1 + (encodeBitsSymNative v).length then
                      ([if s then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v)[j]'(by
                        rw [List.length_append, List.length_singleton]
                        exact hjv_in)
                    else (encodeElementsSymWithSel vs (sel'.set n b))[j - (1 + (encodeBitsSymNative v).length)]'(by
                      rw [WithSel_length vs (sel'.set n b) (by rw [List.length_set, hsel'])]
                      have hshift := elemsPrefixLen_cons_shift v vs n
                      have hj2 : j < 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n := by
                        simpa [hshift] using hj
                      have hle := elemsPrefixLen_le_len vs n
                      omega)) := by
                simp only [encodeElementsSymWithSel, List.zip_cons_cons, List.map_cons, joinLists_cons, List.set_cons_succ]
                by_cases hjv : j < 1 + (encodeBitsSymNative v).length
                · rw [List.getElem_append_left (by
                    rw [List.length_append, List.length_singleton]
                    omega)]
                  rw [dif_pos hjv]
                · rw [List.getElem_append_right (show ([if s then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v).length ≤ j from by
                    rw [List.length_append, List.length_singleton]
                    omega)]
                  rw [dif_neg hjv]
                  congr 1
                  rw [List.length_append, List.length_singleton]
              have hget2 : (encodeElementsSymWithSel (v :: vs) (s :: sel'))[j]'hidx_sel =
                    (if hjv_in : j < 1 + (encodeBitsSymNative v).length then
                      ([if s then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v)[j]'(by
                        rw [List.length_append, List.length_singleton]
                        exact hjv_in)
                    else (encodeElementsSymWithSel vs sel')[j - (1 + (encodeBitsSymNative v).length)]'(by
                      rw [WithSel_length vs sel' hsel']
                      have hshift := elemsPrefixLen_cons_shift v vs n
                      have hj2 : j < 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n := by
                        simpa [hshift] using hj
                      have hle := elemsPrefixLen_le_len vs n
                      omega)) := by
                simp only [encodeElementsSymWithSel, List.zip_cons_cons, List.map_cons, joinLists_cons]
                by_cases hjv : j < 1 + (encodeBitsSymNative v).length
                · rw [List.getElem_append_left (by
                    rw [List.length_append, List.length_singleton]
                    omega)]
                  rw [dif_pos hjv]
                · rw [List.getElem_append_right (show ([if s then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v).length ≤ j from by
                    rw [List.length_append, List.length_singleton]
                    omega)]
                  rw [dif_neg hjv]
                  congr 1
                  rw [List.length_append, List.length_singleton]
              rw [hget1, hget2]
              by_cases hjv : j < 1 + (encodeBitsSymNative v).length
              · simp [hjv]
              · simp [hjv]
                have hj' : j - (1 + (encodeBitsSymNative v).length) < elemsPrefixLen vs n := by omega
                exact ih sel' hsel' n (j - (1 + (encodeBitsSymNative v).length)) hj'

/-- 区间（左界(n), 左界(n+1)）内是元素 n 的原生 data 位。 -/
lemma encodeElementsSym_kind_data_of_prefixRange (elems : List ℕ) (n : ℕ) (i : ℕ)
    (h1 : elemsPrefixLen elems n < i) (h2 : i < elemsPrefixLen elems (n + 1)) (hn : n < elems.length) :
    ((encodeElementsSym elems)[i]'(by
      have h := elemsPrefixLen_le_len elems (n + 1)
      exact Nat.lt_of_lt_of_le h2 h)).1 = SymKind.data0 ∨
    ((encodeElementsSym elems)[i]'(by
      have h := elemsPrefixLen_le_len elems (n + 1)
      exact Nat.lt_of_lt_of_le h2 h)).1 = SymKind.data1 := by
  induction elems generalizing n i with
  | nil => simp at hn
  | cons v vs ih =>
      cases n with
      | zero =>
          have h0 : 0 < i := by omega
          have hget : (encodeElementsSym (v :: vs))[i]'(by
              have h := elemsPrefixLen_le_len (v :: vs) 1
              exact Nat.lt_of_lt_of_le h2 h) =
              (encodeBitsSymNative v)[i - 1]'(by
                have hc := elemsPrefixLen_cons_shift v vs 0
                have h2r : i < 1 + (encodeBitsSymNative v).length := by
                  simpa [hc, elemsPrefixLen] using h2
                omega) := by
            cases vs with
            | nil =>
                have h2z : i < 1 + (encodeBitsSymNative v).length := by
                  have hc := elemsPrefixLen_cons_shift v [] 0
                  simpa [hc, elemsPrefixLen] using h2
                change (([Sym.alpha] ++ encodeBitsSymNative v)[i]'(by
                    have h := elemsPrefixLen_le_len (v :: []) 1
                    exact Nat.lt_of_lt_of_le h2 h)) = (encodeBitsSymNative v)[i - 1]'(by omega)
                have hv := List.getElem_append_right (as := [Sym.alpha])
                  (bs := encodeBitsSymNative v) (i := i) (by omega : 1 ≤ i)
                  (h₂ := by
                    rw [List.length_append]
                    simp
                    exact h2z)
                exact hv
            | cons w rest =>
                have h2z : i < 1 + (encodeBitsSymNative v).length := by
                  have hc := elemsPrefixLen_cons_shift v (w :: rest) 0
                  simpa [hc, elemsPrefixLen] using h2
                change ((([Sym.alpha] ++ encodeBitsSymNative v) ++ encodeElementsSym (w :: rest))[i]'(by
                    have h := elemsPrefixLen_le_len (v :: w :: rest) 1
                    exact Nat.lt_of_lt_of_le h2 h)) = (encodeBitsSymNative v)[i - 1]'(by omega)
                have hv₁ := List.getElem_append_left (as := [Sym.alpha] ++ encodeBitsSymNative v)
                  (bs := encodeElementsSym (w :: rest)) (i := i)
                  (by
                    rw [List.length_append]
                    simp
                    exact h2z)
                  (h' := by
                    rw [List.length_append, List.length_append]
                    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                    omega)
                have hv₂ := List.getElem_append_right (as := [Sym.alpha])
                  (bs := encodeBitsSymNative v) (i := i) (by omega : 1 ≤ i)
                  (h₂ := by
                    rw [List.length_append]
                    simp
                    exact h2z)
                exact (hv₁.trans hv₂)
          rw [hget]
          have h2z' : i < 1 + (encodeBitsSymNative v).length := by
            have hc := elemsPrefixLen_cons_shift v vs 0
            simpa [hc, elemsPrefixLen] using h2
          exact encodeBitsSymNative_kind v ((encodeBitsSymNative v)[i - 1]'(by omega)) (List.getElem_mem (by omega))
      | succ n =>
          have hn' : n < vs.length := by simp at hn; omega
          have hshift : elemsPrefixLen (v :: vs) (n + 1) = 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs n :=
            elemsPrefixLen_cons_shift v vs n
          have hshift2 : elemsPrefixLen (v :: vs) (n + 1 + 1) = 1 + (encodeBitsSymNative v).length + elemsPrefixLen vs (n + 1) :=
            elemsPrefixLen_cons_shift v vs (n + 1)
          have h1' : elemsPrefixLen vs n < i - (1 + (encodeBitsSymNative v).length) := by
            rw [hshift] at h1
            omega
          have h2' : i - (1 + (encodeBitsSymNative v).length) < elemsPrefixLen vs (n + 1) := by
            rw [hshift2] at h2
            omega
          have h := ih n (i - (1 + (encodeBitsSymNative v).length)) h1' h2' hn'
          by_cases hvs : vs = []
          · subst vs
            simp at hn
          · rcases vs with _ | ⟨w, rest⟩
            · exfalso; exact hvs rfl
            · have hget : (encodeElementsSym (v :: w :: rest))[i]'(by
                  rw [show encodeElementsSym (v :: w :: rest) = [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: rest) from by
                    simp only [encodeElementsSym]]
                  rw [List.length_append, List.length_append, List.length_singleton]
                  have hle := elemsPrefixLen_le_len (w :: rest) (n + 1)
                  omega) = (encodeElementsSym (w :: rest))[i - (1 + (encodeBitsSymNative v).length)]'(by
                    have hle := elemsPrefixLen_le_len (w :: rest) (n + 1)
                    exact Nat.lt_of_lt_of_le h2' hle) := by
                change ((([Sym.alpha] ++ encodeBitsSymNative v) ++ encodeElementsSym (w :: rest))[i]'(by
                      rw [List.length_append, List.length_append, List.length_singleton]
                      have hle := elemsPrefixLen_le_len (w :: rest) (n + 1)
                      omega) =
                    (encodeElementsSym (w :: rest))[i - (1 + (encodeBitsSymNative v).length)]'(by
                      have hle := elemsPrefixLen_le_len (w :: rest) (n + 1)
                      exact Nat.lt_of_lt_of_le h2' hle))
                rw [List.getElem_append_right (as := [Sym.alpha] ++ encodeBitsSymNative v)
                    (bs := encodeElementsSym (w :: rest)) (by
                      rw [List.length_append, List.length_singleton]
                      omega)]
                simp [List.length_append, List.length_singleton, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
              simpa [hget] using h

lemma branch_phase_inv (inst : SubsetSumInstance) (π : List SymStep) (cfg : SymConfig) :

    SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg →

    (∀ {π₀ : List SymStep} {cfg₀ : SymConfig},

      SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π₀ cfg₀ →

      (∃ ρ, π = π₀ ++ ρ) → π₀.length < π.length → cfg₀.state ≠ 4) →

    cfg.state = 4 →

    ∃ sel, sel.length = inst.elements.length ∧

      let k : ℤ := (encodeBitsSym inst.target).length

      cfg.headPos = k + 2 ∧

      tapeAgrees cfg.tape 1 (encodeBitsSym inst.target) ∧

      cfg.tape 0 = Sym.boundary ∧

      cfg.tape (1 + k) = Sym.boundary ∧

      tapeAgrees cfg.tape (2 + k) (encodeElementsSymWithSel inst.elements sel) ∧

      cfg.tape (2 + k + ((encodeElementsSymWithSel inst.elements sel).length : ℤ)) = Sym.mk SymKind.boundary true := by

  intro hπ hno4 hs4

  let k : ℤ := (encodeBitsSym inst.target).length

  let input := encodeInstanceSym inst

  let target : List Sym := encodeBitsSym inst.target

  let elems : List Sym := encodeElementsSym inst.elements

  let tape₀ := (symInitialConfig input).tape

  let len := elems.length

  have hk_def : (target.length : ℤ) = k := by

    dsimp [k, target]

  have htape_input : tapeAgrees tape₀ 0 input := by

    dsimp [tape₀]

    exact symInitialConfig_tapeAgrees input

  have hinput : input = [Sym.boundary] ++ target ++ [Sym.boundary] ++ elems ++ [Sym.boundary] := by

    rfl

  have htape0 : tape₀ 0 = Sym.boundary := by

    have h := (tapeAgrees_cons tape₀ 0 Sym.boundary

      (target ++ [Sym.boundary] ++ elems ++ [Sym.boundary])).mp ?_

    · exact h.1

    · rw [hinput] at htape_input

      exact htape_input

  have htape1 : tapeAgrees tape₀ 1 (target ++ [Sym.boundary] ++ elems ++ [Sym.boundary]) := by

    have h := (tapeAgrees_cons tape₀ 0 Sym.boundary

      (target ++ [Sym.boundary] ++ elems ++ [Sym.boundary])).mp ?_

    · exact h.2

    · rw [hinput] at htape_input

      exact htape_input

  have htape_target : tapeAgrees tape₀ 1 (target ++ [Sym.boundary]) := by

    have htape1' : tapeAgrees tape₀ 1 ((target ++ [Sym.boundary]) ++ (elems ++ [Sym.boundary])) := by

      simpa [List.append_assoc] using htape1

    exact (tapeAgrees_append tape₀ 1 (target ++ [Sym.boundary]) (elems ++ [Sym.boundary])).mp htape1' |>.1

  have htape_elems_boundary : tapeAgrees tape₀ (1 + ((target ++ [Sym.boundary]).length : ℤ)) (elems ++ [Sym.boundary]) := by

    have htape1' : tapeAgrees tape₀ 1 ((target ++ [Sym.boundary]) ++ (elems ++ [Sym.boundary])) := by

      simpa [List.append_assoc] using htape1

    exact (tapeAgrees_append tape₀ 1 (target ++ [Sym.boundary]) (elems ++ [Sym.boundary])).mp htape1' |>.2

  have htape_elems' : tapeAgrees tape₀ (2 + (target.length : ℤ)) (elems ++ [Sym.boundary]) := by

    convert htape_elems_boundary using 1

    simp [List.length_append]

    omega

  have htape_elems : tapeAgrees tape₀ (2 + (target.length : ℤ)) elems := by

    exact (tapeAgrees_append tape₀ (2 + (target.length : ℤ)) elems [Sym.boundary]).mp htape_elems' |>.1

  have hbound0 : tape₀ (1 + (target.length : ℤ)) = Sym.boundary := by

    have h := (tapeAgrees_append tape₀ 1 target [Sym.boundary]).mp htape_target |>.2

    simpa using ((tapeAgrees_cons tape₀ (1 + (target.length : ℤ)) Sym.boundary []).mp h).1

  have hbound1 : tape₀ (2 + (target.length : ℤ) + (elems.length : ℤ)) = Sym.boundary := by

    have h := (tapeAgrees_append tape₀ (2 + (target.length : ℤ)) elems [Sym.boundary]).mp htape_elems' |>.2

    simpa using ((tapeAgrees_cons tape₀ (2 + (target.length : ℤ) + (elems.length : ℤ)) Sym.boundary []).mp h).1

  have htape_elems_k : tapeAgrees tape₀ (2 + k) elems := by

    simpa [hk_def] using htape_elems

  have hbound0_k : tape₀ (1 + k) = Sym.boundary := by

    simpa [hk_def] using hbound0

  have hbound1_k : tape₀ (2 + k + (len : ℤ)) = Sym.boundary := by

    dsimp [len, elems]

    simpa [hk_def] using hbound1

  have htape_elems_orig : tapeAgrees tape₀ (2 + k) (encodeElementsSym inst.elements) := by

    dsimp [elems] at htape_elems_k

    exact htape_elems_k

  have hlen_eq : len = (encodeElementsSym inst.elements).length := by

    dsimp [len, elems]

  -- 主归纳：从初始配置出发、状态 ≤ 4 的路径的规范形

  let P : List SymStep → SymConfig → Prop := fun π₁ cfg₁ =>
    (cfg₁.state = 0 ∧ π₁ = [] ∧ cfg₁ = symInitialConfig input) ∨
    (cfg₁.state = 1 ∧ ∃ n : ℕ, (n : ℤ) ≤ k ∧ cfg₁ = SymConfig.mk 1 tape₀ (1 + (n : ℤ))) ∨
    (cfg₁.state = 2 ∧ ∃ sel : List Bool, ∃ n : ℕ, ∃ i : ℕ,
      sel.length = inst.elements.length ∧ n ≤ inst.elements.length ∧
      elemsPrefixLen inst.elements n ≤ i ∧ i ≤ elemsPrefixLen inst.elements (n + 1) ∧
      cfg₁.headPos = 2 + (k : ℤ) + (i : ℤ) ∧
      tapeAgrees cfg₁.tape (2 + (k : ℤ)) ((encodeElementsSymWithSel inst.elements sel).take i) ∧
      (∀ j : ℤ, i ≤ j ∧ j ≤ len → cfg₁.tape (2 + (k : ℤ) + (j : ℤ)) = tape₀ (2 + (k : ℤ) + (j : ℤ))) ∧
      (∀ j : ℤ, j < 2 + (k : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (k : ℤ) + (len : ℤ) < j → cfg₁.tape j = tape₀ j) ∧
      cfg₁.tape (2 + (k : ℤ) + (len : ℤ)) = tape₀ (2 + (k : ℤ) + (len : ℤ))) ∨
    (cfg₁.state = 3 ∧ ∃ sel : List Bool, sel.length = inst.elements.length ∧
      cfg₁.headPos = 2 + (k : ℤ) + (len : ℤ) ∧
      tapeAgrees cfg₁.tape (2 + (k : ℤ)) (encodeElementsSymWithSel inst.elements sel) ∧
      (∀ j : ℤ, j < 2 + (k : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (k : ℤ) + (len : ℤ) < j → cfg₁.tape j = tape₀ j) ∧
      cfg₁.tape (2 + (k : ℤ) + (len : ℤ)) = Sym.boundary) ∨
    (((cfg₁.state = 24 ∧ cfg₁.headPos = 2 + (k : ℤ) + (len : ℤ) - 1) ∨
      (cfg₁.state = 26 ∧ 1 + (k : ℤ) ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ 2 + (k : ℤ) + (len : ℤ) - 2) ∨
      (cfg₁.state = 27 ∧ cfg₁.headPos = 1 + (k : ℤ) - 1) ∨
      (cfg₁.state = 29 ∧ 1 + (k : ℤ) ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ 2 + (k : ℤ) + (len : ℤ) - 2) ∨
      (cfg₁.state = 38 ∧ 0 ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ 1 + (k : ℤ) - 2) ∨
      (cfg₁.state = 28 ∧ 1 ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ 1 + (k : ℤ))) ∧
      ∃ sel : List Bool, sel.length = inst.elements.length ∧
      tapeAgrees cfg₁.tape (2 + (k : ℤ)) (encodeElementsSymWithSel inst.elements sel) ∧
      (∀ j : ℤ, j < 2 + (k : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (k : ℤ) + (len : ℤ) < j → cfg₁.tape j = tape₀ j) ∧
      cfg₁.tape (2 + (k : ℤ) + (len : ℤ)) = Sym.mk SymKind.boundary true) ∨
    (cfg₁.state = 4 ∧ ∃ sel : List Bool, sel.length = inst.elements.length ∧
      cfg₁.headPos = 2 + (k : ℤ) ∧
      tapeAgrees cfg₁.tape (2 + (k : ℤ)) (encodeElementsSymWithSel inst.elements sel) ∧
      (∀ j : ℤ, j < 2 + (k : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (k : ℤ) + (len : ℤ) < j → cfg₁.tape j = tape₀ j) ∧
      cfg₁.tape (2 + (k : ℤ) + (len : ℤ)) = Sym.mk SymKind.boundary true) ∨

    (cfg₁.state = 101)

  have hP : P π cfg := by

    clear hs4

    induction hπ with

    | nil =>

        left

        exact ⟨rfl, rfl, rfl⟩

    | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>

        have hno4₀ : ∀ {π₀' : List SymStep} {cfg₀' : SymConfig},

            SymSteps VerifierSym.transition (symInitialConfig input) π₀' cfg₀' →

            (∃ ρ, π₀ = π₀' ++ ρ) → π₀'.length < π₀.length → cfg₀'.state ≠ 4 := by

          intro π₀' cfg₀' h₀' hpre' hlen'

          exact hno4 h₀' (by

            rcases hpre' with ⟨ρ', hρ'⟩

            refine ⟨ρ' ++ [step], by rw [hρ', List.append_assoc]⟩) (by

            simpa [List.length_append] using Nat.le_of_lt hlen')

        have hP₀ : P π₀ cfg₀ := ih hno4₀

        rcases hP₀ with hs0 | hs1 | hs2 | hs3 | hs4fmt | hs4 | hs101

        · -- 0 → 1

            rcases hs0 with ⟨_, _, hcfg₀⟩

            subst cfg₀

            have hres : step.result = SymTransResult.mk 1 Sym.boundary Dir.R := by

              have hdec : ∀ r ∈ VerifierSym.transition (0, Sym.boundary), r = SymTransResult.mk 1 Sym.boundary Dir.R := by
                decide
              have htrans' : step.result ∈ VerifierSym.transition (0, Sym.boundary) := by
                have h0 : (symInitialConfig (encodeInstanceSym inst)).tape 0 = Sym.boundary := by
                  simpa [tape₀] using htape0
                change step.result ∈ VerifierSym.transition (0, (symInitialConfig (encodeInstanceSym inst)).tape 0)
                rw [h0]
                exact h_trans
              exact hdec step.result htrans'

            right; left

            refine ⟨by rw [hres]; rfl, 0, by omega, ?_⟩

            dsimp [symStepConfig]

            rw [hres]

            have htape_eq : (fun i => if i = (symInitialConfig input).headPos then Sym.boundary else tape₀ i) = tape₀ := by

              funext i

              by_cases h : i = (symInitialConfig input).headPos

              · subst i

                simp only [symInitialConfig]

                exact htape0.symm

              · simp [h]

            rw [htape_eq]

            simp [symInitialConfig, Dir.toInt]

        · -- - 1 → 1 / 1 → 2

            rcases hs1 with ⟨_, n, hn, hcfg₀⟩

            subst cfg₀

            have hmem : step.result ∈ VerifierSym.transition (1, tape₀ (1 + (n : ℤ))) := by

              simpa using h_trans

            rcases trans1_next1_or_2 (tape₀ (1 + (n : ℤ))) step.result hmem with hnext1 | hnext2 | hnext101

            · -- 1 → 1：写回右移

              rcases trans1_next1 (tape₀ (1 + (n : ℤ))) step.result hmem hnext1 with ⟨hnb, hres⟩

              right; left

              refine ⟨by rw [hres]; rfl, n + 1, ?_, ?_⟩

              · by_contra h

                have hn_eq : (n : ℤ) = k := by omega

                have hc : (tape₀ (1 + (n : ℤ))).1 = SymKind.boundary := by

                  rw [hn_eq]

                  rw [hbound0_k]

                  rfl

                exact (hnb hc).elim

              · dsimp [symStepConfig]

                rw [hres]

                have htape_eq : (fun i => if i = 1 + (n : ℤ) then tape₀ (1 + (n : ℤ)) else tape₀ i) = tape₀ := by

                  funext i

                  by_cases h : i = 1 + (n : ℤ)

                  · subst i

                    simp

                  · simp [h]

                rw [htape_eq]

                norm_num [Dir.toInt]

                omega

            · -- 1 → 2：读 #₀

              rcases trans1_next2 (tape₀ (1 + (n : ℤ))) step.result hmem hnext2 with ⟨hbnd, hres⟩

              have hn_eq : (n : ℤ) = k := by

                by_cases hn_lt : (n : ℤ) < k

                · exfalso

                  have hnlt' : n < target.length := by

                    dsimp [k] at hn_lt

                    exact_mod_cast hn_lt

                  have hcell : tape₀ (1 + (n : ℤ)) = target[n]'hnlt' := by

                    have hcell' := htape_target n (by rw [List.length_append]; omega : n < (target ++ [Sym.boundary]).length)

                    have hget : (target ++ [Sym.boundary])[n]'(by rw [List.length_append]; omega : n < (target ++ [Sym.boundary]).length) = target[n]'hnlt' := by

                      rw [List.getElem_append_left hnlt']

                    simpa [hget] using hcell'

                  have hproj := congrArg (fun x : Sym => x.1) hcell

                  have hkind := encodeBitsSym_kind inst.target n hnlt'

                  rcases hkind with hd0 | hd1

                  · exfalso

                    have hbad : SymKind.boundary = SymKind.data0 := (hbnd.symm.trans hproj).trans hd0

                    nomatch hbad

                  · exfalso

                    have hbad : SymKind.boundary = SymKind.data1 := (hbnd.symm.trans hproj).trans hd1

                    nomatch hbad

                · exact le_antisymm hn (by omega)

              right; right; left

              refine ⟨by rw [hres]; rfl, List.replicate inst.elements.length false, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

              · simp

              · simp

              · rw [elemsPrefixLen_zero]

              · simp [elemsPrefixLen]

              · dsimp [symStepConfig]

                rw [hres, hn_eq]

                norm_num [Dir.toInt]

                omega

              · -- hfirst：tapeAgrees (2+k) (WithSel 串 take 0 = [])

                dsimp [symStepConfig]

                have htape_eq : (fun i => if i = 1 + (n : ℤ) then tape₀ (1 + (n : ℤ)) else tape₀ i) = tape₀ := by

                  funext i

                  by_cases h : i = 1 + (n : ℤ)

                  · subst i

                    simp

                  · simp [h]

                rw [hres, htape_eq]

                simp [tapeAgrees]

              · -- hsecond：cfg₁ 写回原符号 → 未转换区不变
                intro j hj
                dsimp [symStepConfig]
                rw [hres]
                by_cases h : 2 + (k : ℤ) + (j : ℤ) = 1 + (n : ℤ) <;> simp [h]
              · intro j hj
                dsimp [symStepConfig]
                rw [hres]
                by_cases h : (j : ℤ) = 1 + (n : ℤ) <;> simp [h]
              · intro j hj
                dsimp [symStepConfig]
                rw [hres]
                by_cases h : (j : ℤ) = 1 + (n : ℤ) <;> simp [h]
              · dsimp [symStepConfig]
                rw [hres]
                by_cases h : 2 + (k : ℤ) + (len : ℤ) = 1 + (n : ℤ) <;> simp [h]


            · -- 101：读符号 kind 矛盾（target 区只有 data/boundary）

              exfalso

              have hkind101 := trans1_next101_read_kind (tape₀ (1 + (n : ℤ))) step.result hmem hnext101

              by_cases hn_lt : (n : ℤ) < k

              · have hnlt' : n < target.length := by

                  dsimp [k] at hn_lt

                  exact_mod_cast hn_lt

                have hcell : tape₀ (1 + (n : ℤ)) = target[n]'hnlt' := by

                  have hcell' := htape_target n (by rw [List.length_append]; omega : n < (target ++ [Sym.boundary]).length)

                  have hget : (target ++ [Sym.boundary])[n]'(by rw [List.length_append]; omega : n < (target ++ [Sym.boundary]).length) = target[n]'hnlt' := by

                    rw [List.getElem_append_left hnlt']

                  simpa [hget] using hcell'

                have hkind := encodeBitsSym_kind inst.target n hnlt'

                rcases hkind with hd0 | hd1

                · rcases hkind101 with h | h | h | h | h <;>

                    (exfalso

                     have hproj := congrArg (fun x : Sym => x.1) hcell

                     rw [hproj] at h

                     rw [hd0] at h

                     cases h)

                · rcases hkind101 with h | h | h | h | h <;>

                    (exfalso

                     have hproj := congrArg (fun x : Sym => x.1) hcell

                     rw [hproj] at h

                     rw [hd1] at h

                     cases h)

              · have hn_eq : (n : ℤ) = k := le_antisymm hn (by omega)

                have hkindb : (tape₀ (1 + (n : ℤ))).1 = SymKind.boundary := by

                  rw [hn_eq]

                  change (tape₀ (1 + k)).1 = SymKind.boundary

                  exact congrArg (fun x : Sym => x.1) hbound0_k

                rcases hkind101 with h | h | h | h | h <;>

                  (exfalso

                   nomatch h.symm.trans hkindb)

        · -- - 2 → 2 / 2 → 3

            rcases hs2 with ⟨hs2', sel, n, i, hsel_len, hn, hpref1, hpref2, hhead₂, hfirst, hsecond, hleft₂, hright₂, hhash₂⟩
            have hi : i ≤ len := by
              exact le_trans hpref2 (by
                simpa [len, elems] using elemsPrefixLen_le_len inst.elements (n + 1))

            have hmem : step.result ∈ VerifierSym.transition (2, cfg₀.tape cfg₀.headPos) := by

              simpa [hs2'] using h_trans

            rcases trans2_next2_or_3 (cfg₀.tape cfg₀.headPos) step.result hmem with hnext2 | hnext3

            · -- 2 → 2

              rcases trans2_next2 (cfg₀.tape cfg₀.headPos) step.result hmem hnext2 with

                hwrite | hselw | hnoselw

              · -- 写回原符号右移（读 data 类符号）

                rcases hwrite with ⟨hres, hna, hnb, hnbnd⟩

                have hi_lt : i < len := by

                  by_contra h

                  have hi_eq : i = len := by omega

                  subst i

                  have hcell : cfg₀.tape (2 + (k : ℤ) + (len : ℤ)) = tape₀ (2 + (k : ℤ) + (len : ℤ)) := hsecond len ⟨by omega, by omega⟩

                  rw [hbound1_k] at hcell

                  have hbc : (cfg₀.tape (2 + (k : ℤ) + (len : ℤ))).1 = SymKind.boundary := by rw [hcell]; rfl

                  have hbc' : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by simpa [hhead₂] using hbc

                  exact (hnbnd hbc').elim

                right; right; left

                refine ⟨by rw [hres]; rfl, sel, n, i + 1, hsel_len, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

                · -- hpref1'：左界 ≤ i+1

                  omega

                · -- hpref2'：i+1 ≤ 右端——i ≠ 右端（读 data 类）

                  by_contra h

                  have hi_ge : elemsPrefixLen inst.elements (n + 1) ≤ i := by omega

                  have hi_eq : i = elemsPrefixLen inst.elements (n + 1) := le_antisymm hpref2 hi_ge

                  by_cases hn1 : n + 1 < inst.elements.length

                  · -- 右端 = 下一元素标记格（alpha/beta），与读 data 矛盾

                    have hcell : cfg₀.tape (2 + (k : ℤ) + (i : ℤ)) = tape₀ (2 + (k : ℤ) + (i : ℤ)) := hsecond i ⟨by omega, by omega⟩

                    have hkind : (tape₀ (2 + (k : ℤ) + (i : ℤ))).1 = SymKind.alpha ∨
                        (tape₀ (2 + (k : ℤ) + (i : ℤ))).1 = SymKind.beta := by

                      rw [hi_eq]

                      have hta := htape_elems_orig (elemsPrefixLen inst.elements (n + 1)) (by
                        exact elemsPrefixLen_lt_len_of_lt inst.elements n hn1)

                      rw [hta]

                      exact encodeElementsSym_kind_at_prefixEnd inst.elements n hn1

                    rw [← hcell] at hkind

                    rcases hkind with hk | hk

                    · exact (hna (by simpa [hhead₂] using hk)).elim

                    · exact (hnb (by simpa [hhead₂] using hk)).elim

                  · -- n+1 ≥ 元素数：右端 = len = #₁（boundary），与读 data 矛盾

                    have hi_len : i = len := by
                      have h1 : elemsPrefixLen inst.elements (n + 1) = elemsPrefixLen inst.elements inst.elements.length := by
                        unfold elemsPrefixLen
                        congr 1
                        rw [List.take_of_length_le (by omega : inst.elements.length ≤ n + 1)]
                        rw [List.take_length]
                      rw [hi_eq, h1]
                      rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl]

                    have hcell : cfg₀.tape (2 + (k : ℤ) + (i : ℤ)) = tape₀ (2 + (k : ℤ) + (i : ℤ)) := hsecond i ⟨by omega, by omega⟩

                    rw [hi_len] at hcell

                    rw [hbound1_k] at hcell

                    have hbc : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by

                      rw [hhead₂, hi_len]

                      exact congrArg (fun x : Sym => x.1) hcell

                    exact (hnbnd hbc).elim

                · -- hhead'

                  dsimp [symStepConfig]

                  rw [hhead₂, hres]

                  norm_num [Dir.toInt]

                  omega

                · -- hfirst'：j < i+1

                  intro j hj

                  by_cases hj_eq : (j = i)

                  · subst j

                    have hcell : cfg₀.tape (2 + (k : ℤ) + (i : ℤ)) = tape₀ (2 + (k : ℤ) + (i : ℤ)) := hsecond i ⟨by omega, by omega⟩

                    have hkrange : (tape₀ (2 + (k : ℤ) + (i : ℤ))).1 = SymKind.data0 ∨
                        (tape₀ (2 + (k : ℤ) + (i : ℤ))).1 = SymKind.data1 := by

                      have hi' : i < len := by omega

                      have hta := htape_elems_orig i hi'

                      rw [hta]

                      have hmem' : (encodeElementsSym inst.elements)[i]'hi' ∈ encodeElementsSym inst.elements :=
                        List.getElem_mem hi'

                      rcases encodeElementsSym_kind_range inst.elements ((encodeElementsSym inst.elements)[i]'hi') hmem' with hα | hβ | hd0 | hd1

                      · exfalso

                        have hk' : (cfg₀.tape cfg₀.headPos).1 = SymKind.alpha := by

                          rw [hhead₂]

                          simpa [hcell, hta] using hα

                        exact (hna hk').elim

                      · exfalso

                        have hk' : (cfg₀.tape cfg₀.headPos).1 = SymKind.beta := by

                          rw [hhead₂]

                          simpa [hcell, hta] using hβ

                        exact (hnb hk').elim

                      · left; exact hd0

                      · right; exact hd1

                    have hi' : i < len := by omega

                    have hlenws : (encodeElementsSymWithSel inst.elements sel).length = len := by
                      rw [WithSel_length inst.elements sel hsel_len]

                    have hws : (encodeElementsSymWithSel inst.elements sel)[i]'(by rw [hlenws]; exact hi') =
                        (encodeElementsSym inst.elements)[i]'hi' := by
                      have hta := htape_elems_orig i hi'
                      have hkrange' : ((encodeElementsSym inst.elements)[i]'hi').1 = SymKind.data0 ∨
                          ((encodeElementsSym inst.elements)[i]'hi').1 = SymKind.data1 := by
                        rw [hta] at hkrange
                        exact hkrange
                      exact encodeElementsSymWithSel_cell_of_data inst.elements sel hsel_len i hi' hkrange'

                    dsimp [symStepConfig]

                    rw [hres]

                    rw [hhead₂]

                    rw [if_pos rfl]

                    rw [hcell]

                    rw [htape_elems_orig i hi']

                    have hget : ((encodeElementsSymWithSel inst.elements sel).take (i + 1))[i]'(by
                      rw [List.length_take]
                      exact Nat.lt_min.mpr ⟨by omega, by rw [hlenws]; exact hi'⟩) = (encodeElementsSymWithSel inst.elements sel)[i]'(by rw [hlenws]; exact hi') := by
                      exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i + 1) (i := i) (h := by
                        rw [List.length_take]
                        exact Nat.lt_min.mpr ⟨by omega, by rw [hlenws]; exact hi'⟩)

                    rw [hget]

                    exact hws.symm

                  · have hj_lt : j < i := by
                      rw [List.length_take] at hj
                      have hjle : j < i + 1 := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
                      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjle) hj_eq

                    have hfirst_j := hfirst j (by

                      rw [List.length_take]

                      refine Nat.lt_min.mpr ⟨hj_lt, by
                        have hlenws : (encodeElementsSymWithSel inst.elements sel).length = len := by
                          rw [WithSel_length inst.elements sel hsel_len]
                        rw [hlenws]
                        omega⟩)

                    rw [show (symStepConfig cfg₀ step.result).tape (2 + (k : ℤ) + (j : ℤ)) = cfg₀.tape (2 + (k : ℤ) + (j : ℤ)) from by

                      dsimp [symStepConfig]

                      have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                        rw [hhead₂]

                        omega

                      simp [hne]]

                    rw [hfirst_j]

                    rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i) (i := j) (h := by
                      rw [List.length_take]
                      exact Nat.lt_min.mpr ⟨hj_lt, by
        have hlenws_tk : (encodeElementsSymWithSel inst.elements sel).length = len := by
          rw [WithSel_length inst.elements sel hsel_len]
        rw [hlenws_tk]
        omega⟩)]

                    rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i + 1) (i := j) (h := by
                      rw [List.length_take]
                      exact Nat.lt_min.mpr ⟨by omega, by
                        have hlenws_tk : (encodeElementsSymWithSel inst.elements sel).length = len := by
                          rw [WithSel_length inst.elements sel hsel_len]
                        rw [hlenws_tk]
                        omega⟩)]

                · intro j hj

                  dsimp [symStepConfig]

                  have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                    rw [hhead₂]

                    omega

                  simpa [hres, hne] using hsecond j ⟨by omega, hj.2⟩

                · intro j hj

                  dsimp [symStepConfig]

                  have hne : j ≠ cfg₀.headPos := by

                    rw [hhead₂]

                    omega

                  simpa [hres, hne] using hleft₂ j hj

                · intro j hj

                  dsimp [symStepConfig]

                  have hne : j ≠ cfg₀.headPos := by

                    rw [hhead₂]

                    omega

                  simpa [hres, hne] using hright₂ j hj

                · dsimp [symStepConfig]

                  have hne : 2 + (k : ℤ) + (len : ℤ) ≠ cfg₀.headPos := by

                    rw [hhead₂]

                    omega

                  simpa [hres, hne] using hhash₂

              · -- α/β 写 sel 右移：sel 置 true，WithSel 位为 sel

                rcases hselw with ⟨hres, hbranch⟩

                have hi_lt : i < len := by

                  by_contra h

                  have hi_eq : i = len := by omega

                  subst i

                  have hcell : cfg₀.tape (2 + (k : ℤ) + (len : ℤ)) = tape₀ (2 + (k : ℤ) + (len : ℤ)) := hsecond len ⟨by omega, by omega⟩

                  rw [hbound1_k] at hcell

                  have hbc : (cfg₀.tape (2 + (k : ℤ) + (len : ℤ))).1 = SymKind.boundary := by rw [hcell]; rfl

                  rcases hbranch with hα | hβ

                  · cases (hbc.symm.trans (by simpa [hhead₂] using hα))

                  · cases (hbc.symm.trans (by simpa [hhead₂] using hβ))

                by_cases hi_eq : (i = elemsPrefixLen inst.elements n)
                · -- i = 左界(n)：元素 n 的标记格——sel.set n true、产出 n+1

                    have hnlt : n < inst.elements.length := by

                      by_contra h

                      have hn_eq : n = inst.elements.length := by omega

                      rw [hn_eq] at hi_eq

                      rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl] at hi_eq

                      rw [← hlen_eq] at hi_eq

                      omega

                    let sel' : List Bool := sel.set n true

                    unfold P

                    right

                    right

                    left

                    refine ⟨by rw [hres]; rfl, sel', n, i + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩



                    · dsimp [sel']

                      rw [List.length_set]

                      exact hsel_len

                    · omega

                    · -- hpref1'：左界(n) ≤ i+1

                      rw [hi_eq]

                      omega

                    · -- hpref2'：i+1 ≤ 左界(n+1)

                      rw [hi_eq]

                      have hsucc2 := elemsPrefixLen_succ inst.elements n hnlt

                      rw [hsucc2]

                      omega

                    · -- hhead'

                      dsimp [symStepConfig]

                      rw [hhead₂, hres]

                      norm_num [Dir.toInt]

                      omega

                    · -- hfirst'：j < i+1

                      intro j hj

                      have hem : j = i ∨ j ≠ i := Classical.em (j = i)
                      match hem with

                      | Or.inl hj_eq =>

                          have hmv : (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements n]'(by
                            rw [WithSel_length inst.elements sel' (by
                              dsimp [sel']
                              rw [List.length_set]
                              exact hsel_len)]
                            simpa [hi_eq] using hi_lt) = Sym.sel := by

                            rw [encodeElementsSymWithSel_mark_val inst.elements sel' (by

                              dsimp [sel']

                              rw [List.length_set]

                              exact hsel_len) n hnlt]

                            dsimp [sel']

                            rw [List.getElem_set_self]

                            simp

                          dsimp [symStepConfig]

                          rw [hres]

                          rw [hhead₂]

                          rw [if_pos (by rw [hj_eq])]

                          rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                            rw [List.length_take]
                            refine Nat.lt_min.mpr ⟨by omega, by
                              rw [WithSel_length inst.elements sel' (by
                                dsimp [sel']
                                rw [List.length_set]
                                exact hsel_len)]
                              rw [hj_eq]
                              exact hi_lt⟩)]

                          have hj_lt' : j < (encodeElementsSymWithSel inst.elements sel').length := by
                            rw [WithSel_length inst.elements sel' (by
                              dsimp [sel']
                              rw [List.length_set]
                              exact hsel_len)]
                            rw [hj_eq]
                            exact hi_lt

                          have heq_lt : elemsPrefixLen inst.elements n < (encodeElementsSymWithSel inst.elements sel').length := by
                            rw [WithSel_length inst.elements sel' (by
                              dsimp [sel']
                              rw [List.length_set]
                              exact hsel_len)]
                            simpa [hi_eq] using hi_lt

                          have hi_eq' : (encodeElementsSymWithSel inst.elements sel')[j] = (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements n] := by
                            simpa [hj_eq, hi_eq]

                          rw [hi_eq']

                          exact hmv.symm

                      | Or.inr hj_ne =>
                            have hj_lt : j < i := by
                              rw [List.length_take] at hj
                              have hjle : j < i + 1 := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
                              exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjle) hj_ne

                            have hfirst_j := hfirst j (by

                              rw [List.length_take]

                              refine Nat.lt_min.mpr ⟨hj_lt, by
                                have hlenws' : (encodeElementsSymWithSel inst.elements sel).length = len := by
                                  rw [WithSel_length inst.elements sel hsel_len]
                                rw [hlenws']
                                omega⟩)

                            rw [show (symStepConfig cfg₀ step.result).tape (2 + (k : ℤ) + (j : ℤ)) = cfg₀.tape (2 + (k : ℤ) + (j : ℤ)) from by

                              dsimp [symStepConfig]

                              have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                                rw [hhead₂]

                                omega

                              simp [hne]]

                            rw [hfirst_j]

                            have hlenws_j : (encodeElementsSymWithSel inst.elements sel).length = len := by
                              rw [WithSel_length inst.elements sel hsel_len]
                            have hget1 : ((encodeElementsSymWithSel inst.elements sel).take i)[j]'(by
                              rw [List.length_take]
                              refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩) =
                              (encodeElementsSymWithSel inst.elements sel)[j]'(by rw [hlenws_j]; omega) := by
                              exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i) (i := j) (h := by
                                rw [List.length_take]
                                refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩)

                            have hlenws_j : (encodeElementsSymWithSel inst.elements sel').length = len := by
                              rw [WithSel_length inst.elements sel' (by dsimp [sel']; rw [List.length_set]; exact hsel_len)]
                            have hget2 : ((encodeElementsSymWithSel inst.elements sel').take (i + 1))[j]'(by
                              rw [List.length_take]
                              refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩) =
                              (encodeElementsSymWithSel inst.elements sel')[j]'(by rw [hlenws_j]; omega) := by
                              exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                                rw [List.length_take]
                                refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩)

                            rw [hget1, hget2]

                            exact (encodeElementsSymWithSel_set_eq_of_lt inst.elements sel hsel_len n true j (by

                            rw [← hi_eq]

                            exact hj_lt)).symm

                    · -- hsecond'：i+1 ≤ j ≤ len

                      intro j hj

                      dsimp [symStepConfig]

                      have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                        rw [hhead₂]

                        omega

                      simpa [hres, hne] using hsecond j ⟨by omega, hj.2⟩

                    · intro j hj

                      dsimp [symStepConfig]

                      have hne : j ≠ cfg₀.headPos := by

                        rw [hhead₂]

                        omega

                      simpa [hres, hne] using hleft₂ j hj

                    · intro j hj

                      dsimp [symStepConfig]

                      have hne : j ≠ cfg₀.headPos := by

                        rw [hhead₂]

                        omega

                      simpa [hres, hne] using hright₂ j hj

                    · dsimp [symStepConfig]

                      have hne : 2 + (k : ℤ) + (len : ℤ) ≠ cfg₀.headPos := by

                        rw [hhead₂]

                        omega

                      simpa [hres, hne] using hhash₂

                · -- i ≠ 左界(n)：必为左界(n+1)（区间内唯一标记格）

                  have hi_gt : elemsPrefixLen inst.elements n < i := by omega

                  have hnlt : n < inst.elements.length := by

                    by_contra h

                    have hn_eq : n = inst.elements.length := by omega

                    rw [hn_eq] at hpref1

                    rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl, ← hlen_eq] at hpref1

                    omega

                  by_cases hi_lt' : i < elemsPrefixLen inst.elements (n + 1)
                  · -- native 区：读 data——与 hbranch（alpha/beta）矛盾

                          exfalso

                          have hcell : cfg₀.tape (2 + (k : ℤ) + (i : ℤ)) = tape₀ (2 + (k : ℤ) + (i : ℤ)) := hsecond i ⟨by omega, by omega⟩

                          have hkrange := encodeElementsSym_kind_data_of_prefixRange inst.elements n i hi_gt hi_lt' hnlt

                          have hta := htape_elems_orig i (by omega : i < len)

                          rw [← hta] at hkrange

                          rw [← hcell] at hkrange

                          rcases hkrange with hk | hk <;> rcases hbranch with hα | hβ

                          · cases (hk.symm.trans (by simpa [hhead₂] using hα))

                          · cases (hk.symm.trans (by simpa [hhead₂] using hβ))

                          · cases (hk.symm.trans (by simpa [hhead₂] using hα))

                          · cases (hk.symm.trans (by simpa [hhead₂] using hβ))

                  · -- i = 左界(n+1)：元素 n+1 的标记格——sel.set (n+1) true、产出 n+2

                          have hi_eq' : i = elemsPrefixLen inst.elements (n + 1) := le_antisymm hpref2 (by omega)

                          have hn1lt : n + 1 < inst.elements.length := by

                            by_contra h

                            have hn1_eq : n + 1 = inst.elements.length := by omega

                            rw [hn1_eq] at hi_eq'

                            rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl, ← hlen_eq] at hi_eq'

                            omega

                          let sel' : List Bool := sel.set (n + 1) true

                          unfold P

                          right

                          right

                          left

                          refine ⟨by rw [hres]; rfl, sel', n + 1, i + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

                          · dsimp [sel']

                            rw [List.length_set]

                            exact hsel_len

                          · omega

                          · -- hpref1'：左界(n+1) ≤ i+1

                            rw [hi_eq']

                            omega

                          · -- hpref2'：i+1 ≤ 左界(n+2)

                            rw [hi_eq']

                            have hsucc3 := elemsPrefixLen_succ inst.elements (n + 1) hn1lt

                            rw [hsucc3]

                            omega

                          · dsimp [symStepConfig]

                            rw [hhead₂, hres]

                            norm_num [Dir.toInt]

                            omega

                          · intro j hj

                            by_cases hj_eq : (j = i)

                            · -- j = i 分支（hj_eq 保留——subst 于 by_cases motive 不生效）

                              have hws_len' : (encodeElementsSymWithSel inst.elements sel').length = len := by
                                rw [WithSel_length inst.elements sel' (by
                                  dsimp [sel']
                                  rw [List.length_set]
                                  exact hsel_len)]

                              have hmv : (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements (n + 1)]'(by
                                rw [hws_len']
                                have hlt' := elemsPrefixLen_lt_len_of_lt inst.elements n hn1lt
                                rw [← hlen_eq] at hlt'
                                exact hlt') = Sym.sel := by

                                rw [encodeElementsSymWithSel_mark_val inst.elements sel' (by

                                  dsimp [sel']

                                  rw [List.length_set]

                                  exact hsel_len) (n + 1) hn1lt]

                                dsimp [sel']

                                rw [List.getElem_set_self]

                                simp

                              have hL : (symStepConfig cfg₀ step.result).tape (2 + k + ↑j) = Sym.sel := by
                                dsimp [symStepConfig]
                                rw [hres]
                                rw [hhead₂]
                                rw [if_pos (by rw [hj_eq])]

                              have hR : (List.take (i + 1) (encodeElementsSymWithSel inst.elements sel'))[j] = (encodeElementsSymWithSel inst.elements sel')[j] := by
                                rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                                  rw [List.length_take]
                                  refine Nat.lt_min.mpr ⟨by
                                    have hj' : j < min (i + 1) (encodeElementsSymWithSel inst.elements sel').length := by
                                      simpa [List.length_take] using hj
                                    exact Nat.lt_of_lt_of_le hj' (Nat.min_le_left (i + 1) (encodeElementsSymWithSel inst.elements sel').length), by
                                    have hj'' : j < min (i + 1) (encodeElementsSymWithSel inst.elements sel').length := by
                                      simpa [List.length_take] using hj
                                    exact Nat.lt_of_lt_of_le hj'' (Nat.min_le_right (i + 1) (encodeElementsSymWithSel inst.elements sel').length)⟩)]

                              rw [hL, hR]
                              rw [show (encodeElementsSymWithSel inst.elements sel')[j] = (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements (n + 1)] from by
                                congr
                                rw [hj_eq]
                                exact hi_eq']
                              exact hmv.symm

                            · have hj_lt : j < i := by rw [List.length_take] at hj; exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _))) hj_eq

                              have hfirst_j := hfirst j (by

                                rw [List.length_take]

                                refine Nat.lt_min.mpr ⟨by omega, by
                                  have hlenws' : (encodeElementsSymWithSel inst.elements sel).length = len := by
                                    rw [WithSel_length inst.elements sel hsel_len]
                                  rw [hlenws']
                                  omega⟩)

                              rw [show (symStepConfig cfg₀ step.result).tape (2 + (k : ℤ) + (j : ℤ)) = cfg₀.tape (2 + (k : ℤ) + (j : ℤ)) from by

                                dsimp [symStepConfig]

                                have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                                  rw [hhead₂]

                                  omega

                                simp [hne]]

                              rw [hfirst_j]

                              have hlenws_j : (encodeElementsSymWithSel inst.elements sel).length = len := by
                                rw [WithSel_length inst.elements sel hsel_len]
                              have hget1 : ((encodeElementsSymWithSel inst.elements sel).take i)[j]'(by
                                rw [List.length_take]
                                refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩) =
                                (encodeElementsSymWithSel inst.elements sel)[j]'(by rw [hlenws_j]; omega) := by
                                exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i) (i := j) (h := by
                                  rw [List.length_take]
                                  refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩)

                              have hlenws_j : (encodeElementsSymWithSel inst.elements sel').length = len := by
                                rw [WithSel_length inst.elements sel' (by dsimp [sel']; rw [List.length_set]; exact hsel_len)]
                              have hget2 : ((encodeElementsSymWithSel inst.elements sel').take (i + 1))[j]'(by
                                rw [List.length_take]
                                refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩) =
                                (encodeElementsSymWithSel inst.elements sel')[j]'(by rw [hlenws_j]; omega) := by
                                exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                                  rw [List.length_take]
                                  refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩)

                              rw [hget1, hget2]

                              exact (encodeElementsSymWithSel_set_eq_of_lt inst.elements sel hsel_len (n + 1) true j (by

                                  rw [← hi_eq']

                                  exact hj_lt)).symm

                          · -- hsecond'：i+1 ≤ j ≤ len

                            intro j hj

                            dsimp [symStepConfig]

                            have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                              rw [hhead₂]

                              omega

                            simpa [hres, hne] using hsecond j ⟨by omega, hj.2⟩

                          · intro j hj

                            dsimp [symStepConfig]

                            have hne : j ≠ cfg₀.headPos := by

                              rw [hhead₂]

                              omega

                            simpa [hres, hne] using hleft₂ j hj

                          · intro j hj

                            dsimp [symStepConfig]

                            have hne : j ≠ cfg₀.headPos := by

                              rw [hhead₂]

                              omega

                            simpa [hres, hne] using hright₂ j hj

                          · dsimp [symStepConfig]

                            have hne : 2 + (k : ℤ) + (len : ℤ) ≠ cfg₀.headPos := by

                              rw [hhead₂]

                              omega

                            simpa [hres, hne] using hhash₂

              · -- β/α 写 nosel 右移：sel 置 false，WithSel 位为 nosel

                rcases hnoselw with ⟨hres, hbranch⟩

                have hi_lt : i < len := by

                  by_contra h

                  have hi_eq : i = len := by omega

                  subst i

                  have hcell : cfg₀.tape (2 + (k : ℤ) + (len : ℤ)) = tape₀ (2 + (k : ℤ) + (len : ℤ)) := hsecond len ⟨by omega, by omega⟩

                  rw [hbound1_k] at hcell

                  have hbc : (cfg₀.tape (2 + (k : ℤ) + (len : ℤ))).1 = SymKind.boundary := by rw [hcell]; rfl

                  rcases hbranch with hα | hβ

                  · cases (hbc.symm.trans (by simpa [hhead₂] using hα))

                  · cases (hbc.symm.trans (by simpa [hhead₂] using hβ))

                by_cases hi_eq : (i = elemsPrefixLen inst.elements n)
                · -- i = 左界(n)：元素 n 的标记格——sel.set n false、产出 n+1

                  have hnlt : n < inst.elements.length := by

                    by_contra h

                    have hn_eq : n = inst.elements.length := by omega

                    rw [hn_eq] at hi_eq

                    rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl] at hi_eq

                    rw [← hlen_eq] at hi_eq

                    omega

                  let sel' : List Bool := sel.set n false

                  right; right; left

                  refine ⟨by rw [hres]; rfl, sel', n, i + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

                  · dsimp [sel']

                    rw [List.length_set]

                    exact hsel_len

                  · omega

                  · -- hpref1'：左界(n) ≤ i+1

                    rw [hi_eq]

                    omega

                  · -- hpref2'：i+1 ≤ 左界(n+1)

                    rw [hi_eq]

                    have hsucc2 := elemsPrefixLen_succ inst.elements n hnlt

                    rw [hsucc2]

                    omega

                  · -- hhead'

                    dsimp [symStepConfig]

                    rw [hhead₂, hres]

                    norm_num [Dir.toInt]

                    omega

                  · -- hfirst'：j < i+1

                    intro j hj

                    by_cases hj_eq : (j = i)

                    · -- j = i 分支（hj_eq 保留）

                      have hpf_lt : elemsPrefixLen inst.elements n < len := by
                        have hsucc := elemsPrefixLen_succ inst.elements n hnlt
                        have hlt : elemsPrefixLen inst.elements n < elemsPrefixLen inst.elements (n + 1) := by
                          rw [hsucc]
                          omega
                        have hpf_le : elemsPrefixLen inst.elements (n + 1) ≤ len := by
                          have h := elemsPrefixLen_le_len inst.elements (n + 1)
                          rw [← hlen_eq] at h
                          exact h
                        exact lt_of_lt_of_le hlt hpf_le

                      have hws_len : (encodeElementsSymWithSel inst.elements sel').length = len := by
                        rw [WithSel_length inst.elements sel' (by
                          dsimp [sel']
                          rw [List.length_set]
                          exact hsel_len)]

                      have hmv : (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements n]'(by
                        rw [hws_len]
                        exact hpf_lt) = Sym.nosel := by

                        rw [encodeElementsSymWithSel_mark_val inst.elements sel' (by

                          dsimp [sel']

                          rw [List.length_set]

                          exact hsel_len) n hnlt]

                        dsimp [sel']

                        rw [List.getElem_set_self]

                        simp

                      dsimp [symStepConfig]

                      rw [hres]

                      rw [hhead₂]

                      rw [if_pos (by rw [hj_eq])]

                      rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                        rw [List.length_take]
                        exact Nat.lt_min.mpr ⟨by omega, by
                          have hlenws_tk : (encodeElementsSymWithSel inst.elements sel').length = len := by
                            rw [WithSel_length inst.elements sel' (by dsimp [sel']; rw [List.length_set]; exact hsel_len)]
                          rw [hlenws_tk]
                          omega⟩)]

                      rw [show (encodeElementsSymWithSel inst.elements sel')[j] = (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements n] from by
                        congr
                        rw [hj_eq]
                        exact hi_eq]

                      exact hmv.symm

                    · have hj_lt : j < i := by
                        rw [List.length_take] at hj
                        have hjle : j < i + 1 := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
                        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjle) hj_eq

                      have hfirst_j := hfirst j (by

                        rw [List.length_take]

                        refine Nat.lt_min.mpr ⟨hj_lt, by
                          have hlenws' : (encodeElementsSymWithSel inst.elements sel).length = len := by
                            rw [WithSel_length inst.elements sel hsel_len]
                          rw [hlenws']
                          omega⟩)

                      rw [show (symStepConfig cfg₀ step.result).tape (2 + (k : ℤ) + (j : ℤ)) = cfg₀.tape (2 + (k : ℤ) + (j : ℤ)) from by

                        dsimp [symStepConfig]

                        have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                          rw [hhead₂]

                          omega

                        simp [hne]]

                      rw [hfirst_j]

                      have hlenws_j : (encodeElementsSymWithSel inst.elements sel).length = len := by
                        rw [WithSel_length inst.elements sel hsel_len]
                      have hget1 : ((encodeElementsSymWithSel inst.elements sel).take i)[j]'(by
                        rw [List.length_take]
                        refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩) =
                        (encodeElementsSymWithSel inst.elements sel)[j]'(by rw [hlenws_j]; omega) := by
                        exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i) (i := j) (h := by
                          rw [List.length_take]
                          refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩)

                      have hlenws_j : (encodeElementsSymWithSel inst.elements sel').length = len := by
                        rw [WithSel_length inst.elements sel' (by dsimp [sel']; rw [List.length_set]; exact hsel_len)]
                      have hget2 : ((encodeElementsSymWithSel inst.elements sel').take (i + 1))[j]'(by
                        rw [List.length_take]
                        refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩) =
                        (encodeElementsSymWithSel inst.elements sel')[j]'(by rw [hlenws_j]; omega) := by
                        exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                          rw [List.length_take]
                          refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩)

                      rw [hget1, hget2]

                      exact (encodeElementsSymWithSel_set_eq_of_lt inst.elements sel hsel_len n false j (by

                        rw [← hi_eq]

                        exact hj_lt)).symm

                  · -- hsecond'：i+1 ≤ j ≤ len

                    intro j hj

                    dsimp [symStepConfig]

                    have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                      rw [hhead₂]

                      omega

                    simpa [hres, hne] using hsecond j ⟨by omega, hj.2⟩

                  · intro j hj

                    dsimp [symStepConfig]

                    have hne : j ≠ cfg₀.headPos := by

                      rw [hhead₂]

                      omega

                    simpa [hres, hne] using hleft₂ j hj

                  · intro j hj

                    dsimp [symStepConfig]

                    have hne : j ≠ cfg₀.headPos := by

                      rw [hhead₂]

                      omega

                    simpa [hres, hne] using hright₂ j hj

                  · dsimp [symStepConfig]

                    have hne : 2 + (k : ℤ) + (len : ℤ) ≠ cfg₀.headPos := by

                      rw [hhead₂]

                      omega

                    simpa [hres, hne] using hhash₂

                · -- i ≠ 左界(n)：必为左界(n+1)（区间内唯一标记格）

                  have hi_gt : elemsPrefixLen inst.elements n < i := by omega

                  have hnlt : n < inst.elements.length := by

                    by_contra h

                    have hn_eq : n = inst.elements.length := by omega

                    rw [hn_eq] at hpref1

                    rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl, ← hlen_eq] at hpref1

                    omega

                  by_cases hi_lt' : i < elemsPrefixLen inst.elements (n + 1)

                  · -- native 区：读 data——与 hbranch（alpha/beta）矛盾

                      exfalso

                      have hcell : cfg₀.tape (2 + (k : ℤ) + (i : ℤ)) = tape₀ (2 + (k : ℤ) + (i : ℤ)) := hsecond i ⟨by omega, by omega⟩

                      have hkrange := encodeElementsSym_kind_data_of_prefixRange inst.elements n i hi_gt hi_lt' hnlt

                      have hta := htape_elems_orig i (by omega : i < len)

                      rw [← hta] at hkrange

                      rw [← hcell] at hkrange

                      rcases hkrange with hk | hk <;> rcases hbranch with hα | hβ

                      · cases (hk.symm.trans (by simpa [hhead₂] using hα))

                      · cases (hk.symm.trans (by simpa [hhead₂] using hβ))

                      · cases (hk.symm.trans (by simpa [hhead₂] using hα))

                      · cases (hk.symm.trans (by simpa [hhead₂] using hβ))

                  · -- i = 左界(n+1)：元素 n+1 的标记格——sel.set (n+1) true、产出 n+2

                      have hi_eq' : i = elemsPrefixLen inst.elements (n + 1) := le_antisymm hpref2 (by omega)

                      have hn1lt : n + 1 < inst.elements.length := by

                        by_contra h

                        have hn1_eq : n + 1 = inst.elements.length := by omega

                        rw [hn1_eq] at hi_eq'

                        rw [elemsPrefixLen_eq_len_of_eq inst.elements inst.elements.length rfl, ← hlen_eq] at hi_eq'

                        omega

                      let sel' : List Bool := sel.set (n + 1) false

                      right; right; left

                      refine ⟨by rw [hres]; rfl, sel', n + 1, i + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

                      · dsimp [sel']

                        rw [List.length_set]

                        exact hsel_len

                      · omega

                      · -- hpref1'：左界(n+1) ≤ i+1

                        rw [hi_eq']

                        omega

                      · -- hpref2'：i+1 ≤ 左界(n+2)

                        rw [hi_eq']

                        have hsucc3 := elemsPrefixLen_succ inst.elements (n + 1) hn1lt

                        rw [hsucc3]

                        omega

                      · dsimp [symStepConfig]

                        rw [hhead₂, hres]

                        norm_num [Dir.toInt]

                        omega

                      · intro j hj

                        by_cases hj_eq : (j = i)

                        · -- j = i 分支（hj_eq 保留）

                          have hws_len' : (encodeElementsSymWithSel inst.elements sel').length = len := by
                            rw [WithSel_length inst.elements sel' (by
                              dsimp [sel']
                              rw [List.length_set]
                              exact hsel_len)]

                          have hmv : (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements (n + 1)]'(by
                            rw [hws_len']
                            have hlt' := elemsPrefixLen_lt_len_of_lt inst.elements n hn1lt
                            rw [← hlen_eq] at hlt'
                            exact hlt') = Sym.nosel := by

                            rw [encodeElementsSymWithSel_mark_val inst.elements sel' (by

                              dsimp [sel']

                              rw [List.length_set]

                              exact hsel_len) (n + 1) hn1lt]

                            dsimp [sel']

                            rw [List.getElem_set_self]

                            simp

                          dsimp [symStepConfig]

                          rw [hres]

                          rw [hhead₂]

                          rw [if_pos (by rw [hj_eq])]

                          rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                            rw [List.length_take]
                            exact Nat.lt_min.mpr ⟨by omega, by
                              have hlenws_tk : (encodeElementsSymWithSel inst.elements sel').length = len := by
                                rw [WithSel_length inst.elements sel' (by dsimp [sel']; rw [List.length_set]; exact hsel_len)]
                              rw [hlenws_tk]
                              omega⟩)]
                          
                          rw [show (encodeElementsSymWithSel inst.elements sel')[j] = (encodeElementsSymWithSel inst.elements sel')[elemsPrefixLen inst.elements (n + 1)] from by
                          congr
                          rw [hj_eq]
                          exact hi_eq']

                          exact hmv.symm

                        · have hj_lt : j < i := by
                            rw [List.length_take] at hj
                            have hjle : j < i + 1 := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
                            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjle) hj_eq

                          have hfirst_j := hfirst j (by

                            rw [List.length_take]

                            refine Nat.lt_min.mpr ⟨hj_lt, by
                              have hlenws' : (encodeElementsSymWithSel inst.elements sel).length = len := by
                                rw [WithSel_length inst.elements sel hsel_len]
                              rw [hlenws']
                              omega⟩)

                          rw [show (symStepConfig cfg₀ step.result).tape (2 + (k : ℤ) + (j : ℤ)) = cfg₀.tape (2 + (k : ℤ) + (j : ℤ)) from by

                            dsimp [symStepConfig]

                            have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                              rw [hhead₂]

                              omega

                            simp [hne]]

                          rw [hfirst_j]

                          have hlenws_j : (encodeElementsSymWithSel inst.elements sel).length = len := by
                            rw [WithSel_length inst.elements sel hsel_len]
                          have hget1 : ((encodeElementsSymWithSel inst.elements sel).take i)[j]'(by
                            rw [List.length_take]
                            refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩) =
                            (encodeElementsSymWithSel inst.elements sel)[j]'(by rw [hlenws_j]; omega) := by
                            exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i) (i := j) (h := by
                              rw [List.length_take]
                              refine Nat.lt_min.mpr ⟨hj_lt, by rw [hlenws_j]; omega⟩)

                          have hlenws_j : (encodeElementsSymWithSel inst.elements sel').length = len := by
                            rw [WithSel_length inst.elements sel' (by dsimp [sel']; rw [List.length_set]; exact hsel_len)]
                          have hget2 : ((encodeElementsSymWithSel inst.elements sel').take (i + 1))[j]'(by
                            rw [List.length_take]
                            refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩) =
                            (encodeElementsSymWithSel inst.elements sel')[j]'(by rw [hlenws_j]; omega) := by
                            exact List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel') (j := i + 1) (i := j) (h := by
                              rw [List.length_take]
                              refine Nat.lt_min.mpr ⟨by omega, by rw [hlenws_j]; omega⟩)

                          rw [hget1, hget2]

                          exact (encodeElementsSymWithSel_set_eq_of_lt inst.elements sel hsel_len (n + 1) false j (by

                            rw [← hi_eq']

                            exact hj_lt)).symm

                      · intro j hj

                        dsimp [symStepConfig]

                        have hne : 2 + (k : ℤ) + (j : ℤ) ≠ cfg₀.headPos := by

                          rw [hhead₂]

                          omega

                        simpa [hres, hne] using hsecond j ⟨by omega, hj.2⟩

                      · intro j hj

                        dsimp [symStepConfig]

                        have hne : j ≠ cfg₀.headPos := by

                          rw [hhead₂]

                          omega

                        simpa [hres, hne] using hleft₂ j hj

                      · intro j hj

                        dsimp [symStepConfig]

                        have hne : j ≠ cfg₀.headPos := by

                          rw [hhead₂]

                          omega

                        simpa [hres, hne] using hright₂ j hj

                      · dsimp [symStepConfig]

                        have hne : 2 + (k : ℤ) + (len : ℤ) ≠ cfg₀.headPos := by

                          rw [hhead₂]

                          omega

                        simpa [hres, hne] using hhash₂

            · -- 2 → 3：读 boundary，不动右移

              rcases hnext3 with h3x | h101

              · -- 2 → 3：读 boundary，不动右移

                  rcases trans2_next3 (cfg₀.tape cfg₀.headPos) step.result hmem h3x with ⟨hbnd, hres⟩

                  have hi_eq : i = len := by

                    by_cases hi_lt : i < len

                    · exfalso

                      have hcell : cfg₀.tape (2 + (k : ℤ) + (i : ℤ)) = tape₀ (2 + (k : ℤ) + (i : ℤ)) := hsecond i ⟨by omega, by omega⟩

                      have hta : (tape₀ (2 + (k : ℤ) + (i : ℤ))).1 ≠ SymKind.boundary := by

                        rw [show tape₀ (2 + (k : ℤ) + (i : ℤ)) = (encodeElementsSym inst.elements)[i] from

                          htape_elems_orig i (by simpa [hlen_eq] using hi_lt)]

                        exact encodeElementsSym_nonboundary (encodeBitsSym inst.target).length inst.elements ((encodeElementsSym inst.elements)[i]) (List.getElem_mem (by

                          simpa [hlen_eq] using hi_lt))

                      rw [← hcell] at hta

                      exact (hta (by simpa [hhead₂] using hbnd)).elim

                    · exact le_antisymm hi (by omega)

                  have hcfgtape : (symStepConfig cfg₀ step.result).tape = cfg₀.tape := by

                    dsimp [symStepConfig]

                    rw [hres]

                    funext x

                    by_cases hx : x = cfg₀.headPos

                    · subst hx

                      have hsym : cfg₀.tape cfg₀.headPos = Sym.boundary := by

                        rw [hhead₂, hi_eq]

                        rw [hsecond len ⟨by omega, by omega⟩]

                        exact hbound1_k

                      rw [hsym]

                      by_cases hxx : cfg₀.headPos = cfg₀.headPos <;> simp [hxx, hsym]

                    · simp [hx]

                  right; right; right; left

                  refine ⟨by rw [hres]; rfl, sel, hsel_len, ?_, ?_, ?_, ?_, ?_⟩

                  · -- hhead：headPos = 2+k+len

                    dsimp [symStepConfig]

                    rw [hhead₂, hi_eq, hres]

                    norm_num [Dir.toInt]

                  · -- hfirst：tapeAgrees (2+k) (WithSel 全串)——take i = 全串（i = len）

                    intro j hj

                    have hj_lt : j < i := by

                      rw [WithSel_length inst.elements sel hsel_len, ← hlen_eq] at hj

                      omega

                    have hfirst_j := hfirst j (by

                      rw [List.length_take]

                      exact Nat.lt_min.mpr ⟨hj_lt, by omega⟩)

                    rw [show (symStepConfig cfg₀ step.result).tape (2 + ↑k + ↑j) = cfg₀.tape (2 + ↑k + ↑j) from by

                      dsimp [symStepConfig]

                      have hne : 2 + ↑k + ↑j ≠ cfg₀.headPos := by

                        rw [hhead₂, hi_eq]

                        omega

                      simp [hne]]

                    rw [hfirst_j]

                    rw [List.getElem_take (xs := encodeElementsSymWithSel inst.elements sel) (j := i) (i := j) (h := by
                      rw [List.length_take]
                      exact Nat.lt_min.mpr ⟨by omega, by
                        have hlenws_tk : (encodeElementsSymWithSel inst.elements sel).length = len := by
                          rw [WithSel_length inst.elements sel hsel_len]
                        rw [hlenws_tk]
                        omega⟩)]

                  · intro j hj

                    rw [show (symStepConfig cfg₀ step.result).tape j = cfg₀.tape j from by

                      dsimp [symStepConfig]

                      have hne : j ≠ cfg₀.headPos := by

                        rw [hhead₂, hi_eq]

                        omega

                      simp [hne]]

                    exact hleft₂ j hj

                  · intro j hj

                    rw [show (symStepConfig cfg₀ step.result).tape j = cfg₀.tape j from by

                      dsimp [symStepConfig]

                      have hne : j ≠ cfg₀.headPos := by

                        rw [hhead₂, hi_eq]

                        omega

                      simp [hne]]

                    exact hright₂ j hj

                  · have hcfgtape : (symStepConfig cfg₀ step.result).tape (2 + ↑k + ↑len) = cfg₀.tape (2 + ↑k + ↑len) := by

                      dsimp [symStepConfig]

                      rw [hres]

                      have hx : 2 + ↑k + ↑len = cfg₀.headPos := by

                        rw [hhead₂, hi_eq]

                      have hb : cfg₀.tape cfg₀.headPos = Sym.boundary := by

                        rw [← hx]

                        rw [show cfg₀.tape (2 + (k : ℤ) + (len : ℤ)) = tape₀ (2 + (k : ℤ) + (len : ℤ)) from hsecond len ⟨by omega, by omega⟩]

                        exact hbound1_k

                      rw [hx]

                      by_cases hxx : cfg₀.headPos = cfg₀.headPos

                      · simp [hxx]

                      · exact (hxx rfl).elim

                    rw [hcfgtape]

                    exact hhash₂.trans hbound1_k

              · -- 2 → 101：读 data/标记异常——拒绝（101 吸收）

                  right; right; right; right; right; right

                  exact by simpa [symStepConfig] using h101

        · -- 3 → 24 / 3 → 101（新表：3 读 #₁ 未标记 → 24 格式检查；已标记 → 101）

            rcases hs3 with ⟨hs3', sel, hsel_len, hhead₃, hfirst₃, hleft₃, hright₃, hhash₃⟩

            have hmem : step.result ∈ VerifierSym.transition (3, cfg₀.tape cfg₀.headPos) := by

              simpa [hs3'] using h_trans

            rcases trans3_next3_or_4 (cfg₀.tape cfg₀.headPos) step.result hmem with hnext24 | hnext101

            · -- 3 → 24：写 (boundary,true) 左移——#₁ 标记——进入格式检查

              have hread₃ : cfg₀.tape cfg₀.headPos = Sym.boundary := by
                rw [hhead₃]
                exact hhash₃
              have hres : step.result = SymTransResult.mk 24 (Sym.mk SymKind.boundary true) Dir.L := by
                have hmem' : step.result ∈ VerifierSym.transition (3, Sym.boundary) := by
                  simpa [hread₃] using hmem
                exact trans3_hash1 step.result hmem'

              have hcfgtape : (symStepConfig cfg₀ step.result).tape = Function.update cfg₀.tape cfg₀.headPos (Sym.mk SymKind.boundary true) := by

                dsimp [symStepConfig]

                rw [hres]

                funext x

                by_cases hx : x = cfg₀.headPos <;> simp [hx]

              have hlenws : (encodeElementsSymWithSel inst.elements sel).length = len := by

                simpa [hlen_eq] using (WithSel_length inst.elements sel hsel_len)

              right; right; right; right; left

              refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

              · dsimp [symStepConfig]; rw [hres]; left
                constructor
                · rfl
                · -- 24 的 headPos = 2+k+len-1（3 的 headPos 左移 1）
                  norm_num [Dir.toInt]
                  rw [hhead₃]
                  omega



              · intro j hj

                rw [hcfgtape]

                by_cases hj_eq : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos

                · exfalso

                  rw [hhead₃] at hj_eq

                  have hj_len : (j : ℤ) < (len : ℤ) := by

                    have hj' : j < len := by simpa [hlenws] using hj

                    exact_mod_cast hj'

                  omega

                · simp [hj_eq]

                  exact hfirst₃ j (by simpa [hlenws] using hj)

              · intro j hj

                rw [hcfgtape]

                by_cases hj_eq : j = cfg₀.headPos

                · exfalso

                  rw [hhead₃] at hj_eq

                  omega

                · simp [hj_eq]

                  exact hleft₃ j hj

              · intro j hj

                rw [hcfgtape]

                by_cases hj_eq : j = cfg₀.headPos

                · exfalso

                  rw [hhead₃] at hj_eq

                  omega

                · simp [hj_eq]

                  exact hright₃ j hj

              · rw [hcfgtape]

                rw [hhead₃]

                simp

            · -- 3 → 101：读已标记 #₁——与 hhash₃（未标记）矛盾

              exfalso

              have hread₃ : cfg₀.tape cfg₀.headPos = Sym.boundary := by

                rw [hhead₃]

                exact hhash₃

              have hmem' : step.result ∈ VerifierSym.transition (3, Sym.boundary) := by

                simpa [hread₃] using hmem

              have h24 := trans3_hash1 step.result hmem'

              rw [h24] at hnext101

              nomatch hnext101



        · -- 格式检查链：cfg₀.state ∈ {24,26,27,29,38,28}——写回原符号，沿链步进

            rcases hs4fmt with ⟨hst, sel, hsel_len, hchosen, hleft, hright, hhash⟩

            rcases hst with h24 | h26 | h27 | h29 | h38 | h28

            · -- 24：读 (data1,false) → 29 L；否则 101

              rcases h24 with ⟨h24, h24p⟩
              have hmem' : step.result ∈ VerifierSym.transition (24, cfg₀.tape cfg₀.headPos) := by
                simpa [h24] using h_trans
              rcases trans24_step (cfg₀.tape cfg₀.headPos) step.result hmem' with h29' | h101'
              · rcases h29' with ⟨hk, hm, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; left
                  constructor
                  · rfl
                  · -- 29 的 headPos ∈ [1+k, 2+k+len-2]：24 在 2+k+len-1 左移；len ≥ 1
                    norm_num [Dir.toInt]
                    rw [h24p]
                    constructor
                    · -- 1+k ≤ 2+k+len-2：len ≥ 1（len = 0 → 24 读的是 #₀ boundary，非 data1）
                      have hlen1 : 1 ≤ (len : ℤ) := by
                        by_contra hlen0
                        have hlen_nonneg : 0 ≤ (len : ℤ) := by dsimp [len, elems]; omega
                        have hlen0' : (len : ℤ) = 0 := by omega
                        have hpk : cfg₀.headPos = 1 + (k : ℤ) := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ (1 + (k : ℤ)) := by
                          rw [hpk]
                          exact hleft (1 + (k : ℤ)) (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, hbound0_k]
                          rfl
                        rw [hk] at hd
                        cases hd
                      omega
                    · omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · right; right; right; right; right; right
                exact by dsimp [symStepConfig]; exact h101'

            · -- 26：读 (data1,false) → 29 L；读 boundary → 27 L；否则 101

              rcases h26 with ⟨h26, h26p⟩
              have hmem' : step.result ∈ VerifierSym.transition (26, cfg₀.tape cfg₀.headPos) := by
                simpa [h26] using h_trans
              rcases trans26_step (cfg₀.tape cfg₀.headPos) step.result hmem' with h29' | h27' | h101'
              · rcases h29' with ⟨hk, hm, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; left
                  constructor
                  · rfl
                  · -- 29 的界：26 读 data1 → p ≥ 2+k（p = 1+k 是 #₀）
                    norm_num [Dir.toInt]
                    rcases h26p with ⟨h26lo, h26hi⟩
                    constructor
                    · have hp2 : 2 + (k : ℤ) ≤ cfg₀.headPos := by
                        by_contra hpnot
                        have hp1 : cfg₀.headPos = 1 + (k : ℤ) := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ (1 + (k : ℤ)) := by
                          rw [hp1]
                          exact hleft (1 + (k : ℤ)) (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, hbound0_k]
                          rfl
                        rw [hk] at hd
                        cases hd
                      omega
                    · omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · rcases h27' with ⟨hb, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; left
                  constructor
                  · rfl
                  · -- 27 的 headPos = 1+k-1：26 读 boundary 必在 1+k（elems 区无 boundary）
                    norm_num [Dir.toInt]
                    rcases h26p with ⟨h26lo, h26hi⟩
                    have hp1 : cfg₀.headPos = 1 + (k : ℤ) := by
                      by_contra hpnot
                      have hge : 2 + (k : ℤ) ≤ cfg₀.headPos := by omega
                      have hj0 : 0 ≤ cfg₀.headPos - (2 + (k : ℤ)) := by omega
                      have hjlen : cfg₀.headPos - (2 + (k : ℤ)) < (len : ℤ) := by omega
                      have hjlen' : (cfg₀.headPos - (2 + (k : ℤ))).toNat < len := by
                        dsimp [len, elems] at hjlen ⊢
                        exact Int.ofNat_lt.mp (show ((cfg₀.headPos - (2 + (k : ℤ))).toNat : ℤ) < (len : ℤ) from by
                          rw [Int.toNat_of_nonneg hj0]
                          exact hjlen)
                      have hlenws : (encodeElementsSymWithSel inst.elements sel).length = len := by
                        simpa [hlen_eq] using (WithSel_length inst.elements sel hsel_len)
                      have ht := hchosen (cfg₀.headPos - (2 + (k : ℤ))).toNat (by
                        rw [hlenws]
                        exact hjlen')
                      have hcast : ((cfg₀.headPos - (2 + (k : ℤ))).toNat : ℤ) = cfg₀.headPos - (2 + (k : ℤ)) := by
                        exact Int.toNat_of_nonneg hj0
                      have hpos : 2 + (k : ℤ) + ((cfg₀.headPos - (2 + (k : ℤ))).toNat : ℤ) = cfg₀.headPos := by omega
                      have htp : cfg₀.tape cfg₀.headPos = (encodeElementsSymWithSel inst.elements sel)[(cfg₀.headPos - (2 + (k : ℤ))).toNat]'(by
                        rw [hlenws]
                        exact hjlen') := by
                        rw [hpos] at ht
                        exact ht
                      have hkind := encodeElementsSymWithSel_kind inst.elements sel ((encodeElementsSymWithSel inst.elements sel)[(cfg₀.headPos - (2 + (k : ℤ))).toNat]'(by
                        rw [hlenws]
                        exact hjlen')) (by simp)
                      rw [htp] at hb
                      rcases hkind with hk1 | hk2 | hk3 | hk4
                      · rw [hk1] at hb; cases hb
                      · rw [hk2] at hb; cases hb
                      · rw [hk3] at hb; cases hb
                      · rw [hk4] at hb; cases hb
                    omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · right; right; right; right; right; right
                exact by dsimp [symStepConfig]; exact h101'

            · -- 27：读 (data1,false) → 38 L；否则 101

              rcases h27 with ⟨h27, h27p⟩
              have hmem' : step.result ∈ VerifierSym.transition (27, cfg₀.tape cfg₀.headPos) := by
                simpa [h27] using h_trans
              rcases trans27_step (cfg₀.tape cfg₀.headPos) step.result hmem' with h38' | h101'
              · rcases h38' with ⟨hk, hm, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; right; left
                  constructor
                  · rfl
                  · -- 38 的界：27 在 1+k-1 读 data1 → k ≥ 1
                    norm_num [Dir.toInt]
                    rw [h27p]
                    constructor
                    · -- 0 ≤ 1+k-2：k ≥ 1（k = 0 → 27 读的是 #ₗ boundary，非 data1）
                      have hk1 : 1 ≤ (k : ℤ) := by
                        by_contra hk0
                        have hknn : 0 ≤ (k : ℤ) := by dsimp [k, target]; omega
                        have hk0' : (k : ℤ) = 0 := by omega
                        have hp0 : cfg₀.headPos = 0 := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ 0 := by
                          rw [hp0]
                          exact hleft 0 (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, htape0]
                          rfl
                        rw [hk] at hd
                        cases hd
                      omega
                    · omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · right; right; right; right; right; right
                exact by dsimp [symStepConfig]; exact h101'

            · -- 29：读 data → 29 L；读 sel/nosel → 26 L；否则 101

              rcases h29 with ⟨h29, h29p⟩
              have hmem' : step.result ∈ VerifierSym.transition (29, cfg₀.tape cfg₀.headPos) := by
                simpa [h29] using h_trans
              rcases trans29_step (cfg₀.tape cfg₀.headPos) step.result hmem' with h29' | h26' | h101'
              · rcases h29' with ⟨hk, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; left
                  constructor
                  · rfl
                  · -- 29 的界：p ≥ 2+k（p = 1+k 是 #₀，读不到 data）
                    norm_num [Dir.toInt]
                    rcases h29p with ⟨h29lo, h29hi⟩
                    constructor
                    · have hp2 : 2 + (k : ℤ) ≤ cfg₀.headPos := by
                        by_contra hpnot
                        have hp1 : cfg₀.headPos = 1 + (k : ℤ) := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ (1 + (k : ℤ)) := by
                          rw [hp1]
                          exact hleft (1 + (k : ℤ)) (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, hbound0_k]
                          rfl
                        rcases hk with hd0 | hd1
                        · rw [hd0] at hd; cases hd
                        · rw [hd1] at hd; cases hd
                      omega
                    · omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · rcases h26' with ⟨hk, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; left
                  constructor
                  · rfl
                  · -- 26 的界：p ≥ 2+k（sel/nosel 只在 elems 区）
                    norm_num [Dir.toInt]
                    rcases h29p with ⟨h29lo, h29hi⟩
                    constructor
                    · have hp2 : 2 + (k : ℤ) ≤ cfg₀.headPos := by
                        by_contra hpnot
                        have hp1 : cfg₀.headPos = 1 + (k : ℤ) := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ (1 + (k : ℤ)) := by
                          rw [hp1]
                          exact hleft (1 + (k : ℤ)) (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, hbound0_k]
                          rfl
                        rcases hk with hd0 | hd1
                        · rw [hd0] at hd; cases hd
                        · rw [hd1] at hd; cases hd
                      omega
                    · omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · right; right; right; right; right; right
                exact by dsimp [symStepConfig]; exact h101'

            · -- 38：读 data → 38 L；读 boundary → 28 R；否则 101

              rcases h38 with ⟨h38, h38p⟩
              have hmem' : step.result ∈ VerifierSym.transition (38, cfg₀.tape cfg₀.headPos) := by
                simpa [h38] using h_trans
              rcases trans38_step (cfg₀.tape cfg₀.headPos) step.result hmem' with h38' | h28' | h101'
              · rcases h38' with ⟨hk, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; right; left
                  constructor
                  · rfl
                  · -- 38 的界：p ≥ 1（p = 0 是 #ₗ，读不到 data）
                    norm_num [Dir.toInt]
                    rcases h38p with ⟨h38lo, h38hi⟩
                    constructor
                    · have hp1 : 1 ≤ cfg₀.headPos := by
                        by_contra hpnot
                        have hp0 : cfg₀.headPos = 0 := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ 0 := by
                          rw [hp0]
                          exact hleft 0 (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, htape0]
                          rfl
                        rcases hk with hd0 | hd1
                        · rw [hd0] at hd; cases hd
                        · rw [hd1] at hd; cases hd
                      omega
                    · omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · rcases h28' with ⟨hb, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; right; right
                  constructor
                  · rfl
                  · -- 28 的界：38 的 p ∈ [0, 1+k-2] → p+1 ∈ [1, 1+k]
                    norm_num [Dir.toInt]
                    rcases h38p with ⟨h38lo, h38hi⟩
                    constructor <;> omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · right; right; right; right; right; right
                exact by dsimp [symStepConfig]; exact h101'

            · -- 28：读 data → 28 R；读 boundary → 4 R；否则 101

              rcases h28 with ⟨h28, h28p⟩
              have hmem' : step.result ∈ VerifierSym.transition (28, cfg₀.tape cfg₀.headPos) := by
                simpa [h28] using h_trans
              rcases trans28_step (cfg₀.tape cfg₀.headPos) step.result hmem' with h28' | h4' | h101'
              · rcases h28' with ⟨hk, hres⟩
                right; right; right; right; left
                refine ⟨?_, sel, hsel_len, ?_, ?_, ?_, ?_⟩

                · dsimp [symStepConfig]; rw [hres]; right; right; right; right; right
                  constructor
                  · rfl
                  · -- 28 的界：p+1 ≤ 1+k（p = 1+k 读的是 #₀，非 data）
                    norm_num [Dir.toInt]
                    rcases h28p with ⟨h28lo, h28hi⟩
                    constructor
                    · omega
                    · have hpk : cfg₀.headPos ≤ (k : ℤ) := by
                        by_contra hpnot
                        have hp1 : cfg₀.headPos = 1 + (k : ℤ) := by omega
                        have ht : cfg₀.tape cfg₀.headPos = tape₀ (1 + (k : ℤ)) := by
                          rw [hp1]
                          exact hleft (1 + (k : ℤ)) (by omega)
                        have hd : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          rw [ht, hbound0_k]
                          rfl
                        rcases hk with hd0 | hd1
                        · rw [hd0] at hd; cases hd
                        · rw [hd1] at hd; cases hd
                      omega

                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · rcases h4' with ⟨hb, hres⟩
                right; right; right; right; right; left
                refine ⟨by dsimp [symStepConfig]; rw [hres], sel, hsel_len, ?_, ?_, ?_, ?_, ?_⟩
                · -- headPos = 2+k：28 读 boundary 必在 #₀（1+k）
                  dsimp [symStepConfig]; rw [hres]; norm_num [Dir.toInt]
                  rcases h28p with ⟨h28lo, h28hi⟩
                  have hp1 : cfg₀.headPos = 1 + (k : ℤ) := by
                    by_contra hpnot
                    have hlt : cfg₀.headPos < 1 + (k : ℤ) := by omega
                    have ht : cfg₀.tape cfg₀.headPos = tape₀ cfg₀.headPos := hleft cfg₀.headPos (by omega)
                    have hb₀ : (tape₀ cfg₀.headPos).1 = SymKind.boundary := by
                      rw [← ht]
                      exact hb
                    have hpn : 0 ≤ cfg₀.headPos - 1 := by omega
                    have hpk : cfg₀.headPos - 1 < (k : ℤ) := by omega
                    have htl : (cfg₀.headPos - 1).toNat < target.length := by
                      dsimp [k, target] at hpk ⊢
                      exact Int.ofNat_lt.mp (show ((cfg₀.headPos - 1).toNat : ℤ) < (target.length : ℤ) from by
                        rw [Int.toNat_of_nonneg hpn]
                        exact hpk)
                    have htp := htape_target ((cfg₀.headPos - 1).toNat) (by
                      rw [List.length_append]
                      exact Nat.lt_succ_of_le (Nat.le_of_lt htl))
                    have hcast : ((cfg₀.headPos - 1).toNat : ℤ) = cfg₀.headPos - 1 := by
                      exact Int.toNat_of_nonneg hpn
                    have hrewrite : 1 + ((cfg₀.headPos - 1).toNat : ℤ) = cfg₀.headPos := by omega
                    rw [hrewrite] at htp
                    rw [List.getElem_append_left (as := target) htl] at htp
                    have hkind := encodeBitsSym_kind inst.target (cfg₀.headPos - 1).toNat htl
                    rw [htp] at hb₀
                    rcases hkind with hd0 | hd1
                    · rw [hd0] at hb₀; cases hb₀
                    · rw [hd1] at hb₀; cases hb₀
                  omega
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : 2 + (k : ℤ) + (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hchosen j hj)
                  · simpa [hx] using (hchosen j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hleft j hj)
                  · simpa [hx] using (hleft j hj)
                · intro j hj
                  dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (j : ℤ) = cfg₀.headPos
                  · simpa [hx] using (hright j hj)
                  · simpa [hx] using (hright j hj)
                · dsimp [symStepConfig]; rw [hres]
                  by_cases hx : (2 + (k : ℤ) + (len : ℤ) = cfg₀.headPos) <;> simpa [hx] using hhash
              · right; right; right; right; right; right
                exact by dsimp [symStepConfig]; exact h101'

        · -- 4：hno4 给出 cfg₀.state ≠ 4，与 4 情形矛盾

            exfalso

            rcases hs4 with ⟨hs, _, _, _, _, _, _, _⟩

            have hne4 : cfg₀.state ≠ 4 :=

              hno4 h_ind ⟨[step], by rw [List.append_cons, List.append_nil]⟩ (by

                simpa [List.length_append])

            rw [hs] at hne4

            exact (hne4 rfl).elim

        · -- 101：吸收

            right; right; right; right; right; right

            refine (by
              have hdec : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (101, s),
                  r.nextState = 101 := by
                intro s
                rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
              dsimp [symStepConfig]
              exact hdec (cfg₀.tape cfg₀.headPos) step.result (by
                simpa [hs101] using h_trans))


  -- 提取最终结论

  rcases hP with hs0 | hs1 | hs2 | hs3 | hs4fmt | hs4' | hs101

  · exfalso; rcases hs0 with ⟨hs, _, _⟩; rw [hs] at hs4; omega

  · exfalso; rcases hs1 with ⟨hs, _⟩; rw [hs] at hs4; omega

  · exfalso; rcases hs2 with ⟨hs, _⟩; rw [hs] at hs4; omega

  · exfalso; rcases hs3 with ⟨hs, _⟩; rw [hs] at hs4; omega

  · exfalso

    rcases hs4fmt with ⟨hs, _⟩

    rcases hs with h24 | h26 | h27 | h29 | h38 | h28

    · rcases h24 with ⟨h24, _⟩; rw [h24] at hs4; omega

    · rcases h26 with ⟨h26, _⟩; rw [h26] at hs4; omega

    · rcases h27 with ⟨h27, _⟩; rw [h27] at hs4; omega

    · rcases h29 with ⟨h29, _⟩; rw [h29] at hs4; omega

    · rcases h38 with ⟨h38, _⟩; rw [h38] at hs4; omega

    · rcases h28 with ⟨h28, _⟩; rw [h28] at hs4; omega

  · rcases hs4' with ⟨_, sel, hsel_len, hhead, hchosen, hleft, hright, hhash⟩

    refine ⟨sel, hsel_len, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhead]

      omega

    · intro i hi

      have hi' : (i : ℤ) < k := by

        rw [← hk_def]

        omega

      have hlt : 1 + (i : ℤ) < 2 + (k : ℤ) := by omega

      rw [show cfg.tape (1 + (i : ℤ)) = tape₀ (1 + (i : ℤ)) from hleft (1 + (i : ℤ)) hlt]

      have hcell := htape_target i (by rw [List.length_append]; omega : i < (target ++ [Sym.boundary]).length)

      rw [List.getElem_append_left (as := target) (by

        rw [← hk_def] at hi'

        exact_mod_cast hi')] at hcell

      simpa [target, k] using hcell

    · rw [show cfg.tape 0 = tape₀ 0 from hleft 0 (by omega)]

      exact htape0

    · rw [show cfg.tape (1 + (k : ℤ)) = tape₀ (1 + (k : ℤ)) from hleft (1 + (k : ℤ)) (by omega)]

      exact hbound0_k

    · simpa [k] using hchosen

    · have hlenws : (encodeElementsSymWithSel inst.elements sel).length = len := by

        simpa [hlen_eq] using (WithSel_length inst.elements sel hsel_len)

      rw [show 2 + (k : ℤ) + ((encodeElementsSymWithSel inst.elements sel).length : ℤ) = 2 + (k : ℤ) + (len : ℤ) from by

        rw [hlenws]]

      exact hhash
  · exfalso

    rw [hs101] at hs4

    omega


/-- 路径终点 < 4 → 一切真前缀终点 < 4。 -/
lemma prefix_states_lt4 {input : List Sym} {π : List SymStep} {cfg : SymConfig}

    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)

    (hlt : cfg.state < 4) :

    ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},

      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →

      (∃ ρ, π = π₀ ++ ρ) → π₀ ≠ π → cfg₀.state < 4 := by

  induction h with

  | nil =>

      intro π₀ cfg₀ h₀ hpre hne

      rcases hpre with ⟨ρ, hρ⟩

      exfalso

      have hπ₀ : π₀ = [] := by

        have hlen : π₀.length + ρ.length = 0 := by

          simpa [List.length_append] using congrArg List.length hρ.symm

        exact List.eq_nil_of_length_eq_zero (by omega)

      exact hne hπ₀

  | cons π₁ step cfg₁ h_ind h_from h_read h_trans ih =>

      intro π₀ cfg₀ h₀ hpre hne

      have hcfg₁lt : cfg₁.state < 4 := by

        have hrange := reachable_state_in_range h_ind

        have hnext : step.result.nextState < 4 := by

          simpa [symStepConfig] using hlt

        exact transition_nextState_lt4_of_lt4 cfg₁.state (cfg₁.tape cfg₁.headPos) step.result

          (by

            have hdec : ∀ q ∈ VerifierSym.legalStates, q ≤ 101 := by decide

            exact hdec cfg₁.state hrange)

          h_trans hnext

      rcases hpre with ⟨ρ, hρ⟩

      have hsplit := List.append_eq_append_iff.mp hρ

      rcases hsplit with ⟨as, hπ₀as, hstepas⟩ | ⟨bs, hπ₁bs, hρbs⟩

      · cases as with

        | nil =>

            subst hπ₀as

            simp at h₀

            have hcfg₀ := SymSteps_cfg_eq h₀ h_ind

            rw [hcfg₀]

            exact hcfg₁lt

        | cons a as' =>

            exfalso

            have hlen : as'.length + ρ.length = 0 := by

              have hlen1 : (a :: as' ++ ρ).length = 1 := by

                rw [← hstepas]

                simp

              simpa [List.length_append, List.length_cons] using hlen1

            have has' : as' = [] := List.eq_nil_of_length_eq_zero (by omega)

            have hρ0 : ρ = [] := List.eq_nil_of_length_eq_zero (by omega)

            subst has'

            subst hρ0

            subst hπ₀as

            simp at hstepas

            subst hstepas

            exact hne rfl

      · by_cases hπ₀eq : π₀ = π₁

        · subst hπ₀eq

          have hcfg₀ := SymSteps_cfg_eq h₀ h_ind

          rw [hcfg₀]

          exact hcfg₁lt

        · exact (@ih hcfg₁lt π₀ cfg₀ h₀ ⟨bs, hπ₁bs⟩ hπ₀eq)

/-- 路径终点 < 4 → 一切严格更短前缀终点 < 4（长度形式）。 -/

lemma prefix_states_lt4_len {input : List Sym} {π : List SymStep} {cfg : SymConfig}

    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)

    (hlt : cfg.state < 4) :

    ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},

      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →

      (∃ ρ, π = π₀ ++ ρ) → π₀.length < π.length → cfg₀.state ≠ 4 := by

  intro π₀ cfg₀ h₀ hpre hlen

  exact (by

    have hlt' : cfg₀.state < 4 := prefix_states_lt4 h hlt h₀ hpre (by

      intro hπ₀

      rw [hπ₀] at hlen

      omega)

    omega)

/-- 前驱终点 < 4 时，追加一步后的一切严格短前缀终点 < 4。 -/

lemma prefix_states_lt4_cons {input : List Sym} {π₀ : List SymStep} {cfg₀ : SymConfig}

    {step : SymStep}

    (h₀ : SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀)

    (hlt₀ : cfg₀.state < 4) :

    ∀ {π' : List SymStep} {cfg' : SymConfig},

      SymSteps VerifierSym.transition (symInitialConfig input) π' cfg' →

      (∃ ρ, π₀ ++ [step] = π' ++ ρ) → π'.length < (π₀ ++ [step]).length → cfg'.state < 4 := by

  intro π' cfg' h' hpre hlen

  have hlen' : π'.length ≤ π₀.length := by

    rcases hpre with ⟨ρ, hρ⟩

    have hlen_eq : π₀.length + 1 = π'.length + ρ.length := by

      simpa [List.length_append] using congrArg List.length hρ

    have hlen'' : π'.length < π₀.length + 1 := by

      simpa [List.length_append] using hlen

    omega

  by_cases hfull : π'.length = π₀.length

  · rcases hpre with ⟨ρ, hρ⟩

    cases ρ with

    | nil =>

        exfalso

        have hlenρ0 : π₀.length + 1 = π'.length := by

          simpa using congrArg List.length hρ

        omega

    | cons x ρ' =>

        have hρ'len : ρ'.length = 0 := by

          have hlenρ' : π₀.length + 1 = π'.length + (ρ'.length + 1) := by

            simpa [List.length_append, List.length_cons] using congrArg List.length hρ

          omega

        have hρ'nil : ρ' = [] := List.eq_nil_of_length_eq_zero hρ'len

        subst hρ'nil

        have htail := append_right_cancel (α := SymStep) hρ

        rcases htail with ⟨hπ'eq, _⟩

        subst hπ'eq

        have hcfg'eq : cfg' = cfg₀ := SymSteps_cfg_eq h' h₀

        rw [hcfg'eq]

        exact hlt₀

  · have hpre₀ : ∃ ρ₀, π₀ = π' ++ ρ₀ := by

      rcases hpre with ⟨ρ, hρ⟩

      have hsplit := List.append_eq_append_iff.mp hρ

      rcases hsplit with ⟨as, h₁, _⟩ | ⟨bs, h₃, _⟩

      · exfalso

        have hlenas : as.length = 0 := by

          have hlen₁ : π'.length = π₀.length + as.length := by

            simpa [List.length_append] using congrArg List.length h₁

          omega

        have has : as = [] := List.eq_nil_of_length_eq_zero hlenas

        subst has

        exact (hfull (by simpa using congrArg List.length h₁)).elim

      · exact ⟨bs, h₃⟩

    · exact prefix_states_lt4 h₀ hlt₀ h' hpre₀ (by

        intro hπ'

        rw [hπ'] at hfull

        exact hfull rfl)

/-- 23 左扫全 data0 到 #ₗ → 100（正向构造）。 -/
lemma scan23_to_100 (p : ℤ) (tape : ℤ → Sym) (hp : 0 ≤ p)
    (hbound : tape 0 = Sym.boundary)
    (hdata : ∀ i : ℤ, 0 < i ∧ i ≤ p → tape i = Sym.data0) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 23 tape p) π cfg' ∧ cfg'.state = 100 := by
  let n := p.toNat
  have hpn : (n : ℤ) = p := by dsimp [n]; exact Int.toNat_of_nonneg hp
  revert hpn
  induction n generalizing p with
  | zero =>
      intro hpn
      have hp0 : p = 0 := by simpa using hpn.symm
      subst p
      let r : SymTransResult := { nextState := 100, writeSym := Sym.boundary, moveDir := Dir.R }
      let step : SymStep := { fromState := 23, readSym := Sym.boundary, result := r }
      refine ⟨[step], symStepConfig (SymConfig.mk 23 tape 0) step.result, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 23 tape 0) SymSteps.nil rfl ?_ ?_
        · simp [SymConfig.mk, step, hbound]
        · simp [SymConfig.mk, step, hbound]
          decide
      · rfl
  | succ n ih =>
      intro hpn
      have hp_gt : 0 < p := by
        rw [← hpn]
        omega
      have hd : tape p = Sym.data0 := hdata p ⟨by omega, by omega⟩
      let r : SymTransResult := { nextState := 23, writeSym := Sym.data0, moveDir := Dir.L }
      let step : SymStep := { fromState := 23, readSym := Sym.data0, result := r }
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 23 tape p) [step] (symStepConfig (SymConfig.mk 23 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 23 tape p) SymSteps.nil rfl ?_ ?_
        · simp [SymConfig.mk, step, hd]
        · simp [SymConfig.mk, step, hd]
          decide
      have hcfg : symStepConfig (SymConfig.mk 23 tape p) step.result = SymConfig.mk 23 tape (p - 1) := by
        dsimp [symStepConfig]
        simp [SymConfig.mk, step, r, Dir.toInt, hd]
        constructor
        · funext x
          by_cases hx : x = p <;> simp [hx, hd]
        · omega
      rcases ih (p - 1) (by
        rw [← hpn]
        norm_num) (by
        intro i hi
        exact hdata i ⟨by omega, by omega⟩) (by omega) with ⟨π', cfg', hπ', hs100⟩
      refine ⟨step :: π', cfg', ?_, hs100⟩
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 23 tape p) (symStepConfig (SymConfig.mk 23 tape p) step.result) cfg' [step] π' hstep (by rw [hcfg]; exact hπ')

/-- 23 起点路径的状态闭合：只可能停在 23/100/101。 -/
lemma symSteps_23_closed {p : ℤ} {tape : ℤ → Sym} {π cfg}
    (h : SymSteps VerifierSym.transition (SymConfig.mk 23 tape p) π cfg) :
    cfg.state = 23 ∨ cfg.state = 100 ∨ cfg.state = 101 := by
  induction h with
  | nil =>
      simp [SymConfig.mk]
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      rcases ih with h23 | h100 | h101
      · have hdec : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (23, s),
            r.nextState = 23 ∨ r.nextState = 100 ∨ r.nextState = 101 := by
          intro s
          rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
        change (symStepConfig cfg₀ step.result).state = 23 ∨
          (symStepConfig cfg₀ step.result).state = 100 ∨ (symStepConfig cfg₀ step.result).state = 101
        dsimp [symStepConfig]
        exact hdec (cfg₀.tape cfg₀.headPos) step.result (by simpa [h23] using h_trans)
      · have hdec : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (100, s),
            r.nextState = 100 ∨ r.nextState = 101 := by
          intro s
          rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
        have hd := hdec (cfg₀.tape cfg₀.headPos) step.result (by simpa [h100] using h_trans)
        rcases hd with h100' | h101'
        · change (symStepConfig cfg₀ step.result).state = 23 ∨
            (symStepConfig cfg₀ step.result).state = 100 ∨ (symStepConfig cfg₀ step.result).state = 101
          dsimp [symStepConfig]
          exact Or.inr (Or.inl h100')
        · change (symStepConfig cfg₀ step.result).state = 23 ∨
            (symStepConfig cfg₀ step.result).state = 100 ∨ (symStepConfig cfg₀ step.result).state = 101
          dsimp [symStepConfig]
          exact Or.inr (Or.inr h101')
      · have hdec : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (101, s),
            r.nextState = 101 := by
          intro s
          rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
        change (symStepConfig cfg₀ step.result).state = 23 ∨
          (symStepConfig cfg₀ step.result).state = 100 ∨ (symStepConfig cfg₀ step.result).state = 101
        dsimp [symStepConfig]
        exact Or.inr (Or.inr (hdec (cfg₀.tape cfg₀.headPos) step.result (by simpa [h101] using h_trans)))

/-- 23 段不变量：终点为 23 时带不变、headPos 不增、扫过的格 kind 全 data0。 -/
lemma scan23_inv (p : ℤ) (tape : ℤ → Sym) {π cfg}
    (h : SymSteps VerifierSym.transition (SymConfig.mk 23 tape p) π cfg)
    (hs : cfg.state = 23) :
    cfg.tape = tape ∧ cfg.headPos ≤ p ∧
      ∀ i : ℤ, cfg.headPos < i ∧ i ≤ p → (tape i).1 = SymKind.data0 := by
  induction h with
  | nil =>
      constructor
      · simpa
      · constructor
        · simpa
        · intro i hi
          exfalso
          dsimp at hi
          omega
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      have hnext : step.result.nextState = 23 := by
        simpa [symStepConfig] using hs
      have hprev := prev_of_nextState_23 cfg₀.state (cfg₀.tape cfg₀.headPos) step.result h_trans hnext
      rcases hprev with h22 | h23'
      · exfalso
        have hinv : cfg₀.state = 23 ∨ cfg₀.state = 100 ∨ cfg₀.state = 101 := symSteps_23_closed h_ind
        rcases hinv with h23c | h100c | h101c
        · omega
        · omega
        · omega
      · rcases ih h23'.1 with ⟨htape, hpos₀, hdata⟩
        constructor
        · rw [← htape]
          dsimp [symStepConfig]
          funext x
          by_cases hx : x = cfg₀.headPos <;> simp [hx, h23'.2.2.1]
        · constructor
          · dsimp [symStepConfig]
            rw [h23'.2.2.2]
            simp [Dir.toInt]
            omega
          · intro i hi'
            have hpos : (symStepConfig cfg₀ step.result).headPos = cfg₀.headPos - 1 := by
              dsimp [symStepConfig]
              rw [h23'.2.2.2]
              simp [Dir.toInt]
              omega
            rw [hpos] at hi'
            by_cases hieq : i = cfg₀.headPos
            · subst i
              rw [← htape]
              exact h23'.2.1
            · have hge : cfg₀.headPos < i := by omega
              exact hdata i ⟨hge, hi'.2⟩

/-- 23 扫到 100 ⇒ 停在 boundary q 处且 (q, p] 的 kind 全 data0。 -/
lemma scan23_stop_boundary (p : ℤ) (tape : ℤ → Sym) {π cfg}
    (h : SymSteps VerifierSym.transition (SymConfig.mk 23 tape p) π cfg)
    (hs : cfg.state = 100) :
    ∃ q : ℤ, q ≤ p ∧ (tape q).1 = SymKind.boundary ∧
      ∀ i : ℤ, q < i ∧ i ≤ p → (tape i).1 = SymKind.data0 := by
  induction h with
  | nil =>
      exfalso
      change (SymConfig.mk 23 tape p).state = 100 at hs
      simp [SymConfig.mk] at hs
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      by_cases h100 : cfg₀.state = 100
      · exact ih h100
      · have hnext : step.result.nextState = 100 := by
          simpa [symStepConfig] using hs
        have hprev := prev_of_nextState_100 cfg₀.state (cfg₀.tape cfg₀.headPos) step.result h_trans hnext
        rcases hprev with h23 | h100'
        · rcases scan23_inv p tape h_ind h23.1 with ⟨htape, hpos₀, hdata₀⟩
          refine ⟨cfg₀.headPos, hpos₀, ?_, ?_⟩
          · rw [← htape]
            exact h23.2.1
          · intro i hi
            exact hdata₀ i hi
        · exact ih h100'.1

/-- SymSteps 的首步拆分。 -/
lemma SymSteps_first_step {M : ℕ × Sym → Finset SymTransResult} {cfg₀ : SymConfig}
    {π : List SymStep} {cfg : SymConfig} (h : SymSteps M cfg₀ π cfg) (hπ : π ≠ []) :
    ∃ step : SymStep, ∃ π' : List SymStep,
      π = step :: π' ∧ step.fromState = cfg₀.state ∧
      step.readSym = cfg₀.tape cfg₀.headPos ∧
      step.result ∈ M (cfg₀.state, cfg₀.tape cfg₀.headPos) ∧
      SymSteps M (symStepConfig cfg₀ step.result) π' cfg := by
  induction h with
  | nil => exfalso; exact hπ rfl
  | cons π₀ step cfg' h_ind h_from h_read h_trans ih =>
      by_cases hπ₀ : π₀ = []
      · subst π₀
        have hcfg' : cfg' = cfg₀ := SymSteps_nil_eq h_ind
        subst hcfg'
        refine ⟨step, [], rfl, h_from, h_read, h_trans, SymSteps.nil⟩
      · rcases ih hπ₀ with ⟨step₀, π₀', hπ₀eq, hfrom₀, hread₀, htrans₀, htail⟩
        refine ⟨step₀, π₀' ++ [step], ?_, hfrom₀, hread₀, htrans₀, ?_⟩
        · rw [hπ₀eq]
          rfl
        · exact SymSteps.cons π₀' step cfg' htail h_from h_read h_trans

/-- 从 22 出发到 100 的路径首读必为 (boundary, true)（否则 101 吸收）。 -/
lemma first_read_of_22_to_100 (tape : ℤ → Sym) (hp : ℤ) {ρ cfg}
    (h : SymSteps VerifierSym.transition (SymConfig.mk 22 tape hp) ρ cfg)
    (hs : cfg.state = 100) :
    tape hp = Sym.mk SymKind.boundary true := by
  rcases SymSteps_first_step h (by
    intro hρ
    subst ρ
    rw [SymSteps_nil_eq h] at hs
    simp [SymConfig.mk] at hs
    ) with ⟨step, ρ', hρeq, hfrom, hread, htrans, htail⟩
  have hdec : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (22, s),
      r.nextState = 23 → s = Sym.mk SymKind.boundary true := by
    intro s
    rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
  have hdec2 : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (22, s),
      r.nextState = 23 ∨ r.nextState = 101 := by
    intro s
    rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
  rcases hdec2 step.readSym step.result (by simpa [hread, SymConfig.mk] using htrans) with h23 | h101
  · change (SymConfig.mk 22 tape hp).tape (SymConfig.mk 22 tape hp).headPos = Sym.mk SymKind.boundary true
    rw [← hread]
    exact hdec step.readSym step.result (by simpa [hread, SymConfig.mk] using htrans) h23
  · exfalso
    have hs101 : (symStepConfig (SymConfig.mk 22 tape hp) step.result).state = 101 := by
      dsimp [symStepConfig]
      exact h101
    have htail' : SymSteps VerifierSym.transition
        (SymConfig.mk 101 (symStepConfig (SymConfig.mk 22 tape hp) step.result).tape
          (symStepConfig (SymConfig.mk 22 tape hp) step.result).headPos) ρ' cfg := by
      rw [show symStepConfig (SymConfig.mk 22 tape hp) step.result = SymConfig.mk 101
          (symStepConfig (SymConfig.mk 22 tape hp) step.result).tape
          (symStepConfig (SymConfig.mk 22 tape hp) step.result).headPos from by
        dsimp [symStepConfig]
        dsimp [symStepConfig] at hs101
        rw [hs101]] at htail
      exact htail
    have hfrom101 := steps_from_101 (symStepConfig (SymConfig.mk 22 tape hp) step.result).tape
      (symStepConfig (SymConfig.mk 22 tape hp) step.result).headPos (π := ρ') (cfg := cfg) htail'
    rw [hfrom101] at hs
    omega

/-- 流程态集的前驱闭包。 -/
lemma flow_prev (q q' : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q', s)) (hrs : r.nextState = q) :
    q ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) →
    q' ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
  intro hq
  have hqle : q' ≤ 101 := by
    by_cases hqin : q' ∈ VerifierSym.legalStates
    · exact legalStates_le_101 q' hqin
    · have htr : VerifierSym.transition (q', s) = {SymTransResult.mk 101 s Dir.S} := by
        unfold VerifierSym.transition
        dsimp
        rw [if_neg hqin]
      have hr' : r = SymTransResult.mk 101 s Dir.S := by
        simpa [htr] using hr
      rw [hr'] at hrs
      have hq101 : q = 101 := by simpa using hrs.symm
      rw [hq101] at hq
      norm_num at hq
  have hdec : ∀ q ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ), ∀ q' : ℕ, q' ≤ 101 → ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q', s) → r.nextState = q →
        q' ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
    native_decide
  exact hdec q hq q' hqle s r hr hrs

/-- 格式检查链态集（分支阶段 + 格式检查）的前驱闭包。 -/
lemma chain_state_prev (q q' : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q', s)) (hrs : r.nextState = q) :
    q ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ) →
    q' ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ) := by
  intro hq
  have hqle : q' ≤ 101 := by
    by_cases hqin : q' ∈ VerifierSym.legalStates
    · exact legalStates_le_101 q' hqin
    · have htr : VerifierSym.transition (q', s) = {SymTransResult.mk 101 s Dir.S} := by
        unfold VerifierSym.transition
        dsimp
        rw [if_neg hqin]
      have hr' : r = SymTransResult.mk 101 s Dir.S := by
        simpa [htr] using hr
      rw [hr'] at hrs
      have hq101 : q = 101 := by simpa using hrs.symm
      rw [hq101] at hq
      norm_num at hq
  have hdec : ∀ q ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ), ∀ q' : ℕ, q' ≤ 101 → ∀ s : Sym, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q', s) → r.nextState = q →
        q' ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ) := by
    native_decide
  exact hdec q hq q' hqle s r hr hrs

/-- 格式检查链路径的一切真前缀终点 ≠ 4。 -/
lemma prefix_states_ne4_of_chain {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hstate : cfg.state ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ)) :
    ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →
      (∃ ρ, π = π₀ ++ ρ) → π₀.length < π.length → cfg₀.state ≠ 4 := by
  intro π₀ cfg₀ h₀ hpre hlen
  induction h generalizing π₀ cfg₀ with
  | nil =>
      rcases hpre with ⟨ρ, hρ⟩
      have hlen₀ : π₀.length + ρ.length = 0 := by
        simpa [List.length_append] using congrArg List.length hρ.symm
      have hπ₀ : π₀ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hρ0 : ρ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hπ₀
      subst hρ0
      have hcfg₀ : cfg₀ = symInitialConfig input := SymSteps_nil_eq h₀
      subst hcfg₀
      dsimp [symInitialConfig]
      omega
  | cons π₁ step cfg₁ h_ind h_from h_read h_trans ih =>
      have hstate₁ : cfg₁.state ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ) := by
        have hnext : step.result.nextState = step.result.nextState := rfl
        exact chain_state_prev step.result.nextState cfg₁.state (cfg₁.tape cfg₁.headPos) step.result h_trans hnext (by
          simpa [symStepConfig] using hstate)
      rcases hpre with ⟨ρ, hρ'⟩
      rcases List.append_eq_append_iff.mp hρ' with ⟨as, h1, h2⟩ | ⟨bs, h3, h4⟩
      · -- π₀ = π₁ ++ as：π₁ 是 π₀ 的前缀
        cases as with
        | nil =>
            subst h1
            simp at h₀
            have hcfg := SymSteps_cfg_eq h₀ h_ind
            rw [hcfg]
            have hne4 : cfg₁.state ≠ 4 := by
              have hdec : ∀ q ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ), q ≠ 4 := by
                native_decide
              exact hdec cfg₁.state hstate₁
            exact hne4
        | cons a as' =>
            -- h1 : π₀ = π₁ ++ (a :: as')：π₀ 比 π₁ 严格长，与 hlen（|π₀| < |π₁| + 1）矛盾
            exfalso
            have hlen₀ : π₀.length = π₁.length + (as'.length + 1) := by
              simpa [List.length_append] using congrArg List.length h1
            have hlen₁ : π₀.length < π₁.length + 1 := by
              simpa [List.length_append, List.length_cons] using hlen
            omega
      · -- π₁ = π₀ ++ bs：π₀ 是 π₁ 的前缀
        by_cases hπ₀eq : π₀ = π₁
        · subst hπ₀eq
          have hcfg := SymSteps_cfg_eq h₀ h_ind
          rw [hcfg]
          have hne4 : cfg₁.state ≠ 4 := by
            have hdec : ∀ q ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38, 28} : Finset ℕ), q ≠ 4 := by
              native_decide
            exact hdec cfg₁.state hstate₁
          exact hne4
        · exact ih hstate₁ h₀ ⟨bs, h3⟩ (by
            have hlenb : π₁.length = π₀.length + bs.length := by
              simpa [List.length_append] using congrArg List.length h3
            have hb : 0 < bs.length := by
              cases bs with
              | nil => exact (hπ₀eq (by simpa using h3.symm)).elim
              | cons b bs' => simp
            rw [hlenb]
            omega)

/-- 从流程态终点往回链到第一个 4 态配置。
    注：S 只含 4 之后的流程态（fmt 段 3/24/26/27/29/38/28 之前无 4）；回走遇 cfg₀=28
    （fmt 尾、28→4 唯一入边）时 cfg 自身就是第一个 4，直接拆分而非递归。 -/
lemma backchain_to_first4 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hs : cfg.state ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ)) :
    ∃ π₁ π₂ cfg₄, π = π₁ ++ π₂ ∧
      SymSteps VerifierSym.transition (symInitialConfig input) π₁ cfg₄ ∧
      cfg₄.state = 4 ∧
      (∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
        SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →
        (∃ ρ, π₁ = π₀ ++ ρ) → π₀.length < π₁.length → cfg₀.state ≠ 4) ∧
      SymSteps VerifierSym.transition cfg₄ π₂ cfg := by
  induction h with
  | nil =>
      have h0 : (symInitialConfig input).state = 0 := by simp [symInitialConfig]
      rw [h0] at hs
      exfalso
      exact (by decide : (0 : ℕ) ∉ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ)) hs
  | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
      by_cases h4 : cfg₀.state = 4
      · -- cfg 的紧前驱已是 4：π₀ 内的第一个 4 由归纳假设给出
        have hstate₄ : cfg₀.state ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
          rw [h4]
          decide
        rcases ih hstate₄ with ⟨π₁, π₂, cfg₄, hsplit, hπ₁, h4f, hno4, hrest⟩
        refine ⟨π₁, π₂ ++ [step], cfg₄, ?_, hπ₁, h4f, hno4, ?_⟩
        · change π₀ ++ [step] = π₁ ++ (π₂ ++ [step])
          rw [hsplit]
          ac_rfl
        · exact SymSteps.cons π₂ step cfg₀ hrest h_from h_read h_trans
      · by_cases h28 : cfg₀.state = 28
        · -- fmt 尾步（28 读 #₀ → 4）：cfg 是路径上第一个 4（fmt 链在 4 之前无 4）
          have hcfg4 : (symStepConfig cfg₀ step.result).state = 4 := by
            have hsS : step.result.nextState ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
              simpa [symStepConfig] using hs
            have hdec : ∀ s : Sym, ∀ r ∈ VerifierSym.transition (28, s),
                r.nextState ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) → r.nextState = 4 := by
              intro s
              rcases s with ⟨ks, ms⟩ <;> cases ks <;> cases ms <;> decide
            exact hdec (cfg₀.tape cfg₀.headPos) step.result (by simpa [h28] using h_trans) hsS
          have hno4' : ∀ {π' : List SymStep} {cfg' : SymConfig},
              SymSteps VerifierSym.transition (symInitialConfig input) π' cfg' →
              (∃ ρ, π₀ ++ [step] = π' ++ ρ) → π'.length < (π₀ ++ [step]).length → cfg'.state ≠ 4 := by
            intro π' cfg' h' hpre' hlen'
            rcases hpre' with ⟨ρ, hρ⟩
            have hlen'' : π'.length < π₀.length + 1 := by
              simpa [List.length_append] using hlen'
            by_cases hlt : π'.length < π₀.length
            · -- π' 严格短于 π₀：fmt 链前缀（prefix_states_ne4_of_chain）
              have hpre₀ : ∃ ρ₀, π₀ = π' ++ ρ₀ := by
                rcases List.append_eq_append_iff.mp hρ with ⟨as, h1, h2⟩ | ⟨bs, h3, h4⟩
                · exfalso
                  have hlen₁ : π₀.length ≤ π'.length := by
                    rw [h1]
                    simp [List.length_append]
                  omega
                · exact ⟨bs, h3⟩
              exact prefix_states_ne4_of_chain h_ind (by rw [h28]; decide) h' hpre₀ hlt
            · -- |π'| = |π₀|：π' = π₀ → cfg' = cfg₀ → 28 ≠ 4
              have heq : π'.length = π₀.length := by omega
              have hπ₀eq' : π₀ = π' := List.append_inj_left hρ heq.symm
              rw [← hπ₀eq'] at h'
              have hcfg' : cfg' = cfg₀ := SymSteps_cfg_eq h' h_ind
              rw [hcfg', h28]
              decide
          refine ⟨π₀ ++ [step], [], symStepConfig cfg₀ step.result, ?_, ?_, hcfg4, hno4', SymSteps.nil⟩
          · simp
          · exact SymSteps.cons π₀ step cfg₀ h_ind h_from h_read h_trans
        · -- 一般流程前驱：回走链（flow_prev 闭包）且排除 fmt 前段态
          have hstate₀ : cfg₀.state ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
            have hnext : step.result.nextState = step.result.nextState := rfl
            have hsS : step.result.nextState ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
              simpa [symStepConfig] using hs
            have hqbig : step.result.nextState ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
              exact (by decide : ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) ⊆ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ)) hsS
            have hbig₀ : cfg₀.state ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) :=
              flow_prev step.result.nextState cfg₀.state (cfg₀.tape cfg₀.headPos) step.result h_trans hnext hqbig
            have hnotF : cfg₀.state ∉ ({0, 1, 2, 3, 24, 26, 27, 29, 38} : Finset ℕ) := by
              intro hF
              have hdec : ∀ q' ∈ ({0, 1, 2, 3, 24, 26, 27, 29, 38} : Finset ℕ), ∀ s : Sym, ∀ r : SymTransResult,
                  r ∈ VerifierSym.transition (q', s) → r.nextState ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) → False := by
                native_decide
              exact hdec cfg₀.state hF (cfg₀.tape cfg₀.headPos) step.result h_trans hsS
            have hdecS : ∀ q : ℕ, q ∈ ({0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 26, 27, 28, 29, 38, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) → q ∉ ({0, 1, 2, 3, 24, 26, 27, 29, 38} : Finset ℕ) → q ≠ 28 → q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 51, 76, 77, 81, 84, 85, 86, 87, 100} : Finset ℕ) := by
              native_decide
            exact hdecS cfg₀.state hbig₀ hnotF (by intro h28'; exact h28 h28')
          rcases ih hstate₀ with ⟨π₁, π₂, cfg₄, hsplit, hπ₁, h4f, hno4, hrest⟩
          refine ⟨π₁, π₂ ++ [step], cfg₄, ?_, hπ₁, h4f, hno4, ?_⟩
          · change π₀ ++ [step] = π₁ ++ (π₂ ++ [step])
            rw [hsplit]
            ac_rfl
          · exact SymSteps.cons π₂ step cfg₀ hrest h_from h_read h_trans


/-- 溢出位（v_j = true 且 2^j > T）：状态 5 → 76 → 77 → 10 → 11 → 14 → 借位穿 #₀ → 101。 -/
lemma process_one_bit_overflow (j : ℕ) (tbits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hjt : j < tbits.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (hvj : tape (p_e + 1 + (j : ℤ)) = Sym.data1)
    (hlt2 : bitsValue tbits < 2 ^ j) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 101 := by
  let r5 : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
  let step5 : SymStep := { fromState := 5, readSym := Sym.data1, result := r5 }
  have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
    rw [hvj]
    decide
  let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
  have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
      (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
    refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.data1 = tape (p_e + 1 + (j : ℤ))
      rw [hvj]
    · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
      rw [hvj]
      decide
  have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
      SymConfig.mk 76 tape1 (p_e + (j : ℤ)) := by
    simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
    omega
  -- 状态 76 左移 j+1 格到 #₀
  have hnb6 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
      (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
    intro i h
    have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
    by_cases heq : i = p_e
    · subst i
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      rcases hsel with hd | hd
      · right; left; simpa using hd
      · right; right; simpa using hd
    · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
        refine ⟨(i - (p_e + 1)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
      rcases ioff with ⟨io, hio⟩
      have hio_le : io ≤ j := by omega
      by_cases heqio : io = j
      · subst io
        have hidx : i = p_e + 1 + (j : ℤ) := by omega
        rw [hidx]
        simp [tape1]
        left
        rfl
      · have hio_lt : io < j := by omega
        have ht := helem_pre io hio_lt
        have hidx : p_e + 1 + (io : ℤ) = i := by omega
        have ht' : tape i = Sym.consumed := by
          rw [hidx] at ht
          exact ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht']
        decide
  have hbound6 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
    have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
    rw [hpos]
    rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
    exact hbound
  have hend6 : { nextState := 77, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (76, Sym.boundary) := by decide
  have hkeep6 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
      { nextState := 76, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (76, s) := trans76_keep
  rcases scanLeftKeepP 76 77 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
      (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb6 hbound6 hkeep6 hend6 rfl
    with ⟨π6, cfg6, hπ6, hs6, hhead6, htape6⟩
  -- 状态 77 左移 (p_e - p_t - 1) 格到 #ₗ
  let n7 : ℕ := (p_e - p_t - 1).toNat
  have hn7 : (n7 : ℤ) = p_e - p_t - 1 := by
    change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
    exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
  have hnb7 : ∀ i : ℤ, (p_e - 2) - (n7 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
    intro i h
    rw [hn7] at h
    have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
    by_cases hlt_target : i < p_t + (tbits.length : ℤ)
    · have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
      have hdata_io := targetTape_data j tbits ((targetTape j tbits)[io]) hmem
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht]
      exact hdata_io
    · have hpad_i := hpad i (by constructor <;> omega)
      rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
      rw [hpad_i]
      decide
  have hbound7 : tape1 ((p_e - 2) - (n7 : ℤ)) = Sym.boundary := by
    have hpos : (p_e - 2) - (n7 : ℤ) = p_t - 1 := by rw [hn7]; omega
    rw [hpos]
    rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
    exact hhashL
  have hend7 : { nextState := 10, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (77, Sym.boundary) := by decide
  have hkeep7 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
      { nextState := 77, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (77, s) := trans77_keep
  rcases scanLeftKeepP 77 10 Sym.boundary Dir.R n7 (p_e - 2) tape1
      (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb7 hbound7 hkeep7 hend7 rfl
    with ⟨π7, cfg7, hπ7, hs7, hhead7, htape7⟩
  -- 状态 10 右移 j 格（扫 4F4.4 标记前缀）
  have hkeep10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape1 i) := by
    intro i h
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
      refine ⟨(i - p_t).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < (targetTape j tbits).length := by
      have hlen : (targetTape j tbits).length = tbits.length := by
        simp [targetTape_length]
      rw [hlen]
      omega
    have ht := htarget io hio_lt
    have hio_j : io < j := by omega
    have hio_tbits : io < tbits.length := by omega
    have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
      simp [targetTape, bitsToSym, hio_j, hio_tbits]
    have hidx : p_t + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
    rw [ht, hsym]
    have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
        (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
      by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    exact trans10_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
  rcases scanRightKeep 10 j p_t tape1 hkeep10 with ⟨π10, cfg10, hπ10, hs10, hhead10, htape10⟩
  -- 借位越界（2^j > T）：[j, L) 段全 false（否则 2^j ≤ T）
  have hall_false : ∀ io : ℕ, j ≤ io → (hlt : io < tbits.length) → tbits[io]'(hlt) = false := by
    intro io hge hlt
    by_contra h
    have htrue : tbits[io] = true := by
      cases hb : tbits[io] <;> simp [hb] at h ⊢
    have hpow : 2 ^ io ≤ bitsValue tbits := bitsValue_ge_pow_of_getElem_true tbits io hlt htrue
    have hge2 : 2 ^ j ≤ 2 ^ io := pow_le_pow_right₀ (by norm_num) hge
    omega
  have hj' : j < tbits.length := by omega
  have htbits_j : tbits[j] = false := hall_false j (by omega) hj'
  -- t_j 处带 = data0（m=0）
  have htape_tj : tape1 (p_t + (j : ℤ)) = Sym.data0 := by
    rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by simp [tape1]; intro h'; omega]
    have h := htarget j (by simpa [targetTape_length] using hj')
    have hget : (targetTape j tbits)[j]'(by simpa [targetTape_length] using hj') = Sym.data0 := by
      rw [targetTape_getElem_ge j j tbits hj' le_rfl]
      simp [htbits_j]
    rw [hget] at h
    exact h
  -- 状态 10 读 t_j（data0 m=0）→ 11（写 data0 m=1 标 m）
  let r10tj : SymTransResult := { nextState := 11, writeSym := Sym.data0 true, moveDir := Dir.S }
  let step10tj : SymStep := { fromState := 10, readSym := Sym.data0, result := r10tj }
  have htrans10tj : step10tj.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ))) := by
    rw [htape_tj]
    simp [step10tj, r10tj]
    decide
  have hstep10tj : SymSteps VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) [step10tj]
      (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) := by
    refine SymSteps.cons [] step10tj (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
    · rfl
    · dsimp [step10tj]
      rw [htape_tj]
    · change step10tj.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ)))
      exact htrans10tj
  let tape2 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data0 true else tape1 i
  have hcfg10tj : symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result =
      SymConfig.mk 11 tape2 (p_t + (j : ℤ)) := by
    simp [symStepConfig, SymConfig.mk, step10tj, r10tj, tape2, Dir.toInt]
  -- 状态 11 读（data0 m=1）→ 14（借位写 data1 m=1）
  let r11 : SymTransResult := { nextState := 14, writeSym := Sym.data1 true, moveDir := Dir.R }
  let step11 : SymStep := { fromState := 11, readSym := Sym.data0 true, result := r11 }
  have htrans11 : step11.result ∈ VerifierSym.transition (11, Sym.data0 true) := by
    simp [step11, r11]
    decide
  have hstep11 : SymSteps VerifierSym.transition (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) [step11]
      (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) := by
    refine SymSteps.cons [] step11 (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
    · rfl
    · dsimp [step11, tape2]
      simp
    · change step11.result ∈ VerifierSym.transition (11, tape2 (p_t + (j : ℤ)))
      simp [tape2]
      exact htrans11
  let tape3 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data1 true else tape2 i
  have hcfg11 : symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result =
      SymConfig.mk 14 tape3 (p_t + (j : ℤ) + 1) := by
    simp [symStepConfig, SymConfig.mk, step11, r11, tape3, Dir.toInt]
  -- 状态 14 借位传播：从 p_t + j + 1 到 #₀（p_e - 1）全 data0 → 101
  have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 :=
    target_ends_before_pe tbits.length j p_t p_e tape tbits (Nat.le_refl _) hjt (by simpa using hp_t_le) htarget hbound
  let n : ℕ := (p_e - 1 - (p_t + (j : ℤ) + 1)).toNat
  have hn_n : (n : ℤ) = p_e - 1 - (p_t + (j : ℤ) + 1) := by
    change ((p_e - 1 - (p_t + (j : ℤ) + 1)).toNat : ℤ) = p_e - 1 - (p_t + (j : ℤ) + 1)
    exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - 1 - (p_t + (j : ℤ) + 1))
  have huf_tape : ∀ i : ℕ, i < n → tape3 (p_t + (j : ℤ) + 1 + (i : ℤ)) = Sym.data0 := by
    intro i hi
    have hx_lt : p_t + (j : ℤ) + 1 + (i : ℤ) < p_e - 1 := by
      have hz : (i : ℤ) < (n : ℤ) := by exact_mod_cast hi
      rw [hn_n] at hz
      omega
    have hne1 : p_t + (j : ℤ) + 1 + (i : ℤ) ≠ p_t + (j : ℤ) := by omega
    simp [tape3, tape2, hne1]
    rw [show tape1 (p_t + (j : ℤ) + 1 + (i : ℤ)) = tape (p_t + (j : ℤ) + 1 + (i : ℤ)) from by
      simp [tape1]; intro h'; omega]
    by_cases hlt : p_t + (j : ℤ) + 1 + (i : ℤ) < p_t + (tbits.length : ℤ)
    · have ioff : ∃ io : ℕ, (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t := by
        refine ⟨(p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat, ?_⟩
        change ((p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t
        exact Int.toNat_of_nonneg (by omega)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = tbits.length := by simp [targetTape_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_ge : j < io := by omega
      have hio_lt_L : io < tbits.length := by omega
      have hbits_false : tbits[io] = false := hall_false io (Nat.le_of_lt hio_ge) hio_lt_L
      have hsym : (targetTape j tbits)[io] = Sym.data0 := by
        rw [targetTape_getElem_ge j io tbits hio_lt_L (Nat.le_of_lt hio_ge)]
        simp [hbits_false]
      have hidx : p_t + (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) := by omega
      rw [hidx] at ht
      rw [ht, hsym]
    · have hpad_i := hpad (p_t + (j : ℤ) + 1 + (i : ℤ)) (by constructor <;> omega)
      rw [hpad_i]
  have huf_bound : tape3 (p_t + (j : ℤ) + 1 + (n : ℤ)) = Sym.boundary := by
    rw [hn_n]
    have hpos : p_t + (j : ℤ) + 1 + (p_e - 1 - (p_t + (j : ℤ) + 1)) = p_e - 1 := by omega
    rw [hpos]
    simp [tape3, tape2, show p_e - 1 ≠ p_t + (j : ℤ) from by omega]
    rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
    exact hbound
  rcases underflow_scan_to_boundary (p_t + (j : ℤ) + 1) n tape3 huf_tape huf_bound
    with ⟨πuf, cfguf, hπuf, hsuf, hheaduf, hdata1uf, hbounduf, hleftuf, hrightuf⟩
  -- 拼链：5 → 76 → 77 → 10 → 11 → 14 → … → 101
  have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
  have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
  have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
    cases cfg6 with
    | mk state tape headPos =>
        change state = 77 at hs6
        change tape = tape1 at htape6
        rw [hs6, htape6]
        congr 1
        change headPos = (p_e + (j : ℤ)) - ((j + 1 : ℕ) : ℤ) + Dir.L.toInt at hhead6
        rw [hhead6]
        simp [Dir.toInt]
        omega
  have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
    rw [hcfg6_eq]; exact hπ7
  have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
  have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
    cases cfg7 with
    | mk state tape headPos =>
        change state = 10 at hs7
        change tape = tape1 at htape7
        rw [hs7, htape7]
        congr 1
        change headPos = (p_e - 2) - (n7 : ℤ) + Dir.R.toInt at hhead7
        rw [hhead7]
        simp [hn7, Dir.toInt]
        omega
  have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
    rw [hcfg7_eq]; exact hπ10
  have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
  have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
    cases cfg10 with
    | mk state tape headPos =>
        change state = 10 at hs10
        change tape = tape1 at htape10
        change headPos = p_t + (j : ℤ) at hhead10
        rw [hs10, htape10, hhead10]
  have h10tj' : SymSteps VerifierSym.transition cfg10 [step10tj]
      (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) := by
    rw [hcfg10_eq]
    exact hstep10tj
  have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
      ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj])
      (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) [step10tj] h567'' h10tj'
  have h11' : SymSteps VerifierSym.transition (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) [step11]
      (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) := by
    rw [hcfg10tj]
    exact hstep11
  have h567'''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
      ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11])
      (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj]) [step11] h567''' h11'
  have h14' : SymSteps VerifierSym.transition (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) πuf cfguf := by
    rw [hcfg11]
    exact hπuf
  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
      ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11] ++ πuf) cfguf :=
    SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11]) πuf h567'''' h14'
  exact ⟨[step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11] ++ πuf, cfguf, htotal, hsuf⟩

/-- 逐位减溢出循环：2^j·bitsValue ebits 超过当前 target 值时，状态 5 起必到 101（借位穿出 #₀ 拒绝）。 -/
lemma subtract_loop_overflow (tbits ebits : List Bool) (j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hebits_pos : 1 ≤ ebits.length)
    (htlen : j + ebits.length ≤ tbits.length)
    (hlt : bitsValue tbits < 2 ^ j * bitsValue ebits)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (helem_rest : tapeAgrees tape (p_e + 1 + (j : ℤ)) (bitsToSym ebits)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 101 := by
  induction ebits generalizing tbits j p_t p_e tape with
  | nil =>
      exfalso
      simp at hebits_pos
  | cons b rest ih =>
      have hvj : tape (p_e + 1 + (j : ℤ)) = if b then Sym.data1 else Sym.data0 := by
        have h0 := helem_rest 0 (by simp [bitsToSym])
        simpa [bitsToSym_cons] using h0
      let ebits_full : List Bool := List.replicate j false ++ (b :: rest)
      have helen_full : ebits_full.length = j + 1 + rest.length := by
        simp [ebits_full]
        omega
      have helem_rest_full : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits_full.drop (j + 1))) := by
        have hdrop : ebits_full.drop (j + 1) = rest := by
          dsimp [ebits_full]
          simp [List.drop_append, List.length_replicate]
        rw [hdrop]
        intro i hi
        have h := helem_rest (i + 1) (by
          simp [bitsToSym] at hi ⊢
          omega)
        simpa [bitsToSym_cons, add_assoc, add_comm, add_left_comm] using h
      have hlen_le : ebits_full.length ≤ tbits.length := by
        rw [helen_full]
        have htlen_l := htlen
        simp [List.length_cons] at htlen_l ⊢
        omega
      have hjh : j < ebits_full.length := by
        rw [helen_full]
        omega
      by_cases hov : b ∧ bitsValue tbits < 2 ^ j
      · -- 溢出位：5 → 76 → 77 → 10 → 11 → 14 → 借位 → 101
        have hb : b = true := hov.1
        have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hb] using hvj
        have hj_lt' : j < tbits.length := by omega
        rcases process_one_bit_overflow j tbits p_t p_e tape hj_lt' hp_t_le hbound hpad htarget hhashL hsel helem_pre hvj' hov.2
          with ⟨π₁, cfg₁, hπ₁, h101⟩
        exact ⟨π₁, cfg₁, hπ₁, h101⟩
      · -- 正常位：process_one_bit_last 的正常分支，然后递归（或 hlt 矛盾）
        rcases process_one_bit_last j b tbits ebits_full p_t p_e tape hlen_le hjh hp_t_le hbound hpad htarget hhashL hsel helem_pre hvj helem_rest_full
          with ⟨π₁, cfg₁, hπ₁, hres1⟩
        rcases hres1 with hnorm | hover
        · rcases hnorm with ⟨hstate₁, hhead₁, hta₁, hcons₁, hrest₁, hsel₁, hhashL₁, hbound₁, hsep₁, hpe_eq₁, hpad_keep₁, hright₁⟩
          let tbits' : List Bool := if b then (subOneAt j tbits).getD tbits else tbits
          have htbits'_eq : tbits' = subAllBitsAt tbits [b] j := by
            simp [tbits', subAllBitsAt]
          have htlen' : (j + 1) + rest.length ≤ tbits'.length := by
            have hlen_t : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen_t]
            have htlen_l := htlen
            simp [List.length_cons] at htlen_l
            omega
          have hsub : (if b then 2 ^ j else 0) ≤ bitsValue tbits := by
            by_cases hb : b
            · simp [hb]
              have hnot : ¬ bitsValue tbits < 2 ^ j := by
                intro h
                exact hov ⟨hb, h⟩
              omega
            · simp [hb]
          have hval : bitsValue tbits' = bitsValue tbits - (if b then 2 ^ j else 0) := by
            by_cases hb : b
            · have hval' := subAllBitsAt_value tbits [b] j (by simpa [hb, bitsValue] using hsub)
              rw [← htbits'_eq] at hval'
              have hb_val : bitsValue [b] = 1 := by simp [hb]
              simpa [hb, hb_val] using hval'
            · have hval' := subAllBitsAt_value tbits [b] j (by simp [hb])
              rw [← htbits'_eq] at hval'
              have hb_val : bitsValue [b] = 0 := by simp [hb]
              simpa [hb, hb_val] using hval'
          have hlt' : bitsValue tbits' < 2 ^ (j + 1) * bitsValue rest := by
            by_cases hb : b
            · -- b = true
              have hbval : bitsValue (b :: rest) = 1 + 2 * bitsValue rest := by simp [hb]
              have hlt0 : bitsValue tbits < 2 ^ j * (1 + 2 * bitsValue rest) := by simpa [hbval] using hlt
              have hle1 : 2 ^ j ≤ bitsValue tbits := by simpa [hb] using hsub
              rw [hval]
              simp [hb]
              have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
                rw [pow_succ]
                ring
              rw [← hpow]
              have hsum : 2 ^ j * (1 + 2 * bitsValue rest) = 2 ^ j + 2 ^ j * (2 * bitsValue rest) := by ring
              rw [hsum] at hlt0
              omega
            · -- b = false
              have hbval : bitsValue (b :: rest) = 2 * bitsValue rest := by simp [hb]
              have hlt0 : bitsValue tbits < 2 ^ j * (2 * bitsValue rest) := by simpa [hbval] using hlt
              have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
                rw [pow_succ]
                ring
              rw [hval]
              simp [hb]
              simpa [hpow] using hlt0
          have hp_t_le' : p_t + (tbits'.length : ℤ) ≤ p_e := by
            have hlen : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen]
            exact hp_t_le
          have hbound' : cfg₁.tape (p_e - 1) = Sym.boundary := hbound₁
          have hpad' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg₁.tape i = Sym.data0 := by
            intro i hi
            have hlen : tbits'.length = tbits.length := by
              rw [htbits'_eq]
              exact subAllBitsAt_length tbits [b] j
            rw [hlen] at hi
            exact hpad_keep₁ i hi
          have hhashL' : cfg₁.tape (p_t - 1) = Sym.boundary := hhashL₁
          have htarget' : tapeAgrees cfg₁.tape p_t (targetTape (j + 1) tbits') := by
            simpa [tbits'] using hta₁
          have helem_pre' : ∀ i : ℕ, i < j + 1 → cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
            intro i hi
            exact hcons₁ i (by omega)
          have hsel' : (cfg₁.tape p_e).1 = SymKind.data0 ∨ (cfg₁.tape p_e).1 = SymKind.data1 := hsel₁
          have hstate_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
            cases cfg₁ with
            | mk s t hp =>
                dsimp
                rw [show s = 13 from hstate₁]
                rw [show hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) from hhead₁]
                norm_num
          cases rest with
          | nil =>
              -- 最后一位且未溢出：hlt 与 ¬hov 矛盾
              exfalso
              have hlt_l := hlt
              by_cases hb : b
              · simp [hb] at hlt_l
                have hnot : 2 ^ j ≤ bitsValue tbits := Nat.le_of_not_gt (by intro h; exact hov ⟨hb, h⟩)
                omega
              · simp [hb] at hlt_l
          | cons b2 rest2 =>
              -- 13 读 v_{j+1}（data）→ 5 S
              have hd : cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (if b2 then Sym.data1 else Sym.data0) := by
                have hdrop : ebits_full.drop (j + 1) = b2 :: rest2 := by
                  dsimp [ebits_full]
                  simp [List.drop_append, List.length_replicate, List.drop]
                have h0 := hrest₁ 0 (by simp [bitsToSym, hdrop])
                simpa [bitsToSym, hdrop] using h0
              let r5b : SymTransResult := { nextState := 5, writeSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), moveDir := Dir.S }
              let step5b : SymStep := { fromState := 13, readSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), result := r5b }
              have hcfg₁_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := hstate_eq
              have htrans5b : step5b.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
                rw [hcfg₁_eq]
                by_cases hb2 : b2
                · unfold step5b r5b
                  rw [show cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data1 from by simpa [if_pos hb2] using hd]
                  simp [SymConfig.mk]
                  decide
                · unfold step5b r5b
                  rw [show cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0 from by simpa [if_neg hb2] using hd]
                  simp [SymConfig.mk]
                  decide
              have hstep5b : SymSteps VerifierSym.transition cfg₁ [step5b] (symStepConfig cfg₁ step5b.result) := by
                refine SymSteps.cons [] step5b cfg₁ SymSteps.nil ?_ ?_ ?_
                · simpa [step5b] using hstate₁.symm
                · rw [hhead₁]
                · exact htrans5b
              let cfg5b : SymConfig := symStepConfig cfg₁ step5b.result
              have htape5b : cfg5b.tape = cfg₁.tape := by
                dsimp [cfg5b]
                simp only [symStepConfig, SymConfig.mk, step5b, r5b]
                funext i
                by_cases h : i = p_e + 1 + ((j + 1 : ℕ) : ℤ)
                · rw [hcfg₁_eq]
                  rw [h]
                  simp
                · rw [hcfg₁_eq]
                  rw [if_neg h]
              have hhead5b : cfg5b.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) := by
                dsimp [cfg5b]
                simp only [symStepConfig, SymConfig.mk, step5b, r5b, Dir.toInt]
                rw [hcfg₁_eq]
                simp
              have hstate5b : cfg5b.state = 5 := by
                dsimp [cfg5b]
                simp only [symStepConfig, SymConfig.mk, step5b, r5b]
              have htotal_pre : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step5b]) cfg5b :=
                SymSteps_trans _ _ _ _ π₁ [step5b] hπ₁ hstep5b
              have hbound'' : cfg5b.tape (p_e - 1) = Sym.boundary := by rw [htape5b]; exact hbound₁
              have hhashL'' : cfg5b.tape (p_t - 1) = Sym.boundary := by rw [htape5b]; exact hhashL₁
              have hpad'' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg5b.tape i = Sym.data0 := by
                intro i hi
                rw [htape5b]
                exact hpad' i hi
              have hsel'' : (cfg5b.tape p_e).1 = SymKind.data0 ∨ (cfg5b.tape p_e).1 = SymKind.data1 := by
                rw [htape5b]
                exact hsel₁
              have helem_pre'' : ∀ i : ℕ, i < j + 1 → cfg5b.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
                intro i hi
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                exact hcons₁ i (Nat.le_of_lt_succ hi)
              have helem_rest'' : tapeAgrees cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (b2 :: rest2)) := by
                simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                have hdrop2 : ebits_full.drop (j + 1) = b2 :: rest2 := by
                  dsimp [ebits_full]
                  simp [List.drop_append, List.length_replicate, List.drop]
                rw [hdrop2] at hrest₁
                exact hrest₁
              have htlen'' : (j + 1) + (b2 :: rest2).length ≤ tbits'.length := by
                have htlen_l := htlen'
                simp [List.length_cons] at htlen_l ⊢
                exact htlen_l
              have hcfg5b_eq : cfg5b = SymConfig.mk 5 cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                rw [← hstate5b, ← hhead5b]
              rw [← htape5b] at htarget'
              rcases ih tbits' (j + 1) p_t p_e cfg5b.tape (by simp : 1 ≤ (b2 :: rest2).length) htlen'' hlt' hp_t_le' htarget'
                  hbound'' hhashL'' hpad'' hsel'' helem_pre'' helem_rest''
                  with ⟨π₂, cfg₂, hπ₂, h101₂⟩
              have hπ₂' : SymSteps VerifierSym.transition cfg5b π₂ cfg₂ := by
                rw [hcfg5b_eq]
                exact hπ₂
              have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step5b] ++ π₂) cfg₂ :=
                SymSteps_trans _ _ _ _ (π₁ ++ [step5b]) π₂ htotal_pre hπ₂'
              exact ⟨π₁ ++ [step5b] ++ π₂, cfg₂, htotal, h101₂⟩
        · -- 溢出分支与 ¬hov 矛盾
          exfalso
          rcases hover with ⟨_, _, hb, hlt2, _⟩
          exact hov ⟨hb, hlt2⟩

/-- 减法溢出：selected 元素值超过当前 target 值时，主循环的元素减法（状态 4 起）必到 101。 -/
lemma subtract_overflow_to_101 (tbits ebits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hebits_pos : 1 ≤ ebits.length)
    (htlen : ebits.length ≤ tbits.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : tape p_e = Sym.sel)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hsep : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary)
    (hgt : bitsValue tbits < bitsValue ebits) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧ cfg'.state = 101 := by
  let r : SymTransResult := { nextState := 5, writeSym := Sym.data0, moveDir := Dir.R }
  let step : SymStep := { fromState := 4, readSym := Sym.sel, result := r }
  let tape1 : ℤ → Sym := fun i => if i = p_e then Sym.data0 else tape i
  have hstep : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step]
      (symStepConfig (SymConfig.mk 4 tape p_e) step.result) := by
    refine SymSteps.cons [] step (SymConfig.mk 4 tape p_e) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.sel = tape p_e
      rw [hsel]
    · change step.result ∈ VerifierSym.transition (4, tape p_e)
      rw [hsel]
      decide
  have hcfg : symStepConfig (SymConfig.mk 4 tape p_e) step.result =
      SymConfig.mk 5 tape1 (p_e + 1) := by
    simp [symStepConfig, SymConfig.mk, step, r, tape1, Dir.toInt]
  have htarget0 : tapeAgrees tape1 p_t (targetTape 0 tbits) := by
    intro i hi
    have hi_t : i < tbits.length := by simpa only [targetTape_length] using hi
    have hneq : p_t + (i : ℤ) ≠ p_e := by omega
    rw [show tape1 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact htarget i hi
  have hbound0 : tape1 (p_e - 1) = Sym.boundary := by
    rw [show tape1 (p_e - 1) = tape (p_e - 1) from by
      simp only [tape1]
      rw [if_neg (by omega : p_e - 1 ≠ p_e)]]
    exact hbound
  have hhashL0 : tape1 (p_t - 1) = Sym.boundary := by
    have hneq : p_t - 1 ≠ p_e := by omega
    rw [show tape1 (p_t - 1) = tape (p_t - 1) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact hhashL
  have hsel0 : (tape1 p_e).1 = SymKind.data0 ∨ (tape1 p_e).1 = SymKind.data1 := by
    left
    simp [tape1]
  have helem0 : tapeAgrees tape1 (p_e + 1) (bitsToSym ebits) := by
    intro i hi
    have hneq : p_e + 1 + (i : ℤ) ≠ p_e := by omega
    rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact helem i hi
  have hpad0 : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape1 i = Sym.data0 := by
    intro i hi
    rw [show tape1 i = tape i from by
      simp only [tape1]
      rw [if_neg (by omega : i ≠ p_e)]]
    exact hpad i hi
  have hlt0 : bitsValue tbits < 2 ^ 0 * bitsValue ebits := by simpa using hgt
  rcases subtract_loop_overflow tbits ebits 0 p_t p_e tape1 hebits_pos (by omega : 0 + ebits.length ≤ tbits.length) hlt0 hp_t_le htarget0 hbound0 hhashL0 hpad0 hsel0
      (by intro i hi; omega) (by simpa using helem0)
      with ⟨π, cfg', hπ, h101⟩
  refine ⟨[step] ++ π, cfg', ?_, h101⟩
  have hstep' : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step]
        (SymConfig.mk 5 tape1 (p_e + 1)) := by
    simpa [hcfg] using hstep
  have hπ' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape1 (p_e + 1)) π cfg' := by
    simpa using hπ
  exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 5 tape1 (p_e + 1)) cfg' [step] π hstep' hπ'


/-- 逐位处理（区域版：只要求 j < tbits.length，tbits 填满 [p_t, p_e-1) 前的整个区域；
    v_j = true 且 2^j > T 时走借位越界拒绝分支，否则正常减/标记回状态 5。 -/
lemma process_one_bit_region (j : ℕ) (v_j : Bool) (tbits ebits : List Bool)
    (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hjt : j < tbits.length)
    (hj_lt_e : j < ebits.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (hvj : tape (p_e + 1 + (j : ℤ)) = if v_j then Sym.data1 else Sym.data0)
    (helem_rest : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1)))) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      ((cfg'.state = 13 ∧
      cfg'.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) ∧
      tapeAgrees cfg'.tape p_t (targetTape (j + 1)
        (if v_j then (subOneAt j tbits).getD tbits else tbits)) ∧
      (∀ i : ℕ, i ≤ j → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      tapeAgrees cfg'.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) ∧
      ((cfg'.tape p_e).1 = SymKind.data0 ∨ (cfg'.tape p_e).1 = SymKind.data1) ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) ∧
      cfg'.tape p_e = tape p_e ∧
      (∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg'.tape i = Sym.data0) ∧
      (∀ i : ℤ, p_e + 1 + (ebits.length : ℤ) < i → cfg'.tape i = tape i)) ∨
      (cfg'.state = 101 ∧
      cfg'.headPos = p_e ∧
      v_j = true ∧
      bitsValue tbits < 2 ^ j ∧
      (∀ i : ℤ, p_t + (j : ℤ) ≤ i ∧ i < p_e - 1 → (cfg'.tape i).1 = SymKind.data1) ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      (∀ i : ℕ, i ≤ j → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape p_e = tape p_e ∧
      (∀ i : ℤ, p_e + 1 + (j : ℤ) < i → cfg'.tape i = tape i))) := by
  by_cases hvj_bool : v_j
  · -- 减路径（v_j = true）：状态 5→6→7→10→减2^j→12→13→5
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hvj_bool] using hvj
    have hp_t_lt : p_t + (tbits.length : ℤ) < p_e := boundary_after_target tbits.length j p_t p_e tape tbits (Nat.le_refl _) hjt (by simpa using hp_t_le) htarget hbound
    have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
    have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
    let r5 : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data1, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data1 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 76 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    -- 2. 状态 76 左移 j+1 格到 #₀
    have hnb6 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e
      · subst i
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        rcases hsel with hd | hd
        · right; left; simpa using hd
        · right; right; simpa using hd
      · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases heqio : io = j
        · subst io
          have hidx : i = p_e + 1 + (j : ℤ) := by omega
          rw [hidx]
          simp [tape1]
          left
          rfl
        · have hio_lt : io < j := by omega
          have ht := helem_pre io hio_lt
          have hidx : p_e + 1 + (io : ℤ) = i := by omega
          have ht' : tape i = Sym.consumed := by
            rw [hidx] at ht
            exact ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
          rw [ht']
          decide
    have hbound6 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend6 : { nextState := 77, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (76, Sym.boundary) := by decide
    have hkeep6 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 76, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (76, s) := trans76_keep
    rcases scanLeftKeepP 76 77 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb6 hbound6 hkeep6 hend6 rfl
      with ⟨π6, cfg6, hπ6, hs6, hhead6, htape6⟩
    -- 3. 状态 7 左移 (p_e - p_t - 1) 格到 #ₗ
    let n7 : ℕ := (p_e - p_t - 1).toNat
    have hn7 : (n7 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb7 : ∀ i : ℤ, (p_e - 2) - (n7 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn7] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases hlt_target : i < p_t + (tbits.length : ℤ)
      · -- target 位
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
        have hdata_io := targetTape_data j tbits ((targetTape j tbits)[io]) hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht]
        exact hdata_io
      · -- data0 填充
        have hpad_i := hpad i (by constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        rw [hpad_i]
        decide
    have hbound7 : tape1 ((p_e - 2) - (n7 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n7 : ℤ) = p_t - 1 := by rw [hn7]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend7 : { nextState := 10, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (77, Sym.boundary) := by decide
    have hkeep7 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 77, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (77, s) := trans77_keep
    rcases scanLeftKeepP 77 10 Sym.boundary Dir.R n7 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb7 hbound7 hkeep7 hend7 rfl
      with ⟨π7, cfg7, hπ7, hs7, hhead7, htape7⟩
    -- 4. 状态 10 右移 j 格（4F4.4 前缀）
    have hkeep10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape1 i) := by
      intro i h
      have hi : p_t ≤ i ∧ i < p_t + (tbits.length : ℤ) := by constructor <;> omega
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_j : io < j := by omega
      have hio_tbits : io < tbits.length := by omega
      have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
        simp [targetTape, bitsToSym, hio_j, hio_tbits]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht, hsym]
      have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
          (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
        by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      exact trans10_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
    rcases scanRightKeep 10 j p_t tape1 hkeep10 with ⟨π10, cfg10, hπ10, hs10, hhead10, htape10⟩
    -- 5. 减 2^j：状态 10 读 t_j 减一
    by_cases hsub2 : 2 ^ j ≤ bitsValue tbits
    · -- 正常减法：target 足够（2^j ≤ T），借位不越界
      rcases subOne_drop_some_of_ge_pow tbits j hsub2 with ⟨b', hsub_drop⟩
      have hsub' : subOne (symToBits (bitsToSym (tbits.drop j))) = some b' := by
        simpa [symToBits_bitsToSym] using hsub_drop
      have htape_drop : tapeAgrees tape1 (p_t + (j : ℤ)) (bitsToSym (tbits.drop j)) := by
        have htarget_drop : tapeAgrees tape (p_t + (j : ℤ)) (bitsToSym (tbits.drop j)) := by
          have hsplit := (tapeAgrees_append tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (bitsToSym (tbits.drop j))).mp (by simpa [targetTape] using htarget)
          have hoffset : p_t + (min j tbits.length : ℤ) = p_t + (j : ℤ) := by omega
          simpa [hoffset] using hsplit.2
        intro i hi
        have h := htarget_drop i hi
        rw [show tape1 (p_t + (j : ℤ) + (i : ℤ)) = tape (p_t + (j : ℤ) + (i : ℤ)) from by
          simp [tape1]
          intro h'
          have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 := target_ends_before_pe tbits.length j p_t p_e tape tbits (Nat.le_refl _) hjt (by simpa using hp_t_le) htarget hbound
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          have hlt_pe : p_t + (j : ℤ) + (i : ℤ) < p_e + 1 := by
            have : (i : ℕ) < tbits.length - j := by
              rw [hlen_drop] at hi
              exact hi
            omega
          omega]
        exact h
      rcases subtract_one_matches_subOne (bitsToSym (tbits.drop j)) b' (p_t + (j : ℤ)) tape1 hsub'
        (bitsToSym_data (tbits.drop j)) (bitsToSym_marks (tbits.drop j)) htape_drop
        with ⟨πsub, cfgsub, hπsub, hs_sub, hhead_sub, htape_sub, hleft_sub, hright_sub⟩
    -- 6. 状态 12 右移回元素区（穿 target 剩余 + #₀ + sel 到 v_0）
      let m := firstTrueIdx (tbits.drop j)
      let n : ℕ := (p_e - p_t - (j : ℤ) - (m : ℤ)).toNat
      let p' : ℤ := p_t + ((j + m + 1 : ℕ) : ℤ)
      have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 := target_ends_before_pe tbits.length j p_t p_e tape tbits (Nat.le_refl _) hjt (by simpa using hp_t_le) htarget hbound
      have hm_lt : m < tbits.length - j := by
        have htrue : true ∈ tbits.drop j := (subOne_some_iff_mem_true (tbits.drop j)).mp ⟨b', hsub_drop⟩
        have hlt := firstTrueIdx_lt_length_of_mem (tbits.drop j) htrue
        simpa [m, List.length_drop] using hlt
      have hn_n : (n : ℤ) = p_e - p_t - (j : ℤ) - (m : ℤ) := by
        change ((p_e - p_t - (j : ℤ) - (m : ℤ)).toNat : ℤ) = p_e - p_t - (j : ℤ) - (m : ℤ)
        exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ) - (m : ℤ))
      have hhead_sub' : cfgsub.headPos = p' := by
        rw [hhead_sub]
        rw [symToBits_bitsToSym]
        simp only [p', m]
        push_cast
        ring
      have hp_n : p' + (n : ℤ) = p_e + 1 := by
        rw [hn_n]
        simp only [p']
        omega
      have hnc12 : ∀ i : ℤ, p' ≤ i ∧ i < p' + (n : ℤ) →
          (cfgsub.tape i).1 = SymKind.data0 ∨ (cfgsub.tape i).1 = SymKind.data1 ∨ (cfgsub.tape i).1 = SymKind.boundary := by
        intro i hi
        have hi_lt_pe : i < p_e + 1 := by
          have := hi.2
          rw [hp_n] at this
          exact this
        by_cases hlt_target : i < p_t + (tbits.length : ℤ)
        · -- target 剩余位（markFirst b' 部分）
          have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_t + (j : ℤ)) := by
            refine ⟨(i - (p_t + (j : ℤ))).toNat, ?_⟩
            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_t + (j : ℤ)))
          rcases ioff with ⟨io, hio⟩
          have hio_lt : io < (markFirst b').length := by
            rw [markFirst_length]
            have hb'_len : b'.length = (tbits.drop j).length := subOne_length (tbits.drop j) b' hsub_drop
            rw [hb'_len, List.length_drop]
            omega
          have ht := htape_sub io hio_lt
          have hidx : p_t + (j : ℤ) + (io : ℤ) = i := by omega
          rw [hidx] at ht
          rw [ht]
          rcases markFirst_data b' ((markFirst b')[io]) (List.getElem_mem hio_lt) with hd0 | hd1
          · left
            exact hd0
          · right; left
            exact hd1
        · -- data0 填充 / #₀ / sel
          have hright_i : cfgsub.tape i = tape1 i := hright_sub i (by
            have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
            omega)
          rw [hright_i]
          by_cases hpad_i : i < p_e - 1
          · -- data0 填充
            have h := hpad i (by constructor <;> omega)
            rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
            rw [h]
            decide
          · -- i ∈ {p_e-1, p_e}
            by_cases hh0 : i = p_e - 1
            · rw [hh0]
              rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h'; omega]
              rw [hbound]
              decide
            · have hi_pe : i = p_e := by omega
              rw [hi_pe]
              rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h'; omega]
              rcases hsel with hd | hd
              · left; simpa using hd
              · right; left; simpa using hd
      have hcons12 : cfgsub.tape (p' + (n : ℤ)) = Sym.consumed := by
        rw [hp_n]
        have hright_v0 : cfgsub.tape (p_e + 1) = tape1 (p_e + 1) := hright_sub (p_e + 1) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_v0]
        by_cases hj0 : j = 0
        · subst j
          simp [tape1]
        · have h0lt : 0 < j := by omega
          have h := helem_pre 0 h0lt
          rw [show tape1 (p_e + 1) = tape (p_e + 1) from by simp [tape1]; intro h'; omega]
          simpa using h
      rcases scanRight81 n p' cfgsub.tape hnc12 hcons12 with ⟨π12, cfg12, hπ12, hs12, hhead12, htape12⟩
    -- 7. 状态 13 右移扫 consumed 到 v_{j+1}
      have hcons13 : ∀ i : ℤ, p_e + 2 ≤ i ∧ i < p_e + 2 + (j : ℤ) → cfgsub.tape i = Sym.consumed := by
        intro i hi
        have hright_i : cfgsub.tape i = tape1 i := hright_sub i (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_i]
        have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 2) := by
          refine ⟨(i - (p_e + 2)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 2))
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < j := by omega
        have hidx : i = p_e + 1 + ((io + 1 : ℕ) : ℤ) := by omega
        rw [hidx]
        have hio1_le : io + 1 ≤ j := by omega
        by_cases hio1_eq : io + 1 = j
        · rw [hio1_eq]
          simp [tape1]
        · have hio1_lt : io + 1 < j := by omega
          have h := helem_pre (io + 1) hio1_lt
          rw [show tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape1]; intro h'; omega]
          exact h
      rcases scanRight13_scan j (p_e + 2) cfgsub.tape hcons13 with ⟨π13, cfg13, hπ13, hs13, hhead13, htape13⟩
    -- 组装：target 区不变量
      have htarget_pre : tapeAgrees tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) := by
        have hsplit := (tapeAgrees_append tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (bitsToSym (tbits.drop j))).mp (by simpa [targetTape] using htarget)
        exact hsplit.1
      have hcfgsub_pre : tapeAgrees cfgsub.tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) := by
        intro i hi
        have h := htarget_pre i hi
        have hlen : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
          simp [List.length_map, List.length_take, min_eq_left (by omega : j ≤ tbits.length)]
        rw [show cfgsub.tape (p_t + (i : ℤ)) = tape1 (p_t + (i : ℤ)) from hleft_sub (p_t + (i : ℤ)) (by omega)]
        rw [show tape1 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
          simp [tape1]
          intro h'
          have hi_lt : (i : ℤ) < (tbits.length : ℤ) := by omega
          omega]
        exact h
      have htarget_next_eq : targetTape (j + 1) ((subOneAt j tbits).getD tbits) =
          (tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true) ++ markFirst b' := by
        have hsubAt : subOneAt j tbits = some ((tbits.take j) ++ b') := by
          rw [subOneAt_eq_drop, hsub_drop]
          rfl
        have hgetD : (subOneAt j tbits).getD tbits = (tbits.take j) ++ b' := by
          rw [hsubAt]
          rfl
        rw [hgetD]
        exact targetTape_succ_append tbits j b' hsub_drop
      have hcfgsub_target : tapeAgrees cfgsub.tape p_t (targetTape (j + 1) ((subOneAt j tbits).getD tbits)) := by
        rw [htarget_next_eq]
        have hlen : ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length = j := by
          simp [List.length_map, List.length_take, min_eq_left (by omega : j ≤ tbits.length)]
        have hsub'' : tapeAgrees cfgsub.tape (p_t + (((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)).length : ℤ)) (markFirst b') := by
          rw [hlen]
          exact htape_sub
        exact (tapeAgrees_append cfgsub.tape p_t ((tbits.take j).map (fun b => if b then Sym.data1 true else Sym.data0 true)) (markFirst b')).mpr ⟨hcfgsub_pre, hsub''⟩
      have hcfgsub_cons : ∀ i : ℕ, i ≤ j → cfgsub.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        have hright_i : cfgsub.tape (p_e + 1 + (i : ℤ)) = tape1 (p_e + 1 + (i : ℤ)) := hright_sub (p_e + 1 + (i : ℤ)) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_i]
        by_cases hij : i = j
        · subst i
          simp [tape1]
        · have hi_lt : i < j := by omega
          have h := helem_pre i hi_lt
          rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
          exact h
      have hcfgsub_rest : tapeAgrees cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) := by
        intro i hi
        have h := helem_rest i hi
        have hright_i : cfgsub.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) := hright_sub (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) (by
          have hlen_drop : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen_drop]
          omega)
        rw [hright_i]
        rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by
          simp [tape1]; intro h'; omega]
        exact h
    -- 组装路径
      have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
      have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
      have hhead6' : cfg6.headPos = p_e - 2 := by
        rw [hhead6]
        simp [Dir.toInt]
        omega
      have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
        rw [← hs6, ← htape6, ← hhead6']
      have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
        rw [hcfg6_eq]; exact hπ7
      have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
      have hhead7' : cfg7.headPos = p_t := by
        rw [hhead7]
        simp [Dir.toInt]
        omega
      have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
        rw [← hs7, ← htape7, ← hhead7']
      have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
        rw [hcfg7_eq]; exact hπ10
      have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
      have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
        rw [← hs10, ← htape10, ← hhead10]
      have hsub' : SymSteps VerifierSym.transition cfg10 πsub cfgsub := by
        rw [hcfg10_eq]; exact hπsub
      have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub) cfgsub := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) πsub h567'' hsub'
      have hcfgsub_eq : cfgsub = SymConfig.mk 81 cfgsub.tape p' := by
        rw [← hs_sub, ← hhead_sub']
      have h12' : SymSteps VerifierSym.transition cfgsub π12 cfg12 := by
        rw [hcfgsub_eq]; exact hπ12
      have h567'''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12) cfg12 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ πsub) π12 h567''' h12'
      have hhead12' : cfg12.headPos = p_e + 2 := by
        rw [hhead12]
        rw [hp_n]
        omega
      have hcfg12_eq : cfg12 = SymConfig.mk 13 cfgsub.tape (p_e + 2) := by
        rw [← hs12, ← htape12, ← hhead12']
      have h13' : SymSteps VerifierSym.transition cfg12 π13 cfg13 := by
        rw [hcfg12_eq]; exact hπ13
      have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12 ++ π13) cfg13 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12) π13 h567'''' h13'
      refine ⟨[step5] ++ π6 ++ π7 ++ π10 ++ πsub ++ π12 ++ π13, cfg13, htotal, Or.inl ⟨hs13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simpa [add_assoc, add_comm, add_left_comm] using hhead13
      · rw [htape13, hvj_bool]
        exact hcfgsub_target
      · intro i hi
        rw [htape13]
        exact hcfgsub_cons i hi
      · rw [htape13]
        exact hcfgsub_rest
      · rw [htape13]
        rw [hright_sub p_e (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        exact hsel
      · rw [htape13]
        rw [hleft_sub (p_t - 1) (by omega)]
        rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
        exact hhashL
      · rw [htape13]
        rw [hright_sub (p_e - 1) (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
        exact hbound
      · rw [htape13]
        rw [hright_sub (p_e + 1 + (ebits.length : ℤ)) (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
          simp [tape1]; intro h; omega]
      · rw [htape13]
        rw [hright_sub p_e (by
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      · intro i hi
        rw [htape13]
        rw [hright_sub i (by
          have hjle : j ≤ tbits.length := Nat.le_of_lt hjt
          have hsum : j + (tbits.length - j) = tbits.length := Nat.add_sub_of_le hjle
          have hz : (p_t : ℤ) + (j : ℤ) + ((tbits.length - j : ℕ) : ℤ) ≤ (p_t : ℤ) + (tbits.length : ℤ) := by
            rw [add_assoc]
            rw [← Nat.cast_add]
            rw [hsum]
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by
            simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        exact hpad i (by omega)
      · intro i hi
        rw [htape13]
        rw [hright_sub i (by
          have hjle : j ≤ tbits.length := Nat.le_of_lt hjt
          have hsum : j + (tbits.length - j) = tbits.length := Nat.add_sub_of_le hjle
          have hz : (p_t : ℤ) + (j : ℤ) + ((tbits.length - j : ℕ) : ℤ) ≤ (p_t : ℤ) + (tbits.length : ℤ) := by
            rw [add_assoc]
            rw [← Nat.cast_add]
            rw [hsum]
          have hlen : (bitsToSym (tbits.drop j)).length = tbits.length - j := by simp [bitsToSym, List.length_drop]
          rw [hlen]
          omega)]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
    · -- 借位越界（2^j > T）：target 不足——状态 5→76→77→10→11→14→…→101（拒绝路径）
      have hlt2 : bitsValue tbits < 2 ^ j := lt_of_not_ge hsub2
      -- [j, L) 段全 false（否则 2^j ≤ T）
      have hall_false : ∀ io : ℕ, j ≤ io → (hlt : io < tbits.length) → tbits[io]'(hlt) = false := by
        intro io hge hlt
        by_contra h
        have htrue : tbits[io] = true := by
          cases hb : tbits[io] <;> simp [hb] at h ⊢
        have hpow : 2 ^ io ≤ bitsValue tbits := bitsValue_ge_pow_of_getElem_true tbits io hlt htrue
        have hge2 : 2 ^ j ≤ 2 ^ io := pow_le_pow_right₀ (by norm_num) hge
        omega
      have hj' : j < tbits.length := by omega
      have htbits_j : tbits[j] = false := hall_false j (by omega) hj'
      -- t_j 处带 = data0（m=0）
      have htape_tj : tape1 (p_t + (j : ℤ)) = Sym.data0 := by
        rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by simp [tape1]; intro h'; omega]
        have h := htarget j (by simpa [targetTape_length] using hj')
        have hget : (targetTape j tbits)[j]'(by simpa [targetTape_length] using hj') = Sym.data0 := by
          rw [targetTape_getElem_ge j j tbits hj' le_rfl]
          simp [htbits_j]
        rw [hget] at h
        exact h
      -- 状态 10 读 t_j（data0 m=0）→ 11（写 data0 m=1 标 m）
      let r10tj : SymTransResult := { nextState := 11, writeSym := Sym.data0 true, moveDir := Dir.S }
      let step10tj : SymStep := { fromState := 10, readSym := Sym.data0, result := r10tj }
      have htrans10tj : step10tj.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ))) := by
        rw [htape_tj]
        simp [step10tj, r10tj]
        decide
      have hstep10tj : SymSteps VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) [step10tj]
          (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) := by
        refine SymSteps.cons [] step10tj (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
        · rfl
        · dsimp [step10tj]
          rw [htape_tj]
        · change step10tj.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ)))
          exact htrans10tj
      let tape2 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data0 true else tape1 i
      have hcfg10tj : symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result =
          SymConfig.mk 11 tape2 (p_t + (j : ℤ)) := by
        simp [symStepConfig, SymConfig.mk, step10tj, r10tj, tape2, Dir.toInt]
      -- 状态 11 读（data0 m=1）→ 14（借位写 data1 m=1）
      let r11 : SymTransResult := { nextState := 14, writeSym := Sym.data1 true, moveDir := Dir.R }
      let step11 : SymStep := { fromState := 11, readSym := Sym.data0 true, result := r11 }
      have htrans11 : step11.result ∈ VerifierSym.transition (11, Sym.data0 true) := by
        simp [step11, r11]
        decide
      have hstep11 : SymSteps VerifierSym.transition (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) [step11]
          (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) := by
        refine SymSteps.cons [] step11 (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
        · rfl
        · dsimp [step11, tape2]
          simp
        · change step11.result ∈ VerifierSym.transition (11, tape2 (p_t + (j : ℤ)))
          simp [tape2]
          exact htrans11
      let tape3 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then Sym.data1 true else tape2 i
      have hcfg11 : symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result =
          SymConfig.mk 14 tape3 (p_t + (j : ℤ) + 1) := by
        simp [symStepConfig, SymConfig.mk, step11, r11, tape3, Dir.toInt]
      -- 状态 14 借位传播：从 p_t + j + 1 到 #₀（p_e - 1）全 data0 → 101
      let n : ℕ := (p_e - 1 - (p_t + (j : ℤ) + 1)).toNat
      have hn_n : (n : ℤ) = p_e - 1 - (p_t + (j : ℤ) + 1) := by
        change ((p_e - 1 - (p_t + (j : ℤ) + 1)).toNat : ℤ) = p_e - 1 - (p_t + (j : ℤ) + 1)
        exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - 1 - (p_t + (j : ℤ) + 1))
      have huf_tape : ∀ i : ℕ, i < n → tape3 (p_t + (j : ℤ) + 1 + (i : ℤ)) = Sym.data0 := by
        intro i hi
        have hx_lt : p_t + (j : ℤ) + 1 + (i : ℤ) < p_e - 1 := by
          have hz : (i : ℤ) < (n : ℤ) := by exact_mod_cast hi
          rw [hn_n] at hz
          omega
        have hne1 : p_t + (j : ℤ) + 1 + (i : ℤ) ≠ p_t + (j : ℤ) := by omega
        simp [tape3, tape2, hne1]
        rw [show tape1 (p_t + (j : ℤ) + 1 + (i : ℤ)) = tape (p_t + (j : ℤ) + 1 + (i : ℤ)) from by
          simp [tape1]; intro h'; omega]
        by_cases hlt : p_t + (j : ℤ) + 1 + (i : ℤ) < p_t + (tbits.length : ℤ)
        · -- target 高位段（[j+1, L) 全 false → data0）
          have ioff : ∃ io : ℕ, (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t := by
            refine ⟨(p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat, ?_⟩
            change ((p_t + (j : ℤ) + 1 + (i : ℤ) - p_t).toNat : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) - p_t
            exact Int.toNat_of_nonneg (by omega)
          rcases ioff with ⟨io, hio⟩
          have hio_lt : io < (targetTape j tbits).length := by
            have hlen : (targetTape j tbits).length = tbits.length := by simp [targetTape_length]
            rw [hlen]
            omega
          have ht := htarget io hio_lt
          have hio_ge : j < io := by omega
          have hio_lt_L : io < tbits.length := by omega
          have hbits_false : tbits[io] = false := hall_false io (Nat.le_of_lt hio_ge) hio_lt_L
          have hsym : (targetTape j tbits)[io] = Sym.data0 := by
            rw [targetTape_getElem_ge j io tbits hio_lt_L (Nat.le_of_lt hio_ge)]
            simp [hbits_false]
          have hidx : p_t + (io : ℤ) = p_t + (j : ℤ) + 1 + (i : ℤ) := by omega
          rw [hidx] at ht
          rw [ht, hsym]
        · -- 填充区（hpad）
          have hpad_i := hpad (p_t + (j : ℤ) + 1 + (i : ℤ)) (by constructor <;> omega)
          rw [hpad_i]
      have huf_bound : tape3 (p_t + (j : ℤ) + 1 + (n : ℤ)) = Sym.boundary := by
        rw [hn_n]
        have hpos : p_t + (j : ℤ) + 1 + (p_e - 1 - (p_t + (j : ℤ) + 1)) = p_e - 1 := by omega
        rw [hpos]
        simp [tape3, tape2, show p_e - 1 ≠ p_t + (j : ℤ) from by omega]
        rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
        exact hbound
      rcases underflow_scan_to_boundary (p_t + (j : ℤ) + 1) n tape3 huf_tape huf_bound
        with ⟨πuf, cfguf, hπuf, hsuf, hheaduf, hdata1uf, hbounduf, hleftuf, hrightuf⟩
      -- 拼链：5 → 76 → 77 → 10 → 11 → 14 → … → 101
      have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
      have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
      have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
        cases cfg6 with
        | mk state tape headPos =>
            change state = 77 at hs6
            change tape = tape1 at htape6
            rw [hs6, htape6]
            congr 1
            change headPos = (p_e + (j : ℤ)) - ((j + 1 : ℕ) : ℤ) + Dir.L.toInt at hhead6
            rw [hhead6]
            simp [Dir.toInt]
            omega
      have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
        rw [hcfg6_eq]; exact hπ7
      have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
      have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
        cases cfg7 with
        | mk state tape headPos =>
            change state = 10 at hs7
            change tape = tape1 at htape7
            rw [hs7, htape7]
            congr 1
            change headPos = (p_e - 2) - (n7 : ℤ) + Dir.R.toInt at hhead7
            rw [hhead7]
            simp [hn7, Dir.toInt]
            omega
      have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
        rw [hcfg7_eq]; exact hπ10
      have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
      have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
        cases cfg10 with
        | mk state tape headPos =>
            change state = 10 at hs10
            change tape = tape1 at htape10
            change headPos = p_t + (j : ℤ) at hhead10
            rw [hs10, htape10, hhead10]
      have h10tj' : SymSteps VerifierSym.transition cfg10 [step10tj]
          (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) := by
        rw [hcfg10_eq]
        exact hstep10tj
      have h567''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
          ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj])
          (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) :=
        SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) [step10tj] h567'' h10tj'
      have h11' : SymSteps VerifierSym.transition (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) step10tj.result) [step11]
          (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) := by
        rw [hcfg10tj]
        exact hstep11
      have h567'''' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
          ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11])
          (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) :=
        SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj]) [step11] h567''' h11'
      have h14' : SymSteps VerifierSym.transition (symStepConfig (SymConfig.mk 11 tape2 (p_t + (j : ℤ))) step11.result) πuf cfguf := by
        rw [hcfg11]
        exact hπuf
      have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
          ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11] ++ πuf) cfguf :=
        SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11]) πuf h567'''' h14'
      -- 结论（101 分支）
      have hhead_uf : cfguf.headPos = p_e := by
        rw [hheaduf]
        rw [hn_n]
        omega
      have hdata1' : ∀ i : ℤ, p_t + (j : ℤ) ≤ i ∧ i < p_e - 1 → (cfguf.tape i).1 = SymKind.data1 := by
        intro i hi
        by_cases heq : i = p_t + (j : ℤ)
        · subst i
          have hl := hleftuf (p_t + (j : ℤ)) (by omega)
          rw [hl]
          simp [tape3, Sym.data1]
        · have hio : ∃ io : ℕ, (io : ℤ) = i - (p_t + (j : ℤ) + 1) := by
            refine ⟨(i - (p_t + (j : ℤ) + 1)).toNat, ?_⟩
            change ((i - (p_t + (j : ℤ) + 1)).toNat : ℤ) = i - (p_t + (j : ℤ) + 1)
            exact Int.toNat_of_nonneg (by omega)
          rcases hio with ⟨io, hio⟩
          have hio_lt : io < n := by
            have hz : (io : ℤ) < (n : ℤ) := by
              rw [hio]
              rw [hn_n]
              omega
            exact_mod_cast hz
          have hd := hdata1uf io hio_lt
          have hidx : i = p_t + (j : ℤ) + 1 + (io : ℤ) := by omega
          rw [hidx, hd]
          simp
      have hcons' : ∀ i : ℕ, i ≤ j → cfguf.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        have hr := hrightuf (p_e + 1 + (i : ℤ)) (by omega)
        rw [hr]
        simp [tape3, tape2, show p_e + 1 + (i : ℤ) ≠ p_t + (j : ℤ) from by omega]
        by_cases heq : i = j
        · subst i
          simp [tape1]
        · have hpre := helem_pre i (by omega)
          rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
          exact hpre
      have hhashL' : cfguf.tape (p_t - 1) = Sym.boundary := by
        have hl := hleftuf (p_t - 1) (by omega)
        rw [hl]
        simp [tape3, tape2, show p_t - 1 ≠ p_t + (j : ℤ) from by omega]
        rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
        exact hhashL
      have hkeep_pe : cfguf.tape p_e = tape p_e := by
        have hr := hrightuf p_e (by omega)
        rw [hr]
        simp [tape3, tape2, show p_e ≠ p_t + (j : ℤ) from by omega]
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      have hbound_pe : cfguf.tape (p_e - 1) = Sym.boundary := by
        rw [show p_e - 1 = p_t + (j : ℤ) + 1 + (n : ℤ) from by rw [hn_n]; omega]
        exact hbounduf
      have hright' : ∀ i : ℤ, p_e + 1 + (j : ℤ) < i → cfguf.tape i = tape i := by
        intro i hi
        have hr := hrightuf i (by omega)
        rw [hr]
        have hne : i ≠ p_t + (j : ℤ) := by omega
        simp [tape3, tape2, hne]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      refine ⟨[step5] ++ π6 ++ π7 ++ π10 ++ [step10tj] ++ [step11] ++ πuf, cfguf, htotal,
        Or.inr ⟨hsuf, hhead_uf, hvj_bool, hlt2, hdata1', hbound_pe, hcons', hhashL', hkeep_pe, hright'⟩⟩
  · -- 标记路径（v_j = false）：状态 5→8→9→11→12→13→5
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data0 := by simpa [hvj_bool] using hvj
    have hp_t_lt : p_t + (tbits.length : ℤ) < p_e := boundary_after_target tbits.length j p_t p_e tape tbits (Nat.le_refl _) hjt (by simpa using hp_t_le) htarget hbound
    have hne_pe : p_e ≠ p_t + (j : ℤ) := by omega
    have hne_pe1 : p_e - 1 ≠ p_t + (j : ℤ) := by omega
    let r5 : SymTransResult := { nextState := 8, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data0, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data0 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 8 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    -- 状态 8 左移 j+1 格到 #₀
    have hnb8 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e
      · subst i
        rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
        rcases hsel with hd | hd
        · right; left; simpa using hd
        · right; right; simpa using hd
      · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
          refine ⟨(i - (p_e + 1)).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
        rcases ioff with ⟨io, hio⟩
        have hio_le : io ≤ j := by omega
        by_cases heqio : io = j
        · subst io
          have hidx : i = p_e + 1 + (j : ℤ) := by omega
          rw [hidx]
          simp [tape1]
          left
          rfl
        · have hio_lt : io < j := by omega
          have ht := helem_pre io hio_lt
          have hidx : p_e + 1 + (io : ℤ) = i := by omega
          have ht' : tape i = Sym.consumed := by
            rw [hidx] at ht
            exact ht
          rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
          rw [ht']
          decide
    have hbound8 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend8 : { nextState := 9, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (8, Sym.boundary) := by decide
    have hkeep8 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 8, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (8, s) := trans8_keep
    rcases scanLeftKeepP 8 9 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb8 hbound8 hkeep8 hend8 rfl
      with ⟨π8, cfg8, hπ8, hs8, hhead8, htape8⟩
    -- 状态 9 左移 (p_e - p_t - 1) 格到 #ₗ
    let n9 : ℕ := (p_e - p_t - 1).toNat
    have hn9 : (n9 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb9 : ∀ i : ℤ, (p_e - 2) - (n9 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn9] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases hlt_target : i < p_t + (tbits.length : ℤ)
      · -- target 位
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hmem : (targetTape j tbits)[io] ∈ targetTape j tbits := List.getElem_mem hio_lt
        have hdata_io := targetTape_data j tbits ((targetTape j tbits)[io]) hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht]
        exact hdata_io
      · -- data0 填充
        have hpad_i := hpad i (by constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        rw [hpad_i]
        decide
    have hbound9 : tape1 ((p_e - 2) - (n9 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n9 : ℤ) = p_t - 1 := by rw [hn9]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend9 : { nextState := 12, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (9, Sym.boundary) := by decide
    have hkeep9 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 9, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (9, s) := trans9_keep
    rcases scanLeftKeepP 9 12 Sym.boundary Dir.R n9 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb9 hbound9 hkeep9 hend9 rfl
      with ⟨π9, cfg9, hπ9, hs9, hhead9, htape9⟩
    -- 状态 12 右移 j 格扫 4F4.4 前缀
    have hkeep11 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 12, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (12, tape1 i) := by
      intro i h
      have hi : p_t ≤ i ∧ i < p_t + (tbits.length : ℤ) := by constructor <;> omega
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape j tbits).length := by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hio_j : io < j := by omega
      have hio_tbits : io < tbits.length := by omega
      have hsym : (targetTape j tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
        simp [targetTape, bitsToSym, hio_j, hio_tbits]
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      rw [ht, hsym]
      have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
          (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
        by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
      exact trans12_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
    rcases scanRightKeep 12 j p_t tape1 hkeep11 with ⟨π11, cfg11, hπ11, hs11, hhead11, htape11⟩
    -- 状态 12 读 t_j（m=0），置 m=1 转 81
    have htape_tj : tape1 (p_t + (j : ℤ)) = (if tbits[j] then Sym.data1 else Sym.data0) := by
      rw [show tape1 (p_t + (j : ℤ)) = tape (p_t + (j : ℤ)) from by simp [tape1]; intro h'; omega]
      have hj' : j < tbits.length := by omega
      have h := htarget j (by
        have hlen : (targetTape j tbits).length = tbits.length := by
          simp [targetTape_length]
        rw [hlen]
        omega)
      simpa [targetTape_getElem_j j tbits hj'] using h
    let tape2 : ℤ → Sym := fun i => if i = p_t + (j : ℤ) then (if tbits[j] then Sym.data1 true else Sym.data0 true) else tape1 i
    let r_tj : SymTransResult := { nextState := 81, writeSym := (if tbits[j] then Sym.data1 true else Sym.data0 true), moveDir := Dir.R }
    let step_tj : SymStep := { fromState := 12, readSym := (if tbits[j] then Sym.data1 else Sym.data0), result := r_tj }
    have htj_mark : ((if tbits[j] then Sym.data1 else Sym.data0).2 = false) := by
      by_cases hb : tbits[j] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    have htj_kind : ((if tbits[j] then Sym.data1 else Sym.data0).1 = SymKind.data0 ∨
        (if tbits[j] then Sym.data1 else Sym.data0).1 = SymKind.data1) := by
      by_cases hb : tbits[j] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    have htrans_tj : step_tj.result ∈ VerifierSym.transition (12, (if tbits[j] then Sym.data1 else Sym.data0)) := by
      by_cases hb : tbits[j]
      · simp [step_tj, r_tj, hb]
        decide
      · simp [step_tj, r_tj, hb]
        decide
    have hstep_tj : SymSteps VerifierSym.transition (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) [step_tj]
        (symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) step_tj.result) := by
      refine SymSteps.cons [] step_tj (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change step_tj.readSym = tape1 (p_t + (j : ℤ))
        simp [step_tj]
        rw [htape_tj]
      · change step_tj.result ∈ VerifierSym.transition (12, tape1 (p_t + (j : ℤ)))
        rw [htape_tj]
        exact htrans_tj
    have hcfg_tj : symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) step_tj.result =
        SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1) := by
      simp [symStepConfig, SymConfig.mk, step_tj, r_tj, tape2, Dir.toInt]
    -- 状态 12 右移回元素区
    let n : ℕ := (p_e - p_t - (j : ℤ)).toNat
    have hn_n : (n : ℤ) = p_e - p_t - (j : ℤ) := by
      change ((p_e - p_t - (j : ℤ)).toNat : ℤ) = p_e - p_t - (j : ℤ)
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (j : ℤ))
    have hnc12 : ∀ i : ℤ, p_t + (j : ℤ) + 1 ≤ i ∧ i < p_t + (j : ℤ) + 1 + (n : ℤ) →
        (tape2 i).1 = SymKind.data0 ∨ (tape2 i).1 = SymKind.data1 ∨ (tape2 i).1 = SymKind.boundary := by
      intro i hi
      have hi_lt_pe : i < p_e + 1 := by
        have := hi.2
        rw [hn_n] at this
        omega
      by_cases hlt_target : i < p_t + (tbits.length : ℤ)
      · -- target 剩余位（t_j+1 到 t_{k-1}）
        have hne_tj : i ≠ p_t + (j : ℤ) := by omega
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_gt : j < io := by omega
        have hio_lt : io < (targetTape j tbits).length := by
          have hlen : (targetTape j tbits).length = tbits.length := by
            simp [targetTape_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hio_tbits : io < tbits.length := by omega
        have hsym : (targetTape j tbits)[io]'(by simpa using hio_tbits) = (if tbits[io] then Sym.data1 else Sym.data0) := by
          exact targetTape_getElem_ge j io tbits hio_tbits (Nat.le_of_lt hio_gt)
        have hnb : ((if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data0 ∨
            (if tbits[io] then Sym.data1 else Sym.data0).1 = SymKind.data1) := by
          by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [show tape2 i = tape1 i from by simp [tape2]; intro h; omega]
        rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
        rw [ht, hsym]
        rcases hnb with hd | hd
        · left; simpa using hd
        · right; left; simpa using hd
      · -- data0 填充 / #₀ / sel
        by_cases hpad_i : i < p_e - 1
        · -- data0 填充
          have h := hpad i (by constructor <;> omega)
          rw [show tape2 i = tape1 i from by simp [tape2]; intro h'; omega]
          rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
          rw [h]
          decide
        · -- i ∈ {p_e-1, p_e}
          by_cases hh0 : i = p_e - 1
          · rw [hh0]
            rw [show tape2 (p_e - 1) = tape1 (p_e - 1) from by simp [tape2]; intro h'; omega]
            rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h'; omega]
            rw [hbound]
            decide
          · have hi_pe : i = p_e := by omega
            rw [hi_pe]
            rw [show tape2 p_e = tape1 p_e from by simp [tape2]; intro h'; omega]
            rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h'; omega]
            rcases hsel with hd | hd
            · left; simpa using hd
            · right; left; simpa using hd
    have hcons12 : tape2 (p_t + (j : ℤ) + 1 + (n : ℤ)) = Sym.consumed := by
      have hpos : p_t + (j : ℤ) + 1 + (n : ℤ) = p_e + 1 := by rw [hn_n]; omega
      rw [hpos]
      rw [show tape2 (p_e + 1) = tape1 (p_e + 1) from by simp [tape2]; intro h; omega]
      by_cases hj0 : j = 0
      · subst j
        simp [tape1]
      · have h0lt : 0 < j := by omega
        have h := helem_pre 0 h0lt
        rw [show tape1 (p_e + 1) = tape (p_e + 1) from by simp [tape1]; intro h'; omega]
        simpa using h
    rcases scanRight81 n (p_t + (j : ℤ) + 1) tape2 hnc12 hcons12 with ⟨π12, cfg12, hπ12, hs12, hhead12, htape12⟩
    -- 状态 13 右移扫 consumed 到 v_{j+1}
    have hcons13 : ∀ i : ℤ, p_e + 2 ≤ i ∧ i < p_e + 2 + (j : ℤ) → tape2 i = Sym.consumed := by
      intro i hi
      have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 2) := by
        refine ⟨(i - (p_e + 2)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 2))
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < j := by omega
      have hidx : i = p_e + 1 + ((io + 1 : ℕ) : ℤ) := by omega
      rw [hidx]
      rw [show tape2 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape2]; intro h; omega]
      have hio1_le : io + 1 ≤ j := by omega
      by_cases hio1_eq : io + 1 = j
      · rw [hio1_eq]
        simp [tape1]
      · have hio1_lt : io + 1 < j := by omega
        have h := helem_pre (io + 1) hio1_lt
        rw [show tape1 (p_e + 1 + ((io + 1 : ℕ) : ℤ)) = tape (p_e + 1 + ((io + 1 : ℕ) : ℤ)) from by simp [tape1]; intro h'; omega]
        exact h
    rcases scanRight13_scan j (p_e + 2) tape2 hcons13 with ⟨π13, cfg13, hπ13, hs13, hhead13, htape13⟩
    -- 组装
    have htarget_next : tapeAgrees tape2 p_t (targetTape (j + 1) tbits) := by
      exact tape_agrees_targetTape_succ_mark tbits.length j tbits p_t tape tape2 (Nat.le_refl _) hjt htarget
        (by simp [tape2])
        (by intro i hi hne
            have htbits_le : p_t + (tbits.length : ℤ) ≤ p_e - 1 := target_ends_before_pe tbits.length j p_t p_e tape tbits (Nat.le_refl _) hjt (by simpa using hp_t_le) htarget hbound
            rw [show tape2 i = tape1 i from by simp [tape2, hne]]
            rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega])
    have hcfg13_cons : ∀ i : ℕ, i ≤ j → tape2 (p_e + 1 + (i : ℤ)) = Sym.consumed := by
      intro i hi
      by_cases hij : i = j
      · subst i
        have hneq : p_e + 1 + (j : ℤ) ≠ p_t + (j : ℤ) := by omega
        rw [show tape2 (p_e + 1 + (j : ℤ)) = tape1 (p_e + 1 + (j : ℤ)) from by
          simp only [tape2]
          rw [if_neg hneq]]
        simp [tape1]
      · have hi_lt : i < j := by omega
        have h := helem_pre i hi_lt
        rw [show tape2 (p_e + 1 + (i : ℤ)) = tape1 (p_e + 1 + (i : ℤ)) from by simp [tape2]; intro h'; omega]
        rw [show tape1 (p_e + 1 + (i : ℤ)) = tape (p_e + 1 + (i : ℤ)) from by simp [tape1]; intro h'; omega]
        exact h
    have hcfg13_rest : tapeAgrees tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits.drop (j + 1))) := by
      intro i hi
      have h := helem_rest i hi
      have hneq : p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ) ≠ p_e + 1 + (j : ℤ) := by omega
      rw [show tape2 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by simp [tape2]; intro h'; omega]
      rw [show tape1 (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) = tape (p_e + 1 + ((j + 1 : ℕ) : ℤ) + (i : ℤ)) from by
        simp [tape1]; intro h'; omega]
      exact h
    -- 组装路径
    have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 8 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
    have h58 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8) cfg8 := SymSteps_trans _ _ _ _ [step5] π8 hstep5' hπ8
    have hhead8' : cfg8.headPos = p_e - 2 := by
      rw [hhead8]
      simp [Dir.toInt]
      omega
    have hcfg8_eq : cfg8 = SymConfig.mk 9 tape1 (p_e - 2) := by
      rw [← hs8, ← htape8, ← hhead8']
    have hπ9' : SymSteps VerifierSym.transition cfg8 π9 cfg9 := by
      rw [hcfg8_eq]; exact hπ9
    have h589 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9) cfg9 := SymSteps_trans _ _ _ _ ([step5] ++ π8) π9 h58 hπ9'
    have hhead9' : cfg9.headPos = p_t := by
      rw [hhead9]
      simp [Dir.toInt]
      omega
    have hcfg9_eq : cfg9 = SymConfig.mk 12 tape1 p_t := by
      rw [← hs9, ← htape9, ← hhead9']
    have hπ11' : SymSteps VerifierSym.transition cfg9 π11 cfg11 := by
      rw [hcfg9_eq]; exact hπ11
    have h58911 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11) cfg11 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9) π11 h589 hπ11'
    have hcfg11_eq : cfg11 = SymConfig.mk 12 tape1 (p_t + (j : ℤ)) := by
      rw [← hs11, ← htape11, ← hhead11]
    have hstep_tj' : SymSteps VerifierSym.transition cfg11 [step_tj] (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) := by
      rw [hcfg11_eq]
      exact hcfg_tj ▸ hstep_tj
    have h58911tj : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj]) (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11) [step_tj] h58911 hstep_tj'
    have h12' : SymSteps VerifierSym.transition (SymConfig.mk 81 tape2 (p_t + (j : ℤ) + 1)) π12 cfg12 := hπ12
    have h58911tj12 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12) cfg12 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj]) π12 h58911tj h12'
    have hhead12' : cfg12.headPos = p_e + 2 := by
      rw [hhead12]
      rw [hn_n]
      omega
    have hcfg12_eq : cfg12 = SymConfig.mk 13 tape2 (p_e + 2) := by
      rw [← hs12, ← htape12, ← hhead12']
    have h13' : SymSteps VerifierSym.transition cfg12 π13 cfg13 := by
      rw [hcfg12_eq]; exact hπ13
    have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12 ++ π13) cfg13 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12) π13 h58911tj12 h13'
    refine ⟨[step5] ++ π8 ++ π9 ++ π11 ++ [step_tj] ++ π12 ++ π13, cfg13, htotal,
      Or.inl ⟨hs13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa [add_assoc, add_comm, add_left_comm] using hhead13
    · rw [htape13]
      simp [hvj_bool]
      exact htarget_next
    · intro i hi
      rw [htape13]
      exact hcfg13_cons i hi
    · rw [htape13]
      exact hcfg13_rest
    · rw [htape13]
      rw [show tape2 p_e = tape1 p_e from by dsimp [tape2]; rw [if_neg (by omega)]]
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
      exact hsel
    · rw [htape13]
      rw [show tape2 (p_t - 1) = tape1 (p_t - 1) from by simp [tape2]; intro h; omega]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    · rw [htape13]
      rw [show tape2 (p_e - 1) = tape1 (p_e - 1) from by dsimp [tape2]; rw [if_neg (by omega)]]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    · rw [htape13]
      rw [show tape2 (p_e + 1 + (ebits.length : ℤ)) = tape1 (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape2]; intro h; omega]
      rw [show tape1 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape1]; intro h; omega]
    · rw [htape13]
      rw [show tape2 p_e = tape1 p_e from by dsimp [tape2]; rw [if_neg (by omega)]]
      rw [show tape1 p_e = tape p_e from by simp [tape1]; intro h; omega]
    · intro i hi
      rw [htape13]
      rw [show tape2 i = tape1 i from by simp [tape2]; intro h; omega]
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]
      exact hpad i (by omega)
    · intro i hi
      rw [htape13]
      rw [show tape2 i = tape1 i from by simp [tape2]; intro h; omega]
      rw [show tape1 i = tape i from by simp [tape1]; intro h; omega]


/-- 边界位（j = tbits.length）：10/12 右扫越过整个标记区域后读 #₀ → 101。 -/
lemma process_one_bit_boundary (j : ℕ) (v_j : Bool) (tbits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hj_eq : j = tbits.length)
    (hregion : p_t + (tbits.length : ℤ) = p_e - 1)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape tbits.length tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (hvj : tape (p_e + 1 + (j : ℤ)) = if v_j then Sym.data1 else Sym.data0) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 101 := by
  have hnb_scan6 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
      (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i h
    have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
    by_cases heq : i = p_e
    · subst i
      rcases hsel with hd | hd
      · right; left; simpa using hd
      · right; right; simpa using hd
    · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
        refine ⟨(i - (p_e + 1)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
      rcases ioff with ⟨io, hio⟩
      have hio_le : io ≤ j := by omega
      by_cases heqio : io = j
      · subst io
        have hidx : i = p_e + 1 + (j : ℤ) := by omega
        rw [hidx]
        rw [hvj]
        by_cases hvb : v_j <;> simp [hvb]
      · have hio_lt : io < j := by omega
        have ht := helem_pre io hio_lt
        have hidx : p_e + 1 + (io : ℤ) = i := by omega
        have ht' : tape i = Sym.consumed := by
          rw [hidx] at ht
          exact ht
        rw [ht']
        decide
  have hnb_scan7 : ∀ i : ℤ, (p_e - 2) - (((p_e - p_t - 1).toNat : ℕ) : ℤ) < i ∧ i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i h
    have hz : (((p_e - p_t - 1).toNat : ℕ) : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    rw [hz] at h
    have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
      refine ⟨(i - p_t).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < (targetTape tbits.length tbits).length := by
      have hlen : (targetTape tbits.length tbits).length = tbits.length := by
        simp [targetTape_length]
      rw [hlen]
      have hsub : p_e - 1 - p_t = (tbits.length : ℤ) := by
        rw [← hregion]
        omega
      have hz2 : (io : ℤ) < (tbits.length : ℤ) := by
        rw [hio]
        omega
      exact_mod_cast hz2
    have ht := htarget io hio_lt
    have hmem : (targetTape tbits.length tbits)[io] ∈ targetTape tbits.length tbits := List.getElem_mem hio_lt
    have hdata_io := targetTape_data tbits.length tbits ((targetTape tbits.length tbits)[io]) hmem
    have hidx : p_t + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [ht]
    exact hdata_io
  have hkeep_marked10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape i) := by
    intro i h
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
      refine ⟨(i - p_t).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
    rcases ioff with ⟨io, hio⟩
    have hio_tbits : io < tbits.length := by
      rw [← hj_eq]
      omega
    have hio_lt : io < (targetTape tbits.length tbits).length := by
      have hlen : (targetTape tbits.length tbits).length = tbits.length := by simp [targetTape_length]
      rw [hlen]
      exact hio_tbits
    have ht := htarget io hio_lt
    have hsym : (targetTape tbits.length tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
      exact targetTape_getElem_lt tbits.length io tbits hio_tbits hio_tbits
    have hidx : p_t + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [ht, hsym]
    have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
        (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
      by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    exact trans10_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
  have hkeep_marked12 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 12, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (12, tape i) := by
    intro i h
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
      refine ⟨(i - p_t).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
    rcases ioff with ⟨io, hio⟩
    have hio_tbits : io < tbits.length := by
      rw [← hj_eq]
      omega
    have hio_lt : io < (targetTape tbits.length tbits).length := by
      have hlen : (targetTape tbits.length tbits).length = tbits.length := by simp [targetTape_length]
      rw [hlen]
      exact hio_tbits
    have ht := htarget io hio_lt
    have hsym : (targetTape tbits.length tbits)[io] = (if tbits[io] then Sym.data1 true else Sym.data0 true) := by
      exact targetTape_getElem_lt tbits.length io tbits hio_tbits hio_tbits
    have hidx : p_t + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [ht, hsym]
    have hk : ((if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data0 ∨
        (if tbits[io] then Sym.data1 true else Sym.data0 true).1 = SymKind.data1) := by
      by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
    exact trans12_marked (if tbits[io] then Sym.data1 true else Sym.data0 true) (by by_cases hb : tbits[io] <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]) hk
  by_cases hvj_bool : v_j
  · -- b = true：5 → 76 → 77 → 10 → 扫 j 格 → #₀ → 101
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hvj_bool] using hvj
    let r5 : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data1, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data1 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 76 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    have hnb6 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e + 1 + (j : ℤ)
      · subst i
        simp [tape1]
        left
        rfl
      · have hnb_i := hnb_scan6 i h
        rw [show tape1 i = tape i from by
          simp only [tape1]
          rw [if_neg (by intro h'; exact heq h')]]
        exact hnb_i
    have hbound6 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend6 : { nextState := 77, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (76, Sym.boundary) := by decide
    have hkeep6 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 76, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (76, s) := trans76_keep
    rcases scanLeftKeepP 76 77 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb6 hbound6 hkeep6 hend6 rfl
      with ⟨π6, cfg6, hπ6, hs6, hhead6, htape6⟩
    let n7 : ℕ := (p_e - p_t - 1).toNat
    have hn7 : (n7 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb7 : ∀ i : ℤ, (p_e - 2) - (n7 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn7] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases heq : i = p_e + 1 + (j : ℤ)
      · exfalso
        omega
      · have hnb_i := hnb_scan7 i (by rw [hn7]; constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        exact hnb_i
    have hbound7 : tape1 ((p_e - 2) - (n7 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n7 : ℤ) = p_t - 1 := by rw [hn7]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend7 : { nextState := 10, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (77, Sym.boundary) := by decide
    have hkeep7 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 77, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (77, s) := trans77_keep
    rcases scanLeftKeepP 77 10 Sym.boundary Dir.R n7 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb7 hbound7 hkeep7 hend7 rfl
      with ⟨π7, cfg7, hπ7, hs7, hhead7, htape7⟩
    have hkeep10 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 10, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (10, tape1 i) := by
      intro i h
      have hnb_i := hkeep_marked10 i h
      rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
      exact hnb_i
    rcases scanRightKeep 10 j p_t tape1 hkeep10 with ⟨π10, cfg10, hπ10, hs10, hhead10, htape10⟩
    have htj_bound : tape1 (p_t + (j : ℤ)) = Sym.boundary := by
      rw [show p_t + (j : ℤ) = p_e - 1 from by rw [hj_eq]; exact hregion]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    let rfin : SymTransResult := { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.L }
    let stepfin : SymStep := { fromState := 10, readSym := Sym.boundary, result := rfin }
    have htransfin : stepfin.result ∈ VerifierSym.transition (10, tape1 (p_t + (j : ℤ))) := by
      rw [htj_bound]
      decide
    have hstepfin : SymSteps VerifierSym.transition (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) [stepfin]
        (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) stepfin.result) := by
      refine SymSteps.cons [] stepfin (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · simpa [stepfin] using htj_bound.symm
      · exact htransfin
    have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 76 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
    have h567 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6) cfg6 := SymSteps_trans _ _ _ _ [step5] π6 hstep5' hπ6
    have hcfg6_eq : cfg6 = SymConfig.mk 77 tape1 (p_e - 2) := by
      cases cfg6 with
      | mk state tape headPos =>
          change state = 77 at hs6
          change tape = tape1 at htape6
          rw [hs6, htape6]
          congr 1
          change headPos = (p_e + (j : ℤ)) - ((j + 1 : ℕ) : ℤ) + Dir.L.toInt at hhead6
          rw [hhead6]
          simp [Dir.toInt]
          omega
    have hπ7' : SymSteps VerifierSym.transition cfg6 π7 cfg7 := by
      rw [hcfg6_eq]; exact hπ7
    have h567' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7) cfg7 := SymSteps_trans _ _ _ _ ([step5] ++ π6) π7 h567 hπ7'
    have hcfg7_eq : cfg7 = SymConfig.mk 10 tape1 p_t := by
      cases cfg7 with
      | mk state tape headPos =>
          change state = 10 at hs7
          change tape = tape1 at htape7
          rw [hs7, htape7]
          congr 1
          change headPos = (p_e - 2) - (n7 : ℤ) + Dir.R.toInt at hhead7
          rw [hhead7]
          simp [hn7, Dir.toInt]
          omega
    have hπ10' : SymSteps VerifierSym.transition cfg7 π10 cfg10 := by
      rw [hcfg7_eq]; exact hπ10
    have h567'' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π6 ++ π7 ++ π10) cfg10 := SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7) π10 h567' hπ10'
    have hcfg10_eq : cfg10 = SymConfig.mk 10 tape1 (p_t + (j : ℤ)) := by
      cases cfg10 with
      | mk state tape headPos =>
          change state = 10 at hs10
          change tape = tape1 at htape10
          change headPos = p_t + (j : ℤ) at hhead10
          rw [hs10, htape10, hhead10]
    have hfin' : SymSteps VerifierSym.transition cfg10 [stepfin]
        (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) stepfin.result) := by
      rw [hcfg10_eq]
      exact hstepfin
    have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
        ([step5] ++ π6 ++ π7 ++ π10 ++ [stepfin])
        (symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) stepfin.result) :=
      SymSteps_trans _ _ _ _ ([step5] ++ π6 ++ π7 ++ π10) [stepfin] h567'' hfin'
    exact ⟨[step5] ++ π6 ++ π7 ++ π10 ++ [stepfin], symStepConfig (SymConfig.mk 10 tape1 (p_t + (j : ℤ))) stepfin.result, htotal, rfl⟩
  · -- b = false：5 → 8 → 9 → 12 → 扫 j 格 → #₀ → 101
    have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data0 := by simpa [hvj_bool] using hvj
    let r5 : SymTransResult := { nextState := 8, writeSym := Sym.consumed, moveDir := Dir.L }
    let step5 : SymStep := { fromState := 5, readSym := Sym.data0, result := r5 }
    have htrans5 : step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ))) := by
      rw [hvj']
      decide
    let tape1 : ℤ → Sym := fun i => if i = p_e + 1 + (j : ℤ) then Sym.consumed else tape i
    have hstep5 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5]
        (symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result) := by
      refine SymSteps.cons [] step5 (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data0 = tape (p_e + 1 + (j : ℤ))
        rw [hvj']
      · change step5.result ∈ VerifierSym.transition (5, tape (p_e + 1 + (j : ℤ)))
        rw [hvj']
        decide
    have hcfg5 : symStepConfig (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) step5.result =
        SymConfig.mk 8 tape1 (p_e + (j : ℤ)) := by
      simp [symStepConfig, SymConfig.mk, step5, r5, tape1, Dir.toInt]
      omega
    have hnb8 : ∀ i : ℤ, p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (j : ℤ) →
        (tape1 i).1 = SymKind.consumed ∨ (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      have hi : p_e ≤ i ∧ i ≤ p_e + (j : ℤ) := by constructor <;> omega
      by_cases heq : i = p_e + 1 + (j : ℤ)
      · subst i
        simp [tape1]
        left
        rfl
      · have hnb_i := hnb_scan6 i h
        rw [show tape1 i = tape i from by
          simp only [tape1]
          rw [if_neg (by intro h'; exact heq h')]]
        exact hnb_i
    have hbound8 : tape1 (p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ)) = Sym.boundary := by
      have hpos : p_e + (j : ℤ) - ((j + 1 : ℕ) : ℤ) = p_e - 1 := by omega
      rw [hpos]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    have hend8 : { nextState := 9, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (8, Sym.boundary) := by decide
    have hkeep8 : ∀ s : Sym, s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 8, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (8, s) := trans8_keep
    rcases scanLeftKeepP 8 9 Sym.boundary Dir.L (j + 1) (p_e + (j : ℤ)) tape1
        (fun s => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb8 hbound8 hkeep8 hend8 rfl
      with ⟨π8, cfg8, hπ8, hs8, hhead8, htape8⟩
    let n9 : ℕ := (p_e - p_t - 1).toNat
    have hn9 : (n9 : ℤ) = p_e - p_t - 1 := by
      change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
      exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
    have hnb9 : ∀ i : ℤ, (p_e - 2) - (n9 : ℤ) < i ∧ i ≤ p_e - 2 → (tape1 i).1 = SymKind.data0 ∨ (tape1 i).1 = SymKind.data1 := by
      intro i h
      rw [hn9] at h
      have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
      by_cases heq : i = p_e + 1 + (j : ℤ)
      · exfalso
        omega
      · have hnb_i := hnb_scan7 i (by rw [hn9]; constructor <;> omega)
        rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
        exact hnb_i
    have hbound9 : tape1 ((p_e - 2) - (n9 : ℤ)) = Sym.boundary := by
      have hpos : (p_e - 2) - (n9 : ℤ) = p_t - 1 := by rw [hn9]; omega
      rw [hpos]
      rw [show tape1 (p_t - 1) = tape (p_t - 1) from by simp [tape1]; intro h; omega]
      exact hhashL
    have hend9 : { nextState := 12, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (9, Sym.boundary) := by decide
    have hkeep9 : ∀ s : Sym, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 →
        { nextState := 9, writeSym := s, moveDir := Dir.L } ∈ VerifierSym.transition (9, s) := trans9_keep
    rcases scanLeftKeepP 9 12 Sym.boundary Dir.R n9 (p_e - 2) tape1
        (fun s => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) hnb9 hbound9 hkeep9 hend9 rfl
      with ⟨π9, cfg9, hπ9, hs9, hhead9, htape9⟩
    have hkeep11 : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (j : ℤ) → { nextState := 12, writeSym := tape1 i, moveDir := Dir.R } ∈ VerifierSym.transition (12, tape1 i) := by
      intro i h
      have hnb_i := hkeep_marked12 i h
      rw [show tape1 i = tape i from by simp [tape1]; intro h'; omega]
      exact hnb_i
    rcases scanRightKeep 12 j p_t tape1 hkeep11 with ⟨π11, cfg11, hπ11, hs11, hhead11, htape11⟩
    have htj_bound : tape1 (p_t + (j : ℤ)) = Sym.boundary := by
      rw [show p_t + (j : ℤ) = p_e - 1 from by rw [hj_eq]; exact hregion]
      rw [show tape1 (p_e - 1) = tape (p_e - 1) from by simp [tape1]; intro h; omega]
      exact hbound
    let rfin : SymTransResult := { nextState := 101, writeSym := Sym.boundary, moveDir := Dir.R }
    let stepfin : SymStep := { fromState := 12, readSym := Sym.boundary, result := rfin }
    have htransfin : stepfin.result ∈ VerifierSym.transition (12, tape1 (p_t + (j : ℤ))) := by
      rw [htj_bound]
      decide
    have hstepfin : SymSteps VerifierSym.transition (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) [stepfin]
        (symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) stepfin.result) := by
      refine SymSteps.cons [] stepfin (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) SymSteps.nil ?_ ?_ ?_
      · rfl
      · simpa [stepfin] using htj_bound.symm
      · exact htransfin
    have hstep5' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) [step5] (SymConfig.mk 8 tape1 (p_e + (j : ℤ))) := hcfg5 ▸ hstep5
    have h58 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8) cfg8 := SymSteps_trans _ _ _ _ [step5] π8 hstep5' hπ8
    have hcfg8_eq : cfg8 = SymConfig.mk 9 tape1 (p_e - 2) := by
      cases cfg8 with
      | mk state tape headPos =>
          change state = 9 at hs8
          change tape = tape1 at htape8
          rw [hs8, htape8]
          congr 1
          change headPos = (p_e + (j : ℤ)) - ((j + 1 : ℕ) : ℤ) + Dir.L.toInt at hhead8
          rw [hhead8]
          simp [Dir.toInt]
          omega
    have hπ9' : SymSteps VerifierSym.transition cfg8 π9 cfg9 := by
      rw [hcfg8_eq]; exact hπ9
    have h589 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9) cfg9 := SymSteps_trans _ _ _ _ ([step5] ++ π8) π9 h58 hπ9'
    have hcfg9_eq : cfg9 = SymConfig.mk 12 tape1 p_t := by
      cases cfg9 with
      | mk state tape headPos =>
          change state = 12 at hs9
          change tape = tape1 at htape9
          rw [hs9, htape9]
          congr 1
          change headPos = (p_e - 2) - (n9 : ℤ) + Dir.R.toInt at hhead9
          rw [hhead9]
          simp [hn9, Dir.toInt]
          omega
    have hπ11' : SymSteps VerifierSym.transition cfg9 π11 cfg11 := by
      rw [hcfg9_eq]; exact hπ11
    have h58911 : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) ([step5] ++ π8 ++ π9 ++ π11) cfg11 := SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9) π11 h589 hπ11'
    have hcfg11_eq : cfg11 = SymConfig.mk 12 tape1 (p_t + (j : ℤ)) := by
      cases cfg11 with
      | mk state tape headPos =>
          change state = 12 at hs11
          change tape = tape1 at htape11
          change headPos = p_t + (j : ℤ) at hhead11
          rw [hs11, htape11, hhead11]
    have hfin' : SymSteps VerifierSym.transition cfg11 [stepfin]
        (symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) stepfin.result) := by
      rw [hcfg11_eq]
      exact hstepfin
    have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ)))
        ([step5] ++ π8 ++ π9 ++ π11 ++ [stepfin])
        (symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) stepfin.result) :=
      SymSteps_trans _ _ _ _ ([step5] ++ π8 ++ π9 ++ π11) [stepfin] h58911 hfin'
    exact ⟨[step5] ++ π8 ++ π9 ++ π11 ++ [stepfin], symStepConfig (SymConfig.mk 12 tape1 (p_t + (j : ℤ))) stepfin.result, htotal, rfl⟩

/-- 逐位减溢出循环（区域版）：tbits 填满 [p_t, p_e-1)（hregion），位越界或值溢出必到 101。 -/
lemma subtract_loop_overflow_gen (tbits ebits : List Bool) (j : ℕ) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hebits_pos : 1 ≤ ebits.length)
    (hlt : bitsValue tbits < 2 ^ j * bitsValue ebits)
    (hj_le : j ≤ tbits.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (hregion : p_t + (tbits.length : ℤ) = p_e - 1)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (helem_pre : ∀ i : ℕ, i < j → tape (p_e + 1 + (i : ℤ)) = Sym.consumed)
    (helem_rest : tapeAgrees tape (p_e + 1 + (j : ℤ)) (bitsToSym ebits)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) π cfg' ∧
      cfg'.state = 101 := by
  induction ebits generalizing tbits j p_t p_e tape with
  | nil =>
      exfalso
      simp at hebits_pos
  | cons b rest ih =>
      have hvj : tape (p_e + 1 + (j : ℤ)) = if b then Sym.data1 else Sym.data0 := by
        have h0 := helem_rest 0 (by simp [bitsToSym])
        simpa [bitsToSym_cons] using h0
      let ebits_full : List Bool := List.replicate j false ++ (b :: rest)
      have helen_full : ebits_full.length = j + 1 + rest.length := by
        simp [ebits_full]
        omega
      have helem_rest_full : tapeAgrees tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (ebits_full.drop (j + 1))) := by
        have hdrop : ebits_full.drop (j + 1) = rest := by
          dsimp [ebits_full]
          simp [List.drop_append, List.length_replicate]
        rw [hdrop]
        intro i hi
        have h := helem_rest (i + 1) (by
          simp [bitsToSym] at hi ⊢
          omega)
        simpa [bitsToSym_cons, add_assoc, add_comm, add_left_comm] using h
      have hjh : j < ebits_full.length := by
        rw [helen_full]
        omega
      by_cases hjt' : j < tbits.length
      · -- 区域内位
        by_cases hov : b ∧ bitsValue tbits < 2 ^ j
        · -- 溢出位：借位穿 #₀ → 101
          have hb : b = true := hov.1
          have hvj' : tape (p_e + 1 + (j : ℤ)) = Sym.data1 := by simpa [hb] using hvj
          rcases process_one_bit_overflow j tbits p_t p_e tape hjt' hp_t_le hbound hpad htarget hhashL hsel helem_pre hvj' hov.2
            with ⟨π₁, cfg₁, hπ₁, h101⟩
          exact ⟨π₁, cfg₁, hπ₁, h101⟩
        · -- 正常位：process_one_bit_region 的正常分支，然后递归（或 hlt 矛盾）
          rcases process_one_bit_region j b tbits ebits_full p_t p_e tape hjt' hjh hp_t_le hbound hpad htarget hhashL hsel helem_pre hvj helem_rest_full
            with ⟨π₁, cfg₁, hπ₁, hres1⟩
          rcases hres1 with hnorm | hover
          · rcases hnorm with ⟨hstate₁, hhead₁, hta₁, hcons₁, hrest₁, hsel₁, hhashL₁, hbound₁, hsep₁, hpe_eq₁, hpad_keep₁, hright₁⟩
            let tbits' : List Bool := if b then (subOneAt j tbits).getD tbits else tbits
            have htbits'_eq : tbits' = subAllBitsAt tbits [b] j := by
              simp [tbits', subAllBitsAt]
            have hsub : (if b then 2 ^ j else 0) ≤ bitsValue tbits := by
              by_cases hb : b
              · simp [hb]
                have hnot : ¬ bitsValue tbits < 2 ^ j := by
                  intro h
                  exact hov ⟨hb, h⟩
                omega
              · simp [hb]
            have hval : bitsValue tbits' = bitsValue tbits - (if b then 2 ^ j else 0) := by
              by_cases hb : b
              · have hval' := subAllBitsAt_value tbits [b] j (by simpa [hb, bitsValue] using hsub)
                rw [← htbits'_eq] at hval'
                have hb_val : bitsValue [b] = 1 := by simp [hb]
                simpa [hb, hb_val] using hval'
              · have hval' := subAllBitsAt_value tbits [b] j (by simp [hb])
                rw [← htbits'_eq] at hval'
                have hb_val : bitsValue [b] = 0 := by simp [hb]
                simpa [hb, hb_val] using hval'
            have hlt' : bitsValue tbits' < 2 ^ (j + 1) * bitsValue rest := by
              by_cases hb : b
              · have hbval : bitsValue (b :: rest) = 1 + 2 * bitsValue rest := by simp [hb]
                have hlt0 : bitsValue tbits < 2 ^ j * (1 + 2 * bitsValue rest) := by simpa [hbval] using hlt
                have hle1 : 2 ^ j ≤ bitsValue tbits := by simpa [hb] using hsub
                rw [hval]
                simp [hb]
                have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
                  rw [pow_succ]
                  ring
                rw [← hpow]
                have hsum : 2 ^ j * (1 + 2 * bitsValue rest) = 2 ^ j + 2 ^ j * (2 * bitsValue rest) := by ring
                rw [hsum] at hlt0
                omega
              · have hbval : bitsValue (b :: rest) = 2 * bitsValue rest := by simp [hb]
                have hlt0 : bitsValue tbits < 2 ^ j * (2 * bitsValue rest) := by simpa [hbval] using hlt
                have hpow : 2 ^ j * (2 * bitsValue rest) = 2 ^ (j + 1) * bitsValue rest := by
                  rw [pow_succ]
                  ring
                rw [hval]
                simp [hb]
                simpa [hpow] using hlt0
            have hp_t_le' : p_t + (tbits'.length : ℤ) ≤ p_e := by
              have hlen : tbits'.length = tbits.length := by
                rw [htbits'_eq]
                exact subAllBitsAt_length tbits [b] j
              rw [hlen]
              exact hp_t_le
            have hregion' : p_t + (tbits'.length : ℤ) = p_e - 1 := by
              have hlen : tbits'.length = tbits.length := by
                rw [htbits'_eq]
                exact subAllBitsAt_length tbits [b] j
              rw [hlen]
              exact hregion
            have hbound' : cfg₁.tape (p_e - 1) = Sym.boundary := hbound₁
            have hpad' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg₁.tape i = Sym.data0 := by
              intro i hi
              have hlen : tbits'.length = tbits.length := by
                rw [htbits'_eq]
                exact subAllBitsAt_length tbits [b] j
              rw [hlen] at hi
              exact hpad_keep₁ i hi
            have hhashL' : cfg₁.tape (p_t - 1) = Sym.boundary := hhashL₁
            have htarget' : tapeAgrees cfg₁.tape p_t (targetTape (j + 1) tbits') := by
              simpa [tbits'] using hta₁
            have helem_pre' : ∀ i : ℕ, i < j + 1 → cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
              intro i hi
              exact hcons₁ i (by omega)
            have hsel' : (cfg₁.tape p_e).1 = SymKind.data0 ∨ (cfg₁.tape p_e).1 = SymKind.data1 := hsel₁
            have hstate_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
              cases cfg₁ with
              | mk s t hp =>
                  dsimp
                  rw [show s = 13 from hstate₁]
                  rw [show hp = p_e + 1 + ((j + 1 : ℕ) : ℤ) from hhead₁]
                  norm_num
            cases rest with
            | nil =>
                -- 最后一位且未溢出：hlt 与 ¬hov 矛盾
                exfalso
                have hlt_l := hlt
                by_cases hb : b
                · simp [hb] at hlt_l
                  have hnot : 2 ^ j ≤ bitsValue tbits := Nat.le_of_not_gt (by intro h; exact hov ⟨hb, h⟩)
                  omega
                · simp [hb] at hlt_l
            | cons b2 rest2 =>
                -- 13 读 v_{j+1}（data）→ 5 S
                have hd : cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = (if b2 then Sym.data1 else Sym.data0) := by
                  have hdrop : ebits_full.drop (j + 1) = b2 :: rest2 := by
                    dsimp [ebits_full]
                    simp [List.drop_append, List.length_replicate, List.drop]
                  have h0 := hrest₁ 0 (by simp [bitsToSym, hdrop])
                  simpa [bitsToSym, hdrop] using h0
                let r5b : SymTransResult := { nextState := 5, writeSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), moveDir := Dir.S }
                let step5b : SymStep := { fromState := 13, readSym := cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)), result := r5b }
                have hcfg₁_eq : cfg₁ = SymConfig.mk 13 cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := hstate_eq
                have htrans5b : step5b.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos) := by
                  rw [hcfg₁_eq]
                  by_cases hb2 : b2
                  · unfold step5b r5b
                    rw [show cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data1 from by simpa [if_pos hb2] using hd]
                    simp [SymConfig.mk]
                    decide
                  · unfold step5b r5b
                    rw [show cfg₁.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) = Sym.data0 from by simpa [if_neg hb2] using hd]
                    simp [SymConfig.mk]
                    decide
                have hstep5b : SymSteps VerifierSym.transition cfg₁ [step5b] (symStepConfig cfg₁ step5b.result) := by
                  refine SymSteps.cons [] step5b cfg₁ SymSteps.nil ?_ ?_ ?_
                  · simpa [step5b] using hstate₁.symm
                  · rw [hhead₁]
                  · exact htrans5b
                let cfg5b : SymConfig := symStepConfig cfg₁ step5b.result
                have htape5b : cfg5b.tape = cfg₁.tape := by
                  dsimp [cfg5b]
                  simp only [symStepConfig, SymConfig.mk, step5b, r5b]
                  funext i
                  by_cases h : i = p_e + 1 + ((j + 1 : ℕ) : ℤ)
                  · rw [hcfg₁_eq]
                    rw [h]
                    simp
                  · rw [hcfg₁_eq]
                    rw [if_neg h]
                have hhead5b : cfg5b.headPos = p_e + 1 + ((j + 1 : ℕ) : ℤ) := by
                  dsimp [cfg5b]
                  simp only [symStepConfig, SymConfig.mk, step5b, r5b, Dir.toInt]
                  rw [hcfg₁_eq]
                  simp
                have hstate5b : cfg5b.state = 5 := by
                  dsimp [cfg5b]
                  simp only [symStepConfig, SymConfig.mk, step5b, r5b]
                have htotal_pre : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step5b]) cfg5b :=
                  SymSteps_trans _ _ _ _ π₁ [step5b] hπ₁ hstep5b
                have hbound'' : cfg5b.tape (p_e - 1) = Sym.boundary := by rw [htape5b]; exact hbound₁
                have hhashL'' : cfg5b.tape (p_t - 1) = Sym.boundary := by rw [htape5b]; exact hhashL₁
                have hpad'' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p_e - 1 → cfg5b.tape i = Sym.data0 := by
                  intro i hi
                  rw [htape5b]
                  exact hpad' i hi
                have hsel'' : (cfg5b.tape p_e).1 = SymKind.data0 ∨ (cfg5b.tape p_e).1 = SymKind.data1 := by
                  rw [htape5b]
                  exact hsel₁
                have helem_pre'' : ∀ i : ℕ, i < j + 1 → cfg5b.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
                  intro i hi
                  simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                  exact hcons₁ i (Nat.le_of_lt_succ hi)
                have helem_rest'' : tapeAgrees cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) (bitsToSym (b2 :: rest2)) := by
                  simp only [show cfg5b.tape = cfg₁.tape from htape5b]
                  have hdrop2 : ebits_full.drop (j + 1) = b2 :: rest2 := by
                    dsimp [ebits_full]
                    simp [List.drop_append, List.length_replicate, List.drop]
                  rw [hdrop2] at hrest₁
                  exact hrest₁
                have hcfg5b_eq : cfg5b = SymConfig.mk 5 cfg5b.tape (p_e + 1 + ((j + 1 : ℕ) : ℤ)) := by
                  rw [← hstate5b, ← hhead5b]
                rw [← htape5b] at htarget'
                have hj_le' : j + 1 ≤ tbits'.length := by
                  have hlen : tbits'.length = tbits.length := by
                    rw [htbits'_eq]
                    exact subAllBitsAt_length tbits [b] j
                  rw [hlen]
                  omega
                rcases ih tbits' (j + 1) p_t p_e cfg5b.tape (by simp : 1 ≤ (b2 :: rest2).length) hlt' hj_le' hp_t_le' hregion' htarget'
                    hbound'' hhashL'' hpad'' hsel'' helem_pre'' helem_rest''
                    with ⟨π₂, cfg₂, hπ₂, h101₂⟩
                have hπ₂' : SymSteps VerifierSym.transition cfg5b π₂ cfg₂ := by
                  rw [hcfg5b_eq]
                  exact hπ₂
                have htotal : SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + 1 + (j : ℤ))) (π₁ ++ [step5b] ++ π₂) cfg₂ :=
                  SymSteps_trans _ _ _ _ (π₁ ++ [step5b]) π₂ htotal_pre hπ₂'
                exact ⟨π₁ ++ [step5b] ++ π₂, cfg₂, htotal, h101₂⟩
          · -- 溢出分支与 ¬hov 矛盾
            exfalso
            rcases hover with ⟨_, _, hb, hlt2, _⟩
            exact hov ⟨hb, hlt2⟩
      · -- 边界位：j = tbits.length，右扫越过区域读 #₀ → 101
        have hj_eq : j = tbits.length := by omega
        have htarget_full : tapeAgrees tape p_t (targetTape tbits.length tbits) := by
          rw [← hj_eq]
          exact htarget
        rcases process_one_bit_boundary j b tbits p_t p_e tape hj_eq hregion hp_t_le htarget_full hbound hhashL hpad hsel helem_pre hvj
          with ⟨π₁, cfg₁, hπ₁, h101⟩
        exact ⟨π₁, cfg₁, hπ₁, h101⟩

/-- 选中元素 v 超过当前 target（v > T）：从状态 4（带头在元素标记）经减法链必到 101。
    （tbits 扩展到恰好填满 [p_t, p) 区域，值/长度溢出统一走借位穿 #₀ 或右扫读 #₀。） -/
lemma subtract_overflow_from_4 (v : ℕ) (tbits : List Bool) (p_t p : ℤ) (tape : ℤ → Sym)
    (hv_pos : 0 < v)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p)
    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape p = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p → tape i = Sym.data0)
    (hmark_sel : tape (p + 1) = Sym.sel)
    (hvals_bits : tapeAgrees tape (p + 2) (bitsToSym (bitsOf v)))
    (hgt_v : bitsValue tbits < v) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) π cfg' ∧ cfg'.state = 101 := by
  have hgt_bits : bitsValue tbits < bitsValue (bitsOf v) := by
    simpa [bitsValue_bitsOf] using hgt_v
  let n : ℕ := (p - p_t).toNat
  have hnn : (n : ℤ) = p - p_t := by
    change ((p - p_t).toNat : ℤ) = p - p_t
    exact Int.toNat_of_nonneg (by omega : 0 ≤ p - p_t)
  have hlen_le_n : tbits.length ≤ n := by
    have hz : (tbits.length : ℤ) ≤ (n : ℤ) := by
      rw [hnn]
      omega
    exact_mod_cast hz
  let tbits_ext : List Bool := tbits ++ List.replicate (n - tbits.length) false
  have htbits_ext_length : tbits_ext.length = n := by
    dsimp [tbits_ext]
    simp [hlen_le_n]
  have htarget_ext : tapeAgrees tape p_t (targetTape 0 tbits_ext) := by
    rw [targetTape_zero]
    have htape_bits : tapeAgrees tape p_t (bitsToSym tbits) := by
      simpa [targetTape_zero] using htarget
    have htape_pad : tapeAgrees tape (p_t + (tbits.length : ℤ)) (bitsToSym (List.replicate (n - tbits.length) false)) := by
      intro i hi
      have hlen : (bitsToSym (List.replicate (n - tbits.length) false)).length = n - tbits.length := by
        simp [bitsToSym]
      have hi' : i < n - tbits.length := by simpa [hlen] using hi
      have hpad_i := hpad (p_t + (tbits.length : ℤ) + (i : ℤ)) (by
        constructor
        · omega
        · have hz : (i : ℤ) < (n - tbits.length : ℕ) := by exact_mod_cast hi'
          omega)
      rw [hpad_i]
      have hget : (bitsToSym (List.replicate (n - tbits.length) false))[i] = Sym.data0 := by
        simp [bitsToSym, List.getElem_replicate]
      rw [hget]
    have hsplit : bitsToSym tbits_ext = bitsToSym tbits ++ bitsToSym (List.replicate (n - tbits.length) false) := by
      dsimp [tbits_ext, bitsToSym]
      rw [List.map_append]
    have htape_pad' : tapeAgrees tape (p_t + ((bitsToSym tbits).length : ℤ)) (bitsToSym (List.replicate (n - tbits.length) false)) := by
      have hlen_bits : (bitsToSym tbits).length = tbits.length := by simp [bitsToSym]
      rw [hlen_bits]
      exact htape_pad
    rw [hsplit]
    exact (tapeAgrees_append tape p_t (bitsToSym tbits) (bitsToSym (List.replicate (n - tbits.length) false))).mpr ⟨htape_bits, htape_pad'⟩
  have hp_t_le_ext : p_t + (tbits_ext.length : ℤ) ≤ p + 1 := by
    rw [htbits_ext_length, hnn]
    omega
  have hregion : p_t + (tbits_ext.length : ℤ) = (p + 1) - 1 := by
    rw [htbits_ext_length, hnn]
    omega
  have hlt_ext : bitsValue tbits_ext < 2 ^ 0 * bitsValue (bitsOf v) := by
    have hval : bitsValue tbits_ext = bitsValue tbits := by
      rw [bitsValue_append]
      have hz : bitsValue (List.replicate (n - tbits.length) false) = 0 := by
        exact (bitsValue_eq_zero_iff_all_false (List.replicate (n - tbits.length) false)).mpr (by
          intro x hx
          exact (List.mem_replicate.mp hx).2)
      rw [hz]
      omega
    rw [hval]
    simpa using hgt_bits
  let r4 : SymTransResult := { nextState := 5, writeSym := Sym.data0, moveDir := Dir.R }
  let step4 : SymStep := { fromState := 4, readSym := Sym.sel, result := r4 }
  let tape1 : ℤ → Sym := fun i => if i = p + 1 then Sym.data0 else tape i
  have hstep4 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) [step4]
      (symStepConfig (SymConfig.mk 4 tape (p + 1)) step4.result) := by
    refine SymSteps.cons [] step4 (SymConfig.mk 4 tape (p + 1)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.sel = tape (p + 1)
      rw [hmark_sel]
    · change step4.result ∈ VerifierSym.transition (4, tape (p + 1))
      rw [hmark_sel]
      decide
  have hcfg4 : symStepConfig (SymConfig.mk 4 tape (p + 1)) step4.result =
      SymConfig.mk 5 tape1 (p + 1 + 1) := by
    simp [symStepConfig, SymConfig.mk, step4, r4, tape1, Dir.toInt]
  have htarget_ext0 : tapeAgrees tape1 p_t (targetTape 0 tbits_ext) := by
    intro i hi
    have hlen : (targetTape 0 tbits_ext).length = tbits_ext.length := by simp only [targetTape_length]
    have hik : i < tbits_ext.length := by simpa only [hlen] using hi
    have hneq : p_t + (i : ℤ) ≠ p + 1 := by omega
    rw [show tape1 (p_t + (i : ℤ)) = tape (p_t + (i : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact htarget_ext i hi
  have hbound0 : tape1 ((p + 1) - 1) = Sym.boundary := by
    rw [show (p + 1) - 1 = p from by omega]
    rw [show tape1 p = tape p from by
      simp only [tape1]
      rw [if_neg (by omega : p ≠ p + 1)]]
    exact hbound
  have hhashL0 : tape1 (p_t - 1) = Sym.boundary := by
    rw [show tape1 (p_t - 1) = tape (p_t - 1) from by
      simp only [tape1]
      rw [if_neg (by omega : p_t - 1 ≠ p + 1)]]
    exact hhashL
  have hsel0 : (tape1 (p + 1)).1 = SymKind.data0 ∨ (tape1 (p + 1)).1 = SymKind.data1 := by
    left
    simp [tape1]
  have helem0 : tapeAgrees tape1 (p + 2) (bitsToSym (bitsOf v)) := by
    intro i hi
    have hneq : p + 2 + (i : ℤ) ≠ p + 1 := by omega
    rw [show tape1 (p + 2 + (i : ℤ)) = tape (p + 2 + (i : ℤ)) from by
      simp only [tape1]
      rw [if_neg hneq]]
    exact hvals_bits i hi
  have hebits_pos_v : 1 ≤ (bitsOf v).length := by
    rw [bitsOf_length]
    exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hv_pos))
  have hj_le0 : 0 ≤ tbits_ext.length := Nat.zero_le _
  rcases subtract_loop_overflow_gen tbits_ext (bitsOf v) 0 p_t (p + 1) tape1 hebits_pos_v hlt_ext hj_le0 hp_t_le_ext hregion htarget_ext0 hbound0 hhashL0 (by
      intro i hi
      rw [htbits_ext_length, hnn] at hi
      omega) hsel0 (by intro i hi; omega) (by simpa [show p + 2 = p + 1 + 1 from by omega] using helem0)
      with ⟨πsub, cfgsub, hπsub, h101⟩
  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) ([step4] ++ πsub) cfgsub := by
    have hstep4' : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) [step4]
        (SymConfig.mk 5 tape1 (p + 1 + 1)) := by
      simpa [hcfg4] using hstep4
    have hπsub' : SymSteps VerifierSym.transition (SymConfig.mk 5 tape1 (p + 1 + 1)) πsub cfgsub := by
      simpa [show p + 1 + 1 + ↑0 = p + 1 + 1 from by omega] using hπsub
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (SymConfig.mk 5 tape1 (p + 1 + 1)) cfgsub [step4] πsub hstep4' hπsub'
  exact ⟨[step4] ++ πsub, cfgsub, htotal, h101⟩

/-- 主循环拒绝路径：选中和超过 target 值时，主循环（状态 4 起）必到 101。 -/
lemma main_loop_reject (elems : List ℕ) (sel : List Bool) (tbits : List Bool)
    (p_t : ℤ) (p : ℤ) (tape : ℤ → Sym)
    (hne : elems ≠ []) (hpos : ∀ v ∈ elems, 0 < v)
    (hsel_len : sel.length = elems.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p)
    (htarget : tapeAgrees tape p_t (targetTape 0 tbits))
    (hbound : tape p = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p → tape i = Sym.data0)
    (helems : tapeAgrees tape (p + 1) (encodeElementsSymWithSel elems sel))
    (hend : (tape (p + 1 + (encodeElementsSymWithSel elems sel).length : ℤ)).1 = SymKind.boundary)
    (hgt : bitsValue tbits < selectedSum elems sel) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) π cfg' ∧ cfg'.state = 101 := by
  induction elems generalizing sel p tape tbits with
  | nil =>
      exfalso
      exact hne rfl
  | cons v rest ih =>
      cases sel with
      | nil =>
          exfalso
          have h := hsel_len
          simp at h
      | cons b sel' =>
          cases rest with
          | nil =>
              have hsel'_nil : sel' = [] := by
                have h : sel'.length = 0 := by
                  have hlen' : sel'.length + 1 = 1 := by
                    simpa [List.length_cons] using hsel_len
                  omega
                exact List.eq_nil_of_length_eq_zero h
              subst sel'
              have hv : v ∈ v :: [] := by simp
              have hv_len : (bitsOf v).length = (Nat.digits 2 v).length := bitsOf_length v
              have henc_len : (encodeBitsSymNative v).length = (bitsOf v).length := by
                simp [encodeBitsSymNative, hv_len]
              have hmark : tape (p + 1) = (if b then Sym.sel else Sym.nosel) := by
                have h := (tapeAgrees_cons tape (p + 1) (if b then Sym.sel else Sym.nosel) (encodeBitsSym v)).mp (by
                  simpa [encodeElementsSymWithSel, joinLists, show encodeBitsSym v = encodeBitsSymNative v from rfl] using helems)
                exact h.1
              have hvals : tapeAgrees tape (p + 2) (encodeBitsSym v) := by
                have h := (tapeAgrees_cons tape (p + 1) (if b then Sym.sel else Sym.nosel) (encodeBitsSym v)).mp (by
                  simpa [encodeElementsSymWithSel, joinLists, show encodeBitsSym v = encodeBitsSymNative v from rfl] using helems)
                simpa [show p + 2 = p + 1 + 1 from by omega] using h.2
              have hvals_bits : tapeAgrees tape (p + 2) (bitsToSym (bitsOf v)) := by
                simpa [encodeBitsSym_eq_bitsToSym_bitsOf] using hvals
              by_cases hb : b
              · -- sel，最后元素：hgt ⟹ v > T → 溢出 → 101
                have hmark_sel : tape (p + 1) = Sym.sel := by simpa [hb] using hmark
                have hgt_v : bitsValue tbits < v := by
                  have hgt_l := hgt
                  simpa [hb, selectedSum] using hgt_l
                rcases subtract_overflow_from_4 v tbits p_t p tape (hpos v hv) hp_t_le htarget hbound hhashL hpad hmark_sel hvals_bits hgt_v
                  with ⟨πo, cfgo, hπo, h101o⟩
                exact ⟨πo, cfgo, hπo, h101o⟩
              · -- nosel，最后元素：hgt ⟹ 0 < 0 矛盾
                exfalso
                have hgt_l := hgt
                simp [hb, selectedSum] at hgt_l
          | cons w rest' =>
              have hv : v ∈ v :: w :: rest' := by simp
              have hv_len : (bitsOf v).length = (Nat.digits 2 v).length := bitsOf_length v
              have henc_len : (encodeBitsSym v).length = (bitsOf v).length := by
                rw [encodeBitsSym_eq_bitsToSym_bitsOf]
                simp [bitsToSym]
              have hsel'_len : sel'.length = (w :: rest').length := by
                have h : (b :: sel').length = (v :: w :: rest').length := hsel_len
                simpa using h
              let mark := if b then Sym.sel else Sym.nosel
              let enc := encodeElementsSymWithSel (w :: rest') sel'
              have hhelems : tapeAgrees tape (p + 1) (mark :: (encodeBitsSym v ++ enc)) := by
                simpa [encodeElementsSymWithSel, joinLists, mark, enc, show encodeBitsSym v = encodeBitsSymNative v from rfl] using helems
              have hmark : tape (p + 1) = mark :=
                (tapeAgrees_cons tape (p + 1) mark (encodeBitsSym v ++ enc)).mp hhelems |>.1
              have htail : tapeAgrees tape (p + 2) (encodeBitsSym v ++ enc) := by
                have h := (tapeAgrees_cons tape (p + 1) mark (encodeBitsSym v ++ enc)).mp hhelems |>.2
                simpa [show p + 2 = p + 1 + 1 from by omega] using h
              have htail_split := (tapeAgrees_append tape (p + 2) (encodeBitsSym v) enc).mp htail
              have hvals : tapeAgrees tape (p + 2) (encodeBitsSym v) := htail_split.1
              have hrest : tapeAgrees tape (p + 2 + ((bitsOf v).length : ℤ)) enc := by
                simpa [henc_len] using htail_split.2
              have hvals_bits : tapeAgrees tape (p + 2) (bitsToSym (bitsOf v)) := by
                simpa [encodeBitsSym_eq_bitsToSym_bitsOf] using hvals
              let p' : ℤ := p + ((bitsOf v).length : ℤ) + 1
              have hsep_sub : tape (p + 2 + ((bitsOf v).length : ℤ)) = Sym.sel ∨ tape (p + 2 + ((bitsOf v).length : ℤ)) = Sym.nosel := by
                have hsel'_cons : ∃ b' sel'', sel' = b' :: sel'' := by
                  cases sel' with
                  | nil => exfalso; have h := hsel'_len; simp at h
                  | cons b' sel'' => exact ⟨b', sel'', rfl⟩
                rcases hsel'_cons with ⟨b', sel'', hsel'_eq⟩
                have hlen_pos : 0 < (encodeElementsSymWithSel (w :: rest') sel').length :=
                  encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len
                subst sel'
                have h0 := hrest 0 (by simpa [enc] using hlen_pos)
                by_cases hb' : b'
                · left
                  simpa [enc, encodeElementsSymWithSel, joinLists, hb', List.getElem_cons_zero] using h0
                · right
                  simpa [enc, encodeElementsSymWithSel, joinLists, hb', List.getElem_cons_zero] using h0
              by_cases hb : b
              · -- sel，非最后元素
                have hmark_sel : tape (p + 1) = Sym.sel := by simpa [hb, mark] using hmark
                by_cases hle_v : v ≤ bitsValue tbits
                · -- 正常：subtract + clear + expand → 递归
                  have hle_bits : bitsValue (bitsOf v) ≤ bitsValue tbits := by simpa [bitsValue_bitsOf] using hle_v
                  have hlen_le_sub : (bitsOf v).length ≤ tbits.length := bitsOf_length_le_of_value_le v tbits (hpos v hv) hle_v
                  have hebits_pos_sub : 1 ≤ (bitsOf v).length := by
                    rw [bitsOf_length]
                    exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt (hpos v hv)))
                  have hp_t_le_sub : p_t + (tbits.length : ℤ) ≤ p + 1 := by omega
                  have hpad_sub : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < (p + 1) - 1 → tape i = Sym.data0 := by
                    intro i hi
                    exact hpad i ⟨hi.1, by omega⟩
                  rcases subtract_element_last_correct tbits (bitsOf v) p_t (p + 1) tape hebits_pos_sub hlen_le_sub hle_bits hp_t_le_sub htarget
                      (by simpa using hbound) hhashL hpad_sub hmark_sel (by simpa [show p + 2 = p + 1 + 1 from by omega] using hvals_bits)
                      (by rcases hsep_sub with hsel_s | hnosel_s
                          · left
                            rw [← show p + 2 + ((bitsOf v).length : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by omega]
                            simpa using hsel_s
                          · right; left
                            rw [← show p + 2 + ((bitsOf v).length : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by omega]
                            simpa using hnosel_s)
                      with ⟨πsub, cfgsub, hπsub, hssub, htasub, hconssub, hpe_sub, hpe0_sub, hhashL_sub, hsep_out, hpad_out, hbound_out, hright_sub⟩
                  rcases clear_counter_correct tbits (bitsOf v) p_t (p + 1) cfgsub.tape hebits_pos_sub hlen_le_sub hp_t_le_sub htasub
                      hbound_out hhashL_sub hpad_out hpe0_sub hconssub
                      with ⟨πcc, cfgcc, hπcc, hscc, hheadcc, htacc, hbound_cc, hhashL_cc, hmark_cc, hcons_cc, hkeep_cc, hgap_cc⟩
                  have hbound_cc0 : cfgcc.tape p = Sym.boundary := by simpa using hbound_cc
                  have hdata_cc : ∀ i : ℕ, i < (bitsOf v).length + 1 → (cfgcc.tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (cfgcc.tape (p + 1 + (i : ℤ))).1 = SymKind.consumed := by
                    intro i hi
                    cases i with
                    | zero => left; simpa using congrArg (fun s : Sym => s.1) hmark_cc
                    | succ j =>
                        right
                        have hj : j < (bitsOf v).length := by simpa [hv_len] using hi
                        have h := hcons_cc j hj
                        simpa [Sym.consumed, hv_len, show p + 1 + (↑j + 1) = p + 1 + 1 + ↑j from by omega] using congrArg (fun s : Sym => s.1) h
                  have hsep_cc : (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.sel ∨
                      (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.nosel := by
                    have hkeep : cfgcc.tape (p + 2 + ((bitsOf v).length : ℤ)) = tape (p + 2 + ((bitsOf v).length : ℤ)) := by
                      rw [hkeep_cc (p + 2 + ((bitsOf v).length : ℤ)) (by omega)]
                      rw [← show p + 1 + 1 + ((bitsOf v).length : ℤ) = p + 2 + ((bitsOf v).length : ℤ) from by omega]
                      exact hsep_out
                    rcases hsep_sub with hsel_s | hnosel_s
                    · left
                      simpa [show p + 1 + (↑(bitsOf v).length + 1) = p + 2 + ↑(bitsOf v).length from by omega] using (by
                        rw [hkeep]
                        exact congrArg (fun s : Sym => s.1) hsel_s)
                    · right
                      simpa [show p + 1 + (↑(bitsOf v).length + 1) = p + 2 + ↑(bitsOf v).length from by omega] using (by
                        rw [hkeep]
                        exact congrArg (fun s : Sym => s.1) hnosel_s)
                  have hend_cc : (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.sel ∨
                      (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.nosel ∨
                      (cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ))).1 = SymKind.boundary := by
                    rcases hsep_cc with hsel_cc | hnosel_cc
                    · left
                      exact hsel_cc
                    · right; left
                      exact hnosel_cc
                  rcases expand_place_correct_ext ((bitsOf v).length + 1) p cfgcc.tape (by omega) hbound_cc0 hdata_cc hend_cc with
                    ⟨πe, cfge, hπe, he0, he_disj, hleft_e, hright_e, hsep_imp_e, hboundary_imp_e⟩
                  let tbits' : List Bool := subAllBits tbits (bitsOf v)
                  have hgt' : bitsValue tbits' < selectedSum (w :: rest') sel' := by
                    dsimp [tbits']
                    have hsv : bitsValue (subAllBits tbits (bitsOf v)) = bitsValue tbits - v := by
                      rw [subAllBits_value]
                      · rw [bitsValue_bitsOf]
                      · simpa [bitsValue_bitsOf] using hle_bits
                    rw [hsv]
                    have hsum : selectedSum (v :: w :: rest') (b :: sel') = v + selectedSum (w :: rest') sel' := by
                      simpa [hb] using (selectedSum_cons v (w :: rest') b sel')
                    have hgt_l : bitsValue tbits < selectedSum (v :: w :: rest') (b :: sel') := hgt
                    have : bitsValue tbits < v + selectedSum (w :: rest') sel' := by simpa [hsum] using hgt_l
                    omega
                  have hp_t_le' : p_t + (tbits'.length : ℤ) ≤ p' := by
                    dsimp [p', tbits']
                    rw [subAllBits_length]
                    omega
                  have hbound' : cfge.tape p' = Sym.boundary := by
                    rcases he_disj with h4 | h22
                    · have hb : cfge.tape (p + (((bitsOf v).length + 1 : ℕ) : ℤ)) = Sym.boundary := h4.2.1
                      convert hb using 1
                      dsimp [p']
                      ring
                    · exfalso
                      have hs4 : cfge.state = 4 := hsep_imp_e hsep_cc
                      have hcontra : (22 : ℕ) = 4 := h22.1.symm.trans hs4
                      cases hcontra
                  have hhashL' : cfge.tape (p_t - 1) = Sym.boundary := by
                    rw [hleft_e (p_t - 1) (by omega)]
                    exact hhashL_cc
                  have htlen_eq : tbits'.length = tbits.length := by
                    dsimp [tbits']
                    rw [subAllBits_length]
                  have hpad' : ∀ i : ℤ, p_t + (tbits'.length : ℤ) ≤ i ∧ i < p' → cfge.tape i = Sym.data0 := by
                    intro i hi
                    by_cases hlt_p : i < p
                    · rw [hleft_e i hlt_p]
                      have hkeep : cfgcc.tape i = cfgsub.tape i := hgap_cc i (by constructor <;> omega)
                      rw [hkeep]
                      exact hpad_out i (by constructor <;> omega)
                    · by_cases heq_p : i = p
                      · subst i
                        exact he0
                      · have : ∃ j : ℕ, j < (bitsOf v).length ∧ i = p + 1 + (j : ℤ) := by
                          have hgt : p < i := by omega
                          let j : ℕ := (i - (p + 1)).toNat
                          refine ⟨j, ?_, ?_⟩
                          · have hj : (j : ℤ) = i - (p + 1) := by
                              dsimp [j]
                              exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                            dsimp [p'] at hi
                            omega
                          · have hj : (j : ℤ) = i - (p + 1) := by
                              dsimp [j]
                              exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                            rw [hj]
                            omega
                        rcases this with ⟨j, hj, hjpos⟩
                        rw [hjpos]
                        have he_data4 : ∀ j : ℕ, j < (bitsOf v).length → cfge.tape (p + 1 + (j : ℤ)) = Sym.data0 := by
                          rcases he_disj with h4 | h22
                          · intro j hj
                            exact h4.2.2.2.2 j (by omega)
                          · exfalso
                            have hs4 : cfge.state = 4 := hsep_imp_e hsep_cc
                            have hcontra : (22 : ℕ) = 4 := h22.1.symm.trans hs4
                            cases hcontra
                        exact he_data4 j (by omega)
                  have helems' : tapeAgrees cfge.tape (p' + 1) enc := by
                    intro i hi
                    by_cases h0 : i = 0
                    · subst i
                      have hkeep0 : cfge.tape (p' + 1) = tape (p' + 1) := by
                        rcases he_disj with h4 | h22
                        · have hmark' : cfge.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) = cfgcc.tape (p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ)) := by
                            rw [h4.2.2.2.1]
                          dsimp [p']
                          rw [show p + ((bitsOf v).length : ℤ) + 1 + 1 = p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ) from by simp only [Int.natCast_add]; omega]
                          rw [hmark']
                          rw [show p + 1 + (((bitsOf v).length + 1 : ℕ) : ℤ) = p + 1 + 1 + ((bitsOf v).length : ℤ) from by simp only [Int.natCast_add]; omega]
                          rw [hkeep_cc (p + 1 + 1 + ((bitsOf v).length : ℤ)) (by omega)]
                          rw [← hsep_out]
                        · exfalso
                          have hs4 : cfge.state = 4 := hsep_imp_e hsep_cc
                          have hcontra : (22 : ℕ) = 4 := h22.1.symm.trans hs4
                          cases hcontra
                      norm_num
                      rw [hkeep0]
                      rw [show p' + 1 = p + 2 + ((bitsOf v).length : ℤ) from by dsimp [p']; omega]
                      simpa using hrest 0 (encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len)
                    · have hkeep : cfge.tape (p' + 1 + (i : ℤ)) = tape (p' + 1 + (i : ℤ)) := by
                        rw [hright_e (p' + 1 + (i : ℤ)) (by dsimp [p']; (have hi_pos : 0 < (i : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)); omega)]
                        rw [hkeep_cc (p' + 1 + (i : ℤ)) (by omega)]
                        exact hright_sub (p' + 1 + (i : ℤ)) (by omega)
                      rw [hkeep]
                      rw [show p' + 1 + (i : ℤ) = p + 2 + ((bitsOf v).length : ℤ) + (i : ℤ) from by dsimp [p']; omega]
                      exact hrest i hi
                  have henc_pos : 0 < enc.length :=
                    encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len
                  have hend' : (cfge.tape (p' + 1 + (enc.length : ℤ))).1 = SymKind.boundary := by
                    have hpos : p + 1 + (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = p' + 1 + (enc.length : ℤ) := by
                      have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = (1 + (bitsOf v).length) + enc.length := by
                        calc
                          (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                              = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                                simp [encodeElementsSymWithSel, joinLists, enc]
                                rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                  simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                                ac_rfl
                          _ = (1 + (bitsOf v).length) + enc.length := by
                                rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                  simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                                try
                                  change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                    (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length
                                  rfl
                      rw [hlen_full]
                      dsimp [p']
                      repeat rw [Int.natCast_add]
                      omega
                    have hkeep : cfge.tape (p' + 1 + (enc.length : ℤ)) = tape (p' + 1 + (enc.length : ℤ)) := by
                      rw [hright_e (p' + 1 + (enc.length : ℤ)) (by dsimp [p']; (have henc_pos' : 0 < (enc.length : ℤ) := by exact_mod_cast henc_pos); omega)]
                      rw [hkeep_cc (p' + 1 + (enc.length : ℤ)) (by omega)]
                      exact hright_sub (p' + 1 + (enc.length : ℤ)) (by omega)
                    rw [hkeep, ← hpos]
                    exact hend
                  have htarget' : tapeAgrees cfge.tape p_t (targetTape 0 tbits') := by
                    intro i hi
                    have hlen : (targetTape 0 tbits').length = tbits'.length := by
                      simp only [targetTape_length]
                    have hik : i < tbits'.length := by simpa only [hlen] using hi
                    have hi_lt : p_t + (i : ℤ) < p := by omega
                    rw [hleft_e (p_t + (i : ℤ)) hi_lt]
                    simpa [tbits'] using htacc i hi
                  have hpos' : ∀ v' ∈ w :: rest', 0 < v' := by
                    intro v' hv'
                    exact hpos v' (by simp [hv'])
                  rcases ih sel' tbits' p' cfge.tape (by simp) hpos' hsel'_len hp_t_le' htarget' hbound' hhashL' hpad' helems' hend' hgt'
                      with ⟨πrec, cfgrec, hπrec, h101rec⟩
                  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc ++ πe ++ πrec) cfgrec := by
                    have hsub : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) πsub cfgsub := by simpa using hπsub
                    have hcc : SymSteps VerifierSym.transition cfgsub πcc cfgcc := by
                      have hcfg : cfgsub = SymConfig.mk 84 cfgsub.tape (p + 1 + ((bitsOf v).length : ℤ)) := by
                        cases cfgsub with
                        | mk s t hp =>
                            dsimp
                            rw [show s = 84 from hssub]
                            rw [show hp = p + 1 + ((bitsOf v).length : ℤ) from hpe_sub]
                      rw [hcfg]
                      exact hπcc
                    have he : SymSteps VerifierSym.transition cfgcc πe cfge := by
                      have hcfg : cfgcc = SymConfig.mk 20 cfgcc.tape p := by
                        cases cfgcc with
                        | mk s t hp =>
                            dsimp
                            rw [show s = 20 from hscc]
                            rw [show hp = p from by simpa using hheadcc]
                      rw [hcfg]
                      exact hπe
                    have hrec : SymSteps VerifierSym.transition cfge πrec cfgrec := by
                      have hcfg : cfge = SymConfig.mk 4 cfge.tape (p' + 1) := by
                        cases cfge with
                        | mk s t hp =>
                            dsimp
                            have hs4 : s = 4 := by
                              simpa using hsep_imp_e hsep_cc
                            rw [hs4]
                            have hhead : hp = p' + 1 := by
                              rcases he_disj with h4 | h22
                              · simpa [show p + (↑(bitsOf v).length + 1) + 1 = p' + 1 from by dsimp [p']; omega] using h4.2.2.1
                              · exfalso
                                have hcontra : (4 : ℕ) = 22 := (hsep_imp_e hsep_cc).symm.trans h22.1
                                cases hcontra
                            rw [hhead]
                      rw [hcfg]
                      exact hπrec
                    have h1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc) cfgcc :=
                      SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgsub cfgcc πsub πcc hsub hcc
                    have h2 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πsub ++ πcc ++ πe) cfge :=
                      SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgcc cfge (πsub ++ πcc) πe h1 he
                    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfge cfgrec (πsub ++ πcc ++ πe) πrec h2 hrec
                  exact ⟨πsub ++ πcc ++ πe ++ πrec, cfgrec, htotal, h101rec⟩
                · -- 溢出：v > T → 101
                  have hgt_v : bitsValue tbits < v := by omega
                  rcases subtract_overflow_from_4 v tbits p_t p tape (hpos v hv) hp_t_le htarget hbound hhashL hpad hmark_sel hvals_bits hgt_v
                    with ⟨πo, cfgo, hπo, h101o⟩
                  exact ⟨πo, cfgo, hπo, h101o⟩
              · -- nosel，非最后元素
                have hmark_nosel : tape (p + 1) = Sym.nosel := by simpa [hb, mark] using hmark
                rcases clear_element_correct (bitsOf v) (p + 1) tape hmark_nosel (by simpa [show (p + 1) - 1 = p from by omega] using hbound) (by simpa [show p + 2 = p + 1 + 1 from by omega] using hvals_bits) (by
                    rcases hsep_sub with hsel_s | hnosel_s
                    · left
                      simpa [← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using hsel_s
                    · right; left
                      simpa [← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using hnosel_s)
                    with ⟨πcl, cfgcl, hπcl, hscl, hheadcl, hbnd22_cl, hsel51_cl, htacl, hbound_cl, hpem1_cl, hmark_cl, hleft_cl, hkeep_sep_cl, hright_cl⟩
                have hcl51 : cfgcl.state = 51 ∧ cfgcl.headPos = p + 1 + ↑(bitsOf v).length := by
                  have hsel51' : (tape (p + 1 + 1 + ↑(bitsOf v).length)).1 = SymKind.sel ∨
                      (tape (p + 1 + 1 + ↑(bitsOf v).length)).1 = SymKind.nosel := by
                    rcases hsep_sub with hsel_s | hnosel_s
                    · left
                      simpa [Sym.sel, Sym.nosel, ← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using congrArg (fun s : Sym => s.1) hsel_s
                    · right
                      simpa [Sym.sel, Sym.nosel, ← hv_len, show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega] using congrArg (fun s : Sym => s.1) hnosel_s
                  have h := hsel51_cl hsel51'
                  exact ⟨h.1, by simpa [show p + 1 + 1 + ↑(bitsOf v).length = p + 1 + ↑(bitsOf v).length + 1 from by omega] using h.2⟩
                have hebits_pos : 1 ≤ (bitsOf v).length := by
                  rw [bitsOf_length]
                  exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt (hpos v hv)))
                have hdata51 : cfgcl.tape (p + 1 + ↑(bitsOf v).length) = Sym.data0 := by
                  have hlt : (bitsOf v).length - 1 < (bitsOf v).length := by omega
                  have h := htacl ((bitsOf v).length - 1) (by simpa using hlt)
                  simpa [show p + 1 + 1 + ↑((bitsOf v).length - 1) = p + 1 + ↑(bitsOf v).length from by omega] using h
                let r51 : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
                let step51 : SymStep := { fromState := 51, readSym := Sym.data0, result := r51 }
                let cfg51 : SymConfig := symStepConfig cfgcl step51.result
                have hstep51 : SymSteps VerifierSym.transition cfgcl [step51] cfg51 := by
                  refine SymSteps.cons [] step51 cfgcl SymSteps.nil ?_ ?_ ?_
                  · rw [hcl51.1]
                  · change Sym.data0 = cfgcl.tape cfgcl.headPos
                    rw [hcl51.2]
                    exact hdata51.symm
                  · rw [hcl51.1, hcl51.2, hdata51]
                    decide
                have hgt' : bitsValue tbits < selectedSum (w :: rest') sel' := by
                  have hsum : selectedSum (v :: w :: rest') (b :: sel') = selectedSum (w :: rest') sel' := by
                    simpa [hb] using (selectedSum_cons v (w :: rest') b sel')
                  have hgt_l : bitsValue tbits < selectedSum (v :: w :: rest') (b :: sel') := hgt
                  simpa [hsum] using hgt_l
                have hp_t_le' : p_t + (tbits.length : ℤ) ≤ p' := by dsimp [p']; omega
                have htarget' : tapeAgrees cfg51.tape p_t (targetTape 0 tbits) := by
                  intro i hi
                  have hlen : (targetTape 0 tbits).length = tbits.length := by simp only [targetTape_length]
                  have hik : i < tbits.length := by simpa only [hlen] using hi
                  have htape51 : cfg51.tape (p_t + (i : ℤ)) = cfgcl.tape (p_t + (i : ℤ)) := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : p_t + (i : ℤ) = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  rw [hleft_cl (p_t + (i : ℤ)) (by omega)]
                  exact htarget i (by simpa only [hlen] using hik)
                have hbound' : cfg51.tape p' = Sym.boundary := by
                  dsimp [cfg51, symStepConfig, step51, r51, p']
                  rw [hcl51.2]
                  rw [if_pos (by omega : p + ↑(bitsOf v).length + 1 = p + 1 + ↑(bitsOf v).length)]
                have hhashL' : cfg51.tape (p_t - 1) = Sym.boundary := by
                  dsimp [cfg51, symStepConfig, step51, r51, p']
                  rw [hcl51.2]
                  by_cases heq : p_t - 1 = p + 1 + ↑(bitsOf v).length
                  · exfalso
                    omega
                  · rw [if_neg heq]
                    rw [hleft_cl (p_t - 1) (by omega)]
                    exact hhashL
                have hpad' : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p' → cfg51.tape i = Sym.data0 := by
                  intro i hi
                  have htape51 : cfg51.tape i = cfgcl.tape i := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : i = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  by_cases hlt_p : i < p
                  · rw [hleft_cl i (by omega)]
                    exact hpad i ⟨hi.1, hlt_p⟩
                  · by_cases heq_p : i = p
                    · subst i
                      simpa [show (p + 1) - 1 = p from by omega] using hpem1_cl
                    · have : ∃ j : ℕ, j < (bitsOf v).length ∧ i = p + 1 + (j : ℤ) := by
                        have hgt : p < i := by omega
                        let j : ℕ := (i - (p + 1)).toNat
                        refine ⟨j, ?_, ?_⟩
                        · have hj : (j : ℤ) = i - (p + 1) := by
                            dsimp [j]
                            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                          dsimp [p'] at hi
                          omega
                        · have hj : (j : ℤ) = i - (p + 1) := by
                            dsimp [j]
                            exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                          rw [hj]
                          omega
                      rcases this with ⟨j, hj, hjpos⟩
                      rw [hjpos]
                      by_cases hj0 : j = 0
                      · subst j
                        norm_num
                        exact hmark_cl
                      · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
                        let j' : ℕ := j - 1
                        have hj'_lt : j' < (bitsOf v).length := by
                          dsimp [j']
                          omega
                        have h := htacl j' (by simpa using hj'_lt)
                        simpa [show p + 1 + 1 + ↑j' = p + 1 + ↑j from by dsimp [j']; omega] using h
                have henc_pos : 0 < enc.length :=
                  encodeElementsSymWithSel_length_pos (w :: rest') sel' (by simp) hsel'_len
                have helems' : tapeAgrees cfg51.tape (p' + 1) enc := by
                  intro i hi
                  have htape51 : cfg51.tape (p' + 1 + (i : ℤ)) = cfgcl.tape (p' + 1 + (i : ℤ)) := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : p' + 1 + (i : ℤ) = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                  rw [htape51]
                  by_cases hi0 : i = 0
                  · subst i
                    norm_num
                    rw [show p' + 1 = p + 2 + ↑(bitsOf v).length from by dsimp [p']; omega]
                    rw [show p + 2 + ↑(bitsOf v).length = p + 1 + 1 + ↑(bitsOf v).length from by omega]
                    rw [hkeep_sep_cl]
                    simpa [show p + 1 + 1 + ↑(bitsOf v).length = p + 2 + ↑(bitsOf v).length from by omega] using hrest 0 (by simpa [enc] using henc_pos)
                  · have hi_gt : 0 < i := Nat.pos_of_ne_zero hi0
                    rw [hright_cl (p' + 1 + (i : ℤ)) (by omega)]
                    simpa [show p' + 1 + (i : ℤ) = p + 2 + ↑(bitsOf v).length + (i : ℤ) from by dsimp [p']; omega] using hrest i hi
                have hend' : (cfg51.tape (p' + 1 + (enc.length : ℤ))).1 = SymKind.boundary := by
                  have hkeep : cfg51.tape (p' + 1 + (enc.length : ℤ)) = tape (p' + 1 + (enc.length : ℤ)) := by
                    dsimp [cfg51, symStepConfig, step51, r51, p']
                    rw [hcl51.2]
                    by_cases heq : p' + 1 + (enc.length : ℤ) = p + 1 + ↑(bitsOf v).length
                    · exfalso
                      omega
                    · rw [if_neg heq]
                      rw [hright_cl (p' + 1 + (enc.length : ℤ)) (by dsimp [p']; (have henc_pos' : 0 < (enc.length : ℤ) := by exact_mod_cast henc_pos); omega)]
                  rw [hkeep]
                  have hpos : p + 1 + (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = p' + 1 + (enc.length : ℤ) := by
                    have hlen_full : (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length = (1 + (bitsOf v).length) + enc.length := by
                      calc
                        (encodeElementsSymWithSel (v :: w :: rest') (b :: sel')).length
                            = (1 + (encodeBitsSymNative v).length) + (encodeElementsSymWithSel (w :: rest') sel').length := by
                              simp [encodeElementsSymWithSel, joinLists, enc]
                              rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                              ac_rfl
                        _ = (1 + (bitsOf v).length) + enc.length := by
                              rw [show (encodeBitsSymNative v).length = (bitsOf v).length from by
                                simpa [show encodeBitsSym v = encodeBitsSymNative v from rfl] using henc_len]
                              try
                                change (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length =
                                  (1 + (bitsOf v).length) + (encodeElementsSymWithSel (w :: rest') sel').length
                                rfl
                    rw [hlen_full]
                    dsimp [p']
                    repeat rw [Int.natCast_add]
                    omega
                  rw [← hpos]
                  exact hend
                have hpos' : ∀ v' ∈ w :: rest', 0 < v' := by
                  intro v' hv'
                  exact hpos v' (by simp [hv'])
                rcases ih sel' tbits p' cfg51.tape (by simp) hpos' hsel'_len hp_t_le' htarget' hbound' hhashL' hpad' helems' hend' hgt'
                    with ⟨πrec, cfgrec, hπrec, h101rec⟩
                have htotal : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πcl ++ [step51] ++ πrec) cfgrec := by
                  have hcl : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) πcl cfgcl := by simpa using hπcl
                  have hrec : SymSteps VerifierSym.transition cfg51 πrec cfgrec := by
                    have hcfg : cfg51 = SymConfig.mk 4 cfg51.tape (p' + 1) := by
                      cases cfgcl with
                      | mk s t hp =>
                          have hhp : hp = p + 1 + ↑(bitsOf v).length := by
                            simpa using hcl51.2
                          dsimp [cfg51, symStepConfig, step51, r51, SymConfig.mk, Dir.toInt]
                          rw [hhp]
                          simp [p', show p + 1 + ↑(bitsOf v).length + 1 = p' + 1 from by dsimp [p']; omega]
                    rw [hcfg]
                    exact hπrec
                  have h1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) (πcl ++ [step51]) cfg51 :=
                    SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfgcl cfg51 πcl [step51] hcl hstep51
                  exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) cfg51 cfgrec (πcl ++ [step51]) πrec h1 hrec
                exact ⟨πcl ++ [step51] ++ πrec, cfgrec, htotal, h101rec⟩

/-- 转移读已标记 boundary（m=1）时必写回自身（#₁ 保持）；状态 20 读 #₀（m=0）排除。 -/
lemma hash1_writes_self (q : ℕ) (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (q, s)) (hs : s.1 = SymKind.boundary)
    (hs2 : s.2 = true) (hq20 : q ≠ 20) :
    r.writeSym = s := by
  by_cases hqin : q ∈ VerifierSym.legalStates
  · have hdec : ∀ q ∈ VerifierSym.legalStates, ∀ s : Sym, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (q, s) → s.1 = SymKind.boundary → s.2 = true →
          q ≠ 20 → r.writeSym = s := by
      native_decide
    exact hdec q hqin s r hr hs hs2 hq20
  · have htr : VerifierSym.transition (q, s) = {SymTransResult.mk 101 s Dir.S} := by
      unfold VerifierSym.transition
      dsimp
      rw [if_neg hqin]
    have hr' : r = SymTransResult.mk 101 s Dir.S := by
      simpa [htr] using hr
    subst r
    rfl

/-- 主循环（状态 4 起）保持 #₁（已标记 boundary）格的值：位置 i 上初始为 (boundary, true) 时，
    路径上除状态 20 读未标记符号的步外，i 处保持 (boundary, true)。 -/
lemma main_loop_keeps_hash1 (elems : List ℕ) (sel : List Bool) (p : ℤ) (tape : ℤ → Sym)
    {π cfg} (h : SymSteps VerifierSym.transition (SymConfig.mk 4 tape (p + 1)) π cfg)
    (hinit : tape (p + 1 + (encodeElementsSymWithSel elems sel).length : ℤ) =
      Sym.mk SymKind.boundary true)
    (hno20 : ∀ step ∈ π, step.fromState ≠ 20 ∨ step.readSym.2 = false) :
    cfg.tape (p + 1 + (encodeElementsSymWithSel elems sel).length : ℤ) =
      tape (p + 1 + (encodeElementsSymWithSel elems sel).length : ℤ) := by
  let i : ℤ := p + 1 + (encodeElementsSymWithSel elems sel).length
  have hkeep : cfg.tape i = Sym.mk SymKind.boundary true := by
    induction h with
    | nil => exact hinit
    | cons π₀ step cfg₁ h_ind h_from h_read h_trans ih =>
        by_cases hi : i = cfg₁.headPos
        · -- 当前步写在 i（#₁ 位置）：写回自身
          have hs : cfg₁.tape cfg₁.headPos = Sym.mk SymKind.boundary true := by
            rw [← hi]
            exact ih (by intro step hmem; exact hno20 step (by simp [hmem]))
          by_cases hq20 : cfg₁.state = 20
          · -- 20 读已标记符号：与 hno20 矛盾
            have hread_marked : step.readSym.2 = true := by
              rw [h_read]
              rw [hs]
              rfl
            have hno := hno20 step (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
            rcases hno with hneq | hreadf
            · exfalso
              exact hneq (by rw [h_from]; exact hq20)
            · exfalso
              simp [hread_marked] at hreadf
          · -- 非 20：写回自身
            have hw : step.result.writeSym = cfg₁.tape cfg₁.headPos := by
              exact hash1_writes_self cfg₁.state (cfg₁.tape cfg₁.headPos) step.result
                (by simpa [h_read] using h_trans) (by simpa [hs]) (by simpa [hs])
                (by intro hq; exact hq20 hq)
            change (symStepConfig cfg₁ step.result).tape i = Sym.mk SymKind.boundary true
            dsimp [symStepConfig]
            rw [if_pos hi]
            rw [hw, ← hi]
            exact ih (by intro step hmem; exact hno20 step (by simp [hmem]))
        · -- 当前步不写 i
          change (symStepConfig cfg₁ step.result).tape i = Sym.mk SymKind.boundary true
          dsimp [symStepConfig]
          rw [if_neg hi]
          exact ih (by intro step hmem; exact hno20 step (by simp [hmem]))
  exact hkeep.trans hinit.symm

/-- 状态 2 带选择的右扫（scan2_from_2）：从 headPos = 2+k 出发扫元素区，α/β 按 sel₀ 写
    sel/nosel 右移，native 位写回原符号右移，扫到 #₁ 后停状态 3（S 不动）。
    最终带：左区（< 2+k）不变，元素区 = encodeElementsSymWithSel inst.elements sel₀。 -/
lemma scan2_from_2 (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    (sel₀ : List Bool) (hsel₀_len : sel₀.length = inst.elements.length)
    (tape : ℤ → Sym)
    (hta : tapeAgrees tape (2 + (encodeBitsSym inst.target).length) (encodeElementsSym inst.elements))
    (hbnd : tape ((2 + (encodeBitsSym inst.target).length) + ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 2 tape (2 + (encodeBitsSym inst.target).length)) π cfg' ∧
      cfg'.state = 3 ∧
      cfg'.headPos = (2 + (encodeBitsSym inst.target).length) + ((encodeElementsSym inst.elements).length : ℤ) ∧
      cfg'.tape ((2 + (encodeBitsSym inst.target).length) + ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary ∧
      (∀ i : ℤ, i < 2 + (encodeBitsSym inst.target).length → cfg'.tape i = tape i) ∧
      ∃ sel : List Bool, sel.length = inst.elements.length ∧
        tapeAgrees cfg'.tape (2 + (encodeBitsSym inst.target).length) (encodeElementsSymWithSel inst.elements sel) ∧
        sel = sel₀ := by
  let p : ℤ := (2 + (encodeBitsSym inst.target).length : ℤ)
  rcases scanRight2_chosen inst.elements sel₀ p tape hsel₀_len hta hbnd with
    ⟨π, cfg', hπ, hs3, hhead, hsel, hnonb, hleft, hbnd'⟩
  refine ⟨π, cfg', hπ, hs3, hhead, hbnd', hleft, ?_⟩
  refine ⟨sel₀, hsel₀_len, hsel, rfl⟩

theorem symVerifier_correct (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target) :
    symAccepts VerifierSym.verifierSymTransition VerifierSym.acceptStates (encodeInstanceSym inst) ↔
      subsetSumHolds inst := by
  constructor
  · -- 可靠性：接受 → 子集和
    intro h
    rcases h with ⟨π, cfg, hpath, hacc⟩
    have hπ : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg :=
      reachablePath_to_steps hpath
    have hs100 : cfg.state = 100 := by
      simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hacc
    have hstart : (symInitialConfig (encodeInstanceSym inst)).tape 0 = Sym.boundary := by
      have hta := symInitialConfig_tapeAgrees (encodeInstanceSym inst)
      have h0 : 0 < (encodeInstanceSym inst).length := by
        dsimp [encodeInstanceSym]
        simp
      have hcell : (encodeInstanceSym inst)[0] = Sym.boundary := by
        dsimp [encodeInstanceSym]
      simpa [hcell] using (hta 0 h0)
    rcases backchain_to_first4 hπ (by rw [hs100]; decide) with
      ⟨π₁, π₂, cfg₄, hsplit, hπ₁, hs4, hno4₁, hrest⟩
    rcases split_at_state4 π₁ cfg₄ hstart hπ₁ hs4 with
      ⟨π₀₃, step₃, cfg₃, π₂', hsplit₃, hπ₀₃, h28h51, hcfg₄, hrest₃⟩
    rcases branch_phase_inv inst π₁ cfg₄ hπ₁ hno4₁ hs4 with
      ⟨sel, hsel_len, hhead₄, htarget₄, hb0₄, hb1₄, helems₄, hend₄⟩
    let k : ℕ := (encodeBitsSym inst.target).length
    let tbits : List Bool := bitsOf inst.target
    have htlen : tbits.length = k := by
      dsimp [tbits, k, bitsOf, symToBits, encodeBitsSym, encodeBitsSymNative]
      rw [List.length_map]
    have htarget' : tapeAgrees cfg₄.tape 1 (targetTape 0 tbits) := by
      dsimp [tbits]
      rw [targetTape_zero]
      rw [show bitsToSym (bitsOf inst.target) = encodeBitsSym inst.target from (encodeBitsSym_eq_bitsToSym_bitsOf inst.target).symm]
      exact htarget₄
    have hbound' : cfg₄.tape (1 + (k : ℤ)) = Sym.boundary := by
      simpa [k] using hb1₄
    have hhashL' : cfg₄.tape (1 - 1) = Sym.boundary := by
      simpa using hb0₄
    have hpad' : ∀ i : ℤ, 1 + (k : ℤ) ≤ i ∧ i < 1 + (k : ℤ) → cfg₄.tape i = Sym.data0 := by
      intro i hi
      omega
    have helems' : tapeAgrees cfg₄.tape ((1 + (k : ℤ)) + 1) (encodeElementsSymWithSel inst.elements sel) := by
      have hpos' : (1 + (k : ℤ)) + 1 = 2 + (k : ℤ) := by omega
      simpa [k, hpos'] using helems₄
    have hend' : (cfg₄.tape ((1 + (k : ℤ)) + 1 + (encodeElementsSymWithSel inst.elements sel).length : ℤ)).1 = SymKind.boundary := by
      have hpos' : (1 + (k : ℤ)) + 1 = 2 + (k : ℤ) := by omega
      simpa [k, hpos'] using (congrArg (fun x : Sym => x.1) hend₄)
    have hcfg₄' : cfg₄ = SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1) := by
      cases cfg₄ with
      | mk s t hp =>
          dsimp
          rw [show s = 4 from hs4]
          rw [show hp = (1 + (k : ℤ)) + 1 from by
            dsimp [k] at hhead₄ ⊢
            omega]
    have hrest' : SymSteps VerifierSym.transition (SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1)) π₂ cfg := by
      rw [hcfg₄'] at hrest
      exact hrest
    let Pd : ℕ → Prop := fun q => q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ)
    have hdet_d : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r r' : SymTransResult⦄,
        Pd q → r ∈ VerifierSym.transition (q, s) → r' ∈ VerifierSym.transition (q, s) → r = r' := by
      intro q s r r' hq hr hr'
      have hdec : ∀ q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ), ∀ s : Sym, ∀ r ∈ VerifierSym.transition (q, s), ∀ r' ∈ VerifierSym.transition (q, s), r = r' := by
        native_decide
      dsimp [Pd] at hq
      exact hdec q hq s r hr r' hr'
    have hclose_d : ∀ ⦃q : ℕ⦄ ⦃s : Sym⦄ ⦃r : SymTransResult⦄,
        Pd q → r ∈ VerifierSym.transition (q, s) → Pd r.nextState := by
      intro q s r hq hr
      have hdec : ∀ q ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ), ∀ s : Sym, ∀ r ∈ VerifierSym.transition (q, s),
          r.nextState ∈ ({4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 76, 77, 81, 84, 85, 86, 87, 38, 51, 28, 100, 101} : Finset ℕ) := by
        native_decide
      dsimp [Pd] at hq
      exact hdec q hq s r hr
    have hP₀_d : Pd 4 := by
      dsimp [Pd]
      native_decide
    by_cases hle_total : selectedSum inst.elements sel ≤ bitsValue tbits
    · -- 借位不越界：主循环确定性走到 22
      rcases main_loop_correct inst.elements sel tbits 1 (1 + (k : ℤ)) cfg₄.tape
          (by exact hne) (by exact hpos) hsel_len (by omega : 1 + (tbits.length : ℤ) ≤ 1 + (k : ℤ))
          htarget' hbound' hhashL' (by intro i hi; exact hpad' i (by rw [htlen] at hi; exact hi)) helems' hend' hle_total with
        ⟨πl, cfgl, hπl, hs22, htarg, hheadl, hclear, hhashLf, hgapf, hrightl⟩
      have hpfx := SymSteps_prefix_unique_det (M := VerifierSym.transition) Pd
        (SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1)) hdet_d hclose_d hP₀_d hrest' hπl
      rcases hpfx with hrev | hfwd
      · exfalso
        rcases hrev with ⟨ρ, _, hρ⟩
        have hcfg100 : cfg = SymConfig.mk 100 cfg.tape cfg.headPos := by
          cases cfg with
          | mk s t p => dsimp; rw [show s = 100 from hs100]
        rw [hcfg100] at hρ
        have hfrom100 : cfgl.state = 100 :=
          steps_from_100 cfg.tape cfg.headPos (π := ρ) (cfg := cfgl) hρ
        rw [hfrom100] at hs22
        omega
      · rcases hfwd with ⟨ρ, _, hρ⟩
        have hcfg22 : cfgl = SymConfig.mk 22 cfgl.tape cfgl.headPos := by
          cases cfgl with
          | mk s t p => dsimp; rw [show s = 22 from hs22]
        rw [hcfg22] at hρ
        have hbound22 : cfgl.tape cfgl.headPos = Sym.mk SymKind.boundary true :=
          first_read_of_22_to_100 cfgl.tape cfgl.headPos hρ hs100
        rcases SymSteps_first_step hρ (by
          intro hρ0
          subst ρ
          have hcfg22' : cfg = SymConfig.mk 22 cfgl.tape cfgl.headPos := SymSteps_nil_eq hρ
          rw [hcfg22'] at hs100
          norm_num at hs100) with ⟨stepc, ρc, hρeq, hfromc, hreadc, htransc, htailc⟩
        have hreadbc : stepc.readSym = Sym.mk SymKind.boundary true := by
          rw [hreadc]
          exact hbound22
        have h23next : stepc.result.nextState = 23 := by
          have hdec : ∀ r ∈ VerifierSym.transition (22, Sym.mk SymKind.boundary true), r.nextState = 23 := by
            decide
          exact hdec stepc.result (by simpa [hbound22] using htransc)
        have hcfg23 : symStepConfig cfgl stepc.result = SymConfig.mk 23 cfgl.tape (cfgl.headPos - 1) := by
          have hdec : ∀ r : SymTransResult, r ∈ VerifierSym.transition (22, Sym.mk SymKind.boundary true) →
              r = SymTransResult.mk 23 (Sym.mk SymKind.boundary true) Dir.L := by
            intro r hr
            have hnext : r.nextState = 23 := by
              have hd : ∀ r ∈ VerifierSym.transition (22, Sym.mk SymKind.boundary true), r.nextState = 23 := by
                decide
              exact hd r hr
            have hwrite : r.writeSym = Sym.mk SymKind.boundary true := by
              have hd : ∀ r ∈ VerifierSym.transition (22, Sym.mk SymKind.boundary true), r.writeSym = Sym.mk SymKind.boundary true := by
                decide
              exact hd r hr
            have hmove : r.moveDir = Dir.L := by
              have hd : ∀ r ∈ VerifierSym.transition (22, Sym.mk SymKind.boundary true), r.moveDir = Dir.L := by
                decide
              exact hd r hr
            rcases r with ⟨ns, ws, md⟩
            have hns : ns = 23 := hnext
            have hws : ws = Sym.mk SymKind.boundary true := hwrite
            have hmd : md = Dir.L := hmove
            subst ns
            subst ws
            subst md
            rfl
          have hres := hdec stepc.result (by simpa [hbound22] using htransc)
          dsimp [symStepConfig]
          rw [hres]
          simp [SymConfig.mk, Dir.toInt]
          constructor
          · funext x
            by_cases hx : x = cfgl.headPos <;> simp [hx, hbound22]
          · rfl
        have hscan := scan23_stop_boundary (cfgl.headPos - 1) cfgl.tape (by
          rw [← hcfg22] at htailc
          rw [hcfg23] at htailc
          exact htailc) hs100
        rcases hscan with ⟨q, hqle, hqb, hqdata⟩
        have hq0 : q = 0 := by
          by_cases hqneg : q < 0
          · exfalso
            have hd0 := hqdata 0 ⟨by omega, by
              rw [hheadl]
              omega⟩
            have hb0 : (cfgl.tape 0).1 = SymKind.boundary := by
              have hb : cfgl.tape 0 = Sym.boundary := by simpa using hhashLf
              rw [hb]
              rfl
            rw [hb0] at hd0
            cases hd0
          · by_cases hqpos : 0 < q
            · exfalso
              by_cases hqlt : q < 1 + (k : ℤ)
              · have hj' : (q - 1).toNat < tbits.length := by
                  rw [htlen]
                  omega
                have hj'' : (q - 1).toNat < (targetTape 0 (subAllSelected 0 tbits inst.elements sel)).length := by
                  calc
                    (q - 1).toNat < tbits.length := hj'
                    _ = (subAllSelected 0 tbits inst.elements sel).length := by exact (subAllSelected_length 0 tbits inst.elements sel).symm
                    _ = (targetTape 0 (subAllSelected 0 tbits inst.elements sel)).length := by exact (targetTape_length 0 (subAllSelected 0 tbits inst.elements sel)).symm
                have hta : cfgl.tape q = (targetTape 0 (subAllSelected 0 tbits inst.elements sel))[(q - 1).toNat] := by
                  have hq' : q = 1 + (q - 1).toNat := by omega
                  exact (congrArg (fun x : ℤ => cfgl.tape x) hq').trans (htarg (q - 1).toNat hj'')
                have hqb' : ((targetTape 0 (subAllSelected 0 tbits inst.elements sel))[(q - 1).toNat]).1 = SymKind.boundary := by
                  exact (congrArg (fun x : Sym => x.1) hta.symm).trans hqb
                have hmem : (targetTape 0 (subAllSelected 0 tbits inst.elements sel))[(q - 1).toNat] ∈
                    targetTape 0 (subAllSelected 0 tbits inst.elements sel) :=
                  List.getElem_mem hj''
                exact (targetTape_nonboundary 0 (subAllSelected 0 tbits inst.elements sel)
                  ((targetTape 0 (subAllSelected 0 tbits inst.elements sel))[(q - 1).toNat]) hmem) hqb'
              · have hd0 := hclear q ⟨by omega, by omega⟩
                rw [hd0] at hqb
                simp [Sym.data0] at hqb
            · omega
        have hcheck : ∀ i : ℤ, 1 ≤ i ∧ i < cfgl.headPos → (cfgl.tape i).1 = SymKind.data0 := by
          intro i hi
          have hqdat := hqdata i ⟨by rw [hq0]; omega, by omega⟩
          exact hqdat
        have hfalse : ∀ b ∈ subAllSelected 0 tbits inst.elements sel, b = false := by
          intro b hb_mem
          rcases List.mem_iff_getElem.mp hb_mem with ⟨j, hj, hbj⟩
          have hjk : j < k := by
            rw [subAllSelected_length, htlen] at hj
            exact hj
          have hj_sub : j < (subAllSelected 0 tbits inst.elements sel).length := by
            rw [subAllSelected_length, htlen]
            exact hjk
          have hj_bs : j < (bitsToSym (subAllSelected 0 tbits inst.elements sel)).length := by
            have hlen : (bitsToSym (subAllSelected 0 tbits inst.elements sel)).length =
                (subAllSelected 0 tbits inst.elements sel).length := by
              unfold bitsToSym
              simp
            exact hlen ▸ hj_sub
          have hge1 : 1 ≤ 1 + (j : ℤ) := by omega
          have hle : 1 + (j : ℤ) < cfgl.headPos := by
            rw [hheadl]
            omega
          have hkind : (cfgl.tape (1 + (j : ℤ))).1 = SymKind.data0 := hcheck (1 + (j : ℤ)) ⟨hge1, hle⟩
          have hj'' : j < (targetTape 0 (subAllSelected 0 tbits inst.elements sel)).length := by
            calc
              j < tbits.length := by rw [htlen]; exact hjk
              _ = (subAllSelected 0 tbits inst.elements sel).length := by exact (subAllSelected_length 0 tbits inst.elements sel).symm
              _ = (targetTape 0 (subAllSelected 0 tbits inst.elements sel)).length := by exact (targetTape_length 0 (subAllSelected 0 tbits inst.elements sel)).symm
          have hta : cfgl.tape (1 + (j : ℤ)) =
                      (targetTape 0 (subAllSelected 0 tbits inst.elements sel))[j]'hj'' :=
            htarg j hj''
          have hkind' : ((bitsToSym (subAllSelected 0 tbits inst.elements sel))[j]'hj_bs).1 = SymKind.data0 := by
            have hk : ((targetTape 0 (subAllSelected 0 tbits inst.elements sel))[j]'hj'').1 = SymKind.data0 := by
              simpa [hta] using hkind
            simpa [targetTape_zero] using hk
          have hb : (subAllSelected 0 tbits inst.elements sel)[j] = false := by
            by_cases hbit : (subAllSelected 0 tbits inst.elements sel)[j]
            · exfalso
              have h1 : ((bitsToSym (subAllSelected 0 tbits inst.elements sel))[j]'hj_bs).1 = SymKind.data1 := by
                rw [show (bitsToSym (subAllSelected 0 tbits inst.elements sel))[j]'hj_bs = Sym.data1 from by
                  unfold bitsToSym
                  rw [List.getElem_map]
                  simp [hbit]]
                rfl
              rw [h1] at hkind'
              cases hkind'
            · exact Bool.eq_false_iff.mpr hbit
          rw [← hbj]
          exact hb
        have hval0 : bitsValue (subAllSelected 0 tbits inst.elements sel) = 0 :=
          (bitsValue_eq_zero_iff_all_false _).mpr hfalse
        have hsv := subAllSelected_value 0 tbits inst.elements sel hle_total
        have hsum : selectedSum inst.elements sel = bitsValue tbits := by
          have : 0 = bitsValue tbits - selectedSum inst.elements sel := by
            rw [hval0] at hsv
            exact hsv
          omega
        have hbv : bitsValue tbits = inst.target := by
          dsimp [tbits]
          exact bitsValue_bitsOf inst.target
        refine ⟨sel, hsel_len, ?_⟩
        rw [hbv] at hsum
        exact hsum
    · -- 借位越界：主循环走到 101——与 100 矛盾
      exfalso
      have hgt_total : bitsValue tbits < selectedSum inst.elements sel := by omega
      rcases main_loop_reject inst.elements sel tbits 1 (1 + (k : ℤ)) cfg₄.tape
          (by exact hne) (by exact hpos) hsel_len (by omega : 1 + (tbits.length : ℤ) ≤ 1 + (k : ℤ))
          htarget' hbound' hhashL' (by simpa only [htlen] using hpad') helems' hend' hgt_total with
        ⟨πr, cfgr, hπr, h101⟩
      have hpfx' := SymSteps_prefix_unique_det (M := VerifierSym.transition) Pd
        (SymConfig.mk 4 cfg₄.tape ((1 + (k : ℤ)) + 1)) hdet_d hclose_d hP₀_d hrest' hπr
      rcases hpfx' with hrev' | hfwd'
      · exfalso
        rcases hrev' with ⟨ρ, _, hρ⟩
        have hcfg100' : cfg = SymConfig.mk 100 cfg.tape cfg.headPos := by
          cases cfg with
          | mk s t p => dsimp; rw [show s = 100 from hs100]
        rw [hcfg100'] at hρ
        have hfrom100 : cfgr.state = 100 :=
          steps_from_100 cfg.tape cfg.headPos (π := ρ) (cfg := cfgr) hρ
        rw [hfrom100] at h101
        omega
      · rcases hfwd' with ⟨ρ, _, hρ⟩
        have hcfg101 : cfgr = SymConfig.mk 101 cfgr.tape cfgr.headPos := by
          cases cfgr with
          | mk s t p => dsimp; rw [show s = 101 from h101]
        rw [hcfg101] at hρ
        have h101' : cfg.state = 101 :=
          steps_from_101 cfgr.tape cfgr.headPos (π := ρ) (cfg := cfg) hρ
        rw [h101'] at hs100
        omega
  · -- 完备性：子集和成立 → 构造接受路径
    intro h
    rcases h with ⟨sel, hsel_len, hsum⟩
    rcases branch_phase inst hne hpos htarget sel hsel_len (scan2_from_2 inst hne hpos htarget sel hsel_len) with
      ⟨πb, cfgb, hπb, hs4b, hheadb, htargetb, hb0b, hb1b, hbels, hendb⟩
    rcases hbels with ⟨selb, hsel_lenb, htapeb, hseq⟩
    let k : ℕ := (encodeBitsSym inst.target).length
    let tbits : List Bool := bitsOf inst.target
    have htlen : tbits.length = k := by
      dsimp [tbits, k, bitsOf, symToBits, encodeBitsSym, encodeBitsSymNative]
      rw [List.length_map]
    have htarget' : tapeAgrees cfgb.tape 1 (targetTape 0 tbits) := by
      dsimp [tbits]
      rw [targetTape_zero]
      rw [show bitsToSym (bitsOf inst.target) = encodeBitsSym inst.target from (encodeBitsSym_eq_bitsToSym_bitsOf inst.target).symm]
      exact htargetb
    have hbound' : cfgb.tape (1 + (k : ℤ)) = Sym.boundary := by
      simpa [k] using hb1b
    have hhashL' : cfgb.tape (1 - 1) = Sym.boundary := by
      simpa using hb0b
    have hpad' : ∀ i : ℤ, 1 + (k : ℤ) ≤ i ∧ i < 1 + (k : ℤ) → cfgb.tape i = Sym.data0 := by
      intro i hi
      omega
    have helems' : tapeAgrees cfgb.tape ((1 + (k : ℤ)) + 1) (encodeElementsSymWithSel inst.elements selb) := by
      have hpos' : (1 + (k : ℤ)) + 1 = 2 + (k : ℤ) := by omega
      simpa [k, hpos'] using htapeb
    have hend' : (cfgb.tape ((1 + (k : ℤ)) + 1 + (encodeElementsSymWithSel inst.elements selb).length : ℤ)).1 = SymKind.boundary := by
      have hlenws := WithSel_length inst.elements selb hsel_lenb
      have hpos' : (1 + (k : ℤ)) + 1 = 2 + (k : ℤ) := by omega
      rw [hpos']
      rw [show (encodeElementsSymWithSel inst.elements selb).length = (encodeElementsSym inst.elements).length from hlenws]
      exact congrArg (fun x : Sym => x.1) hendb
    have hle_total : selectedSum inst.elements selb ≤ bitsValue tbits := by
      rw [hseq, hsum]
      dsimp [tbits]
      rw [bitsValue_bitsOf]
    rcases main_loop_correct inst.elements selb tbits 1 (1 + (k : ℤ)) cfgb.tape
        (by exact hne) (by exact hpos) hsel_lenb (by omega : 1 + (tbits.length : ℤ) ≤ 1 + (k : ℤ))
        htarget' hbound' hhashL' (by intro i hi; exact hpad' i (by rw [htlen] at hi; exact hi)) helems' hend' hle_total with
      ⟨πl, cfgl, hπl, hs22, htarg, hheadl, hclear, hhashLf, hgapf, hrightl, hkeep⟩
    have hval0 : bitsValue (subAllSelected 0 tbits inst.elements selb) = 0 := by
      have hsv := subAllSelected_value 0 tbits inst.elements selb hle_total
      rw [hsv, hseq, hsum]
      dsimp [tbits]
      rw [bitsValue_bitsOf]
      omega
    have hfalse : ∀ b ∈ subAllSelected 0 tbits inst.elements selb, b = false :=
      (bitsValue_eq_zero_iff_all_false _).mp hval0
    have htarg_zero : ∀ s ∈ targetTape 0 (subAllSelected 0 tbits inst.elements selb),
                        s = Sym.data0 := by
      rw [targetTape_zero]
      exact bitsToSym_all_false_data0 _ hfalse
    have hbound22 : cfgl.tape cfgl.headPos = Sym.mk SymKind.boundary true := by
      rw [hkeep]
      have hpos1 : cfgl.headPos = (1 + (k : ℤ)) + 1 + (encodeElementsSymWithSel inst.elements selb).length := by
        rw [hheadl]
        omega
      rw [hpos1]
      have hlenws := WithSel_length inst.elements selb hsel_lenb
      have hpos2 : (1 + (k : ℤ)) + 1 + (encodeElementsSymWithSel inst.elements selb).length =
          2 + (k : ℤ) + (encodeElementsSym inst.elements).length := by
        rw [hlenws]
        omega
      rw [hpos2]
      exact hendb
    have hdata23 : ∀ i : ℤ, 0 < i ∧ i ≤ cfgl.headPos - 1 → cfgl.tape i = Sym.data0 := by
      intro i hi
      by_cases hilt : i < 1 + (k : ℤ)
      · have hj' : (i - 1).toNat < tbits.length := by
          rw [htlen]
          omega
        have hj'' : (i - 1).toNat < (targetTape 0 (subAllSelected 0 tbits inst.elements selb)).length := by
          calc
            (i - 1).toNat < tbits.length := hj'
            _ = (subAllSelected 0 tbits inst.elements selb).length := by exact (subAllSelected_length 0 tbits inst.elements selb).symm
            _ = (targetTape 0 (subAllSelected 0 tbits inst.elements selb)).length := by exact (targetTape_length 0 (subAllSelected 0 tbits inst.elements selb)).symm
        have hta : cfgl.tape i = (targetTape 0 (subAllSelected 0 tbits inst.elements selb))[(i - 1).toNat] := by
          have hi' : i = 1 + (i - 1).toNat := by omega
          exact (congrArg (fun x : ℤ => cfgl.tape x) hi').trans (htarg (i - 1).toNat hj'')
        rw [hta]
        exact htarg_zero ((targetTape 0 (subAllSelected 0 tbits inst.elements selb))[(i - 1).toNat])
          (List.getElem_mem hj'')
      · exact hclear i ⟨by omega, by omega⟩
    have hscan := scan23_to_100 (cfgl.headPos - 1) cfgl.tape (by omega : 0 ≤ cfgl.headPos - 1)
      hhashLf hdata23
    rcases hscan with ⟨πs, cfgs, hπs, hs100'⟩
    let rc : SymTransResult := { nextState := 23, writeSym := Sym.mk SymKind.boundary true, moveDir := Dir.L }
    let stepc : SymStep := { fromState := 22, readSym := Sym.mk SymKind.boundary true, result := rc }
    have hstepc : SymSteps VerifierSym.transition cfgl [stepc] (symStepConfig cfgl stepc.result) := by
      refine SymSteps.cons [] stepc cfgl SymSteps.nil (by simpa [stepc, hs22]) ?_ ?_
      · rw [hbound22]
      · rw [hbound22]
        rw [hs22]
        decide
    have hcfg23 : symStepConfig cfgl stepc.result = SymConfig.mk 23 cfgl.tape (cfgl.headPos - 1) := by
      dsimp [symStepConfig]
      rw [show stepc.result = SymTransResult.mk 23 (Sym.mk SymKind.boundary true) Dir.L from by
        dsimp [stepc, rc]]
      simp [SymConfig.mk, Dir.toInt]
      constructor
      · funext x
        by_cases hx : x = cfgl.headPos <;> simp [hx, hbound22]
      · rfl
    have hcfg_b : cfgb = SymConfig.mk 4 cfgb.tape ((1 + (k : ℤ)) + 1) := by
      cases cfgb with
      | mk s t hp =>
          dsimp
          rw [show s = 4 from hs4b]
          rw [show hp = (1 + (k : ℤ)) + 1 from by
            dsimp [k] at hheadb ⊢
            omega]
    have hπl' : SymSteps VerifierSym.transition (SymConfig.mk 4 cfgb.tape ((1 + (k : ℤ)) + 1)) πl cfgl := by
      rw [hcfg_b] at hπl
      exact hπl
    have h1 : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) (πb ++ πl) cfgl :=
      SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        (SymConfig.mk 4 cfgb.tape ((1 + (k : ℤ)) + 1)) cfgl πb πl (by rw [← hcfg_b]; exact hπb) hπl'
    have h2 : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        ((πb ++ πl) ++ [stepc]) (symStepConfig cfgl stepc.result) :=
      SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) cfgl
        (symStepConfig cfgl stepc.result) (πb ++ πl) [stepc] h1 hstepc
    have h3 : SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        ((πb ++ πl) ++ [stepc] ++ πs) cfgs :=
      SymSteps_trans VerifierSym.transition (symInitialConfig (encodeInstanceSym inst))
        (symStepConfig cfgl stepc.result) cfgs ((πb ++ πl) ++ [stepc]) πs h2 (by
          rw [hcfg23]
          exact hπs)
    refine ⟨(πb ++ πl) ++ [stepc] ++ πs, cfgs, ?_, ?_⟩
    · exact (symSteps_initial_iff VerifierSym.verifierSymTransition
               (encodeInstanceSym inst) ((πb ++ πl) ++ [stepc] ++ πs) cfgs).mp h3
    · simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hs100'

-- ============================================================================
-- §fmt 段（状态 4 之前的格式扫描链）不改磁带：q11a（接受 ⟹ 格式）的地基
-- ============================================================================

/-- fmt 状态集（状态 4 之前的格式扫描链：0 → 24 → 29 → 26 → 27 → 38 → 28 → 4）。 -/
abbrev fmtStates : Finset ℕ := {24, 29, 26, 27, 38, 28}

/-- fmt 状态下的转移写回原符号（纯扫描）。 -/
lemma fmt_write_same (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ fmtStates) (hr : r ∈ VerifierSym.transition (q, s)) : r.writeSym = s := by
  have hqlt : q < 102 := by
    dsimp [fmtStates] at hq
    simp at hq
    omega
  have hb : ∀ q : Fin 102, (q : ℕ) ∈ fmtStates → ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk k m) → r.writeSym = Sym.mk k m := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hb ⟨q, hqlt⟩ hq k m r hr

/-- pre4 状态集（状态 4 之前的全部可达状态：0/1/2/3 + 格式检查链 24/29/26/27/38/28）。 -/
abbrev pre4States : Finset ℕ := {0, 1, 2, 3, 24, 29, 26, 27, 38, 28}

/-- pre4 状态的转移后继仍属 pre4 态、进 4（fmt 完成）或 101（陷阱）。 -/
lemma pre4_nextState_closed (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ pre4States) (hr : r ∈ VerifierSym.transition (q, s)) :
    r.nextState ∈ pre4States ∨ r.nextState = 4 ∨ r.nextState = 101 := by
  have hqlt : q < 102 := by
    dsimp [pre4States] at hq
    simp at hq
    omega
  have hb : ∀ q : Fin 102, (q : ℕ) ∈ pre4States → ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition ((q : ℕ), Sym.mk k m) →
        r.nextState ∈ pre4States ∨ r.nextState = 4 ∨ r.nextState = 101 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hb ⟨q, hqlt⟩ hq k m r hr

/-- fmt 段（所有步 fromState ∈ fmtStates）不改磁带。 -/
lemma symSteps_fmt_tape_unchanged {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hfmt : ∀ step ∈ π, step.fromState ∈ fmtStates) :
    cfg.tape = (symInitialConfig input).tape := by
  induction h with
  | nil => rfl
  | cons π₀ step cfg₀ hprev hfrom hread htrans ih =>
      have htape := ih (by intro st hst; exact hfmt st (by rw [List.mem_append]; left; exact hst))
      have hq : step.fromState ∈ fmtStates := hfmt step (by simp)
      have hw := fmt_write_same step.fromState step.readSym step.result hq
        (by rw [← hfrom, ← hread] at htrans; exact htrans)
      dsimp [symStepConfig, SymConfig.mk]
      funext i
      by_cases hi : i = cfg₀.headPos
      · rw [if_pos hi]
        rw [hw]
        rw [hread]
        rw [show cfg₀.headPos = i by rw [hi]]
        rw [← htape]
      · rw [if_neg hi]
        rw [← htape]


-- ============================================================================
-- §q11a 垫脚石：接受路径首格必 #；π₁（第一个 4 之前）的状态与磁带变换
-- ============================================================================

/-- 状态 0 读非 boundary 必进 101（表分析）。 -/
lemma state0_nonboundary_trap (s : Sym) (r : SymTransResult)
    (hs : s.1 ≠ SymKind.boundary) (hr : r ∈ VerifierSym.transition (0, s)) :
    r.nextState = 101 := by
  rcases s with ⟨k, m⟩
  have hb : ∀ k : SymKind, ∀ m : Bool, (Sym.mk k m).1 ≠ SymKind.boundary →
      ∀ r : SymTransResult, r ∈ VerifierSym.transition (0, (k, m)) → r.nextState = 101 := by
    native_decide
  exact hb k m hs r hr

/-- SymSteps 空路径：π = [] 时 cfg = cfg₀。 -/
lemma symSteps_empty {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg) (hπ : π = []) : cfg = cfg₀ := by
  induction h with
  | nil => rfl
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hlen : π₀.length + 1 = 0 := by simpa using congrArg List.length hπ
      omega

/-- SymSteps 的末步提取：π ≠ [] 时末步合法且前段从 cfg' 一步后到 cfg。 -/
lemma symSteps_last {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg : SymConfig}
    {π : List SymStep} (h : SymSteps M cfg₀ π cfg) (hπ : π ≠ []) :
    ∃ π₀ step cfg', π = π₀ ++ [step] ∧ SymSteps M cfg₀ π₀ cfg' ∧
      step.fromState = cfg'.state ∧ step.readSym = cfg'.tape cfg'.headPos ∧
      step.result ∈ M (cfg'.state, cfg'.tape cfg'.headPos) ∧
      symStepConfig cfg' step.result = cfg := by
  induction h with
  | nil => exact (hπ rfl).elim
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      refine ⟨π₀, step, cfg', rfl, hprev, hfrom, hread, htrans, rfl⟩

/-- SymSteps 的首步分解（对 π₂ 长度强归纳 + 反复末步提取）。 -/
lemma symSteps_head_split {M : ℕ × Sym → Finset SymTransResult} {cfg₀ cfg : SymConfig}
    (step : SymStep) (π₂ : List SymStep)
    (h : SymSteps M cfg₀ ([step] ++ π₂) cfg) :
    step.fromState = cfg₀.state ∧
    step.readSym = cfg₀.tape cfg₀.headPos ∧
    step.result ∈ M (cfg₀.state, cfg₀.tape cfg₀.headPos) ∧
    SymSteps M (symStepConfig cfg₀ step.result) π₂ cfg := by
  induction hlen : π₂.length generalizing π₂ cfg₀ cfg step with
  | zero =>
      have hπ₂ : π₂ = [] := by
        cases π₂ with
        | nil => rfl
        | cons x xs => simp at hlen
      rw [hπ₂] at h
      have hne : [step] ≠ [] := by intro hc; cases hc
      rcases symSteps_last h hne with ⟨π₀, st, cfg', hsplit, hprev, hfrom, hread, htrans, hcfg⟩
      have hπ₀ : π₀ = [] := by
        have hlen₀ : π₀.length = 0 := by
          have hlen' : π₀.length + 1 = 1 := by simpa using congrArg List.length hsplit
          omega
        cases π₀ with
        | nil => rfl
        | cons x xs => simp at hlen₀
      have hst : st = step := by
        rw [hπ₀] at hsplit
        rw [List.nil_append] at hsplit
        cases hsplit
        rfl
      cases hπ₀
      have hcfg₀ : cfg' = cfg₀ := symSteps_empty hprev rfl
      rw [hst] at hfrom hread htrans hcfg
      rw [hcfg₀] at hfrom hread htrans hcfg
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hfrom
      · exact hread
      · exact htrans
      · rw [hπ₂]
        rw [← hcfg]
        exact SymSteps.nil
  | succ n ih =>
      have hπ₂ne : π₂ ≠ [] := by
        intro hc
        rw [hc] at hlen
        simp at hlen
      have h' : SymSteps M cfg₀ (([step] ++ π₂.dropLast) ++ [π₂.getLast hπ₂ne]) cfg := by
        rw [List.append_assoc]
        rw [List.dropLast_concat_getLast (l := π₂) hπ₂ne]
        exact h
      have hne' : ([step] ++ π₂.dropLast) ++ [π₂.getLast hπ₂ne] ≠ [] := by
        intro hc
        cases hc
      rcases symSteps_last h' hne' with ⟨π₀, st, cfg', hsplit, hprev, hfrom, hread, htrans, hcfg⟩
      have hπ₀ : π₀ = [step] ++ π₂.dropLast := by
        have hlenπ : π₀.length = ([step] ++ π₂.dropLast).length := by
          have hlen' := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_singleton] at hlen' ⊢
          omega
        calc
          π₀ = (π₀ ++ [st]).take π₀.length := (List.take_left).symm
          _ = (([step] ++ π₂.dropLast) ++ [π₂.getLast hπ₂ne]).take π₀.length := by rw [hsplit]
          _ = [step] ++ π₂.dropLast := by
            rw [List.take_left' (l₁ := [step] ++ π₂.dropLast) (by rw [hlenπ])]
      cases hπ₀
      have hst : st = π₂.getLast hπ₂ne := by
        have hsing : [st] = [π₂.getLast hπ₂ne] :=
          (List.append_right_inj ([step] ++ π₂.dropLast)).mp hsplit.symm
        cases List.cons.inj hsing with
        | intro h1 _ => exact h1
      have hdrop : π₂.dropLast.length = n := by
        have hL := List.dropLast_concat_getLast (l := π₂) hπ₂ne
        have hlen' := congrArg List.length hL
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_singleton] at hlen'
        rw [hlen] at hlen'
        omega
      rcases ih step π₂.dropLast hprev hdrop with ⟨hfrom₀, hread₀, htrans₀, htail⟩
      refine ⟨hfrom₀, hread₀, htrans₀, ?_⟩
      rw [← List.dropLast_concat_getLast (l := π₂) hπ₂ne]
      rw [← hst]
      rw [← hcfg]
      exact SymSteps.cons π₂.dropLast st cfg' htail hfrom hread htrans


-- ============================================================================
-- §q11a 垫脚石：接受路径首格必 #（kind = boundary）
-- ============================================================================

/-- 接受路径（无 101 步）的输入非空且首格 kind = boundary。 -/
lemma accept_path_first_cell_boundary {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hs : cfg.state = 100)
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) :
    0 < input.length ∧ ((symInitialConfig input).tape 0).1 = SymKind.boundary := by
  constructor
  · by_contra h0
    have hempty : input = [] := by
      cases input with
      | nil => rfl
      | cons x xs => exact (h0 (by simp)).elim
    rw [hempty] at h
    cases π with
    | nil =>
        have hcfg := symSteps_empty h rfl
        rw [hcfg] at hs
        dsimp [symInitialConfig, SymConfig.mk] at hs
        norm_num at hs
    | cons step rest =>
        rcases symSteps_head_split step rest h with ⟨hfrom, hread, htrans, htail⟩
        have hblank : step.readSym = Sym.blank := by
          rw [hread]
          simp [symInitialConfig, SymConfig.mk]
        have hnb : step.readSym.1 ≠ SymKind.boundary := by
          rw [hblank]
          simp [Sym.blank]
        have htrans0 : step.result ∈ VerifierSym.transition (0, step.readSym) := by
          have hf0 : step.fromState = 0 := by simpa [symInitialConfig, SymConfig.mk] using hfrom
          rw [← hread] at htrans
          simpa [hf0, symInitialConfig, SymConfig.mk] using htrans
        have h101 := state0_nonboundary_trap step.readSym step.result hnb htrans0
        exact hno101 step (by simp) h101
  · cases π with
    | nil =>
        have hcfg := symSteps_empty h rfl
        rw [hcfg] at hs
        dsimp [symInitialConfig, SymConfig.mk] at hs
        norm_num at hs
    | cons step rest =>
        rcases symSteps_head_split step rest h with ⟨hfrom, hread, htrans, htail⟩
        have hread0 : step.readSym = (symInitialConfig input).tape 0 := by
          rw [hread]
          simp [symInitialConfig, SymConfig.mk]
        have htrans0 : step.result ∈ VerifierSym.transition (0, step.readSym) := by
          have hf0 : step.fromState = 0 := by simpa [symInitialConfig, SymConfig.mk] using hfrom
          rw [← hread] at htrans
          simpa [hf0, symInitialConfig, SymConfig.mk] using htrans
        have hbnd : step.readSym.1 = SymKind.boundary := by
          by_contra hnot
          have h101 := state0_nonboundary_trap step.readSym step.result hnot htrans0
          exact hno101 step (by simp) h101
        rw [← hread0]
        exact hbnd

-- ===================================================
-- q11a 垫脚石:Sym 层 101 吸收与接受路径无 101
-- ===================================================

/-- Sym 层 101 吸收:状态 101 的任意转移回到 101。 -/
lemma state101_absorb (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (101, s)) :
    r.nextState = 101 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r ∈ VerifierSym.transition (101, Sym.mk k m),
      r.nextState = 101 := by
    decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr

/-- 从状态 101 出发的任意路径终态恒为 101。 -/
lemma symSteps_from_101_stays_101 {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h₀ : cfg₀.state = 101)
    (h : SymSteps VerifierSym.transition cfg₀ π cfg) :
    cfg.state = 101 := by
  induction h with
  | nil => exact h₀
  | cons π₀ step cfg' hprev hfrom hread htrans ih =>
      have hst : step.fromState = 101 := by rw [hfrom]; exact ih
      have hnext : step.result.nextState = 101 := by
        have htrans' : step.result ∈ VerifierSym.transition (101, step.readSym) := by
          rw [← hfrom] at htrans
          rw [hst] at htrans
          rw [← hread] at htrans
          exact htrans
        exact state101_absorb step.readSym step.result htrans'
      exact hnext

/-- 接受路径不经过 101:路径中每步的后继状态 ≠ 101。 -/
lemma symAccepts_no_101 {input : List Sym} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition (symInitialConfig input) π cfg)
    (hs : cfg.state = 100) :
    ∀ step ∈ π, step.result.nextState ≠ 101 := by
  have hmain : ∀ {π' : List SymStep} {cfg' : SymConfig},
      SymSteps VerifierSym.transition (symInitialConfig input) π' cfg' →
      cfg'.state ≠ 101 → ∀ step ∈ π', step.result.nextState ≠ 101 := by
    intro π' cfg' h' hne
    induction h' with
    | nil =>
        intro step hmem
        simp at hmem
    | cons π₀ step cfg₀ hprev hfrom hread htrans ih =>
        intro t ht
        rcases List.mem_append.mp ht with h | h
        · have hne₀ : cfg₀.state ≠ 101 := by
            intro h101
            have hnext : step.result.nextState = 101 := by
              have htrans' : step.result ∈ VerifierSym.transition (101, step.readSym) := by
                rw [h101] at htrans
                rw [← hread] at htrans
                exact htrans
              exact state101_absorb step.readSym step.result htrans'
            apply hne
            change step.result.nextState = 101
            exact hnext
          exact ih hne₀ t h
        · rcases List.mem_singleton.mp h with rfl
          intro h101
          apply hne
          change t.result.nextState = 101
          exact h101
  exact hmain h (by rw [hs]; norm_num)


-- ===================================================
-- q11a 垫脚石:1/2/3 段读格 kind 分析(表级)

/-- 状态 1 读的格:data 或 boundary(读其它 → 101)。 -/
lemma state1_read_kind (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (1, s)) (h101 : r.nextState ≠ 101) :
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (1, Sym.mk k m) → r.nextState ≠ 101 →
      k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.boundary := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr h101

/-- 状态 2 读的格:alpha/beta/data/boundary(读其它 → 101)。 -/
lemma state2_read_kind (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (2, s)) (h101 : r.nextState ≠ 101) :
    s.1 = SymKind.alpha ∨ s.1 = SymKind.beta ∨ s.1 = SymKind.data0 ∨
    s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) → r.nextState ≠ 101 →
      k = SymKind.alpha ∨ k = SymKind.beta ∨ k = SymKind.data0 ∨
      k = SymKind.data1 ∨ k = SymKind.boundary := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr h101

/-- 状态 2 读 data 写回原符号且右移。 -/
lemma state2_read_data_write_same (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (2, s)) (h101 : r.nextState ≠ 101)
    (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    r = SymTransResult.mk 2 s Dir.R := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) → r.nextState ≠ 101 →
      (k = SymKind.data0 ∨ k = SymKind.data1) → r = SymTransResult.mk 2 (Sym.mk k m) Dir.R := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr h101 hs

/-- 状态 2 读 alpha/beta 写 sel/nosel 且右移。 -/
lemma state2_read_branch_write_sel (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (2, s)) (h101 : r.nextState ≠ 101)
    (hs : s.1 = SymKind.alpha ∨ s.1 = SymKind.beta) :
    r.writeSym = Sym.mk SymKind.sel false ∨ r.writeSym = Sym.mk SymKind.nosel false := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) → r.nextState ≠ 101 →
      (k = SymKind.alpha ∨ k = SymKind.beta) →
      r.writeSym = Sym.mk SymKind.sel false ∨ r.writeSym = Sym.mk SymKind.nosel false := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr h101 hs

/-- 状态 2 读 boundary 进 3 且写回 boundary 右移。 -/
lemma state2_read_boundary_to_3 (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (2, s)) (h101 : r.nextState ≠ 101)
    (hs : s.1 = SymKind.boundary) :
    r = SymTransResult.mk 3 s Dir.S := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (2, Sym.mk k m) → r.nextState ≠ 101 →
      k = SymKind.boundary → r = SymTransResult.mk 3 (Sym.mk k m) Dir.S := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr h101 hs

/-- 状态 3 读 (boundary, false) 写 (boundary, true) 进 24;读 (boundary, true) → 101。 -/
lemma state3_read_boundary (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (3, s)) (h101 : r.nextState ≠ 101) :
    s.1 = SymKind.boundary ∧ s.2 = false ∧ r.writeSym = Sym.mk SymKind.boundary true ∧
    r.nextState = 24 := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (3, Sym.mk k m) → r.nextState ≠ 101 →
      k = SymKind.boundary ∧ m = false ∧ r.writeSym = Sym.mk SymKind.boundary true ∧
      r.nextState = 24 := by
    native_decide
  rcases s with ⟨k, m⟩
  exact hdec k m r hr h101


-- ===================================================
-- q11a:P 支转移引理(0→1、1→1、1→2)
-- ===================================================

/-- 0 → 1:首步读 (boundary, m) 写回右移,进入状态 1、头在 1。 -/
lemma pre4_step_0_to_1 {input : List Sym} (step : SymStep)
    (hfrom : step.fromState = (symInitialConfig input).state)
    (hread : step.readSym = (symInitialConfig input).tape (symInitialConfig input).headPos)
    (htrans : step.result ∈ VerifierSym.transition (step.fromState, step.readSym))
    (hno101 : step.result.nextState ≠ 101) :
    step.result.nextState = 1 ∧
    symStepConfig (symInitialConfig input) step.result =
      SymConfig.mk 1 (symInitialConfig input).tape 1 := by
  have hkind : step.readSym.1 = SymKind.boundary := by
    by_contra hnb
    have h101 := state0_nonboundary_trap step.readSym step.result hnb
      (by rw [hfrom] at htrans; exact htrans)
    exact hno101 h101
  have hres : step.result = SymTransResult.mk 1 step.readSym Dir.R := by
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (0, (k, m)) → r.nextState ≠ 101 →
        k = SymKind.boundary → r = SymTransResult.mk 1 (k, m) Dir.R := by
      native_decide
    rw [hfrom] at htrans
    exact hdec step.readSym.1 step.readSym.2 step.result htrans hno101 hkind
  constructor
  · rw [hres]
  · rw [hres]
    dsimp [symStepConfig, symInitialConfig, SymConfig.mk]
    congr
    · funext j
      by_cases hj : j = 0
      · subst j
        rw [if_pos rfl]
        rw [hread]
        rfl
      · rw [if_neg hj]

/-- 1 → 1:读 data 写回右移(从 nextState = 1 推读格是 data)。 -/
lemma pre4_step_1_to_1 {input : List Sym} (n : ℕ) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition
      (1, (symInitialConfig input).tape (1 + (n : ℤ))))
    (hnext1 : step.result.nextState = 1) :
    (((symInitialConfig input).tape (1 + (n : ℤ))).1 = SymKind.data0 ∨
     ((symInitialConfig input).tape (1 + (n : ℤ))).1 = SymKind.data1) ∧
    symStepConfig (SymConfig.mk 1 (symInitialConfig input).tape (1 + (n : ℤ))) step.result =
      SymConfig.mk 1 (symInitialConfig input).tape (1 + ((n + 1 : ℕ) : ℤ)) := by
  have hk := state1_read_kind ((symInitialConfig input).tape (1 + (n : ℤ))) step.result htrans
    (by rw [hnext1]; norm_num)
  rcases hk with hd0 | hd1 | hb
  · have hres : step.result = SymTransResult.mk 1
        ((symInitialConfig input).tape (1 + (n : ℤ))) Dir.R := by
      have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.data0 → r.nextState = 1 →
          r = SymTransResult.mk 1 (k, m) Dir.R := by
        native_decide
      exact hdec _ _ step.result htrans hd0 hnext1
    constructor
    · left; exact hd0
    · rw [hres]
      dsimp [symStepConfig]
      congr 1
      · funext j
        by_cases hj : j = 1 + (n : ℤ) <;> simp [hj]
  · have hres : step.result = SymTransResult.mk 1
        ((symInitialConfig input).tape (1 + (n : ℤ))) Dir.R := by
      have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.data1 → r.nextState = 1 →
          r = SymTransResult.mk 1 (k, m) Dir.R := by
        native_decide
      exact hdec _ _ step.result htrans hd1 hnext1
    constructor
    · right; exact hd1
    · rw [hres]
      dsimp [symStepConfig]
      congr 1
      · funext j
        by_cases hj : j = 1 + (n : ℤ) <;> simp [hj]
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.boundary → r.nextState = 2 := by
      native_decide
    have h2 := hdec _ _ step.result htrans hb
    omega

/-- 1 → 2:读 boundary 写回右移(从 nextState = 2 推读格是 boundary)。 -/
lemma pre4_step_1_to_2 {input : List Sym} (n : ℕ) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition
      (1, (symInitialConfig input).tape (1 + (n : ℤ))))
    (hnext2 : step.result.nextState = 2) :
    ((symInitialConfig input).tape (1 + (n : ℤ))).1 = SymKind.boundary ∧
    symStepConfig (SymConfig.mk 1 (symInitialConfig input).tape (1 + (n : ℤ))) step.result =
      SymConfig.mk 2 (symInitialConfig input).tape (2 + (n : ℤ)) := by
  have hk := state1_read_kind ((symInitialConfig input).tape (1 + (n : ℤ))) step.result htrans
    (by rw [hnext2]; norm_num)
  rcases hk with hd0 | hd1 | hb
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.data0 → r.nextState = 1 := by
      native_decide
    have h1 := hdec _ _ step.result htrans hd0
    omega
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.data1 → r.nextState = 1 := by
      native_decide
    have h1 := hdec _ _ step.result htrans hd1
    omega
  · constructor
    · exact hb
    · have hres : step.result = SymTransResult.mk 2
          ((symInitialConfig input).tape (1 + (n : ℤ))) Dir.R := by
        have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition (1, (k, m)) → k = SymKind.boundary →
            r = SymTransResult.mk 2 (k, m) Dir.R := by
          native_decide
        exact hdec _ _ step.result htrans hb
      rw [hres]
      dsimp [symStepConfig]
      congr 1
      · funext j
        by_cases hj : j = 1 + (n : ℤ) <;> simp [hj]
      · dsimp [Dir.toInt]
        omega


-- ===================================================
-- q11a:P 支转移引理(2→2、2→3、3→24)
-- ===================================================

/-- 2 → 2:读 data 写回 / 读 α/β 写 sel 或 nosel,右移(cfg 参数化)。 -/
lemma pre4_step_2_to_2 (cfg : SymConfig) (n i : ℕ) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (2, cfg.tape cfg.headPos))
    (hnext2 : step.result.nextState = 2) :
    ((cfg.tape cfg.headPos).1 = SymKind.alpha ∨
     (cfg.tape cfg.headPos).1 = SymKind.beta ∨
     (cfg.tape cfg.headPos).1 = SymKind.data0 ∨
     (cfg.tape cfg.headPos).1 = SymKind.data1) ∧
    (step.result.writeSym.1 = SymKind.sel ∨ step.result.writeSym.1 = SymKind.nosel ∨
     step.result.writeSym = cfg.tape cfg.headPos) ∧
    step.result.moveDir = Dir.R ∧
    symStepConfig cfg step.result =
      SymConfig.mk 2
        (fun j => if j = cfg.headPos then step.result.writeSym else cfg.tape j)
        (cfg.headPos + 1) := by
  have hk := state2_read_kind (cfg.tape cfg.headPos) step.result htrans
    (by rw [hnext2]; norm_num)
  have hdir : step.result.moveDir = Dir.R := by
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, (k, m)) → r.nextState = 2 → r.moveDir = Dir.R := by
      native_decide
    exact hdec _ _ step.result htrans hnext2
  constructor
  · rcases hk with hα | hβ | hd0 | hd1 | hb
    · left; exact hα
    · right; left; exact hβ
    · right; right; left; exact hd0
    · right; right; right; exact hd1
    · exfalso
      have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
          r ∈ VerifierSym.transition (2, (k, m)) → k = SymKind.boundary → r.nextState = 3 := by
        native_decide
      have h3 := hdec _ _ step.result htrans hb
      omega
  constructor
  · have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, (k, m)) → r.nextState = 2 →
        r.writeSym.1 = SymKind.sel ∨ r.writeSym.1 = SymKind.nosel ∨ r.writeSym = (k, m) := by
      native_decide
    exact hdec _ _ step.result htrans hnext2
  constructor
  · exact hdir
  · dsimp [symStepConfig]
    rw [hdir, hnext2]
    dsimp [Dir.toInt]


-- ===================================================
-- q11a:P 支转移引理(2→3、3→24)
-- ===================================================

/-- 2 → 3:读 boundary 写回、不动(cfg 参数化)。 -/
lemma pre4_step_2_to_3 (cfg : SymConfig) (n i : ℕ) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (2, cfg.tape cfg.headPos))
    (hnext3 : step.result.nextState = 3) :
    (cfg.tape cfg.headPos).1 = SymKind.boundary ∧
    symStepConfig cfg step.result = SymConfig.mk 3 cfg.tape cfg.headPos := by
  have hk := state2_read_kind (cfg.tape cfg.headPos) step.result htrans
    (by rw [hnext3]; norm_num)
  rcases hk with hα | hβ | hd0 | hd1 | hb
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, (k, m)) → k = SymKind.alpha →
          (m = false → r.nextState = 2) ∧ (m = true → r.nextState = 101) := by
      native_decide
    rcases hdec _ _ step.result htrans hα with ⟨h2, h101⟩
    by_cases hm : (cfg.tape cfg.headPos).2
    · have hn : step.result.nextState = 101 := h101 hm
      omega
    · have hm' : (cfg.tape cfg.headPos).2 = false := by
        cases h : (cfg.tape cfg.headPos).2 <;> simp [h] at hm ⊢
      have hn : step.result.nextState = 2 := h2 hm'
      omega
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, (k, m)) → k = SymKind.beta → r.nextState = 101 := by
      native_decide
    have h2 := hdec _ _ step.result htrans hβ
    omega
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, (k, m)) → k = SymKind.data0 → r.nextState = 2 := by
      native_decide
    have h2 := hdec _ _ step.result htrans hd0
    omega
  · exfalso
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (2, (k, m)) → k = SymKind.data1 → r.nextState = 2 := by
      native_decide
    have h2 := hdec _ _ step.result htrans hd1
    omega
  · constructor
    · exact hb
    · have hres : step.result = SymTransResult.mk 3
          (cfg.tape cfg.headPos) Dir.S := by
        have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
            r ∈ VerifierSym.transition (2, (k, m)) → k = SymKind.boundary →
            r = SymTransResult.mk 3 (k, m) Dir.S := by
          native_decide
        exact hdec _ _ step.result htrans hb
      rw [hres]
      dsimp [symStepConfig]
      congr 1
      · funext j
        by_cases hj : j = cfg.headPos <;> simp [hj]
      · dsimp [Dir.toInt]
        omega

/-- 3 → 24:读 (boundary, false) 写 (boundary, true)、左移,头在元素区末(cfg 参数化)。 -/
lemma pre4_step_3_to_24 (cfg : SymConfig) (n len : ℕ) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (3, cfg.tape cfg.headPos))
    (hnext24 : step.result.nextState = 24) :
    cfg.tape cfg.headPos = Sym.boundary ∧
    step.result.writeSym = Sym.mk SymKind.boundary true ∧
    symStepConfig cfg step.result =
      SymConfig.mk 24
        (fun j => if j = cfg.headPos then Sym.mk SymKind.boundary true else cfg.tape j)
        (cfg.headPos - 1) := by
  have hres : step.result = SymTransResult.mk 24 (Sym.mk SymKind.boundary true) Dir.L := by
    have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
        r ∈ VerifierSym.transition (3, (k, m)) → r.nextState = 24 →
        r = SymTransResult.mk 24 (Sym.mk SymKind.boundary true) Dir.L := by
      native_decide
    exact hdec _ _ step.result htrans hnext24
  have h3 := state3_read_boundary (cfg.tape cfg.headPos)
    step.result htrans (by rw [hnext24]; norm_num)
  constructor
  · apply Prod.ext
    · exact h3.1
    · exact h3.2.1
  constructor
  · exact h3.2.2.1
  · rw [hres]
    dsimp [symStepConfig, Dir.toInt]
    rfl


-- ===================================================
-- q11a:fmt 支转移引理(24/29/26/27/38/28 的表行)
-- ===================================================

/-- 24 支:非 101 转移必读 (data1, false) 写回左移进 29。 -/
lemma pre4_step_24 (s : Sym) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (24, s))
    (hnext : step.result.nextState ≠ 101) :
    s = (SymKind.data1, false) ∧
    step.result = SymTransResult.mk 29 s Dir.L := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (24, (k, m)) → r.nextState ≠ 101 →
      (k, m) = (SymKind.data1, false) ∧ r = SymTransResult.mk 29 (k, m) Dir.L := by
    native_decide
  exact hdec s.1 s.2 step.result htrans hnext

/-- 29 支:读 data0/data1 → 29 左移;读 sel/nosel → 26 左移。 -/
lemma pre4_step_29 (s : Sym) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (29, s))
    (hnext : step.result.nextState ≠ 101) :
    (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) ∧
    (step.result = SymTransResult.mk 29 s Dir.L ∨
     step.result = SymTransResult.mk 26 s Dir.L) := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (29, (k, m)) → r.nextState ≠ 101 →
      (k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.sel ∨ k = SymKind.nosel) ∧
      (r = SymTransResult.mk 29 (k, m) Dir.L ∨ r = SymTransResult.mk 26 (k, m) Dir.L) := by
    native_decide
  exact hdec s.1 s.2 step.result htrans hnext

/-- 26 支:读 data1 → 29 左移;读 boundary → 27 左移。 -/
lemma pre4_step_26 (s : Sym) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (26, s))
    (hnext : step.result.nextState ≠ 101) :
    (s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) ∧
    (step.result = SymTransResult.mk 29 s Dir.L ∨
     step.result = SymTransResult.mk 27 s Dir.L) := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (26, (k, m)) → r.nextState ≠ 101 →
      (k = SymKind.data1 ∨ k = SymKind.boundary) ∧
      (r = SymTransResult.mk 29 (k, m) Dir.L ∨ r = SymTransResult.mk 27 (k, m) Dir.L) := by
    native_decide
  exact hdec s.1 s.2 step.result htrans hnext

/-- 27 支:非 101 转移必读 (data1, false) 写回左移进 38。 -/
lemma pre4_step_27 (s : Sym) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (27, s))
    (hnext : step.result.nextState ≠ 101) :
    s = (SymKind.data1, false) ∧
    step.result = SymTransResult.mk 38 s Dir.L := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (27, (k, m)) → r.nextState ≠ 101 →
      (k, m) = (SymKind.data1, false) ∧ r = SymTransResult.mk 38 (k, m) Dir.L := by
    native_decide
  exact hdec s.1 s.2 step.result htrans hnext

/-- 38 支:读 data0/data1 → 38 左移;读 boundary → 28 右移。 -/
lemma pre4_step_38 (s : Sym) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (38, s))
    (hnext : step.result.nextState ≠ 101) :
    (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) ∧
    (step.result = SymTransResult.mk 38 s Dir.L ∨
     step.result = SymTransResult.mk 28 s Dir.R) := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (38, (k, m)) → r.nextState ≠ 101 →
      (k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.boundary) ∧
      (r = SymTransResult.mk 38 (k, m) Dir.L ∨ r = SymTransResult.mk 28 (k, m) Dir.R) := by
    native_decide
  exact hdec s.1 s.2 step.result htrans hnext

/-- 28 支:读 data0/data1 → 28 右移;读 boundary → 4 右移。 -/
lemma pre4_step_28 (s : Sym) (step : SymStep)
    (htrans : step.result ∈ VerifierSym.transition (28, s))
    (hnext : step.result.nextState ≠ 101) :
    (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 ∨ s.1 = SymKind.boundary) ∧
    (step.result = SymTransResult.mk 28 s Dir.R ∨
     step.result = SymTransResult.mk 4 s Dir.R) := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (28, (k, m)) → r.nextState ≠ 101 →
      (k = SymKind.data0 ∨ k = SymKind.data1 ∨ k = SymKind.boundary) ∧
      (r = SymTransResult.mk 28 (k, m) Dir.R ∨ r = SymTransResult.mk 4 (k, m) Dir.R) := by
    native_decide
  exact hdec s.1 s.2 step.result htrans hnext

-- ===================================================
-- q11a 核心:branch_phase_inv 的任意输入泛化版(格级形态)
-- ===================================================
-- q11a:fmt 支通用引理(写回 s、后继在 fmtStates 或 4)
-- ===================================================

/-- fmt 支通用:状态 q ∈ fmtStates 的非 101 转移写回 s,后继在 fmtStates 或 4。 -/
lemma pre4_fmt_write_same_next (q : ℕ) (s : Sym) (r : SymTransResult)
    (hq : q ∈ fmtStates) (hr : r ∈ VerifierSym.transition (q, s))
    (hnext : r.nextState ≠ 101) :
    r.writeSym = s ∧ (r.nextState ∈ fmtStates ∨ r.nextState = 4) := by
  have hdec : ∀ q ∈ fmtStates, ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (q, (k, m)) → r.nextState ≠ 101 →
      r.writeSym = (k, m) ∧ (r.nextState ∈ fmtStates ∨ r.nextState = 4) := by
    native_decide
  exact hdec q hq s.1 s.2 r hr hnext

/-- 26 → 27:读格必为 Sym.boundary((boundary, false))。 -/
lemma pre4_step_26_boundary_false (s : Sym) (r : SymTransResult)
    (hr : r ∈ VerifierSym.transition (26, s)) (h27 : r.nextState = 27) :
    s = Sym.boundary := by
  have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
      r ∈ VerifierSym.transition (26, (k, m)) → r.nextState = 27 → (k, m) = Sym.boundary := by
    native_decide
  exact (hdec s.1 s.2 r (by simpa using hr) h27)

-- ===================================================

/- completed: branch_phase_inv_general -/
lemma branch_phase_inv_general (input : List Sym) (π : List SymStep) (cfg : SymConfig) :
    SymSteps VerifierSym.transition (symInitialConfig input) π cfg →
    (hno4 : ∀ {π₀ : List SymStep} {cfg₀ : SymConfig},
      SymSteps VerifierSym.transition (symInitialConfig input) π₀ cfg₀ →
      (∃ ρ, π = π₀ ++ ρ) → π₀.length < π.length → cfg₀.state ≠ 4) →
    (hno101 : ∀ step ∈ π, step.result.nextState ≠ 101) →
    cfg.state = 4 →
    ∃ n len : ℕ,
      cfg.headPos = (n : ℤ) + 2 ∧
      (cfg.tape 0).1 = SymKind.boundary ∧
      (∀ j : ℤ, j < (n : ℤ) + 1 → cfg.tape j = (symInitialConfig input).tape j) ∧
      (∀ j : ℕ, j < n → ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig input).tape (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (cfg.tape ((n : ℤ) + 1)).1 = SymKind.boundary ∧
      cfg.tape ((n : ℤ) + 1) = (symInitialConfig input).tape ((n : ℤ) + 1) ∧
      ((symInitialConfig input).tape ((n : ℤ) + 1)).1 = SymKind.boundary ∧
      ((symInitialConfig input).tape ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary ∧
      (∀ j : ℕ, j < len →
        ((cfg.tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.sel ∨
         (cfg.tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.nosel ∨
         cfg.tape ((n : ℤ) + 2 + (j : ℤ)) = (symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ)))) ∧
      (∀ j : ℕ, j < len → ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.beta ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha →
        ((symInitialConfig input).tape ((n : ℤ) + 2 + (j : ℤ))).2 = false) ∧
      (∀ j : ℤ, (n : ℤ) + 2 + (len : ℤ) < j → cfg.tape j = (symInitialConfig input).tape j) ∧
      cfg.tape ((n : ℤ) + 2 + (len : ℤ)) = Sym.mk SymKind.boundary true := by
  intro hπ hno4 hno101 hs4
  have hbnd0 : ((symInitialConfig input).tape 0).1 = SymKind.boundary := by
    by_cases hnil : π = []
    · subst π
      exfalso
      rw [symSteps_empty hπ rfl] at hs4
      norm_num [symInitialConfig, SymConfig.mk] at hs4
    · rcases List.exists_cons_of_ne_nil hnil with ⟨step₀, π₀, hπeq⟩
      rcases symSteps_head_split step₀ π₀ (hπeq ▸ hπ) with ⟨hfrom', hread', htrans', htail⟩
      have hread0 : step₀.readSym = (symInitialConfig input).tape 0 := by
        rw [hread']
        dsimp [symInitialConfig, SymConfig.mk]
      have hk : step₀.readSym.1 = SymKind.boundary := by
        by_contra hnb
        have hf0 : step₀.fromState = 0 := by simpa [symInitialConfig, SymConfig.mk] using hfrom'
        have htr : step₀.result ∈ VerifierSym.transition (0, step₀.readSym) := by
          rw [← hread'] at htrans'
          have hst0 : (symInitialConfig input).state = 0 := by rfl
          rw [hst0] at htrans'
          exact htrans'
        have h101 := state0_nonboundary_trap step₀.readSym step₀.result hnb htr
        exact hno101 step₀ (by simp [hπeq]) h101
      rw [hread0] at hk
      exact hk
  let tape₀ : ℤ → Sym := (symInitialConfig input).tape
  let P : List SymStep → SymConfig → Prop := fun π₁ cfg₁ =>
    (cfg₁.state = 0 ∧ π₁ = [] ∧ cfg₁ = symInitialConfig input) ∨
    (cfg₁.state = 1 ∧ ∃ n : ℕ, cfg₁ = SymConfig.mk 1 tape₀ (1 + (n : ℤ)) ∧
      (∀ j < n, (tape₀ (1 + (j : ℤ))).1 = SymKind.data0 ∨ (tape₀ (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (tape₀ 0).1 = SymKind.boundary) ∨
    (cfg₁.state = 2 ∧ ∃ n i : ℕ, cfg₁.headPos = 2 + (n : ℤ) + (i : ℤ) ∧
      (∀ j : ℕ, j < i → (cfg₁.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.sel ∨
        (cfg₁.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.nosel ∨
        cfg₁.tape (2 + (n : ℤ) + (j : ℤ)) = tape₀ (2 + (n : ℤ) + (j : ℤ))) ∧
      (∀ j : ℕ, j < i → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.beta ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < i → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < i → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha →
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).2 = false) ∧
      (∀ j : ℕ, j < n → (tape₀ (1 + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (tape₀ (1 + (n : ℤ))).1 = SymKind.boundary ∧
      (tape₀ 0).1 = SymKind.boundary ∧
      (∀ j : ℤ, j < 2 + (n : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (n : ℤ) + (i : ℤ) ≤ j → cfg₁.tape j = tape₀ j)) ∨
    (cfg₁.state = 3 ∧ ∃ n len : ℕ, cfg₁.headPos = 2 + (n : ℤ) + (len : ℤ) ∧
      (∀ j : ℕ, j < len → (cfg₁.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.sel ∨
        (cfg₁.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.nosel ∨
        cfg₁.tape (2 + (n : ℤ) + (j : ℤ)) = tape₀ (2 + (n : ℤ) + (j : ℤ))) ∧
      (∀ j : ℕ, j < len → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.beta ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha →
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).2 = false) ∧
      (∀ j : ℕ, j < n → (tape₀ (1 + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (tape₀ (1 + (n : ℤ))).1 = SymKind.boundary ∧
      (tape₀ ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary ∧
      (tape₀ 0).1 = SymKind.boundary ∧
      (∀ j : ℤ, j < 2 + (n : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (n : ℤ) + (len : ℤ) < j → cfg₁.tape j = tape₀ j)) ∨
    ((cfg₁.state = 24 ∨ cfg₁.state = 29 ∨ cfg₁.state = 26 ∨ cfg₁.state = 27 ∨
        cfg₁.state = 38 ∨ cfg₁.state = 28) ∧ ∃ n len : ℕ,
      ((cfg₁.state = 24 ∧ cfg₁.headPos = 2 + (n : ℤ) + (len : ℤ) - 1) ∨
       ((cfg₁.state = 29 ∨ cfg₁.state = 26) ∧ 1 + (n : ℤ) ≤ cfg₁.headPos ∧
         cfg₁.headPos ≤ 2 + (n : ℤ) + (len : ℤ) - 2) ∨
       (cfg₁.state = 27 ∧ cfg₁.headPos = (n : ℤ)) ∨
       (cfg₁.state = 38 ∧ 0 ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ (n : ℤ) - 1) ∨
       (cfg₁.state = 28 ∧ 1 ≤ cfg₁.headPos ∧ cfg₁.headPos ≤ 1 + (n : ℤ))) ∧
      (∀ j : ℕ, j < len → (cfg₁.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.sel ∨
        (cfg₁.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.nosel ∨
        cfg₁.tape (2 + (n : ℤ) + (j : ℤ)) = tape₀ (2 + (n : ℤ) + (j : ℤ))) ∧
      (∀ j : ℕ, j < len → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.beta ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → (tape₀ (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.alpha →
        (tape₀ (2 + (n : ℤ) + (j : ℤ))).2 = false) ∧
      (∀ j : ℕ, j < n → (tape₀ (1 + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (tape₀ (1 + (n : ℤ))).1 = SymKind.boundary ∧
      (tape₀ ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary ∧
      (tape₀ 0).1 = SymKind.boundary ∧
      (∀ j : ℤ, j < 2 + (n : ℤ) → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, 2 + (n : ℤ) + (len : ℤ) < j → cfg₁.tape j = tape₀ j) ∧
      cfg₁.tape (2 + (n : ℤ) + (len : ℤ)) = Sym.mk SymKind.boundary true) ∨
    (cfg₁.state = 4 ∧ ∃ n len : ℕ, cfg₁.headPos = (n : ℤ) + 2 ∧
      (∀ j : ℕ, j < len → (cfg₁.tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.sel ∨
        (cfg₁.tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.nosel ∨
        cfg₁.tape ((n : ℤ) + 2 + (j : ℤ)) = tape₀ ((n : ℤ) + 2 + (j : ℤ))) ∧
      (∀ j : ℕ, j < len → (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.beta ∨
        (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) ∧
      (∀ j : ℕ, j < len → (tape₀ ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha →
        (tape₀ ((n : ℤ) + 2 + (j : ℤ))).2 = false) ∧
      (∀ j : ℕ, j < n → (tape₀ (1 + (j : ℤ))).1 = SymKind.data0 ∨
        (tape₀ (1 + (j : ℤ))).1 = SymKind.data1) ∧
      (tape₀ (1 + (n : ℤ))).1 = SymKind.boundary ∧
      (tape₀ ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary ∧
      (tape₀ 0).1 = SymKind.boundary ∧
      cfg₁.tape ((n : ℤ) + 1) = tape₀ ((n : ℤ) + 1) ∧
      (∀ j : ℤ, j < (n : ℤ) + 1 → cfg₁.tape j = tape₀ j) ∧
      (∀ j : ℤ, (n : ℤ) + 2 + (len : ℤ) < j → cfg₁.tape j = tape₀ j) ∧
      cfg₁.tape ((n : ℤ) + 2 + (len : ℤ)) = Sym.mk SymKind.boundary true) ∨
    (cfg₁.state = 101)
  have hP : P π cfg := by
    clear hs4
    induction hπ with
    | nil => left; exact ⟨rfl, rfl, rfl⟩
    | cons π₀ step cfg₀ h_ind h_from h_read h_trans ih =>
        have hno4₀ : ∀ {π₀' : List SymStep} {cfg₀' : SymConfig},
            SymSteps VerifierSym.transition (symInitialConfig input) π₀' cfg₀' →
            (∃ ρ, π₀ = π₀' ++ ρ) → π₀'.length < π₀.length → cfg₀'.state ≠ 4 := by
          intro π₀' cfg₀' h₀' hpre' hlen'
          exact hno4 h₀' (by
            rcases hpre' with ⟨ρ', hρ'⟩
            refine ⟨ρ' ++ [step], by rw [hρ', List.append_assoc]⟩) (by
            simpa [List.length_append] using Nat.le_of_lt hlen')
        have hP₀ : P π₀ cfg₀ := ih hno4₀ (fun step h => hno101 step (by rw [List.mem_append]; left; exact h))
        have hno101step : step.result.nextState ≠ 101 := hno101 step (by simp)
        rcases hP₀ with hs0 | hs1 | hs2 | hs3 | hsfmt | hs4' | hs101
        · -- 0 → 1
            rcases hs0 with ⟨_, _, hcfg₀⟩
            subst cfg₀
            rcases pre4_step_0_to_1 (input := input) step h_from h_read
              (by rw [h_from, h_read]; exact h_trans) hno101step with ⟨hnext, hcfg⟩
            rw [hcfg]
            right; left
            exact ⟨rfl, 0, rfl, by intro j hj; omega, hbnd0⟩
        · -- 1 → 1 / 1 → 2
            rcases hs1 with ⟨_, n, hcfg₀, hdata, hbnd01⟩
            subst cfg₀
            have hmem : step.result ∈ VerifierSym.transition (1, tape₀ (1 + (n : ℤ))) := by
              simpa using h_trans
            by_cases h2 : step.result.nextState = 2
            · rcases pre4_step_1_to_2 (input := input) n step hmem h2 with ⟨hbnd, hcfg⟩
              rw [hcfg]
              right; right; left
              refine ⟨rfl, n, 0, rfl, by intro j hj; omega, by intro j hj; omega,
                by intro j hj; omega, by intro j hj; omega, hdata,
                by simpa using hbnd, hbnd01, by intro j hj; rfl, by intro j hj; rfl⟩
            · have h1 : step.result.nextState = 1 := by
                have hk := state1_read_kind (tape₀ (1 + (n : ℤ))) step.result hmem hno101step
                rcases hk with hd0 | hd1 | hb
                · have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) →
                    k = SymKind.data0 → r.nextState = 1 := by
                    native_decide
                  exact hdec _ _ step.result hmem hd0
                · have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) →
                    k = SymKind.data1 → r.nextState = 1 := by
                    native_decide
                  exact hdec _ _ step.result hmem hd1
                · exfalso
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (1, (k, m)) →
                      k = SymKind.boundary → r.nextState = 2 := by
                    native_decide
                  exact (h2 (hdec _ _ step.result hmem hb)).elim
              rcases pre4_step_1_to_1 (input := input) n step hmem h1 with ⟨hdata', hcfg⟩
              rw [hcfg]
              right; left
              refine ⟨rfl, n + 1, rfl, ?_, hbnd01⟩
              intro j hj
              have hjl : j < n ∨ j = n := by omega
              rcases hjl with hjn | hj_eq
              · exact hdata j hjn
              · rw [hj_eq]
                exact hdata'
        · -- 2 → 2 / 2 → 3
            rcases hs2 with ⟨hst2, n, i, hhead, hws, hkind₀, hkind₃, hαm, hdata, hbnd, hbnd02, hlow, hhigh⟩
            have hcell : cfg₀.tape (2 + (n : ℤ) + (i : ℤ)) = tape₀ (2 + (n : ℤ) + (i : ℤ)) :=
              hhigh (2 + (n : ℤ) + (i : ℤ)) (by omega)
            have hmem : step.result ∈ VerifierSym.transition (2, cfg₀.tape cfg₀.headPos) := by
              simpa [hst2] using h_trans
            by_cases h3 : step.result.nextState = 3
            · rcases pre4_step_2_to_3 cfg₀ n i step (by simpa [hhead, hst2] using h_trans) h3 with ⟨hbnd', hcfg⟩
              have hbnd1' : (tape₀ ((n : ℤ) + 2 + (i : ℤ))).1 = SymKind.boundary := by
                rw [hhead] at hbnd'
                rw [hcell] at hbnd'
                simpa [add_comm, add_left_comm, add_assoc] using hbnd'
              rw [hcfg]
              right; right; right; left
              refine ⟨rfl, n, i, by rw [hhead], hws, hkind₀, hkind₃, hαm, hdata, hbnd, hbnd1', hbnd02,
                by intro j hj; exact hlow j hj,
                by intro j hj; exact hhigh j (by omega)⟩
            · have h2' : step.result.nextState = 2 := by
                have hk := state2_read_kind (cfg₀.tape cfg₀.headPos) step.result hmem hno101step
                rcases hk with hα | hβ | hd0 | hd1 | hb
                · have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                    k = SymKind.alpha →
                      (m = false → r.nextState = 2) ∧ (m = true → r.nextState = 101) := by
                    native_decide
                  rcases hdec _ _ step.result hmem hα with ⟨h2, h101⟩
                  by_cases hm : (cfg₀.tape cfg₀.headPos).2
                  · exact (hno101step (h101 hm)).elim
                  · have hm' : (cfg₀.tape cfg₀.headPos).2 = false := by
                      cases h : (cfg₀.tape cfg₀.headPos).2 <;> simp [h] at hm ⊢
                    exact h2 hm'
                · exfalso
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                      k = SymKind.beta → r.nextState = 101 := by
                    native_decide
                  exact hno101step (hdec _ _ step.result hmem hβ)
                · have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                    k = SymKind.data0 → r.nextState = 2 := by
                    native_decide
                  exact hdec _ _ step.result hmem hd0
                · have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                    k = SymKind.data1 → r.nextState = 2 := by
                    native_decide
                  exact hdec _ _ step.result hmem hd1
                · exfalso
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                      k = SymKind.boundary → r.nextState = 3 := by
                    native_decide
                  exact (h3 (hdec _ _ step.result hmem hb)).elim
              rcases pre4_step_2_to_2 cfg₀ n i step (by simpa [hhead, hst2] using h_trans) h2' with ⟨hkind', hw', hdir, hcfg⟩
              rw [hcfg]
              right; right; left
              refine ⟨rfl, n, i + 1, by rw [hhead]; rw [Int.natCast_add]; rfl, ?_, ?_, ?_, ?_, hdata, hbnd, hbnd02,
                by intro j hj; change (if j = cfg₀.headPos then step.result.writeSym else cfg₀.tape j) = tape₀ j; rw [if_neg (by omega : j ≠ cfg₀.headPos)]; exact hlow j hj,
                ?_⟩
              · intro j hj
                have hjl : j < i ∨ j = i := by omega
                rcases hjl with hji | hj_eq
                · change (if 2 + (n : ℤ) + (j : ℤ) = cfg₀.headPos then step.result.writeSym
                    else cfg₀.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.sel ∨
                    (if 2 + (n : ℤ) + (j : ℤ) = cfg₀.headPos then step.result.writeSym
                      else cfg₀.tape (2 + (n : ℤ) + (j : ℤ))).1 = SymKind.nosel ∨
                    (if 2 + (n : ℤ) + (j : ℤ) = cfg₀.headPos then step.result.writeSym
                      else cfg₀.tape (2 + (n : ℤ) + (j : ℤ))) = tape₀ (2 + (n : ℤ) + (j : ℤ))
                  by_cases hjeq : 2 + (n : ℤ) + (j : ℤ) = cfg₀.headPos
                  · exfalso
                    rw [hhead] at hjeq
                    omega
                  · rw [if_neg hjeq]
                    exact hws j hji
                · rw [hj_eq]
                  simp [hhead]
                  rcases hw' with hsel | hnosel | heq
                  · left; exact hsel
                  · right; left; exact hnosel
                  · right; right
                    rw [hhead] at heq
                    rw [hcell] at heq
                    exact heq
              · intro j hj
                have hjl : j < i ∨ j = i := by omega
                rcases hjl with hji | hj_eq
                · exact hkind₀ j hji
                · rw [hj_eq]
                  rw [hhead] at hkind'
                  rw [hcell] at hkind'
                  exact hkind'
              · intro j hj
                have hjl : j < i ∨ j = i := by omega
                rcases hjl with hji | hj_eq
                · exact hkind₃ j hji
                · subst j
                  rcases hkind' with hα' | hβ' | hd0' | hd1'
                  · left
                    rw [hhead] at hα'
                    rw [hcell] at hα'
                    exact hα'
                  · exfalso
                    have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                        k = SymKind.beta → r.nextState = 101 := by
                      native_decide
                    have h101' := hdec _ _ step.result hmem hβ'
                    omega
                  · right; left
                    rw [hhead] at hd0'
                    rw [hcell] at hd0'
                    exact hd0'
                  · right; right
                    rw [hhead] at hd1'
                    rw [hcell] at hd1'
                    exact hd1'
              · intro j hj hkindα
                have hjl : j < i ∨ j = i := by omega
                rcases hjl with hji | hj_eq
                · exact hαm j hji hkindα
                · subst j
                  have hαcell : (cfg₀.tape cfg₀.headPos).1 = SymKind.alpha := by
                    rw [← hcell] at hkindα
                    rw [← hhead] at hkindα
                    exact hkindα
                  have hdec : ∀ k m r, r ∈ VerifierSym.transition (2, (k, m)) →
                      k = SymKind.alpha →
                        (m = false → r.nextState = 2) ∧ (m = true → r.nextState = 101) := by
                    native_decide
                  rcases hdec _ _ step.result hmem hαcell with ⟨h2f, h101f⟩
                  by_cases hm : (cfg₀.tape cfg₀.headPos).2
                  · exact (hno101step (h101f hm)).elim
                  · have hm' : (cfg₀.tape cfg₀.headPos).2 = false := by
                      cases h : (cfg₀.tape cfg₀.headPos).2 <;> simp [h] at hm ⊢
                    rw [hhead] at hm'
                    rw [hcell] at hm'
                    exact hm'
              · intro j hj
                change (if j = cfg₀.headPos then step.result.writeSym else cfg₀.tape j) = tape₀ j
                rw [if_neg (by rw [hhead]; omega : j ≠ cfg₀.headPos)]
                have hj' : 2 + (n : ℤ) + (i : ℤ) ≤ j := by
                  rw [Int.natCast_add] at hj
                  omega
                exact hhigh j hj'
        · -- 3 → 24
            rcases hs3 with ⟨hst3', n, len, hhead, hws, hkind₀, hkind₃, hαm, hdata, hbnd, hbnd13, hbnd03, hlow, hhigh⟩
            have hmem : step.result ∈ VerifierSym.transition (3, cfg₀.tape cfg₀.headPos) := by
              simpa [hst3'] using h_trans
            have h24 : step.result.nextState = 24 := by
              have hk := state3_read_boundary (cfg₀.tape cfg₀.headPos) step.result hmem hno101step
              exact hk.2.2.2
            rcases pre4_step_3_to_24 cfg₀ n len step hmem h24 with ⟨hbnd', hw, hcfg⟩
            rw [hcfg]
            right; right; right; right; left
            refine ⟨by simp, n, len, ?_, ?_, ?_, hkind₃, hαm, hdata, hbnd,
              (by simpa [add_comm, add_left_comm, add_assoc] using hbnd13), hbnd03, ?_, ?_, ?_⟩
            · left
              constructor
              · simp
              · dsimp
                rw [hhead]
            · intro j hj
              by_cases hjeq : 2 + (n : ℤ) + (j : ℤ) = cfg₀.headPos
              · exfalso
                rw [hhead] at hjeq
                omega
              · dsimp
                rw [if_neg hjeq]
                exact hws j hj
            · intro j hj
              exact hkind₀ j hj
            · intro j hj
              by_cases hjeq : j = cfg₀.headPos
              · exfalso
                rw [hhead] at hjeq
                omega
              · dsimp
                rw [if_neg hjeq]
                exact hlow j hj
            · intro j hj
              by_cases hjeq : j = cfg₀.headPos
              · exfalso
                rw [hhead] at hjeq
                omega
              · dsimp
                rw [if_neg hjeq]
                exact hhigh j hj
            · change (if 2 + (n : ℤ) + (len : ℤ) = cfg₀.headPos then Sym.mk SymKind.boundary true
                else cfg₀.tape (2 + (n : ℤ) + (len : ℤ))) = Sym.mk SymKind.boundary true
              rw [hhead]
              rw [if_pos rfl]
        · -- fmt → fmt / fmt → 4
            rcases hsfmt with ⟨hst, n, len, hpos, hws, hkind₀, hkind₃, hαm, hdata, hbnd, hbnd1f, hbnd0f, hlow, hhigh, hmark⟩
            have hstin : cfg₀.state ∈ fmtStates := by
              simpa [fmtStates] using hst
            have hwsame := pre4_fmt_write_same_next cfg₀.state (cfg₀.tape cfg₀.headPos) step.result
              hstin h_trans hno101step
            have htape_same : (symStepConfig cfg₀ step.result).tape = cfg₀.tape := by
              funext j
              dsimp [symStepConfig]
              by_cases hj : j = cfg₀.headPos <;> simp [hj, hwsame.1]
            by_cases h4 : step.result.nextState = 4
            · -- fmt → 4:28 读 #₀(于 1+n)右移
              have hst28 : cfg₀.state = 28 := by
                rcases hst with h24 | h29 | h26 | h27 | h38 | h28
                · exfalso
                  rw [h24] at h_trans
                  rcases pre4_step_24 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rw [hr] at h4
                  norm_num at h4
                · exfalso
                  rw [h29] at h_trans
                  rcases pre4_step_29 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hr with hr29 | hr26
                  · rw [hr29] at h4
                    norm_num at h4
                  · rw [hr26] at h4
                    norm_num at h4
                · exfalso
                  rw [h26] at h_trans
                  rcases pre4_step_26 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hr with hr29 | hr27
                  · rw [hr29] at h4
                    norm_num at h4
                  · rw [hr27] at h4
                    norm_num at h4
                · exfalso
                  rw [h27] at h_trans
                  rcases pre4_step_27 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rw [hr] at h4
                  norm_num at h4
                · exfalso
                  rw [h38] at h_trans
                  rcases pre4_step_38 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hr with hr38 | hr28
                  · rw [hr38] at h4
                    norm_num at h4
                  · rw [hr28] at h4
                    norm_num at h4
                · exact h28
              have hbndread : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                rw [hst28] at h_trans
                rcases pre4_step_28 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨hk, hr⟩
                rcases hr with h28r | h4r
                · rw [h28r] at h4
                  norm_num at h4
                · rcases hk with hd0 | hd1 | hb
                  · exfalso
                    have hdec : ∀ k m r, r ∈ VerifierSym.transition (28, (k, m)) →
                        k = SymKind.data0 → r.nextState = 28 := by
                      native_decide
                    have h28'' := hdec _ _ step.result h_trans hd0
                    omega
                  · exfalso
                    have hdec : ∀ k m r, r ∈ VerifierSym.transition (28, (k, m)) →
                        k = SymKind.data1 → r.nextState = 28 := by
                      native_decide
                    have h28'' := hdec _ _ step.result h_trans hd1
                    omega
                  · exact hb
              have hpos28 : cfg₀.headPos = (n : ℤ) + 1 := by
                rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                · exfalso
                  rcases hp24 with ⟨hst', _⟩
                  rw [hst28] at hst'
                  norm_num at hst'
                · exfalso
                  rcases hp29 with ⟨hst', _, _⟩
                  rw [hst28] at hst'
                  norm_num at hst'
                · exfalso
                  rcases hp27 with ⟨hst', _⟩
                  rw [hst28] at hst'
                  norm_num at hst'
                · exfalso
                  rcases hp38 with ⟨hst', _, _⟩
                  rw [hst28] at hst'
                  norm_num at hst'
                · rcases hp28 with ⟨_, h28lo, h28hi⟩
                  by_contra hne
                  have hlt : cfg₀.headPos < (n : ℤ) + 1 := by omega
                  have hlowread : cfg₀.tape cfg₀.headPos = tape₀ cfg₀.headPos :=
                    hlow cfg₀.headPos (by omega : cfg₀.headPos < 2 + (n : ℤ))
                  have hbnd₀ : (tape₀ cfg₀.headPos).1 = SymKind.boundary := by
                    rw [← hlowread]
                    exact hbndread
                  have hup : ↑((cfg₀.headPos - 1).toNat) = cfg₀.headPos - 1 :=
                    Int.toNat_of_nonneg (by omega)
                  have hjz : ↑((cfg₀.headPos - 1).toNat) < (n : ℤ) := by
                    rw [hup]
                    omega
                  have hj : (cfg₀.headPos - 1).toNat < n := by
                    exact_mod_cast hjz
                  have hcell' : tape₀ cfg₀.headPos = tape₀ (1 + ((cfg₀.headPos - 1).toNat : ℕ)) := by
                    congr 1
                    rw [Int.toNat_of_nonneg (by omega : 0 ≤ cfg₀.headPos - 1)]
                    omega
                  have hd : (tape₀ cfg₀.headPos).1 = SymKind.data0 ∨
                      (tape₀ cfg₀.headPos).1 = SymKind.data1 := by
                    rw [hcell']
                    exact hdata (cfg₀.headPos - 1).toNat hj
                  rcases hd with hd0 | hd1
                  · have : SymKind.data0 = SymKind.boundary := hd0.symm.trans hbnd₀
                    nomatch this
                  · have : SymKind.data1 = SymKind.boundary := hd1.symm.trans hbnd₀
                    nomatch this
              have hcfg4 : symStepConfig cfg₀ step.result =
                  SymConfig.mk 4 cfg₀.tape (cfg₀.headPos + 1) := by
                rw [hst28] at h_trans
                rcases pre4_step_28 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                rcases hr with hr28 | hr4r
                · rw [hr28] at h4
                  norm_num at h4
                · rw [hr4r]
                  dsimp [symStepConfig]
                  congr 1
                  · funext j
                    by_cases hj : j = cfg₀.headPos <;> simp [hj, hwsame.1]
              rw [hcfg4]
              right; right; right; right; right; left
              refine ⟨rfl, n, len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hpos28]
                dsimp
                omega
              · intro j hj
                simpa [add_comm, add_left_comm, add_assoc] using hws j hj
              · intro j hj
                simpa [add_comm, add_left_comm, add_assoc] using hkind₀ j hj
              · intro j hj
                simpa [add_comm, add_left_comm, add_assoc] using hkind₃ j hj
              · intro j hj hkindα
                have hαm' := hαm j hj (by simpa [add_comm, add_left_comm, add_assoc] using hkindα)
                simpa [add_comm, add_left_comm, add_assoc] using hαm'
              · intro j hj
                simpa [add_comm, add_left_comm, add_assoc] using hdata j hj
              · exact hbnd
              · exact hbnd1f
              · exact hbnd0f
              · exact (hlow ((n : ℤ) + 1) (by omega) : cfg₀.tape ((n : ℤ) + 1) = tape₀ ((n : ℤ) + 1))
              · intro j hj
                simpa [add_comm, add_left_comm, add_assoc] using hlow j (by omega)
              · intro j hj
                simpa [add_comm, add_left_comm, add_assoc] using hhigh j (by omega)
              · simpa [add_comm, add_left_comm, add_assoc] using hmark
            · -- fmt → fmt
              have hnextfm : step.result.nextState ∈ fmtStates := by
                rcases hwsame.2 with hf | h4'
                · exact hf
                · exfalso
                  exact h4 h4'
              dsimp [P]
              rw [htape_same]
              right; right; right; right; left
              refine ⟨by simpa [symStepConfig, fmtStates] using hnextfm, n, len, ?_, hws, hkind₀, hkind₃, hαm, hdata, hbnd,
                (by simpa [add_comm, add_left_comm, add_assoc] using hbnd1f), hbnd0f, ?_, ?_, hmark⟩
              · -- 头界更新(按状态)
                dsimp [symStepConfig]
                rcases hst with h24 | h29 | h26 | h27 | h38 | h28
                · rw [h24] at h_trans
                  rcases pre4_step_24 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                  · rcases hp24 with ⟨hpst, hph⟩
                    rw [h24] at hpst
                    rw [hph]
                    rw [hr]
                    right; left
                    refine ⟨Or.inl rfl, ?_, by dsimp [Dir.toInt]; omega⟩
                    · have hd1s : (cfg₀.tape cfg₀.headPos).1 = SymKind.data1 := by
                        rcases pre4_step_24 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨hs, _⟩
                        exact congrArg (fun x : Sym => x.1) hs
                      have hlen1 : 1 ≤ len := by
                        by_contra h0
                        have hlen0 : len = 0 := by omega
                        have hcell : cfg₀.tape (2 + (n : ℤ) + (len : ℤ) - 1) =
                            tape₀ (2 + (n : ℤ) + (len : ℤ) - 1) := by
                          rw [hlen0]
                          convert hlow (1 + (n : ℤ)) (by omega) using 3
                          all_goals omega
                        have hb : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          calc
                            (cfg₀.tape cfg₀.headPos).1 = (tape₀ (2 + (n : ℤ) + (len : ℤ) - 1)).1 := by
                              rw [hph, hcell]
                            _ = (tape₀ (1 + (n : ℤ))).1 := by
                              rw [hlen0]
                              have hpos' : 2 + (n : ℤ) + (↑(0 : ℕ) : ℤ) - 1 = 1 + (n : ℤ) := by norm_num; omega
                              exact congrArg (fun t : Sym => t.1) (congrArg tape₀ hpos')
                            _ = SymKind.boundary := hbnd
                        rw [hb] at hd1s
                        nomatch hd1s
                      dsimp [Dir.toInt]
                      omega
                  · rcases hp29 with ⟨hpst, _, _⟩
                    rw [h24] at hpst
                    norm_num at hpst
                  · rcases hp27 with ⟨hpst, _⟩
                    rw [h24] at hpst
                    norm_num at hpst
                  · rcases hp38 with ⟨hpst, _, _⟩
                    rw [h24] at hpst
                    norm_num at hpst
                  · rcases hp28 with ⟨hpst, _, _⟩
                    rw [h24] at hpst
                    norm_num at hpst
                · rw [h29] at h_trans
                  rcases pre4_step_29 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hr with hr29 | hr26
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, hlo, hhi⟩
                      rw [h29] at hpst
                      have hkind : (cfg₀.tape cfg₀.headPos).1 = SymKind.data0 ∨
                          (cfg₀.tape cfg₀.headPos).1 = SymKind.data1 ∨
                          (cfg₀.tape cfg₀.headPos).1 = SymKind.sel ∨
                          (cfg₀.tape cfg₀.headPos).1 = SymKind.nosel := by
                        rcases pre4_step_29 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨hk, _⟩
                        exact hk
                      have hne : cfg₀.headPos ≠ 1 + (n : ℤ) := by
                        intro hb
                        have hkindb0 : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data0 ∨
                            (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data1 ∨
                            (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.sel ∨
                            (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.nosel := by
                          rw [← hb]
                          exact hkind
                        have hbnd0 : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.boundary := by
                          have hlr : cfg₀.tape (1 + (n : ℤ)) = tape₀ (1 + (n : ℤ)) := by
                            rw [← hb]
                            exact hlow cfg₀.headPos (by omega : cfg₀.headPos < 2 + (n : ℤ))
                          rw [hlr]
                          exact hbnd
                        rcases hkindb0 with hd0 | hd1 | hsel | hnosel
                        · rw [hbnd0] at hd0
                          nomatch hd0
                        · rw [hbnd0] at hd1
                          nomatch hd1
                        · rw [hbnd0] at hsel
                          nomatch hsel
                        · rw [hbnd0] at hnosel
                          nomatch hnosel
                      rw [hr29]
                      right; left
                      refine ⟨Or.inl rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, _, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                    · rcases hp28 with ⟨hpst, _, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, hlo, hhi⟩
                      rw [h29] at hpst
                      have hkind : (cfg₀.tape cfg₀.headPos).1 = SymKind.data0 ∨
                          (cfg₀.tape cfg₀.headPos).1 = SymKind.data1 ∨
                          (cfg₀.tape cfg₀.headPos).1 = SymKind.sel ∨
                          (cfg₀.tape cfg₀.headPos).1 = SymKind.nosel := by
                        rcases pre4_step_29 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨hk, _⟩
                        exact hk
                      have hne : cfg₀.headPos ≠ 1 + (n : ℤ) := by
                        intro hb
                        have hkindb0 : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data0 ∨
                            (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data1 ∨
                            (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.sel ∨
                            (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.nosel := by
                          rw [← hb]
                          exact hkind
                        have hbnd0 : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.boundary := by
                          have hlr : cfg₀.tape (1 + (n : ℤ)) = tape₀ (1 + (n : ℤ)) := by
                            rw [← hb]
                            exact hlow cfg₀.headPos (by omega : cfg₀.headPos < 2 + (n : ℤ))
                          rw [hlr]
                          exact hbnd
                        rcases hkindb0 with hd0 | hd1 | hsel | hnosel
                        · rw [hbnd0] at hd0
                          nomatch hd0
                        · rw [hbnd0] at hd1
                          nomatch hd1
                        · rw [hbnd0] at hsel
                          nomatch hsel
                        · rw [hbnd0] at hnosel
                          nomatch hnosel
                      rw [hr26]
                      right; left
                      refine ⟨Or.inr rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, _, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                    · rcases hp28 with ⟨hpst, _, _⟩
                      rw [h29] at hpst
                      norm_num at hpst
                · rw [h26] at h_trans
                  rcases pre4_step_26 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨hk26, hr⟩
                  rcases hr with hr29 | hr27
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, hlo, hhi⟩
                      rw [h26] at hpst
                      have hne : cfg₀.headPos ≠ 1 + (n : ℤ) := by
                        intro hb
                        have hlr : cfg₀.tape (1 + (n : ℤ)) = tape₀ (1 + (n : ℤ)) := by
                          rw [← hb]
                          exact hlow cfg₀.headPos (by omega : cfg₀.headPos < 2 + (n : ℤ))
                        have hbnd0 : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.boundary := by
                          rw [hlr]
                          exact hbnd
                        have hd1 : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data1 := by
                          rcases hk26 with hd1' | hbb
                          · rw [← hb]
                            exact hd1'
                          · exfalso
                            have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
                                r ∈ VerifierSym.transition (26, (k, m)) → k = SymKind.boundary →
                                r.nextState ≠ 101 → r.nextState = 27 := by native_decide
                            have h27n : step.result.nextState = 27 :=
                              hdec (cfg₀.tape cfg₀.headPos).1 (cfg₀.tape cfg₀.headPos).2 step.result h_trans hbb hno101step
                            rw [hr29] at h27n
                            norm_num at h27n
                        rw [hbnd0] at hd1
                        nomatch hd1
                      rw [hr29]
                      right; left
                      refine ⟨Or.inl rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, _, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                    · rcases hp28 with ⟨hpst, _, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, hlo, hhi⟩
                      rw [h26] at hpst
                      have hpos_eq : cfg₀.headPos = 1 + (n : ℤ) := by
                        have hkindb' : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                          have hb' : cfg₀.tape cfg₀.headPos = Sym.boundary :=
                            pre4_step_26_boundary_false (cfg₀.tape cfg₀.headPos) step.result h_trans
                              (by rw [hr27])
                          exact congrArg (fun x : Sym => x.1) hb'
                        by_contra hne
                        have hgt : 1 + (n : ℤ) < cfg₀.headPos := by
                          exact lt_of_le_of_ne hlo (Ne.symm hne)
                        -- p ∈ 元素区 → 格 kind ≠ boundary(hws 于 j)
                        have hjp : cfg₀.headPos = 2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ) := by
                          have hnonneg : 0 ≤ cfg₀.headPos - 2 - (n : ℤ) := by omega
                          rw [Int.toNat_of_nonneg hnonneg]
                          omega
                        have hjlt : (cfg₀.headPos - 2 - (n : ℤ)).toNat < len := by
                          have hz : (cfg₀.headPos - 2 - (n : ℤ) : ℤ) < (len : ℤ) := by omega
                          have hn0 : 0 ≤ cfg₀.headPos - 2 - (n : ℤ) := by omega
                          have hup : ↑((cfg₀.headPos - 2 - (n : ℤ)).toNat) = cfg₀.headPos - 2 - (n : ℤ) :=
                            Int.toNat_of_nonneg hn0
                          exact_mod_cast (by rw [hup]; omega : ↑((cfg₀.headPos - 2 - (n : ℤ)).toNat) < (len : ℤ))
                        have hwsj : (cfg₀.tape (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ))).1 = SymKind.sel ∨
                            (cfg₀.tape (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ))).1 = SymKind.nosel ∨
                            cfg₀.tape (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ)) = tape₀ (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ)) := by
                          simpa [add_comm, add_left_comm, add_assoc] using hws (cfg₀.headPos - 2 - (n : ℤ)).toNat hjlt
                        rw [hjp] at hkindb'
                        rcases hwsj with hsel | hnosel | horig
                        · rw [hsel] at hkindb'
                          nomatch hkindb'
                        · rw [hnosel] at hkindb'
                          nomatch hkindb'
                        · rw [horig] at hkindb'
                          -- 原样支:tape₀ 的元素区格 kind ∈ {α,β,data}(hkind₀)
                          have hkind₀j : (tape₀ (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ))).1 = SymKind.alpha ∨
                              (tape₀ (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ))).1 = SymKind.beta ∨
                              (tape₀ (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ))).1 = SymKind.data0 ∨
                              (tape₀ (2 + (n : ℤ) + ((cfg₀.headPos - 2 - (n : ℤ)).toNat : ℤ))).1 = SymKind.data1 := by
                            simpa [add_comm, add_left_comm, add_assoc] using hkind₀ (cfg₀.headPos - 2 - (n : ℤ)).toNat hjlt
                          rcases hkind₀j with hα | hβ | hd0' | hd1'
                          · rw [hα] at hkindb'
                            nomatch hkindb'
                          · rw [hβ] at hkindb'
                            nomatch hkindb'
                          · rw [hd0'] at hkindb'
                            nomatch hkindb'
                          · rw [hd1'] at hkindb'
                            nomatch hkindb'
                      rw [hr27]
                      right; right; left
                      exact ⟨rfl, by dsimp [Dir.toInt]; omega⟩
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, _, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                    · rcases hp28 with ⟨hpst, _, _⟩
                      rw [h26] at hpst
                      norm_num at hpst
                · rw [h27] at h_trans
                  rcases pre4_step_27 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                  · rcases hp24 with ⟨hpst, _⟩
                    rw [h27] at hpst
                    norm_num at hpst
                  · rcases hp29 with ⟨hpst, _, _⟩
                    rw [h27] at hpst
                    norm_num at hpst
                  · rcases hp27 with ⟨hpst, hph⟩
                    rw [h27] at hpst
                    have hn1 : 1 ≤ n := by
                      by_contra h0
                      have hn0 : n = 0 := by omega
                      have hd1 : (cfg₀.tape cfg₀.headPos).1 = SymKind.data1 := by
                        rcases pre4_step_27 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨hs, _⟩
                        exact congrArg (fun x : Sym => x.1) hs
                      rw [hph] at hd1
                      rw [hn0] at hd1
                      change (cfg₀.tape 0).1 = SymKind.data1 at hd1
                      have hlr : cfg₀.tape 0 = tape₀ 0 := hlow 0 (by omega)
                      rw [hlr] at hd1
                      rw [hbnd0f] at hd1
                      nomatch hd1
                    rw [hph]
                    rw [hr]
                    right; right; right; left
                    refine ⟨rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                  · rcases hp38 with ⟨hpst, _, _⟩
                    rw [h27] at hpst
                    norm_num at hpst
                  · rcases hp28 with ⟨hpst, _, _⟩
                    rw [h27] at hpst
                    norm_num at hpst
                · rw [h38] at h_trans
                  rcases pre4_step_38 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hr with hr38 | hr28'
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, _, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, hlo, hhi⟩
                      rw [h38] at hpst
                      have hne0 : cfg₀.headPos ≠ 0 := by
                        intro hb
                        have hdec : ∀ k : SymKind, ∀ m : Bool, ∀ r : SymTransResult,
                            r ∈ VerifierSym.transition (38, (k, m)) → k = SymKind.boundary →
                            r.nextState ≠ 101 → r = SymTransResult.mk 28 (k, m) Dir.R := by
                          native_decide
                        have h0b : (cfg₀.tape 0).1 = SymKind.boundary := by
                          simpa [hlow 0 (by omega)] using hbnd0f
                        have hkindb : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary :=
                          (congrArg (fun p : ℤ => (cfg₀.tape p).1) hb.symm) ▸ h0b
                        have hr28'' : step.result = SymTransResult.mk 28 (cfg₀.tape cfg₀.headPos) Dir.R :=
                          hdec (cfg₀.tape cfg₀.headPos).1 (cfg₀.tape cfg₀.headPos).2 step.result h_trans hkindb hno101step
                        rw [hr38] at hr28''
                        injection hr28'' with hns _ _
                        norm_num at hns
                      rw [hr38]
                      right; right; right; left
                      refine ⟨rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                    · rcases hp28 with ⟨hpst, _, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, _, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, hlo, hhi⟩
                      rw [h38] at hpst
                      rw [hr28']
                      right; right; right; right
                      refine ⟨rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                    · rcases hp28 with ⟨hpst, _, _⟩
                      rw [h38] at hpst
                      norm_num at hpst
                · rw [h28] at h_trans
                  rcases pre4_step_28 (cfg₀.tape cfg₀.headPos) step h_trans hno101step with ⟨_, hr⟩
                  rcases hr with hr28 | hr4
                  · rcases hpos with hp24 | hp29 | hp27 | hp38 | hp28
                    · rcases hp24 with ⟨hpst, _⟩
                      rw [h28] at hpst
                      norm_num at hpst
                    · rcases hp29 with ⟨hpst, _, _⟩
                      rw [h28] at hpst
                      norm_num at hpst
                    · rcases hp27 with ⟨hpst, _⟩
                      rw [h28] at hpst
                      norm_num at hpst
                    · rcases hp38 with ⟨hpst, _, _⟩
                      rw [h28] at hpst
                      norm_num at hpst
                    · rcases hp28 with ⟨hpst, hlo, hhi⟩
                      rw [h28] at hpst
                      have hne : cfg₀.headPos ≠ 1 + (n : ℤ) := by
                        intro hb
                        have hk28 := (pre4_step_28 (cfg₀.tape cfg₀.headPos) step h_trans hno101step).1
                        simp only [hb] at hk28
                        have hd0c : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data0 → False := by
                          intro hd0
                          rw [hlow (1 + (n : ℤ)) (by omega)] at hd0
                          rw [hbnd] at hd0
                          nomatch hd0
                        have hd1c : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.data1 → False := by
                          intro hd1
                          rw [hlow (1 + (n : ℤ)) (by omega)] at hd1
                          rw [hbnd] at hd1
                          nomatch hd1
                        have hbbc : (cfg₀.tape (1 + (n : ℤ))).1 = SymKind.boundary → False := by
                          intro hbb
                          have hdec : ∀ k m r, r ∈ VerifierSym.transition (28, (k, m)) →
                              k = SymKind.boundary → r.nextState ≠ 101 → r.nextState = 4 := by
                            native_decide
                          have hbb' : (cfg₀.tape cfg₀.headPos).1 = SymKind.boundary := by
                            simpa [hb] using hbb
                          have h4n : step.result.nextState = 4 :=
                            hdec (cfg₀.tape cfg₀.headPos).1 (cfg₀.tape cfg₀.headPos).2
                              step.result h_trans hbb' hno101step
                          rw [hr28] at h4n
                          norm_num at h4n
                        exact Or.elim hk28 hd0c (fun hrest => Or.elim hrest hd1c (fun hbb => False.elim (hbbc hbb)))
                      rw [hr28]
                      right; right; right; right
                      refine ⟨rfl, by dsimp [Dir.toInt]; omega, by dsimp [Dir.toInt]; omega⟩
                  · exfalso
                    rw [hr4] at h4
                    norm_num at h4
              · intro j hj
                exact hlow j hj
              · intro j hj
                exact hhigh j hj
        · -- 4 支:与 hno4(真前缀无 4)矛盾
            exfalso
            exact (hno4 h_ind ⟨[step], rfl⟩ (by simp)) hs4'.1
        · -- 101 支:与 hno101 矛盾
            exfalso
            have h101' : cfg₀.state = 101 := hs101
            have htr' : step.result ∈ VerifierSym.transition (101, step.readSym) := by
              rw [h101'] at h_trans
              rw [← h_read] at h_trans
              exact h_trans
            exact hno101step (state101_absorb step.readSym step.result htr')
  -- 提取结论
  rcases hP with hs0' | hs1' | hs2' | hs3' | hsfmt' | hs4' | hs101'
  · rcases hs0' with ⟨hst0, _, _⟩
    rw [hst0] at hs4
    norm_num at hs4
  · rcases hs1' with ⟨hst1, _⟩
    rw [hst1] at hs4
    norm_num at hs4
  · rcases hs2' with ⟨hst2, _⟩
    rw [hst2] at hs4
    norm_num at hs4
  · rcases hs3' with ⟨hst3, _⟩
    rw [hst3] at hs4
    norm_num at hs4
  · rcases hsfmt' with ⟨hstf, _⟩
    rcases hstf with h24 | h29 | h26 | h27 | h38 | h28
    · rw [h24] at hs4
      norm_num at hs4
    · rw [h29] at hs4
      norm_num at hs4
    · rw [h26] at hs4
      norm_num at hs4
    · rw [h27] at hs4
      norm_num at hs4
    · rw [h38] at hs4
      norm_num at hs4
    · rw [h28] at hs4
      norm_num at hs4
  · rcases hs4' with ⟨_, n, len, hhead, hws, hkind₀k, hkind₃k, hαmk, hdata, hbndk, hbnd1k, hbnd0k, hmid, hlow, hhigh, hmark⟩
    refine ⟨n, len, hhead, ?_, hlow, hdata, ?_, hmid, (by simpa [add_comm] using hbndk), hbnd1k, hws, hkind₀k, hkind₃k, hαmk, ?_, hmark⟩
    · rw [show cfg.tape 0 = tape₀ 0 from hlow 0 (by omega)]
      exact hbnd0k
    · rw [hmid]
      simpa [add_comm, add_left_comm, add_assoc] using hbndk
    · intro j hj
      exact hhigh j hj
  · exfalso
    have h101' : cfg.state = 101 := hs101'
    rw [h101'] at hs4
    norm_num at hs4


/-- q11a 骨架:接受串的输入形态(格级)。boundary(#₁)之后的右垃圾不在形态内。 -/
theorem symAccepts_implies_skeleton (w : List Sym) :
    symAccepts VerifierSym.verifierSymTransition VerifierSym.acceptStates w →
    ∃ n len : ℕ,
      (n + 2 + len + 1 ≤ w.length) ∧
      ((symInitialConfig w).tape 0).1 = SymKind.boundary ∧
      (∀ j : ℕ, j < n → ((symInitialConfig w).tape (1 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig w).tape (1 + (j : ℤ))).1 = SymKind.data1) ∧
      ((symInitialConfig w).tape ((n : ℤ) + 1)).1 = SymKind.boundary ∧
      (∀ j : ℕ, j < len → ((symInitialConfig w).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.alpha ∨
        ((symInitialConfig w).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.beta ∨
        ((symInitialConfig w).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data0 ∨
        ((symInitialConfig w).tape ((n : ℤ) + 2 + (j : ℤ))).1 = SymKind.data1) := by
  intro h
  rcases h with ⟨π, cfg, hpath, hacc⟩
  have hπ : SymSteps VerifierSym.transition (symInitialConfig w) π cfg :=
    reachablePath_to_steps hpath
  have hs100 : cfg.state = 100 := by
    simpa [VerifierSym.acceptStates, VerifierSym.qAccept] using hacc
  have hno101 : ∀ step ∈ π, step.result.nextState ≠ 101 :=
    symAccepts_no_101 hπ hs100
  rcases backchain_to_first4 hπ (by rw [hs100]; native_decide) with
    ⟨π₁, π₂, cfg₄, hsplit, hπ₁, hs4, hno4₁, hrest⟩
  have hno101₁ : ∀ step ∈ π₁, step.result.nextState ≠ 101 := by
    intro step hstep
    exact hno101 step (by rw [hsplit]; exact List.mem_append_left _ hstep)
  rcases branch_phase_inv_general w π₁ cfg₄ hπ₁ hno4₁ hno101₁ hs4 with
    ⟨n, len, hhead, hb0, hlow, hdata, hb1, _, hbndw, hbnd1w, hws, hkind₀, hhigh, hmark⟩
  refine ⟨n, len, ?_, ?_, hdata, hbndw, hkind₀⟩
  · -- 下界:n+2+len+1 ≤ w.length(#₁ 位于界内)
    by_contra hlen
    by_cases hlen0 : len = 0
    · have hto2 : ((n : ℤ) + 2).toNat = n + 2 := by
        have hu : ↑(((n : ℤ) + 2).toNat) = (n : ℤ) + 2 := Int.toNat_of_nonneg (by omega)
        rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) from by rw [Int.natCast_add]; rfl] at hu
        omega
      have hcell2 : (symInitialConfig w).tape ((n : ℤ) + 2) = Sym.blank := by
        dsimp [symInitialConfig, SymConfig.mk]
        by_cases hcond : 0 ≤ (n : ℤ) + 2 ∧ ((n : ℤ) + 2).toNat < w.length
        · exfalso
          rcases hcond with ⟨_, hlt⟩
          rw [hto2] at hlt
          apply hlen
          rw [hlen0]
          omega
        · exact dif_neg hcond
      have hb1k' : ((symInitialConfig w).tape ((n : ℤ) + 2)).1 = SymKind.boundary := by
        simpa [hlen0, add_comm, add_left_comm, add_assoc] using hbnd1w
      rw [hcell2] at hb1k'
      dsimp [Sym.blank] at hb1k'
      cases hb1k'
    · have hto3 : ((n : ℤ) + 2 + (len : ℤ)).toNat = n + 2 + len := by
        have hu : ↑(((n : ℤ) + 2 + (len : ℤ)).toNat) = (n : ℤ) + 2 + (len : ℤ) := Int.toNat_of_nonneg (by omega)
        rw [show (n : ℤ) + 2 + (len : ℤ) = ((n + 2 + len : ℕ) : ℤ) from by rw [Int.natCast_add, Int.natCast_add]; rfl] at hu
        omega
      have hcell3 : (symInitialConfig w).tape ((n : ℤ) + 2 + (len : ℤ)) = Sym.blank := by
        dsimp [symInitialConfig, SymConfig.mk]
        by_cases hcond : 0 ≤ (n : ℤ) + 2 + (len : ℤ) ∧ ((n : ℤ) + 2 + (len : ℤ)).toNat < w.length
        · exfalso
          rcases hcond with ⟨_, hlt⟩
          rw [hto3] at hlt
          apply hlen
          omega
        · exact dif_neg hcond
      have hb1k'' : ((symInitialConfig w).tape ((n : ℤ) + 2 + (len : ℤ))).1 = SymKind.boundary := hbnd1w
      rw [hcell3] at hb1k''
      dsimp [Sym.blank] at hb1k''
      cases hb1k''
  · rw [← hlow 0 (by omega)]
    exact hb0


-- ===================================================

end Mp
