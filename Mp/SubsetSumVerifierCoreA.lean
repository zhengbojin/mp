/-
Copyright (c) 2026 Bojin Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bojin Zheng, Jingwen Zheng
-/


import Mp.SubsetSumVerifierCore1

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

set_option maxRecDepth 2000

namespace Mp

/-- 状态 3 读 #₁（未标记 m=false）→ 24 写 (boundary,true) 标 m=1 左移。 -/
lemma step3_hash1 (tape : ℤ → Sym) (p₃ : ℤ) (hhash1 : tape p₃ = Sym.boundary) :
    ∃ step : SymStep, SymSteps VerifierSym.transition (SymConfig.mk 3 tape p₃) [step]
      (SymConfig.mk 24 (fun i => if i = p₃ then Sym.mk SymKind.boundary true else tape i) (p₃ - 1)) := by
  let r3 : SymTransResult := { nextState := 24, writeSym := Sym.mk SymKind.boundary true, moveDir := Dir.L }
  let step3 : SymStep := { fromState := 3, readSym := Sym.boundary, result := r3 }
  let tape3 : ℤ → Sym := fun i => if i = p₃ then Sym.mk SymKind.boundary true else tape i
  refine ⟨step3, ?_⟩
  have htrans3 : step3.result ∈ VerifierSym.transition (3, Sym.boundary) := by decide
  have hstep3 : SymSteps VerifierSym.transition (SymConfig.mk 3 tape p₃) [step3]
      (symStepConfig (SymConfig.mk 3 tape p₃) step3.result) := by
    refine SymSteps.cons [] step3 (SymConfig.mk 3 tape p₃) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape p₃
      rw [hhash1]
    · change step3.result ∈ VerifierSym.transition (3, tape p₃)
      rw [hhash1]
      exact htrans3
  have hcfg3 : symStepConfig (SymConfig.mk 3 tape p₃) step3.result = SymConfig.mk 24 tape3 (p₃ - 1) := by
    simp [symStepConfig, SymConfig.mk, step3, r3, Dir.toInt, tape3]
    omega
  exact hcfg3 ▸ hstep3

/-- 物理磁带编码：每个元素 = [选择符 sel/nosel] ++ 原生位串，与 encodeElementsSym 逐格对齐。 -/
def encodeElementsSymWithSel (elems : List ℕ) (sel : List Bool) : List Sym :=
  joinLists ((elems.zip sel).map (fun p => [if p.2 then Sym.sel else Sym.nosel] ++ encodeBitsSymNative p.1))

/-- 逻辑选中编码：仅拼接 sel=true 的元素的原生位串，不含选择符（用于子集和的数学验证）。 -/
def encodeElementsSymChosen (elems : List ℕ) (sel : List Bool) : List Sym :=
  joinLists ((elems.zip sel).filterMap (fun p => if p.2 then some (encodeBitsSymNative p.1) else none))

/-- 物理编码 = zip.map 的 joinLists（与 blocks' 同构）。 -/
lemma encodeElementsSymWithSel_eq_join (elems : List ℕ) (sel : List Bool)
    (hsel : sel.length = elems.length) :
    encodeElementsSymWithSel elems sel =
      joinLists ((elems.zip sel).map (fun p => [if p.2 then Sym.sel else Sym.nosel] ++ encodeBitsSymNative p.1)) := by
  rfl

/-- 逻辑选中编码 = filterMap 选中的 native 位串的 joinLists。 -/
lemma encodeElementsSymChosen_eq_join (elems : List ℕ) (sel : List Bool)
    (hsel : sel.length = elems.length) :
    encodeElementsSymChosen elems sel =
      joinLists ((elems.zip sel).filterMap (fun p => if p.2 then some (encodeBitsSymNative p.1) else none)) := by
  rfl


/-- 从扫描结果逐块读出选择：每块的选择符格（α/β 位置）若写 sel 则选 true，否则 false。
    （NTM 双分支：α/β 格可写 sel 或 nosel，选择由实际路径决定。） -/
def scanSelPrefix (elems : List ℕ) (tape : ℤ → Sym) (p : ℤ) : List Bool :=
  match elems with
  | [] => []
  | v :: rest => decide (tape p = Sym.sel) :: scanSelPrefix rest tape (p + 1 + ((encodeBitsSymNative v).length : ℤ))

/-- scanSelPrefix 的长度 = 元素个数。 -/
lemma scanSelPrefix_length (elems : List ℕ) (tape : ℤ → Sym) (p : ℤ) :
    (scanSelPrefix elems tape p).length = elems.length := by
  induction elems generalizing p with
  | nil => rfl
  | cons v rest ih => simp [scanSelPrefix, ih]

/-- 原生位串的符号都是 data0/data1。 -/
lemma encodeBitsSymNative_kind (v : ℕ) : ∀ s ∈ encodeBitsSymNative v,
    s.1 = SymKind.data0 ∨ s.1 = SymKind.data1 := by
  intro s hs
  simp [encodeBitsSymNative] at hs
  rcases hs with ⟨d, hd, hs⟩
  rw [← hs]
  by_cases h : d = 0 <;> simp [h]

/-- WithSel 编码的长度与 encodeElementsSym 相同（与选择无关）。 -/
lemma joinLists_length (l : List (List Sym)) : (joinLists l).length = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [joinLists_cons]
      rw [List.length_append]
      rw [ih]
      simp [List.sum_cons]

/-- 逻辑选中编码长度 = 选中元素的原生位串长度之和。 -/
lemma WithSel_length (elems : List ℕ) (sel : List Bool) (hsel : sel.length = elems.length) :
    (encodeElementsSymWithSel elems sel).length = (encodeElementsSym elems).length := by
  rw [encodeElementsSymWithSel_eq_join elems sel hsel]
  rw [joinLists_length]
  rw [List.map_map]
  simp [Function.comp_def, List.length_append, List.length_singleton]
  rw [hsel]
  simp
  rw [← joinLists_map_sel_len elems]
  rw [joinLists_length]
  rw [List.map_map]
  simp [Function.comp_def, List.length_append, List.length_singleton]
  change ((elems.zip sel).map ((fun v : ℕ => (encodeBitsSymNative v).length) ∘ Prod.fst)).sum =
    (elems.map (fun v => (encodeBitsSymNative v).length)).sum
  rw [← List.map_map]
  rw [List.map_fst_zip (Nat.le_of_eq hsel.symm)]

/-- encodeElementsSym 的 cons 展开（统一 α 头）。 -/
lemma encodeElementsSym_cons_eq (v : ℕ) (rest : List ℕ) :
    encodeElementsSym (v :: rest) =
      [Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym rest := by
  cases rest with
  | nil => simp [encodeElementsSym]
  | cons w rest' => rfl

/-- WithSel 的 cons 块展开。 -/
lemma WithSel_cons (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool) :
    encodeElementsSymWithSel (v :: rest) (b :: sel') =
      [if b then Sym.sel else Sym.nosel] ++ encodeBitsSymNative v ++ encodeElementsSymWithSel rest sel' := by
  rfl

/-- 元素区第 0 格（块头）是 α。 -/
lemma encodeElementsSym_head_branch (v : ℕ) (rest : List ℕ)
    (hie : 0 < (encodeElementsSym (v :: rest)).length) :
    ((encodeElementsSym (v :: rest))[0]'(hie)).1 = SymKind.alpha := by
  by_cases hrest : rest = []
  · subst rest
    simp only [encodeElementsSym]
    rw [List.getElem_append_left (by simp)]
    rfl
  · rcases rest with _ | ⟨w, rest'⟩
    · exfalso; exact hrest rfl
    · simp only [encodeElementsSym]
      rw [List.getElem_append_left (by simp)]
      rw [List.getElem_append_left (by simp)]
      rfl

/-- WithSel（按扫描路径选择）的逐格展开：α/β 格 = 路径在该格的实际写入（sel/nosel），data 格 = 原值。 -/
lemma encodeElementsSymWithSel_cell (elems : List ℕ) (tape : ℤ → Sym) (p : ℤ) (i : ℕ)
    (hi : i < (encodeElementsSymWithSel elems (scanSelPrefix elems tape p)).length)
    (hie : i < (encodeElementsSym elems).length) :
    (encodeElementsSymWithSel elems (scanSelPrefix elems tape p))[i] =
      (if (((encodeElementsSym elems)[i]'(hie)).1 = SymKind.alpha ∨ ((encodeElementsSym elems)[i]'(hie)).1 = SymKind.beta)
       then (if decide (tape (p + (i : ℤ)) = Sym.sel) then Sym.sel else Sym.nosel)
       else (encodeElementsSym elems)[i]'(hie)) := by
  induction elems generalizing p i with
  | nil =>
      simp [encodeElementsSymWithSel, scanSelPrefix, joinLists] at hi
  | cons v rest ih =>
      simp only [scanSelPrefix] at hi ⊢
      by_cases hi0 : i = 0
      · subst i
        simp only [scanSelPrefix, WithSel_cons] at hi ⊢
        rw [List.getElem_append_left (by
          rw [List.length_append, List.length_singleton]
          omega)]
        rw [List.getElem_append_left (by
          rw [List.length_singleton]
          omega)]
        have hb := encodeElementsSym_head_branch v rest hie
        simp [hb]
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
        by_cases hirst : i < 1 + (encodeBitsSymNative v).length
        · -- data 格：i ∈ [1, 1+bits)
          have hgetR : (encodeElementsSym (v :: rest))[i]'(hie) = (encodeBitsSymNative v)[i - 1] := by
            by_cases hrest : rest = []
            · subst rest
              simp only [encodeElementsSym]
              rw [List.getElem_append_right (by
                rw [List.length_singleton]
                omega)]
              rfl
            · rcases rest with _ | ⟨w, rest'⟩
              · exfalso; exact hrest rfl
              · simp only [encodeElementsSym]
                rw [List.getElem_append_left (by
                  rw [List.length_append, List.length_singleton]
                  omega)]
                rw [List.getElem_append_right (by
                  rw [List.length_singleton]
                  omega)]
                rfl
          have hkind : (encodeBitsSymNative v)[i - 1].1 = SymKind.data0 ∨ (encodeBitsSymNative v)[i - 1].1 = SymKind.data1 := by
            have hm : (encodeBitsSymNative v)[i - 1] ∈ encodeBitsSymNative v := List.getElem_mem (by omega : i - 1 < (encodeBitsSymNative v).length)
            exact encodeBitsSymNative_kind v _ hm
          rcases i with _ | j
          · omega
          · simp only [scanSelPrefix, WithSel_cons] at ⊢
            rw [List.getElem_append_left (by
              rw [List.length_append, List.length_singleton]
              omega)]
            rw [List.getElem_append_right (by
              rw [List.length_singleton]
              omega)]
            rw [hgetR]
            have hkind' : (encodeBitsSymNative v)[j].1 = SymKind.data0 ∨ (encodeBitsSymNative v)[j].1 = SymKind.data1 := by
              simpa using hkind
            have hna : ¬ ((encodeBitsSymNative v)[j].1 = SymKind.alpha ∨ (encodeBitsSymNative v)[j].1 = SymKind.beta) := by
              rcases hkind' with hk | hk
              · rw [hk]
                decide
              · rw [hk]
                decide
            simp [hna]
        · -- rest 格：i ≥ 1+bits
          let i' := i - (1 + (encodeBitsSymNative v).length)
          have hrest : 1 + (encodeBitsSymNative v).length ≤ i := by omega
          have hi'_lt : i' < (encodeElementsSymWithSel rest (scanSelPrefix rest tape (p + 1 + ((encodeBitsSymNative v).length : ℤ)))).length := by
            have hrest_len : i - (1 + (encodeBitsSymNative v).length) < (encodeElementsSymWithSel rest (scanSelPrefix rest tape (p + 1 + ((encodeBitsSymNative v).length : ℤ)))).length := by
              rw [congrArg List.length (WithSel_cons v rest (decide (tape p = Sym.sel)) (scanSelPrefix rest tape (p + 1 + ((encodeBitsSymNative v).length : ℤ))))] at hi
              simp [List.length_append, List.length_singleton] at hi
              omega
            simpa [i'] using hrest_len
          have hie'_lt : i' < (encodeElementsSym rest).length := by
            have hrest_len : i - (1 + (encodeBitsSymNative v).length) < (encodeElementsSym rest).length := by
              rw [congrArg List.length (encodeElementsSym_cons_eq v rest)] at hie
              simp [List.length_append, List.length_singleton] at hie
              omega
            simpa [i'] using hrest_len
          have hih := ih (p + 1 + ((encodeBitsSymNative v).length : ℤ)) i' hi'_lt hie'_lt
          simp only [scanSelPrefix, WithSel_cons] at ⊢
          rw [List.getElem_append_right (by
            rw [List.length_append, List.length_singleton]
            omega)]
          simp only [List.length_append, List.length_singleton] at ⊢
          simp only [encodeElementsSym_cons_eq] at ⊢
          rw [List.getElem_append_right (by
            rw [List.length_append, List.length_singleton]
            omega)]
          simp only [List.length_append, List.length_singleton] at ⊢
          change (encodeElementsSymWithSel rest (scanSelPrefix rest tape (p + 1 + ((encodeBitsSymNative v).length : ℤ))))[i'] =
            (if (((encodeElementsSym rest)[i']'(hie'_lt)).1 = SymKind.alpha ∨ ((encodeElementsSym rest)[i']'(hie'_lt)).1 = SymKind.beta)
             then (if decide (tape (p + (i : ℤ)) = Sym.sel) then Sym.sel else Sym.nosel)
             else (encodeElementsSym rest)[i']'(hie'_lt))
          rw [hih]
          rw [show p + (i : ℤ) = (p + 1 + ((encodeBitsSymNative v).length : ℤ)) + (i' : ℤ) from by
            dsimp [i']
            omega]


/-- joinLists 的长度 = 各列表长度之和。 -/
lemma encodeElementsSymChosen_length (elems : List ℕ) (sel : List Bool)
    (hsel_len : sel.length = elems.length) :
    (encodeElementsSymChosen elems sel).length =
      ((elems.zip sel).filterMap (fun p => if p.2 then some (List.length (encodeBitsSymNative p.1)) else none)).sum := by
  rw [encodeElementsSymChosen_eq_join elems sel hsel_len]
  rw [joinLists_length]
  simp [List.map_filterMap]


/-- zip 全 true 的选择符映射 = 全 sel 映射。 -/
lemma map_zip_replicate_true (l : List ℕ) :
    (l.zip (List.replicate l.length true)).map (fun p => [if p.2 then Sym.sel else Sym.nosel] ++ encodeBitsSymNative p.1) =
      l.map (fun v => [Sym.sel] ++ encodeBitsSymNative v) := by
  induction l with
  | nil => simp [List.zip]
  | cons v rest ih =>
      change List.map (fun p => [if p.2 then Sym.sel else Sym.nosel] ++ encodeBitsSymNative p.1)
          ((v :: rest).zip (List.replicate (v :: rest).length true)) =
        ([Sym.sel] ++ encodeBitsSymNative v) :: List.map (fun v => [Sym.sel] ++ encodeBitsSymNative v) rest
      rw [List.length_cons]
      rw [List.replicate_succ]
      rw [List.zip_cons_cons]
      simp only [List.map_cons]
      congr 1

/-- digits 2 p 的最高位（getLast）对 p > 0 恒为 1。 -/
lemma digits_last_eq_one (p : ℕ) (hp : 0 < p) :
    (Nat.digits 2 p).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hp)) = 1 := by
  have hne : Nat.digits 2 p ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hp)
  have hlast0 : (Nat.digits 2 p).getLast hne ≠ 0 :=
    Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hp)
  have hlastlt : (Nat.digits 2 p).getLast hne < 2 := by
    exact Nat.digits_lt_base (by norm_num : 1 < 2) (List.getLast_mem hne)
  omega

/-- encodeBitsSymNative v 的最高位（最右格）对 v > 0 恒为 data1。 -/
lemma encodeBitsSymNative_top_data1 (v : ℕ) (hv : 0 < v) :
    (encodeBitsSymNative v)[(encodeBitsSymNative v).length - 1]'(by
      have hlen : 0 < (encodeBitsSymNative v).length := by
        unfold encodeBitsSymNative
        rw [List.length_map]
        exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hv))
      omega) = Sym.data1 := by
  unfold encodeBitsSymNative
  rw [List.getElem_map]
  have hge : (Nat.digits 2 v)[(Nat.digits 2 v).length - 1]'(by
        have hlen : 0 < (Nat.digits 2 v).length := by
          exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hv))
        omega) = 1 := by
    change (Nat.digits 2 v).get ⟨(Nat.digits 2 v).length - 1, by
        have hlen : 0 < (Nat.digits 2 v).length := by
          exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hv))
        omega⟩ = 1
    rw [List.get_length_sub_one]
    exact digits_last_eq_one v hv
  simp [hge]


lemma branch_phase (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v)
    (htarget : 0 < inst.target)
    (sel₀ : List Bool) (hsel₀_len : sel₀.length = inst.elements.length)
    (scan2 : (tape : ℤ → Sym) →
        tapeAgrees tape (2 + (encodeBitsSym inst.target).length)
          (encodeElementsSym inst.elements) →
        tape ((2 + (encodeBitsSym inst.target).length) +
          ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary →
        ∃ π cfg', SymSteps VerifierSym.transition
            (SymConfig.mk 2 tape (2 + (encodeBitsSym inst.target).length)) π cfg' ∧
          cfg'.state = 3 ∧
          cfg'.headPos = (2 + (encodeBitsSym inst.target).length) +
            ((encodeElementsSym inst.elements).length : ℤ) ∧
          cfg'.tape ((2 + (encodeBitsSym inst.target).length) +
            ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary ∧
          (∀ i : ℤ, i < 2 + (encodeBitsSym inst.target).length → cfg'.tape i = tape i) ∧
          ∃ sel : List Bool, sel.length = inst.elements.length ∧
            tapeAgrees cfg'.tape (2 + (encodeBitsSym inst.target).length)
              (encodeElementsSymWithSel inst.elements sel) ∧
            sel = sel₀) :
    ∃ π cfg', SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg' ∧
      cfg'.state = 4 ∧
      cfg'.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) ∧
      tapeAgrees cfg'.tape 1 (encodeBitsSym inst.target) ∧
      cfg'.tape 0 = Sym.boundary ∧
      cfg'.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
      (∃ sel : List Bool, sel.length = inst.elements.length ∧
        tapeAgrees cfg'.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
          (encodeElementsSymWithSel inst.elements sel) ∧
        sel = sel₀) ∧
      cfg'.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) = Sym.mk SymKind.boundary true := by
  let input := encodeInstanceSym inst
  let target := encodeBitsSym inst.target
  let elems := encodeElementsSym inst.elements
  have hlen_tgt : (encodeBitsSym inst.target).length = target.length := by
    dsimp [target]
  have hlen_tgt' : (encodeBitsSym inst.target).length = target.length := by
    dsimp [target]
  let tape := (symInitialConfig input).tape
  have htape_input : tapeAgrees tape 0 input := by
    dsimp [tape]
    exact symInitialConfig_tapeAgrees input
  -- input = [#ₗ] ++ target ++ [#₀] ++ elems ++ [#₁]
  have hinput : input = [Sym.boundary] ++ target ++ [Sym.boundary] ++ elems ++ [Sym.boundary] := by
    rfl
  have htape0 : tape 0 = Sym.boundary := by
    have h := (tapeAgrees_cons tape 0 Sym.boundary
      (target ++ [Sym.boundary] ++ elems ++ [Sym.boundary])).mp ?_
    · exact h.1
    · rw [hinput] at htape_input
      exact htape_input
  have htape1 : tapeAgrees tape 1 (target ++ [Sym.boundary] ++ elems ++ [Sym.boundary]) := by
    have h := (tapeAgrees_cons tape 0 Sym.boundary
      (target ++ [Sym.boundary] ++ elems ++ [Sym.boundary])).mp ?_
    · exact h.2
    · rw [hinput] at htape_input
      exact htape_input
  have htape_target : tapeAgrees tape 1 (target ++ [Sym.boundary]) := by
    have htape1' : tapeAgrees tape 1 ((target ++ [Sym.boundary]) ++ (elems ++ [Sym.boundary])) := by
      simpa [List.append_assoc] using htape1
    exact (tapeAgrees_append tape 1 (target ++ [Sym.boundary]) (elems ++ [Sym.boundary])).mp htape1' |>.1
  have htape_elems_boundary : tapeAgrees tape (1 + ((target ++ [Sym.boundary]).length : ℤ)) (elems ++ [Sym.boundary]) := by
    have htape1' : tapeAgrees tape 1 ((target ++ [Sym.boundary]) ++ (elems ++ [Sym.boundary])) := by
      simpa [List.append_assoc] using htape1
    exact (tapeAgrees_append tape 1 (target ++ [Sym.boundary]) (elems ++ [Sym.boundary])).mp htape1' |>.2
  have htape_elems' : tapeAgrees tape (2 + (target.length : ℤ)) (elems ++ [Sym.boundary]) := by
    convert htape_elems_boundary using 1
    rw [List.length_append, List.length_singleton]
    omega
  have htape_elems : tapeAgrees tape (2 + (target.length : ℤ)) elems := by
    exact (tapeAgrees_append tape (2 + (target.length : ℤ)) elems [Sym.boundary]).mp htape_elems' |>.1
  have hbound0 : tape (1 + (target.length : ℤ)) = Sym.boundary := by
    have h := (tapeAgrees_append tape 1 target [Sym.boundary]).mp htape_target |>.2
    simpa using ((tapeAgrees_cons tape (1 + (target.length : ℤ)) Sym.boundary []).mp h).1
  have hbound1 : tape (2 + (target.length : ℤ) + (elems.length : ℤ)) = Sym.boundary := by
    have h := (tapeAgrees_append tape (2 + (target.length : ℤ)) elems [Sym.boundary]).mp htape_elems' |>.2
    simpa using ((tapeAgrees_cons tape (2 + (target.length : ℤ) + (elems.length : ℤ)) Sym.boundary []).mp h).1
  have helems_ne : elems ≠ [] := by
    intro h
    rcases hcases : inst.elements with _ | ⟨v, vs⟩
    · exact hne hcases
    · have hlen_e : elems.length =
          1 + (encodeBitsSymNative v).length + (encodeElementsSym vs).length := by
        unfold elems
        rw [hcases]
        cases vs with
        | nil =>
            change ([Sym.alpha] ++ encodeBitsSymNative v).length =
              1 + (encodeBitsSymNative v).length + (encodeElementsSym []).length
            simp [encodeElementsSym, List.length_append]
            omega
        | cons w ws =>
            change ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym (w :: ws)).length =
              1 + (encodeBitsSymNative v).length + (encodeElementsSym (w :: ws)).length
            simp [List.length_append]
            omega
      have hlen := congrArg List.length h
      rw [hlen_e] at hlen
      simp at hlen
  -- 阶段 1：状态 0 读 #ₗ → 1
  rcases step0_initial tape htape0 with ⟨step0, hstep0⟩
  -- 阶段 2：状态 1 跨 target → 2
  have hnb_target : ∀ i : ℤ, 1 ≤ i ∧ i < 1 + ((target.length : ℕ) : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i h
    have htape_target_l : tapeAgrees tape 1 target :=
      (tapeAgrees_append tape 1 target [Sym.boundary]).mp htape_target |>.1
    have ioff : ∃ io : ℕ, (io : ℤ) = i - 1 := by
      refine ⟨(i - 1).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - 1)
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < target.length := by omega
    have ht := htape_target_l io hio_lt
    have hnb_io : (target[io]).1 = SymKind.data0 ∨ (target[io]).1 = SymKind.data1 := by
      have hmem : target[io] ∈ target := List.getElem_mem hio_lt
      exact encodeBitsSym_nonboundary inst.target (target[io]) (by simpa [target] using hmem)
    have hidx : 1 + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [ht]
    exact hnb_io
  -- 元素区 α/β/data
  have hnb_elems : ∀ i : ℤ, (2 + (target.length : ℤ)) ≤ i ∧ i < (2 + (target.length : ℤ)) + (elems.length : ℤ) →
      (tape i).1 = SymKind.alpha ∨ (tape i).1 = SymKind.beta ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i h
    have ioff : ∃ io : ℕ, (io : ℤ) = i - (2 + (target.length : ℤ)) := by
      refine ⟨(i - (2 + (target.length : ℤ))).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (2 + (target.length : ℤ)))
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < elems.length := by omega
    have ht := htape_elems io hio_lt
    have hnb_io : (elems[io]).1 = SymKind.alpha ∨ (elems[io]).1 = SymKind.beta ∨ (elems[io]).1 = SymKind.data0 ∨ (elems[io]).1 = SymKind.data1 := by
      have hmem : elems[io] ∈ elems := List.getElem_mem hio_lt
      exact encodeElementsSym_kind inst.elements (elems[io]) (by simpa [elems] using hmem)
    have hidx : (2 + (target.length : ℤ)) + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [ht]
    exact hnb_io
  rcases scanRight1 target.length 1 tape hnb_target hbound0 with ⟨π1, cfg1, hπ1, hs1, hhead1, htape1⟩
  rcases scan2 tape htape_elems hbound1
    with ⟨π2, cfg2, hπ2, hs2, hhead2, hbnd2, hleft2,
      ⟨sel2, hsel2_len, htape_sel2, hsel2_eq₀⟩⟩
  have hcfg1_eq : cfg1 = SymConfig.mk 2 tape (2 + (target.length : ℤ)) := by
    rcases cfg1 with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htape1
    have hs : s = 2 := by simpa using hs1
    have hhp : hp = 1 + (target.length : ℤ) + 1 := by simpa using hhead1
    subst t; subst s; subst hp
    simp [SymConfig.mk]
    omega
  have hcfg2_eq : cfg2 = SymConfig.mk 3 cfg2.tape (2 + (target.length : ℤ) + (elems.length : ℤ)) := by
    rcases cfg2 with ⟨s, t, hp⟩
    have hs : s = 3 := by simpa using hs2
    have hhp : hp = 2 + (target.length : ℤ) + (elems.length : ℤ) := by simpa using hhead2
    subst s; subst hp
    simp [SymConfig.mk]
  -- 状态 3：#₁ 标 m=1 → 24
  let p₃ : ℤ := 2 + (target.length : ℤ) + (elems.length : ℤ)
  have hhash1 : cfg2.tape p₃ = Sym.boundary := by simpa [p₃] using hbnd2
  rcases step3_hash1 cfg2.tape p₃ hhash1 with ⟨step3, hstep3⟩
  let tape3 : ℤ → Sym := fun i => if i = p₃ then Sym.mk SymKind.boundary true else cfg2.tape i
  -- 格式检查实例化
  let p₀ : ℤ := 2 + (target.length : ℤ)

  let blocks' : List (Sym × List Sym) :=
    (inst.elements.zip sel2).map (fun p => (if p.2 then Sym.sel else Sym.nosel, encodeBitsSymNative p.1))
  have hblocks' : ∀ b ∈ blocks', (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
    intro b hb
    dsimp [blocks'] at hb
    rcases List.mem_map.mp hb with ⟨p, hpm, hb⟩
    rw [← hb]
    constructor
    · by_cases hp2 : p.2
      · left
        simp [hp2]
      · right
        simp [hp2]
    · constructor
      · intro h
        have hlen := congrArg List.length h
        simp only [encodeBitsSymNative, List.length_map] at hlen
        have hlen0 : (Nat.digits 2 p.1).length = 0 := hlen
        have hp1mem : p.1 ∈ inst.elements := by
          have hpm1 : p.1 ∈ (inst.elements.zip sel2).map Prod.fst := by
            exact List.mem_map.mpr ⟨p, hpm, rfl⟩
          rw [List.map_fst_zip] at hpm1
          · exact hpm1
          · exact Nat.le_of_eq hsel2_len.symm
        have hd : 0 < (Nat.digits 2 p.1).length := by
          exact List.length_pos_iff_ne_nil.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt (hpos p.1 hp1mem)))
        omega
      · intro s hs
        constructor
        · exact encodeBitsSymNative_nonboundary p.1 s hs
        · dsimp [encodeBitsSymNative] at hs
          rw [List.mem_map] at hs
          rcases hs with ⟨d, hd, hs⟩
          rw [← hs]
          by_cases hd0 : d = 0
          · simp [hd0]
            rfl
          · simp [hd0]
            rfl
  have hlen_eq' : (joinLists (blocks'.map (fun b => [b.1] ++ b.2))).length =
      (encodeElementsSym inst.elements).length := by
    rw [joinLists_length]
    dsimp [blocks']
    simp [List.map_map, Function.comp_def, List.length_cons]
    have hmin : min inst.elements.length sel2.length = inst.elements.length := by omega
    rw [hmin]
    rw [show (inst.elements.zip sel2).map (fun p => (encodeBitsSymNative p.1).length) =
        inst.elements.map (fun v => (encodeBitsSymNative v).length) from by
      change (List.map ((fun v => (encodeBitsSymNative v).length) ∘ Prod.fst) (inst.elements.zip sel2)) =
        inst.elements.map (fun v => (encodeBitsSymNative v).length)
      rw [← List.map_map]
      rw [List.map_fst_zip (Nat.le_of_eq hsel2_len.symm)]]
    rw [show (encodeElementsSym inst.elements).length =
        ((encodeElementsSym inst.elements).map chosenSub).length from by
      rw [List.length_map]]
    rw [← congrArg List.length (joinLists_map_sel_eq inst.elements)]
    rw [joinLists_length]
    rw [List.map_map]
    simp only [Function.comp_def]
    simp only [List.length_append, List.length_singleton]
    rw [List.sum_map_add]
    simp
    omega
  have hblocks_ne' : blocks' ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    dsimp [blocks'] at hlen
    rw [List.length_map, List.length_zip, hsel2_len, Nat.min_self] at hlen
    exact hne (List.eq_nil_of_length_eq_zero hlen)
  have hels_chosen : tapeAgrees tape3 p₀ (joinLists (blocks'.map (fun b => [b.1] ++ b.2))) := by
    intro i hi
    have hne : p₀ + (i : ℤ) ≠ p₃ := by
      have hp₃ : p₃ = 2 + (target.length : ℤ) + (elems.length : ℤ) := rfl
      have hp₀ : p₀ = 2 + (target.length : ℤ) := rfl
      rw [hp₃, hp₀]
      have hlen' : (joinLists (blocks'.map (fun b => [b.1] ++ b.2))).length = elems.length := hlen_eq'
      have hleni : (i : ℤ) < (elems.length : ℤ) := by
        dsimp [elems]
        exact_mod_cast (Nat.lt_of_lt_of_eq hi (by
          dsimp [elems]
          exact hlen'))
      dsimp [elems] at hleni ⊢
      omega
    rw [show tape3 (p₀ + (i : ℤ)) = cfg2.tape (p₀ + (i : ℤ)) from by simp [tape3, hne]]
    have hlen_chosen : (joinLists (blocks'.map (fun b => [b.1] ++ b.2))).length =
        (encodeElementsSymWithSel inst.elements sel2).length := by
      rw [show (encodeElementsSymWithSel inst.elements sel2) =
          joinLists (blocks'.map (fun b => [b.1] ++ b.2)) from by
        dsimp [encodeElementsSymWithSel, blocks']
        simp only [List.map_map, Function.comp_def]]
    have hjl : joinLists (blocks'.map (fun b => [b.1] ++ b.2)) = encodeElementsSymWithSel inst.elements sel2 := by
      dsimp [encodeElementsSymWithSel, blocks']
      simp only [List.map_map, Function.comp_def]
    simpa [← hjl, p₀, target] using htape_sel2 i (Nat.lt_of_lt_of_eq hi hlen_chosen)
  have htgt_sweep : tapeAgrees tape3 (p₀ - (target.length : ℤ) - 1) target := by
    have hidx : p₀ - (target.length : ℤ) - 1 = 1 := by
      dsimp [p₀]
      omega
    rw [hidx]
    intro i hi
    have hne : 1 + (i : ℤ) ≠ p₃ := by
      have hp₃ : p₃ = 2 + (target.length : ℤ) + (elems.length : ℤ) := rfl
      rw [hp₃]
      have hn : (0 : ℤ) < (elems.length : ℤ) := by
        dsimp [elems]
        exact_mod_cast (List.length_pos_iff_ne_nil.mpr helems_ne)
      have hlen : (i : ℤ) < (target.length : ℤ) := by exact_mod_cast hi
      omega
    rw [show tape3 (1 + (i : ℤ)) = tape (1 + (i : ℤ)) from by
      rw [show tape3 (1 + (i : ℤ)) = cfg2.tape (1 + (i : ℤ)) from by simp [tape3, hne]]
      exact hleft2 (1 + (i : ℤ)) (by
        rw [← hlen_tgt]
        have hlen : (i : ℤ) < (target.length : ℤ) := by exact_mod_cast hi
        omega)]
    exact (tapeAgrees_append tape 1 target [Sym.boundary]).mp htape_target |>.1 i hi
  have htgt_data' : ∀ s ∈ target, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := by
    intro s hs
    constructor
    · exact encodeBitsSym_nonboundary inst.target s (by simpa [target] using hs)
    · change s ∈ encodeBitsSym inst.target at hs
      unfold encodeBitsSym at hs
      rw [List.mem_map] at hs
      rcases hs with ⟨x, hx, hs⟩
      rw [← hs]
      by_cases hx0 : x = 0 <;> simp [hx0, Sym.data0, Sym.data1]
  have hne_tgt : target ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    dsimp [target, encodeBitsSym] at hlen
    rw [List.length_map] at hlen
    have hd : (Nat.digits 2 inst.target).length = 0 := hlen
    have hgt : 0 < (Nat.digits 2 inst.target).length := List.length_pos_iff_ne_nil.mpr
      (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt htarget))
    omega
  have hmid_sweep : tape3 (p₀ - 1) = Sym.boundary := by
    have hne : p₀ - 1 ≠ p₃ := by
      have hp₃ : p₃ = 2 + (target.length : ℤ) + (elems.length : ℤ) := rfl
      have hp₀ : p₀ = 2 + (target.length : ℤ) := rfl
      rw [hp₃, hp₀]
      have hn : (0 : ℤ) < (elems.length : ℤ) := by
        dsimp [elems]
        exact_mod_cast (List.length_pos_iff_ne_nil.mpr helems_ne)
      omega
    rw [show tape3 (p₀ - 1) = cfg2.tape (p₀ - 1) from by simp [tape3, hne]]
    rw [hleft2 (p₀ - 1) (by
      dsimp [p₀, target]
      omega)]
    have hidx : p₀ - 1 = 1 + (target.length : ℤ) := by
      dsimp [p₀, target]
      omega
    rw [hidx]
    exact hbound0
  have hleft_sweep : tape3 (p₀ - (target.length : ℤ) - 2) = Sym.boundary := by
    have hne : p₀ - (target.length : ℤ) - 2 ≠ p₃ := by
      have hp₃ : p₃ = 2 + (target.length : ℤ) + (elems.length : ℤ) := rfl
      have hp₀ : p₀ = 2 + (target.length : ℤ) := rfl
      rw [hp₃, hp₀]
      have hn : (0 : ℤ) < (elems.length : ℤ) := by
        dsimp [elems]
        exact_mod_cast (List.length_pos_iff_ne_nil.mpr helems_ne)
      omega
    rw [show tape3 (p₀ - (target.length : ℤ) - 2) = cfg2.tape (p₀ - (target.length : ℤ) - 2) from by simp [tape3, hne]]
    rw [hleft2 (p₀ - (target.length : ℤ) - 2) (by
      dsimp [p₀, target]
      omega)]
    have hidx : p₀ - (target.length : ℤ) - 2 = 0 := by
      dsimp [p₀, target]
      omega
    rw [hidx]
    exact htape0

  have hpos_sweep : ∀ b ∈ blocks', blockTopIs1 b := by
    intro b hb
    dsimp [blocks'] at hb
    rcases List.mem_map.mp hb with ⟨p, hpm, hb⟩
    rw [← hb]
    intro hne
    have hv : 0 < p.1 := hpos p.1 (by
      have hpm1 : p.1 ∈ (inst.elements.zip sel2).map Prod.fst := List.mem_map.mpr ⟨p, hpm, rfl⟩
      rw [List.map_fst_zip] at hpm1
      · exact hpm1
      · exact Nat.le_of_eq hsel2_len.symm)
    have htop1 := encodeBitsSymNative_top_data1 p.1 hv
    simpa using congrArg (fun s : Sym => s.1) htop1
  have htgt_top : (target[target.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hne_tgt) (by norm_num))).1 = SymKind.data1 := by
    have htop := encodeBitsSymNative_top_data1 inst.target htarget
    simpa [target, show encodeBitsSym inst.target = encodeBitsSymNative inst.target from rfl]
      using congrArg (fun s : Sym => s.1) htop
  rcases format_sweep_correct blocks' target p₀
   tape3 hblocks' hpos_sweep hels_chosen htgt_sweep htgt_data' hne_tgt htgt_top hmid_sweep hleft_sweep hblocks_ne'
    with ⟨π4, cfg4, hπ4, hs4, hhead4, htape4⟩
  refine ⟨[step0] ++ π1 ++ π2 ++ [step3] ++ π4, cfg4, ?_, hs4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  have h01 : SymSteps VerifierSym.transition (symInitialConfig input) [step0]
   (SymConfig.mk 1 tape 1) := by
    change SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) [step0] (SymConfig.mk 1 tape 1)
    exact hstep0
  have h012 : SymSteps VerifierSym.transition (symInitialConfig input) ([step0] ++ π1) cfg1 := by
    exact SymSteps_trans VerifierSym.transition (symInitialConfig input) (SymConfig.mk 1 tape 1) cfg1 [step0] π1 h01 hπ1
  have h012' : SymSteps VerifierSym.transition (symInitialConfig input) ([step0] ++ π1) (SymConfig.mk 2 tape (2 + (target.length : ℤ))) := by
    exact hcfg1_eq ▸ h012
  have h0123 : SymSteps VerifierSym.transition (symInitialConfig input) ([step0] ++ π1 ++ π2) cfg2 := by
    exact SymSteps_trans VerifierSym.transition (symInitialConfig input) (SymConfig.mk 2 tape (2 + (target.length : ℤ))) cfg2 ([step0] ++ π1) π2 h012' hπ2
  have h0123' : SymSteps VerifierSym.transition (symInitialConfig input) ([step0] ++ π1 ++ π2) (SymConfig.mk 3 cfg2.tape p₃) := by
    exact hcfg2_eq ▸ h0123
  have h01234 : SymSteps VerifierSym.transition (symInitialConfig input) ([step0] ++ π1 ++ π2 ++ [step3]) (SymConfig.mk 24 tape3 (p₃ - 1)) := by
    exact SymSteps_trans VerifierSym.transition (symInitialConfig input) (SymConfig.mk 3 cfg2.tape p₃) (SymConfig.mk 24 tape3 (p₃ - 1)) ([step0] ++ π1 ++ π2) [step3] h0123' hstep3
  have hcfg4_entry : SymConfig.mk 24 tape3 (p₃ - 1) = SymConfig.mk 24 tape3 (p₀ + ((joinLists (blocks'.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1) := by
    simp [SymConfig.mk]
    rw [show (joinLists (blocks'.map (fun b => b.1 :: b.2))).length = elems.length from by
      dsimp [elems]
      simpa using hlen_eq']
  exact SymSteps_trans VerifierSym.transition (symInitialConfig input) (SymConfig.mk 24 tape3 (p₃ - 1)) cfg4 ([step0] ++ π1 ++ π2 ++ [step3]) π4 h01234 (hcfg4_entry ▸ hπ4)
  · -- headPos = 2 + target.length
    rw [hhead4]
  · -- target 区保持
    rw [htape4]
    intro i hi
    have hne : 1 + (i : ℤ) ≠ p₃ := by
      dsimp [p₃]
      have hlen : (i : ℤ) < (target.length : ℤ) := by exact_mod_cast hi
      omega
    rw [show tape3 (1 + (i : ℤ)) = tape (1 + (i : ℤ)) from by
      rw [show tape3 (1 + (i : ℤ)) = cfg2.tape (1 + (i : ℤ)) from by simp [tape3, hne]]
      rw [hleft2 (1 + (i : ℤ)) (by
        rw [← hlen_tgt]
        have hlen : (i : ℤ) < (target.length : ℤ) := by exact_mod_cast hi
        omega)]]
    exact ((tapeAgrees_append tape 1 target [Sym.boundary]).mp htape_target).1 i hi
  · -- tape 0 = boundary
    rw [htape4]
    have hne : (0 : ℤ) ≠ p₃ := by
      have hp₃ : p₃ = 2 + (target.length : ℤ) + (elems.length : ℤ) := rfl
      rw [hp₃]
      have hn : (0 : ℤ) < (elems.length : ℤ) := by
        dsimp [elems]
        exact_mod_cast (List.length_pos_iff_ne_nil.mpr helems_ne)
      omega
    rw [show tape3 0 = tape 0 from by
      rw [show tape3 0 = cfg2.tape 0 from by simp [tape3, hne]]
      rw [hleft2 0 (by
        rw [← hlen_tgt]
        omega)]]
    exact htape0
  · -- tape (1+target.length) = boundary
    rw [htape4]
    have hne : 1 + (target.length : ℤ) ≠ p₃ := by
      intro h
      have hh : 1 + (target.length : ℤ) = 2 + (target.length : ℤ) + (elems.length : ℤ) := by
        dsimp [p₃] at h
        exact h
      have helems_pos : (0 : ℤ) < (elems.length : ℤ) := by
        dsimp [elems]
        exact_mod_cast (List.length_pos_iff_ne_nil.mpr helems_ne)
      omega
    rw [show tape3 (1 + (target.length : ℤ)) = tape (1 + (target.length : ℤ)) from by
      rw [show tape3 (1 + (target.length : ℤ)) = cfg2.tape (1 + (target.length : ℤ)) from by simp [tape3, hne]]
      rw [hleft2 (1 + (target.length : ℤ)) (by
        rw [← hlen_tgt]
        omega)]]
    exact hbound0
  · -- 元素区（存在性 withSel）
    refine Exists.intro sel2 (And.intro hsel2_len (And.intro ?_ hsel2_eq₀))
    rw [htape4]
    rw [show (2 + ((encodeBitsSym inst.target).length : ℤ)) = p₀ from by
      dsimp [p₀, target]]
    intro i hi
    have hne : p₀ + (i : ℤ) ≠ p₃ := by
      have hp₃ : p₃ = 2 + (target.length : ℤ) + (elems.length : ℤ) := rfl
      have hp₀ : p₀ = 2 + (target.length : ℤ) := rfl
      rw [hp₃, hp₀]
      have hlen' : (encodeElementsSymWithSel inst.elements sel2).length = elems.length := by
        rw [encodeElementsSymWithSel_eq_join inst.elements sel2 hsel2_len]
        simpa [blocks', elems, Function.comp_def, List.map_map] using hlen_eq'
      have hleni : (i : ℤ) < (elems.length : ℤ) := by exact_mod_cast (Nat.lt_of_lt_of_eq hi (by
        rw [encodeElementsSymWithSel_eq_join inst.elements sel2 hsel2_len]
        simpa [blocks', elems, Function.comp_def, List.map_map] using hlen_eq'))
      dsimp [elems] at hleni ⊢
      omega
    rw [show tape3 (p₀ + (i : ℤ)) = cfg2.tape (p₀ + (i : ℤ)) from by simp [tape3, hne]]
    simpa [p₀, target] using htape_sel2 i hi
  · -- 尾部 #₁ = (boundary, true)
    rw [htape4]
    dsimp [tape3]
    rw [show (2 + ((encodeBitsSym inst.target).length : ℤ) + ((encodeElementsSym inst.elements).length : ℤ)) = p₃ from by
      dsimp [p₃, p₀]]
    simp [tape3]

/-- 状态 38 从 q 左扫到 #ₗ：每步写回、L 一格；读 #ₗ → 28 s R（28 在 target 首格）。 -/
lemma scanLeft38 (q : ℤ) (target : List Bool) (p₀ : ℤ) (tape : ℤ → Sym)
    (htarget : tapeAgrees tape (p₀ - 1 - (target.length : ℤ)) (bitsToSym target))
    (hbndL : tape (p₀ - 2 - (target.length : ℤ)) = Sym.boundary)
    (hq_mem : p₀ - 2 - (target.length : ℤ) ≤ q ∧ q ≤ p₀ - 2) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 38 tape q) π cfg' ∧
      cfg'.state = 28 ∧ cfg'.headPos = p₀ - 1 - (target.length : ℤ) ∧ cfg'.tape = tape := by
  induction target using List.reverseRecOn generalizing q p₀ tape with
  | nil =>
      -- target=[]：q = p₀ - 2 = 左边界 #ₗ，38 读 #ₗ → 28 s R
      have hq : q = p₀ - 2 := by
        have h1 : p₀ - 2 ≤ q := by simpa using hq_mem.1
        have h2 : q ≤ p₀ - 2 := hq_mem.2
        omega
      subst q
      have hbndL' : tape (p₀ - 2) = Sym.boundary := by simpa using hbndL
      let rB : SymTransResult := { nextState := 28, writeSym := Sym.boundary, moveDir := Dir.R }
      let stepB : SymStep := { fromState := 38, readSym := Sym.boundary, result := rB }
      have hcfgB : symStepConfig (SymConfig.mk 38 tape (p₀ - 2)) stepB.result = SymConfig.mk 28 tape (p₀ - 1) := by
        dsimp [symStepConfig, stepB, rB, Dir.toInt]
        congr 1
        · funext i
          by_cases h : i = p₀ - 2 <;> simp [h, hbndL']
        · omega
      have hstepB : SymSteps VerifierSym.transition (SymConfig.mk 38 tape (p₀ - 2)) [stepB]
          (SymConfig.mk 28 tape (p₀ - 1)) := by
        have hcons : SymSteps VerifierSym.transition (SymConfig.mk 38 tape (p₀ - 2)) [stepB]
            (symStepConfig (SymConfig.mk 38 tape (p₀ - 2)) stepB.result) :=
            SymSteps.cons [] stepB (SymConfig.mk 38 tape (p₀ - 2)) SymSteps.nil (by rfl) (by simp [stepB, hbndL']) (by
              unfold stepB rB
              simp [SymConfig.mk, hbndL']
              decide)
        exact hcfgB ▸ hcons
      exact ⟨[stepB], SymConfig.mk 28 tape (p₀ - 1), hstepB, rfl, by simp, rfl⟩
  | append_singleton init b ih =>
      -- target = init ++ [b]，b 是最右元素
      by_cases hb : q = p₀ - 2 - ((init ++ [b]).length : ℤ)
      · -- q 是左边界 #ₗ
        subst q
        have hbndL' : tape (p₀ - 2 - ((init ++ [b]).length : ℤ)) = Sym.boundary := by
          simpa using hbndL
        let rB : SymTransResult := { nextState := 28, writeSym := Sym.boundary, moveDir := Dir.R }
        let stepB : SymStep := { fromState := 38, readSym := Sym.boundary, result := rB }
        have hcfgB : symStepConfig (SymConfig.mk 38 tape (p₀ - 2 - ((init ++ [b]).length : ℤ))) stepB.result =
            SymConfig.mk 28 tape (p₀ - 1 - ((init ++ [b]).length : ℤ)) := by
          dsimp [symStepConfig, stepB, rB, Dir.toInt]
          congr 1
          · funext i
            by_cases h : i = p₀ - 2 - ((init ++ [b]).length : ℤ)
            · rw [h]
              rw [hbndL']
              simp
            · rw [if_neg h]
          · omega
        have hstepB : SymSteps VerifierSym.transition (SymConfig.mk 38 tape (p₀ - 2 - ((init ++ [b]).length : ℤ))) [stepB]
            (SymConfig.mk 28 tape (p₀ - 1 - ((init ++ [b]).length : ℤ))) := by
          have hcons : SymSteps VerifierSym.transition (SymConfig.mk 38 tape (p₀ - 2 - ((init ++ [b]).length : ℤ))) [stepB]
              (symStepConfig (SymConfig.mk 38 tape (p₀ - 2 - ((init ++ [b]).length : ℤ))) stepB.result) :=
              SymSteps.cons [] stepB (SymConfig.mk 38 tape (p₀ - 2 - ((init ++ [b]).length : ℤ))) SymSteps.nil (by rfl) (by
                simp [stepB]
                rw [show p₀ - 2 - ((init.length : ℤ) + 1) = p₀ - 2 - ((init ++ [b]).length : ℤ) from by
                  simp [List.length_append, List.length_singleton]]
                rw [hbndL']) (by
                unfold stepB rB
                simp [SymConfig.mk]
                rw [show p₀ - 2 - ((init.length : ℤ) + 1) = p₀ - 2 - ((init ++ [b]).length : ℤ) from by
                  simp [List.length_append, List.length_singleton]]
                rw [hbndL']
                decide)
          exact hcfgB ▸ hcons
        exact ⟨[stepB], SymConfig.mk 28 tape (p₀ - 1 - ((init ++ [b]).length : ℤ)), hstepB, rfl, by
          simp [List.length_append, List.length_singleton], rfl⟩
      · -- q 是数据位：38 读 data → 38 s L → q-1 递归 init
        have hlen : (init ++ [b]).length = init.length + 1 := by simp
        have hq_mem' : (p₀ - 1) - 2 - (init.length : ℤ) ≤ q - 1 ∧ q - 1 ≤ (p₀ - 1) - 2 := by
          constructor
          · rw [hlen] at hq_mem
            omega
          · have hle : q ≤ p₀ - 2 := hq_mem.2
            omega
        have htarget' : tapeAgrees tape ((p₀ - 1) - 1 - (init.length : ℤ)) (bitsToSym init) := by
          intro j hj
          have hj' : j < (bitsToSym (init ++ [b])).length := by
            unfold bitsToSym at hj
            simp only [List.length_map] at hj
            unfold bitsToSym
            simp only [List.length_map]
            rw [hlen]
            omega
          have h := htarget j hj'
          rw [show p₀ - 1 - ((init ++ [b]).length : ℤ) + (j : ℤ) = (p₀ - 1) - 1 - (init.length : ℤ) + (j : ℤ) from by
            simp [hlen]
            omega] at h
          rw [show (bitsToSym (init ++ [b]))[j]'(hj') = (bitsToSym init)[j]'(hj) from by
            unfold bitsToSym at hj
            simp only [List.length_map] at hj
            unfold bitsToSym
            simp [List.getElem_append, hj, List.getElem_map]] at h
          exact h
        have hbndL' : tape ((p₀ - 1) - 2 - (init.length : ℤ)) = Sym.boundary := by
          rw [show p₀ - 2 - ((init ++ [b]).length : ℤ) = (p₀ - 1) - 2 - (init.length : ℤ) from by
            simp [hlen]
            omega] at hbndL
          exact hbndL
        let idx := (q - (p₀ - 1 - ((init ++ [b]).length : ℤ))).toNat
        have htp : (tape q).1 = SymKind.data0 ∨ (tape q).1 = SymKind.data1 := by
          have hget := htarget (idx) (by
            rw [show (bitsToSym (init ++ [b])).length = (init ++ [b]).length from by
              unfold bitsToSym
              simp [List.length_map, List.length_append, List.length_singleton]]
            rw [hlen]
            omega)
          have hidx : p₀ - 1 - ((init ++ [b]).length : ℤ) + (idx : ℤ) = q := by
            dsimp [idx]
            rw [Int.toNat_of_nonneg]
            · omega
            · have h1 : p₀ - 2 - ((init ++ [b]).length : ℤ) ≤ q := hq_mem.1
              omega
          rw [← hidx]
          rw [hget]
          have hidx_valid : idx < (bitsToSym (init ++ [b])).length := by
            dsimp [idx]
            rw [show (bitsToSym (init ++ [b])).length = (init ++ [b]).length from by
              unfold bitsToSym
              simp [List.length_map, List.length_append, List.length_singleton]]
            have hle : q ≤ p₀ - 2 := hq_mem.2
            have hge : p₀ - 1 - ((init ++ [b]).length : ℤ) ≤ q := by
              have h1 : p₀ - 2 - ((init ++ [b]).length : ℤ) ≤ q := hq_mem.1
              omega
            have hnn : 0 ≤ q - (p₀ - 1 - ((init ++ [b]).length : ℤ)) := by
              have h1 : p₀ - 2 - ((init ++ [b]).length : ℤ) ≤ q := hq_mem.1
              omega
            simp [Int.toNat_of_nonneg hnn, hlen]
            omega
          have hmem : (bitsToSym (init ++ [b]))[idx]'hidx_valid ∈ bitsToSym (init ++ [b]) := List.getElem_mem (by
            simpa using hidx_valid)
          exact bitsToSym_data (init ++ [b]) ((bitsToSym (init ++ [b]))[idx]'hidx_valid) hmem
        have hms38 : (tape q).2 = false := by
          have hget := htarget (idx) (by
            rw [show (bitsToSym (init ++ [b])).length = (init ++ [b]).length from by
              unfold bitsToSym
              simp [List.length_map, List.length_append, List.length_singleton]]
            rw [hlen]
            omega)
          have hidx : p₀ - 1 - ((init ++ [b]).length : ℤ) + (idx : ℤ) = q := by
            dsimp [idx]
            rw [Int.toNat_of_nonneg]
            · omega
            · have h1 : p₀ - 2 - ((init ++ [b]).length : ℤ) ≤ q := hq_mem.1
              omega
          rw [← hidx]
          rw [hget]
          have hidx_valid : idx < (bitsToSym (init ++ [b])).length := by
            dsimp [idx]
            rw [show (bitsToSym (init ++ [b])).length = (init ++ [b]).length from by
              unfold bitsToSym
              simp [List.length_map, List.length_append, List.length_singleton]]
            have hle : q ≤ p₀ - 2 := hq_mem.2
            have hge : p₀ - 1 - ((init ++ [b]).length : ℤ) ≤ q := by
              have h1 : p₀ - 2 - ((init ++ [b]).length : ℤ) ≤ q := hq_mem.1
              omega
            have hnn : 0 ≤ q - (p₀ - 1 - ((init ++ [b]).length : ℤ)) := by
              have h1 : p₀ - 2 - ((init ++ [b]).length : ℤ) ≤ q := hq_mem.1
              omega
            simp [Int.toNat_of_nonneg hnn, hlen]
            omega
          have hmem : (bitsToSym (init ++ [b]))[idx]'hidx_valid ∈ bitsToSym (init ++ [b]) := List.getElem_mem (by
            simpa using hidx_valid)
          exact bitsToSym_marks (init ++ [b]) ((bitsToSym (init ++ [b]))[idx]'hidx_valid) hmem
        let r38 : SymTransResult := { nextState := 38, writeSym := tape q, moveDir := Dir.L }
        let step38 : SymStep := { fromState := 38, readSym := tape q, result := r38 }
        have htrans38 : step38.result ∈ VerifierSym.transition (38, tape q) := by
          rcases htpq : tape q with ⟨ks, ms⟩
          rcases htp with hk0 | hk1
          · have hk0' : ks = SymKind.data0 := by simpa [htpq] using hk0
            subst ks
            have hms' : ms = false := by simpa [htpq] using hms38
            subst ms
            simp [step38, r38, htpq]
            decide
          · have hk1' : ks = SymKind.data1 := by simpa [htpq] using hk1
            subst ks
            have hms' : ms = false := by simpa [htpq] using hms38
            subst ms
            simp [step38, r38, htpq]
            decide
        have hcfg38 : symStepConfig (SymConfig.mk 38 tape q) step38.result = SymConfig.mk 38 tape (q - 1) := by
          dsimp [symStepConfig, step38, r38, Dir.toInt]
          congr 1
          · funext i
            by_cases h : i = q <;> simp [h]
        have hstep38 : SymSteps VerifierSym.transition (SymConfig.mk 38 tape q) [step38] (SymConfig.mk 38 tape (q - 1)) := by
          have hcons : SymSteps VerifierSym.transition (SymConfig.mk 38 tape q) [step38]
              (symStepConfig (SymConfig.mk 38 tape q) step38.result) :=
              SymSteps.cons [] step38 (SymConfig.mk 38 tape q) SymSteps.nil (by rfl) (by simp [step38]) htrans38
          exact hcfg38 ▸ hcons
        rcases ih (q - 1) (p₀ - 1) tape htarget' hbndL' hq_mem' with ⟨π', cfg', hπ', hs', hhead', htape'⟩
        refine ⟨[step38] ++ π', cfg', ?_, hs', ?_, ?_⟩
        · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 38 tape q) (SymConfig.mk 38 tape (q - 1)) cfg' [step38] π' hstep38 hπ'
        · rw [hhead']
          simp [List.length_append, List.length_singleton]
          omega
        · exact htape'

/-- 状态 28 从 target 首格右扫回：每步写回、R 一格；读 #₀ → 4 s R（4 在 #₀ 右侧）。 -/
lemma scanRight28 (target : List Bool) (p₀ : ℤ) (tape : ℤ → Sym)
    (htarget : tapeAgrees tape (p₀ - 1 - (target.length : ℤ)) (bitsToSym target))
    (hbnd₀ : tape (p₀ - 1) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1 - (target.length : ℤ))) π cfg' ∧
      cfg'.state = 4 ∧ cfg'.headPos = p₀ ∧ cfg'.tape = tape := by
  induction target generalizing p₀ tape with
  | nil =>
      -- 28 读 #₀ → 4 s R
      have hbnd₀' : tape (p₀ - 1) = Sym.boundary := by simpa using hbnd₀
      let rB : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
      let stepB : SymStep := { fromState := 28, readSym := Sym.boundary, result := rB }
      have hstepB : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1 - ([] : List Bool).length)) [stepB]
          (symStepConfig (SymConfig.mk 28 tape (p₀ - 1 - ([] : List Bool).length)) stepB.result) := by
        refine SymSteps.cons [] stepB (SymConfig.mk 28 tape (p₀ - 1 - ([] : List Bool).length)) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change Sym.boundary = tape (p₀ - 1 - ([] : List Bool).length)
          rw [show p₀ - 1 - ([] : List Bool).length = p₀ - 1 from by simp]
          rw [hbnd₀']
        · change stepB.result ∈ VerifierSym.transition (28, tape (p₀ - 1 - ([] : List Bool).length))
          rw [show p₀ - 1 - ([] : List Bool).length = p₀ - 1 from by simp]
          rw [hbnd₀']
          decide
      have hcfgB : symStepConfig (SymConfig.mk 28 tape (p₀ - 1 - ([] : List Bool).length)) stepB.result = SymConfig.mk 4 tape p₀ := by
        dsimp [symStepConfig, stepB, rB, Dir.toInt]
        congr 1
        · funext i
          by_cases h : i = p₀ - 1 <;> simp [h, hbnd₀']
        · omega
      refine ⟨[stepB], SymConfig.mk 4 tape p₀, hcfgB ▸ hstepB, rfl, ?_, ?_⟩
      · rfl
      · rfl
  | cons b rest ih =>
      have hfirst : tape (p₀ - 1 - ((b :: rest).length : ℤ)) = (bitsToSym (b :: rest))[0]'(by simp) := by
        have h := htarget 0 (by simp)
        simpa [List.length_cons, show p₀ - 1 - ((b :: rest).length : ℤ) + (0 : ℤ) = p₀ - 1 - ((b :: rest).length : ℤ) from by simp] using h
      let r28 : SymTransResult := { nextState := 28, writeSym := tape (p₀ - 1 - ((b :: rest).length : ℤ)), moveDir := Dir.R }
      let step28 : SymStep := { fromState := 28, readSym := tape (p₀ - 1 - ((b :: rest).length : ℤ)), result := r28 }
      have htrans28 : step28.result ∈ VerifierSym.transition (28, tape (p₀ - 1 - ((b :: rest).length : ℤ))) := by
        rcases htp : tape (p₀ - 1 - ((b :: rest).length : ℤ)) with ⟨ks, ms⟩
        have hmem : (ks, ms) ∈ bitsToSym (b :: rest) := by
          rw [← htp]
          rw [hfirst]
          exact List.getElem_mem (by simp [bitsToSym])
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          have h := bitsToSym_data (b :: rest) (ks, ms) hmem
          simpa using h
        rcases hks with h | h
        · subst ks
          cases ms
          · simp [step28, r28]
            rw [show p₀ - 1 - (↑rest.length + 1) = p₀ - 1 - ↑(b :: rest).length from by simp [List.length_cons]]
            rw [htp]
            decide
          · simp [step28, r28]
            rw [show p₀ - 1 - (↑rest.length + 1) = p₀ - 1 - ↑(b :: rest).length from by simp [List.length_cons]]
            rw [htp]
            decide
        · subst ks
          cases ms
          · simp [step28, r28]
            rw [show p₀ - 1 - (↑rest.length + 1) = p₀ - 1 - ↑(b :: rest).length from by simp [List.length_cons]]
            rw [htp]
            decide
          · simp [step28, r28]
            rw [show p₀ - 1 - (↑rest.length + 1) = p₀ - 1 - ↑(b :: rest).length from by simp [List.length_cons]]
            rw [htp]
            decide
      have hcfg28 : symStepConfig (SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ))) step28.result =
          SymConfig.mk 28 tape (p₀ - (b :: rest).length) := by
        dsimp [symStepConfig, step28, r28, Dir.toInt]
        congr 1
        · funext i
          by_cases h : i = p₀ - 1 - ((b :: rest).length : ℤ)
          · rw [h]
            simp
          · rw [if_neg (show i ≠ p₀ - 1 - (↑rest.length + 1) from by
              simpa [List.length_cons] using h)]
        · omega
      have hstep28_raw : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ))) [step28]
          (symStepConfig (SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ))) step28.result) := by
        refine SymSteps.cons [] step28 (SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ))) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans28
      have hstep28 : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ))) [step28]
          (SymConfig.mk 28 tape (p₀ - (b :: rest).length)) := by
        rw [← hcfg28]; exact hstep28_raw
      by_cases hrest : rest = []
      · subst rest
        -- 28 在 p₀ - 1 读 #₀ → 4 s R
        let rB : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
        let stepB : SymStep := { fromState := 28, readSym := Sym.boundary, result := rB }
        have htransB : stepB.result ∈ VerifierSym.transition (28, Sym.boundary) := by decide
        have hbnd₀' : tape (p₀ - 1) = Sym.boundary := by
          have h := hbnd₀
          simpa [show p₀ - (b :: []).length = p₀ - 1 from by simp] using h
        have hcfgB : symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) stepB.result = SymConfig.mk 4 tape p₀ := by
          dsimp [symStepConfig, stepB, rB, Dir.toInt]
          congr 1
          · funext i
            by_cases h : i = p₀ - 1
            · rw [h]
              rw [hbnd₀']
              simp
            · rw [if_neg h]
          · omega
        have hstepB_raw : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1)) [stepB]
            (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) stepB.result) := by
          refine SymSteps.cons [] stepB (SymConfig.mk 28 tape (p₀ - 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.boundary = tape (p₀ - 1)
            rw [hbnd₀']
          · change stepB.result ∈ VerifierSym.transition (28, tape (p₀ - 1))
            rw [hbnd₀']
            decide
        have hstepB : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1)) [stepB] (SymConfig.mk 4 tape p₀) := by
          rw [← hcfgB]; exact hstepB_raw
        refine ⟨[step28] ++ [stepB], SymConfig.mk 4 tape p₀, ?_, rfl, ?_, ?_⟩
        · refine SymSteps_trans VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1 - ((b :: []).length : ℤ))) (SymConfig.mk 28 tape (p₀ - 1)) (SymConfig.mk 4 tape p₀) [step28] [stepB] ?_ hstepB
          · simpa [show p₀ - (b :: []).length = p₀ - 1 from by simp] using hstep28
        · rfl
        · rfl
      · rcases ih p₀ tape (by
            intro i hi
            have h := htarget (i + 1) (by
              unfold bitsToSym at hi
              simp at hi
              unfold bitsToSym
              simp
              omega)
            have hidx : p₀ - 1 - ((b :: rest).length : ℤ) + ((i + 1 : ℕ) : ℤ) = p₀ - 1 - (rest.length : ℤ) + (i : ℤ) := by
              simp only [List.length_cons]
              omega
            rw [hidx] at h
            simpa [bitsToSym, List.getElem_cons_succ] using h
          ) hbnd₀ with ⟨π', cfg', hπ', hs', hhead', htape'⟩
        refine ⟨[step28] ++ π', cfg', ?_, hs', ?_, ?_⟩
        · have : p₀ - (b :: rest).length = p₀ - 1 - (rest.length : ℤ) := by simp [List.length_cons]; omega
          rw [this] at hstep28
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ))) (SymConfig.mk 28 tape (p₀ - 1 - (rest.length : ℤ))) cfg' [step28] π' hstep28 hπ'
        · rw [hhead']
        · exact htape'


/-- 状态 27（在 target 末位 p₀-2）→ 38 左扫 target 到 #ₗ → 28 右扫回 → 4（在 #₀ 右侧 p₀）。磁带不变。 -/
lemma scanLeft27_target (target : List Bool) (p₀ : ℤ) (tape : ℤ → Sym)
    (hne : target ≠ [])
    (htop : target[target.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hne) (by norm_num)) = true)
    (htarget : tapeAgrees tape (p₀ - 1 - (target.length : ℤ)) (bitsToSym target))
    (hbndL : tape (p₀ - 2 - (target.length : ℤ)) = Sym.boundary)
    (hbnd₀ : tape (p₀ - 1) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) π cfg' ∧
      cfg'.state = 4 ∧ cfg'.headPos = p₀ ∧ cfg'.tape = tape := by
  cases target with
  | nil => exfalso; exact hne rfl
  | cons b rest =>
      have hlast : tape (p₀ - 2) = (bitsToSym (b :: rest))[rest.length]'(by simp [bitsToSym]) := by
        have h := htarget rest.length (by simp [bitsToSym])
        have hidx : p₀ - 1 - ((b :: rest).length : ℤ) + (rest.length : ℤ) = p₀ - 2 := by
          simp [List.length_cons]
          omega
        rw [hidx] at h
        exact h
      have hkind : (tape (p₀ - 2)).1 = SymKind.data0 ∨ (tape (p₀ - 2)).1 = SymKind.data1 := by
        rw [hlast]
        have hmem : (bitsToSym (b :: rest))[rest.length]'(by simp [bitsToSym]) ∈ bitsToSym (b :: rest) := List.getElem_mem (by simp [bitsToSym])
        exact bitsToSym_data (b :: rest) ((bitsToSym (b :: rest))[rest.length]'(by simp [bitsToSym])) hmem
      let r27 : SymTransResult := { nextState := 38, writeSym := tape (p₀ - 2), moveDir := Dir.L }
      let step27 : SymStep := { fromState := 27, readSym := tape (p₀ - 2), result := r27 }
      have htrans27 : step27.result ∈ VerifierSym.transition (27, tape (p₀ - 2)) := by
        rcases htp : tape (p₀ - 2) with ⟨ks, ms⟩
        have hmem : (ks, ms) ∈ bitsToSym (b :: rest) := by
          rw [← htp]
          rw [hlast]
          exact List.getElem_mem (by simp [bitsToSym])
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          have h := bitsToSym_data (b :: rest) (ks, ms) hmem
          simpa using h
        have hms : ms = false := by
          have h := bitsToSym_marks (b :: rest) (ks, ms) hmem
          simpa using h
        rcases hks with hk | hk
        · -- data0：与 htop（target 最高位 true → 末位 data1）矛盾
          subst ks
          subst ms
          have hb_last : (bitsToSym (b :: rest))[rest.length]'(by simp [bitsToSym]) = Sym.data1 := by
            unfold bitsToSym
            rw [List.getElem_map]
            have hlast_true : (b :: rest)[rest.length]'(by simp) = true := by
              have hlen : (b :: rest).length - 1 = rest.length := by simp
              simpa [hlen] using htop
            simp [hlast_true]
          have hb1 : tape (p₀ - 2) = Sym.data1 := by
            rw [hlast]
            exact hb_last
          have hb0 : tape (p₀ - 2) = Sym.data0 := by
            simpa [Sym.data0, Sym.mk] using htp
          have : Sym.data0 = Sym.data1 := by
            rw [← hb1, hb0]
          cases this
        · subst ks
          subst ms
          simp [step27, r27, htp]
          decide
      have hcfg27 : symStepConfig (SymConfig.mk 27 tape (p₀ - 2)) step27.result = SymConfig.mk 38 tape (p₀ - 3) := by
        dsimp [symStepConfig, step27, r27, Dir.toInt]
        congr 1
        · funext i
          by_cases h : i = p₀ - 2 <;> simp [h]
        · omega
      have hstep27_raw : SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) [step27]
          (symStepConfig (SymConfig.mk 27 tape (p₀ - 2)) step27.result) := by
        refine SymSteps.cons [] step27 (SymConfig.mk 27 tape (p₀ - 2)) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans27
      have hstep27 : SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) [step27] (SymConfig.mk 38 tape (p₀ - 3)) := by
        rw [← hcfg27]; exact hstep27_raw
      rcases scanLeft38 (p₀ - 3) (b :: rest) p₀ tape (by simpa using htarget) (by simpa using hbndL) (by
        constructor
        · have hlen : 1 ≤ (b :: rest).length := by simp
          omega
        · omega) with ⟨π38, cfg38, hπ38, hs38, hhead38, htape38⟩
      have hstart : cfg38 = SymConfig.mk 28 tape (p₀ - 1 - ((b :: rest).length : ℤ)) := by
        cases cfg38 with
        | mk s t hp =>
            have hs' : s = 28 := by simpa [SymConfig.mk] using hs38
            have hp' : hp = p₀ - 1 - ((b :: rest).length : ℤ) := by simpa [SymConfig.mk] using hhead38
            subst s
            rw [hp']
            rw [show t = tape from by simpa [SymConfig.mk] using htape38]
      rcases scanRight28 (b :: rest) p₀ tape (by simpa using htarget) hbnd₀ with ⟨π28, cfg4, hπ28, hs4, hhead4, htape4⟩
      refine ⟨[step27] ++ π38 ++ π28, cfg4, ?_, hs4, ?_, ?_⟩
      · have h1 : SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) ([step27] ++ π38) cfg38 := by
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) (SymConfig.mk 38 tape (p₀ - 3)) cfg38 [step27] π38 hstep27 hπ38
        have h2 : SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) ([step27] ++ π38 ++ π28) cfg4 := by
          rw [← hstart] at hπ28
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) cfg38 cfg4 ([step27] ++ π38) π28 h1 hπ28
        exact h2
      · rw [hhead4]
      · exact htape4






/-- 状态 76 读 consumed/data0/data1：写回自身左移。 -/

lemma clear_counter_correct (tbits ebits : List Bool) (p_t p_e : ℤ) (tape : ℤ → Sym)
    (hebits_pos : 1 ≤ ebits.length)
    (hlen_le : ebits.length ≤ tbits.length)
    (hp_t_le : p_t + (tbits.length : ℤ) ≤ p_e)
    (htarget : tapeAgrees tape p_t (targetTape ebits.length (subAllBits tbits ebits)))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hhashL : tape (p_t - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel0 : tape p_e = Sym.data0)
    (hconsumed : ∀ i : ℕ, i < ebits.length → tape (p_e + 1 + (i : ℤ)) = Sym.consumed) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) π cfg' ∧
      cfg'.state = 20 ∧ cfg'.headPos = p_e - 1 ∧
      tapeAgrees cfg'.tape p_t (targetTape 0 (subAllBits tbits ebits)) ∧
      cfg'.tape (p_e - 1) = Sym.boundary ∧
      cfg'.tape (p_t - 1) = Sym.boundary ∧
      cfg'.tape p_e = Sym.data0 ∧
      (∀ i : ℕ, i < ebits.length → cfg'.tape (p_e + 1 + (i : ℤ)) = Sym.consumed) ∧
      (∀ i : ℤ, p_e + (ebits.length : ℤ) < i → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e → cfg'.tape i = tape i) := by
  -- p_t + tbits.length < p_e（元素标记在旧 #₀ 之外）
  have hp_t_lt : p_t + (tbits.length : ℤ) < p_e := by
    by_cases h : p_t + (tbits.length : ℤ) < p_e
    · exact h
    · exfalso
      have hpe' : p_e = p_t + (tbits.length : ℤ) := by omega
      have hk1_lt : tbits.length - 1 < tbits.length := by omega
      have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
        simp [targetTape_length, subAllBits_length]
      have hk1 : tbits.length - 1 < (targetTape ebits.length (subAllBits tbits ebits)).length := by rw [hlen]; exact hk1_lt
      have ht : tape (p_t + ((tbits.length - 1 : ℕ) : ℤ)) = (targetTape ebits.length (subAllBits tbits ebits))[tbits.length - 1]'hk1 := htarget (tbits.length - 1) hk1
      have hmem : (targetTape ebits.length (subAllBits tbits ebits))[tbits.length - 1]'hk1 ∈ targetTape ebits.length (subAllBits tbits ebits) := List.getElem_mem hk1
      have hnb : ((targetTape ebits.length (subAllBits tbits ebits))[tbits.length - 1]'hk1).1 ≠ SymKind.boundary :=
        targetTape_nonboundary ebits.length (subAllBits tbits ebits) _ hmem
      have hpos : p_e - 1 = p_t + ((tbits.length - 1 : ℕ) : ℤ) := by
        rw [hpe']
        omega
      rw [hpos] at hbound
      rw [ht] at hbound
      exact hnb (by simpa [Sym.boundary] using congrArg (fun s : Sym => s.1) hbound)
  -- (a) 状态 84 左移穿过 consumed 值位 + sel 标记（data0），到 #₀ 转 85
  have hnb₈₄ : ∀ i : ℤ, p_e + (ebits.length : ℤ) - ((ebits.length + 1 : ℕ) : ℤ) < i ∧ i ≤ p_e + (ebits.length : ℤ) → (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i h
    have hi : p_e ≤ i ∧ i ≤ p_e + (ebits.length : ℤ) := by constructor <;> omega
    by_cases heq : i = p_e
    · subst i
      rw [hsel0]
      right; left; rfl
    · have ioff : ∃ io : ℕ, (io : ℤ) = i - (p_e + 1) := by
        refine ⟨(i - (p_e + 1)).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p_e + 1))
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < ebits.length := by omega
      have ht := hconsumed io hio_lt
      have hidx : p_e + 1 + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [ht]
      left; rfl
  have hbound₈₄ : tape (p_e + (ebits.length : ℤ) - ((ebits.length + 1 : ℕ) : ℤ)) = Sym.boundary := by
    have hpos : p_e + (ebits.length : ℤ) - ((ebits.length + 1 : ℕ) : ℤ) = p_e - 1 := by omega
    rw [hpos]
    exact hbound
  have hend₈₄ : { nextState := 85, writeSym := Sym.boundary, moveDir := Dir.L } ∈ VerifierSym.transition (84, Sym.boundary) := by
    decide
  rcases scanLeftKeepP 84 85 Sym.boundary Dir.L (ebits.length + 1) (p_e + (ebits.length : ℤ)) tape
      (fun s : Sym => s.1 = SymKind.consumed ∨ s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
      hnb₈₄ hbound₈₄ trans84_keep hend₈₄ rfl with ⟨π₁, cfg₁, hπ₁, hs₁, hhead₁, htape₁⟩
  -- (b) 状态 85 左移到 #ₗ（穿过 target 区 + data0 填充）→ 86
  let n₈₅ : ℕ := (p_e - p_t - 1).toNat
  have hn₈₅ : (n₈₅ : ℤ) = p_e - p_t - 1 := by
    change ((p_e - p_t - 1).toNat : ℤ) = p_e - p_t - 1
    exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - 1)
  have hnb₈₅ : ∀ i : ℤ, (p_e - 2) - (n₈₅ : ℤ) < i ∧ i ≤ p_e - 2 → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i h
    rw [hn₈₅] at h
    have hi : p_t ≤ i ∧ i < p_e - 1 := by constructor <;> omega
    by_cases hlt_target : i < p_t + (tbits.length : ℤ)
    · -- target 位
      have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
        refine ⟨(i - p_t).toNat, ?_⟩
        exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
      rcases ioff with ⟨io, hio⟩
      have hio_lt : io < (targetTape ebits.length (subAllBits tbits ebits)).length := by
        have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
          simp [targetTape_length, subAllBits_length]
        rw [hlen]
        omega
      have ht := htarget io hio_lt
      have hd_io : ((targetTape ebits.length (subAllBits tbits ebits))[io]).1 = SymKind.data0 ∨ ((targetTape ebits.length (subAllBits tbits ebits))[io]).1 = SymKind.data1 := by
        have hmem : (targetTape ebits.length (subAllBits tbits ebits))[io] ∈ targetTape ebits.length (subAllBits tbits ebits) := List.getElem_mem hio_lt
        exact targetTape_data ebits.length (subAllBits tbits ebits) _ hmem
      have hidx : p_t + (io : ℤ) = i := by omega
      rw [hidx] at ht
      rw [ht]
      exact hd_io
    · -- data0 填充
      have hpad_i := hpad i (by constructor <;> omega)
      rw [hpad_i]
      left; rfl
  have hbound₈₅ : tape ((p_e - 2) - (n₈₅ : ℤ)) = Sym.boundary := by
    have hpos : (p_e - 2) - (n₈₅ : ℤ) = p_t - 1 := by rw [hn₈₅]; omega
    rw [hpos]
    exact hhashL
  have hend₈₅ : { nextState := 86, writeSym := Sym.boundary, moveDir := Dir.R } ∈ VerifierSym.transition (85, Sym.boundary) := by
    decide
  rcases scanLeftKeepP 85 86 Sym.boundary Dir.R n₈₅ (p_e - 2) tape
      (fun s : Sym => s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
      hnb₈₅ hbound₈₅ trans85_keep hend₈₅ rfl with ⟨π₂, cfg₂, hπ₂, hs₂, hhead₂, htape₂⟩
  -- (c) 状态 86 右移清 target 区低 ebits.length 格 4F4.4（m=1 → m=0），停在第 ebits.length+1 格（m=0）
  have hmarked : ∀ i : ℕ, i < ebits.length → (tape (p_t + (i : ℤ))).2 = true := by
    intro i hi
    have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
      simp [targetTape_length, subAllBits_length]
    have ht := htarget i (by rw [hlen]; exact lt_of_lt_of_le hi hlen_le)
    rw [ht]
    rw [targetTape_getElem_lt ebits.length i (subAllBits tbits ebits) (by simpa [subAllBits_length] using lt_of_lt_of_le hi hlen_le) hi]
    by_cases hb : (subAllBits tbits ebits)[i]'(by simpa [subAllBits_length] using lt_of_lt_of_le hi hlen_le) <;> simp [hb, Sym.data1, Sym.data0, Sym.mk]
  have hstop : (tape (p_t + (ebits.length : ℤ))).2 = false := by
    by_cases heq : p_t + (ebits.length : ℤ) = p_e - 1
    · rw [heq, hbound]
      simp [Sym.boundary, Sym.mk]
    · by_cases hlt : ebits.length < tbits.length
      · have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
          simp [targetTape_length, subAllBits_length]
        have ht := htarget ebits.length (by rw [hlen]; exact hlt)
        rw [ht]
        have hnth := targetTape_nth_eq_if ebits.length (subAllBits tbits ebits) (by simpa [subAllBits_length] using hlt)
        have h3 := congrArg (fun s : Sym => s.2) hnth
        by_cases hb : (subAllBits tbits ebits)[ebits.length]'(by simpa [subAllBits_length] using hlt) = true
        · simpa [h3, hb, Sym.data1]
        · simpa [h3, hb, Sym.data0]
      · have heq_len : ebits.length = tbits.length := by omega
        have hd : tape (p_t + (ebits.length : ℤ)) = Sym.data0 :=
          hpad (p_t + (ebits.length : ℤ)) (by constructor <;> omega)
        rw [hd]
        simp [Sym.data0, Sym.mk]
  have hdata₈₆ : ∀ i : ℤ, p_t ≤ i ∧ i < p_t + (ebits.length : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
    intro i hi
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
      refine ⟨(i - p_t).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < (targetTape ebits.length (subAllBits tbits ebits)).length := by
      have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
        simp [targetTape_length, subAllBits_length]
      rw [hlen]
      omega
    have ht := htarget io hio_lt
    have hd_io : ((targetTape ebits.length (subAllBits tbits ebits))[io]).1 = SymKind.data0 ∨ ((targetTape ebits.length (subAllBits tbits ebits))[io]).1 = SymKind.data1 := by
      have hmem : (targetTape ebits.length (subAllBits tbits ebits))[io] ∈ targetTape ebits.length (subAllBits tbits ebits) := List.getElem_mem hio_lt
      exact targetTape_data ebits.length (subAllBits tbits ebits) _ hmem
    have hidx : p_t + (io : ℤ) = i := by omega
    rw [hidx] at ht
    rw [ht]
    exact hd_io
  have hdata_stop₈₆ : (tape (p_t + (ebits.length : ℤ))).1 = SymKind.data0 ∨ (tape (p_t + (ebits.length : ℤ))).1 = SymKind.data1 ∨
      (tape (p_t + (ebits.length : ℤ))).1 = SymKind.boundary := by
    by_cases heq : p_t + (ebits.length : ℤ) = p_e - 1
    · right; right
      rw [heq, hbound]
      rfl
    · by_cases hlt : ebits.length < tbits.length
      · have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
          simp [targetTape_length, subAllBits_length]
        have ht := htarget ebits.length (by rw [hlen]; exact hlt)
        rw [ht]
        have hmem : (targetTape ebits.length (subAllBits tbits ebits))[ebits.length]'(by rw [hlen]; exact hlt) ∈
            targetTape ebits.length (subAllBits tbits ebits) := List.getElem_mem (by rw [hlen]; exact hlt)
        have hd01 := targetTape_data ebits.length (subAllBits tbits ebits) _ hmem
        rcases hd01 with hd0 | hd1
        · left; exact hd0
        · right; left; exact hd1
      · have heq_len : ebits.length = tbits.length := by omega
        left
        have hd : tape (p_t + (ebits.length : ℤ)) = Sym.data0 :=
          hpad (p_t + (ebits.length : ℤ)) (by constructor <;> omega)
        rw [hd]
        rfl
  rcases clearMark86 ebits.length p_t tape hmarked hstop hdata₈₆ hdata_stop₈₆ with ⟨π₃, cfg₃, hπ₃, hs₃, hhead₃, hclear₃, hstop₃, hleft₃, hright₃⟩
  -- (d) 状态 87 右移到 #₀ → 20
  let n₈₇ : ℕ := (p_e - p_t - (ebits.length : ℤ) - 1).toNat
  have hn₈₇ : (n₈₇ : ℤ) = p_e - p_t - (ebits.length : ℤ) - 1 := by
    change ((p_e - p_t - (ebits.length : ℤ) - 1).toNat : ℤ) = p_e - p_t - (ebits.length : ℤ) - 1
    exact Int.toNat_of_nonneg (by omega : 0 ≤ p_e - p_t - (ebits.length : ℤ) - 1)
  have hdata₈₇ : ∀ i : ℤ, p_t + (ebits.length : ℤ) ≤ i ∧ i < p_t + (ebits.length : ℤ) + (n₈₇ : ℤ) → (cfg₃.tape i).1 = SymKind.data0 ∨ (cfg₃.tape i).1 = SymKind.data1 := by
    intro i hi
    by_cases heq : i = p_t + (ebits.length : ℤ)
    · subst i
      rw [hstop₃]
      by_cases hb : p_t + (ebits.length : ℤ) = p_e - 1
      · exfalso
        have hn₈₇_pos : 0 < (n₈₇ : ℤ) := by omega
        rw [hn₈₇] at hn₈₇_pos
        omega
      · by_cases hlt : ebits.length < tbits.length
        · have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
            simp [targetTape_length, subAllBits_length]
          have ht := htarget ebits.length (by rw [hlen]; exact hlt)
          rw [ht]
          have hmem : (targetTape ebits.length (subAllBits tbits ebits))[ebits.length]'(by rw [hlen]; exact hlt) ∈
              targetTape ebits.length (subAllBits tbits ebits) := List.getElem_mem (by rw [hlen]; exact hlt)
          simpa using (targetTape_data ebits.length (subAllBits tbits ebits) _ hmem)
        · have hd : tape (p_t + (ebits.length : ℤ)) = Sym.data0 :=
            hpad (p_t + (ebits.length : ℤ)) (by constructor <;> omega)
          rw [hd]
          decide
    · rw [hright₃ i (by omega)]
      by_cases hlt : i < p_t + (tbits.length : ℤ)
      · -- target 高位区（未被 clearMark 扫过的部分：保持原样，data0/data1）
        have ioff : ∃ io : ℕ, (io : ℤ) = i - p_t := by
          refine ⟨(i - p_t).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p_t)
        rcases ioff with ⟨io, hio⟩
        have hio_lt : io < (targetTape ebits.length (subAllBits tbits ebits)).length := by
          have hlen : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
            simp [targetTape_length, subAllBits_length]
          rw [hlen]
          omega
        have ht := htarget io hio_lt
        have hd_io : ((targetTape ebits.length (subAllBits tbits ebits))[io]).1 = SymKind.data0 ∨ ((targetTape ebits.length (subAllBits tbits ebits))[io]).1 = SymKind.data1 := by
          have hmem : (targetTape ebits.length (subAllBits tbits ebits))[io] ∈ targetTape ebits.length (subAllBits tbits ebits) := List.getElem_mem hio_lt
          exact targetTape_data ebits.length (subAllBits tbits ebits) _ hmem
        have hidx : p_t + (io : ℤ) = i := by omega
        rw [hidx] at ht
        rw [ht]
        exact hd_io
      · have hidx : i < p_e - 1 := by rw [hn₈₇] at hi; omega
        have hd : tape i = Sym.data0 := hpad i ⟨by omega, hidx⟩
        rw [hd]
        decide
  have hbound₈₇ : cfg₃.tape (p_t + (ebits.length : ℤ) + (n₈₇ : ℤ)) = Sym.boundary := by
    have hpos : p_t + (ebits.length : ℤ) + (n₈₇ : ℤ) = p_e - 1 := by rw [hn₈₇]; omega
    rw [hpos]
    by_cases heq : p_e - 1 = p_t + (ebits.length : ℤ)
    · rw [heq]
      rw [hstop₃]
      rw [heq] at hbound
      exact hbound
    · rw [hright₃ (p_e - 1) (by omega), hbound]
  rcases scanRight87 n₈₇ (p_t + (ebits.length : ℤ)) cfg₃.tape hdata₈₇ hbound₈₇ with ⟨π₄, cfg₄, hπ₄, hs₄, hhead₄, htape₄⟩
  -- 组装路径
  have hcfg₁_eq : cfg₁ = SymConfig.mk 85 tape (p_e - 2) := by
    rcases hcfg : cfg₁ with ⟨s, t, hp⟩
    have hs' : s = 85 := by simpa [hcfg] using hs₁
    have ht' : t = tape := by simpa [hcfg] using htape₁
    have hp' : hp = p_e - 2 := by
      have hh : hp = cfg₁.headPos := by simpa [hcfg]
      rw [hh, hhead₁]
      simp [Dir.toInt]
      omega
    subst s; subst t; subst hp
    rfl
  have hπ₂' : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
    rw [hcfg₁_eq]; exact hπ₂
  have h₁₂ : SymSteps VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) (π₁ ++ π₂) cfg₂ :=
    SymSteps_trans VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) cfg₁ cfg₂ π₁ π₂ hπ₁ hπ₂'
  have hcfg₂_eq : cfg₂ = SymConfig.mk 86 tape p_t := by
    rcases hcfg : cfg₂ with ⟨s, t, hp⟩
    have hs' : s = 86 := by simpa [hcfg] using hs₂
    have ht' : t = tape := by simpa [hcfg] using htape₂
    have hp' : hp = p_t := by
      have hh : hp = cfg₂.headPos := by simpa [hcfg]
      rw [hh, hhead₂, hn₈₅]
      simp [Dir.toInt]
      ring
    subst s; subst t; subst hp
    rfl
  have hπ₃' : SymSteps VerifierSym.transition cfg₂ π₃ cfg₃ := by
    rw [hcfg₂_eq]; exact hπ₃
  have hcfg₃_eq : cfg₃ = SymConfig.mk 87 cfg₃.tape (p_t + (ebits.length : ℤ)) := by
    rcases hcfg : cfg₃ with ⟨s, t, hp⟩
    have hs' : s = 87 := by simpa [hcfg] using hs₃
    have hp' : hp = p_t + (ebits.length : ℤ) := by
      have hh : hp = cfg₃.headPos := by simpa [hcfg]
      rw [hh, hhead₃]
    subst s; subst hp
    rfl
  have hπ₄' : SymSteps VerifierSym.transition cfg₃ π₄ cfg₄ := by
    rw [hcfg₃_eq]; exact hπ₄
  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) (π₁ ++ π₂ ++ π₃ ++ π₄) cfg₄ := by
    have h₁₂₃ : SymSteps VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) (π₁ ++ π₂ ++ π₃) cfg₃ :=
      SymSteps_trans VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) cfg₂ cfg₃ (π₁ ++ π₂) π₃ h₁₂ hπ₃'
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 84 tape (p_e + (ebits.length : ℤ))) cfg₃ cfg₄ (π₁ ++ π₂ ++ π₃) π₄ h₁₂₃ hπ₄'
  refine ⟨π₁ ++ π₂ ++ π₃ ++ π₄, cfg₄, htotal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₄
  · rw [hhead₄, hn₈₇]
    omega
  · -- target = targetTape 0
    intro i hi
    have hlen : (targetTape 0 (subAllBits tbits ebits)).length = tbits.length := by
      simp [targetTape_length, subAllBits_length]
    have hi_t : i < tbits.length := by rw [hlen] at hi; exact hi
    have htape₄_i : cfg₄.tape (p_t + (i : ℤ)) = cfg₃.tape (p_t + (i : ℤ)) := by rw [htape₄]
    rw [htape₄_i]
    by_cases hle_i : i < ebits.length
    · -- 低 ebits.length 格：被 clearMark 清过
      have hclr := hclear₃ i hle_i
      rw [hclr]
      have ht := htarget i (by
        have hlen' : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
          simp [targetTape_length, subAllBits_length]
        rw [hlen']
        exact hi_t)
      rw [ht]
      exact targetTape_clearMark_nth ebits.length i (subAllBits tbits ebits) hle_i (by simpa [subAllBits_length] using hlen_le)
    · -- 高位：未被 clearMark 扫过，保持原样 = targetTape 0 同一位
      have hge : ebits.length ≤ i := by omega
      by_cases heq_i : i = ebits.length
      · subst i
        rw [hstop₃]
        have ht := htarget ebits.length (by
          have hlen' : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
            simp [targetTape_length, subAllBits_length]
          rw [hlen']
          exact hi_t)
        rw [ht]
        exact targetTape_high_nth ebits.length ebits.length (subAllBits tbits ebits) (le_refl ebits.length) (by simpa [subAllBits_length] using hi_t)
      · rw [hright₃ (p_t + (i : ℤ)) (by omega)]
        have ht := htarget i (by
          have hlen' : (targetTape ebits.length (subAllBits tbits ebits)).length = tbits.length := by
            simp [targetTape_length, subAllBits_length]
          rw [hlen']
          exact hi_t)
        rw [ht]
        exact targetTape_high_nth ebits.length i (subAllBits tbits ebits) hge (by simpa [subAllBits_length] using hi_t)
  · -- tape (p_e - 1) = boundary
    have hkeep : cfg₄.tape (p_e - 1) = cfg₃.tape (p_e - 1) := by rw [htape₄]
    rw [hkeep]
    by_cases heq : p_e - 1 = p_t + (ebits.length : ℤ)
    · rw [heq]
      rw [hstop₃]
      rw [heq] at hbound
      exact hbound
    · rw [hright₃ (p_e - 1) (by omega), hbound]
  · -- tape (p_t - 1) = boundary
    have hkeep : cfg₄.tape (p_t - 1) = cfg₃.tape (p_t - 1) := by rw [htape₄]
    rw [hkeep]
    rw [hleft₃ (p_t - 1) (by omega)]
    exact hhashL
  · -- tape p_e = data0
    have hkeep : cfg₄.tape p_e = cfg₃.tape p_e := by rw [htape₄]
    rw [hkeep]
    rw [hright₃ p_e (by omega)]
    exact hsel0
  · -- value bits = consumed
    intro i hi
    have hkeep : cfg₄.tape (p_e + 1 + (i : ℤ)) = cfg₃.tape (p_e + 1 + (i : ℤ)) := by rw [htape₄]
    rw [hkeep]
    rw [hright₃ (p_e + 1 + (i : ℤ)) (by omega)]
    exact hconsumed i hi
  · -- 右不变：i > p_e + ebits.length
    intro i hi
    rw [htape₄]
    exact hright₃ i (by omega)
  · -- gap 不变：p_t + tbits.length ≤ i < p_e
    intro i hi
    rw [htape₄]
    by_cases heq : i = p_t + (ebits.length : ℤ)
    · rw [heq]
      exact hstop₃
    · exact hright₃ i (by omega)

/-- 按选择 sel 编码元素区（α/β 标记 → sel/nosel，值位保持）。 -/
def subAllSelected (k : ℕ) (tbits : List Bool) (elems : List ℕ) (sel : List Bool) : List Bool :=
  match elems, sel with
  | [], _ => tbits
  | v :: rest, b :: sel' => if b then subAllSelected k (subAllBits tbits (bitsOf v)) rest sel' else subAllSelected k tbits rest sel'
  | _, _ => tbits

/-- `selectedSum` 的 cons 展开。 -/
lemma selectedSum_cons (v : ℕ) (rest : List ℕ) (b : Bool) (sel' : List Bool) :
    selectedSum (v :: rest) (b :: sel') = (if b then v else 0) + selectedSum rest sel' := by
  unfold selectedSum
  by_cases hb : b <;> simp [hb]

/-- 选中当前元素时，其值 ≤ 剩余 target 值。 -/
lemma selected_ge_of_le (v : ℕ) (rest : List ℕ) (sel' : List Bool) (tbits : List Bool)
    (hle : selectedSum (v :: rest) (true :: sel') ≤ bitsValue tbits) :
    v ≤ bitsValue tbits := by
  have h : selectedSum (v :: rest) (true :: sel') = v + selectedSum rest sel' := by
    simpa using (selectedSum_cons v rest true sel')
  omega

/-- 选中当前元素并减完后，剩余选中和 ≤ 剩余 target 值。 -/
lemma selected_rest_le_of_le (k : ℕ) (v : ℕ) (rest : List ℕ) (sel' : List Bool) (tbits : List Bool)
    (hle : selectedSum (v :: rest) (true :: sel') ≤ bitsValue tbits) :
    selectedSum rest sel' ≤ bitsValue (subAllBits tbits (bitsOf v)) := by
  have hv : v ≤ bitsValue tbits := selected_ge_of_le v rest sel' tbits hle
  have hsub : bitsValue (subAllBits tbits (bitsOf v)) = bitsValue tbits - v := by
    rw [subAllBits_value]
    · rw [bitsValue_bitsOf]
    · simpa [bitsValue_bitsOf]
  rw [hsub]
  have h : selectedSum (v :: rest) (true :: sel') = v + selectedSum rest sel' := by
    simpa using (selectedSum_cons v rest true sel')
  omega

/-- 不选中当前元素时，剩余选中和 ≤ 剩余 target 值（target 不变）。 -/
lemma selected_rest_le_of_not (v : ℕ) (rest : List ℕ) (sel' : List Bool) (tbits : List Bool)
    (hle : selectedSum (v :: rest) (false :: sel') ≤ bitsValue tbits) :
    selectedSum rest sel' ≤ bitsValue tbits := by
  have h : selectedSum (v :: rest) (false :: sel') = selectedSum rest sel' := by
    simpa using (selectedSum_cons v rest false sel')
  omega

/-- `subAllSelected` 的值：bitsValue (subAllSelected k tbits elems sel) = bitsValue tbits
- selectedSum elems sel。 -/

lemma subAllSelected_value (k : ℕ) (tbits : List Bool) (elems : List ℕ) (sel : List Bool)
    (hle : selectedSum elems sel ≤ bitsValue tbits) :
    bitsValue (subAllSelected k tbits elems sel) = bitsValue tbits - selectedSum elems sel := by
  induction elems generalizing tbits sel with
  | nil =>
      cases sel <;> simp [subAllSelected, selectedSum]
  | cons v rest ih =>
      cases sel with
      | nil => simp [subAllSelected, selectedSum]
      | cons b sel' =>
          by_cases hb : b
          · have hsv : selectedSum (v :: rest) (b :: sel') = v + selectedSum rest sel' := by
              simpa [hb] using (selectedSum_cons v rest b sel')
            have hle' : v + selectedSum rest sel' ≤ bitsValue tbits := by simpa [hsv] using hle
            have hv_le : v ≤ bitsValue tbits := by omega
            have hsub : bitsValue (subAllBits tbits (bitsOf v)) = bitsValue tbits - v := by
              rw [subAllBits_value]
              · rw [bitsValue_bitsOf]
              · simpa [bitsValue_bitsOf]
            have hle_rest : selectedSum rest sel' ≤ bitsValue (subAllBits tbits (bitsOf v)) := by
              rw [hsub]
              omega
            have hrec := ih (subAllBits tbits (bitsOf v)) sel' hle_rest
            rw [show subAllSelected k tbits (v :: rest) (b :: sel') =
                subAllSelected k (subAllBits tbits (bitsOf v)) rest sel' by
              simp [subAllSelected, hb]]
            rw [hrec, hsub, hsv]
            omega
          · have hsv : selectedSum (v :: rest) (b :: sel') = selectedSum rest sel' := by
              simpa [hb] using (selectedSum_cons v rest b sel')
            have hle_rest : selectedSum rest sel' ≤ bitsValue tbits := by simpa [hsv] using hle
            have hrec := ih tbits sel' hle_rest
            rw [show subAllSelected k tbits (v :: rest) (b :: sel') =
            subAllSelected k tbits rest sel' by
              simp [subAllSelected, hb]]
            rw [hrec, hsv]

/-- 状态 2 读无标记 α：写 nosel，右移（β 与带标记 α 读到即陷阱）。 -/
lemma trans2_nosel (s : Sym) (hs : s.1 = SymKind.alpha ∧ s.2 = false) :
    { nextState := 2, writeSym := Sym.nosel, moveDir := Dir.R } ∈
    VerifierSym.transition (2, s) := by
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.alpha := by simpa using hs.1
  subst k
  have hm : m = false := by simpa using hs.2
  subst m
  decide

/-- 状态 2 读 data0/data1：写回自身右移。 -/
lemma trans2_keep_data (s : Sym) (hs : s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) :
    { nextState := 2, writeSym := s, moveDir := Dir.R } ∈ VerifierSym.transition (2, s) := by
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.data0 ∨ k = SymKind.data1 := by simpa using hs
  cases hk with
  | inl h => subst k; cases m <;> decide
  | inr h => subst k; cases m <;> decide

/-- 状态 2 读无标记 α：按选择 b 写 sel 或 nosel，右移（β 与带标记 α 读到即陷阱）。 -/
lemma trans2_chosen (s : Sym) (b : Bool) (hs : s.1 = SymKind.alpha ∧ s.2 = false) :
    { nextState := 2, writeSym := (if b then Sym.sel else Sym.nosel), moveDir := Dir.R } ∈
      VerifierSym.transition (2, s) := by
  rcases s with ⟨k, m⟩
  have hk : k = SymKind.alpha := by simpa using hs.1
  subst k
  have hm : m = false := by simpa using hs.2
  subst m
  cases b <;> decide

/-- 状态 2 右移 k 格值位（写回自身）到 sep/#₁ 前一格。 -/
lemma scanRight2_bits (v : ℕ) (q : ℤ) (tape : ℤ → Sym)
    (hbits : tapeAgrees tape (q + 1) (encodeBitsSymNative v)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 2 tape (q + 1)) π cfg' ∧
      cfg'.state = 2 ∧ cfg'.headPos = q + 1 + ((encodeBitsSymNative v).length : ℤ) ∧
      cfg'.tape = tape := by
  have hkeep : ∀ i : ℤ, q + 1 ≤ i ∧ i < q + 1 + ((encodeBitsSymNative v).length : ℤ) →
      { nextState := 2, writeSym := tape i, moveDir := Dir.R } ∈
      VerifierSym.transition (2, tape i) := by
    intro i hi
    have ioff : ∃ io : ℕ, (io : ℤ) = i - (q + 1) := by
      refine ⟨(i - (q + 1)).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (q + 1))
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < (encodeBitsSymNative v).length := by omega
    have ht : tape (q + 1 + (io : ℤ)) = (encodeBitsSymNative v)[io] := hbits io hio_lt
    have hidx : q + 1 + (io : ℤ) = i := by omega
    rw [← hidx, ht]
    have hmem : (encodeBitsSymNative v)[io] ∈ encodeBitsSymNative v := List.getElem_mem hio_lt
    have hdata := encodeBitsSymNative_nonboundary v ((encodeBitsSymNative v)[io]) hmem
    exact trans2_keep_data ((encodeBitsSymNative v)[io]) hdata
  exact scanRightKeep 2 (encodeBitsSymNative v).length (q + 1) tape hkeep

/-- `subAllSelected` 保持位宽。 -/
@[simp] lemma subAllSelected_length (k : ℕ) (tbits : List Bool) (elems : List ℕ) (sel : List Bool) :
    (subAllSelected k tbits elems sel).length = tbits.length := by
  induction elems generalizing tbits sel with
  | nil => simp [subAllSelected]
  | cons v rest ih =>
      cases sel with
      | nil => simp [subAllSelected]
      | cons b sel' =>
          by_cases hb : b
          · simp [subAllSelected, hb, subAllBits_length, ih]
          · simp [subAllSelected, hb, ih]

/-- 状态 2 带选择的右扫：逐元素消费 sel，α/β 按 sel[i] 写成 sel/nosel，值位/sep 保持，
    扫到 #₁ → 状态 3。改写后元素区等于物理编码 `encodeElementsSymWithSel`。 -/
lemma scanRight2_chosen (elems : List ℕ) (sel : List Bool) (p : ℤ) (tape : ℤ → Sym)
    (hsel_len : sel.length = elems.length)
    (helems : tapeAgrees tape p (encodeElementsSym elems))
    (hbound : tape (p + (encodeElementsSym elems).length) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) π cfg' ∧
      cfg'.state = 3 ∧
      cfg'.headPos = p + (encodeElementsSym elems).length ∧
      tapeAgrees cfg'.tape p (encodeElementsSymWithSel elems sel) ∧
      (∀ i : ℤ, p ≤ i ∧ i < p + (encodeElementsSym elems).length → (cfg'.tape i).1 ≠ SymKind.boundary) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      cfg'.tape (p + (encodeElementsSym elems).length) = Sym.boundary := by
  induction elems generalizing p tape sel with
  | nil =>
    -- 空元素列表：2 直接读 #₁ → 3 停
    have hsel0 : sel = [] := List.eq_nil_of_length_eq_zero (by simpa using hsel_len)
    subst sel
    let r : SymTransResult := { nextState := 3, writeSym := Sym.boundary, moveDir := Dir.S }
    let step : SymStep := { fromState := 2, readSym := Sym.boundary, result := r }
    have hbound0 : tape p = Sym.boundary := by simpa using hbound
    have htrans : step.result ∈ VerifierSym.transition (2, tape p) := by
      rw [hbound0]
      decide
    refine ⟨[step], symStepConfig (SymConfig.mk 2 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · refine SymSteps.cons [] step (SymConfig.mk 2 tape p) SymSteps.nil ?_ ?_ ?_
      · rfl
      · simp [SymConfig.mk, step, hbound0]
      · simp [step, r, hbound0]
        decide
    · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
    · intro i hi
      change i < (encodeElementsSymWithSel [] []).length at hi
      simp [encodeElementsSymWithSel, joinLists] at hi
    · intro i hi
      exfalso
      simp [encodeElementsSym] at hi
      omega
    · intro i hi
      have hne : i ≠ p := by omega
      simp [symStepConfig, SymConfig.mk, step, r, hne]
    · simp [symStepConfig, SymConfig.mk, step, r, encodeElementsSym]

  | cons v rest ih =>
      cases sel with
      | nil =>
          have h : ([] : List Bool).length = (v :: rest).length := hsel_len
          simp at h
      | cons b sel' =>
          have hsel' : sel'.length = rest.length := by
            have h := hsel_len
            simp at h
            exact h
          let w : Sym := if b then Sym.sel else Sym.nosel
          cases hrest : rest with
          | nil =>
              -- 最后元素：[alpha] ++ encodeBitsSymNative v
              subst rest
              have halpha_cons : tapeAgrees tape p ([Sym.alpha] ++ encodeBitsSymNative v) := by
                simp [encodeElementsSym] at helems ⊢
                exact helems
              have halpha : tape p = Sym.alpha :=
                (tapeAgrees_cons tape p Sym.alpha (encodeBitsSymNative v)).mp halpha_cons |>.1
              have hbits : tapeAgrees tape (p + 1) (encodeBitsSymNative v) :=
                (tapeAgrees_cons tape p Sym.alpha (encodeBitsSymNative v)).mp halpha_cons |>.2
              let r1 : SymTransResult := { nextState := 2, writeSym := w, moveDir := Dir.R }
              let step1 : SymStep := { fromState := 2, readSym := Sym.alpha, result := r1 }
              have htrans1 : step1.result ∈ VerifierSym.transition (2, tape p) := by
                rw [halpha]
                simpa [step1, r1, w] using (trans2_chosen Sym.alpha b ⟨rfl, rfl⟩)
              have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) [step1]
                  (symStepConfig (SymConfig.mk 2 tape p) step1.result) := by
                refine SymSteps.cons [] step1 (SymConfig.mk 2 tape p) SymSteps.nil ?_ ?_ ?_
                · rfl
                · change Sym.alpha = tape p; rw [halpha]
                · exact htrans1
              let tape1 : ℤ → Sym := fun i => if i = p then w else tape i
              have hcfg1 : symStepConfig (SymConfig.mk 2 tape p) step1.result = SymConfig.mk 2 tape1 (p + 1) := by
                simp [symStepConfig, SymConfig.mk, step1, r1, tape1, w, Dir.toInt]
              have hbits1 : tapeAgrees tape1 (p + 1) (encodeBitsSymNative v) := by
                intro i hi
                have hne : p + 1 + (i : ℤ) ≠ p := by omega
                rw [show tape1 (p + 1 + (i : ℤ)) = tape (p + 1 + (i : ℤ)) from by simp [tape1, hne]]
                exact hbits i hi
              rcases scanRight2_bits v p tape1 hbits1 with ⟨π2, cfg2, hπ2, hs2, hhead2, htape2⟩
              have hbound' : tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ)) = Sym.boundary := by
                have hne : p + 1 + ((encodeBitsSymNative v).length : ℤ) ≠ p := by omega
                rw [show tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ)) = tape (p + 1 + ((encodeBitsSymNative v).length : ℤ)) from by simp [tape1, hne]]
                have hlen_e : (encodeElementsSym [v]).length = 1 + (encodeBitsSymNative v).length := by
                  simp [encodeElementsSym]
                  omega
                have hpos : p + 1 + ((encodeBitsSymNative v).length : ℤ) = p + ((encodeElementsSym [v]).length : ℤ) := by
                  rw [hlen_e]
                  push_cast
                  ring
                rw [hpos]
                exact hbound
              let r3 : SymTransResult := { nextState := 3, writeSym := Sym.boundary, moveDir := Dir.S }
              let step3 : SymStep := { fromState := 2, readSym := Sym.boundary, result := r3 }
              have hcfg2_eq : cfg2 = SymConfig.mk 2 tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ)) := by
                rw [← hs2, ← htape2, ← hhead2]
              have htrans3 : step3.result ∈ VerifierSym.transition (2, tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ))) := by
                rw [hbound']; decide
              have hstep3 : SymSteps VerifierSym.transition cfg2 [step3]
                  (symStepConfig cfg2 step3.result) := by
                refine SymSteps.cons [] step3 cfg2 SymSteps.nil ?_ ?_ ?_
                · simpa [step3] using hs2.symm
                · change Sym.boundary = cfg2.tape cfg2.headPos
                  rw [hcfg2_eq]
                  simp [SymConfig.mk, hbound']
                · change step3.result ∈ VerifierSym.transition (cfg2.state, cfg2.tape cfg2.headPos)
                  rw [hcfg2_eq]
                  simp [SymConfig.mk, hbound']
                  decide
              let cfg3 : SymConfig := symStepConfig cfg2 step3.result
              have htotal : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) ([step1] ++ π2 ++ [step3]) cfg3 := by
                have h12 : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) ([step1] ++ π2) cfg2 :=
                  SymSteps_trans VerifierSym.transition (SymConfig.mk 2 tape p) (SymConfig.mk 2 tape1 (p + 1)) cfg2 [step1] π2 (hcfg1 ▸ hstep1) hπ2
                exact SymSteps_trans VerifierSym.transition (SymConfig.mk 2 tape p) cfg2 cfg3 ([step1] ++ π2) [step3] h12 hstep3
              have htape3 : cfg3.tape = tape1 := by
                have hhead2' : cfg2.headPos = p + 1 + ((encodeBitsSymNative v).length : ℤ) := by simpa using hhead2
                have htape2' : cfg2.tape = tape1 := by simpa using htape2
                dsimp [cfg3]
                simp only [symStepConfig, SymConfig.mk, step3, r3]
                rw [hhead2', htape2']
                funext i
                by_cases h : i = p + 1 + ((encodeBitsSymNative v).length : ℤ)
                · simp [h, hbound']
                · simp [h]
              have hfinal : tapeAgrees cfg3.tape p (encodeElementsSymWithSel [v] (b :: sel')) := by
                have hch : encodeElementsSymWithSel [v] (b :: sel') = w :: encodeBitsSymNative v := by
                  simp [encodeElementsSymWithSel, w, joinLists, joinLists_cons]
                rw [hch, htape3]
                exact (tapeAgrees_cons tape1 p w (encodeBitsSymNative v)).mpr ⟨by simp [tape1], hbits1⟩
              refine ⟨[step1] ++ π2 ++ [step3], cfg3, htotal, rfl, ?_, hfinal, ?_, ?_, ?_⟩
              · have hhead3 : cfg3.headPos = p + 1 + ((encodeBitsSymNative v).length : ℤ) := by
                  have hhead2' : cfg2.headPos = p + 1 + ((encodeBitsSymNative v).length : ℤ) := by simpa using hhead2
                  dsimp [cfg3]
                  simp only [symStepConfig, SymConfig.mk, step3, r3, Dir.toInt]
                  rw [hhead2']
                  ring
                rw [hhead3]
                have hlen : (encodeElementsSym [v]).length = 1 + (encodeBitsSymNative v).length := by
                  simp [encodeElementsSym]
                  omega
                rw [hlen]
                rw [show ((1 + (encodeBitsSymNative v).length : ℕ) : ℤ) = 1 + ↑(encodeBitsSymNative v).length from by simp]
                ring
              · intro i h
                have hi : p ≤ i ∧ i < p + 1 + ((encodeBitsSymNative v).length : ℤ) := by
                  have hlen : (encodeElementsSym [v]).length = 1 + (encodeBitsSymNative v).length := by
                    simp [encodeElementsSym]
                    omega
                  omega
                rw [htape3]
                by_cases heq : i = p
                · subst i
                  rw [show tape1 p = w from by simp [tape1]]
                  cases b <;> simp [w] <;> decide
                · have hne : i ≠ p := by omega
                  have ioff : ∃ io : ℕ, (io : ℤ) = i - (p + 1) := by
                    refine ⟨(i - (p + 1)).toNat, ?_⟩
                    exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                  rcases ioff with ⟨io, hio⟩
                  have hio_lt : io < (encodeBitsSymNative v).length := by omega
                  have ht : tape (p + 1 + (io : ℤ)) = (encodeBitsSymNative v)[io] := hbits io hio_lt
                  have hidx : p + 1 + (io : ℤ) = i := by omega
                  rw [show tape1 i = tape i from by simp [tape1, hne]]
                  rw [← hidx, ht]
                  have hmem : (encodeBitsSymNative v)[io] ∈ encodeBitsSymNative v := List.getElem_mem hio_lt
                  have hnb := encodeBitsSymNative_nonboundary v ((encodeBitsSymNative v)[io]) hmem
                  rcases hnb with h' | h' <;> rw [h'] <;> decide
              · intro i hlt
                rw [htape3]
                by_cases h : i = p
                · subst i
                  omega
                · simp [tape1, h]
              · -- 右端 boundary 保持
                have hlen : (encodeElementsSym [v]).length = 1 + (encodeBitsSymNative v).length := by
                  simp [encodeElementsSym]
                  omega
                dsimp [cfg3]
                simp only [symStepConfig, SymConfig.mk, step3, r3]
                rw [show p + ((encodeElementsSym [v]).length : ℤ) = p + 1 + ((encodeBitsSymNative v).length : ℤ) from by
                  rw [hlen]
                  push_cast
                  ring]
                rw [hhead2]
                simp
          | cons w' rest' =>
              -- 非最后元素：[alpha] ++ encodeBitsSymNative v ++ encodeElementsSym rest
              have halpha_cons : tapeAgrees tape p ([Sym.alpha] ++ encodeBitsSymNative v ++ encodeElementsSym rest) := by
                simp [encodeElementsSym, hrest] at helems ⊢
                exact helems
              have halpha : tape p = Sym.alpha :=
                (tapeAgrees_cons tape p Sym.alpha (encodeBitsSymNative v ++ encodeElementsSym rest)).mp halpha_cons |>.1
              have hrest1 : tapeAgrees tape (p + 1) (encodeBitsSymNative v ++ encodeElementsSym rest) :=
                (tapeAgrees_cons tape p Sym.alpha (encodeBitsSymNative v ++ encodeElementsSym rest)).mp halpha_cons |>.2
              have hbits : tapeAgrees tape (p + 1) (encodeBitsSymNative v) :=
                (tapeAgrees_append tape (p + 1) (encodeBitsSymNative v) (encodeElementsSym rest)).mp hrest1 |>.1
              have helems_rest : tapeAgrees tape (p + 1 + ((encodeBitsSymNative v).length : ℤ)) (encodeElementsSym rest) :=
                (tapeAgrees_append tape (p + 1) (encodeBitsSymNative v) (encodeElementsSym rest)).mp hrest1 |>.2
              -- 步骤 1：读 α 写 w 右移
              let r1 : SymTransResult := { nextState := 2, writeSym := w, moveDir := Dir.R }
              let step1 : SymStep := { fromState := 2, readSym := Sym.alpha, result := r1 }
              have htrans1 : step1.result ∈ VerifierSym.transition (2, tape p) := by
                rw [halpha]
                simpa [step1, r1, w] using (trans2_chosen Sym.alpha b ⟨rfl, rfl⟩)
              have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) [step1]
                  (symStepConfig (SymConfig.mk 2 tape p) step1.result) := by
                refine SymSteps.cons [] step1 (SymConfig.mk 2 tape p) SymSteps.nil ?_ ?_ ?_
                · rfl
                · change Sym.alpha = tape p; rw [halpha]
                · exact htrans1
              let tape1 : ℤ → Sym := fun i => if i = p then w else tape i
              have hcfg1 : symStepConfig (SymConfig.mk 2 tape p) step1.result = SymConfig.mk 2 tape1 (p + 1) := by
                simp [symStepConfig, SymConfig.mk, step1, r1, tape1, w, Dir.toInt]
              have hbits1 : tapeAgrees tape1 (p + 1) (encodeBitsSymNative v) := by
                intro i hi
                have hne : p + 1 + (i : ℤ) ≠ p := by omega
                rw [show tape1 (p + 1 + (i : ℤ)) = tape (p + 1 + (i : ℤ)) from by simp [tape1, hne]]
                exact hbits i hi
              rcases scanRight2_bits v p tape1 hbits1 with ⟨π2, cfg2, hπ2, hs2, hhead2, htape2⟩
              -- 直接递归（元素间无分隔符）
              have hcfg2_eq : cfg2 = SymConfig.mk 2 tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ)) := by
                rw [← hs2, ← htape2, ← hhead2]
              have helems_rest1 : tapeAgrees tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ)) (encodeElementsSym rest) := by
                intro i hi
                have hne : p + 1 + ((encodeBitsSymNative v).length : ℤ) + (i : ℤ) ≠ p := by omega
                rw [show tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ) + (i : ℤ)) = tape (p + 1 + ((encodeBitsSymNative v).length : ℤ) + (i : ℤ)) from by simp [tape1, hne]]
                exact helems_rest i hi
              have hbound_rest : tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ) + (encodeElementsSym rest).length) = Sym.boundary := by
                have hne : p + 1 + ((encodeBitsSymNative v).length : ℤ) + (encodeElementsSym rest).length ≠ p := by omega
                rw [show tape1 (p + 1 + ((encodeBitsSymNative v).length : ℤ) + (encodeElementsSym rest).length) = tape (p + 1 + ((encodeBitsSymNative v).length : ℤ) + (encodeElementsSym rest).length) from by simp [tape1, hne]]
                have hlen_e : (encodeElementsSym (v :: rest)).length = (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                  simp [encodeElementsSym, hrest]
                  omega
                have hpos : p + 1 + ((encodeBitsSymNative v).length : ℤ) + (encodeElementsSym rest).length =
                    p + ((encodeElementsSym (v :: rest)).length : ℤ) := by
                  rw [hlen_e]
                  push_cast
                  ring
                rw [hpos]
                exact hbound
              rcases ih sel' (p + 1 + ((encodeBitsSymNative v).length : ℤ)) tape1 hsel' helems_rest1 hbound_rest
                with ⟨π', cfg', hπ', hs', hhead', htape', hnb', hleft', hbound_keep'⟩
              have h12 : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) ([step1] ++ π2) cfg2 :=
                SymSteps_trans VerifierSym.transition (SymConfig.mk 2 tape p) (SymConfig.mk 2 tape1 (p + 1)) cfg2 [step1] π2 (hcfg1 ▸ hstep1) hπ2
              have hπ'' : SymSteps VerifierSym.transition cfg2 π' cfg' := by
                rw [hcfg2_eq]
                exact hπ'
              have htotal : SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) ([step1] ++ π2 ++ π') cfg' :=
                SymSteps_trans VerifierSym.transition (SymConfig.mk 2 tape p) cfg2 cfg' ([step1] ++ π2) π' h12 hπ''
              have hfinal : tapeAgrees cfg'.tape p (encodeElementsSymWithSel (v :: rest) (b :: sel')) := by
                have hch : encodeElementsSymWithSel (v :: rest) (b :: sel') =
                    w :: (encodeBitsSymNative v ++ encodeElementsSymWithSel rest sel') := by
                  simp [encodeElementsSymWithSel, w, joinLists, joinLists_cons]
                rw [hch, tapeAgrees_cons]
                constructor
                · have hleft_p : cfg'.tape p = tape1 p := hleft' p (by omega : p < p + 1 + ((encodeBitsSymNative v).length : ℤ))
                  simp [tape1] at hleft_p
                  rw [hleft_p]
                · rw [tapeAgrees_append]
                  constructor
                  · intro i hi
                    have hleft_i : cfg'.tape (p + 1 + (i : ℤ)) = tape1 (p + 1 + (i : ℤ)) :=
                      hleft' (p + 1 + (i : ℤ)) (by omega)
                    rw [hleft_i]
                    have hne : p + 1 + (i : ℤ) ≠ p := by omega
                    rw [show tape1 (p + 1 + (i : ℤ)) =
                    tape (p + 1 + (i : ℤ)) from by simp [tape1, hne]]
                    simpa using (hbits i hi)
                  · exact htape'
              simp only [← hrest]
              refine ⟨[step1] ++ π2 ++ π', cfg', htotal, hs', ?_, hfinal, ?_, ?_, ?_⟩
              · rw [hhead']
                have hlen_e : (encodeElementsSym (v :: rest)).length = (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                  simp [encodeElementsSym, hrest]
                  omega
                have hlen_e' : ((encodeElementsSym (v :: rest)).length : ℤ) = ((encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length : ℤ) := by
                  exact_mod_cast hlen_e
                rw [hlen_e']
                push_cast
                omega
              · intro i h
                have hi : p ≤ i ∧ i < p + (encodeElementsSym (v :: rest)).length := h
                have hlen_e : (encodeElementsSym (v :: rest)).length = (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                  simp [encodeElementsSym, hrest]
                  omega
                have hi' : i < p + 1 + ((encodeBitsSymNative v).length : ℤ) ∨
                    (p + 1 + ((encodeBitsSymNative v).length : ℤ) ≤ i ∧ i < p + 1 + ((encodeBitsSymNative v).length : ℤ) + (encodeElementsSym rest).length) := by
                  rw [hlen_e] at hi
                  push_cast at hi
                  omega
                rcases hi' with hlt | hge
                · have hleft_i : cfg'.tape i = tape1 i := hleft' i (by omega : i < p + 1 + ((encodeBitsSymNative v).length : ℤ))
                  rw [hleft_i]
                  by_cases heq : i = p
                  · subst i
                    rw [show tape1 p = w from by simp [tape1]]
                    cases b <;> simp [w] <;> decide
                  · have hne : i ≠ p := by omega
                    have ioff : ∃ io : ℕ, (io : ℤ) = i - (p + 1) := by
                      refine ⟨(i - (p + 1)).toNat, ?_⟩
                      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p + 1))
                    rcases ioff with ⟨io, hio⟩
                    have hio_lt : io < (encodeBitsSymNative v).length := by omega
                    have ht : tape (p + 1 + (io : ℤ)) = (encodeBitsSymNative v)[io] := hbits io hio_lt
                    have hidx : p + 1 + (io : ℤ) = i := by omega
                    rw [show tape1 i = tape i from by simp [tape1, hne]]
                    rw [← hidx, ht]
                    have hmem : (encodeBitsSymNative v)[io] ∈ encodeBitsSymNative v :=
                    List.getElem_mem hio_lt
                    have hnb := encodeBitsSymNative_nonboundary v ((encodeBitsSymNative v)[io]) hmem
                    rcases hnb with h' | h' <;> rw [h'] <;> decide
                · exact hnb' i hge
              · intro i hlt
                have hleft_i : cfg'.tape i = tape1 i := hleft' i (by omega :
                i < p + 1 + ((encodeBitsSymNative v).length : ℤ))
                rw [hleft_i]
                by_cases h : i = p
                · subst i
                  omega
                · simp [tape1, h]
              · -- 右端 boundary 保持
                rw [show p + ((encodeElementsSym (v :: rest)).length : ℤ) =
                (p + 1 + ((encodeBitsSymNative v).length : ℤ)) + (encodeElementsSym rest).length from by
                  have hlen_e : (encodeElementsSym (v :: rest)).length =
                  (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                    simp [encodeElementsSym, hrest]
                    omega
                  rw [hlen_e]
                  push_cast
                  ring]
                exact hbound_keep'

/-- 给定选择 sel 的分支阶段（完备性用）：0→1→2(按 sel 写 chosen)→3→24→格式检查→4。
    输出 7 项：state、headPos=k+2、target 区保持、格 0 与格 1+k 的 boundary、
    chosen 元素区、尾部 #₁ 已标 m=1（(boundary,true)）。 -/
lemma mem_zip_fst {α β : Type} {l : List α} {m : List β} {p : α × β}
    (h : p ∈ l.zip m) : p.1 ∈ l := by
  induction l generalizing m with
  | nil => simp at h
  | cons a l ih =>
      cases m with
      | nil => simp at h
      | cons b m =>
          simp at h
          rcases h with h | h
          · simp [h]
          · exact List.mem_cons_of_mem _ (ih h)

lemma branch_with_sel (inst : SubsetSumInstance) (hne : inst.elements ≠ [])
    (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    (sel : List Bool) (hsel_len : sel.length = inst.elements.length) :
    ∃ π cfg', SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg' ∧
      cfg'.state = 4 ∧
      cfg'.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) ∧
      tapeAgrees cfg'.tape 1 (encodeBitsSym inst.target) ∧
      cfg'.tape 0 = Sym.boundary ∧
      cfg'.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
      (∃ sel' : List Bool, sel'.length = inst.elements.length ∧
        tapeAgrees cfg'.tape (2 + ((encodeBitsSym inst.target).length : ℤ)) (encodeElementsSymWithSel inst.elements sel')) ∧
      cfg'.tape (2 + ((encodeBitsSym inst.target).length : ℤ) + ((encodeElementsSym inst.elements).length : ℤ)) =
        Sym.mk SymKind.boundary true := by
  let elems := encodeElementsSym inst.elements
  let blocks : List (Sym × List Sym) := (inst.elements.zip sel).map (fun p => (if p.2 then Sym.sel else Sym.nosel, encodeBitsSymNative p.1))
  have hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
    intro b hb
    rw [List.mem_map] at hb
    rcases hb with ⟨p, hp, hb⟩
    subst b
    constructor
    · by_cases hp2 : p.2 <;> simp [hp2]
    constructor
    · intro h
      have hlen := congrArg List.length h
      simp only [encodeBitsSymNative, List.length_map] at hlen
      have hlen0 : (Nat.digits 2 p.1).length = 0 := hlen
      have hd : 0 < (Nat.digits 2 p.1).length := by
        have hp1mem : p.1 ∈ inst.elements := by
          exact mem_zip_fst hp
        exact List.length_pos_iff_ne_nil.mpr
          (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt (hpos p.1 hp1mem)))
      omega
    · intro s hs
      change s ∈ encodeBitsSymNative p.1 at hs
      unfold encodeBitsSymNative at hs
      rw [List.mem_map] at hs
      rcases hs with ⟨x, hx, hs⟩
      rw [← hs]
      constructor
      · by_cases hxr : x = 0 <;> simp [hxr, Sym.data0, Sym.data1]
      · by_cases hxr : x = 0 <;> simp [hxr, Sym.data0, Sym.data1]
  have hjl : joinLists (blocks.map (fun b => [b.1] ++ b.2)) = encodeElementsSymWithSel inst.elements sel := by
    rw [encodeElementsSymWithSel_eq_join inst.elements sel hsel_len]
    dsimp [blocks]
    simp [Function.comp_def, List.map_map]
  have hlen_eq : (joinLists (blocks.map (fun b => [b.1] ++ b.2))).length = elems.length := by
    rw [joinLists_length]
    dsimp [blocks]
    rw [List.map_map]
    simp [Function.comp_def, List.length_append, List.length_singleton]
    rw [hsel_len]
    simp
    dsimp [elems]
    rw [show (encodeElementsSym inst.elements).length = ((encodeElementsSym inst.elements).map chosenSub).length from by
      rw [List.length_map]]
    rw [← congrArg List.length (joinLists_map_sel_eq inst.elements)]
    rw [joinLists_length]
    rw [List.map_map]
    simp [Function.comp_def, List.length_append, List.length_singleton]
    change ((inst.elements.zip sel).map ((fun v : ℕ => (encodeBitsSymNative v).length) ∘ Prod.fst)).sum =
      (inst.elements.map (fun v => (encodeBitsSymNative v).length)).sum
    rw [← List.map_map]
    rw [List.map_fst_zip (Nat.le_of_eq hsel_len.symm)]
  have hblocks_ne : blocks ≠ [] := by
    intro h
    rcases hcases : inst.elements with _ | ⟨v, vs⟩
    · exact hne hcases
    · have hlen := congrArg List.length h
      simp only [blocks, List.length_map, List.length_nil] at hlen
      rw [hcases] at hlen
      have hpos : 0 < ((v :: vs).zip sel).length := by
        rw [List.length_zip]
        rw [show sel.length = (v :: vs).length from by simpa [hcases] using hsel_len]
        simp
      omega
  rcases branch_phase inst hne hpos htarget sel hsel_len
    (fun tape helems hbound => by
      let p : ℤ := 2 + (encodeBitsSym inst.target).length
      rcases scanRight2_chosen inst.elements sel p tape hsel_len helems hbound
        with ⟨π, cfg', hπ, hs, hh, hchosen, hnb, hleft, hbnd⟩
      refine ⟨π, cfg', hπ, hs, hh, hbnd, hleft, ?_⟩
      refine ⟨sel, hsel_len, ?_, rfl⟩
      exact hchosen)
    with ⟨π, cfg', hπ, hs4, hhead, htarget, hb0, hb1, hbels, hend⟩
  rcases hbels with ⟨hbels, hbels_len, hbels_tape, _hbels_eq⟩
  refine ⟨π, cfg', hπ, hs4, hhead, htarget, hb0, hb1, ?_, ?_⟩
  · exact ⟨hbels, hbels_len, hbels_tape⟩
  · exact hend

end Mp
