import Mp.SubsetSumVerifierReverse12

/-!
# R14 · 施工落点：素材库 + 新方案新节

依根目录 `Plan.md`（形式化实施方案 · 语义单位版 v5）施工。

## 素材三组（自 R13 迁入；代码逐字保留，旧口径标签已清理）
- **表级组**（11 件）：入口锁 / 读锁 / 5 步效应 / 复位闭区 / 100 吸收 —— N1（格的消费）、D1（分解）的内部证据；
- **走带族**（15 件）：回卷段 84-87、轮段（76/8、77/9、12、14、81、13）—— 单位（轮 / 清尾 / 占位扩展）腿账；
- **转向件**（10 件，备用）：转向 ≤ 2×状态改变步数 —— 注入阶段按需取用。

## 后续新节（按 Plan.md 施工顺序）
① α替换段 ② 格式检验段 ③ 逐元素段 ④ 判定段 ⑤ 串链与收口 ⑥ 判定与注入对齐。

（ρ 势函数 / 环链记账等旧方案残件未随迁；R13 整删，git 留史。）
-/

open Mp
open Mp.SymToF4

namespace Mp

set_option maxRecDepth 200000
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


/-! ## 走带族（清尾段 84-87：rewind84/85、clearMark86、scanRight87） -/

/-- clearMark86 长度版副本（Core1:3780 + 步数账 k+1）。86 @ p 东向清 k 个标记 → 87 @ p+k。 -/
lemma clearMark86_len (k : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hmarked : ∀ i : ℕ, i < k → (tape (p + (i : ℤ))).2 = true)
    (hstop : (tape (p + (k : ℤ))).2 = false)
    (hdata : ∀ i : ℤ, p ≤ i ∧ i < p + (k : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hdata_stop : (tape (p + (k : ℤ))).1 = SymKind.data0 ∨ (tape (p + (k : ℤ))).1 = SymKind.data1 ∨
      (tape (p + (k : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 86 tape p) π cfg' ∧
      cfg'.state = 87 ∧ cfg'.headPos = p + (k : ℤ) ∧
      π.length = k + 1 ∧
      (∀ i : ℕ, i < k → cfg'.tape (p + (i : ℤ)) = Sym.mk (tape (p + (i : ℤ))).1 false) ∧
      cfg'.tape (p + (k : ℤ)) = tape (p + (k : ℤ)) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p + (k : ℤ) < i → cfg'.tape i = tape i) := by
  induction k generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 87, writeSym := tape p, moveDir := Dir.S }
      let step : SymStep := { fromState := 86, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (86, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hms : ms = false := by simpa [Sym.mk, htp] using hstop
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 ∨ ks = SymKind.boundary := by
          simpa [Sym.mk, htp] using hdata_stop
        rcases hks with hk | hk | hk <;> subst ks <;> decide
      refine ⟨[step], symStepConfig (SymConfig.mk 86 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 86 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · simp
      · intro i hi
        omega
      · simp [symStepConfig, step, r]
      · intro i hi
        have hne : i ≠ p := by omega
        simp [symStepConfig, step, r, hne]
      · intro i hi
        have hne : i ≠ p := by omega
        simp [symStepConfig, step, r, hne]
  | succ k ih =>
      have h0 : (tape p).2 = true := by simpa using hmarked 0 (by omega)
      let tape₁ : ℤ → Sym := fun i => if i = p then Sym.mk (tape p).1 false else tape i
      let r : SymTransResult := { nextState := 86, writeSym := Sym.mk (tape p).1 false, moveDir := Dir.R }
      let step : SymStep := { fromState := 86, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (86, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hms : ms = true := by simpa [Sym.mk, htp] using h0
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hdata p (by constructor; rfl; omega)
        rcases hks with hk | hk <;> subst ks <;> decide
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk 86 tape p) [step]
          (symStepConfig (SymConfig.mk 86 tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk 86 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk 86 tape p) step.result = SymConfig.mk 86 tape₁ (p + 1) := by
        simp [symStepConfig, step, r, tape₁, Dir.toInt]
      have hmarked₁ : ∀ i : ℕ, i < k → (tape₁ (p + 1 + (i : ℤ))).2 = true := by
        intro i hi
        have h := hmarked (i + 1) (by omega)
        have htape : tape₁ (p + 1 + (i : ℤ)) = tape (p + ((i + 1 : ℕ) : ℤ)) := by
          simp only [tape₁]
          rw [if_neg (by omega : p + 1 + (i : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact h
      have hstop₁ : (tape₁ (p + 1 + (k : ℤ))).2 = false := by
        have htape : tape₁ (p + 1 + (k : ℤ)) = tape (p + ((k + 1 : ℕ) : ℤ)) := by
          simp only [tape₁]
          rw [if_neg (by omega : p + 1 + (k : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact hstop
      have hdata₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (k : ℤ) → (tape₁ i).1 = SymKind.data0 ∨ (tape₁ i).1 = SymKind.data1 := by
        intro i hi
        have hd := hdata i (by constructor <;> omega)
        have htape₁_i : tape₁ i = tape i := by
          simp only [tape₁]
          rw [if_neg (by omega : i ≠ p)]
        simpa [htape₁_i] using hd
      have hdata_stop₁ : (tape₁ (p + 1 + (k : ℤ))).1 = SymKind.data0 ∨ (tape₁ (p + 1 + (k : ℤ))).1 = SymKind.data1 ∨
          (tape₁ (p + 1 + (k : ℤ))).1 = SymKind.boundary := by
        have htape : tape₁ (p + 1 + (k : ℤ)) = tape (p + ((k + 1 : ℕ) : ℤ)) := by
          simp only [tape₁]
          rw [if_neg (by omega : p + 1 + (k : ℤ) ≠ p)]
          exact congrArg tape (by omega)
        rw [htape]
        exact hdata_stop
      rcases ih (p + 1) tape₁ hmarked₁ hstop₁ hdata₁ hdata_stop₁ with
        ⟨π', cfg', hπ', hs', hhead', hlen', hclear', hstop', hleft', hright'⟩
      refine ⟨step :: π', cfg', ?_, hs', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact symSteps_append_concat [step] π' hstep (by simpa [hcfg] using hπ')
      · rw [hhead']
        omega
      · simp [hlen']
      · intro i hi
        cases i with
        | zero =>
            have hkeep : cfg'.tape p = (SymConfig.mk 86 tape₁ (p + 1)).tape p := by
              exact hleft' p (by omega)
            simpa [SymConfig.mk, tape₁] using hkeep
        | succ i =>
            have h := hclear' i (by omega)
            have hshift : p + ((i + 1 : ℕ) : ℤ) = (p + 1) + (i : ℤ) := by omega
            have htape₁ : tape₁ ((p + 1) + (i : ℤ)) = tape ((p + 1) + (i : ℤ)) := by
              simp only [tape₁]
              rw [if_neg (by omega : (p + 1) + (i : ℤ) ≠ p)]
            rw [hshift, ← htape₁]
            exact h
      · rw [show (p + ((k + 1 : ℕ) : ℤ)) = (p + 1) + (k : ℤ) from by omega]
        rw [hstop']
        simp only [tape₁]
        rw [if_neg (by omega : (p + 1) + (k : ℤ) ≠ p)]
      · intro i hi
        have hi₁ : i < p + 1 := by omega
        have h' := hleft' i hi₁
        have htape₁_i : tape₁ i = tape i := by
          simp only [tape₁]
          rw [if_neg (by omega : i ≠ p)]
        rw [h', htape₁_i]
      · intro i hi
        have hi₁ : p + 1 + (k : ℤ) < i := by omega
        have h' := hright' i hi₁
        have htape₁_i : tape₁ i = tape i := by
          simp only [tape₁]
          rw [if_neg (by omega : i ≠ p)]
        rw [h', htape₁_i]

/-- scanRight87 长度版副本（Core1:3914 + 步数账 n+1）。87 @ p 东扫 n 格到 #₀ → 20 @ p+n。 -/
lemma scanRight87_len (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p + (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 87 tape p) π cfg' ∧
      cfg'.state = 20 ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 20, writeSym := tape p, moveDir := Dir.S }
      let step : SymStep := { fromState := 87, readSym := tape p, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      have htrans : step.result ∈ VerifierSym.transition (87, tape p) := by
        simp only [step, r, hbound']
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 87 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 87 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · simp [step]
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · funext i
        by_cases h : i = p <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hd : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 := by
        simpa using (hdata p (by constructor; rfl; omega))
      let r₁ : SymTransResult := { nextState := 87, writeSym := tape p, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 87, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (87, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hd
        rcases hks with hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 87 tape p) [step₁]
          (symStepConfig (SymConfig.mk 87 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 87 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 87 tape p) step₁.result = SymConfig.mk 87 tape (p + 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hdata' : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) →
          (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      have hbound' : tape (p + 1 + (n : ℤ)) = Sym.boundary := by
        rw [show p + 1 + (n : ℤ) = p + ((n + 1 : ℕ) : ℤ) from by omega]
        exact hbound
      rcases ih (p + 1) tape hdata' hbound' with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · simp [hlen']

/-- 84-walk：84 @ p 西跨 n 格（consumed/data0/data1）至 #₀（p−n 位）→ 85 @ p−n−1。
    恰 n+1 步，带保持。 -/
lemma rewind84 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, p - (n : ℤ) + 1 ≤ i ∧ i ≤ p →
      (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p - (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 84 tape p) π cfg' ∧
      cfg'.state = 85 ∧ cfg'.headPos = p - (n : ℤ) - 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 85, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := 84, readSym := tape p, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      have htrans : step.result ∈ VerifierSym.transition (84, tape p) := by
        simp only [step, r, hbound']
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 84 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 84 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · simp [step]
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
        omega
      · funext i
        by_cases h : i = p <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hkp : (tape p).1 = SymKind.consumed ∨ (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 := by
        simpa using (hdata p (by constructor <;> omega))
      let r₁ : SymTransResult := { nextState := 84, writeSym := tape p, moveDir := Dir.L }
      let step₁ : SymStep := { fromState := 84, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (84, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.consumed ∨ ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hkp
        rcases hks with hk | hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 84 tape p) [step₁]
          (symStepConfig (SymConfig.mk 84 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 84 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 84 tape p) step₁.result = SymConfig.mk 84 tape (p - 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hdata' : ∀ i : ℤ, (p - 1) - (n : ℤ) + 1 ≤ i ∧ i ≤ p - 1 →
          (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      have hbound' : tape ((p - 1) - (n : ℤ)) = Sym.boundary := by
        rw [show (p - 1) - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) from by omega]
        exact hbound
      rcases ih (p - 1) tape hdata' hbound' with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · simp [hlen']

/-- 85-walk：85 @ n 西扫数据格（[1, n]）至 #ₗ（0 位）→ 86 @ 1。恰 n+1 步，带保持。 -/
lemma rewind85 (n : ℕ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (n : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape 0 = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 85 tape n) π cfg' ∧
      cfg'.state = 86 ∧ cfg'.headPos = 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing tape with
  | zero =>
      let r : SymTransResult := { nextState := 86, writeSym := tape 0, moveDir := Dir.R }
      let step : SymStep := { fromState := 85, readSym := tape 0, result := r }
      have htrans : step.result ∈ VerifierSym.transition (85, tape 0) := by
        simp only [step, r, hbound]
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 85 tape 0) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 85 tape 0) SymSteps.nil ?_ ?_ ?_
        · rfl
        · simp [step]
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · funext i
        by_cases h : i = 0 <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hdp : (tape (n + 1)).1 = SymKind.data0 ∨ (tape (n + 1)).1 = SymKind.data1 := by
        simpa using (hdata (n + 1) (by constructor <;> omega))
      let r₁ : SymTransResult := { nextState := 85, writeSym := tape (n + 1), moveDir := Dir.L }
      let step₁ : SymStep := { fromState := 85, readSym := tape (n + 1), result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (85, tape (n + 1)) := by
        rcases htp : tape (n + 1) with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hdp
        rcases hks with hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 85 tape (n + 1)) [step₁]
          (symStepConfig (SymConfig.mk 85 tape (n + 1)) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 85 tape (n + 1)) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 85 tape (n + 1)) step₁.result = SymConfig.mk 85 tape n := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = (n + 1 : ℤ) <;> simp [h]
      have hdata' : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (n : ℤ) →
          (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      rcases ih tape hdata' hbound with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
      · simp [hlen']

/-- 回卷段 84-87 总装：84 @ p₀+1+n_e 西跨至 #₀（p₀ 位）→ 85 西扫至 #ₗ → 86 清 k 标 →
    87 东扫回 #₀ → 20 @ p₀。恰 n_e + 2·p₀ + 3 步；[1, 1+k) 格清标，其余带保持。 -/
lemma rewind84_87 (p₀ : ℤ) (n_e : ℕ) (k : ℕ) (tape : ℤ → Sym)
    (h84 : ∀ i : ℤ, p₀ + 1 ≤ i ∧ i ≤ p₀ + 1 + (n_e : ℤ) →
      (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hb0 : tape p₀ = Sym.boundary)
    (h85 : ∀ i : ℤ, 1 ≤ i ∧ i ≤ p₀ - 1 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbl : tape 0 = Sym.boundary)
    (hmarked : ∀ i : ℕ, i < k → (tape (1 + (i : ℤ))).2 = true)
    (hstop : (tape (1 + (k : ℤ))).2 = false)
    (hkind : ∀ i : ℤ, 1 ≤ i ∧ i < 1 + (k : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hkindStop : (tape (1 + (k : ℤ))).1 = SymKind.data0 ∨
      (tape (1 + (k : ℤ))).1 = SymKind.data1 ∨ (tape (1 + (k : ℤ))).1 = SymKind.boundary)
    (h87 : ∀ i : ℤ, 1 + (k : ℤ) ≤ i ∧ i < p₀ →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hk_le : k ≤ p₀ - 1) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 84 tape (p₀ + 1 + (n_e : ℤ))) π cfg' ∧
      cfg'.state = 20 ∧ cfg'.headPos = p₀ ∧
      π.length = n_e + 2 * (p₀ - 1).toNat + 5 ∧
      (∀ i : ℕ, i < k → cfg'.tape (1 + (i : ℤ)) = Sym.mk (tape (1 + (i : ℤ))).1 false) ∧
      (∀ i : ℤ, i < 1 ∨ 1 + (k : ℤ) ≤ i → cfg'.tape i = tape i) := by
  rcases rewind84 (n_e + 1) (p₀ + 1 + (n_e : ℤ)) tape
      (by
        intro i hi
        exact h84 i (by constructor <;> omega))
      (by
        rw [show p₀ + 1 + (n_e : ℤ) - ((n_e + 1 : ℕ) : ℤ) = p₀ from by omega]
        exact hb0) with ⟨π₁, cfg₁, h₁, hst₁, hhead₁, htape₁, hlen₁⟩
  have hp₀pos : 0 ≤ p₀ - 1 := by omega
  have hhead₁' : cfg₁.headPos = p₀ - 1 := by
    rw [hhead₁]
    omega
  have htoNat₁ : (Int.toNat (p₀ - 1) : ℤ) = p₀ - 1 := by
    rw [Int.toNat_of_nonneg hp₀pos]
  have hcfg₁_eq : cfg₁ = SymConfig.mk 85 tape ((Int.toNat (p₀ - 1) : ℤ)) := by
    rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
    rw [hst₁, htape₁, hhead₁', htoNat₁]
  rcases rewind85 (Int.toNat (p₀ - 1)) tape
      (by
        intro i hi
        rw [Int.toNat_of_nonneg hp₀pos] at hi
        exact h85 i hi)
      hbl with ⟨π₂, cfg₂, h₂, hst₂, hhead₂, htape₂, hlen₂⟩
  have h₂' : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
    simpa [hcfg₁_eq] using h₂
  have hhead₂' : cfg₂.headPos = 1 := hhead₂
  have hcfg₂_eq : cfg₂ = SymConfig.mk 86 tape 1 := by
    rw [show cfg₂ = SymConfig.mk cfg₂.state cfg₂.tape cfg₂.headPos from rfl]
    rw [hst₂, htape₂, hhead₂']
  have hmarked' : ∀ i : ℕ, i < k → (tape (1 + (i : ℤ))).2 = true := hmarked
  rcases clearMark86_len k 1 tape hmarked' hstop
      (by
        intro i hi
        exact hkind i hi)
      hkindStop with ⟨π₃, cfg₃, h₃, hst₃, hhead₃, hlen₃, hclear₃, hkeep₃, hkeepL₃, hkeepR₃⟩
  have h₃' : SymSteps VerifierSym.transition cfg₂ π₃ cfg₃ := by
    simpa [hcfg₂_eq] using h₃
  have hhead₃' : cfg₃.headPos = 1 + (k : ℤ) := hhead₃
  have hcfg₃_eq : cfg₃ = SymConfig.mk 87 cfg₃.tape (1 + (k : ℤ)) := by
    rw [show cfg₃ = SymConfig.mk cfg₃.state cfg₃.tape cfg₃.headPos from rfl]
    rw [hst₃, hhead₃']
  have hkpos : 0 ≤ p₀ - 1 - (k : ℤ) := by omega
  rcases scanRight87_len (Int.toNat (p₀ - 1 - (k : ℤ))) (1 + (k : ℤ)) cfg₃.tape
      (by
        intro i hi
        rcases hi with ⟨hlo, hhi⟩
        rw [Int.toNat_of_nonneg hkpos] at hhi
        have hcell : (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 :=
          h87 i ⟨by omega, by omega⟩
        have hkept : cfg₃.tape i = tape i := by
          by_cases hie : i = 1 + (k : ℤ)
          · subst i
            exact hkeep₃
          · exact (hkeepR₃ i (by omega))
        rwa [hkept])
      (by
        have hcell : cfg₃.tape (1 + (k : ℤ) + ↑((p₀ - 1 - (k : ℤ)).toNat)) = tape p₀ := by
          rw [Int.toNat_of_nonneg hkpos]
          have hpos : 1 + (k : ℤ) + (p₀ - 1 - (k : ℤ)) = p₀ := by omega
          rw [hpos]
          by_cases hie : p₀ = 1 + (k : ℤ)
          · subst p₀
            exact hkeep₃
          · exact (hkeepR₃ p₀ (by omega))
        rw [hcell, hb0]) with ⟨π₄, cfg₄, h₄, hst₄, hhead₄, htape₄, hlen₄⟩
  have h₄' : SymSteps VerifierSym.transition cfg₃ π₄ cfg₄ := by
    rw [hcfg₃_eq]
    exact h₄
  refine ⟨π₁ ++ π₂ ++ π₃ ++ π₄, cfg₄, ?_, hst₄, ?_, ?_, ?_, ?_⟩
  · exact symSteps_append_concat ((π₁ ++ π₂) ++ π₃) π₄
      (symSteps_append_concat (π₁ ++ π₂) π₃
        (symSteps_append_concat π₁ π₂ h₁ h₂') h₃') h₄'
  · rw [hhead₄, Int.toNat_of_nonneg hkpos]
    omega
  · rw [List.length_append, List.length_append, List.length_append, hlen₁, hlen₂, hlen₃, hlen₄]
    have htoNat₂ : ↑((p₀ - 1 - ↑k).toNat) = p₀ - 1 - ↑k := by
      rw [Int.toNat_of_nonneg hkpos]
    have hsplit : (p₀ - 1).toNat = k + (p₀ - 1 - ↑k).toNat := by
      rw [← Nat.cast_inj (R := ℤ)]
      rw [Nat.cast_add, htoNat₁, htoNat₂]
      omega
    rw [hsplit]
    omega
  · intro i hi
    rw [htape₄]
    exact hclear₃ i hi
  · intro i hi
    rw [htape₄]
    rcases hi with hlo | hik
    · exact hkeepL₃ i hlo
    · by_cases hie : i = 1 + (k : ℤ)
      · subst i
        exact hkeep₃
      · exact (hkeepR₃ i (by omega))

/-! ## 走带族（轮段：76/8 西扫、77/9、计数器 12、借位 14、返扫 81、走廊 13）

语义依据：转移表 Core:440-490（5 读位写 c- → 76/8 西扫 → 77/9 → 10/12 计数器 →
11/14 借位 → 81 返扫 → 13 走廊 → 5/84）。算术件复用 Core1：
`borrow_matches_subOne`/`subtract_one_matches_subOne`/`subOneAt`/`subAllBitsAt`/`targetTape`。
长度界只求粗略（每 bit ≤ 2j+3|tb|+9；链 ≤ L·(L+3|tb|+9)+1）。 -/

/-- 76-西扫（减路径）：跨 consumed/data0/data1 至 #₀ → 77。 -/
lemma fire_west76 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, p - (n : ℤ) + 1 ≤ i ∧ i ≤ p →
      (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p - (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 76 tape p) π cfg' ∧
      cfg'.state = 77 ∧ cfg'.headPos = p - (n : ℤ) - 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 77, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := 76, readSym := tape p, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      have htrans : step.result ∈ VerifierSym.transition (76, tape p) := by
        simp only [step, r, hbound']
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 76 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 76 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
        omega
      · funext i
        by_cases h : i = p <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hkp : (tape p).1 = SymKind.consumed ∨ (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 := by
        simpa using (hdata p (by constructor <;> omega))
      let r₁ : SymTransResult := { nextState := 76, writeSym := tape p, moveDir := Dir.L }
      let step₁ : SymStep := { fromState := 76, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (76, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.consumed ∨ ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hkp
        rcases hks with hk | hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 76 tape p) [step₁]
          (symStepConfig (SymConfig.mk 76 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 76 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 76 tape p) step₁.result = SymConfig.mk 76 tape (p - 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hdata' : ∀ i : ℤ, (p - 1) - (n : ℤ) + 1 ≤ i ∧ i ≤ p - 1 →
          (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      have hbound' : tape ((p - 1) - (n : ℤ)) = Sym.boundary := by
        rw [show (p - 1) - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) from by omega]
        exact hbound
      rcases ih (p - 1) tape hdata' hbound' with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · simp [hlen']

/-- 8-西扫（记位路径）：跨 consumed/data0/data1 至 #₀ → 9。 -/
lemma fire_west8 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, p - (n : ℤ) + 1 ≤ i ∧ i ≤ p →
      (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape (p - (n : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 8 tape p) π cfg' ∧
      cfg'.state = 9 ∧ cfg'.headPos = p - (n : ℤ) - 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 9, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := 8, readSym := tape p, result := r }
      have hbound' : tape p = Sym.boundary := by simpa using hbound
      have htrans : step.result ∈ VerifierSym.transition (8, tape p) := by
        simp only [step, r, hbound']
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 8 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 8 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
        omega
      · funext i
        by_cases h : i = p <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hkp : (tape p).1 = SymKind.consumed ∨ (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 := by
        simpa using (hdata p (by constructor <;> omega))
      let r₁ : SymTransResult := { nextState := 8, writeSym := tape p, moveDir := Dir.L }
      let step₁ : SymStep := { fromState := 8, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (8, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.consumed ∨ ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hkp
        rcases hks with hk | hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 8 tape p) [step₁]
          (symStepConfig (SymConfig.mk 8 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 8 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 8 tape p) step₁.result = SymConfig.mk 8 tape (p - 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hdata' : ∀ i : ℤ, (p - 1) - (n : ℤ) + 1 ≤ i ∧ i ≤ p - 1 →
          (tape i).1 = SymKind.consumed ∨ (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      have hbound' : tape ((p - 1) - (n : ℤ)) = Sym.boundary := by
        rw [show (p - 1) - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) from by omega]
        exact hbound
      rcases ih (p - 1) tape hdata' hbound' with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · simp [hlen']

/-- 77-西扫（减路径，至 #ₗ）：跨 data0/data1 至 0 的 #ₗ → 10 @ 1。 -/
lemma fire_west77 (n : ℕ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (n : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape 0 = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 77 tape (n : ℤ)) π cfg' ∧
      cfg'.state = 10 ∧ cfg'.headPos = 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing tape with
  | zero =>
      let r : SymTransResult := { nextState := 10, writeSym := tape 0, moveDir := Dir.R }
      let step : SymStep := { fromState := 77, readSym := tape 0, result := r }
      have htrans : step.result ∈ VerifierSym.transition (77, tape 0) := by
        simp only [step, r, hbound]
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 77 tape 0) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 77 tape 0) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · funext i
        by_cases h : i = 0 <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hdp : (tape (n + 1)).1 = SymKind.data0 ∨ (tape (n + 1)).1 = SymKind.data1 := by
        simpa using (hdata (n + 1) (by constructor <;> omega))
      let r₁ : SymTransResult := { nextState := 77, writeSym := tape (n + 1), moveDir := Dir.L }
      let step₁ : SymStep := { fromState := 77, readSym := tape (n + 1), result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (77, tape (n + 1)) := by
        rcases htp : tape (n + 1) with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hdp
        rcases hks with hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 77 tape (n + 1)) [step₁]
          (symStepConfig (SymConfig.mk 77 tape (n + 1)) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 77 tape (n + 1)) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 77 tape (n + 1)) step₁.result = SymConfig.mk 77 tape n := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = (n + 1 : ℤ) <;> simp [h]
      have hdata' : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (n : ℤ) →
          (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      rcases ih tape hdata' hbound with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
      · simp [hlen']

/-- 9-西扫（记位路径，至 #ₗ）：跨 data0/data1 至 0 的 #ₗ → 12 @ 1。 -/
lemma fire_west9 (n : ℕ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (n : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbound : tape 0 = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 9 tape (n : ℤ)) π cfg' ∧
      cfg'.state = 12 ∧ cfg'.headPos = 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing tape with
  | zero =>
      let r : SymTransResult := { nextState := 12, writeSym := tape 0, moveDir := Dir.R }
      let step : SymStep := { fromState := 9, readSym := tape 0, result := r }
      have htrans : step.result ∈ VerifierSym.transition (9, tape 0) := by
        simp only [step, r, hbound]
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 9 tape 0) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 9 tape 0) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · funext i
        by_cases h : i = 0 <;> simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hdp : (tape (n + 1)).1 = SymKind.data0 ∨ (tape (n + 1)).1 = SymKind.data1 := by
        simpa using (hdata (n + 1) (by constructor <;> omega))
      let r₁ : SymTransResult := { nextState := 9, writeSym := tape (n + 1), moveDir := Dir.L }
      let step₁ : SymStep := { fromState := 9, readSym := tape (n + 1), result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (9, tape (n + 1)) := by
        rcases htp : tape (n + 1) with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hdp
        rcases hks with hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 9 tape (n + 1)) [step₁]
          (symStepConfig (SymConfig.mk 9 tape (n + 1)) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 9 tape (n + 1)) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 9 tape (n + 1)) step₁.result = SymConfig.mk 9 tape n := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = (n + 1 : ℤ) <;> simp [h]
      have hdata' : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (n : ℤ) →
          (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
        intro i hi
        exact hdata i (by constructor <;> omega)
      rcases ih tape hdata' hbound with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
      · simp [hlen']

/-- 12-计数器（记位路径）：R 扫 k 个已标格 → 第一个未标格标 m=1 → 81（R）。 -/
lemma counter12 (k : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hmarked : ∀ i : ℕ, i < k → (tape (p + (i : ℤ))).2 = true ∧
      ((tape (p + (i : ℤ))).1 = SymKind.data0 ∨ (tape (p + (i : ℤ))).1 = SymKind.data1))
    (hstop : (tape (p + (k : ℤ))).2 = false ∧
      ((tape (p + (k : ℤ))).1 = SymKind.data0 ∨ (tape (p + (k : ℤ))).1 = SymKind.data1)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 12 tape p) π cfg' ∧
      cfg'.state = 81 ∧ cfg'.headPos = p + (k : ℤ) + 1 ∧
      (∀ i : ℕ, i < k → cfg'.tape (p + (i : ℤ)) = tape (p + (i : ℤ))) ∧
      cfg'.tape (p + (k : ℤ)) = Sym.mk (tape (p + (k : ℤ))).1 true ∧
      (∀ i : ℤ, (i < p ∨ p + (k : ℤ) < i) → cfg'.tape i = tape i) ∧
      π.length = k + 1 := by
  induction k generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 81, writeSym := Sym.mk (tape p).1 true, moveDir := Dir.R }
      let step : SymStep := { fromState := 12, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (12, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hms : ms = false := by simpa [Sym.mk, htp] using hstop.1
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using hstop.2
        rcases hks with hk | hk <;> subst ks <;> decide
      refine ⟨[step], symStepConfig (SymConfig.mk 12 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 12 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · intro i hi
        omega
      · simp [symStepConfig, step, r]
      · intro i hi
        by_cases h : i = p
        · simp [step, r, h] at *
        · simp [symStepConfig, step, r, h]
      · simp
  | succ k ih =>
      let r₁ : SymTransResult := { nextState := 12, writeSym := tape p, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 12, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (12, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hms : ms = true := by simpa [Sym.mk, htp] using (hmarked 0 (by omega)).1
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [Sym.mk, htp] using (hmarked 0 (by omega)).2
        rcases hks with hk | hk <;> subst ks <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 12 tape p) [step₁]
          (symStepConfig (SymConfig.mk 12 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 12 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 12 tape p) step₁.result = SymConfig.mk 12 tape (p + 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hmarked' : ∀ i : ℕ, i < k → (tape (p + 1 + (i : ℤ))).2 = true ∧
          ((tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (tape (p + 1 + (i : ℤ))).1 = SymKind.data1) := by
        intro i hi
        simpa [add_assoc, add_comm, add_left_comm] using hmarked (i + 1) (by omega)
      have hstop' : (tape (p + 1 + (k : ℤ))).2 = false ∧
          ((tape (p + 1 + (k : ℤ))).1 = SymKind.data0 ∨ (tape (p + 1 + (k : ℤ))).1 = SymKind.data1) := by
        simpa [add_assoc, add_comm, add_left_comm] using hstop
      rcases ih (p + 1) tape hmarked' hstop' with ⟨π', cfg', hsteps', hst', hhead', hkeep', hwrite', hside', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, ?_, ?_, ?_, ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · intro i hi
        rcases Nat.lt_or_ge i 1 with hi0 | hi1
        · have : i = 0 := by omega
          subst i
          simpa using (hside' p (by simp))
        · have hkeepi : cfg'.tape (p + 1 + ((i - 1 : ℕ) : ℤ)) = tape (p + 1 + ((i - 1 : ℕ) : ℤ)) := by
            apply hkeep' (i - 1) (by omega)
          have hpos : p + (i : ℤ) = p + 1 + ((i - 1 : ℕ) : ℤ) := by omega
          rw [hpos]
          exact hkeepi
      · have hwritei : cfg'.tape (p + 1 + (k : ℤ)) = Sym.mk (tape (p + 1 + (k : ℤ))).1 true := by
          exact hwrite'
        have hpos : p + ((k + 1 : ℕ) : ℤ) = p + 1 + (k : ℤ) := by omega
        rw [hpos]
        exact hwritei
      · intro i hi
        rcases hi with hlo | hhi
        · exact hside' i (by left; omega)
        · have hsidei : cfg'.tape i = tape i := by
            apply hside'
            right
            omega
          exact hsidei
      · simp [hlen']


/-- 14-借位链：R 扫 n 个 data0 格（0→1）→ data1 格（1→0）终止 → 81（R）。标位随格保留。 -/
lemma borrow14 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hzeros : ∀ i : ℕ, i < n → (tape (p + (i : ℤ))).1 = SymKind.data0)
    (hone : (tape (p + (n : ℤ))).1 = SymKind.data1) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) π cfg' ∧
      cfg'.state = 81 ∧ cfg'.headPos = p + (n : ℤ) + 1 ∧
      (∀ i : ℕ, i < n → cfg'.tape (p + (i : ℤ)) = Sym.mk SymKind.data1 (tape (p + (i : ℤ))).2) ∧
      cfg'.tape (p + (n : ℤ)) = Sym.mk SymKind.data0 (tape (p + (n : ℤ))).2 ∧
      (∀ i : ℤ, (i < p ∨ p + (n : ℤ) + 1 ≤ i) → cfg'.tape i = tape i) ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 81, writeSym := Sym.mk SymKind.data0 (tape p).2, moveDir := Dir.R }
      let step : SymStep := { fromState := 14, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (14, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        rw [htp]
        have hks : ks = SymKind.data1 := by simpa [Sym.mk, htp] using hone
        subst ks
        cases ms <;> decide
      refine ⟨[step], symStepConfig (SymConfig.mk 14 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 14 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · intro i hi
        omega
      · simp [symStepConfig, step, r]
      · intro i hi
        by_cases h : i = p
        · simp [step, r, h] at *
        · simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hz0 : (tape p).1 = SymKind.data0 := by simpa using hzeros 0 (by omega)
      let r₁ : SymTransResult := { nextState := 14, writeSym := Sym.mk SymKind.data1 (tape p).2, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 14, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (14, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.data0 := by simpa [Sym.mk, htp] using hz0
        subst ks
        cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 14 tape p) [step₁]
          (symStepConfig (SymConfig.mk 14 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 14 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      let tape₁ : ℤ → Sym := fun i => if i = p then Sym.mk SymKind.data1 (tape p).2 else tape i
      have hcfg₁ : symStepConfig (SymConfig.mk 14 tape p) step₁.result = SymConfig.mk 14 tape₁ (p + 1) := by
        simp [symStepConfig, step₁, r₁, tape₁, Dir.toInt]
      have hzeros' : ∀ i : ℕ, i < n → (tape₁ (p + 1 + (i : ℤ))).1 = SymKind.data0 := by
        intro i hi
        rw [show tape₁ (p + 1 + (i : ℤ)) = tape (p + 1 + (i : ℤ)) from by
          dsimp [tape₁]
          rw [if_neg]
          omega]
        simpa [add_assoc, add_comm, add_left_comm] using hzeros (i + 1) (by omega)
      have hone' : (tape₁ (p + 1 + (n : ℤ))).1 = SymKind.data1 := by
        rw [show tape₁ (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ)) from by
          dsimp [tape₁]
          rw [if_neg]
          omega]
        simpa [add_assoc, add_comm, add_left_comm] using hone
      rcases ih (p + 1) tape₁ hzeros' hone' with ⟨π', cfg', hsteps', hst', hhead', hwrites', honew', hside', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, ?_, ?_, ?_, ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · intro i hi
        rcases Nat.lt_or_ge i 1 with hi0 | hi1
        · have : i = 0 := by omega
          subst i
          rw [show p + ↑(0 : ℕ) = p from by simp]
          simpa [tape₁] using (hside' p (by left; omega))
        · have hwi : cfg'.tape (p + 1 + ((i - 1 : ℕ) : ℤ)) = Sym.mk SymKind.data1 (tape₁ (p + 1 + ((i - 1 : ℕ) : ℤ))).2 := by
            apply hwrites' (i - 1) (by omega)
          have hmark : (tape₁ (p + 1 + ((i - 1 : ℕ) : ℤ))).2 = (tape (p + 1 + ((i - 1 : ℕ) : ℤ))).2 := by
            dsimp [tape₁]
            rw [if_neg]
            omega
          have hpos : p + (i : ℤ) = p + 1 + ((i - 1 : ℕ) : ℤ) := by omega
          rw [hpos, ← hmark]
          exact hwi
      · have hw : cfg'.tape (p + 1 + (n : ℤ)) = Sym.mk SymKind.data0 (tape₁ (p + 1 + (n : ℤ))).2 := by
          exact honew'
        have hmark : (tape₁ (p + 1 + (n : ℤ))).2 = (tape (p + 1 + (n : ℤ))).2 := by
          dsimp [tape₁]
          rw [if_neg]
          omega
        have hpos : p + ((n + 1 : ℕ) : ℤ) = p + 1 + (n : ℤ) := by omega
        rw [hpos, ← hmark]
        exact hw
      · intro i hi
        rcases hi with hlo | hhi
        · by_cases h : i = p
          · subst i
            simp [symStepConfig, step₁, r₁] at *
          · rw [show cfg'.tape i = tape₁ i from by
              apply hside'
              left
              omega]
            dsimp [tape₁]
            rw [if_neg h]
        · rw [show cfg'.tape i = tape₁ i from by
            apply hside'
            right
            omega]
          dsimp [tape₁]
          rw [if_neg]
          omega
      · simp [hlen']

/-- 81-返扫：R 扫 n 个 data/boundary 格 → consumed 格 → 13（R，回到已消耗区开头）。 -/
lemma return81 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hdata : ∀ i : ℕ, i < n → (tape (p + (i : ℤ))).1 = SymKind.data0 ∨
      (tape (p + (i : ℤ))).1 = SymKind.data1 ∨ (tape (p + (i : ℤ))).1 = SymKind.boundary)
    (hcons : tape (p + (n : ℤ)) = Sym.consumed) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 81 tape p) π cfg' ∧
      cfg'.state = 13 ∧ cfg'.headPos = p + (n : ℤ) + 1 ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
      let step : SymStep := { fromState := 81, readSym := Sym.consumed, result := r }
      have htrans : step.result ∈ VerifierSym.transition (81, Sym.consumed) := by
        decide
      refine ⟨[step], symStepConfig (SymConfig.mk 81 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 81 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · simp [step, show tape p = Sym.consumed from by simpa using hcons]
        · simp [step, r, show tape p = Sym.consumed from by simpa using hcons]
          exact htrans
      · simp [symStepConfig, step, r, Dir.toInt]
      · funext i
        by_cases h : i = p
        · simp [symStepConfig, step, r, h]
          rw [show tape p = Sym.consumed from by simpa using hcons]
        · simp [symStepConfig, step, r, h]
      · simp
  | succ n ih =>
      have hdp : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨ (tape p).1 = SymKind.boundary := by
        simpa using hdata 0 (by omega)
      let r₁ : SymTransResult := { nextState := 81, writeSym := tape p, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 81, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (81, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        rw [htp]
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 ∨ ks = SymKind.boundary := by
          simpa [Sym.mk, htp] using hdp
        rcases hks with hk | hk | hk <;> subst ks <;> cases ms <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 81 tape p) [step₁]
          (symStepConfig (SymConfig.mk 81 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 81 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 81 tape p) step₁.result = SymConfig.mk 81 tape (p + 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hdata' : ∀ i : ℕ, i < n → (tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨
          (tape (p + 1 + (i : ℤ))).1 = SymKind.data1 ∨ (tape (p + 1 + (i : ℤ))).1 = SymKind.boundary := by
        intro i hi
        simpa [add_assoc, add_comm, add_left_comm] using hdata (i + 1) (by omega)
      have hcons' : tape (p + 1 + (n : ℤ)) = Sym.consumed := by
        simpa [add_assoc, add_comm, add_left_comm] using hcons
      rcases ih (p + 1) tape hdata' hcons' with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · simp [hlen']

/-- 13-走廊：R 扫 n 个 consumed 格 → 下一格 data（→ 5 S）或 sel/nosel/boundary（→ 84 L）。
西侧（i<p）恒保持。 -/
lemma corridor13 (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hcons : ∀ i : ℕ, i < n → tape (p + (i : ℤ)) = Sym.consumed)
    (hexit : (tape (p + (n : ℤ))).1 = SymKind.data0 ∨ (tape (p + (n : ℤ))).1 = SymKind.data1 ∨
      (tape (p + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + (n : ℤ))).1 = SymKind.nosel ∨
      (tape (p + (n : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) π cfg' ∧
      (∀ i : ℕ, i < n → cfg'.tape (p + (i : ℤ)) = tape (p + (i : ℤ))) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      π.length = n + 1 ∧
      ((cfg'.state = 5 ∧ cfg'.headPos = p + (n : ℤ) ∧
        ((tape (p + (n : ℤ))).1 = SymKind.data0 ∨ (tape (p + (n : ℤ))).1 = SymKind.data1) ∧
        cfg'.tape (p + (n : ℤ)) = tape (p + (n : ℤ)) ∧
        (∀ i : ℤ, p + (n : ℤ) < i → cfg'.tape i = tape i)) ∨
      (cfg'.state = 84 ∧ cfg'.headPos = p + (n : ℤ) - 1 ∧
        ((tape (p + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + (n : ℤ))).1 = SymKind.nosel ∨
          (tape (p + (n : ℤ))).1 = SymKind.boundary) ∧
        cfg'.tape (p + (n : ℤ)) = tape (p + (n : ℤ)) ∧
        (∀ i : ℤ, p + (n : ℤ) < i → cfg'.tape i = tape i))) := by
  induction n generalizing p tape with
  | zero =>
      by_cases hd : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1
      · let r : SymTransResult := { nextState := 5, writeSym := tape p, moveDir := Dir.S }
        let step : SymStep := { fromState := 13, readSym := tape p, result := r }
        have htrans : step.result ∈ VerifierSym.transition (13, tape p) := by
          rcases htp : tape p with ⟨ks, ms⟩
          simp only [step, r] at *
          rw [htp]
          have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
            simpa [Sym.mk, htp] using hd
          rcases hks with hk | hk <;> subst ks <;> cases ms <;> decide
        refine ⟨[step], symStepConfig (SymConfig.mk 13 tape p) step.result, ?_, ?_, ?_, ?_, ?_⟩
        · refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · rfl
          · exact htrans
        · intro i hi
          omega
        · intro i hi
          by_cases h : i = p
          · simp [step, r, h] at *
          · simp [symStepConfig, step, r, h]
        · simp
        · left
          refine ⟨rfl, ?_, (by simpa using hd), ?_, ?_⟩
          · simp [symStepConfig, step, r, Dir.toInt]
          · simp [symStepConfig, step, r]
          · intro i hi
            by_cases h : i = p
            · simp [step, r, h] at *
            · simp [symStepConfig, step, r, h]
      · have hsep : (tape p).1 = SymKind.sel ∨ (tape p).1 = SymKind.nosel ∨ (tape p).1 = SymKind.boundary := by
          have hex : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨
              (tape p).1 = SymKind.sel ∨ (tape p).1 = SymKind.nosel ∨ (tape p).1 = SymKind.boundary := by
            simpa using hexit
          rcases hex with h1 | h2 | h3 | h4 | h5
          · exfalso
            exact hd (Or.inl h1)
          · exfalso
            exact hd (Or.inr h2)
          · exact Or.inl h3
          · exact Or.inr (Or.inl h4)
          · exact Or.inr (Or.inr h5)
        let r : SymTransResult := { nextState := 84, writeSym := tape p, moveDir := Dir.L }
        let step : SymStep := { fromState := 13, readSym := tape p, result := r }
        have htrans : step.result ∈ VerifierSym.transition (13, tape p) := by
          rcases htp : tape p with ⟨ks, ms⟩
          simp only [step, r] at *
          rw [htp]
          rcases hsep with hk | hk | hk
          · have hks : ks = SymKind.sel := by simpa [Sym.mk, htp] using hk
            subst ks
            cases ms <;> decide
          · have hks : ks = SymKind.nosel := by simpa [Sym.mk, htp] using hk
            subst ks
            cases ms <;> decide
          · have hks : ks = SymKind.boundary := by simpa [Sym.mk, htp] using hk
            subst ks
            cases ms <;> decide
        refine ⟨[step], symStepConfig (SymConfig.mk 13 tape p) step.result, ?_, ?_, ?_, ?_, ?_⟩
        · refine SymSteps.cons [] step (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
          · rfl
          · rfl
          · exact htrans
        · intro i hi
          omega
        · intro i hi
          by_cases h : i = p
          · simp [step, r, h] at *
          · simp [symStepConfig, step, r, h]
        · simp
        · right
          refine ⟨rfl, ?_, (by simpa using hsep), ?_, ?_⟩
          · simp [symStepConfig, step, r, Dir.toInt]
            omega
          · simp [symStepConfig, step, r]
          · intro i hi
            by_cases h : i = p
            · simp [step, r, h] at *
            · simp [symStepConfig, step, r, h]
  | succ n ih =>
      have hc0 : tape p = Sym.consumed := by simpa using hcons 0 (by omega)
      let r₁ : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 13, readSym := Sym.consumed, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (13, Sym.consumed) := by
        decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) [step₁]
          (symStepConfig (SymConfig.mk 13 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · simp [step₁, hc0]
        · simp [step₁, r₁, hc0]
          exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 13 tape p) step₁.result = SymConfig.mk 13 tape (p + 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = p
        · simp [h]
          rw [hc0]
        · simp [h]
      have hcons' : ∀ i : ℕ, i < n → tape (p + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        simpa [add_assoc, add_comm, add_left_comm] using hcons (i + 1) (by omega)
      have hexit' : (tape (p + 1 + (n : ℤ))).1 = SymKind.data0 ∨ (tape (p + 1 + (n : ℤ))).1 = SymKind.data1 ∨
          (tape (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + 1 + (n : ℤ))).1 = SymKind.nosel ∨
          (tape (p + 1 + (n : ℤ))).1 = SymKind.boundary := by
        simpa [add_assoc, add_comm, add_left_comm] using hexit
      rcases ih (p + 1) tape hcons' hexit' with ⟨π', cfg', hsteps', hkeep', hwest', hlen', hres'⟩
      refine ⟨step₁ :: π', cfg', ?_, ?_, ?_, ?_, ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · intro i hi
        rcases Nat.lt_or_ge i 1 with hi0 | hi1
        · have : i = 0 := by omega
          subst i
          simpa using (hwest' p (by omega))
        · have hkeepi : cfg'.tape (p + 1 + ((i - 1 : ℕ) : ℤ)) = tape (p + 1 + ((i - 1 : ℕ) : ℤ)) := by
            apply hkeep' (i - 1) (by omega)
          have hpos : p + (i : ℤ) = p + 1 + ((i - 1 : ℕ) : ℤ) := by omega
          rw [hpos]
          exact hkeepi
      · intro i hi
        by_cases h : i = p
        · subst i
          simp [symStepConfig, step₁, r₁, hc0] at *
        · rw [show cfg'.tape i = tape i from by
            apply hwest'
            omega]
      · simp [hlen']
      · rcases hres' with h5 | h84
        · rcases h5 with ⟨hst', hhead', hkind', hcell', heast'⟩
          left
          refine ⟨hst', ?_, ?_, ?_, ?_⟩
          · rw [hhead']
            omega
          · simpa [add_assoc, add_comm, add_left_comm] using hkind'
          · have hpos : p + ((n + 1 : ℕ) : ℤ) = p + 1 + (n : ℤ) := by omega
            rw [hpos]
            exact hcell'
          · intro i hi
            rw [show cfg'.tape i = tape i from by
              apply heast'
              omega]
        · rcases h84 with ⟨hst', hhead', hkind', hcell', heast'⟩
          right
          refine ⟨hst', ?_, ?_, ?_, ?_⟩
          · rw [hhead']
            omega
          · simpa [add_assoc, add_comm, add_left_comm] using hkind'
          · have hpos : p + ((n + 1 : ℕ) : ℤ) = p + 1 + (n : ℤ) := by omega
            rw [hpos]
            exact hcell'
          · intro i hi
            rw [show cfg'.tape i = tape i from by
              apply heast'
              omega]

/-- 81 返扫路径上各格（目标尾/垫/#₀/α 格）的 kind ∈ {data0, data1, boundary}。 -/
lemma walk_cell_kind (p_t p_e : ℤ) (tbits : List Bool) (j : ℕ) (tape : ℤ → Sym)
    (htarget : tapeAgrees tape p_t (targetTape j tbits))
    (hbound : tape (p_e - 1) = Sym.boundary)
    (hpad : ∀ i : ℤ, p_t + (tbits.length : ℤ) ≤ i ∧ i < p_e - 1 → tape i = Sym.data0)
    (hsel : (tape p_e).1 = SymKind.data0 ∨ (tape p_e).1 = SymKind.data1)
    (x : ℤ) (hlo : p_t + (j : ℤ) + 1 ≤ x) (hhi : x < p_e + 1) :
    (tape x).1 = SymKind.data0 ∨ (tape x).1 = SymKind.data1 ∨ (tape x).1 = SymKind.boundary := by
  by_cases hlow : x < p_t + (tbits.length : ℤ)
  · have hidx : ∃ i₀ : ℕ, i₀ < tbits.length ∧ x = p_t + (i₀ : ℤ) := by
      use Int.toNat (x - p_t)
      constructor
      · have htoNat : ↑((x - p_t).toNat) = x - p_t := by
          rw [Int.toNat_of_nonneg (by omega)]
        omega
      · rw [Int.toNat_of_nonneg (by omega)]
        omega
    rcases hidx with ⟨i₀, hi₀lt, hi₀eq⟩
    have hm : tape x ∈ targetTape j tbits := by
      rw [hi₀eq]
      have hget := htarget i₀ (by simpa [targetTape_length] using hi₀lt)
      rw [hget]
      exact List.getElem_mem (by simpa [targetTape_length] using hi₀lt)
    dsimp [targetTape] at hm
    rw [List.mem_append] at hm
    rcases hm with htake | hdrop
    · rw [List.mem_map] at htake
      rcases htake with ⟨bb, hbbmem, hbbs⟩
      rw [← hbbs]
      by_cases hbbv : bb
      · simp [hbbv]
        right
        left
        rfl
      · simp [hbbv]
        left
        rfl
    · rw [bitsToSym] at hdrop
      rw [List.mem_map] at hdrop
      rcases hdrop with ⟨bb, hbbmem, hbbs⟩
      rw [← hbbs]
      by_cases hbbv : bb <;> simp [hbbv]
  · by_cases hpadx : x < p_e - 1
    · have hx := hpad x (by constructor <;> omega)
      rw [hx]
      exact Or.inl rfl
    · by_cases hb0 : x = p_e - 1
      · rw [hb0, hbound]
        exact Or.inr (Or.inr rfl)
      · have hxeq : x = p_e := by omega
        rw [hxeq]
        rcases hsel with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)

/-- 13-走廊停格版：R 扫 n 个 consumed 格 → 13 @ p+n（不读尾格，纸带全保持）。 -/
lemma corridor13_stop (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hcons : ∀ i : ℕ, i < n → tape (p + (i : ℤ)) = Sym.consumed) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) π cfg' ∧
      cfg'.state = 13 ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape ∧
      π.length = n := by
  induction n generalizing p tape with
  | zero =>
      refine ⟨[], SymConfig.mk 13 tape p, SymSteps.nil, rfl, ?_, rfl, ?_⟩
      · simp
      · simp
  | succ n ih =>
      let r₁ : SymTransResult := { nextState := 13, writeSym := Sym.consumed, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 13, readSym := Sym.consumed, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (13, Sym.consumed) := by
        decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 13 tape p) [step₁]
          (symStepConfig (SymConfig.mk 13 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 13 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · have hc0 : tape p = Sym.consumed := by simpa using hcons 0 (by omega)
          simp [step₁, hc0]
        · have hc0 : tape p = Sym.consumed := by simpa using hcons 0 (by omega)
          simp [step₁, r₁, hc0]
          exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 13 tape p) step₁.result = SymConfig.mk 13 tape (p + 1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = p
        · simp [h]
          have hc0 : tape p = Sym.consumed := by simpa using hcons 0 (by omega)
          rw [hc0]
        · simp [h]
      have hcons' : ∀ i : ℕ, i < n → tape (p + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        simpa [add_assoc, add_comm, add_left_comm] using hcons (i + 1) (by omega)
      rcases ih (p + 1) tape hcons' with ⟨π', cfg', hsteps', hst', hhead', htape', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, htape', ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · simp [hlen']


/-! ============================================================
## 转向件（备用）：转向数 ≤ 2 × 状态改变步数

支点（R11 δ-19-15c-12 `selfLoop_moveDir_unique`，@R11:1725）：同一状态的自环步方向唯一
⇒ 相邻两个「状态不变步」方向必相同；故每个转向都必与某个「状态改变步」相邻
⇒ 转向数 ≤ 2 × 状态改变步数。

用途（备用）：注入阶段若需转向界（hturn）时取用；本件对算路径层面、无实例依赖。

依赖：`SymChained`（StepBound:5216）、`selfLoop_moveDir_unique`（R11:1725）、
      `legalStates_lt_102`（R11）、`VerifierSym.transition`/`SymStep`（Core）。
-/
set_option maxRecDepth 200000

/-- 状态改变指示子（0/1）：`nextState ≠ fromState`。 -/
def scInd (st : SymStep) : ℕ := if st.result.nextState = st.fromState then 0 else 1

/-- 转向指示子（0/1）：相邻两步方向不同。 -/
def flipInd (x y : SymStep) : ℕ := if x.result.moveDir = y.result.moveDir then 0 else 1

/-- 相邻对求和：`pairSum g [x,y,z] = g x y + g y z`。 -/
def pairSum (g : SymStep → SymStep → ℕ) : List SymStep → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: t => g x y + pairSum g (y :: t)

/-- 单步指示函数之和。 -/
def sumF (f : SymStep → ℕ) : List SymStep → ℕ
  | [] => 0
  | x :: t => f x + sumF f t

/-- 表级支点：非合法状态的转移恒为陷阱 `101`。 -/
lemma fromState_mem_legalStates {q : ℕ} {s : Sym} {r : SymTransResult}
    (h : r ∈ VerifierSym.transition (q, s)) (h101 : r.nextState ≠ 101) :
    q ∈ VerifierSym.legalStates := by
  by_contra hq
  have hsub : VerifierSym.transition (q, s) = {⟨101, s, Dir.S⟩} := by
    dsimp only [VerifierSym.transition]
    rw [if_neg hq]
  rw [hsub] at h
  simp only [Finset.mem_singleton] at h
  rw [h] at h101
  exact h101 rfl

/-- 相邻两步皆为自环 ⇒ 方向相同。 -/
lemma selfLoop_pair_same_dir {x y : SymStep}
    (hchain : y.fromState = x.result.nextState)
    (hx : x.result ∈ VerifierSym.transition (x.fromState, x.readSym))
    (hy : y.result ∈ VerifierSym.transition (y.fromState, y.readSym))
    (h101x : x.result.nextState ≠ 101) (h101y : y.result.nextState ≠ 101)
    (hsx : x.result.nextState = x.fromState) (hsy : y.result.nextState = y.fromState) :
    x.result.moveDir = y.result.moveDir := by
  have hqmem : x.fromState ∈ VerifierSym.legalStates := fromState_mem_legalStates hx h101x
  have hqy : y.fromState = x.fromState := by rw [hchain, hsx]
  have hlt : x.fromState < 102 := legalStates_lt_102 x.fromState hqmem
  have hys : y.result.nextState = x.fromState := by rw [hsy, hqy]
  cases hxs : x.readSym with
  | mk k₁ b₁ =>
    cases hys' : y.readSym with
    | mk k₂ b₂ =>
      have hx' : x.result ∈ VerifierSym.transition (((⟨x.fromState, hlt⟩ : Fin 102) : ℕ), (k₁, b₁)) := by
        rw [hxs] at hx
        simpa using hx
      have hy' : y.result ∈ VerifierSym.transition (((⟨x.fromState, hlt⟩ : Fin 102) : ℕ), (k₂, b₂)) := by
        rw [hys'] at hy
        simpa [hqy] using hy
      have hslx : x.result.nextState = ((⟨x.fromState, hlt⟩ : Fin 102) : ℕ) := by rw [hsx]
      have hsly : y.result.nextState = ((⟨x.fromState, hlt⟩ : Fin 102) : ℕ) := by rw [hys]
      exact selfLoop_moveDir_unique k₁ b₁ k₂ b₂ ⟨x.fromState, hlt⟩
        x.result hx' y.result hy' hslx hsly h101x h101y

/-- 相邻对：转向 ≤ 状态改变（x）+ 状态改变（y）。 -/
lemma pair_flip_le_sc {x y : SymStep}
    (hchain : y.fromState = x.result.nextState)
    (hx : x.result ∈ VerifierSym.transition (x.fromState, x.readSym))
    (hy : y.result ∈ VerifierSym.transition (y.fromState, y.readSym))
    (h101x : x.result.nextState ≠ 101) (h101y : y.result.nextState ≠ 101) :
    flipInd x y ≤ scInd x + scInd y := by
  unfold flipInd scInd
  by_cases hdir : x.result.moveDir = y.result.moveDir
  · rw [if_pos hdir]; omega
  · rw [if_neg hdir]
    have hkey : ¬(x.result.nextState = x.fromState ∧ y.result.nextState = y.fromState) := by
      rintro ⟨hsx, hsy⟩
      exact hdir (selfLoop_pair_same_dir hchain hx hy h101x h101y hsx hsy)
    by_cases h1 : x.result.nextState = x.fromState <;>
      by_cases h2 : y.result.nextState = y.fromState
    · exact absurd ⟨h1, h2⟩ hkey
    · rw [if_pos h1, if_neg h2]
    · rw [if_neg h1, if_pos h2]
    · rw [if_neg h1, if_neg h2]; omega

/-- 转向数 = 相邻对转向指示子之和。 -/
theorem symTurnCount_map_moveDir_eq_pairSum : ∀ π : List SymStep,
    symTurnCount (π.map (fun s => s.result.moveDir)) = pairSum flipInd π
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      have ih := symTurnCount_map_moveDir_eq_pairSum (y :: t)
      show (if x.result.moveDir = y.result.moveDir then 0 else 1)
              + symTurnCount ((y :: t).map (fun s => s.result.moveDir))
            = flipInd x y + pairSum flipInd (y :: t)
      rw [ih]
      simp only [flipInd]

/-- 强形式（配对和的精确分解）：`pairSum` ≤ 首步一次 + 其余两次。 -/
theorem pairSum_flip_le_head_add_two (x : SymStep) (t : List SymStep)
    (hch : SymChained (x :: t))
    (hn : ∀ s ∈ (x :: t), s.result.nextState ≠ 101)
    (ht : ∀ s ∈ (x :: t), s.result ∈ VerifierSym.transition (s.fromState, s.readSym)) :
    pairSum flipInd (x :: t) ≤ scInd x + 2 * sumF scInd t := by
  induction t generalizing x with
  | nil => simp [pairSum, sumF]
  | cons y u ih =>
      have hunc : SymChained (x :: y :: u) := hch
      simp only [SymChained] at hch
      obtain ⟨hlink, hcht⟩ := hch
      have hn' : ∀ s ∈ (y :: u), s.result.nextState ≠ 101 :=
        fun s hs => hn s (List.mem_cons_of_mem _ hs)
      have ht' : ∀ s ∈ (y :: u),
          s.result ∈ VerifierSym.transition (s.fromState, s.readSym) :=
        fun s hs => ht s (List.mem_cons_of_mem _ hs)
      have hp : flipInd x y ≤ scInd x + scInd y :=
        pair_flip_le_sc hlink (ht x (by simp)) (ht' y (by simp))
          (hn x (by simp)) (hn' y (by simp))
      have ih' := ih y hcht hn' ht'
      have ih'' : pairSum flipInd (y :: u) ≤ scInd y + 2 * sumF scInd u := by
        simpa [sumF] using ih'
      simp only [pairSum, sumF]
      omega

/-- 转向数 ≤ 2 × 状态改变步数（链上无陷阱路径）。 -/
theorem symTurnCount_le_two_mul_stateChanges :
    ∀ π : List SymStep, SymChained π →
      (∀ s ∈ π, s.result.nextState ≠ 101) →
      (∀ s ∈ π, s.result ∈ VerifierSym.transition (s.fromState, s.readSym)) →
      symTurnCount (π.map (fun s => s.result.moveDir)) ≤ 2 * sumF scInd π := by
  intro π hch hn ht
  cases π with
  | nil => simp [symTurnCount, sumF]
  | cons x t =>
      have hstrong := pairSum_flip_le_head_add_two x t hch hn ht
      rw [symTurnCount_map_moveDir_eq_pairSum]
      simp only [sumF]
      have hstrong' : pairSum flipInd (x :: t) ≤ scInd x + 2 * sumF scInd t := by
        simpa [sumF] using hstrong
      omega


/-! ============================================================
## 表级组：5 步消费与复位闭区（格的消费证据）

① 状态 5 的合法非陷阱步读 `data0`/`data1`（未消费格）；
② 状态 5 的合法非陷阱步写 `consumed`（消费该格）；
③ 「读 `consumed` 却写非 `consumed`」的合法非陷阱步只能是 **21**（全表唯一复位站点，Core:509）；
④ 21/22/23 的合法非陷阱转移（除 `(21, sel/nosel) → 51` 扩展支）不出 `{21,22,23,100}`
   ⇒ **复位后不再出现 5 步**。
-/
set_option maxRecDepth 200000

/-- 表级：状态 5 的合法非陷阱步读 `data0`/`data1`。 -/
theorem transition_five_read_isData (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → (q : ℕ) = 5 → (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级：状态 5 的合法非陷阱步写 `consumed`。 -/
theorem transition_five_write_consumed (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → (q : ℕ) = 5 → r.writeSym.1 = SymKind.consumed := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级：读 `consumed` 却写非 `consumed` 的合法非陷阱步只能是状态 21（唯一复位站点）。 -/
theorem transition_consumed_reset_is_twentyOne (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → s.1 = SymKind.consumed → r.writeSym.1 ≠ SymKind.consumed →
      (q : ℕ) = 21 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级：21/22/23 的合法非陷阱转移（除 `(21, sel/nosel)`）不出 `{21,22,23,100}`。 -/
theorem transition_after_reset_closed (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 →
      ((q : ℕ) = 21 ∨ (q : ℕ) = 22 ∨ (q : ℕ) = 23) →
      ¬((q : ℕ) = 21 ∧ (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel)) →
      (r.nextState = 21 ∨ r.nextState = 22 ∨ r.nextState = 23 ∨ r.nextState = 100) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide


/-! ============================================================
## 表级组：模式锁定（入口锁 / 读锁 / 效应）

由路径模式刻画（2026-09-13）：5 步只出现在减法的「轮」里，且只从 `4`（读 `sel`）
或 `13`（读未消费 `data`）进入；`4/20/51` 的合法读即「模式锁定」（其余读全部落 101）。

① `transition_five_entry`          : 5 只从 `4|sel` 或 `13|data` 进入；
② `transition_four_five_effect`    : `4→5` 写 `data0`、右移（新 5 位置 = 选择符位+1）；
③ `transition_thirteen_five_effect`: `13→5` 写回原符号、原地（新 5 位置 = 停点本身）；
④ `transition_four_read_lock`      : `4` 的非陷阱读 ∈ {sel, nosel}；
⑤ `transition_twenty_read_lock`    : `20` 的非陷阱读 = boundary（#₀）；
⑥ `transition_fiftyOne_read_lock`  : `51` 的非陷阱读 = data0；
⑦ `transition_hundred_closed`      : 100 吸收（合法非陷阱转移只在 100）。
-/
set_option maxRecDepth 200000

/-- 表级：状态 5 的合法非陷阱进入只来自 `4`（读 `sel`）或 `13`（读 `data0/data1`）。 -/
theorem transition_five_entry (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState = 5 →
      ((q : ℕ) = 4 ∧ s.1 = SymKind.sel) ∨
      ((q : ℕ) = 13 ∧ (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级：`4` 的合法非陷阱 5-入口步写 `data0`、右移。 -/
theorem transition_four_five_effect (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState = 5 → (q : ℕ) = 4 → r.writeSym = Sym.data0 ∧ r.moveDir = Dir.R := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级：`13` 的合法非陷阱 5-入口步写回读到的符号、原地（S）。 -/
theorem transition_thirteen_five_effect (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState = 5 → (q : ℕ) = 13 → r.writeSym = s ∧ r.moveDir = Dir.S := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级（模式锁定）：`4` 的合法非陷阱步读 `sel`/`nosel`。 -/
theorem transition_four_read_lock (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → (q : ℕ) = 4 → (s.1 = SymKind.sel ∨ s.1 = SymKind.nosel) := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级（模式锁定）：`20` 的合法非陷阱步读 `boundary`（#₀）。 -/
theorem transition_twenty_read_lock (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → (q : ℕ) = 20 → s.1 = SymKind.boundary := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级（模式锁定）：`51` 的合法非陷阱步读 `data0`。 -/
theorem transition_fiftyOne_read_lock (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → (q : ℕ) = 51 → s.1 = SymKind.data0 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide

/-- 表级：`100` 的合法非陷阱转移只在 100（吸收）。 -/
theorem transition_hundred_closed (s : Sym) :
    ∀ (q : Fin 102), ∀ r ∈ VerifierSym.transition ((q : ℕ), s),
      r.nextState ≠ 101 → (q : ℕ) = 100 → r.nextState = 100 := by
  obtain ⟨k, m⟩ := s
  cases m <;> cases k <;> decide



end Mp