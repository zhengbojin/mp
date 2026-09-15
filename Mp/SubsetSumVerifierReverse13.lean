import Mp.SubsetSumVerifierReverse14
import Mp.A1StepBoundBridge

/-!
# R13 · 计算复杂性内容（形式化实施方案 · 语义单位版 v5）

本文件承载**本方案的计算复杂性内容**（新链施工：登记、总装、界）。
素材（表级组 11 / 走带族 15 / 转向件 10）见 `SubsetSumVerifierReverse14`；
阶段绿件（①`segS0` ②`segS1` ③未选`segSrNosel` ④`segS3`）见 `SubsetSumVerifierReverse12`。

## 目标与主定理形

目标：验证器最坏 100 路径步数上界 O(|x|²) 的形式化。

```text
∃ K, ∀ x π,
  ① h100 : π 是 100 路径（运行达 100，非 101/陷阱）
  ② hW   : π 是最坏案例的路径（x ∈ 最坏族：n 全1、全选、和=target；π 为该实例运行路径）
  ⊢ π.length ≤ K·(标记读+1)·(|x|+1)²
```

注（免费条件）：h100 / hW 来自计算复杂性的定义，是保证链条按序展开的**必要条件**——
缺 h100：路径可能偏离落 101；缺 hW：出现分支（位0轮 / 未选 / 直进）。
二者保障链条 `0 → 3 → 4 → … → 4 → 22 → 100` 按序展开、单位形态唯一。作假设、无证明义务。

## 计量口径

成本 := 位移（#L+#R）；S 步零位移、整块吸收（π.length ≤ 3·位移+2）；借位链、计数器不入账；
放宽规则：每条腿 ≤ L；判定 ≤ L。

## 阶段绿件对口（消费路线）

① `segS0`（初始 → 3 @ #₁；≤ N+3 = L+3）；② `segS1`（3 @ #₁ → 4 @ e₁；≤ 2L）；
③ 未选 `segSrNosel`（≤ n+5）；④ `segS3`（22 @ #₁ → 100 @ #ₗ+1；≤ n+2）。
③ 选中支 `segSrSel` = 主体施工（入口 → 轮 → 清尾 → 扩展 → 出口）。
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

/-! ============================================================
## ① α替换段（施工序 ①）——口径底 + A1 注册
============================================================ -/

/- 【注册 · A1】α替换段 = `segS0`（R12，已绿）。
   链式：初始态 **0** →（正常路径：东行一遍，每 α 格写 s/n，止 #₁）→ 结束态 **3**；
   `π.length ≤ N + 3`，其中 `N = (encodeInstanceSym inst).length = L`（= Σb_j + n + t + 3）。
   下游接 ②（`segS1`：状态 3 → 状态 4）。 -/

/-- 位移（成本口径）：全部移动步的移动量之和（`L`/`R` 各计 1，`S` 计 0）。 -/
def symMoves (π : List SymStep) : ℕ :=
  (π.map (fun st => st.result.moveDir.toInt.natAbs)).sum

/-- 单步移动量 ≤ 1。 -/
lemma dir_toInt_natAbs_le_one (d : Dir) : d.toInt.natAbs ≤ 1 := by
  cases d <;> decide

/-- 位移 ≤ 步数（平凡界；S 步被整块吸收前）。 -/
lemma symMoves_le_length (π : List SymStep) : symMoves π ≤ π.length := by
  unfold symMoves
  induction π with
  | nil => simp
  | cons a t ih =>
      have ha : a.result.moveDir.toInt.natAbs ≤ 1 := dir_toInt_natAbs_le_one _
      have ih' : (List.map (fun st => st.result.moveDir.toInt.natAbs) t).sum ≤ t.length := ih
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- 位移的拼接可加性。 -/
lemma symMoves_append (π₁ π₂ : List SymStep) :
    symMoves (π₁ ++ π₂) = symMoves π₁ + symMoves π₂ := by
  simp [symMoves, List.map_append, List.sum_append]

/- 【口径备注 · 已落件】S 吸收（`π.length ≤ 3·位移 + 2`）：见下 ② 。
   【位置界底 · 来源核实】R11：`length_le_of_all_R`（全 R 段长度 ≤ 窗口宽度）、
   `roundPositions_window`（轮段位置 ∈ [lo,hi]）、`symPositions_walk_covers`（走位连续）；
   实例化窗口 [0, N] 于 ③ 施工时进行。 -/

/-! ============================================================
## ② S 吸收件 —— 口径底：`π.length ≤ 3·位移 + 2`

总思路（表级事实 + 纯列表组合）：
* **无 3 连 S**：S 步的（来源态 → 目标态）只在 `{2,10,13,21,86,87} → {3,11,5,22,87,20}`
  出现（非陷阱行）；交集 = `{87}`；`87` 的 S 行唯一目标 = `20`；`20` 无 S 非陷阱行。
  ⇒ 路径中不可能出现 3 连 S。
* **组合**：把 S 步按「已连续 S 数 acc（封顶 2）」记账：`#S ≤ 2·#非S + 2`，
  即 `length ≤ 3·位移 + 2`。
============================================================ -/

/-- 步是否 S（零位移）。 -/
def isS (st : SymStep) : Bool := decide (st.result.moveDir = Dir.S)

/-- `isS` 为真 ⇒ 移动方向是 S。 -/
lemma isS_move (st : SymStep) (h : isS st = true) : st.result.moveDir = Dir.S := by
  simpa [isS] using h

/-- 单步位移值：S → 0，其余 → 1。 -/
lemma move_natAbs_eq (d : Dir) : d.toInt.natAbs = if d = Dir.S then 0 else 1 := by
  cases d <;> decide

lemma move_natAbs_eq' (st : SymStep) :
    st.result.moveDir.toInt.natAbs = if isS st then 0 else 1 := by
  unfold isS
  cases st.result.moveDir <;> decide

/-- 位移在 cons 上的展开。 -/
lemma symMoves_cons (st : SymStep) (t : List SymStep) :
    symMoves (st :: t) = (if isS st then 0 else 1) + symMoves t := by
  unfold symMoves
  simp only [List.map_cons, List.sum_cons]
  rw [move_natAbs_eq' st]

/- ---------- 表级事实：S 步的位置学 ---------- -/

/-- S 步来源态集合（无陷阱行）。 -/
def symSFrom : Finset ℕ := {2, 10, 13, 21, 86, 87}

/-- S 步目标态集合（无陷阱行）。 -/
def symSTo : Finset ℕ := {3, 11, 5, 22, 87, 20}

/-- [表检查 1] 合法行：S 且非陷阱 ⇒ 来源态 ∈ symSFrom（`100` 臂排除自环）。 -/
lemma tab_s_from_leg : ∀ s ∈ VerifierSym.legalStates, ∀ r ∈ (Finset.univ : Finset Sym),
    ∀ res ∈ VerifierSym.transition (s, r), res.moveDir = Dir.S → res.nextState ≠ 101 →
    s ≠ 100 → s ∈ symSFrom := by
  decide

/-- [表检查 2] 合法行：S 且非陷阱 ⇒ 目标态 ∈ symSTo。 -/
lemma tab_s_to_leg : ∀ s ∈ VerifierSym.legalStates, ∀ r ∈ (Finset.univ : Finset Sym),
    ∀ res ∈ VerifierSym.transition (s, r), res.moveDir = Dir.S → res.nextState ≠ 101 →
    s ≠ 100 → res.nextState ∈ symSTo := by
  decide

/-- [表检查 3] symSFrom ∩ symSTo = {87}。 -/
lemma tab_s_inter : ∀ s ∈ symSFrom, s ∈ symSTo → s = 87 := by
  decide

/-- [表检查 4] 87 的 S 行（非陷阱）唯一：→ 20。 -/
lemma tab_s87 : ∀ r ∈ (Finset.univ : Finset Sym),
    ∀ res ∈ VerifierSym.transition (87, r), res.moveDir = Dir.S → res.nextState ≠ 101 →
    res.nextState = 20 := by
  decide

/-- [表检查 5] 20 无 S 非陷阱行。 -/
lemma tab_s20 : ∀ r ∈ (Finset.univ : Finset Sym),
    ∀ res ∈ VerifierSym.transition (20, r), res.moveDir = Dir.S → res.nextState ≠ 101 →
    False := by
  decide

/-- 表外状态：唯一行（101 陷阱）。 -/
lemma trans_out_of_table (s : ℕ) (r : Sym) (hs : s ∉ VerifierSym.legalStates) :
    VerifierSym.transition (s, r) = {SymTransResult.mk 101 r Dir.S} := by
  simp [VerifierSym.transition, hs]

/-- [S 步来源] S 且非陷阱 ⇒ 来源态 ∈ symSFrom。 -/
lemma tab_s_from (s : ℕ) (r : Sym) (res : SymTransResult)
    (hmem : res ∈ VerifierSym.transition (s, r)) (hm : res.moveDir = Dir.S)
    (hno : res.nextState ≠ 101) (h100 : s ≠ 100) : s ∈ symSFrom := by
  by_cases hs : s ∈ VerifierSym.legalStates
  · exact tab_s_from_leg s hs r (Finset.mem_univ r) res hmem hm hno h100
  · have htr := trans_out_of_table s r hs
    rw [htr] at hmem
    simp at hmem
    rw [hmem] at hno
    exact absurd rfl hno

/-- [S 步目标] S 且非陷阱 ⇒ 目标态 ∈ symSTo。 -/
lemma tab_s_to (s : ℕ) (r : Sym) (res : SymTransResult)
    (hmem : res ∈ VerifierSym.transition (s, r)) (hm : res.moveDir = Dir.S)
    (hno : res.nextState ≠ 101) (h100 : s ≠ 100) : res.nextState ∈ symSTo := by
  by_cases hs : s ∈ VerifierSym.legalStates
  · exact tab_s_to_leg s hs r (Finset.mem_univ r) res hmem hm hno h100
  · have htr := trans_out_of_table s r hs
    rw [htr] at hmem
    simp at hmem
    rw [hmem] at hno
    exact absurd rfl hno

/-- [无 3 连 S · 单组] 三步均为 S 且逐步合法、首尾相接（非陷阱、非 100 自环）⇒ 矛盾。 -/
lemma step_triple (st1 st2 st3 : SymStep)
    (h1 : st1.result ∈ VerifierSym.transition (st1.fromState, st1.readSym))
    (h2 : st2.result ∈ VerifierSym.transition (st2.fromState, st2.readSym))
    (h3 : st3.result ∈ VerifierSym.transition (st3.fromState, st3.readSym))
    (hn1 : st1.result.nextState ≠ 101) (hn2 : st2.result.nextState ≠ 101)
    (hn3 : st3.result.nextState ≠ 101)
    (hd1 : st1.fromState ≠ 100) (hd2 : st2.fromState ≠ 100) (hd3 : st3.fromState ≠ 100)
    (hc12 : st2.fromState = st1.result.nextState)
    (hc23 : st3.fromState = st2.result.nextState)
    (hs1 : isS st1 = true) (hs2 : isS st2 = true) (hs3 : isS st3 = true) : False := by
  have m1 := isS_move st1 hs1
  have m2 := isS_move st2 hs2
  have m3 := isS_move st3 hs3
  have kt1 : st1.result.nextState ∈ symSTo :=
    tab_s_to st1.fromState st1.readSym st1.result h1 m1 hn1 hd1
  have k2 : st2.fromState ∈ symSFrom :=
    tab_s_from st2.fromState st2.readSym st2.result h2 m2 hn2 hd2
  have kt2 : st2.fromState ∈ symSTo := by
    rw [hc12]; exact kt1
  have h87 : st2.fromState = 87 := tab_s_inter st2.fromState k2 kt2
  have h2' : st2.result ∈ VerifierSym.transition (87, st2.readSym) := by
    rw [h87] at h2; exact h2
  have h20 : st2.result.nextState = 20 :=
    tab_s87 st2.readSym (Finset.mem_univ _) st2.result h2' m2 hn2
  have h320 : st3.fromState = 20 := by
    rw [hc23, h20]
  have h3' : st3.result ∈ VerifierSym.transition (20, st3.readSym) := by
    rw [h320] at h3; exact h3
  exact tab_s20 st3.readSym (Finset.mem_univ _) st3.result h3' m3 hn3

/- ---------- 组合：「acc 记账」谓词与界 ---------- -/

/-- 无 3 连 S 的结构化谓词（递归形，供组合证明归纳）。 -/
def symWindows : List SymStep → Prop
  | [] => True
  | [_] => True
  | _ :: _ :: [] => True
  | a :: b :: c :: t => ¬ (isS a = true ∧ isS b = true ∧ isS c = true) ∧ symWindows (b :: c :: t)

/-- 递归窗口 ⇒ 退尾一步。 -/
lemma symWindows_tail (x : SymStep) (l : List SymStep) (h : symWindows (x :: l)) :
    symWindows l := by
  cases l with
  | nil => trivial
  | cons b t =>
      cases t with
      | nil => trivial
      | cons c u => exact h.2

/-- 递归窗口 ⇒ 右段。 -/
lemma symWindows_append_right (a b : List SymStep) (h : symWindows (a ++ b)) :
    symWindows b := by
  induction a with
  | nil => simpa using h
  | cons x a' ih => exact ih (symWindows_tail x (a' ++ b) h)

/-- 逐位（点式）无 3 连 S ⇒ 递归窗口。 -/
lemma symWindows_of_pointwise (l : List SymStep)
    (hw : ∀ i (hi : i + 2 < l.length),
      ¬ (isS (l.get ⟨i, by omega⟩) = true ∧ isS (l.get ⟨i + 1, by omega⟩) = true ∧
         isS (l.get ⟨i + 2, by omega⟩) = true)) :
    symWindows l := by
  induction l with
  | nil => trivial
  | cons a t ih =>
      cases t with
      | nil => trivial
      | cons b u =>
          cases u with
          | nil => trivial
          | cons c v =>
              refine ⟨?_, ih ?_⟩
              · have h0 := hw 0 (by simp only [List.length_cons]; omega)
                simpa [List.getElem_cons_zero, List.getElem_cons_succ] using h0
              · intro i hi
                have h' := hw (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
                simpa [List.getElem_cons_succ] using h'

/-- 链 ⇒ 逐位相接（相邻两步：后者起点态 = 前者终点态）。 -/
lemma symChained_get {l : List SymStep} (hc : SymChained l) :
    ∀ i (hi : i + 1 < l.length),
      (l.get ⟨i + 1, by omega⟩).fromState = (l.get ⟨i, by omega⟩).result.nextState := by
  induction l with
  | nil => intro i hi; simp only [List.length_nil] at hi; omega
  | cons a t ih =>
      cases t with
      | nil => intro i hi; simp only [List.length_cons, List.length_nil] at hi; omega
      | cons b u =>
          intro i hi
          have hc' := hc
          simp only [SymChained] at hc'
          cases i with
          | zero =>
              simpa [List.getElem_cons_zero, List.getElem_cons_succ] using hc'.1
          | succ j =>
              have hj : j + 1 < (b :: u).length := by
                simp only [List.length_cons] at hi ⊢; omega
              simpa [List.getElem_cons_succ] using ih hc'.2 j hj

/-- [SymSteps ⇒ 递归窗口] 无陷阱（next ≠ 101）、无 100 自环（from ≠ 100）⇒ 无 3 连 S。 -/
lemma symWindows_of_symSteps {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hno101 : ∀ st ∈ π, st.result.nextState ≠ 101)
    (h100 : ∀ st ∈ π, st.fromState ≠ 100) :
    symWindows π := by
  have hch : SymChained π := (SymChained_of_symSteps h).1
  apply symWindows_of_pointwise
  intro i hi
  rintro ⟨hs1, hs2, hs3⟩
  have hi1 : i < π.length := by omega
  have hi2 : i + 1 < π.length := by omega
  have hi3 : i + 2 < π.length := by omega
  have hmem1 : π.get ⟨i, hi1⟩ ∈ π := List.getElem_mem hi1
  have hmem2 : π.get ⟨i + 1, hi2⟩ ∈ π := List.getElem_mem hi2
  have hmem3 : π.get ⟨i + 2, hi3⟩ ∈ π := List.getElem_mem hi3
  exact step_triple (π.get ⟨i, hi1⟩) (π.get ⟨i + 1, hi2⟩) (π.get ⟨i + 2, hi3⟩)
    (mem_transition_of_symSteps h _ hmem1)
    (mem_transition_of_symSteps h _ hmem2)
    (mem_transition_of_symSteps h _ hmem3)
    (hno101 _ hmem1) (hno101 _ hmem2) (hno101 _ hmem3)
    (h100 _ hmem1) (h100 _ hmem2) (h100 _ hmem3)
    (symChained_get hch i hi2)
    (symChained_get hch (i + 1) hi3)
    hs1 hs2 hs3

/-- 「acc 记账」：acc = 此前连续 S 数（封顶 2）；谓词断言此后无 3 连 S。 -/
def symG : ℕ → List SymStep → Prop
  | _, [] => True
  | acc, st :: t => (acc = 2 → isS st = false) ∧
      symG (if isS st then min 2 (acc + 1) else 0) t

/-- [组合主件] 递归窗口 + 上下文 acc ⇒ symG。 -/
lemma symG_of_windows : ∀ (pre l : List SymStep), pre.length ≤ 2 →
    (∀ st ∈ pre, isS st = true) → symWindows (pre ++ l) → symG pre.length l := by
  intro pre l
  induction l generalizing pre with
  | nil => intro _ _ _; simp [symG]
  | cons st t ih =>
      intro hlen hpreS hw
      rcases pre with _ | ⟨p0, _ | ⟨p1, pre2⟩⟩
      · -- pre = []
        have hwt : symWindows (st :: t) := hw
        simp only [symG, List.length_nil]
        by_cases hst : isS st = true
        · have hpreS' : ∀ x ∈ [st], isS x = true := by
            intro x hx
            rcases List.mem_singleton.mp hx with rfl
            exact hst
          have hsub := ih [st] (by simp) hpreS' (by simpa using hwt)
          refine ⟨?_, ?_⟩
          · intro h; exact absurd h (by decide)
          · rw [if_pos hst]; exact hsub
        · have hsub := ih [] (by simp) (by simp) (symWindows_tail st t hwt)
          refine ⟨?_, ?_⟩
          · intro h; exact absurd h (by decide)
          · rw [if_neg hst]; exact hsub
      · -- pre = [p0]
        have hw0 : symWindows (p0 :: st :: t) := hw
        have hwt : symWindows (st :: t) := symWindows_tail p0 (st :: t) hw0
        simp only [symG, List.length_cons, List.length_nil]
        by_cases hst : isS st = true
        · have hpreS' : ∀ x ∈ [p0, st], isS x = true := by
            intro x hx
            rcases List.mem_cons.mp hx with h | hx2
            · rw [h]; exact hpreS p0 (by simp)
            · rcases List.mem_singleton.mp hx2 with h2
              rw [h2]; exact hst
          have hsub := ih [p0, st] (by simp) hpreS' hw0
          refine ⟨?_, ?_⟩
          · intro h; exact absurd h (by decide)
          · rw [if_pos hst]; exact hsub
        · have hsub := ih [] (by simp) (by simp) (symWindows_tail st t hwt)
          refine ⟨?_, ?_⟩
          · intro h; exact absurd h (by decide)
          · rw [if_neg hst]; exact hsub
      · -- pre = p0 :: p1 :: pre2
        cases pre2 with
        | nil =>
            have hw1 : symWindows (p0 :: p1 :: st :: t) := hw
            have hwt : symWindows t :=
              symWindows_tail st t (symWindows_tail p1 (st :: t)
                (symWindows_tail p0 (p1 :: st :: t) hw1))
            refine ⟨?_, ?_⟩
            · intro _
              cases hb : isS st with
              | false => rfl
              | true =>
                  exact absurd ⟨hpreS p0 (by simp), hpreS p1 (by simp), hb⟩ hw1.1
            · by_cases hst : isS st = true
              · have hpreS' : ∀ x ∈ [p1, st], isS x = true := by
                  intro x hx
                  rcases List.mem_cons.mp hx with h | hx2
                  · rw [h]; exact hpreS p1 (by simp)
                  · rcases List.mem_singleton.mp hx2 with h2
                    rw [h2]; exact hst
                have hsub := ih [p1, st] (by simp) hpreS'
                  (symWindows_tail p0 (p1 :: st :: t) hw1)
                rw [if_pos hst]; exact hsub
              · have hsub := ih [] (by simp) (by simp) hwt
                rw [if_neg hst]; exact hsub
        | cons p2 pre3 =>
            simp only [List.length_cons] at hlen
            omega

/-- [组合界] symG ⇒ `acc + length ≤ 3·位移 + 2`。 -/
lemma symG_length_bound : ∀ (acc : ℕ) (l : List SymStep), acc ≤ 2 → symG acc l →
    acc + l.length ≤ 3 * symMoves l + 2 := by
  intro acc l
  induction l generalizing acc with
  | nil => intro hacc _; simpa [symMoves] using hacc
  | cons st t ih =>
      intro hacc hG
      have hG' := hG
      simp only [symG] at hG'
      obtain ⟨h1, h2⟩ := hG'
      rw [symMoves_cons, List.length_cons]
      by_cases hst : isS st = true
      · have hne2 : acc ≠ 2 := by
          intro h2'
          have hc := h1 h2'
          rw [hst] at hc
          exact absurd hc (by decide)
        have hacc1 : acc ≤ 1 := by omega
        have hmin : min 2 (acc + 1) = acc + 1 := Nat.min_eq_right (by omega)
        have h2'' : symG (min 2 (acc + 1)) t := by simpa [hst] using h2
        have hih := ih (min 2 (acc + 1)) (by omega) h2''
        rw [hmin] at hih
        have hmv : (if isS st then 0 else 1) = 0 := by simp [hst]
        rw [hmv]
        omega
      · have hst' : isS st = false := by
          cases hb : isS st with
          | false => rfl
          | true => exact absurd hb hst
        have h2'' : symG 0 t := by simpa [hst'] using h2
        have hih := ih 0 (by omega) h2''
        have hmv : (if isS st then 0 else 1) = 1 := by simp [hst']
        rw [hmv]
        omega

/-- [② 主件 · S 吸收] 无陷阱、无 100 自环的运行路径：`π.length ≤ 3·位移 + 2`。 -/
theorem symLen_le_moves {cfg₀ : SymConfig} {π : List SymStep} {cfg : SymConfig}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hno101 : ∀ st ∈ π, st.result.nextState ≠ 101)
    (h100 : ∀ st ∈ π, st.fromState ≠ 100) :
    π.length ≤ 3 * symMoves π + 2 := by
  have hw := symWindows_of_symSteps h hno101 h100
  have hG : symG 0 π := symG_of_windows [] π (by simp) (by simp) (by simpa using hw)
  have := symG_length_bound 0 π (by simp) hG
  simpa using this

/-! ============================================================
## ③ 逐元素段 · 小件（轮链缺口）

轮链（位 1 路径）：`5|d1`（烧写 c、L）→ `76` 西扫 → `77` 西扫 → `10` 东扫定位
→ `11`（按位减）→ {`81` 直达 | `14` 借位 → `81`} → `13`（扫已消耗区）→ `5`（下一轮）/`84`（清尾）。
素材已有：`fire_west76` / `fire_west77` / `borrow14` / `return81` / `corridor13`（R14）；
本段补缺口小件：入口步（`4|sel→5`）· 烧步（`5|d1→76`）· `ride10` · 11 步（两支）。
============================================================ -/

/-- [入口] 4 读 sel：写 d0、R → `5 @ p+1`（单步）。 -/
lemma step4sel (p : ℤ) (tape : ℤ → Sym) (h : tape p = Sym.sel) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p) π cfg' ∧
      cfg'.state = 5 ∧ cfg'.headPos = p + 1 ∧
      cfg'.tape = (fun i => if i = p then Sym.data0 else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult := { nextState := 5, writeSym := Sym.data0, moveDir := Dir.R }
  let step : SymStep := { fromState := 4, readSym := tape p, result := r }
  have htrans : step.result ∈ VerifierSym.transition (4, tape p) := by
    simp only [step, r, h]
    decide
  refine ⟨[step], symStepConfig (SymConfig.mk 4 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 4 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
  · funext i
    by_cases h₂ : i = p <;> simp [symStepConfig, step, r, h₂]
  · simp

/-- [烧步] 5 读 data1：写 consumed、L → `76 @ p−1`（单步）。 -/
lemma step5burn (p : ℤ) (tape : ℤ → Sym) (h : (tape p).1 = SymKind.data1) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape p) π cfg' ∧
      cfg'.state = 76 ∧ cfg'.headPos = p - 1 ∧
      cfg'.tape = (fun i => if i = p then Sym.consumed else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult := { nextState := 76, writeSym := Sym.consumed, moveDir := Dir.L }
  let step : SymStep := { fromState := 5, readSym := tape p, result := r }
  have htrans : step.result ∈ VerifierSym.transition (5, tape p) := by
    rcases htp : tape p with ⟨ks, ms⟩
    simp only [step, r] at *
    have hks : ks = SymKind.data1 := by simpa [htp] using h
    subst ks
    cases ms <;> decide
  refine ⟨[step], symStepConfig (SymConfig.mk 5 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 5 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
    omega
  · funext i
    by_cases h₂ : i = p <;> simp [symStepConfig, step, r, h₂]
  · simp

/-- [10 东扫定位] 10 扫 k 个已标记数据格（过）→ 首个未标记数据格：写 m、S → `11 @ p+k`。
    与 `counter12` 同构（差别：停步为 S、目标态 11、终点 p+k）。 -/
lemma ride10 (k : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hmarked : ∀ i : ℕ, i < k → (tape (p + (i : ℤ))).2 = true ∧
      ((tape (p + (i : ℤ))).1 = SymKind.data0 ∨ (tape (p + (i : ℤ))).1 = SymKind.data1))
    (hstop : (tape (p + (k : ℤ))).2 = false ∧
      ((tape (p + (k : ℤ))).1 = SymKind.data0 ∨ (tape (p + (k : ℤ))).1 = SymKind.data1)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 10 tape p) π cfg' ∧
      cfg'.state = 11 ∧ cfg'.headPos = p + (k : ℤ) ∧
      (∀ i : ℕ, i < k → cfg'.tape (p + (i : ℤ)) = tape (p + (i : ℤ))) ∧
      cfg'.tape (p + (k : ℤ)) = Sym.mk (tape (p + (k : ℤ))).1 true ∧
      (∀ i : ℤ, (i < p ∨ p + (k : ℤ) < i) → cfg'.tape i = tape i) ∧
      π.length = k + 1 := by
  induction k generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := 11, writeSym := Sym.mk (tape p).1 true, moveDir :=
          Dir.S }
      let step : SymStep := { fromState := 10, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (10, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step, r] at *
        simp only [htp]
        have hms : ms = false := by simpa [htp] using hstop.1
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [htp] using hstop.2
        rcases hks with hk | hk <;> subst ks <;> decide
      refine ⟨[step], symStepConfig (SymConfig.mk 10 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_,
          ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk 10 tape p) SymSteps.nil ?_ ?_ ?_
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
      let r₁ : SymTransResult := { nextState := 10, writeSym := tape p, moveDir := Dir.R }
      let step₁ : SymStep := { fromState := 10, readSym := tape p, result := r₁ }
      have htrans₁ : step₁.result ∈ VerifierSym.transition (10, tape p) := by
        rcases htp : tape p with ⟨ks, ms⟩
        simp only [step₁, r₁] at *
        simp only [htp]
        have hms : ms = true := by simpa [htp] using (hmarked 0 (by omega)).1
        subst ms
        have hks : ks = SymKind.data0 ∨ ks = SymKind.data1 := by
          simpa [htp] using (hmarked 0 (by omega)).2
        rcases hks with hk | hk <;> subst ks <;> decide
      have hstep₁ : SymSteps VerifierSym.transition (SymConfig.mk 10 tape p) [step₁]
          (symStepConfig (SymConfig.mk 10 tape p) step₁.result) := by
        refine SymSteps.cons [] step₁ (SymConfig.mk 10 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans₁
      have hcfg₁ : symStepConfig (SymConfig.mk 10 tape p) step₁.result = SymConfig.mk 10 tape (p +
          1) := by
        simp [symStepConfig, step₁, r₁, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hmarked' : ∀ i : ℕ, i < k → (tape (p + 1 + (i : ℤ))).2 = true ∧
          ((tape (p + 1 + (i : ℤ))).1 = SymKind.data0 ∨ (tape (p + 1 + (i : ℤ))).1 =
              SymKind.data1) := by
        intro i hi
        simpa [add_assoc, add_comm, add_left_comm] using hmarked (i + 1) (by omega)
      have hstop' : (tape (p + 1 + (k : ℤ))).2 = false ∧
          ((tape (p + 1 + (k : ℤ))).1 = SymKind.data0 ∨ (tape (p + 1 + (k : ℤ))).1 =
              SymKind.data1) := by
        simpa [add_assoc, add_comm, add_left_comm] using hstop
      rcases ih (p + 1) tape hmarked' hstop' with ⟨π', cfg', hsteps', hst', hhead', hkeep',
          hwrite', hside', hlen'⟩
      refine ⟨step₁ :: π', cfg', ?_, hst', ?_, ?_, ?_, ?_, ?_⟩
      · exact symSteps_append_concat [step₁] π' hstep₁ (by simpa [hcfg₁] using hsteps')
      · rw [hhead']
        omega
      · intro i hi
        rcases Nat.lt_or_ge i 1 with hi0 | hi1
        · have : i = 0 := by omega
          subst i
          simpa using (hside' p (by simp))
        · have hkeepi : cfg'.tape (p + 1 + ((i - 1 : ℕ) : ℤ)) = tape (p + 1 + ((i - 1 : ℕ) : ℤ))
            := by
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

/-- [11 步 · d1 支] 11 读 data1(m)：写 data0(m)、R → `81 @ p+1`（单步）。 -/
lemma step11_d1 (p : ℤ) (tape : ℤ → Sym) (h : (tape p).1 = SymKind.data1) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 11 tape p) π cfg' ∧
      cfg'.state = 81 ∧ cfg'.headPos = p + 1 ∧
      cfg'.tape = (fun i => if i = p then Sym.mk SymKind.data0 (tape p).2 else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult :=
    { nextState := 81, writeSym := Sym.mk SymKind.data0 (tape p).2, moveDir := Dir.R }
  let step : SymStep := { fromState := 11, readSym := tape p, result := r }
  have htrans : step.result ∈ VerifierSym.transition (11, tape p) := by
    rcases htp : tape p with ⟨ks, ms⟩
    simp only [step, r] at *
    simp only [htp]
    have hks : ks = SymKind.data1 := by simpa [htp] using h
    subst ks
    cases ms <;> decide
  refine ⟨[step], symStepConfig (SymConfig.mk 11 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 11 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
  · funext i
    by_cases h₂ : i = p <;> simp [symStepConfig, step, r, h₂]
  · simp

/-- [11 步 · d0 支] 11 读 data0(m)：写 data1(m)、R → `14 @ p+1`（单步）。 -/
lemma step11_d0 (p : ℤ) (tape : ℤ → Sym) (h : (tape p).1 = SymKind.data0) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 11 tape p) π cfg' ∧
      cfg'.state = 14 ∧ cfg'.headPos = p + 1 ∧
      cfg'.tape = (fun i => if i = p then Sym.mk SymKind.data1 (tape p).2 else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult :=
    { nextState := 14, writeSym := Sym.mk SymKind.data1 (tape p).2, moveDir := Dir.R }
  let step : SymStep := { fromState := 11, readSym := tape p, result := r }
  have htrans : step.result ∈ VerifierSym.transition (11, tape p) := by
    rcases htp : tape p with ⟨ks, ms⟩
    simp only [step, r] at *
    simp only [htp]
    have hks : ks = SymKind.data0 := by simpa [htp] using h
    subst ks
    cases ms <;> decide
  refine ⟨[step], symStepConfig (SymConfig.mk 11 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 11 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
  · funext i
    by_cases h₂ : i = p <;> simp [symStepConfig, step, r, h₂]
  · simp

/-! ========== 轮总装（位 1 · 至 13 停） ========== -/

set_option maxHeartbeats 900000 in
-- 轮总装＋footprint 的 if-链项重写需高于默认 200k 的预算（上下文含 5 段 tape if-链与借位组）
/-- [轮 · 位1] 从 `5 @ q`（`q = p_e + k`，`1 ≤ k ≤ p_e−2`）走完一轮：
    烧（5→76）→ 76 西扫 → 77 西扫 → 10 东扫定位 → 11 按位减 → {81 直达 | 14 借位 → 81}，
    止于 `13 @ p_e + 2`（轮界，未含 13 出口步）。长度精确式 `k + 2·p_e + 3`。
    （两栏制：证明栏 = 长度 ≤ 形；位移口径见 ② S 吸收节。） -/
lemma round_to13 (p_e : ℤ) (k : ℕ) (tape : ℤ → Sym)
    (hp_e : 3 ≤ p_e)
    (hk : 1 ≤ k)
    (hkpe : (k : ℤ) ≤ p_e - 2)
    (hbit : (tape (p_e + (k : ℤ))).1 = SymKind.data1)
    (hmarker : (tape p_e).1 = SymKind.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrail : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed)
    (hbwd : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbor : (tape (k : ℤ)).1 = SymKind.data0 →
      ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        cfg'.state = 13 ∧ cfg'.headPos = p_e + 2 ∧
        (π.length : ℤ) = (k : ℤ) + 2 * p_e + 3 ∧
        (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
        ((cfg'.tape (k : ℤ)).2 = true ∧
          ((cfg'.tape (k : ℤ)).1 = SymKind.data0 ∨ (cfg'.tape (k : ℤ)).1 = SymKind.data1)) ∧
        (∀ i : ℤ, (k : ℤ) < i → i ≤ p_e - 2 →
          (((cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape i).2 = false)) ∧
        (∀ i : ℤ, ((p_e - 1 ≤ i ∧ i ≤ p_e) ∨ (p_e + 1 ≤ i ∧ i < p_e + (k : ℤ)) ∨
            p_e + (k : ℤ) < i) → cfg'.tape i = tape i) ∧
        cfg'.tape (p_e + (k : ℤ)) = Sym.consumed ∧
        (((tape (k : ℤ)).1 = SymKind.data1 ∧ (cfg'.tape (k : ℤ)).1 = SymKind.data0 ∧
            (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
            (∀ i : ℤ, (k : ℤ) < i → i ≤ p_e - 2 → cfg'.tape i = tape i))
          ∨ ((tape (k : ℤ)).1 = SymKind.data0 ∧ (cfg'.tape (k : ℤ)).1 = SymKind.data1 ∧
            (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
            ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
              (tape j).1 = SymKind.data1 ∧
              (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → ((tape i).1 = SymKind.data0 ∧
                (cfg'.tape i).1 = SymKind.data1)) ∧
              (cfg'.tape j).1 = SymKind.data0 ∧
              (∀ i : ℤ, j < i → i ≤ p_e - 2 → cfg'.tape i = tape i))) := by
  rcases step5burn (p_e + (k : ℤ)) tape hbit with ⟨π₁, cfg₁, hs₁, hst₁, hhd₁, htp₁, hlen₁⟩
  -- 桥接常用式：cell 在 `tape` 上的值（经 cfg₁/cfg₂/cfg₃ 的只读传递）
  have hkpos : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) = (k : ℤ) := by omega
  have hb : (((k - 1 : ℕ) : ℤ)) = (k : ℤ) - 1 := by omega
  -- ── 76 西扫（n = k） ──
  have hdata₁ : ∀ i : ℤ, (p_e + (k : ℤ) - 1) - (k : ℤ) + 1 ≤ i ∧ i ≤ p_e + (k : ℤ) - 1 →
      (cfg₁.tape i).1 = SymKind.consumed ∨ (cfg₁.tape i).1 = SymKind.data0 ∨
        (cfg₁.tape i).1 = SymKind.data1 := by
    intro i hi
    have hne : i ≠ p_e + (k : ℤ) := by omega
    simp only [htp₁, if_neg hne]
    by_cases hpe : i = p_e
    · rw [hpe]
      exact Or.inr (Or.inl hmarker)
    · rw [htrail i (by omega) (by omega)]
      exact Or.inl rfl
  have hbound₁ : cfg₁.tape ((p_e + (k : ℤ) - 1) - (k : ℤ)) = Sym.boundary := by
    have hne : (p_e + (k : ℤ) - 1) - (k : ℤ) ≠ p_e + (k : ℤ) := by omega
    simp only [htp₁, if_neg hne]
    rw [show (p_e + (k : ℤ) - 1) - (k : ℤ) = p_e - 1 from by omega]
    exact hbound0
  rcases fire_west76 k (p_e + (k : ℤ) - 1) cfg₁.tape hdata₁ hbound₁
    with ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, htp₂, hlen₂⟩
  -- ── 77 西扫（n = p_e − 2） ──
  have hn₂ : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 := Int.toNat_of_nonneg (by omega)
  have hdata₂ : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (((p_e - 2).toNat : ℕ) : ℤ) →
      (cfg₂.tape i).1 = SymKind.data0 ∨ (cfg₂.tape i).1 = SymKind.data1 := by
    intro i hi
    rw [hn₂] at hi
    have hne : i ≠ p_e + (k : ℤ) := by omega
    simp only [htp₂, htp₁, if_neg hne]
    exact hbwd i hi.1 (by omega)
  have hbound₂ : cfg₂.tape 0 = Sym.boundary := by
    have hne : (0 : ℤ) ≠ p_e + (k : ℤ) := by omega
    simp only [htp₂, htp₁, if_neg hne]
    exact hboundL
  rcases fire_west77 ((p_e - 2).toNat) cfg₂.tape hdata₂ hbound₂
    with ⟨π₃, cfg₃, hs₃, hst₃, hhd₃, htp₃, hlen₃⟩
  -- ── 10 东扫定位（k−1 个已标记格） ──
  have hmarked₄ : ∀ i : ℕ, i < k - 1 →
      (cfg₃.tape (1 + (i : ℤ))).2 = true ∧
        ((cfg₃.tape (1 + (i : ℤ))).1 = SymKind.data0 ∨
          (cfg₃.tape (1 + (i : ℤ))).1 = SymKind.data1) := by
    intro i hi
    have hne : (1 : ℤ) + (i : ℤ) ≠ p_e + (k : ℤ) := by omega
    have h1 : cfg₃.tape (1 + (i : ℤ)) = tape (1 + (i : ℤ)) := by
      simp only [htp₃, htp₂, htp₁, if_neg hne]
    rw [h1]
    exact ⟨hmarks (1 + (i : ℤ)) (by omega) (by omega),
      hbwd (1 + (i : ℤ)) (by omega) (by omega)⟩
  have hstop₄ : (cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ))).2 = false ∧
      ((cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ))).1 = SymKind.data0 ∨
        (cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ))).1 = SymKind.data1) := by
    have hne : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) ≠ p_e + (k : ℤ) := by omega
    have h1 : cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ)) = tape (1 + ((k - 1 : ℕ) : ℤ)) := by
      simp only [htp₃, htp₂, htp₁, if_neg hne]
    rw [h1, hkpos]
    exact ⟨hflagFree (k : ℤ) le_rfl hkpe, hbwd (k : ℤ) (by omega) hkpe⟩
  rcases ride10 (k - 1) 1 cfg₃.tape hmarked₄ hstop₄
    with ⟨π₄, cfg₄, hs₄, hst₄, hhd₄, hkeep₄, hwrite₄, hside₄, hlen₄⟩
  -- 桥接：cell k 的值 = tape k 的值（经 ride10 写 m、走 hwrite₄）
  have hkind₄ : (cfg₄.tape (k : ℤ)).1 = SymKind.data1 ∨
      (cfg₄.tape (k : ℤ)).1 = SymKind.data0 := by
    have h1 : (cfg₄.tape (k : ℤ)).1 = (cfg₃.tape (k : ℤ)).1 := by
      rw [← hkpos, hwrite₄]
      rfl
    rw [h1]
    have h2 : cfg₃.tape (k : ℤ) = tape (k : ℤ) := by
      have hne : (k : ℤ) ≠ p_e + (k : ℤ) := by omega
      simp only [htp₃, htp₂, htp₁, if_neg hne]
    rw [h2]
    rcases hbwd (k : ℤ) (by omega) hkpe with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- footprint 常用：`{k, q}` 外格子在 76/77/ride10 段的保持传递
  have hcfg43 : ∀ i : ℤ, i ≠ (k : ℤ) → cfg₄.tape i = cfg₃.tape i := by
    intro i hne
    by_cases h1 : i < 1
    · exact hside₄ i (Or.inl h1)
    · by_cases h2 : i ≤ (k : ℤ) - 1
      · obtain ⟨jj, rfl⟩ : ∃ jj : ℕ, (1 : ℤ) + (jj : ℤ) = i :=
          ⟨(i - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
        exact hkeep₄ jj (by omega)
      · exact hside₄ i (Or.inr (by omega))
  have hcfg31 : ∀ i : ℤ, i ≠ p_e + (k : ℤ) → cfg₃.tape i = tape i := by
    intro i hne
    simp only [htp₃, htp₂, htp₁, if_neg hne]
  -- ── 11 步（两支） ──
  by_cases hd1 : (cfg₄.tape (k : ℤ)).1 = SymKind.data1
  · -- d1 支：11 → 81 @ k+1
    rcases step11_d1 (k : ℤ) cfg₄.tape hd1
      with ⟨π₅, cfg₅, hs₅, hst₅, hhd₅, htp₅, hlen₅⟩
    have hn₃ : (((p_e - (k : ℤ)).toNat : ℕ) : ℤ) = p_e - (k : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    -- 81 直达：cells [k+1, p_e] ∈ {d0, d1, #}
    have hdata₅ : ∀ i : ℕ, i < (p_e - (k : ℤ)).toNat →
        (cfg₅.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.data0 ∨
          (cfg₅.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.data1 ∨
          (cfg₅.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.boundary := by
      intro i hi
      have hi' : (i : ℤ) < p_e - (k : ℤ) := by omega
      have hle : (k : ℤ) + 1 + (i : ℤ) ≤ p_e := by omega
      have h1 : cfg₅.tape ((k : ℤ) + 1 + (i : ℤ)) = cfg₄.tape ((k : ℤ) + 1 + (i : ℤ)) := by
        have hne : (k : ℤ) + 1 + (i : ℤ) ≠ (k : ℤ) := by omega
        simp only [htp₅, if_neg hne]
      rw [h1]
      have h2 : cfg₄.tape ((k : ℤ) + 1 + (i : ℤ)) = cfg₃.tape ((k : ℤ) + 1 + (i : ℤ)) :=
        hside₄ _ (by right; omega)
      rw [h2]
      have hne2 : (k : ℤ) + 1 + (i : ℤ) ≠ p_e + (k : ℤ) := by omega
      have h3 : cfg₃.tape ((k : ℤ) + 1 + (i : ℤ)) = tape ((k : ℤ) + 1 + (i : ℤ)) := by
        simp only [htp₃, htp₂, htp₁, if_neg hne2]
      rw [h3]
      by_cases hp0 : (k : ℤ) + 1 + (i : ℤ) = p_e - 1
      · rw [hp0, hbound0]
        exact Or.inr (Or.inr rfl)
      · by_cases hp1 : (k : ℤ) + 1 + (i : ℤ) = p_e
        · rw [hp1, hmarker]
          exact Or.inl rfl
        · rcases hbwd ((k : ℤ) + 1 + (i : ℤ)) (by omega) (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
    have hcons₅ : cfg₅.tape ((k : ℤ) + 1 + ((p_e - (k : ℤ)).toNat : ℤ)) = Sym.consumed := by
      rw [hn₃]
      have hpos : (k : ℤ) + 1 + (p_e - (k : ℤ)) = p_e + 1 := by omega
      rw [hpos]
      have h4 : cfg₅.tape (p_e + 1) = cfg₄.tape (p_e + 1) := by
        have hne : p_e + 1 ≠ (k : ℤ) := by omega
        simp only [htp₅, if_neg hne]
      rw [h4]
      have h5 : cfg₄.tape (p_e + 1) = cfg₃.tape (p_e + 1) :=
        hside₄ _ (by right; omega)
      rw [h5]
      by_cases hk1 : k = 1
      · subst hk1
        simp only [htp₃, htp₂, htp₁]
        rw [if_pos (show p_e + 1 = p_e + ((1 : ℕ) : ℤ) from rfl)]
      · have hne : p_e + 1 ≠ p_e + (k : ℤ) := by omega
        simp only [htp₃, htp₂, htp₁, if_neg hne]
        exact htrail (p_e + 1) le_rfl (by omega)
    rcases return81 ((p_e - (k : ℤ)).toNat) ((k : ℤ) + 1) cfg₅.tape hdata₅ hcons₅
      with ⟨π₆, cfg₆, hs₆, hst₆, hhd₆, htp₆, hlen₆⟩
    -- footprint：`{k, q}` 外格子经 11 步/81 保持（d1 支：11 只写 k）
    have hkept : ∀ i : ℤ, i ≠ (k : ℤ) → i ≠ p_e + (k : ℤ) → cfg₆.tape i = tape i := by
      intro i h1 h2
      rw [htp₆]
      simp only [htp₅, if_neg h1]
      rw [hcfg43 i h1]
      exact hcfg31 i h2
    refine ⟨π₁ ++ (π₂ ++ (π₃ ++ (π₄ ++ (π₅ ++ π₆)))), cfg₆, ?_, hst₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
    · have e12 : cfg₁ = SymConfig.mk 76 cfg₁.tape (p_e + (k : ℤ) - 1) := by
        rw [← hst₁, ← hhd₁]
      have e23 : cfg₂ = SymConfig.mk 77 cfg₂.tape ((p_e + (k : ℤ) - 1) - (k : ℤ) - 1) := by
        rw [← hst₂, ← hhd₂]
      have e34 : cfg₃ = SymConfig.mk 10 cfg₃.tape (1 : ℤ) := by
        rw [← hst₃, ← hhd₃]
      have e45 : cfg₄ = SymConfig.mk 11 cfg₄.tape (1 + ((k - 1 : ℕ) : ℤ)) := by
        rw [← hst₄, ← hhd₄]
      have e56 : cfg₅ = SymConfig.mk 81 cfg₅.tape ((k : ℤ) + 1) := by
        rw [← hst₅, ← hhd₅]
      have h2pos : (p_e + (k : ℤ) - 1) - (k : ℤ) - 1 = p_e - 2 := by omega
      have c56 : SymSteps VerifierSym.transition cfg₅ π₆ cfg₆ := by
        rw [e56]
        exact hs₆
      have a56 := symSteps_append_concat π₅ π₆ hs₅ c56
      have c45 : SymSteps VerifierSym.transition cfg₄ (π₅ ++ π₆) cfg₆ := by
        rw [e45, hkpos]
        exact a56
      have a46 := symSteps_append_concat π₄ (π₅ ++ π₆) hs₄ c45
      have c34 : SymSteps VerifierSym.transition cfg₃ (π₄ ++ (π₅ ++ π₆)) cfg₆ := by
        rw [e34]
        exact a46
      have a36 := symSteps_append_concat π₃ (π₄ ++ (π₅ ++ π₆)) hs₃ c34
      have c23 : SymSteps VerifierSym.transition cfg₂ (π₃ ++ (π₄ ++ (π₅ ++ π₆))) cfg₆ := by
        rw [e23, h2pos, ← hn₂]
        exact a36
      have a26 := symSteps_append_concat π₂ (π₃ ++ (π₄ ++ (π₅ ++ π₆))) hs₂ c23
      have c12 : SymSteps VerifierSym.transition cfg₁ (π₂ ++ (π₃ ++ (π₄ ++ (π₅ ++ π₆)))) cfg₆ := by
        rw [e12]
        exact a26
      exact symSteps_append_concat π₁ _ hs₁ c12
    · have hcast : ((k : ℤ) + 1 + ((p_e - (k : ℤ)).toNat : ℤ)) = p_e + 1 := by
        rw [hn₃]; omega
      rw [hhd₆, hcast]
      omega
    · simp only [List.length_append]
      have hb2 : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 := hn₂
      have hb3 : (((p_e - (k : ℤ)).toNat : ℕ) : ℤ) = p_e - (k : ℤ) := hn₃
      omega
    · -- keepLow：`i < k` 保持
      intro i hi
      exact hkept i (by omega) (by omega)
    · -- markK：cell k 盖章（m、data）
      have h₁ : cfg₆.tape (k : ℤ) = cfg₅.tape (k : ℤ) := by rw [htp₆]
      have h₂ : cfg₅.tape (k : ℤ) = Sym.mk SymKind.data0 (cfg₄.tape (k : ℤ)).2 := by
        simp only [htp₅, ite_true]
      refine ⟨?_, ?_⟩
      · rw [h₁, h₂]
        have h₄ : (cfg₄.tape (k : ℤ)).2 = true := by
          rw [← hkpos, hwrite₄]
          rfl
        rw [h₄]
        rfl
      · rw [h₁, h₂]
        exact Or.inl rfl
    · -- midData：`k < i ≤ p_e−2` 保持 data、无标
      intro i hik hipe
      rw [hkept i (by omega) (by omega)]
      exact ⟨hbwd i (by omega) hipe, hflagFree i (by omega) hipe⟩
    · -- keepWin：`[p_e−1, p_e]`、旧 trail 段与高区保持
      intro i hw
      apply hkept i
      · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
      · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
    · -- burnQ：q = p_e+k 烧成 consumed
      have h₁ : cfg₆.tape (p_e + (k : ℤ)) = cfg₅.tape (p_e + (k : ℤ)) := by rw [htp₆]
      have h₂ : cfg₅.tape (p_e + (k : ℤ)) = cfg₄.tape (p_e + (k : ℤ)) := by
        simp only [htp₅, if_neg (by omega : p_e + (k : ℤ) ≠ (k : ℤ))]
      rw [h₁, h₂]
      have h₄ : cfg₄.tape (p_e + (k : ℤ)) = cfg₃.tape (p_e + (k : ℤ)) :=
        hside₄ _ (Or.inr (by omega))
      rw [h₄]
      simp only [htp₃, htp₂, htp₁, ite_true]
    · -- 分支共轭：d1 支（cell k 落 d0、全体保持）
      left
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hbridge : (cfg₄.tape (k : ℤ)).1 = (tape (k : ℤ)).1 := by
          rw [← hkpos, hwrite₄]
          simp only [htp₃, htp₂, htp₁, if_neg (by omega : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) ≠ p_e + (k :
              ℤ))]; rfl
        rw [← hbridge]
        exact hd1
      · have h1' : cfg₆.tape (k : ℤ) = cfg₅.tape (k : ℤ) := by rw [htp₆]
        have h2' : cfg₅.tape (k : ℤ) = Sym.mk SymKind.data0 (cfg₄.tape (k : ℤ)).2 := by
          simp only [htp₅, ite_true]
        rw [h1', h2']; rfl
      · intro i hi
        exact hkept i (by omega) (by omega)
      · intro i hi1 hi2
        exact hkept i (by omega) (by omega)
  · -- d0 支：11 → 14 @ k+1，借位 j → 81 @ j+1
    have hd0 : (cfg₄.tape (k : ℤ)).1 = SymKind.data0 := by
      rcases hkind₄ with h | h
      · exact absurd h hd1
      · exact h
    rcases step11_d0 (k : ℤ) cfg₄.tape hd0
      with ⟨π₅, cfg₅, hs₅, hst₅, hhd₅, htp₅, hlen₅⟩
    -- 桥：tape k = d0
    have hk0 : (tape (k : ℤ)).1 = SymKind.data0 := by
      have h1 : (cfg₄.tape (k : ℤ)).1 = (cfg₃.tape (k : ℤ)).1 := by
        rw [← hkpos, hwrite₄]
        rfl
      rw [h1] at hd0
      have hne : (k : ℤ) ≠ p_e + (k : ℤ) := by omega
      simp only [htp₃, htp₂, htp₁, if_neg hne] at hd0
      exact hd0
    rcases hbor hk0 with ⟨j, hjlo, hjhi, hz, hone⟩
    have hn₅ : (((j - ((k : ℤ) + 1)).toNat : ℕ) : ℤ) = j - ((k : ℤ) + 1) :=
      Int.toNat_of_nonneg (by omega)
    -- 借位：crossed [k+1, j−1] 全 data0
    have hzeros₅ : ∀ i : ℕ, i < (j - ((k : ℤ) + 1)).toNat →
        (cfg₅.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.data0 := by
      intro i hi
      have h1 : cfg₅.tape ((k : ℤ) + 1 + (i : ℤ)) = cfg₄.tape ((k : ℤ) + 1 + (i : ℤ)) := by
        have hne : (k : ℤ) + 1 + (i : ℤ) ≠ (k : ℤ) := by omega
        simp only [htp₅, if_neg hne]
      rw [h1]
      have h2 : cfg₄.tape ((k : ℤ) + 1 + (i : ℤ)) = cfg₃.tape ((k : ℤ) + 1 + (i : ℤ)) :=
        hside₄ _ (by right; omega)
      rw [h2]
      have hne2 : (k : ℤ) + 1 + (i : ℤ) ≠ p_e + (k : ℤ) := by omega
      have h3 : cfg₃.tape ((k : ℤ) + 1 + (i : ℤ)) = tape ((k : ℤ) + 1 + (i : ℤ)) := by
        simp only [htp₃, htp₂, htp₁, if_neg hne2]
      rw [h3]
      exact hz ((k : ℤ) + 1 + (i : ℤ)) (by omega) (by omega)
    have hone₅ : (cfg₅.tape ((k : ℤ) + 1 + ((j - ((k : ℤ) + 1)).toNat : ℤ))).1 =
        SymKind.data1 := by
      rw [hn₅]
      have hpos : (k : ℤ) + 1 + (j - ((k : ℤ) + 1)) = j := by omega
      rw [hpos]
      have h1 : cfg₅.tape j = cfg₄.tape j := by
        have hne : j ≠ (k : ℤ) := by omega
        simp only [htp₅, if_neg hne]
      rw [h1]
      have h2 : cfg₄.tape j = cfg₃.tape j :=
        hside₄ _ (by right; omega)
      rw [h2]
      have hne2 : j ≠ p_e + (k : ℤ) := by omega
      have h3 : cfg₃.tape j = tape j := by
        simp only [htp₃, htp₂, htp₁, if_neg hne2]
      rw [h3]
      exact hone
    rcases borrow14 ((j - ((k : ℤ) + 1)).toNat) ((k : ℤ) + 1) cfg₅.tape hzeros₅ hone₅
      with ⟨π₆, cfg₆, hs₆, hst₆, hhd₆, hkeep₆, hwrite₆, hside₆, hlen₆⟩
    have hn₆ : (((p_e - j).toNat : ℕ) : ℤ) = p_e - j :=
      Int.toNat_of_nonneg (by omega)
    -- 81 返扫（自 j+1）：cells [j+1, p_e] ∈ {d0, d1, #}
    have hdata₆ : ∀ i : ℕ, i < (p_e - j).toNat →
        (cfg₆.tape (j + 1 + (i : ℤ))).1 = SymKind.data0 ∨
          (cfg₆.tape (j + 1 + (i : ℤ))).1 = SymKind.data1 ∨
          (cfg₆.tape (j + 1 + (i : ℤ))).1 = SymKind.boundary := by
      intro i hi
      have hi' : (i : ℤ) < p_e - j := by omega
      have hle : j + 1 + (i : ℤ) ≤ p_e := by omega
      have h1 : cfg₆.tape (j + 1 + (i : ℤ)) = cfg₅.tape (j + 1 + (i : ℤ)) := by
        apply hside₆
        right
        rw [hn₅]
        omega
      rw [h1]
      have hne0 : j + 1 + (i : ℤ) ≠ (k : ℤ) := by omega
      have h2 : cfg₅.tape (j + 1 + (i : ℤ)) = cfg₄.tape (j + 1 + (i : ℤ)) := by
        simp only [htp₅, if_neg hne0]
      rw [h2]
      have h3 : cfg₄.tape (j + 1 + (i : ℤ)) = cfg₃.tape (j + 1 + (i : ℤ)) :=
        hside₄ _ (by right; omega)
      rw [h3]
      have hne2 : j + 1 + (i : ℤ) ≠ p_e + (k : ℤ) := by omega
      have h4 : cfg₃.tape (j + 1 + (i : ℤ)) = tape (j + 1 + (i : ℤ)) := by
        simp only [htp₃, htp₂, htp₁, if_neg hne2]
      rw [h4]
      by_cases hp0 : j + 1 + (i : ℤ) = p_e - 1
      · rw [hp0, hbound0]
        exact Or.inr (Or.inr rfl)
      · by_cases hp1 : j + 1 + (i : ℤ) = p_e
        · rw [hp1, hmarker]
          exact Or.inl rfl
        · rcases hbwd (j + 1 + (i : ℤ)) (by omega) (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
    have hcons₆ : cfg₆.tape (j + 1 + ((p_e - j).toNat : ℤ)) = Sym.consumed := by
      rw [hn₆]
      have hpos : j + 1 + (p_e - j) = p_e + 1 := by omega
      rw [hpos]
      have h1 : cfg₆.tape (p_e + 1) = cfg₅.tape (p_e + 1) := by
        apply hside₆
        right
        rw [hn₅]
        omega
      rw [h1]
      have hne0 : p_e + 1 ≠ (k : ℤ) := by omega
      have h2 : cfg₅.tape (p_e + 1) = cfg₄.tape (p_e + 1) := by
        simp only [htp₅, if_neg hne0]
      rw [h2]
      have h3 : cfg₄.tape (p_e + 1) = cfg₃.tape (p_e + 1) :=
        hside₄ _ (by right; omega)
      rw [h3]
      by_cases hk1 : k = 1
      · subst hk1
        simp only [htp₃, htp₂, htp₁]
        rw [if_pos (show p_e + 1 = p_e + ((1 : ℕ) : ℤ) from rfl)]
      · have hne : p_e + 1 ≠ p_e + (k : ℤ) := by omega
        simp only [htp₃, htp₂, htp₁, if_neg hne]
        exact htrail (p_e + 1) le_rfl (by omega)
    rcases return81 ((p_e - j).toNat) (j + 1) cfg₆.tape hdata₆ hcons₆
      with ⟨π₇, cfg₇, hs₇, hst₇, hhd₇, htp₇, hlen₇⟩
    -- footprint：勿写区经借位段/81 保持（d0 支：借位只写 [k+1, j]，81 只写 p_e+1）
    have hbkeep : ∀ i : ℤ, (i < (k : ℤ) + 1 ∨ j + 1 ≤ i) → cfg₆.tape i = cfg₅.tape i := by
      intro i hi
      apply hside₆
      rcases hi with h | h
      · left; omega
      · right; rw [hn₅]; omega
    have hkeptN : ∀ i : ℤ, i ≠ (k : ℤ) → (i < (k : ℤ) + 1 ∨ j + 1 ≤ i) → i ≠ p_e + (k : ℤ) →
        cfg₇.tape i = tape i := by
      intro i h1 h2 h3
      rw [htp₇, hbkeep i h2]
      simp only [htp₅, if_neg h1]
      rw [hcfg43 i h1]
      exact hcfg31 i h3
    refine ⟨π₁ ++ (π₂ ++ (π₃ ++ (π₄ ++ (π₅ ++ (π₆ ++ π₇))))), cfg₇, ?_, hst₇, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
    · have e12 : cfg₁ = SymConfig.mk 76 cfg₁.tape (p_e + (k : ℤ) - 1) := by
        rw [← hst₁, ← hhd₁]
      have e23 : cfg₂ = SymConfig.mk 77 cfg₂.tape ((p_e + (k : ℤ) - 1) - (k : ℤ) - 1) := by
        rw [← hst₂, ← hhd₂]
      have e34 : cfg₃ = SymConfig.mk 10 cfg₃.tape (1 : ℤ) := by
        rw [← hst₃, ← hhd₃]
      have e45 : cfg₄ = SymConfig.mk 11 cfg₄.tape (1 + ((k - 1 : ℕ) : ℤ)) := by
        rw [← hst₄, ← hhd₄]
      have e56 : cfg₅ = SymConfig.mk 14 cfg₅.tape ((k : ℤ) + 1) := by
        rw [← hst₅, ← hhd₅]
      have e67 : cfg₆ = SymConfig.mk 81 cfg₆.tape
          (((k : ℤ) + 1) + (((j - ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + 1) := by
        rw [← hst₆, ← hhd₆]
      have h2pos : (p_e + (k : ℤ) - 1) - (k : ℤ) - 1 = p_e - 2 := by omega
      have hj1 : ((k : ℤ) + 1) + (j - ((k : ℤ) + 1)) + 1 = j + 1 := by omega
      have c67 : SymSteps VerifierSym.transition cfg₆ π₇ cfg₇ := by
        rw [e67, hn₅, hj1]
        exact hs₇
      have a67 := symSteps_append_concat π₆ π₇ hs₆ c67
      have c56 : SymSteps VerifierSym.transition cfg₅ (π₆ ++ π₇) cfg₇ := by
        rw [e56]
        exact a67
      have a57 := symSteps_append_concat π₅ (π₆ ++ π₇) hs₅ c56
      have c45 : SymSteps VerifierSym.transition cfg₄ (π₅ ++ (π₆ ++ π₇)) cfg₇ := by
        rw [e45, hkpos]
        exact a57
      have a47 := symSteps_append_concat π₄ (π₅ ++ (π₆ ++ π₇)) hs₄ c45
      have c34 : SymSteps VerifierSym.transition cfg₃ (π₄ ++ (π₅ ++ (π₆ ++ π₇))) cfg₇ := by
        rw [e34]
        exact a47
      have a37 := symSteps_append_concat π₃ (π₄ ++ (π₅ ++ (π₆ ++ π₇))) hs₃ c34
      have c23 : SymSteps VerifierSym.transition cfg₂ (π₃ ++ (π₄ ++ (π₅ ++ (π₆ ++ π₇)))) cfg₇ := by
        rw [e23, h2pos, ← hn₂]
        exact a37
      have a27 := symSteps_append_concat π₂ (π₃ ++ (π₄ ++ (π₅ ++ (π₆ ++ π₇)))) hs₂ c23
      have c12 : SymSteps VerifierSym.transition cfg₁
          (π₂ ++ (π₃ ++ (π₄ ++ (π₅ ++ (π₆ ++ π₇))))) cfg₇ := by
        rw [e12]
        exact a27
      exact symSteps_append_concat π₁ _ hs₁ c12
    · have hcast : (j + 1 + ((p_e - j).toNat : ℤ)) = p_e + 1 := by
        rw [hn₆]; omega
      rw [hhd₇, hcast]
      omega
    · simp only [List.length_append]
      have hb2 : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 := hn₂
      have hb5 : (((j - ((k : ℤ) + 1)).toNat : ℕ) : ℤ) = j - ((k : ℤ) + 1) := hn₅
      have hb6 : (((p_e - j).toNat : ℕ) : ℤ) = p_e - j := hn₆
      omega
    · -- keepLow：`i < k` 保持
      intro i hi
      refine hkeptN i (by omega) ?_ (by omega)
      left
      omega
    · -- markK：cell k 盖章（m、data）
      have h₁ : cfg₇.tape (k : ℤ) = cfg₆.tape (k : ℤ) := by rw [htp₇]
      have h₂ : cfg₆.tape (k : ℤ) = cfg₅.tape (k : ℤ) := hbkeep (k : ℤ) (Or.inl (by omega))
      have h₃ : cfg₅.tape (k : ℤ) = Sym.mk SymKind.data1 (cfg₄.tape (k : ℤ)).2 := by
        simp only [htp₅, ite_true]
      refine ⟨?_, ?_⟩
      · rw [h₁, h₂, h₃]
        have h₄ : (cfg₄.tape (k : ℤ)).2 = true := by
          rw [← hkpos, hwrite₄]
          rfl
        rw [h₄]
        rfl
      · rw [h₁, h₂, h₃]
        exact Or.inr rfl
    · -- midData：`k < i ≤ p_e−2` 保持 data、无标
      intro i hik hipe
      by_cases hj : j + 1 ≤ i
      · rw [hkeptN i (by omega) (Or.inr hj) (by omega)]
        exact ⟨hbwd i (by omega) hipe, hflagFree i (by omega) hipe⟩
      · have hle : i ≤ j := by omega
        rcases lt_or_eq_of_le hle with hlt | heq
        · -- i < j：借位过格写 data1（旧标保持 false）
          have hcell : cfg₆.tape i = Sym.mk SymKind.data1 (cfg₅.tape i).2 := by
            have hi' : i = (k : ℤ) + 1 + ((i - ((k : ℤ) + 1)).toNat : ℤ) := by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - ((k : ℤ) + 1) by omega)
              omega
            rw [hi']
            exact hkeep₆ ((i - ((k : ℤ) + 1)).toNat) (by omega)
          have hflag : (cfg₅.tape i).2 = false := by
            have h5 : cfg₅.tape i = tape i := by
              simp only [htp₅, if_neg (by omega : i ≠ (k : ℤ))]
              rw [hcfg43 i (by omega)]
              exact hcfg31 i (by omega)
            rw [h5]
            exact hflagFree i (by omega) (by omega)
          rw [htp₇, hcell]
          refine ⟨Or.inr rfl, ?_⟩
          rw [hflag]
          rfl
        · -- i = j：借位停格写 data0（旧标保持 false）
          rw [heq]
          have hcell : cfg₆.tape j = Sym.mk SymKind.data0 (cfg₅.tape j).2 := by
            have hj' : (k : ℤ) + 1 + ((j - ((k : ℤ) + 1)).toNat : ℤ) = j := by
              have hcast := hn₅
              omega
            rw [← hj']
            exact hwrite₆
          have hflag : (cfg₅.tape j).2 = false := by
            have h5 : cfg₅.tape j = tape j := by
              simp only [htp₅, if_neg (by omega : j ≠ (k : ℤ))]
              rw [hcfg43 j (by omega)]
              exact hcfg31 j (by omega)
            rw [h5]
            exact hflagFree j (by omega) (by omega)
          rw [htp₇, hcell]
          refine ⟨Or.inl rfl, ?_⟩
          rw [hflag]
          rfl
    · -- keepWin：`[p_e−1, p_e]`、旧 trail 段与高区保持
      intro i hw
      apply hkeptN i
      · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
      · right
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
      · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
    · -- burnQ：q = p_e+k 烧成 consumed
      have h₁ : cfg₇.tape (p_e + (k : ℤ)) = cfg₆.tape (p_e + (k : ℤ)) := by rw [htp₇]
      have h₂ : cfg₆.tape (p_e + (k : ℤ)) = cfg₅.tape (p_e + (k : ℤ)) :=
        hbkeep _ (Or.inr (by omega))
      rw [h₁, h₂]
      have h₃ : cfg₅.tape (p_e + (k : ℤ)) = cfg₄.tape (p_e + (k : ℤ)) := by
        rw [htp₅]
        dsimp only
        rw [if_neg (by omega : p_e + (k : ℤ) ≠ (k : ℤ))]
      rw [h₃]
      have h₄ : cfg₄.tape (p_e + (k : ℤ)) = cfg₃.tape (p_e + (k : ℤ)) :=
        hside₄ _ (Or.inr (by omega))
      rw [h₄]
      rw [htp₃, htp₂, htp₁]
      dsimp only
      rw [if_pos (show p_e + (k : ℤ) = p_e + (k : ℤ) from rfl)]
    · -- 分支共轭：d0 支（cell k 加一、借位走带 j、携带见证）
      right
      refine ⟨hk0, ?_, ?_, j, hjlo, hjhi, hone, ?_, ?_, ?_⟩
      · have h65 : cfg₆.tape (k : ℤ) = cfg₅.tape (k : ℤ) :=
          hbkeep (k : ℤ) (Or.inl (by omega))
        have h54 : cfg₅.tape (k : ℤ) = Sym.mk SymKind.data1 (cfg₄.tape (k : ℤ)).2 := by
          simp only [htp₅, ite_true]
        rw [htp₇, h65, h54]
        rfl
      · intro i hi
        refine hkeptN i (by omega) ?_ (by omega)
        left
        omega
      · intro i hi1 hi2
        have h7 : cfg₇.tape i = cfg₆.tape i := by rw [htp₇]
        have hcell : cfg₆.tape i = Sym.mk SymKind.data1 (cfg₅.tape i).2 := by
          have hi' : i = (k : ℤ) + 1 + ((i - ((k : ℤ) + 1)).toNat : ℤ) := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - ((k : ℤ) + 1) by omega)
            omega
          rw [hi']
          exact hkeep₆ ((i - ((k : ℤ) + 1)).toNat) (by omega)
        have h5i : cfg₅.tape i = tape i := by
          simp only [htp₅, if_neg (by omega : i ≠ (k : ℤ))]
          rw [hcfg43 i (by omega), hcfg31 i (by omega)]
        refine ⟨hz i hi1 hi2, ?_⟩
        rw [h7, hcell, h5i]
        rfl
      · have h7 : cfg₇.tape j = cfg₆.tape j := by rw [htp₇]
        have hj' : (k : ℤ) + 1 + ((j - ((k : ℤ) + 1)).toNat : ℤ) = j := by
          have hcast := hn₅
          omega
        have hcellj : cfg₆.tape j = Sym.mk SymKind.data0 (cfg₅.tape j).2 := by
          rw [← hj']
          exact hwrite₆
        have h5j : cfg₅.tape j = tape j := by
          simp only [htp₅, if_neg (by omega : j ≠ (k : ℤ))]
          rw [hcfg43 j (by omega), hcfg31 j (by omega)]
        rw [h7, hcellj, h5j]
        rfl
      · intro i hi1 hi2
        have h7 : cfg₇.tape i = cfg₆.tape i := by rw [htp₇]
        have h6 : cfg₆.tape i = cfg₅.tape i := hbkeep i (Or.inr (by omega))
        have h5i : cfg₅.tape i = tape i := by
          simp only [htp₅, if_neg (by omega : i ≠ (k : ℤ))]
          rw [hcfg43 i (by omega), hcfg31 i (by omega)]
        rw [h7, h6, h5i]

/-- [烧步 · d0 支] 5 读 data0：写 consumed、L → `8 @ p−1`（单步）。 -/
lemma step5burn0 (p : ℤ) (tape : ℤ → Sym) (h : (tape p).1 = SymKind.data0) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape p) π cfg' ∧
      cfg'.state = 8 ∧ cfg'.headPos = p - 1 ∧
      cfg'.tape = (fun i => if i = p then Sym.consumed else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult := { nextState := 8, writeSym := Sym.consumed, moveDir := Dir.L }
  let step : SymStep := { fromState := 5, readSym := tape p, result := r }
  have htrans : step.result ∈ VerifierSym.transition (5, tape p) := by
    rcases htp : tape p with ⟨ks, ms⟩
    simp only [step, r] at *
    have hks : ks = SymKind.data0 := by simpa [htp] using h
    subst ks
    cases ms <;> decide
  refine ⟨[step], symStepConfig (SymConfig.mk 5 tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 5 tape p) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
    omega
  · funext i
    by_cases h₂ : i = p <;> simp [symStepConfig, step, r, h₂]
  · simp

set_option maxHeartbeats 900000 in
-- 位0轮装配同 round_to13：if-链项重写需高于默认 200k 的预算
/-- [轮 · 位0 · 至 13 停] 从 `5 @ q`（`q = p_e + k`，位0）走完一轮：
    烧（5→8，写 c）→ 8 西扫（至 #₀）→ 9 西扫（至 #ₗ）→ 12 记位（过已标、k 格盖章）
    → `81 @ k+1`（与位1路合流）→ 81 返扫，止于 `13 @ p_e + 2`（轮界）。
    长度精确式 `k + 2·p_e + 2`（= 位1轮 − 1，借位无关）。 -/
lemma round_d0 (p_e : ℤ) (k : ℕ) (tape : ℤ → Sym)
    (hp_e : 3 ≤ p_e)
    (hk : 1 ≤ k)
    (hkpe : (k : ℤ) ≤ p_e - 2)
    (hbit0 : (tape (p_e + (k : ℤ))).1 = SymKind.data0)
    (hmarker : (tape p_e).1 = SymKind.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrail : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed)
    (hbwd : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        cfg'.state = 13 ∧ cfg'.headPos = p_e + 2 ∧
        (π.length : ℤ) = (k : ℤ) + 2 * p_e + 2 ∧
        (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
        ((cfg'.tape (k : ℤ)).2 = true ∧
          ((cfg'.tape (k : ℤ)).1 = SymKind.data0 ∨ (cfg'.tape (k : ℤ)).1 = SymKind.data1)) ∧
        (∀ i : ℤ, (k : ℤ) < i → i ≤ p_e - 2 → cfg'.tape i = tape i) ∧
        (∀ i : ℤ, ((p_e - 1 ≤ i ∧ i ≤ p_e) ∨ (p_e + 1 ≤ i ∧ i < p_e + (k : ℤ)) ∨
            p_e + (k : ℤ) < i) → cfg'.tape i = tape i) ∧
        cfg'.tape (p_e + (k : ℤ)) = Sym.consumed ∧
        ((cfg'.tape (k : ℤ)).1 = (tape (k : ℤ)).1) := by
  rcases step5burn0 (p_e + (k : ℤ)) tape hbit0 with ⟨π₁, cfg₁, hs₁, hst₁, hhd₁, htp₁, hlen₁⟩
  have hkpos : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) = (k : ℤ) := by omega
  -- ── 8 西扫（n = k） ──
  have hdata₂ : ∀ i : ℤ, (p_e + (k : ℤ) - 1) - (k : ℤ) + 1 ≤ i ∧ i ≤ p_e + (k : ℤ) - 1 →
      (cfg₁.tape i).1 = SymKind.consumed ∨ (cfg₁.tape i).1 = SymKind.data0 ∨
        (cfg₁.tape i).1 = SymKind.data1 := by
    intro i hi
    have hne : i ≠ p_e + (k : ℤ) := by omega
    simp only [htp₁, if_neg hne]
    by_cases hpe : i = p_e
    · rw [hpe]
      exact Or.inr (Or.inl hmarker)
    · rw [htrail i (by omega) (by omega)]
      exact Or.inl rfl
  have hbound₂ : cfg₁.tape ((p_e + (k : ℤ) - 1) - (k : ℤ)) = Sym.boundary := by
    have hne : (p_e + (k : ℤ) - 1) - (k : ℤ) ≠ p_e + (k : ℤ) := by omega
    simp only [htp₁, if_neg hne]
    rw [show (p_e + (k : ℤ) - 1) - (k : ℤ) = p_e - 1 from by omega]
    exact hbound0
  rcases fire_west8 k (p_e + (k : ℤ) - 1) cfg₁.tape hdata₂ hbound₂
    with ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, htp₂, hlen₂⟩
  -- ── 9 西扫（n = p_e − 2） ──
  have hn₂ : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 := Int.toNat_of_nonneg (by omega)
  have hdata₃ : ∀ i : ℤ, 1 ≤ i ∧ i ≤ (((p_e - 2).toNat : ℕ) : ℤ) →
      (cfg₂.tape i).1 = SymKind.data0 ∨ (cfg₂.tape i).1 = SymKind.data1 := by
    intro i hi
    rw [hn₂] at hi
    have hne : i ≠ p_e + (k : ℤ) := by omega
    simp only [htp₂, htp₁, if_neg hne]
    exact hbwd i hi.1 (by omega)
  have hbound₃ : cfg₂.tape 0 = Sym.boundary := by
    have hne : (0 : ℤ) ≠ p_e + (k : ℤ) := by omega
    simp only [htp₂, htp₁, if_neg hne]
    exact hboundL
  rcases fire_west9 ((p_e - 2).toNat) cfg₂.tape hdata₃ hbound₃
    with ⟨π₃, cfg₃, hs₃, hst₃, hhd₃, htp₃, hlen₃⟩
  -- ── 12 记位（k−1 个已标记格） ──
  have hmarked₄ : ∀ i : ℕ, i < k - 1 →
      (cfg₃.tape (1 + (i : ℤ))).2 = true ∧
        ((cfg₃.tape (1 + (i : ℤ))).1 = SymKind.data0 ∨
          (cfg₃.tape (1 + (i : ℤ))).1 = SymKind.data1) := by
    intro i hi
    have hne : (1 : ℤ) + (i : ℤ) ≠ p_e + (k : ℤ) := by omega
    have h1 : cfg₃.tape (1 + (i : ℤ)) = tape (1 + (i : ℤ)) := by
      simp only [htp₃, htp₂, htp₁, if_neg hne]
    rw [h1]
    exact ⟨hmarks (1 + (i : ℤ)) (by omega) (by omega),
      hbwd (1 + (i : ℤ)) (by omega) (by omega)⟩
  have hstop₄ : (cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ))).2 = false ∧
      ((cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ))).1 = SymKind.data0 ∨
        (cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ))).1 = SymKind.data1) := by
    have hne : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) ≠ p_e + (k : ℤ) := by omega
    have h1 : cfg₃.tape (1 + ((k - 1 : ℕ) : ℤ)) = tape (1 + ((k - 1 : ℕ) : ℤ)) := by
      simp only [htp₃, htp₂, htp₁, if_neg hne]
    rw [h1, hkpos]
    exact ⟨hflagFree (k : ℤ) le_rfl hkpe, hbwd (k : ℤ) (by omega) hkpe⟩
  rcases counter12 (k - 1) 1 cfg₃.tape hmarked₄ hstop₄
    with ⟨π₄, cfg₄, hs₄, hst₄, hhd₄, hkeep₄, hwrite₄, hside₄, hlen₄⟩
  -- ── 81 返扫（n₃ = p_e − k，自 k+1） ──
  have hn₃ : (((p_e - (k : ℤ)).toNat : ℕ) : ℤ) = p_e - (k : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have hdata₅ : ∀ i : ℕ, i < (p_e - (k : ℤ)).toNat →
      (cfg₄.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.data0 ∨
        (cfg₄.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.data1 ∨
        (cfg₄.tape ((k : ℤ) + 1 + (i : ℤ))).1 = SymKind.boundary := by
    intro i hi
    have hle : (k : ℤ) + 1 + (i : ℤ) ≤ p_e := by omega
    have h1 : cfg₄.tape ((k : ℤ) + 1 + (i : ℤ)) = cfg₃.tape ((k : ℤ) + 1 + (i : ℤ)) :=
      hside₄ _ (Or.inr (by omega))
    rw [h1]
    have hne2 : (k : ℤ) + 1 + (i : ℤ) ≠ p_e + (k : ℤ) := by omega
    have h3 : cfg₃.tape ((k : ℤ) + 1 + (i : ℤ)) = tape ((k : ℤ) + 1 + (i : ℤ)) := by
      simp only [htp₃, htp₂, htp₁, if_neg hne2]
    rw [h3]
    by_cases hp0 : (k : ℤ) + 1 + (i : ℤ) = p_e - 1
    · rw [hp0, hbound0]
      exact Or.inr (Or.inr rfl)
    · by_cases hp1 : (k : ℤ) + 1 + (i : ℤ) = p_e
      · rw [hp1, hmarker]
        exact Or.inl rfl
      · rcases hbwd ((k : ℤ) + 1 + (i : ℤ)) (by omega) (by omega) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  have hcons₅ : cfg₄.tape ((k : ℤ) + 1 + ((p_e - (k : ℤ)).toNat : ℤ)) = Sym.consumed := by
    rw [hn₃]
    have hpos : (k : ℤ) + 1 + (p_e - (k : ℤ)) = p_e + 1 := by omega
    rw [hpos]
    have h5 : cfg₄.tape (p_e + 1) = cfg₃.tape (p_e + 1) :=
      hside₄ _ (Or.inr (by omega))
    rw [h5]
    by_cases hk1 : k = 1
    · subst hk1
      simp only [htp₃, htp₂, htp₁]
      rw [if_pos (show p_e + 1 = p_e + ((1 : ℕ) : ℤ) from rfl)]
    · have hne : p_e + 1 ≠ p_e + (k : ℤ) := by omega
      simp only [htp₃, htp₂, htp₁, if_neg hne]
      exact htrail (p_e + 1) le_rfl (by omega)
  rcases return81 ((p_e - (k : ℤ)).toNat) ((k : ℤ) + 1) cfg₄.tape hdata₅ hcons₅
    with ⟨π₅, cfg₅, hs₅, hst₅, hhd₅, htp₅, hlen₅⟩
  -- footprint：`{k, q}` 外格子经 12 记位/81 返扫保持（位0轮：12 只写 k）
  have hcfgDC : ∀ i : ℤ, i ≠ (k : ℤ) → cfg₄.tape i = cfg₃.tape i := by
    intro i hne
    by_cases h1 : i < 1
    · exact hside₄ i (Or.inl h1)
    · by_cases h2 : i ≤ (k : ℤ) - 1
      · obtain ⟨jj, rfl⟩ : ∃ jj : ℕ, (1 : ℤ) + (jj : ℤ) = i :=
          ⟨(i - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
        exact hkeep₄ jj (by omega)
      · exact hside₄ i (Or.inr (by omega))
  have hcfgCB : ∀ i : ℤ, i ≠ p_e + (k : ℤ) → cfg₃.tape i = tape i := by
    intro i hne
    simp only [htp₃, htp₂, htp₁, if_neg hne]
  have hkept : ∀ i : ℤ, i ≠ (k : ℤ) → i ≠ p_e + (k : ℤ) → cfg₅.tape i = tape i := by
    intro i h1 h2
    rw [htp₅]
    rw [hcfgDC i h1]
    exact hcfgCB i h2
  refine ⟨π₁ ++ (π₂ ++ (π₃ ++ (π₄ ++ π₅))), cfg₅, ?_, hst₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e12 : cfg₁ = SymConfig.mk 8 cfg₁.tape (p_e + (k : ℤ) - 1) := by
      rw [← hst₁, ← hhd₁]
    have e23 : cfg₂ = SymConfig.mk 9 cfg₂.tape ((p_e + (k : ℤ) - 1) - (k : ℤ) - 1) := by
      rw [← hst₂, ← hhd₂]
    have e34 : cfg₃ = SymConfig.mk 12 cfg₃.tape (1 : ℤ) := by
      rw [← hst₃, ← hhd₃]
    have e45 : cfg₄ = SymConfig.mk 81 cfg₄.tape (1 + ((k - 1 : ℕ) : ℤ) + 1) := by
      rw [← hst₄, ← hhd₄]
    have hcast23 : (p_e + (k : ℤ) - 1) - (k : ℤ) - 1 = (((p_e - 2).toNat : ℕ) : ℤ) := by
      rw [hn₂]; omega
    have hcast45 : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) + 1 := by omega
    have c45 : SymSteps VerifierSym.transition cfg₄ π₅ cfg₅ := by
      rw [e45, hcast45]
      exact hs₅
    have a45 := symSteps_append_concat π₄ π₅ hs₄ c45
    have c34 : SymSteps VerifierSym.transition cfg₃ (π₄ ++ π₅) cfg₅ := by
      rw [e34]
      exact a45
    have a34 := symSteps_append_concat π₃ (π₄ ++ π₅) hs₃ c34
    have c23 : SymSteps VerifierSym.transition cfg₂ (π₃ ++ (π₄ ++ π₅)) cfg₅ := by
      rw [e23, hcast23]
      exact a34
    have a23 := symSteps_append_concat π₂ (π₃ ++ (π₄ ++ π₅)) hs₂ c23
    have c12 : SymSteps VerifierSym.transition cfg₁ (π₂ ++ (π₃ ++ (π₄ ++ π₅))) cfg₅ := by
      rw [e12]
      exact a23
    exact symSteps_append_concat π₁ _ hs₁ c12
  · rw [hhd₅]
    omega
  · simp only [List.length_append]
    have hb2 : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 := hn₂
    have hb3 : (((p_e - (k : ℤ)).toNat : ℕ) : ℤ) = p_e - (k : ℤ) := hn₃
    omega
  · -- keepLow：`i < k` 保持
    intro i hi
    exact hkept i (by omega) (by omega)
  · -- markK：cell k 盖章（m、data）
    have h₁ : cfg₅.tape (k : ℤ) = cfg₄.tape (k : ℤ) := by rw [htp₅]
    have h₂ : cfg₄.tape (k : ℤ) = Sym.mk (cfg₃.tape (k : ℤ)).1 true := by
      rw [← hkpos]
      exact hwrite₄
    refine ⟨?_, ?_⟩
    · rw [h₁, h₂]
      rfl
    · rw [h₁, h₂]
      have hk₃ : (cfg₃.tape (k : ℤ)).1 = SymKind.data0 ∨ (cfg₃.tape (k : ℤ)).1 = SymKind.data1 := by
        rw [hcfgCB (k : ℤ) (by omega)]
        exact hbwd (k : ℤ) (by omega) hkpe
      rcases hk₃ with h | h
      · exact Or.inl h
      · exact Or.inr h
  · -- midData：`k < i ≤ p_e−2` 保持（d0 轮：12 只写 k）
    intro i hik hipe
    exact hkept i (by omega) (by omega)
  · -- keepWin：`[p_e−1, p_e]`、旧 trail 段与高区保持
    intro i hw
    apply hkept i
    · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
    · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 <;> omega
  · -- burnQ：q = p_e+k 烧成 consumed
    have h₁ : cfg₅.tape (p_e + (k : ℤ)) = cfg₄.tape (p_e + (k : ℤ)) := by rw [htp₅]
    have h₂ : cfg₄.tape (p_e + (k : ℤ)) = cfg₃.tape (p_e + (k : ℤ)) :=
      hside₄ _ (Or.inr (by omega))
    rw [h₁, h₂]
    simp only [htp₃, htp₂, htp₁, ite_true]
  · -- krel：cell k kind 保持（d0 轮无减法：12 写 mk kind true）
    have h₁ : cfg₅.tape (k : ℤ) = cfg₄.tape (k : ℤ) := by rw [htp₅]
    have h₂ : cfg₄.tape (k : ℤ) = Sym.mk (cfg₃.tape (k : ℤ)).1 true := by
      rw [← hkpos]
      exact hwrite₄
    have hkk : (cfg₃.tape (k : ℤ)).1 = (tape (k : ℤ)).1 := by
      simp only [htp₃, htp₂, htp₁, if_neg (by omega : (k : ℤ) ≠ p_e + (k : ℤ))]
    rw [h₁, h₂, hkk]; rfl

/-- [13 出口件] 自 `13 @ (p_e+2)` 沿走廊（已消耗格 `[p_e+2, p_e+k]`）扫到出口格 `p_e+k+1`：
    数据格 → `5 @ p_e+k+1`（S，下一轮入口）；sel/nosel/#₁ → `84 @ p_e+k`（L，进入清尾）。
    tape 全程不变；长度 = k（中轮与末轮同长）。 -/
lemma exit13 (p_e : ℤ) (k : ℕ) (tape : ℤ → Sym)
    (hk : 1 ≤ k)
    (hconsE : ∀ i : ℤ, p_e + 2 ≤ i → i ≤ p_e + (k : ℤ) → tape i = Sym.consumed)
    (hexit : (tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 13 tape (p_e + 2)) π cfg' ∧
        π.length = k ∧ cfg'.tape = tape ∧
        ((cfg'.state = 5 ∧ cfg'.headPos = p_e + (k : ℤ) + 1 ∧
            ((tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
              (tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1)) ∨
          (cfg'.state = 84 ∧ cfg'.headPos = p_e + (k : ℤ) ∧
            ((tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
              (tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
              (tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary))) := by
  have hpexit : (p_e + 2) + ((k - 1 : ℕ) : ℤ) = p_e + (k : ℤ) + 1 := by omega
  have hpexitL : (p_e + 2) + ((k - 1 : ℕ) : ℤ) - 1 = p_e + (k : ℤ) := by omega
  rcases corridor13 (k - 1) (p_e + 2) tape
    (by
      intro i hi
      exact hconsE (p_e + 2 + (i : ℤ)) (by omega) (by omega))
    (by rw [hpexit]; exact hexit)
    with ⟨π, cfg', hs, hkeepc, hkeepl, hlen, hdis⟩
  have hexitkeep : cfg'.tape ((p_e + 2) + ((k - 1 : ℕ) : ℤ)) =
      tape ((p_e + 2) + ((k - 1 : ℕ) : ℤ)) := by
    rcases hdis with ⟨-, -, -, hx, -⟩ | ⟨-, -, -, hx, -⟩ <;> exact hx
  have hright : ∀ i : ℤ, (p_e + 2) + ((k - 1 : ℕ) : ℤ) < i → cfg'.tape i = tape i := by
    intro i hi
    rcases hdis with ⟨-, -, -, -, hx⟩ | ⟨-, -, -, -, hx⟩ <;> exact hx i hi
  refine ⟨π, cfg', hs, ?_, ?_, ?_⟩
  · omega
  · funext i
    by_cases h1 : i < p_e + 2
    · exact hkeepl i h1
    · by_cases h2 : i < (p_e + 2) + ((k - 1 : ℕ) : ℤ)
      · have hicast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e + 2) by omega)
        have hi' : (i - (p_e + 2)).toNat < k - 1 := by omega
        have hpos : (p_e + 2) + (((i - (p_e + 2)).toNat : ℕ) : ℤ) = i := by omega
        rw [← hpos]
        exact hkeepc ((i - (p_e + 2)).toNat) hi'
      · by_cases h3 : i = (p_e + 2) + ((k - 1 : ℕ) : ℤ)
        · rw [h3]
          exact hexitkeep
        · exact hright i (by omega)
  · rcases hdis with ⟨hst, hhd, hkx, -, -⟩ | ⟨hst, hhd, hkx, -, -⟩
    · left
      exact ⟨hst, by rw [hhd, hpexit], by rw [← hpexit]; exact hkx⟩
    · right
      exact ⟨hst, by rw [hhd, hpexitL], by rw [← hpexit]; exact hkx⟩

/-- [步 · 20→21] 20 读 `#₀`：写 d0（占位扩展首格）、R → `21 @ p₀+1`（单步）。 -/
lemma step20_21 (p₀ : ℤ) (tape : ℤ → Sym) (hb : tape p₀ = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 20 tape p₀) π cfg' ∧
      cfg'.state = 21 ∧ cfg'.headPos = p₀ + 1 ∧
      cfg'.tape = (fun i => if i = p₀ then Sym.data0 else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
  let step : SymStep := { fromState := 20, readSym := tape p₀, result := r }
  have htrans : step.result ∈ VerifierSym.transition (20, tape p₀) := by
    simp only [step, r, hb]
    decide
  refine ⟨[step], symStepConfig (SymConfig.mk 20 tape p₀) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 20 tape p₀) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
  · funext i
    by_cases h₂ : i = p₀ <;> simp [symStepConfig, step, r, h₂]
  · simp

/-- [步 · 51→4] 51 读 d0：写 `#₀`（对 q 盖章）、R → `4 @ q+1`（单步）。 -/
lemma step51_4 (q : ℤ) (tape : ℤ → Sym) (h : tape q = Sym.data0) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 51 tape q) π cfg' ∧
      cfg'.state = 4 ∧ cfg'.headPos = q + 1 ∧
      cfg'.tape = (fun i => if i = q then Sym.boundary else tape i) ∧
      π.length = 1 := by
  let r : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
  let step : SymStep := { fromState := 51, readSym := tape q, result := r }
  have htrans : step.result ∈ VerifierSym.transition (51, tape q) := by
    simp only [step, r, h]
    decide
  refine ⟨[step], symStepConfig (SymConfig.mk 51 tape q) step.result, ?_, rfl, ?_, ?_, ?_⟩
  · refine SymSteps.cons [] step (SymConfig.mk 51 tape q) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans
  · simp [symStepConfig, step, r, Dir.toInt]
  · funext i
    by_cases h₂ : i = q <;> simp [symStepConfig, step, r, h₂]
  · simp

set_option maxHeartbeats 900000 in -- 因：轮/轮链 if-链项重写需高预算
/-- [清尾 · C1] 元素末轮出口：`13 @ (p_e+2)`（出口格 ∈ {sel,nosel,#₁}）→ exit13 → `84 @ (p_e+k)`
    → `rewind84_87`（84→87→20）→ `20 @ (p_e−1)`。清标 [1,k]、区域外保持；
    长度精确式 `2k + 2·(p_e−2).toNat + 5`。 -/
lemma cleanup_unit (p_e : ℤ) (k : ℕ) (tape : ℤ → Sym)
    (hk : 1 ≤ k)
    (hkpe : (k : ℤ) ≤ p_e - 2)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) → tape i = Sym.consumed)
    (hexit : (tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary)
    (hmarker : (tape p_e).1 = SymKind.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true)
    (hmarkk : (tape (k : ℤ)).2 = true)
    (hflagFree : ∀ i : ℤ, (k : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 13 tape (p_e + 2)) π cfg' ∧
        cfg'.state = 20 ∧ cfg'.headPos = p_e - 1 ∧
        (π.length : ℤ) = 2 * (k : ℤ) + 2 * (((p_e - 2).toNat) : ℤ) + 5 ∧
        (∀ i : ℕ, i < k → cfg'.tape (1 + (i : ℤ)) = Sym.mk (tape (1 + (i : ℤ))).1 false) ∧
        (∀ i : ℤ, i < 1 ∨ 1 + (k : ℤ) ≤ i → cfg'.tape i = tape i) := by
  -- 出口段：13 → 84
  have hconsE : ∀ i : ℤ, p_e + 2 ≤ i → i ≤ p_e + (k : ℤ) → tape i = Sym.consumed := by
    intro i h1 h2
    exact htrailK i (by omega) h2
  have hexit5 : (tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary := by
    rcases hexit with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rcases exit13 p_e k tape hk hconsE hexit5 with ⟨π₁, cfg₁, hs₁, hlen₁, htp₁, hdis₁⟩
  have hnot5 : ¬((tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1) := by
    intro h5
    rcases hexit with h | h | h
    · rcases h5 with h' | h'
      · rw [h] at h'
        exact absurd h' (by decide)
      · rw [h] at h'
        exact absurd h' (by decide)
    · rcases h5 with h' | h'
      · rw [h] at h'
        exact absurd h' (by decide)
      · rw [h] at h'
        exact absurd h' (by decide)
    · rcases h5 with h' | h'
      · rw [h] at h'
        exact absurd h' (by decide)
      · rw [h] at h'
        exact absurd h' (by decide)
  have hsthd₁ : cfg₁.state = 84 ∧ cfg₁.headPos = p_e + (k : ℤ) := by
    rcases hdis₁ with h | h
    · exact absurd h.2.2 hnot5
    · exact ⟨h.1, h.2.1⟩
  -- 84 → 20（rewind84_87，p₀ = p_e−1，n_e = k）
  rcases rewind84_87 (p_e - 1) k k tape
    (by
      intro i hi
      rcases hi with ⟨h1, h2⟩
      by_cases hpe : i = p_e
      · rw [hpe]
        exact Or.inr (Or.inl hmarker)
      · rw [htrailK i (by omega) (by omega)]
        exact Or.inl rfl)
    (by
      rw [show p_e - 1 = p_e - 1 from rfl]
      exact hbound0)
    (by
      intro i hi
      exact hbwd i hi.1 (by omega))
    hboundL
    (by
      intro i hi
      by_cases hc : (1 : ℤ) + (i : ℤ) = (k : ℤ)
      · rw [hc]
        exact hmarkk
      · exact hmarks (1 + (i : ℤ)) (by omega) (by omega))
    (by
      by_cases hc : ((1 : ℤ) + (k : ℤ)) ≤ p_e - 2
      · exact hflagFree (1 + (k : ℤ)) (by omega) hc
      · have hpos : (1 : ℤ) + (k : ℤ) = p_e - 1 := by omega
        rw [hpos, hbound0]
        rfl)
    (by
      intro i hi
      exact hbwd i (by omega) (by omega))
    (by
      by_cases hc : ((1 : ℤ) + (k : ℤ)) ≤ p_e - 2
      · rcases hbwd (1 + (k : ℤ)) (by omega) hc with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hpos : (1 : ℤ) + (k : ℤ) = p_e - 1 := by omega
        rw [hpos, hbound0]
        exact Or.inr (Or.inr rfl))
    (by
      intro i hi
      exact hbwd i (by omega) (by omega))
    (by omega)
    with ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, hlen₂, hclr₂, hkeep₂⟩
  have e₁₂ : cfg₁ = SymConfig.mk 84 tape ((p_e - 1) + 1 + (k : ℤ)) := by
    rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
    rw [hsthd₁.1, htp₁]
    rw [hsthd₁.2, show p_e + (k : ℤ) = (p_e - 1) + 1 + (k : ℤ) from by omega]
  have c₁₂ : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
    rw [e₁₂]
    exact hs₂
  refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hs₁ c₁₂, hst₂, hhd₂, ?_, hclr₂, ?_⟩
  · rw [List.length_append, hlen₁, hlen₂]
    have hb : (((p_e - 1) - 1).toNat) = ((p_e - 2).toNat) := by
      congr 1
      omega
    rw [hb]
    omega
  · intro i hi
    exact hkeep₂ i hi

set_option maxHeartbeats 900000 in -- 因：位0轮 if-链项重写需高预算
/-- [占位扩展 · X1] 自 `20 @ (p_e−1)`：step20（#₀→21，写 d0）→ 21-清场骑乘（[p_e, p_e+k] → d0）
    → 终止符：sel/nosel → 51 @ (p_e+k) → 51 盖章（q ↦ #₀）→ `4 @ (q+1)`；
    #₁ → `22 @ (q+1)`。销毁区 [p_e−1, q]（中元素）/ [p_e−1, q] 含 q（末元素）全 d0；
    终止符与区外保持；长度 = k+4（中元素）/ k+3（末元素）。 -/
lemma expand_unit (p_e : ℤ) (k : ℕ) (tape : ℤ → Sym)
    (hk : 1 ≤ k)
    (hmar0 : tape p_e = Sym.data0)
    (hb0 : tape (p_e - 1) = Sym.boundary)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) → tape i = Sym.consumed)
    (hexit : tape (p_e + (k : ℤ) + 1) = Sym.sel ∨
      tape (p_e + (k : ℤ) + 1) = Sym.nosel ∨
      (tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 20 tape (p_e - 1)) π cfg' ∧
        ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (k : ℤ) + 1 ∧
            (π.length : ℤ) = (k : ℤ) + 4 ∧
            cfg'.tape (p_e + (k : ℤ)) = Sym.boundary ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (k + 1) Sym.data0) ∧
            (∀ i : ℤ, i < p_e - 1 → cfg'.tape i = tape i) ∧
            (cfg'.tape (p_e + (k : ℤ) + 1) = tape (p_e + (k : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (k : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
          (cfg'.state = 22 ∧ cfg'.headPos = p_e + (k : ℤ) + 1 ∧
            (π.length : ℤ) = (k : ℤ) + 3 ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (k + 2) Sym.data0) ∧
            (∀ i : ℤ, i < p_e - 1 → cfg'.tape i = tape i) ∧
            (cfg'.tape (p_e + (k : ℤ) + 1) = tape (p_e + (k : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (k : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
      (((tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
      (((tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
        (tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) := by
  rcases step20_21 (p_e - 1) tape hb0 with ⟨π₁, cfg₁, hs₁, hst₁, hhd₁, htp₁, hlen₁⟩
  have htape1p : cfg₁.tape p_e = Sym.data0 := by
    rw [htp₁]
    simp only [if_neg (show p_e ≠ p_e - 1 by omega)]
    exact hmar0
  have hdata₁ : ∀ i : ℕ, i < k → cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.data0 ∨
      cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.data1 ∨
      cfg₁.tape (p_e + 1 + (i : ℤ)) = Sym.consumed := by
    intro i hi
    rw [htp₁]
    simp only [if_neg (show p_e + 1 + (i : ℤ) ≠ p_e - 1 by omega)]
    rw [htrailK (p_e + 1 + (i : ℤ)) (by omega) (by omega)]
    exact Or.inr (Or.inr rfl)
  have hcfg1q : cfg₁.tape (p_e + 1 + (k : ℤ)) = tape (p_e + 1 + (k : ℤ)) := by
    rw [htp₁]
    simp only [if_neg (show p_e + 1 + (k : ℤ) ≠ p_e - 1 by omega)]
  have hend₁ : cfg₁.tape (p_e + 1 + (k : ℤ)) = Sym.sel ∨
      cfg₁.tape (p_e + 1 + (k : ℤ)) = Sym.nosel ∨
      (cfg₁.tape (p_e + 1 + (k : ℤ))).1 = SymKind.boundary := by
    rw [hcfg1q, show p_e + 1 + (k : ℤ) = p_e + (k : ℤ) + 1 from by omega]
    exact hexit
  have hstart₁ : cfg₁.tape p_e = Sym.data0 ∨ cfg₁.tape p_e = Sym.data1 ∨
      cfg₁.tape p_e = Sym.consumed := Or.inl htape1p
  rcases scanClear21_len k p_e cfg₁.tape hstart₁ hdata₁ hend₁ with
    ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, hb22₂, hsel51₂, hta₂, hbnd₂, hleft₂, hkeepE₂, hright₂, hlen₂⟩
  have e₁₂ : cfg₁ = SymConfig.mk 21 cfg₁.tape p_e := by
    rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
    rw [hst₁, hhd₁, show p_e - 1 + 1 = p_e from by omega]
  have c₁₂ : SymSteps VerifierSym.transition cfg₁ π₂ cfg₂ := by
    rw [e₁₂]
    exact hs₂
  have hcellm1 : cfg₂.tape (p_e - 1) = Sym.data0 := by
    rw [hleft₂ (p_e - 1) (by omega), htp₁]
    simp only [ite_true]
  have hq21 : cfg₂.tape (p_e + (k : ℤ)) = Sym.data0 := by
    rw [show p_e + (k : ℤ) = p_e + ((k : ℕ) : ℤ) from rfl]
    rw [hta₂ k (by simp only [List.length_replicate]; omega)]
    simp
  by_cases hbnd : (tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary
  · -- ===== 末元素（#₁）：22 @ (q+1) =====
    have hb22 := hb22₂ (by
      rw [hcfg1q, show p_e + 1 + (k : ℤ) = p_e + (k : ℤ) + 1 from by omega]
      exact hbnd)
    refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hs₁ c₁₂, ?_, ?_, ?_⟩
    · right
      refine ⟨hb22.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hb22.2]
        omega
      · rw [List.length_append, hlen₁, hlen₂]
        omega
      · -- 销毁区 [p_e−1, p_e+k] 全 d0
        intro i hi
        simp only [List.length_replicate] at hi
        rcases i with _ | m
        · change cfg₂.tape (p_e - 1 + (0 : ℤ)) = (List.replicate (k + 2) Sym.data0)[0]
          rw [show p_e - 1 + (0 : ℤ) = p_e - 1 from by ring, hcellm1]
          simp
        · show cfg₂.tape (p_e - 1 + ((m + 1 : ℕ) : ℤ)) =
            (List.replicate (k + 2) Sym.data0)[m + 1]
          rw [show p_e - 1 + ((m + 1 : ℕ) : ℤ) = p_e + (m : ℤ) from by omega]
          rw [hta₂ m (by simp only [List.length_replicate]; omega)]
          simp
      · intro i hi
        rw [hleft₂ i (by omega), htp₁]
        simp only [if_neg (show i ≠ p_e - 1 by omega)]
      · rw [show p_e + (k : ℤ) + 1 = p_e + 1 + (k : ℤ) from by omega]
        rw [hkeepE₂, htp₁]
        simp only [if_neg (show p_e + 1 + (k : ℤ) ≠ p_e - 1 from by omega)]
      · intro i hi
        rw [hright₂ i (by omega), htp₁]
        simp only [if_neg (show i ≠ p_e - 1 by omega)]
    · -- C1：boundary ⟹ 22（本支即 boundary）
      intro _
      exact hb22.1
    · -- C2：sel/nosel ⟹ 4（与 boundary 矛盾）
      intro hsn
      have hsn2 : (cfg₁.tape (p_e + 1 + (k : ℤ))).1 = SymKind.sel ∨
          (cfg₁.tape (p_e + 1 + (k : ℤ))).1 = SymKind.nosel := by
        rw [hcfg1q, show p_e + 1 + (k : ℤ) = p_e + (k : ℤ) + 1 from by omega]
        exact hsn
      have h551 := (hsel51₂ hsn2).1
      rw [hb22.1] at h551
      exact absurd h551 (by decide)
  · -- ===== 中元素（sel/nosel）：51 @ q → 盖章 → 4 @ (q+1) =====
    have hsel51_in : (cfg₁.tape (p_e + 1 + (k : ℤ))).1 = SymKind.sel ∨
        (cfg₁.tape (p_e + 1 + (k : ℤ))).1 = SymKind.nosel := by
      rw [hcfg1q, show p_e + 1 + (k : ℤ) = p_e + (k : ℤ) + 1 from by omega]
      rcases hexit with h | h | h
      · exact Or.inl (by
          have hh := congrArg (fun s : Sym => s.1) h
          simpa [Sym.sel] using hh)
      · exact Or.inr (by
          have hh := congrArg (fun s : Sym => s.1) h
          simpa [Sym.nosel] using hh)
      · exact absurd h hbnd
    have h51 := hsel51₂ hsel51_in
    rcases step51_4 (p_e + (k : ℤ)) cfg₂.tape hq21 with ⟨π₃, cfg₃, hs₃, hst₃, hhd₃, htp₃, hlen₃⟩
    have e₂₃ : cfg₂ = SymConfig.mk 51 cfg₂.tape (p_e + (k : ℤ)) := by
      rw [show cfg₂ = SymConfig.mk cfg₂.state cfg₂.tape cfg₂.headPos from rfl]
      rw [h51.1, h51.2]
    have c₂₃ : SymSteps VerifierSym.transition cfg₂ π₃ cfg₃ := by
      rw [e₂₃]
      exact hs₃
    refine ⟨π₁ ++ (π₂ ++ π₃), cfg₃,
      symSteps_append_concat π₁ (π₂ ++ π₃) hs₁
        (by rw [e₁₂]; exact symSteps_append_concat π₂ π₃ hs₂ c₂₃), ?_, ?_, ?_⟩
    · left
      refine ⟨hst₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hhd₃]
      · rw [List.length_append, List.length_append, hlen₁, hlen₂, hlen₃]
        omega
      · rw [htp₃]
        simp only [ite_true]
      · -- 销毁区 [p_e−1, p_e+k−1] 全 d0（不含盖章格 q）
        intro i hi
        simp only [List.length_replicate] at hi
        rcases i with _ | m
        · change cfg₃.tape (p_e - 1 + (0 : ℤ)) = (List.replicate (k + 1) Sym.data0)[0]
          rw [htp₃]
          simp only [if_neg (show p_e - 1 + (0 : ℤ) ≠ p_e + (k : ℤ) from by omega)]
          rw [show p_e - 1 + (0 : ℤ) = p_e - 1 from by ring, hcellm1]
          simp
        · show cfg₃.tape (p_e - 1 + ((m + 1 : ℕ) : ℤ)) =
            (List.replicate (k + 1) Sym.data0)[m + 1]
          rw [htp₃]
          simp only [if_neg (show p_e - 1 + ((m + 1 : ℕ) : ℤ) ≠ p_e + (k : ℤ) from by omega)]
          rw [show p_e - 1 + ((m + 1 : ℕ) : ℤ) = p_e + (m : ℤ) from by omega]
          rw [hta₂ m (by simp only [List.length_replicate]; omega)]
          simp
      · intro i hi
        rw [htp₃]
        simp only [if_neg (show i ≠ p_e + (k : ℤ) from by omega)]
        rw [hleft₂ i (by omega), htp₁]
        simp only [if_neg (show i ≠ p_e - 1 by omega)]
      · rw [htp₃]
        simp only [if_neg (show p_e + (k : ℤ) + 1 ≠ p_e + (k : ℤ) from by omega)]
        rw [show p_e + (k : ℤ) + 1 = p_e + 1 + (k : ℤ) from by omega]
        rw [hkeepE₂, htp₁]
        simp only [if_neg (show p_e + 1 + (k : ℤ) ≠ p_e - 1 from by omega)]
      · intro i hi
        rw [htp₃]
        simp only [if_neg (show i ≠ p_e + (k : ℤ) from by omega)]
        rw [hright₂ i (by omega), htp₁]
        simp only [if_neg (show i ≠ p_e - 1 from by omega)]
    · -- C1：boundary ⟹ 22（与分支条件 hbnd 矛盾）
      intro hb
      exact absurd hb hbnd
    · -- C2：sel/nosel ⟹ 4（本支）
      intro _
      exact hst₃

/-- [扫描 · 首次 1] 在 `[a, b]` 内找最低的 data1：两侧 kinds 为 data、`b` 处必为 data1。
    归约变量 = `(b − a).toNat`（eq-参数式递归）。 -/
lemma first_d1 : ∀ (m : ℕ) (a b : ℤ) (tape : ℤ → Sym),
    ((b - a).toNat = m) → a ≤ b →
    (∀ i : ℤ, a ≤ i → i ≤ b → (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) →
    (tape b).1 = SymKind.data1 →
    ∃ j : ℤ, a ≤ j ∧ j ≤ b ∧ (∀ i : ℤ, a ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
      (tape j).1 = SymKind.data1
  | 0, a, b, tape, hm, hle, hkinds, htop => by
      have h0 : a = b := by
        have h2 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ b - a by omega)
        omega
      exact ⟨b, by omega, le_rfl, (by intro i h1 h2; omega), htop⟩
  | m + 1, a, b, tape, hm, hle, hkinds, htop => by
      by_cases ha1 : (tape a).1 = SymKind.data1
      · exact ⟨a, le_rfl, hle, (by intro i h1 h2; omega), ha1⟩
      · have ha0 : (tape a).1 = SymKind.data0 := by
          rcases hkinds a le_rfl hle with h | h
          · exact h
          · exact absurd h ha1
        have hm' : ((b - (a + 1)).toNat = m) := by
          have h2 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ b - a by omega)
          have h3 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ b - (a + 1) by omega)
          omega
        rcases first_d1 m (a + 1) b tape hm' (by omega)
            (by intro i h1 h2; exact hkinds i (by omega) h2) htop
          with ⟨j, hj1, hj2, hb, hd⟩
        exact ⟨j, by omega, hj2, (by
          intro i h1 h2
          by_cases hi1 : i = a
          · rw [hi1]; exact ha0
          · exact hb i (by omega) h2), hd⟩

/-- [引理 A · hbor 供给] 区域 `[1, p_e−2]` 内、位置 `≥ k+1` 有 1 ⟹ 借位见证
    （最低 1 位 j、区间 `[k+1, j)` 全 0）——`T_k ≥ 2^{k−1}` 的位模式形式。 -/
lemma hbor_of_top (tape : ℤ → Sym) (p_e : ℤ) (k : ℕ)
    (hkinds : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (htop : ∃ q : ℤ, (k : ℤ) + 1 ≤ q ∧ q ≤ p_e - 2 ∧ (tape q).1 = SymKind.data1)
    : ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1 := by
  rcases htop with ⟨q, hq1, hq2, hqd1⟩
  rcases first_d1 ((q - ((k : ℤ) + 1)).toNat) ((k : ℤ) + 1) q tape rfl (by omega)
      (by intro i h1 h2; exact hkinds i (by omega) (by omega)) hqd1
    with ⟨j, hj1, hj2, hb, hd⟩
  exact ⟨j, hj1, by omega, hb, hd⟩

set_option maxHeartbeats 900000 in -- 因：轮串联四段拼接需高预算

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in
-- 轮串联含四段拼接与 profile 前移，if-链项重写需高预算
/-- [轮串联 · 中轮] 从轮 k 起点 `5 @ (p_e+k)`（`k < n`：出口格为下一位数据格）走完「整轮 + 出口」，
    落在轮 k+1 起点 `5 @ (p_e+k+1)`，profile 整体前移一格；长度精确式
    `2k + 2p_e + 2 + [bit_k]`（位1恰加一 = P1 局部单调口径）。
    借位义务（hborK）为本轮假设——段级由 T-算术（引理 A/B）供给。 -/
lemma round_chain (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k < ebits.length)
    (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hmar0 : tape p_e = Sym.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbwdK : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbitK : ∀ i : ℕ, k ≤ i → i < ebits.length + 1 →
      (tape (p_e + (i : ℤ))).1 = (if ebits.getD (i - 1) false then SymKind.data1 else
          SymKind.data0))
    (hborK : (tape (k : ℤ)).1 = SymKind.data0 →
      ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        cfg'.state = 5 ∧ cfg'.headPos = p_e + (k : ℤ) + 1 ∧
        (π.length : ℤ) = 2 * (k : ℤ) + 2 * p_e + 2 + (if ebits.getD (k - 1) false then 1 else 0) ∧
        cfg'.tape p_e = Sym.data0 ∧
        cfg'.tape (p_e - 1) = Sym.boundary ∧
        cfg'.tape 0 = Sym.boundary ∧
        (∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) → cfg'.tape i = Sym.consumed) ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) → (cfg'.tape i).2 = true) ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).2 = false) ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
          (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
        (∀ i : ℕ, k + 1 ≤ i → i < ebits.length + 1 →
          (cfg'.tape (p_e + (i : ℤ))).1 =
            (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0)) ∧
        (((tape (k : ℤ)).1 = SymKind.data1 ∧ (cfg'.tape (k : ℤ)).1 = SymKind.data0 ∧
            (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
            (∀ i : ℤ, (k : ℤ) < i → i ≤ p_e - 2 → cfg'.tape i = tape i))
          ∨ ((tape (k : ℤ)).1 = SymKind.data0 ∧ (cfg'.tape (k : ℤ)).1 = SymKind.data1 ∧
            (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
            ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
              (tape j).1 = SymKind.data1 ∧
              (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → ((tape i).1 = SymKind.data0 ∧
                (cfg'.tape i).1 = SymKind.data1)) ∧
              (cfg'.tape j).1 = SymKind.data0 ∧
              (∀ i : ℤ, j < i → i ≤ p_e - 2 → cfg'.tape i = tape i))
          ∨ ((∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).1 = (tape i).1) ∧
              ebits.getD (k - 1) false = false)) ∧
        (∀ i : ℤ, p_e + (k : ℤ) < i → cfg'.tape i = tape i) := by
  have hp_e : 3 ≤ p_e := by omega
  have hkpe : (k : ℤ) ≤ p_e - 2 := by omega
  have hbitk : (tape (p_e + (k : ℤ))).1 =
      (if ebits.getD (k - 1) false then SymKind.data1 else SymKind.data0) :=
    hbitK k le_rfl (by omega)
  -- 出口格（q+1）之 kind 的两个否定式（供排除 84 支；经整轮保持后取自 hbitK）
  by_cases hb : ebits.getD (k - 1) false
  · -- ===== 位1：round_to13 =====
    have hbit1 : (tape (p_e + (k : ℤ))).1 = SymKind.data1 := by rw [hbitk, if_pos hb]
    rcases round_to13 p_e k tape hp_e hk1 hkpe hbit1
      (by have h := congrArg (fun s : Sym => s.1) hmar0; simpa [Sym.data0] using h)
      hbound0 hboundL htrailK hbwdK hmarks hflagFree hborK
      with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
        hsplitr⟩
    have hqplus : cfgr.tape (p_e + (k : ℤ) + 1) = tape (p_e + (k : ℤ) + 1) :=
      hkeepWr _ (Or.inr (Or.inr (by omega)))
    have hkindR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 =
        (if ebits.getD k false then SymKind.data1 else SymKind.data0) := by
      rw [hqplus]
      have h2 := hbitK (k + 1) (by omega) (by omega)
      rw [show p_e + ((k + 1 : ℕ) : ℤ) = p_e + (k : ℤ) + 1 from by push_cast; ring] at h2
      exact h2
    have hconsE : ∀ i : ℤ, p_e + 2 ≤ i → i ≤ p_e + (k : ℤ) → cfgr.tape i = Sym.consumed := by
      intro i h1 h2
      by_cases hq : i = p_e + (k : ℤ)
      · rw [hq]; exact hburnr
      · rw [hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
        exact htrailK i (by omega) (by omega)
    have hexit5 : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary := by
      by_cases hb2 : ebits.getD k false
      · rw [hkindR, if_pos hb2]
        exact Or.inr (Or.inl rfl)
      · rw [hkindR, if_neg hb2]
        exact Or.inl rfl
    rcases exit13 p_e k cfgr.tape hk1 hconsE hexit5 with ⟨πe, cfge, hse, hlene, htpe, hdise⟩
    have hkindNextR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 := by
      by_cases hb2 : ebits.getD k false
      · rw [hkindR, if_pos hb2]
        exact Or.inr rfl
      · rw [hkindR, if_neg hb2]
        exact Or.inl rfl
    have hkindNext' : (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.sel ∧
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.nosel ∧
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.boundary := by
      rcases hkindNextR with h | h
      · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
      · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
    have hst5 : cfge.state = 5 ∧ cfge.headPos = p_e + (k : ℤ) + 1 := by
      rcases hdise with h | h
      · exact ⟨h.1, h.2.1⟩
      · exfalso
        rcases h.2.2 with hk | hk | hk
        · exact absurd hk hkindNext'.1
        · exact absurd hk hkindNext'.2.1
        · exact absurd hk hkindNext'.2.2
    have ere : cfgr = SymConfig.mk 13 cfgr.tape (p_e + 2) := by
      rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
      rw [hstr, hhdr]
    refine ⟨πr ++ πe, cfge, symSteps_append_concat πr πe hsr (by rw [ere]; exact hse),
      hst5.1, hst5.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append]; push_cast; rw [hlenr, hlene, if_pos hb]
      omega
    · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, le_rfl⟩)]
      exact hmar0
    · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, by omega⟩)]
      exact hbound0
    · rw [htpe, hkeepLr 0 (by omega)]
      exact hboundL
    · intro i h1 h2
      by_cases hq : i = p_e + (k : ℤ)
      · rw [htpe, hq]; exact hburnr
      · rw [htpe, hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
        exact htrailK i (by omega) (by omega)
    · intro i h1 h2
      by_cases hk : i = (k : ℤ)
      · rw [htpe, hk]; exact hmK2
      · rw [htpe, hkeepLr i (by omega)]
        exact hmarks i (by omega) (by omega)
    · intro i h1 h2
      rw [htpe]
      exact (hmidr i (by omega) (by omega)).2
    · intro i h1 h2
      rw [htpe]
      by_cases hk : i = (k : ℤ)
      · rw [hk]; exact hmKk
      · by_cases hik : i < (k : ℤ)
        · rw [hkeepLr i hik]
          exact hbwdK i (by omega) h2
        · exact (hmidr i (by omega) (by omega)).1
    · intro i h1 h2
      rw [htpe, hkeepWr (p_e + (i : ℤ)) (Or.inr (Or.inr (by omega)))]
      exact hbitK i (by omega) h2
    · -- 分支共轭：转储 round_to13 split（exit13 不动 tape）
      rcases hsplitr with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw, hj0, hup⟩
      · left
        exact ⟨h1, (by rw [htpe]; exact h2), (by intro i hi; rw [htpe]; exact h3 i hi),
          (by intro i hi1 hi2; rw [htpe]; exact h4 i hi1 hi2)⟩
      · right; left
        exact ⟨h1, (by rw [htpe]; exact h2), (by intro i hi; rw [htpe]; exact h3 i hi), j, hj1, hj2,
          hdj,
          (by intro i hi1 hi2; exact ⟨(hw i hi1 hi2).1, by rw [htpe]; exact (hw i hi1 hi2).2⟩),
          (by rw [htpe]; exact hj0),
          (by intro i hi1 hi2; rw [htpe]; exact hup i hi1 hi2)⟩
    · intro i hi
      rw [htpe]
      exact hkeepWr i (Or.inr (Or.inr (by omega)))
  · -- ===== 位0：round_d0 =====
    have hbit0 : (tape (p_e + (k : ℤ))).1 = SymKind.data0 := by rw [hbitk, if_neg hb]
    rcases round_d0 p_e k tape hp_e hk1 hkpe hbit0
      (by have h := congrArg (fun s : Sym => s.1) hmar0; simpa [Sym.data0] using h)
      hbound0 hboundL htrailK hbwdK hmarks hflagFree
      with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
        hkrelr⟩
    have hqplus : cfgr.tape (p_e + (k : ℤ) + 1) = tape (p_e + (k : ℤ) + 1) :=
      hkeepWr _ (Or.inr (Or.inr (by omega)))
    have hkindR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 =
        (if ebits.getD k false then SymKind.data1 else SymKind.data0) := by
      rw [hqplus]
      have h2 := hbitK (k + 1) (by omega) (by omega)
      rw [show p_e + ((k + 1 : ℕ) : ℤ) = p_e + (k : ℤ) + 1 from by push_cast; ring] at h2
      exact h2
    have hconsE : ∀ i : ℤ, p_e + 2 ≤ i → i ≤ p_e + (k : ℤ) → cfgr.tape i = Sym.consumed := by
      intro i h1 h2
      by_cases hq : i = p_e + (k : ℤ)
      · rw [hq]; exact hburnr
      · rw [hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
        exact htrailK i (by omega) (by omega)
    have hexit5 : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary := by
      by_cases hb2 : ebits.getD k false
      · rw [hkindR, if_pos hb2]
        exact Or.inr (Or.inl rfl)
      · rw [hkindR, if_neg hb2]
        exact Or.inl rfl
    rcases exit13 p_e k cfgr.tape hk1 hconsE hexit5 with ⟨πe, cfge, hse, hlene, htpe, hdise⟩
    have hkindNextR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 := by
      by_cases hb2 : ebits.getD k false
      · rw [hkindR, if_pos hb2]
        exact Or.inr rfl
      · rw [hkindR, if_neg hb2]
        exact Or.inl rfl
    have hkindNext' : (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.sel ∧
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.nosel ∧
        (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.boundary := by
      rcases hkindNextR with h | h
      · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
      · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
    have hst5 : cfge.state = 5 ∧ cfge.headPos = p_e + (k : ℤ) + 1 := by
      rcases hdise with h | h
      · exact ⟨h.1, h.2.1⟩
      · exfalso
        rcases h.2.2 with hk | hk | hk
        · exact absurd hk hkindNext'.1
        · exact absurd hk hkindNext'.2.1
        · exact absurd hk hkindNext'.2.2
    have ere : cfgr = SymConfig.mk 13 cfgr.tape (p_e + 2) := by
      rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
      rw [hstr, hhdr]
    refine ⟨πr ++ πe, cfge, symSteps_append_concat πr πe hsr (by rw [ere]; exact hse),
      hst5.1, hst5.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append]; push_cast; rw [hlenr, hlene, if_neg hb]
      omega
    · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, le_rfl⟩)]
      exact hmar0
    · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, by omega⟩)]
      exact hbound0
    · rw [htpe, hkeepLr 0 (by omega)]
      exact hboundL
    · intro i h1 h2
      by_cases hq : i = p_e + (k : ℤ)
      · rw [htpe, hq]; exact hburnr
      · rw [htpe, hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
        exact htrailK i (by omega) (by omega)
    · intro i h1 h2
      by_cases hk : i = (k : ℤ)
      · rw [htpe, hk]; exact hmK2
      · rw [htpe, hkeepLr i (by omega)]
        exact hmarks i (by omega) (by omega)
    · intro i h1 h2
      rw [htpe, hmidr i (by omega) (by omega)]
      exact hflagFree i (by omega) h2
    · intro i h1 h2
      rw [htpe]
      by_cases hk : i = (k : ℤ)
      · rw [hk]; exact hmKk
      · by_cases hik : i < (k : ℤ)
        · rw [hkeepLr i hik]
          exact hbwdK i (by omega) h2
        · rw [hmidr i (by omega) (by omega)]
          exact hbwdK i (by omega) h2
    · intro i h1 h2
      rw [htpe, hkeepWr (p_e + (i : ℤ)) (Or.inr (Or.inr (by omega)))]
      exact hbitK i (by omega) h2
    · -- 分支共轭：位0轮 — 全区位保持（12 星写 mk kind true）+ 位标 getD = false
      right; right
      refine ⟨?_, by simpa only [Bool.not_eq_true] using hb⟩
      intro i h1 h2
      rw [htpe]
      by_cases hk : i < (k : ℤ)
      · rw [hkeepLr i hk]
      · by_cases hk2 : i = (k : ℤ)
        · rw [hk2]; exact hkrelr
        · rw [hmidr i (by omega) h2]
    · intro i hi
      rw [htpe]
      exact hkeepWr i (Or.inr (Or.inr (by omega)))

set_option maxHeartbeats 900000 in -- 因：轮装配 if-链项重写需高预算

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in
-- valT 基础：区域值递归 + 边界/分裂/顶位（供引理 A/B 与 hbor 供给）
/-- [值 · 递归] 区域 `[b, b+m−1]` 的值：格 `b+j̃` 为 data1 时计 `2^{j̃}`（相对第 b 格起）。 -/
def regValA (tape : ℤ → Sym) (b : ℤ) : ℕ → ℤ → ℤ
  | 0, acc => acc
  | m + 1, acc => regValA tape b m (acc + (if (tape (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ)
      ^ m else 0))

/-- [值 · 区域] 区域 `[1, m]`（格 `1+j` 计 `2^j`，LSB 在前）。 -/
def regVal (tape : ℤ → Sym) (m : ℕ) : ℤ := regValA tape 1 m 0

/-- [值 · 单调] 累加单调。 -/
lemma regValA_mono (tape : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a a' : ℤ), a ≤ a' →
    regValA tape b m a ≤ regValA tape b m a' := by
  intro m
  induction m with
  | zero => intro a a' h; exact h
  | succ m ih =>
      intro a a' h
      simp only [regValA]
      apply ih
      by_cases ht : (tape (b + (m : ℤ))).1 = SymKind.data1
      · simp only [if_pos ht]; omega
      · simp only [if_neg ht]; omega

/-- [值 · 区间单调] 区域加长（新格贡献非负）⟹ 累加不减。 -/
lemma regValA_le_ext (tape : ℤ → Sym) (b : ℤ) : ∀ (m c : ℕ) (a : ℤ),
    regValA tape b m a ≤ regValA tape b (m + c) a := by
  intro m c
  induction c with
  | zero => intro a; rw [Nat.add_zero]
  | succ c ih =>
      intro a
      have h1 : regValA tape b (m + c) a ≤
          regValA tape b (m + c) (a + (if (tape (b + ((m + c : ℕ) : ℤ))).1 = SymKind.data1
            then (2 : ℤ) ^ (m + c) else 0)) := by
        apply regValA_mono
        by_cases ht : (tape (b + ((m + c : ℕ) : ℤ))).1 = SymKind.data1
        · rw [if_pos ht]
          have : (0 : ℤ) ≤ (2 : ℤ) ^ (m + c) := by positivity
          omega
        · rw [if_neg ht]
          omega
      have h2 : regValA tape b (m + c) (a + (if (tape (b + ((m + c : ℕ) : ℤ))).1 = SymKind.data1
            then (2 : ℤ) ^ (m + c) else 0)) = regValA tape b ((m + c) + 1) a := by
        rw [regValA]
      calc regValA tape b m a ≤ regValA tape b (m + c) a := ih a
        _ ≤ regValA tape b (m + c) (a + (if (tape (b + ((m + c : ℕ) : ℤ))).1 = SymKind.data1
              then (2 : ℤ) ^ (m + c) else 0)) := h1
        _ = regValA tape b ((m + c) + 1) a := h2
        _ = regValA tape b (m + (c + 1)) a := by
              rw [show m + (c + 1) = (m + c) + 1 from by omega]

/-- [值 · 累加不减] 初值非负则累加值不低于初值。 -/
lemma regValA_ge_acc (tape : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a : ℤ),
    0 ≤ a → a ≤ regValA tape b m a := by
  intro m
  induction m with
  | zero => intro a ha; exact le_rfl
  | succ m ih =>
      intro a ha
      rw [regValA]
      have ha' : (0 : ℤ) ≤ a + (if (tape (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) := by
        by_cases ht : (tape (b + (m : ℤ))).1 = SymKind.data1
        · rw [if_pos ht]
          have : (0 : ℤ) ≤ (2 : ℤ) ^ m := by positivity
          omega
        · rw [if_neg ht]; omega
      refine le_trans ?_ (ih (a + (if (tape (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0)) ha')
      by_cases ht : (tape (b + (m : ℤ))).1 = SymKind.data1
      · rw [if_pos ht]
        have : (0 : ℤ) ≤ (2 : ℤ) ^ m := by positivity
        omega
      · rw [if_neg ht]; omega

/-- [值 · 归零] 区域全 data（kinds）+ 无标 + 区域值 = 0 ⟹ 区域内全 data0。 -/
lemma all_d0_of_regVal_zero (tape : ℤ → Sym) (m : ℕ)
    (hk : ∀ i : ℤ, 1 ≤ i → i ≤ (m : ℤ) →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hfl : ∀ i : ℤ, 1 ≤ i → i ≤ (m : ℤ) → (tape i).2 = false)
    (h0 : regVal tape m = 0) :
    ∀ i : ℤ, 1 ≤ i → i ≤ (m : ℤ) → tape i = Sym.data0 := by
  intro i hi1 hi2
  have hne1 : (tape i).1 ≠ SymKind.data1 := by
    intro hd1
    have hcell : 1 + (((i - 1).toNat : ℕ) : ℤ) = i := by omega
    have hge : (2 : ℤ) ^ ((i - 1).toNat) ≤ regVal tape m := by
      have hle1 : regVal tape ((i - 1).toNat + 1) ≤ regVal tape m := by
        simp only [regVal]
        have hle := regValA_le_ext tape 1 ((i - 1).toNat + 1) (m - ((i - 1).toNat + 1)) 0
        rw [Nat.add_sub_of_le (by omega)] at hle
        exact hle
      have hge1 : (2 : ℤ) ^ ((i - 1).toNat) ≤ regVal tape ((i - 1).toNat + 1) := by
        simp only [regVal]
        rw [regValA]
        have hterm : (if (tape (1 + (((i - 1).toNat : ℕ) : ℤ))).1 = SymKind.data1 then
            (2 : ℤ) ^ ((i - 1).toNat) else 0) = (2 : ℤ) ^ ((i - 1).toNat) := by
          rw [hcell, hd1, if_pos rfl]
        have hacc0 : (0 : ℤ) ≤ 0 + (if (tape (1 + (((i - 1).toNat : ℕ) : ℤ))).1 = SymKind.data1 then
            (2 : ℤ) ^ ((i - 1).toNat) else 0) := by
          rw [hterm]; positivity
        have hmon := regValA_ge_acc tape 1 ((i - 1).toNat)
          (0 + (if (tape (1 + (((i - 1).toNat : ℕ) : ℤ))).1 = SymKind.data1 then
            (2 : ℤ) ^ ((i - 1).toNat) else 0)) hacc0
        rw [hterm] at hmon ⊢
        linarith
      linarith
    have hpos : (0 : ℤ) < (2 : ℤ) ^ ((i - 1).toNat) := by positivity
    linarith
  rcases hk i hi1 hi2 with h | h
  · have heta : tape i = Sym.mk (tape i).1 (tape i).2 := rfl
    rw [heta, h, hfl i hi1 hi2]
    rfl
  · exact absurd h hne1

/-- [值 · 非负] 累加非负。 -/
lemma regValA_nonneg (tape : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a : ℤ), 0 ≤ a →
    0 ≤ regValA tape b m a := by
  intro m
  induction m with
  | zero => intro a h; exact h
  | succ m ih =>
      intro a h
      simp only [regValA]
      apply ih
      by_cases ht : (tape (b + (m : ℤ))).1 = SymKind.data1
      · simp only [if_pos ht]
        have : (0 : ℤ) ≤ (2 : ℤ) ^ m := by positivity
        omega
      · simp only [if_neg ht]; omega

/-- [值 · 上界] `regValA ≤ acc + 2^m − 1`。 -/
lemma regValA_le (tape : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a : ℤ),
    regValA tape b m a ≤ a + (2 : ℤ) ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      intro a
      simp only [regValA, pow_zero]
      omega
  | succ m ih =>
      intro a
      have htwo : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by
        rw [pow_succ]; ring
      simp only [regValA]
      by_cases ht : (tape (b + (m : ℤ))).1 = SymKind.data1
      · simp only [if_pos ht]
        have h2 := ih (a + (2 : ℤ) ^ m)
        have hc : (0 : ℤ) ≤ (2 : ℤ) ^ m := by positivity
        rw [htwo]
        omega
      · simp only [if_neg ht, add_zero]
        have h2 := ih a
        have hc : (0 : ℤ) ≤ (2 : ℤ) ^ m := by positivity
        rw [htwo]
        omega

/-- [值 · 高位归零] 迭代项 `j ∈ [k, k+t)` 格上无 1 ⟹ 累加不变。 -/
lemma regValA_high_zero (tape : ℤ → Sym) (b : ℤ) (k : ℕ) :
    ∀ (t : ℕ) (a : ℤ), (∀ j : ℕ, k ≤ j → j < k + t → (tape (b + (j : ℤ))).1 ≠ SymKind.data1) →
      regValA tape b (k + t) a = regValA tape b k a := by
  intro t
  induction t with
  | zero =>
      intro a h
      rw [Nat.add_zero]
  | succ t ih =>
      intro a h
      have hzero : (tape (b + ((k + t : ℕ) : ℤ))).1 ≠ SymKind.data1 :=
        h (k + t) (by omega) (by omega)
      have hstep : regValA tape b (k + (t + 1)) a =
          regValA tape b (k + t) (a + (if (tape (b + ((k + t : ℕ) : ℤ))).1 = SymKind.data1
            then (2 : ℤ) ^ (k + t) else 0)) := by
        rw [show k + (t + 1) = (k + t) + 1 from by omega, regValA]
      rw [hstep]
      have hz : (if (tape (b + ((k + t : ℕ) : ℤ))).1 = SymKind.data1 then
          (2 : ℤ) ^ (k + t) else 0) = 0 := by
        rw [if_neg hzero]
      rw [hz, add_zero]
      exact ih a (by intro j h1 h2; exact h j h1 (by omega))

/-- [值 · 顶位] `acc + 2^k ≤ 区域值` ⟹ 迭代位置 `j ∈ [k, m)` 内有 data1。 -/
lemma regValA_top (tape : ℤ → Sym) (b : ℤ) (k m : ℕ) (a : ℤ) (hkm : k ≤ m)
    (hge : a + (2 : ℤ) ^ k ≤ regValA tape b m a) :
    ∃ j : ℕ, k ≤ j ∧ j < m ∧ (tape (b + (j : ℤ))).1 = SymKind.data1 := by
  by_contra hc
  have hno : ∀ j : ℕ, k ≤ j → j < m → (tape (b + (j : ℤ))).1 ≠ SymKind.data1 := by
    intro j h1 h2 h3
    exact hc ⟨j, h1, h2, h3⟩
  obtain ⟨t, ht⟩ : ∃ t, m = k + t := ⟨m - k, by omega⟩
  have h1 : regValA tape b m a = regValA tape b k a := by
    rw [ht]
    exact regValA_high_zero tape b k t a (by
      intro j h1 h2
      exact hno j h1 (by omega))
  have h2 := regValA_le tape b k a
  have h3 : regValA tape b m a ≤ a + (2 : ℤ) ^ k - 1 := by
    rw [h1]
    exact h2
  omega

-- 引理 B 工具：累加平移 / 下段全等 / 单格增量 / 整段填充增量
set_option maxHeartbeats 900000 in -- 因：delta/fill 分支演算与归纳需高于默认 200k 的心跳预算
/-- [值 · 累加平移] `regValA (a+c) = regValA a + c`。 -/
lemma regValA_acc_shift (t : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a c : ℤ),
    regValA t b m (a + c) = regValA t b m a + c := by
  intro m
  induction m with
  | zero => intro a c; simp only [regValA]
  | succ m ih =>
      intro a c
      have h1 := ih (a + c) (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0)
      have h2 := ih a (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0)
      have h3 := ih a c
      simp only [regValA]
      rw [h1, h2, h3]
      ring

set_option maxHeartbeats 900000 in -- 因：delta/fill 分支演算与归纳需高于默认 200k 的心跳预算
/-- [值 · 下段全等] 格 `[b, b+m)` 全同 ⟹ 值同。 -/
lemma regValA_congr_below (t t' : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a : ℤ),
    (∀ j : ℕ, j < m → t' (b + (j : ℤ)) = t (b + (j : ℤ))) →
      regValA t' b m a = regValA t b m a := by
  intro m
  induction m with
  | zero => intro a h; simp only [regValA]
  | succ m ih =>
      intro a h
      simp only [regValA]
      have hcell := h m (by omega)
      rw [hcell]
      exact ih (a + (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
        (by intro j hj; exact h j (by omega))

set_option maxHeartbeats 900000 in -- 因：delta/fill 分支演算与归纳需高于默认 200k 的心跳预算
/-- [值 · 单格增量] 仅格 `b+k₀` 变动 ⟹ 值差 = 该格新旧项之差。 -/
lemma regValA_delta_cell (t t' : ℤ → Sym) (b : ℤ) (k₀ : ℕ) :
    ∀ (m : ℕ) (a : ℤ), k₀ < m →
      (∀ j : ℕ, j < m → j ≠ k₀ → t' (b + (j : ℤ)) = t (b + (j : ℤ))) →
      regValA t' b m a = regValA t b m a
        + (if (t' (b + (k₀ : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ k₀ else 0)
        - (if (t (b + (k₀ : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ k₀ else 0) := by
  intro m
  induction m with
  | zero => intro a hlt h; omega
  | succ m ih =>
      intro a hlt h
      simp only [regValA]
      by_cases hm : m = k₀
      · rw [hm]
        have h1' := regValA_acc_shift t' b k₀ a (if (t' (b + (k₀ : ℤ))).1 = SymKind.data1 then (2
            : ℤ) ^ k₀ else 0)
        have h1 := regValA_acc_shift t b k₀ a (if (t (b + (k₀ : ℤ))).1 = SymKind.data1 then (2 :
            ℤ) ^ k₀ else 0)
        have h2 := regValA_congr_below t t' b k₀ a (by
          intro j hj
          exact h j (by omega) (by omega))
        rw [h1', h1, h2]
        omega
      · have hkm : k₀ < m := by omega
        have hih := ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
          hkm (by intro j hj hne; exact h j (by omega) hne)
        rw [hih]
        have hcell : (t' (b + (m : ℤ))).1 = (t (b + (m : ℤ))).1 :=
          congrArg (fun s : Sym => s.1) (h m (by omega) hm)
        rw [hcell]

set_option maxHeartbeats 900000 in -- 因：delta/fill 分支演算与归纳需高于默认 200k 的心跳预算
/-- [值 · 整段填充增量] 段 `[b+k₀, b+j₀)` 由 d0 填成 d1、格 `b+j₀` 由 d1 变非 d1、
    其余不变 ⟹ 值差 = （`m ≤ k₀`: 0；`m ≤ j₀`: `2^m − 2^{k₀}`；否则 `−2^{k₀}`）。 -/
lemma regValA_delta_fill (t t' : ℤ → Sym) (b : ℤ) (k₀ j₀ : ℕ) (hkj : k₀ ≤ j₀) :
    ∀ (m : ℕ) (a : ℤ),
      (∀ j : ℕ, j < m → j < k₀ → t' (b + (j : ℤ)) = t (b + (j : ℤ))) →
      (∀ j : ℕ, k₀ ≤ j → j < m → j < j₀ → (t (b + (j : ℤ))).1 = SymKind.data0) →
      (∀ j : ℕ, k₀ ≤ j → j < m → j < j₀ → (t' (b + (j : ℤ))).1 = SymKind.data1) →
      (∀ j : ℕ, k₀ ≤ j → j < m → j = j₀ → (t (b + (j : ℤ))).1 = SymKind.data1) →
      (∀ j : ℕ, k₀ ≤ j → j < m → j = j₀ → (t' (b + (j : ℤ))).1 ≠ SymKind.data1) →
      (∀ j : ℕ, j₀ < j → j < m → t' (b + (j : ℤ)) = t (b + (j : ℤ))) →
      regValA t' b m a = regValA t b m a +
        (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀ else -((2 : ℤ) ^ k₀)) := by
  intro m
  induction m with
  | zero =>
      intro a h1 h2 h3 h4 h5 h6
      have h0 : (if 0 ≤ k₀ then 0 else
          if 0 ≤ j₀ then (2 : ℤ) ^ 0 - (2 : ℤ) ^ k₀ else -((2 : ℤ) ^ k₀)) = 0 := by
        rw [if_pos (by omega : (0 : ℕ) ≤ k₀)]
      rw [h0]
      simp only [regValA, add_zero]
  | succ m ih =>
      intro a h1 h2 h3 h4 h5 h6
      simp only [regValA]
      by_cases hA : m < k₀
      · -- m < k₀：本步加数相同
        have hTT : (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) =
            (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) := by
          have hcell := h1 m (by omega) hA
          rw [hcell]
        have hFm : (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀
            else -((2 : ℤ) ^ k₀)) = 0 := by rw [if_pos (by omega)]
        have hFc : (if m + 1 ≤ k₀ then 0 else if m + 1 ≤ j₀ then (2 : ℤ) ^ (m + 1) - (2 : ℤ) ^ k₀
            else -((2 : ℤ) ^ k₀)) = 0 := by rw [if_pos (by omega)]
        rw [ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
          (by intro j hj h; exact h1 j (by omega) h)
          (by intro j hj1 hj2 hj3; exact h2 j hj1 (by omega) hj3)
          (by intro j hj1 hj2 hj3; exact h3 j hj1 (by omega) hj3)
          (by intro j hj1 hj2 hj3; exact h4 j hj1 (by omega) hj3)
          (by intro j hj1 hj2 hj3; exact h5 j hj1 (by omega) hj3)
          (by intro j hj1 hj2; exact h6 j hj1 (by omega))]
        rw [hTT, hFm, hFc]
      · have hA' : k₀ ≤ m := by omega
        by_cases hB : m = k₀
        · by_cases hBj : k₀ < j₀
          · -- m = k₀ < j₀：k₀ 格由 d0 补成 d1
            have hTm : (t (b + (m : ℤ))).1 = SymKind.data0 := h2 m (by omega) (by omega) (by omega)
            have hT'm : (t' (b + (m : ℤ))).1 = SymKind.data1 := h3 m (by omega) (by omega) (by
                omega)
            have hT : (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) = 0 := by
              rw [hTm]; exact if_neg (by intro heq; cases heq)
            have hT' : (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) =
                (2 : ℤ) ^ k₀ := by
              rw [hT'm, hB]; exact if_pos rfl
            have hFm : (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀
                else -((2 : ℤ) ^ k₀)) = 0 := by rw [if_pos (by omega)]
            have hFc : (if m + 1 ≤ k₀ then 0 else if m + 1 ≤ j₀ then (2 : ℤ) ^ (m + 1) - (2 : ℤ) ^
                k₀
                else -((2 : ℤ) ^ k₀)) = (2 : ℤ) ^ (k₀ + 1) - (2 : ℤ) ^ k₀ := by
              rw [if_neg (by omega), if_pos (by omega), hB]
            rw [ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
              (by intro j hj h; exact h1 j (by omega) h)
              (by intro j hj1 hj2 hj3; exact h2 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h3 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h4 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h5 j hj1 (by omega) hj3)
              (by intro j hj1 hj2; exact h6 j hj1 (by omega))]
            rw [hT', hT, hFm, hFc]
            simp only [regValA_acc_shift]
            have hp : (2 : ℤ) ^ (k₀ + 1) = (2 : ℤ) ^ k₀ + (2 : ℤ) ^ k₀ := by
              rw [pow_succ]; ring
            omega
          · -- m = k₀ = j₀：k₀ 格由 d1 变非 d1
            have hTj : (t (b + (m : ℤ))).1 = SymKind.data1 := h4 m (by omega) (by omega) (by omega)
            have hT'j : (t' (b + (m : ℤ))).1 ≠ SymKind.data1 := h5 m (by omega) (by omega) (by
                omega)
            have hT : (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) =
                (2 : ℤ) ^ k₀ := by
              rw [hTj, hB]; exact if_pos rfl
            have hT' : (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) = 0 := by
              exact if_neg hT'j
            have hFm : (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀
                else -((2 : ℤ) ^ k₀)) = 0 := by rw [if_pos (by omega)]
            have hFc : (if m + 1 ≤ k₀ then 0 else if m + 1 ≤ j₀ then (2 : ℤ) ^ (m + 1) - (2 : ℤ) ^
                k₀
                else -((2 : ℤ) ^ k₀)) = -((2 : ℤ) ^ k₀) := by
              rw [if_neg (by omega), if_neg (by omega)]
            rw [ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
              (by intro j hj h; exact h1 j (by omega) h)
              (by intro j hj1 hj2 hj3; exact h2 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h3 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h4 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h5 j hj1 (by omega) hj3)
              (by intro j hj1 hj2; exact h6 j hj1 (by omega))]
            rw [hT', hT, hFm, hFc]
            simp only [regValA_acc_shift]
            omega
        · have hB' : k₀ < m := by omega
          by_cases hC : m < j₀
          · -- k₀ < m < j₀：填充步
            have hTm : (t (b + (m : ℤ))).1 = SymKind.data0 := h2 m (by omega) (by omega) hC
            have hT'm : (t' (b + (m : ℤ))).1 = SymKind.data1 := h3 m (by omega) (by omega) hC
            have hT : (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) = 0 := by
              rw [hTm]; exact if_neg (by intro heq; cases heq)
            have hT' : (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) =
                (2 : ℤ) ^ m := by
              rw [hT'm]; exact if_pos rfl
            have hFm : (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀
                else -((2 : ℤ) ^ k₀)) = (2 : ℤ) ^ m - (2 : ℤ) ^ k₀ := by
              rw [if_neg (by omega), if_pos (by omega)]
            have hFc : (if m + 1 ≤ k₀ then 0 else if m + 1 ≤ j₀ then (2 : ℤ) ^ (m + 1) - (2 : ℤ) ^
                k₀
                else -((2 : ℤ) ^ k₀)) = (2 : ℤ) ^ (m + 1) - (2 : ℤ) ^ k₀ := by
              rw [if_neg (by omega), if_pos (by omega)]
            rw [ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
              (by intro j hj h; exact h1 j (by omega) h)
              (by intro j hj1 hj2 hj3; exact h2 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h3 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h4 j hj1 (by omega) hj3)
              (by intro j hj1 hj2 hj3; exact h5 j hj1 (by omega) hj3)
              (by intro j hj1 hj2; exact h6 j hj1 (by omega))]
            rw [hT', hT, hFm, hFc]
            simp only [regValA_acc_shift]
            have hp : (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m + (2 : ℤ) ^ m := by
              rw [pow_succ]; ring
            omega
          · have hC' : j₀ ≤ m := by omega
            by_cases hD : m = j₀
            · -- m = j₀：末端格落
              have hTj : (t (b + (m : ℤ))).1 = SymKind.data1 := h4 m (by omega) (by omega) hD
              have hT'j : (t' (b + (m : ℤ))).1 ≠ SymKind.data1 := h5 m (by omega) (by omega) hD
              have hT : (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) =
                  (2 : ℤ) ^ j₀ := by
                rw [hTj, hD]; exact if_pos rfl
              have hT' : (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) = 0 := by
                exact if_neg hT'j
              have hFm : (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀
                  else -((2 : ℤ) ^ k₀)) = (2 : ℤ) ^ j₀ - (2 : ℤ) ^ k₀ := by
                rw [if_neg (by omega), if_pos (by omega), hD]
              have hFc : (if m + 1 ≤ k₀ then 0 else if m + 1 ≤ j₀ then (2 : ℤ) ^ (m + 1) - (2 : ℤ)
                  ^ k₀
                  else -((2 : ℤ) ^ k₀)) = -((2 : ℤ) ^ k₀) := by
                rw [if_neg (by omega), if_neg (by omega)]
              rw [ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
                (by intro j hj h; exact h1 j (by omega) h)
                (by intro j hj1 hj2 hj3; exact h2 j hj1 (by omega) hj3)
                (by intro j hj1 hj2 hj3; exact h3 j hj1 (by omega) hj3)
                (by intro j hj1 hj2 hj3; exact h4 j hj1 (by omega) hj3)
                (by intro j hj1 hj2 hj3; exact h5 j hj1 (by omega) hj3)
                (by intro j hj1 hj2; exact h6 j hj1 (by omega))]
              rw [hT', hT, hFm, hFc]
              simp only [regValA_acc_shift]
              omega
            · -- j₀ < m：上方全同
              have hTT : (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) =
                  (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0) := by
                have hcell := h6 m (by omega) (by omega)
                rw [hcell]
              have hFm : (if m ≤ k₀ then 0 else if m ≤ j₀ then (2 : ℤ) ^ m - (2 : ℤ) ^ k₀
                  else -((2 : ℤ) ^ k₀)) = -((2 : ℤ) ^ k₀) := by
                rw [if_neg (by omega), if_neg (by omega)]
              have hFc : (if m + 1 ≤ k₀ then 0 else if m + 1 ≤ j₀ then (2 : ℤ) ^ (m + 1) - (2 : ℤ)
                  ^ k₀
                  else -((2 : ℤ) ^ k₀)) = -((2 : ℤ) ^ k₀) := by
                rw [if_neg (by omega), if_neg (by omega)]
              rw [ih (a + (if (t' (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
                (by intro j hj h; exact h1 j (by omega) h)
                (by intro j hj1 hj2 hj3; exact h2 j hj1 (by omega) hj3)
                (by intro j hj1 hj2 hj3; exact h3 j hj1 (by omega) hj3)
                (by intro j hj1 hj2 hj3; exact h4 j hj1 (by omega) hj3)
                (by intro j hj1 hj2 hj3; exact h5 j hj1 (by omega) hj3)
                (by intro j hj1 hj2; exact h6 j hj1 (by omega))]
              rw [hTT, hFm, hFc]

-- 引理 B 本体：轮级值更新（减法语义三条）
set_option maxHeartbeats 900000 in -- 因：引理 B 三条（delta/fill 应用与 omega 展算）需高于默认 200k 的心跳预算
/-- [值 · 位同构] 格位（.1）逐格相同 ⟹ 值同。 -/
lemma regValA_congr_kind (t t' : ℤ → Sym) (b : ℤ) : ∀ (m : ℕ) (a : ℤ),
    (∀ j : ℕ, j < m → (t' (b + (j : ℤ))).1 = (t (b + (j : ℤ))).1) →
      regValA t' b m a = regValA t b m a := by
  intro m
  induction m with
  | zero => intro a h; simp only [regValA]
  | succ m ih =>
      intro a h
      simp only [regValA]
      have hcell := h m (by omega)
      rw [hcell]
      exact ih (a + (if (t (b + (m : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ m else 0))
        (by intro j hj; exact h j (by omega))

set_option maxHeartbeats 900000 in -- 因：引理 B 三条（delta/fill 应用与 omega 展算）需高于默认 200k 的心跳预算
/-- [引理B · 直减] 目标位1：cell k 由 d1 落 d0、其余（k 以下与 k 以上）保持 ⟹ 值 −2^{k−1}。 -/
lemma regVal_step_d1 (t t' : ℤ → Sym) (m k : ℕ)
    (hkl : 1 ≤ k) (hkm : k ≤ m)
    (hlo : ∀ i : ℤ, i < (k : ℤ) → t' i = t i)
    (hk1 : (t (k : ℤ)).1 = SymKind.data1)
    (hk2 : (t' (k : ℤ)).1 = SymKind.data0)
    (hhi : ∀ i : ℤ, (k : ℤ) < i → i ≤ (m : ℤ) → t' i = t i) :
    regVal t' m = regVal t m - (2 : ℤ) ^ (k - 1) := by
  have hd := regValA_delta_cell t t' 1 (k - 1) m 0 (by omega) (by
    intro j hj hne
    by_cases hjk : j < k - 1
    · exact hlo (1 + (j : ℤ)) (by omega)
    · exact hhi (1 + (j : ℤ)) (by omega) (by omega))
  simp only [regVal]
  rw [hd]
  have hidx : (1 : ℤ) + ((k - 1 : ℕ) : ℤ) = (k : ℤ) := by omega
  have h1 : (if (t' (1 + ((k - 1 : ℕ) : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ (k - 1) else 0) = 0
      := by
    rw [hidx]
    exact if_neg (by intro heq; rw [hk2] at heq; cases heq)
  have h2 : (if (t (1 + ((k - 1 : ℕ) : ℤ))).1 = SymKind.data1 then (2 : ℤ) ^ (k - 1) else 0) =
      (2 : ℤ) ^ (k - 1) := by
    rw [hidx]
    exact if_pos hk1
  rw [h1, h2]
  omega

set_option maxHeartbeats 900000 in -- 因：引理 B 三条（delta/fill 应用与 omega 展算）需高于默认 200k 的心跳预算
/-- [引理B · 借位] 目标位0借位：段 `[k, j)` 填 d1、格 j 落 d0 ⟹ 净差仍 −2^{k−1}。 -/
lemma regVal_step_walk (t t' : ℤ → Sym) (m k j : ℕ)
    (hkl : 1 ≤ k) (hkj : k ≤ j) (hkm : k ≤ m) (hjm : j ≤ m)
    (hlo : ∀ i : ℤ, i < (k : ℤ) → t' i = t i)
    (hfill : ∀ i : ℤ, (k : ℤ) ≤ i → i < (j : ℤ) →
      (t i).1 = SymKind.data0 ∧ (t' i).1 = SymKind.data1)
    (hj : (t (j : ℤ)).1 = SymKind.data1 ∧ (t' (j : ℤ)).1 ≠ SymKind.data1)
    (hhi : ∀ i : ℤ, (j : ℤ) < i → i ≤ (m : ℤ) → t' i = t i) :
    regVal t' m = regVal t m - (2 : ℤ) ^ (k - 1) := by
  have hd := regValA_delta_fill t t' 1 (k - 1) (j - 1) (by omega) m 0
    (by intro jj hj1 hj2; exact hlo (1 + (jj : ℤ)) (by omega))
    (by intro jj hj1 hj2 hj3; exact (hfill (1 + (jj : ℤ)) (by omega) (by omega)).1)
    (by intro jj hj1 hj2 hj3; exact (hfill (1 + (jj : ℤ)) (by omega) (by omega)).2)
    (by intro jj hj1 hj2 hj3
        have hidx : (1 : ℤ) + (jj : ℤ) = (j : ℤ) := by omega
        rw [hidx]
        exact hj.1)
    (by intro jj hj1 hj2 hj3
        have hidx : (1 : ℤ) + (jj : ℤ) = (j : ℤ) := by omega
        rw [hidx]
        exact hj.2)
    (by intro jj hj1 hj2; exact hhi (1 + (jj : ℤ)) (by omega) (by omega))
  simp only [regVal]
  rw [hd]
  have hF : (if m ≤ k - 1 then 0 else if m ≤ j - 1 then (2 : ℤ) ^ m - (2 : ℤ) ^ (k - 1)
      else -((2 : ℤ) ^ (k - 1))) = -((2 : ℤ) ^ (k - 1)) := by
    rw [if_neg (by omega), if_neg (by omega)]
  rw [hF]
  omega

set_option maxHeartbeats 900000 in -- 因：引理 B 三条（delta/fill 应用与 omega 展算）需高于默认 200k 的心跳预算
/-- [引理B · 位0轮] 位0（无减法）：逐格位相同 ⟹ 值不变。 -/
lemma regVal_step_d0 (t t' : ℤ → Sym) (m k : ℕ)
    (hlo : ∀ i : ℤ, 1 ≤ i → i < (k : ℤ) → (t' i).1 = (t i).1)
    (hhi : ∀ i : ℤ, (k : ℤ) ≤ i → i ≤ (m : ℤ) → (t' i).1 = (t i).1) :
    regVal t' m = regVal t m := by
  simp only [regVal]
  exact regValA_congr_kind t t' 1 m 0 (by
    intro jj hj
    by_cases hjk : (1 : ℤ) + (jj : ℤ) < (k : ℤ)
    · exact hlo _ (by omega) hjk
    · exact hhi _ (by omega) (by omega))

-- segSrSel 辅助：hbor 构造（R 不动式 ⟹ 借位见证）+ R 不动式转移算术
set_option maxHeartbeats 900000 in -- 因：区域值顶位/转移算术需高于默认 200k 的心跳预算
/-- [hbor 构造] 区域值 `≥ 2^{k−1}`（且 cell k = d0）⟹ 借位见证（最低 1 位 j、`[k+1, j)` 全 0）。 -/
lemma hbor_of_regVal (tape : ℤ → Sym) (p_e : ℤ) (k : ℕ)
    (hp_e : 3 ≤ p_e) (hk1 : 1 ≤ k) (hkpe : (k : ℤ) ≤ p_e - 2)
    (hkinds : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hR : (2 : ℤ) ^ (k - 1) ≤ regVal tape ((p_e - 2).toNat)) :
    (tape (k : ℤ)).1 = SymKind.data0 →
      ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1 := by
  intro hk0
  have hm : (k - 1) ≤ (p_e - 2).toNat := by
    have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
    omega
  have hge : (0 : ℤ) + (2 : ℤ) ^ (k - 1) ≤ regValA tape 1 ((p_e - 2).toNat) 0 := by
    simpa only [zero_add, regVal] using hR
  rcases regValA_top tape 1 (k - 1) ((p_e - 2).toNat) 0 hm hge with ⟨j, hj1, hj2, hjd1⟩
  have hne : (1 : ℤ) + (j : ℤ) ≠ (k : ℤ) := by
    intro heq
    have hk1' : (tape (k : ℤ)).1 = SymKind.data1 := by
      rw [← heq]
      exact hjd1
    rw [hk1'] at hk0
    exact absurd hk0 (by intro h; cases h)
  have hc1 : (k : ℤ) + 1 ≤ 1 + (j : ℤ) := by omega
  have hc2 : (1 : ℤ) + (j : ℤ) ≤ p_e - 2 := by
    have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
    omega
  exact hbor_of_top tape p_e k hkinds ⟨1 + (j : ℤ), hc1, hc2, hjd1⟩

set_option maxHeartbeats 900000 in -- 因：区域值顶位/转移算术需高于默认 200k 的心跳预算
/-- [R 不动式 · 位1] `2^n − 2^{k−1} ≤ R`、`R' = R − 2^{k−1}` ⟹ `2^n − 2^k ≤ R'`。 -/
lemma Rinv_d1 (k n : ℕ) (hk1 : 1 ≤ k) (R R' : ℤ)
    (hR : (2 : ℤ) ^ n - (2 : ℤ) ^ (k - 1) ≤ R)
    (hstep : R' = R - (2 : ℤ) ^ (k - 1)) :
    (2 : ℤ) ^ n - (2 : ℤ) ^ k ≤ R' := by
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk']
    rw [pow_succ]
    ring
  omega

set_option maxHeartbeats 900000 in -- 因：区域值顶位/转移算术需高于默认 200k 的心跳预算
/-- [R 不动式 · 位0] `2^n − 2^{k−1} ≤ R`、`R' = R` ⟹ `2^n − 2^k ≤ R'`。 -/
lemma Rinv_d0 (k n : ℕ) (hk1 : 1 ≤ k) (R R' : ℤ)
    (hR : (2 : ℤ) ^ n - (2 : ℤ) ^ (k - 1) ≤ R)
    (hstep : R' = R) :
    (2 : ℤ) ^ n - (2 : ℤ) ^ k ≤ R' := by
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk']
    rw [pow_succ]
    ring
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (k - 1) := by positivity
  omega

set_option maxHeartbeats 900000 in -- 因：区域值顶位/转移算术需高于默认 200k 的心跳预算
/-- [R 不动式 · 每轮供给] `2^n − 2^{k−1} ≤ R`、`k ≤ n` ⟹ `2^{k−1} ≤ R`（hbor 前提）。 -/
lemma Rinv_ge (k n : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (R : ℤ)
    (hR : (2 : ℤ) ^ n - (2 : ℤ) ^ (k - 1) ≤ R) :
    (2 : ℤ) ^ (k - 1) ≤ R := by
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk']
    rw [pow_succ]
    ring
  have hpk : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ n := pow_le_pow_right₀ (by norm_num) hkn
  omega


set_option maxHeartbeats 900000 in -- 因：末轮链三段拼接需高预算

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in

set_option maxHeartbeats 900000 in
-- 末轮链三段拼接（轮/清尾(含出口)/扩展）＋ d1/d0 汇合＋统一输出面，if-链项重写需高预算
/-- [轮串联 · 末轮] 从轮 n 起点 `5 @ (p_e+n)`（元素末轮；出口格为元素终止符 `p_e+n+1`）走完
    「整轮 → 清尾（含 13 出口）→ 占位扩展」：
    中元素 → `4 @ (p_e+n+1)`（q 格盖 #₀）；末元素 → `22 @ (p_e+n+1)`。
    输出（段末）：销毁区 d0、区内 `[1, p_e+n−1]` 全无标（flags false）且全 data（供下元素 profile）；
    终止符与高区保持。长度 = `2·p_e + 4·n + 2·(p_e−2).toNat + 11 + [bit_n]`（末元素为 +10）。 -/
lemma last_chain (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hn1 : 1 ≤ ebits.length)
    (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hall : ∀ j, j < ebits.length → ebits.getD j false = true)
    (hmar0 : tape p_e = Sym.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → tape i = Sym.consumed)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (ebits.length : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (ebits.length : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbwdK : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbitN : (tape (p_e + (ebits.length : ℤ))).1 =
      (if ebits.getD (ebits.length - 1) false then SymKind.data1 else SymKind.data0))
    (hborK : (tape (ebits.length : ℤ)).1 = SymKind.data0 →
      ∃ j : ℤ, (ebits.length : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (ebits.length : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1)
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary)
    : ∃ π cfg', SymSteps VerifierSym.transition
          (SymConfig.mk 5 tape (p_e + (ebits.length : ℤ))) π cfg' ∧
        ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) = 2 * p_e + 4 * (ebits.length : ℤ) +
              2 * (((p_e - 2).toNat) : ℤ) + 11 +
              (if ebits.getD (ebits.length - 1) false then 1 else 0) ∧
            cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (regVal cfg'.tape ((p_e - 2).toNat) ≥
              regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1)) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
              tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
          (cfg'.state = 22 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) = 2 * p_e + 4 * (ebits.length : ℤ) +
              2 * (((p_e - 2).toNat) : ℤ) + 10 +
              (if ebits.getD (ebits.length - 1) false then 1 else 0) ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 2) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
              tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) ∧
        (regVal cfg'.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1)) := by
  have hp_e : 3 ≤ p_e := by omega
  have hidx : p_e + (ebits.length : ℤ) + 1 = p_e + 1 + (ebits.length : ℤ) := by omega
  have hmarkerK : (tape p_e).1 = SymKind.data0 := by
    have h := congrArg (fun s : Sym => s.1) hmar0
    simpa [Sym.data0] using h
  obtain ⟨πr, cfgr, hsr, hstr, hhdr, hlenForm, hkeepLr, hkeepWr, hburnr, hmK2, hmKk,
    hmidFlag, hmidKind, hbl0, hnet0, hex0⟩ :
      ∃ (πr : List SymStep) (cfgr : SymConfig),
        SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (ebits.length : ℤ))) πr cfgr ∧
        cfgr.state = 13 ∧ cfgr.headPos = p_e + 2 ∧
        (πr.length : ℤ) = (ebits.length : ℤ) + 2 * p_e + 2 +
          (if ebits.getD (ebits.length - 1) false then 1 else 0) ∧
        (∀ i : ℤ, i < (ebits.length : ℤ) → cfgr.tape i = tape i) ∧
        (∀ i : ℤ, ((p_e - 1 ≤ i ∧ i ≤ p_e) ∨ (p_e + 1 ≤ i ∧ i < p_e + (ebits.length : ℤ)) ∨
            p_e + (ebits.length : ℤ) < i) → cfgr.tape i = tape i) ∧
        cfgr.tape (p_e + (ebits.length : ℤ)) = Sym.consumed ∧
        (cfgr.tape (ebits.length : ℤ)).2 = true ∧
        ((cfgr.tape (ebits.length : ℤ)).1 = SymKind.data0 ∨
          (cfgr.tape (ebits.length : ℤ)).1 = SymKind.data1) ∧
        (∀ i : ℤ, (ebits.length : ℤ) < i → i ≤ p_e - 2 → (cfgr.tape i).2 = false) ∧
        (∀ i : ℤ, (ebits.length : ℤ) < i → i ≤ p_e - 2 →
          (cfgr.tape i).1 = SymKind.data0 ∨ (cfgr.tape i).1 = SymKind.data1) ∧
        (cfgr.tape 0 = tape 0) ∧
        (regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1)) ∧
        (regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1)) := by
    by_cases hb : ebits.getD (ebits.length - 1) false
    · -- 位1
      have hbit1 : (tape (p_e + (ebits.length : ℤ))).1 = SymKind.data1 := by
        rw [hbitN, if_pos hb]
      rcases round_to13 p_e ebits.length tape hp_e hn1 hnpe hbit1 hmarkerK
        hbound0 hboundL htrailK hbwdK hmarks hflagFree hborK
        with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
          hsplit1r⟩
      have hlenForm : (πr.length : ℤ) = (ebits.length : ℤ) + 2 * p_e + 2 +
          (if ebits.getD (ebits.length - 1) false then 1 else 0) := by
        rw [hlenr, if_pos hb]
        omega
      have hexr : regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
        rcases hsplit1r with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw, hj0, hup⟩
        · have hstep := regVal_step_d1 tape cfgr.tape ((p_e - 2).toNat) ebits.length hn1
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            h3 h1 h2
            (by intro i hi1 hi2; exact h4 i hi1 (by omega))
          exact hstep
        · let jn : ℕ := j.toNat
          have hjcast : (jn : ℤ) = j := by
            dsimp only [jn]
            exact Int.toNat_of_nonneg (by omega)
          have hstep := regVal_step_walk tape cfgr.tape ((p_e - 2).toNat) ebits.length jn hn1
            (by omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            h3
            (by
              intro i hi1 hi2
              rw [hjcast] at hi2
              by_cases hik : i = (ebits.length : ℤ)
              · rw [hik]
                exact ⟨h1, h2⟩
              · exact ⟨(hw i (by omega) hi2).1, (hw i (by omega) hi2).2⟩)
            (by
              rw [hjcast]
              exact ⟨hdj, by intro hc; rw [hc] at hj0; exact absurd hj0 (by intro h; cases h)⟩)
            (by
              intro i hi1 hi2
              rw [hjcast] at hi1
              exact hup i hi1 (by omega))
          exact hstep
      have hnetr : regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := hexr.ge
      exact ⟨πr, cfgr, hsr, hstr, hhdr, hlenForm, hkeepLr, hkeepWr, hburnr, hmK2, hmKk,
        (by intro i h1 h2; exact (hmidr i h1 h2).2),
        (by intro i h1 h2; exact (hmidr i h1 h2).1),
        (by rw [hkeepLr 0 (by omega)]),
        hnetr, hexr⟩
    · -- 位0
      have hbit0 : (tape (p_e + (ebits.length : ℤ))).1 = SymKind.data0 := by
        rw [hbitN, if_neg hb]
      rcases round_d0 p_e ebits.length tape hp_e hn1 hnpe hbit0 hmarkerK
        hbound0 hboundL htrailK hbwdK hmarks hflagFree
        with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
          hsplit0r⟩
      have hlenForm : (πr.length : ℤ) = (ebits.length : ℤ) + 2 * p_e + 2 +
          (if ebits.getD (ebits.length - 1) false then 1 else 0) := by
        rw [hlenr, if_neg hb]
        omega
      have hnetr : regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
        have hstep := regVal_step_d0 tape cfgr.tape ((p_e - 2).toNat) ebits.length
          (by intro i hi1 hi2; rw [hkeepLr i hi2])
          (by
            intro i hi1 hi2
            by_cases hik : i = (ebits.length : ℤ)
            · rw [hik]
              exact hsplit0r
            · rw [hmidr i (by omega)
                (by
                  have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
                  omega)])
        rw [hstep]
        exact sub_le_self _ (by positivity)
      have hexr : regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
        exfalso
        exact absurd (hall (ebits.length - 1) (by omega)) hb
      exact ⟨πr, cfgr, hsr, hstr, hhdr, hlenForm, hkeepLr, hkeepWr, hburnr, hmK2, hmKk,
        (by intro i h1 h2; rw [hmidr i h1 h2]; exact hflagFree i (by omega) h2),
        (by intro i h1 h2; rw [hmidr i h1 h2]; exact hbwdK i (by omega) h2),
        (by rw [hkeepLr 0 (by omega)]),
        hnetr, hexr⟩
  -- ===== 清尾（含 13 出口 → 84 → 20） =====
  have htrailR : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) → cfgr.tape i = Sym.consumed
      := by
    intro i h1 h2
    by_cases hq : i = p_e + (ebits.length : ℤ)
    · rw [hq]; exact hburnr
    · rw [hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact htrailK i (by omega) (by omega)
  have hexit3R : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
      (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel ∨
      (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
    rw [hkeepWr _ (Or.inr (Or.inr (by omega))), hidx]
    rcases hend with h | h | h
    · exact Or.inl (by
        have h3 := congrArg (fun s : Sym => s.1) h
        simpa [Sym.sel] using h3)
    · exact Or.inr (Or.inl (by
        have h3 := congrArg (fun s : Sym => s.1) h
        simpa [Sym.nosel] using h3))
    · exact Or.inr (Or.inr h)
  have hbwdR : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (cfgr.tape i).1 = SymKind.data0 ∨ (cfgr.tape i).1 = SymKind.data1 := by
    intro i h1 h2
    by_cases hk : i = (ebits.length : ℤ)
    · rw [hk]; exact hmKk
    · by_cases hik : i < (ebits.length : ℤ)
      · rw [hkeepLr i hik]
        exact hbwdK i (by omega) h2
      · exact hmidKind i (by omega) h2
  have hmarksR : ∀ i : ℤ, 1 ≤ i → i ≤ (ebits.length : ℤ) - 1 → (cfgr.tape i).2 = true := by
    intro i h1 h2
    rw [hkeepLr i (by omega)]
    exact hmarks i (by omega) (by omega)
  have hflagFreeR : ∀ i : ℤ, (ebits.length : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (cfgr.tape i).2 = false :=
      by
    intro i h1 h2
    exact hmidFlag i (by omega) h2
  rcases cleanup_unit p_e ebits.length cfgr.tape hn1 hnpe htrailR hexit3R
    (by rw [hkeepWr p_e (Or.inl ⟨by omega, le_rfl⟩)]; exact hmarkerK)
    (by rw [hkeepWr (p_e - 1) (Or.inl ⟨by omega, by omega⟩)]; exact hbound0)
    (by rw [hkeepLr 0 (by omega)]; exact hboundL)
    hbwdR hmarksR hmK2 hflagFreeR
    with ⟨πc, cfgc, hsc, hstc, hhdc, hlenc, hclrc, hkeepc⟩
  -- ===== 扩展 =====
  have hmar0c : cfgc.tape p_e = Sym.data0 := by
    rw [hkeepc p_e (Or.inr (by omega)), hkeepWr p_e (Or.inl ⟨by omega, le_rfl⟩)]
    exact hmar0
  have hb0c : cfgc.tape (p_e - 1) = Sym.boundary := by
    rw [hkeepc (p_e - 1) (Or.inr (by omega)), hkeepWr (p_e - 1) (Or.inl ⟨by omega, by omega⟩)]
    exact hbound0
  have htrailc : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) → cfgc.tape i = Sym.consumed
      := by
    intro i h1 h2
    rw [hkeepc i (Or.inr (by omega))]
    exact htrailR i h1 h2
  have hexitc : cfgc.tape (p_e + (ebits.length : ℤ) + 1) = Sym.sel ∨
      cfgc.tape (p_e + (ebits.length : ℤ) + 1) = Sym.nosel ∨
      (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
    rw [hkeepc _ (Or.inr (by omega)), hkeepWr _ (Or.inr (Or.inr (by omega))), hidx]
    exact hend
  rcases expand_unit p_e ebits.length cfgc.tape hn1 hmar0c hb0c htrailc hexitc
    with ⟨πx, cfgx, hsx, hdisx, hxC1, hxC2⟩
  have hexc : regVal cfgc.tape ((p_e - 2).toNat) = regVal cfgr.tape ((p_e - 2).toNat) := by
    simp only [regVal]
    exact regValA_congr_kind cfgr.tape cfgc.tape 1 ((p_e - 2).toNat) 0 (by
      intro j hj
      by_cases hjk : j < ebits.length
      · simp only [hclrc j hjk, Sym.mk_fst]
      · rw [hkeepc (1 + (j : ℤ)) (Or.inr (by omega))])
  have hnetc : regVal cfgc.tape ((p_e - 2).toNat) ≥
      regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
    rw [hexc]
    exact hnet0
  -- ===== 拼接 =====
  have e13x : cfgr = SymConfig.mk 13 cfgr.tape (p_e + 2) := by
    rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
    rw [hstr, hhdr]
  have ccc : SymSteps VerifierSym.transition cfgr πc cfgc := by
    rw [e13x]; exact hsc
  have e203 : cfgc = SymConfig.mk 20 cfgc.tape (p_e - 1) := by
    rw [show cfgc = SymConfig.mk cfgc.state cfgc.tape cfgc.headPos from rfl]
    rw [hstc, hhdc]
  have cxx : SymSteps VerifierSym.transition cfgc πx cfgx := by
    rw [e203]; exact hsx
  have acx : SymSteps VerifierSym.transition cfgr (πc ++ πx) cfgx :=
    symSteps_append_concat πc πx ccc cxx
  have afinal : SymSteps VerifierSym.transition
      (SymConfig.mk 5 tape (p_e + (ebits.length : ℤ))) (πr ++ (πc ++ πx)) cfgx :=
    symSteps_append_concat πr (πc ++ πx) hsr acx
  rcases hdisx with ⟨hxst, hxhd, hxlen, hxstamp, hxta, hxl, hxt, hxr⟩ |
      ⟨hxst, hxhd, hxlen, hxta, hxl, hxt, hxr⟩
  · -- ===== 中元素 → 4 =====
    refine ⟨πr ++ (πc ++ πx), cfgx, afinal, ?_, ?_, ?_, ?_⟩
    left
    refine ⟨hxst, hxhd, ?_, hxstamp, hxta, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 长度
      rw [List.length_append, List.length_append]
      push_cast
      rw [hlenForm, hlenc, hxlen]
      omega
    · -- 左界保持（cell 0）
      rw [hxl 0 (by omega), hkeepc 0 (Or.inl (by omega)), hkeepLr 0 (by omega)]
    · -- 净值（引理 B 合成）
      have hxk : regVal cfgx.tape ((p_e - 2).toNat) = regVal cfgc.tape ((p_e - 2).toNat) := by
        simp only [regVal]
        exact regValA_congr_kind cfgc.tape cfgx.tape 1 ((p_e - 2).toNat) 0 (by
          intro j hj
          rw [hxl (1 + (j : ℤ)) (by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega)])
      rw [hxk]
      exact hnetc
    · -- 区内无标 `[1, p_e+n−1]`
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hf : (cfgc.tape i).2 = false := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        exact hf
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidFlag i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; rfl
    · -- 区内全 data `[1, p_e+n−1]`
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hk : (cfgc.tape i).1 = (cfgr.tape i).1 := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        rw [hk]
        exact hbwdR i h1 (by omega)
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidKind i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; exact Or.inl rfl
    · -- 终止符保持
      rw [hxt, hkeepc _ (Or.inr (by omega)), hkeepWr _ (Or.inr (Or.inr (by omega)))]
    · -- 高区保持
      intro i hi
      rw [hxr i hi, hkeepc i (Or.inr (by omega)), hkeepWr i (Or.inr (Or.inr (by omega)))]
    · -- C1：boundary ⟹ 22
      intro hb
      have hbcfgr : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
        rw [hkeepWr (p_e + (ebits.length : ℤ) + 1) (Or.inr (Or.inr (by omega)))]
        exact hb
      have hbcfgc : (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
        rw [hkeepc (p_e + (ebits.length : ℤ) + 1) (Or.inr (by omega))]
        exact hbcfgr
      have h22 := hxC1 hbcfgc
      rw [hxst] at h22
      exact absurd h22 (by decide)
    · -- C2：sel/nosel ⟹ 4（本支）
      intro _
      exact hxst
    · -- EX：净值精确式（清尾/扩展保持 + 轮精确）
      have hexx : regVal cfgx.tape ((p_e - 2).toNat) = regVal cfgc.tape ((p_e - 2).toNat) := by
        simp only [regVal]
        exact regValA_congr_kind cfgc.tape cfgx.tape 1 ((p_e - 2).toNat) 0 (by
          intro j hj
          rw [hxl (1 + (j : ℤ)) (by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega)])
      rw [hexx, hexc]
      exact hex0
  · -- ===== 末元素 → 22 =====
    refine ⟨πr ++ (πc ++ πx), cfgx, afinal, ?_, ?_, ?_, ?_⟩
    right
    refine ⟨hxst, hxhd, ?_, hxta, (by rw [hxl 0 (by omega), hkeepc 0 (Or.inl (by omega)),
      hkeepLr 0 (by omega)]), ?_, ?_, ?_, ?_⟩
    · -- 长度
      rw [List.length_append, List.length_append]
      push_cast
      rw [hlenForm, hlenc, hxlen]
      omega
    · -- 区内无标
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hf : (cfgc.tape i).2 = false := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        exact hf
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidFlag i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; rfl
    · -- 区内全 data
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hk : (cfgc.tape i).1 = (cfgr.tape i).1 := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        rw [hk]
        exact hbwdR i h1 (by omega)
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidKind i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; exact Or.inl rfl
    · -- 终止符保持
      rw [hxt, hkeepc _ (Or.inr (by omega)), hkeepWr _ (Or.inr (Or.inr (by omega)))]
    · -- 高区保持
      intro i hi
      rw [hxr i hi, hkeepc i (Or.inr (by omega)), hkeepWr i (Or.inr (Or.inr (by omega)))]
    · -- C1：boundary ⟹ 22（本支）
      intro _
      exact hxst
    · -- C2：sel/nosel ⟹ 4（与 boundary 矛盾）
      intro hsn
      have hsncfgr : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
        rcases hsn with h | h
        · left
          rw [hkeepWr (p_e + (ebits.length : ℤ) + 1) (Or.inr (Or.inr (by omega)))]
          exact h
        · right
          rw [hkeepWr (p_e + (ebits.length : ℤ) + 1) (Or.inr (Or.inr (by omega)))]
          exact h
      have hsncfgc : (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
        rcases hsncfgr with h | h
        · left
          rw [hkeepc (p_e + (ebits.length : ℤ) + 1) (Or.inr (by omega))]
          exact h
        · right
          rw [hkeepc (p_e + (ebits.length : ℤ) + 1) (Or.inr (by omega))]
          exact h
      have h4 := hxC2 hsncfgc
      rw [hxst] at h4
      exact absurd h4 (by decide)
    · -- EX：净值精确式（清尾/扩展保持 + 轮精确）
      have hexx : regVal cfgx.tape ((p_e - 2).toNat) = regVal cfgc.tape ((p_e - 2).toNat) := by
        simp only [regVal]
        exact regValA_congr_kind cfgc.tape cfgx.tape 1 ((p_e - 2).toNat) 0 (by
          intro j hj
          rw [hxl (1 + (j : ℤ)) (by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega)])
      rw [hexx, hexc]
      exact hex0







set_option maxHeartbeats 900000
-- segSrSel 总装：段递归（中轮串联 + 末轮链，R 不动式线程贯穿）
/-- [段 · 递归核心] 从轮 k 起点 `5 @ (p_e+k)` 走完剩余全部轮（k…n）：
    k < n 用 round_chain 前移；k = n 用 last_chain 收段末。
    长度 ≤ `(n−k)·(2n+2p_e+3) + (4p_e+4n+12)`。 -/
lemma segSrSel_aux (ebits : List Bool) (p_e : ℤ)
    (hn1 : 1 ≤ ebits.length) (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hall : ∀ j, j < ebits.length → ebits.getD j false = true) :
    ∀ (m k : ℕ), ebits.length - k = m → 1 ≤ k → k ≤ ebits.length →
      ∀ (tape : ℤ → Sym),
      (2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1) ≤ regVal tape ((p_e - 2).toNat) →
      tape p_e = Sym.data0 →
      tape (p_e - 1) = Sym.boundary →
      tape 0 = Sym.boundary →
      (∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed) →
      (∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true) →
      (∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false) →
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
        (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) →
      (∀ i : ℕ, k ≤ i → i < ebits.length + 1 →
        (tape (p_e + (i : ℤ))).1 =
          (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0)) →
      (tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) →
      ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) ≤ ((ebits.length - k : ℕ) : ℤ) *
              (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) ∧
            cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (regVal cfg'.tape ((p_e - 2).toNat) ≥
              regVal tape ((p_e - 2).toNat) -
                ((2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1))) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) = tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
          (cfg'.state = 22 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) ≤ ((ebits.length - k : ℕ) : ℤ) *
              (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 2) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) = tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) ∧
        (regVal cfg'.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            ((2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1))) := by
  intro m
  induction m with
  | zero =>
      intro k hnk hk1 hkn tape hR hmar0 hbound0 hboundL htrailK hmarks hflagFree hbwdK hbitK hend
      have hk'n : k = ebits.length := by omega
      have hp_e : 3 ≤ p_e := by omega
      rcases last_chain ebits p_e tape hn1 hnpe hall hmar0 hbound0 hboundL
        (by rw [← hk'n]; exact htrailK)
        (by rw [← hk'n]; exact hmarks)
        (by rw [← hk'n]; exact hflagFree)
        hbwdK
        (by rw [← hk'n]; exact hbitK k le_rfl (by omega))
        (by
          rw [← hk'n]
          intro hk0
          exact hbor_of_regVal tape p_e k hp_e hk1 (by omega) hbwdK
            (Rinv_ge k ebits.length hk1 hkn _ hR) hk0)
        hend
        with ⟨π, cfg', hs, hcase, hC1, hC2, hex⟩
      refine ⟨π, cfg', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk'n]
        exact hs
      rcases hcase with ⟨hst, hhd, hlen, hstamp, hagr, hblA, hnetA, hfl, hkd, htk, hhk⟩ |
        ⟨hst, hhd, hlen, hagr, hblA, hfl, hkd, htk, hhk⟩
      · left
        have hinner : (2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1) =
            (2 : ℤ) ^ (ebits.length - 1) := by
          rw [hk'n]
          have hp : (2 : ℤ) ^ (ebits.length) = 2 * (2 : ℤ) ^ (ebits.length - 1) := by
            calc (2 : ℤ) ^ (ebits.length)
                = (2 : ℤ) ^ (ebits.length - 1 + 1) := by
                  rw [show ebits.length - 1 + 1 = ebits.length from by omega]
              _ = 2 * (2 : ℤ) ^ (ebits.length - 1) := by
                  rw [pow_succ']
          rw [hp]
          ring
        refine ⟨hst, hhd, ?_, hstamp, hagr, hblA, (by rw [hinner]; exact hnetA),
          hfl, hkd, htk, hhk⟩
        have hz : ((ebits.length - k : ℕ) : ℤ) = 0 := by omega
        have hcast : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 :=
          Int.toNat_of_nonneg (by omega)
        have hbit : (if ebits.getD (ebits.length - 1) false then (1 : ℤ) else 0) ≤ 1 := by
          split <;> omega
        rw [hlen, hz, hcast]
        omega
      · right
        refine ⟨hst, hhd, ?_, hagr, hblA, hfl, hkd, htk, hhk⟩
        have hz : ((ebits.length - k : ℕ) : ℤ) = 0 := by omega
        have hcast : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 :=
          Int.toNat_of_nonneg (by omega)
        have hbit : (if ebits.getD (ebits.length - 1) false then (1 : ℤ) else 0) ≤ 1 := by
          split <;> omega
        rw [hlen, hz, hcast]
        omega
      · -- C1：boundary ⟹ 22（透传自 last_chain）
        exact hC1
      · -- C2：sel/nosel ⟹ 4（透传自 last_chain）
        exact hC2
      · -- EX：净值精确式（k=n 基底）
        have hinner' : (2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1) =
            (2 : ℤ) ^ (ebits.length - 1) := by
          rw [hk'n]
          have hp : (2 : ℤ) ^ (ebits.length) = 2 * (2 : ℤ) ^ (ebits.length - 1) := by
            calc (2 : ℤ) ^ (ebits.length)
                = (2 : ℤ) ^ (ebits.length - 1 + 1) := by
                  rw [show ebits.length - 1 + 1 = ebits.length from by omega]
              _ = 2 * (2 : ℤ) ^ (ebits.length - 1) := by
                  rw [pow_succ']
          rw [hp]
          ring
        rw [hinner']
        exact hex
  | succ m ih =>
      intro k hnk hk1 hkn tape hR hmar0 hbound0 hboundL htrailK hmarks hflagFree hbwdK hbitK hend
      have hkn' : k < ebits.length := by omega
      have hp_e : 3 ≤ p_e := by omega
      have hkpe : (k : ℤ) ≤ p_e - 2 := by omega
      -- 本轮 hbor（R 不动式 ⟹ 借位见证）
      have hborK : (tape (k : ℤ)).1 = SymKind.data0 →
          ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
            (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
            (tape j).1 = SymKind.data1 := by
        intro hk0
        exact hbor_of_regVal tape p_e k hp_e hk1 hkpe hbwdK
          (Rinv_ge k ebits.length hk1 hkn _ hR) hk0
      rcases round_chain ebits p_e tape k hk1 hkn' hnpe hmar0 hbound0 hboundL
        htrailK hmarks hflagFree hbwdK hbitK hborK
        with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hmar0', hbound0', hboundL',
          htrailK', hmarks', hflagFree', hbwdK', hbitK', hsplit, hkeepHigh'⟩
      -- R 转移（引理 B：按三分支）
      have hRnew : (2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ k ≤
          regVal cfgr.tape ((p_e - 2).toNat) := by
        rcases hsplit with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw, hj0, hup⟩ | ⟨h3, _⟩
        · have hstep := regVal_step_d1 tape cfgr.tape ((p_e - 2).toNat) k hk1 (by omega) h3 h1 h2
            (by
              intro i hi1 hi2
              exact h4 i hi1 (by omega))
          exact Rinv_d1 k ebits.length hk1 _ _ hR hstep
        · let jn : ℕ := j.toNat
          have hjcast : (jn : ℤ) = j := by
            dsimp only [jn]
            exact Int.toNat_of_nonneg (by omega)
          have hstep := regVal_step_walk tape cfgr.tape ((p_e - 2).toNat) k jn hk1
            (by omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            h3
            (by
              intro i hi1 hi2
              rw [hjcast] at hi2
              by_cases hik : i = (k : ℤ)
              · rw [hik]
                exact ⟨h1, h2⟩
              · exact ⟨(hw i (by omega) hi2).1, (hw i (by omega) hi2).2⟩)
            (by
              rw [hjcast]
              exact ⟨hdj, by intro hc; rw [hc] at hj0; exact absurd hj0 (by intro h; cases h)⟩)
            (by
              intro i hi1 hi2
              rw [hjcast] at hi1
              exact hup i hi1 (by omega))
          exact Rinv_d1 k ebits.length hk1 _ _ hR hstep
        · have hstep := regVal_step_d0 tape cfgr.tape ((p_e - 2).toNat) k
            (by intro i hi1 hi2; exact h3 i (by omega) (by omega))
            (by intro i hi1 hi2; exact h3 i (by omega) (by omega))
          exact Rinv_d0 k ebits.length hk1 _ _ hR hstep
      -- 递归：k+1
      have hnk' : ebits.length - (k + 1) = m := by omega
      have hRge : (2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k + 1 - 1) ≤
          regVal cfgr.tape ((p_e - 2).toNat) := by
        rw [show k + 1 - 1 = k from by omega]
        exact hRnew
      rcases ih (k + 1) hnk' (by omega) (by omega) cfgr.tape hRge hmar0' hbound0' hboundL'
        (by rw [show p_e + ((k + 1 : ℕ) : ℤ) - 1 = p_e + (k : ℤ) from by push_cast; ring]
            exact htrailK')
        (by rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) from by push_cast; ring]
            exact hmarks')
        (by rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring]
            exact hflagFree')
        hbwdK' hbitK'
        (by
          rw [hkeepHigh' (p_e + 1 + (ebits.length : ℤ)) (by omega)]
          exact hend)
        with ⟨π₂, cfg₂, hs₂, hcase₂, hC1₂, hC2₂, hEX₂⟩
      have hRex : regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (k - 1) := by
        rcases hsplit with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw, hj0, hup⟩ | ⟨h3, hb3⟩
        · have hstep := regVal_step_d1 tape cfgr.tape ((p_e - 2).toNat) k hk1 (by omega) h3 h1 h2
            (by intro i hi1 hi2; exact h4 i hi1 (by omega))
          exact hstep
        · let jn : ℕ := j.toNat
          have hjcast : (jn : ℤ) = j := by
            dsimp only [jn]
            exact Int.toNat_of_nonneg (by omega)
          have hstep := regVal_step_walk tape cfgr.tape ((p_e - 2).toNat) k jn hk1
            (by omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            h3
            (by
              intro i hi1 hi2
              rw [hjcast] at hi2
              by_cases hik : i = (k : ℤ)
              · rw [hik]
                exact ⟨h1, h2⟩
              · exact ⟨(hw i (by omega) hi2).1, (hw i (by omega) hi2).2⟩)
            (by
              rw [hjcast]
              exact ⟨hdj, by intro hc; rw [hc] at hj0; exact absurd hj0 (by intro h; cases h)⟩)
            (by
              intro i hi1 hi2
              rw [hjcast] at hi1
              exact hup i hi1 (by omega))
          exact hstep
        · exfalso
          exact absurd (hall (k - 1) (by omega)) (by rw [hb3]; decide)
      have hRnetstep : regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (k - 1) := hRex.ge
      have hcont : ∀ (L₂ : ℤ), (π₂.length : ℤ) ≤ L₂ →
          L₂ ≤ ((ebits.length - (k + 1) : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            (4 * p_e + 4 * (ebits.length : ℤ) + 12) →
          ((πr ++ π₂).length : ℤ) ≤ ((ebits.length - k : ℕ) : ℤ) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
        intro L₂ h2 h3
        rw [List.length_append]
        push_cast
        rw [hlenr]
        have hD2 : ((ebits.length - (k + 1) : ℕ) : ℤ) =
            ((ebits.length - k : ℕ) : ℤ) - 1 := by omega
        have hbnd2' : L₂ ≤ (((ebits.length - k : ℕ) : ℤ) - 1) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
          rw [← hD2]
          exact h3
        have hkey : (2 * (k : ℤ) + 2 * p_e + 2 +
            (if ebits.getD (k - 1) false then (1 : ℤ) else 0)) ≤
            2 * (ebits.length : ℤ) + 2 * p_e + 3 := by
          have hbit1 : (if ebits.getD (k - 1) false then (1 : ℤ) else 0) ≤ 1 := by
            split <;> omega
          omega
        have hAlg : (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            ((((ebits.length - k : ℕ) : ℤ) - 1) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
              (4 * p_e + 4 * (ebits.length : ℤ) + 12)) =
            ((ebits.length - k : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
              (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
          ring
        rw [← hAlg]
        linarith
      have hRexT : regVal cfg₂.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            ((2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1)) := by
        have h2 := hEX₂
        rw [show k + 1 - 1 = k from by omega] at h2
        have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
          calc (2 : ℤ) ^ k
              = (2 : ℤ) ^ (k - 1 + 1) := by
                rw [show k - 1 + 1 = k from by omega]
            _ = 2 * (2 : ℤ) ^ (k - 1) := by
                rw [pow_succ']
        linarith
      refine ⟨πr ++ π₂, cfg₂, symSteps_append_concat πr π₂ hsr ?_, ?_, ?_, ?_, ?_⟩
      · have e : cfgr = SymConfig.mk 5 cfgr.tape (p_e + ((k + 1 : ℕ) : ℤ)) := by
          rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
          rw [hstr, hhdr]
          push_cast
          rw [add_assoc]
        rw [e]
        exact hs₂
      · rcases hcase₂ with ⟨hst, hhd, hl, hstamp, hagr₂, hbl₂, hnet₂, hfl, hkd, htk, hhk⟩ | ⟨hst, hhd, hl, hagr, hbl₂, hfl, hkd, htk, hhk⟩
        have hnet : regVal cfg₂.tape ((p_e - 2).toNat) ≥
            regVal tape ((p_e - 2).toNat) -
              ((2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (k - 1)) := by
          have h2 := hnet₂
          rw [show (k + 1) - 1 = k from by omega] at h2
          have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
            calc (2 : ℤ) ^ k
                = (2 : ℤ) ^ (k - 1 + 1) := by
                  rw [show k - 1 + 1 = k from by omega]
              _ = 2 * (2 : ℤ) ^ (k - 1) := by
                  rw [pow_succ']
          linarith
        have hbl : cfg₂.tape 0 = tape 0 := hbl₂.trans (hboundL'.trans hboundL.symm)
        · left
          refine ⟨hst, hhd, hcont _ le_rfl hl, hstamp, hagr₂, hbl, hnet, hfl, hkd, ?_, ?_⟩
          · rw [htk, hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
          · intro i hi
            rw [hhk i hi, hkeepHigh' i (by omega)]
        · right
          refine ⟨hst, hhd, hcont _ le_rfl hl, hagr,
            hbl₂.trans (hboundL'.trans hboundL.symm), hfl, hkd, ?_, ?_⟩
          · rw [htk, hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
          · intro i hi
            rw [hhk i hi, hkeepHigh' i (by omega)]
      · -- C1：boundary ⟹ 22（经本轮 hkeepHigh' 平移）
        intro hb
        have hb' : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
          rw [hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
          exact hb
        exact hC1₂ hb'
      · -- C2：sel/nosel ⟹ 4（经本轮 hkeepHigh' 平移）
        intro hsn
        have hsn' : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
            (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
          rcases hsn with h | h
          · left
            rw [hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
            exact h
          · right
            rw [hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
            exact h
        exact hC2₂ hsn'
      · -- EX：净值精确式（轮精确 + 归纳精确）
        exact hRexT

set_option maxHeartbeats 900000 in -- 因：段装配含入口桥与长度预算算术
-- segSrSel 公开：入口步 + 段递归 + 段界
/-- [段 · 公开接口] 从 `4 @ p_e`（sel 入口）走完整段：入口步（4→5）→ `segSrSel_aux` 全链。
    长度 ≤ `n·(2n+2p_e+3) + (4p_e+4n+13)`。 -/
lemma segSrSel (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hn1 : 1 ≤ ebits.length) (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hall : ∀ j, j < ebits.length → ebits.getD j false = true)
    (hsel : tape p_e = Sym.sel)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbits : ∀ i : ℕ, 1 ≤ i → i < ebits.length + 1 →
      (tape (p_e + (i : ℤ))).1 =
        (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0))
    (hR0 : (2 : ℤ) ^ (ebits.length) - 1 ≤ regVal tape ((p_e - 2).toNat))
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
          (π.length : ℤ) ≤ (ebits.length : ℤ) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            (4 * p_e + 4 * (ebits.length : ℤ) + 13) ∧
          cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
          tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
          (cfg'.tape 0 = tape 0) ∧
          (regVal cfg'.tape ((p_e - 2).toNat) ≥
            regVal tape ((p_e - 2).toNat) - ((2 : ℤ) ^ (ebits.length) - 1)) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
            (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
          (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
            tape (p_e + (ebits.length : ℤ) + 1)) ∧
          (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
        (cfg'.state = 22 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
          (π.length : ℤ) ≤ (ebits.length : ℤ) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            (4 * p_e + 4 * (ebits.length : ℤ) + 13) ∧
          tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 2) Sym.data0) ∧
          (cfg'.tape 0 = tape 0) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
            (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
          (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
            tape (p_e + (ebits.length : ℤ) + 1)) ∧
          (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) ∧
        (regVal cfg'.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) - ((2 : ℤ) ^ (ebits.length) - 1)) := by
  have hp_e : 3 ≤ p_e := by omega
  rcases step4sel p_e tape hsel with ⟨π₁, cfg₁, hs₁, hst₁, hhd₁, htp₁, hlen₁⟩
  -- 入口后 tape 的区域值不变（写格 p_e 在区域之外）
  have hregEq : regVal cfg₁.tape ((p_e - 2).toNat) = regVal tape ((p_e - 2).toNat) := by
    simp only [regVal]
    refine regValA_congr_kind tape cfg₁.tape 1 ((p_e - 2).toNat) 0 ?_
    intro j hj
    have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
    have hcast : (j : ℤ) < p_e - 2 := by
      have h2 : (j : ℤ) < (((p_e - 2).toNat : ℕ) : ℤ) := by exact_mod_cast hj
      rw [hc] at h2
      exact h2
    have hne : (1 : ℤ) + (j : ℤ) ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
  have hR1 : (2 : ℤ) ^ (ebits.length) - (2 : ℤ) ^ (1 - 1) ≤
      regVal cfg₁.tape ((p_e - 2).toNat) := by
    rw [hregEq]
    have h2 : (2 : ℤ) ^ (1 - 1) = 1 := by norm_num
    rw [h2]
    exact hR0
  have hmar0₁ : cfg₁.tape p_e = Sym.data0 := by
    rw [htp₁]
    simp only [ite_true]
  have hbound0₁ : cfg₁.tape (p_e - 1) = Sym.boundary := by
    rw [htp₁]
    simp only [if_neg (by omega : p_e - 1 ≠ p_e)]
    exact hbound0
  have hboundL₁ : cfg₁.tape 0 = Sym.boundary := by
    rw [htp₁]
    simp only [if_neg (by omega : (0 : ℤ) ≠ p_e)]
    exact hboundL
  have htrail1 : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + ((1 : ℕ) : ℤ) - 1 →
      cfg₁.tape i = Sym.consumed := by
    intro i h1 h2
    omega
  have hmarks1 : ∀ i : ℤ, 1 ≤ i → i ≤ ((1 : ℕ) : ℤ) - 1 → (cfg₁.tape i).2 = true := by
    intro i h1 h2
    omega
  have hflagF1 : ∀ i : ℤ, ((1 : ℕ) : ℤ) ≤ i → i ≤ p_e - 2 → (cfg₁.tape i).2 = false := by
    intro i h1 h2
    have hne : i ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hflag0 i h1 h2
  have hbwd1 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (cfg₁.tape i).1 = SymKind.data0 ∨ (cfg₁.tape i).1 = SymKind.data1 := by
    intro i h1 h2
    have hne : i ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hbwd0 i h1 h2
  have hbit1 : ∀ i : ℕ, 1 ≤ i → i < ebits.length + 1 →
      (cfg₁.tape (p_e + (i : ℤ))).1 =
        (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0) := by
    intro i h1 h2
    have hne : p_e + (i : ℤ) ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hbits i h1 h2
  have hend₁ : cfg₁.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      cfg₁.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (cfg₁.tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
    have hne : p_e + 1 + (ebits.length : ℤ) ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hend
  rcases segSrSel_aux ebits p_e hn1 hnpe hall (ebits.length - 1) 1 rfl le_rfl hn1 cfg₁.tape
    hR1 hmar0₁ hbound0₁ hboundL₁ htrail1 hmarks1 hflagF1 hbwd1 hbit1 hend₁
    with ⟨π₂, cfg₂, hs₂, hcase₂, hC1₂, hC2₂, hEX₂⟩
  have e₁ : cfg₁ = SymConfig.mk 5 cfg₁.tape (p_e + ((1 : ℕ) : ℤ)) := by
    rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
    rw [hst₁, hhd₁]
    push_cast
    rfl
  refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hs₁ ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁]
    exact hs₂
  · have hB : (0 : ℤ) ≤ 2 * (ebits.length : ℤ) + 2 * p_e + 3 := by
      have : (0 : ℤ) ≤ (ebits.length : ℤ) := by positivity
      omega
    have hD : (((ebits.length - 1 : ℕ) : ℤ)) ≤ (ebits.length : ℤ) := by omega
    have hmul : ((ebits.length - 1 : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) ≤
        (ebits.length : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) :=
      mul_le_mul_of_nonneg_right hD hB
    have hUp : ∀ (L : ℤ), (π₂.length : ℤ) ≤ L → L ≤
        ((ebits.length - 1 : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
          (4 * p_e + 4 * (ebits.length : ℤ) + 12) →
        ((π₁ ++ π₂).length : ℤ) ≤ (ebits.length : ℤ) *
          (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 13) := by
      intro L h2 h3
      rw [List.length_append]
      push_cast
      rw [hlen₁]
      have h1 : (π₂.length : ℤ) ≤ (ebits.length : ℤ) *
          (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
          (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
        calc (π₂.length : ℤ)
            ≤ ((ebits.length - 1 : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
                (4 * p_e + 4 * (ebits.length : ℤ) + 12) := le_trans h2 h3
          _ ≤ (ebits.length : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
                (4 * p_e + 4 * (ebits.length : ℤ) + 12) := add_le_add hmul le_rfl
      omega
    rcases hcase₂ with ⟨hst, hhd, hl, hstamp, hagr₂, hbl₂, hnet₂, hfl, hkd, htk, hhk⟩ |
      ⟨hst, hhd, hl, hagr, hbl₂, hfl, hkd, htk, hhk⟩
    · left
      have hbl : cfg₂.tape 0 = tape 0 :=
        hbl₂.trans (by rw [htp₁]; simp only [if_neg (by omega : (0 : ℤ) ≠ p_e)])
      have hnet : regVal cfg₂.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - ((2 : ℤ) ^ (ebits.length) - 1) := by
        rw [← hregEq]
        exact hnet₂
      exact ⟨hst, hhd, hUp _ le_rfl hl, hstamp, hagr₂, hbl, hnet, hfl, hkd,
        (by rw [htk, htp₁]; simp only [if_neg (by omega : p_e + (ebits.length : ℤ) + 1 ≠ p_e)]),
        (by
          intro i hi
          rw [hhk i hi, htp₁]
          simp only [if_neg (by omega : i ≠ p_e)])⟩
    · right
      exact ⟨hst, hhd, hUp _ le_rfl hl, hagr,
        hbl₂.trans (by rw [htp₁]; simp only [if_neg (by omega : (0 : ℤ) ≠ p_e)]), hfl, hkd,
        (by rw [htk, htp₁]; simp only [if_neg (by omega : p_e + (ebits.length : ℤ) + 1 ≠ p_e)]),
        (by
          intro i hi
          rw [hhk i hi, htp₁]
          simp only [if_neg (by omega : i ≠ p_e)])⟩
  · -- C1：boundary ⟹ 22（经入口步 htp₁ 平移）
    intro hb
    have hb₁ : (cfg₁.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
      rw [htp₁]
      simp only [if_neg (show p_e + (ebits.length : ℤ) + 1 ≠ p_e by omega)]
      exact hb
    exact hC1₂ hb₁
  · -- C2：sel/nosel ⟹ 4（经入口步 htp₁ 平移）
    intro hsn
    have hsn₁ : (cfg₁.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
        (cfg₁.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
      rw [htp₁]
      simp only [if_neg (show p_e + (ebits.length : ℤ) + 1 ≠ p_e by omega)]
      exact hsn
    exact hC2₂ hsn₁
  · -- EX：净值精确式（入口不动 + 段精确）
    have h2 : (2 : ℤ) ^ (1 - 1) = 1 := by norm_num
    rw [h2] at hEX₂
    rw [← hregEq]
    exact hEX₂

-- ①②④ 相位注册（消费 R12 绿件；命名对齐 Plan.md 相位表）
set_option linter.defProp false in
/-- [① α替换] 初始 → 首入 3（= R12 `segS0`；成本 ≤ L+3）。 -/
def alpha_phase := segS0

set_option linter.defProp false in
/-- [② 格式检验] 3 → 首入 4（= R12 `segS1`；成本 ≤ 2L）。 -/
def format_phase := segS1

set_option linter.defProp false in
/-- [④ 判定] 22 → 100（= R12 `segS3`；成本 ≤ L+2，带不变）。 -/
def judge_phase := segS3

set_option linter.defProp false in
/-- [E · 未选段] 4@nosel → 4/22（= R12 `segSrNosel`；成本 ≤ n+5）。
    sel 段（= `segSrSel`）与本节互为逐元素段的两支。 -/
def round_nosel := segSrNosel

set_option maxHeartbeats 900000
-- 值 · 零延伸：区间全非 data1 ⟹ 值对延伸不变（供元素折叠的区域增长）
/-- [值 · 零延伸] 区间 `[b+m, b+m+c)` 内全非 data1 ⟹ `regValA` 值不变。 -/
lemma regValA_zero_cells (t : ℤ → Sym) (b : ℤ) :
    ∀ (m : ℕ) (c : ℕ) (a : ℤ),
      (∀ j : ℕ, j < c → (t (b + ((m + j : ℕ) : ℤ))).1 ≠ SymKind.data1) →
        regValA t b (m + c) a = regValA t b m a := by
  intro m c
  induction c with
  | zero => intro a _; simp only [Nat.add_zero]
  | succ c ih =>
      intro a h
      have hstep : regValA t b (m + (c + 1)) a =
          regValA t b (m + c)
            (a + (if (t (b + ((m + c : ℕ) : ℤ))).1 = SymKind.data1
              then (2 : ℤ) ^ (m + c) else 0)) := by
        rw [show m + (c + 1) = (m + c) + 1 from by omega]
        simp only [regValA]
      rw [hstep]
      have hz : (if (t (b + ((m + c : ℕ) : ℤ))).1 = SymKind.data1
          then (2 : ℤ) ^ (m + c) else 0) = 0 := by
        rw [if_neg (h c (by omega))]
      rw [hz, add_zero]
      exact ih a (by intro j hj; exact h j (by omega))

/-- [值 · 零延伸·agrees 版] `tapeAgrees t b (replicate c data0)` ⟹ `regValA` 对延伸不变。 -/
lemma regVal_zero_ext (t : ℤ → Sym) (b : ℤ) (m c : ℕ)
    (hagree : tapeAgrees t (b + (m : ℤ)) (List.replicate c Sym.data0)) :
    regValA t b (m + c) 0 = regValA t b m 0 := by
  refine regValA_zero_cells t b m c 0 ?_
  intro j hj hcon
  have h1 : t (b + ((m + j : ℕ) : ℤ)) = Sym.data0 := by
    have hidx : b + ((m + j : ℕ) : ℤ) = (b + (m : ℤ)) + (j : ℤ) := by push_cast; ring
    rw [hidx, hagree j (by simp only [List.length_replicate]; omega)]
    simp only [List.getElem_replicate]
  rw [h1] at hcon
  rw [Sym.data0_fst] at hcon
  exact absurd hcon (by intro h; cases h)


set_option maxHeartbeats 900000


set_option maxHeartbeats 900000


set_option maxHeartbeats 900000


set_option maxHeartbeats 900000


set_option maxHeartbeats 900000


set_option maxHeartbeats 900000
/-- [段界 · 折叠] 逐元素二次界（递归形）：`el(b,p) = b(2b+2p+3) + (4p+4b+13)`。 -/
def foldLenB : List ℕ → ℤ → ℤ
  | [], _ => 0
  | [b], p_e => (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13)
  | b :: c :: rest, p_e =>
      (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) +
        foldLenB (c :: rest) (p_e + (b : ℤ) + 1)

@[simp] lemma foldLenB_nil (p_e : ℤ) : foldLenB [] p_e = 0 := rfl

@[simp] lemma foldLenB_single (b : ℕ) (p_e : ℤ) : foldLenB [b] p_e =
    (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) := rfl

@[simp] lemma foldLenB_cons_cons (b c : ℕ) (rest : List ℕ) (p_e : ℤ) :
    foldLenB (b :: c :: rest) p_e =
      (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) +
        foldLenB (c :: rest) (p_e + (b : ℤ) + 1) := rfl

/-- [段界 · 折叠] 逐元素界非负（p_e ≥ 0）。 -/
lemma foldLenB_nonneg (bs : List ℕ) (p_e : ℤ) (hpe : 0 ≤ p_e) : 0 ≤ foldLenB bs p_e := by
  match bs with
  | [] => simp
  | [b] =>
      have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg _
      have h1 : 0 ≤ (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) := by
        nlinarith [hb, hpe, sq_nonneg (b : ℤ)]
      have h2 : 0 ≤ 4 * p_e + 4 * (b : ℤ) + 13 := by nlinarith [hb, hpe]
      simp only [foldLenB_single]
      linarith [h1, h2]
  | b :: c :: rest =>
      have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg _
      have h1 : 0 ≤ (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) := by
        nlinarith [hb, hpe, sq_nonneg (b : ℤ)]
      have h2 : 0 ≤ 4 * p_e + 4 * (b : ℤ) + 13 := by nlinarith [hb, hpe]
      have h3 : 0 ≤ foldLenB (c :: rest) (p_e + (b : ℤ) + 1) :=
        foldLenB_nonneg (c :: rest) (p_e + (b : ℤ) + 1) (by
          have hb'' : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg _
          linarith)
      simp only [foldLenB_cons_cons]
      nlinarith [h1, h2, h3]

-- E · 逐元素段折叠：全 1 全选族（位长表 bs）从 `4 @ p_e` 串接 `segSrSel` 至 `22`
/-- 族值：`Σ (2^{b_i} − 1)`。 -/
def valSum (bs : List ℕ) : ℤ := (bs.map (fun b => (2 : ℤ) ^ b - 1)).sum

/-- 全 1 全选族的平坦编码：`[位₁^{b₁}, sel, 位₁^{b₂}, …, sel, 位₁^{bₙ}]`
    （末元素之后随实例 #₁，不在列内）。 -/
def famRest : List ℕ → List Sym
  | [] => []
  | [b] => List.replicate b Sym.data1
  | b :: c :: rest => List.replicate b Sym.data1 ++ Sym.sel :: famRest (c :: rest)

@[simp] lemma famRest_nil : famRest [] = [] := rfl

@[simp] lemma famRest_single (b : ℕ) : famRest [b] = List.replicate b Sym.data1 := rfl

@[simp] lemma famRest_cons_cons (b c : ℕ) (rest : List ℕ) :
    famRest (b :: c :: rest) = List.replicate b Sym.data1 ++ Sym.sel :: famRest (c :: rest) :=
  rfl

@[simp] lemma famRest_length_cons_cons (b c : ℕ) (rest : List ℕ) :
    (famRest (b :: c :: rest)).length = b + 1 + (famRest (c :: rest)).length := by
  simp only [famRest_cons_cons, List.length_append, List.length_cons, List.length_replicate]
  omega

@[simp] lemma valSum_nil : valSum [] = 0 := rfl

@[simp] lemma valSum_cons (b : ℕ) (rest : List ℕ) :
    valSum (b :: rest) = ((2 : ℤ) ^ b - 1) + valSum rest := by
  simp only [valSum, List.map_cons, List.sum_cons]

/-- [E · 折叠] 从 `4 @ p_e` 走完全部元素段（全 1 全选族），达 `22 @ (#₁ 格)`。 -/
lemma segSrFold (bs : List ℕ) (p_e : ℤ) (tape : ℤ → Sym)
    (hne : bs ≠ [])
    (hall1 : ∀ b ∈ bs, 1 ≤ b)
    (hpos : ∀ b ∈ bs, (b : ℤ) ≤ p_e - 2)
    (hsel : tape p_e = Sym.sel)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (henc : tapeAgrees tape (p_e + 1) (famRest bs))
    (h1mark : tape (p_e + 1 + ((famRest bs).length : ℤ)) = Sym.mk SymKind.boundary true)
    (hR0 : valSum bs ≤ regVal tape ((p_e - 2).toNat))
    (hR0ex : regVal tape ((p_e - 2).toNat) = valSum bs) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      cfg'.state = 22 ∧
      cfg'.headPos = p_e + 1 + ((famRest bs).length : ℤ) ∧
      cfg'.tape (p_e + 1 + ((famRest bs).length : ℤ)) = Sym.mk SymKind.boundary true ∧
      cfg'.tape 0 = Sym.boundary ∧
      (π.length : ℤ) ≤ foldLenB bs p_e ∧
      (regVal cfg'.tape ((p_e - 2).toNat) = 0) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
        (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).2 = false) ∧
      (∀ i : ℤ, p_e - 1 ≤ i → i ≤ p_e + ((famRest bs).length : ℤ) → cfg'.tape i = Sym.data0) := by
  match bs with
  | [] => exact absurd rfl hne
  | [b] =>
      have hb1 : 1 ≤ b := hall1 b (by simp)
      have hbpe : (b : ℤ) ≤ p_e - 2 := hpos b (by simp)
      have hbits : ∀ i : ℕ, 1 ≤ i → i < (List.replicate b true).length + 1 →
          (tape (p_e + (i : ℤ))).1 =
            (if (List.replicate b true).getD (i - 1) false then SymKind.data1
              else SymKind.data0) := by
        intro i hi1 hi2
        have hile : i - 1 < b := by
          simp only [List.length_replicate] at hi2
          omega
        have hget : (List.replicate b true).getD (i - 1) false = true :=
          List.getD_replicate true hile
        rw [hget, if_pos rfl]
        have hencI := henc (i - 1) (by
          rw [famRest_single]
          simpa only [List.length_replicate] using hile)
        have hcell : p_e + (i : ℤ) = p_e + 1 + ((i - 1 : ℕ) : ℤ) := by omega
        rw [hcell, hencI]
        simp only [famRest_single, List.getElem_replicate, Sym.data1_fst]
      have hend : tape (p_e + 1 + (b : ℤ)) = Sym.sel ∨
          tape (p_e + 1 + (b : ℤ)) = Sym.nosel ∨
          (tape (p_e + 1 + (b : ℤ))).1 = SymKind.boundary := by
        refine Or.inr (Or.inr ?_)
        have h := congrArg (fun s : Sym => s.1) h1mark
        rw [show p_e + 1 + ((famRest [b]).length : ℤ) = p_e + 1 + (b : ℤ) from by
          simp only [famRest_single, List.length_replicate]] at h
        exact h
      have hR0' : (2 : ℤ) ^ (List.replicate b true).length - 1 ≤
          regVal tape ((p_e - 2).toNat) := by
        have h := hR0
        simp only [valSum_cons, valSum_nil, add_zero] at h
        simpa only [List.length_replicate] using h
      rcases segSrSel (List.replicate b true) p_e tape
        (by simpa only [List.length_replicate] using hb1)
        (by simpa only [List.length_replicate] using hbpe)
        (by intro j hj; exact List.getD_replicate true (by simpa only [List.length_replicate] using hj))
        hsel hbound0 hboundL hbwd0 hflag0 hbits hR0'
        (by simpa only [List.length_replicate] using hend)
        with ⟨π₀, cfg₀, hs₀, hcase₀, hC1, hC2, hex₀⟩
      have hbnd : (tape (p_e + ((List.replicate b true).length : ℤ) + 1)).1 = SymKind.boundary := by
        have h := congrArg (fun s : Sym => s.1) h1mark
        rw [show p_e + 1 + ((famRest [b]).length : ℤ) =
            p_e + ((List.replicate b true).length : ℤ) + 1 from by
          simp only [famRest_single, List.length_replicate]
          ring] at h
        simpa only [Sym.mk_fst] using h
      have hst22 : cfg₀.state = 22 := hC1 hbnd
      rcases hcase₀ with h4 | h22
      · exfalso
        rw [h4.1] at hst22
        exact absurd hst22 (by decide)
      · rcases h22 with ⟨hst, hhd, hlen, hagr, hbl, hfl, hkd, htk, hhk⟩
        have hhead : cfg₀.headPos = p_e + 1 + ((famRest [b]).length : ℤ) := by
          rw [hhd]
          rw [show p_e + ((List.replicate b true).length : ℤ) + 1 =
              p_e + 1 + ((famRest [b]).length : ℤ) from by
            simp only [famRest_single, List.length_replicate]
            ring]
        refine ⟨π₀, cfg₀, hs₀, hst, hhead, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show p_e + 1 + ((famRest [b]).length : ℤ) =
              p_e + ((List.replicate b true).length : ℤ) + 1 from by
            simp only [famRest_single, List.length_replicate]
            ring]
          rw [htk]
          rw [show p_e + ((List.replicate b true).length : ℤ) + 1 =
              p_e + 1 + ((famRest [b]).length : ℤ) from by
            simp only [famRest_single, List.length_replicate]
            ring]
          exact h1mark
        · exact hbl.trans hboundL
        · simpa [foldLenB_single] using hlen
        · -- EX：目标区归零（段精确 + 精确输入）
          have hv : valSum [b] = (2 : ℤ) ^ b - 1 := by
            simp only [valSum_cons, valSum_nil, add_zero]
          have hx : regVal cfg₀.tape ((p_e - 2).toNat) =
              regVal tape ((p_e - 2).toNat) - ((2 : ℤ) ^ b - 1) := by
            simpa only [List.length_replicate] using hex₀
          rw [hx, hR0ex]
          rw [hv]
          ring
        · -- HKD：目标区 kinds（末元素 22 支透传）
          intro i hi1 hi2
          exact hkd i hi1 (by omega)
        · -- HFL：目标区无标（末元素 22 支透传）
          intro i hi1 hi2
          exact hfl i hi1 (by omega)
        · -- HZ：清理区全 data0（末元素 22 支 hagr）
          intro i hi1 hi2
          have hi : (i - (p_e - 1)).toNat <
              (List.replicate ((List.replicate b true).length + 2) Sym.data0).length := by
            rw [List.length_replicate]
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          have hcell := hagr (i - (p_e - 1)).toNat hi
          have hsub : i = (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [hsub, hcell]
          simp only [List.getElem_replicate]
  | b :: c :: rest =>
      have hb1 : 1 ≤ b := hall1 b (by simp)
      have hbpe : (b : ℤ) ≤ p_e - 2 := hpos b (by simp)
      have hrest1 : ∀ b' ∈ (c :: rest), 1 ≤ b' := by
        intro b' hb'
        exact hall1 b' (by simp [hb'])
      have hrestpos : ∀ b' ∈ (c :: rest), (b' : ℤ) ≤ (p_e + (b : ℤ) + 1) - 2 := by
        intro b' hb'
        have h1 := hall1 b' (by simp [hb'])
        have h2 := hpos b' (by simp [hb'])
        omega
      have hsel' : tape (p_e + (b : ℤ) + 1) = Sym.sel := by
        have hget := henc b (by
          rw [famRest_cons_cons]
          simp only [List.length_append, List.length_cons, List.length_replicate]
          omega)
        rw [show p_e + 1 + (b : ℤ) = p_e + (b : ℤ) + 1 from by ring] at hget
        simp only [famRest_cons_cons] at hget
        rw [List.getElem_append_right (by
          simp only [List.length_replicate]
          omega)] at hget
        rw [show (Sym.sel :: famRest (c :: rest))[b - (List.replicate b Sym.data1).length] =
            (Sym.sel :: famRest (c :: rest))[0] from by
          simp only [List.length_replicate, Nat.sub_self]] at hget
        simp only [List.getElem_cons_zero] at hget
        exact hget
      have hselkind : (tape (p_e + ((List.replicate b true).length : ℤ) + 1)).1 = SymKind.sel := by
        rw [show p_e + ((List.replicate b true).length : ℤ) + 1 = p_e + (b : ℤ) + 1 from by
          simp only [List.length_replicate]]
        exact congrArg (fun s : Sym => s.1) hsel'
      have hend' : tape (p_e + (b : ℤ) + 1) = Sym.sel ∨
          tape (p_e + (b : ℤ) + 1) = Sym.nosel ∨
          (tape (p_e + (b : ℤ) + 1)).1 = SymKind.boundary :=
        Or.inl hsel'
      have hbits : ∀ i : ℕ, 1 ≤ i → i < (List.replicate b true).length + 1 →
          (tape (p_e + (i : ℤ))).1 =
            (if (List.replicate b true).getD (i - 1) false then SymKind.data1
              else SymKind.data0) := by
        intro i hi1 hi2
        have hile : i - 1 < b := by
          simp only [List.length_replicate] at hi2
          omega
        have hget : (List.replicate b true).getD (i - 1) false = true :=
          List.getD_replicate true hile
        rw [hget, if_pos rfl]
        have hencI := henc (i - 1) (by
          rw [famRest_cons_cons]
          simp only [List.length_append, List.length_cons, List.length_replicate]
          omega)
        simp only [famRest_cons_cons] at hencI
        rw [List.getElem_append_left (by
          simp only [List.length_replicate]
          omega)] at hencI
        have hcell : p_e + (i : ℤ) = p_e + 1 + ((i - 1 : ℕ) : ℤ) := by omega
        rw [hcell, hencI]
        simp only [List.getElem_replicate, Sym.data1_fst]
      have hR0' : (2 : ℤ) ^ (List.replicate b true).length - 1 ≤
          regVal tape ((p_e - 2).toNat) := by
        have h := hR0
        simp only [valSum_cons] at h
        have hvrest : 0 ≤ valSum (c :: rest) := by
          have hmap : ∀ x ∈ (c :: rest).map (fun b => (2 : ℤ) ^ b - 1), 0 ≤ x := by
            intro x hx
            rcases List.mem_map.mp hx with ⟨b', hb'mem, rfl⟩
            have : (2 : ℤ) ^ b' ≥ 1 := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
            linarith
          exact List.sum_nonneg hmap
        simp only [valSum_cons] at hvrest
        have h2 : (2 : ℤ) ^ b - 1 ≤ regVal tape ((p_e - 2).toNat) := by linarith
        simpa only [List.length_replicate] using h2
      rcases segSrSel (List.replicate b true) p_e tape
        (by simpa only [List.length_replicate] using hb1)
        (by simpa only [List.length_replicate] using hbpe)
        (by intro j hj; exact List.getD_replicate true (by simpa only [List.length_replicate] using hj))
        hsel hbound0 hboundL hbwd0 hflag0 hbits hR0'
        (by
          rw [show p_e + 1 + ((List.replicate b true).length : ℤ) = p_e + (b : ℤ) + 1 from by
            simp only [List.length_replicate]
            ring]
          exact hend')
        with ⟨π₀, cfg₀, hs₀, hcase₀, hC1, hC2, hex₀⟩
      have hst4 : cfg₀.state = 4 := hC2 (Or.inl hselkind)
      rcases hcase₀ with h4 | h22
      · rcases h4 with ⟨hst, hhd, hlen, hstamp, hagr, hbl, hnet, hfl, hkd, htk, hhk⟩
        have hsel₂ : cfg₀.tape (p_e + (b : ℤ) + 1) = Sym.sel := by
          rw [show p_e + (b : ℤ) + 1 = p_e + ((List.replicate b true).length : ℤ) + 1 from by
            simp only [List.length_replicate]]
          rw [htk]
          rw [show p_e + ((List.replicate b true).length : ℤ) + 1 = p_e + (b : ℤ) + 1 from by
            simp only [List.length_replicate]]
          exact hsel'
        have hbound0₂ : cfg₀.tape (p_e + (b : ℤ) + 1 - 1) = Sym.boundary := by
          rw [show p_e + (b : ℤ) + 1 - 1 = p_e + (b : ℤ) from by ring]
          simpa only [List.length_replicate] using hstamp
        have hbwd0₂ : ∀ i : ℤ, 1 ≤ i → i ≤ (p_e + (b : ℤ) + 1) - 2 →
            (cfg₀.tape i).1 = SymKind.data0 ∨ (cfg₀.tape i).1 = SymKind.data1 := by
          intro i hi1 hi2
          exact hkd i hi1 (by
            rw [show (List.replicate b true).length = b from by simp only [List.length_replicate]]
            omega)
        have hflag0₂ : ∀ i : ℤ, 1 ≤ i → i ≤ (p_e + (b : ℤ) + 1) - 2 →
            (cfg₀.tape i).2 = false := by
          intro i hi1 hi2
          exact hfl i hi1 (by
            rw [show (List.replicate b true).length = b from by simp only [List.length_replicate]]
            omega)
        have henc₂ : tapeAgrees cfg₀.tape (p_e + (b : ℤ) + 1 + 1) (famRest (c :: rest)) := by
          intro i hi
          have hgt : p_e + ((List.replicate b true).length : ℤ) + 1 <
              p_e + (b : ℤ) + 1 + 1 + (i : ℤ) := by
            rw [show (List.replicate b true).length = b from by simp only [List.length_replicate]]
            omega
          rw [hhk _ hgt]
          have hencI := henc (b + 1 + i) (by
            rw [famRest_cons_cons]
            simp only [List.length_append, List.length_cons, List.length_replicate]
            omega)
          simp only [famRest_cons_cons] at hencI
          rw [List.getElem_append_right (by
            simp only [List.length_replicate]
            omega)] at hencI
          simp only [List.length_replicate,
            show b + 1 + i - b = i + 1 from by omega] at hencI
          simp only [List.getElem_cons_succ] at hencI
          rw [show p_e + 1 + ((b + 1 + i : ℕ) : ℤ) = p_e + (b : ℤ) + 1 + 1 + (i : ℤ) from by
            push_cast
            ring] at hencI
          exact hencI
        have h1mark₂ : cfg₀.tape (p_e + (b : ℤ) + 1 + 1 + ((famRest (c :: rest)).length : ℤ)) =
            Sym.mk SymKind.boundary true := by
          have hgt : p_e + ((List.replicate b true).length : ℤ) + 1 <
              p_e + (b : ℤ) + 1 + 1 + ((famRest (c :: rest)).length : ℤ) := by
            rw [show (List.replicate b true).length = b from by simp only [List.length_replicate]]
            omega
          rw [hhk _ hgt]
          rw [show p_e + (b : ℤ) + 1 + 1 + ((famRest (c :: rest)).length : ℤ) =
              p_e + 1 + ((famRest (b :: c :: rest)).length : ℤ) from by
            simp only [famRest_length_cons_cons]
            push_cast
            ring]
          exact h1mark
        have hR0₂ : valSum (c :: rest) ≤ regVal cfg₀.tape (((p_e + (b : ℤ) + 1) - 2).toNat) := by
          have hagr' : tapeAgrees cfg₀.tape (1 + (((p_e - 2).toNat) : ℤ))
              (List.replicate (b + 1) Sym.data0) := by
            have heq : (1 : ℤ) + (((p_e - 2).toNat) : ℤ) = p_e - 1 := by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega
            rw [heq]
            simpa only [List.length_replicate] using hagr
          have hext : regVal cfg₀.tape (((p_e - 2).toNat) + (b + 1)) =
              regVal cfg₀.tape ((p_e - 2).toNat) :=
            regVal_zero_ext cfg₀.tape 1 ((p_e - 2).toNat) (b + 1) hagr'
          have hm' : (((p_e + (b : ℤ) + 1) - 2).toNat) = ((p_e - 2).toNat) + (b + 1) := by
            have hc1 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            have hc2 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e + (b : ℤ) + 1 - 2 by omega)
            omega
          rw [hm', hext]
          have h := hR0
          simp only [valSum_cons] at h
          have hnet' : regVal cfg₀.tape ((p_e - 2).toNat) ≥
              regVal tape ((p_e - 2).toNat) - ((2 : ℤ) ^ b - 1) := by
            simpa only [List.length_replicate] using hnet
          rw [valSum_cons]
          linarith
        have hidx0 : ((p_e + (b : ℤ) + 1 - 2).toNat) = ((p_e - 2).toNat) + (b + 1) := by
          have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
          have hc2 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e + (b : ℤ) + 1 - 2 by omega)
          omega
        have hv : valSum (b :: c :: rest) = ((2 : ℤ) ^ b - 1) + valSum (c :: rest) := by
          simp only [valSum_cons]
        have hx : regVal cfg₀.tape ((p_e - 2).toNat) =
            regVal tape ((p_e - 2).toNat) - ((2 : ℤ) ^ b - 1) := by
          simpa only [List.length_replicate] using hex₀
        have hb0 : regVal cfg₀.tape ((p_e + (b : ℤ) + 1 - 2).toNat) =
            regVal cfg₀.tape ((p_e - 2).toNat) := by
          rw [hidx0]
          simp only [regVal]
          exact regValA_high_zero cfg₀.tape 1 ((p_e - 2).toNat) (b + 1) 0 (by
            intro j hj1 hj2
            have hi : j - ((p_e - 2).toNat) <
                (List.replicate ((List.replicate b true).length + 1) Sym.data0).length := by
              simp only [List.length_replicate]
              omega
            have hcell := hagr (j - ((p_e - 2).toNat)) hi
            have hsub : 1 + (j : ℤ) = (p_e - 1) + ((j - ((p_e - 2).toNat) : ℕ) : ℤ) := by
              have hcm := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega
            rw [hsub, hcell]
            simp only [List.getElem_replicate, Sym.data0, Sym.mk_fst]
            exact fun h => SymKind.noConfusion h)
        have hR0ex₂ : regVal cfg₀.tape ((p_e + (b : ℤ) + 1 - 2).toNat) = valSum (c :: rest) := by
          rw [hb0, hx, hR0ex, hv]
          ring
        rcases segSrFold (c :: rest) (p_e + (b : ℤ) + 1) cfg₀.tape (by simp)
          hrest1 hrestpos
          hsel₂ hbound0₂ (hbl.trans hboundL) hbwd0₂ hflag0₂ henc₂ h1mark₂ hR0₂ hR0ex₂
          with ⟨π₂, cfg₂, hs₂, hst₂, hhd₂, hmk₂, hbl₂, hlen₂, hex₂, hkd₂, hfl₂, hz₂⟩
        have e₀ : cfg₀ = SymConfig.mk 4 cfg₀.tape (p_e + (b : ℤ) + 1) := by
          rw [show cfg₀ = SymConfig.mk cfg₀.state cfg₀.tape cfg₀.headPos from rfl]
          rw [hst, hhd]
          rw [show p_e + ((List.replicate b true).length : ℤ) + 1 = p_e + (b : ℤ) + 1 from by
            simp only [List.length_replicate]]
        have hcat : SymSteps VerifierSym.transition cfg₀ π₂ cfg₂ := by
          rw [e₀]
          exact hs₂
        have hall : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) (π₀ ++ π₂) cfg₂ :=
          symSteps_append_concat π₀ π₂ hs₀ hcat
        have hshape : p_e + (b : ℤ) + 1 + 1 + ((famRest (c :: rest)).length : ℤ) =
            p_e + 1 + ((famRest (b :: c :: rest)).length : ℤ) := by
          rw [famRest_length_cons_cons]
          push_cast
          ring
        refine ⟨π₀ ++ π₂, cfg₂, hall, hst₂, (by rw [← hshape]; exact hhd₂),
          (by rw [← hshape]; exact hmk₂), hbl₂, ?_, ?_, ?_, ?_, ?_⟩
        have hT : ((famRest (b :: c :: rest)).length : ℤ) =
            (b : ℤ) + 1 + ((famRest (c :: rest)).length : ℤ) := by
          rw [famRest_length_cons_cons]
          push_cast
          ring
        have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
        have hT2 : (0 : ℤ) ≤ ((famRest (c :: rest)).length : ℤ) := by positivity
        have hpe : 3 ≤ p_e := by omega
        have hn0 : (0 : ℤ) ≤ ((c :: rest).length : ℤ) := by positivity
        have hlen1' : (π₀.length : ℤ) ≤
            (b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13) := by
          simpa only [List.length_replicate] using hlen
        have hs2' : (π₂.length : ℤ) ≤ foldLenB (c :: rest) (p_e + (b : ℤ) + 1) := hlen₂
        have hcomb : (π₀.length : ℤ) + (π₂.length : ℤ) ≤
            ((b : ℤ) * (2 * (b : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (b : ℤ) + 13)) +
              foldLenB (c :: rest) (p_e + (b : ℤ) + 1) := by
          linarith [hlen1', hs2']
        rw [List.length_append]
        push_cast
        rw [foldLenB_cons_cons]
        linarith [hcomb]
        · -- EX：目标区归零（桥 + 递归归零 + 区间单调）
          have hY2 : regVal cfg₂.tape ((p_e + (b : ℤ) + 1 - 2).toNat) = 0 := hex₂
          have hmono : regVal cfg₂.tape ((p_e - 2).toNat) ≤
              regVal cfg₂.tape (((p_e - 2).toNat) + (b + 1)) := by
            simp only [regVal]
            exact regValA_le_ext cfg₂.tape 1 ((p_e - 2).toNat) (b + 1) 0
          rw [hidx0] at hY2
          have hnn : (0 : ℤ) ≤ regVal cfg₂.tape ((p_e - 2).toNat) := by
            simp only [regVal]
            exact regValA_nonneg cfg₂.tape 1 ((p_e - 2).toNat) 0 (by norm_num)
          linarith
        · -- HKD：目标区 kinds（递归透传）
          intro i hi1 hi2
          exact hkd₂ i hi1 (by omega)
        · -- HFL：目标区无标（递归透传）
          intro i hi1 hi2
          exact hfl₂ i hi1 (by omega)
        · -- HZ：清理区全 data0（元素1 段区经递归谓词全零 + 递归区 IH）
          intro i hi1 hi2
          by_cases hc : i ≤ p_e + (b : ℤ) - 1
          · -- [p_e−1, p_e+b−1]：递归寄存器区全零（reg0 + kinds + 无标 ⟹ all_d0）
            have hk2 : ∀ j : ℤ, 1 ≤ j → j ≤ (((p_e + (b : ℤ) + 1 - 2).toNat) : ℤ) →
                (cfg₂.tape j).1 = SymKind.data0 ∨ (cfg₂.tape j).1 = SymKind.data1 := by
              intro j hj1 hj2
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e + (b : ℤ) + 1 - 2 by omega)
              rw [hcast] at hj2
              exact hkd₂ j hj1 hj2
            have hfl2' : ∀ j : ℤ, 1 ≤ j → j ≤ (((p_e + (b : ℤ) + 1 - 2).toNat) : ℤ) →
                (cfg₂.tape j).2 = false := by
              intro j hj1 hj2
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e + (b : ℤ) + 1 - 2 by omega)
              rw [hcast] at hj2
              exact hfl₂ j hj1 hj2
            have hall0 := all_d0_of_regVal_zero cfg₂.tape ((p_e + (b : ℤ) + 1 - 2).toNat)
              hk2 hfl2' hex₂
            have hcast2 := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e + (b : ℤ) + 1 - 2 by omega)
            exact hall0 i (by omega) (by rw [hcast2]; omega)
          · push Not at hc
            have hTb : ((famRest (b :: c :: rest)).length : ℤ) =
                (b : ℤ) + 1 + ((famRest (c :: rest)).length : ℤ) := by
              rw [famRest_length_cons_cons]
              push_cast
              ring
            exact hz₂ i (by omega) (by omega)
      · exfalso
        rw [h22.1] at hst4
        exact absurd hst4 (by decide)

/-- [④ 收口 · 判定前件] 折叠输出（reg0 + kinds + hz）⟹ R12 `segS3` 的三件前件。 -/
lemma judge_pre_of_fold (bs : List ℕ) (p_e : ℤ) (cfg' : SymConfig) (T : ℤ)
    (hp2 : 0 ≤ p_e - 2)
    (hT : T = ((famRest bs).length : ℤ))
    (hmark : cfg'.tape (p_e + 1 + T) = Sym.mk SymKind.boundary true)
    (hbl : cfg'.tape 0 = Sym.boundary)
    (hreg0 : regVal cfg'.tape ((p_e - 2).toNat) = 0)
    (hkd : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1)
    (hfl : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).2 = false)
    (hz : ∀ i : ℤ, p_e - 1 ≤ i → i ≤ p_e + T → cfg'.tape i = Sym.data0) :
    (∀ i : ℤ, 0 < i → i ≤ p_e + T → cfg'.tape i = Sym.data0) ∧
    cfg'.tape 0 = Sym.boundary ∧
    cfg'.tape (0 + (p_e + T) + 1) = Sym.mk SymKind.boundary true := by
  refine ⟨?_, hbl, ?_⟩
  · intro i hi1 hi2
    by_cases hc : i ≤ p_e - 2
    · have hcast : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 := Int.toNat_of_nonneg hp2
      exact all_d0_of_regVal_zero cfg'.tape ((p_e - 2).toNat) (by
        intro j hj1 hj2
        rw [hcast] at hj2
        exact hkd j hj1 hj2) (by
        intro j hj1 hj2
        rw [hcast] at hj2
        exact hfl j hj1 hj2) hreg0 i (by omega) (by rw [hcast]; exact hc)
    · push Not at hc
      exact hz i (by omega) hi2
  · rw [show (0 : ℤ) + (p_e + T) + 1 = p_e + 1 + T from by ring]
    exact hmark


/-! ========== G1 · 一般 sel 块：valFrom 工具 ========== -/

/-- [一般段 · 值函数] LSB 在前、权重倍进：`valFrom [b₀,b₁,…] w = (b₀ ? w : 0) + valFrom [b₁,…] (2w)`。 -/
def valFrom : List Bool → ℤ → ℤ
  | [], _ => 0
  | b :: t, w => (if b then w else 0) + valFrom t (2 * w)

/-- [值 · cons 展开] -/
lemma valFrom_cons (b : Bool) (t : List Bool) (w : ℤ) :
    valFrom (b :: t) w = (if b then w else 0) + valFrom t (2 * w) := rfl

/-- [值 · 单元素] -/
lemma valFrom_single (b : Bool) (w : ℤ) : valFrom [b] w = (if b then w else 0) := by
  simp [valFrom]

/-- [值 · 非负] 权重非负 ⟹ 值非负。 -/
lemma valFrom_nonneg (l : List Bool) : ∀ (w : ℤ), 0 ≤ w → 0 ≤ valFrom l w := by
  induction l with
  | nil => intro w _; simp [valFrom]
  | cons b t ih =>
      intro w hw
      rw [valFrom_cons]
      have h1 : (0 : ℤ) ≤ (if b then w else 0) := by split <;> omega
      have h2 : (0 : ℤ) ≤ valFrom t (2 * w) := ih (2 * w) (by omega)
      omega

/-- [值 · 头部下界] 首位为真且权重非负 ⟹ `w ≤ valFrom (true :: t) w`。 -/
lemma valFrom_head_true_le (t : List Bool) (w : ℤ) (hw : 0 ≤ w) :
    w ≤ valFrom (true :: t) w := by
  rw [valFrom_cons]
  simp only [if_true]
  have h : 0 ≤ valFrom t (2 * w) := valFrom_nonneg t (2 * w) (by omega)
  omega

/-- [值 · drop 分裂] `drop` 的 cons 形（getD 默认 false）。 -/
lemma drop_eq_getD_cons (l : List Bool) (k : ℕ) (hk : k < l.length) :
    l.drop k = l.getD k false :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
      cases k with
      | zero => rfl
      | succ k' =>
          simp only [List.drop_succ_cons]
          exact ih k' (by simpa using hk)

/-- [值 · drop 分裂（主）] `valFrom (drop (k−1) ebits) w = (bit_k ? w : 0) + valFrom (drop k ebits) (2w)`。 -/
lemma valFrom_drop_succ (ebits : List Bool) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ ebits.length)
    (w : ℤ) :
    valFrom (ebits.drop (k - 1)) w =
      (if ebits.getD (k - 1) false then w else 0) + valFrom (ebits.drop k) (2 * w) := by
  conv_lhs =>
    rw [drop_eq_getD_cons ebits (k - 1) (by omega)]
    rw [show k - 1 + 1 = k from by omega]
  rw [valFrom_cons]

/-! ========== G1 · 一般 sel 块：轮串联按位两版 ========== -/

set_option maxHeartbeats 900000 in
/-- [轮串联 · 中轮 · 位1版] 同 `round_chain`，位1前提 `hb` 显式；结论只出位1/借位两结果（D1∨D2）。 -/
lemma round_chain_t (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k < ebits.length)
    (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hb : ebits.getD (k - 1) false = true)
    (hmar0 : tape p_e = Sym.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbwdK : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbitK : ∀ i : ℕ, k ≤ i → i < ebits.length + 1 →
      (tape (p_e + (i : ℤ))).1 = (if ebits.getD (i - 1) false then SymKind.data1 else
          SymKind.data0))
    (hborK : (tape (k : ℤ)).1 = SymKind.data0 →
      ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1)
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        cfg'.state = 5 ∧ cfg'.headPos = p_e + (k : ℤ) + 1 ∧
        (π.length : ℤ) = 2 * (k : ℤ) + 2 * p_e + 2 + (if ebits.getD (k - 1) false then 1 else 0) ∧
        cfg'.tape p_e = Sym.data0 ∧
        cfg'.tape (p_e - 1) = Sym.boundary ∧
        cfg'.tape 0 = Sym.boundary ∧
        (∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) → cfg'.tape i = Sym.consumed) ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) → (cfg'.tape i).2 = true) ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).2 = false) ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
          (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
        (∀ i : ℕ, k + 1 ≤ i → i < ebits.length + 1 →
          (cfg'.tape (p_e + (i : ℤ))).1 =
            (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0)) ∧
        (((tape (k : ℤ)).1 = SymKind.data1 ∧ (cfg'.tape (k : ℤ)).1 = SymKind.data0 ∧
            (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
            (∀ i : ℤ, (k : ℤ) < i → i ≤ p_e - 2 → cfg'.tape i = tape i))
          ∨ ((tape (k : ℤ)).1 = SymKind.data0 ∧ (cfg'.tape (k : ℤ)).1 = SymKind.data1 ∧
            (∀ i : ℤ, i < (k : ℤ) → cfg'.tape i = tape i) ∧
            ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
              (tape j).1 = SymKind.data1 ∧
              (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → ((tape i).1 = SymKind.data0 ∧
                (cfg'.tape i).1 = SymKind.data1)) ∧
              (cfg'.tape j).1 = SymKind.data0 ∧
              (∀ i : ℤ, j < i → i ≤ p_e - 2 → cfg'.tape i = tape i))) ∧
        (∀ i : ℤ, p_e + (k : ℤ) < i → cfg'.tape i = tape i) := by
  have hp_e : 3 ≤ p_e := by omega
  have hkpe : (k : ℤ) ≤ p_e - 2 := by omega
  have hbitk : (tape (p_e + (k : ℤ))).1 =
      (if ebits.getD (k - 1) false then SymKind.data1 else SymKind.data0) :=
    hbitK k le_rfl (by omega)
  have hbit1 : (tape (p_e + (k : ℤ))).1 = SymKind.data1 := by rw [hbitk, if_pos hb]
  rcases round_to13 p_e k tape hp_e hk1 hkpe hbit1
    (by have h := congrArg (fun s : Sym => s.1) hmar0; simpa [Sym.data0] using h)
    hbound0 hboundL htrailK hbwdK hmarks hflagFree hborK
    with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
      hsplitr⟩
  have hqplus : cfgr.tape (p_e + (k : ℤ) + 1) = tape (p_e + (k : ℤ) + 1) :=
    hkeepWr _ (Or.inr (Or.inr (by omega)))
  have hkindR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 =
      (if ebits.getD k false then SymKind.data1 else SymKind.data0) := by
    rw [hqplus]
    have h2 := hbitK (k + 1) (by omega) (by omega)
    rw [show p_e + ((k + 1 : ℕ) : ℤ) = p_e + (k : ℤ) + 1 from by push_cast; ring] at h2
    exact h2
  have hconsE : ∀ i : ℤ, p_e + 2 ≤ i → i ≤ p_e + (k : ℤ) → cfgr.tape i = Sym.consumed := by
    intro i h1 h2
    by_cases hq : i = p_e + (k : ℤ)
    · rw [hq]; exact hburnr
    · rw [hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact htrailK i (by omega) (by omega)
  have hexit5 : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary := by
    by_cases hb2 : ebits.getD k false
    · rw [hkindR, if_pos hb2]
      exact Or.inr (Or.inl rfl)
    · rw [hkindR, if_neg hb2]
      exact Or.inl rfl
  rcases exit13 p_e k cfgr.tape hk1 hconsE hexit5 with ⟨πe, cfge, hse, hlene, htpe, hdise⟩
  have hkindNextR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 := by
    by_cases hb2 : ebits.getD k false
    · rw [hkindR, if_pos hb2]
      exact Or.inr rfl
    · rw [hkindR, if_neg hb2]
      exact Or.inl rfl
  have hkindNext' : (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.sel ∧
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.nosel ∧
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.boundary := by
    rcases hkindNextR with h | h
    · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
  have hst5 : cfge.state = 5 ∧ cfge.headPos = p_e + (k : ℤ) + 1 := by
    rcases hdise with h | h
    · exact ⟨h.1, h.2.1⟩
    · exfalso
      rcases h.2.2 with hk | hk | hk
      · exact absurd hk hkindNext'.1
      · exact absurd hk hkindNext'.2.1
      · exact absurd hk hkindNext'.2.2
  have ere : cfgr = SymConfig.mk 13 cfgr.tape (p_e + 2) := by
    rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
    rw [hstr, hhdr]
  refine ⟨πr ++ πe, cfge, symSteps_append_concat πr πe hsr (by rw [ere]; exact hse),
    hst5.1, hst5.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]; push_cast; rw [hlenr, hlene, if_pos hb]
    omega
  · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, le_rfl⟩)]
    exact hmar0
  · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, by omega⟩)]
    exact hbound0
  · rw [htpe, hkeepLr 0 (by omega)]
    exact hboundL
  · intro i h1 h2
    by_cases hq : i = p_e + (k : ℤ)
    · rw [htpe, hq]; exact hburnr
    · rw [htpe, hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact htrailK i (by omega) (by omega)
  · intro i h1 h2
    by_cases hk : i = (k : ℤ)
    · rw [htpe, hk]; exact hmK2
    · rw [htpe, hkeepLr i (by omega)]
      exact hmarks i (by omega) (by omega)
  · intro i h1 h2
    rw [htpe]
    exact (hmidr i (by omega) (by omega)).2
  · intro i h1 h2
    rw [htpe]
    by_cases hk : i = (k : ℤ)
    · rw [hk]; exact hmKk
    · by_cases hik : i < (k : ℤ)
      · rw [hkeepLr i hik]
        exact hbwdK i (by omega) h2
      · exact (hmidr i (by omega) (by omega)).1
  · intro i h1 h2
    rw [htpe, hkeepWr (p_e + (i : ℤ)) (Or.inr (Or.inr (by omega)))]
    exact hbitK i (by omega) h2
  · -- 分支共轭：转储 round_to13 split（exit13 不动 tape）
    rcases hsplitr with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw, hj0, hup⟩
    · left
      exact ⟨h1, (by rw [htpe]; exact h2), (by intro i hi; rw [htpe]; exact h3 i hi),
        (by intro i hi1 hi2; rw [htpe]; exact h4 i hi1 hi2)⟩
    · right
      exact ⟨h1, (by rw [htpe]; exact h2), (by intro i hi; rw [htpe]; exact h3 i hi), j, hj1, hj2,
        hdj,
        (by intro i hi1 hi2; exact ⟨(hw i hi1 hi2).1, by rw [htpe]; exact (hw i hi1 hi2).2⟩),
        (by rw [htpe]; exact hj0),
        (by intro i hi1 hi2; rw [htpe]; exact hup i hi1 hi2)⟩
  · intro i hi
    rw [htpe]
    exact hkeepWr i (Or.inr (Or.inr (by omega)))

set_option maxHeartbeats 900000 in
/-- [轮串联 · 中轮 · 位0版] 同 `round_chain`，位0前提 `hb` 显式；结论只出位0结果（D3：全区位保持）。 -/
lemma round_chain_f (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k < ebits.length)
    (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hb : ebits.getD (k - 1) false = false)
    (hmar0 : tape p_e = Sym.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbwdK : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbitK : ∀ i : ℕ, k ≤ i → i < ebits.length + 1 →
      (tape (p_e + (i : ℤ))).1 = (if ebits.getD (i - 1) false then SymKind.data1 else
          SymKind.data0))
    : ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        cfg'.state = 5 ∧ cfg'.headPos = p_e + (k : ℤ) + 1 ∧
        (π.length : ℤ) = 2 * (k : ℤ) + 2 * p_e + 2 + (if ebits.getD (k - 1) false then 1 else 0) ∧
        cfg'.tape p_e = Sym.data0 ∧
        cfg'.tape (p_e - 1) = Sym.boundary ∧
        cfg'.tape 0 = Sym.boundary ∧
        (∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) → cfg'.tape i = Sym.consumed) ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) → (cfg'.tape i).2 = true) ∧
        (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).2 = false) ∧
        (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
          (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
        (∀ i : ℕ, k + 1 ≤ i → i < ebits.length + 1 →
          (cfg'.tape (p_e + (i : ℤ))).1 =
            (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0)) ∧
        ((∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (cfg'.tape i).1 = (tape i).1) ∧
            ebits.getD (k - 1) false = false) ∧
        (∀ i : ℤ, p_e + (k : ℤ) < i → cfg'.tape i = tape i) := by
  have hp_e : 3 ≤ p_e := by omega
  have hkpe : (k : ℤ) ≤ p_e - 2 := by omega
  have hbitk : (tape (p_e + (k : ℤ))).1 =
      (if ebits.getD (k - 1) false then SymKind.data1 else SymKind.data0) :=
    hbitK k le_rfl (by omega)
  have hbT : ¬ (ebits.getD (k - 1) false = true) := by rw [hb]; decide
  have hbit0 : (tape (p_e + (k : ℤ))).1 = SymKind.data0 := by rw [hbitk, if_neg hbT]
  rcases round_d0 p_e k tape hp_e hk1 hkpe hbit0
    (by have h := congrArg (fun s : Sym => s.1) hmar0; simpa [Sym.data0] using h)
    hbound0 hboundL htrailK hbwdK hmarks hflagFree
    with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
      hkrelr⟩
  have hqplus : cfgr.tape (p_e + (k : ℤ) + 1) = tape (p_e + (k : ℤ) + 1) :=
    hkeepWr _ (Or.inr (Or.inr (by omega)))
  have hkindR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 =
      (if ebits.getD k false then SymKind.data1 else SymKind.data0) := by
    rw [hqplus]
    have h2 := hbitK (k + 1) (by omega) (by omega)
    rw [show p_e + ((k + 1 : ℕ) : ℤ) = p_e + (k : ℤ) + 1 from by push_cast; ring] at h2
    exact h2
  have hconsE : ∀ i : ℤ, p_e + 2 ≤ i → i ≤ p_e + (k : ℤ) → cfgr.tape i = Sym.consumed := by
    intro i h1 h2
    by_cases hq : i = p_e + (k : ℤ)
    · rw [hq]; exact hburnr
    · rw [hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact htrailK i (by omega) (by omega)
  have hexit5 : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.sel ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.nosel ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.boundary := by
    by_cases hb2 : ebits.getD k false
    · rw [hkindR, if_pos hb2]
      exact Or.inr (Or.inl rfl)
    · rw [hkindR, if_neg hb2]
      exact Or.inl rfl
  rcases exit13 p_e k cfgr.tape hk1 hconsE hexit5 with ⟨πe, cfge, hse, hlene, htpe, hdise⟩
  have hkindNextR : (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data0 ∨
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 = SymKind.data1 := by
    by_cases hb2 : ebits.getD k false
    · rw [hkindR, if_pos hb2]
      exact Or.inr rfl
    · rw [hkindR, if_neg hb2]
      exact Or.inl rfl
  have hkindNext' : (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.sel ∧
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.nosel ∧
      (cfgr.tape (p_e + (k : ℤ) + 1)).1 ≠ SymKind.boundary := by
    rcases hkindNextR with h | h
    · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
  have hst5 : cfge.state = 5 ∧ cfge.headPos = p_e + (k : ℤ) + 1 := by
    rcases hdise with h | h
    · exact ⟨h.1, h.2.1⟩
    · exfalso
      rcases h.2.2 with hk | hk | hk
      · exact absurd hk hkindNext'.1
      · exact absurd hk hkindNext'.2.1
      · exact absurd hk hkindNext'.2.2
  have ere : cfgr = SymConfig.mk 13 cfgr.tape (p_e + 2) := by
    rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
    rw [hstr, hhdr]
  refine ⟨πr ++ πe, cfge, symSteps_append_concat πr πe hsr (by rw [ere]; exact hse),
    hst5.1, hst5.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]; push_cast; rw [hlenr, hlene, if_neg hbT]
    omega
  · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, le_rfl⟩)]
    exact hmar0
  · rw [htpe, hkeepWr _ (Or.inl ⟨by omega, by omega⟩)]
    exact hbound0
  · rw [htpe, hkeepLr 0 (by omega)]
    exact hboundL
  · intro i h1 h2
    by_cases hq : i = p_e + (k : ℤ)
    · rw [htpe, hq]; exact hburnr
    · rw [htpe, hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact htrailK i (by omega) (by omega)
  · intro i h1 h2
    by_cases hk : i = (k : ℤ)
    · rw [htpe, hk]; exact hmK2
    · rw [htpe, hkeepLr i (by omega)]
      exact hmarks i (by omega) (by omega)
  · intro i h1 h2
    rw [htpe, hmidr i (by omega) (by omega)]
    exact hflagFree i (by omega) h2
  · intro i h1 h2
    rw [htpe]
    by_cases hk : i = (k : ℤ)
    · rw [hk]; exact hmKk
    · by_cases hik : i < (k : ℤ)
      · rw [hkeepLr i hik]
        exact hbwdK i (by omega) h2
      · rw [hmidr i (by omega) (by omega)]
        exact hbwdK i (by omega) h2
  · intro i h1 h2
    rw [htpe, hkeepWr (p_e + (i : ℤ)) (Or.inr (Or.inr (by omega)))]
    exact hbitK i (by omega) h2
  · -- 分支共轭：位0轮 — 全区位保持（12 星写 mk kind true）+ 位标 getD = false
    refine ⟨?_, hb⟩
    intro i h1 h2
    rw [htpe]
    by_cases hk : i < (k : ℤ)
    · rw [hkeepLr i hk]
    · by_cases hk2 : i = (k : ℤ)
      · rw [hk2]; exact hkrelr
      · rw [hmidr i (by omega) h2]
  · intro i hi
    rw [htpe]
    exact hkeepWr i (Or.inr (Or.inr (by omega)))

/-! ========== G1 · 一般 sel 块：末轮链一般版（去 hall） ========== -/

set_option maxHeartbeats 900000 in
/-- [轮串联 · 末轮 · 一般版] 同 `last_chain`，去 all-1 前提；末轮结果按位自然分支；
    净值尾项改为条件精确式 `− (bit_n ? 2^{n−1} : 0)`。 -/
lemma last_chain_gen (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hn1 : 1 ≤ ebits.length)
    (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hmar0 : tape p_e = Sym.data0)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (htrailK : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → tape i = Sym.consumed)
    (hmarks : ∀ i : ℤ, 1 ≤ i → i ≤ (ebits.length : ℤ) - 1 → (tape i).2 = true)
    (hflagFree : ∀ i : ℤ, (ebits.length : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbwdK : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hbitN : (tape (p_e + (ebits.length : ℤ))).1 =
      (if ebits.getD (ebits.length - 1) false then SymKind.data1 else SymKind.data0))
    (hborK : ebits.getD (ebits.length - 1) false = true →
      (tape (ebits.length : ℤ)).1 = SymKind.data0 →
      ∃ j : ℤ, (ebits.length : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
        (∀ i : ℤ, (ebits.length : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
        (tape j).1 = SymKind.data1)
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary)
    : ∃ π cfg', SymSteps VerifierSym.transition
          (SymConfig.mk 5 tape (p_e + (ebits.length : ℤ))) π cfg' ∧
        ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) = 2 * p_e + 4 * (ebits.length : ℤ) +
              2 * (((p_e - 2).toNat) : ℤ) + 11 +
              (if ebits.getD (ebits.length - 1) false then 1 else 0) ∧
            cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (regVal cfg'.tape ((p_e - 2).toNat) ≥
              regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1)) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
              tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
          (cfg'.state = 22 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) = 2 * p_e + 4 * (ebits.length : ℤ) +
              2 * (((p_e - 2).toNat) : ℤ) + 10 +
              (if ebits.getD (ebits.length - 1) false then 1 else 0) ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 2) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
              tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) ∧
        (regVal cfg'.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            (if ebits.getD (ebits.length - 1) false then (2 : ℤ) ^ (ebits.length - 1) else 0)) := by
  have hp_e : 3 ≤ p_e := by omega
  have hidx : p_e + (ebits.length : ℤ) + 1 = p_e + 1 + (ebits.length : ℤ) := by omega
  have hmarkerK : (tape p_e).1 = SymKind.data0 := by
    have h := congrArg (fun s : Sym => s.1) hmar0
    simpa [Sym.data0] using h
  obtain ⟨πr, cfgr, hsr, hstr, hhdr, hlenForm, hkeepLr, hkeepWr, hburnr, hmK2, hmKk,
    hmidFlag, hmidKind, hbl0, hnet0, hex0⟩ :
      ∃ (πr : List SymStep) (cfgr : SymConfig),
        SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (ebits.length : ℤ))) πr cfgr ∧
        cfgr.state = 13 ∧ cfgr.headPos = p_e + 2 ∧
        (πr.length : ℤ) = (ebits.length : ℤ) + 2 * p_e + 2 +
          (if ebits.getD (ebits.length - 1) false then 1 else 0) ∧
        (∀ i : ℤ, i < (ebits.length : ℤ) → cfgr.tape i = tape i) ∧
        (∀ i : ℤ, ((p_e - 1 ≤ i ∧ i ≤ p_e) ∨ (p_e + 1 ≤ i ∧ i < p_e + (ebits.length : ℤ)) ∨
            p_e + (ebits.length : ℤ) < i) → cfgr.tape i = tape i) ∧
        cfgr.tape (p_e + (ebits.length : ℤ)) = Sym.consumed ∧
        (cfgr.tape (ebits.length : ℤ)).2 = true ∧
        ((cfgr.tape (ebits.length : ℤ)).1 = SymKind.data0 ∨
          (cfgr.tape (ebits.length : ℤ)).1 = SymKind.data1) ∧
        (∀ i : ℤ, (ebits.length : ℤ) < i → i ≤ p_e - 2 → (cfgr.tape i).2 = false) ∧
        (∀ i : ℤ, (ebits.length : ℤ) < i → i ≤ p_e - 2 →
          (cfgr.tape i).1 = SymKind.data0 ∨ (cfgr.tape i).1 = SymKind.data1) ∧
        (cfgr.tape 0 = tape 0) ∧
        (regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1)) ∧
        (regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            (if ebits.getD (ebits.length - 1) false then (2 : ℤ) ^ (ebits.length - 1) else 0)) := by
    by_cases hb : ebits.getD (ebits.length - 1) false
    · -- 位1
      have hbit1 : (tape (p_e + (ebits.length : ℤ))).1 = SymKind.data1 := by
        rw [hbitN, if_pos hb]
      rcases round_to13 p_e ebits.length tape hp_e hn1 hnpe hbit1 hmarkerK
        hbound0 hboundL htrailK hbwdK hmarks hflagFree (hborK hb)
        with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
          hsplit1r⟩
      have hlenForm : (πr.length : ℤ) = (ebits.length : ℤ) + 2 * p_e + 2 +
          (if ebits.getD (ebits.length - 1) false then 1 else 0) := by
        rw [hlenr, if_pos hb]
        omega
      have hexr : regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            (if ebits.getD (ebits.length - 1) false then (2 : ℤ) ^ (ebits.length - 1) else 0) := by
        rw [if_pos hb]
        rcases hsplit1r with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw, hj0, hup⟩
        · have hstep := regVal_step_d1 tape cfgr.tape ((p_e - 2).toNat) ebits.length hn1
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            h3 h1 h2
            (by intro i hi1 hi2; exact h4 i hi1 (by omega))
          exact hstep
        · let jn : ℕ := j.toNat
          have hjcast : (jn : ℤ) = j := by
            dsimp only [jn]
            exact Int.toNat_of_nonneg (by omega)
          have hstep := regVal_step_walk tape cfgr.tape ((p_e - 2).toNat) ebits.length jn hn1
            (by omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            (by
              have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
              omega)
            h3
            (by
              intro i hi1 hi2
              rw [hjcast] at hi2
              by_cases hik : i = (ebits.length : ℤ)
              · rw [hik]
                exact ⟨h1, h2⟩
              · exact ⟨(hw i (by omega) hi2).1, (hw i (by omega) hi2).2⟩)
            (by
              rw [hjcast]
              exact ⟨hdj, by intro hc; rw [hc] at hj0; exact absurd hj0 (by intro h; cases h)⟩)
            (by
              intro i hi1 hi2
              rw [hjcast] at hi1
              exact hup i hi1 (by omega))
          exact hstep
      have hnetr : regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
        have h2 := hexr
        rw [if_pos hb] at h2
        exact h2.ge
      exact ⟨πr, cfgr, hsr, hstr, hhdr, hlenForm, hkeepLr, hkeepWr, hburnr, hmK2, hmKk,
        (by intro i h1 h2; exact (hmidr i h1 h2).2),
        (by intro i h1 h2; exact (hmidr i h1 h2).1),
        (by rw [hkeepLr 0 (by omega)]),
        hnetr, hexr⟩
    · -- 位0
      have hbit0 : (tape (p_e + (ebits.length : ℤ))).1 = SymKind.data0 := by
        rw [hbitN, if_neg hb]
      rcases round_d0 p_e ebits.length tape hp_e hn1 hnpe hbit0 hmarkerK
        hbound0 hboundL htrailK hbwdK hmarks hflagFree
        with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hkeepLr, ⟨hmK2, hmKk⟩, hmidr, hkeepWr, hburnr,
          hsplit0r⟩
      have hlenForm : (πr.length : ℤ) = (ebits.length : ℤ) + 2 * p_e + 2 +
          (if ebits.getD (ebits.length - 1) false then 1 else 0) := by
        rw [hlenr, if_neg hb]
        omega
      have hstep := regVal_step_d0 tape cfgr.tape ((p_e - 2).toNat) ebits.length
        (by intro i hi1 hi2; rw [hkeepLr i hi2])
        (by
          intro i hi1 hi2
          by_cases hik : i = (ebits.length : ℤ)
          · rw [hik]
            exact hsplit0r
          · rw [hmidr i (by omega)
              (by
                have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
                omega)])
      have hnetr : regVal cfgr.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
        rw [hstep]
        exact sub_le_self _ (by positivity)
      have hexr : regVal cfgr.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            (if ebits.getD (ebits.length - 1) false then (2 : ℤ) ^ (ebits.length - 1) else 0) := by
        rw [if_neg hb, sub_zero]
        exact hstep
      exact ⟨πr, cfgr, hsr, hstr, hhdr, hlenForm, hkeepLr, hkeepWr, hburnr, hmK2, hmKk,
        (by intro i h1 h2; rw [hmidr i h1 h2]; exact hflagFree i (by omega) h2),
        (by intro i h1 h2; rw [hmidr i h1 h2]; exact hbwdK i (by omega) h2),
        (by rw [hkeepLr 0 (by omega)]),
        hnetr, hexr⟩
  -- ===== 清尾（含 13 出口 → 84 → 20） =====
  have htrailR : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) → cfgr.tape i = Sym.consumed
      := by
    intro i h1 h2
    by_cases hq : i = p_e + (ebits.length : ℤ)
    · rw [hq]; exact hburnr
    · rw [hkeepWr i (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact htrailK i (by omega) (by omega)
  have hexit3R : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
      (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel ∨
      (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
    rw [hkeepWr _ (Or.inr (Or.inr (by omega))), hidx]
    rcases hend with h | h | h
    · exact Or.inl (by
        have h3 := congrArg (fun s : Sym => s.1) h
        simpa [Sym.sel] using h3)
    · exact Or.inr (Or.inl (by
        have h3 := congrArg (fun s : Sym => s.1) h
        simpa [Sym.nosel] using h3))
    · exact Or.inr (Or.inr h)
  have hbwdR : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (cfgr.tape i).1 = SymKind.data0 ∨ (cfgr.tape i).1 = SymKind.data1 := by
    intro i h1 h2
    by_cases hk : i = (ebits.length : ℤ)
    · rw [hk]; exact hmKk
    · by_cases hik : i < (ebits.length : ℤ)
      · rw [hkeepLr i hik]
        exact hbwdK i (by omega) h2
      · exact hmidKind i (by omega) h2
  have hmarksR : ∀ i : ℤ, 1 ≤ i → i ≤ (ebits.length : ℤ) - 1 → (cfgr.tape i).2 = true := by
    intro i h1 h2
    rw [hkeepLr i (by omega)]
    exact hmarks i (by omega) (by omega)
  have hflagFreeR : ∀ i : ℤ, (ebits.length : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (cfgr.tape i).2 = false :=
      by
    intro i h1 h2
    exact hmidFlag i (by omega) h2
  rcases cleanup_unit p_e ebits.length cfgr.tape hn1 hnpe htrailR hexit3R
    (by rw [hkeepWr p_e (Or.inl ⟨by omega, le_rfl⟩)]; exact hmarkerK)
    (by rw [hkeepWr (p_e - 1) (Or.inl ⟨by omega, by omega⟩)]; exact hbound0)
    (by rw [hkeepLr 0 (by omega)]; exact hboundL)
    hbwdR hmarksR hmK2 hflagFreeR
    with ⟨πc, cfgc, hsc, hstc, hhdc, hlenc, hclrc, hkeepc⟩
  -- ===== 扩展 =====
  have hmar0c : cfgc.tape p_e = Sym.data0 := by
    rw [hkeepc p_e (Or.inr (by omega)), hkeepWr p_e (Or.inl ⟨by omega, le_rfl⟩)]
    exact hmar0
  have hb0c : cfgc.tape (p_e - 1) = Sym.boundary := by
    rw [hkeepc (p_e - 1) (Or.inr (by omega)), hkeepWr (p_e - 1) (Or.inl ⟨by omega, by omega⟩)]
    exact hbound0
  have htrailc : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) → cfgc.tape i = Sym.consumed
      := by
    intro i h1 h2
    rw [hkeepc i (Or.inr (by omega))]
    exact htrailR i h1 h2
  have hexitc : cfgc.tape (p_e + (ebits.length : ℤ) + 1) = Sym.sel ∨
      cfgc.tape (p_e + (ebits.length : ℤ) + 1) = Sym.nosel ∨
      (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
    rw [hkeepc _ (Or.inr (by omega)), hkeepWr _ (Or.inr (Or.inr (by omega))), hidx]
    exact hend
  rcases expand_unit p_e ebits.length cfgc.tape hn1 hmar0c hb0c htrailc hexitc
    with ⟨πx, cfgx, hsx, hdisx, hxC1, hxC2⟩
  have hexc : regVal cfgc.tape ((p_e - 2).toNat) = regVal cfgr.tape ((p_e - 2).toNat) := by
    simp only [regVal]
    exact regValA_congr_kind cfgr.tape cfgc.tape 1 ((p_e - 2).toNat) 0 (by
      intro j hj
      by_cases hjk : j < ebits.length
      · simp only [hclrc j hjk, Sym.mk_fst]
      · rw [hkeepc (1 + (j : ℤ)) (Or.inr (by omega))])
  have hnetc : regVal cfgc.tape ((p_e - 2).toNat) ≥
      regVal tape ((p_e - 2).toNat) - (2 : ℤ) ^ (ebits.length - 1) := by
    rw [hexc]
    exact hnet0
  -- ===== 拼接 =====
  have e13x : cfgr = SymConfig.mk 13 cfgr.tape (p_e + 2) := by
    rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
    rw [hstr, hhdr]
  have ccc : SymSteps VerifierSym.transition cfgr πc cfgc := by
    rw [e13x]; exact hsc
  have e203 : cfgc = SymConfig.mk 20 cfgc.tape (p_e - 1) := by
    rw [show cfgc = SymConfig.mk cfgc.state cfgc.tape cfgc.headPos from rfl]
    rw [hstc, hhdc]
  have cxx : SymSteps VerifierSym.transition cfgc πx cfgx := by
    rw [e203]; exact hsx
  have acx : SymSteps VerifierSym.transition cfgr (πc ++ πx) cfgx :=
    symSteps_append_concat πc πx ccc cxx
  have afinal : SymSteps VerifierSym.transition
      (SymConfig.mk 5 tape (p_e + (ebits.length : ℤ))) (πr ++ (πc ++ πx)) cfgx :=
    symSteps_append_concat πr (πc ++ πx) hsr acx
  rcases hdisx with ⟨hxst, hxhd, hxlen, hxstamp, hxta, hxl, hxt, hxr⟩ |
      ⟨hxst, hxhd, hxlen, hxta, hxl, hxt, hxr⟩
  · -- ===== 中元素 → 4 =====
    refine ⟨πr ++ (πc ++ πx), cfgx, afinal, ?_, ?_, ?_, ?_⟩
    left
    refine ⟨hxst, hxhd, ?_, hxstamp, hxta, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 长度
      rw [List.length_append, List.length_append]
      push_cast
      rw [hlenForm, hlenc, hxlen]
      omega
    · -- 左界保持（cell 0）
      rw [hxl 0 (by omega), hkeepc 0 (Or.inl (by omega)), hkeepLr 0 (by omega)]
    · -- 净值（引理 B 合成）
      have hxk : regVal cfgx.tape ((p_e - 2).toNat) = regVal cfgc.tape ((p_e - 2).toNat) := by
        simp only [regVal]
        exact regValA_congr_kind cfgc.tape cfgx.tape 1 ((p_e - 2).toNat) 0 (by
          intro j hj
          rw [hxl (1 + (j : ℤ)) (by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega)])
      rw [hxk]
      exact hnetc
    · -- 区内无标 `[1, p_e+n−1]`
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hf : (cfgc.tape i).2 = false := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        exact hf
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidFlag i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; rfl
    · -- 区内全 data `[1, p_e+n−1]`
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hk : (cfgc.tape i).1 = (cfgr.tape i).1 := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        rw [hk]
        exact hbwdR i h1 (by omega)
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidKind i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; exact Or.inl rfl
    · -- 终止符保持
      rw [hxt, hkeepc _ (Or.inr (by omega)), hkeepWr _ (Or.inr (Or.inr (by omega)))]
    · -- 高区保持
      intro i hi
      rw [hxr i hi, hkeepc i (Or.inr (by omega)), hkeepWr i (Or.inr (Or.inr (by omega)))]
    · -- C1：boundary ⟹ 22
      intro hb
      have hbcfgr : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
        rw [hkeepWr (p_e + (ebits.length : ℤ) + 1) (Or.inr (Or.inr (by omega)))]
        exact hb
      have hbcfgc : (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
        rw [hkeepc (p_e + (ebits.length : ℤ) + 1) (Or.inr (by omega))]
        exact hbcfgr
      have h22 := hxC1 hbcfgc
      rw [hxst] at h22
      exact absurd h22 (by decide)
    · -- C2：sel/nosel ⟹ 4（本支）
      intro _
      exact hxst
    · -- EX：净值精确式（清尾/扩展保持 + 轮精确）
      have hexx : regVal cfgx.tape ((p_e - 2).toNat) = regVal cfgc.tape ((p_e - 2).toNat) := by
        simp only [regVal]
        exact regValA_congr_kind cfgc.tape cfgx.tape 1 ((p_e - 2).toNat) 0 (by
          intro j hj
          rw [hxl (1 + (j : ℤ)) (by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega)])
      rw [hexx, hexc]
      exact hex0
  · -- ===== 末元素 → 22 =====
    refine ⟨πr ++ (πc ++ πx), cfgx, afinal, ?_, ?_, ?_, ?_⟩
    right
    refine ⟨hxst, hxhd, ?_, hxta, (by rw [hxl 0 (by omega), hkeepc 0 (Or.inl (by omega)),
      hkeepLr 0 (by omega)]), ?_, ?_, ?_, ?_⟩
    · -- 长度
      rw [List.length_append, List.length_append]
      push_cast
      rw [hlenForm, hlenc, hxlen]
      omega
    · -- 区内无标
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hf : (cfgc.tape i).2 = false := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        exact hf
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidFlag i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; rfl
    · -- 区内全 data
      intro i h1 h2
      by_cases hseg1 : i ≤ (ebits.length : ℤ)
      · rw [hxl i (by omega)]
        have hk : (cfgc.tape i).1 = (cfgr.tape i).1 := by
          rw [show (cfgc.tape i) = Sym.mk (cfgr.tape i).1 false from by
            rw [show i = 1 + (((i - 1).toNat : ℕ) : ℤ) from by
              have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - 1 by omega)
              omega]
            exact hclrc ((i - 1).toNat) (by omega)]
          rfl
        rw [hk]
        exact hbwdR i h1 (by omega)
      · by_cases hseg2 : i ≤ p_e - 2
        · rw [hxl i (by omega), hkeepc i (Or.inr (by omega))]
          exact hmidKind i (by omega) hseg2
        · have h5 := hxta ((i - (p_e - 1)).toNat)
              (by
                simp only [List.length_replicate]
                have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
                omega)
          have hidx2 : (p_e - 1) + (((i - (p_e - 1)).toNat : ℕ) : ℤ) = i := by
            have hcast := Int.toNat_of_nonneg (show (0 : ℤ) ≤ i - (p_e - 1) by omega)
            omega
          rw [← hidx2, h5]
          simp only [List.getElem_replicate, Sym.data0]; exact Or.inl rfl
    · -- 终止符保持
      rw [hxt, hkeepc _ (Or.inr (by omega)), hkeepWr _ (Or.inr (Or.inr (by omega)))]
    · -- 高区保持
      intro i hi
      rw [hxr i hi, hkeepc i (Or.inr (by omega)), hkeepWr i (Or.inr (Or.inr (by omega)))]
    · -- C1：boundary ⟹ 22（本支）
      intro _
      exact hxst
    · -- C2：sel/nosel ⟹ 4（与 boundary 矛盾）
      intro hsn
      have hsncfgr : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
        rcases hsn with h | h
        · left
          rw [hkeepWr (p_e + (ebits.length : ℤ) + 1) (Or.inr (Or.inr (by omega)))]
          exact h
        · right
          rw [hkeepWr (p_e + (ebits.length : ℤ) + 1) (Or.inr (Or.inr (by omega)))]
          exact h
      have hsncfgc : (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (cfgc.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
        rcases hsncfgr with h | h
        · left
          rw [hkeepc (p_e + (ebits.length : ℤ) + 1) (Or.inr (by omega))]
          exact h
        · right
          rw [hkeepc (p_e + (ebits.length : ℤ) + 1) (Or.inr (by omega))]
          exact h
      have h4 := hxC2 hsncfgc
      rw [hxst] at h4
      exact absurd h4 (by decide)
    · -- EX：净值精确式（清尾/扩展保持 + 轮精确）
      have hexx : regVal cfgx.tape ((p_e - 2).toNat) = regVal cfgc.tape ((p_e - 2).toNat) := by
        simp only [regVal]
        exact regValA_congr_kind cfgc.tape cfgx.tape 1 ((p_e - 2).toNat) 0 (by
          intro j hj
          rw [hxl (1 + (j : ℤ)) (by
            have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
            omega)])
      rw [hexx, hexc]
      exact hex0

/-- [值 · 末日] `drop (n−1)` 取到末元素（单元素表）。 -/
lemma drop_last_eq (l : List Bool) (hn : 1 ≤ l.length) :
    l.drop (l.length - 1) = [l.getD (l.length - 1) false] := by
  rw [drop_eq_getD_cons l (l.length - 1) (by omega)]
  rw [show l.length - 1 + 1 = l.length from by omega]
  simp

/-- [值 · 末日值] 单元素表的值 = 位真 ? w : 0。 -/
lemma valFrom_last_eq (l : List Bool) (hn : 1 ≤ l.length) (w : ℤ) :
    valFrom (l.drop (l.length - 1)) w = (if l.getD (l.length - 1) false then w else 0) := by
  rw [drop_last_eq l hn, valFrom_single]

/-- [辅助] Bool 假：(¬ b) ⟹ b = false。 -/
lemma bool_eq_false_of_not (b : Bool) (h : ¬ b) : b = false := by
  cases b <;> simp_all

set_option maxHeartbeats 900000 in
-- segSrSel_aux 一般版：按位分流（round_chain_t/f）+ valFrom 不动式线程贯穿
/-- [段 · 递归核心 · 一般版] 从轮 k 起点 `5 @ (p_e+k)` 走完剩余全部轮（k…n），数据一般：
    k < n 按位 `by_cases` 分流 `round_chain_t/f` 前移；k = n 用 `last_chain_gen` 收段末。
    R 不动式改 valFrom 形：`valFrom (ebits.drop (k−1)) (2^{k−1}) ≤ regVal`。
    长度 ≤ `(n−k)·(2n+2p_e+3) + (4p_e+4n+12)`。 -/
lemma segSrSel_aux_gen (ebits : List Bool) (p_e : ℤ)
    (hn1 : 1 ≤ ebits.length) (hnpe : (ebits.length : ℤ) ≤ p_e - 2) :
    ∀ (m k : ℕ), ebits.length - k = m → 1 ≤ k → k ≤ ebits.length →
      ∀ (tape : ℤ → Sym),
      valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) ≤ regVal tape ((p_e - 2).toNat) →
      tape p_e = Sym.data0 →
      tape (p_e - 1) = Sym.boundary →
      tape 0 = Sym.boundary →
      (∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) - 1 → tape i = Sym.consumed) →
      (∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) - 1 → (tape i).2 = true) →
      (∀ i : ℤ, (k : ℤ) ≤ i → i ≤ p_e - 2 → (tape i).2 = false) →
      (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
        (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1) →
      (∀ i : ℕ, k ≤ i → i < ebits.length + 1 →
        (tape (p_e + (i : ℤ))).1 =
          (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0)) →
      (tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) →
      ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) π cfg' ∧
        ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) ≤ ((ebits.length - k : ℕ) : ℤ) *
              (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) ∧
            cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (regVal cfg'.tape ((p_e - 2).toNat) ≥
              regVal tape ((p_e - 2).toNat) -
                valFrom (ebits.drop (k - 1)) (2 ^ (k - 1))) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) = tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
          (cfg'.state = 22 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
            (π.length : ℤ) ≤ ((ebits.length - k : ℕ) : ℤ) *
              (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) ∧
            tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 2) Sym.data0) ∧
            (cfg'.tape 0 = tape 0) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
            (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
              (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
            (cfg'.tape (p_e + (ebits.length : ℤ) + 1) = tape (p_e + (ebits.length : ℤ) + 1)) ∧
            (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
        (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
          (tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) ∧
        (regVal cfg'.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            valFrom (ebits.drop (k - 1)) (2 ^ (k - 1))) := by
  intro m
  induction m with
  | zero =>
      intro k hnk hk1 hkn tape hR hmar0 hbound0 hboundL htrailK hmarks hflagFree hbwdK hbitK hend
      have hk'n : k = ebits.length := by omega
      have hp_e : 3 ≤ p_e := by omega
      rcases last_chain_gen ebits p_e tape hn1 hnpe hmar0 hbound0 hboundL
        (by rw [← hk'n]; exact htrailK)
        (by rw [← hk'n]; exact hmarks)
        (by rw [← hk'n]; exact hflagFree)
        hbwdK
        (by rw [← hk'n]; exact hbitK k le_rfl (by omega))
        (by
          rw [← hk'n]
          intro hbT hk0
          refine hbor_of_regVal tape p_e k hp_e hk1 (by omega) hbwdK ?_ hk0
          have hbT' : ebits.getD (ebits.length - 1) false = true := by
            rw [← hk'n]; exact hbT
          have hkey : (2 : ℤ) ^ (ebits.length - 1) ≤
              valFrom (ebits.drop (ebits.length - 1)) (2 ^ (ebits.length - 1)) := by
            rw [valFrom_last_eq ebits hn1, if_pos hbT']
          have hw : (2 : ℤ) ^ (k - 1) ≤ valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) := by
            rw [hk'n]
            exact hkey
          exact le_trans hw hR)
        hend
        with ⟨π, cfg', hs, hcase, hC1, hC2, hex⟩
      have hvF : valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) =
          (if ebits.getD (ebits.length - 1) false then (2 : ℤ) ^ (ebits.length - 1) else 0) := by
        rw [hk'n, valFrom_last_eq ebits hn1]
      refine ⟨π, cfg', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk'n]
        exact hs
      rcases hcase with ⟨hst, hhd, hlen, hstamp, hagr, hblA, hnetA, hfl, hkd, htk, hhk⟩ |
        ⟨hst, hhd, hlen, hagr, hblA, hfl, hkd, htk, hhk⟩
      · left
        refine ⟨hst, hhd, ?_, hstamp, hagr, hblA, ?_, hfl, hkd, htk, hhk⟩
        · have hz : ((ebits.length - k : ℕ) : ℤ) = 0 := by omega
          have hcast : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 :=
            Int.toNat_of_nonneg (by omega)
          have hbit : (if ebits.getD (ebits.length - 1) false then (1 : ℤ) else 0) ≤ 1 := by
            split <;> omega
          rw [hlen, hz, hcast]
          omega
        · rw [hvF]
          exact hex.ge
      · right
        refine ⟨hst, hhd, ?_, hagr, hblA, hfl, hkd, htk, hhk⟩
        have hz : ((ebits.length - k : ℕ) : ℤ) = 0 := by omega
        have hcast : (((p_e - 2).toNat : ℕ) : ℤ) = p_e - 2 :=
          Int.toNat_of_nonneg (by omega)
        have hbit : (if ebits.getD (ebits.length - 1) false then (1 : ℤ) else 0) ≤ 1 := by
          split <;> omega
        rw [hlen, hz, hcast]
        omega
      · -- C1：boundary ⟹ 22（透传）
        exact hC1
      · -- C2：sel/nosel ⟹ 4（透传）
        exact hC2
      · -- EX：净值精确式（k = n 基底，经 hvF 归约到条件精确式）
        rw [hvF]
        exact hex
  | succ m ih =>
      intro k hnk hk1 hkn tape hR hmar0 hbound0 hboundL htrailK hmarks hflagFree hbwdK hbitK hend
      have hkn' : k < ebits.length := by omega
      have hp_e : 3 ≤ p_e := by omega
      have hkpe : (k : ℤ) ≤ p_e - 2 := by omega
      have h2k : 2 * (2 : ℤ) ^ (k - 1) = (2 : ℤ) ^ k := by
        have hk' : k = (k - 1) + 1 := by omega
        conv_rhs => rw [hk']
        rw [pow_succ]
        ring
      -- 按位分流：本轮出口束（轮 + 条件净值精确 + valFrom 不动式转移）
      have hbundle : ∃ (πr : List SymStep) (cfgr : SymConfig),
          SymSteps VerifierSym.transition (SymConfig.mk 5 tape (p_e + (k : ℤ))) πr cfgr ∧
          cfgr.state = 5 ∧ cfgr.headPos = p_e + (k : ℤ) + 1 ∧
          (πr.length : ℤ) = 2 * (k : ℤ) + 2 * p_e + 2 +
            (if ebits.getD (k - 1) false then 1 else 0) ∧
          cfgr.tape p_e = Sym.data0 ∧
          cfgr.tape (p_e - 1) = Sym.boundary ∧
          cfgr.tape 0 = Sym.boundary ∧
          (∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + (k : ℤ) → cfgr.tape i = Sym.consumed) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ (k : ℤ) → (cfgr.tape i).2 = true) ∧
          (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i ≤ p_e - 2 → (cfgr.tape i).2 = false) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
            (cfgr.tape i).1 = SymKind.data0 ∨ (cfgr.tape i).1 = SymKind.data1) ∧
          (∀ i : ℕ, k + 1 ≤ i → i < ebits.length + 1 →
            (cfgr.tape (p_e + (i : ℤ))).1 =
              (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0)) ∧
          (∀ i : ℤ, p_e + (k : ℤ) < i → cfgr.tape i = tape i) ∧
          (regVal cfgr.tape ((p_e - 2).toNat) =
            regVal tape ((p_e - 2).toNat) -
              (if ebits.getD (k - 1) false then (2 : ℤ) ^ (k - 1) else 0)) ∧
          (valFrom (ebits.drop k) (2 ^ k) ≤ regVal cfgr.tape ((p_e - 2).toNat)) := by
        by_cases hb : ebits.getD (k - 1) false
        · -- ===== 位1 =====
          have hborK : (tape (k : ℤ)).1 = SymKind.data0 →
              ∃ j : ℤ, (k : ℤ) + 1 ≤ j ∧ j ≤ p_e - 2 ∧
                (∀ i : ℤ, (k : ℤ) + 1 ≤ i → i < j → (tape i).1 = SymKind.data0) ∧
                (tape j).1 = SymKind.data1 := by
            intro hk0
            refine hbor_of_regVal tape p_e k hp_e hk1 hkpe hbwdK ?_ hk0
            have hw : (2 : ℤ) ^ (k - 1) ≤ valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) := by
              rw [valFrom_drop_succ ebits k hk1 (by omega)]
              rw [if_pos hb]
              have h2 : (0 : ℤ) ≤ valFrom (ebits.drop k) (2 * (2 : ℤ) ^ (k - 1)) :=
                valFrom_nonneg _ _ (by positivity)
              omega
            exact le_trans hw hR
          rcases round_chain_t ebits p_e tape k hk1 hkn' hnpe hb hmar0 hbound0 hboundL
            htrailK hmarks hflagFree hbwdK hbitK hborK
            with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hmar0', hbound0', hboundL',
              htrailK', hmarks', hflagFree', hbwdK', hbitK', hsplit, hkeepHigh'⟩
          have hRex : regVal cfgr.tape ((p_e - 2).toNat) =
              regVal tape ((p_e - 2).toNat) -
                (if ebits.getD (k - 1) false then (2 : ℤ) ^ (k - 1) else 0) := by
            rw [if_pos hb]
            rcases hsplit with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, j, hj1, hj2, hdj, hw', hj0, hup⟩
            · have hstep := regVal_step_d1 tape cfgr.tape ((p_e - 2).toNat) k hk1 (by omega) h3 h1 h2
                (by intro i hi1 hi2; exact h4 i hi1 (by omega))
              exact hstep
            · let jn : ℕ := j.toNat
              have hjcast : (jn : ℤ) = j := by
                dsimp only [jn]
                exact Int.toNat_of_nonneg (by omega)
              have hstep := regVal_step_walk tape cfgr.tape ((p_e - 2).toNat) k jn hk1
                (by omega)
                (by
                  have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
                  omega)
                (by
                  have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
                  omega)
                h3
                (by
                  intro i hi1 hi2
                  rw [hjcast] at hi2
                  by_cases hik : i = (k : ℤ)
                  · rw [hik]
                    exact ⟨h1, h2⟩
                  · exact ⟨(hw' i (by omega) hi2).1, (hw' i (by omega) hi2).2⟩)
                (by
                  rw [hjcast]
                  exact ⟨hdj, by intro hc; rw [hc] at hj0; exact absurd hj0 (by intro h; cases h)⟩)
                (by
                  intro i hi1 hi2
                  rw [hjcast] at hi1
                  exact hup i hi1 (by omega))
              exact hstep
          have hRnew : valFrom (ebits.drop k) (2 ^ k) ≤ regVal cfgr.tape ((p_e - 2).toNat) := by
            rw [hRex, if_pos hb]
            have hv1 := valFrom_drop_succ ebits k hk1 (by omega) (2 ^ (k - 1))
            rw [if_pos hb] at hv1
            rw [h2k] at hv1
            linarith [hv1, hR]
          exact ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hmar0', hbound0', hboundL', htrailK',
            hmarks', hflagFree', hbwdK', hbitK', hkeepHigh', hRex, hRnew⟩
        · -- ===== 位0 =====
          have hbF : ebits.getD (k - 1) false = false := bool_eq_false_of_not _ hb
          rcases round_chain_f ebits p_e tape k hk1 hkn' hnpe hbF hmar0 hbound0 hboundL
            htrailK hmarks hflagFree hbwdK hbitK
            with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hmar0', hbound0', hboundL',
              htrailK', hmarks', hflagFree', hbwdK', hbitK', hsplit, hkeepHigh'⟩
          have hRex : regVal cfgr.tape ((p_e - 2).toNat) =
              regVal tape ((p_e - 2).toNat) -
                (if ebits.getD (k - 1) false then (2 : ℤ) ^ (k - 1) else 0) := by
            rw [if_neg hb]
            rcases hsplit with ⟨h3, _⟩
            have hstep := regVal_step_d0 tape cfgr.tape ((p_e - 2).toNat) k
              (by intro i hi1 hi2; exact h3 i (by omega) (by omega))
              (by intro i hi1 hi2; exact h3 i (by omega) (by omega))
            rw [sub_zero]
            exact hstep
          have hRnew : valFrom (ebits.drop k) (2 ^ k) ≤ regVal cfgr.tape ((p_e - 2).toNat) := by
            rw [hRex, if_neg hb, sub_zero]
            have hv1 := valFrom_drop_succ ebits k hk1 (by omega) (2 ^ (k - 1))
            rw [if_neg hb] at hv1
            rw [h2k] at hv1
            have : valFrom (ebits.drop k) (2 ^ k) =
                valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) := by linarith [hv1]
            rw [this]
            exact hR
          exact ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hmar0', hbound0', hboundL', htrailK',
            hmarks', hflagFree', hbwdK', hbitK', hkeepHigh', hRex, hRnew⟩
      rcases hbundle with ⟨πr, cfgr, hsr, hstr, hhdr, hlenr, hmar0', hbound0', hboundL',
        htrailK', hmarks', hflagFree', hbwdK', hbitK', hkeepHigh', hRex, hRnew⟩
      -- 递归：k+1
      have hnk' : ebits.length - (k + 1) = m := by omega
      rcases ih (k + 1) hnk' (by omega) (by omega) cfgr.tape hRnew hmar0' hbound0' hboundL'
        (by rw [show p_e + ((k + 1 : ℕ) : ℤ) - 1 = p_e + (k : ℤ) from by push_cast; ring]
            exact htrailK')
        (by rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) from by push_cast; ring]
            exact hmarks')
        (by rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring]
            exact hflagFree')
        hbwdK' hbitK'
        (by
          rw [hkeepHigh' (p_e + 1 + (ebits.length : ℤ)) (by omega)]
          exact hend)
        with ⟨π₂, cfg₂, hs₂, hcase₂, hC1₂, hC2₂, hEX₂⟩
      have hcont : ∀ (L₂ : ℤ), (π₂.length : ℤ) ≤ L₂ →
          L₂ ≤ ((ebits.length - (k + 1) : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            (4 * p_e + 4 * (ebits.length : ℤ) + 12) →
          ((πr ++ π₂).length : ℤ) ≤ ((ebits.length - k : ℕ) : ℤ) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
        intro L₂ h2 h3
        rw [List.length_append]
        push_cast
        rw [hlenr]
        have hD2 : ((ebits.length - (k + 1) : ℕ) : ℤ) =
            ((ebits.length - k : ℕ) : ℤ) - 1 := by omega
        have hbnd2' : L₂ ≤ (((ebits.length - k : ℕ) : ℤ) - 1) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
          rw [← hD2]
          exact h3
        have hkey : (2 * (k : ℤ) + 2 * p_e + 2 +
            (if ebits.getD (k - 1) false then (1 : ℤ) else 0)) ≤
            2 * (ebits.length : ℤ) + 2 * p_e + 3 := by
          have hbit1 : (if ebits.getD (k - 1) false then (1 : ℤ) else 0) ≤ 1 := by
            split <;> omega
          omega
        have hAlg : (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            ((((ebits.length - k : ℕ) : ℤ) - 1) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
              (4 * p_e + 4 * (ebits.length : ℤ) + 12)) =
            ((ebits.length - k : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
              (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
          ring
        rw [← hAlg]
        linarith
      have hRexT : regVal cfg₂.tape ((p_e - 2).toNat) =
          regVal tape ((p_e - 2).toNat) -
            valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) := by
        have h2 := hEX₂
        rw [show k + 1 - 1 = k from by omega] at h2
        rw [h2, hRex]
        have hv1 := valFrom_drop_succ ebits k hk1 (by omega) (2 ^ (k - 1))
        rw [h2k] at hv1
        by_cases hb : ebits.getD (k - 1) false
        · rw [if_pos hb] at hv1
          rw [if_pos hb]
          linarith [hv1]
        · rw [if_neg hb] at hv1
          rw [if_neg hb]
          linarith [hv1]
      refine ⟨πr ++ π₂, cfg₂, symSteps_append_concat πr π₂ hsr ?_, ?_, ?_, ?_, ?_⟩
      · have e : cfgr = SymConfig.mk 5 cfgr.tape (p_e + ((k + 1 : ℕ) : ℤ)) := by
          rw [show cfgr = SymConfig.mk cfgr.state cfgr.tape cfgr.headPos from rfl]
          rw [hstr, hhdr]
          push_cast
          rw [add_assoc]
        rw [e]
        exact hs₂
      · rcases hcase₂ with ⟨hst, hhd, hl, hstamp, hagr₂, hbl₂, hnet₂, hfl, hkd, htk, hhk⟩ |
          ⟨hst, hhd, hl, hagr, hbl₂, hfl, hkd, htk, hhk⟩
        have hnet : regVal cfg₂.tape ((p_e - 2).toNat) ≥
            regVal tape ((p_e - 2).toNat) -
              valFrom (ebits.drop (k - 1)) (2 ^ (k - 1)) := by
          have h2 := hnet₂
          rw [show (k + 1) - 1 = k from by omega] at h2
          rw [hRex] at h2
          have hv1 := valFrom_drop_succ ebits k hk1 (by omega) (2 ^ (k - 1))
          rw [h2k] at hv1
          by_cases hb : ebits.getD (k - 1) false
          · rw [if_pos hb] at hv1
            rw [if_pos hb] at h2
            linarith [hv1]
          · rw [if_neg hb] at hv1
            rw [if_neg hb] at h2
            linarith [hv1]
        have hbl : cfg₂.tape 0 = tape 0 := hbl₂.trans (hboundL'.trans hboundL.symm)
        · left
          refine ⟨hst, hhd, hcont _ le_rfl hl, hstamp, hagr₂, hbl, hnet, hfl, hkd, ?_, ?_⟩
          · rw [htk, hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
          · intro i hi
            rw [hhk i hi, hkeepHigh' i (by omega)]
        · right
          refine ⟨hst, hhd, hcont _ le_rfl hl, hagr,
            hbl₂.trans (hboundL'.trans hboundL.symm), hfl, hkd, ?_, ?_⟩
          · rw [htk, hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
          · intro i hi
            rw [hhk i hi, hkeepHigh' i (by omega)]
      · -- C1：boundary ⟹ 22（经本轮 hkeepHigh' 平移）
        intro hb'
        have hb'' : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
          rw [hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
          exact hb'
        exact hC1₂ hb''
      · -- C2：sel/nosel ⟹ 4（经本轮 hkeepHigh' 平移）
        intro hsn
        have hsn' : (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
            (cfgr.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
          rcases hsn with h | h
          · left
            rw [hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
            exact h
          · right
            rw [hkeepHigh' (p_e + (ebits.length : ℤ) + 1) (by omega)]
            exact h
        exact hC2₂ hsn'
      · -- EX：净值精确式（轮精确 + 归纳精确）
        exact hRexT

set_option maxHeartbeats 900000 in -- 因：段装配含入口桥与长度预算算术
-- segSrSel 公开（一般版）：入口步 + 段递归（数据一般）+ 段界
/-- [段 · 公开接口 · 一般版] 从 `4 @ p_e`（sel 入口，数据一般）走完整段：入口步（4→5）→ `segSrSel_aux_gen` 全链。
    长度 ≤ `n·(2n+2p_e+3) + (4p_e+4n+13)`（= 族同界）。 -/
lemma segSrSel_gen (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hn1 : 1 ≤ ebits.length) (hnpe : (ebits.length : ℤ) ≤ p_e - 2)
    (hsel : tape p_e = Sym.sel)
    (hbound0 : tape (p_e - 1) = Sym.boundary)
    (hboundL : tape 0 = Sym.boundary)
    (hbwd0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1)
    (hflag0 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 → (tape i).2 = false)
    (hbits : ∀ i : ℕ, 1 ≤ i → i < ebits.length + 1 →
      (tape (p_e + (i : ℤ))).1 =
        (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0))
    (hR0 : valFrom ebits 1 ≤ regVal tape ((p_e - 2).toNat))
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      ((cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
          (π.length : ℤ) ≤ (ebits.length : ℤ) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            (4 * p_e + 4 * (ebits.length : ℤ) + 13) ∧
          cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
          tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
          (cfg'.tape 0 = tape 0) ∧
          (regVal cfg'.tape ((p_e - 2).toNat) ≥
            regVal tape ((p_e - 2).toNat) - valFrom ebits 1) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
            (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
          (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
            tape (p_e + (ebits.length : ℤ) + 1)) ∧
          (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i)) ∨
        (cfg'.state = 22 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
          (π.length : ℤ) ≤ (ebits.length : ℤ) *
            (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
            (4 * p_e + 4 * (ebits.length : ℤ) + 13) ∧
          tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 2) Sym.data0) ∧
          (cfg'.tape 0 = tape 0) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 → (cfg'.tape i).2 = false) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ p_e + (ebits.length : ℤ) - 1 →
            (cfg'.tape i).1 = SymKind.data0 ∨ (cfg'.tape i).1 = SymKind.data1) ∧
          (cfg'.tape (p_e + (ebits.length : ℤ) + 1) =
            tape (p_e + (ebits.length : ℤ) + 1)) ∧
          (∀ i : ℤ, p_e + (ebits.length : ℤ) + 1 < i → cfg'.tape i = tape i))) ∧
      (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary) → cfg'.state = 22) ∧
      (((tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
        (tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel) → cfg'.state = 4) ∧
      (regVal cfg'.tape ((p_e - 2).toNat) =
        regVal tape ((p_e - 2).toNat) - valFrom ebits 1) := by
  have hp_e : 3 ≤ p_e := by omega
  rcases step4sel p_e tape hsel with ⟨π₁, cfg₁, hs₁, hst₁, hhd₁, htp₁, hlen₁⟩
  -- 入口后 tape 的区域值不变（写格 p_e 在区域之外）
  have hregEq : regVal cfg₁.tape ((p_e - 2).toNat) = regVal tape ((p_e - 2).toNat) := by
    simp only [regVal]
    refine regValA_congr_kind tape cfg₁.tape 1 ((p_e - 2).toNat) 0 ?_
    intro j hj
    have hc := Int.toNat_of_nonneg (show (0 : ℤ) ≤ p_e - 2 by omega)
    have hcast : (j : ℤ) < p_e - 2 := by
      have h2 : (j : ℤ) < (((p_e - 2).toNat : ℕ) : ℤ) := by exact_mod_cast hj
      rw [hc] at h2
      exact h2
    have hne : (1 : ℤ) + (j : ℤ) ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
  have hR1 : valFrom (ebits.drop (1 - 1)) (2 ^ (1 - 1)) ≤
      regVal cfg₁.tape ((p_e - 2).toNat) := by
    rw [hregEq]
    have h2 : (2 : ℤ) ^ (1 - 1) = 1 := by norm_num
    have h3 : ebits.drop (1 - 1) = ebits := by simp
    rw [h2, h3]
    exact hR0
  have hmar0₁ : cfg₁.tape p_e = Sym.data0 := by
    rw [htp₁]
    simp only [ite_true]
  have hbound0₁ : cfg₁.tape (p_e - 1) = Sym.boundary := by
    rw [htp₁]
    simp only [if_neg (by omega : p_e - 1 ≠ p_e)]
    exact hbound0
  have hboundL₁ : cfg₁.tape 0 = Sym.boundary := by
    rw [htp₁]
    simp only [if_neg (by omega : (0 : ℤ) ≠ p_e)]
    exact hboundL
  have htrail1 : ∀ i : ℤ, p_e + 1 ≤ i → i ≤ p_e + ((1 : ℕ) : ℤ) - 1 →
      cfg₁.tape i = Sym.consumed := by
    intro i h1 h2
    omega
  have hmarks1 : ∀ i : ℤ, 1 ≤ i → i ≤ ((1 : ℕ) : ℤ) - 1 → (cfg₁.tape i).2 = true := by
    intro i h1 h2
    omega
  have hflagF1 : ∀ i : ℤ, ((1 : ℕ) : ℤ) ≤ i → i ≤ p_e - 2 → (cfg₁.tape i).2 = false := by
    intro i h1 h2
    have hne : i ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hflag0 i h1 h2
  have hbwd1 : ∀ i : ℤ, 1 ≤ i → i ≤ p_e - 2 →
      (cfg₁.tape i).1 = SymKind.data0 ∨ (cfg₁.tape i).1 = SymKind.data1 := by
    intro i h1 h2
    have hne : i ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hbwd0 i h1 h2
  have hbit1 : ∀ i : ℕ, 1 ≤ i → i < ebits.length + 1 →
      (cfg₁.tape (p_e + (i : ℤ))).1 =
        (if ebits.getD (i - 1) false then SymKind.data1 else SymKind.data0) := by
    intro i h1 h2
    have hne : p_e + (i : ℤ) ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hbits i h1 h2
  have hend₁ : cfg₁.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      cfg₁.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (cfg₁.tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
    have hne : p_e + 1 + (ebits.length : ℤ) ≠ p_e := by omega
    rw [htp₁]
    simp only [if_neg hne]
    exact hend
  rcases segSrSel_aux_gen ebits p_e hn1 hnpe (ebits.length - 1) 1 rfl le_rfl hn1 cfg₁.tape
    hR1 hmar0₁ hbound0₁ hboundL₁ htrail1 hmarks1 hflagF1 hbwd1 hbit1 hend₁
    with ⟨π₂, cfg₂, hs₂, hcase₂, hC1₂, hC2₂, hEX₂⟩
  have e₁ : cfg₁ = SymConfig.mk 5 cfg₁.tape (p_e + ((1 : ℕ) : ℤ)) := by
    rw [show cfg₁ = SymConfig.mk cfg₁.state cfg₁.tape cfg₁.headPos from rfl]
    rw [hst₁, hhd₁]
    push_cast
    rfl
  refine ⟨π₁ ++ π₂, cfg₂, symSteps_append_concat π₁ π₂ hs₁ ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁]
    exact hs₂
  · have hB : (0 : ℤ) ≤ 2 * (ebits.length : ℤ) + 2 * p_e + 3 := by
      have : (0 : ℤ) ≤ (ebits.length : ℤ) := by positivity
      omega
    have hD : (((ebits.length - 1 : ℕ) : ℤ)) ≤ (ebits.length : ℤ) := by omega
    have hmul : ((ebits.length - 1 : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) ≤
        (ebits.length : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) :=
      mul_le_mul_of_nonneg_right hD hB
    have hUp : ∀ (L : ℤ), (π₂.length : ℤ) ≤ L → L ≤
        ((ebits.length - 1 : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
          (4 * p_e + 4 * (ebits.length : ℤ) + 12) →
        ((π₁ ++ π₂).length : ℤ) ≤ (ebits.length : ℤ) *
          (2 * (ebits.length : ℤ) + 2 * p_e + 3) + (4 * p_e + 4 * (ebits.length : ℤ) + 13) := by
      intro L h2 h3
      rw [List.length_append]
      push_cast
      rw [hlen₁]
      have h1 : (π₂.length : ℤ) ≤ (ebits.length : ℤ) *
          (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
          (4 * p_e + 4 * (ebits.length : ℤ) + 12) := by
        calc (π₂.length : ℤ)
            ≤ ((ebits.length - 1 : ℕ) : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
                (4 * p_e + 4 * (ebits.length : ℤ) + 12) := le_trans h2 h3
          _ ≤ (ebits.length : ℤ) * (2 * (ebits.length : ℤ) + 2 * p_e + 3) +
                (4 * p_e + 4 * (ebits.length : ℤ) + 12) := add_le_add hmul le_rfl
      omega
    rcases hcase₂ with ⟨hst, hhd, hl, hstamp, hagr₂, hbl₂, hnet₂, hfl, hkd, htk, hhk⟩ |
      ⟨hst, hhd, hl, hagr, hbl₂, hfl, hkd, htk, hhk⟩
    · left
      have hbl : cfg₂.tape 0 = tape 0 :=
        hbl₂.trans (by rw [htp₁]; simp only [if_neg (by omega : (0 : ℤ) ≠ p_e)])
      have hnet : regVal cfg₂.tape ((p_e - 2).toNat) ≥
          regVal tape ((p_e - 2).toNat) - valFrom ebits 1 := by
        have h3 : ebits.drop (1 - 1) = ebits := by simp
        have h4 : (2 : ℤ) ^ (1 - 1) = 1 := by norm_num
        have h2 := hnet₂
        rw [h3, h4] at h2
        rw [← hregEq]
        exact h2
      exact ⟨hst, hhd, hUp _ le_rfl hl, hstamp, hagr₂, hbl, hnet, hfl, hkd,
        (by rw [htk, htp₁]; simp only [if_neg (by omega : p_e + (ebits.length : ℤ) + 1 ≠ p_e)]),
        (by
          intro i hi
          rw [hhk i hi, htp₁]
          simp only [if_neg (by omega : i ≠ p_e)])⟩
    · right
      exact ⟨hst, hhd, hUp _ le_rfl hl, hagr,
        hbl₂.trans (by rw [htp₁]; simp only [if_neg (by omega : (0 : ℤ) ≠ p_e)]), hfl, hkd,
        (by rw [htk, htp₁]; simp only [if_neg (by omega : p_e + (ebits.length : ℤ) + 1 ≠ p_e)]),
        (by
          intro i hi
          rw [hhk i hi, htp₁]
          simp only [if_neg (by omega : i ≠ p_e)])⟩
  · -- C1：boundary ⟹ 22（经入口步 htp₁ 平移）
    intro hb
    have hb₁ : (cfg₁.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.boundary := by
      rw [htp₁]
      simp only [if_neg (show p_e + (ebits.length : ℤ) + 1 ≠ p_e by omega)]
      exact hb
    exact hC1₂ hb₁
  · -- C2：sel/nosel ⟹ 4（经入口步 htp₁ 平移）
    intro hsn
    have hsn₁ : (cfg₁.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.sel ∨
        (cfg₁.tape (p_e + (ebits.length : ℤ) + 1)).1 = SymKind.nosel := by
      rw [htp₁]
      simp only [if_neg (show p_e + (ebits.length : ℤ) + 1 ≠ p_e by omega)]
      exact hsn
    exact hC2₂ hsn₁
  · -- EX：净值精确式（入口不动 + 段精确）
    have h3 : ebits.drop (1 - 1) = ebits := by simp
    have h2 : (2 : ℤ) ^ (1 - 1) = 1 := by norm_num
    rw [h3, h2] at hEX₂
    rw [← hregEq]
    exact hEX₂


end Mp
