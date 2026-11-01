import Mp.LowerBound

/-!
# 两实例区分（论文 `lem:twin`）的机器无关核心

论文 `lem:twin`：取 `s_j = 2j`、`t = Σ s_j`（答案 YES），把第 `i` 个元素换成 `s_i + 1`
（答案 NO），两串只差第 `i` 个元素的编码，故任何正确机器必须读第 `i` 个元素。

本文件先落**奇偶性那一半**：全是偶数的元素表，任何位置选择的和仍为偶数——
于是"把一个元素换成奇数后目标仍为偶数"的实例**无解**。
-/

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Mp

/-- 全偶元素表的任一位置选择和为偶数。 -/
lemma selectedSum_even_of_all_even (l : List ℕ) (h : ∀ x ∈ l, Even x) (sel : List Bool) :
    Even (selectedSum l sel) := by
  induction l generalizing sel with
  | nil => simp [selectedSum]
  | cons a t ih =>
      cases sel with
      | nil => simp [selectedSum]
      | cons b s =>
          have ha : Even a := h a (by simp)
          have ht : ∀ x ∈ t, Even x := fun x hx => h x (by simp [hx])
          by_cases hb : b = true
          · simp only [selectedSum, List.zip_cons_cons, List.filter_cons, hb, if_true,
              List.map_cons, List.sum_cons]
            exact Even.add ha (ih ht s)
          · simp only [selectedSum, List.zip_cons_cons, List.filter_cons, hb, if_false]
            exact ih ht s

/-- 任何位置选择的和 ≤ 整表之和。 -/
lemma selectedSum_le_sum : ∀ (l : List ℕ) (sel : List Bool), selectedSum l sel ≤ l.sum
  | [], _ => by simp [selectedSum]
  | _ :: _, [] => by simp [selectedSum]
  | a :: t, b :: s => by
      have ih := selectedSum_le_sum t s
      cases b
      · simp [selectedSum] at ih ⊢
        omega
      · simp [selectedSum] at ih ⊢
        omega

/-- 长度匹配时的拼接分解：选中和按段相加。 -/
lemma selectedSum_append (a : List ℕ) :
    ∀ (s : List Bool), s.length = a.length → ∀ (b : List ℕ) (t : List Bool),
      selectedSum (a ++ b) (s ++ t) = selectedSum a s + selectedSum b t := by
  induction a with
  | nil =>
      intro s h b t
      cases s with
      | nil => simp [selectedSum]
      | cons _ _ => simp at h
  | cons x xs ih =>
      intro s h b t
      cases s with
      | nil => simp at h
      | cons y ys =>
          have h' : ys.length = xs.length := by simpa using h
          simp only [List.cons_append, selectedSum] at ⊢
          have ih' := ih ys h' b t
          cases y <;> simp [selectedSum] at ih' ⊢ <;> omega

/-- 全选（按位置）时，选择和等于整表之和。 -/
lemma selectedSum_replicate_true (l : List ℕ) :
    selectedSum l (List.replicate l.length true) = l.sum := by
  induction l with
  | nil => simp [selectedSum]
  | cons a t ih =>
      simp only [List.length_cons, List.replicate_succ]
      simpa [selectedSum] using ih

-- ============================================================================
-- §3 拆分与"无解"定理
-- ============================================================================

/-- 在指定位置拆分一个选择串。 -/
lemma exists_split (sel : List Bool) : ∀ (n : ℕ), n < sel.length →
    ∃ s₁ b s₂, sel = s₁ ++ b :: s₂ ∧ s₁.length = n := by
  induction sel with
  | nil => intro n hn; simp at hn
  | cons b rest ih =>
      intro n hn
      cases n with
      | zero => exact ⟨[], b, rest, rfl, rfl⟩
      | succ k =>
          have hk : k < rest.length := by simpa using hn
          obtain ⟨s₁, b', s₂, hsplit, hlen⟩ := ih k hk
          exact ⟨b :: s₁, b', s₂, by simp [hsplit], by simp [hlen]⟩

/-- “两实例区分”的无解一半：表中除 `o` 外全偶、`o` 为奇，其余元素之和小于偶目标 `t`，
    则不存在选择使其和等于 `t`。 -/
theorem twin_no_solution (l₁ l₂ : List ℕ) (o t : ℕ)
    (h₁ : ∀ x ∈ l₁, Even x) (h₂ : ∀ x ∈ l₂, Even x) (ho : Odd o)
    (hsum : l₁.sum + l₂.sum < t) (ht : Even t) :
    ¬ ∃ sel : List Bool, sel.length = (l₁ ++ o :: l₂).length ∧
        selectedSum (l₁ ++ o :: l₂) sel = t := by
  rintro ⟨sel, hlen, hsum_eq⟩
  have hn : l₁.length < sel.length := by
    simp [hlen]
  obtain ⟨s₁, b, s₂, rfl, hs₁⟩ := exists_split sel l₁.length hn
  have hsum₁ : Even (selectedSum l₁ s₁) := selectedSum_even_of_all_even l₁ h₁ s₁
  have hsum₂ : Even (selectedSum l₂ s₂) := selectedSum_even_of_all_even l₂ h₂ s₂
  have hle : selectedSum l₂ s₂ ≤ l₂.sum := selectedSum_le_sum l₂ s₂
  have hdecomp : selectedSum (l₁ ++ o :: l₂) (s₁ ++ b :: s₂)
      = selectedSum l₁ s₁ + (if b then o + selectedSum l₂ s₂ else selectedSum l₂ s₂) := by
    rw [selectedSum_append l₁ s₁ hs₁ (o :: l₂) (b :: s₂)]
    cases b <;> simp [selectedSum]
  rw [hdecomp] at hsum_eq
  cases b
  · -- 不选 o：和 ≤ l₁.sum + l₂.sum < t
    simp only [Bool.false_eq_true, if_false] at hsum_eq
    have h1 : selectedSum l₁ s₁ ≤ l₁.sum := selectedSum_le_sum l₁ s₁
    omega
  · -- 选 o：和 = 偶 + 奇 = 奇，与 t 偶矛盾
    simp only [if_true] at hsum_eq
    obtain ⟨u, hu⟩ := hsum₁
    obtain ⟨v, hv⟩ := hsum₂
    obtain ⟨w, hw⟩ := ho
    obtain ⟨z, hz⟩ := ht
    omega

/-- YES 侧：任何元素表，取全选即命中"目标和 = 元素之和"。 -/
theorem twin_subsetSumHolds (l : List ℕ) :
    subsetSumHolds { elements := l, target := l.sum } :=
  ⟨List.replicate l.length true, by simp, selectedSum_replicate_true l⟩

/-- NO 侧（`subsetSumHolds` 形式）：同 `twin_no_solution`，直接用于两实例区分。 -/
theorem twin_not_subsetSumHolds (l₁ l₂ : List ℕ) (o t : ℕ)
    (h₁ : ∀ x ∈ l₁, Even x) (h₂ : ∀ x ∈ l₂, Even x) (ho : Odd o)
    (hsum : l₁.sum + l₂.sum < t) (ht : Even t) :
    ¬ subsetSumHolds { elements := l₁ ++ o :: l₂, target := t } :=
  twin_no_solution l₁ l₂ o t h₁ h₂ ho hsum ht

/-- 等差表 `[2,4,…,2n]` 之和 `= n(n+1)`。 -/
lemma sum_range_even (n : ℕ) :
    ((List.range n).map (fun k => 2 * (k + 1))).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add]
      ring

/-- 具体 YES 实例：元素 `[2,4,…,2n]`，目标 `n(n+1)`（= 全选之和）。 -/
def twinYes (n : ℕ) : SubsetSumInstance :=
  { elements := (List.range n).map (fun k => 2 * (k + 1)), target := n * (n + 1) }

/-- 具体 YES 实例确实可满足。 -/
theorem twinYes_holds (n : ℕ) : subsetSumHolds (twinYes n) := by
  have h := twin_subsetSumHolds ((List.range n).map (fun k => 2 * (k + 1)))
  simpa [twinYes, sum_range_even n] using h

/-- `[0,2,4,…,2(m−1)]` 之和 `= m(m−1)`。 -/
lemma sum_range_two_mul (m : ℕ) :
    ((List.range m).map (fun k => 2 * k)).sum = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add]
      cases j with
      | zero => simp
      | succ j' => simp [Nat.succ_sub_one]; ring

/-- 移位等差表 `[2c, 2(c+1), …]` 之和 `= m·2c + m(m−1)`。 -/
lemma sum_range_shift (m c : ℕ) :
    ((List.range m).map (fun k => 2 * (c + k))).sum = m * (2 * c) + m * (m - 1) := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add]
      cases j with
      | zero => simp
      | succ j' => simp [Nat.succ_sub_one]; ring

/-- 具体 NO 实例：把 YES 实例的第 `i` 项换成 `2(i+1)+1`（奇数），目标不变。 -/
def twinNo (n i : ℕ) : SubsetSumInstance :=
  { elements := ((List.range i).map (fun k => 2 * (k + 1)))
      ++ (2 * (i + 1) + 1) :: ((List.range (n - (i + 1))).map (fun k => 2 * (i + 2 + k))),
    target := n * (n + 1) }

/-- 偶数的判据：`2k` 是偶数。 -/
lemma even_two_mul (k : ℕ) : Even (2 * k) := ⟨k, by ring⟩

/-- `n(n+1)` 是偶数（连续整数之积）。 -/
lemma even_mul_succ (n : ℕ) : Even (n * (n + 1)) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (2 * k + 1), by rw [hk]; ring⟩
  · exact ⟨(2 * k + 1) * (k + 1), by rw [hk]; ring⟩

/-- 具体 NO 实例确实无解（`i < n` 时）。 -/
theorem twinNo_not_holds (n i : ℕ) (hi : i < n) : ¬ subsetSumHolds (twinNo n i) := by
  have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
  have h₁ : ∀ x ∈ (List.range i).map (fun k => 2 * (k + 1)), Even x := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact even_two_mul (k + 1)
  have h₂ : ∀ x ∈ (List.range (n - (i + 1))).map (fun k => 2 * (i + 2 + k)), Even x := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact even_two_mul (i + 2 + k)
  have ho : Odd (2 * (i + 1) + 1) := ⟨i + 1, by ring⟩
  have ht : Even (n * (n + 1)) := even_mul_succ n
  have hsum : ((List.range i).map (fun k => 2 * (k + 1))).sum
      + ((List.range (n - (i + 1))).map (fun k => 2 * (i + 2 + k))).sum < n * (n + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n = i + 1 + m := ⟨n - (i + 1), by omega⟩
    subst hm
    rw [sum_range_even i]
    simp only [Nat.add_sub_cancel_left]
    rw [sum_range_shift m (i + 2)]
    rcases m with _ | m'
    · nlinarith [Nat.zero_le i]
    · simp only [Nat.succ_sub_one]
      nlinarith [Nat.zero_le i, Nat.zero_le m']
  exact twin_not_subsetSumHolds _ _ _ _ h₁ h₂ ho hsum ht

end Mp
