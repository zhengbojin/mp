import Mp.SubsetSumVerifierReverse11

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Mp

-- ============================================================
-- [C-3 续作] Reverse12：自 R11 迁出的迭代件
--   （用户令 2026-09-13：R11 有错部分外移本文件加速迭代；R11 留绿基座）
--   · five_step_84 : 84 支（回卷下行）——hq4e 强化为 q₄<E 后 hαE 直证
--   · five_step_4  : 4 支（轮首分派/rebase）——已解锁全绿（hαd + α₀″:=q₄+1 + hCNM′ 新形）；附 alphaPos_steps 链件（C3-α）
--   · C3-γ 段 S0   : segS0（初始 → 状态 3 @ #₁，≤ N+3）＋ 长度件 scanRightKeep_len /
--                    scanRight1_bits_len / scanRight2_bits_len / segS2_chosen（2 态选标，步数账）
--   · C3-δ 段 S1   : segS1（状态 3 @ #₁ → 状态 4 @ e₁，≤ 2N，#₁ 打标其余带保持）＋ 长度版
--                    scanLeftKeepPos_len / format_sweep_rec_from26_len / format_sweep_rec_len /
--                    format_sweep_correct_len（format_sweep 三件零封账副本）
-- ============================================================

/-- [C-3] 84 支分派：回卷下行步 ⇒ 包保持。 -/
lemma five_step_84 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (h84h : st.fromState = 84) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  by_cases h84 : st.fromState = 84
  · -- ===== [84] 支：回卷下行 =====
    have hres : st.result.nextState = 84 ∨ st.result.nextState = 85 :=
      state84_nexts st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 hno101
    have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
    have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
    have hne20 : st.result.nextState ≠ 20 := by intro h; rcases hres with h' | h' <;> omega
    have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
    have hne5 : st.result.nextState ≠ 5 := by intro h; rcases hres with h' | h' <;> omega
    have hne13 : st.result.nextState ≠ 13 := by intro h; rcases hres with h' | h' <;> omega
    have hne86 : st.result.nextState ≠ 86 := by intro h; rcases hres with h' | h' <;> omega
    have hne87 : st.result.nextState ≠ 87 := by intro h; rcases hres with h' | h' <;> omega
    have hf2 : st.fromState ≠ 2 := by intro h; omega
    have hf3 : st.fromState ≠ 3 := by intro h; omega
    have hf4 : st.fromState ≠ 4 := by intro h; omega
    have hf5 : st.fromState ≠ 5 := by intro h; omega
    have hf20 : st.fromState ≠ 20 := by intro h; omega
    have hf21 : st.fromState ≠ 21 := by intro h; omega
    have hf51 : st.fromState ≠ 51 := by intro h; omega
    have hpre : cfg₀.state ∈ symMainSet := by rw [← hs_from, h84]; decide
    have hpre84 : cfg₀.state = 84 := by rw [← hs_from]; exact h84
    have hpre84W : cfg₀.state ∈ symWorkSet := by rw [hpre84]; decide
    have hq4 : 2 ≤ S.q₄ := hinv.hq4ge.elim id
      (fun h0 => absurd ((hpre84.symm).trans h0) (by decide))
    have hblk' : SymBlk cfg₂ S.α S.p :=
      SymBlk.step_of_notFive21 hst hleg hno101 (fun h => hf5 h) (fun h => hf21 h) hinv.hblk
    have hC4' : SymLedger inst cfg₂ S.q₄ :=
      ledger_notTwoFour hst hleg hno101 (fun h => hf2 h) (fun h => hf4 h) hinv.hC4
    have hCNM' : SymClearedGone cfg₂ S.α₀ S.α := SymClearedGone.step_any hst hleg hno101 hinv.hCNM
    have hα₀' : S.α₀ ≤ S.q₄ + 1 := hinv.hα₀
    have hαp' : S.α ≤ S.p + 1 := hinv.hαp
    have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → S.α = S.p + 1 := by
      intro h
      rcases h with h | h
      · exact absurd (hstate.symm.trans h) hne4
      · exact absurd (hstate.symm.trans h) hne51
    have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
        ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
      intro h
      rcases h with h | h
      · exact absurd (hstate.symm.trans h) hne20
      · exact absurd (hstate.symm.trans h) hne21
    have h5pos' : cfg₂.state = 5 → S.α ≠ S.p + 1 → cfg₂.headPos = S.p + 1 :=
      fun h _ => absurd (hstate.symm.trans h) hne5
    have hA5' : cfg₂.state = 5 → S.p < cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne5
    have hwalk13' : cfg₂.state = 13 →
        SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ S.α ≤ S.s :=
      fun h => absurd (hstate.symm.trans h) hne13
    have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ S.q₄ - 1 :=
      fun h => h.elim (fun h86 => absurd (hstate.symm.trans h86) hne86)
        (fun h87 => absurd (hstate.symm.trans h87) hne87)
    have hnext1' : cfg₂.state = 5 → S.α = S.p + 1 → cfg₂.headPos = S.q₄ + 1 :=
      fun h _ => absurd (hstate.symm.trans h) hne5
    have hq4ge' : 2 ≤ S.q₄ ∨ cfg₂.state = 4 :=
      Or.inl hq4
    have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape S.p).1 = SymKind.consumed := by
      intro _
      by_cases hph : cfg₀.headPos = S.p
      · have hrc : st.readSym.1 = SymKind.consumed := by
          rw [hs_read, hph]
          exact hinv.hpc hpre84W
        have hw := state84_c_write st.readSym.2 ⟨st.fromState, hlt⟩ h84 st.result
          (by simpa [hrc] using hm)
        rw [← hph, hs_cfg, symStepConfig_tape_headPos]
        exact hw
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.p ≠ cfg₀.headPos by omega)]
        exact hinv.hpc hpre84W
    have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
        z = 0 ∨ z = S.q₄ - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) :=
      hbnd_frame hst hleg hno101 (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h)
        (fun h => absurd (h84h.symm.trans (hs_from.trans h)) (by decide)) hinv.hbnd
    have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (S.q₄ - 1)).1 = SymKind.boundary := by
      intro _
      by_cases hh : cfg₀.headPos = S.q₄ - 1
      · have hread : st.readSym.1 = SymKind.boundary := by
          rw [hs_read, hh]
          exact hinv.hSharp hpre
        have hid := hashRead_id st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (fun h => hf51 h) (fun h => hf3 h) (fun h => hf20 h) hread
        rw [← hh, hs_cfg, symStepConfig_tape_headPos]
        exact (congrArg Prod.fst hid).trans hread
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show S.q₄ - 1 ≠ cfg₀.headPos by omega)]
        exact hinv.hSharp hpre
    have hαqU' : cfg₂.state ∈ symMainSet → S.α = S.q₄ + 1 := fun _ => hinv.hαqU hpre
    have h84le' : cfg₂.state = 84 → S.q₄ - 1 ≤ cfg₂.headPos := by
      intro h844
      have h44 : st.result.nextState = 84 := hstate.symm.trans h844
      have hmvL' := state84_L st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 h44
      have h1 : S.q₄ - 1 ≤ cfg₀.headPos := hinv.h84le hpre84
      have hne' : cfg₀.headPos ≠ S.q₄ - 1 := by
        intro he
        have hrd : st.readSym.1 = SymKind.boundary := by
          rw [hs_read, he]
          exact hinv.hSharp hpre
        exact (state84_no_hash st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 h44) hrd
      have h2 : S.q₄ ≤ cfg₀.headPos := by omega
      rw [hhead, hmvL', show Dir.L.toInt = (-1 : ℤ) from rfl]
      omega
    have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ S.p := by
      intro h844
      have h44 : st.result.nextState = 84 := hstate.symm.trans h844
      have hmvL' := state84_L st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 h44
      have h12 : cfg₀.headPos ≤ S.p := hinv.h84le2 hpre84
      rw [hhead, hmvL', show Dir.L.toInt = (-1 : ℤ) from rfl]
      omega
    have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ S.q₄ - 2 := by
      intro h855
      have h85r : st.result.nextState = 85 := hstate.symm.trans h855
      have hHL := state84_HL st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 h85r
      have h1 : S.q₄ - 1 ≤ cfg₀.headPos := hinv.h84le hpre84
      have h2 : cfg₀.headPos ≤ S.p := hinv.h84le2 hpre84
      have h3 : cfg₀.headPos = S.q₄ - 1 := by
        rcases hinv.hbnd cfg₀.headPos (by rw [← hs_read]; exact hHL.1) with h0 | hq | hE | h4e
        · omega
        · exact hq
        · -- E 臂：#₁ 位与走廊几何矛盾（α ≤ E ≤ p ⟹ #₁ 格应为 c）
          exfalso
          have hEp : symEndPos inst ≤ S.p := by omega
          have hαE : S.α ≤ symEndPos inst := by
            have hαq := hinv.hαqU (by rw [hpre84]; decide)
            have hq4e := hinv.hq4e
            omega
          have hcons : (cfg₀.tape (symEndPos inst)).1 = SymKind.consumed :=
            (hinv.hblk (symEndPos inst)).mpr ⟨hαE, hEp⟩
          have hbnd : (cfg₀.tape (symEndPos inst)).1 = SymKind.boundary := by
            rw [← hE, ← hs_read]
            exact hHL.1
          rw [hcons] at hbnd
          exact absurd hbnd (by decide)
        · have := h4e.2; omega
      have hmvL' := hHL.2
      rw [hhead, hmvL', show Dir.L.toInt = (-1 : ℤ) from rfl]
      omega
    have hgap' : SymGapNoAlpha inst S.q₄ cfg₂ := by
      have hmvL : st.result.moveDir = Dir.L := by
        rcases hres with h' | h'
        · exact state84_L st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 h'
        · exact (state84_HL st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm h84 h').2
      have hle : cfg₂.headPos ≤ cfg₀.headPos := by
        rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
        omega
      exact SymGapNoAlpha.step_shrink hst hle hinv.hgap
    have h51p' : cfg₂.state = 51 → S.p ≤ cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne51
    have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
        (cfg₂.tape (S.q₄ - 1)).1 = SymKind.data0 := by
      intro h
      rcases h with h | h | h
      · exact absurd (hstate.symm.trans h) hne4
      · exact absurd (hstate.symm.trans h) hne21
      · exact absurd (hstate.symm.trans h) hne51
    have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
      fun h => absurd (hstate.symm.trans h) hne4
    have h51q4' : cfg₂.state = 51 → S.q₄ ≤ cfg₂.headPos :=
      fun h => absurd (hstate.symm.trans h) hne51
    have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
      intro h
      rcases h with h86 | h87
      · exact absurd (hstate.symm.trans h86) hne86
      · exact absurd (hstate.symm.trans h87) hne87
    have h20h' : cfg₂.state = 20 → cfg₂.headPos = S.q₄ - 1 :=
      fun h => absurd (hstate.symm.trans h) hne20
    have h5pc' : cfg₂.state = 5 → (cfg₂.tape S.p).1 ≠ SymKind.boundary :=
      fun h => absurd (hstate.symm.trans h) hne5
    exact ⟨{ α := S.α, p := S.p, q₄ := S.q₄, s := S.s, α₀ := S.α₀ },
      ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
        hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d', h4head', h51q4', h86ge', h20h', h5pc', hinv.hq4e⟩,
      fun hf => by rw [symFive, h84] at hf; exact absurd hf (by decide)⟩
  · exact absurd h84h h84

-- ==================== five_step_4（2026-09-13 解锁 · 全绿） ====================
-- 解锁三件：① hαd 参数（α 格恒域，装配期链件 alphaPos_steps 供给）；
-- ② rebase α₀″ := S.q₄+1（清扫区下界随轮推进，消 z≤q₄ 死角）；
-- ③ hCNM′ 新形 [q₄+1, 头₀+1)（hgap+ledger 双杀 + 盖章格直证）。全文件 0 error。
-- ==========================================================================

/-- [C-3] 4 支分派：轮首分派（读元素位标记）⇒ rebase（α,p,q₄ := 头+1,头,头）⇒ 包保持。
    sel → 5（首火准备，写 d0 + R）；nosel → 20（写 d0 + L）。
    hbnd″：旧锚臂由 h20d 杀（4 态旧锚恒 d0）、戳格经 pre 的 4∧头−1 臂；hq4e 由「标记⟹α 位置⟹末界」供。 -/
lemma five_step_4 {inst : SubsetSumInstance} {cfg₀ cfg₂ : SymConfig} {st : SymStep}
    {S : SymFiveSt}
    (hst : SymSteps VerifierSym.transition cfg₀ [st] cfg₂)
    (hleg : cfg₀.state ∈ VerifierSym.legalStates)
    (hno101 : st.result.nextState ≠ 101)
    (hinv : SymFiveInv inst cfg₀ S)
    (hαd : ∀ z : ℤ, (cfg₀.tape z).1 = SymKind.alpha → SymAlphaPos inst z)
    (h4h : st.fromState = 4) :
    ∃ S' : SymFiveSt, SymFiveInv inst cfg₂ S' ∧
      (symFive st = true → S'.p = cfg₀.headPos) := by
  obtain ⟨hs_from, hs_read, hs_mem, hs_cfg⟩ := symSteps_singleton_facts hst
  have hlt : st.fromState < 102 := legalStates_lt_102 st.fromState (by rw [hs_from]; exact hleg)
  have hm : st.result ∈ VerifierSym.transition ((st.fromState : ℕ), st.readSym.1, st.readSym.2) := by
    simpa [← hs_from, ← hs_read] using hs_mem
  have hstate : cfg₂.state = st.result.nextState := by rw [hs_cfg]; rfl
  have hhead : cfg₂.headPos = cfg₀.headPos + st.result.moveDir.toInt := by rw [hs_cfg]; rfl
  have hpre4 : cfg₀.state = 4 := hs_from ▸ h4h
  have h4f := state4_readMark_write_d0 st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
    (by simpa using h4h) hno101
  have hread : st.readSym.1 = SymKind.sel ∨ st.readSym.1 = SymKind.nosel := h4f.1
  have hwr : st.result.writeSym.1 = SymKind.data0 := h4f.2
  have hres : st.result.nextState = 5 ∨ st.result.nextState = 20 := by
    rcases hread with hs | hn
    · exact Or.inl (state4_sel_next st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (by simpa using h4h) hs)
    · exact Or.inr (state4_nosel_next st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (by simpa using h4h) hn)
  have hne4 : st.result.nextState ≠ 4 := by intro h; rcases hres with h' | h' <;> omega
  have hne13 : st.result.nextState ≠ 13 := by intro h; rcases hres with h' | h' <;> omega
  have hne21 : st.result.nextState ≠ 21 := by intro h; rcases hres with h' | h' <;> omega
  have hne51 : st.result.nextState ≠ 51 := by intro h; rcases hres with h' | h' <;> omega
  have hne84 : st.result.nextState ≠ 84 := by intro h; rcases hres with h' | h' <;> omega
  have hne85 : st.result.nextState ≠ 85 := by intro h; rcases hres with h' | h' <;> omega
  have hne86 : st.result.nextState ≠ 86 := by intro h; rcases hres with h' | h' <;> omega
  have hne87 : st.result.nextState ≠ 87 := by intro h; rcases hres with h' | h' <;> omega
  have hf2 : st.fromState ≠ 2 := by intro h; omega
  have hf3 : st.fromState ≠ 3 := by intro h; omega
  have hf20 : st.fromState ≠ 20 := by intro h; omega
  have hf21 : st.fromState ≠ 21 := by intro h; omega
  have hf51 : st.fromState ≠ 51 := by intro h; omega
  -- 4 态读标记：头格为标记 ⇒ 账本给出 q₄ < 头₁（rebase 的全部合法性之源）
  have hkind : (cfg₀.tape cfg₀.headPos).1 = SymKind.sel ∨
      (cfg₀.tape cfg₀.headPos).1 = SymKind.nosel := by
    rw [← hs_read]; exact hread
  have hM : SymMarked cfg₀ cfg₀.headPos := hkind
  have hq4head : S.q₄ < cfg₀.headPos := ((hinv.hC4 cfg₀.headPos).mp hM).2
  -- 4 态块为空形：hempQ-pre（α = p+1）
  have hemp : S.α = S.p + 1 := hinv.hempQ (Or.inl hpre4)
  -- 目标 S″ 共通件（sel/nosel 同一 rebase，19 件共通 + 11 件分派）
  have hblk' : SymBlk cfg₂ (cfg₀.headPos + 1) cfg₀.headPos := by
    apply SymBlk.of_empty
    intro i hc
    by_cases hi : i = cfg₀.headPos
    · rw [hi, hs_cfg, symStepConfig_tape_headPos, hwr] at hc
      exact absurd hc (by decide)
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hi] at hc
      have hb := (hinv.hblk i).mp hc
      omega
  have hC4' : SymLedger inst cfg₂ cfg₀.headPos :=
    ledger_four hst hleg hno101 h4h hinv.hC4 hinv.hgap
  have hCNM' : SymClearedGone cfg₂ (S.q₄ + 1) (cfg₀.headPos + 1) := by
    intro z h1 h2
    by_cases hz : z = cfg₀.headPos
    · subst hz
      rw [Sym.notMarked, hs_cfg, symStepConfig_tape_headPos, hwr]
      exact ⟨by decide, by decide, by decide⟩
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz]
      have hzlt : z < cfg₀.headPos := by omega
      have hq : S.q₄ < z := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro hα
        exact (hinv.hgap z hq hzlt) (hαd z hα)
      · intro hs
        exact (hinv.hgap z hq hzlt) ((hinv.hC4 z).mp (Or.inl hs)).1
      · intro hn
        exact (hinv.hgap z hq hzlt) ((hinv.hC4 z).mp (Or.inr hn)).1
  have hα₀' : S.q₄ + 1 ≤ cfg₀.headPos + 1 := by omega
  have hgap' : SymGapNoAlpha inst cfg₀.headPos cfg₂ := by
    intro z h1 h2
    rcases hres with h5r | h20r
    · have hmvR : st.result.moveDir = Dir.R :=
        state4_sel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (by simpa using h4h) h5r
      have hh2 : cfg₂.headPos = cfg₀.headPos + 1 := by
        rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
      omega
    · have hnsl : st.readSym.1 = SymKind.nosel := by
        rcases hread with hs | hn
        · have h5' := state4_sel_next st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
            (by simpa using h4h) hs
          omega
        · exact hn
      have hmvL : st.result.moveDir = Dir.L :=
        state4_nosel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (by simpa using h4h) hnsl
      have hh2 : cfg₂.headPos = cfg₀.headPos - 1 := by
        rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
        ring
      omega
  have hαp' : cfg₀.headPos + 1 ≤ cfg₀.headPos + 1 := le_refl _
  have hSharp' : cfg₂.state ∈ symMainSet → (cfg₂.tape (cfg₀.headPos - 1)).1 = SymKind.boundary := by
    intro _
    rw [hs_cfg, symStepConfig_tape_of_ne _ _ (show cfg₀.headPos - 1 ≠ cfg₀.headPos by omega)]
    exact hinv.h4head hpre4
  have hq4ge' : 2 ≤ cfg₀.headPos ∨ cfg₂.state = 4 := by
    left
    rcases ((hinv.hC4 cfg₀.headPos).mp hM).1 with ⟨o, _, hz⟩
    rw [hz]
    have h2 : 2 ≤ encPrefixLen inst + o := by rw [encPrefixLen]; omega
    exact_mod_cast h2
  have hq4e' : cfg₀.headPos < symEndPos inst :=
    symAlphaPos_lt_end ((hinv.hC4 cfg₀.headPos).mp hM).1
  have hbnd' : ∀ z : ℤ, (cfg₂.tape z).1 = SymKind.boundary →
      z = 0 ∨ z = cfg₀.headPos - 1 ∨ z = symEndPos inst ∨ (cfg₂.state = 4 ∧ z = cfg₂.headPos - 1) := by
    intro z hz
    by_cases hz1 : z = cfg₀.headPos
    · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwr] at hz
      exact absurd hz (by decide)
    · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hz
      rcases hinv.hbnd z hz with h0 | hq | hE | ⟨h4e1, h4e2⟩
      · exact Or.inl h0
      · exfalso
        have hd0 := hinv.h20d (Or.inl hpre4)
        rw [← hq] at hd0
        exact absurd (hd0.symm.trans hz) (by decide)
      · exact Or.inr (Or.inr (Or.inl hE))
      · exact Or.inr (Or.inl h4e2)
  -- 分派件（sel：h5pos/hA5/hαqU/hnext1 真形；nosel：hB4/h20h 真形）
  have hempQ' : (cfg₂.state = 4 ∨ cfg₂.state = 51) → cfg₀.headPos + 1 = cfg₀.headPos + 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne51
  have hB4' : (cfg₂.state = 20 ∨ cfg₂.state = 21) →
      ∀ z : ℤ, z < cfg₂.headPos → (cfg₂.tape z).1 = SymKind.consumed → False := by
    intro h z hz hc
    rcases hres with h5r | h20r
    · rcases h with h20 | h21
      · exact absurd (hstate.symm.trans h20) (by rw [h5r]; decide)
      · exact absurd (hstate.symm.trans h21) (by rw [h5r]; decide)
    · have hnsl : st.readSym.1 = SymKind.nosel := by
        rcases hread with hs | hn
        · have h5' := state4_sel_next st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
            (by simpa using h4h) hs
          omega
        · exact hn
      have hmvL : st.result.moveDir = Dir.L :=
        state4_nosel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (by simpa using h4h) hnsl
      have hh2 : cfg₂.headPos = cfg₀.headPos - 1 := by
        rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
        ring
      rw [hh2] at hz
      by_cases hz1 : z = cfg₀.headPos
      · rw [hz1, hs_cfg, symStepConfig_tape_headPos, hwr] at hc
        exact absurd hc (by decide)
      · rw [hs_cfg, symStepConfig_tape_of_ne _ _ hz1] at hc
        have hb := (hinv.hblk z).mp hc
        omega
  have h5pos' : cfg₂.state = 5 → cfg₀.headPos + 1 ≠ cfg₀.headPos + 1 →
      cfg₂.headPos = cfg₀.headPos + 1 :=
    fun _ hh => absurd rfl hh
  have hA5' : cfg₂.state = 5 → cfg₀.headPos < cfg₂.headPos := by
    intro h
    have h5r : st.result.nextState = 5 := hstate.symm.trans h
    have hmvR : st.result.moveDir = Dir.R :=
      state4_sel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (by simpa using h4h) h5r
    rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
    omega
  have hwalk13' : cfg₂.state = 13 →
      SymWalkConsumed cfg₂ S.s ∧ S.s < cfg₂.headPos ∧ cfg₀.headPos + 1 ≤ S.s :=
    fun h => absurd (hstate.symm.trans h) hne13
  have h86le' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → cfg₂.headPos ≤ cfg₀.headPos - 1 := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have hαqU' : cfg₂.state ∈ symMainSet → cfg₀.headPos + 1 = cfg₀.headPos + 1 := fun _ => rfl
  have hnext1' : cfg₂.state = 5 → cfg₀.headPos + 1 = cfg₀.headPos + 1 →
      cfg₂.headPos = cfg₀.headPos + 1 := by
    intro h _
    have h5r : st.result.nextState = 5 := hstate.symm.trans h
    have hmvR : st.result.moveDir = Dir.R :=
      state4_sel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (by simpa using h4h) h5r
    rw [hhead, hmvR, show Dir.R.toInt = (1 : ℤ) from rfl]
  have hpc' : cfg₂.state ∈ symWorkSet → (cfg₂.tape cfg₀.headPos).1 = SymKind.consumed :=
    fun h => absurd h (by rcases hres with h' | h' <;> (rw [hstate, h']; decide))
  have h84le' : cfg₂.state = 84 → cfg₀.headPos - 1 ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h84le2' : cfg₂.state = 84 → cfg₂.headPos ≤ cfg₀.headPos :=
    fun h => absurd (hstate.symm.trans h) hne84
  have h85le' : cfg₂.state = 85 → cfg₂.headPos ≤ cfg₀.headPos - 2 :=
    fun h => absurd (hstate.symm.trans h) hne85
  have h51p' : cfg₂.state = 51 → cfg₀.headPos ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h20d' : (cfg₂.state = 4 ∨ cfg₂.state = 21 ∨ cfg₂.state = 51) →
      (cfg₂.tape (cfg₀.headPos - 1)).1 = SymKind.data0 := by
    intro h
    rcases h with h | h | h
    · exact absurd (hstate.symm.trans h) hne4
    · exact absurd (hstate.symm.trans h) hne21
    · exact absurd (hstate.symm.trans h) hne51
  have h4head' : cfg₂.state = 4 → (cfg₂.tape (cfg₂.headPos - 1)).1 = SymKind.boundary :=
    fun h => absurd (hstate.symm.trans h) hne4
  have h51q4' : cfg₂.state = 51 → cfg₀.headPos ≤ cfg₂.headPos :=
    fun h => absurd (hstate.symm.trans h) hne51
  have h86ge' : (cfg₂.state = 86 ∨ cfg₂.state = 87) → 1 ≤ cfg₂.headPos := by
    intro h
    rcases h with h | h
    · exact absurd (hstate.symm.trans h) hne86
    · exact absurd (hstate.symm.trans h) hne87
  have h20h' : cfg₂.state = 20 → cfg₂.headPos = cfg₀.headPos - 1 := by
    intro h
    have hnsl : st.readSym.1 = SymKind.nosel := by
      rcases hread with hs | hn
      · have h5' := state4_sel_next st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
          (by simpa using h4h) hs
        have h20' : st.result.nextState = 20 := hstate.symm.trans h
        omega
      · exact hn
    have hmvL : st.result.moveDir = Dir.L :=
      state4_nosel_move st.readSym.1 st.readSym.2 ⟨st.fromState, hlt⟩ st.result hm
        (by simpa using h4h) hnsl
    rw [hhead, hmvL, show Dir.L.toInt = (-1 : ℤ) from rfl]
    ring
  have h5pc' : cfg₂.state = 5 → (cfg₂.tape cfg₀.headPos).1 ≠ SymKind.boundary := by
    intro _
    rw [hs_cfg, symStepConfig_tape_headPos, hwr]
    exact by decide
  exact ⟨{ α := cfg₀.headPos + 1, p := cfg₀.headPos, q₄ := cfg₀.headPos, s := S.s, α₀ := S.q₄ + 1 },
    ⟨hblk', hC4', hCNM', hα₀', hgap', hαp', hempQ', hB4', h5pos', hA5', hwalk13',
      hSharp', h86le', hαqU', hnext1', hq4ge', hbnd', hpc', h84le', h84le2', h85le', h51p', h20d',
      h4head', h51q4', h86ge', h20h', h5pc', hq4e'⟩,
    fun _hf => rfl⟩

/-- [C3-α] α 格恒域成链主件：沿 SymSteps 逐锤 kind-α ⟹ SymAlphaPos。
    底座 = symInitialConfig_alpha_pos（初始包），逐锤 = alphaPos_step。
    供给点：装配期在 five_step_4 调用处对前缀运行成链（hαd 参数）。 -/
lemma alphaPos_steps {inst : SubsetSumInstance} {cfg₀ cfg : SymConfig} {π : List SymStep}
    (h : SymSteps VerifierSym.transition cfg₀ π cfg)
    (hleg : ∀ s ∈ π, s.fromState ∈ VerifierSym.legalStates)
    (hno101 : ∀ s ∈ π, s.result.nextState ≠ 101)
    (h0 : ∀ z : ℤ, (cfg₀.tape z).1 = SymKind.alpha → SymAlphaPos inst z) :
    ∀ z : ℤ, (cfg.tape z).1 = SymKind.alpha → SymAlphaPos inst z := by
  revert hleg hno101 h0
  induction h with
  | nil =>
      intro _ _ h0
      exact h0
  | cons π₀ step cfg₁ hprev hfrom hread htrans ih =>
      intro hleg hno101 h0
      have hleg₁ : cfg₁.state ∈ VerifierSym.legalStates := by
        have h' := hleg step (by simp)
        simpa [hfrom] using h'
      have h101₁ : step.result.nextState ≠ 101 := hno101 step (by simp)
      have hα₁ : ∀ z : ℤ, (cfg₁.tape z).1 = SymKind.alpha → SymAlphaPos inst z :=
        ih (fun s hs => hleg s (by simp [hs]))
           (fun s hs => hno101 s (by simp [hs]))
           h0
      have hst : SymSteps VerifierSym.transition cfg₁ [step]
          (symStepConfig cfg₁ step.result) :=
        SymSteps.cons [] step cfg₁ SymSteps.nil hfrom hread htrans
      exact alphaPos_step hst hleg₁ h101₁ hα₁

-- ==================== C3-γ：段 S0（相位 0：0→1→2→3） ====================

/-- [C3-γ] 通用右扫 + 步数（scanRightKeep 的长度版）：状态 q 从 p 右扫 n 格
    （每格写回自身、右移），恰 n 步，带保持。 -/
lemma scanRightKeep_len (q : ℕ) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hkeep : ∀ i : ℤ, p ≤ i ∧ i < p + (n : ℤ) →
      { nextState := q, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (q, tape i)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q ∧ cfg'.headPos = p + (n : ℤ) ∧ cfg'.tape = tape ∧ π.length = n := by
  induction n generalizing p tape with
  | zero => exact ⟨[], SymConfig.mk q tape p, SymSteps.nil, rfl, by simp, rfl, rfl⟩
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := tape p, moveDir := Dir.R }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) :=
        hkeep p (by constructor <;> omega)
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg₁ : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        funext i
        by_cases h : i = p <;> simp [h]
      have hkeep₁ : ∀ i : ℤ, p + 1 ≤ i ∧ i < p + 1 + (n : ℤ) →
          { nextState := q, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (q, tape i) := by
        intro i h
        exact hkeep i (by constructor <;> omega)
      rcases ih (p + 1) tape hkeep₁ with ⟨π', cfg', hπ', hs', hhead', htape', hlen'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, htape', ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p) (SymConfig.mk q tape (p + 1)) cfg'
          [step] π' (hcfg₁ ▸ hstep) hπ'
      · rw [hhead']; omega
      · simp [hlen']

/-- [C3-γ] 状态 1 跨位段右扫（长度版）：bits 全为 data0/1（种类），右端为 #。
    从 mk 1 tape p 出发恰 |bits|+1 步到状态 2（头越过 # 右侧一格），带保持。 -/
lemma scanRight1_bits_len (bits : List Sym) (p : ℤ) (tape : ℤ → Sym)
    (hbits : ∀ s ∈ bits, s.1 = SymKind.data0 ∨ s.1 = SymKind.data1)
    (htape : tapeAgrees tape p bits)
    (hbound : tape (p + (bits.length : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 1 tape p) π cfg' ∧
      cfg'.state = 2 ∧ cfg'.headPos = p + (bits.length : ℤ) + 1 ∧
      π.length = bits.length + 1 ∧ cfg'.tape = tape := by
  have hkeep : ∀ i : ℤ, p ≤ i ∧ i < p + (bits.length : ℤ) →
      { nextState := 1, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (1, tape i) := by
    intro i hi
    have ioff : ∃ io : ℕ, (io : ℤ) = i - p := by
      refine ⟨(i - p).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega)
    rcases ioff with ⟨io, hio⟩
    have hio_lt : io < bits.length := by omega
    have ht : tape (p + (io : ℤ)) = bits[io] := htape io hio_lt
    have hidx : p + (io : ℤ) = i := by omega
    rw [← hidx, ht]
    exact trans1_keep bits[io] (hbits bits[io] (List.getElem_mem hio_lt))
  rcases scanRightKeep_len 1 bits.length p tape hkeep with
    ⟨π₁, cfg₁, hπ₁, hs₁, hhead₁, htape₁, hlen₁⟩
  have hcfg₁ : cfg₁ = SymConfig.mk 1 tape (p + (bits.length : ℤ)) := by
    rw [← hs₁, ← htape₁, ← hhead₁]
  let r : SymTransResult := { nextState := 2, writeSym := Sym.boundary, moveDir := Dir.R }
  let step : SymStep := { fromState := 1, readSym := Sym.boundary, result := r }
  have htrans : step.result ∈ VerifierSym.transition (1, tape (p + (bits.length : ℤ))) := by
    rw [hbound]
    decide
  have hstep : SymSteps VerifierSym.transition cfg₁ [step]
      (symStepConfig cfg₁ step.result) := by
    refine SymSteps.cons [] step cfg₁ SymSteps.nil ?_ ?_ ?_
    · simpa [step] using hs₁.symm
    · change Sym.boundary = cfg₁.tape cfg₁.headPos
      rw [hcfg₁]
      simp [SymConfig.mk, hbound]
    · change step.result ∈ VerifierSym.transition (cfg₁.state, cfg₁.tape cfg₁.headPos)
      rw [hcfg₁]
      simp [SymConfig.mk]
      exact htrans
  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 1 tape p) (π₁ ++ [step])
      (symStepConfig cfg₁ step.result) :=
    SymSteps_trans VerifierSym.transition (SymConfig.mk 1 tape p) cfg₁
      (symStepConfig cfg₁ step.result) π₁ [step] hπ₁ hstep
  refine ⟨π₁ ++ [step], symStepConfig cfg₁ step.result, htotal, ?_, ?_, ?_, ?_⟩
  · rw [show symStepConfig cfg₁ step.result =
        symStepConfig (SymConfig.mk 1 tape (p + (bits.length : ℤ))) step.result by rw [hcfg₁]]
    dsimp [step, r]
    simp [symStepConfig, SymConfig.mk]
  · rw [show symStepConfig cfg₁ step.result =
        symStepConfig (SymConfig.mk 1 tape (p + (bits.length : ℤ))) step.result by rw [hcfg₁]]
    dsimp [step, r]
    simp [symStepConfig, SymConfig.mk, Dir.toInt]
  · simp [hlen₁]
  · rw [show symStepConfig cfg₁ step.result =
        symStepConfig (SymConfig.mk 1 tape (p + (bits.length : ℤ))) step.result by rw [hcfg₁]]
    dsimp [step, r]
    simp only [symStepConfig, SymConfig.mk]
    funext i
    by_cases h : i = p + (bits.length : ℤ)
    · simp [h, hbound]
    · simp [h]

/-- [C3-γ] 状态 2 跨单个元素的位段右扫（长度版）：值位保持、恰 |bits| 步，停在 #₁ 前。 -/
lemma scanRight2_bits_len (v : ℕ) (q : ℤ) (tape : ℤ → Sym)
    (hbits : tapeAgrees tape (q + 1) (encodeBitsSymNative v)) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 2 tape (q + 1)) π cfg' ∧
      cfg'.state = 2 ∧ cfg'.headPos = q + 1 + ((encodeBitsSymNative v).length : ℤ) ∧
      cfg'.tape = tape ∧ π.length = (encodeBitsSymNative v).length := by
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
  exact scanRightKeep_len 2 (encodeBitsSymNative v).length (q + 1) tape hkeep

-- ==================== C3-γ：段 S2 核（2 态选标走带·长度版） ====================

/-- [C3-γ] 状态 2 带选择的右扫（长度版）：逐元素消费 sel，α 按 sel[i] 写成 sel/nosel，
    值位保持，扫到 #₁ → 状态 3。改写后元素区等于物理编码 `encodeElementsSymWithSel`。
    步数账：|π| = |encodeElementsSym elems| + 1。 -/
lemma segS2_chosen (elems : List ℕ) (sel : List Bool) (p : ℤ) (tape : ℤ → Sym)
    (hsel_len : sel.length = elems.length)
    (helems : tapeAgrees tape p (encodeElementsSym elems))
    (hbound : tape (p + (encodeElementsSym elems).length) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 2 tape p) π cfg' ∧
      cfg'.state = 3 ∧
      cfg'.headPos = p + (encodeElementsSym elems).length ∧
      tapeAgrees cfg'.tape p (encodeElementsSymWithSel elems sel) ∧
      (∀ i : ℤ, p ≤ i ∧ i < p + (encodeElementsSym elems).length → (cfg'.tape i).1 ≠ SymKind.boundary) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      cfg'.tape (p + (encodeElementsSym elems).length) = Sym.boundary ∧
      π.length = (encodeElementsSym elems).length + 1 := by
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
    refine ⟨[step], symStepConfig (SymConfig.mk 2 tape p) step.result, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simp [encodeElementsSym]

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
              rcases scanRight2_bits_len v p tape1 hbits1 with ⟨π2, cfg2, hπ2, hs2, hhead2, htape2, hlen2⟩
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
              refine ⟨[step1] ++ π2 ++ [step3], cfg3, htotal, rfl, ?_, hfinal, ?_, ?_, ?_, ?_⟩
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
              · have hlen_e : (encodeElementsSym [v]).length = (encodeBitsSymNative v).length + 1 := by
                  simp [encodeElementsSym]
                rw [List.length_append, List.length_append, hlen2, hlen_e]
                simp only [List.length_cons, List.length_nil]
                omega
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
              rcases scanRight2_bits_len v p tape1 hbits1 with ⟨π2, cfg2, hπ2, hs2, hhead2, htape2, hlen2⟩
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
                with ⟨π', cfg', hπ', hs', hhead', htape', hnb', hleft', hbound_keep', hlen'⟩
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
              refine ⟨[step1] ++ π2 ++ π', cfg', htotal, hs', ?_, hfinal, ?_, ?_, ?_, ?_⟩
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
              · rw [List.length_append, List.length_append, hlen2, hlen']
                have hlen_e : (encodeElementsSym (v :: rest)).length =
                    (encodeBitsSymNative v).length + 1 + (encodeElementsSym rest).length := by
                  simp [encodeElementsSym, hrest]
                  omega
                rw [hlen_e]
                simp only [List.length_cons, List.length_nil]
                omega

/-- [C3-γ] 段 S0（相位 0：0→1→2→3）：初始配置 → 状态 3 @ #₁（恰 N 步，≤ N+3）。
    target 区保持、#₀ 原位、元素区按 sel 标记（WithSel）、#₁ 原样未标。 -/
lemma segS0 (inst : SubsetSumInstance) (sel : List Bool)
    (hsel_len : sel.length = inst.elements.length) :
    ∃ π cfg', SymSteps VerifierSym.transition (symInitialConfig (encodeInstanceSym inst)) π cfg' ∧
      cfg'.state = 3 ∧
      cfg'.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ) ∧
      π.length ≤ (encodeInstanceSym inst).length + 3 ∧
      cfg'.tape 0 = Sym.boundary ∧
      tapeAgrees cfg'.tape 1 (encodeBitsSym inst.target) ∧
      cfg'.tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary ∧
      tapeAgrees cfg'.tape (2 + ((encodeBitsSym inst.target).length : ℤ))
        (encodeElementsSymWithSel inst.elements sel) ∧
      cfg'.tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary := by
  let tb := encodeBitsSym inst.target
  let eb := encodeElementsSym inst.elements
  let tape := (symInitialConfig (encodeInstanceSym inst)).tape
  -- 初始带分解：input = #ₗ ++ tb ++ #₀ ++ eb ++ #₁
  have htape0 : tapeAgrees tape 0 (encodeInstanceSym inst) :=
    symInitialConfig_tapeAgrees (encodeInstanceSym inst)
  have htapeA : tapeAgrees tape 0
      ([Sym.boundary] ++ (tb ++ ([Sym.boundary] ++ (eb ++ [Sym.boundary])))) := by
    simpa [encodeInstanceSym, tb, eb] using htape0
  have hsplit1 := (tapeAgrees_append tape 0 [Sym.boundary]
    (tb ++ ([Sym.boundary] ++ (eb ++ [Sym.boundary])))).mp htapeA
  have hb_l : tape 0 = Sym.boundary := ((tapeAgrees_cons tape 0 Sym.boundary []).mp hsplit1.1).1
  have htape1 : tapeAgrees tape 1 (tb ++ ([Sym.boundary] ++ (eb ++ [Sym.boundary]))) := by
    simpa using hsplit1.2
  have hsplit2 := (tapeAgrees_append tape 1 tb ([Sym.boundary] ++ (eb ++ [Sym.boundary]))).mp htape1
  have ht_tb : tapeAgrees tape 1 tb := hsplit2.1
  have hsplit3 := (tapeAgrees_cons tape (1 + (tb.length : ℤ)) Sym.boundary (eb ++ [Sym.boundary])).mp hsplit2.2
  have hb_0 : tape (1 + (tb.length : ℤ)) = Sym.boundary := hsplit3.1
  have hsplit4 := (tapeAgrees_append tape ((1 + (tb.length : ℤ)) + 1) eb [Sym.boundary]).mp hsplit3.2
  have hoff : (1 + (tb.length : ℤ)) + 1 = 2 + (tb.length : ℤ) := by ring
  have hoff2 : ((1 + (tb.length : ℤ)) + 1) + (eb.length : ℤ) =
      (2 + (tb.length : ℤ)) + (eb.length : ℤ) := by ring
  have helems0 : tapeAgrees tape (2 + (tb.length : ℤ)) eb := by
    rw [← hoff]
    exact hsplit4.1
  have hb1 : tape (2 + (tb.length : ℤ) + (eb.length : ℤ)) = Sym.boundary := by
    rw [← hoff2]
    exact ((tapeAgrees_cons tape (((1 + (tb.length : ℤ)) + 1) + (eb.length : ℤ))
      Sym.boundary []).mp hsplit4.2).1
  -- 阶段 1：状态 0 → 1
  rcases step0_initial tape hb_l with ⟨s0, hs0⟩
  -- 阶段 2：状态 1 跨 target 位段 → 2
  rcases scanRight1_bits_len tb 1 tape (encodeBitsSym_nonboundary inst.target) ht_tb hb_0 with
    ⟨π1, cfg1, hπ1, hs1, hhead1, hlen1, htape1'⟩
  have hh1 : cfg1.headPos = 2 + (tb.length : ℤ) := by rw [hhead1]; ring
  have hcfg1 : SymConfig.mk 2 tape (2 + (tb.length : ℤ)) = cfg1 := by
    rw [← hh1, ← hs1, ← htape1']
  -- 阶段 3：状态 2 选标走带 → 3
  rcases segS2_chosen inst.elements sel (2 + (tb.length : ℤ)) tape hsel_len helems0 hb1 with
    ⟨π2, cfg2, hπ2, hs2, hhead2, htape2, _hnb2, hleft2, hbound2, hlen2⟩
  have hπ2' : SymSteps VerifierSym.transition cfg1 π2 cfg2 := hcfg1.symm ▸ hπ2
  have hAB : SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) ([s0] ++ π1) cfg1 :=
    SymSteps_trans VerifierSym.transition (SymConfig.mk 0 tape 0) (SymConfig.mk 1 tape 1)
      cfg1 [s0] π1 hs0 hπ1
  have htotal : SymSteps VerifierSym.transition (SymConfig.mk 0 tape 0) (([s0] ++ π1) ++ π2) cfg2 :=
    SymSteps_trans VerifierSym.transition (SymConfig.mk 0 tape 0) cfg1 cfg2 ([s0] ++ π1) π2 hAB hπ2'
  have hlenπ : (([s0] ++ π1) ++ π2).length = tb.length + eb.length + 3 := by
    rw [List.length_append, List.length_append, hlen1, hlen2]
    simp only [List.length_cons, List.length_nil, eb]
    omega
  have hlenN : (encodeInstanceSym inst).length = tb.length + eb.length + 3 := by
    simp only [encodeInstanceSym, tb, eb, List.length_append, List.length_cons, List.length_nil]
    omega
  refine ⟨([s0] ++ π1) ++ π2, cfg2, htotal, hs2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hhead2
  · rw [hlenπ, hlenN]
    omega
  · rw [hleft2 0 (by omega)]
    exact hb_l
  · intro i hi
    rw [hleft2 (1 + (i : ℤ)) (by dsimp only [tb]; omega)]
    exact ht_tb i hi
  · rw [hleft2 (1 + (tb.length : ℤ)) (by omega)]
    exact hb_0
  · exact htape2
  · exact hbound2


-- ==================== C3-δ：段 S1（相位 1.5：3→24→29/26→27→38→28→4） ====================

/-- [C3-δ] 通用左扫 + 步数（scanLeftKeepPos 的长度版）：q 从 p 左扫 n 格（写回自身、左移），
    再读 w → q'（方向 d）。恰 n+1 步，带保持。 -/
lemma scanLeftKeepPos_len (q q' : ℕ) (w : Sym) (d : Dir) (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hkeep : ∀ i : ℤ, p - (n : ℤ) < i ∧ i ≤ p →
      { nextState := q, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (q, tape i))
    (hend : { nextState := q', writeSym := w, moveDir := d } ∈ VerifierSym.transition (q, w))
    (hbound : tape (p - (n : ℤ)) = w) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk q tape p) π cfg' ∧
      cfg'.state = q' ∧ cfg'.headPos = p - (n : ℤ) + d.toInt ∧ cfg'.tape = tape ∧
      π.length = n + 1 := by
  induction n generalizing p tape with
  | zero =>
      let r : SymTransResult := { nextState := q', writeSym := w, moveDir := d }
      let step : SymStep := { fromState := q, readSym := w, result := r }
      have hbound' : tape p = w := by simpa using hbound
      refine ⟨[step], symStepConfig (SymConfig.mk q tape p) step.result, ?_, rfl, ?_, ?_, ?_⟩
      · refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · change step.readSym = tape p
          rw [hbound']
        · change step.result ∈ VerifierSym.transition (q, tape p)
          rw [hbound']
          exact hend
      · simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
      · simp [symStepConfig, SymConfig.mk, step, r]
        funext i
        by_cases h : i = p <;> simp [h, hbound']
      · simp
  | succ n ih =>
      let r : SymTransResult := { nextState := q, writeSym := tape p, moveDir := Dir.L }
      let step : SymStep := { fromState := q, readSym := tape p, result := r }
      have htrans : step.result ∈ VerifierSym.transition (q, tape p) := by
        exact hkeep p (by constructor <;> omega)
      have hstep : SymSteps VerifierSym.transition (SymConfig.mk q tape p) [step]
          (symStepConfig (SymConfig.mk q tape p) step.result) := by
        refine SymSteps.cons [] step (SymConfig.mk q tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · exact htrans
      have hcfg : symStepConfig (SymConfig.mk q tape p) step.result = SymConfig.mk q tape (p - 1) := by
        simp [symStepConfig, SymConfig.mk, step, r, Dir.toInt]
        constructor
        · funext i
          by_cases h : i = p <;> simp [h]
        · omega
      have hkeep₁ : ∀ i : ℤ, p - 1 - (n : ℤ) < i ∧ i ≤ p - 1 →
          { nextState := q, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (q, tape i) := by
        intro i h
        exact hkeep i (by constructor <;> omega)
      have hbound₁ : tape (p - 1 - (n : ℤ)) = w := by
        have h' : p - 1 - (n : ℤ) = p - ((n + 1 : ℕ) : ℤ) := by omega
        rw [h']
        exact hbound
      rcases ih (p - 1) tape hkeep₁ hbound₁ with ⟨π', cfg', hπ', hs', hhead', htape', hlen'⟩
      refine ⟨[step] ++ π', cfg', ?_, hs', ?_, ?_, ?_⟩
      · exact SymSteps_trans VerifierSym.transition (SymConfig.mk q tape p)
          (SymConfig.mk q tape (p - 1)) cfg' [step] π' (hcfg ▸ hstep) hπ'
      · rw [hhead']
        omega
      · exact htape'
      · simp [hlen']

-- ==================== C3-δ：段 S1 核（西扫+东回·长度版） ====================

set_option linter.unusedVariables false in
lemma format_sweep_rec_from26_len (blocks : List (Sym × List Sym)) (tgt : List Sym) (p₀ : ℤ) (tape : ℤ → Sym)
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hpos : ∀ b ∈ blocks, blockTopIs1 b)
    (hels : tapeAgrees tape p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))))
    (htgt : tapeAgrees tape (p₀ - (tgt.length : ℤ) - 1) tgt)
    (htgt_data : ∀ s ∈ tgt, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne_tgt : tgt ≠ [])
    (hmid : tape (p₀ - 1) = Sym.boundary)
    (hleft : tape (p₀ - (tgt.length : ℤ) - 2) = Sym.boundary)
    (hne_blocks : blocks ≠ []) :
    ∃ π cfg', SymSteps VerifierSym.transition
      (SymConfig.mk 26 tape (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1)) π cfg' ∧
      cfg'.state = 27 ∧ cfg'.headPos = p₀ - 2 ∧ cfg'.tape = tape ∧
      π.length ≤ (joinLists (blocks.map (fun b => [b.1] ++ b.2))).length + blocks.length + 1 := by
  let f : Sym × List Sym → List Sym := fun b => [b.1] ++ b.2
  induction blocks using List.reverseRecOn generalizing p₀ tape with
  | nil => exfalso; exact hne_blocks rfl
  | append_singleton bs b ih =>
      let els' : List Sym := joinLists (bs.map f)
      let els : List Sym := els' ++ f b
      have hels_eq : els = joinLists ((bs ++ [b]).map f) := by
        simp [els, els', f, List.map_append, joinLists_append, joinLists_cons, joinLists_nil]
      have hb_mem : b ∈ bs ++ [b] := by simp
      have hbb := hblocks b hb_mem
      have hb1 : b.1 = Sym.sel ∨ b.1 = Sym.nosel := hbb.1
      have hb2ne : b.2 ≠ [] := hbb.2.1
      have hb2_data : ∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := hbb.2.2
      have hb1m : b.1.2 = false := by rcases hb1 with h | h <;> simp [h, Sym.sel, Sym.nosel, Sym.mk]
      have helen : (els.length : ℤ) = (els'.length : ℤ) + 1 + (b.2.length : ℤ) := by
        simp [els, els', f]
        omega
      have htape_els : tapeAgrees tape p₀ els := by
        intro i hi
        rw [hels_eq] at hi
        have h := hels i hi
        simp only [hels_eq]
        exact h
      -- 定位 b.2 从右往左第一个 data1（最右位 d1 → 29 直接；d0 → 拒绝）
      have hb2_pos : ∃ s ∈ b.2, s.1 = SymKind.data1 := by
        refine ⟨b.2[b.2.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hb2ne) (by norm_num)), ?_, ?_⟩
        · exact List.getElem_mem _
        · exact hpos b hb_mem hb2ne
      rcases first_data1_from_right b.2 hb2_data hb2ne hb2_pos with ⟨k, hk_lt, hk1, hk0s⟩
      have hk_le : k ≤ b.2.length - 1 := by omega
      have hk1_le : k + 1 ≤ b.2.length := by omega
      have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
        rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
        rw [Nat.cast_sub hk1_le]
        rw [Nat.cast_add]
        norm_num
        omega
      -- 24 读最右位（els 最后一位 = b.2 的 last）
      have hlast_tape24 : tape (p₀ + (els.length : ℤ) - 1) = els[els.length - 1]'(by omega) := by
        have hne' : els ≠ [] := by
          simpa [f, els, els', hels_eq] using (blocksJoin_ne_nil (bs ++ [b]) hne_blocks (by intro b' hb'; exact (hblocks b' hb').2.1))
        have hidx : els.length - 1 < els.length := Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne'))
        have h := htape_els (els.length - 1) hidx
        have hcast : p₀ + ↑(els.length - 1) = p₀ + ↑els.length - 1 := by
          rw [Nat.cast_pred (by exact (List.length_pos_iff_ne_nil).mpr hne')]
          omega
        rw [congrArg tape hcast] at h
        exact h
      have hlen_nat : els.length = els'.length + 1 + b.2.length := by
        simp [els, els', f]
        omega
      have hlast_cell : els[els.length - 1]'(by omega) = b.2[b.2.length - 1]'(by omega) := by
        have hidx0 : els.length - 1 < (els' ++ ([b.1] ++ b.2)).length := by
          rw [List.length_append, List.length_append, List.length_singleton]
          omega
        change (els' ++ ([b.1] ++ b.2))[els.length - 1]'hidx0 = b.2[b.2.length - 1]'(by omega)
        rw [List.getElem_append_right (by
          rw [hlen_nat]
          omega)]
        rw [List.getElem_append_right (by
          rw [List.length_singleton]
          omega)]
        have hidx' : els.length - 1 - els'.length - [b.1].length = b.2.length - 1 := by
          rw [List.length_singleton]
          rw [hlen_nat]
          omega
        simp only [hidx']
      have hlast_m : (tape (p₀ + (els.length : ℤ) - 1)).2 = false := by
        rw [hlast_tape24, hlast_cell]
        rcases (hb2_data (b.2[b.2.length - 1]'(by omega)) (List.getElem_mem (by omega))) with ⟨_, hm⟩
        exact hm
      have hb1k : b.1.1 = SymKind.sel ∨ b.1.1 = SymKind.nosel := by
        rcases hb1 with h | h
        · left; rw [h]; rfl
        · right; rw [h]; rfl
      -- 段 2（29 扫剩余数据 → 选择符 → 26）；起点 p29 = 偏移 k+1 位置
      let p29 : ℤ := p₀ + (els.length : ℤ) - (k : ℤ) - 2
      have hkeep29 : ∀ i : ℤ, p29 - ((b.2.length - 1 - k : ℕ) : ℤ) < i ∧ i ≤ p29 →
          { nextState := 29, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (29, tape i) := by
        intro i h
        have hi' : p₀ + (els'.length : ℤ) < i := by
          have hk' := h.1
          rw [show p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) from by
            dsimp [p29]
            rw [hcast_k]
            rw [helen]
            omega] at hk'
          exact hk'
        have hio : ∃ io : ℕ, (io : ℤ) = i - p₀ := by
          refine ⟨(i - p₀).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p₀)
        rcases hio with ⟨io, hio_eq⟩
        have hio_lt : io < els.length := by omega
        have hidx : p₀ + (io : ℤ) = i := by omega
        have hcell : tape i = els[io] := by
          rw [← hidx]
          exact htape_els io hio_lt
        have hio_ge : els'.length + 1 ≤ io := by omega
        have hio_lt2 : io < els'.length + 1 + b.2.length := by omega
        have hcell' : els[io] = b.2[io - (els'.length + 1)]'(by omega) := by
          have hio_ltX : io < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[io]'hio_ltX = b.2[io - (els'.length + 1)]'(by omega)
          rw [List.getElem_append_right (by omega)]
          rw [List.getElem_append_right (by
            rw [List.length_singleton]
            omega)]
          have hidx' : io - els'.length - [b.1].length = io - (els'.length + 1) := by
            rw [List.length_singleton]
            omega
          simp only [hidx']
        have hmem : b.2[io - (els'.length + 1)] ∈ b.2 := List.getElem_mem (by omega)
        have hdata := hb2_data (b.2[io - (els'.length + 1)]) hmem
        have hk : (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
          rw [hcell, hcell']
          exact hdata.1
        have hm : (tape i).2 = false := by
          rw [hcell, hcell']
          exact hdata.2
        exact trans29_data (tape i) hk hm
      have hb29_end : tape (p29 - ((b.2.length - 1 - k : ℕ) : ℤ)) = b.1 := by
        have heq : p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) := by
          dsimp [p29]
          rw [hcast_k]
          rw [helen]
          omega
        rw [heq]
        have hcell : tape (p₀ + (els'.length : ℤ)) = els[els'.length]'(by omega) :=
          htape_els els'.length (by omega)
        rw [hcell]
        rw [show els[els'.length] = b.1 from by
          have hidx0 : els'.length < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[els'.length]'hidx0 = b.1
          rw [List.getElem_append_right (by omega)]
          have hidx1 : els'.length - els'.length = 0 := by omega
          simp only [hidx1]
          rfl]
      -- 入口：24 读最右位 → 25/29 找 1 → 29 态（段 2 起点 p29）
      have hentry : ∃ π0 cfg0, SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) π0 cfg0 ∧
          cfg0 = SymConfig.mk 29 tape p29 ∧ π0.length = 1 := by
        by_cases hk0 : k = 0
        · -- k=0：最右位是 data1：24 d1 → 29
          have hlast1 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data1 := by
            rw [hlast_tape24, hlast_cell]
            simpa [hk0] using hk1
          let r24 : SymTransResult := { nextState := 29, writeSym := tape (p₀ + (els.length : ℤ) - 1), moveDir := Dir.L }
          let step24 : SymStep := { fromState := 26, readSym := tape (p₀ + (els.length : ℤ) - 1), result := r24 }
          have htrans24 : step24.result ∈ VerifierSym.transition (26, tape (p₀ + (els.length : ℤ) - 1)) := by
            exact trans26_data1 (tape (p₀ + (els.length : ℤ) - 1)) (congrArg (fun s : Sym => s.1) hlast1) hlast_m
          have hstep24 : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) [step24]
              (symStepConfig (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) step24.result) := by
            refine SymSteps.cons [] step24 (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
            · rfl
            · rfl
            · exact htrans24
          have hcfg24 : symStepConfig (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) step24.result =
              SymConfig.mk 29 tape (p₀ + (els.length : ℤ) - 2) := by
            simp [symStepConfig, SymConfig.mk, step24, r24, Dir.toInt]
            constructor
            · funext i
              by_cases h : i = p₀ + (els.length : ℤ) - 1 <;> simp [h]
            · omega
          refine ⟨[step24], symStepConfig (SymConfig.mk 26 tape (p₀ + (els.length : ℤ) - 1)) step24.result, hstep24, ?_, ?_⟩
          · rw [hcfg24]
            simp [p29, hk0]
          · rfl
        · -- k ≥ 1：最右位 data0，与 hpos（最高位 = data1）矛盾
          have hk0pos : 0 < k := by omega
          have hlast0 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data0 := by
            rw [hlast_tape24, hlast_cell]
            simpa using hk0s 0 hk0pos
          have hcell0 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data0 := by
            have hc : tape (p₀ + (els.length : ℤ) - 1) = b.2[b.2.length - 1]'(by omega) := by
              rw [hlast_tape24, hlast_cell]
            rw [hc] at hlast0
            simpa using congrArg (fun s : Sym => s.1) hlast0
          have hcell1 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data1 := hpos b hb_mem hb2ne
          have : SymKind.data0 = SymKind.data1 := hcell0.symm.trans hcell1
          cases this
      rcases hentry with ⟨π0, cfg0, hπ0, hcfg0, hlen0⟩
      rcases scanLeftKeepPos_len 29 26 b.1 Dir.L (b.2.length - 1 - k) p29 tape
        hkeep29 (trans29_sel b.1 hb1k hb1m) hb29_end with ⟨πb, cfgb, hπb, hsb, hheadb, htapeb, hlenb⟩
      have hπb' : SymSteps VerifierSym.transition cfg0 πb cfgb := by
        simpa [hcfg0] using hπb
      have hcfgb : cfgb = SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1) := by
        rcases cfgb with ⟨s, t, hp⟩
        have ht : t = tape := by simpa using htapeb
        have hs : s = 26 := by simpa using hsb
        have hhp : hp = p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) := by
          simpa [Dir.toInt, p29] using hheadb
        subst t; subst s; subst hp
        simp [SymConfig.mk]
        rw [show p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) =
            p₀ + (els'.length : ℤ) - 1 from by
          have hk1_le : k + 1 ≤ b.2.length := by omega
          have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
            rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
            rw [Nat.cast_sub hk1_le]
            rw [Nat.cast_add]
            norm_num
            omega
          rw [helen]
          rw [hcast_k]
          omega]
      by_cases hbs : bs = []
      · -- 26 读 #₀ → 27
        have hpos : p₀ + (els'.length : ℤ) - 1 = p₀ - 1 := by
          simp [els', hbs]
        have hmid' : tape (p₀ + (els'.length : ℤ) - 1) = Sym.boundary := by
          rw [hpos]
          exact hmid
        let r26 : SymTransResult := { nextState := 27, writeSym := Sym.boundary, moveDir := Dir.L }
        let step26 : SymStep := { fromState := 26, readSym := Sym.boundary, result := r26 }
        have htrans26 : step26.result ∈ VerifierSym.transition (26, Sym.boundary) := trans26_hash
        have hstep26 : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) [step26]
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result) := by
          refine SymSteps.cons [] step26 (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.boundary = tape (p₀ + (els'.length : ℤ) - 1)
            rw [hmid']
          · change step26.result ∈ VerifierSym.transition (26, tape (p₀ + (els'.length : ℤ) - 1))
            rw [hmid']
            exact htrans26
        refine ⟨π0 ++ πb ++ [step26], symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result, ?_, ?_, ?_, ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1))
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result)
            (π0 ++ πb) [step26] h0b hstep26
        · rfl
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).headPos = p₀ - 2
          simp [symStepConfig, SymConfig.mk, step26, r26, Dir.toInt]
          omega
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).tape = tape
          simp [symStepConfig, SymConfig.mk, step26, r26]
          funext i
          by_cases h : i = p₀ + (els'.length : ℤ) - 1 <;> simp [h, hmid']
        · have helenN : els.length = els'.length + 1 + b.2.length := by simp [els, els', f]; omega
          rw [List.length_append, List.length_append, hlen0, hlenb, List.length_singleton]
          rw [← hels_eq, helenN]
          simp only [List.length_append, List.length_singleton]
          omega
      · -- 26 读 els'.last（data）→ 25，接 ih
        have hbs' : bs ≠ [] := hbs
        have hblocks_bs : ∀ b' ∈ bs, (b'.1 = Sym.sel ∨ b'.1 = Sym.nosel) ∧ b'.2 ≠ [] ∧
            (∀ s ∈ b'.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
          intro b' hb'
          exact hblocks b' (by simp [hb'])
        have hels_bs : tapeAgrees tape p₀ els' := by
          intro i hi
          have helen' := htape_els i (by
            rw [show els = els' ++ ([b.1] ++ b.2) from by simp [els, els', f]]
            rw [List.length_append, List.length_append, List.length_singleton]
            omega)
          have hcelli : els[i]'(by omega) = els'[i]'(by omega) := by
            change (els' ++ ([b.1] ++ b.2))[i]'(by
              rw [List.length_append, List.length_append, List.length_singleton]
              omega) = els'[i]'(by omega)
            rw [List.getElem_append_left (by omega)]
          rw [hcelli] at helen'
          exact helen'
        have hpos_bs : ∀ b' ∈ bs, blockTopIs1 b' := by
          intro b' hb'
          exact hpos b' (by simp [hb'])
        rcases ih p₀ tape hblocks_bs hpos_bs hels_bs htgt hmid hleft hbs' with ⟨π', cfg', hπ', hs', hhead', htape', hlen'⟩
        refine ⟨π0 ++ πb ++ π', cfg', ?_, hs', ?_, ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          have hπ'' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π' cfg' := by
            simpa [f, els'] using hπ'
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 26 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) cfg' (π0 ++ πb) π' h0b hπ''
        · rw [hhead']
        · simpa using htape'
        · have helenN : els.length = els'.length + 1 + b.2.length := by simp [els, els', f]; omega
          have hlen'Nat : π'.length ≤ els'.length + bs.length + 1 := by simpa [els', f] using hlen'
          rw [List.length_append, List.length_append, hlen0, hlenb]
          rw [← hels_eq, helenN]
          simp only [List.length_append, List.length_singleton]
          omega

lemma format_sweep_rec_len (blocks : List (Sym × List Sym)) (tgt : List Sym) (p₀ : ℤ) (tape : ℤ → Sym)
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hpos : ∀ b ∈ blocks, blockTopIs1 b)
    (hels : tapeAgrees tape p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))))
    (htgt : tapeAgrees tape (p₀ - (tgt.length : ℤ) - 1) tgt)
    (htgt_data : ∀ s ∈ tgt, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne_tgt : tgt ≠ [])
    (hmid : tape (p₀ - 1) = Sym.boundary)
    (hleft : tape (p₀ - (tgt.length : ℤ) - 2) = Sym.boundary)
    (hne_blocks : blocks ≠ []) :
    ∃ π cfg', SymSteps VerifierSym.transition
      (SymConfig.mk 24 tape (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1)) π cfg' ∧
      cfg'.state = 27 ∧ cfg'.headPos = p₀ - 2 ∧ cfg'.tape = tape ∧
      π.length ≤ (joinLists (blocks.map (fun b => [b.1] ++ b.2))).length + blocks.length + 1 := by
  let f : Sym × List Sym → List Sym := fun b => [b.1] ++ b.2
  induction blocks using List.reverseRecOn generalizing p₀ tape with
  | nil => exfalso; exact hne_blocks rfl
  | append_singleton bs b ih =>
      let els' : List Sym := joinLists (bs.map f)
      let els : List Sym := els' ++ f b
      have hels_eq : els = joinLists ((bs ++ [b]).map f) := by
        simp [els, els', f, List.map_append, joinLists_append, joinLists_cons, joinLists_nil]
      have hb_mem : b ∈ bs ++ [b] := by simp
      have hbb := hblocks b hb_mem
      have hb1 : b.1 = Sym.sel ∨ b.1 = Sym.nosel := hbb.1
      have hb2ne : b.2 ≠ [] := hbb.2.1
      have hb2_data : ∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := hbb.2.2
      have hb1m : b.1.2 = false := by rcases hb1 with h | h <;> simp [h, Sym.sel, Sym.nosel, Sym.mk]
      have helen : (els.length : ℤ) = (els'.length : ℤ) + 1 + (b.2.length : ℤ) := by
        simp [els, els', f]
        omega
      have htape_els : tapeAgrees tape p₀ els := by
        intro i hi
        rw [hels_eq] at hi
        have h := hels i hi
        simp only [hels_eq]
        exact h
      -- 定位 b.2 从右往左第一个 data1（最右位 d1 → 29 直接；d0 → 拒绝）
      have hb2_pos : ∃ s ∈ b.2, s.1 = SymKind.data1 := by
        refine ⟨b.2[b.2.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hb2ne) (by norm_num)), ?_, ?_⟩
        · exact List.getElem_mem _
        · exact hpos b hb_mem hb2ne
      rcases first_data1_from_right b.2 hb2_data hb2ne hb2_pos with ⟨k, hk_lt, hk1, hk0s⟩
      have hk_le : k ≤ b.2.length - 1 := by omega
      have hk1_le : k + 1 ≤ b.2.length := by omega
      have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
        rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
        rw [Nat.cast_sub hk1_le]
        rw [Nat.cast_add]
        norm_num
        omega
      -- 24 读最右位（els 最后一位 = b.2 的 last）
      have hlast_tape24 : tape (p₀ + (els.length : ℤ) - 1) = els[els.length - 1]'(by omega) := by
        have hne' : els ≠ [] := by
          simpa [f, els, els', hels_eq] using (blocksJoin_ne_nil (bs ++ [b]) hne_blocks (by intro b' hb'; exact (hblocks b' hb').2.1))
        have hidx : els.length - 1 < els.length := Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne'))
        have h := htape_els (els.length - 1) hidx
        have hcast : p₀ + ↑(els.length - 1) = p₀ + ↑els.length - 1 := by
          rw [Nat.cast_pred (by exact (List.length_pos_iff_ne_nil).mpr hne')]
          omega
        rw [congrArg tape hcast] at h
        exact h
      have hlen_nat : els.length = els'.length + 1 + b.2.length := by
        simp [els, els', f]
        omega
      have hlast_cell : els[els.length - 1]'(by omega) = b.2[b.2.length - 1]'(by omega) := by
        have hidx0 : els.length - 1 < (els' ++ ([b.1] ++ b.2)).length := by
          rw [List.length_append, List.length_append, List.length_singleton]
          omega
        change (els' ++ ([b.1] ++ b.2))[els.length - 1]'hidx0 = b.2[b.2.length - 1]'(by omega)
        rw [List.getElem_append_right (by
          rw [hlen_nat]
          omega)]
        rw [List.getElem_append_right (by
          rw [List.length_singleton]
          omega)]
        have hidx' : els.length - 1 - els'.length - [b.1].length = b.2.length - 1 := by
          rw [List.length_singleton]
          rw [hlen_nat]
          omega
        simp only [hidx']
      have hlast_m : (tape (p₀ + (els.length : ℤ) - 1)).2 = false := by
        rw [hlast_tape24, hlast_cell]
        rcases (hb2_data (b.2[b.2.length - 1]'(by omega)) (List.getElem_mem (by omega))) with ⟨_, hm⟩
        exact hm
      have hb1k : b.1.1 = SymKind.sel ∨ b.1.1 = SymKind.nosel := by
        rcases hb1 with h | h
        · left; rw [h]; rfl
        · right; rw [h]; rfl
      -- 段 2（29 扫剩余数据 → 选择符 → 26）；起点 p29 = 偏移 k+1 位置
      let p29 : ℤ := p₀ + (els.length : ℤ) - (k : ℤ) - 2
      have hkeep29 : ∀ i : ℤ, p29 - ((b.2.length - 1 - k : ℕ) : ℤ) < i ∧ i ≤ p29 →
          { nextState := 29, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (29, tape i) := by
        intro i h
        have hi' : p₀ + (els'.length : ℤ) < i := by
          have hk' := h.1
          rw [show p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) from by
            dsimp [p29]
            rw [hcast_k]
            rw [helen]
            omega] at hk'
          exact hk'
        have hio : ∃ io : ℕ, (io : ℤ) = i - p₀ := by
          refine ⟨(i - p₀).toNat, ?_⟩
          exact Int.toNat_of_nonneg (by omega : 0 ≤ i - p₀)
        rcases hio with ⟨io, hio_eq⟩
        have hio_lt : io < els.length := by omega
        have hidx : p₀ + (io : ℤ) = i := by omega
        have hcell : tape i = els[io] := by
          rw [← hidx]
          exact htape_els io hio_lt
        have hio_ge : els'.length + 1 ≤ io := by omega
        have hio_lt2 : io < els'.length + 1 + b.2.length := by omega
        have hcell' : els[io] = b.2[io - (els'.length + 1)]'(by omega) := by
          have hio_ltX : io < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[io]'hio_ltX = b.2[io - (els'.length + 1)]'(by omega)
          rw [List.getElem_append_right (by omega)]
          rw [List.getElem_append_right (by
            rw [List.length_singleton]
            omega)]
          have hidx' : io - els'.length - [b.1].length = io - (els'.length + 1) := by
            rw [List.length_singleton]
            omega
          simp only [hidx']
        have hmem : b.2[io - (els'.length + 1)] ∈ b.2 := List.getElem_mem (by omega)
        have hdata := hb2_data (b.2[io - (els'.length + 1)]) hmem
        have hk : (tape i).1 = SymKind.data0 ∨ (tape i).1 = SymKind.data1 := by
          rw [hcell, hcell']
          exact hdata.1
        have hm : (tape i).2 = false := by
          rw [hcell, hcell']
          exact hdata.2
        exact trans29_data (tape i) hk hm
      have hb29_end : tape (p29 - ((b.2.length - 1 - k : ℕ) : ℤ)) = b.1 := by
        have heq : p29 - ((b.2.length - 1 - k : ℕ) : ℤ) = p₀ + (els'.length : ℤ) := by
          dsimp [p29]
          rw [hcast_k]
          rw [helen]
          omega
        rw [heq]
        have hcell : tape (p₀ + (els'.length : ℤ)) = els[els'.length]'(by omega) :=
          htape_els els'.length (by omega)
        rw [hcell]
        rw [show els[els'.length] = b.1 from by
          have hidx0 : els'.length < (els' ++ ([b.1] ++ b.2)).length := by
            rw [List.length_append, List.length_append, List.length_singleton]
            omega
          change (els' ++ ([b.1] ++ b.2))[els'.length]'hidx0 = b.1
          rw [List.getElem_append_right (by omega)]
          have hidx1 : els'.length - els'.length = 0 := by omega
          simp only [hidx1]
          rfl]
      -- 入口：24 读最右位 → 25/29 找 1 → 29 态（段 2 起点 p29）
      have hentry : ∃ π0 cfg0, SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) π0 cfg0 ∧
          cfg0 = SymConfig.mk 29 tape p29 ∧ π0.length = 1 := by
        by_cases hk0 : k = 0
        · -- k=0：最右位是 data1：24 d1 → 29
          have hlast1 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data1 := by
            rw [hlast_tape24, hlast_cell]
            simpa [hk0] using hk1
          let r24 : SymTransResult := { nextState := 29, writeSym := tape (p₀ + (els.length : ℤ) - 1), moveDir := Dir.L }
          let step24 : SymStep := { fromState := 24, readSym := tape (p₀ + (els.length : ℤ) - 1), result := r24 }
          have htrans24 : step24.result ∈ VerifierSym.transition (24, tape (p₀ + (els.length : ℤ) - 1)) := by
            exact trans24_data1 (tape (p₀ + (els.length : ℤ) - 1)) (congrArg (fun s : Sym => s.1) hlast1) hlast_m
          have hstep24 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) [step24]
              (symStepConfig (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) step24.result) := by
            refine SymSteps.cons [] step24 (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
            · rfl
            · rfl
            · exact htrans24
          have hcfg24 : symStepConfig (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) step24.result =
              SymConfig.mk 29 tape (p₀ + (els.length : ℤ) - 2) := by
            simp [symStepConfig, SymConfig.mk, step24, r24, Dir.toInt]
            constructor
            · funext i
              by_cases h : i = p₀ + (els.length : ℤ) - 1 <;> simp [h]
            · omega
          refine ⟨[step24], symStepConfig (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1)) step24.result, hstep24, ?_, ?_⟩
          · rw [hcfg24]
            simp [p29, hk0]
          · rfl
        · -- k ≥ 1：最右位 data0，与 hpos（最高位 = data1）矛盾
          have hk0pos : 0 < k := by omega
          have hlast0 : tape (p₀ + (els.length : ℤ) - 1) = Sym.data0 := by
            rw [hlast_tape24, hlast_cell]
            simpa using hk0s 0 hk0pos
          have hcell0 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data0 := by
            have hc : tape (p₀ + (els.length : ℤ) - 1) = b.2[b.2.length - 1]'(by omega) := by
              rw [hlast_tape24, hlast_cell]
            rw [hc] at hlast0
            simpa using congrArg (fun s : Sym => s.1) hlast0
          have hcell1 : (b.2[b.2.length - 1]'(by omega)).1 = SymKind.data1 := hpos b hb_mem hb2ne
          have : SymKind.data0 = SymKind.data1 := hcell0.symm.trans hcell1
          cases this
      rcases hentry with ⟨π0, cfg0, hπ0, hcfg0, hlen0⟩
      rcases scanLeftKeepPos_len 29 26 b.1 Dir.L (b.2.length - 1 - k) p29 tape
        hkeep29 (trans29_sel b.1 hb1k hb1m) hb29_end with ⟨πb, cfgb, hπb, hsb, hheadb, htapeb, hlenb⟩
      have hπb' : SymSteps VerifierSym.transition cfg0 πb cfgb := by
        simpa [hcfg0] using hπb
      have hcfgb : cfgb = SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1) := by
        rcases cfgb with ⟨s, t, hp⟩
        have ht : t = tape := by simpa using htapeb
        have hs : s = 26 := by simpa using hsb
        have hhp : hp = p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) := by
          simpa [Dir.toInt, p29] using hheadb
        subst t; subst s; subst hp
        simp [SymConfig.mk]
        rw [show p₀ + (els.length : ℤ) - (k : ℤ) - 2 - ((b.2.length - 1 - k : ℕ) : ℤ) + (-1 : ℤ) =
            p₀ + (els'.length : ℤ) - 1 from by
          have hk1_le : k + 1 ≤ b.2.length := by omega
          have hcast_k : ((b.2.length - 1 - k : ℕ) : ℤ) = (b.2.length : ℤ) - 1 - (k : ℤ) := by
            rw [show b.2.length - 1 - k = b.2.length - (k + 1) from by omega]
            rw [Nat.cast_sub hk1_le]
            rw [Nat.cast_add]
            norm_num
            omega
          rw [helen]
          rw [hcast_k]
          omega]
      by_cases hbs : bs = []
      · -- 26 读 #₀ → 27
        have hpos : p₀ + (els'.length : ℤ) - 1 = p₀ - 1 := by
          simp [els', hbs]
        have hmid' : tape (p₀ + (els'.length : ℤ) - 1) = Sym.boundary := by
          rw [hpos]
          exact hmid
        let r26 : SymTransResult := { nextState := 27, writeSym := Sym.boundary, moveDir := Dir.L }
        let step26 : SymStep := { fromState := 26, readSym := Sym.boundary, result := r26 }
        have htrans26 : step26.result ∈ VerifierSym.transition (26, Sym.boundary) := trans26_hash
        have hstep26 : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) [step26]
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result) := by
          refine SymSteps.cons [] step26 (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · change Sym.boundary = tape (p₀ + (els'.length : ℤ) - 1)
            rw [hmid']
          · change step26.result ∈ VerifierSym.transition (26, tape (p₀ + (els'.length : ℤ) - 1))
            rw [hmid']
            exact htrans26
        refine ⟨π0 ++ πb ++ [step26], symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result, ?_, ?_, ?_, ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1))
            (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result)
            (π0 ++ πb) [step26] h0b hstep26
        · rfl
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).headPos = p₀ - 2
          simp [symStepConfig, SymConfig.mk, step26, r26, Dir.toInt]
          omega
        · change (symStepConfig (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) step26.result).tape = tape
          simp [symStepConfig, SymConfig.mk, step26, r26]
          funext i
          by_cases h : i = p₀ + (els'.length : ℤ) - 1 <;> simp [h, hmid']
        · have helenN : els.length = els'.length + 1 + b.2.length := by simp [els, els', f]; omega
          rw [List.length_append, List.length_append, hlen0, hlenb, List.length_singleton]
          rw [← hels_eq, helenN]
          simp only [List.length_append, List.length_singleton]
          omega
      · -- 26 读 els'.last（data）→ 25，接 ih
        have hbs' : bs ≠ [] := hbs
        have hblocks_bs : ∀ b' ∈ bs, (b'.1 = Sym.sel ∨ b'.1 = Sym.nosel) ∧ b'.2 ≠ [] ∧
            (∀ s ∈ b'.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
          intro b' hb'
          exact hblocks b' (by simp [hb'])
        have hels_bs : tapeAgrees tape p₀ els' := by
          intro i hi
          have helen' := htape_els i (by
            rw [show els = els' ++ ([b.1] ++ b.2) from by simp [els, els', f]]
            rw [List.length_append, List.length_append, List.length_singleton]
            omega)
          have hcelli : els[i]'(by omega) = els'[i]'(by omega) := by
            change (els' ++ ([b.1] ++ b.2))[i]'(by
              rw [List.length_append, List.length_append, List.length_singleton]
              omega) = els'[i]'(by omega)
            rw [List.getElem_append_left (by omega)]
          rw [hcelli] at helen'
          exact helen'
        have hpos_bs : ∀ b' ∈ bs, blockTopIs1 b' := by
          intro b' hb'
          exact hpos b' (by simp [hb'])
        rcases format_sweep_rec_from26_len bs tgt p₀ tape hblocks_bs hpos_bs hels_bs htgt htgt_data hne_tgt hmid hleft hbs' with ⟨π', cfg', hπ', hs', hhead', htape', hlen'⟩
        refine ⟨π0 ++ πb ++ π', cfg', ?_, hs', ?_, ?_, ?_⟩
        · have hπ0' : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) π0 cfg0 := by
            convert hπ0 using 1
            rw [hels_eq]
          have h0b : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) (π0 ++ πb)
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) := by
            exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1)) cfg0
              (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π0 πb hπ0' (hcfgb ▸ hπb')
          have hπ'' : SymSteps VerifierSym.transition (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) π' cfg' := by
            simpa [f, els'] using hπ'
          exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + ↑(joinLists (List.map (fun b => [b.1] ++ b.2) (bs ++ [b]))).length - 1))
            (SymConfig.mk 26 tape (p₀ + (els'.length : ℤ) - 1)) cfg' (π0 ++ πb) π' h0b hπ''
        · rw [hhead']
        · simpa using htape'
        · have helenN : els.length = els'.length + 1 + b.2.length := by simp [els, els', f]; omega
          have hlen'Nat : π'.length ≤ els'.length + bs.length + 1 := by simpa [els', f] using hlen'
          rw [List.length_append, List.length_append, hlen0, hlenb]
          rw [← hels_eq, helenN]
          simp only [List.length_append, List.length_singleton]
          omega

/-- 格式检查左扫（从状态 24、带头在元素区右端数值位出发）：
    24 读 data → 25，接 format_sweep_rec_len 扫完元素区（27 在 tgt 右端），
    38 扫 target 到 #ₗ → 28 右移回 #₀ → 状态 4，磁头在第一个元素选择符，磁带不变。 -/
lemma format_sweep_correct_len (blocks : List (Sym × List Sym)) (tgt : List Sym) (p₀ : ℤ) (tape : ℤ → Sym)
    (hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false))
    (hpos : ∀ b ∈ blocks, blockTopIs1 b)
    (hels : tapeAgrees tape p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))))
    (htgt : tapeAgrees tape (p₀ - (tgt.length : ℤ) - 1) tgt)
    (htgt_data : ∀ s ∈ tgt, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false)
    (hne_tgt : tgt ≠ [])
    (htgt_top : (tgt[tgt.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hne_tgt) (by norm_num))).1 = SymKind.data1)
    (hmid : tape (p₀ - 1) = Sym.boundary)
    (hleft : tape (p₀ - (tgt.length : ℤ) - 2) = Sym.boundary)
    (hne_blocks : blocks ≠ []) :
    ∃ π cfg', SymSteps VerifierSym.transition
      (SymConfig.mk 24 tape (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1)) π cfg' ∧
      cfg'.state = 4 ∧ cfg'.headPos = p₀ ∧ cfg'.tape = tape ∧
      π.length ≤ (joinLists (blocks.map (fun b => [b.1] ++ b.2))).length + blocks.length + 2 * tgt.length + 3 := by
  let els : List Sym := joinLists (blocks.map (fun b => [b.1] ++ b.2))
  -- 24 读 els.last（data）→ L 25
  have hlastdata := blocksJoin_last_data blocks hblocks hne_blocks
  rcases format_sweep_rec_len blocks tgt p₀ tape hblocks hpos hels htgt htgt_data hne_tgt hmid hleft hne_blocks
    with ⟨πs, cfgs, hπs, hss, hheads, htapes, hlens⟩
  have hcfgs : cfgs = SymConfig.mk 27 tape (p₀ - 2) := by
    rcases cfgs with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htapes
    have hs : s = 27 := by simpa using hss
    have hhp : hp = p₀ - 2 := by simpa using hheads
    subst t; subst s; subst hp
    simp [SymConfig.mk]
  -- 27 读 tgt.last → L 38
  have h_tgt_idx : tgt.length - 1 < tgt.length :=
    Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne_tgt))
  have htgt_last : tape (p₀ - 2) = tgt[tgt.length - 1]'h_tgt_idx := by
    have h := htgt (tgt.length - 1) (by
      exact Nat.pred_lt (ne_of_gt ((List.length_pos_iff_ne_nil).mpr hne_tgt)))
    have hcast : p₀ - ↑tgt.length - 1 + ↑(tgt.length - 1) = p₀ - ↑tgt.length - 1 + (↑tgt.length - 1) := by
      rw [Nat.cast_pred (by exact (List.length_pos_iff_ne_nil).mpr hne_tgt)]
    rw [hcast] at h
    have hidx : p₀ - (tgt.length : ℤ) - 1 + ((tgt.length : ℤ) - 1) = p₀ - 2 := by omega
    rw [hidx] at h
    exact h
  have htgt_last_data : ((tgt[tgt.length - 1]'h_tgt_idx).1 = SymKind.data0 ∨ (tgt[tgt.length - 1]'h_tgt_idx).1 = SymKind.data1) ∧
      (tgt[tgt.length - 1]'h_tgt_idx).2 = false := by
    exact htgt_data (tgt[tgt.length - 1]'h_tgt_idx) (List.getElem_mem h_tgt_idx)
  let r27 : SymTransResult := { nextState := 38, writeSym := tape (p₀ - 2), moveDir := Dir.L }
  let step27 : SymStep := { fromState := 27, readSym := tape (p₀ - 2), result := r27 }
  have htrans27 : step27.result ∈ VerifierSym.transition (27, tape (p₀ - 2)) := by
    simpa [step27, r27, htgt_last] using trans27_data1 (tgt[tgt.length - 1]'h_tgt_idx)
      htgt_top htgt_last_data.2
  have hstep27 : SymSteps VerifierSym.transition (SymConfig.mk 27 tape (p₀ - 2)) [step27]
      (symStepConfig (SymConfig.mk 27 tape (p₀ - 2)) step27.result) := by
    refine SymSteps.cons [] step27 (SymConfig.mk 27 tape (p₀ - 2)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · rfl
    · exact htrans27
  have hcfg27 : symStepConfig (SymConfig.mk 27 tape (p₀ - 2)) step27.result =
      SymConfig.mk 38 tape (p₀ - 3) := by
    simp [symStepConfig, SymConfig.mk, step27, r27, Dir.toInt]
    constructor
    · funext i
      by_cases h : i = p₀ - 2 <;> simp [h]
    · omega
  -- 38 扫 tgt（|tgt|-1 格）→ #ₗ → 28
  have hkeep38 : ∀ i : ℤ, p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ) < i ∧ i ≤ p₀ - 3 →
      { nextState := 38, writeSym := tape i, moveDir := Dir.L } ∈ VerifierSym.transition (38, tape i) := by
    intro i h
    have hio : ∃ io : ℕ, (io : ℤ) = i - (p₀ - (tgt.length : ℤ) - 1) := by
      refine ⟨(i - (p₀ - (tgt.length : ℤ) - 1)).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p₀ - (tgt.length : ℤ) - 1))
    rcases hio with ⟨io, hio_eq⟩
    have hio_lt : io < tgt.length := by omega
    have hidx : p₀ - (tgt.length : ℤ) - 1 + (io : ℤ) = i := by omega
    have hcell : tape i = tgt[io] := by
      rw [← hidx]
      exact htgt io hio_lt
    have hdata := htgt_data (tgt[io]) (List.getElem_mem hio_lt)
    exact trans38_data (tape i) (by rw [hcell]; exact hdata.1) (by rw [hcell]; exact hdata.2)
  have hbound38 : tape (p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ)) = Sym.boundary := by
    have hidx : p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ) = p₀ - (tgt.length : ℤ) - 2 := by omega
    rw [hidx]
    exact hleft
  rcases scanLeftKeepPos_len 38 28 Sym.boundary Dir.R (tgt.length - 1) (p₀ - 3) tape
    hkeep38 trans38_hash hbound38 with ⟨π38, cfg38, hπ38, hs38, hhead38, htape38, hlen38⟩
  have hcfg38 : cfg38 = SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1) := by
    rcases cfg38 with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htape38
    have hs : s = 28 := by simpa using hs38
    have hhp : hp = p₀ - 3 - ((tgt.length - 1 : ℕ) : ℤ) + 1 := by
      simpa [Dir.toInt] using hhead38
    subst t; subst s; subst hp
    simp [SymConfig.mk]
    omega
  -- 28 右扫 tgt → #₀ → 4
  have hkeep28 : ∀ i : ℤ, p₀ - (tgt.length : ℤ) - 1 ≤ i ∧ i < p₀ - (tgt.length : ℤ) - 1 + (tgt.length : ℤ) →
      { nextState := 28, writeSym := tape i, moveDir := Dir.R } ∈ VerifierSym.transition (28, tape i) := by
    intro i h
    have hio : ∃ io : ℕ, (io : ℤ) = i - (p₀ - (tgt.length : ℤ) - 1) := by
      refine ⟨(i - (p₀ - (tgt.length : ℤ) - 1)).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by omega : 0 ≤ i - (p₀ - (tgt.length : ℤ) - 1))
    rcases hio with ⟨io, hio_eq⟩
    have hio_lt : io < tgt.length := by omega
    have hidx : p₀ - (tgt.length : ℤ) - 1 + (io : ℤ) = i := by omega
    have hcell : tape i = tgt[io] := by
      rw [← hidx]
      exact htgt io hio_lt
    have hdata := htgt_data (tgt[io]) (List.getElem_mem hio_lt)
    exact trans28_data (tape i) (by rw [hcell]; exact hdata.1)
  rcases scanRightKeep_len 28 tgt.length (p₀ - (tgt.length : ℤ) - 1) tape hkeep28
    with ⟨π28, cfg28, hπ28, hs28, hhead28, htape28, hlen28⟩
  have hcfg28 : cfg28 = SymConfig.mk 28 tape (p₀ - 1) := by
    rcases cfg28 with ⟨s, t, hp⟩
    have ht : t = tape := by simpa using htape28
    have hs : s = 28 := by simpa using hs28
    have hhp : hp = p₀ - (tgt.length : ℤ) - 1 + (tgt.length : ℤ) := by simpa using hhead28
    subst t; subst s; subst hp
    simp [SymConfig.mk]
    omega
  -- 28 读 #₀ → R 4
  let r28 : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
  let step28 : SymStep := { fromState := 28, readSym := Sym.boundary, result := r28 }
  have htrans28 : step28.result ∈ VerifierSym.transition (28, Sym.boundary) := trans28_hash
  have hstep28 : SymSteps VerifierSym.transition (SymConfig.mk 28 tape (p₀ - 1)) [step28]
      (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result) := by
    refine SymSteps.cons [] step28 (SymConfig.mk 28 tape (p₀ - 1)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape (p₀ - 1)
      exact hmid.symm
    · change step28.result ∈ VerifierSym.transition (28, tape (p₀ - 1))
      rw [hmid]
      exact htrans28
  have hcfg28' : symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result =
      SymConfig.mk 4 tape p₀ := by
    simp [symStepConfig, SymConfig.mk, step28, r28, Dir.toInt]
    funext i
    by_cases h : i = p₀ - 1 <;> simp [h, hmid]
  refine ⟨πs ++ [step27] ++ π38 ++ π28 ++ [step28], symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        πs (SymConfig.mk 27 tape (p₀ - 2)) := by
      exact hcfgs ▸ hπs
    have h2 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (πs ++ [step27]) (SymConfig.mk 38 tape (p₀ - 3)) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (SymConfig.mk 27 tape (p₀ - 2)) (SymConfig.mk 38 tape (p₀ - 3))
        πs [step27] h1 (hcfg27 ▸ hstep27)
    have h3 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (πs ++ [step27] ++ π38) (SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1)) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (SymConfig.mk 38 tape (p₀ - 3)) (SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1))
        (πs ++ [step27]) π38 h2 (hcfg38 ▸ hπ38)
    have h4 : SymSteps VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (πs ++ [step27] ++ π38 ++ π28) (SymConfig.mk 28 tape (p₀ - 1)) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
        (SymConfig.mk 28 tape (p₀ - (tgt.length : ℤ) - 1)) (SymConfig.mk 28 tape (p₀ - 1))
        (πs ++ [step27] ++ π38) π28 h3 (hcfg28 ▸ hπ28)
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 24 tape (p₀ + (els.length : ℤ) - 1))
      (SymConfig.mk 28 tape (p₀ - 1)) (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result)
      (πs ++ [step27] ++ π38 ++ π28) [step28] h4 (hcfg28' ▸ hstep28)
  · rfl
  · change (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result).headPos = p₀
    simp [symStepConfig, SymConfig.mk, step28, r28, Dir.toInt]
  · change (symStepConfig (SymConfig.mk 28 tape (p₀ - 1)) step28.result).tape = tape
    simp [symStepConfig, SymConfig.mk, step28, r28]
    funext i
    by_cases h : i = p₀ - 1 <;> simp [h, hmid]
  · have hne_tgt_len : 0 < tgt.length := by cases tgt with
    | nil => exact absurd rfl hne_tgt
    | cons _ _ => simp
    have hlen38' : π38.length = tgt.length := by omega
    have hlen28' : π28.length = tgt.length := hlen28
    rw [List.length_append, List.length_append, List.length_append, List.length_append,
      hlen38', hlen28', List.length_singleton, List.length_singleton]
    omega


/-- [C3-δ] 段 S1（相位 1.5 格式段）：状态 3 @ #₁ → 状态 4 @ e₁。
    西扫（每元素：最高位检查 24/26 + 29 扫位 + 选择符）+ 过 target 西扫 38 + 东回 28；
    恰 1 + |π4| 步，总长 ≤ 2·(3+|tb|+|eb|)；#₁ 打标 (boundary,true)，其余带一字不动。 -/
lemma segS1 (inst : SubsetSumInstance) (sel : List Bool)
    (hsel_len : sel.length = inst.elements.length)
    (hne : inst.elements ≠ []) (hpos : ∀ v ∈ inst.elements, 0 < v) (htarget : 0 < inst.target)
    (tape : ℤ → Sym)
    (htape0 : tape 0 = Sym.boundary)
    (htgt : tapeAgrees tape 1 (encodeBitsSym inst.target))
    (hbnd0 : tape (1 + ((encodeBitsSym inst.target).length : ℤ)) = Sym.boundary)
    (hels : tapeAgrees tape (2 + ((encodeBitsSym inst.target).length : ℤ))
      (encodeElementsSymWithSel inst.elements sel))
    (hbnd1 : tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
      ((encodeElementsSym inst.elements).length : ℤ)) = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition
        (SymConfig.mk 3 tape (2 + ((encodeBitsSym inst.target).length : ℤ) +
          ((encodeElementsSym inst.elements).length : ℤ))) π cfg' ∧
      cfg'.state = 4 ∧
      cfg'.headPos = 2 + ((encodeBitsSym inst.target).length : ℤ) ∧
      π.length ≤ 2 * (3 + (encodeBitsSym inst.target).length +
        (encodeElementsSym inst.elements).length) ∧
      cfg'.tape = (fun i => if i = 2 + ((encodeBitsSym inst.target).length : ℤ) +
        ((encodeElementsSym inst.elements).length : ℤ)
        then Sym.mk SymKind.boundary true else tape i) := by
  let tb := encodeBitsSym inst.target
  let eb := encodeElementsSym inst.elements
  let p₀ : ℤ := 2 + (tb.length : ℤ)
  let p₃ : ℤ := p₀ + (eb.length : ℤ)
  let tape3 : ℤ → Sym := fun i => if i = p₃ then Sym.mk SymKind.boundary true else tape i
  have hbnd1' : tape p₃ = Sym.boundary := by simpa [p₃, p₀, tb, eb] using hbnd1
  rcases step3_hash1 tape p₃ hbnd1' with ⟨step3, hstep3⟩
  let blocks : List (Sym × List Sym) :=
    (inst.elements.zip sel).map (fun p => (if p.2 then Sym.sel else Sym.nosel, encodeBitsSymNative p.1))
  have hblocks : ∀ b ∈ blocks, (b.1 = Sym.sel ∨ b.1 = Sym.nosel) ∧ b.2 ≠ [] ∧
      (∀ s ∈ b.2, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false) := by
    intro b hb
    dsimp [blocks] at hb
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
          have hpm1 : p.1 ∈ (inst.elements.zip sel).map Prod.fst := by
            exact List.mem_map.mpr ⟨p, hpm, rfl⟩
          rw [List.map_fst_zip] at hpm1
          · exact hpm1
          · exact Nat.le_of_eq hsel_len.symm
        have hd : 0 < (Nat.digits 2 p.1).length := by
          exact List.length_pos_iff_ne_nil.mpr
            (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt (hpos p.1 hp1mem)))
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
  have hjl : joinLists (blocks.map (fun b => [b.1] ++ b.2)) =
      encodeElementsSymWithSel inst.elements sel := by
    dsimp [blocks, encodeElementsSymWithSel]
    simp only [List.map_map, Function.comp_def]
  have hlen_eq : (joinLists (blocks.map (fun b => [b.1] ++ b.2))).length = eb.length := by
    rw [hjl]
    exact encodeElementsSymWithSel_length_eq inst.elements sel hsel_len
  have hB_le : blocks.length ≤ eb.length := by
    have h1 : ∀ l : List (Sym × List Sym), l.length ≤
        (joinLists (l.map (fun b => [b.1] ++ b.2))).length := by
      intro l
      induction l with
      | nil => simp
      | cons bl rest ih =>
          have hf1 : 1 ≤ ([bl.1] ++ bl.2).length := by simp
          simp only [List.length_cons, List.map_cons, joinLists_cons, List.length_append]
          omega
    have h2 := h1 blocks
    rw [hlen_eq] at h2
    exact h2
  have heb_pos : (0 : ℤ) < (eb.length : ℤ) := by
    have h1 := encodeElementsSymWithSel_length_pos inst.elements sel hne hsel_len
    have h2 : (encodeElementsSymWithSel inst.elements sel).length = eb.length :=
      encodeElementsSymWithSel_length_eq inst.elements sel hsel_len
    omega
  have htape3_eq : ∀ i : ℤ, i ≠ p₃ → tape3 i = tape i := by
    intro i hi
    simp [tape3, hi]
  have hpos_sweep : ∀ b ∈ blocks, blockTopIs1 b := by
    intro b hb
    dsimp [blocks] at hb
    rcases List.mem_map.mp hb with ⟨p, hpm, hb⟩
    rw [← hb]
    intro hne
    have hv : 0 < p.1 := hpos p.1 (by
      have hpm1 : p.1 ∈ (inst.elements.zip sel).map Prod.fst := List.mem_map.mpr ⟨p, hpm, rfl⟩
      rw [List.map_fst_zip] at hpm1
      · exact hpm1
      · exact Nat.le_of_eq hsel_len.symm)
    have htop1 := encodeBitsSymNative_top_data1 p.1 hv
    simpa using congrArg (fun s : Sym => s.1) htop1
  have hels_chosen : tapeAgrees tape3 p₀ (joinLists (blocks.map (fun b => [b.1] ++ b.2))) := by
    intro i hi
    have hi' : i < (encodeElementsSymWithSel inst.elements sel).length := by rwa [← hjl]
    have hne_i : p₀ + (i : ℤ) ≠ p₃ := by
      dsimp [p₀, p₃]
      have := heb_pos
      omega
    rw [htape3_eq _ hne_i]
    simpa [← hjl, p₀, tb] using hels i hi'
  have htgt_sweep : tapeAgrees tape3 (p₀ - (tb.length : ℤ) - 1) tb := by
    have hidx : p₀ - (tb.length : ℤ) - 1 = 1 := by
      dsimp [p₀]
      ring
    rw [hidx]
    intro i hi
    have hne_i : 1 + (i : ℤ) ≠ p₃ := by
      dsimp [p₀, p₃]
      have := heb_pos
      omega
    rw [htape3_eq _ hne_i]
    exact htgt i hi
  have htgt_data' : ∀ s ∈ tb, (s.1 = SymKind.data0 ∨ s.1 = SymKind.data1) ∧ s.2 = false := by
    intro s hs
    constructor
    · exact encodeBitsSym_nonboundary inst.target s (by simpa [tb] using hs)
    · change s ∈ encodeBitsSym inst.target at hs
      unfold encodeBitsSym at hs
      rw [List.mem_map] at hs
      rcases hs with ⟨x, hx, hs⟩
      rw [← hs]
      by_cases hx0 : x = 0 <;> simp [hx0, Sym.data0, Sym.data1]
  have hne_tgt : tb ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    dsimp [tb, encodeBitsSym] at hlen
    rw [List.length_map] at hlen
    have hd : (Nat.digits 2 inst.target).length = 0 := hlen
    have hgt : 0 < (Nat.digits 2 inst.target).length := List.length_pos_iff_ne_nil.mpr
      (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt htarget))
    omega
  have htgt_top : (tb[tb.length - 1]'(Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hne_tgt)
      (by norm_num))).1 = SymKind.data1 := by
    have htop := encodeBitsSymNative_top_data1 inst.target htarget
    simpa [tb, show encodeBitsSym inst.target = encodeBitsSymNative inst.target from rfl]
      using congrArg (fun s : Sym => s.1) htop
  have hmid_sweep : tape3 (p₀ - 1) = Sym.boundary := by
    have hne_i : p₀ - 1 ≠ p₃ := by
      dsimp [p₀, p₃]
      have := heb_pos
      omega
    rw [htape3_eq _ hne_i]
    have hidx : p₀ - 1 = 1 + (tb.length : ℤ) := by
      dsimp [p₀]
      ring
    rw [hidx]
    exact hbnd0
  have hleft_sweep : tape3 (p₀ - (tb.length : ℤ) - 2) = Sym.boundary := by
    have hne_i : p₀ - (tb.length : ℤ) - 2 ≠ p₃ := by
      dsimp [p₀, p₃]
      have := heb_pos
      omega
    rw [htape3_eq _ hne_i]
    have hidx : p₀ - (tb.length : ℤ) - 2 = 0 := by
      dsimp [p₀]
      ring
    rw [hidx]
    exact htape0
  have hblocks_ne : blocks ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    dsimp [blocks] at hlen
    rw [List.length_map, List.length_zip, hsel_len, Nat.min_self] at hlen
    exact hne (List.eq_nil_of_length_eq_zero hlen)
  rcases format_sweep_correct_len blocks tb p₀ tape3 hblocks hpos_sweep hels_chosen htgt_sweep
    htgt_data' hne_tgt htgt_top hmid_sweep hleft_sweep hblocks_ne
    with ⟨π4, cfg4, hπ4, hs4, hhead4, htape4, hlen4⟩
  have hentry : SymConfig.mk 24 tape3 (p₀ + ((joinLists (blocks.map (fun b => [b.1] ++ b.2))).length : ℤ) - 1) =
      SymConfig.mk 24 tape3 (p₃ - 1) := by
    simp only [SymConfig.mk.injEq]
    refine ⟨trivial, trivial, ?_⟩
    rw [hlen_eq]
  have hπ4' : SymSteps VerifierSym.transition (SymConfig.mk 24 tape3 (p₃ - 1)) π4 cfg4 :=
    hentry ▸ hπ4
  refine ⟨[step3] ++ π4, cfg4, ?_, hs4, ?_, ?_, ?_⟩
  · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 3 tape p₃)
      (SymConfig.mk 24 tape3 (p₃ - 1)) cfg4 [step3] π4 hstep3 hπ4'
  · simpa [p₀, tb] using hhead4
  · simp only [tb, eb] at hlen4 hlen_eq hB_le ⊢
    rw [List.length_append, List.length_singleton]
    omega
  · simpa [tape3, p₃, p₀, tb, eb] using htape4



-- ==================== C3-ε：段 Sr-nosel（清扫长度版 + 装配） ====================

/-- [C3-ε] 状态 21 清除扫描（scanClear21 长度版）：从带头 p 出发（p 处为 data），右扫 n+1 格写 data0，
    遇 sel/nosel → 51（还有下一个元素），遇 boundary → 22（#₁ → 判定）。步数账将在语句中给出。 -/
lemma scanClear21_len (n : ℕ) (p : ℤ) (tape : ℤ → Sym)
    (hstart : tape p = Sym.data0 ∨ tape p = Sym.data1 ∨ tape p = Sym.consumed)
    (hdata : ∀ i : ℕ, i < n → tape (p + 1 + (i : ℤ)) = Sym.data0 ∨
        tape (p + 1 + (i : ℤ)) = Sym.data1 ∨ tape (p + 1 + (i : ℤ)) = Sym.consumed)
    (hend : tape (p + 1 + (n : ℤ)) = Sym.sel ∨ tape (p + 1 + (n : ℤ)) = Sym.nosel ∨
        (tape (p + 1 + (n : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) π cfg' ∧
      (cfg'.state = 51 ∨ cfg'.state = 22) ∧
      (cfg'.headPos = p + (n : ℤ) ∨ cfg'.headPos = p + 1 + (n : ℤ)) ∧
      ((tape (p + 1 + (n : ℤ))).1 = SymKind.boundary → cfg'.state = 22 ∧ cfg'.headPos = p + 1 + (n : ℤ)) ∧
      ((tape (p + 1 + (n : ℤ))).1 = SymKind.sel ∨ (tape (p + 1 + (n : ℤ))).1 = SymKind.nosel →
        cfg'.state = 51 ∧ cfg'.headPos = p + (n : ℤ)) ∧
      tapeAgrees cfg'.tape p (List.replicate (n + 1) Sym.data0) ∧
      (cfg'.tape (p + 1 + (n : ℤ)) = Sym.sel ∨
        cfg'.tape (p + 1 + (n : ℤ)) = Sym.nosel ∨ (cfg'.tape (p + 1 + (n : ℤ))).1 = SymKind.boundary) ∧
      (∀ i : ℤ, i < p → cfg'.tape i = tape i) ∧
      (cfg'.tape (p + 1 + (n : ℤ)) = tape (p + 1 + (n : ℤ))) ∧
      (∀ i : ℤ, p + 1 + (n : ℤ) < i → cfg'.tape i = tape i) ∧
      π.length = n + 2 := by
  induction n generalizing p tape hstart with
  | zero =>
      -- 只有选择位（p 处）是 data，hend 在 p+1：21 读 data → 21 写 data0 R，再读结束符收尾
      let r1 : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
      let step1 : SymStep := { fromState := 21, readSym := tape p, result := r1 }
      have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step1]
          (symStepConfig (SymConfig.mk 21 tape p) step1.result) := by
        refine SymSteps.cons [] step1 (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · change step1.result ∈ VerifierSym.transition (21, tape p)
          exact trans21_data (tape p) (by
            have h1 : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨ (tape p).1 = SymKind.consumed := by
              rcases hstart with h | h | h <;> simp [h, Sym.data0, Sym.data1, Sym.consumed]
            exact h1)
      let tape1 : ℤ → Sym := fun i => if i = p then Sym.data0 else tape i
      have hcfg1 : symStepConfig (SymConfig.mk 21 tape p) step1.result = SymConfig.mk 21 tape1 (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step1, r1, tape1, Dir.toInt]
      rcases hend with hsel | hnosel | hbound
      · -- sel → 51 L
        let r2 : SymTransResult := { nextState := 51, writeSym := tape (p + 1), moveDir := Dir.L }
        let step2 : SymStep := { fromState := 21, readSym := tape (p + 1), result := r2 }
        have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) [step2]
            (symStepConfig (SymConfig.mk 21 tape1 (p + 1)) step2.result) := by
          refine SymSteps.cons [] step2 (SymConfig.mk 21 tape1 (p + 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · simp [step2, tape1]
          · change step2.result ∈ VerifierSym.transition (21, tape1 (p + 1))
            simp [tape1]
            have hk1 : (tape (p + 1)).1 = SymKind.sel := by
              have h := congrArg (fun s : Sym => s.1) hsel
              simpa [Sym.sel] using h
            exact (trans21_end (tape (p + 1)) (Or.inl hk1)).1 (Or.inl hk1)
        refine ⟨[step1, step2], symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result,
          SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p) (SymConfig.mk 21 tape1 (p + 1))
            (symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result)
            [step1] [step2] ?_ hstep2, ?_⟩
        · simpa [hcfg1] using hstep1
        · -- 结论：state = 51，headPos = p，replicate 1，保持
          refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact Or.inl (by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt])
          · intro hb
            exfalso
            have hb' : (tape (p + 1)).1 = SymKind.boundary := by simpa using hb
            have hsel' : (tape (p + 1)).1 = SymKind.sel := by
              have h := congrArg (fun s : Sym => s.1) hsel
              simpa [Sym.sel] using h
            rw [hsel'] at hb'
            cases hb'
          · intro h
            exact ⟨rfl, by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]⟩
          · -- tapeAgrees replicate 1
            intro i hi
            have hi0 : i = 0 := by
              simp at hi
              omega
            subst i
            simp [List.getElem_replicate, symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · left
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
            simpa using hsel
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp
      · -- nosel → 51 L
        let r2 : SymTransResult := { nextState := 51, writeSym := tape (p + 1), moveDir := Dir.L }
        let step2 : SymStep := { fromState := 21, readSym := tape (p + 1), result := r2 }
        have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) [step2]
            (symStepConfig (SymConfig.mk 21 tape1 (p + 1)) step2.result) := by
          refine SymSteps.cons [] step2 (SymConfig.mk 21 tape1 (p + 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · simp [step2, tape1]
          · change step2.result ∈ VerifierSym.transition (21, tape1 (p + 1))
            simp [tape1]
            have hk1 : (tape (p + 1)).1 = SymKind.nosel := by
              have h := congrArg (fun s : Sym => s.1) hnosel
              simpa [Sym.nosel] using h
            exact (trans21_end (tape (p + 1)) (Or.inr (Or.inl hk1))).1 (Or.inr hk1)
        refine ⟨[step1, step2], symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result,
          SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p) (SymConfig.mk 21 tape1 (p + 1))
            (symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result)
            [step1] [step2] ?_ hstep2, ?_⟩
        · simpa [hcfg1] using hstep1
        · refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact Or.inl (by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt])
          · intro hb
            exfalso
            have hb' : (tape (p + 1)).1 = SymKind.boundary := by simpa using hb
            have hnosel' : (tape (p + 1)).1 = SymKind.nosel := by
              have h := congrArg (fun s : Sym => s.1) hnosel
              simpa [Sym.nosel] using h
            rw [hnosel'] at hb'
            cases hb'
          · intro h
            exact ⟨rfl, by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]⟩
          · intro i hi
            have hi0 : i = 0 := by
              simp at hi
              omega
            subst i
            simp [List.getElem_replicate, symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · right; left
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
            simpa using hnosel
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp
      · -- boundary → 22 S（#₁ → 判定）
        let r2 : SymTransResult := { nextState := 22, writeSym := tape (p + 1), moveDir := Dir.S }
        let step2 : SymStep := { fromState := 21, readSym := tape (p + 1), result := r2 }
        have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape1 (p + 1)) [step2]
            (symStepConfig (SymConfig.mk 21 tape1 (p + 1)) step2.result) := by
          refine SymSteps.cons [] step2 (SymConfig.mk 21 tape1 (p + 1)) SymSteps.nil ?_ ?_ ?_
          · rfl
          · simp [step2, tape1]
          · change step2.result ∈ VerifierSym.transition (21, tape1 (p + 1))
            simp [tape1]
            have hk2 : (tape (p + 1)).1 = SymKind.boundary := by
              simpa using hbound
            exact (trans21_end (tape (p + 1)) (Or.inr (Or.inr hk2))).2 hk2
        refine ⟨[step1, step2], symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result,
          SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p) (SymConfig.mk 21 tape1 (p + 1))
            (symStepConfig (symStepConfig (SymConfig.mk 21 tape p) step1.result) step2.result)
            [step1] [step2] ?_ hstep2, ?_⟩
        · simpa [hcfg1] using hstep1
        · refine ⟨Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · right
            simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]
          · intro hb
            exact ⟨rfl, by simp [symStepConfig, step1, r1, step2, r2, Dir.toInt]⟩
          · intro h
            exfalso
            rcases h with hsel | hnosel
            · have hk : (tape (p + 1)).1 = SymKind.boundary := by simpa using hbound
              have hsel' : (tape (p + 1)).1 = SymKind.sel := by simpa using hsel
              rw [hsel'] at hk
              cases hk
            · have hk : (tape (p + 1)).1 = SymKind.boundary := by simpa using hbound
              have hnosel' : (tape (p + 1)).1 = SymKind.nosel := by simpa using hnosel
              rw [hnosel'] at hk
              cases hk
          · intro i hi
            have hi0 : i = 0 := by
              simp at hi
              omega
            subst i
            simp [List.getElem_replicate, symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · right; right
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
            simpa using hbound
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt]
          · intro j hj
            have hj1 : j ≠ p + 1 := by omega
            have hj2 : j ≠ p := by omega
            simp [symStepConfig, step1, r1, step2, r2, tape1, Dir.toInt, hj1, hj2]
          · simp
  | succ n ih =>
      -- 先清 p 处（选择位），再递归清 p+1 起的 n+1 个
      let r1 : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
      let step1 : SymStep := { fromState := 21, readSym := tape p, result := r1 }
      have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 21 tape p) [step1]
          (symStepConfig (SymConfig.mk 21 tape p) step1.result) := by
        refine SymSteps.cons [] step1 (SymConfig.mk 21 tape p) SymSteps.nil ?_ ?_ ?_
        · rfl
        · rfl
        · change step1.result ∈ VerifierSym.transition (21, tape p)
          exact trans21_data (tape p) (by
            have h1 : (tape p).1 = SymKind.data0 ∨ (tape p).1 = SymKind.data1 ∨ (tape p).1 = SymKind.consumed := by
              rcases hstart with h | h | h <;> simp [h, Sym.data0, Sym.data1, Sym.consumed]
            exact h1)
      let tape1 : ℤ → Sym := fun i => if i = p then Sym.data0 else tape i
      have hcfg1 : symStepConfig (SymConfig.mk 21 tape p) step1.result = SymConfig.mk 21 tape1 (p + 1) := by
        simp [symStepConfig, SymConfig.mk, step1, r1, tape1, Dir.toInt]
      have hstart' : tape1 (p + 1) = Sym.data0 ∨ tape1 (p + 1) = Sym.data1 ∨ tape1 (p + 1) = Sym.consumed := by
        have hlt : p + 1 ≠ p := by omega
        simp [tape1, hlt]
        simpa using hdata 0 (by omega)
      have hdata' : ∀ i : ℕ, i < n → tape1 (p + 1 + 1 + (i : ℤ)) = Sym.data0 ∨
          tape1 (p + 1 + 1 + (i : ℤ)) = Sym.data1 ∨ tape1 (p + 1 + 1 + (i : ℤ)) = Sym.consumed := by
        intro i hi
        have h : tape (p + 1 + ((i + 1 : ℕ) : ℤ)) = Sym.data0 ∨
            tape (p + 1 + ((i + 1 : ℕ) : ℤ)) = Sym.data1 ∨ tape (p + 1 + ((i + 1 : ℕ) : ℤ)) = Sym.consumed :=
          hdata (i + 1) (by omega)
        have hpos : p + 1 + 1 + (i : ℤ) = p + 1 + ((i : ℤ) + 1) := by omega
        have hneq : p + 1 + ((i : ℤ) + 1) ≠ p := by omega
        rw [hpos]
        simp [tape1, hneq]
        simpa using h
      have hend' : tape1 (p + 1 + 1 + (n : ℤ)) = Sym.sel ∨ tape1 (p + 1 + 1 + (n : ℤ)) = Sym.nosel ∨
          (tape1 (p + 1 + 1 + (n : ℤ))).1 = SymKind.boundary := by
        have hpos : p + 1 + 1 + (n : ℤ) = p + 1 + ((n : ℤ) + 1) := by omega
        have hneq : p + 1 + ((n : ℤ) + 1) ≠ p := by omega
        rw [hpos]
        simp [tape1, hneq]
        simpa using hend
      rcases ih (p + 1) tape1 hstart' hdata' hend' with ⟨π, cfg', hπ, hs, hhead, hb22, hsel51, hta, hbnd, hleft, hkeep, hright, hlen'⟩
      refine ⟨[step1] ++ π, cfg', SymSteps_trans VerifierSym.transition (SymConfig.mk 21 tape p)
        (SymConfig.mk 21 tape1 (p + 1)) cfg' [step1] π ?_ hπ, ?_⟩
      · simpa [hcfg1] using hstep1
      · refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rcases hhead with hh | hh
          · left
            rw [hh]
            omega
          · right
            rw [hh]
            omega
        · intro hb
          have hb2 : (tape1 ((p + 1) + 1 + ↑n)).1 = SymKind.boundary := by
            rw [show (p + 1) + 1 + ↑n = p + 1 + (↑n + 1) from by omega]
            have hne : p + 1 + (↑n + 1) ≠ p := by omega
            simp [tape1, hne]
            rwa [show p + 1 + (↑n + 1) = p + 1 + ↑(n + 1) from by omega]
          simpa [show (p + 1) + 1 + ↑n = p + 1 + ↑(n + 1) from by omega] using hb22 hb2
        · intro h
          have h2 : (tape1 ((p + 1) + 1 + ↑n)).1 = SymKind.sel ∨ (tape1 ((p + 1) + 1 + ↑n)).1 = SymKind.nosel := by
            rw [show (p + 1) + 1 + ↑n = p + 1 + (↑n + 1) from by omega]
            have hne : p + 1 + (↑n + 1) ≠ p := by omega
            simp [tape1, hne]
            rwa [show p + 1 + (↑n + 1) = p + 1 + ↑(n + 1) from by omega]
          simpa [show p + 1 + ↑n = p + (↑n + 1) from by omega] using hsel51 h2
        · -- tapeAgrees：p 处 data0 而 p+1 起的由 hta
          intro i hi
          by_cases hi0 : i = 0
          · subst i
            have h := hleft p (by omega)
            simpa [tape1] using h
          · have hi' : i - 1 < (List.replicate (n + 1) Sym.data0).length := by
              simp at hi ⊢
              omega
            have h := hta (i - 1) hi'
            -- 组装：replicate (n+2) 的第 i 格 = data0
            have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
            have hnat : (i - 1 : ℕ) + 1 = i := Nat.sub_add_cancel hi1
            have hsub : ((i - 1 : ℕ) : ℤ) + 1 = (i : ℤ) := by
              rw [← hnat]
              simp
            have hpos : p + 1 + ((i - 1 : ℕ) : ℤ) = p + (i : ℤ) := by
              calc
                p + 1 + ((i - 1 : ℕ) : ℤ) = p + (((i - 1 : ℕ) : ℤ) + 1) := by ring
                _ = p + (i : ℤ) := by rw [hsub]
            simp [List.getElem_replicate]
            rw [← hpos]
            simpa using h
        · rw [show p + 1 + ↑(n + 1) = p + 1 + 1 + ↑n from by omega]
          exact hbnd
        · intro j hj
          have hj1 : j ≠ p := by omega
          simpa [tape1, hj1] using hleft j (by omega)
        · rw [show p + 1 + ↑(n + 1) = p + 1 + 1 + ↑n from by omega]
          simpa [tape1, show p + 1 + 1 + (n : ℤ) ≠ p from by omega] using hkeep
        · intro i hi
          have hi' : p + 1 + 1 + (n : ℤ) < i := by omega
          have h := hright i hi'
          simpa [tape1, show i ≠ p from by omega] using h
        · rw [List.length_append, List.length_cons, List.length_nil, hlen']
          omega


/-- [C3-ε] 清一个 nosel 元素（clear_element_correct 长度版）：状态 4、带头 nosel 位置 p_e、
    元素值位 ebits（在 p_e+1 起）→ 51/22 双出口 + 全清零 + 帧保持。步数账将在语句中给出。 -/
lemma clear_element_correct_len (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hsel : tape p_e = Sym.nosel)
    (hbound₀ : tape (p_e - 1) = Sym.boundary)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      (cfg'.state = 51 ∨ cfg'.state = 22) ∧
      (cfg'.headPos = p_e + (ebits.length : ℤ) ∨ cfg'.headPos = p_e + 1 + (ebits.length : ℤ)) ∧
      ((tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary → cfg'.state = 22 ∧ cfg'.headPos = p_e + 1 + (ebits.length : ℤ)) ∧
      ((tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.sel ∨ (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.nosel →
        cfg'.state = 51 ∧ cfg'.headPos = p_e + (ebits.length : ℤ)) ∧
      tapeAgrees cfg'.tape (p_e + 1) (List.replicate ebits.length Sym.data0) ∧
      (cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (cfg'.tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) ∧
      cfg'.tape (p_e - 1) = Sym.data0 ∧
      cfg'.tape p_e = Sym.data0 ∧
      (∀ i : ℤ, i < p_e - 1 → cfg'.tape i = tape i) ∧
      (cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ))) ∧
      (∀ i : ℤ, p_e + 1 + (ebits.length : ℤ) < i → cfg'.tape i = tape i) ∧
      π.length = ebits.length + 4 := by
  let r1 : SymTransResult := { nextState := 20, writeSym := Sym.data0, moveDir := Dir.L }
  let step1 : SymStep := { fromState := 4, readSym := Sym.nosel, result := r1 }
  have hstep1 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step1]
      (symStepConfig (SymConfig.mk 4 tape p_e) step1.result) := by
    refine SymSteps.cons [] step1 (SymConfig.mk 4 tape p_e) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.nosel = tape p_e
      rw [hsel]
    · change step1.result ∈ VerifierSym.transition (4, tape p_e)
      rw [hsel]
      decide
  let tape1 : ℤ → Sym := fun i => if i = p_e then Sym.data0 else tape i
  have hcfg1 : symStepConfig (SymConfig.mk 4 tape p_e) step1.result =
      SymConfig.mk 20 tape1 (p_e - 1) := by
    simp [symStepConfig, SymConfig.mk, step1, r1, tape1, Dir.toInt]
    omega
  let r2 : SymTransResult := { nextState := 21, writeSym := Sym.data0, moveDir := Dir.R }
  let step2 : SymStep := { fromState := 20, readSym := Sym.boundary, result := r2 }
  have hstep2 : SymSteps VerifierSym.transition (SymConfig.mk 20 tape1 (p_e - 1)) [step2]
      (symStepConfig (SymConfig.mk 20 tape1 (p_e - 1)) step2.result) := by
    refine SymSteps.cons [] step2 (SymConfig.mk 20 tape1 (p_e - 1)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.boundary = tape1 (p_e - 1)
      have hne : p_e - 1 ≠ p_e := by omega
      simp [tape1, hne]
      exact hbound₀.symm
    · change step2.result ∈ VerifierSym.transition (20, tape1 (p_e - 1))
      have hne : p_e - 1 ≠ p_e := by omega
      simp [tape1, hne]
      rw [hbound₀]
      decide
  let tape2 : ℤ → Sym := fun i => if i = p_e - 1 then Sym.data0 else tape1 i
  have hcfg2 : symStepConfig (SymConfig.mk 20 tape1 (p_e - 1)) step2.result =
      SymConfig.mk 21 tape2 p_e := by
    simp [symStepConfig, SymConfig.mk, step2, r2, tape2, tape1, Dir.toInt]
  have hstart2 : tape2 p_e = Sym.data0 ∨ tape2 p_e = Sym.data1 ∨ tape2 p_e = Sym.consumed := by
    have hne : p_e ≠ p_e - 1 := by omega
    simp [tape2, tape1, hne]
  have hdata2 : ∀ i : ℕ, i < ebits.length → tape2 (p_e + 1 + (i : ℤ)) = Sym.data0 ∨
      tape2 (p_e + 1 + (i : ℤ)) = Sym.data1 ∨ tape2 (p_e + 1 + (i : ℤ)) = Sym.consumed := by
    intro i hi
    have hne1 : p_e + 1 + (i : ℤ) ≠ p_e := by omega
    have hne2 : p_e + 1 + (i : ℤ) ≠ p_e - 1 := by omega
    simp [tape2, tape1, hne1, hne2]
    have h := helem i (by simpa [bitsToSym] using hi)
    by_cases hb : ebits[i]
    · right; left
      simpa [bitsToSym, hb] using h
    · left
      simpa [bitsToSym, hb] using h
  have hend2 : tape2 (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
      tape2 (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
      (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
    have hne1 : p_e + 1 + (ebits.length : ℤ) ≠ p_e := by omega
    have hne2 : p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 := by omega
    simp [tape2, tape1, hne1, hne2]
    exact hend
  rcases scanClear21_len ebits.length p_e tape2 hstart2 hdata2 hend2 with ⟨π, cfg', hπ, hs, hhead, hb22, hsel51, hta, hbnd, hleft, hkeep, hright, hlen_clear⟩
  have hta' : tapeAgrees cfg'.tape (p_e + 1) (List.replicate ebits.length Sym.data0) := by
    intro i hi
    have h := hta (i + 1) (by
      simpa using hi)
    have hpos : p_e + 1 + (i : ℤ) = p_e + ((i + 1 : ℕ) : ℤ) := by
      rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by norm_num]
      ring
    rw [hpos]
    exact h
  have hmark : cfg'.tape p_e = Sym.data0 := by
    have h := hta 0 (by simp)
    simpa using h
  refine ⟨[step1, step2] ++ π, cfg', ?_, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstep1' : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step1]
        (SymConfig.mk 20 tape1 (p_e - 1)) := by
      simpa [hcfg1] using hstep1
    have hstep2' : SymSteps VerifierSym.transition (SymConfig.mk 20 tape1 (p_e - 1)) [step2]
        (SymConfig.mk 21 tape2 p_e) := by
      simpa [hcfg2] using hstep2
    have h12 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) [step1, step2]
        (SymConfig.mk 21 tape2 p_e) := by
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 20 tape1 (p_e - 1))
        (SymConfig.mk 21 tape2 p_e) [step1] [step2] hstep1' hstep2'
    exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e) (SymConfig.mk 21 tape2 p_e) cfg'
      [step1, step2] π h12 hπ
  · exact hhead
  · -- boundary 右端 → 22（由 scanClear21 的 hb22，把 tape2 还原为 tape）
    intro hb
    have hb2 : (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary := by
      rw [show tape2 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape2, tape1,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 from by omega,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e from by omega]]
      exact hb
    exact hb22 hb2
  · -- sel/nosel 右端 → 51（由 scanClear21 的 hsel51，把 tape2 还原为 tape）
    intro h
    have hb2' : (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.sel ∨
        (tape2 (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.nosel := by
      rw [show tape2 (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ)) from by
        simp [tape2, tape1,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 from by omega,
          show p_e + 1 + (ebits.length : ℤ) ≠ p_e from by omega]]
      exact h
    exact hsel51 hb2'
  · exact hta'
  · exact hbnd
  · -- p_e - 1 位置 = data0（状态 20 读 #₀ 时写入）
    have h := hleft (p_e - 1) (by omega)
    rw [h]
    simp [tape2, tape1]
  · exact hmark
  · intro i hi
    have hi' : i < p_e := by omega
    have h := hleft i hi'
    have hne1 : i ≠ p_e - 1 := by omega
    have hne2 : i ≠ p_e := by omega
    rw [h]
    simp [tape2, tape1, hne1, hne2]
  · rw [hkeep]
    simp [tape2, tape1,
      show p_e + 1 + (ebits.length : ℤ) ≠ p_e from by omega,
      show p_e + 1 + (ebits.length : ℤ) ≠ p_e - 1 from by omega]
  · intro i hi
    have h := hright i hi
    have hne1 : i ≠ p_e - 1 := by omega
    have hne2 : i ≠ p_e := by omega
    rw [h]
    simp [tape2, tape1, hne1, hne2]
  · rw [List.length_append, List.length_cons, List.length_cons, List.length_nil, hlen_clear]
    omega



/-- [C3-ε] 段 Sr-nosel（整轮·nosel 元素）：状态 4、带头 nosel 位置 p_e、#₀ 于 p_e−1、位段 ebits →
    · 非末元素（终结符 sel/nosel）：状态 4、头 = 下一元素标记 e' = p_e+1+n、新 #₀ 于 e'−1（[51] 盖章）；
    · 末元素（终结符 boundary = #₁）：状态 22、头 = #₁。
    销毁区 [p_e−1, p_e+n−1] 清零；帧保持；终结符格保持；恰 ≤ n+5 步（sel 分支 n+5、boundary 分支 n+4）。 -/
lemma segSrNosel (ebits : List Bool) (p_e : ℤ) (tape : ℤ → Sym)
    (hsel : tape p_e = Sym.nosel)
    (hbound₀ : tape (p_e - 1) = Sym.boundary)
    (helem : tapeAgrees tape (p_e + 1) (bitsToSym ebits))
    (hend : tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
        tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π cfg' ∧
      π.length ≤ ebits.length + 5 ∧
      ((tape (p_e + 1 + (ebits.length : ℤ)) = Sym.sel ∨
          tape (p_e + 1 + (ebits.length : ℤ)) = Sym.nosel) →
        cfg'.state = 4 ∧ cfg'.headPos = p_e + (ebits.length : ℤ) + 1 ∧
        cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.boundary ∧
        cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ))) ∧
      ((tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary →
        cfg'.state = 22 ∧ cfg'.headPos = p_e + 1 + (ebits.length : ℤ)) ∧
      tapeAgrees cfg'.tape (p_e - 1) (List.replicate (ebits.length + 1) Sym.data0) ∧
      (∀ i : ℤ, i < p_e - 1 → cfg'.tape i = tape i) ∧
      (∀ i : ℤ, p_e + 1 + (ebits.length : ℤ) < i → cfg'.tape i = tape i) ∧
      (cfg'.tape (p_e + 1 + (ebits.length : ℤ)) = tape (p_e + 1 + (ebits.length : ℤ))) ∧
      ((tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary →
        cfg'.tape (p_e + (ebits.length : ℤ)) = Sym.data0) := by

  rcases clear_element_correct_len ebits p_e tape hsel hbound₀ helem hend with
    ⟨π₀, cfg₀, hπ₀, _hs₀, _hhead₀, hb22₀, hsel51₀, hta₀, hbnd₀, hp1₀, hp2₀, hleft₀, hkeep₀, hright₀, hlen₀⟩
  by_cases hterm : (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.boundary
  · -- ===== 末元素（boundary → 22）：直接出口，无 [51] 步 =====
    have hb22 := hb22₀ hterm
    refine ⟨π₀, cfg₀, hπ₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · intro h
      rcases h with h' | h'
      · have hA : (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.sel := by rw [h']; rfl
        rw [hA] at hterm
        cases hterm
      · have hA : (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.nosel := by rw [h']; rfl
        rw [hA] at hterm
        cases hterm
    · intro _
      exact hb22
    · -- 销毁区（p_e−1 起 n+1 格）
      intro i hi
      simp only [List.length_replicate] at hi
      rcases i with _ | _ | k
      · show cfg₀.tape (p_e - 1 + (0 : ℤ)) = (List.replicate (ebits.length + 1) Sym.data0)[0]
        rw [show p_e - 1 + (0 : ℤ) = p_e - 1 from by ring, hp1₀]
        simp
      · show cfg₀.tape (p_e - 1 + (1 : ℕ)) = (List.replicate (ebits.length + 1) Sym.data0)[1]
        rw [show p_e - 1 + ((1 : ℕ) : ℤ) = p_e from by ring, hp2₀]
        simp
      · have hk : k < ebits.length := by omega
        have h := hta₀ k (by simp only [List.length_replicate]; omega)
        rw [show p_e - 1 + (((k + 2 : ℕ)) : ℤ) = p_e + 1 + (k : ℤ) from by omega]
        rw [h]
        simp
    · exact hleft₀
    · exact hright₀
    · exact hkeep₀
    · intro _
      by_cases h0 : ebits.length = 0
      · show cfg₀.tape (p_e + ((ebits.length : ℕ) : ℤ)) = Sym.data0
        rw [h0]
        simpa using hp2₀
      · have hidx : p_e + (ebits.length : ℤ) = p_e + 1 + (((ebits.length - 1 : ℕ)) : ℤ) := by omega
        rw [hidx]
        have hk : ebits.length - 1 < (List.replicate ebits.length Sym.data0).length := by
          simp only [List.length_replicate]
          omega
        rw [hta₀ (ebits.length - 1) hk]
        simp
  · -- ===== 非末元素（sel/nosel → [51] 盖章）=====
    have hsel'K : (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.sel ∨
        (tape (p_e + 1 + (ebits.length : ℤ))).1 = SymKind.nosel := by
      rcases hend with h | h | h
      · left; rw [h]; rfl
      · right; rw [h]; rfl
      · exact absurd h hterm
    have h51 := hsel51₀ hsel'K
    have hst51 : cfg₀.state = 51 := h51.1
    have hhead51 : cfg₀.headPos = p_e + (ebits.length : ℤ) := h51.2
    have hcell : cfg₀.tape (p_e + (ebits.length : ℤ)) = Sym.data0 := by
      by_cases h0 : ebits.length = 0
      · show cfg₀.tape (p_e + ((ebits.length : ℕ) : ℤ)) = Sym.data0
        rw [h0]
        simpa using hp2₀
      · have hidx : p_e + (ebits.length : ℤ) = p_e + 1 + (((ebits.length - 1 : ℕ)) : ℤ) := by omega
        rw [hidx]
        have hk : ebits.length - 1 < (List.replicate ebits.length Sym.data0).length := by
          simp only [List.length_replicate]
          omega
        rw [hta₀ (ebits.length - 1) hk]
        simp
    let r51 : SymTransResult := { nextState := 4, writeSym := Sym.boundary, moveDir := Dir.R }
    let step51 : SymStep := { fromState := 51, readSym := Sym.data0, result := r51 }
    have hstep51 : SymSteps VerifierSym.transition (SymConfig.mk 51 cfg₀.tape cfg₀.headPos) [step51]
        (symStepConfig (SymConfig.mk 51 cfg₀.tape cfg₀.headPos) step51.result) := by
      refine SymSteps.cons [] step51 (SymConfig.mk 51 cfg₀.tape cfg₀.headPos) SymSteps.nil ?_ ?_ ?_
      · rfl
      · change Sym.data0 = cfg₀.tape cfg₀.headPos
        rw [hhead51]
        exact hcell.symm
      · change step51.result ∈ VerifierSym.transition (51, cfg₀.tape cfg₀.headPos)
        rw [hhead51, hcell]
        decide
    let tape51 : ℤ → Sym := fun i =>
      if i = p_e + (ebits.length : ℤ) then Sym.boundary else cfg₀.tape i
    have hc51 : SymConfig.mk 51 cfg₀.tape cfg₀.headPos = cfg₀ := by
      rw [← hst51]
    have hcfg51 : symStepConfig (SymConfig.mk 51 cfg₀.tape cfg₀.headPos) step51.result =
        SymConfig.mk 4 tape51 (p_e + (ebits.length : ℤ) + 1) := by
      simp [symStepConfig, step51, r51, tape51, hhead51, Dir.toInt]
    have hπ : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) (π₀ ++ [step51])
        (SymConfig.mk 4 tape51 (p_e + (ebits.length : ℤ) + 1)) := by
      have h0 : SymSteps VerifierSym.transition (SymConfig.mk 4 tape p_e) π₀
          (SymConfig.mk 51 cfg₀.tape cfg₀.headPos) := hc51.symm ▸ hπ₀
      have hs51' : SymSteps VerifierSym.transition (SymConfig.mk 51 cfg₀.tape cfg₀.headPos) [step51]
          (SymConfig.mk 4 tape51 (p_e + (ebits.length : ℤ) + 1)) := hcfg51 ▸ hstep51
      exact SymSteps_trans VerifierSym.transition (SymConfig.mk 4 tape p_e)
        (SymConfig.mk 51 cfg₀.tape cfg₀.headPos)
        (SymConfig.mk 4 tape51 (p_e + (ebits.length : ℤ) + 1)) π₀ [step51] h0 hs51'
    refine ⟨π₀ ++ [step51], SymConfig.mk 4 tape51 (p_e + (ebits.length : ℤ) + 1), hπ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, hlen₀, List.length_singleton]
    · intro _
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [tape51]
      · simp [tape51]
      · have hne : p_e + 1 + (ebits.length : ℤ) ≠ p_e + (ebits.length : ℤ) := by omega
        simp only [tape51, hne, ↓reduceIte]
        exact hkeep₀
    · intro h
      exact absurd (by simpa using h) hterm
    · -- 销毁区（tape51 未触及 p_e+n 以外）
      intro i hi
      simp only [List.length_replicate] at hi
      have hi' : (i : ℤ) ≤ (ebits.length : ℤ) := by omega
      have hne : p_e - 1 + (i : ℤ) ≠ p_e + (ebits.length : ℤ) := by omega
      simp only [tape51, hne, ↓reduceIte]
      rcases i with _ | _ | k
      · show cfg₀.tape (p_e - 1 + (0 : ℤ)) = (List.replicate (ebits.length + 1) Sym.data0)[0]
        rw [show p_e - 1 + (0 : ℤ) = p_e - 1 from by ring, hp1₀]
        simp
      · show cfg₀.tape (p_e - 1 + ((1 : ℕ) : ℤ)) = (List.replicate (ebits.length + 1) Sym.data0)[1]
        rw [show p_e - 1 + ((1 : ℕ) : ℤ) = p_e from by ring, hp2₀]
        simp
      · have hk : k < ebits.length := by omega
        have h := hta₀ k (by simp only [List.length_replicate]; omega)
        rw [show p_e - 1 + (((k + 2 : ℕ)) : ℤ) = p_e + 1 + (k : ℤ) from by omega]
        rw [h]
        simp
    · intro i hi
      have hne : i ≠ p_e + (ebits.length : ℤ) := by omega
      simp only [tape51, hne, ↓reduceIte]
      exact hleft₀ i hi
    · intro i hi
      have hne : i ≠ p_e + (ebits.length : ℤ) := by omega
      simp only [tape51, hne, ↓reduceIte]
      exact hright₀ i hi
    · have hne : p_e + 1 + (ebits.length : ℤ) ≠ p_e + (ebits.length : ℤ) := by omega
      simp only [tape51, hne, ↓reduceIte]
      exact hkeep₀
    · intro h
      exact absurd (by simpa using h) hterm


/-- [C3-η 段 S3] 判定段：状态 22 @ #₁（mark ⟨boundary,true⟩）→ [22] 西进一格 → [23] 西扫全 0 检查
    （余 1 → 101 被 100-only 排除）→ 至 #ₗ → 状态 100。
    结论：状态 100 @ #ₗ+1，带保持不变；恰 n+2 步（n = #ₗ 与 #₁ 之间的 d₀ 格数）。 -/
lemma segS3 (n : ℕ) (q : ℤ) (tape : ℤ → Sym)
    (hmark : tape (q + (n : ℤ) + 1) = Sym.mk SymKind.boundary true)
    (hzero : ∀ i : ℤ, q < i → i ≤ q + (n : ℤ) → tape i = Sym.data0)
    (hbnd : tape q = Sym.boundary) :
    ∃ π cfg', SymSteps VerifierSym.transition (SymConfig.mk 22 tape (q + (n : ℤ) + 1)) π cfg' ∧
      π.length ≤ n + 2 ∧
      cfg'.state = 100 ∧
      cfg'.headPos = q + 1 ∧
      cfg'.tape = tape := by
  let r22 : SymTransResult := { nextState := 23, writeSym := Sym.mk SymKind.boundary true, moveDir := Dir.L }
  let step22 : SymStep := { fromState := 22, readSym := Sym.mk SymKind.boundary true, result := r22 }
  have hstep22 : SymSteps VerifierSym.transition (SymConfig.mk 22 tape (q + (n : ℤ) + 1)) [step22]
      (symStepConfig (SymConfig.mk 22 tape (q + (n : ℤ) + 1)) step22.result) := by
    refine SymSteps.cons [] step22 (SymConfig.mk 22 tape (q + (n : ℤ) + 1)) SymSteps.nil ?_ ?_ ?_
    · rfl
    · change Sym.mk SymKind.boundary true = tape (q + (n : ℤ) + 1)
      exact hmark.symm
    · change step22.result ∈ VerifierSym.transition (22, tape (q + (n : ℤ) + 1))
      rw [hmark]
      decide
  have htape22 : (fun i => if i = q + (n : ℤ) + 1 then Sym.mk SymKind.boundary true else tape i) = tape := by
    funext i
    by_cases h : i = q + (n : ℤ) + 1
    · rw [h, if_pos rfl]
      exact hmark.symm
    · simp [h]
  have hhead22 : (q + (n : ℤ) + 1) + Dir.L.toInt = q + (n : ℤ) := by
    simp only [Dir.toInt]
    omega
  have hcfg22 : symStepConfig (SymConfig.mk 22 tape (q + (n : ℤ) + 1)) step22.result =
      SymConfig.mk 23 tape (q + (n : ℤ)) := by
    simp [symStepConfig, step22, r22, htape22, hhead22]
  rcases scanLeftKeepPos_len 23 100 Sym.boundary Dir.R n (q + (n : ℤ)) tape
      (fun i hi => by
        have hlt : q < i := by omega
        rw [hzero i hlt hi.2]
        decide)
      (by decide)
      (by rw [show q + (n : ℤ) - (n : ℤ) = q from by ring]; exact hbnd)
    with ⟨πs, cfgs, hπs, hss, hhs, hts, hlens⟩
  have h0 : SymSteps VerifierSym.transition (SymConfig.mk 22 tape (q + (n : ℤ) + 1)) [step22]
      (SymConfig.mk 23 tape (q + (n : ℤ))) := hcfg22 ▸ hstep22
  refine ⟨[step22] ++ πs, cfgs, ?_, ?_, ?_, ?_, ?_⟩
  · exact SymSteps_trans VerifierSym.transition (SymConfig.mk 22 tape (q + (n : ℤ) + 1))
      (SymConfig.mk 23 tape (q + (n : ℤ))) cfgs [step22] πs h0 hπs
  · rw [List.length_append, List.length_cons, List.length_nil, hlens]
    omega
  · exact hss
  · rw [hhs]
    simp only [Dir.toInt]
    omega
  · exact hts


end Mp
