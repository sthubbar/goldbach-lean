module

public import LeanLab.PNTPort.BV.Statements
public import LeanLab.PNTPort.BV.Helpers
public import LeanLab.PNTPort.StrongPNT.Bridge

/-!
# Bombieri-Vinogradov from Siegel-Walfisz and the large conductor estimate

lab proof, AI wrote this file, known mathematics; the result is CONDITIONAL ON the hypotheses
SiegelWalfisz and LargeConductor.

* `bombieriVinogradov_of`: `SiegelWalfisz → LargeConductor → BombieriVinogradov`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset Real ArithmeticFunction

/-- The error in one residue class, through primitive characters. -/
theorem term_le {q : ℕ} [NeZero q] (x : ℝ) {a : ℕ} (ha : a.Coprime q) :
    |HeathBrown1985.psi x q a - x / q.totient| ≤ psiBad x q +
      |Chebyshev.psi x - x| / q.totient +
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi x χ.primitiveCharacter‖) / q.totient := by
  have hφ1 : 1 ≤ q.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast hφ1
  have h1 := abs_psi_sub_le (q := q) x ha
  have hB : ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), vonMangoldt n =
      psiBad x q := rfl
  have h2 : ‖psiChi x (1 : DirichletCharacter ℂ q) - x‖ ≤
      psiBad x q + |Chebyshev.psi x - x| := by
    calc ‖psiChi x (1 : DirichletCharacter ℂ q) - x‖
        = ‖(psiChi x (1 : DirichletCharacter ℂ q) - Chebyshev.psi x) +
            ((Chebyshev.psi x : ℂ) - x)‖ := by ring_nf
      _ ≤ ‖psiChi x (1 : DirichletCharacter ℂ q) - Chebyshev.psi x‖ +
            ‖(Chebyshev.psi x : ℂ) - x‖ := norm_add_le _ _
      _ ≤ psiBad x q + |Chebyshev.psi x - x| := by
          refine add_le_add ?_ (le_of_eq ?_)
          · rw [← hB]; exact norm_psiChi_one_sub x
          · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hcard : (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) =
      q.totient - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q, Nat.cast_sub hφ1]
    simp
  have h3 : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ ≤
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi x χ.primitiveCharacter‖ + (q.totient - 1) * psiBad x q := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    apply sum_le_sum
    intro χ _
    have := norm_psiChi_sub_primitive x χ
    rw [hB] at this
    have := norm_sub_norm_le (psiChi x χ) (psiChi x χ.primitiveCharacter)
    linarith
  have key : psiBad x q + |Chebyshev.psi x - x| / q.totient +
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi x χ.primitiveCharacter‖) / q.totient =
      ((psiBad x q + |Chebyshev.psi x - x|) +
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi x χ.primitiveCharacter‖ + (q.totient - 1) * psiBad x q)) / q.totient := by
    field_simp
    ring
  rw [key]
  refine h1.trans (div_le_div_of_nonneg_right ?_ hφ.le)
  linarith

/-- The characters `χ ≠ 1` modulo `q` land injectively in primitive pairs. -/
theorem sum_erase_le_primSigma {q Q : ℕ} [NeZero q] (hqQ : q ≤ Q)
    (F : (Σ d : ℕ, DirichletCharacter ℂ d) → ℝ) (hF : ∀ p, 0 ≤ F p) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        F ⟨χ.conductor, χ.primitiveCharacter⟩ ≤
      ∑ p ∈ (primSigma Q).filter (fun p => 2 ≤ p.1 ∧ p.1 ∣ q), F p := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hinj : Set.InjOn (fun χ : DirichletCharacter ℂ q =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ d : ℕ, DirichletCharacter ℂ d))
      ((univ : Finset (DirichletCharacter ℂ q)).erase 1) := by
    intro χ _ χ' _ h
    have gen : ∀ (d d' : ℕ) (ψ : DirichletCharacter ℂ d) (ψ' : DirichletCharacter ℂ d')
        (hd : d ∣ q) (hd' : d' ∣ q),
        (⟨d, ψ⟩ : Σ d : ℕ, DirichletCharacter ℂ d) = ⟨d', ψ'⟩ →
          DirichletCharacter.changeLevel hd ψ = DirichletCharacter.changeLevel hd' ψ' := by
      rintro d d' ψ ψ' hd hd' ⟨⟩
      rfl
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ,
      ← DirichletCharacter.changeLevel_primitiveCharacter χ']
    exact gen _ _ _ _ _ _ h
  rw [← sum_image (f := F) hinj]
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => hF p)
  intro p hp
  rw [mem_image] at hp
  obtain ⟨χ, hχ, rfl⟩ := hp
  have hχ1 : χ ≠ 1 := (mem_erase.1 hχ).1
  have hdvd := DirichletCharacter.conductor_dvd_level χ
  have hc0 : χ.conductor ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have hc1 : χ.conductor ≠ 1 := fun h =>
    hχ1 ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).2 h)
  have hcq : χ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdvd
  simp only [primSigma, mem_filter, mem_sigma, mem_Icc, mem_univ, true_and]
  exact ⟨⟨⟨by omega, by omega⟩, DirichletCharacter.primitiveCharacter_isPrimitive χ⟩,
    by omega, hdvd⟩

/-- `∑_{q ≤ Q, d ∣ q} 1/φ(q) ≤ φ(d)⁻¹ ∑_{m ≤ Q} 1/φ(m)`. -/
theorem sum_dvd_inv_totient_le {d : ℕ} (hd : 1 ≤ d) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / q.totient ≤
      (1 / d.totient) * ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient := by
  have hsub : (Icc 1 Q).filter (fun q => d ∣ q) ⊆ (Icc 1 Q).image (fun m => d * m) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hq
    rw [mem_image]
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at h1
      · exact h
    exact ⟨m, mem_Icc.2 ⟨hm, le_trans (Nat.le_mul_of_pos_left m (by omega)) h2⟩, rfl⟩
  have hinj : Set.InjOn (fun m => d * m) (Icc 1 Q : Finset ℕ) := by
    intro m _ m' _ h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  calc ∑ q ∈ (Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / q.totient
      ≤ ∑ q ∈ (Icc 1 Q).image (fun m => d * m), (1 : ℝ) / q.totient :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ m ∈ Icc 1 Q, (1 : ℝ) / (d * m).totient := sum_image hinj
    _ ≤ ∑ m ∈ Icc 1 Q, (1 / d.totient) * ((1 : ℝ) / m.totient) := by
        apply sum_le_sum
        intro m hm
        rw [mem_Icc] at hm
        have hdφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have hmφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have hsm : ((d.totient * m.totient : ℕ) : ℝ) ≤ (d * m).totient := by
          exact_mod_cast Nat.totient_super_multiplicative d m
        push_cast at hsm
        rw [div_mul_div_comm, one_mul]
        exact one_div_le_one_div_of_le (by positivity) hsm
    _ = (1 / d.totient) * ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient := by rw [mul_sum]

lemma sum_range_zmod {d : ℕ} [NeZero d] (f : ZMod d → ℂ) :
    ∑ a ∈ range d, f (a : ZMod d) = ∑ z : ZMod d, f z := by
  refine Finset.sum_bij' (fun (a : ℕ) _ => (a : ZMod d)) (fun (z : ZMod d) _ => z.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro z _; exact mem_range.2 (ZMod.val_lt z)
  · intro a ha; exact ZMod.val_cast_of_lt (mem_range.1 ha)
  · intro z _; exact ZMod.natCast_zmod_val z
  · intro a _; rfl

/-- `ψ(x, χ) = ∑_{a < d} χ(a) (ψ(x; d, a) - x/φ(d))` for `χ ≠ 1`. -/
theorem psiChi_eq_sum {d : ℕ} [NeZero d] (x : ℝ) (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) :
    psiChi x χ = ∑ a ∈ range d, χ (a : ZMod d) *
      ((HeathBrown1985.psi x d a : ℂ) - (x : ℂ) / d.totient) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsum0 : ∑ a ∈ range d, χ (a : ZMod d) = 0 := by
    rw [sum_range_zmod (fun z => χ z)]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, hsum0, zero_mul, sub_zero]
  unfold psiChi
  have hmaps : ∀ n ∈ Icc 1 ⌊x⌋₊, n % d ∈ range d := fun n _ => mem_range.2 (Nat.mod_lt n hd)
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro a ha
  have ha' : a < d := mem_range.1 ha
  unfold HeathBrown1985.psi
  push_cast
  rw [mul_sum]
  apply sum_congr
  · ext n
    simp only [mem_filter, Nat.mod_eq_of_lt ha']
  · intro n hn
    rw [mem_filter] at hn
    have : (n : ZMod d) = (a : ZMod d) := (ZMod.natCast_eq_natCast_iff' n a d).2 hn.2
    rw [this]
    ring

/-- A character sum bounded by Siegel-Walfisz type errors. -/
theorem norm_psiChi_le {d : ℕ} [NeZero d] (x : ℝ) (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    {E : ℝ}
    (h : ∀ a : ℕ, a.Coprime d → |HeathBrown1985.psi x d a - x / d.totient| ≤ E) :
    ‖psiChi x χ‖ ≤ d.totient * E := by
  rw [psiChi_eq_sum x χ hχ]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a ∈ range d, ‖χ (a : ZMod d) *
      ((HeathBrown1985.psi x d a : ℂ) - (x : ℂ) / d.totient)‖ ≤
        if d.Coprime a then E else 0 := by
    intro a _
    split_ifs with hc
    · rw [norm_mul]
      have h1 : ‖χ (a : ZMod d)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have h2 : ‖(HeathBrown1985.psi x d a : ℂ) - (x : ℂ) / d.totient‖ ≤ E := by
        have : (HeathBrown1985.psi x d a : ℂ) - (x : ℂ) / d.totient =
            ((HeathBrown1985.psi x d a - x / d.totient : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_eq_abs]
        exact h a hc.symm
      calc ‖χ (a : ZMod d)‖ * ‖(HeathBrown1985.psi x d a : ℂ) - (x : ℂ) / d.totient‖
          ≤ 1 * E := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = E := one_mul E
    · have hnu : ¬ IsUnit (a : ZMod d) := fun hu =>
        hc ((ZMod.isUnit_iff_coprime a d).1 hu).symm
      rw [MulChar.map_nonunit _ hnu, zero_mul, norm_zero]
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.totient_eq_card_coprime]

/-- At most `D²` primitive pairs have modulus at most `D`. -/
theorem card_primSigma_le (Q : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (((primSigma Q).filter (fun p => (p.1 : ℝ) ≤ D)).card : ℝ) ≤ D ^ 2 := by
  classical
  set N := ⌊D⌋₊
  have hsub : (primSigma Q).filter (fun p => (p.1 : ℝ) ≤ D) ⊆
      (Icc 1 N).sigma (fun d => (univ : Finset (DirichletCharacter ℂ d))) := by
    intro p hp
    simp only [primSigma, mem_filter, mem_sigma, mem_Icc] at hp
    simp only [mem_sigma, mem_Icc, mem_univ, and_true]
    exact ⟨hp.1.1.1, Nat.le_floor hp.2⟩
  have hc : ((Icc 1 N).sigma (fun d => (univ : Finset (DirichletCharacter ℂ d)))).card ≤
      N * N := by
    rw [card_sigma]
    calc ∑ d ∈ Icc 1 N, (univ : Finset (DirichletCharacter ℂ d)).card
        ≤ ∑ _d ∈ Icc 1 N, N := by
          apply sum_le_sum
          intro d hd
          rw [mem_Icc] at hd
          have : NeZero d := ⟨by omega⟩
          rw [card_univ, ← Nat.card_eq_fintype_card,
            DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d]
          exact (Nat.totient_le d).trans hd.2
      _ = N * N := by rw [sum_const, Nat.card_Icc, smul_eq_mul]; simp
  have h1 := card_le_card hsub
  have h2 : ((N * N : ℕ) : ℝ) ≤ D ^ 2 := by
    have := Nat.floor_le hD
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc _ ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h1.trans hc
    _ ≤ D ^ 2 := h2

/-- Swapping a double sum over a divisibility relation. -/
lemma sum_swap_filter {ι κ : Type*} (I : Finset ι) (P : Finset κ) (R : κ → Prop)
    [DecidablePred R] (rel : κ → ι → Prop) [∀ p q, Decidable (rel p q)]
    (g : ι → ℝ) (F : κ → ℝ) :
    ∑ q ∈ I, g q * ∑ p ∈ P.filter (fun p => R p ∧ rel p q), F p =
      ∑ p ∈ P.filter R, F p * ∑ q ∈ I.filter (fun q => rel p q), g q := by
  simp only [sum_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases h1 : R p
  · simp only [h1, true_and, ite_true]
    apply sum_congr rfl
    intro q _
    split_ifs <;> ring
  · simp [h1]

/-- A primitive character of modulus `d ≥ 2` is not trivial. -/
lemma ne_one_of_isPrimitive {d : ℕ} [NeZero d] (hd : 2 ≤ d) {χ : DirichletCharacter ℂ d}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  have h1 := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).1 h
  have h2 : χ.conductor = d := hχ
  omega

set_option maxHeartbeats 1600000 in
/-- **Bombieri-Vinogradov**, CONDITIONAL ON `SiegelWalfisz` and `LargeConductor`. -/
theorem bombieriVinogradov_of (hSW : HeathBrown1985.SiegelWalfisz) (hLC : LargeConductor) :
    BombieriVinogradov := by
  intro A hA
  obtain ⟨C₁, B, K₁, hB, hLC'⟩ := hLC (A + 1) (by linarith)
  set C := max C₁ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  obtain ⟨c₂, hc₂, K₂, hSW'⟩ := hSW C (by linarith)
  obtain ⟨c₀, hc₀, K₀, hP⟩ := LeanLab.PNTPort.psi_explicit_strong
  obtain ⟨Kp, hKp, hKpb⟩ := log_rpow_le_sqrt (A + 2)
  obtain ⟨Ke0, hKe0, hKe0b⟩ := exp_neg_sqrt_log_le c₀ hc₀ (A + 1)
  obtain ⟨Ke2, hKe2, hKe2b⟩ := exp_neg_sqrt_log_le c₂ hc₂ (A + 1 + 2 * C)
  obtain ⟨C4, hC4, hC4b⟩ := sum_inv_totient_le
  set K₀' := max K₀ 0 with hK₀'
  set K₁' := max K₁ 0 with hK₁'
  set K₂' := max K₂ 0 with hK₂'
  have hK₀0 : 0 ≤ K₀' := le_max_right _ _
  have hK₁0 : 0 ≤ K₁' := le_max_right _ _
  have hK₂0 : 0 ≤ K₂' := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Ks := 8 * 2 ^ A / Real.log 2 ^ B with hKsdef
  set Kb := Kp / Real.log 2 + 2 * C4 * K₀' * Ke0 + 2 * C4 * (K₁' + K₂' * Ke2) with hKbdef
  have hKs : 0 ≤ Ks := by positivity
  have hKb : 0 ≤ Kb := by positivity
  refine ⟨B, hB, Ks + Kb, fun x hx a ha => ?_⟩
  set L := Real.log x with hLdef
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  set M := x / L ^ A with hMdef
  have hM : 0 ≤ M := by positivity
  rw [mul_div_assoc]
  set Q := ⌊Real.sqrt x / L ^ B⌋₊ with hQdef
  rcases lt_or_ge x 3 with hx3 | hx3
  · -- small `x`: a crude bound
    have hterm : ∀ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient| ≤ 4 * x := by
      intro q hq
      rw [mem_Icc] at hq
      have hp0 : 0 ≤ HeathBrown1985.psi x q (a q) :=
        sum_nonneg fun _ _ => vonMangoldt_nonneg
      have hp1 : HeathBrown1985.psi x q (a q) ≤ 3 * x := by
        unfold HeathBrown1985.psi
        calc _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                (fun _ _ _ => vonMangoldt_nonneg)
          _ ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, x := by
              apply sum_le_sum
              intro n hn
              rw [mem_Icc] at hn
              have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn.2).trans (Nat.floor_le hx0.le)
              have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
              calc vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
                _ ≤ Real.log x := Real.log_le_log (by linarith) hnx
                _ ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
          _ = ⌊x⌋₊ * x := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
          _ ≤ x * x := by gcongr; exact Nat.floor_le hx0.le
          _ ≤ 3 * x := by nlinarith
      have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hd0 : 0 ≤ x / q.totient := by positivity
      have hd1 : x / q.totient ≤ x := div_le_self hx0.le hφ
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hsum : ∑ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient| ≤
        Q * (4 * x) := by
      refine (sum_le_sum hterm).trans (le_of_eq ?_)
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    have hsx : Real.sqrt x ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    have hLB : Real.log 2 ^ B ≤ L ^ B :=
      Real.rpow_le_rpow hl2.le (Real.log_le_log (by norm_num) hx) hB.le
    have hl2B : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hl2 B
    have hQ : (Q : ℝ) ≤ 2 / Real.log 2 ^ B := by
      refine (Nat.floor_le (by positivity)).trans ?_
      exact div_le_div₀ (by norm_num) hsx hl2B hLB
    have hL2 : L ≤ 2 := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
    have hLA2 : L ^ A ≤ 2 ^ A := Real.rpow_le_rpow hL0.le hL2 hA.le
    have hxM : x ≤ 2 ^ A * M := by
      rw [hMdef, mul_div_assoc', le_div_iff₀ hLA]
      rw [mul_comm (2 ^ A) x]; exact mul_le_mul_of_nonneg_left hLA2 hx0.le
    calc _ ≤ Q * (4 * x) := hsum
      _ ≤ 2 / Real.log 2 ^ B * (4 * x) := by gcongr
      _ ≤ 2 / Real.log 2 ^ B * (4 * (2 ^ A * M)) := by gcongr
      _ = Ks * M := by rw [hKsdef]; ring
      _ ≤ (Ks + Kb) * M := by nlinarith
  · -- large `x`
    have hL1 : 1 ≤ L := by
      have h3 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      exact h3.le.trans (Real.log_le_log (by norm_num) hx3)
    have hLB : 1 ≤ L ^ B := Real.one_le_rpow hL1 hB.le
    have hsqx : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left hx0.le]
      nlinarith
    have hQs : (Q : ℝ) ≤ Real.sqrt x :=
      (Nat.floor_le (by positivity)).trans (div_le_self (Real.sqrt_nonneg _) hLB)
    have hQx : (Q : ℝ) ≤ x := hQs.trans hsqx
    have hlogQ : 1 + Real.log Q ≤ 2 * L := by
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · rw [h0]; simp; linarith
      · have := Real.log_le_log (by exact_mod_cast h0) hQx
        linarith
    have hH : ∑ m ∈ Icc 1 Q, (1 : ℝ) / m.totient ≤ 2 * C4 * L := by
      refine (hC4b Q).trans ?_
      nlinarith
    -- the per-modulus bound
    set S : ℕ → ℝ := fun q => if hq : q = 0 then 0 else
      haveI : NeZero q := ⟨hq⟩
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi x χ.primitiveCharacter‖ with hSdef
    have hstep : ∀ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient| ≤
        psiBad x q + |Chebyshev.psi x - x| * (1 / q.totient) + 1 / q.totient * S q := by
      intro q hq
      rw [mem_Icc] at hq
      have hq0 : q ≠ 0 := by omega
      have : NeZero q := ⟨hq0⟩
      have := term_le (q := q) x (ha q)
      simp only [hSdef, hq0, dite_false]
      rw [mul_one_div, one_div_mul_eq_div]
      exact this
    -- T1
    have hT1 : ∑ q ∈ Icc 1 Q, psiBad x q ≤ Kp / Real.log 2 * M := by
      have h1 : ∀ q ∈ Icc 1 Q, psiBad x q ≤ L / Real.log 2 * L := by
        intro q hq
        rw [mem_Icc] at hq
        refine (psiBad_le (by linarith) hq.1).trans ?_
        have hqx : (q : ℝ) ≤ x := (Nat.cast_le.2 hq.2).trans hQx
        have : Real.log q ≤ L := Real.log_le_log (by exact_mod_cast hq.1) hqx
        gcongr
      refine (sum_le_sum h1).trans ?_
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      have hK := hKpb x hx
      rw [Real.rpow_add hL0, Real.rpow_two] at hK
      have hsq := Real.mul_self_sqrt hx0.le
      have e : (Q : ℝ) * (L / Real.log 2 * L) ≤ Real.sqrt x * L ^ 2 / Real.log 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc', ← sq]
        apply div_le_div_of_nonneg_right _ hl2.le
        exact mul_le_mul_of_nonneg_right hQs (sq_nonneg L)
      refine e.trans ?_
      rw [hMdef, div_mul_div_comm, mul_comm (Real.log 2) (L ^ A)]
      rw [div_le_div_iff₀ hl2 (by positivity)]
      have : Real.sqrt x * (L ^ A * L ^ 2) ≤ Real.sqrt x * (Kp * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _)
      have h3 : Real.sqrt x * (Kp * Real.sqrt x) = Kp * x := by rw [mul_left_comm, hsq]
      have h4 : Real.sqrt x * (L ^ A * L ^ 2) ≤ Kp * x := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h4 hl2.le]
    -- T2
    have hLA1 : L ^ (A + 1) = L ^ A * L := by rw [Real.rpow_add hL0, Real.rpow_one]
    have hT2 : ∑ q ∈ Icc 1 Q, |Chebyshev.psi x - x| * (1 / q.totient) ≤
        2 * C4 * K₀' * Ke0 * M := by
      rw [← mul_sum]
      have he0 := hKe0b x hx
      rw [← hLdef, hLA1] at he0
      have hPx : |Chebyshev.psi x - x| ≤ K₀' * x * (Ke0 / (L ^ A * L)) := by
        refine (hP x hx).trans ?_
        rw [← hLdef]
        have hex : 0 ≤ Real.exp (-c₀ * Real.sqrt L) := (Real.exp_pos _).le
        calc K₀ * x * Real.exp (-c₀ * Real.sqrt L) ≤ K₀' * x * Real.exp (-c₀ * Real.sqrt L) := by
              gcongr; exact le_max_left _ _
          _ ≤ K₀' * x * (Ke0 / (L ^ A * L)) := by gcongr
      calc |Chebyshev.psi x - x| * ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient
          ≤ K₀' * x * (Ke0 / (L ^ A * L)) * (2 * C4 * L) :=
            mul_le_mul hPx hH (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 2 * C4 * K₀' * Ke0 * M := by rw [hMdef]; field_simp
    -- T3
    set F : (Σ d : ℕ, DirichletCharacter ℂ d) → ℝ := fun p => ‖psiChi x p.2‖ with hFdef
    have hF : ∀ p, 0 ≤ F p := fun p => norm_nonneg _
    set P := primSigma Q with hPdef
    have hstepa : ∀ q ∈ Icc 1 Q, 1 / (q.totient : ℝ) * S q ≤
        1 / (q.totient : ℝ) * ∑ p ∈ P.filter (fun p => 2 ≤ p.1 ∧ p.1 ∣ q), F p := by
      intro q hq
      rw [mem_Icc] at hq
      have hq0 : q ≠ 0 := by omega
      have : NeZero q := ⟨hq0⟩
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [hSdef, hq0, dite_false]
      exact sum_erase_le_primSigma hq.2 F hF
    have hstepc : ∀ p ∈ P.filter (fun p => 2 ≤ p.1),
        F p * ∑ q ∈ (Icc 1 Q).filter (fun q => p.1 ∣ q), (1 : ℝ) / q.totient ≤
          2 * C4 * L * (F p / p.1.totient) := by
      intro p hp
      rw [mem_filter] at hp
      have h := sum_dvd_inv_totient_le (d := p.1) (by omega) Q
      calc F p * ∑ q ∈ (Icc 1 Q).filter (fun q => p.1 ∣ q), (1 : ℝ) / q.totient
          ≤ F p * ((1 / p.1.totient) * (2 * C4 * L)) := by
            apply mul_le_mul_of_nonneg_left _ (hF p)
            exact h.trans (mul_le_mul_of_nonneg_left hH (by positivity))
        _ = 2 * C4 * L * (F p / p.1.totient) := by ring
    -- large conductors
    have hlarge : ∑ p ∈ (P.filter (fun p => 2 ≤ p.1)).filter
        (fun p => ¬ (p.1 : ℝ) ≤ L ^ C), F p / p.1.totient ≤ K₁' * M / L := by
      have hsub : (P.filter (fun p => 2 ≤ p.1)).filter (fun p => ¬ (p.1 : ℝ) ≤ L ^ C) ⊆
          P.filter (fun p => L ^ C₁ < p.1) := by
        intro p hp
        simp only [mem_filter, not_le] at hp ⊢
        refine ⟨hp.1.1, lt_of_le_of_lt ?_ hp.2⟩
        exact Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
      refine (sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => div_nonneg (hF p) (Nat.cast_nonneg _))).trans ?_
      refine (hLC' x hx).trans ?_
      rw [← hLdef, hLA1, hMdef]
      have : K₁ * x ≤ K₁' * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
      calc K₁ * x / (L ^ A * L) ≤ K₁' * x / (L ^ A * L) :=
            div_le_div_of_nonneg_right this (by positivity)
        _ = K₁' * (x / L ^ A) / L := by field_simp
    -- small conductors
    have hLC0 : 0 < L ^ C := Real.rpow_pos_of_pos hL0 C
    set E2 := K₂' * x * Real.exp (-c₂ * Real.sqrt L) with hE2
    have hsmall1 : ∀ p ∈ (P.filter (fun p => 2 ≤ p.1)).filter (fun p => (p.1 : ℝ) ≤ L ^ C),
        F p / p.1.totient ≤ E2 := by
      rintro ⟨d, χ⟩ hp
      simp only [hPdef, primSigma, mem_filter, mem_sigma, mem_Icc, mem_univ, true_and] at hp
      obtain ⟨⟨⟨⟨hd1, _⟩, hprim⟩, hd2⟩, hdL⟩ := hp
      have : NeZero d := ⟨by omega⟩
      have hχ : χ ≠ 1 := ne_one_of_isPrimitive hd2 hprim
      have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
      have hb := norm_psiChi_le x χ hχ (E := E2) (fun b hb => by
        refine (hSW' x hx d b hd1 hb hdL).trans ?_
        rw [hE2, ← hLdef]
        have hex : 0 ≤ Real.exp (-c₂ * Real.sqrt L) := (Real.exp_pos _).le
        gcongr
        exact le_max_left _ _)
      show ‖psiChi x χ‖ / d.totient ≤ E2
      rw [div_le_iff₀ hφ, mul_comm]
      exact hb
    have hcard : ((((P.filter (fun p => 2 ≤ p.1)).filter
        (fun p => (p.1 : ℝ) ≤ L ^ C)).card : ℕ) : ℝ) ≤ (L ^ C) ^ 2 := by
      refine le_trans ?_ (card_primSigma_le Q hLC0.le)
      exact_mod_cast card_le_card (fun p hp => by
        simp only [mem_filter] at hp ⊢
        exact ⟨hp.1.1, hp.2⟩)
    have hE20 : 0 ≤ E2 := by rw [hE2]; have := (Real.exp_pos (-c₂ * Real.sqrt L)).le; positivity
    have hsmall : ∑ p ∈ (P.filter (fun p => 2 ≤ p.1)).filter
        (fun p => (p.1 : ℝ) ≤ L ^ C), F p / p.1.totient ≤ K₂' * Ke2 * M / L := by
      refine (sum_le_card_nsmul _ _ _ hsmall1).trans ?_
      rw [nsmul_eq_mul]
      have he2 := hKe2b x hx
      rw [← hLdef] at he2
      have hpow : L ^ (A + 1 + 2 * C) = L ^ A * L * (L ^ C) ^ 2 := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one, mul_comm 2 C,
          Real.rpow_mul hL0.le, Real.rpow_two]
      rw [hpow] at he2
      calc _ ≤ (L ^ C) ^ 2 * E2 := mul_le_mul_of_nonneg_right hcard hE20
        _ ≤ (L ^ C) ^ 2 * (K₂' * x * (Ke2 / (L ^ A * L * (L ^ C) ^ 2))) := by
            rw [hE2]; gcongr
        _ = K₂' * Ke2 * M / L := by rw [hMdef]; field_simp
    have hT3 : ∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ) * S q ≤
        2 * C4 * (K₁' + K₂' * Ke2) * M := by
      refine (sum_le_sum hstepa).trans ?_
      rw [sum_swap_filter (Icc 1 Q) P (fun p => 2 ≤ p.1) (fun p q => p.1 ∣ q)
        (fun q => 1 / (q.totient : ℝ)) F]
      refine (sum_le_sum hstepc).trans ?_
      rw [← mul_sum, ← sum_filter_add_sum_filter_not _ (fun p => (p.1 : ℝ) ≤ L ^ C)]
      calc 2 * C4 * L * (_ + _) ≤ 2 * C4 * L * (K₂' * Ke2 * M / L + K₁' * M / L) :=
            mul_le_mul_of_nonneg_left (add_le_add hsmall hlarge) (by positivity)
        _ = 2 * C4 * (K₁' + K₂' * Ke2) * M := by field_simp; ring
    -- combine
    calc ∑ q ∈ Icc 1 Q, |HeathBrown1985.psi x q (a q) - x / q.totient|
        ≤ ∑ q ∈ Icc 1 Q, (psiBad x q + |Chebyshev.psi x - x| * (1 / q.totient) +
            1 / q.totient * S q) := sum_le_sum hstep
      _ = ∑ q ∈ Icc 1 Q, psiBad x q + ∑ q ∈ Icc 1 Q, |Chebyshev.psi x - x| * (1 / q.totient) +
            ∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ) * S q := by
          rw [sum_add_distrib, sum_add_distrib]
      _ ≤ Kp / Real.log 2 * M + 2 * C4 * K₀' * Ke0 * M + 2 * C4 * (K₁' + K₂' * Ke2) * M := by
          linarith
      _ = Kb * M := by rw [hKbdef]; ring
      _ ≤ (Ks + Kb) * M := by nlinarith

end LeanLab.PNTPort.BV
