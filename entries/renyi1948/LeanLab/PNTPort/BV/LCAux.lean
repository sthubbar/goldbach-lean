module

public import LeanLab.PNTPort.BV.TypeII
public import LeanLab.PNTPort.BV.Statements

/-!
lab proof, AI wrote this file, known mathematics, no cited input

Bookkeeping for the large conductor estimate: reindexing `primSigma ↔ primIdx`, the count
of primitive characters, the dyadic covering in the modulus, and the Type I and Type II
totals over `L^{C₁} < d ≤ Q`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction
open LeanLab.PNTPort.LargeSieve (primIdx)

lemma sum_primIdx_eq (R : ℕ) (g : (Σ d : ℕ, DirichletCharacter ℂ d) → ℝ) :
    ∑ i ∈ primIdx R, g ⟨i.1 + 1, i.2⟩ = ∑ p ∈ primSigma R, g p := by
  refine Finset.sum_bij (fun i _ => (⟨i.1 + 1, i.2⟩ : Σ d : ℕ, DirichletCharacter ℂ d))
    ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨k, χ⟩ hi
    simp only [primIdx, primSigma, mem_sigma, mem_range, mem_filter, mem_univ, true_and,
      mem_Icc] at hi ⊢
    exact ⟨⟨by omega, by omega⟩, hi.2⟩
  · rintro ⟨a, χ⟩ _ ⟨b, ψ⟩ _ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    have : a = b := by omega
    subst this
    simp only [heq_eq_eq] at h2
    subst h2; rfl
  · rintro ⟨d, χ⟩ hd
    simp only [primSigma, mem_sigma, mem_filter, mem_univ, true_and, mem_Icc] at hd
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    refine ⟨⟨k, χ⟩, ?_, rfl⟩
    simp only [primIdx, mem_sigma, mem_range, mem_filter, mem_univ, true_and]
    exact ⟨by omega, hd.2⟩

lemma sum_inv_totient_primSigma_le (Q : ℕ) (P : (Σ d : ℕ, DirichletCharacter ℂ d) → Prop)
    [DecidablePred P] {c : ℝ} (hc : 0 ≤ c) :
    ∑ p ∈ (primSigma Q).filter P, c / (p.1.totient : ℝ) ≤ Q * c := by
  calc _ ≤ ∑ p ∈ primSigma Q, c / (p.1.totient : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = ∑ d ∈ Icc 1 Q, ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
          (fun χ => χ.IsPrimitive), c / (d.totient : ℝ) := by
        unfold primSigma; rw [sum_sigma]
    _ ≤ ∑ _d ∈ Icc 1 Q, c := by
        apply sum_le_sum; intro d hd
        have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
        have : NeZero d := ⟨by omega⟩
        rw [sum_const, nsmul_eq_mul]
        have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have hcard : (((univ : Finset (DirichletCharacter ℂ d)).filter
            (fun χ => χ.IsPrimitive)).card : ℝ) ≤ d.totient := by
          have h1 := card_filter_le (univ : Finset (DirichletCharacter ℂ d))
            (fun χ => χ.IsPrimitive)
          have h2 : (univ : Finset (DirichletCharacter ℂ d)).card = d.totient := by
            rw [card_univ, ← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d]
          rw [h2] at h1
          exact_mod_cast h1
        calc _ ≤ (d.totient : ℝ) * (c / (d.totient : ℝ)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = c := by field_simp
    _ = Q * c := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

lemma dyadic_exists {U : ℝ} (hU : 1 ≤ U) {d Q : ℕ} (hUd : U < d) (hdQ : d ≤ Q) :
    ∃ j < Nat.log 2 Q + 1, U * 2 ^ j < d ∧ (d : ℝ) ≤ U * 2 ^ (j + 1) := by
  have hex : ∃ j, (d : ℝ) ≤ U * 2 ^ j := by
    refine ⟨Nat.log 2 Q + 1, ?_⟩
    have h1 : Q < 2 ^ (Nat.log 2 Q + 1) := Nat.lt_pow_succ_log_self (by norm_num) Q
    have h2 : (d : ℝ) < (2 : ℝ) ^ (Nat.log 2 Q + 1) := by exact_mod_cast (lt_of_le_of_lt hdQ h1)
    have h3 : (2 : ℝ) ^ (Nat.log 2 Q + 1) ≤ U * 2 ^ (Nat.log 2 Q + 1) :=
      le_mul_of_one_le_left (by positivity) hU
    linarith
  classical
  set j₀ := Nat.find hex with hj₀
  have hspec : (d : ℝ) ≤ U * 2 ^ j₀ := Nat.find_spec hex
  have hj0 : j₀ ≠ 0 := by
    intro h; rw [h, pow_zero, mul_one] at hspec; linarith
  obtain ⟨j, hj⟩ : ∃ j, j₀ = j + 1 := ⟨j₀ - 1, by omega⟩
  have hmin : ¬ (d : ℝ) ≤ U * 2 ^ j := Nat.find_min hex (by omega)
  have hle : j₀ ≤ Nat.log 2 Q + 1 := by
    apply Nat.find_min'
    have h1 : Q < 2 ^ (Nat.log 2 Q + 1) := Nat.lt_pow_succ_log_self (by norm_num) Q
    have h2 : (d : ℝ) < (2 : ℝ) ^ (Nat.log 2 Q + 1) := by exact_mod_cast (lt_of_le_of_lt hdQ h1)
    have h3 : (2 : ℝ) ^ (Nat.log 2 Q + 1) ≤ U * 2 ^ (Nat.log 2 Q + 1) :=
      le_mul_of_one_le_left (by positivity) hU
    linarith
  refine ⟨j, by omega, lt_of_not_ge hmin, ?_⟩
  rw [← hj]; exact hspec

lemma sum_le_sum_blocks {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    (J : ℕ) (B : ℕ → ι → Prop) [∀ j, DecidablePred (B j)]
    (hcov : ∀ i ∈ S, ∃ j < J, B j i) :
    ∑ i ∈ S, f i ≤ ∑ j ∈ range J, ∑ i ∈ S.filter (B j), f i := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  obtain ⟨j, hj, hB⟩ := hcov i hi
  calc f i = (if B j i then f i else 0) := by simp [hB]
    _ ≤ _ := single_le_sum (f := fun j => if B j i then f i else 0)
          (fun k _ => by split_ifs <;> simp [hf i hi]) (mem_range.2 hj)

lemma div_block_arith {x V U R Q ω s : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V) (hR0 : 0 ≤ R)
    (hRV : R ≤ 2 * V) (hRQ : R ≤ Q) (hx : 0 ≤ x) (hω : 0 < ω) (hs : 0 ≤ s) :
    (x + R * x / ω + R ^ 2 * s) / V ≤ x / U + 2 * x / ω + 2 * Q * s := by
  have hV : 0 < V := by linarith
  have hU0 : 0 < U := by linarith
  rw [div_le_iff₀ hV]
  have e1 : x ≤ x / U * V := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hU0]
    exact mul_le_mul_of_nonneg_left hUV hx
  have e2 : R * x / ω ≤ 2 * x / ω * V := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hω.le
    nlinarith
  have e3 : R ^ 2 * s ≤ 2 * Q * s * V := by
    have : R * R ≤ Q * (2 * V) := mul_le_mul hRQ hRV hR0 (by linarith)
    nlinarith
  nlinarith

/-- **Type II total** over the moduli `U < d ≤ Q`. -/
theorem typeII_total {K₂ : ℝ} (hK₂ : 0 < K₂)
    (hII : ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → ∀ R : ℕ, 1 ≤ R →
      ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 x w w i.2‖ ≤
        K₂ * (2 + Real.log x) ^ 4 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x))
    {x : ℝ} (hx : 2 ≤ x) {w : ℕ} (hw : 1 ≤ w) {Q : ℕ} (hQ : 1 ≤ Q) {U : ℝ} (hU : 1 ≤ U) :
    ∑ p ∈ (primSigma Q).filter (fun p => U < p.1), ‖S4 x w w p.2‖ / (p.1.totient : ℝ) ≤
      (Nat.log 2 Q + 1 : ℕ) * (K₂ * (2 + Real.log x) ^ 4 *
        (x / U + 2 * x / Real.sqrt w + 2 * Q * Real.sqrt x)) := by
  classical
  set S := (primSigma Q).filter (fun p => U < p.1) with hS
  set J := Nat.log 2 Q + 1 with hJ
  set ℓ := 2 + Real.log x with hℓ
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hω : 0 < Real.sqrt w := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have hmemS : ∀ p ∈ S, U < p.1 ∧ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2.IsPrimitive := by
    intro p hp
    simp only [hS, primSigma, mem_filter, mem_sigma, mem_Icc, mem_univ, true_and] at hp
    exact ⟨hp.2, hp.1.1.1, hp.1.1.2, hp.1.2⟩
  have step1 := sum_le_sum_blocks S (fun p => ‖S4 x w w p.2‖ / (p.1.totient : ℝ))
    (fun _ _ => by positivity) J
    (fun j p => U * 2 ^ j < p.1 ∧ (p.1 : ℝ) ≤ U * 2 ^ (j + 1)) (by
      intro p hp
      obtain ⟨h1, -, h3, -⟩ := hmemS p hp
      exact dyadic_exists hU h1 h3)
  refine step1.trans ?_
  rw [show ((J : ℕ) : ℝ) * (K₂ * ℓ ^ 4 * (x / U + 2 * x / Real.sqrt w + 2 * Q * Real.sqrt x)) =
    ∑ _j ∈ range J, K₂ * ℓ ^ 4 * (x / U + 2 * x / Real.sqrt w + 2 * Q * Real.sqrt x) by
    rw [sum_const, card_range, nsmul_eq_mul]]
  apply sum_le_sum
  intro j _
  set V : ℝ := U * 2 ^ j with hV
  set R : ℕ := min Q ⌊U * 2 ^ (j + 1)⌋₊ with hR
  have hUV : U ≤ V := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
  have hV0 : 0 < V := by linarith
  have hfl1 : 1 ≤ ⌊U * 2 ^ (j + 1)⌋₊ :=
    Nat.le_floor (by push_cast; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := j + 1) (by norm_num)])
  have hR1 : 1 ≤ R := le_min hQ hfl1
  have hRQ : (R : ℝ) ≤ Q := by exact_mod_cast min_le_left _ _
  have hRV : (R : ℝ) ≤ 2 * V := by
    have : (R : ℝ) ≤ ((⌊U * (2 : ℝ) ^ (j + 1)⌋₊ : ℕ) : ℝ) := Nat.cast_le.2 (min_le_right _ _)
    refine this.trans ((Nat.floor_le (by positivity)).trans (le_of_eq ?_))
    rw [hV]; ring
  calc ∑ p ∈ S.filter (fun p => U * 2 ^ j < p.1 ∧ (p.1 : ℝ) ≤ U * 2 ^ (j + 1)),
        ‖S4 x w w p.2‖ / (p.1.totient : ℝ)
      ≤ ∑ p ∈ S.filter (fun p => U * 2 ^ j < p.1 ∧ (p.1 : ℝ) ≤ U * 2 ^ (j + 1)),
          (p.1 : ℝ) / (p.1.totient : ℝ) * ‖S4 x w w p.2‖ / V := by
        apply sum_le_sum; intro p hp
        have hpj := (mem_filter.1 hp).2.1
        have hd0 : (0 : ℝ) < p.1 := by linarith
        have hd1 : 1 ≤ p.1 := by
          have : (0 : ℕ) < p.1 := by exact_mod_cast hd0
          omega
        have hφ : (0 : ℝ) < p.1.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
        calc ‖S4 x w w p.2‖ / (p.1.totient : ℝ)
            = ((p.1 : ℝ) / (p.1.totient : ℝ) * ‖S4 x w w p.2‖) / (p.1 : ℝ) := by
              field_simp
          _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hV0 hpj.le
    _ ≤ ∑ p ∈ primSigma R, (p.1 : ℝ) / (p.1.totient : ℝ) * ‖S4 x w w p.2‖ / V := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro p hp
        rw [mem_filter] at hp
        obtain ⟨h1, h2, h3, h4⟩ := hmemS p hp.1
        have h5 : p.1 ≤ ⌊U * 2 ^ (j + 1)⌋₊ := Nat.le_floor hp.2.2
        simp only [primSigma, mem_sigma, mem_Icc, mem_filter, mem_univ, true_and]
        exact ⟨⟨h2, le_min h3 h5⟩, h4⟩
    _ = (∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 x w w i.2‖) / V := by
        rw [sum_div, ← sum_primIdx_eq R (fun p => (p.1 : ℝ) / (p.1.totient : ℝ) *
          ‖S4 x w w p.2‖ / V)]
    _ ≤ (K₂ * ℓ ^ 4 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x)) / V :=
        div_le_div_of_nonneg_right (hII x hx w hw R hR1) hV0.le
    _ = K₂ * ℓ ^ 4 * ((x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) / V) := by ring
    _ ≤ K₂ * ℓ ^ 4 * (x / U + 2 * x / Real.sqrt w + 2 * Q * Real.sqrt x) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_block_arith hU hUV (by positivity) hRV hRQ (by linarith) hω (Real.sqrt_nonneg _)

/-- **Type I total** over the moduli `U < d ≤ Q`. -/
theorem typeI_total {x : ℝ} (hx : 2 ≤ x) {w : ℕ} (hw : 1 ≤ w) (Q : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    ∑ p ∈ (primSigma Q).filter (fun p => U < p.1),
      (‖S1 x w p.2‖ + ‖S2 x w w p.2‖ + ‖S3 x w p.2‖) / (p.1.totient : ℝ) ≤
      Q * ((Real.log 4 + 4) * w + 3 * ((w * w + w : ℕ) : ℝ) * Real.log x *
        (Real.sqrt Q * (1 + Real.log Q))) := by
  classical
  set T := (Real.log 4 + 4) * w + 3 * ((w * w + w : ℕ) : ℝ) * Real.log x *
    (Real.sqrt Q * (1 + Real.log Q)) with hT
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ T := by
    have := Real.log_natCast_nonneg Q
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    rw [hT]; positivity
  refine le_trans (sum_le_sum fun p hp => ?_) (sum_inv_totient_primSigma_le Q _ hT0)
  rcases p with ⟨d, χ⟩
  simp only [primSigma, mem_filter, mem_sigma, mem_Icc, mem_univ, true_and] at hp
  obtain ⟨⟨⟨hd1, hdQ⟩, hprim⟩, hUd⟩ := hp
  have hd2 : 1 < d := by
    have : (1 : ℝ) < d := by linarith
    exact_mod_cast this
  have : NeZero d := ⟨by omega⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (typeI_bound hd2 hprim hx w w hw hw).trans ?_
  rw [hT]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hdQr : (d : ℝ) ≤ Q := by exact_mod_cast hdQ
  have hd0 : (0 : ℝ) < d := by positivity
  apply mul_le_mul (Real.sqrt_le_sqrt hdQr) _ (by have := Real.log_natCast_nonneg d; linarith)
    (Real.sqrt_nonneg _)
  have := Real.log_le_log hd0 hdQr
  linarith

end LeanLab.PNTPort.BV
