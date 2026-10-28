module

public import LeanLab.Halupczok2012.U1460Reduction

/-!
# P0077 Halupczok 2012, the analytic layer for `SingSeriesTails`, unit U-1462

AI wrote the Lean code, Claude, run 20261022T0403Z-7595. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Everything here is elementary and PROVED, no cited input.

* `rankin_tail`: Rankin's trick over subsets of a finite set of primes,
  `∑_{t ⊆ P, ∏ t > z} |∏_{p ∈ t} f p| ≤ z^{-σ} ∏_{p ∈ P} (1 + |f p| p^σ)`.
* `prod_le_Kc`: `∏ (1 + a_p) ≤ Kc σ` when `0 ≤ a_p ≤ 8 p^{-1-σ}`, with
  `Kc σ = exp (8 ζ(1 + σ))`.
* `prod_abs_le`: the Euler product of a weight bounded by `1/(p-1)² + [p ∣ r]/(p-1)`, times `p^σ`,
  is at most `Kc σ · Hs σ r`, `Hs σ r = ∏_{p ∣ r} (1 + p^σ/(p-1))`.
* `prod_primeFactors_eq_sum`: `∏_{p ∣ r} (1 + h p) = ∑_{t ⊆ primes ≤ N, ∏ t ∣ r} ∏_{p ∈ t} h p`.
* `sum_Hs_sq_le`: `∑_{m ∈ window} Hs σ (n - m)² ≤ Kc σ (y + n^{2σ})`.
* `sum_Hs_div_totient_le`: `∑_{q ≤ N} Hs σ q / φ(q) ≤ Kc σ (1 + log N)`.
* `hasProd_primes_tendsto`: partial products over the primes up to `w` of a summably perturbed
  function tend to its `tprod` over `Nat.Primes`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset Filter Topology

/-- The primes `p ≤ N`. -/
def PrN (N : ℕ) : Finset ℕ := (range (N + 1)).filter Nat.Prime

theorem mem_PrN {N p : ℕ} : p ∈ PrN N ↔ p ≤ N ∧ p.Prime := by
  simp [PrN]

theorem prime_of_mem_PrN {N p : ℕ} (h : p ∈ PrN N) : p.Prime := (mem_PrN.mp h).2

/-! ### Rankin's trick -/

/-- **Rankin's trick over subsets.** -/
theorem rankin_tail (P : Finset ℕ) (f : ℕ → ℝ) {z σ : ℝ} (hz : 0 < z) (hσ : 0 ≤ σ) :
    ∑ t ∈ P.powerset with z < ((∏ p ∈ t, p : ℕ) : ℝ), |∏ p ∈ t, f p| ≤
      z ^ (-σ) * ∏ p ∈ P, (1 + |f p| * (p : ℝ) ^ σ) := by
  rw [euler_expand, mul_sum]
  calc _ ≤ ∑ t ∈ P.powerset with z < ((∏ p ∈ t, p : ℕ) : ℝ),
        z ^ (-σ) * ∏ p ∈ t, (|f p| * (p : ℝ) ^ σ) := by
        apply sum_le_sum
        intro t ht
        rw [mem_filter] at ht
        have hd := ht.2
        set d := ((∏ p ∈ t, p : ℕ) : ℝ) with hd'
        have hd0 : 0 < d := lt_trans hz hd
        have h1 : 1 ≤ (d / z) ^ σ := Real.one_le_rpow ((one_le_div hz).mpr hd.le) hσ
        have hpr : ∏ p ∈ t, (p : ℝ) ^ σ = d ^ σ := by
          rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), hd', Nat.cast_prod]
        have e : z ^ (-σ) * ∏ p ∈ t, (|f p| * (p : ℝ) ^ σ) =
            (∏ p ∈ t, |f p|) * (d / z) ^ σ := by
          rw [prod_mul_distrib, hpr, Real.div_rpow hd0.le hz.le, Real.rpow_neg hz.le]
          ring
        rw [e, abs_prod]
        exact le_mul_of_one_le_right (prod_nonneg (fun p _ => abs_nonneg _)) h1
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro t _ _
        apply mul_nonneg (Real.rpow_nonneg hz.le _)
        exact prod_nonneg (fun p _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-! ### A uniform bound for convergent Euler products -/

/-- `Kc σ = exp (8 ∑_k k^{-1-σ})`. -/
noncomputable def Kc (σ : ℝ) : ℝ := Real.exp (8 * ∑' k : ℕ, ((k : ℝ) ^ (1 + σ))⁻¹)

theorem one_le_Kc (σ : ℝ) : 1 ≤ Kc σ := by
  unfold Kc
  apply Real.one_le_exp
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg (fun k => by positivity)

theorem Kc_pos (σ : ℝ) : 0 < Kc σ := lt_of_lt_of_le one_pos (one_le_Kc σ)

theorem prod_le_Kc {σ : ℝ} (hσ : 0 < σ) (P : Finset ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ p ∈ P, 0 ≤ a p) (ha : ∀ p ∈ P, a p ≤ 8 * ((p : ℝ) ^ (1 + σ))⁻¹) :
    ∏ p ∈ P, (1 + a p) ≤ Kc σ := by
  have hs : Summable (fun k : ℕ => ((k : ℝ) ^ (1 + σ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  calc ∏ p ∈ P, (1 + a p) ≤ ∏ p ∈ P, Real.exp (a p) := by
        apply Finset.prod_le_prod₀ (fun p hp => by linarith [ha0 p hp])
        intro p _
        linarith [Real.add_one_le_exp (a p)]
    _ = Real.exp (∑ p ∈ P, a p) := (Real.exp_sum _ _).symm
    _ ≤ Kc σ := by
        unfold Kc
        apply Real.exp_le_exp.mpr
        calc ∑ p ∈ P, a p ≤ ∑ p ∈ P, 8 * ((p : ℝ) ^ (1 + σ))⁻¹ := sum_le_sum ha
          _ = 8 * ∑ p ∈ P, ((p : ℝ) ^ (1 + σ))⁻¹ := by rw [mul_sum]
          _ ≤ 8 * ∑' k : ℕ, ((k : ℝ) ^ (1 + σ))⁻¹ := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact hs.sum_le_tsum P (fun k _ => by positivity)

/-! ### Local inequalities, with `x = p^σ`, `1 ≤ x`, `x² ≤ p` -/

theorem rpow_facts {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) :
    1 ≤ (p : ℝ) ^ σ ∧ ((p : ℝ) ^ σ) ^ 2 ≤ p ∧
      ((p : ℝ) ^ (1 + σ))⁻¹ = 1 / ((p : ℝ) * (p : ℝ) ^ σ) ∧
      ((p : ℝ) ^ σ) ^ 2 = (p : ℝ) ^ (2 * σ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have e2 : ((p : ℝ) ^ σ) ^ 2 = (p : ℝ) ^ (2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; ring_nf
  refine ⟨Real.one_le_rpow hp1 hσ.le, ?_, ?_, e2⟩
  · rw [e2]
    calc (p : ℝ) ^ (2 * σ) ≤ (p : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = p := Real.rpow_one _
  · rw [Real.rpow_add hp0, Real.rpow_one, one_div]

theorem loc_i {p x : ℝ} (hp : 2 ≤ p) (hx : 1 ≤ x) (hx2 : x ^ 2 ≤ p) :
    x / (p - 1) ^ 2 ≤ 8 * (1 / (p * x)) := by
  have h1 : 0 < p - 1 := by linarith
  have h1' : 0 < (p - 1) ^ 2 := pow_pos h1 2
  rw [mul_one_div, div_le_div_iff₀ h1' (by positivity)]
  have hp2 : p ^ 2 ≤ 4 * (p - 1) ^ 2 := by nlinarith
  have k : x * (p * x) ≤ p * p := by nlinarith
  nlinarith

theorem loc_b {p x : ℝ} (hp : 2 ≤ p) (hx : 1 ≤ x) (hx2 : x ^ 2 ≤ p) :
    0 ≤ x / (p - 1) ∧ x / (p - 1) * p ≤ 2 * x ∧
      (1 + x / (p - 1)) ^ 2 - 1 ≤ 4 * (x / (p - 1)) := by
  have h1 : 0 < p - 1 := by linarith
  set b := x / (p - 1) with hb
  have hbx : b * (p - 1) = x := by rw [hb]; field_simp
  have hb0 : 0 ≤ b := by positivity
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hb2 : b ≤ 2 := by
    have : b * (p - 1) ≤ 2 * (p - 1) := by rw [hbx]; linarith
    exact le_of_mul_le_mul_right this h1
  refine ⟨hb0, ?_, by nlinarith⟩
  nlinarith

theorem loc_iia {p x : ℝ} (hp : 2 ≤ p) (hx : 1 ≤ x) (hx2 : x ^ 2 ≤ p) :
    ((1 + x / (p - 1)) ^ 2 - 1) / x ^ 2 ≤ 8 * (1 / (p * x)) := by
  obtain ⟨hb0, hbp, hh⟩ := loc_b hp hx hx2
  set b := x / (p - 1) with hb
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((1 + b) ^ 2 - 1) * (p * x) ≤ 4 * b * (p * x) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
    _ = 4 * (b * p) * x := by ring
    _ ≤ 4 * (2 * x) * x := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
    _ = 8 * x ^ 2 := by ring

theorem loc_iib {p x : ℝ} (hp : 2 ≤ p) (hx : 1 ≤ x) (hx2 : x ^ 2 ≤ p) :
    ((1 + x / (p - 1)) ^ 2 - 1) / p ≤ 8 * (1 / (p * x)) := by
  obtain ⟨hb0, hbp, hh⟩ := loc_b hp hx hx2
  set b := x / (p - 1) with hb
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((1 + b) ^ 2 - 1) * (p * x) ≤ 4 * b * (p * x) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
    _ = 4 * (b * p) * x := by ring
    _ ≤ 4 * (2 * x) * x := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
    _ = 8 * x ^ 2 := by ring
    _ ≤ 8 * p := by linarith

theorem loc_iii {p x : ℝ} (hp : 2 ≤ p) (hx : 1 ≤ x) (hx2 : x ^ 2 ≤ p) :
    (p / (p - 1) * (1 + x / (p - 1)) - 1) / p ≤ 8 * (1 / (p * x)) := by
  have h1 : 0 < p - 1 := by linarith
  have h1' : 0 < (p - 1) ^ 2 := pow_pos h1 2
  have e : p / (p - 1) * (1 + x / (p - 1)) - 1 = (p - 1 + p * x) / (p - 1) ^ 2 := by
    field_simp; ring
  rw [e, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hxx : x ≤ x ^ 2 := by nlinarith
  have k1 : (p - 1) * x ≤ 2 * (p - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hxx h1.le, mul_le_mul_of_nonneg_left hx2 h1.le]
  have k2 : p * x ^ 2 ≤ 4 * (p - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ p)]
  have hp0 : 0 ≤ p := by linarith
  calc (p - 1 + p * x) * (p * x) = p * ((p - 1) * x + p * x ^ 2) := by ring
    _ ≤ p * (6 * (p - 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hp0; linarith
    _ ≤ 8 * ((p - 1) ^ 2 * p) := by nlinarith

/-! ### Euler products of weights of size `1/(p-1)² + [p ∣ r]/(p-1)` -/

/-- `Hs σ r = ∏_{p ∣ r} (1 + p^σ/(p-1))`. -/
noncomputable def Hs (σ : ℝ) (r : ℕ) : ℝ := ∏ p ∈ r.primeFactors, (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1))

theorem Hs_nonneg (σ : ℝ) (r : ℕ) : 0 ≤ Hs σ r := by
  unfold Hs
  apply prod_nonneg
  intro p hp
  have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have : 0 < (p : ℝ) - 1 := by linarith
  positivity

theorem PrN_filter_dvd {w r : ℕ} (hr : r ≠ 0) (hrw : r ≤ w) :
    (PrN w).filter (fun p => p ∣ r) = r.primeFactors := by
  ext p
  simp only [mem_filter, mem_PrN, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨_, hp⟩, hd⟩; exact ⟨hp, hd, hr⟩
  · rintro ⟨hp, hd, _⟩
    exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hd).trans hrw, hp⟩, hd⟩

theorem prod_abs_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) {w r : ℕ} (hr : r ≠ 0) (hrw : r ≤ w)
    (f : ℕ → ℝ)
    (hf : ∀ p, p.Prime → |f p| ≤ 1 / ((p : ℝ) - 1) ^ 2 + (if p ∣ r then 1 / ((p : ℝ) - 1) else 0)) :
    ∏ p ∈ PrN w, (1 + |f p| * (p : ℝ) ^ σ) ≤ Kc σ * Hs σ r := by
  have hsplit : ∏ p ∈ PrN w, (1 + |f p| * (p : ℝ) ^ σ) ≤
      (∏ p ∈ PrN w, (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1) ^ 2)) *
        ∏ p ∈ (PrN w).filter (fun p => p ∣ r), (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1)) := by
    rw [prod_filter, ← prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      have hpp := prime_of_mem_PrN hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have h1 : 0 < (p : ℝ) - 1 := by linarith
      have hx : 0 ≤ (p : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hfp := hf p hpp
      have hm := mul_le_mul_of_nonneg_right hfp hx
      split_ifs at hm ⊢ with hd
      · have : 0 ≤ (p : ℝ) ^ σ / ((p : ℝ) - 1) ^ 2 * ((p : ℝ) ^ σ / ((p : ℝ) - 1)) := by
          positivity
        have e : (1 / ((p : ℝ) - 1) ^ 2 + 1 / ((p : ℝ) - 1)) * (p : ℝ) ^ σ =
            (p : ℝ) ^ σ / ((p : ℝ) - 1) ^ 2 + (p : ℝ) ^ σ / ((p : ℝ) - 1) := by ring
        nlinarith
      · have e : (1 / ((p : ℝ) - 1) ^ 2 + 0) * (p : ℝ) ^ σ = (p : ℝ) ^ σ / ((p : ℝ) - 1) ^ 2 := by
          ring
        nlinarith
  refine hsplit.trans ?_
  rw [PrN_filter_dvd hr hrw]
  apply mul_le_mul_of_nonneg_right _ (Hs_nonneg σ r)
  apply prod_le_Kc hσ
  · intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_PrN hp).two_le
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  · intro p hp
    have hpp := prime_of_mem_PrN hp
    obtain ⟨hx1, hx2, he, -⟩ := rpow_facts hpp hσ hσ2
    rw [he]
    exact loc_i (by exact_mod_cast hpp.two_le) hx1 hx2

/-! ### Divisor sums of multiplicative functions -/

theorem prod_primeFactors_eq_sum {r N : ℕ} (hr : r ≠ 0) (hrN : r ≤ N) (h : ℕ → ℝ) :
    ∏ p ∈ r.primeFactors, (1 + h p) =
      ∑ t ∈ (PrN N).powerset, if (∏ p ∈ t, p) ∣ r then ∏ p ∈ t, h p else 0 := by
  rw [euler_expand, ← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [mem_filter, mem_powerset]
  constructor
  · intro ht
    refine ⟨fun p hp => ?_, ?_⟩
    · have hp' := ht hp
      rw [Nat.mem_primeFactors] at hp'
      exact mem_PrN.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hp'.2.1).trans hrN, hp'.1⟩
    · exact (prod_dvd_prod_of_subset t r.primeFactors id ht).trans (Nat.prod_primeFactors_dvd r)
  · rintro ⟨htP, hd⟩ p hp
    rw [Nat.mem_primeFactors]
    exact ⟨prime_of_mem_PrN (htP hp), (dvd_prod_of_mem _ hp).trans hd, hr⟩

theorem sum_inv_multiples_le {d N : ℕ} (hd : 0 < d) :
    ∑ q ∈ (Icc 1 N).filter (fun q => d ∣ q), (1 / (q : ℝ)) ≤ (1 / d) * (1 + Real.log N) := by
  have hsub : (Icc 1 N).filter (fun q => d ∣ q) ⊆ (Icc 1 N).image (fun k => d * k) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hq
    rw [mem_image]
    refine ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at h1
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left k hd) h2
  have hinj : Set.InjOn (fun k => d * k) (Icc 1 N : Set ℕ) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hd hxy
  calc _ ≤ ∑ q ∈ (Icc 1 N).image (fun k => d * k), (1 / (q : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = ∑ k ∈ Icc 1 N, (1 / (d : ℝ)) * (k : ℝ)⁻¹ := by
        rw [sum_image hinj]
        apply sum_congr rfl; intro k _
        push_cast; rw [mul_comm (d : ℝ), one_div, mul_inv, one_div]; ring
    _ = (1 / d) * (harmonic N : ℝ) := by
        rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)

theorem card_window_dvd {W : Finset ℕ} {x y : ℝ} (hy : 0 ≤ y) {n : ℕ}
    (hW : ∀ m ∈ W, x < m ∧ (m : ℝ) ≤ x + y ∧ m < n) {d : ℕ} (hd : 0 < d) {θ : ℝ} (hθ : 0 ≤ θ) :
    ((W.filter (fun m => d ∣ n - m)).card : ℝ) ≤ y / d + ((n : ℝ) / d) ^ θ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hdn : d ≤ n
  · have hc := card_cong_le hd hy (S := W.filter (fun m => d ∣ n - m)) (x := x)
      (fun m hm => ⟨(hW m (mem_filter.mp hm).1).1, (hW m (mem_filter.mp hm).1).2.1⟩)
      (by
        intro m hm m' hm'
        rw [mem_filter] at hm hm'
        have e : ∀ k ∈ W, d ∣ n - k → (k : ℤ) ≡ (n : ℤ) [ZMOD d] := by
          intro k hk hdk
          rw [Int.modEq_iff_dvd]
          have hkn := (hW k hk).2.2
          have : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := Nat.cast_sub hkn.le
          rw [← this]; exact_mod_cast hdk
        exact (e m hm.1 hm.2).trans (e m' hm'.1 hm'.2).symm)
    have h1 : (1 : ℝ) ≤ ((n : ℝ) / d) ^ θ := by
      apply Real.one_le_rpow _ hθ
      rw [one_le_div hd']; exact_mod_cast hdn
    linarith
  · have he : W.filter (fun m => d ∣ n - m) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro m hm hdm
      have hmn := (hW m hm).2.2
      have := Nat.le_of_dvd (by omega) hdm
      omega
    rw [he, card_empty, Nat.cast_zero]
    have : 0 ≤ ((n : ℝ) / d) ^ θ := Real.rpow_nonneg (by positivity) _
    positivity

/-- **The second moment of `Hs` over a short window.** -/
theorem sum_Hs_sq_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) {W : Finset ℕ} {x y : ℝ}
    (hy : 0 ≤ y) {n : ℕ} (hW : ∀ m ∈ W, x < m ∧ (m : ℝ) ≤ x + y ∧ m < n) :
    ∑ m ∈ W, Hs σ (n - m) ^ 2 ≤ Kc σ * (y + (n : ℝ) ^ (2 * σ)) := by
  set h : ℕ → ℝ := fun p => (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1)) ^ 2 - 1 with hh
  have hh0 : ∀ p, p.Prime → 0 ≤ h p := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : 0 < (p : ℝ) - 1 := by linarith
    have : 0 ≤ (p : ℝ) ^ σ / ((p : ℝ) - 1) := by positivity
    simp only [hh]; nlinarith
  have hexp : ∀ m ∈ W, Hs σ (n - m) ^ 2 =
      ∑ t ∈ (PrN n).powerset, if (∏ p ∈ t, p) ∣ n - m then ∏ p ∈ t, h p else 0 := by
    intro m hm
    have hmn := (hW m hm).2.2
    rw [Hs, ← prod_pow, ← prod_primeFactors_eq_sum (by omega) (by omega)]
    apply prod_congr rfl; intro p _; simp only [hh]; ring
  rw [sum_congr rfl hexp, sum_comm]
  set θ := 2 * σ with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hterm : ∀ t ∈ (PrN n).powerset,
      ∑ m ∈ W, (if (∏ p ∈ t, p) ∣ n - m then ∏ p ∈ t, h p else 0) ≤
        y * ∏ p ∈ t, (h p / p) + (n : ℝ) ^ θ * ∏ p ∈ t, (h p / (p : ℝ) ^ θ) := by
    intro t ht
    have htP : ∀ p ∈ t, p.Prime := fun p hp => prime_of_mem_PrN (mem_powerset.mp ht hp)
    have hd : 0 < ∏ p ∈ t, p := prod_pos (fun p hp => (htP p hp).pos)
    have hd' : (0 : ℝ) < ((∏ p ∈ t, p : ℕ) : ℝ) := by exact_mod_cast hd
    have hH : 0 ≤ ∏ p ∈ t, h p := prod_nonneg (fun p hp => hh0 p (htP p hp))
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hc := card_window_dvd hy hW hd hθ0
    calc _ ≤ (y / ((∏ p ∈ t, p : ℕ) : ℝ) + ((n : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)) ^ θ) *
          ∏ p ∈ t, h p := mul_le_mul_of_nonneg_right hc hH
      _ = _ := by
          rw [Real.div_rpow (Nat.cast_nonneg _) hd'.le, Nat.cast_prod,
            ← Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), prod_div_distrib,
            prod_div_distrib]
          have h1 : ∏ p ∈ t, (p : ℝ) ≠ 0 := by rw [← Nat.cast_prod]; exact hd'.ne'
          have h2 : ∏ p ∈ t, (p : ℝ) ^ θ ≠ 0 := by
            rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod]
            exact (Real.rpow_pos_of_pos hd' θ).ne'
          field_simp
  calc _ ≤ ∑ t ∈ (PrN n).powerset,
        (y * ∏ p ∈ t, (h p / p) + (n : ℝ) ^ θ * ∏ p ∈ t, (h p / (p : ℝ) ^ θ)) := sum_le_sum hterm
    _ = y * ∏ p ∈ PrN n, (1 + h p / p) + (n : ℝ) ^ θ * ∏ p ∈ PrN n, (1 + h p / (p : ℝ) ^ θ) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, euler_expand, euler_expand]
    _ ≤ y * Kc σ + (n : ℝ) ^ θ * Kc σ := by
        have hn : 0 ≤ (n : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hy
          apply prod_le_Kc hσ
          · intro p hp
            have := hh0 p (prime_of_mem_PrN hp)
            have : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_PrN hp).pos
            positivity
          · intro p hp
            have hpp := prime_of_mem_PrN hp
            obtain ⟨hx1, hx2, he, -⟩ := rpow_facts hpp hσ hσ2
            rw [he]
            exact loc_iib (by exact_mod_cast hpp.two_le) hx1 hx2
        · apply mul_le_mul_of_nonneg_left _ hn
          apply prod_le_Kc hσ
          · intro p hp
            have := hh0 p (prime_of_mem_PrN hp)
            have : 0 ≤ (p : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
            positivity
          · intro p hp
            have hpp := prime_of_mem_PrN hp
            obtain ⟨hx1, hx2, he, e2⟩ := rpow_facts hpp hσ hσ2
            rw [he, hθ, ← e2]
            exact loc_iia (by exact_mod_cast hpp.two_le) hx1 hx2
    _ = _ := by ring

/-- `1/φ(q) = (1/q) ∏_{p ∣ q} p/(p-1)`. -/
theorem inv_totient_eq {q : ℕ} (hq : 0 < q) :
    1 / (q.totient : ℝ) = (1 / (q : ℝ)) * ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors q
  have hc : ((q.totient : ℕ) : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  have hne : ∀ p ∈ q.primeFactors, (p : ℝ) - 1 ≠ 0 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hP : ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ≠ 0 := prod_ne_zero_iff.mpr hne
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [prod_div_distrib]
  field_simp
  linarith [hc]

/-- **The harmonic sum of `Hs/φ`.** -/
theorem sum_Hs_div_totient_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (N : ℕ) :
    ∑ q ∈ Icc 1 N, Hs σ q / (q.totient : ℝ) ≤ Kc σ * (1 + Real.log N) := by
  set h : ℕ → ℝ := fun p => (p : ℝ) / ((p : ℝ) - 1) * (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1)) - 1
    with hh
  have hh0 : ∀ p, p.Prime → 0 ≤ h p := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h1 : 0 < (p : ℝ) - 1 := by linarith
    have : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by rw [le_div_iff₀ h1]; linarith
    have : 0 ≤ (p : ℝ) ^ σ / ((p : ℝ) - 1) := by positivity
    simp only [hh]; nlinarith
  have hexp : ∀ q ∈ Icc 1 N, Hs σ q / (q.totient : ℝ) = (1 / (q : ℝ)) *
      ∑ t ∈ (PrN N).powerset, if (∏ p ∈ t, p) ∣ q then ∏ p ∈ t, h p else 0 := by
    intro q hq
    rw [mem_Icc] at hq
    rw [div_eq_mul_one_div, inv_totient_eq (by omega), Hs,
      ← prod_primeFactors_eq_sum (by omega) hq.2, mul_comm, mul_assoc, ← prod_mul_distrib]
    congr 1
    apply prod_congr rfl; intro p _; simp only [hh]; ring
  rw [sum_congr rfl hexp]
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm : ∀ t ∈ (PrN N).powerset,
      ∑ q ∈ Icc 1 N, (1 / (q : ℝ)) * (if (∏ p ∈ t, p) ∣ q then ∏ p ∈ t, h p else 0) ≤
        (1 + Real.log N) * ∏ p ∈ t, (h p / p) := by
    intro t ht
    have htP : ∀ p ∈ t, p.Prime := fun p hp => prime_of_mem_PrN (mem_powerset.mp ht hp)
    have hd : 0 < ∏ p ∈ t, p := prod_pos (fun p hp => (htP p hp).pos)
    have hH : 0 ≤ ∏ p ∈ t, h p := prod_nonneg (fun p hp => hh0 p (htP p hp))
    have e : ∀ q ∈ Icc 1 N, (1 / (q : ℝ)) * (if (∏ p ∈ t, p) ∣ q then ∏ p ∈ t, h p else 0) =
        if (∏ p ∈ t, p) ∣ q then (1 / (q : ℝ)) * ∏ p ∈ t, h p else 0 := by
      intro q _; split_ifs <;> simp
    rw [sum_congr rfl e, ← sum_filter, ← sum_mul]
    have hs := sum_inv_multiples_le (N := N) hd
    calc _ ≤ (1 / ((∏ p ∈ t, p : ℕ) : ℝ)) * (1 + Real.log N) * ∏ p ∈ t, h p :=
          mul_le_mul_of_nonneg_right hs hH
      _ = _ := by
          rw [prod_div_distrib, Nat.cast_prod]
          have : ∏ p ∈ t, (p : ℝ) ≠ 0 := by rw [← Nat.cast_prod]; exact_mod_cast hd.ne'
          field_simp
  calc _ ≤ ∑ t ∈ (PrN N).powerset, (1 + Real.log N) * ∏ p ∈ t, (h p / p) := sum_le_sum hterm
    _ = (1 + Real.log N) * ∏ p ∈ PrN N, (1 + h p / p) := by rw [← mul_sum, euler_expand]
    _ ≤ (1 + Real.log N) * Kc σ := by
        have hl : 0 ≤ 1 + Real.log N := by
          rcases Nat.eq_zero_or_pos N with h0 | h0
          · subst h0; simp
          · have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
            linarith
        apply mul_le_mul_of_nonneg_left _ hl
        apply prod_le_Kc hσ
        · intro p hp
          have := hh0 p (prime_of_mem_PrN hp)
          have : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_PrN hp).pos
          positivity
        · intro p hp
          have hpp := prime_of_mem_PrN hp
          obtain ⟨hx1, hx2, he, -⟩ := rpow_facts hpp hσ hσ2
          rw [he]
          exact loc_iii (by exact_mod_cast hpp.two_le) hx1 hx2
    _ = _ := by ring

/-! ### Partial Euler products tend to the `tprod` -/

theorem hasProd_primes_tendsto (f : ℕ → ℝ)
    (hs : Summable (fun k : ℕ => if k.Prime then f k - 1 else 0)) :
    Tendsto (fun w => ∏ p ∈ PrN w, f p) atTop (𝓝 (∏' p : Nat.Primes, f p)) := by
  set F : ℕ → ℝ := fun k => if k.Prime then f k else 1 with hF
  have hF1 : F = fun k => 1 + (if k.Prime then f k - 1 else 0) := by
    funext k; simp only [hF]; split_ifs <;> ring
  have hm : Multipliable F := by rw [hF1]; exact Real.multipliable_one_add_of_summable hs
  have hP : HasProd (F ∘ (Subtype.val : Nat.Primes → ℕ)) (∏' k, F k) := by
    rw [Subtype.val_injective.hasProd_iff]
    · exact hm.hasProd
    · intro k hk
      simp only [hF]
      rw [if_neg]
      intro hp; exact hk ⟨⟨k, hp⟩, rfl⟩
  have hcomp : (F ∘ (Subtype.val : Nat.Primes → ℕ)) = fun p : Nat.Primes => f p := by
    funext p; simp only [Function.comp, hF, if_pos p.prop]
  rw [hcomp] at hP
  have e : (∏' p : Nat.Primes, f p) = ∏' k, F k := hP.tprod_eq
  rw [e]
  have ht := hm.hasProd.tendsto_prod_nat
  have ht2 := ht.comp (tendsto_add_atTop_nat 1)
  refine ht2.congr (fun w => ?_)
  simp only [Function.comp, PrN, hF]
  rw [prod_filter]

end LeanLab.Halupczok2012
