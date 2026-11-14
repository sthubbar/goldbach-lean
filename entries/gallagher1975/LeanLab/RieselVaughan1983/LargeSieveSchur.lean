module

public import LeanLab.PNTPort.LargeSieve.Farey
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The large sieve by the Schur test, constant `N + δ⁻¹ (1 + log(1/(2δ)))`

Session 20261020T1816Z-cloud48, unit U-6711, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

Known mathematics, no cited input. For points `α r`, `r ∈ s`, pairwise at distance at least
`δ` modulo one, `0 < δ ≤ 1/2`, and complex `a n` on `M < n ≤ M + N`:

* `dual_large_sieve_schur`:
  `∑_{M<n≤M+N} ‖∑_r b_r e(n α_r)‖² ≤ (N + δ⁻¹ (1 + log(1/(2δ)))) ∑_r ‖b_r‖²`.
* `large_sieve_schur`:
  `∑_r ‖∑_{M<n≤M+N} a_n e(n α_r)‖² ≤ (N + δ⁻¹ (1 + log(1/(2δ)))) ∑_n ‖a_n‖²`.
* `farey_large_sieve_schur`, `Q ≥ 2`, the reduced fractions `a/q`, `q ≤ Q`, `0 ≤ a < q`:
  `∑_{q≤Q} ∑*_a ‖S(a/q)‖² ≤ (N + Q² (1 + log(Q²/2))) ∑_n ‖a_n‖²`.

Why, from `SCOPE_LS_U6710.md`: the cited Montgomery-Vaughan weighted large sieve (8.17) of
P0032 Lemma 13 has slack only in the additive constant, not in the coefficient of `N`; any
sieve with `N` coefficient exactly one and `Q²` times a power of `log Q` closes Section 9.
Proof: expand the dual form; the diagonal gives `N`; the off-diagonal kernel
`|∑_n e(nθ)| ≤ 1/(2‖θ‖)`; Schur test with `|b_r b_s| ≤ (|b_r|² + |b_s|²)/2`; and for fixed
`r` the spaced distances on each side have distinct floors `⌊t/δ⌋ ∈ [1, ⌊1/(2δ)⌋]`, so the
harmonic bound `H_K ≤ 1 + log K` gives `∑_{s≠r} 1/‖α_r − α_s‖ ≤ 2 δ⁻¹ (1 + log(1/(2δ)))`.

The lab's `LeanLab.PNTPort.LargeSieve.large_sieve` already proves the constant `N + 2/δ`,
also with `N` coefficient one, and is the stronger bound once `δ < 1/(2e)`. This file reuses
its `e`, `dist0`, `Spaced`, `dualSum`, `norm_geom_le`, `farey`, `farey_spaced`.
-/

@[expose] public section


namespace LeanLab.RieselVaughan1983.LargeSieveSchur

open Complex Finset Real LeanLab.PNTPort.LargeSieve

/-- `(M, M+N]` as the image of `range N`. -/
lemma Ioc_eq_image (M : ℤ) (N : ℕ) :
    Ioc M (M + N) = (range N).image (fun v : ℕ => M + 1 + v) := by
  ext n
  simp only [mem_Ioc, mem_image, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(n - M - 1).toNat, by omega, by omega⟩
  · rintro ⟨v, hv, rfl⟩
    omega

lemma card_Ioc_eq (M : ℤ) (N : ℕ) : (Ioc M (M + N)).card = N := by
  rw [Int.card_Ioc]; omega

/-- The interval kernel: `‖∑_{M<n≤M+N} e(nθ)‖ ≤ 1/(2‖θ‖)`. -/
lemma norm_kernel_le (M : ℤ) (N : ℕ) {θ : ℝ} (h : 0 < dist0 θ) :
    ‖∑ n ∈ Ioc M (M + N), e (n * θ)‖ ≤ 1 / (2 * dist0 θ) := by
  have hk : ∑ n ∈ Ioc M (M + N), e (n * θ) = e (((M + 1 : ℤ) : ℝ) * θ) * G N θ := by
    rw [Ioc_eq_image, sum_image (by intro v _ w _ h; simp only at h; omega), G, mul_sum]
    apply sum_congr rfl
    intro v _
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [hk, norm_mul, norm_e, one_mul]
  exact norm_geom_le N h

/-- Harmonic count: for `δ`-separated reals in `[δ, 1/2]`,
`∑ 1/t ≤ δ⁻¹ (1 + log(1/(2δ)))`. -/
lemma sum_inv_sep {ι : Type*} (T : Finset ι) (t : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hpos : ∀ i ∈ T, δ ≤ t i) (hle : ∀ i ∈ T, t i ≤ 1 / 2)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |t i - t j|) :
    ∑ i ∈ T, 1 / t i ≤ (1 / δ) * (1 + Real.log (1 / (2 * δ))) := by
  set k : ι → ℕ := fun i => ⌊t i / δ⌋₊ with hk
  set K : ℕ := ⌊1 / (2 * δ)⌋₊ with hK
  have hk1 : ∀ i ∈ T, 1 ≤ k i := by
    intro i hi
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ, one_mul]; exact hpos i hi)
  have hkK : ∀ i ∈ T, k i ≤ K := by
    intro i hi
    apply Nat.floor_mono
    rw [← div_div]
    exact div_le_div_of_nonneg_right (hle i hi) hδ.le
  have hkle : ∀ i ∈ T, (k i : ℝ) * δ ≤ t i := by
    intro i hi
    have := Nat.floor_le (div_nonneg (hδ.le.trans (hpos i hi)) hδ.le)
    exact (le_div_iff₀ hδ).1 this
  have hinj : Set.InjOn k T := by
    intro i hi j hj hij
    by_contra hne
    have hs := hsep i hi j hj hne
    have hi0 : 0 ≤ t i / δ := div_nonneg (hδ.le.trans (hpos i hi)) hδ.le
    have hj0 : 0 ≤ t j / δ := div_nonneg (hδ.le.trans (hpos j hj)) hδ.le
    have a1 := Nat.floor_le hi0
    have a2 := Nat.lt_floor_add_one (t i / δ)
    have b1 := Nat.floor_le hj0
    have b2 := Nat.lt_floor_add_one (t j / δ)
    have hij' : (⌊t i / δ⌋₊ : ℝ) = ⌊t j / δ⌋₊ := by exact_mod_cast hij
    have : |t i / δ - t j / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
    linarith
  have step1 : ∑ i ∈ T, 1 / t i ≤ ∑ i ∈ T, (1 / δ) * ((k i : ℕ) : ℝ)⁻¹ := by
    apply sum_le_sum
    intro i hi
    have hk0 : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
    calc 1 / t i ≤ 1 / ((k i : ℝ) * δ) :=
          one_div_le_one_div_of_le (by positivity) (hkle i hi)
      _ = (1 / δ) * ((k i : ℕ) : ℝ)⁻¹ := by field_simp
  have step2 : ∑ i ∈ T, ((k i : ℕ) : ℝ)⁻¹ = ∑ j ∈ T.image k, ((j : ℝ))⁻¹ :=
    (sum_image (f := fun j : ℕ => ((j : ℝ))⁻¹) hinj).symm
  have hsub : T.image k ⊆ Icc 1 K := by
    intro j hj
    rw [mem_Icc]
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
    exact ⟨hk1 i hi, hkK i hi⟩
  have step3 : ∑ j ∈ T.image k, ((j : ℝ))⁻¹ ≤ ∑ j ∈ Icc 1 K, ((j : ℝ))⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hH : ∑ j ∈ Icc 1 K, ((j : ℝ))⁻¹ = ((harmonic K : ℚ) : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hH2 := harmonic_le_one_add_log K
  have hone : (1 : ℝ) ≤ 1 / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hK1 : 1 ≤ K := Nat.le_floor (by rw [Nat.cast_one]; exact hone)
  have hlog : Real.log K ≤ Real.log (1 / (2 * δ)) :=
    Real.log_le_log (by exact_mod_cast hK1) (Nat.floor_le (by linarith))
  rw [← mul_sum, step2] at step1
  calc ∑ i ∈ T, 1 / t i ≤ 1 / δ * ∑ j ∈ T.image k, ((j : ℝ))⁻¹ := step1
    _ ≤ 1 / δ * (1 + Real.log (1 / (2 * δ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- For `δ`-spaced points, `∑_{r' ≠ r} 1/‖α r − α r'‖ ≤ 2 δ⁻¹ (1 + log(1/(2δ)))`. -/
lemma sum_off_diag_inv {ι : Type*} [DecidableEq ι] {s : Finset ι} {α : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hs : Spaced s α δ) {r : ι} (hr : r ∈ s) :
    ∑ r' ∈ s.erase r, 1 / dist0 (α r - α r') ≤
      2 * ((1 / δ) * (1 + Real.log (1 / (2 * δ)))) := by
  set t : ι → ℝ := fun r' => α r' - α r - round (α r' - α r) with ht
  have hdt : ∀ r', dist0 (α r - α r') = |t r'| := by
    intro r'; rw [dist0_sub_comm]; rfl
  have habs : ∀ r', |t r'| ≤ 1 / 2 := fun r' => abs_sub_round _
  have hge : ∀ r' ∈ s.erase r, δ ≤ |t r'| := by
    intro r' hr'
    rw [← hdt]
    exact hs r hr r' (mem_of_mem_erase hr') (ne_of_mem_erase hr').symm
  have hsep : ∀ r1 ∈ s.erase r, ∀ r2 ∈ s.erase r, r1 ≠ r2 → δ ≤ |t r1 - t r2| := by
    intro r1 h1 r2 h2 hne
    have := hs r1 (mem_of_mem_erase h1) r2 (mem_of_mem_erase h2) hne
    refine this.trans ?_
    have h := dist0_le_abs_sub_int (α r1 - α r2)
      (round (α r1 - α r) - round (α r2 - α r))
    convert h using 2
    simp only [ht]
    push_cast
    ring
  rw [← sum_filter_add_sum_filter_not (s.erase r) (fun r' => 0 < t r')]
  have hP : ∑ r' ∈ (s.erase r).filter (fun r' => 0 < t r'), 1 / dist0 (α r - α r')
      ≤ (1 / δ) * (1 + Real.log (1 / (2 * δ))) := by
    have := sum_inv_sep ((s.erase r).filter (fun r' => 0 < t r')) t hδ hδ2
      (by
        intro i hi
        rw [mem_filter] at hi
        have := hge i hi.1
        rwa [abs_of_pos hi.2] at this)
      (fun i _ => (abs_le.1 (habs i)).2)
      (by
        intro i hi j hj hne
        exact hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne)
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, abs_of_pos (mem_filter.1 hi).2]
  have hN : ∑ r' ∈ (s.erase r).filter (fun r' => ¬ 0 < t r'), 1 / dist0 (α r - α r')
      ≤ (1 / δ) * (1 + Real.log (1 / (2 * δ))) := by
    have := sum_inv_sep ((s.erase r).filter (fun r' => ¬ 0 < t r')) (fun r' => -t r') hδ hδ2
      (by
        intro i hi
        rw [mem_filter] at hi
        have h1 := hge i hi.1
        have h2 : t i ≤ 0 := not_lt.1 hi.2
        rw [abs_of_nonpos h2] at h1
        exact h1)
      (fun i _ => by have := (abs_le.1 (habs i)).1; show -t i ≤ 1 / 2; linarith)
      (by
        intro i hi j hj hne
        have := hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne
        rwa [show -t i - -t j = -(t i - t j) by ring, abs_neg])
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, abs_of_nonpos (not_lt.1 (mem_filter.1 hi).2)]
  linarith

variable {ι : Type*} [DecidableEq ι]

/-- **Dual large sieve, Schur test form.** -/
theorem dual_large_sieve_schur {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hs : Spaced s α δ) (b : ι → ℂ) (M : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc M (M + N), ‖dualSum s α b n‖ ^ 2 ≤
      (N + (1 / δ) * (1 + Real.log (1 / (2 * δ)))) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  set D := (1 / δ) * (1 + Real.log (1 / (2 * δ))) with hD
  set I := Ioc M (M + (N : ℤ)) with hI
  set Kc : ι → ι → ℂ := fun r r' => ∑ n ∈ I, e ((n : ℝ) * (α r - α r')) with hKc
  set X := ∑ n ∈ I, ‖dualSum s α b n‖ ^ 2 with hXdef
  have hX : (X : ℂ) = ∑ r ∈ s, ∑ r' ∈ s, b r * (starRingEnd ℂ) (b r') * Kc r r' := by
    rw [hXdef]
    simp_rw [Complex.ofReal_sum, normSq_dualSum]
    rw [sum_comm]
    apply sum_congr rfl; intro r _
    rw [sum_comm]
    apply sum_congr rfl; intro r' _
    rw [hKc, mul_sum]
  set Kb : ι → ι → ℝ := fun r r' =>
    if r = r' then (N : ℝ) else 1 / (2 * dist0 (α r - α r')) with hKb
  have hKb0 : ∀ r r', 0 ≤ Kb r r' := by
    intro r r'; simp only [hKb]; split_ifs
    · positivity
    · exact div_nonneg zero_le_one (mul_nonneg zero_le_two (dist0_nonneg _))
  have hKbsym : ∀ r r', Kb r r' = Kb r' r := by
    intro r r'
    simp only [hKb]
    by_cases h : r = r'
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), dist0_sub_comm]
  have hcard : I.card = N := card_Ioc_eq M N
  have hKle : ∀ r ∈ s, ∀ r' ∈ s, ‖Kc r r'‖ ≤ Kb r r' := by
    intro r hr r' hr'
    by_cases h : r = r'
    · subst h
      simp only [hKc, hKb, if_pos rfl, sub_self, mul_zero, e_zero, sum_const, hcard,
        nsmul_eq_mul, mul_one]
      simp
    · simp only [hKb, if_neg h]
      exact norm_kernel_le M N (lt_of_lt_of_le hδ (hs r hr r' hr' h))
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => by positivity)
  have step1 : X ≤ ∑ r ∈ s, ∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * Kb r r' := by
    have : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    rw [this, hX]
    refine (norm_sum_le _ _).trans (sum_le_sum (fun r hr => (norm_sum_le _ _).trans
      (sum_le_sum (fun r' hr' => ?_))))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hKle r hr r' hr') (by positivity)
  have step2 := sum_sum_mul_le s (fun r => ‖b r‖) Kb hKb0 hKbsym
  have step3 : ∀ r ∈ s, ∑ r' ∈ s, Kb r r' ≤ N + D := by
    intro r hr
    rw [← add_sum_erase s _ hr]
    simp only [hKb, if_pos rfl]
    refine add_le_add le_rfl ?_
    have hoff := sum_off_diag_inv hδ hδ2 hs hr
    calc ∑ x ∈ s.erase r, (if r = x then (N : ℝ) else 1 / (2 * dist0 (α r - α x)))
        = ∑ x ∈ s.erase r, (1 / 2) * (1 / dist0 (α r - α x)) := by
          apply sum_congr rfl; intro x hx
          rw [if_neg (ne_of_mem_erase hx).symm]
          field_simp
      _ = (1 / 2) * ∑ x ∈ s.erase r, 1 / dist0 (α r - α x) := by rw [mul_sum]
      _ ≤ (1 / 2) * (2 * D) := by linarith
      _ = D := by ring
  calc X ≤ _ := step1
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * ∑ r' ∈ s, Kb r r' := step2
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * (N + D) :=
        sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (step3 r hr) (by positivity))
    _ = (N + D) * ∑ r ∈ s, ‖b r‖ ^ 2 := by rw [← sum_mul, mul_comm]

omit [DecidableEq ι] in
/-- Duality: a dual bound with constant `Δ ≥ 0` gives the primal bound with the same `Δ`. -/
theorem primal_of_dual {s : Finset ι} {α : ι → ℝ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (M : ℤ) (N : ℕ)
    (hdual : ∀ b : ι → ℂ,
      ∑ n ∈ Ioc M (M + N), ‖dualSum s α b n‖ ^ 2 ≤ Δ * ∑ r ∈ s, ‖b r‖ ^ 2)
    (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (n * α r)‖ ^ 2 ≤
      Δ * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  set S : ι → ℂ := fun r => ∑ n ∈ I, a n * e (n * α r) with hS
  set b : ι → ℂ := fun r => (starRingEnd ℂ) (S r) with hb
  set X := ∑ r ∈ s, ‖S r‖ ^ 2 with hXdef
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => by positivity)
  have hX : (X : ℂ) = ∑ n ∈ I, a n * dualSum s α b n := by
    rw [hXdef, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_pow, ← Complex.conj_mul']
    unfold dualSum
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro r _
    rw [hS, mul_sum]
    apply sum_congr rfl; intro n _
    rw [hb]
    ring
  have h1 : X ≤ ∑ n ∈ I, ‖a n‖ * ‖dualSum s α b n‖ := by
    have : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    rw [this, hX]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp_rw [norm_mul]
  have h2 := sum_mul_sq_le_sq_mul_sq I (fun n => ‖a n‖) (fun n => ‖dualSum s α b n‖)
  have h3 := hdual b
  have hbX : ∑ r ∈ s, ‖b r‖ ^ 2 = X := by
    rw [hXdef]; apply sum_congr rfl; intro r _; rw [hb, Complex.norm_conj]
  rw [hbX] at h3
  set Aa := ∑ n ∈ I, ‖a n‖ ^ 2
  have hAa : 0 ≤ Aa := sum_nonneg (fun _ _ => by positivity)
  have key : X ^ 2 ≤ Aa * (Δ * X) := by
    calc X ^ 2 ≤ (∑ n ∈ I, ‖a n‖ * ‖dualSum s α b n‖) ^ 2 := pow_le_pow_left₀ hX0 h1 2
      _ ≤ Aa * ∑ n ∈ I, ‖dualSum s α b n‖ ^ 2 := h2
      _ ≤ Aa * (Δ * X) := mul_le_mul_of_nonneg_left h3 hAa
  rcases eq_or_lt_of_le hX0 with h | h
  · rw [← h]; positivity
  · have : X * X ≤ X * (Δ * Aa) := by nlinarith
    exact le_of_mul_le_mul_left this h

/-- **LargeSieveSchur.** For `δ`-spaced points mod one, `0 < δ ≤ 1/2`,
`∑_r ‖∑_{M<n≤M+N} a_n e(n α_r)‖² ≤ (N + δ⁻¹ (1 + log(1/(2δ)))) ∑_n ‖a_n‖²`. -/
theorem large_sieve_schur {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hs : Spaced s α δ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (n * α r)‖ ^ 2 ≤
      (N + (1 / δ) * (1 + Real.log (1 / (2 * δ)))) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hone : (1 : ℝ) ≤ 1 / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hlog : 0 ≤ Real.log (1 / (2 * δ)) := Real.log_nonneg hone
  have hΔ : 0 ≤ (N : ℝ) + (1 / δ) * (1 + Real.log (1 / (2 * δ))) := by positivity
  exact primal_of_dual hΔ M N (fun b => dual_large_sieve_schur hδ hδ2 hs b M N) a

/-- **Farey corollary.** For `Q ≥ 2`, over reduced `a/q`, `1 ≤ q ≤ Q`, `0 ≤ a < q`:
`∑ ‖S(a/q)‖² ≤ (N + Q² (1 + log(Q²/2))) ∑_n ‖a_n‖²`. -/
theorem farey_large_sieve_schur {Q : ℕ} (hQ : 2 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ p ∈ farey Q, ‖∑ n ∈ Ioc M (M + N), a n * e (n * fareyPt p)‖ ^ 2 ≤
      (N + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2))) *
        ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hδ2 : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have := large_sieve_schur hδ hδ2 (farey_spaced Q) a M N
  rwa [show (1 : ℝ) / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 by field_simp,
    show (1 : ℝ) / (2 * (1 / (Q : ℝ) ^ 2)) = (Q : ℝ) ^ 2 / 2 by field_simp] at this

end LeanLab.RieselVaughan1983.LargeSieveSchur
