module

public import LeanLab.PNTPort.LargeSieve.Basic

/-!
# The large sieve inequality, dual form and main form

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `dual_large_sieve`: `∑_{M<n≤M+N} ‖∑_r b_r e(n α_r)‖² ≤ (N + 2/δ) ∑_r ‖b_r‖²`.
* `large_sieve`: `∑_r ‖∑_{M<n≤M+N} a_n e(n α_r)‖² ≤ (N + 2/δ) ∑_n ‖a_n‖²`.

Both for points `α_r` that are `δ`-spaced modulo one, `Spaced s α δ`, with `δ > 0`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

variable {ι : Type*} [DecidableEq ι]

/-- The dual sum `B(n) = ∑_r b_r e(n α_r)`. -/
noncomputable def dualSum (s : Finset ι) (α : ι → ℝ) (b : ι → ℂ) (n : ℤ) : ℂ :=
  ∑ r ∈ s, b r * e (n * α r)

omit [DecidableEq ι] in
lemma normSq_dualSum (s : Finset ι) (α : ι → ℝ) (b : ι → ℂ) (n : ℤ) :
    ((‖dualSum s α b n‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ s, ∑ r' ∈ s, b r * (starRingEnd ℂ) (b r') * e (n * (α r - α r')) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold dualSum
  rw [map_sum, sum_mul_sum]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro r' _
  rw [map_mul, ← e_neg, show (n : ℝ) * (α r - α r') = n * α r + -(n * α r') by ring, e_add]
  ring

/-- The geometric sum `G m θ = ∑_{k<m} e(kθ)`. -/
noncomputable def G (m : ℕ) (θ : ℝ) : ℂ := ∑ k ∈ range m, e (k * θ)

lemma G_zero (m : ℕ) : G m 0 = m := by simp [G, e_zero]

lemma shifted_kernel (c : ℤ) (L P : ℕ) (θ : ℝ) :
    ∑ u ∈ range L, ∑ v ∈ range P, e (((c + u + v : ℤ) : ℝ) * θ) =
      e (c * θ) * (G L θ * G P θ) := by
  rw [G, G, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro u _
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  push_cast
  rw [add_mul, add_mul, e_add, e_add]
  ring

lemma norm_shifted_kernel_le (c : ℤ) (L P : ℕ) {θ : ℝ} (hθ : 0 < dist0 θ) :
    ‖∑ u ∈ range L, ∑ v ∈ range P, e (((c + u + v : ℤ) : ℝ) * θ)‖ ≤
      1 / (4 * dist0 θ ^ 2) := by
  rw [shifted_kernel, norm_mul, norm_e, one_mul, norm_mul]
  calc ‖G L θ‖ * ‖G P θ‖ ≤ (1 / (2 * dist0 θ)) * (1 / (2 * dist0 θ)) :=
        mul_le_mul (norm_geom_le L hθ) (norm_geom_le P hθ) (norm_nonneg _) (by positivity)
    _ = 1 / (4 * dist0 θ ^ 2) := by field_simp; ring

omit [DecidableEq ι] in
/-- `∑∑ x_r x_r' K r r' ≤ ∑ x_r² ∑ K r r'` for a symmetric nonnegative kernel. -/
lemma sum_sum_mul_le (s : Finset ι) (x : ι → ℝ) (K : ι → ι → ℝ)
    (hK : ∀ r r', 0 ≤ K r r') (hsym : ∀ r r', K r r' = K r' r) :
    ∑ r ∈ s, ∑ r' ∈ s, x r * x r' * K r r' ≤ ∑ r ∈ s, x r ^ 2 * ∑ r' ∈ s, K r r' := by
  have h1 : ∑ r ∈ s, ∑ r' ∈ s, x r * x r' * K r r' ≤
      ∑ r ∈ s, ∑ r' ∈ s, ((1 / 2) * (x r ^ 2 * K r r') + (1 / 2) * (x r' ^ 2 * K r r')) := by
    apply sum_le_sum; intro r _; apply sum_le_sum; intro r' _
    have := hK r r'
    nlinarith [sq_nonneg (x r - x r'), mul_nonneg this (sq_nonneg (x r - x r'))]
  have h2 : ∑ r ∈ s, ∑ r' ∈ s, x r' ^ 2 * K r r' = ∑ r ∈ s, ∑ r' ∈ s, x r ^ 2 * K r r' := by
    rw [sum_comm]
    apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _
    rw [hsym]
  have h3 : ∑ r ∈ s, ∑ r' ∈ s, ((1 / 2) * (x r ^ 2 * K r r') + (1 / 2) * (x r' ^ 2 * K r r'))
      = (1 / 2) * ∑ r ∈ s, ∑ r' ∈ s, x r ^ 2 * K r r' +
        (1 / 2) * ∑ r ∈ s, ∑ r' ∈ s, x r' ^ 2 * K r r' := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro r _
    rw [mul_sum, mul_sum, ← sum_add_distrib]
  rw [h3, h2] at h1
  refine h1.trans (le_of_eq ?_)
  rw [← add_mul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_mul]
  apply sum_congr rfl; intro r _
  rw [mul_sum]

/-- The averaged shifted sum, bounded by the kernel computation. -/
lemma shifted_bound {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hs : Spaced s α δ)
    (b : ι → ℂ) (c : ℤ) (L P : ℕ) :
    ∑ u ∈ range L, ∑ v ∈ range P, ‖dualSum s α b (c + u + v)‖ ^ 2 ≤
      (L * P + 1 / δ ^ 2) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  set Kc : ι → ι → ℂ := fun r r' =>
    ∑ u ∈ range L, ∑ v ∈ range P, e (((c + u + v : ℤ) : ℝ) * (α r - α r')) with hKc
  set X := ∑ u ∈ range L, ∑ v ∈ range P, ‖dualSum s α b (c + u + v)‖ ^ 2 with hXdef
  have hX : (X : ℂ) = ∑ r ∈ s, ∑ r' ∈ s, b r * (starRingEnd ℂ) (b r') * Kc r r' := by
    rw [hXdef]
    simp_rw [Complex.ofReal_sum, normSq_dualSum]
    calc _ = ∑ u ∈ range L, ∑ r ∈ s, ∑ v ∈ range P, ∑ r' ∈ s,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) :=
          sum_congr rfl (fun u _ => sum_comm)
      _ = ∑ u ∈ range L, ∑ r ∈ s, ∑ r' ∈ s, ∑ v ∈ range P,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) :=
          sum_congr rfl (fun u _ => sum_congr rfl (fun r _ => sum_comm))
      _ = ∑ r ∈ s, ∑ u ∈ range L, ∑ r' ∈ s, ∑ v ∈ range P,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) := sum_comm
      _ = ∑ r ∈ s, ∑ r' ∈ s, ∑ u ∈ range L, ∑ v ∈ range P,
          b r * (starRingEnd ℂ) (b r') * e (((c + u + v : ℤ) : ℝ) * (α r - α r')) :=
          sum_congr rfl (fun r _ => sum_comm)
      _ = _ := by
          apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _
          rw [hKc, mul_sum]
          apply sum_congr rfl; intro u _
          rw [mul_sum]
  set Kb : ι → ι → ℝ := fun r r' =>
    if r = r' then (L * P : ℝ) else 1 / (4 * dist0 (α r - α r') ^ 2) with hKb
  have hKb0 : ∀ r r', 0 ≤ Kb r r' := by
    intro r r'; simp only [hKb]; split_ifs <;> positivity
  have hKbsym : ∀ r r', Kb r r' = Kb r' r := by
    intro r r'
    simp only [hKb]
    by_cases h : r = r'
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), dist0_sub_comm]
  have hKle : ∀ r ∈ s, ∀ r' ∈ s, ‖Kc r r'‖ ≤ Kb r r' := by
    intro r hr r' hr'
    by_cases h : r = r'
    · subst h
      simp only [hKc, hKb, if_pos rfl, sub_self, mul_zero, e_zero, sum_const, card_range,
        nsmul_eq_mul, mul_one]
      rw [norm_mul]
      simp
    · simp only [hKb, if_neg h]
      exact norm_shifted_kernel_le c L P (lt_of_lt_of_le hδ (hs r hr r' hr' h))
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))
  have step1 : X ≤ ∑ r ∈ s, ∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * Kb r r' := by
    have : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    rw [this, hX]
    refine (norm_sum_le _ _).trans (sum_le_sum (fun r hr => (norm_sum_le _ _).trans
      (sum_le_sum (fun r' hr' => ?_))))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hKle r hr r' hr') (by positivity)
  have step2 := sum_sum_mul_le s (fun r => ‖b r‖) Kb hKb0 hKbsym
  have step3 : ∀ r ∈ s, ∑ r' ∈ s, Kb r r' ≤ L * P + 1 / δ ^ 2 := by
    intro r hr
    rw [← add_sum_erase s _ hr]
    simp only [hKb, if_pos rfl]
    refine add_le_add le_rfl ?_
    have hoff := sum_off_diag hδ hs hr
    calc ∑ x ∈ s.erase r, (if r = x then (L * P : ℝ) else 1 / (4 * dist0 (α r - α x) ^ 2))
        = ∑ x ∈ s.erase r, (1 / 4) * (1 / dist0 (α r - α x) ^ 2) := by
          apply sum_congr rfl; intro x hx
          rw [if_neg (ne_of_mem_erase hx).symm]
          field_simp
      _ = (1 / 4) * ∑ x ∈ s.erase r, 1 / dist0 (α r - α x) ^ 2 := by rw [mul_sum]
      _ ≤ (1 / 4) * (4 / δ ^ 2) := by linarith
      _ = 1 / δ ^ 2 := by ring
  calc X ≤ _ := step1
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * ∑ r' ∈ s, Kb r r' := step2
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * (L * P + 1 / δ ^ 2) :=
        sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (step3 r hr) (by positivity))
    _ = (L * P + 1 / δ ^ 2) * ∑ r ∈ s, ‖b r‖ ^ 2 := by rw [← sum_mul, mul_comm]

/-- **Dual large sieve.** -/
theorem dual_large_sieve {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hs : Spaced s α δ) (b : ι → ℂ) (M : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc M (M + N), ‖dualSum s α b n‖ ^ 2 ≤ (N + 2 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  set L : ℕ := ⌈1 / δ⌉₊ with hLdef
  have hinv : 0 < 1 / δ := by positivity
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by
    rw [hLdef]; exact (Nat.ceil_pos.2 hinv).ne')
  have hLge : 1 / δ ≤ L := Nat.le_ceil _
  have hLlt : (L : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one hinv.le
  set P : ℕ := N + L - 1 with hPdef
  set c : ℤ := M + 2 - L with hcdef
  set f : ℤ → ℝ := fun n => ‖dualSum s α b n‖ ^ 2 with hf
  set A := ∑ n ∈ Ioc M (M + N), f n with hA
  have hu : ∀ u ∈ range L, A ≤ ∑ v ∈ range P, f (c + u + v) := by
    intro u hu
    rw [mem_range] at hu
    have hsub : Ioc M (M + N) ⊆ (range P).image (fun v : ℕ => c + u + v) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [mem_image]
      refine ⟨(n - c - u).toNat, ?_, ?_⟩
      · rw [mem_range]; omega
      · omega
    have hinj : Set.InjOn (fun v : ℕ => c + u + v) (range P) := by
      intro v _ w _ h
      simp only at h
      omega
    calc A ≤ ∑ n ∈ (range P).image (fun v : ℕ => c + u + v), f n :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ v ∈ range P, f (c + u + v) := sum_image hinj
  have hsum : (L : ℝ) * A ≤ (L * P + 1 / δ ^ 2) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    calc (L : ℝ) * A = ∑ u ∈ range L, A := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ u ∈ range L, ∑ v ∈ range P, f (c + u + v) := sum_le_sum hu
      _ ≤ _ := shifted_bound hδ hs b c L P
  have hB0 : 0 ≤ ∑ r ∈ s, ‖b r‖ ^ 2 := sum_nonneg (fun _ _ => by positivity)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hPcast : (P : ℝ) = N + L - 1 := by
    rw [hPdef, Nat.cast_sub (by omega)]; push_cast; ring
  have hconst : (L * P + 1 / δ ^ 2) ≤ L * (N + 2 / δ) := by
    rw [hPcast]
    have h1 : 1 / δ ^ 2 ≤ L * (1 / δ) := by
      rw [show 1 / δ ^ 2 = (1 / δ) * (1 / δ) by ring]
      exact mul_le_mul_of_nonneg_right hLge hinv.le
    have h2 : (L : ℝ) * (L - 1) ≤ L * (1 / δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hLpos.le
    calc (L : ℝ) * (N + L - 1) + 1 / δ ^ 2 = L * N + L * (L - 1) + 1 / δ ^ 2 := by ring
      _ ≤ L * N + L * (1 / δ) + L * (1 / δ) := by linarith
      _ = L * (N + 2 / δ) := by ring
  have : (L : ℝ) * A ≤ L * ((N + 2 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) := by
    calc (L : ℝ) * A ≤ _ := hsum
      _ ≤ L * (N + 2 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := mul_le_mul_of_nonneg_right hconst hB0
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hLpos

/-- **The large sieve inequality**, constant `N + 2/δ`. -/
theorem large_sieve {s : Finset ι} {α : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hs : Spaced s α δ) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * e (n * α r)‖ ^ 2 ≤
      (N + 2 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
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
  have h3 := dual_large_sieve hδ hs b M N
  have hbX : ∑ r ∈ s, ‖b r‖ ^ 2 = X := by
    rw [hXdef]; apply sum_congr rfl; intro r _; rw [hb, Complex.norm_conj]
  rw [hbX] at h3
  set Aa := ∑ n ∈ I, ‖a n‖ ^ 2
  have hAa : 0 ≤ Aa := sum_nonneg (fun _ _ => by positivity)
  have hΔ : 0 ≤ (N : ℝ) + 2 / δ := by positivity
  have key : X ^ 2 ≤ Aa * ((N + 2 / δ) * X) := by
    calc X ^ 2 ≤ (∑ n ∈ I, ‖a n‖ * ‖dualSum s α b n‖) ^ 2 := pow_le_pow_left₀ hX0 h1 2
      _ ≤ Aa * ∑ n ∈ I, ‖dualSum s α b n‖ ^ 2 := h2
      _ ≤ Aa * ((N + 2 / δ) * X) := mul_le_mul_of_nonneg_left h3 hAa
  rcases eq_or_lt_of_le hX0 with h | h
  · rw [← h]; positivity
  · have : X * X ≤ X * ((N + 2 / δ) * Aa) := by nlinarith
    exact le_of_mul_le_mul_left this h

end LeanLab.PNTPort.LargeSieve
