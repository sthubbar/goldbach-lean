module

public import LeanLab.Linnik1951.Decomp357e

/-!
P0093 page 162 equation 7.4. Group the prime and power product by its finite fibers.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 162 definition of Psi. The unbounded prime and shifted
exponent fiber is equivalent to the bounded pair set used by the finite count. -/
noncomputable def prime_power_fiber_equiv357 (u : ℕ) :
    {t : Nat.Primes × ℕ // (t.1 : ℕ) + 2 ^ (t.2 + 1) = u} ≃
      {t : Fin (u + 1) × Fin (u + 1) //
        t.1.val.Prime ∧ 1 ≤ t.2.val ∧ u = t.1.val + 2 ^ t.2.val} where
  toFun t := by
    have hp_le : (t.val.1 : ℕ) ≤ u := (Nat.le_add_right _ _).trans_eq t.property
    have hp : (t.val.1 : ℕ) < u + 1 := Nat.lt_succ_of_le hp_le
    have hm_le : 2 ^ (t.val.2 + 1) ≤ u := (Nat.le_add_left _ _).trans_eq t.property
    have hm : t.val.2 + 1 < u + 1 :=
      (Nat.lt_two_pow_self.trans_le hm_le).trans (Nat.lt_succ_self u)
    exact ⟨(⟨t.val.1, hp⟩, ⟨t.val.2 + 1, hm⟩),
      t.val.1.property, Nat.succ_le_succ (Nat.zero_le _), t.property.symm⟩
  invFun t := ⟨(⟨t.val.1.val, t.property.1⟩, t.val.2.val - 1), by
    have he : t.val.2.val - 1 + 1 = t.val.2.val := by have := t.property.2.1; omega
    simpa only [he] using t.property.2.2.symm⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · apply Nat.Primes.coe_nat_injective
      rfl
    · simp
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp
      have := t.property.2.1
      omega

/-- P0093 page 162 equation 7.4. Summing a constant over a prime and power
fiber multiplies it by the exact finite representation count. -/
theorem prime_power_fiber_sum357 (u : ℕ) (z : ℂ) :
    (∑' t : {t : Nat.Primes × ℕ // (t.1 : ℕ) + 2 ^ (t.2 + 1) = u}, z) =
      (primePowerCount111 u : ℂ) * z := by
  classical
  rw [(prime_power_fiber_equiv357 u).tsum_eq (fun _ => z)]
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  congr 1
  unfold primePowerCount111
  norm_cast
  exact Fintype.card_subtype _

/-- P0093 page 154 damping and page 162 equation 7.4. The product term
for one prime and one positive power depends only on their natural sum. -/
theorem prime_power_term357 (N : ℕ) (α : ℝ) (p : Nat.Primes) (m : ℕ) :
    ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)) *
    ((Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)) =
    (Real.exp (-(((p : ℕ) + 2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) + 2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I) := by
  have hd : -(((p : ℕ) + 2 ^ (m + 1) : ℕ) : ℝ) / N =
      -((p : ℕ) : ℝ) / N + -((2 ^ (m + 1) : ℕ) : ℝ) / N := by push_cast; ring
  have he : ((-(2 * Real.pi * α * ((p : ℕ) + 2 ^ (m + 1) : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
      ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hd, he, Real.exp_add, Complex.ofReal_mul, Complex.exp_add]
  ring

/-- P0093 page 162 equation 7.4. Exact product_grouped280 statement,
proved by absolute convergence and the finite fiber equivalence. -/
theorem product_grouped_proved357 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111 N α * powerFourier111 N α =
      ∑' u : ℕ, (((primePowerCount111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) := by
  let f : Nat.Primes → ℂ := fun p =>
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  let g : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  let v : Nat.Primes × ℕ → ℕ := fun t => (t.1 : ℕ) + 2 ^ (t.2 + 1)
  let w : ℕ → ℂ := fun u => (Real.exp (-(u : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)
  have hf : Summable (fun p => ‖f p‖) := (prime_fourier_summable111 N hN α).norm
  have hg : Summable (fun m => ‖g m‖) := (power_fourier_summable111 N hN α).norm
  have hp : (∑' p, f p) * (∑' m, g m) = ∑' t : Nat.Primes × ℕ, f t.1 * g t.2 :=
    tsum_mul_tsum_of_summable_norm hf hg
  have hs := summable_mul_of_summable_norm hf hg
  have hv := hs.hasSum.tsum_fiberwise v
  change (∑' p, f p) * (∑' m, g m) = _
  rw [hp, ← hv.tsum_eq]
  apply tsum_congr
  intro u
  have ht : (∑' t : {t : Nat.Primes × ℕ // v t = u}, f t.val.1 * g t.val.2) =
      ∑' t : {t : Nat.Primes × ℕ // v t = u}, w u := by
    apply tsum_congr
    intro t
    change _ = w u
    rw [show f t.val.1 * g t.val.2 = w (v t.val) from
      prime_power_term357 N α t.val.1 t.val.2, t.property]
  change (∑' t : {t : Nat.Primes × ℕ // v t = u}, f t.val.1 * g t.val.2) = _
  rw [ht]
  change (∑' t : {t : Nat.Primes × ℕ // (t.1 : ℕ) + 2 ^ (t.2 + 1) = u}, w u) = _
  rw [prime_power_fiber_sum357]
  dsimp [w]
  push_cast
  ring

end LeanLab.Linnik1951
