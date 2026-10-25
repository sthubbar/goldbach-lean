module

public import LeanLab.PNTPort.Vinogradov.Block

/-!
# Vinogradov's minor arc bound, the sums `∑ min(Y, 1/‖αm‖)` and `∑ min(X/m, 1/‖αm‖)`

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input. Vaughan,
The Hardy-Littlewood method, Lemma 2.2; Davenport, Multiplicative number theory, ch. 25.

For `(a, q) = 1`, `q ≥ 1`, `|α - a/q| ≤ 1/q²`:
* `small_bound`: `∑_{1 ≤ m ≤ q/2} G (Y m) (α m) ≤ 2q (1 + log q)` for any `Y`.
* `sum_G_le`: `∑_{1 ≤ m ≤ M} G Y (α m) ≤ (M/q + 1)(4Y + q(1 + log q))`.
* `sum_G_div_le`: `∑_{1 ≤ m ≤ M} G (X/m) (α m) ≤ 12 (X/q + M + q)(1 + log q + log M)`, `M ≥ 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open LeanLab.PNTPort.LargeSieve

lemma sum_inv_Icc_le (q : ℕ) :
    ∑ j ∈ Icc 1 (q - 1), (1 / (j : ℝ)) ≤ 1 + Real.log q := by
  have h := harmonic_le_one_add_log (q - 1)
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simp only [one_div]
  refine h.trans ?_
  rcases Nat.lt_or_ge q 2 with hq | hq
  · rw [show q - 1 = 0 by omega]; simpa using Real.log_natCast_nonneg q
  · gcongr
    · exact_mod_cast (show 0 < q - 1 by omega)
    · exact_mod_cast Nat.sub_le q 1

lemma sum_inv_Icc_reflect_le (q : ℕ) :
    ∑ j ∈ Icc 1 (q - 1), (1 / ((q : ℝ) - j)) ≤ 1 + Real.log q := by
  refine le_of_eq_of_le ?_ (sum_inv_Icc_le q)
  refine sum_nbij' (fun j => q - j) (fun j => q - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hj ⊢; omega
  · intro j hj; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hj ⊢; omega
  · intro j hj; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hj; omega
  · intro j hj; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hj; omega
  · intro j hj
    simp only [mem_Icc] at hj
    rw [Nat.cast_sub (by omega)]

/-- Small multipliers, `1 ≤ m ≤ q/2`: here `‖αm‖ ≥ ‖am/q‖/2`. -/
theorem small_bound {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (Y : ℕ → ℝ) :
    ∑ m ∈ Icc 1 (q / 2), G (Y m) (α * m) ≤ 2 * q * (1 + Real.log q) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  set J : ℕ → ℕ := fun m => ((a * m) % (q : ℤ)).toNat with hJ
  have hJnn : ∀ m : ℕ, 0 ≤ (a * m) % (q : ℤ) := fun m => Int.emod_nonneg _ hqz.ne'
  have hJcast : ∀ m : ℕ, ((J m : ℕ) : ℤ) = (a * m) % (q : ℤ) :=
    fun m => Int.toNat_of_nonneg (hJnn m)
  have hJlt : ∀ m, J m < q := by
    intro m
    have := Int.emod_lt_of_pos (a * m) hqz
    have h2 := hJcast m
    omega
  have hJpos : ∀ m ∈ Icc 1 (q / 2), 1 ≤ J m := by
    intro m hm
    have hm' := mem_Icc.1 hm
    by_contra h0
    have h0' : J m = 0 := by omega
    have : (q : ℤ) ∣ (m : ℤ) * a := by
      have := hJcast m
      rw [h0'] at this
      rw [mul_comm]; exact Int.dvd_of_emod_eq_zero this.symm
    have h4 : (q : ℤ) ∣ (m : ℤ) := hcop.symm.dvd_of_dvd_mul_right this
    have h5 : (q : ℕ) ∣ m := by exact_mod_cast h4
    have := Nat.le_of_dvd (by omega) h5
    omega
  have hterm : ∀ m ∈ Icc 1 (q / 2), G (Y m) (α * m) ≤
      q * (1 / (J m : ℝ)) + q * (1 / ((q : ℝ) - J m)) := by
    intro m hm
    have hm' := mem_Icc.1 hm
    have hJ1 : (1 : ℝ) ≤ J m := by exact_mod_cast hJpos m hm
    have hJq : (J m : ℝ) + 1 ≤ q := by exact_mod_cast hJlt m
    have hm2 : (2 : ℝ) * m ≤ q := by
      have : 2 * m ≤ q := by omega
      exact_mod_cast this
    set δ : ℝ := (α - a / q) * m with hδ
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hδb : |δ| ≤ 1 / (2 * q) := by
      rw [hδ, abs_mul, abs_of_nonneg hm0]
      calc |α - a / q| * m ≤ 1 / (q : ℝ) ^ 2 * (q / 2) := by gcongr; linarith
        _ = 1 / (2 * q) := by field_simp
    set x : ℝ := (J m : ℝ) / q with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := by rw [hx, div_le_one hqpos]; linarith
    have hdiv := Int.mul_ediv_add_emod (a * m) (q : ℤ)
    have hdecomp : α * m = x + (((a * m) / (q : ℤ) : ℤ) : ℝ) + δ := by
      have h1 : ((a * m : ℤ) : ℝ) = q * (((a * m) / (q : ℤ) : ℤ) : ℝ) + (J m : ℝ) := by
        have : ((J m : ℕ) : ℝ) = (((a * m) % (q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hJcast m
        rw [this]; exact_mod_cast hdiv.symm
      have h2 : (((a * m) / (q : ℤ) : ℤ) : ℝ) = (((a * m : ℤ) : ℝ) - J m) / q := by
        field_simp; linarith
      rw [h2, hx, hδ]
      push_cast
      field_simp; ring
    have hlow := dist0_ge hx0 hx1 ((a * m) / (q : ℤ)) (y := δ)
    rw [← hdecomp] at hlow
    set μ : ℝ := min (J m : ℝ) ((q : ℝ) - J m) with hμ
    have hμ1 : 1 ≤ μ := le_min hJ1 (by linarith)
    have hmin : μ / q ≤ min x (1 - x) := by
      rw [le_min_iff]; constructor
      · rw [hx]; gcongr; exact min_le_left _ _
      · calc μ / q ≤ ((q : ℝ) - J m) / q := by gcongr; exact min_le_right _ _
          _ = 1 - x := by rw [hx]; field_simp
    have hd : μ / (2 * q) ≤ dist0 (α * m) := by
      have : μ / (2 * q) ≤ μ / q - 1 / (2 * q) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
    have hdpos : 0 < dist0 (α * m) := lt_of_lt_of_le (by positivity) hd
    refine (G_le_inv hdpos).trans ?_
    calc 1 / (2 * dist0 (α * m)) ≤ 1 / (2 * (μ / (2 * q))) := by gcongr
      _ = q / μ := by field_simp
      _ ≤ q * (1 / (J m : ℝ)) + q * (1 / ((q : ℝ) - J m)) := by
          rcases min_choice (J m : ℝ) ((q : ℝ) - J m) with h | h
          · rw [hμ, h]
            have : 0 ≤ (q : ℝ) * (1 / ((q : ℝ) - J m)) :=
              mul_nonneg hqpos.le (div_nonneg zero_le_one (by linarith))
            rw [mul_one_div]; linarith
          · rw [hμ, h]
            have : 0 ≤ (q : ℝ) * (1 / (J m : ℝ)) :=
              mul_nonneg hqpos.le (div_nonneg zero_le_one (by linarith))
            rw [mul_one_div (q : ℝ) ((q : ℝ) - J m)]; linarith
  have hinj : Set.InjOn J (Icc 1 (q / 2) : Set ℕ) := by
    intro m1 hm1 m2 hm2 heq
    simp only [coe_Icc, Set.mem_Icc] at hm1 hm2
    have h1 : (a * m1) % (q : ℤ) = (a * m2) % (q : ℤ) := by
      rw [← hJcast, ← hJcast]; exact_mod_cast heq
    have h2 : (q : ℤ) ∣ a * m1 - a * m2 := Int.ModEq.dvd h1.symm
    rw [show a * (m1 : ℤ) - a * m2 = ((m1 : ℤ) - m2) * a by ring] at h2
    have h4 : (q : ℤ) ∣ (m1 : ℤ) - m2 := hcop.symm.dvd_of_dvd_mul_right h2
    have h5 : |(m1 : ℤ) - m2| < q := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h4 h5
    omega
  set f : ℕ → ℝ := fun j => q * (1 / (j : ℝ)) + q * (1 / ((q : ℝ) - j)) with hf
  calc ∑ m ∈ Icc 1 (q / 2), G (Y m) (α * m) ≤ ∑ m ∈ Icc 1 (q / 2), f (J m) := sum_le_sum hterm
    _ = ∑ j ∈ (Icc 1 (q / 2)).image J, f j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ Icc 1 (q - 1), f j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨m, hm, rfl⟩ := mem_image.1 hj
          have := hJpos m hm; have := hJlt m
          exact mem_Icc.2 ⟨by omega, by omega⟩
        · intro j hj _
          have hj' := mem_Icc.1 hj
          have : (j : ℝ) + 1 ≤ q := by exact_mod_cast (show j + 1 ≤ q by omega)
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          simp only [hf]
          apply add_nonneg <;> apply mul_nonneg hqpos.le <;> apply div_nonneg zero_le_one <;>
            linarith
    _ = q * ∑ j ∈ Icc 1 (q - 1), (1 / (j : ℝ)) + q * ∑ j ∈ Icc 1 (q - 1), (1 / ((q : ℝ) - j)) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ q * (1 + Real.log q) + q * (1 + Real.log q) := by
        gcongr
        · exact sum_inv_Icc_le q
        · exact sum_inv_Icc_reflect_le q
    _ = 2 * q * (1 + Real.log q) := by ring

/-- Splitting `(0, B q]` into `B` blocks of length `q`. -/
lemma sum_Ioc_blocks (f : ℕ → ℝ) (q B : ℕ) :
    ∑ m ∈ Ioc 0 (B * q), f m = ∑ i ∈ range B, ∑ m ∈ Ioc (i * q) (i * q + q), f m := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, show (n + 1) * q = n * q + q by ring]
    exact (sum_Ioc_consecutive f (Nat.zero_le _) (Nat.le_add_right _ _)).symm

lemma sum_Icc_le_blocks {f : ℕ → ℝ} (hf : ∀ m, 0 ≤ f m) {q : ℕ} (hq : 1 ≤ q) (M : ℕ) :
    ∑ m ∈ Icc 1 M, f m ≤ ∑ i ∈ range (M / q + 1), ∑ m ∈ Ioc (i * q) (i * q + q), f m := by
  rw [← sum_Ioc_blocks]
  apply sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [mem_Icc, mem_Ioc] at hm ⊢
    have := Nat.lt_div_mul_add (a := M) (b := q) (by omega)
    constructor
    · omega
    · nlinarith [Nat.div_add_mod M q, Nat.mod_lt M (show q > 0 by omega)]
  · intro _ _ _; exact hf _

/-- `∑_{1 ≤ m ≤ M} G Y (α m) ≤ (M/q + 1)(4Y + q(1 + log q))`. -/
theorem sum_G_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (M : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ m ∈ Icc 1 M, G Y (α * m) ≤ ((M : ℝ) / q + 1) * (4 * Y + q * (1 + Real.log q)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine (sum_Icc_le_blocks (f := fun m => G Y (α * m)) (fun m => G_nonneg hY _) hq M).trans ?_
  refine (sum_le_sum fun i _ => block_bound hq hcop hα (i * q) hY).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have hW : 0 ≤ 4 * Y + q * (1 + Real.log q) := by
    have := Real.log_natCast_nonneg q; positivity
  apply mul_le_mul_of_nonneg_right _ hW
  push_cast
  have : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / q := Nat.cast_div_le
  linarith

lemma harmonic_div_le (M q : ℕ) (hq : 1 ≤ q) :
    ((harmonic (M / q) : ℚ) : ℝ) ≤ 1 + Real.log M := by
  refine (harmonic_le_one_add_log _).trans ?_
  rcases Nat.eq_zero_or_pos (M / q) with h | h
  · rw [h]; simpa using Real.log_natCast_nonneg M
  · gcongr
    exact_mod_cast Nat.div_le_self M q

/-- `∑_{1 ≤ m ≤ M} min(X/m, 1/(2‖αm‖)) ≤ 12 (X/q + M + q)(1 + log q + log M)`. -/
theorem sum_G_div_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (M : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ m ∈ Icc 1 M, G (X / m) (α * m) ≤
      12 * (X / q + M + q) * (1 + Real.log q + Real.log M) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlq := Real.log_natCast_nonneg q
  have hlM := Real.log_natCast_nonneg M
  set g : ℕ → ℝ := fun m => G (X / m) (α * m) with hg
  have hgnn : ∀ m, 0 ≤ g m := fun m => G_nonneg (div_nonneg hX (Nat.cast_nonneg m)) _
  refine (sum_Icc_le_blocks hgnn hq M).trans ?_
  rw [sum_range_succ']
  -- block zero
  have hF0 : ∑ m ∈ Ioc (0 * q) (0 * q + q), g m ≤
      2 * q * (1 + Real.log q) + (8 * (X / q) + q * (1 + Real.log q)) := by
    rw [zero_mul, zero_add]
    rw [← sum_filter_add_sum_filter_not (Ioc 0 q) (fun m => m ≤ q / 2)]
    gcongr
    · calc ∑ m ∈ (Ioc 0 q).filter (fun m => m ≤ q / 2), g m ≤ ∑ m ∈ Icc 1 (q / 2), g m := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro m hm; simp only [mem_filter, mem_Ioc, mem_Icc] at hm ⊢; omega
            · intro m _ _; exact hgnn m
        _ ≤ _ := small_bound hq hcop hα (fun m => X / m)
    · calc ∑ m ∈ (Ioc 0 q).filter (fun m => ¬ m ≤ q / 2), g m
            ≤ ∑ m ∈ (Ioc 0 q).filter (fun m => ¬ m ≤ q / 2), G (2 * X / q) (α * m) := by
            apply sum_le_sum
            intro m hm
            simp only [mem_filter, mem_Ioc] at hm
            apply G_mono
            have h2 : q < 2 * m := by omega
            have h2' : (q : ℝ) ≤ 2 * m := by exact_mod_cast h2.le
            have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
            rw [div_le_div_iff₀ hm0 hqpos]; nlinarith
        _ ≤ ∑ m ∈ Ioc 0 (0 + q), G (2 * X / q) (α * m) := by
            rw [zero_add]
            apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            intro m _ _; exact G_nonneg (by positivity) _
        _ ≤ 4 * (2 * X / q) + q * (1 + Real.log q) := block_bound hq hcop hα 0 (by positivity)
        _ = 8 * (X / q) + q * (1 + Real.log q) := by ring
  -- blocks i + 1
  have hFi : ∀ i ∈ range (M / q), ∑ m ∈ Ioc ((i + 1) * q) ((i + 1) * q + q), g m ≤
      4 * (X / q) * (1 / ((i + 1 : ℕ) : ℝ)) + q * (1 + Real.log q) := by
    intro i _
    have hiq : (0 : ℝ) < ((i + 1) * q : ℕ) := by
      have : 0 < (i + 1) * q := Nat.mul_pos (Nat.succ_pos i) hq
      exact_mod_cast this
    calc ∑ m ∈ Ioc ((i + 1) * q) ((i + 1) * q + q), g m
          ≤ ∑ m ∈ Ioc ((i + 1) * q) ((i + 1) * q + q), G (X / ((i + 1) * q : ℕ)) (α * m) := by
          apply sum_le_sum
          intro m hm
          simp only [mem_Ioc] at hm
          apply G_mono
          have : (((i + 1) * q : ℕ) : ℝ) ≤ m := by exact_mod_cast hm.1.le
          exact div_le_div_of_nonneg_left hX hiq this
      _ ≤ 4 * (X / ((i + 1) * q : ℕ)) + q * (1 + Real.log q) :=
          block_bound hq hcop hα _ (div_nonneg hX hiq.le)
      _ = 4 * (X / q) * (1 / ((i + 1 : ℕ) : ℝ)) + q * (1 + Real.log q) := by
          push_cast; field_simp
  refine (add_le_add (sum_le_sum hFi) hF0).trans ?_
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hH : ∑ i ∈ range (M / q), (1 / ((i + 1 : ℕ) : ℝ)) = ((harmonic (M / q) : ℚ) : ℝ) := by
    rw [harmonic]; push_cast; simp only [one_div]
  rw [hH]
  have h1 := harmonic_div_le M q hq
  have h2 : ((M / q : ℕ) : ℝ) * q ≤ M := by
    have := Nat.div_mul_le_self M q; exact_mod_cast this
  have hXq : 0 ≤ X / q := by positivity
  have e1 : 4 * (X / q) * ((harmonic (M / q) : ℚ) : ℝ) ≤ 4 * (X / q) * (1 + Real.log M) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e2 : ((M / q : ℕ) : ℝ) * (q * (1 + Real.log q)) ≤ M * (1 + Real.log q) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hL : 1 ≤ 1 + Real.log q + Real.log M := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith [mul_nonneg hXq hlq, mul_nonneg hXq hlM, mul_nonneg hM0 hlq, mul_nonneg hM0 hlM,
    mul_nonneg hqpos.le hlq, mul_nonneg hqpos.le hlM]

end LeanLab.PNTPort.Vinogradov

