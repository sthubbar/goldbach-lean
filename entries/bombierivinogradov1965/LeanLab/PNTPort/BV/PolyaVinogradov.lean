module

public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
# The Polya-Vinogradov inequality

Lab proof. AI wrote this file. Known mathematics, the Polya-Vinogradov inequality of 1918,
no cited input. Uses Mathlib's Gauss sums for primitive Dirichlet characters.

For a primitive Dirichlet character `χ` modulo `q > 1` and any interval `M < n ≤ M + N`,

  `‖∑_{M<n≤M+N} χ(n)‖ ≤ √q (1 + log q)`.

Route: `χ⁻¹(n) τ(χ) = ∑_x χ(x) ψ(n x)`, so `√q ‖∑ χ⁻¹(n)‖ ≤ ∑_{0<c<q} ‖∑_n e(n c / q)‖`,
each geometric sum is at most `1/(2‖c/q‖) ≤ (q/c + q/(q-c))/2`, and the harmonic bound
`H_{q-1} ≤ 1 + log q` finishes.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Complex Finset Real LeanLab.PNTPort.LargeSieve

lemma sum_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R] (f : ℤ → R) (M : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc M (M + N), f n = ∑ k ∈ range N, f (M + 1 + k) := by
  refine sum_nbij' (fun n => (n - M - 1).toNat) (fun k => M + 1 + k) ?_ ?_ ?_ ?_ ?_ <;>
    intro n hn <;> simp only [mem_Ioc, mem_range] at hn ⊢
  · omega
  · omega
  · omega
  · omega
  · congr 1; omega

/-- Geometric sum over an interval. -/
lemma norm_sum_Ioc_e_le (M : ℤ) (N : ℕ) {θ : ℝ} (h : 0 < dist0 θ) :
    ‖∑ n ∈ Ioc M (M + N), e (n * θ)‖ ≤ 1 / (2 * dist0 θ) := by
  rw [sum_Ioc_eq_sum_range (fun n : ℤ => e (n * θ))]
  have : ∀ k ∈ range N, e (((M + 1 + k : ℤ) : ℝ) * θ) = e ((M + 1 : ℤ) * θ) * e (k * θ) := by
    intro k _
    rw [← e_add]; congr 1; push_cast; ring
  rw [sum_congr rfl this, ← mul_sum, norm_mul, norm_e, one_mul]
  exact norm_geom_le N h

/-- For `0 < c < q`, `1/(2‖c/q‖) ≤ (q/c + q/(q-c))/2`. -/
lemma inv_two_dist0_le {q c : ℝ} (hc : 0 < c) (hcq : c < q) :
    0 < dist0 (c / q) ∧ 1 / (2 * dist0 (c / q)) ≤ (q / c + q / (q - c)) / 2 := by
  have hq : 0 < q := hc.trans hcq
  set z := round (c / q)
  have hd : dist0 (c / q) = |c / q - z| := rfl
  have hA : 0 < q / c := div_pos hq hc
  have hB : 0 < q / (q - c) := div_pos hq (by linarith)
  rcases le_or_gt z 0 with hz | hz
  · have hz' : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have hlow : c / q ≤ dist0 (c / q) := by
      rw [hd]; exact le_trans (by linarith) (le_abs_self _)
    have hpos : 0 < c / q := div_pos hc hq
    refine ⟨hpos.trans_le hlow, ?_⟩
    have : 1 / (2 * dist0 (c / q)) ≤ 1 / (2 * (c / q)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [show 1 / (2 * (c / q)) = q / c / 2 by field_simp] at this
    linarith
  · have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
    have hlow : (q - c) / q ≤ dist0 (c / q) := by
      rw [hd, sub_div, div_self hq.ne']
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    have hpos : 0 < (q - c) / q := div_pos (by linarith) hq
    refine ⟨hpos.trans_le hlow, ?_⟩
    have : 1 / (2 * dist0 (c / q)) ≤ 1 / (2 * ((q - c) / q)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [show 1 / (2 * ((q - c) / q)) = q / (q - c) / 2 by
      field_simp [(by linarith : q - c ≠ 0)]] at this
    linarith

/-- `∑_{0<c<q} (q/c + q/(q-c))/2 ≤ q (1 + log q)`. -/
lemma sum_harmonic_le {q : ℕ} (hq : 1 < q) :
    ∑ k ∈ range (q - 1), ((q : ℝ) / (k + 1) + q / (q - (k + 1))) / 2 ≤
      q * (1 + Real.log q) := by
  have hH : ∑ k ∈ range (q - 1), (q : ℝ) / (k + 1) = q * (harmonic (q - 1) : ℝ) := by
    rw [harmonic]; push_cast; rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [div_eq_mul_inv]
  have hR : ∑ k ∈ range (q - 1), (q : ℝ) / (q - (k + 1)) =
      ∑ k ∈ range (q - 1), (q : ℝ) / (k + 1) := by
    rw [← sum_range_reflect (fun k : ℕ => (q : ℝ) / (k + 1)) (q - 1)]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [← sum_div, sum_add_distrib, hR, hH]
  have h1 := harmonic_le_one_add_log (q - 1)
  have h2 : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := by
    apply Real.log_le_log
    · have : 1 ≤ q - 1 := by omega
      exact_mod_cast this
    · exact_mod_cast Nat.sub_le q 1
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith

/-- **Polya-Vinogradov.** For a primitive Dirichlet character modulo `q > 1`,
`‖∑_{M<n≤M+N} χ(n)‖ ≤ √q (1 + log q)`. -/
theorem polya_vinogradov {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), χ (n : ZMod q)‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  have : Fact (1 < q) := ⟨hq⟩
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  set τ := gaussSum χ ψ
  set I := Ioc M (M + N)
  set S := ∑ n ∈ I, χ (n : ZMod q)
  set S' := ∑ n ∈ I, χ⁻¹ (n : ZMod q)
  have hSS' : ‖S'‖ = ‖S‖ := by
    have : S' = (starRingEnd ℂ) S := by
      rw [map_sum]; exact sum_congr rfl fun n _ => (conj_char_eq_inv χ _).symm
    rw [this, Complex.norm_conj]
  set T : ZMod q → ℂ := fun x => ∑ n ∈ I, ψ ((n : ZMod q) * x)
  have key : S' * τ = ∑ x : ZMod q, χ x * T x := by
    have hg : ∀ n : ZMod q, χ⁻¹ n * τ = ∑ x : ZMod q, χ x * ψ (n * x) := by
      intro n
      rw [← gaussSum_mulShift_of_isPrimitive ψ hχ, gaussSum]
      rfl
    rw [sum_mul]
    simp_rw [hg]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    simp only [T, mul_sum]
  have hτ : ‖τ‖ = Real.sqrt q := by
    rw [← normSq_gaussSum_of_isPrimitive hχ, Real.sqrt_sq (norm_nonneg _)]
  have hT : ∀ k ∈ range (q - 1), ‖T ((k + 1 : ℕ) : ZMod q)‖ ≤
      ((q : ℝ) / (k + 1) + q / (q - (k + 1))) / 2 := by
    intro k hk
    rw [mem_range] at hk
    have hc : (0 : ℝ) < k + 1 := by positivity
    have hcq : (k : ℝ) + 1 < q := by
      have : k + 1 < q := by omega
      exact_mod_cast this
    obtain ⟨hpos, hle⟩ := inv_two_dist0_le hc hcq
    have : T ((k + 1 : ℕ) : ZMod q) = ∑ n ∈ I, e (n * (((k + 1 : ℕ) : ℝ) / q)) := by
      exact sum_congr rfl fun n _ => stdAddChar_mul_natCast n (k + 1)
    rw [this]
    push_cast
    exact (norm_sum_Ioc_e_le M N hpos).trans hle
  have hbound : ‖S' * τ‖ ≤ q * (1 + Real.log q) := by
    have hr : range q = range (q - 1 + 1) := by congr 1; omega
    rw [key, sum_zmod_eq_sum_range, hr, sum_range_succ']
    simp only [Nat.cast_zero, MulChar.map_zero, zero_mul, add_zero]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (sum_harmonic_le hq)
    refine sum_le_sum fun k hk => ?_
    rw [norm_mul]
    calc ‖χ ((k + 1 : ℕ) : ZMod q)‖ * ‖T ((k + 1 : ℕ) : ZMod q)‖
        ≤ 1 * ‖T ((k + 1 : ℕ) : ZMod q)‖ :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hT k hk
  rw [norm_mul, hSS', hτ] at hbound
  have hsq : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < q))
  have hqq : (q : ℝ) = Real.sqrt q * Real.sqrt q := (Real.mul_self_sqrt (Nat.cast_nonneg q)).symm
  have h2 : Real.sqrt q * ‖S‖ ≤ Real.sqrt q * (Real.sqrt q * (1 + Real.log q)) := by
    rw [← mul_assoc, ← hqq]; linarith
  exact le_of_mul_le_mul_left h2 hsq

/-- Initial segments of the naturals. -/
theorem polya_vinogradov_Icc {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 y, χ n‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  have h := polya_vinogradov hq hχ 0 y
  have : ∑ n ∈ Finset.Icc 1 y, χ n = ∑ n ∈ Ioc (0 : ℤ) (0 + y), χ (n : ZMod q) := by
    refine sum_nbij' (fun n : ℕ => (n : ℤ)) (fun n : ℤ => n.toNat) ?_ ?_ ?_ ?_ ?_ <;>
      intro n hn <;> simp only [mem_Ioc, mem_Icc] at hn ⊢
    · omega
    · omega
    · omega
    · omega
    · simp
  rw [this]; exact h

end LeanLab.PNTPort.BV
