module

public import Mathlib
public import LeanLab.HeathBrown1985.DivMoments
public import LeanLab.HeathBrown1985.Theorem2

/-!
P0096 Heath-Brown 1985, the bound 2.5: `Λ_Q(n) ≪ d(n) (log Q)²`, as on pages 48 to 49,
with `q/φ(q) ≪ log Q` for `q ≤ Q` taken from Elementary.lean.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

theorem divisors_gcd_eq (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    (n.gcd q).divisors = n.divisors.filter (· ∣ q) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left q (by omega)).ne'⟩

/-- `1/φ(q) ≤ e (1 + log Q / log 2) / q` for `1 ≤ q ≤ Q`. -/
theorem inv_totient_le (Q : ℝ) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q) :
    (Nat.totient q : ℝ)⁻¹ ≤ Real.exp 1 * (1 + Real.log Q / Real.log 2) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hl2 := Real.log_pos one_lt_two
  have h1 := div_totient_le q hq
  have hω : (q.primeFactors.card : ℝ) ≤ Real.log Q / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    exact (card_primeFactors_mul_log_two_le q hq).trans (Real.log_le_log hqR hqQ)
  have h2 : (q : ℝ) / Nat.totient q ≤ Real.exp 1 * (1 + Real.log Q / Real.log 2) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le)
  rw [le_div_iff₀ hqR]
  calc (Nat.totient q : ℝ)⁻¹ * q = q / Nat.totient q := by field_simp
    _ ≤ _ := h2

/-- **2.5, proved**: `|Λ_Q(n)| ≤ K d(n) (log Q)²` for `Q ≥ 2`, `n ≥ 1`. -/
theorem bound2_5 : Bound2_5 := by
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  refine ⟨2 * Real.exp 1 * (1 + 1 / l2) / l2, ?_⟩
  intro Q hQ n hn
  set F := ⌊Q⌋₊
  set ℓ := Real.log Q
  have hℓ : l2 ≤ ℓ := Real.log_le_log (by norm_num) hQ
  have hℓ0 : 0 < ℓ := by linarith
  set E := Real.exp 1 * (1 + ℓ / l2)
  have hE : 0 ≤ E := by positivity
  have hF : (F : ℝ) ≤ Q := Nat.floor_le (by linarith)
  unfold LambdaQ
  have hterm : ∀ q ∈ Icc 1 F, |((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
      ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| ≤
      ∑ d ∈ n.divisors.filter (· ∣ q), (d : ℝ) * (E / q) := by
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ Q := le_trans (by exact_mod_cast (mem_Icc.mp hq).2) hF
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hμ : (μ q : ℝ) ^ 2 ≤ 1 := by
      have h' : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [abs_nonneg (μ q : ℝ), sq_abs (μ q : ℝ)]
    have hc : 0 ≤ (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) := by positivity
    have hc1 : (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤ E / q := by
      calc (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤ 1 / (Nat.totient q : ℝ) :=
            div_le_div_of_nonneg_right hμ hφ.le
        _ = (Nat.totient q : ℝ)⁻¹ := one_div _
        _ ≤ E / q := inv_totient_le Q q hq1 hqQ
    have hsum : |∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| ≤
        ∑ d ∈ n.divisors.filter (· ∣ q), (d : ℝ) := by
      rw [divisors_gcd_eq n q hn hq1]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d _ => ?_))
      rw [abs_mul, Nat.abs_cast]
      have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [abs_nonneg (μ d : ℝ), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    rw [abs_mul, abs_of_nonneg hc, ← sum_mul]
    rw [mul_comm]
    exact mul_le_mul hsum hc1 hc (sum_nonneg (fun _ _ => by positivity))
  calc _ ≤ ∑ q ∈ Icc 1 F, |((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
        ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Icc 1 F, ∑ d ∈ n.divisors.filter (· ∣ q), (d : ℝ) * (E / q) := sum_le_sum hterm
    _ = ∑ d ∈ n.divisors, (d : ℝ) * (E * ∑ q ∈ (Icc 1 F).filter (d ∣ ·), (q : ℝ)⁻¹) := by
        rw [Finset.sum_comm' (t' := n.divisors) (s' := fun d => (Icc 1 F).filter (d ∣ ·))]
        · apply sum_congr rfl; intro d _
          rw [mul_sum, mul_sum]; apply sum_congr rfl; intro q _; ring
        · intro q d; simp only [mem_filter]; tauto
    _ ≤ ∑ d ∈ n.divisors, (d : ℝ) * (E * (Hn F / d)) := by
        apply sum_le_sum; intro d hd
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (sum_inv_multiples_le F d hd1) hE
    _ = (n.divisors.card : ℝ) * (E * Hn F) := by
        rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
        apply sum_congr rfl; intro d hd
        have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
        field_simp
        push_cast; ring
    _ ≤ (n.divisors.card : ℝ) * (E * (1 + ℓ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hE
        refine (Hn_le F).trans ?_
        have : Real.log F ≤ ℓ := by
          rcases Nat.eq_zero_or_pos F with h | h
          · rw [h]; simp; linarith
          · exact Real.log_le_log (by exact_mod_cast h) hF
        linarith
    _ ≤ (n.divisors.card : ℝ) * (2 * Real.exp 1 * (1 + 1 / l2) / l2 * ℓ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 : 1 + ℓ / l2 ≤ 2 * ℓ / l2 := by
          have : 1 ≤ ℓ / l2 := by rw [le_div_iff₀ hl2]; linarith
          have e : 2 * ℓ / l2 = ℓ / l2 + ℓ / l2 := by ring
          linarith
        have h2 : 1 + ℓ ≤ (1 + 1 / l2) * ℓ := by
          have : 1 ≤ ℓ / l2 := by rw [le_div_iff₀ hl2]; linarith
          have e : (1 + 1 / l2) * ℓ = ℓ + ℓ / l2 := by field_simp
          linarith
        have he := Real.exp_pos 1
        calc E * (1 + ℓ) ≤ (Real.exp 1 * (2 * ℓ / l2)) * ((1 + 1 / l2) * ℓ) := by
              apply mul_le_mul _ h2 (by linarith) (by positivity)
              exact mul_le_mul_of_nonneg_left h1 he.le
          _ = _ := by field_simp
    _ = _ := by ring

/-- **Theorem 2 of Heath-Brown 1985 from Lemma 1 alone**, 2.6 and 2.7. -/
theorem theorem2_of_lemma1_only (h6 : Lemma1_6) (h7 : Lemma1_7) : Theorem2 :=
  theorem2_of h6 (lemma2_of h7 bound2_5 divMoment2 divMoment3)

end LeanLab.HeathBrown1985
