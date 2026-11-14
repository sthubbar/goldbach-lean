module

public import LeanLab.AlmostPrimes.DDLemma23

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T1203Z-2488, unit U-0948.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
Lemma 2.3 and its proof by Rankin's trick, read in Claude in Chrome on arxiv.org/html/2602.22720.

The paper bounds `R₄(A, D) ≤ Σ_{d ∣ P(z), d < D} τ₈(d)`, using `|r_d(A)| ≤ τ(d)` from Nathanson's
Theorem 7.2, then proves the divisor sum is below `0.591 D log⁸ z` at `D = z^{18.4}`. A squarefree
`d ∣ P(z)` is a set `s` of primes below `z` and `τ₈(d) = 8^{|s|}`.
PROVED `rankin_sum_lt`: for a finite set `P` of primes, all below `z`, with `z ≥ 10¹⁰`, the sum of
`8^{|s|}` over `s ⊆ P` with `∏ s < z^{18.4}` is below `0.591 z^{18.4} log⁸ z`, CONDITIONAL ON the
two Rosser-Schoenfeld bounds `Σ_{p ∈ P} 1/p < log log z + 0.2634` and `Σ_{p ∈ P} log p / p < log z`,
which the paper cites from Rosser and Schoenfeld 1962 Theorem 5 for `P` the primes below `z`.
The step `R₄ ≤ Σ τ₈` stays with the paper. Goldbach is open.
-/

@[expose] public section

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.DDLemma23

/-- **Lemma 2.3 by Rankin's trick.** CONDITIONAL ON the two Rosser-Schoenfeld sums. -/
theorem rankin_sum_lt (z : ℝ) (hz : 10 ^ 10 ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < z)
    (hRS1 : ∑ p ∈ P, (1 : ℝ) / p < log (log z) + 0.2634)
    (hRS2 : ∑ p ∈ P, log p / p < log z) :
    ∑ s ∈ P.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < z ^ (18.4 : ℝ)),
        (8 : ℝ) ^ s.card < 0.591 * z ^ (18.4 : ℝ) * log z ^ 8 := by
  have hz0 : 0 < z := by linarith
  set L := log z with hLdef
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hz0]
    have : exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hL0 : 0 < L := by linarith
  set α : ℝ := 0.457 with hα
  set η := α / L with hη
  set δ := 1 - η with hδ
  have hα1 : α < 1 := by rw [hα]; norm_num
  have hα0' : 0 < α := by rw [hα]; norm_num
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η < 1 := by rw [hη, div_lt_one hL0]; linarith
  have hδ0 : 0 ≤ δ := by linarith
  set D := z ^ (18.4 : ℝ) with hD
  have hD0 : 0 < D := by positivity
  have hp0 : ∀ p ∈ P, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hP p hp).1.pos
  have hp1 : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hP p hp).1.one_lt.le
  -- weights
  set w : ℕ → ℝ := fun p => 8 * (p : ℝ) ^ (-δ) with hw
  -- step 1: each term is at most 8^|s| (D/∏s)^δ = D^δ ∏_{p∈s} w p
  have step1 : ∑ s ∈ P.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), (8 : ℝ) ^ s.card ≤
      ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p := by
    calc _ ≤ ∑ s ∈ P.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), D ^ δ * ∏ p ∈ s, w p := by
          apply Finset.sum_le_sum
          intro s hs
          rw [Finset.mem_filter, Finset.mem_powerset] at hs
          have hpos : 0 < ∏ p ∈ s, (p : ℝ) := Finset.prod_pos fun p hp => hp0 p (hs.1 hp)
          have e : D ^ δ * ∏ p ∈ s, w p = (8 : ℝ) ^ s.card * (D / ∏ p ∈ s, (p : ℝ)) ^ δ := by
            rw [hw, Finset.prod_mul_distrib, Finset.prod_const,
              Real.div_rpow hD0.le hpos.le,
              Real.finsetProd_rpow s _ (fun p hp => (hp0 p (hs.1 hp)).le)]
            rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity),
              ← Real.finsetProd_rpow s _ (fun p hp => (hp0 p (hs.1 hp)).le)]
            ring
          rw [e]
          have : 1 ≤ (D / ∏ p ∈ s, (p : ℝ)) ^ δ :=
            Real.one_le_rpow (by rw [le_div_iff₀ hpos]; linarith [hs.2]) hδ0
          have h8 : (0 : ℝ) ≤ 8 ^ s.card := by positivity
          nlinarith
      _ ≤ ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro s hs _
          rw [Finset.mem_powerset] at hs
          apply mul_nonneg (by positivity)
          apply Finset.prod_nonneg
          intro p hp; rw [hw]; have := hp0 p (hs hp); positivity
  -- step 2: Σ_{s ⊆ P} ∏ w = ∏ (1 + w) ≤ exp (Σ w)
  have step2 : ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p ≤ D ^ δ * exp (∑ p ∈ P, w p) := by
    rw [← Finset.mul_sum, ← Finset.prod_one_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun p hp => by rw [hw]; have := hp0 p hp; positivity)
      (fun p _ => by have := Real.add_one_le_exp (w p); linarith)
  -- step 3: w p ≤ 8/p + 8 η e^α log p / p
  have step3 : ∑ p ∈ P, w p ≤ 8 * ∑ p ∈ P, (1 : ℝ) / p + 8 * η * exp α * ∑ p ∈ P, log p / p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := hp0 p hp
    have hlp : 0 ≤ log p := Real.log_nonneg (hp1 p hp)
    have hlpz : log p ≤ L := by rw [hLdef]; exact Real.log_le_log hp' (hP p hp).2.le
    -- p^{-δ} = exp(η log p) / p
    have e1 : (p : ℝ) ^ (-δ) = exp (η * log p) / p := by
      rw [Real.rpow_def_of_pos hp', hδ, show log p * -(1 - η) = η * log p - log p by ring,
        Real.exp_sub, Real.exp_log hp']
    have hx : η * log p ≤ α := by
      calc η * log p ≤ η * L := mul_le_mul_of_nonneg_left hlpz hη0.le
        _ = α := by rw [hη]; field_simp
    have e2 : exp (η * log p) ≤ 1 + η * log p * exp α := by
      have := exp_le_one_add_mul_exp (η * log p)
      have : η * log p * exp (η * log p) ≤ η * log p * exp α :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hx) (by positivity)
      linarith
    rw [hw]; simp only
    rw [e1]
    have : exp (η * log p) / p ≤ (1 + η * log p * exp α) / p := div_le_div_of_nonneg_right e2 hp'.le
    have e3 : 8 * ((1 + η * log p * exp α) / p) = 8 * (1 / p) + 8 * η * exp α * (log p / p) := by
      field_simp
    nlinarith
  -- assemble the exponent
  have hexp : ∑ p ∈ P, w p ≤ 8 * log L + 2.1072 + 8 * α * exp α := by
    have h1 := hRS1
    have h2 : 8 * η * exp α * ∑ p ∈ P, log p / p ≤ 8 * α * exp α := by
      have hηL : η * L = α := by rw [hη]; field_simp
      have : 8 * η * exp α * ∑ p ∈ P, log p / p ≤ 8 * η * exp α * L :=
        mul_le_mul_of_nonneg_left hRS2.le (by positivity)
      have e : 8 * η * exp α * L = 8 * α * exp α := by rw [← hηL]; ring
      exact this.trans e.le
    have h1' : 8 * ∑ p ∈ P, (1 : ℝ) / p ≤ 8 * log L + 2.1072 := by
      have := mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 8)
      rw [mul_add, const_2_1072] at this
      linarith
    linarith
  -- D^δ = D e^{-18.4 α}
  have hDδ : D ^ δ = D * exp (-(18.4 * α)) := by
    rw [hD, ← Real.rpow_mul hz0.le, Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hz0,
      ← Real.exp_add, ← hLdef, hδ, hη]
    congr 1
    field_simp
    ring
  have hL8 : exp (8 * log L) = L ^ 8 := by
    rw [show (8 : ℝ) * log L = ((8 : ℕ) : ℝ) * log L by norm_num, ← Real.log_pow,
      Real.exp_log (by positivity)]
  calc _ ≤ D ^ δ * exp (∑ p ∈ P, w p) := step1.trans step2
    _ ≤ D ^ δ * exp (8 * log L + 2.1072 + 8 * α * exp α) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) (by positivity)
    _ = D * L ^ 8 * exp (2.1072 + 8 * α * exp α - 18.4 * α) := by
        rw [hDδ, ← hL8]
        simp only [mul_assoc, ← Real.exp_add]
        congr 2; ring
    _ < D * L ^ 8 * 0.591 := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        rw [hα]; exact lemma2_3_const
    _ = 0.591 * D * L ^ 8 := by ring

end LeanLab.AlmostPrimes.DDLemma23
