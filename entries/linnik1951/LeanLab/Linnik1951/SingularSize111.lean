module

public import LeanLab.Perelli1996.Series320
public import LeanLab.Perelli1996.TotientRatio320
public import LeanLab.ChenExplicit.Decomp1552b
public import LeanLab.Akeno2026.Decomp86

/-!
P0093 page 168, after equation 10.6: the size of the truncated singular series.
Burst 8 p3, AI wrote the Lean code. Binary Goldbach is open.

The paper uses an absolute upper bound for the singular series at even N_1, which fails,
see the QUESTION in research/burst-20261112/Linnik1951-error_bound111-p3.md. Equation 10.7
only needs the truncated series to be small against ln N_1. This file proves that: for
every delta there is C with the truncated series at any level Q at most delta ln n plus C.
The route is elementary: the Mobius weighted Ramanujan coefficient bound of Perelli1996
Ramanujan400, the split q equal to gcd of q and n times the rest, the convergent sum of
1 over phi squared of Perelli1996 InverseTotient320, the bound of the sum of 1 over phi of
d for d at most M by 2 times 1 plus ln M of ChenExplicit Decomp1552b, and the divisor
bound of Akeno2026 Decomp86.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168, one term of 10.6 in its real cosine form is at most 1 over phi of q
times phi of q over gcd of q and n in size, from Perelli1996 Ramanujan400
norm_weighted_ramanujanSum_le. Proved. -/
theorem singular_term_le_m111 (q n : ℕ) (hq : 0 < q) :
    |((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          Real.cos (2 * Real.pi * (n : ℝ) * (a : ℝ) / (q : ℝ))| ≤
      1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient) := by
  have h := LeanLab.Perelli1996.Ramanujan400.norm_weighted_ramanujanSum_le q n hq
  have heq : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Real.cos (2 * Real.pi * (n : ℝ) * (a : ℝ) / (q : ℝ)) =
      (((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re := by
    unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    have hc : ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) =
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hc, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold LeanLab.Perelli1996.Kernel.e
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  rw [heq]
  exact (Complex.abs_re_le_norm _).trans h

/-- P0093 page 168, equation 10.4 style count: writing q as gcd of q and n times the rest,
the sum over q at most Q of the term bounds is at most the sum over divisors d of n of
1 over phi of d times twice the constant K of the sum of 1 over phi squared. Proved. -/
theorem singular_sum_le_divisors_m111 :
    ∃ K : ℝ, 0 < K ∧ ∀ Q n : ℕ, 1 ≤ n →
      ∑ q ∈ Icc 1 Q, 1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient) ≤
        (∑ d ∈ n.divisors, 1 / (d.totient : ℝ)) * (2 * K) := by
  obtain ⟨K, hK, htail⟩ := LeanLab.Perelli1996.InverseTotient320.inverse_totient_sq_tail
  refine ⟨K, hK, fun Q n hn => ?_⟩
  classical
  let F : ℕ × ℕ → ℝ := fun x => 1 / (x.1.totient : ℝ) * (1 / (x.2.totient : ℝ) ^ 2)
  let g : ℕ → ℕ × ℕ := fun q => (Nat.gcd q n, q / Nat.gcd q n)
  have hF0 : ∀ x, 0 ≤ F x := fun x => by dsimp [F]; positivity
  have hstep : ∀ q ∈ Icc 1 Q, 1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient) ≤ F (g q) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hgpos : 0 < Nat.gcd q n := Nat.gcd_pos_of_pos_left n (by omega)
    have hdvd : Nat.gcd q n ∣ q := Nat.gcd_dvd_left q n
    have hr : 0 < q / Nat.gcd q n := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hgpos
    have hmul : Nat.gcd q n * (q / Nat.gcd q n) = q := Nat.mul_div_cancel' hdvd
    have hsuper : (Nat.gcd q n).totient * (q / Nat.gcd q n).totient ≤ q.totient := by
      have := Nat.totient_super_multiplicative (Nat.gcd q n) (q / Nat.gcd q n)
      rwa [hmul] at this
    have hφg : (0 : ℝ) < (Nat.gcd q n).totient := by exact_mod_cast Nat.totient_pos.mpr hgpos
    have hφr : (0 : ℝ) < (q / Nat.gcd q n).totient := by exact_mod_cast Nat.totient_pos.mpr hr
    have hsuperR : ((Nat.gcd q n).totient : ℝ) * (q / Nat.gcd q n).totient ≤ q.totient := by
      exact_mod_cast hsuper
    dsimp [F, g]
    rw [one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
    calc ((Nat.gcd q n).totient : ℝ) * ((q / Nat.gcd q n).totient : ℝ) ^ 2
        = ((Nat.gcd q n).totient : ℝ) * (q / Nat.gcd q n).totient *
            (q / Nat.gcd q n).totient := by ring
      _ ≤ (q.totient : ℝ) * (q / Nat.gcd q n).totient :=
          mul_le_mul_of_nonneg_right hsuperR hφr.le
  have hinj : Set.InjOn g (Icc 1 Q : Set ℕ) := by
    intro a _ b _ hab
    have h1 : Nat.gcd a n = Nat.gcd b n := congrArg Prod.fst hab
    have h2 : a / Nat.gcd a n = b / Nat.gcd b n := congrArg Prod.snd hab
    rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left a n), ← Nat.mul_div_cancel' (Nat.gcd_dvd_left b n),
      h1, ← h1, h2, h1]
  have hsub : (Icc 1 Q).image g ⊆ n.divisors ×ˢ Icc 1 Q := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    have hgpos : 0 < Nat.gcd q n := Nat.gcd_pos_of_pos_left n (by omega)
    have hdvd : Nat.gcd q n ∣ q := Nat.gcd_dvd_left q n
    have hr : 0 < q / Nat.gcd q n := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hgpos
    refine Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q n, by omega⟩, ?_⟩
    exact Finset.mem_Icc.mpr ⟨hr, (Nat.div_le_self q _).trans hqQ⟩
  have hr2 : ∑ r ∈ Icc 1 Q, 1 / (r.totient : ℝ) ^ 2 ≤ 2 * K := by
    have := htail (1 / 2) (by norm_num) (Icc 1 Q)
      (fun r hr => ⟨(Finset.mem_Icc.mp hr).1, by
        have : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
        linarith⟩)
    calc _ ≤ K / (1 / 2) := this
      _ = 2 * K := by ring
  calc ∑ q ∈ Icc 1 Q, 1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient)
      ≤ ∑ q ∈ Icc 1 Q, F (g q) := Finset.sum_le_sum hstep
    _ = ∑ x ∈ (Icc 1 Q).image g, F x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ n.divisors ×ˢ Icc 1 Q, F x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hF0 x)
    _ = (∑ d ∈ n.divisors, 1 / (d.totient : ℝ)) * ∑ r ∈ Icc 1 Q, 1 / (r.totient : ℝ) ^ 2 := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ (∑ d ∈ n.divisors, 1 / (d.totient : ℝ)) * (2 * K) :=
        mul_le_mul_of_nonneg_left hr2 (Finset.sum_nonneg (fun d _ => by positivity))

/-- The sum of 1 over phi of d over the divisors d of n is at most delta ln n plus a
constant, for every delta: small divisors by the bound 2 times 1 plus ln M of the sum of
1 over phi up to M, at M equal to n to the delta over 2; large divisors by the divisor
bound and 1 over phi of d at most 2 times 1 plus ln d over d. Proved. -/
theorem divisor_inv_totient_small_m111 (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ d ∈ n.divisors, 1 / (d.totient : ℝ) ≤ δ * Real.log n + C := by
  set θ : ℝ := δ / 2 with hθ
  have hθp : 0 < θ := by positivity
  obtain ⟨Cτ, hCτ, hτ⟩ := LeanLab.Akeno2026.Decomp86.card_divisors_le_rpow (ε := θ / 2) (by positivity)
  refine ⟨2 + 2 * Cτ * (1 + 2 / θ), by positivity, fun n hn => ?_⟩
  classical
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
  set T : ℝ := (n : ℝ) ^ θ with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow hnR hθp.le
  have hTpos : 0 < T := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d : ℕ => (d : ℝ) ≤ T)]
  -- small divisors
  have hsmall : ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ T), 1 / (d.totient : ℝ) ≤
      2 * (1 + θ * Real.log n) := by
    have hM : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT1)
    have hsubs : n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ T) ⊆ Icc 1 ⌊T⌋₊ := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1.1 (by omega), Nat.le_floor hd.2⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsubs
      (fun d _ _ => by positivity : ∀ d ∈ Icc 1 ⌊T⌋₊, d ∉ n.divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ T) → 0 ≤ 1 / (d.totient : ℝ))
    have h2 := LeanLab.ChenExplicit.D1552.sum_inv_totient_le_two_log ⌊T⌋₊ hM
    have h3 : Real.log ⌊T⌋₊ ≤ θ * Real.log n := by
      have hfl : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hTpos.le
      have hfl1 : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hM
      calc Real.log ⌊T⌋₊ ≤ Real.log T := Real.log_le_log hfl1 hfl
        _ = θ * Real.log n := by rw [hT, Real.log_rpow hnpos]
    linarith
  -- large divisors
  have hlarge : ∑ d ∈ n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ T), 1 / (d.totient : ℝ) ≤
      2 * Cτ * (1 + 2 / θ) := by
    have hterm : ∀ d ∈ n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ T),
        1 / (d.totient : ℝ) ≤ 2 * (1 + Real.log n) / T := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (by omega)
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hdn : (d : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (by omega) hd.1.1
      have hTd : T < d := lt_of_not_ge hd.2
      have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hdpos
      have hratio := LeanLab.Perelli1996.TotientRatio320.ratio_le_log d hdpos
      have hlogd : Real.log d ≤ Real.log n := Real.log_le_log hdR hdn
      rw [div_le_iff₀ hφ] at hratio
      rw [div_le_div_iff₀ hφ hTpos]
      have hlog0 : 0 ≤ 1 + Real.log n := by linarith
      calc 1 * T ≤ d := by linarith
        _ ≤ 2 * (1 + Real.log d) * d.totient := hratio
        _ ≤ 2 * (1 + Real.log n) * d.totient := by
            apply mul_le_mul_of_nonneg_right _ hφ.le; linarith
    have hcard : ((n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ T)).card : ℝ) ≤ Cτ * (n : ℝ) ^ (θ / 2) :=
      le_trans (by exact_mod_cast Finset.card_filter_le _ _) (hτ n)
    have hlog : Real.log n ≤ (n : ℝ) ^ (θ / 2) / (θ / 2) :=
      Real.log_le_rpow_div hnpos.le (by positivity)
    have hsplit : (n : ℝ) ^ (θ / 2) * (n : ℝ) ^ (θ / 2) = T := by
      rw [← Real.rpow_add hnpos, hT]; ring_nf
    have hhalf : 1 ≤ (n : ℝ) ^ (θ / 2) := Real.one_le_rpow hnR (by positivity)
    calc ∑ d ∈ n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ T), 1 / (d.totient : ℝ)
        ≤ ((n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ T)).card : ℝ) * (2 * (1 + Real.log n) / T) := by
          have := Finset.sum_le_card_nsmul _ _ _ hterm
          rwa [nsmul_eq_mul] at this
      _ ≤ (Cτ * (n : ℝ) ^ (θ / 2)) * (2 * (1 + Real.log n) / T) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * Cτ * ((1 + Real.log n) / (n : ℝ) ^ (θ / 2)) := by
          rw [← hsplit]; field_simp
      _ ≤ 2 * Cτ * (1 + 2 / θ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by positivity)]
          have h2 : Real.log n ≤ 2 / θ * (n : ℝ) ^ (θ / 2) := by
            calc Real.log n ≤ (n : ℝ) ^ (θ / 2) / (θ / 2) := hlog
              _ = 2 / θ * (n : ℝ) ^ (θ / 2) := by field_simp
          nlinarith
  have hθδ : 2 * (θ * Real.log n) = δ * Real.log n := by rw [hθ]; ring
  linarith

/-- P0093 page 168: the truncated singular series of 10.6 in its real cosine form is at
most epsilon_0 ln n plus C_0 in size, for every epsilon_0, uniformly in the level Q.
Proved. -/
theorem truncSingular_size_m111 (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ Q n : ℕ, 1 ≤ n →
      |∑ q ∈ Finset.Icc 1 Q,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
            ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              Real.cos (2 * Real.pi * (n : ℝ) * (a : ℝ) / (q : ℝ))| ≤
        ε0 * Real.log n + C0 := by
  obtain ⟨K, hK, hdiv⟩ := singular_sum_le_divisors_m111
  obtain ⟨C, hC, hsmall⟩ := divisor_inv_totient_small_m111 (ε0 / (2 * K)) (by positivity)
  refine ⟨C * (2 * K), by positivity, fun Q n hn => ?_⟩
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  calc _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        |((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
            ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              Real.cos (2 * Real.pi * (n : ℝ) * (a : ℝ) / (q : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Icc 1 Q, 1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient) :=
        Finset.sum_le_sum (fun q hq => singular_term_le_m111 q n (Finset.mem_Icc.mp hq).1)
    _ ≤ (∑ d ∈ n.divisors, 1 / (d.totient : ℝ)) * (2 * K) := hdiv Q n hn
    _ ≤ (ε0 / (2 * K) * Real.log n + C) * (2 * K) :=
        mul_le_mul_of_nonneg_right (hsmall n hn) (by positivity)
    _ = ε0 * Real.log n + C * (2 * K) := by field_simp

end LeanLab.Linnik1951
