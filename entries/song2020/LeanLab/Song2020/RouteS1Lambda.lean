module

public import LeanLab.Song2020.RouteS1Weight
public import LeanLab.Song2020.RouteS1Abel

/-!
AI wrote the Lean code, 2026-11-15, toward the step s1_lambda_reduction.
Source: Yanbo Song, arXiv 2012.06322 v1, printed page 5, from "For S1, we first observe" to
"We have shown so far".
This file assembles the reduction of S1 to the von Mangoldt sums from the weight analysis of
RouteS1Weight and the generic partial summation and prime power steps of RouteS1Abel. The
statement of s1_lambda_reduction_route is the statement of
SPLIT_vaughan_per_u.s1_lambda_reduction, copied without change.
Binary Goldbach is open; nothing here changes that.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteS1Lambda

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Song 2020, page 5, one frequency h of the display for Delta psi prime: the sum over the
primes of the window of the weight times e(alpha p) times e(h(-(p+1)^gamma)) - e(h(-p^gamma))
is at most 50 |h| (1 + log n) times the bound for the von Mangoldt sums at the frequency -h,
plus the prime power error 4 pi |h| n^(1/2). The weight bounds come from RouteS1Weight and
the partial summation from RouteS1Abel. -/
private theorem per_frequency_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (α : ℝ) (h : ℤ) (Bh : ℝ)
    (hB : ∀ t : ℝ, ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + ((-h : ℤ) : ℝ) * (x : ℝ) ^ γ)‖ ≤ Bh) :
    ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
        (eC (h * (-((p : ℝ) + 1) ^ γ)) - eC (h * (-(p : ℝ) ^ γ)))‖ ≤
      |(h : ℝ)| * (50 * (1 + Real.log (n : ℝ)) * Bh +
        4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)) := by
  have hB0 : 0 ≤ Bh := (norm_nonneg _).trans (hB 0)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have habs : |(((-h : ℤ) : ℝ))| = |(h : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
  have hcongr : ∀ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
        (eC (h * (-((p : ℝ) + 1) ^ γ)) - eC (h * (-(p : ℝ) ^ γ))) =
      ((psWeight γ p : ℂ) *
          (eC (((-h : ℤ) : ℝ) * (((p : ℝ) + 1) ^ γ - (p : ℝ) ^ γ)) - 1)) *
        eC (α * p + ((-h : ℤ) : ℝ) * (p : ℝ) ^ γ) := by
    intro p _
    rw [← RouteS1Weight.term_identity γ α (((-h : ℤ) : ℝ)) p, Int.cast_neg, neg_neg]
  rw [Finset.sum_congr rfl hcongr]
  have hmain := RouteS1Abel.norm_sum_windowPrimes_le n hn y hy
    (fun x : ℕ => (psWeight γ x : ℂ) *
      (eC (((-h : ℤ) : ℝ) * (((x : ℝ) + 1) ^ γ - (x : ℝ) ^ γ)) - 1))
    (fun x : ℕ => eC (α * x + ((-h : ℤ) : ℝ) * (x : ℝ) ^ γ))
    Bh (10 * |(((-h : ℤ) : ℝ))|) (40 * |(((-h : ℤ) : ℝ))|) (2 * Real.pi * |(((-h : ℤ) : ℝ))|)
    (fun x => (RouteS1Weight.norm_eC _).le)
    hB
    (by positivity)
    (fun x => RouteS1Weight.norm_weight_le γ _ hγ0 hγ1 x)
    (fun x hx => RouteS1Weight.norm_weight_succ_sub_le γ _ hγ0 hγ1 x hx)
    (fun x => RouteS1Weight.norm_phi_le γ _ hγ0 hγ1 x)
  refine hmain.trans ?_
  rw [habs]
  have hh : 0 ≤ |(h : ℝ)| := abs_nonneg _
  have hprod : 0 ≤ |(h : ℝ)| * Bh := mul_nonneg hh hB0
  have hprod2 : 0 ≤ |(h : ℝ)| * Bh * Real.log (n : ℝ) := mul_nonneg hprod hlog
  nlinarith [hprod, hprod2]

/-- Song 2020, page 5, from "For S1, we first observe" to "We have shown so far": the route
proof of SPLIT_vaughan_per_u.s1_lambda_reduction, with the same statement. For each frequency
the weight is bounded by 2 pi |h| and has one step variation at most 40 |h| / x, partial
summation over the window costs 1 + log n, at most a constant times n^epsilon, the proper
prime powers cost a constant times |h| n^(1/2), and a_h at most K / |h| removes the factor
|h| before the sum over h. -/
theorem s1_lambda_reduction_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H → ∀ B : ℤ → ℝ,
              (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ B h) →
              ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
      (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * (-(p : ℝ) ^ γ)))‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                  (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
  intro γ hγ hγ1 ε hε
  have hγ0 : 0 < γ := by linarith
  refine ⟨50 * (1 + 1 / ε) + 48, by positivity, 1, ?_⟩
  intro K hK a ha n hn y _ hy α H hH B hB
  have hK0 : 0 ≤ K := by linarith
  have hnε : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hnhalf : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hnslack : 0 ≤ (n : ℝ) ^ (3 / 2 - γ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hlogle := RouteS1Weight.one_add_log_le_rpow ε hε n hn
  have hlog0 : 0 ≤ 1 + Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
    linarith
  -- nonnegativity of B on the frequencies in play
  have hBnn : ∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → 0 ≤ B h := fun h h0 hh =>
    (norm_nonneg _).trans (hB h h0 hh 0)
  -- interchange the p and h sums
  have hswap : ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
      (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
          a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
          a H h * eC (h * (-(p : ℝ) ^ γ))) =
      ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h *
        ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
          (eC (h * (-((p : ℝ) + 1) ^ γ)) - eC (h * (-(p : ℝ) ^ γ))) := by
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun p _ => ?_))
    ring
  rw [hswap]
  -- each frequency
  have hterm : ∀ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
      ‖a H h * ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
          (eC (h * (-((p : ℝ) + 1) ^ γ)) - eC (h * (-(p : ℝ) ^ γ)))‖ ≤
        K * (50 * (1 + 1 / ε) * (n : ℝ) ^ ε * B (-h) +
          4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)) := by
    intro h hh
    rw [Finset.mem_filter, Finset.mem_Icc] at hh
    have hne : h ≠ 0 := hh.2
    have hneg0 : -h ≠ 0 := neg_ne_zero.mpr hne
    have hnegle : |(-h)| ≤ (H : ℤ) := by
      rw [abs_neg]
      exact abs_le.mpr hh.1
    have habspos : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hne)
    have hBn : 0 ≤ B (-h) := hBnn (-h) hneg0 hnegle
    have hper := per_frequency_bound γ hγ0 hγ1 n hn y hy α h (B (-h))
      (fun t => hB (-h) hneg0 hnegle t)
    rw [norm_mul]
    have h1 : 50 * (1 + Real.log (n : ℝ)) * B (-h) ≤
        50 * (1 + 1 / ε) * (n : ℝ) ^ ε * B (-h) := by
      have := mul_le_mul_of_nonneg_right hlogle hBn
      nlinarith [this]
    have hbr : 0 ≤ 50 * (1 + Real.log (n : ℝ)) * B (-h) +
        4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have := Real.pi_pos
      positivity
    calc ‖a H h‖ * ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
          (eC (h * (-((p : ℝ) + 1) ^ γ)) - eC (h * (-(p : ℝ) ^ γ)))‖
        ≤ (K / |(h : ℝ)|) * (|(h : ℝ)| * (50 * (1 + Real.log (n : ℝ)) * B (-h) +
            4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2))) :=
          mul_le_mul (ha H h hne) hper (norm_nonneg _) (div_nonneg hK0 habspos.le)
      _ = K * (50 * (1 + Real.log (n : ℝ)) * B (-h) +
            4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)) := by
          field_simp
      _ ≤ K * (50 * (1 + 1 / ε) * (n : ℝ) ^ ε * B (-h) +
            4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  -- sum over the frequencies
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    RouteS1Abel.sum_nonzero_Icc_eq H (fun h => B (-h)), Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) ≤
      2 * (H : ℝ) + 1 := by
    have hle : ((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card ≤
        (Finset.Icc (-(H : ℤ)) H).card := Finset.card_filter_le _ _
    have hcard2 : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
      rw [Int.card_Icc]
      omega
    rw [hcard2] at hle
    exact_mod_cast hle
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hsumeq : ∑ k ∈ Finset.Icc 1 H, (B (-(k : ℤ)) + B (- -(k : ℤ))) =
      ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) :=
    Finset.sum_congr rfl (fun k _ => by rw [neg_neg, add_comm])
  rw [hsumeq]
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) := by
    refine Finset.sum_nonneg (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    have hk0 : (k : ℤ) ≠ 0 := by
      have : 1 ≤ k := hk.1
      exact_mod_cast (by omega : k ≠ 0)
    have hkH : |(k : ℤ)| ≤ (H : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hk.2
    have hkH' : |(-(k : ℤ))| ≤ (H : ℤ) := by rw [abs_neg]; exact hkH
    exact add_nonneg (hBnn _ hk0 hkH) (hBnn _ (neg_ne_zero.mpr hk0) hkH')
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hε' : 0 ≤ 1 / ε := by positivity
  -- the prime power part
  have hpp : (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) *
      (4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)) ≤ 48 * ((H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2)) := by
    have h3 : (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) ≤
        3 * (H : ℝ) := by linarith
    have h4 : 4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ 16 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      nlinarith
    calc _ ≤ 3 * (H : ℝ) * (16 * (n : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = 48 * ((H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
  have hT : 0 ≤ (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) :=
    mul_nonneg hnε hsum0
  have hU : 0 ≤ (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := mul_nonneg (by positivity) hnhalf
  have hc : 0 ≤ 50 * (1 + 1 / ε) := by positivity
  have hinner : 50 * (1 + 1 / ε) * (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) +
      (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) *
        (4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)) ≤
      (50 * (1 + 1 / ε) + 48) * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
        (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
    nlinarith [mul_nonneg hc hnslack, mul_nonneg hc hU, hT, hnslack, hpp]
  calc K * (50 * (1 + 1 / ε) * (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) +
        (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) *
          (4 * Real.pi * (n : ℝ) ^ ((1 : ℝ) / 2)))
      ≤ K * ((50 * (1 + 1 / ε) + 48) * ((n : ℝ) ^ (3 / 2 - γ) +
          (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
          (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))))) :=
        mul_le_mul_of_nonneg_left hinner hK0
    _ = _ := by ring

end

end LeanLab.Song2020.RouteS1Lambda
