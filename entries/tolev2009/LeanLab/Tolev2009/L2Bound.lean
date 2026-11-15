module

public import LeanLab.Tolev2009.Displays19to20
public import LeanLab.Tolev2009.DivisorMoment
public import LeanLab.Tolev2009.Dyadic

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real MeasureTheory ComplexConjugate

namespace LeanLab.Tolev2009.L2Bound

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Displays19to20

/-- Parseval for a finite prime frequency polynomial, with real coefficients. -/
theorem finite_mass (a : ℝ) (s : Finset ℕ) (w : ℕ → ℝ) :
    (∫ α, ‖∑ p ∈ s, (w p : ℂ) * ee ((p : ℝ) * α)‖ ^ 2 ∂μI a) =
      ∑ p ∈ s, w p ^ 2 := by
  have he : ∀ α : ℝ, ((‖∑ p ∈ s, (w p : ℂ) * ee ((p : ℝ) * α)‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ s, ∑ q ∈ s, (w p : ℂ) * w q * ee ((((p : ℤ) - q : ℤ) : ℝ) * α) := by
    intro α
    rw [sq_norm_eq_mul_conj, map_sum, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    rw [map_mul, Complex.conj_ofReal, conj_ee]
    have ht : ee ((((p : ℤ) - q : ℤ) : ℝ) * α) = ee ((p : ℝ) * α) * ee (-((q : ℝ) * α)) := by
      rw [← ee_add]
      congr 1
      push_cast
      ring
    rw [ht]
    ring
  have hi : ∀ p q, Integrable (fun α => (w p : ℂ) * w q *
      ee ((((p : ℤ) - q : ℤ) : ℝ) * α)) (μI a) :=
    fun _ _ => ((MB.const _).mul (MB.ee (measurable_const.mul measurable_id))).integrable
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [he]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum s (fun q _ => hi p q))]
  simp_rw [integral_finsetSum _ (fun q _ => hi _ q), integral_const_mul, integral_ee_μI,
    mul_ite, mul_one, mul_zero, sub_eq_zero, Nat.cast_inj]
  push_cast
  refine sum_congr rfl fun p hp => ?_
  rw [sum_ite_eq s p]
  simp [hp, pow_two]

/-- The total coefficient attached to a prime before its logarithmic weight. -/
noncomputable def weight (lam : ℕ → ℝ) (l₃ K₃ p : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 K₃).filter (fun k => Nat.Coprime k l₃ ∧ p % k = l₃ % k), lam k

/-- Regroup Kfun by its prime frequency. -/
theorem Kfun_eq (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (α : ℝ) :
    Kfun lam l₃ K₃ N α = ∑ p ∈ primeSet 1 0 N,
      ((Real.log p * weight lam l₃ K₃ p : ℝ) : ℂ) * ee ((p : ℝ) * α) := by
  have hs : ∀ k, Sexp k l₃ N α = ∑ p ∈ primeSet 1 0 N,
      if p % k = l₃ % k then (Real.log p : ℂ) * ee (α * p) else 0 := by
    intro k
    rw [← sum_filter]
    exact congrArg (fun s : Finset ℕ => ∑ p ∈ s, (Real.log p : ℂ) * ee (α * p))
      (by ext p; simp [primeSet, and_assoc, Nat.mod_one])
  unfold Kfun
  simp_rw [hs, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  simp only [weight, sum_filter, Complex.ofReal_mul, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, mul_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  by_cases hm : p % k = l₃ % k
  · simp only [hm, and_true, ite_true, mul_comm ((p : ℝ)) α]
    split_ifs <;> ring
  · simp [hm]

/-- A bounded weight has at most K3 terms. -/
theorem weight_le (lam : ℕ → ℝ) (l₃ K₃ p : ℕ) (hlam : ∀ k, |lam k| ≤ 1) :
    |weight lam l₃ K₃ p| ≤ K₃ := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun k _ => hlam k).trans ?_
  simp only [sum_const, nsmul_eq_mul, mul_one]
  have h := card_le_card (filter_subset (fun k => Nat.Coprime k l₃ ∧ p % k = l₃ % k) (Icc 1 K₃))
  simpa using (show (((Icc 1 K₃).filter (fun k => Nat.Coprime k l₃ ∧ p % k = l₃ % k)).card : ℝ) ≤ K₃ by
    exact_mod_cast (by simpa using h : ((Icc 1 K₃).filter (fun k => Nat.Coprime k l₃ ∧ p % k = l₃ % k)).card ≤ K₃))

/-- Away from the single prime p equal to l3, divisors bound the coefficient. -/
theorem weight_le_divisors (lam : ℕ → ℝ) (l₃ K₃ p : ℕ) (hlam : ∀ k, |lam k| ≤ 1)
    (hp : p ≠ l₃) : |weight lam l₃ K₃ p| ≤ divisorCount ((p : ℤ) - l₃) := by
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ => hlam k).trans ?_)
  simp only [sum_const, nsmul_eq_mul, mul_one]
  apply Nat.cast_le.mpr
  apply card_le_card
  intro k hk
  rcases mem_filter.mp hk with ⟨hk, hc, hm⟩
  apply Nat.mem_divisors.mpr
  constructor
  · exact Int.natCast_dvd.mp (Nat.ModEq.dvd (show l₃ ≡ p [MOD k] from hm.symm))
  · apply Int.natAbs_ne_zero.mpr
    omega

/-- The single exceptional frequency p equal to l3 is separated before the divisor bound. -/
theorem coefficient_mass_le (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (hlam : ∀ k, |lam k| ≤ 1)
    (hl₃ : l₃ ≤ N) :
    (∑ p ∈ primeSet 1 0 N, (weight lam l₃ K₃ p) ^ 2) ≤
      (K₃ : ℝ) ^ 2 + 2 * ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2 := by
  let P := primeSet 1 0 N
  have hw : ∀ p, weight lam l₃ K₃ p ^ 2 ≤
      if p = l₃ then (K₃ : ℝ) ^ 2 else (divisorCount ((p : ℤ) - l₃) : ℝ) ^ 2 := by
    intro p
    split_ifs with h
    · have ht := pow_le_pow_left₀ (abs_nonneg _) (weight_le lam l₃ K₃ p hlam) 2
      simpa only [sq_abs] using ht
    · have ht := pow_le_pow_left₀ (abs_nonneg _) (weight_le_divisors lam l₃ K₃ p hlam h) 2
      simpa only [sq_abs] using ht
  refine (sum_le_sum fun p _ => hw p).trans ?_
  rw [sum_ite]
  have he : ∑ p ∈ P.filter (fun p => p = l₃), (K₃ : ℝ) ^ 2 ≤ (K₃ : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ p ∈ ({l₃} : Finset ℕ), (K₃ : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun p hp => mem_singleton.mpr (mem_filter.mp hp).2)
          (fun _ _ _ => by positivity)
      _ = _ := sum_singleton _ _
  refine add_le_add he ?_
  have hinj : Set.InjOn (fun p : ℕ => (p : ℤ) - l₃) ↑(P.filter (fun p => p ≠ l₃)) := by
    intro x _ y _ h
    dsimp only at h
    omega
  rw [← sum_image (f := fun n : ℤ => (divisorCount n : ℝ) ^ 2) hinj]
  have hsub : (P.filter (fun p => p ≠ l₃)).image (fun p : ℕ => (p : ℤ) - l₃) ⊆ nonzeroSet N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    rcases mem_filter.mp hp with ⟨hp, hne⟩
    have hpN : p ≤ N := by
      simp only [P, primeSet, mem_filter, mem_range] at hp
      omega
    simp only [nonzeroSet, mem_filter, mem_Icc]
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans_eq ?_
  exact DivisorMoment.signed_sum N (fun n => (n.divisors.card : ℝ) ^ 2)

/-- The L2 mass from prime orthogonality and the elementary second divisor moment. -/
theorem mass_le (a : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (hlam : ∀ k, |lam k| ≤ 1)
    (hl₃ : l₃ ≤ N) :
    (∫ α, ‖Kfun lam l₃ K₃ N α‖ ^ 2 ∂μI a) ≤
      Real.log N ^ 2 * ((K₃ : ℝ) ^ 2 + 2 * N * LeanLab.HeathBrown1985.Hn N ^ 3) := by
  have he : Kfun lam l₃ K₃ N = fun α => ∑ p ∈ primeSet 1 0 N,
      ((Real.log p * weight lam l₃ K₃ p : ℝ) : ℂ) * ee ((p : ℝ) * α) := by
    funext α
    exact Kfun_eq lam l₃ K₃ N α
  rw [he, finite_mass]
  calc
    _ ≤ ∑ p ∈ primeSet 1 0 N, Real.log N ^ 2 * weight lam l₃ K₃ p ^ 2 := by
      refine sum_le_sum fun p hp => ?_
      have hl := log_mem_primeSet hp
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl.1 hl.2 2) (sq_nonneg _)
    _ = Real.log N ^ 2 * ∑ p ∈ primeSet 1 0 N, weight lam l₃ K₃ p ^ 2 := by rw [mul_sum]
    _ ≤ Real.log N ^ 2 * ((K₃ : ℝ) ^ 2 + 2 * ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (coefficient_mass_le lam l₃ K₃ N hlam hl₃) (sq_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have h := LeanLab.HeathBrown1985.sum_sq_divisors_le N
      nlinarith

/-- The L2 half of display 12 is elementary, with an explicit absolute constant. -/
theorem display12_L2 (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (hlam : ∀ k, |lam k| ≤ 1)
    (hl₃ : l₃ ≤ N) (hK₃ : (K₃ : ℝ) ^ 2 ≤ N) (hL : 1 ≤ Real.log N) :
    (∫ α in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N α‖ ^ 2) ≤ 17 * N * Real.log N ^ (20 : ℕ) := by
  have hH : 0 ≤ LeanLab.HeathBrown1985.Hn N := LeanLab.HeathBrown1985.Hn_nonneg N
  have hHle : LeanLab.HeathBrown1985.Hn N ≤ 2 * Real.log N :=
    (LeanLab.HeathBrown1985.Hn_le N).trans (by linarith)
  have hL0 : 0 ≤ Real.log N := by linarith
  have hp : Real.log N ^ (3 : ℕ) ≥ 1 := one_le_pow₀ hL
  have h20 : Real.log N ^ (5 : ℕ) ≤ Real.log N ^ (20 : ℕ) :=
    pow_le_pow_right₀ hL (by norm_num)
  rw [← Kfun_mass_shift 0]
  calc
    _ ≤ Real.log N ^ 2 * ((K₃ : ℝ) ^ 2 + 2 * N * LeanLab.HeathBrown1985.Hn N ^ 3) :=
      mass_le 0 lam l₃ K₃ N hlam hl₃
    _ ≤ Real.log N ^ 2 * ((N : ℝ) + 2 * N * (2 * Real.log N) ^ 3) := by gcongr
    _ ≤ 17 * N * Real.log N ^ (5 : ℕ) := by
      have ht := mul_le_mul_of_nonneg_left hp
        (show 0 ≤ (N : ℝ) * Real.log N ^ 2 by positivity)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left h20 (by positivity)

/-- The third cutoff has square at most N in the paper's range. -/
theorem cutoff3_sq_le (B : ℝ) (N : ℕ) (hB : 0 ≤ B) (hL : 1 ≤ Real.log N) :
    (Dyadic.cutoff3 B N : ℝ) ^ 2 ≤ N := by
  have hN : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    norm_num [this] at hL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : (Dyadic.cutoff3 B N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B) :=
    Nat.floor_le (by positivity)
  have hb : Real.log N ^ (-B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hr : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  have hc : (Dyadic.cutoff3 B N : ℝ) ≤ Real.sqrt N :=
    hf.trans ((mul_le_of_le_one_right (by positivity) hb).trans hr)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (Dyadic.cutoff3 B N)) hc 2
  simpa only [Real.sq_sqrt (Nat.cast_nonneg N)] using hp

/-- The L2 half of display 12 for the exact paper cutoff, with constant 17. -/
theorem display12_L2_cutoff (lam : ℕ → ℝ) (l₃ N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hlam : ∀ k, |lam k| ≤ 1) (hl₃ : l₃ ≤ N) (hL : 1 ≤ Real.log N) :
    (∫ α in (0 : ℝ)..1, ‖Kfun lam l₃ (Dyadic.cutoff3 B N) N α‖ ^ 2) ≤
      17 * N * Real.log N ^ (20 : ℕ) :=
  display12_L2 lam l₃ _ N hlam hl₃ (cutoff3_sq_le B N hB hL) hL

end LeanLab.Tolev2009.L2Bound
