module

public import LeanLab.Tolev2009.ScalarEnvelope346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 page 9, O1.
The scalar rectangular mean is proved. The exact assemblies are derived from it.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp346a
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp314a LeanLab.Tolev2009.Progression346
open LeanLab.Tolev2009.ScalarEnvelope346

section LinearScalarMean

open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Discrepancy346 LeanLab.HeathBrown1985

/-! ### Elementary one-dimensional sums -/

/-- `1 + log K` is nonnegative, including `K = 0`. -/
private theorem one_add_log_nat_nonneg (K : ℕ) : (0 : ℝ) ≤ 1 + Real.log K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · simp [h]
  · have : (0 : ℝ) ≤ Real.log K := Real.log_natCast_nonneg K
    linarith

/-- Harmonic sums against `log`. -/
private theorem sum_Icc_inv_le (K : ℕ) :
    (∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹) ≤ 1 + Real.log K := by
  have h : (harmonic K : ℝ) ≤ 1 + Real.log K := by
    have := harmonic_le_one_add_log K
    exact_mod_cast this
  calc (∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹) = (harmonic K : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ _ := h

/-- The divisor count is at most `k / φ k`. -/
private theorem card_divisors_mul_totient (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ (k.totient : ℝ) * (k.divisors.card : ℝ) := by
  have hsum : (∑ d ∈ k.divisors, (d.totient : ℝ)) = (k : ℝ) := by
    have := Nat.sum_totient k
    exact_mod_cast this
  have hle : (∑ d ∈ k.divisors, (d.totient : ℝ)) ≤
      ∑ _d ∈ k.divisors, (k.totient : ℝ) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hdvd : d ∣ k := (Nat.mem_divisors.mp hd).1
    have hpos : 0 < k.totient := Nat.totient_pos.mpr hk
    have hdvd' : d.totient ∣ k.totient := Nat.totient_dvd_of_dvd hdvd
    have : d.totient ≤ k.totient := Nat.le_of_dvd hpos hdvd'
    exact_mod_cast this
  rw [hsum] at hle
  have hcardsum : (∑ _d ∈ k.divisors, (k.totient : ℝ)) =
      (k.totient : ℝ) * (k.divisors.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hcardsum] at hle
  exact hle

/-- `1/φ k ≤ τ k / k`. -/
private theorem inv_totient_le (k : ℕ) (hk : 1 ≤ k) :
    ((k.totient : ℝ))⁻¹ ≤ (k.divisors.card : ℝ) / (k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ht0 : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  rw [show ((k.totient : ℝ))⁻¹ = 1 / (k.totient : ℝ) by rw [one_div],
    div_le_div_iff₀ ht0 hk0, one_mul, mul_comm]
  exact card_divisors_mul_totient k hk

/-- A filtered reciprocal sum over a divisibility condition. -/
private theorem sum_filter_dvd_inv (m K : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ (Icc 1 K).filter (fun k => m ∣ k), ((k : ℝ))⁻¹) =
      ∑ j ∈ Icc 1 (K / m), ((m * j : ℕ) : ℝ)⁻¹ := by
  have hm0 : 0 < m := by omega
  have hset : (Icc 1 K).filter (fun k => m ∣ k) = (Icc 1 (K / m)).image (fun j => m * j) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkI, hdvd⟩ := Finset.mem_filter.mp hk
      obtain ⟨j, rfl⟩ := hdvd
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hkI
        · exact h
      refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj1, ?_⟩, rfl⟩
      exact (Nat.le_div_iff_mul_le hm0).mpr (by rw [Nat.mul_comm]; exact (Finset.mem_Icc.mp hkI).2)
    · intro hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hmj : 1 ≤ m * j := by simpa using Nat.mul_le_mul hm hj1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmj, ?_⟩, ⟨j, rfl⟩⟩
      calc m * j ≤ m * (K / m) := Nat.mul_le_mul_left m (Finset.mem_Icc.mp hj).2
        _ ≤ K := Nat.mul_div_le K m
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel hm0 hab

/-- `Σ_{k ≤ K} τ k / k ≪ log² K`. -/
private theorem sum_card_divisors_div_le (K : ℕ) :
    (∑ k ∈ Icc 1 K, (k.divisors.card : ℝ) / (k : ℝ)) ≤ (1 + Real.log K) ^ 2 := by
  have hpoint : ∀ k ∈ Icc 1 K, (k.divisors.card : ℝ) / (k : ℝ) =
      ∑ d ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have kK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hkk : k ≠ 0 := by omega
    have hdiv : (Icc 1 K).filter (fun d => d ∣ k) = k.divisors := by
      ext d
      constructor
      · intro hd
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hkk⟩
      · intro hd
        have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
        have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdk (by omega)
        have hdk' : d ≤ k := Nat.le_of_dvd (by omega) hdk
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, by omega⟩, hdk⟩
    have hfil : (∑ d ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0) =
        ∑ d ∈ (Icc 1 K).filter (fun d => d ∣ k), ((k : ℝ))⁻¹ := (Finset.sum_filter _ _).symm
    rw [hfil, hdiv, div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
  calc (∑ k ∈ Icc 1 K, (k.divisors.card : ℝ) / (k : ℝ))
      = ∑ k ∈ Icc 1 K, ∑ d ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0 :=
        Finset.sum_congr rfl hpoint
    _ = ∑ d ∈ Icc 1 K, ∑ k ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0 := Finset.sum_comm
    _ ≤ ∑ d ∈ Icc 1 K, ((d : ℝ))⁻¹ * (1 + Real.log K) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        rw [← Finset.sum_filter]
        calc (∑ k ∈ (Icc 1 K).filter (fun k => d ∣ k), ((k : ℝ))⁻¹)
            = ∑ j ∈ Icc 1 (K / d), ((d * j : ℕ) : ℝ)⁻¹ := sum_filter_dvd_inv d K hd1
          _ = ((d : ℝ))⁻¹ * ∑ j ∈ Icc 1 (K / d), ((j : ℝ))⁻¹ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Nat.cast_mul, mul_inv]
          _ ≤ ((d : ℝ))⁻¹ * (1 + Real.log K) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rcases Nat.eq_zero_or_pos (K / d) with h0 | hpos
              · rw [h0]
                simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), Finset.sum_empty]
                exact one_add_log_nat_nonneg K
              · have hle : ((K / d : ℕ) : ℝ) ≤ (K : ℝ) := by
                  exact_mod_cast Nat.div_le_self K d
                have hlog : Real.log ((K / d : ℕ) : ℝ) ≤ Real.log K :=
                  Real.log_le_log (by exact_mod_cast hpos) hle
                linarith [sum_Icc_inv_le (K / d)]
    _ = (∑ d ∈ Icc 1 K, ((d : ℝ))⁻¹) * (1 + Real.log K) := by rw [Finset.sum_mul]
    _ ≤ (1 + Real.log K) * (1 + Real.log K) := by
        refine mul_le_mul_of_nonneg_right (sum_Icc_inv_le K) ?_
        linarith [one_add_log_nat_nonneg K]
    _ = (1 + Real.log K) ^ 2 := by ring

/-- `Σ_{k ≤ K} 1/φ(k) ≪ log² K`. -/
private theorem sum_inv_totient_le (K : ℕ) :
    (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ (1 + Real.log K) ^ 2 := by
  refine (Finset.sum_le_sum (fun k hk => inv_totient_le k (Finset.mem_Icc.mp hk).1)).trans
    (sum_card_divisors_div_le K)

/-! ### lcm fibres and the linear discrepancy average -/

/-- A fixed-`q` lcm fibre injects into the divisors of `q` through `gcd`. -/
private theorem lcm_fiber_card_le_divisors (K q h : ℕ) (hq : 1 ≤ q) :
    ((Icc 1 K).filter (fun k => Nat.lcm k q = h)).card ≤ q.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun k => Nat.gcd k q)
  · intro k _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right k q, by omega⟩
  · intro k hk k' hk' he
    change Nat.gcd k q = Nat.gcd k' q at he
    have hk0 := (mem_filter.mp hk).2
    have hk1 := (mem_filter.mp hk').2
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < q)
    calc k * q = Nat.gcd k q * Nat.lcm k q := (Nat.gcd_mul_lcm k q).symm
      _ = Nat.gcd k' q * Nat.lcm k' q := by rw [hk0, hk1, he]
      _ = k' * q := Nat.gcd_mul_lcm k' q

/-- One progression range against the divisor multiplicity of `q`. -/
private theorem sum_lcm_le (K q M : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hM : ∀ k ∈ Icc 1 K, Nat.lcm k q ≤ M) :
    (∑ k ∈ Icc 1 K, f (Nat.lcm k q)) ≤ (q.divisors.card : ℝ) * ∑ h ∈ Icc 1 M, f h := by
  have hmap : ∀ k ∈ Icc 1 K, Nat.lcm k q ∈ Icc 1 M := fun k hk =>
    mem_Icc.mpr ⟨Nat.lcm_pos (mem_Icc.mp hk).1 hq, hM k hk⟩
  rw [← sum_fiberwise_of_maps_to hmap (fun k => f (Nat.lcm k q))]
  calc ∑ h ∈ Icc 1 M, ∑ k ∈ (Icc 1 K).filter (fun k => Nat.lcm k q = h), f (Nat.lcm k q)
      = ∑ h ∈ Icc 1 M, (((Icc 1 K).filter (fun k => Nat.lcm k q = h)).card : ℝ) * f h := by
        refine sum_congr rfl (fun h _ => ?_)
        rw [show (∑ k ∈ (Icc 1 K).filter (fun k => Nat.lcm k q = h), f (Nat.lcm k q))
            = ∑ _k ∈ (Icc 1 K).filter (fun k => Nat.lcm k q = h), f h from
            sum_congr rfl (fun k hk => by rw [(mem_filter.mp hk).2]),
          sum_const, nsmul_eq_mul]
    _ ≤ ∑ h ∈ Icc 1 M, (q.divisors.card : ℝ) * f h := by
        refine sum_le_sum (fun h _ => ?_)
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast lcm_fiber_card_le_divisors K q h hq) (hf h)
    _ = _ := by rw [← Finset.mul_sum]

/-- The positive reciprocal lcm average against an ordinary discrepancy sum. -/
private theorem weighted_lcm_le (K R M : ℕ) (f : ℕ → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hM : ∀ q ∈ Icc 1 R, ∀ k ∈ Icc 1 K, Nat.lcm k q ≤ M) :
    (∑ q ∈ Icc 1 R, ∑ k ∈ Icc 1 K, f (Nat.lcm k q) / q) ≤
      (1 + Real.log R) ^ 2 * ∑ h ∈ Icc 1 M, f h := by
  have hF : 0 ≤ ∑ h ∈ Icc 1 M, f h := sum_nonneg (fun h _ => hf h)
  calc (∑ q ∈ Icc 1 R, ∑ k ∈ Icc 1 K, f (Nat.lcm k q) / q)
      = ∑ q ∈ Icc 1 R, (∑ k ∈ Icc 1 K, f (Nat.lcm k q)) / q := by
        refine sum_congr rfl (fun q _ => ?_)
        rw [Finset.sum_div]
    _ ≤ ∑ q ∈ Icc 1 R, (q.divisors.card : ℝ) * (∑ h ∈ Icc 1 M, f h) / q := by
        refine sum_le_sum (fun q hq => ?_)
        exact div_le_div_of_nonneg_right
          (sum_lcm_le K q M (mem_Icc.mp hq).1 f hf (hM q hq)) (by positivity)
    _ = (∑ q ∈ Icc 1 R, (q.divisors.card : ℝ) / q) * (∑ h ∈ Icc 1 M, f h) := by
        rw [Finset.sum_mul]
        refine sum_congr rfl (fun q _ => ?_)
        ring
    _ ≤ (1 + Real.log R) ^ 2 * ∑ h ∈ Icc 1 M, f h :=
        mul_le_mul_of_nonneg_right (sum_card_divisors_div_le R) hF

/-- The linear theta range written with a positive exponent is the same floor. -/
private theorem theta_range_eq (A : ℝ) (N : ℕ) :
    ⌊Real.sqrt N / Real.log N ^ (4 * (2000 * A) + 15)⌋₊ =
      ⌊Real.sqrt N * Real.log N ^ (-(4 * (2000 * A) + 15))⌋₊ := by
  rw [div_eq_mul_inv, ← Real.rpow_neg (Real.log_natCast_nonneg N)]

/-- Every `lcm k q` in the frozen ranges lies in the linear theta range `D = 2000 A`. -/
private theorem lcm_le_theta_range (A : ℝ) (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N)
    {K R : ℕ} (hK : K ≤ cutoff (10 ^ 4 * A) N) (hR : R ≤ ⌊Qof A N⌋₊)
    {q k : ℕ} (hq : q ∈ Icc 1 R) (hk : k ∈ Icc 1 K) :
    Nat.lcm k q ≤ ⌊Real.sqrt N / Real.log N ^ (4 * (2000 * A) + 15)⌋₊ := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < Real.log N := by linarith
  have hKle : (k : ℝ) ≤ Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)) := by
    have h1 : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast (mem_Icc.mp hk).2
    have h2 : (K : ℝ) ≤ ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) := by exact_mod_cast hK
    have h3 : ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) ≤
        Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)) := by
      rw [cutoff]
      exact Nat.floor_le (mul_nonneg (Real.sqrt_nonneg N)
        (Real.rpow_nonneg (le_of_lt hL0) _))
    linarith
  have hRle : (q : ℝ) ≤ Real.log N ^ (20 * A) := by
    have h1 : (q : ℝ) ≤ (R : ℝ) := by exact_mod_cast (mem_Icc.mp hq).2
    have h2 : (R : ℝ) ≤ ((⌊Qof A N⌋₊ : ℕ) : ℝ) := by exact_mod_cast hR
    have h3 : ((⌊Qof A N⌋₊ : ℕ) : ℝ) ≤ Qof A N :=
      Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hL0 (20 * A)))
    have h4 : Qof A N = Real.log N ^ (20 * A) := rfl
    linarith
  have hpk : ((q : ℝ) * (k : ℝ)) ≤ Real.sqrt N * Real.log N ^ (-(9980 * A)) := by
    have h1 : (q : ℝ) * (k : ℝ) ≤
        Real.log N ^ (20 * A) * (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) :=
      mul_le_mul hRle hKle (by positivity) (by positivity)
    have h2 : Real.log N ^ (20 * A) * (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)))
        = Real.sqrt N * Real.log N ^ (-(9980 * A)) := by
      rw [show Real.log N ^ (20 * A) * (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)))
          = Real.sqrt N * (Real.log N ^ (20 * A) * Real.log N ^ (-(10 ^ 4 * A))) by ring,
        ← Real.rpow_add hL0]
      congr 2
      ring
    linarith [h1, h2]
  have hexp : Real.log N ^ (-(9980 * A)) ≤ Real.log N ^ (-(8000 * A + 15)) := by
    refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
    nlinarith [hA]
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  have hq0 : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
  have hlcm : (Nat.lcm k q : ℝ) ≤ Real.sqrt N * Real.log N ^ (-(8000 * A + 15)) := by
    have h1 : Nat.lcm k q ≤ k * q := Nat.lcm_le_mul hk0 hq0
    have h2 : ((Nat.lcm k q : ℕ) : ℝ) ≤ ((k * q : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((k * q : ℕ) : ℝ) = (k : ℝ) * (q : ℝ) := by push_cast; ring
    rw [h3] at h2
    calc (Nat.lcm k q : ℝ) ≤ (k : ℝ) * (q : ℝ) := h2
      _ = (q : ℝ) * (k : ℝ) := by ring
      _ ≤ Real.sqrt N * Real.log N ^ (-(9980 * A)) := hpk
      _ ≤ Real.sqrt N * Real.log N ^ (-(8000 * A + 15)) :=
          mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg N)
  refine Nat.le_floor ?_
  rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hL0)]
  have hpow : 4 * (2000 * A) + 15 = 8000 * A + 15 := by ring
  rw [hpow]
  exact hlcm

/-- The linear discrepancy average with the sharp `2000 A` saving. -/
private theorem theta_linear_le (A : ℝ) (hA : 10 ^ 4 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N → ∀ K R : ℕ, K ≤ cutoff (10 ^ 4 * A) N →
      R ≤ ⌊Qof A N⌋₊ →
      (∑ q ∈ Icc 1 R, ∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q) / q) ≤
        C * (1 + Real.log R) ^ 2 * (N : ℝ) * Real.log N ^ (-(2000 * A)) := by
  obtain ⟨Cθ, hCθ⟩ := thetaError_mean (2000 * A) (by positivity)
  refine ⟨max Cθ 0, le_max_right _ _, fun N hN K R hK hR => ?_⟩
  have hL1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < Real.log N := by linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hmean : (∑ h ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-(4 * (2000 * A) + 15))⌋₊,
      thetaError N h) ≤ Cθ * (N : ℝ) * Real.log N ^ (-(2000 * A)) := by
    have h := hCθ N (by omega)
    rw [theta_range_eq] at h
    rwa [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hL0)] at h
  have hstep : (∑ q ∈ Icc 1 R, ∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q) / q)
      ≤ (1 + Real.log R) ^ 2 *
          ∑ h ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-(4 * (2000 * A) + 15))⌋₊,
            thetaError N h := by
    refine weighted_lcm_le K R _ (thetaError N) (thetaError_nonneg N) (fun q hq k hk => ?_)
    rw [← theta_range_eq]
    exact lcm_le_theta_range A hA hN hK hR hq hk
  refine hstep.trans ?_
  have hR2 : (0 : ℝ) ≤ (1 + Real.log R) ^ 2 := sq_nonneg _
  have hLn : (0 : ℝ) ≤ Real.log N ^ (-(2000 * A)) := Real.rpow_nonneg (le_of_lt hL0) _
  calc (1 + Real.log R) ^ 2 * (∑ h ∈ Icc 1
        ⌊Real.sqrt N * Real.log N ^ (-(4 * (2000 * A) + 15))⌋₊, thetaError N h)
      ≤ (1 + Real.log R) ^ 2 * (Cθ * (N : ℝ) * Real.log N ^ (-(2000 * A))) :=
        mul_le_mul_of_nonneg_left hmean hR2
    _ = ((1 + Real.log R) ^ 2 * (N : ℝ) * Real.log N ^ (-(2000 * A))) * Cθ := by ring
    _ ≤ ((1 + Real.log R) ^ 2 * (N : ℝ) * Real.log N ^ (-(2000 * A))) * max Cθ 0 :=
        mul_le_mul_of_nonneg_left (le_max_left Cθ 0)
          (mul_nonneg (mul_nonneg hR2 hNnn) hLn)
    _ = max Cθ 0 * (1 + Real.log R) ^ 2 * (N : ℝ) * Real.log N ^ (-(2000 * A)) := by ring

/-! ### The degree-one factorization of `scalarMean 1` -/

/-- A product of three one-dimensional sums. -/
private theorem triple_factor {I1 I2 I3 : Finset ℕ} (f1 f2 f3 : ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f1 k1 * f2 k2 * f3 k3)
      = (∑ k1 ∈ I1, f1 k1) * (∑ k2 ∈ I2, f2 k2) * (∑ k3 ∈ I3, f3 k3) := by
  have h1 : (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f1 k1 * f2 k2 * f3 k3)
      = ∑ k1 ∈ I1, ∑ k2 ∈ I2, (f1 k1 * f2 k2) * (∑ k3 ∈ I3, f3 k3) := by
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => ?_))
    rw [Finset.mul_sum]
  have h2 : (∑ k1 ∈ I1, ∑ k2 ∈ I2, (f1 k1 * f2 k2) * (∑ k3 ∈ I3, f3 k3))
      = (∑ k1 ∈ I1, ∑ k2 ∈ I2, f1 k1 * f2 k2) * (∑ k3 ∈ I3, f3 k3) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k1 _ => ?_)
    rw [Finset.sum_mul]
  have h3 : (∑ k1 ∈ I1, ∑ k2 ∈ I2, f1 k1 * f2 k2)
      = (∑ k1 ∈ I1, f1 k1) * (∑ k2 ∈ I2, f2 k2) :=
    (Finset.sum_mul_sum _ _ _ _).symm
  rw [h1, h2, h3]

/-- Splitting a three-term summand at three sum levels. -/
private theorem sum3_add {I : Finset ℕ} (f g h : ℕ → ℝ) :
    (∑ x ∈ I, (f x + g x + h x)) = ∑ x ∈ I, f x + ∑ x ∈ I, g x + ∑ x ∈ I, h x := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The degree-one positive polynomial as a sum of three products of sums. -/
private theorem triple_q_one {I1 I2 I3 : Finset ℕ} (d1 b2 : ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3,
        (d1 k1 * b2 k2 * b2 k3 + b2 k1 * d1 k2 * b2 k3 + b2 k1 * b2 k2 * d1 k3))
      = (∑ k1 ∈ I1, d1 k1) * (∑ k2 ∈ I2, b2 k2) * (∑ k3 ∈ I3, b2 k3)
        + (∑ k1 ∈ I1, b2 k1) * (∑ k2 ∈ I2, d1 k2) * (∑ k3 ∈ I3, b2 k3)
        + (∑ k1 ∈ I1, b2 k1) * (∑ k2 ∈ I2, b2 k2) * (∑ k3 ∈ I3, d1 k3) := by
  simp only [sum3_add]
  rw [triple_factor, triple_factor, triple_factor]

/-- A constant pulls out of three `k`-sums. -/
private theorem sum_const_mul_three {I1 I2 I3 : Finset ℕ} (c : ℝ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, c * f k1 k2 k3)
      = c * ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [Finset.mul_sum]

/-- The `q`-sum moves outside three `k`-sums. -/
private theorem swap_four {I1 I2 I3 Iq : Finset ℕ} (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, ∑ q ∈ Iq, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := by
  have h3 : ∀ k1 k2, (∑ k3 ∈ I3, ∑ q ∈ Iq, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k3 ∈ I3, f k1 k2 k3 q := fun _ _ => Finset.sum_comm
  have h2 : ∀ k1, (∑ k2 ∈ I2, ∑ q ∈ Iq, ∑ k3 ∈ I3, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := fun _ => Finset.sum_comm
  have h1 : (∑ k1 ∈ I1, ∑ q ∈ Iq, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := Finset.sum_comm
  calc (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, ∑ q ∈ Iq, f k1 k2 k3 q)
      = ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ q ∈ Iq, ∑ k3 ∈ I3, f k1 k2 k3 q := by simp only [h3]
    _ = ∑ k1 ∈ I1, ∑ q ∈ Iq, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := by simp only [h2]
    _ = _ := h1

/-- `scalarArc 1` at a tripled index is the explicit three-term product. -/
private theorem scalarArc_one (Q : ℝ) (N q k1 k2 k3 : ℕ) :
    scalarArc 1 Q N q ![k1, k2, k3] =
      (2 * Q / (N : ℝ)) *
        (errorProfile Q N q k1 * mainProfile N q k2 * mainProfile N q k3 +
         mainProfile N q k1 * errorProfile Q N q k2 * mainProfile N q k3 +
         mainProfile N q k1 * mainProfile N q k2 * errorProfile Q N q k3) := by
  unfold scalarArc positivePart
  simp

/-- The degree-one rectangular sum, factorized into `q`-indexed products of
one-dimensional sums of the error and main profiles. -/
private theorem scalarMean_one_eq (A : ℝ) (N : ℕ) :
    scalarMean 1 A N =
      (2 * Qof A N / (N : ℝ)) * ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
        (((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k)
            * (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), mainProfile N q k)
            * (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), mainProfile N q k))
          + ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), mainProfile N q k)
            * (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k)
            * (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), mainProfile N q k))
          + ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), mainProfile N q k)
            * (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), mainProfile N q k)
            * (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), errorProfile (Qof A N) N q k))) := by
  set I1 : Finset ℕ := Icc 1 (cutoff (10 ^ 4 * A) N) with hI1
  set I3 : Finset ℕ := Icc 1 (cutoff3 (10 ^ 4 * A) N) with hI3
  set Iq : Finset ℕ := Icc 1 ⌊Qof A N⌋₊ with hIq
  have hunfold : scalarMean 1 A N = ∑ k1 ∈ I1, ∑ k2 ∈ I1, ∑ k3 ∈ I3, ∑ q ∈ Iq,
      scalarArc 1 (Qof A N) N q ![k1, k2, k3] := by
    simp only [scalarMean, scalarEnvelope, hI1, hI3, hIq]
  rw [hunfold, swap_four]
  simp only [scalarArc_one]
  have hper : ∀ q ∈ Iq,
      (∑ k1 ∈ I1, ∑ k2 ∈ I1, ∑ k3 ∈ I3,
        (2 * Qof A N / (N : ℝ)) *
          (errorProfile (Qof A N) N q (k1) * mainProfile N q (k2) *
              mainProfile N q (k3) +
            mainProfile N q (k1) * errorProfile (Qof A N) N q (k2) *
              mainProfile N q (k3) +
            mainProfile N q (k1) * mainProfile N q (k2) *
              errorProfile (Qof A N) N q (k3)))
        = (2 * Qof A N / (N : ℝ)) *
          (((∑ k ∈ I1, errorProfile (Qof A N) N q k) * (∑ k ∈ I1, mainProfile N q k)
              * (∑ k ∈ I3, mainProfile N q k))
            + ((∑ k ∈ I1, mainProfile N q k) * (∑ k ∈ I1, errorProfile (Qof A N) N q k)
              * (∑ k ∈ I3, mainProfile N q k))
            + ((∑ k ∈ I1, mainProfile N q k) * (∑ k ∈ I1, mainProfile N q k)
              * (∑ k ∈ I3, errorProfile (Qof A N) N q k))) := by
    intro q _
    rw [sum_const_mul_three]
    congr 1
    exact triple_q_one (d1 := fun k => errorProfile (Qof A N) N q k)
      (b2 := fun k => mainProfile N q k)
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]

/-- The error profile sums to a theta sum plus `K` copies of the log profile. -/
private theorem error_sum_eq (Q : ℝ) (N q K : ℕ) :
    (∑ k ∈ Icc 1 K, errorProfile Q N q k) =
      (1 + 2 * π) * Q *
        ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) := by
  unfold errorProfile
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel]

/-- The main profile sums to `N q` times the reciprocal totient sum. -/
private theorem main_sum_eq (N q K : ℕ) :
    (∑ k ∈ Icc 1 K, mainProfile N q k)
      = (N : ℝ) * q * ∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹ := by
  unfold mainProfile
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [div_eq_mul_inv]

/-- The third cutoff is below the first. -/
private theorem cutoff3_le_cutoff (B : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    cutoff3 B N ≤ cutoff B N := by
  unfold cutoff3 cutoff
  apply Nat.floor_le_floor
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _)
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)


/-- `log N ≥ 1` at `N ≥ 3`. -/
private theorem one_le_log {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  linarith [Real.exp_one_lt_d9]

/-- Three positive terms with one factor over-estimated each stay below three copies
of the dominating product. -/
private theorem three_term_le {d1 b1 d3 b3 e0 m0 : ℝ} (hd1 : d1 = e0) (hb1 : b1 = m0)
    (hb3 : b3 ≤ m0) (hd3 : d3 ≤ e0) (he0 : 0 ≤ e0) (hm0 : 0 ≤ m0) :
    d1 * b1 * b3 + b1 * d1 * b3 + b1 * b1 * d3 ≤ 3 * e0 * m0 ^ 2 := by
  rw [hd1, hb1]
  have h1 : e0 * m0 * b3 ≤ e0 * m0 * m0 := mul_le_mul_of_nonneg_left hb3 (mul_nonneg he0 hm0)
  have h2 : m0 * m0 * d3 ≤ m0 * m0 * e0 := mul_le_mul_of_nonneg_left hd3 (mul_nonneg hm0 hm0)
  nlinarith [h1, h2]

/-- The degree-one rectangular bound in explicit scalar form. -/
private theorem scalarMean_one_bound (A : ℝ) (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N) :
    scalarMean 1 A N ≤
      6 * (1 + 2 * π) * (Qof A N) ^ 2 * (N : ℝ) *
        (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), ((k.totient : ℝ))⁻¹) ^ 2 *
        ((Qof A N) ^ 3 * (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
            ∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q) / q)
          + (cutoff (10 ^ 4 * A) N : ℝ) * (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
              (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q))) := by
  have hN1 : 1 ≤ N := by omega
  have hL1 : 1 ≤ Real.log N := one_le_log hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set Q : ℝ := Qof A N with hQ
  set K : ℕ := cutoff (10 ^ 4 * A) N with hK
  set K3 : ℕ := cutoff3 (10 ^ 4 * A) N with hK3
  set Iq : Finset ℕ := Icc 1 ⌊Q⌋₊ with hIq
  set S1 : ℝ := ∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹ with hS1
  set T1 : ℕ → ℝ := fun q => ∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q) with hT1
  set cq : ℕ → ℝ := fun q => (Real.log q / Real.log 2 * Real.log N) / q with hcq
  set D1 : ℕ → ℝ := fun q => ∑ k ∈ Icc 1 K, errorProfile Q N q k with hD1
  set B1 : ℕ → ℝ := fun q => ∑ k ∈ Icc 1 K, mainProfile N q k with hB1
  set D3 : ℕ → ℝ := fun q => ∑ k ∈ Icc 1 K3, errorProfile Q N q k with hD3
  set B3 : ℕ → ℝ := fun q => ∑ k ∈ Icc 1 K3, mainProfile N q k with hB3
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A)
  have hQ0 : 0 < Q := by linarith
  have hK3K : K3 ≤ K := by
    rw [hK3, hK]
    exact cutoff3_le_cutoff _ N hN1
  have herr_nn : ∀ q k, 0 ≤ errorProfile Q N q k := fun q k => errorProfile_nonneg Q N q k hQ0.le
  have hmain_nn : ∀ q k, 0 ≤ mainProfile N q k := fun q k => mainProfile_nonneg N q k
  have hmono : ∀ (F : ℕ → ℕ → ℝ), (∀ q k, 0 ≤ F q k) → ∀ q,
      (∑ k ∈ Icc 1 K3, F q k) ≤ (∑ k ∈ Icc 1 K, F q k) := by
    intro F hF q
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hK3K)
      (fun x _ _ => hF q x)
  -- the factorized scalar being bounded
  have hEq : scalarMean 1 A N = (2 * Q / (N : ℝ)) * ∑ q ∈ Iq,
      (D1 q * B1 q * B3 q + B1 q * D1 q * B3 q + B1 q * B1 q * D3 q) := by
    rw [scalarMean_one_eq]
  have hS1nn : 0 ≤ S1 := by
    rw [hS1]
    exact sum_nonneg (fun k _ => by positivity)
  -- the profile sums
  have hD1eq : ∀ q, D1 q = (1 + 2 * π) * Q * (T1 q + (K : ℝ) * cq q) := by
    intro q
    exact error_sum_eq Q N q K
  have hB1eq : ∀ q, B1 q = (N : ℝ) * q * S1 := by
    intro q
    exact main_sum_eq N q K
  have hB3le : ∀ q, B3 q ≤ (N : ℝ) * q * S1 := by
    intro q
    exact (hmono (fun q k => mainProfile N q k) hmain_nn q).trans_eq (main_sum_eq N q K)
  have hD3le : ∀ q, D3 q ≤ (1 + 2 * π) * Q * (T1 q + (K : ℝ) * cq q) := by
    intro q
    exact (hmono (fun q k => errorProfile Q N q k) herr_nn q).trans_eq (error_sum_eq Q N q K)
  -- the nonnegative factors
  have hEnn : ∀ q, 0 ≤ (1 + 2 * π) * Q * (T1 q + (K : ℝ) * cq q) := by
    intro q
    refine mul_nonneg (mul_nonneg (by positivity) hQ0.le) (add_nonneg ?_ ?_)
    · rw [hT1]
      exact sum_nonneg (fun k _ => thetaError_nonneg N _)
    · refine mul_nonneg (by positivity) ?_
      rw [hcq]
      exact div_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg _)
        (by nlinarith [Real.log_two_gt_d9])) (Real.log_natCast_nonneg _)) (by positivity)
  have hMnn : ∀ q : ℕ, 0 ≤ (N : ℝ) * q * S1 := by
    intro q
    have hq : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.zero_le q
    exact mul_nonneg (mul_nonneg hN0.le hq) hS1nn
  -- the pointwise three-term bound
  have hpt : ∀ q ∈ Iq,
      (D1 q * B1 q * B3 q + B1 q * D1 q * B3 q + B1 q * B1 q * D3 q)
        ≤ 3 * ((1 + 2 * π) * Q * (T1 q + (K : ℝ) * cq q)) * ((N : ℝ) * q * S1) ^ 2 := by
    intro q _
    exact three_term_le (hd1 := hD1eq q) (hb1 := hB1eq q) (hb3 := hB3le q) (hd3 := hD3le q)
      (hEnn q) (hMnn q)
  have hsum : (∑ q ∈ Iq, (D1 q * B1 q * B3 q + B1 q * D1 q * B3 q + B1 q * B1 q * D3 q))
      ≤ ∑ q ∈ Iq, 3 * ((1 + 2 * π) * Q * (T1 q + (K : ℝ) * cq q)) *
          ((N : ℝ) * q * S1) ^ 2 :=
    Finset.sum_le_sum hpt
  have hqQ : ∀ q ∈ Iq, (q : ℝ) ≤ Q := by
    intro q hq
    have h2 : (q : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hq).2
    exact h2.trans (Nat.floor_le hQ0.le)
  have hstep := hEq
  rw [hstep]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans ?_
  -- fold the double sum
  have hfold : (2 * Q / (N : ℝ)) * (∑ q ∈ Iq, 3 * ((1 + 2 * π) * Q *
        (T1 q + (K : ℝ) * cq q)) * ((N : ℝ) * q * S1) ^ 2)
      = 6 * (1 + 2 * π) * Q ^ 2 * (N : ℝ) * S1 ^ 2 *
          ∑ q ∈ Iq, (q : ℝ) ^ 2 * (T1 q + (K : ℝ) * cq q) := by
    rw [show (2 * Q / (N : ℝ)) * (∑ q ∈ Iq, 3 * ((1 + 2 * π) * Q *
        (T1 q + (K : ℝ) * cq q)) * ((N : ℝ) * q * S1) ^ 2)
        = ∑ q ∈ Iq, (2 * Q / (N : ℝ)) * (3 * ((1 + 2 * π) * Q *
        (T1 q + (K : ℝ) * cq q)) * ((N : ℝ) * q * S1) ^ 2) from by
      rw [Finset.mul_sum]]
    rw [show 6 * (1 + 2 * π) * Q ^ 2 * (N : ℝ) * S1 ^ 2 *
        ∑ q ∈ Iq, (q : ℝ) ^ 2 * (T1 q + (K : ℝ) * cq q)
        = ∑ q ∈ Iq, 6 * (1 + 2 * π) * Q ^ 2 * (N : ℝ) * S1 ^ 2 *
            ((q : ℝ) ^ 2 * (T1 q + (K : ℝ) * cq q)) from by
      rw [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    field_simp
    ring
  rw [hfold]
  have hT1nn : ∀ q, 0 ≤ T1 q := by
    intro q
    rw [hT1]
    exact sum_nonneg (fun k _ => thetaError_nonneg N _)
  have hCnn : 0 ≤ 6 * (1 + 2 * π) * Q ^ 2 * (N : ℝ) * S1 ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Q)) hN0.le) (sq_nonneg S1)
  have hsplit : (∑ q ∈ Iq, (q : ℝ) ^ 2 * (T1 q + (K : ℝ) * cq q))
      ≤ Q ^ 3 * (∑ q ∈ Iq, T1 q / q) + (K : ℝ) * (∑ q ∈ Iq, (q : ℝ) ^ 2 * cq q) := by
    have hsplit_point : ∀ q ∈ Iq, (q : ℝ) ^ 2 * (T1 q + (K : ℝ) * cq q)
        = (q : ℝ) ^ 2 * T1 q + (K : ℝ) * ((q : ℝ) ^ 2 * cq q) := fun q _ => by ring
    have hle : ∀ q ∈ Iq, (q : ℝ) ^ 2 * T1 q ≤ Q ^ 3 * (T1 q / q) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hid : (q : ℝ) ^ 2 * T1 q = (q : ℝ) ^ 3 * (T1 q / q) := by
        field_simp
      rw [hid]
      refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (hT1nn q) hq0.le)
      exact pow_le_pow_left₀ (by linarith) (hqQ q hq) 3
    calc (∑ q ∈ Iq, (q : ℝ) ^ 2 * (T1 q + (K : ℝ) * cq q))
        = (∑ q ∈ Iq, (q : ℝ) ^ 2 * T1 q)
            + ∑ q ∈ Iq, (K : ℝ) * ((q : ℝ) ^ 2 * cq q) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl hsplit_point
      _ = (∑ q ∈ Iq, (q : ℝ) ^ 2 * T1 q)
            + (K : ℝ) * ∑ q ∈ Iq, (q : ℝ) ^ 2 * cq q := by
          rw [Finset.mul_sum]
      _ ≤ Q ^ 3 * (∑ q ∈ Iq, T1 q / q)
            + (K : ℝ) * ∑ q ∈ Iq, (q : ℝ) ^ 2 * cq q := by
          refine add_le_add ?_ (le_refl _)
          calc (∑ q ∈ Iq, (q : ℝ) ^ 2 * T1 q) ≤ ∑ q ∈ Iq, Q ^ 3 * (T1 q / q) :=
                Finset.sum_le_sum hle
            _ = Q ^ 3 * ∑ q ∈ Iq, T1 q / q := by rw [Finset.mul_sum]
  have hT1div : (∑ q ∈ Iq, T1 q / q)
      = ∑ q ∈ Iq, ∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q) / q :=
    Finset.sum_congr rfl (fun q _ => by rw [hT1, Finset.sum_div])
  refine (mul_le_mul_of_nonneg_left hsplit hCnn).trans ?_
  rw [hT1div]

/-- The logarithmic part of the degree-one rectangle. -/
private theorem A2_bound (A : ℝ) (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N) :
    (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
        (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q))
      ≤ 40 * A * Real.log N ^ 2 * (Qof A N) ^ 2 := by
  have hL1 : 1 ≤ Real.log N := one_le_log hN
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have hQ1 : 1 ≤ Qof A N := Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A)
  have hQ0 : (0 : ℝ) < Qof A N := by linarith
  have hlogQ : Real.log (Qof A N) = 20 * A * Real.log (Real.log N) := by
    show Real.log (Real.log N ^ (20 * A)) = _
    rw [Real.log_rpow hL0]
  have hlogL : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self (le_of_lt hL0)
  have hpt : ∀ q ∈ Icc 1 ⌊Qof A N⌋₊,
      (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q)
        ≤ 40 * A * Real.log N ^ 2 * (q : ℝ) := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hqQ : (q : ℝ) ≤ Qof A N :=
      (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le hQ0.le)
    have hlogq : Real.log q ≤ 20 * A * Real.log N := by
      rcases Nat.eq_zero_or_pos q with h | h
      · omega
      · have h1 : Real.log q ≤ Real.log (Qof A N) := Real.log_le_log hq0 hqQ
        rw [hlogQ] at h1
        have h2 := mul_le_mul_of_nonneg_left hlogL (by linarith : (0:ℝ) ≤ 20 * A)
        linarith
    have hlq : (0 : ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
    have hid : (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q)
        = (q : ℝ) * (Real.log q / Real.log 2 * Real.log N) := by
      field_simp
    rw [hid]
    have hr : Real.log q / Real.log 2 * Real.log N ≤ 40 * A * Real.log N ^ 2 := by
      have hratio : Real.log q / Real.log 2 ≤ 2 * Real.log q := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]
        nlinarith
      have h2 : Real.log q / Real.log 2 * Real.log N ≤ 2 * Real.log q * Real.log N :=
        mul_le_mul_of_nonneg_right hratio (le_of_lt hL0)
      nlinarith [h2, hlogq, hL0]
    have hqnn : (0 : ℝ) ≤ q := by positivity
    calc (q : ℝ) * (Real.log q / Real.log 2 * Real.log N)
        ≤ (q : ℝ) * (40 * A * Real.log N ^ 2) := mul_le_mul_of_nonneg_left hr hqnn
      _ = 40 * A * Real.log N ^ 2 * (q : ℝ) := by ring
  have hsum : (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, (q : ℝ))
      ≤ (Qof A N) ^ 2 := by
    have h1 : ∀ q ∈ Icc 1 ⌊Qof A N⌋₊, (q : ℝ) ≤ Qof A N := by
      intro q hq
      exact (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le hQ0.le)
    have h2 : (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, (q : ℝ))
        ≤ ∑ _q ∈ Icc 1 ⌊Qof A N⌋₊, Qof A N := sum_le_sum h1
    have h3 : (∑ _q ∈ Icc 1 ⌊Qof A N⌋₊, Qof A N)
        = (⌊Qof A N⌋₊ : ℝ) * Qof A N := by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have h4 : ((⌊Qof A N⌋₊ : ℕ) : ℝ) ≤ Qof A N := Nat.floor_le hQ0.le
    have h5 : (0 : ℝ) ≤ Qof A N := le_of_lt hQ0
    have h6 : ((⌊Qof A N⌋₊ : ℕ) : ℝ) * Qof A N ≤ Qof A N * Qof A N :=
      mul_le_mul_of_nonneg_right h4 h5
    calc (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, (q : ℝ))
        ≤ (⌊Qof A N⌋₊ : ℝ) * Qof A N := h2.trans_eq h3
      _ ≤ Qof A N * Qof A N := h6
      _ = (Qof A N) ^ 2 := by ring
  calc (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
        (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q))
      ≤ ∑ q ∈ Icc 1 ⌊Qof A N⌋₊, 40 * A * Real.log N ^ 2 * (q : ℝ) :=
        sum_le_sum hpt
    _ = 40 * A * Real.log N ^ 2 * ∑ q ∈ Icc 1 ⌊Qof A N⌋₊, (q : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ 40 * A * Real.log N ^ 2 * (Qof A N) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

/-- `(log N)^{20 A}` raised to a natural power. -/
private theorem rpow_pow_local {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ (n * a) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Four factors of one base multiply by adding the exponents. -/
private theorem rpow_prod_le {x : ℝ} (hx1 : 1 ≤ x) (hx0 : 0 < x) {a b c d e : ℝ}
    (h : a + b + c + d ≤ e) : x ^ a * x ^ b * x ^ c * x ^ d ≤ x ^ e := by
  rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx1 h

/-- The degree-one scalar rectangular mean, proved from the rectangle bound and the
linear discrepancy average. -/
private theorem linear_scalar_mean_proof :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 1 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1nn, hC1⟩ := theta_linear_le A hA
  refine ⟨42336 * (1 + 2 * π) * C1 * A ^ 2 + 3840 * (1 + 2 * π) * A, 3,
    fun N _ hN => ?_⟩
  have hN3 : 3 ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := one_le_log hN3
  have hL0 : 0 < Real.log N := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log N with hL
  set Q : ℝ := Qof A N with hQ
  set K : ℕ := cutoff (10 ^ 4 * A) N with hK
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A)
  have hQ0 : 0 < Q := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hS1nn : 0 ≤ ∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹ :=
    sum_nonneg (fun k _ => by positivity)
  -- the discrepancy average
  have hAlin := hC1 N hN3 K ⌊Q⌋₊ (le_of_eq hK.symm) (le_refl _)
  have hlogK : 1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ≤ 21 * A * L := by
    have hQlog : Real.log Q = 20 * A * Real.log L := by
      rw [hQ]
      show Real.log (Real.log N ^ (20 * A)) = 20 * A * Real.log L
      rw [Real.log_rpow hL0]
    have hle : Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Real.log Q := by
      rcases Nat.eq_zero_or_pos ⌊Q⌋₊ with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        have : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ1
        linarith
      · have h1 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
        have h2 : (0 : ℝ) < ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpos
        exact Real.log_le_log h2 h1
    have hlogL : Real.log L ≤ L := Real.log_le_self (le_of_lt hL0)
    have h20 : (0 : ℝ) ≤ 20 * A := by linarith
    have hstep : Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ≤ 20 * A * L := by
      have := mul_le_mul_of_nonneg_left hlogL h20
      linarith [hle, hQlog]
    nlinarith
  have hA1 : (∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q) / q)
      ≤ C1 * (21 * A * L) ^ 2 * (N : ℝ) * L ^ (-(2000 * A)) := by
    refine hAlin.trans ?_
    have hnn : (0 : ℝ) ≤ 1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := Real.log_natCast_nonneg _
      linarith
    have hsq : (1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ)) ^ 2 ≤ (21 * A * L) ^ 2 :=
      pow_le_pow_left₀ hnn hlogK 2
    have hLn : (0 : ℝ) ≤ L ^ (-(2000 * A)) := Real.rpow_nonneg (le_of_lt hL0) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC1nn)
        (Nat.cast_nonneg N)) hLn
  -- the logarithmic rectangle
  have hA2 : (∑ q ∈ Icc 1 ⌊Q⌋₊, (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q))
      ≤ 40 * A * L ^ 2 * Q ^ 2 := by
    have h := A2_bound A hA hN3
    rw [hQ, hL]
    exact h
  -- the totient sum
  have hS1 : (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ (1 + L) ^ 2 := by
    refine (sum_inv_totient_le K).trans ?_
    have hKN : K ≤ N := by
      rw [hK]
      exact cutoff_le (10 ^ 4 * A) N (by positivity) hL1
    have hcast : ((K : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hKN
    have hlog : Real.log K ≤ L := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        have : (0 : ℝ) ≤ L := le_of_lt hL0
        linarith
      · have hh := Real.log_le_log (by exact_mod_cast hpos) hcast
        rw [← hL] at hh
        exact hh
    have h1 : (1 + Real.log K) ≤ (1 + L) := by linarith
    exact pow_le_pow_left₀ (one_add_log_nat_nonneg K) h1 2
  have hS1sq : (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 ≤ 16 * L ^ 4 := by
    calc (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 ≤ ((1 + L) ^ 2) ^ 2 :=
          pow_le_pow_left₀ hS1nn hS1 2
      _ = (1 + L) ^ 4 := by ring
      _ ≤ (2 * L) ^ 4 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 4
          linarith
      _ = 16 * L ^ 4 := by ring
  have hQ5 : Q ^ 5 ≤ L ^ (100 * A) := by
    rw [hQ]
    refine le_of_eq ?_
    show (Real.log N ^ (20 * A)) ^ 5 = Real.log N ^ (100 * A)
    rw [rpow_pow_local (le_of_lt hL0)]
    congr 1
    push_cast
    ring
  have hQ4 : Q ^ 4 ≤ L ^ (80 * A) := by
    rw [hQ]
    refine le_of_eq ?_
    show (Real.log N ^ (20 * A)) ^ 4 = Real.log N ^ (80 * A)
    rw [rpow_pow_local (le_of_lt hL0)]
    congr 1
    push_cast
    ring
  have hKle : (K : ℝ) ≤ Real.sqrt N * L ^ (-(10 ^ 4 * A)) := by
    have h1 : (K : ℝ) ≤ ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) := by rw [hK]
    have h2 : ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) ≤
        Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)) := by
      rw [cutoff]
      exact Nat.floor_le (mul_nonneg (Real.sqrt_nonneg N)
        (Real.rpow_nonneg (le_of_lt hL0) _))
    rw [hL]
    exact h1.trans h2
  have hsqrt : Real.sqrt N ≤ (N : ℝ) := by
    have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt N ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt hNsq
      _ = (N : ℝ) := Real.sqrt_sq (le_of_lt hN0)
  -- the two terms
  have hterm1 : 6 * (1 + 2 * π) * C1 * (21 * A) ^ 2 * Q ^ 5 * (N : ℝ) ^ 2 *
        (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 * L ^ 2 * L ^ (-(2000 * A))
      ≤ 42336 * (1 + 2 * π) * C1 * A ^ 2 * (N : ℝ) ^ 2 * L ^ (-A) := by
    have hbase : (0 : ℝ) ≤ 6 * (1 + 2 * π) * C1 * (21 * A) ^ 2 * (N : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 6)
        (by positivity : (0:ℝ) ≤ 1 + 2 * π)) hC1nn) (sq_nonneg (21 * A)))
        (sq_nonneg (N : ℝ))
    calc 6 * (1 + 2 * π) * C1 * (21 * A) ^ 2 * Q ^ 5 * (N : ℝ) ^ 2 *
          (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 * L ^ 2 * L ^ (-(2000 * A))
        ≤ 6 * (1 + 2 * π) * C1 * (21 * A) ^ 2 * L ^ (100 * A) * (N : ℝ) ^ 2 *
            (16 * L ^ 4) * L ^ 2 * L ^ (-(2000 * A)) := by
          gcongr
      _ = 42336 * (1 + 2 * π) * C1 * A ^ 2 * (N : ℝ) ^ 2 *
            (L ^ (100 * A) * L ^ 4 * L ^ 2 * L ^ (-(2000 * A))) := by ring
      _ ≤ 42336 * (1 + 2 * π) * C1 * A ^ 2 * (N : ℝ) ^ 2 * L ^ (-A) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.rpow_natCast L 4, ← Real.rpow_natCast L 2]
          exact rpow_prod_le (x := L) hL1 hL0 (a := 100 * A) (b := 4) (c := 2)
            (d := -(2000 * A)) (e := -A) (by nlinarith [hA])
  have hterm2 : 240 * (1 + 2 * π) * A * Q ^ 4 * (N : ℝ) *
        (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 * (K : ℝ) * L ^ 2
      ≤ 3840 * (1 + 2 * π) * A * (N : ℝ) ^ 2 * L ^ (-A) := by
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    calc 240 * (1 + 2 * π) * A * Q ^ 4 * (N : ℝ) *
          (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 * (K : ℝ) * L ^ 2
        ≤ 240 * (1 + 2 * π) * A * L ^ (80 * A) * (N : ℝ) * (16 * L ^ 4) *
            (Real.sqrt N * L ^ (-(10 ^ 4 * A))) * L ^ 2 := by
          gcongr
      _ = 3840 * (1 + 2 * π) * A * ((N : ℝ) * Real.sqrt N) *
            (L ^ (80 * A) * L ^ 4 * L ^ (-(10 ^ 4 * A)) * L ^ 2) := by ring
      _ ≤ 3840 * (1 + 2 * π) * A * (N : ℝ) ^ 2 *
            (L ^ (80 * A) * L ^ 4 * L ^ (-(10 ^ 4 * A)) * L ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (N : ℝ) * Real.sqrt N ≤ (N : ℝ) * (N : ℝ) :=
                mul_le_mul_of_nonneg_left hsqrt hN0.le
            _ = (N : ℝ) ^ 2 := by ring
      _ ≤ 3840 * (1 + 2 * π) * A * (N : ℝ) ^ 2 * L ^ (-A) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.rpow_natCast L 4, ← Real.rpow_natCast L 2]
          exact rpow_prod_le (x := L) hL1 hL0 (a := 80 * A) (b := 4) (c := -(10 ^ 4 * A))
            (d := 2) (e := -A)
            (by
              have h10 : ((10 : ℝ)) ^ 4 = 10000 := by norm_num
              rw [h10] at hA ⊢
              nlinarith [hA])
  -- assemble
  have hrect := scalarMean_one_bound A hA hN3
  have hstep : (Qof A N) ^ 3 *
        (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N),
          thetaError N (Nat.lcm k q) / q)
      + (cutoff (10 ^ 4 * A) N : ℝ) *
        (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          (q : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q))
      ≤ Q ^ 3 * (C1 * (21 * A * L) ^ 2 * (N : ℝ) * L ^ (-(2000 * A)))
        + (K : ℝ) * (40 * A * L ^ 2 * Q ^ 2) := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_left hA1 (by positivity)
    · exact mul_le_mul_of_nonneg_left hA2 (by positivity)
  refine hrect.trans ?_
  have hc : (0 : ℝ) ≤ 6 * (1 + 2 * π) * Q ^ 2 * (N : ℝ) *
      (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Q)) hN0.le)
      (sq_nonneg _)
  refine (mul_le_mul_of_nonneg_left hstep hc).trans ?_
  have hstep2 : 6 * (1 + 2 * π) * Q ^ 2 * (N : ℝ) *
        (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 *
        (Q ^ 3 * (C1 * (21 * A * L) ^ 2 * (N : ℝ) * L ^ (-(2000 * A)))
          + (K : ℝ) * (40 * A * L ^ 2 * Q ^ 2))
      = 6 * (1 + 2 * π) * C1 * (21 * A) ^ 2 * Q ^ 5 * (N : ℝ) ^ 2 *
          (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 * L ^ 2 * L ^ (-(2000 * A))
        + 240 * (1 + 2 * π) * A * Q ^ 4 * (N : ℝ) *
          (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ^ 2 * (K : ℝ) * L ^ 2 := by
    ring
  rw [hstep2]
  refine (add_le_add hterm1 hterm2).trans ?_
  refine le_of_eq ?_
  ring

end LinearScalarMean

/-- Halupczok page 9, O1, the positive scalar rectangular mean.
Only real theta discrepancies, totients, logarithms and natural modulus sums occur.
There are no prime polynomials, rational phases, residue variables, signed weights
or integrals in this arithmetic leaf. The bad prime profile is explicit. Proved. -/
theorem linear_scalar_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 1 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  exact linear_scalar_mean_proof

/-- Halupczok page 9, O1, after discrete partial summation on page 7.
Estimate only the static positive degree 1 rational prefix discrepancy average.
There is no beta variable, integral or arbitrary lambda. The full prime interval
and the fixed third residue retain the sealed 2009 adaptation.
Derived from linear_scalar_mean. -/
theorem linear_prefix_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        EF (fun k l => errorEnvelope 1 (Qof A N) (τof A N) k l N)
          (fun _ => 1) l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := linear_scalar_mean A hA
  refine ⟨C, max N₀ 3, fun N hodd hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  exact (prefix_mean_le_scalar 1 A N l₃ hQ (by exact_mod_cast (show (1 : ℝ) ≤ N by linarith))).trans
    (h N hodd ((le_max_left _ _).trans hN))

/-- The exact sealed degree 1 remainder statement.
Derived from the static positive prefix mean. No new integral estimate is assumed. -/
theorem linear_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 1 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := linear_prefix_mean A hA l₃ hl₃
  exact ⟨C, N₀, fun lam hlam N hodd hN =>
    (error_mean_bound 1 A lam l₃ N hlam).trans (h N hodd hN)⟩

end LeanLab.Tolev2009.Decomp346a
