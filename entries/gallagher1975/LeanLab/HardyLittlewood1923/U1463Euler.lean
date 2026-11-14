module

public import LeanLab.HardyLittlewood1923.EulerR

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T0403Z-7595, unit U-1463, paper P0004.

# Hardy-Littlewood 1923, the Euler identity of the Theorem B recursion with a power rate

`EulerR.euler_avg_r` gives `Σ_{d ≤ D, (d,n)=1} g_r(d)/φ(d) → (C_{r+1}/C_r) Br (r+1) n` with no
rate. For Theorem A with a power saving the rate matters. Here, for `r ≥ 3` and `n ≥ 1`:

* `euler_rate`: `|Σ_{d ≤ n squarefree} HR r n d - (C_{r+1}/C_r) Br (r+1) n| ≤ e²⁴/(n √n)`.
  Route: for every `M ≥ n` the full squarefree divisor sum of `primorial M` is the Euler product
  `(∏_{p ≤ M} frR (r+1) p / ∏_{p ≤ M} frR r p) Br (r+1) n`, by `local_identity_r`; the part with
  `d > n` is at most `n^{-3/2} Σ_d |HR(d)| d √d`, and `|HR(p)| p ≤ 3/(p-1)²` bounds that Euler
  product by `e²⁴`; then `M → ∞`.
* `gr_dphi_bdd`: `Σ_{d < N squarefree} |g_r(d)| d/φ(d) ≤ e²⁴`, the same Euler product at `n = 1`.

No hypothesis. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1463

open Real Finset Filter Topology
open LeanLab.HardyLittlewood1923
open LeanLab.PNTPort.Vinogradov (dvd_primorial_of_sqf sum_tele_le)

/-- `d ↦ F(d) d`. -/
noncomputable def mulId (F : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => F d * d, by simp⟩

lemma mulId_apply (F : ArithmeticFunction ℝ) (d : ℕ) : mulId F d = F d * d := rfl

lemma mulId_mult {F : ArithmeticFunction ℝ} (hF : F.IsMultiplicative) :
    (mulId F).IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · show F 1 * ((1 : ℕ) : ℝ) = 1
    rw [hF.map_one]; simp
  · show F (a * b) * ((a * b : ℕ) : ℝ) = (F a * a) * (F b * b)
    rw [hF.map_mul_of_coprime hab]; push_cast; ring

/-- The Euler product bound of `EulerE.euler_absSqrt_le` with a constant `c`. -/
theorem euler_absSqrt_le_c (F : ArithmeticFunction ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hp : ∀ p : ℕ, p.Prime → |F p| ≤ c / ((p : ℝ) - 1) ^ 2) (D : ℕ) :
    ∏ p ∈ Nat.primesLE D, (1 + absSqrt F p) ≤ Real.exp (8 * c) := by
  have h0 : ∀ p ∈ Nat.primesLE D, 0 ≤ 1 + absSqrt F p := fun p _ => by
    rw [absSqrt_apply]; positivity
  calc ∏ p ∈ Nat.primesLE D, (1 + absSqrt F p) ≤ ∏ p ∈ Nat.primesLE D, Real.exp (absSqrt F p) :=
        Finset.prod_le_prod₀ (h0 := h0) (h1 := fun p _ => by
          have := Real.add_one_le_exp (absSqrt F p); linarith)
    _ = Real.exp (∑ p ∈ Nat.primesLE D, absSqrt F p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (8 * c) := by
        apply Real.exp_le_exp.2
        calc ∑ p ∈ Nat.primesLE D, absSqrt F p
            ≤ ∑ p ∈ Nat.primesLE D, c * (Real.sqrt p / ((p : ℝ) - 1) ^ 2) := by
              refine sum_le_sum fun p hp' => ?_
              rw [Nat.mem_primesLE] at hp'
              rw [absSqrt_apply, mul_comm]
              have := hp p hp'.2
              have hs := Real.sqrt_nonneg (p : ℝ)
              calc Real.sqrt p * |F p| ≤ Real.sqrt p * (c / ((p : ℝ) - 1) ^ 2) :=
                    mul_le_mul_of_nonneg_left this hs
                _ = c * (Real.sqrt p / ((p : ℝ) - 1) ^ 2) := by ring
          _ = c * ∑ p ∈ Nat.primesLE D, Real.sqrt p / ((p : ℝ) - 1) ^ 2 := by rw [mul_sum]
          _ ≤ c * ∑ m ∈ Icc 2 D, Real.sqrt m / ((m : ℝ) - 1) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ hc
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp'
                rw [Nat.mem_primesLE] at hp'
                rw [mem_Icc]; exact ⟨hp'.2.two_le, hp'.1⟩
              · intro _ _ _; positivity
          _ ≤ c * 8 := mul_le_mul_of_nonneg_left (sum_tele_le D) hc
          _ = 8 * c := by ring

/-- The full squarefree divisor sum of `|F d| √d` over `primorial M` is at most `e^{8c}`. -/
theorem sum_divisors_absSqrt_le (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative) (c : ℝ)
    (hc : 0 ≤ c) (hp : ∀ p : ℕ, p.Prime → |F p| ≤ c / ((p : ℝ) - 1) ^ 2) (M : ℕ) :
    ∑ d ∈ (primorial M).divisors, absSqrt F d ≤ Real.exp (8 * c) := by
  rw [← (absSqrt_mult hF).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial M),
    primeFactors_primorial]
  exact euler_absSqrt_le_c F c hc hp M

/-- `|phiR r n p| p ≤ 3/(p-1)²` for `r ≥ 3`. -/
theorem phiR_mul_le (r : ℕ) (hr : 3 ≤ r) (n : ℕ) {p : ℕ} (hp : p.Prime) :
    |phiR r n p * p| ≤ 3 / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hnn : 0 ≤ 3 / ((p : ℝ) - 1) ^ 2 := by
    apply div_nonneg (by norm_num); apply pow_nonneg; linarith
  unfold phiR
  split_ifs with h
  · rw [zero_mul, abs_zero]; exact hnn
  by_cases h2 : p = 2
  · subst h2; norm_num [gvR]
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_prime_ne_two hp h2
  have hg := abs_gvR_le r hr hp
  rw [ttR_odd hp h2] at hg
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [abs_mul, abs_div, abs_of_pos hq, abs_of_pos (by linarith : (0 : ℝ) < p)]
  calc |gvR r p| / ((p : ℝ) - 1) * p
      ≤ 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) / ((p : ℝ) - 1) * p := by gcongr
    _ ≤ 3 / ((p : ℝ) - 1) ^ 2 := by
        rw [div_div, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ ((p : ℝ) - 1) ^ 2 := sq_nonneg _
        nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ (p : ℝ) - 3)]

theorem mulId_HR_bound (r : ℕ) (hr : 3 ≤ r) (n : ℕ) :
    ∀ p : ℕ, p.Prime → |mulId (HR r n) p| ≤ 3 / ((p : ℝ) - 1) ^ 2 := fun p hp => by
  rw [mulId_apply, HR_prime r n hp]; exact phiR_mul_le r hr n hp

/-- The squarefree `d ≤ n` dividing `primorial M`, `M ≥ n`. -/
lemma set_le (n M : ℕ) (hM : n ≤ M) :
    (primorial M).divisors.filter (fun d => d ≤ n) = (Icc 1 n).filter Squarefree := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h1 (primorial_pos M), h3⟩,
      (squarefree_primorial M).squarefree_of_dvd h1⟩
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨⟨dvd_primorial_of_sqf h3 (h2.trans hM), (primorial_pos M).ne'⟩, h2⟩

/-- **The Euler identity with a rate**: for `r ≥ 3`, `n ≥ 1`,
`|Σ_{d ≤ n squarefree} HR r n d - (C_{r+1}/C_r) Br (r+1) n| ≤ e²⁴/(n √n)`. -/
theorem euler_rate (r : ℕ) (hr : 3 ≤ r) (n : ℕ) (hn : 1 ≤ n) :
    |∑ d ∈ (Icc 1 n).filter Squarefree, HR r n d - Cr (r + 1) / Cr r * Br (r + 1) n| ≤
      Real.exp 24 / ((n : ℝ) * Real.sqrt n) := by
  set S := ∑ d ∈ (Icc 1 n).filter Squarefree, HR r n d with hS
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hnn : 0 < (n : ℝ) * Real.sqrt n := mul_pos hnr hsn
  -- the bound for each `M ≥ n`
  have hM : ∀ M : ℕ, n ≤ M →
      |S - (∏ p ∈ Nat.primesLE M, frR (r + 1) p) / (∏ p ∈ Nat.primesLE M, frR r p) *
        Br (r + 1) n| ≤ Real.exp 24 / ((n : ℝ) * Real.sqrt n) := by
    intro M hnM
    have hA0 : 0 < ∏ p ∈ Nat.primesLE M, frR r p := lt_of_lt_of_le (by norm_num) (frR_prod_ge r hr M)
    have hfull : ∑ d ∈ (primorial M).divisors, HR r n d =
        ∏ p ∈ Nat.primesLE M, (1 + phiR r n p) := by
      rw [← (HR_mult r n).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial M),
        primeFactors_primorial]
      exact prod_congr rfl fun p hp => by rw [HR_prime r n (Nat.mem_primesLE.1 hp).2]
    have hAE : (∏ p ∈ Nat.primesLE M, frR r p) * ∏ p ∈ Nat.primesLE M, (1 + phiR r n p) =
        (∏ p ∈ Nat.primesLE M, frR (r + 1) p) * Br (r + 1) n := by
      rw [Br_eq_prod r n M hn hnM, ← prod_mul_distrib, ← prod_mul_distrib]
      exact prod_congr rfl fun p hp => local_identity_r r hr n (Nat.mem_primesLE.1 hp).2
    have hE : ∏ p ∈ Nat.primesLE M, (1 + phiR r n p) =
        (∏ p ∈ Nat.primesLE M, frR (r + 1) p) / (∏ p ∈ Nat.primesLE M, frR r p) * Br (r + 1) n := by
      rw [div_mul_eq_mul_div, eq_div_iff hA0.ne', mul_comm, hAE]
    have hsplit := sum_filter_add_sum_filter_not (primorial M).divisors (fun d => d ≤ n) (HR r n)
    rw [set_le n M hnM, hfull, hE] at hsplit
    have e : S - (∏ p ∈ Nat.primesLE M, frR (r + 1) p) / (∏ p ∈ Nat.primesLE M, frR r p) *
        Br (r + 1) n = -∑ d ∈ (primorial M).divisors.filter (fun d => ¬ d ≤ n), HR r n d := by
      rw [hS]; linarith
    rw [e, abs_neg]
    -- the tail `d > n`
    calc |∑ d ∈ (primorial M).divisors.filter (fun d => ¬ d ≤ n), HR r n d|
        ≤ ∑ d ∈ (primorial M).divisors.filter (fun d => ¬ d ≤ n), |HR r n d| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ (primorial M).divisors.filter (fun d => ¬ d ≤ n),
            absSqrt (mulId (HR r n)) d / ((n : ℝ) * Real.sqrt n) := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter] at hd
          have hdn : (n : ℝ) ≤ d := by exact_mod_cast (by omega : n ≤ d)
          rw [absSqrt_apply, mulId_apply, le_div_iff₀ hnn, abs_mul, Nat.abs_cast]
          have h1 : (n : ℝ) * Real.sqrt n ≤ d * Real.sqrt d :=
            mul_le_mul hdn (Real.sqrt_le_sqrt hdn) hsn.le (Nat.cast_nonneg d)
          have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (HR r n d))
          linarith
      _ ≤ ∑ d ∈ (primorial M).divisors, absSqrt (mulId (HR r n)) d / ((n : ℝ) * Real.sqrt n) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _; rw [absSqrt_apply]; positivity
      _ = (∑ d ∈ (primorial M).divisors, absSqrt (mulId (HR r n)) d) / ((n : ℝ) * Real.sqrt n) := by
          rw [sum_div]
      _ ≤ Real.exp (8 * 3) / ((n : ℝ) * Real.sqrt n) := by
          gcongr
          exact sum_divisors_absSqrt_le _ (mulId_mult (HR_mult r n)) 3 (by norm_num)
            (mulId_HR_bound r hr n) M
      _ = Real.exp 24 / ((n : ℝ) * Real.sqrt n) := by norm_num
  -- the limit `M → ∞`
  have hC0 : 0 < Cr r := Cr_pos r hr
  have hlim : Tendsto (fun M : ℕ => |S - (∏ p ∈ Nat.primesLE M, frR (r + 1) p) /
      (∏ p ∈ Nat.primesLE M, frR r p) * Br (r + 1) n|) atTop
      (𝓝 |S - Cr (r + 1) / Cr r * Br (r + 1) n|) := by
    have h := ((tendsto_frR (r + 1) (by omega)).div (tendsto_frR r hr) hC0.ne').mul_const
      (Br (r + 1) n)
    exact (h.const_sub S).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, hM⟩)

/-- **`Σ_{d < N squarefree} |g_r(d)| d/φ(d) ≤ e²⁴`** for `r ≥ 3`. -/
theorem gr_dphi_bdd (r : ℕ) (hr : 3 ≤ r) (N : ℕ) :
    ∑ d ∈ (Finset.range N).filter Squarefree, |gr r d| * ((d : ℝ) / (Nat.totient d : ℝ)) ≤
      Real.exp 24 := by
  calc ∑ d ∈ (Finset.range N).filter Squarefree, |gr r d| * ((d : ℝ) / (Nat.totient d : ℝ))
      ≤ ∑ d ∈ (Finset.range N).filter Squarefree, absSqrt (mulId (HR r 1)) d := by
        refine sum_le_sum fun d hd => ?_
        rw [mem_filter] at hd
        have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd.2.ne_zero
        have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        rw [absSqrt_apply, mulId_apply, HR_eq r 1 hd.2, if_pos (Nat.coprime_one_right d)]
        have hs : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd1'
        have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have e : |gr r d / (Nat.totient d : ℝ) * d| = |gr r d| * ((d : ℝ) / (Nat.totient d : ℝ)) := by
          rw [abs_mul, abs_div, abs_of_pos hφ, Nat.abs_cast]; ring
        rw [e]
        have h0 : 0 ≤ |gr r d| * ((d : ℝ) / (Nat.totient d : ℝ)) := by positivity
        nlinarith
    _ ≤ ∑ d ∈ (primorial N).divisors, absSqrt (mulId (HR r 1)) d := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter, mem_range] at hd
          exact Nat.mem_divisors.2 ⟨dvd_primorial_of_sqf hd.2 hd.1.le, (primorial_pos N).ne'⟩
        · intro d _ _; rw [absSqrt_apply]; positivity
    _ ≤ Real.exp (8 * 3) :=
        sum_divisors_absSqrt_le _ (mulId_mult (HR_mult r 1)) 3 (by norm_num) (mulId_HR_bound r hr 1) N
    _ = Real.exp 24 := by norm_num

end LeanLab.HardyLittlewood1923.U1463
