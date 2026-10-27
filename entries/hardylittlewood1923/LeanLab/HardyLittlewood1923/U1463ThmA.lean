module

public import LeanLab.HardyLittlewood1923.TheoremBUnlike
public import LeanLab.HardyLittlewood1923.U1453PrintedA3
public import LeanLab.HardyLittlewood1923.U1463Euler

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T0403Z-7595, unit U-1463, paper P0004.

# Hardy-Littlewood 1923, Theorem A for every r ≥ 3 with the printed power saving, upper range

Printed, eq. (3.113) p. 21: on Hypothesis R at level `Θ < 3/4`, for every `r ≥ 3`,
`ν_r(n) = n^{r-1}/(r-1)! S_r(n) + O(n^{r-1+(Θ-3/4)} (log n)^B)`.

U-1453 proved `r = 3` for `47/64 ≤ Θ < 3/4`, CONDITIONAL ON `ExplicitFormulaLog`. Here the Theorem B
recursion `ν_{r+1}(n) = Σ_p log p ν_r(n - p)`, `TheoremBRec.nur_succ`, carries the saving to every
`r ≥ 3`, with the main term `Mr r n = (2 C_r/(r-1)!) n^{r-1} Br r n` of Theorem B.

* `APow r e B`: `|ν_r(n) - Mr r n| ≤ K n^{r-1+e} (log n)^B` for `n ≡ r mod 2`, `n` large.
* `Ssum_head`: `PsiPowerLog θ` gives `Σ_{p ≡ n (d)} log p (n-p)^s = n^{s+1}/((s+1) φ(d)) + E`,
  `|E| ≤ n^s ((C+4) n^θ (log n)² + d/φ(d))`, uniformly in `d ≤ n` coprime to `n`.
* `apow_step`: for `s ≥ 2`, `1/2 ≤ θ`, `θ - 1 ≤ e`, `PsiPowerLog θ` and `APow (s+1) e B` give
  `APow (s+2) e (B+s+1)`; the Euler identity with rate is `U1463Euler.euler_rate`.
* `apow_all`: from a base `APow 3 e B` to every `r ≥ 3`.
* `printedA_upper_all`: CONDITIONAL ON `ExplicitFormulaLog`, for every `r ≥ 3` and every
  `Θ ∈ [47/64, 3/4)` with no zeros right of `Θ`, `APow r (Θ - 3/4) B` for some `B`.
* `printedA_upper_all_of_R`: the same on `47/64 < Θ < 3/4` CONDITIONAL ON U-1438's `PsiPowerOfR`.
* `SingRProduct`, an open lab target, the Euler product `S_r(n) = 2 C_r Br r n` for like parity
  and `0` otherwise; `printedA_form_all`: with it, the printed form with `singR` for every `n`.

Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1463

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.U1444
open LeanLab.HardyLittlewood1923.U1453

/-- Theorem A with the main term of Theorem B, like parity, error `K n^{r-1+e} (log n)^B`. -/
def APow (r : ℕ) (e : ℝ) (B : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n % 2 = r % 2 → n₀ ≤ n →
    |nur r n - Mr r n| ≤ K * (n : ℝ) ^ ((r : ℝ) - 1 + e) * Real.log n ^ B

/-! ### Small helpers -/

lemma one_le_log_of_three {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hn3

lemma npow_le_rpow {n : ℕ} (hn : 1 ≤ n) {a : ℕ} {x : ℝ} (h : (a : ℝ) ≤ x) :
    (n : ℝ) ^ a ≤ (n : ℝ) ^ x := by
  rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

lemma log_pow_mono {n : ℕ} (hn : 3 ≤ n) {a b : ℕ} (h : a ≤ b) :
    Real.log n ^ a ≤ Real.log n ^ b :=
  pow_le_pow_right₀ (one_le_log_of_three hn) h

/-! ### Primes in progressions with power weight and a power saving -/

/-- Summation by parts with a bound on `ψ(j; d, a) - j/φ(d)` for `j ≤ n` only. -/
lemma W_pow_le (d a k n : ℕ) (Bn : ℝ)
    (hB : ∀ j : ℕ, j ≤ n →
      |HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ)| ≤ Bn) :
    |∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k
      - (∑ i ∈ range n, (i : ℝ) ^ k) / (Nat.totient d : ℝ)| ≤ Bn * (n : ℝ) ^ k := by
  set P : ℕ → ℝ := fun i => (i : ℝ) ^ k with hP
  have e1 : ∑ m ∈ range (n + 1), gfun d a m * ((n : ℝ) - m) ^ k =
      ∑ m ∈ range (n + 1), gfun d a m * P (n - m) := by
    apply sum_congr rfl; intro m hm
    have : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
    simp only [hP]; rw [Nat.cast_sub this]
  rw [e1, abel_conv, ← sum_j_dif, sum_div, ← sum_sub_distrib]
  calc _ ≤ ∑ j ∈ range (n + 1), |(∑ m ∈ range (j + 1), gfun d a m) * dif P (n - j)
          - (j : ℝ) * dif P (n - j) / (Nat.totient d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (n + 1), Bn * dif P (n - j) := by
        apply sum_le_sum; intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
        have hD := dif_pow_nonneg k (n - j)
        have : (∑ m ∈ range (j + 1), gfun d a m) * dif P (n - j)
            - (j : ℝ) * dif P (n - j) / (Nat.totient d : ℝ) =
            (HeathBrown1985.psi (j : ℝ) d a - (j : ℝ) / (Nat.totient d : ℝ)) * dif P (n - j) := by
          rw [psi_eq_sum_gfun]; ring
        rw [this, abs_mul, abs_of_nonneg hD]
        exact mul_le_mul_of_nonneg_right (hB j hjn) hD
    _ = Bn * (n : ℝ) ^ k := by
        rw [← mul_sum, sum_reflect (dif P) n, sum_dif]

lemma gfun_nonneg (d a m : ℕ) : 0 ≤ gfun d a m := by
  unfold gfun; split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

/-- Below the modulus, or below `2`, `0 ≤ ψ(j; d, a) ≤ log n`. -/
lemma psi_small (d a j n : ℕ) (hj : j < d ∨ j ≤ 1) (hjn : j ≤ n) :
    0 ≤ HeathBrown1985.psi (j : ℝ) d a ∧ HeathBrown1985.psi (j : ℝ) d a ≤ Real.log n := by
  rw [psi_eq_sum_gfun]
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  refine ⟨sum_nonneg fun m _ => gfun_nonneg d a m, ?_⟩
  calc ∑ m ∈ range (j + 1), gfun d a m
      ≤ ∑ m ∈ range (j + 1), (if m = a % d then Real.log n else 0) := by
        refine sum_le_sum fun m hm => ?_
        have hmj : m ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hm)
        have hR : 0 ≤ (if m = a % d then Real.log n else 0) := by split_ifs <;> simp [hL]
        by_cases hm1 : m ≤ 1
        · have hΛ : Λ m = 0 := by
            interval_cases m <;> simp
          have : gfun d a m ≤ 0 := by unfold gfun; split_ifs <;> simp [hΛ]
          linarith
        · have hjd : j < d := by
            rcases hj with h | h
            · exact h
            · omega
          unfold gfun
          rw [Nat.mod_eq_of_lt (by omega : m < d)]
          split_ifs with h1
          · exact (ArithmeticFunction.vonMangoldt_le_log).trans (log_le_log_nat (by omega))
          · exact le_rfl
    _ = if a % d ∈ range (j + 1) then Real.log n else 0 := sum_ite_eq' _ _ _
    _ ≤ Real.log n := by split_ifs <;> simp [hL]

/-- The uniform deviation bound for `j ≤ n` from `PsiPowerLog θ`. -/
lemma psi_dev_le {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hψ : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
      |HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 2)
    {n d : ℕ} (hd : 1 ≤ d) (hc : Nat.Coprime d n) (j : ℕ) (hjn : j ≤ n) :
    |HeathBrown1985.psi (j : ℝ) d n - (j : ℝ) / (Nat.totient d : ℝ)| ≤
      C * (n : ℝ) ^ θ * Real.log n ^ 2 + Real.log n + (d : ℝ) / (Nat.totient d : ℝ) := by
  have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hA : 0 ≤ C * (n : ℝ) ^ θ * Real.log n ^ 2 := by positivity
  have hdφ : 0 ≤ (d : ℝ) / (Nat.totient d : ℝ) := by positivity
  by_cases hbig : 2 ≤ j ∧ d ≤ j
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hbig.1
    have h := hψ j hj2 d n hd hc.symm (by exact_mod_cast hbig.2)
    have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by linarith)
    have h1 : (j : ℝ) ^ θ ≤ (n : ℝ) ^ θ := Real.rpow_le_rpow (by linarith) hjn' hθ
    have h2 : Real.log j ^ 2 ≤ Real.log n ^ 2 :=
      pow_le_pow_left₀ hlj (log_le_log_nat hjn) 2
    have h3 : C * (j : ℝ) ^ θ * Real.log j ^ 2 ≤ C * (n : ℝ) ^ θ * Real.log n ^ 2 := by
      gcongr
    linarith
  · have hj : j < d ∨ j ≤ 1 := by omega
    obtain ⟨h0, h1⟩ := psi_small d n j n hj hjn
    have hjd : (j : ℝ) ≤ d := by
      rcases hj with h | h
      · exact_mod_cast h.le
      · exact_mod_cast (by omega : j ≤ d)
    have h2 : (j : ℝ) / (Nat.totient d : ℝ) ≤ (d : ℝ) / (Nat.totient d : ℝ) :=
      div_le_div_of_nonneg_right hjd hφ.le
    have h3 : 0 ≤ (j : ℝ) / (Nat.totient d : ℝ) := by positivity
    rw [abs_le]; constructor <;> linarith

/-- **The head term with a power saving**, uniformly in `d ≤ n` coprime to `n`. -/
lemma Ssum_head (s : ℕ) {θ C : ℝ} (hθ : 1 / 2 ≤ θ) (hC : 0 ≤ C)
    (hψ : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
      |HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 2)
    {n d : ℕ} (hn : 3 ≤ n) (hd : 1 ≤ d) (hc : Nat.Coprime d n) :
    |Ssum s d n - (n : ℝ) ^ (s + 1) / ((s + 1) * (Nat.totient d : ℝ))| ≤
      (n : ℝ) ^ s * ((C + 4) * (n : ℝ) ^ θ * Real.log n ^ 2 + (d : ℝ) / (Nat.totient d : ℝ)) := by
  have hWM := W_pow_le d n s n _ (psi_dev_le (by linarith) hC hψ hd hc)
  have hTW := T_le_W_pow d n n s
  have hWT := W_sub_T_le_pow d n n s
  have hup := sum_pow_upper s n
  have hlo := sum_pow_lower' s n
  have hL1 := one_le_log_of_three hn
  have hT : Ssum s d n = ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d),
      Real.log p * ((n : ℝ) - p) ^ s := rfl
  rw [hT]
  set N : ℝ := (n : ℝ) with hNdef
  have hN3 : (3 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set L := Real.log N with hLdef
  set φ : ℝ := (Nat.totient d : ℝ) with hφdef
  have hφ1 : (1 : ℝ) ≤ φ := by
    rw [hφdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.2 (by omega)).ne'
  have hφ0 : 0 < φ := by linarith
  set S := ∑ i ∈ range n, (i : ℝ) ^ s with hSdef
  set T := ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d),
    Real.log p * (N - p) ^ s with hTdef
  set W := ∑ m ∈ range (n + 1), gfun d n m * (N - m) ^ s with hWdef
  have hNs : 0 < N ^ s := pow_pos hN0 s
  set A := N ^ θ * L ^ 2 with hAdef
  have hNθ : 1 ≤ N ^ θ := Real.one_le_rpow hN1 (by linarith)
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hA1 : 1 ≤ A := by
    rw [hAdef]; have : 1 ≤ L ^ 2 := by nlinarith
    nlinarith
  have hLA : L ≤ A := by
    rw [hAdef]; nlinarith
  have hsq : Real.sqrt N ≤ N ^ θ := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hN1 hθ
  have hps : Chebyshev.psi N - Chebyshev.theta N ≤ 2 * A := by
    refine (Chebyshev.psi_sub_theta_le hN1).trans ?_
    rw [← hLdef]
    have h1 : Real.sqrt N * L ≤ N ^ θ * L ^ 2 :=
      mul_le_mul hsq hL2 (by linarith) (by linarith)
    rw [hAdef]; linarith
  have hWT' : W - T ≤ N ^ s * (2 * A) := (hWT.trans (mul_le_mul_of_nonneg_left hps hNs.le))
  have hk0 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hSM : |S / φ - N ^ (s + 1) / (((s : ℝ) + 1) * φ)| ≤ N ^ s := by
    have e : S / φ - N ^ (s + 1) / (((s : ℝ) + 1) * φ) =
        (((s : ℝ) + 1) * S - N ^ (s + 1)) / (((s : ℝ) + 1) * φ) := by
      field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hk0 hφ0), div_le_iff₀ (mul_pos hk0 hφ0)]
    have hpos : 0 ≤ ((s : ℝ) + 1) * N ^ s := by positivity
    have hX : |((s : ℝ) + 1) * S - N ^ (s + 1)| ≤ ((s : ℝ) + 1) * N ^ s :=
      abs_le.2 ⟨by linarith, by linarith⟩
    refine hX.trans ?_
    have : ((s : ℝ) + 1) * N ^ s * 1 ≤ ((s : ℝ) + 1) * N ^ s * φ :=
      mul_le_mul_of_nonneg_left hφ1 hpos
    nlinarith
  have hWS : |W - S / φ| ≤ (C * A + L + (d : ℝ) / φ) * N ^ s := by
    have : C * N ^ θ * L ^ 2 = C * A := by rw [hAdef]; ring
    rw [← this]; exact hWM
  have hWS' := abs_le.1 hWS
  have hSM' := abs_le.1 hSM
  have hT0 : 0 ≤ W - T := by linarith
  have k1 : N ^ s * L ≤ N ^ s * A := mul_le_mul_of_nonneg_left hLA hNs.le
  have k2 : N ^ s * 1 ≤ N ^ s * A := mul_le_mul_of_nonneg_left hA1 hNs.le
  have goal_rhs : N ^ s * ((C + 4) * N ^ θ * L ^ 2 + (d : ℝ) / φ) =
      N ^ s * (C * A) + 4 * (N ^ s * A) + N ^ s * ((d : ℝ) / φ) := by rw [hAdef]; ring
  have e2 : (C * A + L + (d : ℝ) / φ) * N ^ s =
      N ^ s * (C * A) + N ^ s * L + N ^ s * ((d : ℝ) / φ) := by ring
  have e3 : N ^ s * (2 * A) = 2 * (N ^ s * A) := by ring
  rw [goal_rhs, abs_le]
  constructor <;> linarith

/-- A modulus not coprime to `n` catches at most one prime. -/
lemma Ssum_noncop_le (s d n : ℕ) (hc : ¬ Nat.Coprime d n) :
    Ssum s d n ≤ Real.log n * (n : ℝ) ^ s := by
  obtain ⟨q, hq, hqd, hqn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  unfold Ssum
  have hsub : (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d) ⊆ {q} := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    have hpn : p ≤ n := by omega
    have h1 : d ∣ n - p := (mod_eq_iff_dvd_sub hpn).mp hp.2.2
    have h2 : q ∣ n - p := hqd.trans h1
    have h3 : q ∣ n - (n - p) := Nat.dvd_sub hqn h2
    rw [Nat.sub_sub_self hpn] at h3
    rw [mem_singleton]
    exact ((Nat.prime_dvd_prime_iff_eq hq hp.2.1).1 h3).symm
  have hcard : (((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) ≤ 1 := by
    exact_mod_cast (card_le_card hsub).trans (card_singleton q).le
  have h0 : 0 ≤ Real.log n * (n : ℝ) ^ s := by have := Real.log_natCast_nonneg n; positivity
  calc ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d),
        Real.log p * ((n : ℝ) - p) ^ s
      ≤ ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card •
          (Real.log n * (n : ℝ) ^ s) := by
        apply sum_le_card_nsmul
        intro p hp
        rw [mem_filter, mem_range] at hp
        have hpn : p ≤ n := by omega
        have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)
        have hp0 : (p : ℝ) ≤ n := by exact_mod_cast hpn
        have h2 : (0 : ℝ) ≤ (n : ℝ) - p := by linarith
        have h3 : ((n : ℝ) - p) ^ s ≤ (n : ℝ) ^ s :=
          pow_le_pow_left₀ h2 (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]) s
        exact mul_le_mul (log_le_log_nat hpn) h3 (pow_nonneg h2 s) (Real.log_natCast_nonneg n)
    _ ≤ Real.log n * (n : ℝ) ^ s := by
        rw [nsmul_eq_mul]; nlinarith

/-- **The divisor sum against its main term**, all `d ≤ n` at once. -/
lemma head_all (s : ℕ) (hs : 2 ≤ s) {θ C : ℝ} (hθ : 1 / 2 ≤ θ) (hC : 0 ≤ C)
    (hψ : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
      |HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 2)
    (Kg : ℝ) (hKg : ∀ N : ℕ, ∑ d ∈ (Finset.range N).filter Squarefree, |gr (s + 1) d| ≤ Kg)
    {n : ℕ} (hn : 3 ≤ n) :
    |∑ d ∈ (Finset.range (n + 1)).filter Squarefree, gr (s + 1) d * Ssum s d n
      - (n : ℝ) ^ (s + 1) / (s + 1) *
        ∑ d ∈ (Finset.range (n + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
          gr (s + 1) d / (Nat.totient d : ℝ)| ≤
      (n : ℝ) ^ s * (Kg * ((C + 4) * (n : ℝ) ^ θ * Real.log n ^ 2 + Real.log n) +
        Real.exp 24) := by
  have hsplit : (n : ℝ) ^ (s + 1) / (s + 1) *
      ∑ d ∈ (Finset.range (n + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
        gr (s + 1) d / (Nat.totient d : ℝ) =
      ∑ d ∈ (Finset.range (n + 1)).filter Squarefree,
        gr (s + 1) d * (if Nat.Coprime d n then
          (n : ℝ) ^ (s + 1) / ((s + 1) * (Nat.totient d : ℝ)) else 0) := by
    rw [mul_sum]
    rw [show (Finset.range (n + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n) =
      ((Finset.range (n + 1)).filter Squarefree).filter (fun d => Nat.Coprime d n) by
        rw [filter_filter]]
    rw [sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs
    · field_simp
    · simp
  rw [hsplit, ← sum_sub_distrib]
  set X := (C + 4) * (n : ℝ) ^ θ * Real.log n ^ 2 with hX
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hX0 : 0 ≤ X := by positivity
  have hNs : 0 ≤ (n : ℝ) ^ s := by positivity
  calc |∑ d ∈ (Finset.range (n + 1)).filter Squarefree,
        (gr (s + 1) d * Ssum s d n - gr (s + 1) d * (if Nat.Coprime d n then
          (n : ℝ) ^ (s + 1) / ((s + 1) * (Nat.totient d : ℝ)) else 0))|
      ≤ ∑ d ∈ (Finset.range (n + 1)).filter Squarefree,
        (|gr (s + 1) d| * ((n : ℝ) ^ s * (X + Real.log n)) +
          |gr (s + 1) d| * ((d : ℝ) / (Nat.totient d : ℝ)) * (n : ℝ) ^ s) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
        rw [← mul_sub, abs_mul]
        rw [mem_filter, mem_range] at hd
        have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd.2.ne_zero
        have hg := abs_nonneg (gr (s + 1) d)
        have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (by omega)
        have hdφ : 0 ≤ (d : ℝ) / (Nat.totient d : ℝ) := by positivity
        have hP : 0 ≤ |gr (s + 1) d| * ((n : ℝ) ^ s * Real.log n) := by positivity
        have hP2 : 0 ≤ |gr (s + 1) d| * ((n : ℝ) ^ s * X) := by positivity
        have hP3 : 0 ≤ |gr (s + 1) d| * ((d : ℝ) / (Nat.totient d : ℝ)) * (n : ℝ) ^ s := by
          positivity
        have e2 : |gr (s + 1) d| * ((n : ℝ) ^ s * (X + Real.log n)) =
            |gr (s + 1) d| * ((n : ℝ) ^ s * X) + |gr (s + 1) d| * ((n : ℝ) ^ s * Real.log n) := by
          ring
        split_ifs with hc
        · have h := Ssum_head s hθ hC hψ hn hd1 hc
          rw [← hX] at h
          have h' := mul_le_mul_of_nonneg_left h hg
          have e : |gr (s + 1) d| * ((n : ℝ) ^ s * (X + (d : ℝ) / (Nat.totient d : ℝ))) =
              |gr (s + 1) d| * ((n : ℝ) ^ s * X) +
                |gr (s + 1) d| * ((d : ℝ) / (Nat.totient d : ℝ)) * (n : ℝ) ^ s := by ring
          linarith
        · rw [sub_zero, abs_of_nonneg (Ssum_nonneg s d n)]
          have h := Ssum_noncop_le s d n hc
          have h' := mul_le_mul_of_nonneg_left h hg
          have e : |gr (s + 1) d| * (Real.log n * (n : ℝ) ^ s) =
              |gr (s + 1) d| * ((n : ℝ) ^ s * Real.log n) := by ring
          linarith
    _ = (∑ d ∈ (Finset.range (n + 1)).filter Squarefree, |gr (s + 1) d|) *
          ((n : ℝ) ^ s * (X + Real.log n)) +
        (∑ d ∈ (Finset.range (n + 1)).filter Squarefree,
          |gr (s + 1) d| * ((d : ℝ) / (Nat.totient d : ℝ))) * (n : ℝ) ^ s := by
        rw [sum_add_distrib, sum_mul, sum_mul]
    _ ≤ Kg * ((n : ℝ) ^ s * (X + Real.log n)) + Real.exp 24 * (n : ℝ) ^ s := by
        have h1 := hKg (n + 1)
        have h2 := gr_dphi_bdd (s + 1) (by omega) (n + 1)
        have h3 : 0 ≤ (n : ℝ) ^ s * (X + Real.log n) := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_right h1 h3) (mul_le_mul_of_nonneg_right h2 hNs)
    _ = (n : ℝ) ^ s * (Kg * (X + Real.log n) + Real.exp 24) := by ring

/-! ### The error carried from `ν_{s+1}` -/

set_option maxHeartbeats 1000000 in
lemma err_quant (s : ℕ) (hs : 2 ≤ s) {e : ℝ} (he : -1 ≤ e) {B : ℕ} (IH : APow (s + 1) e B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → n % 2 = (s + 2) % 2 →
      |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
          Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p))| ≤
        K * (n : ℝ) ^ ((s : ℝ) + 1 + e) * Real.log n ^ (B + s + 1) := by
  obtain ⟨c, Kb, hc, hBK⟩ := Br_bounds (s + 1) (by omega)
  have hK : ∀ m : ℕ, 0 ≤ Br (s + 1) m ∧ Br (s + 1) m ≤ Kb :=
    fun m => ⟨hc.le.trans (hBK m).1, (hBK m).2⟩
  have hKb0 : 0 ≤ Kb := (hK 0).1.trans (hK 0).2
  have hcs : 0 ≤ 2 * Cr (s + 1) / (Nat.factorial s : ℝ) := by
    have := Cr_pos (s + 1) (by omega); positivity
  set cs := 2 * Cr (s + 1) / (Nat.factorial s : ℝ) with hcsdef
  obtain ⟨K₁, hK₁, m₀', hm₀'⟩ := IH
  set m₀ := max m₀' 1 with hm₀def
  set C₀ := ((m₀ : ℝ) + 1) ^ s * Real.log m₀ ^ (s + 1) + cs * Kb * (m₀ : ℝ) ^ s with hC₀
  have hC₀0 : 0 ≤ C₀ := by have := Real.log_natCast_nonneg m₀; positivity
  have hgen : ∀ m : ℕ, |nur (s + 1) m - Mr (s + 1) m| ≤
      ((m : ℝ) + 1) ^ s * Real.log m ^ (s + 1) + cs * Kb * (m : ℝ) ^ s := by
    intro m
    have h1 := nur_le_pow s m
    have h2 := nur_nonneg (s + 1) m
    have h3 := Mr_bounds s Kb hK hcs (le_refl m)
    rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
  have hse : 0 ≤ (s : ℝ) + e := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  set KE := Real.log 4 * K₁ + (m₀ : ℝ) * C₀ + Real.log 2 * (2 ^ s + cs * Kb) with hKE
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hKE0 : 0 ≤ KE := by
    have a1 : 0 ≤ Real.log 4 * K₁ := mul_nonneg hl4 hK₁
    have a2 : 0 ≤ (m₀ : ℝ) * C₀ := mul_nonneg (Nat.cast_nonneg _) hC₀0
    have a3 : 0 ≤ Real.log 2 * (2 ^ s + cs * Kb) :=
      mul_nonneg hl2 (add_nonneg (by positivity) (mul_nonneg hcs hKb0))
    rw [hKE]; linarith
  refine ⟨KE, hKE0, max m₀ 3, fun n hn hpar => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnm : m₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL1 := one_le_log_of_three hn3
  set L := Real.log n with hLdef
  have hL0 : 0 ≤ L := by linarith
  set V := K₁ * (n : ℝ) ^ ((s : ℝ) + e) * L ^ B with hV
  have hV0 : 0 ≤ V := by positivity
  set Big := (2 : ℝ) ^ s * (n : ℝ) ^ s * L ^ (s + 1) + cs * Kb * (n : ℝ) ^ s with hBig
  have hBig0 : 0 ≤ Big := by positivity
  set P := (Finset.range (n + 1)).filter Nat.Prime with hPdef
  have hpt : ∀ p ∈ P, Real.log p * |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤
      Real.log p * V + (if n - p < m₀ then L * C₀ else 0) +
        (if p = 2 then Real.log 2 * Big else 0) := by
    intro p hp
    rw [hPdef, mem_filter, mem_range] at hp
    have hpn : p ≤ n := by omega
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    have hlpn : Real.log p ≤ L := log_le_log_nat hpn
    have hA : 0 ≤ Real.log p * V := by positivity
    have hB : 0 ≤ (if n - p < m₀ then L * C₀ else 0) := by split_ifs <;> positivity
    have hC : 0 ≤ (if p = 2 then Real.log 2 * Big else 0) := by split_ifs <;> positivity
    by_cases h2 : p = 2
    · subst h2
      rw [if_pos rfl]
      have h := hgen (n - 2)
      have e1 : ((n - 2 : ℕ) : ℝ) + 1 ≤ 2 * (n : ℝ) := by
        have : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - 2 ≤ n)
        linarith
      have e2 : Real.log ((n - 2 : ℕ) : ℝ) ≤ L := log_le_log_nat (by omega)
      have e3 : (((n - 2 : ℕ) : ℝ) + 1) ^ s * Real.log ((n - 2 : ℕ) : ℝ) ^ (s + 1) ≤
          (2 : ℝ) ^ s * (n : ℝ) ^ s * L ^ (s + 1) := by
        have := Real.log_natCast_nonneg (n - 2)
        rw [← mul_pow]
        gcongr
      have e4 : cs * Kb * ((n - 2 : ℕ) : ℝ) ^ s ≤ cs * Kb * (n : ℝ) ^ s := by
        gcongr; exact_mod_cast (by omega : n - 2 ≤ n)
      have : |nur (s + 1) (n - 2) - Mr (s + 1) (n - 2)| ≤ Big := by linarith
      have := mul_le_mul_of_nonneg_left this hlp
      push_cast at this hA ⊢
      linarith
    have hpodd : p % 2 = 1 := (hp.2.eq_two_or_odd).resolve_left h2
    by_cases hsmall : n - p < m₀
    · rw [if_pos hsmall, if_neg h2]
      have h := hgen (n - p)
      have e1 : ((n - p : ℕ) : ℝ) + 1 ≤ (m₀ : ℝ) + 1 := by
        have : ((n - p : ℕ) : ℝ) ≤ m₀ := by exact_mod_cast hsmall.le
        linarith
      have e2 : Real.log ((n - p : ℕ) : ℝ) ≤ Real.log m₀ := log_le_log_nat hsmall.le
      have e3 : (((n - p : ℕ) : ℝ) + 1) ^ s * Real.log ((n - p : ℕ) : ℝ) ^ (s + 1) ≤
          ((m₀ : ℝ) + 1) ^ s * Real.log m₀ ^ (s + 1) := by
        have := Real.log_natCast_nonneg (n - p)
        gcongr
      have e4 : cs * Kb * ((n - p : ℕ) : ℝ) ^ s ≤ cs * Kb * (m₀ : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _)
          (by exact_mod_cast hsmall.le) s) (mul_nonneg hcs hKb0)
      have h5 : |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤ C₀ := by linarith
      have h6 : Real.log p * |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| ≤ L * C₀ :=
        mul_le_mul hlpn h5 (abs_nonneg _) (by linarith)
      linarith
    · rw [if_neg hsmall, if_neg h2]
      push_neg at hsmall
      have hparm : (n - p) % 2 = (s + 1) % 2 := by omega
      have h := hm₀' (n - p) hparm (le_trans (le_max_left _ _) hsmall)
      have hexp : (((s + 1 : ℕ) : ℝ) - 1 + e) = (s : ℝ) + e := by push_cast; ring
      rw [hexp] at h
      have hm1 : 1 ≤ n - p := le_trans (le_max_right _ _) hsmall
      have hcast : ((n - p : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - p ≤ n)
      have i1 : ((n - p : ℕ) : ℝ) ^ ((s : ℝ) + e) ≤ (n : ℝ) ^ ((s : ℝ) + e) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcast hse
      have i2 : Real.log ((n - p : ℕ) : ℝ) ^ B ≤ L ^ B :=
        pow_le_pow_left₀ (Real.log_natCast_nonneg _) (log_le_log_nat (by omega)) B
      have i3 : K₁ * ((n - p : ℕ) : ℝ) ^ ((s : ℝ) + e) * Real.log ((n - p : ℕ) : ℝ) ^ B ≤ V := by
        rw [hV]
        have := Real.log_natCast_nonneg (n - p)
        gcongr
      have := mul_le_mul_of_nonneg_left (h.trans i3) hlp
      linarith
  -- sum the pointwise bounds
  have hsum1 : ∑ p ∈ P, Real.log p * V ≤ Real.log 4 * n * V := by
    rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (theta_le n) hV0
  have hsum2 : ∑ p ∈ P, (if n - p < m₀ then L * C₀ else 0) ≤ (m₀ : ℝ) * (L * C₀) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hsub : P.filter (fun p => n - p < m₀) ⊆ (range m₀).image (fun i => n - i) := by
      intro p hp
      rw [hPdef, mem_filter, mem_filter, mem_range] at hp
      obtain ⟨⟨hp1, _⟩, hp2⟩ := hp
      rw [mem_image]
      exact ⟨n - p, mem_range.2 hp2, by omega⟩
    have hc2 : ((P.filter (fun p => n - p < m₀)).card : ℝ) ≤ m₀ := by
      exact_mod_cast (card_le_card hsub).trans (card_image_le.trans (card_range m₀).le)
    exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  have hsum3 : ∑ p ∈ P, (if p = 2 then Real.log 2 * Big else 0) ≤ Real.log 2 * Big := by
    rw [sum_ite_eq']; split_ifs
    · exact le_rfl
    · positivity
  have htot : |∑ p ∈ P, Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p))| ≤
      Real.log 4 * n * V + (m₀ : ℝ) * (L * C₀) + Real.log 2 * Big := by
    calc |∑ p ∈ P, Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p))|
        ≤ ∑ p ∈ P, Real.log p * |nur (s + 1) (n - p) - Mr (s + 1) (n - p)| := by
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun p hp => ?_))
          rw [hPdef, mem_filter] at hp
          rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))]
      _ ≤ ∑ p ∈ P, (Real.log p * V + (if n - p < m₀ then L * C₀ else 0) +
            (if p = 2 then Real.log 2 * Big else 0)) := sum_le_sum hpt
      _ = ∑ p ∈ P, Real.log p * V + ∑ p ∈ P, (if n - p < m₀ then L * C₀ else 0) +
            ∑ p ∈ P, (if p = 2 then Real.log 2 * Big else 0) := by
          rw [sum_add_distrib, sum_add_distrib]
      _ ≤ _ := by linarith
  refine htot.trans ?_
  -- compare with `n^{s+1+e} L^{B+s+1}`
  set Y := (n : ℝ) ^ ((s : ℝ) + 1 + e) with hY
  set Z := L ^ (B + s + 1) with hZ
  have hY1 : 1 ≤ Y := Real.one_le_rpow hn1 (by linarith)
  have hZ1 : 1 ≤ Z := one_le_pow₀ hL1
  have hnY : (n : ℝ) ^ ((s : ℝ) + e) * n = Y := by
    rw [hY, ← Real.rpow_add_one hn0.ne']; congr 1; ring
  have hBZ : L ^ B ≤ Z := log_pow_mono hn3 (by omega)
  have hLZ : L ≤ Z := by
    have := log_pow_mono hn3 (show 1 ≤ B + s + 1 by omega); simpa using this
  have hsZ : L ^ (s + 1) ≤ Z := log_pow_mono hn3 (by omega)
  have hnsY : (n : ℝ) ^ s ≤ Y := npow_le_rpow (by omega) (by push_cast; linarith)
  have hY0 : 0 ≤ Y := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have p1 : Real.log 4 * n * V ≤ Real.log 4 * K₁ * (Y * Z) := by
    have e : Real.log 4 * n * V = Real.log 4 * K₁ * ((n : ℝ) ^ ((s : ℝ) + e) * n) * L ^ B := by
      rw [hV]; ring
    rw [e, hnY]
    have := mul_le_mul_of_nonneg_left hBZ (by positivity : (0 : ℝ) ≤ Real.log 4 * K₁ * Y)
    linarith
  have p2 : (m₀ : ℝ) * (L * C₀) ≤ (m₀ : ℝ) * C₀ * (Y * Z) := by
    have hZY := mul_le_mul_of_nonneg_right hY1 hZ0
    have : L ≤ Y * Z := by linarith only [hZY, hLZ]
    have h := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (m₀ : ℝ) * C₀)
    linarith only [h]
  have p3 : Real.log 2 * Big ≤ Real.log 2 * (2 ^ s + cs * Kb) * (Y * Z) := by
    have q1 : (n : ℝ) ^ s * L ^ (s + 1) ≤ Y * Z := mul_le_mul hnsY hsZ (by positivity) hY0
    have hYZ := mul_le_mul_of_nonneg_left hZ1 hY0
    have q2 : (n : ℝ) ^ s ≤ Y * Z := by linarith only [hYZ, hnsY]
    have e : Big = (2 : ℝ) ^ s * ((n : ℝ) ^ s * L ^ (s + 1)) + cs * Kb * (n : ℝ) ^ s := by
      rw [hBig]; ring
    rw [e, mul_assoc (Real.log 2)]
    apply mul_le_mul_of_nonneg_left _ hl2
    have h1 := mul_le_mul_of_nonneg_left q1 (by positivity : (0 : ℝ) ≤ 2 ^ s)
    have h2 := mul_le_mul_of_nonneg_left q2 (by positivity : (0 : ℝ) ≤ cs * Kb)
    linarith only [h1, h2]
  have e : KE * Y * Z = Real.log 4 * K₁ * (Y * Z) + (m₀ : ℝ) * C₀ * (Y * Z) +
      Real.log 2 * (2 ^ s + cs * Kb) * (Y * Z) := by rw [hKE]; ring
  rw [e]
  linarith only [htot, p1, p2, p3]

/-! ### The induction step -/

set_option maxHeartbeats 1000000 in
/-- **The step**: `APow (s+1) e B` gives `APow (s+2) e (B+s+1)` on `PsiPowerLog θ`,
`1/2 ≤ θ`, `θ - 1 ≤ e`. -/
theorem apow_step (s : ℕ) (hs : 2 ≤ s) {θ e : ℝ} (hθ : 1 / 2 ≤ θ) (hθe : θ - 1 ≤ e)
    (hψ : PsiPowerLog θ) {B : ℕ} (IH : APow (s + 1) e B) : APow (s + 2) e (B + s + 1) := by
  have he : -1 ≤ e := by linarith
  obtain ⟨C, hC, hψ'⟩ := hψ
  obtain ⟨KE, hKE, n₁, hErr⟩ := err_quant s hs he IH
  obtain ⟨Kg, hKg⟩ := gr_sum_bdd (s + 1) (by omega)
  have hKg0 : 0 ≤ Kg := (sum_nonneg fun _ _ => abs_nonneg _).trans (hKg 0)
  have hC1 := Cr_pos (s + 1) (by omega)
  have hC2 := Cr_pos (s + 2) (by omega)
  have hcs : 0 < 2 * Cr (s + 1) / (Nat.factorial s : ℝ) := by positivity
  set cs := 2 * Cr (s + 1) / (Nat.factorial s : ℝ) with hcsdef
  have he24 : 0 ≤ Real.exp 24 := (Real.exp_pos _).le
  refine ⟨cs * (Kg * (C + 5) + Real.exp 24) + cs * Real.exp 24 + KE, by positivity,
    max n₁ 3, fun n hpar hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hErr := hErr n (le_trans (le_max_left _ _) hn) hpar
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL1 := one_le_log_of_three hn3
  -- the main term
  have hMr : Mr (s + 2) n = cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
      (Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n) := by
    rw [Mr, show s + 2 - 1 = s + 1 by omega, hcsdef, Nat.factorial_succ]
    push_cast
    field_simp
  set Hall := ∑ d ∈ (Finset.range (n + 1)).filter Squarefree, gr (s + 1) d * Ssum s d n
    with hHall
  set Eu := ∑ d ∈ (Finset.range (n + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d n),
    gr (s + 1) d / (Nat.totient d : ℝ) with hEu
  set Er := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
    Real.log p * (nur (s + 1) (n - p) - Mr (s + 1) (n - p)) with hEr
  have hdec : nur (s + 2) n = cs * Hall + Er := by
    rw [show s + 2 = (s + 1) + 1 by omega, nur_succ]
    have : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p * nur (s + 1) (n - p) =
        ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p * Mr (s + 1) (n - p) + Er := by
      rw [hEr, ← sum_add_distrib]
      exact sum_congr rfl fun p _ => by ring
    rw [this, main_expand s n (by omega)]
  have key : nur (s + 2) n - Mr (s + 2) n =
      cs * (Hall - (n : ℝ) ^ (s + 1) / (s + 1) * Eu) +
      cs * ((n : ℝ) ^ (s + 1) / (s + 1)) * (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n) +
      Er := by
    rw [hdec, hMr]; ring
  -- the head
  have b1 := head_all s hs hθ hC hψ' Kg hKg hn3
  rw [← hHall, ← hEu] at b1
  -- the Euler identity with rate
  have hEuHR : Eu = ∑ d ∈ (Icc 1 n).filter Squarefree, HR (s + 1) n d := by
    rw [hEu]; exact sum_eq_sum_HR (s + 1) n n
  have b2 := euler_rate (s + 1) (by omega) n (by omega)
  rw [← hEuHR] at b2
  -- exponents
  have hexp : (((s + 2 : ℕ) : ℝ) - 1 + e) = (s : ℝ) + 1 + e := by push_cast; ring
  rw [hexp]
  set L := Real.log n with hLdef
  set Y := (n : ℝ) ^ ((s : ℝ) + 1 + e) with hY
  set Z := L ^ (B + s + 1) with hZ
  have hY1 : 1 ≤ Y := Real.one_le_rpow hn1 (by linarith)
  have hZ1 : 1 ≤ Z := one_le_pow₀ hL1
  have hY0 : 0 ≤ Y := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hNs : 0 < (n : ℝ) ^ s := by positivity
  have hNθ : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hn1 (by linarith)
  have hsθ : (n : ℝ) ^ s * (n : ℝ) ^ θ ≤ Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hsY : (n : ℝ) ^ s ≤ Y := by
    have := mul_le_mul_of_nonneg_left hNθ hNs.le
    linarith only [this, hsθ]
  have hL2Z : L ^ 2 ≤ Z := log_pow_mono hn3 (by omega)
  have hLL2 : L ≤ L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hL1 (by linarith : (0 : ℝ) ≤ L)
    linarith only [this]
  -- bound 1
  have inner : |Hall - (n : ℝ) ^ (s + 1) / (s + 1) * Eu| ≤
      (Kg * (C + 5) + Real.exp 24) * (Y * Z) := by
    refine b1.trans ?_
    have q1 : (n : ℝ) ^ s * (n : ℝ) ^ θ * L ^ 2 ≤ Y * Z :=
      mul_le_mul hsθ hL2Z (by positivity) hY0
    have q2 : (n : ℝ) ^ s * L ≤ Y * Z := mul_le_mul hsY (hLL2.trans hL2Z) (by linarith) hY0
    have hYZ := mul_le_mul_of_nonneg_left hZ1 hY0
    have q3 : (n : ℝ) ^ s ≤ Y * Z := by linarith only [hYZ, hsY]
    have r1 := mul_le_mul_of_nonneg_left q1 (by positivity : (0 : ℝ) ≤ Kg * (C + 4))
    have r2 := mul_le_mul_of_nonneg_left q2 hKg0
    have r3 := mul_le_mul_of_nonneg_left q3 he24
    linarith only [r1, r2, r3]
  have B1 : |cs * (Hall - (n : ℝ) ^ (s + 1) / (s + 1) * Eu)| ≤
      cs * (Kg * (C + 5) + Real.exp 24) * (Y * Z) := by
    rw [abs_mul, abs_of_pos hcs]
    have := mul_le_mul_of_nonneg_left inner hcs.le
    exact this.trans_eq (by ring)
  -- bound 2
  have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  have hs0 : 0 < Real.sqrt n := by linarith
  have hk1 : (1 : ℝ) ≤ (s : ℝ) + 1 := by have := (Nat.cast_nonneg s : (0 : ℝ) ≤ s); linarith
  have hrat : (n : ℝ) ^ (s + 1) / (s + 1) * (Real.exp 24 / ((n : ℝ) * Real.sqrt n)) ≤
      Real.exp 24 * (Y * Z) := by
    have a1 : (n : ℝ) ^ (s + 1) / (s + 1) ≤ (n : ℝ) ^ (s + 1) := div_le_self (by positivity) hk1
    have a2 : (n : ℝ) ^ (s + 1) * (Real.exp 24 / ((n : ℝ) * Real.sqrt n)) =
        Real.exp 24 * ((n : ℝ) ^ s / Real.sqrt n) := by
      have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
      have hs0' : Real.sqrt n ≠ 0 := hs0.ne'
      rw [pow_succ]; field_simp
    have a3 : (n : ℝ) ^ s / Real.sqrt n ≤ (n : ℝ) ^ s := div_le_self hNs.le hsq
    have hYZ := mul_le_mul_of_nonneg_left hZ1 hY0
    have a4 : (n : ℝ) ^ s ≤ Y * Z := by linarith only [hYZ, hsY]
    have a5 : 0 ≤ Real.exp 24 / ((n : ℝ) * Real.sqrt n) := by positivity
    have b5 := mul_le_mul_of_nonneg_right a1 a5
    have b6 := mul_le_mul_of_nonneg_left (a3.trans a4) he24
    linarith only [b5, b6, a2]
  have B2 : |cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
      (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n)| ≤ cs * Real.exp 24 * (Y * Z) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left b2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (s + 1) / (s + 1))
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hrat) hcs.le
    linarith only [h2]
  rw [key]
  have t1 := abs_add_le (cs * (Hall - (n : ℝ) ^ (s + 1) / (s + 1) * Eu) +
      cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
        (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n)) Er
  have t2 := abs_add_le (cs * (Hall - (n : ℝ) ^ (s + 1) / (s + 1) * Eu))
      (cs * ((n : ℝ) ^ (s + 1) / (s + 1)) *
        (Eu - Cr (s + 1 + 1) / Cr (s + 1) * Br (s + 1 + 1) n))
  have e : (cs * (Kg * (C + 5) + Real.exp 24) + cs * Real.exp 24 + KE) * Y * Z =
      cs * (Kg * (C + 5) + Real.exp 24) * (Y * Z) + cs * Real.exp 24 * (Y * Z) + KE * Y * Z := by
    ring
  rw [e]
  linarith only [t1, t2, B1, B2, hErr]

/-! ### The base case and the induction -/

/-- The base `r = 3` from U-1453's printed bound, with `Mr 3 n = n²/2 · 𝔖₃(n)` for odd `n`. -/
theorem apow_three_of_bound {Θ : ℝ} (h : printedA3Bound Θ) : ∃ B : ℕ, APow 3 (Θ - 3 / 4) B := by
  obtain ⟨B, hB0, C, n₀, h⟩ := h
  refine ⟨⌈B⌉₊, max C 0, le_max_right _ _, max n₀ 3, fun n hpar hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hodd : Odd n := Nat.odd_iff.mpr (by simpa using hpar)
  have hL := one_le_log_of_three hn3
  have hm := h n (le_trans (le_max_left _ _) hn)
  have eM : Mr 3 n = (n : ℝ) ^ 2 / 2 * sing3 n := by
    rw [sing3_odd hodd, ← Cr3_eq, ← Br3_eq n hodd]
    simp only [Mr, show (3 : ℕ) - 1 = 2 from rfl, Nat.factorial_two]
    push_cast
    ring
  have hexp : ((3 : ℕ) : ℝ) - 1 + (Θ - 3 / 4) = 2 + (Θ - 3 / 4) := by norm_num
  rw [eM, hexp]
  have hLB : Real.log n ^ B ≤ Real.log n ^ ⌈B⌉₊ := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil B)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hX : 0 ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) := Real.rpow_nonneg hn0 _
  have hLB0 : 0 ≤ Real.log n ^ B := Real.rpow_nonneg (by linarith) _
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      ≤ C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := hm
    _ ≤ max C 0 * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ ⌈B⌉₊ := by
        gcongr

/-- **From a base `r = 3` to every `r ≥ 3`** by the Theorem B recursion. -/
theorem apow_all {θ e : ℝ} (hθ : 1 / 2 ≤ θ) (hθe : θ - 1 ≤ e) (hψ : PsiPowerLog θ)
    (base : ∃ B : ℕ, APow 3 e B) : ∀ r : ℕ, 3 ≤ r → ∃ B : ℕ, APow r e B := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact base
  | succ r hr ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    exact ⟨B + s + 1, apow_step s (by omega) hθ hθe hψ hB⟩

/-! ### The printed form with `S_r`, on an open lab target -/

/-- **Open lab target, NOT proved**: the Euler product of the printed singular series,
`S_r(n) = 2 C_r Br r n` for `n ≡ r mod 2` and `S_r(n) = 0` otherwise, `r ≥ 3`. Proved in the lab
for `r = 3` only, `U1438Sing.sing3_odd` and `sing3_even`. -/
def SingRProduct : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n : ℕ,
    (n % 2 = r % 2 → singR r n = 2 * Cr r * Br r n) ∧ (n % 2 ≠ r % 2 → singR r n = 0)

/-- `SingRProduct` holds at `r = 3`, from U-1438. -/
theorem singRProduct_three (n : ℕ) :
    (n % 2 = 3 % 2 → singR 3 n = 2 * Cr 3 * Br 3 n) ∧ (n % 2 ≠ 3 % 2 → singR 3 n = 0) := by
  rw [singR_three]
  constructor
  · intro h
    have hodd : Odd n := Nat.odd_iff.mpr (by simpa using h)
    rw [sing3_odd hodd, Cr3_eq, Br3_eq n hodd]
  · intro h
    have hev : Even n := Nat.even_iff.mpr (by omega)
    exact sing3_even hev

/-- Like parity: with `SingRProduct`, `Mr r n` is the printed main term `n^{r-1}/(r-1)! S_r(n)`. -/
theorem Mr_eq_printed (hS : SingRProduct) {r n : ℕ} (hr : 3 ≤ r) (h : n % 2 = r % 2) :
    Mr r n = (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n := by
  rw [(hS r hr n).1 h, Mr]; ring

/-- `APow` is monotone in the power of `log`. -/
theorem apow_mono {r : ℕ} {e : ℝ} {B B' : ℕ} (h : B ≤ B') (hA : APow r e B) : APow r e B' := by
  obtain ⟨K, hK, n₀, hn⟩ := hA
  refine ⟨K, hK, max n₀ 3, fun n hpar hn' => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn'
  refine (hn n hpar (le_trans (le_max_left _ _) hn')).trans ?_
  have := log_pow_mono hn3 h
  have h0 : 0 ≤ K * (n : ℝ) ^ ((r : ℝ) - 1 + e) := by positivity
  exact mul_le_mul_of_nonneg_left this h0

/-- Vacuity: the hypotheses of `apow_step` are jointly satisfiable in form, `θ = 1`, `e = 0`,
`PsiPowerLog 1` from Chebyshev. -/
theorem step_hyps_nonvacuous : PsiPowerLog 1 ∧ (1 / 2 : ℝ) ≤ 1 ∧ (1 : ℝ) - 1 ≤ 0 :=
  ⟨psiPowerLog_one, by norm_num, by norm_num⟩

end LeanLab.HardyLittlewood1923.U1463
