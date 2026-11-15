module

public import LeanLab.PNTPort.BVMax.Grid

/-!
# Bombieri-Vinogradov for `θ` and `π`, with the maximum over `y ≤ x`

Lab proof, unit U-5301, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

* `thetaAP y q a = Σ_{p ≤ y, p ≡ a (q)} log p`, `piAP y q a = #{p ≤ y : p ≡ a (q)}`,
  `liD y = Σ_{2 ≤ n ≤ y} 1/log n`, the discrete logarithmic integral; the `n = 1` term of the
  sum defining `liD` is `1/log 1 = 1/0 = 0` in Lean.
* `bvTheta_of`: `BombieriVinogradovMax → BVTheta`, `Σ_q max_{y ≤ x} max_a |θ(y; q, a) - y/φ(q)|
  ≪ x/(log x)^A`, by `ψ - θ ≤ 2√x log x` from Mathlib.
* `abel_identity`, `abel_bound`: discrete partial summation; `π(N; q, a) - liD(N)/φ(q)` is at most
  `1/log 2` times the largest `|θ(n; q, a) - (n - 1)/φ(q)|` over `2 ≤ n ≤ N`.
* `bvPi_of`: `BVTheta → BVPi`, `Σ_q max_{y ≤ x} max_a |π(y; q, a) - liD(y)/φ(q)| ≪ x/(log x)^A`,
  the level of distribution `1/2` for the primes in the form sieve papers cite.
* `bvTheta`, `bvPi`: unconditional, in `PrimesUncond.lean`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.HeathBrown1985 (psi)

/-- `θ(N; q, a)`, natural argument. -/
noncomputable def thetaN (N q a : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n % q = a % q ∧ n.Prime), Real.log n

/-- `π(N; q, a)`, natural argument. -/
noncomputable def piN (N q a : ℕ) : ℝ :=
  (((Icc 1 N).filter (fun n => n % q = a % q ∧ n.Prime)).card : ℝ)

/-- `Σ_{2 ≤ n ≤ N} 1/log n`; the `n = 1` term is `1/log 1 = 0`. -/
noncomputable def liN (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, 1 / Real.log n

/-- `θ(y; q, a) = Σ_{p ≤ y, p ≡ a mod q} log p`. -/
noncomputable def thetaAP (y : ℝ) (q a : ℕ) : ℝ := thetaN ⌊y⌋₊ q a

/-- `π(y; q, a) = #{p ≤ y : p prime, p ≡ a mod q}`. -/
noncomputable def piAP (y : ℝ) (q a : ℕ) : ℝ := piN ⌊y⌋₊ q a

/-- `liD(y) = Σ_{2 ≤ n ≤ y} 1/log n`. -/
noncomputable def liD (y : ℝ) : ℝ := liN ⌊y⌋₊

/-- Bombieri-Vinogradov for `θ`, classical form with the maximum over `y ≤ x`. -/
def BVTheta : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |thetaAP (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A

/-- Bombieri-Vinogradov for `π` against `liD`, classical form with the maximum over `y ≤ x`. -/
def BVPi : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |piAP (y q) q (a q) - liD (y q) / q.totient| ≤ K * x / Real.log x ^ A

/-- Small `x`: a sum over `q ≤ √x/(log x)^B` of terms at most `3x(log x + 1)` is `≤ T x/(log x)^A`
for `2 ≤ x ≤ X₁`. -/
lemma small_x_bound (A B X1 : ℝ) (hA : 0 < A) (hB : 0 < B) (hX1 : 2 ≤ X1) :
    ∃ T : ℝ, ∀ x : ℝ, 2 ≤ x → x ≤ X1 → ∀ F : ℕ → ℝ, (∀ q, 1 ≤ q → 0 ≤ F q) →
      (∀ q, 1 ≤ q → F q ≤ 3 * x * (Real.log x + 1)) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊, F q ≤ T * x / Real.log x ^ A := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2B : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hlog2 B
  refine ⟨X1 / Real.log 2 ^ B * (3 * (Real.log X1 + 1)) * Real.log X1 ^ A, ?_⟩
  intro x hx hxX F hF0 hF
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hlog2L : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hLX : Real.log x ≤ Real.log X1 := Real.log_le_log hx0 hxX
  have hsum := sum_le_card_nsmul _ _ _ (fun q (hq : q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊) =>
    hF q (mem_Icc.mp hq).1)
  rw [nsmul_eq_mul, Nat.card_Icc, add_tsub_cancel_right] at hsum
  have hLB : Real.log 2 ^ B ≤ Real.log x ^ B := Real.rpow_le_rpow hlog2.le hlog2L hB.le
  have hQ : (⌊Real.sqrt x / Real.log x ^ B⌋₊ : ℝ) ≤ x / Real.log 2 ^ B := by
    refine (Nat.floor_le (by positivity)).trans ?_
    calc Real.sqrt x / Real.log x ^ B ≤ x / Real.log x ^ B :=
          div_le_div_of_nonneg_right (sqrt_le_self' (by linarith)) (by positivity)
      _ ≤ x / Real.log 2 ^ B := div_le_div_of_nonneg_left hx0.le hl2B hLB
  have hW : 0 ≤ 3 * x * (Real.log x + 1) := mul_nonneg (by positivity) (by linarith)
  have hLAX : Real.log x ^ A ≤ Real.log X1 ^ A := Real.rpow_le_rpow hL0.le hLX hA.le
  calc _ ≤ _ := hsum
    _ ≤ x / Real.log 2 ^ B * (3 * x * (Real.log x + 1)) := mul_le_mul_of_nonneg_right hQ hW
    _ ≤ X1 / Real.log 2 ^ B * (3 * (Real.log X1 + 1)) * Real.log X1 ^ A * x /
          Real.log x ^ A := by
        rw [le_div_iff₀ hLA0]
        have h1 : x / Real.log 2 ^ B ≤ X1 / Real.log 2 ^ B :=
          div_le_div_of_nonneg_right hxX hl2B.le
        have h2 : 3 * (Real.log x + 1) ≤ 3 * (Real.log X1 + 1) := by linarith
        have e : x / Real.log 2 ^ B * (3 * x * (Real.log x + 1)) * Real.log x ^ A =
            (x / Real.log 2 ^ B) * (3 * (Real.log x + 1)) * Real.log x ^ A * x := by ring
        rw [e]
        apply mul_le_mul_of_nonneg_right _ hx0.le
        have hlX : 0 ≤ Real.log X1 := Real.log_nonneg (by linarith)
        apply mul_le_mul _ hLAX hLA0.le (mul_nonneg (by positivity) (by linarith))
        exact mul_le_mul h1 h2 (by linarith) (by positivity)

/-- `0 ≤ ψ(y; q, a) - θ(y; q, a) ≤ 2√x log x` for `0 ≤ y ≤ x`, `x ≥ 1`. -/
lemma psi_sub_thetaAP {x y : ℝ} (q a : ℕ) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : 1 ≤ x) :
    0 ≤ psi y q a - thetaAP y q a ∧ psi y q a - thetaAP y q a ≤ 2 * Real.sqrt x * Real.log x := by
  have e : psi y q a - thetaAP y q a =
      ∑ n ∈ Icc 1 ⌊y⌋₊, (if n % q = a % q ∧ ¬ n.Prime then Λ n else 0) := by
    unfold psi thetaAP thetaN
    rw [sum_filter, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl (fun n _ => ?_)
    by_cases h1 : n % q = a % q <;> by_cases h2 : n.Prime <;>
      simp [h1, h2, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [e]
  refine ⟨sum_nonneg (fun n _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]), ?_⟩
  have h1 : ∑ n ∈ Icc 1 ⌊y⌋₊, (if n % q = a % q ∧ ¬ n.Prime then Λ n else 0) ≤
      ∑ n ∈ Icc 1 ⌊y⌋₊, (if ¬ n.Prime then Λ n else 0) := by
    apply sum_le_sum; intro n _
    by_cases h1 : n % q = a % q <;> by_cases h2 : n.Prime <;>
      simp [h1, h2, ArithmeticFunction.vonMangoldt_nonneg]
  have h2 : ∑ n ∈ Icc 1 ⌊y⌋₊, (if ¬ n.Prime then Λ n else 0) =
      Chebyshev.psi y - Chebyshev.theta y := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter, ← Icc_add_one_left_eq_Ioc, zero_add]
  rw [h2] at h1
  refine h1.trans ?_
  rcases lt_or_ge y 1 with hy1 | hy1
  · have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy1
    have hp : Chebyshev.psi y = 0 := by simp [Chebyshev.psi, this]
    have ht : Chebyshev.theta y = 0 := by simp [Chebyshev.theta, this]
    rw [hp, ht, sub_zero]
    have : 0 ≤ Real.log x := Real.log_nonneg hx
    positivity
  · refine (Chebyshev.psi_sub_theta_le hy1).trans ?_
    have h3 : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
    have h4 : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
    have h5 : 0 ≤ Real.log y := Real.log_nonneg hy1
    have : Real.sqrt y * Real.log y ≤ Real.sqrt x * Real.log x :=
      mul_le_mul h3 h4 h5 (Real.sqrt_nonneg _)
    linarith

/-- `0 ≤ θ(y; q, a) ≤ ψ(y; q, a) ≤ (y/q + 2) log x`. -/
lemma thetaAP_bounds {x y : ℝ} (q a : ℕ) (hq : 0 < q) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : 1 ≤ x) :
    0 ≤ thetaAP y q a ∧ thetaAP y q a ≤ (y / q + 2) * Real.log x := by
  have h := psi_sub_bounds q a hq le_rfl hy hyx hx
  have h0 : psi 0 q a = 0 := by simp [psi]
  rw [h0, sub_zero, sub_zero] at h
  have ht := psi_sub_thetaAP q a hy hyx hx
  refine ⟨?_, by linarith [ht.1, h.2]⟩
  unfold thetaAP thetaN
  exact sum_nonneg (fun n hn => Real.log_natCast_nonneg n)

theorem bvTheta_of (hBV : BombieriVinogradovMax) : BVTheta := by
  intro A hA
  obtain ⟨B0, hB0, K0, hK0⟩ := hBV A hA
  set B := B0 + A + 1 with hBdef
  have hB : 0 < B := by linarith
  obtain ⟨T, hT⟩ := small_x_bound A B (Real.exp 1) hA hB
    (by have := Real.add_one_le_exp (1 : ℝ); linarith)
  refine ⟨B, hB, max (K0 + 2) T, ?_⟩
  intro x hx a ha y hy
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hxL : 0 ≤ x / Real.log x ^ A := by positivity
  by_cases hxe : Real.exp 1 ≤ x
  · set L := Real.log x with hLdef
    have hL1 : 1 ≤ L := by
      rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hBB : L ^ B0 ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hsub : Icc 1 ⌊Real.sqrt x / L ^ B⌋₊ ⊆ Icc 1 ⌊Real.sqrt x / L ^ B0⌋₊ := by
      apply Icc_subset_Icc_right; apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hsx0.le (Real.rpow_pos_of_pos hL0 _) hBB
    have hterm : ∀ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊,
        |thetaAP (y q) q (a q) - y q / q.totient| ≤
          |psi (y q) q (a q) - y q / q.totient| + 2 * Real.sqrt x * L := by
      intro q _
      have h := psi_sub_thetaAP q (a q) (hy q).1 (hy q).2 (by linarith)
      have := abs_sub_abs_le_abs_sub (thetaAP (y q) q (a q) - y q / q.totient)
        (psi (y q) q (a q) - y q / q.totient)
      have e : thetaAP (y q) q (a q) - y q / q.totient - (psi (y q) q (a q) - y q / q.totient) =
        -(psi (y q) q (a q) - thetaAP (y q) q (a q)) := by ring
      rw [e, abs_neg, abs_of_nonneg h.1] at this
      linarith [h.2]
    have hs1 := sum_le_sum hterm
    rw [sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hs1
    have hs2 : ∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, |psi (y q) q (a q) - y q / q.totient| ≤
        K0 * x / L ^ A :=
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans
        (hK0 x hx a ha y hy)
    have hQ : (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) ≤ Real.sqrt x / L ^ B :=
      Nat.floor_le (by positivity)
    have hs3 : (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) * (2 * Real.sqrt x * L) ≤ 2 * x / L ^ A := by
      have hLB : L ^ B = L ^ (B0 + A) * L := by
        rw [hBdef, Real.rpow_add hL0, Real.rpow_one]
      have hLA : L ^ A ≤ L ^ (B0 + A) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have hLAp : 0 < L ^ (B0 + A) := Real.rpow_pos_of_pos hL0 _
      calc (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) * (2 * Real.sqrt x * L)
          ≤ Real.sqrt x / L ^ B * (2 * Real.sqrt x * L) :=
            mul_le_mul_of_nonneg_right hQ (by positivity)
        _ = 2 * x / L ^ (B0 + A) := by
            rw [hLB]; field_simp; rw [Real.sq_sqrt hx0.le]
        _ ≤ 2 * x / L ^ A := div_le_div_of_nonneg_left (by positivity) hLA0 hLA
    calc _ ≤ _ := hs1
      _ ≤ K0 * x / L ^ A + 2 * x / L ^ A := add_le_add hs2 hs3
      _ = (K0 + 2) * x / L ^ A := by ring
      _ ≤ max (K0 + 2) T * x / L ^ A := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxL
  · push Not at hxe
    refine (hT x hx hxe.le (fun q => |thetaAP (y q) q (a q) - y q / q.totient|)
      (fun _ _ => abs_nonneg _) ?_).trans ?_
    · intro q hq
      · have hb := thetaAP_bounds q (a q) hq (hy q).1 (hy q).2 (by linarith)
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
        have e1 : y q / q ≤ x := (div_le_self (hy q).1 hq1).trans (hy q).2
        have e2 : y q / q.totient ≤ x := (div_le_self (hy q).1 hφ1).trans (hy q).2
        have e3 : 0 ≤ y q / q.totient := div_nonneg (hy q).1 (by linarith)
        rw [abs_le]; constructor <;> nlinarith
    · rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxL

section Abel

variable (q a : ℕ)

/-- `c(n) = 1_{n ≡ a (q), n prime} log n - 1_{n ≥ 2}/φ(q)`. -/
noncomputable def cc (n : ℕ) : ℝ :=
  (if n % q = a % q ∧ n.Prime then Real.log n else 0) -
    (if 2 ≤ n then 1 / (q.totient : ℝ) else 0)

/-- `C(N) = Σ_{n ≤ N} c(n) = θ(N; q, a) - (N - 1)/φ(q)`. -/
noncomputable def CC (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, cc q a n

/-- `Σ_{n ≤ N} c(n)/log n = π(N; q, a) - liD(N)/φ(q)`. -/
noncomputable def EE (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, cc q a n / Real.log n

lemma cc_one : cc q a 1 = 0 := by simp [cc, Nat.not_prime_one]

lemma CC_eq (N : ℕ) (hN : 1 ≤ N) : CC q a N = thetaN N q a - ((N : ℝ) - 1) / q.totient := by
  unfold CC cc thetaN
  rw [sum_sub_distrib, ← sum_filter, ← sum_filter, sum_const, nsmul_eq_mul]
  have hf : (Icc 1 N).filter (fun n => 2 ≤ n) = Icc 2 N := by
    ext n; simp only [mem_filter, mem_Icc]; omega
  rw [hf, Nat.card_Icc, Nat.cast_sub (by omega)]
  push_cast
  ring

lemma EE_eq (N : ℕ) : EE q a N = piN N q a - liN N / q.totient := by
  unfold EE piN liN
  have hterm : ∀ n ∈ Icc 1 N, cc q a n / Real.log n =
      (if n % q = a % q ∧ n.Prime then 1 else 0) - (1 / Real.log n) / q.totient := by
    intro n hn
    rw [mem_Icc] at hn
    rcases Nat.eq_or_lt_of_le hn.1 with h1 | h2
    · subst h1; simp [cc, Nat.not_prime_one]
    · have hn2 : 2 ≤ n := h2
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast h2)
      unfold cc
      rw [if_pos hn2]
      split_ifs <;> field_simp <;> ring
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_boole, ← sum_div]

lemma EE_small (N : ℕ) (hN : N < 2) : EE q a N = 0 := by
  unfold EE
  rcases Nat.lt_succ_iff.mp hN |>.lt_or_eq with h0 | h1
  · have : N = 0 := by omega
    subst this; simp
  · subst h1; simp [cc_one]

lemma abel_identity (N : ℕ) (hN : 2 ≤ N) :
    EE q a N = CC q a N / Real.log N +
      ∑ n ∈ Ico 2 N, CC q a n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
  induction N, hN using Nat.le_induction with
  | base =>
      have h12 : Icc 1 2 = {1, 2} := by decide
      simp [EE, CC, h12, cc_one]
  | succ N hN ih =>
      have h1 : EE q a (N + 1) = EE q a N + cc q a (N + 1) / Real.log ((N : ℝ) + 1) := by
        unfold EE; rw [sum_Icc_succ_top (by omega)]; push_cast; ring
      have h2 : CC q a (N + 1) = CC q a N + cc q a (N + 1) := by
        unfold CC; rw [sum_Icc_succ_top (by omega)]
      rw [h1, h2, ih, sum_Ico_succ_top hN]
      push_cast
      ring

lemma tele (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Ico 2 N, (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
      1 / Real.log 2 - 1 / Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [sum_Ico_succ_top hN, ih]; push_cast; ring

lemma abel_bound (N : ℕ) (hN : 2 ≤ N) (M : ℝ) (hM : ∀ n ∈ Icc 2 N, |CC q a n| ≤ M) :
    |EE q a N| ≤ M / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 2 (mem_Icc.mpr ⟨le_rfl, hN⟩))
  have hdiff : ∀ n ∈ Ico 2 N, 0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    have hle : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hl hle
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [abel_identity q a N hN]
  calc |CC q a N / Real.log N + ∑ n ∈ Ico 2 N, CC q a n *
          (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))|
      ≤ |CC q a N| / Real.log N + ∑ n ∈ Ico 2 N, |CC q a n| *
          (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_div, abs_of_pos hlN]
        · refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl (fun n hn => ?_)))
          rw [abs_mul, abs_of_nonneg (hdiff n hn)]
    _ ≤ M / Real.log N + ∑ n ∈ Ico 2 N, M * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
        refine add_le_add (div_le_div_of_nonneg_right (hM N (mem_Icc.mpr ⟨hN, le_rfl⟩)) hlN.le)
          (sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right ?_ (hdiff n hn)))
        rw [mem_Ico] at hn
        exact hM n (mem_Icc.mpr ⟨hn.1, hn.2.le⟩)
    _ = M / Real.log 2 := by
        rw [← mul_sum, tele N hN]; field_simp; ring

/-- For each `q ≥ 1` and `0 ≤ y ≤ x` there is `0 ≤ z ≤ x` with
`|π(y; q, a) - liD(y)/φ(q)| ≤ (|θ(z; q, a) - z/φ(q)| + 1/φ(q))/log 2`. -/
lemma pi_le_theta (hq : 1 ≤ q) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ x ∧ |piAP y q a - liD y / q.totient| ≤
      (|thetaAP z q a - z / q.totient| + 1 / q.totient) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  set N := ⌊y⌋₊ with hNdef
  have hEE : piAP y q a - liD y / q.totient = EE q a N := by
    rw [EE_eq]; rfl
  rcases lt_or_ge N 2 with hN | hN
  · refine ⟨0, le_rfl, hy.trans hyx, ?_⟩
    rw [hEE, EE_small q a N hN, abs_zero]
    positivity
  · obtain ⟨m, hm, hmax⟩ := exists_max_image (Icc 2 N) (fun n => |CC q a n|)
      ⟨2, mem_Icc.mpr ⟨le_rfl, hN⟩⟩
    rw [mem_Icc] at hm
    have hmy : (m : ℝ) ≤ y := by
      have : (m : ℝ) ≤ N := by exact_mod_cast hm.2
      exact this.trans (Nat.floor_le hy)
    refine ⟨m, Nat.cast_nonneg _, hmy.trans hyx, ?_⟩
    rw [hEE]
    refine (abel_bound q a N hN _ hmax).trans ?_
    apply div_le_div_of_nonneg_right _ hlog2.le
    rw [CC_eq q a m (by omega)]
    have ht : thetaAP (m : ℝ) q a = thetaN m q a := by simp [thetaAP]
    rw [ht]
    have e : thetaN m q a - ((m : ℝ) - 1) / q.totient =
        (thetaN m q a - m / q.totient) + 1 / q.totient := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / q.totient)]

end Abel

theorem bvPi_of (hT : BVTheta) : BVPi := by
  intro A hA
  obtain ⟨B1, hB1, K1, hK1⟩ := hT A hA
  set B := B1 + A with hBdef
  have hB : 0 < B := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨T, hTs⟩ := small_x_bound A B (Real.exp 1) hA hB
    (by have := Real.add_one_le_exp (1 : ℝ); linarith)
  refine ⟨B, hB, max ((K1 + 1) / Real.log 2) T, ?_⟩
  intro x hx a ha y hy
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hxL : 0 ≤ x / Real.log x ^ A := by positivity
  by_cases hxe : Real.exp 1 ≤ x
  · set L := Real.log x with hLdef
    have hL1 : 1 ≤ L := by
      rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hch : ∀ q, ∃ z : ℝ, 0 ≤ z ∧ z ≤ x ∧ (1 ≤ q → |piAP (y q) q (a q) - liD (y q) / q.totient| ≤
        (|thetaAP z q (a q) - z / q.totient| + 1 / q.totient) / Real.log 2) := by
      intro q
      rcases Nat.eq_zero_or_pos q with h0 | hq
      · exact ⟨0, le_rfl, hx0.le, fun h => by omega⟩
      · obtain ⟨z, h1, h2, h3⟩ := pi_le_theta q (a q) hq (hy q).1 (hy q).2
        exact ⟨z, h1, h2, fun _ => h3⟩
    choose z hz0 hzx hz using hch
    have hBB : L ^ B1 ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hsub : Icc 1 ⌊Real.sqrt x / L ^ B⌋₊ ⊆ Icc 1 ⌊Real.sqrt x / L ^ B1⌋₊ := by
      apply Icc_subset_Icc_right; apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hsx0.le (Real.rpow_pos_of_pos hL0 _) hBB
    have hs1 : ∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, |piAP (y q) q (a q) - liD (y q) / q.totient| ≤
        (∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, |thetaAP (z q) q (a q) - z q / q.totient| +
          ∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, (1 : ℝ) / q.totient) / Real.log 2 := by
      rw [← sum_add_distrib, sum_div]
      exact sum_le_sum (fun q hq => hz q (mem_Icc.mp hq).1)
    have hs2 : ∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, |thetaAP (z q) q (a q) - z q / q.totient| ≤
        K1 * x / L ^ A :=
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans
        (hK1 x hx a ha z (fun q => ⟨hz0 q, hzx q⟩))
    have hs3 : ∑ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, (1 : ℝ) / q.totient ≤ x / L ^ A := by
      have hle : ∀ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊, (1 : ℝ) / q.totient ≤ 1 := by
        intro q hq
        have hφ1 : (1 : ℝ) ≤ q.totient := by
          exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hq).1
        rw [div_le_one (by linarith)]; exact hφ1
      refine (sum_le_card_nsmul _ _ _ hle).trans ?_
      rw [Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
      have hLA : L ^ A ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      calc (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) ≤ Real.sqrt x / L ^ B := Nat.floor_le (by positivity)
        _ ≤ x / L ^ B := div_le_div_of_nonneg_right (sqrt_le_self' (by linarith)) (by positivity)
        _ ≤ x / L ^ A := div_le_div_of_nonneg_left hx0.le hLA0 hLA
    calc _ ≤ _ := hs1
      _ ≤ (K1 * x / L ^ A + x / L ^ A) / Real.log 2 :=
          div_le_div_of_nonneg_right (add_le_add hs2 hs3) hlog2.le
      _ = (K1 + 1) / Real.log 2 * x / L ^ A := by field_simp
      _ ≤ max ((K1 + 1) / Real.log 2) T * x / L ^ A := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxL
  · push Not at hxe
    refine (hTs x hx hxe.le (fun q => |piAP (y q) q (a q) - liD (y q) / q.totient|)
      (fun _ _ => abs_nonneg _) ?_).trans ?_
    · intro q hq
      have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
      have hN : (⌊y q⌋₊ : ℝ) ≤ x := (Nat.floor_le (hy q).1).trans (hy q).2
      have hp0 : 0 ≤ piAP (y q) q (a q) := by unfold piAP piN; positivity
      have hp : piAP (y q) q (a q) ≤ x := by
        unfold piAP piN
        refine le_trans ?_ hN
        have := card_filter_le (Icc 1 ⌊y q⌋₊) (fun n => n % q = a q % q ∧ n.Prime)
        rw [Nat.card_Icc, add_tsub_cancel_right] at this
        exact_mod_cast this
      have hl2 : (1 : ℝ) / Real.log 2 ≤ 2 := by
        rw [div_le_iff₀ hlog2]; have := Real.log_two_gt_d9; linarith
      have hli0 : 0 ≤ liD (y q) := by
        unfold liD liN
        exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
      have hli : liD (y q) ≤ 2 * x := by
        unfold liD liN
        have hle : ∀ n ∈ Icc 1 ⌊y q⌋₊, (1 : ℝ) / Real.log n ≤ 2 := by
          intro n hn
          rw [mem_Icc] at hn
          rcases Nat.eq_or_lt_of_le hn.1 with h1 | h2
          · subst h1; simp
          · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
            have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
            exact (one_div_le_one_div_of_le hlog2 hl).trans hl2
        refine (sum_le_card_nsmul _ _ _ hle).trans ?_
        rw [Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
        nlinarith
      have hli' : liD (y q) / q.totient ≤ 2 * x := (div_le_self hli0 hφ1).trans hli
      have hli0' : 0 ≤ liD (y q) / q.totient := div_nonneg hli0 (by linarith)
      have : 0 ≤ 3 * x * Real.log x := by positivity
      rw [abs_le]; constructor <;> nlinarith
    · rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxL

end LeanLab.PNTPort.BVMax

