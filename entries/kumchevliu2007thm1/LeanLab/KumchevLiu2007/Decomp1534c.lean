module

public import LeanLab.KumchevLiu2007.Statements

/-!
Kumchev and Liu 2007, Sums of primes and squares of primes in short intervals, arXiv 0801.0130.
Unit U-1534, run 20261026T0004Z-24325, DECOMPOSE. File c: the singular series factor `A₂(n, q)`
of eqs. (7), (8), (45) at `q = 1, 2, 3` and at primes dividing `n`, eq. (46), and the counting
step from the mean square bound of Proposition 1, eq. (33), to an exceptional set bound.

`ee x = e(x) = exp(2πix)`; `gaussS q a = S(q, a)`, eq. (8); `A2 n q = A₂(n, q)`, eq. (45).
These are noncomputable functions to `ℂ`, not Props.

Assemblies, no gap of their own, CONDITIONAL ON the leaves below:
* `InH2_iff_A2_ne`: `n ∈ ℋ₂` exactly when `1 + A₂(n, 2) ≠ 0` and `1 + A₂(n, 3) ≠ 0`, the local
  factors at 2 and 3 of `𝔖₂(n)`; Section 3.3, property iii.
* `card_nonpos_le`: a mean square bound `∑ |R - G|² ≤ B` with `G ≥ m > 0` leaves at most `B / m²`
  of the `n` with `R(n) ≤ 0`; the step from eq. (33) to the exceptional set bound.

AI-written Lean code, Claude, unit U-1534. Checked only by the Lean kernel.
Binary Goldbach is OPEN; these are Hua type problems.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.U1534

open Real Complex LeanLab.KumchevLiu2007

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `S(q, a) = ∑_{1 ≤ x ≤ q, (x, q) = 1} e(a x² / q)`, eq. (8); `x = q` is replaced by `x = 0`,
the same residue. -/
noncomputable def gaussS (q a : ℕ) : ℂ :=
  ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), ee ((a * x ^ 2 : ℕ) / (q : ℝ))

/-- `A₂(n, q) = μ(q) φ(q)^{-2} ∑_{1 ≤ a ≤ q, (a, q) = 1} S(q, a) e(-an/q)`, eq. (45). -/
noncomputable def A2 (n q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) *
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      gaussS q a * ee (-((a * n : ℕ) : ℝ) / q)

/-- LEAF. Unit U-1534. `S(2, 1) = e(1/2) = -1`; eq. (8) at `q = 2`. -/
theorem gaussS_two_one : gaussS 2 1 = -1 := by
  dsimp [gaussS]
  have : (Finset.range 2).filter (fun x => Nat.Coprime x 2) = {1} := by decide
  rw [this, Finset.sum_singleton]
  dsimp [ee]
  have : (2 : ℂ) * (Real.pi : ℂ) * I * ↑(((1 : ℕ) : ℝ) / (2 : ℝ)) = (Real.pi : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_pi_mul_I]

/-- LEAF. Unit U-1534. `S(3, a) = 2 e(a/3)`, since `1² ≡ 2² ≡ 1 (mod 3)`; eq. (8) at `q = 3`. -/
theorem gaussS_three (a : ℕ) : gaussS 3 a = 2 * ee ((a : ℝ) / 3) := by
  dsimp [gaussS]
  have : (Finset.range 3).filter (fun x => Nat.Coprime x 3) = {1, 2} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_singleton]
  have eq1 : ((a * 1 ^ 2 : ℕ) : ℝ) / 3 = (a : ℝ) / 3 := by
    push_cast
    ring
  have eq2 : ((a * 2 ^ 2 : ℕ) : ℝ) / 3 = ((a * 4 : ℕ) : ℝ) / 3 := by
    push_cast
    ring
  have eq3 : ee (((a * 4 : ℕ) : ℝ) / 3) = ee ((a : ℝ) / 3) := by
    dsimp [ee]
    have : (2 : ℂ) * ↑Real.pi * I * ↑(((a * 4 : ℕ) : ℝ) / 3) = (2 : ℂ) * ↑Real.pi * I * ↑(((a : ℕ) : ℝ) / 3) + ↑a * (2 * ↑Real.pi * I) := by
      push_cast
      ring
    rw [this, Complex.exp_add]
    have : cexp (↑a * (2 * ↑Real.pi * I)) = 1 := by
      rw [Complex.exp_nat_mul_two_pi_mul_I]
    rw [this, mul_one]
  rw [eq1, eq2, eq3]
  ring

/-- LEAF. Unit U-1534. `A₂(n, 1) = 1` for every `n`, the term `q = 1` of eq. (7). -/
theorem A2_one (n : ℕ) : A2 n 1 = 1 := by
  unfold A2
  have h1 : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := rfl
  rw [h1]
  rw [Finset.sum_singleton]
  unfold gaussS
  have h2 : (Finset.range 1).filter (fun x => Nat.Coprime x 1) = {0} := rfl
  rw [h2]
  rw [Finset.sum_singleton]
  have h3 : (ArithmeticFunction.moebius 1 : ℂ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]
    push_cast
    rfl
  have h4 : (Nat.totient 1 : ℂ) = 1 := by
    rw [Nat.totient_one]
    push_cast
    rfl
  rw [h3, h4]
  have eq1 : (1 : ℂ) / (1 : ℂ) ^ 2 = 1 := by ring
  rw [eq1, one_mul]
  unfold ee
  have H : cexp (2 * ↑Real.pi * I * ↑(((0 * 0 ^ 2 : ℕ) : ℝ) / (1 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((0 * n : ℕ) : ℝ) / (1 : ℝ))) = 1 := by
    have h1_inner : 2 * ↑Real.pi * I * ↑(((0 * 0 ^ 2 : ℕ) : ℝ) / (1 : ℝ)) = 0 := by push_cast; ring
    have h2_inner : 2 * ↑Real.pi * I * ↑(-((0 * n : ℕ) : ℝ) / (1 : ℝ)) = 0 := by push_cast; ring
    rw [h1_inner, h2_inner, Complex.exp_zero, mul_one]
  convert H using 4 <;> norm_cast

/-- LEAF. Unit U-1534. `A₂(n, 2) = 1` for even `n`, eq. (46) with `p = 2`, `p ∣ n`. -/
theorem A2_two_even {n : ℕ} (hn : n % 2 = 0) : A2 n 2 = 1 := by
  unfold A2
  have h1 : (Finset.range 2).filter (fun a => Nat.Coprime a 2) = {1} := rfl
  rw [h1, Finset.sum_singleton]
  have h_moe : (ArithmeticFunction.moebius 2 : ℂ) = -1 := by
    have h : ArithmeticFunction.moebius 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
    rw [h]
    push_cast
    rfl
  have h_tot : (Nat.totient 2 : ℂ) = 1 := by
    have h : Nat.totient 2 = 1 := rfl
    rw [h]
    push_cast
    rfl
  rw [h_moe, h_tot, gaussS_two_one]
  have eq1 : (-1 : ℂ) / (1 : ℂ) ^ 2 = -1 := by ring
  rw [eq1]
  unfold ee
  have : ∃ k : ℕ, n = 2 * k := by exists n / 2; omega
  rcases this with ⟨k, rfl⟩
  have H : cexp (2 * ↑Real.pi * I * ↑(-((1 * (2 * k) : ℕ) : ℝ) / (2 : ℝ))) = 1 := by
    have h_inner : 2 * ↑Real.pi * I * ↑(-((1 * (2 * k) : ℕ) : ℝ) / (2 : ℝ)) = ↑(- (k : ℤ)) * (2 * ↑Real.pi * I) := by
      push_cast
      ring
    rw [h_inner, Complex.exp_int_mul_two_pi_mul_I]
  have H2 : (-1 : ℂ) * (-1 * cexp (2 * ↑Real.pi * I * ↑(-((1 * (2 * k) : ℕ) : ℝ) / (2 : ℝ)))) = 1 := by
    rw [H]
    ring
  convert H2 using 2

/-- LEAF. Unit U-1534. `A₂(n, 2) = -1` for odd `n`, so the local factor `1 + A₂(n, 2)` vanishes;
eqs. (7), (8), (45) at `q = 2`. -/
theorem A2_two_odd {n : ℕ} (hn : n % 2 = 1) : A2 n 2 = -1 := by
  unfold A2
  have h1 : (Finset.range 2).filter (fun a => Nat.Coprime a 2) = {1} := rfl
  rw [h1, Finset.sum_singleton]
  have h_moe : (ArithmeticFunction.moebius 2 : ℂ) = -1 := by
    have h : ArithmeticFunction.moebius 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
    rw [h]
    push_cast
    rfl
  have h_tot : (Nat.totient 2 : ℂ) = 1 := by
    have h : Nat.totient 2 = 1 := rfl
    rw [h]
    push_cast
    rfl
  rw [h_moe, h_tot, gaussS_two_one]
  have eq1 : (-1 : ℂ) / (1 : ℂ) ^ 2 = -1 := by ring
  rw [eq1]
  unfold ee
  have : ∃ k : ℕ, n = 2 * k + 1 := by exists n / 2; omega
  rcases this with ⟨k, rfl⟩
  have H : cexp (2 * ↑Real.pi * I * ↑(-((1 * (2 * k + 1) : ℕ) : ℝ) / (2 : ℝ))) = -1 := by
    have h_inner : 2 * ↑Real.pi * I * ↑(-((1 * (2 * k + 1) : ℕ) : ℝ) / (2 : ℝ)) = ↑(- (k : ℤ)) * (2 * ↑Real.pi * I) - ↑Real.pi * I := by
      push_cast
      ring
    rw [h_inner, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I]
    have h_inner2 : cexp (↑Real.pi * I) = -1 := Complex.exp_pi_mul_I
    rw [h_inner2]
    ring
  have H2 : (-1 : ℂ) * (-1 * cexp (2 * ↑Real.pi * I * ↑(-((1 * (2 * k + 1) : ℕ) : ℝ) / (2 : ℝ)))) = -1 := by
    rw [H]
    ring
  convert H2 using 2

lemma eval_exp : cexp (2 * ↑Real.pi * I * (1 / 3)) + cexp (2 * ↑Real.pi * I * (2 / 3)) = -1 := by
  have : cexp (2 * ↑Real.pi * I * (1 / 3)) ^ 3 = 1 := by
    rw [← Complex.exp_nat_mul]
    have h : (3 : ℕ) * (2 * ↑Real.pi * I * (1 / 3)) = 2 * ↑Real.pi * I := by push_cast; ring
    rw [h, Complex.exp_two_pi_mul_I]
  have eq2 : cexp (2 * ↑Real.pi * I * (2 / 3)) = cexp (2 * ↑Real.pi * I * (1 / 3)) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [eq2]
  set x := cexp (2 * ↑Real.pi * I * (1 / 3))
  have H : x^3 - 1 = 0 := sub_eq_zero.mpr this
  have H_factor : (x - 1) * (x^2 + x + 1) = 0 := by
    calc (x - 1) * (x^2 + x + 1) = x^3 - 1 := by ring
      _ = 0 := H
  have h_ne : x - 1 ≠ 0 := by
    intro hc
    have h_x_1 : cexp (2 * ↑Real.pi * I * (1 / 3)) = 1 := sub_eq_zero.mp hc
    have H_eq : ∃ k : ℤ, 2 * ↑Real.pi * I * (1 / 3) = k * (2 * ↑Real.pi * I) := by
      rw [← Complex.exp_eq_one_iff]
      exact h_x_1
    rcases H_eq with ⟨k, hk⟩
    have h_div : (2 * ↑Real.pi * I) * (1 / 3) = (2 * ↑Real.pi * I) * k := by
      calc (2 * ↑Real.pi * I) * (1 / 3) = 2 * ↑Real.pi * I * (1 / 3) := by ring
        _ = ↑k * (2 * ↑Real.pi * I) := hk
        _ = (2 * ↑Real.pi * I) * ↑k := by ring
    have h_2piI_ne : 2 * ↑Real.pi * I ≠ 0 := by
      intro h
      have : (2 * ↑Real.pi * I).im = 0 := by rw [h]; rfl
      have H_im : (2 * ↑Real.pi * I).im = 2 * Real.pi := by simp
      rw [H_im] at this
      have : Real.pi = 0 := by linarith
      have ppos : 0 < Real.pi := Real.pi_pos
      linarith
    have hk_eq : (1 / 3 : ℂ) = ↑k := mul_left_cancel₀ h_2piI_ne h_div
    have hk_re : (1 / 3 : ℝ) = (k : ℝ) := by
      have h1 : ((1 / 3 : ℂ)).re = 1 / 3 := by norm_num
      have h2 : (↑k : ℂ).re = ↑k := by norm_num
      have h3 : ((1 / 3 : ℂ)).re = (↑k : ℂ).re := by rw [hk_eq]
      rw [h1, h2] at h3
      exact h3
    have hlt1 : (k : ℝ) < 1 := by linarith
    have hlt1_int : k < 1 := by exact_mod_cast hlt1
    have hgt0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hgt0_int : 0 < k := by exact_mod_cast hgt0
    omega
  have H2 : x^2 + x + 1 = 0 := by
    cases mul_eq_zero.mp H_factor with
    | inl h => contradiction
    | inr h => exact h
  calc x + x^2 = x^2 + x := by ring
    _ = (x^2 + x + 1) - 1 := by ring
    _ = 0 - 1 := by rw [H2]
    _ = -1 := by ring

/-- LEAF. Unit U-1534. `A₂(n, 3) = -1` for `n ≡ 1 (mod 3)`, so the local factor `1 + A₂(n, 3)`
vanishes; eqs. (7), (8), (45) at `q = 3`. -/
theorem A2_three_one {n : ℕ} (hn : n % 3 = 1) : A2 n 3 = -1 := by
  unfold A2
  have h1 : (Finset.range 3).filter (fun a => Nat.Coprime a 3) = {1, 2} := rfl
  rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]
  have h_moe : (ArithmeticFunction.moebius 3 : ℂ) = -1 := by
    have h : ArithmeticFunction.moebius 3 = -1 := ArithmeticFunction.moebius_apply_prime (by decide)
    rw [h]; push_cast; rfl
  have h_tot : (Nat.totient 3 : ℂ) = 2 := by
    have h : Nat.totient 3 = 2 := rfl
    rw [h]; push_cast; rfl
  rw [h_moe, h_tot]
  have eq1 : (-1 : ℂ) / (2 : ℂ) ^ 2 = -1 / 4 := by ring
  rw [eq1]
  rw [gaussS_three 1, gaussS_three 2]
  unfold ee
  have : ∃ k : ℕ, n = 3 * k + 1 := by exists n / 3; omega
  rcases this with ⟨k, rfl⟩
  have H : (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k + 1) : ℕ) : ℝ) / (3 : ℝ))) + 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k + 1) : ℕ) : ℝ) / (3 : ℝ)))) = -1 := by
    have H1 : 2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k + 1) : ℕ) : ℝ) / (3 : ℝ))) = 2 * cexp (↑(- (k : ℤ)) * (2 * ↑Real.pi * I)) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have H1b : cexp (↑(- (k : ℤ)) * (2 * ↑Real.pi * I)) = 1 := by rw [Complex.exp_int_mul_two_pi_mul_I]
    have H2 : 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k + 1) : ℕ) : ℝ) / (3 : ℝ))) = 2 * cexp (↑(- (2 * k : ℤ)) * (2 * ↑Real.pi * I)) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have H2b : cexp (↑(- (2 * k : ℤ)) * (2 * ↑Real.pi * I)) = 1 := by rw [Complex.exp_int_mul_two_pi_mul_I]
    have step1 : 2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k + 1) : ℕ) : ℝ) / (3 : ℝ))) = 2 * 1 := by rw [H1, H1b]
    have step2 : 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k + 1) : ℕ) : ℝ) / (3 : ℝ))) = 2 * 1 := by rw [H2, H2b]
    rw [step1, step2]
    ring
  exact H

/-- LEAF. Unit U-1534. `A₂(n, 3) = 1/2` for `n ≢ 1 (mod 3)`; eqs. (45), (46) at `q = 3`. -/
theorem A2_three_ne_one {n : ℕ} (hn : n % 3 ≠ 1) : A2 n 3 = 1 / 2 := by
  unfold A2
  have h1 : (Finset.range 3).filter (fun a => Nat.Coprime a 3) = {1, 2} := rfl
  rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]
  have h_moe : (ArithmeticFunction.moebius 3 : ℂ) = -1 := by
    have h : ArithmeticFunction.moebius 3 = -1 := ArithmeticFunction.moebius_apply_prime (by decide)
    rw [h]; push_cast; rfl
  have h_tot : (Nat.totient 3 : ℂ) = 2 := by
    have h : Nat.totient 3 = 2 := rfl
    rw [h]; push_cast; rfl
  rw [h_moe, h_tot]
  have eq1 : (-1 : ℂ) / (2 : ℂ) ^ 2 = -1 / 4 := by ring
  rw [eq1]
  rw [gaussS_three 1, gaussS_three 2]
  unfold ee
  have h_cases : n % 3 = 0 ∨ n % 3 = 2 := by omega
  rcases h_cases with h_zero | h_two
  · have : ∃ k : ℕ, n = 3 * k := by exists n / 3; omega
    rcases this with ⟨k, rfl⟩
    have H : (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k) : ℕ) : ℝ) / (3 : ℝ))) + 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k) : ℕ) : ℝ) / (3 : ℝ)))) = 1 / 2 := by
      have H1 : 2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k) : ℕ) : ℝ) / (3 : ℝ))) = 2 * cexp (2 * ↑Real.pi * I * (1 / 3)) := by
        rw [mul_assoc, ← Complex.exp_add]
        have H1_inner : 2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ)) + 2 * ↑Real.pi * I * ↑(-((1 * (3 * k) : ℕ) : ℝ) / (3 : ℝ)) = 2 * ↑Real.pi * I * (1 / 3) + ↑(- (k : ℤ)) * (2 * ↑Real.pi * I) := by
          push_cast
          ring
        rw [H1_inner, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have H2 : 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k) : ℕ) : ℝ) / (3 : ℝ))) = 2 * cexp (2 * ↑Real.pi * I * (2 / 3)) := by
        rw [mul_assoc, ← Complex.exp_add]
        have H2_inner : 2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ)) + 2 * ↑Real.pi * I * ↑(-((2 * (3 * k) : ℕ) : ℝ) / (3 : ℝ)) = 2 * ↑Real.pi * I * (2 / 3) + ↑(- (2 * k : ℤ)) * (2 * ↑Real.pi * I) := by
          push_cast
          ring
        rw [H2_inner, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [H1, H2]
      have H_eval : (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * (1 / 3)) + 2 * cexp (2 * ↑Real.pi * I * (2 / 3))) = 1 / 2 := by
        calc (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * (1 / 3)) + 2 * cexp (2 * ↑Real.pi * I * (2 / 3))) = (-1 / 4 : ℂ) * 2 * (cexp (2 * ↑Real.pi * I * (1 / 3)) + cexp (2 * ↑Real.pi * I * (2 / 3))) := by ring
          _ = (-1 / 4 : ℂ) * 2 * (-1) := by rw [eval_exp]
          _ = 1 / 2 := by ring
      exact H_eval
    exact H
  · have : ∃ k : ℕ, n = 3 * k + 2 := by exists n / 3; omega
    rcases this with ⟨k, rfl⟩
    have H : (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k + 2) : ℕ) : ℝ) / (3 : ℝ))) + 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k + 2) : ℕ) : ℝ) / (3 : ℝ)))) = 1 / 2 := by
      have H1 : 2 * cexp (2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((1 * (3 * k + 2) : ℕ) : ℝ) / (3 : ℝ))) = 2 * cexp (2 * ↑Real.pi * I * (-1 / 3)) := by
        rw [mul_assoc, ← Complex.exp_add]
        have H1_inner : 2 * ↑Real.pi * I * ↑(((1 : ℕ) : ℝ) / (3 : ℝ)) + 2 * ↑Real.pi * I * ↑(-((1 * (3 * k + 2) : ℕ) : ℝ) / (3 : ℝ)) = 2 * ↑Real.pi * I * (-1 / 3) + ↑(- (k : ℤ)) * (2 * ↑Real.pi * I) := by
          push_cast
          ring
        rw [H1_inner, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have H2 : 2 * cexp (2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ))) * cexp (2 * ↑Real.pi * I * ↑(-((2 * (3 * k + 2) : ℕ) : ℝ) / (3 : ℝ))) = 2 * cexp (2 * ↑Real.pi * I * (-2 / 3)) := by
        rw [mul_assoc, ← Complex.exp_add]
        have H2_inner : 2 * ↑Real.pi * I * ↑(((2 : ℕ) : ℝ) / (3 : ℝ)) + 2 * ↑Real.pi * I * ↑(-((2 * (3 * k + 2) : ℕ) : ℝ) / (3 : ℝ)) = 2 * ↑Real.pi * I * (-2 / 3) + ↑(- (2 * k : ℤ)) * (2 * ↑Real.pi * I) := by
          push_cast
          ring
        rw [H2_inner, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [H1, H2]
      have h1 : cexp (2 * ↑Real.pi * I * (-1 / 3)) = cexp (2 * ↑Real.pi * I * (2 / 3)) := by
        have : 2 * ↑Real.pi * I * (-1 / 3) = 2 * ↑Real.pi * I * (2 / 3) + (-1 : ℤ) * (2 * ↑Real.pi * I) := by push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have h2 : cexp (2 * ↑Real.pi * I * (-2 / 3)) = cexp (2 * ↑Real.pi * I * (1 / 3)) := by
        have : 2 * ↑Real.pi * I * (-2 / 3) = 2 * ↑Real.pi * I * (1 / 3) + (-1 : ℤ) * (2 * ↑Real.pi * I) := by push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [h1, h2]
      have H_eval : (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * (2 / 3)) + 2 * cexp (2 * ↑Real.pi * I * (1 / 3))) = 1 / 2 := by
        calc (-1 / 4 : ℂ) * (2 * cexp (2 * ↑Real.pi * I * (2 / 3)) + 2 * cexp (2 * ↑Real.pi * I * (1 / 3))) = (-1 / 4 : ℂ) * 2 * (cexp (2 * ↑Real.pi * I * (1 / 3)) + cexp (2 * ↑Real.pi * I * (2 / 3))) := by ring
          _ = (-1 / 4 : ℂ) * 2 * (-1) := by rw [eval_exp]
          _ = 1 / 2 := by ring
      exact H_eval
    exact H

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- LEAF. Unit U-1534. `A₂(n, p) = 1/(p - 1)` for every prime `p` dividing `n`; eq. (46),
first case. -/
theorem A2_prime_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) : A2 n p = 1 / ((p : ℂ) - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have std_int (a : ℤ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    rw [ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    simpa using std_int (a : ℤ)
  have sum_range (f : ZMod p → ℂ) :
      ∑ a ∈ Finset.range p, f (a : ZMod p) = ∑ a : ZMod p, f a := by
    apply Finset.sum_bij (s := Finset.range p) (t := (Finset.univ : Finset (ZMod p))) (fun a _ => (a : ZMod p))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have coprime_iff (a : ℕ) : Nat.Coprime a p ↔ (a : ZMod p) ≠ 0 := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, ne_eq, ZMod.natCast_eq_zero_iff]
  have filtered (f : ZMod p → ℂ) :
      ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p), f (a : ZMod p) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod p)), f a := by
    rw [Finset.sum_filter]
    simp_rw [coprime_iff]
    rw [sum_range (fun a => if a ≠ 0 then f a else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  have gauss_eq (a : ℕ) : gaussS p a =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar ((a : ZMod p) * x ^ 2) := by
    unfold gaussS
    simp_rw [std_nat, Nat.cast_mul, Nat.cast_pow]
    exact filtered (fun x => ZMod.stdAddChar ((a : ZMod p) * x ^ 2))
  have hn : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
  have exp_neg (a : ℕ) : ee (-((a * n : ℕ) : ℝ) / p) = 1 := by
    have heq : -((a * n : ℕ) : ℝ) / p = ((-((a * n : ℕ) : ℤ) : ℤ) : ℝ) / p := by
      push_cast; ring
    rw [heq, std_int]
    simp [hn]
  have hchar (x : ZMod p) (hx : x ≠ 0) :
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * x ^ 2) = -1 := by
    have ht := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) (x ^ 2)
      (ZMod.isPrimitive_stdAddChar p)
    rw [ite_eq_right (pow_ne_zero 2 hx)] at ht
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a : ZMod p => ZMod.stdAddChar (a * x ^ 2)) (Finset.mem_univ 0)
    simp only [zero_mul, AddChar.map_zero_eq_one] at hs
    rw [ht] at hs
    linear_combination hs
  have hg : ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p), gaussS p a =
      -((p : ℂ) - 1) := by
    simp_rw [gauss_eq]
    rw [filtered (fun a => ∑ x ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * x ^ 2)), Finset.sum_comm]
    have ht : ∑ x ∈ Finset.univ.erase (0 : ZMod p),
        ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * x ^ 2) =
        ∑ x ∈ Finset.univ.erase (0 : ZMod p), (-1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hchar x (Finset.mem_erase.mp hx).1
    rw [ht]
    simp [ZMod.card, Nat.cast_sub hp.one_le]
  unfold A2
  simp_rw [exp_neg, mul_one]
  rw [hg, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  push_cast
  have hpC : (p : ℂ) - 1 ≠ 0 := by
    have hp2 := hp.two_le
    exact_mod_cast (show (p : ℤ) - 1 ≠ 0 by omega)
  rw [Nat.cast_sub hp.one_le]
  norm_num only [Nat.cast_one]
  field_simp

/-- LEAF. Unit U-1534. Chebyshev counting: on a finite set, the number of `n` with `|f n| ≥ T`,
times `T²`, is at most `∑ f n²`, for `T > 0`; the counting step after eq. (33). -/
theorem chebyshev_count (s : Finset ℕ) (f : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    ((s.filter (fun n => T ≤ |f n|)).card : ℝ) * T ^ 2 ≤ ∑ n ∈ s, f n ^ 2 := by
  have H : ∑ n ∈ s.filter (fun n => T ≤ |f n|), T ^ 2 ≤ ∑ n ∈ s.filter (fun n => T ≤ |f n|), f n ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    have : T ^ 2 ≤ |f i| ^ 2 := by
      have H1 : |T| ≤ |(|f i|)| := by
        rw [abs_of_pos hT, abs_of_nonneg (abs_nonneg _)]
        exact hi.2
      exact sq_le_sq.mpr H1
    have h_abs_sq : |f i| ^ 2 = f i ^ 2 := sq_abs (f i)
    rwa [h_abs_sq] at this
  have H2 : ∑ n ∈ s.filter (fun n => T ≤ |f n|), T ^ 2 = ((s.filter (fun n => T ≤ |f n|)).card : ℝ) * T ^ 2 := by
    simp
  rw [H2] at H
  calc ((s.filter (fun n => T ≤ |f n|)).card : ℝ) * T ^ 2 ≤ ∑ n ∈ s.filter (fun n => T ≤ |f n|), f n ^ 2 := H
    _ ≤ ∑ n ∈ s, f n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro i _ _
        positivity

/-- LEAF. Unit U-1534. If `0 < m ≤ G` and `R ≤ 0`, then `m ≤ |R - G|`; a nonpositive count is
far from a large main term, the step after eq. (33). -/
theorem deficit_le {R G m : ℝ} (hm : 0 < m) (hG : m ≤ G) (hR : R ≤ 0) : m ≤ |R - G| := by
  calc m ≤ G - R := by linarith
       _ = -(R - G) := by ring
       _ ≤ |-(R - G)| := le_abs_self _
       _ = |R - G| := abs_neg _

/-- LEAF. Unit U-1534. Exponent bookkeeping: `H Y L^{-A} / (Y^{1/2} L^{-2})² = H L^{4 - A}`
for `Y, L > 0`; the size of eq. (33) against the main term `r₂(n) ≍ Y^{1/2} L^{-2}`. -/
theorem mean_square_ratio {H Y L A : ℝ} (hY : 0 < Y) (hL : 0 < L) :
    H * Y * L ^ (-A) / (Y ^ (1 / 2 : ℝ) * L ^ (-2 : ℝ)) ^ 2 = H * L ^ (4 - A) := by
  have h1 : (Y ^ (1 / 2 : ℝ) * L ^ (-2 : ℝ)) ^ 2 = Y * L ^ (-4 : ℝ) := by
    rw [mul_pow]
    have h1a : (Y ^ (1 / 2 : ℝ)) ^ 2 = Y := by
      rw [← rpow_natCast, ← rpow_mul hY.le]
      norm_num
    have h1b : (L ^ (-2 : ℝ)) ^ 2 = L ^ (-4 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hL.le]
      norm_num
    rw [h1a, h1b]
  rw [h1]
  rw [div_eq_mul_inv, mul_inv]
  calc H * Y * L ^ (-A) * (Y⁻¹ * (L ^ (-4 : ℝ))⁻¹) = H * (Y * Y⁻¹) * (L ^ (-A) * (L ^ (-4 : ℝ))⁻¹) := by ring
    _ = H * 1 * (L ^ (-A) * (L ^ (-4 : ℝ))⁻¹) := by rw [mul_inv_cancel₀ hY.ne']
    _ = H * (L ^ (-A) * (L ^ (-4 : ℝ))⁻¹) := by ring
    _ = H * (L ^ (-A) / L ^ (-4 : ℝ)) := by rw [div_eq_mul_inv]
    _ = H * L ^ (-A - -4) := by rw [← rpow_sub hL]
    _ = H * L ^ (4 - A) := by congr 2; ring

/-- LEAF. Unit U-1534. For `1 < a ≤ X` and `1 < b ≤ X`, `1/(log a log b) ≥ 1/(log X)²`; each
term of `r₂(n)`, eq. (6), is at least `L^{-2}`. -/
theorem inv_log_mul_ge {a b X : ℝ} (ha : 1 < a) (haX : a ≤ X) (hb : 1 < b) (hbX : b ≤ X) :
    1 / Real.log X ^ 2 ≤ 1 / (Real.log a * Real.log b) := by
  have loga_pos : 0 < Real.log a := Real.log_pos ha
  have logb_pos : 0 < Real.log b := Real.log_pos hb
  have logX_pos : 0 < Real.log X := by
    calc 0 < Real.log a := loga_pos
         _ ≤ Real.log X := Real.log_le_log (by positivity) haX
  rw [one_div, one_div]
  apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
  calc Real.log a * Real.log b ≤ Real.log X * Real.log b := by
        apply mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) haX) logb_pos.le
       _ ≤ Real.log X * Real.log X := by
        apply mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hbX) logX_pos.le
       _ = Real.log X ^ 2 := by ring

/-! ### Assemblies -/

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `A2_two_even`, `A2_two_odd`, `A2_three_one`
and `A2_three_ne_one`. `n ∈ ℋ₂` exactly when the local factors `1 + A₂(n, 2)` and
`1 + A₂(n, 3)` of the singular series are nonzero. -/
theorem InH2_iff_A2_ne (n : ℕ) : InH2 n ↔ (1 + A2 n 2 ≠ 0 ∧ 1 + A2 n 3 ≠ 0) := by
  constructor
  · intro ⟨h3, h2⟩
    rw [A2_two_even (by omega), A2_three_ne_one h3]
    norm_num
  · intro ⟨h2, h3⟩
    refine ⟨fun h => h3 (by rw [A2_three_one h]; ring), ?_⟩
    by_contra hc
    exact h2 (by rw [A2_two_odd (by omega)]; ring)

/-- ASSEMBLY, no gap of its own, CONDITIONAL ON `chebyshev_count` and `deficit_le`.
If `∑_{n ∈ s} (R n - G n)² ≤ B` and `G n ≥ m > 0` on `s`, then at most `B / m²` of the `n ∈ s`
have `R n ≤ 0`; with `R = R(n; λ₁, λ₂)`, `G = 𝔖₂(n, P) I(n; λ₁, λ₂)` this is how eq. (33)
bounds the exceptional set. -/
theorem card_nonpos_le (s : Finset ℕ) (R G : ℕ → ℝ) {m B : ℝ} (hm : 0 < m)
    (hG : ∀ n ∈ s, m ≤ G n) (hB : ∑ n ∈ s, (R n - G n) ^ 2 ≤ B) :
    ((s.filter (fun n => R n ≤ 0)).card : ℝ) ≤ B / m ^ 2 := by
  have hsub : s.filter (fun n => R n ≤ 0) ⊆ s.filter (fun n => m ≤ |R n - G n|) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, deficit_le hm (hG n hn.1) hn.2⟩
  have hc := chebyshev_count s (fun n => R n - G n) hm
  have hcard : ((s.filter (fun n => R n ≤ 0)).card : ℝ) ≤
      (s.filter (fun n => m ≤ |R n - G n|)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hm2 : 0 < m ^ 2 := by positivity
  rw [le_div_iff₀ hm2]
  calc ((s.filter (fun n => R n ≤ 0)).card : ℝ) * m ^ 2
      ≤ ((s.filter (fun n => m ≤ |R n - G n|)).card : ℝ) * m ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hm2.le
    _ ≤ ∑ n ∈ s, (R n - G n) ^ 2 := hc
    _ ≤ B := hB

end LeanLab.KumchevLiu2007.U1534
