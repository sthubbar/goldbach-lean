module

public import LeanLab.RieselVaughan1983.Lemma8

/-!
P0032 Riesel-Vaughan 1983, Lemma 15, page 68: for `log y ≥ 350`,
`Σ_{k ≤ K} S_k > (Ky/log y)(1 - 3.6581/log y)` with `K = 200`, where `S_k` is the number of
primes in `I_k = (ky/2, ky/2 + y]`. PROVED CONDITIONAL ON Lemma 6 (i) and (ii), page 55,
including the telescoping (8.22), the lower bound (8.23), the bound for `π(y/2)` with its
constant 0.85683, which has slack about 3·10⁻⁶ at `log y = 350`, and `A₁₂ ≤ 3.6581`, slack
3.3·10⁻⁵.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real

namespace LeanLab.RieselVaughan1983

/-- Lemma 6 (ii), p. 55, CITED: `π(x) < x/log x + 1.0151 x/(log x)²` for `log x ≥ 300`. -/
def Lemma6ii : Prop :=
  ∀ x : ℝ, 0 < x → 300 ≤ Real.log x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2

/-- `S_k`, (8.13): the primes in `(ky/2, ky/2 + y]`, as `π(ky/2 + y) - π(ky/2)`. -/
noncomputable def Sk (y : ℝ) (k : ℕ) : ℝ :=
  (Nat.primeCounting ⌊k * y / 2 + y⌋₊ : ℝ) - Nat.primeCounting ⌊k * y / 2⌋₊

/-- (8.22): `Σ_{k=1}^K S_k = π(Ky/2 + y/2) + π(Ky/2 + y) - π(y/2) - π(y)`, by telescoping. -/
lemma sum_Sk (y : ℝ) (K : ℕ) :
    ∑ k ∈ Icc 1 K, Sk y k = (Nat.primeCounting ⌊(K + 1) * y / 2⌋₊ : ℝ) +
      Nat.primeCounting ⌊(K + 2) * y / 2⌋₊ - Nat.primeCounting ⌊1 * y / 2⌋₊ -
      Nat.primeCounting ⌊2 * y / 2⌋₊ := by
  set f : ℕ → ℝ := fun k => (Nat.primeCounting ⌊k * y / 2⌋₊ : ℝ) with hf
  have hS : ∀ k : ℕ, Sk y k = f (k + 2) - f k := by
    intro k; simp only [Sk, hf]; push_cast
    rw [show ((k : ℝ) + 2) * y / 2 = k * y / 2 + y by ring]
  simp_rw [hS]
  induction K with
  | zero => simp [hf]
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    simp only [hf]; push_cast; ring_nf

/-- `log(1 - x) ≤ -Σ_{i<n} x^{i+1}/(i+1) + x^{n+1}/(1 - x)` for `0 ≤ x < 1`. -/
lemma log_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    Real.log (1 - x) ≤ -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).2
  linarith

lemma log_101_le : Real.log 101 ≤ 461513 / 100000 := by
  have e : (101 : ℝ) = 2 ^ 7 * (1 - 27 / 128) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_one_sub_le (27 / 128) (by norm_num) (by norm_num) 12
  have h2 := Real.log_two_lt_d9
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h ⊢
  linarith

lemma log_1005_le : Real.log (201 / 2) ≤ 461016 / 100000 := by
  have e : (201 / 2 : ℝ) = 2 ^ 7 * (1 - 55 / 256) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_one_sub_le (55 / 256) (by norm_num) (by norm_num) 12
  have h2 := Real.log_two_lt_d9
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h ⊢
  linarith

lemma log_ge_of_ge8 {lam : ℝ} (h : 8 ≤ lam) : 19822 / 10000 ≤ Real.log lam := by
  have : Real.log 8 ≤ Real.log lam := Real.log_le_log (by norm_num) h
  have e : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

/-- (8.23), page 68: `π(λy) > (λy/log y)(1 - (log λ - 0.9911)/log y)`; the paper needs
`log λ ≥ 1.9822`, here `λ ≥ 8`. -/
lemma pi_lam_lower (h6 : Lemma6i) (lam y : ℝ) (hlam8 : 8 ≤ lam)
    (hy : 0 < y) (hL : 17 ≤ Real.log y) :
    lam * y / Real.log y * (1 - (Real.log lam - 9911 / 10000) / Real.log y) <
      (Nat.primeCounting ⌊lam * y⌋₊ : ℝ) := by
  have hlam0 : 0 < lam := by linarith
  have ha := log_ge_of_ge8 hlam8
  set a := Real.log lam with hadef
  set L := Real.log y with hLdef
  set c : ℝ := 9911 / 10000 with hc
  have hM : Real.log (lam * y) = a + L := Real.log_mul hlam0.ne' hy.ne'
  have hpi := h6 (lam * y) (by positivity) (by rw [hM]; linarith)
  rw [hM] at hpi
  have hL0 : 0 < L := by linarith
  have hML : 0 < a + L := by linarith
  have hid : 1 / (a + L) + c / (a + L) ^ 2 - 1 / L * (1 - (a - c) / L) =
      (a * L * (a - 2 * c) + a ^ 2 * (a - c)) / (L ^ 2 * (a + L) ^ 2) := by
    field_simp; ring
  have hnn : 0 ≤ (a * L * (a - 2 * c) + a ^ 2 * (a - c)) / (L ^ 2 * (a + L) ^ 2) := by
    apply div_nonneg _ (by positivity)
    have h1 : 0 ≤ a - 2 * c := by rw [hc]; linarith
    have h2 : 0 ≤ a - c := by rw [hc]; linarith
    have ha0 : 0 ≤ a := by linarith
    positivity
  have key : 1 / L * (1 - (a - c) / L) ≤ 1 / (a + L) + c / (a + L) ^ 2 := by linarith
  have hly : 0 < lam * y := by positivity
  calc lam * y / L * (1 - (a - c) / L) = lam * y * (1 / L * (1 - (a - c) / L)) := by ring
    _ ≤ lam * y * (1 / (a + L) + c / (a + L) ^ 2) := mul_le_mul_of_nonneg_left key hly.le
    _ = lam * y / (a + L) + c * (lam * y) / (a + L) ^ 2 := by ring
    _ < _ := hpi

/-- Page 68: `π(y/2) < (y/log y)(1/2 + 0.85683/log y)` for `log y ≥ 350`. -/
lemma pi_half_upper (h6 : Lemma6ii) (y : ℝ) (hy : 0 < y) (hL : 350 ≤ Real.log y) :
    (Nat.primeCounting ⌊y / 2⌋₊ : ℝ) < y / Real.log y * (1 / 2 + 85683 / 100000 / Real.log y) := by
  set L := Real.log y with hLdef
  set b := Real.log 2 with hb
  have hb1 := Real.log_two_gt_d9
  have hb2 := Real.log_two_lt_d9
  have hM : Real.log (y / 2) = L - b := Real.log_div hy.ne' (by norm_num)
  have hpi := h6 (y / 2) (by positivity) (by rw [hM]; linarith)
  rw [hM] at hpi
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < L - b := by linarith
  -- `(1/2)/M + (1.0151/2)/M² ≤ 1/(2L) + 0.85683/L²`, a quadratic in `L` positive for `L ≥ 350`
  have hq : 0 ≤ L ^ 2 * (69856 / 100000 - b) + L * (b ^ 2 - 342732 / 100000 * b) +
      171366 / 100000 * b ^ 2 := by
    have hα : 54128192 / 10000000000 ≤ 69856 / 100000 - b := by linarith
    have hβ : -18951842 / 10000000 ≤ b ^ 2 - 342732 / 100000 * b := by nlinarith
    have hγ : 82333 / 100000 ≤ 171366 / 100000 * b ^ 2 := by nlinarith
    have t1 : L ^ 2 * (54128192 / 10000000000) ≤ L ^ 2 * (69856 / 100000 - b) :=
      mul_le_mul_of_nonneg_left hα (by positivity)
    have t2 : L * (-18951842 / 10000000) ≤ L * (b ^ 2 - 342732 / 100000 * b) :=
      mul_le_mul_of_nonneg_left hβ hL0.le
    nlinarith
  have hid : y / L * (1 / 2 + 85683 / 100000 / L) - (y / 2 / (L - b) + 10151 / 10000 * (y / 2) /
      (L - b) ^ 2) = y * (L ^ 2 * (69856 / 100000 - b) + L * (b ^ 2 - 342732 / 100000 * b) +
      171366 / 100000 * b ^ 2) / (2 * L ^ 2 * (L - b) ^ 2) := by
    field_simp; ring
  have : 0 ≤ y * (L ^ 2 * (69856 / 100000 - b) + L * (b ^ 2 - 342732 / 100000 * b) +
      171366 / 100000 * b ^ 2) / (2 * L ^ 2 * (L - b) ^ 2) := by positivity
  linarith

/-- **Lemma 15**, page 68, CONDITIONAL ON Lemma 6 (i) and (ii): with `K = 200`,
`Σ_{k=1}^K S_k > (Ky/log y)(1 - 3.6581/log y)` for `log y ≥ 350`. -/
theorem lemma15 (h6 : Lemma6i) (h6' : Lemma6ii) (y : ℝ) (hy : 0 < y)
    (hL : 350 ≤ Real.log y) :
    200 * y / Real.log y * (1 - 36581 / 10000 / Real.log y) < ∑ k ∈ Icc 1 200, Sk y k := by
  rw [sum_Sk]
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  have e1 : ((200 : ℕ) + 1 : ℝ) * y / 2 = 201 / 2 * y := by push_cast; ring
  have e2 : ((200 : ℕ) + 2 : ℝ) * y / 2 = 101 * y := by push_cast; ring
  have e3 : (1 : ℝ) * y / 2 = y / 2 := by ring
  have e4 : (2 : ℝ) * y / 2 = y := by ring
  push_cast at e1 e2 ⊢
  rw [e1, e2, e3, e4]
  have p1 := pi_lam_lower h6 (201 / 2) y (by norm_num) hy (by linarith)
  have p2 := pi_lam_lower h6 101 y (by norm_num) hy (by linarith)
  have p3 := pi_half_upper h6' y hy hL
  have p4 := h6' y hy (by linarith)
  have l1 := log_1005_le
  have l2 := log_101_le
  -- collect: the bracket is `200 - (100.5(a₁ - c) + 101(a₂ - c) + 1.0151 + 0.85683)/L`
  have hyL : 0 < y / L := by positivity
  have hsum : 200 * y / L * (1 - 36581 / 10000 / L) ≤
      201 / 2 * y / L * (1 - (Real.log (201 / 2) - 9911 / 10000) / L) +
      101 * y / L * (1 - (Real.log 101 - 9911 / 10000) / L) -
      y / L * (1 / 2 + 85683 / 100000 / L) - (y / L + 10151 / 10000 * y / L ^ 2) := by
    have hc : (201 / 2 * (Real.log (201 / 2) - 9911 / 10000) + 101 * (Real.log 101 - 9911 / 10000) +
        10151 / 10000 + 85683 / 100000) ≤ 200 * (36581 / 10000) := by linarith
    have : 200 * y / L * (1 - 36581 / 10000 / L) -
        (201 / 2 * y / L * (1 - (Real.log (201 / 2) - 9911 / 10000) / L) +
        101 * y / L * (1 - (Real.log 101 - 9911 / 10000) / L) -
        y / L * (1 / 2 + 85683 / 100000 / L) - (y / L + 10151 / 10000 * y / L ^ 2)) =
        y / L ^ 2 * ((201 / 2 * (Real.log (201 / 2) - 9911 / 10000) +
          101 * (Real.log 101 - 9911 / 10000) + 10151 / 10000 + 85683 / 100000) -
          200 * (36581 / 10000)) := by
      field_simp; ring
    have : y / L ^ 2 * ((201 / 2 * (Real.log (201 / 2) - 9911 / 10000) +
          101 * (Real.log 101 - 9911 / 10000) + 10151 / 10000 + 85683 / 100000) -
          200 * (36581 / 10000)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  rw [show y / L + 10151 / 10000 * y / L ^ 2 = y / Real.log y + 10151 / 10000 * y / Real.log y ^ 2
    from rfl] at hsum
  linarith

end LeanLab.RieselVaughan1983
