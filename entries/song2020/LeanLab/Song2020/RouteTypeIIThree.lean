module

public import LeanLab.Song2020.SPLIT_typeII_per_RS

/-!
AI wrote the Lean code, 2026-11-15, the split of the
Type II display typeII_bound.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 6 and 7, from
"By Lemma 2.5 in [2], we have" to the five term display for T(R,S).
This new file holds the step "So we have T(R,S) << x L^(-1/2) + R^(3/4) S L^(1/4)
x^(gamma/4-3/4) y^(1/2) |h|^(1/4) + R^(3/4) S L^(-1/4) x^(1/4-gamma/4) |h|^(-1/4)", from the
two inputs in SPLIT_typeII_per_RS.
Reading common to the files of this split: x of the print is R S, the size of r s on the
dyadic block, and the passage from R S to n is made at the end by monotonicity; r ~ R is
R at most r < 2 R; the window is |r s - n/3| < y and r s at most t; the phase R_b(m) is
alpha m + h m^gamma. The file defines nothing.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteTypeIIThree

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Song 2020, page 7, summing the first term of the Cor. 8.13 bound over 1 <= l <= L:
the sum of l^(1/2) is at most L * L^(1/2), each term being at most L^(1/2). -/
theorem sum_sqrt_le (L : ℕ) :
    ∑ l ∈ Finset.Icc 1 L, ((l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ (L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) := by
  have h : ∀ l ∈ Finset.Icc 1 L, ((l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ (L : ℝ) ^ ((1 : ℝ) / 2) := by
    intro l hl
    have hl' := (Finset.mem_Icc.mp hl).2
    exact Real.rpow_le_rpow (Nat.cast_nonneg l) (by exact_mod_cast hl') (by norm_num)
  calc ∑ l ∈ Finset.Icc 1 L, ((l : ℕ) : ℝ) ^ ((1 : ℝ) / 2)
      ≤ ∑ _l ∈ Finset.Icc 1 L, (L : ℝ) ^ ((1 : ℝ) / 2) := Finset.sum_le_sum h
    _ = (L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Finset.sum_const, Nat.card_Icc]; simp

/-- Song 2020, page 7, summing the second term of the Cor. 8.13 bound over 1 <= l <= L:
the sum of l^(-1/2) is at most 2 L^(1/2), by induction from
1 / sqrt (k+1) <= 2 sqrt (k+1) - 2 sqrt k. -/
theorem sum_inv_sqrt_le (L : ℕ) :
    ∑ l ∈ Finset.Icc 1 L, ((l : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) ≤ 2 * (L : ℝ) ^ ((1 : ℝ) / 2) := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have e1 : ((k + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hk1.le]; congr 1; ring
    have e2 : ((k + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      (Real.sqrt_eq_rpow _).symm
    have e3 : (k : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (k : ℝ) := (Real.sqrt_eq_rpow _).symm
    rw [e1, e2]
    rw [e3] at ih
    have hs : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
    have ht : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
    have hs2 : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt hk
    have ht2 : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 = (k : ℝ) + 1 :=
      (Real.sq_sqrt hk1.le).trans (Nat.cast_succ k)
    have key : (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ ht]
      nlinarith [sq_nonneg (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))]
    linarith

/-- Song 2020, page 7, "So we have T(R,S) << ...": the rule (x^e)^2 = x^(2e) for a positive
base, used to recognise each term of the display as a square root. -/
theorem rpow_sq_eq (x : ℝ) (hx : 0 < x) (e f : ℝ) (hef : 2 * e = f) : (x ^ e) ^ 2 = x ^ f := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← hef]; congr 1; push_cast; ring

/-- Song 2020, page 7, summing the Cor. 8.13 bound over 1 <= l <= L: the factor |h| l splits,
and the two elementary sums over l give L * L^(1/2) and 2 L^(1/2). -/
theorem three_sum (Ci R S y A γ : ℝ) (L : ℕ) (hCi : 0 ≤ Ci) (hR0 : 0 < R) (hS0 : 0 < S)
    (hy0 : 0 < y) (hA0 : 0 < A) :
    ∑ l ∈ Finset.Icc 1 L,
      Ci * ((y / S + 1) * (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
                (A * l) ^ ((1 : ℝ) / 2)) +
              R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * (A * l) ^ (-(1 : ℝ) / 2)) ≤
      Ci * ((y / S + 1) * ((R ^ ((1 : ℝ) / 2))⁻¹ * (R * S) ^ ((γ - 1) / 2) *
          A ^ ((1 : ℝ) / 2)) * ((L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) +
        R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * A ^ (-(1 : ℝ) / 2) *
          (2 * (L : ℝ) ^ ((1 : ℝ) / 2))) := by
  have hX0 : 0 < R * S := mul_pos hR0 hS0
  have hRneg : R ^ (-(1 : ℝ) / 2) = (R ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hR0.le]; congr 1; ring
  have e : ∀ l ∈ Finset.Icc 1 L,
      Ci * ((y / S + 1) * (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
              (A * l) ^ ((1 : ℝ) / 2)) +
            R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * (A * l) ^ (-(1 : ℝ) / 2)) =
      Ci * ((y / S + 1) * ((R ^ ((1 : ℝ) / 2))⁻¹ * (R * S) ^ ((γ - 1) / 2) *
          A ^ ((1 : ℝ) / 2))) * ((l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) +
        Ci * (R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * A ^ (-(1 : ℝ) / 2)) *
          ((l : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
    intro l _
    rw [Real.mul_rpow hA0.le (Nat.cast_nonneg l), Real.mul_rpow hA0.le (Nat.cast_nonneg l),
      hRneg]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hyS : 0 ≤ y / S + 1 := by positivity
  have hr0 : 0 < R ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hR0 _
  have hu0 : 0 < (R * S) ^ ((γ - 1) / 2) := Real.rpow_pos_of_pos hX0 _
  have hv0 : 0 < (R * S) ^ ((1 - γ) / 2) := Real.rpow_pos_of_pos hX0 _
  have ha0 : 0 < A ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hA0 _
  have ha'0 : 0 < A ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hA0 _
  have c1 : 0 ≤ Ci * ((y / S + 1) * ((R ^ ((1 : ℝ) / 2))⁻¹ * (R * S) ^ ((γ - 1) / 2) *
          A ^ ((1 : ℝ) / 2))) :=
    mul_nonneg hCi (mul_nonneg hyS (mul_nonneg (mul_nonneg (inv_pos.mpr hr0).le hu0.le) ha0.le))
  have c2 : 0 ≤ Ci * (R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * A ^ (-(1 : ℝ) / 2)) :=
    mul_nonneg hCi (mul_nonneg (mul_nonneg hr0.le hv0.le) ha'0.le)
  have h1 := mul_le_mul_of_nonneg_left (sum_sqrt_le L) c1
  have h2 := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le L) c2
  have e1 : Ci * ((y / S + 1) * ((R ^ ((1 : ℝ) / 2))⁻¹ * (R * S) ^ ((γ - 1) / 2) *
          A ^ ((1 : ℝ) / 2)) * ((L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) +
        R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * A ^ (-(1 : ℝ) / 2) *
          (2 * (L : ℝ) ^ ((1 : ℝ) / 2))) =
      Ci * ((y / S + 1) * ((R ^ ((1 : ℝ) / 2))⁻¹ * (R * S) ^ ((γ - 1) / 2) *
          A ^ ((1 : ℝ) / 2))) * ((L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) +
      Ci * (R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) * A ^ (-(1 : ℝ) / 2)) *
          (2 * (L : ℝ) ^ ((1 : ℝ) / 2)) := by ring
  rw [e1]
  exact add_le_add h1 h2

/-- Song 2020, page 7, the first term of "So we have T(R,S) << ...": the square of
x L^(-1/2) is x^2 / L, with x = R S. -/
theorem three_sq_p (R S L : ℝ) (hL0 : 0 < L) :
    (R * S * L ^ (-(1 : ℝ) / 2)) ^ 2 = (R * S) ^ 2 / L := by
  rw [mul_pow, rpow_sq_eq L hL0 _ (-1) (by norm_num), Real.rpow_neg_one, div_eq_mul_inv]

/-- Song 2020, page 7, the second term of "So we have T(R,S) << ...": the square of
R^(3/4) S L^(1/4) x^(gamma/4-3/4) y^(1/2) |h|^(1/4), in terms of square roots. -/
theorem three_sq_q (R S L y A γ : ℝ) (hR0 : 0 < R) (hS0 : 0 < S) (hL0 : 0 < L) (hy0 : 0 < y)
    (hA0 : 0 < A) :
    (R ^ ((3 : ℝ) / 4) * S * L ^ ((1 : ℝ) / 4) * (R * S) ^ (γ / 4 - 3 / 4) *
        y ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 4)) ^ 2 =
      R ^ ((1 : ℝ) / 2) * S * L ^ ((1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) * y *
        A ^ ((1 : ℝ) / 2) := by
  have hX0 : 0 < R * S := mul_pos hR0 hS0
  have hR34 : (R ^ ((3 : ℝ) / 4)) ^ 2 = R ^ ((1 : ℝ) / 2) * R := by
    rw [rpow_sq_eq R hR0 _ ((1 : ℝ) / 2 + 1) (by norm_num), Real.rpow_add hR0, Real.rpow_one]
  have hL14 : (L ^ ((1 : ℝ) / 4)) ^ 2 = L ^ ((1 : ℝ) / 2) :=
    rpow_sq_eq _ hL0 _ _ (by norm_num)
  have hX1 : ((R * S) ^ (γ / 4 - 3 / 4)) ^ 2 = (R * S) ^ ((γ - 1) / 2) * (R * S)⁻¹ := by
    rw [rpow_sq_eq _ hX0 _ ((γ - 1) / 2 + -1) (by ring), Real.rpow_add hX0, Real.rpow_neg_one]
  have hy12 : (y ^ ((1 : ℝ) / 2)) ^ 2 = y := by
    rw [rpow_sq_eq _ hy0 _ 1 (by norm_num), Real.rpow_one]
  have hA14 : (A ^ ((1 : ℝ) / 4)) ^ 2 = A ^ ((1 : ℝ) / 2) := rpow_sq_eq _ hA0 _ _ (by norm_num)
  simp only [mul_pow]
  rw [hR34, hL14, hX1, hy12, hA14]
  generalize R ^ ((1 : ℝ) / 2) = r
  generalize L ^ ((1 : ℝ) / 2) = lam
  generalize (R * S) ^ ((γ - 1) / 2) = u
  generalize A ^ ((1 : ℝ) / 2) = a
  have hR : R ≠ 0 := hR0.ne'
  have hS : S ≠ 0 := hS0.ne'
  field_simp

/-- Song 2020, page 7, the third term of "So we have T(R,S) << ...": the square of
R^(3/4) S L^(-1/4) x^(1/4-gamma/4) |h|^(-1/4), in terms of square roots. -/
theorem three_sq_w (R S L A γ : ℝ) (hR0 : 0 < R) (hS0 : 0 < S) (hL0 : 0 < L) (hA0 : 0 < A) :
    (R ^ ((3 : ℝ) / 4) * S * L ^ (-(1 : ℝ) / 4) * (R * S) ^ (1 / 4 - γ / 4) *
        A ^ (-(1 : ℝ) / 4)) ^ 2 =
      R ^ ((1 : ℝ) / 2) * R * S ^ 2 * (L ^ ((1 : ℝ) / 2))⁻¹ * (R * S) ^ ((1 - γ) / 2) *
        A ^ (-(1 : ℝ) / 2) := by
  have hX0 : 0 < R * S := mul_pos hR0 hS0
  have hR34 : (R ^ ((3 : ℝ) / 4)) ^ 2 = R ^ ((1 : ℝ) / 2) * R := by
    rw [rpow_sq_eq R hR0 _ ((1 : ℝ) / 2 + 1) (by norm_num), Real.rpow_add hR0, Real.rpow_one]
  have hL14' : (L ^ (-(1 : ℝ) / 4)) ^ 2 = (L ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [rpow_sq_eq _ hL0 _ (-((1 : ℝ) / 2)) (by norm_num), Real.rpow_neg hL0.le]
  have hX2 : ((R * S) ^ (1 / 4 - γ / 4)) ^ 2 = (R * S) ^ ((1 - γ) / 2) :=
    rpow_sq_eq _ hX0 _ _ (by ring)
  have hA14' : (A ^ (-(1 : ℝ) / 4)) ^ 2 = A ^ (-(1 : ℝ) / 2) :=
    rpow_sq_eq _ hA0 _ _ (by norm_num)
  simp only [mul_pow]
  rw [hR34, hL14', hX2, hA14']

/-- Song 2020, page 7, the last line of the passage to "So we have T(R,S) << ...": if
T^2 <= K (P + Ci X + 2 Ci W) with X <= 2 Q, then T^2 <= K (1 + 2 Ci) (P + Q + W). Purely
linear in the named products. -/
theorem three_lin (Cw Ci P Q W X T2 : ℝ) (hCw : 0 ≤ Cw) (hCi : 0 ≤ Ci) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hX : X ≤ 2 * Q) (hT : T2 ≤ Cw * (P + (Ci * X + 2 * Ci * W))) :
    T2 ≤ Cw * (1 + 2 * Ci) * (P + Q + W) := by
  have h1 : Cw * (Ci * X) ≤ Cw * (Ci * (2 * Q)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hCi) hCw
  have h2 : 0 ≤ Cw * (Ci * P) := mul_nonneg hCw (mul_nonneg hCi hP)
  have h3 : 0 ≤ Cw * Q := mul_nonneg hCw hQ
  have h4 : 0 ≤ Cw * W := mul_nonneg hCw hW
  have e1 : Cw * (P + (Ci * X + 2 * Ci * W)) =
      Cw * P + Cw * (Ci * X) + 2 * (Cw * (Ci * W)) := by ring
  have e2 : Cw * (1 + 2 * Ci) * (P + Q + W) =
      Cw * P + Cw * (Ci * (2 * Q)) + 2 * (Cw * (Ci * W)) + 2 * (Cw * (Ci * P)) + Cw * Q +
        Cw * W := by ring
  rw [e2]; rw [e1] at hT
  linarith

/-- Song 2020, page 7, the passage to "So we have T(R,S) << ..." over plain real atoms:
r, lam, u, v, a, a' stand for R^(1/2), L^(1/2), x^((gamma-1)/2), x^((1-gamma)/2), |h|^(1/2),
|h|^(-1/2), and p, q, w for the three terms of the display. The length of I is at most
2 y / S, each summed term is the square of the matching term, and the square root is taken. -/
theorem three_alg (Cw Ci r lam u v a a' R Lr S y p q w T : ℝ) (hCw : 0 ≤ Cw) (hCi : 0 ≤ Ci)
    (hr : 0 < r) (hlam : 0 < lam) (hu : 0 < u) (ha : 0 < a)
    (hS0 : 0 < S) (hSy : S ≤ y) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hw0 : 0 ≤ w)
    (hrR : r ^ 2 = R) (hlamL : lam ^ 2 = Lr)
    (hp2 : p ^ 2 = (R * S) ^ 2 / Lr)
    (hq2 : q ^ 2 = r * S * lam * u * y * a)
    (hw2 : w ^ 2 = r * R * S ^ 2 * lam⁻¹ * v * a')
    (hT : T ^ 2 ≤ Cw * ((R * S) ^ 2 / Lr + R * S ^ 2 / Lr *
      (Ci * ((y / S + 1) * (r⁻¹ * u * a) * (Lr * lam) + r * v * a' * (2 * lam))))) :
    T ≤ Real.sqrt (Cw * (1 + 2 * Ci)) * (p + q + w) := by
  subst hrR
  subst hlamL
  have hy1 : y / S + 1 ≤ 2 * (y / S) := by
    have : 1 ≤ y / S := by rw [le_div_iff₀ hS0]; linarith
    linarith
  have b1 : r ^ 2 * S ^ 2 / lam ^ 2 * (Ci * ((y / S + 1) * (r⁻¹ * u * a) * (lam ^ 2 * lam) +
      r * v * a' * (2 * lam))) =
      Ci * ((y / S + 1) * (r * S ^ 2 * u * a * lam)) + 2 * Ci * w ^ 2 := by
    rw [hw2]; field_simp
  have b2 : (y / S + 1) * (r * S ^ 2 * u * a * lam) ≤ 2 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hy1 (show 0 ≤ r * S ^ 2 * u * a * lam by positivity)
    refine h.trans (le_of_eq ?_)
    rw [hq2]; field_simp
  rw [b1, ← hp2] at hT
  have hC' : 0 ≤ Cw * (1 + 2 * Ci) := by positivity
  have hmain : T ^ 2 ≤ Cw * (1 + 2 * Ci) * (p ^ 2 + q ^ 2 + w ^ 2) :=
    three_lin Cw Ci (p ^ 2) (q ^ 2) (w ^ 2) _ _ hCw hCi (sq_nonneg p) (sq_nonneg q)
      (sq_nonneg w) b2 hT
  have hB0 : 0 ≤ Real.sqrt (Cw * (1 + 2 * Ci)) * (p + q + w) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hsq : p ^ 2 + q ^ 2 + w ^ 2 ≤ (p + q + w) ^ 2 := by
    have e : (p + q + w) ^ 2 = p ^ 2 + q ^ 2 + w ^ 2 + 2 * (p * q) + 2 * (p * w) +
        2 * (q * w) := by ring
    have := mul_nonneg hp0 hq0
    have := mul_nonneg hp0 hw0
    have := mul_nonneg hq0 hw0
    rw [e]; linarith
  have hfin : T ^ 2 ≤ (Real.sqrt (Cw * (1 + 2 * Ci)) * (p + q + w)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC']
    exact hmain.trans (mul_le_mul_of_nonneg_left hsq hC')
  exact le_of_sq_le_sq hfin hB0

/-- Song 2020, page 7, the passage from the Lemma 2.5 display with the Cor. 8.13 bound put
in to "So we have T(R,S) << ...": sum over l, use that the length of I is at most 2 y / S,
note that each of the three resulting terms is the square of the matching term of the
display, with x = R S, and take the square root. -/
theorem three_arith (Cw Ci R S y A γ T : ℝ) (L : ℕ) (hCw : 0 ≤ Cw) (hCi : 0 ≤ Ci)
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hSy : S ≤ y) (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hT : T ^ 2 ≤ Cw * ((R * S) ^ 2 / L + R * S ^ 2 / L * ∑ l ∈ Finset.Icc 1 L,
      Ci * ((y / S + 1) * (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
                (A * l) ^ ((1 : ℝ) / 2)) +
              R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) *
                (A * l) ^ (-(1 : ℝ) / 2)))) :
    T ≤ Real.sqrt (Cw * (1 + 2 * Ci)) * (R * S * (L : ℝ) ^ (-(1 : ℝ) / 2) +
              R ^ ((3 : ℝ) / 4) * S * (L : ℝ) ^ ((1 : ℝ) / 4) * (R * S) ^ (γ / 4 - 3 / 4) *
                y ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 4) +
              R ^ ((3 : ℝ) / 4) * S * (L : ℝ) ^ (-(1 : ℝ) / 4) * (R * S) ^ (1 / 4 - γ / 4) *
                A ^ (-(1 : ℝ) / 4)) := by
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hy0 : 0 < y := by linarith
  have hA0 : 0 < A := by linarith
  have hX0 : 0 < R * S := mul_pos hR0 hS0
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hc : (0 : ℝ) ≤ R * S ^ 2 / L := by positivity
  have hT' := hT.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (three_sum Ci R S y A γ L hCi hR0 hS0 hy0 hA0) hc)) hCw)
  have hrR : (R ^ ((1 : ℝ) / 2)) ^ 2 = R := by
    rw [rpow_sq_eq R hR0 _ 1 (by norm_num), Real.rpow_one]
  have hlamL : ((L : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = L := by
    rw [rpow_sq_eq _ hL0 _ 1 (by norm_num), Real.rpow_one]
  exact three_alg Cw Ci (R ^ ((1 : ℝ) / 2)) ((L : ℝ) ^ ((1 : ℝ) / 2))
    ((R * S) ^ ((γ - 1) / 2)) ((R * S) ^ ((1 - γ) / 2)) (A ^ ((1 : ℝ) / 2))
    (A ^ (-(1 : ℝ) / 2)) R L S y _ _ _ T hCw hCi
    (Real.rpow_pos_of_pos hR0 _) (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hX0 _)
    (Real.rpow_pos_of_pos hA0 _)
    hS0 hSy (by positivity) (by positivity) (by positivity) hrR hlamL
    (three_sq_p R S L hL0) (three_sq_q R S L y A γ hR0 hS0 hL0 hy0 hA0)
    (three_sq_w R S L A γ hR0 hS0 hL0 hA0) hT'

/-- Proved from weyl_shift and inner_vdc: Song 2020, page 7, "So we have T(R,S) <<
x L^(-1/2) + R^(3/4) S L^(1/4)
x^(gamma/4-3/4) y^(1/2) |h|^(1/4) + R^(3/4) S L^(-1/4) x^(1/4-gamma/4) |h|^(-1/4)", for every
integer L with 1 <= L <= S, with x = R S. The hypothesis S <= y is what makes the length of
I at most 2 y / S, which is the print's y R / x. -/
theorem three_term :
    ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : ℝ), 0 < y → ∀ (α t : ℝ)
      (h : ℤ), h ≠ 0 → ∀ a b : ℕ → ℂ, (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖b s‖ ≤ 1) →
        ∀ R S : ℝ, 1 ≤ R → 1 ≤ S → S ≤ y → ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ S →
          ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
                if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
                  a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
                else 0‖ ≤
            C * (R * S * (L : ℝ) ^ (-(1 : ℝ) / 2) +
              R ^ ((3 : ℝ) / 4) * S * (L : ℝ) ^ ((1 : ℝ) / 4) * (R * S) ^ (γ / 4 - 3 / 4) *
                y ^ ((1 : ℝ) / 2) * |(h : ℝ)| ^ ((1 : ℝ) / 4) +
              R ^ ((3 : ℝ) / 4) * S * (L : ℝ) ^ (-(1 : ℝ) / 4) * (R * S) ^ (1 / 4 - γ / 4) *
                |(h : ℝ)| ^ (-(1 : ℝ) / 4)) := by
  intro γ hγ0 hγ1
  obtain ⟨Cw, hCw, hw⟩ := SPLIT_typeII_per_RS.weyl_shift
  obtain ⟨Ci, hCi, hi⟩ := SPLIT_typeII_per_RS.inner_vdc γ hγ0 hγ1
  refine ⟨Real.sqrt (Cw * (1 + 2 * Ci)), Real.sqrt_nonneg _, ?_⟩
  intro n y hy α t h hh a b ha hb R S hR hS hSy L hL hLS
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hA : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have key := hw n y α t γ h a b ha hb R S hR hS L hL hLS
    (fun l : ℕ => Ci * ((y / S + 1) * (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
                (|(h : ℝ)| * l) ^ ((1 : ℝ) / 2)) +
              R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) *
                (|(h : ℝ)| * l) ^ (-(1 : ℝ) / 2)))
    (fun l => by positivity)
    (fun l hl1 _ s hs hsl => hi n y hy α t h hh R S hR hS l s hl1 hs hsl)
  exact three_arith Cw Ci R S y |(h : ℝ)| γ _ L hCw hCi hR hS hSy hA hL key

end

end LeanLab.Song2020.RouteTypeIIThree
