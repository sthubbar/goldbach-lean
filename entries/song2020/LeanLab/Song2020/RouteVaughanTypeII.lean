module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.Akeno2026.Vaughan86
public import LeanLab.Song2020.RouteTypeIIChoose

/-!
AI wrote the Lean code, 2026-11-15, the Sigma 2 and Sigma 3 pieces of vaughan_uv.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 6 and 7: from
"For Sigma2, we use dyadic division" to the displays for x^(-epsilon) Sigma2 and
x^(-epsilon) Sigma3.
This file routes the two page 7 displays one level deeper. The only open input is the single
The step typeII_bound, the paper's display for T(R,S) with general bounded coefficients, which
the paper gets from Graham and Kolesnik Lemma 2.5, Iwaniec and Kowalski Corollary 8.13 and
Graham and Kolesnik Lemma 2.4. Proved here from that leaf: the dyadic division, the
normalisation of the coefficients, the summation over the dyadic blocks with R > u/2 and R at
most n/v for Sigma 2 or at most u v for Sigma 3, and the absorption of all logarithms into
n^epsilon. The file defines nothing.

Reading of the leaf typeII_bound. The paper's T(R,S) is the sum over r ~ R of a_r times the
sum over s ~ S with |r s - n/3| < z of b_s e(R_b(r s)), with |a_r| and |b_s| at most 1.
Deviations from the print: r ~ R is read as R at most r < 2 R and likewise for s, so that
the powers of two R = 2^i cover every positive integer exactly once; R and S are any reals
at least 1, with no condition tying R S to n, since for R S far above n the sum is empty and
for R S far below n the window forces y of size n and the display with n in place of
R S still dominates, every term of the paper's bound before the choice of L being
nondecreasing in R S; x is replaced by n; R_b(x) is alpha x + h x^gamma with alpha free; the
window is the initial segment |r s - n/3| < y and r s at most t; a harmless factor
n^epsilon is allowed; the constant C depends on gamma and epsilon only.

How Sigma 2 is grouped here. The coefficient of (mu - mu_u) * (Lambda - Lambda_v) * zeta is
read as the convolution of a = mu - mu_u, of modulus at most 1 and supported on r > u, with
b = (Lambda - Lambda_v) * zeta, which satisfies 0 at most b(s) at most log s and is supported
on s > v. The paper instead puts the divisor sum on the r side; the grouping here needs no
divisor bound and gives the same display, since r > u and r s at most n and s > v still
hold. For Sigma 3 the coefficient is a = g - g_u with g = mu_u * Lambda_v, of modulus at most
log r and supported on u < r at most u v, and b = 1.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteVaughanTypeII

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Akeno2026.Vaughan86
open scoped Classical

noncomputable section

/-- Song 2020, page 7, the display "T(R,S) << R^(-1/6) n^((gamma+3)/6) y^(1/3)
|h|^(1/6) + n^(1-gamma/4) |h|^(-1/4) + R^(1/2) n^(1/2) + R^(-1/4) n^((gamma+1)/4) y^(1/2)
|h|^(1/4) + n^(3/4) y^(1/4) R^(-1/4)" for T(R,S) = sum over r ~ R of a_r, sum over s ~ S
with |r s - n/3| < z, of b_s e(R_b(r s)), with |a_r|, |b_s| at most 1. Citation wall: Graham
and Kolesnik Lemmas 2.5 and 2.4, Iwaniec and Kowalski Corollary 8.13. Deviations are listed
in the header of this file under "Reading of the leaf typeII_bound". -/
theorem typeII_bound :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ a b : ℕ → ℂ, (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖b s‖ ≤ 1) →
            ∀ R S : ℝ, 1 ≤ R → 1 ≤ S →
            ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
                if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
                  a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
                else 0‖ ≤
              C * (n : ℝ) ^ ε *
                (R ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                R ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4)) +
                R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))) := by
  exact RouteTypeIIChoose.typeII_route

/-- Song 2020, page 5, Lemma 3.2 and the definition of Sigma 2: a Dirichlet convolution at a
positive x below M is the double sum over r and s with r s = x. -/
private theorem conv_apply_eq (a b : ArithmeticFunction ℝ) (M x : ℕ) (hx0 : x ≠ 0)
    (hxM : x < M) :
    (a * b) x = ∑ r ∈ Finset.Icc 1 (M - 1), ∑ s ∈ Finset.range M,
      if r * s = x then a r * b s else 0 := by
  rw [ArithmeticFunction.mul_apply,
    ← Finset.sum_product' _ _ (fun r s : ℕ => if r * s = x then a r * b s else 0),
    ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨r, s⟩
  simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨h, _⟩
    have hr : r ≠ 0 := by
      rintro rfl
      exact hx0 (by rw [← h, Nat.zero_mul])
    have hs : s ≠ 0 := by
      rintro rfl
      exact hx0 (by rw [← h, Nat.mul_zero])
    have h1 : r ≤ x := h ▸ Nat.le_mul_of_pos_right r (Nat.pos_of_ne_zero hs)
    have h2 : s ≤ x := h ▸ Nat.le_mul_of_pos_left s (Nat.pos_of_ne_zero hr)
    exact ⟨⟨⟨Nat.pos_of_ne_zero hr, by omega⟩, by omega⟩, h⟩
  · rintro ⟨_, h⟩
    exact ⟨h, hx0⟩

/-- Song 2020, page 6, the definition of Sigma 2 as a double sum: a window sum of a Dirichlet
convolution a * b against G is the sum over r of a(r) times the inner sum over s of b(s)
G(r s), with r s restricted to the window. -/
private theorem conv_window_reindex (a b : ArithmeticFunction ℝ) (G : ℕ → ℂ) (M : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (hP0 : ¬ P 0) (hPM : ∀ x, P x → x < M) :
    ∑ x ∈ (Finset.range M).filter P, ((a * b) x : ℂ) * G x =
      ∑ r ∈ Finset.Icc 1 (M - 1), (a r : ℂ) *
        ∑ s ∈ Finset.range M, (b s : ℂ) * (if P (r * s) then G (r * s) else 0) := by
  have hstep : ∀ x ∈ (Finset.range M).filter P, ((a * b) x : ℂ) * G x =
      ∑ r ∈ Finset.Icc 1 (M - 1), ∑ s ∈ Finset.range M,
        if r * s = x then (a r : ℂ) * (b s : ℂ) * G (r * s) else 0 := by
    intro x hx
    have hxP : P x := (Finset.mem_filter.mp hx).2
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hP0 hxP
    rw [conv_apply_eq a b M x hx0 (hPM x hxP)]
    simp only [Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_mul,
      Complex.ofReal_zero]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_ite_eq ((Finset.range M).filter P) (r * s)
    (fun _ => (a r : ℂ) * (b s : ℂ) * G (r * s))]
  by_cases hP : P (r * s)
  · have hmem : r * s ∈ (Finset.range M).filter P :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hPM _ hP), hP⟩
    simp only [hP, hmem, ite_true]
    ring
  · have hmem : r * s ∉ (Finset.range M).filter P := fun hmem => hP (Finset.mem_filter.mp hmem).2
    simp only [hP, hmem, ite_false]
    ring

/-- Song 2020, page 6, "we use dyadic division", for one variable: a sum over r < M of a
function vanishing at 0 is the sum over i of the sums over the dyadic blocks
2^i at most r < 2^(i+1), and i runs over at most log_2 M + 1 values. -/
private theorem dyadic_sum (M : ℕ) (f : ℕ → ℂ) (hf : f 0 = 0) :
    ∑ r ∈ Finset.range M, f r =
      ∑ i ∈ Finset.range (Nat.log 2 M + 1),
        ∑ r ∈ (Finset.range M).filter
          (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i), f r := by
  have h1 : ∑ r ∈ Finset.range M, f r =
      ∑ r ∈ (Finset.range M).filter (fun r => r ≠ 0), f r := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    by_cases h : r = 0
    · simp [h, hf]
    · simp [h]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := Nat.log 2)
    (t := Finset.range (Nat.log 2 M + 1))]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    have hc : ((2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i) ↔
        (2 ^ i ≤ r ∧ r < 2 ^ (i + 1)) := by
      rw [pow_succ']
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    rw [hc]
    constructor
    · rintro ⟨⟨hM, h0⟩, hl⟩
      exact ⟨hM, (Nat.log_eq_iff (Or.inr ⟨by norm_num, h0⟩)).mp hl⟩
    · rintro ⟨hM, h2⟩
      have h0 : r ≠ 0 := by
        rintro rfl
        have h3 := h2.1
        have h4 : 0 < 2 ^ i := Nat.pos_of_ne_zero (by positivity)
        omega
      exact ⟨⟨hM, h0⟩, (Nat.log_eq_iff (Or.inr ⟨by norm_num, h0⟩)).mpr h2⟩
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hr.1.le))

/-- Song 2020, page 6, "we use dyadic division we can write Sigma2 << x^epsilon sum over
R, S of |T(R,S)|": the window sum of a Dirichlet convolution a * b against G is at most the
sum over the pairs of dyadic blocks R = 2^i, S = 2^j of the moduli of the block sums. -/
private theorem window_dyadic (a b : ArithmeticFunction ℝ) (G : ℕ → ℂ) (M : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (hP0 : ¬ P 0) (hPM : ∀ x, P x → x < M) :
    ‖∑ x ∈ (Finset.range M).filter P, ((a * b) x : ℂ) * G x‖ ≤
      ∑ i ∈ Finset.range (Nat.log 2 M + 1), ∑ j ∈ Finset.range (Nat.log 2 M + 1),
        ‖∑ r ∈ (Finset.range M).filter
            (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i),
          ∑ s ∈ (Finset.range M).filter
            (fun s : ℕ => (2 : ℝ) ^ j ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (2 : ℝ) ^ j),
            if P (r * s) then (a r : ℂ) * (b s : ℂ) * G (r * s) else 0‖ := by
  have hE : ∑ x ∈ (Finset.range M).filter P, ((a * b) x : ℂ) * G x =
      ∑ i ∈ Finset.range (Nat.log 2 M + 1), ∑ j ∈ Finset.range (Nat.log 2 M + 1),
        ∑ r ∈ (Finset.range M).filter
            (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i),
          ∑ s ∈ (Finset.range M).filter
            (fun s : ℕ => (2 : ℝ) ^ j ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (2 : ℝ) ^ j),
            if P (r * s) then (a r : ℂ) * (b s : ℂ) * G (r * s) else 0 := by
    rw [conv_window_reindex a b G M P hP0 hPM]
    have hF0 : ((a 0 : ℝ) : ℂ) * ∑ s ∈ Finset.range M,
        (b s : ℂ) * (if P (0 * s) then G (0 * s) else 0) = 0 := by
      simp [hP0]
    have hsub : ∑ r ∈ Finset.Icc 1 (M - 1), (a r : ℂ) *
        ∑ s ∈ Finset.range M, (b s : ℂ) * (if P (r * s) then G (r * s) else 0) =
        ∑ r ∈ Finset.range M, (a r : ℂ) *
        ∑ s ∈ Finset.range M, (b s : ℂ) * (if P (r * s) then G (r * s) else 0) := by
      refine Finset.sum_subset ?_ ?_
      · intro r hr
        rw [Finset.mem_Icc] at hr
        exact Finset.mem_range.mpr (by omega)
      · intro r hr hr'
        rw [Finset.mem_range] at hr
        rw [Finset.mem_Icc] at hr'
        have hr0 : r = 0 := by omega
        rw [hr0]
        exact hF0
    rw [hsub, dyadic_sum M _ hF0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [dyadic_sum M (fun s => (b s : ℂ) * (if P (r * s) then G (r * s) else 0))
      (by simp [hP0]), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · ring
    · ring
  rw [hE]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact norm_sum_le _ _

/-- Song 2020, page 7, "So we have x^(-epsilon) Sigma2 <<", the passage from R to u: for a
dyadic block with u < 2 R and an exponent e between -1 and 0, R^e is at most 2 u^e. -/
private theorem rpow_dyadic_le (u R e : ℝ) (hu : 0 < u) (hR : u < 2 * R) (he0 : e ≤ 0)
    (he1 : -1 ≤ e) : R ^ e ≤ 2 * u ^ e := by
  have h1 : R ^ e ≤ (u / 2) ^ e :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he0
  rw [Real.div_rpow hu.le (by norm_num)] at h1
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ e :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
  have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg_one]
    norm_num
  rw [h3] at h2
  have h2pos : 0 < (2 : ℝ) ^ e := by positivity
  rw [le_div_iff₀ h2pos] at h1
  have hR0 : 0 ≤ R ^ e := Real.rpow_nonneg (by linarith) e
  nlinarith [mul_le_mul_of_nonneg_left h2 hR0]

/-- Song 2020, pages 6 and 7, from "we use dyadic division" to the displays for Sigma 2 and
Sigma 3, in general form: for a convolution a * b with |a| at most K, |b| at most L, whose
nonzero terms in the window have u < r at most W, the window sum is at most
K L (log_2 M + 1)^2 2 D times the display with R^(1/2) replaced by W^(1/2) and the negative
powers of R by those of u, given the T(R,S) display with constant D for all coefficients of
modulus at most 1. T2 to T5 stand for the R free factors of the display. -/
private theorem conv_typeII (n : ℕ) (y t α γ : ℝ) (h : ℤ) (hy : y ≤ (n : ℝ) / 3)
    (u W D T2 T3 T4 T5 K L : ℝ) (hu : 0 < u) (hW : 0 ≤ W) (hD : 0 ≤ D) (hT2 : 0 ≤ T2)
    (hT3 : 0 ≤ T3) (hT4 : 0 ≤ T4) (hT5 : 0 ≤ T5) (hK : 0 < K) (hL : 0 < L)
    (a b : ArithmeticFunction ℝ)
    (ha : ∀ r : ℕ, r ≤ n → |a r| ≤ K) (hb : ∀ s : ℕ, s ≤ n → |b s| ≤ L)
    (hsupp : ∀ r s : ℕ, a r ≠ 0 → b s ≠ 0 → |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y →
      u < (r : ℝ) ∧ (r : ℝ) ≤ W)
    (hleaf : ∀ a' b' : ℕ → ℂ, (∀ r, ‖a' r‖ ≤ 1) → (∀ s, ‖b' s‖ ≤ 1) →
      ∀ R S : ℝ, 1 ≤ R → 1 ≤ S →
        ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
          ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
            if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
              a' r * b' s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
            else 0‖ ≤
          D * (R ^ (-(1 : ℝ) / 6) * T4 + T2 + R ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) +
            R ^ (-(1 : ℝ) / 4) * T5 + R ^ (-(1 : ℝ) / 4) * T3)) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
        ((a * b) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
      K * L * ((Nat.log 2 (Nat.ceil ((n : ℝ) / 3 + y) + 1) + 1 : ℕ) : ℝ) ^ 2 * (2 * D) *
        (W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) + T2 + u ^ (-(1 : ℝ) / 4) * T3 +
          u ^ (-(1 : ℝ) / 6) * T4 + u ^ (-(1 : ℝ) / 4) * T5) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hMn : Nat.ceil ((n : ℝ) / 3 + y) ≤ n := Nat.ceil_le.mpr (by linarith)
  have hP0 : ¬ (|((0 : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((0 : ℕ) : ℝ) ≤ t) := by
    rintro ⟨h, _⟩
    rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at h
    linarith
  have hPM : ∀ x : ℕ, (|(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t) →
      x < Nat.ceil ((n : ℝ) / 3 + y) + 1 := by
    rintro x ⟨h, _⟩
    have h1 : (x : ℝ) < ((Nat.ceil ((n : ℝ) / 3 + y) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil ((n : ℝ) / 3 + y), (abs_lt.mp h).2]
    exact_mod_cast h1
  have hX : 0 ≤ W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) + T2 + u ^ (-(1 : ℝ) / 4) * T3 +
      u ^ (-(1 : ℝ) / 6) * T4 + u ^ (-(1 : ℝ) / 4) * T5 := by positivity
  have hblock : ∀ i j : ℕ,
      ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i),
        ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun s : ℕ => (2 : ℝ) ^ j ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (2 : ℝ) ^ j),
          if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
            (a r : ℂ) * (b s : ℂ) * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
          else 0‖ ≤
        K * L * (2 * D) *
          (W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) + T2 + u ^ (-(1 : ℝ) / 4) * T3 +
            u ^ (-(1 : ℝ) / 6) * T4 + u ^ (-(1 : ℝ) / 4) * T5) := by
    intro i j
    by_cases hex : ∃ r s : ℕ, ((2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i) ∧
        |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ a r ≠ 0 ∧ b s ≠ 0
    · obtain ⟨r0, s0, hri, hP, har, hbs⟩ := hex
      obtain ⟨hur, hrW⟩ := hsupp r0 s0 har hbs hP
      have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      have hS1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hRu : u < 2 * (2 : ℝ) ^ i := lt_trans hur hri.2
      have hRW : (2 : ℝ) ^ i ≤ W := le_trans hri.1 hrW
      have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
      have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have ha' : ∀ r : ℕ, ‖(if r ≤ n then (a r : ℂ) / (K : ℂ) else 0)‖ ≤ 1 := by
        intro r
        split_ifs with hr
        · rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hK, div_le_one hK]
          exact ha r hr
        · rw [norm_zero]
          exact zero_le_one
      have hb' : ∀ s : ℕ, ‖(if s ≤ n then (b s : ℂ) / (L : ℂ) else 0)‖ ≤ 1 := by
        intro s
        split_ifs with hs
        · rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hL, div_le_one hL]
          exact hb s hs
        · rw [norm_zero]
          exact zero_le_one
      have hl := hleaf (fun r : ℕ => if r ≤ n then (a r : ℂ) / (K : ℂ) else 0)
        (fun s : ℕ => if s ≤ n then (b s : ℂ) / (L : ℂ) else 0) ha' hb' ((2 : ℝ) ^ i)
        ((2 : ℝ) ^ j) hR1 hS1
      have hEq : (∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i),
          ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun s : ℕ => (2 : ℝ) ^ j ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (2 : ℝ) ^ j),
            if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
              (a r : ℂ) * (b s : ℂ) *
                eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
            else 0) =
          ((K * L : ℝ) : ℂ) *
          ∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i),
          ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun s : ℕ => (2 : ℝ) ^ j ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (2 : ℝ) ^ j),
            if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
              (fun r : ℕ => if r ≤ n then (a r : ℂ) / (K : ℂ) else 0) r *
                (fun s : ℕ => if s ≤ n then (b s : ℂ) / (L : ℂ) else 0) s *
                eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
            else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r hr => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        have hrn : r ≤ n := by
          have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
          omega
        have hsn : s ≤ n := by
          have := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
          omega
        simp only [hrn, hsn, ↓reduceIte]
        split_ifs
        · push_cast
          field_simp
        · rw [mul_zero]
      rw [hEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hK hL)]
      have e1 : ((2 : ℝ) ^ i) ^ (-(1 : ℝ) / 6) * T4 ≤ 2 * u ^ (-(1 : ℝ) / 6) * T4 :=
        mul_le_mul_of_nonneg_right
          (rpow_dyadic_le u _ _ hu hRu (by norm_num) (by norm_num)) hT4
      have e2 : ((2 : ℝ) ^ i) ^ (-(1 : ℝ) / 4) * T5 ≤ 2 * u ^ (-(1 : ℝ) / 4) * T5 :=
        mul_le_mul_of_nonneg_right
          (rpow_dyadic_le u _ _ hu hRu (by norm_num) (by norm_num)) hT5
      have e3 : ((2 : ℝ) ^ i) ^ (-(1 : ℝ) / 4) * T3 ≤ 2 * u ^ (-(1 : ℝ) / 4) * T3 :=
        mul_le_mul_of_nonneg_right
          (rpow_dyadic_le u _ _ hu hRu (by norm_num) (by norm_num)) hT3
      have e4 : ((2 : ℝ) ^ i) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) ≤
          W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) hRW (by norm_num)) (by positivity)
      have e5 : 0 ≤ W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := by positivity
      have hdisp : ((2 : ℝ) ^ i) ^ (-(1 : ℝ) / 6) * T4 + T2 +
          ((2 : ℝ) ^ i) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) +
          ((2 : ℝ) ^ i) ^ (-(1 : ℝ) / 4) * T5 + ((2 : ℝ) ^ i) ^ (-(1 : ℝ) / 4) * T3 ≤
          2 * (W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) + T2 + u ^ (-(1 : ℝ) / 4) * T3 +
            u ^ (-(1 : ℝ) / 6) * T4 + u ^ (-(1 : ℝ) / 4) * T5) := by
        linarith
      have hKL : 0 ≤ K * L := (mul_pos hK hL).le
      calc K * L * _ ≤ K * L * (D * (2 * (W ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) + T2 +
            u ^ (-(1 : ℝ) / 4) * T3 + u ^ (-(1 : ℝ) / 6) * T4 + u ^ (-(1 : ℝ) / 4) * T5))) :=
            mul_le_mul_of_nonneg_left
              (hl.trans (mul_le_mul_of_nonneg_left hdisp hD)) hKL
        _ = _ := by ring
    · have hz : (∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun r : ℕ => (2 : ℝ) ^ i ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 : ℝ) ^ i),
          ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun s : ℕ => (2 : ℝ) ^ j ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (2 : ℝ) ^ j),
            if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
              (a r : ℂ) * (b s : ℂ) *
                eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
            else 0) = 0 := by
        refine Finset.sum_eq_zero (fun r hr => Finset.sum_eq_zero (fun s _ => ?_))
        by_cases hP : |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
          by_cases har : a r = 0
          · rw [har, Complex.ofReal_zero, zero_mul, zero_mul]
          · by_cases hbs : b s = 0
            · rw [hbs, Complex.ofReal_zero, mul_zero, zero_mul]
            · exact absurd ⟨r, s, (Finset.mem_filter.mp hr).2, hP.1, har, hbs⟩ hex
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
      rw [hz, norm_zero]
      have hKL : 0 ≤ K * L := (mul_pos hK hL).le
      positivity
  refine (window_dyadic a b (fun x : ℕ => eC (α * x + h * (x : ℝ) ^ γ)) _
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t) hP0 hPM).trans ?_
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hblock i j).trans
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Song 2020, page 7, the factor x^epsilon of the displays for Sigma 2 and Sigma 3: one
logarithm from the coefficients times the square of the number of dyadic blocks, which is at
most log_2 M + 1 with M at most n + 1, is at most a constant times n^(epsilon/2). -/
private theorem log_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 1 ≤ n → ∀ M : ℕ, 1 ≤ M → M ≤ n + 1 →
      (1 + Real.log n) * ((Nat.log 2 M + 1 : ℕ) : ℝ) ^ 2 * 2 ≤ c * (n : ℝ) ^ (ε / 2) := by
  refine ⟨18 * (1 + 6 / ε) ^ 3, by positivity, ?_⟩
  intro n hn M hM1 hMn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hk : ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ 3 * (1 + Real.log n) := by
    have h1 : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 (by omega)
    have h2 : (2 : ℝ) ^ Nat.log 2 M ≤ 2 * n := by
      have h2' : 2 ^ Nat.log 2 M ≤ 2 * n := by omega
      exact_mod_cast h2'
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, Real.log_mul (by norm_num) hnpos.ne'] at h3
    have h4 := Real.log_two_gt_d9
    have h5 := Real.log_two_lt_d9
    have hk0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
    have h6 := mul_nonneg hk0 (sub_nonneg.mpr h4.le)
    push_cast
    linarith
  have hpow : 1 + Real.log n ≤ (1 + 6 / ε) * (n : ℝ) ^ (ε / 6) := by
    have h1 := Real.log_le_rpow_div (x := (n : ℝ)) hnpos.le (show 0 < ε / 6 by positivity)
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ (ε / 6) := Real.one_le_rpow hn1 (by positivity)
    have h3 : (n : ℝ) ^ (ε / 6) / (ε / 6) = 6 / ε * (n : ℝ) ^ (ε / 6) := by
      field_simp
    rw [h3] at h1
    linarith
  have hcube : ((n : ℝ) ^ (ε / 6)) ^ 3 = (n : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    push_cast
    ring
  have hA : 0 ≤ 1 + Real.log n := by linarith
  have hk0 : (0 : ℝ) ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc (1 + Real.log n) * ((Nat.log 2 M + 1 : ℕ) : ℝ) ^ 2 * 2
      ≤ (1 + Real.log n) * (3 * (1 + Real.log n)) ^ 2 * 2 := by gcongr
    _ = 18 * (1 + Real.log n) ^ 3 := by ring
    _ ≤ 18 * ((1 + 6 / ε) * (n : ℝ) ^ (ε / 6)) ^ 3 := by gcongr
    _ = 18 * (1 + 6 / ε) ^ 3 * (n : ℝ) ^ (ε / 2) := by
        rw [mul_pow, hcube]
        ring

/-- Song 2020, page 7, the factor x^epsilon again: the constant of the T(R,S) display at
epsilon/2 times the logarithmic factor of log_factor gives one constant times n^epsilon. -/
private theorem absorb (A K L Kd2 C0 E1 E c X : ℝ) (hX : 0 ≤ X) (hC0 : 0 ≤ C0)
    (hE1 : 0 ≤ E1) (hE : E1 * E1 = E) (h1 : A ≤ K * L * Kd2 * (2 * (C0 * E1)) * X)
    (h2 : K * L * Kd2 * 2 ≤ c * E1) : A ≤ C0 * c * E * X := by
  have h3 : C0 * E1 * (K * L * Kd2 * 2) * X ≤ C0 * E1 * (c * E1) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hE1)) hX
  calc A ≤ C0 * E1 * (K * L * Kd2 * 2) * X := by linarith
    _ ≤ C0 * E1 * (c * E1) * X := h3
    _ = C0 * c * E * X := by
        rw [← hE]
        ring

/-- Song 2020, page 5, Lemma 3.2: the value of f minus its cut at U, which is f above U and
zero at arguments at most U. Used for mu - mu_u, Lambda - Lambda_v and the part r > u of
mu_u * Lambda_v. -/
private theorem sub_short_apply (f : ArithmeticFunction ℝ) (U : ℝ) (r : ℕ) :
    (f - shortPart f U) r = if (r : ℝ) ≤ U then 0 else f r := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  show f r + -(if (r : ℝ) ≤ U then f r else 0) = _
  split_ifs <;> simp

/-- Song 2020, page 5, Lemma 3.2: the Moebius function has modulus at most one. -/
private theorem abs_mu_le_one (r : ℕ) :
    |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) r| ≤ 1 := by
  rw [ArithmeticFunction.intCoe_apply]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r))

/-- Song 2020, page 6, the coefficient b_s of Sigma 2 in the grouping of this file: the sum
of Lambda(d) over the divisors d > v of s has modulus at most log s. -/
private theorem abs_LV_zeta_le (v : ℝ) (s : ℕ) :
    |((ArithmeticFunction.vonMangoldt - shortPart ArithmeticFunction.vonMangoldt v) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) s| ≤ Real.log s := by
  rw [ArithmeticFunction.coe_mul_zeta_apply, ← ArithmeticFunction.vonMangoldt_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [sub_short_apply]
  split_ifs
  · rw [abs_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg
  · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Song 2020, page 6, "s > v" in T(R,S): the coefficient b_s of Sigma 2 in the grouping of
this file vanishes for s at most v, since every divisor of s is then at most v. -/
private theorem LV_zeta_eq_zero (v : ℝ) (s : ℕ) (hs : (s : ℝ) ≤ v) :
    ((ArithmeticFunction.vonMangoldt - shortPart ArithmeticFunction.vonMangoldt v) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) s = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [sub_short_apply]
  have hds : (d : ℝ) ≤ s := by exact_mod_cast Nat.divisor_le hd
  rw [ite_eq_left_of_eq_true _ _ (eq_true (hds.trans hs))]

/-- Song 2020, page 7, the display "x^(-epsilon) Sigma2 << n v^(-1/2) + n^(1-gamma/4)
|h|^(-1/4) + n^(3/4) y^(1/4) u^(-1/4) + u^(-1/6) n^((gamma+3)/6) y^(1/3) |h|^(1/6) +
u^(-1/4) n^((gamma+1)/4) y^(1/2) |h|^(1/4)", proved from the single leaf typeII_bound by
dyadic division, with R > u/2 and R at most n/v. Same statement as
RouteVaughanLeaves.sigma2_bound. The grouping of the coefficients is described in the header
of this file. -/
theorem sigma2_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
                ((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
                    shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u) *
                  (ArithmeticFunction.vonMangoldt - shortPart ArithmeticFunction.vonMangoldt v) *
                  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
              C * (n : ℝ) ^ ε *
                ((n : ℝ) * v ^ (-(1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  intro γ hγ1 hγ2 ε hε
  obtain ⟨C0, hC0, N0, hleaf⟩ := typeII_bound γ hγ1 hγ2 (ε / 2) (by positivity)
  obtain ⟨c, hc, hlogf⟩ := log_factor ε hε
  refine ⟨C0 * c, mul_nonneg hC0 hc, max N0 1, ?_⟩
  intro n hn y hy1 hy2 α h hh t u v hu hv huv
  have hnN : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := lt_of_le_of_lt (Real.rpow_nonneg hnpos.le _) hy1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have hMn : Nat.ceil ((n : ℝ) / 3 + y) ≤ n := Nat.ceil_le.mpr (by linarith)
  have hE : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hWeq : ((n : ℝ) / v) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) =
      (n : ℝ) * v ^ (-(1 : ℝ) / 2) := by
    have hnn : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = n := by
      rw [← Real.rpow_add hnpos]
      norm_num
    have hvv : v ^ (-(1 : ℝ) / 2) * v ^ ((1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hv0]
      norm_num
    rw [Real.div_rpow hnpos.le hv0.le, div_mul_eq_mul_div,
      div_eq_iff (Real.rpow_pos_of_pos hv0 _).ne', hnn, mul_assoc, hvv, mul_one]
  rw [mul_assoc ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
      shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u)
    (ArithmeticFunction.vonMangoldt - shortPart ArithmeticFunction.vonMangoldt v)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
  have key := conv_typeII n y t α γ h hy2 u ((n : ℝ) / v) (C0 * (n : ℝ) ^ (ε / 2))
    ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4))
    ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))
    ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) * |(h : ℝ)| ^ ((1 : ℝ) / 6))
    ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) * |(h : ℝ)| ^ ((1 : ℝ) / 4))
    1 (1 + Real.log n) hu0 (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) one_pos (by linarith)
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
      shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u)
    ((ArithmeticFunction.vonMangoldt - shortPart ArithmeticFunction.vonMangoldt v) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
    (by
      intro r _
      rw [sub_short_apply]
      split_ifs
      · rw [abs_zero]
        exact zero_le_one
      · exact abs_mu_le_one r)
    (by
      intro s hs
      refine (abs_LV_zeta_le v s).trans ?_
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        linarith
      · have h1 : (0 : ℝ) < s := by exact_mod_cast hpos
        have h2 : (s : ℝ) ≤ n := by exact_mod_cast hs
        linarith [Real.log_le_log h1 h2])
    (by
      intro r s har hbs hP
      have hur : u < (r : ℝ) := by
        by_contra hcon
        apply har
        rw [sub_short_apply, ite_eq_left_of_eq_true _ _ (eq_true (not_lt.mp hcon))]
      have hvs : v < (s : ℝ) := by
        by_contra hcon
        exact hbs (LV_zeta_eq_zero v s (not_lt.mp hcon))
      refine ⟨hur, ?_⟩
      rw [le_div_iff₀ hv0]
      have h1 := (abs_lt.mp hP).2
      push_cast at h1
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith [mul_le_mul_of_nonneg_left hvs.le hr0])
    (fun a' b' ha' hb' R S hR hS => hleaf n hnN y hy1 hy2 α h hh t a' b' ha' hb' R S hR hS)
  rw [hWeq] at key
  refine absorb _ _ _ _ C0 ((n : ℝ) ^ (ε / 2)) _ c _ (by positivity) hC0 (by positivity) hE
    key ?_
  rw [one_mul]
  exact hlogf n hn1 _ (by omega) (by omega)

/-- Song 2020, page 5, Lemma 3.2: the cut Moebius function mu_u has modulus at most one. -/
private theorem abs_muU_le_one (u : ℝ) (r : ℕ) :
    |shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u r| ≤ 1 := by
  show |if (r : ℝ) ≤ u then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) r else 0| ≤ 1
  split_ifs
  · exact abs_mu_le_one r
  · rw [abs_zero]
    exact zero_le_one

/-- Song 2020, pages 5 and 7, the coefficient a_r of Sigma 3: the sum over w t = r of
mu(w) Lambda(t), with the cuts of Lemma 3.2, has modulus at most the sum of Lambda over the
divisors of r, which is log r. -/
private theorem abs_muU_mul_LV_le (u v : ℝ) (r : ℕ) :
    |(shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
      shortPart ArithmeticFunction.vonMangoldt v) r| ≤ Real.log r := by
  rw [ArithmeticFunction.mul_apply, ← ArithmeticFunction.vonMangoldt_sum,
    ← Nat.sum_divisorsAntidiagonal' (fun _ d : ℕ => ArithmeticFunction.vonMangoldt d)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  have h1 := abs_muU_le_one u p.1
  have h2 : |shortPart ArithmeticFunction.vonMangoldt v p.2| ≤
      ArithmeticFunction.vonMangoldt p.2 := by
    show |if (p.2 : ℝ) ≤ v then ArithmeticFunction.vonMangoldt p.2 else 0| ≤ _
    split_ifs
    · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    · rw [abs_zero]
      exact ArithmeticFunction.vonMangoldt_nonneg
  calc _ ≤ 1 * ArithmeticFunction.vonMangoldt p.2 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Song 2020, page 7, "Similarly" for Sigma 3, the range u < R at most u v: the coefficient
mu_u * Lambda_v vanishes at r > u v, since r = w t with w at most u and t at most v. -/
private theorem muU_mul_LV_eq_zero (u v : ℝ) (hu : 0 ≤ u) (r : ℕ) (hr : u * v < (r : ℝ)) :
    (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
      shortPart ArithmeticFunction.vonMangoldt v) r = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hpr : p.1 * p.2 = r := (Nat.mem_divisorsAntidiagonal.mp hp).1
  show (if (p.1 : ℝ) ≤ u then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) p.1 else 0) *
    (if (p.2 : ℝ) ≤ v then ArithmeticFunction.vonMangoldt p.2 else 0) = 0
  by_cases h1 : (p.1 : ℝ) ≤ u
  · by_cases h2 : (p.2 : ℝ) ≤ v
    · exfalso
      have h3 : (r : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by
        rw [← hpr]
        push_cast
        ring
      have h4 := mul_le_mul h1 h2 (Nat.cast_nonneg p.2) hu
      linarith
    · simp [h2]
  · simp [h1]

/-- Song 2020, page 7, the coefficient b_s = 1 of Sigma 3: the real zeta arithmetic function
has modulus at most one. -/
private theorem abs_zeta_le_one (s : ℕ) :
    |(ArithmeticFunction.zeta : ArithmeticFunction ℝ) s| ≤ 1 := by
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
  split_ifs <;> simp

/-- Song 2020, page 7, the display "Similarly we have x^(-epsilon) Sigma3 << n^(1/2)
(u v)^(1/2) + n^(1-gamma/4) |h|^(-1/4) + n^(3/4) y^(1/4) u^(-1/4) + u^(-1/6) n^((gamma+3)/6)
y^(1/3) |h|^(1/6) + u^(-1/4) n^((gamma+1)/4) y^(1/2) |h|^(1/4)", proved from the single leaf
typeII_bound by dyadic division, with R > u/2 and R at most u v. Same statement as
RouteVaughanLeaves.sigma3_bound. -/
theorem sigma3_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
                (((shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
                      shortPart ArithmeticFunction.vonMangoldt v -
                    shortPart (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
                      shortPart ArithmeticFunction.vonMangoldt v) u) *
                  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
              C * (n : ℝ) ^ ε *
                ((n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  intro γ hγ1 hγ2 ε hε
  obtain ⟨C0, hC0, N0, hleaf⟩ := typeII_bound γ hγ1 hγ2 (ε / 2) (by positivity)
  obtain ⟨c, hc, hlogf⟩ := log_factor ε hε
  refine ⟨C0 * c, mul_nonneg hC0 hc, max N0 1, ?_⟩
  intro n hn y hy1 hy2 α h hh t u v hu hv huv
  have hnN : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := lt_of_le_of_lt (Real.rpow_nonneg hnpos.le _) hy1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have hMn : Nat.ceil ((n : ℝ) / 3 + y) ≤ n := Nat.ceil_le.mpr (by linarith)
  have hE : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have key := conv_typeII n y t α γ h hy2 u (u * v) (C0 * (n : ℝ) ^ (ε / 2))
    ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4))
    ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))
    ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) * |(h : ℝ)| ^ ((1 : ℝ) / 6))
    ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) * |(h : ℝ)| ^ ((1 : ℝ) / 4))
    (1 + Real.log n) 1 hu0 (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by linarith) one_pos
    (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
        shortPart ArithmeticFunction.vonMangoldt v -
      shortPart (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
        shortPart ArithmeticFunction.vonMangoldt v) u)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (by
      intro r hr
      rw [sub_short_apply]
      split_ifs
      · rw [abs_zero]
        linarith
      · refine (abs_muU_mul_LV_le u v r).trans ?_
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · rw [h0, Nat.cast_zero, Real.log_zero]
          linarith
        · have h1 : (0 : ℝ) < r := by exact_mod_cast hpos
          have h2 : (r : ℝ) ≤ n := by exact_mod_cast hr
          linarith [Real.log_le_log h1 h2])
    (fun s _ => abs_zeta_le_one s)
    (by
      intro r s har _ _
      rw [sub_short_apply] at har
      constructor
      · by_contra hcon
        exact har (ite_eq_left_of_eq_true _ _ (eq_true (not_lt.mp hcon)))
      · by_contra hcon
        apply har
        rw [muU_mul_LV_eq_zero u v hu0.le r (not_le.mp hcon)]
        exact ite_self 0)
    (fun a' b' ha' hb' R S hR hS => hleaf n hnN y hy1 hy2 α h hh t a' b' ha' hb' R S hR hS)
  rw [mul_comm ((u * v) ^ ((1 : ℝ) / 2)) ((n : ℝ) ^ ((1 : ℝ) / 2))] at key
  refine absorb _ _ _ _ C0 ((n : ℝ) ^ (ε / 2)) _ c _ (by positivity) hC0 (by positivity) hE
    key ?_
  rw [mul_one]
  exact hlogf n hn1 _ (by omega) (by omega)

end

end LeanLab.Song2020.RouteVaughanTypeII
