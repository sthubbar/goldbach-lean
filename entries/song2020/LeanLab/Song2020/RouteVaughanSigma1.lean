module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.Akeno2026.Vaughan86
public import LeanLab.Song2020.RouteVaughanInner

/-!
AI wrote the Lean code, 2026-11-15, the Sigma 1 piece of vaughan_uv.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 5 and 6: the
definition of Sigma 1, the display "By partial summation Sigma1 << log x sum over r at most u
of max over z of the inner sum over s of e(R_b(r s))", and the display
"Sigma1 << log^2 x (u |h|^(1/2) x^(gamma/2-1) y + x^(1-gamma/2) |h|^(-1/2))".
This file routes the Sigma 1 statement used by RouteVaughanUV one level deeper: the only open
input is the inner sum over s for one fixed r, the paper's use of Iwaniec and Kowalski
Corollary 8.13, the van der Corput second derivative estimate. The partial summation that
removes log s and the summation over r at most u are proved here. It defines nothing.

How the paper's pieces map to the lab's proved Vaughan identity
LeanLab.Akeno2026.Vaughan86.vaughan_weighted_identity, whose four terms are, with mu_u the
Moebius function cut at arguments at most u and Lambda_v the von Mangoldt function cut at
arguments at most v, written with the existing definition Vaughan86.shortPart:
  A = mu_u * log,  B = mu_u * Lambda_v * zeta,  E = Lambda_v,
  D = (mu - mu_u) * (Lambda - Lambda_v) * zeta,   Lambda = A - B + E + D.
B is split at r at most u, where r = w t is the argument of g = mu_u * Lambda_v:
  B1 = shortPart g u * zeta,  B3 = (g - shortPart g u) * zeta,  B = B1 + B3.
Then the paper's Sigma 1 is the window sum of A minus the window sum of B1, the paper's
Sigma 3 is minus the window sum of B3, where r at most u v holds automatically, and the
paper's Sigma 2 is the window sum of D: the coefficient of D at x is the sum over x = r s,
s > v, of Lambda(s) times the sum of mu(d) over d dividing r with d > u, which forces r > u,
and for r > 1 that inner sum is minus the sum of mu(d) over d dividing r with d at most u,
which is the print's form with its minus sign. The term E, the short von Mangoldt sum, does
not appear in the paper, whose window sits above v; it is bounded trivially in
RouteVaughanUV.

Deviations from the print, the same in every statement here and the same as in the existing
statement SPLIT_vaughan_per_u.vaughan_uv: the phase R_b(x) is written alpha x + h x^gamma
with alpha free, which covers beta x - b x / q; the window is the initial segment
|x - n/3| < y and x at most t of the existing statement, covering the paper's maximum over
z; x is replaced by n in every power; the paper's log x, log^2 x and x^epsilon factors are
all carried by one factor n^epsilon; the implied constant is C, depending on gamma and
epsilon only, valid for n at least N0; u and v are free reals with 1 at most u, 1 at most v
and u v at most n; h is any nonzero integer.

Reading of the inner sum leaf, inner_sum_bound: the bound is the number of terms times the
square root of the second derivative plus the inverse square root. Deviations from the
print: x is replaced by n; the factor n^epsilon carries the logarithm of the dyadic division
in r s that is needed when y is close to n/3 and the window reaches small r s, where r s is
no longer of size n; R_b(x) is alpha x + h x^gamma with alpha free; r is any positive
integer; the initial segment is s at most tau.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteVaughanSigma1

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Akeno2026.Vaughan86
open scoped Classical

noncomputable section

/-- Song 2020, page 6, "Let f(s) = R_b(r s), and noting that r s ~ n and f''(s) is of
size r^2 n^(gamma-2) |h|. And applying the van der Corput's estimate in [3] (Cor. 8.13) to
f(s) in the inner sum": for one fixed r the sum over s of e(R_b(r s)), over any initial
segment of the window |r s - n/3| < y, is at most
|h|^(1/2) n^(gamma/2-1) y + r^(-1) n^(1-gamma/2) |h|^(-1/2). Citation wall: Iwaniec and
Kowalski Corollary 8.13. Deviations are listed in the header of this file under
"Reading of the inner sum leaf".
Proved from RouteVaughanInner.inner_sum_bound_route. -/
theorem inner_sum_bound :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ r : ℕ, 1 ≤ r → ∀ τ : ℝ,
            ‖∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ (s : ℝ) ≤ τ),
                eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)‖ ≤
              C * (n : ℝ) ^ ε *
                (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y +
                  (r : ℝ)⁻¹ * ((n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2))) := by
  exact RouteVaughanInner.inner_sum_bound_route

/-- Song 2020, page 6, "By partial summation": Abel summation against a nonnegative
nondecreasing weight, the paper's log s. If every initial partial sum of c has modulus at
most B and the weight is at most L on the range, the weighted sum has modulus at most
2 L B. -/
private theorem abel_mono (m : ℕ) (w : ℕ → ℝ) (c : ℕ → ℂ) (L B : ℝ) (hL0 : 0 ≤ L)
    (hw0 : ∀ s, 0 ≤ w s) (hmono : ∀ s, w s ≤ w (s + 1)) (hL : ∀ s, s < m → w s ≤ L)
    (hB : ∀ j, j ≤ m → ‖∑ s ∈ Finset.range j, c s‖ ≤ B) :
    ‖∑ s ∈ Finset.range m, (w s : ℂ) * c s‖ ≤ 2 * L * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le _)
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have hparts := Finset.sum_range_by_parts (fun i : ℕ => w i) (fun i : ℕ => c i) (k + 1)
  simp only [Nat.add_sub_cancel] at hparts
  have h1 : ‖w k • (∑ i ∈ Finset.range (k + 1), c i)‖ ≤ w k * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 k)]
    exact mul_le_mul_of_nonneg_left (hB (k + 1) le_rfl) (hw0 k)
  have h2 : ‖∑ i ∈ Finset.range k,
      (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), c j)‖ ≤ (w k - w 0) * B := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range k,
        ‖(w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), c j)‖ ≤ (w (i + 1) - w i) * B := by
      intro i hi
      have hnonneg : 0 ≤ w (i + 1) - w i := by linarith [hmono i]
      have hik : i + 1 ≤ k + 1 := by have := Finset.mem_range.mp hi; omega
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left (hB (i + 1) hik) hnonneg
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun i : ℕ => w i) k]
  have hwk : w k ≤ L := hL k (Nat.lt_succ_self k)
  calc ‖∑ s ∈ Finset.range (k + 1), (w s : ℂ) * c s‖
      = ‖w k • (∑ i ∈ Finset.range (k + 1), c i) -
          ∑ i ∈ Finset.range k,
            (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), c j)‖ := by
        rw [← hparts]
        congr 1
    _ ≤ w k * B + (w k - w 0) * B := (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ ≤ 2 * L * B := by
        nlinarith [hw0 0, hw0 k, mul_nonneg (hw0 0) hB0, mul_le_mul_of_nonneg_right hwk hB0]

/-- Song 2020, page 5, Lemma 3.2 and the definition of Sigma 1: a Dirichlet convolution at a
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

/-- Song 2020, page 5, the definition of Sigma 1 as a double sum: a window sum of a Dirichlet
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

/-- Song 2020, page 6, the summation over r at most u of r^(-1): the harmonic sum up to m is
at most 1 + log m, which is one of the two logarithms of the display for Sigma 1. -/
private theorem sum_inv_le (m : ℕ) :
    ∑ r ∈ Finset.Icc 1 m, ((r : ℝ))⁻¹ ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- Song 2020, page 6, the summation over r at most u: there are at most u such r. -/
private theorem sum_indicator_le (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ∑ r ∈ Finset.Icc 1 m, (if (r : ℝ) ≤ u then (1 : ℝ) else 0) ≤ u := by
  rw [Finset.sum_boole]
  have hsub : (Finset.Icc 1 m).filter (fun r : ℕ => (r : ℝ) ≤ u) ⊆ Finset.Icc 1 ⌊u⌋₊ := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    exact Finset.mem_Icc.mpr ⟨hr.1.1, Nat.le_floor hr.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  calc ((((Finset.Icc 1 m).filter (fun r : ℕ => (r : ℝ) ≤ u)).card : ℕ) : ℝ)
      ≤ ((⌊u⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ u := Nat.floor_le hu

/-- Song 2020, page 5, Lemma 3.2: the cut Moebius function mu_u has modulus at most one. -/
private theorem abs_muU_le_one (u : ℝ) (r : ℕ) :
    |shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u r| ≤ 1 := by
  show |if (r : ℝ) ≤ u then (ArithmeticFunction.moebius : ArithmeticFunction ℝ) r else 0| ≤ 1
  split_ifs
  · rw [ArithmeticFunction.intCoe_apply]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r))
  · rw [abs_zero]
    exact zero_le_one

/-- Song 2020, page 5 and 6, the coefficient of the second part of Sigma 1: the sum over
w t = r of mu(w) Lambda(t), with the cuts of Lemma 3.2, has modulus at most the sum of
Lambda over the divisors of r, which is log r. -/
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

/-- Song 2020, page 6, from "By partial summation" to the display for Sigma 1, in general
form: for a convolution a * b whose first factor is supported on r at most u with modulus
at most K, and whose second factor is a nonnegative nondecreasing weight at most L, the
window sum against G is bounded by summing over r at most u the partial summation bound
2 L (B1 + B2 / r), given the bound B1 + B2 / r for every initial segment of the inner sum
over s. The paper uses it with b = log and with b = 1. -/
private theorem conv_bound (n : ℕ) (hn : 1 ≤ n) (y t : ℝ) (hy : y ≤ (n : ℝ) / 3) (u : ℝ)
    (hu : 1 ≤ u) (G : ℕ → ℂ) (a b : ArithmeticFunction ℝ) (K L B1 B2 : ℝ) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (ha : ∀ r : ℕ, 1 ≤ r → r ≤ n → |a r| ≤ K) (ha0 : ∀ r : ℕ, u < (r : ℝ) → a r = 0)
    (hb0 : ∀ s, 0 ≤ b s) (hbmono : ∀ s, b s ≤ b (s + 1)) (hbL : ∀ s : ℕ, s ≤ n → b s ≤ L)
    (hleaf : ∀ r : ℕ, 1 ≤ r → ∀ τ : ℝ,
      ‖∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun s : ℕ => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ (s : ℝ) ≤ τ), G (r * s)‖ ≤
        B1 + (r : ℝ)⁻¹ * B2) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t), ((a * b) x : ℂ) * G x‖ ≤
      2 * K * L * (u * B1 + (1 + Real.log n) * B2) := by
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
  rw [conv_window_reindex a b G _
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t) hP0 hPM]
  simp only [Nat.add_sub_cancel]
  have hterm : ∀ r ∈ Finset.Icc 1 (Nat.ceil ((n : ℝ) / 3 + y)),
      ‖(a r : ℂ) * ∑ s ∈ Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1), (b s : ℂ) *
        (if (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) then G (r * s)
          else 0)‖ ≤
      2 * K * L * ((if (r : ℝ) ≤ u then (1 : ℝ) else 0) * B1 + (r : ℝ)⁻¹ * B2) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr.1
    have hinv : 0 ≤ (r : ℝ)⁻¹ * B2 := by positivity
    by_cases hru : (r : ℝ) ≤ u
    · simp only [hru, ite_true, one_mul]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hab := abel_mono (Nat.ceil ((n : ℝ) / 3 + y) + 1) (fun s => b s)
        (fun s => if (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) then
          G (r * s) else 0) L (B1 + (r : ℝ)⁻¹ * B2) hL hb0 hbmono
        (fun s hs => hbL s (by omega))
        (by
          intro j hj
          rw [← Finset.sum_filter]
          refine le_of_eq_of_le ?_ (hleaf r hr.1 (min ((j : ℝ) - 1) (t / r)))
          congr 1
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext s
          simp only [Finset.mem_filter, Finset.mem_range, le_min_iff]
          constructor
          · rintro ⟨hsj, habs, hst⟩
            refine ⟨by omega, habs, ?_, ?_⟩
            · have h1 : ((s + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hsj
              push_cast at h1
              linarith
            · rw [le_div_iff₀ hrpos]
              push_cast at hst
              linarith
          · rintro ⟨_, habs, h1, h2⟩
            refine ⟨?_, habs, ?_⟩
            · have h3 : ((s + 1 : ℕ) : ℝ) ≤ j := by
                push_cast
                linarith
              exact_mod_cast h3
            · rw [le_div_iff₀ hrpos] at h2
              push_cast
              linarith)
      have hK' := ha r hr.1 (hr.2.trans hMn)
      calc |a r| * _ ≤ K * (2 * L * (B1 + (r : ℝ)⁻¹ * B2)) :=
            mul_le_mul hK' hab (norm_nonneg _) hK
        _ = _ := by ring
    · rw [ha0 r (not_le.mp hru)]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero, hru, ite_false]
      positivity
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have h1 := sum_indicator_le (Nat.ceil ((n : ℝ) / 3 + y)) u (by linarith)
  have h2 : ∑ r ∈ Finset.Icc 1 (Nat.ceil ((n : ℝ) / 3 + y)), ((r : ℝ))⁻¹ ≤
      1 + Real.log n := by
    refine (sum_inv_le _).trans ?_
    rcases Nat.eq_zero_or_pos (Nat.ceil ((n : ℝ) / 3 + y)) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_natCast_nonneg n]
    · have hlog : Real.log (Nat.ceil ((n : ℝ) / 3 + y) : ℝ) ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hMn)
      linarith
  have hKL : 0 ≤ 2 * K * L := by positivity
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right h1 hB1) (mul_le_mul_of_nonneg_right h2 hB2)) hKL

/-- Song 2020, page 6, the display "Sigma1 << log^2 x (u |h|^(1/2) x^(gamma/2-1) y +
x^(1-gamma/2) |h|^(-1/2))". This is the Sigma 1 input of
RouteVaughanUV.vaughan_uv_route. Proved here from the single open input inner_sum_bound, the
citation wall Iwaniec and Kowalski Corollary 8.13, by the paper's steps: the double sum form
of Sigma 1, partial summation in s against log s, the coefficient bound log r for the second
part, and the summation over r at most u, with the two logarithms absorbed in n^epsilon. -/
theorem sigma1_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖(∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
                ((shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
                  ArithmeticFunction.log) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)) -
              (∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
                ((shortPart (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
                    shortPart ArithmeticFunction.vonMangoldt v) u *
                  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ))‖ ≤
              C * (n : ℝ) ^ ε *
                (u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                  (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2)) := by
  intro γ hγ1 hγ2 ε hε
  obtain ⟨C0, hC0, N0, hleaf⟩ := inner_sum_bound γ hγ1 hγ2 (ε / 3) (by positivity)
  have hδ : 0 < ε / 3 := by positivity
  refine ⟨4 * (1 / (ε / 3)) * (1 + 1 / (ε / 3)) * C0, by positivity, max N0 1, ?_⟩
  intro n hn y hy1 hy2 α h hh t u v hu hv huv
  have hnN : N0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg hnpos.le _) hy1.le
  have hL0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hX1 : 1 ≤ (n : ℝ) ^ (ε / 3) := Real.one_le_rpow hn1' hδ.le
  have hLX : Real.log n ≤ (n : ℝ) ^ (ε / 3) / (ε / 3) := Real.log_le_rpow_div hnpos.le hδ
  have hX3 : (n : ℝ) ^ ε = (n : ℝ) ^ (ε / 3) * (n : ℝ) ^ (ε / 3) * (n : ℝ) ^ (ε / 3) := by
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hT1 : 0 ≤ |(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y := by positivity
  have hT2 : 0 ≤ (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) := by positivity
  have hleaf' : ∀ r : ℕ, 1 ≤ r → ∀ τ : ℝ,
      ‖∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun s : ℕ => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ (s : ℝ) ≤ τ),
          (fun x : ℕ => eC (α * x + h * (x : ℝ) ^ γ)) (r * s)‖ ≤
        C0 * (n : ℝ) ^ (ε / 3) * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
          (r : ℝ)⁻¹ * (C0 * (n : ℝ) ^ (ε / 3) *
            ((n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2))) := by
    intro r hr τ
    exact (hleaf n hnN y hy1 hy2 α h hh r hr τ).trans (le_of_eq (by ring))
  have hlogmono : ∀ s : ℕ, Real.log s ≤ Real.log ((s + 1 : ℕ) : ℝ) := by
    intro s
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast hpos) (by push_cast; linarith)
  have hlogle : ∀ s : ℕ, s ≤ n → Real.log s ≤ Real.log n := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact hL0
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hs)
  have hA := conv_bound n hn1 y t hy2 u hu (fun x : ℕ => eC (α * x + h * (x : ℝ) ^ γ))
    (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u) ArithmeticFunction.log
    1 (Real.log n) _ _ zero_le_one hL0 (by positivity) (by positivity)
    (fun r _ _ => abs_muU_le_one u r)
    (fun r hr => by
      show (if (r : ℝ) ≤ u then _ else 0) = (0 : ℝ)
      simp only [not_le.mpr hr, ite_false])
    (fun s => Real.log_natCast_nonneg s) hlogmono hlogle hleaf'
  have hB := conv_bound n hn1 y t hy2 u hu (fun x : ℕ => eC (α * x + h * (x : ℝ) ^ γ))
    (shortPart (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
      shortPart ArithmeticFunction.vonMangoldt v) u)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (Real.log n) 1 _ _ hL0 zero_le_one (by positivity) (by positivity)
    (fun r _ hrn => by
      show |if (r : ℝ) ≤ u then _ else 0| ≤ Real.log n
      split_ifs
      · exact (abs_muU_mul_LV_le u v r).trans (hlogle r hrn)
      · rw [abs_zero]
        exact hL0)
    (fun r hr => by
      show (if (r : ℝ) ≤ u then _ else 0) = (0 : ℝ)
      simp only [not_le.mpr hr, ite_false])
    (fun s => by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
      split_ifs <;> simp)
    (fun s => by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, ArithmeticFunction.zeta_apply]
      split_ifs <;> simp_all)
    (fun s _ => by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
      split_ifs <;> simp)
    hleaf'
  refine (norm_sub_le _ _).trans ((add_le_add hA hB).trans ?_)
  generalize hXdef : (n : ℝ) ^ (ε / 3) = X at *
  generalize hT1def : |(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y = T1 at *
  generalize hT2def : (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) = T2 at *
  generalize hLdef : Real.log (n : ℝ) = L at *
  rw [hX3]
  have hu0 : 0 ≤ u := by linarith
  have hS : 0 ≤ C0 * X * (u * T1 + T2) := by positivity
  have hstep : u * (C0 * X * T1) + (1 + L) * (C0 * X * T2) ≤
      (1 + L) * (C0 * X * (u * T1 + T2)) := by
    have hnn : 0 ≤ L * (u * (C0 * X * T1)) := by positivity
    have e : (1 + L) * (C0 * X * (u * T1 + T2)) =
        u * (C0 * X * T1) + (1 + L) * (C0 * X * T2) + L * (u * (C0 * X * T1)) := by ring
    linarith
  have hLL : L * (1 + L) ≤ X / (ε / 3) * (X * (1 + 1 / (ε / 3))) := by
    refine mul_le_mul hLX ?_ (by positivity) (by positivity)
    have h1 : X * (1 + 1 / (ε / 3)) = X + X / (ε / 3) := by ring
    rw [h1]
    linarith
  calc 2 * 1 * L * (u * (C0 * X * T1) + (1 + L) * (C0 * X * T2)) +
        2 * L * 1 * (u * (C0 * X * T1) + (1 + L) * (C0 * X * T2))
      = 4 * L * (u * (C0 * X * T1) + (1 + L) * (C0 * X * T2)) := by ring
    _ ≤ 4 * L * ((1 + L) * (C0 * X * (u * T1 + T2))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 4 * (L * (1 + L)) * (C0 * X * (u * T1 + T2)) := by ring
    _ ≤ 4 * (X / (ε / 3) * (X * (1 + 1 / (ε / 3)))) * (C0 * X * (u * T1 + T2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLL (by norm_num)) hS
    _ = 4 * (1 / (ε / 3)) * (1 + 1 / (ε / 3)) * C0 * (X * X * X) * (u * T1 + T2) := by ring

end

end LeanLab.Song2020.RouteVaughanSigma1
