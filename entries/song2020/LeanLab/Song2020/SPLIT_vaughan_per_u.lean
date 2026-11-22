module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.Song2020.RouteS1Lambda
public import LeanLab.Song2020.RouteVaughanUV

/-!
AI wrote the Lean code, 2026-11-13.
Source: https://arxiv.org/pdf/2012.06322, printed pages 5 through 8.
The two analytic steps that Decomp139 uses are stated in this file, and Decomp139 proves
its own steps from them.
The gate rejects any new def, not even a private one, so this file defines nothing: the
definitions Decomp139 uses are written out in full in the statement of each leaf, with the
left hand sides substituted by their bodies from Decomp139. Decomp139 transfers a leaf back
by unfolding its own fourier, truncatedSum, subWindow and lambdaSum.

s1_lambda_reduction, page 5, the displays from "For S1, we first observe" to "We have shown
so far": partial summation in the weight c x to the 1 minus gamma, the bound a_h at most K
over h for the Fourier coefficients, the bound of e of h times the difference of x plus 1 to
the gamma and x to the gamma minus 1 by h x to the gamma minus 1, and the passage from primes
to the von Mangoldt function. The paper writes the maximum over centred windows and a saving
1 over log n; this form keeps instead the initial segments that partial summation really
produces, drops the log saving, and writes out the prime power error as K H n to the 1/2,
which the paper absorbs into its O of n to the 3/2 minus gamma. Any bound B on the von
Mangoldt sums for 1 at most |h| at most H then bounds S1. The factor n to the epsilon on the
B sum was added in the check of 2026-11-12: for y close to n/3 the window reaches down to
small x, and the total variation of the partial summation weight x to the 1 minus gamma times
e of h times the gamma difference minus 1 is then of size |h| log n, not |h|; the paper's y is
a power of n below 1, where this loss does not arise, and n to the epsilon absorbs it.

vaughan_uv, pages 5 to 7, the bounds for the three Vaughan pieces with both parameters u and v
free, 1 at most u, 1 at most v and u v at most n, before the choice v = (n/u)^{1/2}: the
Sigma 1 display of page 6, u |h|^{1/2} x^{gamma/2-1} y plus x^{1-gamma/2} |h|^{-1/2}, with its
log squared factor absorbed in n to the epsilon, plus the display for x^{-epsilon} times
Sigma 2 plus Sigma 3 on page 7, n v^{-1/2} plus n^{1/2} (u v)^{1/2} plus the four u and h
monomials. Here x is replaced by n, since x is of size n over 3. Published inputs: Dirichlet
approximation and the Ramanujan sum splitting, page 5; the Vaughan identity, the paper's
Lemma 3.2, page 5; Iwaniec and Kowalski Corollary 8.13 for Sigma 1, page 6; dyadic division
into T(R,S) and Graham and Kolesnik Lemma 2.5, page 6; Iwaniec and Kowalski Corollary 8.13 for
the inner r sum and Graham and Kolesnik Lemma 2.4 for L, page 7.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.SPLIT_vaughan_per_u

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Song 2020, page 5, from "For S1, we first observe" to "We have shown so far":
partial summation over the prime window with a_h at most K over h reduces S1 to the von
Mangoldt sums over an initial segment, with n to the epsilon absorbing the weight variation
when y is close to n/3. The header of this file carries the full reading.
Proved from RouteS1Lambda.s1_lambda_reduction_route. -/
theorem s1_lambda_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H → ∀ B : ℤ → ℝ,
              (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ B h) →
              ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
      (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * (-(p : ℝ) ^ γ)))‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                  (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
  exact RouteS1Lambda.s1_lambda_reduction_route

/-- Song 2020, pages 6 and 7, with u and v both free: the Sigma 1 display and the
display for x to the minus epsilon times Sigma 2 plus Sigma 3, before the choice
v = (n/u)^{1/2}. The header of this file carries the full reading.
Proved through RouteVaughanUV.vaughan_uv_route. Conditional on the
three open leaves RouteVaughanLeaves.sigma2_bound, RouteVaughanLeaves.sigma3_bound and
RouteVaughanSigma1.inner_sum_bound. -/
theorem vaughan_uv :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ C * (n : ℝ) ^ ε *
              (u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) +
                (n : ℝ) * v ^ (-(1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  exact RouteVaughanUV.vaughan_uv_route

/-- Proved. The modulus of the additive character is one, so the triangle inequality leaves
the von Mangoldt mass of the window: the first step inside the partial summation leaf. -/
private theorem norm_eC (θ : ℝ) : ‖eC θ‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- Proved. Triangle inequality for the window sum: the exponential sum is at most the
von Mangoldt mass over the same initial segment, since each term has modulus Lambda of x. -/
theorem norm_lambdaSum_le_vonMangoldt_mass (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℝ) := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro x hx
  rw [norm_mul, Complex.norm_real, norm_eC, mul_one, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Proved. The window is monotone in the upper endpoint, which is what partial summation
needs when it replaces the weight by its total variation. -/
theorem subWindow_mono (n : ℕ) (y : ℝ) {t t' : ℝ} (htt : t ≤ t') :
    (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t) ⊆
      (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t') := by
  intro x hx
  simp only [Finset.mem_filter] at *
  exact ⟨hx.1, hx.2.1, hx.2.2.trans htt⟩

/-- Proved. The weight difference of the partial summation: for 0 < gamma < 1 and x at
least 1, the increment of the weight t to the 1 minus gamma over the step from x to x plus 1
is at most the derivative at the left endpoint, 1 minus gamma times x to the minus gamma.
This is Lagrange's mean value theorem with the derivative of t to the 1 minus gamma equal to
1 minus gamma times t to the minus gamma, decreasing, so the intermediate point gives the
bound. This is the step the paper records as bounding the difference of x plus 1 to the gamma
and x to the gamma by x to the gamma minus 1, inside the partial summation leaf. -/
theorem abs_rpow_window_weight_le (γ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx : 1 ≤ x) :
    |(x + 1) ^ (1 - γ) - x ^ (1 - γ)| ≤ (1 - γ) * x ^ (-γ) := by
  have hx0 : 0 < x := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (1 - γ)) (Set.Icc x (x + 1)) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 ht.1)))
  have hderiv : ∀ t ∈ Set.Ioo x (x + 1),
      HasDerivAt (fun t : ℝ => t ^ (1 - γ)) ((1 - γ) * t ^ ((1 - γ) - 1)) t := by
    intro t ht
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hx0 ht.1)))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 - γ))
    (fun t : ℝ => (1 - γ) * t ^ ((1 - γ) - 1)) (by linarith : x < x + 1) hcont hderiv
  rw [show x + 1 - x = 1 by ring, div_one] at hslope
  have hc0 : 0 < c := lt_trans hx0 hc.1
  have hcle : c ^ ((1 - γ) - 1) ≤ x ^ ((1 - γ) - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 hc.1.le (by linarith)
  have hkey : (x + 1) ^ (1 - γ) - x ^ (1 - γ) ≤ (1 - γ) * x ^ ((1 - γ) - 1) := by
    rw [← hslope]
    exact mul_le_mul_of_nonneg_left hcle h1γ.le
  have hexp : (1 - γ) - 1 = -γ := by ring
  rw [hexp] at hkey
  have hnn : 0 ≤ (x + 1) ^ (1 - γ) - x ^ (1 - γ) := by
    have := Real.rpow_le_rpow hx0.le (by linarith : x ≤ x + 1) h1γ.le
    linarith
  rw [abs_of_nonneg hnn]
  exact hkey

/-- Proved. The weight of the partial summation telescopes: the sum of the increments of
t to the 1 minus gamma over the first m steps is the weight at m, since the weight at 0
vanishes for a positive exponent. This is the total variation the paper charges when it sums
the weight difference by parts, inside the partial summation leaf. -/
theorem sum_rpow_weight_telescope (γ : ℝ) (hγ1 : γ < 1) (m : ℕ) :
    ∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) ^ (1 - γ) - (k : ℝ) ^ (1 - γ)) =
      (m : ℝ) ^ (1 - γ) := by
  have h := Finset.sum_range_sub (fun k : ℕ => (k : ℝ) ^ (1 - γ)) m
  rw [h, show ((0 : ℕ) : ℝ) = 0 by norm_num,
    Real.zero_rpow (by linarith : (1 : ℝ) - γ ≠ 0), sub_zero]

/-- Proved. The von Mangoldt mass of the window is at most its length times the logarithm of
its top: every term is Lambda of x at most log x, and x runs below the top of the range, so
the whole window costs at most the number of integers in the range times that logarithm. This
is the crude estimate the paper's partial summation carries along until the cancellation of
the exponential sums takes over. -/
theorem mass_le_card_mul_log (n : ℕ) (y t : ℝ) :
    ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
        (ArithmeticFunction.vonMangoldt x : ℝ) ≤
      ((Nat.ceil ((n : ℝ) / 3 + y) + 1 : ℕ) : ℝ) *
        Real.log ((Nat.ceil ((n : ℝ) / 3 + y) + 1 : ℕ) : ℝ) := by
  set M : ℕ := Nat.ceil ((n : ℝ) / 3 + y) + 1 with hMdef
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    have h1 : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast h1
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  refine (Finset.sum_le_card_nsmul _ _ (Real.log (M : ℝ)) ?_).trans ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rcases Nat.eq_zero_or_pos x with h0 | hp
    · subst h0
      simpa using hlog
    · have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hp
      have hxM : (x : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hx.1)
      exact (ArithmeticFunction.vonMangoldt_le_log (n := x)).trans
        (Real.log_le_log hxpos hxM)
  · rw [nsmul_eq_mul]
    have hc : ((Finset.range M).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)).card ≤ M := by
      calc _ ≤ (Finset.range M).card := Finset.card_filter_le _ _
        _ = M := Finset.card_range M
    have hc' : (((Finset.range M).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)).card : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hc' hlog

/-- Proved. The two preceding steps together: the von Mangoldt exponential sum of the window
is at most the number of integers in the range times the logarithm of its top. This is the
trivial estimate the paper starts from before the cancellation of the exponential sums. -/
theorem norm_lambdaSum_le_card_mul_log (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
        (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
      ((Nat.ceil ((n : ℝ) / 3 + y) + 1 : ℕ) : ℝ) *
        Real.log ((Nat.ceil ((n : ℝ) / 3 + y) + 1 : ℕ) : ℝ) :=
  (norm_lambdaSum_le_vonMangoldt_mass γ n y α h t).trans (mass_le_card_mul_log n y t)

/-- Proved. Abel summation, in the form the paper uses it: a weight that is nonnegative and
nonincreasing turns a bound B on the partial sums of a complex sequence into a bound w 0 times
B on the weighted sum. The proof is summation by parts, Finset.sum_range_by_parts, with the
differences of the weight telescoping to w 0 minus w at the top. This is the partial summation
step of the leaf: the exponential sums supply B and the prime weight is w. -/
theorem norm_sum_mul_le_of_partial_sum_bound (w : ℕ → ℝ) (a : ℕ → ℂ) (B : ℝ)
    (hwpos : ∀ k, 0 ≤ w k) (hwanti : ∀ k, w (k + 1) ≤ w k)
    (hB : ∀ j : ℕ, ‖∑ k ∈ Finset.range j, a k‖ ≤ B) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, (w k : ℂ) * a k‖ ≤ w 0 * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (hwpos 0) hB0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have hparts := Finset.sum_range_by_parts (fun k : ℕ => w k) (fun k : ℕ => a k) (n + 1)
  simp only [Nat.add_sub_cancel] at hparts
  have h1 : ‖w n • (∑ i ∈ Finset.range (n + 1), a i)‖ ≤ w n * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hwpos n)]
    exact mul_le_mul_of_nonneg_left (hB (n + 1)) (hwpos n)
  have h2 : ‖∑ i ∈ Finset.range n,
      (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), a j)‖ ≤ (w 0 - w n) * B := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range n,
        ‖(w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), a j)‖ ≤ (w i - w (i + 1)) * B := by
      intro i _
      have hnonpos : w (i + 1) - w i ≤ 0 := by linarith [hwanti i]
      have hnonneg : 0 ≤ w i - w (i + 1) := by linarith [hwanti i]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hnonpos, neg_sub]
      exact mul_le_mul_of_nonneg_left (hB (i + 1)) hnonneg
    calc ∑ i ∈ Finset.range n, ‖(w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), a j)‖
        ≤ ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range n, (w i - w (i + 1))) * B := by rw [Finset.sum_mul]
      _ = (w 0 - w n) * B := by
        have htel : ∑ i ∈ Finset.range n, (w (i + 1) - w i) = w n - w 0 :=
          Finset.sum_range_sub (fun i : ℕ => w i) n
        have hneg : ∑ i ∈ Finset.range n, (w i - w (i + 1)) =
            -(∑ i ∈ Finset.range n, (w (i + 1) - w i)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [hneg, htel]
        ring
  calc ‖∑ k ∈ Finset.range (n + 1), (w k : ℂ) * a k‖
      = ‖w n • (∑ i ∈ Finset.range (n + 1), a i) -
          ∑ i ∈ Finset.range n,
            (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), a j)‖ := by
        rw [← hparts]
        simp only [Complex.real_smul]
    _ ≤ ‖w n • (∑ i ∈ Finset.range (n + 1), a i)‖ +
          ‖∑ i ∈ Finset.range n,
            (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), a j)‖ := norm_sub_le _ _
    _ ≤ w n * B + (w 0 - w n) * B := add_le_add h1 h2
    _ = w 0 * B := by ring

/-- Proved. The Abel step at the decreasing weight the derivative estimate produces: for
0 < gamma the weight k plus 1 to the minus gamma is nonnegative and nonincreasing, so a bound
B on the partial sums of a complex sequence bounds the weighted sum by B itself, since the
weight at the bottom is one. -/
theorem norm_sum_mul_rpow_neg_le_of_partial_sum_bound (γ : ℝ) (hγ0 : 0 < γ)
    (a : ℕ → ℂ) (B : ℝ)
    (hB : ∀ j : ℕ, ‖∑ k ∈ Finset.range j, a k‖ ≤ B) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, ((((k + 1 : ℕ) : ℝ) ^ (-γ) : ℝ) : ℂ) * a k‖ ≤ B := by
  have hmain := norm_sum_mul_le_of_partial_sum_bound
    (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-γ)) a B
    (fun k => Real.rpow_nonneg (by positivity) _)
    (fun k => by
      have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith))
    hB m
  simpa using hmain

/-- Proved. The trivial bound on the Fourier side of the S1 estimate: with the coefficient
hypothesis of the paper, every term of the truncated Fourier polynomial has modulus at most K,
so the polynomial is at most K times the number of frequencies. This is what the exponential
sum estimates have to improve on; on its own it carries no cancellation. -/
theorem norm_fourier_sum_le_of_coeff_bound (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) (K : ℝ)
    (hK0 : 0 ≤ K)
    (hK : ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) :
    ‖∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * x)‖
      ≤ K * (2 * (H : ℝ) + 1) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
      ‖a H h * eC (h * x)‖ ≤ K := by
    intro h hh
    have hne : h ≠ 0 := (Finset.mem_filter.mp hh).2
    have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      have h' : (1 : ℤ) ≤ |h| := Int.one_le_abs hne
      exact_mod_cast h'
    rw [norm_mul, norm_eC, mul_one]
    exact (hK h hne).trans (div_le_self hK0 h1)
  refine (Finset.sum_le_card_nsmul _ _ K hterm).trans ?_
  rw [nsmul_eq_mul]
  have hcard : (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) ≤
      2 * (H : ℝ) + 1 := by
    have hle : ((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card ≤
        (Finset.Icc (-(H : ℤ)) H).card := Finset.card_filter_le _ _
    have hcard2 : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
      rw [Int.card_Icc]
      have hz : (H : ℤ) + 1 - (-(H : ℤ)) = 2 * (H : ℤ) + 1 := by ring
      rw [hz]
      have hz2 : (((2 * (H : ℤ) + 1).toNat : ℤ)) = 2 * (H : ℤ) + 1 :=
        Int.toNat_of_nonneg (by positivity)
      omega
    rw [hcard2] at hle
    exact_mod_cast hle
  have hfin := mul_le_mul_of_nonneg_right hcard hK0
  calc (((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0)).card : ℝ) * K
      ≤ (2 * (H : ℝ) + 1) * K := hfin
    _ = K * (2 * (H : ℝ) + 1) := by ring

/-- Proved. The window also grows with the width y: if y is at most y prime then the initial
segments of the narrower window are initial segments of the wider one. Partial summation uses
this when the width is enlarged. -/
theorem subWindow_mono_y (n : ℕ) {y y' t : ℝ} (hyy : y ≤ y') :
    (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t) ⊆
      (Finset.range (Nat.ceil ((n : ℝ) / 3 + y') + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y' ∧ (x : ℝ) ≤ t) := by
  intro x hx
  rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
  have hceil : Nat.ceil ((n : ℝ) / 3 + y) ≤ Nat.ceil ((n : ℝ) / 3 + y') :=
    Nat.ceil_le_ceil (by linarith)
  exact ⟨by omega, lt_of_lt_of_le hx.2.1 hyy, hx.2.2⟩

/-- Proved. The S1 side assembled from a bound on the truncated Fourier sums: if every one of
those sums is at most M in modulus, then the window sum of the paper is at most twice M times
the total weight of the window, by the triangle inequality and the fact that the additive
character has modulus one. This is the shape the paper needs when the exponential sum
estimates are inserted into S1, with M a free parameter. -/
theorem norm_truncatedSum_le_of_fourier_bound (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ)
    (y α : ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ x : ℝ,
      ‖∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * x)‖ ≤ M) :
    ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
        (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-(p : ℝ) ^ γ)))‖
      ≤ 2 * M * ∑ p ∈ windowPrimes n y, ‖(psWeight γ p : ℂ)‖ := by
  have hterm : ∀ p ∈ windowPrimes n y,
      ‖(psWeight γ p : ℂ) * eC (α * p) *
        (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-(p : ℝ) ^ γ)))‖
        ≤ 2 * M * ‖(psWeight γ p : ℂ)‖ := by
    intro p _
    rw [norm_mul, norm_mul, norm_eC, mul_one]
    have hdiff : ‖(∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-((p : ℝ) + 1) ^ γ))) -
          (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-(p : ℝ) ^ γ)))‖ ≤ 2 * M := by
      refine (norm_sub_le _ _).trans ?_
      linarith [hF (-((p : ℝ) + 1) ^ γ), hF (-(p : ℝ) ^ γ)]
    have hnn : 0 ≤ ‖(psWeight γ p : ℂ)‖ := norm_nonneg _
    nlinarith [hdiff, hnn, hM]
  calc ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
        (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0),
            a H h * eC (h * (-(p : ℝ) ^ γ)))‖
      ≤ ∑ p ∈ windowPrimes n y, 2 * M * ‖(psWeight γ p : ℂ)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * M * ∑ p ∈ windowPrimes n y, ‖(psWeight γ p : ℂ)‖ := by
        rw [Finset.mul_sum]

end

end LeanLab.Song2020.SPLIT_vaughan_per_u
