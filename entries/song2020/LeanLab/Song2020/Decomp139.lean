module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.Song2020.SPLIT_lambda_sum_per_h
public import LeanLab.Song2020.SPLIT_vaughan_per_u

/-!
AI wrote the Lean code, Codex by OpenAI, 2026-10-27.
Source: https://arxiv.org/pdf/2012.06322, printed pages 4 through 8.
The analytic steps are proved in the files this one imports. The assembly of Lemma 4 from
these steps is in Wire1122Lemma4.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Decomp139

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Pages 4 and 5. The truncated Fourier polynomial of Lemma 1. -/
def fourier (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)

/-- Pages 4 and 5. S1 with negative Fourier frequencies as in the defined sawtooth. -/
def truncatedSum (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ))

/-- Pages 4 and 5. The displayed S2 bound. -/
def tailBudget (γ n y H : ℝ) : ℝ :=
  H ^ ((1 : ℝ) / 2) * n ^ (1 - γ / 2) + H⁻¹ * y * n ^ (1 - γ)

/-- Page 8. Exponent pairs of the optimized bound, with the S2 balance computed from page 5. -/
def terms (γ : ℝ) : List (ℝ × ℝ) :=
  [(3 / 2 - γ, 0),
   (1 - γ / 4, 0), ((γ + 2) / 6, 1 / 3), (γ / 4, 1 / 2), (3 / 4, 1 / 8),
   (γ / 8 + 1 / 2, 1 / 4), (γ / 10 + 3 / 5, 1 / 5), (3 * γ / 10, 3 / 5),
   (3 * γ / 14 + 2 / 7, 3 / 7), (1 - 2 * γ / 3, 1 / 3),
   (1 - 4 * γ / 7, 3 / 7), (7 / 8 - γ / 2, 1 / 2), (1 / 5 - 2 * γ / 5, 1),
   (9 / 13 - 6 * γ / 13, 9 / 13), (5 / 9 - 4 * γ / 9, 7 / 9),
   (7 / 8 - γ / 2, 9 / 16), (13 / 17 - 8 * γ / 17, 11 / 17),
   (17 / 21 - 10 * γ / 21, 13 / 21), (13 / 23 - 10 * γ / 23, 19 / 23),
   (21 / 31 - 14 * γ / 31, 23 / 31)]

/-- Page 8. The sum of the optimized monomials, including the prime power remainder. -/
def budget (γ n y : ℝ) : ℝ := (terms γ |>.map (fun ab => n ^ ab.1 * y ^ ab.2)).sum

/-- Page 4, first two displays of the proof of Lemma 4.
The floor characteristic and Taylor remainder reduce the discrepancy to the sawtooth sum. -/
theorem characteristic_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ‖fS γ n y α - gS n y α - sawSum γ n y α‖ ≤ C * (n : ℝ) ^ (3 / 2 - γ) :=
  LeanLab.Song2020.Characteristic139.characteristic_reduction139

/-- Page 8, first display after summing over h. The exponent triples of the S1 bound:
the exponent of n, of y and of H in each monomial. The last triple uses n to the
gamma over four, from the preceding per h display on page 8, as recorded in a lab question;
the printed page 8 display shows n to the gamma there. -/
def s1Terms (γ : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(1 - γ / 4, 0, 3 / 4), ((γ + 4) / 8, 1 / 4, 9 / 8), ((3 * γ + 4) / 14, 3 / 7, 17 / 14),
   (3 / 4, 1 / 8, 1), (γ / 2 - 1, 1, 3 / 2), (3 * γ / 10, 3 / 5, 13 / 10),
   ((γ + 6) / 10, 1 / 5, 11 / 10), ((γ + 2) / 6, 1 / 3, 7 / 6), (γ / 4, 1 / 2, 5 / 4)]

/-- Page 8, first display after summing over h. The S1 polynomial in H. -/
def s1Poly (γ n y H : ℝ) : ℝ :=
  (s1Terms γ |>.map (fun t => n ^ t.1 * y ^ t.2.1 * H ^ t.2.2)).sum

/-- Page 5. The truncated subwindow of the prime window: the integers x with
x minus n over 3 less than y in absolute value and x at most t. Partial summation over the
window produces sums over these initial segments. -/
def subWindow (n : ℕ) (y t : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)

/-- Page 5. The von Mangoldt weighted exponential sum of the paper, the sum of
Lambda of x times e of alpha x plus h x to the gamma, over an initial segment of the window. -/
def lambdaSum (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) : ℂ :=
  ∑ x ∈ subWindow n y t,
    (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)

/-- Page 8, first display. The ten monomials of the per h bound for
x to the minus epsilon times Sigma 1 plus Sigma 2 plus Sigma 3, with x replaced by n,
which is legitimate since x is of size n over 3 on the window. The argument k stands for
the absolute value of h. -/
def perH (γ n y k : ℝ) : ℝ :=
  n ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) + n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) +
  n ^ (γ / 2 - 1) * y * k ^ ((1 : ℝ) / 2) +
  n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6) +
  n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4) +
  n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * k ^ ((1 : ℝ) / 8) +
  n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) +
  n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) +
  n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * k ^ ((3 : ℝ) / 10) +
  n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * k ^ ((3 : ℝ) / 14)

/-- Song 2020, page 5, the displays from "For S1, we first observe" to
"We have shown so far": partial summation in the weight c x to the 1 minus gamma,
the bound a_h at most K over h for the Fourier coefficients, the bound of
e of h times the difference of x plus 1 to the gamma and x to the gamma minus 1
by h x to the gamma minus 1, and the passage from primes to the von Mangoldt function.
The paper writes the maximum over centred windows and a saving 1 over log n; this form
keeps instead the initial segments that partial summation really produces, drops the
log saving, and writes out the prime power error as K H n to the 1/2, which the
paper absorbs into its O of n to the 3/2 minus gamma. Any bound B on the von Mangoldt
sums for 1 at most |h| at most H then bounds S1. The factor n to the epsilon on the B sum
was added in the check of 2026-11-12: for y close to n/3 the window reaches down to small x,
and the total variation of the partial summation weight x to the 1 minus gamma times
e of h times the gamma difference minus 1 is then of size |h| log n, not |h|; the paper's
y is a power of n below 1, where this loss does not arise, and n to the epsilon absorbs it. -/
theorem s1_lambda_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H → ∀ B : ℤ → ℝ,
              (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖lambdaSum γ n y α h t‖ ≤ B h) →
              ‖truncatedSum a H γ n y α‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                  (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
  simpa only [fourier, truncatedSum, subWindow, lambdaSum]
    using LeanLab.Song2020.SPLIT_vaughan_per_u.s1_lambda_reduction

/-- Song 2020, pages 5 to 7, the bounds for the three Vaughan pieces with both
parameters u and v free, 1 at most u, 1 at most v and u v at most n, before the choice
v = (n/u)^{1/2}: the Sigma 1 display of page 6, u |h|^{1/2} x^{γ/2-1} y plus
x^{1-γ/2} |h|^{-1/2}, with its log squared factor absorbed in n to the epsilon, plus the
display for x^{-ε} times Sigma 2 plus Sigma 3 on page 7, n v^{-1/2} plus n^{1/2} (u v)^{1/2}
plus the four u and h monomials. Here x is replaced by n, since x is of size n over 3.
Published inputs: Dirichlet approximation and the Ramanujan sum splitting, page 5; the
Vaughan identity, the paper's Lemma 3.2, page 5; Iwaniec and Kowalski Corollary 8.13 for
Sigma 1, page 6; dyadic division into T(R,S) and Graham and Kolesnik Lemma 2.5, page 6;
Iwaniec and Kowalski Corollary 8.13 for the inner r sum and Graham and Kolesnik Lemma 2.4
for L, page 7. -/
theorem vaughan_uv :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              (u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) +
                (n : ℝ) * v ^ (-(1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  simpa only [subWindow, lambdaSum]
    using LeanLab.Song2020.SPLIT_vaughan_per_u.vaughan_uv

/-- Proved. Triangle inequality for the von Mangoldt sum of the window, transferred from the
repair file: the exponential sum is at most the mass of the von Mangoldt function over the
same initial segment, since every term has modulus Lambda of x. This is the first step inside
the partial summation leaf, s1_lambda_reduction, and it is the only part of that leaf that
Mathlib supplies on its own. -/
theorem norm_lambdaSum_le_vonMangoldt_mass (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) :
    ‖lambdaSum γ n y α h t‖ ≤ ∑ x ∈ subWindow n y t, (ArithmeticFunction.vonMangoldt x : ℝ) := by
  simpa only [lambdaSum, subWindow]
    using LeanLab.Song2020.SPLIT_vaughan_per_u.norm_lambdaSum_le_vonMangoldt_mass γ n y α h t

/-- Proved. Page 7, the choice v = (n/u)^{1/2}, written as n^{1/2} u^{-1/2}: for
1 at most u at most n it is at least 1, u v is at most n, and both n v^{-1/2} and
n^{1/2} (u v)^{1/2} equal u^{1/4} n^{3/4}. -/
theorem choice_v (N u : ℝ) (hu : 1 ≤ u) (huN : u ≤ N) :
    1 ≤ N ^ ((1 : ℝ) / 2) * u ^ (-(1 : ℝ) / 2) ∧
      u * (N ^ ((1 : ℝ) / 2) * u ^ (-(1 : ℝ) / 2)) ≤ N ∧
      N * (N ^ ((1 : ℝ) / 2) * u ^ (-(1 : ℝ) / 2)) ^ (-(1 : ℝ) / 2) =
        u ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) ∧
      N ^ ((1 : ℝ) / 2) * (u * (N ^ ((1 : ℝ) / 2) * u ^ (-(1 : ℝ) / 2))) ^ ((1 : ℝ) / 2) =
        u ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) := by
  have hu0 : 0 < u := by linarith
  have hN0 : 0 < N := by linarith
  obtain ⟨L, rfl⟩ : ∃ L, N = Real.exp L := ⟨Real.log N, (Real.exp_log hN0).symm⟩
  obtain ⟨M, rfl⟩ : ∃ M, u = Real.exp M := ⟨Real.log u, (Real.exp_log hu0).symm⟩
  have hML : M ≤ L := Real.exp_le_exp.mp huN
  simp only [← Real.exp_mul, ← Real.exp_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.one_le_exp_iff]; linarith
  · rw [Real.exp_le_exp]; linarith
  · congr 1; ring
  · congr 1; ring

/-- Song 2020, page 7. The per u display, assembled from the cited free u and v bounds
vaughan_uv by the proved choice v = (n/u)^{1/2}, choice_v, with the Sigma 1 term
x^{1-γ/2} |h|^{-1/2} absorbed in n^{1-γ/4} |h|^{-1/4}. -/
theorem vaughan_per_u_of_split :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u : ℝ, 1 ≤ u → u ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) +
                u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₁, hC₁, N₁, hv⟩ := vaughan_uv γ hγ hγ1 ε hε
  refine ⟨2 * C₁, by positivity, max 1 N₁, ?_⟩
  intro n hn y hy hyu α h hh t u hu1 huN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨hv1, huv, e1, e2⟩ := choice_v (n : ℝ) u hu1 huN
  have hb := hv n (by omega) y hy hyu α h hh t u _ hu1 hv1 huv
  rw [e1, e2] at hb
  set N : ℝ := (n : ℝ) with hNdef
  set k : ℝ := |(h : ℝ)| with hkdef
  have hk1 : 1 ≤ k := by
    rw [hkdef]
    have h' : 1 ≤ |h| := Int.one_le_abs hh
    exact_mod_cast h'
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hN0 _).trans hy
  have habs : N ^ (1 - γ / 2) * k ^ (-(1 : ℝ) / 2) ≤ N ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)) (by positivity) (by positivity)
  have z0 : 0 ≤ N ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) := by positivity
  have z1 : 0 ≤ u ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) := by positivity
  have z2 : 0 ≤ u * (k ^ ((1 : ℝ) / 2) * N ^ (γ / 2 - 1) * y) := by positivity
  have z3 : 0 ≤ u ^ (-(1 : ℝ) / 4) * (N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) := by positivity
  have z4 : 0 ≤ u ^ (-(1 : ℝ) / 6) * (N ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
      k ^ ((1 : ℝ) / 6)) := by positivity
  have z5 : 0 ≤ u ^ (-(1 : ℝ) / 4) * (N ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
      k ^ ((1 : ℝ) / 4)) := by positivity
  refine hb.trans ?_
  rw [show 2 * C₁ * N ^ ε = C₁ * N ^ ε * 2 by ring, mul_assoc (C₁ * N ^ ε)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- Song 2020, page 7, the display after "Choosing v = (n/u)^{1/2}": for every
Vaughan parameter u with 1 at most u at most n, so that u v is at most n,
x to the minus epsilon times Sigma 1 plus Sigma 2 plus Sigma 3 is bounded by six monomials,
written here with x replaced by n since x is of size n over 3, and with k the absolute value
of h. Published inputs: Dirichlet approximation with q at most log n and the Ramanujan sum
splitting, page 5; the Vaughan identity, the paper's Lemma 3.2, page 5; Iwaniec and
Kowalski Corollary 8.13 for Sigma 1, page 6; dyadic division into T(R,S) and Graham and
Kolesnik Lemma 2.5, page 6; Iwaniec and Kowalski Corollary 8.13 for the inner r sum and
Graham and Kolesnik Lemma 2.4 for L, page 7. The Sigma 1 term x to the 1 minus gamma over 2
times h to the minus 1/2 of page 6 is absorbed in n to the 1 minus gamma over 4 times
h to the minus 1/4, as on page 7. -/
theorem vaughan_per_u :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u : ℝ, 1 ≤ u → u ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) +
                u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) :=
  vaughan_per_u_of_split

/-- Proved. The balancing step inside Graham and Kolesnik Lemma 2.4: if S is at most
3 P u to the a and at most 3 Q u to the minus b, then S is at most 3 times the balance
P to the b times Q to the a, to the power 1 over a plus b. -/
theorem balance_core (S P Q u a b : ℝ) (hS : 0 ≤ S) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hu : 0 < u)
    (ha : 0 < a) (hb : 0 < b) (h₁ : S ≤ 3 * (P * u ^ a)) (h₂ : S ≤ 3 * (Q * u ^ (-b))) :
    S ≤ 3 * (P ^ b * Q ^ a) ^ (1 / (a + b)) := by
  have hab : a + b ≠ 0 := by linarith
  have e1 : S ^ b ≤ (3 * (P * u ^ a)) ^ b := Real.rpow_le_rpow hS h₁ hb.le
  have e2 : S ^ a ≤ (3 * (Q * u ^ (-b))) ^ a := Real.rpow_le_rpow hS h₂ ha.le
  have hua : 0 ≤ u ^ a := by positivity
  have hub : 0 ≤ u ^ (-b) := by positivity
  have f1 : (3 * (P * u ^ a)) ^ b = 3 ^ b * (P ^ b * u ^ (a * b)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hP hua,
      ← Real.rpow_mul hu.le]
  have f2 : (3 * (Q * u ^ (-b))) ^ a = 3 ^ a * (Q ^ a * u ^ (-b * a)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hQ hub,
      ← Real.rpow_mul hu.le]
  have f3 : u ^ (-b * a) * u ^ (a * b) = 1 := by
    rw [← Real.rpow_add hu, show -b * a + a * b = 0 by ring, Real.rpow_zero]
  have f4 : (3 : ℝ) ^ a * 3 ^ b = 3 ^ (a + b) := (Real.rpow_add (by norm_num) a b).symm
  have hSab : S ^ (a + b) ≤ 3 ^ (a + b) * (P ^ b * Q ^ a) := by
    rw [Real.rpow_add' hS hab]
    calc S ^ a * S ^ b ≤ (3 * (Q * u ^ (-b))) ^ a * (3 * (P * u ^ a)) ^ b :=
          mul_le_mul e2 e1 (Real.rpow_nonneg hS _) (by positivity)
      _ = (3 ^ a * 3 ^ b) * (P ^ b * Q ^ a) * (u ^ (-b * a) * u ^ (a * b)) := by
          rw [f1, f2]; ring
      _ = 3 ^ (a + b) * (P ^ b * Q ^ a) := by rw [f3, f4, mul_one]
  have hX : 0 ≤ P ^ b * Q ^ a := by positivity
  have g1 := Real.rpow_le_rpow (Real.rpow_nonneg hS _) hSab
    (by positivity : (0 : ℝ) ≤ 1 / (a + b))
  rw [one_div, Real.rpow_rpow_inv hS hab, Real.mul_rpow (by positivity) hX,
    Real.rpow_rpow_inv (by norm_num) hab] at g1
  rw [one_div]
  exact g1

/-- Proved. Graham and Kolesnik, Van der Corput's Method of Exponential Sums, Lemma 2.4,
with two positive and three negative powers and the range 1 at most u at most U, as Song 2020
applies it on page 8 to choose u: some u in the range has the five term sum bounded by the
six pairwise balances, the values of the positive terms at u equal to 1 and the values of the
negative terms at u equal to U. Proved here by the intermediate value theorem, not cited. -/
theorem gk_lemma_2_4_two_three (a₁ a₂ b₁ b₂ b₃ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P₁ P₂ Q₁ Q₂ Q₃ : ℝ, 0 ≤ P₁ → 0 ≤ P₂ → 0 ≤ Q₁ → 0 ≤ Q₂ → 0 ≤ Q₃ →
      ∀ U : ℝ, 1 ≤ U → ∃ u : ℝ, 1 ≤ u ∧ u ≤ U ∧
        P₁ * u ^ a₁ + P₂ * u ^ a₂ + Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) ≤
          C * ((P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) + (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) +
            (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) + (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) +
            (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) + (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) +
            P₁ + P₂ + Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃)) := by
  refine ⟨6, by norm_num, ?_⟩
  intro P₁ P₂ Q₁ Q₂ Q₃ hP₁ hP₂ hQ₁ hQ₂ hQ₃ U hU
  set B : ℝ := (P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) + (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) +
    (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) + (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) +
    (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) + (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) with hBdef
  have hB : ∀ x, x = (P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) ∨
      x = (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) ∨ x = (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) ∨
      x = (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) ∨ x = (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) ∨
      x = (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) → x ≤ B := by
    have z1 : 0 ≤ (P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) := by positivity
    have z2 : 0 ≤ (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) := by positivity
    have z3 : 0 ≤ (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) := by positivity
    have z4 : 0 ≤ (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) := by positivity
    have z5 : 0 ≤ (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) := by positivity
    have z6 : 0 ≤ (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) := by positivity
    intro x hx
    rw [hBdef]
    rcases hx with h | h | h | h | h | h <;> rw [h] <;> linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  let g : ℝ → ℝ := fun u => P₁ * u ^ a₁ + P₂ * u ^ a₂
  let k : ℝ → ℝ := fun u => Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃)
  have hfg : ∀ u, P₁ * u ^ a₁ + P₂ * u ^ a₂ + Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) +
      Q₃ * u ^ (-b₃) = g u + k u := by intro u; simp only [g, k]; ring
  have hU0 : 0 < U := by linarith
  have hQU : 0 ≤ Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃) := by positivity
  by_cases c1 : k 1 ≤ g 1
  · refine ⟨1, le_rfl, hU, ?_⟩
    rw [hfg]
    have : g 1 = P₁ + P₂ := by simp [g]
    linarith
  by_cases c2 : g U ≤ k U
  · refine ⟨U, hU, le_rfl, ?_⟩
    rw [hfg]
    have : k U = Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃) := rfl
    have hP0 : 0 ≤ P₁ + P₂ := by linarith
    linarith
  push_neg at c1 c2
  have hpow : ∀ c : ℝ, ContinuousOn (fun u : ℝ => u ^ c) (Set.Icc 1 U) := fun c =>
    ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (by
      have := hx.1; exact (show (0 : ℝ) < x by linarith).ne'))
  have hcont : ContinuousOn (fun u => g u - k u) (Set.Icc 1 U) := by
    simp only [g, k]
    exact (((continuousOn_const.mul (hpow a₁)).add (continuousOn_const.mul (hpow a₂))).sub
      (((continuousOn_const.mul (hpow (-b₁))).add (continuousOn_const.mul (hpow (-b₂)))).add
        (continuousOn_const.mul (hpow (-b₃)))))
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun u => g u - k u) 1) ((fun u => g u - k u) U) := by
    exact ⟨by show g 1 - k 1 ≤ 0; linarith, by show 0 ≤ g U - k U; linarith⟩
  obtain ⟨u, ⟨hu1, huU⟩, hu⟩ := intermediate_value_Icc hU hcont hmem
  have hu' : g u - k u = 0 := hu
  refine ⟨u, hu1, huU, ?_⟩
  have hu0 : 0 < u := by linarith
  have hgk : g u = k u := by linarith
  have hSg : g u = P₁ * u ^ a₁ + P₂ * u ^ a₂ := rfl
  have hSk' : k u = Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) := rfl
  have hS0 : 0 ≤ g u := by rw [hSg]; positivity
  have t1 : 0 ≤ P₁ * u ^ a₁ := by positivity
  have t2 : 0 ≤ P₂ * u ^ a₂ := by positivity
  have r1 : 0 ≤ Q₁ * u ^ (-b₁) := by positivity
  have r2 : 0 ≤ Q₂ * u ^ (-b₂) := by positivity
  have r3 : 0 ≤ Q₃ * u ^ (-b₃) := by positivity
  have hSk : g u = Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) := hgk.trans hSk'
  have key : (g u) ≤ 3 * B := by
    rcases le_total (P₂ * u ^ a₂) (P₁ * u ^ a₁) with hi | hi
    · have hSi : (g u) ≤ 3 * (P₁ * u ^ a₁) := by linarith
      rcases le_or_gt (g u) (3 * (Q₁ * u ^ (-b₁))) with j1 | j1
      · have := balance_core (g u) P₁ Q₁ u a₁ b₁ hS0 hP₁ hQ₁ hu0 ha₁ hb₁ hSi j1
        linarith [hB _ (Or.inl rfl)]
      rcases le_or_gt (g u) (3 * (Q₂ * u ^ (-b₂))) with j2 | j2
      · have := balance_core (g u) P₁ Q₂ u a₁ b₂ hS0 hP₁ hQ₂ hu0 ha₁ hb₂ hSi j2
        linarith [hB _ (Or.inr (Or.inl rfl))]
      have j3 : (g u) ≤ 3 * (Q₃ * u ^ (-b₃)) := by linarith
      have := balance_core (g u) P₁ Q₃ u a₁ b₃ hS0 hP₁ hQ₃ hu0 ha₁ hb₃ hSi j3
      linarith [hB _ (Or.inr (Or.inr (Or.inl rfl)))]
    · have hSi : (g u) ≤ 3 * (P₂ * u ^ a₂) := by linarith
      rcases le_or_gt (g u) (3 * (Q₁ * u ^ (-b₁))) with j1 | j1
      · have := balance_core (g u) P₂ Q₁ u a₂ b₁ hS0 hP₂ hQ₁ hu0 ha₂ hb₁ hSi j1
        linarith [hB _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      rcases le_or_gt (g u) (3 * (Q₂ * u ^ (-b₂))) with j2 | j2
      · have := balance_core (g u) P₂ Q₂ u a₂ b₂ hS0 hP₂ hQ₂ hu0 ha₂ hb₂ hSi j2
        linarith [hB _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
      have j3 : (g u) ≤ 3 * (Q₃ * u ^ (-b₃)) := by linarith
      have := balance_core (g u) P₂ Q₃ u a₂ b₃ hS0 hP₂ hQ₃ hu0 ha₂ hb₃ hSi j3
      linarith [hB _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]
  rw [hfg]
  have hP0 : 0 ≤ P₁ + P₂ := by linarith
  linarith

/-- Proved. Page 8, exponent arithmetic of one balance in Graham and Kolesnik Lemma 2.4
for monomials in n, y and the absolute value k of h. -/
theorem balance3 (n y k p₁ p₂ p₃ q₁ q₂ q₃ a b E₁ E₂ E₃ : ℝ) (hn : 0 < n) (hy : 0 < y)
    (hk : 0 < k) (hab : 0 < a + b)
    (h₁ : p₁ * b + q₁ * a = E₁ * (a + b)) (h₂ : p₂ * b + q₂ * a = E₂ * (a + b))
    (h₃ : p₃ * b + q₃ * a = E₃ * (a + b)) :
    ((n ^ p₁ * y ^ p₂ * k ^ p₃) ^ b * (n ^ q₁ * y ^ q₂ * k ^ q₃) ^ a) ^ (1 / (a + b)) =
      n ^ E₁ * y ^ E₂ * k ^ E₃ := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  obtain ⟨M, rfl⟩ : ∃ M, y = Real.exp M := ⟨Real.log y, (Real.exp_log hy).symm⟩
  obtain ⟨T, rfl⟩ : ∃ T, k = Real.exp T := ⟨Real.log k, (Real.exp_log hk).symm⟩
  simp only [← Real.exp_mul, ← Real.exp_add]
  congr 1
  have hne : a + b ≠ 0 := hab.ne'
  field_simp
  linear_combination L * h₁ + M * h₂ + T * h₃

/-- Proved. One monomial at most perH, since every monomial of perH is nonnegative. -/
theorem le_perH_of (γ n y k z : ℝ) (hn : 0 < n) (hy : 0 < y) (hk : 0 < k)
    (h : z ≤ n ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) ∨
      z ≤ n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) ∨
      z ≤ n ^ (γ / 2 - 1) * y * k ^ ((1 : ℝ) / 2) ∨
      z ≤ n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6) ∨
      z ≤ n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4) ∨
      z ≤ n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * k ^ ((1 : ℝ) / 8) ∨
      z ≤ n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) ∨
      z ≤ n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) ∨
      z ≤ n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * k ^ ((3 : ℝ) / 10) ∨
      z ≤ n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * k ^ ((3 : ℝ) / 14)) :
    z ≤ perH γ n y k := by
  have q1 : 0 ≤ n ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) := by positivity
  have q2 : 0 ≤ n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) := by positivity
  have q3 : 0 ≤ n ^ (γ / 2 - 1) * y * k ^ ((1 : ℝ) / 2) := by positivity
  have q4 : 0 ≤ n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6) := by positivity
  have q5 : 0 ≤ n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4) := by positivity
  have q6 : 0 ≤ n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * k ^ ((1 : ℝ) / 8) := by positivity
  have q7 : 0 ≤ n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) := by positivity
  have q8 : 0 ≤ n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) := by positivity
  have q9 : 0 ≤ n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * k ^ ((3 : ℝ) / 10) := by positivity
  have q10 : 0 ≤ n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * k ^ ((3 : ℝ) / 14) := by
    positivity
  unfold perH
  rcases h with h | h | h | h | h | h | h | h | h | h <;> linarith

/-- Song 2020, pages 7 and 8. The per h display at the top of page 8, assembled from the
cited per u display vaughan_per_u and the cited Graham and Kolesnik Lemma 2.4 choice of u,
with the six balances and five endpoint terms matched to the ten monomials of perH. -/
theorem lambda_sum_per_h_of_split :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ,
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε * perH γ n y |(h : ℝ)| := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₁, hC₁, N₁, hv⟩ := vaughan_per_u γ hγ hγ1 ε hε
  obtain ⟨Cg, hCg, hgk⟩ := gk_lemma_2_4_two_three (1 / 4) 1 (1 / 4) (1 / 6) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C₁ * (1 + 11 * Cg), by positivity, max 1 N₁, ?_⟩
  intro n hn y hy hyu α h hh t
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  set N : ℝ := (n : ℝ) with hNdef
  set k : ℝ := |(h : ℝ)| with hkdef
  have hk1 : 1 ≤ k := by
    rw [hkdef]
    have : (1 : ℝ) ≤ |(h : ℝ)| := by
      have h' : 1 ≤ |h| := Int.one_le_abs hh
      exact_mod_cast h'
    exact this
  have hk0 : 0 < k := by linarith
  have hN0 : 0 < N := by linarith
  have hθ : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy1 : 1 ≤ y := (Real.one_le_rpow hn1 hθ).trans hy.le
  have hy0 : 0 < y := by linarith
  have hyn : y ≤ N := by linarith
  set P₁ : ℝ := N ^ ((3 : ℝ) / 4) * y ^ (0 : ℝ) * k ^ (0 : ℝ) with hP₁
  set P₂ : ℝ := N ^ (γ / 2 - 1) * y ^ (1 : ℝ) * k ^ ((1 : ℝ) / 2) with hP₂
  set Q₁ : ℝ := N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) * k ^ (0 : ℝ) with hQ₁
  set Q₂ : ℝ := N ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6) with hQ₂
  set Q₃ : ℝ := N ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4) with hQ₃
  obtain ⟨u, hu1, huN, hbound⟩ := hgk P₁ P₂ Q₁ Q₂ Q₃ (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) N hn1
  have hvu := hv n (by omega) y hy hyu α h hh t u hu1 huN
  have hu0 : 0 < u := by linarith
  -- the cited display is the Lemma 2.4 sum plus the h to the minus 1/4 term
  have hshape : u ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) +
      u * (k ^ ((1 : ℝ) / 2) * N ^ (γ / 2 - 1) * y) +
      u ^ (-(1 : ℝ) / 4) * (N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
      u ^ (-(1 : ℝ) / 6) * (N ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6)) +
      u ^ (-(1 : ℝ) / 4) * (N ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4)) =
      P₁ * u ^ ((1 : ℝ) / 4) + P₂ * u ^ (1 : ℝ) + Q₁ * u ^ (-((1 : ℝ) / 4)) +
        Q₂ * u ^ (-((1 : ℝ) / 6)) + Q₃ * u ^ (-((1 : ℝ) / 4)) := by
    simp only [hP₁, hP₂, hQ₁, hQ₂, hQ₃, Real.rpow_zero, Real.rpow_one, mul_one, neg_div]
    ring
  -- each of the eleven pieces is at most perH
  have b11 : (P₁ ^ ((1 : ℝ) / 4) * Q₁ ^ ((1 : ℝ) / 4)) ^ (1 / ((1 : ℝ) / 4 + 1 / 4)) ≤
      perH γ N y k := by
    rw [hP₁, hQ₁, balance3 N y k (3 / 4) 0 0 (3 / 4) (1 / 4) 0 (1 / 4) (1 / 4) (3 / 4) (1 / 8) 0 hN0 hy0 hk0 (by norm_num)
      (by ring) (by ring) (by ring)]
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; left; rw [Real.rpow_zero, mul_one]
  have b12 : (P₁ ^ ((1 : ℝ) / 6) * Q₂ ^ ((1 : ℝ) / 4)) ^ (1 / ((1 : ℝ) / 4 + 1 / 6)) ≤
      perH γ N y k := by
    rw [hP₁, hQ₂, balance3 N y k (3 / 4) 0 0 ((γ + 3) / 6) (1 / 3) (1 / 6) (1 / 4) (1 / 6) ((γ + 6) / 10) (1 / 5) (1 / 10) hN0 hy0 hk0
      (by norm_num) (by ring) (by ring) (by ring)]
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; right; right; right; left; exact le_rfl
  have b13 : (P₁ ^ ((1 : ℝ) / 4) * Q₃ ^ ((1 : ℝ) / 4)) ^ (1 / ((1 : ℝ) / 4 + 1 / 4)) ≤
      perH γ N y k := by
    rw [hP₁, hQ₃, balance3 N y k (3 / 4) 0 0 ((γ + 1) / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 4) (γ / 8 + 1 / 2) (1 / 4) (1 / 8) hN0 hy0 hk0
      (by norm_num) (by ring) (by ring) (by ring)]
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; right; right; left; exact le_rfl
  have b21 : (P₂ ^ ((1 : ℝ) / 4) * Q₁ ^ (1 : ℝ)) ^ (1 / ((1 : ℝ) + 1 / 4)) ≤
      perH γ N y k := by
    rw [hP₂, hQ₁, balance3 N y k (γ / 2 - 1) 1 (1 / 2) (3 / 4) (1 / 4) 0 1 (1 / 4) (γ / 10 + 2 / 5) (2 / 5) (1 / 10) hN0 hy0 hk0
      (by norm_num) (by ring) (by ring) (by ring)]
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; right; right; right; right; left; exact le_rfl
  have b22 : (P₂ ^ ((1 : ℝ) / 6) * Q₂ ^ (1 : ℝ)) ^ (1 / ((1 : ℝ) + 1 / 6)) ≤
      perH γ N y k := by
    rw [hP₂, hQ₂, balance3 N y k (γ / 2 - 1) 1 (1 / 2) ((γ + 3) / 6) (1 / 3) (1 / 6) 1 (1 / 6) (3 * γ / 14 + 2 / 7) (3 / 7) (3 / 14) hN0 hy0 hk0
      (by norm_num) (by ring) (by ring) (by ring)]
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; right; right; right; right; right; right; exact le_rfl
  have b23 : (P₂ ^ ((1 : ℝ) / 4) * Q₃ ^ (1 : ℝ)) ^ (1 / ((1 : ℝ) + 1 / 4)) ≤
      perH γ N y k := by
    rw [hP₂, hQ₃, balance3 N y k (γ / 2 - 1) 1 (1 / 2) ((γ + 1) / 4) (1 / 2) (1 / 4) 1 (1 / 4) (3 * γ / 10) (3 / 5) (3 / 10) hN0 hy0 hk0
      (by norm_num) (by ring) (by ring) (by ring)]
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; right; right; right; right; right; left; exact le_rfl
  have e1 : P₁ ≤ perH γ N y k := by
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; left
    rw [hP₁, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hy1 (by norm_num))
  have e2 : P₂ ≤ perH γ N y k := by
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; left
    rw [hP₂, Real.rpow_one]
  have e3 : Q₁ * N ^ (-((1 : ℝ) / 4)) ≤ perH γ N y k := by
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; left
    have hy8 : y ^ ((1 : ℝ) / 8) ≤ N ^ ((1 : ℝ) / 4) :=
      (Real.rpow_le_rpow hy0.le hyn (by norm_num)).trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
    have hm : N ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 4) ≤ N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) := by
      have e1 : y ^ ((1 : ℝ) / 4) = y ^ ((1 : ℝ) / 8) * y ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_add hy0]; norm_num
      have e2 : N ^ ((3 : ℝ) / 4) = N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hN0]; norm_num
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left hy8
        (by positivity : 0 ≤ N ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 8))
      linarith
    have : Q₁ * N ^ (-((1 : ℝ) / 4)) = N ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 4) := by
      rw [hQ₁, Real.rpow_zero, mul_one, mul_comm, ← mul_assoc, ← Real.rpow_add hN0]
      norm_num
    rw [this]; exact hm
  have e4 : Q₂ * N ^ (-((1 : ℝ) / 6)) ≤ perH γ N y k := by
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; left
    apply le_of_eq
    rw [hQ₂, mul_comm, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hN0,
      show -((1 : ℝ) / 6) + (γ + 3) / 6 = (γ + 2) / 6 by ring]
  have e5 : Q₃ * N ^ (-((1 : ℝ) / 4)) ≤ perH γ N y k := by
    apply le_perH_of γ N y k _ hN0 hy0 hk0
    right; right; right; right; left
    apply le_of_eq
    rw [hQ₃, mul_comm, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hN0,
      show -((1 : ℝ) / 4) + (γ + 1) / 4 = γ / 4 by ring]
  have e0 : N ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) ≤ perH γ N y k :=
    le_perH_of γ N y k _ hN0 hy0 hk0 (Or.inl le_rfl)
  have hsum : P₁ * u ^ ((1 : ℝ) / 4) + P₂ * u ^ (1 : ℝ) + Q₁ * u ^ (-((1 : ℝ) / 4)) +
        Q₂ * u ^ (-((1 : ℝ) / 6)) + Q₃ * u ^ (-((1 : ℝ) / 4)) ≤ Cg * (11 * perH γ N y k) := by
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hCg)
    linarith
  have hNe : 0 ≤ N ^ ε := by positivity
  calc ‖lambdaSum γ n y α h t‖ ≤ C₁ * N ^ ε * (N ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) +
        (P₁ * u ^ ((1 : ℝ) / 4) + P₂ * u ^ (1 : ℝ) + Q₁ * u ^ (-((1 : ℝ) / 4)) +
        Q₂ * u ^ (-((1 : ℝ) / 6)) + Q₃ * u ^ (-((1 : ℝ) / 4)))) := by
        refine hvu.trans (le_of_eq ?_)
        rw [← hshape]; ring
    _ ≤ C₁ * N ^ ε * (perH γ N y k + Cg * (11 * perH γ N y k)) :=
        mul_le_mul_of_nonneg_left (add_le_add e0 hsum) (by positivity)
    _ = C₁ * (1 + 11 * Cg) * N ^ ε * perH γ N y k := by ring

/-- Song 2020, pages 5 to 8, the per h estimate displayed at the top of page 8:
x to the minus epsilon times Sigma 1 plus Sigma 2 plus Sigma 3 is bounded by the ten
monomials of perH at k equal to the absolute value of h. Published inputs, in the order the
paper applies them: Dirichlet approximation of alpha by a over q with q at most log n and the
splitting into the Ramanujan type sums S of a plus b and q, page 5; the Vaughan identity,
the paper's Lemma 3.2 with u v at most n, page 5; Iwaniec and Kowalski Corollary 8.13 for
the type I sum Sigma 1, page 6; dyadic division of Sigma 2 and Sigma 3 into the bilinear
sums T of R and S, page 6; Graham and Kolesnik Lemma 2.5, the Weyl differencing
inequality for T of R and S, page 6; Iwaniec and Kowalski Corollary 8.13 for the inner sum
over r, page 7; and Graham and Kolesnik Lemma 2.4 for the choices of L, v and u, pages 7
and 8. -/
theorem lambda_sum_per_h :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ,
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε * perH γ n y |(h : ℝ)| :=
  lambda_sum_per_h_of_split

/-- Proved. Summation over h on page 8, nonnegative exponents: the sum of k to the beta
for k from 1 to H is at most H to the beta plus 1. -/
theorem sum_rpow_le_of_nonneg (β : ℝ) (hβ : 0 ≤ β) (H : ℕ) :
    ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ β ≤ (H : ℝ) ^ (β + 1) := by
  have hle : ∀ k ∈ Finset.Icc 1 H, (k : ℝ) ^ β ≤ (H : ℝ) ^ β := by
    intro k hk
    have hk' := (Finset.mem_Icc.mp hk).2
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk') hβ
  have h1 := Finset.sum_le_card_nsmul _ _ _ hle
  rw [Nat.card_Icc, nsmul_eq_mul] at h1
  have h2 : ((H + 1 - 1 : ℕ) : ℝ) * (H : ℝ) ^ β = (H : ℝ) ^ (β + 1) := by
    rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos H with h | h
    · subst h; simp [Real.zero_rpow (by linarith : β + 1 ≠ 0)]
    · rw [Real.rpow_add (by exact_mod_cast h), Real.rpow_one]; ring
  linarith

/-- Proved. Summation over h on page 8, the one negative exponent: the sum of k to the
minus 1/4 for k from 1 to H is at most 4/3 times H to the 3/4. Proof by induction with the
weighted arithmetic geometric mean inequality, which is the concavity of t to the 3/4. -/
theorem sum_rpow_neg_quarter_le (H : ℕ) :
    ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ (-(1 : ℝ) / 4) ≤ 4 / 3 * (H : ℝ) ^ ((3 : ℝ) / 4) := by
  induction H with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hs0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have amgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 3 / 4) (w₂ := 1 / 4)
      (p₁ := (m : ℝ)) (p₂ := (m : ℝ) + 1) (by norm_num) (by norm_num) (by positivity)
      hs0.le (by norm_num)
    have hq : ((m : ℝ) + 1) ^ ((1 : ℝ) / 4) * ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hs0]; norm_num
    have hq2 : ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) =
        ((m : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
      calc ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) =
            ((m : ℝ) + 1) ^ (1 : ℝ) * ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) := by rw [Real.rpow_one]
        _ = ((m : ℝ) + 1) ^ ((3 : ℝ) / 4) := by rw [← Real.rpow_add hs0]; norm_num
    have hpos : 0 < ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hs0 _
    have h1 := mul_le_mul_of_nonneg_right amgm hpos.le
    have h3 : (m : ℝ) ^ ((3 : ℝ) / 4) * ((m : ℝ) + 1) ^ ((1 : ℝ) / 4) *
        ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) = (m : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [mul_assoc, hq, mul_one]
    have e : (3 / 4 * (m : ℝ) + 1 / 4 * ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) =
        ((m : ℝ) + 1) ^ ((3 : ℝ) / 4) - 3 / 4 * ((m : ℝ) + 1) ^ (-(1 : ℝ) / 4) := by
      rw [← hq2]; ring
    linarith

/-- Proved. Page 8, summation over h of the per h display: the sum of perH over
k from 1 to H is at most twice the S1 polynomial. The term n to the gamma over 10 plus 2/5
times y to the 2/5, which the printed summed display omits, is dominated by the term
n to the gamma plus 6 over 10 times y to the 1/5, since y is at most n. -/
theorem sum_perH_le (γ n y : ℝ) (hn : 0 < n) (hy : 0 < y) (hyn : y ≤ n) (H : ℕ) :
    ∑ k ∈ Finset.Icc 1 H, perH γ n y k ≤ 2 * s1Poly γ n y H := by
  have hdom : n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) ≤ n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) := by
    have e1 : n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) =
        (n ^ (γ / 10 + 2 / 5) * y ^ ((1 : ℝ) / 5)) * y ^ ((1 : ℝ) / 5) := by
      rw [mul_assoc, ← Real.rpow_add hy]; norm_num
    have e2 : n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) =
        (n ^ (γ / 10 + 2 / 5) * y ^ ((1 : ℝ) / 5)) * n ^ ((1 : ℝ) / 5) := by
      rw [mul_comm (n ^ (γ / 10 + 2 / 5)), mul_assoc, ← Real.rpow_add hn]
      rw [mul_comm]; congr 1; congr 1; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le hyn (by norm_num)) (by positivity)
  have s1 := sum_rpow_neg_quarter_le H
  have s3 := sum_rpow_le_of_nonneg ((1 : ℝ) / 2) (by norm_num) H
  have s4 := sum_rpow_le_of_nonneg ((1 : ℝ) / 6) (by norm_num) H
  have s5 := sum_rpow_le_of_nonneg ((1 : ℝ) / 4) (by norm_num) H
  have s6 := sum_rpow_le_of_nonneg ((1 : ℝ) / 8) (by norm_num) H
  have s7 := sum_rpow_le_of_nonneg ((1 : ℝ) / 10) (by norm_num) H
  have s9 := sum_rpow_le_of_nonneg ((3 : ℝ) / 10) (by norm_num) H
  have s10 := sum_rpow_le_of_nonneg ((3 : ℝ) / 14) (by norm_num) H
  have hS7 : 0 ≤ ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 10) := by positivity
  have t1 := mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ n ^ (1 - γ / 4))
  have t3 := mul_le_mul_of_nonneg_left s3 (by positivity : 0 ≤ n ^ (γ / 2 - 1) * y)
  have t4 := mul_le_mul_of_nonneg_left s4
    (by positivity : 0 ≤ n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3))
  have t5 := mul_le_mul_of_nonneg_left s5
    (by positivity : 0 ≤ n ^ (γ / 4) * y ^ ((1 : ℝ) / 2))
  have t6 := mul_le_mul_of_nonneg_left s6
    (by positivity : 0 ≤ n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4))
  have t7 := mul_le_mul_of_nonneg_left s7
    (by positivity : 0 ≤ n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5))
  have t8 := mul_le_mul_of_nonneg_right hdom hS7
  have t9 := mul_le_mul_of_nonneg_left s9
    (by positivity : 0 ≤ n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5))
  have t10 := mul_le_mul_of_nonneg_left s10
    (by positivity : 0 ≤ n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7))
  have hH0 : 0 ≤ (H : ℝ) ^ ((3 : ℝ) / 4) := by positivity
  have hn1 : 0 ≤ n ^ (1 - γ / 4) * (H : ℝ) ^ ((3 : ℝ) / 4) := by positivity
  have hP : s1Poly γ n y H =
      n ^ (1 - γ / 4) * (H : ℝ) ^ ((3 : ℝ) / 4) +
      n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * (H : ℝ) ^ ((1 : ℝ) / 8 + 1) +
      n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * (H : ℝ) ^ ((3 : ℝ) / 14 + 1) +
      n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) * (H : ℝ) +
      n ^ (γ / 2 - 1) * y * (H : ℝ) ^ ((1 : ℝ) / 2 + 1) +
      n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * (H : ℝ) ^ ((3 : ℝ) / 10 + 1) +
      n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * (H : ℝ) ^ ((1 : ℝ) / 10 + 1) +
      n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * (H : ℝ) ^ ((1 : ℝ) / 6 + 1) +
      n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * (H : ℝ) ^ ((1 : ℝ) / 4 + 1) := by
    simp only [s1Poly, s1Terms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Real.rpow_zero, Real.rpow_one, mul_one, add_zero]
    rw [show (γ + 4) / 8 = γ / 8 + 1 / 2 by ring, show (3 * γ + 4) / 14 = 3 * γ / 14 + 2 / 7 by ring]
    norm_num
    ring_nf
  have hL : ∑ k ∈ Finset.Icc 1 H, perH γ n y k =
      n ^ (1 - γ / 4) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ (-(1 : ℝ) / 4) +
      n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) * (H : ℝ) +
      n ^ (γ / 2 - 1) * y * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 2) +
      n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 6) +
      n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 4) +
      n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 8) +
      n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 10) +
      n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((1 : ℝ) / 10) +
      n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((3 : ℝ) / 10) +
      n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) *
        ∑ k ∈ Finset.Icc 1 H, (k : ℝ) ^ ((3 : ℝ) / 14) := by
    simp only [perH, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul, Nat.add_sub_cancel]
    ring
  have p2 : 0 ≤ n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * (H : ℝ) ^ ((1 : ℝ) / 8 + 1) := by
    positivity
  have p3 : 0 ≤ n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * (H : ℝ) ^ ((3 : ℝ) / 14 + 1) := by
    positivity
  have p4 : 0 ≤ n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) * (H : ℝ) := by positivity
  have p5 : 0 ≤ n ^ (γ / 2 - 1) * y * (H : ℝ) ^ ((1 : ℝ) / 2 + 1) := by positivity
  have p6 : 0 ≤ n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * (H : ℝ) ^ ((3 : ℝ) / 10 + 1) := by
    positivity
  have p7 : 0 ≤ n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * (H : ℝ) ^ ((1 : ℝ) / 10 + 1) := by
    positivity
  have p8 : 0 ≤ n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * (H : ℝ) ^ ((1 : ℝ) / 6 + 1) := by
    positivity
  have p9 : 0 ≤ n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * (H : ℝ) ^ ((1 : ℝ) / 4 + 1) := by positivity
  rw [hL, hP]
  linarith

/-- Song 2020, pages 5 through 8. The S1 estimate after summing over h, now assembled from
the cited partial summation step s1_lambda_reduction, the cited per h estimate
lambda_sum_per_h, and the proved summation over h, sum_perH_le. -/
theorem s1_estimate_of_split :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H →
              ‖truncatedSum a H γ n y α‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (n : ℝ) ^ ε * s1Poly γ n y H) := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₁, hC₁, N₁, hred⟩ := s1_lambda_reduction γ hγ hγ1 (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂, N₂, hper⟩ := lambda_sum_per_h γ hγ hγ1 (ε / 2) (by positivity)
  refine ⟨C₁ * (1 + 4 * C₂), by positivity, max 1 (max N₁ N₂), ?_⟩
  intro K hK a ha n hn y hy hyu α H hH
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  set N : ℝ := (n : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hθ : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy1 : 1 ≤ y := (Real.one_le_rpow hn1 hθ).trans hy.le
  have hy0 : 0 < y := by linarith
  have hyn : y ≤ N := by linarith
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hn1 hε.le
  have hee : N ^ (ε / 2) * N ^ (ε / 2) = N ^ ε := by
    rw [← Real.rpow_add hN0, add_halves]
  let B : ℤ → ℝ := fun h => C₂ * N ^ (ε / 2) * perH γ N y |(h : ℝ)|
  have hB : ∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖lambdaSum γ n y α h t‖ ≤ B h :=
    fun h hh _ t => hper n (by omega) y hy hyu α h hh t
  have hr := hred K hK a ha n (by omega) y hy hyu α H hH B hB
  have hsumB : ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) =
      2 * C₂ * N ^ (ε / 2) * ∑ k ∈ Finset.Icc 1 H, perH γ N y k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [B]
    have : |((-(k : ℤ) : ℤ) : ℝ)| = (k : ℝ) := by
      push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
    have h2 : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by push_cast; exact abs_of_nonneg (by positivity)
    rw [this, h2]; ring
  have hsum := sum_perH_le γ N y hN0 hy0 hyn H
  have hP0 : 0 ≤ s1Poly γ N y H := by
    unfold s1Poly
    apply List.sum_nonneg
    intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  have hHn : (H : ℝ) * N ^ ((1 : ℝ) / 2) ≤ N ^ ε * s1Poly γ N y H := by
    have h4 : N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) * (H : ℝ) ^ (1 : ℝ) ≤ s1Poly γ N y H := by
      unfold s1Poly
      apply List.single_le_sum
      · intro x hx
        obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
        positivity
      · exact List.mem_map.mpr ⟨(3 / 4, 1 / 8, 1), by simp [s1Terms], rfl⟩
    rw [Real.rpow_one] at h4
    have h5 : N ^ ((1 : ℝ) / 2) ≤ N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) := by
      calc N ^ ((1 : ℝ) / 2) ≤ N ^ ((3 : ℝ) / 4) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ ≤ N ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) :=
            le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hy1 (by norm_num))
    have hH0 : (0 : ℝ) ≤ H := by positivity
    have h6 := mul_le_mul_of_nonneg_left h5 hH0
    have h7 := le_mul_of_one_le_left hP0 hNe
    nlinarith
  have hK0 : 0 ≤ K := by linarith
  have hfin : N ^ (3 / 2 - γ) + (H : ℝ) * N ^ ((1 : ℝ) / 2) +
      N ^ (ε / 2) * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ))) ≤
      (1 + 4 * C₂) * (N ^ (3 / 2 - γ) + N ^ ε * s1Poly γ N y H) := by
    rw [hsumB, show N ^ (ε / 2) * (2 * C₂ * N ^ (ε / 2) * ∑ k ∈ Finset.Icc 1 H, perH γ N y k) =
      2 * C₂ * N ^ ε * ∑ k ∈ Finset.Icc 1 H, perH γ N y k by rw [← hee]; ring]
    have h8 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * C₂ * N ^ ε)
    have h9 : 0 ≤ N ^ (3 / 2 - γ) := by positivity
    have h10 : 0 ≤ C₂ * N ^ (3 / 2 - γ) := by positivity
    have h11 : 0 ≤ C₂ * (N ^ ε * s1Poly γ N y H) := by positivity
    nlinarith
  calc ‖truncatedSum a H γ n y α‖ ≤ C₁ * K * (N ^ (3 / 2 - γ) + (H : ℝ) * N ^ ((1 : ℝ) / 2) +
        N ^ (ε / 2) * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := hr
    _ ≤ C₁ * K * ((1 + 4 * C₂) * (N ^ (3 / 2 - γ) + N ^ ε * s1Poly γ N y H)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = C₁ * (1 + 4 * C₂) * K * (N ^ (3 / 2 - γ) + N ^ ε * s1Poly γ N y H) := by ring

/-- Song 2020, pages 5 through 8, the S1 estimate after summing over h:
S1 is bounded by n to the 3/2 minus gamma plus n to the epsilon times the nine H monomials.
Published inputs used by the paper for this display: the reduction to Lambda weighted sums
by partial summation, page 5; the Vaughan identity, the paper's Lemma 3.2, page 5;
Iwaniec and Kowalski Corollary 8.13 for Sigma 1, page 6, and for the inner sums of
T(R,S), page 7; Graham and Kolesnik Lemma 2.5 for T(R,S), page 6; Graham and Kolesnik
Lemma 2.4 for the choices of L and u, page 7; and the additive character identity, page 8.
The coefficient hypothesis is the paper's bound a_h less than 1 over h, with constant K. -/
theorem s1_estimate :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H →
              ‖truncatedSum a H γ n y α‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (n : ℝ) ^ ε * s1Poly γ n y H) :=
  s1_estimate_of_split

/-- Proved. Graham and Kolesnik, Van der Corput's Method of Exponential Sums, Lemma 2.4,
in the case of a single negative power and lower endpoint H1 equal to 1, as Song 2020 uses
it on page 8 to choose H: for L(H) the sum of A_i H to the a_i plus B over H, some integer H
with 1 at most H at most H2 has L(H) bounded by the sum of the balanced terms
A_i to the 1 over a_i plus 1 times B to the a_i over a_i plus 1, plus the endpoint terms
A_i at H equal to 1 and B over H2. The constant depends only on the exponents, which
absorbs the rounding to an integer. Proved here directly, not cited. -/
theorem gk_lemma_2_4 {m : ℕ} (e : Fin m → ℝ) (he : ∀ i, 0 < e i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Fin m → ℝ) (B : ℝ), (∀ i, 0 ≤ A i) → 0 ≤ B →
      ∀ H₂ : ℕ, 1 ≤ H₂ →
      ∃ H : ℕ, 1 ≤ H ∧ H ≤ H₂ ∧
        ∑ i, A i * (H : ℝ) ^ (e i) + B * (H : ℝ)⁻¹ ≤
          C * (∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) + ∑ i, A i + B * (H₂ : ℝ)⁻¹) := by
  refine ⟨∑ i, (2 : ℝ) ^ (e i) + 1, by positivity, ?_⟩
  intro A B hA hB H₂ hH₂
  set S := ∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) + ∑ i, A i with hS
  have hb0 : ∀ i, 0 ≤ (A i * B ^ (e i)) ^ (1 / (e i + 1)) := fun i => by
    have := hA i; positivity
  have hS1 : 0 ≤ ∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) :=
    Finset.sum_nonneg (fun i _ => hb0 i)
  have hS2 : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  have hAS : ∀ i, A i ≤ S := fun i => by
    have := Finset.single_le_sum (f := A) (fun j _ => hA j) (Finset.mem_univ i)
    linarith
  have hbS : ∀ i, A i * B ^ (e i) ≤ S ^ (e i + 1) := by
    intro i
    have h1 : (A i * B ^ (e i)) ^ (1 / (e i + 1)) ≤ S := by
      have := Finset.single_le_sum (f := fun j => (A j * B ^ (e j)) ^ (1 / (e j + 1)))
        (fun j _ => hb0 j) (Finset.mem_univ i)
      linarith
    have hne : e i + 1 ≠ 0 := by linarith [he i]
    have h2 := Real.rpow_le_rpow (hb0 i) h1 (by linarith [he i] : 0 ≤ e i + 1)
    rwa [one_div, Real.rpow_inv_rpow (by have := hA i; positivity) hne] at h2
  have hC1 : (1 : ℝ) ≤ ∑ i, (2 : ℝ) ^ (e i) + 1 := by
    have : 0 ≤ ∑ i, (2 : ℝ) ^ (e i) := by positivity
    linarith
  have hBH₂ : 0 ≤ B * (H₂ : ℝ)⁻¹ := by positivity
  have hfin := le_mul_of_one_le_left hBH₂ hC1
  rcases (show 0 ≤ S by linarith).lt_or_eq with hSpos | hS0
  · set H₀ : ℕ := max 1 ⌈B / S⌉₊ with hH₀
    refine ⟨min H₀ H₂, le_min (le_max_left _ _) hH₂, min_le_right _ _, ?_⟩
    have hH₀1 : 1 ≤ H₀ := le_max_left _ _
    have hH₀R : (1 : ℝ) ≤ H₀ := by exact_mod_cast hH₀1
    have hH₂R : (1 : ℝ) ≤ H₂ := by exact_mod_cast hH₂
    have hBH₀ : B * (H₀ : ℝ)⁻¹ ≤ S := by
      have hc : B / S ≤ (H₀ : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
      rw [div_le_iff₀ hSpos] at hc
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
      linarith
    have hHle : ((min H₀ H₂ : ℕ) : ℝ) ≤ H₀ := by exact_mod_cast min_le_left _ _
    have hHpos : (0 : ℝ) < ((min H₀ H₂ : ℕ) : ℝ) := by
      have : 1 ≤ min H₀ H₂ := le_min hH₀1 hH₂
      exact_mod_cast (show 0 < min H₀ H₂ by omega)
    have hBH : B * ((min H₀ H₂ : ℕ) : ℝ)⁻¹ ≤ S + B * (H₂ : ℝ)⁻¹ := by
      rcases min_choice H₀ H₂ with h | h <;> rw [h] <;> linarith
    have hH₀2 : (H₀ : ℝ) ≤ 2 * max 1 (B / S) := by
      rw [hH₀, Nat.cast_max, Nat.cast_one]
      apply max_le
      · linarith [le_max_left 1 (B / S)]
      · rcases le_total (B / S) 1 with h | h
        · have h' : ⌈B / S⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using h)
          have : (⌈B / S⌉₊ : ℝ) ≤ 1 := by exact_mod_cast h'
          linarith [le_max_left 1 (B / S)]
        · have := Nat.ceil_lt_add_one (show 0 ≤ B / S by positivity)
          linarith [le_max_right 1 (B / S)]
    have key : ∀ i, A i * (max 1 (B / S)) ^ (e i) ≤ S := by
      intro i
      rcases le_total (B / S) 1 with h | h
      · rw [max_eq_left h, Real.one_rpow, mul_one]
        exact hAS i
      · rw [max_eq_right h, Real.div_rpow hB hSpos.le, ← mul_div_assoc,
          div_le_iff₀ (Real.rpow_pos_of_pos hSpos _)]
        calc A i * B ^ e i ≤ S ^ (e i + 1) := hbS i
          _ = S * S ^ e i := by rw [Real.rpow_add hSpos, Real.rpow_one]; ring
    have hterm : ∀ i, A i * ((min H₀ H₂ : ℕ) : ℝ) ^ (e i) ≤ 2 ^ (e i) * S := by
      intro i
      have hr1 : 1 ≤ max 1 (B / S) := le_max_left _ _
      calc A i * ((min H₀ H₂ : ℕ) : ℝ) ^ (e i)
          ≤ A i * (2 * max 1 (B / S)) ^ (e i) := by
            apply mul_le_mul_of_nonneg_left _ (hA i)
            exact Real.rpow_le_rpow hHpos.le (hHle.trans hH₀2) (he i).le
        _ = 2 ^ (e i) * (A i * (max 1 (B / S)) ^ (e i)) := by
            rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
        _ ≤ 2 ^ (e i) * S := mul_le_mul_of_nonneg_left (key i) (by positivity)
    have hsum : ∑ i, A i * ((min H₀ H₂ : ℕ) : ℝ) ^ (e i) ≤ (∑ i, (2 : ℝ) ^ (e i)) * S := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => hterm i)
    have hexp : (∑ i, (2 : ℝ) ^ (e i) + 1) * (S + B * (H₂ : ℝ)⁻¹) =
        (∑ i, (2 : ℝ) ^ (e i)) * S + S + (∑ i, (2 : ℝ) ^ (e i) + 1) * (B * (H₂ : ℝ)⁻¹) := by
      ring
    linarith
  · refine ⟨H₂, hH₂, le_rfl, ?_⟩
    have hA0 : ∀ i, A i = 0 := fun i => le_antisymm (by linarith [hAS i]) (hA i)
    have h0 : ∑ i, A i * (H₂ : ℝ) ^ (e i) = 0 := by simp [hA0]
    rw [h0, ← hS0]
    linarith

/-- Proved. Page 8, exponent arithmetic of the balance in Graham and Kolesnik Lemma 2.4:
balancing n to the eps times n to the e1 times y to the e2 times H to the a against
n to the eps times y times n to the 1 minus gamma over H gives n to the eps times
n to the E times y to the F with E and F as below. -/
theorem balance_rpow (n y ε γ e1 e2 a E F : ℝ) (hn : 0 < n) (hy : 0 < y) (ha : 0 < a)
    (hE : e1 + a * (1 - γ) = E * (a + 1)) (hF : e2 + a = F * (a + 1)) :
    ((n ^ ε * (n ^ e1 * y ^ e2)) * (n ^ ε * (y * n ^ (1 - γ))) ^ a) ^ (1 / (a + 1)) =
      n ^ ε * (n ^ E * y ^ F) := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  obtain ⟨M, rfl⟩ : ∃ M, y = Real.exp M := ⟨Real.log y, (Real.exp_log hy).symm⟩
  simp only [← Real.exp_mul, ← Real.exp_add]
  congr 1
  have ha1 : a + 1 ≠ 0 := by linarith
  field_simp
  linear_combination L * hE + M * hF

/-- Proved. Page 8. Every optimized monomial is at most the optimized budget. -/
theorem le_budget (γ n y : ℝ) (hn : 0 ≤ n) (hy : 0 ≤ y) (E F : ℝ)
    (h : (E, F) ∈ terms γ) : n ^ E * y ^ F ≤ budget γ n y := by
  unfold budget
  apply List.single_le_sum
  · intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  · exact List.mem_map.mpr ⟨(E, F), h, rfl⟩

/-- Pages 5 through 8, S1 estimates and parameter choices.
Published inputs: Iwaniec and Kowalski Corollary 8.13, the cited Vaughan identity,
and Graham and Kolesnik Lemmas 2.4 and 2.5.
The S2 monomial uses the balance derived from page 5, as recorded in STATEMENTS.md. -/
theorem optimized_truncated_bound :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∃ H : ℕ, 1 ≤ H ∧
              ‖truncatedSum a H γ n y α‖ + tailBudget γ n y H ≤
                C * K * (n : ℝ) ^ ε * budget γ n y := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₁, hC₁, N₀, hs1⟩ := s1_estimate γ hγ hγ1 ε hε
  let e : Fin 10 → ℝ := ![3 / 4, 9 / 8, 17 / 14, 1, 3 / 2, 13 / 10, 11 / 10, 7 / 6, 5 / 4, 1 / 2]
  obtain ⟨Cg, hCg, hgk⟩ := gk_lemma_2_4 e (by intro i; fin_cases i <;> norm_num [e])
  refine ⟨C₁ + max 1 C₁ * Cg * 21, by positivity, N₀, ?_⟩
  intro K hK a ha n hn y hy hyu α
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hse : songExponent γ ≠ 0 := by unfold songExponent; intro h; linarith
      simp [Real.zero_rpow hse] at hy hyu
      linarith
    · exact_mod_cast h
  set N : ℝ := (n : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hN0 _).trans hy
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hn1 hε.le
  let t : Fin 10 → ℝ × ℝ :=
    ![(1 - γ / 4, 0), ((γ + 4) / 8, 1 / 4), ((3 * γ + 4) / 14, 3 / 7), (3 / 4, 1 / 8),
      (γ / 2 - 1, 1), (3 * γ / 10, 3 / 5), ((γ + 6) / 10, 1 / 5), ((γ + 2) / 6, 1 / 3),
      (γ / 4, 1 / 2), (1 - γ / 2, 0)]
  let A : Fin 10 → ℝ := fun i => N ^ ε * (N ^ (t i).1 * y ^ (t i).2)
  let B : ℝ := N ^ ε * (y * N ^ (1 - γ))
  obtain ⟨H, hH, -, hL⟩ := hgk A B (by intro i; positivity) (by positivity)
    (⌈B⌉₊ + 1) (by omega)
  refine ⟨H, hH, ?_⟩
  have hs := hs1 K hK a ha n hn y hy hyu α H hH
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  set M : ℝ := N ^ ε * budget γ N y with hM
  have hbud0 : 0 ≤ budget γ N y := by
    unfold budget
    apply List.sum_nonneg
    intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  have hM0 : 0 ≤ M := by positivity
  -- each balanced term and each endpoint term is at most M
  have hgen : ∀ e1 e2 c E F : ℝ, 0 < c → e1 + c * (1 - γ) = E * (c + 1) →
      e2 + c = F * (c + 1) → (E, F) ∈ terms γ →
      ((N ^ ε * (N ^ e1 * y ^ e2)) * B ^ c) ^ (1 / (c + 1)) ≤ M := by
    intro e1 e2 c E F hc hE hF hmem
    rw [balance_rpow N y ε γ e1 e2 c E F hN0 hy0 hc hE hF]
    exact mul_le_mul_of_nonneg_left (le_budget γ N y hN0.le hy0.le E F hmem) (by positivity)
  have hend : ∀ e1 e2 E : ℝ, e1 ≤ E → (E, e2) ∈ terms γ →
      N ^ ε * (N ^ e1 * y ^ e2) ≤ M := by
    intro e1 e2 E hle hmem
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc N ^ e1 * y ^ e2 ≤ N ^ E * y ^ e2 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hle) (by positivity)
      _ ≤ budget γ N y := le_budget γ N y hN0.le hy0.le E e2 hmem
  have hbal : ∀ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) ≤ M := by
    intro i
    fin_cases i
    · exact hgen (1 - γ / 4) (0) (3 / 4) (1 - 4 * γ / 7) (3 / 7) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((γ + 4) / 8) (1 / 4) (9 / 8) (13 / 17 - 8 * γ / 17) (11 / 17) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((3 * γ + 4) / 14) (3 / 7) (17 / 14) (21 / 31 - 14 * γ / 31) (23 / 31) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (3 / 4) (1 / 8) (1) (7 / 8 - γ / 2) (9 / 16) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (γ / 2 - 1) (1) (3 / 2) (1 / 5 - 2 * γ / 5) (1) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (3 * γ / 10) (3 / 5) (13 / 10) (13 / 23 - 10 * γ / 23) (19 / 23) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((γ + 6) / 10) (1 / 5) (11 / 10) (17 / 21 - 10 * γ / 21) (13 / 21) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen ((γ + 2) / 6) (1 / 3) (7 / 6) (9 / 13 - 6 * γ / 13) (9 / 13) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (γ / 4) (1 / 2) (5 / 4) (5 / 9 - 4 * γ / 9) (7 / 9) (by norm_num) (by ring) (by ring)
        (by simp [terms])
    · exact hgen (1 - γ / 2) (0) (1 / 2) (1 - 2 * γ / 3) (1 / 3) (by norm_num) (by ring) (by ring)
        (by simp [terms])
  have hA : ∀ i, A i ≤ M := by
    intro i
    fin_cases i
    · exact hend (1 - γ / 4) (0) (1 - γ / 4) (by linarith) (by simp [terms])
    · exact hend ((γ + 4) / 8) (1 / 4) (γ / 8 + 1 / 2) (by linarith) (by simp [terms])
    · exact hend ((3 * γ + 4) / 14) (3 / 7) (3 * γ / 14 + 2 / 7) (by linarith) (by simp [terms])
    · exact hend (3 / 4) (1 / 8) (3 / 4) (by linarith) (by simp [terms])
    · exact hend (γ / 2 - 1) (1) (1 / 5 - 2 * γ / 5) (by linarith) (by simp [terms])
    · exact hend (3 * γ / 10) (3 / 5) (3 * γ / 10) (by linarith) (by simp [terms])
    · exact hend ((γ + 6) / 10) (1 / 5) (γ / 10 + 3 / 5) (by linarith) (by simp [terms])
    · exact hend ((γ + 2) / 6) (1 / 3) ((γ + 2) / 6) (by linarith) (by simp [terms])
    · exact hend (γ / 4) (1 / 2) (γ / 4) (by linarith) (by simp [terms])
    · exact hend (1 - γ / 2) (0) (1 - γ / 4) (by linarith) (by simp [terms])
  have hbase : N ^ (3 / 2 - γ) ≤ M := by
    have h := hend (3 / 2 - γ) 0 (3 / 2 - γ) le_rfl (by simp [terms])
    have : N ^ (3 / 2 - γ) ≤ N ^ ε * (N ^ (3 / 2 - γ) * y ^ (0 : ℝ)) := by
      rw [Real.rpow_zero, mul_one]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hN0.le _) hNe
    linarith
  have hR : ∑ i, (A i * B ^ (e i)) ^ (1 / (e i + 1)) + ∑ i, A i +
      B * ((⌈B⌉₊ + 1 : ℕ) : ℝ)⁻¹ ≤ 21 * M := by
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbal i)
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hA i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
    push_cast at h1 h2
    have hB2 : B * ((⌈B⌉₊ + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      have hc : B ≤ ((⌈B⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith [Nat.le_ceil B]
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact hc
    have hM1 : 1 ≤ M := (Real.one_le_rpow hn1 (by linarith)).trans hbase
    linarith
  -- the S1 polynomial and the S2 budget are the Lemma 2.4 sum
  have hQ : ∑ i, A i * (H : ℝ) ^ (e i) + B * (H : ℝ)⁻¹ =
      N ^ ε * s1Poly γ N y H + N ^ ε * (N ^ (1 - γ / 2) * (H : ℝ) ^ ((1 : ℝ) / 2)) +
        N ^ ε * ((H : ℝ)⁻¹ * y * N ^ (1 - γ)) := by
    simp [A, B, t, e, Fin.sum_univ_succ, s1Poly, s1Terms]
    ring
  have hP0 : 0 ≤ s1Poly γ N y H := by
    unfold s1Poly
    apply List.sum_nonneg
    intro x hx
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hx
    positivity
  have hT : tailBudget γ N y H ≤ N ^ ε * (N ^ (1 - γ / 2) * (H : ℝ) ^ ((1 : ℝ) / 2)) +
        N ^ ε * ((H : ℝ)⁻¹ * y * N ^ (1 - γ)) := by
    unfold tailBudget
    have h1 : 0 ≤ N ^ (1 - γ / 2) * (H : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    have h2 : 0 ≤ (H : ℝ)⁻¹ * y * N ^ (1 - γ) := by positivity
    have h3 := le_mul_of_one_le_left h1 hNe
    have h4 := le_mul_of_one_le_left h2 hNe
    linarith
  have hT0 : 0 ≤ tailBudget γ N y H := by unfold tailBudget; positivity
  have hPT : N ^ ε * s1Poly γ N y H + tailBudget γ N y H ≤ Cg * (21 * M) := by
    calc _ ≤ ∑ i, A i * (H : ℝ) ^ (e i) + B * (H : ℝ)⁻¹ := by rw [hQ]; linarith
      _ ≤ _ := hL
      _ ≤ _ := mul_le_mul_of_nonneg_left hR hCg
  have hK0 : 0 ≤ K := by linarith
  have hmax : 1 ≤ max 1 C₁ := le_max_left _ _
  have hmax' : C₁ ≤ max 1 C₁ := le_max_right _ _
  have hPs0 : 0 ≤ N ^ ε * s1Poly γ N y H := by positivity
  have hstep : C₁ * K * (N ^ ε * s1Poly γ N y H) + tailBudget γ N y H ≤
      max 1 C₁ * K * (N ^ ε * s1Poly γ N y H + tailBudget γ N y H) := by
    have e1 : C₁ * K * (N ^ ε * s1Poly γ N y H) ≤ max 1 C₁ * K * (N ^ ε * s1Poly γ N y H) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax' hK0) hPs0
    have e2 : tailBudget γ N y H ≤ max 1 C₁ * K * tailBudget γ N y H :=
      le_mul_of_one_le_left hT0 (one_le_mul_of_one_le_of_one_le hmax hK)
    rw [mul_add]
    linarith
  have hfin : ‖truncatedSum a H γ n y α‖ + tailBudget γ N y H ≤
      C₁ * K * M + max 1 C₁ * K * (Cg * (21 * M)) := by
    have h3 : C₁ * K * N ^ (3 / 2 - γ) ≤ C₁ * K * M :=
      mul_le_mul_of_nonneg_left hbase (mul_nonneg hC₁ hK0)
    have h4 := mul_le_mul_of_nonneg_left hPT (mul_nonneg (by linarith : 0 ≤ max 1 C₁) hK0)
    have hs' : ‖truncatedSum a H γ n y α‖ ≤
        C₁ * K * N ^ (3 / 2 - γ) + C₁ * K * (N ^ ε * s1Poly γ N y H) := by
      rw [← mul_add]; exact hs
    linarith
  calc ‖truncatedSum a H γ n y α‖ + tailBudget γ N y H
      ≤ C₁ * K * M + max 1 C₁ * K * (Cg * (21 * M)) := hfin
    _ = (C₁ + max 1 C₁ * Cg * 21) * K * N ^ ε * budget γ N y := by rw [hM]; ring

/-- Page 8, last sentence. Endpoint exponent comparisons bound each monomial. -/
theorem monomial_le (n y θ A B D E : ℝ) (hn : 1 ≤ n) (hy : n ^ θ ≤ y)
    (hyn : y ≤ n) (hlo : A + θ * (B - E) ≤ D) (hhi : A + B - E ≤ D) :
    n ^ A * y ^ B ≤ n ^ D * y ^ E := by
  have hn0 : 0 < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans_le hy
  have hratio : n ^ A * y ^ (B - E) ≤ n ^ D := by
    by_cases hBE : B ≤ E
    · calc
        n ^ A * y ^ (B - E) ≤ n ^ A * (n ^ θ) ^ (B - E) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hy (by linarith)
        _ = n ^ (A + θ * (B - E)) := by
          rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
        _ ≤ n ^ D := Real.rpow_le_rpow_of_exponent_le hn hlo
    · calc
        n ^ A * y ^ (B - E) ≤ n ^ A * n ^ (B - E) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow hy0.le hyn (by linarith)
        _ = n ^ (A + B - E) := by rw [← Real.rpow_add hn0]; congr 1; ring
        _ ≤ n ^ D := Real.rpow_le_rpow_of_exponent_le hn hhi
  calc
    n ^ A * y ^ B = (n ^ A * y ^ (B - E)) * y ^ E := by
      rw [mul_assoc, ← Real.rpow_add hy0]
      congr 2
      ring
    _ ≤ n ^ D * y ^ E := mul_le_mul_of_nonneg_right hratio (by positivity)

/-- Page 8, last sentence. The twenty monomials are bounded on the window of Theorem 1. -/
theorem budget_le (γ n y : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1)
    (hn : 1 ≤ n) (hy : n ^ songExponent γ ≤ y) (hyn : y ≤ n) :
    budget γ n y ≤ 20 * (n ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31)) := by
  have hexps : ∀ ab ∈ terms γ,
      ab.1 + songExponent γ * (ab.2 - 23 / 31) ≤ 21 / 31 - 14 * γ / 31 ∧
      ab.1 + ab.2 - 23 / 31 ≤ 21 / 31 - 14 * γ / 31 := by
    intro ab hab
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp; unfold songExponent; constructor <;> linarith
  have hterm : ∀ ab ∈ terms γ,
      n ^ ab.1 * y ^ ab.2 ≤ n ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31) := by
    intro ab hab
    exact monomial_le n y (songExponent γ) ab.1 ab.2 _ _ hn hy hyn
      (hexps ab hab).1 (hexps ab hab).2
  unfold budget
  have hsum := List.sum_le_length_nsmul (terms γ |>.map (fun ab => n ^ ab.1 * y ^ ab.2))
    (n ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31)) (by
      intro x hx
      obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hx
      exact hterm ab hab)
  simpa [terms, nsmul_eq_mul] using hsum

end

end LeanLab.Song2020.Decomp139
