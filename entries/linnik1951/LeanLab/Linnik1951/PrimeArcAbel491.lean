module

public import LeanLab.PNTPort.Selberg.WeightedMeanB
public import LeanLab.PNTPort.Selberg.AbelWeight

/-!
P0093 pages 159 through 161. Mean square of the von Mangoldt series with the
weights one over ln n, the analytic core of equations 6.1 and 6.3 on the arc.
From the mean square of primes in short intervals under the Riemann hypothesis
in PNTPort.Selberg and partial summation against the decreasing weights.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- The weights one over ln of max n 2 are antitone. -/
private lemma logWeight_antitone491 :
    Antitone (fun n : ℕ => 1 / Real.log ((max n 2 : ℕ) : ℝ)) := by
  intro m n hmn
  have h2 : (2 : ℝ) ≤ ((max m 2 : ℕ) : ℝ) := by exact_mod_cast le_max_right m 2
  have hle : ((max m 2 : ℕ) : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := by
    exact_mod_cast max_le_max hmn le_rfl
  have hpos : 0 < Real.log ((max m 2 : ℕ) : ℝ) := Real.log_pos (by linarith)
  exact one_div_le_one_div_of_le hpos (Real.log_le_log (by linarith) hle)

/-- The weights one over ln of max n 2 are nonnegative. -/
private lemma logWeight_nonneg491 (n : ℕ) : 0 ≤ 1 / Real.log ((max n 2 : ℕ) : ℝ) := by
  have h2 : (2 : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := by exact_mod_cast le_max_right n 2
  exact le_of_lt (one_div_pos.mpr (Real.log_pos (by linarith)))

/-- The damped terms are continuous in the frequency. -/
private lemma term_continuous491 (N n : ℕ) : Continuous (fun β : ℝ =>
    (Real.exp (-(n / N)) : ℂ) *
      (LeanLab.PNTPort.Gallagher.lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β))) := by
  unfold LeanLab.PNTPort.LargeSieve.e
  fun_prop

/-- Abstract step: weights with total mass w 0 against integrals all at most B. -/
private lemma abel_bracket491 (w : ℕ → ℝ) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n)
    (I : ℕ → ℝ) (J B : ℝ) (hI : ∀ n, I n ≤ B) (hJ : J ≤ B) (M : ℕ) :
    (∑ n ∈ range M, (w n - w (n + 1)) * I n) + w M * J ≤ w 0 * B := by
  have h1 : ∑ n ∈ range M, (w n - w (n + 1)) * I n ≤
      ∑ n ∈ range M, (w n - w (n + 1)) * B :=
    sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (hI n) (sub_nonneg.mpr (hw (Nat.le_succ n)))
  have h2 : w M * J ≤ w M * B := mul_le_mul_of_nonneg_left hJ (hw0 M)
  have h3 : ∑ n ∈ range M, (w n - w (n + 1)) * B + w M * B = w 0 * B := by
    rw [← sum_mul, sum_range_sub']; ring
  linarith

/-- Not in P0093. Formalizer's replacement for the Lemma 2 step of page 160
equation 6.1 and for the unargued step to page 161 equation 6.3.
Under the Riemann hypothesis the damped series with coefficients von Mangoldt
minus one, weighted by one over ln n, has square integral over the arc of radius
one over 2 L at most the short interval mean square bound, uniformly in the
truncation. Inputs: PNTPort.Selberg.weighted_mean_b, the mean square without the
logarithmic weights, conditional on the Riemann hypothesis, and
PNTPort.Selberg.abel_cs_integral, partial summation with Cauchy-Schwarz. The
constant is the one of weighted_mean_b divided by the square of ln 2. -/
theorem lam_log_mean_square491 (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N L M : ℕ, 1 ≤ L → L ≤ N →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β)))‖ ^ 2 ≤
      C * (N * (Real.log (N / L) + 3) ^ 2 / L +
        N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 +
        L * (Real.log N + 1) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := LeanLab.PNTPort.Selberg.weighted_mean_b hRH
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / (Real.log 2) ^ 2, by positivity, fun N L M hL hLN => ?_⟩
  have hξ : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
  have habel := LeanLab.PNTPort.Selberg.abel_cs_integral
    (fun (n : ℕ) (β : ℝ) => (Real.exp (-(n / N)) : ℂ) *
      (LeanLab.PNTPort.Gallagher.lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β)))
    (term_continuous491 N) (fun n : ℕ => 1 / Real.log ((max n 2 : ℕ) : ℝ))
    logWeight_antitone491 logWeight_nonneg491 M hξ
  have hbr := abel_bracket491 (fun n : ℕ => 1 / Real.log ((max n 2 : ℕ) : ℝ))
    logWeight_antitone491 logWeight_nonneg491 _ _ _
    (fun n => hb N L (n + 1) hL hLN) (hb N L M hL hLN) M
  have hw0 : (0 : ℝ) ≤ 1 / Real.log ((max 0 2 : ℕ) : ℝ) := logWeight_nonneg491 0
  have hw0e : 1 / Real.log ((max 0 2 : ℕ) : ℝ) = 1 / Real.log 2 := by norm_num
  refine (habel.trans (mul_le_mul_of_nonneg_left hbr hw0)).trans (le_of_eq ?_)
  simp only [hw0e]
  field_simp
