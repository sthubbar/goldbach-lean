module

public import LeanLab.Linnik1951.Base491b

/-!
P0093 pages 160 and 161. Decay of the model series S one away from the origin,
the input of the extension of the arc integral to a full period in equation 6.2.
Steps: partial summation for a decreasing nonnegative weight against a unit
modulus geometric factor, the lower bound for the distance of the phase to one,
and the passage to the limit of the partial sums of the series of equation 6.3.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- Partial summation identity for a real weight against powers of w. -/
private theorem abel_identity_decay491 (c : ℕ → ℝ) (w : ℂ) (M : ℕ) :
    (1 - w) * ∑ m ∈ range (M + 1), (c m : ℂ) * w ^ m =
      (c 0 : ℂ) + ∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)
        - (c M : ℂ) * w ^ (M + 1) := by
  induction M with
  | zero => simp; ring
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ (n := M)]
    ring

/-- Partial summation bound: a decreasing nonnegative weight against a unit
modulus geometric factor has partial sums at most twice the first weight after
multiplication by one minus the ratio. -/
private theorem abel_bound_decay491 (c : ℕ → ℝ) (hc : Antitone c) (h0 : ∀ m, 0 ≤ c m)
    (w : ℂ) (hw : ‖w‖ = 1) (M : ℕ) :
    ‖(1 - w) * ∑ m ∈ range M, (c m : ℂ) * w ^ m‖ ≤ 2 * c 0 := by
  rcases M with _ | M
  · simp; exact h0 0
  rw [abel_identity_decay491]
  have h1 : ‖∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖ ≤ c 0 - c M := by
    calc ‖∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖
        ≤ ∑ m ∈ range M, ‖((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖ := norm_sum_le _ _
      _ = ∑ m ∈ range M, (c m - c (m + 1)) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [norm_mul, norm_pow, hw, one_pow, mul_one, ← Complex.ofReal_sub,
            Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr (hc (Nat.le_succ m)))]
      _ = c 0 - c M := Finset.sum_range_sub' c M
  have h2 : ‖(c M : ℂ) * w ^ (M + 1)‖ = c M := by
    rw [norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h0 M)]
  have h3 : ‖(c 0 : ℂ)‖ = c 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 0)]
  calc ‖(c 0 : ℂ) + ∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)
          - (c M : ℂ) * w ^ (M + 1)‖
      ≤ ‖(c 0 : ℂ)‖ + ‖∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖
          + ‖(c M : ℂ) * w ^ (M + 1)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ c 0 + (c 0 - c M) + c M := by rw [h2, h3]; linarith
    _ = 2 * c 0 := by ring

/-- The shifted weight exp of minus m plus two over N over ln of m plus two is
decreasing. -/
private theorem weight_antitone_decay491 (N : ℕ) :
    Antitone (fun m : ℕ => Real.exp (-((m + 2 : ℕ) : ℝ) / N) / Real.log ((m + 2 : ℕ) : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro m
  have hl : 0 < Real.log ((m + 2 : ℕ) : ℝ) := by
    apply Real.log_pos; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hll : Real.log ((m + 2 : ℕ) : ℝ) ≤ Real.log ((m + 1 + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · push_cast; linarith
  have he : Real.exp (-((m + 1 + 2 : ℕ) : ℝ) / N) ≤ Real.exp (-((m + 2 : ℕ) : ℝ) / N) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    push_cast; linarith
  exact div_le_div₀ (Real.exp_pos _).le he hl hll

/-- The distance of the phase to one is at least four times the distance of z
to the origin on the half period. -/
private theorem phase_distance_decay491 (z : ℝ) (hz : |z| ≤ 1 / 2) :
    4 * |z| ≤ ‖1 - Complex.exp ((-(2 * Real.pi * z) : ℝ) * Complex.I)‖ := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (-(2 * Real.pi * z))
  rw [mul_comm] at h
  rw [norm_sub_rev, h, Real.norm_eq_abs, abs_mul, abs_two,
    show -(2 * Real.pi * z) / 2 = -(Real.pi * z) by ring, Real.sin_neg, abs_neg]
  have hpi := Real.pi_pos
  have hs : 2 / Real.pi * (Real.pi * |z|) ≤ Real.sin (Real.pi * |z|) := by
    apply Real.mul_le_sin (by positivity)
    nlinarith
  have hs2 : 2 / Real.pi * (Real.pi * |z|) = 2 * |z| := by field_simp
  have hs3 : Real.sin (Real.pi * |z|) ≤ |Real.sin (Real.pi * z)| := by
    rcases abs_cases z with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact le_abs_self _
    · rw [h1, mul_neg, Real.sin_neg]; exact neg_le_abs _
  linarith

/-- P0093 page 160, the step from equation 6.1 to equation 6.2.
Off the arc the model series S one of equation 6.3 is at most one over the
distance to the origin. The print states the corresponding bound q tau for the
contour integrand; for S one it is partial summation with the decreasing
weights exp of minus m over N over ln m. -/
theorem logFourier_decay491 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) (hz0 : z ≠ 0)
    (hz : |z| ≤ 1 / 2) : ‖logFourier520 N z‖ ≤ 1 / |z| := by
  have hzpos : 0 < |z| := abs_pos.mpr hz0
  set w : ℂ := Complex.exp ((-(2 * Real.pi * z) : ℝ) * Complex.I) with hw
  have hwn : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hdist : 4 * |z| ≤ ‖1 - w‖ := phase_distance_decay491 z hz
  have hdpos : 0 < ‖1 - w‖ := by linarith
  set c : ℕ → ℝ :=
    fun m : ℕ => Real.exp (-((m + 2 : ℕ) : ℝ) / N) / Real.log ((m + 2 : ℕ) : ℝ) with hc
  have hcanti : Antitone c := weight_antitone_decay491 N
  have hc0 : ∀ m, 0 ≤ c m := by
    intro m
    apply div_nonneg (Real.exp_pos _).le
    apply Real.log_nonneg; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set f : ℕ → ℂ := fun m => logCoefficient520 N m *
    Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) with hf
  have hfs : Summable f := by
    apply Summable.of_norm
    have : (fun m => ‖f m‖) = fun m => ‖logCoefficient520 N m‖ := by
      funext m
      simp only [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [this]
    exact (logCoefficient_summable520 N hN).norm
  have hterm : ∀ m, f (m + 2) = w ^ 2 * ((c m : ℂ) * w ^ m) := by
    intro m
    have hexp : Complex.exp ((-(2 * Real.pi * z * ((m + 2 : ℕ) : ℝ)) : ℝ) * Complex.I)
        = w ^ (m + 2) := by
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast; ring
    simp only [hf, logCoefficient520, show 2 ≤ m + 2 by omega, ↓reduceIte]
    rw [hexp]
    simp only [hc]
    ring
  have hsplit : logFourier520 N z = ∑' m, f (m + 2) := by
    have h := hfs.sum_add_tsum_nat_add 2
    have h01 : ∑ i ∈ range 2, f i = 0 := by
      simp [Finset.sum_range_succ, hf, logCoefficient520]
    rw [h01, zero_add] at h
    exact h.symm
  have hgs : Summable (fun m => f (m + 2)) := (summable_nat_add_iff 2).mpr hfs
  have hB : ∀ n, ‖∑ m ∈ range n, f (m + 2)‖ ≤ 2 * c 0 / ‖1 - w‖ := by
    intro n
    have h := abel_bound_decay491 c hcanti hc0 w hwn n
    rw [norm_mul] at h
    have heq : ∑ m ∈ range n, f (m + 2) = w ^ 2 * ∑ m ∈ range n, (c m : ℂ) * w ^ m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => hterm m)
    rw [heq, norm_mul, norm_pow, hwn, one_pow, one_mul, le_div_iff₀ hdpos]
    linarith [mul_comm ‖1 - w‖ ‖∑ m ∈ range n, (c m : ℂ) * w ^ m‖]
  have hlim : ‖∑' m, f (m + 2)‖ ≤ 2 * c 0 / ‖1 - w‖ :=
    le_of_tendsto (hgs.hasSum.tendsto_sum_nat.norm) (Filter.Eventually.of_forall hB)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc0le : c 0 ≤ 2 := by
    simp only [hc]
    rw [div_le_iff₀ (by simpa using (by linarith : (0 : ℝ) < Real.log 2))]
    have he : Real.exp (-((0 + 2 : ℕ) : ℝ) / N) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg N)
      simp
    have : (1 : ℝ) ≤ 2 * Real.log ((0 + 2 : ℕ) : ℝ) := by
      simp only [zero_add, Nat.cast_ofNat]; linarith
    linarith
  rw [hsplit]
  refine hlim.trans ?_
  rw [div_le_div_iff₀ hdpos hzpos]
  nlinarith [hc0 0]
