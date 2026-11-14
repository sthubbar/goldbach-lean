module

public import LeanLab.Linnik.LiLiuDisplay37
public import LeanLab.PNTPort.StrongPNT.Bridge

/-!
Li-Liu, arXiv 2610.15784 v1, Section 4, proof of Lemma 4.3, display (37):
  (1/N) ∫_{-T/N}^{T/N} |S(β)|² dβ = ∫_{-T}^{T} |∫_0^1 e(ut) dt|² du + o_T(1),
S(α) = ∑_{N₁ < p ≤ N} (log p) e(pα), N₁ = N^{1-κ}. The paper: "by the prime number theorem and
partial summation, uniformly for |u| ≤ T, S(u/N)/N = ∫_0^1 e(ut) dt + o_T(1)", then integrate.
Display stated as `Display37 κ` in LiLiuDisplay37.lean, unit U-1379.

This file proves `Display37 κ` for every κ > 0 from the lab's strong PNT
`LeanLab.PNTPort.psi_explicit_strong`, StrongPNT/Bridge.lean:
* `theta_pnt`: |θ(n) - n| ≤ ε n + C_ε, from psi_explicit_strong and Mathlib's ψ - θ ≤ 2√x log x;
* `abel_bound`: discrete partial summation with D(n) = θ(n) - n;
* `riemann`: the Riemann sum (1/N) ∑_{n ≤ N} e(un/N) is within 2π|u|/N of ∫_0^1 e(ut) dt;
* `key_bound`, `uniform_conv`: S(u/N)/N → ∫_0^1 e(ut) dt uniformly for |u| ≤ T;
* `display37`: Display37 κ for κ > 0; `lemma43_lower`: the lower half of (36) at level I(T) - ε.

Unit U-1389, PC run 20261021T0703Z-4724. AI-written Lean code, Claude. KNOWN mathematics: the
paper's own step, prime number theorem plus partial summation. Nothing here is progress on
Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.LiLiuDisplay37PNT

open MeasureTheory Set Real Finset Filter Asymptotics
open LeanLab.Linnik.LiLiuLemma43 LeanLab.Linnik.LiLiuDisplay37
open LeanLab.PNTPort.LargeSieve

/-- The lab additive character `e(x) = exp(2πix)`, named to avoid the StrongPNT port root `e`. -/
local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-! ## The prime number theorem for θ -/

theorem theta_pnt : ∀ ε > 0, ∃ C : ℝ, ∀ n : ℕ, |Chebyshev.theta n - n| ≤ ε * n + C := by
  intro ε hε
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  -- K exp(-c √log x) → 0
  have h1 : Tendsto (fun x : ℝ => K * Real.exp (-(c * Real.sqrt (Real.log x)))) atTop (nhds 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc)).const_mul K
    simpa using this
  have ev1 : ∀ᶠ x : ℝ in atTop, K * Real.exp (-(c * Real.sqrt (Real.log x))) ≤ ε / 2 :=
    (h1.eventually (ge_mem_nhds (by linarith : (0:ℝ) < ε / 2)))
  have ev2 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ ε / 4 * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).bound (by linarith)
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ev1.and (ev2.and (eventually_ge_atTop (2 : ℝ))))
  have hbig : ∀ x : ℝ, X ≤ x → |Chebyshev.theta x - x| ≤ ε * x := by
    intro x hx
    obtain ⟨hA, hB, h2⟩ := hX x hx
    have hx0 : 0 < x := by linarith
    have hpsi := hK x h2
    have hpt := Chebyshev.psi_sub_theta_le (by linarith : (1:ℝ) ≤ x)
    have htp := Chebyshev.theta_le_psi x
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at hB
    have hs : 2 * √x * Real.log x ≤ ε / 2 * x := by
      have : √x * √x = x := Real.mul_self_sqrt hx0.le
      nlinarith [Real.sqrt_nonneg x]
    have hK' : K * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ ε / 2 * x := by
      rw [show K * x * Real.exp (-c * Real.sqrt (Real.log x)) =
        (K * Real.exp (-(c * Real.sqrt (Real.log x)))) * x by rw [neg_mul]; ring]
      exact mul_le_mul_of_nonneg_right hA hx0.le
    rw [abs_le] at hpsi ⊢
    constructor <;> nlinarith
  refine ⟨(Real.log 4 + 1) * X, fun n => ?_⟩
  rcases le_total X n with h | h
  · have := hbig n h
    have : 0 ≤ (Real.log 4 + 1) * X := by
      have : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hX2 := (hX X le_rfl).2.2
      positivity
    linarith
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ht0 := Chebyshev.theta_nonneg (n : ℝ)
    have ht := Chebyshev.theta_le_log4_mul_x hn0
    have hl : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h hl]


/-! ## Elementary lemmas: Lipschitz bound for e, Abel summation, Riemann sum -/

lemma e_lip (x y : ℝ) : ‖eL x - eL y‖ ≤ 2 * π * |x - y| := by
  have h1 : eL x - eL y = eL y * (eL (x - y) - 1) := by
    rw [mul_sub, ← e_add]; ring_nf
  rw [h1, norm_mul, norm_e, one_mul]
  have h2 : eL (x - y) = Complex.exp (Complex.I * ((2 * π * (x - y) : ℝ) : ℂ)) := rfl
  rw [h2]
  refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]

lemma continuous_e : Continuous eL := by
  unfold LeanLab.PNTPort.LargeSieve.e; fun_prop

/-- Abel summation identity, indexed from `range`. -/
lemma abel_identity (D : ℕ → ℝ) (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, ((D (n + 1) - D n : ℝ) : ℂ) * f (n + 1) =
      (D N : ℂ) * f N - (D 0 : ℂ) * f 0 - ∑ n ∈ range N, (D n : ℂ) * (f (n + 1) - f n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]; push_cast; ring

lemma abel_bound (D : ℕ → ℝ) (hD0 : D 0 = 0) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {L : ℝ}
    (hL : ∀ n, ‖f (n + 1) - f n‖ ≤ L) (N : ℕ) :
    ‖∑ n ∈ range N, ((D (n + 1) - D n : ℝ) : ℂ) * f (n + 1)‖ ≤
      |D N| + L * ∑ n ∈ range N, |D n| := by
  rw [abel_identity, hD0]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (mul_le_mul_of_nonneg_left (hf N) (abs_nonneg _)) (by simp)
  · refine le_trans (norm_sum_le _ _) ?_
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm L]
    exact mul_le_mul_of_nonneg_left (hL n) (abs_nonneg _)

/-- `F(u) = ∫_0^1 e(ut) dt`. -/
noncomputable def F (u : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, eL (u * t)

lemma norm_F_le (u : ℝ) : ‖F u‖ ≤ 1 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => eL (u * t)) (C := 1) (fun t _ => le_of_eq (norm_e _))
  simpa [F] using this

lemma continuous_F : Continuous F := by
  unfold F
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_e.comp (by fun_prop)

/-- Riemann sum: `‖(1/N) ∑_{n<N} e(u(n+1)/N) - F(u)‖ ≤ 2π|u|/N`. -/
lemma riemann (u : ℝ) {N : ℕ} (hN : 0 < N) :
    ‖(1 / (N : ℂ)) * ∑ n ∈ range N, eL (u * ((n + 1 : ℕ) / N)) - F u‖ ≤ 2 * π * |u| / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : Continuous fun t => eL (u * t) := continuous_e.comp (by fun_prop)
  have hsplit : F u = ∑ n ∈ range N, ∫ t in ((n : ℕ) / (N : ℝ))..(((n + 1 : ℕ)) / N), eL (u * t) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / N)
      (fun k _ => hc.intervalIntegrable _ _)]
    simp [F, hNr.ne']
  have hterm : ∀ n : ℕ, (1 / (N : ℂ)) * eL (u * ((n + 1 : ℕ) / N)) =
      ∫ t in ((n : ℕ) / (N : ℝ))..(((n + 1 : ℕ)) / N), eL (u * ((n + 1 : ℕ) / N)) := by
    intro n
    rw [intervalIntegral.integral_const]
    have : ((((n + 1 : ℕ)) / (N : ℝ)) - (n : ℕ) / N) = 1 / N := by
      push_cast; field_simp; ring
    rw [this, Complex.real_smul]; push_cast; ring
  rw [hsplit, mul_sum, ← sum_sub_distrib]
  have hb : ∀ n ∈ range N, ‖(1 / (N : ℂ)) * eL (u * ((n + 1 : ℕ) / N)) -
      ∫ t in ((n : ℕ) / (N : ℝ))..(((n + 1 : ℕ)) / N), eL (u * t)‖ ≤ 2 * π * |u| / N * (1 / N) := by
    intro n _
    rw [hterm, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hc.intervalIntegrable _ _)]
    have hlen : |(((n + 1 : ℕ)) / (N : ℝ)) - (n : ℕ) / N| = 1 / N := by
      rw [show (((n + 1 : ℕ)) / (N : ℝ)) - (n : ℕ) / N = 1 / N by push_cast; field_simp; ring]
      exact abs_of_pos (by positivity)
    rw [← hlen]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have hn0 : (n : ℝ) / N ≤ ((n + 1 : ℕ)) / N := by
      apply div_le_div_of_nonneg_right _ hNr.le; push_cast; linarith
    rw [Set.uIoc_of_le hn0] at ht
    refine le_trans (e_lip _ _) ?_
    have : |u * (((n + 1 : ℕ)) / N) - u * t| ≤ |u| * (1 / N) := by
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_of_nonneg (by linarith [ht.2])]
      have := ht.1
      have h2 : (((n + 1 : ℕ)) / (N : ℝ)) - (n : ℕ) / N = 1 / N := by
        push_cast; field_simp; ring
      linarith
    calc 2 * π * |u * (((n + 1 : ℕ)) / N) - u * t| ≤ 2 * π * (|u| * (1 / N)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * π * |u| / N := by ring
  refine le_trans (norm_sum_le _ _) (le_trans (sum_le_sum hb) (le_of_eq ?_))
  rw [sum_const, card_range, nsmul_eq_mul]; field_simp


/-! ## Splitting `S` into the full prime sum up to `N` minus the primes up to `N₁` -/

/-- The prime indicator weighted by `log`. -/
noncomputable def cw (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

lemma sum_Ioc_zero_eq_range {R : Type*} [AddCommMonoid R] (g : ℕ → R) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, g k = ∑ k ∈ range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, sum_range_succ]

lemma theta_eq_range (n : ℕ) : Chebyshev.theta n = ∑ k ∈ range n, cw (k + 1) := by
  have h := sum_primesIn (Nat.zero_le n)
  rw [Nat.cast_zero, Chebyshev.theta_zero, sub_zero] at h
  rw [← h, primesIn, Finset.sum_filter, sum_Ioc_zero_eq_range]
  rfl

/-- `D(n) = θ(n) - n`. -/
noncomputable def D (n : ℕ) : ℝ := Chebyshev.theta n - n

lemma D_zero : D 0 = 0 := by simp [D, Chebyshev.theta_zero]

lemma cw_eq (n : ℕ) : cw (n + 1) = D (n + 1) - D n + 1 := by
  simp only [D, theta_eq_range, sum_range_succ]; push_cast; ring

lemma SA_split {M N : ℕ} (hMN : M ≤ N) (β : ℝ) :
    SA (primesIn M N) logw β =
      ∑ n ∈ range N, (cw (n + 1) : ℂ) * eL (((n + 1 : ℕ) : ℝ) * β) -
        SA (primesIn 0 M) logw β := by
  have hg : ∀ k : ℕ, (if k.Prime then logw k * eL (k * β) else 0) = (cw k : ℂ) * eL (k * β) := by
    intro k; unfold cw logw; split_ifs <;> simp
  unfold SA
  rw [primesIn, primesIn, Finset.sum_filter, Finset.sum_filter, eq_sub_iff_add_eq, add_comm,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN, Finset.sum_congr rfl (fun k _ => hg k),
    sum_Ioc_zero_eq_range]

lemma norm_SA_le_theta (M : ℕ) (β : ℝ) : ‖SA (primesIn 0 M) logw β‖ ≤ Chebyshev.theta M := by
  have h := sum_primesIn (Nat.zero_le M)
  rw [Nat.cast_zero, Chebyshev.theta_zero, sub_zero] at h
  rw [← h]
  refine le_trans (norm_sum_le _ _) (le_of_eq (sum_congr rfl fun p _ => ?_))
  rw [norm_mul, norm_e, mul_one, logw, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg p)]

lemma continuous_SA (A : Finset ℕ) (w : ℕ → ℂ) : Continuous (SA A w) := by
  unfold SA
  exact continuous_finsetSum _ fun p _ =>
    continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))

/-! ## The pointwise estimate, uniform in `|u| ≤ T` -/

/-- **Partial summation estimate.** For `|u| ≤ T`, `M ≤ N`:
`‖S(u/N)/N - F(u)‖ ≤ θ(M)/N + (|D(N)| + (2πT/N) ∑_{n<N} |D(n)|)/N + 2πT/N`. -/
theorem key_bound {M N : ℕ} (hN : 0 < N) (hMN : M ≤ N) {T u : ℝ} (hu : |u| ≤ T) :
    ‖(1 / (N : ℂ)) * SA (primesIn M N) logw (u / N) - F u‖ ≤
      Chebyshev.theta M / N + (|D N| + 2 * π * T / N * ∑ n ∈ range N, |D n|) / N +
        2 * π * T / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set f : ℕ → ℂ := fun k => eL (u * ((k : ℝ) / N)) with hf
  set R := SA (primesIn 0 M) logw (u / N)
  have hS : SA (primesIn M N) logw (u / N) =
      ∑ n ∈ range N, ((D (n + 1) - D n : ℝ) : ℂ) * f (n + 1) +
        ∑ n ∈ range N, f (n + 1) - R := by
    rw [SA_split hMN, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    rw [cw_eq, hf]
    simp only
    rw [show (((n + 1 : ℕ) : ℝ)) * (u / N) = u * (((n + 1 : ℕ) : ℝ) / N) by ring]
    push_cast; ring
  have hL : ∀ n, ‖f (n + 1) - f n‖ ≤ 2 * π * T / N := by
    intro n
    refine le_trans (e_lip _ _) ?_
    have : u * (((n + 1 : ℕ) : ℝ) / N) - u * ((n : ℝ) / N) = u / N := by
      push_cast; field_simp; ring
    rw [this, abs_div, abs_of_pos hNr]
    have : 2 * π * (|u| / N) = 2 * π * |u| / N := by ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hNr.le
    have := Real.pi_pos
    nlinarith
  have hab := abel_bound D D_zero f (fun n => le_of_eq (norm_e _)) hL N
  have hri := riemann u hN
  have hR := norm_SA_le_theta M (u / N)
  have hsplit : (1 / (N : ℂ)) * SA (primesIn M N) logw (u / N) - F u =
      (1 / (N : ℂ)) * ∑ n ∈ range N, ((D (n + 1) - D n : ℝ) : ℂ) * f (n + 1) +
        ((1 / (N : ℂ)) * ∑ n ∈ range N, eL (u * ((n + 1 : ℕ) / N)) - F u) -
          (1 / (N : ℂ)) * R := by
    rw [hS]; ring
  have hnN : ‖(1 / (N : ℂ))‖ = 1 / N := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_mul, norm_mul, hnN]
  have h2 : 2 * π * |u| / N ≤ 2 * π * T / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    have := Real.pi_pos
    nlinarith
  have e1 : 1 / (N : ℝ) * ‖∑ n ∈ range N, ((D (n + 1) - D n : ℝ) : ℂ) * f (n + 1)‖ ≤
      (|D N| + 2 * π * T / N * ∑ n ∈ range N, |D n|) / N := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hab hNr.le
  have e3 : 1 / (N : ℝ) * ‖R‖ ≤ Chebyshev.theta M / N := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hR hNr.le
  linarith

/-- **Uniform convergence.** For `κ > 0`, `T ≥ 0`, uniformly for `|u| ≤ T`,
`S(u/N)/N → ∫_0^1 e(ut) dt` as `N → ∞`, with `S` over the primes in `(N^{1-κ}, N]`. -/
theorem uniform_conv {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) :
    ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ u : ℝ, |u| ≤ T →
      ‖(1 / (N : ℂ)) * SA (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw (u / N) - F u‖ ≤ ε := by
  intro ε hε
  have hπ := Real.pi_pos
  have hP : 0 < 1 + 2 * π * T := by positivity
  set ε' := ε / (4 * (1 + 2 * π * T)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨C, hC⟩ := theta_pnt ε' hε'0
  have hC0 : 0 ≤ C := by have := hC 0; simp at this; linarith
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have t1 : Filter.Tendsto (fun N : ℕ => Real.log 4 * (N : ℝ) ^ (-κ)) Filter.atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop).const_mul (Real.log 4)
    simpa using this
  have t2 := tendsto_const_div_atTop_nhds_zero_nat (C + 2 * π * T * C + 2 * π * T)
  filter_upwards [t1.eventually (ge_mem_nhds (by linarith : (0:ℝ) < ε / 4)),
    t2.eventually (ge_mem_nhds (by linarith : (0:ℝ) < ε / 4)),
    Filter.eventually_gt_atTop 0] with N h1 h2 hN u hu
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set M := ⌊(N : ℝ) ^ (1 - κ)⌋₊ with hM
  have hpow : (N : ℝ) ^ (1 - κ) = N * (N : ℝ) ^ (-κ) := by
    rw [show (1 - κ) = 1 + -κ by ring, Real.rpow_add hNr, Real.rpow_one]
  have hMN : M ≤ N := by
    apply Nat.floor_le_of_le
    have := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 1 - κ ≤ 1)
    rwa [Real.rpow_one] at this
  refine le_trans (key_bound hN hMN hu) ?_
  -- θ(M)/N ≤ log 4 · N^{-κ}
  have hth : Chebyshev.theta M / N ≤ Real.log 4 * (N : ℝ) ^ (-κ) := by
    rw [div_le_iff₀ hNr]
    have hM0 : (M : ℝ) ≤ (N : ℝ) ^ (1 - κ) := Nat.floor_le (by positivity)
    have := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M)
    calc Chebyshev.theta M ≤ Real.log 4 * M := this
      _ ≤ Real.log 4 * (N : ℝ) ^ (1 - κ) := mul_le_mul_of_nonneg_left hM0 hl4
      _ = _ := by rw [hpow]; ring
  have hDN : |D N| ≤ ε' * N + C := hC N
  have hsum : ∑ n ∈ range N, |D n| ≤ N * (ε' * N + C) := by
    calc ∑ n ∈ range N, |D n| ≤ ∑ n ∈ range N, (ε' * N + C) := by
          apply sum_le_sum; intro n hn
          have : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
          exact le_trans (hC n) (by nlinarith)
      _ = N * (ε' * N + C) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hmid : (|D N| + 2 * π * T / N * ∑ n ∈ range N, |D n|) / N ≤
      (1 + 2 * π * T) * ε' + (C + 2 * π * T * C) / N := by
    rw [div_le_iff₀ hNr]
    have hA : 2 * π * T / N * ∑ n ∈ range N, |D n| ≤ 2 * π * T * (ε' * N + C) := by
      calc 2 * π * T / N * ∑ n ∈ range N, |D n| ≤ 2 * π * T / N * (N * (ε' * N + C)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by field_simp
    have : ((1 + 2 * π * T) * ε' + (C + 2 * π * T * C) / N) * N =
        (1 + 2 * π * T) * ε' * N + (C + 2 * π * T * C) := by field_simp
    rw [this]; nlinarith
  have hε'e : (1 + 2 * π * T) * ε' = ε / 4 := by rw [hε']; field_simp
  have hlast : (C + 2 * π * T * C) / N + 2 * π * T / N =
      (C + 2 * π * T * C + 2 * π * T) / N := by ring
  linarith

/-! ## Display (37) -/

lemma cov (h : ℝ → ℝ) {N : ℝ} (hN : 0 < N) (T : ℝ) :
    (1 / N) * ∫ β in (-(T / N))..(T / N), h β = ∫ u in (-T)..T, h (u / N) / N ^ 2 := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div h hN.ne', smul_eq_mul,
    neg_div]
  field_simp

/-- **Display (37) of Li-Liu, PROVED from the lab's strong PNT.** For every `κ > 0` and every
`T ≥ 1`, `(1/N) ∫_{-T/N}^{T/N} |S(β)|² dβ → ∫_{-T}^{T} |∫_0^1 e(ut) dt|² du` as `N → ∞`,
`S` over the primes in `(⌊N^{1-κ}⌋, N]` with log weights. -/
theorem display37 {κ : ℝ} (hκ : 0 < κ) : Display37 κ := by
  intro T hT
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hT0 : 0 < T := by linarith
  set δ := min 1 (ε / (8 * T)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (8 * T) := min_le_right _ _
  filter_upwards [uniform_conv hκ hT0.le δ hδ0, Filter.eventually_gt_atTop 0] with N hU hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set A := primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N
  set a : ℝ → ℂ := fun u => (1 / (N : ℂ)) * SA A logw (u / N) with ha
  have hnN : ‖(1 / (N : ℂ))‖ = 1 / N := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [cov (fun β => ‖SA A logw β‖ ^ 2) hNr T]
  have hcongr : ∫ u in (-T)..T, ‖SA A logw (u / N)‖ ^ 2 / (N : ℝ) ^ 2 =
      ∫ u in (-T)..T, ‖a u‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [ha, norm_mul, hnN]
    field_simp
  rw [hcongr, Real.dist_eq, I]
  have hca : Continuous fun u => ‖a u‖ ^ 2 := by
    simp only [ha]
    exact ((continuous_const.mul ((continuous_SA A logw).comp
      (continuous_id.div_const _))).norm).pow 2
  have hcF : Continuous fun u => ‖F u‖ ^ 2 := (continuous_F.norm).pow 2
  have hFdef : (fun u => ‖∫ t in (0 : ℝ)..1, eL (u * t)‖ ^ 2) = fun u => ‖F u‖ ^ 2 := rfl
  rw [hFdef, ← intervalIntegral.integral_sub (hca.intervalIntegrable _ _)
    (hcF.intervalIntegrable _ _), ← Real.norm_eq_abs]
  have hb : ∀ u ∈ Set.uIoc (-T) T, ‖‖a u‖ ^ 2 - ‖F u‖ ^ 2‖ ≤ δ * (2 + δ) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    have hu' : |u| ≤ T := abs_le.mpr ⟨hu.1.le, hu.2⟩
    have h1 := hU u hu'
    have h2 := abs_norm_sub_norm_le (a u) (F u)
    have h3 := norm_F_le u
    have h4 := norm_nonneg (a u)
    have h5 := norm_nonneg (F u)
    rw [Real.norm_eq_abs, abs_le]
    rw [abs_le] at h2
    constructor <;> nlinarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith : (0:ℝ) < 2 * T)] at this
  have hfin : δ * (2 + δ) * (2 * T) ≤ 6 * T * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (le_of_lt (mul_pos hδ0 hT0))]
  have hfin2 : 6 * T * δ ≤ 6 * T * (ε / (8 * T)) := mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have hfin3 : 6 * T * (ε / (8 * T)) < ε := by
    rw [show 6 * T * (ε / (8 * T)) = 3 / 4 * ε by field_simp; ring]; linarith
  linarith

/-- The hypothesis `0 < κ` of `display37` can hold: the paper's κ is any small positive constant,
and `Display37 (1/2)` follows. -/
theorem vacuity_display37 : Display37 (1 / 2) := display37 (by norm_num)

/-- Lemma 4.3 lower half at level `I(T) - ε`, now unconditional: `lemma43_lower_of_display37`
with `display37`. -/
theorem lemma43_lower {κ : ℝ} (hκ : 0 < κ) {T ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (Q : ℕ) (P : ℝ), 1 ≤ Q →
      Q ≤ ⌊(N : ℝ) ^ (1 - κ)⌋₊ → (Q : ℝ) ≤ P → (Q : ℝ) * T ≤ P → 2 * P ^ 2 < T * N →
      (I T - ε) * N * Real.log ((Q : ℝ) + 1) ≤
        LeanLab.Linnik.LiLiuLemma43Int.R10 (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw P N :=
  lemma43_lower_of_display37 (display37 hκ) hT hε

end LeanLab.Linnik.LiLiuDisplay37PNT
