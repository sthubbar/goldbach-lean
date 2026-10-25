module

public import LeanLab.DensityGoldbach.U1502Core
public import LeanLab.DensityGoldbach.U1494Spec
public import LeanLab.PNTSieve.MertensUpper
public import LeanLab.PNTPort.BV.Helpers

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

Before: `U1494.alsetriShao_1_2_U1494_mid : GreenLargeSpecMid → AlsetriShao12`, and
`GreenLargeSpecMid` is equivalent to the full large spectrum bound `GreenLargeSpec` (U-1500), a
restriction type estimate for every `0 ≤ f ≤ ν_b`.

Now: the restriction estimate is PROVED from a pointwise statement about the Fourier
coefficients of the majorant `ν_b` alone, with no `f` in it:

* `NuMajorant`: for some absolute `C`, all large `z`, reduced `b`, large primes `N`, every
  `1 ≤ T ≤ (log N)^4` and every `s ≠ 0`,
    `|ν̂_b(s)| ≤ (log N)^{-2} + C T^{-1/2} + C Σ_{q ≤ T sqfree} Σ_{(a,q)=1} φ(q)⁻¹ ψ_N(s/N - a/q)`,
  `ψ_N(θ) = min(1, 1/(N‖θ‖))`. This is the standard major and minor arc description of the
  exponential sum over primes in the class `b mod W`: on the arc at `a/q` the main term is
  `μ(q)/φ(q)` times a geometric sum, zero unless `q` is squarefree and prime to `W`; the arcs with
  `q > T` contribute at most `1/φ(q) ≤ q^{-1/2}`; the minor arcs and the Siegel-Walfisz errors are
  below `(log N)^{-2}`.

Results:
* `tt_pairs`: the TT* inequality `(|S| δ)² ≤ A Σ_{r, r' ∈ S} |ν̂(r - r')|`.
* `MT_le_sqrt`: `M_T ≤ C₂ √T` for `T ≥ 3`, from Mertens and `Σ 1/φ ≪ log`.
* `mid_of_majorant : NuMajorant → GreenLargeSpecMid`, at the exponent `q = 3`.
* `alsetriShao_1_2_U1502 : NuMajorant → AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-23. Checked only by the Lean kernel. Binary Goldbach is
OPEN.
-/

@[expose] public section

open Finset Real Filter
open scoped Classical ComplexConjugate

noncomputable section
namespace LeanLab.DensityGoldbach.U1502
open LeanLab.DensityGoldbach.U1446

variable {N : ℕ} [NeZero N]

/-- **TT* in pair form**: `(|S| δ)² ≤ A Σ_{r, r' ∈ S} |ν̂(r - r')|` for `0 ≤ f ≤ ν`, `E ν ≤ A` and
`|f̂| ≥ δ` on `S`. Steps 1 to 3 are those of `U1494.tt_star`. -/
theorem tt_pairs (f ν : ZMod N → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ ν n) (A : ℝ)
    (hA : avg N ν ≤ A) (δ : ℝ) (hδ : 0 < δ) (S : Finset (ZMod N))
    (hS : ∀ r ∈ S, δ ≤ ‖hatE N f r‖) :
    ((S.card : ℝ) * δ) ^ 2 ≤ A * ∑ r ∈ S, ∑ r' ∈ S, ‖hatE N ν (r - r')‖ := by
  have hν0 : ∀ n, 0 ≤ ν n := fun n => (hf n).1.trans (hf n).2
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have havg0 : 0 ≤ avg N ν := by
    unfold avg
    exact mul_nonneg (by positivity) (sum_nonneg fun n _ => hν0 n)
  have hA0 : 0 ≤ A := havg0.trans hA
  set u : ZMod N → ℂ := fun r => conj (hatE N f r) / (‖hatE N f r‖ : ℂ) with hu
  have hu1 : ∀ r, ‖u r‖ ≤ 1 := by
    intro r
    simp only [u, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have huf : ∀ r ∈ S, u r * hatE N f r = (‖hatE N f r‖ : ℂ) := by
    intro r hr
    have hne : (‖hatE N f r‖ : ℂ) ≠ 0 := by
      exact_mod_cast (hδ.trans_le (hS r hr)).ne'
    simp only [u]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj', div_eq_iff hne]
    push_cast; ring
  set g : ZMod N → ℂ := fun n => ∑ r ∈ S, u r * ZMod.stdAddChar (-(r * n)) with hg
  have h1 : ((∑ r ∈ S, ‖hatE N f r‖ : ℝ) : ℂ) =
      (1 / (N : ℂ)) * ∑ n : ZMod N, (f n : ℂ) * g n := by
    push_cast
    rw [← sum_congr rfl huf]
    simp only [g, hatE, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => sum_congr rfl fun n _ => ?_
    ring
  have h2 : ∑ r ∈ S, ‖hatE N f r‖ ≤ (1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖ := by
    have e := congrArg norm h1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg fun r _ => norm_nonneg _)] at e
    rw [e, norm_mul]
    have hN' : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by rw [norm_div, norm_one]; simp
    rw [hN']
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n).1]
    exact mul_le_mul_of_nonneg_right (hf n).2 (norm_nonneg _)
  have h3 : (∑ n : ZMod N, ν n * ‖g n‖) ^ 2 ≤
      (∑ n : ZMod N, ν n) * ∑ n : ZMod N, ν n * ‖g n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun n => Real.sqrt (ν n))
      (fun n => Real.sqrt (ν n) * ‖g n‖)
    have ea : ∀ n, Real.sqrt (ν n) * (Real.sqrt (ν n) * ‖g n‖) = ν n * ‖g n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (hν0 n)]
    have eb : ∀ n, Real.sqrt (ν n) ^ 2 = ν n := fun n => Real.sq_sqrt (hν0 n)
    have ec : ∀ n, (Real.sqrt (ν n) * ‖g n‖) ^ 2 = ν n * ‖g n‖ ^ 2 := fun n => by
      rw [mul_pow, eb]
    simp only [ea, eb, ec] at this
    exact this
  set Q := (1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg (by positivity)
    (sum_nonneg fun n _ => mul_nonneg (hν0 n) (by positivity))
  have h4 : Q ≤ ∑ r ∈ S, ∑ r' ∈ S, ‖hatE N ν (r - r')‖ := by
    have e := LeanLab.DensityGoldbach.U1494.weighted_sq_expand ν S u
    have hQn : Q = ‖((Q : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0]
    rw [hQn]
    change ‖(((1 / (N : ℝ)) * ∑ n : ZMod N, ν n *
      ‖∑ r ∈ S, u r * ZMod.stdAddChar (-(r * n))‖ ^ 2 : ℝ) : ℂ)‖ ≤ _
    rw [e]
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ =>
      (norm_sum_le _ _).trans (sum_le_sum fun r' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc ‖u r‖ * ‖u r'‖ * ‖hatE N ν (r - r')‖ ≤ 1 * 1 * ‖hatE N ν (r - r')‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul (hu1 r) (hu1 r') (norm_nonneg _) zero_le_one
      _ = ‖hatE N ν (r - r')‖ := by ring
  have hSδ : (S.card : ℝ) * δ ≤ ∑ r ∈ S, ‖hatE N f r‖ := by
    have := sum_le_sum hS
    rwa [sum_const, nsmul_eq_mul] at this
  have hP : 0 ≤ (S.card : ℝ) * δ := by positivity
  have hstep : ((S.card : ℝ) * δ) ^ 2 ≤ ((1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖) ^ 2 :=
    pow_le_pow_left₀ hP (hSδ.trans h2) 2
  have hav : (1 / (N : ℝ)) * ∑ n : ZMod N, ν n = avg N ν := rfl
  calc ((S.card : ℝ) * δ) ^ 2 ≤ ((1 / (N : ℝ)) * ∑ n : ZMod N, ν n * ‖g n‖) ^ 2 := hstep
    _ = (1 / (N : ℝ)) ^ 2 * (∑ n : ZMod N, ν n * ‖g n‖) ^ 2 := by ring
    _ ≤ (1 / (N : ℝ)) ^ 2 * ((∑ n : ZMod N, ν n) * ∑ n : ZMod N, ν n * ‖g n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = avg N ν * Q := by rw [← hav, hQ]; ring
    _ ≤ A * ∑ r ∈ S, ∑ r' ∈ S, ‖hatE N ν (r - r')‖ :=
        mul_le_mul hA h4 hQ0 hA0

/-! ### `M_T ≪ √T` -/

theorem MT_le_sqrt : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ T : ℕ, 3 ≤ T → MT T ≤ C₂ * Real.sqrt T := by
  obtain ⟨C, hC, hS⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  set ε : ℝ := 1 / 13136 with hε
  have hε0 : 0 < ε := by norm_num [hε]
  refine ⟨(2 * C * Real.exp 1) ^ 8 * Real.exp (6560 * 12) * (1 / ε) ^ 6568, by positivity,
    fun T hT => ?_⟩
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog0 : 0 < Real.log T := by linarith
  -- `S(T) ≤ 2 C log T`
  have hST : ST T ≤ 2 * C * Real.log T := by
    have := hS T
    unfold ST
    nlinarith
  have hST0 := ST_nonneg T
  -- Mertens
  have hM : ∑ p ∈ PT T, (1 : ℝ) / p ≤ Real.log (Real.log T) + 12 := by
    have := LeanLab.PNTSieve.Mertens.sum_inv_primes_le T (by omega)
    unfold PT; exact this
  have hexp : Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p) ≤
      Real.exp (6560 * 12) * Real.log T ^ 6560 := by
    have h1 : Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p) ≤
        Real.exp (6560 * (Real.log (Real.log T) + 12)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (6560 * (Real.log (Real.log T) + 12)) =
        Real.exp (6560 * 12) * Real.log T ^ 6560 := by
      rw [show 6560 * (Real.log (Real.log T) + 12) = 6560 * 12 + 6560 * Real.log (Real.log T) by
        ring, Real.exp_add]
      congr 1
      rw [← Real.log_rpow hlog0, Real.exp_log (by positivity)]
      norm_cast
    exact le_of_le_of_eq h1 h2
  -- `log T ≤ T^ε / ε`, so `(log T)^6568 ≤ ε^{-6568} √T`
  have hlogε : Real.log T ≤ (T : ℝ) ^ ε / ε := Real.log_le_rpow_div hT0.le hε0
  have hpow : Real.log T ^ 6568 ≤ (1 / ε) ^ 6568 * Real.sqrt T := by
    have h1 : Real.log T ^ 6568 ≤ ((T : ℝ) ^ ε / ε) ^ 6568 :=
      pow_le_pow_left₀ hlog0.le hlogε 6568
    have h2 : ((T : ℝ) ^ ε / ε) ^ 6568 = (1 / ε) ^ 6568 * Real.sqrt T := by
      rw [div_pow, ← Real.rpow_natCast ((T : ℝ) ^ ε), ← Real.rpow_mul hT0.le,
        Real.sqrt_eq_rpow]
      rw [show ε * ((6568 : ℕ) : ℝ) = 1 / 2 by rw [hε]; norm_num]
      field_simp
    linarith
  unfold MT
  have hST8 : (ST T * Real.exp 1) ^ 8 ≤ (2 * C * Real.exp 1) ^ 8 * Real.log T ^ 8 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have := mul_le_mul_of_nonneg_right hST (Real.exp_pos 1).le
    nlinarith [Real.exp_pos 1]
  calc (ST T * Real.exp 1) ^ 8 * Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p)
      ≤ ((2 * C * Real.exp 1) ^ 8 * Real.log T ^ 8) * (Real.exp (6560 * 12) * Real.log T ^ 6560) :=
        mul_le_mul hST8 hexp (by positivity) (by positivity)
    _ = (2 * C * Real.exp 1) ^ 8 * Real.exp (6560 * 12) * Real.log T ^ 6568 := by ring
    _ ≤ (2 * C * Real.exp 1) ^ 8 * Real.exp (6560 * 12) * ((1 / ε) ^ 6568 * Real.sqrt T) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-! ### The cited input -/

/-- **The major arc majorant for `ν_b`**, the new cited input: an absolute `C` such that for
large `z`, reduced `b`, large primes `N`, every `1 ≤ T ≤ (log N)^4` and every `s ≠ 0`,
`|ν̂_b(s)| ≤ (log N)^{-2} + C/√T + C Φ_T(s)`, `Φ_T` the major arc profile `PhiT`. -/
def NuMajorant : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z → ∀ b : ℕ, b < primorial z →
    Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ T : ℕ, 1 ≤ T → (T : ℝ) ≤ Real.log N ^ 4 → ∀ s : ZMod N, s ≠ 0 →
        ‖hatE N (nuW (primorial z) b N) s‖ ≤
          1 / Real.log N ^ 2 + C / Real.sqrt T + C * PhiT N T s

/-! ### Asymptotic helpers -/

lemma eventually_log7_div (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Real.log N ^ 7 / N ≤ ε := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 7 one_ne_zero
  have h2 := h.comp tendsto_natCast_atTop_atTop
  have h3 := (h2.eventually (gt_mem_nhds hε))
  rw [Filter.eventually_atTop] at h3
  obtain ⟨N₀, hN₀⟩ := h3
  refine ⟨N₀, fun N hN => ?_⟩
  have := hN₀ N hN
  simp only [Function.comp, one_mul, add_zero] at this
  exact this.le

lemma Jn_succ_le_log (N : ℕ) (hN : 4 ≤ N) : ((Jn N + 1 : ℕ) : ℝ) ≤ 2 * Real.log N := by
  obtain ⟨h1, _⟩ := Jn_spec N hN
  have hN1 : (2 : ℝ) ^ (Jn N + 1) ≤ N := by exact_mod_cast h1
  have hl := Real.log_le_log (by positivity) hN1
  rw [Real.log_pow] at hl
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have : ((Jn N + 1 : ℕ) : ℝ) * (1 / 2) ≤ ((Jn N + 1 : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _)
  linarith

/-! ### The large spectrum bound in the middle window -/

set_option maxHeartbeats 1600000 in
/-- **`NuMajorant → GreenLargeSpecMid`**, at `q = 3`, `δ₀ = 1/2`. -/
theorem mid_of_majorant (H : NuMajorant) : LeanLab.DensityGoldbach.U1494.GreenLargeSpecMid := by
  obtain ⟨C, hC, z₁, hmaj⟩ := H
  obtain ⟨C₂, hC₂, hMT⟩ := MT_le_sqrt
  set c₁ : ℝ := 1024 * C ^ 2 + 4 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set K : ℝ := 16 + 256 * c₁ + 512 + (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ := by positivity
    linarith
  have hK0 : 0 < K := by linarith
  refine ⟨1 / 2, by norm_num, 3, by norm_num, by norm_num, K, hK0, z₁,
    fun z hz b hb hcop => ?_⟩
  set W := primorial z with hW
  obtain ⟨Na, hNa⟩ := hmaj z hz b hb hcop
  obtain ⟨Nc, hNc⟩ := nu_avg_close W b hb hcop 1 one_pos
  obtain ⟨Nd, hNd⟩ := eventually_log7_div (K ^ 2 / (67584 * C)) (by positivity)
  refine ⟨max (max Na Nc) (max Nd (max W 4)), fun N _ hNp hN f hf δ hδ hδ₀ hwin => ?_⟩
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNc' : Nc ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNd' : Nd ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNW : W ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  have hN4 : 4 ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  set ν := nuW W b N with hν
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hNr0 : (0 : ℝ) < N := by linarith
  have hW1 : 1 ≤ W := primorial_pos z
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWN : (W : ℝ) ≤ N := by exact_mod_cast hNW
  set lN := Real.log N with hlN
  have hlN1 : 1 ≤ lN := by
    rw [hlN, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlN0 : 0 < lN := by linarith
  -- the window gives `δ > K / (4 log N)`
  set L := Real.log ((W : ℝ) * N) with hL
  have hL0 : 0 < L := Real.log_pos (by nlinarith)
  have hL2 : L ≤ 2 * lN := by
    rw [hL, Real.log_mul (by positivity) (by positivity)]
    have := Real.log_le_log (by positivity) hWN
    linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hd3 : δ ^ (-(3 : ℝ)) = 1 / δ ^ 3 := by
    rw [Real.rpow_neg hδ.le, one_div]; norm_cast
  have hd2 : δ ^ (-(2 : ℝ)) = 1 / δ ^ 2 := by
    rw [Real.rpow_neg hδ.le, one_div]; norm_cast
  have hKδ : K < 2 * L * δ := by
    rw [hd3, hd2] at hwin
    have h3 : 0 < δ ^ 3 := by positivity
    have h2 : 0 < δ ^ 2 := by positivity
    rw [mul_one_div, mul_one_div, div_lt_div_iff₀ h3 h2] at hwin
    have : K * δ ^ 2 < 2 * L * δ * δ ^ 2 := by
      calc K * δ ^ 2 < 2 * L * δ ^ 3 := hwin
        _ = 2 * L * δ * δ ^ 2 := by ring
    exact lt_of_mul_lt_mul_right this h2.le
  have hδlow : K / (4 * lN) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  -- the choice of `T`
  set T : ℕ := ⌈1024 * C ^ 2 / δ ^ 4⌉₊ + 3 with hT
  have hT3 : 3 ≤ T := by omega
  have hT1 : 1 ≤ T := by omega
  have hδ4 : 0 < δ ^ 4 := by positivity
  have hTlow : 1024 * C ^ 2 / δ ^ 4 ≤ (T : ℝ) := by
    have := Nat.le_ceil (1024 * C ^ 2 / δ ^ 4)
    simp only [T]; push_cast; linarith
  have hTup : (T : ℝ) ≤ c₁ / δ ^ 4 := by
    have h1 : (⌈1024 * C ^ 2 / δ ^ 4⌉₊ : ℝ) < 1024 * C ^ 2 / δ ^ 4 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (4 : ℝ) ≤ 4 / δ ^ 4 := by
      rw [le_div_iff₀ hδ4]
      have : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
      linarith
    simp only [T]; push_cast
    rw [hc₁, add_div]
    linarith
  -- `T ≤ (log N)^4`
  have hTlog : (T : ℝ) ≤ lN ^ 4 := by
    have h1 : 1 / δ < 4 * lN / K := by
      rw [div_lt_div_iff₀ hδ hK0]
      rw [div_lt_iff₀ (by positivity)] at hδlow
      linarith
    have h1' : (1 / δ) ^ 4 ≤ (4 * lN / K) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h1.le 4
    have hK4 : 256 * c₁ ≤ K ^ 4 := by
      have : K ≤ K ^ 4 := by
        calc K = K ^ 1 := (pow_one K).symm
          _ ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
      have : 256 * c₁ ≤ K := by
        have : 0 ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ := by positivity
        linarith
      linarith
    calc (T : ℝ) ≤ c₁ / δ ^ 4 := hTup
      _ = c₁ * (1 / δ) ^ 4 := by rw [one_div_pow]; ring
      _ ≤ c₁ * (4 * lN / K) ^ 4 := mul_le_mul_of_nonneg_left h1' hc₁0.le
      _ = 256 * c₁ * lN ^ 4 / K ^ 4 := by rw [div_pow]; ring
      _ ≤ K ^ 4 * lN ^ 4 / K ^ 4 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hK4 (by positivity)
      _ = lN ^ 4 := by field_simp
  -- the average and the majorant
  have hA : avg N ν ≤ 2 := by
    have := hNc N hNc'
    linarith [(abs_le.1 this).2]
  have hmajN := hNa N hNp hNa' T hT1 hTlog
  -- the error terms
  set η := 1 / lN ^ 2 + C / Real.sqrt T with hη
  have hη0 : 0 ≤ η := by positivity
  have hδ2low : K ^ 2 / (16 * lN ^ 2) < δ ^ 2 := by
    have h := pow_lt_pow_left₀ hδlow (by positivity) (two_ne_zero)
    calc K ^ 2 / (16 * lN ^ 2) = (K / (4 * lN)) ^ 2 := by ring
      _ < δ ^ 2 := h
  have hE1 : 2 * (1 / lN ^ 2) ≤ δ ^ 2 / 16 := by
    have hK2 : 512 ≤ K ^ 2 := by
      have : 512 ≤ K := by
        have : 0 ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ := by positivity
        linarith
      nlinarith
    have : 2 * (1 / lN ^ 2) ≤ K ^ 2 / (16 * lN ^ 2) / 16 := by
      rw [div_div, show 16 * lN ^ 2 * 16 = 256 * lN ^ 2 by ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hE2 : 2 * (C / Real.sqrt T) ≤ δ ^ 2 / 16 := by
    have hsq : 32 * C / δ ^ 2 ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      calc (32 * C / δ ^ 2) ^ 2 = 1024 * C ^ 2 / δ ^ 4 := by ring
        _ ≤ (T : ℝ) := hTlow
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 (by positivity)
    have : C / Real.sqrt T ≤ δ ^ 2 / 32 := by
      rw [div_le_iff₀ hsT]
      have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ δ ^ 2 / 32 by positivity)
      have e : δ ^ 2 / 32 * (32 * C / δ ^ 2) = C := by field_simp
      linarith
    linarith
  obtain ⟨_, hJ2⟩ := Jn_spec N hN4
  have hJ2r : (N : ℝ) < 4 * 2 ^ Jn N := by
    have : (N : ℝ) < 2 ^ (Jn N + 2) := by exact_mod_cast hJ2
    rw [pow_add] at this; linarith
  have h2J0 : (0 : ℝ) < 2 ^ Jn N := by positivity
  have hJlog := Jn_succ_le_log N hN4
  have hE3 : 2 * (C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N) + 8 * T / N)) ≤ δ ^ 2 / 8 := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have hinv : 1 / (2 : ℝ) ^ Jn N ≤ 4 / N := by
      rw [div_le_div_iff₀ h2J0 hNr0]; linarith
    have ha : ((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N ≤ 8 * lN ^ 5 / N := by
      calc ((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N = ((Jn N + 1 : ℕ) : ℝ) * T * (1 / 2 ^ Jn N) := by
            ring
        _ ≤ (2 * lN) * lN ^ 4 * (4 / N) := by
            apply mul_le_mul (mul_le_mul hJlog hTlog hT0 (by positivity)) hinv (by positivity)
              (by positivity)
        _ = 8 * lN ^ 5 / N := by ring
    have hb : 8 * (T : ℝ) / N ≤ 8 * lN ^ 5 / N := by
      apply div_le_div_of_nonneg_right _ hNr0.le
      have : lN ^ 4 ≤ lN ^ 5 := pow_le_pow_right₀ hlN1 (by norm_num)
      linarith
    have hc : 2 * (C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N) + 8 * T / N)) ≤
        528 * C * (lN ^ 5 / N) := by
      have := mul_le_mul_of_nonneg_left ha hC.le
      have := mul_le_mul_of_nonneg_left hb hC.le
      have e : 528 * C * (lN ^ 5 / N) = 2 * (C * (32 * (8 * lN ^ 5 / N) + 8 * lN ^ 5 / N)) := by
        ring
      rw [e]
      have : C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N) + 8 * T / N) ≤
          C * (32 * (8 * lN ^ 5 / N) + 8 * lN ^ 5 / N) := by
        apply mul_le_mul_of_nonneg_left _ hC.le; linarith
      linarith
    have hd := hNd N hNd'
    have hd' : 528 * C * (lN ^ 5 / N) ≤ K ^ 2 / (128 * lN ^ 2) := by
      have e : lN ^ 5 / N = (lN ^ 7 / N) / lN ^ 2 := by field_simp
      rw [e]
      have : 528 * C * ((lN ^ 7 / N) / lN ^ 2) ≤ 528 * C * ((K ^ 2 / (67584 * C)) / lN ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right hd (by positivity)
      have e2 : 528 * C * ((K ^ 2 / (67584 * C)) / lN ^ 2) = K ^ 2 / (128 * lN ^ 2) := by
        field_simp; ring
      linarith
    have : K ^ 2 / (128 * lN ^ 2) < δ ^ 2 / 8 := by
      have e : K ^ 2 / (128 * lN ^ 2) = K ^ 2 / (16 * lN ^ 2) / 8 := by ring
      rw [e]; linarith
    linarith
  have hE : 2 * (η + C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N) + 8 * T / N)) ≤ δ ^ 2 / 4 := by
    simp only [hη]
    linarith
  -- the spectrum and TT*
  set S := univ.filter (fun r : ZMod N => δ ≤ ‖hatE N f r‖) with hSdef
  have htt := tt_pairs f ν hf 2 hA δ hδ S (fun r hr => (mem_filter.1 hr).2)
  have havg0 : 0 ≤ avg N ν := by
    unfold avg
    exact mul_nonneg (by positivity) (sum_nonneg fun n _ => nuW_nonneg _ _ _ n)
  have hF0 : ‖hatE N ν 0‖ ≤ 2 := by
    rw [hatE_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg havg0]
    exact hA
  have hmaj' : ∀ s : ZMod N, s ≠ 0 → ‖hatE N ν s‖ ≤ η + C * PhiT N T s := by
    intro s hs
    have := hmajN s hs
    simp only [hη]; linarith
  have hdich := spec_dichotomy hN4 S (fun s => ‖hatE N ν s‖) 2 C η δ T (by norm_num) hC.le hη0 hδ
    hF0 hmaj' htt hE
  set k := (S.card : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  rw [hd3]
  have hδ3 : 0 < δ ^ 3 := by positivity
  rw [mul_one_div, le_div_iff₀ hδ3]
  rcases hdich with h1 | h2
  · -- `k δ² ≤ 16`
    have : k * δ ^ 3 ≤ k * δ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hk0
      calc δ ^ 3 = δ ^ 2 * δ := by ring
        _ ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
        _ = δ ^ 2 := mul_one _
    have : (16 : ℝ) ≤ K := by
      have : 0 ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ := by positivity
      linarith
    nlinarith
  · -- `k^6 δ^16 ≤ (7168 C)^8 M_T`
    have hM := hMT T hT3
    have hsqrt : Real.sqrt T ≤ Real.sqrt c₁ / δ ^ 2 := by
      have := Real.sqrt_le_sqrt hTup
      rw [Real.sqrt_div' _ hδ4.le, show δ ^ 4 = (δ ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)] at this
      exact this
    have hB : (3584 * 2 * C) ^ 8 * MT T ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ / δ ^ 2 := by
      calc (3584 * 2 * C) ^ 8 * MT T ≤ (3584 * 2 * C) ^ 8 * (C₂ * Real.sqrt T) :=
            mul_le_mul_of_nonneg_left hM (by positivity)
        _ ≤ (3584 * 2 * C) ^ 8 * (C₂ * (Real.sqrt c₁ / δ ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hsqrt hC₂.le
        _ = _ := by ring
    have h3 : (k * δ ^ 3) ^ 6 ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ := by
      have h4 : k ^ 6 * δ ^ 16 ≤ (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ / δ ^ 2 := h2.trans hB
      rw [le_div_iff₀ (by positivity)] at h4
      calc (k * δ ^ 3) ^ 6 = k ^ 6 * δ ^ 16 * δ ^ 2 := by ring
        _ ≤ _ := h4
    have hK6 : (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ ≤ K ^ 6 := by
      have : K ≤ K ^ 6 := by
        calc K = K ^ 1 := (pow_one K).symm
          _ ≤ K ^ 6 := pow_le_pow_right₀ hK1 (by norm_num)
      have : (3584 * 2 * C) ^ 8 * C₂ * Real.sqrt c₁ ≤ K := by linarith
      linarith
    have := (pow_le_pow_iff_left₀ (by positivity) hK0.le (by norm_num : (6 : ℕ) ≠ 0)).1
      (h3.trans hK6)
    linarith

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `NuMajorant` only. -/
theorem alsetriShao_1_2_U1502 (H : NuMajorant) : AlsetriShao12 :=
  LeanLab.DensityGoldbach.U1494.alsetriShao_1_2_U1494_mid (mid_of_majorant H)

/-- The full large spectrum bound of U-1488 from `NuMajorant`. -/
theorem largeSpec_of_majorant (H : NuMajorant) : LeanLab.DensityGoldbach.U1488.GreenLargeSpec :=
  LeanLab.DensityGoldbach.U1494.largeSpec_of_small
    (LeanLab.DensityGoldbach.U1494.small_of_mid (mid_of_majorant H))

end LeanLab.DensityGoldbach.U1502
