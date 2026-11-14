module

public import LeanLab.Linnik.ExplicitFormula.Window
public import LeanLab.Linnik.ExplicitFormula.LeftHalf
public import LeanLab.Linnik.ExplicitFormula.Primes
public import LeanLab.Linnik.ExplicitFormula.Page
public import LeanLab.Linnik.ExplicitFormula.DensityLayer
public import LeanLab.Linnik.Decomp482a
public import LeanLab.PNTPort.Gallagher.Basic

/-!
# Assembly of Gallagher 1975 p.131 display 14 from the explicit formula

AI wrote the Lean code. Binary Goldbach is OPEN; this is Gallagher 1975 Theorem 3, used for
Linnik's theorem on primes and powers of 2.

Per character: `window_corr_bound`, the corrected prime window of length at most `L = N/(2P)`,
from `window_bCoef_bound`, `corrCoef_window_le`, a dyadic split of windows that start below
`2L`, and the trivial bound below `N/P^7`, with `h = min(a, L) P^(-3)` and `T = P^10`.
Summed: `mean_decay_nonexceptional` and `mean_decay_exceptional_max`, with
`zero_sum_density_layer`. The statements match `Decomp486c.short_interval_mean_decay` and a
variant of `short_interval_mean_decay_exceptional`, with `corrCoef` for `correctedCoefficient`
and `⌊N/(2N^θ)⌋₊` for `gallagherLength N θ`, both equal by `rfl`.

Status: `window_corr_bound` is proved from the cutoff bound and `asm_window_corr_tail`, the
windows that start above `N/P^7`, itself proved from `asm_piece`, one window `(b, a]` with
`a ≤ 2b` and `h = b P^(-5)`, and `asm_dyadic`, the dyadic split by induction. Both
mean decay theorems are proved from `window_corr_bound`, `zero_sum_density_layer`,
`zero_left_strip`, `mult_zero_le_one`, `page_one_zero`, `Decomp1532b.page_real` and
`Decomp1532b.page_subsingleton`. `asm_window_corr_tail` needs `window_bCoef_bound` from Window.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- A zero of `L(s, χ)` off `s = 1` has analytic order at least one: `L` is analytic on the
connected set `ℂ \ {1}` and `L(2, χ) ≠ 0`, so by the identity theorem it does not vanish near
the zero. Mathlib's `LFunction_ne_zero_of_one_le_re` and `eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
lemma asm_one_le_mult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ : χ.LFunction ρ = 0) (hne : ρ ≠ 1) : 1 ≤ mult χ ρ := by
  have hd : DifferentiableOn ℂ χ.LFunction {1}ᶜ := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have han : AnalyticOnNhd ℂ χ.LFunction {1}ᶜ := hd.analyticOnNhd isOpen_compl_singleton
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have h0 : analyticOrderAt χ.LFunction ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push_neg
    exact ⟨han ρ hne, hρ⟩
  have htop : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have hEq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (z₀ := ρ) hne ht
    have h2 : χ.LFunction 2 = 0 := hEq (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
      (by norm_num) h2
  unfold mult analyticOrderNatAt
  rw [Nat.one_le_iff_ne_zero, Ne, ENat.toNat_eq_zero]
  push_neg
  exact ⟨h0, htop⟩

/-- Membership in `zerosTo` for a primitive character, from `zeros_rect_finite`. -/
lemma asm_zerosTo_iff {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (T : ℝ) (ρ : ℂ) : ρ ∈ zerosTo χ T ↔ ρ ∈ Zall χ ∧ |ρ.im| ≤ T := by
  unfold zerosTo
  rw [dif_pos (zeros_rect_finite hχ T), Set.Finite.mem_toFinset]
  rfl

/-- The weighted zero sum of the tail bound, with `X = N/P^8` and `T = P^10`. -/
noncomputable def asmZ (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)) (r : ℕ) (γ : ℝ) (N P : ℝ) : ℝ :=
  ∑ ρ ∈ zerosTo χ (P ^ 10), ((mult χ ρ : ℝ) -
    (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0)) * (N / P ^ 8) ^ (ρ.re - 1)

/-- The zeros in `zerosTo` of a primitive character have `0 ≤ Re ρ ≤ 1`. -/
lemma asm_re_bounds {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosTo χ T) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  obtain ⟨⟨h0, h1, h2⟩, _⟩ := (asm_zerosTo_iff hχ T ρ).1 hρ
  constructor
  · by_contra hn
    have := zero_left_strip hχ h0 h1 (le_of_lt (not_le.mp hn))
    rw [this] at hn; simp at hn
  · by_contra hn
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (not_le.mp hn).le h0

/-- The weights `m(ρ) - [ρ = γ]` are nonnegative. -/
lemma asm_weight_nonneg (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)) (r : ℕ) (γ : ℝ)
    (hγ : k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 → 0 < γ ∧ γ < 1) (ρ : ℂ) :
    0 ≤ (mult χ ρ : ℝ) - (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0) := by
  split_ifs with hc
  · have hγ1 := (hγ ⟨hc.1, hc.2.1⟩).2
    have hne : (γ : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have := asm_one_le_mult χ hc.2.1 hne
    rw [hc.2.2]
    have : (1 : ℝ) ≤ mult χ (γ : ℂ) := by exact_mod_cast this
    linarith
  · simp

lemma asmZ_nonneg (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)) (r : ℕ) (γ : ℝ)
    (hγ : k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 → 0 < γ ∧ γ < 1) {N P : ℝ} (hX : 0 < N / P ^ 8) :
    0 ≤ asmZ k χ r γ N P :=
  sum_nonneg fun ρ _ => mul_nonneg (asm_weight_nonneg k χ r γ hγ ρ) (Real.rpow_nonneg hX.le _)

/-- `x^(3/2) = x √x`. -/
lemma asm_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

set_option maxHeartbeats 1000000 in
/-- One window `(b, a]` with `a ≤ 2b` above the cutoff: `corrCoef_window_le` with `M` from
`window_bCoef_bound`, `h = b P^(-5)` and `T = P^10`. -/
theorem asm_piece : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N P : ℝ), 3 ≤ N → 8 ≤ P → P ^ 21 ≤ N →
    Real.log N ≤ P → ∀ (k : ℕ), ((k : ℝ) + 1 ≤ P) →
    ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
    ∀ (r : ℕ) (γ : ℝ), (k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 → 0 < γ ∧ γ < 1) →
    ∀ (a b : ℕ), b ≤ a → (a : ℝ) ≤ 2 * b → (a : ℝ) ≤ 3 * N → N / P ^ 7 ≤ b →
      ‖∑ n ∈ Ioc b a, corrCoef χ r γ n‖ ≤
        8 * ((a : ℝ) - b) / Real.log N * asmZ k χ r γ N P + K * (b / P ^ 5 + 1) := by
  obtain ⟨C, hC, hW⟩ := window_bCoef_bound
  refine ⟨20 * C + 1, by positivity, ?_⟩
  intro N P hN3 hP8 hPN hlogP k hkP χ hχ r γ hγ a b hba ha2 ha3 hb
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hN0 : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  -- the size of `b`
  have hNb : N ≤ b * P ^ 7 := by rwa [div_le_iff₀ (by positivity)] at hb
  have hb14 : P ^ 14 ≤ (b : ℝ) := by
    have : P ^ 14 * P ^ 7 ≤ b * P ^ 7 := by
      calc P ^ 14 * P ^ 7 = P ^ 21 := by ring
        _ ≤ N := hPN
        _ ≤ _ := hNb
    exact le_of_mul_le_mul_right this (by positivity)
  have hP7 : 8 * P ^ 6 ≤ P ^ 7 := by
    have : 0 ≤ P ^ 6 := by positivity
    have e : P ^ 7 = P * P ^ 6 := by ring
    rw [e]; nlinarith
  have hP7b : P ^ 7 ≤ (b : ℝ) := by
    have : P ^ 7 ≤ P ^ 14 := pow_le_pow_right₀ hP1 (by norm_num)
    linarith
  have hb4 : (4 : ℝ) ≤ b := by
    have : (8 : ℝ) ≤ P ^ 7 := by
      calc (8 : ℝ) ≤ P := hP8
        _ ≤ P ^ 7 := le_self_pow₀ hP1 (by norm_num)
    linarith
  have hb2 : 2 ≤ b := by
    have : (2 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  have hb1 : 1 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hNb2 : N ≤ (b : ℝ) * b := by
    calc N ≤ b * P ^ 7 := hNb
      _ ≤ b * b := mul_le_mul_of_nonneg_left hP7b hb0.le
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlogb1 : 1 ≤ Real.log b := by
    have h4 : Real.log 4 ≤ Real.log b := Real.log_le_log (by norm_num) hb4
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hlogNb : Real.log N ≤ 2 * Real.log b := by
    have := Real.log_le_log hN0 hNb2
    rw [Real.log_mul hb0.ne' hb0.ne'] at this
    linarith
  -- `s = √b`
  set s := Real.sqrt b with hs
  have hss : s * s = b := Real.mul_self_sqrt hb0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsP : P ^ 7 ≤ s := by
    have := Real.sqrt_le_sqrt hb14
    rwa [show P ^ 14 = (P ^ 7) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
  have hs8 : 8 * P ^ 6 ≤ s := hP7.trans hsP
  have hsa : Real.sqrt a ≤ 2 * s := by
    rw [hs, show 2 * Real.sqrt b = Real.sqrt (4 * b) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsb : 8 * P ^ 6 * s ≤ b := by
    rw [← hss]; exact mul_le_mul_of_nonneg_right hs8 hs0
  -- the parameters
  set h : ℝ := (b : ℝ) / P ^ 5 with hh
  set T : ℝ := P ^ 10 with hT
  have hP5b : P ^ 5 ≤ (b : ℝ) := le_trans (pow_le_pow_right₀ hP1 (by norm_num)) hb14
  have hh0 : 0 < h := by positivity
  have hh1 : 1 ≤ h := by rw [hh, le_div_iff₀ (by positivity)]; linarith
  have hhb : h ≤ b := div_le_self hb0.le (one_le_pow₀ hP1)
  have hT1 : 1 ≤ T := one_le_pow₀ hP1
  have hT0 : 0 < T := by linarith
  have hS : ∀ ρ, ρ ∈ zerosTo χ T ↔ ρ ∈ Zall χ ∧ |ρ.im| ≤ T := asm_zerosTo_iff hχ T
  set e : ℕ := if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 then 1 else 0 with he
  have he1 : e ≤ 1 := by rw [he]; split_ifs <;> norm_num
  have heγ : e = 1 → (γ : ℂ) ∈ zerosTo χ T ∧ 0 < γ := by
    intro h1
    have hc : k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 := by
      by_contra hc
      rw [he, if_neg hc] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨hγ0, hγ1⟩ := hγ hc
    refine ⟨(hS _).2 ⟨⟨hc.2, ?_, ?_⟩, ?_⟩, hγ0⟩
    · simp only [Complex.ofReal_re]; linarith
    · intro h'
      have := congrArg Complex.re h'
      simp at this
      linarith
    · simp only [Complex.ofReal_im, abs_zero]; positivity
  have hind : ∀ ρ : ℂ, (if e = 1 ∧ ρ = (γ : ℂ) then (1 : ℝ) else 0) =
      (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0) := by
    intro ρ
    by_cases hc : k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0
    · have : e = 1 := by rw [he, if_pos hc]
      simp [this, hc.1, hc.2]
    · have : e = 0 := by rw [he, if_neg hc]
      rw [if_neg (by rw [this]; simp), if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩)]
  have hw0 : ∀ ρ, 0 ≤ (mult χ ρ : ℝ) - (if e = 1 ∧ ρ = (γ : ℂ) then (1 : ℝ) else 0) := by
    intro ρ; rw [hind ρ]; exact asm_weight_nonneg k χ r γ hγ ρ
  -- the bound `M` on the partial windows
  set Sa := ∑ ρ ∈ zerosTo χ T, ((mult χ ρ : ℝ) - (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) *
    (2 * (a : ℝ)) ^ ρ.re with hSa
  set E := (h + 1) * a * Real.log (2 * a) +
    Real.log (((k + 1 : ℕ) : ℝ) + 2) * (a : ℝ) ^ (3 / 2 : ℝ) / h +
    (a : ℝ) ^ 3 * Real.log (((k + 1 : ℕ) : ℝ) * (T + 2)) / (h * T) with hE
  have hM : ∀ u ∈ Icc b a, ‖∑ n ∈ Ioc b u, (bCoef χ n - (if k + 1 = 1 then (n : ℂ) else 0) +
        (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 then (((n : ℝ) ^ γ : ℝ) : ℂ) else 0))‖ ≤
        ((a : ℝ) - b) * Sa + C * E := by
    intro u hu
    obtain ⟨hbu, hua⟩ := mem_Icc.1 hu
    have hbu' : (b : ℝ) ≤ u := by exact_mod_cast hbu
    have hua' : (u : ℝ) ≤ a := by exact_mod_cast hua
    have hwu := hW (k + 1) χ hχ u b h T hb1 hbu hh1 (hhb.trans hbu') hT1 (zerosTo χ T) hS e γ
      he1 heγ
    have hsum : ∑ n ∈ Ioc b u, (bCoef χ n - (if k + 1 = 1 then (n : ℂ) else 0) +
        (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 then (((n : ℝ) ^ γ : ℝ) : ℂ) else 0)) =
        ∑ n ∈ Ioc b u, bCoef χ n - (if k + 1 = 1 then ∑ n ∈ Ioc b u, (n : ℂ) else 0) +
          (e : ℂ) * ∑ n ∈ Ioc b u, (((n : ℝ) ^ γ : ℝ) : ℂ) := by
      rw [sum_add_distrib, sum_sub_distrib]
      congr 1
      · congr 1
        split_ifs <;> simp
      · rw [he]; split_ifs <;> simp
    rw [hsum]
    refine hwu.trans ?_
    have hu0 : (0 : ℝ) < u := by linarith
    have hmono : ∑ ρ ∈ zerosTo χ T, ((mult χ ρ : ℝ) - (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) *
        (2 * (u : ℝ)) ^ ρ.re ≤ Sa := by
      apply sum_le_sum
      intro ρ hρ
      apply mul_le_mul_of_nonneg_left _ (hw0 ρ)
      exact Real.rpow_le_rpow (by positivity) (by linarith) (asm_re_bounds hχ hρ).1
    have hS0u : 0 ≤ ∑ ρ ∈ zerosTo χ T, ((mult χ ρ : ℝ) -
        (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) * (2 * (u : ℝ)) ^ ρ.re :=
      sum_nonneg fun ρ _ => mul_nonneg (hw0 ρ) (Real.rpow_nonneg (by positivity) _)
    have hq2 : (0 : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ) + 2) := Real.log_nonneg (by push_cast; linarith)
    have hqT : (0 : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ) * (T + 2)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      nlinarith
    have e1 : (h + 1) * u * Real.log (2 * u) ≤ (h + 1) * a * Real.log (2 * a) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hua' (by linarith))
        (Real.log_le_log (by positivity) (by linarith)) (Real.log_nonneg (by linarith))
        (by positivity)
    have e2 : Real.log (((k + 1 : ℕ) : ℝ) + 2) * (u : ℝ) ^ (3 / 2 : ℝ) / h ≤
        Real.log (((k + 1 : ℕ) : ℝ) + 2) * (a : ℝ) ^ (3 / 2 : ℝ) / h :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hu0.le hua' (by norm_num)) hq2) hh0.le
    have e3 : (u : ℝ) ^ 3 * Real.log (((k + 1 : ℕ) : ℝ) * (T + 2)) / (h * T) ≤
        (a : ℝ) ^ 3 * Real.log (((k + 1 : ℕ) : ℝ) * (T + 2)) / (h * T) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hu0.le hua' 3) hqT) (by positivity)
    have e4 : ((u : ℝ) - b) * ∑ ρ ∈ zerosTo χ T, ((mult χ ρ : ℝ) -
        (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) * (2 * (u : ℝ)) ^ ρ.re ≤ ((a : ℝ) - b) * Sa :=
      mul_le_mul (by linarith) hmono hS0u (by linarith)
    have e5 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hC
    rw [hE]
    linarith
  have hcw := corrCoef_window_le χ r γ hb2 hba hM
  refine hcw.trans ?_
  -- the main term
  have hX0 : 0 < N / P ^ 8 := by positivity
  have hX2a : N / P ^ 8 ≤ 2 * a := by
    have : N / P ^ 8 ≤ N / P ^ 7 :=
      div_le_div_of_nonneg_left hN0.le (by positivity) (pow_le_pow_right₀ hP1 (by norm_num))
    linarith
  have hZ0 := asmZ_nonneg k χ r γ hγ hX0
  have hSaZ : Sa ≤ 2 * a * asmZ k χ r γ N P := by
    rw [hSa, asmZ, mul_sum]
    apply sum_le_sum
    intro ρ hρ
    rw [hind ρ]
    have hre := asm_re_bounds hχ hρ
    have h2a : (0 : ℝ) < 2 * a := by linarith
    have hpw : (2 * (a : ℝ)) ^ ρ.re = 2 * a * (2 * a) ^ (ρ.re - 1) := by
      rw [Real.rpow_sub_one h2a.ne']; field_simp
    rw [hpw]
    have hmono : (2 * (a : ℝ)) ^ (ρ.re - 1) ≤ (N / P ^ 8) ^ (ρ.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hX0 hX2a (by linarith)
    have key := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmono (asm_weight_nonneg k χ r γ hγ ρ)) h2a.le
    linarith
  clear_value Sa E s h T
  generalize asmZ k χ r γ N P = Z at hZ0 hSaZ ⊢
  have hSa0 : 0 ≤ Sa := by
    rw [hSa]; exact sum_nonneg fun ρ _ => mul_nonneg (hw0 ρ) (Real.rpow_nonneg (by positivity) _)
  have hD : (0 : ℝ) ≤ (a : ℝ) - b := by linarith
  have hmain : ((a : ℝ) - b) * Sa / (b * Real.log b) ≤
      8 * ((a : ℝ) - b) / Real.log N * Z := by
    rw [div_le_iff₀ (by positivity)]
    have hr : 1 ≤ 2 * Real.log b / Real.log N := by rw [le_div_iff₀ hlogN]; linarith
    have e1 : 8 * ((a : ℝ) - b) / Real.log N * Z * (b * Real.log b) =
        4 * ((a : ℝ) - b) * Z * b * (2 * Real.log b / Real.log N) := by
      field_simp; ring
    rw [e1]
    have h4 : 0 ≤ 4 * ((a : ℝ) - b) * Z * b :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD) hZ0) hb0.le
    have e2 := mul_le_mul_of_nonneg_left hr h4
    have e3' := mul_le_mul_of_nonneg_right (show 2 * (a : ℝ) ≤ 4 * b by linarith) hZ0
    have e3 : Sa ≤ 4 * b * Z := by linarith
    have e4 := mul_le_mul_of_nonneg_left e3 hD
    linarith
  -- the errors
  have hlog2a : Real.log (2 * a) ≤ 2 * Real.log b := by
    have h1 : Real.log (2 * a) ≤ Real.log (4 * b) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hb0.ne'] at h1
    have : Real.log 4 ≤ Real.log b := Real.log_le_log (by norm_num) hb4
    linarith
  have hT1b : (h + 1) * a * Real.log (2 * a) ≤ (4 * (b / P ^ 5) + 4) * (b * Real.log b) := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left ha2 (show (0 : ℝ) ≤ h + 1 by linarith)) hlog2a
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * a))
      (mul_nonneg (by linarith : (0 : ℝ) ≤ h + 1) (by positivity : (0 : ℝ) ≤ 2 * b))
    rw [← hh]
    linarith
  have hq : ((k + 1 : ℕ) : ℝ) ≤ P := by push_cast; linarith
  have hT2b : Real.log (((k + 1 : ℕ) : ℝ) + 2) * (a : ℝ) ^ (3 / 2 : ℝ) / h ≤ b * Real.log b := by
    rw [div_le_iff₀ hh0]
    have L1 : Real.log (((k + 1 : ℕ) : ℝ) + 2) ≤ 2 * P := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 2 by positivity)
      linarith
    have L2 : (a : ℝ) ^ (3 / 2 : ℝ) ≤ 4 * b * s := by
      rw [asm_rpow_three_halves ha0.le]
      have := mul_le_mul ha2 hsa (Real.sqrt_nonneg _) (by positivity)
      linarith
    have L3 := mul_le_mul L1 L2 (by positivity) (by positivity)
    have L4 : 2 * P * (4 * b * s) ≤ b * h := by
      rw [hh, mul_div_assoc', le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hsb hb0.le
      have e : 2 * P * (4 * (b : ℝ) * s) * P ^ 5 = b * (8 * P ^ 6 * s) := by ring
      rw [e]; exact this
    have L5 : b * h ≤ b * Real.log b * h := by
      have := mul_le_mul_of_nonneg_left hlogb1 (mul_nonneg hb0.le hh0.le)
      linarith
    linarith
  have hT3b : (a : ℝ) ^ 3 * Real.log (((k + 1 : ℕ) : ℝ) * (T + 2)) / (h * T) ≤
      16 * (b / P ^ 5) * (b * Real.log b) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 16 * (b / P ^ 5) * (b * Real.log b) * (h * T) = 16 * (b : ℝ) ^ 3 * Real.log b := by
      rw [hh, hT]; first | (field_simp; ring) | field_simp
    rw [e]
    have L1 : (a : ℝ) ^ 3 ≤ 8 * (b : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ ha0.le ha2 3
      linarith [show (2 * (b : ℝ)) ^ 3 = 8 * (b : ℝ) ^ 3 by ring]
    have hqT1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (T + 2) := by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact one_le_mul_of_one_le_of_one_le this (by linarith)
    have L2 : Real.log (((k + 1 : ℕ) : ℝ) * (T + 2)) ≤ 2 * Real.log b := by
      have hP11 : P ^ 10 + 2 ≤ P ^ 11 := by
        have : 0 ≤ P ^ 10 := by positivity
        have e : P ^ 11 = P * P ^ 10 := by ring
        have : 1 ≤ P ^ 10 := one_le_pow₀ hP1
        rw [e]; nlinarith
      have hP12 : P ^ 12 ≤ N := by
        have : P ^ 12 ≤ P ^ 21 := pow_le_pow_right₀ hP1 (by norm_num)
        linarith
      have hle : ((k + 1 : ℕ) : ℝ) * (T + 2) ≤ N := by
        calc ((k + 1 : ℕ) : ℝ) * (T + 2) ≤ P * P ^ 11 := by
              rw [hT]; exact mul_le_mul hq hP11 (by positivity) hP0.le
          _ = P ^ 12 := by ring
          _ ≤ N := hP12
      have := Real.log_le_log (by linarith) hle
      linarith
    have := mul_le_mul L1 L2 (Real.log_nonneg hqT1) (by positivity)
    linarith
  have hEb : E / (b * Real.log b) ≤ 20 * (b / P ^ 5) + 5 := by
    rw [div_le_iff₀ (by positivity), hE]
    have : 0 ≤ (b : ℝ) * Real.log b := by positivity
    linarith
  have hpp : 2 * Real.sqrt a * Real.log a ≤ b / P ^ 5 := by
    have hla : Real.log a ≤ 2 * P := by
      have h1 : Real.log a ≤ Real.log (N * N) := Real.log_le_log ha0 (by nlinarith)
      rw [Real.log_mul hN0.ne' hN0.ne'] at h1
      linarith
    have := mul_le_mul (mul_le_mul_of_nonneg_left hsa (by norm_num : (0 : ℝ) ≤ 2)) hla
      (Real.log_nonneg (by linarith)) (by positivity)
    have h8 : 8 * P * s ≤ b / P ^ 5 := by
      rw [le_div_iff₀ (by positivity)]
      have e : 8 * P * s * P ^ 5 = 8 * P ^ 6 * s := by ring
      rw [e]; exact hsb
    linarith
  have hsplit : (((a : ℝ) - b) * Sa + C * E) / (b * Real.log b) =
      ((a : ℝ) - b) * Sa / (b * Real.log b) + C * (E / (b * Real.log b)) := by
    ring
  rw [hsplit]
  have hCE := mul_le_mul_of_nonneg_left hEb hC
  have hbP : 0 ≤ (b : ℝ) / P ^ 5 := by positivity
  have hC5 : C * 5 ≤ C * 20 := by linarith
  rw [← hh] at hCE hpp
  linarith

/-- The dyadic split: windows `(b, a]` with `a ≤ 2^(j+1) b`, by induction on `j`. -/
theorem asm_dyadic (K : ℝ) (hK : 0 ≤ K) (N P : ℝ) (k : ℕ) (χ : DirichletCharacter ℂ (k + 1))
    (r : ℕ) (γ : ℝ)
    (hpiece : ∀ (a b : ℕ), b ≤ a → (a : ℝ) ≤ 2 * b → (a : ℝ) ≤ 3 * N → N / P ^ 7 ≤ b →
      ‖∑ n ∈ Ioc b a, corrCoef χ r γ n‖ ≤
        8 * ((a : ℝ) - b) / Real.log N * asmZ k χ r γ N P + K * (b / P ^ 5 + 1))
    (hP : 0 < P) (j : ℕ) :
    ∀ (a b : ℕ), b ≤ a → (a : ℝ) ≤ 2 ^ (j + 1) * b → (a : ℝ) ≤ 3 * N → N / P ^ 7 ≤ b →
      ‖∑ n ∈ Ioc b a, corrCoef χ r γ n‖ ≤
        8 * ((a : ℝ) - b) / Real.log N * asmZ k χ r γ N P +
          K * ((2 * ((a : ℝ) - b) + b) / P ^ 5 + (j + 1)) := by
  induction j with
  | zero =>
    intro a b hba ha2 ha3 hb
    rw [zero_add, pow_one] at ha2
    have hab : (b : ℝ) ≤ a := by exact_mod_cast hba
    refine (hpiece a b hba ha2 ha3 hb).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hK))
    have : (b : ℝ) / P ^ 5 ≤ (2 * ((a : ℝ) - b) + b) / P ^ 5 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    push_cast
    linarith
  | succ j ih =>
    intro a b hba ha2 ha3 hb
    have hab : (b : ℝ) ≤ a := by exact_mod_cast hba
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    by_cases hc : (a : ℝ) ≤ 2 * b
    · refine (hpiece a b hba hc ha3 hb).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hK))
      have : (b : ℝ) / P ^ 5 ≤ (2 * ((a : ℝ) - b) + b) / P ^ 5 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      push_cast
      linarith
    · push_neg at hc
      have h2b : 2 * b ≤ a := by
        have : ((2 * b : ℕ) : ℝ) ≤ a := by push_cast; linarith
        exact_mod_cast this
      have hb2 : b ≤ 2 * b := by omega
      rw [← sum_Ioc_consecutive _ hb2 h2b]
      have h1 := hpiece (2 * b) b hb2 (by push_cast; linarith) (by push_cast; linarith) hb
      have h2 := ih a (2 * b) h2b (by push_cast; rw [pow_succ] at ha2; linarith) ha3
        (by push_cast; linarith)
      push_cast at h1 h2 ⊢
      generalize asmZ k χ r γ N P = Z at h1 h2 ⊢
      have e : 8 * (2 * (b : ℝ) - b) / Real.log N * Z + K * (b / P ^ 5 + 1) +
          (8 * ((a : ℝ) - 2 * b) / Real.log N * Z +
            K * ((2 * ((a : ℝ) - 2 * b) + 2 * b) / P ^ 5 + (j + 1))) =
          8 * ((a : ℝ) - b) / Real.log N * Z +
            K * ((2 * ((a : ℝ) - b) + b) / P ^ 5 + (j + 1 + 1)) := by ring
      have := norm_add_le (∑ n ∈ Ioc b (2 * b), corrCoef χ r γ n)
        (∑ n ∈ Ioc (2 * b) a, corrCoef χ r γ n)
      linarith

set_option maxHeartbeats 1000000 in
/-- Gallagher 1970 Section 7 and Gallagher 1975 p.131, one character, one window that starts
above the cutoff `N/P^7`. This is the analytic part of `window_corr_bound`: a dyadic split of the
window, `corrCoef_window_le` on each piece with `M` from `window_bCoef_bound`, `T = P^10` and,
in place of the plan note's `h = min(a, L) P^(-3)`, the step `h = b P^(-5)` on a piece `(b, a]`,
which balances the smoothing error `h` against the truncation error `b^2/(h T)`. -/
theorem asm_window_corr_tail : ∃ C θ₁ : ℝ, 0 ≤ C ∧ 0 < θ₁ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₁ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
    ∀ (r : ℕ) (γ : ℝ), (k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 → 0 < γ ∧ γ < 1) →
    ∀ (a b : ℕ), b ≤ a → a ≤ 2 * N + 2 → ((a : ℝ) - b) ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ) →
      (N : ℝ) / ((N : ℝ) ^ θ) ^ 7 ≤ b →
      ‖∑ n ∈ Ioc b a, corrCoef χ r γ n‖ ≤
        C * ((N : ℝ) / (N : ℝ) ^ θ) / Real.log N *
          (∑ ρ ∈ zerosTo χ (((N : ℝ) ^ θ) ^ 10),
              ((mult χ ρ : ℝ) -
                (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0)) *
                ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (ρ.re - 1) +
            ((N : ℝ) ^ θ)⁻¹ ^ 3) := by
  obtain ⟨K, hK, hpiece⟩ := asm_piece
  refine ⟨4 + 5 * K, 1 / 21, by linarith, by norm_num, ?_⟩
  intro θ hθ hθ1
  refine ⟨max 3 ⌈Real.exp (8 / θ ^ 2)⌉₊, ?_⟩
  intro N hN k hk χ hχ r γ hγ a b hba ha hab hb
  have hN3 : (3 : ℝ) ≤ N := by
    have : 3 ≤ N := le_trans (le_max_left _ _) hN
    exact_mod_cast this
  have hNe : Real.exp (8 / θ ^ 2) ≤ N := by
    have : ⌈Real.exp (8 / θ ^ 2)⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog1 : 8 / θ ^ 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hθle : θ ≤ 1 := by linarith
  have hθ2 : 8 ≤ θ ^ 2 * Real.log N := by
    have := mul_le_mul_of_nonneg_left hlog1 (sq_nonneg θ)
    rwa [show θ ^ 2 * (8 / θ ^ 2) = 8 by field_simp] at this
  have hx8 : 8 ≤ θ * Real.log N := by
    have : θ ^ 2 * Real.log N ≤ θ * Real.log N := by
      have : θ ^ 2 ≤ θ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hlog.le
    linarith
  set P := (N : ℝ) ^ θ with hPdef
  have hPexp : P = Real.exp (θ * Real.log N) := by
    rw [hPdef, Real.rpow_def_of_pos hN0, mul_comm]
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ θ * Real.log N by linarith)
  have hP8 : 8 ≤ P := by
    rw [hPexp]
    have : 0 ≤ (θ * Real.log N) ^ 2 / 2 := by positivity
    linarith
  have hlogP : Real.log N ≤ P := by
    rw [hPexp]
    have h4 : 8 * Real.log N ≤ θ ^ 2 * Real.log N * Real.log N :=
      mul_le_mul_of_nonneg_right hθ2 hlog.le
    have e : (θ * Real.log N) ^ 2 / 2 = θ ^ 2 * Real.log N * Real.log N / 2 := by ring
    linarith
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hPN : P ^ 21 ≤ N := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ (θ * ((21 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = N := Real.rpow_one _
  clear_value P
  have hkP : (k : ℝ) + 1 ≤ P := by
    have h1 : k + 1 ≤ ⌊P⌋₊ := hk
    have : ((k + 1 : ℕ) : ℝ) ≤ P := (Nat.cast_le.mpr h1).trans (Nat.floor_le hP0.le)
    push_cast at this; exact this
  have ha3 : (a : ℝ) ≤ 3 * N := by
    have : (a : ℝ) ≤ 2 * N + 2 := by exact_mod_cast ha
    linarith
  -- the number of dyadic pieces
  set m := ⌈P⌉₊ with hm
  have hPm : P ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hmP : (m : ℝ) ≤ P + 1 := (Nat.ceil_lt_add_one hP0.le).le
  have hNb : N ≤ b * P ^ 7 := by rwa [div_le_iff₀ (by positivity)] at hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hP6 : 2 ≤ P ^ 6 := by
    have : P ≤ P ^ 6 := le_self_pow₀ hP1 (by norm_num)
    linarith
  have hab' : (a : ℝ) ≤ P ^ 6 * b := by
    have h1 : (N : ℝ) / (2 * P) ≤ b * P ^ 6 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have e : (b : ℝ) * P ^ 6 * (2 * P) = 2 * (b * P ^ 7) := by ring
      rw [e]; linarith
    have h2 : (b : ℝ) + b * P ^ 6 / 2 ≤ P ^ 6 * b := by nlinarith
    linarith
  have hpow : (a : ℝ) ≤ 2 ^ (6 * m + 1) * b := by
    have h1 : P ^ 6 ≤ (2 : ℝ) ^ (6 * m + 1) := by
      calc P ^ 6 ≤ ((2 : ℝ) ^ m) ^ 6 := pow_le_pow_left₀ hP0.le (hPm.trans hm2) 6
        _ = 2 ^ (6 * m) := by rw [← pow_mul, mul_comm]
        _ ≤ 2 ^ (6 * m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact hab'.trans (mul_le_mul_of_nonneg_right h1 hb0)
  have hd := asm_dyadic K hK (N : ℝ) P k χ r γ
    (hpiece N P hN3 hP8 hPN hlogP k hkP χ hχ r γ hγ) hP0 (6 * m) a b hba hpow ha3 hb
  show _ ≤ (4 + 5 * K) * ((N : ℝ) / P) / Real.log N * (asmZ k χ r γ N P + P⁻¹ ^ 3)
  refine hd.trans ?_
  have hZ0 := asmZ_nonneg k χ r γ hγ (show (0 : ℝ) < N / P ^ 8 by positivity)
  generalize asmZ k χ r γ N P = Z at hZ0 ⊢
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  -- the main term
  have hA : 8 * ((a : ℝ) - b) / Real.log N * Z ≤
      4 * ((N : ℝ) / P / Real.log N) * Z := by
    apply mul_le_mul_of_nonneg_right _ hZ0
    rw [show 4 * ((N : ℝ) / P / Real.log N) = 4 * ((N : ℝ) / P) / Real.log N by ring]
    apply div_le_div_of_nonneg_right _ hlog.le
    have : (N : ℝ) / (2 * P) = N / P / 2 := by field_simp
    linarith
  -- the errors
  have hB1 : (2 * ((a : ℝ) - b) + b) / P ^ 5 ≤ 4 * (N / P ^ 5) := by
    rw [show 4 * ((N : ℝ) / P ^ 5) = (4 * N) / P ^ 5 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (N : ℝ) / (2 * P) ≤ N / 2 := div_le_div_of_nonneg_left hN0.le (by norm_num) (by linarith)
    linarith
  have hB2 : ((6 * m : ℕ) : ℝ) + 1 ≤ N / P ^ 5 := by
    rw [le_div_iff₀ (by positivity)]
    push_cast
    have h7 : 7 * P ^ 6 ≤ P ^ 21 := by
      have : P ^ 6 * P ^ 15 = P ^ 21 := by ring
      have h15 : 8 ≤ P ^ 15 := hP8.trans (le_self_pow₀ hP1 (by norm_num))
      have := mul_le_mul_of_nonneg_left h15 (by positivity : (0 : ℝ) ≤ P ^ 6)
      linarith
    have : (6 * (m : ℝ) + 1) ≤ 7 * P := by linarith
    have h3 := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ P ^ 5)
    have e : 7 * P * P ^ 5 = 7 * P ^ 6 := by ring
    linarith
  have hB3 : (N : ℝ) / P ^ 5 ≤ (N : ℝ) / P / Real.log N * P⁻¹ ^ 3 := by
    have e : (N : ℝ) / P / Real.log N * P⁻¹ ^ 3 = N / (P ^ 4 * Real.log N) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_left hN0.le (by positivity)
    calc P ^ 4 * Real.log N ≤ P ^ 4 * P := mul_le_mul_of_nonneg_left hlogP (by positivity)
      _ = P ^ 5 := by ring
  have hB : K * ((2 * ((a : ℝ) - b) + b) / P ^ 5 + (((6 * m : ℕ) : ℝ) + 1)) ≤
      5 * K * ((N : ℝ) / P / Real.log N * P⁻¹ ^ 3) := by
    have := mul_le_mul_of_nonneg_left (add_le_add hB1 hB2) hK
    have h2 := mul_le_mul_of_nonneg_left hB3 (show 0 ≤ 5 * K by positivity)
    linarith
  have hQ0 : 0 ≤ (N : ℝ) / P / Real.log N := by positivity
  have hI0 : 0 ≤ P⁻¹ ^ 3 := by positivity
  have e : (4 + 5 * K) * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) =
      4 * ((N : ℝ) / P / Real.log N) * Z +
        5 * K * ((N : ℝ) / P / Real.log N * P⁻¹ ^ 3) +
        4 * ((N : ℝ) / P / Real.log N * P⁻¹ ^ 3) +
        5 * K * ((N : ℝ) / P / Real.log N) * Z := by ring
  rw [e]
  have x1 : 0 ≤ 4 * ((N : ℝ) / P / Real.log N * P⁻¹ ^ 3) := by positivity
  have x2 : 0 ≤ 5 * K * ((N : ℝ) / P / Real.log N) * Z :=
    mul_nonneg (mul_nonneg (by positivity) hQ0) hZ0
  push_cast at hB ⊢
  linarith

/-- Gallagher 1970 Section 7 and Gallagher 1975 p.131, one character, one window. -/
theorem window_corr_bound : ∃ C θ₁ : ℝ, 0 ≤ C ∧ 0 < θ₁ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₁ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
    ∀ (r : ℕ) (γ : ℝ), (k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 → 0 < γ ∧ γ < 1) →
    ∀ (a b : ℕ), b ≤ a → a ≤ 2 * N + 2 → ((a : ℝ) - b) ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ) →
      ‖∑ n ∈ Ioc b a, corrCoef χ r γ n‖ ≤
        C * ((N : ℝ) / (N : ℝ) ^ θ) / Real.log N *
          (∑ ρ ∈ zerosTo χ (((N : ℝ) ^ θ) ^ 10),
              ((mult χ ρ : ℝ) -
                (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0)) *
                ((N : ℝ) / ((N : ℝ) ^ θ) ^ 8) ^ (ρ.re - 1) +
            ((N : ℝ) ^ θ)⁻¹ ^ 3) := by
  obtain ⟨C, θ₁, hC, hθ₁, hT⟩ := asm_window_corr_tail
  refine ⟨C + 8, min θ₁ (1 / 11), by linarith, lt_min hθ₁ (by norm_num), ?_⟩
  intro θ hθ hθ0
  obtain ⟨N₁, hN₁⟩ := hT θ hθ (hθ0.trans (min_le_left _ _))
  have hθc : θ ≤ 1 / 11 := hθ0.trans (min_le_right _ _)
  refine ⟨max N₁ (max 3 ⌈Real.exp (1 / θ ^ 2)⌉₊), ?_⟩
  intro N hN k hk χ hχ r γ hγ a b hba ha hab
  have hN1' : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : (3 : ℝ) ≤ N := by
    have : 3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact_mod_cast this
  have hNe : Real.exp (1 / θ ^ 2) ≤ N := by
    have : ⌈Real.exp (1 / θ ^ 2)⌉₊ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog1 : 1 / θ ^ 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  set P := (N : ℝ) ^ θ with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 hθ.le
  have hP0 : 0 < P := by linarith
  have hPθ : 1 / θ ≤ P := by
    rw [hPdef, Real.rpow_def_of_pos hN0]
    have h1 := Real.add_one_le_exp (Real.log N * θ)
    have h2 : 1 / θ ≤ Real.log N * θ := by
      have : 1 / θ = (1 / θ ^ 2) * θ := by field_simp
      rw [this]; exact mul_le_mul_of_nonneg_right hlog1 hθ.le
    linarith
  have hlogP : Real.log N ≤ P ^ 3 := by
    have h1 : Real.log N ≤ P / θ := Real.log_le_rpow_div hN0.le hθ
    have h2 : P / θ = P * (1 / θ) := by ring
    have h3 : P * (1 / θ) ≤ P * P := mul_le_mul_of_nonneg_left hPθ hP0.le
    have h4 : P * P ≤ P ^ 3 := by nlinarith
    linarith
  have hP7 : P ^ 7 ≤ N := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ (θ * ((7 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = N := Real.rpow_one _
  set X := (N : ℝ) / P ^ 8 with hXdef
  have hX0 : 0 < X := by positivity
  set Z := ∑ ρ ∈ zerosTo χ (P ^ 10),
    ((mult χ ρ : ℝ) - (if k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0)) *
      X ^ (ρ.re - 1) with hZdef
  have hZ0 : 0 ≤ Z := by
    apply sum_nonneg
    intro ρ hρ
    apply mul_nonneg _ (Real.rpow_nonneg hX0.le _)
    split_ifs with hc
    · have hγ1 := (hγ ⟨hc.1, hc.2.1⟩).2
      have hne : (γ : ℂ) ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have := asm_one_le_mult χ hc.2.1 hne
      rw [hc.2.2]
      have : (1 : ℝ) ≤ mult χ (γ : ℂ) := by exact_mod_cast this
      linarith
    · simp
  have hcoef : ∀ m, ‖corrCoef χ r γ m‖ ≤ 4 := by
    intro m
    by_cases hc : k + 1 = r ∧ χ.LFunction (γ : ℂ) = 0
    · exact norm_corrCoef_le χ r (hγ hc).2.le m
    · have : corrCoef χ r γ m = corrCoef χ 0 0 m := by
        unfold corrCoef
        rw [if_neg hc, if_neg (show ¬ ((k + 1 = 0) ∧ χ.LFunction ((0 : ℝ) : ℂ) = 0) from
          fun h => Nat.succ_ne_zero k h.1)]
      rw [this]
      exact norm_corrCoef_le χ 0 (by norm_num) m
  have hsumle : ∀ b' a' : ℕ, ‖∑ n ∈ Ioc b' a', corrCoef χ r γ n‖ ≤ 4 * ((a' - b' : ℕ) : ℝ) := by
    intro b' a'
    calc _ ≤ ∑ n ∈ Ioc b' a', ‖corrCoef χ r γ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc b' a', (4 : ℝ) := sum_le_sum fun n _ => hcoef n
      _ = 4 * ((a' - b' : ℕ) : ℝ) := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]; ring
  have hcut : 4 * ((N : ℝ) / P ^ 7 + 1) ≤ 8 * ((N : ℝ) / P) / Real.log N * P⁻¹ ^ 3 := by
    have hD : 0 < P ^ 4 * Real.log N := by positivity
    have e1 : 8 * ((N : ℝ) / P) / Real.log N * P⁻¹ ^ 3 = 8 * ((N : ℝ) / (P ^ 4 * Real.log N)) := by
      field_simp
    rw [e1]
    have h1 : (N : ℝ) / P ^ 7 ≤ (N : ℝ) / (P ^ 4 * Real.log N) := by
      apply div_le_div_of_nonneg_left hN0.le hD
      calc P ^ 4 * Real.log N ≤ P ^ 4 * P ^ 3 :=
            mul_le_mul_of_nonneg_left hlogP (by positivity)
        _ = P ^ 7 := by ring
    have h2 : 1 ≤ (N : ℝ) / (P ^ 4 * Real.log N) := by
      rw [le_div_iff₀ hD]
      calc 1 * (P ^ 4 * Real.log N) ≤ P ^ 4 * P ^ 3 := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hlogP (by positivity)
        _ = P ^ 7 := by ring
        _ ≤ N := hP7
    linarith
  have hA0 : 0 ≤ (N : ℝ) / P / Real.log N := by positivity
  have hfin : C * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) + 8 * ((N : ℝ) / P) / Real.log N * P⁻¹ ^ 3
      ≤ (C + 8) * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) := by
    have : 8 * ((N : ℝ) / P) / Real.log N * P⁻¹ ^ 3 ≤
        8 * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : (C + 8) * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) =
        C * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) +
          8 * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) := by ring
    linarith
  have hR0 : 0 ≤ C * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) := by positivity
  by_cases hbig : (N : ℝ) / P ^ 7 ≤ b
  · refine (hN₁ N hN1' k hk χ hχ r γ hγ a b hba ha hab hbig).trans ?_
    have : 0 ≤ 8 * ((N : ℝ) / P) / Real.log N * P⁻¹ ^ 3 := by positivity
    linarith
  · push_neg at hbig
    set m := min a ⌈(N : ℝ) / P ^ 7⌉₊ with hmdef
    have hbm : b ≤ m := by
      apply le_min hba
      have : (b : ℝ) < ⌈(N : ℝ) / P ^ 7⌉₊ := hbig.trans_le (Nat.le_ceil _)
      exact_mod_cast this.le
    have hma : m ≤ a := min_le_left _ _
    rw [← sum_Ioc_consecutive _ hbm hma]
    have h1 : ‖∑ n ∈ Ioc b m, corrCoef χ r γ n‖ ≤ 8 * ((N : ℝ) / P) / Real.log N * P⁻¹ ^ 3 := by
      refine (hsumle b m).trans (le_trans ?_ hcut)
      have hm1 : (m : ℝ) ≤ (N : ℝ) / P ^ 7 + 1 :=
        (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.ceil_lt_add_one (by positivity)).le
      have : ((m - b : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m b
      linarith
    have h2 : ‖∑ n ∈ Ioc m a, corrCoef χ r γ n‖ ≤
        C * ((N : ℝ) / P) / Real.log N * (Z + P⁻¹ ^ 3) := by
      by_cases hma' : m = a
      · rw [hma', Ioc_self, sum_empty, norm_zero]; exact hR0
      · have hmc : m = ⌈(N : ℝ) / P ^ 7⌉₊ := by
          rcases min_choice a ⌈(N : ℝ) / P ^ 7⌉₊ with h | h
          · exact absurd (hmdef.trans h) hma'
          · exact hmdef.trans h
        apply hN₁ N hN1' k hk χ hχ r γ hγ a m hma ha
        · have : (b : ℝ) ≤ m := by exact_mod_cast hbm
          linarith
        · rw [hmc]; exact Nat.le_ceil _
    calc _ ≤ ‖∑ n ∈ Ioc b m, corrCoef χ r γ n‖ + ‖∑ n ∈ Ioc m a, corrCoef χ r γ n‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith

/-- The Gallagher window as an interval sum: `win c (N+1) L m = Σ_{m - L < n ≤ min(m, N)} c n`. -/
theorem win_eq_Ioc (c : ℕ → ℂ) (N L m : ℕ) (hL : 1 ≤ L) :
    LeanLab.PNTPort.Gallagher.win c (N + 1) L m =
      (if L ≤ m then 0 else c 0) + ∑ n ∈ Ioc (m - L) (min m N), c n := by
  unfold LeanLab.PNTPort.Gallagher.win
  by_cases hLm : L ≤ m
  · rw [if_pos hLm, zero_add]
    apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter, mem_range, mem_Ioc]
    omega
  · rw [if_neg hLm]
    have hset : (range (N + 1)).filter (fun n => n ≤ m ∧ m < n + L) =
        insert 0 (Ioc (m - L) (min m N)) := by
      ext n
      simp only [mem_filter, mem_range, mem_insert, mem_Ioc]
      omega
    have h0 : (0 : ℕ) ∉ Ioc (m - L) (min m N) := by
      simp only [mem_Ioc]
      omega
    rw [hset, sum_insert h0]

/-- `corrCoef` vanishes at `0`: `0` is not prime and the two corrections need `1 < m`. -/
lemma asm_corrCoef_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℕ) (γ : ℝ) :
    corrCoef χ r γ 0 = 0 := by
  simp [corrCoef, Nat.not_prime_zero]

/-- Membership in `zerosTo`, from its definition. -/
lemma asm_mem_zerosTo {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosTo χ T) : ρ ∈ Zall χ ∧ |ρ.im| ≤ T := by
  unfold zerosTo at hρ
  split_ifs at hρ with h
  · exact h.mem_toFinset.1 hρ
  · simp at hρ

/-- There are at most `q` characters mod `q`, Mathlib's count `φ(q)`. -/
lemma asm_card_prim_le (k : ℕ) :
    ((univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive)).card
      ≤ k + 1 := by
  calc _ ≤ (univ : Finset (DirichletCharacter ℂ (k + 1))).card := card_filter_le _ _
    _ = Nat.card (DirichletCharacter ℂ (k + 1)) := by rw [card_univ, Nat.card_eq_fintype_card]
    _ = (k + 1).totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
    _ ≤ k + 1 := Nat.totient_le _

/-- The squared window sum from a uniform window bound: every Gallagher window with `f 0 = 0`
is an interval sum over `(b, a]` with `a ≤ N` and `a - b ≤ L`, by `win_eq_Ioc`. -/
lemma asm_win_sq_sum_le (f : ℕ → ℂ) (hf0 : f 0 = 0) (N L : ℕ) (hL : 1 ≤ L) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b a : ℕ, b ≤ a → a ≤ N → a - b ≤ L → ‖∑ n ∈ Ioc b a, f n‖ ≤ B) :
    ∑ m ∈ range (N + 1 + L), ‖LeanLab.PNTPort.Gallagher.win f (N + 1) L m‖ ^ 2
      ≤ ((N : ℝ) + 1 + L) * B ^ 2 := by
  calc _ ≤ ∑ m ∈ range (N + 1 + L), B ^ 2 := by
        apply sum_le_sum
        intro m _
        rw [win_eq_Ioc f N L m hL, hf0, ite_self, zero_add]
        have h : ‖∑ n ∈ Ioc (m - L) (min m N), f n‖ ≤ B := by
          by_cases hc : m - L ≤ min m N
          · exact hB _ _ hc (min_le_right _ _) (by omega)
          · rw [Finset.Ioc_eq_empty_of_le (by omega)]
            simpa using hB0
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ((N : ℝ) + 1 + L) * B ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The normalisation arithmetic: with `x = N/(2P) ≥ 1`, `L = ⌊x⌋`, `1 ≤ P` and `4 ≤ N`,
`π/(2L) * sqrt(N + 1 + L) * (N/P) ≤ 4π sqrt N`. -/
lemma asm_norm_factor_le {N P : ℝ} (hN : 4 ≤ N) (hP : 1 ≤ P) (hx : 1 ≤ N / (2 * P)) :
    Real.pi / (2 * ⌊N / (2 * P)⌋₊) * Real.sqrt (N + 1 + ⌊N / (2 * P)⌋₊) * (N / P)
      ≤ 4 * Real.pi * Real.sqrt N := by
  set x := N / (2 * P) with hxdef
  set L : ℝ := (⌊x⌋₊ : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.floor_pos.mpr hx))
  have hLx : L ≤ x := Nat.floor_le (by linarith)
  have hxL : x < L + 1 := Nat.lt_floor_add_one x
  have h2L : x ≤ 2 * L := by linarith
  have hP0 : 0 < P := by linarith
  have hNP : N / P = 2 * x := by rw [hxdef]; field_simp
  have hxN : x ≤ N := by
    rw [hxdef, div_le_iff₀ (by positivity)]; nlinarith
  have hsq : Real.sqrt (N + 1 + L) ≤ 2 * Real.sqrt N := by
    rw [show 2 * Real.sqrt N = Real.sqrt (4 * N) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hL0 : 0 < L := by linarith
  rw [hNP]
  have hpi := Real.pi_pos
  have hs0 := Real.sqrt_nonneg (N + 1 + L)
  have hfac : Real.pi / (2 * L) * (2 * x) ≤ 2 * Real.pi := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  calc Real.pi / (2 * L) * Real.sqrt (N + 1 + L) * (2 * x)
      = Real.pi / (2 * L) * (2 * x) * Real.sqrt (N + 1 + L) := by ring
    _ ≤ 2 * Real.pi * (2 * Real.sqrt N) :=
        mul_le_mul hfac hsq hs0 (by positivity)
    _ = 4 * Real.pi * Real.sqrt N := by ring

/-- Per character and summed over characters: a uniform window bound
`C₁ (N/P)/log N * W(k, χ)` for windows of length at most `N/(2P)` inside `[0, N]` gives the
Gallagher display 14 sum at most `4π C₁ (sqrt N / log N) Σ W`. Elementary, from `win_eq_Ioc`. -/
lemma asm_mean_core (N : ℕ) (θ C₁ : ℝ) (hN : 4 ≤ (N : ℝ)) (hP : 1 ≤ (N : ℝ) ^ θ)
    (hx : 1 ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ)) (hlog : 0 < Real.log N) (hC₁ : 0 ≤ C₁)
    (f : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℕ → ℂ)
    (W : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℝ) (hW0 : ∀ k χ, 0 ≤ W k χ)
    (hf0 : ∀ k χ, f k χ 0 = 0)
    (hwin : ∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
      ∀ a b : ℕ, b ≤ a → a ≤ N → ((a : ℝ) - b) ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ) →
        ‖∑ n ∈ Ioc b a, f k χ n‖ ≤ C₁ * ((N : ℝ) / (N : ℝ) ^ θ) / Real.log N * W k χ) :
    ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        Real.pi / (2 * ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊) *
          Real.sqrt (∑ m ∈ range (N + 1 + ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊),
            ‖LeanLab.PNTPort.Gallagher.win (f k χ) (N + 1)
              ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊ m‖ ^ 2)
      ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) *
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            W k χ := by
  set P := (N : ℝ) ^ θ with hPdef
  set L := ⌊(N : ℝ) / (2 * P)⌋₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.floor_pos.mpr hx))
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  rw [mem_range] at hk
  rw [mul_sum]
  apply sum_le_sum
  intro χ hχ
  have hprim := (mem_filter.mp hχ).2
  set B := C₁ * ((N : ℝ) / P) / Real.log N * W k χ with hBdef
  have hP0 : 0 < P := by linarith
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := hW0 k χ
    positivity
  have hsq := asm_win_sq_sum_le (f k χ) (hf0 k χ) N L hL1 hB0 (fun b a hba haN hab => by
    apply hwin k hk χ hprim a b hba haN
    rw [← Nat.cast_sub hba]
    calc ((a - b : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hab
      _ ≤ _ := Nat.floor_le (by positivity))
  have hfac := asm_norm_factor_le hN hP hx
  have hpi := Real.pi_pos
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hD : 0 ≤ C₁ * W k χ / Real.log N := by
    have := hW0 k χ
    positivity
  calc Real.pi / (2 * (L : ℝ)) * Real.sqrt (∑ m ∈ range (N + 1 + L),
          ‖LeanLab.PNTPort.Gallagher.win (f k χ) (N + 1) L m‖ ^ 2)
      ≤ Real.pi / (2 * (L : ℝ)) * Real.sqrt (((N : ℝ) + 1 + L) * B ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (by positivity)
    _ = Real.pi / (2 * (L : ℝ)) * Real.sqrt ((N : ℝ) + 1 + L) * ((N : ℝ) / P) *
          (C₁ * W k χ / Real.log N) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB0, hBdef]
        ring
    _ ≤ 4 * Real.pi * Real.sqrt N * (C₁ * W k χ / Real.log N) :=
        mul_le_mul_of_nonneg_right hfac hD
    _ = 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * W k χ := by ring

/-- The zeros with `Re ρ ≤ 0` in `zerosTo` contribute at most `X⁻¹`: by `zero_left_strip` only
`ρ = 0` occurs, simple by `mult_zero_le_one`; Davenport ch. 9. -/
lemma asm_zsum_split {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (T X : ℝ) (hX : 0 < X) (w : ℂ → ℝ) (hw0 : ∀ ρ, 0 ≤ w ρ) (hw : ∀ ρ, w ρ ≤ mult χ ρ) :
    ∑ ρ ∈ zerosTo χ T, w ρ * X ^ (ρ.re - 1) ≤
      ∑ ρ ∈ (zerosTo χ T).filter (fun ρ => 0 < ρ.re), w ρ * X ^ (ρ.re - 1) + X⁻¹ := by
  rw [← sum_filter_add_sum_filter_not (zerosTo χ T) (fun ρ => 0 < ρ.re)]
  gcongr
  have hsub : (zerosTo χ T).filter (fun ρ => ¬ 0 < ρ.re) ⊆ {0} := by
    intro ρ hρ
    obtain ⟨hρz, hre⟩ := mem_filter.mp hρ
    have hZ := (asm_mem_zerosTo hρz).1
    rw [mem_singleton]
    exact zero_left_strip hχ hZ.1 hZ.2.1 (not_lt.mp hre)
  calc _ ≤ ∑ ρ ∈ ({0} : Finset ℂ), w ρ * X ^ (ρ.re - 1) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => mul_nonneg (hw0 ρ)
          (Real.rpow_nonneg hX.le _))
    _ = w 0 * X⁻¹ := by simp [Real.rpow_neg_one]
    _ ≤ 1 * X⁻¹ := by
        gcongr
        exact (hw 0).trans (by exact_mod_cast mult_zero_le_one hχ)
    _ = X⁻¹ := one_mul _

/-- Gallagher 1975 p.131 display 14 without exceptional character, the content of
`Decomp486c.short_interval_mean_decay` for any strip constant `b > 0`. -/
theorem mean_decay_nonexceptional (b : ℝ) (hb : 0 < b) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
          ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 →
            ρ.re < 1 - b / Real.log (((N : ℝ) ^ θ) ^ 5)) →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊) *
              Real.sqrt (∑ m ∈ range (N + 1 + ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊),
                ‖LeanLab.PNTPort.Gallagher.win (corrCoef χ 0 0) (N + 1)
                  ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊ m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨C₁, θ₁, hC₁, hθ₁, hW⟩ := window_corr_bound
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hZ⟩ := zero_sum_density_layer b hb
  refine ⟨c₂, 4 * Real.pi * C₁ * (C₂ + 2) + 1, min (min θ₁ θ₂) (1 / 11), hc₂,
    by positivity, lt_min (lt_min hθ₁ hθ₂) (by norm_num),
    (min_le_right _ _).trans (by norm_num), ?_⟩
  intro θ hθ hθ0
  have hθa : θ ≤ θ₁ := hθ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθb : θ ≤ θ₂ := hθ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθc : θ ≤ 1 / 11 := hθ0.trans (min_le_right _ _)
  obtain ⟨NW, hNW⟩ := hW θ hθ hθa
  obtain ⟨NZ, hNZ⟩ := hZ θ hθ hθb
  refine ⟨max (max NW NZ) (max 4 ⌈Real.exp (c₂ / θ ^ 2)⌉₊), ?_⟩
  intro N hN hgap
  have hNW' : NW ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNZ' : NZ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4 : (4 : ℝ) ≤ N := by
    have : 4 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact_mod_cast this
  have hNe : Real.exp (c₂ / θ ^ 2) ≤ N := by
    have : ⌈Real.exp (c₂ / θ ^ 2)⌉₊ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogc : c₂ / θ ^ 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set P := (N : ℝ) ^ θ with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 hθ.le
  have hP0 : 0 < P := by linarith
  -- `2P ≤ N`
  have hPs : P ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsN : 2 ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN4
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hx : 1 ≤ (N : ℝ) / (2 * P) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `P^3 ≤ X = N/P^8`
  set X := (N : ℝ) / P ^ 8 with hXdef
  have hP11 : P ^ 11 ≤ N := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ (θ * ((11 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = N := Real.rpow_one _
  have hX3 : P ^ 3 ≤ X := by
    rw [hXdef, le_div_iff₀ (by positivity)]
    calc P ^ 3 * P ^ 8 = P ^ 11 := by ring
      _ ≤ (N : ℝ) := hP11
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX3
  have hXinv : X⁻¹ ≤ P⁻¹ ^ 3 := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) hX3
  -- `P⁻¹ ≤ e^(-c/θ)`
  have hPe : P⁻¹ ≤ Real.exp (-c₂ / θ) := by
    rw [hPdef, Real.rpow_def_of_pos hN0, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have : c₂ / θ ≤ Real.log N * θ := by
      have h1 : c₂ / θ = θ * (c₂ / θ ^ 2) := by field_simp
      rw [h1, mul_comm (Real.log N)]
      exact mul_le_mul_of_nonneg_left hlogc hθ.le
    rw [neg_div]; linarith
  -- the window weights
  let W : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℝ := fun k χ =>
    ∑ ρ ∈ zerosTo χ (P ^ 10), (mult χ ρ : ℝ) * X ^ (ρ.re - 1) + P⁻¹ ^ 3
  have hW0 : ∀ k χ, 0 ≤ W k χ := fun k χ => add_nonneg
    (sum_nonneg fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _))
    (by positivity)
  have hcore := asm_mean_core N θ C₁ hN4 hP1 hx hlog hC₁ (fun k χ => corrCoef χ 0 0) W hW0
    (fun k χ => asm_corrCoef_zero χ 0 0) (by
      intro k hk χ hχ a b hba haN hab
      have hk0 : ¬ (k + 1 = 0) := by omega
      have h := hNW N hNW' k hk χ hχ 0 0 (fun h => absurd h.1 hk0) a b hba (by omega) hab
      simpa [hk0, W] using h)
  refine hcore.trans ?_
  -- the sum of the weights
  let S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ := fun k χ =>
    if k < ⌊P⌋₊ ∧ χ.IsPrimitive then (zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re) else ∅
  have hS : ∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ P ^ 10 ∧ (|ρ.im| ≤ P ^ 5 → ρ.re < 1 - b / Real.log (P ^ 5)) := by
    intro k χ ρ hρ
    simp only [S] at hρ
    split_ifs at hρ with hc
    · obtain ⟨hρz, hre⟩ := mem_filter.mp hρ
      obtain ⟨⟨hz, _, hne⟩, him⟩ := asm_mem_zerosTo hρz
      refine ⟨hz, hre, ?_, him, fun h5 => hgap k hc.1 χ hc.2 ρ hz h5⟩
      by_contra h1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne) (not_lt.mp h1) hz
    · simp at hρ
  have hZb := hNZ N hNZ' S hS
  have hsumZ : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        W k χ ≤
      ∑ k ∈ range ⌊P⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          (∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) + 2 * P⁻¹ ^ 3) := by
    apply sum_le_sum
    intro k hk
    apply sum_le_sum
    intro χ hχ
    have hprim := (mem_filter.mp hχ).2
    have hSe : S k χ = (zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re) := by
      simp only [S]; rw [if_pos ⟨mem_range.mp hk, hprim⟩]
    rw [hSe]
    have := asm_zsum_split hprim (P ^ 10) X hX0 (fun ρ => (mult χ ρ : ℝ))
      (fun ρ => Nat.cast_nonneg _) (fun ρ => le_rfl)
    simp only [W]
    linarith
  have hcount : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (2 * P⁻¹ ^ 3) ≤ 2 * Real.exp (-c₂ / θ) := by
    have hK : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le hP0.le
    calc _ = ∑ k ∈ range ⌊P⌋₊,
          (((univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive)).card : ℝ) * (2 * P⁻¹ ^ 3) := by
          apply sum_congr rfl; intro k _; rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ range ⌊P⌋₊, P * (2 * P⁻¹ ^ 3) := by
          apply sum_le_sum; intro k hk
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h1 := asm_card_prim_le k
          have h2 : k + 1 ≤ ⌊P⌋₊ := mem_range.mp hk
          calc (_ : ℝ) ≤ ((⌊P⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
            _ ≤ P := hK
      _ = (⌊P⌋₊ : ℝ) * (P * (2 * P⁻¹ ^ 3)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ P * (P * (2 * P⁻¹ ^ 3)) := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = 2 * P⁻¹ := by field_simp
      _ ≤ 2 * Real.exp (-c₂ / θ) := by linarith
  have hZb' : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤ C₂ * Real.exp (-c₂ / θ) := hZb
  have htot : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        W k χ ≤ (C₂ + 2) * Real.exp (-c₂ / θ) := by
    refine hsumZ.trans ?_
    calc _ = ∑ k ∈ range ⌊P⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) +
          ∑ k ∈ range ⌊P⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            (2 * P⁻¹ ^ 3) := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro k _
          rw [← sum_add_distrib]
      _ ≤ C₂ * Real.exp (-c₂ / θ) + 2 * Real.exp (-c₂ / θ) := add_le_add hZb' hcount
      _ = (C₂ + 2) * Real.exp (-c₂ / θ) := by ring
  have hA : 0 ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) := by positivity
  have hE : 0 ≤ Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N) := by positivity
  calc 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * _
      ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * ((C₂ + 2) * Real.exp (-c₂ / θ)) :=
        mul_le_mul_of_nonneg_left htot hA
    _ = (4 * Real.pi * C₁ * (C₂ + 2)) * (Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N)) := by
        ring
    _ ≤ (4 * Real.pi * C₁ * (C₂ + 2) + 1) * (Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N)) :=
        mul_le_mul_of_nonneg_right (by linarith) hE
    _ = _ := by ring

/-- The real zeros of the exceptional character in the strip are finitely many, so a largest
one exists. -/
theorem exists_max_real_zero {T : ℝ} (hT : 2 ≤ T) (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1))
    (hx : x ∈ LeanLab.Linnik.Decomp1532b.excSet LeanLab.Linnik.Decomp466a.exceptionalStrip T) :
    ∃ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 ∧
      1 - LeanLab.Linnik.Decomp466a.exceptionalStrip / Real.log T ≤ γ ∧ γ < 1 ∧
      ∀ γ' : ℝ, x.2.LFunction (γ' : ℂ) = 0 →
        1 - LeanLab.Linnik.Decomp466a.exceptionalStrip / Real.log T ≤ γ' → γ' < 1 → γ' ≤ γ := by
  let br := Classical.choose LeanLab.Linnik.Decomp1532b.page_real
  have hb : LeanLab.Linnik.Decomp466a.exceptionalStrip ≤ br :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hxr := LeanLab.Linnik.Decomp1532b.excSet_mono hb hT hx
  have hp := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_real).2 T hT x hxr
  obtain ⟨c, hc, hs⟩ := LeanLab.Linnik.Decomp1532b.siegel 1 zero_lt_one
  set lo := 1 - LeanLab.Linnik.Decomp466a.exceptionalStrip / Real.log T with hlo
  set hi := 1 - c * ((x.1 : ℝ) + 1) ^ (-(1 : ℝ)) with hhi_def
  have hpos : 0 < c * ((x.1 : ℝ) + 1) ^ (-(1 : ℝ)) :=
    mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hhi : hi < 1 := by linarith
  have hbd : ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 → γ ≤ hi :=
    fun γ h => hs x.1 x.2 hx.2.1 hp.1 γ h
  -- a real zero in the strip, as in `Decomp486c.exceptional_real_zero`
  obtain ⟨γ0, h0z, h0lo⟩ : ∃ γ0 : ℝ, x.2.LFunction (γ0 : ℂ) = 0 ∧ lo ≤ γ0 := by
    obtain ⟨ρ, hz, hβ, ht⟩ := hx.2.2
    have hβr : 1 - br / Real.log T ≤ ρ.re := by
      have hd := div_le_div_of_nonneg_right hb
        (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
      linarith
    have him := hp.2 ρ hz hβr ht
    have he : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
    exact ⟨ρ.re, by rwa [he], hβ⟩
  let f : ℝ → ℂ := fun γ => x.2.LFunction (γ : ℂ)
  let Z : Set ℝ := Set.Icc lo hi ∩ f ⁻¹' {0}
  have hcont : ContinuousOn f (Set.Icc lo hi) := by
    intro γ hγ
    have hne : (γ : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hγ.2]
    exact ((DirichletCharacter.differentiableAt_LFunction _ _ (Or.inl hne)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hZc : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZk : IsCompact Z := isCompact_Icc.of_isClosed_subset hZc Set.inter_subset_left
  have hne : Z.Nonempty := ⟨γ0, ⟨h0lo, hbd _ h0z⟩, h0z⟩
  have hm := hZk.sSup_mem hne
  refine ⟨sSup Z, hm.2, hm.1.1, lt_of_le_of_lt hm.1.2 hhi, ?_⟩
  intro γ' hz' hlo' _
  exact le_csSup hZk.bddAbove ⟨⟨hlo', hbd _ hz'⟩, hz'⟩

/-- Gallagher 1975 p.131, the paragraph after display 14, with `γ` the largest real zero of the
exceptional character in the strip. This is `Decomp486c.short_interval_mean_decay_exceptional`
with the extra hypothesis that `γ` is the largest such zero; see the plan note for why the
statement for every real zero in the strip is not provable from Page's theorem. -/
theorem mean_decay_exceptional_max :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ LeanLab.Linnik.Decomp1532b.excSet LeanLab.Linnik.Decomp466a.exceptionalStrip
            (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - LeanLab.Linnik.Decomp466a.exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ →
            γ < 1 →
          (∀ γ' : ℝ, x.2.LFunction (γ' : ℂ) = 0 →
            1 - LeanLab.Linnik.Decomp466a.exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ' →
            γ' < 1 → γ' ≤ γ) →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊) *
              Real.sqrt (∑ m ∈ range (N + 1 + ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊),
                ‖LeanLab.PNTPort.Gallagher.win (corrCoef χ (x.1 + 1) γ) (N + 1)
                  ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊ m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨C₁, θ₁, hC₁, hθ₁, hW⟩ := window_corr_bound
  obtain ⟨cp, hcp, hpage⟩ := page_one_zero
  set es := LeanLab.Linnik.Decomp466a.exceptionalStrip with hes
  have hes0 : 0 < es := LeanLab.Linnik.Decomp466a.exceptionalStrip_pos
  set b := min es cp with hbdef
  have hb : 0 < b := lt_min hes0 hcp
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hZ⟩ := zero_sum_density_layer b hb
  refine ⟨c₂, 4 * Real.pi * C₁ * (C₂ + 2) + 1, min (min θ₁ θ₂) (1 / 11), hc₂,
    by positivity, lt_min (lt_min hθ₁ hθ₂) (by norm_num),
    (min_le_right _ _).trans (by norm_num), ?_⟩
  intro θ hθ hθ0
  have hθa : θ ≤ θ₁ := hθ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθb : θ ≤ θ₂ := hθ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθc : θ ≤ 1 / 11 := hθ0.trans (min_le_right _ _)
  obtain ⟨NW, hNW⟩ := hW θ hθ hθa
  obtain ⟨NZ, hNZ⟩ := hZ θ hθ hθb
  refine ⟨max (max NW NZ) (max 4 (max ⌈Real.exp (c₂ / θ ^ 2)⌉₊ ⌈Real.exp ((es + 1) / θ)⌉₊)), ?_⟩
  intro N hN x hx hxP γ hγz hγlo hγ1 hγmax
  have hNW' : NW ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNZ' : NZ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4 : (4 : ℝ) ≤ N := by
    have : 4 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact_mod_cast this
  have hNe : Real.exp (c₂ / θ ^ 2) ≤ N := by
    have : ⌈Real.exp (c₂ / θ ^ 2)⌉₊ ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hNe' : Real.exp ((es + 1) / θ) ≤ N := by
    have : ⌈Real.exp ((es + 1) / θ)⌉₊ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogc : c₂ / θ ^ 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hloge : (es + 1) / θ ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe'
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set P := (N : ℝ) ^ θ with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 hθ.le
  have hP0 : 0 < P := by linarith
  have hlogP : Real.log P = θ * Real.log N := by rw [hPdef, Real.log_rpow hN0]
  have hlogP' : es + 1 ≤ Real.log P := by
    rw [hlogP]
    have : es + 1 = θ * ((es + 1) / θ) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hloge hθ.le
  set T := P ^ 5 with hTdef
  have hlogT : Real.log T = 5 * Real.log P := by rw [hTdef, Real.log_pow]; push_cast; ring
  have hlogT0 : 0 < Real.log T := by rw [hlogT]; linarith
  have hesT : es / Real.log T < 1 := by
    rw [div_lt_one hlogT0, hlogT]; linarith
  have hP2 : 2 ≤ P := by
    have h1 : Real.exp 1 ≤ P := by
      rw [← Real.exp_log hP0]; exact Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  have hPT : P ≤ T := by
    rw [hTdef]
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hT2 : 2 ≤ T := hP2.trans hPT
  have hγpos : 0 < γ := by linarith
  -- `2P ≤ N`
  have hPs : P ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsN : 2 ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN4
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hx2 : 1 ≤ (N : ℝ) / (2 * P) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `P^3 ≤ X = N/P^8`
  set X := (N : ℝ) / P ^ 8 with hXdef
  have hP11 : P ^ 11 ≤ N := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ (θ * ((11 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = N := Real.rpow_one _
  have hX3 : P ^ 3 ≤ X := by
    rw [hXdef, le_div_iff₀ (by positivity)]
    calc P ^ 3 * P ^ 8 = P ^ 11 := by ring
      _ ≤ (N : ℝ) := hP11
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX3
  have hXinv : X⁻¹ ≤ P⁻¹ ^ 3 := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) hX3
  have hPe : P⁻¹ ≤ Real.exp (-c₂ / θ) := by
    rw [hPdef, Real.rpow_def_of_pos hN0, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have : c₂ / θ ≤ Real.log N * θ := by
      have h1 : c₂ / θ = θ * (c₂ / θ ^ 2) := by field_simp
      rw [h1, mul_comm (Real.log N)]
      exact mul_le_mul_of_nonneg_left hlogc hθ.le
    rw [neg_div]; linarith
  -- the weights, with the exceptional zero removed once
  let w : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℂ → ℝ := fun k χ ρ =>
    max ((mult χ ρ : ℝ) -
      (if k + 1 = x.1 + 1 ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0)) 0
  have hw0 : ∀ k χ ρ, 0 ≤ w k χ ρ := fun k χ ρ => le_max_right _ _
  have hwm : ∀ k χ ρ, w k χ ρ ≤ mult χ ρ := fun k χ ρ => by
    apply max_le _ (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ (if k + 1 = x.1 + 1 ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0) := by
      split_ifs <;> norm_num
    linarith
  let W : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℝ := fun k χ =>
    ∑ ρ ∈ zerosTo χ (P ^ 10), w k χ ρ * X ^ (ρ.re - 1) + P⁻¹ ^ 3
  have hW0 : ∀ k χ, 0 ≤ W k χ := fun k χ => add_nonneg
    (sum_nonneg fun ρ _ => mul_nonneg (hw0 k χ ρ) (Real.rpow_nonneg hX0.le _))
    (by positivity)
  have hcore := asm_mean_core N θ C₁ hN4 hP1 hx2 hlog hC₁
    (fun k χ => corrCoef χ (x.1 + 1) γ) W hW0
    (fun k χ => asm_corrCoef_zero χ _ _) (by
      intro k hk χ hχ a b' hba haN hab
      have h := hNW N hNW' k hk χ hχ (x.1 + 1) γ (fun _ => ⟨hγpos, hγ1⟩) a b' hba (by omega) hab
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact add_le_add (sum_le_sum fun ρ _ =>
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hX0.le _)) le_rfl)
  refine hcore.trans ?_
  -- the zero sets for the density layer
  let S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ := fun k χ =>
    if k < ⌊P⌋₊ ∧ χ.IsPrimitive then
      ((zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re)).filter (fun ρ => 0 < w k χ ρ) else ∅
  have hxprim := hx.2.1
  have hxq : ((x.1 + 1 : ℕ) : ℝ) ≤ T := hxP.trans hPT
  -- Page: the only zero near `1` is `γ`
  have hnear : ∀ ρ : ℂ, x.2.LFunction ρ = 0 → ρ ≠ 1 → |ρ.im| ≤ T →
      1 - b / Real.log T ≤ ρ.re → ρ.re < 1 → (mult x.2 ρ : ℝ) -
        (if ρ = (γ : ℂ) then 1 else 0) ≤ 0 := by
    intro ρ hz hne him hge hlt1
    have hbes : b / Real.log T ≤ es / Real.log T :=
      div_le_div_of_nonneg_right (min_le_left _ _) hlogT0.le
    have hbcp : b / Real.log T ≤ cp / Real.log T :=
      div_le_div_of_nonneg_right (min_le_right _ _) hlogT0.le
    let br := Classical.choose LeanLab.Linnik.Decomp1532b.page_real
    have hbr : es ≤ br := (min_le_right _ _).trans (min_le_left _ _)
    have hxr := LeanLab.Linnik.Decomp1532b.excSet_mono hbr hT2 hx
    have hp := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_real).2 T hT2 x hxr
    have hbrT : es / Real.log T ≤ br / Real.log T :=
      div_le_div_of_nonneg_right hbr hlogT0.le
    have him0 := hp.2 ρ hz (by linarith) him
    have hρr : ((ρ.re : ℝ) : ℂ) = ρ := by apply Complex.ext <;> simp [him0]
    have hle : ρ.re ≤ γ := hγmax ρ.re (by rw [hρr]; exact hz) (by linarith) hlt1
    have hγne : (γ : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hγcond : x.2.LFunction (γ : ℂ) = 0 ∧ 1 - cp / Real.log T ≤ (γ : ℂ).re ∧
        |(γ : ℂ).im| ≤ T ∧ (γ : ℂ) ≠ 1 := by
      refine ⟨hγz, ?_, ?_, hγne⟩
      · simp only [Complex.ofReal_re]; linarith
      · simp only [Complex.ofReal_im, abs_zero]; linarith
    by_cases hργ : ρ = (γ : ℂ)
    · rw [if_pos hργ]
      have h1 := hpage T hT2 (x.1 + 1) x.2 hxprim hxq {(γ : ℂ)}
        (by intro σ hσ; rw [mem_singleton] at hσ; subst hσ; exact hγcond)
      rw [sum_singleton] at h1
      rw [hργ]
      have : (mult x.2 (γ : ℂ) : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith
    · rw [if_neg hργ]
      have h1 := hpage T hT2 (x.1 + 1) x.2 hxprim hxq {ρ, (γ : ℂ)}
        (by
          intro σ hσ
          rw [mem_insert, mem_singleton] at hσ
          rcases hσ with rfl | rfl
          · exact ⟨hz, by linarith, him, hne⟩
          · exact hγcond)
      rw [sum_pair hργ] at h1
      have h2 := asm_one_le_mult x.2 hγz hγne
      have : mult x.2 ρ = 0 := by omega
      rw [this]; simp
  have hS : ∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ P ^ 10 ∧ (|ρ.im| ≤ P ^ 5 → ρ.re < 1 - b / Real.log (P ^ 5)) := by
    intro k χ ρ hρ
    simp only [S] at hρ
    split_ifs at hρ with hc
    · obtain ⟨hρ1, hwpos⟩ := mem_filter.mp hρ
      obtain ⟨hρz, hre⟩ := mem_filter.mp hρ1
      obtain ⟨⟨hz, _, hne⟩, him⟩ := asm_mem_zerosTo hρz
      have hlt1 : ρ.re < 1 := by
        by_contra h1
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne) (not_lt.mp h1) hz
      refine ⟨hz, hre, hlt1, him, fun h5 => ?_⟩
      by_contra hge
      push_neg at hge
      -- `(k, χ)` is exceptional, hence equal to `x`
      have hbes : b / Real.log T ≤ es / Real.log T :=
        div_le_div_of_nonneg_right (min_le_left _ _) hlogT0.le
      have hkT : ((k : ℝ) + 1) ≤ T := by
        have h1 : k + 1 ≤ ⌊P⌋₊ := hc.1
        have h2 : ((k + 1 : ℕ) : ℝ) ≤ P := (Nat.cast_le.mpr h1).trans (Nat.floor_le hP0.le)
        push_cast at h2; linarith
      have hmem : (⟨k, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ∈
          LeanLab.Linnik.Decomp1532b.excSet es T :=
        ⟨hkT, hc.2, ρ, hz, by linarith, h5⟩
      let bs := Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton
      have hbs : es ≤ bs := (min_le_right _ _).trans (min_le_right _ _)
      have hsub := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton).2 T hT2
      have heq := hsub (LeanLab.Linnik.Decomp1532b.excSet_mono hbs hT2 hmem)
        (LeanLab.Linnik.Decomp1532b.excSet_mono hbs hT2 hx)
      obtain ⟨x1, x2⟩ := x
      obtain ⟨rfl, hχ⟩ := Sigma.mk.inj_iff.mp heq
      have hχ' : χ = x2 := eq_of_heq hχ
      subst hχ'
      have hn := hnear ρ hz hne h5 hge hlt1
      have hwle : w k χ ρ ≤ 0 := by
        apply max_le _ le_rfl
        simp only at hn ⊢
        by_cases hργ : ρ = (γ : ℂ)
        · rw [if_pos (by simp [hγz, hργ])]; rw [if_pos hργ] at hn; exact hn
        · rw [if_neg (fun h => hργ h.2.2)]; rw [if_neg hργ] at hn; exact hn
      linarith
    · simp at hρ
  have hZb := hNZ N hNZ' S hS
  have hZb' : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤ C₂ * Real.exp (-c₂ / θ) := hZb
  have hsumZ : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        W k χ ≤
      ∑ k ∈ range ⌊P⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          (∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) + 2 * P⁻¹ ^ 3) := by
    apply sum_le_sum
    intro k hk
    apply sum_le_sum
    intro χ hχ
    have hprim := (mem_filter.mp hχ).2
    have hSe : S k χ = ((zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re)).filter
        (fun ρ => 0 < w k χ ρ) := by
      simp only [S]; rw [if_pos ⟨mem_range.mp hk, hprim⟩]
    have h1 := asm_zsum_split hprim (P ^ 10) X hX0 (w k χ) (hw0 k χ) (hwm k χ)
    have h2 : ∑ ρ ∈ (zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re), w k χ ρ * X ^ (ρ.re - 1)
        ≤ ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) := by
      rw [hSe]
      calc _ = ∑ ρ ∈ ((zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re)).filter
            (fun ρ => 0 < w k χ ρ), w k χ ρ * X ^ (ρ.re - 1) :=
            (sum_filter_of_ne (fun ρ _ hne => by
              rcases (hw0 k χ ρ).lt_or_eq with h | h
              · exact h
              · exact absurd (by rw [← h, zero_mul]) hne)).symm
        _ ≤ _ := sum_le_sum fun ρ _ =>
            mul_le_mul_of_nonneg_right (hwm k χ ρ) (Real.rpow_nonneg hX0.le _)
    simp only [W]
    linarith
  have hcount : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (2 * P⁻¹ ^ 3) ≤ 2 * Real.exp (-c₂ / θ) := by
    have hK : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le hP0.le
    calc _ = ∑ k ∈ range ⌊P⌋₊,
          (((univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive)).card : ℝ) * (2 * P⁻¹ ^ 3) := by
          apply sum_congr rfl; intro k _; rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ range ⌊P⌋₊, P * (2 * P⁻¹ ^ 3) := by
          apply sum_le_sum; intro k hk
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h1 := asm_card_prim_le k
          have h2 : k + 1 ≤ ⌊P⌋₊ := mem_range.mp hk
          calc (_ : ℝ) ≤ ((⌊P⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
            _ ≤ P := hK
      _ = (⌊P⌋₊ : ℝ) * (P * (2 * P⁻¹ ^ 3)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ P * (P * (2 * P⁻¹ ^ 3)) := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = 2 * P⁻¹ := by field_simp
      _ ≤ 2 * Real.exp (-c₂ / θ) := by linarith
  have htot : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        W k χ ≤ (C₂ + 2) * Real.exp (-c₂ / θ) := by
    refine hsumZ.trans ?_
    calc _ = ∑ k ∈ range ⌊P⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) +
          ∑ k ∈ range ⌊P⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            (2 * P⁻¹ ^ 3) := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro k _
          rw [← sum_add_distrib]
      _ ≤ C₂ * Real.exp (-c₂ / θ) + 2 * Real.exp (-c₂ / θ) := add_le_add hZb' hcount
      _ = (C₂ + 2) * Real.exp (-c₂ / θ) := by ring
  have hA : 0 ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) := by positivity
  have hE : 0 ≤ Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N) := by positivity
  calc 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * _
      ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * ((C₂ + 2) * Real.exp (-c₂ / θ)) :=
        mul_le_mul_of_nonneg_left htot hA
    _ = (4 * Real.pi * C₁ * (C₂ + 2)) * (Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N)) := by
        ring
    _ ≤ (4 * Real.pi * C₁ * (C₂ + 2) + 1) * (Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N)) :=
        mul_le_mul_of_nonneg_right (by linarith) hE
    _ = _ := by ring


end LeanLab.Linnik.ExplicitFormula
