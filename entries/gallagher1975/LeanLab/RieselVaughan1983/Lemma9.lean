module

public import LeanLab.RieselVaughan1983.Section9
public import LeanLab.RieselVaughan1983.Lemma9Calc

/-!
P0032 Riesel-Vaughan 1983, Lemma 9, pages 60-61: with `K = 200`, `y = x/202`, `log y > 350`,
`Ψ ≤ (N(x) - N(y)) 8Cy/((log(y/2))(8.3 + log(y/2)))`, CONDITIONAL ON Lemma 5 at the row
`L = 60`, `A = 8.3` with `a = -1`, `b = n`, over closed intervals.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.RieselVaughan1983
open LeanLab.SchnirelmannConstant

/-- Lemma 5, p. 53, CITED, the case used in Lemma 9: `a = -1`, `b = n`, an interval `[c, c + ℓ]`
of length `ℓ ≥ e^60`, `A = 8.3`; `p ≤ n` is kept so that `n - p` is a natural number, which
only makes the count smaller. -/
def Lemma5Neg : Prop :=
  ∀ ℓ : ℝ, Real.exp 60 ≤ ℓ → ∀ (c : ℝ) (n : ℕ), 0 < n →
    (#((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧ c ≤ p ∧ (p : ℝ) ≤ c + ℓ)) : ℝ) <
      (8 * Ctw * ℓ / (Real.log ℓ * (83 / 10 + Real.log ℓ)) - 100 * Real.sqrt ℓ) * wt n

lemma wn_le_one (n : ℕ) : wn n ≤ 1 := by
  unfold wn
  apply Finset.prod_le_one₀
  · intro p hp
    simp only [mem_filter] at hp
    have : (2 : ℝ) < p := by exact_mod_cast hp.2
    apply div_nonneg <;> linarith
  · intro p hp
    simp only [mem_filter] at hp
    have : (2 : ℝ) < p := by exact_mod_cast hp.2
    rw [div_le_one (by linarith)]; linarith

lemma wt_mul_wn (n : ℕ) : wt n * wn n = 1 := by
  unfold wt wn
  rw [← prod_mul_distrib]
  apply prod_eq_one
  intro p hp
  simp only [mem_filter] at hp
  have : (2 : ℝ) < p := by exact_mod_cast hp.2
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp

lemma wn_pos (n : ℕ) : 0 < wn n := by
  have h0 : 0 ≤ wn n := by
    unfold wn
    apply prod_nonneg
    intro p hp
    simp only [mem_filter] at hp
    have : (2 : ℝ) < p := by exact_mod_cast hp.2
    apply div_nonneg <;> linarith
  rcases h0.lt_or_eq with h | h
  · exact h
  · have := wt_mul_wn n; rw [← h] at this; simp at this

/-- Lemma 5 multiplied through by `w(n)`. -/
lemma lemma5_w (h5 : Lemma5Neg) (ℓ : ℝ) (hℓ : Real.exp 60 ≤ ℓ) (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (#((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧ c ≤ p ∧ (p : ℝ) ≤ c + ℓ)) : ℝ) *
      wn n < 8 * Ctw * g83 ℓ - 100 * Real.sqrt ℓ := by
  have h := h5 ℓ hℓ c n hn
  have hw := wn_pos n
  have := mul_lt_mul_of_pos_right h hw
  rw [mul_assoc, wt_mul_wn, mul_one] at this
  unfold g83; linarith [show 8 * Ctw * ℓ / (Real.log ℓ * (83 / 10 + Real.log ℓ)) =
    8 * Ctw * (ℓ / (Real.log ℓ * (83 / 10 + Real.log ℓ))) by ring]

/-- At most `ℓ + 1` naturals lie in `[c, c + ℓ]`. -/
lemma card_closed_le (c ℓ : ℝ) (hc : 0 ≤ c) (hℓ : 0 ≤ ℓ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, c ≤ p ∧ (p : ℝ) ≤ c + ℓ) : (#S : ℝ) ≤ ℓ + 1 := by
  have hsub : S ⊆ Icc ⌈c⌉₊ ⌊c + ℓ⌋₊ := by
    intro p hp
    obtain ⟨h1, h2⟩ := hS p hp
    simp only [mem_Icc]
    exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
  have hc1 := card_le_card hsub
  rw [Nat.card_Icc] at hc1
  have hf : (⌊c + ℓ⌋₊ : ℝ) ≤ c + ℓ := Nat.floor_le (by linarith)
  have hcc : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  have : (#S : ℝ) ≤ ((⌊c + ℓ⌋₊ + 1 - ⌈c⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc1
  rcases le_or_gt ⌈c⌉₊ (⌊c + ℓ⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h] at this; push_cast at this; linarith
  · rw [Nat.sub_eq_zero_of_le h.le] at this; simp at this; rw [this]; simp; linarith

/-- `g` is increasing on `[e^60, ∞)`. -/
lemma g83_mono : MonotoneOn g83 (Set.Ici (Real.exp 60)) := by
  have h1 : 1 < Real.exp 60 := by have := Real.add_one_le_exp 60; linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro v hv
    simp only [Set.mem_Ici] at hv
    exact (hasDerivAt_g83 (by linarith)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro v hv
    simp only [Set.mem_Ioi] at hv
    exact (hasDerivAt_g83 (by linarith)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro v hv
    simp only [Set.mem_Ioi] at hv
    rw [(hasDerivAt_g83 (by linarith)).deriv]
    have hl : 60 ≤ Real.log v := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact hv.le
    unfold phi83
    apply div_nonneg _ (by positivity)
    nlinarith

lemma g83_le_two_half (y : ℝ) (hy : 4 < y) : g83 y ≤ 2 * g83 (y / 2) := by
  unfold g83
  have hy0 : 0 < y := by linarith
  have hL := Real.log_div hy0.ne' (two_ne_zero (α := ℝ))
  have h2 : Real.log 2 < Real.log (y / 2) := Real.log_lt_log (by norm_num) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < Real.log (y / 2) := by linarith
  rw [show 2 * (y / 2 / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2)))) =
    y / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2))) by ring]
  apply div_le_div_of_nonneg_left hy0.le (by positivity)
  have : Real.log (y / 2) ≤ Real.log y := by rw [hL]; linarith
  nlinarith

/-- The two-block estimate of page 61: if `u ∈ (0, y]` and the two counts satisfy Lemma 5
on lengths `u` and `y - u` when those are at least `e^60`, and the trivial bound otherwise,
then `(r₁ + r₂) w ≤ 8C·y/((log(y/2))(8.3 + log(y/2)))`. -/
lemma two_block (y u w r1 r2 : ℝ) (hy : Real.exp 121 ≤ y) (hu0 : 0 ≤ u) (huy : u ≤ y)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (h1 : Real.exp 60 ≤ u → r1 * w ≤ 8 * Ctw * g83 u - 100 * Real.sqrt u)
    (h1' : r1 ≤ u + 1)
    (h2 : Real.exp 60 ≤ y - u → r2 * w ≤ 8 * Ctw * g83 (y - u) - 100 * Real.sqrt (y - u))
    (h2' : r2 ≤ y - u + 1) :
    (r1 + r2) * w ≤ 8 * Ctw * (2 * g83 (y / 2)) := by
  have hC := Ctw_pos
  have e60 : (1 : ℝ) ≤ Real.exp 60 := by have := Real.add_one_le_exp 60; linarith
  have e121 : 2 * Real.exp 120 ≤ Real.exp 121 := by
    rw [show (121 : ℝ) = 120 + 1 by norm_num, Real.exp_add]
    have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    nlinarith [Real.exp_pos 120]
  have e120 : Real.exp 60 * Real.exp 60 = Real.exp 120 := by rw [← Real.exp_add]; norm_num
  have hy4 : 4 < y := by
    have := Real.add_one_le_exp 120
    linarith
  have hhalf := g83_le_two_half y hy4
  -- `√(v) ≥ e^60` when `v ≥ e^120`
  have hsq : ∀ v, Real.exp 120 ≤ v → Real.exp 60 ≤ Real.sqrt v := by
    intro v hv
    rw [Real.le_sqrt (by positivity) (by linarith [Real.exp_pos 120])]
    rw [sq, e120]; exact hv
  have hmono := g83_mono
  have hgy : ∀ v, Real.exp 60 ≤ v → v ≤ y → g83 v ≤ g83 y := fun v hv hvy =>
    hmono hv (le_trans hv hvy) hvy
  by_cases hA : Real.exp 60 ≤ u
  · by_cases hB : Real.exp 60 ≤ y - u
    · have a1 := h1 hA
      have a2 := h2 hB
      have hs1 : 0 ≤ 100 * Real.sqrt u := by positivity
      have hs2 : 0 ≤ 100 * Real.sqrt (y - u) := by positivity
      have key : g83 u + g83 (y - u) ≤ 2 * g83 (y / 2) := by
        rcases le_total u (y / 2) with h | h
        · have := eq78 u y hA h
          unfold g83; unfold g83 at hhalf
          rw [show 2 * (y / 2 / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2)))) =
            y / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2))) by ring]
          exact this
        · have := eq78 (y - u) y hB (by linarith)
          rw [show y - (y - u) = u by ring] at this
          unfold g83
          rw [show 2 * (y / 2 / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2)))) =
            y / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2))) by ring]
          linarith
      have : 8 * Ctw * (g83 u + g83 (y - u)) ≤ 8 * Ctw * (2 * g83 (y / 2)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
      nlinarith
    · push Not at hB
      -- `y - u < e^60`, so `u > y - e^60 ≥ e^120`
      have hu120 : Real.exp 120 ≤ u := by nlinarith
      have a1 := h1 hA
      have hs := hsq u hu120
      have hr2w : r2 * w ≤ Real.exp 60 + 1 := by
        have : r2 * w ≤ r2 := by nlinarith
        linarith
      have := hgy u hA huy
      have : 8 * Ctw * g83 u ≤ 8 * Ctw * (2 * g83 (y / 2)) :=
        mul_le_mul_of_nonneg_left (this.trans hhalf) (by positivity)
      nlinarith
  · push Not at hA
    have hB : Real.exp 120 ≤ y - u := by nlinarith
    have hB60 : Real.exp 60 ≤ y - u := by
      have : Real.exp 60 ≤ Real.exp 120 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    have a2 := h2 hB60
    have hs := hsq (y - u) hB
    have hr1w : r1 * w ≤ Real.exp 60 + 1 := by
      have : r1 * w ≤ r1 := by nlinarith
      linarith
    have := hgy (y - u) hB60 (by linarith)
    have : 8 * Ctw * g83 (y - u) ≤ 8 * Ctw * (2 * g83 (y / 2)) :=
      mul_le_mul_of_nonneg_left (this.trans hhalf) (by positivity)
    nlinarith

lemma Ctw_ge : 13 / 10 ≤ Ctw := by
  have := LeanLab.ChenExplicit.twinC_ge_065
  unfold Ctw; linarith

/-- `100 √v ≤ 8C g(v)` for `v ≥ e^60`, so an empty block meets the Lemma 5 bound. -/
lemma sqrt_le_g (v : ℝ) (hv : Real.exp 60 ≤ v) : 100 * Real.sqrt v ≤ 8 * Ctw * g83 v := by
  have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos 60) hv
  set s := Real.sqrt v with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hv0
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv0.le
  set t := Real.log s with ht
  have hL : Real.log v = 2 * t := by rw [← hs2, Real.log_pow]; push_cast; ring
  have hL60 : 60 ≤ Real.log v := by rw [Real.le_log_iff_exp_le hv0]; exact hv
  have ht30 : 30 ≤ t := by linarith
  have hst : Real.exp t = s := Real.exp_log hs0
  have hexp := Real.pow_div_factorial_le_exp t (by linarith) 5
  rw [hst] at hexp
  have hf : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  have hC := Ctw_ge
  have hden : 0 < 2 * t * (83 / 10 + 2 * t) := by positivity
  unfold g83
  rw [hL, ← hs2]
  rw [show 8 * Ctw * (s ^ 2 / (2 * t * (83 / 10 + 2 * t))) = s * (8 * Ctw * s / (2 * t * (83 / 10 + 2 * t))) by
    field_simp]
  have t3 : (30 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht30 3
  have t5 : t ^ 5 = t ^ 2 * t ^ 3 := by ring
  have h8 : 104 / 10 * s ≤ 8 * Ctw * s := by nlinarith
  have key : 100 ≤ 8 * Ctw * s / (2 * t * (83 / 10 + 2 * t)) := by
    rw [le_div_iff₀ hden]
    have : 2 * (30 : ℝ) ^ 3 * t ^ 2 ≤ 2 * t ^ 5 := by rw [t5]; nlinarith [sq_nonneg t]
    nlinarith
  calc 100 * s = s * 100 := by ring
    _ ≤ s * (8 * Ctw * s / (2 * t * (83 / 10 + 2 * t))) := mul_le_mul_of_nonneg_left key hs0.le

lemma rk_pos_elim {y : ℝ} {k n : ℕ} (h : Rk y k n ≠ 0) :
    ∃ p, p ≤ n ∧ p.Prime ∧ (n - p).Prime ∧ (k * y / 2 < p ∧ (p : ℝ) ≤ k * y / 2 + y) ∧
      (k * y / 2 < ((n - p : ℕ) : ℝ) ∧ ((n - p : ℕ) : ℝ) ≤ k * y / 2 + y) := by
  unfold Rk at h
  obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp h
  rw [mem_filter, mem_range] at hp
  exact ⟨p, by omega, hp.2⟩

/-- (7.3): `R_k(n) ≠ 0` only for `ky < n ≤ ky + 2y`. -/
lemma rk_support {y : ℝ} {k n : ℕ} (h : Rk y k n ≠ 0) :
    (k : ℝ) * y < n ∧ (n : ℝ) ≤ k * y + 2 * y := by
  obtain ⟨p, hpn, _, _, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := rk_pos_elim h
  rw [Nat.cast_sub hpn] at h3 h4
  constructor <;> linarith

/-- Page 61, `ky < n ≤ ky + y`: the primes of `R_k(n)` lie in `[ky/2, ky/2 + (n - ky)]`. -/
lemma rk_lower {y : ℝ} {k n : ℕ} :
    Rk y k n ≤ #((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧
      k * y / 2 ≤ p ∧ (p : ℝ) ≤ k * y / 2 + (n - k * y))) := by
  unfold Rk
  apply card_le_card
  intro p hp
  rw [mem_filter, mem_range] at hp ⊢
  obtain ⟨hpn, h0, h1, ⟨h2, h3⟩, ⟨h4, h5⟩⟩ := hp
  rw [Nat.cast_sub (by omega : p ≤ n)] at h4
  exact ⟨hpn, h0, h1, h2.le, by linarith⟩

/-- Page 61, `ky + y < n ≤ ky + 2y`: the primes lie in `[n - ky/2 - y, ky/2 + y]`. -/
lemma rk_upper {y : ℝ} {k n : ℕ} :
    Rk y k n ≤ #((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧
      (n - k * y / 2 - y : ℝ) ≤ p ∧ (p : ℝ) ≤ (n - k * y / 2 - y) + (k * y + 2 * y - n))) := by
  unfold Rk
  apply card_le_card
  intro p hp
  rw [mem_filter, mem_range] at hp ⊢
  obtain ⟨hpn, h0, h1, ⟨h2, h3⟩, ⟨h4, h5⟩⟩ := hp
  rw [Nat.cast_sub (by omega : p ≤ n)] at h5
  exact ⟨hpn, h0, h1, by linarith, by linarith⟩

lemma rk_mem_G {x y : ℝ} {k n : ℕ} (hy : 4 < y) (hk : 1 ≤ k) (hnx : n ≤ ⌊x⌋₊)
    (h : Rk y k n ≠ 0) : n ∈ Eset ⌊x⌋₊ \ Eset ⌊y⌋₊ := by
  obtain ⟨p, hpn, hp, hq, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := rk_pos_elim h
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp2 : p ≠ 2 := by
    intro e; rw [e] at h1; push_cast at h1; nlinarith
  have hq2 : n - p ≠ 2 := by
    intro e; rw [e] at h3; push_cast at h3; nlinarith
  obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
  obtain ⟨b, hb⟩ := hq.odd_of_ne_two hq2
  have hsum : p + (n - p) = n := by omega
  rw [mem_sdiff, mem_Eset, mem_Eset]
  have hny : (⌊y⌋₊ : ℝ) < n := by
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ y)
    rw [Nat.cast_sub hpn] at h3
    nlinarith
  have hny' : ⌊y⌋₊ < n := by exact_mod_cast hny
  refine ⟨⟨⟨by omega, hnx⟩, ⟨a + b + 1, by omega⟩, ?_⟩, fun h' => by omega⟩
  have := (AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)
  rwa [hsum] at this

set_option maxHeartbeats 4000000 in
/-- **Lemma 9**, page 60, CONDITIONAL ON Lemma 5 at `L = 60`, `A = 8.3`, `a = -1`. -/
theorem lemma9_of (h5 : Lemma5Neg) : Lemma9P := by
  intro x hx0 hL
  set y := x / 202 with hy
  have hy0 : 0 < y := by positivity
  have hy121 : Real.exp 121 ≤ y := by
    rw [← Real.exp_log hy0]; exact Real.exp_le_exp.mpr (by linarith)
  have hy4 : 4 < y := by have := Real.add_one_le_exp 121; linarith
  have hC := Ctw_pos
  set Bs := 8 * Ctw * (2 * g83 (y / 2)) with hBs
  have hBs0 : 0 ≤ Bs := by
    rw [hBs]; unfold g83
    have : Real.log 2 < Real.log (y / 2) := Real.log_lt_log (by norm_num) (by linarith)
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 < Real.log (y / 2) := by linarith
    positivity
  have hRHS : 8 * Ctw * y / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2))) = Bs := by
    rw [hBs]; unfold g83; ring
  rw [hRHS]
  set G := Eset ⌊x⌋₊ \ Eset ⌊y⌋₊ with hG
  -- per-n bound
  have hper : ∀ n ∈ range (⌊x⌋₊ + 1),
      ∑ k ∈ Icc 1 200, (Rk y k n : ℝ) * wn n ≤ Bs * (if n ∈ G then 1 else 0) := by
    intro n hn
    rw [mem_range] at hn
    have hnx : n ≤ ⌊x⌋₊ := by omega
    by_cases hnG : n ∈ G
    · rw [if_pos hnG, mul_one]
      have hn0 : 0 < n := by
        rw [hG, mem_sdiff, mem_Eset] at hnG; omega
      have hnR : (n : ℝ) ≤ 202 * y := by
        have : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hnx
        have := Nat.floor_le hx0.le
        rw [hy]; linarith
      by_cases hsmall : (n : ℝ) ≤ y
      · have : ∀ k ∈ Icc 1 200, (Rk y k n : ℝ) * wn n = 0 := by
          intro k hk
          rw [mem_Icc] at hk
          by_contra hc
          have hne : Rk y k n ≠ 0 := by
            intro e; rw [e] at hc; simp at hc
          have := (rk_support hne).1
          have : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
          nlinarith
        rw [sum_eq_zero this]; exact hBs0
      push Not at hsmall
      -- the block index `j` with `jy < n ≤ (j + 1)y`
      set j := ⌈(n : ℝ) / y⌉₊ - 1 with hj
      have hc1 : (n : ℝ) / y ≤ ⌈(n : ℝ) / y⌉₊ := Nat.le_ceil _
      have hc2 : (⌈(n : ℝ) / y⌉₊ : ℝ) < n / y + 1 := Nat.ceil_lt_add_one (by positivity)
      have hgt1 : 1 < (n : ℝ) / y := by rw [lt_div_iff₀ hy0]; linarith
      have hc3 : 2 ≤ ⌈(n : ℝ) / y⌉₊ := by
        have : (1 : ℝ) < ⌈(n : ℝ) / y⌉₊ := lt_of_lt_of_le hgt1 hc1
        have : 1 < ⌈(n : ℝ) / y⌉₊ := by exact_mod_cast this
        omega
      have hjR : (j : ℝ) = ⌈(n : ℝ) / y⌉₊ - 1 := by
        rw [hj, Nat.cast_sub (by omega)]; simp
      have hj1 : (j : ℝ) * y < n := by
        rw [hjR]
        have : ((⌈(n : ℝ) / y⌉₊ : ℝ) - 1) < n / y := by linarith
        rw [lt_div_iff₀ hy0] at this; linarith
      have hj2 : (n : ℝ) ≤ (j + 1) * y := by
        rw [hjR]; rw [div_le_iff₀ hy0] at hc1; linarith
      have hjge : 1 ≤ j := by omega
      -- only `k = j` and `k = j - 1` contribute
      have hsupp : ∀ k ∈ Icc 1 200, (Rk y k n : ℝ) * wn n =
          (if k = j then (Rk y k n : ℝ) * wn n else 0) +
          (if k + 1 = j then (Rk y k n : ℝ) * wn n else 0) := by
        intro k _
        by_cases hR : Rk y k n = 0
        · simp [hR]
        obtain ⟨s1, s2⟩ := rk_support hR
        have a1 : (k : ℝ) < j + 1 := by
          by_contra hc; push Not at hc
          have : ((j : ℝ) + 1) * y ≤ k * y := mul_le_mul_of_nonneg_right hc hy0.le
          linarith
        have a2 : (j : ℝ) < k + 2 := by
          by_contra hc; push Not at hc
          have : ((k : ℝ) + 2) * y ≤ j * y := mul_le_mul_of_nonneg_right hc hy0.le
          linarith
        have b1 : k < j + 1 := by exact_mod_cast a1
        have b2 : j < k + 2 := by exact_mod_cast a2
        rcases (by omega : k = j ∨ k + 1 = j) with e | e
        · rw [if_pos e, if_neg (by omega)]; ring
        · rw [if_neg (by omega), if_pos e]; ring
      rw [sum_congr rfl hsupp, sum_add_distrib, sum_ite_eq']
      have e2 : ∑ k ∈ Icc 1 200, (if k + 1 = j then (Rk y k n : ℝ) * wn n else 0) =
          if j - 1 ∈ Icc 1 200 then (Rk y (j - 1) n : ℝ) * wn n else 0 := by
        rw [← sum_ite_eq' (Icc 1 200) (j - 1) (fun k => (Rk y k n : ℝ) * wn n)]
        apply sum_congr rfl
        intro k _
        congr 1
        apply propext; constructor <;> intro h <;> omega
      rw [e2]
      set u := (n : ℝ) - j * y with hu
      set r1 : ℝ := if j ∈ Icc 1 200 then (Rk y j n : ℝ) else 0 with hr1
      set r2 : ℝ := if j - 1 ∈ Icc 1 200 then (Rk y (j - 1) n : ℝ) else 0 with hr2
      have hw := wn_pos n
      have hw1 := wn_le_one n
      have hsplit : (if j ∈ Icc 1 200 then (Rk y j n : ℝ) * wn n else 0) +
          (if j - 1 ∈ Icc 1 200 then (Rk y (j - 1) n : ℝ) * wn n else 0) = (r1 + r2) * wn n := by
        rw [hr1, hr2]; split_ifs <;> ring
      rw [hsplit]
      have hjm1 : ((j - 1 : ℕ) : ℝ) = j - 1 := by rw [Nat.cast_sub hjge]; simp
      -- the lower block `k = j`, length `u`
      have L1 : (Rk y j n : ℝ) ≤ #((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧
          j * y / 2 ≤ p ∧ (p : ℝ) ≤ j * y / 2 + u)) := by
        have := @rk_lower y j n; rw [hu]; exact_mod_cast this
      -- the upper block `k = j - 1`, length `y - u`
      have L2 : (Rk y (j - 1) n : ℝ) ≤ #((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧
          (n - (j - 1 : ℝ) * y / 2 - y : ℝ) ≤ p ∧
          (p : ℝ) ≤ (n - (j - 1 : ℝ) * y / 2 - y) + (y - u))) := by
        have := @rk_upper y (j - 1) n
        rw [hjm1] at this
        have e : ((j : ℝ) - 1) * y + 2 * y - n = y - u := by rw [hu]; ring
        rw [e] at this
        exact_mod_cast this
      have hu0 : 0 ≤ u := by rw [hu]; linarith
      have huy : u ≤ y := by rw [hu]; linarith
      have hc0 : 0 ≤ (n - (j - 1 : ℝ) * y / 2 - y : ℝ) := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast hjge
        nlinarith
      apply two_block y u (wn n) r1 r2 hy121 hu0 huy hw hw1
      · rw [hr1]; split_ifs <;> positivity
      · rw [hr2]; split_ifs <;> positivity
      · intro hu60
        rw [hr1]; split_ifs
        · have := lemma5_w h5 u hu60 (j * y / 2) n hn0
          exact (mul_le_mul_of_nonneg_right L1 hw.le).trans this.le
        · simp; exact sqrt_le_g u hu60
      · rw [hr1]; split_ifs
        · exact L1.trans (card_closed_le (j * y / 2) u (by positivity) hu0 _ (fun p hp => by
            rw [mem_filter] at hp; exact ⟨hp.2.2.2.1, hp.2.2.2.2⟩))
        · linarith
      · intro hu60
        rw [hr2]; split_ifs
        · have := lemma5_w h5 (y - u) hu60 (n - (j - 1 : ℝ) * y / 2 - y) n hn0
          exact (mul_le_mul_of_nonneg_right L2 hw.le).trans this.le
        · simp; exact sqrt_le_g (y - u) hu60
      · rw [hr2]; split_ifs
        · exact L2.trans (card_closed_le (n - (j - 1 : ℝ) * y / 2 - y) (y - u) hc0 (by linarith) _ (fun p hp => by
            rw [mem_filter] at hp; exact ⟨hp.2.2.2.1, hp.2.2.2.2⟩))
        · linarith
    · rw [if_neg hnG, mul_zero]
      apply le_of_eq
      apply sum_eq_zero
      intro k hk
      rw [mem_Icc] at hk
      by_cases hR : Rk y k n = 0
      · simp [hR]
      · exact absurd (rk_mem_G hy4 hk.1 hnx hR) hnG
  -- sum over `n`
  have hswap : ∑ k ∈ Icc 1 200, PsiK x y k =
      ∑ n ∈ range (⌊x⌋₊ + 1), ∑ k ∈ Icc 1 200, (Rk y k n : ℝ) * wn n := by
    unfold PsiK; exact sum_comm
  rw [hswap]
  refine (sum_le_sum hper).trans ?_
  rw [← mul_sum, sum_boole, mul_comm _ Bs]
  apply mul_le_mul_of_nonneg_left _ hBs0
  have hsub : Eset ⌊y⌋₊ ⊆ Eset ⌊x⌋₊ := by
    intro m hm
    rw [mem_Eset] at hm ⊢
    have : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by rw [hy]; linarith)
    exact ⟨⟨hm.1.1, by omega⟩, hm.2⟩
  have hcard : (#G : ℝ) = (NCount x : ℝ) - NCount y := by
    rw [hG, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
    rfl
  rw [← hcard]
  have : #((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ G)) ≤ #G := by
    apply card_le_card; intro m hm; rw [mem_filter] at hm; exact hm.2
  exact_mod_cast this

end LeanLab.RieselVaughan1983
