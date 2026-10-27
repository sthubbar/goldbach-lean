module

public import Mathlib
public import LeanLab.DERZ1997.Lemma
public import LeanLab.KanieckiGap.Lemma7

/-!
P0022 L. Kaniecki 1995, Acta Arith. 72, page 371, Lemma 6: under RH,
`λ(x) < (1/4π) √((1 + 1/16597) x) log² x` for `x ≥ 2.3 · 10^9`, "This follows easily from
Theorems 10 and 12 of [11]", [11] Schoenfeld 1976. Read from the page image of
papers/P0022.pdf, cloud session 20261019T1116Z-cloud23, unit U-5463.

Here `lemma6` proves it for integer `x`, CONDITIONAL ON two cited inputs:
* `LeanLab.DERZ1997.Schoenfeld61`, Schoenfeld's θ bound in the `(log x - 2) log x` form for
  `x ≥ 2.3 · 10^9`, as P0011 quotes it, the same Prop the lab uses for P0011;
* `YoungPotler`, every prime gap with right end below `7.263 · 10^13` is at most `778`,
  the Young-Potler table Kaniecki cites as [16] in Section 3.
The proof is the one P0011 page 101 uses, plus a bootstrap for the right end of the gap,
which can lie beyond `x`: a crude bound from Bertrand first, then `ε = g/p` with
`ε log p ≤ 3`, from `log³ p ≤ 20 √p` via `log p ≤ 10 p^{1/10}`. The factor
`√(1 + 1/16597)` is not needed: the proof gives `λ(x) < √x log² x / (4π)`.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.KanieckiGap
open Real Chebyshev

/-- Schoenfeld's (6.1) right side as P0011 quotes it. -/
noncomputable def B (t : ℝ) : ℝ := √t * (Real.log t - 2) * Real.log t / (8 * π)

/-- Young-Potler, cited by Kaniecki as [16]: every gap `p' - p` with `p' ≤ 7.263 · 10^13`
is at most `778`. CITED, not proved here. -/
def YoungPotler : Prop :=
  ∀ p : ℕ, p.Prime → nextPrime p ≤ 7263 * 10 ^ 10 → gapAt p ≤ 778

/-! ### Real inequalities -/

theorem log_ge_21_5 {p : ℝ} (hp : 23 * 10 ^ 8 ≤ p) : 21.5 ≤ Real.log p := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h43 : Real.exp 43 ≤ (2.7182818286 : ℝ) ^ 43 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 43
    rwa [← Real.exp_nat_mul, show ((43 : ℕ) : ℝ) * 1 = 43 by norm_num] at h
  have hsq : Real.exp 21.5 ^ 2 = Real.exp 43 := by rw [← Real.exp_nat_mul]; norm_num
  have h0 := Real.exp_pos 21.5
  nlinarith

/-- `log³ p ≤ 20 √p` for `p ≥ 2.3 · 10^9`, from `log p ≤ 10 p^{1/10}`. -/
theorem log_cube_le {p : ℝ} (hp : 23 * 10 ^ 8 ≤ p) : Real.log p ^ 3 ≤ 20 * √p := by
  have hp0 : 0 < p := by linarith
  set r := p ^ ((1 : ℝ) / 10) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hp0 _
  have hr10 : r ^ 10 = p := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hlog : Real.log p ≤ 10 * r := by
    have := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 10)
    rw [← hr] at this; linarith
  have hs : √p = r ^ 5 := by
    rw [← hr10, show r ^ 10 = (r ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hr2 : 50 ≤ r ^ 2 := by
    by_contra h
    push_neg at h
    have : (r ^ 2) ^ 5 < 50 ^ 5 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    rw [← pow_mul] at this; norm_num at this; linarith
  have hL0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  rw [hs]
  calc Real.log p ^ 3 ≤ (10 * r) ^ 3 := pow_le_pow_left₀ hL0 hlog 3
    _ = 1000 * r ^ 3 := by ring
    _ ≤ 20 * r ^ 5 := by nlinarith [pow_pos hr0 3]

/-- The core: if a gap `g ≤ p` after `p ≥ 2.3 · 10^9` obeys `g - 1 < B(p) + B(p + g - 1)`,
then `g < √p log² p / (4π)`. -/
theorem core {p g : ℝ} (hp : 23 * 10 ^ 8 ≤ p) (hg1 : 1 ≤ g) (hgp : g ≤ p)
    (h : g - 1 < B p + B (p + g - 1)) : g < √p * Real.log p ^ 2 / (4 * π) := by
  have hp0 : 0 < p := by linarith
  set s := √p with hs
  set L := Real.log p with hLdef
  set t := p + g - 1 with ht
  have hs0 : 0 < s := Real.sqrt_pos.mpr hp0
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp0.le
  have hL : 21.5 ≤ L := log_ge_21_5 hp
  have hL3 : L ^ 3 ≤ 20 * s := log_cube_le hp
  have hpt : p ≤ t := by linarith
  have ht2 : t ≤ 2 * p := by linarith
  have ht0 : 0 < t := by linarith
  have hpi := Real.pi_gt_d2
  have hpi0 := Real.pi_pos
  have h8pi : 0 < 8 * π := by positivity
  have hlogt : L ≤ Real.log t := Real.log_le_log hp0 hpt
  have hBdef : ∀ u, B u = √u * (Real.log u - 2) * Real.log u / (8 * π) := fun u => rfl
  -- crude bound: g ≤ 1 + s L² / 10
  have hlog2p : Real.log t ≤ L + 0.7 := by
    have := Real.log_le_log ht0 ht2
    rw [Real.log_mul (by norm_num) hp0.ne'] at this
    have := Real.log_two_lt_d9; linarith
  have hst : √t ≤ 1.4143 * s := by
    have h2 : √(2 : ℝ) ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc √t ≤ √(2 * p) := Real.sqrt_le_sqrt ht2
      _ = √2 * s := by rw [Real.sqrt_mul (by norm_num)]
      _ ≤ 1.4143 * s := mul_le_mul_of_nonneg_right h2 hs0.le
  have hlt2 : 0 ≤ Real.log t - 2 := by linarith
  have hBp' : B p = s * ((L - 2) * L) / (8 * π) := by rw [hBdef]; ring
  have hBp : B p ≤ s * L ^ 2 / (8 * π) := by
    rw [hBp']
    apply div_le_div_of_nonneg_right _ h8pi.le
    apply mul_le_mul_of_nonneg_left _ hs0.le
    nlinarith
  have hBt1 : B t ≤ 1.4143 * s * (L + 0.7) ^ 2 / (8 * π) := by
    rw [hBdef]
    apply div_le_div_of_nonneg_right _ h8pi.le
    have a1 : √t * (Real.log t - 2) ≤ (1.4143 * s) * (L + 0.7) :=
      mul_le_mul hst (by linarith) hlt2 (by positivity)
    have a2 := mul_le_mul a1 hlog2p (by linarith) (by positivity)
    nlinarith
  have hcrude : g ≤ 1 + s * L ^ 2 / 10 := by
    have h1 : g - 1 < (s * L ^ 2 + 1.4143 * s * (L + 0.7) ^ 2) / (8 * π) := by
      rw [add_div]; linarith
    have h2 : (s * L ^ 2 + 1.4143 * s * (L + 0.7) ^ 2) / (8 * π) ≤ s * L ^ 2 / 10 := by
      rw [div_le_div_iff₀ h8pi (by norm_num)]
      have h3 : (L + 0.7) ^ 2 ≤ 1.067 * L ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1.4143 * s)
      have h5 : 0 ≤ s * L ^ 2 := by positivity
      nlinarith
    linarith
  -- ε = g / p, with ε L ≤ 3
  set ε := g / p with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεp : ε * p = g := by rw [hε]; field_simp
  have hLp : L ≤ p := by
    have := Real.log_le_sub_one_of_pos hp0; rw [← hLdef] at this; linarith
  have hεL : ε * L ≤ 3 := by
    have h1 : ε * L * p ≤ 3 * p := by
      calc ε * L * p = g * L := by rw [← hεp]; ring
        _ ≤ (1 + s * L ^ 2 / 10) * L := mul_le_mul_of_nonneg_right hcrude (by linarith)
        _ = L + s * L ^ 3 / 10 := by ring
        _ ≤ p + s * (20 * s) / 10 := by
            have := mul_le_mul_of_nonneg_left hL3 hs0.le
            linarith
        _ = 3 * p := by rw [← hs2]; ring
    exact le_of_mul_le_mul_right h1 hp0
  have hεs : ε ≤ 0.14 := by
    have := mul_le_mul_of_nonneg_left hL hε0; linarith
  -- refined bounds at t
  have hst2 : √t ≤ s * (1 + ε / 2) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, hs2]
    have : t ≤ p * (1 + ε) := by rw [mul_add, mul_one, mul_comm, hεp]; linarith
    nlinarith [mul_nonneg hp0.le (sq_nonneg ε)]
  have hlogt2 : Real.log t ≤ L + ε := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 hp0)
    rw [Real.log_div ht0.ne' hp0.ne', ← hLdef] at h1
    have : t / p - 1 ≤ ε := by
      rw [hε, div_sub_one hp0.ne', div_le_div_iff_of_pos_right hp0]; linarith
    linarith
  have hBt : B t ≤ s * ((1 + ε / 2) * (L + ε - 2) * (L + ε)) / (8 * π) := by
    rw [hBdef]
    apply div_le_div_of_nonneg_right _ h8pi.le
    have a1 : √t * (Real.log t - 2) ≤ (s * (1 + ε / 2)) * (L + ε - 2) :=
      mul_le_mul hst2 (by linarith) hlt2 (by positivity)
    have a2 := mul_le_mul a1 hlogt2 (by linarith)
      (mul_nonneg (by positivity) (by linarith))
    exact a2.trans_eq (by ring)
  have hpoly : (1 + ε / 2) * (L + ε - 2) * (L + ε) ≤ (L - 2) * L + 1.9 * L := by
    have expand : (1 + ε / 2) * (L + ε - 2) * (L + ε)
        = (L - 2) * L + ε * L - 2 * ε + (ε * L) * L / 2 + ε * (ε * L) + ε ^ 3 / 2 := by ring
    have h1 : (ε * L) * L ≤ 3 * L := mul_le_mul_of_nonneg_right hεL (by linarith)
    have h2 : ε * (ε * L) ≤ ε * 3 := mul_le_mul_of_nonneg_left hεL hε0
    have h3 : ε ^ 3 ≤ 0.14 ^ 3 := pow_le_pow_left₀ hε0 hεs 3
    rw [expand]; linarith
  have hBp' : B p = s * ((L - 2) * L) / (8 * π) := by unfold B; rw [← hs, ← hLdef]; ring
  have hsum : g - 1 < s * (2 * L ^ 2 - 2.1 * L) / (8 * π) := by
    have h3 : B t ≤ s * ((L - 2) * L + 1.9 * L) / (8 * π) :=
      hBt.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hs0.le) h8pi.le)
    have h4 : B p + B (p + g - 1) ≤ s * (2 * L ^ 2 - 2.1 * L) / (8 * π) := by
      rw [hBp']
      have : s * ((L - 2) * L) / (8 * π) + s * ((L - 2) * L + 1.9 * L) / (8 * π)
          = s * (2 * L ^ 2 - 2.1 * L) / (8 * π) := by ring
      linarith
    linarith
  have hfin : s * (2 * L ^ 2 - 2.1 * L) / (8 * π) + 1 < s * L ^ 2 / (4 * π) := by
    have : s * L ^ 2 / (4 * π) = s * (2 * L ^ 2) / (8 * π) := by field_simp; ring
    rw [this, ← sub_pos]
    have : s * (2 * L ^ 2) / (8 * π) - (s * (2 * L ^ 2 - 2.1 * L) / (8 * π) + 1)
        = (2.1 * s * L - 8 * π) / (8 * π) := by field_simp; ring
    rw [this]
    apply div_pos _ (by positivity)
    have : (10000 : ℝ) ≤ s := by
      rw [hs, Real.le_sqrt (by norm_num) hp0.le]; linarith
    have := Real.pi_lt_d2
    nlinarith
  linarith

/-! ### Lemma 6 -/

theorem nextPrime_le_two_mul {p : ℕ} (hp : 1 ≤ p) : nextPrime p ≤ 2 * p := by
  obtain ⟨r, hr, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul p (by omega)
  exact (nextPrime_min h1 hr).trans h2

/-- No prime in `(p, nextPrime p - 1]`, so `θ(nextPrime p - 1) = θ(p)`. -/
theorem theta_before_next (p : ℕ) :
    θ (((nextPrime p - 1 : ℕ)) : ℝ) = θ (p : ℝ) := by
  obtain ⟨h1, _⟩ := nextPrime_spec p
  rw [LeanLab.DERZ1997.theta_nat_add (a := p) (b := nextPrime p - 1) (by omega)]
  rw [Finset.sum_eq_zero, add_zero]
  intro k hk
  rw [Finset.mem_Ioc] at hk
  rw [if_neg]
  intro hkp
  have := nextPrime_min hk.1 hkp
  omega

/-- The gap after one prime `p ≤ x`, `x ≥ 2.3 · 10^9`, is below `√x log² x / (4π)`. -/
theorem gap_lt (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : YoungPotler) {p x : ℕ}
    (hp : p.Prime) (hpx : p ≤ x) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * π) := by
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx := log_ge_21_5 hxR
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  obtain ⟨hq1, hq2⟩ := nextPrime_spec p
  rcases Nat.lt_or_ge (7263 * 10 ^ 10) (nextPrime p) with hbig | hsmall
  · -- the analytic case: p ≥ 3.6 · 10^13
    have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
    have hp13 : 23 * 10 ^ 8 ≤ p := by omega
    have hpR : (23 * 10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp13
    set q := nextPrime p with hq
    have hθ := theta_before_next p
    rw [← hq] at hθ
    have hcast : ((q - 1 : ℕ) : ℝ) = (p : ℝ) + (gapAt p : ℝ) - 1 := by
      unfold gapAt; rw [← hq]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hg1 : (1 : ℝ) ≤ gapAt p := by unfold gapAt; exact_mod_cast (by omega : 1 ≤ q - p)
    have hS1 := hS ((q - 1 : ℕ) : ℝ) (by rw [hcast]; linarith)
    have hS2 := hS (p : ℝ) hpR
    have hgp : (gapAt p : ℝ) ≤ p := by unfold gapAt; exact_mod_cast (by omega : q - p ≤ p)
    have hkey : (gapAt p : ℝ) - 1 < B p + B (p + gapAt p - 1) := by
      rw [hθ, hcast] at hS1
      have a1 := (abs_lt.mp hS1).1
      have a2 := (abs_lt.mp hS2).2
      unfold B; linarith
    refine (core hpR hg1 hgp hkey).trans_le ?_
    have hpx' : (p : ℝ) ≤ x := by exact_mod_cast hpx
    have hLp := log_ge_21_5 hpR
    gcongr
  · -- the table case
    have h778 := hY p hp hsmall
    have : (gapAt p : ℝ) ≤ 778 := by exact_mod_cast h778
    have hsx : (47958 : ℝ) ≤ √(x : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hsx (pow_le_pow_left₀ (by norm_num) hLx 2) (by norm_num)
      (Real.sqrt_nonneg _)]

/-- **Kaniecki Lemma 6**, integer `x`, CONDITIONAL ON `Schoenfeld61` and `YoungPotler`:
`λ(x) < (1/4π) √((1 + 1/16597) x) log² x` for `x ≥ 2.3 · 10^9`. -/
theorem lemma6 (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : YoungPotler) (x : ℕ)
    (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 := by
  have hx7 : ¬ x ≤ 7 := by omega
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  obtain ⟨p, hpmem, hpeq⟩ := Finset.exists_mem_eq_sup _ hne gapAt
  rw [Finset.mem_filter, Finset.mem_range] at hpmem
  have hlam : lam x = gapAt p := by unfold lam; rw [if_neg hx7, hpeq]
  rw [hlam]
  refine (gap_lt hS hY hpmem.2 (by omega) hx).trans_le ?_
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hsq : √(x : ℝ) ≤ √((1 + 1 / 16597) * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
  gcongr

end LeanLab.KanieckiGap

