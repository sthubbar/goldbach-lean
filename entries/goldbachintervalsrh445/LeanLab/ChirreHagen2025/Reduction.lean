module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.ChirreHagen2025.Statements

/-!
P0075 Chirre-Hagen 2025: Section 5 in Lean. From the Section 5 upper bound, which the paper
derives from its Theorem 3 under RH, and the Cully-Hugill-Dudek lower bound, a Goldbach number
lies in `(x, x + 122.75 log² x]` for `x ≥ 1.1 · 10^18`; with the Oliveira e Silva, Herzog and
Pardi verification to `4 · 10^18` this gives Theorem 1 for every `x ≥ 2`.
All numerics of Section 5 are proved here, including the threshold `1.1 · 10^18`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real

/-- The paper's choice `C = 122.75` beats `6 · 2.5571 / (1/8 - a³)` with `a = 10^-13`. -/
theorem C_choice : 6 * 2.5571 / (1 / 8 - (1 / 10 ^ 13 : ℝ) ^ 3) < 122.75 := by norm_num

theorem log_x0_le : Real.log (1.1 * 10 ^ 18) ≤ 42 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 42 = Real.exp 1 ^ 42 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  calc (1.1 * 10 ^ 18 : ℝ) ≤ 2.7182818283 ^ 42 := by norm_num
    _ ≤ Real.exp 1 ^ 42 := by gcongr; exact Real.exp_one_gt_d9.le

theorem log_ge_41 {x : ℝ} (hx : 1.1 * 10 ^ 18 ≤ x) : 41 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 : Real.exp 41 = Real.exp 1 ^ 41 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  calc Real.exp 1 ^ 41 ≤ (2.7182818286 : ℝ) ^ 41 := by gcongr; exact Real.exp_one_lt_d9.le
    _ ≤ 1.1 * 10 ^ 18 := by norm_num
    _ ≤ x := hx

/-- Section 5's threshold: `122.75 log² x / (2x) ≤ 10^-13` whenever `x ≥ 1.1 · 10^18`. -/
theorem threshold {x : ℝ} (hx : 1.1 * 10 ^ 18 ≤ x) :
    122.75 * Real.log x ^ 2 / (2 * x) ≤ 1 / 10 ^ 13 := by
  have he2 : Real.exp 2 ≤ 1.1 * 10 ^ 18 := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 1.1 * 10 ^ 18 := by norm_num
  have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.mpr he2)
    (Set.mem_Ici.mpr (le_trans he2 hx)) hx
  simp only at hanti
  have hx0 : (0 : ℝ) < 1.1 * 10 ^ 18 := by norm_num
  have hxpos : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x / √x := div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hl0 hanti 2
  rw [div_pow, div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hx0.le] at hsq
  have hlx0 : 0 ≤ Real.log (1.1 * 10 ^ 18) := Real.log_nonneg (by norm_num)
  have h42 : Real.log (1.1 * 10 ^ 18) ^ 2 ≤ 42 ^ 2 := pow_le_pow_left₀ hlx0 log_x0_le 2
  have hb : Real.log x ^ 2 / x ≤ 42 ^ 2 / (1.1 * 10 ^ 18) :=
    le_trans hsq (div_le_div_of_nonneg_right h42 hx0.le)
  have : 122.75 * Real.log x ^ 2 / (2 * x) = 61.375 * (Real.log x ^ 2 / x) := by
    field_simp; ring
  rw [this]
  calc 61.375 * (Real.log x ^ 2 / x) ≤ 61.375 * (42 ^ 2 / (1.1 * 10 ^ 18)) := by gcongr
    _ ≤ 1 / 10 ^ 13 := by norm_num

/-- The numerical core of Section 5: with `h = 122.75 log² x`, `δ = h/(2x)`, `a = 10^-13`,
Theorem 3's upper bound is strictly below the no-Goldbach lower bound. -/
theorem core {x : ℝ} (hx : 1.1 * 10 ^ 18 ≤ x) :
    2.5571 * (122.75 * Real.log x ^ 2 / (2 * x)) *
        Real.log (2.0001 / (122.75 * Real.log x ^ 2 / (2 * x))) ^ 2 * x ^ 2
      < (122.75 * Real.log x ^ 2 / (2 * x)) ^ 2 * x ^ 3 / 3 * (1 / 8 - (1 / 10 ^ 13) ^ 3) := by
  set L := Real.log x with hLdef
  have hL : 41 ≤ L := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set δ := 122.75 * L ^ 2 / (2 * x) with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 10 ^ 13 := threshold hx
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by
    rw [le_div_iff₀ hδpos]; linarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, div_div_eq_mul_div]
    rw [div_le_iff₀ (by positivity)]
    have : (4.0002 : ℝ) ≤ 122.75 * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hD : 0 < δ * x ^ 2 := by positivity
  have hdx : δ * x = 122.75 * L ^ 2 / 2 := by rw [hδ]; field_simp
  have e1 : 2.5571 * δ * u ^ 2 * x ^ 2 = (δ * x ^ 2) * (2.5571 * u ^ 2) := by ring
  have e2 : δ ^ 2 * x ^ 3 / 3 * (1 / 8 - (1 / 10 ^ 13) ^ 3)
      = (δ * x ^ 2) * ((δ * x) / 3 * (1 / 8 - (1 / 10 ^ 13) ^ 3)) := by ring
  rw [e1, e2]
  apply mul_lt_mul_of_pos_left _ hD
  rw [hdx]
  have hL2 : 0 < L ^ 2 := by positivity
  nlinarith

/-- Section 5: a Goldbach number in `(x, x + 122.75 log² x]` for `x ≥ 1.1 · 10^18`. -/
theorem large_of (hU : Section5Upper) (hLow : NoGoldbachLower) :
    ∀ x : ℝ, 1.1 * 10 ^ 18 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 122.75 * Real.log x ^ 2 := by
  intro x hx
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := 122.75 * Real.log x ^ 2 with hh
  have hδle : h / (2 * x) ≤ 1 / 10 ^ 13 := threshold hx
  have hδpos : 0 < h / (2 * x) := by positivity
  have h1 : 1 ≤ h := by nlinarith
  have hhx : h ≤ x := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * x)).mp hδle
    nlinarith
  have hlow := hLow (1 / 10 ^ 13) x h (h / (2 * x)) le_rfl (by norm_num) (by linarith) (by linarith) h1 hhx hδpos
    hδle le_rfl hno
  have hup := hU (1 / 10 ^ 13) x (h / (2 * x)) le_rfl (by norm_num) (by linarith) hδpos hδle
  have hc := core hx
  rw [← hh] at hc
  linarith

/-- Small range from the even verification: for `2 ≤ x ≤ 2 · 10^18` a Goldbach number in
`(x, x + 4]`. -/
theorem small_of (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ x : ℝ, 2 ≤ x → x ≤ 2 * 10 ^ 18 →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 4 := by
  intro x h2 hX
  have hx0 : 0 ≤ x := by linarith
  set m := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  have hm2 : 2 ≤ m := Nat.le_floor (by exact_mod_cast h2)
  have hmX : m ≤ 2 * 10 ^ 18 := by
    have : (m : ℝ) ≤ 2 * 10 ^ 18 := le_trans hmx hX
    exact_mod_cast this
  set k := m / 2 with hk
  have hk1 : 2 * k ≤ m := Nat.mul_div_le m 2
  have hk2 : m ≤ 2 * k + 1 := by omega
  refine ⟨2 * k + 4, ?_, ?_, ?_⟩
  · have hev : Even (2 * k + 4) := ⟨k + 2, by ring⟩
    obtain ⟨p, q, hp, hq, hpq⟩ := hE (2 * k + 4) hev (by omega) (by omega)
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hqe : Even q := ⟨k + 1, by omega⟩
      have := (Nat.Prime.even_iff hq).mp hqe
      omega
    have hq2 : q ≠ 2 := by
      rintro rfl
      have hpe : Even p := ⟨k + 1, by omega⟩
      have := (Nat.Prime.even_iff hp).mp hpe
      omega
    exact ⟨p, q, hp, hq, hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2, hpq⟩
  · have : ((m : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hk2
    push_cast at this ⊢; linarith
  · have : ((2 * k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk1
    push_cast at this ⊢; linarith

/-- Theorem 1 from the large range and the `4 · 10^18` verification. -/
theorem theorem1_of
    (hLarge : ∀ x : ℝ, 1.1 * 10 ^ 18 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 122.75 * Real.log x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 123 * Real.log x ^ 2 := by
  intro x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2⟩ := small_of hE x hx hs
    refine ⟨n, hn, h1, ?_⟩
    nlinarith
  · obtain ⟨n, hn, h1, h2⟩ := hLarge x (by linarith)
    refine ⟨n, hn, h1, ?_⟩
    nlinarith

/-- Theorem 1 under RH, from the Section 5 inputs and the even verification. -/
theorem theorem1_of_inputs (hU : RiemannHypothesis → Section5Upper)
    (hLow : NoGoldbachLower) (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 123 * Real.log x ^ 2 :=
  fun hRH => theorem1_of (large_of (hU hRH) hLow) hE

end LeanLab.ChirreHagen2025
