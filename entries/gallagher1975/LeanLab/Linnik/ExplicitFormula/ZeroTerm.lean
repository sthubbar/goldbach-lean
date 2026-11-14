module

public import LeanLab.Linnik.ExplicitFormula.Defs

/-!
# Second differences of the zero terms, Gallagher 1970 Section 7

AI wrote the Lean code. Binary Goldbach is OPEN.
With `D_ρ(u) = u^(ρ+2)/((ρ+1)(ρ+2))`, `D_ρ'' = u^ρ`, so for `b ≤ a`
`D(a+h) - D(a) - D(b+h) + D(b) = ∫_b^a ∫_u^(u+h) t^ρ dt du`, of norm at most `h (a - b) max t^β`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- First antiderivative layer `u^(ρ+1)/(ρ+1)`, elementary. -/
noncomputable def D1z (ρ : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (ρ + 1) / (ρ + 1)

/-- `D1z ρ` has derivative `x^ρ` at `x > 0`, elementary. -/
theorem D1z_hasDerivAt {ρ : ℂ} (hρ : ρ ≠ -1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => D1z ρ y) ((x : ℂ) ^ ρ) x :=
  hasDerivAt_ofReal_cpow_const' hx.ne' hρ

/-- `Dz ρ` has derivative `D1z ρ x` at `x > 0`, elementary. -/
theorem Dz_hasDerivAt {ρ : ℂ} (hρ1 : ρ + 1 ≠ -1) (hρ0 : ρ + 1 ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Dz ρ y) (D1z ρ x) x := by
  have h := (hasDerivAt_ofReal_cpow_const' hx.ne' hρ1).div_const (ρ + 1)
  have he : (fun y : ℝ => Dz ρ y) =
      fun y : ℝ => (y : ℂ) ^ ((ρ + 1) + 1) / ((ρ + 1) + 1) / (ρ + 1) := by
    funext y
    unfold Dz
    rw [div_div, show ρ + 1 + 1 = ρ + 2 by ring, mul_comm (ρ + 2)]
  rw [he]
  exact h

/-- Inner difference: `‖D1z(u+h) - D1z(u)‖ ≤ h (u+h)^β` for `Re ρ ≥ 0`, mean value inequality. -/
theorem D1z_diff_le {ρ : ℂ} (h0 : 0 ≤ ρ.re) {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) :
    ‖D1z ρ (u + h) - D1z ρ u‖ ≤ (u + h) ^ ρ.re * h := by
  have hρ : ρ ≠ -1 := by
    intro e; rw [e] at h0; norm_num at h0
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun y : ℝ => D1z ρ y)
    (f' := fun t : ℝ => (t : ℂ) ^ ρ) (C := (u + h) ^ ρ.re) (a := u) (b := u + h)
    (fun x hx => (D1z_hasDerivAt hρ (lt_of_lt_of_le hu hx.1)).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hu hx.1
      rw [norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_rpow hx0.le hx.2.le h0)
    (u + h) ⟨by linarith, le_rfl⟩
  simpa using key

/-- Second difference bound by the size of `t^ρ`, for `0 ≤ Re ρ ≤ 1`. -/
theorem double_diff_le {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) {a b h : ℝ} (hb : 0 < b)
    (hba : b ≤ a) (hh : 0 ≤ h) :
    ‖Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b‖ ≤ h * (a - b) * (a + h) ^ ρ.re := by
  have hρ1 : ρ + 1 ≠ -1 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith
  have hρ0 : ρ + 1 ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => Dz ρ (y + h) - Dz ρ y)
    (f' := fun t : ℝ => D1z ρ (t + h) - D1z ρ t) (C := (a + h) ^ ρ.re * h) (a := b) (b := a)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hb hx.1
      have h1 := (Dz_hasDerivAt hρ1 hρ0 (show 0 < x + h by linarith)).comp_add_const x h
      exact (h1.sub (Dz_hasDerivAt hρ1 hρ0 hx0)).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hb hx.1
      refine (D1z_diff_le h0 hx0 hh).trans ?_
      gcongr
      · linarith [hx.2])
    a ⟨hba, le_rfl⟩
  have e : Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b =
      (Dz ρ (a + h) - Dz ρ a) - (Dz ρ (b + h) - Dz ρ b) := by ring
  rw [e]
  refine key.trans (le_of_eq ?_)
  ring

/-- Size of a single `Dz` term: `‖Dz ρ u‖ ≤ M^(β+2)/‖(ρ+1)(ρ+2)‖` for `0 < u ≤ M`, `β ≥ -2`, elementary. -/
theorem norm_Dz_le {ρ : ℂ} (h0 : -2 ≤ ρ.re) {u M : ℝ} (hu : 0 < u) (huM : u ≤ M) :
    ‖Dz ρ u‖ ≤ M ^ (ρ.re + 2) / ‖(ρ + 1) * (ρ + 2)‖ := by
  unfold Dz
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hu]
  have : (ρ + 2).re = ρ.re + 2 := by simp
  rw [this]
  gcongr
  linarith

/-- Second difference bound by the size of `D` itself, for `-1/2 ≤ Re ρ ≤ 1`. -/
theorem double_diff_le' {ρ : ℂ} (h0 : -1 / 2 ≤ ρ.re) (h1 : ρ.re ≤ 1) {a b h : ℝ} (hb : 0 < b)
    (hba : b ≤ a) (hh : 0 ≤ h) :
    ‖Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b‖ ≤
      4 * (a + h) ^ (ρ.re + 2) / ‖(ρ + 1) * (ρ + 2)‖ := by
  have hr : -2 ≤ ρ.re := by linarith
  have t1 := norm_Dz_le hr (u := a + h) (M := a + h) (by linarith) le_rfl
  have t2 := norm_Dz_le hr (u := a) (M := a + h) (by linarith) (by linarith)
  have t3 := norm_Dz_le hr (u := b + h) (M := a + h) (by linarith) (by linarith)
  have t4 := norm_Dz_le hr (u := b) (M := a + h) hb (by linarith)
  calc ‖Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b‖
      ≤ ‖Dz ρ (a + h)‖ + ‖Dz ρ a‖ + ‖Dz ρ (b + h)‖ + ‖Dz ρ b‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 4 * (a + h) ^ (ρ.re + 2) / ‖(ρ + 1) * (ρ + 2)‖ := by
        rw [mul_div_assoc]; linarith

/-- The real parameter `e ≥ 0`, seen in `ℂ`, is not `-1`, elementary. -/
theorem ofReal_ne_neg_one {e : ℝ} (he0 : 0 ≤ e) : (e : ℂ) ≠ -1 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith

/-- One unit step of the main term comparison: for real `m ≥ 1`, the scaled second difference on
`[m, m+1]` is `(m+1)^e` up to `(m+1+h)^e - m^e`, mean value inequality twice, elementary. -/
theorem double_diff_step {e : ℝ} (he0 : 0 ≤ e) {m h : ℝ} (hm : 1 ≤ m) (hh : 0 < h) :
    ‖(Dz (e : ℂ) (m + 1 + h) - Dz (e : ℂ) (m + 1) - Dz (e : ℂ) (m + h) + Dz (e : ℂ) m) / h -
        (((m + 1) ^ e : ℝ) : ℂ)‖ ≤ (m + 1 + h) ^ e - m ^ e := by
  set N : ℂ := (((m + 1) ^ e : ℝ) : ℂ) with hN
  set c : ℝ := (m + 1 + h) ^ e - m ^ e with hc
  have hρ : (e : ℂ) ≠ -1 := ofReal_ne_neg_one he0
  have hρ1 : (e : ℂ) + 1 ≠ -1 := by
    intro h'; have := congrArg Complex.re h'; simp at this; linarith
  have hρ0 : (e : ℂ) + 1 ≠ 0 := by
    intro h'; have := congrArg Complex.re h'; simp at this; linarith
  -- pointwise bound on the derivative
  have hpt : ∀ t : ℝ, m ≤ t → t ≤ m + 1 + h → ‖(t : ℂ) ^ (e : ℂ) - N‖ ≤ c := by
    intro t ht1 ht2
    have ht0 : 0 ≤ t := by linarith
    rw [hN, ← ofReal_cpow ht0, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_le_iff]
    have a1 : m ^ e ≤ t ^ e := Real.rpow_le_rpow (by linarith) ht1 he0
    have a2 : t ^ e ≤ (m + 1 + h) ^ e := Real.rpow_le_rpow ht0 ht2 he0
    have a3 : m ^ e ≤ (m + 1) ^ e := Real.rpow_le_rpow (by linarith) (by linarith) he0
    have a4 : (m + 1) ^ e ≤ (m + 1 + h) ^ e := Real.rpow_le_rpow (by linarith) (by linarith) he0
    constructor <;> linarith
  -- inner mean value step
  have hin : ∀ u : ℝ, m ≤ u → u ≤ m + 1 →
      ‖D1z (e : ℂ) (u + h) - D1z (e : ℂ) u - (h : ℂ) * N‖ ≤ c * h := by
    intro u hu1 hu2
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => D1z (e : ℂ) t - (t : ℂ) * N)
      (f' := fun t : ℝ => (t : ℂ) ^ (e : ℂ) - N) (C := c) (a := u) (b := u + h)
      (fun x hx => by
        have hx0 : 0 < x := by linarith [hx.1]
        have h2 := ((hasDerivAt_id x).ofReal_comp).mul_const N
        exact ((D1z_hasDerivAt hρ hx0).sub h2).hasDerivWithinAt.congr_deriv (by simp))
      (fun x hx => hpt x (by linarith [hx.1]) (by linarith [hx.2]))
      (u + h) ⟨by linarith, le_rfl⟩
    have e1 : D1z (e : ℂ) (u + h) - ((u + h : ℝ) : ℂ) * N - (D1z (e : ℂ) u - (u : ℂ) * N) =
        D1z (e : ℂ) (u + h) - D1z (e : ℂ) u - (h : ℂ) * N := by push_cast; ring
    rw [e1] at key
    simpa using key
  -- outer mean value step
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u : ℝ => Dz (e : ℂ) (u + h) - Dz (e : ℂ) u - (u : ℂ) * ((h : ℂ) * N))
    (f' := fun u : ℝ => D1z (e : ℂ) (u + h) - D1z (e : ℂ) u - (h : ℂ) * N)
    (C := c * h) (a := m) (b := m + 1)
    (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      have h1 := (Dz_hasDerivAt hρ1 hρ0 (show 0 < x + h by linarith)).comp_add_const x h
      have h2 := ((hasDerivAt_id x).ofReal_comp).mul_const ((h : ℂ) * N)
      exact ((h1.sub (Dz_hasDerivAt hρ1 hρ0 hx0)).sub h2).hasDerivWithinAt.congr_deriv
        (by simp))
    (fun x hx => hin x hx.1 hx.2.le)
    (m + 1) ⟨by linarith, le_rfl⟩
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have e2 : (Dz (e : ℂ) (m + 1 + h) - Dz (e : ℂ) (m + 1) - Dz (e : ℂ) (m + h) + Dz (e : ℂ) m) / h -
      N = (Dz (e : ℂ) (m + 1 + h) - Dz (e : ℂ) (m + 1) - ((m + 1 : ℝ) : ℂ) * ((h : ℂ) * N) -
        (Dz (e : ℂ) (m + h) - Dz (e : ℂ) m - (m : ℂ) * ((h : ℂ) * N))) / h := by
    field_simp
    push_cast
    ring
  rw [e2, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_le_iff₀ hh]
  have : m + 1 - m = 1 := by ring
  rw [this, mul_one] at key
  exact key

/-- Summing `double_diff_step` over `b < n ≤ a`, telescoping, elementary. -/
theorem double_diff_tele {e : ℝ} (he0 : 0 ≤ e) {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a)
    {h : ℝ} (hh : 0 < h) :
    ‖(Dz (e : ℂ) (a + h) - Dz (e : ℂ) a - Dz (e : ℂ) (b + h) + Dz (e : ℂ) b) / h -
        ∑ n ∈ Ioc b a, (((n : ℝ) ^ e : ℝ) : ℂ)‖ ≤
      ∑ n ∈ Ioc b a, (((n : ℝ) + h) ^ e - ((n : ℝ) - 1) ^ e) := by
  induction a, hba using Nat.le_induction with
  | base =>
    have : Dz (e : ℂ) (b + h) - Dz (e : ℂ) b - Dz (e : ℂ) (b + h) + Dz (e : ℂ) b = 0 := by ring
    simp [this]
  | succ a hab ih =>
    rw [sum_Ioc_succ_top hab, sum_Ioc_succ_top hab]
    have hm : (1 : ℝ) ≤ a := by exact_mod_cast hb.trans hab
    have st := double_diff_step he0 hm hh
    have e1 : (Dz (e : ℂ) (((a + 1 : ℕ) : ℝ) + h) - Dz (e : ℂ) ((a + 1 : ℕ) : ℝ) -
        Dz (e : ℂ) (b + h) + Dz (e : ℂ) b) / h -
        (∑ n ∈ Ioc b a, (((n : ℝ) ^ e : ℝ) : ℂ) + ((((a + 1 : ℕ) : ℝ) ^ e : ℝ) : ℂ)) =
        ((Dz (e : ℂ) (a + h) - Dz (e : ℂ) a - Dz (e : ℂ) (b + h) + Dz (e : ℂ) b) / h -
          ∑ n ∈ Ioc b a, (((n : ℝ) ^ e : ℝ) : ℂ)) +
        ((Dz (e : ℂ) (a + 1 + h) - Dz (e : ℂ) (a + 1) - Dz (e : ℂ) (a + h) + Dz (e : ℂ) a) / h -
          ((((a : ℝ) + 1) ^ e : ℝ) : ℂ)) := by
      push_cast; ring
    rw [e1]
    have e2 : (((a + 1 : ℕ) : ℝ) + h) ^ e - (((a + 1 : ℕ) : ℝ) - 1) ^ e =
        ((a : ℝ) + 1 + h) ^ e - (a : ℝ) ^ e := by push_cast; ring_nf
    rw [e2]
    exact (norm_add_le _ _).trans (add_le_add ih st)

/-- The error sum is at most `4 (h+1) (2a)^e`, by shifting `n + h` up to `n - 1 + k`,
`k = ⌈h⌉ + 1`, and telescoping in steps of one, elementary. -/
theorem err_sum_le {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a)
    {h : ℝ} (hh1 : 1 ≤ h) (hha : h ≤ a) :
    ∑ n ∈ Ioc b a, (((n : ℝ) + h) ^ e - ((n : ℝ) - 1) ^ e) ≤ 4 * (h + 1) * (2 * a : ℝ) ^ e := by
  set k : ℕ := ⌈h⌉₊ + 1 with hk
  have hkh : (k : ℝ) ≤ h + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ h by linarith)
    rw [hk]; push_cast; linarith
  have hhk : h ≤ (k : ℝ) - 1 := by
    rw [hk]; push_cast; linarith [Nat.le_ceil h]
  -- shift up
  have s1 : ∑ n ∈ Ioc b a, (((n : ℝ) + h) ^ e - ((n : ℝ) - 1) ^ e) ≤
      ∑ n ∈ Ioc b a, (((n : ℝ) - 1 + k) ^ e - ((n : ℝ) - 1) ^ e) := by
    apply sum_le_sum
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (hb.trans this.le)
    have : ((n : ℝ) + h) ^ e ≤ ((n : ℝ) - 1 + k) ^ e :=
      Real.rpow_le_rpow (by linarith) (by linarith) he0
    linarith
  -- telescoping identity
  have s2 : ∀ a' : ℕ, b ≤ a' →
      ∑ n ∈ Ioc b a', (((n : ℝ) - 1 + k) ^ e - ((n : ℝ) - 1) ^ e) =
        ∑ j ∈ range k, (((a' : ℝ) + j) ^ e - ((b : ℝ) + j) ^ e) := by
    intro a' hba'
    induction a', hba' using Nat.le_induction with
    | base => simp
    | succ a' hab ih =>
      rw [sum_Ioc_succ_top hab, ih]
      have t := Finset.sum_range_sub (fun j : ℕ => ((a' : ℝ) + j) ^ e) k
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at t
      rw [← sub_eq_zero]
      have e3 : ∑ j ∈ range k, (((a' : ℝ) + 1 + j) ^ e - ((b : ℝ) + j) ^ e) =
          ∑ j ∈ range k, (((a' : ℝ) + j) ^ e - ((b : ℝ) + j) ^ e) +
          ∑ j ∈ range k, (((a' : ℝ) + (j + 1)) ^ e - ((a' : ℝ) + j) ^ e) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        ring_nf
      push_cast
      rw [e3, t]
      have : (a' : ℝ) + 1 - 1 = a' := by ring
      simp only [this]
      ring
  rw [s2 a hba] at s1
  -- bound the telescoped sum
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hb.trans hba
  have s3 : ∑ j ∈ range k, (((a : ℝ) + j) ^ e - ((b : ℝ) + j) ^ e) ≤
      ∑ j ∈ range k, ((4 : ℝ) * a) ^ e := by
    apply sum_le_sum
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ k := by
      have := mem_range.1 hj; exact_mod_cast this
    have : ((a : ℝ) + j) ^ e ≤ ((4 : ℝ) * a) ^ e :=
      Real.rpow_le_rpow (by positivity) (by linarith) he0
    have : 0 ≤ ((b : ℝ) + j) ^ e := by positivity
    linarith
  rw [sum_const, card_range, nsmul_eq_mul] at s3
  have h4 : ((4 : ℝ) * a) ^ e ≤ 2 * (2 * a : ℝ) ^ e := by
    rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.mul_rpow (by norm_num) (by positivity)]
    have : (2 : ℝ) ^ e ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) he1
      simpa using this
    have : 0 ≤ (2 * a : ℝ) ^ e := by positivity
    nlinarith
  have hp : 0 ≤ (2 * a : ℝ) ^ e := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  calc _ ≤ _ := s1
    _ ≤ _ := s3
    _ ≤ (k : ℝ) * (2 * (2 * a : ℝ) ^ e) := mul_le_mul_of_nonneg_left h4 hk0
    _ ≤ 4 * (h + 1) * (2 * a : ℝ) ^ e := by nlinarith

/-- The main terms: for real `0 < e ≤ 1` and naturals `b ≤ a`, `1 ≤ h ≤ a`,
`(1/h)(D_e(a+h) - D_e(a) - D_e(b+h) + D_e(b))` is `Σ_{b < n ≤ a} n^e` up to `4 (h + 1) (2a)^e`.
At `e = 1`, `D_1(u) = u³/6`, the pole term. -/
theorem double_diff_main {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a)
    {h : ℝ} (hh1 : 1 ≤ h) (hha : h ≤ a) :
    ‖(Dz (e : ℂ) (a + h) - Dz (e : ℂ) a - Dz (e : ℂ) (b + h) + Dz (e : ℂ) b) / h -
        ∑ n ∈ Ioc b a, (((n : ℝ) ^ e : ℝ) : ℂ)‖ ≤ 4 * (h + 1) * (2 * a : ℝ) ^ e :=
  (double_diff_tele he0.le hb hba (by linarith)).trans (err_sum_le he0.le he1 hb hba hh1 hha)

end LeanLab.Linnik.ExplicitFormula
