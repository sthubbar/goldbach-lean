module

public import Mathlib
public import LeanLab.HelfgottMajor.BookE

/-!
# Helfgott's book, Part IV of 2020-04-01, Lemma 15.23: `E(r)/r` is non-increasing

Unit U-1419, PC run 20261021T1303Z-13145, P0014. AI wrote this file.

`E` is `BookE.E`, the function of (15.2) of the book:
`E(r) = (1/2) arccos(1/υ(r)) - (υ(r) - 1)/r`, `υ(r) = √((1 + √(1 + r²))/2)`.

Method, a rational parametrization. For `0 < t < 1` put
`R(t) = 4t(1 + t²)/(1 - t²)²`, `g(t) = t(1 - t²)/(2(1 + t²))`, `F(t) = arctan t - g(t)`.
Then `√(1 + R²) = (1 + 6t² + t⁴)/(1 - t²)²`, `υ(R(t)) = (1 + t²)/(1 - t²)`,
`arccos(1/υ) = arctan(2t/(1 - t²)) = 2 arctan t`, so `E(R(t)) = F(t)`: `E_Rt`.
`F' = (1 + 6t² + t⁴)/(2(1 + t²)²)`, `R' = 4(1 + 6t² + t⁴)/(1 - t²)³ > 0` and `F'R = R'g`, so
`(F/R)' = R'(2g - arctan t)/R² ≤ 0` by `arctan t ≥ t(1 - t²)/(1 + t²)`, whose difference has
derivative `(5t² + t⁴)/(1 + t²)² ≥ 0`. Since `R` maps `(0,1)` increasingly onto `(0,∞)`,
`E(r)/r` is non-increasing on all of `r > 0`: `lemma_15_23`.

PROVED:
* `arctan_ge_two_g`, `E_Rt`, `G_antitone`, `Rt_strictMono`, `Rt_surj`: the tools;
* `lemma_15_23`: `AntitoneOn (fun r => E r / r) (Ioi 0)`, Lemma 15.23 of the book on its
  whole range;
* `small_p1_all`, `small_p2_all`: (16.61), (16.62) for every `0 < r ≤ 0.001`, which removes
  the CONDITIONAL label of `BookE.small_p1_E`, `BookE.small_p2_E`;
* `E_01`: `E(0.1) ≥ 0.01248`, value 0.0124870200;
* `mid_p2`: `2.72 r^{-1/2} e^{-E(r)/(rπ²)·(125/2)²} ≤ 10⁻¹⁹` for `0.001 ≤ r ≤ 0.1`, the range
  part 2 of Theorem 14.3 leaves out, far below its `1.8019·10⁻¹⁸`.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. AI-written Lean code,
Claude, 2026-10-21.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.BookL1523
open Real Set Finset
open LeanLab.HelfgottMajor.BookE

/-- `R(t) = 4t(1 + t²)/(1 - t²)²`, the radius as a rational function of `t = tan(θ/2)`. -/
noncomputable def Rt (t : ℝ) : ℝ := 4 * t * (1 + t ^ 2) / (1 - t ^ 2) ^ 2

/-- `g(t) = t(1 - t²)/(2(1 + t²))`. -/
noncomputable def gt (t : ℝ) : ℝ := t * (1 - t ^ 2) / (2 * (1 + t ^ 2))

/-- `F(t) = arctan t - g(t)`, so that `E(R(t)) = F(t)`. -/
noncomputable def Ft (t : ℝ) : ℝ := arctan t - gt t

/-- `G(t) = F(t)/R(t) = E(r)/r`. -/
noncomputable def Gt (t : ℝ) : ℝ := Ft t / Rt t

/-- **`arctan t ≥ t(1 - t²)/(1 + t²) = 2g(t)`** for `t ≥ 0`: the derivative of the difference
is `(5t² + t⁴)/(1 + t²)²`. -/
theorem arctan_ge_two_g {t : ℝ} (ht : 0 ≤ t) : 2 * gt t ≤ arctan t := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => arctan x - x * (1 - x ^ 2) / (1 + x ^ 2))
      ((5 * x ^ 2 + x ^ 4) / (1 + x ^ 2) ^ 2) x := by
    intro x
    have h1 : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (hasDerivAt_arctan x).sub
      (((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x))).div
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_pow 2 x)) h1)
    convert h using 1
    · funext y
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
        Nat.cast_ofNat]
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
        Nat.cast_ofNat]
      field_simp
      ring
  have hmono : Monotone (fun x => arctan x - x * (1 - x ^ 2) / (1 + x ^ 2)) := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    positivity
  have := hmono ht
  simp only [arctan_zero] at this
  have e : 2 * gt t = t * (1 - t ^ 2) / (1 + t ^ 2) := by
    unfold gt; field_simp
  rw [e]; norm_num at this; linarith

/-- **`E(R(t)) = F(t)`** for `0 < t < 1`. -/
theorem E_Rt {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : E (Rt t) = Ft t := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hs : √(1 + Rt t ^ 2) = (1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2 := by
    rw [show 1 + Rt t ^ 2 = ((1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2) ^ 2 by
      unfold Rt; field_simp; ring]
    exact sqrt_sq (by positivity)
  have hu : ups (Rt t) = (1 + t ^ 2) / (1 - t ^ 2) := by
    unfold ups; rw [hs]
    rw [show (1 + (1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2) / 2
      = ((1 + t ^ 2) / (1 - t ^ 2)) ^ 2 by field_simp; ring]
    exact sqrt_sq (by positivity)
  have hu1 : 1 ≤ (1 + t ^ 2) / (1 - t ^ 2) := by
    rw [le_div_iff₀ hq]; nlinarith
  unfold E
  rw [hu, arccos_inv hu1]
  have hX : √(((1 + t ^ 2) / (1 - t ^ 2)) ^ 2 - 1) = 2 * t / (1 - t ^ 2) := by
    rw [show ((1 + t ^ 2) / (1 - t ^ 2)) ^ 2 - 1 = (2 * t / (1 - t ^ 2)) ^ 2 by
      field_simp; ring]
    exact sqrt_sq (by positivity)
  rw [hX]
  have h2 : arctan (2 * t / (1 - t ^ 2)) = 2 * arctan t := by
    have := arctan_add (x := t) (y := t) (by nlinarith)
    rw [show (t + t) / (1 - t * t) = 2 * t / (1 - t ^ 2) by ring] at this
    linarith
  rw [h2]
  unfold Ft gt Rt
  have : (1 - t ^ 2) ≠ 0 := hq.ne'
  field_simp
  ring

lemma hasDerivAt_Ft (x : ℝ) :
    HasDerivAt Ft ((1 + 6 * x ^ 2 + x ^ 4) / (2 * (1 + x ^ 2) ^ 2)) x := by
  have h1 : (2 * (1 + x ^ 2)) ≠ 0 := by positivity
  have h := (hasDerivAt_arctan x).sub
    (((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x))).div
      (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_pow 2 x)).const_mul 2) h1)
  convert h using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat]
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat]
    field_simp
    ring

lemma hasDerivAt_Rt {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    HasDerivAt Rt (4 * (1 + 6 * x ^ 2 + x ^ 4) / (1 - x ^ 2) ^ 3) x := by
  have h2 : (1 - x ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h := ((((hasDerivAt_id x).const_mul 4).mul
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_pow 2 x))).div
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).pow 2) h2)
  convert h using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat]
    unfold Rt; ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat]
    field_simp
    ring

/-- **`G = F/R` is non-increasing on `(0,1)`**: `(F/R)' = R'(2g - arctan t)/R² ≤ 0`. -/
theorem G_antitone : AntitoneOn Gt (Ioo 0 1) := by
  have hq : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < 1 - x ^ 2 := fun x hx => by
    obtain ⟨a, b⟩ := hx; nlinarith
  have hR0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < Rt x := fun x hx => by
    have := hq x hx; obtain ⟨a, _⟩ := hx; unfold Rt; positivity
  have hG : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Gt
      (((1 + 6 * x ^ 2 + x ^ 4) / (2 * (1 + x ^ 2) ^ 2) * Rt x -
        Ft x * (4 * (1 + 6 * x ^ 2 + x ^ 4) / (1 - x ^ 2) ^ 3)) / Rt x ^ 2) x := fun x hx =>
    (hasDerivAt_Ft x).div (hasDerivAt_Rt (hq x hx).ne') (hR0 x hx).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · intro x hx; exact (hG x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; intro x hx; exact (hG x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]; intro x hx
    rw [(hG x hx).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have hqx := hq x hx
    have hx0 : 0 < x := hx.1
    have hRp : 0 < 4 * (1 + 6 * x ^ 2 + x ^ 4) / (1 - x ^ 2) ^ 3 := by positivity
    have hid : (1 + 6 * x ^ 2 + x ^ 4) / (2 * (1 + x ^ 2) ^ 2) * Rt x
        = 4 * (1 + 6 * x ^ 2 + x ^ 4) / (1 - x ^ 2) ^ 3 * gt x := by
      unfold Rt gt; field_simp
    have hat := arctan_ge_two_g hx0.le
    rw [hid]
    unfold Ft
    nlinarith

lemma Rt_zero : Rt 0 = 0 := by simp [Rt]

/-- **`R` is strictly increasing on `[0,1)`**. -/
theorem Rt_strictMono : StrictMonoOn Rt (Ico 0 1) := by
  have hq : ∀ x ∈ Ico (0 : ℝ) 1, 0 < 1 - x ^ 2 := fun x hx => by
    obtain ⟨a, b⟩ := hx; nlinarith
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro x hx; exact (hasDerivAt_Rt (hq x hx).ne').continuousAt.continuousWithinAt
  · rw [interior_Ico]; intro x hx
    have hx' : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    rw [(hasDerivAt_Rt (hq x hx').ne').deriv]
    have := hq x hx'
    positivity

/-- **`R` maps `(0,1)` onto `(0,∞)`**: by the intermediate value theorem on `[0, c]` with
`c = 1 - 1/(2(r + 1))`. -/
theorem Rt_surj {r : ℝ} (hr : 0 < r) : ∃ t ∈ Ioo (0 : ℝ) 1, Rt t = r := by
  set d : ℝ := 1 / (2 * (r + 1)) with hd
  have hd0 : 0 < d := by positivity
  have hdr : d * (2 * (r + 1)) = 1 := by rw [hd]; field_simp
  have hd2 : d ≤ 1 / 2 := by nlinarith
  set c : ℝ := 1 - d
  have hc1 : c < 1 := by simp only [c]; linarith
  have hc0 : 1 / 2 ≤ c := by simp only [c]; linarith
  have hqc : 0 < 1 - c ^ 2 := by nlinarith
  have hRc : r ≤ Rt c := by
    unfold Rt
    rw [le_div_iff₀ (by positivity)]
    have e : 1 - c ^ 2 = d * (2 - d) := by simp only [c]; ring
    rw [e]
    have h1 : r * d ≤ 1 / 2 := by nlinarith
    have h2 : (d * (2 - d)) ^ 2 ≤ 4 * d ^ 2 := by nlinarith
    have h3 : r * (d * (2 - d)) ^ 2 ≤ 2 * d := by nlinarith
    nlinarith
  have hcont : ContinuousOn Rt (Icc 0 c) := by
    intro x hx
    have : 0 < 1 - x ^ 2 := by obtain ⟨a, b⟩ := hx; nlinarith
    exact (hasDerivAt_Rt this.ne').continuousAt.continuousWithinAt
  have hivt := intermediate_value_Icc (by linarith) hcont
  rw [Rt_zero] at hivt
  obtain ⟨t, ⟨ht0, htc⟩, htr⟩ := hivt ⟨hr.le, hRc⟩
  refine ⟨t, ⟨?_, by linarith⟩, htr⟩
  rcases ht0.lt_or_eq with h | h
  · exact h
  · rw [← h, Rt_zero] at htr; linarith

/-- **Lemma 15.23 of the book: `E(r)/r` is non-increasing on `r > 0`.** -/
theorem lemma_15_23 : AntitoneOn (fun r => E r / r) (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨ta, hta, hRa⟩ := Rt_surj (r := a) ha
  obtain ⟨tb, htb, hRb⟩ := Rt_surj (r := b) hb
  have hle : ta ≤ tb := by
    by_contra h
    push Not at h
    have := Rt_strictMono ⟨htb.1.le, htb.2⟩ ⟨hta.1.le, hta.2⟩ h
    rw [hRa, hRb] at this
    linarith
  have := G_antitone hta htb hle
  simp only [Gt] at this
  simp only
  rw [← hRa, ← hRb, E_Rt hta.1 hta.2, E_Rt htb.1 htb.2]
  exact this

/-- `E(0.001)/0.001 ≤ E(r)/r` for `0 < r ≤ 0.001`. -/
theorem E_div_ge_001 {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 0.001) :
    E 0.001 / 0.001 ≤ E r / r :=
  lemma_15_23 (show r ∈ Set.Ioi (0 : ℝ) from h0) (show (0.001 : ℝ) ∈ Set.Ioi 0 by norm_num) h1

lemma expo_mono {r K : ℝ} (h0 : 0 < r) (h1 : r ≤ 0.001) :
    E 0.001 / (0.001 * π ^ 2) * K ^ 2 ≤ E r / (r * π ^ 2) * K ^ 2 := by
  have h := E_div_ge_001 h0 h1
  have hp : 0 < π ^ 2 := by positivity
  rw [← div_div, ← div_div]
  gcongr

/-- **(16.61) for every `0 < r ≤ 0.001`**, PROVED: `BookT143.small_p1` with the exponent
`E(r)/(rπ²)·(1375/32)²` bounded below through Lemma 15.23 and `BookE.E_small`. -/
theorem small_p1_all {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 0.001) :
    2.72 * 606.225 * exp (-(E r / (r * π ^ 2) * (1375 / 32) ^ 2)) ≤ 1.15275e-7 :=
  BookT143.small_p1 (E_small.1.trans (expo_mono h0 h1))

/-- **(16.62) for every `0 < r ≤ 0.001`**, PROVED: `BookT143.small_p2` with the exponent
`E(r)/(rπ²)·(125/2)²` bounded below through Lemma 15.23 and `BookE.E_small`. -/
theorem small_p2_all {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 0.001) :
    2.72 * 584.033 * exp (-(E r / (r * π ^ 2) * (125 / 2) ^ 2)) ≤ 5.46217e-19 :=
  BookT143.small_p2 (E_small.2.trans (expo_mono h0 h1))

/-- **`E(0.1) ≥ 0.01248`**; value 0.0124870200. -/
theorem E_01 : 0.01248 ≤ E 0.1 := by
  have hE := E_lower (rL := 0.1) (rU := 0.1) (sL := 1.0049875621)
    (sU := 1.0049875622) (XL := 0.0499377717) (uU := 1.0012461142)
    (by norm_num) le_rfl le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha := BookL1614.arctan_ge_sub_cube (z := 0.0499377717) (by norm_num)
  norm_num at ha hE ⊢
  linarith

/-- **Theorem 14.3 part 2 on `0.001 ≤ r ≤ 0.1`**, the range its proof leaves out:
`2.72 r^{-1/2} e^{-E(r)/(rπ²)·(125/2)²} ≤ 10⁻¹⁹`, via `E(r)/r ≥ E(0.1)/0.1 ≥ 0.1248`, so the
exponent is at least 49.39, and `r^{-1/2} ≤ 31.6228`. -/
theorem mid_p2 {r : ℝ} (h0 : 0.001 ≤ r) (h1 : r ≤ 0.1) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2) ^ 2)) ≤ 1e-19 := by
  have hr0 : 0 < r := by linarith
  have hmono : E 0.1 / 0.1 ≤ E r / r :=
    lemma_15_23 (show r ∈ Set.Ioi (0 : ℝ) from hr0) (show (0.1 : ℝ) ∈ Set.Ioi 0 by norm_num) h1
  have hE := E_01
  have h01 : 0.1248 ≤ E 0.1 / 0.1 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hEr : 0.1248 ≤ E r / r := h01.trans hmono
  have hp := BookE.pi_sq_hi
  have hp0 : 0 < π ^ 2 := by positivity
  have hy : 49.39 ≤ E r / (r * π ^ 2) * (125 / 2) ^ 2 := by
    rw [← div_div, div_mul_eq_mul_div, le_div_iff₀ hp0]
    nlinarith
  have he : (2.0e21 : ℝ) ≤ exp 49.39 := by
    have h := BookT141.exp_lower 49 (r := 0.39) (by norm_num) 8
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hexp : exp (-(E r / (r * π ^ 2) * (125 / 2) ^ 2)) ≤ 1 / 2.0e21 := by
    calc exp (-(E r / (r * π ^ 2) * (125 / 2) ^ 2)) ≤ exp (-49.39) :=
          exp_le_exp.mpr (by linarith)
      _ = 1 / exp 49.39 := by rw [exp_neg, inv_eq_one_div]
      _ ≤ 1 / 2.0e21 := one_div_le_one_div_of_le (by norm_num) he
  have hs : (0.0316227 : ℝ) ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hinv : 1 / √r ≤ 1 / 0.0316227 := one_div_le_one_div_of_le (by norm_num) hs
  have hpos : 0 ≤ exp (-(E r / (r * π ^ 2) * (125 / 2) ^ 2)) := (exp_pos _).le
  calc 2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2) ^ 2))
      ≤ 2.72 * (1 / 0.0316227) * (1 / 2.0e21) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hinv (by norm_num)) hexp hpos
        positivity
    _ ≤ 1e-19 := by norm_num

end LeanLab.HelfgottMajor.BookL1523
