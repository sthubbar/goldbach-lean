module

public import Mathlib
public import LeanLab.ChirreHagen2025.U1348Bilinear

/-!
Unit U-1505, T3 CONNECTION SWEEP, run 20261023T1343Z-19109. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics. Binary Goldbach is OPEN.

Relabel of the P0075 RH Goldbach interval line, I-5171: `goldbach_445_of_J` of
ChirreHagen2025/U1348Goldbach.lean takes `hS : RiemannHypothesis → SchoenfeldTheta`, Schoenfeld
1976 Corollary 1 CITED, and uses it only through `thetaRel6_of_schoenfeld (hS hRH)`, that is only
at `u ≥ 10^16`. PNTPort/ExplicitPsi1/ThetaSchoenfeldLarge.lean `theta_schoenfeld_large` already
PROVES the same bound for `u ≥ 10^11` under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`.

* `thetaRel6_of_large`: `ThetaRel6` from the Schoenfeld bound on `u ≥ 10^11` only. PROVED, the
  proof of `thetaRel6_of_schoenfeld` with the hypothesis narrowed.
* `goldbach_of_J_T6`, `goldbach_445_of_J_T6`: `goldbach_of_J` and `goldbach_445_of_J` with `hS`
  replaced by `hT : RiemannHypothesis → ThetaRel6`; proofs copied, one term swapped.
The composition with `theta_schoenfeld_large` is the one line
`fun hRH => thetaRel6_of_large (fun u hu => theta_schoenfeld_large hRH hN hH h14 hu)`, written
in U1505Theta6HSW.lean, which imports the PNTPort explicit formula chain.
-/

@[expose] public section

namespace LeanLab.Routes.U1505
open Real Chebyshev
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.U1348

/-- `ThetaRel6` from `|θ(u) - u| ≤ √u log² u/(8π)` on `u ≥ 10^11`. -/
theorem thetaRel6_of_large
    (h : ∀ u : ℝ, 10 ^ 11 ≤ u → |θ u - u| ≤ √u * Real.log u ^ 2 / (8 * π)) : ThetaRel6 := by
  intro u hu
  have hu0 : 0 < u := by linarith
  refine le_trans (h u (by linarith)) ?_
  set w := √u with hw
  have hw2 : w ^ 2 = u := Real.sq_sqrt hu0.le
  have hw8 : (10 : ℝ) ^ 8 ≤ w := by
    rw [hw, Real.le_sqrt (by positivity) hu0.le]; norm_num at hu ⊢; linarith
  have hw0 : 0 < w := by linarith
  have hlog : Real.log u = 2 * Real.log w := by
    rw [hw, Real.log_sqrt hu0.le]; ring
  have he2 : Real.exp 2 ≤ (10 : ℝ) ^ 8 := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 10 ^ 8 := by norm_num
  have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.mpr he2)
    (Set.mem_Ici.mpr (le_trans he2 hw8)) hw8
  simp only at hanti
  have hs8 : √((10 : ℝ) ^ 8) = 10 ^ 4 := by
    rw [show (10 : ℝ) ^ 8 = (10 ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs8] at hanti
  have hl0 : 0 ≤ Real.log w / √w := div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hb : Real.log w / √w ≤ 19 / 10 ^ 4 :=
    le_trans hanti (div_le_div_of_nonneg_right log_1e8_le (by norm_num))
  have hsq := pow_le_pow_left₀ hl0 hb 2
  rw [div_pow, Real.sq_sqrt hw0.le] at hsq
  have e : √u * Real.log u ^ 2 = 4 * u * (Real.log w ^ 2 / w) := by
    rw [← hw, hlog, ← hw2]; field_simp; ring
  rw [e]
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : 4 * u * (Real.log w ^ 2 / w) ≤ 4 * u * ((19 / 10 ^ 4) ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  nlinarith

theorem goldbach_of_J_T6 {J H : ℝ} (hJ0 : 0 ≤ J) (hH1 : 4 ≤ H) (hH : H ≤ 61.5)
    (hm : (1.001 * J + 0.0019) * 0.24922 < H * ((11 / 5 * (((5 / 11) ^ 3 - (1 / 64) ^ 3) / 3
        - ((5 / 11) ^ 4 - (1 / 64) ^ 4) / 4)
      + (((1 / 2) ^ 2 - (5 / 11) ^ 2) / 2 - ((1 / 2) ^ 3 - (5 / 11) ^ 3) / 3))
      - (11 / 10 * (10 * (5 / 11 - 1 / 64) + 2 * (5 / 11) + 2 * (1 / 64))
        + (3 * (1 / 2 - 5 / 11) + 2 * (1 / 2) + 2 * (5 / 11))
        + 11 / 10 * (16 * (63 / 64 - 6 / 11) + 2 * (63 / 64) + 2 * (6 / 11))
        + (3 * (6 / 11 - 1 / 2) + 2 * (6 / 11) + 2 * (1 / 2))) / 10 ^ 6))
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ J * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hT : RiemannHypothesis → ThetaRel6) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + (H + 1 / 100) * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x (by linarith) hs
    exact ⟨n, hn, h1, by nlinarith [hlog]⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := H * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := div_pos (mul_pos (by linarith) (by positivity)) hxpos
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith [sq_nonneg (Real.log x)]
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = H * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = H * (Real.log x ^ 2 / √x) := by
        rw [show H * (Real.log x ^ 2 / √x) = H * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have h4 : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      have h5 : 0 ≤ Real.log x ^ 2 / √x := by positivity
      rw [e]
      have : H * (Real.log x ^ 2 / √x) ≤ 61.5 * (7.5 / 10 ^ 5) :=
        mul_le_mul hH h4 h5 (by norm_num)
      linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_u1348 (c := 1.001 * J + 0.0019) (H := H)
      (by linarith) (by linarith) hH hm (hT hRH) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_of_c hJ0 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith [sq_nonneg (Real.log x)]⟩

theorem goldbach_445_of_J_T6
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hT : RiemannHypothesis → ThetaRel6) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 := by
  have := goldbach_of_J_T6 (J := 1.0069) (H := 4.44) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h2 hE hT
  intro hRH x hx
  obtain ⟨n, hn, h1, h3⟩ := this hRH x hx
  have e : (4.44 : ℝ) + 1 / 100 = 4.45 := by norm_num
  rw [e] at h3
  exact ⟨n, hn, h1, h3⟩

end LeanLab.Routes.U1505

