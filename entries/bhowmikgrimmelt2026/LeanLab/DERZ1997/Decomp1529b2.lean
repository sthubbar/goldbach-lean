module

public import LeanLab.DERZ1997.Decomp1529b
public import LeanLab.Routes.Decomp1551a
public import LeanLab.PNTPort.ExplicitPsi1.Final

/-!
Perron cutoff and finite height transfers for the DERZ1997 explicit formula decomposition.
These are auxiliary derivations. They do not assert the sealed constant 1000.
Published zero-count inputs remain explicit premises or existing named leaves.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.DERZ1997.Decomp1529b2
open Complex Real MeasureTheory Set Filter Topology
open LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp1529b

/-- Perron's error at arbitrary noninteger x.
Auxiliary derivation for Davenport chapter 17 pages 105 to 109. -/
theorem perron_error_arbitrary266 {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T)
    (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) :
    ‖(Chebyshev.psi x : ℂ) - perronPsi x (1 + 1 / Real.log x) T‖ ≤
      432 * (x * Real.log x ^ 2 / T + Real.log x) := by
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 1 < 1 + 1 / Real.log x := by linarith [one_div_pos.mpr hL]
  have hh := (perron_psi hx hxn hc (by linarith : 0 < T)).trans (perron_tail_arbitrary266 hx hT)
  exact hh.trans (by nlinarith)

/-- Explicit formula at arbitrary noninteger x and separated height, with an absolute constant.
Auxiliary derivation for Davenport chapter 17 pages 105 to 109.
This retains the exact separation premise and does not assert the sealed constant 1000. -/
theorem explicit_formula_noninteger_good266 : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    T ≤ x → (∀ n : ℕ, (n : ℝ) ≠ x) →
    (∀ ρ ∈ LeanLab.DERZ1997.Decomp1529a.zetaZeros (T+1),
      1/(100*Real.log T) ≤ |ρ.im-T|) →
    ∀ hfin : (LeanLab.DERZ1997.Decomp1529a.zetaZeros T).Finite,
      ‖(Chebyshev.psi x:ℂ) - x + ∑ ρ ∈ hfin.toFinset,
        (LeanLab.DERZ1997.Decomp1529a.zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ‖ ≤
          C * (x*Real.log x^2/T + Real.log x) := by
  let A : ℝ := 432
  obtain ⟨B,hB⟩ := contour_shift
  let K : ℝ := |Real.log (2*Real.pi)|+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨|A|+|B|+2*K, ?_⟩
  intro x T hx hT hTx hxn hsep hfin
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1/2 ≤ Real.log x := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < Real.log x := by linarith
  let c : ℝ := 1+1/Real.log x
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hL0]
  let E : ℝ := x*Real.log x^2/T + Real.log x
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hper : ‖(Chebyshev.psi x:ℂ)-perronPsi x c T‖ ≤ |A| *E := by
    have hh := perron_error_arbitrary266 hx hT hxn
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self A) hE0)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogTx : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
  have hratio : x*Real.log T^2/T ≤ E := by
    have hh : Real.log T^2 ≤ Real.log x^2 := pow_le_pow_left₀ hlogT hlogTx 2
    have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hx0.le) hT0.le
    dsimp [E]; linarith
  let Z : ℂ := ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ
  let M : ℂ := (x:ℂ)-Z-Real.log (2*Real.pi)-(1/2:ℂ)*Real.log (1-x^(-2:ℤ))
  have hcont : ‖perronPsi x c T-M‖ ≤ |B| *E := by
    have hh := hB x T hx hT hsep hfin
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hratio (abs_nonneg B)))
  have hw : 1/2 ≤ 1-x^(-2:ℤ) := by
    have hs : 2 ≤ x^2 := by nlinarith
    have hi : (x^2)⁻¹ ≤ (2:ℝ)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hs
    simp only [zpow_neg, zpow_ofNat] at *
    norm_num at hi
    linarith
  have hw1 : 1-x^(-2:ℤ) ≤ 1 := by
    have : 0 ≤ x^(-2:ℤ) := by positivity
    linarith
  have hcorr : |Real.log (1-x^(-2:ℤ))| ≤ 1 := by
    have hlo := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1-x^(-2:ℤ))
    have hi : (1-x^(-2:ℤ))⁻¹ ≤ (1/2:ℝ)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hw
    have hhi := Real.log_nonpos (by linarith : 0 ≤ 1-x^(-2:ℤ)) hw1
    rw [abs_of_nonpos hhi]
    norm_num only [one_div, inv_inv] at hi
    linarith
  simp only [zpow_neg, zpow_ofNat] at hcorr
  have hcorrection : ‖(Real.log (2*Real.pi):ℂ)+(1/2:ℂ)*Real.log (1-x^(-2:ℤ))‖ ≤ K := by
    calc
      _ ≤ ‖(Real.log (2*Real.pi):ℂ)‖+‖(1/2:ℂ)*Real.log (1-x^(-2:ℤ))‖ := norm_add_le _ _
      _ ≤ K := by
        norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        dsimp [K]
        linarith
  have hElog : Real.log x ≤ E := by
    have : 0 ≤ x*Real.log x^2/T := by positivity
    dsimp [E]; linarith
  have hKE : K ≤ 2*K*E := by nlinarith
  have heq : (Chebyshev.psi x:ℂ)-x+Z = ((Chebyshev.psi x:ℂ)-perronPsi x c T)+
      (perronPsi x c T-M)-((Real.log (2*Real.pi):ℂ)+(1/2:ℂ)*Real.log (1-x^(-2:ℤ))) := by
    dsimp [M]; ring
  change ‖(Chebyshev.psi x:ℂ)-x+Z‖ ≤ (|A|+|B|+2*K)*E
  rw [heq]
  calc
    _ ≤ (‖(Chebyshev.psi x:ℂ)-perronPsi x c T‖+‖perronPsi x c T-M‖)+
        ‖(Real.log (2*Real.pi):ℂ)+(1/2:ℂ)*Real.log (1-x^(-2:ℤ))‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |A| * E + |B| * E + 2 * K * E :=
      add_le_add (add_le_add hper hcont) (hcorrection.trans hKE)
    _ = _ := by ring

/-- Explicit formula for all real x at separated height, with an absolute constant.
The integer endpoint follows by a right limit.
Auxiliary derivation for Davenport chapter 17 pages 105 to 109. -/
theorem explicit_formula_good266 : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    T ≤ x → (∀ ρ ∈ zetaZeros (T+1), 1/(100*Real.log T) ≤ |ρ.im-T|) →
    ∀ hfin : (zetaZeros T).Finite,
      ‖(Chebyshev.psi x:ℂ) - x + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ:ℂ)*(x:ℂ)^ρ/ρ‖ ≤
        C * (x*Real.log x^2/T + Real.log x) := by
  obtain ⟨C, hC⟩ := explicit_formula_noninteger_good266
  refine ⟨C, ?_⟩
  intro x T hx hT hTx hsep hfin
  by_cases hnat : ∃ N : ℕ, (N : ℝ) = x
  · obtain ⟨N, rfl⟩ := hnat
    have hN : 2 ≤ N := by exact_mod_cast hx
    have hlocal : ∀ y : ℝ, (N : ℝ) < y → y < (N : ℝ) + 1 →
        ‖(Chebyshev.psi y : ℂ) - y + ∑ ρ ∈ hfin.toFinset,
          (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ C * (y * Real.log y ^ 2 / T + Real.log y) := by
      intro y hy hy1
      apply hC y T (by linarith) hT (by linarith) _ hsep hfin
      intro n hn
      have h0 : N < n := by exact_mod_cast (show (N : ℝ) < n by simpa only [hn] using hy)
      have h1 : n < N + 1 := by exact_mod_cast (show (n : ℝ) < (N : ℝ) + 1 by simpa only [hn] using hy1)
      omega
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hpow (ρ : ℂ) : ContinuousAt (fun y : ℝ => (y : ℂ) ^ ρ) (N : ℝ) :=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hN0)).comp
        Complex.continuous_ofReal.continuousAt
    have hsum : ContinuousAt (fun y : ℝ => ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ) (N : ℝ) := by
      apply tendsto_finsetSum hfin.toFinset
      intro ρ hρ
      exact (continuousAt_const.mul (hpow ρ)).div_const ρ
    have hleft : ContinuousAt (fun y : ℝ =>
        ‖(Chebyshev.psi N : ℂ) - y + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖) (N : ℝ) :=
      ((continuousAt_const.sub Complex.continuous_ofReal.continuousAt).add hsum).norm
    have hright : ContinuousAt (fun y : ℝ => C * (y * Real.log y ^ 2 / T + Real.log y)) (N : ℝ) := by
      fun_prop (disch := exact hN0.ne')
    apply le_of_tendsto_of_tendsto (b := 𝓝[>] (N : ℝ)) (hleft.tendsto.mono_left inf_le_left)
      (hright.tendsto.mono_left inf_le_left)
    filter_upwards [Ioo_mem_nhdsGT (show (N : ℝ) < N + 1 by linarith)] with y hy
    have hfloor : ⌊y⌋₊ = N := (Nat.floor_eq_iff (by linarith [hy.1, Nat.cast_nonneg (α := ℝ) N])).mpr ⟨hy.1.le, hy.2⟩
    have hpsi : Chebyshev.psi y = Chebyshev.psi N := by
      rw [Chebyshev.psi_eq_psi_coe_floor, hfloor]
    simpa only [hpsi] using hlocal y hy.1 hy.2
  · apply hC x T hx hT hTx _ hsep hfin
    intro n hn
    exact hnat ⟨n, hn⟩

end LeanLab.DERZ1997.Decomp1529b2
