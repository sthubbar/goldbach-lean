module

public import LeanLab.PNTPort.LargeSieve.Bilinear
public import LeanLab.PNTPort.Perron.Cutoff

/-!
# The hyperbolic bilinear large sieve

Lab proof, AI wrote this file, known mathematics, no cited input.

`hyperbolic_large_sieve`: the bilinear large sieve with the extra hyperbolic cutoff `m n ≤ X`,

  `∑_{q ≤ Q} W(q) ∑_{χ prim} ‖∑_{m,n, mn ≤ X} a_m b_n χ(mn)‖
     ≤ C₀ (1 + log X + log(1 + N₁ + N₂ + M₁ + M₂)) √((N₁ + 2Q²)‖a‖²(N₂ + 2Q²)‖b‖²)
       + C₀ Q² ‖a‖₁ ‖b‖₁ / X`.

Route: the truncated Perron cutoff `perron_cutoff` with `X' = ⌊X⌋ + 1/2`, `T = X²`,
separating `1_{mn ≤ X}` as `∫_{-T}^{T} (mn)^{it} e^{-i c t} K(t) dt` up to `O(X'/T)`,
then `bilinear_large_sieve` at each fixed `t` and `integral_abs_sin_div_le`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset MeasureTheory
open LeanLab.PNTPort.LargeSieve (primIdx bilinear_large_sieve mls_primIdx)

noncomputable section

/-- The shifted cutoff point `⌊X⌋ + 1/2`. -/
def hypX (X : ℝ) : ℝ := (⌊X⌋ : ℝ) + 1 / 2
/-- The centre of the log window. -/
def hypC (X : ℝ) : ℝ := (Real.log (hypX X) + Real.log (1 / 2)) / 2
/-- The half width of the log window. -/
def hypB (X : ℝ) : ℝ := (Real.log (hypX X) - Real.log (1 / 2)) / 2

lemma hypX_bounds {X : ℝ} (hX : 2 ≤ X) :
    X - 1 / 2 < hypX X ∧ hypX X ≤ X + 1 / 2 ∧ 5 / 2 ≤ hypX X := by
  have h1 := Int.floor_le X
  have h2 := Int.lt_floor_add_one X
  have h3 : (2 : ℤ) ≤ ⌊X⌋ := Int.le_floor.2 (by simpa using hX)
  have h3' : (2 : ℝ) ≤ ⌊X⌋ := by exact_mod_cast h3
  unfold hypX
  refine ⟨by linarith, by linarith, by linarith⟩

lemma log_half : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]

lemma hypB_pos {X : ℝ} (hX : 2 ≤ X) : 0 < hypB X := by
  obtain ⟨-, -, h⟩ := hypX_bounds hX
  unfold hypB
  have : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have : 0 < Real.log (hypX X) := Real.log_pos (by linarith)
  linarith

lemma gap_in {X : ℝ} (hX : 2 ≤ X) {k : ℤ} (hk : 1 ≤ k) (hkX : (k : ℝ) ≤ X) :
    |Real.log k - hypC X| + 1 / (4 * hypX X) ≤ hypB X := by
  obtain ⟨h1, h2, h3⟩ := hypX_bounds hX
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkf : k ≤ ⌊X⌋ := Int.le_floor.2 hkX
  have hkf' : (k : ℝ) ≤ ⌊X⌋ := by exact_mod_cast hkf
  have hkX' : (k : ℝ) ≤ hypX X - 1 / 2 := by unfold hypX; linarith
  have hlog2 := Real.log_two_gt_d9
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk'
  have hpos : 0 < hypX X := by linarith
  have key : Real.log k ≤ Real.log (hypX X) - 1 / (2 * hypX X) := by
    have a1 : Real.log k ≤ Real.log (hypX X - 1 / 2) := Real.log_le_log (by linarith) hkX'
    have a2 : Real.log ((hypX X - 1 / 2) / hypX X) ≤ (hypX X - 1 / 2) / hypX X - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) hpos)
    rw [Real.log_div (by linarith) hpos.ne'] at a2
    have a3 : (hypX X - 1 / 2) / hypX X - 1 = -(1 / (2 * hypX X)) := by field_simp; ring
    linarith
  have hd : 1 / (4 * hypX X) ≤ 1 / (2 * hypX X) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hd2 : 1 / (4 * hypX X) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hab : |Real.log k - hypC X| ≤ hypB X - 1 / (4 * hypX X) := by
    unfold hypC hypB
    rw [log_half]
    rw [abs_le]
    constructor <;> linarith
  linarith

lemma gap_out {X : ℝ} (hX : 2 ≤ X) {k : ℤ} (hkX : ¬ (k : ℝ) ≤ X) :
    hypB X + 1 / (4 * hypX X) ≤ |Real.log k - hypC X| := by
  obtain ⟨h1, h2, h3⟩ := hypX_bounds hX
  have hkf : ⌊X⌋ < k := Int.floor_lt.2 (lt_of_not_ge hkX)
  have hkf2 : ⌊X⌋ + 1 ≤ k := hkf
  have hkf' : (⌊X⌋ : ℝ) + 1 ≤ k := by exact_mod_cast hkf2
  have hkX' : hypX X + 1 / 2 ≤ (k : ℝ) := by unfold hypX; linarith
  have hpos : 0 < hypX X := by linarith
  have key : Real.log (hypX X) + 1 / (4 * hypX X) ≤ Real.log k := by
    have a1 : Real.log (hypX X + 1 / 2) ≤ Real.log k := Real.log_le_log (by linarith) hkX'
    have a2 : 1 - ((hypX X + 1 / 2) / hypX X)⁻¹ ≤ Real.log ((hypX X + 1 / 2) / hypX X) :=
      Real.one_sub_inv_le_log_of_pos (div_pos (by linarith) hpos)
    rw [Real.log_div (by linarith) hpos.ne'] at a2
    have a3 : 1 / (4 * hypX X) ≤ 1 - ((hypX X + 1 / 2) / hypX X)⁻¹ := by
      rw [inv_div]
      have : 1 - hypX X / (hypX X + 1 / 2) = (1 / 2) / (hypX X + 1 / 2) := by
        field_simp; ring
      rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  refine le_trans ?_ (le_abs_self _)
  unfold hypC hypB
  rw [log_half] at *
  linarith

/-- One application of the Perron cutoff, at an integer `k ≥ 1`. -/
lemma cutoff_point {C : ℝ} (hC : 0 < C)
    (hP : ∀ T : ℝ, 1 ≤ T → ∀ β : ℝ, 0 < β → ∀ α : ℝ, |α| ≠ β →
      ‖(∫ t in (-T)..T, Complex.exp (Complex.I * (α * t : ℝ)) *
        ((Real.sin (β * t) / (Real.pi * t) : ℝ) : ℂ))
        - (if |α| < β then (1 : ℂ) else 0)‖ ≤ C / (T * |(|α| - β)|))
    {X : ℝ} (hX : 2 ≤ X) {T : ℝ} (hT : 1 ≤ T) {k : ℤ} (hk : 1 ≤ k) :
    ‖(∫ t in (-T)..T, Complex.exp (Complex.I * ((Real.log k - hypC X) * t : ℝ)) *
        ((Real.sin (hypB X * t) / (Real.pi * t) : ℝ) : ℂ))
        - (if (k : ℝ) ≤ X then (1 : ℂ) else 0)‖ ≤ C / (T * (1 / (4 * hypX X))) := by
  obtain ⟨h1, h2, h3⟩ := hypX_bounds hX
  have hβ := hypB_pos hX
  have hδ : 0 < 1 / (4 * hypX X) := by positivity
  have hT0 : 0 < T := by linarith
  have fin : ∀ d : ℝ, 1 / (4 * hypX X) ≤ d → C / (T * d) ≤ C / (T * (1 / (4 * hypX X))) := by
    intro d hd
    apply div_le_div_of_nonneg_left hC.le (by positivity)
    exact mul_le_mul_of_nonneg_left hd hT0.le
  by_cases hkX : (k : ℝ) ≤ X
  · have g := gap_in hX hk hkX
    have hlt : |Real.log k - hypC X| < hypB X := by linarith
    have := hP T hT (hypB X) hβ (Real.log k - hypC X) hlt.ne
    rw [if_pos hlt] at this
    rw [if_pos hkX]
    refine this.trans (fin _ ?_)
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · have g := gap_out hX hkX
    have hlt : ¬ |Real.log k - hypC X| < hypB X := by linarith
    have hne : |Real.log k - hypC X| ≠ hypB X := by intro h; linarith
    have := hP T hT (hypB X) hβ (Real.log k - hypC X) hne
    rw [if_neg hlt] at this
    rw [if_neg hkX]
    refine this.trans (fin _ ?_)
    rw [abs_of_pos (by linarith)]
    linarith

/-- Integrability of the kernel. -/
lemma kernel_integrable {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    IntervalIntegrable (fun t => ((Real.sin (β * t) / (Real.pi * t) : ℝ) : ℂ)) volume (-T) T ∧
    IntervalIntegrable (fun t => |Real.sin (β * t) / (Real.pi * t)|) volume (-T) T := by
  have hb : ∀ t, |Real.sin (β * t) / (Real.pi * t)| ≤ 2 / Real.pi * β := by
    intro t
    refine (LeanLab.PNTPort.Perron.abs_sin_div_le β t hβ).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg t, mul_nonneg hβ.le (abs_nonneg t)]
  have hm : Measurable fun t => Real.sin (β * t) / (Real.pi * t) := by fun_prop
  constructor
  · refine IntervalIntegrable.mono_fun' (g := fun _ => 2 / Real.pi * β)
      intervalIntegrable_const ?_ ?_
    · exact (Complex.measurable_ofReal.comp hm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        simp only [Complex.norm_real, Real.norm_eq_abs]; exact hb t
  · refine IntervalIntegrable.mono_fun' (g := fun _ => 2 / Real.pi * β)
      intervalIntegrable_const ?_ ?_
    · exact (hm.abs).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        simp only [Real.norm_eq_abs, abs_abs]; exact hb t

lemma norm_exp_I_mul (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

/-- **The hyperbolic bilinear large sieve.** -/
theorem hyperbolic_large_sieve : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (Q : ℕ), 1 ≤ Q →
    ∀ (M₁ M₂ : ℤ) (N₁ N₂ : ℕ), 0 ≤ M₁ → 0 ≤ M₂ → ∀ (a b : ℤ → ℂ),
    ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂),
        (if ((m * n : ℤ) : ℝ) ≤ X then a m * b n * i.2 ((m * n : ℤ)) else 0)‖ ≤
      C₀ * (1 + Real.log X + Real.log (1 + N₁ + N₂ + M₁ + M₂)) *
        Real.sqrt (((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖ ^ 2) *
          ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖ ^ 2))
      + C₀ * (Q : ℝ) ^ 2 * (∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖) * (∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖) / X := by
  obtain ⟨C, hC, hP⟩ := LeanLab.PNTPort.Perron.perron_cutoff
  refine ⟨8 + 24 * C, by positivity, ?_⟩
  intro X hX Q hQ M₁ M₂ N₁ N₂ hM₁ hM₂ a b
  obtain ⟨hX1, hX2, hX3⟩ := hypX_bounds hX
  have hX0 : 0 < X := by linarith
  set I₁ := Ioc M₁ (M₁ + N₁) with hI₁
  set I₂ := Ioc M₂ (M₂ + N₂) with hI₂
  have hm1 : ∀ m ∈ I₁, 1 ≤ m := fun m hm => by rw [hI₁, mem_Ioc] at hm; omega
  have hn1 : ∀ n ∈ I₂, 1 ≤ n := fun n hn => by rw [hI₂, mem_Ioc] at hn; omega
  set T : ℝ := X ^ 2 with hTdef
  have hT : 1 ≤ T := by nlinarith
  have hTT : -T ≤ T := by linarith
  set β := hypB X with hβdef
  have hβ : 0 < β := hypB_pos hX
  set c := hypC X with hcdef
  set K : ℝ → ℝ := fun t => Real.sin (β * t) / (Real.pi * t) with hK
  obtain ⟨hKc, hKa⟩ := kernel_integrable hβ T
  set E : ℝ := C / (T * (1 / (4 * hypX X))) with hE
  set A₁ := ∑ m ∈ I₁, ‖a m‖ with hA₁
  set B₁ := ∑ n ∈ I₂, ‖b n‖ with hB₁
  set P := ((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ I₁, ‖a m‖ ^ 2) *
    ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ I₂, ‖b n‖ ^ 2) with hPdef
  set e : ℝ → ℤ → ℂ := fun t m => Complex.exp (Complex.I * ((t * Real.log m : ℝ))) with he
  have hen : ∀ t m, ‖e t m‖ = 1 := fun t m => norm_exp_I_mul _
  set G : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ → ℂ := fun i t =>
    ∑ m ∈ I₁, ∑ n ∈ I₂, (a m * e t m) * (b n * e t n) * i.2 ((m * n : ℤ)) with hG
  have hGc : ∀ i, Continuous (G i) := by
    intro i; simp only [hG, he]; fun_prop

  -- the integrand identity
  have hfac : ∀ (χ : ℤ → ℂ) (m n : ℤ), 1 ≤ m → 1 ≤ n → ∀ t : ℝ,
      a m * b n * χ (m * n) * (Complex.exp (Complex.I *
        ((Real.log ((m * n : ℤ) : ℝ) - c) * t : ℝ)) * (K t : ℂ)) =
      (a m * e t m) * (b n * e t n) * χ (m * n) *
        (Complex.exp (Complex.I * ((-c * t : ℝ))) * (K t : ℂ)) := by
    intro χ m n hm hn t
    have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm' : (m : ℝ) ≠ 0 := by linarith
    have hn' : (n : ℝ) ≠ 0 := by linarith
    have hl : Real.log ((m * n : ℤ) : ℝ) = Real.log m + Real.log n := by
      push_cast; exact Real.log_mul hm' hn'
    have hsplit : Complex.I * (((Real.log ((m * n : ℤ) : ℝ) - c) * t : ℝ) : ℂ) =
        Complex.I * ((t * Real.log m : ℝ) : ℂ) + Complex.I * ((t * Real.log n : ℝ) : ℂ) +
          Complex.I * ((-c * t : ℝ) : ℂ) := by
      rw [hl]; push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_add]
    simp only [he]
    ring
  -- per character bound
  have hchar : ∀ i ∈ primIdx Q,
      ‖∑ m ∈ I₁, ∑ n ∈ I₂,
        (if ((m * n : ℤ) : ℝ) ≤ X then a m * b n * i.2 ((m * n : ℤ)) else 0)‖ ≤
      (∫ t in (-T)..T, ‖G i t‖ * |K t|) + E * (A₁ * B₁) := by
    intro i _
    set χ : ℤ → ℂ := fun x => i.2 x with hχ
    set J : ℤ → ℂ := fun k => ∫ t in (-T)..T,
      Complex.exp (Complex.I * ((Real.log (k : ℝ) - c) * t : ℝ)) * (K t : ℂ) with hJ
    have hJb : ∀ k : ℤ, 1 ≤ k →
        ‖J k - (if (k : ℝ) ≤ X then (1 : ℂ) else 0)‖ ≤ E :=
      fun k hk => cutoff_point hC hP hX hT hk
    have hsum : ∀ m n : ℤ,
        (if ((m * n : ℤ) : ℝ) ≤ X then a m * b n * i.2 ((m * n : ℤ)) else 0) =
        a m * b n * χ (m * n) * J (m * n) -
          a m * b n * χ (m * n) * (J (m * n) - (if ((m * n : ℤ) : ℝ) ≤ X then 1 else 0)) := by
      intro m n; simp only [hχ]; split_ifs <;> ring
    simp_rw [hsum, sum_sub_distrib]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · -- main part
      rw [← sum_product']
      have hint : ∀ p ∈ I₁ ×ˢ I₂, IntervalIntegrable (fun t => a p.1 * b p.2 * χ (p.1 * p.2) *
          (Complex.exp (Complex.I * ((Real.log ((p.1 * p.2 : ℤ) : ℝ) - c) * t : ℝ)) * (K t : ℂ)))
          volume (-T) T := by
        intro p _
        exact (hKc.continuousOn_mul (by fun_prop)).const_mul _
      have : ∑ p ∈ I₁ ×ˢ I₂, a p.1 * b p.2 * χ (p.1 * p.2) * J (p.1 * p.2) =
          ∫ t in (-T)..T, ∑ p ∈ I₁ ×ˢ I₂, a p.1 * b p.2 * χ (p.1 * p.2) *
          (Complex.exp (Complex.I * ((Real.log ((p.1 * p.2 : ℤ) : ℝ) - c) * t : ℝ)) * (K t : ℂ)) := by
        rw [intervalIntegral.integral_finset_sum hint]
        apply sum_congr rfl; intro p _
        rw [hJ, intervalIntegral.integral_const_mul]
      rw [this]
      refine intervalIntegral.norm_integral_le_of_norm_le hTT
        (Filter.Eventually.of_forall fun t _ => le_of_eq ?_)
        ((hKa.continuousOn_mul ((hGc i).norm.continuousOn)))
      rw [Finset.sum_product, hG]
      simp only []
      rw [sum_congr rfl (fun m hm => sum_congr rfl (fun n hn =>
        hfac χ m n (hm1 m hm) (hn1 n hn) t))]
      simp_rw [← sum_mul]
      rw [norm_mul, norm_mul, norm_exp_I_mul, one_mul, Complex.norm_real, Real.norm_eq_abs]
    · -- error part
      refine (norm_sum_le _ _).trans ?_
      rw [hA₁, hB₁, sum_mul_sum, mul_sum]
      apply sum_le_sum; intro m hm
      refine (norm_sum_le _ _).trans ?_
      rw [mul_sum]
      apply sum_le_sum; intro n hn
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖χ (m * n)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have h2 := hJb (m * n) (by nlinarith [hm1 m hm, hn1 n hn])
      have : ‖a m‖ * ‖b n‖ * ‖χ (m * n)‖ ≤ ‖a m‖ * ‖b n‖ :=
        mul_le_of_le_one_right (by positivity) h1
      calc _ ≤ ‖a m‖ * ‖b n‖ * E := mul_le_mul this h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring

  -- the large sieve at each fixed t
  have hW : ∀ i ∈ primIdx Q, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hpt : ∀ t, ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖G i t‖ ≤
      Real.sqrt P := by
    intro t
    have h := bilinear_large_sieve hQ (fun m => a m * e t m) (fun n => b n * e t n) M₁ M₂ N₁ N₂
    simp only [norm_mul, hen, mul_one] at h
    exact Real.le_sqrt_of_sq_le h
  -- the sum of the weights
  have hWs : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient ≤ 1 + 2 * (Q : ℝ) ^ 2 := by
    have h := mls_primIdx hQ (fun _ => (1 : ℂ)) 0 1
    have hI : Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
    rw [hI] at h
    simpa using h
  -- integrability of the real integrands
  have hGi : ∀ i, IntervalIntegrable (fun t => ‖G i t‖ * |K t|) volume (-T) T :=
    fun i => hKa.continuousOn_mul ((hGc i).norm.continuousOn)
  have hmain : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      (∫ t in (-T)..T, ‖G i t‖ * |K t|) ≤ Real.sqrt P * (2 * (1 + Real.log (1 + β * T))) := by
    have e1 : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        (∫ t in (-T)..T, ‖G i t‖ * |K t|) = ∫ t in (-T)..T, ∑ i ∈ primIdx Q,
          ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (‖G i t‖ * |K t|) := by
      rw [intervalIntegral.integral_finset_sum (fun i _ => (hGi i).const_mul _)]
      apply sum_congr rfl; intro i _
      rw [intervalIntegral.integral_const_mul]
    rw [e1]
    have e2 : ∫ t in (-T)..T, ∑ i ∈ primIdx Q,
          ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (‖G i t‖ * |K t|) ≤
        ∫ t in (-T)..T, Real.sqrt P * |K t| := by
      apply intervalIntegral.integral_mono_on hTT
      · convert IntervalIntegrable.sum (primIdx Q) (fun i _ => (hGi i).const_mul
          (((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient)) using 1
        ext t; rw [Finset.sum_apply]
      · exact hKa.const_mul _
      · intro t _
        have : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (‖G i t‖ * |K t|) =
            (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖G i t‖) * |K t| := by
          rw [sum_mul]; apply sum_congr rfl; intro i _; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (hpt t) (abs_nonneg _)
    refine e2.trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (LeanLab.PNTPort.Perron.integral_abs_sin_div_le T hT β hβ) (Real.sqrt_nonneg _)
  -- numerics
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hβX : β ≤ X := by
    rw [hβdef]; unfold hypB; rw [log_half]
    have := Real.log_le_sub_one_of_pos (show 0 < hypX X by linarith)
    have := Real.log_two_lt_d9
    norm_num at *
    linarith
  have hlogT : Real.log (1 + β * T) ≤ 4 * Real.log X := by
    have h4 : Real.log (X ^ 4) = 4 * Real.log X := by rw [Real.log_pow]; norm_num
    rw [← h4]
    apply Real.log_le_log (by positivity)
    have : β * T ≤ X ^ 3 := by rw [hTdef]; nlinarith
    have h3 : (2 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
    have h4' : X ^ 4 = X ^ 3 * X := by ring
    nlinarith
  have hEb : E ≤ 8 * C / X := by
    have h0 : E = 4 * C * hypX X / X ^ 2 := by
      rw [hE, hTdef]; field_simp
    rw [h0, div_le_div_iff₀ (by positivity) hX0]
    have h2X : hypX X ≤ 2 * X := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2X (le_of_lt (mul_pos hC hX0))]
  have hL : 0 ≤ Real.log (1 + N₁ + N₂ + M₁ + M₂) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ M₁ := by exact_mod_cast hM₁
    have : (0 : ℝ) ≤ M₂ := by exact_mod_cast hM₂
    have : (0 : ℝ) ≤ N₁ := by positivity
    have : (0 : ℝ) ≤ N₂ := by positivity
    linarith
  have hA0 : 0 ≤ A₁ * B₁ := by positivity
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  -- assemble
  calc _ ≤ ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ((∫ t in (-T)..T, ‖G i t‖ * |K t|) + E * (A₁ * B₁)) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hchar i hi) (hW i hi)
    _ = ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          (∫ t in (-T)..T, ‖G i t‖ * |K t|) +
        (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) * (E * (A₁ * B₁)) := by
        rw [Finset.sum_mul (s := primIdx Q), ← sum_add_distrib]; apply sum_congr rfl; intro i _; ring
    _ ≤ Real.sqrt P * (2 * (1 + Real.log (1 + β * T))) +
        (1 + 2 * (Q : ℝ) ^ 2) * (8 * C / X * (A₁ * B₁)) := by
        refine add_le_add hmain ?_
        apply mul_le_mul hWs (mul_le_mul_of_nonneg_right hEb hA0) (by positivity)
          (by positivity)
    _ ≤ _ := by
        have s0 := Real.sqrt_nonneg P
        set L := Real.log (1 + N₁ + N₂ + M₁ + M₂) with hLdef
        set lT := Real.log (1 + β * T) with hlT
        set lX := Real.log X with hlX
        set Z := A₁ * B₁ with hZ
        have k1 : Real.sqrt P * (2 * (1 + lT)) ≤ (8 + 24 * C) * (1 + lX + L) * Real.sqrt P := by
          have u1 : 2 * (1 + lT) ≤ 8 * (1 + lX + L) := by linarith
          have u2 : 8 * (1 + lX + L) ≤ (8 + 24 * C) * (1 + lX + L) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          calc Real.sqrt P * (2 * (1 + lT)) ≤ Real.sqrt P * ((8 + 24 * C) * (1 + lX + L)) :=
                mul_le_mul_of_nonneg_left (u1.trans u2) s0
            _ = _ := by ring
        have k2 : (1 + 2 * (Q : ℝ) ^ 2) * (8 * C / X * Z) ≤
            (8 + 24 * C) * (Q : ℝ) ^ 2 * A₁ * B₁ / X := by
          have r1 : (1 + 2 * (Q : ℝ) ^ 2) * (8 * C / X * Z) =
              ((1 + 2 * (Q : ℝ) ^ 2) * (8 * C) * Z) / X := by ring
          have r2 : (8 + 24 * C) * (Q : ℝ) ^ 2 * A₁ * B₁ / X =
              ((8 + 24 * C) * (Q : ℝ) ^ 2 * Z) / X := by rw [hZ]; ring
          rw [r1, r2]
          apply div_le_div_of_nonneg_right _ hX0.le
          apply mul_le_mul_of_nonneg_right _ hA0
          have : 1 + 2 * (Q : ℝ) ^ 2 ≤ 3 * (Q : ℝ) ^ 2 := by nlinarith
          have v1 : (1 + 2 * (Q : ℝ) ^ 2) * (8 * C) ≤ 3 * (Q : ℝ) ^ 2 * (8 * C) :=
            mul_le_mul_of_nonneg_right this (by linarith)
          have v2 : 0 ≤ 8 * (Q : ℝ) ^ 2 := by positivity
          have v3 : 3 * (Q : ℝ) ^ 2 * (8 * C) + 8 * (Q : ℝ) ^ 2 = (8 + 24 * C) * (Q : ℝ) ^ 2 := by
            ring
          linarith
        linarith

end

end LeanLab.PNTPort.BV

