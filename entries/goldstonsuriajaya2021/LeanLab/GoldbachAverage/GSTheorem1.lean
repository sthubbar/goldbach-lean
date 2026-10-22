module

public import LeanLab.GoldbachAverage.Unconditional
public import LeanLab.GoldbachAverage.FromVonKoch
public import LeanLab.PNTPort.ExplicitPsi1.VonKoch2

/-!
# P0051 Goldston-Suriajaya Theorem 1, simplified form, proved

Lab proof, unit U-5326, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input. `gs_theorem1_proved` proves the statement of the cited `gs_theorem1`:
`Σ_{n ≤ N} G(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + E(N) + O(N)`, unconditional, where
`E(N) = ∫₀¹ (Ψ(r,α) - I(r,α))² I_N(1/r, -α) dα`.
Route: by orthogonality `E(N) = Σ_{n=1}^{N} Σ_{a+b=n} (Λ(a) - 1)(Λ(b) - 1)`, with `a, b ≥ 1`; expanding,
`Σ_{n ≤ N} G(n) = E(N) + 2ψ₁(N) - N(N - 1)/2`, and `ψ₁(N)` is the lab's explicit formula
`PNTPort.ExplicitPsi1`. Binary Goldbach is open; this is an average over n.
-/

@[expose] public section


open Finset Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- The coefficients of `Ψ - I`: `Λ(n) - 1` for `n ≥ 1`, and `0` at `n = 0`. -/
def cf (n : ℕ) : ℂ := (Λ n : ℂ) - (if n = 0 then 0 else 1)

/-- The coefficients of `(Ψ - I)²`. -/
def dc (n : ℕ) : ℂ := ∑ p ∈ antidiagonal n, cf p.1 * cf p.2

lemma norm_eAdd (u : ℝ) : ‖eAdd u‖ = 1 := by
  unfold eAdd
  rw [Complex.norm_exp]
  simp

lemma eAdd_add (u v : ℝ) : eAdd (u + v) = eAdd u * eAdd v := by
  unfold eAdd; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_cf_le (n : ℕ) : ‖cf n‖ ≤ n + 1 := by
  unfold cf
  have h1 : Λ n ≤ n := (ArithmeticFunction.vonMangoldt_le_log).trans
    (Real.log_le_self (Nat.cast_nonneg n))
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  split_ifs <;> simp <;> linarith

lemma summable_geom_poly {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_geometric_of_lt_one hr0 hr
  have := h1.add h2
  refine this.congr (fun n => ?_)
  simp only [pow_one]; ring

/-- The terms of `Ψ - I`. -/
def tm (r α : ℝ) (n : ℕ) : ℂ := cf n * (r : ℂ) ^ n * eAdd (α * n)

lemma norm_tm_le {r : ℝ} (hr0 : 0 ≤ r) (α : ℝ) (n : ℕ) : ‖tm r α n‖ ≤ ((n : ℝ) + 1) * r ^ n := by
  unfold tm
  rw [norm_mul, norm_mul, norm_eAdd, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, mul_one]
  exact mul_le_mul_of_nonneg_right (norm_cf_le n) (by positivity)

lemma summable_norm_tm {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (α : ℝ) :
    Summable (fun n => ‖tm r α n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_tm_le hr0 α) (summable_geom_poly hr0 hr)

lemma psi_sub_I {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (α : ℝ) :
    PsiGen r α - IGen r α = ∑' n, tm r α n := by
  have hP : Summable (fun n : ℕ => (Λ n : ℂ) * (r : ℂ) ^ n * eAdd (α * n)) := by
    refine Summable.of_norm_bounded (summable_geom_poly hr0 hr) (fun n => ?_)
    rw [norm_mul, norm_mul, norm_eAdd, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr0,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_one]
    have h1 : Λ n ≤ n := (ArithmeticFunction.vonMangoldt_le_log).trans
      (Real.log_le_self (Nat.cast_nonneg n))
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hI : Summable (fun n : ℕ => (if n = 0 then 0 else (r : ℂ) ^ n * eAdd (α * n))) := by
    refine Summable.of_norm_bounded (summable_geom_poly hr0 hr) (fun n => ?_)
    split_ifs
    · simp; positivity
    · rw [norm_mul, norm_eAdd, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr0, mul_one]
      have : r ^ n ≤ ((n : ℝ) + 1) * r ^ n := le_mul_of_one_le_left (by positivity)
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      exact this
  rw [PsiGen, IGen, ← hP.tsum_sub hI]
  apply tsum_congr; intro n
  unfold tm cf
  split_ifs <;> ring

/-- The square `(Ψ - I)² = Σ dc(n) rⁿ e(αn)`. -/
lemma sq_psi_sub_I {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (α : ℝ) :
    (PsiGen r α - IGen r α) ^ 2 = ∑' n, dc n * (r : ℂ) ^ n * eAdd (α * n) := by
  rw [psi_sub_I hr0 hr, sq,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_tm hr0 hr α)
      (summable_norm_tm hr0 hr α)]
  apply tsum_congr; intro n
  rw [dc, sum_mul, sum_mul]
  apply sum_congr rfl; intro p hp
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  unfold tm
  have e1 : (r : ℂ) ^ p.1 * (r : ℂ) ^ p.2 = (r : ℂ) ^ n := by rw [← pow_add, hp]
  have e2 : eAdd (α * p.1) * eAdd (α * p.2) = eAdd (α * n) := by
    rw [← eAdd_add, ← hp]; push_cast; ring_nf
  calc cf p.1 * (r : ℂ) ^ p.1 * eAdd (α * p.1) * (cf p.2 * (r : ℂ) ^ p.2 * eAdd (α * p.2))
      = cf p.1 * cf p.2 * ((r : ℂ) ^ p.1 * (r : ℂ) ^ p.2) *
          (eAdd (α * p.1) * eAdd (α * p.2)) := by ring
    _ = _ := by rw [e1, e2]

lemma continuous_eAdd_mul (k : ℝ) : Continuous fun α : ℝ => eAdd (α * k) := by
  unfold eAdd; fun_prop

lemma integral_eAdd (k : ℤ) :
    ∫ α in (0 : ℝ)..1, eAdd (α * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eAdd]
  · have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Complex.I_ne_zero, this, hk']
    have e : ∀ α : ℝ, eAdd (α * k) = Complex.exp ((2 * Real.pi * Complex.I * k) * α) := by
      intro α; unfold eAdd; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * k * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * Real.pi * Complex.I * k * ((1 : ℝ) : ℂ)) = k * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

lemma summable_dc {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n => ‖dc n‖ * r ^ n) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (summable_norm_tm hr0 hr 0) (summable_norm_tm hr0 hr 0)
  refine hs.congr (fun n => ?_)
  have : ∑ kl ∈ antidiagonal n, tm r 0 kl.1 * tm r 0 kl.2 = dc n * (r : ℂ) ^ n := by
    rw [dc, sum_mul]
    apply sum_congr rfl; intro p hp
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    unfold tm
    simp only [zero_mul, eAdd, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [← hp, pow_add]; ring
  rw [this, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]

/-- **Orthogonality**: `E(N) = Σ_{m=1}^{N} dc(m)`. -/
theorem EGS_eq (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    EGS N r = ∑ m ∈ Icc 1 N, dc m := by
  set D : ℕ → ℝ → ℂ := fun n α => dc n * (r : ℂ) ^ n * eAdd (α * n) with hD
  set H : ℕ → ℝ → ℂ := fun m α => ((1 / r : ℝ) : ℂ) ^ m * eAdd (-α * m) with hH
  have hpt : ∀ α : ℝ, (PsiGen r α - IGen r α) ^ 2 * IGenN N (1 / r) (-α) =
      ∑ m ∈ Icc 1 N, ∑' n, D n α * H m α := by
    intro α
    rw [sq_psi_sub_I hr0.le hr, IGenN, mul_sum]
    apply sum_congr rfl; intro m _
    rw [← tsum_mul_right]
  have hDb : ∀ n α, ‖D n α‖ = ‖dc n‖ * r ^ n := by
    intro n α
    simp only [hD, norm_mul, norm_pow, norm_eAdd, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0.le, mul_one]
  have hHb : ∀ m α, ‖H m α‖ = (1 / r) ^ m := by
    intro m α
    simp only [hH, norm_mul, norm_pow, norm_eAdd, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / r), mul_one]
  have hcont : ∀ n m, Continuous fun α => D n α * H m α := by
    intro n m
    simp only [hD, hH]
    have h1 := continuous_eAdd_mul (n : ℝ)
    have h2 : Continuous fun α : ℝ => eAdd (-α * m) := by unfold eAdd; fun_prop
    exact ((continuous_const.mul h1)).mul (continuous_const.mul h2)
  have hsum : ∀ m, Summable (fun n => ‖dc n‖ * r ^ n * (1 / r) ^ m) :=
    fun m => (summable_dc hr0.le hr).mul_right _
  have hbound : ∀ m n α, ‖D n α * H m α‖ ≤ ‖dc n‖ * r ^ n * (1 / r) ^ m := by
    intro m n α; rw [norm_mul, hDb, hHb]
  have hcm : ∀ m, Continuous fun α => ∑' n, D n α * H m α := fun m =>
    continuous_tsum (fun n => hcont n m) (hsum m) (fun n α => hbound m n α)
  rw [EGS]
  simp_rw [hpt]
  rw [intervalIntegral.integral_finset_sum (fun m _ => (hcm m).intervalIntegrable _ _)]
  apply sum_congr rfl; intro m _
  have hhs := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := 1)
    (μ := MeasureTheory.volume) (F := fun n α => D n α * H m α)
    (fun n _ => ‖dc n‖ * r ^ n * (1 / r) ^ m)
    (fun n => (hcont n m).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun α _ => hbound m n α)
    (Filter.Eventually.of_forall fun α _ => hsum m)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun α _ =>
      (Summable.of_norm_bounded (hsum m) (fun n => hbound m n α)).hasSum)
  rw [← hhs.tsum_eq]
  have hval : ∀ n, ∫ α in (0 : ℝ)..1, D n α * H m α = if n = m then dc m else 0 := by
    intro n
    have e : ∀ α : ℝ, D n α * H m α =
        (dc n * (r : ℂ) ^ n * ((1 / r : ℝ) : ℂ) ^ m) * eAdd (α * ((n : ℤ) - m : ℤ)) := by
      intro α
      simp only [hD, hH]
      have : eAdd (α * n) * eAdd (-α * m) = eAdd (α * ((n : ℤ) - m : ℤ)) := by
        rw [← eAdd_add]; congr 1; push_cast; ring
      rw [← this]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_eAdd]
    split_ifs with h1 h2 h2
    · subst h2
      rw [mul_one, mul_assoc, ← mul_pow]
      push_cast
      rw [mul_one_div_cancel (by exact_mod_cast hr0.ne'), one_pow, mul_one]
    · exfalso; apply h2; omega
    · exfalso; apply h1; rw [h2]; simp
    · ring
  simp_rw [hval]
  rw [tsum_ite_eq]

/-- Real coefficients. -/
def cfr (n : ℕ) : ℝ := Λ n - (if n = 0 then 0 else 1)

lemma dc_eq_real (m : ℕ) : dc m = ((∑ a ∈ range (m + 1), cfr a * cfr (m - a) : ℝ) : ℂ) := by
  rw [dc, Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => cf i * cf j)]
  push_cast
  apply sum_congr rfl; intro a _
  unfold cf cfr
  split_ifs <;> push_cast <;> ring

/-- For `m ≥ 1`, `dc(m) = G(m) - 2 Σ_{a<m} Λ(a) + (m - 1)`. -/
lemma dcr_eq {m : ℕ} (hm : 1 ≤ m) :
    ∑ a ∈ range (m + 1), cfr a * cfr (m - a) =
      G m - 2 * ∑ a ∈ range m, Λ a + ((m : ℝ) - 1) := by
  have e : ∀ a ∈ range (m + 1), cfr a * cfr (m - a) =
      Λ a * Λ (m - a) - Λ a * (if m - a = 0 then 0 else 1) - (if a = 0 then 0 else 1) * Λ (m - a) +
        (if a = 0 then 0 else 1) * (if m - a = 0 then 0 else 1) := by
    intro a _; unfold cfr; ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← G_eq]
  have h1 : ∑ a ∈ range (m + 1), Λ a * (if m - a = 0 then 0 else 1) = ∑ a ∈ range m, Λ a := by
    rw [sum_range_succ, Nat.sub_self]; simp only [if_true, mul_zero, add_zero]
    apply sum_congr rfl; intro a ha; rw [mem_range] at ha
    rw [if_neg (by omega), mul_one]
  have h2 : ∑ a ∈ range (m + 1), (if a = 0 then (0 : ℝ) else 1) * Λ (m - a) =
      ∑ a ∈ range m, Λ a := by
    rw [← sum_range_reflect]
    rw [← h1]
    apply sum_congr rfl; intro a ha; rw [mem_range] at ha
    rw [show m + 1 - 1 - a = m - a by omega, show m - (m - a) = a by omega]
    ring
  have h3 : ∑ a ∈ range (m + 1), (if a = 0 then (0 : ℝ) else 1) * (if m - a = 0 then 0 else 1) =
      (m : ℝ) - 1 := by
    have : ∀ a ∈ range (m + 1), (if a = 0 then (0 : ℝ) else 1) * (if m - a = 0 then 0 else 1) =
        if a ∈ Ioo 0 m then 1 else 0 := by
      intro a ha; rw [mem_range] at ha
      simp only [mem_Ioo]
      split_ifs <;> first | omega | (simp; done) | ring
    rw [sum_congr rfl this, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hf : (range (m + 1)).filter (fun a => a ∈ Ioo 0 m) = Ioo 0 m := by
      ext a; simp only [mem_filter, mem_range, mem_Ioo]; omega
    rw [hf, Nat.card_Ioo, Nat.cast_sub (by omega)]; simp
  rw [h1, h2, h3]; ring

lemma sum_S (N : ℕ) : ∑ m ∈ Icc 1 N, ∑ a ∈ range m, Λ a =
    ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ (fun a => Λ a * (((N + 1 : ℕ) : ℝ) - a))]
    have : ∑ a ∈ range (N + 1), Λ a * (((N + 1 : ℕ) : ℝ) - a) =
        ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) + ∑ a ∈ range (N + 1), Λ a := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro a _; push_cast; ring
    rw [this]; push_cast; ring

lemma sum_G_Icc (N : ℕ) : ∑ m ∈ Icc 1 N, G m = ∑ n ∈ range (N + 1), G n := by
  induction N with
  | zero => simp [G]
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ (fun n => G n) (N + 1)]

lemma sum_Icc_sub_one (N : ℕ) : ∑ m ∈ Icc 1 N, ((m : ℝ) - 1) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- `E(N) = Σ_{n ≤ N} G(n) - 2 Σ_{a ≤ N} Λ(a)(N - a) + N(N - 1)/2`. -/
theorem sum_dc (N : ℕ) : ∑ m ∈ Icc 1 N, dc m =
    ((∑ n ∈ range (N + 1), G n - 2 * ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) +
      (N : ℝ) * (N - 1) / 2 : ℝ) : ℂ) := by
  have h : ∀ m ∈ Icc 1 N, dc m = ((G m - 2 * ∑ a ∈ range m, Λ a + ((m : ℝ) - 1) : ℝ) : ℂ) := by
    intro m hm; rw [mem_Icc] at hm; rw [dc_eq_real, dcr_eq hm.1]
  rw [sum_congr rfl h, ← Complex.ofReal_sum]
  congr 1
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_S]
  rw [sum_G_Icc, sum_Icc_sub_one]

open LZCesaroShort PNTPort.ExplicitPsi1 in
/-- **Goldston-Suriajaya Theorem 1, simplified form**, unconditional, now proved: the statement
of the cited `gs_theorem1`. -/
theorem gs_theorem1_proved : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℝ, 0 < r → r < 1 →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r‖ ≤ K * N := by
  obtain ⟨K, hK0, hK⟩ := psi1_sqrt
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hd0
  refine ⟨2 * K + 2 * ‖d0‖ + 1, fun N hN r hr0 hr => ?_⟩
  have hN0 : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN
                               linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hRg : Rg N (N : ℝ) = ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) := by
    rw [Rg]; apply sum_congr rfl; intro a ha; rw [mem_range] at ha
    have : (a : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp ha
    rw [max_eq_right (by linarith)]
  have hW : Wf (N : ℝ) = Z1 N := by
    rw [Wf, Z1, zeroSum]
    have e : (∑' ρ : Zall, wterm (N : ℝ) ρ.1) =
        ∑' ρ : NontrivialZero, wterm (N : ℝ) ρ.1 := by
      rw [Zall_eq]; rfl
    rw [e]; rfl
  have hb := hK N N hN0 le_rfl
  rw [hRg, hW] at hb
  rw [EGS_eq N hr0 hr, sum_dc]
  set P := ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a)
  set Err : ℂ := ((P : ℝ) : ℂ) - (((((N : ℝ) ^ 2 / 2 : ℝ)) : ℂ) - ((N : ℝ) : ℂ) * d0 - Z1 N)
    with hErr
  have key : ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N -
      ((∑ n ∈ range (N + 1), G n - 2 * P + (N : ℝ) * (N - 1) / 2 : ℝ) : ℂ) =
      2 * Err - 2 * ((N : ℝ) : ℂ) * d0 + (((N : ℝ) / 2 : ℝ) : ℂ) := by
    rw [hErr]; push_cast; ring
  rw [key]
  have hs : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
    calc (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have n1 : ‖2 * Err‖ ≤ 2 * K * N := by
    rw [norm_mul, Complex.norm_two]
    have h' : ‖Err‖ ≤ K * (N : ℝ) ^ (1 / 2 : ℝ) := hb
    have : ‖Err‖ ≤ K * N := h'.trans (by gcongr)
    linarith
  have n2 : ‖2 * ((N : ℝ) : ℂ) * d0‖ = 2 * ‖d0‖ * N := by
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hN0]; ring
  have n3 : ‖((((N : ℝ) / 2 : ℝ)) : ℂ)‖ = N / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖2 * Err - 2 * ((N : ℝ) : ℂ) * d0 + (((N : ℝ) / 2 : ℝ) : ℂ)‖
      ≤ ‖2 * Err‖ + ‖2 * ((N : ℝ) : ℂ) * d0‖ + ‖((((N : ℝ) / 2 : ℝ)) : ℂ)‖ := by
        have a1 := norm_add_le (2 * Err - 2 * ((N : ℝ) : ℂ) * d0) ((((N : ℝ) / 2 : ℝ)) : ℂ)
        have a2 := norm_sub_le (2 * Err) (2 * ((N : ℝ) : ℂ) * d0)
        linarith
    _ ≤ 2 * K * N + 2 * ‖d0‖ * N + N / 2 := by rw [n2, n3]; linarith
    _ ≤ (2 * K + 2 * ‖d0‖ + 1) * N := by nlinarith

end LeanLab.GoldbachAverage

