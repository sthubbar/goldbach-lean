module

public import LeanLab.GoldbachAverage.GSTheorem1
public import LeanLab.GoldbachAverage.Links
public import LeanLab.LZCesaroShort.Lemma1Proved
public import LeanLab.LZCesaroShort.Layer2
public import LeanLab.PNTPort.Selberg.GeomZ

/-!
# Languasco-Zaccagnini's Theorem 1 under RH, from Goldston-Suriajaya and P0058 Lemma 1

Lab proof, unit U-6305, CLOUD 20261020T1017Z-cloud40, P0052, P0050, P0049. AI wrote this file.
Known mathematics: Languasco-Zaccagnini, The number of Goldbach representations of an integer,
Proc. AMS 140 (2012), arXiv 1011.3198, Theorem 1, which Goldston-Yang 2016 quote as their Lemma 2.

`lz_theorem1_proved : RiemannHypothesis → ∃ K, ∀ N ≥ 2,`
`‖Σ_{n ≤ N} G(n) - N²/2 + 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1))‖ ≤ K N log³ N`, the lab's cited `lz_theorem1`
statement, not part of this copy, PROVED CONDITIONAL ON RiemannHypothesis only. Route, the paper's own: the lab's
`gs_theorem1_proved` reduces it to `E(N) = ∫_0^1 (Ψ - I)² I_N(1/r, -α) dα ≪ N log³ N` at
`r = e^{-1/N}`; on `|α| ≤ 1/2`, `|I_N| ≤ 6 min(N, 1/(2|α|))` and `|Ψ - I| ≤ |S̃ - 1/z| + 9`, and the
dyadic layers of `LZCesaroShort.integral_G_le` with P0058's Lemma 1 under RH, `lemma1_full`, give
`N (1 + log N)²` per layer over `log₂ N + 2` layers.

With `Links.lean` this also gives the quoted P0050 bound `O(N log⁵ N)`, `bsp_upper_proved`, and the
quoted P0049 bound `O((N log N)^{4/3})`, `fujii_proved`, both CONDITIONAL ON RH only.
Binary Goldbach is OPEN; these are averages over n.
-/

@[expose] public section


noncomputable section
namespace LeanLab.GoldbachAverage
open Complex Finset Filter MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov LeanLab.LZCesaroShort

lemma eAdd_eq_e (u : ℝ) : eAdd u = LeanLab.PNTPort.LargeSieve.e u := by
  unfold eAdd LeanLab.PNTPort.LargeSieve.e; congr 1; push_cast; ring

lemma eAdd_nat_mul (α : ℝ) (n : ℕ) : eAdd (α * n) = eAdd α ^ n := by
  rw [eAdd_eq_e, eAdd_eq_e, mul_comm, e_nat_mul]

lemma eAdd_add_one (α : ℝ) (n : ℕ) : eAdd ((α + 1) * n) = eAdd (α * n) := by
  rw [eAdd_eq_e, eAdd_eq_e, show (α + 1) * n = α * n + ((n : ℤ) : ℝ) by push_cast; ring, e_add,
    e_int, mul_one]

lemma norm_eAdd' (u : ℝ) : ‖eAdd u‖ = 1 := by rw [eAdd_eq_e, norm_e]

/-- `Ψ` at `r = e^{-1/N}` is P0058's `S̃`. -/
lemma psiGen_eq_St (N : ℕ) (α : ℝ) : PsiGen (Real.exp (-(1 / (N : ℝ)))) α = St N α := by
  unfold PsiGen St
  apply tsum_congr; intro n
  rw [eAdd_eq_e]
  have h1 : ((Real.exp (-(1 / (N : ℝ))) : ℂ)) ^ n = ((Real.exp (-n / N) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; ring
  rw [h1, mul_comm (α : ℝ) n]; push_cast; ring

/-- `I(r, α) = 1/(1 - w) - 1`, `w = r e(α)`. -/
lemma iGen_eq {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (α : ℝ) :
    IGen r α = 1 / (1 - (r : ℂ) * eAdd α) - 1 := by
  set w : ℂ := (r : ℂ) * eAdd α with hw
  have hwn : ‖w‖ < 1 := by
    rw [hw, norm_mul, norm_eAdd', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr
  have hs := hasSum_geometric_of_norm_lt_one hwn
  have hterm : ∀ n : ℕ, (if n = 0 then (0 : ℂ) else (r : ℂ) ^ n * eAdd (α * n)) =
      w ^ n - (if n = 0 then 1 else 0) := by
    intro n
    split_ifs with h
    · subst h; simp
    · rw [sub_zero, hw, mul_pow, eAdd_nat_mul]
  have hs2 : HasSum (fun n : ℕ => w ^ n - (if n = 0 then (1 : ℂ) else 0)) ((1 - w)⁻¹ - 1) :=
    hs.sub (hasSum_ite_eq 0 (1 : ℂ))
  unfold IGen
  simp_rw [hterm]
  rw [hs2.tsum_eq, one_div]

lemma w_eq_exp (N : ℕ) (α : ℝ) :
    ((Real.exp (-(1 / (N : ℝ))) : ℝ) : ℂ) * eAdd α = cexp (-zz N α) := by
  unfold zz eAdd
  rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring

/-- `‖I - 1/z‖ ≤ 9` on `|α| ≤ 1/2`. -/
lemma norm_iGen_sub_le {N : ℕ} (hN : 1 ≤ N) {α : ℝ} (hα : |α| ≤ 1 / 2) :
    ‖IGen (Real.exp (-(1 / (N : ℝ)))) α - 1 / zz N α‖ ≤ 9 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ Real.exp (-(1 / (N : ℝ))) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1 / (N : ℝ))) < 1 := (Real.exp_lt_one_iff.mpr (by
    have : 0 < 1 / (N : ℝ) := by positivity
    linarith))
  rw [iGen_eq hr0 hr1, w_eq_exp]
  have hre : (zz N α).re = 1 / N := by unfold zz; simp
  have him : (zz N α).im = -(2 * Real.pi * α) := by unfold zz; simp
  have hg := LeanLab.PNTPort.Selberg.geom_sub_inv_le (z := zz N α)
    (by rw [hre]; positivity)
    (by rw [hre, div_le_one hN0]; exact_mod_cast hN)
    (by
      rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos])
  calc ‖1 / (1 - cexp (-zz N α)) - 1 - 1 / zz N α‖
      = ‖(1 / (1 - cexp (-zz N α)) - 1 / zz N α) - 1‖ := by ring_nf
    _ ≤ ‖1 / (1 - cexp (-zz N α)) - 1 / zz N α‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 9 := by rw [norm_one]; linarith

lemma norm_sub_sq_le (a b c : ℂ) (hc : ‖c‖ ≤ 9) : ‖a - b‖ ^ 2 ≤ 2 * ‖a - (b - c)‖ ^ 2 + 162 := by
  have h1 : ‖a - b‖ ≤ ‖a - (b - c)‖ + ‖c‖ := by
    calc ‖a - b‖ = ‖(a - (b - c)) - c‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have h2 : ‖a - b‖ ≤ ‖a - (b - c)‖ + 9 := by linarith
  have h3 : ‖a - b‖ ^ 2 ≤ (‖a - (b - c)‖ + 9) ^ 2 := pow_le_pow_left₀ h0 h2 2
  nlinarith [sq_nonneg (‖a - (b - c)‖ - 9)]

/-- `‖Ψ - I‖² ≤ 2 ‖S̃ - 1/z‖² + 162` on `|α| ≤ 1/2`. -/
lemma norm_psi_sub_I_sq_le {N : ℕ} (hN : 1 ≤ N) {α : ℝ} (hα : |α| ≤ 1 / 2) :
    ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α - IGen (Real.exp (-(1 / (N : ℝ)))) α‖ ^ 2 ≤
      2 * ‖St N α - 1 / zz N α‖ ^ 2 + 162 := by
  rw [psiGen_eq_St]
  have := norm_sub_sq_le (St N α) (IGen (Real.exp (-(1 / (N : ℝ)))) α)
    (IGen (Real.exp (-(1 / (N : ℝ)))) α - 1 / zz N α) (norm_iGen_sub_le hN hα)
  rwa [sub_sub_cancel] at this

/-- `‖ρu - 1‖ ≥ ‖u - 1‖` for `ρ ≥ 1`, `‖u‖ = 1`. -/
lemma norm_smul_sub_one_ge {ρ : ℝ} (hρ : 1 ≤ ρ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖u - 1‖ ≤ ‖(ρ : ℂ) * u - 1‖ := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have := Complex.sq_norm u; rw [hu, Complex.normSq_apply] at this; nlinarith
  have hre : u.re ≤ 1 := by nlinarith [sq_nonneg u.im]
  have e1 : ‖u - 1‖ ^ 2 = (u.re - 1) ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have e2 : ‖(ρ : ℂ) * u - 1‖ ^ 2 = (ρ * u.re - 1) ^ 2 + (ρ * u.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hid : (ρ * u.re - 1) ^ 2 + (ρ * u.im) ^ 2 - ((u.re - 1) ^ 2 + u.im ^ 2) =
      (ρ - 1) * (ρ + 1 - 2 * u.re) := by linear_combination (ρ ^ 2 - 1) * hu2
  have : ‖u - 1‖ ^ 2 ≤ ‖(ρ : ℂ) * u - 1‖ ^ 2 := by
    rw [e1, e2]
    have := mul_nonneg (sub_nonneg.mpr hρ) (show 0 ≤ ρ + 1 - 2 * u.re by linarith)
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

lemma sum_Icc_one (N : ℕ) (f : ℕ → ℂ) : ∑ n ∈ Icc 1 N, f n = ∑ k ∈ range N, f (1 + k) := by
  have : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [this, sum_Ico_eq_sum_range, Nat.add_sub_cancel]

/-- `|I_N(1/r, -α)| ≤ 6 min(N, 1/(2|α|))` at `r = e^{-1/N}`. -/
lemma norm_IGenN_le {N : ℕ} (hN : 1 ≤ N) {α : ℝ} (hα : |α| ≤ 1 / 2) :
    ‖IGenN N (1 / Real.exp (-(1 / (N : ℝ)))) (-α)‖ ≤ 6 * LeanLab.PNTPort.Vinogradov.G (N : ℝ) α := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set ρ : ℝ := 1 / Real.exp (-(1 / (N : ℝ))) with hρ
  have hρe : ρ = Real.exp (1 / N) := by rw [hρ, Real.exp_neg, one_div, inv_inv]
  have hρ1 : 1 ≤ ρ := by rw [hρe]; exact Real.one_le_exp (by positivity)
  have hρpow : ∀ n : ℕ, n ≤ N → ρ ^ n ≤ 3 := by
    intro n hn
    rw [hρe, ← Real.exp_nat_mul]
    have : (n : ℝ) * (1 / N) ≤ 1 := by
      rw [mul_one_div, div_le_one hN0]; exact_mod_cast hn
    calc Real.exp (n * (1 / N)) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  set v : ℂ := (ρ : ℂ) * eAdd (-α) with hv
  have hterm : ∀ n : ℕ, (ρ : ℂ) ^ n * eAdd (-α * n) = v ^ n := by
    intro n; rw [hv, mul_pow, eAdd_nat_mul]
  have hsum : IGenN N ρ (-α) = ∑ n ∈ Icc 1 N, v ^ n := by
    unfold IGenN; exact sum_congr rfl fun n _ => hterm n
  rw [hsum]
  -- bound A
  have hA : ‖∑ n ∈ Icc 1 N, v ^ n‖ ≤ 3 * N := by
    calc ‖∑ n ∈ Icc 1 N, v ^ n‖ ≤ ∑ n ∈ Icc 1 N, ‖v ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Icc 1 N, (3 : ℝ) := by
          apply sum_le_sum; intro n hn
          rw [norm_pow, hv, norm_mul, norm_eAdd', mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith)]
          exact hρpow n (mem_Icc.mp hn).2
      _ = 3 * N := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hG : LeanLab.PNTPort.Vinogradov.G (N : ℝ) α = if dist0 α = 0 then (N : ℝ) else min (N : ℝ) (1 / (2 * dist0 α)) := rfl
  have hd : dist0 α = |α| := dist0_eq_abs hα
  rw [hG, hd]
  split_ifs with h0
  · linarith
  · have hpos : 0 < |α| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
    -- bound B
    have hu : ‖eAdd (-α) - 1‖ ≥ 4 * |α| := by
      rw [eAdd_eq_e]
      have := four_dist0_le (-α)
      rwa [dist0_eq_abs (by rwa [abs_neg]), abs_neg] at this
    have hv1 : 4 * |α| ≤ ‖v - 1‖ := le_trans hu (norm_smul_sub_one_ge hρ1 (norm_eAdd' _))
    have hvne : v ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hv1; linarith
    have hB : ‖∑ n ∈ Icc 1 N, v ^ n‖ ≤ 12 / (4 * |α|) := by
      rw [sum_Icc_one]
      have : ∑ k ∈ range N, v ^ (1 + k) = v * ((v ^ N - 1) / (v - 1)) := by
        rw [← geom_sum_eq hvne, mul_sum]; exact sum_congr rfl fun k _ => by rw [pow_add, pow_one]
      rw [this, norm_mul, norm_div]
      have hvn : ‖v‖ ≤ 3 := by
        have := hρpow 1 hN; rw [pow_one] at this
        rw [hv, norm_mul, norm_eAdd', mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]; exact this
      have hvN : ‖v ^ N - 1‖ ≤ 4 := by
        calc ‖v ^ N - 1‖ ≤ ‖v ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 3 + 1 := by
              rw [norm_one, norm_pow, hv, norm_mul, norm_eAdd', mul_one, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg (by linarith)]
              linarith [hρpow N le_rfl]
          _ = 4 := by norm_num
      have h4 : 0 < 4 * |α| := by positivity
      calc ‖v‖ * (‖v ^ N - 1‖ / ‖v - 1‖) ≤ 3 * (4 / (4 * |α|)) := by
            apply mul_le_mul hvn _ (by positivity) (by norm_num)
            exact div_le_div₀ (by norm_num) hvN h4 hv1
        _ = 12 / (4 * |α|) := by ring
    rcases le_total (N : ℝ) (1 / (2 * |α|)) with hm | hm
    · rw [min_eq_left hm]; linarith
    · rw [min_eq_right hm]
      have : 12 / (4 * |α|) = 6 * (1 / (2 * |α|)) := by field_simp; ring
      linarith

lemma eAdd_add_int (x : ℝ) (k : ℤ) : eAdd (x + k) = eAdd x := by
  rw [eAdd_eq_e, eAdd_eq_e, e_add, e_int, mul_one]

/-- The integrand of `E(N)`. -/
def FE (N : ℕ) (r α : ℝ) : ℂ := (PsiGen r α - IGen r α) ^ 2 * IGenN N (1 / r) (-α)

lemma FE_periodic (N : ℕ) (r : ℝ) : Function.Periodic (FE N r) 1 := by
  intro α
  have h1 : PsiGen r (α + 1) = PsiGen r α := by
    unfold PsiGen; apply tsum_congr; intro n; rw [eAdd_add_one]
  have h2 : IGen r (α + 1) = IGen r α := by
    unfold IGen; apply tsum_congr; intro n; rw [eAdd_add_one]
  have h3 : IGenN N (1 / r) (-(α + 1)) = IGenN N (1 / r) (-α) := by
    unfold IGenN; apply sum_congr rfl; intro n _
    rw [show -(α + 1) * n = -α * n + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, eAdd_add_int]
  unfold FE; rw [h1, h2, h3]

lemma EGS_eq_sym (N : ℕ) (r : ℝ) : EGS N r = ∫ α in (-(1 / 2 : ℝ))..(1 / 2), FE N r α := by
  have := (FE_periodic N r).intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at this
  rw [this]; rfl

lemma continuous_IGenN_norm (N : ℕ) (ρ : ℝ) : Continuous fun α : ℝ => ‖IGenN N ρ (-α)‖ := by
  unfold IGenN eAdd; fun_prop

lemma natLog_le (N : ℕ) (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
  have h := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have h' : ((2 : ℝ) ^ (Nat.log 2 N)) ≤ N := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at this
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]; exact this

lemma fin_alg {M L K₁ N : ℝ} (hK : 0 ≤ K₁) (hN : 2 ≤ N) (hL : 0.69 ≤ L) (hMl : M + 1 ≤ 5 * L) :
    (M + 1) * (6 * (4 * K₁ * N * (1 + L) ^ 2 + 648)) ≤ 30 * (40 * K₁ + 1400) * N * L ^ 3 := by
  have hsq : (1 + L) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
  have hL2 : (0.4761 : ℝ) ≤ L ^ 2 := by nlinarith
  have h648 : (648 : ℝ) ≤ 1400 * N * L ^ 2 := by nlinarith
  have hA : 4 * K₁ * N * (1 + L) ^ 2 ≤ 36 * K₁ * N * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * K₁ * N)
    linarith
  have hin : 6 * (4 * K₁ * N * (1 + L) ^ 2 + 648) ≤ 6 * (40 * K₁ + 1400) * N * L ^ 2 := by
    have : 36 * K₁ * N * L ^ 2 ≤ 6 * 40 * K₁ * N * L ^ 2 := by
      have : 0 ≤ K₁ * N * L ^ 2 := by positivity
      linarith
    linarith
  have hin0 : 0 ≤ 6 * (4 * K₁ * N * (1 + L) ^ 2 + 648) := by positivity
  calc (M + 1) * (6 * (4 * K₁ * N * (1 + L) ^ 2 + 648))
      ≤ (5 * L) * (6 * (4 * K₁ * N * (1 + L) ^ 2 + 648)) := mul_le_mul_of_nonneg_right hMl hin0
    _ ≤ (5 * L) * (6 * (40 * K₁ + 1400) * N * L ^ 2) :=
        mul_le_mul_of_nonneg_left hin (by linarith)
    _ = 30 * (40 * K₁ + 1400) * N * L ^ 3 := by ring

/-- **`E(N) ≪ N log³ N` under RH.** -/
theorem EGS_bound (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖EGS N (Real.exp (-(1 / (N : ℝ))))‖ ≤ K * N * Real.log N ^ 3 := by
  obtain ⟨K₁, hK₁0, hl⟩ := lemma1_full hRH
  refine ⟨30 * (40 * K₁ + 1400), fun N hN2 => ?_⟩
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set r := Real.exp (-(1 / (N : ℝ))) with hr
  set L := Real.log N with hL
  have hlog2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hN2r
  have hL0 : 0 < L := by linarith
  set f : ℝ → ℝ := fun α => 2 * ‖St N α - 1 / zz N α‖ ^ 2 + 162 with hf
  set g : ℝ → ℝ := fun α => ‖IGenN N (1 / r) (-α)‖ with hg
  have hfc : Continuous f := (continuous_const.mul (continuous_St_sub hN)).add continuous_const
  have hf0 : ∀ α, 0 ≤ f α := fun α => by simp only [hf]; positivity
  have hgc : Continuous g := continuous_IGenN_norm N (1 / r)
  have hgG : ∀ α ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), g α ≤ 6 * LeanLab.PNTPort.Vinogradov.G (N : ℝ) α := fun α hα =>
    norm_IGenN_le hN (abs_le.mpr ⟨hα.1, hα.2⟩)
  set M := Nat.log 2 N + 1 with hM
  have hKM : (N : ℝ) ≤ 2 ^ M := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    exact_mod_cast this.le
  -- step 1: the norm of the integral
  have step1 : ‖EGS N r‖ ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α * f α := by
    rw [EGS_eq_sym]
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · refine Filter.Eventually.of_forall fun α hα => ?_
      have hα' : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1.le, hα.2⟩
      unfold FE
      rw [norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_psi_sub_I_sq_le hN hα') (norm_nonneg _)
    · exact (hgc.mul hfc).intervalIntegrable _ _
  -- step 2: the dyadic layers
  have step2 := integral_G_le (H := N) (K := M) hN (by exact_mod_cast hKM) hfc hf0 hgc
    (by norm_num : (0 : ℝ) ≤ 6) hgG
  -- step 3: each layer
  have hlayer : ∀ k ∈ range (M + 1), 6 * (2 * (N : ℝ) / 2 ^ k) *
      ∫ α in (-xi N k)..(xi N k), f α ≤ 6 * (4 * K₁ * N * (1 + L) ^ 2 + 648) := by
    intro k _
    set ξ := xi N k with hξ
    have hξh : ξ ≤ 1 / 2 := xi_le_half N k
    have hξk : ξ ≤ (2 : ℝ) ^ k / N := xi_le N k
    have hξl : 1 / (N : ℝ) ≤ ξ := by
      rw [hξ]; unfold xi; apply le_min
      · apply div_le_div_of_nonneg_right _ hN0.le; exact one_le_pow₀ (by norm_num)
      · rw [div_le_iff₀ hN0]; linarith
    have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξl
    have hint : ∫ α in (-ξ)..ξ, f α =
        2 * (∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) + 162 * (2 * ξ) := by
      simp only [hf]
      rw [intervalIntegral.integral_add (((continuous_St_sub hN).intervalIntegrable _ _).const_mul 2)
        intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        smul_eq_mul]
      ring
    have hl1 := hl N hN ξ (by
      have : 1 / (2 * (N : ℝ)) ≤ 1 / N := by
        apply one_div_le_one_div_of_le hN0; linarith
      linarith) hξh
    have hlog : (1 + Real.log (2 * N * ξ)) ^ 2 ≤ (1 + L) ^ 2 := by
      have h1 : 1 ≤ 2 * N * ξ := by
        have := (div_le_iff₀ hN0).mp hξl
        nlinarith
      have h2 : 2 * N * ξ ≤ N := by nlinarith
      have h3 := Real.log_nonneg h1
      have h4 := Real.log_le_log (by linarith) h2
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hA : 2 * (N : ℝ) / 2 ^ k * ξ ≤ 2 := by
      have hξN : ξ * N ≤ 2 ^ k := (le_div_iff₀ hN0).mp hξk
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hB0 : 0 ≤ 2 * (N : ℝ) / 2 ^ k := by positivity
    rw [hint]
    have hstep : 2 * (N : ℝ) / 2 ^ k * (2 * (∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) + 162 * (2 * ξ))
        ≤ 4 * K₁ * N * (1 + L) ^ 2 + 648 := by
      have e1 : 2 * (N : ℝ) / 2 ^ k * (2 * ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2) ≤
          4 * K₁ * N * (1 + L) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * (2 * (N : ℝ) / 2 ^ k))
        have e2 : 2 * (2 * (N : ℝ) / 2 ^ k) * (K₁ * N * ξ * (1 + Real.log (2 * N * ξ)) ^ 2) =
            2 * K₁ * N * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + Real.log (2 * N * ξ)) ^ 2 := by ring
        rw [e2] at this
        have h5 : 2 * K₁ * N * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + Real.log (2 * N * ξ)) ^ 2 ≤
            2 * K₁ * N * 2 * (1 + L) ^ 2 := by
          have hk0 : 0 ≤ 2 * K₁ * N := by positivity
          calc 2 * K₁ * N * (2 * (N : ℝ) / 2 ^ k * ξ) * (1 + Real.log (2 * N * ξ)) ^ 2
              ≤ 2 * K₁ * N * 2 * (1 + Real.log (2 * N * ξ)) ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                exact mul_le_mul_of_nonneg_left hA hk0
            _ ≤ 2 * K₁ * N * 2 * (1 + L) ^ 2 :=
                mul_le_mul_of_nonneg_left hlog (by positivity)
        nlinarith
      have e3 : 2 * (N : ℝ) / 2 ^ k * (162 * (2 * ξ)) ≤ 648 := by nlinarith
      nlinarith
    nlinarith
  -- assemble
  have hsum : ∑ k ∈ range (M + 1), 6 * (2 * (N : ℝ) / 2 ^ k) * ∫ α in (-xi N k)..(xi N k), f α
      ≤ (M + 1) * (6 * (4 * K₁ * N * (1 + L) ^ 2 + 648)) := by
    calc _ ≤ ∑ _k ∈ range (M + 1), 6 * (4 * K₁ * N * (1 + L) ^ 2 + 648) := sum_le_sum hlayer
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hMl : (M : ℝ) + 1 ≤ 5 * L := by
    have h := natLog_le N hN
    have h23 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
    have hL23 : (2 : ℝ) / 3 ≤ L := le_trans h23 hL2
    have a : Real.log N / Real.log 2 ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]
      have : L = Real.log N := rfl
      nlinarith
    have hM' : (M : ℝ) = Nat.log 2 N + 1 := by rw [hM]; push_cast; ring
    rw [hM']
    linarith
  have hfin := fin_alg hK₁0 hN2r (by linarith) hMl
  push_cast at hsum hfin ⊢
  calc ‖EGS N r‖ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := hsum
    _ ≤ _ := hfin

/-- **Languasco-Zaccagnini Theorem 1 under RH**, the cited `lz_theorem1`. -/
theorem lz_theorem1_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * N * Real.log N ^ 3 := by
  intro hRH
  obtain ⟨K0, hK0⟩ := gs_theorem1_proved
  obtain ⟨K2, hK2⟩ := EGS_bound hRH
  refine ⟨|K0| * 4 + K2, fun N hN => ?_⟩
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hr0 : 0 < Real.exp (-(1 / (N : ℝ))) := Real.exp_pos _
  have hr1 : Real.exp (-(1 / (N : ℝ))) < 1 := (Real.exp_lt_one_iff.mpr (by
    have : 0 < 1 / (N : ℝ) := by positivity
    linarith))
  have h1 := hK0 N hN _ hr0 hr1
  have h2 := hK2 N hN
  have hL : 0.69 ≤ Real.log N := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hN2r; linarith
  have hL3 : (1 : ℝ) / 4 ≤ Real.log N ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at this; linarith
  set X := ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N
  have htri : ‖X‖ ≤ ‖X - EGS N (Real.exp (-(1 / (N : ℝ))))‖ + ‖EGS N (Real.exp (-(1 / (N : ℝ))))‖ := by
    calc ‖X‖ = ‖(X - EGS N _) + EGS N _‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have hK0N : K0 * N ≤ |K0| * 4 * N * Real.log N ^ 3 := by
    have : K0 * N ≤ |K0| * N := mul_le_mul_of_nonneg_right (le_abs_self K0) (by positivity)
    have : |K0| * (N : ℝ) * 1 ≤ |K0| * N * (4 * Real.log N ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  calc ‖X‖ ≤ K0 * N + K2 * N * Real.log N ^ 3 := by linarith
    _ ≤ (|K0| * 4 + K2) * N * Real.log N ^ 3 := by nlinarith

/-- P0050 as quoted, `O(N log⁵ N)` under RH, from `lz_theorem1_proved`. -/
theorem bsp_upper_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * N * Real.log N ^ 5 := fun hRH => lz_to_bsp (lz_theorem1_proved hRH)

/-- P0049 as quoted, `O((N log N)^{4/3})` under RH. -/
theorem fujii_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * ((N : ℝ) * Real.log N) ^ ((4 : ℝ) / 3) :=
  fun hRH => bsp_to_fujii (lz_to_bsp (lz_theorem1_proved hRH))

/-- The zero sum `Z1 x = Σ_ρ m(ρ) x^{ρ+1}/(ρ(ρ+1))` converges absolutely: for every real `x > 0`
the family summed by `zeroSum` in `Z1 x` is summable over the nontrivial zeros, so the `tsum` is its
genuine sum and not the junk value `0`. Unconditional. Added for the Palomar entry. -/
theorem lz_zeroSum_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((x : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1)))) := by
  have hs := (PNTPort.ExplicitPsi1.summable_zterm hx).mul_left (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : ∀ ρ : PNTPort.ExplicitPsi1.Zall, (x : ℂ) * PNTPort.ExplicitPsi1.zterm x ρ =
      (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * ((x : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1))) := by
    intro ρ
    simp only [PNTPort.ExplicitPsi1.zterm]
    rw [cpow_add _ _ hx0, cpow_one]
    ring
  simp_rw [e] at hs
  rw [PNTPort.ExplicitPsi1.Zall_eq] at hs
  exact hs

end LeanLab.GoldbachAverage

