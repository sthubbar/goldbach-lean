module

public import LeanLab.GoldbachAverage.Sums
public import LeanLab.GoldbachAverage.ZeroSums
public import LeanLab.LZCesaroShort.Lemma8Proof
public import LeanLab.PNTPort.Selberg.CramerSum

/-!
# Goldston-Yang Theorem 2 under RH

Lab proof, unit U-6306, CLOUD 20261020T1017Z-cloud40, P0052. AI wrote this file. Known
mathematics, Goldston-Yang 2016, arXiv 1601.06902, Theorem 2.

`gy_theorem2_proved : RiemannHypothesis → ∃ K, ∀ N ≥ 2,`
`‖Σ_{n ≤ N} (1 - n/N) G(n) - N²/6 + 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)(ρ+2))‖ ≤ K N`, the cited
`gy_theorem2` of `ZeroSums.lean`, PROVED CONDITIONAL ON RiemannHypothesis only.

Route, the lab's: `P = Σ_{n ≤ N} (N - n) G(n) = Σ_{m<N} ψ(m) ψ(N - 1 - m)`, `fejerG`; with
`ψ(m) = m + E(m)` the cross terms give `2 Σ_{m<N} (N - 1 - m) E(m)`, which is the second Riesz mean
`Σ_{a ≤ N} Λ(a)(N - a)²/2` up to `O(N²)`, evaluated by integrating the lab's `ψ₁` explicit formula,
`LZCesaroShort.psi1_formula`, term by term over the zeros; the term `Σ_m E(m) E(N - 1 - m)` is at
most `Σ_m E(m)²` by AM-GM after the reflection `m ↦ N - 1 - m`, and Cramér's mean square under RH,
`PNTPort.Selberg.cramer_sum`, makes that `O(N²)`. Dividing by `N` gives the theorem.
Binary Goldbach is OPEN; this is an average over n.
-/

@[expose] public section


noncomputable section
namespace LeanLab.GoldbachAverage
open Complex Finset
open scoped ArithmeticFunction.vonMangoldt

/-! ### Discrete identities -/

lemma psiN_succ (k : ℕ) : psiN (k + 1) = psiN k + Λ (k + 1) := by
  unfold psiN; rw [sum_range_succ]

lemma psiN_zero : psiN 0 = 0 := by simp [psiN]

lemma psiN_nonneg (k : ℕ) : 0 ≤ psiN k :=
  sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- `Σ_{n ≤ N} (N - n) G(n) = Σ_{m<N} Σ_{n ≤ m} G(n)`. -/
lemma weighted_eq_sum_partial (N : ℕ) :
    ∑ n ∈ range (N + 1), ((N : ℝ) - n) * G n = ∑ m ∈ range N, ∑ n ∈ range (m + 1), G n := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc ∑ n ∈ range (N + 1 + 1), (((N + 1 : ℕ) : ℝ) - n) * G n
        = ∑ n ∈ range (N + 1), (((N : ℝ) - n) * G n + G n) + 0 := by
          rw [sum_range_succ]; congr 1
          · exact sum_congr rfl fun n _ => by push_cast; ring
          · push_cast; ring
      _ = ∑ m ∈ range (N + 1), ∑ n ∈ range (m + 1), G n := by
          rw [add_zero, sum_add_distrib, ih, sum_range_succ (fun m => ∑ n ∈ range (m + 1), G n)]

/-- `F(N) = Σ_{m<N} ψ(m) ψ(N - 1 - m)`. -/
def fejerG (N : ℕ) : ℝ := ∑ m ∈ range N, psiN m * psiN (N - 1 - m)

lemma fejerG_succ (N : ℕ) : fejerG (N + 1) = fejerG N + ∑ a ∈ range (N + 1), Λ a * psiN (N - a) := by
  unfold fejerG
  rw [sum_range_succ, show N + 1 - 1 - N = 0 by omega, psiN_zero, mul_zero, add_zero]
  have h1 : ∀ m ∈ range N, psiN m * psiN (N + 1 - 1 - m) =
      psiN m * psiN (N - 1 - m) + psiN m * Λ (N - m) := by
    intro m hm
    have := mem_range.mp hm
    rw [show N + 1 - 1 - m = (N - 1 - m) + 1 by omega, psiN_succ,
      show N - 1 - m + 1 = N - m by omega]
    ring
  rw [sum_congr rfl h1, sum_add_distrib]
  congr 1
  -- Σ_{m<N} ψ(m) Λ(N - m) = Σ_{a ≤ N} Λ(a) ψ(N - a)
  rw [sum_range_succ', show N - 0 = N by omega]
  simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_mul, add_zero]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro m hm
  have := mem_range.mp hm
  rw [show N - (N - 1 - m) = m + 1 by omega, show N - 1 - m = N - (m + 1) by omega, mul_comm]

/-- `Σ_{n ≤ N} (N - n) G(n) = Σ_{m<N} ψ(m) ψ(N - 1 - m)`. -/
lemma weighted_eq_fejerG (N : ℕ) :
    ∑ n ∈ range (N + 1), ((N : ℝ) - n) * G n = fejerG N := by
  rw [weighted_eq_sum_partial]
  induction N with
  | zero => simp [fejerG]
  | succ N ih => rw [sum_range_succ, ih, fejerG_succ, sum_G]

/-- `Σ_{m<N} ψ(m) = Σ_{a ≤ N} Λ(a) (N - a)`. -/
lemma sum_psiN (N : ℕ) : ∑ m ∈ range N, psiN m = ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc ∑ m ∈ range (N + 1), psiN m = ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) + psiN N := by
          rw [sum_range_succ, ih]
      _ = ∑ a ∈ range (N + 1), (Λ a * ((N : ℝ) - a) + Λ a) := by
          rw [sum_add_distrib]; rfl
      _ = ∑ a ∈ range (N + 1 + 1), Λ a * (((N + 1 : ℕ) : ℝ) - a) := by
          rw [sum_range_succ _ (N + 1)]
          have : Λ (N + 1) * (((N + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ)) = 0 := by rw [sub_self, mul_zero]
          rw [this, add_zero]
          exact sum_congr rfl fun a _ => by push_cast; ring

/-- `Σ_{m<N} (N - 1 - m) ψ(m) = Σ_{a ≤ N} Λ(a)(N - a)(N - a - 1)/2`. -/
lemma sum_weight_psiN (N : ℕ) :
    ∑ m ∈ range N, ((N : ℝ) - 1 - m) * psiN m =
      ∑ a ∈ range (N + 1), Λ a * (((N : ℝ) - a) * ((N : ℝ) - a - 1) / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc ∑ m ∈ range (N + 1), (((N + 1 : ℕ) : ℝ) - 1 - m) * psiN m
        = ∑ m ∈ range N, ((((N : ℝ) - 1 - m) * psiN m) + psiN m) + 0 := by
          rw [sum_range_succ]; congr 1
          · exact sum_congr rfl fun m _ => by push_cast; ring
          · push_cast; ring
      _ = ∑ a ∈ range (N + 1), Λ a * (((N : ℝ) - a) * ((N : ℝ) - a - 1) / 2) +
            ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) := by
          rw [add_zero, sum_add_distrib, ih, sum_psiN]
      _ = ∑ a ∈ range (N + 1 + 1), Λ a * ((((N + 1 : ℕ) : ℝ) - a) * (((N + 1 : ℕ) : ℝ) - a - 1) / 2) := by
          rw [sum_range_succ _ (N + 1), ← sum_add_distrib]
          have : Λ (N + 1) * ((((N + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ)) *
              (((N + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) - 1) / 2) = 0 := by rw [sub_self]; ring
          rw [this, add_zero]
          exact sum_congr rfl fun a _ => by push_cast; ring

/-- `Σ_{m<N} m (N - 1 - m) = N(N - 1)(N - 2)/6`. -/
lemma sum_m_mul (N : ℕ) : ∑ m ∈ range N, (m : ℝ) * ((N : ℝ) - 1 - m) =
    (N : ℝ) * (N - 1) * (N - 2) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hid : ∀ M : ℕ, ∑ m ∈ range M, (m : ℝ) = (M : ℝ) * (M - 1) / 2 := by
      intro M; induction M with
      | zero => simp
      | succ M ihM => rw [sum_range_succ, ihM]; push_cast; ring
    calc ∑ m ∈ range (N + 1), (m : ℝ) * (((N + 1 : ℕ) : ℝ) - 1 - m)
        = ∑ m ∈ range N, ((m : ℝ) * ((N : ℝ) - 1 - m) + m) + (N : ℝ) * 0 := by
          rw [sum_range_succ]; congr 1
          · exact sum_congr rfl fun m _ => by push_cast; ring
          · push_cast; ring
      _ = _ := by rw [mul_zero, add_zero, sum_add_distrib, ih, hid]; push_cast; ring

/-! ### The second Riesz mean -/

/-- `Q(N) = Σ_{a ≤ N} Λ(a)(N - a)²/2`. -/
def Q2 (N : ℕ) : ℝ := ∑ a ∈ range (N + 1), Λ a * (((N : ℝ) - a) ^ 2 / 2)

/-- `Σ_ρ N^{ρ+1}/(ρ(ρ+1)(ρ+2))`. -/
def Z2 (N : ℝ) : ℂ := zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1) * (ρ + 2)))

lemma integral_max_sub {k N : ℝ} (hk : 0 ≤ k) (hkN : k ≤ N) :
    ∫ u in (0 : ℝ)..N, max 0 (u - k) = (N - k) ^ 2 / 2 := by
  have hc : Continuous fun u : ℝ => max 0 (u - k) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := k) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ u in (0 : ℝ)..k, max 0 (u - k) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u hu => by
      rw [Set.uIcc_of_le hk] at hu
      simp only; rw [max_eq_left (by linarith [hu.2])])]
    simp
  have h2 : ∫ u in k..N, max 0 (u - k) = (N - k) ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun u => u - k) (fun u hu => by
      rw [Set.uIcc_of_le hkN] at hu
      simp only; rw [max_eq_right (by linarith [hu.1])])]
    rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ => k)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1, h2, zero_add]

lemma continuous_Rg (M : ℕ) : Continuous fun u : ℝ => LZCesaroShort.Rg M u := by
  unfold LZCesaroShort.Rg; fun_prop

lemma integral_Rg (N : ℕ) : ∫ u in (0 : ℝ)..N, LZCesaroShort.Rg N u = Q2 N := by
  unfold LZCesaroShort.Rg Q2
  rw [intervalIntegral.integral_finset_sum]
  swap
  · intro k _
    exact (continuous_const.mul (by fun_prop : Continuous fun u : ℝ => max 0 (u - k))).intervalIntegrable _ _
  apply sum_congr rfl; intro k hk
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [intervalIntegral.integral_const_mul, integral_max_sub (Nat.cast_nonneg k) hk']

open PNTPort.ExplicitPsi1 in
lemma integral_Wf (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (0 : ℝ)..N, LZCesaroShort.Wf u = (N : ℂ) * Z2 N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← (LZCesaroShort.hasSum_integral_W le_rfl hN0.le).tsum_eq]
  have e : ∀ ρ : Zall, ∫ u in (0 : ℝ)..N, LZCesaroShort.wterm u ρ =
      (N : ℂ) * ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((N : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1) * (ρ.1 + 2)))) := by
    intro ρ
    rw [LZCesaroShort.integral_wterm ρ.2]
    have h2 : ρ.1 + 2 ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
      linarith [LZCesaroShort.Zall_re_pos ρ.2]
    have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [Complex.ofReal_zero, zero_cpow h2, sub_zero,
      show ρ.1 + 2 = (ρ.1 + 1) + 1 by ring, cpow_add _ _ hNc, cpow_one]
    push_cast; ring
  simp_rw [e]
  rw [tsum_mul_left, Z2, zeroSum]
  congr 1
  have e2 : (∑' ρ : Zall, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((N : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1) * (ρ.1 + 2)))) =
      ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((N : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1) * (ρ.1 + 2))) := by
    rw [Zall_eq]; rfl
  rw [e2]; push_cast; rfl

open PNTPort.ExplicitPsi1 in
/-- The zero sum of Goldston-Yang Theorem 2 converges absolutely: for every `N ≥ 1` the family
`ρ ↦ m(ρ) N^{ρ+1}/(ρ(ρ+1)(ρ+2))` over the nontrivial zeros is summable, so `zeroSum` is its
genuine unordered sum, not the junk value `0`. Unconditional. -/
theorem gy_zeroSum_summable (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((N : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1) * (ρ.1 + 2)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := (LZCesaroShort.hasSum_integral_W (a := 0) (b := N) le_rfl hN0.le).summable
  have e : ∀ ρ : Zall, ∫ u in (0 : ℝ)..N, LZCesaroShort.wterm u ρ =
      (N : ℂ) * ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((N : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1) * (ρ.1 + 2)))) := by
    intro ρ
    rw [LZCesaroShort.integral_wterm ρ.2]
    have h2 : ρ.1 + 2 ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
      linarith [LZCesaroShort.Zall_re_pos ρ.2]
    have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [Complex.ofReal_zero, zero_cpow h2, sub_zero,
      show ρ.1 + 2 = (ρ.1 + 1) + 1 by ring, cpow_add _ _ hNc, cpow_one]
    push_cast; ring
  simp_rw [e] at hs
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hs2 := (summable_mul_left_iff hNc).mp hs
  rw [Zall_eq] at hs2
  exact hs2

/-- **The second Riesz mean, explicit.** `Q(N) = N³/6 - (ζ'/ζ)(0) N²/2 - N Z₂(N) + O(N²)`. -/
theorem Q2_explicit : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
    ‖((Q2 N : ℝ) : ℂ) - ((N : ℂ) ^ 3 / 6 - (N : ℂ) ^ 2 / 2 * (deriv riemannZeta 0 / riemannZeta 0)
      - (N : ℂ) * Z2 N)‖ ≤ K * ((N : ℝ) ^ 2 / 2 + N) := by
  obtain ⟨K, hK0, hK⟩ := LZCesaroShort.psi1_formula
  refine ⟨K, hK0, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0
  set F : ℝ → ℂ := fun u => ((LZCesaroShort.Rg N u : ℝ) : ℂ) -
    ((u : ℂ) ^ 2 / 2 - u * d0 - LZCesaroShort.Wf u) with hF
  have hRgc : IntervalIntegrable (fun u : ℝ => ((LZCesaroShort.Rg N u : ℝ) : ℂ))
      MeasureTheory.volume 0 N :=
    (Complex.continuous_ofReal.comp (continuous_Rg N)).intervalIntegrable _ _
  have hpc : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ 2 / 2 - u * d0) MeasureTheory.volume 0 N :=
    (by fun_prop : Continuous fun u : ℝ => (u : ℂ) ^ 2 / 2 - u * d0).intervalIntegrable _ _
  have hW := LZCesaroShort.Wf_intervalIntegrable le_rfl hN0.le
  have hint : ∫ u in (0 : ℝ)..N, F u = ((Q2 N : ℝ) : ℂ) -
      ((N : ℂ) ^ 3 / 6 - (N : ℂ) ^ 2 / 2 * d0 - (N : ℂ) * Z2 N) := by
    simp only [hF]
    rw [intervalIntegral.integral_sub hRgc (hpc.sub hW), intervalIntegral.integral_sub hpc hW,
      intervalIntegral.integral_ofReal, integral_Rg, integral_Wf N hN]
    have e1 : ∫ u in (0 : ℝ)..N, ((u : ℂ) ^ 2 / 2 - u * d0) = (N : ℂ) ^ 3 / 6 - (N : ℂ) ^ 2 / 2 * d0 := by
      have : (fun u : ℝ => (u : ℂ) ^ 2 / 2 - u * d0) =
          fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ) - ((u : ℝ) : ℂ) * d0 := by
        funext u; push_cast; ring
      rw [this, intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun u : ℝ => ((u : ℝ) : ℂ) * d0).intervalIntegrable _ _),
        intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_div, integral_pow, integral_id]
      push_cast; ring
    rw [e1]
  rw [← hint]
  have hb : ∫ u in (0 : ℝ)..N, K * (u + 1) = K * ((N : ℝ) ^ 2 / 2 + N) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (f := fun x : ℝ => x)
      (g := fun _ => (1 : ℝ)) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hb]
  apply intervalIntegral.norm_integral_le_of_norm_le hN0.le
  · refine MeasureTheory.ae_of_all _ fun u hu => ?_
    exact hK N u hu.1 hu.2
  · exact (by fun_prop : Continuous fun u : ℝ => K * (u + 1)).intervalIntegrable _ _

/-! ### Assembly -/

lemma psiN_le (m : ℕ) : psiN m ≤ 6 * m := by
  rw [psiN_eq]
  have := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have h4 : Real.log 4 + 4 ≤ 6 := by
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    linarith
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- The decomposition `F(N) = 2 Q(N) - ψ₁(N) - S₃(N) + Σ E E`. -/
lemma fejerG_decomp (N : ℕ) :
    fejerG N = 2 * Q2 N - ∑ m ∈ range N, psiN m - (N : ℝ) * (N - 1) * (N - 2) / 6 +
      ∑ m ∈ range N, (psiN m - m) * (psiN (N - 1 - m) - ((N - 1 - m : ℕ) : ℝ)) := by
  set E : ℕ → ℝ := fun m => psiN m - m with hE
  have hcast : ∀ m ∈ range N, ((N - 1 - m : ℕ) : ℝ) = (N : ℝ) - 1 - m := by
    intro m hm; have := mem_range.mp hm
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hterm : ∀ m ∈ range N, psiN m * psiN (N - 1 - m) =
      (m : ℝ) * ((N : ℝ) - 1 - m) + (m : ℝ) * E (N - 1 - m) + ((N : ℝ) - 1 - m) * E m +
        E m * E (N - 1 - m) := by
    intro m hm
    simp only [hE]; rw [hcast m hm]; ring
  have hrefl : ∑ m ∈ range N, (m : ℝ) * E (N - 1 - m) = ∑ m ∈ range N, ((N : ℝ) - 1 - m) * E m := by
    rw [← sum_range_reflect]
    apply sum_congr rfl; intro m hm
    have := mem_range.mp hm
    rw [show N - 1 - (N - 1 - m) = m by omega, hcast m hm]
  have hW : ∑ m ∈ range N, ((N : ℝ) - 1 - m) * E m =
      ∑ m ∈ range N, ((N : ℝ) - 1 - m) * psiN m - ∑ m ∈ range N, (m : ℝ) * ((N : ℝ) - 1 - m) := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro m _; simp only [hE]; ring
  have hW2 : ∑ m ∈ range N, ((N : ℝ) - 1 - m) * psiN m = Q2 N - (∑ m ∈ range N, psiN m) / 2 := by
    rw [sum_weight_psiN, sum_psiN, Q2, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl; intro a _; ring
  have hEE : ∑ m ∈ range N, E m * E (N - 1 - m) =
      ∑ m ∈ range N, (psiN m - m) * (psiN (N - 1 - m) - ((N - 1 - m : ℕ) : ℝ)) := rfl
  unfold fejerG
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, sum_add_distrib, hrefl, hW, hW2,
    sum_m_mul, ← hEE]
  ring

lemma abs_EE_le (N : ℕ) :
    |∑ m ∈ range N, (psiN m - m) * (psiN (N - 1 - m) - ((N - 1 - m : ℕ) : ℝ))| ≤
      ∑ m ∈ range N, (Chebyshev.psi m - m) ^ 2 := by
  set E : ℕ → ℝ := fun m => psiN m - m with hE
  have hrefl : ∑ m ∈ range N, E (N - 1 - m) ^ 2 = ∑ m ∈ range N, E m ^ 2 :=
    sum_range_reflect (fun m => E m ^ 2) N
  have hsq : ∑ m ∈ range N, E m ^ 2 = ∑ m ∈ range N, (Chebyshev.psi m - m) ^ 2 := by
    apply sum_congr rfl; intro m _; simp only [hE]; rw [psiN_eq]
  have e : ∑ m ∈ range N, (psiN m - m) * (psiN (N - 1 - m) - ((N - 1 - m : ℕ) : ℝ)) =
      ∑ m ∈ range N, E m * E (N - 1 - m) := rfl
  rw [e, ← hsq]
  calc |∑ m ∈ range N, E m * E (N - 1 - m)| ≤ ∑ m ∈ range N, |E m * E (N - 1 - m)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ range N, (E m ^ 2 + E (N - 1 - m) ^ 2) / 2 := by
        apply sum_le_sum; intro m _
        rw [abs_mul]
        have := two_mul_le_add_sq |E m| |E (N - 1 - m)|
        rw [sq_abs, sq_abs] at this; linarith
    _ = ∑ m ∈ range N, E m ^ 2 := by rw [← sum_div, sum_add_distrib, hrefl]; ring

/-- **Goldston-Yang Theorem 2 under RH**, the cited `gy_theorem2`. -/
theorem gy_theorem2_proved : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), (1 - (n : ℝ) / N) * G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 6
      + 2 * zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1) * (ρ + 2)))‖ ≤ K * N := by
  intro hRH
  obtain ⟨Kq, hKq0, hQ⟩ := Q2_explicit
  obtain ⟨Kc, hKc0, hc⟩ := PNTPort.Selberg.cramer_sum hRH
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hd0
  refine ⟨2 * Kq + 8 + ‖d0‖ + Kc, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set GY := ∑ n ∈ range (N + 1), (1 - (n : ℝ) / N) * G n with hGYdef
  set ps := ∑ m ∈ range N, psiN m with hps
  set EE := ∑ m ∈ range N, (psiN m - m) * (psiN (N - 1 - m) - ((N - 1 - m : ℕ) : ℝ)) with hEEdef
  have hGY : GY * N = fejerG N := by
    rw [← weighted_eq_fejerG, hGYdef, sum_mul]
    apply sum_congr rfl; intro n _
    field_simp
  have hF := fejerG_decomp N
  rw [← hps, ← hEEdef] at hF
  have hps0 : 0 ≤ ps := sum_nonneg fun m _ => psiN_nonneg m
  have hps1 : ps ≤ 6 * (N : ℝ) ^ 2 := by
    calc ps ≤ ∑ _m ∈ range N, 6 * (N : ℝ) := by
          apply sum_le_sum; intro m hm
          have := mem_range.mp hm
          have h1 := psiN_le m
          have : (m : ℝ) ≤ N := by exact_mod_cast this.le
          linarith
      _ = 6 * (N : ℝ) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hEE : |EE| ≤ Kc * (N : ℝ) ^ 2 := (abs_EE_le N).trans (hc N)
  have hQN := hQ N (by omega)
  set errQ : ℂ := ((Q2 N : ℝ) : ℂ) - ((N : ℂ) ^ 3 / 6 - (N : ℂ) ^ 2 / 2 * d0 - (N : ℂ) * Z2 N)
    with herrQ
  have hGYc : ((GY : ℝ) : ℂ) * N = ((fejerG N : ℝ) : ℂ) := by exact_mod_cast hGY
  have hFc : ((fejerG N : ℝ) : ℂ) = 2 * ((Q2 N : ℝ) : ℂ) - (ps : ℂ) -
      (N : ℂ) * (N - 1) * (N - 2) / 6 + (EE : ℂ) := by rw [hF]; push_cast; ring
  have key : (N : ℂ) * (((GY : ℝ) : ℂ) - (N : ℂ) ^ 2 / 6 + 2 * Z2 N) =
      2 * errQ + ((((N : ℝ) ^ 2 / 2 - N / 3 - ps + EE : ℝ)) : ℂ) - (N : ℂ) ^ 2 * d0 := by
    rw [herrQ]; push_cast
    linear_combination hGYc + hFc
  have hZ : zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1) * (ρ + 2))) = Z2 N := by
    rw [Z2]; push_cast; rfl
  rw [hZ]
  have hnorm : ‖(N : ℂ) * (((GY : ℝ) : ℂ) - (N : ℂ) ^ 2 / 6 + 2 * Z2 N)‖ ≤
      (2 * Kq + 8 + ‖d0‖ + Kc) * N * N := by
    rw [key]
    have h1 : ‖2 * errQ‖ ≤ 2 * Kq * ((N : ℝ) ^ 2 / 2 + N) := by
      rw [norm_mul, Complex.norm_two]; linarith
    have h2 : ‖((((N : ℝ) ^ 2 / 2 - N / 3 - ps + EE : ℝ)) : ℂ)‖ ≤ (N : ℝ) ^ 2 / 2 + N / 3 + 6 * (N : ℝ) ^ 2 +
        Kc * (N : ℝ) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      rw [abs_le] at hEE
      constructor <;> nlinarith
    have h3 : ‖(N : ℂ) ^ 2 * d0‖ = (N : ℝ) ^ 2 * ‖d0‖ := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc ‖2 * errQ + ((((N : ℝ) ^ 2 / 2 - N / 3 - ps + EE : ℝ)) : ℂ) - (N : ℂ) ^ 2 * d0‖
        ≤ ‖2 * errQ‖ + ‖((((N : ℝ) ^ 2 / 2 - N / 3 - ps + EE : ℝ)) : ℂ)‖ + ‖(N : ℂ) ^ 2 * d0‖ :=
          norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ (2 * Kq + 8 + ‖d0‖ + Kc) * N * N := by
          rw [h3]
          have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by nlinarith
          have hd : 0 ≤ ‖d0‖ := norm_nonneg _
          nlinarith
  rw [norm_mul, Complex.norm_natCast] at hnorm
  have := le_of_mul_le_mul_left (by nlinarith : (N : ℝ) * ‖((GY : ℝ) : ℂ) - (N : ℂ) ^ 2 / 6 + 2 * Z2 N‖ ≤
    (N : ℝ) * ((2 * Kq + 8 + ‖d0‖ + Kc) * N)) hN0
  exact this

end LeanLab.GoldbachAverage
