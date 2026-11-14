module

public import Mathlib
public import LeanLab.PNTPort.Vinogradov.Final
public import LeanLab.Linnik.Decomp1532b
public import LeanLab.Linnik.Gallagher1975Lemma2
public import LeanLab.Romanov.GallagherBridge
public import LeanLab.ExceptionalSet.MVMajorSing
public import LeanLab.Common.CircleOrth
public import LeanLab.Linnik.Decomp466c

/-!
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File c: display (6) for `k ≥ k₀`, p. 139, the last analytic input of the lab's proof of
Theorems 1 and 2; every leaf below is proved. The integral over `[0, 1]` is split as on p. 138 into the major arcs
`𝔐`, the part `C(𝔐) ∩ ℰ` where `|G| ≥ (1 - η)L`, and `C(𝔐) ∩ C(ℰ)`, with
`η = (log k)/k` and `θ = 2 ε(η)`, `ε(η) = (4/log 2) η log(e/η)` the exponent of Lemma 2.
Leaves: display (5) on the major arcs, Lemma 11 off the major arcs, four parameter facts, the
measurability of `𝔐`, and the identity of the two spellings of `G`.
Assemblies: `display6Large_of_leaves`, display (6) for large `k`, and from it Theorems 1 and 2,
display (3) and (4) p. 125, through the lab's proved Lemma 12 and Lemma 2.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- `η = (log k)/k`, p. 139. -/
noncomputable def etaK (k : ℕ) : ℝ := Real.log k / k

/-- `ε(η) = (4/log 2) η log(e/η)`, the exponent of the lab's Lemma 2 for g = 2, p. 132. -/
noncomputable def epsK (k : ℕ) : ℝ :=
  4 / Real.log 2 * etaK k * Real.log (Real.exp 1 / etaK k)

/-- `θ = 2 ε(η)`, the choice `θ = 2Cη log(e/η)` of p. 139. -/
noncomputable def thetaK (k : ℕ) : ℝ := 2 * epsK k

/-- Auxiliary parameter estimate for Gallagher 1975 p.139. -/
theorem thetaK_bounds (k : ℕ) (hk : 3 ≤ k) :
    0 < thetaK k ∧ thetaK k ≤ (8 / Real.log 2) * etaK k * (1 + Real.log k) := by
  unfold thetaK epsK etaK
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hk0]
    exact (Real.exp_one_lt_d9.le).trans (by linarith)
  have he0 : 0 < Real.log k / k := div_pos (by linarith) hk0
  have he1 : Real.log k / k < 1 := (div_lt_one hk0).2 (by linarith [Real.log_le_sub_one_of_pos hk0])
  have hlogpos : 0 < Real.log (Real.exp 1 / (Real.log k / k)) := by
    apply Real.log_pos
    rw [one_lt_div he0]
    exact he1.trans (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hlogle : Real.log (Real.exp 1 / (Real.log k / k)) ≤ 1 + Real.log k := by
    calc _ ≤ Real.log (Real.exp 1 * k) := by
           apply Real.log_le_log (by positivity)
           rw [div_le_iff₀ he0]
           have : Real.exp 1 * k * (Real.log k / k) = Real.exp 1 * Real.log k := by field_simp
           rw [this]
           nlinarith [Real.exp_pos 1]
         _ = _ := by rw [Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
  constructor
  · positivity
  · calc _ = (8 / Real.log 2) * (Real.log k / k) * Real.log (Real.exp 1 / (Real.log k / k)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlogle (by positivity)

/-- Auxiliary parameter estimate for Gallagher 1975 p.139. -/
theorem thetaK_mul_log_tendsto_zero : Filter.Tendsto (fun k : ℕ => thetaK k * Real.log k)
    Filter.atTop (nhds 0) := by
  have h2 := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h3 := (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu : Tendsto (fun k : ℕ => (8 / Real.log 2) * (Real.log k / k) *
      (1 + Real.log k) * Real.log k) atTop (𝓝 0) := by
    convert (h2.add h3).const_mul (8 / Real.log 2) using 1
    · ext k; dsimp; ring
    · simp
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop 3] with k hk
    exact mul_nonneg (thetaK_bounds k hk).1.le (Real.log_natCast_nonneg k)
  · filter_upwards [eventually_ge_atTop 3] with k hk
    exact mul_le_mul_of_nonneg_right (thetaK_bounds k hk).2 (Real.log_natCast_nonneg k)

/-- LEAF. Unit U-1532. The major arcs form a measurable set, p. 127, display (2). -/
theorem measurableSet_majorArcs (N : ℕ) (P : ℝ) : MeasurableSet (majorArcs N P) := by
  classical
  unfold majorArcs
  simp only [Set.ofPred_and, Set.ofPred_exists]
  refine measurableSet_Icc.inter (MeasurableSet.iUnion fun q => ?_)
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (MeasurableSet.iUnion fun a => ?_))
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet)

/-- LEAF. Unit U-1532. The two spellings of `G(α) = Σ_{ν=1}^{L} e(2^ν α)` in the lab agree,
p. 132. -/
theorem G_eq_Gs (L : ℕ) (α : ℝ) : LeanLab.Linnik.Gallagher1975Lemma1.G L α = Gs L α := by
  unfold LeanLab.Linnik.Gallagher1975Lemma1.G Gs
  apply Finset.sum_congr rfl
  intro ν hν
  unfold LeanLab.Linnik.Gallagher1975Lemma1.e LeanLab.Linnik.U1412Display53.eC
  congr 1
  push_cast
  ring



/-- Auxiliary for the minor arc estimate on p.137 of Gallagher 1975. -/
theorem vonMangoldt_prefix_bound {N q : ℕ} (hN : 2 ≤ N) {θ : ℝ} (hθ : 0 < θ) (hθmax : θ ≤ 2 / 5)
    (hq : (N : ℝ) ^ θ < q) (hqmax : (q : ℝ) ≤ N / (N : ℝ) ^ θ)
    {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) :
    ∀ m : ℕ, m ≤ N → ‖LeanLab.PNTPort.Vinogradov.S m α‖ ≤
      (900 + (Real.log 4 + 4)) * N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have hp : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow hn hθ.le
  have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
  have hqN : q ≤ N := by
    exact_mod_cast hqmax.trans (div_le_self hn0.le hp)
  have ht : 0 < (N : ℝ) ^ (θ / 2) := Real.rpow_pos_of_pos hn0 _
  have ht2 : ((N : ℝ) ^ (θ / 2)) ^ 2 = (N : ℝ) ^ θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    norm_num
  have hs : (N : ℝ) ^ (θ / 2) ≤ Real.sqrt q := by
    rw [Real.le_sqrt ht.le (Nat.cast_nonneg q), ht2]
    exact hq.le
  have h1 : (N : ℝ) / Real.sqrt q ≤ N / (N : ℝ) ^ (θ / 2) :=
    div_le_div_of_nonneg_left hn0.le ht hs
  have h2 : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ N / (N : ℝ) ^ (θ / 2) := by
    calc (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (N : ℝ) ^ (1 - θ / 2) :=
           Real.rpow_le_rpow_of_exponent_le hn (by linarith)
         _ = N / (N : ℝ) ^ (θ / 2) := by rw [Real.rpow_sub hn0, Real.rpow_one]
  have h3 : Real.sqrt (N * q) ≤ (N : ℝ) / (N : ℝ) ^ (θ / 2) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hb := mul_le_mul_of_nonneg_left hqmax hn0.le
    rw [div_pow, ht2]
    calc (N : ℝ) * q ≤ N * (N / (N : ℝ) ^ θ) := hb
         _ = (N : ℝ) ^ 2 / (N : ℝ) ^ θ := by ring

  have hL : 1 ≤ (1 + Real.log N) ^ 4 := one_le_pow₀ (by linarith [Real.log_natCast_nonneg N])
  have hmain : 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
      (1 + Real.log N) ^ 4 ≤ 900 * N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 := by
    calc _ ≤ 300 * (3 * (N / (N : ℝ) ^ (θ / 2))) * (1 + Real.log N) ^ 4 := by gcongr; linarith
         _ = _ := by ring
  intro m hm
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hc0 : 0 ≤ Real.log 4 + 4 := by positivity
  by_cases hqm : q ≤ m
  · have hm1 : 1 ≤ m := hq1.trans hqm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq1 hcop hα hqm
    calc _ ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        (1 + Real.log N) ^ 4 := by
          apply h.trans
          gcongr
      _ ≤ 900 * N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 := hmain
      _ ≤ _ := by gcongr; linarith
  · have hmQ : (m : ℝ) ≤ q := by exact_mod_cast (show m ≤ q by omega)
    have hpow : (N : ℝ) ^ (θ / 2) ≤ (N : ℝ) ^ θ :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    have hmT : (m : ℝ) ≤ N / (N : ℝ) ^ (θ / 2) :=
      hmQ.trans (hqmax.trans (div_le_div_of_nonneg_left hn0.le ht hpow))
    have htriv : ‖LeanLab.PNTPort.Vinogradov.S m α‖ ≤ Chebyshev.psi m := by
      unfold LeanLab.PNTPort.Vinogradov.S Chebyshev.psi
      rw [Nat.floor_natCast]
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
      rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc _ ≤ (Real.log 4 + 4) * m := htriv.trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg m))
         _ ≤ (Real.log 4 + 4) * (N / (N : ℝ) ^ (θ / 2)) * (1 + Real.log N) ^ 4 := by
           exact (mul_le_mul_of_nonneg_left hmT hc0).trans (le_mul_of_one_le_right (by positivity) hL)
         _ ≤ _ := by
           have hterm : 0 ≤ N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 := by positivity
           convert mul_le_mul_of_nonneg_right
             (show Real.log 4 + 4 ≤ 900 + (Real.log 4 + 4) by linarith) hterm using 1 <;> ring


/-- Auxiliary for the minor arc estimate on p.137 of Gallagher 1975. -/
theorem norm_sum_div_log_le {N : ℕ} (hN : 2 ≤ N) (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ m ∈ Icc 2 N, ‖∑ n ∈ Icc 2 m, f n‖ ≤ B) :
    ‖∑ n ∈ Icc 2 N, f n / (Real.log n : ℂ)‖ ≤ B / Real.log 2 := by
  let F (m : ℕ) := ∑ n ∈ Icc 2 m, f n
  let U (m : ℕ) := ∑ n ∈ Icc 2 m, f n / (Real.log n : ℂ)
  have hid : ∀ m : ℕ, 2 ≤ m → U m = F m / (Real.log m : ℂ) +
      ∑ n ∈ Ico 2 m, F n * ((1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) : ℝ) : ℂ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp [U, F]
    | succ m hm ih =>
      have hu : U (m + 1) = U m + f (m + 1) / (Real.log ((m : ℝ) + 1) : ℂ) := by
        dsimp [U]; rw [sum_Icc_succ_top (by omega)]; push_cast; rfl
      have hf : F (m + 1) = F m + f (m + 1) := by
        dsimp [F]; rw [sum_Icc_succ_top (by omega)]
      rw [hu, hf, ih, sum_Ico_succ_top hm]
      push_cast
      ring
  have htele : ∑ n ∈ Ico 2 N, (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
      1 / Real.log 2 - 1 / Real.log N := by
    clear hB
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih => rw [sum_Ico_succ_top hN, ih]; push_cast; ring
  have hd : ∀ n ∈ Ico 2 N, 0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hlog (Real.log_le_log (by linarith) (by linarith))
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  change ‖U N‖ ≤ _
  rw [hid N hN]
  calc
    _ ≤ ‖F N‖ / Real.log N + ∑ n ∈ Ico 2 N, ‖F n‖ *
        (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlN]
      · refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd n hn)]
    _ ≤ B / Real.log N + ∑ n ∈ Ico 2 N, B *
        (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (hB N (mem_Icc.mpr ⟨hN, le_rfl⟩)) hlN.le
      · apply sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_right _ (hd n hn)
        exact hB n (mem_Icc.mpr ⟨(mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩)
    _ = B / Real.log 2 := by rw [← mul_sum, htele]; ring


/-- Auxiliary for the major arc expansion on p.138 of Gallagher 1975. -/
theorem major_arc_integrand_expand (k L N : ℕ) (α : ℝ) :
    ‖Sg N α * Gs L α ^ k‖ ^ 2 =
      ∑ x : LeanLab.Linnik.Decomp1532a.pairs k L, ‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re := by
  classical
  have hG : Gs L α ^ k * (starRingEnd ℂ) (Gs L α ^ k) =
      ∑ x : LeanLab.Linnik.Decomp1532a.pairs k L, LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α) := by
    simp_rw [LeanLab.Linnik.U1434Lemma21.Gs_pow]
    simp_rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
    simp only [map_sum, sum_mul, mul_sum, Fintype.sum_prod_type]
    conv_lhs => rw [sum_comm]
    refine sum_congr rfl fun ν _ => sum_congr rfl fun μ _ => ?_
    rw [← LeanLab.PNTPort.LargeSieve.e_neg, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    dsimp [LeanLab.Linnik.Decomp1532a.dif]
    push_cast
    ring
  have hr := congrArg Complex.re hG
  simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] at hr
  rw [norm_mul, mul_pow, hr, mul_sum]


/-- Auxiliary for the major arc expansion on p.138 of Gallagher 1975. -/
theorem major_arc_integral_expand (k L N : ℕ) (P : ℝ) :
    ∫ α in majorArcs N P, ‖Sg N α * Gs L α ^ k‖ ^ 2 =
      ∑ x : LeanLab.Linnik.Decomp1532a.pairs k L, ∫ α in majorArcs N P,
        ‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re := by
  simp_rw [LeanLab.Linnik.Decomp1532c.major_arc_integrand_expand]
  apply integral_finsetSum
  intro x hx
  have hf : Continuous (fun α : ℝ =>
      ‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    have hs := LeanLab.Linnik.U7206.continuous_Sg N
    fun_prop
  exact hf.integrableOn_Icc.mono_set (fun α (h : α ∈ majorArcs N P) => h.1)


/-- Auxiliary for the major arc expansion on p.138 of Gallagher 1975. -/
theorem major_arc_Sg_mean_le (N : ℕ) (P : ℝ) :
    ∫ α in majorArcs N P, ‖Sg N α‖ ^ 2 ≤ Nat.primeCounting N := by
  have hi : IntegrableOn (fun α => ‖Sg N α‖ ^ 2) (Set.Icc (0 : ℝ) 1) :=
    ((LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2).integrableOn_Icc
  have hmono := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖Sg N α‖))
    (Filter.Eventually.of_forall (fun α (h : α ∈ majorArcs N P) => h.1))
  have hfull : ∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α‖ ^ 2 = (primesLe N).card := by
    simpa [Sg] using LeanLab.Linnik.U1426ChainWire.parseval (primesLe N) (fun _ => 1)
  have hc : (primesLe N).card = Nat.primeCounting N := Nat.primesLE_card_eq_primeCounting N
  rw [hfull] at hmono
  exact hmono.trans_eq (by exact_mod_cast hc)


/-- Auxiliary for the major arc expansion on p.138 of Gallagher 1975. -/
theorem major_arc_Sg_mean_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P : ℝ,
      ∫ α in majorArcs N P, ‖Sg N α‖ ^ 2 ≤ (Real.log 4 + ε) * N / Real.log N := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hε)
  simp only [Nat.floor_natCast] at h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, fun N hN P => (major_arc_Sg_mean_le N P).trans (hN₀ N hN)⟩


/-- Auxiliary for the major arc expansion on p.138 of Gallagher 1975. -/
theorem major_arc_diagonal_split (k L N : ℕ) (P : ℝ) :
    ∫ α in majorArcs N P, ‖Sg N α * Gs L α ^ k‖ ^ 2 =
      (((univ : Finset (LeanLab.Linnik.Decomp1532a.pairs k L)).filter (fun x => LeanLab.Linnik.Decomp1532a.dif x = 0)).card : ℝ) *
        (∫ α in majorArcs N P, ‖Sg N α‖ ^ 2) +
      ∑ x : LeanLab.Linnik.Decomp1532a.pairs k L with LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N P,
        ‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re := by
  classical
  rw [LeanLab.Linnik.Decomp1532c.major_arc_integral_expand,
    ← sum_filter_add_sum_filter_not univ (fun x : LeanLab.Linnik.Decomp1532a.pairs k L => LeanLab.Linnik.Decomp1532a.dif x = 0)]
  congr 1
  calc _ = ∑ x ∈ (univ : Finset (LeanLab.Linnik.Decomp1532a.pairs k L)).filter (fun x => LeanLab.Linnik.Decomp1532a.dif x = 0),
        ∫ α in majorArcs N P, ‖Sg N α‖ ^ 2 := by
          apply sum_congr rfl
          intro x hx
          simp only [mem_filter] at hx
          simp [hx.2, LeanLab.PNTPort.LargeSieve.e_zero]
       _ = _ := by simp


/-- Auxiliary for the major arc expansion on p.138 of Gallagher 1975. -/
theorem major_arc_crude_bound (k L N : ℕ) (P : ℝ) :
    ∫ α in majorArcs N P, ‖Sg N α * Gs L α ^ k‖ ^ 2 ≤
      (Nat.primeCounting N : ℝ) * (L : ℝ) ^ (2 * k) := by
  have hs := LeanLab.Linnik.U7206.continuous_Sg N
  have hsub : majorArcs N P ⊆ Set.Icc (0 : ℝ) 1 := fun α h => h.1
  have hfi : IntegrableOn (fun α => ‖Sg N α * Gs L α ^ k‖ ^ 2) (majorArcs N P) :=
    (((hs.mul ((continuous_Gs L).pow k)).norm.pow 2).integrableOn_Icc).mono_set hsub
  have hgi : IntegrableOn (fun α => ‖Sg N α‖ ^ 2 * (L : ℝ) ^ (2 * k)) (majorArcs N P) :=
    (((hs.norm.pow 2).integrableOn_Icc).mono_set hsub).mul_const _
  have hpt : ∀ α ∈ majorArcs N P,
      ‖Sg N α * Gs L α ^ k‖ ^ 2 ≤ ‖Sg N α‖ ^ 2 * (L : ℝ) ^ (2 * k) := by
    intro α hα
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm k 2]
    gcongr
    exact LeanLab.Linnik.U7206.norm_Gs_le L α
  have hmono := setIntegral_mono_on hfi hgi
    (LeanLab.Linnik.Decomp1532c.measurableSet_majorArcs N P) hpt
  rw [integral_mul_const] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_right
    (LeanLab.Linnik.Decomp1532c.major_arc_Sg_mean_le N P) (by positivity))


/-- Gallagher 1975 p.134 proof of Lemma 5. Auxiliary binary uniqueness. -/
theorem two_pow_add_sorted {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) : a = c ∧ b = d := by
  have hp : Function.Injective (fun n : ℕ => 2 ^ n) := Nat.pow_right_injective (by decide)
  by_cases hab' : a = b
  · subst b
    have hleft : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := by simp [pow_succ]; omega
    rw [hleft] at h
    by_cases hcd' : c = d
    · subst d
      have hright : 2 ^ c + 2 ^ c = 2 ^ (c + 1) := by simp [pow_succ]; omega
      rw [hright] at h
      have := hp h
      constructor <;> omega
    · have hc : c < d := by omega
      have h1 := Nat.bitIndices_sum_map_two_pow (L := [a + 1]) (by simp [List.sortedLT_iff_pairwise])
      have h2 := Nat.bitIndices_sum_map_two_pow (L := [c, d]) (by simpa [List.sortedLT_iff_pairwise] using hc)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1 h2
      rw [← h] at h2
      rw [h1] at h2
      simp at h2
  · have ha : a < b := by omega
    have h1 := Nat.bitIndices_sum_map_two_pow (L := [a, b]) (by simpa [List.sortedLT_iff_pairwise] using ha)
    by_cases hcd' : c = d
    · subst d
      have hright : 2 ^ c + 2 ^ c = 2 ^ (c + 1) := by simp [pow_succ]; omega
      rw [hright] at h
      have h2 := Nat.bitIndices_sum_map_two_pow (L := [c + 1]) (by simp [List.sortedLT_iff_pairwise])
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1 h2
      rw [h] at h1
      rw [h2] at h1
      simp at h1
    · have hc : c < d := by omega
      have h2 := Nat.bitIndices_sum_map_two_pow (L := [c, d]) (by simpa [List.sortedLT_iff_pairwise] using hc)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1 h2
      rw [h] at h1
      rw [h2] at h1
      simpa using h1.symm


/-- Gallagher 1975 p.134 proof of Lemma 5. -/
theorem two_pow_add_eq {a b c d : ℕ} (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · exact Or.inl (two_pow_add_sorted hab hcd h)
    · have hs := two_pow_add_sorted hab hdc (by simpa [add_comm] using h)
      exact Or.inr hs
  · rcases le_total c d with hcd | hdc
    · have hs := two_pow_add_sorted hba hcd (by simpa [add_comm] using h)
      exact Or.inr ⟨hs.2, hs.1⟩
    · have hs := two_pow_add_sorted hba hdc (by simpa [add_comm] using h)
      exact Or.inl ⟨hs.2, hs.1⟩


/-- Gallagher 1975 p.134 proof of Lemma 5. Auxiliary finite interval form. -/
theorem two_pow_pair_fiber_card (L n : ℕ) :
    #{x ∈ (univ : Finset (Fin L × Fin L)) | 2 ^ (x.1 : ℕ) + 2 ^ (x.2 : ℕ) = n} ≤ 2 := by
  classical
  let s := (univ : Finset (Fin L × Fin L)).filter
    (fun x => 2 ^ (x.1 : ℕ) + 2 ^ (x.2 : ℕ) = n)
  change s.card ≤ 2
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hsub : s ⊆ {x, (x.2, x.1)} := by
      intro y hy
      have he : 2 ^ (y.1 : ℕ) + 2 ^ (y.2 : ℕ) = 2 ^ (x.1 : ℕ) + 2 ^ (x.2 : ℕ) :=
        (mem_filter.mp hy).2.trans (mem_filter.mp hx).2.symm
      rcases two_pow_add_eq he with h | h
      · have hyx : y = x := Prod.ext (Fin.ext h.1) (Fin.ext h.2)
        simp [hyx]
      · have hyx : y = (x.2, x.1) := Prod.ext (Fin.ext h.1) (Fin.ext h.2)
        simp [hyx]
    exact (card_le_card hsub).trans (card_le_two)
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp


/-- Gallagher 1975 p.134 Lemma 5 display 4. Fiber counting form. -/
theorem equal_sum_tuple_count (k L : ℕ) :
    #{x : (Fin (k + 2) → Fin L) × (Fin (k + 2) → Fin L) |
      (∑ i, 2 ^ ((x.1 i : ℕ) + 1)) = ∑ i, 2 ^ ((x.2 i : ℕ) + 1)} ≤
      2 * L ^ (2 * k + 2) := by
  classical
  let s := (univ : Finset ((Fin (k + 2) → Fin L) × (Fin (k + 2) → Fin L))).filter
    (fun x => (∑ i, 2 ^ ((x.1 i : ℕ) + 1)) = ∑ i, 2 ^ ((x.2 i : ℕ) + 1))
  let f : ((Fin (k + 2) → Fin L) × (Fin (k + 2) → Fin L)) →
      (Fin (k + 2) → Fin L) × (Fin k → Fin L) :=
    fun x => (x.1, fun i => x.2 i.succ.succ)
  have hf : ∀ b ∈ s.image f, #{x ∈ s | f x = b} ≤ 2 := by
    intro b hb
    obtain ⟨x, hx, hxb⟩ := mem_image.mp hb
    let y : (Fin (k + 2) → Fin L) × (Fin (k + 2) → Fin L) :=
      (x.1, Fin.cons (x.2 1) (Fin.cons (x.2 0) (fun i => x.2 i.succ.succ)))
    have hsub : {z ∈ s | f z = b} ⊆ {x, y} := by
      intro z hz
      obtain ⟨hz, hzb⟩ := mem_filter.mp hz
      have hfx : f z = f x := hzb.trans hxb.symm
      have hfst : z.1 = x.1 := by simpa only [f] using congrArg Prod.fst hfx
      have htail : (fun i : Fin k => z.2 i.succ.succ) = fun i => x.2 i.succ.succ :=
        congrArg Prod.snd hfx
      have hsum : (∑ i, 2 ^ ((z.2 i : ℕ) + 1)) = ∑ i, 2 ^ ((x.2 i : ℕ) + 1) := by
        rw [← (mem_filter.mp hz).2, hfst, (mem_filter.mp hx).2]
      simp only [Fin.sum_univ_succ] at hsum
      have hrest : (∑ i : Fin k, 2 ^ ((z.2 i.succ.succ : ℕ) + 1)) =
          ∑ i : Fin k, 2 ^ ((x.2 i.succ.succ : ℕ) + 1) := by
        apply sum_congr rfl
        intro i hi
        rw [congrFun htail i]
      have hpair : 2 ^ ((z.2 0 : ℕ) + 1) + 2 ^ ((z.2 1 : ℕ) + 1) =
          2 ^ ((x.2 0 : ℕ) + 1) + 2 ^ ((x.2 1 : ℕ) + 1) := by
        change _ + (2 ^ ((z.2 1 : ℕ) + 1) + _) = _ + (2 ^ ((x.2 1 : ℕ) + 1) + _) at hsum
        omega
      rcases two_pow_add_eq hpair with hp | hp
      · have he : z = x := by
          apply Prod.ext hfst
          funext i
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) i
          · exact Fin.ext (by omega)
          · apply Fin.ext
            change (z.2 1 : ℕ) = x.2 1
            omega
          · exact congrFun htail j
        simp [he]
      · have he : z = y := by
          apply Prod.ext (y := y) (by exact hfst)
          change z.2 = Fin.cons (x.2 1) (Fin.cons (x.2 0) (fun i => x.2 i.succ.succ))
          funext i
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) i
          · exact Fin.ext (by simpa [y] using (show (z.2 0 : ℕ) = x.2 1 by omega))
          · simpa [y] using (show z.2 1 = x.2 0 from Fin.ext (by omega))
          · simpa [y] using congrFun htail j
        simp [he]
    exact (card_le_card hsub).trans card_le_two
  have h := s.card_le_mul_card_image 2 hf
  have him : (s.image f).card ≤ L ^ (2 * k + 2) := by
    calc _ ≤ Fintype.card ((Fin (k + 2) → Fin L) × (Fin k → Fin L)) := card_le_univ _
         _ = _ := by simp [Fintype.card_prod, ← pow_add]; congr 1; omega
  exact h.trans (Nat.mul_le_mul_left 2 him)


/-- Gallagher 1975 p.134 Lemma 5 display 4. Constant 2 for base 2. -/
theorem diagonal_tuple_count {k : ℕ} (hk : 2 ≤ k) (L : ℕ) :
    #{x : LeanLab.Linnik.Decomp1532a.pairs k L | LeanLab.Linnik.Decomp1532a.dif x = 0} ≤
      2 * L ^ (2 * k - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  convert equal_sum_tuple_count j L using 1
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      LeanLab.Linnik.Decomp1532a.dif, sub_eq_zero, Nat.cast_inj]
    rfl
  · congr 2


/-- Gallagher 1975 p.138 zero frequency estimate before display 5. -/
theorem major_arc_diagonal_le {k L N : ℕ} (hk : 2 ≤ k) (P : ℝ) :
    (#{x : LeanLab.Linnik.Decomp1532a.pairs k L | LeanLab.Linnik.Decomp1532a.dif x = 0} : ℝ) *
        (∫ α in majorArcs N P, ‖Sg N α‖ ^ 2) ≤
      2 * (L : ℝ) ^ (2 * k - 2) * (Nat.primeCounting N : ℝ) := by
  have hc : (#{x : LeanLab.Linnik.Decomp1532a.pairs k L | LeanLab.Linnik.Decomp1532a.dif x = 0} : ℝ) ≤
      2 * (L : ℝ) ^ (2 * k - 2) := by exact_mod_cast diagonal_tuple_count hk L
  exact mul_le_mul hc (major_arc_Sg_mean_le N P)
    (integral_nonneg fun _ => sq_nonneg _) (by positivity)


/-- Gallagher 1975 p.138 zero frequency estimate before display 5. -/
theorem major_arc_diagonal_negligible {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P : ℝ,
      (#{x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) |
        LeanLab.Linnik.Decomp1532a.dif x = 0} : ℝ) *
          (∫ α in majorArcs N P, ‖Sg N α‖ ^ 2) ≤
        δ * (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) := by
  obtain ⟨N₁, hN₁⟩ := major_arc_Sg_mean_eventually 1 (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop ((Real.log 4 + 1) / δ))
  refine ⟨max 8 (max N₁ N₂), fun N hN P => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL := LeanLab.Linnik.U7206.log_le_L hN8
  have hcoef : (Real.log 4 + 1) / Real.log N ≤ δ := by
    apply (div_le_iff₀ hl).mpr
    have h := (div_le_iff₀ hδ).mp (hN₂ N hNN₂)
    nlinarith
  have hc : (#{x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) |
      LeanLab.Linnik.Decomp1532a.dif x = 0} : ℝ) ≤
      2 * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by
    exact_mod_cast diagonal_tuple_count hk (Nat.log 2 N)
  have hd := mul_le_mul hc (hN₁ N hNN₁ P)
    (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  have hp : (Nat.log 2 N : ℝ) ^ (2 * k) =
      (Nat.log 2 N : ℝ) ^ (2 * k - 2) * (Nat.log 2 N : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hbase : 2 * (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hl), hp]
    calc _ = (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) * Real.log N ^ 2 := by ring
         _ ≤ (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) * (Nat.log 2 N : ℝ) ^ 2 :=
           mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hL 2) (by positivity)
         _ = _ := by ring
  calc _ ≤ 2 * (Nat.log 2 N : ℝ) ^ (2 * k - 2) * ((Real.log 4 + 1) * N / Real.log N) := hd
       _ = ((Real.log 4 + 1) / Real.log N) * (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by ring
       _ ≤ δ * (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) :=
         mul_le_mul_of_nonneg_right hcoef (by positivity)
       _ ≤ _ := mul_le_mul_of_nonneg_left hbase hδ.le


/-- Gallagher 1975 p.130 divisor formula before display 11. -/
theorem ramanujanSum_im_zero (q : ℕ) (n : ℤ) : (LeanLab.Linnik.Decomp1532b.ramanujanSum q n).im = 0 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [LeanLab.Linnik.Decomp1532b.ramanujanSum]
  · rw [LeanLab.Linnik.Decomp1532b.ramanujanSum_eq_divisor_sum hq n]
    simp


/-- Gallagher 1975 p.130 divisor formula before display 11. Auxiliary signed frequency identity. -/
theorem ramanujanSum_neg (q : ℕ) (n : ℤ) : LeanLab.Linnik.Decomp1532b.ramanujanSum q (-n) = LeanLab.Linnik.Decomp1532b.ramanujanSum q n := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [LeanLab.Linnik.Decomp1532b.ramanujanSum]
  · simp only [LeanLab.Linnik.Decomp1532b.ramanujanSum_eq_divisor_sum hq, Int.natAbs_neg]


/-- Gallagher 1975 pp.130 and 138. Auxiliary signed frequency identity. -/
theorem singSeries_neg (n : ℤ) : LeanLab.Linnik.Decomp1532b.singSeries (-n) = LeanLab.Linnik.Decomp1532b.singSeries n := by
  unfold LeanLab.Linnik.Decomp1532b.singSeries
  simp_rw [ramanujanSum_neg]


/-- Gallagher 1975 p.130 real divisor formula defining the singular series. -/
theorem singSeries_im_zero (n : ℤ) : (LeanLab.Linnik.Decomp1532b.singSeries n).im = 0 := by
  let f : ℕ → ℂ := fun q =>
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * LeanLab.Linnik.Decomp1532b.ramanujanSum q n
  have hf : ∀ q, (f q).im = 0 := by
    intro q
    have hr : ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 =
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    dsimp [f]
    rw [hr]
    rw [Complex.mul_im, Complex.ofReal_im, ramanujanSum_im_zero]
    ring
  have he : (∑' q, f q) = ((∑' q, (f q).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro q
    apply Complex.ext
    · simp
    · simpa using hf q
  change (∑' q, f q).im = 0
  rw [he]
  rfl


/-- Gallagher 1975 p.127 choice P equal N to theta. Auxiliary range comparison with the lab logarithmic Siegel Walfisz estimate. -/
theorem logarithmic_range_lt_power (A : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (Real.log N) ^ A < (N : ℝ) ^ θ := by
  have hr : Tendsto (fun N : ℕ => (Real.log N) ^ A / (N : ℝ) ^ θ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop A hθ).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (div_lt_one (Real.rpow_pos_of_pos hNpos θ)).mp (hN₀ N (by omega))


/-- Gallagher 1975 p.138 display 5. Auxiliary method limit from Mathlib Chebyshev lower bound. This is not a paper error. -/
theorem primeCounting_not_log_sq_bounded (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → B * N / Real.log N ^ 2 < Nat.primeCounting N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / N) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simpa [Function.comp_def, add_assoc] using h
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hr.eventually (gt_mem_nhds (show (0 : ℝ) < Real.log 2 / 2 by positivity)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop (2 * B / Real.log 2))
  refine ⟨max 2 (max N₁ N₂), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hsmall := hN₁ N (by omega)
  have hlarge := hN₂ N (by omega)
  have hhalf : Real.log ((N : ℝ) + 1) < N * (Real.log 2 / 2) :=
    by simpa [mul_comm] using (div_lt_iff₀ hn).mp hsmall
  have hcoef : B < (Real.log 2 / 2) * Real.log N := by
    have h := (div_lt_iff₀ hlog2).mp hlarge
    nlinarith
  have hpi := Chebyshev.pi_ge N
  calc
    B * N / Real.log N ^ 2 < (Real.log 2 / 2) * N / Real.log N := by
      rw [div_lt_div_iff₀ (sq_pos_of_pos hl) hl]
      nlinarith [mul_pos hn hl, mul_pos (sub_pos.mpr hcoef) (mul_pos hn hl)]
    _ ≤ ((N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1)) / Real.log N := by
      apply div_le_div_of_nonneg_right _ hl.le
      nlinarith
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using hpi




/-- Gallagher 1975 p.138 zero frequency bound before display 5. The displayed absolute constant is made explicit using Mathlib Chebyshev. -/
theorem major_arc_diagonal_order : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ k : ℕ, 2 ≤ k → ∀ P : ℝ,
      (#{x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) |
        LeanLab.Linnik.Decomp1532a.dif x = 0} : ℝ) *
          (∫ α in majorArcs N P, ‖Sg N α‖ ^ 2) ≤
        (2 * (Real.log 4 + 1) / Real.log 2) * N * (Nat.log 2 N : ℝ) ^ (2 * k - 3) := by
  obtain ⟨N₁, hN₁⟩ := major_arc_Sg_mean_eventually 1 (by norm_num)
  refine ⟨max 8 N₁, fun N hN k hk P => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb N 2
  have hc : (#{x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) |
      LeanLab.Linnik.Decomp1532a.dif x = 0} : ℝ) ≤
      2 * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by
    exact_mod_cast diagonal_tuple_count hk (Nat.log 2 N)
  have hd := mul_le_mul hc (hN₁ N (by omega) P)
    (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  have hp : (Nat.log 2 N : ℝ) ^ (2 * k - 2) =
      (Nat.log 2 N : ℝ) ^ (2 * k - 3) * (Nat.log 2 N : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  calc _ ≤ 2 * (Nat.log 2 N : ℝ) ^ (2 * k - 2) * ((Real.log 4 + 1) * N / Real.log N) := hd
       _ = (2 * (Nat.log 2 N : ℝ) ^ (2 * k - 3) * ((Real.log 4 + 1) * N / Real.log N)) *
           (Nat.log 2 N : ℝ) := by rw [hp]; ring
       _ ≤ (2 * (Nat.log 2 N : ℝ) ^ (2 * k - 3) * ((Real.log 4 + 1) * N / Real.log N)) *
           (Real.log N / Real.log 2) :=
         mul_le_mul_of_nonneg_left hL (by positivity)
       _ = _ := by field_simp


/-- Gallagher 1975 p.130 singular series and Montgomery and Vaughan 1975 p.363 display 6.16. Auxiliary definition bridge. -/
theorem singSeries_term_eq_f2 (q : ℕ) (n : ℤ) :
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * LeanLab.Linnik.Decomp1532b.ramanujanSum q n =
      (LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q : ℂ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [LeanLab.ExceptionalSet.MVMajor.f2_apply hq,
      LeanLab.Linnik.Decomp1532b.ramanujanSum_eq_divisor_sum hq n]
    unfold LeanLab.HeathBrown1985.ramanujan
    push_cast
    rw [Nat.gcd_comm]
    ring


/-- Gallagher 1975 pp.125 and 130 and Montgomery and Vaughan 1975 p.363 display 6.16. -/
theorem singSeries_eq_tsum_f2 (n : ℤ) :
    LeanLab.Linnik.Decomp1532b.singSeries n = ((∑' q : ℕ, LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q : ℝ) : ℂ) := by
  unfold LeanLab.Linnik.Decomp1532b.singSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro q
  exact singSeries_term_eq_f2 q n


/-- Gallagher 1975 p.125 singular product and p.138 use of J at n at most J at zero. Proved by the existing truncated binary series estimate ExceptionalSet.MVMajor.sing2_ge and the odd case. -/
theorem singSeries_re_nonneg {n : ℤ} (hn : n ≠ 0) : 0 ≤ (LeanLab.Linnik.Decomp1532b.singSeries n).re := by
  by_cases he : Even n
  · have hm : Even n.natAbs := Int.natAbs_even.mpr he
    have hm0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    have hsc : Summable (fun q : ℕ => (LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q : ℂ)) :=
      (LeanLab.Linnik.Decomp1532b.summable_singSeries hn).congr (fun q => singSeries_term_eq_f2 q n)
    have hsr : Summable (fun q : ℕ => LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q) := by
      simpa using Complex.reCLM.summable hsc
    have hpartial : Tendsto (fun P : ℕ => ∑ q ∈ Icc 1 P,
        LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q) atTop
        (𝓝 (∑' q : ℕ, LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q)) := by
      have ht := hsr.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      convert ht using 1
      ext P
      change _ = ∑ q ∈ range (P + 1), LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q
      have hs : range (P + 1) = insert 0 (Icc 1 P) := by
        ext q
        simp only [mem_range, mem_insert, mem_Icc]
        omega
      rw [hs, sum_insert (by simp)]
      simp
    have hlo : Tendsto (fun P : ℕ => 1 - Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G n.natAbs /
        Real.sqrt (P : ℝ)) atTop (𝓝 1) := by
      have hz : Tendsto (fun P : ℕ => Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G n.natAbs /
          Real.sqrt (P : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using tendsto_const_nhds.sub hz
    have hlower : 1 ≤ ∑' q : ℕ, LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q := by
      apply le_of_tendsto_of_tendsto hlo hpartial
      filter_upwards [eventually_ge_atTop 2] with P hP
      exact LeanLab.ExceptionalSet.MVMajor.sing2_ge hm hm0 hP
    rw [singSeries_eq_tsum_f2, Complex.ofReal_re]
    linarith
  · have ho : Odd n := Int.not_even_iff_odd.mp he
    rw [LeanLab.Linnik.Decomp1532b.singSeries_odd ho]
    simp


/-- Gallagher 1975 p.138 use of J at n at most J at zero before display 5. -/
theorem weighted_singSeries_le (k L N : ℕ) :
    (∑ x : LeanLab.Linnik.Decomp1532a.pairs k L with LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
      LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
        (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) ≤
      LeanLab.Linnik.Decomp1532b.Jn N 0 *
        (∑ x : LeanLab.Linnik.Decomp1532a.pairs k L with LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
          (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) := by
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_right (LeanLab.Linnik.Decomp1532b.Jn_le_J0 N _)
    (singSeries_re_nonneg (mem_filter.mp hx).2)


/-- ASSEMBLY. CONDITIONAL ON Decomp1532b.lemma6. Gallagher 1975 p.138 main term before display 5, using J at zero asymptotic on p.130 and Lemma 6 on p.134. -/
theorem weighted_singSeries_main_bound : ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k →
    ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
        LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
          (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) ≤
        2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 *
          (1 + K * (Real.log k ^ 2 / k)) := by
  obtain ⟨C6, h6⟩ := LeanLab.Linnik.Decomp1532b.lemma6
  refine ⟨1 + |C6|, fun k hk => ?_⟩
  let y : ℝ := Real.log k ^ 2 / k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hy : 0 < y := div_pos (sq_pos_of_pos hlogk) hkpos
  let ε : ℝ := min y 1
  have hε : 0 < ε := lt_min hy zero_lt_one
  obtain ⟨N6, hN6⟩ := h6 k hk
  obtain ⟨NJ, hNJ⟩ := eventually_atTop.mp
    (LeanLab.Linnik.Decomp1532b.J0_asymp.eventually
      (gt_mem_nhds (show (1 : ℝ) < 1 + ε by linarith)))
  refine ⟨max 8 (max N6 NJ), fun N hN => ?_⟩
  let l : ℝ := Nat.log 2 N
  let p : ℝ := l ^ (2 * k)
  let B : ℝ := (N : ℝ) / Real.log N ^ 2
  have hN8 : 8 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hB : 0 < B := div_pos hn (sq_pos_of_pos hl)
  have hJ : LeanLab.Linnik.Decomp1532b.Jn N 0 ≤ (1 + ε) * B :=
    ((div_lt_iff₀ hB).mp (hNJ N (by omega))).le
  have hcast : (2 * (Nat.log 2 N : ℂ) ^ (2 * k) : ℂ) = ((2 * p : ℝ) : ℂ) := by
    dsimp [p, l]
    push_cast
    rfl
  have hreal :
      (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
          (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) - 2 * p ≤ C6 * y * p := by
    have h := (Complex.re_le_norm
      ((∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0, LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)) -
        2 * (Nat.log 2 N : ℂ) ^ (2 * k))).trans (hN6 N (by omega))
    rw [hcast, Complex.sub_re, Complex.re_sum, Complex.ofReal_re] at h
    exact h
  have hsum0 : 0 ≤ ∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
        (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re := by
    apply sum_nonneg
    intro x hx
    exact singSeries_re_nonneg (mem_filter.mp hx).2
  have hsum : (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
        (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) ≤ (2 + |C6| * y) * p := by
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C6) hy.le) (show 0 ≤ p by dsimp [p, l]; positivity)
    nlinarith
  have he1 : ε ≤ 1 := min_le_right _ _
  have hey : ε ≤ y := min_le_left _ _
  have hprod : (1 + ε) * (2 + |C6| * y) ≤ 2 * (1 + (1 + |C6|) * y) := by
    have hmult := mul_le_mul_of_nonneg_right (show 1 + ε ≤ 2 by linarith)
      (mul_nonneg (abs_nonneg C6) hy.le)
    nlinarith
  calc _ ≤ LeanLab.Linnik.Decomp1532b.Jn N 0 * (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
            (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) := weighted_singSeries_le k _ N
       _ ≤ ((1 + ε) * B) * ((2 + |C6| * y) * p) := mul_le_mul hJ hsum hsum0 (by positivity)
       _ = (B * p) * ((1 + ε) * (2 + |C6| * y)) := by ring
       _ ≤ (B * p) * (2 * (1 + (1 + |C6|) * y)) :=
         mul_le_mul_of_nonneg_left hprod (by dsimp [B, p, l]; positivity)
       _ = _ := by dsimp [B, p, l, y]; ring

/-- Gallagher 1975 p.127, Fourier display 1 and the definition of J in Theorem 3.
Elementary support consequence. If the absolute shift exceeds N, the sum J of reciprocal log products over integer pairs in the interval from 2 to N is zero.
AI wrote the Lean code. Goldbach is open. -/
theorem Jn_eq_zero_of_large_shift (N : ℕ) (n : ℤ) (hn : (N : ℝ) < |(n : ℝ)|) :
    LeanLab.Linnik.Decomp1532b.Jn N n = 0 := by
  classical
  unfold LeanLab.Linnik.Decomp1532b.Jn
  apply sum_eq_zero
  intro m hm
  obtain ⟨hm, heq⟩ := mem_filter.mp hm
  obtain ⟨hm₁, hm₂⟩ := mem_product.mp hm
  obtain ⟨_, hm₁⟩ := mem_Ioc.mp hm₁
  obtain ⟨_, hm₂⟩ := mem_Ioc.mp hm₂
  have hni : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by omega
  have hnr : -(N : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hni
  have := abs_le.mpr hnr
  linarith

/-- Gallagher 1975 p.127, Fourier display 1 and the definition of J in Theorem 3.
Elementary support consequence. If the absolute integer shift exceeds N, the full unit interval integral of the squared prime exponential sum times the real additive character is zero.
AI wrote the Lean code. Goldbach is open. -/
theorem prime_correlation_full_zero_of_large_shift (N : ℕ) (n : ℤ)
    (hn : (N : ℝ) < |(n : ℝ)|) :
    (∫ α in Set.Icc (0 : ℝ) 1, ‖Sg N α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) = 0 := by
  let A := primesLe N
  have hA : ∀ a ∈ A, a ≤ N := by
    intro a ha
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
  change (∫ α in Set.Icc (0 : ℝ) 1,
    ‖LeanLab.Linnik.LiLiuLemma43.SA A (fun _ => 1) α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) = 0
  have he (α : ℝ) : (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re =
      Real.cos (2 * Real.pi * (n : ℝ) * α) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  simp_rw [he]
  have hnorm (α : ℝ) : ‖LeanLab.Linnik.LiLiuLemma43.SA A (fun _ => 1) α‖ ^ 2 =
      ∑ a ∈ A, ∑ b ∈ A, Real.cos (2 * Real.pi * ((a : ℝ) - b) * α) := by
    simpa only [one_mul, Complex.ofReal_one] using LeanLab.Linnik.LiLiuDisplay37.normSq_expand A (fun _ => 1) α
  simp_rw [hnorm]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp_rw [sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_eq_zero
    intro a ha
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_eq_zero
      intro b hb
      have hna : a ≤ N := hA a ha
      have hnb : b ≤ N := hA b hb
      have hnot : ∀ s : ℤ, - (N : ℤ) ≤ s → s ≤ N → s ≠ n := by
        intro s hs₁ hs₂ heq
        subst s
        have hnr : -(N : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (show -(N : ℤ) ≤ n ∧ n ≤ N from ⟨hs₁, hs₂⟩)
        linarith [abs_le.mpr hnr]
      have hplus : (a : ℤ) - b + n ≠ 0 := by
        intro hz
        exact hnot ((b : ℤ) - a) (by omega) (by omega) (by omega)
      have hminus : (a : ℤ) - b - n ≠ 0 := by
        intro hz
        exact hnot ((a : ℤ) - b) (by omega) (by omega) (by omega)
      have heq : (fun α : ℝ => Real.cos (2 * Real.pi * ((a : ℝ) - b) * α) *
          Real.cos (2 * Real.pi * (n : ℝ) * α)) =
        (fun α => (Real.cos (2 * Real.pi * (((a : ℤ) - b + n : ℤ) : ℝ) * α) +
          Real.cos (2 * Real.pi * (((a : ℤ) - b - n : ℤ) : ℝ) * α)) / 2) := by
        funext α
        push_cast
        rw [show 2 * Real.pi * ((a : ℝ) - b + n) * α =
            2 * Real.pi * ((a : ℝ) - b) * α + 2 * Real.pi * n * α by ring,
          show 2 * Real.pi * ((a : ℝ) - b - n) * α =
            2 * Real.pi * ((a : ℝ) - b) * α - 2 * Real.pi * n * α by ring,
          Real.cos_add, Real.cos_sub]
        ring
      rw [heq, intervalIntegral.integral_div,
        intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
        LeanLab.Linnik.U1426ChainWire.integral_cos_int, LeanLab.Linnik.U1426ChainWire.integral_cos_int, if_neg hplus, if_neg hminus]
      norm_num
    · intro b hb
      exact (by fun_prop : Continuous (fun α : ℝ =>
        Real.cos (2 * Real.pi * ((a : ℝ) - b) * α) * Real.cos (2 * Real.pi * n * α))).intervalIntegrable _ _
  · intro a ha
    apply Continuous.intervalIntegrable
    fun_prop

/-- Gallagher 1975 p.127, Fourier display 1 and the definition of J in Theorem 3.
Elementary support consequence. If the absolute integer shift exceeds N, its major arc correlation equals the negative correlation over the complement of those arcs in the unit interval.
AI wrote the Lean code. Goldbach is open. -/
theorem major_correlation_eq_neg_minor_of_large_shift (N : ℕ) (P : ℝ) (n : ℤ)
    (hn : (N : ℝ) < |(n : ℝ)|) :
    (∫ α in majorArcs N P, ‖Sg N α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) =
      -(∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N P, ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) := by
  let f : ℝ → ℝ := fun α => ‖Sg N α‖ ^ 2 *
    (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re
  have he : Continuous (fun α : ℝ =>
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hf : Continuous f := ((LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2).mul he
  have hi : IntegrableOn f (Set.Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have hsplit := integral_inter_add_sdiff (measurableSet_majorArcs N P) hi
  rw [Set.inter_eq_right.mpr (show majorArcs N P ⊆ Set.Icc (0 : ℝ) 1 from fun _ h => h.1)] at hsplit
  have hzero : (∫ α in Set.Icc (0 : ℝ) 1, f α) = 0 :=
    prime_correlation_full_zero_of_large_shift N n hn
  rw [hzero] at hsplit
  change (∫ α in majorArcs N P, f α) = -(∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N P, f α)
  linarith

/-- Gallagher 1975 p.127 display 1. The prime difference representation count equals
its complex Fourier integral over the full unit interval. Ordered pairs are counted.
AI wrote the Lean code. Goldbach is open. -/
theorem prime_pair_fourier_identity (N : ℕ) (n : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1, ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) =
      ((#{x ∈ primesLe N ×ˢ primesLe N | (x.1 : ℤ) - x.2 = n} : ℕ) : ℂ) := by
  classical
  let A := primesLe N
  have he (x : ℝ) : LeanLab.PNTPort.LargeSieve.e x = LeanLab.CircleOrth.ee x := by
    exact LeanLab.Linnik.U1434Lemma21.e_eq_eC x
  have hnorm (α : ℝ) : ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) =
      Sg N α * (starRingEnd ℂ) (Sg N α) := by
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hexp (α : ℝ) : ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α) =
      ∑ p ∈ A, ∑ q ∈ A,
        LeanLab.PNTPort.LargeSieve.e ((((p : ℤ) - q + n : ℤ) : ℝ) * α) := by
    rw [hnorm]
    simp only [Sg, LeanLab.Linnik.LiLiuLemma43.SA, one_mul, map_sum]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro q hq
    rw [← LeanLab.PNTPort.LargeSieve.e_neg,
      ← LeanLab.PNTPort.LargeSieve.e_add, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    push_cast
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp_rw [hexp, he]
  rw [intervalIntegral.integral_finsetSum]
  · have hsum : (∑ p ∈ A, ∑ q ∈ A,
        if (p : ℤ) - q + n = 0 then (1 : ℂ) else 0) =
        ∑ p ∈ A, ∑ q ∈ A, if (p : ℤ) - q = n then (1 : ℂ) else 0 := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro q hq
      have hh : ((q : ℤ) - p + n = 0) ↔ ((p : ℤ) - q = n) := by omega
      simp only [hh]
    have hinner : ∀ p ∈ A, (∫ α in (0 : ℝ)..1, ∑ q ∈ A,
        LeanLab.CircleOrth.ee ((((p : ℤ) - q + n : ℤ) : ℝ) * α)) =
        ∑ q ∈ A, if (p : ℤ) - q + n = 0 then (1 : ℂ) else 0 := by
      intro p hp
      rw [intervalIntegral.integral_finsetSum]
      · exact sum_congr rfl (fun q _ => LeanLab.CircleOrth.integral_ee_int _)
      · intro q hq
        exact (LeanLab.CircleOrth.continuous_ee.comp
          (continuous_const.mul continuous_id)).intervalIntegrable _ _
    rw [sum_congr rfl hinner]
    rw [hsum]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_product, A]
  · intro p hp
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun q _ => LeanLab.CircleOrth.continuous_ee.comp
      (continuous_const.mul continuous_id))

/-- The plain form of the nonzero correlation error before Gallagher 1975 p.138 display (5): the
same averaged error as `major_arc_remainder_bound`, with no `e^{-c/θ}` term. For each fixed
`θ ≤ θ₀`, `k ≥ 2` and `δ > 0` the error is at most `δ` times the main size for large `N`.
The average over the tuple differences is essential. The frequency by frequency form is not
what is claimed: in Theorem 3 p.127 the quoted exceptional term is of size about `1` when the
exceptional conductor divides `n`. -/
def Display5PlainExpansion : Prop :=
  ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * δ

/-- PROVED reduction, reproducing the worker result of 20261103T0714Z: the plain form implies
`major_arc_remainder_bound`, with `c = 1` and `C = 0`. This is one way only. The plain form is
STRONGER than Gallagher's Theorem 3 p.127 and display (5) p.138, both of which keep `e^{-c/θ}`,
so this reduction does not remove the density input. Unused by the assembly since U-1625. -/
theorem major_arc_remainder_bound_of_plain (h : Display5PlainExpansion) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
            (C * Real.exp (-c / θ) + δ) := by
  obtain ⟨θ₀, hθ₀, h⟩ := h
  refine ⟨1, 0, θ₀, one_pos, hθ₀, fun θ hθ hθ₀' k hk δ hδ => ?_⟩
  simpa using h θ hθ hθ₀' k hk δ hδ

/- RETIRED 2026-11-06 architect 20261106T0803Z-25677 U-1625, kept as text.
`theorem display5_plain_expansion : Display5PlainExpansion`, OPEN LEAF of U-1610. Gallagher prints no
such statement: his error keeps `e^{-c/θ}` at every frequency, Theorem 3 p.127, and in display 5
p.138. It is not refuted. `major_arc_remainder_bound` does not need it, so the leaf is dropped. -/

/-- ASSEMBLY. CONDITIONAL ON the four Decomp486 analytic cases through Theorem 3.
Gallagher 1975 P0094 p.138, the sum over nonzero `n` before display 5.
Theorem 3 p.127 bounds each frequency by `O(N L⁻² n/φ(n) (τ(n) log P/P + e^{-c/θ} + E(n)))`,
with `E(n) = r φ((n,r))/φ²(r)` present only for an exceptional conductor `r ≤ P`, relative to
`T = P⁵`. Lemma 8 p.136 gives `∑ r_{k,k}(n) n/φ(n) ≪ L^{2k}`, and Lemma 10 p.136 gives the average
of `E` at most `L^{2k}/(log r)^{1/3}`, which is below `δ L^{2k}` for large `N` since
`log r ≫ log log N` p.127. The term `τ(n) log P/P` is below `(kN)^ε log P/P`, which tends to zero
for `ε < θ`. That is this statement, with `C e^{-c/θ}` kept and `δ` free.
DECISION 2026-11-06 architect 20261106T0803Z-25677 U-1625: this statement is unchanged and is a
leaf again, replacing `display5_plain_expansion`, the form with `C = 0`, which is stronger than
the printed source and which no written proof supplies; compare task262 routes one to three.
Twin: for theta small, k at least 2, delta positive and large N, the nonzero correlation error is
at most the main size times C exp of minus c over theta plus delta.
Instance: `Audit1625.major_arc_remainder_instance`.
External inputs of Theorem 3 include Gallagher 1970 Inventiones 11 pp.329 to 339 and Montgomery
and Vaughan 1975 Acta Arithmetica 27 pp.353 to 370. Lemma 6 is not part of this input. -/
theorem major_arc_remainder_bound : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
            (C * Real.exp (-c / θ) + δ) := by
  exact LeanLab.Linnik.Decomp466c.major_arc_remainder_bound_split

/-- ASSEMBLY. CONDITIONAL ON weighted_singSeries_main_bound and major_arc_remainder_bound. Gallagher 1975 p.138 nonzero contribution before display 5. -/
theorem major_arc_nonzero_bound : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
        LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖Sg N α‖ ^ 2 *
            (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) ≤
        2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 *
          (1 + C * (Real.log k ^ 2 / k + Real.exp (-c / θ))) := by
  obtain ⟨K, hmain⟩ := weighted_singSeries_main_bound
  obtain ⟨c, C, θ₀, hc, hθ₀, herror⟩ := major_arc_remainder_bound
  refine ⟨c, |K| + |C| + 1, θ₀, hc, hθ₀, fun θ hθ hθmax k hk => ?_⟩
  let y : ℝ := Real.log k ^ 2 / k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hy : 0 < y := div_pos (sq_pos_of_pos hlogk) hkpos
  obtain ⟨N₁, hN₁⟩ := hmain k hk
  obtain ⟨N₂, hN₂⟩ := herror θ hθ hθmax k hk y hy
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  let S : ℝ := ∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
    LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let W : ℝ := ∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
    LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
      LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
        (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hm : W ≤ M * (1 + K * y) := hN₁ N (by omega)
  have he : |S - W| ≤ M * (C * Real.exp (-c / θ) + y) := hN₂ N (by omega)
  have hupper : S ≤ W + M * (C * Real.exp (-c / θ) + y) := by
    have h := (le_abs_self (S - W)).trans he
    linarith
  have hcoef : (K + 1) * y + C * Real.exp (-c / θ) ≤
      (|K| + |C| + 1) * (y + Real.exp (-c / θ)) := by
    have hky := mul_le_mul_of_nonneg_right (le_abs_self K) hy.le
    have hce := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos (-c / θ)).le
    have hcy : 0 ≤ |C| * y := by positivity
    have hke : 0 ≤ (|K| + 1) * Real.exp (-c / θ) := by positivity
    nlinarith
  change S ≤ M * (1 + (|K| + |C| + 1) * (y + Real.exp (-c / θ)))
  calc S ≤ W + M * (C * Real.exp (-c / θ) + y) := hupper
       _ ≤ M * (1 + K * y) + M * (C * Real.exp (-c / θ) + y) := add_le_add hm le_rfl
       _ = M * (1 + ((K + 1) * y + C * Real.exp (-c / θ))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hcoef) hM

/-- LEAF. Unit U-1532. Display (5), p. 138, for g = 2 where `D/φ(D) = 2`: there are `c > 0`,
`C` and `θ₀ > 0` such that for `0 < θ ≤ θ₀`, `k ≥ 2` and `N ≥ N_{k,θ}`, with `P = N^θ`,
`∫_𝔐 |S G^k|² ≤ 2 N L^{2k}/log² N · (1 + C(log² k / k + e^{-c/θ}))`. It follows from
Theorem 3, p. 127, and Lemmas 5, 6, 8 and 10. -/
theorem major_arc_bound : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      ∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 *
          (1 + C * (Real.log k ^ 2 / k + Real.exp (-c / θ))) := by
  -- LEAF. External analytic sources: Gallagher 1970 Inventiones 11 pp.329 to 339;
  -- Montgomery and Vaughan 1975 Acta Arith.27 pp.353 to 370. See Gallagher 1975 p.138 display 5.
  obtain ⟨c, C, θ₀, hc, hθ₀, hnonzero⟩ := major_arc_nonzero_bound
  refine ⟨c, |C| + 1, θ₀, hc, hθ₀, fun θ hθ hθmax k hk => ?_⟩
  let y : ℝ := Real.log k ^ 2 / k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hy : 0 < y := div_pos (sq_pos_of_pos hlogk) hkpos
  obtain ⟨Nd, hd⟩ := major_arc_diagonal_negligible hk hy
  obtain ⟨Nk, hNk⟩ := hnonzero θ hθ hθmax k hk
  refine ⟨max Nd Nk, fun N hN => ?_⟩
  have hD := hd N (by omega) ((N : ℝ) ^ θ)
  have hS := hNk N (by omega)
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have he : 0 ≤ y + Real.exp (-c / θ) := by positivity
  have hC : C * (y + Real.exp (-c / θ)) + y ≤
      (|C| + 1) * (y + Real.exp (-c / θ)) := by
    calc _ ≤ |C| * (y + Real.exp (-c / θ)) + (y + Real.exp (-c / θ)) :=
           add_le_add (mul_le_mul_of_nonneg_right (le_abs_self C) he)
             (le_add_of_nonneg_right (Real.exp_pos _).le)
         _ = _ := by ring
  rw [major_arc_diagonal_split]
  calc _ ≤ y * M + M * (1 + C * (y + Real.exp (-c / θ))) := add_le_add hD hS
       _ = M * (1 + (C * (y + Real.exp (-c / θ)) + y)) := by ring
       _ ≤ M * (1 + (|C| + 1) * (y + Real.exp (-c / θ))) :=
         mul_le_mul_of_nonneg_left (add_le_add le_rfl hC) hM

/-- LEAF. Unit U-1532. Lemma 11, display (1) p. 137, Vinogradov and Montgomery: there are `C`,
`θ₀ > 0` and `E` such that for `0 < θ ≤ θ₀`, `N ≥ 2`, `P = N^θ` and `α ∈ [0, 1]` off the major
arcs, `|S(α)| ≤ C N P^{-1/2} L^E`. -/
theorem lemma11 : ∃ C θ₀ : ℝ, ∃ E : ℕ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    ∀ N : ℕ, 2 ≤ N → ∀ α ∈ Set.Icc (0 : ℝ) 1, α ∉ majorArcs N ((N : ℝ) ^ θ) →
      ‖Sg N α‖ ≤ C * N * (Nat.log 2 N : ℝ) ^ E / (N : ℝ) ^ (θ / 2) := by
  classical
  obtain ⟨Cψ, hCψ⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D : ℝ := 900 + (Real.log 4 + 4) + |Cψ|
  let C : ℝ := 16 * D / Real.log 2 + 16
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 16 ≤ C := by
    have : 0 ≤ 16 * D / Real.log 2 := by positivity
    dsimp [C]
    linarith
  refine ⟨C, 2 / 5, 4, by norm_num, fun θ hθ hθmax N hN α hα hM => ?_⟩
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have ht : 0 < (N : ℝ) ^ (θ / 2) := Real.rpow_pos_of_pos hn0 _
  have hL1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have hLr : (1 : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hL1
  have hp0 : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hn0 _
  have hpN : (N : ℝ) ^ θ ≤ N := by
    calc _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
         _ = _ := Real.rpow_one _
  by_cases hN8 : 8 ≤ N
  · obtain ⟨q, a, hq, hqmax, haq, hcop, happ⟩ :=
      LeanLab.Linnik.Decomp1532b.minor_approx hp0 hpN hα hM
    have hq0 : (0 : ℝ) < q := hp0.trans hq
    have happ' : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
      apply happ.trans
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < q * N) (by positivity : 0 < (q : ℝ) ^ 2)]
      have hqp : (q : ℝ) * (N : ℝ) ^ θ ≤ N := (le_div_iff₀ hp0).mp hqmax
      nlinarith
    have hv := vonMangoldt_prefix_bound hN hθ hθmax hq hqmax (a := (a : ℤ)) hcop.isCoprime
      (by simpa using happ')
    let f (n : ℕ) : ℂ := if n.Prime then (Real.log n : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * α) else 0
    have hB : ∀ m ∈ Icc 2 N, ‖∑ n ∈ Icc 2 m, f n‖ ≤
        D * N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 := by
      intro m hm
      have hmN : (m : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hm).2
      have hsub : Icc 2 m ⊆ Icc 1 m := by intro n hn; simp only [mem_Icc] at *; omega
      have hf1 : ∑ n ∈ Icc 2 m, f n = ∑ n ∈ Icc 1 m, f n := by
        apply sum_subset hsub
        intro n hn hn'
        have : n = 1 := by simp only [mem_Icc] at *; omega
        subst n
        simp [f]
      have hgap : ‖(∑ n ∈ Icc 2 m, f n) - LeanLab.PNTPort.Vinogradov.S m α‖ ≤
          Chebyshev.psi m - Chebyshev.theta m := by
        rw [hf1]
        unfold LeanLab.PNTPort.Vinogradov.S Chebyshev.psi Chebyshev.theta
        rw [Nat.floor_natCast, sum_filter, ← sum_sub_distrib, ← sum_sub_distrib]
        refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
        by_cases hp : n.Prime
        · simp [f, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
        · simp only [f, hp, if_false, zero_sub, norm_neg, sub_zero]
          rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hsqrt : Real.sqrt m ≤ N / (N : ℝ) ^ (θ / 2) := by
        calc _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hmN
             _ = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
             _ ≤ (N : ℝ) ^ (1 - θ / 2) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
             _ = _ := by rw [Real.rpow_sub hn0, Real.rpow_one]
      have hg : ‖(∑ n ∈ Icc 2 m, f n) - LeanLab.PNTPort.Vinogradov.S m α‖ ≤
          |Cψ| * (N / (N : ℝ) ^ (θ / 2)) * (1 + Real.log N) ^ 4 := by
        calc _ ≤ Cψ * Real.sqrt m := hgap.trans (hCψ m)
             _ ≤ |Cψ| * Real.sqrt m := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
             _ ≤ |Cψ| * (N / (N : ℝ) ^ (θ / 2)) := mul_le_mul_of_nonneg_left hsqrt (abs_nonneg _)
             _ ≤ _ := le_mul_of_one_le_right (by positivity)
               (one_le_pow₀ (by linarith [Real.log_natCast_nonneg N]))
      calc _ ≤ ‖LeanLab.PNTPort.Vinogradov.S m α‖ +
          ‖(∑ n ∈ Icc 2 m, f n) - LeanLab.PNTPort.Vinogradov.S m α‖ := by
            simpa only [add_sub_cancel] using norm_add_le (LeanLab.PNTPort.Vinogradov.S m α)
              ((∑ n ∈ Icc 2 m, f n) - LeanLab.PNTPort.Vinogradov.S m α)
        _ ≤ (900 + (Real.log 4 + 4)) * N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 +
            |Cψ| * (N / (N : ℝ) ^ (θ / 2)) * (1 + Real.log N) ^ 4 :=
              add_le_add (hv m (mem_Icc.mp hm).2) hg
        _ = _ := by dsimp [D]; ring
    have hprimes : primesLe N = (Icc 2 N).filter Nat.Prime := by
      ext n
      simp only [primesLe, mem_filter, mem_range, mem_Icc]
      constructor <;> intro h
      · exact ⟨⟨h.2.two_le, by omega⟩, h.2⟩
      · exact ⟨by omega, h.2⟩
    have hSg : Sg N α = ∑ n ∈ Icc 2 N, f n / (Real.log n : ℂ) := by
      unfold Sg LeanLab.Linnik.LiLiuLemma43.SA
      rw [hprimes, sum_filter]
      apply sum_congr rfl
      intro n hn
      by_cases hp : n.Prime
      · have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        have hlc : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hl
        dsimp [f]
        rw [if_pos hp]
        simp only [one_mul]
        field_simp <;> simp [hp]
      · simp [f, hp]
    have hub := norm_sum_div_log_le hN f _ hB
    rw [← hSg] at hub
    have hlN := LeanLab.Linnik.U7206.log_le_L hN8
    have hlog2 : 0 < Real.log 2 := by positivity
    calc _ ≤ D * N / (N : ℝ) ^ (θ / 2) * (1 + Real.log N) ^ 4 / Real.log 2 := hub
         _ ≤ D * N / (N : ℝ) ^ (θ / 2) * (2 * (Nat.log 2 N : ℝ)) ^ 4 / Real.log 2 := by gcongr; linarith
         _ = (16 * D / Real.log 2) * N * (Nat.log 2 N : ℝ) ^ 4 / (N : ℝ) ^ (θ / 2) := by ring
         _ ≤ _ := by dsimp [C]; gcongr; linarith
  · have htriv : ‖Sg N α‖ ≤ (N : ℝ) + 1 := by
      unfold Sg LeanLab.Linnik.LiLiuLemma43.SA
      calc _ ≤ ∑ p ∈ primesLe N, ‖LeanLab.PNTPort.LargeSieve.e (p * α)‖ := by simpa using norm_sum_le (primesLe N) (fun p => (1 : ℂ) * LeanLab.PNTPort.LargeSieve.e (p * α))
           _ = (primesLe N).card := by simp [LeanLab.PNTPort.LargeSieve.norm_e]
           _ ≤ N + 1 := by
             have hh : (primesLe N).card ≤ N + 1 := by
               simpa [primesLe] using card_le_card (filter_subset (fun p => p.Prime) (range (N + 1)))
             exact_mod_cast hh
    have htN : (N : ℝ) ^ (θ / 2) ≤ N := by
      calc _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
           _ = _ := Real.rpow_one _
    have hNr : (N : ℝ) ≤ 7 := by exact_mod_cast (show N ≤ 7 by omega)
    apply htriv.trans
    rw [le_div_iff₀ ht]
    have hLp : 1 ≤ (Nat.log 2 N : ℝ) ^ 4 := one_le_pow₀ hLr
    calc ((N : ℝ) + 1) * (N : ℝ) ^ (θ / 2) ≤ 14 * N := by nlinarith
         _ ≤ C * N := mul_le_mul_of_nonneg_right (by linarith) hn0.le
         _ ≤ _ := le_mul_of_one_le_right (by positivity) hLp


/-- LEAF. Unit U-1532. `θ = 2(4/log 2) η log(e/η)` with `η = (log k)/k` is positive and tends
to 0, so `θ ≤ θ₀` for large `k`, p. 139. -/
theorem thetaK_small (θ₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < thetaK k ∧ thetaK k ≤ θ₀ := by
  apply Filter.eventually_atTop.mp
  filter_upwards [thetaK_mul_log_tendsto_zero.eventually (gt_mem_nhds hθ₀), eventually_ge_atTop 3] with k hb hk
  have hpos := (thetaK_bounds k hk).1
  refine ⟨hpos, le_trans ?_ hb.le⟩
  have hl : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Real.exp_one_lt_d9]
  nlinarith


/-- LEAF. Unit U-1532. With this `θ`, `θ ≍ log² k / k`, so `e^{-c/θ} ≤ log²(2k)/k` for large
`k`, which absorbs the term `e^{-c/θ}` of display (5) into display (6), p. 139. -/
theorem exp_neg_le (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Real.exp (-c / thetaK k) ≤ Real.log (2 * k) ^ 2 / k := by
  apply Filter.eventually_atTop.mp
  filter_upwards [thetaK_mul_log_tendsto_zero.eventually (gt_mem_nhds hc), eventually_ge_atTop 3] with k hb hk
  have hpos := (thetaK_bounds k hk).1
  have hk0 : (0 : ℝ) < k := by positivity
  have hl : 1 ≤ Real.log (2 * k) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Real.exp_one_lt_d9]
  calc _ ≤ Real.exp (-Real.log k) := by
         apply Real.exp_le_exp.mpr
         rw [div_le_iff₀ hpos]
         nlinarith
       _ = 1 / (k : ℝ) := by rw [Real.exp_neg, Real.exp_log hk0]; simp
       _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hk0.le


/-- LEAF. Unit U-1532. `0 < η = (log k)/k ≤ 1/16` for large `k`, the range where Lemma 2 of
p. 132 applies, p. 139. -/
theorem etaK_small : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < etaK k ∧ etaK k ≤ 1 / 16 := by
  have hlim : Tendsto (fun k : ℕ => Real.log k / k) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1 / 16 by norm_num))
  have hp : ∀ᶠ k : ℕ in atTop, 0 < Real.log k / k := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact div_pos (Real.log_pos (by exact_mod_cast hk)) (by positivity)
  change ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < Real.log k / k ∧ Real.log k / k ≤ 1 / 16
  exact (hp.and (hsmall.mono fun _ h => h.le)).exists_forall_of_atTop


/-- LEAF. Unit U-1532. Any fixed power of `L = [log₂ N]` is beaten by any fixed power of `N`:
`A L^E ≤ N^ε` for large `N`; the last step `= o_η(N L^{2k-2})` of p. 139, line 3. -/
theorem power_le (A : ℝ) (E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → A * (Nat.log 2 N : ℝ) ^ E ≤ (N : ℝ) ^ ε := by
  have h := (isLittleO_log_rpow_rpow_atTop (E : ℝ) hε).const_mul_left
    (|A| / Real.log 2 ^ E)
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (h.bound (show (0 : ℝ) < 1 by norm_num))
  apply Filter.eventually_atTop.mp
  filter_upwards [he] with N hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hNat := Real.natLog_le_logb N 2
  rw [Real.logb] at hNat
  norm_num only [Nat.cast_ofNat] at hNat
  simp only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (|A| / Real.log 2 ^ E) * Real.log (N : ℝ) ^ E),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) ε), one_mul] at hN
  calc A * (Nat.log 2 N : ℝ) ^ E
      ≤ |A| * (Nat.log 2 N : ℝ) ^ E := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |A| * (Real.log (N : ℝ) / Real.log 2) ^ E := by gcongr
    _ = (|A| / Real.log 2 ^ E) * Real.log (N : ℝ) ^ E := by ring
    _ ≤ _ := hN


/-- PROVED. The three way split of p. 138 for a continuous integrand. -/
theorem split3 (f : ℝ → ℝ) (hf : Continuous f) {M E : Set ℝ} (hM : MeasurableSet M)
    (hMs : M ⊆ Set.Icc 0 1) (hE : MeasurableSet E) :
    ∫ α in Set.Icc (0 : ℝ) 1, f α = (∫ α in M, f α) + (∫ α in (Set.Icc 0 1 \ M) ∩ E, f α) +
      ∫ α in (Set.Icc 0 1 \ M) \ E, f α := by
  have hI : IntegrableOn f (Set.Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have h1 := integral_inter_add_sdiff hM hI
  have h2 := integral_inter_add_sdiff (s := Set.Icc (0 : ℝ) 1 \ M) hE
    (hI.mono_set Set.diff_subset)
  rw [Set.inter_eq_right.mpr hMs] at h1
  linarith

/-- PROVED. On a set of finite measure at most `V` where `|S| ≤ B`,
`∫ |S G^k|² ≤ B² L^{2k} V`, using `|G| ≤ L`. -/
theorem sup_piece {k N : ℕ} {S : Set ℝ} {B V : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ S, ‖Sg N α‖ ≤ B) (hV0 : 0 ≤ V) (hV : volume S ≤ ENNReal.ofReal V) :
    ∫ α in S, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) * V := by
  have hfin : volume S < ⊤ := lt_of_le_of_lt hV ENNReal.ofReal_lt_top
  have hbound : ∀ α ∈ S, ‖‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2‖ ≤
      B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) := by
    intro α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_pow]
    have hG := LeanLab.Linnik.U7206.norm_Gs_le (Nat.log 2 N) α
    rw [show B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) = (B * (Nat.log 2 N : ℝ) ^ k) ^ 2 by ring]
    gcongr
    exact hB α hα
  have h1 := norm_setIntegral_le_of_norm_le_const hfin hbound
  have hreal : volume.real S ≤ V := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  calc ∫ α in S, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2
      ≤ ‖∫ α in S, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) * volume.real S := h1
    _ ≤ B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) * V := mul_le_mul_of_nonneg_left hreal (by positivity)

/-- PROVED. The algebra of the `C(𝔐) ∩ ℰ` piece, p. 139, line 3. -/
theorem alg_piece2 {C l n x k : ℝ} {E j : ℕ} (hx : 0 < x) (hn : 0 < n) (hk : 0 < k) (hl : 0 ≤ l)
    (hA : 4 * C ^ 2 * k * l ^ (2 * E + 2) ≤ x) :
    (|C| * n * l ^ E / x) ^ 2 * (l ^ j * l ^ 2) * (4 * (x / n)) ≤ n * l ^ j / k := by
  have hid : (|C| * n * l ^ E / x) ^ 2 * (l ^ j * l ^ 2) * (4 * (x / n)) =
      (4 * C ^ 2 * k * l ^ (2 * E + 2)) * (n * l ^ j / k) / x := by
    rw [div_pow, mul_pow, mul_pow, sq_abs]
    field_simp
    ring
  rw [hid]
  have h0 : 0 ≤ n * l ^ j / k := by positivity
  calc (4 * C ^ 2 * k * l ^ (2 * E + 2)) * (n * l ^ j / k) / x
      ≤ x * (n * l ^ j / k) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA h0) hx.le
    _ = n * l ^ j / k := by field_simp

/-- PROVED. The final bookkeeping of p. 139: the three pieces add up to display (6). -/
theorem alg_final {I1 I2 I3 main W y C5 R e2 : ℝ} (hI1 : I1 ≤ main * (1 + 2 * |C5| * y))
    (hI2 : I2 ≤ y * W) (hI3 : I3 ≤ R * e2 * y * W) (hW : W ≤ main / 2) (hy : 0 ≤ y)
    (hR : 0 ≤ R) (he : 0 ≤ e2) (hmain : 0 ≤ main) :
    I1 + I2 + I3 ≤ main * (1 + (2 * |C5| + 1 + R * e2) * y) := by
  have h1 : 0 ≤ (1 + R * e2) * y := by positivity
  have h2 := mul_le_mul_of_nonneg_left hW h1
  have h3 : 0 ≤ (1 + R * e2) * y * main := by positivity
  nlinarith

/-- PROVED. Piece `C(𝔐) ∩ ℰ` of p. 139 from Lemma 11, the lab's Lemma 2, and `A L^{2E+2} ≤ P^{1/2}`:
`∫ ≤ N L^{2k-2}/k`. -/
theorem piece2 {k N : ℕ} (hk : 3 ≤ k) (hN8 : 8 ≤ N) {C11 : ℝ} {E : ℕ}
    (hη0 : 0 < etaK k) (hη : etaK k ≤ 1 / 16)
    (h11 : ∀ α ∈ Set.Icc (0 : ℝ) 1, α ∉ majorArcs N ((N : ℝ) ^ thetaK k) →
      ‖Sg N α‖ ≤ C11 * N * (Nat.log 2 N : ℝ) ^ E / (N : ℝ) ^ (thetaK k / 2))
    (hA : 4 * C11 ^ 2 * k * (Nat.log 2 N : ℝ) ^ (2 * E + 2) ≤ (N : ℝ) ^ (thetaK k / 2)) :
    ∫ α in (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
        {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) / k := by
  have hN2 : 2 ≤ N := by omega
  have hL3 : 3 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hLr3 : (3 : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hL3
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : 0 < (N : ℝ) ^ (thetaK k / 2) := Real.rpow_pos_of_pos hNr _
  have hB : ∀ α ∈ (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α‖ ≤ |C11| * N * (Nat.log 2 N : ℝ) ^ E / (N : ℝ) ^ (thetaK k / 2) := by
    intro α hα
    refine (h11 α hα.1.1 hα.1.2).trans ?_
    apply div_le_div_of_nonneg_right _ hx.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hNr.le
  have hη4 : etaK k ≤ 1 / 4 := by linarith
  have hηa : 0 < 4 * etaK k * ((Nat.log 2 N : ℕ) : ℝ) := by positivity
  have hηb : 4 * etaK k * ((Nat.log 2 N : ℕ) : ℝ) ≤ ((Nat.log 2 N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    nlinarith
  have hL2 := LeanLab.Linnik.Gallagher1975Lemma1.lemma2 N hN2 (etaK k) hηa hηb hη4
  have hsub : (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} ⊆
      LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k) ∪ {1} := by
    intro α hα
    have hI : α ∈ Set.Icc (0 : ℝ) 1 := hα.1.1
    have hE : (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖ := hα.2
    rcases eq_or_lt_of_le hI.2 with h1 | h1
    · right; exact h1
    · left
      refine ⟨⟨hI.1, h1⟩, ?_⟩
      rw [G_eq_Gs]
      exact hE
  have hV : volume ((Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖}) ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ (epsK k - 1)) := by
    calc _ ≤ volume (LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k) ∪ {1}) :=
          measure_mono hsub
      _ ≤ volume (LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k)) +
            volume ({1} : Set ℝ) := measure_union_le _ _
      _ = volume (LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k)) := by
          rw [Real.volume_singleton, add_zero]
      _ ≤ ENNReal.ofReal (4 * (N : ℝ) ^ (epsK k - 1)) := hL2
  have h := sup_piece (k := k) (by positivity) hB (by positivity) hV
  have hθx : epsK k = thetaK k / 2 := by rw [thetaK]; ring
  have hVx : (N : ℝ) ^ (epsK k - 1) = (N : ℝ) ^ (thetaK k / 2) / N := by
    rw [hθx, Real.rpow_sub_one hNr.ne']
  have hpow : (Nat.log 2 N : ℝ) ^ (2 * k) =
      (Nat.log 2 N : ℝ) ^ (2 * k - 2) * (Nat.log 2 N : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [hVx, hpow] at h
  exact h.trans (alg_piece2 hx hNr hk0 (Nat.cast_nonneg _) hA)

/-- PROVED. Piece `C(𝔐) ∩ C(ℰ)` of p. 139 from the lab's proved Lemma 12 arc bound:
`∫ ≤ R e² y N L^{2k-2}` with `y = log²(2k)/k`, `R = 8(9 + 2R₁)`. -/
theorem piece3 {k N : ℕ} (hk : 3 ≤ k) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in (Set.Icc 0 1 \ M) \
        {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        8 * (9 + 2 * LeanLab.Romanov.R₁) * Real.exp 2 * (Real.log (2 * k) ^ 2 / k) *
          ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hEm : MeasurableSet {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} :=
    measurableSet_le measurable_const (continuous_Gs _).norm.measurable
  have hA : MeasurableSet ((Set.Icc (0 : ℝ) 1 \ M) \
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖}) :=
    (measurableSet_Icc.diff hM).diff hEm
  have hAs : (Set.Icc (0 : ℝ) 1 \ M) \
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} ⊆ Set.Icc 0 1 :=
    fun α h => h.1.1
  have hGb : ∀ α ∈ (Set.Icc (0 : ℝ) 1 \ M) \
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Gs (Nat.log 2 N) α‖ ≤ (1 - Real.log k / k) * (Nat.log 2 N : ℝ) := by
    intro α hα
    have h : ¬ ((1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖) := hα.2
    rw [not_le] at h
    exact h.le
  have h := LeanLab.Romanov.gallagher_eta_arc_le (by omega : 2 ≤ k) N hA hAs hGb
  have hR := LeanLab.Romanov.R₁_pos
  have hlog2k : 1 ≤ Real.log (2 * k) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hy1 : 1 / (k : ℝ) ≤ Real.log (2 * k) ^ 2 / k :=
    div_le_div_of_nonneg_right (by nlinarith) hk0.le
  have hk2 : Real.exp 2 / (k : ℝ) ^ 2 ≤ Real.exp 2 * (Real.log (2 * k) ^ 2 / k) := by
    have h1 : Real.exp 2 / (k : ℝ) ^ 2 ≤ Real.exp 2 * (1 / k) := by
      rw [div_le_iff₀ (by positivity)]
      have : Real.exp 2 * (1 / k) * (k : ℝ) ^ 2 = Real.exp 2 * k := by field_simp
      rw [this]
      nlinarith [Real.exp_pos 2]
    exact h1.trans (mul_le_mul_of_nonneg_left hy1 (Real.exp_pos 2).le)
  have hW0 : 0 ≤ (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by positivity
  calc _ ≤ (Real.exp 2 / (k : ℝ) ^ 2) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) *
          (8 * (9 + 2 * LeanLab.Romanov.R₁) * N) := h
    _ = 8 * (9 + 2 * LeanLab.Romanov.R₁) * (Real.exp 2 / (k : ℝ) ^ 2) *
          ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by ring
    _ ≤ 8 * (9 + 2 * LeanLab.Romanov.R₁) * (Real.exp 2 * (Real.log (2 * k) ^ 2 / k)) *
          ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
        apply mul_le_mul_of_nonneg_right _ hW0
        exact mul_le_mul_of_nonneg_left hk2 (by positivity)
    _ = _ := by ring

/-- ASSEMBLY from the proved leaves `measurableSet_majorArcs`, `G_eq_Gs`,
`major_arc_bound`, `lemma11`, `thetaK_small`, `exp_neg_le`, `etaK_small` and `power_le`,
with the lab's proved Lemma 2, `lemma2`, and Lemma 12, `gallagher_eta_arc_le`.
Display (6) for `k ≥ k₀`, p. 139, in the lab's form `Display6Large`. -/
theorem display6Large_of_leaves : LeanLab.Linnik.U7206.Display6Large := by
  obtain ⟨c, C5, θ0, hc, hθ0, h5⟩ := major_arc_bound
  obtain ⟨C11, θ1, E, hθ1, h11⟩ := lemma11
  obtain ⟨K1, hK1⟩ := thetaK_small (min θ0 θ1) (lt_min hθ0 hθ1)
  obtain ⟨K2, hK2⟩ := exp_neg_le c hc
  obtain ⟨K3, hK3⟩ := etaK_small
  have hR := LeanLab.Romanov.R₁_pos
  refine ⟨2 * |C5| + 1 + 8 * (9 + 2 * LeanLab.Romanov.R₁) * Real.exp 2,
    max (max K1 K2) (max K3 3), fun k hk => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3' : 3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hθpos, hθle⟩ := hK1 k hk1
  have hθ0' : thetaK k ≤ θ0 := hθle.trans (min_le_left _ _)
  have hθ1' : thetaK k ≤ θ1 := hθle.trans (min_le_right _ _)
  obtain ⟨hηpos, hηle⟩ := hK3 k hk3
  obtain ⟨Nk5, hN5⟩ := h5 (thetaK k) hθpos hθ0' k (by omega)
  obtain ⟨N7, hN7⟩ := power_le (4 * C11 ^ 2 * k) (2 * E + 2) (thetaK k / 2) (by positivity)
  refine ⟨max (max Nk5 N7) 8, fun N hN => ?_⟩
  have hN5' : Nk5 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN7' : N7 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN8 : 8 ≤ N := le_trans (le_max_right _ _) hN
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk3'
  have hk0 : (0 : ℝ) < k := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMm := measurableSet_majorArcs N ((N : ℝ) ^ thetaK k)
  have hMs : majorArcs N ((N : ℝ) ^ thetaK k) ⊆ Set.Icc 0 1 := fun α h => h.1
  have hEm : MeasurableSet {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} :=
    measurableSet_le measurable_const (continuous_Gs _).norm.measurable
  have hf : Continuous fun α => ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 :=
    ((LeanLab.Linnik.U7206.continuous_Sg N).mul ((continuous_Gs _).pow k)).norm.pow 2
  rw [split3 _ hf hMm hMs hEm]
  -- piece 1
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLge : Real.log N ≤ (Nat.log 2 N : ℝ) := LeanLab.Linnik.U7206.log_le_L hN8
  have hI1 := hN5 N hN5'
  have hlogk : Real.log k ^ 2 / k ≤ Real.log (2 * k) ^ 2 / k := by
    apply div_le_div_of_nonneg_right _ hk0.le
    have h0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
    have h1 : Real.log k ≤ Real.log (2 * k) := Real.log_le_log hk0 (by linarith)
    exact pow_le_pow_left₀ h0 h1 2
  have hexp : Real.exp (-c / thetaK k) ≤ Real.log (2 * k) ^ 2 / k := hK2 k hk2
  have hsum0 : 0 ≤ Real.log k ^ 2 / k + Real.exp (-c / thetaK k) := by positivity
  have hC : C5 * (Real.log k ^ 2 / k + Real.exp (-c / thetaK k)) ≤
      2 * |C5| * (Real.log (2 * k) ^ 2 / k) := by
    calc C5 * (Real.log k ^ 2 / k + Real.exp (-c / thetaK k))
        ≤ |C5| * (Real.log k ^ 2 / k + Real.exp (-c / thetaK k)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
      _ ≤ |C5| * (2 * (Real.log (2 * k) ^ 2 / k)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 2 * |C5| * (Real.log (2 * k) ^ 2 / k) := by ring
  have hmain0 : 0 ≤ 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 := by positivity
  have hI1' := hI1.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + C5 * (Real.log k ^ 2 / k +
    Real.exp (-c / thetaK k)) ≤ 1 + 2 * |C5| * (Real.log (2 * k) ^ 2 / k)) hmain0)
  -- piece 2
  have hA := hN7 N hN7'
  have hI2 := piece2 hk3' hN8 hηpos hηle (h11 (thetaK k) hθpos hθ1' N (by omega)) hA
  have hy1 : 1 / (k : ℝ) ≤ Real.log (2 * k) ^ 2 / k := by
    have hlog2k : 1 ≤ Real.log (2 * k) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    exact div_le_div_of_nonneg_right (by nlinarith) hk0.le
  have hW0 : 0 ≤ (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by positivity
  have hI2' : ∫ α in (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
        {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        (Real.log (2 * k) ^ 2 / k) * ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
    refine hI2.trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hy1 hW0
  -- piece 3
  have hI3 := piece3 (N := N) hk3' hMm
  -- W ≤ main / 2
  have hpow : (Nat.log 2 N : ℝ) ^ (2 * k) =
      (Nat.log 2 N : ℝ) ^ (2 * k - 2) * (Nat.log 2 N : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hW : (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 / 2 := by
    have hq : 1 ≤ (Nat.log 2 N : ℝ) ^ 2 / Real.log N ^ 2 :=
      (one_le_div (by positivity)).mpr (pow_le_pow_left₀ hlogN.le hLge 2)
    have : 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 / 2 =
        (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) * ((Nat.log 2 N : ℝ) ^ 2 / Real.log N ^ 2) := by
      rw [hpow]; field_simp
    rw [this]
    nlinarith
  exact alg_final hI1' hI2' hI3 hW (by positivity) (by positivity) (Real.exp_pos 2).le hmain0

/-- ASSEMBLY from the proved leaves of this file listed at `display6Large_of_leaves`, with no
hypothesis. Gallagher's Theorem 1, display (3) p. 125, for g = 2, through the lab's proved Lemma 12. -/
theorem theorem1_of_leaves : LeanLab.Linnik.Gallagher1975.Theorem1 :=
  LeanLab.Romanov.gallagher_theorem1_of_large display6Large_of_leaves

/-- ASSEMBLY from the proved leaves of this file listed at `display6Large_of_leaves`, with no
hypothesis. Gallagher's Theorem 2, display (4) p. 125, for g = 2: for `k ≥ 2` and even `N ≥ N_k`,
`r''_k(N) = 2N L^k / log² N · (1 + O(log² k / k))`. -/
theorem theorem2_of_leaves :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(LeanLab.Linnik.Gallagher1975Thm2.rpp k N : ℝ) -
        2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  LeanLab.Romanov.gallagher_theorem2_of_large display6Large_of_leaves

end LeanLab.Linnik.Decomp1532c
