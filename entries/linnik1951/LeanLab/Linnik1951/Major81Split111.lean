module

public import LeanLab.Linnik1951.CircleSplit111
public import LeanLab.Linnik1951.Decomp520a
public import LeanLab.Perelli1996.TotientRatio320
public import LeanLab.Linnik1951.LogConvPort111
public import LeanLab.Linnik1951.SingularSize111

/-!
P0093 pages 161 and 165 to 168, equations 6.4, 8.1, 8.2 and 10.7, the major arcs.
Burst 8 p3 split of major_truncated_split111 of Decomp111.
AI wrote the Lean code. Binary Goldbach is open.

The tuple expansion of T to the k, the first step of 8.1, is proved here, and so is the
whole bookkeeping of 8.1, 8.2 and 10.7: major_bookkeeping_m111, major_main_sum_m111 and
truncSingular_small_m111, with the convolution estimate ported in LogConvPort111 and the
singular series size proved in SingularSize111. The remaining input is decomposed in Decomp520a:
- major_local_expansion_m111, under GRH and three local analytic leaves: 6.4 for every q at most Q, summed over the arcs
  of the major arcs, at one residual n, uniformly in n. This is the analytic core, which
  rests in P0093 on Lemma 1, cited to Lucke [5], and on the GRH bound for ln L of s chi
  on the line sigma_0 stated on page 159 without proof. CITED-LEFT.
Definitions here are local copies, same bodies, of truncSingular111 and mainTermTrunc111
of Decomp111 and of logConvolution1622 of SPLIT1622_major, which sit downstream.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- P0093 page 165 equation 8.1, the expansion of T to the k: splitting the first exponent
off a tuple of k plus 1 exponents. Proved. -/
theorem tuple_cons_prod_split111 {R : Type*} [CommMonoid R] (f : ℕ → R) (k : ℕ)
    (x : ℕ × (Fin k → ℕ)) :
    (fun ν : Fin (k + 1) → ℕ => ∏ i, f (ν i)) (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ) x) =
      f x.1 * ∏ i, f (x.2 i) := by
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- P0093 page 165 equation 8.1: for a summable nonnegative family, the products over
tuples of k exponents are summable. Proved by induction on k. -/
theorem summable_tuple_prod_real_split111 (g : ℕ → ℝ) (hg0 : ∀ m, 0 ≤ g m)
    (hg : Summable g) (k : ℕ) : Summable (fun ν : Fin k → ℕ => ∏ i, g (ν i)) := by
  induction k with
  | zero => exact (hasSum_fintype _).summable
  | succ k ih =>
      let G : (Fin k → ℕ) → ℝ := fun ν => ∏ i, g (ν i)
      have hG0 : 0 ≤ G := fun ν => Finset.prod_nonneg (fun i _ => hg0 _)
      have hg0' : 0 ≤ g := fun m => hg0 m
      have hprod : Summable (fun x : ℕ × (Fin k → ℕ) => g x.1 * G x.2) :=
        Summable.mul_of_nonneg (f := g) (g := G) hg ih hg0' hG0
      refine ((Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).summable_iff).mp ?_
      refine hprod.congr ?_
      intro x
      exact (tuple_cons_prod_split111 g k x).symm

/-- P0093 page 165 equation 8.1: an absolutely summable series raised to the k is the sum
over all tuples x_1 to x_k of the products of its terms. Proved by induction on k with
Mathlib HasSum.mul. -/
theorem hasSum_tuple_prod_split111 (f : ℕ → ℂ) (hf : Summable (fun m => ‖f m‖)) (k : ℕ) :
    HasSum (fun ν : Fin k → ℕ => ∏ i, f (ν i)) ((∑' m, f m) ^ k) := by
  induction k with
  | zero =>
      have := hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, f (ν i))
      simpa using this
  | succ k ih =>
      let F : (Fin k → ℕ) → ℂ := fun ν => ∏ i, f (ν i)
      have hnorm : Summable (fun ν : Fin k → ℕ => ‖F ν‖) := by
        have h := summable_tuple_prod_real_split111 (fun m => ‖f m‖) (fun m => norm_nonneg _) hf k
        refine h.congr ?_
        intro ν
        simp only [F, norm_prod]
      have hmul := HasSum.mul (f := f) (g := F) hf.of_norm.hasSum ih
        (summable_mul_of_summable_norm (f := f) (g := F) hf hnorm)
      rw [pow_succ']
      refine ((Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).hasSum_iff).mp ?_
      refine hmul.congr_fun ?_
      intro x
      exact tuple_cons_prod_split111 f k x

/-- P0093 page 165 equation 8.1, first step: on any part s of the unit interval, the
integral of S squared times T to the k times e of N alpha is the sum over all tuples of
exponents of the tuple weight, the product of the e to the minus 2 to the x_i over N,
times the integral of S squared times e of N_1 alpha, with N_1 equal to N minus the sum of
the 2 to the x_i, here x_i equal to nu i plus 1. Exchange of sum and integral by dominated
convergence, with dominating function S squared times the tuple weight. Proved. -/
theorem arc_tuple_expand_split111 (k N : ℕ) (hN : 1 ≤ N) (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1) :
    HasSum (fun ν : Fin k → ℕ =>
      (((∏ i, Real.exp (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N)) : ℝ) : ℂ) *
        ∫ α in s, primeFourier111_up111 N α ^ 2 *
          Complex.exp (((2 * Real.pi * α * ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ))) : ℝ) *
            Complex.I))
      (∫ α in s, primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k *
          Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let w : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let f : ℝ → ℕ → ℂ := fun α m => (w m : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hw0 : ∀ m, 0 ≤ w m := fun m => (Real.exp_pos _).le
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have hw : Summable w := (damping_summable111_up111 N hN).comp_injective hi
  have hfn : ∀ α m, ‖f α m‖ = w m := by
    intro α m
    simp only [f, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hw0 m)]
  have hfs : ∀ α, Summable (fun m => ‖f α m‖) := fun α => hw.congr (fun m => (hfn α m).symm)
  have hT : ∀ α, powerFourier111_up111 N α = ∑' m, f α m := fun α => rfl
  let W : (Fin k → ℕ) → ℝ := fun ν => ∏ i, w (ν i)
  have hW0 : ∀ ν, 0 ≤ W ν := fun ν => Finset.prod_nonneg (fun i _ => hw0 _)
  have hWs : Summable W := summable_tuple_prod_real_split111 w hw0 hw k
  let F : (Fin k → ℕ) → ℝ → ℂ := fun ν α => primeFourier111_up111 N α ^ 2 *
    (∏ i, f α (ν i)) * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)
  have hS : Continuous (primeFourier111_up111 N) := continuous_prime_fourier111_up111 N hN
  have hFcont : ∀ ν, Continuous (F ν) := by
    intro ν
    simp only [F, f]
    fun_prop
  have hFnorm : ∀ ν α, ‖F ν α‖ = ‖primeFourier111_up111 N α‖ ^ 2 * W ν := by
    intro ν α
    simp only [F, W, norm_mul, norm_pow, norm_prod, hfn, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hlim : ∀ α, HasSum (fun ν => F ν α) (primeFourier111_up111 N α ^ 2 *
      powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by
    intro α
    have h := hasSum_tuple_prod_split111 (f α) (hfs α) k
    rw [hT α]
    exact (h.mul_left (primeFourier111_up111 N α ^ 2)).mul_right _
  have hint : MeasureTheory.IntegrableOn (fun α => ‖primeFourier111_up111 N α‖ ^ 2) s :=
    (((continuous_prime_fourier111_up111 N hN).norm.pow 2).continuousOn.integrableOn_Icc).mono_set
      hs
  have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict s) (F := F)
    (bound := fun ν α => ‖primeFourier111_up111 N α‖ ^ 2 * W ν)
    (fun ν => (hFcont ν).aestronglyMeasurable)
    (fun ν => Filter.Eventually.of_forall (fun α => (hFnorm ν α).le))
    (Filter.Eventually.of_forall (fun α => hWs.mul_left _))
    (by
      have : (fun α => ∑' ν, ‖primeFourier111_up111 N α‖ ^ 2 * W ν) =
          fun α => ‖primeFourier111_up111 N α‖ ^ 2 * ∑' ν, W ν := by
        funext α; exact tsum_mul_left
      rw [this]
      exact hint.mul_const _)
    (Filter.Eventually.of_forall hlim)
  refine hmain.congr_fun ?_
  intro ν
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun α => ?_)
  simp only [F, f]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod]
  have hexp : Complex.exp (∑ i, ((-(2 * Real.pi * α * ((2 ^ (ν i + 1) : ℕ) : ℝ)) : ℝ) : ℂ) *
        Complex.I) * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
      Complex.exp (((2 * Real.pi * α * ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ))) : ℝ) *
        Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rw [← Finset.sum_mul, ← add_mul]
    congr 1
    rw [Finset.sum_neg_distrib, mul_sub, Finset.mul_sum]
    ring
  rw [← hexp]
  ring




section Support89
open Filter

/-- Copy of polylog_small_split111 of Decomp111, same proof, for use upstream of it.
P0093 pages 166 and 168: a constant times a fixed power of ln N is eventually below
epsilon times a fixed positive power of N. Proved. -/
theorem polylog_small_m111 (j : ℕ) {c A ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → A * Real.log N ^ j ≤ ε * (N : ℝ) ^ c := by
  have hA : 0 < |A| + 1 := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ) hc).def (c := ε / (|A| + 1)) (by positivity)
  have h3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (h.and (eventually_gt_atTop 1))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h3
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hb, h1⟩ := hN0 N hN.le
  have hL : 0 ≤ Real.log N := (Real.log_pos h1).le
  have hNc : 0 ≤ (N : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL _),
    Real.norm_eq_abs, abs_of_nonneg hNc] at hb
  have hpow : 0 ≤ Real.log N ^ j := pow_nonneg hL _
  calc A * Real.log N ^ j ≤ (|A| + 1) * Real.log N ^ j :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) hpow
    _ ≤ (|A| + 1) * (ε / (|A| + 1) * (N : ℝ) ^ c) := mul_le_mul_of_nonneg_left hb hA.le
    _ = ε * (N : ℝ) ^ c := by field_simp


/-- Helper for P0093 page 166 equation 8.2: the sum of 1 over the square root of q for q
from 1 to Q is at most 2 times the square root of Q. Proved by induction. -/
theorem inv_sqrt_sum_le_split111 (Q : ℕ) :
    ∑ q ∈ Icc 1 Q, 1 / Real.sqrt q ≤ 2 * Real.sqrt Q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    set a := Real.sqrt ((Q : ℝ) + 1) with ha
    set b := Real.sqrt (Q : ℝ) with hb
    have ha2 : a ^ 2 = (Q : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (Q : ℝ) := Real.sq_sqrt (by positivity)
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
    have hstep : 1 / a ≤ 2 * a - 2 * b := by
      rw [div_le_iff₀ hapos]
      nlinarith
    linarith

/-- P0093 page 166 equation 8.2 with the parameters of page 165, tau equal to N to the one
seventh and Q equal to N to the one tenth: the sum over q at most Q of the error factor
1 over tau plus 1 over the square root of q tau from 6.4 is at most 3 times N to the minus
3 over 140, the printed N to the minus 1 over 68 up to the exponent. Proved. This is the
computation behind the resolution of the burst 9 QUESTION in the p3 note. -/
theorem error_sum_82_split111 (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      3 * (N : ℝ) ^ (-(3 / 140 : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  set Q : ℕ := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ with hQ
  have hτp : 0 < τ := Real.rpow_pos_of_pos hNp _
  have hQle : (Q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hNp.le _)
  rw [Finset.sum_add_distrib]
  have h1 : ∑ q ∈ Icc 1 Q, 1 / τ ≤ (N : ℝ) ^ (-(3 / 140 : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    calc (Q : ℝ) * (1 / τ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (1 / τ) :=
          mul_le_mul_of_nonneg_right hQle (by positivity)
      _ = (N : ℝ) ^ (-(3 / 70 : ℝ)) := by
          rw [hτ, mul_one_div, ← Real.rpow_sub hNp]; norm_num
      _ ≤ (N : ℝ) ^ (-(3 / 140 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h2 : ∑ q ∈ Icc 1 Q, 1 / Real.sqrt (q * τ) ≤ 2 * (N : ℝ) ^ (-(3 / 140 : ℝ)) := by
    have hsplit : ∀ q ∈ Icc 1 Q, 1 / Real.sqrt (q * τ) =
        (1 / Real.sqrt q) * (1 / Real.sqrt τ) := by
      intro q _
      rw [Real.sqrt_mul (Nat.cast_nonneg q), one_div_mul_one_div]
    rw [Finset.sum_congr rfl hsplit, ← Finset.sum_mul]
    have hsq : Real.sqrt (Q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
      rw [show (1 / 20 : ℝ) = (1 / 10) * (1 / 2) by norm_num, Real.rpow_mul hNp.le,
        Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hQle (by norm_num)
    have hsτ : 1 / Real.sqrt τ = (N : ℝ) ^ (-(1 / 14 : ℝ)) := by
      rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le, Real.rpow_neg hNp.le, one_div]
      norm_num
    calc (∑ q ∈ Icc 1 Q, 1 / Real.sqrt q) * (1 / Real.sqrt τ)
        ≤ (2 * Real.sqrt Q) * (1 / Real.sqrt τ) :=
          mul_le_mul_of_nonneg_right (inv_sqrt_sum_le_split111 Q) (by positivity)
      _ ≤ (2 * (N : ℝ) ^ (1 / 20 : ℝ)) * (N : ℝ) ^ (-(1 / 14 : ℝ)) := by
          rw [hsτ]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * (N : ℝ) ^ (-(3 / 140 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hNp]; norm_num
  linarith

/-- P0093 page 166 equation 9.1, read for one system F_q with q between Q equal to N to the
one tenth and tau equal to N to the one seventh: the right side of 9.1, mu squared of q
over phi of q times N over ln N plus B N ln to the 13 of N times 1 over tau plus 2 over the
square root of q tau, is at most 5 times N to the 93 hundredths for large N. So the leaf
system_mass_split111 of Lemma6Split111 is a consequence of 9.1. Proved, with the lab bound
q over phi of q at most 2 times 1 plus ln q of Perelli1996 TotientRatio320. -/
theorem system_bound_91_split111 (B : ℝ) (hB : 0 < B) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) *
            ((N : ℝ) / Real.log N) +
          B * N * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 2 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
          5 * (N : ℝ) ^ (93 / 100 : ℝ) := by
  obtain ⟨N1, hpl⟩ := polylog_small_m111 13 (c := 9 / 175) (A := 3 * B) (ε := 1)
    (by norm_num) one_pos
  refine ⟨max N1 3, fun N hN q hqQ hqτ => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNR : (3 : ℝ) < N := by exact_mod_cast hN3
  have hNp : (0 : ℝ) < N := by linarith
  have hN1R : (1 : ℝ) ≤ N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogp : 0 < Real.log N := by linarith
  have hqpos : (0 : ℝ) < q := lt_of_le_of_lt (Real.rpow_nonneg hNp.le _) hqQ
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have htot : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  -- first term of 9.1
  have hq_le_N : (q : ℝ) ≤ N := hqτ.trans (by
    calc (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
      _ = N := Real.rpow_one _)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hqpos hq_le_N
  have hratio := LeanLab.Perelli1996.TotientRatio320.ratio_le_log q hq0
  have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := q)
    have h' : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ), sq_abs
      ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
  have hinvtot : 1 / (Nat.totient q : ℝ) ≤ 4 * Real.log N / q := by
    rw [div_le_div_iff₀ htot hqpos, one_mul]
    have h2 := (div_le_iff₀ htot).mp hratio
    nlinarith
  have hfirst : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) *
      ((N : ℝ) / Real.log N) ≤ 4 * (N : ℝ) ^ (93 / 100 : ℝ) := by
    have hm0 : 0 ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 := sq_nonneg _
    have hNl : 0 ≤ (N : ℝ) / Real.log N := by positivity
    calc ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) *
          ((N : ℝ) / Real.log N)
        ≤ (1 / (Nat.totient q : ℝ)) * ((N : ℝ) / Real.log N) := by
          apply mul_le_mul_of_nonneg_right _ hNl
          rw [div_eq_mul_one_div]
          exact mul_le_of_le_one_left (by positivity) hmu
      _ ≤ (4 * Real.log N / q) * ((N : ℝ) / Real.log N) :=
          mul_le_mul_of_nonneg_right hinvtot hNl
      _ = 4 * (N : ℝ) / q := by field_simp
      _ ≤ 4 * (N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNp _) hqQ.le
      _ = 4 * (N : ℝ) ^ (9 / 10 : ℝ) := by
          rw [mul_div_assoc]
          congr 1
          rw [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num, Real.rpow_sub hNp, Real.rpow_one]
      _ ≤ 4 * (N : ℝ) ^ (93 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)) (by norm_num)
  -- second term of 9.1
  have hτ : 1 / (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (-(17 / 140 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg hNp.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
  have hqτs : 2 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ)) ≤ 2 * (N : ℝ) ^ (-(17 / 140 : ℝ)) := by
    have hlow : (N : ℝ) ^ (17 / 140 : ℝ) ≤ Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ)) := by
      have hprod : (N : ℝ) ^ (17 / 70 : ℝ) ≤ q * (N : ℝ) ^ (1 / 7 : ℝ) := by
        calc (N : ℝ) ^ (17 / 70 : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
              rw [← Real.rpow_add hNp]; norm_num
          _ ≤ q * (N : ℝ) ^ (1 / 7 : ℝ) :=
              mul_le_mul_of_nonneg_right hqQ.le (Real.rpow_nonneg hNp.le _)
      calc (N : ℝ) ^ (17 / 140 : ℝ) = Real.sqrt ((N : ℝ) ^ (17 / 70 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]; norm_num
        _ ≤ _ := Real.sqrt_le_sqrt hprod
    have hpos : 0 < (N : ℝ) ^ (17 / 140 : ℝ) := Real.rpow_pos_of_pos hNp _
    calc 2 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ)) ≤ 2 / (N : ℝ) ^ (17 / 140 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hlow
      _ = 2 * (N : ℝ) ^ (-(17 / 140 : ℝ)) := by
          rw [Real.rpow_neg hNp.le, div_eq_mul_inv]
  have hpl' := hpl N hN1
  have hsecond : B * N * Real.log N ^ 13 *
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 2 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
        (N : ℝ) ^ (93 / 100 : ℝ) := by
    have hBN : 0 ≤ B * N * Real.log N ^ 13 := by positivity
    calc B * N * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 2 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ)))
        ≤ B * N * Real.log N ^ 13 * (3 * (N : ℝ) ^ (-(17 / 140 : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) hBN
      _ = (3 * B * Real.log N ^ 13) * ((N : ℝ) * (N : ℝ) ^ (-(17 / 140 : ℝ))) := by ring
      _ ≤ (1 * (N : ℝ) ^ (9 / 175 : ℝ)) * ((N : ℝ) * (N : ℝ) ^ (-(17 / 140 : ℝ))) :=
          mul_le_mul_of_nonneg_right hpl' (by positivity)
      _ = (N : ℝ) ^ (93 / 100 : ℝ) := by
          rw [← Real.rpow_one_add' hNp.le (by norm_num), one_mul, ← Real.rpow_add hNp]
          norm_num
  linarith

/-- P0093 page 166 equation 8.2 and page 168, the absorption of R_1 into the scale of
Section 11: with at most ln N over ln 2 plus 2 to the k in tuple weight, as in the count
of the N_1 on page 166, and the summed error N ln to the 13 of N times 3 N to the minus
3 over 140 of error_sum_82_split111, the total is eventually below any epsilon times
scale111 for every k at least 3. Proved. With the paper's parameters, so the lab tau, the
error accounting of 8.1 and 8.2 therefore fits inside major_truncated_split111. -/
theorem r1_absorb_split111 (B : ℝ) (hB : 0 < B) (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      B * (Real.log N / Real.log 2 + 2) ^ k * N * Real.log N ^ 13 *
          (3 * (N : ℝ) ^ (-(3 / 140 : ℝ))) ≤ ε * scale111_up111 k N := by
  obtain ⟨N1, hpl⟩ := polylog_small_m111 15 (c := 3 / 140) (A := 3 * B * 4 ^ k)
    (by norm_num) hε
  refine ⟨max N1 3, fun N hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNR : (3 : ℝ) < N := by exact_mod_cast hN3
  have hNp : (0 : ℝ) < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl21 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl2p : 0 < Real.log 2 := by linarith
  set L := Real.log N with hL
  have hbase : L / Real.log 2 + 2 ≤ 4 * L := by
    have : L / Real.log 2 ≤ 2 * L := by
      rw [div_le_iff₀ hl2p]; nlinarith
    linarith
  have hbase0 : 0 ≤ L / Real.log 2 + 2 := by positivity
  have hpowk : (L / Real.log 2 + 2) ^ k ≤ 4 ^ k * L ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hbase0 hbase k
  have hscale : N * L ^ (k - 2) ≤ scale111_up111 k N := by
    unfold scale111_up111
    rw [← hL]
    apply mul_le_mul_of_nonneg_left _ hNp.le
    rw [div_pow]
    rw [le_div_iff₀ (pow_pos hl2p _)]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hl2p.le hl21.le)
  have hk2 : L ^ k * L ^ 13 = L ^ 15 * L ^ (k - 2) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hpl' := hpl N hN1
  have hNsplit : (N : ℝ) * (N : ℝ) ^ (-(3 / 140 : ℝ)) * (N : ℝ) ^ (3 / 140 : ℝ) = N := by
    rw [mul_assoc, ← Real.rpow_add hNp]; norm_num
  have hnn : 0 ≤ (N : ℝ) * (N : ℝ) ^ (-(3 / 140 : ℝ)) * L ^ (k - 2) := by positivity
  calc B * (L / Real.log 2 + 2) ^ k * N * L ^ 13 * (3 * (N : ℝ) ^ (-(3 / 140 : ℝ)))
      ≤ B * (4 ^ k * L ^ k) * N * L ^ 13 * (3 * (N : ℝ) ^ (-(3 / 140 : ℝ))) := by
        gcongr
    _ = (3 * B * 4 ^ k * L ^ 15) * ((N : ℝ) * (N : ℝ) ^ (-(3 / 140 : ℝ)) * L ^ (k - 2)) := by
        rw [show B * (4 ^ k * L ^ k) * N * L ^ 13 * (3 * (N : ℝ) ^ (-(3 / 140 : ℝ))) =
          3 * B * 4 ^ k * (L ^ k * L ^ 13) * ((N : ℝ) * (N : ℝ) ^ (-(3 / 140 : ℝ))) by ring,
          hk2]
        ring
    _ ≤ (ε * (N : ℝ) ^ (3 / 140 : ℝ)) *
          ((N : ℝ) * (N : ℝ) ^ (-(3 / 140 : ℝ)) * L ^ (k - 2)) :=
        mul_le_mul_of_nonneg_right hpl' hnn
    _ = ε * ((N : ℝ) * (N : ℝ) ^ (-(3 / 140 : ℝ)) * (N : ℝ) ^ (3 / 140 : ℝ) * L ^ (k - 2)) := by
        ring
    _ = ε * (N * L ^ (k - 2)) := by rw [hNsplit]
    _ ≤ ε * scale111_up111 k N := mul_le_mul_of_nonneg_left hscale hε.le


end Support89

/-- P0093 page 168 equation 10.6 left side. Local copy of truncSingular111 of Decomp111. -/
noncomputable def truncSingular_m111 (Q n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Real.cos (2 * Real.pi * (n : ℝ) * (a : ℝ) / (q : ℝ))

/-- P0093 page 165 equation 8.1 main term with the truncated singular series. Local copy
of mainTermTrunc111 of Decomp111. -/
noncomputable def mainTermTrunc_m111 (k N Q : ℕ) : ℝ := by
  classical
  exact ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
      Even (N - ∑ i, 2 ^ (ν i).val)),
    truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2

/-- P0093 page 161 after equation 6.3: the sum of 1 over ln m ln m prime over m plus m
prime equal to n with both at least 2, empty for n below 4. Local copy of
logConvolution1622 of SPLIT1622_major. -/
noncomputable def logConv_m111 (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ))

/-- P0093 page 165, the N_1 of 8.1 are even: a sum of powers 2 to the x with x at least 1
is even. Proved. -/
theorem tuple_sum_even_m111 {k : ℕ} (ν : Fin k → ℕ) : Even (∑ i, 2 ^ (ν i + 1)) := by
  rw [even_iff_two_dvd]
  exact Finset.dvd_sum (fun i _ => dvd_pow_self 2 (Nat.succ_ne_zero _))

/-- P0093 page 165 equation 8.1 and page 168 equation 10.7: the main term of Decomp111,
indexed by tuples in Fin of N plus 1 with exponents at least 1, rewritten over tuples of
naturals nu with x_i equal to nu i plus 1 and N_1 at least 2; evenness of N_1 is automatic
for even N. Proved. -/
theorem mainTermTrunc_reindex_m111 (k N Q : ℕ) (hN : Even N) (hN1 : 1 ≤ N) :
    mainTermTrunc_m111 k N Q =
      ∑ ν ∈ (Fintype.piFinset fun _ : Fin k => Finset.range N).filter
          (fun ν => 2 + ∑ i, 2 ^ (ν i + 1) ≤ N),
        truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
          ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) / Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2 := by
  classical
  unfold mainTermTrunc_m111
  refine Finset.sum_nbij' (fun ν' j => (ν' j).val - 1)
    (fun ν j => (⟨(ν j + 1) % (N + 1), Nat.mod_lt _ (by omega)⟩ : Fin (N + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intro ν' hν'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν'
    obtain ⟨h1, h2, _⟩ := hν'
    have hs : ∑ i, 2 ^ ((ν' i).val - 1 + 1) = ∑ i, 2 ^ (ν' i).val :=
      Finset.sum_congr rfl (fun i _ => by rw [Nat.sub_add_cancel (h1 i)])
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i => ?_, ?_⟩
    · have := (ν' i).isLt; have := h1 i; omega
    · rw [hs]; omega
  · intro ν hν
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hν
    obtain ⟨h1, h2⟩ := hν
    have hval : ∀ i, (ν i + 1) % (N + 1) = ν i + 1 := fun i => Nat.mod_eq_of_lt (by have := h1 i; omega)
    have hs : ∑ i, 2 ^ ((ν i + 1) % (N + 1)) = ∑ i, 2 ^ (ν i + 1) :=
      Finset.sum_congr rfl (fun i _ => by rw [hval i])
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i => by rw [hval i]; omega, by rw [hs]; omega, ?_⟩
    rw [hs, Nat.even_sub (by omega)]
    exact iff_of_true hN (tuple_sum_even_m111 ν)
  · intro ν' hν'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν'
    funext j
    apply Fin.ext
    simp only
    have := (ν' j).isLt; have := hν'.1 j
    rw [Nat.sub_add_cancel (hν'.1 j), Nat.mod_eq_of_lt (by omega)]
  · intro ν hν
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hν
    funext j
    simp only
    rw [Nat.mod_eq_of_lt (by have := hν.1 j; omega)]
    omega
  · intro ν' hν'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν'
    have hs : ∑ i, 2 ^ ((ν' i).val - 1 + 1) = ∑ i, 2 ^ (ν' i).val :=
      Finset.sum_congr rfl (fun i _ => by rw [Nat.sub_add_cancel (hν'.1 i)])
    simp only [hs]

/-- PROVED in burst 8 p3, formerly a leaf. P0093 page 168, after equation 10.6, the size of the truncated
singular series, in the form 10.7 needs: for every epsilon_0 there is C_0 with the
truncated series at any level Q and any n at least 1 at most epsilon_0 ln n plus C_0. It
follows from the classical bound: the Ramanujan sum at a squarefree q is at most the gcd
of q and n in size, so the series is at most the product over p of 1 plus gcd of p and n
over p minus 1 squared, a constant times n over phi of n, which is at most a constant
times ln ln n by Landau. The paper uses instead an absolute upper bound c_1 for the
singular series at even N_1, which fails; see the QUESTION in the p3 note. -/
theorem truncSingular_small_m111 (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ Q n : ℕ, 1 ≤ n →
      |truncSingular_m111 Q n| ≤ ε0 * Real.log n + C0 := by
  -- PROVED burst 8 p3 in SingularSize111, by the gcd split of q, the convergent sum of
  -- 1 over phi squared, and the divisor sum of 1 over phi.
  obtain ⟨C0, hC0, h⟩ := truncSingular_size_m111 ε0 hε0
  exact ⟨C0, hC0, fun Q n hn => h Q n hn⟩

/-- P0093 page 161 after equation 6.3: for 4 at most m at most N, the convolution
differs from m over ln squared m by at most K_0 plus C_1 times the square root of N plus
8 N over ln cubed N. From the ported clean lab estimates, the finite range bound for m
below 1000 and the excess bound C m over ln cubed m above. Proved. -/
theorem logConv_dev_m111 :
    ∃ K0 C1 : ℝ, 0 < K0 ∧ 0 < C1 ∧ ∀ N m : ℕ, 4 ≤ m → m ≤ N →
      |logConv_m111 m - (m : ℝ) / Real.log m ^ 2| ≤
        K0 + C1 * (Real.sqrt N + 8 * (N : ℝ) / Real.log N ^ 3) := by
  obtain ⟨B, hB, hsmall⟩ := logConv_small_range1622_lc111
  obtain ⟨C1, hC1, hexc⟩ := logConv_excess_corrected474_lc111
  refine ⟨B * 1000, C1, by positivity, hC1, fun N m h4 hmN => ?_⟩
  have hl4 : 1 < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9; push_cast; linarith
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast h4
  have hlm : 1 < Real.log m := lt_of_lt_of_le hl4 (Real.log_le_log (by norm_num) hmR)
  have hNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlN : 1 < Real.log N := lt_of_lt_of_le hlm (Real.log_le_log (by linarith) hNR)
  have hsq0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hterm0 : 0 ≤ 8 * (N : ℝ) / Real.log N ^ 3 := by positivity
  rcases lt_or_ge m 1000 with hm | hm
  · have h := hsmall m (by omega) hm.le
    have hf : (m : ℝ) / Real.log m ^ 2 ≤ 1000 := by
      rw [div_le_iff₀ (by positivity)]
      have : (m : ℝ) ≤ 1000 := by exact_mod_cast hm.le
      nlinarith
    have hs : 1 / Real.sqrt (Real.log m) ≤ 1 := by
      rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have hf0 : 0 ≤ (m : ℝ) / Real.log m ^ 2 := by positivity
    calc |logConv_m111 m - (m : ℝ) / Real.log m ^ 2|
        ≤ B * ((m : ℝ) / Real.log m ^ 2) * (1 / Real.sqrt (Real.log m)) := h
      _ ≤ B * 1000 * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hf hB.le) hs (by positivity) (by positivity)
      _ ≤ B * 1000 + C1 * (Real.sqrt N + 8 * (N : ℝ) / Real.log N ^ 3) := by
          have : 0 ≤ C1 * (Real.sqrt N + 8 * (N : ℝ) / Real.log N ^ 3) := by positivity
          linarith
  · have hlow : (m : ℝ) / Real.log m ^ 2 ≤ logConv_m111 m := logConv_main_le1622_lc111 m h4
    have hup := hexc m hm
    have habs : |logConv_m111 m - (m : ℝ) / Real.log m ^ 2| =
        logConv_m111 m - (m : ℝ) / Real.log m ^ 2 := abs_of_nonneg (by linarith)
    have hcube : (m : ℝ) / Real.log m ^ 3 ≤ Real.sqrt N + 8 * (N : ℝ) / Real.log N ^ 3 := by
      rcases le_or_gt (m : ℝ) (Real.sqrt N) with hs | hs
      · have : (m : ℝ) / Real.log m ^ 3 ≤ m := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ Real.log m ^ 3 := one_le_pow₀ hlm.le
          nlinarith
        linarith
      · have hlog2 : Real.log N / 2 ≤ Real.log m := by
          have h1 : Real.log (Real.sqrt N) = Real.log N / 2 := by
            rw [Real.log_sqrt hNpos.le]
          rw [← h1]
          exact Real.log_le_log (Real.sqrt_pos.mpr hNpos) hs.le
        have hcub : (Real.log N / 2) ^ 3 ≤ Real.log m ^ 3 :=
          pow_le_pow_left₀ (by linarith) hlog2 3
        have : (m : ℝ) / Real.log m ^ 3 ≤ 8 * (N : ℝ) / Real.log N ^ 3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hN3 : 0 < Real.log N ^ 3 := by positivity
          have : Real.log N ^ 3 ≤ 8 * Real.log m ^ 3 := by nlinarith
          nlinarith
        linarith
    rw [habs]
    calc logConv_m111 m - (m : ℝ) / Real.log m ^ 2 ≤ C1 * ((m : ℝ) / Real.log m ^ 3) := hup
      _ ≤ C1 * (Real.sqrt N + 8 * (N : ℝ) / Real.log N ^ 3) :=
          mul_le_mul_of_nonneg_left hcube hC1.le
      _ ≤ _ := by linarith [mul_pos hB (by norm_num : (0 : ℝ) < 1000)]

set_option maxHeartbeats 1000000 in
/-- SPLIT burst 8 p3, PROVED, through truncSingular_small_m111. P0093 page 165
equation 8.1 and page 168 equations 10.6 and 10.7, the arithmetic left of the bookkeeping
once the GRH errors are summed: over the tuples of exponents x_i equal to nu i plus 1 with
N_1, N minus the sum of the 2 to the x_i, at least 4, the sum of the truncated singular
series at N_1 times the exact convolution of 6.3 at N_1 is the main term with N_1 over
ln squared N_1 up to epsilon times the scale. The proof reindexes the main term by
mainTermTrunc_reindex_m111, bounds the convolution error by logConv_dev_m111 from the
ported clean lab estimates of LogConvPort111, bounds the tuples with N_1 equal to 2 or 3
directly, and counts at most ln N over ln 2 to the k tuples. -/
theorem major_main_sum_m111 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |∑ ν ∈ (Fintype.piFinset fun _ : Fin k => Finset.range N).filter
            (fun ν => 4 + ∑ i, 2 ^ (ν i + 1) ≤ N),
          truncSingular_m111 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ (N - ∑ i, 2 ^ (ν i + 1)) *
            logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
        mainTermTrunc_m111 k N ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊| ≤ ε * scale111_up111 k N := by
  classical
  obtain ⟨K0, C1, hK0, hC1, hdev⟩ := logConv_dev_m111
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2p : 0 < Real.log 2 := by linarith
  set c : ℝ := Real.log 2 ^ 2 with hc
  have hcp : 0 < c := by positivity
  set ε0 : ℝ := ε * c / (32 * C1) with hε0
  have hε0p : 0 < ε0 := by positivity
  obtain ⟨C0, hC0, htS⟩ := truncSingular_small_m111 ε0 hε0p
  set A : ℝ := (ε0 + C0) * (K0 + C1) + 7 * (2 * ε0 + C0) with hA
  obtain ⟨Np, hp⟩ := polylog_small_m111 3 (c := 1 / 2) (A := A) (ε := ε * c / 4)
    (by norm_num) (by positivity)
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp (32 * C0 * C1 / (ε * c)))
  refine ⟨max (max Np L) 3, fun N hEv hN => ?_⟩
  have hNp' : Np < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNL : L < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNR : (3 : ℝ) < N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  set lN : ℝ := Real.log N with hlN
  have hlN1 : 1 ≤ lN := by
    rw [hlN, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlNbig : 32 * C0 * C1 / (ε * c) ≤ lN := by
    have h1 : Real.exp (32 * C0 * C1 / (ε * c)) < N := lt_trans hL (by exact_mod_cast hNL)
    rw [hlN, ← Real.log_exp (32 * C0 * C1 / (ε * c))]
    exact (Real.log_lt_log (Real.exp_pos _) h1).le
  set sN : ℝ := Real.sqrt N with hsN
  have hsN1 : 1 ≤ sN := by rw [hsN, Real.one_le_sqrt]; linarith
  have hsNsq : sN * sN = N := Real.mul_self_sqrt hNpos.le
  set Q : ℕ := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ with hQ
  set P : Finset (Fin k → ℕ) := Fintype.piFinset fun _ : Fin k => Finset.range N with hP
  set S : Finset (Fin k → ℕ) := P.filter (fun ν => 4 + ∑ i, 2 ^ (ν i + 1) ≤ N) with hS
  set S2 : Finset (Fin k → ℕ) := P.filter (fun ν => 2 + ∑ i, 2 ^ (ν i + 1) ≤ N) with hS2
  rw [mainTermTrunc_reindex_m111 k N Q hEv (by omega)]
  have hsub : S ⊆ S2 := by
    intro ν hν
    rw [hS, Finset.mem_filter] at hν
    rw [hS2, Finset.mem_filter]
    exact ⟨hν.1, by omega⟩
  -- cardinality
  have hcard : (S2.card : ℝ) ≤ (lN / Real.log 2) ^ k := by
    have hsubP : S2 ⊆ Fintype.piFinset fun _ : Fin k => Finset.range (Nat.log 2 N) := by
      intro ν hν
      rw [hS2, Finset.mem_filter] at hν
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      have h1 : 2 ^ (ν i + 1) ≤ ∑ j, 2 ^ (ν j + 1) :=
        Finset.single_le_sum (f := fun j => 2 ^ (ν j + 1)) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have h2 : ν i + 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by omega)
      omega
    have hc1 : S2.card ≤ (Nat.log 2 N) ^ k := by
      have := Finset.card_le_card hsubP
      simpa [Fintype.card_piFinset] using this
    have hlog : (Nat.log 2 N : ℝ) ≤ lN / Real.log 2 := by
      have := Real.natLog_le_logb N 2
      rwa [Real.logb] at this
    calc (S2.card : ℝ) ≤ ((Nat.log 2 N) ^ k : ℕ) := by exact_mod_cast hc1
      _ = (Nat.log 2 N : ℝ) ^ k := by push_cast; ring
      _ ≤ (lN / Real.log 2) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hlog k
  have hcardS : (S.card : ℝ) ≤ (lN / Real.log 2) ^ k :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) hcard
  have hcardD : ((S2 \ S).card : ℝ) ≤ (lN / Real.log 2) ^ k :=
    le_trans (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) hcard
  -- per term bounds
  set D : ℝ := K0 + C1 * (sN + 8 * (N : ℝ) / lN ^ 3) with hD
  set T : ℝ := ε0 * lN + C0 with hT
  have hD0 : 0 ≤ D := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hterm1 : ∀ ν ∈ S, |truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
      logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
      truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) /
        Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2| ≤ T * D := by
    intro ν hν
    rw [hS, Finset.mem_filter] at hν
    set m : ℕ := N - ∑ i, 2 ^ (ν i + 1) with hm
    have hm4 : 4 ≤ m := by omega
    have hmN : m ≤ N := by omega
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have ht := htS Q m (by omega)
    have hlm : Real.log m ≤ lN := Real.log_le_log (by linarith) (by exact_mod_cast hmN)
    have ht' : |truncSingular_m111 Q m| ≤ T := by
      rw [hT]; nlinarith [hε0p]
    have hd := hdev N m hm4 hmN
    rw [mul_div_assoc, ← mul_sub, abs_mul]
    exact mul_le_mul ht' hd (abs_nonneg _) hT0
  have hterm2 : ∀ ν ∈ S2 \ S, |truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
      ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) /
        Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2| ≤ (2 * ε0 + C0) * 7 := by
    intro ν hν
    rw [Finset.mem_sdiff, hS2, hS, Finset.mem_filter, Finset.mem_filter] at hν
    set m : ℕ := N - ∑ i, 2 ^ (ν i + 1) with hm
    have hm2 : 2 ≤ m := by omega
    have hm3 : m ≤ 3 := by
      by_contra h
      exact hν.2 ⟨hν.1.1, by omega⟩
    have hmR2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hmR3 : (m : ℝ) ≤ 3 := by exact_mod_cast hm3
    have ht := htS Q m (by omega)
    have hl3 : Real.log m ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by linarith); linarith
    have ht' : |truncSingular_m111 Q m| ≤ 2 * ε0 + C0 := by nlinarith [hε0p]
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hmR2
    have hl2' : (69 / 100 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hf : (m : ℝ) / Real.log m ^ 2 ≤ 7 := by
      rw [div_le_iff₀ (pow_pos (by linarith) 2)]
      have : (69 / 100 : ℝ) ^ 2 ≤ Real.log m ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      nlinarith
    rw [mul_div_assoc, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) / Real.log m ^ 2)]
    exact mul_le_mul ht' hf (by positivity) (by positivity)
  -- the sum
  rw [← Finset.sum_sdiff hsub]
  have hsplit : ∀ (a b : Finset (Fin k → ℕ)) (F G : (Fin k → ℕ) → ℝ),
      ∑ ν ∈ a, F ν - (∑ ν ∈ b, G ν + ∑ ν ∈ a, G ν) = ∑ ν ∈ a, (F ν - G ν) - ∑ ν ∈ b, G ν := by
    intro a b F G; rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  have hE1 := Finset.abs_sum_le_sum_abs (s := S) (fun ν => truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
      logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
      truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) /
        Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2)
  have hE1' := Finset.sum_le_card_nsmul S _ (T * D) hterm1
  have hE2 := Finset.abs_sum_le_sum_abs (s := S2 \ S) (fun ν => truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
      ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) / Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2)
  have hE2' := Finset.sum_le_card_nsmul (S2 \ S) _ ((2 * ε0 + C0) * 7) hterm2
  rw [nsmul_eq_mul] at hE1' hE2'
  set Pw : ℝ := (lN / Real.log 2) ^ k with hPw
  set R : ℝ := (lN / Real.log 2) ^ (k - 2) with hR
  have hR0 : 0 ≤ R := by positivity
  have hPwR : Pw = R * (lN ^ 2 / c) := by
    have hk2 : k = (k - 2) + 2 := by omega
    rw [hPw, hR, hc]
    conv_lhs => rw [hk2]
    rw [pow_add, div_pow lN (Real.log 2) 2]
  have hbound : (S.card : ℝ) * (T * D) + ((S2 \ S).card : ℝ) * ((2 * ε0 + C0) * 7) ≤
      Pw * (T * D + (2 * ε0 + C0) * 7) := by
    have h7 : 0 ≤ (2 * ε0 + C0) * 7 := by positivity
    calc (S.card : ℝ) * (T * D) + ((S2 \ S).card : ℝ) * ((2 * ε0 + C0) * 7)
        ≤ Pw * (T * D) + Pw * ((2 * ε0 + C0) * 7) :=
          add_le_add (mul_le_mul_of_nonneg_right hcardS (mul_nonneg hT0 hD0))
            (mul_le_mul_of_nonneg_right hcardD h7)
      _ = Pw * (T * D + (2 * ε0 + C0) * 7) := by ring
  -- the real inequality
  have hpoly := hp N hNp'
  have hsqrt : (N : ℝ) ^ (1 / 2 : ℝ) = sN := by rw [hsN, Real.sqrt_eq_rpow]
  rw [hsqrt] at hpoly
  have hkey : lN ^ 2 * (T * D + (2 * ε0 + C0) * 7) ≤ ε * c * N := by
    have hl3 : 0 < lN ^ 3 := by positivity
    have hpart1 : lN ^ 2 * T * (8 * C1 * (N : ℝ) / lN ^ 3) = 8 * C1 * ε0 * N + 8 * C1 * C0 * N / lN := by
      rw [hT]; field_simp
    have h8 : 8 * C1 * ε0 = ε * c / 4 := by rw [hε0]; field_simp; ring
    have h9 : 8 * C1 * C0 * N / lN ≤ ε * c / 4 * N := by
      rw [div_le_iff₀ (by linarith)]
      have h32 := (div_le_iff₀ (by positivity : 0 < ε * c)).mp hlNbig
      calc 8 * C1 * C0 * (N : ℝ) = (32 * C0 * C1) / 4 * N := by ring
        _ ≤ (lN * (ε * c)) / 4 * N := by gcongr
        _ = ε * c / 4 * N * lN := by ring
    have hTle : T ≤ (ε0 + C0) * lN := by
      have := mul_le_mul_of_nonneg_left hlN1 hC0.le
      rw [hT]; linarith
    have hKle : K0 + C1 * sN ≤ (K0 + C1) * sN := by
      have := mul_le_mul_of_nonneg_left hsN1 hK0.le
      linarith
    have hpart2 : lN ^ 2 * T * (K0 + C1 * sN) ≤ (ε0 + C0) * (K0 + C1) * (lN ^ 3 * sN) := by
      calc lN ^ 2 * T * (K0 + C1 * sN) ≤ lN ^ 2 * ((ε0 + C0) * lN) * ((K0 + C1) * sN) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hTle (by positivity)) hKle
              (by positivity) (by positivity)
        _ = (ε0 + C0) * (K0 + C1) * (lN ^ 3 * sN) := by ring
    have hpart3 : lN ^ 2 * ((2 * ε0 + C0) * 7) ≤ 7 * (2 * ε0 + C0) * (lN ^ 3 * sN) := by
      have h1 : lN ^ 2 ≤ lN ^ 3 := pow_le_pow_right₀ hlN1 (by norm_num)
      have h2 : lN ^ 3 ≤ lN ^ 3 * sN := le_mul_of_one_le_right (by positivity) hsN1
      have hX : 0 ≤ (2 * ε0 + C0) * 7 := by positivity
      calc lN ^ 2 * ((2 * ε0 + C0) * 7) ≤ (lN ^ 3 * sN) * ((2 * ε0 + C0) * 7) :=
            mul_le_mul_of_nonneg_right (h1.trans h2) hX
        _ = 7 * (2 * ε0 + C0) * (lN ^ 3 * sN) := by ring
    have hAp : A * lN ^ 3 * sN ≤ ε * c / 4 * N := by
      calc A * lN ^ 3 * sN ≤ ε * c / 4 * sN * sN :=
            mul_le_mul_of_nonneg_right hpoly (by linarith)
        _ = ε * c / 4 * N := by rw [mul_assoc, hsNsq]
    have hexpand : lN ^ 2 * (T * D + (2 * ε0 + C0) * 7) =
        lN ^ 2 * T * (K0 + C1 * sN) + lN ^ 2 * T * (8 * C1 * (N : ℝ) / lN ^ 3) +
          lN ^ 2 * ((2 * ε0 + C0) * 7) := by
      rw [hD]; ring
    rw [hexpand, hpart1, h8]
    have hAexp : A * lN ^ 3 * sN = (ε0 + C0) * (K0 + C1) * (lN ^ 3 * sN) +
        7 * (2 * ε0 + C0) * (lN ^ 3 * sN) := by rw [hA]; ring
    have hpos : 0 ≤ ε * c * N := by positivity
    linarith [hpart2, hpart3, hAp, hAexp, h9]
  have hscale : scale111_up111 k N = N * R := by rw [scale111_up111, hR]
  calc |∑ ν ∈ S, (truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
          logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
          truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) /
            Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2) -
        ∑ ν ∈ S2 \ S, truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
          ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) / Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2|
      ≤ |∑ ν ∈ S, (truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
          logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
          truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) /
            Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2)| +
        |∑ ν ∈ S2 \ S, truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
          ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) / Real.log ((N - ∑ i, 2 ^ (ν i + 1) : ℕ) : ℝ) ^ 2| :=
        abs_sub _ _
    _ ≤ (S.card : ℝ) * (T * D) + ((S2 \ S).card : ℝ) * ((2 * ε0 + C0) * 7) :=
        add_le_add (hE1.trans hE1') (hE2.trans hE2')
    _ ≤ Pw * (T * D + (2 * ε0 + C0) * 7) := hbound
    _ = R / c * (lN ^ 2 * (T * D + (2 * ε0 + C0) * 7)) := by rw [hPwR]; ring
    _ ≤ R / c * (ε * c * N) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ε * scale111_up111 k N := by rw [hscale]; field_simp

/-- P0093 page 165 equation 8.1, page 166 equation 8.2 and page 168 equation 10.7. Given
any function J of the residual that satisfies the local expansion of
major_local_expansion_m111 at every integer residual at most N, the tuple sum of 8.1,
e times the real part of the sum over tuples of the tuple weight times J at N_1, is the
main term with the truncated singular series at Q equal to N to the one tenth up to
epsilon times the scale. Proved, through major_main_sum_m111: e times the tuple
weight times e to the minus N_1 over N is 1, the main terms vanish for N_1 below 4, and
the errors sum to at most the tuple weight sum, at most ln N over ln 2 plus 2 to the k,
times the 8.2 error, which r1_absorb_split111 absorbs. -/
theorem major_bookkeeping_m111 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N → ∀ J : ℝ → ℂ,
      (∀ n : ℤ, n ≤ N →
        ‖J n - (((Real.exp (-(n : ℝ) / N) * truncSingular_m111 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ n.toNat *
            logConv_m111 n.toNat) : ℝ) : ℂ)‖ ≤
          B * N * Real.log N ^ 13 * ∑ q ∈ Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ)))) →
      |Real.exp 1 * (∑' ν : Fin k → ℕ,
          (((∏ i, Real.exp (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N)) : ℝ) : ℂ) *
            J ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ))).re -
        mainTermTrunc_m111 k N ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊| ≤ ε * scale111_up111 k N := by
  classical
  obtain ⟨ND, hD⟩ := major_main_sum_m111 k hk (ε / 2) (by positivity)
  obtain ⟨NR, hR⟩ := r1_absorb_split111 (Real.exp 1 * B) (by positivity) k hk (ε / 2)
    (by positivity)
  refine ⟨max (max ND NR) 1, fun N hEv hN J hJ => ?_⟩
  have hND : ND < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNR : NR < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := by have := le_max_right (max ND NR) 1; omega
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  set Q : ℕ := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ with hQ
  set E : ℝ := B * N * Real.log N ^ 13 * ∑ q ∈ Finset.Icc 1 Q,
    (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) with hE
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNR1
  have hE0 : 0 ≤ E := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun q _ => by positivity)
  have hEle : E ≤ B * N * Real.log N ^ 13 * (3 * (N : ℝ) ^ (-(3 / 140 : ℝ))) :=
    mul_le_mul_of_nonneg_left (error_sum_82_split111 N hN1) (by positivity)
  -- the tuple weights
  let w : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hw0 : ∀ m, 0 ≤ w m := fun m => (Real.exp_pos _).le
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have hw : Summable w := (damping_summable111_up111 N hN1).comp_injective hi
  let W : (Fin k → ℕ) → ℝ := fun ν => ∏ i, w (ν i)
  have hW0 : ∀ ν, 0 ≤ W ν := fun ν => Finset.prod_nonneg (fun i _ => hw0 _)
  have hWs : Summable W := summable_tuple_prod_real_split111 w hw0 hw k
  have hWsum : ∑' ν, W ν = (∑' m, w m) ^ k := by
    have h := hasSum_tuple_prod_split111 (fun m => (w m : ℂ))
      (hw.congr (fun m => by simp [Complex.norm_real, abs_of_nonneg (hw0 m)])) k
    have h2 := (Complex.hasSum_re h)
    simp only [← Complex.ofReal_prod, Complex.ofReal_re] at h2
    rw [h2.tsum_eq, ← Complex.ofReal_tsum, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hT0 : ∑' m, w m ≤ Real.log N / Real.log 2 + 2 := by
    have h := power_abs_le_log357_up111 N hN1 0
    have heq : powerFourier111_up111 N 0 = ((∑' m, w m : ℝ) : ℂ) := by
      unfold powerFourier111_up111
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro m
      simp [w]
    rw [heq, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hT00 : 0 ≤ ∑' m, w m := tsum_nonneg hw0
  -- residuals
  let s : (Fin k → ℕ) → ℕ := fun ν => ∑ i, 2 ^ (ν i + 1)
  let n : (Fin k → ℕ) → ℤ := fun ν => (N : ℤ) - (s ν : ℤ)
  have hcast : ∀ ν, ((n ν : ℤ) : ℝ) = (N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ) := by
    intro ν; simp [n, s]
  let M : (Fin k → ℕ) → ℝ := fun ν =>
    Real.exp (-((n ν : ℤ) : ℝ) / N) * truncSingular_m111 Q (n ν).toNat *
      logConv_m111 (n ν).toNat
  have hJν : ∀ ν, ‖J ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ)) - (M ν : ℂ)‖ ≤ E := by
    intro ν
    have h := hJ (n ν) (by simp only [n]; omega)
    rw [show J ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ)) = J ((n ν : ℤ) : ℝ) by rw [hcast]]
    exact h
  -- the support of the main terms
  let S : Finset (Fin k → ℕ) := (Fintype.piFinset fun _ : Fin k => Finset.range N).filter
    (fun ν => 4 + ∑ i, 2 ^ (ν i + 1) ≤ N)
  have hlogConv0 : ∀ m : ℕ, m < 4 → logConv_m111 m = 0 := by
    intro m hm
    unfold logConv_m111
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  have hout : ∀ ν, ν ∉ S → M ν = 0 := by
    intro ν hν
    have hlt : N < s ν + 4 := by
      by_contra hc
      push_neg at hc
      simp only [s] at hc
      apply hν
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_), by omega⟩
      have h1 : 2 ^ (ν i + 1) ≤ ∑ j, 2 ^ (ν j + 1) :=
        Finset.single_le_sum (f := fun j => 2 ^ (ν j + 1)) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have h2 : ν i < 2 ^ (ν i + 1) :=
        lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Finset.mem_range.mpr (by omega)
    have h4 : (n ν).toNat < 4 := by simp only [n]; omega
    simp only [M, hlogConv0 _ h4, mul_zero]
  have hin : ∀ ν ∈ S, Real.exp 1 * W ν * M ν =
      truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) := by
    intro ν hν
    have hs : 4 + s ν ≤ N := (Finset.mem_filter.mp hν).2
    have htn : (n ν).toNat = N - ∑ i, 2 ^ (ν i + 1) := by
      change ((N : ℤ) - (s ν : ℤ)).toNat = N - s ν
      omega
    have hW : W ν = Real.exp (∑ i, (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N)) := by
      simp only [W, w, Real.exp_sum]
    have hone : Real.exp 1 * W ν * Real.exp (-((n ν : ℤ) : ℝ) / N) = 1 := by
      rw [hW, ← Real.exp_add, ← Real.exp_add, hcast]
      have : (1 : ℝ) + ∑ i, (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N) +
          -((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ)) / N = 0 := by
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
        field_simp
        ring
      rw [this, Real.exp_zero]
    simp only [M, htn]
    calc Real.exp 1 * W ν * (Real.exp (-((n ν : ℤ) : ℝ) / N) *
          truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)))
        = (Real.exp 1 * W ν * Real.exp (-((n ν : ℤ) : ℝ) / N)) *
          (truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) *
            logConv_m111 (N - ∑ i, 2 ^ (ν i + 1))) := by ring
      _ = _ := by rw [hone, one_mul]
  -- split the tuple sum into errors and main terms
  let a : (Fin k → ℕ) → ℂ := fun ν => (W ν : ℂ) *
    (J ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ)) - (M ν : ℂ))
  let b : (Fin k → ℕ) → ℂ := fun ν => (W ν : ℂ) * (M ν : ℂ)
  have ha_norm : ∀ ν, ‖a ν‖ ≤ W ν * E := by
    intro ν
    simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 ν)]
    exact mul_le_mul_of_nonneg_left (hJν ν) (hW0 ν)
  have hWEs : Summable (fun ν => W ν * E) := hWs.mul_right E
  have ha : Summable a := Summable.of_norm_bounded hWEs ha_norm
  have hb0 : ∀ ν ∉ S, b ν = 0 := fun ν hν => by simp [b, hout ν hν]
  have hb : Summable b := summable_of_ne_finset_zero hb0
  have hsplit : (∑' ν : Fin k → ℕ, (((∏ i, Real.exp (-((2 ^ (ν i + 1) : ℕ) : ℝ) / N)) : ℝ) : ℂ) *
      J ((N : ℝ) - ∑ i, ((2 ^ (ν i + 1) : ℕ) : ℝ))) = (∑' ν, a ν) + ∑ ν ∈ S, b ν := by
    have hbS : ∑' ν, b ν = ∑ ν ∈ S, b ν := tsum_eq_sum (fun ν hν => hb0 ν hν)
    rw [← hbS, ← ha.tsum_add hb]
    apply tsum_congr
    intro ν
    simp only [a, b, W, w]
    ring
  have hbre : Real.exp 1 * (∑ ν ∈ S, b ν).re = ∑ ν ∈ S,
      truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) := by
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν hν
    rw [← hin ν hν]
    simp only [b, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have haE : ‖∑' ν, a ν‖ ≤ (Real.log N / Real.log 2 + 2) ^ k * E := by
    calc ‖∑' ν, a ν‖ ≤ ∑' ν, W ν * E :=
          tsum_of_norm_bounded hWEs.hasSum ha_norm
      _ = (∑' ν, W ν) * E := tsum_mul_right
      _ = (∑' m, w m) ^ k * E := by rw [hWsum]
      _ ≤ (Real.log N / Real.log 2 + 2) ^ k * E :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT00 hT0 k) hE0
  have hR' := hR N hNR
  have hD' := hD N hEv hND
  have hbase0 : 0 ≤ (Real.log N / Real.log 2 + 2) ^ k := by positivity
  have herr : Real.exp 1 * ‖∑' ν, a ν‖ ≤ ε / 2 * scale111_up111 k N := by
    calc Real.exp 1 * ‖∑' ν, a ν‖
        ≤ Real.exp 1 * ((Real.log N / Real.log 2 + 2) ^ k *
            (B * N * Real.log N ^ 13 * (3 * (N : ℝ) ^ (-(3 / 140 : ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
          exact haE.trans (mul_le_mul_of_nonneg_left hEle hbase0)
      _ = Real.exp 1 * B * (Real.log N / Real.log 2 + 2) ^ k * N * Real.log N ^ 13 *
            (3 * (N : ℝ) ^ (-(3 / 140 : ℝ))) := by ring
      _ ≤ ε / 2 * scale111_up111 k N := hR'
  rw [hsplit, Complex.add_re, mul_add, hbre]
  have hre : |Real.exp 1 * (∑' ν, a ν).re| ≤ Real.exp 1 * ‖∑' ν, a ν‖ := by
    rw [abs_mul, abs_of_pos (Real.exp_pos 1)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos 1).le
  calc |Real.exp 1 * (∑' ν, a ν).re + ∑ ν ∈ S,
        truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
        mainTermTrunc_m111 k N Q|
      ≤ |Real.exp 1 * (∑' ν, a ν).re| + |∑ ν ∈ S,
        truncSingular_m111 Q (N - ∑ i, 2 ^ (ν i + 1)) * logConv_m111 (N - ∑ i, 2 ^ (ν i + 1)) -
        mainTermTrunc_m111 k N Q| := by
        rw [add_sub_assoc]; exact abs_add_le _ _
    _ ≤ ε / 2 * scale111_up111 k N + ε / 2 * scale111_up111 k N := add_le_add (hre.trans herr) hD'
    _ = ε * scale111_up111 k N := by ring

end LeanLab.Linnik1951
