module

public import Mathlib
public import LeanLab.ExceptionalSet.State1539Data264

/-!
Unit U-1539, run 20261026T0403Z-9802, DECOMP job for P0082, track T1.
J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, §8, p. 370-377: the proof of Theorem 2.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

CODEX task140 completion. All 25 original LEAF bodies are proved with their statements unchanged.
The derivative inputs are exported together as `section8_derivative_inputs` without a cited input.
Theorem 2 remains CONDITIONAL ON the cited Karacuba Lemma 10.
AI wrote the task140 proof bodies using GPT-6 Codex.

The provable structure of §8 is split into LEAF lemmas and ASSEMBLIES; in this copy every leaf
is proved. Each assembly has a real proof of its own and is CONDITIONAL ON the leaves it uses, and on the
State1539 statements it takes as hypotheses.

Chain:
* Lemma 11 from the leaves on `Q_{s,t}` and the one-step derivative, `lemma11_of_leaves`.
* Lemma 12 from the base case (44) and two induction steps, `lemma12_of_leaves`.
* Lemma 13 from Lemmas 11, 12 and the geometric tail bound, `lemma13_of_leaves`.
* Lemma 14 from Lemma 13 and two elementary leaves, `lemma14_of_leaves`.
* Lemma 15 from a Cauchy estimate and a bound on the circle, `lemma15_of_leaves`.
* Lemma 16 (a), (b) from Lemmas 15, 14 and three algebra leaves.
* Theorem 2 from Lemma 10, which is CITED, Lemma 16 and nine leaves on the parameters,
  `theorem2_of_leaves`.

Two slips of §8 are repaired in the leaves, see STATEMENTS.md, QUESTIONs:
the lower end of display (56), p. 377, lacks a `+ log 2 / log N` that display (53) needs;
and the choice `C < γ(1 - θ)` on p. 377 must read `1 + C < γ(1 - θ)` for `s ≤ γ (log N)^{γ-1}`.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial Filter Topology
open Metric
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Auxiliary definitions -/

/-- One summand of Lemma 11: `F(x) x^{-s} (log x)^{-t} Q_{s,t}(ξ(x))`. -/
noncomputable def piece (γ : ℝ) (s t : ℕ) (x : ℝ) : ℝ :=
  F γ x / x ^ s * ((Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x))

/-- The right side of Lemma 11, summed to `t = s` so that it also covers `s = 0`. -/
noncomputable def term (γ : ℝ) (s : ℕ) (x : ℝ) : ℝ :=
  ∑ t ∈ Finset.range (s + 1), piece γ s t x

/-- The derivative of `piece γ s t`, computed on p. 372 from (47). -/
noncomputable def pieceD (γ : ℝ) (s t : ℕ) (x : ℝ) : ℝ :=
  F γ x / x ^ (s + 1) *
    ((Real.log x ^ t)⁻¹ * ((xi γ x - s) * (Q γ s t).eval (xi γ x))
      - (t : ℝ) * (Real.log x ^ (t + 1))⁻¹ * (Q γ s t).eval (xi γ x)
      + (Real.log x ^ (t + 1))⁻¹ * ((γ - 1) * xi γ x * (derivative (Q γ s t)).eval (xi γ x)))

/-- The statement (50) for one pair `s, t`, all `j`. -/
def P12 (γ : ℝ) (s t : ℕ) : Prop :=
  ∀ j : ℕ, t + j ≤ s → ∀ ξ : ℝ, (s : ℝ) ≤ ξ →
    |(derivative^[j] (Q γ s t)).eval ξ| ≤ (s : ℝ) ^ (2 * t + j) * (q (s - t - j)).eval ξ

/-- The holomorphic continuation `F(z) = exp((log z)^γ)` used in the proof of Lemma 15. -/
noncomputable def Fc (γ : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.log z ^ (γ : ℂ))

/-- `k = [9 (log N)^{γ-1}] + 1`, p. 377. -/
noncomputable def kN (γ N : ℝ) : ℕ := ⌊9 * Real.log N ^ (γ - 1)⌋₊ + 1

/-- `δ = (1/20)(1-c)(1/(1-θ) - 1/(1-θ/2))`, p. 377. -/
noncomputable def deltaK (c θ : ℝ) : ℝ := 1 / 20 * (1 - c) * (1 / (1 - θ) - 1 / (1 - θ / 2))

/-- Lower end of display (56), p. 377, with the `log 2 / log N` that (53) needs. -/
noncomputable def lowerB (γ θ A N : ℝ) : ℝ :=
  ((Real.log 2 + Real.log (3 * N) ^ γ) / Real.log N - A) / (1 - θ / 2 - Real.log 2 / Real.log N)

/-- Upper end of display (56), p. 377. -/
noncomputable def upperB (γ θ A N : ℝ) : ℝ :=
  (Real.log N ^ (γ - 1) - A - Real.log 2 / Real.log N) / (1 - θ)

/-- The set `S` of p. 377: the `s` in `[1, k-1]` satisfying (56). -/
noncomputable def Sset (γ θ A N : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (kN γ N - 1)).filter (fun s : ℕ => lowerB γ θ A N ≤ s ∧ (s : ℝ) ≤ upperB γ θ A N)

/-! ### Proved helpers -/

theorem Q_s0 (γ : ℝ) : ∀ s : ℕ, Q γ s 0 = q s
  | 0 => by simp [Q, q]
  | s + 1 => by
      rw [Q_succ_zero, Q_s0 γ s]
      simp only [q]
      rw [descPochhammer_succ_right, mul_comm]
      simp

theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : (2 * Real.pi * Complex.I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem eC_neg (x : ℝ) : eC (-x) = (starRingEnd ℂ) (eC x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

theorem norm_expSumF_neg (γ α : ℝ) (N : ℕ) : ‖expSumF γ (-α) N‖ = ‖expSumF γ α N‖ := by
  have : expSumF γ (-α) N = (starRingEnd ℂ) (expSumF γ α N) := by
    unfold expSumF
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← eC_neg]; congr 1; ring
  rw [this, Complex.norm_conj]

theorem norm_expSumF_le (γ α : ℝ) (N : ℕ) : ‖expSumF γ α N‖ ≤ N + 1 := by
  unfold expSumF
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_eC, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [show 2 * N + 1 - N = N + 1 by omega]
  norm_num

theorem norm_Icc_le (γ α : ℝ) (N : ℕ) :
    ‖expSumF γ α N‖ ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), eC ((fun x => α * F γ x) n)‖ + 1 := by
  unfold expSumF
  rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
  refine (norm_add_le _ _).trans ?_
  rw [norm_eC, add_comm]

theorem iteratedDeriv_const_mul' (a : ℝ) (f : ℝ → ℝ) :
    ∀ n : ℕ, iteratedDeriv n (fun x => a * f x) = fun x => a * iteratedDeriv n f x
  | 0 => by simp
  | n + 1 => by
      rw [iteratedDeriv_succ, iteratedDeriv_const_mul' a f n, iteratedDeriv_succ]
      exact deriv_const_mul_field' a

theorem Q_iter_derivative_recurrence (γ : ℝ) (s t j : ℕ) (ht : 1 ≤ t) :
    derivative^[j] (Q γ (s + 1) t) =
      (X - C (s : ℝ)) * derivative^[j] (Q γ s t) +
      C (j : ℝ) * derivative^[j - 1] (Q γ s t) +
      C (γ - 1) * X * derivative^[j + 1] (Q γ s (t - 1)) +
      (C (γ - 1) * C (j : ℝ) - C ((t : ℝ) - 1)) * derivative^[j] (Q γ s (t - 1)) := by
  have hsub (p r : ℝ[X]) : derivative^[j] (p - r) = derivative^[j] p - derivative^[j] r :=
    iterate_derivative_sub
  have hadd (p r : ℝ[X]) : derivative^[j] (p + r) = derivative^[j] p + derivative^[j] r :=
    by simp_rw [← Module.End.pow_apply, map_add]
  have hX (p : ℝ[X]) : derivative^[j] (X * p) = X * derivative^[j] p + C (j : ℝ) * derivative^[j - 1] p := by
    rw [mul_comm X p, iterate_derivative_mul_X]
    simp only [nsmul_eq_mul, ← C_eq_natCast]
    ring
  rw [Q]
  simp only [show t ≠ 0 by omega, ↓reduceIte, hadd, hsub, sub_mul, hX, iterate_derivative_C_mul,
    mul_assoc, iterate_derivative_C_mul]
  have he : derivative^[j] (derivative (Q γ s (t - 1))) = derivative^[j + 1] (Q γ s (t - 1)) := by
    rw [Function.iterate_succ_apply]
  rw [he]
  cases j with
  | zero => simp <;> ring
  | succ j =>
    simp only [Nat.add_sub_cancel]
    rw [← Function.iterate_succ_apply]
    ring

theorem lemma12_coefficient_bound (s t j : ℕ) (ht : 1 ≤ t) (hs : t + 1 ≤ s) (hj : t + j ≤ s + 1) :
    (s : ℝ) ^ (2 * t + j) + (j + 1 : ℝ) * (s : ℝ) ^ (2 * t + j - 1) +
      (j + t - 1 : ℝ) * (s : ℝ) ^ (2 * t + j - 2) ≤ ((s + 1 : ℕ) : ℝ) ^ (2 * t + j) := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hpow : (s : ℝ) ^ (2 * t + j - 1) = s * (s : ℝ) ^ (2 * t + j - 2) := by
    rw [show 2 * t + j - 1 = (2 * t + j - 2) + 1 by omega, pow_succ]
    ring
  have hcoef : (j + t - 1 : ℝ) ≤ (2 * t - 1 : ℝ) * s := by
    have hjs : (j : ℝ) + t - 1 ≤ s := by
      have h : (j : ℝ) + t ≤ s + 1 := by exact_mod_cast (show j + t ≤ s + 1 by omega)
      linarith
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hs0 (2 * t + j - 2))
  have hb := pow_add_mul_le_add_pow (a := (s : ℝ)) (b := 1) hs0 (by positivity) (2 * t + j)
  push_cast at hb ⊢
  rw [hpow] at hb ⊢
  nlinarith

theorem card_nat_interval_lower_bound (a b : ℝ) (K : ℕ) (ha : 1 ≤ a) (hb : b ≤ K) :
    b - a - 1 ≤ (((Finset.Icc 1 K).filter (fun n : ℕ => a ≤ n ∧ (n : ℝ) ≤ b)).card : ℝ) := by
  classical
  by_cases hwidth : b ≤ a + 1
  · have hnonneg := Nat.cast_nonneg (((Finset.Icc 1 K).filter (fun n : ℕ => a ≤ n ∧ (n : ℝ) ≤ b)).card) (α := ℝ)
    linarith
  have hb0 : 0 ≤ b := by linarith
  have hfloor := Nat.lt_floor_add_one b
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ a by linarith)
  have hfa : a ≤ (⌊b⌋₊ : ℝ) := by push_cast at hfloor; linarith
  have hcf : ⌈a⌉₊ ≤ ⌊b⌋₊ := Nat.ceil_le.mpr hfa
  have hsub : Finset.Icc ⌈a⌉₊ ⌊b⌋₊ ⊆ (Finset.Icc 1 K).filter (fun n : ℕ => a ≤ n ∧ (n : ℝ) ≤ b) := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hna : a ≤ (n : ℝ) := (Nat.le_ceil a).trans (by exact_mod_cast hnlo)
    have hnb : (n : ℝ) ≤ b := (show (n : ℝ) ≤ (⌊b⌋₊ : ℝ) by exact_mod_cast hnhi).trans (Nat.floor_le hb0)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hna, hnb⟩
    · exact_mod_cast (ha.trans hna)
    · exact_mod_cast (hnb.trans hb)
  have hcard := Finset.card_le_card hsub
  have hlen : ((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) = (⌊b⌋₊ : ℝ) + 1 - ⌈a⌉₊ := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hcast : ((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤
      (((Finset.Icc 1 K).filter (fun n : ℕ => a ≤ n ∧ (n : ℝ) ≤ b)).card : ℝ) := by exact_mod_cast hcard
  rw [hlen] at hcast
  push_cast at hfloor hceil
  linarith

theorem log_scale_rpow_ratio_tendsto (γ a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℝ => (Real.log (a * N) ^ γ / Real.log N) / Real.log N ^ (γ - 1)) atTop (𝓝 1) := by
  have hr : Tendsto (fun N : ℝ => Real.log (a * N) / Real.log N) atTop (𝓝 1) := by
    have ht : Tendsto (fun N : ℝ => Real.log a / Real.log N + 1) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add_const 1
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hL : 0 < Real.log N := Real.log_pos hN
    rw [Real.log_mul ha.ne' (by linarith), add_div, div_self hL.ne']
  have hp : Tendsto (fun N : ℝ => (Real.log (a * N) / Real.log N) ^ γ) atTop (𝓝 1) := by
    simpa using hr.rpow_const (p := γ) (Or.inl one_ne_zero)
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (max 2 (1 / a))] with N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have haN : 1 ≤ a * N := by
    have := (le_max_right (2 : ℝ) (1 / a)).trans hN
    exact (div_le_iff₀ ha).mp this |>.trans_eq (by ring)
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  rw [Real.div_rpow (Real.log_nonneg haN) hL.le, Real.rpow_sub_one hL.ne']
  field_simp

theorem q_iter_deriv_le_descFactorial (s t : ℕ) (hts : t ≤ s) (x : ℝ) (hx : (s : ℝ) ≤ x) :
    0 ≤ (derivative^[t] (q s)).eval x ∧ (derivative^[t] (q s)).eval x ≤ (s.descFactorial t : ℝ) * (q (s - t)).eval x := by
  have hd (n u : ℕ) : derivative^[u + 1] (q (n + 1)) =
      derivative^[u + 1] (q n) * (X - C (n : ℝ)) + C ((u + 1 : ℕ) : ℝ) * derivative^[u] (q n) := by
    simp only [q, descPochhammer_succ_right, mul_sub, iterate_derivative_sub,
      iterate_derivative_mul_X, Nat.add_sub_cancel]
    simp only [← C_eq_natCast]
    rw [mul_comm (descPochhammer ℝ n) (C (n : ℝ)), iterate_derivative_C_mul]
    simp only [nsmul_eq_mul, ← C_eq_natCast]
    ring
  induction s generalizing t with
  | zero =>
    have : t = 0 := by omega
    subst t
    simp [q]
  | succ n ih =>
    cases t with
    | zero =>
      simp only [Function.iterate_zero_apply, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero, one_mul, le_refl, and_true]
      exact descPochhammer_nonneg (by norm_num only [Nat.cast_add, Nat.cast_one] at hx ⊢; linarith)
    | succ u =>
      have hxn : (n : ℝ) ≤ x := by push_cast at hx; linarith
      have hxu : 0 ≤ x - n := by linarith
      have hp := ih u (by omega) hxn
      rw [hd, eval_add, eval_mul, eval_mul, eval_sub, eval_X, eval_C, eval_C]
      by_cases htu : u + 1 ≤ n
      · have hc := ih (u + 1) htu hxn
        have hq0 : 0 ≤ (q (n + 1 - (u + 1))).eval x := descPochhammer_nonneg (by
          have : ((n + 1 - (u + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - (u + 1) ≤ n)
          linarith)
        have hq : (q (n - (u + 1))).eval x * (x - n) ≤ (q (n + 1 - (u + 1))).eval x := by
          have he : n + 1 - (u + 1) = n - (u + 1) + 1 := by omega
          rw [he]
          simp only [q, descPochhammer_succ_eval]
          have hq' : 0 ≤ (q (n - (u + 1))).eval x := descPochhammer_nonneg (by
            have : ((n - (u + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (u + 1)
            linarith)
          have hcast : ((n - (u + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (u + 1)
          change 0 ≤ (descPochhammer ℝ (n - (u + 1))).eval x at hq'
          nlinarith
        have hcoeff : (n.descFactorial (u + 1) : ℝ) + ((u + 1 : ℕ) : ℝ) * (n.descFactorial u : ℝ) =
            ((n + 1).descFactorial (u + 1) : ℝ) := by
          rw [Nat.descFactorial_succ, Nat.succ_descFactorial_succ]
          push_cast
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        have hprev : n - u = n + 1 - (u + 1) := by omega
        rw [hprev] at hp
        refine ⟨add_nonneg (mul_nonneg hc.1 hxu) (mul_nonneg (by positivity) hp.1), ?_⟩
        calc (derivative^[u + 1] (q n)).eval x * (x - n) + ((u + 1 : ℕ) : ℝ) * (derivative^[u] (q n)).eval x
            ≤ ((n.descFactorial (u + 1) : ℝ) * (q (n - (u + 1))).eval x) * (x - n) +
              ((u + 1 : ℕ) : ℝ) * ((n.descFactorial u : ℝ) * (q (n + 1 - (u + 1))).eval x) := by gcongr <;> first | exact hc.2 | exact hp.2
          _ ≤ ((n.descFactorial (u + 1) : ℝ) + ((u + 1 : ℕ) : ℝ) * (n.descFactorial u : ℝ)) * (q (n + 1 - (u + 1))).eval x := by
            have hm := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (n.descFactorial (u + 1) : ℝ))
            nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff.le hq0
      · have hu : u = n := by omega
        subst u
        have hz : derivative^[n + 1] (q n) = 0 := iterate_derivative_eq_zero (by simp [q, descPochhammer_natDegree])
        rw [hz]
        simp only [eval_zero, zero_mul, zero_add, Nat.sub_self, q, descPochhammer_zero, eval_one, mul_one] at hp ⊢
        refine ⟨mul_nonneg (by positivity) hp.1, ?_⟩
        calc ((n + 1 : ℕ) : ℝ) * (derivative^[n] (descPochhammer ℝ n)).eval x
            ≤ ((n + 1 : ℕ) : ℝ) * (n.descFactorial n : ℝ) := mul_le_mul_of_nonneg_left hp.2 (by positivity)
          _ = _ := by rw [Nat.succ_descFactorial_succ, Nat.cast_mul]

/-! ### Leaves for Lemma 11, p. 372 -/

/-- LEAF. Unit U-1539. For `s ≥ 1` and `t ≥ s`, `Q_{s,t} = 0`: Lemma 11 on p. 372 sums only
`t ≤ s - 1`; follows from the recursion (46) by induction on `s`. -/
theorem leaf_Q_vanish (γ : ℝ) (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) : Q γ s t = 0 := by
  induction s generalizing t with
  | zero => omega
  | succ s ih =>
    by_cases hs0 : s = 0
    · subst s
      cases t with
      | zero => omega
      | succ t => cases t <;> simp [Q]
    · have hs1 : 1 ≤ s := by omega
      have ht0 : t ≠ 0 := by omega
      simp [Q, ht0, ih t hs1 (by omega), ih (t - 1) hs1 (by omega)]

/-- LEAF. Unit U-1539. The second identity of display (45), p. 372: for `s ≥ 1`,
`Q_{s+1,s}(ξ) = q_s(γ-1) ξ`, by induction from (49) as on p. 373. -/
theorem leaf_Q_top (γ : ℝ) (s : ℕ) (hs : 1 ≤ s) :
    Q γ (s + 1) s = C ((q s).eval (γ - 1)) * X := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hs0 : s = 0
    · subst s
      simp [Q, q, descPochhammer_succ_right]
    · have hs1 : 1 ≤ s := by omega
      rw [Q, leaf_Q_vanish γ (s + 1) (s + 1) (by omega) le_rfl]
      simp only [mul_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, zero_add, ih hs1, derivative_mul, derivative_C,
        zero_mul, derivative_X, mul_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      simp only [q, descPochhammer_succ_eval]
      simp only [map_mul, map_sub]
      push_cast
      ring

/-- LEAF. Unit U-1539. Lemma 11, p. 372: for `s ≥ 1` and `t ≤ s - 1`, `Q_{s,t}` has degree at
most `s - t` and no constant term; induction on `s` with (46) and (48). -/
theorem leaf_Q_degree (γ : ℝ) (s t : ℕ) (hs : 1 ≤ s) (ht : t < s) :
    (Q γ s t).natDegree ≤ s - t ∧ (Q γ s t).coeff 0 = 0 := by
  induction s generalizing t with
  | zero => omega
  | succ s ih =>
    by_cases hs0 : s = 0
    · subst s
      have : t = 0 := by omega
      subst t
      simp [Q]
    have hs1 : 1 ≤ s := by omega
    by_cases ht0 : t = 0
    · subst t
      rw [Q_s0]
      simp [q, coeff_zero_eq_eval_zero, descPochhammer_eval_zero]
    have hprev := ih (t - 1) hs1 (by omega)
    have hcur : (Q γ s t).natDegree ≤ s - t ∧ (Q γ s t).coeff 0 = 0 := by
      by_cases ht' : t < s
      · exact ih t hs1 ht'
      · rw [leaf_Q_vanish γ s t hs1 (by omega)]
        simp
    rw [Q]
    simp only [ht0, ↓reduceIte]
    constructor
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · have hm := natDegree_mul_le (p := X - C (s : ℝ)) (q := Q γ s t)
        have hx := natDegree_X_sub_C_le (s : ℝ)
        omega
      · apply (natDegree_sub_le _ _).trans
        apply max_le
        · have hd := natDegree_derivative_le (Q γ s (t - 1))
          have hm := natDegree_mul_le (p := C (γ - 1) * X) (q := derivative (Q γ s (t - 1)))
          have hc : (C (γ - 1) * X).natDegree ≤ 1 := by
            exact (natDegree_C_mul_le _ _).trans (by simp)
          omega
        · exact (natDegree_C_mul_le _ _).trans (by omega)
    · simp only [coeff_zero_eq_eval_zero] at hcur hprev ⊢
      simp [hcur.2, hprev.2]

/-- LEAF. Unit U-1539. The derivative of one summand, p. 372, from (47): for `γ > 0`, `x > 1`,
using `F' = F ξ / x` and `ξ' = (γ-1) ξ / (x log x)`. -/
theorem leaf_piece_hasDerivAt (γ : ℝ) (hγ : 0 < γ) (s t : ℕ) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (piece γ s t) (pieceD γ s t x) x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hlog := Real.hasDerivAt_log hx0.ne'
  have hF : HasDerivAt (F γ) (F γ x * xi γ x / x) x := by
    convert (hlog.rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
    · rfl
    · dsimp [F, xi]; ring
  have hxi : HasDerivAt (xi γ) ((γ - 1) * xi γ x / (x * Real.log x)) x := by
    convert (hlog.rpow_const (p := γ - 1) (Or.inl hL.ne')).const_mul γ using 1
    · rfl
    · dsimp [xi]
      rw [Real.rpow_sub_one hL.ne' (γ - 1)]
      ring
  have hq := ((Q γ s t).hasDerivAt (xi γ x)).comp x hxi
  have h := (hF.div ((hasDerivAt_id x).pow s) (pow_ne_zero s hx0.ne')).mul
    (((hlog.pow t).inv (pow_ne_zero t hL.ne')).mul hq)
  change HasDerivAt (piece γ s t) _ x at h
  convert h using 1
  dsimp [pieceD]
  cases s with
  | zero =>
    cases t with
    | zero => simp [Q, xi] <;> ring
    | succ t => simp [Q]
  | succ s =>
    cases t with
    | zero =>
      simp only [pow_zero, pow_one, inv_one, Nat.cast_zero, zero_mul, zero_div,
        mul_zero, zero_sub, sub_zero, zero_add, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        pow_succ]
      field_simp
      ring
    | succ t =>
      simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- LEAF. Unit U-1539. Regrouping by powers of `log x`, the last display of p. 372 with the
recursion (46), (48), (49): the derivatives of the summands for `s` sum to the formula for
`s + 1`. Uses `Q_{s,s} = 0` for `s ≥ 1`. -/
theorem leaf_regroup (γ : ℝ) (s : ℕ) (x : ℝ) (hx : 1 < x) :
    ∑ t ∈ Finset.range (s + 1), pieceD γ s t x = term γ (s + 1) x := by
  let a : ℕ → ℝ := fun t => F γ x / x ^ (s + 1) *
    (Real.log x ^ t)⁻¹ * ((xi γ x - s) * (Q γ s t).eval (xi γ x))
  let b : ℕ → ℝ := fun t => F γ x / x ^ (s + 1) * (Real.log x ^ (t + 1))⁻¹ *
    ((γ - 1) * xi γ x * (derivative (Q γ s t)).eval (xi γ x) - t * (Q γ s t).eval (xi γ x))
  have hd (t : ℕ) : pieceD γ s t x = a t + b t := by dsimp [pieceD, a, b]; ring
  have h0 : piece γ (s + 1) 0 x = a 0 := by simp [piece, a, Q_succ_zero]
  have hp (t : ℕ) : piece γ (s + 1) (t + 1) x = a (t + 1) + b t := by
    simp [piece, a, b, Q, Nat.cast_add, Nat.cast_one]
    ring
  have hz : Q γ s (s + 1) = 0 := by
    cases s with
    | zero => simp [Q]
    | succ s => exact leaf_Q_vanish γ (s + 1) (s + 1 + 1) (by omega) (by omega)
  have ha : a (s + 1) = 0 := by simp [a, hz]
  have hsum : (∑ t ∈ Finset.range (s + 1), a (t + 1)) + a 0 = ∑ t ∈ Finset.range (s + 1), a t := by
    have h := Finset.sum_range_succ' a (s + 1)
    have h' := Finset.sum_range_succ a (s + 1)
    rw [ha, add_zero] at h'
    linarith
  simp_rw [hd]
  unfold term
  rw [Finset.sum_range_succ' (fun t => piece γ (s + 1) t x), h0]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

/-! ### Assemblies for Lemma 11 -/

/-- ASSEMBLY, CONDITIONAL ON `leaf_piece_hasDerivAt` and `leaf_regroup`. -/
theorem term_hasDerivAt (γ : ℝ) (hγ : 0 < γ) (s : ℕ) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (term γ s) (term γ (s + 1) x) x := by
  have h := HasDerivAt.sum (u := Finset.range (s + 1)) (A := fun t => piece γ s t)
    (A' := fun t => pieceD γ s t x) (x := x)
    (fun t _ => leaf_piece_hasDerivAt γ hγ s t x hx)
  rw [leaf_regroup γ s x hx] at h
  have e : (∑ i ∈ Finset.range (s + 1), piece γ s i) = term γ s := by
    funext y; simp [term, Finset.sum_apply]
  rw [e] at h
  exact h

/-- ASSEMBLY, CONDITIONAL ON the Lemma 11 leaves: `F^{(s)} = term γ s` on `x > 1`. -/
theorem iteratedDeriv_eq_term (γ : ℝ) (hγ : 0 < γ) :
    ∀ s : ℕ, ∀ x : ℝ, 1 < x → iteratedDeriv s (F γ) x = term γ s x := by
  intro s
  induction s with
  | zero => intro x _; simp [term, piece, Q]
  | succ s ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv s (F γ) =ᶠ[𝓝 x] term γ s := by
        filter_upwards [Ioi_mem_nhds hx] with y hy using ih y hy
      rw [heq.deriv_eq]
      exact (term_hasDerivAt γ hγ s x hx).deriv

/-- ASSEMBLY. Lemma 11, CONDITIONAL ON `leaf_Q_vanish`, `leaf_Q_top`, `leaf_Q_degree`,
`leaf_piece_hasDerivAt`, `leaf_regroup`. -/
theorem lemma11_of_leaves : Lemma11 := by
  intro γ hγ s hs
  refine ⟨fun t ht => leaf_Q_degree γ s t hs ht, Q_s0 γ s, leaf_Q_top γ s hs, fun x hx => ?_⟩
  rw [iteratedDeriv_eq_term γ hγ s x hx]
  unfold term piece
  rw [Finset.sum_range_succ, leaf_Q_vanish γ s s hs le_rfl, Finset.mul_sum]
  simp

/-! ### Leaves for Lemma 12, p. 373-374 -/

/-- LEAF. Unit U-1539. Display (44), p. 371: for `t ≤ s` and `x ≥ s`,
`0 ≤ q_s^{(t)}(x) ≤ s^t q_{s-t}(x)`, from (43). -/
theorem leaf_q_iter_deriv (s t : ℕ) (hts : t ≤ s) (x : ℝ) (hx : (s : ℝ) ≤ x) :
    0 ≤ (derivative^[t] (q s)).eval x ∧ (derivative^[t] (q s)).eval x ≤ (s : ℝ) ^ t * (q (s - t)).eval x := by
  obtain ⟨h0, hle⟩ := q_iter_deriv_le_descFactorial s t hts x hx
  refine ⟨h0, hle.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow s t)
  exact descPochhammer_nonneg (by
    have h : ((s - t : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s t
    linarith)

/-- LEAF. Unit U-1539. The case `s = t + 1` of (50), p. 373, with `s^{2t+j}`: from
`Q_{t+1,t}(ξ) = q_t(γ-1) ξ` and `|q_t(γ-1)| ≤ t!` for `1 < γ < 2`. -/
theorem leaf12_diag (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 2) (t : ℕ) (ht : 1 ≤ t) : P12 γ (t + 1) t := by
  have habs : ∀ n : ℕ, |(q n).eval (γ - 1)| ≤ (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => simp [q]
    | succ n ih =>
      simp only [q, descPochhammer_succ_eval, abs_mul] at ih ⊢
      have hfactor : |γ - 1 - n| ≤ (n : ℝ) + 1 := by
        apply abs_le.mpr
        constructor <;> have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n <;> linarith
      calc |(descPochhammer ℝ n).eval (γ - 1)| * |γ - 1 - n|
          ≤ (n.factorial : ℝ) * (n + 1) := mul_le_mul ih hfactor (abs_nonneg _) (by positivity)
        _ = ((n + 1).factorial : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring
  have hfac : (t.factorial : ℝ) ≤ ((t + 1 : ℕ) : ℝ) ^ (2 * t) := by
    calc (t.factorial : ℝ) ≤ (t : ℝ) ^ t := by exact_mod_cast Nat.factorial_le_pow t
      _ ≤ ((t + 1 : ℕ) : ℝ) ^ t := pow_le_pow_left₀ (by positivity) (by norm_cast; omega) _
      _ ≤ ((t + 1 : ℕ) : ℝ) ^ (2 * t) := pow_le_pow_right₀ (by norm_cast; omega) (by omega)
  intro j hj ξ hξ
  rw [leaf_Q_top γ t ht]
  have hj1 : j ≤ 1 := by omega
  interval_cases j
  · simp only [Function.iterate_zero_apply, eval_mul, eval_C, eval_X, mul_zero, add_zero,
      Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_zero, Nat.sub_self, q, descPochhammer_one, eval_X]
    rw [abs_mul, abs_of_nonneg (by have := Nat.cast_nonneg (t + 1) (α := ℝ); linarith : 0 ≤ ξ)]
    simpa [q] using mul_le_mul_of_nonneg_right ((habs t).trans hfac) (by have := Nat.cast_nonneg (t + 1) (α := ℝ); linarith)
  · simp only [Function.iterate_one, derivative_C_mul, derivative_X, mul_one, eval_C]
    have he : t + 1 - t - 1 = 0 := by omega
    rw [he]
    simp only [q, descPochhammer_zero, eval_one, mul_one]
    exact (habs t).trans (hfac.trans (pow_le_pow_right₀ (by norm_cast; omega) (by omega)))

/-- LEAF. Unit U-1539. The induction step in `s` of (50), p. 373-374, with `s^{2t+j}`:
from (46) differentiated `j` times, display (52), the case `t` and `s`, and the case `t - 1`
for all `s' ≥ t`, deduce the case `t` and `s + 1`. -/
theorem leaf12_step (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 2) (t : ℕ) (ht : 1 ≤ t) (s : ℕ)
    (hs : t + 1 ≤ s) (hst : P12 γ s t) (hprev : ∀ s' : ℕ, t ≤ s' → P12 γ s' (t - 1)) :
    P12 γ (s + 1) t := by
  intro j hj ξ hξ
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hξs : 0 ≤ ξ - s := by push_cast at hξ; linarith
  have hξ0 : 0 ≤ ξ := by push_cast at hξ; linarith
  have hν0 : 0 ≤ γ - 1 := by linarith
  have hcγ : |(γ - 1) * j - (t - 1)| ≤ (j : ℝ) + t - 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  let v : ℕ → ℝ := fun k => (derivative^[k] (Q γ s t)).eval ξ
  let w : ℕ → ℝ := fun k => (derivative^[k] (Q γ s (t - 1))).eval ξ
  have hform : (derivative^[j] (Q γ (s + 1) t)).eval ξ =
      (ξ - s) * v j + j * v (j - 1) + (γ - 1) * ξ * w (j + 1) +
        ((γ - 1) * j - (t - 1)) * w j := by
    rw [Q_iter_derivative_recurrence γ s t j ht]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]
    rfl
  have hsum : |(derivative^[j] (Q γ (s + 1) t)).eval ξ| ≤
      (ξ - s) * |v j| + j * |v (j - 1)| + ξ * |w (j + 1)| + (j + t - 1 : ℝ) * |w j| := by
    rw [hform]
    calc |(ξ - s) * v j + j * v (j - 1) + (γ - 1) * ξ * w (j + 1) + ((γ - 1) * j - (t - 1)) * w j|
        ≤ |(ξ - s) * v j| + |j * v (j - 1)| + |(γ - 1) * ξ * w (j + 1)| + |((γ - 1) * j - (t - 1)) * w j| := by
          grw [abs_add_le, abs_add_le, abs_add_le]
      _ = (ξ - s) * |v j| + j * |v (j - 1)| + (γ - 1) * (ξ * |w (j + 1)|) + |(γ - 1) * j - (t - 1)| * |w j| := by
        simp only [abs_mul, abs_of_nonneg hξs, abs_of_nonneg hj0, abs_of_nonneg hξ0, abs_of_nonneg hν0]
        ring
      _ ≤ _ := by
        have hm1 := mul_le_mul_of_nonneg_right (show γ - 1 ≤ 1 by linarith) (mul_nonneg hξ0 (abs_nonneg (w (j + 1))))
        have hm2 := mul_le_mul_of_nonneg_right hcγ (abs_nonneg (w j))
        nlinarith
  have hB := lemma12_coefficient_bound s t j ht hs hj
  have hvprev : (j : ℝ) * |v (j - 1)| ≤
      j * (s : ℝ) ^ (2 * t + j - 1) * (q (s + 1 - t - j)).eval ξ := by
    by_cases hjz : j = 0
    · subst j; simp
    have h := hst (j - 1) (by omega) ξ (by push_cast at hξ; linarith)
    have hexp : 2 * t + (j - 1) = 2 * t + j - 1 := by omega
    have hidx : s - t - (j - 1) = s + 1 - t - j := by omega
    rw [hexp, hidx] at h
    have hm := mul_le_mul_of_nonneg_left h hj0
    simpa [v, mul_assoc] using hm
  have hwcur : |w j| ≤ (s : ℝ) ^ (2 * t + j - 2) * (q (s + 1 - t - j)).eval ξ := by
    have h := hprev s (by omega) j (by omega) ξ (by push_cast at hξ; linarith)
    have hexp : 2 * (t - 1) + j = 2 * t + j - 2 := by omega
    have hidx : s - (t - 1) - j = s + 1 - t - j := by omega
    simpa [w, hexp, hidx] using h
  have hq0 : 0 ≤ (q (s + 1 - t - j)).eval ξ := descPochhammer_nonneg (by
    have hidx : ((s + 1 - t - j : ℕ) : ℝ) ≤ s + 1 := by exact_mod_cast (Nat.sub_le (s + 1 - t) j |>.trans (Nat.sub_le (s + 1) t))
    push_cast at hξ
    linarith)
  have hcoef0 : 0 ≤ (j + t - 1 : ℝ) := by linarith
  by_cases hbound : t + j ≤ s
  · have hv := hst j hbound ξ (by push_cast at hξ; linarith)
    have hw := hprev s (by omega) (j + 1) (by omega) ξ (by push_cast at hξ; linarith)
    have hew : 2 * (t - 1) + (j + 1) = 2 * t + j - 1 := by omega
    have hiw : s - (t - 1) - (j + 1) = s - t - j := by omega
    rw [hew, hiw] at hw
    have hqrec : (q (s + 1 - t - j)).eval ξ = (q (s - t - j)).eval ξ * (ξ - (s - t - j : ℕ)) := by
      have hi : s + 1 - t - j = (s - t - j) + 1 := by omega
      simp only [hi, q, descPochhammer_succ_eval]
    have hqm0 : 0 ≤ (q (s - t - j)).eval ξ := descPochhammer_nonneg (by
      have hidx : ((s - t - j : ℕ) : ℝ) ≤ s := by exact_mod_cast (Nat.sub_le (s - t) j |>.trans (Nat.sub_le s t))
      push_cast at hξ
      linarith)
    have hsquares : (s : ℝ) ^ (2 * t + j) = s * (s : ℝ) ^ (2 * t + j - 1) := by
      have hp : 2 * t + j - 1 + 1 = 2 * t + j := by omega
      calc (s : ℝ) ^ (2 * t + j) = (s : ℝ) ^ ((2 * t + j - 1) + 1) := by rw [hp]
        _ = _ := by rw [pow_succ]; ring
    have hcast : ((s - t - j : ℕ) : ℝ) = (s : ℝ) - t - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    change |v j| ≤ _ at hv
    change |w (j + 1)| ≤ _ at hw
    have hvb := mul_le_mul_of_nonneg_left hv hξs
    have hwb := mul_le_mul_of_nonneg_left hw hξ0
    have hwcb := mul_le_mul_of_nonneg_left hwcur hcoef0
    have hBmul := mul_le_mul_of_nonneg_right hB hq0
    let R : ℝ := (((t : ℝ) + j - 1) * (s : ℝ) ^ (2 * t + j) +
      ((t : ℝ) + j) * (s : ℝ) ^ (2 * t + j - 1)) * (q (s - t - j)).eval ξ
    have hR : 0 ≤ R := by
      have hc : 0 ≤ (t : ℝ) + j - 1 := by linarith
      dsimp [R]
      positivity
    have hid : ((ξ - s) * ((s : ℝ) ^ (2 * t + j) * (q (s - t - j)).eval ξ) +
        j * (s : ℝ) ^ (2 * t + j - 1) * (q (s + 1 - t - j)).eval ξ +
        ξ * ((s : ℝ) ^ (2 * t + j - 1) * (q (s - t - j)).eval ξ) +
        (j + t - 1 : ℝ) * ((s : ℝ) ^ (2 * t + j - 2) * (q (s + 1 - t - j)).eval ξ)) + R =
        ((s : ℝ) ^ (2 * t + j) + (j + 1 : ℝ) * (s : ℝ) ^ (2 * t + j - 1) +
          (j + t - 1 : ℝ) * (s : ℝ) ^ (2 * t + j - 2)) * (q (s + 1 - t - j)).eval ξ := by
      dsimp [R]
      rw [hqrec, hcast, hsquares]
      ring
    linarith
  · have hboundary : t + j = s + 1 := by omega
    have hzv : derivative^[j] (Q γ s t) = 0 := iterate_derivative_eq_zero (by have := (leaf_Q_degree γ s t (by omega) (by omega)).1; omega)
    have hzw : derivative^[j + 1] (Q γ s (t - 1)) = 0 := iterate_derivative_eq_zero (by have := (leaf_Q_degree γ s (t - 1) (by omega) (by omega)).1; omega)
    have hvz : v j = 0 := by simp [v, hzv]
    have hwz : w (j + 1) = 0 := by simp [w, hzw]
    rw [hvz, hwz] at hsum
    simp only [abs_zero, mul_zero, zero_add, add_zero] at hsum
    have hwcb := mul_le_mul_of_nonneg_left hwcur hcoef0
    have hBmul := mul_le_mul_of_nonneg_right hB hq0
    have hpos : 0 ≤ ((s : ℝ) ^ (2 * t + j) + (s : ℝ) ^ (2 * t + j - 1)) * (q (s + 1 - t - j)).eval ξ := by positivity
    nlinarith

/-! ### Assemblies for Lemma 12 -/

/-- ASSEMBLY, CONDITIONAL ON `leaf_q_iter_deriv`: the case `t = 0` of (50). -/
theorem P12_zero (γ : ℝ) (s : ℕ) : P12 γ s 0 := by
  intro j hj ξ hξ
  rw [Q_s0]
  obtain ⟨h0, hle⟩ := leaf_q_iter_deriv s j (by omega) ξ hξ
  rw [abs_of_nonneg h0]
  simpa using hle

/-- ASSEMBLY, CONDITIONAL ON the Lemma 12 leaves: (50) for all `t < s`. -/
theorem P12_all (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 2) : ∀ t s : ℕ, t < s → P12 γ s t := by
  intro t
  induction t with
  | zero => intro s _; exact P12_zero γ s
  | succ t ih =>
      intro s hs
      have hs2 : t + 1 + 1 ≤ s := hs
      induction s, hs2 using Nat.le_induction with
      | base => exact leaf12_diag γ h1 h2 (t + 1) (by omega)
      | succ s hs' ihs =>
          exact leaf12_step γ h1 h2 (t + 1) (by omega) s (by omega) (ihs (by omega))
            (fun s' hs'' => by simpa using ih s' (by omega))

/-- ASSEMBLY. Lemma 12 with `s^{2t+j}`, CONDITIONAL ON `leaf_Q_degree`, `leaf_q_iter_deriv`,
`leaf12_diag`, `leaf12_step`. -/
theorem lemma12_of_leaves : Lemma12 := by
  intro γ h1 h2 s t j hts htj
  refine ⟨?_, fun ξ hξ => P12_all γ h1 h2 t s hts j htj ξ hξ⟩
  apply iterate_derivative_eq_zero
  have := (leaf_Q_degree γ s t (by omega) hts).1
  omega

/-! ### Lemma 13, p. 374-375 -/

/-- LEAF. Unit U-1539. The bound for `E(x)` on p. 374-375: given Lemma 12, for `1 < γ < 2`,
`s ≥ 1`, `ξ ≥ s`, `s² ≤ (log x)/2`, `|Σ_{t=1}^{s-1} (log x)^{-t} Q_{s,t}(ξ)| ≤ 2s²/(log x) q_{s-1}(ξ)`,
by (50) at `j = 0`, `q_{s-t}(ξ) ≤ q_{s-1}(ξ)` and the geometric series in `s²/log x ≤ 1/2`. -/
theorem leaf13_E_bound (h12 : Lemma12) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 2) (s : ℕ) (hs : 1 ≤ s)
    (x : ℝ) (hx : 1 < x) (hξ : (s : ℝ) ≤ xi γ x) (hsq : (s : ℝ) ^ 2 ≤ Real.log x / 2) :
    |∑ t ∈ Finset.Ico 1 s, (Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x)| ≤
      2 * (s : ℝ) ^ 2 / Real.log x * (q (s - 1)).eval (xi γ x) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hqm : ∀ m : ℕ, m < s → ∀ n : ℕ, n ≤ m → (q n).eval (xi γ x) ≤ (q m).eval (xi γ x) := by
    intro m
    induction m with
    | zero =>
      intro hm n hn
      have : n = 0 := by omega
      subst n
      rfl
    | succ m ih =>
      intro hm n hn
      by_cases heq : n = m + 1
      · subst n; rfl
      have hi := ih (by omega) n (by omega)
      have hξm : (m : ℝ) + 1 ≤ xi γ x := by
        have : (m + 1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ s)
        linarith
      have hq0 : 0 ≤ (q m).eval (xi γ x) := descPochhammer_nonneg (by linarith)
      calc (q n).eval (xi γ x) ≤ (q m).eval (xi γ x) := hi
        _ ≤ (q (m + 1)).eval (xi γ x) := by
          simp only [q, descPochhammer_succ_eval]
          change 0 ≤ (descPochhammer ℝ m).eval (xi γ x) at hq0
          nlinarith
  let r : ℝ := (s : ℝ) ^ 2 / Real.log x
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr2 : r ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith)
  have hq0 : 0 ≤ (q (s - 1)).eval (xi γ x) := descPochhammer_nonneg (by
    have : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast (Nat.sub_le s 1)
    linarith)
  have hterm (t : ℕ) (ht : t ∈ Finset.Ico 1 s) :
      |(Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x)| ≤ r ^ t * (q (s - 1)).eval (xi γ x) := by
    obtain ⟨ht1, hts⟩ := Finset.mem_Ico.mp ht
    have hQ := (h12 γ h1 h2 s t 0 hts (by omega)).2 (xi γ x) hξ
    simp only [Function.iterate_zero_apply, add_zero, Nat.sub_zero] at hQ
    have hq := hqm (s - 1) (by omega) (s - t) (by omega)
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.log x ^ t)⁻¹)]
    calc (Real.log x ^ t)⁻¹ * |(Q γ s t).eval (xi γ x)|
        ≤ (Real.log x ^ t)⁻¹ * ((s : ℝ) ^ (2 * t) * (q (s - t)).eval (xi γ x)) :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
      _ ≤ (Real.log x ^ t)⁻¹ * ((s : ℝ) ^ (2 * t) * (q (s - 1)).eval (xi γ x)) := by gcongr
      _ = r ^ t * (q (s - 1)).eval (xi γ x) := by dsimp [r]; rw [div_pow, pow_mul]; ring
  have hgeom : (∑ t ∈ Finset.Ico 1 s, r ^ t) ≤ 2 * r := by
    have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := s) hr0 (by linarith : r < 1)
    simp only [pow_one] at h
    apply h.trans
    apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
    nlinarith
  calc |∑ t ∈ Finset.Ico 1 s, (Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x)|
      ≤ ∑ t ∈ Finset.Ico 1 s, |(Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.Ico 1 s, r ^ t * (q (s - 1)).eval (xi γ x) := Finset.sum_le_sum hterm
    _ = (∑ t ∈ Finset.Ico 1 s, r ^ t) * (q (s - 1)).eval (xi γ x) := (Finset.sum_mul _ _ _).symm
    _ ≤ (2 * r) * (q (s - 1)).eval (xi γ x) := mul_le_mul_of_nonneg_right hgeom hq0
    _ = _ := by dsimp [r]; ring

/-- ASSEMBLY. Lemma 13, CONDITIONAL ON Lemma 11, Lemma 12 and `leaf13_E_bound`. -/
theorem lemma13_of_leaves (h11 : Lemma11) (h12 : Lemma12) : Lemma13 := by
  intro γ h1 h2 s hs x hx hξ hsq
  have hF : 0 < F γ x := Real.exp_pos _
  have hxs : 0 < x ^ s := pow_pos (by linarith) s
  obtain ⟨_, hQ0, _, hform⟩ := h11 γ (by linarith) s hs
  rw [hform x hx]
  have hc : F γ x / x ^ s *
      (∑ t ∈ Finset.range s, (Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x)) * x ^ s / F γ x =
      ∑ t ∈ Finset.range s, (Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x) := by
    field_simp
  rw [hc, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < s), hQ0]
  simp only [pow_zero, inv_one, one_mul, add_sub_cancel_left]
  exact leaf13_E_bound h12 γ h1 h2 s hs x hx hξ hsq

/-! ### Lemma 14, p. 375 -/

/-- LEAF. Unit U-1539. The comment before Lemma 14, p. 375: for `1 < γ < 3/2` there is
`x₀ ≥ 2` such that `s ≤ γ (log x)^{γ-1}` implies `s² ≤ (log x)/4` for `x ≥ x₀`. -/
theorem leaf14_s_small (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ s : ℕ, (s : ℝ) ≤ xi γ x →
      (s : ℝ) ^ 2 ≤ Real.log x / 4 := by
  have ht : Tendsto (fun x : ℝ => γ ^ 2 * Real.log x ^ (-(3 - 2 * γ))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop (by linarith : 0 < 3 - 2 * γ)).comp Real.tendsto_log_atTop)
  have he : ∀ᶠ x : ℝ in atTop, γ ^ 2 * Real.log x ^ (-(3 - 2 * γ)) ≤ 1 / 4 :=
    ((tendsto_order.1 ht).2 _ (by norm_num)).mono (fun _ h => h.le)
  obtain ⟨b, hb⟩ := eventually_atTop.1 he
  refine ⟨max 2 b, le_max_left _ _, fun x hx s hs => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have heq : (xi γ x) ^ 2 = (γ ^ 2 * Real.log x ^ (-(3 - 2 * γ))) * Real.log x := by
    unfold xi
    rw [mul_pow, ← Real.rpow_natCast (Real.log x ^ (γ - 1)) 2, ← Real.rpow_mul hL.le]
    conv_rhs => rhs; rw [← Real.rpow_one (Real.log x)]
    rw [mul_assoc, ← Real.rpow_add hL]
    congr 2 <;> ring
  have hsq : (s : ℝ) ^ 2 ≤ (xi γ x) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hs 2
  rw [heq] at hsq
  have hsmall := mul_le_mul_of_nonneg_right (hb x ((le_max_right _ _).trans hx)) hL.le
  nlinarith

/-- LEAF. Unit U-1539. P. 375 before Lemma 14: for `s ≥ 1` and `ξ ≥ s`, `q_{s-1}(ξ) ≥ 0` and
`q_{s-1}(ξ)(ξ - s + 1/2) ≥ s!/2`, the function being increasing with value `s!/2` at `ξ = s`. -/
theorem leaf14_q_tail (s : ℕ) (hs : 1 ≤ s) (ξ : ℝ) (hξ : (s : ℝ) ≤ ξ) :
    0 ≤ (q (s - 1)).eval ξ ∧ (s.factorial : ℝ) / 2 ≤ (q (s - 1)).eval ξ * (ξ - s + 1 / 2) := by
  have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by simp [Nat.cast_sub hs]
  have hq : 0 ≤ (q (s - 1)).eval ξ := descPochhammer_nonneg (by rw [hcast]; linarith)
  have hm : (q (s - 1)).eval (s : ℝ) ≤ (q (s - 1)).eval ξ :=
    monotoneOn_descPochhammer_eval (s - 1) (by rw [hcast]; simp only [Set.mem_Ici]; linarith)
      (by rw [hcast]; simp only [Set.mem_Ici]; linarith) hξ
  have heq : (q (s - 1)).eval (s : ℝ) = (s.factorial : ℝ) := by
    have h := descPochhammer_succ_eval (S := ℝ) (s - 1) (s : ℝ)
    rw [Nat.sub_add_cancel hs, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self,
      hcast] at h
    simpa [q] using h.symm
  rw [heq] at hm
  refine ⟨hq, ?_⟩
  have hfactor : 1 / 2 ≤ ξ - s + 1 / 2 := by linarith
  have := mul_le_mul_of_nonneg_left hfactor hq
  nlinarith

/-- ASSEMBLY. Lemma 14, CONDITIONAL ON Lemma 13, `leaf14_s_small`, `leaf14_q_tail`. -/
theorem lemma14_of_leaves (h13 : Lemma13) : Lemma14 := by
  intro γ h1 h2
  obtain ⟨x₀, hx₀2, hsmall⟩ := leaf14_s_small γ h1 h2
  refine ⟨x₀, fun s x hx hξ => ?_⟩
  have hx1 : 1 < x := by linarith
  have hF : 0 < F γ x := Real.exp_pos _
  have hL : 0 < Real.log x := Real.log_pos hx1
  cases s with
  | zero =>
      simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        mul_one]
      linarith
  | succ m =>
      have hxs : 0 < x ^ (m + 1) := pow_pos (by linarith) _
      have hsq4 := hsmall x hx (m + 1) hξ
      have hsq2 : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ Real.log x / 2 := by linarith
      have h := h13 γ h1 (by linarith) (m + 1) (by omega) x hx1 hξ hsq2
      obtain ⟨hq0, htail⟩ := leaf14_q_tail (m + 1) (by omega) (xi γ x) hξ
      simp only [Nat.add_sub_cancel] at h hq0 htail
      have hqs : (q (m + 1)).eval (xi γ x) = (q m).eval (xi γ x) * (xi γ x - m) := by
        simp [q, descPochhammer_succ_right]
      have h2s : 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / Real.log x ≤ 1 / 2 := by
        rw [div_le_iff₀ hL]; linarith
      have hmul : 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / Real.log x * (q m).eval (xi γ x) ≤
          1 / 2 * (q m).eval (xi γ x) := mul_le_mul_of_nonneg_right h2s hq0
      have hlow := (abs_sub_le_iff.mp h).2
      have key : ((m + 1).factorial : ℝ) / 2 ≤
          iteratedDeriv (m + 1) (F γ) x * x ^ (m + 1) / F γ x := by
        push_cast at htail hqs hlow hmul ⊢
        nlinarith
      rw [le_div_iff₀ hF] at key
      have hk : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [div_le_div_iff₀ (by positivity) hk]
      nlinarith

/-! ### Lemma 15, p. 375-376 -/

/-- LEAF. Unit U-1539. Cauchy's estimate in the proof of Lemma 15, p. 376, on the circle of
radius `N/2` about `x`: `F` is the restriction of the holomorphic `Fc` on `Re z > 0`, so
`|F^{(s)}(x)/s!| ≤ (2/N)^s max |Fc|` for `N ≥ 10`, `N ≤ x ≤ 2N`. -/
theorem leaf15_cauchy (γ : ℝ) (hγ : 1 < γ) (N : ℝ) (hN : 10 ≤ N) (s : ℕ) (x : ℝ) (hx1 : N ≤ x)
    (hx2 : x ≤ 2 * N) (M : ℝ) (hM : ∀ z : ℂ, ‖z - x‖ = N / 2 → ‖Fc γ z‖ ≤ M) :
    |iteratedDeriv s (F γ) x / s.factorial| ≤ (2 / N) ^ s * M := by
  let U : Set ℂ := {z | 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (Fc γ) U := by
    intro z hz
    have hz1 : 1 < z.re := hz
    have hzS : z ∈ Complex.slitPlane := Or.inl (by linarith)
    have hlogS : Complex.log z ∈ Complex.slitPlane := by
      apply Or.inl
      rw [Complex.log_re]
      exact Real.log_pos (hz1.trans_le (Complex.re_le_norm z))
    exact (((Complex.differentiableAt_log hzS).cpow_const hlogS).cexp).differentiableWithinAt
  have hDn : ∀ n : ℕ, DifferentiableOn ℂ (iteratedDeriv n (Fc γ)) U := by
    intro n
    induction n with
    | zero => simpa using hD
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv hU
  have hreal : ∀ n : ℕ, ∀ y : ℝ, 1 < y →
      iteratedDeriv n (F γ) y = (iteratedDeriv n (Fc γ) (y : ℂ)).re := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simp only [iteratedDeriv_zero]
      unfold Fc F
      rw [← Complex.ofReal_log (by linarith : 0 ≤ y), ← Complex.ofReal_cpow (Real.log_nonneg (by linarith))]
      rw [← Complex.ofReal_exp]
      rfl
    | succ n ih =>
      intro y hy
      have hyU : (y : ℂ) ∈ U := hy
      have hd := ((hDn n).differentiableAt (hU.mem_nhds hyU)).hasDerivAt.real_of_complex
      have heq : iteratedDeriv n (F γ) =ᶠ[𝓝 y] (fun z : ℝ => (iteratedDeriv n (Fc γ) (z : ℂ)).re) := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using ih z hz
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact (hd.congr_of_eventuallyEq heq).deriv
  have hR : 0 < N / 2 := by linarith
  have hball : closedBall (x : ℂ) (N / 2) ⊆ U := by
    intro z hz
    have hn : ‖z - x‖ ≤ N / 2 := mem_closedBall_iff_norm.mp hz
    have hr := (Complex.abs_re_le_norm (z - x)).trans hn
    simp only [Complex.sub_re, Complex.ofReal_re, abs_le] at hr
    change 1 < z.re
    linarith
  have hDC : DiffContOnCl ℂ (Fc γ) (ball (x : ℂ) (N / 2)) :=
    hD.diffContOnCl_ball hball
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s hR hDC
    (fun z hz => hM z (mem_sphere_iff_norm.mp hz))
  have hre : |iteratedDeriv s (F γ) x| ≤ ‖iteratedDeriv s (Fc γ) (x : ℂ)‖ := by
    rw [hreal s x (by linarith)]
    exact Complex.abs_re_le_norm _
  have hfact : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  rw [abs_div, abs_of_pos hfact]
  apply (div_le_iff₀ hfact).mpr
  have hpow : (2 / N) ^ s * (N / 2) ^ s = 1 := by rw [← mul_pow]; field_simp; simp
  have h := (le_div_iff₀ (pow_pos hR s)).mp (hre.trans hb)
  have hn0 : N ≠ 0 := by linarith
  have heq : ((2 / N) ^ s * M * s.factorial) * (N / 2) ^ s = (s.factorial : ℝ) * M := by
    calc ((2 / N) ^ s * M * s.factorial) * (N / 2) ^ s
        = ((2 / N) ^ s * (N / 2) ^ s) * ((s.factorial : ℝ) * M) := by ring
      _ = _ := by rw [hpow, one_mul]
  exact (mul_le_mul_iff_left₀ (pow_pos hR s)).mp (by nlinarith)

/-- LEAF. Unit U-1539. The bound `|F(z)| ≤ F(3N)` on p. 376 for `|z - x| ≤ N/2`, `N ≤ x ≤ 2N`,
`N ≥ 10`, from `|F(z)| ≤ exp(|log z|^γ)` and `|log z|² = (log r)² + φ²` with `r ≤ 5N/2`,
`|φ| ≤ π/6`. The printed step `|log z| ≤ log r + π/6 ≤ log 3N` overshoots; the square root form
suffices, see STATEMENTS.md. -/
theorem leaf15_max (γ : ℝ) (hγ : 1 < γ) (N : ℝ) (hN : 10 ≤ N) (x : ℝ) (hx1 : N ≤ x)
    (hx2 : x ≤ 2 * N) (z : ℂ) (hz : ‖z - x‖ ≤ N / 2) : ‖Fc γ z‖ ≤ F γ (3 * N) := by
  have hNp : 0 < N := by linarith
  have hxp : 0 < x := by linarith
  let w : ℂ := (z - x) / x
  have hw : ‖w‖ ≤ N / (2 * x) := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]
    exact (div_le_div_of_nonneg_right hz hxp.le).trans_eq (by ring)
  have hw2 : ‖w‖ ≤ 1 / 2 := by
    apply hw.trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * x)).mpr
    linarith
  have hzw : z = (1 + w) * (x : ℂ) := by dsimp [w]; field_simp [Complex.ofReal_ne_zero.mpr hxp.ne']; ring
  have hwne : (1 + w : ℂ) ≠ 0 := by
    intro heq
    have he : w = -1 := by linear_combination heq
    rw [he, norm_neg, norm_one] at hw2
    norm_num at hw2
  have hlog : ‖Complex.log z‖ ≤ Real.log (3 * N) := by
    have hlogw := Complex.norm_log_one_add_half_le_self hw2
    have hrational : 3 * N / (4 * x) ≤ 2 * (3 * N - x) / (3 * N + x) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * x) (by positivity : 0 < 3 * N + x)).mpr
      have hp : (x - N) * (x - 2 * N) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hx2 hNp.le]
    have hlow := Real.le_log_one_add_of_nonneg (show 0 ≤ 3 * N / x - 1 by
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hxp).mpr
      linarith)
    have heq : 1 + (3 * N / x - 1) = 3 * N / x := by ring
    rw [heq] at hlow
    have heq' : 2 * (3 * N / x - 1) / (3 * N / x - 1 + 2) = 2 * (3 * N - x) / (3 * N + x) := by
      apply (div_eq_iff (by
        have hp : 0 < 3 * N / x := by positivity
        linarith : 3 * N / x - 1 + 2 ≠ 0)).mpr
      field_simp [hxp.ne', show 3 * N + x ≠ 0 by positivity]
      ring
    rw [heq', Real.log_div (by positivity) hxp.ne'] at hlow
    rw [hzw, Complex.log_mul_ofReal x hxp (1 + w) hwne]
    calc ‖(Real.log x : ℂ) + Complex.log (1 + w)‖
        ≤ ‖(Real.log x : ℂ)‖ + ‖Complex.log (1 + w)‖ := norm_add_le _ _
      _ ≤ Real.log x + (3 / 2) * ‖w‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
        linarith
      _ ≤ Real.log x + 3 * N / (4 * x) := by
        have h := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 3 / 2)
        have he : 3 / 2 * (N / (2 * x)) = 3 * N / (4 * x) := by ring
        rw [he] at h
        linarith
      _ ≤ Real.log (3 * N) := by linarith
  unfold Fc F
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc (Complex.log z ^ (γ : ℂ)).re ≤ ‖Complex.log z ^ (γ : ℂ)‖ := Complex.re_le_norm _
    _ = ‖Complex.log z‖ ^ γ := Complex.norm_cpow_real _ _
    _ ≤ Real.log (3 * N) ^ γ := Real.rpow_le_rpow (norm_nonneg _) hlog (by linarith)

/-- ASSEMBLY. Lemma 15, CONDITIONAL ON `leaf15_cauchy` and `leaf15_max`. -/
theorem lemma15_of_leaves : Lemma15 := by
  intro γ hγ N hN s x hx1 hx2
  have h := leaf15_cauchy γ hγ N hN s x hx1 hx2 (F γ (3 * N))
    (fun z hz => leaf15_max γ hγ N hN x hx1 hx2 z hz.le)
  have hF : 0 < F γ (3 * N) := Real.exp_pos _
  have hp : 0 < (2 / N) ^ s := pow_pos (by positivity) s
  calc _ ≤ (2 / N) ^ s * F γ (3 * N) := h
    _ ≤ 2 * (2 / N) ^ s * F γ (3 * N) := by nlinarith

/-! ### Lemma 16, p. 376-377 -/

/-- LEAF. Unit U-1539. The proof of Lemma 16 (a), p. 376-377: with `α = N^{-A}`, `N ≥ 10`,
display (53) is equivalent after taking logarithms to `2αF(3N)(2/N)^s ≤ N^{-ϑs}`. -/
theorem leaf16_53 (γ N : ℝ) (hN : 10 ≤ N) (α ϑ A : ℝ) (hα : 0 < α) (hαA : α = N ^ (-A))
    (s : ℕ) (h53 : ((s : ℝ) + 1) * Real.log 2 / Real.log N + Real.log (3 * N) ^ γ / Real.log N
        ≤ s * (1 - ϑ) + A) :
    2 * α * F γ (3 * N) * (2 / N) ^ s ≤ N ^ (-(ϑ * s)) := by
  have hNp : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogα : Real.log α = -A * Real.log N := by rw [hαA, Real.log_rpow hNp]
  unfold F
  apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hNp _)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) hα.ne', hlogα, Real.log_exp, Real.log_pow,
    Real.log_div (by norm_num) hNp.ne', Real.log_rpow hNp]
  rw [← add_div] at h53
  have h := (div_le_iff₀ hL).mp h53
  nlinarith

/-- LEAF. Unit U-1539. The proof of Lemma 16 (b), p. 377: with `α = N^{-A}`, `N > 1`,
display (54) is equivalent after taking logarithms to `αF(N)/(2N^s) ≥ N^{-ϑs}`. -/
theorem leaf16_54 (γ N : ℝ) (hN : 1 < N) (α ϑ A : ℝ) (hα : 0 < α) (hαA : α = N ^ (-A))
    (s : ℕ) (h54 : s * (1 - ϑ) + A ≤ Real.log N ^ (γ - 1) - Real.log 2 / Real.log N) :
    N ^ (-(ϑ * s)) ≤ α * F γ N / (2 * N ^ s) := by
  have hNp : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hlogα : Real.log α = -A * Real.log N := by rw [hαA, Real.log_rpow hNp]
  unfold F
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hNp _) (by positivity)).mp
  rw [Real.log_rpow hNp, Real.log_div (by positivity) (by positivity),
    Real.log_mul hα.ne' (Real.exp_pos _).ne', hlogα, Real.log_exp,
    Real.log_mul (by norm_num) (pow_pos hNp _).ne', Real.log_pow]
  rw [Real.rpow_sub_one hL.ne'] at h54
  have h := (le_div_iff₀ hL).mp (show s * (1 - ϑ) + A ≤
    (Real.log N ^ γ - Real.log 2) / Real.log N by simpa [sub_div] using h54)
  nlinarith

/-- LEAF. Unit U-1539. P. 377: `x^{-s} F(x)` is increasing for `x ≥ N` when
`s ≤ γ (log N)^{γ-1}`, its derivative being `x^{-s-1} F(x)(ξ(x) - s)`. -/
theorem leaf16_mono (γ : ℝ) (hγ : 1 < γ) (N : ℝ) (hN : 1 < N) (s : ℕ) (hs : (s : ℝ) ≤ xi γ N)
    (x : ℝ) (hx : N ≤ x) : F γ N / N ^ s ≤ F γ x / x ^ s := by
  have hd (y : ℝ) (hy : N ≤ y) : HasDerivAt (fun z => F γ z / z ^ s)
      (F γ y / y ^ (s + 1) * (xi γ y - s)) y := by
    have hy0 : 0 < y := by linarith
    have hL : 0 < Real.log y := Real.log_pos (by linarith)
    have hF : HasDerivAt (F γ) (F γ y * xi γ y / y) y := by
      convert ((Real.hasDerivAt_log hy0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
      · rfl
      · dsimp [F, xi]; ring
    convert hF.div ((hasDerivAt_id y).pow s) (pow_ne_zero s hy0.ne') using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq]
      cases s with
      | zero => simp <;> ring
      | succ s => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; field_simp <;> ring
  have hnonneg (y : ℝ) (hy : N ≤ y) : 0 ≤ F γ y / y ^ (s + 1) * (xi γ y - s) := by
    have hy0 : 0 < y := by linarith
    have hxi : xi γ N ≤ xi γ y := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ γ)
      exact Real.rpow_le_rpow (Real.log_nonneg (by linarith))
        (Real.log_le_log (by linarith) hy) (by linarith)
    have : 0 ≤ xi γ y - s := by linarith
    unfold F
    positivity
  have hm : MonotoneOn (fun z => F γ z / z ^ s) (Set.Ici N) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici N)
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      exact hnonneg y (interior_subset hy)
  exact hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx

/-- ASSEMBLY. Lemma 16 (a), CONDITIONAL ON Lemma 15 and `leaf16_53`. -/
theorem lemma16a_of_leaves (h15 : Lemma15) : Lemma16a := by
  intro γ hγ N hN α ϑ A hα _ _ hαA s h53 x hx1 hx2
  have h := h15 γ hγ N hN s x hx1 hx2
  have hb := leaf16_53 γ N hN α ϑ A hα hαA s h53
  calc |α * iteratedDeriv s (F γ) x / s.factorial|
      = α * |iteratedDeriv s (F γ) x / s.factorial| := by
        rw [mul_div_assoc, abs_mul, abs_of_pos hα]
    _ ≤ α * (2 * (2 / N) ^ s * F γ (3 * N)) := mul_le_mul_of_nonneg_left h hα.le
    _ = 2 * α * F γ (3 * N) * (2 / N) ^ s := by ring
    _ ≤ _ := hb

/-- ASSEMBLY. Lemma 16 (b), CONDITIONAL ON Lemma 14, `leaf16_54`, `leaf16_mono`. -/
theorem lemma16b_of_leaves (h14 : Lemma14) : Lemma16b := by
  intro γ h1 h2
  obtain ⟨x₀, hx₀⟩ := h14 γ h1 h2
  refine ⟨max x₀ 2, fun N hN α ϑ A hα _ _ hαA s hs h54 x hx1 hx2 => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNx : x₀ ≤ x := le_trans (le_trans (le_max_left _ _) hN) hx1
  have hξ : (s : ℝ) ≤ xi γ x := by
    refine le_trans hs ?_
    unfold xi
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact Real.rpow_le_rpow (Real.log_nonneg (by linarith))
      (Real.log_le_log (by linarith) hx1) (by linarith)
  have hD := hx₀ s x hNx hξ
  have hmono := leaf16_mono γ h1 N (by linarith) s hs x hx1
  have hb := leaf16_54 γ N (by linarith) α ϑ A hα hαA s h54
  calc N ^ (-(ϑ * s)) ≤ α * F γ N / (2 * N ^ s) := hb
    _ = α / 2 * (F γ N / N ^ s) := by ring
    _ ≤ α / 2 * (F γ x / x ^ s) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = α * (F γ x / (2 * x ^ s)) := by ring
    _ ≤ α * (iteratedDeriv s (F γ) x / s.factorial) := mul_le_mul_of_nonneg_left hD hα.le
    _ = α * iteratedDeriv s (F γ) x / s.factorial := by ring
    _ ≤ _ := le_abs_self _

/-! ### Leaves for Theorem 2, p. 377 -/

/-- LEAF. Unit U-1539. `αF` is smooth on `x > 1` for `γ > 0`, as Lemma 10 needs. -/
theorem leaf_T2_smooth (γ α : ℝ) (hγ : 0 < γ) (k : ℕ) :
    ContDiffOn ℝ k (fun x => α * F γ x) (Set.Ioi 1) := by
  apply contDiffOn_const.mul
  unfold F
  apply ContDiffOn.exp
  apply ContDiffOn.rpow_const_of_ne
  · exact contDiffOn_id.log (fun x hx => ne_of_gt (lt_trans zero_lt_one hx))
  · intro x hx
    exact ne_of_gt (Real.log_pos hx)

/-- LEAF. Unit U-1539. Display (55), p. 377: for `N ≥ 2`, `α > 0` with
`F(2N)^{-c} ≤ α ≤ F(N)^C`, the exponent `A = -log α / log N` has
`-C (log N)^{γ-1} ≤ A ≤ c (log 2N)^γ / log N`. -/
theorem leaf_T2_A_range (γ c C : ℝ) (h1 : 1 < γ) (hc : 0 < c) (hC : 0 < C) (N : ℝ) (hN : 2 ≤ N)
    (α : ℝ) (hα : 0 < α) (hlo : F γ (2 * N) ^ (-c) ≤ α) (hhi : α ≤ F γ N ^ C) :
    -C * Real.log N ^ (γ - 1) ≤ -Real.log α / Real.log N ∧
      -Real.log α / Real.log N ≤ c * Real.log (2 * N) ^ γ / Real.log N := by
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hlo' := Real.log_le_log (Real.rpow_pos_of_pos (Real.exp_pos _) _) hlo
  have hhi' := Real.log_le_log hα hhi
  unfold F at hlo' hhi'
  rw [Real.log_rpow (Real.exp_pos _), Real.log_exp] at hlo' hhi'
  rw [Real.rpow_sub_one hL.ne']
  constructor
  · apply (le_div_iff₀ hL).mpr
    have : -C * (Real.log N ^ γ / Real.log N) * Real.log N = -C * Real.log N ^ γ := by field_simp
    rw [this]
    linarith
  · exact div_le_div_of_nonneg_right (by linarith) hL.le

/-- LEAF. Unit U-1539. P. 377, "Take ϑ = 3/4 and s = k in Lemma 16 (a)": for large `N` and
`A ≥ -C (log N)^{γ-1}` with `C < γ - 1`, display (53) holds at `ϑ = 3/4`, `s = k`. -/
theorem leaf_T2_top (γ C : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hC0 : 0 < C) (hC1 : C < γ - 1) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ A : ℝ, -C * Real.log N ^ (γ - 1) ≤ A →
      ((kN γ N : ℝ) + 1) * Real.log 2 / Real.log N + Real.log (3 * N) ^ γ / Real.log N
        ≤ (kN γ N : ℝ) * (1 - 3 / 4) + A := by
  have hr : Tendsto (fun N : ℝ => Real.log (3 * N) / Real.log N) atTop (𝓝 1) := by
    have ht : Tendsto (fun N : ℝ => Real.log 3 / Real.log N + 1) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add_const 1
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hL : 0 < Real.log N := Real.log_pos hN
    rw [Real.log_mul (by norm_num) (by linarith), add_div, div_self hL.ne']
  have hrpow : Tendsto (fun N : ℝ => (Real.log (3 * N) / Real.log N) ^ γ) atTop (𝓝 1) := by
    simpa using hr.rpow_const (p := γ) (Or.inl one_ne_zero)
  have hep : ∀ᶠ N : ℝ in atTop, (Real.log (3 * N) / Real.log N) ^ γ ≤ 3 / 2 :=
    ((tendsto_order.1 hrpow).2 _ (by norm_num)).mono (fun _ h => h.le)
  have helog : ∀ᶠ N : ℝ in atTop, Real.log 2 / Real.log N ≤ 1 / 100 := by
    have ht : Tendsto (fun N : ℝ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    exact ((tendsto_order.1 ht).2 _ (by norm_num)).mono (fun _ h => h.le)
  have heone : ∀ᶠ N : ℝ in atTop, 1 ≤ Real.log N ^ (γ - 1) :=
    ((tendsto_rpow_atTop (by linarith : 0 < γ - 1)).comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  suffices ∀ᶠ N : ℝ in atTop, ∀ A : ℝ, -C * Real.log N ^ (γ - 1) ≤ A →
      ((kN γ N : ℝ) + 1) * Real.log 2 / Real.log N + Real.log (3 * N) ^ γ / Real.log N
        ≤ (kN γ N : ℝ) * (1 - 3 / 4) + A from eventually_atTop.1 this
  filter_upwards [eventually_ge_atTop (2 : ℝ), hep, helog, heone] with N hN hp hl ho
  intro A hA
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hL3 : 0 ≤ Real.log (3 * N) := Real.log_nonneg (by linarith)
  have hratio : Real.log (3 * N) ^ γ / Real.log N ≤ 3 / 2 * Real.log N ^ (γ - 1) := by
    rw [Real.div_rpow hL3 hL.le] at hp
    have he := (div_le_iff₀ (Real.rpow_pos_of_pos hL γ)).mp hp
    rw [Real.rpow_sub_one hL.ne']
    exact (div_le_div_of_nonneg_right he hL.le).trans_eq (by ring)
  have hklow : 9 * Real.log N ^ (γ - 1) ≤ (kN γ N : ℝ) := by
    have h := (Nat.lt_floor_add_one (9 * Real.log N ^ (γ - 1))).le
    simpa [kN, Nat.cast_add, Nat.cast_one] using h
  have hkup : (kN γ N : ℝ) ≤ 10 * Real.log N ^ (γ - 1) := by
    have hf := Nat.floor_le (show 0 ≤ 9 * Real.log N ^ (γ - 1) by positivity)
    unfold kN
    push_cast
    linarith
  have hfirst : ((kN γ N : ℝ) + 1) * Real.log 2 / Real.log N ≤ 11 / 100 * Real.log N ^ (γ - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (kN γ N : ℝ) + 1)
    have : (kN γ N : ℝ) + 1 ≤ 11 * Real.log N ^ (γ - 1) := by linarith
    calc ((kN γ N : ℝ) + 1) * Real.log 2 / Real.log N
        = ((kN γ N : ℝ) + 1) * (Real.log 2 / Real.log N) := by ring
      _ ≤ ((kN γ N : ℝ) + 1) * (1 / 100) := hmul
      _ ≤ 11 / 100 * Real.log N ^ (γ - 1) := by linarith
  have hC : C ≤ 1 / 2 := by linarith
  have hm := mul_le_mul_of_nonneg_right hC (Real.rpow_pos_of_pos hL (γ - 1)).le
  nlinarith

/-- LEAF. Unit U-1539. For large `N`, `k = [9 (log N)^{γ-1}] + 1` has `3 ≤ k ≤ 10 (log N)^{γ-1}`. -/
theorem leaf_T2_k3 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → 3 ≤ kN γ N ∧ (kN γ N : ℝ) ≤ 10 * Real.log N ^ (γ - 1) := by
  have ht := (tendsto_rpow_atTop (by linarith : 0 < γ - 1)).comp Real.tendsto_log_atTop
  obtain ⟨b, hb⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop 1))
  refine ⟨b, fun N hN => ?_⟩
  have hL : 1 ≤ Real.log N ^ (γ - 1) := hb N hN
  have hf : (⌊9 * Real.log N ^ (γ - 1)⌋₊ : ℝ) ≤ 9 * Real.log N ^ (γ - 1) :=
    Nat.floor_le (by positivity)
  have hfloor : 3 ≤ ⌊9 * Real.log N ^ (γ - 1)⌋₊ :=
    Nat.le_floor (by norm_num only [Nat.cast_ofNat]; linarith)
  unfold kN
  push_cast
  constructor
  · omega
  · linarith

/-- LEAF. Unit U-1539. P. 377, "#S ≥ δk, at least for large N", from (55) and (56). -/
theorem leaf_T2_S_card (γ c C θ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hc0 : 0 < c) (hc1 : c < 1)
    (hC0 : 0 < C) (hC1 : C < γ - 1) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    (hθC : 1 + C < γ * (1 - θ)) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ A : ℝ, -C * Real.log N ^ (γ - 1) ≤ A →
      A ≤ c * Real.log (2 * N) ^ γ / Real.log N →
      deltaK c θ * kN γ N ≤ (Sset γ θ A N).card := by
  let H : ℝ → ℝ := fun N => Real.log N ^ (γ - 1)
  let e : ℝ → ℝ := fun N => Real.log 2 / Real.log N
  let f : ℝ → ℝ → ℝ := fun a N => Real.log (a * N) ^ γ / Real.log N
  let D : ℝ := (1 - c) * (1 / (1 - θ) - 1 / (1 - θ / 2))
  let l : ℝ := (1 - c) / (1 - θ / 2)
  have hd0 : 0 < 1 - θ / 2 := by linarith
  have hd1 : 0 < 1 - θ := by linarith
  have hD : 0 < D := by
    dsimp [D]
    apply mul_pos (by linarith)
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hd1 (by linarith))
  have hl : 0 < l := div_pos (by linarith) hd0
  have htH : Tendsto H atTop atTop := (tendsto_rpow_atTop (by linarith : 0 < γ - 1)).comp Real.tendsto_log_atTop
  have hte : Tendsto e atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hteH : Tendsto (fun N => e N / H N) atTop (𝓝 0) := hte.div_atTop htH
  have htf2 : Tendsto (fun N => f 2 N / H N) atTop (𝓝 1) := log_scale_rpow_ratio_tendsto γ 2 (by norm_num)
  have htf3 : Tendsto (fun N => f 3 N / H N) atTop (𝓝 1) := log_scale_rpow_ratio_tendsto γ 3 (by norm_num)
  have htlo : Tendsto (fun N => lowerB γ θ (c * f 2 N) N / H N) atTop (𝓝 l) := by
    have ht := ((hteH.add htf3).sub (htf2.const_mul c)).div ((tendsto_const_nhds (x := 1 - θ / 2)).sub hte) (by simpa using hd0.ne')
    have ht0 : Tendsto (fun N => ((e N / H N + f 3 N / H N) - c * (f 2 N / H N)) / (1 - θ / 2 - e N)) atTop (𝓝 l) := by
      convert ht using 1 <;> simp [l]
    apply ht0.congr'
    exact Filter.Eventually.of_forall (fun N => by dsimp [lowerB, e, f]; ring)
  have hthi : Tendsto (fun N => upperB γ θ (c * f 2 N) N / H N) atTop (𝓝 ((1 - c) / (1 - θ))) := by
    have ht := (((tendsto_const_nhds (x := (1 : ℝ))).sub (htf2.const_mul c)).sub hteH).div_const (1 - θ)
    apply (show Tendsto (fun N => (1 - c * (f 2 N / H N) - e N / H N) / (1 - θ)) atTop (𝓝 ((1 - c) / (1 - θ))) by simpa using ht).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hH : H N ≠ 0 := (Real.rpow_pos_of_pos (Real.log_pos hN) _).ne'
    calc (1 - c * (f 2 N / H N) - e N / H N) / (1 - θ)
        = (H N / H N - c * (f 2 N / H N) - e N / H N) / (1 - θ) := by rw [div_self hH]
      _ = _ := by dsimp [upperB, H, e, f]; ring
  have htwidth : Tendsto (fun N => (upperB γ θ (c * f 2 N) N - lowerB γ θ (c * f 2 N) N) / H N) atTop (𝓝 D) := by
    convert hthi.sub htlo using 1
    · ext N; ring
    · dsimp [D, l]; ring
  have hewidth : ∀ᶠ N : ℝ in atTop,
      3 / 4 * D ≤ (upperB γ θ (c * f 2 N) N - lowerB γ θ (c * f 2 N) N) / H N :=
    ((tendsto_order.1 htwidth).1 _ (by nlinarith)).mono (fun _ h => h.le)
  have helo : ∀ᶠ N : ℝ in atTop, l / 2 ≤ lowerB γ θ (c * f 2 N) N / H N :=
    ((tendsto_order.1 htlo).1 _ (by linarith)).mono (fun _ h => h.le)
  have heden : ∀ᶠ N : ℝ in atTop, e N < θ / 2 := (tendsto_order.1 hte).2 _ (by linarith)
  have heH : ∀ᶠ N : ℝ in atTop, max 1 (max (4 / D) (2 / l)) ≤ H N := htH.eventually (eventually_ge_atTop _)
  obtain ⟨bk, hbk⟩ := leaf_T2_k3 γ h1 h2
  suffices ∀ᶠ N : ℝ in atTop, ∀ A : ℝ, -C * Real.log N ^ (γ - 1) ≤ A →
      A ≤ c * Real.log (2 * N) ^ γ / Real.log N → deltaK c θ * kN γ N ≤ (Sset γ θ A N).card from eventually_atTop.1 this
  filter_upwards [eventually_ge_atTop (2 : ℝ), hewidth, helo, heden, heH, eventually_ge_atTop bk] with N hN hw hlo he hH hNk
  intro A hAlo hAhi
  have hLp : 0 < Real.log N := Real.log_pos (by linarith)
  have hHp : 0 < H N := Real.rpow_pos_of_pos hLp _
  have hH1 : 1 ≤ H N := (le_max_left _ _).trans hH
  have hH4 : 4 / D ≤ H N := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hH2 : 2 / l ≤ H N := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hden : 0 < 1 - θ / 2 - e N := by linarith
  have hdenlt : 1 - θ < 1 - θ / 2 - e N := by linarith
  have he0 : 0 ≤ e N := div_nonneg (Real.log_nonneg (by norm_num)) hLp.le
  have hAmax : A ≤ c * f 2 N := by simpa [f, mul_div_assoc] using hAhi
  have hlowmono : lowerB γ θ (c * f 2 N) N ≤ lowerB γ θ A N := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact sub_le_sub_left hAmax _
  have hlo1 : 1 ≤ lowerB γ θ A N := by
    have hmul := (le_div_iff₀ hHp).mp hlo
    have hbig := (div_le_iff₀ hl).mp hH2
    nlinarith
  have hwidthmono : upperB γ θ (c * f 2 N) N - lowerB γ θ (c * f 2 N) N ≤
      upperB γ θ A N - lowerB γ θ A N := by
    have hrec : 0 ≤ 1 / (1 - θ) - 1 / (1 - θ / 2 - e N) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hd1 hdenlt.le)
    have hmul := mul_nonneg (sub_nonneg.mpr hAmax) hrec
    have heq : (upperB γ θ A N - lowerB γ θ A N) -
        (upperB γ θ (c * f 2 N) N - lowerB γ θ (c * f 2 N) N) =
        (c * f 2 N - A) * (1 / (1 - θ) - 1 / (1 - θ / 2 - e N)) := by
      dsimp [upperB, lowerB, e]
      ring
    rw [← heq] at hmul
    linarith
  have hup : upperB γ θ A N ≤ γ * H N := by
    apply (div_le_iff₀ hd1).mpr
    have hmargin := mul_le_mul_of_nonneg_right hθC.le hHp.le
    change H N - A - e N ≤ γ * H N * (1 - θ)
    change -C * H N ≤ A at hAlo
    nlinarith
  have hkfloor : 9 * H N < (kN γ N : ℝ) := by
    simpa [kN, H, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (9 * H N)
  have hk1 : 1 ≤ kN γ N := by unfold kN; omega
  have hpred : ((kN γ N - 1 : ℕ) : ℝ) = (kN γ N : ℝ) - 1 := by simp [Nat.cast_sub hk1]
  have hupK : upperB γ θ A N ≤ (kN γ N - 1 : ℕ) := by rw [hpred]; nlinarith
  have hcount := card_nat_interval_lower_bound (lowerB γ θ A N) (upperB γ θ A N) (kN γ N - 1) hlo1 hupK
  change upperB γ θ A N - lowerB γ θ A N - 1 ≤ (Sset γ θ A N).card at hcount
  have hwidth := (le_div_iff₀ hHp).mp hw
  have hlarge := (div_le_iff₀ hD).mp hH4
  have hkupper := (hbk N hNk).2
  have hdelta : deltaK c θ = D / 20 := by dsimp [deltaK, D]; ring
  rw [hdelta]
  change (kN γ N : ℝ) ≤ 10 * H N at hkupper
  have hkmul := mul_le_mul_of_nonneg_left hkupper (show 0 ≤ D / 20 by positivity)
  nlinarith

/-- LEAF. Unit U-1539. P. 377: for large `N`, every `s` in `S` satisfies display (53) with
`ϑ = θ/2`, display (54) with `ϑ = θ`, and `s ≤ γ (log N)^{γ-1}`, the last from
`1 + C < γ(1 - θ)`. -/
theorem leaf_T2_S_ineq (γ c C θ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hc0 : 0 < c) (hc1 : c < 1)
    (hC0 : 0 < C) (hC1 : C < γ - 1) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    (hθC : 1 + C < γ * (1 - θ)) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ A : ℝ, -C * Real.log N ^ (γ - 1) ≤ A →
      A ≤ c * Real.log (2 * N) ^ γ / Real.log N → ∀ s ∈ Sset γ θ A N,
      (((s : ℝ) + 1) * Real.log 2 / Real.log N + Real.log (3 * N) ^ γ / Real.log N
          ≤ s * (1 - θ / 2) + A) ∧
      (s * (1 - θ) + A ≤ Real.log N ^ (γ - 1) - Real.log 2 / Real.log N) ∧
      (s : ℝ) ≤ xi γ N := by
  have ht : Tendsto (fun N : ℝ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  obtain ⟨b, hb⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 (1 - θ / 2) (by linarith))
  refine ⟨max 2 b, fun N hN A hAlo hAhi s hs => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hden : 0 < 1 - θ / 2 - Real.log 2 / Real.log N := by
    have := hb N ((le_max_right _ _).trans hN)
    linarith
  have hden' : 0 < 1 - θ := by linarith
  obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hs
  unfold lowerB at hlo
  unfold upperB at hhi
  have hlo' := (div_le_iff₀ hden).mp hlo
  have hhi' := (le_div_iff₀ hden').mp hhi
  refine ⟨?_, by linarith, ?_⟩
  · have heq : ((s : ℝ) + 1) * Real.log 2 / Real.log N + Real.log (3 * N) ^ γ / Real.log N =
        (Real.log 2 + Real.log (3 * N) ^ γ) / Real.log N + s * (Real.log 2 / Real.log N) := by ring
    rw [heq]
    nlinarith
  · have hpow : 0 ≤ Real.log N ^ (γ - 1) := (Real.rpow_pos_of_pos hL _).le
    have hlog : 0 ≤ Real.log 2 / Real.log N := div_nonneg (Real.log_nonneg (by norm_num)) hL.le
    have hmargin := mul_le_mul_of_nonneg_right hθC.le hpow
    unfold xi
    nlinarith

/-- LEAF. Unit U-1539. The last step of p. 377: for `N ≥ 2` and `1 ≤ k ≤ 10 (log N)^{γ-1}`,
`N^{1 - c/k²} ≤ N exp(-(c/100)(log N)^{3-2γ})`. -/
theorem leaf_T2_conv (γ c' : ℝ) (h1 : 1 < γ) (hc' : 0 < c') (N : ℕ) (hN : 2 ≤ N) (k : ℕ)
    (hk : 1 ≤ k) (hk10 : (k : ℝ) ≤ 10 * Real.log N ^ (γ - 1)) :
    (N : ℝ) ^ (1 - c' / (k : ℝ) ^ 2) ≤ N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow : (Real.log N ^ (γ - 1)) ^ 2 * Real.log N ^ (3 - 2 * γ) = Real.log N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    convert Real.rpow_one (Real.log N) using 1 <;> congr 1 <;> ring
  have hsq : (k : ℝ) ^ 2 ≤ 100 * (Real.log N ^ (γ - 1)) ^ 2 := by
    nlinarith [Real.rpow_pos_of_pos hL (γ - 1)]
  have hexp : c' / 100 * Real.log N ^ (3 - 2 * γ) ≤ c' * Real.log N / (k : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hkp)).mpr
    have := mul_le_mul_of_nonneg_right hsq (Real.rpow_pos_of_pos hL (3 - 2 * γ)).le
    rw [mul_assoc, hpow] at this
    nlinarith
  rw [Real.rpow_def_of_pos hNp]
  conv_rhs => lhs; rw [← Real.exp_log hNp]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert sub_le_sub_left hexp (Real.log N) using 1 <;> ring

/-- LEAF. Unit U-1539. Small `N` in Theorem 2: finitely many `N` are absorbed by the
implied constant. -/
theorem leaf_T2_small (γ κ : ℝ) (N₀ : ℕ) :
    ∃ B₀ : ℝ, ∀ N : ℕ, 1 ≤ N → N < N₀ →
      (N : ℝ) + 1 ≤ B₀ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  classical
  let f : ℕ → ℝ := fun N => ((N : ℝ) + 1) / (N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)))
  obtain ⟨B, hB⟩ := ((Finset.range N₀).image f).bddAbove
  refine ⟨B, fun N hN hN₀ => ?_⟩
  have hpos : 0 < (N : ℝ) * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) :=
    mul_pos (by exact_mod_cast hN) (Real.exp_pos _)
  have h := hB (Finset.mem_image.mpr ⟨N, Finset.mem_range.mpr hN₀, rfl⟩)
  dsimp [f] at h
  simpa [mul_assoc] using (div_le_iff₀ hpos).mp h

/-- LEAF. Unit U-1539. For `1 < γ < 3/2`, `N exp(-κ (log N)^{3-2γ}) ≥ 1` for large `N`,
since `3 - 2γ < 1`; this absorbs the term `n = N` of Theorem 2 that Lemma 10 omits. -/
theorem leaf_T2_large_one (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  have ht : Tendsto (fun x : ℝ => κ * Real.log x ^ (-(2 * γ - 2))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 * γ - 2)).comp Real.tendsto_log_atTop)
  obtain ⟨b, hb⟩ := eventually_atTop.1 (((tendsto_order.1 ht).2 1 (by norm_num)).mono (fun _ h => h.le))
  refine ⟨max 2 ⌈b⌉₊, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNb : b ≤ (N : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast ((le_max_right _ _).trans hN))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have heq : Real.log N ^ (3 - 2 * γ) = Real.log N ^ (-(2 * γ - 2)) * Real.log N := by
    conv_rhs => rhs; rw [← Real.rpow_one (Real.log N)]
    rw [← Real.rpow_add hL]
    congr 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right (hb N hNb) hL.le
  have he : 0 ≤ Real.log N + -κ * Real.log N ^ (3 - 2 * γ) := by rw [heq]; nlinarith
  calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log N + -κ * Real.log N ^ (3 - 2 * γ)) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, Real.exp_log hNp]

/-! ### Assemblies for Theorem 2 -/

/-- ASSEMBLY, CONDITIONAL ON Lemma 16 (a), (b) and the leaves `leaf_T2_*`: for large `N` and
`F(2N)^{-c} ≤ α ≤ F(N)^C`, `αF` lies in Karacuba's class with `θ, θ/2, 3/4, δ` and
`k = [9 (log N)^{γ-1}] + 1`, as on p. 377. -/
theorem classMembership_of_leaves (h16a : Lemma16a) (h16b : Lemma16b) (γ c C θ : ℝ)
    (h1 : 1 < γ) (h2 : γ < 3 / 2) (hc0 : 0 < c) (hc1 : c < 1) (hC0 : 0 < C) (hC1 : C < γ - 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hθC : 1 + C < γ * (1 - θ)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ, 0 < α → F γ (2 * N) ^ (-c) ≤ α → α ≤ F γ N ^ C →
      KClass N θ (θ / 2) (3 / 4) (deltaK c θ) (fun x => α * F γ x) (kN γ N) ∧
      1 ≤ kN γ N ∧ (kN γ N : ℝ) ≤ 10 * Real.log N ^ (γ - 1) := by
  obtain ⟨Na, hNa⟩ := leaf_T2_top γ C h1 h2 hC0 hC1
  obtain ⟨Nb, hNb⟩ := leaf_T2_k3 γ h1 h2
  obtain ⟨Nc, hNc⟩ := leaf_T2_S_card γ c C θ h1 h2 hc0 hc1 hC0 hC1 hθ0 hθ1 hθC
  obtain ⟨Nd, hNd⟩ := leaf_T2_S_ineq γ c C θ h1 h2 hc0 hc1 hC0 hC1 hθ0 hθ1 hθC
  obtain ⟨N1, hN1⟩ := h16b γ h1 h2
  refine ⟨⌈max (max (max Na Nb) (max Nc Nd)) (max N1 10)⌉₊, fun N hN α hα hlo hhi => ?_⟩
  have hNr : max (max (max Na Nb) (max Nc Nd)) (max N1 10) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨⟨⟨hNa', hNb'⟩, ⟨hNc', hNd'⟩⟩, ⟨hN1', hN10⟩⟩ := by simpa only [max_le_iff] using hNr
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  set A := -Real.log α / Real.log N with hAdef
  have hαA : α = (N : ℝ) ^ (-A) := by
    have : Real.log N * -A = Real.log α := by
      rw [hAdef]; field_simp
    rw [Real.rpow_def_of_pos hNpos, this, Real.exp_log hα]
  obtain ⟨hA1, hA2⟩ := leaf_T2_A_range γ c C h1 hc0 hC0 N (by linarith) α hα hlo hhi
  obtain ⟨hk3, hk10⟩ := hNb N hNb'
  refine ⟨⟨hk3, ⟨Set.Ioi 1, isOpen_Ioi, ?_, leaf_T2_smooth γ α (by linarith) _⟩, ?_, ?_⟩,
    by omega, hk10⟩
  · intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  · intro x hx
    simp only [iteratedDeriv_const_mul']
    exact h16a γ h1 N hN10 α (3 / 4) A hα (by norm_num) (by norm_num) hαA (kN γ N)
      (hNa N hNa' A hA1) x hx.1 hx.2
  · refine ⟨Sset γ θ A N, Finset.filter_subset _ _, hNc N hNc' A hA1 hA2, ?_⟩
    intro s hs x hx
    obtain ⟨h53, h54, hsx⟩ := hNd N hNd' A hA1 hA2 s hs
    simp only [iteratedDeriv_const_mul']
    exact ⟨hN1 N hN1' α θ A hα hθ0 (by linarith) hαA s hsx h54 x hx.1 hx.2,
      h16a γ h1 N hN10 α (θ / 2) A hα (by linarith) (by linarith) hαA s h53 x hx.1 hx.2⟩

/-- ASSEMBLY. Theorem 2, CONDITIONAL ON Lemma 10, which is CITED, on Lemma 16 (a), (b) and on
the leaves `leaf_T2_*`. With `lemma16a_of_leaves`, `lemma16b_of_leaves` and the chain above,
Theorem 2 rests on Lemma 10 and the leaves of this file only: see `theorem2_of_all_leaves`. -/
theorem theorem2_of_leaves (h10 : Lemma10) (h16a : Lemma16a) (h16b : Lemma16b) : Theorem2 := by
  intro γ h1 h2 c C hc0 hc1 hC0 hC1
  set θ := min (1 / 4 : ℝ) ((γ - 1 - C) / (2 * γ)) with hθdef
  have hθ0 : 0 < θ := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have hθ1 : θ < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθC : 1 + C < γ * (1 - θ) := by
    have hm := min_le_right (1 / 4 : ℝ) ((γ - 1 - C) / (2 * γ))
    have hγθ : γ * θ ≤ (γ - 1 - C) / 2 := by
      calc γ * θ ≤ γ * ((γ - 1 - C) / (2 * γ)) := mul_le_mul_of_nonneg_left hm (by linarith)
        _ = (γ - 1 - C) / 2 := by field_simp
    nlinarith
  have hd1 : 1 / (1 - θ / 2) < 1 / (1 - θ) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hd2 : 1 / (1 - θ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hd3 : 0 < 1 / (1 - θ / 2) := by apply div_pos one_pos; linarith
  have hδ0 : 0 < deltaK c θ := by
    unfold deltaK
    have : 0 < 1 / (1 - θ) - 1 / (1 - θ / 2) := by linarith
    have : 0 < 1 - c := by linarith
    positivity
  have hδ1 : deltaK c θ < 1 := by
    unfold deltaK
    have : (1 - c) * (1 / (1 - θ) - 1 / (1 - θ / 2)) < 2 := by nlinarith
    nlinarith
  obtain ⟨B, c', hB, hc', hK⟩ := h10 θ (θ / 2) (3 / 4) (deltaK c θ) hδ0 hδ1 (by linarith)
    (by linarith) (by linarith) (by norm_num)
  obtain ⟨N0, hN0⟩ := classMembership_of_leaves h16a h16b γ c C θ h1 h2 hc0 hc1 hC0 hC1 hθ0 hθ1 hθC
  obtain ⟨N2, hN2⟩ := leaf_T2_large_one γ (c' / 100) h1 h2
  obtain ⟨B0, hB0⟩ := leaf_T2_small γ (c' / 100) (max N0 (max N2 2))
  refine ⟨c' / 100, max B0 (B + 1), by positivity, fun N hN α hlo hhi => ?_⟩
  have hFpos : 0 < F γ (2 * N) ^ (-c) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hαabs : 0 < |α| := lt_of_lt_of_le hFpos hlo
  have hnorm : ‖expSumF γ α N‖ = ‖expSumF γ |α| N‖ := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, norm_expSumF_neg]
  rw [hnorm]
  have hE : 0 ≤ (N : ℝ) * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by positivity
  by_cases hbig : max N0 (max N2 2) ≤ N
  · have hN0' : N0 ≤ N := le_trans (le_max_left _ _) hbig
    have hN2' : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbig
    have hN2'' : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hbig
    obtain ⟨hKC, hk1, hk10⟩ := hN0 N hN0' |α| hαabs hlo hhi
    have h1' := hK N hN (fun x => |α| * F γ x) (kN γ N) hKC
    have h2' := leaf_T2_conv γ c' h1 hc' N hN2'' (kN γ N) hk1 hk10
    have h3' := norm_Icc_le γ |α| N
    have h4' := hN2 N hN2'
    calc ‖expSumF γ |α| N‖
        ≤ B * (N : ℝ) ^ (1 - c' / (kN γ N : ℝ) ^ 2) + 1 := by linarith
      _ ≤ B * ((N : ℝ) * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)))
          + (N : ℝ) * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
          have := mul_le_mul_of_nonneg_left h2' hB.le
          linarith
      _ = (B + 1) * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by ring
      _ ≤ max B0 (B + 1) * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE
  · have hsmall := hB0 N hN (by omega)
    calc ‖expSumF γ |α| N‖ ≤ N + 1 := norm_expSumF_le γ |α| N
      _ ≤ B0 * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := hsmall
      _ ≤ max B0 (B + 1) * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE

/-- ASSEMBLY. Theorem 2 CONDITIONAL ON Lemma 10, which is CITED, and on the leaves of this
file only: Lemmas 11 to 16 are discharged by their assemblies above. -/
theorem theorem2_of_all_leaves (h10 : Lemma10) : Theorem2 :=
  theorem2_of_leaves h10
    (lemma16a_of_leaves lemma15_of_leaves)
    (lemma16b_of_leaves (lemma14_of_leaves (lemma13_of_leaves lemma11_of_leaves lemma12_of_leaves)))

theorem section8_derivative_inputs : Lemma11 ∧ Lemma12 ∧ Lemma13 ∧ Lemma14 ∧ Lemma15 ∧ Lemma16a ∧ Lemma16b := by
  have h11 := lemma11_of_leaves
  have h12 := lemma12_of_leaves
  have h13 := lemma13_of_leaves h11 h12
  have h14 := lemma14_of_leaves h13
  have h15 := lemma15_of_leaves
  exact ⟨h11, h12, h13, h14, h15, lemma16a_of_leaves h15, lemma16b_of_leaves h14⟩

end LeanLab.ExceptionalSet.U1539
