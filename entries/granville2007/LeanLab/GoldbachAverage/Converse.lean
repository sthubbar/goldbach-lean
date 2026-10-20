module

public import Mathlib
public import LeanLab.GoldbachAverage.Statements
public import LeanLab.GoldbachAverage.FromVonKoch
public import LeanLab.PNTPort.ZetaZeros.LogDerivZero
public import LeanLab.PNTPort.ZetaZeros.Sym

/-!
P0098 Granville 2007, the converse half of the Granville equivalence: AvgRH ⇒ RH.
Route, after Bhowmik, Halupczok, Matsumoto and Suzuki: the power series identity
Σ G(n) qⁿ = (Σ Λ(n) qⁿ)², an Abelian step from AvgRH to
Σ Λ(n) e^{-nt} = 1/t + O(t^{-1/2-ε}) as t → 0⁺, the Mellin transform of
Σ Λ(n) e^{-nt} − e^{-t}/t, which is Γ(s) L(Λ, s) − Γ(s − 1) for Re s > 1 and holomorphic on
Re s > 1/2, and the residue of ζ'/ζ at a zero.
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T1107Z-17600, unit U-1056.
Checked only by the Lean kernel. Binary Goldbach is OPEN; AvgRH is an average over n.
-/

@[expose] public section

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage.Converse

/-! ### Part A, the Abelian step -/

lemma vm_le (n : ℕ) : Λ n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (ArithmeticFunction.vonMangoldt_le_log).trans
      (Real.log_le_self (by exact_mod_cast hn.le))

lemma vm_nonneg (n : ℕ) : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg

lemma G_nonneg (n : ℕ) : 0 ≤ G n :=
  Finset.sum_nonneg fun p _ => mul_nonneg (vm_nonneg _) (vm_nonneg _)

lemma summable_vm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => ‖Λ n * q ^ n‖ := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ 1 * q ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (vm_nonneg n) (pow_nonneg hq0 n)), pow_one]
  exact mul_le_mul_of_nonneg_right (vm_le n) (pow_nonneg hq0 n)

/-- `L(q) = Σ Λ(n) qⁿ`. -/
def Lq (q : ℝ) : ℝ := ∑' n : ℕ, Λ n * q ^ n

lemma Lq_nonneg {q : ℝ} (hq0 : 0 ≤ q) : 0 ≤ Lq q :=
  tsum_nonneg fun n => mul_nonneg (vm_nonneg n) (pow_nonneg hq0 n)

/-- The power series identity `L(q)² = Σ G(n) qⁿ`. -/
lemma Lq_sq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Lq q ^ 2 = ∑' n : ℕ, G n * q ^ n := by
  rw [sq, Lq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_vm hq0 hq1)
    (summable_vm hq0 hq1)]
  refine tsum_congr fun n => ?_
  rw [G, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← hp', pow_add]; ring

lemma summable_G {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => G n * q ^ n := by
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm (summable_vm hq0 hq1)
    (summable_vm hq0 hq1)).of_norm
  refine h.congr fun n => ?_
  rw [G, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← hp', pow_add]; ring

/-- Partial sums `S(N) = Σ_{n ≤ N} G(n)`. -/
def S (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), G n

lemma summable_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable fun n : ℕ => ‖q ^ n‖ := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 _)] using
    summable_geometric_of_lt_one hq0 hq1

/-- Summation by parts: `Σ G(n) qⁿ = (1 − q) Σ S(N) q^N`. -/
lemma G_eq_S {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, G n * q ^ n = (1 - q) * ∑' N : ℕ, S N * q ^ N := by
  have hG : Summable fun n : ℕ => ‖G n * q ^ n‖ :=
    (summable_G hq0 hq1).congr fun n =>
      (Real.norm_of_nonneg (mul_nonneg (G_nonneg _) (pow_nonneg hq0 _))).symm
  have key := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hG (summable_geom hq0 hq1)
  rw [tsum_geometric_of_lt_one hq0 hq1] at key
  have h2 : ∀ N : ℕ, ∑ k ∈ range (N + 1), G k * q ^ k * q ^ (N - k) = S N * q ^ N := by
    intro N
    rw [S, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  simp_rw [h2] at key
  have h1q : (1 - q) ≠ 0 := by linarith
  rw [← key]; field_simp

/-- `Σ N(N+1)/2 q^N = q/(1 − q)³`. -/
lemma tri_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun N : ℕ => ((N : ℝ) * (N + 1) / 2) * q ^ N) (q / (1 - q) ^ 3) := by
  have hn : Summable fun n : ℕ => ‖(n : ℝ) * q ^ n‖ := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖q‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
    exact (this.congr fun n => by rw [pow_one]).congr fun n =>
      (Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _))).symm
  have key := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn (summable_geom hq0 hq1)
  have hsum : Summable fun N : ℕ => ∑ k ∈ range (N + 1), (k : ℝ) * q ^ k * q ^ (N - k) :=
    (summable_norm_sum_mul_range_of_summable_norm hn (summable_geom hq0 hq1)).of_norm
  have h2 : ∀ N : ℕ, ∑ k ∈ range (N + 1), (k : ℝ) * q ^ k * q ^ (N - k) =
      ((N : ℝ) * (N + 1) / 2) * q ^ N := by
    intro N
    have e : ∀ k ∈ range (N + 1), (k : ℝ) * q ^ k * q ^ (N - k) = (k : ℝ) * q ^ N := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
    congr 1
    have := Finset.sum_range_id_mul_two (N + 1)
    have h' : (∑ k ∈ range (N + 1), (k : ℝ)) * 2 = ((N + 1 : ℕ) : ℝ) * ((N + 1 - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast this
    simp only [Nat.add_sub_cancel] at h'
    push_cast at h'
    linarith
  simp_rw [h2] at key hsum
  rw [tsum_coe_mul_geometric_of_norm_lt_one
    (show ‖q‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1),
    tsum_geometric_of_lt_one hq0 hq1] at key
  have h1q : (1 - q) ≠ 0 := by linarith
  convert hsum.hasSum using 1
  rw [← key]; field_simp

lemma rpow_le_one_add_sq {y a : ℝ} (hy : 0 ≤ y) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    y ^ a ≤ 1 + y ^ 2 := by
  rcases le_total y 1 with h | h
  · have := Real.rpow_le_one hy h ha0; nlinarith [sq_nonneg y]
  · have h2 : y ^ a ≤ y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ha2
    rw [Real.rpow_two] at h2
    linarith

lemma sq_le_two_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ 2 * exp y := by
  have := Real.quadratic_le_exp_of_nonneg hy
  nlinarith

lemma exp_neg_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : exp (-x) ≤ 1 - x / 2 := by
  have h := Real.add_one_le_exp x
  have key : 1 ≤ (1 - x / 2) * exp x := by
    nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - x / 2)]
  have e : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [mul_le_mul_of_nonneg_left key (Real.exp_pos (-x)).le]

lemma term_bound {a t : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (ht : 0 < t) (N : ℕ) :
    (N : ℝ) ^ a * exp (-t) ^ N ≤ 3 * (2 / t) ^ a * exp (-t / 2) ^ N := by
  set y : ℝ := N * t / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hN : (N : ℝ) = 2 / t * y := by rw [hy]; field_simp
  have hya : y ^ a ≤ 3 * exp y := by
    have h1 := rpow_le_one_add_sq hy0 ha0 ha2
    have h2 := sq_le_two_exp hy0
    have h3 : 1 ≤ exp y := Real.one_le_exp hy0
    linarith
  rw [hN, Real.mul_rpow (by positivity) hy0]
  have e1 : exp (-t) ^ N = exp (-(2 * y)) := by
    rw [← Real.exp_nat_mul, hy]; congr 1; ring
  have e2 : exp (-t / 2) ^ N = exp (-y) := by
    rw [← Real.exp_nat_mul, hy]; congr 1; ring
  rw [e1, e2]
  have e3 : exp y * exp (-(2 * y)) = exp (-y) := by rw [← Real.exp_add]; congr 1; ring
  have hp : 0 ≤ (2 / t) ^ a := by positivity
  calc (2 / t) ^ a * y ^ a * exp (-(2 * y)) ≤ (2 / t) ^ a * (3 * exp y) * exp (-(2 * y)) := by
        gcongr
    _ = 3 * (2 / t) ^ a * (exp y * exp (-(2 * y))) := by ring
    _ = 3 * (2 / t) ^ a * exp (-y) := by rw [e3]

lemma summable_rpow_geom {a t : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (ht : 0 < t) :
    Summable fun N : ℕ => (N : ℝ) ^ a * exp (-t) ^ N := by
  have hr0 : 0 ≤ exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : exp (-t / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun N => by positivity) (term_bound ha0 ha2 ht)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _)

lemma rpow_geom {a t : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∑' N : ℕ, (N : ℝ) ^ a * exp (-t) ^ N ≤ 48 * t ^ (-a) / t := by
  have hr0 : 0 ≤ exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : exp (-t / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left (3 * (2 / t) ^ a)
  have h1 := Summable.tsum_le_tsum (term_bound ha0 ha2 ht) (summable_rpow_geom ha0 ha2 ht) hs
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at h1
  have hgap : t / 4 ≤ 1 - exp (-t / 2) := by
    have := exp_neg_le (x := t / 2) (by linarith) (by linarith)
    rw [show -(t / 2) = -t / 2 by ring] at this; linarith
  have h2a : (2 / t) ^ a = 2 ^ a * t ^ (-a) := by
    rw [Real.div_rpow (by norm_num) ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  have h2le : (2 : ℝ) ^ a ≤ 4 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 4 := by norm_num
  have hta : 0 ≤ t ^ (-a) := Real.rpow_nonneg ht.le _
  have hpos : 0 < 1 - exp (-t / 2) := by linarith
  calc ∑' N : ℕ, (N : ℝ) ^ a * exp (-t) ^ N ≤ 3 * (2 / t) ^ a * (1 - exp (-t / 2))⁻¹ := h1
    _ ≤ 3 * (4 * t ^ (-a)) * (4 / t) := by
        rw [h2a]
        gcongr
        · rw [inv_le_comm₀ hpos (by positivity)]; rw [inv_div]; linarith
    _ = 48 * t ^ (-a) / t := by ring

/-- `|q/(1 − q)² − 1/t²| ≤ 1/2` for `q = e^{-t}`, `0 < t ≤ 1`. -/
lemma geom_main {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |exp (-t) / (1 - exp (-t)) ^ 2 - 1 / t ^ 2| ≤ 1 / 2 := by
  set u := exp (t / 2) - exp (-(t / 2)) with hu
  have hsinh : u = 2 * Real.sinh (t / 2) := by rw [Real.sinh_eq, hu]; ring
  have htu : t ≤ u := by
    have := (Real.self_le_sinh_iff (x := t / 2)).mpr (by linarith); rw [hsinh]; linarith
  have hu0 : 0 < u := by linarith
  have hq : exp (-t) / (1 - exp (-t)) ^ 2 = 1 / u ^ 2 := by
    have e1 : exp (t / 2) * (1 - exp (-t)) = u := by
      rw [hu, mul_sub, mul_one, ← Real.exp_add]; congr 2; ring
    have e2 : exp (-t) * exp (t / 2) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num; ring_nf
    have h1 : 0 < 1 - exp (-t) := by
      have := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith); linarith
    rw [← e1]; field_simp; nlinarith [e2]
  have hu2 : u ^ 2 ≤ t ^ 2 + t ^ 4 / 2 := by
    have e : u ^ 2 = 2 * Real.cosh t - 2 := by
      rw [hu, Real.cosh_eq]; ring_nf
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf; rw [Real.exp_zero]; ring
    have hc := Real.cosh_le_exp_half_sq t
    have hy : |t ^ 2 / 2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; nlinarith
    have hb := Real.abs_exp_sub_one_sub_id_le hy
    rw [abs_le] at hb
    nlinarith [hb.2]
  rw [hq]
  have e : 1 / u ^ 2 - 1 / t ^ 2 = -((u ^ 2 - t ^ 2) / (u ^ 2 * t ^ 2)) := by
    field_simp; ring
  have hut : t ^ 2 ≤ u ^ 2 := by nlinarith
  rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul hut hut (by positivity) (by positivity)]

lemma S_zero : S 0 = 0 := by simp [S, G]

/-- **The Abelian step**: AvgRH gives `Σ G(n) e^{-nt} = 1/t² + O(t^{-3/2-ε})` on `(0, 1]`. -/
theorem abelian (H : AvgRH) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      |∑' n : ℕ, G n * exp (-t) ^ n - 1 / t ^ 2| ≤ C * t ^ (-(3 / 2 + ε)) := by
  obtain ⟨K, hK⟩ := H ε hε
  set a : ℝ := 3 / 2 + ε with ha
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha2 : a ≤ 2 := by linarith
  have hK0 : 0 ≤ K := by
    have h := hK 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  set e : ℕ → ℝ := fun N => S N - (N : ℝ) * (N + 1) / 2 with he_def
  have he : ∀ N : ℕ, |e N| ≤ (K + 1) * (N : ℝ) ^ a := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [e, S_zero, Nat.cast_zero]
      norm_num
      exact mul_nonneg (by linarith) (Real.rpow_nonneg le_rfl _)
    · have h1 : |S N - (N : ℝ) ^ 2 / 2| ≤ K * (N : ℝ) ^ a := hK N hN
      have hNa : (N : ℝ) ≤ (N : ℝ) ^ a := by
        have := Real.rpow_le_rpow_of_exponent_le (x := (N : ℝ)) (by exact_mod_cast hN) ha1
        rwa [Real.rpow_one] at this
      have e1 : e N = (S N - (N : ℝ) ^ 2 / 2) - (N : ℝ) / 2 := by simp only [e]; ring
      rw [e1]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc |S N - (N : ℝ) ^ 2 / 2 - (N : ℝ) / 2| ≤ |S N - (N : ℝ) ^ 2 / 2| + |(N : ℝ) / 2| :=
            abs_sub _ _
        _ ≤ K * (N : ℝ) ^ a + (N : ℝ) ^ a := by
            have h2 : |(N : ℝ) / 2| = (N : ℝ) / 2 := abs_of_nonneg (by positivity)
            linarith
        _ = (K + 1) * (N : ℝ) ^ a := by ring
  refine ⟨1 / 2 + 48 * (K + 1), fun t ht ht1 => ?_⟩
  set q := exp (-t) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := summable_rpow_geom ha0 ha2 ht
  have hbound : ∀ N : ℕ, ‖e N * q ^ N‖ ≤ (K + 1) * ((N : ℝ) ^ a * q ^ N) := by
    intro N
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 N), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (he N) (pow_nonneg hq0 N)
  have hsum_e : Summable fun N : ℕ => e N * q ^ N :=
    Summable.of_norm_bounded (hgeo.mul_left (K + 1)) hbound
  have hT := tri_sum hq0 hq1
  have hS : ∑' N : ℕ, S N * q ^ N = q / (1 - q) ^ 3 + ∑' N : ℕ, e N * q ^ N := by
    rw [← hT.tsum_eq, ← Summable.tsum_add hT.summable hsum_e]
    refine tsum_congr fun N => ?_
    simp only [e]; ring
  rw [G_eq_S hq0 hq1, hS]
  set E := ∑' N : ℕ, e N * q ^ N with hE_def
  have hE : |E| ≤ (K + 1) * (48 * t ^ (-a) / t) := by
    calc |E| = ‖E‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' N : ℕ, (K + 1) * ((N : ℝ) ^ a * q ^ N) :=
          tsum_of_norm_bounded (hgeo.mul_left (K + 1)).hasSum hbound
      _ = (K + 1) * ∑' N : ℕ, (N : ℝ) ^ a * q ^ N := tsum_mul_left
      _ ≤ (K + 1) * (48 * t ^ (-a) / t) := by
          gcongr; exact rpow_geom ha0 ha2 ht ht1
  have h1q : 1 - q ≤ t := by have := Real.add_one_le_exp (-t); linarith
  have h1q0 : 0 < 1 - q := by linarith
  have hgm := geom_main ht ht1
  rw [← hq] at hgm
  have expand : (1 - q) * (q / (1 - q) ^ 3 + E) - 1 / t ^ 2 =
      (q / (1 - q) ^ 2 - 1 / t ^ 2) + (1 - q) * E := by
    field_simp; ring
  rw [expand]
  have hta : 1 ≤ t ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  have hta0 : 0 ≤ t ^ (-a) := by linarith
  have h2 : |(1 - q) * E| ≤ 48 * (K + 1) * t ^ (-a) := by
    rw [abs_mul, abs_of_pos h1q0]
    calc (1 - q) * |E| ≤ t * ((K + 1) * (48 * t ^ (-a) / t)) :=
          mul_le_mul h1q hE (abs_nonneg _) ht.le
      _ = 48 * (K + 1) * t ^ (-a) := by field_simp
  calc |q / (1 - q) ^ 2 - 1 / t ^ 2 + (1 - q) * E|
      ≤ |q / (1 - q) ^ 2 - 1 / t ^ 2| + |(1 - q) * E| := abs_add_le _ _
    _ ≤ 1 / 2 + 48 * (K + 1) * t ^ (-a) := add_le_add hgm h2
    _ ≤ (1 / 2 + 48 * (K + 1)) * t ^ (-a) := by nlinarith

/-- `φ(t) = Σ Λ(n) e^{-nt}`. -/
def phi (t : ℝ) : ℝ := Lq (exp (-t))

/-- **AvgRH ⇒ φ(t) = 1/t + O(t^{-1/2-ε})** on `(0, 1]`. -/
theorem phi_near_zero (H : AvgRH) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → |phi t - 1 / t| ≤ C * t ^ (-(1 / 2 + ε)) := by
  obtain ⟨C, hC⟩ := abelian H hε hε2
  refine ⟨C, fun t ht ht1 => ?_⟩
  have hq0 : 0 ≤ exp (-t) := (Real.exp_pos _).le
  have hq1 : exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := hC t ht ht1
  rw [← Lq_sq hq0 hq1] at h
  have hφ0 : 0 ≤ phi t := Lq_nonneg hq0
  have hX : 0 ≤ C * t ^ (-(3 / 2 + ε)) := (abs_nonneg _).trans h
  have hpos : 0 < phi t + 1 / t := by positivity
  have hfac : |phi t - 1 / t| * (phi t + 1 / t) = |Lq (exp (-t)) ^ 2 - 1 / t ^ 2| := by
    rw [← abs_of_pos hpos, ← abs_mul]; congr 1; simp only [phi]; ring
  have h1 : |phi t - 1 / t| ≤ C * t ^ (-(3 / 2 + ε)) / (phi t + 1 / t) := by
    rw [le_div_iff₀ hpos, hfac]; exact h
  have h2 : C * t ^ (-(3 / 2 + ε)) / (phi t + 1 / t) ≤ C * t ^ (-(3 / 2 + ε)) / (1 / t) :=
    div_le_div_of_nonneg_left hX (by positivity) (by linarith)
  have h3 : C * t ^ (-(3 / 2 + ε)) / (1 / t) = C * t ^ (-(1 / 2 + ε)) := by
    rw [one_div, div_inv_eq_mul, mul_assoc, ← Real.rpow_add_one ht.ne']; congr 2; ring
  linarith

/-! ### Part C, the Mellin transform -/

open Complex MeasureTheory Filter Asymptotics Topology Set

/-- `F(t) = φ(t) − e^{-t}/t`, as a complex function. -/
def Fc (t : ℝ) : ℂ := ((phi t - Real.exp (-t) / t : ℝ) : ℂ)

lemma phi_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => ((Λ n : ℝ) : ℂ) * ((Real.exp (-(n : ℝ) * t) : ℝ) : ℂ)) ((phi t : ℝ) : ℂ) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (summable_vm hq0 hq1).of_norm.hasSum
  have e : ∀ n : ℕ, Real.exp (-(n : ℝ) * t) = Real.exp (-t) ^ n := by
    intro n; rw [← Real.exp_nat_mul]; ring_nf
  simp_rw [e, ← Complex.ofReal_mul]
  exact Complex.hasSum_ofReal.mpr h

lemma mellin_phi {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => ((phi t : ℝ) : ℂ)) s = Gamma s * LSeries (fun n => ((Λ n : ℝ) : ℂ)) s := by
  have hp : ∀ n : ℕ, ((Λ n : ℝ) : ℂ) = 0 ∨ 0 < (n : ℝ) := by
    intro n; rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp
    · right; exact_mod_cast hn
  have hsum : Summable fun n : ℕ => ‖((Λ n : ℝ) : ℂ)‖ / (n : ℝ) ^ s.re := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    refine (h.norm).congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne']
  have h := hasSum_mellin hp (by linarith) (fun t ht => phi_hasSum ht) hsum
  rw [← h.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne', Complex.ofReal_natCast, mul_div_assoc]

lemma integrand_E {s : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) • ((Real.exp (-t) / t : ℝ) : ℂ) =
      ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (s - 1 - 1) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [smul_eq_mul, Complex.ofReal_div]
  conv_rhs => rw [Complex.cpow_sub _ _ htc, Complex.cpow_one]
  ring

lemma mellinConvergent_E {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t => ((Real.exp (-t) / t : ℝ) : ℂ)) s := by
  have h := Complex.GammaIntegral_convergent (s := s - 1) (by simp; linarith)
  refine h.congr_fun (fun t ht => (integrand_E ht).symm) measurableSet_Ioi

lemma mellin_E {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => ((Real.exp (-t) / t : ℝ) : ℂ)) s = Gamma (s - 1) := by
  rw [Complex.Gamma_eq_integral (by simp; linarith), Complex.GammaIntegral]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => integrand_E ht)

lemma phi_cont : ContinuousOn phi (Ioi 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  have hr0 : 0 ≤ Real.exp (-(t0 / 2)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(t0 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hon : ContinuousOn phi (Ioi (t0 / 2)) := by
    have hc := continuousOn_tsum (f := fun (n : ℕ) (t : ℝ) => Λ n * Real.exp (-t) ^ n)
      (s := Ioi (t0 / 2)) (u := fun n : ℕ => ‖Λ n * Real.exp (-(t0 / 2)) ^ n‖)
      (fun n => by fun_prop) (summable_vm hr0 hr1) (fun n t ht => ?_)
    · exact hc
    · have ht' : t0 / 2 < t := ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      gcongr
  exact (hon.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma Fc_cont : ContinuousOn Fc (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => phi t - Real.exp (-t) / t) (Ioi 0) := by
    refine phi_cont.sub ?_
    refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
    intro t ht; exact (ne_of_gt ht)
  exact Complex.continuous_ofReal.comp_continuousOn h1

lemma Fc_loc : LocallyIntegrableOn Fc (Ioi 0) :=
  Fc_cont.locallyIntegrableOn measurableSet_Ioi

lemma phi_le {t : ℝ} (ht : 1 ≤ t) : |phi t| ≤ 4 * Real.exp (-t) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnorm : ‖Real.exp (-t)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  show |Lq (Real.exp (-t))| ≤ _
  rw [abs_of_nonneg (Lq_nonneg hq0)]
  have hsn : Summable fun n : ℕ => (n : ℝ) * Real.exp (-t) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h1 : phi t ≤ ∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n :=
    Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (vm_le n) (pow_nonneg hq0 n))
      (summable_vm hq0 hq1).of_norm hsn
  rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm] at h1
  have he : Real.exp (-t) ≤ 1 / 2 := by
    have := Real.add_one_le_exp t
    have e : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-t)]
  have h2 : Real.exp (-t) / (1 - Real.exp (-t)) ^ 2 ≤ 4 * Real.exp (-t) := by
    have hq' : 1 / 4 ≤ (1 - Real.exp (-t)) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]; nlinarith [mul_le_mul_of_nonneg_left hq' hq0]
  have h1' : Lq (Real.exp (-t)) ≤ Real.exp (-t) / (1 - Real.exp (-t)) ^ 2 := h1
  linarith

lemma Fc_top : Fc =O[atTop] fun t => Real.exp (-1 * t) := by
  refine IsBigO.of_bound 5 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Fc, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    neg_one_mul]
  have h1 := phi_le ht
  have h2 : |Real.exp (-t) / t| ≤ Real.exp (-t) := by
    rw [abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith)]
    exact div_le_self (Real.exp_pos _).le ht
  calc |phi t - Real.exp (-t) / t| ≤ |phi t| + |Real.exp (-t) / t| := abs_sub _ _
    _ ≤ 5 * Real.exp (-t) := by linarith

lemma Fc_bot (H : AvgRH) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Fc =O[𝓝[>] 0] fun t => t ^ (-(1 / 2 + ε)) := by
  obtain ⟨C, hC⟩ := phi_near_zero H hε hε2
  refine IsBigO.of_bound (|C| + 1) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with t ht ht1
  have ht' : 0 < t := ht
  have ht1' : t ≤ 1 := le_of_lt ht1
  rw [Fc, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht'.le _)]
  have hb : 1 ≤ t ^ (-(1 / 2 + ε)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht' ht1' (by linarith)
  have h1 := hC t ht' ht1'
  have h2 : |1 / t - Real.exp (-t) / t| ≤ 1 := by
    have hx : 1 / t - Real.exp (-t) / t = (1 - Real.exp (-t)) / t := by ring
    have hle : 1 - Real.exp (-t) ≤ t := by have := Real.add_one_le_exp (-t); linarith
    have hge : 0 ≤ 1 - Real.exp (-t) := by
      have := Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith); linarith
    rw [hx, abs_of_nonneg (div_nonneg hge ht'.le), div_le_one ht']; exact hle
  have h3 : C * t ^ (-(1 / 2 + ε)) ≤ |C| * t ^ (-(1 / 2 + ε)) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  calc |phi t - Real.exp (-t) / t| ≤ |phi t - 1 / t| + |1 / t - Real.exp (-t) / t| := abs_sub_le _ _ _
    _ ≤ (|C| + 1) * t ^ (-(1 / 2 + ε)) := by nlinarith

/-- `mellin F` is holomorphic on `Re s > 1/2`. -/
theorem mellin_Fc_diff (H : AvgRH) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (mellin Fc) s := by
  set ε := min ((s.re - 1 / 2) / 2) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε2 : ε ≤ 1 / 2 := min_le_right _ _
  have hεs : 1 / 2 + ε < s.re := by
    have := min_le_left ((s.re - 1 / 2) / 2) (1 / 2); linarith
  exact mellin_differentiableAt_of_isBigO_rpow_exp one_pos Fc_loc Fc_top
    ((Fc_bot H hε0 hε2).congr_right fun t => by rw [neg_neg]) (by simpa using hεs)

/-- For `Re s > 1`: `mellin F (s) = Γ(s) L(Λ, s) − Γ(s − 1)`. -/
theorem mellin_Fc_eq (H : AvgRH) {s : ℂ} (hs : 1 < s.re) :
    mellin Fc s = Gamma s * LSeries (fun n => ((Λ n : ℝ) : ℂ)) s - Gamma (s - 1) := by
  have hεs : 1 / 2 + 1 / 4 < s.re := by linarith
  have hconvF : MellinConvergent Fc s :=
    mellinConvergent_of_isBigO_rpow_exp one_pos Fc_loc Fc_top
      ((Fc_bot H (ε := 1 / 4) (by norm_num) (by norm_num)).congr_right fun t => by rw [neg_neg])
      (by simpa using hεs)
  have hconvE := mellinConvergent_E hs
  have hsplit : mellin (fun t => ((phi t : ℝ) : ℂ)) s =
      mellin Fc s + mellin (fun t => ((Real.exp (-t) / t : ℝ) : ℂ)) s := by
    unfold mellin
    rw [← integral_add hconvF hconvE]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Fc, smul_eq_mul, ← mul_add, ← Complex.ofReal_add]
    congr 2; ring
  rw [mellin_phi hs, mellin_E hs] at hsplit
  rw [hsplit]; ring

/-! ### Part D, no zero of ζ with Re s > 1/2 -/

/-- `H(s) = (mellin F(s) + Γ(s − 1)) ζ(s) + Γ(s) ζ'(s)`, zero for `Re s > 1`. -/
def Hf (s : ℂ) : ℂ :=
  (mellin Fc s + Gamma (s - 1)) * riemannZeta s + Gamma s * deriv riemannZeta s

/-- The slit half plane `Re s > 1/2` minus the real ray `[1, ∞)`. -/
def Vset : Set ℂ := {s | 1 / 2 < s.re} \ {s | s.im = 0 ∧ 1 ≤ s.re}

lemma V_eq : Vset = (({s : ℂ | 1 / 2 < s.re} ∩ {s | 0 < s.im}) ∪
    ({s : ℂ | 1 / 2 < s.re} ∩ {s | s.re < 1})) ∪ ({s : ℂ | 1 / 2 < s.re} ∩ {s | s.im < 0}) := by
  ext s
  simp only [Vset, mem_diff, mem_setOf_eq, mem_union, mem_inter_iff, not_and, not_le]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy s.im 0 with h | h | h
    · right; exact ⟨h1, h⟩
    · left; right; exact ⟨h1, h2 h⟩
    · left; left; exact ⟨h1, h⟩
  · rintro ((⟨h1, h⟩ | ⟨h1, h⟩) | ⟨h1, h⟩)
    · exact ⟨h1, fun h' => absurd h' (ne_of_gt h)⟩
    · exact ⟨h1, fun _ => h⟩
    · exact ⟨h1, fun h' => absurd h' (ne_of_lt h)⟩

lemma V_open : IsOpen Vset := by
  refine IsOpen.sdiff (isOpen_lt continuous_const Complex.continuous_re) ?_
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

lemma V_preconn : IsPreconnected Vset := by
  rw [V_eq]
  have hA := ((convex_halfSpace_re_gt (1 / 2 : ℝ)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC := ((convex_halfSpace_re_gt (1 / 2 : ℝ)).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hB := ((convex_halfSpace_re_gt (1 / 2 : ℝ)).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hAC := hA.union (⟨3 / 4, 1⟩ : ℂ) (by constructor <;> simp <;> norm_num)
    (by constructor <;> simp <;> norm_num) hC
  exact hAC.union (⟨3 / 4, -1⟩ : ℂ) (Or.inr (by constructor <;> simp <;> norm_num))
    (by constructor <;> simp <;> norm_num) hB

lemma ne_neg_nat_of_re_pos {s : ℂ} (h : 0 < s.re) (m : ℕ) : s ≠ -m := by
  intro hm
  have := congrArg Complex.re hm
  simp at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma Hf_diff (H : AvgRH) : DifferentiableOn ℂ Hf Vset := by
  intro s hs
  have hre : 1 / 2 < s.re := hs.1
  have hs2 := hs.2
  simp only [mem_setOf_eq, not_and, not_le] at hs2
  have hs1 : s ≠ 1 := by intro h; have := hs2 (by rw [h]; simp); rw [h] at this; simp at this
  have hG1 : ∀ m : ℕ, s - 1 ≠ -m := by
    intro m hm
    have him : s.im = 0 := by have := congrArg Complex.im hm; simpa using this
    have hre' : s.re = 1 - m := by have := congrArg Complex.re hm; simp at this; linarith
    have hlt := hs2 him
    have hm0 : (m : ℝ) < 1 / 2 := by linarith
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm' : m = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    rw [hm'] at hre'; simp at hre'; linarith
  have hζ : AnalyticAt ℂ riemannZeta s := analyticAt_riemannZeta hs1
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun z => Complex.Gamma (z - 1)) s :=
    (Complex.differentiableAt_Gamma _ hG1).comp s (differentiableAt_id.sub_const 1)
  have h2 : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos (by linarith))
  exact (((mellin_Fc_diff H hre).add h1).mul hζ.differentiableAt).add
    (h2.mul hζ.deriv.differentiableAt)

lemma Hf_zero_right {s : ℂ} (H : AvgRH) (hs : 1 < s.re) : Hf s = 0 := by
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [Hf, mellin_Fc_eq H hs, sub_add_cancel,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  field_simp
  ring

lemma Hf_eqOn (H : AvgRH) : EqOn Hf 0 Vset := by
  have hA : AnalyticOnNhd ℂ Hf Vset := (Hf_diff H).analyticOnNhd V_open
  have hz0 : (⟨2, 1⟩ : ℂ) ∈ Vset := by
    refine ⟨by simp; norm_num, ?_⟩
    simp
  refine hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero V_preconn hz0 ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (⟨2, 1⟩ : ℂ).re by norm_num)] with s hs
  exact Hf_zero_right H hs

/-- **AvgRH ⇒ no zero of ζ with `1/2 < Re ρ < 1`.** -/
theorem no_zero_right (H : AvgRH) {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : False := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hρV : ρ ∈ Vset := by
    refine ⟨h0, ?_⟩
    simp only [mem_setOf_eq, not_and, not_le]
    intro _; exact h1
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ1
  -- the order is finite and at least 1
  have hU : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz => analyticAt_riemannZeta hz
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    simp
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    hU.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := ρ)
      (by simp) (by simpa using hρ1) h2
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    have : analyticOrderAt riemannZeta ρ = 0 := by rw [← hm]; rfl
    rw [analyticOrderAt_eq_zero] at this
    rcases this with h' | h'
    · exact h' hζ
    · exact h' hz
  have hlim := LeanLab.PNTPort.ZetaZeros.tendsto_mul_logDeriv hζ hm.symm
  -- ζ is nonzero near ρ, off ρ
  have hne : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 := by
    rcases hζ.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) htop
    · exact h
  -- but by `H = 0`, `(s − ρ) ζ'/ζ = −(s − ρ)(mellin F + Γ(s − 1))/Γ(s)` near `ρ`
  set g : ℂ → ℂ := fun s => -((s - ρ) * (mellin Fc s + Gamma (s - 1)) / Gamma s) with hg
  have hVn : Vset ∈ 𝓝 ρ := V_open.mem_nhds hρV
  have hev : ∀ᶠ s in 𝓝[≠] ρ, (s - ρ) * (deriv riemannZeta s / riemannZeta s) = g s := by
    filter_upwards [hne, nhdsWithin_le_nhds hVn] with s hs hsV
    have hH := Hf_eqOn H hsV
    simp only [Hf, Pi.zero_apply] at hH
    have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by have : 1 / 2 < s.re := hsV.1; linarith)
    simp only [hg]
    field_simp
    linear_combination (s - ρ) * hH
  have hgc : ContinuousAt g ρ := by
    have hΓ : Gamma ρ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hGd : DifferentiableAt ℂ (fun z => Complex.Gamma (z - 1)) ρ := by
      have := (Hf_diff H)
      have hG1 : ∀ k : ℕ, ρ - 1 ≠ -k := by
        intro k hk
        have hr := congrArg Complex.re hk
        simp at hr
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0] at hr; simp at hr; linarith
        · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
          linarith
      exact (Complex.differentiableAt_Gamma _ hG1).comp ρ (differentiableAt_id.sub_const 1)
    have hGa : DifferentiableAt ℂ Complex.Gamma ρ :=
      Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos (by linarith))
    exact (((continuousAt_id.sub continuousAt_const).mul
      ((mellin_Fc_diff H h0).continuousAt.add hGd.continuousAt)).div hGa.continuousAt hΓ).neg
  have hg0 : g ρ = 0 := by simp [hg]
  have hlim2 : Tendsto g (𝓝[≠] ρ) (𝓝 0) := by
    rw [← hg0]; exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique (hlim.congr' hev) hlim2
  exact hm0 (by exact_mod_cast this)

open LeanLab.PNTPort.ZetaZeros in
/-- `ζ(s) ≠ 0` for real `s ≤ 0` that is not a trivial zero. -/
lemma zeta_ne_zero_real_nonpos {s : ℂ} (hre : s.re ≤ 0) (him : s.im = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : riemannZeta s ≠ 0 := by
  by_cases hs0 : s = 0
  · rw [hs0, riemannZeta_zero]; norm_num
  set w := 1 - s with hw
  have hw0 : 1 ≤ w.re := by rw [hw]; simp; linarith
  have hw1 : w ≠ 1 := by intro h; apply hs0; rw [hw] at h; linear_combination -h
  have hodd : ∀ k : ℤ, w ≠ 2 * k + 1 := by
    intro k hk
    have hsk : s = -2 * k := by rw [hw] at hk; linear_combination -hk
    have hr : s.re = -2 * k := by rw [hsk]; simp
    rcases lt_trichotomy k 0 with h | h | h
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      linarith
    · apply hs0; rw [hsk, h]; simp
    · apply htriv
      refine ⟨(k - 1).toNat, ?_⟩
      have hk1 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
        have := congrArg (fun z : ℤ => (z : ℂ)) hk1
        simpa using this
      rw [hc, hsk]; ring
  have e := riemannZeta_one_sub (not_neg_nat_of_re_pos (by linarith : 0 < w.re)) hw1
  rw [show 1 - w = s by rw [hw]; ring] at e
  rw [e]
  have hF : feF w ≠ 0 := feF_ne_zero (by linarith) hodd
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw0
  have : 2 * (2 * (π : ℂ)) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w =
      feF w * riemannZeta w := by rw [feF]
  rw [this]
  exact mul_ne_zero hF hζw

open LeanLab.PNTPort.ZetaZeros in
/-- **AvgRH ⇒ RH**, unconditional. -/
theorem rh_of_avgRH (H : AvgRH) : RiemannHypothesis := by
  intro s hz htriv hs1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · by_cases h0 : 0 < s.re
    · exact no_zero_right H (ρ := 1 - s) (by simp; linarith) (by simp; linarith)
        (zeta_one_sub_eq_zero h0 (by linarith) hz)
    · push_neg at h0
      by_cases him : s.im = 0
      · exact zeta_ne_zero_real_nonpos h0 him htriv hz
      · exact zeta_ne_zero_of_re_nonpos h0 him hz
  · by_cases h1 : s.re < 1
    · exact no_zero_right H hgt h1 hz
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1) hz

/-- **The Granville equivalence, both directions, with no cited input**:
RH ⇔ `Σ_{n ≤ N} G(n) = N²/2 + O(N^{3/2+ε})` for every `ε > 0`. -/
theorem granville_equiv_proved : GranvilleEquiv :=
  ⟨avgRH_of_RH, rh_of_avgRH⟩

end LeanLab.GoldbachAverage.Converse
