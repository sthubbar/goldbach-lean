module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-19, run 20261019T1703Z-20733, unit U-1084, T2 FRONTIER, I-0073.
Li, Liu, "6 powers of 2 in the Linnik-Goldbach problem", arXiv 2610.15784 v1, 2026-10-11,
read in Claude in Chrome on arxiv.org/html/2610.15784v1, Sections 3, 5.2, 6 and 7.

The paper proves K = 6 unconditionally and K = 5 on GRH. This file checks every finite
numerical step of Sections 3, 6 and 7:
- `numer_*`: the integer recipe of Section 3, n_j(r) and Ramanujan sums c_q, kernel computed
  for q = 3, 5, 7, 15, 31; `A_*_eq` turns them into the five printed Gram matrices, all MATCH.
- `vAv_star`, `wAw_4vAv_star`: the two exact rationals printed in (59) and (66), MATCH.
- `Astar_diag`, `tail_*`: the diagonal sums and the tail bounds of (23), MATCH.
- `k6_criterion`, `k6_final`: criterion (58) with a = 1/4, b = 1/16 from the cited inputs
  C₀R₀ < 1.279, C₁ = 6.7814, the cited diagonal bounds (22), and H < 2/15 of (61); the
  final 1/128.
- `k5_criterion`, `k5_final`: criterion (65) on GRH with c = 1/8, τ = 2, H < 41/60 of (67);
  the final 1/320.
- `gamma6`, `gamma5`: N^{-γ} exponents, γ₆ > 7/12 and γ₅ > 1/2, from Mathlib's log 2 bound.
- `I56`, `I2532`: I(5/6) > 81/200 and I(25/32) > 347/1000, equation (49), from Mathlib's
  log 2 bounds and the log(1 - x) series; true values 0.406311 and 0.347941.
- `region61`, `region67`: the maxima (61) and (67) over the regions D_λ of (51), exact,
  for every z in D_{5/6} and D_{25/32}; true maxima 0.130555 and 0.680557 at z = β_λ.
Inputs kept as hypotheses, cited from earlier papers: C₀R₀ < 1.279, C₁ = 6.7814, the
diagonal bounds (22). Python recomputation in numerics/liliu_U1084.py, all MATCH.
The analytic content, Propositions 5.2, Lemma 2.1, Lemma 4.3, the arcs, is not formalized.
No error found. Goldbach is open.
-/

@[expose] public section

open Real

namespace LeanLab.Linnik.LiLiu

/-! ### Section 3, the integer recipe -/

/-- H_q = {2^t mod q : 1 ≤ t ≤ ε(q)}. -/
def Hq (q e : ℕ) : List ℕ := (List.range e).map (fun t => 2 ^ (t + 1) % q)

/-- n_{j+1}(r) = Σ_{h ∈ H_q} n_j(r - h). -/
def step (q : ℕ) (H : List ℕ) (n : List ℤ) : List ℤ :=
  (List.range q).map fun r => (H.map fun h => n.getD ((r + q - h) % q) 0).sum

def nvec (q e : ℕ) : ℕ → List ℤ
  | 0 => (List.range q).map (fun r => if r = 0 then 1 else 0)
  | j + 1 => step q (Hq q e) (nvec q e j)

/-- Möbius on the quotients q/d that occur for q ∈ {3, 5, 7, 15, 31}. -/
def mob : ℕ → ℤ
  | 1 => 1
  | 15 => 1
  | _ => -1

/-- The Ramanujan sum c_q(t) = Σ_{d | (q, t)} d μ(q/d), for the five moduli. -/
def ram (q t : ℕ) : ℤ :=
  (((List.range (q + 1)).filter (fun d => d ≠ 0 ∧ q % d = 0 ∧ t % d = 0)).map
    (fun d : ℕ => (d : ℤ) * mob (Nat.div q d))).sum

/-- Σ_{r,s mod q} n_i(r) n_j(s) c_q(r - s). -/
def numer (q e i j : ℕ) : ℤ :=
  ((List.range q).map fun r => ((List.range q).map fun s =>
    (nvec q e i).getD r 0 * (nvec q e j).getD s 0 * ram q ((r + q - s) % q)).sum).sum

/-- A_{ij}(q) = numer / (φ(q)² ε(q)^{i+j}). -/
def Aq (q e ph i j : ℕ) : ℚ := (numer q e i j : ℚ) / ((ph : ℚ) ^ 2 * (e : ℚ) ^ (i + j))

theorem numer_3 : (List.range 3).map (fun i => (List.range 3).map fun j => numer 3 2 (i+1) (j+1))
    = [[2, -2, 2], [-2, 2, -2], [2, -2, 2]] := by decide +kernel
theorem numer_5 : (List.range 3).map (fun i => (List.range 3).map fun j => numer 5 4 (i+1) (j+1))
    = [[4, -4, 4], [-4, 4, -4], [4, -4, 4]] := by decide +kernel
theorem numer_7 : (List.range 3).map (fun i => (List.range 3).map fun j => numer 7 3 (i+1) (j+1))
    = [[12, -6, -18], [-6, 24, -12], [-18, -12, 48]] := by decide +kernel
theorem numer_15 : (List.range 3).map (fun i => (List.range 3).map fun j =>
    numer 15 4 (i+1) (j+1)) = [[32, 16, -112], [16, 128, 64], [-112, 64, 512]] := by decide +kernel
theorem numer_31 : (List.range 3).map (fun i => (List.range 3).map fun j =>
    numer 31 5 (i+1) (j+1)) = [[130, 30, -160], [30, 770, 440], [-160, 440, 4990]] := by decide +kernel

/-! The five printed matrices of Section 3, as rational 3 by 3 tables. -/

def A3 : Fin 3 → Fin 3 → ℚ := ![![1/8, -1/16, 1/32], ![-1/16, 1/32, -1/64], ![1/32, -1/64, 1/128]]
def A5 : Fin 3 → Fin 3 → ℚ :=
  ![![1/64, -1/256, 1/1024], ![-1/256, 1/1024, -1/4096], ![1/1024, -1/4096, 1/16384]]
def A7 : Fin 3 → Fin 3 → ℚ :=
  ![![1/27, -1/162, -1/162], ![-1/162, 2/243, -1/729], ![-1/162, -1/729, 4/2187]]
def A15 : Fin 3 → Fin 3 → ℚ :=
  ![![1/32, 1/256, -7/1024], ![1/256, 1/128, 1/1024], ![-7/1024, 1/1024, 1/512]]
def A31 : Fin 3 → Fin 3 → ℚ :=
  ![![13/2250, 1/3750, -8/28125], ![1/3750, 77/56250, 22/140625],
    ![-8/28125, 22/140625, 499/1406250]]

/-- Printed entry from recipe numerator: entry = numer / (φ² ε^{i+j}). -/
theorem A3_eq : ∀ i j : Fin 3, A3 i j = ((([[2, -2, 2], [-2, 2, -2], [2, -2, 2]] : List (List ℤ)).getD i [] |>.getD j 0 : ℤ) : ℚ) / (2 ^ 2 * 2 ^ ((i:ℕ) + 1 + ((j:ℕ) + 1))) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A3, A5, A7, A15, A31] <;> norm_num
theorem A5_eq : ∀ i j : Fin 3, A5 i j = ((([[4, -4, 4], [-4, 4, -4], [4, -4, 4]] : List (List ℤ)).getD i [] |>.getD j 0 : ℤ) : ℚ) / (4 ^ 2 * 4 ^ ((i:ℕ) + 1 + ((j:ℕ) + 1))) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A3, A5, A7, A15, A31] <;> norm_num
theorem A7_eq : ∀ i j : Fin 3, A7 i j = ((([[12, -6, -18], [-6, 24, -12], [-18, -12, 48]] : List (List ℤ)).getD i [] |>.getD j 0 : ℤ) : ℚ) / (6 ^ 2 * 3 ^ ((i:ℕ) + 1 + ((j:ℕ) + 1))) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A3, A5, A7, A15, A31] <;> norm_num
theorem A15_eq : ∀ i j : Fin 3, A15 i j = ((([[32, 16, -112], [16, 128, 64], [-112, 64, 512]] : List (List ℤ)).getD i [] |>.getD j 0 : ℤ) : ℚ) / (8 ^ 2 * 4 ^ ((i:ℕ) + 1 + ((j:ℕ) + 1))) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A3, A5, A7, A15, A31] <;> norm_num
theorem A31_eq : ∀ i j : Fin 3, A31 i j = ((([[130, 30, -160], [30, 770, 440], [-160, 440, 4990]] : List (List ℤ)).getD i [] |>.getD j 0 : ℤ) : ℚ) / (30 ^ 2 * 5 ^ ((i:ℕ) + 1 + ((j:ℕ) + 1))) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A3, A5, A7, A15, A31] <;> norm_num

def Astar (i j : Fin 3) : ℚ := A3 i j + A5 i j + A7 i j + A15 i j + A31 i j

def qf (M : Fin 3 → Fin 3 → ℚ) (x : Fin 3 → ℚ) : ℚ := ∑ i, ∑ j, x i * M i j * x j

def v : Fin 3 → ℚ := ![-1/16, -1/4, 1]
def w : Fin 3 → ℚ := ![-1/8, 1, 0]

/-- (59): vᵀ A_* v, printed 54590609909 / 2799360000000. -/
theorem vAv_star : qf Astar v = 54590609909 / 2799360000000 := by
  simp [qf, Astar, A3, A5, A7, A15, A31, v, Fin.sum_univ_three]; norm_num

theorem vAv_star_lt : qf Astar v < 1 / 50 := by rw [vAv_star]; norm_num

/-- (66): wᵀ A_* w + 4 vᵀ A_* v, printed 51822763867 / 349920000000. -/
theorem wAw_4vAv_star : qf Astar w + 4 * qf Astar v = 51822763867 / 349920000000 := by
  simp [qf, Astar, A3, A5, A7, A15, A31, v, w, Fin.sum_univ_three]; norm_num

theorem wAw_4vAv_star_lt : qf Astar w + 4 * qf Astar v < 3 / 20 := by
  rw [wAw_4vAv_star]; norm_num

/-- Table 3 rows, the per-modulus quadratic forms. -/
theorem table3 :
    (qf A3 v, qf A5 v, qf A7 v, qf A15 v, qf A31 v) =
      (25/2048, 1/16384, 2101/559872, 25/8192, 154309/360000000) ∧
    (qf A3 w + 4 * qf A3 v, qf A5 w + 4 * qf A5 v, qf A7 w + 4 * qf A7 v,
      qf A15 w + 4 * qf A15 v, qf A31 w + 4 * qf A31 v) =
      (25/256, 5/2048, 1775/69984, 5/256, 139817/45000000) := by
  simp [qf, A3, A5, A7, A15, A31, v, w, Fin.sum_univ_three]; norm_num

/-- The diagonal sums of Section 3. -/
theorem Astar_diag : (0.2146 : ℚ) < Astar 0 0 ∧ (0.0496 : ℚ) < Astar 1 1 ∧ (0.012 : ℚ) < Astar 2 2 := by
  simp [Astar, A3, A5, A7, A15, A31]; norm_num

/-- The tail bounds: T_ii < cited bound minus the diagonal sum. -/
theorem tail_bounds {A11 A22 A33 : ℚ} (h1 : A11 < 0.279) (h2 : A22 < 0.0555) (h3 : A33 < 0.0136) :
    A11 - Astar 0 0 < 0.254 ^ 2 ∧ A22 - Astar 1 1 < 0.077 ^ 2 ∧ A33 - Astar 2 2 < 0.04 ^ 2 := by
  obtain ⟨a, b, c⟩ := Astar_diag
  refine ⟨?_, ?_, ?_⟩ <;> norm_num at * <;> linarith

/-- (59) to (60): vᵀ A v < 13/500 from vᵀ A_* v and the (23) tail. -/
theorem vAv_tail : (1 / 50 : ℚ) + (0.254 / 16 + 0.077 / 4 + 0.04) ^ 2 < 13 / 500 := by norm_num

/-- (66): the GRH quadratic form below 37/200. -/
theorem wAw_tail : (3 / 20 : ℚ) + (0.254 / 8 + 0.077) ^ 2 + 4 * (0.254 / 16 + 0.077 / 4 + 0.04) ^ 2
    < 37 / 200 := by norm_num

/-! ### Section 6, K = 6 unconditional -/

/-- Criterion (58) at a = 1/4, b = 1/16 with C₁ = 6.7814: the left side is below 15/32,
CONDITIONAL ON the cited C₀R₀ < 1.279 and the region bound H < 2/15 of (61). -/
theorem k6_criterion {CR H VA : ℝ} (hCR0 : 0 ≤ CR) (hCR : CR < 1.279) (hH0 : 0 ≤ H)
    (hH : H < 2 / 15) (hVA : VA < 13 / 500) :
    VA + 11 * (1 / 16) ^ 2 * Real.log 2 / 50 + H * ((6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25)
      < 15 / 32 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : (6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25 < 3.26 := by nlinarith
  have hX0 : 0 ≤ (6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25 := by positivity
  have : H * ((6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25) ≤ 2 / 15 * 3.26 := by
    apply mul_le_mul hH.le hX.le hX0 (by norm_num)
  nlinarith

/-- (1 - a - b)² = 121/256 beats the 15/32 of (62). -/
theorem k6_margin : (15 / 32 : ℚ) < (1 - 1/4 - 1/16) ^ 2 ∧ (1 - 1/4 - 1/16 : ℚ) ^ 2 = 121 / 256 := by
  norm_num

/-- The final constant of Theorem 1.1: 4·121/256 - 2(121/256 + 15/32) = 1/128 > 1/1000. -/
theorem k6_final : (4 * (121 / 256) - 2 * (121 / 256 + 15 / 32) : ℚ) = 1 / 128 ∧
    (1 / 1000 : ℚ) < 1 / 128 := by norm_num

/-- I(5/6) > 81/200 > (7/12) log 2, the second inequality, and γ₆ = 81/(200 log 2) > 7/12. -/
theorem gamma6 : 7 / 12 * Real.log 2 < 81 / 200 ∧ 7 / 12 < 81 / (200 * Real.log 2) := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]; nlinarith

/-- 19/12 - γ₆ < 1, the exponent in Lemma 6.1. -/
theorem lemma61_exp : 19 / 12 - 81 / (200 * Real.log 2) < 1 := by linarith [gamma6.2]

/-! ### Section 7, K = 5 on GRH -/

theorem k5_setup :
    (∀ z : ℚ, z ^ 2 - z / 4 - 1 / 16 = (z - 1/8) ^ 2 - 5 / 64) ∧
    ((1:ℚ)/8) ^ 2 + 2 ^ 2 * (1/16) ^ 2 = 1 / 32 ∧
    1 - (1:ℚ)/8 + 2 * (1 - 1/4 - 1/16) = 9 / 4 ∧
    (1 - (1:ℚ)/8) ^ 2 + 2 ^ 2 * (1 - 1/4 - 1/16) ^ 2 = 85 / 32 := by
  refine ⟨fun z => by ring, by norm_num, by norm_num, by norm_num⟩

/-- Criterion (65) at a = 1/4, b = 1/16, c = 1/8, τ = 2: (66) plus D log 2 / 4 and the
H term are below 12/5, CONDITIONAL ON C₀R₀ < 1.279 and H < 41/60 of (67). -/
theorem k5_criterion {CR H WA : ℝ} (hCR0 : 0 ≤ CR) (hCR : CR < 1.279) (hH0 : 0 ≤ H)
    (hH : H < 41 / 60) (hWA : WA < 37 / 200) :
    WA + 1 / 32 * Real.log 2 / 4 + H * ((6.7814 - 2) / 2 * CR + Real.log 2 / 4) < 12 / 5 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : (6.7814 - 2) / 2 * CR + Real.log 2 / 4 < 3.2313 := by nlinarith
  have hX0 : 0 ≤ (6.7814 - 2) / 2 * CR + Real.log 2 / 4 := by positivity
  have : H * ((6.7814 - 2) / 2 * CR + Real.log 2 / 4) ≤ 41 / 60 * 3.2313 := by
    apply mul_le_mul hH.le hX.le hX0 (by norm_num)
  nlinarith

/-- The final constant of Theorem 1.2: (81/16 - 85/32 - 12/5)/2 = 1/320 > 1/1000. -/
theorem k5_final : ((9/4 : ℚ) ^ 2 - 85 / 32 - 12 / 5) / 2 = 1 / 320 ∧ (1/1000 : ℚ) < 1 / 320 := by
  norm_num

/-- I(25/32) > 347/1000 > (1/2) log 2 and γ₅ = 347/(1000 log 2) > 1/2. -/
theorem gamma5 : 1 / 2 * Real.log 2 < 347 / 1000 ∧ 1 / 2 < 347 / (1000 * Real.log 2) := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]; nlinarith


/-! ### The large deviation exponents I(λ) of (49) -/

/-- I(λ) = ((1+λ)/2) log(1+λ) + ((1-λ)/2) log(1-λ), equation (49). -/
noncomputable def Ilam (l : ℝ) : ℝ := (1 + l) / 2 * Real.log (1 + l) + (1 - l) / 2 * Real.log (1 - l)

lemma log_one_sub_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x) ∧
    Real.log (1 - x) ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- **I(5/6) > 81/200**, used in Section 6 with ρ = 81/200; I(5/6) = 0.40631... -/
theorem I56 : (81 / 200 : ℝ) < Ilam (5 / 6) := by
  have e1 : Real.log (1 + 5 / 6) = Real.log 2 + Real.log (1 - 1 / 12) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log (1 - 5 / 6) = -(3 * Real.log 2 + Real.log (1 - 1 / 4)) := by
    have : (1 - 5 / 6 : ℝ) = ((2 ^ 3) * (1 - 1 / 4))⁻¹ := by norm_num
    rw [this, Real.log_inv, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  obtain ⟨a1, -⟩ := log_one_sub_bounds (x := 1 / 12) (by norm_num) (by norm_num) 6
  obtain ⟨-, a2⟩ := log_one_sub_bounds (x := 1 / 4) (by norm_num) (by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at a1 a2
  norm_num at a1 a2
  have hl := Real.log_two_gt_d9
  unfold Ilam; rw [e1, e2]; nlinarith

/-- **I(25/32) > 347/1000**, used in Section 7 with ρ = 347/1000; I(25/32) = 0.34794... -/
theorem I2532 : (347 / 1000 : ℝ) < Ilam (25 / 32) := by
  have e1 : Real.log (1 + 25 / 32) = Real.log 2 + Real.log (1 - 7 / 64) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log (1 - 25 / 32) = -(2 * Real.log 2) + Real.log (1 - 1 / 8) := by
    have : (1 - 25 / 32 : ℝ) = (2 ^ 2)⁻¹ * (1 - 1 / 8) := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_inv, Real.log_pow]; push_cast; ring
  obtain ⟨a1, -⟩ := log_one_sub_bounds (x := 7 / 64) (by norm_num) (by norm_num) 6
  obtain ⟨a2, -⟩ := log_one_sub_bounds (x := 1 / 8) (by norm_num) (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at a1 a2
  norm_num at a1 a2
  have hl := Real.log_two_gt_d9
  unfold Ilam; rw [e1, e2]; nlinarith


/-! ### The regions D_λ of (51) and the maxima (61), (67) -/

noncomputable def rl (l : ℝ) : ℝ := l ^ 2 / 2
noncomputable def betal (l : ℝ) : ℝ := (rl l + Real.sqrt (rl l ^ 2 + 4 * rl l)) / 2

/-- D_λ = {x + iy : x ≤ β_λ, x² + y² ≤ r_λ / (1 + r_λ - x)}, equation (51). -/
def Dl (l : ℝ) : Set ℂ :=
  {z | z.re ≤ betal l ∧ Complex.normSq z ≤ rl l / (1 + rl l - z.re)}

lemma beta56_le : betal (5 / 6) ≤ 79 / 100 := by
  unfold betal rl
  have : Real.sqrt ((((5:ℝ) / 6) ^ 2 / 2) ^ 2 + 4 * (((5:ℝ) / 6) ^ 2 / 2)) ≤ 158/100 - ((5:ℝ)/6)^2/2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

lemma beta2532_le : betal (25 / 32) ≤ 726 / 1000 := by
  unfold betal rl
  have : Real.sqrt ((((25:ℝ) / 32) ^ 2 / 2) ^ 2 + 4 * (((25:ℝ) / 32) ^ 2 / 2)) ≤
      1452/1000 - ((25:ℝ)/32)^2/2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

lemma normSq_Q (z : ℂ) : Complex.normSq (z ^ 2 - z / 4 - 1 / 16) = (Complex.normSq z) ^ 2 -
    Complex.normSq z * z.re / 2 - z.re ^ 2 / 4 + 3 * Complex.normSq z / 16 + z.re / 32 + 1 / 256 := by
  simp [Complex.normSq_apply, pow_two]; ring

lemma normSq_sub8 (z : ℂ) : Complex.normSq (z - 1 / 8) = Complex.normSq z - z.re / 4 + 1 / 64 := by
  simp [Complex.normSq_apply]; ring

lemma mem_Dl_poly {l b : ℝ} {z : ℂ} (hb : betal l ≤ b) (hb1 : b < 1) (hr : 0 ≤ rl l) (hz : z ∈ Dl l) :
    z.re ^ 2 ≤ Complex.normSq z ∧ Complex.normSq z * (1 + rl l - z.re) ≤ rl l ∧ z.re ≤ b := by
  obtain ⟨h1, h2⟩ := hz
  have hpos : 0 < 1 + rl l - z.re := by linarith
  refine ⟨?_, (le_div_iff₀ hpos).1 h2, h1.trans hb⟩
  rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg z.im]

/-- **(61)**: |Q(z)|² < 2/15 on D_{5/6}, Q(z) = z² - z/4 - 1/16; the maximum is 0.13055 at z = β. -/
theorem region61 (z : ℂ) (hz : z ∈ Dl (5 / 6)) : Complex.normSq (z ^ 2 - z / 4 - 1 / 16) < 2 / 15 := by
  obtain ⟨hx2, hD, hx⟩ := mem_Dl_poly beta56_le (by norm_num) (by unfold rl; positivity) hz
  rw [normSq_Q]
  have hr : rl (5 / 6) = 25 / 72 := by unfold rl; norm_num
  rw [hr] at hD
  set x := z.re; set u := Complex.normSq z
  have hp : 0 ≤ (u - x^2) * (25/72 - u * (1 + 25/72 - x)) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hp, sq_nonneg (x - 79/100), sq_nonneg (x+1/2), sq_nonneg u,
    mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hx)]

/-- **(67)**: |z - 1/8|² + 4|Q(z)|² < 41/60 on D_{25/32}; the maximum is 0.68055 at z = β. -/
theorem region67 (z : ℂ) (hz : z ∈ Dl (25 / 32)) :
    Complex.normSq (z - 1 / 8) + 4 * Complex.normSq (z ^ 2 - z / 4 - 1 / 16) < 41 / 60 := by
  obtain ⟨hx2, hD, hx⟩ := mem_Dl_poly beta2532_le (by norm_num) (by unfold rl; positivity) hz
  rw [normSq_Q, normSq_sub8]
  have hr : rl (25 / 32) = 625 / 2048 := by unfold rl; norm_num
  rw [hr] at hD
  set x := z.re; set u := Complex.normSq z
  have hp : 0 ≤ (u - x^2) * (625/2048 - u * (1 + 625/2048 - x)) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hp, sq_nonneg (x - 726/1000), sq_nonneg (x+1/2), sq_nonneg u,
    mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hx)]

/-- Vacuity of the region statements: 0 ∈ D_λ for both λ. -/
theorem zero_mem_Dl : (0 : ℂ) ∈ Dl (5 / 6) ∧ (0 : ℂ) ∈ Dl (25 / 32) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [betal, rl] <;> first | positivity | (apply div_nonneg <;> norm_num)

/-- Vacuity: the hypotheses of `k6_criterion` and `k5_criterion` can hold together. -/
theorem vacuity : ∃ CR H : ℝ, 0 ≤ CR ∧ CR < 1.279 ∧ 0 ≤ H ∧ H < 2 / 15 ∧ H < 41 / 60 :=
  ⟨1.27, 0.13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Linnik.LiLiu
