module

public import LeanLab.Halupczok2012.U1493Theorem5Min
public import LeanLab.PrimePowerWindow.Count

/-!
# P0077 Halupczok 2012: Theorem 5 from Perelli-Pintz 1993, unit U-1496

AI wrote the Lean code, Claude, run 20261022T2003Z-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Source: A. Perelli and J. Pintz, On the exceptional set for Goldbach's problem in short
intervals, J. London Math. Soc. (2) 47 (1993) 41-49, read from page images.

* `PP1993Thm3Printed`: PP1993 Theorem 3, p. 44, exactly as printed. It is the `2k`-TWIN
  PRIMES result, `n - m = 2k`, with `ψ*` and `P*` of p. 44. It is not a Goldbach statement.
* `PP1993Goldbach`: the Goldbach analogue of Theorem 3, with `R*` and `M*` of p. 43. It is not a
  numbered statement of PP1993. The paper establishes it in §§3-5: display (1) and (3), p. 44,
  reduce the mean square `∑_{N<2n≤N+H} |R*(2n) - M*(2n) 𝔖(2n)|²` to (4) and (5), and the
  paper proves (4) "for any `N^{7/12+ε} ≤ Y ≤ N`", §4 p. 45, and (5) "for any `Y ≥ Y₀(A,ε)` and
  `H ≥ Y^{1/3+ε}`", §5 p. 46, with `H = Y^{1/3+ε}` chosen on p. 44. Theorem 3 itself is
  derived on p. 44 by the sentence "the analogues of (4) and (5) ... imply the following
  theorem"; `PP1993Goldbach` is what (4) and (5) themselves give by the same sentence.
* `theorem5_of_PP : PP1993Goldbach → Theorem5`. CONDITIONAL ON `PP1993Goldbach` only.
  Elementary: the window condition `p₂ ∈ (X₂, X₂ + Y]` is the DIFFERENCE of two PP1993 sums,
  `R*(2k, 2X₁, 2X₁ - X₂) - R*(2k, 2X₁, 2X₁ - X₂ - Y)`, up to the `p₂` within `2R` of the two
  window ends, prime powers, and `M*` versus `Y`, all `≪ Y^{19/20}` per `k`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset
open scoped ArithmeticFunction.vonMangoldt Classical

/-! ## Part 1. PP1993 as printed -/

/-- The summation condition of `R*(2n, N, Y)` and `M*(2n, N, Y)`, PP1993 p. 43, for `m = 2n`,
`h` the first prime and `k = m - h`: `N - Y < h ≤ N`, `k ≤ Y`. -/
def ppCond (m : ℕ) (N Y : ℝ) (h : ℕ) : Prop :=
  N - Y < (h : ℝ) ∧ (h : ℝ) ≤ N ∧ ((m - h : ℕ) : ℝ) ≤ Y

/-- PP1993 p. 43: `R*(2n, N, Y) = ∑_{h+k=2n, N-Y<h≤N, k≤Y} Λ(h) Λ(k)`, `h, k ≥ 1`, `m = 2n`. -/
noncomputable def ppR (m : ℕ) (N Y : ℝ) : ℝ :=
  ∑ h ∈ (Ioo 0 m).filter (ppCond m N Y), Λ h * Λ (m - h)

/-- PP1993 p. 43: `M*(2n, N, Y) = ∑_{h+k=2n, N-Y<h≤N, k≤Y} 1`. -/
noncomputable def ppM (m : ℕ) (N Y : ℝ) : ℝ :=
  (((Ioo 0 m).filter (ppCond m N Y)).card : ℝ)

/-- PP1993 p. 44: `ψ*(2k, N, Y) = ∑_{n-m=2k, N<n≤N+Y, m≤Y} Λ(n) Λ(m)`, `m ≥ 1`, `d = 2k`. -/
noncomputable def ppPsi (d : ℕ) (N Y : ℝ) : ℝ :=
  ∑ j ∈ (Icc 1 ⌊Y⌋₊).filter (fun j => N < ((j + d : ℕ) : ℝ) ∧ ((j + d : ℕ) : ℝ) ≤ N + Y),
    Λ (j + d) * Λ j

/-- PP1993 p. 44: `P*(2k, N, Y) = ∑_{n-m=2k, N<n≤N+Y, m≤Y} 1`. -/
noncomputable def ppP (d : ℕ) (N Y : ℝ) : ℝ :=
  (((Icc 1 ⌊Y⌋₊).filter
    (fun j => N < ((j + d : ℕ) : ℝ) ∧ ((j + d : ℕ) : ℝ) ≤ N + Y)).card : ℝ)

/-- **PP1993 Theorem 3, p. 44, as printed.** Let `ε, A > 0`, `N^{7/12+ε} ≤ Y ≤ N` and
`H = Y^{1/3+ε}`. Then `∑_{N<2k≤N+H} |ψ*(2k) - 𝔖(2k) P*(2k)|² ≪_{ε,A} H Y² L^{-A}`, `L = log N`,
`N > N₀(A, ε)`, p. 43. `𝔖` is the lab's `S`, p. 41. The `2k`-twin primes problem. -/
def PP1993Thm3Printed : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ, N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        (ppPsi (2 * k) N Y - S (2 * k) * ppP (2 * k) N Y) ^ 2 ≤
      C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A)

/-- **The Goldbach analogue of PP1993 Theorem 3**, from (1), (3), (4), (5) of PP1993 §§3-5:
for `ε, A > 0`, `N^{7/12+ε} ≤ Y ≤ N`, `H = Y^{1/3+ε}`,
`∑_{N<2n≤N+H} |R*(2n) - M*(2n) 𝔖(2n)|² ≪_{ε,A} H Y² L^{-A}`, `L = log N`. Not a numbered
statement of PP1993; see the module doc. -/
def PP1993Goldbach : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ, N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        (ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y) ^ 2 ≤
      C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A)

/-! ### Vacuity -/

/-- The hypotheses of both PP1993 Props hold at `Y = N` for every `N ≥ 1` and `ε ≤ 5/12`. -/
theorem pp_hyp_instance (N ε : ℝ) (hN : 1 ≤ N) (hε : ε ≤ 5 / 12) :
    N ^ (7 / 12 + ε) ≤ N ∧ N ≤ N := by
  refine ⟨?_, le_rfl⟩
  calc N ^ (7 / 12 + ε) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = N := Real.rpow_one N

/-- `M*(10, 5, 5) = 1`: the only pair is `5 + 5`, so `R*` and `M*` are not degenerate. -/
theorem ppM_instance : ppM 10 5 5 = 1 := by
  have : (Ioo 0 10).filter (ppCond 10 5 5) = {5} := by
    ext h
    simp only [mem_filter, mem_Ioo, mem_singleton, ppCond]
    constructor
    · rintro ⟨⟨h0, h10⟩, a, b, c⟩
      have b' : h ≤ 5 := by exact_mod_cast b
      have c' : 10 - h ≤ 5 := by exact_mod_cast c
      omega
    · rintro rfl; norm_num
  rw [ppM, this, card_singleton, Nat.cast_one]

/-! ## Part 2. The three sums over `h ∈ (0, m)` -/

theorem ppR_eq (m : ℕ) (N Y : ℝ) :
    ppR m N Y = ∑ h ∈ Ioo 0 m, (if ppCond m N Y h then (1 : ℝ) else 0) * (Λ h * Λ (m - h)) := by
  rw [ppR, sum_filter]
  refine sum_congr rfl fun h _ => ?_
  split_ifs <;> simp

theorem ppM_eq (m : ℕ) (N Y : ℝ) :
    ppM m N Y = ∑ h ∈ Ioo 0 m, (if ppCond m N Y h then (1 : ℝ) else 0) := by
  rw [ppM, card_filter]; push_cast; rfl

/-- `binSum` as a sum over `h ∈ (0, m)` with the von Mangoldt weights. -/
theorem binSum_eq (X2 Y : ℝ) (m : ℕ) :
    binSum X2 Y m = ∑ h ∈ Ioo 0 m,
      (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime) then (1 : ℝ) else 0) *
        (Λ h * Λ (m - h)) := by
  unfold binSum binSumAP
  rw [sum_filter]
  have hsub : Ioo 0 m ⊆ range (m + 1) := by
    intro h hh; rw [mem_Ioo] at hh; rw [mem_range]; omega
  rw [← sum_subset hsub ?_]
  · refine sum_congr rfl fun h hh => ?_
    by_cases c : (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime)
    · rw [if_pos c, one_mul, if_pos ⟨c.2.1, c.2.2, c.1.1, c.1.2, by simp [Int.modEq_one]⟩,
        ArithmeticFunction.vonMangoldt_apply_prime c.2.1,
        ArithmeticFunction.vonMangoldt_apply_prime c.2.2]
    · rw [if_neg c, zero_mul, if_neg]
      rintro ⟨a, b, d, e, -⟩
      exact c ⟨⟨d, e⟩, a, b⟩
  · intro h hh hn
    rw [if_neg]
    rintro ⟨a, b, -⟩
    apply hn
    rw [mem_Ioo]
    refine ⟨a.pos, ?_⟩
    have := b.pos
    omega

/-! ## Part 3. Indicator identities -/

/-- For `m = N + s`, `0 < s`, `X₂ + Y + s ≤ N`: the two PP1993 conditions differ exactly on
`X₂ + s ≤ h < X₂ + Y + s`. -/
theorem ind_diff {m h : ℕ} {N s X2 Y : ℝ} (hm : (m : ℝ) = N + s) (hhm : h < m) (hs : 0 < s)
    (hY : 0 ≤ Y) (hN : X2 + Y + s ≤ N) :
    (if ppCond m N (N - X2) h then (1 : ℝ) else 0) - (if ppCond m N (N - X2 - Y) h then 1 else 0)
      = if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then 1 else 0 := by
  have hmh : ((m - h : ℕ) : ℝ) = N + s - h := by rw [Nat.cast_sub hhm.le, hm]
  have e1 : ppCond m N (N - X2) h ↔ (X2 + s ≤ (h : ℝ) ∧ (h : ℝ) ≤ N) := by
    unfold ppCond; rw [hmh]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by linarith, b⟩
    · rintro ⟨a, b⟩; exact ⟨by linarith, b, by linarith⟩
  have e2 : ppCond m N (N - X2 - Y) h ↔ (X2 + Y + s ≤ (h : ℝ) ∧ (h : ℝ) ≤ N) := by
    unfold ppCond; rw [hmh]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by linarith, b⟩
    · rintro ⟨a, b⟩; exact ⟨by linarith, b, by linarith⟩
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  by_cases A : X2 + s ≤ (h : ℝ)
  · by_cases B : (h : ℝ) < X2 + Y + s
    · rw [if_pos ⟨A, by linarith⟩, if_neg (fun c => by linarith [c.1]), if_pos ⟨A, B⟩]; norm_num
    · rw [if_neg (fun c : _ ∧ _ => B c.2)]
      push_neg at B
      by_cases C : (h : ℝ) ≤ N
      · rw [if_pos ⟨A, C⟩, if_pos ⟨B, C⟩]; norm_num
      · rw [if_neg (fun c => C c.2), if_neg (fun c => C c.2)]; norm_num
  · rw [if_neg (fun c => A c.1), if_neg (fun c => by linarith [c.1]), if_neg (fun c => A c.1)]
    norm_num

/-- The pointwise error of the window difference against the prime window. -/
theorem coef_bound {h X2 Y s : ℝ} (P : Prop) [Decidable P] (hs : 0 < s) (hsY : s ≤ Y) :
    |(if X2 + s ≤ h ∧ h < X2 + Y + s then (1 : ℝ) else 0) -
        (if (X2 < h ∧ h ≤ X2 + Y) ∧ P then 1 else 0)| ≤
      (if X2 < h ∧ h < X2 + s then (1 : ℝ) else 0) +
        (if X2 + Y < h ∧ h < X2 + Y + s then 1 else 0) +
        (if (X2 < h ∧ h ≤ X2 + Y) ∧ ¬ P then 1 else 0) := by
  have n5 : (h < X2 + s) ↔ ¬ (X2 + s ≤ h) := not_le.symm
  have n6 : (X2 + Y < h) ↔ ¬ (h ≤ X2 + Y) := not_le.symm
  simp only [n5, n6]
  by_cases hp : P <;> by_cases a1 : X2 < h <;> by_cases a2 : h ≤ X2 + Y <;>
    by_cases a3 : X2 + s ≤ h <;> by_cases a4 : h < X2 + Y + s <;>
    simp only [hp, a1, a2, a3, a4, and_true, true_and, and_false, false_and, not_true,
      not_false_eq_true, if_true, if_false] <;> norm_num <;> linarith

/-! ## Part 4. Elementary bounds -/

theorem lam_le_log {n m : ℕ} (hn : n ≤ m) : Λ n ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [ArithmeticFunction.map_zero]; exact Real.log_natCast_nonneg m
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn))

theorem f_bound {m h : ℕ} (hh : h ≤ m) :
    0 ≤ Λ h * Λ (m - h) ∧ Λ h * Λ (m - h) ≤ Real.log m ^ 2 := by
  have a := lam_le_log hh
  have b := lam_le_log (Nat.sub_le m h)
  have a0 : 0 ≤ Λ h := ArithmeticFunction.vonMangoldt_nonneg
  have b0 : 0 ≤ Λ (m - h) := ArithmeticFunction.vonMangoldt_nonneg
  refine ⟨mul_nonneg a0 b0, ?_⟩
  rw [sq]; exact mul_le_mul a b b0 (a0.trans a)

/-- Pairs with `h` in an open window of length `y`: at most `(y + 1) log² m`. -/
theorem window_sum_le (m : ℕ) {x y : ℝ} (hy : 0 ≤ y) :
    ∑ h ∈ Ioo 0 m, (if x < (h : ℝ) ∧ (h : ℝ) < x + y then (1 : ℝ) else 0) * (Λ h * Λ (m - h)) ≤
      Real.log m ^ 2 * (y + 1) := by
  have hcard : ((((Ioo 0 m).filter (fun h : ℕ => x < (h : ℝ) ∧ (h : ℝ) < x + y)).card : ℕ) : ℝ)
      ≤ y / ((1 : ℕ) : ℝ) + 1 :=
    card_cong_le one_pos hy (fun h hh => by rw [mem_filter] at hh; exact ⟨hh.2.1, hh.2.2.le⟩)
      (fun _ _ _ _ => by simp [Int.modEq_one])
  calc _ ≤ ∑ h ∈ Ioo 0 m,
        (if x < (h : ℝ) ∧ (h : ℝ) < x + y then (1 : ℝ) else 0) * Real.log m ^ 2 := by
        refine sum_le_sum fun h hh => ?_
        have := f_bound (m := m) (h := h) (by rw [mem_Ioo] at hh; omega)
        split_ifs <;> simp [this.2]
    _ = Real.log m ^ 2 *
          ((((Ioo 0 m).filter (fun h : ℕ => x < (h : ℝ) ∧ (h : ℝ) < x + y)).card : ℕ) : ℝ) := by
        rw [← sum_mul, mul_comm, sum_boole]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa using hcard

/-- The von Mangoldt mass of the non-primes in `(0, m]`. -/
noncomputable def ppMass (m : ℕ) : ℝ := ∑ n ∈ (Ioc 0 m).filter (fun n => ¬ n.Prime), Λ n

theorem ppMass_nonneg (m : ℕ) : 0 ≤ ppMass m :=
  sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Pairs where `h` or `m - h` is not prime: at most `2 log m` times the prime power mass. -/
theorem nonprime_sum_le (m : ℕ) (T : ℕ → Prop) [DecidablePred T] :
    ∑ h ∈ Ioo 0 m, (if T h ∧ ¬ (h.Prime ∧ (m - h).Prime) then (1 : ℝ) else 0) *
        (Λ h * Λ (m - h)) ≤ 2 * Real.log m * ppMass m := by
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hpt : ∀ h ∈ Ioo 0 m,
      (if T h ∧ ¬ (h.Prime ∧ (m - h).Prime) then (1 : ℝ) else 0) * (Λ h * Λ (m - h)) ≤
        Real.log m * ((if ¬ h.Prime then Λ h else 0) +
          (if ¬ (m - h).Prime then Λ (m - h) else 0)) := by
    intro h hh
    rw [mem_Ioo] at hh
    have a := lam_le_log (n := h) (m := m) hh.2.le
    have b := lam_le_log (n := m - h) (m := m) (Nat.sub_le m h)
    have a0 : 0 ≤ Λ h := ArithmeticFunction.vonMangoldt_nonneg
    have b0 : 0 ≤ Λ (m - h) := ArithmeticFunction.vonMangoldt_nonneg
    have i1 : 0 ≤ (if ¬ h.Prime then Λ h else 0) := by split_ifs <;> simp [a0]
    have i2 : 0 ≤ (if ¬ (m - h).Prime then Λ (m - h) else 0) := by split_ifs <;> simp [b0]
    by_cases c : T h ∧ ¬ (h.Prime ∧ (m - h).Prime)
    · rw [if_pos c, one_mul]
      by_cases ph : h.Prime
      · have pm : ¬ (m - h).Prime := fun q => c.2 ⟨ph, q⟩
        rw [if_neg (not_not.mpr ph), if_pos pm, zero_add]
        exact mul_le_mul_of_nonneg_right a b0
      · rw [if_pos ph]
        calc Λ h * Λ (m - h) ≤ Λ h * Real.log m := mul_le_mul_of_nonneg_left b a0
          _ = Real.log m * Λ h := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hlog
    · rw [if_neg c, zero_mul]; positivity
  have hA : ∑ h ∈ Ioo 0 m, (if ¬ h.Prime then Λ h else 0) ≤ ppMass m := by
    rw [ppMass, sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro h hh; rw [mem_Ioo] at hh; rw [mem_Ioc]; omega
    · intro n _ _; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  have hB : ∑ h ∈ Ioo 0 m, (if ¬ (m - h).Prime then Λ (m - h) else 0) =
      ∑ h ∈ Ioo 0 m, (if ¬ h.Prime then Λ h else 0) := by
    apply sum_nbij' (fun h => m - h) (fun h => m - h)
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh ⊢; omega
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh ⊢; omega
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh; omega
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh; omega
    · intro h _; rfl
  calc _ ≤ ∑ h ∈ Ioo 0 m, Real.log m * ((if ¬ h.Prime then Λ h else 0) +
          (if ¬ (m - h).Prime then Λ (m - h) else 0)) := sum_le_sum hpt
    _ = Real.log m * (∑ h ∈ Ioo 0 m, (if ¬ h.Prime then Λ h else 0) +
          ∑ h ∈ Ioo 0 m, (if ¬ (m - h).Prime then Λ (m - h) else 0)) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ Real.log m * (ppMass m + ppMass m) := by
        rw [hB]; exact mul_le_mul_of_nonneg_left (by linarith) hlog
    _ = 2 * Real.log m * ppMass m := by ring

theorem natLog_le (m : ℕ) (hm : 1 ≤ m) : ((Nat.log 2 m : ℕ) : ℝ) ≤ 2 * Real.log m := by
  have h1 : 2 ^ (Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 m : ℕ) : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have h3 := Real.log_two_gt_d9
  have h4 : 0 ≤ ((Nat.log 2 m : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The prime power mass: `ppMass m ≤ 4 log² m · m^{1/2}`. -/
theorem ppMass_le {m : ℕ} (hm : 1 ≤ m) :
    ppMass m ≤ 4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by
  have h1 := LeanLab.PrimePowerWindow.sum_nonprime_le 0 m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hm' (by norm_num)
  have hterm : ∀ k ∈ Icc 2 (Nat.log 2 m), (Real.log m / k) *
      ((((Iic m).filter (fun j => 0 < j ^ k ∧ j ^ k ≤ m)).card : ℕ) : ℝ) ≤
        Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ)) := by
    intro k hk
    rw [mem_Icc] at hk
    have hk1 : 1 ≤ k := by omega
    have hc := LeanLab.PrimePowerWindow.count_le (a := 0) (b := (m : ℝ)) le_rfl
      (Nat.cast_nonneg m) hk1
    rw [Nat.floor_natCast, Nat.floor_zero] at hc
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hz : (0 : ℝ) ^ (1 / (k : ℝ)) = 0 := Real.zero_rpow (by positivity)
    rw [hz, sub_zero] at hc
    have hr : (m : ℝ) ^ (1 / (k : ℝ)) ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm'
        (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk.1))
    have hdiv : Real.log m / k ≤ Real.log m := div_le_self hlog (by exact_mod_cast hk1)
    have hdiv0 : 0 ≤ Real.log m / k := div_nonneg hlog hkpos.le
    calc _ ≤ Real.log m * ((m : ℝ) ^ (1 / 2 : ℝ) + 1) :=
          mul_le_mul hdiv (by linarith) (Nat.cast_nonneg _) hlog
      _ ≤ _ := by nlinarith
  have hcardI : ((Icc 2 (Nat.log 2 m)).card : ℝ) ≤ 2 * Real.log m := by
    rw [Nat.card_Icc]
    refine le_trans ?_ (natLog_le m hm)
    exact_mod_cast (by omega : Nat.log 2 m + 1 - 2 ≤ Nat.log 2 m)
  calc ppMass m ≤ _ := h1
    _ ≤ ∑ k ∈ Icc 2 (Nat.log 2 m), Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ)) := sum_le_sum hterm
    _ = ((Icc 2 (Nat.log 2 m)).card : ℝ) * (Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.log m) * (Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardI (by positivity)
    _ = 4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by ring

/-- Integers in `[a, b)`, `b = a + Y`, inside `(0, m)`: their number is within `1` of `Y`. -/
theorem card_window {m : ℕ} {a b Y : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) (hb : b = a + Y)
    (ham : b < m) :
    |∑ h ∈ Ioo 0 m, (if a ≤ (h : ℝ) ∧ (h : ℝ) < b then (1 : ℝ) else 0) - Y| ≤ 1 := by
  subst hb
  have hset : (Ioo 0 m).filter (fun h : ℕ => a ≤ (h : ℝ) ∧ (h : ℝ) < a + Y) =
      Ico ⌈a⌉₊ ⌈a + Y⌉₊ := by
    ext h
    simp only [mem_filter, mem_Ioo, mem_Ico, Nat.ceil_le, Nat.lt_ceil]
    constructor
    · rintro ⟨-, b, c⟩; exact ⟨b, c⟩
    · rintro ⟨b, c⟩
      refine ⟨⟨?_, ?_⟩, b, c⟩
      · exact_mod_cast (show (0 : ℝ) < h by linarith)
      · exact_mod_cast (show (h : ℝ) < m by linarith)
  rw [sum_boole, hset, Nat.card_Ico, Nat.cast_sub (Nat.ceil_mono (by linarith))]
  have h1 := Nat.le_ceil (a + Y)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ a + Y by linarith)
  have h3 := Nat.le_ceil a
  have h4 := Nat.ceil_lt_add_one ha.le
  rw [abs_le]; constructor <;> linarith

/-! ### The singular series is at most `2^17 r^{1/4}` -/

theorem f2_mem {p : ℕ} (hp : p.Prime) : 0 ≤ f2 p ∧ f2 p ≤ 1 := by
  unfold f2
  split_ifs with h2
  · norm_num
  · have h3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      exact_mod_cast (show 3 ≤ p by omega)
    have hq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hq0 : 0 < ((p : ℝ) - 1) ^ 2 := by linarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    constructor <;> linarith

theorem twinC_mem : 0 ≤ twinC ∧ twinC ≤ 1 := by
  constructor
  · exact ge_of_tendsto' twinC_tendsto fun w =>
      prod_nonneg fun p hp => (f2_mem (prime_of_mem_PrN hp)).1
  · exact le_of_tendsto' twinC_tendsto fun w =>
      prod_le_one₀ (fun p hp => (f2_mem (prime_of_mem_PrN hp)).1)
        (fun p hp => (f2_mem (prime_of_mem_PrN hp)).2)

theorem sixteen_rpow : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem factor_le {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) ∧
      ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ (if p < 16 then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 4 : ℝ) := by
  have h3 : (3 : ℝ) ≤ p := by
    have := hp.two_le
    exact_mod_cast (show 3 ≤ p by omega)
  have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hle2 : ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
  split_ifs with h16
  · nlinarith
  · push_neg at h16
    have : (16 : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast h16) (by norm_num)
    rw [sixteen_rpow] at this
    linarith

theorem S_abs_le {r : ℕ} (hr : 1 ≤ r) : |S r| ≤ 2 ^ 17 * (r : ℝ) ^ (1 / 4 : ℝ) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) := by positivity
  set F := r.primeFactors.filter (· ≠ 2) with hF
  have hFp : ∀ p ∈ F, p.Prime ∧ p ≠ 2 := by
    intro p hp; rw [hF, mem_filter, Nat.mem_primeFactors] at hp; exact ⟨hp.1.1, hp.2⟩
  have hprod0 : 0 ≤ ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2)) :=
    prod_nonneg fun p hp => (factor_le (hFp p hp).1 (hFp p hp).2).1
  have hc : ∏ p ∈ F, (if p < 16 then (2 : ℝ) else 1) ≤ 2 ^ 16 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    apply pow_le_pow_right₀ (by norm_num)
    calc (F.filter (· < 16)).card ≤ (range 16).card := by
          apply card_le_card; intro p hp; rw [mem_filter] at hp; rw [mem_range]; exact hp.2
      _ = 16 := card_range 16
  have hP : ((∏ p ∈ F, p : ℕ) : ℝ) ≤ r := by
    have h1 : ∏ p ∈ F, p ≤ ∏ p ∈ r.primeFactors, p :=
      prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
        (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    have h2 : ∏ p ∈ r.primeFactors, p ≤ r := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd r)
    exact_mod_cast h1.trans h2
  have hprod : ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ 2 ^ 16 * (r : ℝ) ^ (1 / 4 : ℝ) := by
    calc ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ ∏ p ∈ F, ((if p < 16 then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 4 : ℝ)) :=
          prod_le_prod₀ (fun p hp => (factor_le (hFp p hp).1 (hFp p hp).2).1)
            (fun p hp => (factor_le (hFp p hp).1 (hFp p hp).2).2)
      _ = (∏ p ∈ F, (if p < 16 then (2 : ℝ) else 1)) * (∏ p ∈ F, (p : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
      _ ≤ 2 ^ 16 * (r : ℝ) ^ (1 / 4 : ℝ) := by
          apply mul_le_mul hc _ (by positivity) (by norm_num)
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          have hP' := hP
          push_cast at hP'
          exact hP'
  obtain ⟨t0, t1⟩ := twinC_mem
  unfold S
  rw [← hF]
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    calc 2 * twinC * ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ 2 * 1 * (2 ^ 16 * (r : ℝ) ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul (by linarith) hprod hprod0 (by norm_num)
      _ = 2 ^ 17 * (r : ℝ) ^ (1 / 4 : ℝ) := by ring
  · rw [abs_zero]; positivity

/-! ## Part 5. The pointwise decomposition -/

theorem mem_kRange' {X R : ℝ} {k : ℕ} (hk : k ∈ kRange X R) : X < k ∧ (k : ℝ) ≤ X + R := by
  unfold kRange at hk; rw [mem_filter] at hk; exact hk.2

theorem kRange_mono {X R R' : ℝ} (h : R ≤ R') : kRange X R ⊆ kRange X R' := by
  intro k hk
  unfold kRange at hk ⊢
  rw [mem_filter] at hk ⊢
  obtain ⟨h1, h2, h3⟩ := hk
  refine ⟨?_, h2, by linarith⟩
  rw [mem_Icc] at h1 ⊢
  exact ⟨h1.1, h1.2.trans (Nat.ceil_mono (by linarith))⟩

theorem card_kRange_le {X R : ℝ} (hR : 0 ≤ R) : ((kRange X R).card : ℝ) ≤ R + 1 := by
  have := card_cong_le (S := kRange X R) (l := 1) one_pos hR (fun k hk => mem_kRange' hk)
    (fun _ _ _ _ => by simp [Int.modEq_one])
  simpa using this

/-- **Pointwise.** For `m = 2k`, `X₁ < k ≤ X₁ + R`, `2R ≤ Y`, `2R ≤ 2X₁ - X₂ - Y`: the
Halupczok error at `2k` minus the difference of the two PP1993 errors at
`N = 2X₁`, `Y' = 2X₁ - X₂` and `Y' = 2X₁ - X₂ - Y` is at most
`2(2R+1) log² m + 8 log³ m · m^{1/2} + 2^17 m^{1/4}`. -/
theorem pointwise {X1 X2 Y R : ℝ} {k : ℕ} (hk : k ∈ kRange X1 R) (hY : 0 < Y) (hX2 : 0 ≤ X2)
    (h2R : 2 * R ≤ Y) (hV : 2 * R ≤ 2 * X1 - X2 - Y) :
    |(binSum X2 Y (2 * k) - S (2 * k) * Y) -
        ((ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2)) -
          (ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
            S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y)))| ≤
      2 * (2 * R + 1) * Real.log ((2 * k : ℕ) : ℝ) ^ 2 +
        8 * Real.log ((2 * k : ℕ) : ℝ) ^ 3 * ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) +
        2 ^ 17 * ((2 * k : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨hk1, hk2⟩ := mem_kRange' hk
  set m := 2 * k with hmdef
  set N := 2 * X1 with hN
  set s := (m : ℝ) - N with hs
  have hmR : (m : ℝ) = N + s := by rw [hs]; ring
  have hmk : (m : ℝ) = 2 * k := by rw [hmdef]; push_cast; ring
  have hs0 : 0 < s := by rw [hs, hmk, hN]; linarith
  have hs2 : s ≤ 2 * R := by rw [hs, hmk, hN]; linarith
  have hsY : s ≤ Y := by linarith
  have hNs : X2 + Y + s ≤ N := by rw [hN]; linarith
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := by linarith
    have : 0 < m := by exact_mod_cast this
    omega
  set f : ℕ → ℝ := fun h => Λ h * Λ (m - h) with hf
  -- the window identity
  have hdiffR : ppR m N (N - X2) - ppR m N (N - X2 - Y) - binSum X2 Y m =
      ∑ h ∈ Ioo 0 m, ((if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then (1 : ℝ) else 0) -
        (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime) then 1 else 0)) *
          f h := by
    rw [ppR_eq, ppR_eq, binSum_eq, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun h hh => ?_
    rw [mem_Ioo] at hh
    rw [← ind_diff hmR hh.2 hs0 hY.le hNs]
    simp only [hf]; ring
  have hdiffM : ppM m N (N - X2) - ppM m N (N - X2 - Y) =
      ∑ h ∈ Ioo 0 m, (if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then (1 : ℝ) else 0) := by
    rw [ppM_eq, ppM_eq, ← sum_sub_distrib]
    refine sum_congr rfl fun h hh => ?_
    rw [mem_Ioo] at hh
    exact ind_diff hmR hh.2 hs0 hY.le hNs
  -- bound of the window identity
  have hlog0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hR1 : |ppR m N (N - X2) - ppR m N (N - X2 - Y) - binSum X2 Y m| ≤
      2 * (2 * R + 1) * Real.log m ^ 2 + 8 * Real.log m ^ 3 * (m : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hdiffR]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ h ∈ Ioo 0 m,
        |((if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then (1 : ℝ) else 0) -
          (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime) then 1 else 0)) *
            f h| ≤
        (if X2 < (h : ℝ) ∧ (h : ℝ) < X2 + s then (1 : ℝ) else 0) * f h +
          (if X2 + Y < (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then 1 else 0) * f h +
          (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ ¬ (h.Prime ∧ (m - h).Prime) then 1 else 0) *
            f h := by
      intro h hh
      rw [mem_Ioo] at hh
      have hf0 : 0 ≤ f h := (f_bound (m := m) (h := h) hh.2.le).1
      rw [abs_mul, abs_of_nonneg hf0, ← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right (coef_bound _ hs0 hsY) hf0
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, sum_add_distrib]
    have e1 := window_sum_le m (x := X2) hs0.le
    have e2 := window_sum_le m (x := X2 + Y) hs0.le
    have e3 := nonprime_sum_le m (fun h => X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y)
    have e4 := ppMass_le hm1
    simp only [hf] at e1 e2 e3 ⊢
    have : 2 * Real.log m * ppMass m ≤
        2 * Real.log m * (4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left e4 (by positivity)
    have hl2 : 0 ≤ Real.log m ^ 2 := sq_nonneg _
    have hs1 : Real.log m ^ 2 * (s + 1) ≤ Real.log m ^ 2 * (2 * R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hl2
    have e5 : 2 * Real.log m * (4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ)) =
        8 * Real.log m ^ 3 * (m : ℝ) ^ (1 / 2 : ℝ) := by ring
    linarith
  have hM1 : |ppM m N (N - X2) - ppM m N (N - X2 - Y) - Y| ≤ 1 := by
    rw [hdiffM]
    apply card_window (a := X2 + s) (by linarith) hY.le (by ring)
    rw [hmR]; linarith
  have hS := S_abs_le hm1
  have key : (binSum X2 Y m - S m * Y) -
      ((ppR m N (N - X2) - S m * ppM m N (N - X2)) -
        (ppR m N (N - X2 - Y) - S m * ppM m N (N - X2 - Y))) =
      -(ppR m N (N - X2) - ppR m N (N - X2 - Y) - binSum X2 Y m) +
        S m * (ppM m N (N - X2) - ppM m N (N - X2 - Y) - Y) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul]
  have hSM : |S m| * |ppM m N (N - X2) - ppM m N (N - X2 - Y) - Y| ≤
      2 ^ 17 * (m : ℝ) ^ (1 / 4 : ℝ) := by
    calc _ ≤ |S m| * 1 := mul_le_mul_of_nonneg_left hM1 (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hS
  linarith

/-! ## Part 6. The core sum over one window -/

/-- The error bound `Emax` at the top `M = 2X₁ + 2R` of the window. -/
noncomputable def Emax (R M : ℝ) : ℝ :=
  2 * (2 * R + 1) * Real.log M ^ 2 + 8 * Real.log M ^ 3 * M ^ (1 / 2 : ℝ) +
    2 ^ 17 * M ^ (1 / 4 : ℝ)

theorem sq_three (a b c : ℝ) : (a - b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b + c)]

/-- **Core.** One window `X₁ < k ≤ X₁ + R` with `2R ≤ Y`, `2R ≤ 2X₁ - X₂ - Y` and `R` at most half
of both PP1993 window lengths `(2X₁ - X₂)^a` and `(2X₁ - X₂ - Y)^a`: the Halupczok mean square is
at most three times the two PP1993 mean squares plus `3 (R + 1) Emax²`. -/
theorem core_sum {X1 X2 Y R a Bhi Blo : ℝ}
    (hhi : ∑ k ∈ kRange X1 ((2 * X1 - X2) ^ a / 2),
      (ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2)) ^ 2
        ≤ Bhi)
    (hlo : ∑ k ∈ kRange X1 ((2 * X1 - X2 - Y) ^ a / 2),
      (ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
        S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y)) ^ 2 ≤ Blo)
    (hY : 0 < Y) (hX2 : 0 ≤ X2) (hR : 0 ≤ R) (h2R : 2 * R ≤ Y) (hV : 2 * R ≤ 2 * X1 - X2 - Y)
    (hRhi : R ≤ (2 * X1 - X2) ^ a / 2) (hRlo : R ≤ (2 * X1 - X2 - Y) ^ a / 2) :
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      3 * Bhi + 3 * Blo + 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 := by
  set M := 2 * X1 + 2 * R with hM
  set Dhi : ℕ → ℝ := fun k =>
    ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2) with hDhi
  set Dlo : ℕ → ℝ := fun k => ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
    S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y) with hDlo
  have hE0 : ∀ k ∈ kRange X1 R, |(binSum X2 Y (2 * k) - S (2 * k) * Y) - (Dhi k - Dlo k)| ≤
      Emax R M := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_kRange' hk
    have hp := pointwise hk hY hX2 h2R hV
    have hk0 : (0 : ℝ) < k := by linarith
    have hk1' : 1 ≤ k := by
      have : 0 < k := by exact_mod_cast hk0
      omega
    have hm1 : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1'
      push_cast; linarith
    have hmM : ((2 * k : ℕ) : ℝ) ≤ M := by push_cast; rw [hM]; linarith
    have hl : Real.log ((2 * k : ℕ) : ℝ) ≤ Real.log M := Real.log_le_log (by linarith) hmM
    have hl0 : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) := Real.log_nonneg hm1
    have h12 : ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hmM (by norm_num)
    have h14 : ((2 * k : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ M ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hmM (by norm_num)
    have hsq0 : 0 ≤ ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hl2 : Real.log ((2 * k : ℕ) : ℝ) ^ 2 ≤ Real.log M ^ 2 := pow_le_pow_left₀ hl0 hl 2
    have hl3 : Real.log ((2 * k : ℕ) : ℝ) ^ 3 ≤ Real.log M ^ 3 := pow_le_pow_left₀ hl0 hl 3
    have t1 : 2 * (2 * R + 1) * Real.log ((2 * k : ℕ) : ℝ) ^ 2 ≤
        2 * (2 * R + 1) * Real.log M ^ 2 := mul_le_mul_of_nonneg_left hl2 (by linarith)
    have t2 : Real.log ((2 * k : ℕ) : ℝ) ^ 3 * ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤
        Real.log M ^ 3 * M ^ (1 / 2 : ℝ) :=
      mul_le_mul hl3 h12 hsq0 (by have := Real.log_nonneg (show (1 : ℝ) ≤ M by linarith); positivity)
    unfold Emax
    simp only [hDhi, hDlo]
    linarith
  have hpt : ∀ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      3 * Dhi k ^ 2 + 3 * Dlo k ^ 2 + 3 * Emax R M ^ 2 := by
    intro k hk
    have h := hE0 k hk
    set e := (binSum X2 Y (2 * k) - S (2 * k) * Y) - (Dhi k - Dlo k) with he
    have : binSum X2 Y (2 * k) - S (2 * k) * Y = Dhi k - Dlo k + e := by rw [he]; ring
    rw [this]
    have h3 := sq_three (Dhi k) (Dlo k) e
    have : e ^ 2 ≤ Emax R M ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    linarith
  have hsubhi : ∑ k ∈ kRange X1 R, Dhi k ^ 2 ≤ Bhi :=
    (sum_le_sum_of_subset_of_nonneg (kRange_mono hRhi) (fun _ _ _ => sq_nonneg _)).trans hhi
  have hsublo : ∑ k ∈ kRange X1 R, Dlo k ^ 2 ≤ Blo :=
    (sum_le_sum_of_subset_of_nonneg (kRange_mono hRlo) (fun _ _ _ => sq_nonneg _)).trans hlo
  have hcard := card_kRange_le (X := X1) hR
  calc _ ≤ ∑ k ∈ kRange X1 R, (3 * Dhi k ^ 2 + 3 * Dlo k ^ 2 + 3 * Emax R M ^ 2) := sum_le_sum hpt
    _ = 3 * ∑ k ∈ kRange X1 R, Dhi k ^ 2 + 3 * ∑ k ∈ kRange X1 R, Dlo k ^ 2 +
          ((kRange X1 R).card : ℝ) * (3 * Emax R M ^ 2) := by
        rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum, mul_sum]
    _ ≤ 3 * Bhi + 3 * Blo + (R + 1) * (3 * Emax R M ^ 2) := by
        have : 0 ≤ 3 * Emax R M ^ 2 := by positivity
        nlinarith
    _ = _ := by ring

/-! ## Part 7. Asymptotics on one window of the minimal scale -/

theorem rpow_natpow {u : ℝ} (hu : 0 ≤ u) (n k : ℕ) {r : ℝ} (h : (n : ℝ) * r = k) :
    (u ^ n) ^ r = u ^ k := by
  rw [← Real.rpow_natCast u n, ← Real.rpow_mul hu, h, Real.rpow_natCast]

/-- `X₂ ≤ c₁^{-12/7} u^{300}` when `c₁ X₂^{7/12+ε₂} ≤ Y = u^{175}`, `X₂ ≥ 1`. -/
theorem x2_le {c1 ε2 X2 Y u : ℝ} (hc1 : 0 < c1) (hε2 : 0 ≤ ε2) (hX21 : 1 ≤ X2)
    (h1 : c1 * X2 ^ (7 / 12 + ε2) ≤ Y) (hYu : Y = u ^ (175 : ℕ)) (hu0 : 0 ≤ u) :
    X2 ≤ (1 / c1) ^ (12 / 7 : ℝ) * u ^ (300 : ℕ) := by
  have hY0 : 0 ≤ Y := by rw [hYu]; positivity
  have e1 : X2 ^ (7 / 12 : ℝ) ≤ Y / c1 := by
    rw [le_div_iff₀ hc1]
    have : X2 ^ (7 / 12 : ℝ) ≤ X2 ^ (7 / 12 + ε2) :=
      Real.rpow_le_rpow_of_exponent_le hX21 (by linarith)
    nlinarith
  have e2 : X2 = (X2 ^ (7 / 12 : ℝ)) ^ (12 / 7 : ℝ) := by
    rw [← Real.rpow_mul (by linarith)]; norm_num
  calc X2 = (X2 ^ (7 / 12 : ℝ)) ^ (12 / 7 : ℝ) := e2
    _ ≤ (Y / c1) ^ (12 / 7 : ℝ) := Real.rpow_le_rpow (by positivity) e1 (by norm_num)
    _ = (1 / c1) ^ (12 / 7 : ℝ) * Y ^ (12 / 7 : ℝ) := by
        rw [div_eq_mul_one_div Y c1, mul_comm Y, Real.mul_rpow (by positivity) hY0]
    _ = (1 / c1) ^ (12 / 7 : ℝ) * u ^ (300 : ℕ) := by
        rw [hYu, rpow_natpow hu0 175 300 (by norm_num)]

/-- **The error bound in powers of `u`.** -/
theorem emax_le {c4a KM R M u : ℝ} (hu1 : 1 ≤ u) (hM1 : 1 ≤ M) (hKM0 : 0 ≤ KM)
    (hMu : M ≤ KM * u ^ (300 : ℕ)) (hc4a : 0 ≤ c4a) (hR : 2 * R + 1 ≤ 3 / 2 * (c4a * u ^ (70 : ℕ))) :
    Emax R M ≤ (3 * c4a * (100 * KM ^ (1 / 100 : ℝ)) ^ 2 +
        8 * (100 * KM ^ (1 / 100 : ℝ)) ^ 3 * KM ^ (1 / 2 : ℝ) + 2 ^ 17 * KM ^ (1 / 4 : ℝ)) *
      u ^ (166 : ℕ) := by
  have hu0 : 0 ≤ u := by linarith
  have hupow : ∀ i j : ℕ, i ≤ j → u ^ i ≤ u ^ j := fun i j hij => pow_le_pow_right₀ hu1 hij
  have hMr : ∀ (r : ℝ) (k : ℕ), 0 ≤ r → (300 : ℝ) * r = k → M ^ r ≤ KM ^ r * u ^ k := by
    intro r k hr hk
    calc M ^ r ≤ (KM * u ^ (300 : ℕ)) ^ r := Real.rpow_le_rpow (by linarith) hMu hr
      _ = KM ^ r * u ^ k := by
          rw [Real.mul_rpow hKM0 (by positivity), rpow_natpow hu0 300 k hk]
  obtain ⟨cL, hcL⟩ : ∃ cL : ℝ, cL = 100 * KM ^ (1 / 100 : ℝ) := ⟨_, rfl⟩
  rw [← hcL]
  have hcL0 : 0 ≤ cL := by rw [hcL]; positivity
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlogM : Real.log M ≤ cL * u ^ (3 : ℕ) := by
    have e1 := Real.log_le_rpow_div (by linarith : 0 ≤ M) (show (0 : ℝ) < 1 / 100 by norm_num)
    have e2 := hMr (1 / 100) 3 (by norm_num) (by norm_num)
    have e3 : M ^ (1 / 100 : ℝ) / (1 / 100) = 100 * M ^ (1 / 100 : ℝ) := by ring
    rw [hcL]; nlinarith
  have hl2 : Real.log M ^ 2 ≤ cL ^ 2 * u ^ (6 : ℕ) := by
    calc Real.log M ^ 2 ≤ (cL * u ^ (3 : ℕ)) ^ 2 := pow_le_pow_left₀ hlogM0 hlogM 2
      _ = _ := by ring
  have hl3 : Real.log M ^ 3 ≤ cL ^ 3 * u ^ (9 : ℕ) := by
    calc Real.log M ^ 3 ≤ (cL * u ^ (3 : ℕ)) ^ 3 := pow_le_pow_left₀ hlogM0 hlogM 3
      _ = _ := by ring
  have hM12 := hMr (1 / 2) 150 (by norm_num) (by norm_num)
  have hM14 := hMr (1 / 4) 75 (by norm_num) (by norm_num)
  have u76 := hupow 76 166 (by norm_num)
  have u159 := hupow 159 166 (by norm_num)
  have u75 := hupow 75 166 (by norm_num)
  have t1 : 2 * (2 * R + 1) * Real.log M ^ 2 ≤ 3 * c4a * cL ^ 2 * u ^ (166 : ℕ) := by
    calc 2 * (2 * R + 1) * Real.log M ^ 2
        ≤ 2 * (3 / 2 * (c4a * u ^ (70 : ℕ))) * (cL ^ 2 * u ^ (6 : ℕ)) := by
          apply mul_le_mul (by linarith) hl2 (sq_nonneg _) (by positivity)
      _ = 3 * c4a * cL ^ 2 * u ^ (76 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left u76 (by positivity)
  have t2 : 8 * Real.log M ^ 3 * M ^ (1 / 2 : ℝ) ≤
      8 * cL ^ 3 * KM ^ (1 / 2 : ℝ) * u ^ (166 : ℕ) := by
    calc 8 * Real.log M ^ 3 * M ^ (1 / 2 : ℝ)
        ≤ 8 * (cL ^ 3 * u ^ (9 : ℕ)) * (KM ^ (1 / 2 : ℝ) * u ^ (150 : ℕ)) :=
          mul_le_mul (by linarith) hM12 (by positivity) (by positivity)
      _ = 8 * cL ^ 3 * KM ^ (1 / 2 : ℝ) * u ^ (159 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left u159 (by positivity)
  have t3 : 2 ^ 17 * M ^ (1 / 4 : ℝ) ≤ 2 ^ 17 * KM ^ (1 / 4 : ℝ) * u ^ (166 : ℕ) := by
    have : KM ^ (1 / 4 : ℝ) * u ^ (75 : ℕ) ≤ KM ^ (1 / 4 : ℝ) * u ^ (166 : ℕ) :=
      mul_le_mul_of_nonneg_left u75 (by positivity)
    nlinarith
  unfold Emax
  nlinarith

/-- **Logarithm against a power of `u`.** For `Y = u^{175} > 1`:
`u^{332} ≤ (175A/18)^A · Y² (log Y)^{-A}`. -/
theorem logpow_le {A Y u : ℝ} (hA : 0 < A) (hY1 : 1 < Y) (hYu : Y = u ^ (175 : ℕ))
    (hu0 : 0 ≤ u) :
    u ^ (332 : ℕ) ≤ (175 * A / 18) ^ A * (Y ^ 2 * Real.log Y ^ (-A)) := by
  have hYpos : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 18 / (175 * A) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηi : 175 * A / 18 = 1 / η := by rw [hη]; field_simp
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Real.log Y ^ A := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hlogY A
  have hLP : Real.log Y ^ (-A) = P⁻¹ := by rw [hP, Real.rpow_neg hlogY.le]
  have hPb : P ≤ (1 / η) ^ A * u ^ (18 : ℕ) := by
    have e1 := Real.log_le_rpow_div hYpos.le hη0
    have e2 : P ≤ (Y ^ η / η) ^ A := by rw [hP]; exact Real.rpow_le_rpow hlogY.le e1 hA.le
    have e3 : (Y ^ η / η) ^ A = (1 / η) ^ A * (Y ^ (η * A)) := by
      rw [div_eq_mul_one_div, Real.mul_rpow (by positivity) (by positivity), mul_comm,
        ← Real.rpow_mul hYpos.le]
    have e4 : Y ^ (η * A) = u ^ (18 : ℕ) := by
      rw [hYu]; apply rpow_natpow hu0 175 18; rw [hη]; field_simp; norm_num
    rw [e3, e4] at e2; exact e2
  have hY2u : Y ^ 2 = u ^ (350 : ℕ) := by rw [hYu, ← pow_mul]
  rw [hLP, hY2u, hηi, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hP0]
  calc u ^ (332 : ℕ) * P ≤ u ^ (332 : ℕ) * ((1 / η) ^ A * u ^ (18 : ℕ)) :=
        mul_le_mul_of_nonneg_left hPb (pow_nonneg hu0 _)
    _ = (1 / η) ^ A * u ^ (350 : ℕ) := by
        rw [show (350 : ℕ) = 332 + 18 from rfl, pow_add]; ring

/-- **A PP1993 term in Halupczok's units.** -/
theorem ppterm_le {C0 V a A c4 c5 Y X1 R : ℝ} (hA : 0 < A) (hc4 : 0 < c4) (hc5 : 0 < c5)
    (ha : 0 < a)
    (hY1 : 1 < Y) (hYX : Y ≤ 2 * X1) (hV0 : 0 ≤ V) (hVc : V ≤ (c5 + 1) * Y)
    (hR4 : (c4 * Y) ^ a ≤ 4 * R) :
    C0 * V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A) ≤
      max C0 0 * (4 * ((c5 + 1) / c4) ^ a) * (c5 + 1) ^ 2 * (R * Y ^ 2 * Real.log Y ^ (-A)) := by
  have hYpos : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hlogN : Real.log (2 * X1) ^ (-A) ≤ Real.log Y ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos hlogY (Real.log_le_log hYpos hYX) (by linarith)
  have hlogN0 : 0 ≤ Real.log (2 * X1) ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hVa : V ^ a ≤ 4 * ((c5 + 1) / c4) ^ a * R := by
    have e1 : V ^ a ≤ ((c5 + 1) * Y) ^ a := Real.rpow_le_rpow hV0 hVc ha.le
    have e2 : ((c5 + 1) * Y) ^ a = ((c5 + 1) / c4) ^ a * (c4 * Y) ^ a := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
    have e3 : ((c5 + 1) / c4) ^ a * (c4 * Y) ^ a ≤ ((c5 + 1) / c4) ^ a * (4 * R) :=
      mul_le_mul_of_nonneg_left hR4 (by positivity)
    linarith
  have hV2 : V ^ 2 ≤ (c5 + 1) ^ 2 * Y ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hV0 hVc 2
  have hC0p : 0 ≤ max C0 0 := le_max_right _ _
  have hR0 : 0 ≤ R := by
    have : 0 ≤ (c4 * Y) ^ a := by positivity
    linarith
  have hK : 0 ≤ max C0 0 * (4 * ((c5 + 1) / c4) ^ a * R) :=
    mul_nonneg hC0p (by positivity)
  have hK2 : 0 ≤ max C0 0 * (4 * ((c5 + 1) / c4) ^ a * R) * ((c5 + 1) ^ 2 * Y ^ 2) :=
    mul_nonneg hK (by positivity)
  have hP : 0 ≤ V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A) := by positivity
  calc C0 * V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A)
      = C0 * (V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A)) := by ring
    _ ≤ max C0 0 * (V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hP
    _ = max C0 0 * V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A) := by ring
    _ ≤ max C0 0 * (4 * ((c5 + 1) / c4) ^ a * R) * ((c5 + 1) ^ 2 * Y ^ 2) *
          Real.log Y ^ (-A) := by
        apply mul_le_mul _ hlogN hlogN0 hK2
        apply mul_le_mul _ hV2 (by positivity) hK
        exact mul_le_mul_of_nonneg_left hVa hC0p
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **One window.** CONDITIONAL ON `PP1993Goldbach`: the Halupczok mean square over a window of
length `R ≍ (c₄ Y)^{1/3+δ}` is `≪ R Y² L^{-A}`, for `δ ≤ ε₂/2`, `δ ≤ 1/24`. -/
theorem piece (hPP : PP1993Goldbach) {A ε2 δ : ℝ} (hA : 0 < A) (hε2 : 0 < ε2) (hδ : 0 < δ)
    (hδ2 : δ ≤ ε2 / 2) (hδ1 : δ ≤ 1 / 24) {c1 c4 c5 : ℝ} (hc1 : 0 < c1) (hc4 : 0 < c4)
    (hc5 : 0 < c5) :
    ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y → c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 →
      c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
      (c4 * Y) ^ (1 / 3 + δ) / 4 ≤ R → R ≤ (c4 * Y) ^ (1 / 3 + δ) / 2 →
      ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
        C * R * Y ^ 2 * Real.log Y ^ (-A) := by
  obtain ⟨C0, N0, hC0⟩ := hPP δ A hδ hA
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / 3 + δ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 7 / 12 + δ := ⟨_, rfl⟩
  rw [← ha, ← hb] at hC0
  rw [← ha]
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha3 : a ≤ 2 / 5 := by rw [ha]; linarith
  have ha13 : 1 / 3 ≤ a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  obtain ⟨Kpp, hKpp⟩ : ∃ K : ℝ, K = (c5 + 2) ^ b / (c4 * c1) := ⟨_, rfl⟩
  have hKpp0 : 0 ≤ Kpp := by rw [hKpp]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max 1 (max (c4 ^ a) (c4 ^ a / c4)) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact le_trans zero_le_one (le_max_left _ _)
  obtain ⟨KM, hKM⟩ : ∃ K : ℝ, K = (c5 + 3) * (1 / c1) ^ (12 / 7 : ℝ) := ⟨_, rfl⟩
  have hKM0 : 0 ≤ KM := by rw [hKM]; positivity
  obtain ⟨KE, hKE⟩ : ∃ K : ℝ, K = 3 * c4 ^ a * (100 * KM ^ (1 / 100 : ℝ)) ^ 2 +
      8 * (100 * KM ^ (1 / 100 : ℝ)) ^ 3 * KM ^ (1 / 2 : ℝ) + 2 ^ 17 * KM ^ (1 / 4 : ℝ) :=
    ⟨_, rfl⟩
  have hKE0 : 0 ≤ KE := by rw [hKE]; positivity
  obtain ⟨K1, hK1⟩ : ∃ K : ℝ, K = max C0 0 * (4 * ((c5 + 1) / c4) ^ a) * (c5 + 1) ^ 2 :=
    ⟨_, rfl⟩
  refine ⟨6 * K1 + 6 * KE ^ 2 * (175 * A / 18) ^ A,
    max (max 2 N0) (max (Kpp ^ (2 / ε2)) (max (T ^ (175 : ℕ)) (64 / c4))), ?_⟩
  intro X1 X2 Y R hY0 h1 h2 h4 h5 hR1 hR2
  have hY2 : 2 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY0
  have hYN0 : N0 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY0
  have hYK : Kpp ^ (2 / ε2) ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY0
  have hYT : T ^ (175 : ℕ) ≤ Y :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hY0
  have hY64 : 64 / c4 ≤ Y :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hY0
  have hYpos : 0 < Y := by linarith
  have hX21 : 1 ≤ X2 := by linarith
  -- u = Y^{1/175}
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Y ^ (1 / 175 : ℝ) := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hu0 : 0 ≤ u := by linarith
  have hYu : Y = u ^ (175 : ℕ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hYpos.le]; norm_num
  have huT : T ≤ u := by
    have := Real.rpow_le_rpow (pow_nonneg hT0 175) hYT (show (0 : ℝ) ≤ 1 / 175 by norm_num)
    rw [rpow_natpow hT0 175 1 (by norm_num), pow_one, ← hu] at this
    exact this
  have hupow : ∀ i j : ℕ, i ≤ j → u ^ i ≤ u ^ j := fun i j hij => pow_le_pow_right₀ hu1 hij
  -- (c4 Y)^a
  have hc4a0 : 0 ≤ c4 ^ a := by positivity
  have hYa : Y ^ a ≤ u ^ (70 : ℕ) := by
    calc Y ^ a ≤ Y ^ (2 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha3
      _ = u ^ (70 : ℕ) := by rw [hYu]; exact rpow_natpow hu0 175 70 (by norm_num)
  have hcY : (c4 * Y) ^ a ≤ c4 ^ a * u ^ (70 : ℕ) := by
    rw [Real.mul_rpow hc4.le hYpos.le]; exact mul_le_mul_of_nonneg_left hYa hc4a0
  have hTa : c4 ^ a ≤ u := by
    refine le_trans ?_ huT; rw [hT]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTa' : c4 ^ a / c4 ≤ u := by
    refine le_trans ?_ huT; rw [hT]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hu105 : u ≤ u ^ (105 : ℕ) := by simpa using hupow 1 105 (by norm_num)
  have hu175 : u ^ (105 : ℕ) * u ^ (70 : ℕ) = u ^ (175 : ℕ) := by rw [← pow_add]
  have hu70 : 0 ≤ u ^ (70 : ℕ) := by positivity
  have hcYY : (c4 * Y) ^ a ≤ Y := by
    calc (c4 * Y) ^ a ≤ c4 ^ a * u ^ (70 : ℕ) := hcY
      _ ≤ u ^ (105 : ℕ) * u ^ (70 : ℕ) := mul_le_mul_of_nonneg_right (hTa.trans hu105) hu70
      _ = Y := by rw [hu175, hYu]
  have hcYc : (c4 * Y) ^ a ≤ c4 * Y := by
    have e : c4 ^ a ≤ c4 * u ^ (105 : ℕ) := by
      rw [div_le_iff₀ hc4] at hTa'; nlinarith
    calc (c4 * Y) ^ a ≤ c4 ^ a * u ^ (70 : ℕ) := hcY
      _ ≤ c4 * u ^ (105 : ℕ) * u ^ (70 : ℕ) := mul_le_mul_of_nonneg_right e hu70
      _ = c4 * Y := by rw [mul_assoc, hu175, hYu]
  have hcY4 : 4 ≤ (c4 * Y) ^ a := by
    have h64 : (64 : ℝ) ≤ c4 * Y := by rw [div_le_iff₀ hc4] at hY64; linarith
    calc (4 : ℝ) = ((4 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [rpow_natpow (by norm_num) 3 1 (by norm_num), pow_one]
      _ ≤ (c4 * Y) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num; linarith)
          (by norm_num)
      _ ≤ (c4 * Y) ^ a := Real.rpow_le_rpow_of_exponent_le (by linarith) ha13
  have hR0 : 1 ≤ R := by linarith
  have h2R : 2 * R ≤ Y := by linarith
  have hV : 2 * R ≤ 2 * X1 - X2 - Y := by linarith
  have hc5X : c5 * Y ≤ c5 * X2 := mul_le_mul_of_nonneg_left h2 hc5.le
  have hc4Y : 0 ≤ c4 * Y := by positivity
  -- M = 2 X1 + 2 R
  have hX2u := x2_le hc1 hε2.le hX21 h1 hYu hu0
  have hM1 : 1 ≤ 2 * X1 + 2 * R := by linarith
  have hMu : 2 * X1 + 2 * R ≤ KM * u ^ (300 : ℕ) := by
    have : 2 * X1 + 2 * R ≤ (c5 + 3) * X2 := by linarith
    calc 2 * X1 + 2 * R ≤ (c5 + 3) * X2 := this
      _ ≤ (c5 + 3) * ((1 / c1) ^ (12 / 7 : ℝ) * u ^ (300 : ℕ)) :=
          mul_le_mul_of_nonneg_left hX2u (by linarith)
      _ = KM * u ^ (300 : ℕ) := by rw [hKM]; ring
  have hR3 : 2 * R + 1 ≤ 3 / 2 * (c4 ^ a * u ^ (70 : ℕ)) := by linarith
  have hEm := emax_le hu1 hM1 hKM0 hMu hc4a0 hR3
  rw [← hKE] at hEm
  -- PP1993 hypotheses at N = 2 X1
  have hN0 : N0 ≤ 2 * X1 := by linarith
  have hXpow : Kpp ≤ X2 ^ (ε2 / 2) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hKpp0 _) (hYK.trans h2)
      (by positivity : 0 ≤ ε2 / 2)
    rwa [← Real.rpow_mul hKpp0, show 2 / ε2 * (ε2 / 2) = 1 by field_simp, Real.rpow_one] at this
  have hNb : (2 * X1) ^ b ≤ 2 * X1 - X2 - Y := by
    have e1 : (2 * X1) ^ b ≤ (c5 + 2) ^ b * X2 ^ b := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hb0.le
    have e2 : X2 ^ b * X2 ^ (ε2 / 2) ≤ X2 ^ (7 / 12 + ε2) := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hX21 (by rw [hb]; linarith)
    have e3 : (c5 + 2) ^ b = c4 * c1 * Kpp := by rw [hKpp]; field_simp
    have hXb : 0 ≤ X2 ^ b := by positivity
    have e4 : c4 * c1 * X2 ^ (7 / 12 + ε2) ≤ c4 * Y := by
      have := mul_le_mul_of_nonneg_left h1 hc4.le; linarith
    calc (2 * X1) ^ b ≤ (c5 + 2) ^ b * X2 ^ b := e1
      _ = c4 * c1 * (Kpp * X2 ^ b) := by rw [e3]; ring
      _ ≤ c4 * c1 * (X2 ^ (ε2 / 2) * X2 ^ b) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXpow hXb) (by positivity)
      _ ≤ c4 * c1 * X2 ^ (7 / 12 + ε2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ ≤ c4 * Y := e4
      _ ≤ 2 * X1 - X2 - Y := h4
  have hhi := hC0 (2 * X1) (2 * X1 - X2) hN0 (by linarith) (by linarith)
  have hlo := hC0 (2 * X1) (2 * X1 - X2 - Y) hN0 hNb (by linarith)
  have e2X : 2 * X1 / 2 = X1 := by ring
  rw [e2X] at hhi hlo
  have hRlo : R ≤ (2 * X1 - X2 - Y) ^ a / 2 := by
    have := Real.rpow_le_rpow (by positivity) h4 ha0.le
    linarith
  have hRhi : R ≤ (2 * X1 - X2) ^ a / 2 := by
    have := Real.rpow_le_rpow (by linarith) (show 2 * X1 - X2 - Y ≤ 2 * X1 - X2 by linarith)
      ha0.le
    linarith
  have hcore := core_sum hhi hlo hYpos (by linarith) (by linarith) h2R hV hRhi hRlo
  -- the PP terms
  have hR4 : (c4 * Y) ^ a ≤ 4 * R := by linarith
  have hB1 := ppterm_le (C0 := C0) (X1 := X1) (R := R) (Y := Y) hA hc4 hc5 ha0 (by linarith) (by linarith)
    (show 0 ≤ 2 * X1 - X2 by linarith) (show 2 * X1 - X2 ≤ (c5 + 1) * Y by linarith) hR4
  have hB2 := ppterm_le (C0 := C0) (X1 := X1) (R := R) (Y := Y) hA hc4 hc5 ha0 (by linarith) (by linarith)
    (show 0 ≤ 2 * X1 - X2 - Y by linarith) (show 2 * X1 - X2 - Y ≤ (c5 + 1) * Y by linarith) hR4
  rw [← hK1] at hB1 hB2
  -- the error term
  have hEmax0 : 0 ≤ Emax R (2 * X1 + 2 * R) := by
    unfold Emax
    have := Real.log_nonneg hM1
    positivity
  have hEsq : Emax R (2 * X1 + 2 * R) ^ 2 ≤ KE ^ 2 * u ^ (332 : ℕ) := by
    calc Emax R (2 * X1 + 2 * R) ^ 2 ≤ (KE * u ^ (166 : ℕ)) ^ 2 := pow_le_pow_left₀ hEmax0 hEm 2
      _ = _ := by ring
  have hlp := logpow_le hA (by linarith) hYu hu0
  have hT3 : 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 ≤
      6 * KE ^ 2 * (175 * A / 18) ^ A * (R * Y ^ 2 * Real.log Y ^ (-A)) := by
    have e1 : 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 ≤ 6 * R * (KE ^ 2 * u ^ (332 : ℕ)) := by
      have : 3 * (R + 1) ≤ 6 * R := by linarith
      exact mul_le_mul this hEsq (sq_nonneg _) (by linarith)
    calc 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 ≤ 6 * R * (KE ^ 2 * u ^ (332 : ℕ)) := e1
      _ ≤ 6 * R * (KE ^ 2 * ((175 * A / 18) ^ A * (Y ^ 2 * Real.log Y ^ (-A)))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hlp (sq_nonneg _)
      _ = _ := by ring
  have e : (6 * K1 + 6 * KE ^ 2 * (175 * A / 18) ^ A) * R * Y ^ 2 * Real.log Y ^ (-A) =
      6 * (K1 * (R * Y ^ 2 * Real.log Y ^ (-A))) +
        6 * KE ^ 2 * (175 * A / 18) ^ A * (R * Y ^ 2 * Real.log Y ^ (-A)) := by ring
  rw [e]
  linarith

/-! ## Part 8. Theorem 5 and the F-0008 repair from PP1993 -/

/-- **`Theorem5` from the Goldbach analogue of PP1993 Theorem 3.** CONDITIONAL ON
`PP1993Goldbach` only. Each window is cut into pieces of length `≍ (c₄ Y)^{1/3+δ}`,
`δ = min(ε, ε₂, 1/12)/2`, and `piece` is applied to each. -/
theorem theorem5_of_PP (hPP : PP1993Goldbach) : Theorem5 := by
  intro A ε ε2 hA hε hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5
  set δ : ℝ := min (min ε ε2) (1 / 12) / 2 with hδ
  have hm1 := min_le_left (min ε ε2) (1 / 12)
  have hm2 := min_le_right (min ε ε2) (1 / 12)
  have hm3 := min_le_left ε ε2
  have hm4 := min_le_right ε ε2
  have hδ0 : 0 < δ := by
    rw [hδ]; have : 0 < min (min ε ε2) (1 / 12) := lt_min (lt_min hε hε2) (by norm_num)
    linarith
  have hδε : δ ≤ ε / 2 := by rw [hδ]; linarith
  have hδ2 : δ ≤ ε2 / 2 := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; linarith
  obtain ⟨C, Y0, hC⟩ := piece hPP hA hε2 hδ0 hδ2 hδ1 hc1 hc4
    (show 0 < c5 + 2 * c3 by positivity)
  set a : ℝ := 1 / 3 + δ with ha
  set K : ℝ := c4 ^ a / (4 * c2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C, max (max Y0 1) (K ^ (2 / ε)), ?_⟩
  intro X1 X2 Y R hY h1 h2 h3 h4 h5 h6 h7 h8
  have hY0 : Y0 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY1 : 1 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYK : K ^ (2 / ε) ≤ Y := le_trans (le_max_right _ _) hY
  set R0 := (c4 * Y) ^ a / 4 with hR0def
  have hR0 : 0 < R0 := by
    rw [hR0def]; have : 0 < (c4 * Y) ^ a := Real.rpow_pos_of_pos (by positivity) _
    linarith
  have hR0R : R0 ≤ R := by
    have e1 : (c4 * Y) ^ a = c4 ^ a * Y ^ a := Real.mul_rpow hc4.le (by linarith)
    have e2 : K ≤ Y ^ (ε / 2) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hYK (by positivity : 0 ≤ ε / 2)
      rwa [← Real.rpow_mul hK0, show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one] at this
    have e3 : Y ^ (ε / 2) * Y ^ a ≤ Y ^ (1 / 3 + ε) := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by rw [ha]; linarith)
    have e4 : c4 ^ a = 4 * c2 * K := by rw [hK]; field_simp
    have hYa : 0 ≤ Y ^ a := by positivity
    calc R0 = c2 * (K * Y ^ a) := by rw [hR0def, e1, e4]; ring
      _ ≤ c2 * (Y ^ (ε / 2) * Y ^ a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 hYa) hc2.le
      _ ≤ c2 * Y ^ (1 / 3 + ε) := mul_le_mul_of_nonneg_left e3 hc2.le
      _ ≤ R := h3
  obtain ⟨hm1, hlo, hhi⟩ := floor_pieces hR0 hR0R
  set m := ⌊R / R0⌋₊ with hmdef
  have hm0 : 0 < m := hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hRpos : 0 < R := lt_of_lt_of_le hR0 hR0R
  set g : ℕ → ℝ := fun k => (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 with hg
  have hgnn : ∀ k, 0 ≤ g k := fun k => sq_nonneg _
  have hpiece : ∀ j ∈ range m, ∑ k ∈ kRange (X1 + j * (R / m)) (R / m), g k ≤
      C * (R / m) * Y ^ 2 * Real.log Y ^ (-A) := by
    intro j hj
    have hj' : (j : ℝ) < m := by exact_mod_cast Finset.mem_range.mp hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjR : (j : ℝ) * (R / m) ≤ R := by
      rw [mul_div_assoc']; rw [div_le_iff₀ hmR]; nlinarith
    have hjR0 : 0 ≤ (j : ℝ) * (R / m) := by positivity
    exact hC (X1 + j * (R / m)) X2 Y (R / m) hY0 h1 h2 (by linarith) (by nlinarith)
      (by rw [hR0def] at hlo; exact hlo) (by rw [hR0def] at hhi; linarith)
  calc ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2
      = ∑ k ∈ kRange X1 R, g k := rfl
    _ ≤ ∑ j ∈ range m, ∑ k ∈ kRange (X1 + j * (R / m)) (R / m), g k :=
        sum_kRange_le_pieces X1 R hRpos m hm0 g hgnn
    _ ≤ ∑ j ∈ range m, C * (R / m) * Y ^ 2 * Real.log Y ^ (-A) := Finset.sum_le_sum hpiece
    _ = C * R * Y ^ 2 * Real.log Y ^ (-A) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- `Theorem5Min` from PP1993. CONDITIONAL ON `PP1993Goldbach`. -/
theorem theorem5Min_of_PP (hPP : PP1993Goldbach) : Theorem5Min :=
  theorem5Min_of_theorem5 (theorem5_of_PP hPP)

/-- **HEADLINE. The F-0008 repair, CONDITIONAL ON `Theorem3` and `PP1993Goldbach`.** -/
theorem theorem2Zeroed_U1496 (h3 : Theorem3) (hPP : PP1993Goldbach) : Theorem2Zeroed :=
  theorem2Zeroed_U1462 h3 (theorem5_of_PP hPP)

/-- Theorem 2 in the lab's coprime reading, CONDITIONAL ON `Theorem3` and `PP1993Goldbach`. -/
theorem theorem2_U1496 (h3 : Theorem3) (hPP : PP1993Goldbach) : Theorem2 :=
  theorem2_U1462 h3 (theorem5_of_PP hPP)

end LeanLab.Halupczok2012
