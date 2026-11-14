module

public import LeanLab.Linnik.U1469Mertens

/-!
The convergence of `R₀`, the cited input `R0Summable` of U-1466, PROVED unconditionally.

Li-Liu, arXiv 2610.15784, display (15): `R₀ = ∑'_{d odd squarefree} 1/(ε(d) ∏_{p | d}(p-2))`,
`ε(d)` the order of `2` mod `d`. Li-Liu cite Pintz-Ruzsa 2003 Lemma 1 for `R₀ < ∞`.

Route, a Romanov-Erdős style dyadic argument, not Pintz-Ruzsa's own proof.
1. For odd `d`, `d | 2^{ε(d)} - 1`, so `ε(d) ≤ x` forces `d | Q_x := ∏_{k=1}^{x}(2^k - 1)`.
2. Hence `∑_{d odd, ε(d) ≤ x} w(d) ≤ ∑_{d | Q_x} w(d) = ∏_{p | Q_x, p > 2}(p-1)/(p-2)`,
   the lab's `prod_expand` of U-1464.
3. `Q_x ≤ 2^{x²}`, so `Q_x` has at most `x² ≤ 2x²` prime factors, and U-1466's `prod_bound`
   with U-1469's Mertens constant `e^{24}` gives `≤ 3 e^{26} log x` for `x ≥ 2`.
4. Group `d` by `j = ⌊log₂ ε(d)⌋`, so `2^j ≤ ε(d) < 2^{j+1}`: block `j` contributes at most
   `2^{-j} · 3 e^{26} (j+1) log 2`, and `∑_j (j+1)/2^j = 4`.
So every partial sum of `R₀` is at most `12 e^{26} log 2`, and `R₀` converges.
Numerics: numerics/r0_U1474.py and .out: the partial sum over odd squarefree `d ≤ 2·10⁵` is
about `1.936`, `C₀` times it about `1.2781 < 1.2784421041`; the block bounds of step 2 and 3
hold for `x = 2, 4, 8, 16, 32`. The explicit constant `12 e^{26} log 2 ≈ 1.63·10¹²` is crude
and KNOWN in spirit, it is not a literature claim.

Contents.
* `dvd_two_pow_eps`, `dvd_Q`, `Q_le`: steps 1 and 3, PROVED.
* `block_le`: steps 2 and 3, PROVED.
* `partial_le`: every finite partial sum `≤ 12 e^{26} log 2`, PROVED.
* `r0Summable`: `U1466Display17.R0Summable`, PROVED unconditionally.
* `R0_le`: `R₀ ≤ 12 e^{26} log 2`, PROVED.
* `display17`: `U1464Display20.Display17`, PROVED unconditionally.
* `r6_lower10`: `U1469Mertens.r6_lower9` with `R0Summable` discharged.

Unit U-1474, run 20261022T0804Z-19316. AI-written Lean code, Claude. KNOWN mathematics.
Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1474R0

open Set Real Filter Finset Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1447Display30
open LeanLab.Linnik.U1458Lemma42
open LeanLab.Linnik.U1464Display20
open LeanLab.Linnik.U1466Display17
open LeanLab.Linnik.U1469Mertens

/-- `Q_x = ∏_{k=1}^{x}(2^k - 1)`. -/
def Q (x : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 x, (2 ^ k - 1)

lemma Q_ne_zero (x : ℕ) : Q x ≠ 0 := by
  unfold Q
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  omega

lemma Q_le (x : ℕ) : Q x ≤ 2 ^ (x * x) := by
  unfold Q
  calc ∏ k ∈ Finset.Icc 1 x, (2 ^ k - 1) ≤ (2 ^ x) ^ (Finset.Icc 1 x).card :=
        Finset.prod_le_pow_card _ _ _ fun k hk => by
          have := (Finset.mem_Icc.mp hk).2
          have : 2 ^ k ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) this
          exact (Nat.sub_le _ _).trans this
    _ = 2 ^ (x * x) := by rw [Nat.card_Icc, ← pow_mul]; congr 1

/-- **Step 1, PROVED**: for odd `d`, `d | 2^{ε(d)} - 1`. -/
lemma dvd_two_pow_eps {d : ℕ} (_hd : Odd d) : d ∣ 2 ^ eps d - 1 := by
  have h1 : (2 : ZMod d) ^ eps d = 1 := pow_orderOf_eq_one _
  rw [← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rw [h1, sub_self]

lemma dvd_Q {d x : ℕ} (hd : Odd d) (hx : eps d ≤ x) : d ∣ Q x :=
  (dvd_two_pow_eps hd).trans (Finset.dvd_prod_of_mem _
    (Finset.mem_Icc.mpr ⟨eps_pos hd, hx⟩))

/-- **Steps 2 and 3, PROVED**: for `x ≥ 2` and any finite `S`,
`∑_{d ∈ S, d odd, ε(d) ≤ x} w(d) ≤ 3 e^{26} log x`. -/
lemma block_le (S : Finset ℕ) {x : ℕ} (hx : 2 ≤ x) :
    ∑ d ∈ S.filter (fun d => Odd d ∧ eps d ≤ x), wt d ≤
      Real.exp 24 * 3 * Real.exp 2 * Real.log x := by
  have h1 : ∑ d ∈ S.filter (fun d => Odd d ∧ eps d ≤ x), wt d ≤ ∑ d ∈ (Q x).divisors, wt d := by
    refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => wt_nonneg d)
    have hd' := (Finset.mem_filter.mp hd).2
    exact Nat.mem_divisors.mpr ⟨dvd_Q hd'.1 hd'.2, Q_ne_zero x⟩
  rw [← prod_expand (Q_ne_zero x)] at h1
  have hcard : (Q x).primeFactors.card ≤ 2 * x ^ 2 := by
    have := card_pf_le (Q_ne_zero x) (Q_le x)
    nlinarith
  have h2 := prod_bound oddPrimes_prod_le hx hcard
  have hm : max (Real.exp 24) 0 = Real.exp 24 := max_eq_left (Real.exp_pos _).le
  rw [hm] at h2
  linarith

/-- The dyadic index `j(d) = ⌊log₂ ε(d)⌋`. -/
noncomputable def jd (d : ℕ) : ℕ := Nat.log 2 (eps d)

/-- The block weight `g(j) = 3 e^{26} log 2 · (j+1)/2^j`. -/
noncomputable def g (j : ℕ) : ℝ :=
  Real.exp 24 * 3 * Real.exp 2 * Real.log 2 * (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j)

lemma g_summable : Summable g := by
  have h1 : Summable (fun j : ℕ => (j : ℝ) ^ 1 * (1 / 2 : ℝ) ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h3 : Summable (fun j : ℕ => ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) := by
    refine (h1.add h2).congr fun j => ?_
    simp only [pow_one]; ring
  exact h3.mul_left _

lemma g_nonneg (j : ℕ) : 0 ≤ g j := by
  unfold g
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  positivity

/-- `∑_j (j+1)/2^j = 4`. -/
lemma tsum_g : ∑' j, g j = Real.exp 24 * 3 * Real.exp 2 * Real.log 2 * 4 := by
  unfold g
  rw [tsum_mul_left]
  congr 1
  have h1 : ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num)]; norm_num
  have h2 : ∑' j : ℕ, (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hs1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := (1 / 2 : ℝ)) 1
      (by norm_num)
  have hs2 : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑' j : ℕ, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j
      = ∑' j : ℕ, ((j : ℝ) * (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) := by
        congr 1; ext j; ring
    _ = 4 := by rw [hs1.tsum_add hs2, h1, h2]; norm_num

/-- One dyadic block, PROVED: `∑_{d ∈ S, d odd, j(d) = j} w(d)/ε(d) ≤ g(j)`. -/
lemma dyadic_le (S : Finset ℕ) (j : ℕ) :
    ∑ d ∈ S.filter (fun d => Odd d ∧ jd d = j), wt d / (eps d : ℝ) ≤ g j := by
  have hx : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have step1 : ∑ d ∈ S.filter (fun d => Odd d ∧ jd d = j), wt d / (eps d : ℝ) ≤
      ∑ d ∈ S.filter (fun d => Odd d ∧ jd d = j), wt d * (1 / 2 : ℝ) ^ j := by
    refine sum_le_sum fun d hd => ?_
    have hd' := (Finset.mem_filter.mp hd).2
    have he := eps_pos hd'.1
    have hle : 2 ^ j ≤ eps d := by
      rw [← hd'.2]; exact Nat.pow_log_le_self 2 he.ne'
    have hle' : (2 : ℝ) ^ j ≤ eps d := by exact_mod_cast hle
    rw [div_eq_mul_one_div, one_div_pow]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpow hle') (wt_nonneg d)
  have step2 : ∑ d ∈ S.filter (fun d => Odd d ∧ jd d = j), wt d ≤
      ∑ d ∈ S.filter (fun d => Odd d ∧ eps d ≤ 2 ^ (j + 1)), wt d := by
    refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => wt_nonneg d)
    have hd' := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨hd'.1, hd'.2.1, ?_⟩
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (eps d)
    rw [show Nat.log 2 (eps d) = j from hd'.2.2] at this
    exact this.le
  have step3 := block_le S hx
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * Real.log 2 := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  rw [hlog] at step3
  rw [← Finset.sum_mul] at step1
  have hq : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
  calc _ ≤ (∑ d ∈ S.filter (fun d => Odd d ∧ jd d = j), wt d) * (1 / 2 : ℝ) ^ j := step1
    _ ≤ (Real.exp 24 * 3 * Real.exp 2 * (((j : ℝ) + 1) * Real.log 2)) * (1 / 2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right (step2.trans step3) hq
    _ = g j := by unfold g; ring

/-- **Every finite partial sum of `R₀` is at most `12 e^{26} log 2`, PROVED**. -/
theorem partial_le (S : Finset ℕ) :
    ∑ d ∈ S, wt d / (eps d : ℝ) ≤ Real.exp 24 * 3 * Real.exp 2 * Real.log 2 * 4 := by
  have hodd : ∑ d ∈ S, wt d / (eps d : ℝ) = ∑ d ∈ S.filter Odd, wt d / (eps d : ℝ) := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rfl
    · simp [wt, h]
  rw [hodd]
  set T := S.filter Odd
  have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image jd) (g := jd)
    (fun d hd => Finset.mem_image_of_mem jd hd) (fun d => wt d / (eps d : ℝ))
  rw [← hfib, ← tsum_g]
  calc ∑ j ∈ T.image jd, ∑ d ∈ T with jd d = j, wt d / (eps d : ℝ)
      ≤ ∑ j ∈ T.image jd, g j := by
        refine sum_le_sum fun j _ => ?_
        have e : T.filter (fun d => jd d = j) = S.filter (fun d => Odd d ∧ jd d = j) := by
          ext d; simp [T, Finset.mem_filter, and_assoc]
        rw [e]; exact dyadic_le S j
    _ ≤ ∑' j, g j := g_summable.sum_le_tsum _ (fun j _ => g_nonneg j)

/-- **`R0Summable` of U-1466, PROVED unconditionally**: `R₀` of (15) converges. -/
theorem r0Summable : R0Summable :=
  summable_of_sum_range_le (fun d => div_nonneg (wt_nonneg d) (Nat.cast_nonneg _))
    (fun n => partial_le (range n))

/-- **An explicit bound, PROVED**: `R₀ ≤ 12 e^{26} log 2`, crude; numerically `R₀ ≈ 1.936`. -/
theorem R0_le : ∑' d : ℕ, wt d / (eps d : ℝ) ≤ 12 * Real.exp 26 * Real.log 2 := by
  have h := Real.tsum_le_of_sum_range_le
    (fun d => div_nonneg (wt_nonneg d) (Nat.cast_nonneg _)) (fun n => partial_le (range n))
  have e : Real.exp 24 * 3 * Real.exp 2 * Real.log 2 * 4 = 12 * Real.exp 26 * Real.log 2 := by
    rw [show (26 : ℝ) = 24 + 2 by norm_num, Real.exp_add]; ring
  linarith

/-- **Lemma 3.1, display (17), PROVED unconditionally**. -/
theorem display17 : Display17 := display17_of' r0Summable

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON** the cited Lemma 4.1 `Lemma41 κ P ε` for every `ε > 0`,
display (18) `Lemma31_18`, Proposition 3.2 `Prop32 Bdef (A_* + T)`, the cited (31)
`Display31 6.7814`, `MinorSup1924 P`, the conditions (24) on `P` and the cited constants of
`k6_wired`. This is `U1469Mertens.r6_lower9` with `R0Summable` discharged. -/
theorem r6_lower10 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814)
    (h18 : Lemma31_18)
    (h32 : Prop32 Bdef (fun i j => (LiLiu.Astar i j : ℝ) + T i j)) :
    ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      (∀ ε > 0, Lemma41 κ P ε) →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) :=
  r6_lower9 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h18 r0Summable h32

/-! ### Vacuity and sanity -/

/-- `Q_4 = 1 · 3 · 7 · 15 = 315`. -/
theorem Q_four : Q 4 = 315 := by decide

/-- `15 | Q_4`, as step 1 predicts from `ε(15) = 4`. -/
theorem fifteen_dvd_Q : 15 ∣ Q 4 :=
  dvd_Q (by decide) (by rw [wt_eps_instance.2])

end LeanLab.Linnik.U1474R0
