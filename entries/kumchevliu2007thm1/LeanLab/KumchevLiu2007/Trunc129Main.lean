module

public import LeanLab.KumchevLiu2007.Decomp1534a
public import LeanLab.KumchevLiu2007.Decomp1534c
public import LeanLab.KumchevLiu2007.Decomp506a
public import LeanLab.KumchevLiu2007.Decomp506b

/-!
Kumchev and Liu, arXiv 0801.0130, paper P0088. Truncated window sieve route
for the transition regime of `Task129L.residual_full_range_extension`, final
assembly.

For X < n < X + Y with Y = X ^ (7 / 12 + ε / 2) the window of page 2 displays
4 to 6, anchored at X, is truncated: its m range has length
W(n) = sqrt Y - max (sqrt Y / 2) (sqrt (n - X)). This file combines three
inputs, taken as hypotheses whose types are the conclusions of the interface
theorems of the truncated route:
the truncated sieve bound of pages 16 and 17, displays 56 to 59,
the comparison of the residual with the sifted count of page 17 display 58,
and the lower bound for the weighted integer count r2 of page 2 display 6.
It adds Lemma 3.8 of page 14, display 49, by Chebyshev counting, and an
elementary count of the edge integers n where W(n) is below sqrt Y times
L to the -A.

This file declares nothing but theorems. The lemmas adapted from Decomp129 are
proved again here under new names, with the definitions written out, because
Decomp129 imports Leaves129 and cannot be imported.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Trunc129

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Pages 16 and 17, displays 56 to 59, truncated window version: every power
of the logarithm is eventually below every positive power of X. Used to show
that the truncated window length is at least 4 away from the edge and that
H times L to the -A is at least 1. -/
theorem log_rpow_le_rpow_large (A t c : ℝ) (ht : 0 < t) (hc : 0 < c) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X → c * Real.log X ^ A ≤ X ^ t := by
  have h := (isLittleO_log_rpow_rpow_atTop A ht).bound (show (0 : ℝ) < 1 / c by positivity)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X0 1, le_max_right _ _, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have h1 : ‖Real.log X ^ A‖ ≤ 1 / c * ‖X ^ t‖ := hX0 X ((le_max_left _ _).trans hX)
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl A),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) t)] at h1
  calc c * Real.log X ^ A ≤ c * (1 / c * X ^ t) := mul_le_mul_of_nonneg_left h1 hc.le
    _ = X ^ t := by field_simp

/-- Page 17, displays 58 and 59, truncated window version: a real Q with Q^2 at
most L lies below the sieve level z = exp of L to the 1 - delta/2. -/
theorem le_level {X δ Q : ℝ} (hδ : δ < 1) (hL1 : 1 ≤ Real.log X)
    (hQ : Q ^ 2 ≤ Real.log X) : Q ≤ Real.exp (Real.log X ^ (1 - δ / 2)) := by
  have h1 : Q ≤ Real.sqrt (Real.log X) := Real.le_sqrt_of_sq_le hQ
  have h2 : Real.sqrt (Real.log X) ≤ Real.log X ^ (1 - δ / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h3 : Real.log X ^ (1 - δ / 2) ≤ Real.exp (Real.log X ^ (1 - δ / 2)) := by
    linarith [Real.add_one_le_exp (Real.log X ^ (1 - δ / 2))]
  linarith

/-- Page 17 and page 14 Lemma 3.8 display 49, truncated window version: the
constraint P = L^B at most z. For L large in terms of B and delta, L^B is at
most exp of L to the 1 - delta/2. -/
theorem pow_le_level (B δ : ℝ) (hB : 0 < B) (hδ : δ < 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ X : ℝ, M ≤ Real.log X →
      Real.log X ^ B ≤ Real.exp (Real.log X ^ (1 - δ / 2)) := by
  have hs0 : 0 < (1 - δ / 2) / 2 := by linarith
  refine ⟨max 1 ((B / ((1 - δ / 2) / 2)) ^ (1 / ((1 - δ / 2) / 2))), le_max_left _ _, ?_⟩
  intro X hX
  have hL1 : 1 ≤ Real.log X := le_trans (le_max_left _ _) hX
  have hLpos : 0 < Real.log X := by linarith
  have hBs : 0 ≤ B / ((1 - δ / 2) / 2) := by positivity
  have hpow : B / ((1 - δ / 2) / 2) ≤ Real.log X ^ ((1 - δ / 2) / 2) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hBs _) (le_trans (le_max_right _ _) hX) hs0.le
    rwa [one_div, Real.rpow_inv_rpow hBs hs0.ne'] at h
  have hlog : Real.log (Real.log X) ≤ Real.log X ^ ((1 - δ / 2) / 2) / ((1 - δ / 2) / 2) :=
    Real.log_le_rpow_div hLpos.le hs0
  have hLs : 0 ≤ Real.log X ^ ((1 - δ / 2) / 2) := Real.rpow_nonneg hLpos.le _
  have hkey : B * Real.log (Real.log X) ≤ Real.log X ^ (1 - δ / 2) := by
    have e : Real.log X ^ (1 - δ / 2) =
        Real.log X ^ ((1 - δ / 2) / 2) * Real.log X ^ ((1 - δ / 2) / 2) := by
      rw [← Real.rpow_add hLpos]; congr 1; ring
    rw [e]
    calc B * Real.log (Real.log X) ≤
          B * (Real.log X ^ ((1 - δ / 2) / 2) / ((1 - δ / 2) / 2)) :=
          mul_le_mul_of_nonneg_left hlog hB.le
      _ = B / ((1 - δ / 2) / 2) * Real.log X ^ ((1 - δ / 2) / 2) := by ring
      _ ≤ Real.log X ^ ((1 - δ / 2) / 2) * Real.log X ^ ((1 - δ / 2) / 2) :=
          mul_le_mul_of_nonneg_right hpow hLs
  rw [Real.rpow_def_of_pos hLpos B]
  apply Real.exp_le_exp.mpr
  linarith [mul_comm (Real.log (Real.log X)) B]

/-- Page 17, truncated window version: Chebyshev counting, used to pass from
the mean square bound of Lemma 3.8, page 14 display 49, to an exceptional set.
Elements where f exceeds t number at most the sum of f over the interval
divided by t. -/
theorem cnt_mul_le_sum {S : ℕ → Prop} {X H t : ℝ} (f : ℕ → ℝ) (hX : 0 ≤ X)
    (hf : ∀ n, 0 ≤ f n) (hS : ∀ n : ℕ, X < (n : ℝ) → S n → t < f n) :
    (cntIoc S X H : ℝ) * t ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, f n := by
  classical
  set T := (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)
  have hsub : T ⊆ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
    intro n hn
    obtain ⟨hr, hXn, _⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX).mpr hXn, ?_⟩
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hcard : (cntIoc S X H : ℝ) * t = ∑ n ∈ T, t := by
    simp [cntIoc, T, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  calc ∑ n ∈ T, t ≤ ∑ n ∈ T, f n := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨_, hXn, hSn⟩ := Finset.mem_filter.mp hn
        exact (hS n hXn hSn).le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

/-- Page 14 Lemma 3.8, display 49, for j = 2, with the series of page 2 display
7 and the partial product of page 13 display 45 written out. Used for the
truncated window version of Proposition 2. Supplied by the proved lab theorem
Task506aTask342e.lemma38_two_proved. -/
theorem lemma38_two_written (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖(∑ q ∈ Finset.Icc 1 ⌊(P)⌋₊, U1534.A2 n q) - ∏ p ∈ (Finset.range (⌊(Q)⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  exact Task506aTask342e.lemma38_two_proved A ε hA hε

/-- Page 17, last display of the proof of Proposition 2, truncated window
version: the Chebyshev step behind the comparison of P2(n, z) with S2(n, P),
for arbitrary sequences p and s. If the mean square of s - p over the interval
is at most y and p has norm at least c / L on H2, then the n in H2 with
norm of p - s above 2 / c times L to the -1 times the norm of s number at most
y times L to the 4. -/
theorem cheb_generic {X H c L y : ℝ} (p s : ℕ → ℂ) (hX : 0 ≤ X) (hc : 0 < c) (hL : 0 < L)
    (hLc : 2 / c ≤ L) (hlow : ∀ n, InH2 n → c / L ≤ ‖p n‖)
    (hsum : ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, ‖s n - p n‖ ^ 2 ≤ y) :
    (cntIoc (fun n => InH2 n ∧ 2 / c * L ^ (-1 : ℝ) * ‖s n‖ < ‖p n - s n‖) X H : ℝ) ≤
      y * L ^ (4 : ℝ) := by
  have hu0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hu : L⁻¹ ≤ c / 2 := by
    rw [inv_le_comm₀ hL (by positivity)]
    calc (c / 2)⁻¹ = 2 / c := by rw [inv_div]
      _ ≤ L := hLc
  have key : ∀ n : ℕ, X < (n : ℝ) → (InH2 n ∧ 2 / c * L ^ (-1 : ℝ) * ‖s n‖ < ‖p n - s n‖) →
      L⁻¹ * L⁻¹ * (L⁻¹ * L⁻¹) < ‖s n - p n‖ ^ 2 := by
    rintro n - ⟨hn, hbad⟩
    rw [Real.rpow_neg_one] at hbad
    have hpn := hlow n hn
    have hlt : L⁻¹ * L⁻¹ < ‖p n - s n‖ := by
      by_contra hcon'
      have hcon : ‖p n - s n‖ ≤ L⁻¹ * L⁻¹ := not_lt.mp hcon'
      have hcp : c * L⁻¹ ≤ ‖p n‖ := by
        calc c * L⁻¹ = c / L := by ring
          _ ≤ ‖p n‖ := hpn
      have htri : ‖p n‖ - ‖s n‖ ≤ ‖p n - s n‖ := norm_sub_norm_le _ _
      have huu : L⁻¹ * L⁻¹ ≤ c / 2 * L⁻¹ := mul_le_mul_of_nonneg_right hu hu0
      have hsl : c / 2 * L⁻¹ ≤ ‖s n‖ := by linarith
      have hfin : L⁻¹ * L⁻¹ ≤ 2 / c * L⁻¹ * ‖s n‖ := by
        calc L⁻¹ * L⁻¹ = 2 / c * L⁻¹ * (c / 2 * L⁻¹) := by field_simp
          _ ≤ 2 / c * L⁻¹ * ‖s n‖ := mul_le_mul_of_nonneg_left hsl (by positivity)
      linarith
    have h0 : 0 ≤ L⁻¹ * L⁻¹ := by positivity
    rw [norm_sub_rev, sq]
    exact mul_self_lt_mul_self h0 hlt
  have hcheb := cnt_mul_le_sum (S := fun n => InH2 n ∧ 2 / c * L ^ (-1 : ℝ) * ‖s n‖ <
      ‖p n - s n‖) (H := H)
    (fun n => ‖s n - p n‖ ^ 2) hX (fun n => by positivity) key
  have ht : 0 < L⁻¹ * L⁻¹ * (L⁻¹ * L⁻¹) := by positivity
  have hcnt := le_trans hcheb hsum
  have e4 : (L⁻¹ * L⁻¹ * (L⁻¹ * L⁻¹))⁻¹ = L ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [← e4, ← div_eq_mul_inv, le_div_iff₀ ht]
  exact hcnt

/-- Page 17, last display of the proof of Proposition 2, truncated window
version. By display 47 and Lemma 3.8 on page 14, display 49, with x = X, y = H
and Q = z, P2(n, z) = S2(n, P) times 1 + O of L to the -1 for all but
O of H L to the -A integers n in H2 in the interval, provided P = L^B with B
at least A + 5. The series of page 2 display 7 and the partial product of
page 13 display 45 are written out. -/
theorem product_series_count (A B δ ε : ℝ) (hA : 0 < A) (hB : A + 5 ≤ B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ C K2 X0 : ℝ, 0 < C ∧ 0 ≤ K2 ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
      (cntIoc (fun n => InH2 n ∧
        K2 * Real.log X ^ (-1 : ℝ) * ‖∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q‖ <
        ‖(∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter Nat.Prime,
            (1 + U1534.A2 n p)) -
          ∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q‖) X H : ℝ) ≤
        C * H / Real.log X ^ A := by
  obtain ⟨c, Q2, hc, _, hl⟩ := Task129a.P2_lower_explicit
  have hBpos : 0 < B := by linarith
  obtain ⟨ε', hε'pos, hε'δ, hε'7⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ δ / 2 ∧ ε' ≤ 7 / 18 :=
    ⟨min (δ / 2) (7 / 18), lt_min (by linarith) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨C, x0, hC, hx0, hm⟩ := lemma38_two_written (max 2 (A + 4)) ε' (le_max_left _ _) hε'pos
  obtain ⟨M, hM1, hMz⟩ := pow_le_level B δ hBpos hδ1
  refine ⟨2 * C, 2 / c, max x0 (Real.exp (max M (max (Q2 ^ 2) (2 / c)))), by positivity,
    by positivity, le_trans hx0 (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hx0X : x0 ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by linarith
  have hLM : max M (max (Q2 ^ 2) (2 / c)) ≤ Real.log X := by
    have hE := le_trans (le_max_right _ _) hX
    have := Real.log_le_log (Real.exp_pos _) hE
    rwa [Real.log_exp] at this
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hH
  have hX1 : 1 ≤ X := by linarith
  have hyε : X ^ ε' ≤ H :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hH
  have hPz := hMz X (le_trans (le_max_left _ _) hLM)
  have hL1 : 1 ≤ Real.log X := le_trans hM1 (le_trans (le_max_left _ _) hLM)
  have hLpos : 0 < Real.log X := by linarith
  have hQ2z : Q2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) :=
    le_level hδ1 hL1 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLM))
  have hLc : 2 / c ≤ Real.log X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLM)
  have hzle : Real.exp (Real.log X ^ (1 - δ / 2)) ≤ Real.exp (Real.log X ^ (1 - ε')) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hPpos : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hLpos B
  have hsum := hm X H (Real.log X ^ B) (Real.exp (Real.log X ^ (1 - δ / 2)))
    hx0X hyε hHX hPpos hPz hzle
  have hlz : 0 < Real.log X ^ (1 - δ / 2) := Real.rpow_pos_of_pos hLpos _
  have hLle : Real.log X ^ (1 - δ / 2) ≤ Real.log X := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (show 1 - δ / 2 ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hlow : ∀ n : ℕ, InH2 n → c / Real.log X ≤
      ‖∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter Nat.Prime,
        (1 + U1534.A2 n p)‖ := by
    intro n hn
    have h0 := hl _ hQ2z n hn
    rw [Real.log_exp] at h0
    exact (div_le_div_of_nonneg_left hc.le hlz hLle).trans h0
  have hfinal : (cntIoc (fun n => InH2 n ∧
      2 / c * Real.log X ^ (-1 : ℝ) * ‖∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q‖ <
      ‖(∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter Nat.Prime,
          (1 + U1534.A2 n p)) -
        ∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q‖) X H : ℝ) ≤
      C * (H / Real.log X ^ B * Real.log X + H / Real.log X ^ (max 2 (A + 4))) *
        Real.log X ^ (4 : ℝ) :=
    cheb_generic
      (fun n => ∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter
        Nat.Prime, (1 + U1534.A2 n p))
      (fun n => ∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q)
      hXpos.le hc hLpos hLc hlow hsum
  have hA' : A + 4 ≤ max 2 (A + 4) := le_max_right _ _
  have b1 : H / Real.log X ^ B * Real.log X * Real.log X ^ (4 : ℝ) ≤ H * Real.log X ^ (-A) := by
    have : H / Real.log X ^ B * Real.log X * Real.log X ^ (4 : ℝ) =
        H * Real.log X ^ (-B + 1 + 4) := by
      rw [Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_neg hLpos.le, Real.rpow_one]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hHpos.le
  have b2 : H / Real.log X ^ (max 2 (A + 4)) * Real.log X ^ (4 : ℝ) ≤
      H * Real.log X ^ (-A) := by
    have : H / Real.log X ^ (max 2 (A + 4)) * Real.log X ^ (4 : ℝ) =
        H * Real.log X ^ (-(max 2 (A + 4)) + 4) := by
      rw [Real.rpow_add hLpos, Real.rpow_neg hLpos.le]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hHpos.le
  calc _ ≤ C * (H / Real.log X ^ B * Real.log X + H / Real.log X ^ (max 2 (A + 4))) *
        Real.log X ^ (4 : ℝ) := hfinal
    _ = C * (H / Real.log X ^ B * Real.log X * Real.log X ^ (4 : ℝ) +
        H / Real.log X ^ (max 2 (A + 4)) * Real.log X ^ (4 : ℝ)) := by ring
    _ ≤ C * (H * Real.log X ^ (-A) + H * Real.log X ^ (-A)) :=
        mul_le_mul_of_nonneg_left (add_le_add b1 b2) hC.le
    _ = 2 * C * H / Real.log X ^ A := by rw [Real.rpow_neg hLpos.le]; ring

/-- Page 17 displays 58 and 59 with the lower bound of page 13 display 48,
truncated window version. The sieve bound with main term W L^-2 log L V and
error sqrt Y L^-(A+4), where W is the truncated window length, gives
R at most a constant times W L^(-3+delta) P2(n, z) when W is at least
sqrt Y L^-A, that is away from the edge. -/
theorem sieve_arith {R Ks W s s2 L V Pn c δ A : ℝ} (hKs : 0 < Ks) (hW : 0 ≤ W) (hL1 : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hc : 0 < c) (hPn0 : 0 ≤ Pn)
    (hV : V ≤ 1 * Pn / L ^ (1 - δ / 2)) (hP : c / L ^ (1 - δ / 2) ≤ Pn)
    (hs2 : s2 = s) (hedge : s * L ^ (-A) ≤ W)
    (hR : R ≤ Ks * (W * L ^ (-2 : ℝ) * Real.log L * V + s2 * L ^ (-(A + 4)))) :
    R ≤ Ks * (2 / δ + 1 / c) * W * L ^ (-3 + δ) * Pn := by
  subst hs2
  have hLpos : 0 < L := by linarith
  have hlz : 0 < L ^ (1 - δ / 2) := Real.rpow_pos_of_pos hLpos _
  have hlogL : Real.log L ≤ L ^ (δ / 2) / (δ / 2) :=
    Real.log_le_rpow_div hLpos.le (by linarith)
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hV' : V ≤ Pn / L ^ (1 - δ / 2) := by rw [one_mul] at hV; exact hV
  have hW' : 0 ≤ Pn / L ^ (1 - δ / 2) := by positivity
  have t1 : Real.log L * V ≤ (2 / δ) * (L ^ (δ / 2) * (Pn / L ^ (1 - δ / 2))) := by
    calc Real.log L * V ≤ Real.log L * (Pn / L ^ (1 - δ / 2)) :=
          mul_le_mul_of_nonneg_left hV' hlogL0
      _ ≤ (L ^ (δ / 2) / (δ / 2)) * (Pn / L ^ (1 - δ / 2)) :=
          mul_le_mul_of_nonneg_right hlogL hW'
      _ = _ := by field_simp
  have e1 : L ^ (-2 : ℝ) * L ^ (δ / 2) / L ^ (1 - δ / 2) = L ^ (-3 + δ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hLpos.le, ← Real.rpow_add hLpos,
      ← Real.rpow_add hLpos]
    ring_nf
  have T1 : W * L ^ (-2 : ℝ) * Real.log L * V ≤ W * L ^ (-3 + δ) * Pn * (2 / δ) := by
    have h : L ^ (-2 : ℝ) * (Real.log L * V) ≤ L ^ (-3 + δ) * Pn * (2 / δ) := by
      calc L ^ (-2 : ℝ) * (Real.log L * V) ≤
            L ^ (-2 : ℝ) * ((2 / δ) * (L ^ (δ / 2) * (Pn / L ^ (1 - δ / 2)))) :=
            mul_le_mul_of_nonneg_left t1 (Real.rpow_nonneg hLpos.le _)
        _ = (L ^ (-2 : ℝ) * L ^ (δ / 2) / L ^ (1 - δ / 2)) * Pn * (2 / δ) := by ring
        _ = _ := by rw [e1]
    calc W * L ^ (-2 : ℝ) * Real.log L * V = W * (L ^ (-2 : ℝ) * (Real.log L * V)) := by ring
      _ ≤ W * (L ^ (-3 + δ) * Pn * (2 / δ)) := mul_le_mul_of_nonneg_left h hW
      _ = _ := by ring
  have hLle : L ^ (1 - δ / 2) ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (show 1 - δ / 2 ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hPc : L ^ (-1 : ℝ) ≤ Pn * (1 / c) := by
    rw [Real.rpow_neg_one]
    have h1 : c / L ≤ c / L ^ (1 - δ / 2) := div_le_div_of_nonneg_left hc.le hlz hLle
    have h2 : c / L ≤ Pn := h1.trans hP
    rw [mul_one_div, le_div_iff₀ hc]
    calc L⁻¹ * c = c / L := by ring
      _ ≤ Pn := h2
  have T2 : s2 * L ^ (-(A + 4)) ≤ W * L ^ (-3 + δ) * Pn * (1 / c) := by
    have hL4 : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) * L ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    have h3 : L ^ (-3 : ℝ) ≤ L ^ (-3 + δ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h4 : L ^ (-4 : ℝ) ≤ L ^ (-3 + δ) * (Pn * (1 / c)) := by
      rw [hL4]
      exact mul_le_mul h3 hPc (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hLpos.le _)
    have hsplit : L ^ (-(A + 4)) = L ^ (-A) * L ^ (-4 : ℝ) := by
      rw [← Real.rpow_add hLpos]; congr 1; ring
    calc s2 * L ^ (-(A + 4)) = (s2 * L ^ (-A)) * L ^ (-4 : ℝ) := by rw [hsplit]; ring
      _ ≤ W * L ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right hedge (Real.rpow_nonneg hLpos.le _)
      _ ≤ W * (L ^ (-3 + δ) * (Pn * (1 / c))) := mul_le_mul_of_nonneg_left h4 hW
      _ = _ := by ring
  calc R ≤ Ks * (W * L ^ (-2 : ℝ) * Real.log L * V + s2 * L ^ (-(A + 4))) := hR
    _ ≤ Ks * (W * L ^ (-3 + δ) * Pn * (2 / δ) + W * L ^ (-3 + δ) * Pn * (1 / c)) :=
        mul_le_mul_of_nonneg_left (add_le_add T1 T2) hKs.le
    _ = Ks * (2 / δ + 1 / c) * W * L ^ (-3 + δ) * Pn := by ring

/-- Page 16 Proposition 2 and page 17, truncated window version: a relative
error bound P2 = S2 times 1 + O of L to the -1 gives a norm comparison. -/
theorem norm_le_of_close {a b : ℂ} {K2 Li : ℝ} (hK2 : 0 ≤ K2) (_hLi0 : 0 ≤ Li)
    (hLi : Li ≤ 1) (h : ‖a - b‖ ≤ K2 * Li * ‖b‖) : ‖a‖ ≤ (1 + K2) * ‖b‖ := by
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa using norm_add_le (a - b) b
  have hb : 0 ≤ ‖b‖ := norm_nonneg b
  have : K2 * Li * ‖b‖ ≤ K2 * ‖b‖ := by
    have := mul_le_mul_of_nonneg_left hLi hK2
    exact mul_le_mul_of_nonneg_right (by simpa using this) hb
  nlinarith

/-- Page 17, truncated window version: combining the sieve bound R0 of order
W L^(-3+delta) P2(n, z), the comparison P2 = S2 times 1 + O of L to the -1,
and r2 at least c W L^-2, with W the truncated window length. -/
theorem compare_core_general {R I S Q K1 K2 c Ke Y2 L2 Ld L3d L3 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 ≤ K2) (hc : 0 < c) (hKe : 0 < Ke) (hS : 0 ≤ S)
    (hY2 : 0 < Y2) (hL2 : 0 < L2) (hLd : 0 < Ld) (hL3d : 0 ≤ L3d)
    (hexp : L2 * Ld = L3) (hmono : L3d ≤ L3)
    (hres : R ≤ K1 * Y2 * L3d * Q) (hQ : Q ≤ (1 + K2) * S) (hI : c * Y2 * L2 ≤ I) :
    R ≤ (Ke + K1 * (1 + K2) / c) * (I * S) * Ld := by
  have hA0 : 0 ≤ K1 * Y2 * L3d := by positivity
  have h1 : R ≤ K1 * Y2 * L3d * ((1 + K2) * S) :=
    hres.trans (mul_le_mul_of_nonneg_left hQ hA0)
  have h2 : K1 * Y2 * L3d * ((1 + K2) * S) ≤ K1 * Y2 * L3 * ((1 + K2) * S) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have h3 : K1 * Y2 * L3 * ((1 + K2) * S) =
      (K1 * (1 + K2) / c) * (c * Y2 * L2) * S * Ld := by
    rw [← hexp]; field_simp
  have h4 : (K1 * (1 + K2) / c) * (c * Y2 * L2) * S * Ld ≤
      (K1 * (1 + K2) / c) * I * S * Ld := by
    have hk : 0 ≤ K1 * (1 + K2) / c := by positivity
    have := mul_le_mul_of_nonneg_left hI hk
    have := mul_le_mul_of_nonneg_right this hS
    exact mul_le_mul_of_nonneg_right this hLd.le
  have hI0 : 0 ≤ I := le_trans (by positivity) hI
  have h5 : (K1 * (1 + K2) / c) * I * S * Ld ≤ (Ke + K1 * (1 + K2) / c) * (I * S) * Ld := by
    have h0 : 0 ≤ I * S * Ld := by positivity
    nlinarith
  linarith

/-- Page 17, truncated window version: the comparison of the previous theorem
with c = 1/2 and the lower bound for r2 of page 2 display 6 in the form
W / 2 times L^-2, as supplied by the truncated integer main term bound. -/
theorem compare_core {R I S Q K1 K2 Y2 L2 Ld L3d L3 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 ≤ K2) (hS : 0 ≤ S)
    (hY2 : 0 < Y2) (hL2 : 0 < L2) (hLd : 0 < Ld) (hL3d : 0 ≤ L3d)
    (hexp : L2 * Ld = L3) (hmono : L3d ≤ L3)
    (hres : R ≤ K1 * Y2 * L3d * Q) (hQ : Q ≤ (1 + K2) * S) (hI : Y2 / 2 * L2 ≤ I) :
    R ≤ (1 + K1 * (1 + K2) / (1 / 2)) * (|I| * S) * Ld := by
  have hI' : (1 / 2 : ℝ) * Y2 * L2 ≤ |I| := by
    calc (1 / 2 : ℝ) * Y2 * L2 = Y2 / 2 * L2 := by ring
      _ ≤ I := hI
      _ ≤ |I| := le_abs_self I
  exact compare_core_general hK1 hK2 (by norm_num) one_pos hS hY2 hL2 hLd hL3d hexp hmono
    hres hQ hI'

/-- Bookkeeping for the exceptional sets of page 17, truncated window version:
monotonicity of the interval count, where the implication may use
X < n and n at most X + H. -/
theorem cnt_mono_gt {S T : ℕ → Prop} {X H : ℝ}
    (h : ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) ≤ X + H → S n → T n) (hXH : 0 ≤ X + H) :
    cntIoc S X H ≤ cntIoc T X H := by
  unfold cntIoc
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hr, hXn, hS⟩ := Finset.mem_filter.mp hn
  have hnle : (n : ℝ) ≤ X + H :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))).trans (Nat.floor_le hXH)
  exact Finset.mem_filter.mpr ⟨hr, hXn, h n hXn hnle hS⟩

/-- Bookkeeping for the exceptional sets of page 17, truncated window version:
the interval count of a property is at most the size of any finite set that
contains every natural with the property. -/
theorem cnt_le_card_of_forall_mem {S : ℕ → Prop} {X H : ℝ} (F : Finset ℕ)
    (h : ∀ n : ℕ, S n → n ∈ F) : cntIoc S X H ≤ F.card := by
  unfold cntIoc
  apply Finset.card_le_card
  intro n hn
  obtain ⟨_, _, hS⟩ := Finset.mem_filter.mp hn
  exact h n hS

/-- Page 2 displays 4 to 6, truncated window version: the number of naturals
strictly between two reals a and b is at most b - a + 1. Used to count the
edge integers n where the truncated window is too short. -/
theorem cnt_open_interval_le (X H a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (cntIoc (fun n => a < (n : ℝ) ∧ (n : ℝ) < b) X H : ℝ) ≤ b - a + 1 := by
  have hcard : cntIoc (fun n => a < (n : ℝ) ∧ (n : ℝ) < b) X H ≤
      (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).card :=
    cnt_le_card_of_forall_mem (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)
      (fun n hS => Finset.mem_Ioc.mpr ⟨(Nat.floor_lt ha).mpr hS.1, Nat.le_floor hS.2.le⟩)
  rw [Nat.card_Ioc] at hcard
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have h1 : ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) = (⌊b⌋₊ : ℝ) - (⌊a⌋₊ : ℝ) := Nat.cast_sub hfl
  have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (ha.trans hab)
  have h3 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have h4 : (cntIoc (fun n => a < (n : ℝ) ∧ (n : ℝ) < b) X H : ℝ) ≤
      ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- Page 2 displays 4 to 6 and page 16 Proposition 2, truncated window version:
the edge integers. If the truncated window length
sqrt Y - max (sqrt Y / 2) (sqrt (n - X)) is below sqrt Y times Li, with
Li at most 1/4, then n - X exceeds Y (1 - 2 Li). The integers n below X + Y
with this property lie in an interval of length 2 Y Li, and an n at most X + H
of this kind forces Y at most 2 H, so they number at most 5 H Li when H Li is
at least 1. -/
theorem edge_count {X H Yv Li : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H) (hYv : 0 < Yv)
    (hLi0 : 0 < Li) (hLi : Li ≤ 1 / 4) (hHL : 1 ≤ H * Li) :
    (cntIoc (fun n => (n : ℝ) < X + Yv ∧
      Real.sqrt Yv - max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) < Real.sqrt Yv * Li)
        X H : ℝ) ≤ 5 * (H * Li) := by
  have hs0 : 0 < Real.sqrt Yv := Real.sqrt_pos.mpr hYv
  have hss : Real.sqrt Yv * Real.sqrt Yv = Yv := Real.mul_self_sqrt hYv.le
  have hquarter : 0 ≤ Yv * (1 / 4 - Li) := mul_nonneg hYv.le (by linarith)
  have himp : ∀ n : ℕ, ((n : ℝ) < X + Yv ∧
      Real.sqrt Yv - max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) < Real.sqrt Yv * Li) →
      X + Yv * (1 - 2 * Li) < (n : ℝ) := by
    rintro n ⟨_, h2⟩
    have hmax : Real.sqrt Yv * (1 - Li) <
        max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) := by linarith
    have hhalf : Real.sqrt Yv / 2 ≤ Real.sqrt Yv * (1 - Li) := by
      nlinarith [mul_nonneg hs0.le (show (0 : ℝ) ≤ 1 / 4 - Li by linarith)]
    have hsq : Real.sqrt Yv * (1 - Li) < Real.sqrt ((n : ℝ) - X) := by
      rcases lt_max_iff.mp hmax with h | h
      · linarith
      · exact h
    have h0 : 0 ≤ Real.sqrt Yv * (1 - Li) :=
      mul_nonneg hs0.le (by linarith)
    have h5 : (Real.sqrt Yv * (1 - Li)) ^ 2 < (n : ℝ) - X := (Real.lt_sqrt h0).mp hsq
    have h6 : (Real.sqrt Yv * (1 - Li)) ^ 2 = Yv * (1 - 2 * Li) + Yv * Li ^ 2 := by
      linear_combination (1 - Li) ^ 2 * hss
    have h7 : 0 ≤ Yv * Li ^ 2 := by positivity
    linarith
  by_cases hYH : Yv ≤ 2 * H
  · have hab : X + Yv * (1 - 2 * Li) ≤ X + Yv := by
      nlinarith [mul_nonneg hYv.le hLi0.le]
    have ha0 : 0 ≤ X + Yv * (1 - 2 * Li) := by
      nlinarith [mul_nonneg hYv.le (show (0 : ℝ) ≤ 1 - 2 * Li by linarith)]
    have hc1 : cntIoc (fun n => (n : ℝ) < X + Yv ∧
        Real.sqrt Yv - max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) < Real.sqrt Yv * Li)
          X H ≤
        cntIoc (fun n => X + Yv * (1 - 2 * Li) < (n : ℝ) ∧ (n : ℝ) < X + Yv) X H :=
      U1534.cnt_mono (fun n hS => ⟨himp n hS, hS.1⟩) X H
    have hc2 := cnt_open_interval_le X H (X + Yv * (1 - 2 * Li)) (X + Yv) ha0 hab
    have hc3 : (cntIoc (fun n => (n : ℝ) < X + Yv ∧
        Real.sqrt Yv - max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) < Real.sqrt Yv * Li)
          X H : ℝ) ≤
        (cntIoc (fun n => X + Yv * (1 - 2 * Li) < (n : ℝ) ∧ (n : ℝ) < X + Yv) X H : ℝ) := by
      exact_mod_cast hc1
    have h8 : Yv * Li ≤ 2 * H * Li := mul_le_mul_of_nonneg_right hYH hLi0.le
    nlinarith
  · have hYH' : 2 * H < Yv := lt_of_not_ge hYH
    have hle : cntIoc (fun n => (n : ℝ) < X + Yv ∧
        Real.sqrt Yv - max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) < Real.sqrt Yv * Li)
          X H ≤ cntIoc (fun _ => False) X H := by
      refine cnt_mono_gt ?_ (by linarith)
      intro n _ hnle hS
      have han := himp n hS
      nlinarith
    have hz : cntIoc (fun _ => False) X H = 0 := by simp [cntIoc]
    have hzero : cntIoc (fun n => (n : ℝ) < X + Yv ∧
        Real.sqrt Yv - max (Real.sqrt Yv / 2) (Real.sqrt ((n : ℝ) - X)) < Real.sqrt Yv * Li)
          X H = 0 := Nat.le_zero.mp (hle.trans hz.le)
    rw [hzero]
    have hHLi : 0 ≤ H * Li := mul_nonneg hH hLi0.le
    simp only [Nat.cast_zero]
    linarith

/-- Page 17, the end of the proof of Proposition 2, truncated window version:
the exceptional set splits into the Lemma 3.8 exceptional set, page 14 display
49, and the edge set where the truncated window length W is below the
threshold. Away from both, the pointwise comparison rules out the bad event. -/
theorem count_split {X H C2 K K2 Linv Ld sLi Ye Yb D : ℝ} {I R W : ℕ → ℝ} {S Pz : ℕ → ℂ}
    (hXH : 0 ≤ X + H)
    (hpoint : ∀ n : ℕ, InH2 n → X < (n : ℝ) → (n : ℝ) < Yb → sLi ≤ W n →
      ‖Pz n - S n‖ ≤ K2 * Linv * ‖S n‖ → |R n| ≤ K * (|I n| * ‖S n‖) * Ld)
    (hexc : (cntIoc (fun n => InH2 n ∧ K2 * Linv * ‖S n‖ < ‖Pz n - S n‖) X H : ℝ) ≤
      C2 * H / D)
    (hedge : (cntIoc (fun n => (n : ℝ) < Yb ∧ W n < sLi) X H : ℝ) ≤ 5 * H / D) :
    (cntIoc (fun n => Ye < (n : ℝ) ∧ (n : ℝ) < Yb ∧ InH2 n ∧
      K * ‖((I n : ℝ) : ℂ) * S n‖ * Ld < |R n|) X H : ℝ) ≤ (C2 + 5) * H / D := by
  have hcnt : cntIoc (fun n => Ye < (n : ℝ) ∧ (n : ℝ) < Yb ∧ InH2 n ∧
      K * ‖((I n : ℝ) : ℂ) * S n‖ * Ld < |R n|) X H ≤
      cntIoc (fun n => InH2 n ∧ K2 * Linv * ‖S n‖ < ‖Pz n - S n‖) X H +
      cntIoc (fun n => (n : ℝ) < Yb ∧ W n < sLi) X H := by
    refine le_trans ?_ (U1534.cnt_or_le _ _ X H)
    refine cnt_mono_gt ?_ hXH
    rintro n hXn - ⟨-, hnb, hn, hbad⟩
    by_cases hedge' : W n < sLi
    · exact Or.inr ⟨hnb, hedge'⟩
    · refine Or.inl ⟨hn, ?_⟩
      by_contra hgood
      have h1 := hpoint n hn hXn hnb (not_lt.mp hedge') (not_lt.mp hgood)
      have hnorm : ‖((I n : ℝ) : ℂ) * S n‖ = |I n| * ‖S n‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm] at hbad
      exact absurd h1 (not_le.mpr hbad)
  have hcntR : (cntIoc (fun n => Ye < (n : ℝ) ∧ (n : ℝ) < Yb ∧ InH2 n ∧
      K * ‖((I n : ℝ) : ℂ) * S n‖ * Ld < |R n|) X H : ℝ) ≤
      (cntIoc (fun n => InH2 n ∧ K2 * Linv * ‖S n‖ < ‖Pz n - S n‖) X H : ℝ) +
      (cntIoc (fun n => (n : ℝ) < Yb ∧ W n < sLi) X H : ℝ) := by exact_mod_cast hcnt
  calc _ ≤ _ := hcntR
    _ ≤ C2 * H / D + 5 * H / D := add_le_add hexc hedge
    _ = (C2 + 5) * H / D := by ring

/-- Pages 16 and 17, displays 56 to 59, Proposition 2, with page 2 displays 4 to 6,
page 13 Lemma 3.7 and page 14 Lemma 3.8 display 49: the transition regime of the
full range residual extension, truncated window version. For epsilon at most
11/18 and X < n < X + Y with the windows anchored at X, the residual of display
35 is at most K times the main term times L to the -1 + delta for all but
C H L^-A integers n in H2. The three inputs are hypotheses: hsieve is the
truncated sieve bound with main term W L^-2 log L V, hres compares the residual
with the sifted count of display 58, and hmain is the lower bound W / 2 times
L^-2 for r2 of page 2 display 6, where
W = sqrt Y - max (sqrt Y / 2) (sqrt (n - X)) is the truncated window length.
The conclusion is the hypothesis htrans of
Task129L.residual_full_range_extension_of_transition_agy61, written out. -/
theorem transition_of_inputs (A : ℝ) (hA : 0 < A)
    (hsieve : ∀ (A' B δ ε : ℝ), 0 < A' → 0 < B → 0 < δ → δ < 1 → 0 < ε → ε ≤ 11 / 18 →
      ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → (n : ℝ) < X + Task506b.Y X ε →
        Task506b.siftedCount X B δ ε n ≤ K *
          ((Real.sqrt (Task506b.Y X ε) - max (Real.sqrt (Task506b.Y X ε) / 2) (Real.sqrt ((n : ℝ) - X))) * Real.log X ^ (-2 : ℝ) *
              Real.log (Real.log X) * Task506b.sieveProduct X δ n + Task506b.errorScale X ε A'))
    (hres : ∀ (B δ ε : ℝ), 0 < B → 0 < δ → 0 < ε → ε ≤ 11 / 18 →
    ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ,
      |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))| ≤
        Task506b.siftedCount X B δ ε n)
    (hmain : ∀ (ε : ℝ), 0 < ε → ε ≤ 11 / 18 →
    ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) < X + Task506b.Y X ε →
      4 ≤ Real.sqrt (Task506b.Y X ε) - max (Real.sqrt (Task506b.Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) →
      (Real.sqrt (Task506b.Y X ε) - max (Real.sqrt (Task506b.Y X ε) / 2) (Real.sqrt ((n : ℝ) - X))) / 2 *
          Real.log X ^ (-2 : ℝ) ≤
        ∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 11 / 18 →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧
          (n : ℝ) < X + X ^ (7 / 12 + ε / 2) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  refine ⟨A + 5, by linarith, ?_⟩
  intro B hB δ ε hδ hε hε1
  have hBpos : 0 < B := by linarith
  obtain ⟨δ', hδ'pos, hδ'1, hδ'le⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' < 1 ∧ δ' ≤ δ :=
    ⟨min δ (1 / 2), lt_min hδ (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  obtain ⟨Ks, Xs, hKs, hs⟩ := hsieve (A + 4) B δ' ε (by linarith) hBpos hδ'pos hδ'1 hε hε1
  obtain ⟨Xr, hr⟩ := hres B δ' ε hBpos hδ'pos hε hε1
  obtain ⟨Xm, hm⟩ := hmain ε hε hε1
  obtain ⟨c, P0, hc, hP0, hl⟩ := Task129a.P2_lower_explicit
  obtain ⟨C2, K2, X2, hC2, hK2, hX2, h2⟩ :=
    product_series_count A B δ' ε hA hB hδ'pos hδ'1 hε
  obtain ⟨Xg, hXg1, hg⟩ := log_rpow_le_rpow_large A (7 / 24) 4 (by norm_num) (by norm_num)
  have hK1 : 0 < Ks * (2 / δ' + 1 / c) := by positivity
  refine ⟨C2 + 5, 1 + Ks * (2 / δ' + 1 / c) * (1 + K2) / (1 / 2),
    max (max Xs Xr) (max (max Xm X2)
      (max Xg (Real.exp (max (P0 ^ 2) (max 1 ((4 : ℝ) ^ (1 / A))))))),
    by positivity, by positivity,
    le_trans hX2 (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))),
    ?_⟩
  intro X H hX hH1 hH2 hH3
  have hXs' : Xs ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXr' : Xr ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXm' : Xm ≤ X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have hX2' : X2 ≤ X :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have hXg' : Xg ≤ X :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
  have hXe : Real.exp (max (P0 ^ 2) (max 1 ((4 : ℝ) ^ (1 / A)))) ≤ X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
  have hX1 : 1 ≤ X := hXg1.trans hXg'
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hH1
  have hLM : max (P0 ^ 2) (max 1 ((4 : ℝ) ^ (1 / A))) ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos _) hXe
    rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log X := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hLpos : 0 < Real.log X := by linarith
  have hL4 : (4 : ℝ) ^ (1 / A) ≤ Real.log X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLM)
  have h4A : ((4 : ℝ) ^ (1 / A)) ^ A = 4 := by
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hA.ne', Real.rpow_one]
  have hLA4 : 4 ≤ Real.log X ^ A := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / A)) ^ A := h4A.symm
      _ ≤ Real.log X ^ A := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hL4 hA.le
  have hLA0 : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hLpos A
  have hLi0 : 0 < Real.log X ^ (-A) := Real.rpow_pos_of_pos hLpos _
  have hLi : Real.log X ^ (-A) ≤ 1 / 4 := by
    calc Real.log X ^ (-A) = (Real.log X ^ A)⁻¹ := Real.rpow_neg hLpos.le A
      _ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hLA4
      _ = 1 / 4 := by norm_num
  have hLALi : Real.log X ^ A * Real.log X ^ (-A) = 1 := by
    rw [Real.rpow_neg hLpos.le]
    exact mul_inv_cancel₀ hLA0.ne'
  have hgX : 4 * Real.log X ^ A ≤ X ^ (7 / 24 : ℝ) := hg X hXg'
  have hYdef : Task506b.Y X ε = X ^ (7 / 12 + ε / 2) := rfl
  have hYpos : 0 < Task506b.Y X ε := by rw [hYdef]; exact Real.rpow_pos_of_pos hXpos _
  have hsX : X ^ (7 / 24 : ℝ) ≤ Real.sqrt (Task506b.Y X ε) := by
    rw [hYdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hsLi4 : 4 ≤ Real.sqrt (Task506b.Y X ε) * Real.log X ^ (-A) := by
    calc (4 : ℝ) = 4 * Real.log X ^ A * Real.log X ^ (-A) := by
          rw [mul_assoc, hLALi, mul_one]
      _ ≤ X ^ (7 / 24 : ℝ) * Real.log X ^ (-A) := mul_le_mul_of_nonneg_right hgX hLi0.le
      _ ≤ Real.sqrt (Task506b.Y X ε) * Real.log X ^ (-A) :=
          mul_le_mul_of_nonneg_right hsX hLi0.le
  have hHX : X ^ (7 / 24 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)).trans hH1
  have hHLi : 1 ≤ H * Real.log X ^ (-A) := by
    calc (1 : ℝ) = Real.log X ^ A * Real.log X ^ (-A) := hLALi.symm
      _ ≤ H * Real.log X ^ (-A) := mul_le_mul_of_nonneg_right (by linarith) hLi0.le
  have hP0z : P0 ≤ Real.exp (Real.log X ^ (1 - δ' / 2)) :=
    le_level hδ'1 hL1 ((le_max_left _ _).trans hLM)
  have hz2 : 2 ≤ Real.exp (Real.log X ^ (1 - δ' / 2)) := hP0.trans hP0z
  have hs2 : Task506b.Y X ε ^ (1 / 2 : ℝ) = Real.sqrt (Task506b.Y X ε) := by
    rw [Real.sqrt_eq_rpow]
  refine count_split
    (W := fun n : ℕ => Real.sqrt (Task506b.Y X ε) -
      max (Real.sqrt (Task506b.Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)))
    (Pz := fun n : ℕ => ∏ p ∈ (Finset.range
      (⌊(Real.exp (Real.log X ^ (1 - δ' / 2)))⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p))
    (K2 := K2) (Linv := Real.log X ^ (-1 : ℝ))
    (sLi := Real.sqrt (Task506b.Y X ε) * Real.log X ^ (-A)) (by linarith) ?_ ?_ ?_
  · intro n hn hXn hnb hWn hclose
    have hres1 := hr X hXr' n
    have hs1 := hs X hXs' n hn hXn hnb
    unfold Task506b.errorScale Task506b.sieveProduct at hs1
    have hV := Task129s.sieve_product_explicit (Real.exp (Real.log X ^ (1 - δ' / 2))) hz2 n
    have hP := hl (Real.exp (Real.log X ^ (1 - δ' / 2))) hP0z n hn
    rw [Real.log_exp] at hV hP
    have hW4 := hsLi4.trans hWn
    have hm1 := hm X hXm' n hXn hnb hW4
    have hR1 := sieve_arith hKs (le_trans (by norm_num) hW4) hL1 hδ'pos hδ'1 hc
      (norm_nonneg _) hV hP hs2 hWn (hres1.trans hs1)
    have hLinv : Real.log X ^ (-1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    have hLinv0 : 0 ≤ Real.log X ^ (-1 : ℝ) := Real.rpow_nonneg hLpos.le _
    have hprod := norm_le_of_close hK2 hLinv0 hLinv hclose
    have hexp : Real.log X ^ (-2 : ℝ) * Real.log X ^ (-1 + δ) = Real.log X ^ (-3 + δ) := by
      rw [← Real.rpow_add hLpos]; ring_nf
    have hmono : Real.log X ^ (-3 + δ') ≤ Real.log X ^ (-3 + δ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact compare_core hK1 hK2 (norm_nonneg _) (lt_of_lt_of_le (by norm_num) hW4)
      (Real.rpow_pos_of_pos hLpos _) (Real.rpow_pos_of_pos hLpos _)
      (Real.rpow_nonneg hLpos.le _) hexp hmono hR1 hprod hm1
  · exact h2 X H hX2' hH1 hH3
  · have e : 5 * (H * Real.log X ^ (-A)) = 5 * H / Real.log X ^ A := by
      rw [Real.rpow_neg hLpos.le]; ring
    exact (edge_count (Yv := Task506b.Y X ε) hXpos.le hHpos.le hYpos hLi0 hLi hHLi).trans e.le


end LeanLab.KumchevLiu2007.Trunc129
