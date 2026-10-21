module

public import Mathlib
public import LeanLab.GoldbachAverage.OddSum
public import LeanLab.PNTPort.StrongPNT.Bridge

/-!
P0051 Goldston-Suriajaya, Theorem 7, first line, unconditional:
`Σ_{n ≤ N, n odd} ψ₂(n) = 2 N log N + O(N)`, PROVED from the prime number theorem with error
term, LeanLab.PNTPort.psi_explicit_strong, ported from PrimeNumberTheoremAnd.
Route: for odd n one of a, n - a is even, and an even a with Λ(a) ≠ 0 is 2^j; so
Σ_{n ≤ N odd} ψ₂(n) = 2 Σ_{1 ≤ j ≤ log₂ N} log 2 · ψ_odd(N - 2^j), and ψ_odd(x) = x + O(N / log N)
uniformly for x ≤ N, by the PNT for x ≥ √N and by Chebyshev below.
AI-written Lean code, Claude, run 20261018T0002Z-3485, unit U-0913. KNOWN mathematics.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `Λ` on odd arguments, `0` on even ones. -/
def fO (a : ℕ) : ℝ := if Even a then 0 else Λ a

lemma fE_add_fO (a : ℕ) : fE a + fO a = Λ a := by
  unfold fE fO; split_ifs <;> simp

lemma fO_nonneg (a : ℕ) : 0 ≤ fO a := by
  unfold fO; split_ifs
  · rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- For odd `n`, `ψ₂(n) = 2 Σ_{a ≤ n} fE(a) fO(n - a)`. -/
lemma G_odd_eq (n : ℕ) (hn : Odd n) :
    G n = 2 * ∑ a ∈ range (n + 1), fE a * fO (n - a) := by
  rw [G_eq]
  have hpt : ∀ a ∈ range (n + 1), Λ a * Λ (n - a) = fE a * fO (n - a) + fO a * fE (n - a) := by
    intro a ha
    rw [mem_range] at ha
    rw [← fE_add_fO a, ← fE_add_fO (n - a)]
    unfold fE fO
    rcases Nat.even_or_odd a with he | ho
    · have : ¬ Even (n - a) := by
        rw [Nat.not_even_iff_odd]; rcases hn with ⟨k, hk⟩; rcases he with ⟨l, hl⟩
        exact ⟨k - l, by omega⟩
      simp [he, this]
    · have : Even (n - a) := by
        rcases hn with ⟨k, hk⟩; rcases ho with ⟨l, hl⟩; exact ⟨k - l, by omega⟩
      simp [Nat.not_even_iff_odd.2 ho, this]
  rw [sum_congr rfl hpt, sum_add_distrib]
  have hrefl : ∑ a ∈ range (n + 1), fO a * fE (n - a) = ∑ a ∈ range (n + 1), fE a * fO (n - a) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    rw [show n + 1 - 1 - a = n - a by omega, Nat.sub_sub_self (by omega), mul_comm]
  rw [hrefl]; ring

/-- For even `n` the convolution `Σ fE(a) fO(n - a)` vanishes. -/
lemma H_even_zero (n : ℕ) (hn : Even n) : ∑ a ∈ range (n + 1), fE a * fO (n - a) = 0 := by
  apply sum_eq_zero
  intro a ha
  rw [mem_range] at ha
  unfold fE fO
  rcases Nat.even_or_odd a with he | ho
  · have : Even (n - a) := by
      rcases hn with ⟨k, hk⟩; rcases he with ⟨l, hl⟩; exact ⟨k - l, by omega⟩
    simp [this]
  · simp [Nat.not_even_iff_odd.2 ho]

/-- The odd sum as a convolution. -/
lemma sum_G_odd_eq (N : ℕ) :
    ∑ n ∈ (range (N + 1)).filter Odd, G n =
      2 * ∑ a ∈ range (N + 1), fE a * ∑ b ∈ range (N + 1 - a), fO b := by
  rw [← conv_sum, mul_sum, sum_filter]
  apply sum_congr rfl
  intro n _
  split_ifs with h
  · exact G_odd_eq n h
  · rw [H_even_zero n (Nat.not_odd_iff_even.1 h), mul_zero]

/-- Change of variables: `fE` lives on the powers `2^j`, `1 ≤ j ≤ log₂ N`. -/
lemma sum_fE_mul (N : ℕ) (F : ℕ → ℝ) :
    ∑ a ∈ range (N + 1), fE a * F a = ∑ j ∈ Icc 1 (Nat.log 2 N), Real.log 2 * F (2 ^ j) := by
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) (Icc 1 (Nat.log 2 N) : Set ℕ) :=
    fun x _ y _ h => Nat.pow_right_injective le_rfl h
  have hval : ∀ j ∈ Icc 1 (Nat.log 2 N), fE (2 ^ j) = Real.log 2 := by
    intro j hj
    rw [mem_Icc] at hj
    unfold fE
    rw [if_pos ((Nat.even_pow' (by omega)).2 even_two),
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hsub : (Icc 1 (Nat.log 2 N)).image (fun j : ℕ => 2 ^ j) ⊆ range (N + 1) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
    rw [mem_Icc] at hj
    rw [mem_range]
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj.2
    have h2 := Nat.pow_log_le_self 2 (show N ≠ 0 by
      intro h0; rw [h0] at hj; simp at hj; omega)
    omega
  have hzero : ∀ a ∈ range (N + 1), a ∉ (Icc 1 (Nat.log 2 N)).image (fun j : ℕ => 2 ^ j) →
      fE a * F a = 0 := by
    intro a ha hna
    rw [mem_range] at ha
    unfold fE
    split_ifs with he
    · by_cases hp : IsPrimePow a
      · obtain ⟨j, hj, rfl⟩ := even_primePow he hp
        exfalso; apply hna
        refine mem_image.2 ⟨j, mem_Icc.2 ⟨hj, Nat.le_log_of_pow_le (by norm_num) (by omega)⟩, rfl⟩
      · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hp, zero_mul]
    · rw [zero_mul]
  rw [← sum_subset hsub hzero, sum_image hinj]
  apply sum_congr rfl
  intro j hj
  rw [hval j hj]

/-- `Σ_{b ≤ M} fE(b) = log 2 · ⌊log₂ M⌋`. -/
lemma sum_fE_eq (M : ℕ) : ∑ b ∈ range (M + 1), fE b = Real.log 2 * Nat.log 2 M := by
  have := sum_fE_mul M (fun _ => 1)
  simp only [mul_one] at this
  rw [this, sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  ring

/-- `L e^{-c √L} ≤ 2 / c²` for `L ≥ 0`. -/
lemma mul_exp_neg_sqrt_le {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L) :
    L * Real.exp (-c * Real.sqrt L) ≤ 2 / c ^ 2 := by
  set u := Real.sqrt L with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg L
  have hLu : L = u ^ 2 := by rw [hu, Real.sq_sqrt hL]
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hu0)
  have hE : (c * u) ^ 2 / 2 ≤ Real.exp (c * u) := by nlinarith [mul_nonneg hc.le hu0]
  have hpos : 0 < Real.exp (c * u) := Real.exp_pos _
  have hinv : Real.exp (-c * u) = (Real.exp (c * u))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hLu, hinv, ← div_eq_mul_inv, div_le_div_iff₀ hpos (by positivity)]
  nlinarith [sq_nonneg u, sq_nonneg c]

/-- `log N ≤ 2 √N`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  rw [Real.log_sqrt hx.le] at h1
  linarith

/-- The PNT with error term in the form `|ψ(x) - x| ≤ A x / log x`, `x ≥ 2`. -/
lemma psi_div_log : ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.psi x - x| ≤ A * x / Real.log x := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  refine ⟨|K| * (2 / c ^ 2), by positivity, fun x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : 0 ≤ x := by linarith
  have h1 := hK x hx
  have h2 := mul_exp_neg_sqrt_le hc hl.le
  have he : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 2 / c ^ 2 / Real.log x := by
    rw [le_div_iff₀ hl]; linarith
  calc |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := h1
    _ ≤ |K| * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (le_abs_self K) hx0
    _ ≤ |K| * x * (2 / c ^ 2 / Real.log x) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = |K| * (2 / c ^ 2) * x / Real.log x := by ring

/-- Uniform in `m ≤ N`: `|ψ(m) - m| ≤ C N / log N`. -/
lemma psiN_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ m : ℕ, m ≤ N →
    |psiN m - m| ≤ C * N / Real.log N := by
  obtain ⟨A, hA, hpsi⟩ := psi_div_log
  refine ⟨2 * A + 12, by positivity, fun N hN m hm => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
  rw [psiN_eq]
  by_cases hbig : 2 ≤ m ∧ N ≤ m ^ 2
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hbig.1
    have hlm : 0 < Real.log m := Real.log_pos (by linarith)
    have hsq : (N : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hbig.2
    have hlog2 : Real.log N ≤ 2 * Real.log m := by
      have := Real.log_le_log hNpos hsq
      rw [Real.log_pow] at this; push_cast at this; linarith
    have h1 := hpsi m hm2
    have h2 : A * m / Real.log m ≤ 2 * A * N / Real.log N := by
      rw [div_le_div_iff₀ hlm hlN]
      have : A * m * Real.log N ≤ A * N * (2 * Real.log m) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hmN hA) hlog2 hlN.le (by positivity)
      linarith
    have h3 : 2 * A * N / Real.log N ≤ (2 * A + 12) * N / Real.log N := by
      apply div_le_div_of_nonneg_right _ hlN.le; nlinarith
    linarith
  · have hsmall : (m : ℝ) ≤ Real.sqrt N := by
      rcases not_and_or.1 hbig with h | h
      · have : m ≤ 1 := by omega
        have h1 : (m : ℝ) ≤ 1 := by exact_mod_cast this
        have : (1 : ℝ) ≤ Real.sqrt N := by
          rw [Real.one_le_sqrt]; linarith
        linarith
      · have h' : (m : ℝ) ^ 2 < N := by exact_mod_cast (not_le.1 h)
        rw [Real.le_sqrt (by positivity) hNpos.le]; linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hps := Chebyshev.psi_le_const_mul_self hm0
    have hps0 := Chebyshev.psi_nonneg (m : ℝ)
    have hl4 : Real.log 4 < 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      have := Real.log_two_lt_d9; linarith
    have hab : |Chebyshev.psi m - m| ≤ 6 * m := by
      rw [abs_le]; constructor <;> nlinarith
    have hsN : Real.sqrt N * Real.log N ≤ 2 * N := by
      have := log_le_two_sqrt hNpos
      have hs := Real.mul_self_sqrt hNpos.le
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    have h6 : 6 * (m : ℝ) ≤ 12 * N / Real.log N := by
      rw [le_div_iff₀ hlN]; nlinarith
    have h7 : 12 * (N : ℝ) / Real.log N ≤ (2 * A + 12) * N / Real.log N := by
      apply div_le_div_of_nonneg_right _ hlN.le; nlinarith
    linarith

/-- `Σ_{1 ≤ j ≤ J} 2^j ≤ 2^{J+1}`. -/
lemma sum_pow_two_le (J : ℕ) : ∑ j ∈ Icc 1 J, (2 : ℝ) ^ j ≤ 2 ^ (J + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_Icc_succ_top (by omega), pow_succ (2 : ℝ) (J + 1)]
    linarith

/-- **P0051 Goldston-Suriajaya, Theorem 7, first line, PROVED unconditional**:
`Σ_{n ≤ N, n odd} ψ₂(n) = 2 N log N + O(N)`. Same statement as the cited `gs_theorem7_odd`. -/
theorem gs_theorem7_odd_proved : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    |∑ n ∈ (range (N + 1)).filter Odd, G n - 2 * N * Real.log N| ≤ K * N := by
  obtain ⟨C, hC0, hC⟩ := psiN_uniform
  refine ⟨2 * C + 14, fun N hN => ?_⟩
  set J := Nat.log 2 N with hJ
  have hN0 : N ≠ 0 := by omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hT : ∀ M : ℕ, ∑ b ∈ range (M + 1), fO b = psiN M - Real.log 2 * Nat.log 2 M := by
    intro M
    have : psiN M = ∑ b ∈ range (M + 1), fE b + ∑ b ∈ range (M + 1), fO b := by
      unfold psiN; rw [← sum_add_distrib]; exact sum_congr rfl (fun b _ => (fE_add_fO b).symm)
    rw [← sum_fE_eq]; linarith
  have hS : ∑ n ∈ (range (N + 1)).filter Odd, G n = 2 * ∑ j ∈ Icc 1 J,
      Real.log 2 * (psiN (N - 2 ^ j) - Real.log 2 * Nat.log 2 (N - 2 ^ j)) := by
    rw [sum_G_odd_eq]
    congr 1
    rw [show (∑ a ∈ range (N + 1), fE a * ∑ b ∈ range (N + 1 - a), fO b) =
        ∑ a ∈ range (N + 1), fE a * (psiN (N - a) - Real.log 2 * Nat.log 2 (N - a)) from
      sum_congr rfl (fun a ha => by
        rw [mem_range] at ha; rw [show N + 1 - a = (N - a) + 1 by omega, hT])]
    exact sum_fE_mul N (fun a => psiN (N - a) - Real.log 2 * Nat.log 2 (N - a))
  have hpowJ : 2 ^ J ≤ N := Nat.pow_log_le_self 2 hN0
  have hpowj : ∀ j ∈ Icc 1 J, 2 ^ j ≤ N := fun j hj =>
    (Nat.pow_le_pow_right (by norm_num) (mem_Icc.1 hj).2).trans hpowJ
  have hcast : ∀ j ∈ Icc 1 J, ((N - 2 ^ j : ℕ) : ℝ) = N - 2 ^ j := by
    intro j hj; rw [Nat.cast_sub (hpowj j hj)]; push_cast; ring
  have hJlog : (J : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpowJ)
  have hJlog' : Real.log N < ((J : ℝ) + 1) * Real.log 2 := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) N
    have h' : (N : ℝ) < 2 ^ (J + 1) := by exact_mod_cast h
    have := Real.log_lt_log hNpos h'
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hcard : ((Icc 1 J).card : ℝ) = J := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  set X1 := 2 * ∑ j ∈ Icc 1 J, Real.log 2 * (psiN (N - 2 ^ j) - ((N - 2 ^ j : ℕ) : ℝ)) with hX1
  set X2 := 2 * ∑ j ∈ Icc 1 J, Real.log 2 * ((N - 2 ^ j : ℕ) : ℝ) - 2 * N * Real.log N with hX2
  set X3 := 2 * ∑ j ∈ Icc 1 J, Real.log 2 * (Real.log 2 * Nat.log 2 (N - 2 ^ j)) with hX3
  have hdec : ∑ n ∈ (range (N + 1)).filter Odd, G n - 2 * N * Real.log N = X1 + X2 - X3 := by
    rw [hS, hX1, hX2, hX3]
    have : ∑ j ∈ Icc 1 J, Real.log 2 * (psiN (N - 2 ^ j) - Real.log 2 * Nat.log 2 (N - 2 ^ j)) =
        ∑ j ∈ Icc 1 J, Real.log 2 * (psiN (N - 2 ^ j) - ((N - 2 ^ j : ℕ) : ℝ)) +
        ∑ j ∈ Icc 1 J, Real.log 2 * ((N - 2 ^ j : ℕ) : ℝ) -
        ∑ j ∈ Icc 1 J, Real.log 2 * (Real.log 2 * Nat.log 2 (N - 2 ^ j)) := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl; intro j _; ring
    rw [this]; ring
  -- X1, the PNT error
  have hB1 : |X1| ≤ 2 * C * N := by
    have h1 : |∑ j ∈ Icc 1 J, Real.log 2 * (psiN (N - 2 ^ j) - ((N - 2 ^ j : ℕ) : ℝ))| ≤
        ∑ j ∈ Icc 1 J, Real.log 2 * (C * N / Real.log N) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_pos hl2]
      exact mul_le_mul_of_nonneg_left (hC N hN (N - 2 ^ j) (Nat.sub_le _ _)) hl2.le
    rw [sum_const, nsmul_eq_mul, hcard] at h1
    have h2 : (J : ℝ) * (Real.log 2 * (C * N / Real.log N)) ≤ C * N := by
      rw [show (J : ℝ) * (Real.log 2 * (C * N / Real.log N)) =
        (J * Real.log 2) * (C * N) / Real.log N by ring, div_le_iff₀ hlN]
      have : 0 ≤ C * N := by positivity
      nlinarith
    rw [hX1, abs_mul, abs_two]; linarith
  -- X2, the main term
  have hsum2 : ∑ j ∈ Icc 1 J, Real.log 2 * ((N - 2 ^ j : ℕ) : ℝ) =
      Real.log 2 * (J * N - ∑ j ∈ Icc 1 J, (2 : ℝ) ^ j) := by
    rw [sum_congr rfl (fun j hj => by rw [hcast j hj]), ← mul_sum, sum_sub_distrib, sum_const,
      nsmul_eq_mul, hcard]
  have hg0 : 0 ≤ ∑ j ∈ Icc 1 J, (2 : ℝ) ^ j := sum_nonneg fun _ _ => by positivity
  have hg1 : ∑ j ∈ Icc 1 J, (2 : ℝ) ^ j ≤ 2 * N := by
    have := sum_pow_two_le J
    have h' : (2 : ℝ) ^ J ≤ N := by exact_mod_cast hpowJ
    rw [pow_succ] at this; linarith
  have hB2 : |X2| ≤ 6 * N := by
    rw [hX2, hsum2, abs_le]; constructor <;> nlinarith
  -- X3, the even powers of two
  have hB3a : 0 ≤ X3 := by
    rw [hX3]; apply mul_nonneg (by norm_num); apply sum_nonneg; intro j _; positivity
  have hB3b : X3 ≤ 8 * N := by
    have h1 : ∑ j ∈ Icc 1 J, Real.log 2 * (Real.log 2 * Nat.log 2 (N - 2 ^ j)) ≤
        ∑ j ∈ Icc 1 J, Real.log 2 * (Real.log 2 * J) := by
      apply sum_le_sum; intro j _
      have : (Nat.log 2 (N - 2 ^ j) : ℝ) ≤ J := by exact_mod_cast Nat.log_mono_right (Nat.sub_le _ _)
      have := mul_le_mul_of_nonneg_left this hl2.le
      exact mul_le_mul_of_nonneg_left this hl2.le
    rw [sum_const, nsmul_eq_mul, hcard] at h1
    have h2 := log_le_two_sqrt hNpos
    have hs := Real.mul_self_sqrt hNpos.le
    have h3 : Real.log N ^ 2 ≤ 4 * N := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
    have h4 : ((J : ℝ) * Real.log 2) ^ 2 ≤ Real.log N ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hJlog
    rw [hX3]; nlinarith
  rw [hdec]
  calc |X1 + X2 - X3| ≤ |X1| + |X2| + |X3| := by
        have := abs_sub (X1 + X2) X3; have := abs_add_le X1 X2; linarith
    _ ≤ 2 * C * N + 6 * N + 8 * N := by rw [abs_of_nonneg hB3a]; linarith
    _ = (2 * C + 14) * N := by ring

end LeanLab.GoldbachAverage
