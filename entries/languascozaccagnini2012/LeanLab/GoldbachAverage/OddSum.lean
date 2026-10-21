module

public import LeanLab.GoldbachAverage.Sums

/-!
Upper half of P0051 Goldston-Suriajaya Theorem 7, elementary:
`Σ_{n ≤ N, n odd} ψ₂(n) ≤ 2 (log 4 + 4) N log N`. For odd `n` one of `m, n - m` is even, and
an even `m` with `Λ(m) ≠ 0` is a power of 2, of which there are at most `log₂ N` up to `N`.
The paper's exact main term `2 N log N + O(N)` needs the prime number theorem; not done here.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0095.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- An even prime power is a power of 2. -/
lemma even_primePow {a : ℕ} (ha : Even a) (hp : IsPrimePow a) : ∃ j, 1 ≤ j ∧ a = 2 ^ j := by
  obtain ⟨p, k, hpp, hk, rfl⟩ := hp
  have hpp' : p.Prime := hpp.nat_prime
  have h2 : 2 ∣ p ^ k := even_iff_two_dvd.1 ha
  have : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp').1 (Nat.prime_two.dvd_of_dvd_pow h2)
  exact ⟨k, hk, by rw [← this]⟩

/-- `Σ_{a ≤ N, a even} Λ(a) ≤ log N`. -/
lemma sum_even_vonMangoldt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ (range (N + 1)).filter Even, Λ a ≤ Real.log N := by
  set S := ((range (N + 1)).filter Even).filter (fun a => IsPrimePow a)
  have hsplit : ∑ a ∈ (range (N + 1)).filter Even, Λ a = ∑ a ∈ S, Λ a :=
    (sum_filter_of_ne (fun a _ h => ArithmeticFunction.vonMangoldt_ne_zero_iff.1 h)).symm
  have hval : ∀ a ∈ S, Λ a = Real.log 2 := by
    intro a ha
    simp only [S, mem_filter] at ha
    obtain ⟨j, hj, rfl⟩ := even_primePow ha.1.2 ha.2
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
  have hsub : S ⊆ (Icc 1 (Nat.log 2 N)).image (2 ^ ·) := by
    intro a ha
    simp only [S, mem_filter, mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := even_primePow ha.1.2 ha.2
    refine mem_image.2 ⟨j, mem_Icc.2 ⟨hj, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hcard : #S ≤ Nat.log 2 N :=
    (card_le_card hsub).trans (card_image_le.trans (by simp))
  rw [hsplit, sum_congr rfl hval, sum_const, nsmul_eq_mul]
  have hpow : ((2 : ℕ) : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hl : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc (#S : ℝ) * Real.log 2 ≤ (Nat.log 2 N : ℝ) * Real.log 2 := by gcongr
    _ ≤ Real.log N := hl

/-- For odd `n`, `ψ₂(n) ≤ 2 Σ_{a ≤ n, a even} Λ(a) Λ(n - a)`. -/
lemma G_odd_le (n : ℕ) (hn : Odd n) :
    G n ≤ 2 * ∑ a ∈ (range (n + 1)).filter Even, Λ a * Λ (n - a) := by
  rw [G_eq]
  have hsym : ∑ a ∈ (range (n + 1)).filter (fun a => Even (n - a)), Λ a * Λ (n - a) =
      ∑ a ∈ (range (n + 1)).filter Even, Λ a * Λ (n - a) := by
    apply sum_nbij' (fun a => n - a) (fun a => n - a)
    · intro a ha; simp only [mem_filter, mem_range] at ha ⊢; exact ⟨by omega, ha.2⟩
    · intro a ha; simp only [mem_filter, mem_range] at ha ⊢
      refine ⟨by omega, ?_⟩; rw [Nat.sub_sub_self (by omega)]; exact ha.2
    · intro a ha; simp only [mem_filter, mem_range] at ha; omega
    · intro a ha; simp only [mem_filter, mem_range] at ha; omega
    · intro a ha; simp only [mem_filter, mem_range] at ha
      rw [Nat.sub_sub_self (by omega), mul_comm]
  have hle : ∑ a ∈ range (n + 1), Λ a * Λ (n - a) ≤
      ∑ a ∈ (range (n + 1)).filter Even, Λ a * Λ (n - a) +
      ∑ a ∈ (range (n + 1)).filter (fun a => Even (n - a)), Λ a * Λ (n - a) := by
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro a ha
    rw [mem_range] at ha
    have h0 : 0 ≤ Λ a * Λ (n - a) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    rcases Nat.even_or_odd a with he | ho
    · rw [if_pos he]; split_ifs <;> linarith
    · have : Even (n - a) := by
        rcases hn with ⟨k, hk⟩; rcases ho with ⟨l, hl⟩; exact ⟨k - l, by omega⟩
      rw [if_neg (Nat.not_even_iff_odd.2 ho), if_pos this]; linarith
  rw [hsym] at hle; linarith

/-- `Λ` on even arguments, `0` on odd ones. -/
def fE (a : ℕ) : ℝ := if Even a then Λ a else 0

lemma fE_nonneg (a : ℕ) : 0 ≤ fE a := by
  unfold fE; split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · rfl

/-- Convolution sums: `Σ_{n ≤ N} Σ_{a ≤ n} f(a) g(n - a) = Σ_{a ≤ N} f(a) Σ_{b ≤ N - a} g(b)`. -/
lemma conv_sum (f g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), ∑ a ∈ range (n + 1), f a * g (n - a) =
      ∑ a ∈ range (N + 1), f a * ∑ b ∈ range (N + 1 - a), g b := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : ∀ a ∈ range (N + 1), f a * ∑ b ∈ range (N + 1 + 1 - a), g b
        = f a * ∑ b ∈ range (N + 1 - a), g b + f a * g (N + 1 - a) := by
      intro a ha
      rw [mem_range] at ha
      have : N + 1 + 1 - a = (N + 1 - a) + 1 := by omega
      rw [this, sum_range_succ, mul_add]
    rw [sum_range_succ, ih, sum_range_succ (fun a => f a * ∑ b ∈ range (N + 1 + 1 - a), g b) (N + 1),
      sum_range_succ (fun a => f a * g (N + 1 - a)) (N + 1), sum_congr rfl hstep, sum_add_distrib]
    rw [show N + 1 + 1 - (N + 1) = 1 by omega, range_one, sum_singleton, Nat.sub_self]
    ring

/-- **Upper half of GS Theorem 7**: `Σ_{n ≤ N, n odd} ψ₂(n) ≤ 2 (log 4 + 4) N log N`. -/
theorem sum_G_odd_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ (range (N + 1)).filter Odd, G n ≤ 2 * (Real.log 4 + 4) * N * Real.log N := by
  have hΛ : ∀ m, 0 ≤ Λ m := fun _ => ArithmeticFunction.vonMangoldt_nonneg
  have hodd : ∀ n, Odd n → G n ≤ 2 * ∑ a ∈ range (n + 1), fE a * Λ (n - a) := by
    intro n hn
    have := G_odd_le n hn
    rw [sum_filter] at this
    convert this using 3 with a
    unfold fE; split_ifs <;> simp
  have hin : ∀ n, 0 ≤ ∑ a ∈ range (n + 1), fE a * Λ (n - a) :=
    fun n => sum_nonneg fun a _ => mul_nonneg (fE_nonneg a) (hΛ _)
  have step1 : ∑ n ∈ (range (N + 1)).filter Odd, G n ≤
      ∑ n ∈ range (N + 1), 2 * ∑ a ∈ range (n + 1), fE a * Λ (n - a) := by
    calc _ ≤ ∑ n ∈ (range (N + 1)).filter Odd, 2 * ∑ a ∈ range (n + 1), fE a * Λ (n - a) :=
          sum_le_sum fun n hn => hodd n (mem_filter.1 hn).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun n _ _ => mul_nonneg (by norm_num) (hin n))
  rw [← mul_sum, conv_sum] at step1
  have hpsi0 : 0 ≤ psiN N := sum_nonneg fun _ _ => hΛ _
  have step2 : ∑ a ∈ range (N + 1), fE a * ∑ b ∈ range (N + 1 - a), Λ b ≤
      (∑ a ∈ range (N + 1), fE a) * psiN N := by
    rw [sum_mul]; apply sum_le_sum; intro a _
    apply mul_le_mul_of_nonneg_left _ (fE_nonneg a)
    exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun b _ _ => hΛ b)
  have hfE : ∑ a ∈ range (N + 1), fE a ≤ Real.log N := by
    have := sum_even_vonMangoldt_le N hN
    rw [sum_filter] at this
    exact this
  have hpsi : psiN N ≤ (Real.log 4 + 4) * N := by
    rw [psiN_eq]; exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h3 : (∑ a ∈ range (N + 1), fE a) * psiN N ≤ Real.log N * psiN N :=
    mul_le_mul_of_nonneg_right hfE hpsi0
  have h4 : Real.log N * psiN N ≤ Real.log N * ((Real.log 4 + 4) * N) :=
    mul_le_mul_of_nonneg_left hpsi hlog
  nlinarith

end LeanLab.GoldbachAverage
