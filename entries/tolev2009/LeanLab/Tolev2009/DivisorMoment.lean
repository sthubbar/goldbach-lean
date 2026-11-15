module

public import LeanLab.HeathBrown1985.DivMoments

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.DivisorMoment

open LeanLab.HeathBrown1985

/-- Expand one divisor factor by its positive divisor index. -/
theorem divisor_expand (N : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, w n * (n.divisors.card : ℝ) =
      ∑ a ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (a ∣ ·), w n := by
  have he : ∀ n ∈ Icc 1 N, w n * (n.divisors.card : ℝ) =
      ∑ a ∈ Icc 1 N, if a ∣ n then w n else 0 := by
    intro n hn
    rw [← sum_filter, ← divisors_eq_filter N n hn, sum_const, nsmul_eq_mul]
    ring
  rw [sum_congr rfl he, sum_comm]
  exact sum_congr rfl fun a _ => (sum_filter _ _).symm

/-- Multiples can be reindexed by their positive quotient. -/
theorem sum_multiples_le (N a : ℕ) (ha : 1 ≤ a) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ (Icc 1 N).filter (a ∣ ·), f n ≤
      ∑ b ∈ Icc 1 (N / a), f (a * b) := by
  have hsub : (Icc 1 N).filter (a ∣ ·) ⊆ (Icc 1 (N / a)).image (a * ·) := by
    intro k hk
    rcases mem_filter.mp hk with ⟨hk, b, rfl⟩
    rcases mem_Icc.mp hk with ⟨hk1, hkN⟩
    refine mem_image.mpr ⟨b, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hk1
      · exact h
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hf _)).trans_eq ?_
  rw [sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem Hn_mono {M N : ℕ} (h : M ≤ N) : Hn M ≤ Hn N := by
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro k hk
  exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans h⟩

/-- A reciprocal divisor moment gives the next reciprocal moment by squaring. -/
theorem reciprocal_step (N r e : ℕ)
    (h : ∀ M ≤ N, ∑ n ∈ Icc 1 M, (n.divisors.card : ℝ) ^ r / n ≤ Hn M ^ e) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ (r + 1) / n ≤ Hn N ^ (2 * e) := by
  have hHN := Hn_nonneg N
  have he : (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ (r + 1) / n) =
      ∑ a ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (a ∣ ·), (n.divisors.card : ℝ) ^ r / n := by
    rw [← divisor_expand]
    refine sum_congr rfl fun n _ => ?_
    rw [pow_succ]
    ring
  rw [he]
  calc
    _ ≤ ∑ a ∈ Icc 1 N, ((a.divisors.card : ℝ) ^ r / a) * Hn N ^ e := by
      refine sum_le_sum fun a ha => ?_
      have ha1 := (mem_Icc.mp ha).1
      refine (sum_multiples_le N a ha1 _ (fun _ => by positivity)).trans ?_
      calc
        _ ≤ ∑ b ∈ Icc 1 (N / a), ((a.divisors.card : ℝ) ^ r / a) *
            ((b.divisors.card : ℝ) ^ r / b) := by
          refine sum_le_sum fun b hb => ?_
          have hd : ((a * b).divisors.card : ℝ) ≤ (a.divisors.card : ℝ) * b.divisors.card :=
            by exact_mod_cast card_divisors_mul_le a b
          have hp := pow_le_pow_left₀ (by positivity) hd r
          calc
            _ ≤ ((a.divisors.card : ℝ) * b.divisors.card) ^ r / (a * b : ℕ) :=
              div_le_div_of_nonneg_right hp (by positivity)
            _ = _ := by push_cast; rw [mul_pow]; ring
        _ = ((a.divisors.card : ℝ) ^ r / a) *
            ∑ b ∈ Icc 1 (N / a), (b.divisors.card : ℝ) ^ r / b := by rw [mul_sum]
        _ ≤ ((a.divisors.card : ℝ) ^ r / a) * Hn (N / a) ^ e :=
          mul_le_mul_of_nonneg_left (h _ (Nat.div_le_self _ _)) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Hn_nonneg _) (Hn_mono (Nat.div_le_self _ _)) e) (by positivity)
    _ = (∑ a ∈ Icc 1 N, (a.divisors.card : ℝ) ^ r / a) * Hn N ^ e := by rw [sum_mul]
    _ ≤ Hn N ^ e * Hn N ^ e := mul_le_mul_of_nonneg_right (h N le_rfl) (by positivity)
    _ = Hn N ^ (2 * e) := by rw [two_mul, pow_add]

/-- The ordinary next moment uses the preceding ordinary and reciprocal moments. -/
theorem moment_step (N r e d : ℕ)
    (hm : ∀ M ≤ N, ∑ n ∈ Icc 1 M, (n.divisors.card : ℝ) ^ r ≤ M * Hn M ^ e)
    (hr : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤ Hn N ^ d) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ (r + 1) ≤ N * Hn N ^ (e + d) := by
  have hHN := Hn_nonneg N
  have he : (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ (r + 1)) =
      ∑ a ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (a ∣ ·), (n.divisors.card : ℝ) ^ r := by
    rw [← divisor_expand]
    refine sum_congr rfl fun n _ => ?_
    rw [pow_succ]
  rw [he]
  calc
    _ ≤ ∑ a ∈ Icc 1 N, (a.divisors.card : ℝ) ^ r * ((N : ℝ) / a * Hn N ^ e) := by
      refine sum_le_sum fun a ha => ?_
      refine (sum_multiples_le N a (mem_Icc.mp ha).1 _ (fun _ => by positivity)).trans ?_
      calc
        _ ≤ ∑ b ∈ Icc 1 (N / a), (a.divisors.card : ℝ) ^ r * (b.divisors.card : ℝ) ^ r := by
          refine sum_le_sum fun b _ => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast card_divisors_mul_le a b) r
        _ = (a.divisors.card : ℝ) ^ r * ∑ b ∈ Icc 1 (N / a), (b.divisors.card : ℝ) ^ r := by rw [mul_sum]
        _ ≤ (a.divisors.card : ℝ) ^ r * ((N / a : ℕ) * Hn (N / a) ^ e) :=
          mul_le_mul_of_nonneg_left (hm _ (Nat.div_le_self _ _)) (by positivity)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul Nat.cast_div_le
            (pow_le_pow_left₀ (Hn_nonneg _) (Hn_mono (Nat.div_le_self _ _)) e)
            (by have := Hn_nonneg (N / a); positivity) (by positivity)
    _ = N * Hn N ^ e * ∑ a ∈ Icc 1 N, (a.divisors.card : ℝ) ^ r / a := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ N * Hn N ^ e * Hn N ^ d := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem reciprocal_cube (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 3 / n ≤ Hn N ^ 8 :=
  reciprocal_step N 2 4 (fun M _ => sum_sq_divisors_div_le M)

/-- The fourth divisor moment required by Tolev 2009 page 7. -/
theorem fourth_moment (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 4 ≤ N * Hn N ^ 15 := by
  apply moment_step N 3 7 8 _ (reciprocal_cube N)
  intro M _
  simpa only [show (7 : ℕ) = 3 + 4 by norm_num, pow_add, mul_assoc] using sum_cube_divisors_le M

/-- The positive fourth moment with the paper's logarithmic exponent 15. -/
theorem fourth_moment_log (N : ℕ) (hL : 1 ≤ Real.log N) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 4 ≤
      (2 ^ 15 : ℝ) * N * Real.log N ^ (15 : ℕ) := by
  have hHle : Hn N ≤ 2 * Real.log N := (Hn_le N).trans (by linarith)
  calc
    _ ≤ (N : ℝ) * Hn N ^ 15 := fourth_moment N
    _ ≤ (N : ℝ) * (2 * Real.log N) ^ 15 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Hn_nonneg _) hHle 15) (by positivity)
    _ = _ := by ring

/-- A signed nonzero sum is twice the corresponding positive sum. -/
theorem signed_sum (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ (Icc (-(N : ℤ)) N).filter (fun n => n ≠ 0), f n.natAbs =
      2 * ∑ n ∈ Icc 1 N, f n := by
  let s := Icc 1 N
  have he : (Icc (-(N : ℤ)) N).filter (fun n => n ≠ 0) =
      s.image (fun n : ℕ => (n : ℤ)) ∪ s.image (fun n : ℕ => -(n : ℤ)) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_union, mem_image, s]
    constructor
    · intro hn
      by_cases hp : 0 ≤ n
      · left
        refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hp⟩
        omega
      · right
        refine ⟨(-n).toNat, ?_, ?_⟩
        · omega
        · have h : 0 ≤ -n := by omega
          rw [Int.toNat_of_nonneg h]
          omega
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) <;> omega
  have hd : Disjoint (s.image (fun n : ℕ => (n : ℤ))) (s.image (fun n : ℕ => -(n : ℤ))) := by
    rw [disjoint_left]
    intro n hn hn'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    obtain ⟨j, hj, he⟩ := mem_image.mp hn'
    simp only [s, mem_Icc] at hk hj
    omega
  rw [he, sum_union hd, sum_image (fun x _ y _ h => by omega),
    sum_image (fun x _ y _ h => by omega)]
  simp only [Int.natAbs_natCast, Int.natAbs_neg]
  ring

/-- The signed fourth moment has the logarithmic exponent required in display 20. -/
theorem signed_fourth_moment (N : ℕ) (hL : 1 ≤ Real.log N) :
    ∑ n ∈ (Icc (-(N : ℤ)) N).filter (fun n => n ≠ 0), (n.natAbs.divisors.card : ℝ) ^ 4 ≤
      (2 ^ 16 : ℝ) * N * Real.log N ^ (16 : ℕ) := by
  rw [signed_sum N (fun n => (n.divisors.card : ℝ) ^ 4)]
  have hH := Hn_nonneg N
  have hHle : Hn N ≤ 2 * Real.log N := (Hn_le N).trans (by linarith)
  have hp : Real.log N ^ (15 : ℕ) ≤ Real.log N ^ (16 : ℕ) :=
    pow_le_pow_right₀ hL (by norm_num)
  calc
    _ ≤ 2 * ((N : ℝ) * Hn N ^ 15) := mul_le_mul_of_nonneg_left (fourth_moment N) (by norm_num)
    _ ≤ 2 * ((N : ℝ) * (2 * Real.log N) ^ 15) := by gcongr
    _ = (2 ^ 16 : ℝ) * N * Real.log N ^ (15 : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end LeanLab.Tolev2009.DivisorMoment
