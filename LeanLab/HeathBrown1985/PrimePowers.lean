module

public import Mathlib
public import LeanLab.HeathBrown1985.Section3

/-!
P0096 Heath-Brown 1985, pages 56 to 58, the prime power error in Theorem 1: replacing
`N₂(m) = Σ_{p + p' = m} (log p)(log p')` by `Σ_{n ≤ x} Λ(n) Λ(m - n)` costs only the terms
where `n` or `m - n` is a prime power `p^e` with `e ≥ 2`.
PROVED here: there are at most `(√N + 1)(log₂ N + 1)` such prime powers up to `N`, and
`Σ_{2x < m ≤ 3x} |Σ_{n ≤ x} Λ(n) Λ(m - n) - N₂(m)| ≤ 1296 x^{3/2} L³` for `x ≥ 2`.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- Prime powers `k ≤ N` that are not primes, `k = p^e`, `e ≥ 2`. -/
def ppNP (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun k => IsPrimePow k ∧ ¬ k.Prime)

theorem card_ppNP_le (N : ℕ) : #(ppNP N) ≤ (N.sqrt + 1) * (Nat.log 2 N + 1) := by
  rw [← card_range (N.sqrt + 1), ← card_range (Nat.log 2 N + 1), ← card_product]
  apply card_le_card_of_injOn (fun k => (k.minFac, k.factorization k.minFac))
  · intro k hk
    simp only [ppNP, coe_filter, mem_Icc, Set.mem_ofPred_eq] at hk
    obtain ⟨⟨hk1, hkN⟩, hpp, hnp⟩ := hk
    have hk0 : k ≠ 0 := by omega
    have hp := Nat.minFac_prime hpp.ne_one
    have heq := hpp.minFac_pow_factorization_eq
    set p := k.minFac
    set e := k.factorization p
    have he1 : 1 ≤ e := (hp.dvd_iff_one_le_factorization hk0).mp (Nat.minFac_dvd k)
    have he2 : 2 ≤ e := by
      by_contra h
      have : e = 1 := by omega
      rw [this, pow_one] at heq
      exact hnp (heq ▸ hp)
    have hp2 := hp.two_le
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
    constructor
    · have : p ^ 2 ≤ N := by
        calc p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right (by omega) he2
          _ = k := heq
          _ ≤ N := hkN
      have := Nat.le_sqrt'.mpr this
      omega
    · have : 2 ^ e ≤ N := by
        calc 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp2 e
          _ = k := heq
          _ ≤ N := hkN
      exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) this)
  · intro a ha b hb hab
    simp only [ppNP, coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only [Prod.mk.injEq] at hab
    rw [← ha.2.1.minFac_pow_factorization_eq, ← hb.2.1.minFac_pow_factorization_eq, hab.2, hab.1]

theorem card_ppNP_real (y : ℝ) (hy : 2 ≤ y) :
    (#(ppNP ⌊y⌋₊) : ℝ) ≤ (Real.sqrt y + 1) * (2 * Real.log y + 1) := by
  set N := ⌊y⌋₊
  have hy0 : 0 ≤ y := by linarith
  have hN : (N : ℝ) ≤ y := Nat.floor_le hy0
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have h := card_ppNP_le N
  have hR : (#(ppNP N) : ℝ) ≤ ((N.sqrt : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 1) := by
    exact_mod_cast h
  refine hR.trans ?_
  have hs : (N.sqrt : ℝ) ≤ Real.sqrt y :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt hN)
  have hl : (Nat.log 2 N : ℝ) ≤ 2 * Real.log y := by
    have h1 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have h2 : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have h4 : Real.log N ≤ Real.log y := Real.log_le_log (by exact_mod_cast hN1) hN
    have h5 := Real.log_two_gt_d9
    have h6 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
    nlinarith
  apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

theorem vonMangoldt_le_log_of_le (k : ℕ) (y : ℝ) (hy : 1 ≤ y) (hk : (k : ℝ) ≤ y) :
    Λ k ≤ Real.log y := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp only [ArithmeticFunction.map_zero]; exact Real.log_nonneg hy
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast h) hk)

/-- `N₂(m)` is the sum of `Λ(n) Λ(m - n)` over `n ≤ x` with `n` and `m - n` both prime. -/
theorem N2_eq (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    N2 x m = ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n.Prime ∧ (m - n).Prime), Λ n * Λ (m - n) := by
  unfold N2
  apply sum_congr
  · ext p
    simp only [mem_filter, mem_range, mem_Icc, Nat.le_floor_iff hx]
    constructor
    · rintro ⟨_, hp, hq, hpx⟩
      exact ⟨⟨hp.one_lt.le, hpx⟩, hp, hq⟩
    · rintro ⟨⟨_, hpx⟩, hp, hq⟩
      have := hq.two_le
      exact ⟨by omega, hp, hq, hpx⟩
  · intro p hp
    simp only [mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2.1,
      ArithmeticFunction.vonMangoldt_apply_prime hp.2.2]

theorem ppErr_le (x : ℝ) (hx : 2 ≤ x) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n) - N2 x m| ≤
      2 * Real.log (3 * x) ^ 2 * (#(ppNP ⌊3 * x⌋₊) : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨_, hm3⟩, _⟩ := hm
  set S := ppNP ⌊3 * x⌋₊
  set l3 := Real.log (3 * x)
  have hl3 : 0 ≤ l3 := Real.log_nonneg (by linarith)
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  rw [N2_eq x hx0, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊)
    (fun n => n.Prime ∧ (m - n).Prime), add_sub_cancel_left]
  have hterm : ∀ n ∈ Icc 1 ⌊x⌋₊, 0 ≤ Λ n * Λ (m - n) :=
    fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_of_nonneg (sum_nonneg (fun n hn => hterm n (mem_filter.mp hn).1))]
  set f : ℕ → ℝ := fun n => l3 ^ 2 * ((if n ∈ S then 1 else 0) + (if m - n ∈ S then 1 else 0))
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [f]; apply mul_nonneg (by positivity); split_ifs <;> norm_num
  have hpt : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ (n.Prime ∧ (m - n).Prime)),
      Λ n * Λ (m - n) ≤ f n := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, hnp⟩ := hn
    by_cases h0 : Λ n * Λ (m - n) = 0
    · rw [h0]; exact hf0 n
    have ha := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h0)
    have hb := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (right_ne_zero_of_mul h0)
    have hnR : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) (Nat.floor_le hx0)
    have h1 : Λ n ≤ l3 := vonMangoldt_le_log_of_le n _ (by linarith) (by linarith)
    have h2 : Λ (m - n) ≤ l3 := vonMangoldt_le_log_of_le _ _ (by linarith)
      (le_trans (by exact_mod_cast Nat.sub_le m n) hmR)
    have hprod : Λ n * Λ (m - n) ≤ l3 ^ 2 := by
      rw [sq]
      exact mul_le_mul h1 h2 ArithmeticFunction.vonMangoldt_nonneg hl3
    have hind : 1 ≤ ((if n ∈ S then (1 : ℝ) else 0) + (if m - n ∈ S then 1 else 0)) := by
      have hb0 : m - n ≠ 0 := fun h => by rw [h] at hb; exact not_isPrimePow_zero hb
      by_cases hpn : n.Prime
      · have hq : ¬ (m - n).Prime := fun hq => hnp ⟨hpn, hq⟩
        have : m - n ∈ S := by
          simp only [S, ppNP, mem_filter, mem_Icc]
          exact ⟨⟨by omega, (Nat.sub_le m n).trans hm3⟩, hb, hq⟩
        rw [if_pos this]; split_ifs <;> norm_num
      · have : n ∈ S := by
          simp only [S, ppNP, mem_filter, mem_Icc]
          refine ⟨⟨hn1, hnx.trans (Nat.floor_le_floor (by linarith))⟩, ha, hpn⟩
        rw [if_pos this]; split_ifs <;> norm_num
    calc Λ n * Λ (m - n) ≤ l3 ^ 2 := hprod
      _ = l3 ^ 2 * 1 := (mul_one _).symm
      _ ≤ f n := mul_le_mul_of_nonneg_left hind (by positivity)
  refine (sum_le_sum hpt).trans ?_
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => hf0 n)).trans ?_
  simp only [f]
  rw [← mul_sum, sum_add_distrib, sum_boole, sum_boole]
  have c1 : #((Icc 1 ⌊x⌋₊).filter (fun n => n ∈ S)) ≤ #S :=
    card_le_card_of_injOn id (fun n hn => (mem_filter.mp hn).2) (fun _ _ _ _ h => h)
  have c2 : #((Icc 1 ⌊x⌋₊).filter (fun n => m - n ∈ S)) ≤ #S := by
    apply card_le_card_of_injOn (fun n => m - n) (fun n hn => (mem_filter.mp hn).2)
    intro a ha b hb hab
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
    have ha' : m - a ≠ 0 := by
      intro h; have := ha.2; rw [h] at this
      simp [S, ppNP] at this
    have hb' : m - b ≠ 0 := by
      intro h; have := hb.2; rw [h] at this
      simp [S, ppNP] at this
    have hab' : m - a = m - b := hab
    omega
  have c1R : (#((Icc 1 ⌊x⌋₊).filter (fun n => n ∈ S)) : ℝ) ≤ #S := by exact_mod_cast c1
  have c2R : (#((Icc 1 ⌊x⌋₊).filter (fun n => m - n ∈ S)) : ℝ) ≤ #S := by exact_mod_cast c2
  have : l3 ^ 2 * ((#((Icc 1 ⌊x⌋₊).filter (fun n => n ∈ S)) : ℝ) +
      #((Icc 1 ⌊x⌋₊).filter (fun n => m - n ∈ S))) ≤ l3 ^ 2 * (2 * #S) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

theorem card_mRange_le (x : ℝ) (hx : 0 ≤ x) : (#(mRange x) : ℝ) ≤ 3 * x := by
  have h : #(mRange x) ≤ ⌊3 * x⌋₊ := by
    unfold mRange; refine (card_filter_le _ _).trans ?_; simp
  exact le_trans (by exact_mod_cast h) (Nat.floor_le (by linarith))

/-- **The prime power error**: `Σ_{2x < m ≤ 3x} |Σ_{n ≤ x} Λ(n) Λ(m - n) - N₂(m)| ≤
1296 x √x L³` for `x ≥ 2`. -/
theorem sum_ppErr_le (x : ℝ) (hx : 2 ≤ x) :
    ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n) - N2 x m| ≤
      1296 * x * Real.sqrt x * Real.log x ^ 3 := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL : 1 / 2 ≤ L := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
    linarith
  have hl3 : Real.log (3 * x) ≤ 3 * L := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have h1 : Real.log 3 ≤ Real.log (x ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hl30 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt (3 * x) ≤ 2 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc := card_ppNP_real (3 * x) (by linarith)
  have hper : ∀ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n) - N2 x m| ≤
      432 * Real.sqrt x * L ^ 3 := by
    intro m hm
    refine (ppErr_le x hx m hm).trans ?_
    have e1 : Real.log (3 * x) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hl30 hl3 2
    have e2 : (Real.sqrt (3 * x) + 1) * (2 * Real.log (3 * x) + 1) ≤
        (3 * Real.sqrt x) * (8 * L) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    calc 2 * Real.log (3 * x) ^ 2 * (#(ppNP ⌊3 * x⌋₊) : ℝ)
        ≤ 2 * (3 * L) ^ 2 * ((3 * Real.sqrt x) * (8 * L)) := by
          apply mul_le_mul (by linarith) (hc.trans e2) (by positivity) (by positivity)
      _ = 432 * Real.sqrt x * L ^ 3 := by ring
  refine (sum_le_sum hper).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have := card_mRange_le x hx0.le
  calc (#(mRange x) : ℝ) * (432 * Real.sqrt x * L ^ 3) ≤ 3 * x * (432 * Real.sqrt x * L ^ 3) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by ring

end LeanLab.HeathBrown1985
