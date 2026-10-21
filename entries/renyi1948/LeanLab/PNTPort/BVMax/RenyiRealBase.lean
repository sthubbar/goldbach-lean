module

public import LeanLab.PNTPort.BVMax.RenyiSmallK

/-!
# Rényi's theorem with `K = 28`, blocks on a real scale

Unit U-6052, CLOUD 20261020T0516Z-cloud35. AI wrote the Lean code. Known mathematics, IDEAS I-5051.

`RenyiSmallK.lean` sifts to `z = 2^{2^k}`, and the dyadic choice of `k` costs a factor 2 in the
sifting limit, so `Ω ≤ 59`. Here the block ends are `thr c j = exp(2^j c)` for a real
`c ∈ [log 2, 2 log 2)` chosen so that `thr c k = exp(log N/29)` exactly; `blkE N c j` holds the
primes `p ∤ N` in `(thr c j, thr c (j+1)]`, all primes from 3 for `j = 0`. With the top level 4 the
level is `exp(14 log N/29) ≤ N^{49/100}`, and every survivor `N - p` has all prime factors above
`exp(log N/29)`, so `Ω(N - p) ≤ 28`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN; Chen's `Ω(m) ≤ 2` is far stronger than this route.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- The block ends `exp(2^j c)`. -/
noncomputable def thr (c : ℝ) (j : ℕ) : ℝ := Real.exp (2 ^ j * c)

lemma thr_pos (c : ℝ) (j : ℕ) : 0 < thr c j := Real.exp_pos _

lemma one_le_thr {c : ℝ} (hc : 0 ≤ c) (j : ℕ) : 1 ≤ thr c j := Real.one_le_exp (by positivity)

lemma thr_mono {c : ℝ} (hc : 0 ≤ c) {i j : ℕ} (h : i ≤ j) : thr c i ≤ thr c j := by
  unfold thr; apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) hc

lemma thr_pow (c : ℝ) (j n : ℕ) : thr c j ^ n = Real.exp (2 ^ j * c * n) := by
  unfold thr; rw [← Real.exp_nat_mul]; ring_nf

lemma thr_succ (c : ℝ) (j : ℕ) : thr c (j + 1) = thr c j ^ 2 := by
  rw [thr_pow]; unfold thr; push_cast; ring_nf

/-- The primes `p ∤ N` with `3 ≤ p ≤ thr c (j + 1)` and, for `j ≥ 1`, `thr c j < p`. -/
noncomputable def blkE (N : ℕ) (c : ℝ) (j : ℕ) : Finset ℕ :=
  (Icc 3 ⌊thr c (j + 1)⌋₊).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ (j = 0 ∨ thr c j < p))

/-- Blocks `j, j - 1, …, 0` on the real scale, the level rising by 2 at each step down. -/
noncomputable def GE (N : ℕ) (c : ℝ) : ℕ → ℕ → List Block
  | 0, r => [(blkE N c 0, r, r + 1)]
  | j + 1, r => (blkE N c (j + 1), r, r + 1) :: GE N c j (r + 2)

lemma GE_length (N : ℕ) (c : ℝ) : ∀ j r, (GE N c j r).length = j + 1
  | 0, r => by simp [GE]
  | j + 1, r => by simp [GE, GE_length N c j (r + 2)]

lemma blkE_mem {N : ℕ} {c : ℝ} {j p : ℕ} (hp : p ∈ blkE N c j) :
    (p : ℝ) ≤ thr c (j + 1) ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p ∧ (j = 0 ∨ thr c j < p) := by
  simp only [blkE, mem_filter, mem_Icc] at hp
  obtain ⟨⟨h3, hle⟩, hpp, hN, hj⟩ := hp
  exact ⟨(Nat.le_floor_iff (thr_pos c _).le).mp hle, hpp, hN, h3, hj⟩

lemma GE_mem (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j r, ∀ p ∈ univB (GE N c j r),
    (p : ℝ) ≤ thr c (j + 1) ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p
  | 0, r, p, hp => by
    simp only [GE, univB, union_empty] at hp
    obtain ⟨h1, h2, h3, h4, -⟩ := blkE_mem hp
    exact ⟨h1, h2, h3, h4⟩
  | j + 1, r, p, hp => by
    simp only [GE, univB, mem_union] at hp
    rcases hp with h | h
    · obtain ⟨h1, h2, h3, h4, -⟩ := blkE_mem h
      exact ⟨h1, h2, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := GE_mem N hc j (r + 2) p h
      exact ⟨h1.trans (thr_mono hc (by omega)), h2, h3, h4⟩

lemma GE_good (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j r, Even r → Good (GE N c j r)
  | 0, r, hr => by
    simp only [GE, Good, univB]
    exact ⟨fun p hp => (blkE_mem hp).2.1, disjoint_empty_right _, hr, hr.add_one, trivial⟩
  | j + 1, r, hr => by
    simp only [GE, Good]
    refine ⟨fun p hp => (blkE_mem hp).2.1, ?_, hr, hr.add_one, GE_good N hc j (r + 2) (by
      rcases hr with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩)⟩
    rw [disjoint_left]
    intro p hp hp'
    have h1 := (GE_mem N hc j (r + 2) p hp').1
    rcases (blkE_mem hp).2.2.2.2 with h | h
    · omega
    · linarith

lemma GE_cover (N : ℕ) (c : ℝ) : ∀ j r, ∀ p, p.Prime → ¬ p ∣ N → 3 ≤ p →
    (p : ℝ) ≤ thr c (j + 1) → p ∈ univB (GE N c j r)
  | 0, r, p, hp, hpN, h3, hpz => by
    simp only [GE, univB, union_empty, blkE, mem_filter, mem_Icc]
    exact ⟨⟨h3, Nat.le_floor hpz⟩, hp, hpN, Or.inl trivial⟩
  | j + 1, r, p, hp, hpN, h3, hpz => by
    simp only [GE, univB, mem_union]
    by_cases h : (p : ℝ) ≤ thr c (j + 1)
    · exact Or.inr (GE_cover N c j (r + 2) p hp hpN h3 h)
    · left
      simp only [blkE, mem_filter, mem_Icc]
      exact ⟨⟨h3, Nat.le_floor hpz⟩, hp, hpN, Or.inr (not_le.mp h)⟩

lemma blkE_sup_le (N : ℕ) {c : ℝ} (hc : 0 ≤ c) (j : ℕ) :
    ((max ((blkE N c j).sup id) 1 : ℕ) : ℝ) ≤ thr c (j + 1) := by
  have h1 : (blkE N c j).sup id ≤ ⌊thr c (j + 1)⌋₊ := by
    apply Finset.sup_le
    intro p hp
    simp only [blkE, mem_filter, mem_Icc] at hp
    exact hp.1.2
  have h2 : (((blkE N c j).sup id : ℕ) : ℝ) ≤ thr c (j + 1) :=
    (Nat.cast_le.mpr h1).trans (Nat.floor_le (thr_pos c _).le)
  push_cast
  exact max_le h2 (one_le_thr hc _)

lemma GE_lev (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j r,
    (lev (GE N c j r) : ℝ) ≤ Real.exp (2 ^ (j + 1) * c * (2 * r + 6))
  | 0, r => by
    simp only [GE, lev, mul_one]
    rw [show max r (r + 1) = r + 1 by omega]
    push_cast
    have hs := blkE_sup_le N hc 0
    push_cast at hs
    calc (max (((blkE N c 0).sup id : ℕ) : ℝ) 1) ^ (r + 1) ≤ thr c (0 + 1) ^ (r + 1) :=
          pow_le_pow_left₀ (by positivity) hs _
      _ = Real.exp (2 ^ (0 + 1) * c * ((r + 1 : ℕ) : ℝ)) := thr_pow c _ _
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          push_cast
          have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
          nlinarith
  | j + 1, r => by
    simp only [GE, lev]
    rw [show max r (r + 1) = r + 1 by omega]
    push_cast
    have hs := blkE_sup_le N hc (j + 1)
    push_cast at hs
    have ih := GE_lev N hc j (r + 2)
    calc (max (((blkE N c (j + 1)).sup id : ℕ) : ℝ) 1) ^ (r + 1) * (lev (GE N c j (r + 2)) : ℝ)
        ≤ thr c (j + 1 + 1) ^ (r + 1) * Real.exp (2 ^ (j + 1) * c * (2 * ((r + 2 : ℕ) : ℝ) + 6)) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hs _) ih (Nat.cast_nonneg _)
            (pow_nonneg (thr_pos c _).le _)
      _ = Real.exp (2 ^ (j + 1 + 1) * c * (2 * r + 6)) := by
          rw [thr_pow, ← Real.exp_add]
          congr 1
          push_cast
          ring

lemma two_le_thr {c : ℝ} (hc : Real.log 2 ≤ c) (j : ℕ) : 2 ≤ thr c j := by
  have h0 : 0 ≤ c := le_trans (Real.log_nonneg (by norm_num)) hc
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ thr c 0 := by unfold thr; apply Real.exp_le_exp.mpr; simpa using hc
    _ ≤ thr c j := thr_mono h0 (Nat.zero_le j)

/-- The lower end used for the Mertens bound of block `j`. -/
noncomputable def yE (c : ℝ) (j : ℕ) : ℕ := if j = 0 then 2 else ⌊thr c j⌋₊

lemma yE_two {c : ℝ} (hc : Real.log 2 ≤ c) (j : ℕ) : 2 ≤ yE c j := by
  unfold yE; split_ifs
  · exact le_rfl
  · exact Nat.le_floor (by exact_mod_cast two_le_thr hc j)

lemma blkE_sub (N : ℕ) {c : ℝ} (j : ℕ) :
    blkE N c j ⊆ (Ioc (yE c j) ⌊thr c (j + 1)⌋₊).filter Nat.Prime := by
  intro p hp
  have hm := blkE_mem hp
  simp only [blkE, mem_filter, mem_Icc] at hp
  simp only [mem_filter, mem_Ioc]
  refine ⟨⟨?_, hp.1.2⟩, hp.2.1⟩
  unfold yE
  split_ifs with hj
  · omega
  · rcases hm.2.2.2.2 with h | h
    · exact absurd h hj
    · exact (Nat.floor_lt (thr_pos c _).le).mpr h

/-- `⌊thr c (j+1)⌋ ≤ 4 yE c j ²`. -/
lemma w_le {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) (j : ℕ) :
    ((⌊thr c (j + 1)⌋₊ : ℕ) : ℝ) ≤ 4 * ((yE c j : ℕ) : ℝ) ^ 2 := by
  have hfl := Nat.floor_le (thr_pos c (j + 1)).le
  refine hfl.trans ?_
  unfold yE
  split_ifs with hj
  · subst hj
    unfold thr
    have : Real.exp (2 ^ (0 + 1) * c) ≤ Real.exp (2 ^ (0 + 1) * (2 * Real.log 2)) :=
      Real.exp_le_exp.mpr (by norm_num; linarith)
    refine this.trans (le_of_eq ?_)
    rw [show (2 : ℝ) ^ (0 + 1) * (2 * Real.log 2) = ((4 : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  · rw [thr_succ]
    have h1 : thr c j < (⌊thr c j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (1 : ℝ) ≤ ⌊thr c j⌋₊ := by
      have : 2 ≤ ⌊thr c j⌋₊ := Nat.le_floor (by exact_mod_cast two_le_thr hc j)
      exact_mod_cast (by omega : 1 ≤ ⌊thr c j⌋₊)
    have h0 := (thr_pos c j).le
    nlinarith

lemma yE_le_w {c : ℝ} (hc : Real.log 2 ≤ c) (j : ℕ) : yE c j ≤ ⌊thr c (j + 1)⌋₊ := by
  have h0 : 0 ≤ c := le_trans (Real.log_nonneg (by norm_num)) hc
  unfold yE; split_ifs
  · exact Nat.le_floor (by exact_mod_cast two_le_thr hc _)
  · exact Nat.floor_le_floor (thr_mono h0 (by omega))

/-- **Every block has `Σ 1/(p - 1) ≤ 47`.** -/
lemma blkE_xsum (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) (j : ℕ) :
    ∑ p ∈ blkE N c j, xDen p ≤ 47 := by
  set y := yE c j with hy
  set w := ⌊thr c (j + 1)⌋₊ with hw
  have hy2 := yE_two hc j
  have hM := LeanLab.PNTSieve.Mertens.sum_inv_primes_block y w hy2 (yE_le_w hc j)
  have hl2 := Real.log_two_gt_d9
  have hy2r : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2r
  have hlpos : 0 < Real.log y := by linarith
  have hw4 : Real.log w ≤ Real.log 4 + 2 * Real.log y := by
    have hwpos : (0 : ℝ) < w := by
      have := yE_le_w hc j; have : (2 : ℝ) ≤ w := by exact_mod_cast hy2.trans this
      linarith
    have := Real.log_le_log hwpos (w_le hc hc2 j)
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2' := Real.log_two_lt_d9
  have hM2 : (Real.log w - Real.log y + 14) / Real.log y ≤ 23.2 := by
    rw [div_le_iff₀ hlpos]; nlinarith
  calc ∑ p ∈ blkE N c j, xDen p ≤ ∑ p ∈ blkE N c j, 2 * (1 / (p : ℝ)) :=
        sum_le_sum (fun p hp => xDen_le_two_div p (blkE_mem hp).2.2.2.1)
    _ = 2 * ∑ p ∈ blkE N c j, (1 / (p : ℝ)) := by rw [mul_sum]
    _ ≤ 2 * ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (blkE_sub N j) (fun _ _ _ => by positivity)
    _ ≤ 47 := by linarith

lemma thr_ge_big {c : ℝ} (hc : Real.log 2 ≤ c) {j : ℕ} (hj : 9 ≤ j) : 354 ≤ 2 ^ j * c - Real.log 2 := by
  have hl2 := Real.log_two_gt_d9
  have h : (512 : ℝ) ≤ 2 ^ j := by
    have : (2 : ℝ) ^ 9 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    norm_num at this; exact this
  nlinarith

/-- **For `j ≥ 9` a block has `Σ 1/(p - 1) ≤ 11/10` and all its primes above 101.** -/
lemma blkE_sharp (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) {j : ℕ}
    (hj : 9 ≤ j) : (∀ p ∈ blkE N c j, 101 ≤ p) ∧ ∑ p ∈ blkE N c j, xDen p ≤ 11 / 10 := by
  have hj0 : j ≠ 0 := by omega
  have hbig := thr_ge_big hc hj
  have hT : (101 : ℝ) ≤ thr c j := by
    unfold thr
    have := Real.add_one_le_exp (2 ^ j * c)
    have := Real.log_two_gt_d9
    linarith
  have h101 : ∀ p ∈ blkE N c j, 101 ≤ p := by
    intro p hp
    rcases (blkE_mem hp).2.2.2.2 with h | h
    · exact absurd h hj0
    · have : (101 : ℝ) < p := lt_of_le_of_lt hT h
      exact_mod_cast this.le
  refine ⟨h101, ?_⟩
  set y := yE c j with hy
  set w := ⌊thr c (j + 1)⌋₊ with hw
  have hy2 := yE_two hc j
  have hM := LeanLab.PNTSieve.Mertens.sum_inv_primes_block y w hy2 (yE_le_w hc j)
  have hyv : y = ⌊thr c j⌋₊ := by rw [hy]; unfold yE; rw [if_neg hj0]
  have hyr : thr c j / 2 ≤ (y : ℝ) := by
    rw [hyv]
    have := Nat.lt_floor_add_one (thr c j)
    have h1 : (1 : ℝ) ≤ thr c j / 2 := by linarith
    linarith
  have hly : 354 ≤ Real.log y := by
    have h1 := Real.log_le_log (by positivity) hyr
    rw [Real.log_div (thr_pos c j).ne' (by norm_num)] at h1
    unfold thr at h1; rw [Real.log_exp] at h1
    linarith
  have hlpos : 0 < Real.log y := by linarith
  have hy2r : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hw4 : Real.log w ≤ Real.log 4 + 2 * Real.log y := by
    have hwpos : (0 : ℝ) < w := by
      have := yE_le_w hc j; have : (2 : ℝ) ≤ w := by exact_mod_cast hy2.trans this
      linarith
    have := Real.log_le_log hwpos (w_le hc hc2 j)
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2' := Real.log_two_lt_d9
  have hM2 : (Real.log w - Real.log y + 14) / Real.log y ≤ 1045 / 1000 := by
    rw [div_le_iff₀ hlpos]; nlinarith
  calc ∑ p ∈ blkE N c j, xDen p ≤ ∑ p ∈ blkE N c j, 101 / 100 * (1 / (p : ℝ)) :=
        sum_le_sum (fun p hp => xDen_le_sharp p (h101 p hp))
    _ = 101 / 100 * ∑ p ∈ blkE N c j, (1 / (p : ℝ)) := by rw [mul_sum]
    _ ≤ 101 / 100 * ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (blkE_sub N j) (fun _ _ _ => by positivity)
    _ ≤ 11 / 10 := by nlinarith

/-- `ρ ≤ fR L` for any finset of primes above 101 with `Σ 1/(p - 1) ≤ 11/10`. -/
lemma rho_sharp_of (P : Finset ℕ) (L : ℕ) (h101 : ∀ p ∈ P, 101 ≤ p)
    (hs : ∑ p ∈ P, xDen p ≤ 11 / 10) : rho xDen (P, L, L + 1) ≤ fR L := by
  have h0 : ∀ p ∈ P, 0 ≤ xDen p := fun p _ => xDen_nonneg p
  have h1 : ∀ p ∈ P, xDen p ≤ 1 / 100 := by
    intro p hp
    have h3 : (101 : ℝ) ≤ p := by exact_mod_cast h101 p hp
    unfold xDen
    rw [if_pos (by have := h101 p hp; omega), div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hV : Real.exp (-(6 / 5)) ≤ ∏ p ∈ P, (1 - xDen p) := by
    refine le_trans ?_ (LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp _ _ h0
      (fun p hp => (h1 p hp).trans (by norm_num)))
    apply Real.exp_le_exp.mpr
    have hsq : ∑ p ∈ P, xDen p ^ 2 ≤ ∑ p ∈ P, xDen p / 100 := by
      apply sum_le_sum; intro p hp; nlinarith [h0 p hp, h1 p hp]
    rw [← sum_div] at hsq
    linarith
  set u := ∑ p ∈ P, xDen p with hu
  have hu0 : 0 ≤ u := sum_nonneg h0
  have hF : (0 : ℝ) < (L + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpow : u ^ (L + 1) ≤ (11 / 10 : ℝ) ^ (L + 1) := pow_le_pow_left₀ hu0 hs _
  have hT1 : truncErr P xDen L ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := by
    unfold truncErr; rw [← hu]
    exact div_le_div_of_nonneg_right hpow hF.le
  have hT2 : truncErr P xDen (L + 1) ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := by
    unfold truncErr; rw [← hu]
    have hf : ((L + 1 + 1).factorial : ℝ) = (L + 2) * (L + 1).factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf, pow_succ]
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    rw [div_le_div_iff₀ (by positivity) hF]
    have hp0 : 0 ≤ u ^ (L + 1) := by positivity
    have : u ^ (L + 1) * u ≤ u ^ (L + 1) * (L + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    nlinarith [mul_le_mul_of_nonneg_right hpow hF.le]
  have hVpos : 0 < ∏ p ∈ P, (1 - xDen p) := lt_of_lt_of_le (Real.exp_pos _) hV
  unfold rho
  simp only
  rw [div_le_iff₀ hVpos]
  have hfR : fR L = (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial / Real.exp (-(6 / 5)) := by
    unfold fR; rw [Real.exp_neg]; field_simp
  rw [hfR]
  have hq : 0 ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := by positivity
  calc max (truncErr P xDen L) (truncErr P xDen (L + 1))
      ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := max_le hT1 hT2
    _ = (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial / Real.exp (-(6 / 5)) *
          Real.exp (-(6 / 5)) := by field_simp
    _ ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial / Real.exp (-(6 / 5)) *
          ∏ p ∈ P, (1 - xDen p) :=
        mul_le_mul_of_nonneg_left hV (div_nonneg hq (Real.exp_pos _).le)

/-- `ρ ≤ e^{93 - L}` for any finset of primes from 3 with `Σ 1/(p - 1) ≤ 47`, at `L ≥ 1000`. -/
lemma rho_crude_of (P : Finset ℕ) (L : ℕ) (h3 : ∀ p ∈ P, 3 ≤ p)
    (hs : ∑ p ∈ P, xDen p ≤ 47) (hL : 1000 ≤ L) : rho xDen (P, L, L + 1) ≤ Real.exp (93 - L) := by
  have h0 : ∀ p ∈ P, 0 ≤ xDen p := fun p _ => xDen_nonneg p
  have h1 : ∀ p ∈ P, xDen p ≤ 1 / 2 := by
    intro p hp
    have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3 p hp
    unfold xDen
    rw [if_pos (h3 p hp), div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hV : Real.exp (-94) ≤ ∏ p ∈ P, (1 - xDen p) := by
    refine le_trans ?_ (LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp _ _ h0 h1)
    apply Real.exp_le_exp.mpr
    have hsq : ∑ p ∈ P, xDen p ^ 2 ≤ ∑ p ∈ P, xDen p / 2 := by
      apply sum_le_sum; intro p hp; nlinarith [h0 p hp, h1 p hp]
    rw [← sum_div] at hsq
    linarith
  have hu0 : 0 ≤ ∑ p ∈ P, xDen p := sum_nonneg h0
  have hL' : (1000 : ℝ) ≤ L := by exact_mod_cast hL
  have he := exp3_lt
  have hE : ∀ n : ℕ, L + 1 ≤ n → truncErr P xDen (n - 1) ≤ Real.exp (-(L + 1 : ℝ)) := by
    intro n hn
    unfold truncErr
    rw [Nat.sub_add_cancel (by omega)]
    have hn' : ((L : ℝ) + 1) ≤ n := by exact_mod_cast hn
    have h := pow_div_factorial_le_exp_neg _ hu0 n (by nlinarith)
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have h1' := hE (L + 1) le_rfl
  have h2' := hE (L + 2) (by omega)
  simp only [Nat.add_sub_cancel] at h1'
  rw [show L + 2 - 1 = L + 1 by omega] at h2'
  have hVpos : 0 < ∏ p ∈ P, (1 - xDen p) := lt_of_lt_of_le (Real.exp_pos _) hV
  unfold rho
  simp only
  rw [div_le_iff₀ hVpos]
  calc max (truncErr P xDen L) (truncErr P xDen (L + 1))
      ≤ Real.exp (-(L + 1 : ℝ)) := max_le h1' h2'
    _ = Real.exp (93 - L) * Real.exp (-94) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (93 - L) * ∏ p ∈ P, (1 - xDen p) :=
        mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le

/-- **`Σ ρ ≤ 2 e^{93 - r}`** over `GE N c j r`, for `r ≥ 1000`. -/
lemma GE_rho (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) :
    ∀ j r, 1000 ≤ r → rhoSum xDen (GE N c j r) ≤ 2 * Real.exp (93 - r)
  | 0, r, hr => by
    simp only [GE, rhoSum, add_zero]
    have := rho_crude_of _ r (fun p hp => (blkE_mem hp).2.2.2.1) (blkE_xsum N hc hc2 0) hr
    have := Real.exp_pos (93 - (r : ℝ))
    linarith
  | j + 1, r, hr => by
    simp only [GE, rhoSum]
    have h1 := rho_crude_of _ r (fun p hp => (blkE_mem hp).2.2.2.1) (blkE_xsum N hc hc2 (j + 1)) hr
    have h2 := GE_rho N hc hc2 j (r + 2) (by omega)
    have e : Real.exp (93 - ((r + 2 : ℕ) : ℝ)) = Real.exp (93 - r) * Real.exp (-2) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have he2 : Real.exp (-2) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have hpos := Real.exp_pos (93 - (r : ℝ))
    rw [e] at h2
    nlinarith

/-- **`Σ ρ ≤ 2 fR r + 2 e^{93 - (r + 2(j - 8))}`** over `GE N c j r` for `j ≥ 8`. -/
lemma GE_rho_sharp (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) :
    ∀ j, 8 ≤ j → ∀ r, 1000 ≤ r + 2 * (j - 8) →
      rhoSum xDen (GE N c j r) ≤ 2 * fR r + 2 * Real.exp (93 - ((r + 2 * (j - 8) : ℕ) : ℝ)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro r hr
    simp only [Nat.sub_self, mul_zero, add_zero] at hr ⊢
    have := GE_rho N hc hc2 8 r hr
    have := fR_nonneg r
    linarith
  | succ j hj ih =>
    intro r hr
    simp only [GE, rhoSum]
    obtain ⟨h101, hs⟩ := blkE_sharp N hc hc2 (j := j + 1) (by omega)
    have h1 := rho_sharp_of _ r h101 hs
    have h2 := ih (r + 2) (by omega)
    have e : r + 2 + 2 * (j - 8) = r + 2 * (j + 1 - 8) := by omega
    rw [e] at h2
    have h3 := fR_step r
    linarith

lemma two_fR_four_le : 2 * fR 4 ≤ 92 / 1000 := by
  unfold fR
  have h := exp_six_fifths_lt
  have hf : ((4 + 1).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf]
  norm_num
  nlinarith

lemma exp_neg_907_le : Real.exp (-907) ≤ 1 / 400 := by
  have h3 : Real.exp (-3) ≤ 1 / 20 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have he1 := Real.exp_one_gt_d9
    rw [h2]
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
    norm_num at this ⊢; linarith
  have : Real.exp (-907) ≤ Real.exp (-3) ^ 2 := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by norm_num)
  have := pow_le_pow_left₀ (Real.exp_pos (-3 : ℝ)).le h3 2
  norm_num at this; linarith

lemma big_aux2 (ℓ : ℝ) (h : (2 : ℝ) ^ 600 ≤ ℓ) :
    (10 : ℝ) ^ 6 ≤ ℓ ∧ 2 ^ 507 ≤ ⌊ℓ / (29 * Real.log 2)⌋₊ := by
  have h2p : (2 : ℝ) ^ 600 = 2 ^ 93 * 2 ^ 507 := by rw [← pow_add]
  have h94 : (2 : ℝ) ^ 20 ≤ 2 ^ 93 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h1p : (1 : ℝ) ≤ 2 ^ 507 := one_le_pow₀ (by norm_num)
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hc : ((2 ^ 507 : ℕ) : ℝ) = (2 : ℝ) ^ 507 := by push_cast; rfl
  rw [h2p] at h
  rw [h20] at h94
  generalize (2 : ℝ) ^ 93 = C at *
  generalize (2 : ℝ) ^ 507 = A at *
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hCA : 1048576 * A ≤ C * A := mul_le_mul_of_nonneg_right h94 (by linarith)
  clear h2p h20
  refine ⟨by nlinarith, ?_⟩
  apply Nat.le_floor
  rw [hc]
  clear hc
  rw [le_div_iff₀ (by positivity)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Rényi with `K = 28`, deterministic core with the count.** -/
theorem renyi28_count {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hE : Even N) (hℓ6 : (2 : ℝ) ^ 600 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    10 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 28)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨h10, ht507⟩ := big_aux2 ℓ hℓ6
  clear hℓ6
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN8 : (8 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- t, k and the real scale c
  set t := ⌊ℓ / (29 * Real.log 2)⌋₊ with ht
  have ht1 : ℓ / (29 * Real.log 2) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (ℓ / (29 * Real.log 2)); rw [← ht] at this; linarith
  have ht2 : (t : ℝ) ≤ ℓ / (29 * Real.log 2) := Nat.floor_le (by positivity)
  have htge : 2 ≤ t := le_trans (Nat.le_self_pow (by norm_num) 2) ht507
  set k := Nat.log 2 t with hk
  have hk507 : 507 ≤ k := Nat.le_log_of_pow_le (by norm_num) ht507
  clear ht507
  have hkt : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
  have htk : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hkt' : ((2 ^ k : ℕ) : ℝ) ≤ t := by exact_mod_cast hkt
  have htk1 : (t : ℝ) + 1 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
    have : t + 1 ≤ 2 ^ (k + 1) := htk
    have : ((t + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [pow_succ] at this; push_cast at this ⊢; linarith
  set L := ℓ / 29 with hL
  have h2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  set c := L / ((2 ^ k : ℕ) : ℝ) with hc
  have hLe : ℓ / (29 * Real.log 2) * Real.log 2 = L := by rw [hL]; field_simp
  have hc1 : Real.log 2 ≤ c := by
    rw [hc, le_div_iff₀ h2k, ← hLe]
    have := mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
    linarith
  have hc2 : c ≤ 2 * Real.log 2 := by
    rw [hc, div_le_iff₀ h2k, ← hLe]
    have h1 : ℓ / (29 * Real.log 2) ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right h1 hl2pos.le
    linarith
  have hc0 : 0 ≤ c := le_trans hl2pos.le hc1
  have h2kc : (2 : ℝ) ^ k * c = L := by
    rw [hc]; push_cast; field_simp
  have hthr : thr c k = Real.exp L := by unfold thr; rw [h2kc]
  set j := k - 1 with hj
  have hjk : j + 1 = k := by omega
  have hLbig : (10 : ℝ) ≤ L := by rw [hL]; linarith
  set z := ⌊Real.exp L⌋₊ with hz
  have hz3 : 3 ≤ z := by
    apply Nat.le_floor
    have := Real.add_one_le_exp L
    push_cast; linarith
  have hzr : (z : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos _).le
  have hz1 : Real.exp L < (z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogz : Real.log z ≤ L := by
    have := Real.log_le_log (by positivity) hzr
    rwa [Real.log_exp] at this
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogz1 : L < Real.log ((z : ℝ) + 1) := by
    have := Real.log_lt_log (Real.exp_pos _) hz1
    rwa [Real.log_exp] at this
  -- the blocks
  set Bs := GE N c j 4 with hBs
  have hG : Good Bs := GE_good N hc0 j 4 ⟨2, rfl⟩
  have hmem := GE_mem N hc0 j 4
  rw [hjk, hthr] at hmem
  have hcov := GE_cover N c j 4
  rw [hjk, hthr] at hcov
  have hlen : Bs.length = k := by rw [hBs, GE_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply Nat.le_floor
    have h1 := GE_lev N hc0 j 4
    rw [hjk] at h1
    have h2 : Real.exp (2 ^ k * c * (2 * ((4 : ℕ) : ℝ) + 6)) ≤ Real.exp (49 / 100 * ℓ) := by
      apply Real.exp_le_exp.mpr
      rw [h2kc, hL]; push_cast; nlinarith
    exact h1.trans (h2.trans hE2)
  have hρ : rhoSum xDen Bs ≤ 1 / 10 := by
    refine (GE_rho_sharp N hc1 hc2 j (by omega) 4 (by omega)).trans ?_
    have hlv : (1000 : ℝ) ≤ ((4 + 2 * (j - 8) : ℕ) : ℝ) := by
      have : 1000 ≤ 4 + 2 * (j - 8) := by omega
      exact_mod_cast this
    have h0 : Real.exp (93 - ((4 + 2 * (j - 8) : ℕ) : ℝ)) ≤ Real.exp (-907) :=
      Real.exp_le_exp.mpr (by linarith)
    have := two_fR_four_le
    have := exp_neg_907_le
    linarith
  -- the sieve count
  have hS := hK N (by omega) Bs hG (fun p hp => ⟨(hmem p hp).2.2.1, (hmem p hp).2.2.2⟩) hlev hρ
  rw [hlen] at hS
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hV : Real.exp (-36) / Real.log z ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    have := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz3 (univB Bs)
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, Nat.le_floor (hmem p hp).1⟩)
    refine this.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
    simp only [xDen, if_pos (hmem p hp).2.2.2]
  have hV2 : Real.exp (-36) * 29 / ℓ ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    refine le_trans ?_ hV
    rw [div_le_div_iff₀ hℓpos hlogz_pos]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 29 ≤ ℓ := by rw [hL] at hlogz; linarith
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 29 / ℓ) * (1 / 2) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 29 / ℓ) * (1 / 2) =
      (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have := Real.exp_pos (-37 : ℝ); have := Real.exp_pos (-36 : ℝ); linarith
  -- the error term: 3^k K N / ℓ^5 ≤ |K| N / ℓ^3
  have h3k : ((3 : ℝ) ^ k) ≤ ℓ ^ 2 := by
    have h1 : (3 : ℝ) ^ k ≤ ((2 ^ k : ℕ) : ℝ) ^ 2 := by
      push_cast; rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ ℓ := by
      refine hkt'.trans (ht2.trans ?_)
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact h1.trans (pow_le_pow_left₀ (by positivity) h2 2)
  have h5r : ℓ ^ (5 : ℝ) = ℓ ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have herr : 3 ^ k * (K * N / ℓ ^ (5 : ℝ)) ≤ |K| * N / ℓ ^ (3 : ℝ) := by
    rw [h5r, h3r]
    have hK1 : K * N / ℓ ^ 5 ≤ |K| * N / ℓ ^ 5 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hNpos.le)
        (by positivity)
    have hK0 : 0 ≤ |K| * N / ℓ ^ 5 := by positivity
    calc 3 ^ k * (K * N / ℓ ^ 5) ≤ 3 ^ k * (|K| * N / ℓ ^ 5) :=
          mul_le_mul_of_nonneg_left hK1 (by positivity)
      _ ≤ ℓ ^ 2 * (|K| * N / ℓ ^ 5) := mul_le_mul_of_nonneg_right h3k hK0
      _ = |K| * N / ℓ ^ 3 := by field_simp
  have hzle : (z : ℝ) ≤ Real.exp (ℓ / 3) := by
    refine hzr.trans (Real.exp_le_exp.mpr ?_); rw [hL]; linarith
  set Surv := (goldbachSeq N).filter (fun a => ∀ p ∈ univB Bs, ¬ p ∣ a) with hSurv
  have hcardS : (sifted (goldbachSeq N) (univB Bs) : ℝ) = (Surv.card : ℝ) := by
    simp [sifted, hSurv]
  set small := (range (z + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ z + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 28) with hGd
  -- every survivor outside the small image is N - p for a good p
  have hsub : Surv \ small ⊆ Gd.image (fun p => N - p) := by
    intro m hm
    rw [mem_sdiff] at hm
    obtain ⟨hmS, hmn⟩ := hm
    rw [hSurv, mem_filter] at hmS
    obtain ⟨hmG, hmP⟩ := hmS
    unfold goldbachSeq at hmG
    rw [mem_image] at hmG
    obtain ⟨p, hp, rfl⟩ := hmG
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpN, hpp⟩ := hp
    have hpz : z < p := by
      by_contra h
      push Not at h
      exact hmn (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
    have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hmodd : Odd (N - p) := by
      rcases hE with ⟨a, ha⟩
      rcases hpodd with ⟨b, hb⟩
      exact ⟨a - b - 1, by omega⟩
    have hm0 : N - p ≠ 0 := by omega
    have hfac_big : ∀ q ∈ (N - p).primeFactorsList, z + 1 ≤ q := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      by_contra hlt
      push Not at hlt
      have hqz : q ≤ z := by omega
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hqd)
      have hq3 : 3 ≤ q := by have := hqp.two_le; omega
      by_cases hqN : q ∣ N
      · have : q ∣ p := by
          have h1 := Nat.dvd_sub hqN hqd
          rwa [Nat.sub_sub_self hpN.le] at h1
        have := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp this
        omega
      · exact hmP q (hcov q hqp hqN hq3 ((Nat.le_floor_iff (Real.exp_pos _).le).mp hqz)) hqd
    have hpow := pow_bigOmega_le (N - p) (z + 1) hm0 hfac_big
    have hpowr : ((z : ℝ) + 1) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := by
      have : (z + 1) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := hpow.trans (Nat.sub_le N p)
      exact_mod_cast this
    have hlogpow : (ArithmeticFunction.cardFactors (N - p) : ℝ) * Real.log ((z : ℝ) + 1) ≤ ℓ := by
      have := Real.log_le_log (by positivity) hpowr
      rwa [Real.log_pow] at this
    have hΩr : ArithmeticFunction.cardFactors (N - p) ≤ 28 := by
      by_contra hcon
      push Not at hcon
      have h29 : (29 : ℝ) ≤ (ArithmeticFunction.cardFactors (N - p) : ℝ) := by exact_mod_cast hcon
      have hl0 : 0 < Real.log ((z : ℝ) + 1) := by linarith
      have : 29 * Real.log ((z : ℝ) + 1) ≤ ℓ :=
        (mul_le_mul_of_nonneg_right h29 hl0.le).trans hlogpow
      rw [hL] at hlogz1
      linarith
    refine mem_image.mpr ⟨p, ?_, rfl⟩
    rw [hGd, mem_filter, mem_filter, mem_range]
    exact ⟨⟨hpN, hpp⟩, hΩr⟩
  have hc1 : Surv.card ≤ (Surv \ small).card + small.card := card_le_card_sdiff_add_card
  have hc2 : (Surv \ small).card ≤ Gd.card := (card_le_card hsub).trans card_image_le
  have hc3 : (Surv.card : ℝ) ≤ (Gd.card : ℝ) + (z : ℝ) + 1 := by
    have : Surv.card ≤ Gd.card + (z + 1) := by omega
    exact_mod_cast this
  -- the count
  have hfin : (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 - |K| * N / ℓ ^ (3 : ℝ) ≤
      (Surv.card : ℝ) := by rw [← hcardS]; linarith
  have hgoal : 10 * Real.exp (-36) * N / ℓ ^ 2 ≤
      (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 -
        (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := Real.exp_pos (-37 : ℝ); have e2 := Real.exp_pos (-36 : ℝ)
    nlinarith [mul_nonneg e2.le (show (0 : ℝ) ≤ (N : ℝ) - 8 by linarith),
      mul_nonneg e1.le (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  linarith only [hgoal, hfin, hc3, hE3, hzle]


open Filter in
/-- **Rényi's theorem with the count and `K = 28`, PROVED unconditional**: for every large even
`N`, `#{p < N prime : Ω(N - p) ≤ 28} ≥ 10 e^{-36} N/log² N`. Ineffective, through Siegel-Walfisz. -/
theorem renyi28_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    10 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 28)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_blocks_rel 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 600)))
  refine ⟨⌈max (max X X₂) Y⌉₊, fun N hN hE => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact renyi28_count hK N hE (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's theorem with `K = 28`, PROVED unconditional.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 28`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN; Chen 1973 has `Ω(m) ≤ 2` by a far stronger sieve. -/
theorem renyi28_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 28 := by
  obtain ⟨N₀, hN₀⟩ := renyi28_fixedK_count
  refine ⟨max N₀ 4, fun N hN hE => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) hE
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < 10 * Real.exp (-36) * N / Real.log N ^ 2 := by positivity
  have hc : 0 < (((range N).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 28)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨p, hp⟩ := card_pos.mp hc
  simp only [mem_filter, mem_range] at hp
  obtain ⟨⟨hpN, hpp⟩, hΩ⟩ := hp
  exact ⟨p, N - p, hpp, by omega, by omega, hΩ⟩

end LeanLab.PNTPort.BVMax

