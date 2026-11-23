module

public import LeanLab.Romanov.SingProd

/-!
# Romanov's lemma: `Σ_{m ≤ K} singProd(2^m - 1) ≤ 8 log 2 · e^13 · K`

Lab proof, unit U-5601, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics:
Romanov 1934, in Erdős's 1950 form. Binary Goldbach is OPEN; this is the Linnik-Goldbach line,
IDEAS I-5052.

Proof. Expand `singProd(2^m - 1) = Σ_{s ⊆ primeFactors(2^m - 1)} w(s)` and swap the sums. A set
`s` of primes divides `2^m - 1` exactly when its order `e(s)`, the least `e ≥ 1` with
`∏ s ∣ 2^e - 1`, divides `m`, by `gcd(2^a - 1, 2^b - 1) = 2^gcd(a, b) - 1`; so `s` is counted at
most `K / e(s)` times. Group the `s` by `j = ⌊log₂ e(s)⌋`: every `s` in group `j` divides
`M_j = ∏_{e ≤ 2^(j+1)} (2^e - 1)`, which has at most `4^(j+1)` prime factors, so the group's
weight is at most `singProd(M_j) ≤ e^13 · 2(j + 1) log 2`; and `Σ_j (j + 1)/2^j ≤ 4`.

* `ord_dvd`: `e(s) ∣ m` whenever `∏ s ∣ 2^m - 1`, `m ≥ 1`.
* `card_good_le`: `#{m ≤ K : s ⊆ primeFactors(2^m - 1)} ≤ K / e(s)`.
* `singProd_M_le`: `singProd(M_j) ≤ e^13 · 2(j + 1) log 2`.
* `sum_succ_div_pow_le`: `Σ_{j < n} (j + 1)/2^j ≤ 4`.
* `romanov_lemma`: the bound, PROVED, no cited input.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset Real
open LeanLab.SchnirelmannGoldbach (singProd)

/-- `s` is a set of primes dividing `2^m - 1`, `m ≥ 1`. -/
def Good (s : Finset ℕ) (m : ℕ) : Prop := 0 < m ∧ s ⊆ (2 ^ m - 1).primeFactors

lemma two_pow_sub_one_ne_zero {m : ℕ} (hm : 0 < m) : 2 ^ m - 1 ≠ 0 := by
  have : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

lemma subset_pf_iff (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) {n : ℕ} (hn : n ≠ 0) :
    s ⊆ n.primeFactors ↔ ∏ p ∈ s, p ∣ n := by
  constructor
  · intro h
    exact prod_primes_dvd n (fun p hp => (hs p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (h hp))
  · intro h p hp
    exact Nat.mem_primeFactors.2 ⟨hs p hp, (dvd_prod_of_mem _ hp).trans h, hn⟩

open Classical in
/-- The order `e(s)`: the least `m ≥ 1` with `s ⊆ primeFactors(2^m - 1)`, `0` if none. -/
noncomputable def ord (s : Finset ℕ) : ℕ :=
  if h : ∃ m, Good s m then Nat.find h else 0

lemma ord_spec {s : Finset ℕ} (h : ∃ m, Good s m) : Good s (ord s) := by
  classical
  unfold ord
  rw [dif_pos h]
  exact Nat.find_spec h

lemma ord_min {s : Finset ℕ} {m : ℕ} (hm : Good s m) : ord s ≤ m := by
  classical
  have h : ∃ m, Good s m := ⟨m, hm⟩
  unfold ord
  rw [dif_pos h]
  exact Nat.find_min' h hm

theorem ord_dvd {s : Finset ℕ} {m : ℕ} (hm : Good s m) : ord s ∣ m := by
  have hs : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hm.2 hp)
  have he := ord_spec ⟨m, hm⟩
  set e := ord s
  have hde : ∏ p ∈ s, p ∣ 2 ^ e - 1 := (subset_pf_iff s hs (two_pow_sub_one_ne_zero he.1)).1 he.2
  have hdm : ∏ p ∈ s, p ∣ 2 ^ m - 1 := (subset_pf_iff s hs (two_pow_sub_one_ne_zero hm.1)).1 hm.2
  have hg := Nat.dvd_gcd hde hdm
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have hg0 : 0 < Nat.gcd e m := Nat.gcd_pos_of_pos_left _ he.1
  have hgood : Good s (Nat.gcd e m) :=
    ⟨hg0, (subset_pf_iff s hs (two_pow_sub_one_ne_zero hg0)).2 hg⟩
  have h1 : e ≤ Nat.gcd e m := ord_min hgood
  have h2 : Nat.gcd e m ≤ e := Nat.le_of_dvd he.1 (Nat.gcd_dvd_left e m)
  have : Nat.gcd e m = e := le_antisymm h2 h1
  rw [← this]
  exact Nat.gcd_dvd_right e m

theorem card_good_le (s : Finset ℕ) (K : ℕ) (h : ∃ m, Good s m) :
    #{m ∈ Icc 1 K | s ⊆ (2 ^ m - 1).primeFactors} ≤ K / ord s := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine card_le_card fun m hm => ?_
  simp only [mem_filter, mem_Icc] at hm
  simp only [mem_filter, mem_Ioc]
  exact ⟨⟨by omega, hm.1.2⟩, ord_dvd ⟨by omega, hm.2⟩⟩

/-- `M_j = ∏_{1 ≤ e ≤ 2^(j+1)} (2^e - 1)`. -/
def M (j : ℕ) : ℕ := ∏ e ∈ Icc 1 (2 ^ (j + 1)), (2 ^ e - 1)

lemma M_ne_zero (j : ℕ) : M j ≠ 0 := by
  unfold M
  rw [prod_ne_zero_iff]
  intro e he
  exact two_pow_sub_one_ne_zero (by simp only [mem_Icc] at he; omega)

lemma M_le (j : ℕ) : M j ≤ 2 ^ (2 ^ (j + 1) * 2 ^ (j + 1)) := by
  unfold M
  calc ∏ e ∈ Icc 1 (2 ^ (j + 1)), (2 ^ e - 1) ≤ ∏ _e ∈ Icc 1 (2 ^ (j + 1)), 2 ^ (2 ^ (j + 1)) := by
        refine prod_le_prod' fun e he => ?_
        simp only [mem_Icc] at he
        exact le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right (by norm_num) he.2)
    _ = 2 ^ (2 ^ (j + 1) * 2 ^ (j + 1)) := by
        rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul, mul_comm]

lemma card_pf_M_le (j : ℕ) : (M j).primeFactors.card ≤ 2 ^ (j + 1) * 2 ^ (j + 1) := by
  have h := le_trans (two_pow_card_le (M j) (M_ne_zero j)) (M_le j)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem singProd_M_le (j : ℕ) :
    singProd (M j) ≤ exp 13 * (2 * (j + 1) * log 2) := by
  have hy : 2 ≤ 2 ^ (j + 1) * 2 ^ (j + 1) := by
    have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have h := singProd_le_log (M j) _ hy (card_pf_M_le j)
  have hlog : log ((2 ^ (j + 1) * 2 ^ (j + 1) : ℕ) : ℝ) = 2 * (j + 1) * log 2 := by
    push_cast
    rw [← pow_add, Real.log_pow]
    push_cast; ring
  rw [hlog] at h
  exact h

lemma dvd_M {e j : ℕ} (he : 0 < e) (hej : e < 2 ^ (j + 1)) : 2 ^ e - 1 ∣ M j := by
  unfold M
  exact dvd_prod_of_mem _ (by simp only [mem_Icc]; omega)

theorem sum_succ_div_pow_le (n : ℕ) : ∑ j ∈ range n, ((j : ℝ) + 1) / 2 ^ j ≤ 4 := by
  have key : ∀ n : ℕ, ∑ j ∈ range n, ((j : ℝ) + 1) / 2 ^ j + (2 * n + 4) / 2 ^ n = 4 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ]
      have h2 : ((n : ℝ) + 1) / 2 ^ n + (2 * ((n + 1 : ℕ) : ℝ) + 4) / 2 ^ (n + 1) =
          (2 * n + 4) / 2 ^ n := by
        push_cast
        rw [pow_succ]
        field_simp
        ring
      linarith
  have := key n
  have : 0 ≤ (2 * (n : ℝ) + 4) / 2 ^ n := by positivity
  linarith

/-- **Romanov's lemma**: `Σ_{1 ≤ m ≤ K} singProd(2^m - 1) ≤ 8 log 2 · e^13 · K`. -/
theorem romanov_lemma (K : ℕ) :
    ∑ m ∈ Icc 1 K, singProd (2 ^ m - 1) ≤ 8 * log 2 * exp 13 * K := by
  set P : ℕ → Finset (Finset ℕ) := fun m => (2 ^ m - 1).primeFactors.powerset with hP
  set U := (Icc 1 K).biUnion P with hU
  have hPU : ∀ m ∈ Icc 1 K, P m ⊆ U := fun m hm => subset_biUnion_of_mem P hm
  -- step 1: expand and swap
  have step1 : ∑ m ∈ Icc 1 K, singProd (2 ^ m - 1) =
      ∑ s ∈ U, (#{m ∈ Icc 1 K | s ⊆ (2 ^ m - 1).primeFactors} : ℝ) * w s := by
    calc ∑ m ∈ Icc 1 K, singProd (2 ^ m - 1)
        = ∑ m ∈ Icc 1 K, ∑ s ∈ U, if s ∈ P m then w s else 0 := by
          refine sum_congr rfl fun m hm => ?_
          rw [singProd_eq_sum, sum_ite_mem, inter_eq_right.2 (hPU m hm)]
      _ = ∑ s ∈ U, ∑ m ∈ Icc 1 K, if s ∈ P m then w s else 0 := sum_comm
      _ = _ := by
          refine sum_congr rfl fun s _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          simp only [hP, mem_powerset]
  -- step 2: each `s` is counted at most `K / e(s)` times
  have hex : ∀ s ∈ U, ∃ m, Good s m := by
    intro s hs
    rw [hU, mem_biUnion] at hs
    obtain ⟨m, hm, hsm⟩ := hs
    simp only [mem_Icc] at hm
    exact ⟨m, by omega, mem_powerset.1 hsm⟩
  have hord : ∀ s ∈ U, 0 < ord s ∧ ord s ≤ K := by
    intro s hs
    obtain ⟨m, hm⟩ := hex s hs
    refine ⟨(ord_spec ⟨m, hm⟩).1, ?_⟩
    rw [hU, mem_biUnion] at hs
    obtain ⟨m', hm', hsm'⟩ := hs
    simp only [mem_Icc] at hm'
    exact le_trans (ord_min ⟨by omega, mem_powerset.1 hsm'⟩) hm'.2
  have step2 : ∑ s ∈ U, (#{m ∈ Icc 1 K | s ⊆ (2 ^ m - 1).primeFactors} : ℝ) * w s ≤
      ∑ s ∈ U, (K : ℝ) / ord s * w s := by
    refine sum_le_sum fun s hs => ?_
    refine mul_le_mul_of_nonneg_right ?_ (w_nonneg s)
    have hc := card_good_le s K (hex s hs)
    have hc' : ((#{m ∈ Icc 1 K | s ⊆ (2 ^ m - 1).primeFactors} : ℕ) : ℝ) ≤
        ((K / ord s : ℕ) : ℝ) := Nat.cast_le.2 hc
    exact hc'.trans Nat.cast_div_le
  -- step 3: group by `j = ⌊log₂ e(s)⌋`
  have hmaps : ∀ s ∈ U, Nat.log 2 (ord s) ∈ range (K + 1) := by
    intro s hs
    rw [mem_range]
    have := Nat.log_le_self 2 (ord s)
    have := (hord s hs).2
    omega
  have step3 : ∑ s ∈ U, (K : ℝ) / ord s * w s =
      ∑ j ∈ range (K + 1), ∑ s ∈ U with Nat.log 2 (ord s) = j, (K : ℝ) / ord s * w s :=
    (sum_fiberwise_of_maps_to hmaps _).symm
  have block : ∀ j ∈ range (K + 1),
      ∑ s ∈ U with Nat.log 2 (ord s) = j, (K : ℝ) / ord s * w s ≤
        (K : ℝ) * (2 * log 2 * exp 13) * (((j : ℝ) + 1) / 2 ^ j) := by
    intro j _
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc ∑ s ∈ U with Nat.log 2 (ord s) = j, (K : ℝ) / ord s * w s
        ≤ ∑ s ∈ U with Nat.log 2 (ord s) = j, (K : ℝ) / 2 ^ j * w s := by
          refine sum_le_sum fun s hs => ?_
          rw [mem_filter] at hs
          refine mul_le_mul_of_nonneg_right ?_ (w_nonneg s)
          have h0 := (hord s hs.1).1
          have hpow : 2 ^ j ≤ ord s := by
            rw [← hs.2]; exact Nat.pow_log_le_self 2 h0.ne'
          have hpow' : (2 : ℝ) ^ j ≤ ord s := by exact_mod_cast hpow
          exact div_le_div_of_nonneg_left hK (by positivity) hpow'
      _ = (K : ℝ) / 2 ^ j * ∑ s ∈ U with Nat.log 2 (ord s) = j, w s := by rw [mul_sum]
      _ ≤ (K : ℝ) / 2 ^ j * ∑ s ∈ (M j).primeFactors.powerset, w s := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine sum_le_sum_of_subset_of_nonneg ?_ fun s _ _ => w_nonneg s
          intro s hs
          rw [mem_filter] at hs
          rw [mem_powerset]
          have hg := ord_spec (hex s hs.1)
          have hlt : ord s < 2 ^ (j + 1) := by
            rw [← hs.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
          exact hg.2.trans (Nat.primeFactors_mono (dvd_M hg.1 hlt) (M_ne_zero j))
      _ = (K : ℝ) / 2 ^ j * singProd (M j) := by rw [singProd_eq_sum]
      _ ≤ (K : ℝ) / 2 ^ j * (exp 13 * (2 * (j + 1) * log 2)) :=
          mul_le_mul_of_nonneg_left (singProd_M_le j) (by positivity)
      _ = (K : ℝ) * (2 * log 2 * exp 13) * (((j : ℝ) + 1) / 2 ^ j) := by ring
  have hc : (0 : ℝ) ≤ K * (2 * log 2 * exp 13) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  calc ∑ m ∈ Icc 1 K, singProd (2 ^ m - 1)
      ≤ ∑ s ∈ U, (K : ℝ) / ord s * w s := step1 ▸ step2
    _ = ∑ j ∈ range (K + 1), ∑ s ∈ U with Nat.log 2 (ord s) = j, (K : ℝ) / ord s * w s := step3
    _ ≤ ∑ j ∈ range (K + 1), (K : ℝ) * (2 * log 2 * exp 13) * (((j : ℝ) + 1) / 2 ^ j) :=
        sum_le_sum block
    _ = (K : ℝ) * (2 * log 2 * exp 13) * ∑ j ∈ range (K + 1), (((j : ℝ) + 1) / 2 ^ j) := by
        rw [mul_sum]
    _ ≤ (K : ℝ) * (2 * log 2 * exp 13) * 4 :=
        mul_le_mul_of_nonneg_left (sum_succ_div_pow_le _) hc
    _ = 8 * log 2 * exp 13 * K := by ring

end LeanLab.Romanov
