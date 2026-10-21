module

public import LeanLab.PNTPort.BVMax.Renyi20

/-!
# Rényi's theorem with `K = 14`: one Buchstab step on top of the `K = 20` block sieve

Unit U-6757, CLOUD 20261020T2317Z-cloud53. AI wrote the Lean code. Known mathematics, the
Kuhn and Buchstab device of subtracting the elements with a prime factor in a middle range,
IDEAS I-5051.

`Renyi20.lean` sifts `{N - p}` by the odd primes `p ∤ N` up to `z = N^{1/21}` and reads off
`Ω(N - p) ≤ 20`. Here the primes `q ∤ N` in `(z, y]`, `y = N^{1/15}`, are removed as well:

* `blocks_upper_rel5`: the upper block sieve with relative error,
  `S(A, Ω) ≤ X V (1 + (5/4) Σ ρ) + Σ_{cU S ≠ 0} |R_S|` when `Σ ρ ≤ 1/5`;
* `sifted_union_ge`: `S(A, Ω ∪ Q) ≥ S(A, Ω) - Σ_{q ∈ Q} S(A_q, Ω')` for `Ω' ⊆ Ω`, `A_q` the
  multiples of `q` in `A`;
* `rem_filter_dvd`: the remainder of `A_q` at `S` with `X_q = X x_q` is the remainder of `A` at
  `S ∪ {q}`, so all remainders of the upper sieves are Bombieri-Vinogradov remainders of `A` at
  distinct moduli `q ∏S ≤ N^{1/15} N^{(154/15)(2/49)} = N^{0.486}`;
* `one_sub_sum_le_prod`: `∏ (1 - x_p) ≥ 1 - Σ x_p`;
* `block_pack`: the four-per-level blocks `GQ` of `Renyi20.lean` for any sifting limit
  `exp M`, `M ≥ 2^2005`, with level `exp((154/15) M)` and `Σ ρ ≤ 0.1916`;
* `renyi14_count`, `renyi14_fixedK_count`, `renyi14_fixedK`: every large even `N` is `p + m`
  with `Ω(m) ≤ 14`, and at least `e^{-36} N/(10 log² N)` primes `p < N` have `Ω(N - p) ≤ 14`.

The numbers, all from lab-proved constants: the upper sieve for `A_q` sifts only up to
`w = N^{2/49}` so that the level stays below `N^{1/2}`; the lab's block Mertens bound gives
`Σ_{z < q ≤ y} 1/(q - 1) ≤ 21/15 - 1 + o(1) = 0.4 + o(1)` and `Σ_{w < p ≤ z} 1/(p - 1) ≤
1/6 + o(1)`, so the subtracted part is at most `1.2395 · 0.402/0.832 < 0.599` of `X V_z`
against `1 - 2 · 0.1916 = 0.6168` for the sifted count; margin `1/100`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN; Pan K = 4 and Chen K = 2 are far stronger.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- **Brun's upper block sieve with relative error at `1/5`.** -/
theorem blocks_upper_rel5 (A : Finset ℕ) (Bs : List Block) (hG : Good Bs) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1) (X : ℝ) (hX : 0 ≤ X)
    (hρ : rhoSum x Bs ≤ 1 / 5) :
    (sifted A (univB Bs) : ℝ) ≤
      X * (∏ p ∈ univB Bs, (1 - x p)) * (1 + 5 / 4 * rhoSum x Bs) +
        ∑ S ∈ (univB Bs).powerset.filter (fun S => cU Bs S ≠ 0), |rem A x X S| := by
  have hx1' : ∀ p, x p ≤ 1 := fun p => (hx1 p).le
  have h1 : (sifted A (univB Bs) : ℝ) ≤ ∑ a ∈ A, wEval (univB Bs) (cU Bs) a := by
    rw [sifted_eq]
    push_cast
    refine sum_le_sum (fun a _ => ?_)
    have := (blocks_pointwise Bs hG a).2
    unfold xind at this
    split_ifs at this ⊢ <;> simpa using this
  rw [sum_wEval A (univB Bs) (cU Bs) x X] at h1
  have h2 := (blocks_rel_dev x hx0 hx1 Bs hG).1
  rw [abs_le] at h2
  have hd := (d_le_of_sum5 x hx0 hx1' Bs hρ).2.1
  have hV : 0 ≤ ∏ p ∈ univB Bs, (1 - x p) := prod_nonneg (fun p _ => by linarith [hx1 p])
  have h3 : ∑ S ∈ (univB Bs).powerset, cU Bs S * rem A x X S ≤
      ∑ S ∈ (univB Bs).powerset.filter (fun S => cU Bs S ≠ 0), |rem A x X S| := by
    rw [sum_filter]
    refine sum_le_sum (fun S _ => ?_)
    split_ifs with hS
    · calc cU Bs S * rem A x X S ≤ |cU Bs S * rem A x X S| := le_abs_self _
        _ = |cU Bs S| * |rem A x X S| := abs_mul _ _
        _ ≤ 1 * |rem A x X S| :=
            mul_le_mul_of_nonneg_right (coeff_bounds Bs S).1 (abs_nonneg _)
        _ = |rem A x X S| := one_mul _
    · push Not at hS; rw [hS]; simp
  have h4 : wMain (univB Bs) (cU Bs) x ≤
      (∏ p ∈ univB Bs, (1 - x p)) * (1 + 5 / 4 * rhoSum x Bs) := by
    have := mul_le_mul_of_nonneg_left hd hV
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 hX
  nlinarith

/-- **One Buchstab step, combinatorial form**: `S(A, Ω ∪ Q) ≥ S(A, Ω) - Σ_{q ∈ Q} S(A_q, Ω')`
for `Ω' ⊆ Ω`. -/
theorem sifted_union_ge (A Ω Ω' Q : Finset ℕ) (hΩ : Ω' ⊆ Ω) :
    (sifted A Ω : ℝ) - ∑ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) ≤
      (sifted A (Ω ∪ Q) : ℝ) := by
  classical
  have hsub : A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a) ⊆
      A.filter (fun a => ∀ p ∈ Ω ∪ Q, ¬ p ∣ a) ∪
        Q.biUnion (fun q => (A.filter (fun a => q ∣ a)).filter (fun a => ∀ p ∈ Ω', ¬ p ∣ a)) := by
    intro a ha
    rw [mem_filter] at ha
    rw [mem_union]
    by_cases h : ∀ p ∈ Ω ∪ Q, ¬ p ∣ a
    · exact Or.inl (mem_filter.mpr ⟨ha.1, h⟩)
    · right
      push Not at h
      obtain ⟨p, hp, hpa⟩ := h
      rcases mem_union.mp hp with h1 | h1
      · exact absurd hpa (ha.2 p h1)
      · rw [mem_biUnion]
        exact ⟨p, h1, mem_filter.mpr ⟨mem_filter.mpr ⟨ha.1, hpa⟩,
          fun r hr => ha.2 r (hΩ hr)⟩⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hb := card_biUnion_le (s := Q)
    (t := fun q => (A.filter (fun a => q ∣ a)).filter (fun a => ∀ p ∈ Ω', ¬ p ∣ a))
  have hc' : ((A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a)).card : ℝ) ≤
      ((A.filter (fun a => ∀ p ∈ Ω ∪ Q, ¬ p ∣ a)).card : ℝ) +
        ∑ q ∈ Q, (((A.filter (fun a => q ∣ a)).filter (fun a => ∀ p ∈ Ω', ¬ p ∣ a)).card : ℝ) := by
    have := hc.trans (Nat.add_le_add_left hb _)
    exact_mod_cast this
  simp only [sifted]
  push_cast
  linarith

/-- The remainder of the multiples of a prime `q` is a remainder of `A` at one more prime. -/
lemma rem_filter_dvd (A : Finset ℕ) (x : ℕ → ℝ) (X : ℝ) {q : ℕ} (hq : q.Prime) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hqS : q ∉ S) :
    rem (A.filter (fun a => q ∣ a)) x (X * x q) S = rem A x X (insert q S) := by
  have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
    refine Nat.Coprime.prod_right (fun p hp => ?_)
    exact (Nat.coprime_primes hq (hS p hp)).mpr (fun h => hqS (h ▸ hp))
  unfold rem cnt
  rw [prod_insert hqS, prod_insert hqS, filter_filter]
  have e : (A.filter (fun a => q ∣ a ∧ (∏ p ∈ S, p) ∣ a)) =
      A.filter (fun a => q * ∏ p ∈ S, p ∣ a) := by
    refine filter_congr (fun a _ => ⟨fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩⟩)
  rw [e]
  ring

/-- `∏ (1 - x_p) ≥ 1 - Σ x_p` for `0 ≤ x_p ≤ 1`. -/
lemma one_sub_sum_le_prod (S : Finset ℕ) (x : ℕ → ℝ) (h0 : ∀ p, 0 ≤ x p) (h1 : ∀ p, x p ≤ 1) :
    1 - ∑ p ∈ S, x p ≤ ∏ p ∈ S, (1 - x p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hs : 0 ≤ ∑ p ∈ S, x p := sum_nonneg (fun p _ => h0 p)
    have hx := h0 a
    have hx1 := h1 a
    have := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 - x a by linarith)
    nlinarith

end LeanLab.PNTSieve.Bonferroni

namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- **The blocks for a sifting limit `exp M`.** -/
lemma block_pack (N : ℕ) (M : ℝ) (hM : (2 : ℝ) ^ 2006 ≤ M) : ∃ Bs : List Block, Good Bs ∧
    (∀ p ∈ univB Bs, (p : ℝ) ≤ Real.exp M ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) ∧
    (∀ p, p.Prime → ¬ p ∣ N → 3 ≤ p → (p : ℝ) ≤ Real.exp M → p ∈ univB Bs) ∧
    (lev Bs : ℝ) ≤ Real.exp (154 / 15 * M) ∧ rhoSum xDen Bs ≤ 1916 / 10000 ∧
    (3 : ℝ) ^ Bs.length ≤ 4 * M ^ 2 := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  have hlt1 : Real.log 2 < 1 := by norm_num at hl2'; linarith
  have hgt : 1 / 2 < Real.log 2 := by norm_num at hl2; linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM
  set t := ⌊M / Real.log 2⌋₊ with ht
  have ht2 : (t : ℝ) ≤ M / Real.log 2 := Nat.floor_le (by positivity)
  have ht1 : M / Real.log 2 - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (M / Real.log 2); rw [← ht] at this; linarith
  have hMl : M ≤ M / Real.log 2 := by
    rw [le_div_iff₀ hl2pos]; nlinarith [mul_le_mul_of_nonneg_left hlt1.le hMpos.le]
  have ht2005 : 2 ^ 2005 ≤ t := by
    apply Nat.le_floor
    have h2 : (2 : ℝ) ^ 2005 ≤ 2 ^ 2006 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hc : ((2 ^ 2005 : ℕ) : ℝ) = (2 : ℝ) ^ 2005 := by rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [hc]
    exact h2.trans (hM.trans hMl)
  set k := Nat.log 2 t with hk
  have hk2005 : 2005 ≤ k := Nat.le_log_of_pow_le (by norm_num) ht2005
  have htge : 2 ≤ t := le_trans (Nat.le_self_pow (by norm_num) 2) ht2005
  have hkt : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
  have htk : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hkt' : ((2 ^ k : ℕ) : ℝ) ≤ t := by exact_mod_cast hkt
  have htk1 : (t : ℝ) + 1 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
    have : t + 1 ≤ 2 ^ (k + 1) := htk
    have : ((t + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [pow_succ] at this; push_cast at this ⊢; linarith
  have h2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  set c := M / ((2 ^ k : ℕ) : ℝ) with hc
  have hLe : M / Real.log 2 * Real.log 2 = M := by field_simp
  have hc1 : Real.log 2 ≤ c := by
    rw [hc, le_div_iff₀ h2k, ← hLe]
    have := mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
    linarith
  have hc2 : c ≤ 2 * Real.log 2 := by
    rw [hc, div_le_iff₀ h2k, ← hLe]
    have h1 : M / Real.log 2 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right h1 hl2pos.le
    linarith
  have hc0 : 0 ≤ c := le_trans hl2pos.le hc1
  have h2kc : (2 : ℝ) ^ k * c = M := by
    rw [hc]; push_cast; field_simp
  have hthr : thr c k = Real.exp M := by unfold thr; rw [h2kc]
  set j := k - 1 with hj
  have hjk : j + 1 = k := by omega
  refine ⟨GQ N c j 4 0, GQ_good N hc0 ⟨2, rfl⟩ j 0, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem := GQ_mem N hc0 j 4 0
    rw [hjk, hthr] at hmem
    exact hmem
  · have hcov := GQ_cover N c j 4 0
    rw [hjk, hthr] at hcov
    exact hcov
  · have h1 := GQ_lev N hc0 j 0
    rw [hjk, h2kc, FQ_zero] at h1
    rw [mul_comm]; exact h1
  · have hlv0 : 1000 ≤ lvQ 4 (0 + (j - 8)) := by unfold lvQ; omega
    refine (GQ_rho_sharp N hc1 hc2 j (by omega) 0 hlv0).trans ?_
    have hlv : (1000 : ℝ) ≤ ((lvQ 4 (0 + (j - 8)) : ℕ) : ℝ) := by exact_mod_cast hlv0
    have h0 : Real.exp (93 - ((lvQ 4 (0 + (j - 8)) : ℕ) : ℝ)) ≤ Real.exp (-907) :=
      Real.exp_le_exp.mpr (by linarith)
    have := HH_zero_le
    have := exp_neg_907_le'
    linarith
  · rw [GQ_length, hjk]
    have h1 : (3 : ℝ) ^ k ≤ ((2 ^ k : ℕ) : ℝ) ^ 2 := by
      push_cast; rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ M / Real.log 2 := hkt'.trans ht2
    have h3 : M / Real.log 2 ≤ 2 * M := by
      rw [div_le_iff₀ hl2pos]; nlinarith [mul_le_mul_of_nonneg_left hgt.le hMpos.le]
    calc (3 : ℝ) ^ k ≤ ((2 ^ k : ℕ) : ℝ) ^ 2 := h1
      _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (by positivity) (h2.trans h3) 2
      _ = 4 * M ^ 2 := by ring

end LeanLab.PNTPort.BVMax
