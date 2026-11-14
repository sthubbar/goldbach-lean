module

public import LeanLab.SchnirelmannGoldbach.S1.Setup

/-!
AI-written Lean code, Claude, 2026-10-16.
S1 main term: the Selberg bounding sum of the Goldbach sieve is at least
`(log z)^2 / (32 singProd n)`.
-/

@[expose] public section

open Finset
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace LeanLab.SchnirelmannGoldbach.S1

/-- Indicator of being coprime to `n`. -/
def chiN (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≠ 0 ∧ Nat.Coprime m n then 1 else 0, by simp⟩

lemma chiN_apply (n m : ℕ) : chiN n m = if m ≠ 0 ∧ Nat.Coprime m n then 1 else 0 := rfl

lemma chiN_nonneg (n m : ℕ) : 0 ≤ chiN n m := by
  rw [chiN_apply]; split_ifs <;> norm_num

lemma chiN_mult (n : ℕ) : (chiN n).IsMultiplicative := by
  refine ⟨by simp [chiN_apply], ?_⟩
  intro a b _
  simp only [chiN_apply]
  rw [ite_zero_mul_ite_zero, one_mul]
  apply if_congr _ rfl rfl
  rw [Nat.coprime_mul_iff_left]
  constructor
  · rintro ⟨h0, h1, h2⟩; exact ⟨⟨left_ne_zero_of_mul h0, h1⟩, right_ne_zero_of_mul h0, h2⟩
  · rintro ⟨⟨h0, h1⟩, h0', h2⟩; exact ⟨mul_ne_zero h0 h0', h1, h2⟩

/-- The divisor sum `∑_{i ∣ m} [i, n coprime]`. -/
def tauN (n : ℕ) : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ) * chiN n

lemma tauN_mult (n : ℕ) : (tauN n).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul (chiN_mult n)

lemma tauN_apply (n m : ℕ) : tauN n m = ∑ i ∈ m.divisors, chiN n i := by
  rw [tauN, ArithmeticFunction.coe_zeta_mul_apply]

lemma tauN_nonneg (n m : ℕ) : 0 ≤ tauN n m := by
  rw [tauN_apply]; exact sum_nonneg fun i _ => chiN_nonneg n i

lemma tauN_prime_pow_le {n p : ℕ} (hp : p.Prime) (k : ℕ) : tauN n (p ^ k) ≤ wt n p ^ k := by
  rw [tauN_apply, Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  by_cases hpn : p ∣ n
  · have : ∀ j ∈ range (k + 1), chiN n (p ^ j) = if j = 0 then 1 else 0 := by
      intro j _
      rw [chiN_apply]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · rw [if_neg (Nat.pos_iff_ne_zero.mp hj)]
        rw [if_neg]
        rintro ⟨_, hc⟩
        rw [Nat.coprime_pow_left_iff hj] at hc
        exact (hp.coprime_iff_not_dvd.mp hc) hpn
    rw [sum_congr rfl this, sum_ite_eq']
    simp [wt, hpn]
  · have : ∀ j ∈ range (k + 1), chiN n (p ^ j) = 1 := by
      intro j _
      rw [chiN_apply, if_pos]
      exact ⟨pow_ne_zero _ hp.ne_zero, Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr hpn)⟩
    rw [sum_congr rfl this]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one, wt, hpn, if_false]
    have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    exact_mod_cast this

lemma tauN_le_rhoN (n : ℕ) {m : ℕ} (hm : m ≠ 0) : tauN n m ≤ rhoN n m := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ (tauN_mult n) hm,
    rhoN_apply hm, Finsupp.prod, Finsupp.prod]
  apply prod_le_prod₀
  · intro p _; exact tauN_nonneg n _
  · intro p hp
    rw [Nat.support_factorization] at hp
    exact tauN_prime_pow_le (Nat.prime_of_mem_primeFactors hp) _

/-- Dirichlet hyperbola, lower half: products of short harmonic sums. -/
lemma sum_tauN_ge (n : ℕ) {Y M : ℕ} (hYM : Y * Y ≤ M) :
    (∑ a ∈ Icc 1 Y, (1 : ℝ) / a) * (∑ b ∈ Icc 1 Y, chiN n b / b) ≤
      ∑ m ∈ Icc 1 M, tauN n m / m := by
  rw [sum_mul_sum, ← sum_product']
  simp_rw [tauN_apply, sum_div]
  rw [← sum_sigma (Icc 1 M) (fun m => m.divisors) (fun x => chiN n x.2 / x.1)]
  apply sum_le_sum_of_injOn (fun x : ℕ × ℕ => (⟨x.1 * x.2, x.2⟩ : Σ _ : ℕ, ℕ))
  · intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_Icc] at hx hy
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have h1' : x.1 = y.1 := by
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_right (by omega) h1
    exact Prod.ext h1' h2
  · intro σ hσ
    simp only [mem_image, mem_product, mem_Icc] at hσ
    obtain ⟨x, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩ := hσ
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega)),
      (Nat.mul_le_mul h2 h4).trans hYM⟩, Nat.dvd_mul_left _ _, mul_ne_zero (by omega) (by omega)⟩
  · intro x _
    simp only [Nat.cast_mul]
    exact le_of_eq (by ring)
  · intro σ _ _
    exact div_nonneg (chiN_nonneg n _) (Nat.cast_nonneg _)

/-- Removing the multiples of one more prime loses at most a factor `1 - 1/p`. -/
lemma harmonic_avoid_step (Y : ℕ) (Q : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * ∑ b ∈ Icc 1 Y with ∀ q ∈ Q, ¬ q ∣ b, (1 : ℝ) / b ≤
      ∑ b ∈ Icc 1 Y with ∀ q ∈ insert p Q, ¬ q ∣ b, (1 : ℝ) / b := by
  set A := {b ∈ Icc 1 Y | ∀ q ∈ Q, ¬ q ∣ b}
  set A' := {b ∈ Icc 1 Y | ∀ q ∈ insert p Q, ¬ q ∣ b}
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hx1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
  have key : ∑ b ∈ A, (1 : ℝ) / b ≤
      ∑ x ∈ range (Y + 1) ×ˢ A', (1 : ℝ) / ((p : ℝ) ^ x.1 * x.2) := by
    apply sum_le_sum_of_injOn (fun b => (b.factorization p, b / p ^ b.factorization p))
    · intro a ha b hb hab
      simp only [Prod.mk.injEq] at hab
      have h1 := Nat.ordProj_mul_ordCompl_eq_self a p
      have h2 := Nat.ordProj_mul_ordCompl_eq_self b p
      rw [hab.2, hab.1] at h1
      exact h1.symm.trans h2
    · intro x hx
      simp only [mem_image] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      simp only [A, mem_filter, mem_Icc] at hb
      obtain ⟨⟨hb1, hbY⟩, hbQ⟩ := hb
      have hb0 : b ≠ 0 := by omega
      simp only [A', mem_product, mem_range, mem_filter, mem_Icc, mem_insert, forall_eq_or_imp]
      have hcl := Nat.ordCompl_le b p
      have hclpos : 0 < b / p ^ b.factorization p := Nat.ordCompl_pos p hb0
      refine ⟨?_, ⟨by omega, by omega⟩, Nat.not_dvd_ordCompl hp hb0, fun q hq h => ?_⟩
      · have h1 := Nat.ordProj_le p hb0
        have h2 : b.factorization p < p ^ b.factorization p := Nat.lt_pow_self hp.one_lt
        omega
      · exact hbQ q hq (h.trans (Nat.ordCompl_dvd b p))
    · intro b hb
      simp only [A, mem_filter, mem_Icc] at hb
      have hb0 : b ≠ 0 := by omega
      apply le_of_eq
      congr 1
      have := Nat.ordProj_mul_ordCompl_eq_self b p
      exact_mod_cast this.symm
    · intro x _ _
      have : (0 : ℝ) ≤ (p : ℝ) ^ x.1 * x.2 := by positivity
      positivity
  have hsplit : ∑ x ∈ range (Y + 1) ×ˢ A', (1 : ℝ) / ((p : ℝ) ^ x.1 * x.2) =
      (∑ k ∈ range (Y + 1), (1 / (p : ℝ)) ^ k) * ∑ b ∈ A', (1 : ℝ) / b := by
    rw [sum_product, sum_mul]
    apply sum_congr rfl
    intro k _
    rw [mul_sum]
    apply sum_congr rfl
    intro b _
    rw [div_pow, one_pow]; field_simp
  have hgeom : ∑ k ∈ range (Y + 1), (1 / (p : ℝ)) ^ k ≤ 1 / (1 - 1 / p) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := Y + 1) hx0 hx1
    simpa using this
  have hA'0 : 0 ≤ ∑ b ∈ A', (1 : ℝ) / b := sum_nonneg fun b _ => by positivity
  have hpos : 0 < 1 - 1 / (p : ℝ) := by linarith
  calc (1 - 1 / (p : ℝ)) * ∑ b ∈ A, (1 : ℝ) / b
      ≤ (1 - 1 / (p : ℝ)) * ((1 / (1 - 1 / p)) * ∑ b ∈ A', (1 : ℝ) / b) := by
        gcongr
        calc _ ≤ _ := key
          _ = _ := hsplit
          _ ≤ _ := mul_le_mul_of_nonneg_right hgeom hA'0
    _ = ∑ b ∈ A', (1 : ℝ) / b := by rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul]

lemma harmonic_avoid (Y : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) :
    (∏ q ∈ Q, (1 - 1 / (q : ℝ))) * ∑ b ∈ Icc 1 Y, (1 : ℝ) / b ≤
      ∑ b ∈ Icc 1 Y with ∀ q ∈ Q, ¬ q ∣ b, (1 : ℝ) / b := by
  induction Q using Finset.induction_on with
  | empty => simp
  | insert p Q hpQ ih =>
    have hp := hQ p (mem_insert_self p Q)
    have ih' := ih fun q hq => hQ q (mem_insert_of_mem hq)
    rw [prod_insert hpQ, mul_assoc]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have h0 : 0 ≤ 1 - 1 / (p : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hp1
    calc _ ≤ (1 - 1 / (p : ℝ)) * ∑ b ∈ Icc 1 Y with ∀ q ∈ Q, ¬ q ∣ b, (1 : ℝ) / b := by gcongr
      _ ≤ _ := harmonic_avoid_step Y Q hp

lemma sum_chiN_eq (n : ℕ) (hn : n ≠ 0) (Y : ℕ) :
    ∑ b ∈ Icc 1 Y, chiN n b / b =
      ∑ b ∈ Icc 1 Y with ∀ q ∈ n.primeFactors, ¬ q ∣ b, (1 : ℝ) / b := by
  rw [sum_filter]
  apply sum_congr rfl
  intro b hb
  simp only [mem_Icc] at hb
  rw [chiN_apply]
  have key : (b ≠ 0 ∧ Nat.Coprime b n) ↔ ∀ q ∈ n.primeFactors, ¬ q ∣ b := by
    constructor
    · rintro ⟨_, hc⟩ q hq hqb
      rw [Nat.mem_primeFactors] at hq
      have : Nat.Coprime q n := Nat.Coprime.coprime_dvd_left hqb hc
      exact (hq.1.coprime_iff_not_dvd.mp this) hq.2.1
    · intro h
      refine ⟨by omega, Nat.coprime_of_dvd fun k hk hkb hkn => h k ?_ hkb⟩
      exact Nat.mem_primeFactors.mpr ⟨hk, hkn, hn⟩
  by_cases h : ∀ q ∈ n.primeFactors, ¬ q ∣ b
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (mt key.mp h), if_neg h, zero_div]

/-- Closed form of the telescoping product `∏_{k=2}^{M+1} (1 - 1/k^2)`. -/
lemma prod_range_one_sub_inv_sq (M : ℕ) :
    ∏ k ∈ range M, (1 - 1 / ((k : ℝ) + 2) ^ 2) = ((M : ℝ) + 2) / (2 * ((M : ℝ) + 1)) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [prod_range_succ, ih]
    push_cast
    field_simp
    ring

lemma prod_one_sub_inv_sq_ge (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    1 / 2 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) := by
  set M := s.sup id
  set t := (range M).image (· + 2)
  have hst : s ⊆ t := by
    intro p hp
    have hpM : p ≤ M := Finset.le_sup (f := id) hp
    have := hs p hp
    simp only [t, mem_image, mem_range]
    exact ⟨p - 2, by omega, by omega⟩
  have hf0 : ∀ k : ℕ, 1 ≤ k → 0 ≤ 1 - 1 / (k : ℝ) ^ 2 := by
    intro k hk
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  have hf1 : ∀ k : ℕ, 1 - 1 / (k : ℝ) ^ 2 ≤ 1 := by
    intro k
    have : 0 ≤ 1 / (k : ℝ) ^ 2 := by positivity
    linarith
  have ht : ∏ p ∈ t, (1 - 1 / (p : ℝ) ^ 2) = ((M : ℝ) + 2) / (2 * ((M : ℝ) + 1)) := by
    rw [prod_image (by intro a _ b _ h; simpa using h), ← prod_range_one_sub_inv_sq M]
    push_cast; rfl
  have hsd := prod_sdiff (f := fun p : ℕ => (1 - 1 / (p : ℝ) ^ 2)) hst
  have hle1 : ∏ p ∈ t \ s, (1 - 1 / (p : ℝ) ^ 2) ≤ 1 := prod_le_one₀
    (fun k hk => hf0 k (by
      simp only [t, mem_sdiff, mem_image] at hk; obtain ⟨⟨j, _, rfl⟩, _⟩ := hk; omega))
    (fun k _ => hf1 k)
  have hs0 : 0 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) :=
    prod_nonneg fun k hk => hf0 k (by have := hs k hk; omega)
  have hM : (1 : ℝ) / 2 ≤ ((M : ℝ) + 2) / (2 * ((M : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  calc (1 : ℝ) / 2 ≤ ∏ p ∈ t, (1 - 1 / (p : ℝ) ^ 2) := ht ▸ hM
    _ = (∏ p ∈ t \ s, (1 - 1 / (p : ℝ) ^ 2)) * ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) := hsd.symm
    _ ≤ 1 * ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hle1 hs0
    _ = _ := one_mul _

lemma singProd_pos (n : ℕ) : 0 < singProd n :=
  prod_pos fun p _ => by positivity

lemma prod_one_sub_inv_ge (n : ℕ) :
    1 / (2 * singProd n) ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hsp := singProd_pos n
  have h := prod_one_sub_inv_sq_ge n.primeFactors fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have heq : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) =
      (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))) * singProd n := by
    rw [singProd, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    ring
  rw [heq] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Main term.** The Selberg bounding sum of the Goldbach sieve is `≫ log² z / singProd n`. -/
theorem boundingSum_gSieve_ge (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) (z : ℝ) (hz : 1 ≤ z) :
    Real.log z ^ 2 / (32 * singProd n) ≤ selbergBoundingSum (gSieve n hn z hz) := by
  have hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (gSieve n hn z hz).level →
      p ∣ (gSieve n hn z hz).prodPrimes := by
    intro p hp hpz
    show p ∣ primorial ⌊z⌋₊
    rw [prime_dvd_primorial_iff _ _ hp]
    exact Nat.le_floor hpz
  have hA := selbergBoundingSum_ge_sum_div (gSieve n hn z hz) hP (nuN_compMult n) (nuN_nonneg n)
    (fun p hp _ => nuN_lt_one hn hp)
  change ∑ m ∈ Icc 1 ⌊√z⌋₊, nuN n m ≤ selbergBoundingSum (gSieve n hn z hz) at hA
  set y := √(√z) with hy
  set Y := ⌊y⌋₊
  set M := ⌊√z⌋₊
  have hsz : 1 ≤ √z := Real.one_le_sqrt.mpr hz
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr hsz
  have hYM : Y * Y ≤ M := by
    apply Nat.le_floor
    have hY : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
    push_cast
    calc (Y : ℝ) * Y ≤ y * y := mul_le_mul hY hY hY0 (by linarith)
      _ = √z := Real.mul_self_sqrt (by positivity)
  have h1 : ∑ m ∈ Icc 1 M, tauN n m / m ≤ ∑ m ∈ Icc 1 M, nuN n m := by
    apply sum_le_sum
    intro m hm
    simp only [mem_Icc] at hm
    rw [nuN_apply]
    exact div_le_div_of_nonneg_right (tauN_le_rhoN n (by omega)) (Nat.cast_nonneg _)
  have h2 := sum_tauN_ge n hYM
  have hlogy : Real.log y = Real.log z / 4 := by
    rw [hy, Real.log_sqrt (by positivity), Real.log_sqrt (by linarith)]; ring
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have h3 : Real.log y ≤ ∑ a ∈ Icc 1 Y, (1 : ℝ) / a := by
    simp_rw [one_div]
    exact LeanLab.PNTSieve.Aux.log_le_sum_inv y hy1
  have h4 : 1 / (2 * singProd n) * Real.log y ≤ ∑ b ∈ Icc 1 Y, chiN n b / b := by
    rw [sum_chiN_eq n hn0]
    refine le_trans ?_ (harmonic_avoid Y n.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp)
    apply mul_le_mul (prod_one_sub_inv_ge n) h3 hlogy0
    exact prod_nonneg fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).one_lt
      have : (1 : ℝ) < p := by exact_mod_cast this
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hsp := singProd_pos n
  have hc0 : 0 ≤ 1 / (2 * singProd n) * Real.log y := by positivity
  calc Real.log z ^ 2 / (32 * singProd n)
      = Real.log y * (1 / (2 * singProd n) * Real.log y) := by
        rw [hlogy]; field_simp; ring
    _ ≤ (∑ a ∈ Icc 1 Y, (1 : ℝ) / a) * (∑ b ∈ Icc 1 Y, chiN n b / b) :=
        mul_le_mul h3 h4 hc0 (hlogy0.trans h3)
    _ ≤ _ := h2.trans (h1.trans hA)

end LeanLab.SchnirelmannGoldbach.S1
