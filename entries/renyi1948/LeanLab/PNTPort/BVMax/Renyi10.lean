module

public import LeanLab.PNTPort.BVMax.Renyi14

/-!
# Rényi's theorem with `K = 10`: Kuhn weights on the Buchstab step

Unit U-6757, CLOUD 20261020T2317Z-cloud53. AI wrote the Lean code. Known mathematics, Kuhn's
weighted sieve in its simplest form, Kuhn 1954; Rényi 1948 for some K, Pan K = 4, Chen K = 2.

`Renyi14.lean` subtracts every element with a prime factor in `(z, y]` with weight 1. Here each
element `a` sifted to `z = N^{1/21}` gets weight `1 - (1/5) #{q ∈ Q : q ∣ a}`, `Q` the primes
`q ∤ N` in `(z, y]`, `y = N^{11/95}`:

* `omega_split`: if `D` is the set of the primes of `Q` dividing `a`, no square of one divides
  `a`, and every prime factor up to `y` lies in `D`, then `(z + 1)^{|D|} (y + 1)^{Ω(a) - |D|} ≤ a`;
  so `Ω(a) ≥ 11` forces `|D| ≥ 5`, since `4/21 + 7 · 11/95 > 1`, and the weight is `≤ 0`;
* the elements with `q² ∣ a` for some `q ∈ Q` number at most `2N/(z + 1)`;
* the weighted sum is `S(A, z) - (1/5) Σ_q #{a sifted, q ∣ a}`, and the upper block sieve at
  `w = N^{2/55}` bounds each term, level `N^{11/95 + (154/15)(2/55)} = N^{0.4892}`;
* the lab's block Mertens bounds give `Σ_q 1/(q - 1) ≤ 1.432`, `Σ_{w < p ≤ z} 1/(p - 1) ≤ 0.3097`,
  so the subtracted part is at most `(1/5) 1.2395 · 1.432/0.6903 < 0.515` of `X V_z` against
  `0.6168`; margin `1/10`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

lemma cardFactors_prod_primes (D : Finset ℕ) (hD : ∀ q ∈ D, q.Prime) :
    ArithmeticFunction.cardFactors (∏ q ∈ D, q) = D.card := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    have hp := hD a (mem_insert_self a D)
    have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
    rw [ArithmeticFunction.cardFactors_mul hp.ne_zero
      (prod_ne_zero_iff.mpr (fun q hq => (hD' q hq).ne_zero)),
      ArithmeticFunction.cardFactors_apply_prime hp, ih hD']
    ring

/-- **Splitting off the middle primes.** -/
lemma omega_split (a : ℕ) (ha : a ≠ 0) (D : Finset ℕ) (hD : ∀ q ∈ D, q.Prime ∧ q ∣ a)
    (hsq : ∀ q ∈ D, ¬ q ^ 2 ∣ a) (Y : ℕ) (hsmall : ∀ r, r.Prime → r ∣ a → r ≤ Y → r ∈ D)
    (Z : ℕ) (hZ : ∀ q ∈ D, Z ≤ q) :
    D.card ≤ ArithmeticFunction.cardFactors a ∧
    Z ^ D.card * (Y + 1) ^ (ArithmeticFunction.cardFactors a - D.card) ≤ a := by
  classical
  have hgd : (∏ q ∈ D, q) ∣ a :=
    Finset.prod_primes_dvd a (fun q hq => (hD q hq).1.prime) (fun q hq => (hD q hq).2)
  obtain ⟨h, hh⟩ := hgd
  set g := ∏ q ∈ D, q with hg
  have hg0 : g ≠ 0 := by rw [hh] at ha; exact left_ne_zero_of_mul ha
  have hh0 : h ≠ 0 := by rw [hh] at ha; exact right_ne_zero_of_mul ha
  have hΩ : ArithmeticFunction.cardFactors a = D.card + ArithmeticFunction.cardFactors h := by
    rw [hh, ArithmeticFunction.cardFactors_mul hg0 hh0, hg,
      cardFactors_prod_primes D (fun q hq => (hD q hq).1)]
  have hbig : ∀ r ∈ h.primeFactorsList, Y + 1 ≤ r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactorsList hr
    have hrd := Nat.dvd_of_mem_primeFactorsList hr
    by_contra hlt
    push Not at hlt
    have hra : r ∣ a := by rw [hh]; exact dvd_mul_of_dvd_right hrd g
    have hrD := hsmall r hrp hra (by omega)
    have hrg : r ∣ g := Finset.dvd_prod_of_mem _ hrD
    exact hsq r hrD (by rw [hh, pow_two]; exact mul_dvd_mul hrg hrd)
  have h1 := pow_bigOmega_le h (Y + 1) hh0 hbig
  have h2 : Z ^ D.card ≤ g := Finset.pow_card_le_prod D (fun q => q) Z (fun q hq => hZ q hq)
  rw [hΩ, Nat.add_sub_cancel_left, hh]
  exact ⟨Nat.le_add_right _ _, Nat.mul_le_mul h2 h1⟩

lemma big_aux10 (ℓ : ℝ) (h : (2 : ℝ) ^ 2100 ≤ ℓ) :
    (2 : ℝ) ^ 2006 ≤ ℓ / 21 ∧ (2 : ℝ) ^ 2006 ≤ 2 * ℓ / 55 ∧ (10 : ℝ) ^ 30 ≤ ℓ := by
  have e : (2 : ℝ) ^ 2100 = 2 ^ 94 * 2 ^ 2006 := by rw [← pow_add]
  rw [e] at h
  clear e
  have h94 : (28 : ℝ) ≤ 2 ^ 94 :=
    calc (28 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ 94 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h20 : (10 : ℝ) ^ 30 ≤ 2 ^ 2006 :=
    calc (10 : ℝ) ^ 30 ≤ 2 ^ 100 := by norm_num
      _ ≤ 2 ^ 2006 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  generalize (2 : ℝ) ^ 2006 = A at *
  generalize (2 : ℝ) ^ 94 = C at *
  have hA : 0 ≤ A := le_trans (by norm_num) h20
  have hm := mul_le_mul_of_nonneg_right h94 hA
  refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma exp_36_le : Real.exp 36 ≤ 10 ^ 18 := by
  have h1 : Real.exp 36 = Real.exp 1 ^ 36 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  calc Real.exp 1 ^ 36 ≤ 3 ^ 36 := pow_le_pow_left₀ (Real.exp_pos 1).le h2 36
    _ ≤ 10 ^ 18 := by norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **Rényi with `K = 10`, deterministic core with the count**, Kuhn weights `1 - (1/5) #{q ∣ a}`. -/
theorem renyi10_count {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (hE : Even N) (hℓ6 : (2 : ℝ) ^ 2100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : 100 * |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 10)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨hLbig0, hL2big0, h10⟩ := big_aux10 ℓ hℓ6
  clear hℓ6
  obtain ⟨Bs, hG, hmem, hcov, hlev, hρ, h3k⟩ := block_pack N (ℓ / 21) hLbig0
  obtain ⟨Cs, hG', hmem', hcov', hlev', hρ', -⟩ := block_pack N (2 * ℓ / 55) hL2big0
  clear hLbig0 hL2big0
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN38 : (38 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  -- the three limits
  set L := ℓ / 21 with hL
  set L2 := 2 * ℓ / 55 with hL2
  have hL10 : (10 ^ 4 : ℝ) ≤ L2 := by linarith
  obtain ⟨hz3, hzr, hz1, hlogz1, hlogz2, hlogz3⟩ := floor_exp_facts L (by linarith)
  obtain ⟨hw3, hwr, hw1, hlogw1, hlogw2, -⟩ := floor_exp_facts L2 (by linarith)
  obtain ⟨hy3, hyr, hy1, hlogy1, hlogy2, hlogy3⟩ := floor_exp_facts (11 * ℓ / 95) (by linarith)
  set z := ⌊Real.exp L⌋₊ with hz
  set w := ⌊Real.exp L2⌋₊ with hw
  set y := ⌊Real.exp (11 * ℓ / 95)⌋₊ with hy
  have hL2L : L2 ≤ L := by linarith
  have hLy : L ≤ 11 * ℓ / 95 := by linarith
  have hwz : w ≤ z := Nat.floor_le_floor (Real.exp_le_exp.mpr hL2L)
  have hzy : z ≤ y := Nat.floor_le_floor (Real.exp_le_exp.mpr hLy)
  set Ω := univB Bs with hΩ
  set Ω' := univB Cs with hΩ'
  set Q := (Ioc z y).filter (fun q => q.Prime ∧ ¬ q ∣ N) with hQ
  have hsubΩ : Ω' ⊆ Ω := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem' p hp
    exact hcov p h2 h3 h4 (h1.trans (Real.exp_le_exp.mpr hL2L))
  have hΩ'z : ∀ p ∈ Ω', p ≤ z := fun p hp =>
    Nat.le_floor (((hmem' p hp).1).trans (Real.exp_le_exp.mpr hL2L))
  have hQmem : ∀ q ∈ Q, z < q ∧ q ≤ y ∧ q.Prime ∧ ¬ q ∣ N := by
    intro q hq
    rw [hQ, mem_filter, mem_Ioc] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  -- the sequence
  set A := goldbachSeq N with hAdef
  set X := liD ((N - 1 : ℕ) : ℝ) with hXdef
  have hX : 0 ≤ X := by
    rw [hXdef]; unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have hlevel : ∀ e : ℝ, e ≤ 49 / 100 * ℓ → ∀ n : ℕ, (n : ℝ) ≤ Real.exp e →
      n ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := fun e he n hn =>
    Nat.le_floor (hn.trans ((Real.exp_le_exp.mpr he).trans hE2))
  -- the lower sieve
  have hρ5 : rhoSum xDen Bs ≤ 1 / 5 := hρ.trans (by norm_num)
  have hρ'5 : rhoSum xDen Cs ≤ 1 / 5 := hρ'.trans (by norm_num)
  have hlow := blocks_main_rel5 A Bs hG xDen xDen_nonneg xDen_lt_one X hX hρ5
  have hlowR := hR Ω (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.1, (hmem p hp).2.2.2⟩)
    (Ω.powerset.filter (fun S => cL Bs S ≠ 0)) (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      refine (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans
        (hlevel (154 / 15 * L) (by linarith) _ hlev))
  -- the upper sieves
  set F' := Ω'.powerset.filter (fun S => cU Cs S ≠ 0) with hF'
  have hup : ∀ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) ≤
      X * xDen q * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) +
        ∑ S ∈ F', |rem A xDen X (insert q S)| := by
    intro q hq
    obtain ⟨hzq, -, hqp, -⟩ := hQmem q hq
    have h := blocks_upper_rel5 (A.filter (fun a => q ∣ a)) Cs hG' xDen xDen_nonneg xDen_lt_one
      (X * xDen q) (mul_nonneg hX (xDen_nonneg q)) hρ'5
    refine h.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl (fun S hS => ?_)
    rw [hF', mem_filter, mem_powerset] at hS
    rw [rem_filter_dvd A xDen X hqp S (fun p hp => (hmem' p (hS.1 hp)).2.1)
      (fun hqS => by have := hΩ'z q (hS.1 hqS); omega)]
  set G := (Q ×ˢ F').image (fun qs => insert qs.1 qs.2) with hGdef
  have hinj : Set.InjOn (fun qs : ℕ × Finset ℕ => insert qs.1 qs.2) ↑(Q ×ˢ F') := by
    rintro ⟨q1, S1⟩ h1 ⟨q2, S2⟩ h2 he
    simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
    simp only at he
    have hS1 : S1 ⊆ Ω' := mem_powerset.mp (mem_filter.mp h1.2).1
    have hS2 : S2 ⊆ Ω' := mem_powerset.mp (mem_filter.mp h2.2).1
    have hq1 := (hQmem q1 h1.1).1
    have hq2 := (hQmem q2 h2.1).1
    have hn1 : q1 ∉ S1 := fun h => by have := hΩ'z q1 (hS1 h); omega
    have hn2 : q2 ∉ S2 := fun h => by have := hΩ'z q2 (hS2 h); omega
    have hq : q1 = q2 := by
      have : q1 ∈ insert q2 S2 := by rw [← he]; exact mem_insert_self q1 S1
      rcases mem_insert.mp this with h | h
      · exact h
      · exact absurd (hΩ'z q1 (hS2 h)) (by omega)
    subst hq
    have e1 := erase_insert hn1
    have e2 := erase_insert hn2
    rw [he] at e1
    rw [e1] at e2
    rw [Prod.mk.injEq]
    exact ⟨rfl, e2⟩
  have hGR : ∑ T ∈ G, |rem A xDen X T| ≤ K * N / ℓ ^ (5 : ℝ) := by
    refine hR (Ω' ∪ Q) (fun p hp => ?_) G ?_ ?_
    · rcases mem_union.mp hp with h | h
      · exact ⟨(hmem' p h).2.1, (hmem' p h).2.2.1, (hmem' p h).2.2.2⟩
      · obtain ⟨h1, -, h3, h4⟩ := hQmem p h
        exact ⟨h3, h4, by omega⟩
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω' := mem_powerset.mp (mem_filter.mp hqS.2).1
      rw [mem_powerset]
      intro p hp
      rcases mem_insert.mp hp with h | h
      · exact mem_union_right _ (h ▸ hqS.1)
      · exact mem_union_left _ (hS h)
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω' := mem_powerset.mp (mem_filter.mp hqS.2).1
      have hcU : cU Cs S ≠ 0 := (mem_filter.mp hqS.2).2
      obtain ⟨hzq, hqy, -, -⟩ := hQmem q hqS.1
      have hn : q ∉ S := fun h => by have := hΩ'z q (hS h); omega
      simp only
      rw [prod_insert hn]
      have hSl := support_prod Cs hG' S hS (Or.inr hcU)
      apply hlevel (11 * ℓ / 95 + 154 / 15 * L2) (by linarith)
      rw [Real.exp_add]
      push_cast
      have hqr : (q : ℝ) ≤ Real.exp (11 * ℓ / 95) :=
        le_trans (by exact_mod_cast hqy) hyr
      have hSr : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.exp (154 / 15 * L2) :=
        le_trans (by exact_mod_cast hSl) hlev'
      push_cast at hSr
      exact mul_le_mul hqr hSr (by positivity) (Real.exp_pos _).le
  have hupsum : ∑ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) ≤
      X * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q +
        K * N / ℓ ^ (5 : ℝ) := by
    refine (sum_le_sum hup).trans ?_
    rw [sum_add_distrib]
    have e1 : ∑ q ∈ Q, X * xDen q * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) =
        X * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q := by
      rw [mul_sum]; refine sum_congr rfl (fun q _ => by ring)
    have e2 : ∑ q ∈ Q, ∑ S ∈ F', |rem A xDen X (insert q S)| = ∑ T ∈ G, |rem A xDen X T| := by
      rw [hGdef, sum_image hinj, sum_product]
    rw [e1, e2]
    linarith
  -- the densities
  set V := ∏ p ∈ Ω, (1 - xDen p) with hVdef
  set W := ∏ p ∈ Ω', (1 - xDen p) with hWdef
  have hW0 : 0 ≤ W := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hsw : ∑ p ∈ Ω \ Ω', xDen p ≤ 3097 / 10000 := by
    have h := xDen_block w z (by omega) hwz (Ω \ Ω') (fun p hp => by
      rw [mem_sdiff] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hmem p hp.1
      refine ⟨h2, ?_, Nat.le_floor h1⟩
      by_contra hc
      push Not at hc
      exact hp.2 (hcov' p h2 h3 h4 ((show (p : ℝ) ≤ w by exact_mod_cast hc).trans hwr)))
    refine h.trans ?_
    have hw0 : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    have hlw : 0 < Real.log w := by linarith
    have hfrac : (Real.log z - Real.log w + 14) / Real.log w ≤ 3096 / 10000 := by
      rw [div_le_iff₀ hlw]
      linarith
    have hw6 : (Real.exp L2) - 1 ≤ w := by linarith
    have hwbig : (10000 : ℝ) ≤ w := by
      have := Real.add_one_le_exp L2
      linarith
    have hinv : 1 / (w : ℝ) ≤ 1 / 10000 := one_div_le_one_div_of_le (by norm_num) hwbig
    have hfrac0 : 0 ≤ (Real.log z - Real.log w + 14) / Real.log w := by
      apply div_nonneg _ hlw.le
      have := Real.log_le_log (by linarith) (show (w : ℝ) ≤ z by exact_mod_cast hwz)
      linarith
    nlinarith
  have hsw0 : 0 ≤ ∑ p ∈ Ω \ Ω', xDen p := sum_nonneg (fun p _ => xDen_nonneg p)
  have hVW : W * (6903 / 10000) ≤ V := by
    have e : (∏ p ∈ Ω \ Ω', (1 - xDen p)) * W = V := prod_sdiff hsubΩ
    have h1 := one_sub_sum_le_prod (Ω \ Ω') xDen xDen_nonneg xDen_le_one
    have hP : (6903 / 10000 : ℝ) ≤ ∏ p ∈ Ω \ Ω', (1 - xDen p) := by linarith
    have := mul_le_mul_of_nonneg_left hP hW0
    calc W * (6903 / 10000) ≤ W * ∏ p ∈ Ω \ Ω', (1 - xDen p) := this
      _ = V := by rw [← e]; ring
  have hsQ : ∑ q ∈ Q, xDen q ≤ 1432 / 1000 := by
    have h := xDen_block z y (by omega) hzy Q (fun q hq => by
      obtain ⟨h1, h2, h3, -⟩ := hQmem q hq
      exact ⟨h3, h1, h2⟩)
    refine h.trans ?_
    have hlz : 0 < Real.log z := by linarith
    have hfrac : (Real.log y - Real.log z + 14) / Real.log z ≤ 14317 / 10000 := by
      rw [div_le_iff₀ hlz]
      linarith
    have hzbig : (10000 : ℝ) ≤ z := by
      have := Real.add_one_le_exp L
      linarith
    have hinv : 1 / (z : ℝ) ≤ 1 / 10000 := one_div_le_one_div_of_le (by norm_num) hzbig
    have hfrac0 : 0 ≤ (Real.log y - Real.log z + 14) / Real.log z := by
      apply div_nonneg _ hlz.le
      have := Real.log_le_log (by linarith) (show (z : ℝ) ≤ y by exact_mod_cast hzy)
      linarith
    nlinarith
  have hsQ0 : 0 ≤ ∑ q ∈ Q, xDen q := sum_nonneg (fun p _ => xDen_nonneg p)
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hρ'0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Cs
  -- the main term
  have hsubtr : X * W * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q ≤
      X * V * (2575 / 1000) := by
    have h1 : (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q ≤ (12395 / 10000) * (1432 / 1000) :=
      mul_le_mul (by linarith) hsQ hsQ0 (by norm_num)
    have h2 : W * ((1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q) ≤
        W * ((12395 / 10000) * (1432 / 1000)) := mul_le_mul_of_nonneg_left h1 hW0
    have h3 : W * ((12395 / 10000) * (1432 / 1000)) ≤ V * (2575 / 1000) := by linarith
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hX
    calc X * W * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q
        = X * (W * ((1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q)) := by ring
      _ ≤ X * (V * (2575 / 1000)) := h4
      _ = X * V * (2575 / 1000) := by ring
  have hV0 : 0 ≤ V := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hXV0 : 0 ≤ X * V := mul_nonneg hX hV0
  have hlowmain : X * V * (6168 / 10000) ≤ X * V * (1 - 2 * rhoSum xDen Bs) :=
    mul_le_mul_of_nonneg_left (by linarith) hXV0
  -- absolute size of X V
  have hV2 : Real.exp (-36) * 21 / ℓ ≤ V := by
    have hV := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz3 Ω
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, Nat.le_floor (hmem p hp).1⟩)
    have hV' : Real.exp (-36) / Real.log z ≤ V := by
      refine hV.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
      simp only [xDen, if_pos (hmem p hp).2.2.2]
    refine le_trans ?_ hV'
    have hlz : 0 < Real.log z := by linarith
    rw [div_le_div_iff₀ hℓpos hlz]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 21 ≤ ℓ := by linarith
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hXV : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 21 / ℓ) ≤ X * V :=
    mul_le_mul hliD hV2 (by positivity) hX
  have hXV2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 21 / ℓ) =
      21 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    ring
  have hXV' : 21 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) ≤ X * V := hXV2 ▸ hXV
  -- errors
  have h5r : ℓ ^ (5 : ℝ) = ℓ ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hKN : K * N / ℓ ^ (5 : ℝ) ≤ |K| * N / ℓ ^ 5 := by
    rw [h5r]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hNpos.le)
      (by positivity)
  have hK0 : 0 ≤ |K| * N / ℓ ^ 5 := by positivity
  have herr : ((3 : ℝ) ^ Bs.length + 1) * (|K| * N / ℓ ^ 5) ≤ |K| * N / ℓ ^ (3 : ℝ) := by
    rw [h3r]
    have h1 : (3 : ℝ) ^ Bs.length + 1 ≤ ℓ ^ 2 := by
      have : 4 * L ^ 2 + 1 ≤ ℓ ^ 2 := by rw [hL]; nlinarith
      linarith
    calc ((3 : ℝ) ^ Bs.length + 1) * (|K| * N / ℓ ^ 5) ≤ ℓ ^ 2 * (|K| * N / ℓ ^ 5) :=
          mul_le_mul_of_nonneg_right h1 hK0
      _ = |K| * N / ℓ ^ 3 := by field_simp
  have hlow3 : (3 : ℝ) ^ Bs.length *
      ∑ S ∈ Ω.powerset.filter (fun S => cL Bs S ≠ 0), |rem A xDen X S| ≤
      (3 : ℝ) ^ Bs.length * (|K| * N / ℓ ^ 5) :=
    mul_le_mul_of_nonneg_left (hlowR.trans hKN) (by positivity)
  -- the sifted set and the weight
  set Sz := A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a) with hSz
  have hcardSz : (sifted A Ω : ℝ) = (Sz.card : ℝ) := by simp [sifted, hSz]
  have hswap : ∑ a ∈ Sz, ((Q.filter (fun q => q ∣ a)).card : ℝ) =
      ∑ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) := by
    rw [show (∑ a ∈ Sz, ((Q.filter (fun q => q ∣ a)).card : ℝ)) =
        ∑ a ∈ Sz, ∑ q ∈ Q, (if q ∣ a then (1 : ℝ) else 0) from
      sum_congr rfl (fun a _ => (sum_boole _ _).symm)]
    rw [sum_comm]
    exact sum_congr rfl (fun q _ => sum_boole _ _)
  have hqle : ∀ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) ≤
      (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) := by
    intro q _
    simp only [sifted]
    push_cast
    exact_mod_cast card_le_card (fun a ha => by
      simp only [hSz, mem_filter] at ha ⊢
      exact ⟨⟨ha.1.1, ha.2⟩, fun p hp => ha.1.2 p (hsubΩ hp)⟩)
  set SQ := A.filter (fun a => ∃ q ∈ Q, q ^ 2 ∣ a) with hSQ
  set small := (range (y + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ y + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 10) with hGd
  set U := small ∪ SQ ∪ Gd.image (fun p => N - p) with hU
  have hw : ∀ a ∈ Sz, 1 - ((Q.filter (fun q => q ∣ a)).card : ℝ) / 5 ≤
      if a ∈ U then 1 else 0 := by
    intro a ha
    split_ifs with haU
    · have : (0 : ℝ) ≤ ((Q.filter (fun q => q ∣ a)).card : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [hSz, mem_filter] at ha
      obtain ⟨haA, haP⟩ := ha
      have haA' := haA
      rw [hAdef] at haA'
      unfold goldbachSeq at haA'
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA'
      rw [mem_filter, mem_range] at hp
      obtain ⟨hpN, hpp⟩ := hp
      simp only [hU, mem_union, not_or] at haU
      obtain ⟨⟨hns, hnsq⟩, hng⟩ := haU
      have hpy : y < p := by
        by_contra h
        push Not at h
        exact hns (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
      have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
      have hmodd : Odd (N - p) := by
        rcases hE with ⟨a, ha⟩
        rcases hpodd with ⟨b, hb⟩
        exact ⟨a - b - 1, by omega⟩
      have hm0 : N - p ≠ 0 := by omega
      have hsq : ∀ q ∈ Q.filter (fun q => q ∣ N - p), ¬ q ^ 2 ∣ N - p := fun q hq h2 =>
        hnsq (mem_filter.mpr ⟨haA, q, (mem_filter.mp hq).1, h2⟩)
      have hΩ11 : 11 ≤ ArithmeticFunction.cardFactors (N - p) := by
        by_contra hc
        push Not at hc
        exact hng (mem_image.mpr ⟨p, by
          rw [hGd, mem_filter, mem_filter, mem_range]; exact ⟨⟨hpN, hpp⟩, by omega⟩, rfl⟩)
      have hsmallD : ∀ r, r.Prime → r ∣ N - p → r ≤ y →
          r ∈ Q.filter (fun q => q ∣ N - p) := by
        intro r hrp hrd hry
        have hr2 : r ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hrd)
        have hr3 : 3 ≤ r := by have := hrp.two_le; omega
        have hrN : ¬ r ∣ N := by
          intro hrN
          have : r ∣ p := by
            have h1 := Nat.dvd_sub hrN hrd
            rwa [Nat.sub_sub_self hpN.le] at h1
          have := (Nat.prime_dvd_prime_iff_eq hrp hpp).mp this
          omega
        have hrz : z < r := by
          by_contra hle
          push Not at hle
          exact haP r (hcov r hrp hrN hr3
            ((show (r : ℝ) ≤ z by exact_mod_cast hle).trans hzr)) hrd
        rw [mem_filter, hQ, mem_filter, mem_Ioc]
        exact ⟨⟨⟨hrz, hry⟩, hrp, hrN⟩, hrd⟩
      obtain ⟨hcardle, hpow⟩ := omega_split (N - p) hm0 (Q.filter (fun q => q ∣ N - p))
        (fun q hq => ⟨(hQmem q (mem_filter.mp hq).1).2.2.1, (mem_filter.mp hq).2⟩) hsq y hsmallD
        (z + 1) (fun q hq => (hQmem q (mem_filter.mp hq).1).1)
      set d := (Q.filter (fun q => q ∣ N - p)).card with hd
      set Ωa := ArithmeticFunction.cardFactors (N - p) with hΩa
      by_contra hlt
      push Not at hlt
      have hd4 : d ≤ 4 := by
        have h1 : (d : ℝ) < 5 := by linarith
        have h2 : d < 5 := by exact_mod_cast h1
        omega
      have hpowr : ((z : ℝ) + 1) ^ d * ((y : ℝ) + 1) ^ (Ωa - d) ≤ N := by
        have : (z + 1) ^ d * (y + 1) ^ (Ωa - d) ≤ N := hpow.trans (Nat.sub_le N p)
        exact_mod_cast this
      have hlog := Real.log_le_log (by positivity) hpowr
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Nat.cast_sub hcardle, ← hℓ] at hlog
      have hdr : (d : ℝ) ≤ 4 := by exact_mod_cast hd4
      have hΩr : (11 : ℝ) ≤ Ωa := by exact_mod_cast hΩ11
      have hdΩ : (d : ℝ) ≤ Ωa := by exact_mod_cast hcardle
      have h1 : (d : ℝ) * (ℓ / 21) ≤ d * Real.log ((z : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      have h2 : ((Ωa : ℝ) - d) * (11 * ℓ / 95) ≤ ((Ωa : ℝ) - d) * Real.log ((y : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogy3.le (by linarith)
      have h3 := mul_nonneg (show (0 : ℝ) ≤ 4 - d by linarith) hℓpos.le
      have h4 := mul_nonneg (show (0 : ℝ) ≤ (Ωa : ℝ) - 11 by linarith) hℓpos.le
      linarith
  have hsumw := sum_le_sum hw
  rw [sum_boole, sum_sub_distrib, ← sum_div, hswap] at hsumw
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsumw
  have hU1 : (Sz.filter (fun a => a ∈ U)).card ≤ U.card := card_le_card (fun a ha => (mem_filter.mp ha).2)
  have hU2 : U.card ≤ small.card + SQ.card + Gd.card :=
    (card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) card_image_le)
  have hU3 : ((Sz.filter (fun a => a ∈ U)).card : ℝ) ≤ (y : ℝ) + 1 + SQ.card + Gd.card := by
    have : (Sz.filter (fun a => a ∈ U)).card ≤ (y + 1) + SQ.card + Gd.card := by omega
    exact_mod_cast this
  have hqsum : ∑ q ∈ Q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) ≤
      ∑ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) := sum_le_sum hqle
  -- the squares
  have hSQ1 : (SQ.card : ℝ) ≤ 2 * N / ((z : ℝ) + 1) := by
    have h1 : SQ ⊆ Q.biUnion (fun q => (Ioc 0 N).filter (fun x => q ^ 2 ∣ x)) := by
      intro a ha
      rw [hSQ, mem_filter] at ha
      obtain ⟨haA, q, hq, hqa⟩ := ha
      rw [mem_biUnion]
      refine ⟨q, hq, mem_filter.mpr ⟨?_, hqa⟩⟩
      rw [hAdef] at haA
      unfold goldbachSeq at haA
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA
      rw [mem_filter, mem_range] at hp
      rw [mem_Ioc]
      omega
    have h2 := (card_le_card h1).trans card_biUnion_le
    have h3 : ∀ q ∈ Q, (((Ioc 0 N).filter (fun x => q ^ 2 ∣ x)).card : ℝ) ≤
        N * ((q : ℝ) ^ 2)⁻¹ := by
      intro q _
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := q ^ 2)
      push_cast at this
      rw [div_eq_mul_inv] at this
      exact this
    have h4 : ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ ≤ 2 / ((z : ℝ) + 1) := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg (?_ : Q ⊆ Ioo z (y + 1))
        (fun _ _ _ => by positivity)) (sum_Ioo_inv_sq_le z (y + 1))
      intro q hq
      obtain ⟨h1, h2, -, -⟩ := hQmem q hq
      rw [mem_Ioo]
      omega
    calc (SQ.card : ℝ) ≤ ∑ q ∈ Q, (((Ioc 0 N).filter (fun x => q ^ 2 ∣ x)).card : ℝ) := by
          exact_mod_cast h2
      _ ≤ ∑ q ∈ Q, (N : ℝ) * ((q : ℝ) ^ 2)⁻¹ := sum_le_sum h3
      _ = N * ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ N * (2 / ((z : ℝ) + 1)) := mul_le_mul_of_nonneg_left h4 hNpos.le
      _ = 2 * N / ((z : ℝ) + 1) := by ring
  have hSQ2 : 2 * N / ((z : ℝ) + 1) ≤ Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 2 := by
    have hcube := Real.pow_div_factorial_le_exp (x := L) (by linarith) 3
    have hT : ℓ ^ 3 / 55566 ≤ (z : ℝ) + 1 := by
      have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [h6] at hcube
      have e : ℓ ^ 3 / 55566 = L ^ 3 / 6 := by rw [hL]; ring
      linarith
    have hTpos : 0 < ℓ ^ 3 / 55566 := by positivity
    have hstep : 2 * N / ((z : ℝ) + 1) ≤ 2 * N / (ℓ ^ 3 / 55566) :=
      div_le_div_of_nonneg_left (by positivity) hTpos hT
    refine hstep.trans ?_
    rw [div_div_eq_mul_div, div_le_iff₀ (pow_pos hℓpos 3)]
    have e3 : ℓ ^ 3 = ℓ ^ 2 * ℓ := by ring
    have e : Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 2 * ℓ ^ 3 =
        Real.exp (-36) * (((N : ℝ) - 2) * ℓ) / 2 := by
      rw [e3, show Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 2 * (ℓ ^ 2 * ℓ) =
        Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) * ℓ / 2 by ring,
        div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
      ring
    rw [e]
    have hem : (1 : ℝ) / 10 ^ 18 ≤ Real.exp (-36) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 36) exp_36_le
    have h1 : ((N : ℝ) - 2) * 10 ^ 30 ≤ ((N : ℝ) - 2) * ℓ :=
      mul_le_mul_of_nonneg_left h10 (by linarith)
    have h2 : (1 / 10 ^ 18) * (((N : ℝ) - 2) * ℓ) ≤ Real.exp (-36) * (((N : ℝ) - 2) * ℓ) :=
      mul_le_mul_of_nonneg_right hem (mul_nonneg (by linarith) hℓpos.le)
    linarith
  -- y is small
  have hy50 : 50 * ((y : ℝ) + 1) ≤ Real.exp (ℓ / 3) + 2 := by
    have h1 : Real.exp (ℓ / 3) = Real.exp (11 * ℓ / 95) * Real.exp (62 * ℓ / 285) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (100 : ℝ) ≤ Real.exp (62 * ℓ / 285) := by
      have := Real.add_one_le_exp (62 * ℓ / 285); linarith
    have h3 : (1 : ℝ) ≤ Real.exp (11 * ℓ / 95) := Real.one_le_exp (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one h3)
    linarith
  have hc0 : Real.exp (-36) - Real.exp (-37) ≤ Real.exp (-36) := by
    have := Real.exp_pos (-37 : ℝ); linarith
  have hD : 0 ≤ ((N : ℝ) - 2) / ℓ ^ 2 := div_nonneg (by linarith) (by positivity)
  have hcD : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hc0 hD
  have hK3 : 0 ≤ |K| * N / ℓ ^ (3 : ℝ) := by rw [h3r]; positivity
  have he36 := Real.exp_pos (-36 : ℝ)
  have hgoal : Real.exp (-36) * N / ℓ ^ 2 ≤
      157 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 157 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) * ℓ ^ 2 =
        157 / 100 * Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) := by ring
    rw [e, div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
    nlinarith [mul_nonneg he36.le (show (0 : ℝ) ≤ (N : ℝ) - 38 by linarith)]
  have hE3' : 100 * (|K| * N / ℓ ^ (3 : ℝ)) + Real.exp (ℓ / 3) + 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    have : 100 * |K| * N / ℓ ^ (3 : ℝ) = 100 * (|K| * N / ℓ ^ (3 : ℝ)) := by ring
    linarith
  rw [hcardSz] at hlow
  linarith

end LeanLab.PNTPort.BVMax
