module

public import LeanLab.PNTPort.BVMax.RenyiWeighted

/-!
# Rényi's theorem with `K = 14`

Unit U-6757, CLOUD 20261020T2317Z-cloud53. AI wrote the Lean code. Known mathematics.
The assembly of `RenyiWeighted.lean`: the lower block sieve of `Renyi20.lean` at
`z = N^{1/21}`, minus the upper block sieves at `w = N^{2/49}` of the multiples of each prime
`q ∤ N` in `(z, y]`, `y = N^{1/15}`. A survivor `N - p` with `p > y` has every prime factor above
`y`, so `Ω(N - p) ≤ 14`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN; Pan K = 4 and Chen K = 2 are far stronger.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- Facts on `⌊exp M⌋` for `M ≥ 10`. -/
lemma floor_exp_facts (M : ℝ) (hM : 10 ≤ M) :
    3 ≤ ⌊Real.exp M⌋₊ ∧ (⌊Real.exp M⌋₊ : ℝ) ≤ Real.exp M ∧
    Real.exp M < (⌊Real.exp M⌋₊ : ℝ) + 1 ∧ M - 1 ≤ Real.log ⌊Real.exp M⌋₊ ∧
    Real.log ⌊Real.exp M⌋₊ ≤ M ∧ M < Real.log ((⌊Real.exp M⌋₊ : ℝ) + 1) := by
  have h1 : (⌊Real.exp M⌋₊ : ℝ) ≤ Real.exp M := Nat.floor_le (Real.exp_pos _).le
  have h2 : Real.exp M < (⌊Real.exp M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hM1 : (1 : ℝ) ≤ Real.exp (M - 1) := Real.one_le_exp (by linarith)
  have hsplit : Real.exp M = Real.exp (M - 1) * Real.exp 1 := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (M - 1) ≤ (⌊Real.exp M⌋₊ : ℝ) := by nlinarith
  have hpos : (0 : ℝ) < ⌊Real.exp M⌋₊ := lt_of_lt_of_le (Real.exp_pos _) h3
  refine ⟨?_, h1, h2, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    have := Real.add_one_le_exp M
    push_cast; linarith
  · have := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at this
  · have := Real.log_le_log hpos h1
    rwa [Real.log_exp] at this
  · have := Real.log_lt_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this

/-- The lab's block Mertens bound for the densities `1/(p - 1)`. -/
lemma xDen_block (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ a < p ∧ p ≤ b) :
    ∑ p ∈ S, xDen p ≤
      (1 + 1 / (a : ℝ)) * ((Real.log b - Real.log a + 14) / Real.log a) := by
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hterm : ∀ p ∈ S, xDen p ≤ (1 + 1 / (a : ℝ)) * (1 / (p : ℝ)) := by
    intro p hp
    obtain ⟨-, hap, -⟩ := hS p hp
    have h3 : 3 ≤ p := by omega
    have hap' : (a : ℝ) + 1 ≤ p := by exact_mod_cast hap
    simp only [xDen, if_pos h3]
    rw [show (1 + 1 / (a : ℝ)) * (1 / (p : ℝ)) = (a + 1) / (a * p) by field_simp]
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  have hsub : S ⊆ (Ioc a b).filter Nat.Prime := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨h2, h3⟩, h1⟩
  have hM := LeanLab.PNTSieve.Mertens.sum_inv_primes_block a b ha hab
  have h2 : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  calc ∑ p ∈ S, xDen p ≤ ∑ p ∈ S, (1 + 1 / (a : ℝ)) * (1 / (p : ℝ)) := sum_le_sum hterm
    _ = (1 + 1 / (a : ℝ)) * ∑ p ∈ S, (1 : ℝ) / p := by rw [mul_sum]
    _ ≤ (1 + 1 / (a : ℝ)) * ((Real.log b - Real.log a + 14) / Real.log a) :=
        mul_le_mul_of_nonneg_left (h2.trans hM) (by positivity)

lemma big_aux14 (ℓ : ℝ) (h : (2 : ℝ) ^ 2100 ≤ ℓ) :
    (2 : ℝ) ^ 2006 ≤ ℓ / 21 ∧ (2 : ℝ) ^ 2006 ≤ 2 * ℓ / 49 ∧ (10 : ℝ) ^ 6 ≤ ℓ := by
  have e : (2 : ℝ) ^ 2100 = 2 ^ 94 * 2 ^ 2006 := by rw [← pow_add]
  rw [e] at h
  clear e
  have h94 : (25 : ℝ) ≤ 2 ^ 94 :=
    calc (25 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ 94 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h20 : (10 : ℝ) ^ 6 ≤ 2 ^ 2006 :=
    calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
      _ ≤ 2 ^ 2006 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  generalize (2 : ℝ) ^ 2006 = A at *
  generalize (2 : ℝ) ^ 94 = C at *
  have hA : 0 ≤ A := le_trans (by norm_num) h20
  have hm := mul_le_mul_of_nonneg_right h94 hA
  refine ⟨?_, ?_, ?_⟩ <;> linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **Rényi with `K = 14`, deterministic core with the count.** -/
theorem renyi14_count {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (hE : Even N) (hℓ6 : (2 : ℝ) ^ 2100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : 100 * |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    Real.exp (-36) * N / (10 * Real.log N ^ 2) ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 14)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨hLbig0, hL2big0, h10⟩ := big_aux14 ℓ hℓ6
  clear hℓ6
  obtain ⟨Bs, hG, hmem, hcov, hlev, hρ, h3k⟩ := block_pack N (ℓ / 21) hLbig0
  obtain ⟨Cs, hG', hmem', hcov', hlev', hρ', -⟩ := block_pack N (2 * ℓ / 49) hL2big0
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
  set L2 := 2 * ℓ / 49 with hL2
  have hL10 : (10 ^ 4 : ℝ) ≤ L2 := by linarith
  obtain ⟨hz3, hzr, hz1, hlogz1, hlogz2, -⟩ := floor_exp_facts L (by linarith)
  obtain ⟨hw3, hwr, hw1, hlogw1, hlogw2, -⟩ := floor_exp_facts L2 (by linarith)
  obtain ⟨hy3, hyr, hy1, hlogy1, hlogy2, hlogy3⟩ := floor_exp_facts (ℓ / 15) (by linarith)
  set z := ⌊Real.exp L⌋₊ with hz
  set w := ⌊Real.exp L2⌋₊ with hw
  set y := ⌊Real.exp (ℓ / 15)⌋₊ with hy
  have hL2L : L2 ≤ L := by linarith
  have hLy : L ≤ ℓ / 15 := by linarith
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
      apply hlevel (ℓ / 15 + 154 / 15 * L2) (by linarith)
      rw [Real.exp_add]
      push_cast
      have hqr : (q : ℝ) ≤ Real.exp (ℓ / 15) :=
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
  -- Buchstab
  have hkuhn := sifted_union_ge A Ω Ω' Q hsubΩ
  -- the densities
  set V := ∏ p ∈ Ω, (1 - xDen p) with hVdef
  set W := ∏ p ∈ Ω', (1 - xDen p) with hWdef
  have hW0 : 0 ≤ W := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hsw : ∑ p ∈ Ω \ Ω', xDen p ≤ 168 / 1000 := by
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
    have hfrac : (Real.log z - Real.log w + 14) / Real.log w ≤ 1675 / 10000 := by
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
  have hVW : W * (832 / 1000) ≤ V := by
    have e : (∏ p ∈ Ω \ Ω', (1 - xDen p)) * W = V := prod_sdiff hsubΩ
    have h1 := one_sub_sum_le_prod (Ω \ Ω') xDen xDen_nonneg xDen_le_one
    have hP : (832 / 1000 : ℝ) ≤ ∏ p ∈ Ω \ Ω', (1 - xDen p) := by linarith
    have := mul_le_mul_of_nonneg_left hP hW0
    calc W * (832 / 1000) ≤ W * ∏ p ∈ Ω \ Ω', (1 - xDen p) := this
      _ = V := by rw [← e]; ring
  have hsQ : ∑ q ∈ Q, xDen q ≤ 402 / 1000 := by
    have h := xDen_block z y (by omega) hzy Q (fun q hq => by
      obtain ⟨h1, h2, h3, -⟩ := hQmem q hq
      exact ⟨h3, h1, h2⟩)
    refine h.trans ?_
    have hlz : 0 < Real.log z := by linarith
    have hfrac : (Real.log y - Real.log z + 14) / Real.log z ≤ 4005 / 10000 := by
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
  have hsubtr : X * W * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q ≤ X * V * (599 / 1000) := by
    have h1 : (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q ≤ (12395 / 10000) * (402 / 1000) :=
      mul_le_mul (by linarith) hsQ hsQ0 (by norm_num)
    have h2 : W * ((1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q) ≤
        W * ((12395 / 10000) * (402 / 1000)) := mul_le_mul_of_nonneg_left h1 hW0
    have h3 : W * ((12395 / 10000) * (402 / 1000)) ≤ V * (599 / 1000) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hX
    calc X * W * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q
        = X * (W * ((1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, xDen q)) := by ring
      _ ≤ X * (V * (599 / 1000)) := h4
      _ = X * V * (599 / 1000) := by ring
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
  have hsum0 : 0 ≤ ∑ S ∈ Ω.powerset.filter (fun S => cL Bs S ≠ 0), |rem A xDen X S| :=
    sum_nonneg (fun _ _ => abs_nonneg _)
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
  -- the sifted count of Ω ∪ Q
  have hS : 21 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) - |K| * N / ℓ ^ (3 : ℝ) ≤
      (sifted A (Ω ∪ Q) : ℝ) := by
    have hXV' : 21 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) ≤ X * V := hXV2 ▸ hXV
    linarith
  -- survivors
  set Surv := A.filter (fun a => ∀ p ∈ Ω ∪ Q, ¬ p ∣ a) with hSurv
  have hcardS : (sifted A (Ω ∪ Q) : ℝ) = (Surv.card : ℝ) := by
    simp [sifted, hSurv]
  set small := (range (y + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ y + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 14) with hGd
  have hsub : Surv \ small ⊆ Gd.image (fun p => N - p) := by
    intro m hm
    rw [mem_sdiff] at hm
    obtain ⟨hmS, hmn⟩ := hm
    rw [hSurv, mem_filter] at hmS
    obtain ⟨hmG, hmP⟩ := hmS
    rw [hAdef] at hmG
    unfold goldbachSeq at hmG
    rw [mem_image] at hmG
    obtain ⟨p, hp, rfl⟩ := hmG
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpN, hpp⟩ := hp
    have hpy : y < p := by
      by_contra h
      push Not at h
      exact hmn (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
    have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hmodd : Odd (N - p) := by
      rcases hE with ⟨a, ha⟩
      rcases hpodd with ⟨b, hb⟩
      exact ⟨a - b - 1, by omega⟩
    have hm0 : N - p ≠ 0 := by omega
    have hfac_big : ∀ q ∈ (N - p).primeFactorsList, y + 1 ≤ q := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      by_contra hlt
      push Not at hlt
      have hqy : q ≤ y := by omega
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
      · by_cases hqz : (q : ℝ) ≤ Real.exp L
        · exact hmP q (mem_union_left _ (hcov q hqp hqN hq3 hqz)) hqd
        · push Not at hqz
          have hzq : z < q := by
            have : (z : ℝ) < q := lt_of_le_of_lt hzr hqz
            exact_mod_cast this
          exact hmP q (mem_union_right _ (by
            rw [hQ, mem_filter, mem_Ioc]; exact ⟨⟨hzq, hqy⟩, hqp, hqN⟩)) hqd
    have hpow := pow_bigOmega_le (N - p) (y + 1) hm0 hfac_big
    have hpowr : ((y : ℝ) + 1) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := by
      have : (y + 1) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := hpow.trans (Nat.sub_le N p)
      exact_mod_cast this
    have hlogpow : (ArithmeticFunction.cardFactors (N - p) : ℝ) * Real.log ((y : ℝ) + 1) ≤ ℓ := by
      have := Real.log_le_log (by positivity) hpowr
      rwa [Real.log_pow] at this
    have hΩr : ArithmeticFunction.cardFactors (N - p) ≤ 14 := by
      by_contra hcon
      push Not at hcon
      have h15 : (15 : ℝ) ≤ (ArithmeticFunction.cardFactors (N - p) : ℝ) := by exact_mod_cast hcon
      have hl0 : 0 < Real.log ((y : ℝ) + 1) := by linarith
      have : 15 * Real.log ((y : ℝ) + 1) ≤ ℓ :=
        (mul_le_mul_of_nonneg_right h15 hl0.le).trans hlogpow
      linarith
    refine mem_image.mpr ⟨p, ?_, rfl⟩
    rw [hGd, mem_filter, mem_filter, mem_range]
    exact ⟨⟨hpN, hpp⟩, hΩr⟩
  have hc1 : Surv.card ≤ (Surv \ small).card + small.card := card_le_card_sdiff_add_card
  have hc2 : (Surv \ small).card ≤ Gd.card := (card_le_card hsub).trans card_image_le
  have hc3 : (Surv.card : ℝ) ≤ (Gd.card : ℝ) + (y : ℝ) + 1 := by
    have : Surv.card ≤ Gd.card + (y + 1) := by omega
    exact_mod_cast this
  -- y is small
  have hy50 : 50 * ((y : ℝ) + 1) ≤ Real.exp (ℓ / 3) + 2 := by
    have h1 : Real.exp (ℓ / 3) = Real.exp (ℓ / 15) * Real.exp (4 * ℓ / 15) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (100 : ℝ) ≤ Real.exp (4 * ℓ / 15) := by
      have := Real.add_one_le_exp (4 * ℓ / 15); linarith
    have h3 : (1 : ℝ) ≤ Real.exp (ℓ / 15) := Real.one_le_exp (by linarith)
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
  have hgoal : Real.exp (-36) * N / (10 * ℓ ^ 2) ≤
      18 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 18 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) * (10 * ℓ ^ 2) =
        18 / 10 * Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) := by ring
    rw [e, div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
    nlinarith [mul_nonneg he36.le (show (0 : ℝ) ≤ (N : ℝ) - 38 by linarith)]
  have hE3' : 100 * (|K| * N / ℓ ^ (3 : ℝ)) + Real.exp (ℓ / 3) + 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    have : 100 * |K| * N / ℓ ^ (3 : ℝ) = 100 * (|K| * N / ℓ ^ (3 : ℝ)) := by ring
    linarith
  rw [← hcardS] at hc3
  linarith

end LeanLab.PNTPort.BVMax
