module

public import LeanLab.Halupczok2012.U1462Analytic

/-!
# P0077 Halupczok 2012, pointwise tails of the singular series, unit U-1462

AI wrote the Lean code, Claude, run 20261022T0403Z-7595. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Everything here is elementary and PROVED, no cited input.

* `S_tendsto`: for `r ≠ 0`, `∏_{p ≤ w} (1 + c_p(r)/(p-1)²) → S(r)` as `w → ∞`. The convergence
  layer for `twinC`, from `hasProd_primes_tendsto` and the summability of `1/(p-1)²`.
* `T_tendsto`: for `q ≥ 1`, `φ(q)⁻¹ ∏_{p ≤ w} tF(p) → 𝔗(n, q, a)`.
* `sum_Zsq_eq`: the sum over the squarefree `s ∈ Zsq z X₁` is the sum over the sets `t` of primes
  `≤ w` with `∏ t ≤ ⌊z⌋`, `∏ t ≤ X₁`, for every `w ≥ ⌊z⌋`.
* `tail_pointwise`: RAMANUJAN TAIL, for `m < n` and `0 < z ≤ X₁`,
  `|S(n - m) - ∑_{s ∈ Zsq z X₁} g_s(m)| ≤ z^{-σ} Kc σ Hs σ (n - m)`.
* `euler_pointwise`: EULER TAIL, for `q ≥ 1`, `(a, q) = 1`, `0 < z ≤ X₁`,
  `|∑_{s ∈ Zsq z X₁} Y/φ([q,s]) ∑_{b ∈ G(a,q,s)} g_s(b) - 𝔗(n,q,a) Y| ≤ Y z^{-σ} Kc σ Hs σ q / φ(q)`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset Filter Topology

theorem inv_sq_pred_le {k : ℕ} (hk : 2 ≤ k) : 1 / ((k : ℝ) - 1) ^ 2 ≤ 4 * ((k : ℝ) ^ 2)⁻¹ := by
  have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 < (k : ℝ) - 1 := by linarith
  rw [← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem summable_pert (f : ℕ → ℝ) {q : ℕ} (hq : 0 < q)
    (hb : ∀ k, k.Prime → |f k - 1| ≤ 1 / ((k : ℝ) - 1) ^ 2 + (if k ∣ q then 1 else 0)) :
    Summable (fun k : ℕ => if k.Prime then f k - 1 else 0) := by
  have hg : Summable (fun k : ℕ => 4 * ((k : ℝ) ^ 2)⁻¹ + (if k ∣ q then (1 : ℝ) else 0)) := by
    apply Summable.add
    · exact (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left 4
    · apply summable_of_ne_finset_zero (s := q.divisors)
      intro k hk
      rw [Nat.mem_divisors] at hk
      rw [if_neg (fun h => hk ⟨h, hq.ne'⟩)]
  refine Summable.of_norm_bounded hg (fun k => ?_)
  have hg0 : 0 ≤ (if k ∣ q then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h4 : 0 ≤ 4 * ((k : ℝ) ^ 2)⁻¹ := by positivity
  by_cases hp : k.Prime
  · rw [if_pos hp, Real.norm_eq_abs]
    refine (hb k hp).trans ?_
    have := inv_sq_pred_le hp.two_le
    linarith
  · rw [if_neg hp, norm_zero]; linarith

/-! ### The binary singular series as a limit of partial Euler products -/

/-- The factor of `twinC`. -/
noncomputable def f2 (p : ℕ) : ℝ := if p = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- The local factor `1 + c_p(r)/(p-1)²`. -/
noncomputable def locS (r p : ℕ) : ℝ := 1 + cPZ p (r : ℤ) / ((p : ℝ) - 1) ^ 2

/-- The correction factor of `S(r)` at `p`. -/
noncomputable def corrS (r p : ℕ) : ℝ :=
  if p = 2 then (if 2 ∣ r then 2 else 0) else (if p ∣ r then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1)

theorem locS_eq {r p : ℕ} (hp : p.Prime) : locS r p = f2 p * corrS r p := by
  unfold locS f2 corrS cPZ
  have hdvd : ((p : ℤ) ∣ (r : ℤ)) ↔ p ∣ r := Int.natCast_dvd_natCast
  by_cases h2 : p = 2
  · subst h2
    by_cases hr : 2 ∣ r
    · rw [if_pos (hdvd.mpr hr), if_pos rfl, if_pos rfl, if_pos hr]; norm_num
    · rw [if_neg (fun h => hr (hdvd.mp h)), if_pos rfl, if_pos rfl, if_neg hr]; norm_num
  · have h3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      have : 3 ≤ p := by omega
      exact_mod_cast this
    by_cases hr : p ∣ r
    · rw [if_pos (hdvd.mpr hr), if_neg h2, if_neg h2, if_pos hr]
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) - 2 ≠ 0 := by linarith
      field_simp; ring
    · rw [if_neg (fun h => hr (hdvd.mp h)), if_neg h2, if_neg h2, if_neg hr]; ring

theorem prod_corrS {r w : ℕ} (hr : r ≠ 0) (hrw : r ≤ w) (hw : 2 ≤ w) :
    ∏ p ∈ PrN w, corrS r p =
      if Even r then 2 * ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))
      else 0 := by
  have h2 : 2 ∈ PrN w := mem_PrN.mpr ⟨hw, Nat.prime_two⟩
  rw [← mul_prod_erase _ _ h2]
  have hrest : ∏ p ∈ (PrN w).erase 2, corrS r p =
      ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    have e : ∀ p ∈ (PrN w).erase 2, corrS r p =
        if p ∣ r then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
      intro p hp
      unfold corrS
      rw [if_neg (ne_of_mem_erase hp)]
    rw [prod_congr rfl e, ← prod_filter]
    apply prod_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_erase, mem_PrN, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp2, _, hp⟩, hd⟩; exact ⟨⟨hp, hd, hr⟩, hp2⟩
    · rintro ⟨⟨hp, hd, _⟩, hp2⟩
      exact ⟨⟨hp2, (Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hd).trans hrw, hp⟩, hd⟩
  rw [hrest]
  unfold corrS
  rw [if_pos rfl]
  by_cases he : Even r
  · rw [if_pos (even_iff_two_dvd.mp he), if_pos he]
  · rw [if_neg (fun h => he (even_iff_two_dvd.mpr h)), if_neg he, zero_mul]

theorem twinC_tendsto : Tendsto (fun w => ∏ p ∈ PrN w, f2 p) atTop (𝓝 twinC) := by
  have h := hasProd_primes_tendsto f2 (summable_pert f2 (q := 1) one_pos (fun k hk => by
    have hg0 : (0 : ℝ) ≤ (if k ∣ 1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have h0 : (0 : ℝ) ≤ 1 / ((k : ℝ) - 1) ^ 2 := by positivity
    unfold f2
    by_cases h2 : k = 2
    · rw [if_pos h2, sub_self, abs_zero]; linarith
    · rw [if_neg h2, show 1 - 1 / ((k : ℝ) - 1) ^ 2 - 1 = -(1 / ((k : ℝ) - 1) ^ 2) by ring,
        abs_neg, abs_of_nonneg h0]
      linarith))
  exact h

/-- **`S(r)` as the limit of its partial Euler products.** -/
theorem S_tendsto {r : ℕ} (hr : r ≠ 0) :
    Tendsto (fun w => ∏ p ∈ PrN w, locS r p) atTop (𝓝 (S r)) := by
  set cr : ℝ := if Even r then 2 * ∏ p ∈ r.primeFactors.filter (· ≠ 2),
    (((p : ℝ) - 1) / ((p : ℝ) - 2)) else 0 with hcr
  have hS : S r = twinC * cr := by
    unfold S; rw [hcr]; split_ifs <;> ring
  rw [hS]
  refine (twinC_tendsto.mul_const cr).congr' ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨max r 2, fun w hw => ?_⟩
  show (∏ p ∈ PrN w, f2 p) * cr = ∏ p ∈ PrN w, locS r p
  rw [prod_congr rfl (fun p hp => locS_eq (prime_of_mem_PrN hp)), prod_mul_distrib,
    prod_corrS hr (le_of_max_le_left hw) (le_of_max_le_right hw)]

/-! ### The ternary singular series as a limit -/

theorem ellT_bound {n q : ℕ} {a : ℤ} {p : ℕ} (hp : p.Prime) :
    |ellT n q a p| ≤ 1 / ((p : ℝ) - 1) ^ 2 + (if p ∣ q then 1 / ((p : ℝ) - 1) else 0) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold ellT locG cPZ
  set u : ℝ := (p : ℝ) - 1 with hu
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have i1 : 0 ≤ 1 / u ^ 2 := by positivity
  have i2 : 0 ≤ 1 / u := by positivity
  have hu' : u ≠ 0 := hu0.ne'
  have e1 : u / u ^ 2 = 1 / u := by rw [div_eq_div_iff (by positivity) hu']; ring
  have e2 : u / u ^ 3 = 1 / u ^ 2 := by rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e3 : 1 / u ^ 3 ≤ 1 / u ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity); nlinarith
  have p2 : 0 < u ^ 2 := by positivity
  have p3 : 0 < u ^ 3 := by positivity
  split_ifs <;>
    simp only [abs_div, abs_neg, abs_one, abs_of_pos hu0, abs_of_pos p2, abs_of_pos p3] <;>
    linarith

theorem T_tendsto {n q : ℕ} (a : ℤ) (hq : 0 < q) :
    Tendsto (fun w => 1 / (q.totient : ℝ) * ∏ p ∈ PrN w, tF n q a p) atTop (𝓝 (T n q a)) := by
  rw [T_eq_tprod]
  apply Tendsto.const_mul
  apply hasProd_primes_tendsto
  apply summable_pert _ hq
  intro k hk
  rw [tF_eq_one_add hk, add_sub_cancel_left]
  refine (ellT_bound hk).trans ?_
  have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.two_le
  have : 1 / ((k : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  split_ifs <;> linarith

/-! ### Squarefree moduli as sets of primes -/

theorem squarefree_prod_primes {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (ht p hp).prime.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq

theorem sum_Zsq_eq (G : Finset ℕ → ℝ) {z X1 : ℝ} {w : ℕ} (hw : ⌊z⌋₊ ≤ w) :
    ∑ s ∈ Zsq z X1, G s.primeFactors =
      ∑ t ∈ (PrN w).powerset with ((∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧ ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1), G t := by
  apply sum_nbij' (fun s => s.primeFactors) (fun t => ∏ p ∈ t, p)
  · intro s hs
    simp only [Zsq, coe_filter, mem_filter, mem_Icc, Set.mem_setOf_eq] at hs
    simp only [coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq]
    rw [Nat.prod_primeFactors_of_squarefree hs.2.1]
    refine ⟨fun p hp => ?_, hs.1.2, hs.2.2⟩
    rw [Nat.mem_primeFactors] at hp
    exact mem_PrN.mpr ⟨((Nat.le_of_dvd (by omega) hp.2.1).trans hs.1.2).trans hw, hp.1⟩
  · intro t ht
    simp only [coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at ht
    simp only [Zsq, coe_filter, mem_filter, mem_Icc, Set.mem_setOf_eq]
    have htP : ∀ p ∈ t, p.Prime := fun p hp => prime_of_mem_PrN (ht.1 hp)
    exact ⟨⟨prod_pos (fun p hp => (htP p hp).pos), ht.2.1⟩, squarefree_prod_primes htP, ht.2.2⟩
  · intro s hs
    simp only [Zsq, coe_filter, mem_filter, mem_Icc, Set.mem_setOf_eq] at hs
    exact Nat.prod_primeFactors_of_squarefree hs.2.1
  · intro t ht
    simp only [coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at ht
    exact Nat.primeFactors_prod (fun p hp => prime_of_mem_PrN (ht.1 hp))
  · intro s _; rfl

theorem lt_of_not_cond {z X1 : ℝ} (hz : 0 ≤ z) (hzX : z ≤ X1) {d : ℕ}
    (h : ¬ (d ≤ ⌊z⌋₊ ∧ (d : ℝ) ≤ X1)) : z < (d : ℝ) := by
  by_cases h1 : d ≤ ⌊z⌋₊
  · have h2 : ¬ (d : ℝ) ≤ X1 := fun h2 => h ⟨h1, h2⟩
    push_neg at h2; linarith
  · push_neg at h1
    exact Nat.lt_of_floor_lt h1

theorem abs_sub_le_of_tendsto {u : ℕ → ℝ} {L c B : ℝ} (h : Tendsto u atTop (𝓝 L))
    (hb : ∀ᶠ w in atTop, |c - u w| ≤ B) : |c - L| ≤ B :=
  le_of_tendsto ((tendsto_const_nhds.sub h).abs) hb

/-! ### The two pointwise tails -/

/-- **RAMANUJAN TAIL, pointwise.** -/
theorem tail_pointwise {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) {n m : ℕ} (hmn : m < n)
    {z X1 : ℝ} (hz : 0 < z) (hzX : z ≤ X1) :
    |S (n - m) - ∑ s ∈ Zsq z X1, gS n s m| ≤ z ^ (-σ) * (Kc σ * Hs σ (n - m)) := by
  have hr : n - m ≠ 0 := by omega
  have hcast : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub hmn.le
  rw [abs_sub_comm]
  apply abs_sub_le_of_tendsto (S_tendsto hr)
  rw [eventually_atTop]
  refine ⟨max (n - m) ⌊z⌋₊, fun w hw => ?_⟩
  beta_reduce
  have hw1 : n - m ≤ w := le_of_max_le_left hw
  have hw2 : ⌊z⌋₊ ≤ w := le_of_max_le_right hw
  have hZ : ∑ s ∈ Zsq z X1, gS n s m = ∑ t ∈ (PrN w).powerset with
      ((∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧ ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1), gW n t m :=
    sum_Zsq_eq (fun t => gW n t m) hw2
  have hP : ∏ p ∈ PrN w, locS (n - m) p = ∑ t ∈ (PrN w).powerset, gW n t m := by
    unfold locS gW
    rw [euler_expand, hcast]
  rw [hZ, hP, ← sum_filter_add_sum_filter_not (PrN w).powerset
    (fun t => (∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧ ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1), sub_add_cancel_left, abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hsub : ((PrN w).powerset.filter (fun t => ¬ ((∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧
      ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1))) ⊆
      (PrN w).powerset.filter (fun t => z < ((∏ p ∈ t, p : ℕ) : ℝ)) := by
    intro t ht
    rw [mem_filter] at ht ⊢
    exact ⟨ht.1, lt_of_not_cond hz.le hzX ht.2⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans ?_
  have hR := rankin_tail (PrN w) (fun p => cPZ p ((n : ℤ) - m) / ((p : ℝ) - 1) ^ 2) hz hσ.le
  refine hR.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hz.le _)
  apply prod_abs_le hσ hσ2 hr hw1
  intro p hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 0 < (p : ℝ) - 1 := by linarith
  have h1' : 0 < ((p : ℝ) - 1) ^ 2 := pow_pos h1 2
  rw [← hcast]
  unfold cPZ
  have hdvd : ((p : ℤ) ∣ ((n - m : ℕ) : ℤ)) ↔ p ∣ n - m := Int.natCast_dvd_natCast
  by_cases hd : p ∣ n - m
  · rw [if_pos (hdvd.mpr hd), if_pos hd, abs_div, abs_of_pos h1, abs_of_pos h1']
    have e : ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 = 1 / ((p : ℝ) - 1) := by
      rw [div_eq_div_iff h1'.ne' h1.ne']; ring
    rw [e]
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · rw [if_neg (fun h => hd (hdvd.mp h)), if_neg hd, abs_div, abs_neg, abs_one,
      abs_of_pos h1']
    linarith

/-- The term of the Euler sum at a set `t` of primes. -/
theorem term_eq {n q : ℕ} {a : ℤ} (hq : 0 < q) (ha : Int.gcd a q = 1) {t : Finset ℕ}
    (ht : ∀ p ∈ t, p.Prime) :
    1 / ((Nat.lcm q (∏ p ∈ t, p)).totient : ℝ) * ∑ b ∈ crtG a q (∏ p ∈ t, p), gW n t b =
      1 / (q.totient : ℝ) * ∏ p ∈ t, ellT n q a p := by
  classical
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hne : ∀ p ∈ t, (p : ℝ) - 1 ≠ 0 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (ht p hp).two_le
    linarith
  rw [crtG_sum ha ht, totient_lcm_prod ht]
  have hell : ∏ p ∈ t, ellT n q a p =
      (∏ p ∈ t, locG n q a p / ((p : ℝ) - 1) ^ 2) *
        ∏ p ∈ t with ¬ p ∣ q, (1 / ((p : ℝ) - 1)) := by
    rw [prod_filter, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    unfold ellT
    have := hne p hp
    split_ifs <;> field_simp <;> ring
  rw [hell, prod_div_distrib (s := t.filter _) (f := fun _ => (1 : ℝ)), prod_const_one]
  field_simp

/-- **EULER TAIL, pointwise in `q`.** -/
theorem euler_pointwise {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) {n q : ℕ} {a : ℤ} (hq : 0 < q)
    (ha : Int.gcd a q = 1) {z X1 Y1 : ℝ} (hz : 0 < z) (hzX : z ≤ X1) (hY : 0 ≤ Y1) :
    |∑ s ∈ Zsq z X1, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, gS n s b -
        T n q a * Y1| ≤ Y1 * (z ^ (-σ) * (Kc σ * Hs σ q) / (q.totient : ℝ)) := by
  set G : Finset ℕ → ℝ := fun t =>
    1 / ((Nat.lcm q (∏ p ∈ t, p)).totient : ℝ) * ∑ b ∈ crtG a q (∏ p ∈ t, p), gW n t b with hG
  have hZG : ∑ s ∈ Zsq z X1, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG a q s, gS n s b =
      Y1 * ∑ s ∈ Zsq z X1, G s.primeFactors := by
    rw [mul_sum]
    apply sum_congr rfl
    intro s hs
    simp only [Zsq, mem_filter] at hs
    have e := Nat.prod_primeFactors_of_squarefree hs.2.1
    simp only [hG, e, gS]
    ring
  rw [hZG, show Y1 * ∑ s ∈ Zsq z X1, G s.primeFactors - T n q a * Y1 =
    Y1 * (∑ s ∈ Zsq z X1, G s.primeFactors - T n q a) by ring, abs_mul, abs_of_nonneg hY]
  apply mul_le_mul_of_nonneg_left _ hY
  apply abs_sub_le_of_tendsto (T_tendsto a hq)
  rw [eventually_atTop]
  refine ⟨max q ⌊z⌋₊, fun w hw => ?_⟩
  beta_reduce
  have hw1 : q ≤ w := le_of_max_le_left hw
  have hw2 : ⌊z⌋₊ ≤ w := le_of_max_le_right hw
  rw [sum_Zsq_eq G hw2, ← euler_finite hq ha (PrN w) (fun p hp => prime_of_mem_PrN hp)]
  change |∑ t ∈ (PrN w).powerset with ((∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧ ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1),
    G t - ∑ t ∈ (PrN w).powerset, G t| ≤ _
  rw [← sum_filter_add_sum_filter_not (PrN w).powerset (fun t => (∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧ ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1), sub_add_cancel_left, abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hsub : ((PrN w).powerset.filter (fun t => ¬ ((∏ p ∈ t, p) ≤ ⌊z⌋₊ ∧
      ((∏ p ∈ t, p : ℕ) : ℝ) ≤ X1))) ⊆
      (PrN w).powerset.filter (fun t => z < ((∏ p ∈ t, p : ℕ) : ℝ)) := by
    intro t ht
    rw [mem_filter] at ht ⊢
    exact ⟨ht.1, lt_of_not_cond hz.le hzX ht.2⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans ?_
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have e : ∀ t ∈ (PrN w).powerset.filter (fun t => z < ((∏ p ∈ t, p : ℕ) : ℝ)),
      |G t| = 1 / (q.totient : ℝ) * |∏ p ∈ t, ellT n q a p| := by
    intro t ht
    rw [mem_filter, mem_powerset] at ht
    simp only [hG]
    rw [term_eq hq ha (fun p hp => prime_of_mem_PrN (ht.1 hp)), abs_mul,
      abs_of_pos (by positivity)]
  rw [sum_congr rfl e, ← mul_sum]
  have hR := rankin_tail (PrN w) (ellT n q a) hz hσ.le
  have hK := prod_abs_le hσ hσ2 hq.ne' hw1 (ellT n q a) (fun p hp => ellT_bound hp)
  calc 1 / (q.totient : ℝ) * ∑ t ∈ (PrN w).powerset with z < ((∏ p ∈ t, p : ℕ) : ℝ),
        |∏ p ∈ t, ellT n q a p|
      ≤ 1 / (q.totient : ℝ) * (z ^ (-σ) * (Kc σ * Hs σ q)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hR.trans (mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hz.le _))
    _ = _ := by ring

end LeanLab.Halupczok2012
