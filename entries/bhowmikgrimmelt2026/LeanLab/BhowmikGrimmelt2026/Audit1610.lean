module

public import LeanLab.BhowmikGrimmelt2026.DecompJ249

/-!
Unit U-1610, run 20261103T0803Z-22341. Refutations of the old statements of `DecompJ249`.
The old forms are spelled here as Props, since the file now holds the repaired forms.

* `euler_sing_eq_old_false`: the old `euler_sing_eq` at `N = 0`, the product diverges.
* `euler_gen_eq_old_false`: the old `euler_gen_eq` at `r₁ = r₂ = 1`, `N = 0`.
* `local_bound_old_false`: the old `local_bound` at `p = 2`, `r₁ = r₂ = 2`, `N = 1`.
* `euler_gen_eq_old_forces_zero`: adding `1 ≤ N` alone leaves the old `euler_gen_eq` forcing
  `genSing 1 1 2 = 0` at `r₁ = 1`, `r₂ = 2`, whose true value is about `0.66`, numerics only.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026.Audit1610

open Filter Topology Finset ArithmeticFunction

/-- The old `euler_sing_eq`. -/
def OldEulerSing : Prop := ∀ N : ℕ,
  Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorSing N p) atTop
    (𝓝 (singular N))

/-- The old `euler_gen_eq`. -/
def OldEulerGen : Prop := ∀ (r₁ r₂ : ℕ) [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ),
  Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen χ₁ χ₂ N p) atTop
    (𝓝 (genSing χ₁ χ₂ N))

/-- The old `local_bound`. -/
def OldLocalBound : Prop := ∀ (r₁ r₂ : ℕ) [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N p : ℕ),
  ‖eulerFactorGen χ₁ χ₂ N p‖ ≤ eulerFactorSing N p

/-! ### The product of `1 + 1/p` has no limit -/

lemma one_add_sum_le_prod (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ s, 0 ≤ a p) :
    1 + ∑ p ∈ s, a p ≤ ∏ p ∈ s, (1 + a p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hax := ha x (Finset.mem_insert_self _ _)
    have hs := ih (fun p hp => ha p (Finset.mem_insert_of_mem hp))
    have hsum : 0 ≤ ∑ p ∈ s, a p :=
      Finset.sum_nonneg (fun p hp => ha p (Finset.mem_insert_of_mem hp))
    nlinarith

theorem no_limit (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → 1 + 1 / (p : ℝ) ≤ f p) (L : ℝ)
    (h : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, f p) atTop (𝓝 L)) :
    False := by
  obtain ⟨c, hc⟩ := h.bddAbove_range
  have hc' : ∀ X, ∏ p ∈ (Finset.range X).filter Nat.Prime, f p ≤ c :=
    fun X => hc ⟨X, rfl⟩
  refine not_summable_one_div_on_primes (summable_of_sum_range_le (c := c) ?_ ?_)
  · intro n
    exact Set.indicator_nonneg (fun x _ => by positivity) n
  · intro n
    have h1 : ∑ i ∈ Finset.range n, Set.indicator {p : ℕ | p.Prime} (fun k : ℕ => (1 : ℝ) / k) i
        = ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / p := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Set.indicator_apply]
    rw [h1]
    have h2 := one_add_sum_le_prod ((Finset.range n).filter Nat.Prime) (fun p => (1 : ℝ) / p)
      (fun p _ => by positivity)
    have h3 : ∏ p ∈ (Finset.range n).filter Nat.Prime, (1 + (1 : ℝ) / p) ≤
        ∏ p ∈ (Finset.range n).filter Nat.Prime, f p := by
      refine Finset.prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
      exact hf p (Finset.mem_filter.mp hp).2
    linarith [hc' n]

/-! ### Roots of unity -/

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_val {q : ℕ} [NeZero q] (m : ZMod q) :
    ee ((m.val : ℝ) / q) = ZMod.stdAddChar m := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  simp only [ee]
  congr 1
  push_cast
  ring

lemma tauConj_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = ∑ m : ZMod q, starRingEnd ℂ (χ m) * ZMod.stdAddChar m := by
  simp only [tauConj, ee_val]

/-- The Gauss sum of the principal character mod `p ^ k` vanishes for `k ≥ 2`. -/
theorem tauConj_one_pow (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) [NeZero (p ^ k)] :
    tauConj (1 : DirichletCharacter ℂ (p ^ k)) = 0 := by
  set d : ZMod (p ^ k) := ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) with hd
  have hnil : IsNilpotent d := by
    refine ⟨2, ?_⟩
    rw [hd, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← pow_mul]
    exact pow_dvd_pow _ (by omega)
  have hd0 : d ≠ 0 := by
    rw [hd, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.pow_dvd_pow_iff_le_right hp.one_lt |>.mp h
    omega
  have hunit : ∀ m : ZMod (p ^ k), IsUnit (m + d) ↔ IsUnit m := by
    intro m
    constructor
    · intro h
      have := hnil.neg.isUnit_add_left_of_commute h (Commute.all _ _)
      simpa using this
    · intro h
      exact hnil.isUnit_add_left_of_commute h (Commute.all _ _)
  have hχ : ∀ m : ZMod (p ^ k), (1 : DirichletCharacter ℂ (p ^ k)) (m + d) =
      (1 : DirichletCharacter ℂ (p ^ k)) m := by
    intro m
    by_cases h : IsUnit m
    · obtain ⟨u, rfl⟩ := h
      obtain ⟨v, hv⟩ := (hunit u).mpr u.isUnit
      rw [← hv, MulChar.one_apply_coe, MulChar.one_apply_coe]
    · rw [MulChar.map_nonunit _ h, MulChar.map_nonunit _ (fun h' => h ((hunit m).mp h'))]
  set ψ := ZMod.stdAddChar (N := p ^ k) with hψ
  have hψd : ψ d ≠ 1 := by
    intro h
    apply hd0
    apply ZMod.injective_stdAddChar (N := p ^ k)
    rw [← hψ, h, AddChar.map_zero_eq_one]
  have hshift : tauConj (1 : DirichletCharacter ℂ (p ^ k)) =
      tauConj (1 : DirichletCharacter ℂ (p ^ k)) * ψ d := by
    rw [tauConj_eq, Finset.sum_mul]
    rw [← Equiv.sum_comp (Equiv.addRight d)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Equiv.coe_addRight, hχ, AddChar.map_add_eq_mul]
    ring
  have : tauConj (1 : DirichletCharacter ℂ (p ^ k)) * (1 - ψ d) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hψd

/-- Sum of `1` against an additive function over the nonzero residues mod a prime. -/
lemma sum_one_mul_std (p : ℕ) [Fact p.Prime] :
    ∑ m : ZMod p, (1 : DirichletCharacter ℂ p) m * ZMod.stdAddChar m = -1 := by
  have h0 : ∑ m : ZMod p, (ZMod.stdAddChar m : ℂ) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (fun h => by
      have := ZMod.isPrimitive_stdAddChar p
      have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
      have h2 := this h1
      apply h2
      ext x
      simp [AddChar.mulShift_apply, h])
  have hsplit : ∀ m : ZMod p, (1 : DirichletCharacter ℂ p) m * ZMod.stdAddChar m =
      ZMod.stdAddChar m - if m = 0 then 1 else 0 := by
    intro m
    by_cases h : m = 0
    · subst h
      simp [MulChar.map_zero, AddChar.map_zero_eq_one]
    · have hu : IsUnit m := isUnit_iff_ne_zero.mpr h
      obtain ⟨u, rfl⟩ := hu
      simp [MulChar.one_apply_coe]
  simp only [hsplit, Finset.sum_sub_distrib, h0]
  simp

lemma tauConj_one_prime (p : ℕ) [Fact p.Prime] : tauConj (1 : DirichletCharacter ℂ p) = -1 := by
  rw [tauConj_eq, ← sum_one_mul_std p]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  by_cases h : IsUnit m
  · obtain ⟨u, rfl⟩ := h
    simp [MulChar.one_apply_coe]
  · simp [MulChar.map_nonunit _ h]

lemma tauConj_one_level_one : tauConj (1 : DirichletCharacter ℂ 1) = 1 := by
  unfold tauConj
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  have h : (1 : DirichletCharacter ℂ 1) 0 = 1 := by
    have : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one]
  simp [h, ZMod.val_zero, ee_zero]

lemma cChi_one_level_one (N : ℤ) : cChi (1 : DirichletCharacter ℂ 1) N = 1 := by
  unfold cChi
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  have h : (1 : DirichletCharacter ℂ 1) 0 = 1 := by
    have : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one]
  simp [h, ZMod.val_zero, ee_zero]

lemma cChi_one_zero (p : ℕ) [Fact p.Prime] :
    cChi (1 : DirichletCharacter ℂ p) 0 = (Nat.totient p : ℂ) := by
  unfold cChi
  have h : ∀ a : ZMod p, (1 : DirichletCharacter ℂ p) a * ee ((a.val : ℝ) * ((0 : ℤ) : ℝ) / p) =
      (1 : DirichletCharacter ℂ p) a := by
    intro a
    simp [ee_zero]
  simp only [h]
  rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

lemma cChi_one_two_one : cChi (1 : DirichletCharacter ℂ 2) 1 = -1 := by
  rw [← sum_one_mul_std 2]
  unfold cChi
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← ee_val]
  norm_num

lemma Aq_congr {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    {q q' : ℕ} (h : q = q') [i : NeZero q] [i' : NeZero q'] :
    @Aq r₁ r₂ χ₁ χ₂ N q i = @Aq r₁ r₂ χ₁ χ₂ N q' i' := by
  subst h
  rfl

lemma Aq_one {r : ℕ} (N : ℤ) (q : ℕ) [NeZero q] (hr : r ∣ q) :
    Aq (1 : DirichletCharacter ℂ r) (1 : DirichletCharacter ℂ r) N q =
      tauConj (1 : DirichletCharacter ℂ q) * tauConj (1 : DirichletCharacter ℂ q) *
        cChi (1 : DirichletCharacter ℂ q) N / (Nat.totient q : ℂ) ^ 2 := by
  unfold Aq
  rw [dif_pos ⟨hr, hr⟩, DirichletCharacter.changeLevel_one, mul_one]

lemma Aq_one_high {r : ℕ} (N : ℤ) (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) [NeZero (p ^ k)]
    (hr : r ∣ p ^ k) :
    Aq (1 : DirichletCharacter ℂ r) (1 : DirichletCharacter ℂ r) N (p ^ k) = 0 := by
  rw [Aq_one N _ hr, tauConj_one_pow p k hp hk]
  simp

/-- At `r₁ = r₂ = 1`, `N = 0` the generalized Euler factor is `1 + 1/φ(p)`. -/
theorem eulerFactorGen_one_zero (p : ℕ) (hp : p.Prime) :
    eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 0 p =
      ((1 + 1 / (Nat.totient p : ℝ) : ℝ) : ℂ) := by
  haveI := Fact.mk hp
  have hne : ∀ k, p ^ k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  have hφ : (Nat.totient p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  unfold eulerFactorGen
  rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair zero_ne_one, dif_neg (hne 0), dif_neg (hne 1)]
  · rw [Aq_congr _ _ _ (pow_zero p) (i' := ⟨one_ne_zero⟩), Aq_congr _ _ _ (pow_one p) (i' := ⟨hp.ne_zero⟩),
      Aq_one 0 1 (one_dvd _), Aq_one 0 p (one_dvd _), tauConj_one_level_one, cChi_one_level_one,
      tauConj_one_prime, cChi_one_zero]
    push_cast
    simp only [Nat.totient_one, Nat.cast_one]
    field_simp
  · intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [dif_neg (hne k)]
    haveI : NeZero (p ^ k) := ⟨hne k⟩
    exact Aq_one_high 0 p k hp hk2 (one_dvd _)

lemma ramanujan_one (N : ℤ) : ramanujan 1 N = 1 := by
  simp [ramanujan, ee_zero]

/-- The ordinary Euler factor at a prime, written out. -/
theorem eulerFactorSing_prime (N p : ℕ) (hp : p.Prime) :
    eulerFactorSing N p = 1 + (ramanujan p N).re / (Nat.totient p : ℝ) ^ 2 := by
  unfold eulerFactorSing
  rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair zero_ne_one]
  · simp only [pow_zero, pow_one, ramanujan_one, moebius_apply_one, Nat.totient_one,
      moebius_apply_prime hp]
    norm_num
    ring
  · intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp

lemma ramanujan_prime_zero (p : ℕ) : (ramanujan p (0 : ℕ)).re = (Nat.totient p : ℝ) := by
  unfold ramanujan
  have h : ∀ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
      ee ((a : ℝ) * (((0 : ℕ) : ℤ) : ℝ) / p) = 1 := by
    intro a _
    simp [ee_zero]
  rw [Finset.sum_congr rfl h, Nat.totient_eq_card_coprime]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Complex.natCast_re]
  congr 2
  exact Finset.filter_congr (fun a _ => Nat.coprime_comm)

lemma one_div_le_totient (p : ℕ) (hp : p.Prime) :
    1 + 1 / (p : ℝ) ≤ 1 + 1 / (Nat.totient p : ℝ) := by
  have h0 : (0 : ℝ) < Nat.totient p := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have h1 : (Nat.totient p : ℝ) ≤ p := by exact_mod_cast Nat.totient_le p
  have := one_div_le_one_div_of_le h0 h1
  linarith

/-- The old `euler_sing_eq` is false at `N = 0`. -/
theorem euler_sing_eq_old_false : ¬ OldEulerSing := by
  intro h
  refine no_limit (fun p => eulerFactorSing 0 p) (fun p hp => ?_) _ (h 0)
  have h0 : (0 : ℝ) < Nat.totient p := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  show 1 + 1 / (p : ℝ) ≤ eulerFactorSing 0 p
  rw [eulerFactorSing_prime 0 p hp, ramanujan_prime_zero]
  have : (Nat.totient p : ℝ) / (Nat.totient p : ℝ) ^ 2 = 1 / (Nat.totient p : ℝ) := by
    field_simp
  rw [this]
  exact one_div_le_totient p hp

/-- The old `euler_gen_eq` is false at `r₁ = r₂ = 1`, `N = 0`. -/
theorem euler_gen_eq_old_false : ¬ OldEulerGen := by
  intro h
  have h0 := h 1 1 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 0
  have hre := Complex.continuous_re.tendsto _ |>.comp h0
  refine no_limit (fun p => 1 + 1 / (Nat.totient p : ℝ)) (fun p hp => one_div_le_totient p hp) _
    (hre.congr fun X => ?_)
  simp only [Function.comp_apply]
  have : ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 0 p =
      ((∏ p ∈ (Finset.range X).filter Nat.Prime, (1 + 1 / (Nat.totient p : ℝ)) : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [eulerFactorGen_one_zero p (Finset.mem_filter.mp hp).2]
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

/-- The old `local_bound` is false at `p = 2`, `r₁ = r₂ = 2`, `χ₁ = χ₂ = 1`, `N = 1`: the
generalized factor is `-1` and the ordinary factor is `0`. -/
theorem local_bound_old_false : ¬ OldLocalBound := by
  intro h
  have hb := h 2 2 (1 : DirichletCharacter ℂ 2) (1 : DirichletCharacter ℂ 2) 1 2
  have hne : ∀ k, 2 ^ k ≠ 0 := fun k => pow_ne_zero k two_ne_zero
  have hgen : eulerFactorGen (1 : DirichletCharacter ℂ 2) (1 : DirichletCharacter ℂ 2)
      ((1 : ℕ) : ℤ) 2 = -1 := by
    unfold eulerFactorGen
    rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair zero_ne_one, dif_neg (hne 0), dif_neg (hne 1)]
    · rw [Aq_congr _ _ _ (pow_zero 2) (i' := ⟨one_ne_zero⟩),
        Aq_congr _ _ _ (pow_one 2) (i' := ⟨two_ne_zero⟩), Aq_one _ 2 (dvd_refl 2)]
      have h0 : Aq (1 : DirichletCharacter ℂ 2) (1 : DirichletCharacter ℂ 2) ((1 : ℕ) : ℤ) 1 = 0 := by
        unfold Aq
        rw [dif_neg (by omega)]
      have hcast : (((1 : ℕ) : ℤ)) = 1 := by norm_num
      rw [h0, hcast, tauConj_one_prime, cChi_one_two_one]
      norm_num
    · intro k hk
      have hk2 : 2 ≤ k := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        omega
      rw [dif_neg (hne k)]
      haveI : NeZero (2 ^ k) := ⟨hne k⟩
      exact Aq_one_high _ 2 k Nat.prime_two hk2 (dvd_pow_self 2 (by omega))
  have hram : (ramanujan 2 ((1 : ℕ) : ℤ)).re = -1 := by
    have hfil : (Finset.range 2).filter (fun a => Nat.Coprime a 2) = {1} := by decide
    unfold ramanujan
    rw [hfil, Finset.sum_singleton]
    have : ee (((1 : ℕ) : ℝ) * ((((1 : ℕ) : ℤ)) : ℝ) / ((2 : ℕ) : ℝ)) = -1 := by
      have h' : (2 * (Real.pi : ℂ) * Complex.I * (((((1 : ℕ) : ℝ) * ((((1 : ℕ) : ℤ)) : ℝ) /
          ((2 : ℕ) : ℝ) : ℝ)) : ℂ)) = Real.pi * Complex.I := by
        push_cast
        ring
      simp only [ee]
      rw [h', Complex.exp_pi_mul_I]
    rw [this]
    simp
  have hsing : eulerFactorSing 1 2 = 0 := by
    rw [eulerFactorSing_prime 1 2 Nat.prime_two, hram, Nat.totient_two]
    norm_num
  rw [hgen, hsing] at hb
  norm_num at hb

/-- Adding `1 ≤ N` alone does not repair the old `euler_gen_eq`: at `r₁ = 1`, `r₂ = 2` every prime
power `3 ^ k` misses the level `2`, so the factor at `3` is `0` and the old form forces the
series to vanish. Its true value is about `0.66`; that value is numerics, not kernel checked. -/
theorem euler_gen_eq_old_forces_zero
    (h : ∀ (r₁ r₂ : ℕ) [NeZero r₁] [NeZero r₂] (χ₁ : DirichletCharacter ℂ r₁)
      (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ), 1 ≤ N →
      Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen χ₁ χ₂ N p)
        atTop (𝓝 (genSing χ₁ χ₂ N))) :
    genSing (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 2) 2 = 0 := by
  have h3 : eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 2) 2 3 = 0 := by
    unfold eulerFactorGen
    have : ∀ k : ℕ, (if h : 3 ^ k = 0 then (0 : ℂ) else
        @Aq 1 2 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 2) 2 (3 ^ k) ⟨h⟩) = 0 := by
      intro k
      split_ifs with h0
      · rfl
      · unfold Aq
        rw [dif_neg]
        rintro ⟨-, h2⟩
        have := Nat.prime_two.dvd_of_dvd_pow h2
        omega
    simp only [this, tsum_zero]
  have hlim := h 1 2 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 2) 2 (by norm_num)
  have hz : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 2) 2 p) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with X hX
    symm
    refine Finset.prod_eq_zero (i := 3) ?_ h3
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by norm_num⟩
  exact tendsto_nhds_unique hlim hz

/-! ### Vacuity instances -/

lemma isPrimitive_of_level_one {n : ℕ} (hn : n = 1) (χ : DirichletCharacter ℂ n) :
    χ.IsPrimitive := by
  subst hn
  rw [DirichletCharacter.level_one χ]
  exact DirichletCharacter.isPrimitive_one_level_one

/-- `IsPrimeComponents` holds for the trivial character. -/
theorem isPrimeComponents_one :
    IsPrimeComponents (1 : DirichletCharacter ℂ 1) (fun _ => 1) := by
  refine ⟨fun p => isPrimitive_of_level_one (by simp [compLevel]) _, fun a _ => ?_⟩
  have : (a : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [this]

/-- The hypotheses of `euler_gen_eq` and `local_bound` hold at the trivial character. -/
theorem hypotheses_instance :
    (1 : DirichletCharacter ℂ 1).IsPrimitive ∧ (2 : ℕ).Prime ∧ 1 ≤ (1 : ℕ) :=
  ⟨DirichletCharacter.isPrimitive_one_level_one, Nat.prime_two, le_rfl⟩

end LeanLab.BhowmikGrimmelt2026.Audit1610
