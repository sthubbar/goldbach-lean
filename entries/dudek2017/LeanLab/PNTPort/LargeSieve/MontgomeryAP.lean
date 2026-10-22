module

public import LeanLab.PNTPort.LargeSieve.MontgomeryBT
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Brun-Titchmarsh in arithmetic progressions from Montgomery's sieve

Lab proof, unit U-5553, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Montgomery 1968, with the lab's weak large sieve constant `N + 2Q²`. No cited input.

* `fP q = ∏_{p ∣ q} 1/(p - 1)`, so `fP q = 1/φ(q)` for squarefree `q`.
* `sum_divisors_rad_fP`: `∑_{d ∣ rad k} fP d = k/φ(k)`.
* `sum_sqf_le_coprime`: `∑_{q ≤ Q sqf} fP q ≤ k/φ(k) · ∑_{q ≤ Q sqf, (q,k)=1} fP q`.
* `brun_titchmarsh_ap_montgomery`: for `k, Q ≥ 1` the number of primes `p ≡ r mod k` in
  `(x, x + y]` is at most `Q + (y/k + 2 + 2Q²) · k / (φ(k) log(Q + 1))`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Finset Real

/-- `fP q = ∏_{p ∣ q} 1/(p - 1)`. -/
noncomputable def fP (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)

lemma fP_nonneg (q : ℕ) : 0 ≤ fP q :=
  prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg zero_le_one (by linarith)

lemma fP_mul {m n : ℕ} (h : Nat.Coprime m n) : fP (m * n) = fP m * fP n := by
  unfold fP
  rw [Nat.Coprime.primeFactors_mul h, prod_union h.disjoint_primeFactors]

/-- `fP` as a multiplicative arithmetic function. -/
noncomputable def fPA : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else fP d, by simp⟩

lemma fPA_mult : fPA.IsMultiplicative := by
  refine ⟨by simp [fPA, fP], fun {m n} h => ?_⟩
  show (if m * n = 0 then 0 else fP (m * n)) = (if m = 0 then 0 else fP m) * (if n = 0 then 0 else fP n)
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, fP_mul h]

/-- `∑_{d ∣ rad k} fP d = k/φ(k)`. -/
theorem sum_divisors_rad_fP {k : ℕ} (hk : 1 ≤ k) :
    ∑ d ∈ (rad k).divisors, fP d = (k : ℝ) / k.totient := by
  have h1 := fPA_mult.prodPrimeFactors_one_add_of_squarefree (rad_sqf k)
  have h2 : ∑ d ∈ (rad k).divisors, fPA d = ∑ d ∈ (rad k).divisors, fP d := by
    refine sum_congr rfl fun d hd => ?_
    show (if d = 0 then 0 else fP d) = fP d
    rw [if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [← h2, ← h1, rad_pf]
  have h3 : ∀ p ∈ k.primeFactors, 1 + fPA p = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    show 1 + (if p = 0 then 0 else fP p) = _
    rw [if_neg hpp.ne_zero]
    unfold fP
    rw [hpp.primeFactors, prod_singleton]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [eq_div_iff hne, add_mul, one_div, inv_mul_cancel₀ hne]
    ring
  rw [prod_congr rfl h3, prod_div_distrib]
  have ht := Nat.totient_mul_prod_primeFactors k
  have hcast : ((∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    push_cast
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have ht' : (k.totient : ℝ) * ∏ p ∈ k.primeFactors, (p : ℝ) =
      k * ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have ht2 : ((k.totient * ∏ p ∈ k.primeFactors, p : ℕ) : ℝ) =
        ((k * ∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [ht]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, hcast] at ht2
    exact ht2
  have hφ : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hk).ne'
  have hP : ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [div_eq_div_iff hP hφ]
  linarith [ht']

lemma dvd_rad {k ℓ : ℕ} (hk : k ≠ 0) (hℓ : ℓ.Prime) (h : ℓ ∣ k) : ℓ ∣ rad k :=
  dvd_prod_of_mem _ (Nat.mem_primeFactors.2 ⟨hℓ, h, hk⟩)

/-- Splitting off the part of `q` that divides `rad k`. -/
theorem sum_sqf_le_coprime {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter Squarefree, fP q ≤
      (k : ℝ) / k.totient * ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k), fP q := by
  set C := (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k)
  set D := (rad k).divisors
  set g : ℕ → ℕ × ℕ := fun q => (Nat.gcd q (rad k), q / Nat.gcd q (rad k))
  have hk0 : k ≠ 0 := by omega
  have hsplit : ∀ q, Squarefree q → q ≠ 0 →
      q = (g q).1 * (g q).2 ∧ Nat.Coprime (g q).1 (g q).2 ∧ Squarefree (g q).2 := by
    intro q hq _
    have hq' : q = (g q).1 * (g q).2 := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q (rad k))).symm
    refine ⟨hq', ?_⟩
    have := hq' ▸ hq
    rw [Nat.squarefree_mul_iff] at this
    exact ⟨this.1, this.2.2⟩
  have hmaps : ∀ q ∈ (Icc 1 Q).filter Squarefree, g q ∈ D ×ˢ C := by
    intro q hq
    rw [mem_filter, mem_Icc] at hq
    obtain ⟨heq, hcop, hsqf⟩ := hsplit q hq.2 (by omega)
    have hd0 : 0 < (g q).1 := Nat.gcd_pos_of_pos_left _ (by omega)
    rw [mem_product]
    refine ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, (rad_pos k).ne'⟩, ?_⟩
    rw [mem_filter, mem_Icc]
    have hq2pos : 0 < (g q).2 := by
      rcases Nat.eq_zero_or_pos (g q).2 with h | h
      · rw [h, mul_zero] at heq; omega
      · exact h
    have hq2le : (g q).2 ≤ q := Nat.div_le_self _ _
    refine ⟨⟨hq2pos, hq2le.trans hq.1.2⟩, hsqf, ?_⟩
    apply Nat.coprime_of_dvd
    intro ℓ hℓ h1 h2
    have hℓd : ℓ ∣ (g q).1 := by
      apply Nat.dvd_gcd
      · exact h1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      · exact dvd_rad hk0 hℓ h2
    have := Nat.dvd_gcd hℓd h1
    rw [hcop.gcd_eq_one] at this
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
  have hinj : Set.InjOn g ((Icc 1 Q).filter Squarefree) := by
    intro a ha b hb hab
    rw [mem_coe, mem_filter, mem_Icc] at ha hb
    rw [(hsplit a ha.2 (by omega)).1, (hsplit b hb.2 (by omega)).1, hab]
  have hval : ∀ q ∈ (Icc 1 Q).filter Squarefree, fP q = fP (g q).1 * fP (g q).2 := by
    intro q hq
    rw [mem_filter, mem_Icc] at hq
    obtain ⟨heq, hcop, -⟩ := hsplit q hq.2 (by omega)
    rw [← fP_mul hcop, ← heq]
  calc ∑ q ∈ (Icc 1 Q).filter Squarefree, fP q
      = ∑ q ∈ (Icc 1 Q).filter Squarefree, fP (g q).1 * fP (g q).2 := sum_congr rfl hval
    _ = ∑ y ∈ ((Icc 1 Q).filter Squarefree).image g, fP y.1 * fP y.2 :=
        (sum_image (f := fun y : ℕ × ℕ => fP y.1 * fP y.2) hinj).symm
    _ ≤ ∑ y ∈ D ×ˢ C, fP y.1 * fP y.2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro y hy
          obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
          exact hmaps q hq
        · intro y _ _; exact mul_nonneg (fP_nonneg _) (fP_nonneg _)
    _ = (∑ d ∈ D, fP d) * ∑ q ∈ C, fP q := by rw [sum_mul_sum, sum_product]
    _ = _ := by rw [sum_divisors_rad_fP hk]

lemma div_add_div_le (x y k : ℕ) (hk : 1 ≤ k) : (x + y) / k ≤ x / k + y / k + 1 := by
  have h1 := Nat.lt_mul_div_succ x (by omega : 0 < k)
  have h2 := Nat.lt_mul_div_succ y (by omega : 0 < k)
  have : x + y < k * (x / k + y / k + 2) := by nlinarith
  have := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).2 (by rw [mul_comm] at this; exact this)
  omega

/-- **Brun-Titchmarsh in progressions, explicit, from Montgomery's sieve.** -/
theorem brun_titchmarsh_ap_montgomery (x y k r Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) :
    ((((Ioc x (x + y)).filter (fun p => p.Prime ∧ p % k = r % k)).card : ℕ) : ℝ) ≤
      Q + ((y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * Real.log ((Q : ℝ) + 1)) := by
  set P := (Ioc x (x + y)).filter (fun p => p.Prime ∧ p % k = r % k)
  set Psmall := P.filter (· ≤ Q)
  set Pbig := P.filter (fun p => ¬ p ≤ Q)
  have hsplit : P.card = Psmall.card + Pbig.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have : Psmall ⊆ Icc 1 Q := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_Ioc] at hp
      exact mem_Icc.2 ⟨hp.1.2.1.one_lt.le, hp.2⟩
    have := card_le_card this
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  set r' := r % k
  have hdecomp : ∀ p ∈ Pbig, p = k * (p / k) + r' := by
    intro p hp
    simp only [Pbig, P, mem_filter] at hp
    show p = k * (p / k) + r % k
    rw [← hp.1.2.2]; exact (Nat.div_add_mod p k).symm
  set A : Finset ℤ := Pbig.image (fun p : ℕ => ((p / k : ℕ) : ℤ))
  have hAcard : A.card = Pbig.card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    simp only [Nat.cast_inj] at hab
    rw [hdecomp a ha, hdecomp b hb, hab]
  set M : ℤ := ((x / k : ℕ) : ℤ) - 1
  set N : ℕ := y / k + 2
  have hA : A ⊆ Ioc M (M + N) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Ioc] at hp
    have h1 : x / k ≤ p / k := Nat.div_le_div_right hp.1.1.1.le
    have h2 : p / k ≤ (x + y) / k := Nat.div_le_div_right hp.1.1.2
    have h3 := div_add_div_le x y k hk
    rw [mem_Ioc]
    simp only [M, N]
    constructor <;> push_cast <;> omega
  -- the forbidden class modulo a prime not dividing `k`
  set b : ℕ → ℕ := fun ℓ => ((-(r' : ZMod ℓ)) * (k : ZMod ℓ)⁻¹).val
  set B : ℕ → Finset ℕ := fun ℓ => if ℓ ∣ k then ∅ else {b ℓ}
  have hB : ∀ ℓ, ℓ.Prime → B ℓ ⊆ range ℓ ∧ (B ℓ).card < ℓ := by
    intro ℓ hℓ
    have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    simp only [B]
    split_ifs
    · exact ⟨empty_subset _, by rw [card_empty]; exact hℓ.pos⟩
    · refine ⟨?_, by rw [card_singleton]; exact hℓ.one_lt⟩
      intro c hc
      rw [mem_singleton] at hc
      rw [hc, mem_range]
      exact ZMod.val_lt _
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    have hpd := hdecomp p hp
    simp only [Pbig, P, mem_filter, mem_Ioc] at hp
    simp only [B]
    split_ifs with hdvd
    · exact Finset.notMem_empty _
    rw [mem_singleton, ← Int.natCast_mod, Int.toNat_natCast]
    intro hmod
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hk0 : (k : ZMod ℓ) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hdvd
    have hcast : ((p / k : ℕ) : ZMod ℓ) = (-(r' : ZMod ℓ)) * (k : ZMod ℓ)⁻¹ := by
      rw [← ZMod.natCast_mod, hmod, ZMod.natCast_zmod_val]
    have hp0 : (p : ZMod ℓ) = 0 := by
      rw [hpd]
      push_cast
      have hu : (k : ZMod ℓ) * (k : ZMod ℓ)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _
          ((ZMod.isUnit_iff_coprime k ℓ).2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hdvd).symm)
      rw [hcast, mul_comm (-(r' : ZMod ℓ)), ← mul_assoc, hu]
      ring
    rw [ZMod.natCast_eq_zero_iff] at hp0
    have := (Nat.prime_dvd_prime_iff_eq hℓ hp.1.2.1).1 hp0
    omega
  have hmont := montgomery_sieve hQ M N A hA B hB hAB
  -- lower bound for the sieve sum
  have hW_ge : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k), fP q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have heq : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q k),
        fP q = hW B q := by
      intro q hq
      rw [mem_filter, mem_Icc] at hq
      unfold fP hW
      refine prod_congr rfl fun ℓ hℓ => ?_
      have hℓk : ¬ ℓ ∣ k := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact (Nat.prime_of_mem_primeFactors hℓ).one_lt.ne' (Nat.dvd_one.1 this)
      simp only [B, if_neg hℓk, card_singleton, Nat.cast_one]
    rw [sum_congr rfl heq]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hlog := log_le_sum_sqf Q
  have hfP : ∀ q : ℕ, ∏ p ∈ q.primeFactors, 1 / (((p : ℕ) : ℝ) - 1) = fP q := fun q => rfl
  simp_rw [hfP] at hlog
  have hcop := sum_sqf_le_coprime hk Q
  have hlogpos : 0 < Real.log ((Q : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 hk
  -- `φ(k)/k · log(Q + 1) ≤ ∑ hW`
  have hL : (k.totient : ℝ) * Real.log ((Q : ℝ) + 1) ≤
      k * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have h1 : Real.log ((Q : ℝ) + 1) ≤ (k : ℝ) / k.totient *
        ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q :=
      (hlog.trans hcop).trans (mul_le_mul_of_nonneg_left hW_ge (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ hφ] at h1
    linarith
  have hbig : (Pbig.card : ℝ) ≤
      ((y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2) * k / (k.totient * Real.log ((Q : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity), ← hAcard]
    have hm : (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q ≤
        (y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2 := by
      have := hmont; simp only [N] at this; push_cast at this ⊢; linarith
    calc (A.card : ℝ) * (k.totient * Real.log ((Q : ℝ) + 1))
        ≤ (A.card : ℝ) * (k * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q) :=
          mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ = k * ((A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q) := by ring
      _ ≤ k * ((y / k : ℕ) + 2 + 2 * (Q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hm hk'.le
      _ = _ := by ring
  rw [hsplit, Nat.cast_add]
  linarith

end LeanLab.PNTPort.LargeSieve

