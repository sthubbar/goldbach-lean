module

public import Mathlib
public import LeanLab.HeathBrown1985.Bound25

/-!
P0096 Heath-Brown 1985, Lemma 1, 2.6 and 2.7, deduced from 2.4 as on pages 48 to 50.
2.4 is the named input `Bound2_4`; 2.1 is replaced by `k/φ(k) ≤ e(1 + ω(k))` and
`σ(q)/q ≤ 1 + log q`, both proved.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-! ### Counting `n ≤ N`, `n ≡ l (k)`, `d ∣ n` -/

theorem modEq_lcm_iff {a b m n : ℕ} :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD Nat.lcm m n] := by
  rcases le_total a b with h | h
  · rw [Nat.modEq_iff_dvd' h, Nat.modEq_iff_dvd' h, Nat.modEq_iff_dvd' h, Nat.lcm_dvd_iff]
  · rw [Nat.ModEq.comm (n := m), Nat.ModEq.comm (n := n), Nat.ModEq.comm (n := Nat.lcm m n),
      Nat.modEq_iff_dvd' h, Nat.modEq_iff_dvd' h, Nat.modEq_iff_dvd' h, Nat.lcm_dvd_iff]

/-- At least `N / m` integers of `[1, N]` lie in any residue class mod `m`. -/
theorem card_residue_ge (N m r : ℕ) (hm : 1 ≤ m) :
    N / m ≤ ((Icc 1 N).filter (fun n => n % m = r % m)).card := by
  set r' := if r % m = 0 then m else r % m
  have hr'1 : 1 ≤ r' := by
    simp only [r']; split_ifs with h <;> omega
  have hr'm : r' ≤ m := by
    simp only [r']; split_ifs with h
    · exact le_rfl
    · exact (Nat.mod_lt r (by omega)).le
  have hr'mod : r' % m = r % m := by
    simp only [r']; split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_mod r m
  have : (Icc 1 (N / m)).card ≤ ((Icc 1 N).filter (fun n => n % m = r % m)).card := by
    apply card_le_card_of_injOn (fun j => m * (j - 1) + r')
    · intro j hj
      simp only [coe_Icc, Set.mem_Icc] at hj
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq]
      have h1 : m * (j - 1) + r' ≤ m * j := by
        have : m * j = m * (j - 1) + m := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      have h2 : m * j ≤ N := by
        have := Nat.mul_div_le N m
        calc m * j ≤ m * (N / m) := Nat.mul_le_mul_left _ hj.2
          _ ≤ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self N m
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.mul_add_mod, hr'mod]
    · intro a ha b hb hab
      simp only [coe_Icc, Set.mem_Icc] at ha hb
      simp only at hab
      have := Nat.eq_of_mul_eq_mul_left (show 0 < m by omega) (by omega : m * (a - 1) = m * (b - 1))
      omega
  simpa using this

/-- The number of `n ∈ [1, ⌊x⌋]` with `n ≡ l (k)` and `d ∣ n`. -/
def cnt (x : ℝ) (k l d : ℕ) : ℕ :=
  ((Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k ∧ d ∣ n)).card

theorem cnt_eq_zero (x : ℝ) (k l d : ℕ) (h : ¬ Nat.gcd d k ∣ l) : cnt x k l d = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro n _ ⟨h1, h2⟩
  apply h
  have hg1 : Nat.gcd d k ∣ n := (Nat.gcd_dvd_left d k).trans h2
  have hmod : n ≡ l [MOD Nat.gcd d k] := Nat.ModEq.of_dvd (Nat.gcd_dvd_right d k) h1
  exact (Nat.dvd_iff_mod_eq_zero.mpr ((Nat.mod_eq_zero_of_dvd hg1).symm.trans hmod).symm)

theorem abs_cnt_sub_le (x : ℝ) (hx : 1 ≤ x) (k l d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (h : Nat.gcd d k ∣ l) :
    |(cnt x k l d : ℝ) - x * Nat.gcd d k / (d * k)| ≤ 2 := by
  set m := Nat.lcm d k
  have hm1 : 1 ≤ m := Nat.lcm_pos hd hk
  have hcr : 0 ≡ l [MOD Nat.gcd d k] := by
    rw [Nat.ModEq, Nat.zero_mod, eq_comm]; exact Nat.mod_eq_zero_of_dvd h
  obtain ⟨n0, hn0d, hn0k⟩ := Nat.chineseRemainder' hcr
  have hiff : ∀ n, (n % k = l % k ∧ d ∣ n) ↔ n % m = n0 % m := by
    intro n
    have e1 : (n % k = l % k) ↔ n ≡ n0 [MOD k] := by
      constructor
      · intro h1; exact (h1 : n ≡ l [MOD k]).trans hn0k.symm
      · intro h1; exact h1.trans hn0k
    have e2 : d ∣ n ↔ n ≡ n0 [MOD d] := by
      constructor
      · intro h1; exact ((Nat.modEq_zero_iff_dvd.mpr h1)).trans hn0d.symm
      · intro h1; exact Nat.modEq_zero_iff_dvd.mp (h1.trans hn0d)
    rw [e1, e2, and_comm]
    exact modEq_lcm_iff
  have hc : cnt x k l d = ((Icc 1 ⌊x⌋₊).filter (fun n => n % m = n0 % m)).card := by
    unfold cnt; congr 1; ext n; simp only [mem_filter]; rw [hiff]
  have hup := card_residue_le ⌊x⌋₊ m (n0 % m) hm1
  have hlo := card_residue_ge ⌊x⌋₊ m n0 hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hgl : (Nat.gcd d k : ℝ) * m = d * k := by exact_mod_cast Nat.gcd_mul_lcm d k
  have hdk : x * Nat.gcd d k / (d * k) = x / m := by
    have : (d : ℝ) * k ≠ 0 := by positivity
    rw [← hgl]; field_simp
  rw [hdk, hc]
  have hfl1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfl2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hq1 : ((⌊x⌋₊ / m : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / m := Nat.cast_div_le
  have hq2 : (⌊x⌋₊ : ℝ) / m - 1 < ((⌊x⌋₊ / m : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := ⌊x⌋₊) hm1
    have h' : (⌊x⌋₊ : ℝ) < ((⌊x⌋₊ / m : ℕ) : ℝ) * m + m := by exact_mod_cast this
    rw [div_sub_one hmR.ne', div_lt_iff₀ hmR]; linarith
  have hxm1 : x / m - (⌊x⌋₊ : ℝ) / m ≤ 1 := by
    rw [← sub_div, div_le_one hmR]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hxm0 : (⌊x⌋₊ : ℝ) / m ≤ x / m := div_le_div_of_nonneg_right hfl1 hmR.le
  have hupR : (((Icc 1 ⌊x⌋₊).filter (fun n => n % m = n0 % m)).card : ℝ) ≤
      ((⌊x⌋₊ / m : ℕ) : ℝ) + 1 := by exact_mod_cast hup
  have hloR : ((⌊x⌋₊ / m : ℕ) : ℝ) ≤
      (((Icc 1 ⌊x⌋₊).filter (fun n => n % m = n0 % m)).card : ℝ) := by exact_mod_cast hlo
  rw [abs_le]; constructor <;> linarith

/-! ### The multiplicative evaluation on page 49 -/

/-- `h(d) = (d, k)` if `(d, k) ∣ l`, else `0`. -/
def hfun (k l : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else if Nat.gcd d k ∣ l then (Nat.gcd d k : ℝ) else 0, by simp⟩

theorem hfun_apply (k l d : ℕ) (hd : d ≠ 0) :
    hfun k l d = if Nat.gcd d k ∣ l then (Nat.gcd d k : ℝ) else 0 := by
  simp [hfun, hd]

theorem hfun_mult (k l : ℕ) : (hfun k l).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [hfun], fun {m n} hm hn hmn => ?_⟩
  rw [hfun_apply _ _ _ (mul_ne_zero hm hn), hfun_apply _ _ _ hm, hfun_apply _ _ _ hn]
  have hg : Nat.gcd (m * n) k = Nat.gcd m k * Nat.gcd n k := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul k hmn, Nat.gcd_comm k m, Nat.gcd_comm k n]
  have hcop : Nat.Coprime (Nat.gcd m k) (Nat.gcd n k) :=
    Nat.Coprime.of_dvd (Nat.gcd_dvd_left m k) (Nat.gcd_dvd_left n k) hmn
  rw [hg]
  by_cases h1 : Nat.gcd m k ∣ l <;> by_cases h2 : Nat.gcd n k ∣ l
  · rw [if_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2), if_pos h1, if_pos h2]; push_cast; ring
  · rw [if_neg (fun h => h2 ((Nat.dvd_mul_left _ _).trans h)), if_pos h1, if_neg h2]; ring
  · rw [if_neg (fun h => h1 ((Nat.dvd_mul_right _ _).trans h)), if_neg h1]; ring
  · rw [if_neg (fun h => h1 ((Nat.dvd_mul_right _ _).trans h)), if_neg h1]; ring

/-- `G(q) = Σ_{d ∣ q} μ(d) (d,k) [(d,k) ∣ l]`. -/
def Gfun (k l q : ℕ) : ℝ := ∑ d ∈ q.divisors, (μ d : ℝ) * hfun k l d

theorem Gfun_eq_prod (k l q : ℕ) (hq : Squarefree q) :
    Gfun k l q = ∏ p ∈ q.primeFactors, (1 - hfun k l p) := by
  unfold Gfun
  rw [(hfun_mult k l).prodPrimeFactors_one_sub_of_squarefree _ hq]

theorem hfun_prime_not_dvd (k l p : ℕ) (hp : p.Prime) (hpk : ¬ p ∣ k) : hfun k l p = 1 := by
  rw [hfun_apply _ _ _ hp.ne_zero]
  have : Nat.gcd p k = 1 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk)).symm
    |> fun h => by rw [Nat.gcd_comm]; exact (Nat.Coprime.symm (by
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpk))
  rw [this]; simp

theorem hfun_prime_dvd (k l p : ℕ) (hp : p.Prime) (hpk : p ∣ k) :
    hfun k l p = if p ∣ l then (p : ℝ) else 0 := by
  rw [hfun_apply _ _ _ hp.ne_zero, Nat.gcd_eq_left hpk]

/-- `Σ_{q ∣ k, q squarefree} Π_{p ∣ q} c(p) = Π_{p ∣ k} (1 + c(p))`. -/
theorem sum_sqfree_divisors_prod (k : ℕ) (hk : k ≠ 0) (c : ℕ → ℝ) :
    ∑ q ∈ k.divisors.filter Squarefree, ∏ p ∈ q.primeFactors, c p =
      ∏ p ∈ k.primeFactors, (1 + c p) := by
  rw [Nat.sum_divisors_filter_squarefree hk, prod_one_add]
  have e : (UniqueFactorizationMonoid.normalizedFactors k).toFinset = k.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [e]
  apply sum_congr rfl
  intro t ht
  rw [mem_powerset] at ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  have : t.val.prod = ∏ p ∈ t, p := by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  rw [this, Nat.primeFactors_prod hprime]

/-- `q/φ(q) = Π_{p ∣ q} p/(p - 1)`. -/
theorem div_totient_eq_prod (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hP : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have keyR : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    push_cast at this
    rw [this]; congr 1; apply prod_congr rfl; intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [this]; ring
  have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) :=
    prod_pos (fun p hp => by linarith [hP p hp])
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hpos.ne']
  linarith [keyR]

/-- `φ(q) = Π_{p ∣ q} (p - 1)` for squarefree `q`. -/
theorem totient_eq_prod_of_squarefree (q : ℕ) (hq : Squarefree q) :
    (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  have h1 := div_totient_eq_prod q hq1
  have hP : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) :=
    prod_pos (fun p hp => by linarith [hP p hp])
  have hqP : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hq)
    push_cast at this; exact this.symm
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [prod_div_distrib, ← hqP, div_eq_div_iff hφ.ne' hpos.ne'] at h1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  nlinarith

/-- `w(p) = (1 - h(p))/(p - 1)`. -/
def wfun (k l p : ℕ) : ℝ := (1 - hfun k l p) / ((p : ℝ) - 1)

theorem term_eq (k l q : ℕ) (hq : 1 ≤ q) :
    (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * Gfun k l q =
      if Squarefree q then ∏ p ∈ q.primeFactors, wfun k l p else 0 := by
  split_ifs with hsq
  · rw [Gfun_eq_prod k l q hsq, totient_eq_prod_of_squarefree q hsq,
      ArithmeticFunction.moebius_apply_of_squarefree hsq]
    unfold wfun
    rw [prod_div_distrib]
    push_cast
    rw [← pow_mul, show (ArithmeticFunction.cardFactors q * 2) =
      2 * ArithmeticFunction.cardFactors q by ring, pow_mul]
    simp only [neg_one_sq, one_pow, one_div]
    rw [div_eq_inv_mul]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp

theorem prod_wfun_eq_zero (k l q : ℕ) (hk : k ≠ 0) (hq : Squarefree q) (hqk : ¬ q ∣ k) :
    ∏ p ∈ q.primeFactors, wfun k l p = 0 := by
  have : ∃ p ∈ q.primeFactors, ¬ p ∣ k := by
    by_contra h; push_neg at h
    apply hqk
    rw [← Nat.prod_primeFactors_of_squarefree hq]
    exact Finset.prod_primes_dvd k (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) h
  obtain ⟨p, hp, hpk⟩ := this
  apply prod_eq_zero hp
  unfold wfun
  rw [hfun_prime_not_dvd k l p (Nat.prime_of_mem_primeFactors hp) hpk]; simp

theorem full_sum (k l : ℕ) (hk : 1 ≤ k) :
    ∑ q ∈ k.divisors.filter Squarefree, ∏ p ∈ q.primeFactors, wfun k l p =
      if Nat.Coprime l k then (k : ℝ) / (Nat.totient k : ℝ) else 0 := by
  rw [sum_sqfree_divisors_prod k (by omega)]
  have hw : ∀ p ∈ k.primeFactors, 1 + wfun k l p =
      if p ∣ l then 0 else (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpk := Nat.dvd_of_mem_primeFactors hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    unfold wfun
    rw [hfun_prime_dvd k l p hpr hpk]
    split_ifs with h
    · field_simp; ring
    · field_simp; ring
  rw [prod_congr rfl hw]
  split_ifs with hc
  · rw [div_totient_eq_prod k hk]
    apply prod_congr rfl; intro p hp
    rw [if_neg]
    intro hpl
    have hpk := Nat.dvd_of_mem_primeFactors hp
    have h1 := Nat.dvd_gcd hpl hpk
    rw [Nat.Coprime.gcd_eq_one hc] at h1
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp h1)
  · have : ∃ p ∈ k.primeFactors, p ∣ l := by
      by_contra h; push_neg at h
      apply hc
      apply Nat.coprime_of_dvd
      intro p hp hpl hpk
      exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpk, by omega⟩) hpl
    obtain ⟨p, hp, hpl⟩ := this
    exact prod_eq_zero hp (if_pos hpl)

/-- For a squarefree `q ∣ k`: `q |Π_{p ∣ q} w(p)| ≤ (k, l) · q/φ(q)`. -/
theorem q_mul_abs_prod_wfun_le (k l q : ℕ) (hk : 1 ≤ k) (hq : Squarefree q) (hqk : q ∣ k) :
    (q : ℝ) * |∏ p ∈ q.primeFactors, wfun k l p| ≤
      (Nat.gcd k l : ℝ) * ((q : ℝ) / (Nat.totient q : ℝ)) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  have hqP : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hq)
    push_cast at this; exact this.symm
  have hpk : ∀ p ∈ q.primeFactors, p ∣ k := fun p hp => (Nat.dvd_of_mem_primeFactors hp).trans hqk
  have hval : ∀ p ∈ q.primeFactors, (p : ℝ) * |wfun k l p| =
      if p ∣ l then (p : ℝ) else (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    unfold wfun
    rw [hfun_prime_dvd k l p hpr (hpk p hp)]
    split_ifs with h
    · rw [show (1 - (p : ℝ)) / ((p : ℝ) - 1) = -1 by field_simp; ring]; simp
    · rw [sub_zero, abs_of_pos (by apply div_pos one_pos; linarith)]; field_simp
  have hsplit : (q : ℝ) * |∏ p ∈ q.primeFactors, wfun k l p| =
      ∏ p ∈ q.primeFactors, ((p : ℝ) * |wfun k l p|) := by
    rw [abs_prod, hqP, ← prod_mul_distrib]
  rw [hsplit, prod_congr rfl hval, ← prod_filter_mul_prod_filter_not
    q.primeFactors (fun p => p ∣ l)]
  have hA : ∏ p ∈ q.primeFactors.filter (fun p => p ∣ l),
      (if p ∣ l then (p : ℝ) else (p : ℝ) / ((p : ℝ) - 1)) ≤ Nat.gcd k l := by
    rw [prod_congr rfl (fun p hp => if_pos (mem_filter.mp hp).2)]
    have hd : ∏ p ∈ q.primeFactors.filter (fun p => p ∣ l), p ∣ Nat.gcd k l := by
      apply Finset.prod_primes_dvd
      · intro p hp; exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
      · intro p hp
        exact Nat.dvd_gcd (hpk p (mem_filter.mp hp).1) (mem_filter.mp hp).2
    have hg : 0 < Nat.gcd k l := Nat.gcd_pos_of_pos_left l (by omega)
    have := Nat.le_of_dvd hg hd
    have h' : ((∏ p ∈ q.primeFactors.filter (fun p => p ∣ l), p : ℕ) : ℝ) ≤ Nat.gcd k l := by
      exact_mod_cast this
    push_cast at h'; exact h'
  have hB : ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ l),
      (if p ∣ l then (p : ℝ) else (p : ℝ) / ((p : ℝ) - 1)) ≤ (q : ℝ) / (Nat.totient q : ℝ) := by
    rw [prod_congr rfl (fun p hp => if_neg (mem_filter.mp hp).2), div_totient_eq_prod q hq1]
    apply prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _)
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
      apply div_nonneg <;> linarith
    · intro p hp _
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      rw [le_div_iff₀ (by linarith)]; linarith
  have hA0 : 0 ≤ ∏ p ∈ q.primeFactors.filter (fun p => p ∣ l),
      (if p ∣ l then (p : ℝ) else (p : ℝ) / ((p : ℝ) - 1)) := by
    apply prod_nonneg; intro p hp
    have h2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    split_ifs <;> [linarith; (apply div_nonneg <;> linarith)]
  have hB0 : 0 ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ l),
      (if p ∣ l then (p : ℝ) else (p : ℝ) / ((p : ℝ) - 1)) := by
    apply prod_nonneg; intro p hp
    have h2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    split_ifs <;> [linarith; (apply div_nonneg <;> linarith)]
  exact mul_le_mul hA hB hB0 (by positivity)

/-- The tail `Σ_{q ∣ k, q > ⌊Q⌋}`. -/
theorem tail_bound (x Q : ℝ) (hQ : 1 ≤ Q) (k l : ℕ) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x) :
    |∑ q ∈ (k.divisors.filter Squarefree).filter (fun q => ⌊Q⌋₊ < q),
        ∏ p ∈ q.primeFactors, wfun k l p| ≤
      (k.divisors.card : ℝ) * (Nat.gcd k l : ℝ) *
        (Real.exp 1 * (1 + Real.log x / Real.log 2)) / Q := by
  set E := Real.exp 1 * (1 + Real.log x / Real.log 2)
  have hQ0 : 0 < Q := by linarith
  have hE : ∀ q ∈ k.divisors, (q : ℝ) / (Nat.totient q : ℝ) ≤ E := by
    intro q hq
    have hq1 : 1 ≤ q := Nat.pos_of_mem_divisors hq
    have hqk : (q : ℝ) ≤ k := by exact_mod_cast Nat.divisor_le hq
    have := inv_totient_le x q hq1 (hqk.trans hkx)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
    rw [div_eq_mul_inv, mul_comm]
    calc (Nat.totient q : ℝ)⁻¹ * q ≤ E / q * q := mul_le_mul_of_nonneg_right this hqR.le
      _ = E := by field_simp
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ q ∈ (k.divisors.filter Squarefree).filter (fun q => ⌊Q⌋₊ < q),
        (Nat.gcd k l : ℝ) * E / Q := by
        apply sum_le_sum; intro q hq
        simp only [mem_filter] at hq
        obtain ⟨⟨hqd, hsq⟩, hqF⟩ := hq
        have hq1 : 1 ≤ q := Nat.pos_of_mem_divisors hqd
        have hqQ : Q < q := by
          have := Nat.lt_floor_add_one Q
          have : ((⌊Q⌋₊ + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hqF
          push_cast at this; linarith
        have h := q_mul_abs_prod_wfun_le k l q hk hsq (Nat.dvd_of_mem_divisors hqd)
        have hg : (0 : ℝ) ≤ Nat.gcd k l := by positivity
        have h2 : (q : ℝ) * |∏ p ∈ q.primeFactors, wfun k l p| ≤ (Nat.gcd k l : ℝ) * E :=
          h.trans (mul_le_mul_of_nonneg_left (hE q hqd) hg)
        rw [le_div_iff₀ hQ0]
        have h0 := abs_nonneg (∏ p ∈ q.primeFactors, wfun k l p)
        nlinarith
    _ ≤ ∑ q ∈ k.divisors, (Nat.gcd k l : ℝ) * E / Q := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro q hq; exact (mem_filter.mp (mem_filter.mp hq).1).1
        · intro q _ _
          have : 0 ≤ E := by
            have := Real.log_pos one_lt_two
            have h1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hk) hkx
            have := Real.log_nonneg h1
            positivity
          positivity
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- The main term on page 49 to 50: `Σ_{q ≤ Q} μ(q)²/φ(q) G(q) = E_{k,l} k/φ(k) - tail`. -/
theorem main_T (k l : ℕ) (Q : ℝ) (hk : 1 ≤ k) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * Gfun k l q =
      (if Nat.Coprime l k then (k : ℝ) / (Nat.totient k : ℝ) else 0) -
        ∑ q ∈ (k.divisors.filter Squarefree).filter (fun q => ⌊Q⌋₊ < q),
          ∏ p ∈ q.primeFactors, wfun k l p := by
  set F := ⌊Q⌋₊
  rw [← full_sum k l hk, ← sum_filter_add_sum_filter_not (k.divisors.filter Squarefree)
    (fun q => F < q), add_sub_cancel_left]
  rw [sum_congr rfl (fun q hq => term_eq k l q (mem_Icc.mp hq).1), ← sum_filter]
  rw [← sum_filter_of_ne (p := fun q => q ∣ k)]
  · apply sum_congr
    · ext q
      simp only [mem_filter, mem_Icc, Nat.mem_divisors, not_lt]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨⟨h4, by omega⟩, h3⟩, h2⟩
      · rintro ⟨⟨⟨h4, _⟩, h3⟩, h2⟩
        exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr h3.ne_zero, h2⟩, h3⟩, h4⟩
    · intro _ _; rfl
  · intro q hq hne
    by_contra h
    exact hne (prod_wfun_eq_zero k l q (by omega) (mem_filter.mp hq).2 h)

/-- `σ(q) ≤ q (1 + log q)`. -/
theorem sigma_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ d ∈ q.divisors, (d : ℝ) ≤ q * (1 + Real.log q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have e : ∑ d ∈ q.divisors, (d : ℝ) = ∑ d ∈ q.divisors, ((q / d : ℕ) : ℝ) := by
    rw [Nat.sum_div_divisors q (fun d => (d : ℝ))]
  rw [e]
  calc ∑ d ∈ q.divisors, ((q / d : ℕ) : ℝ) = ∑ d ∈ q.divisors, (q : ℝ) * (d : ℝ)⁻¹ := by
        apply sum_congr rfl; intro d hd
        rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast
          (Nat.pos_of_mem_divisors hd).ne')]
        ring
    _ = q * ∑ d ∈ q.divisors, (d : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ q * ∑ d ∈ Icc 1 q, (d : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hqR.le
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro d hd
        simp only [mem_Icc]
        exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    _ ≤ q * (1 + Real.log q) := mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log q) hqR.le

/-! ### Lemma 1 from 2.4 -/

/-- The counting error. -/
def ecnt (x : ℝ) (k l d : ℕ) : ℝ :=
  (cnt x k l d : ℝ) - (if Nat.gcd d k ∣ l then x * Nat.gcd d k / (d * k) else 0)

theorem abs_ecnt_le (x : ℝ) (hx : 1 ≤ x) (k l d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    |ecnt x k l d| ≤ 2 := by
  unfold ecnt
  split_ifs with h
  · exact abs_cnt_sub_le x hx k l d hk hd h
  · rw [cnt_eq_zero x k l d h]; simp

theorem apSum_LambdaQ_eq (x Q : ℝ) (k l : ℕ) :
    apSum (LambdaQ Q) x k l = ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
      ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * (cnt x k l d : ℝ) := by
  unfold apSum LambdaQ
  rw [sum_comm]
  apply sum_congr rfl; intro q hq
  have hq1 := (mem_Icc.mp hq).1
  rw [← mul_sum]; congr 1
  have e1 : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k),
      ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ) =
        ∑ d ∈ q.divisors.filter (· ∣ n), (d : ℝ) * (μ d : ℝ) := by
    intro n hn
    have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    rw [Nat.gcd_comm, divisors_gcd_eq q n hq1 hn1]
  rw [sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := q.divisors)
    (s' := fun d => ((Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k)).filter (d ∣ ·))]
  · apply sum_congr rfl; intro d _
    rw [sum_const, nsmul_eq_mul, cnt, filter_filter]; ring
  · intro n d; simp only [mem_filter]; tauto

theorem apSum_LambdaQ_decomp (x Q : ℝ) (k l : ℕ) (hk : 1 ≤ k) :
    apSum (LambdaQ Q) x k l = x / k * ∑ q ∈ Icc 1 ⌊Q⌋₊,
        (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * Gfun k l q +
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
        ∑ d ∈ q.divisors, (μ d : ℝ) * (d : ℝ) * ecnt x k l d := by
  rw [apSum_LambdaQ_eq, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro q _
  unfold Gfun
  rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro d hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hfun_apply k l d (by omega)]
  unfold ecnt
  split_ifs with h
  · field_simp; ring
  · ring

theorem abs_err_decomp_le (x Q : ℝ) (hx : 1 ≤ x) (k l : ℕ) (hk : 1 ≤ k) :
    |∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
        ∑ d ∈ q.divisors, (μ d : ℝ) * (d : ℝ) * ecnt x k l d| ≤
      2 * ∑ q ∈ Icc 1 ⌊Q⌋₊, (∑ d ∈ q.divisors, (d : ℝ)) / (Nat.totient q : ℝ) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum; intro q hq
  have hq1 := (mem_Icc.mp hq).1
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hμ : (μ q : ℝ) ^ 2 ≤ 1 := by
    have h' : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [abs_nonneg (μ q : ℝ), sq_abs (μ q : ℝ)]
  have hc0 : 0 ≤ (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) := by positivity
  have hc1 : (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤ 1 / (Nat.totient q : ℝ) :=
    div_le_div_of_nonneg_right hμ (by linarith)
  have hin : |∑ d ∈ q.divisors, (μ d : ℝ) * (d : ℝ) * ecnt x k l d| ≤
      2 * ∑ d ∈ q.divisors, (d : ℝ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]; apply sum_le_sum; intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 := abs_ecnt_le x hx k l d hk hd1
    have h3 : (0 : ℝ) ≤ d := by positivity
    calc |(μ d : ℝ)| * (d : ℝ) * |ecnt x k l d| ≤ 1 * (d : ℝ) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) h2 (abs_nonneg _) (by positivity)
      _ = 2 * (d : ℝ) := by ring
  rw [abs_mul, abs_of_nonneg hc0]
  calc (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) * |∑ d ∈ q.divisors, (μ d : ℝ) * (d : ℝ) * ecnt x k l d|
      ≤ 1 / (Nat.totient q : ℝ) * (2 * ∑ d ∈ q.divisors, (d : ℝ)) :=
        mul_le_mul hc1 hin (abs_nonneg _) (by positivity)
    _ = 2 * ((∑ d ∈ q.divisors, (d : ℝ)) / (Nat.totient q : ℝ)) := by ring

/-- The constant of the core estimate. -/
def Kc : ℝ := 4 * Real.exp 1 * (1 + 1 / Real.log 2) / Real.log 2 + 2 * Real.exp 1 / Real.log 2

/-- **The formula after 2.10**: `Σ_{n ≤ x, n ≡ l (k)} Λ_Q(n) = E_{k,l} x/φ(k) + O(QL²) +
O(x L (kQ)⁻¹ (k,l) d(k))`, uniformly for `1 ≤ Q, k ≤ x`. -/
theorem core (x Q : ℝ) (hx2 : 2 ≤ x) (hQ1 : 1 ≤ Q) (hQx : Q ≤ x) (k l : ℕ) (hk : 1 ≤ k)
    (hkx : (k : ℝ) ≤ x) :
    |apSum (LambdaQ Q) x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
      Kc * (Q * Real.log x ^ 2 +
        x * Real.log x / (k * Q) * (Nat.gcd k l : ℝ) * (k.divisors.card : ℝ)) := by
  set L := Real.log x
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx2
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ0 : 0 < Q := by linarith
  set E := Real.exp 1 * (1 + L / l2)
  have he := Real.exp_pos 1
  have hE : E ≤ 2 * Real.exp 1 * L / l2 := by
    have : 1 ≤ L / l2 := by rw [le_div_iff₀ hl2]; linarith
    have e : 2 * Real.exp 1 * L / l2 = Real.exp 1 * (L / l2 + L / l2) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) he.le
  have hE0 : 0 ≤ E := by positivity
  have hdec := apSum_LambdaQ_decomp x Q k l hk
  rw [main_T k l Q hk] at hdec
  set F := ⌊Q⌋₊
  have hF : (F : ℝ) ≤ Q := Nat.floor_le hQ0.le
  set tail := ∑ q ∈ (k.divisors.filter Squarefree).filter (fun q => F < q),
    ∏ p ∈ q.primeFactors, wfun k l p
  set Err := ∑ q ∈ Icc 1 F, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
    ∑ d ∈ q.divisors, (μ d : ℝ) * (d : ℝ) * ecnt x k l d
  have hmain : apSum (LambdaQ Q) x k l -
      (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0) = -(x / k * tail) + Err := by
    rw [hdec]
    split_ifs with hc
    · have hφ : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      field_simp; ring
    · ring
  rw [hmain]
  have htail := tail_bound x Q hQ1 k l hk hkx
  have herr := abs_err_decomp_le x Q (by linarith) k l hk
  have hsig : ∑ q ∈ Icc 1 F, (∑ d ∈ q.divisors, (d : ℝ)) / (Nat.totient q : ℝ) ≤
      Q * ((1 + L) * E) := by
    calc _ ≤ ∑ q ∈ Icc 1 F, (1 + L) * E := by
          apply sum_le_sum; intro q hq
          have hq1 := (mem_Icc.mp hq).1
          have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
          have hqx : (q : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (hF.trans hQx)
          have h1 := sigma_le q hq1
          have h2 := inv_totient_le x q hq1 hqx
          have hlq : Real.log q ≤ L := Real.log_le_log hqR hqx
          have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
          rw [div_eq_mul_inv]
          calc (∑ d ∈ q.divisors, (d : ℝ)) * (Nat.totient q : ℝ)⁻¹
              ≤ (q * (1 + Real.log q)) * (E / q) :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = (1 + Real.log q) * E := by field_simp
            _ ≤ (1 + L) * E := mul_le_mul_of_nonneg_right (by linarith) hE0
      _ = (F : ℝ) * ((1 + L) * E) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ Q * ((1 + L) * E) := mul_le_mul_of_nonneg_right hF (by positivity)
  have h1L : 1 + L ≤ (1 + 1 / l2) * L := by
    have : 1 ≤ L / l2 := by rw [le_div_iff₀ hl2]; linarith
    have e : (1 + 1 / l2) * L = L + L / l2 := by field_simp
    linarith
  have hErr : |Err| ≤ 4 * Real.exp 1 * (1 + 1 / l2) / l2 * (Q * L ^ 2) := by
    refine herr.trans ?_
    calc 2 * ∑ q ∈ Icc 1 F, (∑ d ∈ q.divisors, (d : ℝ)) / (Nat.totient q : ℝ)
        ≤ 2 * (Q * ((1 + L) * E)) := by linarith
      _ ≤ 2 * (Q * (((1 + 1 / l2) * L) * (2 * Real.exp 1 * L / l2))) := by
          gcongr
      _ = _ := by ring
  have hT : |x / k * tail| ≤ 2 * Real.exp 1 / l2 *
      (x * L / (k * Q) * (Nat.gcd k l : ℝ) * (k.divisors.card : ℝ)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < x / k)]
    calc x / k * |tail| ≤ x / k * ((k.divisors.card : ℝ) * (Nat.gcd k l : ℝ) * E / Q) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ x / k * ((k.divisors.card : ℝ) * (Nat.gcd k l : ℝ) * (2 * Real.exp 1 * L / l2) / Q) := by
          gcongr
      _ = _ := by field_simp
  calc |-(x / k * tail) + Err| ≤ |x / k * tail| + |Err| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ ≤ 2 * Real.exp 1 / l2 * (x * L / (k * Q) * (Nat.gcd k l : ℝ) * (k.divisors.card : ℝ)) +
        4 * Real.exp 1 * (1 + 1 / l2) / l2 * (Q * L ^ 2) := add_le_add hT hErr
    _ ≤ Kc * (Q * L ^ 2 + x * L / (k * Q) * (Nat.gcd k l : ℝ) * (k.divisors.card : ℝ)) := by
        unfold Kc
        have hA : 0 ≤ 4 * Real.exp 1 * (1 + 1 / l2) / l2 := by positivity
        have hB : 0 ≤ 2 * Real.exp 1 / l2 := by positivity
        have hX : 0 ≤ Q * L ^ 2 := by positivity
        have hY : 0 ≤ x * L / (k * Q) * (Nat.gcd k l : ℝ) * (k.divisors.card : ℝ) := by positivity
        nlinarith

/-- **Lemma 1, 2.6, proved.** -/
theorem lemma1_6 : Lemma1_6 := by
  refine ⟨Kc, fun x hx Q hQ1 hQx k l hk hkx hcop => ?_⟩
  have h := core x Q hx hQ1 hQx k l hk hkx
  rw [if_pos hcop, Nat.Coprime.gcd_eq_one hcop.symm] at h
  simpa using h

/-- 2.4: the Siegel-Walfisz theorem in the form used on page 48, for `1 ≤ k ≤ x`. -/
def Bound2_4 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
    |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
      K * x * Real.log x ^ (-A)

/-- **Lemma 1, 2.7, from 2.4.** -/
theorem lemma1_7_of (h4 : Bound2_4) : Lemma1_7 := by
  intro A hA
  obtain ⟨K4, hK4⟩ := h4 A hA
  refine ⟨Kc + |K4|, fun x hx Q hQ1 hQx k l hk hkx => ?_⟩
  have h1 := core x Q hx hQ1 hQx k l hk hkx
  have h2 := hK4 x hx k l hk hkx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hKc : 0 ≤ Kc := by unfold Kc; have := Real.log_pos one_lt_two; positivity
  have e : apSum (DeltaQ Q) x k l = (apSum (LambdaQ Q) x k l -
      (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)) -
      (psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)) := by
    rw [apSum_DeltaQ]; ring
  rw [e]
  have hX : 0 ≤ Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (Nat.gcd k l : ℝ) *
      (k.divisors.card : ℝ) := by positivity
  have hY : 0 ≤ x * Real.log x ^ (-A) := by positivity
  have h2' : |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
      |K4| * (x * Real.log x ^ (-A)) := by
    refine h2.trans ?_
    calc K4 * x * Real.log x ^ (-A) = K4 * (x * Real.log x ^ (-A)) := by ring
      _ ≤ |K4| * (x * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right (le_abs_self _) hY
  calc _ ≤ _ := abs_sub _ _
    _ ≤ Kc * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (Nat.gcd k l : ℝ) *
          (k.divisors.card : ℝ)) + |K4| * (x * Real.log x ^ (-A)) := add_le_add h1 h2'
    _ ≤ _ := by
        have hK4 := abs_nonneg K4
        nlinarith

/-- **Theorem 2 of Heath-Brown 1985 from 2.4 alone**, the Siegel-Walfisz theorem in the form
used on page 48. Fully proved. -/
theorem theorem2_of_bound2_4 (h4 : Bound2_4) : Theorem2 :=
  theorem2_of_lemma1_only lemma1_6 (lemma1_7_of h4)

end LeanLab.HeathBrown1985
