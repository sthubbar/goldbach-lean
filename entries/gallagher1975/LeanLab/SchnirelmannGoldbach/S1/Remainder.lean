module

public import LeanLab.SchnirelmannGoldbach.S1.Setup

/-!
AI-written Lean code, Claude, 2026-10-16.
S1 remainder: the sieve remainder for Goldbach representations is at most `2^ω(d)`,
via a CRT count of the roots of `x (n - x)` modulo squarefree `d`.
-/

@[expose] public section

open Finset
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace LeanLab.SchnirelmannGoldbach.S1

/-- The root predicate `m (n - m) ≡ 0 (mod d)`, stated in `ZMod d`. -/
def rootPred (n d m : ℕ) : Prop := (m : ZMod d) * ((n : ZMod d) - m) = 0

instance (n d : ℕ) : DecidablePred (rootPred n d) := fun m => by
  unfold rootPred; infer_instance

/-- Number of roots of `x (n - x)` modulo `d`. -/
def cnt (n d : ℕ) : ℕ := #{m ∈ range d | rootPred n d m}

lemma rootPred_periodic (n d : ℕ) : Function.Periodic (rootPred n d) d := by
  intro m
  simp [rootPred]

lemma card_zmod_roots (n d : ℕ) [NeZero d] :
    cnt n d = Fintype.card {x : ZMod d // x * ((n : ZMod d) - x) = 0} := by
  rw [Fintype.card_subtype, cnt]
  refine Finset.card_bij (fun m _ => (m : ZMod d)) ?_ ?_ ?_
  · intro m hm
    simp only [mem_filter, mem_range] at hm
    simpa [rootPred] using hm.2
  · intro a ha b hb hab
    simp only [mem_filter, mem_range] at ha hb
    have := congrArg ZMod.val hab
    simpa [ZMod.val_cast_of_lt ha.1, ZMod.val_cast_of_lt hb.1] using this
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
      ZMod.natCast_zmod_val x⟩
    simp only [mem_filter, mem_univ, true_and] at hx
    simpa [rootPred] using hx

lemma cnt_mul {n a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    cnt n (a * b) = cnt n a * cnt n b := by
  have : NeZero a := ⟨ha⟩
  have : NeZero b := ⟨hb⟩
  have : NeZero (a * b) := ⟨mul_ne_zero ha hb⟩
  rw [card_zmod_roots, card_zmod_roots, card_zmod_roots, ← Fintype.card_prod]
  let e := ZMod.chineseRemainder hab
  refine Fintype.card_congr ((e.toEquiv.subtypeEquiv (q := fun y : ZMod a × ZMod b =>
      y.1 * ((n : ZMod a) - y.1) = 0 ∧ y.2 * ((n : ZMod b) - y.2) = 0) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun x : ZMod a => x * ((n : ZMod a) - x) = 0)
      (q := fun x : ZMod b => x * ((n : ZMod b) - x) = 0)))
  intro x
  have h1 : e (x * ((n : ZMod (a * b)) - x)) = e x * ((n : ZMod a × ZMod b) - e x) := by
    rw [map_mul, map_sub, map_natCast]
  constructor
  · intro hx
    have : e (x * ((n : ZMod (a * b)) - x)) = 0 := by rw [hx, map_zero]
    rw [h1, Prod.ext_iff] at this
    simpa using this
  · intro hx
    have : e (x * ((n : ZMod (a * b)) - x)) = 0 := by
      rw [h1, Prod.ext_iff]; simpa using hx
    exact (map_eq_zero_iff e e.injective).mp this

lemma cnt_prime {n p : ℕ} (hp : p.Prime) : (cnt n p : ℝ) = wt n p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [card_zmod_roots, Fintype.card_subtype]
  have hset : ({x ∈ (univ : Finset (ZMod p)) | x * ((n : ZMod p) - x) = 0}) =
      {0, (n : ZMod p)} := by
    ext x
    simp [mul_eq_zero, sub_eq_zero, eq_comm]
  rw [hset, wt]
  by_cases h : p ∣ n
  · have : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr h
    simp [this, h]
  · have : (0 : ZMod p) ≠ n := fun h' => h ((ZMod.natCast_eq_zero_iff n p).mp h'.symm)
    rw [Finset.card_pair this]; simp [h]

lemma cnt_prod_primes (n : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (cnt n (∏ p ∈ s, p) : ℝ) = ∏ p ∈ s, wt n p := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, Nat.cast_eq_one]
    rw [cnt, Finset.filter_true_of_mem]
    · simp
    intro m hm
    simp only [mem_range, Nat.lt_one_iff] at hm
    subst hm; simp [rootPred]
  | insert p s hps ih =>
    rw [prod_insert hps, prod_insert hps]
    have hp := hs p (mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp (hs' q hq)).mpr (fun h => hps (h ▸ hq))
    have hne : (∏ q ∈ s, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hs' q hq).ne_zero
    rw [cnt_mul hp.ne_zero hne hcop, Nat.cast_mul, cnt_prime hp, ih hs']

lemma cnt_squarefree {n d : ℕ} (hd : Squarefree d) :
    (cnt n d : ℝ) = ∏ p ∈ d.primeFactors, wt n p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact cnt_prod_primes n _ fun p hp => Nat.prime_of_mem_primeFactors hp

lemma rhoN_squarefree {n d : ℕ} (hd : Squarefree d) :
    rhoN n d = ∏ p ∈ d.primeFactors, wt n p := by
  rw [← LeanLab.PNTSieve.Aux.prod_factors_of_mult _ (rhoN_compMult n).isMultiplicative hd]
  exact Finset.prod_congr rfl fun p hp => rhoN_prime (Nat.prime_of_mem_primeFactors hp)

lemma cnt_le_two_pow {n d : ℕ} (hd : Squarefree d) : (cnt n d : ℝ) ≤ 2 ^ ω d := by
  rw [cnt_squarefree hd]
  have : ω d = #d.primeFactors := by rw [ArithmeticFunction.cardDistinctFactors_apply]; rfl
  rw [this, ← Finset.prod_const]
  exact prod_le_prod₀ (fun p _ => (wt_pos n p).le) (fun p _ => wt_le_two n p)

/-- Counting a periodic predicate on `[0, N)`. -/
lemma count_periodic_approx (Q : ℕ → Prop) [DecidablePred Q] {d : ℕ} (hd : 0 < d)
    (hQ : Function.Periodic Q d) (N : ℕ) :
    |(#{m ∈ range N | Q m} : ℝ) - #{m ∈ range d | Q m} * N / d| ≤ #{m ∈ range d | Q m} := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  have hshift : ∀ a : ℕ, Nat.count (fun k => Q (a * d + k)) d = Nat.count Q d := by
    intro a
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    have := Nat.filter_Ico_card_eq_of_periodic (a * d) d Q hQ
    rw [Nat.count_eq_card_filter_range] at this
    rw [← this]
    apply Finset.card_bij (fun k _ => a * d + k)
    · intro k hk
      simp only [mem_filter, mem_range, mem_Ico] at hk ⊢
      exact ⟨⟨by omega, by omega⟩, hk.2⟩
    · intro x _ y _ h; simpa using h
    · intro y hy
      simp only [mem_filter, mem_range, mem_Ico] at hy
      refine ⟨y - a * d, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      rw [show a * d + (y - a * d) = y by omega]; exact hy.2
  set c := Nat.count Q d
  have hfull : ∀ q : ℕ, Nat.count Q (q * d) = q * c := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [add_mul, one_mul, Nat.count_add, ih, hshift, add_mul, one_mul]
  have hN : N = N / d * d + N % d := (Nat.div_add_mod' N d).symm
  have hsplit := Nat.count_add Q (N / d * d) (N % d)
  rw [← hN, hfull] at hsplit
  have hle : Nat.count (fun k => Q (N / d * d + k)) (N % d) ≤ c := by
    rw [← hshift (N / d)]
    exact Nat.count_monotone _ (Nat.mod_lt N hd).le
  set e := Nat.count (fun k => Q (N / d * d + k)) (N % d)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (N : ℝ) = (N / d : ℕ) * d + (N % d : ℕ) := by exact_mod_cast hN
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have hr0 : (0 : ℝ) ≤ (N % d : ℕ) := Nat.cast_nonneg _
  have hcN : (c : ℝ) * N / d = (N / d : ℕ) * c + c * ((N % d : ℕ) / d) := by
    rw [hNR]; field_simp
  rw [hsplit, hcN]
  push_cast
  have hfrac0 : 0 ≤ ((N % d : ℕ) : ℝ) / d := div_nonneg hr0 hdR.le
  have hfrac1 : ((N % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hdR).mpr hr.le
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have heR : (e : ℝ) ≤ c := by exact_mod_cast hle
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

variable {n : ℕ} {hn : Even n} {z : ℝ} {hz : 1 ≤ z}

lemma dvd_iff_rootPred {n d m : ℕ} (hm : m ≤ n) : d ∣ m * (n - m) ↔ rootPred n d m := by
  rw [rootPred, ← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_sub hm]

/-- The sieve remainder is at most `2^ω(d)` for squarefree `d`. -/
theorem abs_rem_gSieve_le {d : ℕ} (hd : Squarefree d) :
    |rem (s := (gSieve n hn z hz).toBoundingSieve) d| ≤ 2 ^ ω d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  rw [rem_gSieve]
  have hcongr : (#{m ∈ range n | d ∣ m * (n - m)}) = #{m ∈ range n | rootPred n d m} := by
    congr 1
    apply Finset.filter_congr
    intro m hm
    exact dvd_iff_rootPred (by simp at hm; omega)
  rw [hcongr]
  have hnu : nuN n d * n = (cnt n d : ℝ) * n / d := by
    rw [nuN_apply, rhoN_squarefree hd, ← cnt_squarefree hd]; ring
  rw [hnu]
  exact (count_periodic_approx (rootPred n d) hd0 (rootPred_periodic n d) n).trans
    (cnt_le_two_pow hd)

/-- The error sum in the Selberg bound. -/
theorem errSum_gSieve_le :
    ∑ d ∈ (gSieve n hn z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d * |rem (s := (gSieve n hn z hz).toBoundingSieve) d|
          else 0) ≤ z * (1 + Real.log z) ^ 6 := by
  have hP : Squarefree (gSieve n hn z hz).prodPrimes := (gSieve n hn z hz).prodPrimes_squarefree
  calc _ ≤ ∑ d ∈ (gSieve n hn z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then ((6 : ℕ) : ℝ) ^ ω d else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs
        · have hsq : Squarefree d := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
          calc (3 : ℝ) ^ ω d * |rem (s := (gSieve n hn z hz).toBoundingSieve) d|
              ≤ 3 ^ ω d * 2 ^ ω d := by gcongr; exact abs_rem_gSieve_le hsq
            _ = ((6 : ℕ) : ℝ) ^ ω d := by rw [← mul_pow]; norm_num
        · rfl
    _ ≤ z * (1 + Real.log z) ^ 6 :=
        LeanLab.PNTSieve.Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow z hz hP

end LeanLab.SchnirelmannGoldbach.S1
