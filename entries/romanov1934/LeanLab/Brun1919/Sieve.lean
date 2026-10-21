module

public import LeanLab.SchnirelmannGoldbach.S1.Final
public import LeanLab.Brun1919.Statements

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Selberg sieve upper bound for twin primes, built on the Goldbach sieve of
`LeanLab.SchnirelmannGoldbach.S1`. We sift `{m (m + 2) : m < N}` by the primes up to `z`.
The local densities are those of the Goldbach sieve for `n = 2`: one root mod 2,
two roots mod every odd prime.
-/

@[expose] public section

open Finset
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace LeanLab.Brun1919

/-- The Selberg sieve for twin primes below `N`. -/
def tSieve (N : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (range N).image (fun m => m * (m + 2))
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun k => (#{m ∈ range N | m * (m + 2) = k} : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := N
  nu := nuN 2
  nu_mult := (nuN_compMult 2).isMultiplicative
  nu_pos_of_prime := fun p hp _ => by
    rw [nuN_prime hp]; exact div_pos (wt_pos 2 p) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => nuN_lt_one even_two hp
  level := z
  one_le_level := hz

variable {N : ℕ} {z : ℝ} {hz : 1 ≤ z}

lemma siftedSum_tSieve :
    siftedSum (s := (tSieve N z hz).toBoundingSieve) =
      (#{m ∈ range N | Nat.Coprime (primorial ⌊z⌋₊) (m * (m + 2))} : ℝ) := by
  unfold siftedSum
  exact sum_image_fiber N (fun m => m * (m + 2)) _

lemma multSum_tSieve (d : ℕ) :
    multSum (s := (tSieve N z hz).toBoundingSieve) d =
      (#{m ∈ range N | d ∣ m * (m + 2)} : ℝ) := by
  unfold multSum
  exact sum_image_fiber N (fun m => m * (m + 2)) _

lemma rem_tSieve (d : ℕ) :
    rem (s := (tSieve N z hz).toBoundingSieve) d =
      (#{m ∈ range N | d ∣ m * (m + 2)} : ℝ) - nuN 2 d * N := by
  unfold rem
  rw [multSum_tSieve]
  rfl

/-- The twin root predicate `m (m + 2) ≡ 0 (mod d)`. -/
def tPred (d m : ℕ) : Prop := (m : ZMod d) * ((m : ZMod d) + 2) = 0

instance (d : ℕ) : DecidablePred (tPred d) := fun m => by unfold tPred; infer_instance

lemma tPred_periodic (d : ℕ) : Function.Periodic (tPred d) d := by
  intro m; simp [tPred]

lemma dvd_iff_tPred {d m : ℕ} : d ∣ m * (m + 2) ↔ tPred d m := by
  rw [tPred, ← ZMod.natCast_eq_zero_iff]; push_cast; rfl

lemma card_tPred_eq_cnt (d : ℕ) (hd : 0 < d) : #{m ∈ range d | tPred d m} = cnt 2 d := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [card_zmod_roots]
  have h1 : #{m ∈ range d | tPred d m} =
      Fintype.card {x : ZMod d // x * (x + 2) = 0} := by
    rw [Fintype.card_subtype]
    refine Finset.card_bij (fun m _ => (m : ZMod d)) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      simpa [tPred] using hm.2
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      have := congrArg ZMod.val hab
      simpa [ZMod.val_cast_of_lt ha.1, ZMod.val_cast_of_lt hb.1] using this
    · intro x hx
      refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
        ZMod.natCast_zmod_val x⟩
      simp only [mem_filter, mem_univ, true_and] at hx
      simpa [tPred] using hx
  rw [h1]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.neg (ZMod d)) ?_)
  intro x
  simp only [Equiv.neg_apply, Nat.cast_ofNat]
  constructor
  · intro h; linear_combination (-1 : ZMod d) * h
  · intro h; linear_combination (-1 : ZMod d) * h

/-- The twin sieve remainder is at most `2^ω(d)` for squarefree `d`. -/
theorem abs_rem_tSieve_le {d : ℕ} (hd : Squarefree d) :
    |rem (s := (tSieve N z hz).toBoundingSieve) d| ≤ 2 ^ ω d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  rw [rem_tSieve]
  have hcongr : (#{m ∈ range N | d ∣ m * (m + 2)}) = #{m ∈ range N | tPred d m} := by
    congr 1
    exact Finset.filter_congr fun m _ => dvd_iff_tPred
  rw [hcongr]
  have hnu : nuN 2 d * N = (#{m ∈ range d | tPred d m} : ℝ) * N / d := by
    rw [card_tPred_eq_cnt d hd0, nuN_apply, rhoN_squarefree hd, ← cnt_squarefree hd]; ring
  rw [hnu]
  refine (count_periodic_approx (tPred d) hd0 (tPred_periodic d) N).trans ?_
  rw [card_tPred_eq_cnt d hd0]
  exact cnt_le_two_pow hd

theorem errSum_tSieve_le :
    ∑ d ∈ (tSieve N z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d * |rem (s := (tSieve N z hz).toBoundingSieve) d|
          else 0) ≤ z * (1 + Real.log z) ^ 6 := by
  have hP : Squarefree (tSieve N z hz).prodPrimes := (tSieve N z hz).prodPrimes_squarefree
  calc _ ≤ ∑ d ∈ (tSieve N z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then ((6 : ℕ) : ℝ) ^ ω d else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs
        · have hsq : Squarefree d := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
          calc (3 : ℝ) ^ ω d * |rem (s := (tSieve N z hz).toBoundingSieve) d|
              ≤ 3 ^ ω d * 2 ^ ω d := by gcongr; exact abs_rem_tSieve_le hsq
            _ = ((6 : ℕ) : ℝ) ^ ω d := by rw [← mul_pow]; norm_num
        · rfl
    _ ≤ z * (1 + Real.log z) ^ 6 :=
        LeanLab.PNTSieve.Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow z hz hP

/-- The twin sieve has the same Selberg bounding sum as the Goldbach sieve for `n = 2`. -/
lemma boundingSum_tSieve_eq :
    selbergBoundingSum (tSieve N z hz) = selbergBoundingSum (gSieve 2 even_two z hz) := rfl

lemma singProd_two : singProd 2 = 3 / 2 := by
  unfold singProd; rw [Nat.Prime.primeFactors Nat.prime_two]; norm_num

theorem boundingSum_tSieve_ge :
    Real.log z ^ 2 / 48 ≤ selbergBoundingSum (tSieve N z hz) := by
  rw [boundingSum_tSieve_eq]
  have := boundingSum_gSieve_ge 2 even_two two_ne_zero z hz
  rw [singProd_two] at this
  convert this using 2; norm_num

/-- Twin primes above `z` survive the sieve. -/
lemma twinCount_le_siftedSum (N : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (twinCount N : ℝ) ≤ siftedSum (s := (tSieve N z hz).toBoundingSieve) + (z + 1) := by
  rw [siftedSum_tSieve]
  set Z := ⌊z⌋₊
  have hsub : {p ∈ range N | IsTwin p} ⊆
      {m ∈ range N | Nat.Coprime (primorial Z) (m * (m + 2))} ∪ range (Z + 1) := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpN, hp, hq⟩ := hp
    simp only [mem_union, mem_filter, mem_range]
    by_cases h1 : p ≤ Z
    · right; omega
    left
    refine ⟨hpN, Nat.Coprime.mul_right ?_ ?_⟩
    · exact (hp.coprime_iff_not_dvd.mpr fun h =>
        h1 ((prime_dvd_primorial_iff _ _ hp).mp h)).symm
    · exact (hq.coprime_iff_not_dvd.mpr fun h =>
        h1 (by have := (prime_dvd_primorial_iff _ _ hq).mp h; omega)).symm
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le {m ∈ range N | Nat.Coprime (primorial Z) (m * (m + 2))}
    (range (Z + 1))
  simp only [card_range] at hc2
  have hZ : (Z : ℝ) ≤ z := Nat.floor_le (by linarith)
  have : (twinCount N : ℝ) ≤
      (#{m ∈ range N | Nat.Coprime (primorial Z) (m * (m + 2))} : ℝ) + ((Z + 1 : ℕ) : ℝ) := by
    unfold twinCount; exact_mod_cast (by omega : _ ≤ _)
  push_cast at this
  linarith

/-- **Selberg sieve bound for twin primes** at level `z > 1`. -/
theorem twinCount_le (N : ℕ) {z : ℝ} (hz : 1 < z) :
    (twinCount N : ℝ) ≤ 48 * N / Real.log z ^ 2 + z * (1 + Real.log z) ^ 6 + (z + 1) := by
  have h1 := twinCount_le_siftedSum N z hz.le
  have h2 : siftedSum (s := (tSieve N z hz.le).toBoundingSieve) ≤
      (N : ℝ) / selbergBoundingSum (tSieve N z hz.le) +
      ∑ d ∈ (tSieve N z hz.le).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d *
          |rem (s := (tSieve N z hz.le).toBoundingSieve) d| else 0) :=
    LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple (tSieve N z hz.le)
  have h3 := errSum_tSieve_le (N := N) (z := z) (hz := hz.le)
  have h4 := boundingSum_tSieve_ge (N := N) (z := z) (hz := hz.le)
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hlow : 0 < Real.log z ^ 2 / 48 := by positivity
  have h5 : (N : ℝ) / selbergBoundingSum (tSieve N z hz.le) ≤ (N : ℝ) / (Real.log z ^ 2 / 48) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlow h4
  have h6 : (N : ℝ) / (Real.log z ^ 2 / 48) = 48 * N / Real.log z ^ 2 := by field_simp
  linarith

end LeanLab.Brun1919
