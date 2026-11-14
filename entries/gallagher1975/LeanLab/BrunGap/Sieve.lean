module

public import LeanLab.SchnirelmannGoldbach.S1.Final

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Selberg sieve upper bound for prime pairs (p, p + h) with even gap h, via the Goldbach sieve.
-/

@[expose] public section

open Finset
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace LeanLab.BrunGap

/-- The number of primes `p < N` with `p + h` prime. -/
def gapCount (h N : ℕ) : ℕ := #{p ∈ range N | p.Prime ∧ (p + h).Prime}

/-- The Selberg sieve for prime pairs `(p, p + h)` below `N`, sifting `{m (m + h) : m < N}`. -/
def hSieve (h : ℕ) (hh : Even h) (N : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (range N).image (fun m => m * (m + h))
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun k => (#{m ∈ range N | m * (m + h) = k} : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := N
  nu := nuN h
  nu_mult := (nuN_compMult h).isMultiplicative
  nu_pos_of_prime := fun p hp _ => by
    rw [nuN_prime hp]; exact div_pos (wt_pos h p) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => nuN_lt_one hh hp
  level := z
  one_le_level := hz

variable {h : ℕ} {hh : Even h} {N : ℕ} {z : ℝ} {hz : 1 ≤ z}

lemma siftedSum_hSieve :
    siftedSum (s := (hSieve h hh N z hz).toBoundingSieve) =
      (#{m ∈ range N | Nat.Coprime (primorial ⌊z⌋₊) (m * (m + h))} : ℝ) := by
  unfold siftedSum
  exact sum_image_fiber N (fun m => m * (m + h)) _

lemma multSum_hSieve (d : ℕ) :
    multSum (s := (hSieve h hh N z hz).toBoundingSieve) d =
      (#{m ∈ range N | d ∣ m * (m + h)} : ℝ) := by
  unfold multSum
  exact sum_image_fiber N (fun m => m * (m + h)) _

lemma rem_hSieve (d : ℕ) :
    rem (s := (hSieve h hh N z hz).toBoundingSieve) d =
      (#{m ∈ range N | d ∣ m * (m + h)} : ℝ) - nuN h d * N := by
  unfold rem
  rw [multSum_hSieve]
  rfl

/-- The root predicate `m (m + h) ≡ 0 (mod d)`. -/
def hPred (h d m : ℕ) : Prop := (m : ZMod d) * ((m : ZMod d) + h) = 0

instance (h d : ℕ) : DecidablePred (hPred h d) := fun m => by unfold hPred; infer_instance

lemma hPred_periodic (h d : ℕ) : Function.Periodic (hPred h d) d := by
  intro m; simp [hPred]

lemma dvd_iff_hPred {h d m : ℕ} : d ∣ m * (m + h) ↔ hPred h d m := by
  rw [hPred, ← ZMod.natCast_eq_zero_iff]; push_cast; rfl

/-- Roots of `x (x + h)` biject with roots of `x (h - x)` via `x ↦ -x`. -/
lemma card_hPred_eq_cnt (h d : ℕ) (hd : 0 < d) : #{m ∈ range d | hPred h d m} = cnt h d := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [card_zmod_roots]
  have h1 : #{m ∈ range d | hPred h d m} =
      Fintype.card {x : ZMod d // x * (x + h) = 0} := by
    rw [Fintype.card_subtype]
    refine Finset.card_bij (fun m _ => (m : ZMod d)) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      simpa [hPred] using hm.2
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      have := congrArg ZMod.val hab
      simpa [ZMod.val_cast_of_lt ha.1, ZMod.val_cast_of_lt hb.1] using this
    · intro x hx
      refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
        ZMod.natCast_zmod_val x⟩
      simp only [mem_filter, mem_univ, true_and] at hx
      simpa [hPred] using hx
  rw [h1]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.neg (ZMod d)) ?_)
  intro x
  simp only [Equiv.neg_apply]
  constructor
  · intro hx; linear_combination (-1 : ZMod d) * hx
  · intro hx; linear_combination (-1 : ZMod d) * hx

/-- The gap sieve remainder is at most `2^ω(d)` for squarefree `d`. -/
theorem abs_rem_hSieve_le {d : ℕ} (hd : Squarefree d) :
    |rem (s := (hSieve h hh N z hz).toBoundingSieve) d| ≤ 2 ^ ω d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  rw [rem_hSieve]
  have hcongr : (#{m ∈ range N | d ∣ m * (m + h)}) = #{m ∈ range N | hPred h d m} := by
    congr 1
    exact Finset.filter_congr fun m _ => dvd_iff_hPred
  rw [hcongr]
  have hnu : nuN h d * N = (#{m ∈ range d | hPred h d m} : ℝ) * N / d := by
    rw [card_hPred_eq_cnt h d hd0, nuN_apply, rhoN_squarefree hd, ← cnt_squarefree hd]; ring
  rw [hnu]
  refine (count_periodic_approx (hPred h d) hd0 (hPred_periodic h d) N).trans ?_
  rw [card_hPred_eq_cnt h d hd0]
  exact cnt_le_two_pow hd

theorem errSum_hSieve_le :
    ∑ d ∈ (hSieve h hh N z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d * |rem (s := (hSieve h hh N z hz).toBoundingSieve) d|
          else 0) ≤ z * (1 + Real.log z) ^ 6 := by
  have hP : Squarefree (hSieve h hh N z hz).prodPrimes := (hSieve h hh N z hz).prodPrimes_squarefree
  calc _ ≤ ∑ d ∈ (hSieve h hh N z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then ((6 : ℕ) : ℝ) ^ ω d else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs
        · have hsq : Squarefree d := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
          calc (3 : ℝ) ^ ω d * |rem (s := (hSieve h hh N z hz).toBoundingSieve) d|
              ≤ 3 ^ ω d * 2 ^ ω d := by gcongr; exact abs_rem_hSieve_le hsq
            _ = ((6 : ℕ) : ℝ) ^ ω d := by rw [← mul_pow]; norm_num
        · rfl
    _ ≤ z * (1 + Real.log z) ^ 6 :=
        LeanLab.PNTSieve.Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow z hz hP

/-- The gap sieve has the same Selberg bounding sum as the Goldbach sieve for `n = h`. -/
lemma boundingSum_hSieve_eq :
    selbergBoundingSum (hSieve h hh N z hz) = selbergBoundingSum (gSieve h hh z hz) := rfl

theorem boundingSum_hSieve_ge (hh0 : h ≠ 0) :
    Real.log z ^ 2 / (32 * singProd h) ≤ selbergBoundingSum (hSieve h hh N z hz) :=
  boundingSum_gSieve_ge h hh hh0 z hz

/-- Prime pairs with `p > z` survive the sieve. -/
lemma gapCount_le_siftedSum (h : ℕ) (hh : Even h) (N : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (gapCount h N : ℝ) ≤ siftedSum (s := (hSieve h hh N z hz).toBoundingSieve) + (z + 1) := by
  rw [siftedSum_hSieve]
  set Z := ⌊z⌋₊
  have hsub : {p ∈ range N | p.Prime ∧ (p + h).Prime} ⊆
      {m ∈ range N | Nat.Coprime (primorial Z) (m * (m + h))} ∪ range (Z + 1) := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpN, hp, hq⟩ := hp
    simp only [mem_union, mem_filter, mem_range]
    by_cases h1 : p ≤ Z
    · right; omega
    left
    refine ⟨hpN, Nat.Coprime.mul_right ?_ ?_⟩
    · exact (hp.coprime_iff_not_dvd.mpr fun h' =>
        h1 ((prime_dvd_primorial_iff _ _ hp).mp h')).symm
    · exact (hq.coprime_iff_not_dvd.mpr fun h' =>
        h1 (by have := (prime_dvd_primorial_iff _ _ hq).mp h'; omega)).symm
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le {m ∈ range N | Nat.Coprime (primorial Z) (m * (m + h))}
    (range (Z + 1))
  simp only [card_range] at hc2
  have hZ : (Z : ℝ) ≤ z := Nat.floor_le (by linarith)
  have : (gapCount h N : ℝ) ≤
      (#{m ∈ range N | Nat.Coprime (primorial Z) (m * (m + h))} : ℝ) + ((Z + 1 : ℕ) : ℝ) := by
    unfold gapCount; exact_mod_cast (by omega : _ ≤ _)
  push_cast at this
  linarith

/-- **Selberg sieve bound for prime pairs `(p, p + h)`** at level `z > 1`. -/
theorem gapCount_le (h N : ℕ) (hh : Even h) (hh0 : h ≠ 0) {z : ℝ} (hz : 1 < z) :
    (gapCount h N : ℝ) ≤
      32 * N * singProd h / Real.log z ^ 2 + z * (1 + Real.log z) ^ 6 + (z + 1) := by
  have h1 := gapCount_le_siftedSum h hh N z hz.le
  have h2 : siftedSum (s := (hSieve h hh N z hz.le).toBoundingSieve) ≤
      (N : ℝ) / selbergBoundingSum (hSieve h hh N z hz.le) +
      ∑ d ∈ (hSieve h hh N z hz.le).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d *
          |rem (s := (hSieve h hh N z hz.le).toBoundingSieve) d| else 0) :=
    LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple (hSieve h hh N z hz.le)
  have h3 := errSum_hSieve_le (h := h) (hh := hh) (N := N) (z := z) (hz := hz.le)
  have h4 := boundingSum_hSieve_ge (h := h) (hh := hh) (N := N) (z := z) (hz := hz.le) hh0
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hsp := singProd_pos h
  have hlow : 0 < Real.log z ^ 2 / (32 * singProd h) := by positivity
  have h5 : (N : ℝ) / selbergBoundingSum (hSieve h hh N z hz.le) ≤
      (N : ℝ) / (Real.log z ^ 2 / (32 * singProd h)) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlow h4
  have h6 : (N : ℝ) / (Real.log z ^ 2 / (32 * singProd h)) =
      32 * N * singProd h / Real.log z ^ 2 := by
    field_simp
  linarith

end LeanLab.BrunGap
