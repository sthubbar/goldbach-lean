module

public import LeanLab.PNTSieve.Selberg
public import LeanLab.PNTSieve.SelbergBounds
public import LeanLab.SchnirelmannGoldbach.S3

/-!
AI-written Lean code, Claude, 2026-10-16.
S1 setup: the Selberg sieve instance attached to Goldbach representations of an even `n`.
We sift the multiset `{m (n - m) : 0 ≤ m < n}` by the primes up to `z`.
-/

@[expose] public section

open Finset
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace LeanLab.SchnirelmannGoldbach.S1

/-- Local density numerator at a prime: `1` if `p ∣ n`, else `2`. -/
def wt (n p : ℕ) : ℝ := if p ∣ n then 1 else 2

lemma wt_pos (n p : ℕ) : 0 < wt n p := by unfold wt; split_ifs <;> norm_num

lemma wt_le_two (n p : ℕ) : wt n p ≤ 2 := by unfold wt; split_ifs <;> norm_num

lemma one_le_wt (n p : ℕ) : 1 ≤ wt n p := by unfold wt; split_ifs <;> norm_num

/-- The completely multiplicative function with `rhoN n p = wt n p`. -/
def rhoN (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m = 0 then 0 else m.factorization.prod (fun p k => wt n p ^ k), by simp⟩

lemma rhoN_apply {n m : ℕ} (hm : m ≠ 0) :
    rhoN n m = m.factorization.prod (fun p k => wt n p ^ k) := by
  show (if m = 0 then 0 else _) = _
  rw [ite_eq_right_iff.mpr (fun h => absurd h hm)]

lemma rhoN_compMult (n : ℕ) : CompletelyMultiplicative (rhoN n) := by
  constructor
  · rw [rhoN_apply one_ne_zero]; simp
  intro a b
  by_cases ha : a = 0
  · subst ha; simp [rhoN]
  by_cases hb : b = 0
  · subst hb; simp [rhoN]
  rw [rhoN_apply (mul_ne_zero ha hb), rhoN_apply ha, rhoN_apply hb, Nat.factorization_mul ha hb,
    Finsupp.prod_add_index']
  · intro; simp
  · intros; rw [pow_add]

lemma rhoN_prime {n p : ℕ} (hp : p.Prime) : rhoN n p = wt n p := by
  rw [rhoN_apply hp.ne_zero, hp.factorization, Finsupp.prod_single_index] <;> simp

lemma rhoN_nonneg (n m : ℕ) : 0 ≤ rhoN n m := by
  by_cases hm : m = 0
  · subst hm; simp [rhoN]
  rw [rhoN_apply hm]
  exact Finset.prod_nonneg fun p _ => pow_nonneg (wt_pos n p).le _

/-- The sieve density `ν(m) = ρ(m)/m`. -/
def nuN (n : ℕ) : ArithmeticFunction ℝ := (rhoN n).pdiv ArithmeticFunction.id

lemma nuN_apply (n m : ℕ) : nuN n m = rhoN n m / m := by
  simp [nuN]

lemma nuN_compMult (n : ℕ) : CompletelyMultiplicative (nuN n) :=
  (rhoN_compMult n).pdiv CompletelyMultiplicative.id

lemma nuN_nonneg (n m : ℕ) : 0 ≤ nuN n m := by
  rw [nuN_apply]; exact div_nonneg (rhoN_nonneg n m) (Nat.cast_nonneg _)

lemma nuN_prime {n p : ℕ} (hp : p.Prime) : nuN n p = wt n p / p := by
  rw [nuN_apply, rhoN_prime hp]

lemma nuN_lt_one {n p : ℕ} (hn : Even n) (hp : p.Prime) : nuN n p < 1 := by
  rw [nuN_prime hp]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [div_lt_one hp0]
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    have : wt n 2 = 1 := by unfold wt; simp [even_iff_two_dvd.mp hn]
    rw [this]; norm_num
  · have h3 : 3 ≤ p := by
      rcases hodd with ⟨k, hk⟩
      have := hp.two_le; omega
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    linarith [wt_le_two n p]

/-- The Selberg sieve for Goldbach representations of `n`. -/
def gSieve (n : ℕ) (hn : Even n) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (range n).image (fun m => m * (n - m))
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun k => (#{m ∈ range n | m * (n - m) = k} : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := n
  nu := nuN n
  nu_mult := (nuN_compMult n).isMultiplicative
  nu_pos_of_prime := fun p hp _ => by
    rw [nuN_prime hp]; exact div_pos (wt_pos n p) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => nuN_lt_one hn hp
  level := z
  one_le_level := hz

variable {n : ℕ} {hn : Even n} {z : ℝ} {hz : 1 ≤ z}

/-- Summing fibre counts over the image. -/
lemma sum_image_fiber (n : ℕ) (F : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ k ∈ (range n).image F, (if Q k then (#{m ∈ range n | F m = k} : ℝ) else 0) =
      (#{m ∈ range n | Q (F m)} : ℝ) := by
  rw [← Finset.sum_filter]
  have := Finset.sum_card_fiberwise_eq_card_filter (range n) (((range n).image F).filter Q) F
  rw [← Nat.cast_sum, this]
  congr 2
  ext m
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨m, h1, rfl⟩, h2⟩

lemma siftedSum_gSieve :
    siftedSum (s := (gSieve n hn z hz).toBoundingSieve) =
      (#{m ∈ range n | Nat.Coprime (primorial ⌊z⌋₊) (m * (n - m))} : ℝ) := by
  unfold siftedSum
  exact sum_image_fiber n (fun m => m * (n - m)) _

lemma multSum_gSieve (d : ℕ) :
    multSum (s := (gSieve n hn z hz).toBoundingSieve) d =
      (#{m ∈ range n | d ∣ m * (n - m)} : ℝ) := by
  unfold multSum
  exact sum_image_fiber n (fun m => m * (n - m)) _

lemma rem_gSieve (d : ℕ) :
    rem (s := (gSieve n hn z hz).toBoundingSieve) d =
      (#{m ∈ range n | d ∣ m * (n - m)} : ℝ) - nuN n d * n := by
  unfold rem
  rw [multSum_gSieve]
  rfl

/-- Goldbach primes either survive the sieve or are at most `z` from an end. -/
lemma r_le_siftedSum (n : ℕ) (hn : Even n) (z : ℝ) (hz : 1 ≤ z) :
    (r n : ℝ) ≤ siftedSum (s := (gSieve n hn z hz).toBoundingSieve) + 2 * (z + 1) := by
  rw [siftedSum_gSieve]
  set Z := ⌊z⌋₊
  have hsub : {p ∈ range n | p.Prime ∧ (n - p).Prime} ⊆
      {m ∈ range n | Nat.Coprime (primorial Z) (m * (n - m))} ∪
        (range (Z + 1) ∪ (range (Z + 1)).image (fun k => n - k)) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpn, hp, hq⟩ := hp
    simp only [mem_union, mem_filter, mem_range, mem_image]
    by_cases h1 : p ≤ Z
    · right; left; omega
    by_cases h2 : n - p ≤ Z
    · right; right; exact ⟨n - p, by omega, by omega⟩
    left
    refine ⟨hpn, Nat.Coprime.mul_right ?_ ?_⟩
    · exact (hp.coprime_iff_not_dvd.mpr fun h =>
        h1 ((prime_dvd_primorial_iff _ _ hp).mp h)).symm
    · exact (hq.coprime_iff_not_dvd.mpr fun h =>
        h2 ((prime_dvd_primorial_iff _ _ hq).mp h)).symm
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le {m ∈ range n | Nat.Coprime (primorial Z) (m * (n - m))}
    (range (Z + 1) ∪ (range (Z + 1)).image (fun k => n - k))
  have hc3 := Finset.card_union_le (range (Z + 1)) ((range (Z + 1)).image (fun k => n - k))
  have himg := Finset.card_image_le (s := range (Z + 1)) (f := fun k => n - k)
  simp only [card_range] at hc3 himg
  have hZ : (Z : ℝ) ≤ z := Nat.floor_le (by linarith)
  have : (r n : ℝ) ≤ (#{m ∈ range n | Nat.Coprime (primorial Z) (m * (n - m))} : ℝ) +
      ((Z + 1 : ℕ) : ℝ) + ((Z + 1 : ℕ) : ℝ) := by
    unfold r; exact_mod_cast (by omega : _ ≤ _)
  push_cast at this
  linarith

end LeanLab.SchnirelmannGoldbach.S1
