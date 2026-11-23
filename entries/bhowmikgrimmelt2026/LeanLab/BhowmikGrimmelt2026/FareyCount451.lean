module

public import LeanLab.BhowmikGrimmelt2026.WeightedGap
public import Mathlib.Data.Int.Interval

/-!
Weighted rational shell counts for the multiplier in P0029 page 26 display 7.5.
These are derived finite counting bounds, not printed paper constants.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Separated points in a fixed real interval inject into integer floor bins. -/
theorem separated_card451 {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (D c : ℝ) (K : ℕ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ |D * (f i - f j)|)
    (hclose : ∀ i ∈ s, |D * (f i - c)| ≤ K) :
    s.card ≤ 2 * K + 1 := by
  let t : Finset ℤ := Finset.Icc (⌊D * c⌋ - K) (⌊D * c⌋ + K)
  have hm : Set.MapsTo (fun i => ⌊D * f i⌋) s t := by
    intro i hi
    have hh := abs_le.mp (hclose i hi)
    have hlo : D * c - (K : ℝ) ≤ D * f i := by nlinarith only [hh.1]
    have hhi : D * f i ≤ D * c + (K : ℝ) := by nlinarith only [hh.2]
    have h1 := Int.floor_le_floor hlo
    have h2 := Int.floor_le_floor hhi
    simp only [Int.floor_sub_natCast, Int.floor_add_natCast] at h1 h2
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hinj : (s : Set ι).InjOn (fun i => ⌊D * f i⌋) := by
    intro i hi j hj heq
    by_contra hne
    change ⌊D * f i⌋ = ⌊D * f j⌋ at heq
    have hh := hsep i hi j hj hne
    have hi0 := Int.floor_le (D * f i)
    have hi1 := Int.lt_floor_add_one (D * f i)
    have hj0 := Int.floor_le (D * f j)
    have hj1 := Int.lt_floor_add_one (D * f j)
    rw [heq] at hi0 hi1
    have hlt : |D * (f i - f j)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith only [hi0, hi1, hj0, hj1]
    exact (not_lt_of_ge hh) hlt
  have hb := Finset.card_le_card_of_injOn (fun i => ⌊D * f i⌋) hm hinj
  have ht : t.card = 2 * K + 1 := by
    dsimp [t]
    rw [Int.card_Icc]
    omega
  exact ht ▸ hb

/-- The representative of a reduced rational closest to the frequency. -/
noncomputable def pairCenter451 (α : ℝ) (p : Σ _ : ℕ, ℕ) : ℝ :=
  p.2 / p.1 + round (α - p.2 / p.1)

/-- The centered representative realizes the exact distance to an integer. -/
theorem pairCenter_dist451 (α : ℝ) (p : Σ _ : ℕ, ℕ) :
    |α - pairCenter451 α p| = intDist (α - p.2 / p.1) := by
  unfold pairCenter451 intDist
  congr 1
  ring

/-- Centered reduced rationals with bounded denominators retain Farey separation. -/
theorem pairCenter_separated451 {M : ℕ} {R α : ℝ} (hR : 0 < R)
    (hMR : (M : ℝ) ≤ R) {p r : Σ _ : ℕ, ℕ}
    (hp : p ∈ reducedPairs M) (hr : r ∈ reducedPairs M) (hne : p ≠ r) :
    1 ≤ |R ^ 2 * (pairCenter451 α p - pairCenter451 α r)| := by
  obtain ⟨hq1, hqM, ha, hcop⟩ := (mem_reducedPairs M p).mp hp
  obtain ⟨hr1, hrM, hb, hcopr⟩ := (mem_reducedPairs M r).mp hr
  have hqp : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hrp : (0 : ℝ) < r.1 := by exact_mod_cast hr1
  have hqR : (p.1 : ℝ) ≤ R := (by exact_mod_cast hqM : (p.1 : ℝ) ≤ M).trans hMR
  have hrR : (r.1 : ℝ) ≤ R := (by exact_mod_cast hrM : (r.1 : ℝ) ≤ M).trans hMR
  have hne' : (p.2, p.1) ≠ (r.2, r.1) := by
    intro heq
    apply hne
    exact Sigma.ext (congrArg Prod.snd heq) (by simpa using congrArg Prod.fst heq)
  have hs := farey_intDist_separation ha hb hcop hcopr hne'
  have hc : intDist ((p.2 : ℝ) / p.1 - (r.2 : ℝ) / r.1) ≤
      |pairCenter451 α p - pairCenter451 α r| := by
    have ht := intDist_le_abs_sub ((p.2 : ℝ) / p.1 - (r.2 : ℝ) / r.1)
      (round (α - r.2 / r.1) - round (α - p.2 / p.1))
    convert ht using 1
    unfold pairCenter451
    push_cast
    congr 1
    ring
  have hd : 1 / R ^ 2 ≤ 1 / ((p.1 : ℝ) * r.1) :=
    one_div_le_one_div_of_le (mul_pos hqp hrp)
      (by nlinarith [mul_le_mul hqR hrR hrp.le hR.le])
  have hh := (div_le_iff₀ (sq_pos_of_pos hR)).mp (hd.trans (hs.trans hc))
  rw [abs_mul, abs_of_nonneg (sq_nonneg R)]
  nlinarith only [hh]

/-- Close distinct weighted rational approximations force a large denominator sum. -/
theorem near_pair_denominator_sum451 {M : ℕ} {R L α : ℝ} (hR : 0 < R)
    {p r : Σ _ : ℕ, ℕ} (hp : p ∈ reducedPairs M) (hr : r ∈ reducedPairs M)
    (hne : p ≠ r)
    (hpnear : R * p.1 * intDist (α - p.2 / p.1) ≤ L)
    (hrnear : R * r.1 * intDist (α - r.2 / r.1) ≤ L) :
    R ≤ L * ((p.1 : ℝ) + r.1) := by
  obtain ⟨hq1, hqM, ha, hcop⟩ := (mem_reducedPairs M p).mp hp
  obtain ⟨hr1, hrM, hb, hcopr⟩ := (mem_reducedPairs M r).mp hr
  have hqp : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hrp : (0 : ℝ) < r.1 := by exact_mod_cast hr1
  have hne' : (p.2, p.1) ≠ (r.2, r.1) := by
    intro heq
    apply hne
    exact Sigma.ext (congrArg Prod.snd heq) (by simpa using congrArg Prod.fst heq)
  have hs := farey_intDist_separation ha hb hcop hcopr hne'
  have ht := intDist_sub_le (α - r.2 / r.1) (α - p.2 / p.1)
  rw [show (α - (r.2 : ℝ) / r.1) - (α - p.2 / p.1) =
    p.2 / p.1 - r.2 / r.1 by ring] at ht
  have hh := (div_le_iff₀ (mul_pos hqp hrp)).mp (hs.trans ht)
  have h1 := mul_le_mul_of_nonneg_left hh hR.le
  have h2 := mul_le_mul_of_nonneg_right hpnear hrp.le
  have h3 := mul_le_mul_of_nonneg_right hrnear hqp.le
  nlinarith only [h1, h2, h3]

/-- The reduced rational pairs in a weighted distance shell through K. -/
noncomputable def nearPairs451 (R α : ℝ) (K : ℕ) : Finset (Σ _ : ℕ, ℕ) := by
  classical
  exact (reducedPairs ⌊R⌋₊).filter
    (fun p => R * p.1 * intDist (α - p.2 / p.1) ≤ K)

/-- At most one close pair can have denominator below R divided by twice K. -/
theorem nearPairs_small_card451 {R α : ℝ} (hR : 0 < R) {K : ℕ} (hK : 1 ≤ K) :
    ((nearPairs451 R α K).filter (fun p => (p.1 : ℝ) < R / (2 * K))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp r hr
  by_contra hne
  obtain ⟨hp, hpq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr, hrq⟩ := Finset.mem_filter.mp hr
  obtain ⟨hpM, hpnear⟩ := Finset.mem_filter.mp hp
  obtain ⟨hrM, hrnear⟩ := Finset.mem_filter.mp hr
  have hkp : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hh := near_pair_denominator_sum451 hR hpM hrM hne hpnear hrnear
  have h1 := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp hpq
  have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp hrq
  nlinarith only [hh, h1, h2]

/-- A weighted shell contains at most four K squared plus two pairs, independently of R. -/
theorem nearPairs_card451 {R α : ℝ} (hR : 1 ≤ R) {K : ℕ} (hK : 1 ≤ K) :
    (nearPairs451 R α K).card ≤ 4 * K ^ 2 + 2 := by
  classical
  have hRp : 0 < R := by linarith
  have hkp : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  let s := nearPairs451 R α K
  let low := s.filter (fun p => (p.1 : ℝ) < R / (2 * K))
  let high := s.filter (fun p => ¬ (p.1 : ℝ) < R / (2 * K))
  have hl : low.card ≤ 1 := nearPairs_small_card451 hRp hK
  have hh : high.card ≤ 4 * K ^ 2 + 1 := by
    have hsep : ∀ p ∈ high, ∀ r ∈ high, p ≠ r →
        1 ≤ |R ^ 2 * (pairCenter451 α p - pairCenter451 α r)| := by
      intro p hp r hr hne
      have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      have hr' := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      exact pairCenter_separated451 hRp (Nat.floor_le hRp.le) hp' hr' hne
    have hclose : ∀ p ∈ high, |R ^ 2 * (pairCenter451 α p - α)| ≤ (2 * K ^ 2 : ℕ) := by
      intro p hp
      obtain ⟨hp, hlarge⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpM, hpnear⟩ := Finset.mem_filter.mp hp
      have hq : R ≤ 2 * K * (p.1 : ℝ) := by
        have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp (le_of_not_gt hlarge)
        nlinarith only [hh]
      have h1 := mul_le_mul_of_nonneg_right hq
        (mul_nonneg hRp.le (intDist_nonneg (α - p.2 / p.1)))
      have h2 := mul_le_mul_of_nonneg_left hpnear (by positivity : (0 : ℝ) ≤ 2 * K)
      rw [abs_mul, abs_of_nonneg (sq_nonneg R), abs_sub_comm, pairCenter_dist451]
      push_cast
      nlinarith only [h1, h2]
    have hc := separated_card451 high (pairCenter451 α) (R ^ 2) α (2 * K ^ 2) hsep hclose
    omega
  have hun : s = low ∪ high := by
    ext p
    by_cases h : (p.1 : ℝ) < R / (2 * K)
    · simp [low, high, h, not_le.mpr h]
    · simp [low, high, h, le_of_not_gt h]
  have hc := Finset.card_union_le low high
  rw [← hun] at hc
  change s.card ≤ _
  omega

end LeanLab.BhowmikGrimmelt2026
