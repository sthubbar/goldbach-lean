module

public import LeanLab.PNTPort.BVMax.RenyiPaired

/-!
# Rényi's theorem with `K = 20`, four blocks per level

Unit U-6742, CLOUD 20261020T2113Z-cloud51. AI wrote the Lean code. Known mathematics, IDEAS I-5051.

`RenyiPaired.lean` raises the level by 2 every second block and needs `Σ ρ ≤ 1/10` for the
relative error bound `d_le_of_sum` of `BrunBlocksRel.lean`, giving `K = 23`. Here:

* `d_le_of_sum5`: if `Σ ρ ≤ 1/5` then `dU ≤ (5/4) Σ ρ` and `dL ≤ 2 Σ ρ`, so
  `blocks_main_rel5` and `renyi_blocks_rel5` give `S ≥ X V (1 - 2 Σ ρ) - …` under `Σ ρ ≤ 1/5`;
* the level rises by 2 every fourth block, `lvQ 4 d = 4 + 2⌊d/4⌋`; the level exponent is
  `FQ d = 10 + 4⌊d/4⌋ + 2^{(d mod 4) + 2}/15`, the fixed point of the level recursion,
  `FQ 0 = 154/15`;
* `Σ ρ ≤ (120/29) fR 4 + 9 e^{-907} < 0.192 < 1/5`;
* with `L = log N/21` the level is `exp((154/15) L) ≤ N^{0.489} ≤ N^{49/100}`, and every prime
  factor of a survivor exceeds `exp(log N/21)`, so `Ω(N - p) ≤ 20`.

Within Brun's pure block scheme with top level 4, `FQ 0 > 10`, so `K = 20` is the floor of this
route; level 2 blocks have `ρ ≥ 0.49` at the proved block sum and do not fit.

Binary Goldbach is `Ω(m) = 1` and stays OPEN; Chen's `Ω(m) ≤ 2` is far stronger than this route.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- **Accumulation at `1/5`**: if `Σ ρ_b ≤ 1/5` then `0 ≤ dU ≤ (5/4) Σ ρ_b` and
`0 ≤ dL ≤ 2 Σ ρ_b`. -/
theorem d_le_of_sum5 (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) :
    ∀ Bs : List Block, rhoSum x Bs ≤ 1 / 5 →
      0 ≤ dU x Bs ∧ dU x Bs ≤ 5 / 4 * rhoSum x Bs ∧ 0 ≤ dL x Bs ∧ dL x Bs ≤ 2 * rhoSum x Bs
  | [], _ => by simp [dU, dL, rhoSum]
  | b :: Bs, h => by
    have hρ := rho_nonneg x hx0 hx1 b
    have hS := rhoSum_nonneg x hx0 hx1 Bs
    simp only [rhoSum] at h
    obtain ⟨hU0, hU, hL0, hL⟩ := d_le_of_sum5 x hx0 hx1 Bs (by linarith)
    simp only [dU, dL, rhoSum]
    have hU2 : dU x Bs ≤ 1 / 4 := by linarith
    have hL2 : dL x Bs ≤ 2 / 5 := by linarith
    have m1 := mul_le_mul_of_nonneg_left hU2 hρ
    have m2 := mul_le_mul_of_nonneg_left hL2 hρ
    refine ⟨by positivity, ?_, by positivity, ?_⟩
    · nlinarith
    · nlinarith

/-- **Brun's block sieve with relative error at `1/5`**:
`S(A, Ω) ≥ X V (1 - 2 Σ ρ_b) - 3^n Σ |R_S|` when `Σ ρ_b ≤ 1/5`. -/
theorem blocks_main_rel5 (A : Finset ℕ) (Bs : List Block) (hG : Good Bs) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1) (X : ℝ) (hX : 0 ≤ X)
    (hρ : rhoSum x Bs ≤ 1 / 5) :
    X * (∏ p ∈ univB Bs, (1 - x p)) * (1 - 2 * rhoSum x Bs) -
      3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), |rem A x X S| ≤
      (sifted A (univB Bs) : ℝ) := by
  have hx1' : ∀ p, x p ≤ 1 := fun p => (hx1 p).le
  have h1 := blocks_sum A Bs hG
  rw [sum_wEval A (univB Bs) (cL Bs) x X] at h1
  have h2 := (blocks_rel_dev x hx0 hx1 Bs hG).2
  rw [abs_le] at h2
  have hd := (d_le_of_sum5 x hx0 hx1' Bs hρ).2.2.2
  have hV : 0 ≤ ∏ p ∈ univB Bs, (1 - x p) := prod_nonneg (fun p _ => by linarith [hx1 p])
  have h3 : -(3 ^ Bs.length *
      ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), |rem A x X S|) ≤
      ∑ S ∈ (univB Bs).powerset, cL Bs S * rem A x X S := by
    have hle : ∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤
        3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0),
          |rem A x X S| := by
      rw [mul_sum, sum_filter]
      refine sum_le_sum (fun S _ => ?_)
      split_ifs with hS
      · exact mul_le_mul_of_nonneg_right (coeff_bounds Bs S).2 (abs_nonneg _)
      · push Not at hS; rw [hS]; simp
    have : -∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤
        ∑ S ∈ (univB Bs).powerset, cL Bs S * rem A x X S := by
      rw [← sum_neg_distrib]
      refine sum_le_sum (fun S _ => ?_)
      rw [← abs_mul]
      exact neg_abs_le _
    linarith
  have h4 : (∏ p ∈ univB Bs, (1 - x p)) * (1 - 2 * rhoSum x Bs) ≤ wMain (univB Bs) (cL Bs) x := by
    have := mul_le_mul_of_nonneg_left hd hV
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 hX
  nlinarith

end LeanLab.PNTSieve.Bonferroni

namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- **Brun's block sieve on `{N - p}`, relative form at `1/5`**: if `Σ ρ_B ≤ 1/5`,
`S({N - p}, Ω) ≥ X V (1 - 2 Σ ρ_B) - 3^{#blocks} K N/(log N)^A`. -/
theorem renyi_blocks_rel5 (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
    lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 5 →
    liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 2 * rhoSum xDen Bs) -
      3 ^ Bs.length * (K * N / Real.log N ^ A) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ) := by
  obtain ⟨B, hB, K, hK⟩ := renyi_rem_family A hA
  refine ⟨B, hB, K, fun N hN Bs hG hBs hlev hρ => ?_⟩
  have hX : 0 ≤ liD ((N - 1 : ℕ) : ℝ) := by
    unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have h1 := blocks_main_rel5 (goldbachSeq N) Bs hG xDen xDen_nonneg xDen_lt_one _ hX hρ
  have hP : ∀ p ∈ univB Bs, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p :=
    fun p hp => ⟨univB_prime Bs hG p hp, (hBs p hp).1, (hBs p hp).2⟩
  have h2 := hK N hN (univB Bs) hP ((univB Bs).powerset.filter (fun S => cL Bs S ≠ 0))
    (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      exact (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans hlev)
  have h3 : (0 : ℝ) ≤ 3 ^ Bs.length := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

/-- The level at depth `d`: it rises by 2 every fourth block. -/
def lvQ (r d : ℕ) : ℕ := r + 2 * (d / 4)

lemma lvQ_mono (r : ℕ) {d e : ℕ} (h : d ≤ e) : lvQ r d ≤ lvQ r e := by
  unfold lvQ; have := Nat.div_le_div_right (c := 4) h; omega

lemma lvQ_even {r : ℕ} (hr : Even r) (d : ℕ) : Even (lvQ r d) := by
  unfold lvQ; exact hr.add (even_two_mul _)

lemma lvQ_eq (q s : ℕ) (hs : s < 4) : lvQ 4 (4 * q + s) = 4 + 2 * q := by
  unfold lvQ; omega

/-- Blocks `j, …, 0` on the real scale with levels `lvQ`, starting at depth `d`. -/
noncomputable def GQ (N : ℕ) (c : ℝ) : ℕ → ℕ → ℕ → List Block
  | 0, r, d => [(blkE N c 0, lvQ r d, lvQ r d + 1)]
  | j + 1, r, d => (blkE N c (j + 1), lvQ r d, lvQ r d + 1) :: GQ N c j r (d + 1)

lemma GQ_length (N : ℕ) (c : ℝ) : ∀ j r d, (GQ N c j r d).length = j + 1
  | 0, r, d => by simp [GQ]
  | j + 1, r, d => by simp [GQ, GQ_length N c j r (d + 1)]

lemma GQ_mem (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j r d, ∀ p ∈ univB (GQ N c j r d),
    (p : ℝ) ≤ thr c (j + 1) ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p
  | 0, r, d, p, hp => by
    simp only [GQ, univB, union_empty] at hp
    obtain ⟨h1, h2, h3, h4, -⟩ := blkE_mem hp
    exact ⟨h1, h2, h3, h4⟩
  | j + 1, r, d, p, hp => by
    simp only [GQ, univB, mem_union] at hp
    rcases hp with h | h
    · obtain ⟨h1, h2, h3, h4, -⟩ := blkE_mem h
      exact ⟨h1, h2, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := GQ_mem N hc j r (d + 1) p h
      exact ⟨h1.trans (thr_mono hc (by omega)), h2, h3, h4⟩

lemma GQ_good (N : ℕ) {c : ℝ} (hc : 0 ≤ c) {r : ℕ} (hr : Even r) : ∀ j d, Good (GQ N c j r d)
  | 0, d => by
    simp only [GQ, Good, univB]
    exact ⟨fun p hp => (blkE_mem hp).2.1, disjoint_empty_right _, lvQ_even hr d,
      (lvQ_even hr d).add_one, trivial⟩
  | j + 1, d => by
    simp only [GQ, Good]
    refine ⟨fun p hp => (blkE_mem hp).2.1, ?_, lvQ_even hr d, (lvQ_even hr d).add_one,
      GQ_good N hc hr j (d + 1)⟩
    rw [disjoint_left]
    intro p hp hp'
    have h1 := (GQ_mem N hc j r (d + 1) p hp').1
    rcases (blkE_mem hp).2.2.2.2 with h | h
    · omega
    · linarith

lemma GQ_cover (N : ℕ) (c : ℝ) : ∀ j r d, ∀ p, p.Prime → ¬ p ∣ N → 3 ≤ p →
    (p : ℝ) ≤ thr c (j + 1) → p ∈ univB (GQ N c j r d)
  | 0, r, d, p, hp, hpN, h3, hpz => by
    simp only [GQ, univB, union_empty, blkE, mem_filter, mem_Icc]
    exact ⟨⟨h3, Nat.le_floor hpz⟩, hp, hpN, Or.inl trivial⟩
  | j + 1, r, d, p, hp, hpN, h3, hpz => by
    simp only [GQ, univB, mem_union]
    by_cases h : (p : ℝ) ≤ thr c (j + 1)
    · exact Or.inr (GQ_cover N c j r (d + 1) p hp hpN h3 h)
    · left
      simp only [blkE, mem_filter, mem_Icc]
      exact ⟨⟨h3, Nat.le_floor hpz⟩, hp, hpN, Or.inr (not_le.mp h)⟩

/-- The level exponent at depth `d` for top level 4: `10 + 4⌊d/4⌋ + 2^{(d mod 4) + 2}/15`. -/
noncomputable def FQ (d : ℕ) : ℝ := 10 + 4 * ((d / 4 : ℕ) : ℝ) + (2 : ℝ) ^ (d % 4 + 2) / 15

lemma FQ_eq (q s : ℕ) (hs : s < 4) : FQ (4 * q + s) = 10 + 4 * (q : ℝ) + (2 : ℝ) ^ (s + 2) / 15 := by
  unfold FQ
  have h1 : (4 * q + s) / 4 = q := by omega
  have h2 : (4 * q + s) % 4 = s := by omega
  rw [h1, h2]

lemma FQ_zero : FQ 0 = 154 / 15 := by
  have := FQ_eq 0 0 (by norm_num)
  simp only [mul_zero, add_zero] at this
  rw [this]; norm_num

lemma lvQ_FQ (d : ℕ) : ((lvQ 4 d : ℕ) : ℝ) + 1 ≤ FQ d ∧
    ((lvQ 4 d : ℕ) : ℝ) + 1 + FQ (d + 1) / 2 ≤ FQ d := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 4 ∧ d = 4 * q + s :=
    ⟨d / 4, d % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod d 4).symm⟩
  rw [lvQ_eq q s hs, FQ_eq q s hs]
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (s + 2) / 15 := by positivity
  rcases (by omega : s < 3 ∨ s = 3) with hs3 | rfl
  · have e : (2 : ℝ) ^ (s + 1 + 2) = 2 * 2 ^ (s + 2) := by ring
    rw [show 4 * q + s + 1 = 4 * q + (s + 1) by ring, FQ_eq q (s + 1) (by omega), e]
    push_cast
    constructor <;> linarith
  · rw [show 4 * q + 3 + 1 = 4 * (q + 1) + 0 by ring, FQ_eq (q + 1) 0 (by norm_num)]
    push_cast
    norm_num
    constructor <;> linarith

lemma GQ_lev (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j d,
    (lev (GQ N c j 4 d) : ℝ) ≤ Real.exp (2 ^ (j + 1) * c * FQ d)
  | 0, d => by
    simp only [GQ, lev, mul_one]
    rw [show max (lvQ 4 d) (lvQ 4 d + 1) = lvQ 4 d + 1 by omega]
    push_cast
    have hs := blkE_sup_le N hc 0
    push_cast at hs
    calc (max (((blkE N c 0).sup id : ℕ) : ℝ) 1) ^ (lvQ 4 d + 1) ≤ thr c (0 + 1) ^ (lvQ 4 d + 1) :=
          pow_le_pow_left₀ (by positivity) hs _
      _ = Real.exp (2 ^ (0 + 1) * c * ((lvQ 4 d + 1 : ℕ) : ℝ)) := thr_pow c _ _
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have := (lvQ_FQ d).1
          push_cast at this ⊢
          nlinarith
  | j + 1, d => by
    simp only [GQ, lev]
    rw [show max (lvQ 4 d) (lvQ 4 d + 1) = lvQ 4 d + 1 by omega]
    push_cast
    have hs := blkE_sup_le N hc (j + 1)
    push_cast at hs
    have ih := GQ_lev N hc j (d + 1)
    calc (max (((blkE N c (j + 1)).sup id : ℕ) : ℝ) 1) ^ (lvQ 4 d + 1) * (lev (GQ N c j 4 (d + 1)) : ℝ)
        ≤ thr c (j + 1 + 1) ^ (lvQ 4 d + 1) * Real.exp (2 ^ (j + 1) * c * FQ (d + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hs _) ih (Nat.cast_nonneg _)
            (pow_nonneg (thr_pos c _).le _)
      _ ≤ Real.exp (2 ^ (j + 1 + 1) * c * FQ d) := by
          rw [thr_pow, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h := (lvQ_FQ d).2
          have h2 : (0 : ℝ) ≤ 2 ^ (j + 1) * c := by positivity
          have e : (2 : ℝ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
          rw [e]; push_cast at h ⊢
          nlinarith [mul_le_mul_of_nonneg_left h h2]

/-- The running bound of the sharp part: `(4 - d mod 4) fR(lvQ 4 d) + (120/29) fR(lvQ 4 d + 2)`. -/
noncomputable def HH (d : ℕ) : ℝ :=
  ((4 - d % 4 : ℕ) : ℝ) * fR (lvQ 4 d) + 120 / 29 * fR (lvQ 4 d + 2)

lemma HH_nonneg (d : ℕ) : 0 ≤ HH d := by
  unfold HH; have := fR_nonneg (lvQ 4 d); have := fR_nonneg (lvQ 4 d + 2)
  positivity

lemma HH_step (d : ℕ) : fR (lvQ 4 d) + HH (d + 1) ≤ HH d := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 4 ∧ d = 4 * q + s :=
    ⟨d / 4, d % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod d 4).symm⟩
  unfold HH
  rcases (by omega : s < 3 ∨ s = 3) with hs3 | rfl
  · have hl : lvQ 4 (4 * q + s + 1) = lvQ 4 (4 * q + s) := by unfold lvQ; omega
    have e : 4 - (4 * q + s) % 4 = (4 - (4 * q + s + 1) % 4) + 1 := by omega
    rw [hl, e]
    push_cast
    linarith
  · have hl : lvQ 4 (4 * q + 3 + 1) = lvQ 4 (4 * q + 3) + 2 := by unfold lvQ; omega
    have e1 : 4 - (4 * q + 3) % 4 = 1 := by omega
    have e2 : 4 - (4 * q + 3 + 1) % 4 = 4 := by omega
    have h4 : 4 ≤ lvQ 4 (4 * q + 3) + 2 := by unfold lvQ; omega
    have := fR_step30 _ h4
    rw [hl, e1, e2, show lvQ 4 (4 * q + 3) + 2 + 2 = (lvQ 4 (4 * q + 3) + 2) + 2 by ring]
    push_cast
    linarith

/-- Crude: `Σ ρ ≤ (j + 1) e^{93 - lvQ r d}` over `GQ N c j r d` when `lvQ r d ≥ 1000`. -/
lemma GQ_rho (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) (r : ℕ) :
    ∀ j d, 1000 ≤ lvQ r d → rhoSum xDen (GQ N c j r d) ≤ (j + 1) * Real.exp (93 - lvQ r d)
  | 0, d, hd => by
    simp only [GQ, rhoSum, add_zero]
    have := rho_crude_of _ _ (fun p hp => (blkE_mem hp).2.2.2.1) (blkE_xsum N hc hc2 0) hd
    push_cast; linarith
  | j + 1, d, hd => by
    simp only [GQ, rhoSum]
    have h1 := rho_crude_of _ _ (fun p hp => (blkE_mem hp).2.2.2.1) (blkE_xsum N hc hc2 (j + 1)) hd
    have hm := lvQ_mono r (Nat.le_succ d)
    have h2 := GQ_rho N hc hc2 r j (d + 1) (hd.trans hm)
    have h3 : Real.exp (93 - ((lvQ r (d + 1) : ℕ) : ℝ)) ≤ Real.exp (93 - lvQ r d) :=
      Real.exp_le_exp.mpr (by have : ((lvQ r d : ℕ) : ℝ) ≤ lvQ r (d + 1) := by exact_mod_cast hm
                              linarith)
    have h4 : ((j + 1 : ℕ) : ℝ) * Real.exp (93 - ((lvQ r (d + 1) : ℕ) : ℝ)) ≤
        ((j + 1 : ℕ) : ℝ) * Real.exp (93 - lvQ r d) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    push_cast at h2 h4 ⊢
    linarith

/-- **`Σ ρ ≤ HH d + 9 e^{93 - lvQ 4 (d + (j - 8))}`** over `GQ N c j 4 d` for `j ≥ 8`. -/
lemma GQ_rho_sharp (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) :
    ∀ j, 8 ≤ j → ∀ d, 1000 ≤ lvQ 4 (d + (j - 8)) →
      rhoSum xDen (GQ N c j 4 d) ≤ HH d + 9 * Real.exp (93 - ((lvQ 4 (d + (j - 8)) : ℕ) : ℝ)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro d hd
    simp only [Nat.sub_self, add_zero] at hd ⊢
    have := GQ_rho N hc hc2 4 8 d hd
    have := HH_nonneg d
    push_cast at *
    linarith
  | succ j hj ih =>
    intro d hd
    simp only [GQ, rhoSum]
    obtain ⟨h101, hs⟩ := blkE_sharp N hc hc2 (j := j + 1) (by omega)
    have h1 := rho_sharp_of _ (lvQ 4 d) h101 hs
    have e : d + 1 + (j - 8) = d + (j + 1 - 8) := by omega
    have h2 := ih (d + 1) (by rw [e]; exact hd)
    rw [e] at h2
    have h3 := HH_step d
    linarith

lemma HH_zero_le : HH 0 ≤ 1904 / 10000 := by
  have h0 : HH 0 = 4 * fR 4 + 120 / 29 * fR 6 := by unfold HH lvQ; norm_num
  have h6 := fR_step30 4 (le_refl _)
  norm_num at h6
  have h4 := two_fR_four_le
  have := fR_nonneg 4
  rw [h0]
  linarith

lemma big_aux21 (ℓ : ℝ) (h : (2 : ℝ) ^ 2100 ≤ ℓ) :
    (10 : ℝ) ^ 6 ≤ ℓ ∧ 2 ^ 2005 ≤ ⌊ℓ / (21 * Real.log 2)⌋₊ := by
  have h2p : (2 : ℝ) ^ 2100 = 2 ^ 95 * 2 ^ 2005 := by rw [← pow_add]
  have h94 : (2 : ℝ) ^ 20 ≤ 2 ^ 95 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h1p : (1 : ℝ) ≤ 2 ^ 2005 := one_le_pow₀ (by norm_num)
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hc : ((2 ^ 2005 : ℕ) : ℝ) = (2 : ℝ) ^ 2005 := by push_cast; rfl
  rw [h2p] at h
  rw [h20] at h94
  generalize (2 : ℝ) ^ 95 = C at *
  generalize (2 : ℝ) ^ 2005 = A at *
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hCA : 1048576 * A ≤ C * A := mul_le_mul_of_nonneg_right h94 (by linarith)
  clear h2p h20
  refine ⟨by nlinarith, ?_⟩
  apply Nat.le_floor
  rw [hc]
  clear hc
  rw [le_div_iff₀ (by positivity)]
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Rényi with `K = 20`, deterministic core with the count.** -/
theorem renyi20_count {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 5 →
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 2 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hE : Even N) (hℓ6 : (2 : ℝ) ^ 2100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    9 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 20)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨h10, ht2005⟩ := big_aux21 ℓ hℓ6
  clear hℓ6
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN8 : (8 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  have hN38 : (38 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- t, k and the real scale c
  set t := ⌊ℓ / (21 * Real.log 2)⌋₊ with ht
  have ht1 : ℓ / (21 * Real.log 2) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (ℓ / (21 * Real.log 2)); rw [← ht] at this; linarith
  have ht2 : (t : ℝ) ≤ ℓ / (21 * Real.log 2) := Nat.floor_le (by positivity)
  have htge : 2 ≤ t := le_trans (Nat.le_self_pow (by norm_num) 2) ht2005
  set k := Nat.log 2 t with hk
  have hk2005 : 2005 ≤ k := Nat.le_log_of_pow_le (by norm_num) ht2005
  clear ht2005
  have hkt : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
  have htk : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hkt' : ((2 ^ k : ℕ) : ℝ) ≤ t := by exact_mod_cast hkt
  have htk1 : (t : ℝ) + 1 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
    have : t + 1 ≤ 2 ^ (k + 1) := htk
    have : ((t + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [pow_succ] at this; push_cast at this ⊢; linarith
  set L := ℓ / 21 with hL
  have h2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  set c := L / ((2 ^ k : ℕ) : ℝ) with hc
  have hLe : ℓ / (21 * Real.log 2) * Real.log 2 = L := by rw [hL]; field_simp
  have hc1 : Real.log 2 ≤ c := by
    rw [hc, le_div_iff₀ h2k, ← hLe]
    have := mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
    linarith
  have hc2 : c ≤ 2 * Real.log 2 := by
    rw [hc, div_le_iff₀ h2k, ← hLe]
    have h1 : ℓ / (21 * Real.log 2) ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right h1 hl2pos.le
    linarith
  have hc0 : 0 ≤ c := le_trans hl2pos.le hc1
  have h2kc : (2 : ℝ) ^ k * c = L := by
    rw [hc]; push_cast; field_simp
  have hthr : thr c k = Real.exp L := by unfold thr; rw [h2kc]
  set j := k - 1 with hj
  have hjk : j + 1 = k := by omega
  have hLbig : (10 : ℝ) ≤ L := by rw [hL]; linarith
  set z := ⌊Real.exp L⌋₊ with hz
  have hz3 : 3 ≤ z := by
    apply Nat.le_floor
    have := Real.add_one_le_exp L
    push_cast; linarith
  have hzr : (z : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos _).le
  have hz1 : Real.exp L < (z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogz : Real.log z ≤ L := by
    have := Real.log_le_log (by positivity) hzr
    rwa [Real.log_exp] at this
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogz1 : L < Real.log ((z : ℝ) + 1) := by
    have := Real.log_lt_log (Real.exp_pos _) hz1
    rwa [Real.log_exp] at this
  -- the blocks
  set Bs := GQ N c j 4 0 with hBs
  have hG : Good Bs := GQ_good N hc0 ⟨2, rfl⟩ j 0
  have hmem := GQ_mem N hc0 j 4 0
  rw [hjk, hthr] at hmem
  have hcov := GQ_cover N c j 4 0
  rw [hjk, hthr] at hcov
  have hlen : Bs.length = k := by rw [hBs, GQ_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply Nat.le_floor
    have h1 := GQ_lev N hc0 j 0
    rw [hjk] at h1
    have h2 : Real.exp (2 ^ k * c * FQ 0) ≤ Real.exp (49 / 100 * ℓ) := by
      apply Real.exp_le_exp.mpr
      rw [h2kc, hL]; rw [FQ_zero]; nlinarith
    exact h1.trans (h2.trans hE2)
  have hρ : rhoSum xDen Bs ≤ 1 / 5 := by
    have hlv0 : 1000 ≤ lvQ 4 (0 + (j - 8)) := by unfold lvQ; omega
    refine (GQ_rho_sharp N hc1 hc2 j (by omega) 0 hlv0).trans ?_
    have hlv : (1000 : ℝ) ≤ ((lvQ 4 (0 + (j - 8)) : ℕ) : ℝ) := by exact_mod_cast hlv0
    have h0 : Real.exp (93 - ((lvQ 4 (0 + (j - 8)) : ℕ) : ℝ)) ≤ Real.exp (-907) :=
      Real.exp_le_exp.mpr (by linarith)
    have := HH_zero_le
    have := exp_neg_907_le'
    linarith
  -- the sieve count
  have hS := hK N (by omega) Bs hG (fun p hp => ⟨(hmem p hp).2.2.1, (hmem p hp).2.2.2⟩) hlev hρ
  rw [hlen] at hS
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hV : Real.exp (-36) / Real.log z ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    have := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz3 (univB Bs)
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, Nat.le_floor (hmem p hp).1⟩)
    refine this.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
    simp only [xDen, if_pos (hmem p hp).2.2.2]
  have hV2 : Real.exp (-36) * 21 / ℓ ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    refine le_trans ?_ hV
    rw [div_le_div_iff₀ hℓpos hlogz_pos]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 21 ≤ ℓ := by rw [hL] at hlogz; linarith
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 21 / ℓ) * (1 / 2) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 2 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 21 / ℓ) * (1 / 2) =
      21 / 2 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      21 / 2 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have := Real.exp_pos (-37 : ℝ); have := Real.exp_pos (-36 : ℝ); linarith
  -- the error term: 3^k K N / ℓ^5 ≤ |K| N / ℓ^3
  have h3k : ((3 : ℝ) ^ k) ≤ ℓ ^ 2 := by
    have h1 : (3 : ℝ) ^ k ≤ ((2 ^ k : ℕ) : ℝ) ^ 2 := by
      push_cast; rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ ℓ := by
      refine hkt'.trans (ht2.trans ?_)
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact h1.trans (pow_le_pow_left₀ (by positivity) h2 2)
  have h5r : ℓ ^ (5 : ℝ) = ℓ ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have herr : 3 ^ k * (K * N / ℓ ^ (5 : ℝ)) ≤ |K| * N / ℓ ^ (3 : ℝ) := by
    rw [h5r, h3r]
    have hK1 : K * N / ℓ ^ 5 ≤ |K| * N / ℓ ^ 5 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hNpos.le)
        (by positivity)
    have hK0 : 0 ≤ |K| * N / ℓ ^ 5 := by positivity
    calc 3 ^ k * (K * N / ℓ ^ 5) ≤ 3 ^ k * (|K| * N / ℓ ^ 5) :=
          mul_le_mul_of_nonneg_left hK1 (by positivity)
      _ ≤ ℓ ^ 2 * (|K| * N / ℓ ^ 5) := mul_le_mul_of_nonneg_right h3k hK0
      _ = |K| * N / ℓ ^ 3 := by field_simp
  have hzle : (z : ℝ) ≤ Real.exp (ℓ / 3) := by
    refine hzr.trans (Real.exp_le_exp.mpr ?_); rw [hL]; linarith
  set Surv := (goldbachSeq N).filter (fun a => ∀ p ∈ univB Bs, ¬ p ∣ a) with hSurv
  have hcardS : (sifted (goldbachSeq N) (univB Bs) : ℝ) = (Surv.card : ℝ) := by
    simp [sifted, hSurv]
  set small := (range (z + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ z + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 20) with hGd
  -- every survivor outside the small image is N - p for a good p
  have hsub : Surv \ small ⊆ Gd.image (fun p => N - p) := by
    intro m hm
    rw [mem_sdiff] at hm
    obtain ⟨hmS, hmn⟩ := hm
    rw [hSurv, mem_filter] at hmS
    obtain ⟨hmG, hmP⟩ := hmS
    unfold goldbachSeq at hmG
    rw [mem_image] at hmG
    obtain ⟨p, hp, rfl⟩ := hmG
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpN, hpp⟩ := hp
    have hpz : z < p := by
      by_contra h
      push Not at h
      exact hmn (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
    have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hmodd : Odd (N - p) := by
      rcases hE with ⟨a, ha⟩
      rcases hpodd with ⟨b, hb⟩
      exact ⟨a - b - 1, by omega⟩
    have hm0 : N - p ≠ 0 := by omega
    have hfac_big : ∀ q ∈ (N - p).primeFactorsList, z + 1 ≤ q := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      by_contra hlt
      push Not at hlt
      have hqz : q ≤ z := by omega
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
      · exact hmP q (hcov q hqp hqN hq3 ((Nat.le_floor_iff (Real.exp_pos _).le).mp hqz)) hqd
    have hpow := pow_bigOmega_le (N - p) (z + 1) hm0 hfac_big
    have hpowr : ((z : ℝ) + 1) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := by
      have : (z + 1) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := hpow.trans (Nat.sub_le N p)
      exact_mod_cast this
    have hlogpow : (ArithmeticFunction.cardFactors (N - p) : ℝ) * Real.log ((z : ℝ) + 1) ≤ ℓ := by
      have := Real.log_le_log (by positivity) hpowr
      rwa [Real.log_pow] at this
    have hΩr : ArithmeticFunction.cardFactors (N - p) ≤ 20 := by
      by_contra hcon
      push Not at hcon
      have h21 : (21 : ℝ) ≤ (ArithmeticFunction.cardFactors (N - p) : ℝ) := by exact_mod_cast hcon
      have hl0 : 0 < Real.log ((z : ℝ) + 1) := by linarith
      have : 21 * Real.log ((z : ℝ) + 1) ≤ ℓ :=
        (mul_le_mul_of_nonneg_right h21 hl0.le).trans hlogpow
      rw [hL] at hlogz1
      linarith
    refine mem_image.mpr ⟨p, ?_, rfl⟩
    rw [hGd, mem_filter, mem_filter, mem_range]
    exact ⟨⟨hpN, hpp⟩, hΩr⟩
  have hc1 : Surv.card ≤ (Surv \ small).card + small.card := card_le_card_sdiff_add_card
  have hc2 : (Surv \ small).card ≤ Gd.card := (card_le_card hsub).trans card_image_le
  have hc3 : (Surv.card : ℝ) ≤ (Gd.card : ℝ) + (z : ℝ) + 1 := by
    have : Surv.card ≤ Gd.card + (z + 1) := by omega
    exact_mod_cast this
  -- the count
  have hfin : 21 / 2 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 - |K| * N / ℓ ^ (3 : ℝ) ≤
      (Surv.card : ℝ) := by rw [← hcardS]; linarith
  have hgoal : 9 * Real.exp (-36) * N / ℓ ^ 2 ≤
      21 / 2 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 -
        (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := Real.exp_pos (-37 : ℝ); have e2 := Real.exp_pos (-36 : ℝ)
    nlinarith [mul_nonneg e2.le (show (0 : ℝ) ≤ (N : ℝ) - 38 by linarith),
      mul_nonneg e1.le (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  linarith only [hgoal, hfin, hc3, hE3, hzle]


open Filter in
/-- **Rényi's theorem with the count and `K = 20`, PROVED unconditional**: for every large even
`N`, `#{p < N prime : Ω(N - p) ≤ 20} ≥ 10 e^{-36} N/log² N`. Ineffective, through Siegel-Walfisz. -/
theorem renyi20_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    9 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 20)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_blocks_rel5 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 2100)))
  refine ⟨⌈max (max X X₂) Y⌉₊, fun N hN hE => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact renyi20_count hK N hE (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's theorem with `K = 20`, PROVED unconditional.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 20`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN; Chen 1973 has `Ω(m) ≤ 2` by a far stronger sieve. -/
theorem renyi20_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 20 := by
  obtain ⟨N₀, hN₀⟩ := renyi20_fixedK_count
  refine ⟨max N₀ 4, fun N hN hE => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) hE
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < 9 * Real.exp (-36) * N / Real.log N ^ 2 := by positivity
  have hc : 0 < (((range N).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 20)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨p, hp⟩ := card_pos.mp hc
  simp only [mem_filter, mem_range] at hp
  obtain ⟨⟨hpN, hpp⟩, hΩ⟩ := hp
  exact ⟨p, N - p, hpp, by omega, by omega, hΩ⟩

end LeanLab.PNTPort.BVMax
