module

public import LeanLab.PNTPort.BVMax.RenyiRealBase

/-!
# Rényi's theorem with `K = 23`, paired block levels

Unit U-6057, CLOUD 20261020T0516Z-cloud35. AI wrote the Lean code. Known mathematics, IDEAS I-5051.

`RenyiRealBase.lean` raises the level by 2 at every block on the way down, so the level of the
whole list is `exp(14 L)` at top level 4. Here the level rises by 2 only every second block,
`lvP 4 d = 4 + 2⌊d/2⌋` at depth `d`, so the sharp blocks pair up, `Σ ρ ≤ (60/29) fR 4 < 0.096`,
and the level is `exp((34/3) L)`, `FP 0 = 34/3`. With `L = log N/24`, `(34/3)/24 < 0.49`, and every
prime factor of a survivor exceeds `exp(log N/24)`, so `Ω(N - p) ≤ 23`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN; Chen's `Ω(m) ≤ 2` is far stronger than this route.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- The level at depth `d`: it rises by 2 every second block. -/
def lvP (r d : ℕ) : ℕ := r + 2 * (d / 2)

lemma lvP_mono (r : ℕ) {d e : ℕ} (h : d ≤ e) : lvP r d ≤ lvP r e := by
  unfold lvP; have := Nat.div_le_div_right (c := 2) h; omega

lemma lvP_even {r : ℕ} (hr : Even r) (d : ℕ) : Even (lvP r d) := by
  unfold lvP; exact hr.add (even_two_mul _)

/-- Blocks `j, …, 0` on the real scale with the paired levels, starting at depth `d`. -/
noncomputable def GP (N : ℕ) (c : ℝ) : ℕ → ℕ → ℕ → List Block
  | 0, r, d => [(blkE N c 0, lvP r d, lvP r d + 1)]
  | j + 1, r, d => (blkE N c (j + 1), lvP r d, lvP r d + 1) :: GP N c j r (d + 1)

lemma GP_length (N : ℕ) (c : ℝ) : ∀ j r d, (GP N c j r d).length = j + 1
  | 0, r, d => by simp [GP]
  | j + 1, r, d => by simp [GP, GP_length N c j r (d + 1)]

lemma GP_mem (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j r d, ∀ p ∈ univB (GP N c j r d),
    (p : ℝ) ≤ thr c (j + 1) ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p
  | 0, r, d, p, hp => by
    simp only [GP, univB, union_empty] at hp
    obtain ⟨h1, h2, h3, h4, -⟩ := blkE_mem hp
    exact ⟨h1, h2, h3, h4⟩
  | j + 1, r, d, p, hp => by
    simp only [GP, univB, mem_union] at hp
    rcases hp with h | h
    · obtain ⟨h1, h2, h3, h4, -⟩ := blkE_mem h
      exact ⟨h1, h2, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := GP_mem N hc j r (d + 1) p h
      exact ⟨h1.trans (thr_mono hc (by omega)), h2, h3, h4⟩

lemma GP_good (N : ℕ) {c : ℝ} (hc : 0 ≤ c) {r : ℕ} (hr : Even r) : ∀ j d, Good (GP N c j r d)
  | 0, d => by
    simp only [GP, Good, univB]
    exact ⟨fun p hp => (blkE_mem hp).2.1, disjoint_empty_right _, lvP_even hr d,
      (lvP_even hr d).add_one, trivial⟩
  | j + 1, d => by
    simp only [GP, Good]
    refine ⟨fun p hp => (blkE_mem hp).2.1, ?_, lvP_even hr d, (lvP_even hr d).add_one,
      GP_good N hc hr j (d + 1)⟩
    rw [disjoint_left]
    intro p hp hp'
    have h1 := (GP_mem N hc j r (d + 1) p hp').1
    rcases (blkE_mem hp).2.2.2.2 with h | h
    · omega
    · linarith

lemma GP_cover (N : ℕ) (c : ℝ) : ∀ j r d, ∀ p, p.Prime → ¬ p ∣ N → 3 ≤ p →
    (p : ℝ) ≤ thr c (j + 1) → p ∈ univB (GP N c j r d)
  | 0, r, d, p, hp, hpN, h3, hpz => by
    simp only [GP, univB, union_empty, blkE, mem_filter, mem_Icc]
    exact ⟨⟨h3, Nat.le_floor hpz⟩, hp, hpN, Or.inl trivial⟩
  | j + 1, r, d, p, hp, hpN, h3, hpz => by
    simp only [GP, univB, mem_union]
    by_cases h : (p : ℝ) ≤ thr c (j + 1)
    · exact Or.inr (GP_cover N c j r (d + 1) p hp hpN h3 h)
    · left
      simp only [blkE, mem_filter, mem_Icc]
      exact ⟨⟨h3, Nat.le_floor hpz⟩, hp, hpN, Or.inr (not_le.mp h)⟩

/-- The level exponent at depth `d` for top level 4: `34/3 + 2d`, less `2/3` at odd depth. -/
noncomputable def FP (d : ℕ) : ℝ := 34 / 3 + 2 * d - 2 / 3 * ((d % 2 : ℕ) : ℝ)

lemma lvP_FP (d : ℕ) : ((lvP 4 d : ℕ) : ℝ) + 1 ≤ FP d ∧
    ((lvP 4 d : ℕ) : ℝ) + 1 + FP (d + 1) / 2 ≤ FP d := by
  unfold FP lvP
  rcases Nat.even_or_odd' d with ⟨m, rfl | rfl⟩
  · have h1 : 2 * m / 2 = m := by omega
    have h2 : 2 * m % 2 = 0 := by omega
    have h3 : (2 * m + 1) % 2 = 1 := by omega
    rw [h1, h2, h3]; push_cast
    constructor <;> nlinarith
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    have h3 : (2 * m + 1 + 1) % 2 = 0 := by omega
    rw [h1, h2, h3]; push_cast
    constructor <;> nlinarith

lemma GP_lev (N : ℕ) {c : ℝ} (hc : 0 ≤ c) : ∀ j d,
    (lev (GP N c j 4 d) : ℝ) ≤ Real.exp (2 ^ (j + 1) * c * FP d)
  | 0, d => by
    simp only [GP, lev, mul_one]
    rw [show max (lvP 4 d) (lvP 4 d + 1) = lvP 4 d + 1 by omega]
    push_cast
    have hs := blkE_sup_le N hc 0
    push_cast at hs
    calc (max (((blkE N c 0).sup id : ℕ) : ℝ) 1) ^ (lvP 4 d + 1) ≤ thr c (0 + 1) ^ (lvP 4 d + 1) :=
          pow_le_pow_left₀ (by positivity) hs _
      _ = Real.exp (2 ^ (0 + 1) * c * ((lvP 4 d + 1 : ℕ) : ℝ)) := thr_pow c _ _
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have := (lvP_FP d).1
          push_cast at this ⊢
          nlinarith
  | j + 1, d => by
    simp only [GP, lev]
    rw [show max (lvP 4 d) (lvP 4 d + 1) = lvP 4 d + 1 by omega]
    push_cast
    have hs := blkE_sup_le N hc (j + 1)
    push_cast at hs
    have ih := GP_lev N hc j (d + 1)
    calc (max (((blkE N c (j + 1)).sup id : ℕ) : ℝ) 1) ^ (lvP 4 d + 1) * (lev (GP N c j 4 (d + 1)) : ℝ)
        ≤ thr c (j + 1 + 1) ^ (lvP 4 d + 1) * Real.exp (2 ^ (j + 1) * c * FP (d + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hs _) ih (Nat.cast_nonneg _)
            (pow_nonneg (thr_pos c _).le _)
      _ ≤ Real.exp (2 ^ (j + 1 + 1) * c * FP d) := by
          rw [thr_pow, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h := (lvP_FP d).2
          have h2 : (0 : ℝ) ≤ 2 ^ (j + 1) * c := by positivity
          have e : (2 : ℝ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
          rw [e]; push_cast at h ⊢
          nlinarith [mul_le_mul_of_nonneg_left h h2]

lemma fR_step30 (L : ℕ) (hL : 4 ≤ L) : 30 * fR (L + 2) ≤ fR L := by
  unfold fR
  have hf : ((L + 2 + 1).factorial : ℝ) = (L + 3) * (L + 2) * (L + 1).factorial := by
    rw [show L + 2 + 1 = (L + 1 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf]
  have hF : (0 : ℝ) < (L + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hL' : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have he := Real.exp_pos (6 / 5 : ℝ)
  have hp : (0 : ℝ) < (11 / 10 : ℝ) ^ (L + 1) := by positivity
  rw [show L + 2 + 1 = (L + 1) + 2 by ring, pow_add]
  have e2 : 30 * (Real.exp (6 / 5) * ((11 / 10 : ℝ) ^ (L + 1) * (11 / 10) ^ 2) /
      ((L + 3) * (L + 2) * (L + 1).factorial)) =
      (30 * (Real.exp (6 / 5) * ((11 / 10 : ℝ) ^ (L + 1) * (11 / 10) ^ 2))) /
      ((L + 3) * (L + 2) * (L + 1).factorial) := by ring
  rw [e2, div_le_div_iff₀ (by positivity) hF]
  have h6 : (42 : ℝ) ≤ (L + 3) * (L + 2) := by nlinarith
  have hpos : 0 < Real.exp (6 / 5) * (11 / 10 : ℝ) ^ (L + 1) * (L + 1).factorial := by positivity
  nlinarith

/-- The running bound of the sharp part. -/
noncomputable def GG (d : ℕ) : ℝ :=
  if d % 2 = 0 then 60 / 29 * fR (lvP 4 d) else fR (lvP 4 d) + 60 / 29 * fR (lvP 4 d + 2)

lemma GG_nonneg (d : ℕ) : 0 ≤ GG d := by
  unfold GG; have := fR_nonneg (lvP 4 d); have := fR_nonneg (lvP 4 d + 2)
  split_ifs <;> positivity

lemma GG_step (d : ℕ) : fR (lvP 4 d) + GG (d + 1) ≤ GG d := by
  unfold GG
  have h4 : 4 ≤ lvP 4 d := by unfold lvP; omega
  rcases Nat.even_or_odd' d with ⟨m, rfl | rfl⟩
  · have h1 : (2 * m + 1) % 2 ≠ 0 := by omega
    have h2 : 2 * m % 2 = 0 := by omega
    have hl : lvP 4 (2 * m + 1) = lvP 4 (2 * m) := by unfold lvP; omega
    rw [if_neg h1, if_pos h2, hl]
    have := fR_step30 _ h4
    linarith
  · have h1 : (2 * m + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 ≠ 0 := by omega
    have hl : lvP 4 (2 * m + 1 + 1) = lvP 4 (2 * m + 1) + 2 := by unfold lvP; omega
    rw [if_pos h1, if_neg h2, hl]

/-- Crude: `Σ ρ ≤ (j + 1) e^{93 - lvP r d}` over `GP N c j r d` when `lvP r d ≥ 1000`. -/
lemma GP_rho (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) (r : ℕ) :
    ∀ j d, 1000 ≤ lvP r d → rhoSum xDen (GP N c j r d) ≤ (j + 1) * Real.exp (93 - lvP r d)
  | 0, d, hd => by
    simp only [GP, rhoSum, add_zero]
    have := rho_crude_of _ _ (fun p hp => (blkE_mem hp).2.2.2.1) (blkE_xsum N hc hc2 0) hd
    push_cast; linarith
  | j + 1, d, hd => by
    simp only [GP, rhoSum]
    have h1 := rho_crude_of _ _ (fun p hp => (blkE_mem hp).2.2.2.1) (blkE_xsum N hc hc2 (j + 1)) hd
    have hm := lvP_mono r (Nat.le_succ d)
    have h2 := GP_rho N hc hc2 r j (d + 1) (hd.trans hm)
    have h3 : Real.exp (93 - ((lvP r (d + 1) : ℕ) : ℝ)) ≤ Real.exp (93 - lvP r d) :=
      Real.exp_le_exp.mpr (by have : ((lvP r d : ℕ) : ℝ) ≤ lvP r (d + 1) := by exact_mod_cast hm
                              linarith)
    have h4 : ((j + 1 : ℕ) : ℝ) * Real.exp (93 - ((lvP r (d + 1) : ℕ) : ℝ)) ≤
        ((j + 1 : ℕ) : ℝ) * Real.exp (93 - lvP r d) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    push_cast at h2 h4 ⊢
    linarith

/-- **`Σ ρ ≤ GG d + 9 e^{93 - lvP 4 (d + (j - 8))}`** over `GP N c j 4 d` for `j ≥ 8`. -/
lemma GP_rho_sharp (N : ℕ) {c : ℝ} (hc : Real.log 2 ≤ c) (hc2 : c ≤ 2 * Real.log 2) :
    ∀ j, 8 ≤ j → ∀ d, 1000 ≤ lvP 4 (d + (j - 8)) →
      rhoSum xDen (GP N c j 4 d) ≤ GG d + 9 * Real.exp (93 - ((lvP 4 (d + (j - 8)) : ℕ) : ℝ)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro d hd
    simp only [Nat.sub_self, add_zero] at hd ⊢
    have := GP_rho N hc hc2 4 8 d hd
    have := GG_nonneg d
    push_cast at *
    linarith
  | succ j hj ih =>
    intro d hd
    simp only [GP, rhoSum]
    obtain ⟨h101, hs⟩ := blkE_sharp N hc hc2 (j := j + 1) (by omega)
    have h1 := rho_sharp_of _ (lvP 4 d) h101 hs
    have e : d + 1 + (j - 8) = d + (j + 1 - 8) := by omega
    have h2 := ih (d + 1) (by rw [e]; exact hd)
    rw [e] at h2
    have h3 := GG_step d
    linarith

lemma exp_neg_907_le' : Real.exp (-907) ≤ 1 / 8000 := by
  have h3 : Real.exp (-3) ≤ 1 / 20 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have he1 := Real.exp_one_gt_d9
    rw [h2]
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
    norm_num at this ⊢; linarith
  have : Real.exp (-907) ≤ Real.exp (-3) ^ 3 := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by norm_num)
  have := pow_le_pow_left₀ (Real.exp_pos (-3 : ℝ)).le h3 3
  norm_num at this; linarith

lemma big_aux3 (ℓ : ℝ) (h : (2 : ℝ) ^ 1100 ≤ ℓ) :
    (10 : ℝ) ^ 6 ≤ ℓ ∧ 2 ^ 1005 ≤ ⌊ℓ / (24 * Real.log 2)⌋₊ := by
  have h2p : (2 : ℝ) ^ 1100 = 2 ^ 95 * 2 ^ 1005 := by rw [← pow_add]
  have h94 : (2 : ℝ) ^ 20 ≤ 2 ^ 95 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h1p : (1 : ℝ) ≤ 2 ^ 1005 := one_le_pow₀ (by norm_num)
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hc : ((2 ^ 1005 : ℕ) : ℝ) = (2 : ℝ) ^ 1005 := by push_cast; rfl
  rw [h2p] at h
  rw [h20] at h94
  generalize (2 : ℝ) ^ 95 = C at *
  generalize (2 : ℝ) ^ 1005 = A at *
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

set_option maxHeartbeats 1000000 in
/-- **Rényi with `K = 23`, deterministic core with the count.** -/
theorem renyi23_count {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hE : Even N) (hℓ6 : (2 : ℝ) ^ 1100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    10 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 23)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨h10, ht1005⟩ := big_aux3 ℓ hℓ6
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
  have hN22 : (22 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- t, k and the real scale c
  set t := ⌊ℓ / (24 * Real.log 2)⌋₊ with ht
  have ht1 : ℓ / (24 * Real.log 2) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (ℓ / (24 * Real.log 2)); rw [← ht] at this; linarith
  have ht2 : (t : ℝ) ≤ ℓ / (24 * Real.log 2) := Nat.floor_le (by positivity)
  have htge : 2 ≤ t := le_trans (Nat.le_self_pow (by norm_num) 2) ht1005
  set k := Nat.log 2 t with hk
  have hk1005 : 1005 ≤ k := Nat.le_log_of_pow_le (by norm_num) ht1005
  clear ht1005
  have hkt : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
  have htk : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hkt' : ((2 ^ k : ℕ) : ℝ) ≤ t := by exact_mod_cast hkt
  have htk1 : (t : ℝ) + 1 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
    have : t + 1 ≤ 2 ^ (k + 1) := htk
    have : ((t + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [pow_succ] at this; push_cast at this ⊢; linarith
  set L := ℓ / 24 with hL
  have h2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  set c := L / ((2 ^ k : ℕ) : ℝ) with hc
  have hLe : ℓ / (24 * Real.log 2) * Real.log 2 = L := by rw [hL]; field_simp
  have hc1 : Real.log 2 ≤ c := by
    rw [hc, le_div_iff₀ h2k, ← hLe]
    have := mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
    linarith
  have hc2 : c ≤ 2 * Real.log 2 := by
    rw [hc, div_le_iff₀ h2k, ← hLe]
    have h1 : ℓ / (24 * Real.log 2) ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
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
  set Bs := GP N c j 4 0 with hBs
  have hG : Good Bs := GP_good N hc0 ⟨2, rfl⟩ j 0
  have hmem := GP_mem N hc0 j 4 0
  rw [hjk, hthr] at hmem
  have hcov := GP_cover N c j 4 0
  rw [hjk, hthr] at hcov
  have hlen : Bs.length = k := by rw [hBs, GP_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply Nat.le_floor
    have h1 := GP_lev N hc0 j 0
    rw [hjk] at h1
    have h2 : Real.exp (2 ^ k * c * FP 0) ≤ Real.exp (49 / 100 * ℓ) := by
      apply Real.exp_le_exp.mpr
      rw [h2kc, hL]; unfold FP; push_cast; nlinarith
    exact h1.trans (h2.trans hE2)
  have hρ : rhoSum xDen Bs ≤ 1 / 10 := by
    have hlv0 : 1000 ≤ lvP 4 (0 + (j - 8)) := by unfold lvP; omega
    refine (GP_rho_sharp N hc1 hc2 j (by omega) 0 hlv0).trans ?_
    have hlv : (1000 : ℝ) ≤ ((lvP 4 (0 + (j - 8)) : ℕ) : ℝ) := by exact_mod_cast hlv0
    have h0 : Real.exp (93 - ((lvP 4 (0 + (j - 8)) : ℕ) : ℝ)) ≤ Real.exp (-907) :=
      Real.exp_le_exp.mpr (by linarith)
    have hG : GG 0 = 60 / 29 * fR 4 := by unfold GG lvP; simp
    have := two_fR_four_le
    have := exp_neg_907_le'
    rw [hG]
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
  have hV2 : Real.exp (-36) * 24 / ℓ ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    refine le_trans ?_ hV
    rw [div_le_div_iff₀ hℓpos hlogz_pos]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 24 ≤ ℓ := by rw [hL] at hlogz; linarith
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 24 / ℓ) * (1 / 2) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 24 / ℓ) * (1 / 2) =
      12 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp; ring
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      12 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
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
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 23) with hGd
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
    have hΩr : ArithmeticFunction.cardFactors (N - p) ≤ 23 := by
      by_contra hcon
      push Not at hcon
      have h24 : (24 : ℝ) ≤ (ArithmeticFunction.cardFactors (N - p) : ℝ) := by exact_mod_cast hcon
      have hl0 : 0 < Real.log ((z : ℝ) + 1) := by linarith
      have : 24 * Real.log ((z : ℝ) + 1) ≤ ℓ :=
        (mul_le_mul_of_nonneg_right h24 hl0.le).trans hlogpow
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
  have hfin : 12 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 - |K| * N / ℓ ^ (3 : ℝ) ≤
      (Surv.card : ℝ) := by rw [← hcardS]; linarith
  have hgoal : 10 * Real.exp (-36) * N / ℓ ^ 2 ≤
      12 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 -
        (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := Real.exp_pos (-37 : ℝ); have e2 := Real.exp_pos (-36 : ℝ)
    nlinarith [mul_nonneg e2.le (show (0 : ℝ) ≤ (N : ℝ) - 22 by linarith),
      mul_nonneg e1.le (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  linarith only [hgoal, hfin, hc3, hE3, hzle]


open Filter in
/-- **Rényi's theorem with the count and `K = 23`, PROVED unconditional**: for every large even
`N`, `#{p < N prime : Ω(N - p) ≤ 23} ≥ 10 e^{-36} N/log² N`. Ineffective, through Siegel-Walfisz. -/
theorem renyi23_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    10 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 23)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_blocks_rel 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 1100)))
  refine ⟨⌈max (max X X₂) Y⌉₊, fun N hN hE => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact renyi23_count hK N hE (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's theorem with `K = 23`, PROVED unconditional.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 23`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN; Chen 1973 has `Ω(m) ≤ 2` by a far stronger sieve. -/
theorem renyi23_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 23 := by
  obtain ⟨N₀, hN₀⟩ := renyi23_fixedK_count
  refine ⟨max N₀ 4, fun N hN hE => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) hE
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < 10 * Real.exp (-36) * N / Real.log N ^ 2 := by positivity
  have hc : 0 < (((range N).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 23)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨p, hp⟩ := card_pos.mp hc
  simp only [mem_filter, mem_range] at hp
  obtain ⟨⟨hpN, hpp⟩, hΩ⟩ := hp
  exact ⟨p, N - p, hpp, by omega, by omega, hΩ⟩

end LeanLab.PNTPort.BVMax

