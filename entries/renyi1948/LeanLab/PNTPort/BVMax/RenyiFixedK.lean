module

public import LeanLab.PNTPort.BVMax.RenyiBlocks
public import LeanLab.PNTSieve.MertensLower
public import LeanLab.PNTPort.BVMax.RenyiMain
public import LeanLab.PNTPort.BVMax.RenyiAssembly

/-!
# The blocks for Rényi's theorem with a fixed number of prime factors

Unit U-5510, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics, IDEAS I-5051.

`blk N j` is the set of primes `p ∤ N` in `(2^{2^j}, 2^{2^{j+1}}]`; `G N j r` is the list of blocks
`j, j - 1, …, 0` with levels `r, r + 2, r + 4, …` on the way down, odd levels one more. By induction on
`j`:

* `G_good`, `G_mem`, `G_cover`: good blocks whose union is exactly the odd primes `p ∤ N` up to
  `z = 2^{2^{j+1}}`;
* `G_lev`: `lev (G N j r) ≤ 2^{2^{j+1}(2r + 6)} = z^{2r + 6}`;
* `G_rho`: for `r ≥ 900`, `Σ ρ_B ≤ 2 e^{85 - r}`, from `Σ_{B} 1/(p - 1) ≤ 43` per block by
  `Mertens.sum_inv_primes_block` and `V_B ≥ e^{-86}`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- The primes `p ∤ N` in `(2^{2^j}, 2^{2^{j+1}}]`. -/
def blk (N j : ℕ) : Finset ℕ :=
  (Ioc (2 ^ (2 ^ j)) (2 ^ (2 ^ (j + 1)))).filter (fun p => p.Prime ∧ ¬ p ∣ N)

/-- Blocks `j, j - 1, …, 0`, the level rising by 2 at each step down. -/
def G (N : ℕ) : ℕ → ℕ → List Block
  | 0, r => [(blk N 0, r, r + 1)]
  | j + 1, r => (blk N (j + 1), r, r + 1) :: G N j (r + 2)

lemma G_length (N : ℕ) : ∀ j r, (G N j r).length = j + 1
  | 0, _ => rfl
  | j + 1, r => by simp [G, G_length N j (r + 2)]

lemma two_pow_pow_mono {i j : ℕ} (h : i ≤ j) : 2 ^ (2 ^ i) ≤ 2 ^ (2 ^ j) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

lemma G_mem (N : ℕ) : ∀ j r, ∀ p ∈ univB (G N j r),
    p ≤ 2 ^ (2 ^ (j + 1)) ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p
  | 0, r, p, hp => by
    simp only [G, univB, union_empty, blk, mem_filter, mem_Ioc] at hp
    norm_num at hp
    exact ⟨by norm_num; omega, hp.2.1, hp.2.2, by omega⟩
  | j + 1, r, p, hp => by
    simp only [G, univB, mem_union] at hp
    rcases hp with h | h
    · simp only [blk, mem_filter, mem_Ioc] at h
      have : 2 ≤ 2 ^ (2 ^ (j + 1)) := by
        calc 2 = 2 ^ (2 ^ 0) := by norm_num
          _ ≤ _ := two_pow_pow_mono (by omega)
      exact ⟨h.1.2, h.2.1, h.2.2, by omega⟩
    · obtain ⟨h1, h2, h3, h4⟩ := G_mem N j (r + 2) p h
      exact ⟨h1.trans (two_pow_pow_mono (by omega)), h2, h3, h4⟩

lemma G_good (N : ℕ) : ∀ j r, Even r → Good (G N j r)
  | 0, r, hr => by
    simp only [G, Good, univB]
    refine ⟨fun p hp => ?_, disjoint_empty_right _, hr, hr.add_one, trivial⟩
    simp only [blk, mem_filter] at hp; exact hp.2.1
  | j + 1, r, hr => by
    simp only [G, Good]
    refine ⟨fun p hp => ?_, ?_, hr, hr.add_one, G_good N j (r + 2) (by
      rcases hr with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩)⟩
    · simp only [blk, mem_filter] at hp; exact hp.2.1
    · rw [disjoint_left]
      intro p hp hp'
      have := (G_mem N j (r + 2) p hp').1
      simp only [blk, mem_filter, mem_Ioc] at hp
      omega

lemma G_cover (N : ℕ) : ∀ j r, ∀ p, p.Prime → ¬ p ∣ N → 3 ≤ p → p ≤ 2 ^ (2 ^ (j + 1)) →
    p ∈ univB (G N j r)
  | 0, r, p, hp, hpN, h3, hpz => by
    simp only [G, univB, union_empty, blk, mem_filter, mem_Ioc]
    norm_num at hpz ⊢
    exact ⟨⟨by omega, hpz⟩, hp, hpN⟩
  | j + 1, r, p, hp, hpN, h3, hpz => by
    simp only [G, univB, mem_union]
    by_cases h : p ≤ 2 ^ (2 ^ (j + 1))
    · exact Or.inr (G_cover N j (r + 2) p hp hpN h3 h)
    · left
      simp only [blk, mem_filter, mem_Ioc]
      exact ⟨⟨by omega, hpz⟩, hp, hpN⟩

lemma blk_sup_le (N j : ℕ) : max ((blk N j).sup id) 1 ≤ 2 ^ (2 ^ (j + 1)) := by
  apply max_le
  · apply Finset.sup_le
    intro p hp
    simp only [blk, mem_filter, mem_Ioc] at hp
    exact hp.1.2
  · exact Nat.one_le_two_pow

lemma G_lev (N : ℕ) : ∀ j r, lev (G N j r) ≤ 2 ^ (2 ^ (j + 1) * (2 * r + 6))
  | 0, r => by
    simp only [G, lev, mul_one]
    rw [show max r (r + 1) = r + 1 by omega]
    calc (max ((blk N 0).sup id) 1) ^ (r + 1) ≤ (2 ^ (2 ^ (0 + 1))) ^ (r + 1) :=
          Nat.pow_le_pow_left (blk_sup_le N 0) _
      _ ≤ 2 ^ (2 ^ (0 + 1) * (2 * r + 6)) := by
          rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  | j + 1, r => by
    simp only [G, lev]
    rw [show max r (r + 1) = r + 1 by omega]
    have ih := G_lev N j (r + 2)
    calc (max ((blk N (j + 1)).sup id) 1) ^ (r + 1) * lev (G N j (r + 2))
        ≤ (2 ^ (2 ^ (j + 1 + 1))) ^ (r + 1) * 2 ^ (2 ^ (j + 1) * (2 * (r + 2) + 6)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (blk_sup_le N (j + 1)) _) ih
      _ = 2 ^ (2 ^ (j + 1 + 1) * (2 * r + 6)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          rw [pow_succ]
          ring

lemma xDen_le_two_div (p : ℕ) (hp : 3 ≤ p) : xDen p ≤ 2 * (1 / (p : ℝ)) := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold xDen
  rw [if_pos hp, mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

lemma blk_mem (N j p : ℕ) (hp : p ∈ blk N j) : p.Prime ∧ 3 ≤ p := by
  simp only [blk, mem_filter, mem_Ioc] at hp
  have : 2 ≤ 2 ^ (2 ^ j) := by
    calc 2 = 2 ^ (2 ^ 0) := by norm_num
      _ ≤ _ := two_pow_pow_mono (by omega)
  exact ⟨hp.2.1, by omega⟩

/-- Each block has `Σ 1/(p - 1) ≤ 43`. -/
lemma blk_xsum (N j : ℕ) : ∑ p ∈ blk N j, xDen p ≤ 43 := by
  set y := 2 ^ (2 ^ j) with hy
  have hy2 : 2 ≤ y := by
    calc 2 = 2 ^ (2 ^ 0) := by norm_num
      _ ≤ _ := two_pow_pow_mono (by omega)
  have hw : 2 ^ (2 ^ (j + 1)) = y ^ 2 := by rw [hy, ← pow_mul, pow_succ]
  have hsub : blk N j ⊆ (Ioc y (y ^ 2)).filter Nat.Prime := by
    intro p hp
    simp only [blk, mem_filter, mem_Ioc] at hp ⊢
    rw [← hw]; exact ⟨hp.1, hp.2.1⟩
  have hM := LeanLab.PNTSieve.Mertens.sum_inv_primes_block y (y ^ 2) hy2 (by nlinarith)
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
  have hl2 := Real.log_two_gt_d9
  have hlpos : 0 < Real.log y := by linarith
  have hsq : Real.log ((y ^ 2 : ℕ) : ℝ) = 2 * Real.log y := by
    push_cast; rw [Real.log_pow]; norm_num
  rw [hsq] at hM
  have hM2 : (2 * Real.log y - Real.log y + 14) / Real.log y ≤ 21.2 := by
    rw [div_le_iff₀ hlpos]; nlinarith
  calc ∑ p ∈ blk N j, xDen p ≤ ∑ p ∈ blk N j, 2 * (1 / (p : ℝ)) :=
        sum_le_sum (fun p hp => xDen_le_two_div p (blk_mem N j p hp).2)
    _ = 2 * ∑ p ∈ blk N j, (1 / (p : ℝ)) := by rw [mul_sum]
    _ ≤ 2 * ∑ p ∈ (Ioc y (y ^ 2)).filter Nat.Prime, (1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 43 := by linarith

/-- Each block has `V_B ≥ e^{-86}`. -/
lemma blk_V (N j : ℕ) : Real.exp (-86) ≤ ∏ p ∈ blk N j, (1 - xDen p) := by
  have h0 : ∀ p ∈ blk N j, 0 ≤ xDen p := fun p _ => xDen_nonneg p
  have h1 : ∀ p ∈ blk N j, xDen p ≤ 1 / 2 := by
    intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (blk_mem N j p hp).2
    unfold xDen
    rw [if_pos (blk_mem N j p hp).2, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine le_trans ?_ (LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp _ _ h0 h1)
  apply Real.exp_le_exp.mpr
  have hsq : ∑ p ∈ blk N j, xDen p ^ 2 ≤ ∑ p ∈ blk N j, xDen p / 2 := by
    apply sum_le_sum; intro p hp; nlinarith [h0 p hp, h1 p hp]
  rw [← sum_div] at hsq
  have := blk_xsum N j
  linarith

lemma exp3_lt : Real.exp 3 < 21 := by
  have := Real.exp_one_lt_d9
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h1 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ h0 this.le 3
  norm_num at h1
  linarith

/-- For `r ≥ 1000` the block ratio is at most `e^{85 - r}`. -/
lemma rho_blk (N j r : ℕ) (hr : 1000 ≤ r) :
    rho xDen (blk N j, r, r + 1) ≤ Real.exp (85 - r) := by
  have hu0 : 0 ≤ ∑ p ∈ blk N j, xDen p := sum_nonneg (fun p _ => xDen_nonneg p)
  have hu := blk_xsum N j
  have hr' : (1000 : ℝ) ≤ r := by exact_mod_cast hr
  have he := exp3_lt
  have hE : ∀ n : ℕ, r + 1 ≤ n → truncErr (blk N j) xDen (n - 1) ≤ Real.exp (-(r + 1 : ℝ)) := by
    intro n hn
    unfold truncErr
    rw [Nat.sub_add_cancel (by omega)]
    have hn' : ((r : ℝ) + 1) ≤ n := by exact_mod_cast hn
    have h := pow_div_factorial_le_exp_neg _ hu0 n (by nlinarith)
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have h1 := hE (r + 1) le_rfl
  have h2 := hE (r + 2) (by omega)
  simp only [Nat.add_sub_cancel] at h1
  rw [show r + 2 - 1 = r + 1 by omega] at h2
  have hV := blk_V N j
  have hVpos : 0 < ∏ p ∈ blk N j, (1 - xDen p) := lt_of_lt_of_le (Real.exp_pos _) hV
  unfold rho
  simp only
  rw [div_le_iff₀ hVpos]
  calc max (truncErr (blk N j) xDen r) (truncErr (blk N j) xDen (r + 1))
      ≤ Real.exp (-(r + 1 : ℝ)) := max_le h1 h2
    _ = Real.exp (85 - r) * Real.exp (-86) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (85 - r) * ∏ p ∈ blk N j, (1 - xDen p) :=
        mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le

/-- **`Σ ρ_B ≤ 2 e^{85 - r}`** over the blocks of `G N j r`, for `r ≥ 1000`. -/
lemma G_rho (N : ℕ) : ∀ j r, 1000 ≤ r → rhoSum xDen (G N j r) ≤ 2 * Real.exp (85 - r)
  | 0, r, hr => by
    simp only [G, rhoSum, add_zero]
    have := rho_blk N 0 r hr
    have := Real.exp_pos (85 - (r : ℝ))
    linarith
  | j + 1, r, hr => by
    simp only [G, rhoSum]
    have h1 := rho_blk N (j + 1) r hr
    have h2 := G_rho N j (r + 2) (by omega)
    have e : Real.exp (85 - ((r + 2 : ℕ) : ℝ)) = Real.exp (85 - r) * Real.exp (-2) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have he2 : Real.exp (-2) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have hpos := Real.exp_pos (85 - (r : ℝ))
    rw [e] at h2
    nlinarith

lemma two_pow_cast (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = Real.exp ((n : ℝ) * Real.log 2) := by
  rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num), Real.rpow_natCast]
  push_cast; ring

/-- **The deterministic core of Rényi's theorem with `K = 13000`.** `B, K` come from
`renyi_blocks_rel` at `A = 5`; at an even `N` with `log N ≥ 10⁶` and the two inequalities of
`renyi_large` (with `|K|`), `N = p + m` with `Ω(m) ≤ 13000`. -/
theorem renyiK_core {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hE : Even N) (hℓ6 : 10 ^ 6 ≤ Real.log N)
    (hE2 : Real.exp (Real.log N / 3) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 13000 := by
  classical
  set ℓ := Real.log N with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN4 : (4 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast hN4
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- t and k
  set t := ⌊ℓ / (6018 * Real.log 2)⌋₊ with ht
  have ht1 : ℓ / (6018 * Real.log 2) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (ℓ / (6018 * Real.log 2)); rw [← ht] at this; linarith
  have ht2 : (t : ℝ) ≤ ℓ / (6018 * Real.log 2) := Nat.floor_le (by positivity)
  have hbig : (100 : ℝ) ≤ ℓ / (6018 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have htge : 2 ≤ t := by
    have : (2 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  set k := Nat.log 2 t with hk
  have hk1 : 1 ≤ k := Nat.log_pos (by norm_num) htge
  have hkt : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
  have htk : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hkt' : ((2 ^ k : ℕ) : ℝ) ≤ t := by exact_mod_cast hkt
  have htk' : (t : ℝ) < 2 * ((2 ^ k : ℕ) : ℝ) := by
    have : (t : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast htk
    rw [pow_succ] at this; push_cast at this ⊢; linarith
  set j := k - 1 with hj
  have hjk : j + 1 = k := by omega
  set z := 2 ^ (2 ^ k) with hz
  have hzr : (z : ℝ) = Real.exp ((2 ^ k : ℕ) * Real.log 2) := by
    rw [hz, two_pow_cast]
  have hlogz : Real.log z = ((2 ^ k : ℕ) : ℝ) * Real.log 2 := by rw [hzr, Real.log_exp]
  have hlogz_hi : Real.log z ≤ ℓ / 6018 := by
    rw [hlogz]
    calc ((2 ^ k : ℕ) : ℝ) * Real.log 2 ≤ ℓ / (6018 * Real.log 2) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
      _ = ℓ / 6018 := by field_simp
  have hlogz_lo : ℓ / 13000 ≤ Real.log z := by
    rw [hlogz]
    have h1 : ℓ / (6018 * Real.log 2) - 1 < 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
    have h2 : ℓ / 6018 - Real.log 2 < 2 * (((2 ^ k : ℕ) : ℝ) * Real.log 2) := by
      have := mul_lt_mul_of_pos_right h1 hl2pos
      have e : (ℓ / (6018 * Real.log 2) - 1) * Real.log 2 = ℓ / 6018 - Real.log 2 := by
        field_simp
      linarith
    nlinarith
  have hlogz_pos : 0 < Real.log z := by linarith
  have hz4 : 4 ≤ z := by
    rw [hz]
    calc 4 = 2 ^ (2 ^ 1) := by norm_num
      _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk1)
  -- the blocks
  set Bs := G N j 1000 with hBs
  have hG : Good Bs := G_good N j 1000 ⟨500, rfl⟩
  have hmem := G_mem N j 1000
  rw [hjk] at hmem
  have hcov := G_cover N j 1000
  rw [hjk] at hcov
  have hlen : Bs.length = k := by rw [hBs, G_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply (G_lev N j 1000).trans
    rw [hjk]
    apply Nat.le_floor
    have hexp : ((2 ^ (2 ^ k * (2 * 1000 + 6)) : ℕ) : ℝ) ≤ Real.exp (ℓ / 3) := by
      have e : ((2 ^ (2 ^ k * (2 * 1000 + 6)) : ℕ) : ℝ) = Real.exp (2006 * Real.log z) := by
        rw [hlogz, two_pow_cast]
        push_cast; ring_nf
      rw [e]; apply Real.exp_le_exp.mpr; linarith
    linarith
  have hρ : rhoSum xDen Bs ≤ 1 / 10 := by
    refine (G_rho N j 1000 le_rfl).trans ?_
    have h0 : Real.exp (85 - ((1000 : ℕ) : ℝ)) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by norm_num)
    have h1 : Real.exp (-3) ≤ 1 / 20 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
      have he := Real.exp_one_gt_d9
      have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
      norm_num at h2 ⊢
      linarith
    norm_num
    have h0' : Real.exp (-915) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by norm_num)
    linarith
  -- the sieve count
  have hS := hK N (by omega) Bs hG (fun p hp => ⟨(hmem p hp).2.2.1, (hmem p hp).2.2.2⟩) hlev hρ
  rw [hlen] at hS
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hV : Real.exp (-36) / Real.log z ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    have := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z (by omega) (univB Bs)
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, (hmem p hp).1⟩)
    refine this.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
    simp only [xDen, if_pos (hmem p hp).2.2.2]
  have hV2 : Real.exp (-36) * 6018 / ℓ ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    refine le_trans ?_ hV
    rw [div_le_div_iff₀ hℓpos hlogz_pos]
    have := Real.exp_pos (-36 : ℝ)
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 6018 / ℓ) * (1 / 2) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 6018 / ℓ) * (1 / 2) =
      3009 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp; ring
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      3009 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
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
  push_cast at hS
  have hzle : (z : ℝ) ≤ Real.exp (ℓ / 3) := by
    rw [hzr]; apply Real.exp_le_exp.mpr; rw [← hlogz]; linarith
  have hSbig : (z : ℝ) + 2 ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ) := by linarith
  -- a survivor N - p with p > z
  set Surv := (goldbachSeq N).filter (fun a => ∀ p ∈ univB Bs, ¬ p ∣ a) with hSurv
  have hcardS : (z : ℝ) + 2 ≤ (Surv.card : ℝ) := by
    have : (sifted (goldbachSeq N) (univB Bs) : ℝ) = (Surv.card : ℝ) := by
      simp [sifted, hSurv]
    linarith
  have hsmall : ((range (z + 1)).image (fun p => N - p)).card ≤ z + 1 :=
    card_image_le.trans (by simp)
  obtain ⟨m, hmS, hmn⟩ : ∃ m ∈ Surv, m ∉ (range (z + 1)).image (fun p => N - p) := by
    by_contra h
    push Not at h
    have hsub : Surv ⊆ (range (z + 1)).image (fun p => N - p) := fun m hm => h m hm
    have := card_le_card hsub
    have : (Surv.card : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast this.trans hsmall
    linarith
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
  have hfac_big : ∀ q ∈ (N - p).primeFactorsList, z ≤ q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactorsList hq
    have hqd := Nat.dvd_of_mem_primeFactorsList hq
    by_contra hlt
    push Not at hlt
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
    · exact hmP q (hcov q hqp hqN hq3 hlt.le) hqd
  have hpow := pow_bigOmega_le (N - p) z hm0 hfac_big
  set Ω := ArithmeticFunction.cardFactors (N - p) with hΩ
  have hpowr : (z : ℝ) ^ Ω ≤ N := by
    have : z ^ Ω ≤ N := hpow.trans (Nat.sub_le N p)
    exact_mod_cast this
  have hlogpow : (Ω : ℝ) * Real.log z ≤ ℓ := by
    have := Real.log_le_log (by positivity) hpowr
    rwa [Real.log_pow] at this
  have hΩr : (Ω : ℝ) ≤ 13000 := by
    have h1 : (Ω : ℝ) * (ℓ / 13000) ≤ ℓ :=
      (mul_le_mul_of_nonneg_left hlogz_lo (Nat.cast_nonneg _)).trans hlogpow
    have h2 : (Ω : ℝ) * (ℓ / 13000) = (Ω : ℝ) * ℓ / 13000 := by ring
    rw [h2, div_le_iff₀ (by norm_num)] at h1
    exact le_of_mul_le_mul_right (h1.trans_eq (mul_comm _ _)) hℓpos
  refine ⟨p, N - p, hpp, by omega, by omega, ?_⟩
  exact_mod_cast hΩr


set_option maxHeartbeats 1000000 in
/-- Rényi with the count, deterministic core. -/
theorem renyiK_count {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hE : Even N) (hℓ6 : 10 ^ 6 ≤ Real.log N)
    (hE2 : Real.exp (Real.log N / 3) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    1000 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 13000)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN4 : (4 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast hN4
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- t and k
  set t := ⌊ℓ / (6018 * Real.log 2)⌋₊ with ht
  have ht1 : ℓ / (6018 * Real.log 2) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (ℓ / (6018 * Real.log 2)); rw [← ht] at this; linarith
  have ht2 : (t : ℝ) ≤ ℓ / (6018 * Real.log 2) := Nat.floor_le (by positivity)
  have hbig : (100 : ℝ) ≤ ℓ / (6018 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have htge : 2 ≤ t := by
    have : (2 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  set k := Nat.log 2 t with hk
  have hk1 : 1 ≤ k := Nat.log_pos (by norm_num) htge
  have hkt : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
  have htk : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hkt' : ((2 ^ k : ℕ) : ℝ) ≤ t := by exact_mod_cast hkt
  have htk' : (t : ℝ) < 2 * ((2 ^ k : ℕ) : ℝ) := by
    have : (t : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast htk
    rw [pow_succ] at this; push_cast at this ⊢; linarith
  set j := k - 1 with hj
  have hjk : j + 1 = k := by omega
  set z := 2 ^ (2 ^ k) with hz
  have hzr : (z : ℝ) = Real.exp ((2 ^ k : ℕ) * Real.log 2) := by
    rw [hz, two_pow_cast]
  have hlogz : Real.log z = ((2 ^ k : ℕ) : ℝ) * Real.log 2 := by rw [hzr, Real.log_exp]
  have hlogz_hi : Real.log z ≤ ℓ / 6018 := by
    rw [hlogz]
    calc ((2 ^ k : ℕ) : ℝ) * Real.log 2 ≤ ℓ / (6018 * Real.log 2) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
      _ = ℓ / 6018 := by field_simp
  have hlogz_lo : ℓ / 13000 ≤ Real.log z := by
    rw [hlogz]
    have h1 : ℓ / (6018 * Real.log 2) - 1 < 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
    have h2 : ℓ / 6018 - Real.log 2 < 2 * (((2 ^ k : ℕ) : ℝ) * Real.log 2) := by
      have := mul_lt_mul_of_pos_right h1 hl2pos
      have e : (ℓ / (6018 * Real.log 2) - 1) * Real.log 2 = ℓ / 6018 - Real.log 2 := by
        field_simp
      linarith
    nlinarith
  have hlogz_pos : 0 < Real.log z := by linarith
  have hz4 : 4 ≤ z := by
    rw [hz]
    calc 4 = 2 ^ (2 ^ 1) := by norm_num
      _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk1)
  -- the blocks
  set Bs := G N j 1000 with hBs
  have hG : Good Bs := G_good N j 1000 ⟨500, rfl⟩
  have hmem := G_mem N j 1000
  rw [hjk] at hmem
  have hcov := G_cover N j 1000
  rw [hjk] at hcov
  have hlen : Bs.length = k := by rw [hBs, G_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply (G_lev N j 1000).trans
    rw [hjk]
    apply Nat.le_floor
    have hexp : ((2 ^ (2 ^ k * (2 * 1000 + 6)) : ℕ) : ℝ) ≤ Real.exp (ℓ / 3) := by
      have e : ((2 ^ (2 ^ k * (2 * 1000 + 6)) : ℕ) : ℝ) = Real.exp (2006 * Real.log z) := by
        rw [hlogz, two_pow_cast]
        push_cast; ring_nf
      rw [e]; apply Real.exp_le_exp.mpr; linarith
    linarith
  have hρ : rhoSum xDen Bs ≤ 1 / 10 := by
    refine (G_rho N j 1000 le_rfl).trans ?_
    have h0 : Real.exp (85 - ((1000 : ℕ) : ℝ)) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by norm_num)
    have h1 : Real.exp (-3) ≤ 1 / 20 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
      have he := Real.exp_one_gt_d9
      have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
      norm_num at h2 ⊢
      linarith
    norm_num
    have h0' : Real.exp (-915) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by norm_num)
    linarith
  -- the sieve count
  have hS := hK N (by omega) Bs hG (fun p hp => ⟨(hmem p hp).2.2.1, (hmem p hp).2.2.2⟩) hlev hρ
  rw [hlen] at hS
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hV : Real.exp (-36) / Real.log z ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    have := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z (by omega) (univB Bs)
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, (hmem p hp).1⟩)
    refine this.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
    simp only [xDen, if_pos (hmem p hp).2.2.2]
  have hV2 : Real.exp (-36) * 6018 / ℓ ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    refine le_trans ?_ hV
    rw [div_le_div_iff₀ hℓpos hlogz_pos]
    have := Real.exp_pos (-36 : ℝ)
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 6018 / ℓ) * (1 / 2) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 6018 / ℓ) * (1 / 2) =
      3009 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp; ring
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      3009 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
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
  push_cast at hS
  have hzle : (z : ℝ) ≤ Real.exp (ℓ / 3) := by
    rw [hzr]; apply Real.exp_le_exp.mpr; rw [← hlogz]; linarith
  have hSbig : (z : ℝ) + 2 ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ) := by linarith
  set Surv := (goldbachSeq N).filter (fun a => ∀ p ∈ univB Bs, ¬ p ∣ a) with hSurv
  have hcardS : (sifted (goldbachSeq N) (univB Bs) : ℝ) = (Surv.card : ℝ) := by
    simp [sifted, hSurv]
  set small := (range (z + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ z + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 13000) with hGd
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
    have hfac_big : ∀ q ∈ (N - p).primeFactorsList, z ≤ q := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      by_contra hlt
      push Not at hlt
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
      · exact hmP q (hcov q hqp hqN hq3 hlt.le) hqd
    have hpow := pow_bigOmega_le (N - p) z hm0 hfac_big
    have hpowr : (z : ℝ) ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := by
      have : z ^ (ArithmeticFunction.cardFactors (N - p)) ≤ N := hpow.trans (Nat.sub_le N p)
      exact_mod_cast this
    have hlogpow : (ArithmeticFunction.cardFactors (N - p) : ℝ) * Real.log z ≤ ℓ := by
      have := Real.log_le_log (by positivity) hpowr
      rwa [Real.log_pow] at this
    have hΩr : (ArithmeticFunction.cardFactors (N - p) : ℝ) ≤ 13000 := by
      have h1 : (ArithmeticFunction.cardFactors (N - p) : ℝ) * (ℓ / 13000) ≤ ℓ :=
        (mul_le_mul_of_nonneg_left hlogz_lo (Nat.cast_nonneg _)).trans hlogpow
      have h2 : (ArithmeticFunction.cardFactors (N - p) : ℝ) * (ℓ / 13000) =
          (ArithmeticFunction.cardFactors (N - p) : ℝ) * ℓ / 13000 := by ring
      rw [h2, div_le_iff₀ (by norm_num)] at h1
      exact le_of_mul_le_mul_right (h1.trans_eq (mul_comm _ _)) hℓpos
    refine mem_image.mpr ⟨p, ?_, rfl⟩
    rw [hGd, mem_filter, mem_filter, mem_range]
    exact ⟨⟨hpN, hpp⟩, by exact_mod_cast hΩr⟩
  have hc1 : Surv.card ≤ (Surv \ small).card + small.card := card_le_card_sdiff_add_card
  have hc2 : (Surv \ small).card ≤ Gd.card := (card_le_card hsub).trans card_image_le
  have hc3 : (Surv.card : ℝ) ≤ (Gd.card : ℝ) + (z : ℝ) + 1 := by
    have : Surv.card ≤ Gd.card + (z + 1) := by omega
    exact_mod_cast this
  -- the count
  have hfin : 3009 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 - |K| * N / ℓ ^ (3 : ℝ) ≤
      (Surv.card : ℝ) := by rw [← hcardS]; linarith
  have hgoal : 1000 * Real.exp (-36) * N / ℓ ^ 2 ≤
      3009 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 -
        (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := Real.exp_pos (-37 : ℝ); have e2 := Real.exp_pos (-36 : ℝ)
    nlinarith [mul_nonneg e2.le (show (0 : ℝ) ≤ (N : ℝ) - 4 by linarith),
      mul_nonneg e1.le (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  linarith only [hgoal, hfin, hc3, hE3, hzle]

open Filter in
/-- **Rényi's theorem, PROVED unconditional, with `K = 13000`.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 13000`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN. -/
theorem renyi_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 13000 := by
  obtain ⟨B, -, K, hK⟩ := renyi_blocks_rel 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10 ^ 6 : ℝ)))
  refine ⟨⌈max X Y⌉₊, fun N hN hE => ?_⟩
  have hx : max X Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, h2, h3⟩ := hX N ((le_max_left _ _).trans hx)
  exact renyiK_core hK N hE (hY N ((le_max_right _ _).trans hx)) h2 h3

open Filter in
/-- **Rényi's theorem with the count, PROVED unconditional**: for every large even `N`,
`#{p < N prime : Ω(N - p) ≤ 13000} ≥ 1000 e^{-36} N/log² N`, the order of the Goldbach count. -/
theorem renyi_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    1000 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 13000)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_blocks_rel 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10 ^ 6 : ℝ)))
  refine ⟨⌈max X Y⌉₊, fun N hN hE => ?_⟩
  have hx : max X Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, h2, h3⟩ := hX N ((le_max_left _ _).trans hx)
  exact renyiK_count hK N hE (hY N ((le_max_right _ _).trans hx)) h2 h3

end LeanLab.PNTPort.BVMax

