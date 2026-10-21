module

public import LeanLab.PNTPort.BVMax.RenyiFixedK

/-!
# Rényi's theorem with `K = 59`

Unit U-6050, CLOUD 20261020T0516Z-cloud35. AI wrote the Lean code. Known mathematics, IDEAS I-5051.

`RenyiFixedK.lean` proves `Ω(N - p) ≤ 13000` with the same blocks `G N j r` at the uniform level
`r = 1000`, because its block bound `Σ_B 1/(p - 1) ≤ 43` is what the smallest blocks need. Here:

* `blk_xsum_sharp`: for `j ≥ 8`, so `y = 2^{2^j} ≥ 2^256`, the block sum is at most `11/10`,
  from `Mertens.sum_inv_primes_block`, `Σ_{y < p ≤ y²} 1/p ≤ 1 + 14/log y`;
* `rho_blk_sharp`: those blocks have `ρ ≤ fR L = e^{6/5} 1.1^{L+1}/(L+1)!` at level `L`;
* `G_rho_sharp`: in `G N j r` the level rises by 2 per block on the way down, so once the top
  index `j` is large the eight small blocks `j ≤ 7` sit at level `≥ 1000` and cost `e^{-915}`, while
  the top level can be `r = 4`; `Σ ρ ≤ 2 fR 4 + 2 e^{-915} < 1/10`.

The level is then `z^{2·4 + 6} = z^{14}`, and with level `N^{49/100}` from Bombieri-Vinogradov the
sifting limit is `log z ≤ log N/29`; the dyadic choice of `z` loses a factor 2, so `Ω ≤ 59`.
Binary Goldbach is `Ω(m) = 1` and stays OPEN; Chen's `Ω(m) ≤ 2` is not reached by this route.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

lemma log_two_pow_pow (j : ℕ) : Real.log ((2 ^ (2 ^ j) : ℕ) : ℝ) = ((2 ^ j : ℕ) : ℝ) * Real.log 2 := by
  rw [two_pow_cast, Real.log_exp]

lemma xDen_le_sharp (p : ℕ) (hp : 101 ≤ p) : xDen p ≤ 101 / 100 * (1 / (p : ℝ)) := by
  have h3 : (101 : ℝ) ≤ p := by exact_mod_cast hp
  unfold xDen
  rw [if_pos (by omega), mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

lemma blk_big (N j p : ℕ) (hj : 8 ≤ j) (hp : p ∈ blk N j) : 2 ^ 256 < p := by
  simp only [blk, mem_filter, mem_Ioc] at hp
  have : 2 ^ 256 ≤ 2 ^ (2 ^ j) := by
    calc 2 ^ 256 = 2 ^ (2 ^ 8) := by norm_num
      _ ≤ _ := two_pow_pow_mono hj
  omega

/-- For `j ≥ 8` each block has `Σ 1/(p - 1) ≤ 11/10`. -/
lemma blk_xsum_sharp (N j : ℕ) (hj : 8 ≤ j) : ∑ p ∈ blk N j, xDen p ≤ 11 / 10 := by
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
  have hl2 := Real.log_two_gt_d9
  have hly : (177 : ℝ) ≤ Real.log y := by
    rw [hy, log_two_pow_pow]
    have : (256 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
      have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      exact_mod_cast this
    nlinarith
  have hlpos : 0 < Real.log y := by linarith
  have hsq : Real.log ((y ^ 2 : ℕ) : ℝ) = 2 * Real.log y := by
    push_cast; rw [Real.log_pow]; norm_num
  rw [hsq] at hM
  have hM2 : (2 * Real.log y - Real.log y + 14) / Real.log y ≤ 191 / 177 := by
    rw [div_le_iff₀ hlpos]; nlinarith
  calc ∑ p ∈ blk N j, xDen p ≤ ∑ p ∈ blk N j, 101 / 100 * (1 / (p : ℝ)) :=
        sum_le_sum (fun p hp => xDen_le_sharp p (by have := blk_big N j p hj hp; omega))
    _ = 101 / 100 * ∑ p ∈ blk N j, (1 / (p : ℝ)) := by rw [mul_sum]
    _ ≤ 101 / 100 * ∑ p ∈ (Ioc y (y ^ 2)).filter Nat.Prime, (1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 11 / 10 := by nlinarith

/-- For `j ≥ 8` each block has `V_B ≥ e^{-6/5}`. -/
lemma blk_V_sharp (N j : ℕ) (hj : 8 ≤ j) :
    Real.exp (-(6 / 5)) ≤ ∏ p ∈ blk N j, (1 - xDen p) := by
  have h0 : ∀ p ∈ blk N j, 0 ≤ xDen p := fun p _ => xDen_nonneg p
  have h1 : ∀ p ∈ blk N j, xDen p ≤ 1 / 100 := by
    intro p hp
    have hb := blk_big N j p hj hp
    have h3 : (101 : ℝ) ≤ p := by exact_mod_cast (show 101 ≤ p by omega)
    unfold xDen
    rw [if_pos (by omega), div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine le_trans ?_ (LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp _ _ h0
    (fun p hp => (h1 p hp).trans (by norm_num)))
  apply Real.exp_le_exp.mpr
  have hsq : ∑ p ∈ blk N j, xDen p ^ 2 ≤ ∑ p ∈ blk N j, xDen p / 100 := by
    apply sum_le_sum; intro p hp; nlinarith [h0 p hp, h1 p hp]
  rw [← sum_div] at hsq
  have := blk_xsum_sharp N j hj
  linarith

/-- The block ratio bound at level `L` for the large blocks. -/
noncomputable def fR (L : ℕ) : ℝ := Real.exp (6 / 5) * (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial

lemma fR_nonneg (L : ℕ) : 0 ≤ fR L := by unfold fR; positivity

lemma fR_step (L : ℕ) : 2 * fR (L + 2) ≤ fR L := by
  unfold fR
  have hf : ((L + 2 + 1).factorial : ℝ) = (L + 3) * (L + 2) * (L + 1).factorial := by
    rw [show L + 2 + 1 = (L + 1 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf]
  have hF : (0 : ℝ) < (L + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have he := Real.exp_pos (6 / 5 : ℝ)
  have hp : (0 : ℝ) < (11 / 10 : ℝ) ^ (L + 1) := by positivity
  rw [show L + 2 + 1 = (L + 1) + 2 by ring, pow_add]
  have e2 : 2 * (Real.exp (6 / 5) * ((11 / 10 : ℝ) ^ (L + 1) * (11 / 10) ^ 2) /
      ((L + 3) * (L + 2) * (L + 1).factorial)) =
      (2 * (Real.exp (6 / 5) * ((11 / 10 : ℝ) ^ (L + 1) * (11 / 10) ^ 2))) /
      ((L + 3) * (L + 2) * (L + 1).factorial) := by ring
  rw [e2, div_le_div_iff₀ (by positivity) hF]
  have h6 : (6 : ℝ) ≤ (L + 3) * (L + 2) := by nlinarith
  have hpos : 0 < Real.exp (6 / 5) * (11 / 10 : ℝ) ^ (L + 1) * (L + 1).factorial := by positivity
  nlinarith

/-- **`ρ ≤ fR L`** for a block with `j ≥ 8` at levels `L, L + 1`. -/
lemma rho_blk_sharp (N j L : ℕ) (hj : 8 ≤ j) : rho xDen (blk N j, L, L + 1) ≤ fR L := by
  set u := ∑ p ∈ blk N j, xDen p with hu
  have hu0 : 0 ≤ u := sum_nonneg (fun p _ => xDen_nonneg p)
  have hu1 : u ≤ 11 / 10 := blk_xsum_sharp N j hj
  have hF : (0 : ℝ) < (L + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpow : u ^ (L + 1) ≤ (11 / 10 : ℝ) ^ (L + 1) := pow_le_pow_left₀ hu0 hu1 _
  have hT1 : truncErr (blk N j) xDen L ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := by
    unfold truncErr; rw [← hu]
    exact div_le_div_of_nonneg_right hpow hF.le
  have hT2 : truncErr (blk N j) xDen (L + 1) ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := by
    unfold truncErr; rw [← hu]
    have hf : ((L + 1 + 1).factorial : ℝ) = (L + 2) * (L + 1).factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf, pow_succ]
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    rw [div_le_div_iff₀ (by positivity) hF]
    have hp0 : 0 ≤ u ^ (L + 1) := by positivity
    have : u ^ (L + 1) * u ≤ u ^ (L + 1) * (L + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    nlinarith [mul_le_mul_of_nonneg_right hpow hF.le]
  have hV := blk_V_sharp N j hj
  have hVpos : 0 < ∏ p ∈ blk N j, (1 - xDen p) := lt_of_lt_of_le (Real.exp_pos _) hV
  unfold rho
  simp only
  rw [div_le_iff₀ hVpos]
  have hfR : fR L = (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial / Real.exp (-(6 / 5)) := by
    unfold fR; rw [Real.exp_neg]; field_simp
  rw [hfR]
  have hq : 0 ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := by positivity
  calc max (truncErr (blk N j) xDen L) (truncErr (blk N j) xDen (L + 1))
      ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial := max_le hT1 hT2
    _ = (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial / Real.exp (-(6 / 5)) *
          Real.exp (-(6 / 5)) := by field_simp
    _ ≤ (11 / 10 : ℝ) ^ (L + 1) / (L + 1).factorial / Real.exp (-(6 / 5)) *
          ∏ p ∈ blk N j, (1 - xDen p) :=
        mul_le_mul_of_nonneg_left hV (div_nonneg hq (Real.exp_pos _).le)

/-- **`Σ ρ ≤ 2 fR r + 2 e^{85 - (r + 2(j - 7))}`** over `G N j r` for `j ≥ 7`, once the eight small
blocks sit at level at least 1000. -/
lemma G_rho_sharp (N : ℕ) : ∀ j, 7 ≤ j → ∀ r, 1000 ≤ r + 2 * (j - 7) →
    rhoSum xDen (G N j r) ≤ 2 * fR r + 2 * Real.exp (85 - ((r + 2 * (j - 7) : ℕ) : ℝ)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro r hr
    simp only [Nat.sub_self, mul_zero, add_zero] at hr ⊢
    have := G_rho N 7 r hr
    have := fR_nonneg r
    linarith
  | succ j hj ih =>
    intro r hr
    simp only [G, rhoSum]
    have h1 := rho_blk_sharp N (j + 1) r (by omega)
    have h2 := ih (r + 2) (by omega)
    have e : r + 2 + 2 * (j - 7) = r + 2 * (j + 1 - 7) := by omega
    rw [e] at h2
    have h3 := fR_step r
    linarith

lemma exp_six_fifths_lt : Real.exp (6 / 5) < 34 / 10 := by
  have h1 : Real.exp (6 / 5) = Real.exp 1 * Real.exp (1 / 5) := by
    rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (1 / 5) ≤ 5 / 4 := by
    have := Real.add_one_le_exp (-(1 / 5) : ℝ)
    rw [Real.exp_neg] at this
    have hp := Real.exp_pos (1 / 5 : ℝ)
    rw [le_inv_comm₀ (by norm_num) hp] at this
    linarith
  have he := Real.exp_one_lt_d9
  have hp := Real.exp_pos (1 / 5 : ℝ)
  rw [h1]
  nlinarith [Real.exp_pos 1]

lemma fR_four : 2 * fR 4 + 2 * Real.exp (-915) ≤ 1 / 10 := by
  unfold fR
  have h := exp_six_fifths_lt
  have hf : ((4 + 1).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf]
  have he : Real.exp (-915) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by norm_num)
  have h3 : Real.exp (-3) ≤ 1 / 20 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
    have := Real.add_one_le_exp (3 : ℝ)
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have he1 := Real.exp_one_gt_d9
    rw [h2]
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
    norm_num at this ⊢; linarith
  have he0 := Real.exp_pos (-915 : ℝ)
  -- 2 · 3.4 · 1.61051 / 120 ≈ 0.09126; the e^{-915} term is far below 0.008
  have h5 : Real.exp (-915) ≤ 1 / 400 := by
    have : Real.exp (-915) ≤ Real.exp (-3) ^ 2 := by
      rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by norm_num)
    have := pow_le_pow_left₀ (Real.exp_pos (-3 : ℝ)).le h3 2
    norm_num at this; linarith
  norm_num
  nlinarith

/-- The size facts used below, kept apart so that no tactic meets the literal `2 ^ 600`. -/
lemma big_aux (ℓ : ℝ) (h : (2 : ℝ) ^ 600 ≤ ℓ) :
    (10 : ℝ) ^ 6 ≤ ℓ ∧ 2 ^ 506 ≤ ⌊ℓ / (29 * Real.log 2)⌋₊ := by
  have h2p : (2 : ℝ) ^ 600 = 2 ^ 94 * 2 ^ 506 := by rw [← pow_add]
  have h94 : (2 : ℝ) ^ 20 ≤ 2 ^ 94 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h1p : (1 : ℝ) ≤ 2 ^ 506 := one_le_pow₀ (by norm_num)
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have hc : ((2 ^ 506 : ℕ) : ℝ) = (2 : ℝ) ^ 506 := by push_cast; rfl
  rw [h2p] at h
  rw [h20] at h94
  generalize (2 : ℝ) ^ 94 = C at *
  generalize (2 : ℝ) ^ 506 = A at *
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
/-- **Rényi with `K = 59`, deterministic core with the count.** -/
theorem renyi59_count {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, ¬ p ∣ N ∧ 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (goldbachSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hE : Even N) (hℓ6 : (2 : ℝ) ^ 600 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    10 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 59)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨h10, ht506⟩ := big_aux ℓ hℓ6
  clear hℓ6
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
  have hN8 : (8 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    have : (8 : ℝ) ≤ ℓ := by linarith
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- t and k
  set t := ⌊ℓ / (29 * Real.log 2)⌋₊ with ht
  have ht1 : ℓ / (29 * Real.log 2) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one (ℓ / (29 * Real.log 2)); rw [← ht] at this; linarith
  have ht2 : (t : ℝ) ≤ ℓ / (29 * Real.log 2) := Nat.floor_le (by positivity)
  have hbig : (100 : ℝ) ≤ ℓ / (29 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have htge : 2 ≤ t := by
    have : (2 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  set k := Nat.log 2 t with hk
  have hk1 : 1 ≤ k := Nat.log_pos (by norm_num) htge
  have hk506 : 506 ≤ k := Nat.le_log_of_pow_le (by norm_num) ht506
  clear ht506
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
  have hlogz_hi : Real.log z ≤ ℓ / 29 := by
    rw [hlogz]
    calc ((2 ^ k : ℕ) : ℝ) * Real.log 2 ≤ ℓ / (29 * Real.log 2) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (hkt'.trans ht2) hl2pos.le
      _ = ℓ / 29 := by field_simp
  have hlogz_lo : ℓ / 59 ≤ Real.log z := by
    rw [hlogz]
    have h1 : ℓ / (29 * Real.log 2) - 1 < 2 * ((2 ^ k : ℕ) : ℝ) := by linarith
    have h2 : ℓ / 29 - Real.log 2 < 2 * (((2 ^ k : ℕ) : ℝ) * Real.log 2) := by
      have := mul_lt_mul_of_pos_right h1 hl2pos
      have e : (ℓ / (29 * Real.log 2) - 1) * Real.log 2 = ℓ / 29 - Real.log 2 := by
        field_simp
      linarith
    nlinarith
  have hlogz_pos : 0 < Real.log z := by linarith
  have hz4 : 4 ≤ z := by
    rw [hz]
    calc 4 = 2 ^ (2 ^ 1) := by norm_num
      _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk1)
  -- the blocks
  set Bs := G N j 4 with hBs
  have hG : Good Bs := G_good N j 4 ⟨2, rfl⟩
  have hmem := G_mem N j 4
  rw [hjk] at hmem
  have hcov := G_cover N j 4
  rw [hjk] at hcov
  have hlen : Bs.length = k := by rw [hBs, G_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply (G_lev N j 4).trans
    rw [hjk]
    apply Nat.le_floor
    have hexp : ((2 ^ (2 ^ k * (2 * 4 + 6)) : ℕ) : ℝ) ≤ Real.exp (49 / 100 * ℓ) := by
      have e : ((2 ^ (2 ^ k * (2 * 4 + 6)) : ℕ) : ℝ) = Real.exp (14 * Real.log z) := by
        rw [hlogz, two_pow_cast]
        push_cast; ring_nf
      rw [e]; apply Real.exp_le_exp.mpr; linarith
    linarith
  have hρ : rhoSum xDen Bs ≤ 1 / 10 := by
    refine (G_rho_sharp N j (by omega) 4 (by omega)).trans ?_
    have hlv : (1000 : ℝ) ≤ ((4 + 2 * (j - 7) : ℕ) : ℝ) := by
      have : 1000 ≤ 4 + 2 * (j - 7) := by omega
      exact_mod_cast this
    have h0 : Real.exp (85 - ((4 + 2 * (j - 7) : ℕ) : ℝ)) ≤ Real.exp (-915) :=
      Real.exp_le_exp.mpr (by linarith)
    have := fR_four
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
  have hV2 : Real.exp (-36) * 29 / ℓ ≤ ∏ p ∈ univB Bs, (1 - xDen p) := by
    refine le_trans ?_ hV
    rw [div_le_div_iff₀ hℓpos hlogz_pos]
    have := Real.exp_pos (-36 : ℝ)
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hmain : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 29 / ℓ) * (1 / 2) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 29 / ℓ) * (1 / 2) =
      (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
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
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 59) with hGd
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
    have hΩr : (ArithmeticFunction.cardFactors (N - p) : ℝ) ≤ 59 := by
      have h1 : (ArithmeticFunction.cardFactors (N - p) : ℝ) * (ℓ / 59) ≤ ℓ :=
        (mul_le_mul_of_nonneg_left hlogz_lo (Nat.cast_nonneg _)).trans hlogpow
      have h2 : (ArithmeticFunction.cardFactors (N - p) : ℝ) * (ℓ / 59) =
          (ArithmeticFunction.cardFactors (N - p) : ℝ) * ℓ / 59 := by ring
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
  have hfin : (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 - |K| * N / ℓ ^ (3 : ℝ) ≤
      (Surv.card : ℝ) := by rw [← hcardS]; linarith
  have hgoal : 10 * Real.exp (-36) * N / ℓ ^ 2 ≤
      (29 / 2) * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 -
        (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := Real.exp_pos (-37 : ℝ); have e2 := Real.exp_pos (-36 : ℝ)
    nlinarith [mul_nonneg e2.le (show (0 : ℝ) ≤ (N : ℝ) - 8 by linarith),
      mul_nonneg e1.le (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  linarith only [hgoal, hfin, hc3, hE3, hzle]


open Filter in
/-- Bombieri-Vinogradov's level `√x/(log x)^B` exceeds `x^{49/100}` for large `x`. -/
lemma renyi_large49 (B : ℝ) : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    Real.exp (49 / 100 * Real.log x) ≤ Real.sqrt x / Real.log x ^ B := by
  have hb := (isLittleO_log_rpow_rpow_atTop B (show (0 : ℝ) < 1 / 100 by norm_num)).bound one_pos
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hb.and (eventually_gt_atTop (1 : ℝ)))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨h, hx1⟩ := hX x hx
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hlB : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hl B
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlB,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul] at h
  have he : Real.exp (49 / 100 * Real.log x) = x ^ (49 / 100 : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
  rw [le_div_iff₀ hlB, he, Real.sqrt_eq_rpow]
  calc x ^ (49 / 100 : ℝ) * Real.log x ^ B ≤ x ^ (49 / 100 : ℝ) * x ^ (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add (by linarith)]; norm_num

open Filter in
/-- **Rényi's theorem with the count and `K = 59`, PROVED unconditional**: for every large even
`N`, `#{p < N prime : Ω(N - p) ≤ 59} ≥ 10 e^{-36} N/log² N`. Ineffective, through Siegel-Walfisz. -/
theorem renyi59_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    10 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 59)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_blocks_rel 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 600)))
  refine ⟨⌈max (max X X₂) Y⌉₊, fun N hN hE => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact renyi59_count hK N hE (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's theorem with `K = 59`, PROVED unconditional.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 59`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN; Chen 1973 has `Ω(m) ≤ 2` by a far stronger sieve. -/
theorem renyi59_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 59 := by
  obtain ⟨N₀, hN₀⟩ := renyi59_fixedK_count
  refine ⟨max N₀ 4, fun N hN hE => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) hE
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < 10 * Real.exp (-36) * N / Real.log N ^ 2 := by positivity
  have hc : 0 < (((range N).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 59)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨p, hp⟩ := card_pos.mp hc
  simp only [mem_filter, mem_range] at hp
  obtain ⟨⟨hpN, hpp⟩, hΩ⟩ := hp
  exact ⟨p, N - p, hpp, by omega, by omega, hΩ⟩

end LeanLab.PNTPort.BVMax

