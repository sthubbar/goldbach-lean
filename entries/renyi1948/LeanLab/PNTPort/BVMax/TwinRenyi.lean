module

public import LeanLab.PNTPort.BVMax.RenyiFixedK

/-!
# Rényi's twin theorem: infinitely many primes `p` with `Ω(p + 2) ≤ 13000`

Unit U-5516, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics, Rényi 1948,
the twin companion of `renyi_fixedK`: the same block sieve on `A = {p + 2 : p ≤ x}`, whose
remainders are the Bombieri-Vinogradov errors at the class `-2 mod d`.

* `card_dvd_twinSeq`: `#{m ∈ A : d ∣ m} = π(x; d, d - 2)` for `d = 1` or odd `d ≥ 3`;
* `twin_rem_family`: the Bombieri-Vinogradov bound for the block remainders of `A`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset

/-- `A = {p + 2 : p ≤ x prime}`. -/
def twinSeq (N : ℕ) : Finset ℕ := ((Icc 1 N).filter Nat.Prime).image (fun p => p + 2)

/-- The residue `-2 mod d` for odd `d ≥ 3`, and `1` otherwise. -/
def twinRes (d : ℕ) : ℕ := if Odd d ∧ 3 ≤ d then d - 2 else 1

lemma twinRes_coprime (d : ℕ) : Nat.Coprime (twinRes d) d := by
  unfold twinRes
  split_ifs with h
  · obtain ⟨hodd, h3⟩ := h
    have e : d = (d - 2) + 2 := by omega
    conv_rhs => rw [e]
    rw [Nat.coprime_self_add_right, Nat.coprime_two_right]
    rcases hodd with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  · exact Nat.coprime_one_left d

lemma mod_twinRes_iff (d n : ℕ) (hd : d = 1 ∨ (Odd d ∧ 3 ≤ d)) :
    n % d = twinRes d % d ↔ d ∣ n + 2 := by
  rcases hd with rfl | ⟨hodd, h3⟩
  · simp [Nat.mod_one]
  · unfold twinRes
    rw [if_pos ⟨hodd, h3⟩]
    constructor
    · intro h
      have h1 : n ≡ d - 2 [MOD d] := h
      have h2 := h1.add_right 2
      rw [show d - 2 + 2 = d by omega] at h2
      exact (Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)))
    · intro h
      have h1 : n + 2 ≡ d - 2 + 2 [MOD d] := by
        rw [show d - 2 + 2 = d by omega]
        exact (Nat.modEq_zero_iff_dvd.mpr h).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
      exact Nat.ModEq.add_right_cancel' 2 h1

theorem card_dvd_twinSeq (N d : ℕ) (hd : d = 1 ∨ (Odd d ∧ 3 ≤ d)) :
    (((twinSeq N).filter (fun m => d ∣ m)).card : ℝ) = piN N d (twinRes d) := by
  unfold twinSeq piN
  rw [filter_image, card_image_of_injOn]
  · congr 2
    ext p
    simp only [mem_filter, mem_Icc]
    rw [mod_twinRes_iff d p hd]
    tauto
  · intro a _ b _ he
    simp only at he
    omega

lemma prod_odd_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ 3 ≤ p) :
    (∏ p ∈ T, p) = 1 ∨ (Odd (∏ p ∈ T, p) ∧ 3 ≤ ∏ p ∈ T, p) := by
  rcases T.eq_empty_or_nonempty with h | ⟨q, hq⟩
  · left; rw [h, prod_empty]
  · right
    refine ⟨?_, ?_⟩
    · apply Nat.not_even_iff_odd.mp
      intro he
      obtain ⟨p, hp, h2p⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).mp (even_iff_two_dvd.mp he)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hT p hp).1).mp h2p
      have := (hT p hp).2
      omega
    · have h1 : q ≤ ∏ p ∈ T, p :=
        Nat.le_of_dvd (prod_pos (fun p hp => (hT p hp).1.pos)) (dvd_prod_of_mem _ hq)
      have := (hT q hq).2
      omega

/-- **Bombieri-Vinogradov for the twin remainders.** -/
theorem twin_rem_family (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
    F ⊆ P.powerset →
    (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
    ∑ T ∈ F, |LeanLab.PNTSieve.Bonferroni.rem (twinSeq N) xDen (liD (N : ℝ)) T| ≤
        K * N / Real.log N ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun N hN P hP F hF hTQ => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set y : ℝ := (N : ℝ) with hy
  have hbv := hK N hN2 twinRes twinRes_coprime (fun _ => y) (fun _ => ⟨Nat.cast_nonneg _, le_rfl⟩)
  set E : ℕ → ℝ := fun d => |piAP y d (twinRes d) - liD y / d.totient| with hE
  have hrem : ∀ T ∈ F,
      |LeanLab.PNTSieve.Bonferroni.rem (twinSeq N) xDen (liD y) T| = E (∏ p ∈ T, p) := by
    intro T hT
    have hTP : T ⊆ P := mem_powerset.mp (hF hT)
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => (hP p (hTP hp)).1
    have hx : ∏ p ∈ T, xDen p = 1 / ((∏ p ∈ T, p).totient : ℝ) := by
      rw [inv_totient_prod_primes T hTp]
      refine prod_congr rfl (fun p hp => ?_)
      simp only [xDen, if_pos (hP p (hTP hp)).2]
    have hpi : piAP y (∏ p ∈ T, p) (twinRes (∏ p ∈ T, p)) =
        piN N (∏ p ∈ T, p) (twinRes (∏ p ∈ T, p)) := by
      unfold piAP; rw [hy, Nat.floor_natCast]
    unfold LeanLab.PNTSieve.Bonferroni.rem LeanLab.PNTSieve.Bonferroni.cnt
    rw [card_dvd_twinSeq N _ (prod_odd_primes T (fun p hp => hP p (hTP hp))), hx, hE]
    simp only
    rw [hpi, mul_one_div]
  rw [sum_congr rfl hrem]
  have hinj : ∀ T₁ ∈ F, ∀ T₂ ∈ F, ∏ p ∈ T₁, p = ∏ p ∈ T₂, p → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ he
    have h₁ : T₁ ⊆ P := mem_powerset.mp (hF h₁)
    have h₂ : T₂ ⊆ P := mem_powerset.mp (hF h₂)
    rw [← Nat.primeFactors_prod (fun p hp => (hP p (h₁ hp)).1),
      ← Nat.primeFactors_prod (fun p hp => (hP p (h₂ hp)).1), he]
  rw [← sum_image hinj]
  refine le_trans ?_ hbv
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
  intro d hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
  rw [mem_Icc]
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, hTQ T hT⟩
  have hTP : T ⊆ P := mem_powerset.mp (hF hT)
  exact prod_ne_zero_iff.mpr (fun p hp => (hP p (hTP hp)).1.ne_zero)

open LeanLab.PNTSieve.Bonferroni in
/-- **Brun's block sieve on `{p + 2}`, relative form.** -/
theorem twin_blocks_rel (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, 3 ≤ p) →
    lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
    liD (N : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
      3 ^ Bs.length * (K * N / Real.log N ^ A) ≤ (sifted (twinSeq N) (univB Bs) : ℝ) := by
  obtain ⟨B, hB, K, hK⟩ := twin_rem_family A hA
  refine ⟨B, hB, K, fun N hN Bs hG hBs hlev hρ => ?_⟩
  have hX : 0 ≤ liD (N : ℝ) := by
    unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have h1 := blocks_main_rel (twinSeq N) Bs hG xDen xDen_nonneg xDen_lt_one _ hX hρ
  have hP : ∀ p ∈ univB Bs, p.Prime ∧ 3 ≤ p := fun p hp => ⟨univB_prime Bs hG p hp, hBs p hp⟩
  have h2 := hK N hN (univB Bs) hP ((univB Bs).powerset.filter (fun S => cL Bs S ≠ 0))
    (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      exact (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans hlev)
  have h3 : (0 : ℝ) ≤ 3 ^ Bs.length := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

open LeanLab.PNTSieve.Bonferroni

set_option maxHeartbeats 1000000 in
/-- Twin Rényi with the count, deterministic core. -/
theorem twinK_count {B K : ℝ}
    (hK : ∀ N : ℕ, 2 ≤ N →
      ∀ Bs : List Block, Good Bs → (∀ p ∈ univB Bs, 3 ≤ p) →
      lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ → rhoSum xDen Bs ≤ 1 / 10 →
      liD (N : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) -
        3 ^ Bs.length * (K * N / Real.log N ^ (5 : ℝ)) ≤ (sifted (twinSeq N) (univB Bs) : ℝ))
    (N : ℕ) (hℓ6 : 10 ^ 6 ≤ Real.log N)
    (hE2 : Real.exp (Real.log N / 3) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    1000 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((Icc 1 N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 13000)).card : ℝ) := by
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
  have hN6 : (6 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
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
  set Bs := G 1 j 1000 with hBs
  have hG : Good Bs := G_good 1 j 1000 ⟨500, rfl⟩
  have hmem := G_mem 1 j 1000
  rw [hjk] at hmem
  have hcov := G_cover 1 j 1000
  rw [hjk] at hcov
  have hlen : Bs.length = k := by rw [hBs, G_length, hjk]
  have hlev : lev Bs ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
    apply (G_lev 1 j 1000).trans
    rw [hjk]
    apply Nat.le_floor
    have hexp : ((2 ^ (2 ^ k * (2 * 1000 + 6)) : ℕ) : ℝ) ≤ Real.exp (ℓ / 3) := by
      have e : ((2 ^ (2 ^ k * (2 * 1000 + 6)) : ℕ) : ℝ) = Real.exp (2006 * Real.log z) := by
        rw [hlogz, two_pow_cast]
        push_cast; ring_nf
      rw [e]; apply Real.exp_le_exp.mpr; linarith
    linarith
  have hρ : rhoSum xDen Bs ≤ 1 / 10 := by
    refine (G_rho 1 j 1000 le_rfl).trans ?_
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
  have hS := hK N (by omega) Bs hG (fun p hp => (hmem p hp).2.2.2) hlev hρ
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
  have hliD : ((N : ℝ) - 2) / (2 * ℓ) ≤ liD (N : ℝ) := by
    have h := liD_ge (N + 1) (by omega)
    rw [show N + 1 - 1 = N by omega] at h
    push_cast at h
    refine le_trans ?_ h
    have hl1 : Real.log ((N : ℝ) + 1) ≤ 2 * ℓ := by
      rw [hℓ, ← Real.log_rpow hNpos, show ((N : ℝ) ^ (2 : ℝ)) = (N : ℝ) * N by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have hl0 : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    rw [div_le_div_iff₀ (by positivity) hl0]
    nlinarith
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / (2 * ℓ) := div_nonneg (by linarith) (by positivity)
  have hmain : ((N : ℝ) - 2) / (2 * ℓ) * (Real.exp (-36) * 6018 / ℓ) * (1 / 2) ≤
      liD (N : ℝ) * (∏ p ∈ univB Bs, (1 - xDen p)) * (1 - 5 * rhoSum xDen Bs) := by
    apply mul_le_mul (mul_le_mul hliD hV2 (by positivity) (hliD0.trans hliD)) (by linarith)
      (by norm_num)
    exact mul_nonneg (hliD0.trans hliD) (le_trans (by positivity) hV2)
  have hmain2 : ((N : ℝ) - 2) / (2 * ℓ) * (Real.exp (-36) * 6018 / ℓ) * (1 / 2) =
      1504.5 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    field_simp; ring
  have hc : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      1504.5 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 := by
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
  have hSbig : (z : ℝ) + 2 ≤ (sifted (twinSeq N) (univB Bs) : ℝ) := by linarith
  set Surv := (twinSeq N).filter (fun a => ∀ p ∈ univB Bs, ¬ p ∣ a) with hSurv
  have hcardS : (sifted (twinSeq N) (univB Bs) : ℝ) = (Surv.card : ℝ) := by
    simp [sifted, hSurv]
  set small := (range (z + 1)).image (fun p => p + 2) with hsmall_def
  have hsmall : small.card ≤ z + 1 := card_image_le.trans (by simp)
  set Gd := ((Icc 1 N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 13000) with hGd
  have hsub : Surv \ small ⊆ Gd.image (fun p => p + 2) := by
    intro m hm
    rw [mem_sdiff] at hm
    obtain ⟨hmS, hmn⟩ := hm
    rw [hSurv, mem_filter] at hmS
    obtain ⟨hmG, hmP⟩ := hmS
    unfold twinSeq at hmG
    rw [mem_image] at hmG
    obtain ⟨p, hp, rfl⟩ := hmG
    rw [mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hpp⟩ := hp
    have hpz : z < p := by
      by_contra h
      push Not at h
      exact hmn (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
    have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hmodd : Odd (p + 2) := by
      rcases hpodd with ⟨b, hb⟩
      exact ⟨b + 1, by omega⟩
    have hm0 : p + 2 ≠ 0 := by omega
    have hfac_big : ∀ q ∈ (p + 2).primeFactorsList, z ≤ q := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      by_contra hlt
      push Not at hlt
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hqd)
      have hq3 : 3 ≤ q := by have := hqp.two_le; omega
      have hq1 : ¬ q ∣ 1 := fun h => hqp.one_lt.ne' (Nat.dvd_one.mp h)
      exact hmP q (hcov q hqp hq1 hq3 hlt.le) hqd
    have hpow := pow_bigOmega_le (p + 2) z hm0 hfac_big
    have hpowr : (z : ℝ) ^ (ArithmeticFunction.cardFactors (p + 2)) ≤ (N : ℝ) * Real.exp 1 := by
      have h1 : z ^ (ArithmeticFunction.cardFactors (p + 2)) ≤ N + 2 := hpow.trans (by omega)
      have h2 : ((z ^ (ArithmeticFunction.cardFactors (p + 2)) : ℕ) : ℝ) ≤ (N : ℝ) + 2 := by
        exact_mod_cast h1
      have he := Real.add_one_le_exp (1 : ℝ)
      push_cast at h2
      nlinarith
    have hlogpow : (ArithmeticFunction.cardFactors (p + 2) : ℝ) * Real.log z ≤ ℓ + 1 := by
      have := Real.log_le_log (by positivity) hpowr
      rwa [Real.log_pow, Real.log_mul hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    have hΩr : (ArithmeticFunction.cardFactors (p + 2) : ℝ) < 13001 := by
      have h1 : (ArithmeticFunction.cardFactors (p + 2) : ℝ) * (ℓ / 13000) ≤ ℓ + 1 :=
        (mul_le_mul_of_nonneg_left hlogz_lo (Nat.cast_nonneg _)).trans hlogpow
      have h2 : (ArithmeticFunction.cardFactors (p + 2) : ℝ) * (ℓ / 13000) =
          (ArithmeticFunction.cardFactors (p + 2) : ℝ) * ℓ / 13000 := by ring
      rw [h2, div_le_iff₀ (by norm_num)] at h1
      by_contra hc
      push Not at hc
      nlinarith
    have hΩn : ArithmeticFunction.cardFactors (p + 2) < 13001 := by exact_mod_cast hΩr
    refine mem_image.mpr ⟨p, ?_, rfl⟩
    rw [hGd, mem_filter, mem_filter, mem_Icc]
    exact ⟨⟨⟨hp1, hpN⟩, hpp⟩, by omega⟩
  have hc1 : Surv.card ≤ (Surv \ small).card + small.card := card_le_card_sdiff_add_card
  have hc2 : (Surv \ small).card ≤ Gd.card := (card_le_card hsub).trans card_image_le
  have hc3 : (Surv.card : ℝ) ≤ (Gd.card : ℝ) + (z : ℝ) + 1 := by
    have : Surv.card ≤ Gd.card + (z + 1) := by omega
    exact_mod_cast this
  -- the count
  have hfin : 1504.5 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 - |K| * N / ℓ ^ (3 : ℝ) ≤
      (Surv.card : ℝ) := by rw [← hcardS]; linarith
  have hgoal : 1000 * Real.exp (-36) * N / ℓ ^ 2 ≤
      1504.5 * Real.exp (-36) * ((N : ℝ) - 2) / ℓ ^ 2 -
        (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := Real.exp_pos (-37 : ℝ); have e2 := Real.exp_pos (-36 : ℝ)
    nlinarith [mul_nonneg e2.le (show (0 : ℝ) ≤ (N : ℝ) - 6 by linarith),
      mul_nonneg e1.le (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  linarith only [hgoal, hfin, hc3, hE3, hzle]

open Filter in
/-- **Rényi's twin theorem with the count, PROVED unconditional**: for every large `N`,
`#{p ≤ N prime : Ω(p + 2) ≤ 13000} ≥ 1000 e^{-36} N/log² N`. The twin prime conjecture is
`Ω(p + 2) = 1` and stays OPEN; Chen 1973 has `Ω(p + 2) ≤ 2`. -/
theorem twin_renyi_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    1000 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((Icc 1 N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 13000)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := twin_blocks_rel 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B |K|
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10 ^ 6 : ℝ)))
  refine ⟨⌈max X Y⌉₊, fun N hN => ?_⟩
  have hx : max X Y ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨_, _, h2, h3⟩ := hX N ((le_max_left _ _).trans hx)
  exact twinK_count hK N (hY N ((le_max_right _ _).trans hx)) h2 h3

end LeanLab.PNTPort.BVMax

