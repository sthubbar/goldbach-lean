module

public import LeanLab.BhowmikGrimmelt2026.FareyCount451
public import LeanLab.BhowmikGrimmelt2026.ArcTails150
public import LeanLab.BhowmikGrimmelt2026.MajorArcPair
public import LeanLab.BhowmikGrimmelt2026.Decomp443a
public import LeanLab.BhowmikGrimmelt2026.InducedFormula443
public import LeanLab.PNTPort.Vinogradov.Basic

/-!
Separated inverse square kernels for the arc tails of P0029 page 12.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open Set Metric Filter

/-- P0029 page 12. Split a separated inverse square sum at zero. -/
theorem sum_inv_sq_abs504 {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ i ∈ s, δ ≤ |f i|)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |f i - f j|) :
    ∑ i ∈ s, 1 / (f i) ^ 2 ≤ 4 / δ ^ 2 := by
  classical
  have hp := LeanLab.PNTPort.LargeSieve.sum_inv_sq_sep
    (s.filter (fun i => 0 ≤ f i)) f hδ
    (fun i hi => by
      obtain ⟨hi, hf⟩ := Finset.mem_filter.mp hi
      simpa only [abs_of_nonneg hf] using hpos i hi)
    (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j
      (Finset.mem_filter.mp hj).1 hij)
  have hn := LeanLab.PNTPort.LargeSieve.sum_inv_sq_sep
    (s.filter (fun i => ¬ 0 ≤ f i)) (fun i => -f i) hδ
    (fun i hi => by
      obtain ⟨hi, hf⟩ := Finset.mem_filter.mp hi
      simpa only [abs_of_neg (lt_of_not_ge hf)] using hpos i hi)
    (fun i hi j hj hij => by
      simpa only [neg_sub_neg, abs_sub_comm] using
        hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
  simp only [neg_sq] at hn
  have heq := Finset.sum_filter_add_sum_filter_not s (fun i => 0 ≤ f i)
    (fun i => 1 / (f i) ^ 2)
  calc
    _ = _ := heq.symm
    _ ≤ 2 / δ ^ 2 + 2 / δ ^ 2 := add_le_add hp hn
    _ = 4 / δ ^ 2 := by ring

/-- P0029 page 12. One denominator block has a quadratic inverse square budget.
The sum contains only fractions outside their Dirichlet widths. -/
theorem far_block_inv_sq504 {R Q : ℕ} (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (α : ℝ) (s : Finset (Σ _ : ℕ, ℕ))
    (hs : s ⊆ reducedPairs (2 * R))
    (hfar : ∀ p ∈ s, 1 < (Q : ℝ) * p.1 * intDist (α - p.2 / p.1)) :
    ∑ p ∈ s, 1 / intDist (α - p.2 / p.1) ^ 2 ≤
      64 * (R : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hQR : (R : ℝ) ≤ Q := by exact_mod_cast hRQ
  have hQp : (0 : ℝ) < Q := hRp.trans_le hQR
  have hδ : 0 < 1 / (4 * (R : ℝ) * Q) := by positivity
  have hb := sum_inv_sq_abs504 s (fun p => α - pairCenter451 α p) hδ
    (fun p hp => by
      rw [pairCenter_dist451]
      have hq := (mem_reducedPairs _ p).mp (hs hp)
      have hqR : (p.1 : ℝ) ≤ 2 * R := by exact_mod_cast hq.2.1
      have hd := intDist_nonneg (α - p.2 / p.1)
      have hf := hfar p hp
      apply (div_le_iff₀ (by positivity : 0 < 4 * (R : ℝ) * Q)).mpr
      have hh := mul_le_mul_of_nonneg_right hqR (mul_nonneg hQp.le hd)
      nlinarith only [hf, hh, mul_nonneg hQp.le hd])
    (fun p hp r hr hne => by
      have h := pairCenter_separated451 (α := α)
        (by positivity : (0 : ℝ) < (2 * R : ℕ))
        (le_refl ((2 * R : ℕ) : ℝ)) (hs hp) (hs hr) hne
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)] at h
      have hden : 0 < ((2 * R : ℕ) : ℝ) ^ 2 := by positivity
      have hh : 1 / ((2 * R : ℕ) : ℝ) ^ 2 ≤
          |pairCenter451 α p - pairCenter451 α r| :=
        (div_le_iff₀ hden).mpr (by nlinarith only [h])
      have hδle : 1 / (4 * (R : ℝ) * Q) ≤ 1 / ((2 * R : ℕ) : ℝ) ^ 2 := by
        apply one_div_le_one_div_of_le hden
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hQR hRp.le]
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hδle.trans hh)
  have heq : (∑ p ∈ s, 1 / (α - pairCenter451 α p) ^ 2) =
      ∑ p ∈ s, 1 / intDist (α - p.2 / p.1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [← pairCenter_dist451, sq_abs]
  rw [heq] at hb
  convert hb using 1 <;> field_simp <;> norm_num

/-- P0029 page 12. The totient divisor identity bounds the denominator ratio. -/
theorem le_totient_mul_divisors504 (n : ℕ) :
    n ≤ Nat.totient n * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc
    n = ∑ d ∈ n.divisors, Nat.totient d := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors, Nat.totient n := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hn)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = Nat.totient n * n.divisors.card := by simp [mul_comm]

/-- P0029 page 12. A uniform totient ratio bound costs only a reciprocal power. -/
theorem totient_ratio_subpower504 (k : ℕ) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ D * (n : ℝ) ^ (k : ℝ)⁻¹ * Nat.totient n := by
  obtain ⟨D, hD, hb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨D, hD, fun n hn => ?_⟩
  have ht : (n : ℝ) ≤ (Nat.totient n : ℝ) * n.divisors.card := by
    exact_mod_cast le_totient_mul_divisors504 n
  calc
    (n : ℝ) ≤ (Nat.totient n : ℝ) * n.divisors.card := ht
    _ ≤ (Nat.totient n : ℝ) * (D * (n : ℝ) ^ (k : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (hb n hn) (by positivity)
    _ = D * (n : ℝ) ^ (k : ℝ)⁻¹ * Nat.totient n := by ring

/-- P0029 page 12. Reciprocal totient weights cancel the block scale. -/
theorem far_block_weighted504 {R Q : ℕ} (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (α D : ℝ) (hD : 0 ≤ D) (s : Finset (Σ _ : ℕ, ℕ))
    (hs : s ⊆ reducedPairs (2 * R))
    (hlo : ∀ p ∈ s, R ≤ p.1)
    (hweight : ∀ p ∈ s, (p.1 : ℝ) ≤ D * Nat.totient p.1)
    (hfar : ∀ p ∈ s, 1 < (Q : ℝ) * p.1 * intDist (α - p.2 / p.1)) :
    ∑ p ∈ s, (1 / (Nat.totient p.1 : ℝ) ^ 2) *
      (1 / intDist (α - p.2 / p.1) ^ 2) ≤ 64 * D ^ 2 * (Q : ℝ) ^ 2 := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hpt (p) (hp : p ∈ s) : 1 / (Nat.totient p.1 : ℝ) ^ 2 ≤ D ^ 2 / (R : ℝ) ^ 2 := by
    have hφ : (0 : ℝ) < Nat.totient p.1 := by
      exact_mod_cast Nat.totient_pos.mpr ((hR.trans (hlo p hp)))
    have hRφ : (R : ℝ) ≤ D * Nat.totient p.1 :=
      (by exact_mod_cast hlo p hp : (R : ℝ) ≤ p.1).trans (hweight p hp)
    have hh := pow_le_pow_left₀ hRp.le hRφ 2
    rw [mul_pow] at hh
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using hh
  calc
    _ ≤ ∑ p ∈ s, (D ^ 2 / (R : ℝ) ^ 2) *
        (1 / intDist (α - p.2 / p.1) ^ 2) :=
      Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hpt p hp) (by positivity)
    _ = (D ^ 2 / (R : ℝ) ^ 2) * ∑ p ∈ s, 1 / intDist (α - p.2 / p.1) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (D ^ 2 / (R : ℝ) ^ 2) * (64 * (R : ℝ) ^ 2 * (Q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (far_block_inv_sq504 hR hRQ α s hs hfar) (by positivity)
    _ = 64 * D ^ 2 * (Q : ℝ) ^ 2 := by field_simp

/-- P0029 page 12. Sum the weighted inverse square budgets over dyadic denominator blocks. -/
theorem far_dyadic_sum504 {Q : ℕ} (hQ : 1 ≤ Q) (α D : ℝ) (hD : 0 ≤ D)
    (s : Finset (Σ _ : ℕ, ℕ)) (hs : s ⊆ reducedPairs Q)
    (hweight : ∀ p ∈ s, (p.1 : ℝ) ≤ D * Nat.totient p.1)
    (hfar : ∀ p ∈ s, 1 < (Q : ℝ) * p.1 * intDist (α - p.2 / p.1)) :
    ∑ p ∈ s, (1 / (Nat.totient p.1 : ℝ) ^ 2) *
      (1 / intDist (α - p.2 / p.1) ^ 2) ≤
        64 * D ^ 2 * (Q : ℝ) ^ 2 * (Nat.log 2 Q + 1) := by
  classical
  have hm : ∀ p ∈ s, Nat.log 2 p.1 ∈ Finset.range (Nat.log 2 Q + 1) := by
    intro p hp
    have hq := (mem_reducedPairs _ p).mp (hs hp)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hq.2.1))
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  calc
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 Q + 1), 64 * D ^ 2 * (Q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      let t := s.filter (fun p => Nat.log 2 p.1 = j)
      by_cases ht : t.Nonempty
      · obtain ⟨p, hp⟩ := ht
        obtain ⟨hp, hpj⟩ := Finset.mem_filter.mp hp
        have hpq := (mem_reducedPairs _ p).mp (hs hp)
        have hR : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by decide)
        have hRQ : 2 ^ j ≤ Q := by
          rw [← hpj]
          exact (Nat.pow_log_le_self 2 (by omega : p.1 ≠ 0)).trans hpq.2.1
        apply far_block_weighted504 hR hRQ α D hD t
        · intro r hr
          obtain ⟨hr, hrj⟩ := Finset.mem_filter.mp hr
          have hrq := (mem_reducedPairs _ r).mp (hs hr)
          apply (mem_reducedPairs _ r).mpr
          refine ⟨hrq.1, ?_, hrq.2.2⟩
          have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) r.1
          rw [hrj, pow_succ] at hh
          omega
        · intro r hr
          obtain ⟨hr, hrj⟩ := Finset.mem_filter.mp hr
          have hrq := (mem_reducedPairs _ r).mp (hs hr)
          rw [← hrj]
          exact Nat.pow_log_le_self 2 (by omega)
        · intro r hr
          exact hweight r (Finset.mem_filter.mp hr).1
        · intro r hr
          exact hfar r (Finset.mem_filter.mp hr).1
      · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
        change (∑ r ∈ t, _) ≤ _
        rw [ht0, Finset.sum_empty]
        positivity
    _ = _ := by simp; ring

/-- P0029 page 12. The number of dyadic blocks has an arbitrarily small power cost. -/
theorem dyadic_count_subpower504 {t : ℝ} (ht : 0 < t) {Q : ℕ} (hQ : 1 ≤ Q) :
    (Nat.log 2 Q + 1 : ℝ) ≤
      (1 + 1 / (t * Real.log 2)) * (Q : ℝ) ^ t := by
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := Real.natLog_le_logb Q 2
  have hr := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hQp t)
  rw [Real.log_rpow hQp] at hr
  have hpow : 1 ≤ (Q : ℝ) ^ t := Real.one_le_rpow hQ1 ht.le
  unfold Real.logb at hn
  have hn' := (le_div_iff₀ hlog).mp hn
  have hh : (Nat.log 2 Q : ℝ) ≤ (Q : ℝ) ^ t / (t * Real.log 2) := by
    apply (le_div_iff₀ (mul_pos ht hlog)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hn' ht.le, hr]
  calc
    (Nat.log 2 Q + 1 : ℝ) ≤ (Q : ℝ) ^ t / (t * Real.log 2) + (Q : ℝ) ^ t := by
      linarith
    _ = (1 + 1 / (t * Real.log 2)) * (Q : ℝ) ^ t := by ring

/-- P0029 page 12. The far rational inverse square kernel has a subpower weighted budget. -/
theorem far_weighted_subpower504 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ α : ℝ,
      ∀ s : Finset (Σ _ : ℕ, ℕ), s ⊆ reducedPairs Q →
      (∀ p ∈ s, 1 < (Q : ℝ) * p.1 * intDist (α - p.2 / p.1)) →
      ∑ p ∈ s, (1 / (Nat.totient p.1 : ℝ) ^ 2) *
        (1 / intDist (α - p.2 / p.1) ^ 2) ≤ C * (Q : ℝ) ^ (2 + ε) := by
  intro ε hε
  let k : ℕ := ⌈4 / ε⌉₊ + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hsmall : 2 * (k : ℝ)⁻¹ ≤ ε / 2 := by
    have hh := Nat.le_ceil (4 / ε)
    have hkbig : 4 / ε < (k : ℝ) := by dsimp [k]; push_cast; linarith
    have hh' := (div_lt_iff₀ hε).mp hkbig
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hkp]
    nlinarith only [hh']
  obtain ⟨D, hD, hDb⟩ := totient_ratio_subpower504 k hk
  let B := 1 + 1 / ((ε / 2) * Real.log 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨64 * D ^ 2 * B, by positivity, fun Q hQ α s hs hfar => ?_⟩
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hweight : ∀ p ∈ s, (p.1 : ℝ) ≤
      (D * (Q : ℝ) ^ (k : ℝ)⁻¹) * Nat.totient p.1 := by
    intro p hp
    have hq := (mem_reducedPairs _ p).mp (hs hp)
    refine (hDb p.1 hq.1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hq.2.1) (by positivity)
  have hb := far_dyadic_sum504 hQ α (D * (Q : ℝ) ^ (k : ℝ)⁻¹)
    (by positivity) s hs hweight hfar
  have hc := dyadic_count_subpower504 (by linarith : 0 < ε / 2) hQ
  have heq : 64 * (D * (Q : ℝ) ^ (k : ℝ)⁻¹) ^ 2 * (Q : ℝ) ^ 2 *
      (B * (Q : ℝ) ^ (ε / 2)) =
      (64 * D ^ 2 * B) * (Q : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹ + ε / 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hQp.le, ← Real.rpow_natCast,
      Real.rpow_add hQp, Real.rpow_add hQp]
    push_cast
    simp only [Real.rpow_two]
    ring_nf
  calc
    _ ≤ 64 * (D * (Q : ℝ) ^ (k : ℝ)⁻¹) ^ 2 * (Q : ℝ) ^ 2 *
        (B * (Q : ℝ) ^ (ε / 2)) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (64 * D ^ 2 * B) * (Q : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹ + ε / 2) := heq
    _ ≤ (64 * D ^ 2 * B) * (Q : ℝ) ^ (2 + ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)

/-- P0029 pages 11 and 12. Minimal assigned denominators force a coprime numerator. -/
theorem assigned_coprime504 {X q : ℕ} (hq : 1 ≤ q) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (ha : α ∈ arcSet150 X q) :
    Nat.Coprime (nint150 ((q : ℝ) * α)).toNat q := by
  let a := (nint150 ((q : ℝ) * α)).toNat
  have ha0 := (nint_mem150 (q := q) hα).1
  have hac : (a : ℤ) = nint150 ((q : ℝ) * α) := Int.toNat_of_nonneg ha0
  have hacR : (a : ℝ) = (nint150 ((q : ℝ) * α) : ℝ) := by exact_mod_cast hac
  change Nat.gcd a q = 1
  by_contra hbad
  let d := Nat.gcd a q
  have hd : 1 ≤ d := Nat.gcd_pos_of_pos_right a hq
  have hd2 : 1 < d := by omega
  have hdq : d ∣ q := Nat.gcd_dvd_right a q
  have hda : d ∣ a := Nat.gcd_dvd_left a q
  have hk : 1 ≤ q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  have hkq : q / d < q := Nat.div_lt_self hq hd2
  have hqc : (d : ℝ) * (q / d : ℕ) = q := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  have hac' : (d : ℝ) * (a / d : ℕ) = a := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hda]
  have heq : (d : ℝ) * ((q / d : ℕ) * α - (a / d : ℕ)) = (q : ℝ) * α - a := by
    calc
      _ = ((d : ℝ) * (q / d : ℕ)) * α - (d : ℝ) * (a / d : ℕ) := by ring
      _ = _ := by rw [hqc, hac']
  have hscale : |(q / d : ℕ) * α - (a / d : ℕ)| ≤ |(q : ℝ) * α - a| := by
    have habs := congrArg abs heq
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)] at habs
    rw [← habs]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith only [mul_le_mul_of_nonneg_right hdR (abs_nonneg
      ((q / d : ℕ) * α - (a / d : ℕ)))]
  have hround := round_le ((q / d : ℕ) * α : ℝ) (a / d : ℕ)
  have hnear : |(q / d : ℕ) * α - (nint150 ((q / d : ℕ) * α) : ℝ)| ≤
      1 / (Nat.sqrt X : ℝ) := by
    unfold nint150
    rw [← round_eq]
    refine hround.trans (hscale.trans ?_)
    rw [hacR]
    exact ha.1
  have ham := ha
  simp only [arcSet150, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at ham
  have hex := ham.2 (q / d) (Finset.mem_Ico.mpr ⟨hk, hkq⟩)
  exact (not_lt_of_ge hnear) hex

/-- P0029 page 12. Integer shifts leave the sharp model sum unchanged. -/
theorem TX_add_int504 (X : ℕ) (β : ℝ) (k : ℤ) :
    TX150 X (β + k) = TX150 X β := by
  unfold TX150
  apply Finset.sum_congr rfl
  intro n hn
  have heq : (n : ℝ) * (β + k) = (n : ℝ) * β + ((n : ℤ) * k : ℤ) := by
    push_cast
    ring
  rw [heq, ee_add_int]

/-- P0029 page 12. Scaling circular distance by a positive integer gives an upper bound. -/
theorem intDist_mul_nat504 (q a : ℕ) (α : ℝ) (hq : 1 ≤ q) :
    intDist ((q : ℝ) * α) ≤ (q : ℝ) * intDist (α - a / q) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have h := intDist_le_abs_sub ((q : ℝ) * α)
    ((a : ℤ) + q * round (α - a / q))
  have heq : (q : ℝ) * α - ((a : ℤ) + q * round (α - a / q) : ℤ) =
      (q : ℝ) * (α - a / q - round (α - a / q)) := by
    push_cast
    field_simp
    ring
  rw [heq, abs_mul, abs_of_nonneg hqp.le] at h
  exact h

/-- P0029 page 12. The assigned arc term is a canonical nearby reduced residue term. -/
theorem assigned_residue504 {X q : ℕ} (hq : q ∈ Finset.Icc 1 (Nat.sqrt X))
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (ha : α ∈ arcSet150 X q) :
    ∃ b : ℕ, b < q ∧ Nat.Coprime b q ∧
      (Nat.sqrt X : ℝ) * q * intDist (α - b / q) ≤ 1 ∧
      arcTerm150 X q α ^ 2 = wq150 q * TX150 X (α - b / q) ^ 2 := by
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hQ := hq1.trans (Finset.mem_Icc.mp hq).2
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq1
  have hQp : (0 : ℝ) < Nat.sqrt X := by exact_mod_cast hQ
  have hcop := assigned_coprime504 hq1 hα ha
  have ha0 := (nint_mem150 (q := q) hα).1
  have hac : ((nint150 ((q : ℝ) * α)).toNat : ℤ) = nint150 ((q : ℝ) * α) :=
    Int.toNat_of_nonneg ha0
  have hcopI : Int.gcd (nint150 ((q : ℝ) * α)) q = 1 := by
    rw [← hac, Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  obtain ⟨b, hb, hbcop, k, hshift⟩ := reduced_residue_of_int (by omega : 0 < q) hcopI
  refine ⟨b, hb, hbcop, ?_, ?_⟩
  · have hd : intDist (α - b / q) ≤
        |α - (nint150 ((q : ℝ) * α) : ℝ) / q| := by
      have hh := intDist_le_abs_sub (α - (b : ℝ) / q) k
      convert hh using 1
      congr 1
      linarith only [hshift]
    have heq : (q : ℝ) * |α - (nint150 ((q : ℝ) * α) : ℝ) / q| =
        |(q : ℝ) * α - nint150 ((q : ℝ) * α)| := by
      calc
        _ = |(q : ℝ) * (α - (nint150 ((q : ℝ) * α) : ℝ) / q)| := by
          rw [abs_mul, abs_of_pos hqp]
        _ = _ := by
          congr 1
          field_simp
    have hh := mul_le_mul_of_nonneg_left hd hqp.le
    rw [heq] at hh
    have hbound := mul_le_mul_of_nonneg_left (hh.trans ha.1) hQp.le
    have heq' : (Nat.sqrt X : ℝ) * (1 / (Nat.sqrt X : ℝ)) = 1 := by field_simp
    nlinarith only [hbound, heq']
  · have ht : TX150 X (α - (nint150 ((q : ℝ) * α) : ℝ) / q) =
        TX150 X (α - b / q) := by
      have hh := TX_add_int504 X (α - b / q) (-k)
      convert hh using 1
      congr 1
      push_cast
      linarith only [hshift]
    simp only [arcTerm150, ht, mul_pow, div_pow, wq150]

/-- P0029 page 12. A nearby unassigned term with large denominator has linear size. -/
theorem near_term_le504 {X Q q : ℕ} (hX : (X : ℝ) ≤ 4 * (Q : ℝ) ^ 2)
    (hq : 1 ≤ q) (hlarge : (Q : ℝ) ≤ 2 * q) {D : ℝ}
    (hweight : (q : ℝ) ≤ D * Nat.totient q) (β : ℝ) :
    ‖wq150 q * TX150 X β ^ 2‖ ≤ 16 * D ^ 2 * X := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hD : 0 < D := by nlinarith only [hweight, hqp, hφ]
  have hQφ : (Q : ℝ) ≤ 2 * (D * Nat.totient q) := by linarith only [hlarge, hweight]
  have hQφ2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQφ 2
  have hXφ : (X : ℝ) ≤ 16 * D ^ 2 * (Nat.totient q : ℝ) ^ 2 := by
    nlinarith only [hX, hQφ2]
  calc
    _ ≤ (1 / (Nat.totient q : ℝ) ^ 2) * (X : ℝ) ^ 2 := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul norm_wq_le150
        (pow_le_pow_left₀ (norm_nonneg _) (norm_TX_le150 X β) 2)
        (sq_nonneg _) (by positivity)
    _ ≤ 16 * D ^ 2 * X := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hφ)).mp
      have hh := mul_le_mul_of_nonneg_right hXφ (Nat.cast_nonneg X)
      field_simp
      nlinarith only [hh]


/-- P0029 pages 11 and 12. Finite zero modes pass through Abel summation before norms. -/
theorem finite_mode_abel504 {ι : Type*} (Z : Finset ι) (c : ι → ℂ)
    (g : ι → ℕ → ℂ) (r u : ℕ → ℂ) (X : ℕ) :
    ((∑ ρ ∈ Z, c ρ * g ρ X) + r X) * u X -
      ∑ n ∈ Finset.range X, ((∑ ρ ∈ Z, c ρ * g ρ n) + r n) * (u (n + 1) - u n) =
    (∑ ρ ∈ Z, c ρ * (g ρ X * u X -
      ∑ n ∈ Finset.range X, g ρ n * (u (n + 1) - u n))) +
      (r X * u X - ∑ n ∈ Finset.range X, r n * (u (n + 1) - u n)) := by
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_sub,
    Finset.mul_sum, mul_assoc, Finset.sum_sub_distrib]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_comm (s := Finset.range X) (t := Z)]
  ring

/-- P0029 pages 11 and 12. The sharp major arc error at X equal to one has norm one. -/
theorem major_error_one504 (α : ℝ) : ‖Ssum 1 α - VX150 1 α‖ = 1 := by
  have ha : α ∈ arcSet150 1 1 := by
    have hd : |α - (nint150 α : ℝ)| ≤ 1 := by
      unfold nint150
      rw [← round_eq]
      exact (abs_sub_round α).trans (by norm_num)
    simpa [arcSet150] using hd
  have hV : VX150 1 α = ee (α - (nint150 α : ℝ)) := by
    simp [VX150, arcTerm150, ha, TX150]
  rw [hV]
  have hS : Ssum 1 α = 0 := by simp [Ssum]
  rw [hS, zero_sub, norm_neg, norm_ee150]

/-- P0029 page 11, display 3.4. Character orthogonality in conjugate form. -/
theorem character_orthogonality504 {q : ℕ} [NeZero q] (x b : ZMod q) (hx : IsUnit x) :
    (∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ b) * χ x) =
      if b = x then (Nat.totient q : ℂ) else 0 := by
  classical
  by_cases hb : IsUnit b
  · have hc (χ : DirichletCharacter ℂ q) : starRingEnd ℂ (χ b) = χ b⁻¹ := by
      have hnz : χ b ≠ 0 := MulChar.apply_ne_zero_iff.mpr hb
      have hmul : χ b * χ b⁻¹ = 1 := by
        rw [← map_mul, ZMod.mul_inv_of_unit b hb, map_one]
      have hi : χ b⁻¹ = (χ b)⁻¹ := by
        apply mul_left_cancel₀ hnz
        rw [hmul, mul_inv_cancel₀ hnz]
      rw [hi]
      change star (χ b) = (χ b)⁻¹
      rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    simp_rw [hc]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb x
  · have hne : b ≠ x := by rintro rfl; exact hb hx
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [MulChar.map_nonunit χ hb]
    simp

/-- P0029 page 11, display 3.4. Inverting conjugate Gauss sums recovers the additive phase. -/
theorem gauss_character_inversion504 {q : ℕ} [NeZero q] (x : ZMod q) (hx : IsUnit x) :
    ee ((x.val : ℝ) / q) = (1 / (Nat.totient q : ℂ)) *
      (∑ χ : DirichletCharacter ℂ q, tauConj χ * χ x) := by
  have hsum : (∑ χ : DirichletCharacter ℂ q, tauConj χ * χ x) =
      (Nat.totient q : ℂ) * ee ((x.val : ℝ) / q) := by
    classical
    unfold tauConj
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b : ZMod q, ee ((b.val : ℝ) / q) *
          (∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ b) * χ x) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ hχ
        ring
      _ = ∑ b : ZMod q, ee ((b.val : ℝ) / q) *
          (if b = x then (Nat.totient q : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [character_orthogonality504 x b hx]
      _ = _ := by simp [mul_comm]
  rw [hsum]
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  field_simp

/-- P0029 page 11, display 3.6. The normalized character error costs only square root q. -/
theorem character_error_bound504 {q : ℕ} [NeZero q] (x : ZMod q)
    (f : DirichletCharacter ℂ q → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ χ, ‖f χ‖ ≤ B) :
    ‖(1 / (Nat.totient q : ℂ)) *
      (∑ χ : DirichletCharacter ℂ q, tauConj χ * χ x * f χ)‖ ≤ Real.sqrt q * B := by
  classical
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hτ (χ : DirichletCharacter ℂ q) : ‖tauConj χ‖ ≤ Real.sqrt q := by
    simpa using tau_lift_bound443 χ (dvd_refl q)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hs : ‖∑ χ : DirichletCharacter ℂ q, tauConj χ * χ x * f χ‖ ≤
      (Nat.totient q : ℝ) * (Real.sqrt q * B) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, Real.sqrt q * B := by
        apply Finset.sum_le_sum
        intro χ hχ
        rw [norm_mul, norm_mul]
        have hh : ‖tauConj χ‖ * ‖χ x‖ ≤ Real.sqrt q := by
          calc
            _ ≤ Real.sqrt q * 1 := mul_le_mul (hτ χ)
              (DirichletCharacter.norm_le_one χ x) (norm_nonneg _) (Real.sqrt_nonneg _)
            _ = _ := mul_one _
        exact mul_le_mul hh (hB χ) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by simp [hcard]
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc
    _ ≤ (1 / (Nat.totient q : ℝ)) *
        ((Nat.totient q : ℝ) * (Real.sqrt q * B)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp

/-- P0029 page 11, display 3.5. The principal conjugate Gauss sum is the Mobius value. -/
theorem tau_principal504 (q : ℕ) [NeZero q] :
    tauConj (1 : DirichletCharacter ℂ q) = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  rw [tauConj_eq_cChi_inv436, inv_one, cChi_int_gauss436]
  simp only [Int.cast_one, AddChar.mulShift_one]
  have hg : gaussSum (1 : DirichletCharacter ℂ 1) (ZMod.stdAddChar (N := 1)) = 1 := by
    unfold gaussSum
    rw [Fintype.sum_subsingleton (fun a : ZMod 1 =>
      (1 : DirichletCharacter ℂ 1) a * ZMod.stdAddChar a) (0 : ZMod 1)]
    have hunit : IsUnit (0 : ZMod 1) := by
      rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _]
      exact isUnit_one
    simp [MulChar.one_apply hunit]
  have hh := gaussSum_lift_formula443 (1 : DirichletCharacter ℂ 1) (one_dvd q)
  simpa only [map_one, Nat.div_one, hg, mul_one,
    show (1 : DirichletCharacter ℂ 1) ((q : ℕ) : ZMod 1) = 1 by
      rw [show ((q : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _]; exact map_one _]
    using hh

/-- P0029 page 11. An entire function nonzero at one has finitely many zeros in a bounded strip. -/
theorem finite_entire_strip_zeros504 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h1 : f 1 ≠ 0) (T : ℝ) :
    {ρ : ℂ | f ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  let R := |T| + 2
  have hRp : 0 < R := by dsimp [R]; positivity
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hsub : {ρ : ℂ | f ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} ⊆
      closedBall (0 : ℂ) R := by
    intro ρ hρ
    rw [mem_closedBall, dist_zero_right]
    have hn := Complex.norm_le_abs_re_add_abs_im ρ
    have hr := abs_of_pos hρ.2.1
    have hi := hρ.2.2.2.trans (le_abs_self T)
    dsimp [R]
    linarith only [hn, hr, hi, hρ.2.2.1]
  obtain ⟨z, hz, hacc⟩ := hinf.exists_accPt_of_subset_isCompact
    (isCompact_closedBall (0 : ℂ) R) hsub
  have hA : AnalyticOnNhd ℂ f (ball (0 : ℂ) (R + 1)) := fun w _ => hf.analyticAt w
  have hzero : Set.EqOn f 0 (ball (0 : ℂ) (R + 1)) := by
    apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hA isPreconnected_ball
      (z₀ := z)
    · simp only [mem_ball, mem_closedBall, dist_zero_right] at hz ⊢
      linarith
    · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
      exact hacc.mono (principal_mono.mpr fun _ h => h.1)
  apply h1
  apply hzero
  simp only [mem_ball, dist_zero_right, norm_one]
  dsimp [R]
  linarith [abs_nonneg T]

/-- P0029 page 11, display 3.5. Every bounded nontrivial character zero set has a complete finite list. -/
theorem character_zero_finset504 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ Z : Finset ℂ, ∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
  classical
  have hfinite : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
    by_cases hχ : χ = 1
    · subst χ
      have hh := finite_entire_strip_zeros504 (DirichletCharacter.LFunctionTrivChar₁ q)
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
        (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q) T
      apply hh.subset
      intro ρ hρ
      refine ⟨?_, hρ.2⟩
      have hρ1 : ρ ≠ 1 := by
        intro heq
        have hh := hρ.2.2.1
        rw [heq] at hh
        norm_num at hh
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ1]
      change (ρ - 1) * DirichletCharacter.LFunction 1 ρ = 0
      rw [hρ.1, mul_zero]
    · exact finite_entire_strip_zeros504 (DirichletCharacter.LFunction χ)
        (DirichletCharacter.differentiable_LFunction hχ)
        (χ.LFunction_apply_one_ne_zero hχ) T
  exact ⟨hfinite.toFinset, fun ρ => Set.Finite.mem_toFinset hfinite⟩

end LeanLab.BhowmikGrimmelt2026
