module

public import LeanLab.Perelli1996.VaughanInput
public import LeanLab.Perelli1996.Linear88
public import LeanLab.Perelli1996.Divisor103

/-!
P0083 Perelli 1996, page 482, the named Weyl lemma and equations 6 through 8.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Decomp103b
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- A uniform envelope for the linear interval sums in equation 6. -/
def linearEnvelope (H β : ℝ) : ℝ :=
  sSup {x | ∃ start len : ℕ, (len : ℝ) ≤ H + 1 ∧ x = ‖Kernel.T start len β‖}

/-- The normalized heavy or light contribution in equations 7 and 8. -/
def divisorCost (F : ℤ[X]) (c N H D α : ℝ) (heavy : Bool) : ℝ :=
  (∑ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
      (fun h => if heavy then Real.log N ^ D < (divisorCount F.natDegree h : ℝ)
        else (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
    (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h)) / H ^ F.natDegree

/-- The linear interval envelope is nonnegative. -/
theorem linearEnvelope_nonneg (H β : ℝ) : 0 ≤ linearEnvelope H β := by
  unfold linearEnvelope
  apply Real.sSup_nonneg
  rintro x ⟨start, len, hlen, rfl⟩
  exact norm_nonneg _

/-- Both divisor costs are nonnegative for positive H. -/
theorem divisorCost_nonneg (F : ℤ[X]) (c N H D α : ℝ) (heavy : Bool) (hH : 0 < H) :
    0 ≤ divisorCost F c N H D α heavy := by
  unfold divisorCost
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg (Nat.cast_nonneg _) (linearEnvelope_nonneg _ _)

/-- The linear envelope never exceeds the allowed length. -/
theorem linearEnvelope_le (H β : ℝ) (hH : 0 ≤ H + 1) : linearEnvelope H β ≤ H + 1 := by
  unfold linearEnvelope
  apply csSup_le
  · exact ⟨0, 0, 0, by simpa using hH, by simp [Kernel.T]⟩
  · rintro x ⟨start, len, hlen, rfl⟩
    exact (Kernel.norm_T_le start len β).trans hlen

/-- Every permitted linear interval sum is bounded by the envelope. -/
theorem norm_T_le_linearEnvelope (start len : ℕ) (H β : ℝ) (hlen : (len : ℝ) ≤ H + 1) :
    ‖Kernel.T start len β‖ ≤ linearEnvelope H β := by
  unfold linearEnvelope
  apply le_csSup
  · refine ⟨H + 1, ?_⟩
    rintro x ⟨a, m, hm, rfl⟩
    exact (Kernel.norm_T_le a m β).trans hm
  · exact ⟨start, len, hlen, rfl⟩

/-- The two divisor costs partition the full normalized divisor sum. -/
theorem divisorCost_partition (F : ℤ[X]) (c N H D α : ℝ) :
    divisorCost F c N H D α true + divisorCost F c N H D α false =
      (∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
        (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h)) / H ^ F.natDegree := by
  classical
  unfold divisorCost
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← add_div]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hheavy : Real.log N ^ D < (divisorCount F.natDegree h : ℝ)
  · simp [hheavy, not_le.mpr hheavy]
  · simp [hheavy, le_of_not_gt hheavy]


/-- The heavy cost is bounded by the truncated divisor second moment. -/
theorem heavyCost_le (F : ℤ[X]) (c N H D α : ℝ) (hH : 1 ≤ H)
    (hL : 0 < Real.log N) :
    divisorCost F c N H D α true ≤
      ((H + 1) / Real.log N ^ D *
        ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊, (divisorCount F.natDegree h : ℝ) ^ 2) /
          H ^ F.natDegree := by
  have hH0 : 0 < H := by linarith
  have hb := heavy_weight_cutoff (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊)
    (fun h => (divisorCount F.natDegree h : ℝ))
    (fun h => linearEnvelope H (α * h))
    (Real.rpow_pos_of_pos hL D) (show 0 ≤ H + 1 by linarith)
    (fun h _ => Nat.cast_nonneg _) (fun h _ => linearEnvelope_le H (α * h) (by linarith))
  unfold divisorCost
  simp only [Bool.true_eq, ite_true]
  exact div_le_div_of_nonneg_right hb (by positivity)

/-- LEAF. Page 482 equation 7, normalized by H to the k.
Vaughan 1981 page 120 supplies the divisor second moment. -/
theorem leaf_heavy (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree)
    (c D : ℝ) (hc : 0 < c) (hD : 0 < D) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      divisorCost F c N H D α true ≤
        C * Real.log N ^ (-D + (F.natDegree : ℝ) ^ 2 - 1) := by
  let k := F.natDegree
  let l := k ^ 2 - 1
  let T := 2 + Real.log (c + 2)
  let C := 2 * (c + 2) * T ^ l
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hc2 : 0 < c + 2 := by linarith
  have hT : 0 < T := by
    have : 0 ≤ Real.log (c + 2) := Real.log_nonneg (by linarith)
    dsimp [T]
    linarith
  obtain ⟨CM, hCM, hmom⟩ := Divisor103.divisorSecondMoment k hk1
  refine ⟨CM * C, max 3 (Real.exp 1), by positivity, le_max_left _ _, ?_⟩
  intro N H α hN hH hHu
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
    simpa using hh
  have hL : 0 < Real.log N := by linarith
  have hH0 : 0 < H := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hHk : H ^ k ≤ N := by
    have hh := pow_le_pow_left₀ hH0.le hHu k
    change H ^ k ≤ (N ^ (1 / (k : ℝ))) ^ k at hh
    rw [← Real.rpow_natCast (N ^ (1 / (k : ℝ))) k, ← Real.rpow_mul hN0.le,
      show 1 / (k : ℝ) * k = 1 by field_simp, Real.rpow_one] at hh
    exact hh
  have hHpred : H ^ (k - 1) ≤ N := by
    exact (pow_le_pow_right₀ hH (show k - 1 ≤ k by omega)).trans hHk
  let x := (c + 2) * H ^ (k - 1)
  have hx : 2 ≤ x := by
    have hp : 1 ≤ H ^ (k - 1) := one_le_pow₀ hH
    dsimp [x]
    nlinarith
  have hsum : (∑ h ∈ Icc 1 ⌊c * H ^ (k - 1)⌋₊, (divisorCount k h : ℝ) ^ 2) ≤
      CM * x * Real.log (Real.exp 1 * x) ^ l := by
    apply le_trans _ (hmom x hx)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.Icc_subset_Icc le_rfl
      apply Nat.floor_le_floor
      dsimp [x]
      nlinarith [pow_pos hH0 (k - 1)]
    · intro h _ _; exact sq_nonneg _
  have hxN : x ≤ (c + 2) * N := mul_le_mul_of_nonneg_left hHpred hc2.le
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * x) := Real.log_nonneg (by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith)
  have hlogx : Real.log (Real.exp 1 * x) ≤ T * Real.log N := by
    calc
      _ = 1 + Real.log x := by rw [Real.log_mul (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
      _ ≤ 1 + Real.log ((c + 2) * N) := add_le_add le_rfl (Real.log_le_log hx0 hxN)
      _ = 1 + Real.log (c + 2) + Real.log N := by rw [Real.log_mul hc2.ne' hN0.ne']; ring
      _ ≤ _ := by
        have hcLog : 0 ≤ Real.log (c + 2) := Real.log_nonneg (by linarith)
        dsimp [T]
        nlinarith
  have hsum' : (∑ h ∈ Icc 1 ⌊c * H ^ (k - 1)⌋₊, (divisorCount k h : ℝ) ^ 2) ≤
      CM * (c + 2) * T ^ l * H ^ (k - 1) * Real.log N ^ l := by
    calc
      _ ≤ CM * x * (T * Real.log N) ^ l := hsum.trans (by gcongr)
      _ = _ := by dsimp [x]; rw [mul_pow]; ring
  have hb := heavyCost_le F c N H D α hH hL
  have hHrel : H ^ k = H ^ (k - 1) * H := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
  have hcoef : (H + 1) / H ≤ 2 := (div_le_iff₀ hH0).mpr (by linarith)
  calc
    _ ≤ ((H + 1) / Real.log N ^ D *
        (CM * (c + 2) * T ^ l * H ^ (k - 1) * Real.log N ^ l)) / H ^ k :=
      hb.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum' (by positivity)) (by positivity))
    _ = CM * (c + 2) * T ^ l * ((H + 1) / H) * Real.log N ^ (-D + (k : ℝ) ^ 2 - 1) := by
      rw [hHrel]
      have hl : (l : ℝ) = (k : ℝ) ^ 2 - 1 := by
        dsimp [l]
        rw [Nat.cast_sub (by nlinarith : 1 ≤ k ^ 2)]
        push_cast
        ring
      rw [show -D + (k : ℝ) ^ 2 - 1 = -D + (l : ℝ) by rw [hl]; ring,
        Real.rpow_add hL, Real.rpow_neg hL.le, Real.rpow_natCast]
      field_simp
      <;> ring
    _ ≤ CM * (c + 2) * T ^ l * 2 * Real.log N ^ (-D + (k : ℝ) ^ 2 - 1) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity)) (by positivity)
    _ = _ := by dsimp [C]; ring



set_option maxHeartbeats 2000000

theorem linearEnvelope_le_int (H β : ℝ) (hH : 1 ≤ H) (hβ : β ≠ (round β : ℝ)) :
    linearEnvelope H β ≤ min (H + 1) (1 / (2 * |β - (round β : ℝ)|)) := by
  unfold linearEnvelope
  apply csSup_le
  · refine ⟨0, 0, 0, ?_, ?_⟩
    · push_cast; linarith
    · simp [Kernel.T]
  · rintro x ⟨start, len, hlen, rfl⟩
    calc ‖Kernel.T start len β‖
        ≤ min (len : ℝ) (1 / (2 * |β - (round β : ℝ)|)) := Kernel.norm_T_le_min start len hβ
      _ ≤ min (H + 1) (1 / (2 * |β - (round β : ℝ)|)) :=
          min_le_min (hlen.trans (by linarith)) le_rfl

theorem divisorCost_le_int_sum (F : ℤ[X]) (c N H D α : ℝ) (hH : 1 ≤ H)
    (hL : 0 ≤ Real.log N) :
    divisorCost F c N H D α false ≤
      (Real.log N ^ D *
        ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
          (if α * h = (round (α * h) : ℝ) then H + 1
           else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|)))) /
        H ^ F.natDegree := by
  classical
  have hH0 : 0 < H := by linarith
  have hD : 0 ≤ Real.log N ^ D := Real.rpow_nonneg hL D
  have hterm : ∀ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
      (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
      (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h) ≤
        Real.log N ^ D *
          (if α * h = (round (α * h) : ℝ) then H + 1
           else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|))) := by
    intro h hh
    obtain ⟨-, ht⟩ := Finset.mem_filter.mp hh
    apply mul_le_mul ht _ (linearEnvelope_nonneg _ _) hD
    by_cases hc : α * h = (round (α * h) : ℝ)
    · rw [if_pos hc]
      exact linearEnvelope_le H (α * h) (by linarith)
    · rw [if_neg hc]
      exact linearEnvelope_le_int H (α * h) hH hc
  have hgn : ∀ h : ℕ, 0 ≤ (if α * h = (round (α * h) : ℝ) then H + 1
      else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|))) := by
    intro h
    by_cases hc : α * h = (round (α * h) : ℝ)
    · rw [if_pos hc]; linarith
    · rw [if_neg hc]
      exact le_min (by linarith) (by positivity)
  have hstep : (∑ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
      (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
      (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h)) ≤
      Real.log N ^ D * ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
        (if α * h = (round (α * h) : ℝ) then H + 1
         else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|))) := by
    calc (∑ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
          (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
          (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h))
        ≤ ∑ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
            (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
            Real.log N ^ D *
              (if α * h = (round (α * h) : ℝ) then H + 1
               else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|))) :=
          Finset.sum_le_sum hterm
      _ = Real.log N ^ D * ∑ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
            (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
            (if α * h = (round (α * h) : ℝ) then H + 1
             else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|))) := by
          rw [Finset.mul_sum]
      _ ≤ Real.log N ^ D * ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
            (if α * h = (round (α * h) : ℝ) then H + 1
             else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D) _)
              (fun h _ _ => hgn h)) hD
  unfold divisorCost
  simp only [Bool.false_eq_true, ite_false]
  exact div_le_div_of_nonneg_right hstep (by positivity)

/-- `leaf_light` follows from a reciprocal-sum estimate for the phases `h * α`. -/
theorem leaf_light_of_recip_sum (F : ℤ[X]) (hk : 2 ≤ F.natDegree)
    (c D : ℝ) (hc : 0 < c) (hD : 0 < D)
    (hRS : ∃ K : ℝ, 1 ≤ K ∧ ∀ (X Y : ℝ) (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ X → 1 ≤ Y →
      0 < q → Nat.Coprime a.natAbs q → |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      ∑ h ∈ Icc 1 ⌊X⌋₊,
          (if α * h = (round (α * h) : ℝ) then Y
           else min Y (1 / (2 * |α * h - (round (α * h) : ℝ)|)))
        ≤ K * (1 + Real.log X + Real.log Y) * (X + Y + q + X * Y / q)) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      1 / H + divisorCost F c N H D α false ≤
        C * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
          Real.log N ^ (D + 1) := by
  classical
  obtain ⟨K, hK1, hrec⟩ := hRS
  have hlogc0 : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hCpos : 0 < K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * (3 * c + 5)) + 1 := by
    have h1 : 0 < 1 + Real.log (c + 1) + Real.log 2 + 2 := by linarith
    have h2 : 0 < 3 * c + 5 := by linarith
    have h3 : 0 < K := by linarith
    nlinarith [mul_pos h3 (mul_pos h1 h2)]
  refine ⟨K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * (3 * c + 5)) + 1, 3,
    hCpos, le_rfl, ?_⟩
  intro N H α hN hH hHu a q hq hcop happ
  have hN3 : (3 : ℝ) ≤ N := hN
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) h3
  have hL1 : (1 : ℝ) ≤ Real.log N := hlog3.trans (Real.log_le_log (by norm_num) hN3)
  have hLpos : 0 < Real.log N := by linarith
  have hH0 : 0 < H := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : 0 < N := by linarith
  have hHk : H ^ F.natDegree ≤ N := by
    have hh := pow_le_pow_left₀ hH0.le hHu F.natDegree
    change H ^ F.natDegree ≤ (N ^ (1 / (F.natDegree : ℝ))) ^ F.natDegree at hh
    rw [← Real.rpow_natCast (N ^ (1 / (F.natDegree : ℝ))) F.natDegree, ← Real.rpow_mul hN0.le,
      show 1 / (F.natDegree : ℝ) * (F.natDegree : ℝ) = 1 by field_simp, Real.rpow_one] at hh
    exact hh
  have hHlog : Real.log H ≤ Real.log N := by
    have h0 : 0 ≤ Real.log H := Real.log_nonneg hH
    have h1 : (F.natDegree : ℝ) * Real.log H ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hHk
    have hkR : (1 : ℝ) ≤ (F.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ F.natDegree)
    nlinarith [h0, h1, hkR]
  set X' : ℝ := max (c * H ^ (F.natDegree - 1)) 1 with hX'def
  have hX'1 : 1 ≤ X' := by rw [hX'def]; exact le_max_right _ _
  have hpow1 : (1 : ℝ) ≤ H ^ (F.natDegree - 1) := one_le_pow₀ hH
  have hX'le : X' ≤ (c + 1) * H ^ (F.natDegree - 1) := by
    rw [hX'def]
    have h1 : c * H ^ (F.natDegree - 1) ≤ (c + 1) * H ^ (F.natDegree - 1) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (1 : ℝ) ≤ (c + 1) * H ^ (F.natDegree - 1) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (c + 1) * H ^ (F.natDegree - 1) := by
            apply mul_le_mul (by linarith) hpow1 (by norm_num) (by linarith)
    exact max_le h1 h2
  have hfloor : ⌊c * H ^ (F.natDegree - 1)⌋₊ ≤ ⌊X'⌋₊ :=
    Nat.floor_mono (by rw [hX'def]; exact le_max_left _ _)
  have hcost : divisorCost F c N H D α false ≤
      (Real.log N ^ D *
        ∑ h ∈ Icc 1 ⌊X'⌋₊,
          (if α * h = (round (α * h) : ℝ) then H + 1
           else min (H + 1) (1 / (2 * |α * h - (round (α * h) : ℝ)|)))) /
        H ^ F.natDegree := by
    refine (divisorCost_le_int_sum F c N H D α hH hLpos.le).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLpos.le D)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hfloor)
    intro h _ _
    by_cases hc' : α * h = (round (α * h) : ℝ)
    · rw [if_pos hc']; linarith
    · rw [if_neg hc']
      exact le_min (by linarith) (by positivity)
  have hY1 : (1 : ℝ) ≤ H + 1 := by linarith
  have hsum := hrec X' (H + 1) α a q hX'1 hY1 hq hcop happ
  have hcost2 : divisorCost F c N H D α false ≤
      (Real.log N ^ D *
        (K * (1 + Real.log X' + Real.log (H + 1)) *
          (X' + (H + 1) + q + X' * (H + 1) / q))) / H ^ F.natDegree := by
    refine hcost.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hLpos.le D)
  have hlogX : Real.log X' ≤ Real.log (c + 1) + Real.log N := by
    have h1 : Real.log X' ≤ Real.log ((c + 1) * H ^ (F.natDegree - 1)) :=
      Real.log_le_log (by linarith) hX'le
    have h2 : Real.log ((c + 1) * H ^ (F.natDegree - 1))
        = Real.log (c + 1) + ((F.natDegree - 1 : ℕ) : ℝ) * Real.log H := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have h3 : ((F.natDegree - 1 : ℕ) : ℝ) * Real.log H ≤ Real.log N := by
      have h0 : 0 ≤ Real.log H := Real.log_nonneg hH
      have h4 : ((F.natDegree - 1 : ℕ) : ℝ) ≤ (F.natDegree : ℝ) := by
        exact_mod_cast Nat.sub_le F.natDegree 1
      have h5 : (F.natDegree : ℝ) * Real.log H ≤ Real.log N := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hHk
      nlinarith [h0, h5, h4]
    rw [h2] at h1
    linarith
  have hlogY : Real.log (H + 1) ≤ Real.log 2 + Real.log N := by
    have h1 : Real.log (H + 1) ≤ Real.log (2 * H) := by
      apply Real.log_le_log (by linarith)
      linarith
    rw [Real.log_mul (by norm_num) hH0.ne'] at h1
    linarith [hHlog]
  have hlogc : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogfac : 1 + Real.log X' + Real.log (H + 1) ≤
      (1 + Real.log (c + 1) + Real.log 2 + 2) * Real.log N := by
    have h1 : Real.log (c + 1) * 1 ≤ Real.log (c + 1) * Real.log N :=
      mul_le_mul_of_nonneg_left hL1 hlogc
    have h2 : Real.log 2 * 1 ≤ Real.log 2 * Real.log N :=
      mul_le_mul_of_nonneg_left hL1 hlog2
    have h3 : (1 : ℝ) * 1 ≤ 1 * Real.log N := by linarith
    nlinarith [hlogX, hlogY, h1, h2, h3]
  have hHk0 : 0 < H ^ F.natDegree := by positivity
  have hsplit : H ^ F.natDegree = H ^ (F.natDegree - 1) * H := by
    conv_lhs => rw [show F.natDegree = F.natDegree - 1 + 1 by omega, pow_succ]
  have hA : 0 < H ^ (F.natDegree - 1) := by positivity
  have hHle : H ≤ H ^ (F.natDegree - 1) := by
    calc H = H ^ 1 := by ring
      _ ≤ H ^ (F.natDegree - 1) := pow_le_pow_right₀ hH (by omega)
  have hH1 : H + 1 ≤ 2 * H := by linarith
  have hX'sum : X' + (H + 1) + q + X' * (H + 1) / q ≤
      (c + 1) * H ^ (F.natDegree - 1) + (H + 1) + q +
        2 * (c + 1) * (H ^ F.natDegree / q) := by
    have hmul : (c + 1) * H ^ (F.natDegree - 1) * (H + 1) ≤ 2 * (c + 1) * H ^ F.natDegree := by
      have h2 : (c + 1) * H ^ (F.natDegree - 1) * (H + 1) ≤
          (c + 1) * H ^ (F.natDegree - 1) * (2 * H) :=
        mul_le_mul_of_nonneg_left hH1 (by positivity)
      rw [hsplit]
      nlinarith [h2]
    have h3 : X' * (H + 1) / q ≤ 2 * (c + 1) * (H ^ F.natDegree / q) := by
      calc X' * (H + 1) / q ≤ (c + 1) * H ^ (F.natDegree - 1) * (H + 1) / q :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hX'le (by linarith)) hq0.le
        _ ≤ 2 * (c + 1) * H ^ F.natDegree / q := div_le_div_of_nonneg_right hmul hq0.le
        _ = 2 * (c + 1) * (H ^ F.natDegree / q) := by ring
    linarith
  have hRH : (c + 1) * H ^ (F.natDegree - 1) + (H + 1) + q +
      2 * (c + 1) * (H ^ F.natDegree / q) ≤
      (3 * c + 5) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
        H ^ F.natDegree := by
    have hRHk : (3 * c + 5) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
        H ^ F.natDegree =
        (3 * c + 5) * (H ^ F.natDegree / q + H ^ (F.natDegree - 1) + q) := by
      rw [hsplit]; field_simp; try ring
    rw [hRHk]
    have hB : 0 ≤ H ^ F.natDegree / q := by positivity
    have hP : 0 ≤ H ^ (F.natDegree - 1) := hA.le
    have hqq : 0 ≤ (q : ℝ) := hq0.le
    have hc1 : c + 1 ≤ 3 * c + 5 := by linarith
    have hc4 : (1 : ℝ) ≤ 3 * c + 5 := by linarith
    have hc5 : (0 : ℝ) ≤ 2 * c + 4 := by linarith
    have k1 : (c + 1) * H ^ (F.natDegree - 1) ≤ (3 * c + 5) * H ^ (F.natDegree - 1) :=
      mul_le_mul_of_nonneg_right hc1 hP
    have k2 : 2 * (c + 1) * (H ^ F.natDegree / q) ≤ (3 * c + 5) * (H ^ F.natDegree / q) := by
      have h2 : 2 * (c + 1) ≤ 3 * c + 5 := by linarith
      exact mul_le_mul_of_nonneg_right h2 hB
    have k3 : q ≤ (3 * c + 5) * q := by
      simpa using mul_le_mul_of_nonneg_right hc4 hqq
    have k4 : H + 1 ≤ (2 * c + 4) * H ^ (F.natDegree - 1) := by
      have h2 : (2 * c + 4) * H ≤ (2 * c + 4) * H ^ (F.natDegree - 1) :=
        mul_le_mul_of_nonneg_left hHle hc5
      nlinarith [h2]
    nlinarith [k1, k2, k3, k4, mul_nonneg hc5 hP]
  have hcost3 : divisorCost F c N H D α false ≤
      K * (1 + Real.log (c + 1) + Real.log 2 + 2) * (3 * c + 5) *
        (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
        (Real.log N ^ D) * Real.log N := by
    have hlogX'0 : 0 ≤ Real.log X' := Real.log_nonneg hX'1
    have hlogY0 : 0 ≤ Real.log (H + 1) := Real.log_nonneg (by linarith)
    have hC0 : 0 ≤ 1 + Real.log (c + 1) + Real.log 2 + 2 := by linarith
    have hK0 : (0 : ℝ) ≤ K := by linarith
    have ha' : (0 : ℝ) ≤ (1 + Real.log (c + 1) + Real.log 2 + 2) * Real.log N :=
      mul_nonneg hC0 hLpos.le
    have hb : (0 : ℝ) ≤ X' + (H + 1) + q + X' * (H + 1) / q := by positivity
    have hmain : K * (1 + Real.log X' + Real.log (H + 1)) *
          (X' + (H + 1) + q + X' * (H + 1) / q) ≤
        K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * Real.log N) *
          ((3 * c + 5) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
            H ^ F.natDegree) := by
      calc K * (1 + Real.log X' + Real.log (H + 1)) *
              (X' + (H + 1) + q + X' * (H + 1) / q)
          ≤ K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * Real.log N) *
              (X' + (H + 1) + q + X' * (H + 1) / q) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogfac hK0) hb
        _ ≤ K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * Real.log N) *
              ((3 * c + 5) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
                H ^ F.natDegree) :=
            mul_le_mul_of_nonneg_left (hX'sum.trans hRH) (mul_nonneg hK0 ha')
    refine hcost2.trans ?_
    calc (Real.log N ^ D * (K * (1 + Real.log X' + Real.log (H + 1)) *
            (X' + (H + 1) + q + X' * (H + 1) / q))) / H ^ F.natDegree
        ≤ (Real.log N ^ D * (K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * Real.log N) *
            ((3 * c + 5) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
              H ^ F.natDegree))) / H ^ F.natDegree := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hLpos.le D)
      _ = _ := by field_simp; try ring
  have hone : 1 / H ≤ Real.log N ^ (D + 1) *
      (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) := by
    have hpow : (1 : ℝ) ≤ Real.log N ^ (D + 1) := one_le_rpow hL1 (by linarith)
    have hR : 1 / H ≤ (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) := by
      have h1 : 0 ≤ 1 / (q : ℝ) := by positivity
      have h2 : 0 ≤ (q : ℝ) / H ^ F.natDegree := by positivity
      linarith
    have h3 : (1 : ℝ) * (1 / H) ≤ Real.log N ^ (D + 1) *
        (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) :=
      mul_le_mul hpow hR (by positivity) (by linarith)
    simpa using h3
  calc 1 / H + divisorCost F c N H D α false
      ≤ Real.log N ^ (D + 1) *
          (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) +
        K * (1 + Real.log (c + 1) + Real.log 2 + 2) * (3 * c + 5) *
          (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
          (Real.log N ^ D) * Real.log N := add_le_add hone hcost3
    _ = (K * ((1 + Real.log (c + 1) + Real.log 2 + 2) * (3 * c + 5)) + 1) *
          (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
          Real.log N ^ (D + 1) := by
        rw [Real.rpow_add hLpos, Real.rpow_one]
        ring

set_option maxHeartbeats 2000000

theorem d_le_abs_sub (x : ℝ) (m : ℤ) : |x - round x| ≤ |x - (m : ℝ)| :=
  round_le x m

theorem d_le_half (x : ℝ) : |x - round x| ≤ 1 / 2 := abs_sub_round x

theorem d_neg (x : ℝ) : |(-x) - round (-x)| = |x - round x| := by
  apply le_antisymm
  · have h := d_le_abs_sub (-x) (-(round x))
    have he : (-x : ℝ) - ((-(round x) : ℤ) : ℝ) = -(x - (round x : ℝ)) := by
      push_cast; ring
    rw [he, abs_neg] at h
    exact h
  · have h := d_le_abs_sub x (-(round (-x)))
    have he : (x : ℝ) - ((-(round (-x)) : ℤ) : ℝ) = -((-x) - (round (-x) : ℝ)) := by
      push_cast; ring
    rw [he, abs_neg] at h
    exact h

theorem d_triangle (x y : ℝ) :
    |x - round x| ≤ |(x + y) - round (x + y)| + |y - round y| := by
  have h := d_le_abs_sub x (round (x + y) - round y)
  have he : x - (((round (x + y) - round y : ℤ)) : ℝ) =
      ((x + y) - (round (x + y) : ℝ)) + ((round y : ℝ) - y) := by
    push_cast; try ring
  rw [he] at h
  refine h.trans ?_
  calc |((x + y) - (round (x + y) : ℝ)) + ((round y : ℝ) - y)|
      ≤ |(x + y) - (round (x + y) : ℝ)| + |(round y : ℝ) - y| := abs_add_le _ _
    _ = |(x + y) - (round (x + y) : ℝ)| + |y - round y| := by
        rw [abs_sub_comm ((round y : ℝ)) y]

theorem d_add_ge (x y : ℝ) :
    |x - round x| - |y| ≤ |(x + y) - round (x + y)| := by
  have h := d_triangle x y
  have hy : |y - round y| ≤ |y| := by
    have h0 := d_le_abs_sub y 0
    simpa using h0
  linarith

/-- The phase difference of two points of one block, as an integer cast. -/
theorem d_sub_ge_int (x y : ℝ) :
    |(x - y) - round (x - y)| ≤ |(x - round x) - (y - round y)| := by
  have h := d_le_abs_sub (x - y) (round x - round y)
  have he : (x - y) - (((round x - round y : ℤ)) : ℝ) =
      (x - round x) - (y - round y) := by push_cast; try ring
  rwa [he] at h

/-- Phases in a common block of length below `q/2` are `1/(2q)`-separated. -/
theorem d_sep_nat (α : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2)
    (e : ℕ) (he0 : 0 < e) (heq : (e : ℝ) ≤ (q : ℝ) / 2) :
    1 / (2 * (q : ℝ)) ≤ |α * (e : ℝ) - round (α * (e : ℝ))| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set β : ℝ := α - (a : ℝ) / (q : ℝ) with hβ
  have hβle : |β| ≤ 1 / (q : ℝ) ^ 2 := happ
  have heq2 : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by field_simp; try ring
  -- the rational point is at distance at least `1/q`
  have hrat : 1 / (q : ℝ) ≤
      |((a : ℝ) * (e : ℝ) / (q : ℝ)) - (round ((a : ℝ) * (e : ℝ) / (q : ℝ)) : ℝ)| := by
    set M : ℤ := round ((a : ℝ) * (e : ℝ) / (q : ℝ)) with hM
    have hcast : ((a : ℝ) * (e : ℝ) / (q : ℝ)) - (M : ℝ) =
        (((a * (e : ℤ) - M * (q : ℤ) : ℤ)) : ℝ) / (q : ℝ) := by
      push_cast; field_simp; try ring
    have hne : (a * (e : ℤ) - M * (q : ℤ) : ℤ) ≠ 0 := by
      intro hzero
      have hdvdZ : (q : ℤ) ∣ a * (e : ℤ) := ⟨M, by linarith [hzero]⟩
      have hdvdN : q ∣ e * a.natAbs := by
        have h1 : (q : ℤ).natAbs ∣ (a * (e : ℤ)).natAbs := Int.natAbs_dvd_natAbs.mpr hdvdZ
        rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
        simpa [mul_comm] using h1
      have hdvdE : q ∣ e := hcop.symm.dvd_of_dvd_mul_right hdvdN
      have hqle : q ≤ e := Nat.le_of_dvd he0 hdvdE
      have hqe : (q : ℝ) ≤ (e : ℝ) := by exact_mod_cast hqle
      have he1 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he0
      linarith
    rw [hcast, abs_div, abs_of_pos hq0]
    refine (le_div_iff₀ hq0).mpr ?_
    have hone : (1 : ℤ) ≤ |(a * (e : ℤ) - M * (q : ℤ) : ℤ)| := Int.one_le_abs hne
    have hR : (1 : ℝ) ≤ ((|(a * (e : ℤ) - M * (q : ℤ) : ℤ)| : ℤ) : ℝ) := by
      exact_mod_cast hone
    have hone' : 1 / (q : ℝ) * (q : ℝ) = 1 := by field_simp
    rw [hone']
    simpa using hR
  -- `d(β e) ≤ |β e| ≤ 1/(2q)`
  have hβe : |β * (e : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
    have heq' : |(e : ℝ)| ≤ (q : ℝ) / 2 := by
      rw [abs_of_nonneg (by positivity)]; exact heq
    have h1 : |β| * |(e : ℝ)| ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) :=
      mul_le_mul hβle heq' (abs_nonneg _) (by positivity)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ))] at h1
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ))]
    calc |β| * (e : ℝ) ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) := h1
      _ = 1 / (2 * (q : ℝ)) := by field_simp; try ring
  have hβe' : |β * (e : ℝ)| ≤ (1 / (q : ℝ)) / 2 := by rw [← heq2]; exact hβe
  have hαe : α * (e : ℝ) = ((a : ℝ) * (e : ℝ) / (q : ℝ)) + β * (e : ℝ) := by
    rw [hβ]; ring
  have hstep : |((a : ℝ) * (e : ℝ) / (q : ℝ)) -
      round ((a : ℝ) * (e : ℝ) / (q : ℝ))| - |β * (e : ℝ)| ≤
      |α * (e : ℝ) - round (α * (e : ℝ))| := by
    rw [hαe]
    exact d_add_ge _ _
  have hfin : (1 / (q : ℝ)) / 2 ≤ |α * (e : ℝ) - round (α * (e : ℝ))| := by
    linarith
  rw [heq2]
  exact hfin

/-! ### 2. Separated points in an interval -/

theorem card_sep_real (s : Finset ℝ) (a b δ : ℝ) (hδ : 0 < δ) (hab : a ≤ b)
    (hs : ∀ x ∈ s, a ≤ x ∧ x ≤ b)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) :
    (s.card : ℝ) ≤ (b - a) / δ + 1 := by
  classical
  suffices H : ∀ n : ℕ, ∀ (s : Finset ℝ), s.card = n → ∀ a b : ℝ, 0 < δ → a ≤ b →
      (∀ x ∈ s, a ≤ x ∧ x ≤ b) → (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) →
      (s.card : ℝ) ≤ (b - a) / δ + 1 by
    exact H s.card s rfl a b hδ hab hs hsep
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hcard a b hδ hab hs hsep
    rcases Finset.eq_empty_or_nonempty s with rfl | hne
    · have h0 : 0 ≤ (b - a) / δ := div_nonneg (by linarith) hδ.le
      simp only [Finset.card_empty, Nat.cast_zero]
      linarith
    · set m := s.min' hne with hm
      have hmem : m ∈ s := Finset.min'_mem s hne
      have hmin : ∀ x ∈ s, m ≤ x := fun x hx => Finset.min'_le s x hx
      have hsub : ∀ x ∈ s.erase m, m + δ ≤ x ∧ x ≤ b := by
        intro x hx
        obtain ⟨hxm, hxs⟩ := Finset.mem_erase.mp hx
        have hmx : m < x := lt_of_le_of_ne (hmin x hxs) (Ne.symm hxm)
        have hd : δ ≤ |x - m| := hsep x hxs m hmem hxm
        rw [abs_of_pos (by linarith : (0:ℝ) < x - m)] at hd
        exact ⟨by linarith, (hs x hxs).2⟩
      have hsep' : ∀ x ∈ s.erase m, ∀ y ∈ s.erase m, x ≠ y → δ ≤ |x - y| := by
        intro x hx y hy hxy
        exact hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
      have hcard' : (s.erase m).card = n - 1 := by
        rw [Finset.card_erase_of_mem hmem, hcard]
      have hn0 : 0 < n := by rw [← hcard]; exact Finset.card_pos.mpr hne
      have hc : (s.card : ℝ) = ((s.erase m).card : ℝ) + 1 := by
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr hne
        rw [Finset.card_erase_of_mem hmem, Nat.cast_sub hpos]
        push_cast
        try ring
      have hma : m ≥ a := (hs m hmem).1
      have hb1 : (b - m) / δ ≤ (b - a) / δ :=
        div_le_div_of_nonneg_right (by linarith) hδ.le
      rw [hc]
      rcases le_or_gt (m + δ) b with hcase | hcase
      · have ih' := ih (n - 1) (by omega) (s.erase m) hcard' (m + δ) b hδ hcase hsub hsep'
        have hstep : (b - (m + δ)) / δ + 1 + 1 = (b - m) / δ + 1 := by
          field_simp
          ring
        linarith
      · have hempty : s.erase m = ∅ := by
          rcases Finset.eq_empty_or_nonempty (s.erase m) with h | h
          · exact h
          · obtain ⟨x, hx⟩ := h
            have h1 := (hsub x hx).1
            have h2 := (hsub x hx).2
            linarith
        rw [hempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        have : 0 ≤ (b - a) / δ := div_nonneg (by linarith) hδ.le
        linarith

/-! ### 3. A block of `q/2` consecutive phases meets each level set rarely -/

theorem phase_sep (α : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2)
    (x y : ℕ) (hne : x ≠ y) (hdiff : |(x : ℝ) - (y : ℝ)| < (q : ℝ) / 2) :
    1 / (2 * (q : ℝ)) ≤ |(α * (x : ℝ) - (round (α * (x : ℝ)) : ℝ)) -
        (α * (y : ℝ) - (round (α * (y : ℝ)) : ℝ))| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsym : |(x : ℝ) - (y : ℝ)| = |(y : ℝ) - (x : ℝ)| := abs_sub_comm _ _
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · -- `x < y`: use the difference `y - x`
    have he0 : 0 < y - x := by omega
    have hcast : (y : ℝ) - (x : ℝ) = ((y - x : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hlt.le]; ring
    have hle : ((y - x : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
      have h2 : |(y : ℝ) - (x : ℝ)| < (q : ℝ) / 2 := by rw [← hsym]; exact hdiff
      have hyx : (0:ℝ) < (y : ℝ) - (x : ℝ) := by
        have h' : (x:ℝ) < (y:ℝ) := by exact_mod_cast hlt
        linarith
      rw [abs_of_pos hyx] at h2
      rw [← hcast]; exact h2.le
    have hsep := d_sep_nat α a q hq hcop happ (y - x) he0 hle
    have harg : α * ((y : ℝ) - (x : ℝ)) = α * (x : ℝ) * 0 + α * ((y:ℝ) - (x:ℝ)) := by ring
    have h1 : 1 / (2 * (q : ℝ)) ≤
        |α * ((y : ℝ) - (x : ℝ)) - round (α * ((y : ℝ) - (x : ℝ)))| := by
      rw [hcast]
      exact hsep
    have h2 := d_sub_ge_int (α * (y : ℝ)) (α * (x : ℝ))
    have h3 : α * (y : ℝ) - α * (x : ℝ) = α * ((y : ℝ) - (x : ℝ)) := by ring
    have h4 : (α * (y : ℝ) - round (α * (y : ℝ)) - (α * (x : ℝ) - round (α * (x : ℝ)))) =
        -((α * (x : ℝ) - round (α * (x : ℝ))) - (α * (y : ℝ) - round (α * (y : ℝ)))) := by ring
    rw [h3, h4, abs_neg] at h2
    linarith
  · -- `y < x`
    have he0 : 0 < x - y := by omega
    have hcast : (x : ℝ) - (y : ℝ) = ((x - y : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hlt.le]; ring
    have hle : ((x - y : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
      have h2 : (x : ℝ) - (y : ℝ) < (q : ℝ) / 2 := by
        have h' : (y:ℝ) < (x:ℝ) := by exact_mod_cast hlt
        rw [abs_of_pos (by linarith : (0:ℝ) < (x : ℝ) - (y : ℝ))] at hdiff
        exact hdiff
      rw [← hcast]; exact h2.le
    have hsep := d_sep_nat α a q hq hcop happ (x - y) he0 hle
    have h1 : 1 / (2 * (q : ℝ)) ≤
        |α * ((x : ℝ) - (y : ℝ)) - round (α * ((x : ℝ) - (y : ℝ)))| := by
      rw [hcast]
      exact hsep
    have h2 := d_sub_ge_int (α * (x : ℝ)) (α * (y : ℝ))
    have h3 : α * (x : ℝ) - α * (y : ℝ) = α * ((x : ℝ) - (y : ℝ)) := by ring
    rw [h3] at h2
    linarith

theorem card_dist_block (α : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2)
    (B : Finset ℕ)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → |(x : ℝ) - (y : ℝ)| < (q : ℝ) / 2)
    (r : ℝ) (hr : 0 ≤ r) :
    ((B.filter (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < r)).card : ℝ)
      ≤ 1 + 4 * (q : ℝ) * r := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set B' : Finset ℕ := B.filter
    (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < r) with hB'
  set φ : ℕ → ℝ := fun h => α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ) with hφ
  have hinj : ∀ x ∈ B', ∀ y ∈ B', φ x = φ y → x = y := by
    intro x hx y hy heq
    by_contra hne
    have hsep := phase_sep α a q hq hcop happ x y hne (hB x (Finset.mem_filter.mp hx).1
      y (Finset.mem_filter.mp hy).1 hne)
    have hzero : |φ x - φ y| = 0 := by rw [heq, sub_self, abs_zero]
    rw [hzero] at hsep
    have hpos : 0 < 1 / (2 * (q : ℝ)) := by positivity
    linarith
  have hcard : ((B'.image φ).card : ℝ) = (B'.card : ℝ) := by
    rw [Finset.card_image_of_injOn (f := φ) (fun x hx y hy h => hinj x hx y hy h)]
  have hmem : ∀ z ∈ B'.image φ, -r ≤ z ∧ z ≤ r := by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    have hlt : |φ h| < r := (Finset.mem_filter.mp hh).2
    rw [abs_lt] at hlt
    exact ⟨hlt.1.le, hlt.2.le⟩
  have hsep' : ∀ z ∈ B'.image φ, ∀ w ∈ B'.image φ, z ≠ w → 1 / (2 * (q : ℝ)) ≤ |z - w| := by
    intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by
      rintro rfl
      exact hzw rfl
    exact phase_sep α a q hq hcop happ x y hxy (hB x (Finset.mem_filter.mp hx).1
      y (Finset.mem_filter.mp hy).1 hxy)
  have hfin := card_sep_real (B'.image φ) (-r) r (1 / (2 * (q : ℝ))) (by positivity)
    (by linarith) hmem hsep'
  have hval : (r - (-r)) / (1 / (2 * (q : ℝ))) + 1 = 4 * (q : ℝ) * r + 1 := by
    field_simp
    ring
  rw [hval] at hfin
  rw [← hcard]
  linarith

theorem geom_two (J : ℕ) : (∑ j ∈ range J, (2 : ℝ) ^ j) = 2 ^ J - 1 := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem two_pow_half_pow (j : ℕ) : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by
  rw [← mul_pow]; norm_num

theorem half_pow_anti {j k : ℕ} (h : k ≤ j) : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ k := by
  have e : ∀ n : ℕ, (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
    intro n
    rw [div_pow, one_pow]
  rw [e j, e k]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- Dyadic decomposition of the capped reciprocal phase weights, any finset. -/
theorem sum_capped_dyadic (S : Finset ℕ) (J : ℕ) (α Y : ℝ) (hY : 1 ≤ Y) (hJ : Y + 1 ≤ 2 ^ J) :
    (∑ h ∈ S, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
      ≤ ∑ j ∈ range J, (2 : ℝ) ^ j *
          (((S).filter
            (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j)).card : ℝ) := by
  classical
  have hterm : ∀ h : ℕ, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|)))
      ≤ ∑ j ∈ range J, (2 : ℝ) ^ j *
          (if |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0) := by
    intro h
    set d : ℝ := |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| with hddef
    have hd0 : 0 ≤ d := abs_nonneg _
    have hd1 : d ≤ 1 / 2 := abs_sub_round _
    have hpos : (0 : ℝ) < 1 / 2 := by norm_num
    by_cases hc : α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ)
    · have hdz : d = 0 := by rw [hddef, sub_eq_zero.mpr hc, abs_zero]
      rw [if_pos hc]
      have hdeq : |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| = d := hddef.symm
      have hall : (∑ j ∈ range J, (2 : ℝ) ^ j *
          (if |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0))
          = ∑ j ∈ range J, (2 : ℝ) ^ j := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j := by
          rw [hdeq, hdz]
          positivity
        rw [if_pos hj, mul_one]
      rw [hall, geom_two]
      linarith
    · rw [if_neg hc]
      have hdpos : 0 < d := by
        rw [hddef]
        exact abs_pos.mpr (sub_ne_zero.mpr hc)
      by_cases hbig : 2 * (1 / 2 : ℝ) ^ J ≤ d
      · have hJwit : (1 / 2 : ℝ) ^ J ≤ d := by
          have := pow_pos hpos J
          linarith
        have hex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j ≤ d := ⟨J, hJwit⟩
        let k := Nat.find hex
        have hk1 : (1 / 2 : ℝ) ^ k ≤ d := Nat.find_spec hex
        have hk2 : ∀ j, j < k → d < (1 / 2 : ℝ) ^ j := by
          intro j hj
          have := Nat.find_min hex hj
          linarith
        have hkJ : k ≤ J := Nat.find_min' hex hJwit
        have hkpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · exfalso
            rw [h] at hk1
            simp at hk1
            linarith
          · exact h
        have hfilter : (range J).filter (fun j => d < (1 / 2 : ℝ) ^ j) = range k := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hj, hlt⟩
            by_contra hge
            push_neg at hge
            have hmono : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ k := half_pow_anti hge
            linarith
          · intro hj
            exact ⟨by omega, hk2 j hj⟩
        have hsum_eq : (∑ j ∈ range J, (2 : ℝ) ^ j *
            (if |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0))
            = 2 ^ k - 1 := by
          rw [show |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| = d from hddef.symm]
          rw [show (∑ j ∈ range J, (2 : ℝ) ^ j *
              (if d < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0))
              = ∑ j ∈ (range J).filter (fun j => d < (1 / 2 : ℝ) ^ j), (2 : ℝ) ^ j from ?_]
          · rw [hfilter, geom_two]
          · rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : d < (1 / 2 : ℝ) ^ j <;> simp [hj]
        rw [hsum_eq]
        have hpk : 1 / d ≤ 2 ^ k := by
          rw [div_le_iff₀ hdpos]
          have h2 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
            rw [← mul_pow]
            norm_num
          nlinarith [hk1, pow_pos (by norm_num : (0 : ℝ) < 2) k, pow_pos hpos k, h2]
        have hk1' : (1 : ℝ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num)
        have hkw : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [show k = k - 1 + 1 by omega]
          rw [pow_succ]
          ring
        have hfac1 : 1 / (2 * d) ≤ 2 ^ k - 1 := by
          have heq : 1 / (2 * d) = (1 / d) / 2 := by field_simp
          rw [heq]
          nlinarith [hpk, hk1', hkw]
        have hfac1' : min Y (1 / (2 * d)) ≤ 2 ^ k - 1 := by
          rcases le_total Y (1 / (2 * d)) with h | h
          · rw [min_eq_left h]
            have h3 : 2 * Y ≤ 1 / d := by
              rw [le_div_iff₀ hdpos]
              have hmem : Y * (2 * d) ≤ 1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mp h
              nlinarith [hmem]
            have h4 : 2 * Y ≤ 2 ^ k := h3.trans hpk
            nlinarith [h4, hk1', hkw]
          · rw [min_eq_right h]
            exact hfac1
        exact hfac1'
      · -- all indicators are one
        have hdall : ∀ j, j < J → d < (1 / 2 : ℝ) ^ j := by
          intro j hj
          have hmono : (1 / 2 : ℝ) ^ (J - 1) ≤ (1 / 2 : ℝ) ^ j := half_pow_anti (by omega)
          have hJ1 : (1 / 2 : ℝ) ^ (J - 1) = 2 * (1 / 2 : ℝ) ^ J := by
            rcases Nat.eq_zero_or_pos J with h | h
            · omega
            · conv_lhs => rw [show J - 1 = J - 1 + 0 from rfl]
              rcases Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0) with ⟨n, hn⟩
              rw [hn, Nat.succ_sub_one, pow_succ]
              ring
          push_neg at hbig
          rw [hJ1] at hmono
          linarith
        have hall : (∑ j ∈ range J, (2 : ℝ) ^ j *
            (if |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0))
            = ∑ j ∈ range J, (2 : ℝ) ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos (hdall j (Finset.mem_range.mp hj)), mul_one]
        rw [hall, geom_two]
        have hYle : Y ≤ 2 ^ J - 1 := by linarith
        exact le_trans (min_le_left _ _) hYle
  calc (∑ h ∈ S, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
      ≤ ∑ h ∈ S, ∑ j ∈ range J, (2 : ℝ) ^ j *
          (if |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun h _ => hterm h)
    _ = ∑ j ∈ range J, (2 : ℝ) ^ j *
          (∑ h ∈ S,
            (if |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ = ∑ j ∈ range J, (2 : ℝ) ^ j *
          (((S).filter
            (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro h _
        by_cases hp : |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j <;> simp [hp]



/-- One block of at most `q/2` consecutive integers contributes `2^J + 4qJ`. -/
theorem block_sum (α : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hcop : Nat.Coprime a.natAbs q) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2)
    (B : Finset ℕ)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → |(x : ℝ) - (y : ℝ)| < (q : ℝ) / 2)
    (Y : ℝ) (hY : 1 ≤ Y) (J : ℕ) (hJ : Y + 1 ≤ 2 ^ J) :
    (∑ h ∈ B, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
      ≤ 2 ^ J + 4 * (q : ℝ) * J := by
  refine (sum_capped_dyadic B J α Y hY hJ).trans ?_
  have hterm : ∀ j ∈ range J,
      (2 : ℝ) ^ j * (((B.filter
          (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j)).card : ℝ))
        ≤ (2 : ℝ) ^ j + 4 * (q : ℝ) := by
    intro j _
    have hr : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
    have hc := card_dist_block α a q hq hcop happ B hB ((1 / 2 : ℝ) ^ j) hr
    have h1 : (2 : ℝ) ^ j * (((B.filter
        (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j)).card : ℝ))
        ≤ (2 : ℝ) ^ j * (1 + 4 * (q : ℝ) * (1 / 2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have h2 : (2 : ℝ) ^ j * (1 + 4 * (q : ℝ) * (1 / 2 : ℝ) ^ j)
        = (2 : ℝ) ^ j + 4 * (q : ℝ) := by
      have hsp := two_pow_half_pow j
      calc (2 : ℝ) ^ j * (1 + 4 * (q : ℝ) * (1 / 2 : ℝ) ^ j)
          = (2 : ℝ) ^ j + 4 * (q : ℝ) * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) := by ring
        _ = (2 : ℝ) ^ j + 4 * (q : ℝ) := by rw [hsp]; ring
    linarith [h1, h2.le, h2.ge]
  calc (∑ j ∈ range J, (2 : ℝ) ^ j * (((B.filter
        (fun h : ℕ => |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)| < (1 / 2 : ℝ) ^ j)).card : ℝ)))
      ≤ ∑ j ∈ range J, ((2 : ℝ) ^ j + 4 * (q : ℝ)) := Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ J - 1) + 4 * (q : ℝ) * J := by
        rw [Finset.sum_add_distrib, geom_two, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 2 ^ J + 4 * (q : ℝ) * J := by
        have h0 : (0 : ℝ) ≤ 4 * (q : ℝ) * J := by positivity
        linarith

/-- **Vaughan's Lemma 2.2 bound**, block-separation form. -/
theorem recip_sum :
    ∀ (X Y : ℝ) (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ X → 1 ≤ Y → 0 < q →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ h ∈ Icc 1 ⌊X⌋₊, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
          else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
        ≤ 60 * (1 + Real.log X + Real.log Y) * (X + Y + (q : ℝ) + X * Y / (q : ℝ)) := by
  intro X Y α a q hX hY hq hcop happ
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  set M : ℝ := 1 + Real.log X + Real.log Y with hM
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  obtain ⟨J, hJ1, hJmin⟩ : ∃ J : ℕ, Y + 1 ≤ (2 : ℝ) ^ J ∧ ∀ k, k < J → ¬ (Y + 1 ≤ (2 : ℝ) ^ k) := by
    have hex : ∃ n : ℕ, Y + 1 ≤ (2 : ℝ) ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Y + 1) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, hn.le⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hpow_bound : (2 : ℝ) ^ J ≤ 4 * Y := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]; norm_num; linarith
    · have hprev : ¬ (Y + 1 ≤ (2 : ℝ) ^ (J - 1)) := hJmin (J - 1) (by omega)
      have hlt : (2 : ℝ) ^ (J - 1) < Y + 1 := lt_of_not_ge hprev
      have hJ1 : J = (J - 1) + 1 := by omega
      have hstep : (2 : ℝ) ^ J = 2 * (2 : ℝ) ^ (J - 1) := by
        conv_lhs => rw [hJ1]
        rw [pow_succ]
        ring
      rw [hstep]; linarith
  have hJlog : (J : ℝ) ≤ 4 * (1 + Real.log Y) := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (J : ℝ) * Real.log 2 ≤ Real.log (4 * Y) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
      have h2 := Real.log_le_log hpos hpow_bound
      rwa [Real.log_pow] at h2
    have h3 : Real.log (4 * Y) = 2 * Real.log 2 + Real.log Y := by
      rw [Real.log_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.log_pow]
      push_cast; ring
    rw [h3] at h1
    have h4 : (J : ℝ) ≤ 2 + Real.log Y / Real.log 2 := by
      rw [show (2 : ℝ) + Real.log Y / Real.log 2 = (2 * Real.log 2 + Real.log Y) / Real.log 2 by
        field_simp; try ring]
      rw [le_div_iff₀ hlog2pos]; linarith
    have h5 : Real.log Y / Real.log 2 ≤ 2 * Real.log Y := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hlogY, Real.log_two_gt_d9]
    linarith
  rcases Nat.eq_or_lt_of_le (show 1 ≤ q by omega) with hq1 | hq2
  · -- the trivial denominator
    subst hq1
    have hterm : ∀ h ∈ Icc 1 ⌊X⌋₊, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))) ≤ Y := by
      intro h _
      by_cases hc : α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ)
      · rw [if_pos hc]
      · rw [if_neg hc]; exact min_le_left _ _
    have hb : (∑ h ∈ Icc 1 ⌊X⌋₊, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|)))) ≤ (⌊X⌋₊ : ℝ) * Y := by
      calc _ ≤ ∑ _h ∈ Icc 1 ⌊X⌋₊, Y := Finset.sum_le_sum hterm
        _ = (⌊X⌋₊ : ℝ) * Y := by simp
    have hbase : X * Y ≤ X + Y + ((1 : ℕ) : ℝ) + X * Y / ((1 : ℕ) : ℝ) := by
      push_cast
      rw [div_one]; linarith
    have hXY : (⌊X⌋₊ : ℝ) * Y ≤ X * Y :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hX0) hY0
    have hbig : (1 : ℝ) ≤ 60 * M := by nlinarith
    calc _ ≤ (⌊X⌋₊ : ℝ) * Y := hb
      _ ≤ X * Y := hXY
      _ ≤ X + Y + ((1 : ℕ) : ℝ) + X * Y / ((1 : ℕ) : ℝ) := hbase
      _ ≤ 60 * M * (X + Y + ((1 : ℕ) : ℝ) + X * Y / ((1 : ℕ) : ℝ)) := by
          have h0 : (0 : ℝ) ≤ X + Y + ((1 : ℕ) : ℝ) + X * Y / ((1 : ℕ) : ℝ) := by positivity
          nlinarith [hbig, h0]
  · -- a genuine denominator: fibre into blocks of `q/2` consecutive integers
    set N : ℕ := ⌊X⌋₊ with hN
    set L : ℕ := q / 2 with hLdef
    have hL1 : 1 ≤ L := by omega
    have hLle : (L : ℝ) ≤ (q : ℝ) / 2 := by
      have h := Nat.cast_div_le (α := ℝ) (m := q) (n := 2)
      simpa [hLdef] using h
    have hLge : (q : ℝ) / 3 ≤ (L : ℝ) := by
      have h1 : q ≤ 3 * L := by omega
      have h2 : (q : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast h1
      linarith
    have hNL : (N : ℝ) ≤ X := by rw [hN]; exact Nat.floor_le hX0
    have hfiber_sep : ∀ x ∈ Icc 1 N, ∀ y ∈ Icc 1 N, x / L = y / L → x ≠ y →
        |(x : ℝ) - (y : ℝ)| < (q : ℝ) / 2 := by
      intro x _ y _ hxy _
      have hxmod : x % L < L := Nat.mod_lt _ (by omega)
      have hymod : y % L < L := Nat.mod_lt _ (by omega)
      have hxe : x = L * (x / L) + x % L := (Nat.div_add_mod x L).symm
      have hye : y = L * (y / L) + y % L := (Nat.div_add_mod y L).symm
      have hx' : (x : ℝ) = (L : ℝ) * ((x / L : ℕ) : ℝ) + ((x % L : ℕ) : ℝ) := by
        conv_lhs => rw [hxe]
        push_cast
        ring
      have hy' : (y : ℝ) = (L : ℝ) * ((y / L : ℕ) : ℝ) + ((y % L : ℕ) : ℝ) := by
        conv_lhs => rw [hye]
        push_cast
        ring
      have hdiff : (x : ℝ) - (y : ℝ) = ((x % L : ℕ) : ℝ) - ((y % L : ℕ) : ℝ) := by
        rw [hx', hy', hxy]; ring
      rw [hdiff, abs_lt]
      have h1 : ((x % L : ℕ) : ℝ) < (L : ℝ) := by exact_mod_cast hxmod
      have h3 : ((y % L : ℕ) : ℝ) < (L : ℝ) := by exact_mod_cast hymod
      constructor <;> linarith
    have hmaps : ∀ h ∈ Icc 1 N, h / L ∈ (Icc 1 N).image (fun h : ℕ => h / L) :=
      fun h hh => Finset.mem_image_of_mem (fun h : ℕ => h / L) hh
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Icc 1 N)
      (t := (Icc 1 N).image (fun h : ℕ => h / L)) (g := fun h : ℕ => h / L)
      (f := fun h => (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
          else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|)))) hmaps
    have hcard : ((Icc 1 N).image (fun h : ℕ => h / L)).card ≤ N / L + 1 := by
      have hsub : (Icc 1 N).image (fun h : ℕ => h / L) ⊆ Finset.range (N / L + 1) := by
        intro k hk
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hk
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp hh).2)
      calc ((Icc 1 N).image (fun h : ℕ => h / L)).card
          ≤ (Finset.range (N / L + 1)).card := Finset.card_le_card hsub
        _ = N / L + 1 := Finset.card_range _
    have hmain : (∑ h ∈ Icc 1 N, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
        ≤ (((N / L : ℕ) : ℝ) + 1) * (2 ^ J + 4 * (q : ℝ) * J) := by
      rw [← hfib]
      calc (∑ k ∈ (Icc 1 N).image (fun h : ℕ => h / L),
            ∑ h ∈ (Icc 1 N).filter (fun h : ℕ => h / L = k),
              (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
                else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
          ≤ ∑ _k ∈ (Icc 1 N).image (fun h : ℕ => h / L), (2 ^ J + 4 * (q : ℝ) * J) := by
            apply Finset.sum_le_sum
            intro k _
            exact block_sum α a q hq2 hcop happ _
              (fun x hx y hy hxy => hfiber_sep x (Finset.mem_filter.mp hx).1
                y (Finset.mem_filter.mp hy).1
                (by rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]) hxy)
              Y hY J hJ1
        _ = (((Icc 1 N).image (fun h : ℕ => h / L)).card : ℝ) * (2 ^ J + 4 * (q : ℝ) * J) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (((N / L : ℕ) : ℝ) + 1) * (2 ^ J + 4 * (q : ℝ) * J) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard
    have hNL2 : ((N / L : ℕ) : ℝ) + 1 ≤ 3 * X / (q : ℝ) + 1 := by
      have h1 : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / (L : ℝ) := Nat.cast_div_le
      have h2 : (N : ℝ) / (L : ℝ) ≤ X / (L : ℝ) :=
        div_le_div_of_nonneg_right hNL (by positivity)
      have h3 : X / (L : ℝ) ≤ X / ((q : ℝ) / 3) :=
        div_le_div_of_nonneg_left hX0 (by positivity) hLge
      have h4 : X / ((q : ℝ) / 3) = 3 * X / (q : ℝ) := by field_simp; try ring
      linarith
    have h2J : (2 : ℝ) ^ J + 4 * (q : ℝ) * J ≤ 4 * Y + 16 * (q : ℝ) * M := by
      have h1 : 4 * (q : ℝ) * (J : ℝ) ≤ 16 * (q : ℝ) * M := by
        have hJ' : (J : ℝ) ≤ 4 * M := by rw [hM]; linarith
        nlinarith [hqR, hJ']
      nlinarith [hpow_bound, h1]
    have key : (3 * X / (q : ℝ) + 1) * (4 * Y + 16 * (q : ℝ) * M)
        ≤ 60 * M * (X + Y + (q : ℝ) + X * Y / (q : ℝ)) := by
      have hXY : (0 : ℝ) ≤ X * Y / (q : ℝ) := by positivity
      have k1 : 12 * (X * Y / (q : ℝ)) ≤ 60 * M * (X * Y / (q : ℝ)) := by
        nlinarith [hXY, hM1]
      have k2 : 48 * X * M ≤ 60 * M * X := by nlinarith [hX0, hM1]
      have k3 : 4 * Y ≤ 60 * M * Y := by nlinarith [hY0, hM1]
      have k4 : 16 * (q : ℝ) * M ≤ 60 * M * (q : ℝ) := by nlinarith [hqR, hM1]
      have e1 : (3 * X / (q : ℝ) + 1) * (4 * Y + 16 * (q : ℝ) * M)
          = 12 * (X * Y / (q : ℝ)) + 48 * X * M + 4 * Y + 16 * (q : ℝ) * M := by
        field_simp
        ring
      have e2 : 60 * M * (X + Y + (q : ℝ) + X * Y / (q : ℝ))
          = 60 * M * X + 60 * M * Y + 60 * M * (q : ℝ) + 60 * M * (X * Y / (q : ℝ)) := by
        ring
      rw [e1, e2]
      linarith [k1, k2, k3, k4]
    calc (∑ h ∈ Icc 1 N, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
        else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|))))
        = (∑ h ∈ Icc 1 ⌊X⌋₊, (if α * (h : ℝ) = (round (α * (h : ℝ)) : ℝ) then Y
            else min Y (1 / (2 * |α * (h : ℝ) - (round (α * (h : ℝ)) : ℝ)|)))) := by rw [hN]
      _ ≤ (((N / L : ℕ) : ℝ) + 1) * (2 ^ J + 4 * (q : ℝ) * J) := hmain
      _ ≤ (3 * X / (q : ℝ) + 1) * (4 * Y + 16 * (q : ℝ) * M) := by
          apply mul_le_mul hNL2 h2J (by positivity) (by positivity)
      _ ≤ 60 * M * (X + Y + (q : ℝ) + X * Y / (q : ℝ)) := key

/-- LEAF. Page 482 equation 8, normalized by H to the k.
Vaughan 1981 Lemma 2.2 supplies the rational linear sum estimate. -/
theorem leaf_light (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree)
    (c D : ℝ) (hc : 0 < c) (hD : 0 < D) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      1 / H + divisorCost F c N H D α false ≤
        C * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
          Real.log N ^ (D + 1) :=
  leaf_light_of_recip_sum F hk c D hc hD ⟨60, by norm_num, recip_sum⟩

/-- The light cost has a trivial logarithmic bound for every phase. -/
theorem lightCost_trivial (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hL : 0 < Real.log N) :
    divisorCost F c N H D α false ≤ 2 * c * Real.log N ^ D := by
  classical
  let k := F.natDegree
  let s := (Icc 1 ⌊c * H ^ (k - 1)⌋₊).filter
    (fun h => (divisorCount k h : ℝ) ≤ Real.log N ^ D)
  have hH0 : 0 < H := by linarith
  have hcard : (s.card : ℝ) ≤ c * H ^ (k - 1) := by
    calc
      _ ≤ ((Icc 1 ⌊c * H ^ (k - 1)⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (⌊c * H ^ (k - 1)⌋₊ : ℝ) := by simp
      _ ≤ _ := Nat.floor_le (by positivity)
  have hterm : ∀ h ∈ s, (divisorCount k h : ℝ) * linearEnvelope H (α * h) ≤
      Real.log N ^ D * (H + 1) := by
    intro h hh
    have ht := (Finset.mem_filter.mp hh).2
    exact mul_le_mul ht (linearEnvelope_le H (α * h) (by linarith))
      (linearEnvelope_nonneg _ _) (Real.rpow_nonneg hL.le _)
  have hsum : (∑ h ∈ s, (divisorCount k h : ℝ) * linearEnvelope H (α * h)) ≤
      c * H ^ (k - 1) * (Real.log N ^ D * (H + 1)) := by
    calc
      _ ≤ ∑ _h ∈ s, Real.log N ^ D * (H + 1) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (Real.log N ^ D * (H + 1)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hrel : H ^ k = H ^ (k - 1) * H := by
    conv_lhs => rw [show k = k - 1 + 1 by dsimp [k]; omega, pow_succ]
  change (∑ h ∈ s, (divisorCount k h : ℝ) * linearEnvelope H (α * h)) / H ^ k ≤ _
  apply (div_le_iff₀ (pow_pos hH0 k)).mpr
  rw [hrel]
  have ht : 0 ≤ c * H ^ (k - 1) * Real.log N ^ D := by positivity
  nlinarith

/-- The light rational estimate is elementary whenever its rational factor is at least one. -/
theorem lightCost_of_large_factor (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hD : 0 < D) (hL : 1 ≤ Real.log N)
    (R : ℝ) (hR : 1 ≤ R) :
    1 / H + divisorCost F c N H D α false ≤
      (2 * c + 1) * R * Real.log N ^ (D + 1) := by
  have hL0 : 0 < Real.log N := by linarith
  have ht := lightCost_trivial F hk c N H D α hc hH hL0
  have hHp : 0 < H := by linarith
  have hHinv : 1 / H ≤ 1 := (div_le_one hHp).mpr hH
  have hpow : 1 ≤ Real.log N ^ D := Real.one_le_rpow hL hD.le
  have hpow' : Real.log N ^ D ≤ Real.log N ^ (D + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc
    _ ≤ (2 * c + 1) * Real.log N ^ D := by nlinarith
    _ ≤ (2 * c + 1) * Real.log N ^ (D + 1) := mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ ≤ _ := by
      have hh := mul_nonneg (sub_nonneg.mpr hR)
        (show 0 ≤ (2 * c + 1) * Real.log N ^ (D + 1) by positivity)
      nlinarith

/-- Denominators at least H to the k satisfy the light estimate by the trivial bound. -/
theorem lightCost_large_denominator (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hD : 0 < D) (hL : 1 ≤ Real.log N)
    (q : ℕ) (hq : H ^ F.natDegree ≤ (q : ℝ)) :
    1 / H + divisorCost F c N H D α false ≤
      (2 * c + 1) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
        Real.log N ^ (D + 1) := by
  apply lightCost_of_large_factor F hk c N H D α hc hH hD hL
  have hHp : 0 < H := by linarith
  have hratio : 1 ≤ (q : ℝ) / H ^ F.natDegree := (le_div_iff₀ (pow_pos hHp _)).mpr (by simpa using hq)
  have ha : 0 ≤ 1 / (q : ℝ) := by positivity
  have hb : 0 ≤ 1 / H := by positivity
  linarith

/-- The denominator one case of the light estimate requires no rational approximation. -/
theorem lightCost_denominator_one (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hD : 0 < D) (hL : 1 ≤ Real.log N) :
    1 / H + divisorCost F c N H D α false ≤
      (2 * c + 1) * (1 + 1 / H + 1 / H ^ F.natDegree) * Real.log N ^ (D + 1) := by
  apply lightCost_of_large_factor F hk c N H D α hc hH hD hL
  have h1 : 0 ≤ 1 / H := by positivity
  have h2 : 0 ≤ 1 / H ^ F.natDegree := by positivity
  linarith

/-- The existing rational separation estimate transfers to the linear envelope. -/
theorem linearEnvelope_scaled_rational (H α : ℝ) (hH : 1 ≤ H) (a : ℤ) (q h : ℕ)
    (hq : 0 < q) (hh : 0 < h) (hcop : Nat.Coprime a.natAbs q)
    (happ : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    linearEnvelope H (α * h) ≤ 2 * h * ((H + 1) / q + q) := by
  unfold linearEnvelope
  apply csSup_le
  · exact ⟨0, 0, 0, by norm_num; linarith, by simp [Kernel.T]⟩
  · rintro x ⟨start, len, hlen, rfl⟩
    have hb := norm_T_le_scaled_rational start len h hh a q hq hcop happ
    rw [mul_comm α (h : ℝ)]
    exact hb.trans (by gcongr)

/-- Termwise rational separation gives this weaker light bound.
The sum of h loses a power and does not prove the required equation 8. -/
theorem lightCost_scaled_rational (F : ℤ[X]) (c N H D α : ℝ)
    (hH : 1 ≤ H) (hL : 0 < Real.log N) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime a.natAbs q) (happ : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    divisorCost F c N H D α false ≤
      (Real.log N ^ D * 2 * ((H + 1) / q + q) *
        ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊, (h : ℝ)) / H ^ F.natDegree := by
  classical
  let s := Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊
  have hH0 : 0 < H := by linarith
  unfold divisorCost
  simp only [Bool.false_eq_true, ite_false]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ h ∈ s.filter (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
        Real.log N ^ D * (2 * h * ((H + 1) / q + q)) := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp hh
      have hh0 : 0 < h := (Finset.mem_Icc.mp hs).1
      exact mul_le_mul ht (linearEnvelope_scaled_rational H α hH a q h hq hh0 hcop happ)
        (linearEnvelope_nonneg _ _) (Real.rpow_nonneg hL.le _)
    _ ≤ ∑ h ∈ s, Real.log N ^ D * (2 * h * ((H + 1) / q + q)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring

end
end LeanLab.Perelli1996.Decomp103b
