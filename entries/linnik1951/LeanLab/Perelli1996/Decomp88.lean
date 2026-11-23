module

public import LeanLab.Perelli1996.Section2
public import LeanLab.Perelli1996.Kernel17
public import LeanLab.Perelli1996.Farey
public import LeanLab.Perelli1996.LocalBounds88
public import LeanLab.Perelli1996.Linear88
public import LeanLab.Perelli1996.Decomp103
public import LeanLab.Perelli1996.Decomp103b
public import LeanLab.Perelli1996.Character632

/-!
P0083 Perelli 1996, Section 2, pages 480 through 486.
Theorem 1 is assembled from explicit analytic leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Decomp88
open Finset Real Polynomial MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- The large N geometry needed for equations 16 and 17, from the orders on page 480. -/
theorem arc_parameters (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ)
    (hε : 0 < ε) (hB : 0 < B) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      Real.log N ^ B / N ≤ 1 / 2 ∧ 2 ≤ fareyOrder F N H B := by
  have ht1 := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have ht2 := (isLittleO_log_rpow_rpow_atTop (B / 4) (by norm_num : (0 : ℝ) < 1 / 3)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp ht1
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp ht2
  refine ⟨max 3 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hb1 := hN₁ N (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hb2 := hN₂ N (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le B),
    Real.rpow_one, abs_of_pos hN0] at hb1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le (B / 4)),
    abs_of_nonneg (Real.rpow_nonneg hN0.le (1 / 3))] at hb2
  refine ⟨(div_le_iff₀ hN0).mpr (by linarith), ?_⟩
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF.1)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hpow : N ^ ((1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree) ≤ H ^ F.natDegree := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hH F.natDegree
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hN0.le] at h
  have hbase : (1 : ℝ) / 3 ≤ (1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree := by
    have hid : 1 / (3 * (F.natDegree : ℝ)) * F.natDegree = (1 : ℝ) / 3 := by field_simp
    rw [add_mul, hid]
    have := mul_pos hε hk
    linarith
  have hlow := (Real.rpow_le_rpow_of_exponent_le hN1 hbase).trans hpow
  have harg : 16 ≤ H ^ F.natDegree * Real.log N ^ (-B / 4) := by
    have hL : 0 < Real.log N ^ (B / 4) := Real.rpow_pos_of_pos hlog _
    have hratio : 16 ≤ H ^ F.natDegree / Real.log N ^ (B / 4) := by
      apply (le_div_iff₀ hL).mpr
      linarith
    rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hlog.le, ← div_eq_mul_inv]
    exact hratio
  unfold fareyOrder
  have hs : 4 ≤ Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact harg)
  linarith

/-- LEAF. Page 480 before equation 1. The polynomial is positive and bounded by c N
on the full window for large N. This is an elementary cutoff statement. -/
theorem leaf_cutoff (F : ℤ[X]) (hF : Admissible F) :
    ∃ c N₀ : ℝ, 0 < c ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) → ∀ n ∈ win F N H,
      0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊ := by
  let G : ℝ[X] := F.map (Int.castRingHom ℝ)
  have hinj : Function.Injective (Int.castRingHom ℝ) := (Int.castRingHom ℝ).injective_int
  have hdeg : G.natDegree = F.natDegree := natDegree_map_eq_of_injective hinj F
  have hlc : G.leadingCoeff = (F.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj F
  have ha : (0 : ℝ) < F.leadingCoeff := by exact_mod_cast hF.2
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF.1)
  have hE := (Polynomial.isEquivalent_atTop_lead (P := G)).isLittleO.bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hE
  have ht := (tendsto_rpow_atTop (one_div_pos.mpr hk)).eventually
    (Filter.eventually_ge_atTop (max X 1))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp ht
  let c : ℝ := 2 * (F.leadingCoeff : ℝ) * 2 ^ F.natDegree
  refine ⟨c, max 3 N₁, by dsimp [c]; positivity, le_max_left _ _, ?_⟩
  intro N H hN hH hHu n hn
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  let x := N ^ (1 / (F.natDegree : ℝ))
  have hx : max X 1 ≤ x := hN₁ N (le_trans (le_max_right _ _) hN)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hnlo : x ≤ (n : ℝ) := (Nat.le_ceil x).trans (by
    exact_mod_cast (Finset.mem_Icc.mp hn).1)
  have hnhi : (n : ℝ) ≤ 2 * x := by
    have hnf : (n : ℝ) ≤ ⌊x + H⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hfl := Nat.floor_le (show 0 ≤ x + H by positivity)
    linarith
  have hn1 : (1 : ℝ) ≤ n := (le_trans (le_max_right _ _) hx).trans hnlo
  have hb := hX (n : ℝ) ((le_trans (le_max_left _ _) hx).trans hnlo)
  rw [hdeg, hlc] at hb
  have hev : G.eval (n : ℝ) = (Fv F n : ℝ) := by
    simp [G, Fv, Polynomial.eval_map]
  simp only [Pi.sub_apply, hev, Real.norm_eq_abs] at hb
  have hv : 0 < (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by positivity
  rw [abs_of_pos hv] at hb
  have hb' := abs_le.mp hb
  have hposR : (0 : ℝ) ≤ Fv F n := by linarith
  have hpos : 0 ≤ Fv F n := by exact_mod_cast hposR
  refine ⟨hpos, Nat.le_floor ?_⟩
  have hxn : x ^ F.natDegree = N := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    rw [one_div_mul_cancel (ne_of_gt hk), Real.rpow_one]
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ n by positivity) hnhi F.natDegree
  rw [mul_pow, hxn] at hpow
  have hupper : (Fv F n : ℝ) ≤ 2 * (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by
    linarith
  have hnat : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hpos
  rw [hnat]
  calc (Fv F n : ℝ) ≤ 2 * (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := hupper
    _ ≤ 2 * (F.leadingCoeff : ℝ) * (2 ^ F.natDegree * N) := by gcongr
    _ = c * N := by dsimp [c]; ring

/-- LEAF. Page 480 equation 1, finite Fourier orthogonality.
The cutoff includes both summands of each representation. -/
theorem leaf_fourier (M m : ℕ) (hm : m ≤ M) :
    (∫ α in Set.Icc (0 : ℝ) 1, coefficientIntegrand M m α) = (R m : ℂ) := by
  classical
  have he (z : ℤ) : (∫ α in Set.Icc (0 : ℝ) 1, Kernel.e ((z : ℝ) * α)) =
      if z = 0 then 1 else 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    by_cases hz : z = 0
    · simp [hz, Kernel.e]
    · rw [if_neg hz]
      have heq : (fun α : ℝ => Kernel.e ((z : ℝ) * α)) =
          fun α : ℝ => Complex.exp (((z : ℂ) * (2 * Real.pi * Complex.I)) * α) := by
        funext α
        unfold Kernel.e
        congr 1
        push_cast
        ring
      rw [heq, integral_exp_mul_complex]
      · simp [Complex.exp_int_mul_two_pi_mul_I]
      · apply mul_ne_zero
        · exact_mod_cast hz
        · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hterm (p q : ℕ) :
      (∫ α in Set.Icc (0 : ℝ) 1,
        ((Λ p : ℂ) * Kernel.e ((p : ℝ) * α)) *
        ((Λ q : ℂ) * Kernel.e ((q : ℝ) * α)) * Kernel.e (-(m : ℝ) * α)) =
      if p + q = m then ((Λ p * Λ q : ℝ) : ℂ) else 0 := by
    have heq (α : ℝ) :
        ((Λ p : ℂ) * Kernel.e ((p : ℝ) * α)) *
        ((Λ q : ℂ) * Kernel.e ((q : ℝ) * α)) * Kernel.e (-(m : ℝ) * α) =
        ((Λ p * Λ q : ℝ) : ℂ) * Kernel.e ((((p : ℤ) + q - m : ℤ) : ℝ) * α) := by
      unfold Kernel.e
      push_cast
      rw [show (Λ p : ℂ) * Complex.exp (Complex.I * (2 * Real.pi * ((p : ℂ) * α))) *
          ((Λ q : ℂ) * Complex.exp (Complex.I * (2 * Real.pi * ((q : ℂ) * α)))) *
          Complex.exp (Complex.I * (2 * Real.pi * (-(m : ℂ) * α))) =
          (Λ p : ℂ) * (Λ q : ℂ) *
          (Complex.exp (Complex.I * (2 * Real.pi * ((p : ℂ) * α))) *
          Complex.exp (Complex.I * (2 * Real.pi * ((q : ℂ) * α))) *
          Complex.exp (Complex.I * (2 * Real.pi * (-(m : ℂ) * α)))) by ring]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring
    simp_rw [heq]
    rw [integral_const_mul, he]
    have hz : ((p : ℤ) + q - m = 0) ↔ p + q = m := by omega
    rw [if_congr hz rfl rfl]
    split_ifs <;> simp
  have hexpand (α : ℝ) : coefficientIntegrand M m α =
      ∑ p ∈ range (M + 1), ∑ q ∈ range (M + 1),
        ((Λ p : ℂ) * Kernel.e ((p : ℝ) * α)) *
        ((Λ q : ℂ) * Kernel.e ((q : ℝ) * α)) * Kernel.e (-(m : ℝ) * α) := by
    unfold coefficientIntegrand primeSum
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hint (p q : ℕ) : IntegrableOn (fun α : ℝ =>
      ((Λ p : ℂ) * Kernel.e ((p : ℝ) * α)) *
      ((Λ q : ℂ) * Kernel.e ((q : ℝ) * α)) * Kernel.e (-(m : ℝ) * α))
      (Set.Icc 0 1) volume := by
    apply Continuous.integrableOn_Icc
    unfold Kernel.e
    fun_prop
  have hi (p : ℕ) :
      (∫ α in Set.Icc (0 : ℝ) 1, ∑ q ∈ range (M + 1),
        ((Λ p : ℂ) * Kernel.e ((p : ℝ) * α)) *
        ((Λ q : ℂ) * Kernel.e ((q : ℝ) * α)) * Kernel.e (-(m : ℝ) * α)) =
      ∑ q ∈ range (M + 1), ∫ α in Set.Icc (0 : ℝ) 1,
        ((Λ p : ℂ) * Kernel.e ((p : ℝ) * α)) *
        ((Λ q : ℂ) * Kernel.e ((q : ℝ) * α)) * Kernel.e (-(m : ℝ) * α) :=
    integral_finsetSum _ (fun q _ => hint p q)
  simp_rw [hexpand]
  rw [integral_finsetSum]
  · simp_rw [hi]
    simp_rw [hterm]
    have hinner (p : ℕ) : (∑ q ∈ range (M + 1),
        if p + q = m then ((Λ p * Λ q : ℝ) : ℂ) else 0) =
        if p ≤ m then ((Λ p * Λ (m - p) : ℝ) : ℂ) else 0 := by
      by_cases hp : p ≤ m
      · rw [if_pos hp]
        rw [Finset.sum_eq_single (m - p)]
        · simp [Nat.add_sub_of_le hp]
        · intro q hq hne
          rw [if_neg (by omega)]
        · intro hnot
          have hmem : m - p ∈ range (M + 1) := Finset.mem_range.mpr (by omega)
          exact (hnot hmem).elim
      · rw [if_neg hp]
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg (by omega)]
    simp_rw [hinner]
    have hsum : (∑ p ∈ range (M + 1),
        if p ≤ m then ((Λ p * Λ (m - p) : ℝ) : ℂ) else 0) =
        ∑ p ∈ range (m + 1), ((Λ p * Λ (m - p) : ℝ) : ℂ) := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hm 1))]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [if_pos (by have := Finset.mem_range.mp hp; omega)]
      · intro p hp hpnot
        rw [if_neg (by simp only [Finset.mem_range] at hpnot; omega)]
    rw [hsum]
    unfold R
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    push_cast
    rfl
  · intro p hp
    exact integrable_finsetSum _ (fun q _ => hint p q)

/-- LEAF. Page 480 equation 1, splitting the coefficient integral and squaring. -/
theorem leaf_split (F : ℤ[X]) (M : ℕ) (N H B : ℝ)
    (hcut : ∀ n ∈ win F N H, (Fv F n).toNat ≤ M) :
    ∑ n ∈ win F N H, Delta F n ^ 2 ≤
      2 * majorError F M N H B + 2 * minorError F M N H B := by
  classical
  have hmeas : MeasurableSet (majorArcs N B) := by
    unfold majorArcs
    measurability
  unfold majorError minorError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  let f := coefficientIntegrand M (Fv F n).toNat
  have hf : Continuous f := by
    unfold f coefficientIntegrand primeSum Kernel.e
    fun_prop
  have hfi : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume := hf.integrableOn_Icc
  have hi := integral_inter_add_sdiff hmeas hfi
  have hfour := leaf_fourier M (Fv F n).toNat (hcut n hn)
  rw [hfour] at hi
  let a := (∫ α in Set.Icc 0 1 ∩ majorArcs N B, f α) -
    ((Fv F n : ℝ) * Sing (Fv F n).toNat : ℂ)
  let b := ∫ α in minorArcs N B, f α
  have heq : ((Delta F n : ℝ) : ℂ) = a + b := by
    dsimp [a, b, minorArcs, Delta]
    push_cast
    linear_combination -hi
  have hnorm := norm_add_le a b
  have hsq := pow_le_pow_left₀ (norm_nonneg (a + b)) hnorm 2
  have hbound : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hdelta : Delta F n ^ 2 = ‖a + b‖ ^ 2 := by
    rw [← heq]
    simp
  rw [hdelta]
  exact hbound

/-- LEAF. Page 481 equation 4. The c exponent depends on F.
Inputs are Vaughan Chapter 3 for equation 2 and Nair 1992 for equation 4. -/
theorem leaf_major (F : ℤ[X]) (hF : Admissible F) (c : ℝ) (hc : 0 < c) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ A ε B : ℝ, 0 < A → 0 < ε → 0 < B →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      majorError F ⌊c * N⌋₊ N H B ≤
        C * H * N ^ 2 * (Real.log N ^ (-2 * B + d) + Real.log N ^ (-A)) := by
  exact Decomp103.major F hF c hc

/-- LEAF. Pages 481 through 483 equations 5 through 14.
Parseval, the Weyl lemma and Farey separation reduce the minor mean square
 to the largest local prime second moment. -/
theorem leaf_minor_reduction (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (c : ℝ) (hc : 0 < c)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      minorError F ⌊c * N⌋₊ N H B ≤
        C * H * N * Real.log N ^ (B / 2 + 1) *
          localMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        C * H * N ^ 2 * Real.log N ^
          (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F)) := by
  obtain ⟨NP, hNP, hp⟩ := arc_parameters F hF ε B hε hB
  exact Decomp103.minor F hF hW c hc ε B hε hB
    ⟨NP, hNP, fun N H hN hH => (hp N H hN hH).2⟩


/-- LEAF. Pages 483 through 485 equations 14 through 17 and 25.
The kernel bound of task60 and the character remainder control every punctured arc. -/
theorem leaf_local_mass (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B)
    (hR : ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤ C * N * Real.log N ^ (-B)) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      localMass ⌊c * N⌋₊ N B (fareyOrder F N H B) ≤ C * N * Real.log N ^ (-B) := by
  classical
  obtain ⟨CR, NR, hCR, hNR, hrem⟩ := hR
  obtain ⟨NP, hNP, hparam⟩ := arc_parameters F hF ε B hε hB
  refine ⟨8 * (c + 1) + 2 * CR, max NR NP, by positivity, le_trans hNR (le_max_left _ _), ?_⟩
  intro N H hN hH hHu
  have hNRN := le_trans (le_max_left NR NP) hN
  have hNPN := le_trans (le_max_right NR NP) hN
  have hN3 : 3 ≤ N := hNR.trans hNRN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  let P := Real.log N ^ B
  let Q := fareyOrder F N H B
  let M := ⌊c * N⌋₊
  have hP : 0 < P := Real.rpow_pos_of_pos hlog _
  obtain ⟨hradius, hQ⟩ := hparam N H hNPN hH
  have hQ0 : 0 < Q := by dsimp [Q]; linarith
  have hM : ((M + 1 : ℕ) : ℝ) ≤ (c + 1) * N := by
    have hf := Nat.floor_le (show 0 ≤ c * N by positivity)
    dsimp [M]
    push_cast
    linarith
  have hmmajor : MeasurableSet (majorArcs N B) := by unfold majorArcs; measurability
  unfold localMass
  apply csSup_le
  · refine ⟨∫ α in puncturedArc N B Q 1 0, ‖primeSum M α‖ ^ 2, 1, by norm_num, ?_, 0, by norm_num, rfl⟩
    norm_num only [Nat.cast_one]
    linarith
  · rintro x ⟨q, hq, hqQ, a, hcop, rfl⟩
    let t : ℝ := (a : ℝ) / q
    let δ : ℝ := 1 / ((q : ℝ) * Q)
    let s : Set ℝ := {η | t + η ∈ puncturedArc N B Q q a}
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδhalf : δ ≤ 1 / 2 := by
      dsimp [δ]
      apply (div_le_iff₀ (by positivity : 0 < (q : ℝ) * Q)).mpr
      have hQ2 : 2 ≤ Q := hQ
      nlinarith
    have hms : MeasurableSet (puncturedArc N B Q q a) := measurableSet_Icc.diff hmmajor
    have hs : MeasurableSet s := hms.preimage (measurable_const.add measurable_id)
    have hsub : s ⊆ Set.Icc (-δ) δ := by
      intro η hη
      obtain ⟨⟨hl, hu⟩, _⟩ := hη
      change (a : ℝ) / q - δ ≤ t + η at hl
      change t + η ≤ (a : ℝ) / q + δ at hu
      dsimp [t] at hl hu
      constructor <;> linarith
    have hgap : (q : ℝ) ≤ P → ∀ η ∈ s, P / N ≤ |η| := by
      intro hqP η hη
      apply le_of_lt
      apply lt_of_not_ge
      intro hsmall
      apply hη.2
      refine ⟨q, hq, hqP, a, hcop, ?_⟩
      change |t + η - (a : ℝ) / q| ≤ P / N
      simpa [t] using hsmall
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hz : ‖((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ)‖ ≤ 1 / (q.totient : ℝ) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ hφ.le
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have hf : Continuous (fun η : ℝ => primeSum M (t + η)) := by
      unfold primeSum Kernel.e
      fun_prop
    have hr : Continuous (characterRemainder M q a) := by
      unfold characterRemainder primeSum Kernel.T Kernel.e
      fun_prop
    have hdecomp (η : ℝ) : primeSum M (t + η) =
        ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η +
          characterRemainder M q a η := by
      unfold characterRemainder
      dsimp [t]
      ring
    have hrr := hrem N H hNRN hH hHu q hq hqQ a hcop
    have hb := LocalBounds88.second_moment_subset (M + 1) q
      (fun η => primeSum M (t + η)) (characterRemainder M q a)
      ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ)
      hs hf hr hq hP hN0 (show 1 ≤ c + 1 by linarith) hM hradius hδ.le hδhalf hsub hgap hz hdecomp hrr
    rw [LocalBounds88.translate_setIntegral _ hms _ t]
    change (∫ η in s, ‖primeSum M (t + η)‖ ^ 2) ≤ _
    refine hb.trans_eq ?_
    dsimp [P]
    rw [Real.rpow_neg hlog.le]
    ring

end
end LeanLab.Perelli1996.Decomp88
