module

public import LeanLab.Perelli1996.Section2
public import LeanLab.Perelli1996.Farey

/-!
P0083, page 482, the degree one case of the Weyl input.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Section2
open Finset Real Polynomial
noncomputable section

/-- The linear kernel under a reduced rational approximation, page 482 degree one case. -/
theorem norm_T_le_rational (start M : ℕ) {α : ℝ} (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖Kernel.T start M α‖ ≤ (M : ℝ) / q + q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hq1 : q = 1
  · subst q
    simpa using (Kernel.norm_T_le start M α).trans (by linarith : (M : ℝ) ≤ M / 1 + 1)
  have hq2 : 2 ≤ q := by omega
  have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hne : (a : ℝ) / q ≠ (round α : ℝ) := by
    intro heq
    have hm : (a : ℝ) = (round α : ℝ) * q := (div_eq_iff hqR.ne').mp heq
    have hmZ : a = round α * (q : ℤ) := by exact_mod_cast hm
    have hd : (q : ℤ) ∣ a := ⟨round α, by rw [hmZ]; ring⟩
    have hdN : q ∣ a.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
    exact hq1 (Nat.eq_one_of_dvd_coprimes hcop hdN (dvd_refl q))
  have hsep := Farey.rational_separation a (round α) q 1 hq (by norm_num) (by simpa using hne)
  norm_num only [Nat.cast_one, mul_one, div_one] at hsep
  have htri := abs_sub_le ((a : ℝ) / q) α (round α : ℝ)
  have happ : |(a : ℝ) / q - α| ≤ 1 / (q : ℝ) ^ 2 := by simpa [abs_sub_comm] using happrox
  have hsmall : 1 / (q : ℝ) ^ 2 ≤ 1 / (2 * (q : ℝ)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hqR) (by positivity)).mpr
    nlinarith
  have hfrac : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by field_simp
  have hdist : 1 / (2 * (q : ℝ)) ≤ |α - (round α : ℝ)| := by linarith
  have hdist0 : 0 < |α - (round α : ℝ)| := lt_of_lt_of_le (by positivity) hdist
  have hα : α ≠ (round α : ℝ) := sub_ne_zero.mp (abs_pos.mp hdist0)
  have hk := (Kernel.norm_T_le_min start M hα).trans (min_le_right _ _)
  have hlast : 1 / (2 * |α - (round α : ℝ)|) ≤ (q : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * |α - (round α : ℝ)|)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mp hdist
    nlinarith
  have hnon : 0 ≤ (M : ℝ) / q := by positivity
  exact (hk.trans hlast).trans (by linarith)

/-- The cited Weyl lemma is elementary for the polynomial X, page 482. -/
theorem weyl_X : WeylLemma (X : ℤ[X]) := by
  intro _ D hD
  refine ⟨2, Real.exp 1 + 3, by norm_num, by have := Real.exp_pos 1; linarith, ?_⟩
  intro N H α hN hH hHu a q hq hcop happ
  have hN0 : 0 < N := by have := Real.exp_pos 1; linarith
  have hlog : 1 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ N by linarith)
    simpa using hh
  have hlog0 : 0 ≤ Real.log N := by linarith
  let x : ℝ := N ^ (1 / ((X : ℤ[X]).natDegree : ℝ))
  let lo := ⌈x⌉₊
  let hi := ⌊x + H⌋₊
  let M := hi + 1 - lo
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hlo : x ≤ (lo : ℝ) := Nat.le_ceil _
  have hhi : (hi : ℝ) ≤ x + H := Nat.floor_le (by positivity)
  have hM : (M : ℝ) ≤ H + 1 := by
    by_cases hb : lo ≤ hi + 1
    · dsimp [M]
      rw [Nat.cast_sub hb]
      push_cast
      linarith
    · have hz : M = 0 := by dsimp [M]; omega
      rw [hz]
      simp only [Nat.cast_zero]
      linarith
  have hkernel : polynomialKernel (X : ℤ[X]) N H α = Kernel.T lo M α := by
    unfold polynomialKernel win Kernel.T
    simp only [Fv, Polynomial.eval_X, Int.cast_natCast]
    change (∑ n ∈ Icc lo hi, Kernel.e ((n : ℝ) * α)) =
      ∑ n ∈ range M, Kernel.e (((lo + n : ℕ) : ℝ) * α)
    have hset : Icc lo hi = Ico lo (hi + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
  have hnorm := norm_T_le_rational lo M a q hq hcop happ
  rw [hkernel]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hH0 : 0 < H := by linarith
  have hM2 : (M : ℝ) ≤ 2 * H := by linarith
  have hpow : 1 ≤ Real.log N ^ (D + 1) := Real.one_le_rpow hlog (by linarith)
  have herr : 0 ≤ Real.log N ^ (-2 * D - 1) := Real.rpow_nonneg hlog0 _
  simp only [Polynomial.natDegree_X, weylExponent, Nat.sub_self, pow_zero,
    Nat.cast_one, mul_one, one_div_one, Real.rpow_one, pow_one, div_one]
  calc ‖Kernel.T lo M α‖ ≤ (M : ℝ) / q + q := hnorm
    _ ≤ 2 * H / q + q := by gcongr
    _ ≤ 2 * H * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H + Real.log N ^ (-2 * D + 1 ^ 2 - 2)) := by
      have heq : 2 * H * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H + Real.log N ^ (-2 * D + 1 ^ 2 - 2)) =
          2 * H / q + 2 + 2 * q + 2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2) := by field_simp <;> ring
      rw [heq]
      have hpow0 : 0 ≤ Real.log N ^ (-2 * D + 1 ^ 2 - 2) := Real.rpow_nonneg hlog0 _
      have hrest : (q : ℝ) ≤ 2 + 2 * q + 2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2) := by
        nlinarith [mul_nonneg hH0.le hpow0]
      calc 2 * H / q + q ≤ 2 * H / q + (2 + 2 * q + 2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2)) :=
          add_le_add le_rfl hrest
        _ = _ := by ring
    _ ≤ 2 * H * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H + Real.log N ^ (-2 * D + 1 ^ 2 - 2)) *
        Real.log N ^ (D + 1) := by
      have hn : 0 ≤ 2 * H * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H + Real.log N ^ (-2 * D + 1 ^ 2 - 2)) := by positivity
      nlinarith

/-- The linear rational kernel bound for every positive integral slope, page 482. -/
theorem norm_T_le_scaled_rational (start M l : ℕ) (hl : 0 < l) {α : ℝ}
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖Kernel.T start M ((l : ℝ) * α)‖ ≤ 2 * l * ((M : ℝ) / q + q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  by_cases hsmall : q ≤ 2 * l
  · have hqle : (q : ℝ) ≤ 2 * l := by exact_mod_cast hsmall
    have hm : (M : ℝ) ≤ 2 * l * ((M : ℝ) / q) := by
      apply (mul_le_mul_iff_left₀ hqR).mp
      have hid : (2 * l * ((M : ℝ) / q)) * q = 2 * l * M := by field_simp
      rw [hid]
      nlinarith [mul_nonneg (Nat.cast_nonneg M) (sub_nonneg.mpr hqle)]
    refine (Kernel.norm_T_le start M _).trans ?_
    have hh : 0 ≤ 2 * (l : ℝ) * q := by positivity
    nlinarith only [hm, hh]
  have hbig : 2 * l < q := by omega
  have hqle : 2 * (l : ℝ) ≤ q := by exact_mod_cast hbig.le
  let β := (l : ℝ) * α
  have hne : (((l : ℤ) * a : ℤ) : ℝ) / q ≠ (round β : ℝ) := by
    intro heq
    have hm : (((l : ℤ) * a : ℤ) : ℝ) = (round β : ℝ) * q := (div_eq_iff hqR.ne').mp heq
    have hmZ : (l : ℤ) * a = round β * (q : ℤ) := by exact_mod_cast hm
    have hd : (q : ℤ) ∣ (l : ℤ) * a := ⟨round β, by rw [hmZ]; ring⟩
    have hdN : q ∣ l * a.natAbs := by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
    have hql : q ∣ l := hcop.symm.dvd_of_dvd_mul_right hdN
    have hqlle := Nat.le_of_dvd hl hql
    omega
  have hsep := Farey.rational_separation ((l : ℤ) * a) (round β) q 1 hq (by norm_num) (by simpa using hne)
  norm_num only [Nat.cast_one, mul_one, div_one] at hsep
  have happ : |(((l : ℤ) * a : ℤ) : ℝ) / q - β| ≤ (l : ℝ) / (q : ℝ) ^ 2 := by
    have hid : (((l : ℤ) * a : ℤ) : ℝ) / q - β = (l : ℝ) * ((a : ℝ) / q - α) := by
      dsimp [β]
      push_cast
      ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
    have hh : |(a : ℝ) / q - α| ≤ 1 / (q : ℝ) ^ 2 := by simpa [abs_sub_comm] using happrox
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg l)
  have hsmallR : (l : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (2 * (q : ℝ)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hqR) (by positivity)).mpr
    nlinarith
  have htri := abs_sub_le ((((l : ℤ) * a : ℤ) : ℝ) / q) β (round β : ℝ)
  have hfrac : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by field_simp
  have hdist : 1 / (2 * (q : ℝ)) ≤ |β - (round β : ℝ)| := by linarith
  have hdist0 : 0 < |β - (round β : ℝ)| := lt_of_lt_of_le (by positivity) hdist
  have hβ : β ≠ (round β : ℝ) := sub_ne_zero.mp (abs_pos.mp hdist0)
  have hk := (Kernel.norm_T_le_min start M hβ).trans (min_le_right _ _)
  have hlast : 1 / (2 * |β - (round β : ℝ)|) ≤ (q : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * |β - (round β : ℝ)|)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mp hdist
    nlinarith
  have hn : 0 ≤ (M : ℝ) / q := by positivity
  have hbound : (q : ℝ) ≤ 2 * l * ((M : ℝ) / q + q) := by
    have hh := mul_nonneg (show 0 ≤ 2 * (l : ℝ) - 1 by linarith) hqR.le
    have hm := mul_nonneg (show 0 ≤ 2 * (l : ℝ) by positivity) hn
    nlinarith
  exact (hk.trans hlast).trans hbound

/-- The exact Weyl lemma for every affine polynomial of positive integral slope, page 482. -/
theorem weyl_affine (l : ℕ) (hl : 0 < l) (b : ℤ) :
    WeylLemma (C (l : ℤ) * X + C b) := by
  let F : ℤ[X] := C (l : ℤ) * X + C b
  change WeylLemma F
  have hdeg : F.natDegree = 1 := Polynomial.natDegree_linear (by exact_mod_cast hl.ne')
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  intro _ D hD
  refine ⟨4 * l, Real.exp 1 + 3, by positivity, by have := Real.exp_pos 1; linarith, ?_⟩
  intro N H α hN hH hHu a q hq hcop happ
  have hN0 : 0 < N := by have := Real.exp_pos 1; linarith
  have hlog : 1 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ N by linarith)
    simpa using hh
  have hlog0 : 0 ≤ Real.log N := by linarith
  let x : ℝ := N ^ (1 / (F.natDegree : ℝ))
  let lo := ⌈x⌉₊
  let hi := ⌊x + H⌋₊
  let M := hi + 1 - lo
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hlo : x ≤ (lo : ℝ) := Nat.le_ceil _
  have hhi : (hi : ℝ) ≤ x + H := Nat.floor_le (by positivity)
  have hM : (M : ℝ) ≤ H + 1 := by
    by_cases hb : lo ≤ hi + 1
    · dsimp [M]
      rw [Nat.cast_sub hb]
      push_cast
      linarith
    · have hz : M = 0 := by dsimp [M]; omega
      rw [hz]
      simp only [Nat.cast_zero]
      linarith
  have hkernel : ‖polynomialKernel F N H α‖ = ‖Kernel.T lo M ((l : ℝ) * α)‖ := by
    have heq : polynomialKernel F N H α =
        Kernel.e ((b : ℝ) * α) * Kernel.T lo M ((l : ℝ) * α) := by
      unfold polynomialKernel win Kernel.T
      change (∑ n ∈ Icc lo hi, Kernel.e ((Fv F n : ℝ) * α)) =
        Kernel.e ((b : ℝ) * α) * ∑ n ∈ range M,
          Kernel.e (((lo + n : ℕ) : ℝ) * ((l : ℝ) * α))
      have hset : Icc lo hi = Ico lo (hi + 1) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hset, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Fv, F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      unfold Kernel.e
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [heq, norm_mul]
    simp [Kernel.e, Complex.norm_exp]
  have hnorm := norm_T_le_scaled_rational lo M l hl a q hq hcop happ
  rw [hkernel]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hH0 : 0 < H := by linarith
  have hM2 : (M : ℝ) ≤ 2 * H := by linarith
  have hpow : 1 ≤ Real.log N ^ (D + 1) := Real.one_le_rpow hlog (by linarith)
  simp only [weylExponent, hdeg, Nat.sub_self, pow_zero, Nat.cast_one, Real.rpow_one, pow_one, div_one]
  let J := 1 / (q : ℝ) + 1 / H + (q : ℝ) / H + Real.log N ^ (-2 * D + 1 ^ 2 - 2)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hbase : (M : ℝ) / q + q ≤ 2 * H * J := by
    have heq : 2 * H * J = 2 * H / q + 2 + 2 * q +
        2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2) := by dsimp [J]; field_simp <;> ring
    rw [heq]
    have hpart : (M : ℝ) / q ≤ 2 * H / q := div_le_div_of_nonneg_right hM2 hqR.le
    have hrest : (q : ℝ) ≤ 2 + 2 * q + 2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2) := by
      have hnon : 0 ≤ 2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2) := by positivity
      linarith
    calc (M : ℝ) / q + q ≤ 2 * H / q + (2 + 2 * q + 2 * H * Real.log N ^ (-2 * D + 1 ^ 2 - 2)) :=
        add_le_add hpart hrest
      _ = _ := by ring
  change ‖Kernel.T lo M ((l : ℝ) * α)‖ ≤ (4 * l) * H * J * Real.log N ^ (D + 1)
  calc ‖Kernel.T lo M ((l : ℝ) * α)‖ ≤ 2 * l * ((M : ℝ) / q + q) := hnorm
    _ ≤ 2 * l * (2 * H * J) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (4 * l) * H * J := by ring
    _ ≤ (4 * l) * H * J * Real.log N ^ (D + 1) := by
      have hnon : 0 ≤ (4 * l) * H * J := by positivity
      nlinarith

/-- Every admissible degree one polynomial satisfies the Weyl input, page 482. -/
theorem weyl_of_natDegree_one (F : ℤ[X]) (hdeg : F.natDegree = 1) : WeylLemma F := by
  intro hF
  obtain ⟨a, ha, b, heq⟩ := Polynomial.natDegree_eq_one.mp hdeg
  have hlc : F.leadingCoeff = a := by rw [← heq, Polynomial.leadingCoeff_linear ha]
  have ha0 : 0 < a := by have hh := hF.2; rwa [hlc] at hh
  let l := a.toNat
  have hl : 0 < l := by dsimp [l]; omega
  have hla : (l : ℤ) = a := Int.toNat_of_nonneg ha0.le
  have hW := weyl_affine l hl b
  have hrep : C (l : ℤ) * X + C b = F := by rw [hla]; exact heq
  rw [hrep] at hW
  exact hW hF

end
end LeanLab.Perelli1996.Section2
