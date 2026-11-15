module

public import LeanLab.Tolev2009.SeriesIdentification

/-!
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 12 to 14, finite coefficient multiplicativity.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.CRT355
open LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.SeriesIdentification

/-- Halupczok page 13, CRT splits the restricted coefficient residue set. -/
theorem coeffRes_crt_image (k l m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : Nat.Coprime m n) :
    (coeffRes k l (m * n)).image (fun r => (r % m, r % n)) =
      (coeffRes k l m) ×ˢ (coeffRes k l n) := by
  ext u
  constructor
  · intro hu
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hu
    rcases mem_filter.mp hr with ⟨hr, hcop, hmod⟩
    apply mem_product.mpr
    constructor
    · simp only [coeffRes, mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ (by omega), ?_, ?_⟩
      · exact (coprime_modEq m (r % m) r (Nat.mod_mod _ _)).mpr
          (hcop.coprime_dvd_right (dvd_mul_right m n))
      · rw [Nat.mod_mod_of_dvd r (Nat.gcd_dvd_right k m)]
        exact Nat.ModEq.of_dvd (Nat.gcd_dvd_gcd_mul_right_right k m n) hmod
    · simp only [coeffRes, mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ (by omega), ?_, ?_⟩
      · exact (coprime_modEq n (r % n) r (Nat.mod_mod _ _)).mpr
          (hcop.coprime_dvd_right (dvd_mul_left n m))
      · rw [Nat.mod_mod_of_dvd r (Nat.gcd_dvd_right k n)]
        exact Nat.ModEq.of_dvd (Nat.gcd_dvd_gcd_mul_left_right k n m) hmod
  · rcases u with ⟨x, y⟩
    intro hu
    rcases mem_product.mp hu with ⟨hx, hy⟩
    rcases mem_filter.mp hx with ⟨hx, hcx, hxm⟩
    rcases mem_filter.mp hy with ⟨hy, hcy, hym⟩
    let r := Nat.chineseRemainder hmn x y
    have hrm : (r : ℕ) ≡ x [MOD m] := r.property.1
    have hrn : (r : ℕ) ≡ y [MOD n] := r.property.2
    have hcm : Nat.Coprime (r : ℕ) m := (coprime_modEq m _ _ hrm).mpr hcx
    have hcn : Nat.Coprime (r : ℕ) n := (coprime_modEq n _ _ hrn).mpr hcy
    refine mem_image.mpr ⟨r, ?_, ?_⟩
    · simp only [coeffRes, mem_filter, mem_range]
      refine ⟨Nat.chineseRemainder_lt_mul hmn x y (by omega) (by omega), hcm.mul_right hcn, ?_⟩
      rw [hmn.gcd_mul k]
      apply (Nat.modEq_and_modEq_iff_modEq_mul
        ((hmn.coprime_dvd_left (Nat.gcd_dvd_right k m)).coprime_dvd_right (Nat.gcd_dvd_right k n))).mp
      exact ⟨(hrm.of_dvd (Nat.gcd_dvd_right k m)).trans hxm,
        (hrn.of_dvd (Nat.gcd_dvd_right k n)).trans hym⟩
    · apply Prod.ext
      · exact (show (r : ℕ) % m = x % m from hrm).trans (Nat.mod_eq_of_lt (mem_range.mp hx))
      · exact (show (r : ℕ) % n = y % n from hrn).trans (Nat.mod_eq_of_lt (mem_range.mp hy))

/-- Halupczok page 13, CRT projection is injective on reduced coefficient representatives. -/
theorem coeffRes_crt_inj (k l m n : ℕ) (hmn : Nat.Coprime m n) :
    Set.InjOn (fun r => (r % m, r % n)) (coeffRes k l (m * n)) := by
  intro r hr s hs he
  have hm := congrArg Prod.fst he
  have hn := congrArg Prod.snd he
  have h := Nat.mod_lcm hm hn
  rw [hmn.lcm_eq_mul] at h
  exact h.eq_of_lt_of_lt (mem_range.mp (mem_filter.mp hr).1) (mem_range.mp (mem_filter.mp hs).1)

/-- Halupczok page 13, Proposition 1 for the literal restricted coefficient sum. -/
theorem coeff_crt (k l m n a b : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : Nat.Coprime m n) :
    coeff k l (m * n) (a * n + b * m) = coeff k l m a * coeff k l n b := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hphase (r : ℕ) : ee (((a * n + b * m : ℕ) : ℝ) * r / (m * n : ℕ)) =
      ee ((a : ℝ) * (r % m : ℕ) / m) * ee ((b : ℝ) * (r % n : ℕ) / n) := by
    rw [← ee_rat_mod a r m hm, ← ee_rat_mod b r n hn, ← ee_add]
    congr 1
    push_cast
    field_simp
    <;> ring
  calc
    _ = ∑ r ∈ coeffRes k l (m * n),
        ee ((a : ℝ) * (r % m : ℕ) / m) * ee ((b : ℝ) * (r % n : ℕ) / n) := by
      exact sum_congr rfl (fun r _ => hphase r)
    _ = ∑ u ∈ (coeffRes k l (m * n)).image (fun r => (r % m, r % n)),
        ee ((a : ℝ) * u.1 / m) * ee ((b : ℝ) * u.2 / n) :=
      (sum_image (f := fun u : ℕ × ℕ => ee ((a : ℝ) * u.1 / m) * ee ((b : ℝ) * u.2 / n))
        (coeffRes_crt_inj k l m n hmn)).symm
    _ = ∑ u ∈ (coeffRes k l m) ×ˢ (coeffRes k l n),
        ee ((a : ℝ) * u.1 / m) * ee ((b : ℝ) * u.2 / n) := by
      rw [coeffRes_crt_image k l m n hm hn hmn]
    _ = _ := by
      simp only [sum_product, coeff, sum_mul, mul_sum]
      rw [sum_comm]

/-- Halupczok page 14, the linear CRT parametrization of the outer reduced residues is injective. -/
theorem linear_crt_inj (m n : ℕ) (hmn : Nat.Coprime m n) :
    Set.InjOn (fun u : ℕ × ℕ => (u.1 * n + u.2 * m) % (m * n))
      ((((range m).filter (fun a => Nat.Coprime a m)) ×ˢ
        ((range n).filter (fun b => Nat.Coprime b n))) : Finset (ℕ × ℕ)) := by
  intro u hu v hv he
  have hu' := mem_product.mp hu
  have hv' := mem_product.mp hv
  have H : u.1 * n + u.2 * m ≡ v.1 * n + v.2 * m [MOD m * n] := he
  have Hm : u.1 * n ≡ v.1 * n [MOD m] := by
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod,
      add_zero, Nat.mod_mod] using H.of_mul_right n
  have Hn : u.2 * m ≡ v.2 * m [MOD n] := by
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod,
      zero_add, Nat.mod_mod] using H.of_mul_left m
  apply Prod.ext
  · exact (Nat.ModEq.cancel_right_of_coprime hmn Hm).eq_of_lt_of_lt
      (mem_range.mp (mem_filter.mp hu'.1).1) (mem_range.mp (mem_filter.mp hv'.1).1)
  · exact (Nat.ModEq.cancel_right_of_coprime hmn.symm Hn).eq_of_lt_of_lt
      (mem_range.mp (mem_filter.mp hu'.2).1) (mem_range.mp (mem_filter.mp hv'.2).1)

/-- Halupczok page 14, every outer reduced residue has a linear CRT representative. -/
theorem linear_crt_image (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    ((((range m).filter (fun a => Nat.Coprime a m)) ×ˢ
        ((range n).filter (fun b => Nat.Coprime b n))).image
      (fun u : ℕ × ℕ => (u.1 * n + u.2 * m) % (m * n))) =
      (range (m * n)).filter (fun a => Nat.Coprime a (m * n)) := by
  have hsub : ((((range m).filter (fun a => Nat.Coprime a m)) ×ˢ
        ((range n).filter (fun b => Nat.Coprime b n))).image
      (fun u : ℕ × ℕ => (u.1 * n + u.2 * m) % (m * n))) ⊆
      (range (m * n)).filter (fun a => Nat.Coprime a (m * n)) := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    rcases mem_product.mp hu with ⟨hu, hv⟩
    have hum := (mem_filter.mp hu).2
    have hun := (mem_filter.mp hv).2
    have hcm : Nat.Coprime (u.1 * n + u.2 * m) m := by
      simpa only [Nat.coprime_add_mul_right_left] using hum.mul_left hmn.symm
    have hcn : Nat.Coprime (u.1 * n + u.2 * m) n := by
      simpa only [Nat.coprime_mul_right_add_left] using hun.mul_left hmn
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
    exact (coprime_modEq (m * n) _ _ (Nat.mod_mod _ _)).mpr (hcm.mul_right hcn)
  have hcard (q : ℕ) : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    simp only [Nat.totient_eq_card_coprime, Nat.coprime_comm]
  apply eq_of_subset_of_card_le hsub
  rw [card_image_of_injOn (linear_crt_inj m n hmn), card_product,
    hcard m, hcard n, hcard (m * n), Nat.totient_mul hmn]

/-- Halupczok pages 12 to 14, changing an integer numerator modulo q preserves the coefficient. -/
theorem coeff_frequency_mod (k l q a : ℕ) (hq : 1 ≤ q) :
    coeff k l q (a % q) = coeff k l q a := by
  apply sum_congr rfl
  intro r hr
  simpa only [mul_comm] using (ee_rat_mod r a q hq).symm

/-- Halupczok page 14, the negative outer phase depends only on its reduced numerator. -/
theorem negative_phase_mod (N a q : ℕ) (hq : 1 ≤ q) :
    ee (-(((a % q : ℕ) : ℝ) * N / q)) = ee (-((a : ℝ) * N / q)) := by
  have H : ee (((a % q : ℕ) : ℝ) * N / q) = ee ((a : ℝ) * N / q) := by
    simpa only [mul_comm] using (ee_rat_mod N a q hq).symm
  have hneg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
    unfold ee
    rw [show 2 * (π : ℂ) * Complex.I * (-x : ℝ) = -(2 * π * Complex.I * x) by push_cast; ring,
      Complex.exp_neg]
  rw [hneg, hneg, H]

/-- Halupczok page 11, b of q before the three totient ratios are inserted. -/
noncomputable def numerator (k l : Fin 3 → ℕ) (N q : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ee (-((a : ℝ) * N / q)) * ∏ i : Fin 3, coeff (k i) (l i) q a

/-- Halupczok page 14, Proposition 2 for the full finite numerator. -/
theorem numerator_mul (k l : Fin 3 → ℕ) (N m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    numerator k l N (m * n) = numerator k l N m * numerator k l N n := by
  have hq : 1 ≤ m * n := by nlinarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hterm (u : ℕ × ℕ) :
      ee (-((((u.1 * n + u.2 * m) % (m * n) : ℕ) : ℝ) * N / (m * n : ℕ))) *
        (∏ i : Fin 3, coeff (k i) (l i) (m * n) ((u.1 * n + u.2 * m) % (m * n))) =
      (ee (-((u.1 : ℝ) * N / m)) * ∏ i : Fin 3, coeff (k i) (l i) m u.1) *
        (ee (-((u.2 : ℝ) * N / n)) * ∏ i : Fin 3, coeff (k i) (l i) n u.2) := by
    rw [negative_phase_mod N _ _ hq]
    simp_rw [coeff_frequency_mod _ _ _ _ hq, coeff_crt _ _ _ _ _ _ hm hn hmn]
    have he : ee (-(((u.1 * n + u.2 * m : ℕ) : ℝ) * N / (m * n : ℕ))) =
        ee (-((u.1 : ℝ) * N / m)) * ee (-((u.2 : ℝ) * N / n)) := by
      rw [← ee_add]
      congr 1
      push_cast
      field_simp
      <;> ring
    rw [he, prod_mul_distrib]
    ring
  unfold numerator
  rw [← linear_crt_image m n hm hn hmn, sum_image (linear_crt_inj m n hmn)]
  simp_rw [hterm]
  simp only [sum_product, sum_mul, mul_sum]
  rw [sum_comm]

/-- Halupczok page 16, the lcm totient ratios are multiplicative in a coprime denominator. -/
theorem totient_lcm_product (k m n : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : Nat.Coprime m n) :
    k.totient * (Nat.lcm k (m * n)).totient =
      (Nat.lcm k m).totient * (Nat.lcm k n).totient := by
  let f : ArithmeticFunction ℕ := ⟨Nat.totient, by simp⟩
  have hf : f.IsMultiplicative := ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  have H (q : ℕ) : (Nat.lcm k q).totient * (Nat.gcd k q).totient = k.totient * q.totient :=
    hf.lcm_apply_mul_gcd_apply
  have hgc : Nat.Coprime (Nat.gcd k m) (Nat.gcd k n) :=
    (hmn.coprime_dvd_left (Nat.gcd_dvd_right k m)).coprime_dvd_right (Nat.gcd_dvd_right k n)
  have Hmn := H (m * n)
  rw [hmn.gcd_mul k, Nat.totient_mul hgc, Nat.totient_mul hmn] at Hmn
  have hGm : 0 < (Nat.gcd k m).totient :=
    Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left m hk)
  have hGn : 0 < (Nat.gcd k n).totient :=
    Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left n hk)
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hGm hGn)
  calc
    _ = k.totient * ((Nat.lcm k (m * n)).totient *
        ((Nat.gcd k m).totient * (Nat.gcd k n).totient)) := by ring
    _ = k.totient * (k.totient * (m.totient * n.totient)) := by rw [Hmn]
    _ = ((Nat.lcm k m).totient * (Nat.gcd k m).totient) *
        ((Nat.lcm k n).totient * (Nat.gcd k n).totient) := by rw [H m, H n]; ring
    _ = _ := by ring

/-- Halupczok page 16, the complex totient normalization respects the same CRT product. -/
theorem normalization_mul (k m n : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : Nat.Coprime m n) :
    ((k.totient : ℂ) / (Nat.lcm k (m * n)).totient) =
      ((k.totient : ℂ) / (Nat.lcm k m).totient) *
        ((k.totient : ℂ) / (Nat.lcm k n).totient) := by
  have H : (k.totient : ℂ) * (Nat.lcm k (m * n)).totient =
      (Nat.lcm k m).totient * (Nat.lcm k n).totient := by
    exact_mod_cast totient_lcm_product k m n hk hm hn hmn
  have hφ (q : ℕ) (hq : 1 ≤ q) : ((Nat.lcm k q).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos hk hq)).ne'
  field_simp [hφ m hm, hφ n hn, hφ (m * n) (by nlinarith)]
  linear_combination -(k.totient : ℂ) * H

/-- Halupczok page 11, recover the exact explicit coefficient from its finite numerator. -/
theorem ssTerm_factor (k l : Fin 3 → ℕ) (N q : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) (hq : 1 ≤ q) :
    ssTerm k l N q = (∏ i : Fin 3, ((k i).totient : ℂ) / (Nat.lcm (k i) q).totient) *
      numerator k l N q := by
  rw [ssTerm_eq_halupczokTerm k l N q hk hq hl]
  simp only [halupczokTerm, numerator, coeffPaper_eq_coeff _ _ _ _ hq]

/-- Halupczok pages 14 and 16, the full explicit coefficient is multiplicative. -/
theorem ssTerm_mul (k l : Fin 3 → ℕ) (N m n : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    ssTerm k l N (m * n) = ssTerm k l N m * ssTerm k l N n := by
  rw [ssTerm_factor k l N (m * n) hk hl (by nlinarith), ssTerm_factor k l N m hk hl hm,
    ssTerm_factor k l N n hk hl hn, numerator_mul k l N m n hm hn hmn]
  simp_rw [normalization_mul _ _ _ (hk _) hm hn hmn]
  rw [prod_mul_distrib]
  ring

end LeanLab.Tolev2009.CRT355
