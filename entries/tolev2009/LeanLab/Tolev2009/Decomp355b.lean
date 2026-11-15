module

public import LeanLab.Tolev2009.Decomp355a
public import LeanLab.Tolev2009.Gcd355
public import LeanLab.Tolev2009.CoefficientMoment314
public import LeanLab.Tolev2009.ScalarEnvelope346
public import LeanLab.PNTPort.BV.Helpers

/-!
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 18 to 19.
The seven variable finite gcd reindexing is proved.
-/

@[expose] public section

open Finset Real
set_option maxHeartbeats 2000000
namespace LeanLab.Tolev2009.Decomp355b
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp314b LeanLab.Tolev2009.Decomp355a
open LeanLab.Tolev2009.CoefficientMoment314 LeanLab.HeathBrown1985

/-- Halupczok page 19, expand a product over the seven factor coordinates. -/
theorem seven_product (f : Fin 7 → ℝ) :
    (∏ i : Fin 7, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  norm_num [Fin.prod_univ_succ]
  <;> ring

/-- Halupczok pages 18 to 19, one reconstructed triple is bounded by seven scalar weights. -/
theorem factor_weight_le (a b c : ℕ) (t : Fin 7 → ℕ) (ht : ∀ i, 1 ≤ t i)
    (ha : a = t 0 * t 1 * t 2 * t 4) (hb : b = t 0 * t 1 * t 3 * t 5)
    (hc : c = t 0 * t 2 * t 3 * t 6)
    (hab : Nat.gcd a b = t 0 * t 1) (hac : Nat.gcd a c = t 0 * t 2)
    (hbc : Nat.gcd b c = t 0 * t 3) (hd : Nat.gcd (Nat.gcd a b) c = t 0) :
    rawWeight ![a, b, c] / ((a : ℝ) * b * c) ≤
      ((t 0).divisors.card : ℝ) ^ 12 / t 0 *
      (((t 1).divisors.card : ℝ) ^ 8 / t 1) *
      (((t 2).divisors.card : ℝ) ^ 8 / t 2) *
      (((t 3).divisors.card : ℝ) ^ 8 / t 3) *
      (((t 4).divisors.card : ℝ) ^ 4 / t 4) *
      (((t 5).divisors.card : ℝ) ^ 4 / t 5) *
      (((t 6).divisors.card : ℝ) ^ 4 / t 6) := by
  have ht0 (i : Fin 7) : (t i : ℝ) ≠ 0 := by
    exact_mod_cast (show t i ≠ 0 by have := ht i; omega)
  have hr : gcdWeight ![a, b, c] / ((a : ℝ) * b * c) =
      1 / ((t 0 : ℝ) * t 1 * t 2 * t 3 * t 4 * t 5 * t 6) := by
    change (((Nat.gcd a b : ℝ) * Nat.gcd a c * Nat.gcd b c) /
      Nat.gcd (Nat.gcd a b) c) / ((a : ℝ) * b * c) = _
    rw [hd, hab, hac, hbc]
    rw [ha, hb, hc]
    push_cast
    field_simp [ht0]
    <;> ring
  have hta := Gcd355.divisor_count_four (t 0) (t 1) (t 2) (t 4)
  have htb := Gcd355.divisor_count_four (t 0) (t 1) (t 3) (t 5)
  have htc := Gcd355.divisor_count_four (t 0) (t 2) (t 3) (t 6)
  rw [← ha] at hta
  rw [← hb] at htb
  rw [← hc] at htc
  have hT : (a.divisors.card : ℝ) ^ 4 * (b.divisors.card : ℝ) ^ 4 * (c.divisors.card : ℝ) ^ 4 ≤
      ((t 0).divisors.card : ℝ) ^ 12 * ((t 1).divisors.card : ℝ) ^ 8 *
      ((t 2).divisors.card : ℝ) ^ 8 * ((t 3).divisors.card : ℝ) ^ 8 *
      ((t 4).divisors.card : ℝ) ^ 4 * ((t 5).divisors.card : ℝ) ^ 4 *
      ((t 6).divisors.card : ℝ) ^ 4 := by
    calc
      _ ≤ ((t 0).divisors.card * (t 1).divisors.card * (t 2).divisors.card *
          (t 4).divisors.card : ℝ) ^ 4 *
          ((t 0).divisors.card * (t 1).divisors.card * (t 3).divisors.card *
          (t 5).divisors.card : ℝ) ^ 4 *
          ((t 0).divisors.card * (t 2).divisors.card * (t 3).divisors.card *
          (t 6).divisors.card : ℝ) ^ 4 := by gcongr
      _ = _ := by ring
  calc
    _ = (gcdWeight ![a, b, c] / ((a : ℝ) * b * c)) *
        ((a.divisors.card : ℝ) ^ 4 * (b.divisors.card : ℝ) ^ 4 * (c.divisors.card : ℝ) ^ 4) := by
      simp [rawWeight, Fin.prod_univ_three]
      <;> ring
    _ = ((a.divisors.card : ℝ) ^ 4 * (b.divisors.card : ℝ) ^ 4 * (c.divisors.card : ℝ) ^ 4) /
        ((t 0 : ℝ) * t 1 * t 2 * t 3 * t 4 * t 5 * t 6) := by rw [hr]; ring
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hT
        (show 0 ≤ (t 0 : ℝ) * t 1 * t 2 * t 3 * t 4 * t 5 * t 6 by positivity)
      simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hh

/-- Halupczok pages 18 to 19, the substitution q1 = dabe, q2 = dacf, q3 = dcbg.
The exact seven factor map is injective because it reconstructs the three moduli. -/
theorem gcd_reindex (N : ℕ) :
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
      rawWeight ![a, b, c] / ((a : ℝ) * b * c)) ≤
      (∑ d ∈ Icc 1 N, (d.divisors.card : ℝ) ^ 12 / d) *
        (∑ a ∈ Icc 1 N, (a.divisors.card : ℝ) ^ 8 / a) ^ 3 *
        (∑ e ∈ Icc 1 N, (e.divisors.card : ℝ) ^ 4 / e) ^ 3 := by
  classical
  let S : Finset (ℕ × ℕ × ℕ) := (Icc 1 N) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))
  have hex (u : {u : ℕ × ℕ × ℕ // u ∈ S}) :=
    Gcd355.exists_gcd_factors u.val.1 u.val.2.1 u.val.2.2
      (by have := (mem_Icc.mp (mem_product.mp u.property).1).1; omega)
      (by have := (mem_Icc.mp (mem_product.mp (mem_product.mp u.property).2).1).1; omega)
      (by have := (mem_Icc.mp (mem_product.mp (mem_product.mp u.property).2).2).1; omega)
  choose T hT using hex
  let r : Fin 7 → ℕ := ![12, 8, 8, 8, 4, 4, 4]
  let V : (Fin 7 → ℕ) → ℝ := fun t => ∏ i : Fin 7, ((t i).divisors.card : ℝ) ^ (r i) / t i
  let P := Fintype.piFinset (fun _ : Fin 7 => Icc 1 N)
  have hsub : S.attach.image T ⊆ P := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
    rcases hT u with ⟨hpos, ha, hb, hc, hab, hac, hbc, hd⟩
    have hle := Gcd355.factors_le (T u) hpos u.val.1 u.val.2.1 u.val.2.2 N ha hb hc
      (mem_Icc.mp (mem_product.mp u.property).1).2
      (mem_Icc.mp (mem_product.mp (mem_product.mp u.property).2).1).2
      (mem_Icc.mp (mem_product.mp (mem_product.mp u.property).2).2).2
    exact Fintype.mem_piFinset.mpr (fun i => mem_Icc.mpr ⟨hpos i, hle i⟩)
  have hinj : Set.InjOn T (S.attach : Set {u : ℕ × ℕ × ℕ // u ∈ S}) := by
    intro u hu v hv huv
    rcases hT u with ⟨hpu, hau, hbu, hcu, hgu⟩
    rcases hT v with ⟨hpv, hav, hbv, hcv, hgv⟩
    apply Subtype.ext
    apply Prod.ext
    · rw [hau, hav, huv]
    · apply Prod.ext
      · rw [hbu, hbv, huv]
      · rw [hcu, hcv, huv]
  calc
    _ = ∑ u ∈ S.attach, rawWeight ![u.val.1, u.val.2.1, u.val.2.2] /
        ((u.val.1 : ℝ) * u.val.2.1 * u.val.2.2) := by
      rw [Finset.sum_attach S (fun u : ℕ × ℕ × ℕ =>
        rawWeight ![u.1, u.2.1, u.2.2] / ((u.1 : ℝ) * u.2.1 * u.2.2))]
      simp only [S, sum_product]
    _ ≤ ∑ u ∈ S.attach, V (T u) := by
      apply sum_le_sum
      intro u hu
      rcases hT u with ⟨hpos, ha, hb, hc, hab, hac, hbc, hd⟩
      have hh := factor_weight_le u.val.1 u.val.2.1 u.val.2.2 (T u) hpos ha hb hc hab hac hbc hd
      change _ ≤ ∏ i : Fin 7, ((T u i).divisors.card : ℝ) ^ (r i) / T u i
      rw [seven_product]
      exact hh
    _ = ∑ t ∈ S.attach.image T, V t := (sum_image hinj).symm
    _ ≤ ∑ t ∈ P, V t := sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ =>
      prod_nonneg (fun i _ => div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)))
    _ = _ := by
      dsimp only [P, V]
      rw [Finset.sum_prod_piFinset (Icc 1 N)
        (fun (i : Fin 7) (n : ℕ) => (n.divisors.card : ℝ) ^ (r i) / n), seven_product]
      change _ * _ * _ * _ * _ * _ * _ = _
      norm_num [r]
      <;> ring

/-- Halupczok page 18, reuse the proved reciprocal totient mean to bound one denominator. -/
theorem reciprocal_totient_uniform :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      ∀ k ∈ Icc 1 N, (1 : ℝ) / k.totient ≤ D * Real.log N / k := by
  obtain ⟨C, hC, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨2 * C, by positivity, fun N hL k hk => ?_⟩
  have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  have hs : ∑ d ∈ k.divisors, LeanLab.PNTPort.BV.sqfTot d ≤ C * (1 + Real.log N) := by
    apply le_trans _ (hsum N)
    apply le_trans (sum_le_sum fun d _ => LeanLab.PNTPort.BV.sqfTot_le d)
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      have hdp := Nat.pos_of_mem_divisors hd
      have hdle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.dvd_of_mem_divisors hd)
      exact mem_Icc.mpr ⟨hdp, hdle.trans (mem_Icc.mp hk).2⟩
    · intro d _ _
      positivity
  rw [LeanLab.PNTPort.BV.inv_totient_eq hk0]
  calc
    _ ≤ (1 / (k : ℝ)) * (C * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (1 / (k : ℝ)) * (2 * C * Real.log N) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by ring

/-- Halupczok page 18, remove three totient denominators with three logarithmic losses. -/
theorem normalized_weight_le (D : ℝ) (N : ℕ) (hD : 0 ≤ D) (hL : 1 ≤ Real.log N)
    (hDk : ∀ k ∈ Icc 1 N, (1 : ℝ) / k.totient ≤ D * Real.log N / k)
    (k : Fin 3 → ℕ) (hk : ∀ i, k i ∈ Icc 1 N) :
    rawWeight k / phiProduct k ≤
      (D * Real.log N) ^ 3 * (rawWeight k / ∏ i : Fin 3, (k i : ℝ)) := by
  have hp : (∏ i : Fin 3, (1 : ℝ) / (k i).totient) ≤
      ∏ i : Fin 3, D * Real.log N / k i := by
    exact prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hDk (k i) (hk i))
  have he : ∏ i : Fin 3, D * Real.log N / (k i : ℝ) =
      (D * Real.log N) ^ 3 / ∏ i : Fin 3, (k i : ℝ) := by
    rw [prod_div_distrib]
    simp
  rw [he, prod_div_distrib] at hp
  simp only [prod_const_one, one_div] at hp
  have hh := mul_le_mul_of_nonneg_left hp (rawWeight_nonneg k)
  simpa only [phiProduct, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh

/-- Halupczok pages 18 to 19, the finite gcd envelope has a logarithmic mean.
The seven variable reindexing and reciprocal moment bounds are proved. -/
theorem normalized_weight_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ Real.log N →
      (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
        rawWeight ![a, b, c] / phiProduct ![a, b, c]) ≤ C * Real.log N ^ (4915 : ℕ) := by
  obtain ⟨D, hD, hDk⟩ := reciprocal_totient_uniform
  refine ⟨D ^ 3 * 2 ^ 4912, by positivity, fun N hL => ?_⟩
  have hL0 : 0 ≤ Real.log N := by linarith
  calc
    _ ≤ (D * Real.log N) ^ 3 *
        (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
          rawWeight ![a, b, c] / ((a : ℝ) * b * c)) := by
      simp only [mul_sum]
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      apply sum_le_sum
      intro c hc
      simpa [Fin.prod_univ_three] using normalized_weight_le D N hD hL (hDk N hL)
        ![a, b, c] (by intro i; fin_cases i <;> assumption)
    _ ≤ (D * Real.log N) ^ 3 * Hn N ^ 4912 :=
      mul_le_mul_of_nonneg_left ((gcd_reindex N).trans (seven_reciprocal_moments N)) (by positivity)
    _ ≤ (D * Real.log N) ^ 3 * (2 * Real.log N) ^ 4912 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (Hn_nonneg N) ((Hn_le N).trans (by linarith)) _
    _ = _ := by ring

/-- Halupczok page 18, the third cutoff lies in the full arithmetic averaging cube. -/
theorem cutoff3_le (B : ℝ) (N : ℕ) (hB : 0 ≤ B) (hL : 1 ≤ Real.log N) :
    Dyadic.cutoff3 B N ≤ N := by
  have hN : (1 : ℝ) ≤ N := by
    have hn : 1 ≤ N := by
      by_contra hn
      have : N = 0 := by omega
      norm_num [this] at hL
    exact_mod_cast hn
  have hp : Real.log N ^ (-B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have ht : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN (show (1 : ℝ) / 3 ≤ 1 by norm_num)
  apply Nat.floor_le_of_le
  exact (mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg N) _) hp).trans ht

/-- Halupczok pages 18 to 19, a modulus envelope on the averaging cube bounds EF.
This finite transfer retains the reduced residue conditions and all three cutoffs. -/
theorem EF_le_cube (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ)
    (G : (Fin 3 → ℕ) → ℝ) (B : ℝ) (N l₃ : ℕ)
    (hB : 0 ≤ B) (hL : 1 ≤ Real.log N) (hG : ∀ k, 0 ≤ G k)
    (hFG : ∀ k l, (∀ i, k i ∈ Icc 1 N) →
      (∀ i, Nat.Coprime (l i) (k i)) → |F k l| ≤ G k) :
    EF F (fun _ => 1) l₃ B N ≤
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, G ![a, b, c] := by
  have hK := Dyadic.cutoff_le B N hB hL
  have hK3 := cutoff3_le B N hB hL
  have hsub : Icc 1 (Dyadic.cutoff B N) ⊆ Icc 1 N := Icc_subset_Icc_right hK
  have hsub3 : Icc 1 (Dyadic.cutoff3 B N) ⊆ Icc 1 N := Icc_subset_Icc_right hK3
  have hf : EF F (fun _ => 1) l₃ B N ≤
      ∑ a ∈ Icc 1 (Dyadic.cutoff B N), ∑ b ∈ Icc 1 (Dyadic.cutoff B N),
        ∑ c ∈ Icc 1 (Dyadic.cutoff3 B N), G ![a, b, c] := by
    unfold EF
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro b hb
    have h0 : 0 ≤ ∑ c ∈ Icc 1 (Dyadic.cutoff3 B N), G ![a, b, c] :=
      sum_nonneg fun _ _ => hG _
    unfold innerF
    refine Real.iSup_le (fun x => Real.iSup_le (fun hx => Real.iSup_le
      (fun y => Real.iSup_le (fun hy => ?_) h0) h0) h0) h0
    simp only [one_mul]
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans (sum_le_sum fun c hc => ?_)
    · exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun c _ _ => hG _)
    · apply hFG
      · intro i
        fin_cases i
        · exact hsub ha
        · exact hsub hb
        · exact hsub3 (mem_filter.mp hc).1
      · intro i
        fin_cases i
        · exact (mem_filter.mp hx).2
        · exact (mem_filter.mp hy).2
        · exact (mem_filter.mp hc).2.symm
  apply hf.trans
  apply le_trans (sum_le_sum fun a _ => sum_le_sum fun b _ =>
    sum_le_sum_of_subset_of_nonneg hsub3 (fun c _ _ => hG _))
  apply le_trans (sum_le_sum fun a _ =>
    sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => sum_nonneg fun c _ => hG _))
  exact sum_le_sum_of_subset_of_nonneg hsub
    (fun a _ _ => sum_nonneg fun b _ => sum_nonneg fun c _ => hG _)

/-- Halupczok pages 18 to 19, the proved scalar budget after the three totient losses. -/
theorem log_budget (L : ℝ) (hL : 1 ≤ L) : L ^ (4926 : ℕ) ≤ L ^ (5000 : ℝ) := by
  rw [show (5000 : ℝ) = ((5000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact pow_le_pow_right₀ hL (by norm_num)

/-- Exact supply for the sealed coefficient mean leaf.
Derived from the local prime product leaf only. -/
theorem coefficient_mass_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        EF (fun k l => coefficientMass k l N) (fun _ => 1) l₃ (10 ^ 4 * A) N ≤
          C * Real.log N ^ (5000 : ℝ) := by
  intro A hA l₃ hl₃
  obtain ⟨C, hC, hmass⟩ := coefficientMass_le
  obtain ⟨D, hD, hsum⟩ := normalized_weight_sum
  refine ⟨C * D, Real.exp 1, mul_nonneg hC hD, fun N hodd hN => ?_⟩
  have hN0 : (0 : ℝ) < N := (Real.exp_pos 1).trans_le hN
  have hL : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hN
  have hL0 : 0 ≤ Real.log N := by linarith
  calc
    _ ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
        C * Real.log N ^ 11 * (rawWeight ![a, b, c] / phiProduct ![a, b, c]) := by
      apply EF_le_cube (fun k l => coefficientMass k l N)
        (fun k => C * Real.log N ^ 11 * (rawWeight k / phiProduct k))
        (10 ^ 4 * A) N l₃ (by positivity) hL
      · intro k
        exact mul_nonneg (mul_nonneg hC (by positivity))
          (div_nonneg (rawWeight_nonneg k) (phiProduct_nonneg k))
      · intro k l hk hl
        rw [abs_of_nonneg (coefficientMass_nonneg k l N)]
        exact hmass k l N N (fun i => (mem_Icc.mp (hk i)).1) hl hodd le_rfl
          (fun i => by exact_mod_cast (mem_Icc.mp (hk i)).2) hL
    _ = C * Real.log N ^ 11 *
        (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
          rawWeight ![a, b, c] / phiProduct ![a, b, c]) := by simp only [mul_sum]
    _ ≤ C * Real.log N ^ 11 * (D * Real.log N ^ (4915 : ℕ)) :=
      mul_le_mul_of_nonneg_left (hsum N hL) (by positivity)
    _ = (C * D) * Real.log N ^ (4926 : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (log_budget _ hL) (mul_nonneg hC hD)

end LeanLab.Tolev2009.Decomp355b
