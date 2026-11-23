module

public import LeanLab.DERZ1997.Character266
public import LeanLab.PNTPort.ZetaZeros.GoodHeight

/-!
Conductor-uniform contour helpers for the DERZ1997 character explicit formula.
The existing explicit-formula leaves remain unchanged.
The finite gap argument is checked against Dudek arXiv 1401.4233v1 pages 12 to 14.
The character extension uses the proved local estimates in Character266.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.DERZ1997.Decomp574a
open Complex Set Filter Metric Topology
open LeanLab.PNTPort.DirichletZF LeanLab.DERZ1997.Character266
set_option maxHeartbeats 500000


/-- The enlarged-disc local character count also bounds the number of distinct zeros.
Auxiliary height-selection step for Davenport chapter 19 page 120 and Dudek pages 12 to 13.
The multiplicity estimate is the proved Jensen bound in Character266.
-/
theorem character_scaled_card574 : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
      let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t + (3 / 2 : ℂ) * z)
      ∃ hf : (SetOfZeros (14 / 15) f).Finite,
        (hf.toFinset.card : ℝ) ≤ K * Real.log ((q : ℝ) * (|t| + 3)) := by
  obtain ⟨K, hK, hcount⟩ := character_scaled_zero_count266
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ t
  dsimp only
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t + (3 / 2 : ℂ) * z)
  obtain ⟨hf, hmass⟩ := hcount q χ hχ t
  refine ⟨hf, le_trans ?_ hmass⟩
  have hA (z : ℂ) : AnalyticAt ℂ f z := by
    have hd : Differentiable ℂ f := (DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop)
    exact hd.analyticAt z
  have hU : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z _ => hA z
  have hzero : analyticOrderAt f 0 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr ?_)]
    · simp
    · simpa only [f, mul_zero, add_zero] using LFunction_c_ne_zero χ t
  have hpos (z : ℂ) (hz : z ∈ hf.toFinset) : 1 ≤ analyticOrderNatAt f z := by
    have htop := hU.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 0) (y := z) (by simp) (by simp) hzero
    have hne := analyticOrderAt_ne_zero.mpr ⟨hA z, (hf.mem_toFinset.mp hz).2⟩
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
    rw [← hn] at hne
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  calc
    (hf.toFinset.card : ℝ) = ∑ _z ∈ hf.toFinset, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun z hz => by exact_mod_cast hpos z hz




/-- Under GRH a single height avoids zeros on both horizontal character contours.
The constant is absolute and the separation is inverse logarithmic in q times T plus four.
Auxiliary derivation from the proved local Jensen count for Davenport chapter 19 page 120.
No conjugation symmetry of the character is assumed.
-/
theorem character_good_height_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → ∃ U ∈ Set.Icc T (T + 1),
        ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
          1 / (C * Real.log ((q : ℝ) * (T + 4))) ≤ |(|ρ.im|) - U| := by
  classical
  obtain ⟨K, hK, hcard⟩ := character_scaled_card574
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨4 * (2 * K + 1 / Real.log 6), by positivity, ?_⟩
  intro q _ χ hχ T hT
  let t : ℝ := T + 1 / 2
  let c : ℝ → ℂ := fun v => (3 : ℂ) / 2 + I * v
  let f : ℝ → ℂ → ℂ := fun v z => DirichletCharacter.LFunction χ (c v + (3 / 2 : ℂ) * z)
  obtain ⟨hp, hpc⟩ := hcard q χ hχ t
  obtain ⟨hn, hnc⟩ := hcard q χ hχ (-t)
  let P := hp.toFinset.image (fun z : ℂ => |(c t + (3 / 2 : ℂ) * z).im|)
  let N := hn.toFinset.image (fun z : ℂ => |(c (-t) + (3 / 2 : ℂ) * z).im|)
  let G := P ∪ N
  let L : ℝ := Real.log ((q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 6 ≤ (q : ℝ) * (T + 4) := by nlinarith
  have hL6 : Real.log 6 ≤ L := Real.log_le_log (by norm_num) hM
  have hL : 0 < L := hlog6.trans_le hL6
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hlog : Real.log ((q : ℝ) * (|t| + 3)) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [abs_of_nonneg ht]
    dsimp [t]
    nlinarith
  have hGc : (G.card : ℝ) ≤ 2 * K * L := by
    have h1 := Finset.card_union_le P N
    have h2 := Finset.card_image_le (s := hp.toFinset)
      (f := fun z : ℂ => |(c t + (3 / 2 : ℂ) * z).im|)
    have h3 := Finset.card_image_le (s := hn.toFinset)
      (f := fun z : ℂ => |(c (-t) + (3 / 2 : ℂ) * z).im|)
    have hpbound := hpc.trans (mul_le_mul_of_nonneg_left hlog hK.le)
    have hnbound : (hn.toFinset.card : ℝ) ≤ K * L := by
      simpa only [abs_neg] using hnc.trans
        (mul_le_mul_of_nonneg_left (by simpa only [abs_neg] using hlog) hK.le)
    have h12 : (G.card : ℝ) ≤ hp.toFinset.card + hn.toFinset.card := by
      exact_mod_cast h1.trans (Nat.add_le_add h2 h3)
    linarith
  let δ : ℝ := 1 / (4 * ((G.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ4 : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
    linarith
  have hbudget : 1 / (4 * (2 * K + 1 / Real.log 6) * L) ≤ δ := by
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : 1 ≤ (1 / Real.log 6) * L := by
      rw [one_div_mul_eq_div, le_div_iff₀ hlog6]
      simpa only [one_mul] using hL6
    nlinarith
  obtain ⟨U, hUI, hfar⟩ := LeanLab.PNTPort.ZetaZeros.exists_far G T
  refine ⟨U, hUI, ?_⟩
  intro ρ hz hr0 hr1
  have hline := hG q χ ρ hz hr0 hr1
  have hsep : δ ≤ |(|ρ.im|) - U| := by
    by_cases hnear : |(|ρ.im|) - t| ≤ 3 / 4
    · have hmem : |ρ.im| ∈ G := by
        have hnorm (v : ℝ) (hv : |ρ.im - v| ≤ 3 / 4) :
            ‖(ρ - c v) / (3 / 2 : ℂ)‖ ≤ 14 / 15 := by
          have hsq : ‖ρ - c v‖ ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            have hre : (ρ - c v).re = -1 := by simp [c, hline]; norm_num
            have him : (ρ - c v).im = ρ.im - v := by simp [c]
            rw [hre, him]
            have hv' := (sq_le_sq₀ (abs_nonneg (ρ.im - v)) (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr hv
            rw [sq_abs] at hv'
            nlinarith
          have hb : ‖ρ - c v‖ ≤ 5 / 4 := by nlinarith [norm_nonneg (ρ - c v)]
          rw [norm_div]
          norm_num only [norm_div, norm_ofNat]
          linarith
        have he (v : ℝ) : c v + (3 / 2 : ℂ) * ((ρ - c v) / (3 / 2 : ℂ)) = ρ := by ring
        by_cases hi : 0 ≤ ρ.im
        · apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨(ρ - c t) / (3 / 2 : ℂ), hp.mem_toFinset.mpr ?_, ?_⟩
          · exact ⟨hnorm t (by simpa only [abs_of_nonneg hi] using hnear), by change DirichletCharacter.LFunction χ (c t + (3 / 2 : ℂ) * ((ρ - c t) / (3 / 2 : ℂ))) = 0; rw [he]; exact hz⟩
          · rw [he]
        · apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨(ρ - c (-t)) / (3 / 2 : ℂ), hn.mem_toFinset.mpr ?_, ?_⟩
          · refine ⟨hnorm (-t) ?_, by change DirichletCharacter.LFunction χ (c (-t) + (3 / 2 : ℂ) * ((ρ - c (-t)) / (3 / 2 : ℂ))) = 0; rw [he]; exact hz⟩
            rw [abs_of_neg (lt_of_not_ge hi)] at hnear
            have he : ρ.im - (-t) = -(-ρ.im - t) := by ring
            rw [he, abs_neg]
            exact hnear
          · rw [he]
      have hh := hfar |ρ.im| hmem
      rw [abs_sub_comm] at hh
      have hd : δ ≤ 1 / (2 * ((G.card : ℝ) + 1)) := by
        dsimp [δ]
        apply one_div_le_one_div_of_le (by positivity)
        have : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
        linarith
      exact hd.trans hh
    · have htri := abs_sub_le |ρ.im| U t
      have hut : |U - t| ≤ 1 / 2 := by
        rw [abs_le]
        dsimp [t]
        constructor <;> linarith [hUI.1, hUI.2]
      have hnear' : 3 / 4 < |(|ρ.im|) - t| := lt_of_not_ge hnear
      linarith
  exact hbudget.trans hsep



/-- A simultaneous bound for the two horizontal character contours under GRH.
The constant is uniform in the modulus. The interval reaches real part one eighth.
Auxiliary explicit-formula step for Davenport chapter 19 page 120 and chapter 20 page 125.
The proof uses the local partial fractions and the two-sign good-height selection.
-/
theorem character_horizontal_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → ∃ U ∈ Set.Icc T (T + 1),
        ∀ y ∈ ({U, -U} : Set ℝ), ∀ σ ∈ Set.Icc (1 / 8 : ℝ) (5 / 2),
          DirichletCharacter.LFunction χ ((σ : ℂ) + I * y) ≠ 0 ∧
          ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * y) /
            DirichletCharacter.LFunction χ ((σ : ℂ) + I * y)‖ ≤
              C * Real.log ((q : ℝ) * (T + 4)) ^ 2 := by
  obtain ⟨A, hA, hpartial⟩ := character_scaled_local266
  obtain ⟨B, hB, hcount⟩ := character_scaled_zero_count266
  obtain ⟨D, hD, hheight⟩ := character_good_height_GRH574 hG
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨(2 / 3) * A / Real.log 6 + B * D, by positivity, ?_⟩
  intro q _ χ hχ T hT
  obtain ⟨U, hUI, hsep⟩ := hheight q χ hχ T hT
  refine ⟨U, hUI, ?_⟩
  intro y hy σ hσ
  let L : ℝ := Real.log ((q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 6 ≤ (q : ℝ) * (T + 4) := by nlinarith
  have hL6 : Real.log 6 ≤ L := Real.log_le_log (by norm_num) hM
  have hL : 0 < L := hlog6.trans_le hL6
  have hU : 0 < U := by linarith [hUI.1]
  have hyabs : |y| = U := by
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy : y = U ∨ y = -U) with rfl | rfl
    · exact abs_of_pos hU
    · rw [abs_neg, abs_of_pos hU]
  have hlog : Real.log ((q : ℝ) * (|y| + 3)) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hyabs]
    nlinarith [hUI.2]
  let c : ℂ := (3 : ℂ) / 2 + I * y
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (c + (3 / 2 : ℂ) * z)
  let s : ℂ := (σ : ℂ) + I * y
  let z : ℂ := ((σ : ℂ) - 3 / 2) / (3 / 2 : ℂ)
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = y := by simp [s]
  have hsz : c + (3 / 2 : ℂ) * z = s := by dsimp [c, z, s]; ring
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro hz
    have hr0 : 0 < s.re := by rw [hsre]; linarith [hσ.1]
    have hr1 : s.re < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hz
    have hh := hsep s hz hr0 hr1
    rw [hsim, hyabs, sub_self, abs_zero] at hh
    exact not_le_of_gt (one_div_pos.mpr (mul_pos hD hL)) hh
  refine ⟨hLs, ?_⟩
  obtain ⟨hf, hp⟩ := hpartial q χ hχ y
  obtain ⟨hf', hc⟩ := hcount q χ hχ y
  have hmass : (∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ)) ≤ B * L :=
    hc.trans (mul_le_mul_of_nonneg_left hlog hB.le)
  have hdist (ρ : ℂ) (hρ : ρ ∈ hf.toFinset) :
      1 / (D * L) ≤ ‖s - (c + (3 / 2 : ℂ) * ρ)‖ := by
    have hh := hf.mem_toFinset.mp hρ
    let r : ℂ := c + (3 / 2 : ℂ) * ρ
    have hr0 : 0 < r.re := by
      have hn := (Complex.abs_re_le_norm ρ).trans hh.1
      have hlo := (abs_le.mp hn).1
      dsimp [r, c]
      simp only [div_ofNat_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      linarith
    have hr1 : r.re < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hh.2
    have hs := hsep r hh.2 hr0 hr1
    have htri : |(|r.im|) - U| ≤ |y - r.im| := by
      rw [← hyabs]
      exact (abs_abs_sub_abs_le_abs_sub r.im y).trans_eq (abs_sub_comm _ _)
    exact hs.trans (htri.trans (by simpa only [sub_im, hsim] using Complex.abs_im_le_norm (s - r)))
  have hsepz (ρ : ℂ) (hρ : ρ ∈ hf.toFinset) :
      (2 / 3) / (D * L) ≤ ‖z - ρ‖ := by
    have hh := hdist ρ hρ
    have he : s - (c + (3 / 2 : ℂ) * ρ) = (3 / 2 : ℂ) * (z - ρ) := by rw [← hsz]; ring
    rw [he, norm_mul] at hh
    norm_num only [norm_div, norm_ofNat] at hh
    have heq : (2 / 3 : ℝ) / (D * L) = (2 / 3) * (1 / (D * L)) := by ring
    rw [heq]
    nlinarith
  let S : ℂ := ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)
  have hsum : ‖S‖ ≤ (3 / 2) * B * D * L ^ 2 := by
    calc
      _ ≤ ∑ ρ ∈ hf.toFinset, ‖(analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ) / ((2 / 3) / (D * L)) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (hsepz ρ hρ)
      _ = (3 / 2) * D * L * ∑ ρ ∈ hf.toFinset, (analyticOrderNatAt f ρ : ℝ) := by
        rw [← Finset.sum_div]
        field_simp
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ (3 / 2) * D * L)]
  have hz : ‖z‖ ≤ 11 / 12 := by
    have he : z = (((σ - 3 / 2) / (3 / 2) : ℝ) : ℂ) := by dsimp [z]; push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hfn : f z ≠ 0 := by dsimp [f]; rwa [hsz]
  have hpart := (hp z hz hfn).trans (mul_le_mul_of_nonneg_left hlog hA.le)
  have htri : ‖deriv f z / f z‖ ≤ A * L + (3 / 2) * B * D * L ^ 2 := by
    have hh := norm_sub_le (deriv f z / f z - S) (-S)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hh
    change ‖deriv f z / f z - S‖ ≤ _ at hpart
    linarith
  have hderiv : deriv f z = (3 / 2 : ℂ) * deriv (DirichletCharacter.LFunction χ) s := by
    have haff : HasDerivAt (fun w : ℂ => c + (3 / 2 : ℂ) * w) (3 / 2 : ℂ) z := by
      simpa only [id_eq, mul_one, add_comm] using ((hasDerivAt_id z).const_mul (3 / 2 : ℂ)).const_add c
    have hh := ((DirichletCharacter.differentiable_LFunction hχ (c + (3 / 2 : ℂ) * z)).hasDerivAt.comp z haff)
    rw [hsz] at hh
    simpa only [f, Function.comp_def, mul_comm] using hh.deriv
  have hfnval : f z = DirichletCharacter.LFunction χ s := by dsimp [f]; rw [hsz]
  rw [hderiv, hfnval, mul_div_assoc, norm_mul] at htri
  norm_num only [norm_div, norm_ofNat] at htri
  have hLL : L ≤ L ^ 2 / Real.log 6 := by
    rw [le_div_iff₀ hlog6]
    nlinarith
  have hAL := mul_le_mul_of_nonneg_left hLL hA.le
  change ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
    ((2 / 3) * A / Real.log 6 + B * D) * L ^ 2
  calc
    _ ≤ (2 / 3) * (A * L + (3 / 2) * B * D * L ^ 2) := by rw [norm_div]; linarith
    _ ≤ (2 / 3) * (A * (L ^ 2 / Real.log 6) + (3 / 2) * B * D * L ^ 2) := by gcongr
    _ = _ := by ring



/-- A pointwise horizontal logarithmic derivative bound controls the unsmoothed Perron edge.
The proof retains interval integrability, which is required for the rectangle assembly.
Auxiliary integral estimate for Davenport chapter 19 page 120 and Dudek page 14.
-/
theorem character_horizontal_integral574 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x U B : ℝ}
    (hx : 2 ≤ x) (hU : 0 < U) (hB : 0 ≤ B)
    (y : ℝ) (hy : |y| = U)
    (hbound : ∀ σ ∈ Set.Icc (1 / 8 : ℝ) (5 / 2),
      DirichletCharacter.LFunction χ ((σ : ℂ) + I * y) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * y) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + I * y)‖ ≤ B) :
    IntervalIntegrable (fun σ : ℝ =>
      -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * y) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + I * y)) *
          (x : ℂ) ^ ((σ : ℂ) + I * y) / ((σ : ℂ) + I * y))
      MeasureTheory.volume (1 / 8) (1 + 1 / Real.log x) ∧
    ‖∫ σ in (1 / 8 : ℝ)..(1 + 1 / Real.log x),
      -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * y) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + I * y)) *
          (x : ℂ) ^ ((σ : ℂ) + I * y) / ((σ : ℂ) + I * y)‖ ≤
      8 * B * x / U := by
  let c : ℝ := 1 + 1 / Real.log x
  let L := DirichletCharacter.LFunction χ
  let s : ℝ → ℂ := fun σ => (σ : ℂ) + I * y
  let F : ℝ → ℂ := fun σ => -(deriv L (s σ) / L (s σ)) * (x : ℂ) ^ (s σ) / s σ
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog23 : (2 / 3 : ℝ) ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  have hc1 : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlog]
  have hc : c ≤ 5 / 2 := by
    have hh : 1 / Real.log x ≤ (3 / 2 : ℝ) := (div_le_iff₀ hlog).mpr (by linarith)
    dsimp [c]; linarith
  have hac : (1 / 8 : ℝ) ≤ c := by linarith
  have hsub : Set.uIcc (1 / 8 : ℝ) c ⊆ Set.Icc (1 / 8 : ℝ) (5 / 2) := by
    rw [Set.uIcc_of_le hac]
    exact fun _ hh => ⟨hh.1, hh.2.trans hc⟩
  have hsn (σ : ℝ) : s σ ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [s, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add, zero_im] at hh
    rw [hh, abs_zero] at hy
    linarith
  have hLA (z : ℂ) : AnalyticAt ℂ L z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hderiv : Continuous (deriv L) :=
    continuous_iff_continuousAt.mpr fun z => (hLA z).deriv.continuousAt
  have hLc : Continuous L := (DirichletCharacter.differentiable_LFunction hχ).continuous
  have hsc : Continuous s := by dsimp [s]; fun_prop
  have hcont : ContinuousOn F (Set.uIcc (1 / 8 : ℝ) c) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact ((hderiv.comp hsc).continuousOn.div (hLc.comp hsc).continuousOn
          (fun σ hσ => (hbound σ (hsub hσ)).1)).neg
      · exact (Continuous.const_cpow hsc (Or.inl (Complex.ofReal_ne_zero.mpr hx0.ne'))).continuousOn
    · exact hsc.continuousOn
    · intro σ _; exact hsn σ
  have hint : IntervalIntegrable F MeasureTheory.volume (1 / 8) c := hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  have hpow : x ^ c ≤ 3 * x := by
    have he : x ^ c = x * Real.exp 1 := by
      dsimp [c]
      rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
      congr 1
      rw [mul_one_div_cancel hlog.ne']
    rw [he]
    nlinarith [Real.exp_one_lt_three]
  have hb (σ : ℝ) (hσ : σ ∈ Set.uIoc (1 / 8 : ℝ) c) : ‖F σ‖ ≤ 3 * B * x / U := by
    have hσ' : σ ∈ Set.uIcc (1 / 8 : ℝ) c := Set.uIoc_subset_uIcc hσ
    have hσc : σ ≤ c := by rw [Set.uIcc_of_le hac] at hσ'; exact hσ'.2
    have hp : x ^ σ ≤ 3 * x :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσc).trans hpow
    have hn : U ≤ ‖s σ‖ := by
      have hh := Complex.abs_im_le_norm (s σ)
      simpa only [s, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add, hy] using hh
    dsimp [F]
    rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hsre : (s σ).re = σ := by simp [s]
    rw [hsre]
    have hnum : ‖deriv L (s σ) / L (s σ)‖ * x ^ σ ≤ B * (3 * x) :=
      mul_le_mul (hbound σ (hsub hσ')).2 hp (Real.rpow_nonneg hx0.le _) hB
    have hh := div_le_div₀ (mul_nonneg hB (by positivity : 0 ≤ 3 * x)) hnum hU hn
    convert hh using 1; ring
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  change ‖∫ σ in (1 / 8 : ℝ)..c, F σ‖ ≤ _
  have hlen : |c - 1 / 8| ≤ 5 / 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  calc
    _ ≤ (3 * B * x / U) * |c - 1 / 8| := hh
    _ ≤ (3 * B * x / U) * (5 / 2) := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = (15 / 2) * (B * x / U) := by ring
    _ ≤ 8 * (B * x / U) := by nlinarith [div_nonneg (mul_nonneg hB hx0.le) hU.le]
    _ = _ := by ring



/-- The positive left Perron edge loses only a logarithm of its height.
The pointwise logarithmic derivative estimate is retained as an explicit premise.
Auxiliary integral estimate for Davenport chapter 20 page 125.
-/
theorem character_left_integral574 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x U B : ℝ}
    (hx : 0 < x) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Icc (-U) U,
      DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
        DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)‖ ≤ B) :
    IntervalIntegrable (fun t : ℝ =>
      -(deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
        DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)) *
          (x : ℂ) ^ ((1 / 8 : ℂ) + I * t) / ((1 / 8 : ℂ) + I * t))
      MeasureTheory.volume (-U) U ∧
    ‖∫ t in (-U)..U,
      -(deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
        DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)) *
          (x : ℂ) ^ ((1 / 8 : ℂ) + I * t) / ((1 / 8 : ℂ) + I * t)‖ ≤
      18 * B * x ^ (1 / 8 : ℝ) * Real.log (1 + U) := by
  let L := DirichletCharacter.LFunction χ
  let s : ℝ → ℂ := fun t => (1 / 8 : ℂ) + I * t
  let F : ℝ → ℂ := fun t => -(deriv L (s t) / L (s t)) * (x : ℂ) ^ (s t) / s t
  let g : ℝ → ℝ := fun t => 1 / (1 + |t|)
  have hab : -U ≤ U := by linarith
  have hsn (t : ℝ) : s t ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [s] at hh
  have hsc : Continuous s := by dsimp [s]; fun_prop
  have hLA (z : ℂ) : AnalyticAt ℂ L z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hderiv : Continuous (deriv L) :=
    continuous_iff_continuousAt.mpr fun z => (hLA z).deriv.continuousAt
  have hLc : Continuous L := (DirichletCharacter.differentiable_LFunction hχ).continuous
  have hcont : ContinuousOn F (Set.uIcc (-U) U) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact ((hderiv.comp hsc).continuousOn.div (hLc.comp hsc).continuousOn
          (fun t ht => (hbound t (by simpa only [Set.uIcc_of_le hab] using ht)).1)).neg
      · exact (Continuous.const_cpow hsc (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).continuousOn
    · exact hsc.continuousOn
    · intro t _; exact hsn t
  have hint : IntervalIntegrable F MeasureTheory.volume (-U) U := hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  have hgc : Continuous g := by
    apply continuous_const.div (continuous_const.add continuous_abs)
    intro t
    change 1 + |t| ≠ 0
    positivity
  have hgi : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b := fun a b => hgc.intervalIntegrable a b
  have hpos : (∫ t in (0 : ℝ)..U, g t) = Real.log (1 + U) := by
    have he : (∫ t in (0 : ℝ)..U, g t) = ∫ t in (0 : ℝ)..U, 1 / (1 + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hU] at ht
      simp only [g, abs_of_nonneg ht.1]
    rw [he]
    have hd (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) U) :
        HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
      rw [Set.uIcc_of_le hU] at ht
      convert ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).log (by linarith [ht.1] : 1 + t ≠ 0) using 1 <;> simp
    have hi : IntervalIntegrable (fun t : ℝ => 1 / (1 + t)) MeasureTheory.volume 0 U := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
      intro t ht
      rw [Set.uIcc_of_le hU] at ht
      change 1 + t ≠ 0
      linarith [ht.1]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hneg : (∫ t in (-U)..(0 : ℝ), g t) = Real.log (1 + U) := by
    have he : (∫ t in (-U)..(0 : ℝ), g t) = ∫ t in (-U)..(0 : ℝ), 1 / (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -U ≤ (0 : ℝ))] at ht
      simp only [g, abs_of_nonpos ht.2, sub_eq_add_neg]
    rw [he]
    have hd (t : ℝ) (ht : t ∈ Set.uIcc (-U) (0 : ℝ)) :
        HasDerivAt (fun t : ℝ => -Real.log (1 - t)) (1 / (1 - t)) t := by
      rw [Set.uIcc_of_le (by linarith : -U ≤ (0 : ℝ))] at ht
      convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log
        (by linarith [ht.2] : 1 - t ≠ 0)).neg using 1
      · rfl
      · dsimp; ring
    have hi : IntervalIntegrable (fun t : ℝ => 1 / (1 - t)) MeasureTheory.volume (-U) 0 := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -U ≤ (0 : ℝ))] at ht
      change 1 - t ≠ 0
      linarith [ht.2]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hgint : (∫ t in (-U)..U, g t) = 2 * Real.log (1 + U) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi (-U) 0) (hgi 0 U), hneg, hpos]
    ring
  have hb (t : ℝ) (ht : t ∈ Set.Ioc (-U) U) :
      ‖F t‖ ≤ (9 * B * x ^ (1 / 8 : ℝ)) * g t := by
    have hn : (1 + |t|) / 9 ≤ ‖s t‖ := by
      have hre := Complex.abs_re_le_norm (s t)
      have him := Complex.abs_im_le_norm (s t)
      norm_num [s] at hre him
      linarith
    have hn0 : 0 < (1 + |t|) / 9 := by positivity
    dsimp [F]
    rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hsre : (s t).re = 1 / 8 := by norm_num [s]
    rw [hsre]
    have hnum := mul_le_mul_of_nonneg_right (hbound t ⟨ht.1.le, ht.2⟩).2
      (Real.rpow_nonneg hx.le (1 / 8 : ℝ))
    have hh := div_le_div₀ (mul_nonneg hB (Real.rpow_nonneg hx.le (1 / 8 : ℝ))) hnum hn0 hn
    calc
      _ ≤ B * x ^ (1 / 8 : ℝ) / ((1 + |t|) / 9) := hh
      _ = _ := by dsimp [g]; rw [div_div_eq_mul_div]; ring
  have hmajor := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall hb) ((hgi (-U) U).const_mul (9 * B * x ^ (1 / 8 : ℝ)))
  change ‖∫ t in (-U)..U, F t‖ ≤ _
  calc
    _ ≤ ∫ t in (-U)..U, (9 * B * x ^ (1 / 8 : ℝ)) * g t := hmajor
    _ = _ := by rw [intervalIntegral.integral_const_mul, hgint]; ring



/-- Under GRH the positive left-edge integral fits the sealed character error scale.
This is uniform in the modulus and allows height up to x plus one.
Auxiliary derivation for Davenport chapter 20 page 125.
-/
theorem character_left_budget_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x U : ℝ, 2 ≤ x → 0 ≤ U → U ≤ x + 1 →
        IntervalIntegrable (fun t : ℝ =>
          -(deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
            DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)) *
              (x : ℂ) ^ ((1 / 8 : ℂ) + I * t) / ((1 / 8 : ℂ) + I * t))
          MeasureTheory.volume (-U) U ∧
        ‖∫ t in (-U)..U,
          -(deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
            DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)) *
              (x : ℂ) ^ ((1 / 8 : ℂ) + I * t) / ((1 / 8 : ℂ) + I * t)‖ ≤
          C * (Real.sqrt x + Real.log ((q : ℝ) * x) ^ 2) := by
  obtain ⟨K, hK, hleft⟩ := character_left_eighth_GRH266 hG
  refine ⟨432 * K, by positivity, ?_⟩
  intro q _ χ hχ x U hx hU hUx
  let L : ℝ := Real.log ((q : ℝ) * x)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx0 : 0 < x := by linarith
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
  have hlog3 : Real.log 3 ≤ 2 * L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hlogQ : Real.log ((q : ℝ) * (U + 3)) ≤ 3 * L := by
    have hh : Real.log ((q : ℝ) * (U + 3)) ≤ Real.log (3 * ((q : ℝ) * x)) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hh
    dsimp [L] at *
    linarith
  have hlogU : Real.log (1 + U) ≤ 2 * Real.log x := by
    have hh := Real.log_le_log (by linarith : 0 < 1 + U) (show 1 + U ≤ x ^ 2 by nlinarith)
    rwa [Real.log_pow] at hh
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-U) U) :
      DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + I * t) /
          DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + I * t)‖ ≤ 3 * K * L := by
    obtain ⟨hn, hb⟩ := hleft q χ hχ t
    refine ⟨hn, ?_⟩
    have habs : |t| ≤ U := abs_le.mpr ht
    have hh : Real.log ((q : ℝ) * (|t| + 3)) ≤ Real.log ((q : ℝ) * (U + 3)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hh' := hb.trans (mul_le_mul_of_nonneg_left (hh.trans hlogQ) hK.le)
    convert hh' using 1; ring
  obtain ⟨hint, hb⟩ := character_left_integral574 χ hχ hx0 hU (by positivity) hpoint
  refine ⟨hint, hb.trans ?_⟩
  have hnum := mul_le_mul_of_nonneg_left hlogU
    (by positivity : 0 ≤ 18 * (3 * K * L) * x ^ (1 / 8 : ℝ))
  have hbudget := mul_le_mul_of_nonneg_left (left_edge_budget266 hx hL.le)
    (by positivity : 0 ≤ 108 * K)
  calc
    _ ≤ 18 * (3 * K * L) * x ^ (1 / 8 : ℝ) * (2 * Real.log x) := hnum
    _ = 108 * K * (x ^ (1 / 8 : ℝ) * Real.log x * L) := by ring
    _ ≤ 108 * K * (4 * (Real.sqrt x + L ^ 2)) := hbudget
    _ = _ := by ring



/-- A finite family of critical-line L-zeros in a short ordinate interval has logarithmic mass.
The affine coordinates preserve the analytic zero orders.
Auxiliary height-transfer estimate for Davenport chapter 19 page 120 and Dudek page 14.
-/
theorem character_local_mass574 : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (t : ℝ) (S : Finset ℂ),
        (∀ ρ ∈ S, DirichletCharacter.LFunction χ ρ = 0 ∧
          ρ.re = 1 / 2 ∧ |ρ.im - t| ≤ 3 / 4) →
        (∑ ρ ∈ S, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
          K * Real.log ((q : ℝ) * (|t| + 3)) := by
  classical
  obtain ⟨K, hK, hcount⟩ := character_scaled_zero_count266
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ t S hS
  let L := DirichletCharacter.LFunction χ
  let c : ℂ := (3 : ℂ) / 2 + I * t
  let a : ℂ → ℂ := fun z => c + (3 / 2 : ℂ) * z
  let f : ℂ → ℂ := fun z => L (a z)
  let w : ℂ → ℂ := fun ρ => (ρ - c) / (3 / 2 : ℂ)
  have haw (ρ : ℂ) : a (w ρ) = ρ := by dsimp [a, w]; ring
  obtain ⟨hf, hc⟩ := hcount q χ hχ t
  have hmem (ρ : ℂ) (hρ : ρ ∈ S) : w ρ ∈ hf.toFinset := by
    obtain ⟨hz, hr, hi⟩ := hS ρ hρ
    apply hf.mem_toFinset.mpr
    constructor
    · have hsq : ‖ρ - c‖ ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have hre : (ρ - c).re = -1 := by simp [c, hr]; norm_num
        have him : (ρ - c).im = ρ.im - t := by simp [c]
        rw [hre, him]
        have hi' := (sq_le_sq₀ (abs_nonneg (ρ.im - t)) (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr hi
        rw [sq_abs] at hi'
        nlinarith
      have hb : ‖ρ - c‖ ≤ 5 / 4 := by nlinarith [norm_nonneg (ρ - c)]
      dsimp [w]
      rw [norm_div]
      norm_num only [norm_div, norm_ofNat]
      linarith
    · change L (a (w ρ)) = 0
      rw [haw]
      exact hz
  have hord (ρ : ℂ) : analyticOrderNatAt f (w ρ) =
      LeanLab.DERZ1997.Decomp1529a.LMult χ ρ := by
    have ha : AnalyticAt ℂ a (w ρ) := by dsimp [a]; fun_prop
    have hd : deriv a (w ρ) = (3 / 2 : ℂ) := by
      have hh : HasDerivAt a (3 / 2 : ℂ) (w ρ) := by
        simpa only [a, id_eq, mul_one, add_comm] using
          ((hasDerivAt_id (w ρ)).const_mul (3 / 2 : ℂ)).const_add c
      exact hh.deriv
    have he := analyticOrderAt_comp_of_deriv_ne_zero (f := L) ha (by rw [hd]; norm_num)
    change analyticOrderAt f (w ρ) = analyticOrderAt L (a (w ρ)) at he
    rw [haw] at he
    exact congrArg ENat.toNat he
  have hinj : Function.Injective w := by
    intro ρ τ he
    have hh := congrArg a he
    simpa only [haw] using hh
  have hsub : S.image w ⊆ hf.toFinset := by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
    exact hmem ρ hρ
  calc
    _ = ∑ ρ ∈ S, (analyticOrderNatAt f (w ρ) : ℝ) := by simp_rw [hord]
    _ = ∑ z ∈ S.image w, (analyticOrderNatAt f z : ℝ) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ he => hinj he
    _ ≤ ∑ z ∈ hf.toFinset, (analyticOrderNatAt f z : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ _ := hc



/-- Under GRH the total L-zero multiplicity in a two-sided unit band is logarithmic.
Both signs are bounded independently for a general complex character.
Auxiliary height-transfer estimate for Davenport chapter 19 page 120 and Dudek page 14.
-/
theorem character_band_mass_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (T U : ℝ) (S : Finset ℂ), 2 ≤ T → U ≤ T + 1 →
        (∀ ρ ∈ S, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          T < |ρ.im| ∧ |ρ.im| ≤ U) →
        (∑ ρ ∈ S, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
          C * Real.log ((q : ℝ) * (T + 4)) := by
  classical
  obtain ⟨K, hK, hmass⟩ := character_local_mass574
  refine ⟨2 * K, by positivity, ?_⟩
  intro q _ χ hχ T U S hT hU hS
  let t : ℝ := T + 1 / 2
  let P := S.filter (fun ρ => 0 ≤ ρ.im)
  let N := S.filter (fun ρ => ¬ 0 ≤ ρ.im)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hlog : Real.log ((q : ℝ) * (|t| + 3)) ≤ Real.log ((q : ℝ) * (T + 4)) := by
    apply Real.log_le_log (by positivity)
    rw [abs_of_nonneg ht]
    dsimp [t]
    nlinarith
  have hpos : (∑ ρ ∈ P, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
      K * Real.log ((q : ℝ) * (T + 4)) := by
    apply (hmass q χ hχ t P ?_).trans (mul_le_mul_of_nonneg_left hlog hK.le)
    intro ρ hρ
    obtain ⟨hρS, hi⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hS ρ hρS
    refine ⟨hz, hG q χ ρ hz hr0 hr1, ?_⟩
    rw [abs_of_nonneg hi] at hlo hhi
    rw [abs_le]
    dsimp [t]
    constructor <;> linarith
  have hneg : (∑ ρ ∈ N, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) ≤
      K * Real.log ((q : ℝ) * (T + 4)) := by
    apply (hmass q χ hχ (-t) N ?_).trans
      (mul_le_mul_of_nonneg_left (by simpa only [abs_neg] using hlog) hK.le)
    intro ρ hρ
    obtain ⟨hρS, hi⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hS ρ hρS
    refine ⟨hz, hG q χ ρ hz hr0 hr1, ?_⟩
    rw [abs_of_neg (lt_of_not_ge hi)] at hlo hhi
    rw [abs_le]
    dsimp [t]
    constructor <;> linarith
  have he := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ => 0 ≤ ρ.im)
    (fun ρ => (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ))
  change (∑ ρ ∈ P, _) + (∑ ρ ∈ N, _) = _ at he
  linarith


/-- A unit height transfer of the character zero sum has the square-root GRH size.
The conductor-uniform mass bound comes from local Jensen, not the cited global count.
Auxiliary height-transfer step for Davenport chapter 19 page 120 and Dudek page 14.
-/
theorem character_height_transfer_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x T U : ℝ, 1 ≤ x → 2 ≤ T → T ≤ U → U ≤ T + 1 →
        ∀ (hfT : (LeanLab.DERZ1997.Decomp1529a.LZeros χ T).Finite)
          (hfU : (LeanLab.DERZ1997.Decomp1529a.LZeros χ U).Finite),
          ‖(∑ ρ ∈ hfU.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) *
              (x : ℂ) ^ ρ / ρ) -
            ∑ ρ ∈ hfT.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) *
              (x : ℂ) ^ ρ / ρ‖ ≤
            C * Real.sqrt x * Real.log ((q : ℝ) * (T + 4)) / T := by
  classical
  obtain ⟨C, hC, hband⟩ := character_band_mass_GRH574 hG
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ x T U hx hT hTU hU hfT hfU
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hsub : hfT.toFinset ⊆ hfU.toFinset := by
    intro ρ hρ
    obtain ⟨hz, hr0, hr1, ht⟩ := hfT.mem_toFinset.mp hρ
    exact hfU.mem_toFinset.mpr ⟨hz, hr0, hr1, ht.trans hTU⟩
  let S := hfU.toFinset \ hfT.toFinset
  have hS (ρ : ℂ) (hρ : ρ ∈ S) : DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im| ∧ |ρ.im| ≤ U := by
    obtain ⟨hu, ht⟩ := Finset.mem_sdiff.mp hρ
    obtain ⟨hz, hr0, hr1, hi⟩ := hfU.mem_toFinset.mp hu
    refine ⟨hz, hr0, hr1, ?_, hi⟩
    exact lt_of_not_ge (fun hh => ht (hfT.mem_toFinset.mpr ⟨hz, hr0, hr1, hh⟩))
  have hterm (ρ : ℂ) (hρ : ρ ∈ S) :
      ‖(LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ) * Real.sqrt x / T := by
    obtain ⟨hz, hr0, hr1, hi, hu⟩ := hS ρ hρ
    have hline := hG q χ ρ hz hr0 hr1
    have hn : T ≤ ‖ρ‖ := hi.le.trans (Complex.abs_im_le_norm ρ)
    rw [norm_div, norm_mul, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, hline, ← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_left (by positivity) hT0 hn
  have hmass := hband q χ hχ T U S hT hU hS
  rw [← Finset.sum_sdiff_eq_sub hsub]
  calc
    _ ≤ ∑ ρ ∈ S, ‖(LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ) * Real.sqrt x / T :=
      Finset.sum_le_sum hterm
    _ = (∑ ρ ∈ S, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) * Real.sqrt x / T := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
    _ ≤ (C * Real.log ((q : ℝ) * (T + 4))) * Real.sqrt x / T := by gcongr
    _ = _ := by ring



/-- Under GRH both horizontal Perron edges fit the character explicit-formula scale.
A single height between T and T plus one works for both signs.
Auxiliary derivation for Davenport chapter 19 page 120 and chapter 20 page 125.
-/
theorem character_horizontal_budget_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x → ∃ U ∈ Set.Icc T (T + 1),
        ∀ y ∈ ({U, -U} : Set ℝ),
          (∀ σ ∈ Set.Icc (1 / 8 : ℝ) (5 / 2),
            DirichletCharacter.LFunction χ ((σ : ℂ) + I * y) ≠ 0) ∧
          IntervalIntegrable (fun σ : ℝ =>
            -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * y) /
              DirichletCharacter.LFunction χ ((σ : ℂ) + I * y)) *
                (x : ℂ) ^ ((σ : ℂ) + I * y) / ((σ : ℂ) + I * y))
            MeasureTheory.volume (1 / 8) (1 + 1 / Real.log x) ∧
          ‖∫ σ in (1 / 8 : ℝ)..(1 + 1 / Real.log x),
            -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * y) /
              DirichletCharacter.LFunction χ ((σ : ℂ) + I * y)) *
                (x : ℂ) ^ ((σ : ℂ) + I * y) / ((σ : ℂ) + I * y)‖ ≤
            C * x * Real.log ((q : ℝ) * x) ^ 2 / T := by
  obtain ⟨A, hA, hhor⟩ := character_horizontal_GRH574 hG
  refine ⟨72 * A, by positivity, ?_⟩
  intro q _ χ hχ x T hx hT hTx
  obtain ⟨U, hUI, hpoint⟩ := hhor q χ hχ T hT
  refine ⟨U, hUI, ?_⟩
  intro y hy
  refine ⟨fun σ hσ => (hpoint y hy σ hσ).1, ?_⟩
  let L : ℝ := Real.log ((q : ℝ) * x)
  let H : ℝ := Real.log ((q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := by linarith [hUI.1]
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hH : 0 < H := Real.log_pos (by nlinarith)
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
  have hlog3 : Real.log 3 ≤ 2 * L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hHL : H ≤ 3 * L := by
    have hh : H ≤ Real.log (3 * ((q : ℝ) * x)) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hh
    change H ≤ Real.log 3 + L at hh
    linarith
  have hyabs : |y| = U := by
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy : y = U ∨ y = -U) with rfl | rfl
    · exact abs_of_pos hU0
    · rw [abs_neg, abs_of_pos hU0]
  obtain ⟨hint, hb⟩ := character_horizontal_integral574 χ hχ hx hU0
    (by positivity : 0 ≤ A * H ^ 2) y hyabs (hpoint y hy)
  refine ⟨hint, hb.trans ?_⟩
  have hsq : H ^ 2 ≤ 9 * L ^ 2 := by nlinarith
  have hnum : 8 * (A * H ^ 2) * x ≤ 8 * (A * (9 * L ^ 2)) * x := by gcongr
  calc
    _ ≤ (8 * (A * (9 * L ^ 2)) * x) / T :=
      div_le_div₀ (by positivity) hnum hT0 hUI.1
    _ = _ := by dsimp [L]; ring



/-- The nonprincipal rectangle identity turns bounds on three edges into a Perron remainder.
The zeros and multiplicities are exactly LZeros and LMult. This is not a psi estimate.
Auxiliary contour assembly for Davenport chapter 19 page 120.
-/
theorem character_rectangle_error_GRH574 (hG : LeanLab.DERZ1997.GRH)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x c T A B : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hf : (LeanLab.DERZ1997.Decomp1529a.LZeros χ T).Finite)
    (hbd : ∀ z ∈ RectangleBorder (⟨1 / 8, -T⟩ : ℂ) ⟨c, T⟩,
      DirichletCharacter.LFunction χ z ≠ 0)
    (hleft : ‖∫ t in (-T)..T,
      -(deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + t * I)) *
          (x : ℂ) ^ ((1 / 8 : ℂ) + t * I) / ((1 / 8 : ℂ) + t * I)‖ ≤ A)
    (hhor : ∀ y ∈ ({T, -T} : Set ℝ),
      ‖∫ σ in (1 / 8 : ℝ)..c,
        -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)) *
            (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤ B) :
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
      -(deriv (DirichletCharacter.LFunction χ) ((c : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((c : ℂ) + t * I)) *
          (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) +
      ∑ ρ ∈ hf.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        A + 2 * B := by
  let F : ℂ → ℂ := fun s => -(deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s
  let V : ℝ → ℂ := fun a => ∫ t in (-T)..T, F ((a : ℂ) + t * I)
  let H : ℝ → ℂ := fun y => ∫ σ in (1 / 8 : ℝ)..c, F ((σ : ℂ) + y * I)
  let r : ℂ := 1 / (2 * Real.pi)
  let s : ℂ := 1 / (2 * Real.pi * I)
  let Z : ℂ := ∑ ρ ∈ hf.toFinset,
    (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  have he : RectangleIntegral' F (⟨1 / 8, -T⟩ : ℂ) ⟨c, T⟩ =
      r * (V c - V (1 / 8)) + s * (H (-T) - H T) := by
    simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
    dsimp [r, s, V, H]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [div_mul_eq_mul_div, one_mul]
    field_simp
    ring
  have hrect := character_contour_GRH266 hG χ hχ hx hc hT hbd hf
  change RectangleIntegral' F (⟨1 / 8, -T⟩ : ℂ) ⟨c, T⟩ = -Z at hrect
  rw [he] at hrect
  have hid : r * V c + Z = r * V (1 / 8) - s * (H (-T) - H T) := by
    linear_combination hrect
  have hr : ‖r‖ ≤ 1 := by
    dsimp [r]
    norm_num only [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact (div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr (by linarith [Real.pi_gt_three])
  have hs : ‖s‖ ≤ 1 := by
    have hh : s = r / I := by dsimp [r, s]; field_simp
    rw [hh, norm_div, norm_I, div_one]
    exact hr
  change ‖r * V c + Z‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖r * V (1 / 8)‖ + ‖s * (H (-T) - H T)‖ := norm_sub_le _ _
    _ ≤ ‖V (1 / 8)‖ + (‖H (-T)‖ + ‖H T‖) := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hr)
        ((mul_le_of_le_one_left (norm_nonneg _) hs).trans (norm_sub_le _ _))
    _ ≤ _ := by
      have hb := hhor (-T) (by simp)
      have ht := hhor T (by simp)
      have hl : ‖V (1 / 8)‖ ≤ A := by simpa [V, F] using hleft
      change ‖H (-T)‖ ≤ B at hb
      change ‖H T‖ ≤ B at ht
      linarith



/-- A conductor-uniform unsmoothed character contour remainder at a selected height.
This estimates the Perron integral plus its finite zero sum. It contains no psi term.
Auxiliary contour result for Davenport chapter 19 page 120 and chapter 20 page 125.
-/
theorem character_selected_contour_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x → ∃ U ∈ Set.Icc T (T + 1),
        ∀ hf : (LeanLab.DERZ1997.Decomp1529a.LZeros χ U).Finite,
          ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-U)..U,
            -(deriv (DirichletCharacter.LFunction χ) (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
              DirichletCharacter.LFunction χ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) *
                (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
                  (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) +
            ∑ ρ ∈ hf.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
              C * (x * Real.log ((q : ℝ) * x) ^ 2 / T + Real.sqrt x +
                Real.log ((q : ℝ) * x) ^ 2) := by
  obtain ⟨A, hA, hleft⟩ := character_left_budget_GRH574 hG
  obtain ⟨B, hB, hhorizontal⟩ := character_horizontal_budget_GRH574 hG
  refine ⟨A + 2 * B, by positivity, ?_⟩
  intro q _ χ hχ x T hx hT hTx
  obtain ⟨U, hUI, hhor⟩ := hhorizontal q χ hχ x T hx hT hTx
  refine ⟨U, hUI, ?_⟩
  intro hf
  let c : ℝ := 1 + 1 / Real.log x
  let L : ℝ := Real.log ((q : ℝ) * x)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr hlogx]
  have hU : 0 < U := by linarith [hUI.1]
  have hbd : ∀ z ∈ RectangleBorder (⟨1 / 8, -U⟩ : ℂ) ⟨c, U⟩,
      DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz hzero
    have hzr := rectangleBorder_subset_rectangle (⟨1 / 8, -U⟩ : ℂ) ⟨c, U⟩ hz
    change z.re ∈ Set.uIcc (1 / 8 : ℝ) c ∧ z.im ∈ Set.uIcc (-U) U at hzr
    rw [Set.uIcc_of_le (by linarith : (1 / 8 : ℝ) ≤ c)] at hzr
    have hr0 : 0 < z.re := by linarith [hzr.1.1]
    have hr1 : z.re < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hzero
    have hline := hG q χ z hzero hr0 hr1
    have hσ : z.re ∈ Set.Icc (1 / 8 : ℝ) (5 / 2) := by rw [hline]; constructor <;> norm_num
    have hcases : z.im = -U ∨ z.re = 1 / 8 ∨ z.im = U ∨ z.re = c := by
      simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm] at hz
      rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    rcases hcases with hi | hr | hi | hr
    · have he : (z.re : ℂ) + I * (-U : ℝ) = z := by apply Complex.ext <;> simp [hi]
      exact ((hhor (-U) (by simp)).1 z.re hσ) (by rwa [he])
    · linarith
    · have he : (z.re : ℂ) + I * (U : ℝ) = z := by apply Complex.ext <;> simp [hi]
      exact ((hhor U (by simp)).1 z.re hσ) (by rwa [he])
    · linarith
  have hl := hleft q χ hχ x U hx hU.le (by linarith [hUI.2])
  have hl' : ‖∫ t in (-U)..U,
      -(deriv (DirichletCharacter.LFunction χ) ((1 / 8 : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((1 / 8 : ℂ) + t * I)) *
          (x : ℂ) ^ ((1 / 8 : ℂ) + t * I) / ((1 / 8 : ℂ) + t * I)‖ ≤
      A * (Real.sqrt x + L ^ 2) := by simpa only [mul_comm I] using hl.2
  have hh' (y : ℝ) (hy : y ∈ ({U, -U} : Set ℝ)) :
      ‖∫ σ in (1 / 8 : ℝ)..c,
        -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)) *
            (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤ B * x * L ^ 2 / T := by
    simpa only [mul_comm I] using (hhor y hy).2.2
  have hb := character_rectangle_error_GRH574 hG χ hχ hx0 hc hU hf hbd hl' hh'
  refine hb.trans ?_
  have hm : 0 ≤ x * L ^ 2 / T := by positivity
  have he : 0 ≤ Real.sqrt x + L ^ 2 := by positivity
  change A * (Real.sqrt x + L ^ 2) + 2 * (B * x * L ^ 2 / T) ≤
    (A + 2 * B) * (x * L ^ 2 / T + Real.sqrt x + L ^ 2)
  rw [show 2 * (B * x * L ^ 2 / T) = (2 * B) * (x * L ^ 2 / T) by ring]
  calc
    _ ≤ (A + 2 * B) * (Real.sqrt x + L ^ 2) +
        (A + 2 * B) * (x * L ^ 2 / T) :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith) he)
        (mul_le_mul_of_nonneg_right (by linarith) hm)
    _ = _ := by ring


/-- The selected Perron integral can use the original zero cutoff T.
The uniform local band count pays for the transfer from the selected height U.
Auxiliary unrestricted-height assembly for Davenport chapter 19 page 120.
The remaining psi connection is the separate truncated Perron error.
-/
theorem character_cutoff_contour_GRH574 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x → ∃ U ∈ Set.Icc T (T + 1),
        ∀ hf : (LeanLab.DERZ1997.Decomp1529a.LZeros χ T).Finite,
          ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-U)..U,
            -(deriv (DirichletCharacter.LFunction χ) (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
              DirichletCharacter.LFunction χ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) *
                (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
                  (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) +
            ∑ ρ ∈ hf.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
              C * (x * Real.log ((q : ℝ) * x) ^ 2 / T + Real.sqrt x +
                Real.log ((q : ℝ) * x) ^ 2) := by
  obtain ⟨A, hA, hcontour⟩ := character_selected_contour_GRH574 hG
  obtain ⟨B, hB, htransfer⟩ := character_height_transfer_GRH574 hG
  refine ⟨A + 6 * B, by positivity, ?_⟩
  intro q _ χ hχ x T hx hT hTx
  obtain ⟨U, hUI, herror⟩ := hcontour q χ hχ x T hx hT hTx
  refine ⟨U, hUI, ?_⟩
  intro hfT
  let hfU := LeanLab.DERZ1997.Decomp1529a.LZeros_finite χ U
  let Z : ℝ → ℂ := fun V => ∑ ρ ∈ (LeanLab.DERZ1997.Decomp1529a.LZeros_finite χ V).toFinset,
    (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let P : ℂ := (1 / (2 * Real.pi) : ℂ) * (∫ t in (-U)..U,
    -(deriv (DirichletCharacter.LFunction χ) (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
      DirichletCharacter.LFunction χ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)) *
        (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
          (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I))
  let L : ℝ := Real.log ((q : ℝ) * x)
  let H : ℝ := Real.log ((q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hH : 0 ≤ H := Real.log_nonneg (by nlinarith)
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
  have hlog3 : Real.log 3 ≤ 2 * L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hHL : H ≤ 3 * L := by
    have hh : H ≤ Real.log (3 * ((q : ℝ) * x)) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hh
    change H ≤ Real.log 3 + L at hh
    linarith
  have hHsq : H ≤ 6 * L ^ 2 := by
    have := Real.log_two_gt_d9
    nlinarith
  have hsqrt : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hnum : B * Real.sqrt x * H ≤ 6 * B * x * L ^ 2 := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hB.le) hHsq hH
      (mul_nonneg hB.le hx0.le)
    convert hh using 1; ring
  have hdiff : ‖Z U - Z T‖ ≤ 6 * B * x * L ^ 2 / T := by
    have hh := htransfer q χ hχ x T U (by linarith) hT hUI.1 hUI.2
      (LeanLab.DERZ1997.Decomp1529a.LZeros_finite χ T) hfU
    exact hh.trans (div_le_div_of_nonneg_right hnum hT0.le)
  have hsel : ‖P + Z U‖ ≤ A * (x * L ^ 2 / T + Real.sqrt x + L ^ 2) := herror hfU
  have htri : ‖P + Z T‖ ≤ ‖P + Z U‖ + ‖Z U - Z T‖ := by
    have he : P + Z T = (P + Z U) - (Z U - Z T) := by ring
    rw [he]
    exact norm_sub_le _ _
  change ‖P + Z T‖ ≤ (A + 6 * B) * (x * L ^ 2 / T + Real.sqrt x + L ^ 2)
  have hM : 0 ≤ x * L ^ 2 / T := by positivity
  have hE : 0 ≤ Real.sqrt x + L ^ 2 := by positivity
  have hb : 6 * B * x * L ^ 2 / T = (6 * B) * (x * L ^ 2 / T) := by ring
  rw [hb] at hdiff
  calc
    _ ≤ A * (x * L ^ 2 / T + Real.sqrt x + L ^ 2) + (6 * B) * (x * L ^ 2 / T) :=
      htri.trans (add_le_add hsel hdiff)
    _ ≤ A * (x * L ^ 2 / T + Real.sqrt x + L ^ 2) +
        (6 * B) * (x * L ^ 2 / T + Real.sqrt x + L ^ 2) := by
      gcongr
      linarith
    _ = _ := by ring

/-- On the Perron line the twisted von Mangoldt series is the negative L-logarithmic derivative.
This bridges the existing character Perron error to the contour estimates.
Davenport chapter 17 pages 105 to 106 and chapter 19 page 120, auxiliary series identity.
The proof reuses Mathlib's twisted von Mangoldt and continuation derivative identities.
-/
theorem character_perron_logderiv574 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x c T : ℝ) (hc : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
      LSeries (fun n => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
    (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
      -(deriv (DirichletCharacter.LFunction χ) ((c : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((c : ℂ) + t * I)) *
          (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have hs : 1 < ((c : ℂ) + t * I).re := by simpa using hc
  have hh := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    ← DirichletCharacter.LFunction_eq_LSeries χ hs, neg_div] at hh
  change LSeries (fun n => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((c : ℂ) + t * I) = _ at hh
  dsimp only
  rw [hh]

end LeanLab.DERZ1997.Decomp574a
