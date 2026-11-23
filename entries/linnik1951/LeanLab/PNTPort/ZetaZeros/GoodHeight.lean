module

public import LeanLab.PNTPort.ZetaZeros.Sym
public import LeanLab.PNTPort.ZetaZeros.LocalPF

/-!
# Good heights: `|ζ'/ζ(σ + iT')| ≪ log² T` on `1/2 ≤ σ ≤ 2` for some `T'` in every `[T, T + 1]`

Lab proof, unit U-5264, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
Davenport ch. 17, no cited input; from `zero_count` of Sym.lean and `logDeriv_local` of
LocalPF.lean. The horizontal segments a contour shift for an explicit formula needs.

* `ord_pos`: at a zero `ρ ≠ 1` of `ζ` the order is at least `1`.
* `exists_far`: for a finite set `G` of reals, some `T'` in `[T, T + 1]` keeps distance at least
  `1 / (2 (#G + 1))` from every point of `G`.
* `zero_count_two`: zeros with `|Im ρ - t| ≤ 2` are finite and number `O(log t)`, `t ≥ 5`.
* `good_height`: an absolute `C` such that for every `T ≥ 5` there is `T'` in `[T, T + 1]` with
  `ζ(σ + iT') ≠ 0` and `‖ζ'/ζ(σ + iT')‖ ≤ C log² T` for every `σ` in `[1/2, 2]`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology

local notation "ζ" => riemannZeta

/-- At a zero `ρ ≠ 1` of `ζ` the order is at least `1`. -/
theorem ord_pos {ρ : ℂ} (hρ : ζ ρ = 0) (h1 : ρ ≠ 1) : 1 ≤ analyticOrderNatAt ζ ρ := by
  have hU : AnalyticOnNhd ℂ ζ ({1}ᶜ : Set ℂ) := fun z hz => analyticAt_riemannZeta hz
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have h2 : analyticOrderAt ζ 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    simp
  have htop : analyticOrderAt ζ ρ ≠ ⊤ :=
    hU.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := ρ)
      (by simp) (by simpa using h1) h2
  have h0 : analyticOrderAt ζ ρ ≠ 0 := by
    rw [ne_eq, analyticOrderAt_eq_zero]
    push_neg
    exact ⟨analyticAt_riemannZeta h1, hρ⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
  rw [← hn] at h0
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h0)

/-- Pigeonhole: some point of `[T, T + 1]` is at least `1 / (2 (#G + 1))` from all of `G`. -/
theorem exists_far (G : Finset ℝ) (T : ℝ) :
    ∃ T' ∈ Icc T (T + 1), ∀ γ ∈ G, 1 / (2 * ((G.card : ℝ) + 1)) ≤ |T' - γ| := by
  set n := G.card
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  let p : ℕ → ℝ := fun k => T + k / ((n : ℝ) + 1)
  -- the bad set of indices
  set Bad := (Finset.range (n + 1)).filter (fun k => ∃ γ ∈ G, |p k - γ| < δ) with hBad
  have hone : ∀ γ ∈ G, ((Finset.range (n + 1)).filter (fun k => |p k - γ| < δ)).card ≤ 1 := by
    intro γ _
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    have hd : 1 / ((n : ℝ) + 1) ≤ |p a - p b| := by
      have e : p a - p b = ((a : ℝ) - b) / ((n : ℝ) + 1) := by
        simp only [p]; field_simp; ring
      rw [e, abs_div, abs_of_pos hn1]
      apply div_le_div_of_nonneg_right _ hn1.le
      have : (a : ℤ) ≠ b := by exact_mod_cast hab
      have h1 : (1 : ℤ) ≤ |(a : ℤ) - b| := Int.one_le_abs (sub_ne_zero.mpr this)
      have : ((1 : ℤ) : ℝ) ≤ ((|(a : ℤ) - b| : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at this; exact this
    have htri : |p a - p b| ≤ |p a - γ| + |p b - γ| := by
      calc |p a - p b| = |(p a - γ) - (p b - γ)| := by ring_nf
        _ ≤ |p a - γ| + |p b - γ| := abs_sub _ _
    have h2δ : 2 * δ = 1 / ((n : ℝ) + 1) := by rw [hδ]; field_simp
    linarith [ha.2, hb.2]
  have hsub : Bad ⊆ G.biUnion (fun γ => (Finset.range (n + 1)).filter (fun k => |p k - γ| < δ)) := by
    intro k hk
    rw [hBad, Finset.mem_filter] at hk
    obtain ⟨γ, hγ, hk2⟩ := hk.2
    rw [Finset.mem_biUnion]
    exact ⟨γ, hγ, Finset.mem_filter.mpr ⟨hk.1, hk2⟩⟩
  have hcard : Bad.card ≤ n := by
    calc Bad.card ≤ (G.biUnion fun γ => (Finset.range (n + 1)).filter
          (fun k => |p k - γ| < δ)).card := Finset.card_le_card hsub
      _ ≤ ∑ γ ∈ G, ((Finset.range (n + 1)).filter (fun k => |p k - γ| < δ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ G, 1 := Finset.sum_le_sum hone
      _ = n := by simp [n]
  have hex : ∃ k ∈ Finset.range (n + 1), k ∉ Bad := by
    by_contra h
    push_neg at h
    have : Finset.range (n + 1) ⊆ Bad := h
    have := Finset.card_le_card this
    simp at this; omega
  obtain ⟨k, hk, hkB⟩ := hex
  rw [Finset.mem_range] at hk
  refine ⟨p k, ⟨?_, ?_⟩, ?_⟩
  · simp only [p]; have : (0 : ℝ) ≤ k / ((n : ℝ) + 1) := by positivity
    linarith
  · simp only [p]
    have : (k : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1]; exact_mod_cast hk.le
    linarith
  · intro γ hγ
    by_contra hlt
    push_neg at hlt
    exact hkB (by rw [hBad, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hk, γ, hγ, hlt⟩)

/-- A union bound for nonnegative sums over a `biUnion`. -/
lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α] [DecidableEq ι] (s : Finset ι)
    (S : ι → Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion S, f x ≤ ∑ i ∈ s, ∑ x ∈ S i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hu := Finset.sum_union_inter (s₁ := S i) (s₂ := s.biUnion S) (f := f)
    have hn : 0 ≤ ∑ x ∈ S i ∩ s.biUnion S, f x := Finset.sum_nonneg (fun x _ => hf x)
    linarith

/-- The zeros with `|Im ρ - t| ≤ 2`. -/
def Z2 (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ |ρ.im - t| ≤ 2}

/-- **Zeros with `|Im ρ - t| ≤ 2` number `O(log t)`**, `t ≥ 5`. -/
theorem zero_count_two : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 5 ≤ t →
    ∃ hfin : (Z2 t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) ≤ C * Real.log t := by
  obtain ⟨C, hC, hA⟩ := zero_count
  refine ⟨10 * C, by positivity, fun t ht => ?_⟩
  -- five windows at t + j·4/5 - 8/5, j = 0..4
  let c : ℕ → ℝ := fun j => t + 4 / 5 * j - 8 / 5
  have hc3 : ∀ j ∈ Finset.range 5, 3 ≤ |c j| := by
    intro j _
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [c]; rw [abs_of_nonneg (by linarith)]; linarith
  have hfins : ∀ j ∈ Finset.range 5, (ZA (c j)).Finite := fun j hj => (hA (c j) (hc3 j hj)).1
  have hcover : Z2 t ⊆ ⋃ j ∈ Finset.range 5, ZA (c j) := by
    intro ρ ⟨hz, hi⟩
    rw [Set.mem_iUnion₂]
    obtain ⟨h1, h2⟩ := abs_le.mp hi
    -- pick j = round((Im ρ - t + 8/5) · 5/4)
    have key : ∃ j : ℕ, j < 5 ∧ |ρ.im - c j| ≤ 2 / 5 := by
      by_cases a0 : ρ.im - t ≤ -6 / 5
      · exact ⟨0, by norm_num, by simp only [c]; rw [abs_le]; push_cast; constructor <;> linarith⟩
      by_cases a1 : ρ.im - t ≤ -2 / 5
      · exact ⟨1, by norm_num, by simp only [c]; rw [abs_le]; push_cast; constructor <;> linarith⟩
      by_cases a2 : ρ.im - t ≤ 2 / 5
      · exact ⟨2, by norm_num, by simp only [c]; rw [abs_le]; push_cast; constructor <;> linarith⟩
      by_cases a3 : ρ.im - t ≤ 6 / 5
      · exact ⟨3, by norm_num, by simp only [c]; rw [abs_le]; push_cast; constructor <;> linarith⟩
      · exact ⟨4, by norm_num, by simp only [c]; rw [abs_le]; push_cast; constructor <;> linarith⟩
    obtain ⟨j, hj, hji⟩ := key
    exact ⟨j, Finset.mem_range.mpr hj, hz, hji⟩
  have hfinU : (⋃ j ∈ Finset.range 5, ZA (c j)).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) hfins
  have hfin : (Z2 t).Finite := hfinU.subset hcover
  refine ⟨hfin, ?_⟩
  -- the finset of the union
  set U := (Finset.range 5).attach.biUnion
    (fun j => (hfins j.1 j.2).toFinset) with hU
  have hsub : hfin.toFinset ⊆ U := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have := hcover hρ
    rw [Set.mem_iUnion₂] at this
    obtain ⟨j, hj, hρj⟩ := this
    rw [hU, Finset.mem_biUnion]
    exact ⟨⟨j, hj⟩, Finset.mem_attach _ _, (Set.Finite.mem_toFinset _).mpr hρj⟩
  have hlog : ∀ j ∈ Finset.range 5, Real.log |c j| ≤ 2 * Real.log t := by
    intro j hj
    have hj5 : (j : ℝ) ≤ 4 := by
      have := Finset.mem_range.mp hj; exact_mod_cast (by omega : j ≤ 4)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hpos : 0 < |c j| := by linarith [hc3 j hj]
    calc Real.log |c j| ≤ Real.log (t ^ 2) := by
          apply Real.log_le_log hpos
          simp only [c]; rw [abs_of_nonneg (by linarith)]; nlinarith
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  calc (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ))
      ≤ ∑ ρ ∈ U, (analyticOrderNatAt ζ ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ (Finset.range 5).attach,
          ∑ ρ ∈ (hfins j.1 j.2).toFinset, (analyticOrderNatAt ζ ρ : ℝ) :=
        sum_biUnion_le_of_nonneg _ _ _ (fun _ => Nat.cast_nonneg _)
    _ ≤ ∑ _j ∈ (Finset.range 5).attach, C * (2 * Real.log t) := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨hf', hs'⟩ := hA (c j.1) (hc3 j.1 j.2)
        calc (∑ ρ ∈ (hfins j.1 j.2).toFinset, (analyticOrderNatAt ζ ρ : ℝ))
            = ∑ ρ ∈ hf'.toFinset, (analyticOrderNatAt ζ ρ : ℝ) := rfl
          _ ≤ C * Real.log |c j.1| := hs'
          _ ≤ C * (2 * Real.log t) := mul_le_mul_of_nonneg_left (hlog j.1 j.2) hC.le
    _ = 10 * C * Real.log t := by simp; ring

/-- **Good heights.** For every `T ≥ 5` some `T'` in `[T, T + 1]` has `ζ(σ + iT') ≠ 0` and
`‖ζ'/ζ(σ + iT')‖ ≤ C log² T` for all `σ` in `[1/2, 2]`. -/
theorem good_height : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
    ∀ σ ∈ Icc (1 / 2 : ℝ) 2, ζ (σ + I * T') ≠ 0 ∧
      ‖deriv ζ (σ + I * T') / ζ (σ + I * T')‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨C1, hC1, h2⟩ := zero_count_two
  obtain ⟨C2, hC2, hL⟩ := logDeriv_local
  refine ⟨2 * C2 + 4 * C1 + 8 * C1 ^ 2, by positivity, fun T hT => ?_⟩
  set t0 := T + 1 / 2 with ht0def
  have ht0 : 5 ≤ t0 := by linarith
  obtain ⟨hfW, hsW⟩ := h2 t0 ht0
  set Zw := hfW.toFinset with hZw
  set G := Zw.image Complex.im with hG
  set M : ℝ := ∑ ρ ∈ Zw, (analyticOrderNatAt ζ ρ : ℝ) with hM
  have hGcard : (G.card : ℝ) ≤ M := by
    have h1 : G.card ≤ Zw.card := Finset.card_image_le
    have h2' : (Zw.card : ℝ) ≤ M := by
      rw [hM, Finset.card_eq_sum_ones, Nat.cast_sum]
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [hZw, Set.Finite.mem_toFinset] at hρ
      have hne : ρ ≠ 1 := by
        intro h; rw [h] at hρ
        have := hρ.2; simp at this
        rw [abs_le] at this; linarith [this.1]
      exact_mod_cast ord_pos hρ.1 hne
    calc (G.card : ℝ) ≤ Zw.card := by exact_mod_cast h1
      _ ≤ M := h2'
  obtain ⟨T', hT'I, hfar⟩ := exists_far G T
  set δ : ℝ := 1 / (2 * ((G.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨T', hT'I, fun σ hσ => ?_⟩
  obtain ⟨hT1, hT2⟩ := hT'I
  obtain ⟨hσ1, hσ2⟩ := hσ
  set s : ℂ := σ + I * T' with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T' := by simp [hs]
  have hsc : ‖s - cen T'‖ ≤ 1 := by
    have e : s - cen T' = ((σ - 3 / 2 : ℝ) : ℂ) := by
      simp only [hs, cen]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hT'3 : 3 ≤ |T'| := by rw [abs_of_nonneg (by linarith)]; linarith
  -- membership of a zero near `T'` in `Zw`, so its height lies in `G`
  have hfarρ : ∀ ρ : ℂ, ζ ρ = 0 → |ρ.im - T'| ≤ 27 / 25 → δ ≤ |T' - ρ.im| := by
    intro ρ hz hi
    have hmem : ρ ∈ Zw := by
      rw [hZw, Set.Finite.mem_toFinset]
      refine ⟨hz, ?_⟩
      rw [abs_le] at hi ⊢; constructor <;> linarith [hi.1, hi.2]
    exact hfar ρ.im (Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩)
  have hzs : ζ s ≠ 0 := by
    intro hz
    have := hfarρ s hz (by rw [hsim, sub_self, abs_zero]; norm_num)
    rw [hsim, sub_self, abs_zero] at this
    linarith
  refine ⟨hzs, ?_⟩
  obtain ⟨hfin, hb⟩ := hL T' hT'3
  have hloc := hb s hsc hzs
  -- the zero sum
  have hsub : hfin.toFinset ⊆ Zw := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rw [hZw, Set.Finite.mem_toFinset]
    refine ⟨hρ.1, ?_⟩
    have him : |(ρ - cen T').im| ≤ ‖ρ - cen T'‖ := Complex.abs_im_le_norm _
    have e : (ρ - cen T').im = ρ.im - T' := by simp [cen]
    rw [e] at him
    have := hρ.2
    rw [abs_le] at him ⊢; constructor <;> linarith [him.1, him.2]
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤ (analyticOrderNatAt ζ ρ : ℝ) / δ := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hi : |ρ.im - T'| ≤ 27 / 25 := by
      have him : |(ρ - cen T').im| ≤ ‖ρ - cen T'‖ := Complex.abs_im_le_norm _
      have e : (ρ - cen T').im = ρ.im - T' := by simp [cen]
      rw [e] at him; linarith [hρ.2]
    have hd := hfarρ ρ hρ.1 hi
    have hn : δ ≤ ‖s - ρ‖ := by
      have : |(s - ρ).im| ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
      have e : (s - ρ).im = T' - ρ.im := by simp [hsim]
      rw [e] at this; linarith
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδpos hn
  have hsumle : ‖∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤ M / δ := by
    calc _ ≤ ∑ ρ ∈ hfin.toFinset, ‖(analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ) / δ := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) / δ := by rw [Finset.sum_div]
      _ ≤ M / δ := by
          apply div_le_div_of_nonneg_right _ hδpos.le
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  -- logs
  have hlT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlog2 : ∀ x : ℝ, T ≤ x → x ≤ T + 1 → Real.log x ≤ 2 * Real.log T := by
    intro x hx1 hx2
    calc Real.log x ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hM : M ≤ 2 * C1 * Real.log T := by
    calc M ≤ C1 * Real.log t0 := hsW
      _ ≤ C1 * (2 * Real.log T) := mul_le_mul_of_nonneg_left (hlog2 t0 (by linarith) (by linarith)) hC1.le
      _ = 2 * C1 * Real.log T := by ring
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hMd : M / δ ≤ 2 * M * (M + 1) := by
    rw [hδ, div_div_eq_mul_div, div_one]
    have : (G.card : ℝ) + 1 ≤ M + 1 := by linarith
    nlinarith
  have hT'log : Real.log |T'| ≤ 2 * Real.log T := by
    rw [abs_of_nonneg (by linarith)]; exact hlog2 T' hT1 hT2
  have htri : ‖deriv ζ s / ζ s‖ ≤ C2 * Real.log |T'| + M / δ := by
    have := norm_sub_le_norm_sub_add_norm_sub (deriv ζ s / ζ s)
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)) 0
    rw [sub_zero, sub_zero] at this
    linarith
  have hL1 : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  calc ‖deriv ζ s / ζ s‖ ≤ C2 * Real.log |T'| + M / δ := htri
    _ ≤ C2 * (2 * Real.log T) + 2 * M * (M + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hT'log hC2.le) hMd
    _ ≤ C2 * (2 * Real.log T) + 2 * (2 * C1 * Real.log T) * (2 * C1 * Real.log T + 1) := by
        gcongr
    _ = 2 * C2 * Real.log T + 4 * C1 * Real.log T + 8 * C1 ^ 2 * Real.log T ^ 2 := by ring
    _ ≤ (2 * C2 + 4 * C1 + 8 * C1 ^ 2) * Real.log T ^ 2 := by nlinarith

end LeanLab.PNTPort.ZetaZeros

