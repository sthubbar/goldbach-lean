module

public import LeanLab.Linnik.ExplicitFormula.Final
public import LeanLab.Linnik.ExplicitFormula.Cesaro
public import LeanLab.Linnik.ExplicitFormula.ZeroTerm

/-!
# Short interval sums of `n χ(n) Λ(n)` from the explicit formula, Gallagher 1970 Section 7

AI wrote the Lean code. Binary Goldbach is OPEN.
Second differences of `J(x) = x² S(x, χ)` with step `h`, the explicit formula
`explicit_formula_primitive` at the four points `b, b + h, a, a + h`, the zero term bounds of
ZeroTerm.lean below height `T` and the tail bound `zero_sum_tail` above it. The pole term at `1`
and at most one copy `e ≤ 1` of a real zero `γ` are kept as main terms.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- Davenport ch. 12, elementary: a zero in `Zall χ` has multiplicity at least one, since
`L(s, χ)` is analytic on the connected set `ℂ \ {1}` and nonzero at `2`. -/
lemma one_le_mult_of_mem_Zall {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hρ : ρ ∈ Zall χ) : 1 ≤ mult χ ρ := by
  obtain ⟨h0, -, h1⟩ := hρ
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hU : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have h2 : analyticOrderAt χ.LFunction 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)))]
    simp
  have htop : analyticOrderAt χ.LFunction ρ ≠ ⊤ :=
    hU.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := ρ)
      (by norm_num) h1 h2
  have hne0 : analyticOrderAt χ.LFunction ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push Not
    exact ⟨hU ρ h1, h0⟩
  unfold mult analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)

/-- elementary: `x² zterm(x, ρ) = m(ρ) D_ρ(x)` for `x > 0`. -/
lemma sq_mul_zterm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ) ^ 2 * zterm χ x ρ = (mult χ ρ : ℂ) * Dz ρ x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold zterm Dz
  rw [cpow_add _ _ hx0, show ((x : ℂ) ^ (2 : ℂ)) = (x : ℂ) ^ (2 : ℕ) from cpow_ofNat (x : ℂ) 2]
  ring

/-- elementary: `D_1(u) = u³/6`. -/
lemma Dz_one (u : ℝ) : Dz 1 u = (u : ℂ) ^ 3 / 6 := by
  unfold Dz
  rw [show (1 : ℂ) + 2 = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast]
  norm_num

/-- elementary: a tsum minus a finite subsum over `S ⊆ Z` is bounded by any bound on finite sums
off `S`. -/
lemma norm_tsum_sub_sum_le {Z : Set ℂ} (F : ℂ → ℂ) (hF : Summable (fun ρ : Z => F ρ))
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ Z) {B : ℝ}
    (hB : ∀ U : Finset ℂ, (∀ ρ ∈ U, ρ ∈ Z ∧ ρ ∉ S) → ‖∑ ρ ∈ U, F ρ‖ ≤ B) :
    ‖(∑' ρ : Z, F ρ) - ∑ ρ ∈ S, F ρ‖ ≤ B := by
  classical
  have ht : Filter.Tendsto (fun u : Finset Z => ‖(∑ ρ ∈ u, F ρ) - ∑ ρ ∈ S, F ρ‖) Filter.atTop
      (nhds ‖(∑' ρ : Z, F ρ) - ∑ ρ ∈ S, F ρ‖) :=
    ((hF.hasSum : Filter.Tendsto (fun u : Finset Z => ∑ ρ ∈ u, F ρ) Filter.atTop
      (nhds (∑' ρ : Z, F ρ))).sub_const _).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop (S.subtype (· ∈ Z))] with u hu
  rw [show ∑ ρ ∈ u, F ρ = ∑ ρ ∈ u.map (Function.Embedding.subtype _), F ρ from
    (Finset.sum_map u (Function.Embedding.subtype _) F).symm]
  have hSU : S ⊆ u.map (Function.Embedding.subtype _) := fun ρ hρ =>
    mem_map.2 ⟨⟨ρ, hS ρ hρ⟩, hu (mem_subtype.2 hρ), rfl⟩
  rw [← Finset.sum_sdiff hSU, add_sub_cancel_right]
  refine hB _ (fun ρ hρ => ?_)
  rw [mem_sdiff, mem_map] at hρ
  obtain ⟨⟨a, _, rfl⟩, h2⟩ := hρ
  exact ⟨a.2, h2⟩


/-- The explicit formula error `S(x, χ) - [q = 1] x/6 + Σ_ρ zterm`, Davenport ch. 17 and 19. -/
noncomputable def efErr {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  cesaroChi χ x - (if q = 1 then (x : ℂ) / 6 else 0) + ∑' ρ : Zall χ, zterm χ x ρ

/-- elementary, from the definitions: `J(x) = [q = 1] D_1(x) - Σ_ρ m(ρ) D_ρ(x) + x² efErr(x)`. -/
lemma Jchi_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    Jchi χ x = (if q = 1 then Dz 1 x else 0) - ∑' ρ : Zall χ, (mult χ ρ : ℂ) * Dz ρ x +
      (x : ℂ) ^ 2 * efErr χ x := by
  have e1 : ∑' ρ : Zall χ, (mult χ ρ : ℂ) * Dz ρ x = (x : ℂ) ^ 2 * ∑' ρ : Zall χ, zterm χ x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => (sq_mul_zterm χ hx ρ).symm
  rw [e1]
  unfold Jchi efErr
  split_ifs
  · rw [Dz_one]; ring
  · ring

/-- `ρ ↦ m(ρ) D_ρ(x)` is summable over `Zall χ` for primitive `χ` and `x > 0`, from
`summable_zterm`. -/
lemma summable_mult_Dz {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) : Summable (fun ρ : Zall χ => (mult χ ρ : ℂ) * Dz ρ x) := by
  have := (summable_zterm hχ hx).mul_left ((x : ℂ) ^ 2)
  refine this.congr fun ρ => ?_
  exact sq_mul_zterm χ hx ρ

/-- The sharp window sum from the second difference of `J`, Davenport ch. 17 via
`first_difference`, elementary. -/
lemma sharp_window_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a b : ℕ} {h : ℝ}
    (hb : 1 ≤ b) (hba : b ≤ a) (hh1 : 1 ≤ h) (hha : h ≤ a) :
    ‖∑ n ∈ Ioc b a, bCoef χ n - (Jchi χ (a + h) - Jchi χ a - Jchi χ (b + h) + Jchi χ b) / h‖ ≤
      4 * (h + 1) * a * Real.log (2 * a) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  have hh0 : 0 < h := by linarith
  have fa := first_difference χ (x := (a : ℝ)) (h := h) (by linarith) hh0
  have fb := first_difference χ (x := (b : ℝ)) (h := h) (by linarith) hh0
  have ea := first_difference_err_le χ (x := (a : ℝ)) (h := h) (by linarith) hh0
  have eb := first_difference_err_le χ (x := (b : ℝ)) (h := h) (by linarith) hh0
  rw [Nat.floor_natCast] at fa fb ea eb
  have hsplit : ∑ n ∈ range (a + 1), bCoef χ n =
      ∑ n ∈ range (b + 1), bCoef χ n + ∑ n ∈ Ioc b a, bCoef χ n := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : b + 1 ≤ a + 1),
      Finset.Ico_add_one_add_one_eq_Ioc]
  have hh0' : (h : ℂ) ≠ 0 := by exact_mod_cast hh0.ne'
  have key : ∑ n ∈ Ioc b a, bCoef χ n -
      (Jchi χ (a + h) - Jchi χ a - Jchi χ (b + h) + Jchi χ b) / h =
      ((Jchi χ (b + h) - Jchi χ b) / h - ∑ n ∈ range (b + 1), bCoef χ n) -
      ((Jchi χ (a + h) - Jchi χ a) / h - ∑ n ∈ range (a + 1), bCoef χ n) := by
    rw [hsplit]; field_simp; ring
  rw [key]
  have hL1 : Real.log ((a : ℝ) + h) ≤ Real.log (2 * a) := Real.log_le_log (by linarith) (by linarith)
  have hL2 : Real.log ((b : ℝ) + h) ≤ Real.log (2 * a) := Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log ((b : ℝ) + h) := Real.log_nonneg (by linarith)
  have hl0' : 0 ≤ Real.log ((a : ℝ) + h) := Real.log_nonneg (by linarith)
  have b1 : (h + 1) * ((a : ℝ) + h) * Real.log ((a : ℝ) + h) ≤ (h + 1) * (2 * a) * Real.log (2 * a) := by
    gcongr; linarith
  have b2 : (h + 1) * ((b : ℝ) + h) * Real.log ((b : ℝ) + h) ≤ (h + 1) * (2 * a) * Real.log (2 * a) := by
    gcongr; linarith
  calc _ ≤ ‖(Jchi χ (b + h) - Jchi χ b) / h - ∑ n ∈ range (b + 1), bCoef χ n‖ +
        ‖(Jchi χ (a + h) - Jchi χ a) / h - ∑ n ∈ range (a + 1), bCoef χ n‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith

/-- Second difference of `D_ρ` bounded with `(2a)^β`, from `double_diff_le`, for a zero of a
primitive `χ`. -/
lemma D2_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ Zall χ) {a b : ℕ} {h : ℝ} (hb : 1 ≤ b) (hba : b ≤ a) (hh1 : 1 ≤ h) (hha : h ≤ a) :
    ‖Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b‖ ≤ h * (a - b) * (2 * a : ℝ) ^ ρ.re := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  have hre : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
    rcases Zall_nt_or_zero hχ hρ with h' | h'
    · exact ⟨h'.2.1.le, h'.2.2.le⟩
    · rw [h']; simp
  refine (double_diff_le hre.1 hre.2 (by linarith) hba' (by linarith)).trans ?_
  have : ((a : ℝ) + h) ^ ρ.re ≤ (2 * a : ℝ) ^ ρ.re :=
    Real.rpow_le_rpow (by linarith) (by linarith) hre.1
  have hp : 0 ≤ h * ((a : ℝ) - b) := mul_nonneg (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left this hp

/-- The zeros up to height `T`, with the kept real zero removed, Gallagher 1970 Section 7. -/
lemma zero_part_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {a b : ℕ} {h : ℝ} (hb : 1 ≤ b) (hba : b ≤ a) (hh1 : 1 ≤ h) (hha : h ≤ a)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ Zall χ) (e : ℕ) (γ : ℝ) (he1 : e ≤ 1)
    (heγ : e = 1 → (γ : ℂ) ∈ S ∧ 0 < γ) :
    ‖(∑ ρ ∈ S, (mult χ ρ : ℂ) * (Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b) -
        (e : ℂ) * (Dz (γ : ℂ) (a + h) - Dz (γ : ℂ) a - Dz (γ : ℂ) (b + h) + Dz (γ : ℂ) b)) / h‖ ≤
      (a - b : ℝ) * ∑ ρ ∈ S, ((mult χ ρ : ℝ) - (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) *
        (2 * a : ℝ) ^ ρ.re := by
  classical
  set D2 : ℂ → ℂ := fun ρ => Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b with hD2
  set c : ℂ → ℝ := fun ρ => (mult χ ρ : ℝ) - (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0) with hc
  have hc0 : ∀ ρ ∈ S, 0 ≤ c ρ := by
    intro ρ hρ
    have := one_le_mult_of_mem_Zall (hS ρ hρ)
    have h1 : (1 : ℝ) ≤ mult χ ρ := by exact_mod_cast this
    simp only [hc]
    split_ifs <;> linarith
  have hsplit : ∑ ρ ∈ S, (mult χ ρ : ℂ) * D2 ρ - (e : ℂ) * D2 (γ : ℂ) =
      ∑ ρ ∈ S, ((c ρ : ℝ) : ℂ) * D2 ρ := by
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · simp [hc]
    · have hγ := (heγ rfl).1
      have e2 : ∑ ρ ∈ S, ((c ρ : ℝ) : ℂ) * D2 ρ =
          ∑ ρ ∈ S, (mult χ ρ : ℂ) * D2 ρ - ∑ ρ ∈ S, (if ρ = (γ : ℂ) then D2 ρ else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [hc]
        split_ifs with h1 h2 h2
        · push_cast; ring
        · simp_all
        · simp_all
        · push_cast; ring
      rw [e2, Finset.sum_ite_eq' S (γ : ℂ) D2]
      simp only [hγ, ↓reduceIte]
      push_cast; ring
  have hh0 : 0 < h := by linarith
  rw [hsplit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0, div_le_iff₀ hh0]
  calc ‖∑ ρ ∈ S, ((c ρ : ℝ) : ℂ) * D2 ρ‖ ≤ ∑ ρ ∈ S, c ρ * (h * (a - b) * (2 * a : ℝ) ^ ρ.re) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 ρ hρ)]
        exact mul_le_mul_of_nonneg_left (D2_le hχ (hS ρ hρ) hb hba hh1 hha) (hc0 ρ hρ)
    _ = (a - b : ℝ) * (∑ ρ ∈ S, c ρ * (2 * a : ℝ) ^ ρ.re) * h := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ρ _ => by ring

/-- The zero sum above height `T`, from `zero_sum_tail` and `double_diff_le'`, Davenport ch. 17. -/
lemma tail_part_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ (a b : ℕ) (h T : ℝ), 1 ≤ b → b ≤ a → 1 ≤ h → h ≤ a → 1 ≤ T →
    ∀ (S : Finset ℂ), (∀ ρ, ρ ∈ S ↔ ρ ∈ Zall χ ∧ |ρ.im| ≤ T) →
      ‖(∑' ρ : Zall χ, (mult χ ρ : ℂ) * (Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b)) -
        ∑ ρ ∈ S, (mult χ ρ : ℂ) * (Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b)‖ ≤
        C * ((a : ℝ) ^ 3 * Real.log (q * (T + 2)) / T) := by
  obtain ⟨C1, hC1, htail⟩ := zero_sum_tail
  refine ⟨32 * C1, by positivity, fun q _ χ hχ a b h T hb hba hh1 hha hT S hS => ?_⟩
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  have ha1 : (1 : ℝ) ≤ a := hb1.trans hba'
  set F : ℂ → ℂ := fun ρ => (mult χ ρ : ℂ) * (Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b)
    with hF
  have hsum : Summable (fun ρ : Zall χ => F ρ) := by
    have s1 := summable_mult_Dz hχ (x := (a : ℝ) + h) (by linarith)
    have s2 := summable_mult_Dz hχ (x := (a : ℝ)) (by linarith)
    have s3 := summable_mult_Dz hχ (x := (b : ℝ) + h) (by linarith)
    have s4 := summable_mult_Dz hχ (x := (b : ℝ)) (by linarith)
    refine (((s1.sub s2).sub s3).add s4).congr fun ρ => ?_
    simp only [hF]; ring
  refine norm_tsum_sub_sum_le F hsum S (fun ρ hρ => ((hS ρ).1 hρ).1) (fun U hU => ?_)
  have hU' : ∀ ρ ∈ U, ρ ∈ Zall χ ∧ T < |ρ.im| := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hU ρ hρ
    refine ⟨h1, ?_⟩
    by_contra h3
    exact h2 ((hS ρ).2 ⟨h1, not_lt.mp h3⟩)
  have hT0 : 0 < T := by linarith
  have ht := htail q χ hχ T hT U hU'
  have hpt : ∀ ρ ∈ U, ‖F ρ‖ ≤ 32 * a ^ 3 * ((mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖) := by
    intro ρ hρ
    have hz := (hU' ρ hρ).1
    have hre : -1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 := by
      refine ⟨hz.2.1, ?_⟩
      rcases Zall_nt_or_zero hχ hz with h' | h'
      · exact h'.2.2.le
      · rw [h']; simp
    have hd := double_diff_le' hre.1 hre.2 (a := (a : ℝ)) (b := (b : ℝ)) (h := h)
      (by linarith) hba' (by linarith)
    have hp1 : ((a : ℝ) + h) ^ (ρ.re + 2) ≤ ((a : ℝ) + h) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hp2 : ((a : ℝ) + h) ^ (3 : ℝ) ≤ 8 * (a : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have : (a : ℝ) + h ≤ 2 * a := by linarith
      have h0 : 0 ≤ (a : ℝ) + h := by linarith
      calc ((a : ℝ) + h) ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ h0 this 3
        _ = 8 * (a : ℝ) ^ 3 := by ring
    have hn := norm_mul_ge_of_re hre.1
    have hn0 : 0 < ‖(ρ + 1) * (ρ + 2)‖ := by linarith
    simp only [hF]
    rw [norm_mul, Complex.norm_natCast]
    have hm : (0 : ℝ) ≤ mult χ ρ := by positivity
    calc (mult χ ρ : ℝ) * ‖Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b‖
        ≤ (mult χ ρ : ℝ) * (4 * ((a : ℝ) + h) ^ (ρ.re + 2) / ‖(ρ + 1) * (ρ + 2)‖) :=
          mul_le_mul_of_nonneg_left hd hm
      _ ≤ (mult χ ρ : ℝ) * (4 * (8 * (a : ℝ) ^ 3) / ‖(ρ + 1) * (ρ + 2)‖) := by
          gcongr; linarith
      _ = 32 * a ^ 3 * ((mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖) := by ring
  calc ‖∑ ρ ∈ U, F ρ‖ ≤ ∑ ρ ∈ U, 32 * a ^ 3 * ((mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hpt)
    _ = 32 * a ^ 3 * ∑ ρ ∈ U, (mult χ ρ : ℝ) / ‖(ρ + 1) * (ρ + 2)‖ := by rw [Finset.mul_sum]
    _ ≤ 32 * a ^ 3 * (C1 * Real.log (q * (T + 2)) / T) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 32 * C1 * ((a : ℝ) ^ 3 * Real.log (q * (T + 2)) / T) := by ring

/-- One point of the explicit formula error, scaled: `‖x² efErr(x)‖ ≤ 4 C log(q + 2) a^(3/2)` for
`1 ≤ x ≤ 2a`, from `explicit_formula_primitive`, elementary. -/
lemma point_err_le {C : ℝ} (hC : 0 ≤ C) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x a : ℝ} (hx : 1 ≤ x) (hxa : x ≤ 2 * a)
    (hE : ‖efErr χ x‖ ≤ C * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ))) :
    ‖(x : ℂ) ^ 2 * efErr χ x‖ ≤ 4 * C * Real.log (q + 2) * a ^ (3 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlq : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have h1 : x ^ 2 * x ^ (-(1 / 2 : ℝ)) = x ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; norm_num
  have h2 : x ^ (3 / 2 : ℝ) ≤ (2 * a) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hx0.le hxa (by norm_num)
  have h3 : (2 * a) ^ (3 / 2 : ℝ) ≤ 4 * a ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) ha0]
    have : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    have : 0 ≤ a ^ (3 / 2 : ℝ) := by positivity
    nlinarith
  have hx2 : 0 ≤ x ^ 2 := by positivity
  calc x ^ 2 * ‖efErr χ x‖ ≤ x ^ 2 * (C * Real.log (q + 2) * x ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hE hx2
    _ = C * Real.log (q + 2) * (x ^ 2 * x ^ (-(1 / 2 : ℝ))) := by ring
    _ ≤ C * Real.log (q + 2) * (4 * a ^ (3 / 2 : ℝ)) := by
        rw [h1]; gcongr; linarith
    _ = 4 * C * Real.log (q + 2) * a ^ (3 / 2 : ℝ) := by ring

/-- Gallagher 1970 Section 7 for one primitive character, the window `(b, a]`. -/
theorem window_bCoef_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ (a b : ℕ) (h T : ℝ), 1 ≤ b → b ≤ a → 1 ≤ h → h ≤ a → 1 ≤ T →
    ∀ (S : Finset ℂ), (∀ ρ, ρ ∈ S ↔ ρ ∈ Zall χ ∧ |ρ.im| ≤ T) →
    ∀ (e : ℕ) (γ : ℝ), e ≤ 1 → (e = 1 → (γ : ℂ) ∈ S ∧ 0 < γ) →
      ‖∑ n ∈ Ioc b a, bCoef χ n - (if q = 1 then ∑ n ∈ Ioc b a, (n : ℂ) else 0) +
          (e : ℂ) * ∑ n ∈ Ioc b a, (((n : ℝ) ^ γ : ℝ) : ℂ)‖ ≤
        (a - b : ℝ) * ∑ ρ ∈ S, ((mult χ ρ : ℝ) - (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) *
            (2 * a : ℝ) ^ ρ.re +
          C * ((h + 1) * a * Real.log (2 * a) + Real.log (q + 2) * (a : ℝ) ^ (3 / 2 : ℝ) / h +
            (a : ℝ) ^ 3 * Real.log (q * (T + 2)) / (h * T)) := by
  classical
  obtain ⟨C0, hC0, hEF⟩ := explicit_formula_primitive
  obtain ⟨C1, hC1, htl⟩ := tail_part_le
  refine ⟨40 + C1 + 16 * C0, by positivity, ?_⟩
  intro q _ χ hχ a b h T hb hba hh1 hha hT S hS e γ he1 heγ
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  have ha1 : (1 : ℝ) ≤ a := hb1.trans hba'
  have hh0 : 0 < h := by linarith
  have hT0 : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog2 := Real.log_two_gt_d9
  have hL2 : Real.log 2 ≤ Real.log (2 * a) := Real.log_le_log (by norm_num) (by linarith)
  have hS' : ∀ ρ ∈ S, ρ ∈ Zall χ := fun ρ hρ => ((hS ρ).1 hρ).1
  -- notation
  set D2 : ℂ → ℂ := fun ρ => Dz ρ (a + h) - Dz ρ a - Dz ρ (b + h) + Dz ρ b with hD2
  set F : ℂ → ℂ := fun ρ => (mult χ ρ : ℂ) * D2 ρ with hF
  set E6 : ℂ := (((a : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (a + h) - ((a : ℝ) : ℂ) ^ 2 * efErr χ a -
    (((b : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (b + h) + ((b : ℝ) : ℂ) ^ 2 * efErr χ b with hE6
  have p1 : (0 : ℝ) < a + h := by linarith
  have p2 : (0 : ℝ) < a := by linarith
  have p3 : (0 : ℝ) < b + h := by linarith
  have p4 : (0 : ℝ) < b := by linarith
  have htsum : ∑' ρ : Zall χ, F ρ =
      ∑' ρ : Zall χ, (mult χ ρ : ℂ) * Dz ρ (a + h) - ∑' ρ : Zall χ, (mult χ ρ : ℂ) * Dz ρ a -
      ∑' ρ : Zall χ, (mult χ ρ : ℂ) * Dz ρ (b + h) + ∑' ρ : Zall χ, (mult χ ρ : ℂ) * Dz ρ b := by
    have s1 := summable_mult_Dz hχ p1
    have s2 := summable_mult_Dz hχ p2
    have s3 := summable_mult_Dz hχ p3
    have s4 := summable_mult_Dz hχ p4
    rw [← Summable.tsum_sub s1 s2, ← Summable.tsum_sub (s1.sub s2) s3,
      ← Summable.tsum_add ((s1.sub s2).sub s3) s4]
    exact tsum_congr fun ρ => by simp only [hF, hD2]; ring
  have hΔ : Jchi χ (a + h) - Jchi χ a - Jchi χ (b + h) + Jchi χ b =
      (if q = 1 then D2 1 else 0) - ∑' ρ : Zall χ, F ρ + E6 := by
    rw [Jchi_decomp χ p1, Jchi_decomp χ p2, Jchi_decomp χ p3, Jchi_decomp χ p4, htsum]
    simp only [hD2, hE6]
    split_ifs <;> ring
  -- the six pieces
  have b1 := sharp_window_le χ hb hba hh1 hha
  have b2 : ‖(if q = 1 then D2 1 else 0) / h - (if q = 1 then ∑ n ∈ Ioc b a, (n : ℂ) else 0)‖ ≤
      8 * (h + 1) * a := by
    split_ifs
    · have hm := double_diff_main (e := 1) one_pos le_rfl hb hba hh1 hha
      simp only [Complex.ofReal_one, Real.rpow_one, Complex.ofReal_natCast] at hm
      simp only [hD2]
      linarith
    · have : 0 ≤ 8 * (h + 1) * (a : ℝ) := mul_nonneg (by linarith) (by linarith)
      simp only [zero_div, sub_zero, norm_zero]; exact this
  have b3 := htl q χ hχ a b h T hb hba hh1 hha hT S hS
  have b4 := zero_part_le hχ hb hba hh1 hha S hS' e γ he1 heγ
  have b5 : ‖(e : ℂ) * (D2 (γ : ℂ) / h - ∑ n ∈ Ioc b a, (((n : ℝ) ^ γ : ℝ) : ℂ))‖ ≤
      8 * (h + 1) * a := by
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · have : 0 ≤ 8 * (h + 1) * (a : ℝ) := mul_nonneg (by linarith) (by linarith)
      simp only [Nat.cast_zero, zero_mul, norm_zero]; exact this
    · obtain ⟨hγS, hγ0⟩ := heγ rfl
      have hγ1 : γ ≤ 1 := by
        rcases Zall_nt_or_zero hχ (hS' _ hγS) with h' | h'
        · have := h'.2.2; simp at this; linarith
        · have : γ = 0 := by exact_mod_cast h'
          linarith
      have hm := double_diff_main hγ0 hγ1 hb hba hh1 hha
      have hp : (2 * a : ℝ) ^ γ ≤ 2 * a := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 * a by linarith) hγ1
        simpa using this
      simp only [Nat.cast_one, one_mul, hD2]
      have : 4 * (h + 1) * (2 * a : ℝ) ^ γ ≤ 4 * (h + 1) * (2 * a) := by gcongr
      linarith
  have b6 : ‖E6‖ ≤ 16 * C0 * Real.log (q + 2) * (a : ℝ) ^ (3 / 2 : ℝ) := by
    have e1 := point_err_le hC0 χ (x := (a : ℝ) + h) (a := a) (by linarith) (by linarith)
      (hEF q χ hχ _ p1).2
    have e2 := point_err_le hC0 χ (x := (a : ℝ)) (a := a) (by linarith) (by linarith)
      (hEF q χ hχ _ p2).2
    have e3 := point_err_le hC0 χ (x := (b : ℝ) + h) (a := a) (by linarith) (by linarith)
      (hEF q χ hχ _ p3).2
    have e4 := point_err_le hC0 χ (x := (b : ℝ)) (a := a) (by linarith) (by linarith)
      (hEF q χ hχ _ p4).2
    have t1 := norm_add_le ((((a : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (a + h) -
      ((a : ℝ) : ℂ) ^ 2 * efErr χ a - (((b : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (b + h))
      (((b : ℝ) : ℂ) ^ 2 * efErr χ b)
    have t2 := norm_sub_le ((((a : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (a + h) -
      ((a : ℝ) : ℂ) ^ 2 * efErr χ a) ((((b : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (b + h))
    have t3 := norm_sub_le ((((a : ℝ) + h : ℝ) : ℂ) ^ 2 * efErr χ (a + h))
      (((a : ℝ) : ℂ) ^ 2 * efErr χ a)
    simp only [hE6]
    linarith
  -- assembly
  set X1 := ∑ n ∈ Ioc b a, bCoef χ n
  set Δ := Jchi χ (a + h) - Jchi χ a - Jchi χ (b + h) + Jchi χ b
  set t1 := X1 - Δ / h
  set t2 := (if q = 1 then D2 1 else 0) / h - (if q = 1 then ∑ n ∈ Ioc b a, (n : ℂ) else 0)
  set t3 := (∑' ρ : Zall χ, F ρ) - ∑ ρ ∈ S, F ρ
  set t4 := (∑ ρ ∈ S, F ρ - (e : ℂ) * D2 (γ : ℂ)) / h
  set t5 := (e : ℂ) * (D2 (γ : ℂ) / h - ∑ n ∈ Ioc b a, (((n : ℝ) ^ γ : ℝ) : ℂ))
  have hX : X1 - (if q = 1 then ∑ n ∈ Ioc b a, (n : ℂ) else 0) +
      (e : ℂ) * ∑ n ∈ Ioc b a, (((n : ℝ) ^ γ : ℝ) : ℂ) =
      t1 + t2 - t3 / h - t4 - t5 + E6 / h := by
    simp only [t1, t2, t3, t4, t5]
    linear_combination (1 / (h : ℂ)) * hΔ
  rw [hX]
  have hh' : h ≠ 0 := hh0.ne'
  have hT' : T ≠ 0 := hT0.ne'
  have hhn : ‖(h : ℂ)‖ = h := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
  have n3 : ‖t3 / h‖ ≤ C1 * ((a : ℝ) ^ 3 * Real.log (q * (T + 2)) / (h * T)) := by
    rw [norm_div, hhn, div_le_iff₀ hh0]
    calc ‖t3‖ ≤ C1 * ((a : ℝ) ^ 3 * Real.log (q * (T + 2)) / T) := b3
      _ = _ := by field_simp
  have n6 : ‖E6 / h‖ ≤ 16 * C0 * (Real.log (q + 2) * (a : ℝ) ^ (3 / 2 : ℝ) / h) := by
    rw [norm_div, hhn, div_le_iff₀ hh0]
    calc ‖E6‖ ≤ _ := b6
      _ = _ := by field_simp
  have m1 := norm_add_le (t1 + t2 - t3 / h - t4 - t5) (E6 / h)
  have m2 := norm_sub_le (t1 + t2 - t3 / h - t4) t5
  have m3 := norm_sub_le (t1 + t2 - t3 / h) t4
  have m4 := norm_sub_le (t1 + t2) (t3 / h)
  have m5 := norm_add_le t1 t2
  set A := (h + 1) * a * Real.log (2 * a) with hA
  set B := Real.log (q + 2) * (a : ℝ) ^ (3 / 2 : ℝ) / h with hB
  set D := (a : ℝ) ^ 3 * Real.log (q * (T + 2)) / (h * T) with hD
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
    positivity
  have hD0 : 0 ≤ D := by
    have : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
    positivity
  have hA8 : 8 * (h + 1) * a ≤ 16 * A := by
    rw [hA]
    have : 0 ≤ (h + 1) * (a : ℝ) := mul_nonneg (by linarith) (by linarith)
    have hL5 : 1 / 2 ≤ Real.log (2 * a) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hL5 this]
  have k1 := mul_nonneg hC1 hA0
  have k2 := mul_nonneg hC1 hB0
  have k3 := mul_nonneg hC0 hA0
  have k4 := mul_nonneg hC0 hD0
  have b4' : ‖t4‖ ≤ (a - b : ℝ) * ∑ ρ ∈ S, ((mult χ ρ : ℝ) -
      (if e = 1 ∧ ρ = (γ : ℂ) then 1 else 0)) * (2 * a : ℝ) ^ ρ.re := b4
  have b1' : ‖t1‖ ≤ 4 * A := by rw [hA]; linarith
  linarith

end LeanLab.Linnik.ExplicitFormula
