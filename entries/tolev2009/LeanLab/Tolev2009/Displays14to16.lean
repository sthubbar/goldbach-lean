module

public import LeanLab.Tolev2009.Faithful

/-!
P0055 D. I. Tolev, "The ternary Goldbach problem with primes from arithmetic progressions",
arXiv 0902.2669, section on `E₂`, displays (13) to (17). Unit U-6798, session
20261021T0017Z-cloud54.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is proved; ternary Goldbach is a theorem, Helfgott 2013.

Content, all in the definitions of `Faithful.lean`:
* `U`, `Ihat`, `Kc`, `Vblk`, `Wblk`: the paper's `U`, `I_{k₁,l₁}(r)` of (13), `∫_𝔪 |K|² e(nβ)`,
  the dyadic block sum `V(K₁,K₂)` of (11) built from `Faithful.innerF` and `Faithful.Rm`,
  and `W` of (17).
* Display (14), pointwise form: `|U| ≤ L Σ_{r} |I(r)| ≤ L √J √F`, PROVED.
* Display (16), in the stronger form `F ≤ 2 L² (N/k₁ + 1) Σ_{k₁|n, k₂|n, |n|≤N} |∫_𝔪 |K|² e(nβ)|`,
  PROVED. The paper's route uses the decomposition of `min(H, 1/‖α‖)` and gets `L³ N/K₁`; here
  the sharp sum over `r ≤ N` is majorised by a Fejér kernel, which is a trigonometric
  polynomial with nonnegative values, so no `log H` appears. The paper's (16) follows.
* Display (17): `V ≤ 2√2 L² N W^{1/2}`, hence the paper's `V ≤ 2√2 L³ N W^{1/2}`, PROVED,
  unconditionally: displays (13) to (17) do not use display (12).
-/

@[expose] public section

open Finset Real MeasureTheory ComplexConjugate

namespace LeanLab.Tolev2009.Displays14to16

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-! ### Basic facts on `e(x)` -/

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee, show 2 * (π : ℂ) * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ee (x : ℝ) : conj (ee x) = ee (-x) := by
  rw [ee, ← Complex.exp_conj, ee]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem measurable_ee : Measurable ee := continuous_ee.measurable

/-! ### Bounded functions are integrable for a finite measure -/

/-- `f` is bounded. -/
def Bdd {X : Type*} (f : X → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

theorem Bdd.mul {X : Type*} {f g : X → ℂ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨max C 0 * max D 0, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (le_trans (hC x) (le_max_left _ _)) (le_trans (hD x) (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

theorem Bdd.sum {X ι : Type*} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i, Bdd (f i)) :
    Bdd (fun x => ∑ i ∈ s, f i x) := by
  choose C hC using hf
  exact ⟨∑ i ∈ s, C i, fun x => le_trans (norm_sum_le _ _) (sum_le_sum fun i _ => hC i x)⟩

theorem Bdd.const {X : Type*} (c : ℂ) : Bdd (fun _ : X => c) := ⟨‖c‖, fun _ => le_rfl⟩

theorem Bdd.ee {X : Type*} (φ : X → ℝ) : Bdd (fun x => ee (φ x)) :=
  ⟨1, fun x => (norm_ee _).le⟩

theorem Bdd.comp {X Y : Type*} {f : Y → ℂ} (hf : Bdd f) (g : X → Y) : Bdd (fun x => f (g x)) := by
  obtain ⟨C, hC⟩ := hf; exact ⟨C, fun x => hC _⟩

theorem Bdd.indicator {f : ℝ → ℂ} (hf : Bdd f) (s : Set ℝ) : Bdd (s.indicator f) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun x => le_trans (norm_indicator_le_norm_self _ _) (hC x)⟩

theorem Bdd.conj {X : Type*} {f : X → ℂ} (hf : Bdd f) : Bdd (fun x => conj (f x)) := by
  obtain ⟨C, hC⟩ := hf; exact ⟨C, fun x => by rw [Complex.norm_conj]; exact hC x⟩

theorem Bdd.normSq {X : Type*} {f : X → ℂ} (hf : Bdd f) : Bdd (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨max C 0 ^ 2, fun x => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (hC x) (le_max_left _ _)) 2

theorem integrable_of_bdd {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℂ} (hm : Measurable f) (hb : Bdd f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)

/-! ### The objects of displays (11) to (17) -/

/-- The unit interval `(a, a+1]`; the paper takes `a = -1/τ`. -/
noncomputable def μI (a : ℝ) : Measure ℝ := volume.restrict (Set.Ioc a (a + 1))

instance (a : ℝ) : IsFiniteMeasure (μI a) :=
  isFiniteMeasure_restrict.mpr (by simp)

/-- `K(α) = Σ_{k₃ ≤ K₃, (k₃,l₃)=1} λ(k₃) S_{k₃,l₃}(α)`, page 3. -/
noncomputable def Kfun (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (α : ℝ) : ℂ :=
  ∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃), (lam k₃ : ℂ) * Sexp k₃ l₃ N α

/-- `K` restricted to the minor arcs: `1_𝔪(α) K(α)`. -/
noncomputable def Km (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : ℝ → ℂ :=
  (majorArcs Q τ)ᶜ.indicator (Kfun lam l₃ K₃ N)

/-- `I_{k₁,l₁}(r) = ∫_𝔪 S_{k₁,l₁}(α) K(α) e((r - N)α) dα`, display (13), as a function of the
frequency `t = r - N`. -/
noncomputable def Ihat (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ : ℕ) (t : ℝ) : ℂ :=
  ∫ α, Sexp k₁ l₁ N α * Km Q τ lam l₃ K₃ N α * ee (t * α) ∂μI a

/-- `U = ∫_𝔪 S_{k₁,l₁}(α) S_{k₂,l₂}(α) K(α) e(-Nα) dα`, page 3. -/
noncomputable def U (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ l₂ : ℕ) : ℂ :=
  ∫ α, Sexp k₁ l₁ N α * Sexp k₂ l₂ N α * Km Q τ lam l₃ K₃ N α * ee (-((N : ℝ) * α)) ∂μI a

/-- `∫_𝔪 |K(β)|² e(nβ) dβ`, the inner integral of display (17). -/
noncomputable def Kc (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (n : ℤ) : ℂ :=
  ∫ β, ((‖Km Q τ lam l₃ K₃ N β‖ ^ 2 : ℝ) : ℂ) * ee ((n : ℝ) * β) ∂μI a

/-- The `n` of display (17): `|n| ≤ N`, `k₁ | n`, `k₂ | n`. -/
def nSet (N k₁ k₂ : ℕ) : Finset ℤ :=
  (Icc (-(N : ℤ)) N).filter (fun n => (k₁ : ℤ) ∣ n ∧ (k₂ : ℤ) ∣ n)

/-- The primes `p ≤ N`, `p ≡ l (mod k)`, the range of `Sexp`. -/
def primeSet (k l N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ p % k = l % k)

theorem Sexp_eq (k l N : ℕ) (α : ℝ) :
    Sexp k l N α = ∑ p ∈ primeSet k l N, (Real.log p : ℂ) * ee (α * p) := rfl

/-! ### Measurability and boundedness -/

theorem measurable_Sexp (k l N : ℕ) : Measurable (Sexp k l N) := (continuous_Sexp k l N).measurable

theorem continuous_Kfun (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : Continuous (Kfun lam l₃ K₃ N) := by
  unfold Kfun
  exact continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_Sexp _ _ _)

theorem measurable_Km (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : Measurable (Km Q τ lam l₃ K₃ N) :=
  (continuous_Kfun lam l₃ K₃ N).measurable.indicator (measurableSet_majorArcs Q τ).compl

theorem bdd_Sexp (k l N : ℕ) : Bdd (Sexp k l N) := by
  have : Sexp k l N = fun α => ∑ p ∈ primeSet k l N, (Real.log p : ℂ) * ee (α * p) := rfl
  rw [this]
  exact Bdd.sum _ fun p => (Bdd.const _).mul (Bdd.ee _)

theorem bdd_Km (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : Bdd (Km Q τ lam l₃ K₃ N) := by
  refine Bdd.indicator ?_ _
  have : Kfun lam l₃ K₃ N = fun α => ∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
      (lam k₃ : ℂ) * Sexp k₃ l₃ N α := rfl
  rw [this]
  exact Bdd.sum _ fun k₃ => (Bdd.const _).mul (bdd_Sexp _ _ _)

/-! ### Orthogonality on the unit interval -/

theorem integral_ee_μI (a : ℝ) (n : ℤ) :
    ∫ α, ee ((n : ℝ) * α) ∂μI a = if n = 0 then 1 else 0 := by
  rw [μI, ← intervalIntegral.integral_of_le (by linarith), integral_ee]

/-! ### Measurable and bounded functions -/

/-- `f` is measurable and bounded. -/
def MB {X : Type*} [MeasurableSpace X] (f : X → ℂ) : Prop := Measurable f ∧ Bdd f

theorem MB.mul {X : Type*} [MeasurableSpace X] {f g : X → ℂ} (hf : MB f) (hg : MB g) :
    MB (fun x => f x * g x) := ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩

theorem MB.conj {X : Type*} [MeasurableSpace X] {f : X → ℂ} (hf : MB f) :
    MB (fun x => conj (f x)) := ⟨Complex.continuous_conj.measurable.comp hf.1, hf.2.conj⟩

theorem MB.comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {f : Y → ℂ} (hf : MB f)
    {g : X → Y} (hg : Measurable g) : MB (fun x => f (g x)) := ⟨hf.1.comp hg, hf.2.comp g⟩

theorem MB.ee {X : Type*} [MeasurableSpace X] {φ : X → ℝ} (hφ : Measurable φ) :
    MB (fun x => ee (φ x)) := ⟨measurable_ee.comp hφ, Bdd.ee φ⟩

theorem MB.const {X : Type*} [MeasurableSpace X] (c : ℂ) : MB (fun _ : X => c) :=
  ⟨measurable_const, Bdd.const c⟩

theorem MB.sum {X ι : Type*} [MeasurableSpace X] (s : Finset ι) {f : ι → X → ℂ}
    (hf : ∀ i, MB (f i)) : MB (fun x => ∑ i ∈ s, f i x) :=
  ⟨Finset.measurable_fun_sum s fun i _ => (hf i).1, Bdd.sum s fun i => (hf i).2⟩

theorem MB.normSq {X : Type*} [MeasurableSpace X] {f : X → ℂ} (hf : MB f) :
    MB (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) :=
  ⟨Complex.measurable_ofReal.comp (hf.1.norm.pow_const 2), hf.2.normSq⟩

theorem MB.integrable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℂ} (hf : MB f) : Integrable f μ := integrable_of_bdd hf.1 hf.2

theorem MB.integrable_normSq {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℂ} (hf : MB f) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  obtain ⟨C, hC⟩ := hf.2
  refine Integrable.of_bound (hf.1.norm.pow_const 2).aestronglyMeasurable (max C 0 ^ 2)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (hC x) (le_max_left _ _)) 2

theorem mb_Sexp (k l N : ℕ) : MB (Sexp k l N) := ⟨measurable_Sexp k l N, bdd_Sexp k l N⟩

theorem mb_Km (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : MB (Km Q τ lam l₃ K₃ N) :=
  ⟨measurable_Km Q τ lam l₃ K₃ N, bdd_Km Q τ lam l₃ K₃ N⟩

theorem sq_norm_eq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ### Display (14) -/

/-- Page 3, first display after (12): `U = Σ_{p ≤ N, p ≡ l₂ (k₂)} (log p) I_{k₁,l₁}(p)`. -/
theorem U_eq_sum (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ l₂ : ℕ) :
    U a Q τ lam l₃ K₃ N k₁ l₁ k₂ l₂ =
      ∑ p ∈ primeSet k₂ l₂ N, (Real.log p : ℂ) * Ihat a Q τ lam l₃ K₃ N k₁ l₁ ((p : ℝ) - N) := by
  have hint : ∀ p ∈ primeSet k₂ l₂ N, Integrable (fun α => (Real.log p : ℂ) *
      (Sexp k₁ l₁ N α * Km Q τ lam l₃ K₃ N α * ee (((p : ℝ) - N) * α))) (μI a) := fun p _ =>
    ((MB.const _).mul (((mb_Sexp _ _ _).mul (mb_Km _ _ _ _ _ _)).mul
      (MB.ee (measurable_const.mul measurable_id)))).integrable
  simp only [Ihat, ← integral_const_mul]
  rw [← integral_finsetSum _ hint]
  unfold U
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  simp only
  rw [Sexp_eq k₂ l₂ N α, mul_sum, sum_mul, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  have : ee (((p : ℝ) - N) * α) = ee (α * p) * ee (-((N : ℝ) * α)) := by
    rw [← ee_add]; congr 1; ring
  rw [this]; ring

/-- Cauchy's inequality for a finite sum of norms. -/
theorem sum_norm_le_sqrt {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ∑ j ∈ s, ‖x j‖ ≤ Real.sqrt s.card * Real.sqrt (∑ j ∈ s, ‖x j‖ ^ 2) := by
  have h := Real.sum_sqrt_mul_sqrt_le s (f := fun _ => (1 : ℝ)) (g := fun j => ‖x j‖ ^ 2)
    (fun _ => zero_le_one) (fun _ => by positivity)
  simp only [Real.sqrt_one, one_mul, Real.sqrt_sq (norm_nonneg _), sum_const, nsmul_eq_mul,
    mul_one] at h
  exact h

/-- `F = Σ_{j < N/k₂ + 1} |I_{k₁,l₁}(l₂ mod k₂ + k₂ j)|²`, the `F` of display (14). The residues
`r = l₂ mod k₂ + k₂ j` run over every `r ≤ N` with `r ≡ l₂ (mod k₂)`, and a few more terms
`r ≤ N + k₂`, which only enlarge `F`. -/
noncomputable def Fsum (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ l₂ : ℕ) : ℝ :=
  ∑ j ∈ range (N / k₂ + 1),
    ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (((l₂ % k₂ : ℕ) : ℝ) - N + (j : ℝ) * k₂)‖ ^ 2

/-- Display (14), pointwise form: `|U| ≤ L Σ_{r ≤ N, r ≡ l₂ (k₂)} |I(r)| ≤ L (N/k₂ + 1)^{1/2} F^{1/2}`.
PROVED. -/
theorem display14 (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ l₂ : ℕ) (hk₂ : 1 ≤ k₂) :
    ‖U a Q τ lam l₃ K₃ N k₁ l₁ k₂ l₂‖ ≤ Real.log N * Real.sqrt ((N / k₂ + 1 : ℕ) : ℝ) *
      Real.sqrt (Fsum a Q τ lam l₃ K₃ N k₁ l₁ k₂ l₂) := by
  set g : ℕ → ℕ := fun j => l₂ % k₂ + k₂ * j with hg
  have hsub : primeSet k₂ l₂ N ⊆ (range (N / k₂ + 1)).image g := by
    intro p hp
    simp only [primeSet, mem_filter, mem_range] at hp
    simp only [mem_image, mem_range]
    refine ⟨p / k₂, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp hp.1)), ?_⟩
    simp only [hg]
    rw [← hp.2.2]; exact Nat.mod_add_div p k₂
  have hinj : Set.InjOn g (range (N / k₂ + 1) : Set ℕ) := by
    intro x _ y _ h
    simp only [hg] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [U_eq_sum]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ p ∈ primeSet k₂ l₂ N,
        ‖(Real.log p : ℂ) * Ihat a Q τ lam l₃ K₃ N k₁ l₁ ((p : ℝ) - N)‖
      ≤ ∑ p ∈ primeSet k₂ l₂ N, Real.log N * ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ ((p : ℝ) - N)‖ := by
        refine sum_le_sum fun p hp => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simp only [primeSet, mem_filter, mem_range] at hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
        rw [abs_of_nonneg (Real.log_nonneg hp1)]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith)
          (by exact_mod_cast Nat.lt_succ_iff.mp hp.1)) (norm_nonneg _)
    _ ≤ ∑ r ∈ (range (N / k₂ + 1)).image g,
          Real.log N * ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ ((r : ℝ) - N)‖ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => mul_nonneg hL (norm_nonneg _)
    _ = Real.log N * ∑ j ∈ range (N / k₂ + 1),
          ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (((l₂ % k₂ : ℕ) : ℝ) - N + (j : ℝ) * k₂)‖ := by
        rw [sum_image hinj, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [hg]; push_cast; ring_nf
    _ ≤ _ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hL
        have := sum_norm_le_sqrt (range (N / k₂ + 1))
          (fun j => Ihat a Q τ lam l₃ K₃ N k₁ l₁ (((l₂ % k₂ : ℕ) : ℝ) - N + (j : ℝ) * k₂))
        simpa [Fsum] using this

/-! ### Display (16) through a Fejér kernel -/

/-- `G_M(y) = Σ_{u < M} e(uy)`; `|G_M(k₂ x)|²` is the Fejér kernel used to majorise the sum
over `r ≤ N`, `r ≡ l₂ (mod k₂)`. -/
noncomputable def G (M : ℕ) (y : ℝ) : ℂ := ∑ u ∈ range M, ee ((u : ℝ) * y)

theorem G_neg (M : ℕ) (y : ℝ) : G M (-y) = conj (G M y) := by
  simp only [G, map_sum, conj_ee]
  refine sum_congr rfl fun u _ => by ring_nf

theorem mb_G (M : ℕ) : MB (G M) :=
  MB.sum _ fun u => MB.ee (measurable_const.mul measurable_id)

/-- `|I(t)|² = ∫∫ S(α)K(α)e(tα) conj(S(β)K(β)) e(-tβ)`. -/
theorem sq_norm_Ihat (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ : ℕ) (t : ℝ) :
    ((‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ t‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, (Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.1 * ee (t * z.1)) *
        (conj (Sexp k₁ l₁ N z.2 * Km Q τ lam l₃ K₃ N z.2) * ee (-t * z.2))
        ∂(μI a).prod (μI a) := by
  have h := integral_prod_mul (μ := μI a) (ν := μI a)
    (fun α => Sexp k₁ l₁ N α * Km Q τ lam l₃ K₃ N α * ee (t * α))
    (fun β => conj (Sexp k₁ l₁ N β * Km Q τ lam l₃ K₃ N β) * ee (-t * β))
  beta_reduce at h
  rw [h, sq_norm_eq_mul_conj, Ihat, ← integral_conj]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun β => ?_)
  simp only [map_mul, conj_ee, neg_mul]

theorem kernel_expand (c α β : ℝ) (M k₂ : ℕ) :
    ∑ uv ∈ range M ×ˢ range M, ee ((c + ((uv.1 : ℝ) - uv.2) * k₂) * α) *
        ee (-(c + ((uv.1 : ℝ) - uv.2) * k₂) * β) =
      ee (c * (α - β)) * (G M (k₂ * (α - β)) * conj (G M (k₂ * (α - β)))) := by
  rw [G, map_sum, sum_mul_sum, sum_product, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [conj_ee, ← ee_add, ← ee_add, ← ee_add]
  congr 1; ring

/-- The Fejér expansion of `Σ_{u,v < M} |I(c + (u - v)k₂)|²` as a double integral. -/
theorem sum_sq_norm_Ihat (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ : ℕ) (c : ℝ) (M k₂ : ℕ) :
    ((∑ uv ∈ range M ×ˢ range M,
        ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + ((uv.1 : ℝ) - uv.2) * k₂)‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.1 *
          conj (Sexp k₁ l₁ N z.2 * Km Q τ lam l₃ K₃ N z.2) *
          (ee (c * (z.1 - z.2)) * (G M (k₂ * (z.1 - z.2)) * conj (G M (k₂ * (z.1 - z.2)))))
        ∂(μI a).prod (μI a) := by
  rw [Complex.ofReal_sum]
  simp_rw [sq_norm_Ihat]
  have hS := mb_Sexp k₁ l₁ N
  have hK := mb_Km Q τ lam l₃ K₃ N
  rw [← integral_finsetSum]
  · refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [← kernel_expand, mul_sum]
    refine sum_congr rfl fun uv _ => ?_
    ring
  · intro uv _
    refine MB.integrable ?_
    exact ((((hS.comp measurable_fst).mul (hK.comp measurable_fst)).mul
      (MB.ee (measurable_const.mul measurable_fst))).mul
      ((((hS.comp measurable_snd).mul (hK.comp measurable_snd)).conj).mul
      (MB.ee (measurable_const.mul measurable_snd))))

/-- `Σ_{u,v<M} |I(c + (u-v)k₂)|² ≤ ∫∫ |S(α)|² |K_𝔪(β)|² |G_M(k₂(α-β))|²`, from
`xy ≤ (x² + y²)/2` and the symmetry `α ↔ β`. -/
theorem fejer_le (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ : ℕ) (c : ℝ) (M k₂ : ℕ) :
    ∑ uv ∈ range M ×ˢ range M,
        ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + ((uv.1 : ℝ) - uv.2) * k₂)‖ ^ 2 ≤
      ∫ z, ‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.2 * G M (k₂ * (z.1 - z.2))‖ ^ 2
        ∂(μI a).prod (μI a) := by
  have hS := mb_Sexp k₁ l₁ N
  have hK := mb_Km Q τ lam l₃ K₃ N
  have hGm := mb_G M
  have hsum := sum_sq_norm_Ihat a Q τ lam l₃ K₃ N k₁ l₁ c M k₂
  set f : ℝ × ℝ → ℝ := fun z =>
    ‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.2 * G M (k₂ * (z.1 - z.2))‖ ^ 2 with hf
  have hfi : Integrable f ((μI a).prod (μI a)) :=
    MB.integrable_normSq (((hS.comp measurable_fst).mul (hK.comp measurable_snd)).mul
      (hGm.comp (measurable_const.mul (measurable_fst.sub measurable_snd))))
  have hfsi : Integrable (fun z => f z.swap) ((μI a).prod (μI a)) :=
    MB.integrable_normSq (((hS.comp measurable_snd).mul (hK.comp measurable_fst)).mul
      (hGm.comp (measurable_const.mul (measurable_snd.sub measurable_fst))))
  have hYi : Integrable (fun z : ℝ × ℝ => Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.1 *
      conj (Sexp k₁ l₁ N z.2 * Km Q τ lam l₃ K₃ N z.2) *
      (ee (c * (z.1 - z.2)) * (G M (k₂ * (z.1 - z.2)) * conj (G M (k₂ * (z.1 - z.2))))))
      ((μI a).prod (μI a)) :=
    MB.integrable ((((hS.comp measurable_fst).mul (hK.comp measurable_fst)).mul
      ((hS.comp measurable_snd).mul (hK.comp measurable_snd)).conj).mul
      ((MB.ee (measurable_const.mul (measurable_fst.sub measurable_snd))).mul
      ((hGm.comp (measurable_const.mul (measurable_fst.sub measurable_snd))).mul
      (hGm.comp (measurable_const.mul (measurable_fst.sub measurable_snd))).conj)))
  have hpt : ∀ z : ℝ × ℝ, ‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.1 *
      conj (Sexp k₁ l₁ N z.2 * Km Q τ lam l₃ K₃ N z.2) *
      (ee (c * (z.1 - z.2)) * (G M (k₂ * (z.1 - z.2)) * conj (G M (k₂ * (z.1 - z.2)))))‖ ≤
      (f z + f z.swap) / 2 := by
    intro z
    simp only [hf, Prod.fst_swap, Prod.snd_swap]
    rw [show (k₂ : ℝ) * (z.2 - z.1) = -((k₂ : ℝ) * (z.1 - z.2)) by ring, G_neg]
    simp only [norm_mul, Complex.norm_conj, norm_ee]
    nlinarith [sq_nonneg (‖Sexp k₁ l₁ N z.1‖ * ‖Km Q τ lam l₃ K₃ N z.2‖ *
      ‖G M (k₂ * (z.1 - z.2))‖ - ‖Sexp k₁ l₁ N z.2‖ * ‖Km Q τ lam l₃ K₃ N z.1‖ *
      ‖G M (k₂ * (z.1 - z.2))‖)]
  have hnn : 0 ≤ ∑ uv ∈ range M ×ˢ range M,
      ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + ((uv.1 : ℝ) - uv.2) * k₂)‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  rw [← abs_of_nonneg hnn, ← Real.norm_eq_abs, ← Complex.norm_real, hsum]
  calc _ ≤ _ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, (f z + f z.swap) / 2 ∂(μI a).prod (μI a) :=
        integral_mono hYi.norm ((hfi.add hfsi).div_const 2) hpt
    _ = ((∫ z, f z ∂(μI a).prod (μI a)) + ∫ z, f z.swap ∂(μI a).prod (μI a)) / 2 := by
        rw [integral_div, integral_add hfi hfsi]
    _ = ∫ z, f z ∂(μI a).prod (μI a) := by rw [integral_prod_swap f]; ring

theorem expand_S (k l N : ℕ) (α : ℝ) :
    Sexp k l N α * conj (Sexp k l N α) = ∑ pp ∈ primeSet k l N ×ˢ primeSet k l N,
      (Real.log pp.1 : ℂ) * Real.log pp.2 * ee ((((pp.1 : ℤ) - pp.2 : ℤ) : ℝ) * α) := by
  rw [Sexp_eq, map_sum, sum_mul_sum, sum_product]
  refine sum_congr rfl fun p₁ _ => sum_congr rfl fun p₂ _ => ?_
  dsimp only
  rw [map_mul, Complex.conj_ofReal, conj_ee]
  have : ee (α * p₁) * ee (-(α * p₂)) = ee ((((p₁ : ℤ) - p₂ : ℤ) : ℝ) * α) := by
    rw [← ee_add]; congr 1; push_cast; ring
  rw [← this]; ring

theorem expand_G (M : ℕ) (y : ℝ) : G M y * conj (G M y) =
    ∑ uv ∈ range M ×ˢ range M, ee ((((uv.1 : ℤ) - uv.2 : ℤ) : ℝ) * y) := by
  rw [G, map_sum, sum_mul_sum, sum_product]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  dsimp only
  rw [conj_ee, ← ee_add]; congr 1; push_cast; ring

/-- The frequency `p₁ - p₂ + (u - v)k₂` met in the `α` integral. -/
def nq (k₂ : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  ((q.1.1 : ℤ) - q.1.2) + ((q.2.1 : ℤ) - q.2.2) * k₂

/-- The frequency `-(u - v)k₂` met in the `β` integral. -/
def mq (k₂ : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ := -(((q.2.1 : ℤ) - q.2.2) * k₂)

/-- Counting: at most `M` pairs `u, v < M` have `d + (u - v)k₂ = 0`, and none unless `k₂ | d`. -/
theorem count_le (M k₂ : ℕ) (hk₂ : 1 ≤ k₂) (d : ℤ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ uv ∈ range M ×ˢ range M, (if d + ((uv.1 : ℤ) - uv.2) * k₂ = 0 then x else 0) ≤
      M * (if (k₂ : ℤ) ∣ d then x else 0) := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  split_ifs with hd
  · refine mul_le_mul_of_nonneg_right ?_ hx
    have hc : ((range M ×ˢ range M).filter
        (fun uv : ℕ × ℕ => d + ((uv.1 : ℤ) - uv.2) * k₂ = 0)).card ≤ (range M).card := by
      refine card_le_card_of_injOn Prod.fst ?_ ?_
      · intro uv huv
        simp only [Finset.mem_coe, mem_filter, mem_product, mem_range] at huv ⊢
        exact huv.1.1
      · intro uv huv uv' huv' h
        simp only [Finset.mem_coe, mem_filter, mem_product, mem_range] at huv huv'
        have hu : (uv.1 : ℤ) = uv'.1 := by exact_mod_cast h
        have hk : (k₂ : ℤ) ≠ 0 := by exact_mod_cast (show k₂ ≠ 0 by omega)
        have h2 : ((uv.2 : ℤ) - uv'.2) * k₂ = 0 := by
          linear_combination huv'.2 - huv.2 + (k₂ : ℤ) * hu
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact Prod.ext h (by omega)
        · exact absurd h3 hk
    rw [card_range] at hc
    exact_mod_cast hc
  · have : ((range M ×ˢ range M).filter
        (fun uv : ℕ × ℕ => d + ((uv.1 : ℤ) - uv.2) * k₂ = 0)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro uv _ h
      exact hd ⟨(uv.2 : ℤ) - uv.1, by linear_combination h⟩
    simp [this]

theorem log_mem_primeSet {k l N p : ℕ} (hp : p ∈ primeSet k l N) :
    0 ≤ Real.log p ∧ Real.log p ≤ Real.log N := by
  simp only [primeSet, mem_filter, mem_range] at hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
  exact ⟨Real.log_nonneg hp1, Real.log_le_log (by linarith)
    (by exact_mod_cast Nat.lt_succ_iff.mp hp.1)⟩

/-- The `α` integral computed by orthogonality:
`∫∫ |S(α)|² |K_𝔪(β)|² |G_M(k₂(α-β))|² ≤ M Σ_{p₁,p₂, k₂ | p₁-p₂} log p₁ log p₂ |∫_𝔪 |K|² e((p₁-p₂)β)|`. -/
theorem T1_le (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ : ℕ) (M k₂ : ℕ) (hk₂ : 1 ≤ k₂) :
    ∫ z, ‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.2 * G M (k₂ * (z.1 - z.2))‖ ^ 2
        ∂(μI a).prod (μI a) ≤
      M * ∑ p₁ ∈ primeSet k₁ l₁ N, ∑ p₂ ∈ primeSet k₁ l₁ N,
        (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then
          Real.log p₁ * Real.log p₂ * ‖Kc a Q τ lam l₃ K₃ N ((p₁ : ℤ) - p₂)‖ else 0) := by
  set P := primeSet k₁ l₁ N with hP
  have hS := mb_Sexp k₁ l₁ N
  have hK := mb_Km Q τ lam l₃ K₃ N
  have hexp : ∀ z : ℝ × ℝ,
      ((‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.2 * G M (k₂ * (z.1 - z.2))‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ (P ×ˢ P) ×ˢ (range M ×ˢ range M),
        ((Real.log q.1.1 : ℂ) * Real.log q.1.2 * ee (((nq k₂ q : ℤ) : ℝ) * z.1)) *
        (((‖Km Q τ lam l₃ K₃ N z.2‖ ^ 2 : ℝ) : ℂ) * ee (((mq k₂ q : ℤ) : ℝ) * z.2)) := by
    intro z
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.ofReal_mul, Complex.ofReal_mul,
      sq_norm_eq_mul_conj (Sexp k₁ l₁ N z.1), sq_norm_eq_mul_conj (G M _), expand_S, expand_G,
      sum_mul, sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun q _ => ?_
    have : ee ((((q.1.1 : ℤ) - q.1.2 : ℤ) : ℝ) * z.1) *
        ee ((((q.2.1 : ℤ) - q.2.2 : ℤ) : ℝ) * (k₂ * (z.1 - z.2))) =
        ee (((nq k₂ q : ℤ) : ℝ) * z.1) * ee (((mq k₂ q : ℤ) : ℝ) * z.2) := by
      rw [← ee_add, ← ee_add]; congr 1; simp only [nq, mq]; push_cast; ring
    linear_combination ((Real.log q.1.1 : ℂ) * Real.log q.1.2 *
      ((‖Km Q τ lam l₃ K₃ N z.2‖ ^ 2 : ℝ) : ℂ)) * this
  have hint : ∀ q ∈ (P ×ˢ P) ×ˢ (range M ×ˢ range M), Integrable (fun z : ℝ × ℝ =>
      ((Real.log q.1.1 : ℂ) * Real.log q.1.2 * ee (((nq k₂ q : ℤ) : ℝ) * z.1)) *
      (((‖Km Q τ lam l₃ K₃ N z.2‖ ^ 2 : ℝ) : ℂ) * ee (((mq k₂ q : ℤ) : ℝ) * z.2)))
      ((μI a).prod (μI a)) := fun q _ =>
    MB.integrable (((MB.const _).mul (MB.ee (measurable_const.mul measurable_fst))).mul
      ((hK.comp measurable_snd).normSq.mul (MB.ee (measurable_const.mul measurable_snd))))
  have hT : ((∫ z, ‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.2 * G M (k₂ * (z.1 - z.2))‖ ^ 2
      ∂(μI a).prod (μI a) : ℝ) : ℂ) = ∑ q ∈ (P ×ˢ P) ×ˢ (range M ×ˢ range M),
        (Real.log q.1.1 : ℂ) * Real.log q.1.2 * (if nq k₂ q = 0 then 1 else 0) *
          Kc a Q τ lam l₃ K₃ N (mq k₂ q) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ hint]
    refine sum_congr rfl fun q _ => ?_
    have h := integral_prod_mul (μ := μI a) (ν := μI a)
      (fun α => (Real.log q.1.1 : ℂ) * Real.log q.1.2 * ee (((nq k₂ q : ℤ) : ℝ) * α))
      (fun β => ((‖Km Q τ lam l₃ K₃ N β‖ ^ 2 : ℝ) : ℂ) * ee (((mq k₂ q : ℤ) : ℝ) * β))
    beta_reduce at h
    rw [h, integral_const_mul, integral_ee_μI]
    rfl
  have hnn : 0 ≤ ∫ z, ‖Sexp k₁ l₁ N z.1 * Km Q τ lam l₃ K₃ N z.2 * G M (k₂ * (z.1 - z.2))‖ ^ 2
      ∂(μI a).prod (μI a) := integral_nonneg fun _ => by positivity
  rw [← abs_of_nonneg hnn, ← Real.norm_eq_abs, ← Complex.norm_real, hT]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ q ∈ (P ×ˢ P) ×ˢ (range M ×ˢ range M),
      ‖(Real.log q.1.1 : ℂ) * Real.log q.1.2 * (if nq k₂ q = 0 then 1 else 0) *
          Kc a Q τ lam l₃ K₃ N (mq k₂ q)‖ ≤
        if ((q.1.1 : ℤ) - q.1.2) + ((q.2.1 : ℤ) - q.2.2) * k₂ = 0 then
          Real.log q.1.1 * Real.log q.1.2 * ‖Kc a Q τ lam l₃ K₃ N ((q.1.1 : ℤ) - q.1.2)‖
        else 0 := by
    intro q hq
    simp only [mem_product] at hq
    have h1 := log_mem_primeSet hq.1.1
    have h2 := log_mem_primeSet hq.1.2
    by_cases h : nq k₂ q = 0
    · have h' : ((q.1.1 : ℤ) - q.1.2) + ((q.2.1 : ℤ) - q.2.2) * k₂ = 0 := h
      have hm : mq k₂ q = (q.1.1 : ℤ) - q.1.2 := by simp only [mq]; linarith
      rw [if_pos h, if_pos h', hm, mul_one, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1.1,
        abs_of_nonneg h2.1]
    · have h' : ¬ (((q.1.1 : ℤ) - q.1.2) + ((q.2.1 : ℤ) - q.2.2) * k₂ = 0) := h
      rw [if_neg h, if_neg h']
      simp
  refine le_trans (sum_le_sum hterm) ?_
  rw [sum_product, sum_product, mul_sum]
  refine sum_le_sum fun p₁ hp₁ => ?_
  rw [mul_sum]
  refine sum_le_sum fun p₂ hp₂ => ?_
  dsimp only
  have h1 := log_mem_primeSet hp₁
  have h2 := log_mem_primeSet hp₂
  exact count_le M k₂ hk₂ ((p₁ : ℤ) - p₂) _
    (mul_nonneg (mul_nonneg h1.1 h2.1) (norm_nonneg _))

theorem card_primeSet_le (k l N : ℕ) (hk : 1 ≤ k) : (primeSet k l N).card ≤ N / k + 1 := by
  calc (primeSet k l N).card ≤ (range (N / k + 1)).card := by
        refine card_le_card_of_injOn (fun p => p / k) ?_ ?_
        · intro p hp
          simp only [Finset.mem_coe, primeSet, mem_filter, mem_range] at hp ⊢
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp hp.1))
        · intro p hp q hq h
          simp only [Finset.mem_coe, primeSet, mem_filter, mem_range] at hp hq
          simp only at h
          rw [← Nat.mod_add_div p k, ← Nat.mod_add_div q k, h, hp.2.2, hq.2.2]
    _ = N / k + 1 := card_range _

/-- The `(p₁,p₂)` sum regrouped by `n = p₁ - p₂`: `w(n) ≪ L² N/k₁`, display (15), and
`k₁ | n`. -/
theorem pair_sum_le (N k₁ l₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (x : ℤ → ℝ) (hx : ∀ n, 0 ≤ x n) :
    ∑ p₁ ∈ primeSet k₁ l₁ N, ∑ p₂ ∈ primeSet k₁ l₁ N,
      (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then Real.log p₁ * Real.log p₂ * x ((p₁ : ℤ) - p₂) else 0) ≤
    Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) * ∑ n ∈ nSet N k₁ k₂, x n := by
  set P := primeSet k₁ l₁ N with hP
  have step1 : ∀ p₁ ∈ P, ∀ p₂ ∈ P,
      (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then Real.log p₁ * Real.log p₂ * x ((p₁ : ℤ) - p₂) else 0) ≤
      Real.log N ^ 2 * (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then x ((p₁ : ℤ) - p₂) else 0) := by
    intro p₁ h₁ p₂ h₂
    have l1 := log_mem_primeSet h₁
    have l2 := log_mem_primeSet h₂
    split_ifs
    · rw [sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul l1.2 l2.2 l2.1 (le_trans l1.1 l1.2)) (hx _)
    · simp
  have step2 : ∀ p₂ ∈ P, ∑ p₁ ∈ P,
      (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then x ((p₁ : ℤ) - p₂) else 0) ≤ ∑ n ∈ nSet N k₁ k₂, x n := by
    intro p₂ h₂
    rw [← sum_filter]
    have hinj : Set.InjOn (fun p₁ : ℕ => (p₁ : ℤ) - p₂)
        ↑(P.filter (fun p₁ : ℕ => (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂)) := by
      intro u _ v _ h; simp only at h; omega
    rw [← sum_image (f := x) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hx _)
    intro n hn
    simp only [mem_image, mem_filter] at hn
    obtain ⟨p₁, ⟨h₁, hd⟩, rfl⟩ := hn
    simp only [hP, primeSet, mem_filter, mem_range] at h₁ h₂
    simp only [nSet, mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_, hd⟩
    exact Nat.ModEq.dvd (show p₂ ≡ p₁ [MOD k₁] from h₂.2.2.trans h₁.2.2.symm)
  have hcard : ((P.card : ℕ) : ℝ) ≤ (N : ℝ) / k₁ + 1 := by
    have h1 : P.card ≤ N / k₁ + 1 := card_primeSet_le k₁ l₁ N hk₁
    have h2 : ((N / k₁ : ℕ) : ℝ) ≤ (N : ℝ) / k₁ := Nat.cast_div_le
    calc ((P.card : ℕ) : ℝ) ≤ ((N / k₁ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := by push_cast; linarith
  have hS0 : 0 ≤ ∑ n ∈ nSet N k₁ k₂, x n := sum_nonneg fun _ _ => hx _
  calc _ ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, Real.log N ^ 2 *
        (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then x ((p₁ : ℤ) - p₂) else 0) :=
        sum_le_sum fun p₁ h₁ => sum_le_sum fun p₂ h₂ => step1 p₁ h₁ p₂ h₂
    _ = Real.log N ^ 2 * ∑ p₂ ∈ P, ∑ p₁ ∈ P,
        (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then x ((p₁ : ℤ) - p₂) else 0) := by
        rw [sum_comm, mul_sum]; simp only [mul_sum]
    _ ≤ Real.log N ^ 2 * ∑ p₂ ∈ P, ∑ n ∈ nSet N k₁ k₂, x n :=
        mul_le_mul_of_nonneg_left (sum_le_sum step2) (sq_nonneg _)
    _ = Real.log N ^ 2 * ((P.card : ℝ) * ∑ n ∈ nSet N k₁ k₂, x n) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.log N ^ 2 * (((N : ℝ) / k₁ + 1) * ∑ n ∈ nSet N k₁ k₂, x n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hS0) (sq_nonneg _)
    _ = _ := by ring

theorem lower_fejer (J : ℕ) (φ : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (hφ : ∀ u v, 0 ≤ φ u v)
    (hψ : ∀ j v, φ (v + j) v = ψ j) :
    (J : ℝ) * ∑ j ∈ range J, ψ j ≤ ∑ uv ∈ range (2 * J) ×ˢ range (2 * J), φ uv.1 uv.2 := by
  have himg : (range J ×ˢ range J).image (fun jv : ℕ × ℕ => (jv.2 + jv.1, jv.2)) ⊆
      range (2 * J) ×ˢ range (2 * J) := by
    intro x hx
    simp only [mem_image, mem_product, mem_range] at hx ⊢
    obtain ⟨⟨j, v⟩, ⟨hj, hv⟩, rfl⟩ := hx
    dsimp only
    omega
  have hinj : Set.InjOn (fun jv : ℕ × ℕ => (jv.2 + jv.1, jv.2)) ↑(range J ×ˢ range J) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) h.2
  calc (J : ℝ) * ∑ j ∈ range J, ψ j
      = ∑ jv ∈ range J ×ˢ range J, φ (jv.2 + jv.1) jv.2 := by
        rw [sum_product]; simp only [hψ, sum_const, card_range, nsmul_eq_mul]; rw [mul_sum]
    _ = ∑ x ∈ (range J ×ˢ range J).image (fun jv : ℕ × ℕ => (jv.2 + jv.1, jv.2)), φ x.1 x.2 := by
        rw [sum_image hinj]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => hφ _ _)

/-- Display (16), strong form, PROVED: for every real `c` and every `J`,
`Σ_{j<J} |I_{k₁,l₁}(c + j k₂)|² ≤ 2 L² (N/k₁ + 1) Σ_{|n| ≤ N, k₁|n, k₂|n} |∫_𝔪 |K(β)|² e(nβ) dβ|`.
With `c = (l₂ mod k₂) - N` the left side is the `F` of display (14). The paper's (16) has `L³`
in place of `L²`, the extra `L` being its `log H` from `min(H, 1/‖α‖)`. -/
theorem display16_strong (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁)
    (hk₂ : 1 ≤ k₂) (c : ℝ) (J : ℕ) :
    ∑ j ∈ range J, ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + (j : ℝ) * k₂)‖ ^ 2 ≤
      2 * Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) * ∑ n ∈ nSet N k₁ k₂, ‖Kc a Q τ lam l₃ K₃ N n‖ := by
  set X := ∑ p₁ ∈ primeSet k₁ l₁ N, ∑ p₂ ∈ primeSet k₁ l₁ N,
    (if (k₂ : ℤ) ∣ (p₁ : ℤ) - p₂ then
      Real.log p₁ * Real.log p₂ * ‖Kc a Q τ lam l₃ K₃ N ((p₁ : ℤ) - p₂)‖ else 0) with hX
  have hXle := pair_sum_le N k₁ l₁ k₂ hk₁ (fun n => ‖Kc a Q τ lam l₃ K₃ N n‖) (fun _ => norm_nonneg _)
  rw [← hX] at hXle
  have h1 := lower_fejer J (fun u v => ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + ((u : ℝ) - v) * k₂)‖ ^ 2)
    (fun j => ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + (j : ℝ) * k₂)‖ ^ 2) (fun _ _ => by positivity)
    (fun j v => by simp only [Nat.cast_add, add_sub_cancel_left])
  have h2 := fejer_le a Q τ lam l₃ K₃ N k₁ l₁ c (2 * J) k₂
  have h3 := T1_le a Q τ lam l₃ K₃ N k₁ l₁ (2 * J) k₂ hk₂
  rw [← hX] at h3
  push_cast at h3
  have h4 : (J : ℝ) * ∑ j ∈ range J, ‖Ihat a Q τ lam l₃ K₃ N k₁ l₁ (c + (j : ℝ) * k₂)‖ ^ 2 ≤
      (J : ℝ) * (2 * X) := by
    have := h1.trans (h2.trans h3); linarith
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    simp only [range_zero, sum_empty]
    have : 0 ≤ ∑ n ∈ nSet N k₁ k₂, ‖Kc a Q τ lam l₃ K₃ N n‖ := sum_nonneg fun _ _ => norm_nonneg _
    have : 0 ≤ (N : ℝ) / k₁ + 1 := by positivity
    positivity
  · have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
    have h5 := le_of_mul_le_mul_left h4 hJ'
    linarith

/-- Display (16) in the paper's form, PROVED: for `K₁ < k₁`, `1 ≤ K₁ ≤ N` and `L ≥ 1`,
`F ≤ 4 L³ N K₁^{-1} Σ_{|n| ≤ N, k₁|n, k₂|n} |∫_𝔪 |K(β)|² e(nβ) dβ|`. -/
theorem display16 (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ l₂ K₁ : ℕ) (hK₁ : 1 ≤ K₁)
    (hk₁ : K₁ < k₁) (hK₁N : K₁ ≤ N) (hk₂ : 1 ≤ k₂) (hL : 1 ≤ Real.log N) :
    Fsum a Q τ lam l₃ K₃ N k₁ l₁ k₂ l₂ ≤
      4 * Real.log N ^ 3 * N / K₁ * ∑ n ∈ nSet N k₁ k₂, ‖Kc a Q τ lam l₃ K₃ N n‖ := by
  have h := display16_strong a Q τ lam l₃ K₃ N k₁ l₁ k₂ (by omega) hk₂
    (((l₂ % k₂ : ℕ) : ℝ) - N) (N / k₂ + 1)
  have hS : 0 ≤ ∑ n ∈ nSet N k₁ k₂, ‖Kc a Q τ lam l₃ K₃ N n‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hK₁' : (0 : ℝ) < K₁ := by exact_mod_cast hK₁
  have hd1 : (N : ℝ) / k₁ ≤ N / K₁ :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hK₁' (by exact_mod_cast hk₁.le)
  have hd2 : (1 : ℝ) ≤ N / K₁ := by
    rw [one_le_div hK₁']; exact_mod_cast hK₁N
  have hL2 : Real.log N ^ 2 ≤ Real.log N ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  have hc : 2 * Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) ≤ 4 * Real.log N ^ 3 * N / K₁ := by
    have e : 4 * Real.log N ^ 3 * N / K₁ = 2 * Real.log N ^ 3 * (2 * (N / K₁)) := by ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL2 (by norm_num)) (by linarith) (by positivity)
      (by positivity)
  exact le_trans h (mul_le_mul_of_nonneg_right hc hS)

/-! ### From `R^(m)` to `U`, and display (17) -/

theorem mb_integrand (k l : Fin 3 → ℕ) (N : ℕ) : MB (integrand k l N) := by
  have : integrand k l N = fun α => Sexp (k 0) (l 0) N α * Sexp (k 1) (l 1) N α *
      Sexp (k 2) (l 2) N α * ee (-((N : ℝ) * α)) := rfl
  rw [this]
  exact (((mb_Sexp _ _ _).mul (mb_Sexp _ _ _)).mul (mb_Sexp _ _ _)).mul
    (MB.ee (measurable_const.mul measurable_id).neg)

theorem MB.indicator {f : ℝ → ℂ} (hf : MB f) {s : Set ℝ} (hs : MeasurableSet s) :
    MB (s.indicator f) := ⟨hf.1.indicator hs, hf.2.indicator s⟩

/-- `Σ_{k₃} λ(k₃) R^(m)_{k,l} = Re U`, with `U` over the paper's interval `[-1/τ, 1 - 1/τ]`. -/
theorem sum_lam_Rm (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ l₁ k₂ l₂ : ℕ) :
    ∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
        lam k₃ * Rm Q τ ![k₁, k₂, k₃] ![l₁, l₂, l₃] N =
      (U (-1 / τ) Q τ lam l₃ K₃ N k₁ l₁ k₂ l₂).re := by
  have hI : ∀ k₃, (∫ α in (-1 / τ)..(1 - 1 / τ),
      (majorArcs Q τ)ᶜ.indicator (integrand ![k₁, k₂, k₃] ![l₁, l₂, l₃] N) α) =
      ∫ α, (majorArcs Q τ)ᶜ.indicator (integrand ![k₁, k₂, k₃] ![l₁, l₂, l₃] N) α
        ∂μI (-1 / τ) := by
    intro k₃
    rw [show (1 : ℝ) - 1 / τ = -1 / τ + 1 by ring, intervalIntegral.integral_of_le (by linarith)]
    rfl
  simp only [Rm, hI, ← Complex.re_ofReal_mul, ← Complex.re_sum, ← integral_const_mul]
  congr 1
  have hint : ∀ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃), Integrable (fun α =>
      (lam k₃ : ℂ) * (majorArcs Q τ)ᶜ.indicator (integrand ![k₁, k₂, k₃] ![l₁, l₂, l₃] N) α)
      (μI (-1 / τ)) := fun k₃ _ =>
    ((MB.const _).mul ((mb_integrand _ _ _).indicator (measurableSet_majorArcs Q τ).compl)).integrable
  rw [← integral_finsetSum _ hint]
  unfold U
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  by_cases h : α ∈ (majorArcs Q τ)ᶜ
  · simp only [Set.indicator_of_mem h, Km, Kfun]
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun k₃ _ => ?_
    simp only [integrand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · simp only [Set.indicator_of_notMem h, Km, mul_zero, zero_mul, sum_const_zero]

theorem innerF_Rm_le (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ k₁ k₂ ≤
      Real.log N * Real.sqrt ((N / k₂ + 1 : ℕ) : ℝ) *
        Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) *
          ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖) := by
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h0 : 0 ≤ Real.log N * Real.sqrt ((N / k₂ + 1 : ℕ) : ℝ) *
      Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) *
        ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖) :=
    mul_nonneg (mul_nonneg hL (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  unfold innerF
  refine Real.iSup_le (fun l₁ => Real.iSup_le (fun _ => Real.iSup_le
    (fun l₂ => Real.iSup_le (fun _ => ?_) h0) h0) h0) h0
  rw [sum_lam_Rm]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  refine le_trans (display14 _ _ _ _ _ _ _ _ _ _ _ hk₂) ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (mul_nonneg hL (Real.sqrt_nonneg _))
  exact display16_strong (-1 / τ) Q τ lam l₃ K₃ N k₁ l₁ k₂ hk₁ hk₂ _ _

/-- `V(K₁,K₂) = Σ_{K₁ < k₁ ≤ 2K₁} Σ_{K₂ < k₂ ≤ 2K₂} max_{l₁,l₂} |Σ_{k₃} λ(k₃) R^(m)_{k,l}|`,
display (11), with the same maximum `Faithful.innerF` as in `E₂`. -/
noncomputable def Vblk (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) : ℝ :=
  ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂), innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ k₁ k₂

/-- `W = Σ_{k₁ ∼ K₁} Σ_{k₂ ∼ K₂} Σ_{|n| ≤ N, k₁|n, k₂|n} |∫_𝔪 |K(β)|² e(nβ) dβ|`, display (17). -/
noncomputable def Wblk (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) : ℝ :=
  ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂), ∑ n ∈ nSet N k₁ k₂, ‖Kc a Q τ lam l₃ K₃ N n‖

/-- `W'`, the terms `n = 0` of `W`, display (18). -/
noncomputable def Wzero (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) : ℝ :=
  ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂),
    ∑ n ∈ (nSet N k₁ k₂).filter (fun n => n = 0), ‖Kc a Q τ lam l₃ K₃ N n‖

/-- `W*`, the terms `n ≠ 0` of `W`, display (18). -/
noncomputable def Wstar (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) : ℝ :=
  ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂),
    ∑ n ∈ (nSet N k₁ k₂).filter (fun n => ¬ n = 0), ‖Kc a Q τ lam l₃ K₃ N n‖

/-- Display (18): `W = W' + W*`. -/
theorem Wblk_eq (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) :
    Wblk a Q τ lam l₃ K₃ N K₁ K₂ = Wzero a Q τ lam l₃ K₃ N K₁ K₂ + Wstar a Q τ lam l₃ K₃ N K₁ K₂ := by
  simp only [Wblk, Wzero, Wstar, ← sum_add_distrib, sum_filter_add_sum_filter_not]

theorem Wzero_nonneg (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) :
    0 ≤ Wzero a Q τ lam l₃ K₃ N K₁ K₂ :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

theorem Wstar_nonneg (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) :
    0 ≤ Wstar a Q τ lam l₃ K₃ N K₁ K₂ :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

theorem Vblk_nonneg (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) :
    0 ≤ Vblk Q τ lam l₃ K₃ N K₁ K₂ :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => innerF_nonneg _ _ _ _ _ _

/-- Display (17), strong form, PROVED unconditionally: for `1 ≤ K₁, K₂ ≤ N`,
`V(K₁,K₂) ≤ √8 L² N W^{1/2}`. Displays (14) and (16) as printed give `L^{5/2}`;
the Fejér form of (16) removes the `log H` and gives `L²`. -/
theorem display17_strong (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) (hK₁ : 1 ≤ K₁)
    (hK₁N : K₁ ≤ N) (hK₂ : 1 ≤ K₂) (hK₂N : K₂ ≤ N) :
    Vblk Q τ lam l₃ K₃ N K₁ K₂ ≤
      Real.sqrt 8 * Real.log N ^ 2 * N * Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := by
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hK₁' : (0 : ℝ) < K₁ := by exact_mod_cast hK₁
  have hK₂' : (0 : ℝ) < K₂ := by exact_mod_cast hK₂
  have hT0 : ∀ k₁ k₂, 0 ≤ ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ :=
    fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have hA0 : (0 : ℝ) ≤ (N : ℝ) / K₂ + 1 := by positivity
  have hB0 : (0 : ℝ) ≤ 2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1) := by positivity
  have hterm : ∀ k₁ ∈ Ioc K₁ (2 * K₁), ∀ k₂ ∈ Ioc K₂ (2 * K₂),
      innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ k₁ k₂ ≤
        Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
          (Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
            Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖)) := by
    intro k₁ hk₁ k₂ hk₂
    simp only [mem_Ioc] at hk₁ hk₂
    refine le_trans (innerF_Rm_le Q τ lam l₃ K₃ N k₁ k₂ (by omega) (by omega)) ?_
    rw [← Real.sqrt_mul hB0]
    have hJ : ((N / k₂ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / K₂ + 1 := by
      have h1 : ((N / k₂ : ℕ) : ℝ) ≤ (N : ℝ) / k₂ := Nat.cast_div_le
      have h2 : (N : ℝ) / k₂ ≤ N / K₂ :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) hK₂' (by exact_mod_cast hk₂.1.le)
      push_cast; linarith
    have hk1 : (N : ℝ) / k₁ ≤ N / K₁ :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg N) hK₁' (by exact_mod_cast hk₁.1.le)
    have hBT : 2 * Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) *
        ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ ≤
        2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1) *
        ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        (hT0 _ _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hJ) hL)
      (Real.sqrt_le_sqrt hBT) (Real.sqrt_nonneg _) (mul_nonneg hL (Real.sqrt_nonneg _))
  have hcard : ((Ioc K₁ (2 * K₁) ×ˢ Ioc K₂ (2 * K₂)).card : ℝ) = (K₁ : ℝ) * K₂ := by
    rw [card_product, Nat.card_Ioc, Nat.card_Ioc]
    push_cast [show 2 * K₁ - K₁ = K₁ by omega, show 2 * K₂ - K₂ = K₂ by omega]
    ring
  have hCS : ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂),
      Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖) ≤
      Real.sqrt ((K₁ : ℝ) * K₂) * Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := by
    rw [← sum_product', Wblk, ← sum_product', ← hcard]
    have h := Real.sum_sqrt_mul_sqrt_le (Ioc K₁ (2 * K₁) ×ˢ Ioc K₂ (2 * K₂))
      (f := fun _ => (1 : ℝ))
      (g := fun x => ∑ n ∈ nSet N x.1 x.2, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖)
      (fun _ => zero_le_one) (fun x => hT0 _ _)
    simp only [Real.sqrt_one, one_mul, sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  have hprod : ((N : ℝ) / K₂ + 1) * (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) * ((K₁ : ℝ) * K₂) ≤
      8 * Real.log N ^ 2 * (N : ℝ) ^ 2 := by
    have e1 : ((N : ℝ) / K₂ + 1) * K₂ = N + K₂ := by field_simp
    have e2 : ((N : ℝ) / K₁ + 1) * K₁ = N + K₁ := by field_simp
    have hN1 : (K₁ : ℝ) ≤ N := by exact_mod_cast hK₁N
    have hN2 : (K₂ : ℝ) ≤ N := by exact_mod_cast hK₂N
    have hm : ((N : ℝ) + K₂) * (N + K₁) ≤ (2 * N) * (2 * N) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    calc ((N : ℝ) / K₂ + 1) * (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) * ((K₁ : ℝ) * K₂)
        = 2 * Real.log N ^ 2 * ((((N : ℝ) / K₂ + 1) * K₂) * (((N : ℝ) / K₁ + 1) * K₁)) := by ring
      _ = 2 * Real.log N ^ 2 * (((N : ℝ) + K₂) * (N + K₁)) := by rw [e1, e2]
      _ ≤ 2 * Real.log N ^ 2 * ((2 * N) * (2 * N)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 8 * Real.log N ^ 2 * (N : ℝ) ^ 2 := by ring
  have hsq : Real.sqrt ((N : ℝ) / K₂ + 1) * Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
      Real.sqrt ((K₁ : ℝ) * K₂) ≤ Real.sqrt 8 * Real.log N * N := by
    rw [← Real.sqrt_mul hA0, ← Real.sqrt_mul (mul_nonneg hA0 hB0)]
    calc _ ≤ Real.sqrt (8 * Real.log N ^ 2 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt 8 * Real.log N * N := by
        rw [show 8 * Real.log N ^ 2 * (N : ℝ) ^ 2 = 8 * (Real.log N * N) ^ 2 by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
        ring
  have hW0 : 0 ≤ Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := Real.sqrt_nonneg _
  calc Vblk Q τ lam l₃ K₃ N K₁ K₂
      ≤ ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂),
          Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
            (Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
              Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖)) :=
        sum_le_sum fun k₁ h₁ => sum_le_sum fun k₂ h₂ => hterm k₁ h₁ k₂ h₂
    _ = Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
          Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
          ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂),
            Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖) := by
        simp only [mul_sum, mul_assoc]
    _ ≤ Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
          Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
          (Real.sqrt ((K₁ : ℝ) * K₂) * Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂)) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = Real.log N * (Real.sqrt ((N : ℝ) / K₂ + 1) *
          Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) * Real.sqrt ((K₁ : ℝ) * K₂)) *
          Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := by ring
    _ ≤ Real.log N * (Real.sqrt 8 * Real.log N * N) *
          Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hL) hW0
    _ = Real.sqrt 8 * Real.log N ^ 2 * N * Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := by
        ring

/-- Display (17) in the paper's form, PROVED: for `L ≥ 1` and `1 ≤ K₁, K₂ ≤ N`,
`V ≤ √8 L³ N (W' + W*)^{1/2}`, exactly the hypothesis `h17` of `Faithful.E2_bookkeeping`
with `c₃ = √8`. -/
theorem display17 (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) (hL : 1 ≤ Real.log N)
    (hK₁ : 1 ≤ K₁) (hK₁N : K₁ ≤ N) (hK₂ : 1 ≤ K₂) (hK₂N : K₂ ≤ N) :
    Vblk Q τ lam l₃ K₃ N K₁ K₂ ≤ Real.sqrt 8 * Real.log N ^ 3 * N *
      Real.sqrt (Wzero (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ + Wstar (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := by
  rw [← Wblk_eq]
  refine le_trans (display17_strong Q τ lam l₃ K₃ N K₁ K₂ hK₁ hK₁N hK₂ hK₂N) ?_
  have hL2 : Real.log N ^ 2 ≤ Real.log N ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  have h8 : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  have hW : 0 ≤ Real.sqrt (Wblk (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂) := Real.sqrt_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL2 h8) hN) hW

/-- `Faithful.E2_bookkeeping` with its hypothesis `h17` discharged by `display17`: from
display (10) `E ≤ c₄ L² V(K₁,K₂)`, display (19) for `W'` and display (20) for `W*`,
`E ≤ c₄ √8 (√c₁ + √c₂) N² L^{-A}`. Displays (19) and (20) rest on display (12), from
Tolev 1999 Lemma 12, and stay hypotheses here; display (10) is the dyadic split. -/
theorem E2_bound_of_displays {A B E c₁ c₂ c₄ : ℝ} (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ)
    (hA : 10 ^ 4 ≤ A) (hB : B = 10 ^ 4 * A) (hL : 1 ≤ Real.log N) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₄ : 0 ≤ c₄) (hK₁ : 1 ≤ K₁) (hK₁N : K₁ ≤ N) (hK₂ : 1 ≤ K₂) (hK₂N : K₂ ≤ N)
    (h19 : Wzero (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤ c₁ * Real.log N ^ (20 - 2 * B) * (N : ℝ) ^ 2)
    (h20 : Wstar (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤ c₂ * (N : ℝ) ^ 2 * Real.log N ^ (400 - 4 * A))
    (h10 : E ≤ c₄ * Real.log N ^ 2 * Vblk Q τ lam l₃ K₃ N K₁ K₂) :
    E ≤ c₄ * Real.sqrt 8 * (Real.sqrt c₁ + Real.sqrt c₂) * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  E2_bookkeeping hA hB hL (Nat.cast_nonneg N) hc₁ hc₂ (Real.sqrt_nonneg 8) hc₄
    (Wzero_nonneg _ _ _ _ _ _ _ _ _) (Wstar_nonneg _ _ _ _ _ _ _ _ _) h19 h20
    (display17 Q τ lam l₃ K₃ N K₁ K₂ hL hK₁ hK₁N hK₂ hK₂N) h10

theorem Kc_lam_zero (a Q τ : ℝ) (l₃ K₃ N : ℕ) (n : ℤ) :
    Kc a Q τ (fun _ => 0) l₃ K₃ N n = 0 := by
  have h : Kfun (fun _ => 0) l₃ K₃ N = fun _ => 0 := by funext α; simp [Kfun]
  simp [Kc, Km, h]

/-- Non vacuity of `E2_bound_of_displays`: all its hypotheses hold at `λ = 0`, `N = 16`,
`K₁ = K₂ = 1`, `A = 10⁴`, `B = 10⁸`, `E = 0`, every constant `1`. -/
example : ∃ (A B E c₁ c₂ c₄ Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ),
    10 ^ 4 ≤ A ∧ B = 10 ^ 4 * A ∧ 1 ≤ Real.log N ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ 0 ≤ c₄ ∧
    1 ≤ K₁ ∧ K₁ ≤ N ∧ 1 ≤ K₂ ∧ K₂ ≤ N ∧
    Wzero (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤ c₁ * Real.log N ^ (20 - 2 * B) * (N : ℝ) ^ 2 ∧
    Wstar (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤ c₂ * (N : ℝ) ^ 2 * Real.log N ^ (400 - 4 * A) ∧
    E ≤ c₄ * Real.log N ^ 2 * Vblk Q τ lam l₃ K₃ N K₁ K₂ := by
  have hL : (1 : ℝ) ≤ Real.log ((16 : ℕ) : ℝ) := by
    have h16 : Real.exp 1 < 16 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [Real.le_log_iff_exp_le (by norm_num)]
    push_cast; linarith
  have hL0 : (0 : ℝ) < Real.log ((16 : ℕ) : ℝ) := by linarith
  refine ⟨10 ^ 4, 10 ^ 8, 0, 1, 1, 1, 1, 1, fun _ => 0, 1, 1, 16, 1, 1, by norm_num, by norm_num,
    hL, zero_le_one, zero_le_one, zero_le_one, le_rfl, by norm_num, le_rfl, by norm_num,
    ?_, ?_, ?_⟩
  · simp only [Wzero, Kc_lam_zero, norm_zero, sum_const_zero]; positivity
  · simp only [Wstar, Kc_lam_zero, norm_zero, sum_const_zero]; positivity
  · have := Vblk_nonneg 1 1 (fun _ => 0) 1 1 16 1 1
    positivity

end LeanLab.Tolev2009.Displays14to16
