module

public import LeanLab.Tolev2009.Statements

/-!
P0055 D. I. Tolev, "The ternary Goldbach problem with primes from arithmetic progressions",
arXiv 0902.2669. Unit U-6782, session 20261020T2317Z-cloud53.

Faithful restatement of the main Theorem with real content, replacing the opaque
`halupczokS` of `Statements.lean`, which is kept unchanged.

* `singSeries` is the singular series written out concretely as the major arc series
  `𝔖_{k,l}(N) = Σ_q Σ_{(a,q)=1} e(-aN/q) Π_i (φ(kᵢ)/φ([kᵢ,q])) Σ_{r mod [kᵢ,q], r ≡ lᵢ (kᵢ), (r,[kᵢ,q])=1} e(ar/q)`,
  normalised so that `M = N² 𝔖 / (2 φ(k₁)φ(k₂)φ(k₃))` as in the paper, page 1.
  The paper does not print `𝔖`; it points to Halupczok 2008, ref [2], which the lab has no
  copy of. This is the series the major arcs produce; for `k = (1,1,1)` it is the classical
  ternary series. Whether it is literally Halupczok's displayed formula is a QUESTION.
* `MainTheorem := TheTheorem singSeries` is the faithful restatement.
* The circle method split `R = R^(M) + R^(m)` with the paper's major arcs is PROVED,
  through the orthogonality integral, and so is `𝓔* ≤ E₁ + E₂`, display (8).
* `mainTheorem_of_E1_E2` deduces `MainTheorem` from the two cited bounds,
  display (9) for `E₁` and the bound `E₂ ≪ N² L^{-A}` of displays (10) to (20).
* `E2_bookkeeping` checks the exponent arithmetic of displays (6), (10), (17) to (20).

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Fully proved.
Binary Goldbach is proved; ternary Goldbach is a theorem, Helfgott 2013.
-/

@[expose] public section

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.Faithful

open LeanLab.Tolev2009

/-! ### The singular series -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- Residues `r mod [k,q]` with `r ≡ l (mod k)` and `(r,[k,q]) = 1`. -/
def liftRes (k l q : ℕ) : Finset ℕ :=
  (range (Nat.lcm k q)).filter (fun r => r % k = l % k ∧ Nat.Coprime r (Nat.lcm k q))

/-- The local factor `(φ(k)/φ([k,q])) Σ_{r} e(ar/q)` for one prime variable. -/
noncomputable def localSum (k l q a : ℕ) : ℂ :=
  ((k.totient : ℂ) / ((Nat.lcm k q).totient : ℂ)) *
    ∑ r ∈ liftRes k l q, ee ((a : ℝ) * r / q)

/-- The `q`th term of the singular series. -/
noncomputable def ssTerm (k l : Fin 3 → ℕ) (N q : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ee (-((a : ℝ) * N / q)) * ∏ i : Fin 3, localSum (k i) (l i) q a

/-- The singular series `𝔖_{k,l}(N) = Σ_{q ≥ 1} ssTerm q`, real part of the complex sum;
the sum is real since the terms for `a` and `q - a` are conjugate. -/
noncomputable def singSeries : SSeries := fun k l N => (∑' q : ℕ, ssTerm k l N (q + 1)).re

/-- The faithful main Theorem of the paper, with the concrete singular series. -/
def MainTheorem : Prop := TheTheorem singSeries

theorem ee_zero : ee 0 = 1 := by simp [ee]

/-- For `k ≥ 1` and `(l,k) = 1` the lifted residue set at `q = 1` is the single class `l mod k`. -/
theorem liftRes_one {k l : ℕ} (hk : 1 ≤ k) (hl : Nat.Coprime l k) : liftRes k l 1 = {l % k} := by
  ext r
  simp only [liftRes, Nat.lcm_one_right, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hr, h1, -⟩
    rw [← h1, Nat.mod_eq_of_lt hr]
  · rintro rfl
    refine ⟨Nat.mod_lt _ (by omega), Nat.mod_mod _ _, ?_⟩
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hl

/-- The `q = 1` term of the singular series is `1` when every `(lᵢ,kᵢ) = 1`. -/
theorem ssTerm_one {k l : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (N : ℕ) : ssTerm k l N 1 = 1 := by
  have hloc : ∀ i, localSum (k i) (l i) 1 0 = 1 := by
    intro i
    have ht : ((k i).totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by have := hk i; omega)).ne'
    simp [localSum, liftRes_one (hk i) (hl i), ee_zero, ht]
  simp [ssTerm, hloc, ee_zero]

/-- A non admissible residue `(lᵢ,kᵢ) ≠ 1` empties the lifted residue set for every `q`. -/
theorem liftRes_eq_empty {k l : ℕ} (hl : ¬ Nat.Coprime l k) (q : ℕ) : liftRes k l q = ∅ := by
  ext r
  simp only [liftRes, mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
  intro _ h1 h2
  apply hl
  have hrk : Nat.Coprime r k := Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_left k q) h2
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, ← h1, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hrk

/-- If some `(lᵢ,kᵢ) ≠ 1` the singular series vanishes, so `M = 0`. -/
theorem singSeries_eq_zero {k l : Fin 3 → ℕ} {i : Fin 3} (hl : ¬ Nat.Coprime (l i) (k i))
    (N : ℕ) : singSeries k l N = 0 := by
  have hterm : ∀ q, ssTerm k l N q = 0 := by
    intro q
    refine sum_eq_zero fun a _ => ?_
    rw [Finset.prod_eq_zero (i := i) (mem_univ _)]
    · ring
    · simp [localSum, liftRes_eq_empty hl]
  simp [singSeries, hterm]

/-- The series depends on each `lᵢ` only through `lᵢ mod kᵢ`, so the maximum over all
integers `lᵢ` coprime to `kᵢ` in the paper is the maximum over `residues kᵢ` in Lean. -/
theorem singSeries_mod (k l : Fin 3 → ℕ) (N : ℕ) :
    singSeries k (fun i => l i % k i) N = singSeries k l N := by
  have h : ∀ i q, liftRes (k i) (l i % k i) q = liftRes (k i) (l i) q := by
    intro i q; simp [liftRes]
  simp [singSeries, ssTerm, localSum, h]

/-- For `k = (1,1,1)` the term is the classical one, `Σ_a e(-aN/q) (c_q(a)/φ(q))³`, with
`c_q(a)` the Ramanujan sum written out. -/
theorem ssTerm_classical (l : Fin 3 → ℕ) (N q : ℕ) :
    ssTerm (fun _ => 1) l N q = ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ee (-((a : ℝ) * N / q)) *
        ((∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), ee ((a : ℝ) * r / q)) /
          (q.totient : ℂ)) ^ 3 := by
  have hl : ∀ i, liftRes 1 (l i) q = (range q).filter (fun r => Nat.Coprime r q) := by
    intro i; ext r; simp [liftRes, Nat.mod_one]
  refine sum_congr rfl fun a _ => ?_
  simp only [localSum, hl, Nat.lcm_one_left, Fin.prod_univ_three, Nat.totient_one,
    Nat.cast_one]
  ring

/-! ### The circle method split, display (8) -/

/-- `S_{k,l}(α) = Σ_{p ≤ N, p ≡ l (k)} log p e(αp)`, display (7). -/
noncomputable def Sexp (k l N : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % k = l % k), (Real.log p : ℂ) * ee (α * p)

/-- The integrand `S_{k₁,l₁}(α) S_{k₂,l₂}(α) S_{k₃,l₃}(α) e(-Nα)`. -/
noncomputable def integrand (k l : Fin 3 → ℕ) (N : ℕ) (α : ℝ) : ℂ :=
  Sexp (k 0) (l 0) N α * Sexp (k 1) (l 1) N α * Sexp (k 2) (l 2) N α * ee (-((N : ℝ) * α))

/-- The major arcs `𝔐 = ⋃_{q ≤ Q} ⋃_{(a,q)=1, 0 ≤ a < q} [a/q - 1/(qτ), a/q + 1/(qτ)]`. -/
def majorArcs (Q τ : ℝ) : Set ℝ :=
  ⋃ q ∈ Icc 1 ⌊Q⌋₊, ⋃ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    Set.Icc ((a : ℝ) / q - 1 / (q * τ)) ((a : ℝ) / q + 1 / (q * τ))

theorem measurableSet_majorArcs (Q τ : ℝ) : MeasurableSet (majorArcs Q τ) :=
  Finset.measurableSet_biUnion _ fun _ _ =>
    Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Icc

/-- `R^(M)`: the integral of the integrand over the major arcs inside `[-1/τ, 1 - 1/τ]`. -/
noncomputable def RM (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (∫ α in (-1 / τ)..(1 - 1 / τ), (majorArcs Q τ).indicator (integrand k l N) α).re

/-- `R^(m)`: the integral over the minor arcs `𝔪 = [-1/τ, 1 - 1/τ] \ 𝔐`. -/
noncomputable def Rm (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (∫ α in (-1 / τ)..(1 - 1 / τ), (majorArcs Q τ)ᶜ.indicator (integrand k l N) α).re

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  simp only [ee, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem ee_int (n : ℤ) : ee n = 1 := by
  simp only [ee, Complex.ofReal_intCast]
  rw [show 2 * (π : ℂ) * Complex.I * n = n * (2 * π * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem continuous_ee : Continuous ee := by
  unfold ee; fun_prop

/-- Orthogonality: `∫_c^{c+1} e(nα) dα = [n = 0]`. -/
theorem integral_ee (c : ℝ) (n : ℤ) :
    ∫ α in c..(c + 1), ee ((n : ℝ) * α) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp [ee_zero]
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have h := integral_exp_mul_complex (a := c) (b := c + 1) hc
    have h2 : ∀ x : ℝ, ee ((n : ℝ) * x) = Complex.exp (2 * π * Complex.I * n * x) := by
      intro x; simp only [ee, Complex.ofReal_mul, Complex.ofReal_intCast]; ring_nf
    simp_rw [h2]
    rw [h]
    have h3 : Complex.exp (2 * π * Complex.I * n * ((c + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * n * (c : ℂ)) := by
      rw [← h2, ← h2, mul_add, mul_one, ee_add, ee_int, mul_one]
    rw [h3, sub_self, zero_div]

theorem continuous_Sexp (k l N : ℕ) : Continuous (Sexp k l N) := by
  unfold Sexp
  refine continuous_finsetSum _ fun p _ => continuous_const.mul ?_
  exact continuous_ee.comp (continuous_id.mul continuous_const)

theorem continuous_integrand (k l : Fin 3 → ℕ) (N : ℕ) : Continuous (integrand k l N) := by
  unfold integrand
  exact (((continuous_Sexp _ _ _).mul (continuous_Sexp _ _ _)).mul (continuous_Sexp _ _ _)).mul
    (continuous_ee.comp (continuous_const.mul continuous_id).neg)

/-- The integral of the integrand over any unit interval is `R`. -/
theorem integral_integrand (c : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) :
    ∫ α in c..(c + 1), integrand k l N α = (R k l N : ℂ) := by
  set A := fun i : Fin 3 => (range (N + 1)).filter (fun p => p.Prime ∧ p % k i = l i % k i)
  set w : ℕ × ℕ × ℕ → ℂ := fun p =>
    (Real.log p.1 : ℂ) * (Real.log p.2.1 : ℂ) * (Real.log p.2.2 : ℂ)
  have hexp : ∀ α : ℝ, integrand k l N α = ∑ p ∈ A 0 ×ˢ A 1 ×ˢ A 2,
      w p * ee (((((p.1 + p.2.1 + p.2.2 : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    simp only [integrand, Sexp, sum_product, sum_mul, mul_sum, A, w]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    refine sum_congr rfl fun p1 _ => sum_congr rfl fun p2 _ => sum_congr rfl fun p3 _ => ?_
    have : ee (((((p1 + p2 + p3 : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) * α) =
        ee (α * p1) * ee (α * p2) * ee (α * p3) * ee (-((N : ℝ) * α)) := by
      rw [← ee_add, ← ee_add, ← ee_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hexp]
  have hcont : ∀ p : ℕ × ℕ × ℕ, Continuous (fun α : ℝ =>
      w p * ee (((((p.1 + p.2.1 + p.2.2 : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) * α)) := fun p =>
    continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_finsetSum (fun p _ => (hcont p).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_ee, mul_ite, mul_one, mul_zero,
    sub_eq_zero, Nat.cast_inj]
  rw [← sum_filter]
  unfold R
  push_cast
  refine sum_congr ?_ fun p _ => by simp [w]
  ext ⟨p1, p2, p3⟩
  simp only [mem_filter, mem_product, mem_range, A]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩⟩, h10⟩
    exact ⟨⟨h1, h4, h7⟩, h2, h5, h8, h10, h3, h6, h9⟩
  · rintro ⟨⟨h1, h4, h7⟩, h2, h5, h8, h10, h3, h6, h9⟩
    exact ⟨⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩⟩, h10⟩

/-- `R = R^(M) + R^(m)`, the circle method split on page 2. -/
theorem R_eq_RM_add_Rm (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) :
    R k l N = RM Q τ k l N + Rm Q τ k l N := by
  have hc := continuous_integrand k l N
  have hi : ∀ s : Set ℝ, MeasurableSet s →
      IntervalIntegrable (s.indicator (integrand k l N)) volume (-1 / τ) (1 - 1 / τ) := by
    intro s hs
    exact intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hc.intervalIntegrable (μ := volume) _ _)).indicator hs)
  have hsum := intervalIntegral.integral_add (hi _ (measurableSet_majorArcs Q τ))
    (hi _ (measurableSet_majorArcs Q τ).compl)
  simp only [Set.indicator_self_add_compl_apply] at hsum
  have h1 := integral_integrand (-1 / τ) k l N
  rw [show -1 / τ + 1 = 1 - 1 / τ by ring] at h1
  rw [h1] at hsum
  unfold RM Rm
  rw [← Complex.add_re, ← hsum, Complex.ofReal_re]

/-! ### `𝓔* ≤ E₁ + E₂`, display (8) -/

/-- The shape shared by `𝓔*`, `E₁`, `E₂`: for a quantity `F k l`,
`Σ_{k₁,k₂ ≤ K₁₂} max_{l₁,l₂} |Σ_{k₃ ≤ K₃, (k₃,l₃)=1} λ(k₃) F|`. -/
noncomputable def innerF (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (lam : ℕ → ℝ) (l₃ K₃ k₁ k₂ : ℕ) : ℝ :=
  ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
    |∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * F ![k₁, k₂, k₃] ![l₁, l₂, l₃]|

noncomputable def EF (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) : ℝ :=
  let L := Real.log N
  let K₁₂ := ⌊Real.sqrt N * L ^ (-B)⌋₊
  let K₃ := ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * L ^ (-B)⌋₊
  ∑ k₁ ∈ Icc 1 K₁₂, ∑ k₂ ∈ Icc 1 K₁₂, innerF F lam l₃ K₃ k₁ k₂

theorem Estar_eq_EF (S : SSeries) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    Estar S lam l₃ B N = EF (fun k l => Δ S k l N) lam l₃ B N := rfl

/-- The paper's `Q = L^{20A}`. -/
noncomputable def Qof (A : ℝ) (N : ℕ) : ℝ := Real.log N ^ (20 * A)

/-- The paper's `τ = N Q^{-1}`. -/
noncomputable def τof (A : ℝ) (N : ℕ) : ℝ := N / Qof A N

/-- `E₁ = Σ max |Σ λ(k₃) (R^(M) - M)|`, page 2, with `B = 10⁴ A`. -/
noncomputable def E1 (lam : ℕ → ℝ) (l₃ : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  EF (fun k l => RM (Qof A N) (τof A N) k l N - M singSeries k l N) lam l₃ (10 ^ 4 * A) N

/-- `E₂ = Σ max |Σ λ(k₃) R^(m)|`, page 2, with `B = 10⁴ A`. -/
noncomputable def E2 (lam : ℕ → ℝ) (l₃ : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  EF (fun k l => Rm (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N

/-- Each nested supremum of nonnegative values over two finite sets is at most their sum. -/
theorem iSup2_le_sum (s t : Finset ℕ) (g : ℕ → ℕ → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    (⨆ x ∈ s, ⨆ y ∈ t, g x y) ≤ ∑ x ∈ s, ∑ y ∈ t, g x y := by
  have h0 : 0 ≤ ∑ x ∈ s, ∑ y ∈ t, g x y := sum_nonneg fun _ _ => sum_nonneg fun _ _ => hg _ _
  refine Real.iSup_le (fun x => Real.iSup_le (fun hx => ?_) h0) h0
  refine le_trans ?_ (single_le_sum (f := fun x => ∑ y ∈ t, g x y)
    (fun _ _ => sum_nonneg fun _ _ => hg _ _) hx)
  refine Real.iSup_le (fun y => Real.iSup_le (fun hy => ?_) (sum_nonneg fun _ _ => hg _ _))
    (sum_nonneg fun _ _ => hg _ _)
  exact single_le_sum (f := fun y => g x y) (fun _ _ => hg _ _) hy

/-- A value at a point of the two finite sets is at most the nested supremum. -/
theorem le_iSup2 (s t : Finset ℕ) (g : ℕ → ℕ → ℝ) (hg : ∀ a b, 0 ≤ g a b) {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ t) : g a b ≤ ⨆ x ∈ s, ⨆ y ∈ t, g x y := by
  have hb1 : ∀ x, BddAbove (Set.range fun y => ⨆ (_ : y ∈ t), g x y) := by
    intro x
    refine ⟨∑ y ∈ t, g x y, ?_⟩
    rintro _ ⟨y, rfl⟩
    refine Real.iSup_le (fun hy => single_le_sum (f := fun y => g x y) (fun _ _ => hg _ _) hy)
      (sum_nonneg fun _ _ => hg _ _)
  have hin : g a b ≤ ⨆ y ∈ t, g a y := by
    refine le_ciSup_of_le (hb1 a) b ?_
    exact le_ciSup_of_le (Set.finite_range _).bddAbove hb le_rfl
  refine le_trans hin ?_
  have hb2 : BddAbove (Set.range fun x => ⨆ (_ : x ∈ s), ⨆ y ∈ t, g x y) := by
    refine ⟨∑ x ∈ s, ∑ y ∈ t, g x y, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h0 : 0 ≤ ∑ x ∈ s, ∑ y ∈ t, g x y := sum_nonneg fun _ _ => sum_nonneg fun _ _ => hg _ _
    refine Real.iSup_le (fun hx => ?_) h0
    refine le_trans ?_ (single_le_sum (f := fun x => ∑ y ∈ t, g x y)
      (fun _ _ => sum_nonneg fun _ _ => hg _ _) hx)
    refine Real.iSup_le (fun y => Real.iSup_le (fun hy => ?_) (sum_nonneg fun _ _ => hg _ _))
      (sum_nonneg fun _ _ => hg _ _)
    exact single_le_sum (f := fun y => g x y) (fun _ _ => hg _ _) hy
  refine le_ciSup_of_le hb2 a ?_
  exact le_ciSup_of_le (Set.finite_range _).bddAbove ha le_rfl

theorem innerF_nonneg (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (lam : ℕ → ℝ) (l₃ K₃ k₁ k₂ : ℕ) :
    0 ≤ innerF F lam l₃ K₃ k₁ k₂ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The maximum is subadditive. -/
theorem innerF_add_le (F G : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (lam : ℕ → ℝ) (l₃ K₃ k₁ k₂ : ℕ) :
    innerF (fun k l => F k l + G k l) lam l₃ K₃ k₁ k₂ ≤
      innerF F lam l₃ K₃ k₁ k₂ + innerF G lam l₃ K₃ k₁ k₂ := by
  have h0 := add_nonneg (innerF_nonneg F lam l₃ K₃ k₁ k₂) (innerF_nonneg G lam l₃ K₃ k₁ k₂)
  refine Real.iSup_le (fun l₁ => Real.iSup_le (fun h₁ => Real.iSup_le
    (fun l₂ => Real.iSup_le (fun h₂ => ?_) h0) h0) h0) h0
  simp only [mul_add, sum_add_distrib]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · exact le_iSup2 _ _ (fun l₁ l₂ => |∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
      lam k₃ * F ![k₁, k₂, k₃] ![l₁, l₂, l₃]|) (fun _ _ => abs_nonneg _) h₁ h₂
  · exact le_iSup2 _ _ (fun l₁ l₂ => |∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
      lam k₃ * G ![k₁, k₂, k₃] ![l₁, l₂, l₃]|) (fun _ _ => abs_nonneg _) h₁ h₂

theorem EF_nonneg (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    0 ≤ EF F lam l₃ B N :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => innerF_nonneg _ _ _ _ _ _

theorem EF_add_le (F G : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    EF (fun k l => F k l + G k l) lam l₃ B N ≤ EF F lam l₃ B N + EF G lam l₃ B N := by
  simp only [EF, ← sum_add_distrib]
  exact sum_le_sum fun _ _ => sum_le_sum fun _ _ => innerF_add_le _ _ _ _ _ _ _

/-- Display (8): `𝓔* ≤ E₁ + E₂`, PROVED, from `R = R^(M) + R^(m)`. -/
theorem Estar_le_E1_add_E2 (lam : ℕ → ℝ) (l₃ : ℕ) (A : ℝ) (N : ℕ) :
    Estar singSeries lam l₃ (10 ^ 4 * A) N ≤ E1 lam l₃ A N + E2 lam l₃ A N := by
  rw [Estar_eq_EF]
  have : (fun k l => Δ singSeries k l N) = fun k l =>
      (RM (Qof A N) (τof A N) k l N - M singSeries k l N) + Rm (Qof A N) (τof A N) k l N := by
    funext k l
    rw [Δ, R_eq_RM_add_Rm (Qof A N) (τof A N)]; ring
  rw [this]
  exact EF_add_le _ _ _ _ _ _

/-! ### The conditional deduction -/

/-- Cited input, display (9), from Tolev 1999 sections 4 and 5 and Halupczok 2008 Theorem 3:
the major arc error `E₁ ≪ N² L^{-A}` with `B = 10⁴ A`, for `A ≥ 10⁴`. -/
def BoundE1 : Prop :=
  ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
    ∀ N : ℕ, Odd N → N₀ ≤ N → E1 lam l₃ A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)

/-- Cited input, displays (10) to (20), resting on display (12) from Tolev 1999 Lemma 12:
the minor arc sum `E₂ ≪ N² L^{-A}` with `B = 10⁴ A`, for `A ≥ 10⁴`. -/
def BoundE2 : Prop :=
  ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
    ∀ N : ℕ, Odd N → N₀ ≤ N → E2 lam l₃ A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)

/-- The main Theorem, from `BoundE1` and `BoundE2`. The reduction to `A ≥ 10⁴`,
display (6), and the split (8) are proved. -/
theorem mainTheorem_of_E1_E2 (h1 : BoundE1) (h2 : BoundE2) : MainTheorem := by
  intro A hA
  set A' := max A (10 ^ 4) with hA'
  have hA'1 : (10 : ℝ) ^ 4 ≤ A' := le_max_right _ _
  refine ⟨10 ^ 4 * A', by positivity, fun l₃ hl₃ => ?_⟩
  obtain ⟨C₁, N₁, hC₁⟩ := h1 A' hA'1 l₃ hl₃
  obtain ⟨C₂, N₂, hC₂⟩ := h2 A' hA'1 l₃ hl₃
  refine ⟨max C₁ 0 + max C₂ 0, max (max N₁ N₂) 3, fun lam hlam N hN hN0 => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN0
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN0
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN0
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hN3
  have hpow : Real.log N ^ (-A') ≤ Real.log N ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (le_max_left _ _))
  have hX : 0 ≤ (N : ℝ) ^ 2 * Real.log N ^ (-A') := by positivity
  have hXX : (N : ℝ) ^ 2 * Real.log N ^ (-A') ≤ (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have e1 := hC₁ lam hlam N hN hN1
  have e2 := hC₂ lam hlam N hN hN2
  have hs := Estar_le_E1_add_E2 lam l₃ A' N
  have m1 : C₁ * (N : ℝ) ^ 2 * Real.log N ^ (-A') ≤ max C₁ 0 * ((N : ℝ) ^ 2 * Real.log N ^ (-A')) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have m2 : C₂ * (N : ℝ) ^ 2 * Real.log N ^ (-A') ≤ max C₂ 0 * ((N : ℝ) ^ 2 * Real.log N ^ (-A')) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have hc0 : 0 ≤ max C₁ 0 + max C₂ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  calc Estar singSeries lam l₃ (10 ^ 4 * A') N ≤ E1 lam l₃ A' N + E2 lam l₃ A' N := hs
    _ ≤ (max C₁ 0 + max C₂ 0) * ((N : ℝ) ^ 2 * Real.log N ^ (-A')) := by nlinarith
    _ ≤ (max C₁ 0 + max C₂ 0) * ((N : ℝ) ^ 2 * Real.log N ^ (-A)) :=
        mul_le_mul_of_nonneg_left hXX hc0
    _ = (max C₁ 0 + max C₂ 0) * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by ring

/-! ### Exponent bookkeeping, displays (6), (10), (12), (17) to (20) -/

theorem rpow_sq_half {L : ℝ} (hL : 0 < L) (x : ℝ) : L ^ (2 * x) = (L ^ x) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; ring_nf

/-- Display (20) from display (12): with `sup_𝔪 |K| ≤ c N L^{350-4A}` and `∫|K|² ≤ c' N L^{20}`,
`W* ≤ c'' L^8 N^{1/2} (sup|K|)(∫|K|²)^{1/2}` gives `W* ≤ c'' c √c' N² L^{368-4A}`, inside the
paper's `N² L^{400-4A}`. -/
theorem Wstar_bookkeeping {A L N Ws Kmax K2 c c' c'' : ℝ} (hL : 1 ≤ L) (hN : 0 ≤ N)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hc'' : 0 ≤ c'')
    (h12a : Kmax ≤ c * N * L ^ (350 - 4 * A)) (h12b : K2 ≤ c' * N * L ^ (20 : ℝ))
    (hW : Ws ≤ c'' * L ^ (8 : ℝ) * Real.sqrt N * (Kmax * Real.sqrt K2)) :
    Ws ≤ c'' * c * Real.sqrt c' * N ^ 2 * L ^ (400 - 4 * A) := by
  have hL0 : 0 < L := by linarith
  have hsK2 : Real.sqrt K2 ≤ Real.sqrt c' * Real.sqrt N * L ^ (10 : ℝ) := by
    calc Real.sqrt K2 ≤ Real.sqrt (c' * N * L ^ (20 : ℝ)) := Real.sqrt_le_sqrt h12b
      _ = Real.sqrt c' * Real.sqrt N * L ^ (10 : ℝ) := by
        rw [show (20 : ℝ) = 2 * 10 by norm_num, rpow_sq_half hL0, Real.sqrt_mul (by positivity),
          Real.sqrt_mul hc', Real.sqrt_sq (by positivity)]
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  have hprod : Kmax * Real.sqrt K2 ≤ (c * N * L ^ (350 - 4 * A)) *
      (Real.sqrt c' * Real.sqrt N * L ^ (10 : ℝ)) :=
    mul_le_mul h12a hsK2 (Real.sqrt_nonneg _) (by positivity)
  have hpow : L ^ (8 : ℝ) * L ^ (350 - 4 * A) * L ^ (10 : ℝ) ≤ L ^ (400 - 4 * A) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc Ws ≤ c'' * L ^ (8 : ℝ) * Real.sqrt N * (Kmax * Real.sqrt K2) := hW
    _ ≤ c'' * L ^ (8 : ℝ) * Real.sqrt N * ((c * N * L ^ (350 - 4 * A)) *
        (Real.sqrt c' * Real.sqrt N * L ^ (10 : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = c'' * c * Real.sqrt c' * N * (Real.sqrt N * Real.sqrt N) *
        (L ^ (8 : ℝ) * L ^ (350 - 4 * A) * L ^ (10 : ℝ)) := by ring
    _ ≤ c'' * c * Real.sqrt c' * N * (Real.sqrt N * Real.sqrt N) * L ^ (400 - 4 * A) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = c'' * c * Real.sqrt c' * N ^ 2 * L ^ (400 - 4 * A) := by rw [hsN]; ring

/-- The closing step of the proof: from `B = 10⁴ A`, `A ≥ 10⁴`, display (19)
`W' ≤ c₁ L^{20-2B} N²`, display (20) `W* ≤ c₂ N² L^{400-4A}`, display (17)
`V ≤ c₃ L³ N W^{1/2}` with `W = W' + W*` from (18), and display (10) `E₂ ≤ c₄ L² V`,
we get `E₂ ≤ c₄ c₃ (√c₁ + √c₂) N² L^{-A}`. -/
theorem E2_bookkeeping {A B L N W₁ Ws V E c₁ c₂ c₃ c₄ : ℝ} (hA : 10 ^ 4 ≤ A)
    (hB : B = 10 ^ 4 * A) (hL : 1 ≤ L) (hN : 0 ≤ N) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) (hW₁ : 0 ≤ W₁) (hWs : 0 ≤ Ws)
    (h19 : W₁ ≤ c₁ * L ^ (20 - 2 * B) * N ^ 2) (h20 : Ws ≤ c₂ * N ^ 2 * L ^ (400 - 4 * A))
    (h17 : V ≤ c₃ * L ^ 3 * N * Real.sqrt (W₁ + Ws)) (h10 : E ≤ c₄ * L ^ 2 * V) :
    E ≤ c₄ * c₃ * (Real.sqrt c₁ + Real.sqrt c₂) * N ^ 2 * L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have hs1 : Real.sqrt W₁ ≤ Real.sqrt c₁ * L ^ (10 - B) * N := by
    calc Real.sqrt W₁ ≤ Real.sqrt (c₁ * L ^ (20 - 2 * B) * N ^ 2) := Real.sqrt_le_sqrt h19
      _ = Real.sqrt c₁ * L ^ (10 - B) * N := by
        rw [show (20 : ℝ) - 2 * B = 2 * (10 - B) by ring, rpow_sq_half hL0,
          Real.sqrt_mul (by positivity), Real.sqrt_mul hc₁, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hN]
  have hs2 : Real.sqrt Ws ≤ Real.sqrt c₂ * N * L ^ (200 - 2 * A) := by
    calc Real.sqrt Ws ≤ Real.sqrt (c₂ * N ^ 2 * L ^ (400 - 4 * A)) := Real.sqrt_le_sqrt h20
      _ = Real.sqrt c₂ * N * L ^ (200 - 2 * A) := by
        rw [show (400 : ℝ) - 4 * A = 2 * (200 - 2 * A) by ring, rpow_sq_half hL0,
          Real.sqrt_mul (by positivity), Real.sqrt_mul hc₂, Real.sqrt_sq hN,
          Real.sqrt_sq (Real.rpow_nonneg hL0.le _)]
  have hsum : Real.sqrt (W₁ + Ws) ≤ Real.sqrt W₁ + Real.sqrt Ws := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hW₁, Real.sq_sqrt hWs, Real.sqrt_nonneg W₁, Real.sqrt_nonneg Ws]
  have hL5 : L ^ 2 * L ^ 3 = L ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have p1 : L ^ (5 : ℝ) * L ^ (10 - B) ≤ L ^ (-A) := by
    rw [← Real.rpow_add hL0]; exact Real.rpow_le_rpow_of_exponent_le hL (by subst hB; linarith)
  have p2 : L ^ (5 : ℝ) * L ^ (200 - 2 * A) ≤ L ^ (-A) := by
    rw [← Real.rpow_add hL0]; exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hV : V ≤ c₃ * L ^ 3 * N * (Real.sqrt c₁ * L ^ (10 - B) * N +
      Real.sqrt c₂ * N * L ^ (200 - 2 * A)) :=
    le_trans h17 (mul_le_mul_of_nonneg_left (le_trans hsum (add_le_add hs1 hs2)) (by positivity))
  have hsc₁ := Real.sqrt_nonneg c₁
  have hsc₂ := Real.sqrt_nonneg c₂
  calc E ≤ c₄ * L ^ 2 * V := h10
    _ ≤ c₄ * L ^ 2 * (c₃ * L ^ 3 * N * (Real.sqrt c₁ * L ^ (10 - B) * N +
          Real.sqrt c₂ * N * L ^ (200 - 2 * A))) := mul_le_mul_of_nonneg_left hV (by positivity)
    _ = c₄ * c₃ * N ^ 2 * (Real.sqrt c₁ * (L ^ 2 * L ^ 3 * L ^ (10 - B)) +
          Real.sqrt c₂ * (L ^ 2 * L ^ 3 * L ^ (200 - 2 * A))) := by ring
    _ ≤ c₄ * c₃ * N ^ 2 * (Real.sqrt c₁ * L ^ (-A) + Real.sqrt c₂ * L ^ (-A)) := by
        rw [hL5]
        gcongr
    _ = c₄ * c₃ * (Real.sqrt c₁ + Real.sqrt c₂) * N ^ 2 * L ^ (-A) := by ring

/-- Non vacuity of `E2_bookkeeping`: its hypotheses hold with every quantity `1`
except `B = 10⁸`, `A = 10⁴`. -/
example : ∃ A B L N W₁ Ws V E c₁ c₂ c₃ c₄ : ℝ, 10 ^ 4 ≤ A ∧ B = 10 ^ 4 * A ∧ 1 ≤ L ∧ 0 ≤ N ∧
    0 < W₁ ∧ 0 < Ws ∧ 0 < V ∧ 0 < E ∧
    W₁ ≤ c₁ * L ^ (20 - 2 * B) * N ^ 2 ∧ Ws ≤ c₂ * N ^ 2 * L ^ (400 - 4 * A) ∧
    V ≤ c₃ * L ^ 3 * N * Real.sqrt (W₁ + Ws) ∧ E ≤ c₄ * L ^ 2 * V := by
  refine ⟨10 ^ 4, 10 ^ 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, by norm_num, by norm_num, le_rfl,
    zero_le_one, one_pos, one_pos, one_pos, one_pos, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp only [one_pow, mul_one, one_mul]
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · simp

end LeanLab.Tolev2009.Faithful
