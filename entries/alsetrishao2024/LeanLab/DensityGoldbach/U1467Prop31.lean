module

public import LeanLab.DensityGoldbach.U1448Fix

/-!
U-1467, run 20261022T0403Z-7595, P0047 Alsetri and Shao 2024, arXiv 2405.18576v2, Section 3.

Goal: remove cited inputs from `U1448.alsetriShao_1_2_of_printed`, which is CONDITIONAL ON
`AS_Prop31Printed`, `Green62`, `Green66`. Of the three, the transference principle,
Proposition 3.1, is the elementary one: it is pure Fourier analysis on `Z_N`, while Green's
Lemmas 6.2 and 6.6 are exponential sum and restriction estimates over primes.

The paper proves Proposition 3.1 from three lemmas. Lemma 3.2 builds a bounded approximant
`g_i` of `f_i` with a Bohr set; Lemma 3.3 shows `g_1 * g_2 ≥ δ³/200` everywhere; Lemma 3.4
transfers this to `f_1 * f_2` off `η N` points by Plancherel and an `ℓ^∞`, `ℓ^{p/2}`
interpolation. Here Lemmas 3.3 and 3.4 and the assembly are PROVED, with Fourier inversion for
the convolution and Parseval on `ZMod N` proved from scratch from the orthogonality
`AddChar.sum_mulShift` of Mathlib. Lemma 3.2 is the one remaining input, `AS_Lemma32`.

Lemma 3.3 is proved with a pointwise inequality `g₁(m) g₂(n-m) ≥ (δ/10)² (u₁(m) + u₂(n-m) - 1)`,
`u_i` the indicator of `g_i ≥ δ/10`, which gives `δ³/125 ≥ δ³/200`.

Result: `as_prop31_of_lemma32 : AS_Lemma32 → AS_Prop31`, hence `AS_Prop31Printed`, and the
headline `alsetriShao_1_2_of_lemma32 : AS_Lemma32 → Green62 → Green66 → AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical ComplexConjugate

noncomputable section
namespace LeanLab.DensityGoldbach.U1467
open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1448

/-- **Alsetri-Shao, Lemma 3.2**, arXiv 2405.18576v2 Section 3: under the assumptions of
Proposition 3.1, for every `ε > 0` and `c` small in terms of `ε, δ, p, M`, there are
approximants `g_i ≥ 0` with `E g_i = E f_i`, `‖g_i‖_∞ ≤ 1 + δ/10`, `‖f̂_i - ĝ_i‖_∞ ≤ ε` and
`‖ĝ_i‖_p ≤ M`. Restricted to prime `N ≥ N₀` and `δ < 1/2`, as `AS_Prop31` is. -/
def AS_Lemma32 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∀ p : ℝ, 2 < p → p < 4 → ∀ Mc : ℝ, 1 ≤ Mc →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N.Prime → N₀ ≤ N →
      ∀ f₁ f₂ ν₁ ν₂ : ZMod N → ℝ,
        (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ ν₁ n) → (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ ν₂ n) →
        1 + δ ≤ avg N f₁ + avg N f₂ →
        lpHat N p f₁ ≤ Mc → lpHat N p f₂ ≤ Mc →
        (∀ r, ‖hatE N ν₁ r - (if r = 0 then 1 else 0)‖ ≤ c) →
        (∀ r, ‖hatE N ν₂ r - (if r = 0 then 1 else 0)‖ ≤ c) →
        ∃ g₁ g₂ : ZMod N → ℝ,
          (∀ n, 0 ≤ g₁ n ∧ g₁ n ≤ 1 + δ / 10) ∧ (∀ n, 0 ≤ g₂ n ∧ g₂ n ≤ 1 + δ / 10) ∧
          avg N g₁ = avg N f₁ ∧ avg N g₂ = avg N f₂ ∧
          (∀ r, ‖hatE N f₁ r - hatE N g₁ r‖ ≤ ε) ∧ (∀ r, ‖hatE N f₂ r - hatE N g₂ r‖ ≤ ε) ∧
          lpHat N p g₁ ≤ Mc ∧ lpHat N p g₂ ≤ Mc

variable {N : ℕ} [NeZero N]

/-! ### Fourier analysis on `ZMod N` -/

lemma orth (x : ZMod N) :
    ∑ r : ZMod N, ZMod.stdAddChar (r * x) = if x = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)]
  simp [ZMod.card]

lemma norm_e (x : ZMod N) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N

/-- Fourier inversion of the convolution: `f * g(n) = Σ_r f̂(r) ĝ(r) e_N(rn)`. -/
lemma conv_inv (f g : ZMod N → ℝ) (n : ZMod N) :
    ((convE N f g n : ℝ) : ℂ) =
      ∑ r : ZMod N, hatE N f r * hatE N g r * ZMod.stdAddChar (r * n) := by
  have key : ∀ r : ZMod N, hatE N f r * hatE N g r * ZMod.stdAddChar (r * n) =
      (1 / (N : ℂ)) * (1 / (N : ℂ)) * ∑ a : ZMod N, ∑ b : ZMod N,
        ((f a : ℂ) * (g b : ℂ)) * ZMod.stdAddChar (r * (n - a - b)) := by
    intro r
    unfold hatE
    have e1 : ∀ a b : ZMod N, ZMod.stdAddChar (r * (n - a - b)) =
        ZMod.stdAddChar (-(r * a)) * ZMod.stdAddChar (-(r * b)) * ZMod.stdAddChar (r * n) := by
      intro a b
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    simp_rw [e1]
    rw [show ∀ x y z : ℂ, (1 / (N : ℂ) * x) * (1 / (N : ℂ) * y) * z =
      1 / (N : ℂ) * (1 / (N : ℂ)) * (x * y * z) from fun x y z => by ring]
    congr 1
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Finset.sum_congr rfl (fun r _ => key r), ← Finset.mul_sum]
  have h2 : ∑ r : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N,
      ((f a : ℂ) * (g b : ℂ)) * ZMod.stdAddChar (r * (n - a - b)) =
      ∑ a : ZMod N, ∑ b : ZMod N, ((f a : ℂ) * (g b : ℂ)) *
        ∑ r : ZMod N, ZMod.stdAddChar (r * (n - a - b)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [h2]
  simp_rw [orth]
  have h3 : ∀ a : ZMod N, ∑ b : ZMod N, ((f a : ℂ) * (g b : ℂ)) *
      (if n - a - b = 0 then (N : ℂ) else 0) = (f a : ℂ) * (g (n - a) : ℂ) * N := by
    intro a
    rw [Finset.sum_eq_single (n - a)]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; apply hb; rw [sub_eq_zero] at h; exact h.symm
    · simp
  simp_rw [h3]
  unfold convE
  push_cast
  rw [← Finset.sum_mul]
  field_simp [hN]

/-- Parseval: `Σ_r |ĥ(r)|² = E_n h(n)²`. -/
lemma parseval (h : ZMod N → ℝ) :
    ∑ r : ZMod N, ‖hatE N h r‖ ^ 2 = (1 / (N : ℝ)) * ∑ n : ZMod N, h n ^ 2 := by
  have hc : ∀ r : ZMod N, ((‖hatE N h r‖ : ℝ) : ℂ) ^ 2 =
      (1 / (N : ℂ)) * (1 / (N : ℂ)) * ∑ a : ZMod N, ∑ b : ZMod N,
        ((h a : ℂ) * (h b : ℂ)) * ZMod.stdAddChar (r * (b - a)) := by
    intro r
    rw [← Complex.mul_conj', hatE, map_mul, map_sum]
    have e1 : ∀ b : ZMod N, conj ((h b : ℂ) * ZMod.stdAddChar (-(r * b))) =
        (h b : ℂ) * ZMod.stdAddChar (r * b) := by
      intro b
      rw [map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj, neg_neg]
    simp_rw [e1]
    have e2 : conj (1 / (N : ℂ)) = 1 / (N : ℂ) := by simp
    rw [e2]
    have e3 : ∀ a b : ZMod N, ZMod.stdAddChar (r * (b - a)) =
        ZMod.stdAddChar (-(r * a)) * ZMod.stdAddChar (r * b) := by
      intro a b
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    simp_rw [e3]
    rw [show ∀ x y : ℂ, (1 / (N : ℂ) * x) * (1 / (N : ℂ) * y) =
      1 / (N : ℂ) * (1 / (N : ℂ)) * (x * y) from fun x y => by ring]
    congr 1
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsum : ((∑ r : ZMod N, ‖hatE N h r‖ ^ 2 : ℝ) : ℂ) =
      (((1 / (N : ℝ)) * ∑ n : ZMod N, h n ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp_rw [hc]
    rw [← Finset.mul_sum]
    have h2 : ∑ r : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N,
        ((h a : ℂ) * (h b : ℂ)) * ZMod.stdAddChar (r * (b - a)) =
        ∑ a : ZMod N, ∑ b : ZMod N, ((h a : ℂ) * (h b : ℂ)) *
          ∑ r : ZMod N, ZMod.stdAddChar (r * (b - a)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
    rw [h2]
    simp_rw [orth]
    have h3 : ∀ a : ZMod N, ∑ b : ZMod N, ((h a : ℂ) * (h b : ℂ)) *
        (if b - a = 0 then (N : ℂ) else 0) = (h a : ℂ) ^ 2 * N := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [sub_self, if_pos rfl]; ring
      · intro b _ hb
        rw [if_neg, mul_zero]
        intro h'; apply hb; rwa [sub_eq_zero] at h'
      · simp
    simp_rw [h3]
    rw [← Finset.sum_mul]
    field_simp [hN]
  exact_mod_cast hsum

/-- `|f̂(r)| ≤ E f` for `f ≥ 0`. -/
lemma norm_hatE_le (f : ZMod N → ℝ) (hf : ∀ n, 0 ≤ f n) (r : ZMod N) :
    ‖hatE N f r‖ ≤ avg N f := by
  unfold hatE avg
  rw [norm_mul]
  have hN' : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by
    rw [norm_div, norm_one]; simp
  rw [hN']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n)]

lemma avg_mono (f g : ZMod N → ℝ) (h : ∀ n, f n ≤ g n) : avg N f ≤ avg N g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => h n) (by positivity)

/-- `‖f̂‖_p ≤ M` gives `Σ_r |f̂(r)|^p ≤ M^p`. -/
lemma sum_pow_le (f : ZMod N → ℝ) (p Mc : ℝ) (hp : 0 < p) (h : lpHat N p f ≤ Mc) :
    ∑ r : ZMod N, ‖hatE N f r‖ ^ p ≤ Mc ^ p := by
  unfold lpHat at h
  have hS : 0 ≤ ∑ r : ZMod N, ‖hatE N f r‖ ^ p :=
    Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _
  have e : (∑ r : ZMod N, ‖hatE N f r‖ ^ p) =
      ((∑ r : ZMod N, ‖hatE N f r‖ ^ p) ^ (1 / p)) ^ p := by
    rw [one_div, Real.rpow_inv_rpow hS hp.ne']
  rw [e]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hS _) h hp.le

/-! ### Lemma 3.3 -/

/-- **Alsetri-Shao Lemma 3.3**: `0 ≤ g_i ≤ 1 + δ/10` and `E g₁ + E g₂ ≥ 1 + δ` give
`g₁ * g₂(n) ≥ δ³/200` for every `n`. -/
theorem lemma33 (g₁ g₂ : ZMod N → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (h1 : ∀ n, 0 ≤ g₁ n ∧ g₁ n ≤ 1 + δ / 10) (h2 : ∀ n, 0 ≤ g₂ n ∧ g₂ n ≤ 1 + δ / 10)
    (hs : 1 + δ ≤ avg N g₁ + avg N g₂) (n : ZMod N) : δ ^ 3 / 200 ≤ convE N g₁ g₂ n := by
  set t := δ / 10 with ht
  have ht0 : 0 < t := by positivity
  let u : (ZMod N → ℝ) → ZMod N → ℝ := fun g m => if t ≤ g m then 1 else 0
  have hu : ∀ g : ZMod N → ℝ, (∀ m, 0 ≤ g m ∧ g m ≤ 1 + t) → ∀ m, g m ≤ u g m + t := by
    intro g hg m
    simp only [u]
    split_ifs with h
    · linarith [(hg m).2]
    · push Not at h; linarith
  have hpt : ∀ m, t ^ 2 * (u g₁ m + u g₂ (n - m) - 1) ≤ g₁ m * g₂ (n - m) := by
    intro m
    simp only [u]
    split_ifs with ha hb hb
    · have := mul_le_mul ha hb ht0.le (h1 m).1
      nlinarith
    · nlinarith [mul_nonneg (h1 m).1 (h2 (n - m)).1]
    · nlinarith [mul_nonneg (h1 m).1 (h2 (n - m)).1]
    · nlinarith [mul_nonneg (h1 m).1 (h2 (n - m)).1]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (Finset.univ : Finset (ZMod N)).card = N := by simp [ZMod.card]
  have hsumu : ∀ g : ZMod N → ℝ, (∀ m, 0 ≤ g m ∧ g m ≤ 1 + t) →
      N * avg N g - N * t ≤ ∑ m : ZMod N, u g m := by
    intro g hg
    have : ∑ m : ZMod N, g m ≤ ∑ m : ZMod N, (u g m + t) :=
      Finset.sum_le_sum fun m _ => hu g hg m
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at this
    unfold avg
    field_simp
    linarith
  have hshift : ∑ m : ZMod N, u g₂ (n - m) = ∑ m : ZMod N, u g₂ m :=
    Equiv.sum_comp (Equiv.subLeft n) (u g₂)
  have hA := hsumu g₁ h1
  have hB := hsumu g₂ h2
  have htot : t ^ 2 * (∑ m : ZMod N, u g₁ m + ∑ m : ZMod N, u g₂ m - N) ≤
      ∑ m : ZMod N, g₁ m * g₂ (n - m) := by
    have := Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hpt m
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, hshift,
      Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at this
    exact this
  unfold convE
  rw [ht] at htot hA hB
  have key : δ ^ 3 / 200 * N ≤ ∑ m : ZMod N, g₁ m * g₂ (n - m) := by
    have hlow : 4 * δ / 5 * N ≤ ∑ m : ZMod N, u g₁ m + ∑ m : ZMod N, u g₂ m - N := by
      nlinarith
    have : (δ / 10) ^ 2 * (4 * δ / 5 * N) ≤
        (δ / 10) ^ 2 * (∑ m : ZMod N, u g₁ m + ∑ m : ZMod N, u g₂ m - N) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    have h3 : δ ^ 3 / 200 * N ≤ (δ / 10) ^ 2 * (4 * δ / 5 * N) := by
      have : 0 ≤ δ ^ 3 * N := by positivity
      nlinarith
    linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hN0]
  exact key

/-! ### Lemma 3.4 -/

/-- The Plancherel step of Lemma 3.4: if `g₁ * g₂ ≥ θ + τ` everywhere, the set
`E = {f₁ * f₂ ≤ θ}` has `(|E|/N) τ² ≤ Σ_r |ĝ₁ĝ₂ - f̂₁f̂₂|²`. -/
theorem exc_plancherel (f₁ f₂ g₁ g₂ : ZMod N → ℝ) (θ τ : ℝ) (hτ : 0 < τ)
    (hg : ∀ n, θ + τ ≤ convE N g₁ g₂ n) :
    ((univ.filter (fun n => convE N f₁ f₂ n ≤ θ)).card : ℝ) / N * τ ^ 2 ≤
      ∑ r : ZMod N, ‖hatE N g₁ r * hatE N g₂ r - hatE N f₁ r * hatE N f₂ r‖ ^ 2 := by
  set E := univ.filter (fun n => convE N f₁ f₂ n ≤ θ) with hE
  set D : ZMod N → ℂ := fun r => hatE N g₁ r * hatE N g₂ r - hatE N f₁ r * hatE N f₂ r
  set ind : ZMod N → ℝ := fun n => if n ∈ E then 1 else 0 with hind
  set α : ℝ := (E.card : ℝ) / N with hα
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the pairing `I = E_n 1_E(n) (g₁*g₂ - f₁*f₂)(n)`
  set I : ℝ := (1 / (N : ℝ)) * ∑ n : ZMod N, ind n * (convE N g₁ g₂ n - convE N f₁ f₂ n)
  have hIlow : τ * α ≤ I := by
    have : ∀ n, τ * ind n ≤ ind n * (convE N g₁ g₂ n - convE N f₁ f₂ n) := by
      intro n
      simp only [ind]
      split_ifs with h
      · rw [hE, mem_filter] at h
        linarith [hg n, h.2]
      · simp
    have hs := Finset.sum_le_sum fun n (_ : n ∈ univ) => this n
    rw [← Finset.mul_sum] at hs
    have hsi : ∑ n : ZMod N, ind n = E.card := by
      simp only [ind]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsi] at hs
    simp only [I, hα]
    rw [mul_div_assoc', div_eq_mul_one_div, mul_comm (τ * _)]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  -- `I = Σ_r D(r) conj(1̂_E(r))`
  have hIc : (I : ℂ) = ∑ r : ZMod N, D r * conj (hatE N ind r) := by
    have hconj : ∀ r : ZMod N, conj (hatE N ind r) =
        (1 / (N : ℂ)) * ∑ n : ZMod N, (ind n : ℂ) * ZMod.stdAddChar (r * n) := by
      intro r
      rw [hatE, map_mul, map_sum]
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj, neg_neg]
    simp_rw [hconj]
    simp only [I]
    push_cast
    have hdiff : ∀ n : ZMod N, ((convE N g₁ g₂ n : ℝ) : ℂ) - ((convE N f₁ f₂ n : ℝ) : ℂ) =
        ∑ r : ZMod N, D r * ZMod.stdAddChar (r * n) := by
      intro n
      rw [conv_inv, conv_inv, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [D]; ring
    simp_rw [hdiff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  -- Cauchy-Schwarz and Parseval for `1_E`
  have hpars : ∑ r : ZMod N, ‖hatE N ind r‖ ^ 2 = α := by
    rw [parseval]
    have : ∀ n, ind n ^ 2 = ind n := by intro n; simp only [ind]; split_ifs <;> norm_num
    simp_rw [this]
    simp only [ind]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one, hα]
    ring
  have hIup : I ≤ ∑ r : ZMod N, ‖D r‖ * ‖hatE N ind r‖ := by
    have h1 : I ≤ ‖(I : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self I
    refine h1.trans ?_
    rw [hIc]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
    rw [norm_mul, Complex.norm_conj]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq univ (fun r => ‖D r‖) (fun r => ‖hatE N ind r‖)
  rw [hpars] at hCS
  have hα0 : 0 ≤ α := by positivity
  have hI0 : 0 ≤ τ * α := by positivity
  have hsq : (τ * α) ^ 2 ≤ (∑ r : ZMod N, ‖D r‖ ^ 2) * α :=
    (pow_le_pow_left₀ hI0 (hIlow.trans hIup) 2).trans hCS
  rcases hα0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact Finset.sum_nonneg fun r _ => by positivity
  · have : α * τ ^ 2 * α ≤ (∑ r : ZMod N, ‖D r‖ ^ 2) * α := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- The interpolation step of Lemma 3.4: `|D| ≤ s` and `|D| ≤ |a₁a₂| + |b₁b₂|` with
`Σ|a_i|^p, Σ|b_i|^p ≤ K`, `2 < p < 4`, give `Σ|D|² ≤ 8 K s^{2 - p/2}`. -/
theorem interp (D a₁ a₂ b₁ b₂ : ZMod N → ℂ) (p s K : ℝ) (hp : 2 < p) (hp4 : p < 4)
    (hs : ∀ r, ‖D r‖ ≤ s) (hD : ∀ r, ‖D r‖ ≤ ‖a₁ r‖ * ‖a₂ r‖ + ‖b₁ r‖ * ‖b₂ r‖)
    (ha₁ : ∑ r : ZMod N, ‖a₁ r‖ ^ p ≤ K) (ha₂ : ∑ r : ZMod N, ‖a₂ r‖ ^ p ≤ K)
    (hb₁ : ∑ r : ZMod N, ‖b₁ r‖ ^ p ≤ K) (hb₂ : ∑ r : ZMod N, ‖b₂ r‖ ^ p ≤ K) :
    ∑ r : ZMod N, ‖D r‖ ^ 2 ≤ 8 * K * s ^ (2 - p / 2) := by
  set q := p / 2 with hq
  have hq1 : 1 < q := by simp only [q]; linarith
  have hq2 : q < 2 := by simp only [q]; linarith
  have hK : 0 ≤ K := le_trans (Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _) ha₁
  -- the Cauchy-Schwarz step `Σ |x|^q |y|^q ≤ K`
  have cs : ∀ x y : ZMod N → ℂ, ∑ r : ZMod N, ‖x r‖ ^ p ≤ K → ∑ r : ZMod N, ‖y r‖ ^ p ≤ K →
      ∑ r : ZMod N, ‖x r‖ ^ q * ‖y r‖ ^ q ≤ K := by
    intro x y hx hy
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun r => ‖x r‖ ^ q) (fun r => ‖y r‖ ^ q)
    have e : ∀ z : ℂ, (‖z‖ ^ q) ^ 2 = ‖z‖ ^ p := by
      intro z
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      congr 1; simp only [q]; ring
    simp_rw [e] at h
    have h2 : (∑ r : ZMod N, ‖x r‖ ^ q * ‖y r‖ ^ q) ^ 2 ≤ K ^ 2 := by
      refine h.trans ?_
      rw [sq]
      exact mul_le_mul hx hy (Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _) hK
    have h0 : 0 ≤ ∑ r : ZMod N, ‖x r‖ ^ q * ‖y r‖ ^ q :=
      Finset.sum_nonneg fun r _ => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _)
    exact (pow_le_pow_iff_left₀ h0 hK two_ne_zero).1 h2
  have hA := cs a₁ a₂ ha₁ ha₂
  have hB := cs b₁ b₂ hb₁ hb₂
  -- pointwise bound
  have hpt : ∀ r, ‖D r‖ ^ 2 ≤ s ^ (2 - q) *
      (4 * (‖a₁ r‖ ^ q * ‖a₂ r‖ ^ q + ‖b₁ r‖ ^ q * ‖b₂ r‖ ^ q)) := by
    intro r
    have hd0 := norm_nonneg (D r)
    have e1 : ‖D r‖ ^ 2 = ‖D r‖ ^ (2 - q) * ‖D r‖ ^ q := by
      rw [← Real.rpow_add' hd0 (by norm_num), sub_add_cancel, Real.rpow_two]
    have e2 : ‖D r‖ ^ (2 - q) ≤ s ^ (2 - q) := Real.rpow_le_rpow hd0 (hs r) (by linarith)
    set x := ‖a₁ r‖ * ‖a₂ r‖
    set y := ‖b₁ r‖ * ‖b₂ r‖
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    have hxq : x ^ q = ‖a₁ r‖ ^ q * ‖a₂ r‖ ^ q := Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
    have hyq : y ^ q = ‖b₁ r‖ ^ q * ‖b₂ r‖ ^ q := Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
    have e3 : ‖D r‖ ^ q ≤ 4 * (x ^ q + y ^ q) := by
      have hm : ‖D r‖ ≤ 2 * max x y := by
        have := hD r; linarith [le_max_left x y, le_max_right x y]
      have h1 : ‖D r‖ ^ q ≤ (2 * max x y) ^ q := Real.rpow_le_rpow hd0 hm (by linarith)
      rw [Real.mul_rpow (by norm_num) (le_max_of_le_left hx)] at h1
      have h2 : (2 : ℝ) ^ q ≤ 4 := by
        have : (2 : ℝ) ^ q ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2.le
        rw [Real.rpow_two] at this; linarith
      have h3 : (max x y) ^ q ≤ x ^ q + y ^ q := by
        rcases le_total x y with h | h
        · rw [max_eq_right h]; linarith [Real.rpow_nonneg hx q]
        · rw [max_eq_left h]; linarith [Real.rpow_nonneg hy q]
      have h4 : 0 ≤ (max x y) ^ q := Real.rpow_nonneg (le_max_of_le_left hx) q
      nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) q]
    rw [e1, ← hxq, ← hyq]
    exact mul_le_mul e2 e3 (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg ((norm_nonneg _).trans (hs r)) _)
  calc ∑ r : ZMod N, ‖D r‖ ^ 2
      ≤ ∑ r : ZMod N, s ^ (2 - q) *
          (4 * (‖a₁ r‖ ^ q * ‖a₂ r‖ ^ q + ‖b₁ r‖ ^ q * ‖b₂ r‖ ^ q)) :=
        Finset.sum_le_sum fun r _ => hpt r
    _ = s ^ (2 - q) * (4 * (∑ r : ZMod N, ‖a₁ r‖ ^ q * ‖a₂ r‖ ^ q +
          ∑ r : ZMod N, ‖b₁ r‖ ^ q * ‖b₂ r‖ ^ q)) := by
        rw [← Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ s ^ (2 - q) * (4 * (K + K)) := by
        have hs0 : 0 ≤ s ^ (2 - q) := by
          by_cases h : (0 : ℝ) ≤ s
          · exact Real.rpow_nonneg h _
          · exfalso; push Not at h
            have := hs 0; linarith [norm_nonneg (D 0)]
        exact mul_le_mul_of_nonneg_left (by linarith) hs0
    _ = 8 * K * s ^ (2 - q) := by ring

/-! ### Proposition 3.1 from Lemma 3.2 -/

/-- **Alsetri-Shao Proposition 3.1, U1446 form, CONDITIONAL ON `AS_Lemma32`.** The bad set is
`{f₁ * f₂ ≤ δ³/1000}`, as in the paper's Lemma 3.4. -/
theorem as_prop31_of_lemma32 (H : AS_Lemma32) : AS_Prop31 := by
  intro δ hδ hδ1 η hη p hp hp4 Mc hM
  set τ := δ ^ 3 / 250 with hτ
  have hτ0 : 0 < τ := by positivity
  have hMp : 0 < Mc ^ p := Real.rpow_pos_of_pos (by linarith) p
  set T := η * τ ^ 2 / (8 * Mc ^ p) with hT
  have hT0 : 0 < T := by positivity
  set y := 2 - p / 2 with hy
  have hy0 : 0 < y := by simp only [y]; linarith
  set s := T ^ y⁻¹ with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hT0 _
  have hsT : s ^ y = T := Real.rpow_inv_rpow hT0.le hy0.ne'
  obtain ⟨c, hc, N₀, hL⟩ := H δ hδ hδ1 (s / 4) (by positivity) p hp hp4 Mc hM
  refine ⟨min c 1, lt_min hc one_pos, N₀, fun N _ hNp hN₀ f₁ f₂ ν₁ ν₂ h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have h6' : ∀ r, ‖hatE N ν₁ r - (if r = 0 then 1 else 0)‖ ≤ c :=
    fun r => (h6 r).trans (min_le_left _ _)
  have h7' : ∀ r, ‖hatE N ν₂ r - (if r = 0 then 1 else 0)‖ ≤ c :=
    fun r => (h7 r).trans (min_le_left _ _)
  obtain ⟨g₁, g₂, hg₁, hg₂, ha₁, ha₂, he₁, he₂, hl₁, hl₂⟩ :=
    hL N hNp hN₀ f₁ f₂ ν₁ ν₂ h1 h2 h3 h4 h5 h6' h7'
  -- Lemma 3.3
  have hconv : ∀ n, δ ^ 3 / 1000 + τ ≤ convE N g₁ g₂ n := by
    intro n
    have := lemma33 g₁ g₂ δ hδ hg₁ hg₂ (by rw [ha₁, ha₂]; exact h3) n
    have e : δ ^ 3 / 1000 + τ = δ ^ 3 / 200 := by simp only [τ]; ring
    rw [e]; exact this
  have hP := exc_plancherel f₁ f₂ g₁ g₂ (δ ^ 3 / 1000) τ hτ0 hconv
  -- sizes of the transforms
  have havgν : ∀ ν : ZMod N → ℝ, (∀ r, ‖hatE N ν r - (if r = 0 then 1 else 0)‖ ≤ min c 1) →
      avg N ν ≤ 2 := by
    intro ν hν
    have := hν 0
    rw [if_pos rfl, hatE_zero] at this
    rw [show ((avg N ν : ℂ) - 1) = ((avg N ν - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at this
    have := (le_abs_self _).trans this
    linarith [min_le_right c 1]
  have hf₁ : avg N f₁ ≤ 2 := (avg_mono _ _ fun n => (h1 n).2).trans (havgν ν₁ h6)
  have hf₂ : avg N f₂ ≤ 2 := (avg_mono _ _ fun n => (h2 n).2).trans (havgν ν₂ h7)
  have nf₂ : ∀ r, ‖hatE N f₂ r‖ ≤ 2 := fun r => (norm_hatE_le f₂ (fun n => (h2 n).1) r).trans hf₂
  have ng₁ : ∀ r, ‖hatE N g₁ r‖ ≤ 2 := fun r =>
    (norm_hatE_le g₁ (fun n => (hg₁ n).1) r).trans (by rw [ha₁]; exact hf₁)
  have hDs : ∀ r, ‖hatE N g₁ r * hatE N g₂ r - hatE N f₁ r * hatE N f₂ r‖ ≤ s := by
    intro r
    have e : hatE N g₁ r * hatE N g₂ r - hatE N f₁ r * hatE N f₂ r =
        hatE N g₁ r * (hatE N g₂ r - hatE N f₂ r) + hatE N f₂ r * (hatE N g₁ r - hatE N f₁ r) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_sub_rev (hatE N g₂ r), norm_sub_rev (hatE N g₁ r)]
    have := mul_le_mul (ng₁ r) (he₂ r) (norm_nonneg _) (by norm_num)
    have := mul_le_mul (nf₂ r) (he₁ r) (norm_nonneg _) (by norm_num)
    linarith
  have hDab : ∀ r, ‖hatE N g₁ r * hatE N g₂ r - hatE N f₁ r * hatE N f₂ r‖ ≤
      ‖hatE N g₁ r‖ * ‖hatE N g₂ r‖ + ‖hatE N f₁ r‖ * ‖hatE N f₂ r‖ := by
    intro r
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  have hp0 : 0 < p := by linarith
  have hI := interp (fun r => hatE N g₁ r * hatE N g₂ r - hatE N f₁ r * hatE N f₂ r)
    (hatE N g₁) (hatE N g₂) (hatE N f₁) (hatE N f₂) p s (Mc ^ p) hp hp4 hDs hDab
    (sum_pow_le g₁ p Mc hp0 hl₁) (sum_pow_le g₂ p Mc hp0 hl₂)
    (sum_pow_le f₁ p Mc hp0 h4) (sum_pow_le f₂ p Mc hp0 h5)
  rw [← hy, hsT] at hI
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  have hfin : ((univ.filter (fun n => convE N f₁ f₂ n ≤ δ ^ 3 / 1000)).card : ℝ) / N * τ ^ 2 ≤
      η * τ ^ 2 := by
    refine hP.trans (hI.trans (le_of_eq ?_))
    simp only [T]; field_simp
  have := le_of_mul_le_mul_right hfin (by positivity)
  rwa [div_le_iff₀ hN0] at this

/-- The printed form, `≥ δ³/1000` off `η N` points, CONDITIONAL ON `AS_Lemma32`. -/
theorem as_prop31Printed_of_lemma32 (H : AS_Lemma32) : AS_Prop31Printed :=
  printed_of_U1446 (as_prop31_of_lemma32 H)

/-- **Alsetri-Shao 2024, Theorem 1.2, CONDITIONAL ON `AS_Lemma32`, `Green62`, `Green66`.**
Proposition 3.1 is no longer an input: only its Lemma 3.2, the Bohr set approximant, is. -/
theorem alsetriShao_1_2_of_lemma32 (H32 : AS_Lemma32) (H62 : Green62) (H66 : Green66) :
    AlsetriShao12 :=
  alsetriShao_1_2_of_printed (as_prop31Printed_of_lemma32 H32) H62 H66

/-! ### Vacuity -/

/-- The conclusion of `AS_Lemma32` can hold with real content: for `f = ν = 1`, `g = 1` meets
every requirement, for every `N`, `δ > 0`, `ε > 0`, `p > 2`, `M ≥ 1`. -/
theorem vacuity_Lemma32 (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) (p : ℝ) (hp : 2 < p)
    (Mc : ℝ) (hM : 1 ≤ Mc) :
    let g : ZMod N → ℝ := fun _ => 1
    (∀ n, 0 ≤ g n ∧ g n ≤ 1 + δ / 10) ∧ avg N g = avg N g ∧
      (∀ r, ‖hatE N g r - hatE N g r‖ ≤ ε) ∧ lpHat N p g ≤ Mc := by
  intro g
  refine ⟨fun n => ⟨by simp [g], by simp only [g]; linarith⟩, rfl, fun r => by simp [hε.le], ?_⟩
  have := vacuity_Prop31 (N := N) 0 (by norm_num) p hp Mc hM 1 one_pos
  exact this.2.2.1

end LeanLab.DensityGoldbach.U1467

