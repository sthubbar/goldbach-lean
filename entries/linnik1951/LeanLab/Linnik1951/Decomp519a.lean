module

public import LeanLab.Linnik1951.CircleSplit111
public import LeanLab.Linnik1951.GaussBound376
public import LeanLab.PNTPort.ZetaZeros.GammaBounds
public import LeanLab.Perelli1996.TotientRatio320
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
P0093 pages 155 through 160 and page 166 equation 9.1.
Upstream ports of the finite character and principal mass proofs.
The source proofs are in SPLIT_doubled_system_characters1622 and Principal442.
Those files import Lemma6Split111 through Decomp111, so this port breaks that cycle.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- P0093 page 159 before equation 5.1. The damped character prime series. -/
noncomputable def characterPrime519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes, χ (p : ℕ) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- P0093 page 166 equation 9.1. The doubled rational system. -/
def arcSystem519 (q : ℕ) (τ : ℝ) : Set ℝ :=
  {x | ∃ r : ℚ, r.den = q ∧ |x - r| ≤ 2 / ((q : ℝ) * τ)}

/-- P0093 page 159 before equation 5.1. Character weighting preserves the
uniform geometric majorant of the damped prime series. -/
theorem continuous_character_prime519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) : Continuous (characterPrime519 χ N) := by
  unfold characterPrime519
  apply continuous_tsum
    (u := fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N))
  · intro p
    fun_prop
  · exact (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
  · intro p α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)


open MeasureTheory

/-- P0093 page 159 trivial full period bound before equation 5.3.
Parseval for an absolutely summable negative natural Fourier series. -/
theorem series_square_integral519 (a : ℕ → ℂ) (ha : Summable a) :
    (∫ α in (0 : ℝ)..1, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) =
        ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hf : Continuous (fun α : ℝ => ∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) := by
    apply continuous_tsum (u := fun n => ‖a n‖)
    · intro n
      fun_prop
    · exact ha.norm
    · intro n α
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have hs : IntervalIntegrable (fun α : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) volume 0 1 :=
    (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => ∑' n : ℕ, a n *
          Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) i‖ ^ 2 := by
      simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm
    _ = _ := negative_modes_sum111_up111 _ _ (negative_series_coefficient_proved357_up111 a ha)

/-- P0093 page 159 before equation 5.3. Natural coefficient zero
extension of the character prime series, with absolute summability. -/
theorem character_coefficients_summable519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun n : ℕ => if n.Prime then
      χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (damping_summable111_up111 N hN)
  intro n
  by_cases hn : n.Prime
  · simp only [if_pos hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)
  · simp [hn, (Real.exp_pos _).le]

/-- P0093 page 159 before equation 5.3. The subtype prime series
equals its zero extension over the natural frequencies. -/
theorem character_series_nat519 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (α : ℝ) :
    characterPrime519 χ N α = ∑' n : ℕ,
      (if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0) *
        Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I) := by
  classical
  let f : ℕ → ℂ := fun n => if n.Prime then χ n *
    (Real.exp (-(n : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I) else 0
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hp : n.Prime
    · exact ⟨⟨n, hp⟩, rfl⟩
    · exact absurd (by simp [f, hp] : f n = 0) hn
  calc
    _ = ∑' p : Nat.Primes, f (p : ℕ) := by
      unfold characterPrime519
      apply tsum_congr
      intro p
      simp only [f, if_pos p.property]
    _ = ∑' n : ℕ, f n := Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = _ := by
      apply tsum_congr
      intro n
      by_cases hn : n.Prime <;> simp [f, hn]

/-- P0093 page 159 before equation 5.3. Every character has full
period square mass at most two N. The estimate discards primality and
uses the geometric damping sum. No prime number theorem is needed. -/
theorem character_full_mass519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖characterPrime519 χ N α‖ ^ 2) ≤ 2 * (N : ℝ) := by
  classical
  simp_rw [character_series_nat519]
  rw [series_square_integral519 _ (character_coefficients_summable519 χ N hN)]
  have he : ∀ n : ℕ,
      ‖if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0‖ ^ 2 ≤
        Real.exp (-2 * (n : ℝ) / N) := by
    intro n
    by_cases hn : n.Prime
    · simp only [if_pos hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc := pow_le_pow_left₀ (norm_nonneg (χ n)) (χ.norm_le_one n) 2
      have heq : Real.exp (-(n : ℝ) / N) ^ 2 = Real.exp (-2 * (n : ℝ) / N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc
        _ = ‖χ n‖ ^ 2 * Real.exp (-(n : ℝ) / N) ^ 2 := by ring
        _ ≤ 1 * Real.exp (-(n : ℝ) / N) ^ 2 :=
          mul_le_mul_of_nonneg_right (by simpa using hc) (by positivity)
        _ = _ := by rw [one_mul, heq]
    · simp [hn, (Real.exp_pos _).le]
  have hh := laplace_bound111_up111 (fun _ => (1 : ℝ)) 1 N hN (by norm_num)
    (fun _ => by norm_num) (by intro M; simp)
  have hg : Summable (fun n : ℕ => Real.exp (-2 * (n : ℝ) / N)) := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hr : ‖Real.exp (-2 / (N : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hNp)
    have hs := summable_geometric_of_norm_lt_one hr
    convert hs using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ ∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N) :=
      (Summable.of_nonneg_of_le (fun n => sq_nonneg _) he hg).tsum_le_tsum he hg
    _ ≤ _ := by simpa using hh

/-- P0093 page 159 before equation 5.3. Integer frequency character
sums have period one in the additive phase. -/
theorem character_periodic519 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Function.Periodic (characterPrime519 χ N) 1 := by
  intro α
  unfold characterPrime519
  apply tsum_congr
  intro p
  congr 1
  have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
        ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
  rw [hp, mul_one]

/-- P0093 page 159 before equation 5.3. The local square mass on a
symmetric interval of radius at most one half is at most the full
period square mass. -/
theorem character_local_mass519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    (∫ α in -r..r, ‖characterPrime519 χ N α‖ ^ 2) ≤ 2 * (N : ℝ) := by
  have hc := (continuous_character_prime519 χ N hN).norm.pow 2
  have hp : Function.Periodic (fun α => ‖characterPrime519 χ N α‖ ^ 2) 1 :=
    (character_periodic519 χ N).comp (fun z => ‖z‖ ^ 2)
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hrh
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖characterPrime519 χ N α‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
  have he := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num only at he
  exact hi.trans (he.trans_le (character_full_mass519 χ N hN))


open MeasureTheory Filter Finset

/-- The reduced residues below q number the totient of q, in the form the assembly
uses for the counting of the doubled intervals. -/
private theorem card_reduced1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

/-- LEAF. The covering step of the geometry. For q at least two and tau at least four,
every point of the arc system of denominator q that lies in the unit interval lies in
one of the doubled rational intervals of radius two over q tau about a reduced residue
below q. Only rational arithmetic and the positivity of q and tau are used; no
integration, no character and no bound on the prime system occurs. -/
theorem rational_cover519 (q : ℕ) [NeZero q] (τ : ℝ) (hq : 2 ≤ q) (hτ : 4 ≤ τ) :
    arcSystem519 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
  rintro x ⟨⟨r, hrden, hrδ⟩, hx0, hx1⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hRle : 2 / ((q : ℝ) * τ) ≤ 1 / (2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_le] at hrδ
  obtain ⟨hrlo, hrhi⟩ := hrδ
  have hrcq : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, hrden]
  have hcop : r.num.natAbs.Coprime q := by
    have h := r.reduced
    rwa [hrden] at h
  have hnum_nonneg : 0 ≤ r.num := by
    by_contra hneg
    push_neg at hneg
    have hle : (r.num : ℝ) ≤ -1 := by
      have : r.num ≤ -1 := by omega
      exact_mod_cast this
    have hrle : (r : ℝ) ≤ -1 / (q : ℝ) := by
      rw [hrcq, div_le_div_iff₀ hqpos hqpos]
      nlinarith
    have hxle : x ≤ -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) := by linarith
    have hneg' : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) < 0 := by
      have hsplit : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) = -(1 / (2 * (q : ℝ))) := by
        field_simp
        ring
      rw [hsplit]
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  have hnum_lt : r.num < (q : ℤ) := by
    by_contra hge
    push_neg at hge
    have hne : r.num ≠ (q : ℤ) := by
      intro he
      have hnat : r.num.natAbs = q := by
        rw [he]
        exact Int.natAbs_natCast q
      rw [hnat] at hcop
      have hq1 : q = 1 := Nat.coprime_self q |>.mp hcop
      omega
    have hge' : (q : ℤ) + 1 ≤ r.num := by omega
    have hcastZ : ((q : ℤ) : ℝ) + 1 ≤ (r.num : ℝ) := by exact_mod_cast hge'
    have hcast : (q : ℝ) + 1 ≤ (r.num : ℝ) := by
      have hqZ : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
      linarith
    have hrbig : 1 + 1 / (q : ℝ) ≤ (r : ℝ) := by
      rw [hrcq, le_div_iff₀ hqpos]
      have hmul : (1 + 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) + 1 := by
        field_simp
      rw [hmul]
      exact hcast
    have hxge : 1 + 1 / (2 * (q : ℝ)) ≤ x := by
      have hsplit : (1 : ℝ) + 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 + 1 / (2 * (q : ℝ)) := by
        field_simp
        ring
      linarith
    have : (1 : ℝ) < 1 + 1 / (2 * (q : ℝ)) := by
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  set a := r.num.toNat with hadef
  have hanum : (a : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
  have halt : a < q := by
    have h' : (a : ℤ) < (q : ℤ) := by rw [hanum]; exact hnum_lt
    exact_mod_cast h'
  have hcopa : Nat.Coprime a q := by
    have hna : r.num.natAbs = a := by
      rw [hadef]
      have h1 : ((r.num.natAbs : ℕ) : ℤ) = r.num := Int.natAbs_of_nonneg hnum_nonneg
      have h2 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
      exact_mod_cast h1.trans h2.symm
    rwa [hna] at hcop
  have hcasta : (a : ℝ) = (r.num : ℝ) := by
    have : (a : ℝ) = ((a : ℤ) : ℝ) := by push_cast; ring
    rw [this, hanum]
  have hmem : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨halt, hcopa⟩
  have hxI : x ∈ Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ))
      ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
    have e1 : (a : ℝ) / q - 2 / ((q : ℝ) * τ) = (r : ℝ) - 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    have e2 : (a : ℝ) / q + 2 / ((q : ℝ) * τ) = (r : ℝ) + 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    rw [Set.mem_Icc, e1, e2]
    constructor <;> linarith
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨a, hmem, hxI⟩


/-- LEAF. The integral step of the geometry. For a nonnegative continuous function and a
cover of the clipped arc system by the doubled intervals of the reduced residues, the
integral over the clipped system is at most the integral over the radius interval of the
sum of the shifted values at the reduced residues. This is subadditivity of the integral
over a finite union together with translation of the interval, so it uses no property of
the function beyond nonnegativity and continuity, and none of the characters. -/
theorem rational_cover_integral519 (q : ℕ) [NeZero q] (τ : ℝ) (hτ : 0 < τ) (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ x : ℝ, 0 ≤ f x)
    (hcover : arcSystem519 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ))) :
    (∫ α in arcSystem519 q τ ∩ Set.Icc 0 1, f α) ≤
      ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f ((a : ℝ) / q + z) := by
  classical
  let r : ℝ := 2 / ((q : ℝ) * τ)
  let S := (Finset.range q).filter (fun a => Nat.Coprime a q)
  let t : ℕ → Set ℝ := fun a => Set.Icc ((a : ℝ) / q - r) ((a : ℝ) / q + r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hi (a : ℕ) : IntegrableOn f (t a) := hf.integrableOn_Icc
  have hU : (∫ x in ⋃ a ∈ S, t a, f x) ≤ ∑ a ∈ S, ∫ x in t a, f x := by
    clear hcover
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      have hiU : IntegrableOn f (⋃ i ∈ S, t i) :=
        integrableOn_finset_iUnion.mpr (fun i _ => hi i)
      have hle := integral_mono_measure
        (Measure.restrict_union_le (μ := volume) (t a) (⋃ i ∈ S, t i))
        (ae_of_all _ hn) (integrable_add_measure.mpr ⟨hi a, hiU⟩)
      rw [integral_add_measure (hi a) hiU] at hle
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert ha]
      exact hle.trans (add_le_add le_rfl ih)
  have hiU : IntegrableOn f (⋃ a ∈ S, t a) :=
    integrableOn_finset_iUnion.mpr (fun a _ => hi a)
  calc
    _ ≤ ∫ x in ⋃ a ∈ S, t a, f x :=
      setIntegral_mono_set hiU (ae_of_all _ hn) (ae_of_all _ hcover)
    _ ≤ ∑ a ∈ S, ∫ x in t a, f x := hU
    _ = ∑ a ∈ S, ∫ z in -r..r, f ((a : ℝ) / q + z) := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [t]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : (a : ℝ) / q - r ≤ (a : ℝ) / q + r),
        intervalIntegral.integral_comp_add_left]
      simp only [sub_eq_add_neg]
    _ = _ := by
      change (∑ a ∈ S, ∫ z in -r..r, f ((a : ℝ) / q + z)) =
        ∫ z in -r..r, ∑ a ∈ S, f ((a : ℝ) / q + z)
      exact (intervalIntegral.integral_finsetSum
        (fun a _ => (hf.comp (continuous_const.add continuous_id)).intervalIntegrable (-r) r)).symm




open MeasureTheory Finset

/-- The phase of the residue `m` modulo `q`, as an `n`-th power. -/
private theorem exp_phase_nat (q m a : ℕ) (hq : 0 < q) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) ^ a := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- Complete residue sums vanish off the divisibility condition. -/
private theorem full_sum_nat (q m : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))) =
      if q ∣ m then (q : ℂ) else 0 := by
  classical
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpower : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) ^ q = 1 := by
    rw [← exp_phase_nat q m q hq]
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (q : ℂ) / (q : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / ((1 : ℕ) : ℂ) := by
      field_simp
      ring
    rw [harg, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by norm_num : (1 : ℕ) ≠ 0)]
    exact one_dvd m
  simp_rw [exp_phase_nat q m _ hq]
  by_cases hdiv : q ∣ m
  · rw [if_pos hdiv]
    have hone : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) = 1 := by
      rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne']
      exact hdiv
    rw [hone]
    simp
  · rw [if_neg hdiv]
    have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) - 1 ≠ 0 := by
      intro h0
      apply hdiv
      rw [sub_eq_zero] at h0
      have := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := m) (N := q) hq.ne').mp h0
      exact this
    have hmul := geom_sum_mul (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ))) q
    rw [hpower, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right hne

/-- The sum over the multiples of a divisor reduces to the quotient modulus. -/
private theorem multiples_sum_nat (q d m : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))) =
      if q / d ∣ m then ((q / d : ℕ) : ℂ) else 0 := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hq
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hd0
  have hqeq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
  have hfilter : (Finset.range q).filter (fun a => d ∣ a) =
      (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      rw [hqeq] at ha
      exact ⟨b, (Nat.mul_lt_mul_left hd0).mp ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by rw [hqeq]; exact (Nat.mul_lt_mul_left hd0).mpr hb, ⟨b, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · have heq (b : ℕ) :
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((d * b : ℕ) : ℂ) / (q : ℂ))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
              (b : ℂ) / ((q / d : ℕ) : ℂ)) := by
      congr 1
      conv_lhs => rw [hqeq]
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hqdC : ((q / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hqd.ne'
      push_cast
      field_simp
    simp_rw [heq]
    exact full_sum_nat (q / d) m hqd
  · intro b _ c _ heq
    exact Nat.eq_of_mul_eq_mul_left hd0 heq

/-- Möbius inversion gives the coprimality indicator at every positive modulus. -/
private theorem coprime_indicator_nat (q a : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime a q then 1 else 0 := by
  classical
  have hset : q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd a q ≠ 0 := Nat.gcd_ne_zero_right hq.ne'
    simp [hg, hq.ne', and_comm]
  rw [← Finset.sum_filter, hset]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd a q))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.coprime_iff_gcd_eq_one] using h

/-- The Ramanujan sum at argument one is the Möbius function of the modulus. -/
private theorem ramanujan_sum_one_nat (q : ℕ) (hq : 0 < q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ))) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  have heq (a : ℕ) :
      (if Nat.Coprime a q then
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) else 0) =
        (∑ d ∈ q.divisors,
            if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) := by
    rw [coprime_indicator_nat q a hq]
    split_ifs <;> simp
  rw [Finset.sum_filter]
  simp_rw [heq, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hstep : ∀ d ∈ q.divisors,
      (∑ a ∈ Finset.range q,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ))) =
        (ArithmeticFunction.moebius d : ℂ) *
          (if q / d ∣ 1 then ((q / d : ℕ) : ℂ) else 0) := by
    intro d hd
    have hdd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hone : ∀ a ∈ Finset.range q,
        (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) =
          (ArithmeticFunction.moebius d : ℂ) *
            (if d ∣ a then
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) else 0) := by
      intro a _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hone, ← Finset.mul_sum, ← Finset.sum_filter,
      multiples_sum_nat q d 1 hq hdd]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_eq_single q]
  · rw [Nat.div_self hq]
    simp
  · intro d hd hdne
    have hnot : ¬ q / d ∣ 1 := by
      intro h1
      have hqd1 : q / d = 1 := Nat.dvd_one.mp h1
      have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      rw [hqd1, mul_one] at h
      exact hdne h
    rw [if_neg hnot, mul_zero]
  · intro hnot
    exact absurd (Nat.mem_divisors_self q hq.ne') hnot



/-! ### The principal Gauss vector of the unit group

The unit sum of the additive character is the Ramanujan sum at argument one, so its
modulus is at most one, and the same holds for the conjugate sum that the Gauss vector of
the principal character is. -/

/-- The unit sum of the additive character has modulus at most one. -/
private theorem unit_sum_addChar_le_one (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c‖ ≤ 1 := by
  classical
  have hq : 0 < q := NeZero.pos q
  have hfil : (Finset.range q).filter (fun a => IsUnit ((a : ℕ) : ZMod q))
      = (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    refine Finset.filter_congr ?_
    intro a _
    exact ZMod.isUnit_iff_coprime a q
  have hconv :
      (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c)
        = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) := by
    rw [Finset.sum_filter, LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, ← Finset.sum_filter,
      hfil]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Int.cast_natCast a, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hconv, ramanujan_sum_one_nat q hq, Complex.norm_intCast]
  have h1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast h1

/-- The Gauss vector of the principal character at the unit shift one has modulus at most
one: it is the conjugate of the unit sum of the additive character. -/
private theorem unit_gauss_principal_le (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
        ZMod.stdAddChar (-(1 * c))‖ ≤ 1 := by
  have hconj :
      (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-(1 * c)))
        = (starRingEnd ℂ)
            (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [LeanLab.PNTPort.LargeSieve.conj_stdAddChar]
    simp
  rw [hconj, Complex.norm_conj]
  exact unit_sum_addChar_le_one q

/-! ### Counting the primes that divide the modulus

At most `log_2 q` primes divide `q`, since their product is at most `q`; the correction
terms of the prime series are supported on exactly those primes. -/

/-- The number of distinct prime divisors of a positive integer obeys `2 ^ ω ≤ q`. -/
private theorem two_pow_primeFactors_card_le (q : ℕ) (hq : 0 < q) :
    2 ^ q.primeFactors.card ≤ q := by
  have h2 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact h2.trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))

/-- The count of distinct prime divisors is at most twice the logarithm. -/
private theorem primeFactors_card_le_log (q : ℕ) (hq : 2 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have hq0 : 0 < q := by omega
  have hle : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le q hq0
  have hpos : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card := by positivity
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq : (1 : ℝ) < q)
  nlinarith

/-- The tail of the prime series at a unit residue is supported on the primes dividing `q`,
and each of its terms has modulus at most one. -/
private theorem corr_bound (N q : ℕ) [NeZero q] (hq : 2 ≤ q) (z : ℝ) (a : ZMod q) :
    ‖∑' p : Nat.Primes, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ ≤ 2 * Real.log q := by
  classical
  let emb : Function.Embedding {d // d ∈ q.primeFactors} Nat.Primes :=
    ⟨fun d => (⟨d.1, (Nat.mem_primeFactors.mp d.2).1⟩ : Nat.Primes),
      fun x y hxy => Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) hxy)⟩
  set sf : Finset Nat.Primes := q.primeFactors.attach.map emb with hsf
  have hmem : ∀ p : Nat.Primes, p ∉ sf → IsUnit (((p : ℕ)) : ZMod q) := by
    intro p hp
    by_contra hnu
    apply hp
    have hpnot : ¬ Nat.Coprime (p : ℕ) q :=
      fun h => hnu ((ZMod.isUnit_iff_coprime (p : ℕ) q).mpr h)
    have hdvd : (p : ℕ) ∣ q := by
      have hg : Nat.gcd (p : ℕ) q ∣ (p : ℕ) := Nat.gcd_dvd_left _ _
      have hg1 : Nat.gcd (p : ℕ) q ≠ 1 := fun h => hpnot (Nat.coprime_iff_gcd_eq_one.mpr h)
      rcases Nat.Prime.eq_one_or_self_of_dvd p.2 (Nat.gcd (p : ℕ) q) hg with h1 | h1
      · exact absurd h1 hg1
      · exact h1 ▸ Nat.gcd_dvd_right _ _
    have hmem' : (p : ℕ) ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨p.2, hdvd, by omega⟩
    rw [hsf, Finset.mem_map]
    exact ⟨⟨(p : ℕ), hmem'⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hcard : sf.card = q.primeFactors.card := by
    rw [hsf]
    simp
  have hterm : ∀ p : Nat.Primes,
      ‖(if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ ≤ 1 := by
    intro p
    by_cases hp : IsUnit (((p : ℕ)) : ZMod q)
    · rw [if_pos hp, norm_zero]; norm_num
    · rw [if_neg hp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.mpr ?_
      rw [neg_div]
      exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))
  have hzero : ∀ p : Nat.Primes, p ∉ sf →
      (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I)) = 0 := by
    intro p hp
    rw [if_pos (hmem p hp)]
  rw [tsum_eq_sum hzero]
  calc ‖∑ p ∈ sf, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖
      ≤ ∑ p ∈ sf, ‖(if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ sf, (1 : ℝ) := Finset.sum_le_sum (fun p _ => hterm p)
    _ = (sf.card : ℝ) := by simp
    _ = (q.primeFactors.card : ℝ) := by rw [hcard]
    _ ≤ 2 * Real.log q := primeFactors_card_le_log q hq




open MeasureTheory Filter Finset

/-! ### Finite character expansion

The character table expands the additive character on the units.
The unit Gauss vector is written out as an explicit finite sum at every use site.
-/

open MeasureTheory Filter Finset Complex
open LeanLab.PNTPort.LargeSieve
noncomputable section
variable {q : ℕ} [NeZero q]

/-- Character-table expansion of the additive character on the units. -/
private theorem sum_Gunit_mul_char (a b : ZMod q) (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ b
      = (q.totient : ℂ) * ZMod.stdAddChar (-(a * b)) := by
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ b = ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
        ZMod.stdAddChar (-(a * c)) * χ (c⁻¹ * b) := by
    intro χ
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, hcu⟩ := hc
    rw [conj_char_of_isUnit χ hcu, mul_assoc, ← map_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq,
      if_pos (ZMod.inv_mul_of_unit b hb)]
    ring
  · intro c hc hcb
    rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq, if_neg ?_]
    · simp
    · intro h
      apply hcb
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hcu⟩ := hc
      have h2 : c * (c⁻¹ * b) = c * 1 := by rw [h]
      rw [← mul_assoc, ZMod.mul_inv_of_unit c hcu, one_mul, mul_one] at h2
      exact h2.symm
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩) hnot

/-- `G` is multiplicative in the additive shift: on units it is `χ a` times `G χ 1`. -/
private theorem Gunit_eq_mul (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) = χ a * (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) := by
  classical
  have hainv : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  have hbinv : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have hau : IsUnit a⁻¹ := by
    obtain ⟨u, rfl⟩ := ha
    exact ⟨u⁻¹, by simp⟩
  have hinv2 : a⁻¹⁻¹ = a := by
    calc a⁻¹⁻¹ = a⁻¹⁻¹ * 1 := (mul_one _).symm
      _ = a⁻¹⁻¹ * (a⁻¹ * a) := by rw [hainv]
      _ = a⁻¹⁻¹ * a⁻¹ * a := by rw [mul_assoc]
      _ = 1 * a := by rw [ZMod.inv_mul_of_unit a⁻¹ hau]
      _ = a := one_mul a
  have hconj : (starRingEnd ℂ) (χ a⁻¹) = χ a := by
    rw [conj_char_of_isUnit χ hau, hinv2]
  have hstep : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))
      = ∑ d ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
          ZMod.stdAddChar (-d) * (starRingEnd ℂ) (χ (a⁻¹ * d)) := by
    skip
    refine Finset.sum_nbij' (fun c => a * c) (fun c => a⁻¹ * c) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, ha.mul hc.2⟩
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, hau.mul hc.2⟩
    · intro c hc
      show a⁻¹ * (a * c) = c
      rw [← mul_assoc, hainv, one_mul]
    · intro c hc
      show a * (a⁻¹ * c) = c
      rw [← mul_assoc, hbinv, one_mul]
    · intro c hc
      show ZMod.stdAddChar (-(a * c)) * (starRingEnd ℂ) (χ c)
        = ZMod.stdAddChar (-(a * c)) * (starRingEnd ℂ) (χ (a⁻¹ * (a * c)))
      rw [← mul_assoc, hainv, one_mul]
  rw [hstep]
  skip
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.mem_filter] at hd
  simp only [map_mul, hconj, one_mul]
  ring



/-- A nontrivial Dirichlet character has vanishing sum over the units. -/
private theorem sum_unit_char_of_ne_one {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a = 0 := by
  classical
  have hex : ∃ u : (ZMod q)ˣ, ψ ((u : ZMod q)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (MulChar.ext_iff.mpr (fun u => by rw [h u]; simp))
  obtain ⟨u, hu⟩ := hex
  have huo : IsUnit ((u : ZMod q)) := u.isUnit
  have hji : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, (u⁻¹).isUnit.mul ha.2⟩
  have hbi : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ ((u : ZMod q) * a) := by
    refine Finset.sum_nbij' (fun a => ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) (fun a => (u : ZMod q) * a)
      hji ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, huo.mul ha.2⟩
    · intro a ha
      show (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) = a
      have h1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
    · intro a ha
      show ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * a) = a
      have h1 : (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * (u : ZMod q) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
    · intro a ha
      show ψ a = ψ ((u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a))
      have h1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
  have hfac : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ ((u : ZMod q) * a)
      = ψ (u : ZMod q) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_mul]
  have hS : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a
      = ψ (u : ZMod q) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a :=
    hbi.trans hfac
  have hz : (1 - ψ (u : ZMod q)) *
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  refine (mul_eq_zero.1 hz).resolve_left ?_
  intro hc
  exact hu (sub_eq_zero.1 hc).symm

/-- `χ·conj χ'` summed over the units: the totient at `χ = χ'`, zero otherwise. -/
private theorem sum_unit_char_mul_inv (χ χ' : DirichletCharacter ℂ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), χ a * χ' a⁻¹
      = if χ = χ' then (q.totient : ℂ) else 0 := by
  classical
  set ψ : DirichletCharacter ℂ q := χ * χ'⁻¹ with hpsi
  have hpt : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      χ a * χ' a⁻¹ = ψ a := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hau⟩ := ha
    rw [hpsi, MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    congr 1
    have hmul : χ' a⁻¹ * χ' a = 1 := by
      rw [← map_mul, ZMod.inv_mul_of_unit a hau, map_one]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [Finset.sum_congr rfl hpt]
  by_cases hχ : χ = χ'
  · subst hχ
    rw [if_pos rfl]
    have hψ1 : ψ = 1 := by rw [hpsi]; simp
    rw [hψ1]
    have hconst : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        (1 : DirichletCharacter ℂ q) a = (1 : ℂ) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨v, rfl⟩ := ha.2
      simp
    rw [Finset.sum_congr rfl hconst, Finset.sum_filter]
    have hC : ∑ x : ZMod q, (if IsUnit x then (1 : ℂ) else 0) = (q.totient : ℂ) := by
      have hR := sum_isUnit_eq_totient (q := q)
      have h2 : ((∑ x : ZMod q, (if IsUnit x then (1 : ℝ) else 0) : ℝ) : ℂ) = (q.totient : ℂ) := by
        rw [hR]
        push_cast
        ring
      rw [← h2]
      push_cast
      ring_nf
      congr 1
      funext x
      by_cases hx : IsUnit x <;> simp [hx]
    exact hC
  · rw [if_neg hχ]
    refine sum_unit_char_of_ne_one ?_
    intro h
    apply hχ
    rw [hpsi] at h
    have h2 := congrArg (fun t => t * χ') h
    simp only [one_mul] at h2
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h2

/-- The Gauss vectors of two characters are orthogonal over the units. -/
private theorem sum_Gunit_orth (χ χ' : DirichletCharacter ℂ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))
      = if χ = χ' then (q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))) else 0 := by
  classical
  have hpt : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))
        = (χ a * χ' a⁻¹) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hau⟩ := ha
    rw [Gunit_eq_mul χ hau, Gunit_eq_mul χ' hau, map_mul, conj_char_of_isUnit χ' hau]
    ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, sum_unit_char_mul_inv]
  by_cases h : χ = χ'
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The principal Gauss vector: the additive character of the units is the conjugate of
the Ramanujan sum, so its norm is `|μ(q)|`. -/
private theorem Gunit_one_principal_le (hq : 0 < q) : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ≤ 1 := by
  classical
  have hU : ∀ c : ZMod q, (1 : DirichletCharacter ℂ q) c = if IsUnit c then (1 : ℂ) else 0 := by
    intro c
    by_cases hc : IsUnit c
    · rw [if_pos hc]
      obtain ⟨v, rfl⟩ := hc
      simp
    · rw [if_neg hc, MulChar.map_nonunit _ hc]
  have hG : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))
      = ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-c) := by
    skip
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [hU c, if_pos hc.2]
    simp
  have hconj : ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-c)
      = (starRingEnd ℂ) (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
          ZMod.stdAddChar c) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    exact (LeanLab.PNTPort.LargeSieve.conj_stdAddChar c).symm
  have hram : ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c
      = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q 1 := by
    rw [Finset.sum_filter, sum_zmod_eq_sum_range]
    unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_range] at hc
    by_cases hcop : Nat.Coprime c q
    · rw [if_pos ((ZMod.isUnit_iff_coprime c q).2 hcop), if_pos hcop]
      have hone : ((c : ZMod q)) = ((1 : ℤ) : ZMod q) * (c : ZMod q) := by simp
      rw [hone, stdAddChar_mul_natCast (q := q) 1 c]
      congr 1
      push_cast
      ring
    · rw [if_neg (fun h => hcop ((ZMod.isUnit_iff_coprime c q).1 h)), if_neg hcop]
  have hmu : LeanLab.Perelli1996.Ramanujan103.ramanujanSum q 1
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) :=
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 hq (Nat.coprime_one_right q)
  rw [hG, hconj, norm_conj, hram, hmu, Complex.norm_intCast]
  have h1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast h1

/-- `G χ 1` is the Gauss sum of `χ⁻¹`, so its square norm is at most the modulus. -/
private theorem Gunit_one_norm_sq_le (χ : DirichletCharacter ℂ q) : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 ≤ (q : ℝ) := by
  have hcongr : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))
      = ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a := by
    skip
    rw [Finset.sum_filter (s := Finset.univ)]
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases ha : IsUnit a
    · rw [if_pos ha, MulChar.inv_apply_eq_inv']
      have h1 : (χ a)⁻¹ = (starRingEnd ℂ) (χ a) := by
        have hnorm : ‖χ a‖ = 1 := by
          rw [show a = ((ha.unit : (ZMod q)ˣ) : ZMod q) from ha.unit_spec.symm]
          exact DirichletCharacter.unit_norm_eq_one χ ha.unit
        rw [Complex.inv_eq_conj hnorm]
      rw [h1]
      have h2 : ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a = ZMod.stdAddChar (-(1 * a)) := by
        rw [AddChar.mulShift_apply]
        simp
      rw [h2]
      ring
    · rw [if_neg ha, MulChar.map_nonunit _ ha, zero_mul]
  rw [hcongr]
  have hgs : (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a)
      = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q)) := rfl
  rw [hgs, gaussSum_mulShift_eq, norm_mul, mul_pow]
  rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
  have hχ1 : ‖χ (((-1 : (ZMod q)ˣ)) : ZMod q)‖ ^ 2 = 1 := by
    rw [normSq_char (χ := χ) (((-1 : (ZMod q)ˣ)) : ZMod q), if_pos ((-1 : (ZMod q)ˣ).isUnit)]
  rw [hχ1, one_mul]
  have hb := LeanLab.Linnik1951.gauss_norm_le376 (χ⁻¹)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsq : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 ≤ (Real.sqrt (q : ℝ)) ^ 2 := by
    nlinarith [hb, norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar)]
  rwa [Real.sq_sqrt hq0] at hsq

/-- Per-prime character expansion: on a prime whose residue is a unit, the additive character
of the shifted fraction is `1/φ` times the Gauss-weighted character sum. -/
private theorem char_expansion_pointwise (q : ℕ) [NeZero q] (a : ZMod q) (p : Nat.Primes)
    (hp : IsUnit ((p : ℕ) : ZMod q)) :
    ZMod.stdAddChar (-(a * ((p : ℕ) : ZMod q)))
      = (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q) := by
  rw [sum_Gunit_mul_char a ((p : ℕ) : ZMod q) hp]
  have hφ : ((q.totient : ℂ)) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  field_simp

/-- Splitting the exponential of the shifted fraction into the residue phase and the shift. -/
private theorem exp_split_phase (q : ℕ) [NeZero q] (z : ℝ) (a : ZMod q) (p : Nat.Primes) :
    ZMod.stdAddChar (-(a * ((p : ℕ) : ZMod q))) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
      = Complex.exp
          ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  have h1 : ((a.val : ℕ) : ZMod q) = a := ZMod.natCast_zmod_val a
  have h2 : ((((p : ℕ) : ℤ)) : ZMod q) = ((p : ℕ) : ZMod q) := Int.cast_natCast _
  have hpos : a * ((p : ℕ) : ZMod q) = ((↑((a.val : ℤ) * ((p : ℕ) : ℤ))) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, h1]
  rw [(LeanLab.PNTPort.LargeSieve.conj_stdAddChar (a * ((p : ℕ) : ZMod q))).symm, hpos,
    ZMod.stdAddChar_coe, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast,
    map_ofNat]
  ring


/-- Pointwise expansion of the prime series at a shifted unit fraction. -/
private theorem prime_fourier_expansion (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) (a : ZMod q) :
    primeFourier111_up111 N ((a.val : ℝ) / q + z) =
      (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z +
        ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0
          else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
  classical
  have hφ : ((q.totient : ℂ)) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  set F : Nat.Primes → DirichletCharacter ℂ q → ℂ := fun p χ =>
    (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (χ ((p : ℕ) : ZMod q) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) with hF
  have hsumF : ∀ χ : DirichletCharacter ℂ q, Summable (fun p : Nat.Primes => F p χ) := by
    intro χ
    have hb : Summable (fun p : Nat.Primes => ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * Real.exp (-((p : ℕ) : ℝ) / N)) :=
      ((damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective).mul_left _
    refine Summable.of_norm_bounded hb (fun p => ?_)
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul]
    have he : ‖Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    have hce : ‖(Real.exp (-((p : ℕ) : ℝ) / N) : ℂ)‖ = Real.exp (-((p : ℕ) : ℝ) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hχ : ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := by
      have h2 : ‖χ ((p : ℕ) : ZMod q)‖ ^ 2 ≤ 1 := by
        rw [normSq_char]
        split_ifs <;> norm_num
      nlinarith [norm_nonneg (χ ((p : ℕ) : ZMod q))]
    rw [he, hce, mul_one]
    have hc0 : 0 ≤ Real.exp (-((p : ℕ) : ℝ) / N) := (Real.exp_pos _).le
    have hstep : ‖χ ((p : ℕ) : ZMod q)‖ * Real.exp (-((p : ℕ) : ℝ) / N)
        ≤ 1 * Real.exp (-((p : ℕ) : ℝ) / N) :=
      mul_le_mul_of_nonneg_right hχ hc0
    calc ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * (‖χ ((p : ℕ) : ZMod q)‖ * Real.exp (-((p : ℕ) : ℝ) / N))
        ≤ ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * (1 * Real.exp (-((p : ℕ) : ℝ) / N)) :=
          mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      _ = ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * Real.exp (-((p : ℕ) : ℝ) / N) := by ring
  have hp_id : ∀ p : Nat.Primes,
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
      = (1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q, F p χ)
          + (if IsUnit ((p : ℕ) : ZMod q) then 0
              else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
                Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
    intro p
    by_cases hp : IsUnit ((p : ℕ) : ZMod q)
    · rw [if_pos hp, add_zero, ← exp_split_phase (q := q) z a p]
      rw [char_expansion_pointwise (q := q) a p hp]
      have hL : (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          ((1 / (q.totient : ℂ)) *
            (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))
          = ∑ χ : DirichletCharacter ℂ q, (1 / (q.totient : ℂ)) * F p χ := by
        rw [show (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            ((1 / (q.totient : ℂ)) *
              (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))
            = (1 / (q.totient : ℂ)) *
              ((∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
              ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) by ring]
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        simp only [hF]
        ring
      rw [hL, Finset.mul_sum]
    · have hS : (∑ χ : DirichletCharacter ℂ q, F p χ) = 0 := by
        refine Finset.sum_eq_zero (fun χ _ => ?_)
        simp only [hF]
        rw [MulChar.map_nonunit _ hp]
        ring
      rw [if_neg hp, hS, mul_zero, zero_add]
  have hsA : Summable (fun p : Nat.Primes => (1 / (q.totient : ℂ)) *
      (∑ χ : DirichletCharacter ℂ q, F p χ)) := by
    have h : Summable (fun p : Nat.Primes => ∑ χ : DirichletCharacter ℂ q, F p χ) :=
      summable_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (f := fun (χ : DirichletCharacter ℂ q) (p : Nat.Primes) => F p χ)
        (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) => hsumF χ)
    exact h.mul_left _
  have hsB : Summable (fun p : Nat.Primes => (if IsUnit ((p : ℕ) : ZMod q) then 0
      else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    have hb := (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
    refine Summable.of_norm_bounded hb (fun p => ?_)
    by_cases hp : IsUnit ((p : ℕ) : ZMod q)
    · rw [if_pos hp, norm_zero]
      exact (Real.exp_pos _).le
    · rw [if_neg hp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_rfl
  rw [primeFourier111_up111, tsum_congr hp_id, Summable.tsum_add hsA hsB]
  congr 1
  rw [tsum_mul_left]
  congr 1
  have hswap : (∑' (p : Nat.Primes), ∑ χ : DirichletCharacter ℂ q, F p χ)
      = ∑ χ : DirichletCharacter ℂ q, ∑' (p : Nat.Primes), F p χ :=
    Summable.tsum_finsetSum (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) =>
      hsumF χ)
  rw [hswap]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [characterPrime519, ← tsum_mul_left]

/-- The squared character combination summed over the reduced residues. The Gauss vectors of
distinct characters are orthogonal, so only the diagonal survives: the sum is the totient times
the character squares weighted by the squared Gauss norms at `1`. -/
private theorem sum_normSq_chi_combo (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z‖ ^ 2
      = (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
  classical
  have hreal : ∀ w : ℂ, ‖w‖ ^ 2 = (w * (starRingEnd ℂ) w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hresumA : ∀ f : ZMod q → ℂ,
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), (f a).re)
        = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), f a).re := by
    intro f
    have h := map_sum Complex.reCLM f
      ((Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a))
    simpa only [Complex.reCLM_apply] using h.symm
  have hresumC : ∀ f : DirichletCharacter ℂ q → ℂ,
      (∑ χ : DirichletCharacter ℂ q, (f χ).re) = (∑ χ : DirichletCharacter ℂ q, f χ).re := by
    intro f
    have h := map_sum Complex.reCLM f (Finset.univ : Finset (DirichletCharacter ℂ q))
    simpa only [Complex.reCLM_apply] using h.symm
  have hre : ∀ χ : DirichletCharacter ℂ q,
      ((characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
          ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))))).re
        = (q.totient : ℝ) * (‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
    intro χ
    rw [Complex.mul_conj, Complex.mul_conj]
    rw [show ((q.totient : ℂ)) = (((q.totient : ℝ)) : ℂ) by simp]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  have hcomplex :
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
        = ∑ χ : DirichletCharacter ℂ q,
            (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
              ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))))) := by
    have hexp : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
        = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
              ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
                (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime519 χ' N z) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum, Finset.sum_mul_sum]
    rw [hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Finset.sum_comm]
    have hfac : ∀ a : ZMod q,
        ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
        = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)))) := by
      intro a
      rw [map_mul]
      ring
    rw [Finset.sum_eq_single χ]
    · have hstep : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
          = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
              ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
                ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => hfac a)
      rw [hstep, sum_Gunit_orth χ χ, if_pos rfl]
    · intro χ' _ hne
      have hfac' : ∀ a : ZMod q,
          ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime519 χ' N z)
          = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ' N z)) *
              ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
        intro a
        rw [map_mul]
        ring
      have hstep : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime519 χ' N z)
          = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ' N z)) *
              ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
                ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => hfac' a)
      rw [hstep, sum_Gunit_orth χ χ', if_neg (fun h => hne h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ χ) h
  calc ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z‖ ^ 2
      = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          ((∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)).re := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact hreal _
    _ = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)).re := by
        exact hresumA _
    _ = (∑ χ : DirichletCharacter ℂ q,
          (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
            ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))))).re := by
        rw [hcomplex]
    _ = ∑ χ : DirichletCharacter ℂ q,
          (q.totient : ℝ) * (‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
        rw [← hresumC]
        exact Finset.sum_congr rfl (fun χ _ => hre χ)
    _ = (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
        rw [Finset.mul_sum]

end





open MeasureTheory Filter Finset

private theorem card_reduced_aux1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

set_option maxHeartbeats 2000000 in
private theorem pointwise_assembly (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      (8 / (q.totient : ℝ)) *
        (‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime519 χ N z‖ ^ 2) +
        8 * (q.totient : ℝ) * Real.log q ^ 2 := by
  classical
  have hq0 : 0 < q := by omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have := Nat.totient_pos.mpr hq0
    exact_mod_cast this
  set S := Finset.univ.filter (fun c : ZMod q => IsUnit c) with hS
  set FF := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hFF
  set X : ℝ := ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
      (q : ℝ) * ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 with hX
  -- membership characterisations
  have hSmem : ∀ c : ZMod q, c ∈ S ↔ IsUnit c := by
    intro c
    rw [hS]
    simp
  have hRmem : ∀ a : ℕ, a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ↔
      a < q ∧ Nat.Coprime a q := by
    intro a
    simp
  have hX0 : 0 ≤ X := by
    rw [hX]
    have h1 : (0 : ℝ) ≤ ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
      positivity
    have h2 : (0 : ℝ) ≤ ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 :=
      Finset.sum_nonneg (fun χ _ => by positivity)
    have h3 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  -- step 1: the reduced residues of `range q` are the units of `ZMod q`
  have hbij : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2)
      = ∑ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2 := by
    refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod q)) (fun c : ZMod q => c.val)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact (hSmem _).mpr ((ZMod.isUnit_iff_coprime a q).mpr ((hRmem a).mp ha).2)
    · intro c hc
      have hunit : IsUnit (((c.val : ℕ)) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]
        exact (hSmem c).mp hc
      exact (hRmem c.val).mpr ⟨ZMod.val_lt c, (ZMod.isUnit_iff_coprime c.val q).mp hunit⟩
    · intro a ha
      exact ZMod.val_natCast_of_lt ((hRmem a).mp ha).1
    · intro c _
      exact ZMod.natCast_zmod_val c
    · intro a ha
      rw [ZMod.val_natCast_of_lt ((hRmem a).mp ha).1]
  have hcardS : S.card = q.totient := by
    have hb : S.card = ((Finset.range q).filter (fun a => Nat.Coprime a q)).card := by
      refine Finset.card_nbij' (fun c : ZMod q => c.val) (fun a : ℕ => (a : ZMod q))
        ?_ ?_ ?_ ?_
      · intro c hc
        have hunit : IsUnit (((c.val : ℕ)) : ZMod q) := by
          rw [ZMod.natCast_zmod_val]
          exact (hSmem c).mp hc
        exact (hRmem c.val).mpr ⟨ZMod.val_lt c, (ZMod.isUnit_iff_coprime c.val q).mp hunit⟩
      · intro a ha
        exact (hSmem _).mpr ((ZMod.isUnit_iff_coprime a q).mpr ((hRmem a).mp ha).2)
      · intro c _
        exact ZMod.natCast_zmod_val c
      · intro a ha
        exact ZMod.val_natCast_of_lt ((hRmem a).mp ha).1
    rw [hb, card_reduced_aux1622]
  -- the principal Gauss vector has norm at most one
  have hG1 : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2 ≤ 1 := by
    have hG : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))
        = ∑ c ∈ S, ZMod.stdAddChar (-(1 * c)) := by
      rw [hS]
      skip
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have h1 : (1 : DirichletCharacter ℂ q) c = 1 := by
        obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hc).2
        simp
      rw [h1, map_one, mul_one]
    rw [hG]
    nlinarith [unit_gauss_principal_le q,
      norm_nonneg (∑ c ∈ S, ZMod.stdAddChar (-(1 * c)))]
  -- the character sum is bounded by the bracket of the statement
  have hGbound : (∑ χ : DirichletCharacter ℂ q,
        ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) ≤ X := by
    have hsplit_chi : (∑ χ : DirichletCharacter ℂ q,
          ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        = ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 *
            ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2
          + ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
      have h := Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (p := fun χ : DirichletCharacter ℂ q => χ = 1)
        (f := fun χ => ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
      rw [← h]
      have hsingle : (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ = 1) = {1} := by
        ext χ
        simp
      have hrest : (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => ¬ (χ = 1)) = FF := by
        rw [hFF]
      rw [hsingle, hrest, Finset.sum_singleton]
    rw [hsplit_chi, hX]
    have hb1 : ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 *
          ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2
        ≤ ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hG1 (by positivity)
    have hb2 : (∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        ≤ ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * (q : ℝ) :=
      Finset.sum_le_sum (fun χ _ =>
        mul_le_mul_of_nonneg_left (Gunit_one_norm_sq_le χ) (by positivity))
    have hb2' : (∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * (q : ℝ))
        = (q : ℝ) * ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun χ _ => by ring)
    linarith [hb1, hb2, hb2'.le]
  -- the squared phi-normalised character sums
  have hfac : ∀ c : ZMod q,
      ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2
        = (1 / (q.totient : ℝ)) ^ 2 *
            ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z‖ ^ 2 := by
    intro c
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_one, one_div, mul_pow]
  have hA : (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
      ≤ (1 / (q.totient : ℝ)) * X := by
    have horth := sum_normSq_chi_combo N q hN z
    have hsum : (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
        = (1 / (q.totient : ℝ)) ^ 2 *
            ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
              ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
      rw [Finset.sum_congr rfl (fun c _ => hfac c), ← Finset.mul_sum]
      rw [hS, horth]
    rw [hsum]
    have heq : (1 / (q.totient : ℝ)) ^ 2 *
          ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
            ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        = (1 / (q.totient : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
            ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hGbound (by positivity)
  -- the bound at each residue
  have hpoint : ∀ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2 ≤
      2 * ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
    intro c _
    have hexp := prime_fourier_expansion N q hN z c
    set A : ℂ := (1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) with hAdef
    set Tt : ℂ := ∑' p : Nat.Primes, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((c.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I)) with hTdef
    have hT : ‖Tt‖ ≤ 2 * Real.log q := by
      rw [hTdef]
      exact corr_bound N q hq z c
    have hlog : 0 ≤ Real.log q :=
      Real.log_nonneg (by linarith [show (1 : ℝ) ≤ 2 by norm_num,
        show (2 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq])
    have h3 : ‖A + Tt‖ ^ 2 ≤ (‖A‖ + 2 * Real.log q) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      linarith [norm_add_le A Tt]
    have h4 : (‖A‖ + 2 * Real.log q) ^ 2 ≤
        2 * ‖A‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
      nlinarith [sq_nonneg (‖A‖ - 2 * Real.log q)]
    have hgoal : ‖A + Tt‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
      linarith [h3, h4]
    rw [hexp, hAdef, hTdef]
    exact hgoal
  -- the correction terms
  have hcorr : (∑ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2) ≤
      2 * (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
        + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
    have h1 := Finset.sum_le_sum hpoint
    have h2 : (∑ c ∈ S, (2 * ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
            (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2 + 2 * (2 * Real.log q) ^ 2))
        = 2 * (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
            (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
          + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith [h1, h2.le, h2.ge]
  -- the final comparison
  have hmain : (∑ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2) ≤
      2 * ((1 / (q.totient : ℝ)) * X) + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
    linarith [hcorr, hA]
  have hlast : 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 =
      8 * (q.totient : ℝ) * Real.log q ^ 2 := by
    rw [hcardS]
    ring
  have hfirst : 2 * ((1 / (q.totient : ℝ)) * X) ≤ (8 / (q.totient : ℝ)) * X := by
    have h1 : 2 * ((1 / (q.totient : ℝ)) * X) = (2 / (q.totient : ℝ)) * X := by ring
    have h2 : (2 / (q.totient : ℝ)) * X ≤ (8 / (q.totient : ℝ)) * X := by
      apply mul_le_mul_of_nonneg_right _ hX0
      apply div_le_div_of_nonneg_right _ hφpos.le
      norm_num
    linarith
  rw [hbij]
  linarith [hmain, hlast.le, hlast.ge, hfirst]


/-- LEAF. The finite unit character step, pointwise in z. At any z the sum of the squares
of the prime system shifted to the reduced residues below q is at most a constant over the
totient of q times the principal square plus q times the sum of the nonprincipal squares,
plus a constant times the totient of q times the square of the logarithm of q. The
orthogonality of the unit group gives the coefficient one over the totient, the Gauss
squares are bounded by q, and the primes dividing q are absorbed in the logarithmic term.
No tau, no integration and no growth hypothesis occurs. -/
theorem rational_pointwise_characters519 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime519 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  refine ⟨8, by norm_num, ?_⟩
  intro N q _ hN hq z
  exact pointwise_assembly N q hN hq z

/-- The doubled system mass, from the two geometry steps and the pointwise finite
character bound. The target statement is unchanged. -/
theorem doubled_system_characters1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem519 q τ ∩ Set.Icc 0 1, ‖primeFourier111_up111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime519 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters519
  refine ⟨2 * B, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  set r := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by positivity
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime519 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ => ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime519 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) :
      Continuous (fun z : ℝ => ‖characterPrime519 χ N z‖ ^ 2) :=
    (continuous_character_prime519 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hJ0 : ∀ z, 0 ≤ J z := by intro z; dsimp [J]; positivity
  have hS : Continuous (fun z => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111_up111 N hN).norm.pow 2).comp (continuous_const.add continuous_id))
  have hgeo := rational_cover_integral519 q τ hτp (fun α => ‖primeFourier111_up111 N α‖ ^ 2)
    ((continuous_prime_fourier111_up111 N hN).norm.pow 2) (fun α => sq_nonneg _)
    (rational_cover519 q τ hq hτ)
  have hmono : (∫ z in -r..r, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z + B * (q.totient : ℝ) * Real.log q ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hS.intervalIntegrable _ _)
      (((hJ.const_mul _).add continuous_const).intervalIntegrable _ _)
      (fun z _ => hb N q hN hq z)
  have hsplit : (∫ z in -r..r, J z) =
      (∫ z in -r..r, ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (q : ℝ) * ∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime519 χ N z‖ ^ 2 := by
    dsimp [J]
    rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      (((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun χ _ => (hc χ).intervalIntegrable _ _)]
  have hpos : 0 ≤ B / (q.totient : ℝ) * (∫ z in -r..r, J z) :=
    mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (intervalIntegral.integral_nonneg_of_forall (by linarith) hJ0)
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : B / (q.totient : ℝ) * (∫ z in -r..r, J z) +
      (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) ≤
      (2 * B) / (q.totient : ℝ) * (∫ z in -r..r, J z) +
        (2 * B) * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    calc
      _ ≤ 2 * (B / (q.totient : ℝ) * (∫ z in -r..r, J z)) +
          (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) := by linarith
      _ = _ := by ring
  have hh := hgeo.trans (hmono.trans hfinal)
  rw [hsplit] at hh
  exact hh


/-- P0093 page 156 Lemma 2. The vertical Mellin line. -/
noncomputable def mellinLine519 (N : ℕ) (t : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log N : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- P0093 page 156 display after equation 4.1 with ds equal to i dt. -/
noncomputable def mellinU519 (N : ℕ) (M : ℝ → ℂ) (α : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
      (-(mellinLine519 N t)) * Complex.Gamma (mellinLine519 N t) * M t

/-- P0093 page 156 Lemma 2. The line bound has a nonzero instance:
the constant coefficient one works with the displayed fixed positive constant. -/
theorem line_coefficient_one519 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (fun _ : ℝ => (1 : ℂ)) ∧ ∀ t : ℝ,
      ‖(1 : ℂ)‖ ≤ (1 / Real.log 2 ^ 3) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  refine ⟨continuous_const, fun t => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg : (2 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hl : Real.log 2 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_le_log (by norm_num) harg
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [norm_one, one_div_mul_eq_div]
  apply (le_div_iff₀ (pow_pos hl0 3)).mpr
  simpa only [one_mul] using pow_le_pow_left₀ hl0.le hl 3


/-! Upstream central kernel ports from Repair493KernelData, Gamma442,
SPLIT_central_kernel_mass442 and Repair493ContourData. -/

open MeasureTheory

/-- P0093 page 156 equation 4.1. The Mellin kernel before its coefficient M.
The factor one over two pi remains outside this kernel. -/
noncomputable def mellinKernel519 (N : ℕ) (α t : ℝ) : ℂ :=
  (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
    (-(mellinLine519 N t)) * Complex.Gamma (mellinLine519 N t)

/-- LEAF. P0093 page 156 equation 4.1. A line bound on M bounds the
Mellin integral by B0 over two pi times its absolute weighted kernel
mass. This is the norm integral inequality alone. -/
theorem mellin_kernel_domination519 (N : ℕ) (α B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : (Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3))
    (hI : Integrable (fun t : ℝ => ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :
    ‖mellinU519 N M α‖ ≤ (1 / (2 * Real.pi)) * B0 *
      (∫ t : ℝ, ‖mellinKernel519 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hb (t : ℝ) : ‖mellinKernel519 N α t * M t‖ ≤
      B0 * (‖mellinKernel519 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left (hM.2 t) (norm_nonneg (mellinKernel519 N α t))
    nlinarith
  have hnorm := norm_integral_le_of_norm_le (hI.const_mul B0) (Filter.Eventually.of_forall hb)
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, mellinKernel519 N α t * M t)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ, B0 * (‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- LEAF. P0093 page 158 before equation 4.8. Square root N is at
most N over square root R when one is at most R at most N. -/
theorem sqrt_scale519 (N R : ℝ) (hN : 0 < N) (hR : 0 < R) (hRN : R ≤ N) :
    Real.sqrt N ≤ N / Real.sqrt R := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    Real.sqrt N * Real.sqrt R ≤ Real.sqrt N * Real.sqrt N := by
      gcongr
    _ = N := Real.mul_self_sqrt hN.le


/-- P0093 page 157 Gamma asymptotic used before equation 4.4.
The existing PNTPort strip bound gives exponential decay in the
absolute imaginary part by conjugation. -/
theorem gamma_absolute_decay519 (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * ‖s + 1‖ *
      Real.exp (-(Real.pi * |s.im| / 2)) := by
  by_cases hs : 0 ≤ s.im
  · simpa only [abs_of_nonneg hs] using
      LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL hlo hhi
  · have hh := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL
      (s := star s) (by simpa using hlo) (by simpa using hhi)
    have hn : ‖star s + 1‖ = ‖s + 1‖ := by
      simpa using norm_star (s + 1)
    have hgamma : ‖Complex.Gamma (star s)‖ = ‖Complex.Gamma s‖ := by
      simp only [Complex.star_def, Complex.Gamma_conj, Complex.norm_conj]
    have him : (star s).im = -s.im := by simp
    rw [hgamma, hn, him] at hh
    simpa only [abs_of_neg (lt_of_not_ge hs)] using hh

/-- P0093 page 157 shifted Mellin line. For N at least three the
Gamma factor is bounded by square root of two pi times three plus
absolute t times exp of negative pi absolute t over two. -/
theorem gamma_mellin_line519 (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hNr)
  have hlog : 0 < Real.log N := by linarith
  have hinv : 1 / Real.log N ≤ 1 := (div_le_one hlog).mpr hl
  have hre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hg := gamma_absolute_decay519 (mellinLine519 N t)
    (by rw [hre]; exact le_add_of_nonneg_right (by positivity))
    (by rw [hre]; linarith)
  have hn : ‖mellinLine519 N t + 1‖ ≤ 3 + |t| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t + 1)
    have hr : (mellinLine519 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by simp [hre]
    have hi : (mellinLine519 N t + 1).im = t := by simp [him]
    rw [hr, hi, abs_of_pos (by positivity : 0 < 1 / 2 + 1 / Real.log N + 1)] at hh
    linarith
  rw [him] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn (by positivity)) (Real.exp_pos _).le)


open MeasureTheory

/-- The gap in the principal argument: `pi / 2 - 1 / (16 * pi)` is strictly positive. -/
private lemma pi_gap519 : (0 : ℝ) < Real.pi / 2 - 1 / (16 * Real.pi) := by
  have h16 : (0 : ℝ) < 16 * Real.pi := by positivity
  have h : (1 : ℝ) < Real.pi / 2 * (16 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have h2 : 1 / (16 * Real.pi) < Real.pi / 2 := (div_lt_iff₀ h16).mpr h
  linarith

/-- The principal argument of the base `1 / N + 2 pi alpha i` of the Mellin power factor
stays `1 / (16 * pi)` away from `pi / 2` when `|alpha| ≤ 4 / N`: the modulus of the base is at
most `(1 / N) sqrt (1 + (8 pi) ^ 2)`, so its cosine is at least `1 / sqrt (1 + (8 pi) ^ 2)`,
which is at least `1 / (16 pi)`, which is at least `sin (1 / (16 pi))`. -/
private lemma arg_base_bound519 (N : ℕ) (α : ℝ) (hN : 2 ≤ N) (hα : |α| ≤ 4 / (N : ℝ)) :
    |Complex.arg ((((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I))| ≤
      Real.pi / 2 - 1 / (16 * Real.pi) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzim : z.im = 2 * Real.pi * α := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have him : |z.im| ≤ 8 * Real.pi / (N : ℝ) := by
    rw [hzim, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    calc 2 * Real.pi * |α| ≤ 2 * Real.pi * (4 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 8 * Real.pi / (N : ℝ) := by field_simp; ring
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm_le : ‖z‖ ≤ (1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2) := by
    have hz2 : ‖z‖ ^ 2 ≤ (1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2) := by
      have hsqim : z.im ^ 2 ≤ (8 * Real.pi / (N : ℝ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg z.im) him 2
        rwa [sq_abs] at h
      have expand : (1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2) =
          (1 / (N : ℝ)) ^ 2 + (8 * Real.pi / (N : ℝ)) ^ 2 := by
        field_simp; ring
      rw [hsq, hzre, expand]
      linarith
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ Real.sqrt ((1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2)) := Real.sqrt_le_sqrt hz2
      _ = (1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity) hnorm_ge
  have hcos : Real.sin (1 / (16 * Real.pi)) ≤ z.re / ‖z‖ := by
    have h16 : (1 : ℝ) / (16 * Real.pi) ≤ 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have h1 : 1 + 64 * Real.pi ^ 2 ≤ (16 * Real.pi) ^ 2 := by
        nlinarith [Real.pi_gt_three, Real.pi_pos]
      calc Real.sqrt (1 + 64 * Real.pi ^ 2) ≤ Real.sqrt ((16 * Real.pi) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = 16 * Real.pi := Real.sqrt_sq (by positivity)
    have hsin : Real.sin (1 / (16 * Real.pi)) ≤ 1 / (16 * Real.pi) :=
      (Real.sin_lt (by positivity)).le
    have hstep : 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) ≤ z.re / ‖z‖ := by
      rw [hzre]
      have heq : 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) =
          (1 / (N : ℝ)) / ((1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2)) := by
        field_simp
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) hzpos hnorm_le
    exact hsin.trans (h16.trans hstep)
  have hθmem : Real.pi / 2 - 1 / (16 * Real.pi) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨(pi_gap519).le, by
      have h1 : (0 : ℝ) < 1 / (16 * Real.pi) := by positivity
      linarith [Real.pi_pos]⟩
  have hargmem : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hcosarg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  rw [← Real.cos_pi_div_two_sub (1 / (16 * Real.pi)), ← hcosarg] at hcos
  exact (Real.strictAntiOn_cos.le_iff_ge hθmem hargmem).mp hcos

/-- LEAF. First step of the parent proof, the modulus of the power factor.
For N at least two and alpha at most four over N the base of the power has
real part one over N and imaginary part at most eight pi over N, so the
imaginary part of its logarithm is at most pi over two minus one over
sixteen pi; its modulus is at least one over N, and N to the power a half
plus one over log N is at most e times the square root of N. No Gamma
factor, no logarithm of N, no integral here. -/
theorem mellin_base_bound519 (N : ℕ) (α t : ℝ) (hN : 2 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have harg : |Complex.arg z| ≤ Real.pi / 2 - 1 / (16 * Real.pi) :=
    arg_base_bound519 N α hN hα
  have hsre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hσ : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hmul : (1 / 2 + 1 / Real.log N) * Real.log N = Real.log N / 2 + 1 := by
    field_simp
    try ring
  have hlogz : -(1 / 2 + 1 / Real.log N) * Real.log ‖z‖ ≤ Real.log N / 2 + 1 := by
    have h1 : Real.log (1 / (N : ℝ)) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by positivity) hnorm_ge
    have h2 : Real.log (1 / (N : ℝ)) = -Real.log N := by
      rw [Real.log_div one_ne_zero hNr.ne']; simp
    have hσ' : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := hσ
    nlinarith [h1, h2, hmul]
  have htarg : t * Complex.arg z ≤ |t| * (Real.pi / 2 - 1 / (16 * Real.pi)) := by
    have hlow : -(Real.pi / 2 - 1 / (16 * Real.pi)) ≤ Complex.arg z := (abs_le.mp harg).1
    have hhigh : Complex.arg z ≤ Real.pi / 2 - 1 / (16 * Real.pi) := (abs_le.mp harg).2
    rcases lt_or_ge t 0 with ht | ht
    · rw [abs_of_neg ht]
      have h : t * (Complex.arg z + (Real.pi / 2 - 1 / (16 * Real.pi))) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ht.le (by linarith)
      nlinarith [h]
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hhigh ht
  have hkey : (Complex.log z * (-(mellinLine519 N t))).re ≤
      Real.log N / 2 + 1 + |t| * (Real.pi / 2 - 1 / (16 * Real.pi)) := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im,
      hsre, hsim]
    nlinarith [hlogz, htarg]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  refine (Real.exp_le_exp.mpr hkey).trans (le_of_eq ?_)
  have hexp_logN : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hNr.le, Real.exp_log (Real.sqrt_pos.mpr hNr)]
  rw [Real.exp_add, Real.exp_add, hexp_logN]
  try ring

/-- LEAF. Second step of the parent proof, the split of the logarithm.
For N at least two the logarithm of N times the sum of absolute t and two
is the sum of two nonnegative logarithms, so its cube is at most eight
cubes of log N plus eight cubes of the logarithm of the sum. -/
theorem log_cube_split519 (N : ℕ) (t : ℝ) (hN : 2 ≤ N) :
    Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hu : (0 : ℝ) < |t| + 2 := by positivity
  have hu1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hsplit : Real.log ((N : ℝ) * (|t| + 2)) =
      Real.log N + Real.log (|t| + 2) := Real.log_mul hNr.ne' hu.ne'
  have hA : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hB : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg hu1
  rw [hsplit]
  set a := Real.log N with ha
  set b := Real.log (|t| + 2) with hb
  have hA' : 0 ≤ a := by rw [ha]; exact hA
  have hB' : 0 ≤ b := by rw [hb]; exact hB
  have h1 : 0 ≤ 2 * a ^ 3 + b ^ 3 - 3 * a ^ 2 * b := by
    rw [show 2 * a ^ 3 + b ^ 3 - 3 * a ^ 2 * b = (a - b) ^ 2 * (2 * a + b) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 := by
    rw [show a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 = (a - b) ^ 2 * (a + 2 * b) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ a ^ 3 := pow_nonneg hA' 3
  have h4 : 0 ≤ b ^ 3 := pow_nonneg hB' 3
  nlinarith [h1, h2, h3, h4]

/-- `exp (-b * |t|)` is integrable on the line for `b > 0`. -/
private lemma integrable_exp_neg_abs519 (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) (0 : ℝ)).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    show Real.exp (-b * t) = Real.exp (-b * |t|)
    rw [abs_of_pos ht]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := b) hb (0 : ℝ)).congr_fun ?_ measurableSet_Iic
    intro t ht
    show Real.exp (b * t) = Real.exp (-b * |t|)
    rw [abs_of_nonpos ht]
    ring_nf
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0 ∪ Set.Iic 0) :=
    integrableOn_union.mpr ⟨h1, h2⟩
  rw [Set.Ioi_union_Iic] at h3
  exact integrableOn_univ.mp h3

/-- A fifth power is dominated by a constant times `exp (e * |t|)` for every `e > 0`: this is
Taylor's inequality `v ^ 5 ≤ 5 ! exp v` at `v = e * (|t| + 4)`, together with
`e * (|t| + 4) = e * |t| + 4 * e`. -/
private lemma shift_pow_five_le_exp519 (e : ℝ) (he : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, (|t| + 4) ^ 5 ≤ K * Real.exp (e * |t|) := by
  refine ⟨120 * (1 / e) ^ 5 * Real.exp (4 * e), by positivity, fun t => ?_⟩
  have hv : (0 : ℝ) ≤ e * (|t| + 4) := by positivity
  have h1 : (e * (|t| + 4)) ^ 5 ≤ 120 * Real.exp (e * (|t| + 4)) := by
    have h := Real.pow_div_factorial_le_exp (x := e * (|t| + 4)) hv 5
    norm_num at h
    calc (e * (|t| + 4)) ^ 5 = (e * (|t| + 4)) ^ 5 / 120 * 120 := by ring
      _ ≤ Real.exp (e * (|t| + 4)) * 120 := by
          exact mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 120 * Real.exp (e * (|t| + 4)) := by ring
  have h2 : (|t| + 4) ^ 5 = (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hExp : Real.exp (e * (|t| + 4)) = Real.exp (4 * e) * Real.exp (e * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  calc (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5
      ≤ (1 / e) ^ 5 * (120 * Real.exp (e * (|t| + 4))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 120 * (1 / e) ^ 5 * Real.exp (4 * e) * Real.exp (e * |t|) := by
        rw [hExp]; ring

/-- The majorant `(|t| + 4) ^ 5 exp (-|t| / (16 pi))` of the twisted Gamma mass is
integrable on the line. -/
private lemma integrable_majorant519 :
    Integrable (fun t : ℝ => (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
  obtain ⟨K, hK, hKle⟩ := shift_pow_five_le_exp519 (1 / (16 * Real.pi) / 2) (by positivity)
  have hbase : Integrable (fun t : ℝ => Real.exp (-(1 / (16 * Real.pi) / 2) * |t|)) :=
    integrable_exp_neg_abs519 _ (by positivity)
  refine Integrable.mono' (hbase.const_mul K) (by fun_prop) ?_
  filter_upwards with t
  have h1 : (|t| + 4) ^ 5 ≤ K * Real.exp (1 / (16 * Real.pi) / 2 * |t|) := hKle t
  have h2 : (0 : ℝ) ≤ (|t| + 4) ^ 5 := by positivity
  have h3 : (0 : ℝ) ≤ Real.exp (-(1 / (16 * Real.pi)) * |t|) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h3)]
  calc (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)
      ≤ (K * Real.exp (1 / (16 * Real.pi) / 2 * |t|)) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = K * Real.exp (-(1 / (16 * Real.pi) / 2) * |t|) := by
        rw [mul_assoc, ← Real.exp_add,
          show 1 / (16 * Real.pi) / 2 * |t| + -(1 / (16 * Real.pi)) * |t| =
            -(1 / (16 * Real.pi) / 2) * |t| by ring]

/-- `mellinLine519 N` is continuous in `t`. -/
private lemma continuous_mellinLine519 (N : ℕ) :
    Continuous fun t : ℝ => mellinLine519 N t := by
  have h : (fun t : ℝ => mellinLine519 N t) =
      fun t : ℝ => (((1 / 2 + 1 / Real.log N : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    funext t
    simp [mellinLine519]
  rw [h]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- The Gamma factor on the shifted Mellin line decays exponentially in `|t|` for every
`N ≥ 2`. For a line with real part at most `3 / 2` this is `gamma_absolute_decay519`; otherwise
the real part is at most `5 / 2` and `Gamma s = (s - 1) Gamma (s - 1)` moves it into the strip. -/
private theorem gamma_line_uniform519 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hinv : 1 / Real.log N ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 hlogle
  have hlog2' : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hinvle : 1 / Real.log N ≤ 3 / 2 := by
    have h2 : 1 / Real.log 2 ≤ 3 / 2 := by
      rw [div_le_iff₀ hlog2]
      linarith
    linarith
  have hquad : ∀ x : ℝ, |x| + 4 ≤ (|x| + 4) ^ 2 := by
    intro x
    have h : (1 : ℝ) ≤ |x| + 4 := by linarith [abs_nonneg x]
    nlinarith [h, abs_nonneg x]
  have hsp : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by positivity
  by_cases hcase : (mellinLine519 N t).re ≤ 3 / 2
  · have hlo : (1 : ℝ) / 2 ≤ (mellinLine519 N t).re := by
      rw [hre]
      have hp : (0 : ℝ) < 1 / Real.log N := by positivity
      linarith
    have h := gamma_absolute_decay519 (mellinLine519 N t) hlo hcase
    rw [him] at h
    have hnorm : ‖mellinLine519 N t + 1‖ ≤ |t| + 4 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t + 1)
      have hr : (mellinLine519 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by
        rw [Complex.add_re, Complex.one_re, hre]
      have hi : (mellinLine519 N t + 1).im = t := by
        rw [Complex.add_im, Complex.one_im, him]; ring
      rw [hr, hi] at hb
      have hre2 : |1 / 2 + 1 / Real.log N + 1| ≤ 4 := by
        rw [abs_of_pos (by positivity)]
        linarith
      linarith [abs_nonneg t]
    have he : (0 : ℝ) ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
    have hnorm2 : ‖mellinLine519 N t + 1‖ ≤ (|t| + 4) ^ 2 := le_trans hnorm (hquad t)
    have hstep : Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t + 1‖ *
        Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hnorm2 hsp
    exact h.trans hstep
  · push_neg at hcase
    have hσle : (mellinLine519 N t).re ≤ 5 / 2 := by rw [hre]; linarith
    have hre1 : (mellinLine519 N t - 1).re = 1 / 2 + 1 / Real.log N - 1 := by
      rw [Complex.sub_re, Complex.one_re, hre]
    have him1 : (mellinLine519 N t - 1).im = t := by
      rw [Complex.sub_im, Complex.one_im, him]; ring
    have hne : mellinLine519 N t - 1 ≠ 0 := by
      intro h
      have h' := congr_arg Complex.re h
      rw [hre1] at h'
      simp only [Complex.zero_re] at h'
      linarith [hlog]
    have hGam : Complex.Gamma (mellinLine519 N t) =
        (mellinLine519 N t - 1) * Complex.Gamma (mellinLine519 N t - 1) := by
      have h := Complex.Gamma_add_one (mellinLine519 N t - 1) hne
      rwa [sub_add_cancel] at h
    have hpos1 : (1 : ℝ) / 2 ≤ (mellinLine519 N t - 1).re := by rw [hre1]; linarith
    have hle1 : (mellinLine519 N t - 1).re ≤ 3 / 2 := by rw [hre1]; linarith
    have hbound := gamma_absolute_decay519 (mellinLine519 N t - 1) hpos1 hle1
    rw [him1] at hbound
    have hb2 : ‖Complex.Gamma (mellinLine519 N t - 1)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ * Real.exp (-(Real.pi * |t| / 2)) := by
      have h := hbound
      rwa [sub_add_cancel] at h
    have hn1 : ‖mellinLine519 N t - 1‖ ≤ |t| + 2 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t - 1)
      rw [hre1, him1] at hb
      have hre2 : |1 / 2 + 1 / Real.log N - 1| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith [abs_nonneg t]
    have hn0 : ‖mellinLine519 N t‖ ≤ |t| + 3 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t)
      rw [hre, him] at hb
      have hre2 : |1 / 2 + 1 / Real.log N| ≤ 3 := by
        rw [abs_of_pos (by positivity)]
        linarith
      linarith [abs_nonneg t]
    rw [hGam, norm_mul]
    have he : (0 : ℝ) ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
    have hstep1 : ‖mellinLine519 N t - 1‖ *
        ‖Complex.Gamma (mellinLine519 N t - 1)‖ ≤
        (|t| + 2) * (Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ *
          Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hn1 hb2 (norm_nonneg _) (by positivity)
    refine hstep1.trans ?_
    have hinner : Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ *
        Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.sqrt (2 * Real.pi) * (|t| + 3) * Real.exp (-(Real.pi * |t| / 2)) := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hn0 hsp
    have hstep2 : (|t| + 2) * (Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ *
        Real.exp (-(Real.pi * |t| / 2))) ≤
        (|t| + 2) * (Real.sqrt (2 * Real.pi) * (|t| + 3) *
          Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    refine hstep2.trans ?_
    have hq2 : (|t| + 2) * (|t| + 3) ≤ (|t| + 4) ^ 2 := by nlinarith [abs_nonneg t]
    calc (|t| + 2) * (Real.sqrt (2 * Real.pi) * (|t| + 3) * Real.exp (-(Real.pi * |t| / 2)))
        = ((|t| + 2) * (|t| + 3)) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ ((|t| + 4) ^ 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) :=
          mul_le_mul_of_nonneg_right hq2 (by positivity)
      _ = Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by ring

/-- Pointwise domination of the twisted Gamma mass with a logarithm factor. -/
private lemma gamma_twist_pointwise519 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
  have hg := gamma_line_uniform519 N hN t
  have hfac : (0 : ℝ) ≤ Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) :=
    (Real.exp_pos _).le
  have h1 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) :=
    mul_le_mul_of_nonneg_left hg hfac
  have hee : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      Real.exp (-(Real.pi * |t| / 2)) = Real.exp (-(1 / (16 * Real.pi)) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmid : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) =
      Real.sqrt (2 * Real.pi) * ((|t| + 4) ^ 2 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          Real.exp (-(Real.pi * |t| / 2)))) := by ring
  have h2 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) *
        ((|t| + 4) ^ 2 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    rw [hmid, hee] at h1
    exact h1
  have hlogp0 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
    have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
    positivity
  have hlogp1 : (1 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by linarith
  have hlog3 : (1 : ℝ) + Real.log (|t| + 2) ^ 3 ≤ 2 * (|t| + 4) ^ 3 := by
    have h1' : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h2' : Real.log (|t| + 2) ≤ |t| + 2 := Real.log_le_self (by linarith)
    have h3' : Real.log (|t| + 2) ≤ |t| + 4 := by linarith
    have h4' : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1'
    have h5' : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := pow_le_pow_left₀ h4' h3' 3
    have h6' : (1 : ℝ) ≤ (|t| + 4) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg t])
    linarith
  have h4 : (0 : ℝ) ≤ (|t| + 4) ^ 2 := by positivity
  have h5 : (0 : ℝ) ≤ Real.exp (-(1 / (16 * Real.pi)) * |t|) := (Real.exp_pos _).le
  have h3 : (|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3) ≤ 2 * (|t| + 4) ^ 5 := by
    have := mul_le_mul_of_nonneg_left hlog3 h4
    calc (|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3) ≤
        (|t| + 4) ^ 2 * (2 * (|t| + 4) ^ 3) := this
      _ = 2 * (|t| + 4) ^ 5 := by ring
  calc Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)
      = (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) * (1 + Real.log (|t| + 2) ^ 3) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi) *
          ((|t| + 4) ^ 2 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) *
          (1 + Real.log (|t| + 2) ^ 3) := by
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
    _ = Real.sqrt (2 * Real.pi) *
          ((|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3)) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * (2 * (|t| + 4) ^ 5) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) := by
        apply mul_le_mul_of_nonneg_right _ h5
        apply mul_le_mul_of_nonneg_left h3
        exact Real.sqrt_nonneg _
    _ = Real.sqrt (2 * Real.pi) * 2 *
          ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by ring

/-- `Gamma` composed with the shifted Mellin line is continuous: the line has positive real
part, so it stays away from the poles of `Gamma`. -/
private lemma continuous_gamma_mellin519 (N : ℕ) (hN : 2 ≤ N) :
    Continuous fun t : ℝ => Complex.Gamma (mellinLine519 N t) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hre : ∀ t : ℝ, (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hpos : (0 : ℝ) < 1 / 2 + 1 / Real.log N := by positivity
  have hne : ∀ t : ℝ, ∀ m : ℕ, mellinLine519 N t ≠ -(m : ℂ) := by
    intro t m h
    have h1 := congr_arg Complex.re h
    rw [hre t] at h1
    have h3 : (-(m : ℂ)).re = -(m : ℝ) := by push_cast; simp
    rw [h3] at h1
    have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hpos]
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact ((Complex.differentiableAt_Gamma _ (hne t)).continuousAt).comp
    (continuous_mellinLine519 N).continuousAt

/-- LEAF. Third step of the parent proof, the twisted Gamma mass. The
Gamma factor on the line, weighted by the exponential gap of the power
factor and by the cube of the logarithm of the sum of absolute t and two,
is integrable for every N at least two, and both of its integrals are at
most one constant independent of N and of alpha. This is the analytic core
of the parent proof and the only place where the decay of Gamma is used. -/
theorem gamma_twist_mass519 :
    ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) ∧
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖) ≤ G ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ *
          Real.log (|t| + 2) ^ 3)) ≤ G := by
  have hM : Integrable (fun t : ℝ =>
      (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := integrable_majorant519
  have h2pi : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * 2 := by positivity
  have hMc : Integrable (fun t : ℝ => Real.sqrt (2 * Real.pi) * 2 *
      ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) := hM.const_mul _
  have hInt_nonneg : (0 : ℝ) ≤ ∫ t : ℝ, Real.sqrt (2 * Real.pi) * 2 *
      ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) :=
    integral_nonneg (fun t => by positivity)
  refine ⟨(∫ t : ℝ, Real.sqrt (2 * Real.pi) * 2 *
    ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) + 1, by linarith, ?_⟩
  intro N hN
  have hpt := gamma_twist_pointwise519 N hN
  have hApt : ∀ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    intro t
    have h := hpt t
    have hlogp1 : (1 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      have h3 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by positivity
      linarith
    have h3 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ ≤
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
      calc Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖
          = Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖ * 1 := by ring
        _ ≤ Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
            apply mul_le_mul_of_nonneg_left hlogp1
            positivity
    exact h3.trans h
  have hBpt : ∀ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3) ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    intro t
    have h := hpt t
    have hlogp : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      positivity
    have h3 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3) ≤
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
      rw [show Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)
          = Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)) by ring]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith
    exact h3.trans h
  have hGamma_cont : Continuous fun t : ℝ => Complex.Gamma (mellinLine519 N t) :=
    continuous_gamma_mellin519 N hN
  have hAcont : Continuous fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ :=
    (Real.continuous_exp.comp (continuous_abs.mul continuous_const)).mul hGamma_cont.norm
  have hBcont : Continuous fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3) :=
    (Real.continuous_exp.comp (continuous_abs.mul continuous_const)).mul
      (hGamma_cont.norm.mul (((continuous_abs.add continuous_const).log
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < |t| + 2))).pow 3))
  have hAi : Integrable (fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖) := by
    refine Integrable.mono' hMc hAcont.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact hApt t
  have hBi : Integrable (fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    refine Integrable.mono' hMc hBcont.aestronglyMeasurable ?_
    filter_upwards with t
    have hlogp : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) hlogp))]
    exact hBpt t
  exact ⟨hAi, hBi, (integral_mono hAi hMc hApt).trans (by linarith),
    (integral_mono hBi hMc hBpt).trans (by linarith)⟩


/-- LEAF. Fourth step of the parent proof, the integrability half of the
parent conclusion. The modulus of the kernel times the cube of the
logarithm of N times the sum of absolute t and two is integrable, for N at
least thirty two and alpha at most four over N. This is the first
conjunct of the parent statement on its own, without any estimate of the
integral. -/
theorem kernel_mass_integrable519 (N : ℕ) (α : ℝ) (hN : 32 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    Integrable (fun t : ℝ => ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNr2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass519
  obtain ⟨hAi, hBi, -, -⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hcont : Continuous fun t : ℝ => ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    have hg : Continuous fun t : ℝ => Complex.Gamma (mellinLine519 N t) :=
      continuous_gamma_mellin519 N hN2
    have he : Continuous fun t : ℝ =>
        Complex.exp (Complex.log z * (-(mellinLine519 N t))) :=
      Complex.continuous_exp.comp (continuous_const.mul (continuous_mellinLine519 N).neg)
    have h1 : Continuous fun t : ℝ => mellinKernel519 N α t := by
      have hfun : (fun t : ℝ => mellinKernel519 N α t) =
          fun t => Complex.exp (Complex.log z * (-(mellinLine519 N t))) *
            Complex.Gamma (mellinLine519 N t) := by
        funext t
        unfold mellinKernel519
        rw [Complex.cpow_def_of_ne_zero hz]
      rw [hfun]
      exact he.mul hg
    have harg : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
      continuous_const.mul (continuous_abs.add continuous_const)
    have h2 : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
      harg.log (fun t => ne_of_gt (by positivity))
    exact h1.norm.mul (h2.pow 3)
  refine Integrable.mono' hdomint hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hbase := mellin_base_bound519 N α t hN2 hα
  have hlog := log_cube_split519 N t hN2
  have hk : ‖mellinKernel519 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ := by
    unfold mellinKernel519
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
  have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t, hNr2])
    positivity
  have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ := by positivity
  have h1 := mul_le_mul hk hlog hpos hf
  have hEq : (Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) *
      (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    ring
  rw [hEq] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos)]
  exact h1
/-- LEAF. Fifth step of the parent proof, the bookkeeping of the constant.
For N at least thirty two and a positive constant G, eight e times the
square root of N times the cube of log N times G plus G is at most the
cube of log N times the square root of N times the constant eight e G
times one plus the inverse cube of log two. The last factor absorbs the
additive G because the cube of log N is at least the cube of log two. -/
theorem mass_constant519 (N : ℕ) (G : ℝ) (hN : 32 ≤ N) (hG : 0 < G) :
    8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hlr : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlogN : 0 < Real.log N := lt_of_lt_of_le hlog2 hlr
  have hl3 : Real.log 2 ^ 3 ≤ Real.log N ^ 3 := pow_le_pow_left₀ hlog2.le hlr 3
  have h19 : (1 : ℝ) ≤ Real.log N ^ 3 / Real.log 2 ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    simpa using hl3
  have hGeq : G ≤ G * (Real.log N ^ 3 / Real.log 2 ^ 3) := by
    simpa using mul_le_mul_of_nonneg_left h19 hG.le
  have hc : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N := by positivity
  have hkey : Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3)) := by
    apply mul_le_mul_of_nonneg_left _ hc
    nlinarith [hGeq]
  have hEq : Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3)) =
      Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
    field_simp
    try ring
  calc 8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G)
      = 8 * (Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G)) := by ring
    _ ≤ 8 * (Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3))) := by
        linarith [hkey]
    _ = 8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
        rw [hEq]; try ring

/-- The parent statement central_kernel_mass442, reassembled from the five
leaves above. No use of the parent theorem, no placeholder proof. -/
theorem central_kernel_mass519 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
        Integrable (fun t : ℝ => ‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧
        (∫ t : ℝ, ‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
            C * Real.sqrt N * Real.log N ^ 3 := by
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass519
  refine ⟨8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3), ?_, 31, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < 1 + 1 / Real.log 2 ^ 3 := by positivity
    positivity
  intro N hN α hα
  have hN32 : 32 ≤ N := hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  obtain ⟨hAi, hBi, hA, hB⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hpoint : ∀ t : ℝ, ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    intro t
    have hbase := mellin_base_bound519 N α t hN2 hα
    have hlog := log_cube_split519 N t hN2
    have hk : ‖mellinKernel519 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ := by
      unfold mellinKernel519
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg t, hNr])
      positivity
    have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ := by positivity
    have h1 := mul_le_mul hk hlog hpos hf
    have hEq : (Real.exp 1 * Real.sqrt N *
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖) *
        (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
        8 * Real.exp 1 * Real.sqrt N *
          (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖) +
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
      ring
    rw [hEq] at h1
    exact h1
  have hval : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (∫ t : ℝ,
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖) +
          ∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ *
              Real.log (|t| + 2) ^ 3)) := by
    rw [integral_const_mul, integral_add (hAi.const_mul _) hBi, integral_const_mul]
  have hub : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) ≤
      8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) := by
    rw [hval]
    have hc : (0 : ℝ) ≤ 8 * Real.exp 1 * Real.sqrt N := by positivity
    have hl : (0 : ℝ) ≤ Real.log N ^ 3 := pow_nonneg hlogN.le 3
    have h1 : Real.log N ^ 3 * (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) ≤ Real.log N ^ 3 * G :=
      mul_le_mul_of_nonneg_left hA hl
    have h2 : (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ *
            Real.log (|t| + 2) ^ 3)) ≤ G := hB
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  exact ⟨kernel_mass_integrable519 N α hN32 hα,
    (integral_mono (kernel_mass_integrable519 N α hN32 hα) hdomint hpoint).trans
      (hub.trans (mass_constant519 N G hN32 hGpos))⟩

/-- P0093 page 157 equation 4.4. The signed kernel with a continuous coefficient is jointly continuous in alpha and the finite line parameter. -/
theorem continuous_mellin_integrand519 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (fun p : ℝ × ℝ => mellinKernel519 N p.1 p.2 * M p.2) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hNr
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hline : Continuous (fun t : ℝ => mellinLine519 N t) := by
    dsimp [mellinLine519]; fun_prop
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine519 N t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hline.continuousAt
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hh
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hinv : 0 < 1 / Real.log N := by positivity
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  exact (((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)).mul (hM.comp continuous_snd)

/-- P0093 page 156 equation 4.1. Parameter integration of the continuous signed kernel makes the full Mellin value strongly measurable. -/
theorem stronglyMeasurable_mellinU519 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    StronglyMeasurable (mellinU519 N M) := by
  exact stronglyMeasurable_const.mul
    (continuous_mellin_integrand519 N hN M hM).stronglyMeasurable.integral_prod_right


/-- P0093 page 158 final sentence after equation 4.8. Reflecting alpha
conjugates the Mellin integral and reflects and conjugates its coefficient.
Positive N keeps the complex power base away from its branch cut.
No GRH or line bound is assumed. -/
theorem mellin_reflection519 (N : ℕ) (hN : 1 ≤ N) (M : ℝ → ℂ) (α : ℝ) :
    mellinU519 N (fun t => (starRingEnd ℂ) (M (-t))) α = (starRingEnd ℂ) (mellinU519 N M (-α)) := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * I
  have hx : x.arg ≠ Real.pi := by
    intro h
    have hh := (Complex.arg_eq_pi_iff.mp h).1
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hxp : 0 < x.re := by dsimp [x]; simp; positivity
    linarith
  have hline (t : ℝ) : mellinLine519 N (-t) = (starRingEnd ℂ) (mellinLine519 N t) := by
    simp only [mellinLine519, map_add, map_mul, Complex.conj_ofReal,
      Complex.ofReal_neg, Complex.conj_I]
    ring
  have hbase : (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * -α : ℝ) : ℂ) * I) = (starRingEnd ℂ) x := by
    dsimp [x]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  unfold mellinU519
  rw [map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  conv_rhs => rw [← integral_neg_eq_self _ volume]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hbase, hline, map_mul, map_mul, ← Gamma_conj, conj_conj]
  have hp := Complex.conj_cpow x (-((starRingEnd ℂ) (mellinLine519 N t))) hx
  simp only [map_neg, conj_conj] at hp
  rw [hp, conj_conj]

/-- P0093 page 158 final sentence after equation 4.8. Reflecting and
conjugating a coefficient preserves continuity and the cubic logarithmic
line bound with the same constant. -/
theorem reflected_line_bound519 (N : ℕ) (B0 : ℝ) (M : ℝ → ℂ) (hM : Continuous M)
    (hb : ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :
    Continuous (fun t => (starRingEnd ℂ) (M (-t))) ∧ ∀ t : ℝ,
      ‖(starRingEnd ℂ) (M (-t))‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  refine ⟨continuous_star.comp (hM.comp continuous_neg), fun t => ?_⟩
  simpa only [Complex.norm_conj, abs_neg] using hb (-t)

/-- P0093 page 158 final sentence after equation 4.8. The negative
half square integral equals the positive half square integral for the
reflected conjugate coefficient. Interval orientation is retained. -/
theorem mellin_negative_square519 (N : ℕ) (hN : 1 ≤ N) (M : ℝ → ℂ) (r : ℝ) :
    (∫ α in -r..0, ‖mellinU519 N M α‖ ^ 2) =
      ∫ α in 0..r, ‖mellinU519 N (fun t => (starRingEnd ℂ) (M (-t))) α‖ ^ 2 := by
  simp_rw [mellin_reflection519 N hN M, Complex.norm_conj]
  simpa only [neg_zero] using
    (intervalIntegral.integral_comp_neg (f := fun α => ‖mellinU519 N M α‖ ^ 2)
      (a := 0) (b := r)).symm

/-- P0093 page 158 before equation 4.8. The clean central absolute
kernel bound controls every coefficient with the cubic logarithmic line bound. -/
theorem central_mellin_bound519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
        ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
        ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
          ‖mellinU519 N M α‖ ≤ K * Real.sqrt N * Real.log N ^ 3 := by
  obtain ⟨C, hC, N0, hc⟩ := central_kernel_mass519
  refine ⟨(1 / (2 * Real.pi)) * B0 * C, by positivity, N0, ?_⟩
  intro N hN M hM α hα
  obtain ⟨hi, hm⟩ := hc N hN α hα
  calc
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (∫ t : ℝ, ‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mellin_kernel_domination519 N α B0 hB0.le M hM hi
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (C * Real.sqrt N * Real.log N ^ 3) := by gcongr
    _ = _ := by ring

/-- P0093 page 158 equation 4.8. The positive central interval has
integrable square mass at most a constant times log to the sixth N.
This follows from the clean square root N pointwise bound and interval length. -/
theorem central_square_mass519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
        ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
        IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc 0 (4 / (N : ℝ))) ∧
        (∫ α in 0..(4 / (N : ℝ)), ‖mellinU519 N M α‖ ^ 2) ≤ C * Real.log N ^ 6 := by
  obtain ⟨K, hK, Nk, hk⟩ := central_mellin_bound519 B0 hB0
  refine ⟨4 * K ^ 2, by positivity, max 3 Nk, ?_⟩
  intro N hN M hM
  have hN3 : 3 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : ∀ α ∈ Set.Icc (0 : ℝ) (4 / (N : ℝ)),
      ‖mellinU519 N M α‖ ^ 2 ≤ K ^ 2 * N * Real.log N ^ 6 := by
    intro α hα
    have hαabs : |α| ≤ 4 / (N : ℝ) := by rw [abs_of_nonneg hα.1]; exact hα.2
    have hh := hk N (by omega) M hM α hαabs
    calc _ ≤ (K * Real.sqrt N * Real.log N ^ 3) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hNp.le]; ring
  have hiC : IntegrableOn (fun _ : ℝ => K ^ 2 * N * Real.log N ^ 6)
      (Set.Icc 0 (4 / (N : ℝ))) := continuous_const.integrableOn_Icc
  have hi : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc 0 (4 / (N : ℝ))) := by
    refine hiC.mono' ((stronglyMeasurable_mellinU519 N hN3 M hM.1).norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖mellinU519 N M α‖)]
    exact hs α hα
  refine ⟨hi, ?_⟩
  have hiI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))).mpr hi
  calc
    _ ≤ ∫ α in (0 : ℝ)..(4 / (N : ℝ)), K ^ 2 * N * Real.log N ^ 6 :=
      intervalIntegral.integral_mono_on (by positivity) hiI intervalIntegrable_const hs
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp [hNp.ne'] <;> ring


/-- P0093 page 166 passage from equation 9.1 to 9.3. The logarithmic
totient ratio keeps the full q saving on the specified minor denominator range. -/
theorem principal_arithmetic519 (N q : ℕ) (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hq : (N : ℝ) ^ (1 / 10 : ℝ) ≤ q) (hqN : (q : ℝ) ≤ N) :
    (N : ℝ) / q.totient ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : 1 ≤ q := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hφp : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hratio : (q : ℝ) / q.totient ≤ 4 * Real.log N := by
    have ht := LeanLab.Perelli1996.TotientRatio320.ratio_le_log q (by omega)
    have hl := Real.log_le_log hqp hqN
    linarith
  have hdiv : (N : ℝ) / q ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc
      _ ≤ (N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) :=
        div_le_div_of_nonneg_left hNp.le (by positivity) hq
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one (N : ℝ)]
        rw [← Real.rpow_sub hNp]
        norm_num
  calc
    _ = ((N : ℝ) / q) * ((q : ℝ) / q.totient) := by field_simp
    _ ≤ (N : ℝ) ^ (9 / 10 : ℝ) * (4 * Real.log N) :=
      mul_le_mul hdiv hratio (by positivity) (by positivity)
    _ = _ := by ring

/-- P0093 page 166 equations 9.1 and 9.3. The denominator range is
nonempty at arbitrarily large integral scales: N is k to seventy and q
is k to nine for any integer k at least two. -/
theorem denominator_range519 (k : ℕ) (hk : 2 ≤ k) :
    (((k ^ 70 : ℕ) : ℝ) ^ (1 / 10 : ℝ) < (k ^ 9 : ℕ)) ∧
      ((k ^ 9 : ℕ) : ℝ) ≤ ((k ^ 70 : ℕ) : ℝ) ^ (1 / 7 : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkl : (1 : ℝ) < k := by exact_mod_cast hk
  have he10 : (((k ^ 70 : ℕ) : ℝ) ^ (1 / 10 : ℝ)) = (k : ℝ) ^ (7 : ℕ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hk0]
    norm_num
  have he7 : (((k ^ 70 : ℕ) : ℝ) ^ (1 / 7 : ℝ)) = (k : ℝ) ^ (10 : ℕ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hk0]
    norm_num
  rw [he10, he7, Nat.cast_pow]
  exact ⟨pow_lt_pow_right₀ hkl (by omega), pow_le_pow_right₀ hkl.le (by omega)⟩

/-- P0093 page 166 passage from equation 9.1 to 9.3. Arithmetic audit
of the earlier square root totient route. A bound at exponent nineteen
twentieths cannot imply any fixed constant bound at ninety three hundredths.
This compares candidate bounds and asserts no failure of the paper. -/
theorem square_root_totient_loss519 (C : ℝ) : ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
    C * (N : ℝ) ^ (93 / 100 : ℝ) < (N : ℝ) ^ (19 / 20 : ℝ) := by
  have he : ∀ᶠ N : ℕ in atTop, C < (N : ℝ) ^ (1 / 50 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp he
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hC := hN0 N (by omega)
  calc _ < (N : ℝ) ^ (1 / 50 : ℝ) * (N : ℝ) ^ (93 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hNp _)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

/-- P0093 page 159 equation 5.2. The nonprincipal character domain
has a concrete inhabitant modulo three. This instance assumes no GRH. -/
theorem nonprincipal_mod_three519 : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  have hc : Fintype.card (DirichletCharacter ℂ 3) = 2 := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 3]
    rw [Nat.totient_prime Nat.prime_three]
  exact Fintype.exists_ne_of_one_lt_card (by omega) 1

/-- P0093 page 166 definition of the doubled system. A concrete membership. -/
example : (1 / 2 : ℝ) ∈ arcSystem519 2 4 := by
  refine ⟨(1 / 2 : ℚ), by norm_num, ?_⟩
  norm_num

/-! Axiom audit for every public and private theorem in this port. -/











end LeanLab.Linnik1951.Task519
