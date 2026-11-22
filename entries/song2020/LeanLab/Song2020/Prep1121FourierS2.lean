module

public import LeanLab.Song2020.Decomp139
public import LeanLab.Song2020.Repair591FourierMajorant
public import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-!
AI wrote the Lean code, Claude, 2026-11-21.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, printed pages 3 to 5, S2 on page 4 and the top of page 5,
Lemma 1 and the S2 displays of the proof of Lemma 4.
Split of the route step `Decomp139.fourier_approximation` into leaves.
The coefficient family comes from the proved `song_lemma1_majorant591`, set to zero
outside the range |h| at most H. The S2 argument of page 5 is then cut into a pointwise
majorant bound, the passage from primes to integers, the expansion of the majorant,
the conjugation symmetry, partial summation, the exponent pair (1/2, 1/2) input of
Graham and Kolesnik display 3.3.4, the frequency zero term and the final arithmetic.
The theorem `fourier_approximation_of_leaves` at the end proves the exact statement
of `Decomp139.fourier_approximation` from these leaves; no existing file is changed.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Prep1121FourierS2

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput
open scoped Classical

noncomputable section

/-! ## Elementary facts about `eC` -/

theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : (2 * Real.pi * Complex.I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem eC_neg (x : ℝ) : eC (-x) = (starRingEnd ℂ) (eC x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, Complex.conj_ofReal]
  simp [Complex.conj_ofReal, h2]

/-! ## Leaves and proved steps -/

/-- Proved STEP: Song 2020, page 4, display defining S1 plus S2, and page 3, Lemma 1.
The sawtooth difference minus its truncation is the difference of the two values of
psi double prime, and a pointwise real majorant M of psi double prime bounds S2 by the
weighted sum of M at both points. Proved here. -/
theorem s2_pointwise_majorant (γ : ℝ) (hγ : 0 < γ) (n : ℕ) (y α : ℝ)
    (a : ℕ → ℤ → ℂ) (H : ℕ) (M : ℝ → ℝ)
    (hM : ∀ x : ℝ, ‖((saw x : ℝ) : ℂ) - Decomp139.fourier a H x‖ ≤ M x) :
    ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
      ∑ p ∈ windowPrimes n y,
        psWeight γ p * (M (-((p : ℝ) + 1) ^ γ) + M (-(p : ℝ) ^ γ)) := by
  unfold sawSum truncatedSum
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have hw : 0 ≤ psWeight γ p := by
    unfold psWeight
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have heq : (psWeight γ p : ℂ) * eC (α * p) *
        ((saw (-((p : ℝ) + 1) ^ γ) - saw (-(p : ℝ) ^ γ) : ℝ) : ℂ) -
      (psWeight γ p : ℂ) * eC (α * p) *
        (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ)) =
      (psWeight γ p : ℂ) * eC (α * p) *
        ((((saw (-((p : ℝ) + 1) ^ γ) : ℝ) : ℂ) - fourier a H (-((p : ℝ) + 1) ^ γ)) -
          (((saw (-(p : ℝ) ^ γ) : ℝ) : ℂ) - fourier a H (-(p : ℝ) ^ γ))) := by
    push_cast; ring
  rw [heq, norm_mul, norm_mul, norm_eC, Complex.norm_real, Real.norm_of_nonneg hw, mul_one]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hM _) (hM _))) hw

/-- Proved STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the passage from the primes of the window
to all integers of the window, valid because the summand is nonnegative. Proved here. -/
theorem primes_to_window (n : ℕ) (y : ℝ) (F : ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ p ∈ windowPrimes n y, F p ≤
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), F x := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hF x)
  intro x hx
  unfold windowPrimes at hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.2⟩

/-- Proved STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", expansion of the majorant of Lemma 1:
the weighted sum of the real majorant is at most the coefficient bound times the sum over
|h| at most H of the exponential sums. Proved here. -/
theorem majorant_expand (S : Finset ℕ) (w : ℕ → ℝ) (φ : ℕ → ℝ) (b : ℤ → ℂ) (H : ℕ)
    (B : ℝ) (hb : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b h‖ ≤ B) :
    ∑ x ∈ S, w x * (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (φ x * h)).re ≤
      B * ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        ‖∑ x ∈ S, (w x : ℂ) * eC (φ x * h)‖ := by
  have h1 : ∑ x ∈ S, w x * (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (φ x * h)).re =
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * ∑ x ∈ S, (w x : ℂ) * eC (φ x * h)).re := by
    have hc : (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * ∑ x ∈ S, (w x : ℂ) * eC (φ x * h)) =
        ∑ x ∈ S, (w x : ℂ) * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (φ x * h) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro h _
      ring
    rw [hc, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.re_ofReal_mul]
  rw [h1, Finset.mul_sum]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb h hh) (norm_nonneg _)

/-- Proved STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the reduction to positive frequencies
1 at most h at most H: with real weights, the frequency h at the point minus u has the same
modulus as the frequency |h| at the point u, by complex conjugation. Proved here. -/
theorem conj_phase (S : Finset ℕ) (w u : ℕ → ℝ) (h : ℤ) :
    ‖∑ x ∈ S, (w x : ℂ) * eC (-(u x) * h)‖ =
      ‖∑ x ∈ S, (w x : ℂ) * eC (((h.natAbs : ℕ) : ℝ) * u x)‖ := by
  rcases le_or_gt 0 h with h0 | h0
  · have hc : ((h.natAbs : ℕ) : ℝ) = (h : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h0)]
    have : ∑ x ∈ S, (w x : ℂ) * eC (-(u x) * h) =
        (starRingEnd ℂ) (∑ x ∈ S, (w x : ℂ) * eC (((h.natAbs : ℕ) : ℝ) * u x)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← eC_neg, hc]
      congr 2; ring
    rw [this, Complex.norm_conj]
  · have hc : ((h.natAbs : ℕ) : ℝ) = -(h : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h0)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hc]; congr 2; ring

/-! ## Private partial summation lemmas for `weighted_window_bound`

The four elementary steps needed by the leaf are proved in `RouteS1Abel`, which is not an
import of this file in the lab; they are restated privately here so that the leaf needs no new import. -/

private theorem window_mem_bounds' (n : ℕ) (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (x : ℕ)
    (hx : x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)) :
    1 ≤ x ∧ x ≤ n := by
  rw [Finset.mem_filter] at hx
  obtain ⟨_, hx⟩ := hx
  rw [abs_lt] at hx
  obtain ⟨h1, h2⟩ := hx
  constructor
  · have h3 : (0 : ℝ) < (x : ℝ) := by linarith
    exact Nat.succ_le_of_lt (by exact_mod_cast h3)
  · have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : (x : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast h3

private theorem window_eq_Ico' (n : ℕ) (y : ℝ) :
    ∃ a b : ℕ, (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
      (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y) = Finset.Ico a b := by
  by_cases h0 : 0 ≤ (n : ℝ) / 3 - y
  · refine ⟨Nat.floor ((n : ℝ) / 3 - y) + 1, Nat.ceil ((n : ℝ) / 3 + y), ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, abs_lt]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt h0).2 (by linarith)), Nat.lt_ceil.2 (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.floor_lt h0).1 (Nat.lt_of_succ_le h1)
      have h4 := Nat.lt_ceil.1 h2
      exact ⟨by omega, by linarith, by linarith⟩
  · refine ⟨0, Nat.ceil ((n : ℝ) / 3 + y), ?_⟩
    rw [not_le] at h0
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, abs_lt]
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Nat.zero_le _, Nat.lt_ceil.2 (by linarith)⟩
    · rintro ⟨_, h2⟩
      have h4 := Nat.lt_ceil.1 h2
      exact ⟨by omega, by linarith, by linarith⟩

private theorem sum_Ico_by_parts' (w c : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a (b + 1), w x * c x =
      w b * ∑ x ∈ Finset.Ico a (b + 1), c x -
        ∑ x ∈ Finset.Ico a b, (w (x + 1) - w x) * ∑ z ∈ Finset.Ico a (x + 1), c z := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top (by omega : a ≤ b + 1) (fun x => w x * c x), ih,
      Finset.sum_Ico_succ_top (by omega : a ≤ b + 1) c,
      Finset.sum_Ico_succ_top hab
        (fun x => (w (x + 1) - w x) * ∑ z ∈ Finset.Ico a (x + 1), c z)]
    ring

private theorem norm_sum_Ico_mul_le' (w c : ℕ → ℂ) (a b : ℕ) (B : ℝ)
    (hB : ∀ m : ℕ, m ≤ b → ‖∑ x ∈ Finset.Ico a m, c x‖ ≤ B) :
    ‖∑ x ∈ Finset.Ico a b, w x * c x‖ ≤
      (‖w (b - 1)‖ + ∑ x ∈ Finset.Ico a (b - 1), ‖w (x + 1) - w x‖) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
    have had : a ≤ d := by omega
    rw [sum_Ico_by_parts' w c a d had, Nat.add_sub_cancel, add_mul, Finset.sum_mul]
    refine (norm_sub_le _ _).trans
      (add_le_add ?_ ((norm_sum_le _ _).trans (Finset.sum_le_sum ?_)))
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _ le_rfl) (norm_nonneg _)
    · intro x hx
      rw [norm_mul]
      have hx2 := (Finset.mem_Ico.1 hx).2
      exact mul_le_mul_of_nonneg_left (hB _ (by omega)) (norm_nonneg _)
  · rw [Finset.Ico_eq_empty_of_le hab, Finset.sum_empty, norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))) hB0

private theorem sum_Ico_telescope' (g : ℕ → ℝ) (a : ℕ) :
    ∀ b : ℕ, a ≤ b → ∑ x ∈ Finset.Ico a b, (g (x + 1) - g x) = g b - g a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

/-- Song 2020, page 4, display after "Partial summation yields":
the weighted window sum with the weight psWeight, at most 1/γ times n to the 1 minus γ,
is at most 2/γ times n to the 1 minus γ times any bound B on the exponential sums over the
initial segments of the window. Route: RouteS1Abel.norm_window_sum_mul_le with the weight
truncated beyond n, plus the telescoping total variation of the increasing weight. -/
theorem weighted_window_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (f : ℕ → ℝ) (B : ℝ)
    (hB : ∀ t : ℝ, ‖∑ x ∈ subWindow n y t, eC (f x)‖ ≤ B) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), (psWeight γ x : ℂ) * eC (f x)‖ ≤
      2 / γ * (n : ℝ) ^ (1 - γ) * B := by
  obtain ⟨a, b, hab⟩ := window_eq_Ico' n y
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [hab]
  rcases Nat.lt_or_ge a b with hablt | habge
  · have hseg : ∀ m : ℕ, m ≤ b → ‖∑ x ∈ Finset.Ico a m, eC (f x)‖ ≤ B := by
      intro m hm
      have hff : (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ (m : ℝ) - 1) =
          ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y)).filter
              (fun x : ℕ => (x : ℝ) ≤ (m : ℝ) - 1) := by
        rw [Finset.filter_filter]
      have hset : Finset.Ico a m = (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ (m : ℝ) - 1) := by
        rw [hff, hab]
        ext x
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, by omega⟩, ?_⟩
          have h3 : ((x + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
          push_cast at h3
          linarith
        · rintro ⟨⟨h1, _⟩, h2⟩
          refine ⟨h1, ?_⟩
          have h3 : ((x + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
            push_cast
            linarith
          exact_mod_cast h3
      rw [hset]
      exact hB _
    have key := norm_sum_Ico_mul_le' (fun x => (psWeight γ x : ℂ)) (fun x => eC (f x)) a b B hseg
    refine key.trans (mul_le_mul_of_nonneg_right ?_ hB0)
    have hmem : b - 1 ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hmem' : b - 1 ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y) := by
      rw [hab]
      exact hmem
    have hb1n : b - 1 ≤ n := (window_mem_bounds' n y hy (b - 1) hmem').2
    have hpow : ((b - 1 : ℕ) : ℝ) ^ (1 - γ) ≤ (n : ℝ) ^ (1 - γ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg (b - 1)) (by exact_mod_cast hb1n) (by linarith)
    have hps0 : ∀ m : ℕ, 0 ≤ psWeight γ m := fun m => by
      unfold psWeight
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    have hlast : ‖(psWeight γ (b - 1) : ℂ)‖ ≤ 1 / γ * (n : ℝ) ^ (1 - γ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (hps0 (b - 1))]
      unfold psWeight
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hstep : ∀ x ∈ Finset.Ico a (b - 1),
        ‖(psWeight γ (x + 1) : ℂ) - (psWeight γ x : ℂ)‖ = psWeight γ (x + 1) - psWeight γ x := by
      intro x _
      have hnn : 0 ≤ psWeight γ (x + 1) - psWeight γ x := by
        unfold psWeight
        rw [← mul_sub]
        refine mul_nonneg (by positivity) ?_
        have hmono : (x : ℝ) ^ (1 - γ) ≤ ((x + 1 : ℕ) : ℝ) ^ (1 - γ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg x) (by push_cast; linarith) (by linarith)
        linarith
      rw [← Complex.ofReal_sub, Complex.norm_real]
      exact Real.norm_of_nonneg hnn
    have hvar : ∑ x ∈ Finset.Ico a (b - 1),
        ‖(psWeight γ (x + 1) : ℂ) - (psWeight γ x : ℂ)‖ ≤ 1 / γ * (n : ℝ) ^ (1 - γ) := by
      have hcongr : ∑ x ∈ Finset.Ico a (b - 1),
          ‖(psWeight γ (x + 1) : ℂ) - (psWeight γ x : ℂ)‖ =
          ∑ x ∈ Finset.Ico a (b - 1), (psWeight γ (x + 1) - psWeight γ x) :=
        Finset.sum_congr rfl hstep
      have htel : ∑ x ∈ Finset.Ico a (b - 1),
          (psWeight γ (x + 1) - psWeight γ x) = psWeight γ (b - 1) - psWeight γ a :=
        sum_Ico_telescope' (fun x => psWeight γ x) a (b - 1) (by omega)
      rw [hcongr, htel]
      have hdrop : psWeight γ (b - 1) - psWeight γ a ≤ psWeight γ (b - 1) := by
        linarith [hps0 a]
      refine hdrop.trans ?_
      unfold psWeight
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    calc ‖(psWeight γ (b - 1) : ℂ)‖ +
          ∑ x ∈ Finset.Ico a (b - 1), ‖(psWeight γ (x + 1) : ℂ) - (psWeight γ x : ℂ)‖
        ≤ 1 / γ * (n : ℝ) ^ (1 - γ) + 1 / γ * (n : ℝ) ^ (1 - γ) := add_le_add hlast hvar
      _ = 2 / γ * (n : ℝ) ^ (1 - γ) := by ring
  · rw [Finset.Ico_eq_empty_of_le habge, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hB0


/-! ### Analytic core (from results/scratch1121s2/coreA.lean) -/


/-- `y ↦ y ^ e` is decreasing on the positive half line when `e < 0`. -/
theorem rpow_mono_of_neg_exp {e : ℝ} (he : e < 0) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ e ≤ x ^ e := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h1 : y ^ e = (y ^ (-e))⁻¹ := by
    simpa using Real.rpow_neg (x := y) hy.le (-e)
  have h2 : x ^ e = (x ^ (-e))⁻¹ := by
    simpa using Real.rpow_neg (x := x) hx.le (-e)
  rw [h1, h2]
  have h3 : x ^ (-e) ≤ y ^ (-e) := Real.rpow_le_rpow hx.le hxy (by linarith)
  have h4 : 1 / y ^ (-e) ≤ 1 / x ^ (-e) :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx _) h3
  simpa [one_div] using h4

/-- The increment of `y ↦ y ^ γ` over `[a, b]` is between `γ b ^ (γ-1)` and `γ a ^ (γ-1)`
times `b - a`, for `0 < γ < 1` and `1 ≤ a ≤ b`. -/
theorem rpow_step_sandwich {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    γ * b ^ (γ - 1) * (b - a) ≤ b ^ γ - a ^ γ ∧ b ^ γ - a ^ γ ≤ γ * a ^ (γ - 1) * (b - a) := by
  have ha0 : 0 < a := by linarith
  rcases lt_or_eq_of_le hab with hlt | heq
  · have hb0 : 0 < b := by linarith
    have hcont : ContinuousOn (fun y : ℝ => y ^ γ) (Set.Icc a b) :=
      (Real.continuous_rpow_const hγ0.le).continuousOn
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => y ^ γ) (Set.Ioo a b) :=
      (Real.differentiableOn_rpow_const γ).mono
        (fun y hy => ne_of_gt (show (0 : ℝ) < y from by linarith [hy.1]))
    obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope (fun y : ℝ => y ^ γ) hlt hcont hdiff
    have hc0 : 0 < c := by linarith [hc.1]
    have hval : deriv (fun y : ℝ => y ^ γ) c = γ * c ^ (γ - 1) := Real.deriv_rpow_const c γ
    rw [hval] at hderiv
    have hba : (0 : ℝ) < b - a := by linarith
    have key : b ^ γ - a ^ γ = γ * c ^ (γ - 1) * (b - a) := by
      rw [hderiv]
      field_simp
    rw [key]
    constructor
    · have h1 : b ^ (γ - 1) ≤ c ^ (γ - 1) :=
        rpow_mono_of_neg_exp (by linarith) hc0 hc.2.le
      have h2 : γ * b ^ (γ - 1) ≤ γ * c ^ (γ - 1) :=
        mul_le_mul_of_nonneg_left h1 hγ0.le
      exact mul_le_mul_of_nonneg_right h2 hba.le
    · have h1 : c ^ (γ - 1) ≤ a ^ (γ - 1) :=
        rpow_mono_of_neg_exp (by linarith) ha0 hc.1.le
      have h2 : γ * c ^ (γ - 1) ≤ γ * a ^ (γ - 1) :=
        mul_le_mul_of_nonneg_left h1 hγ0.le
      exact mul_le_mul_of_nonneg_right h2 hba.le
  · subst heq
    simp

/-- The increments of `y ↦ y ^ γ` are decreasing. -/
theorem rpow_incr_anti {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {x : ℝ} (hx : 1 ≤ x) :
    (x + 2) ^ γ - (x + 1) ^ γ ≤ (x + 1) ^ γ - x ^ γ := by
  have h1 := (rpow_step_sandwich hγ0 hγ1 (a := x) (b := x + 1) hx (by linarith)).1
  have h2 := (rpow_step_sandwich hγ0 hγ1 (a := x + 1) (b := x + 2) (by linarith) (by linarith)).2
  have h1' : γ * (x + 1) ^ (γ - 1) ≤ (x + 1) ^ γ - x ^ γ := by
    have := h1; rw [show (x + 1) - x = (1 : ℝ) by ring, mul_one] at this; linarith
  have h2' : (x + 2) ^ γ - (x + 1) ^ γ ≤ γ * (x + 1) ^ (γ - 1) := by
    have := h2; rw [show (x + 2) - (x + 1) = (1 : ℝ) by ring, mul_one] at this; linarith
  linarith

/-- The second difference of `y ↦ y ^ γ` is between `γ(1-γ)(x+2)^(γ-2)` and `γ(1-γ)x^(γ-2)`. -/
theorem rpow_second_diff_sandwich {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {x : ℝ} (hx : 1 ≤ x) :
    γ * (1 - γ) * (x + 2) ^ (γ - 2) ≤ 2 * (x + 1) ^ γ - x ^ γ - (x + 2) ^ γ ∧
      2 * (x + 1) ^ γ - x ^ γ - (x + 2) ^ γ ≤ γ * (1 - γ) * x ^ (γ - 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hγ1' : γ - 1 < 0 := by linarith
  have hγ2' : γ - 2 < 0 := by linarith
  -- continuity of the increment function
  have hcont_i : ContinuousOn (fun y : ℝ => (y + 1) ^ γ - y ^ γ) (Set.Icc x (x + 1)) := by
    refine (((Real.continuous_rpow_const hγ0.le).comp (by continuity)).sub
      (Real.continuous_rpow_const hγ0.le)).continuousOn
  have hdiff_i : DifferentiableOn ℝ (fun y : ℝ => (y + 1) ^ γ - y ^ γ) (Set.Ioo x (x + 1)) := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (by linarith [hy.1])
    have hy1 : y + 1 ≠ 0 := ne_of_gt (by linarith [hy.1])
    exact (((Real.differentiableAt_rpow_const_of_ne γ hy1).comp y
      (differentiableAt_id.add_const 1)).sub
        (Real.differentiableAt_rpow_const_of_ne γ hy0)).differentiableWithinAt
  obtain ⟨ζ, hζ, hζderiv⟩ :=
    exists_deriv_eq_slope (fun y : ℝ => (y + 1) ^ γ - y ^ γ) (by linarith : x < x + 1)
      hcont_i hdiff_i
  have hζ0 : 0 < ζ := by linarith [hζ.1]
  have hζ1 : 0 < ζ + 1 := by linarith [hζ.1]
  -- derivative of the increment function
  have hdi : deriv (fun y : ℝ => (y + 1) ^ γ - y ^ γ) ζ =
      γ * (ζ + 1) ^ (γ - 1) - γ * ζ ^ (γ - 1) := by
    have h1 : HasDerivAt (fun y : ℝ => (y + 1) ^ γ) (γ * (ζ + 1) ^ (γ - 1)) ζ := by
      have hbase : HasDerivAt (fun y : ℝ => y + 1) 1 ζ := by
        simpa using (hasDerivAt_id ζ).add_const (1 : ℝ)
      have h := (Real.hasDerivAt_rpow_const (x := ζ + 1) (p := γ) (Or.inl (ne_of_gt hζ1))).comp ζ hbase
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun y : ℝ => y ^ γ) (γ * ζ ^ (γ - 1)) ζ :=
      Real.hasDerivAt_rpow_const (x := ζ) (p := γ) (Or.inl (ne_of_gt hζ0))
    have hd := (h1.sub h2).deriv
    rw [show ((fun y : ℝ => (y + 1) ^ γ) - fun y : ℝ => y ^ γ)
      = (fun y : ℝ => (y + 1) ^ γ - y ^ γ) from rfl] at hd
    exact hd
  -- the value at ζ is also the slope of the first derivative over ζ, ζ + 1
  have hcont_g : ContinuousOn (fun y : ℝ => γ * y ^ (γ - 1)) (Set.Icc ζ (ζ + 1)) := by
    have h : ContinuousOn (fun y : ℝ => y ^ (γ - 1)) (Set.Icc ζ (ζ + 1)) := by
      intro y hy
      exact (Real.continuousAt_rpow_const y (γ - 1)
        (Or.inl (ne_of_gt (by linarith [hy.1])))).continuousWithinAt
    exact continuousOn_const.mul h
  have hdiff_g : DifferentiableOn ℝ (fun y : ℝ => γ * y ^ (γ - 1)) (Set.Ioo ζ (ζ + 1)) := by
    have h : DifferentiableOn ℝ (fun y : ℝ => y ^ (γ - 1)) (Set.Ioo ζ (ζ + 1)) := by
      intro y hy
      exact (Real.differentiableAt_rpow_const_of_ne (γ - 1)
        (ne_of_gt (by linarith [hy.1]))).differentiableWithinAt
    simpa using h.const_mul γ
  obtain ⟨θ, hθ, hθderiv⟩ :=
    exists_deriv_eq_slope (fun y : ℝ => γ * y ^ (γ - 1)) (by linarith [hζ.1] : ζ < ζ + 1)
      hcont_g hdiff_g
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hdg : deriv (fun y : ℝ => γ * y ^ (γ - 1)) θ = γ * (γ - 1) * θ ^ (γ - 2) := by
    have hθne : θ ≠ 0 := ne_of_gt hθ0
    have h : HasDerivAt (fun y : ℝ => γ * y ^ (γ - 1)) (γ * ((γ - 1) * θ ^ (γ - 2))) θ := by
      have h0 := (Real.hasDerivAt_rpow_const (x := θ) (p := γ - 1) (Or.inl hθne)).const_mul γ
      convert h0 using 2
      ring
    rw [h.deriv]
    ring
  -- chain the two mean value equalities
  have hζval : (x + 2) ^ γ - 2 * (x + 1) ^ γ + x ^ γ =
      γ * ((ζ + 1) ^ (γ - 1) - ζ ^ (γ - 1)) := by
    have hfrac : (x + 2) ^ γ - 2 * (x + 1) ^ γ + x ^ γ =
        ((x + 1 + 1) ^ γ - (x + 1) ^ γ - ((x + 1) ^ γ - x ^ γ)) / (x + 1 - x) := by
      rw [show x + 1 - x = (1 : ℝ) by ring, div_one]
      ring
    rw [hfrac, ← hζderiv, hdi]
    ring
  have hθval : γ * ((ζ + 1) ^ (γ - 1) - ζ ^ (γ - 1)) = γ * (γ - 1) * θ ^ (γ - 2) := by
    have hfrac : γ * ((ζ + 1) ^ (γ - 1) - ζ ^ (γ - 1)) =
        (γ * (ζ + 1) ^ (γ - 1) - γ * ζ ^ (γ - 1)) / (ζ + 1 - ζ) := by
      rw [show ζ + 1 - ζ = (1 : ℝ) by ring, div_one]
      ring
    rw [hfrac, ← hθderiv, hdg]
  have hD : 2 * (x + 1) ^ γ - x ^ γ - (x + 2) ^ γ = γ * (1 - γ) * θ ^ (γ - 2) := by
    have := hζval.trans hθval
    linarith [this]
  rw [hD]
  have hθb : θ < x + 2 := by linarith [hθ.2, hζ.2]
  have hγpos : 0 < γ * (1 - γ) := by nlinarith
  have hlo : θ ^ (γ - 2) ≤ x ^ (γ - 2) :=
    rpow_mono_of_neg_exp hγ2' hx0 (by linarith [hθ.1, hζ.1])
  have hhi : (x + 2) ^ (γ - 2) ≤ θ ^ (γ - 2) :=
    rpow_mono_of_neg_exp hγ2' hθ0 (le_of_lt hθb)
  constructor
  · exact mul_le_mul_of_nonneg_left hhi hγpos.le
  · exact mul_le_mul_of_nonneg_left hlo hγpos.le


/-! ### The leaf-2 development -/

/-- `eC` of the target file is `PortedVanDerCorput.eK`. -/
private theorem eC_eq_eK (x : ℝ) : eC x = eK x := by
  unfold eC eK
  congr 1
  push_cast
  ring

/-- Replacing `eC` by the conjugate of `eK` at the negative phase keeps the modulus. -/
private theorem norm_sum_eC_eq_neg_eK (s : Finset ℕ) (g : ℕ → ℝ) :
    ‖∑ x ∈ s, eC (g x)‖ = ‖∑ x ∈ s, eK (-(g x))‖ := by
  have h1 : ∑ x ∈ s, eK (-(g x)) = (starRingEnd ℂ) (∑ x ∈ s, eK (g x)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => eK_neg (g x)
  rw [h1, Complex.norm_conj]
  exact congrArg norm (Finset.sum_congr rfl fun x _ => eC_eq_eK (g x))

/-- `Ioc (A-1) (B-1)` is `Ico A B` for `1 ≤ A`. -/
private theorem Ioc_pred_eq_Ico {A B : ℕ} (hA : 1 ≤ A) :
    Finset.Ioc (A - 1) (B - 1) = Finset.Ico A B := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- FLAT case of the exponent pair: if the phase differences are all smaller than `1/2`, the
Kusmin-Landau inequality gives `1/δ` with `δ` the top of the range. -/
private theorem flat_case {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {N k A B : ℕ}
    (hA : 1 ≤ A) (hB1 : 1 ≤ B) (hBN : B ≤ N) (hk : 1 ≤ k)
    (hslope : (k : ℝ) * γ * (A : ℝ) ^ (γ - 1) ≤ 1 / 2) :
    ‖∑ x ∈ Finset.Ico A B, eC ((k : ℝ) * (x : ℝ) ^ γ)‖ ≤
      1 / γ * (N : ℝ) ^ (1 - γ) * (k : ℝ)⁻¹ := by
  by_cases hBA : B ≤ A
  · rw [Finset.Ico_eq_empty_of_le hBA]
    simp only [Finset.sum_empty, norm_zero]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (1 - γ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hk0 : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
    have : (0 : ℝ) ≤ 1 / γ * (N : ℝ) ^ (1 - γ) * (k : ℝ)⁻¹ :=
      mul_nonneg (mul_nonneg (by positivity) hN0) hk0
    linarith
  · have hAB : A < B := by omega
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
    have hABr : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_of_lt hAB
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hδ0 : 0 < (k : ℝ) * γ * (B : ℝ) ^ (γ - 1) := by positivity
    have hδhalf : (k : ℝ) * γ * (B : ℝ) ^ (γ - 1) ≤ 1 / 2 := by
      have hBAr : (B : ℝ) ^ (γ - 1) ≤ (A : ℝ) ^ (γ - 1) :=
        rpow_mono_of_neg_exp (by linarith) hApos hABr
      have hkγ : (0 : ℝ) < (k : ℝ) * γ := mul_pos hkpos hγ0
      have h1 : (k : ℝ) * γ * (B : ℝ) ^ (γ - 1) ≤ (k : ℝ) * γ * (A : ℝ) ^ (γ - 1) := by
        calc (k : ℝ) * γ * (B : ℝ) ^ (γ - 1) = ((k : ℝ) * γ) * (B : ℝ) ^ (γ - 1) := by ring
          _ ≤ ((k : ℝ) * γ) * (A : ℝ) ^ (γ - 1) := mul_le_mul_of_nonneg_left hBAr hkγ.le
          _ = (k : ℝ) * γ * (A : ℝ) ^ (γ - 1) := by ring
      linarith [h1, hslope]
    rw [norm_sum_eC_eq_neg_eK, ← Ioc_pred_eq_Ico hA]
    have hmain := kusmin_landau (f := fun n : ℕ => -((k : ℝ) * (n : ℝ) ^ γ))
      (a := A - 1) (b := B - 1) (δ := (k : ℝ) * γ * (B : ℝ) ^ (γ - 1)) (m := -1)
      hδ0 hδhalf
      (by
        intro n hn1 hn2
        have hnA : A ≤ n := by omega
        have hn1' : (1 : ℕ) ≤ n := le_trans hA hnA
        have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
        have hna : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnA
        have hinc : ((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ ≤ γ * (n : ℝ) ^ (γ - 1) := by
          have hstep := (rpow_step_sandwich hγ0 hγ1 (a := (n : ℝ)) (b := (n : ℝ) + 1)
            hnr (by linarith)).2
          rwa [show (n : ℝ) + 1 - (n : ℝ) = (1 : ℝ) by ring, mul_one] at hstep
        have hmono : (n : ℝ) ^ (γ - 1) ≤ (A : ℝ) ^ (γ - 1) :=
          rpow_mono_of_neg_exp (by linarith) hApos hna
        have hsmall : (k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ) ≤ 1 / 2 := by
          have h2 : γ * (n : ℝ) ^ (γ - 1) ≤ γ * (A : ℝ) ^ (γ - 1) :=
            mul_le_mul_of_nonneg_left hmono hγ0.le
          have h3 : (k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ) ≤
              (k : ℝ) * (γ * (A : ℝ) ^ (γ - 1)) :=
            mul_le_mul_of_nonneg_left (le_trans hinc h2) hkpos.le
          linarith [h3, hslope]
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hmm : ((-1 : ℤ) : ℝ) = -1 := by norm_num
        rw [hmm]
        have e1 : -((k : ℝ) * ((n : ℝ) + 1) ^ γ) - -((k : ℝ) * (n : ℝ) ^ γ)
            = -((k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ)) := by ring
        rw [e1]
        linarith [hsmall, hδhalf])
      (by
        intro n hn1 hn2
        have hnA : A ≤ n := by omega
        have hn1' : (1 : ℕ) ≤ n := le_trans hA hnA
        have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
        have hnB : n + 1 ≤ B := by omega
        have hinc : γ * ((n : ℝ) + 1) ^ (γ - 1) ≤ ((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ := by
          have hstep := (rpow_step_sandwich hγ0 hγ1 (a := (n : ℝ)) (b := (n : ℝ) + 1)
            hnr (by linarith)).1
          rwa [show (n : ℝ) + 1 - (n : ℝ) = (1 : ℝ) by ring, mul_one] at hstep
        have hnb : ((n : ℝ) + 1) ≤ (B : ℝ) := by exact_mod_cast hnB
        have hmono : (B : ℝ) ^ (γ - 1) ≤ ((n : ℝ) + 1) ^ (γ - 1) :=
          rpow_mono_of_neg_exp (by linarith) (by linarith) hnb
        have hbig : (k : ℝ) * γ * (B : ℝ) ^ (γ - 1) ≤
            (k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ) := by
          have h1 : γ * (B : ℝ) ^ (γ - 1) ≤ ((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ := by
            have h2 : γ * (B : ℝ) ^ (γ - 1) ≤ γ * ((n : ℝ) + 1) ^ (γ - 1) :=
              mul_le_mul_of_nonneg_left hmono hγ0.le
            linarith [h2, hinc]
          have h2 : (k : ℝ) * (γ * (B : ℝ) ^ (γ - 1)) ≤
              (k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ) :=
            mul_le_mul_of_nonneg_left h1 hkpos.le
          linarith [h2]
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hmm : ((-1 : ℤ) : ℝ) = -1 := by norm_num
        rw [hmm]
        have e1 : -((k : ℝ) * ((n : ℝ) + 1) ^ γ) - -((k : ℝ) * (n : ℝ) ^ γ)
            = -((k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ)) := by ring
        rw [e1]
        linarith [hbig])
      (by
        intro n hn1 hn2
        have hnA : A ≤ n := by omega
        have hn1' : (1 : ℕ) ≤ n := le_trans hA hnA
        have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
        have hmono := rpow_incr_anti hγ0 hγ1 hnr
        have hknn : (0 : ℝ) ≤ (k : ℝ) := by positivity
        have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 1 + 1 := by push_cast; ring
        rw [hcast1, hcast2]
        have e1 : -((k : ℝ) * ((n : ℝ) + 1) ^ γ) - -((k : ℝ) * (n : ℝ) ^ γ)
            = -((k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ)) := by ring
        have e2 : -((k : ℝ) * ((n : ℝ) + 1 + 1) ^ γ) - -((k : ℝ) * ((n : ℝ) + 1) ^ γ)
            = -((k : ℝ) * (((n : ℝ) + 1 + 1) ^ γ - ((n : ℝ) + 1) ^ γ)) := by ring
        rw [e1, e2]
        have hmono' : ((n : ℝ) + 1 + 1) ^ γ - ((n : ℝ) + 1) ^ γ ≤
            ((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ := by
          convert hmono using 2 <;> ring
        have h2 : (k : ℝ) * (((n : ℝ) + 1 + 1) ^ γ - ((n : ℝ) + 1) ^ γ) ≤
            (k : ℝ) * (((n : ℝ) + 1) ^ γ - (n : ℝ) ^ γ) :=
          mul_le_mul_of_nonneg_left hmono' hknn
        linarith [h2])
    refine hmain.trans ?_
    have hBN' : (B : ℝ) ≤ (N : ℝ) := by exact_mod_cast hBN
    have hpow : (B : ℝ) ^ (1 - γ) ≤ (N : ℝ) ^ (1 - γ) :=
      Real.rpow_le_rpow hBpos.le hBN' (by linarith)
    have hden : (0 : ℝ) < (k : ℝ) * γ := mul_pos hkpos hγ0
    have hδeq : 1 / ((k : ℝ) * γ * (B : ℝ) ^ (γ - 1)) =
        (B : ℝ) ^ (1 - γ) / ((k : ℝ) * γ) := by
      have hBne : (B : ℝ) ^ (γ - 1) ≠ 0 := (Real.rpow_pos_of_pos hBpos _).ne'
      have hkey : (B : ℝ) ^ (1 - γ) = ((B : ℝ) ^ (γ - 1))⁻¹ := by
        rw [← Real.rpow_neg hBpos.le]
        congr 1
        ring
      rw [hkey]
      field_simp
    rw [hδeq]
    calc (B : ℝ) ^ (1 - γ) / ((k : ℝ) * γ) ≤ (N : ℝ) ^ (1 - γ) / ((k : ℝ) * γ) :=
          div_le_div_of_nonneg_right hpow hden.le
      _ = 1 / γ * (N : ℝ) ^ (1 - γ) * (k : ℝ)⁻¹ := by
          field_simp

/-! ### Threshold for the dyadic split -/

/-- At `T = ceil ((2 k γ)^(1/(1-γ)))` the phase slope is at most `1/2`. -/
private theorem threshold_slope_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {k : ℕ} (hk : 1 ≤ k)
    (T : ℕ) (hT1 : 1 ≤ T)
    (hT : ((2 * (k:ℝ) * γ) : ℝ) ^ (1 / (1 - γ)) ≤ (T : ℝ)) :
    (k:ℝ) * γ * (T:ℝ) ^ (γ - 1) ≤ 1 / 2 := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hbase : (0:ℝ) < 2 * (k:ℝ) * γ := by nlinarith
  set a : ℝ := (2 * (k:ℝ) * γ) ^ (1 / (1 - γ)) with hadef
  have hT0 : (0:ℝ) < (T:ℝ) := by
    have : (0:ℝ) < (T:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hT1)
    exact this
  have hpow : (2 * (k:ℝ) * γ) ≤ (T:ℝ) ^ (1 - γ) := by
    have h1 : a ^ (1 - γ) ≤ (T:ℝ) ^ (1 - γ) :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hbase _)) hT (by linarith)
    have h2 : a ^ (1 - γ) = 2 * (k:ℝ) * γ := by
      rw [hadef, ← Real.rpow_mul (le_of_lt hbase)]
      have h3 : (1 / (1 - γ)) * (1 - γ) = 1 := one_div_mul_cancel (sub_pos.mpr hγ1).ne'
      rw [h3, Real.rpow_one]
    rw [← h2]; exact h1
  have hneg : (T:ℝ) ^ (γ - 1) = ((T:ℝ) ^ (1 - γ))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt hT0)]
    congr 1; ring
  have hpos : (0:ℝ) < (T:ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos hT0 _
  rw [hneg]
  have h2 : (k:ℝ) * γ * ((T:ℝ) ^ (1 - γ))⁻¹ ≤ (k:ℝ) * γ * (2 * (k:ℝ) * γ)⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact inv_anti₀ hbase hpow
  refine h2.trans ?_
  have hkk : (k:ℝ) * γ * (2 * (k:ℝ) * γ)⁻¹ = 1 / 2 := by
    field_simp
  rw [hkk]

/-- Below `T` the phase slope is bigger than `1/2`. -/
private theorem half_lt_slope_of_lt {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {k : ℕ} (hk : 1 ≤ k)
    (T : ℕ) (hT : (T:ℝ) - 1 < ((2 * (k:ℝ) * γ) : ℝ) ^ (1 / (1 - γ)))
    {x : ℕ} (hx : 1 ≤ x) (hxT : x < T) :
    1 / 2 < (k:ℝ) * γ * (x:ℝ) ^ (γ - 1) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hbase : (0:ℝ) < 2 * (k:ℝ) * γ := by nlinarith
  set a : ℝ := (2 * (k:ℝ) * γ) ^ (1 / (1 - γ)) with hadef
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlt : (x:ℝ) < a := by
    have h1 : (x:ℝ) ≤ (T:ℝ) - 1 := by
      have h2 : x + 1 ≤ T := hxT
      have h3 : ((x:ℝ) + 1) ≤ (T:ℝ) := by exact_mod_cast h2
      linarith
    linarith
  have hpowlt : (x:ℝ) ^ (1 - γ) < a ^ (1 - γ) :=
    Real.rpow_lt_rpow (le_of_lt hxpos) hlt (by linarith)
  have heq : a ^ (1 - γ) = 2 * (k:ℝ) * γ := by
    rw [hadef, ← Real.rpow_mul (le_of_lt hbase)]
    have h3 : (1 / (1 - γ)) * (1 - γ) = 1 := one_div_mul_cancel (sub_pos.mpr hγ1).ne'
    rw [h3, Real.rpow_one]
  rw [heq] at hpowlt
  have hneg : (x:ℝ) ^ (γ - 1) = ((x:ℝ) ^ (1 - γ))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt hxpos)]
    congr 1; ring
  rw [hneg]
  have hx0 : (0:ℝ) < (x:ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos hxpos _
  have h2 : ((2 * (k:ℝ) * γ))⁻¹ < ((x:ℝ) ^ (1 - γ))⁻¹ := (inv_lt_inv₀ hbase hx0).2 hpowlt
  have h3 : (k:ℝ) * γ * ((2 * (k:ℝ) * γ))⁻¹ < (k:ℝ) * γ * ((x:ℝ) ^ (1 - γ))⁻¹ :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  have h4 : (k:ℝ) * γ * ((2 * (k:ℝ) * γ))⁻¹ = 1 / 2 := by field_simp
  linarith [h3, h4]


/-- `√(k γ (1-γ) B^(γ-2)) = √(γ (1-γ) k) · B^(γ/2-1)`. -/
private theorem sqrt_lam_eq {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {k : ℕ} (hk : 1 ≤ k)
    {B : ℕ} (hB1 : 1 ≤ B) :
    Real.sqrt ((k:ℝ) * γ * (1 - γ) * (B:ℝ) ^ (γ - 2)) =
      Real.sqrt (γ * (1 - γ) * (k:ℝ)) * (B:ℝ) ^ (γ/2 - 1) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hBpos : (0:ℝ) < (B:ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hB1)
  have hsq : (B:ℝ) ^ (γ - 2) = ((B:ℝ) ^ (γ/2 - 1)) ^ 2 := by
    rw [show ((B:ℝ) ^ (γ/2 - 1)) ^ 2 = ((B:ℝ) ^ (γ/2 - 1)) ^ (2:ℝ)
      from (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_mul hBpos.le]
    congr 1; ring
  have hc : (0:ℝ) ≤ γ * (1 - γ) * (k:ℝ) := by positivity
  have hU0 : (0:ℝ) ≤ (B:ℝ) ^ (γ/2 - 1) := (Real.rpow_pos_of_pos hBpos _).le
  rw [hsq]
  rw [show (k:ℝ) * γ * (1 - γ) * ((B:ℝ) ^ (γ/2 - 1)) ^ 2
      = (γ * (1 - γ) * (k:ℝ)) * ((B:ℝ) ^ (γ/2 - 1)) ^ 2 by ring]
  rw [Real.sqrt_mul hc]
  congr 1
  exact Real.sqrt_sq hU0

set_option maxHeartbeats 1000000 in
/-- A single dyadic block `[A, B]` with `B ≤ 2 A`, `1 ≤ A ≤ B` and phase slope at least `1/2`
at `A`: van der Corput's second derivative test gives `KB √k A^(γ/2)`, `KB = 16 + 64 √(γ/(1-γ))`. -/
private theorem block_vdC {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {k : ℕ} (hk : 1 ≤ k) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hB2A : B ≤ 2 * A)
    (hslope : 1 / 2 ≤ (k:ℝ) * γ * (A:ℝ) ^ (γ - 1)) :
    ‖∑ x ∈ Finset.Ico A B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖ ≤
      (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hA)
  have hgl : (0:ℝ) < γ * (1 - γ) := by nlinarith
  have hsqk : Real.sqrt (k:ℝ) * Real.sqrt (k:ℝ) = (k:ℝ) := Real.mul_self_sqrt hkpos.le
  have hsqksq : Real.sqrt (k:ℝ) ^ 2 = (k:ℝ) := by rw [sq, hsqk]
  have hsqA2 : ((A:ℝ) ^ (γ/2 - 1)) ^ 2 = (A:ℝ) ^ (γ - 2) := by
    rw [show ((A:ℝ)^(γ/2-1))^2 = ((A:ℝ)^(γ/2-1))^(2:ℝ) from (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_mul hApos.le]
    congr 1; ring
  have hAid : (A:ℝ) * (A:ℝ) ^ (γ/2 - 1) = (A:ℝ) ^ (γ/2) := by
    have h1 := Real.rpow_add hApos (1:ℝ) (γ/2 - 1)
    rw [Real.rpow_one, show (1:ℝ) + (γ/2 - 1) = γ/2 by ring] at h1
    exact h1.symm
  have hsqrtpos : (0:ℝ) < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hkpos
  by_cases hBA : B ≤ A
  · rw [Finset.Ico_eq_empty_of_le hBA]
    simp only [Finset.sum_empty, norm_zero]
    have h1 : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
    have h2 : (0:ℝ) ≤ (A:ℝ) ^ (γ/2) := (Real.rpow_pos_of_pos hApos _).le
    positivity
  · have hAlt : A < B := lt_of_not_ge hBA
    have hB1 : 1 ≤ B := le_trans hA (le_of_lt hAlt)
    have hBpos : (0:ℝ) < (B:ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hB1)
    have hABr : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast le_of_lt hAlt
    have hB2Ar : (B:ℝ) ≤ 2 * (A:ℝ) := by
      have h : ((B:ℕ):ℝ) ≤ ((2*A:ℕ):ℝ) := by exact_mod_cast hB2A
      push_cast at h; linarith
    -- `A^(γ-2) ≤ 4 B^(γ-2)`
    have hA4B : (A:ℝ) ^ (γ - 2) ≤ 4 * (B:ℝ) ^ (γ - 2) := by
      have ht4 : (2:ℝ) ^ (2 - γ) ≤ 4 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (show (2:ℝ) - γ ≤ 2 by linarith)
        rwa [show ((2:ℝ)) ^ (2:ℝ) = 4 by rw [Real.rpow_two]; norm_num] at h
      have htp : (2:ℝ) ^ (2 - γ) * (2:ℝ) ^ (γ - 2) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        norm_num
      have hpA : (2:ℝ) ^ (γ - 2) * (A:ℝ) ^ (γ - 2) = ((2:ℝ) * (A:ℝ)) ^ (γ - 2) :=
        (Real.mul_rpow (by norm_num) hApos.le).symm
      have h2A : ((2:ℝ) * (A:ℝ)) ^ (γ - 2) ≤ (B:ℝ) ^ (γ - 2) :=
        rpow_mono_of_neg_exp (by linarith) (by linarith) hB2Ar
      have ht0 : (0:ℝ) < (2:ℝ) ^ (2 - γ) := Real.rpow_pos_of_pos (by norm_num) _
      have hq0 : (0:ℝ) < (A:ℝ) ^ (γ - 2) := Real.rpow_pos_of_pos hApos _
      have hr0 : (0:ℝ) < (B:ℝ) ^ (γ - 2) := Real.rpow_pos_of_pos hBpos _
      have hpq : (A:ℝ) ^ (γ - 2) = (2:ℝ) ^ (2 - γ) * ((2:ℝ) ^ (γ - 2) * (A:ℝ) ^ (γ - 2)) := by
        rw [← mul_assoc, htp, one_mul]
      rw [hpq]
      calc (2:ℝ) ^ (2 - γ) * ((2:ℝ) ^ (γ - 2) * (A:ℝ) ^ (γ - 2))
          ≤ (2:ℝ) ^ (2 - γ) * (B:ℝ) ^ (γ - 2) :=
            mul_le_mul_of_nonneg_left (by rw [hpA]; exact h2A) ht0.le
        _ ≤ 4 * (B:ℝ) ^ (γ - 2) := mul_le_mul_of_nonneg_right ht4 hr0.le
    set lam : ℝ := (k:ℝ) * γ * (1 - γ) * (B:ℝ) ^ (γ - 2) with hlam
    have hBex : (0:ℝ) < (B:ℝ) ^ (γ - 2) := Real.rpow_pos_of_pos hBpos _
    have hlam0 : (0:ℝ) < lam := by
      rw [hlam]
      have : (0:ℝ) < (k:ℝ) * γ * (1 - γ) := by positivity
      exact mul_pos this hBex
    -- second differences of `f m = -k m^γ`
    have h2nd : ∀ n : ℕ, A - 1 < n → n < B - 1 →
        lam ≤ ((fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1 + 1)
            - (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1))
          - ((fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1)
            - (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) n) ∧
        ((fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1 + 1)
            - (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1))
          - ((fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1)
            - (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) n) ≤ 4 * lam := by
      intro n hn1 hn2
      have hnA : A ≤ n := by omega
      have hnB : n + 2 ≤ B := by omega
      have hn1' : 1 ≤ n := le_trans hA hnA
      have hnr : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1'
      obtain ⟨hlo, hhi⟩ := rpow_second_diff_sandwich hγ0 hγ1 hnr
      set S : ℝ := 2 * ((n:ℝ) + 1) ^ γ - (n:ℝ) ^ γ - ((n:ℝ) + 2) ^ γ with hS
      have hn2B : ((n:ℝ) + 2) ≤ (B:ℝ) := by
        have h : ((n + 2 : ℕ) : ℝ) ≤ (B:ℝ) := by exact_mod_cast hnB
        push_cast at h; linarith
      have hBle : (B:ℝ) ^ (γ - 2) ≤ ((n:ℝ) + 2) ^ (γ - 2) :=
        rpow_mono_of_neg_exp (by linarith) (by linarith) hn2B
      have hAn : (A:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnA
      have hnA2 : (n:ℝ) ^ (γ - 2) ≤ (A:ℝ) ^ (γ - 2) :=
        rpow_mono_of_neg_exp (by linarith) hApos hAn
      have e1 : (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1 + 1)
          - (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1)
          - ((fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) (n + 1)
            - (fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ)) n) = (k:ℝ) * S := by
        simp only []
        have c1 : (((n + 1 + 1 : ℕ)) : ℝ) = (n:ℝ) + 1 + 1 := by push_cast; ring
        have c2 : (((n + 1 : ℕ)) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
        rw [c1, c2, hS]; ring
      constructor
      · rw [e1, hlam]
        have h1 : γ * (1 - γ) * (B:ℝ) ^ (γ - 2) ≤ S := by
          rw [hS]
          exact le_trans (mul_le_mul_of_nonneg_left hBle hgl.le) hlo
        nlinarith [h1, hkpos]
      · rw [e1, hlam]
        have h1 : S ≤ γ * (1 - γ) * (A:ℝ) ^ (γ - 2) := by
          rw [hS]
          exact le_trans hhi (mul_le_mul_of_nonneg_left hnA2 hgl.le)
        have h2 : γ * (1 - γ) * (A:ℝ) ^ (γ - 2) ≤ 4 * (γ * (1 - γ) * (B:ℝ) ^ (γ - 2)) := by
          nlinarith [hA4B, hgl]
        nlinarith [h1, h2, hkpos]
    have hkey := vdC_second_derivative (f := fun m : ℕ => -((k:ℝ) * (m:ℝ) ^ γ))
      (a := A - 1) (b := B - 1) (lam := lam) (c := 4)
      (by omega) hlam0 (by norm_num)
      (fun n hn1 hn2 => (h2nd n hn1 hn2).1) (fun n hn1 hn2 => (h2nd n hn1 hn2).2)
    have hrange : Finset.Ioc (A - 1) (B - 1) = Finset.Ico A B := Ioc_pred_eq_Ico hA
    have eL : ‖∑ x ∈ Finset.Ico A B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖
        = ‖∑ n ∈ Finset.Ioc (A - 1) (B - 1), eK (-((k:ℝ) * (n:ℝ) ^ γ))‖ := by
      rw [hrange, norm_sum_eC_eq_neg_eK]
    rw [eL]
    refine hkey.trans ?_
    have hlen : ((B - 1 : ℕ) : ℝ) - ((A - 1 : ℕ) : ℝ) = (B:ℝ) - (A:ℝ) := by
      have h1 : ((B - 1 : ℕ) : ℝ) = (B:ℝ) - 1 := by
        rw [Nat.cast_sub hB1]; norm_num
      have h2 : ((A - 1 : ℕ) : ℝ) = (A:ℝ) - 1 := by
        rw [Nat.cast_sub hA]; norm_num
      linarith
    rw [hlen]
    -- `√lam = √(γ(1-γ)k) · B^(γ/2-1)`
    have hsq_lam : Real.sqrt lam = Real.sqrt (γ * (1 - γ) * (k:ℝ)) * (B:ℝ) ^ (γ/2 - 1) := by
      rw [hlam]; exact sqrt_lam_eq hγ0 hγ1 hk hB1
    have hBexne : (B:ℝ) ^ (γ/2 - 1) ≠ 0 := (Real.rpow_pos_of_pos hBpos _).ne'
    -- `A^(1-γ) ≤ 2 k γ`
    have hA1g : (A:ℝ) ^ (1 - γ) ≤ 2 * (k:ℝ) * γ := by
      have hstep : (1:ℝ) ≤ 2 * ((k:ℝ) * γ) * (A:ℝ) ^ (γ - 1) := by linarith
      have hpos := Real.rpow_pos_of_pos hApos (γ - 1)
      have hinv : ((A:ℝ) ^ (γ - 1))⁻¹ ≤ 2 * ((k:ℝ) * γ) := by
        have h2 := mul_le_mul_of_nonneg_right hstep (le_of_lt (inv_pos.mpr hpos))
        rwa [mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] at h2
      have hneg : (A:ℝ) ^ (1 - γ) = ((A:ℝ) ^ (γ - 1))⁻¹ := by
        rw [← Real.rpow_neg hApos.le]; congr 1; ring
      rw [hneg]
      calc ((A:ℝ) ^ (γ - 1))⁻¹ ≤ 2 * ((k:ℝ) * γ) := hinv
        _ = 2 * (k:ℝ) * γ := by ring
    have hA1 : (A:ℝ) ^ (1 - γ/2) ≤ 2 * (k:ℝ) * γ * (A:ℝ) ^ (γ/2) := by
      have hs : (A:ℝ) ^ (1 - γ/2) = (A:ℝ) ^ (1 - γ) * (A:ℝ) ^ (γ/2) := by
        rw [← Real.rpow_add hApos]; congr 1; ring
      rw [hs]
      exact mul_le_mul_of_nonneg_right hA1g (Real.rpow_pos_of_pos hApos _).le
    -- `√lam ≤ (1/2) √k A^(γ/2-1)`
    have hsqrtle : Real.sqrt lam ≤ (1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1) := by
      have hsq : lam ≤ ((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1)) ^ 2 := by
        rw [hlam]
        have hBle : (B:ℝ) ^ (γ - 2) ≤ (A:ℝ) ^ (γ - 2) :=
          rpow_mono_of_neg_exp (by linarith) hApos hABr
        have hq : γ * (1 - γ) ≤ 1 / 4 := by nlinarith [sq_nonneg (γ - 1/2)]
        have hsq2 : ((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1)) ^ 2
            = (1/4) * (k:ℝ) * (A:ℝ) ^ (γ - 2) := by
          rw [mul_pow, mul_pow, hsqA2, hsqksq]
          norm_num
        rw [hsq2]
        have hr := Real.rpow_pos_of_pos hApos (γ - 2)
        have hkb : (0:ℝ) ≤ (k:ℝ) := hkpos.le
        have hBpos' : (0:ℝ) < (B:ℝ) ^ (γ - 2) := Real.rpow_pos_of_pos hBpos _
        calc (k:ℝ) * γ * (1 - γ) * (B:ℝ) ^ (γ - 2)
            ≤ (k:ℝ) * (1 / 4) * (B:ℝ) ^ (γ - 2) := by
              have h1 : γ * (1 - γ) ≤ 1 / 4 := hq
              have h2 : (k:ℝ) * (γ * (1 - γ)) ≤ (k:ℝ) * (1 / 4) :=
                mul_le_mul_of_nonneg_left h1 hkb
              nlinarith [h2, hBpos'.le]
          _ ≤ (k:ℝ) * (1 / 4) * (A:ℝ) ^ (γ - 2) := by
              have h1 : (0:ℝ) ≤ (k:ℝ) * (1/4) := by positivity
              exact mul_le_mul_of_nonneg_left hBle h1
          _ = 1 / 4 * (k:ℝ) * (A:ℝ) ^ (γ - 2) := by ring
      calc Real.sqrt lam ≤ Real.sqrt (((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1)) ^ 2) :=
            Real.sqrt_le_sqrt hsq
        _ = (1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1) := by
            rw [Real.sqrt_sq (by positivity)]
    have hL1 : 32 * ((B:ℝ) - (A:ℝ)) * Real.sqrt lam
        ≤ 16 * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := by
      have h0 : (0:ℝ) ≤ (B:ℝ) - (A:ℝ) := by linarith
      have hBA : (B:ℝ) - (A:ℝ) ≤ (A:ℝ) := by linarith
      have h1 : 32 * ((B:ℝ) - (A:ℝ)) * Real.sqrt lam
          ≤ 32 * (A:ℝ) * ((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1)) := by
        have h3 : (0:ℝ) ≤ 32 * ((B:ℝ) - (A:ℝ)) := by linarith
        have := mul_le_mul_of_nonneg_left hsqrtle h3
        calc 32 * ((B:ℝ) - (A:ℝ)) * Real.sqrt lam
            ≤ 32 * ((B:ℝ) - (A:ℝ)) * ((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1)) := this
          _ ≤ 32 * (A:ℝ) * ((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1)) := by
              have h4 : (0:ℝ) ≤ (1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1) := by positivity
              nlinarith [hBA, h4, h0]
      have h2 : 32 * (A:ℝ) * ((1/2) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2 - 1))
          = 16 * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := by
        rw [← hAid]; ring
      linarith [h1, h2.le, h2.ge]
    -- `B^(1-γ/2) ≤ 4 k γ A^(γ/2)`
    have hB1g : (B:ℝ) ^ (1 - γ/2) ≤ 4 * (k:ℝ) * γ * (A:ℝ) ^ (γ/2) := by
      have h1 : (B:ℝ) ^ (1 - γ/2) ≤ ((2:ℝ) * (A:ℝ)) ^ (1 - γ/2) :=
        Real.rpow_le_rpow hBpos.le hB2Ar (by linarith)
      have h3 : ((2:ℝ) * (A:ℝ)) ^ (1 - γ/2)
          = (2:ℝ) ^ (1 - γ/2) * (A:ℝ) ^ (1 - γ/2) :=
        Real.mul_rpow (by norm_num) hApos.le
      rw [h3] at h1
      have h4 : (2:ℝ) ^ (1 - γ/2) ≤ 2 := by
        have h5 : (2:ℝ) ^ (1 - γ/2) ≤ (2:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)
        rwa [Real.rpow_one] at h5
      have hA20 : (0:ℝ) ≤ (A:ℝ) ^ (1 - γ/2) := (Real.rpow_pos_of_pos hApos _).le
      have h6 : (2:ℝ) ^ (1 - γ/2) * (A:ℝ) ^ (1 - γ/2) ≤ 2 * (A:ℝ) ^ (1 - γ/2) := by
        nlinarith [h4, hA20]
      have h9 : 2 * (A:ℝ) ^ (1 - γ/2) ≤ 2 * (2 * (k:ℝ) * γ * (A:ℝ) ^ (γ/2)) := by
        nlinarith [hA1]
      linarith [h1, h6, h9]
    have hBinv : (B:ℝ) ^ (γ/2 - 1) = ((B:ℝ) ^ (1 - γ/2))⁻¹ := by
      rw [← Real.rpow_neg hBpos.le]; congr 1; ring
    have hsqrtk : Real.sqrt (γ * (1 - γ) * (k:ℝ)) = Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ) := by
      rw [Real.sqrt_mul hgl.le]
    have hprod : Real.sqrt (γ / (1 - γ)) * Real.sqrt (γ * (1 - γ)) = γ := by
      rw [← Real.sqrt_mul (show (0:ℝ) ≤ γ / (1 - γ) by positivity)]
      rw [show γ / (1 - γ) * (γ * (1 - γ)) = γ ^ 2 by
        have hne : (1 - γ) ≠ 0 := (sub_pos.mpr hγ1).ne'
        field_simp]
      exact Real.sqrt_sq hγ0.le
    have hsqprod : Real.sqrt (γ * (1 - γ)) * Real.sqrt (γ / (1 - γ)) = γ := by
      rw [mul_comm]; exact hprod
    -- the `1/√lam` piece
    have hL2 : 8 / Real.sqrt lam
        ≤ 64 * Real.sqrt (γ / (1 - γ)) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := by
      have hid : 64 * Real.sqrt (γ / (1 - γ)) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
            * (Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ))
          = 64 * γ * (k:ℝ) * (A:ℝ) ^ (γ/2) := by
        calc 64 * Real.sqrt (γ / (1 - γ)) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
              * (Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ))
            = 64 * (Real.sqrt (γ / (1 - γ)) * Real.sqrt (γ * (1 - γ)))
              * (Real.sqrt (k:ℝ) * Real.sqrt (k:ℝ)) * (A:ℝ) ^ (γ/2) := by ring
          _ = 64 * γ * (k:ℝ) * (A:ℝ) ^ (γ/2) := by rw [hprod, hsqk]
      have hstep : 8 * (B:ℝ) ^ (1 - γ/2)
          ≤ 64 * Real.sqrt (γ / (1 - γ)) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
            * (Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ)) := by
        rw [hid]
        have hgp : (0:ℝ) ≤ (k:ℝ) * γ * (A:ℝ) ^ (γ/2) := by positivity
        nlinarith [hB1g, hgp]
      have hden : (0:ℝ) < Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ) := by positivity
      rw [hsq_lam, hsqrtk, hBinv]
      rw [show 8 / (Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ) * ((B:ℝ) ^ (1 - γ/2))⁻¹)
          = 8 * (B:ℝ) ^ (1 - γ/2) / (Real.sqrt (γ * (1 - γ)) * Real.sqrt (k:ℝ)) by
        field_simp]
      rw [div_le_iff₀ hden]
      linarith [hstep]
    calc 8 * (4 * ((B:ℝ) - (A:ℝ)) * Real.sqrt lam + 1 / Real.sqrt lam)
        = 32 * ((B:ℝ) - (A:ℝ)) * Real.sqrt lam + 8 / Real.sqrt lam := by ring
      _ ≤ 16 * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
            + 64 * Real.sqrt (γ / (1 - γ)) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := add_le_add hL1 hL2
      _ = (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := by ring

/-! ### The dyadic chain -/

private lemma geom_step {q : ℝ} (hq : 1 < q) (m : ℕ) :
    1 + q * ((q^m - 1) / (q - 1)) = (q^(m+1) - 1) / (q - 1) := by
  have hq1 : q - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

private lemma geom_ge_one {q : ℝ} (hq : 1 < q) (m : ℕ) :
    1 ≤ (q^(m+1) - 1) / (q - 1) := by
  rw [le_div_iff₀ (by linarith : (0:ℝ) < q - 1)]
  have h1 : q ^ 1 ≤ q ^ (m+1) := pow_le_pow_right₀ hq.le (by omega)
  rw [pow_one] at h1
  linarith

private lemma geom_cast_succ {q : ℝ} (hq : 1 < q) (m : ℕ) :
    (q : ℝ) ^ (m+1) = q ^ m * q := by ring

/-- Dyadic chain: summing van der Corput's block bound over the chain
`A, 2A, 4A, ...` up to `B` costs the partial geometric sum. -/
private theorem chain_bound {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {k : ℕ} (hk : 1 ≤ k) {T : ℕ}
    (hslope : ∀ x : ℕ, 1 ≤ x → x < T → 1 / 2 ≤ (k:ℝ) * γ * (x:ℝ) ^ (γ - 1)) :
    ∀ (m : ℕ) (A B : ℕ), 1 ≤ A → A ≤ B → B ≤ T → (B:ℝ) ≤ (2:ℝ)^m * (A:ℝ) →
      ‖∑ x ∈ Finset.Ico A B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖ ≤
        (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
          * ((((2:ℝ) ^ (γ/2)) ^ m - 1) / ((2:ℝ) ^ (γ/2) - 1)) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hq : (1:ℝ) < (2:ℝ) ^ (γ/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq0 : (0:ℝ) < (2:ℝ) ^ (γ/2) - 1 := by linarith
  have hKB : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
  intro m
  induction m with
  | zero =>
    intro A B hA hAB hBT h2
    have hBA : B ≤ A := by
      have h3 : (B:ℝ) ≤ (A:ℝ) := by simpa using h2
      exact_mod_cast h3
    have hBeq : B = A := le_antisymm hBA hAB
    rw [hBeq, Finset.Ico_self, Finset.sum_empty, norm_zero]
    have h0 : (((2:ℝ) ^ (γ/2)) ^ 0 - 1) = 0 := by simp
    rw [h0, zero_div, mul_zero]
  | succ m ih =>
    intro A B hA hAB hBT h2
    have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hA)
    have h3A : (0:ℝ) ≤ (A:ℝ) ^ (γ/2) := (Real.rpow_pos_of_pos hApos _).le
    have h2k : (0:ℝ) ≤ Real.sqrt (k:ℝ) := Real.sqrt_nonneg _
    rcases eq_or_lt_of_le hAB with heq | hAlt
    · rw [← heq, Finset.Ico_self, Finset.sum_empty, norm_zero]
      have hge := geom_ge_one hq m
      have h5 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) :=
        mul_nonneg (mul_nonneg hKB h2k) h3A
      have h6 : (0:ℝ) ≤ (((2:ℝ) ^ (γ/2)) ^ (m+1) - 1) / ((2:ℝ) ^ (γ/2) - 1) :=
        le_trans (by norm_num) hge
      exact mul_nonneg h5 h6
    · have hAT : A < T := lt_of_lt_of_le hAlt hBT
      by_cases hB2A : B ≤ 2 * A
      · have hblock := block_vdC (γ := γ) (k := k) (A := A) (B := B) hγ0 hγ1 hk hA hAB hB2A
          (hslope A hA hAT)
        refine hblock.trans ?_
        have hge := geom_ge_one hq m
        have h5 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) :=
          mul_nonneg (mul_nonneg hKB h2k) h3A
        have h6 : (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
            ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
              * ((((2:ℝ) ^ (γ/2)) ^ (m+1) - 1) / ((2:ℝ) ^ (γ/2) - 1)) := by
          calc (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
              = (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) * 1 := by ring
            _ ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
                * ((((2:ℝ) ^ (γ/2)) ^ (m+1) - 1) / ((2:ℝ) ^ (γ/2) - 1)) :=
                mul_le_mul_of_nonneg_left hge h5
        exact h6
      · rw [not_le] at hB2A
        have hA2T : 2 * A ≤ T := by omega
        have hA2B : 2 * A ≤ B := le_of_lt hB2A
        have hA2pos : (1:ℕ) ≤ 2 * A := by omega
        have hblock := block_vdC (γ := γ) (k := k) (A := A) (B := 2 * A) hγ0 hγ1 hk hA
          (by omega : A ≤ 2 * A) (by omega : 2 * A ≤ 2 * A) (hslope A hA hAT)
        have hIH : (B:ℝ) ≤ (2:ℝ)^m * ((2 * A : ℕ) : ℝ) := by
          have hc : ((2 * A : ℕ) : ℝ) = 2 * (A:ℝ) := by push_cast; ring
          rw [hc]
          calc (B:ℝ) ≤ (2:ℝ)^(m+1) * (A:ℝ) := h2
            _ = (2:ℝ)^m * (2 * (A:ℝ)) := by ring
        have hrest := ih (2 * A) B hA2pos hA2B hBT hIH
        have hsplit : ‖∑ x ∈ Finset.Ico A B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖
            ≤ ‖∑ x ∈ Finset.Ico A (2*A), eC ((k:ℝ) * (x:ℝ) ^ γ)‖
              + ‖∑ x ∈ Finset.Ico (2*A) B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖ := by
          have h1 : Finset.Ico A B = Finset.Ico A (2*A) ∪ Finset.Ico (2*A) B := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
          rw [h1, Finset.sum_union (by
            simp only [Finset.disjoint_left, Finset.mem_Ico]; omega)]
          exact norm_add_le _ _
        have hA2 : ((2 * A : ℕ) : ℝ) ^ (γ/2) = (2:ℝ)^(γ/2) * (A:ℝ)^(γ/2) := by
          have hc : ((2 * A : ℕ) : ℝ) = 2 * (A:ℝ) := by push_cast; ring
          rw [hc, Real.mul_rpow (by norm_num) hApos.le]
        -- the two pieces, both measured in `KB √k A^(γ/2)`
        have e2 : ‖∑ x ∈ Finset.Ico (2*A) B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖
            ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
              * ((2:ℝ)^(γ/2) * ((((2:ℝ) ^ (γ/2)) ^ m - 1) / ((2:ℝ) ^ (γ/2) - 1))) := by
          rw [hA2] at hrest
          refine hrest.trans (le_of_eq ?_)
          ring
        refine hsplit.trans ?_
        have e1 : ‖∑ x ∈ Finset.Ico A (2*A), eC ((k:ℝ) * (x:ℝ) ^ γ)‖
            ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2) := hblock
        have hsum := add_le_add e1 e2
        refine hsum.trans ?_
        set Y : ℝ := (((2:ℝ) ^ (γ/2)) ^ m - 1) / ((2:ℝ) ^ (γ/2) - 1) with hY
        have hstep : 1 + (2:ℝ)^(γ/2) * Y
            = ((((2:ℝ) ^ (γ/2)) ^ (m+1) - 1) / ((2:ℝ) ^ (γ/2) - 1)) := by
          rw [hY]; exact geom_step hq m
        have hfinal : (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
              + (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
                * ((2:ℝ)^(γ/2) * ((((2:ℝ) ^ (γ/2)) ^ m - 1) / ((2:ℝ) ^ (γ/2) - 1)))
            = (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
              * ((((2:ℝ) ^ (γ/2)) ^ (m+1) - 1) / ((2:ℝ) ^ (γ/2) - 1)) := by
          rw [show (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
                + (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
                  * ((2:ℝ)^(γ/2) * Y)
              = (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
                * (1 + (2:ℝ)^(γ/2) * Y) from by ring, hstep]
        linarith [hfinal]

/-- Two consecutive powers of two bracketing `B` above `A`. -/
private theorem exists_dyadic {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) :
    ∃ m : ℕ, 1 ≤ m ∧ B ≤ A * 2^m ∧ A * 2^(m-1) < B := by
  have hex : ∃ m : ℕ, B ≤ A * 2^m := by
    refine ⟨B, ?_⟩
    calc B ≤ 2^B := le_of_lt (Nat.lt_two_pow_self (n := B))
      _ = 1 * 2^B := (one_mul _).symm
      _ ≤ A * 2^B := Nat.mul_le_mul_right _ hA
  set m := Nat.find hex with hmdef
  have hm : B ≤ A * 2^m := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero, mul_one] at hm; omega
    · exact h
  have hlt : A * 2^(m-1) < B := by
    have h2 : ¬ (B ≤ A * 2^(m-1)) := Nat.find_min hex (by omega)
    omega
  exact ⟨m, hm1, hm, hlt⟩

/-- `(2^(γ/2))^m = (2^m)^(γ/2)`. -/
private theorem qpow_eq {γ : ℝ} (m : ℕ) :
    ((2:ℝ)^(γ/2))^m = (((2:ℝ)^m))^(γ/2) := by
  rw [show ((2:ℝ)^(γ/2))^m = ((2:ℝ)^(γ/2))^(m:ℝ) from (Real.rpow_natCast _ m).symm]
  rw [show (((2:ℝ)^m))^(γ/2) = ((2:ℝ)^(m:ℝ))^(γ/2) from by rw [Real.rpow_natCast]]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1; ring

/-- The dyadic chain bound, in the form used by the interval estimate:
`KB q/(q-1) √k n^(γ/2)` whenever the top of the interval is at most `T`. -/
private theorem chain_top {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {k : ℕ} (hk : 1 ≤ k) {T n : ℕ}
    (hslope : ∀ x : ℕ, 1 ≤ x → x < T → 1 / 2 ≤ (k:ℝ) * γ * (x:ℝ) ^ (γ - 1))
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBT : B ≤ T) (hBn : B ≤ n) :
    ‖∑ x ∈ Finset.Ico A B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖ ≤
      (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
        * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hq : (1:ℝ) < (2:ℝ)^(γ/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq0 : (0:ℝ) < (2:ℝ)^(γ/2) - 1 := by linarith
  have hqpos : (0:ℝ) < (2:ℝ)^(γ/2) := by linarith
  have hKB : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
  have hn1 : 1 ≤ n := le_trans hA (le_trans hAB hBn)
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hA)
  rcases eq_or_lt_of_le hAB with heq | hlt
  · rw [← heq, Finset.Ico_self, Finset.sum_empty, norm_zero]
    positivity
  · obtain ⟨m, hm1, hmB, hmm⟩ := exists_dyadic hA hlt
    have hmB' : (B:ℝ) ≤ (2:ℝ)^m * (A:ℝ) := by
      have h : ((B:ℕ):ℝ) ≤ ((A * 2^m : ℕ):ℝ) := by exact_mod_cast hmB
      push_cast at h ⊢
      linarith
    have hchain := chain_bound hγ0 hγ1 hk (T := T) hslope m A B hA hAB hBT hmB'
    refine hchain.trans ?_
    -- drop the `-1`
    have hq1 : (1:ℝ) ≤ ((2:ℝ)^(γ/2))^m := one_le_pow₀ hq.le
    have hY : ((((2:ℝ)^(γ/2))^m - 1) / ((2:ℝ)^(γ/2) - 1))
        ≤ (((2:ℝ)^(γ/2))^m / ((2:ℝ)^(γ/2) - 1)) := by
      rw [div_le_div_iff_of_pos_right hq0]
      linarith
    have hstep : (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
          * ((((2:ℝ)^(γ/2))^m - 1) / ((2:ℝ)^(γ/2) - 1))
        ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
          * (((2:ℝ)^(γ/2))^m / ((2:ℝ)^(γ/2) - 1)) := by
      refine mul_le_mul_of_nonneg_left hY ?_
      positivity
    refine hstep.trans ?_
    -- `A^(γ/2) (2^(γ/2))^m = (A 2^m)^(γ/2) ≤ (2B)^(γ/2)`
    have h2m : (2:ℕ)^m = 2^(m-1) * 2 := by
      have h := Nat.pow_succ 2 (m-1)
      rw [show (m - 1).succ = m by omega] at h
      exact h
    have hAB2 : A * 2^m ≤ 2 * B := by
      calc A * 2^m = A * (2^(m-1) * 2) := by rw [h2m]
        _ = A * 2^(m-1) * 2 := by ring
        _ ≤ 2 * B := by omega
    have hcast : ((A * 2^m : ℕ) : ℝ) ≤ 2 * (B:ℝ) := by
      have : ((A * 2^m : ℕ) : ℝ) ≤ ((2 * B : ℕ) : ℝ) := by exact_mod_cast hAB2
      simpa using this
    have hAr : (A:ℝ) * (2:ℝ)^m = ((A * 2^m : ℕ) : ℝ) := by push_cast; ring
    have hBpow : ((A:ℝ) * (2:ℝ)^m) ^ (γ/2) ≤ ((2:ℝ) * (B:ℝ)) ^ (γ/2) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
      rw [hAr]; exact hcast
    have hexp : ((2:ℝ) * (B:ℝ)) ^ (γ/2) = (2:ℝ)^(γ/2) * (B:ℝ) ^ (γ/2) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have hkey : (A:ℝ) ^ (γ/2) * (((2:ℝ)^(γ/2))^m) = ((A:ℝ) * (2:ℝ)^m) ^ (γ/2) := by
      rw [qpow_eq m]
      rw [Real.mul_rpow (le_of_lt hApos) (by positivity)]
    have hmain : (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
          * (((2:ℝ)^(γ/2))^m / ((2:ℝ)^(γ/2) - 1))
        ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
      have hBle : (B:ℝ) ^ (γ/2) ≤ (n:ℝ) ^ (γ/2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
        exact_mod_cast hBn
      have h1 : (A:ℝ) ^ (γ/2) * (((2:ℝ)^(γ/2))^m) ≤ (2:ℝ)^(γ/2) * (B:ℝ) ^ (γ/2) := by
        rw [hkey]
        exact le_trans hBpow (le_of_eq hexp)
      have hstep1 : (16 + 64 * Real.sqrt (γ / (1 - γ))) * Real.sqrt (k:ℝ) * (A:ℝ) ^ (γ/2)
            * (((2:ℝ)^(γ/2))^m / ((2:ℝ)^(γ/2) - 1))
          = ((16 + 64 * Real.sqrt (γ / (1 - γ))) / ((2:ℝ)^(γ/2) - 1))
            * (Real.sqrt (k:ℝ) * ((A:ℝ) ^ (γ/2) * (((2:ℝ)^(γ/2))^m))) := by
        field_simp
      have hstep2 : ((16 + 64 * Real.sqrt (γ / (1 - γ))) / ((2:ℝ)^(γ/2) - 1))
            * (Real.sqrt (k:ℝ) * ((A:ℝ) ^ (γ/2) * (((2:ℝ)^(γ/2))^m)))
          ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) / ((2:ℝ)^(γ/2) - 1))
            * (Real.sqrt (k:ℝ) * ((2:ℝ)^(γ/2) * (n:ℝ) ^ (γ/2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hBle (by positivity)
      have hstep3 : ((16 + 64 * Real.sqrt (γ / (1 - γ))) / ((2:ℝ)^(γ/2) - 1))
            * (Real.sqrt (k:ℝ) * ((2:ℝ)^(γ/2) * (n:ℝ) ^ (γ/2)))
          = (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
            * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
        ring
      exact (le_of_eq hstep1).trans (hstep2.trans (le_of_eq hstep3))
    exact hmain

/-- The exponent-pair bound for one interval `[A, B] ⊆ [1, n]`, with an explicit constant. -/
private theorem interval_bound {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {k n A B : ℕ} (hk : 1 ≤ k) (hA : 1 ≤ A) (hAB : A ≤ B) (hBn : B ≤ n) :
    ‖∑ x ∈ Finset.Ico A B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖ ≤
      ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
        * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hn1 : 1 ≤ n := le_trans hA (le_trans hAB hBn)
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hq : (1:ℝ) < (2:ℝ)^(γ/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq0 : (0:ℝ) < (2:ℝ)^(γ/2) - 1 := by linarith
  have hKB : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
  -- the threshold
  set T := Nat.ceil ((2 * (k:ℝ) * γ) ^ (1 / (1 - γ))) with hTdef
  have hbase : (0:ℝ) < 2 * (k:ℝ) * γ := by positivity
  have hTpos : (0:ℝ) < (2 * (k:ℝ) * γ) ^ (1 / (1 - γ)) := Real.rpow_pos_of_pos hbase _
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Nat.ceil_pos.mpr hTpos
  have hTr : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT1
  have hT0 : (0:ℝ) < (T:ℝ) := by linarith
  have hTa : (2 * (k:ℝ) * γ) ^ (1 / (1 - γ)) ≤ (T:ℝ) := by
    rw [hTdef]; exact Nat.le_ceil _
  have hT2 : (T:ℝ) - 1 < (2 * (k:ℝ) * γ) ^ (1 / (1 - γ)) := by
    have h := Nat.ceil_lt_add_one (le_of_lt hTpos)
    rw [hTdef]
    have h2 : ((Nat.ceil ((2 * (k:ℝ) * γ) ^ (1 / (1 - γ))) : ℕ) : ℝ)
        < (2 * (k:ℝ) * γ) ^ (1 / (1 - γ)) + 1 := h
    linarith
  have hslopeT : (k:ℝ) * γ * (T:ℝ) ^ (γ - 1) ≤ 1 / 2 :=
    threshold_slope_le hγ0 hγ1 hk T hT1 hTa
  have hslope : ∀ x : ℕ, 1 ≤ x → x < T → 1 / 2 ≤ (k:ℝ) * γ * (x:ℝ) ^ (γ - 1) :=
    fun x hx hxT => le_of_lt (half_lt_slope_of_lt hγ0 hγ1 hk T hT2 hx hxT)
  have hK1 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) :=
    div_nonneg (mul_nonneg hKB (le_trans (by norm_num) (le_of_lt hq))) hq0.le
  have hC0 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
      + 1 / γ := add_nonneg hK1 (by positivity)
  have hsqk : (0:ℝ) ≤ Real.sqrt (k:ℝ) := Real.sqrt_nonneg _
  have hnpow : (0:ℝ) ≤ (n:ℝ) ^ (γ/2) := (Real.rpow_pos_of_pos hnpos _).le
  have hn1g : (0:ℝ) ≤ (n:ℝ) ^ (1 - γ) := (Real.rpow_pos_of_pos hnpos _).le
  have hkinv : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
  by_cases hBT : B ≤ T
  · have hch := chain_top hγ0 hγ1 hk hslope hA hAB hBT hBn
    refine hch.trans ?_
    have h1 : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
        * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2))
        ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
      have h0 : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) := mul_nonneg hsqk hnpow
      have hle : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
          ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ :=
        le_add_of_nonneg_right (by positivity)
      exact mul_le_mul_of_nonneg_right hle h0
    refine h1.trans ?_
    have h2 : ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2))
        ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
      have h3 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := mul_nonneg hkinv hn1g
      exact mul_le_mul_of_nonneg_left (by linarith) hC0
    exact h2
  · rw [not_le] at hBT
    have hBTle : T ≤ B := le_of_lt hBT
    have hTn : T ≤ n := le_trans hBTle hBn
    -- cut at `T' = max A T`
    set T' := max A T with hT'def
    have hAT' : A ≤ T' := le_max_left _ _
    have hTT' : T ≤ T' := le_max_right _ _
    have hT'B : T' ≤ B := max_le hAB (le_of_lt hBT)
    have hT'1 : 1 ≤ T' := le_trans hA hAT'
    have hT'n : T' ≤ n := le_trans hT'B hBn
    have hT'r1 : (1:ℝ) ≤ (T':ℝ) := by exact_mod_cast hT'1
    have hT'pos : (0:ℝ) < (T':ℝ) := by linarith
    have hslopeT' : (k:ℝ) * γ * (T':ℝ) ^ (γ - 1) ≤ 1 / 2 := by
      have hle : (T:ℝ) ≤ (T':ℝ) := by exact_mod_cast hTT'
      have hmono : (T':ℝ) ^ (γ - 1) ≤ (T:ℝ) ^ (γ - 1) :=
        rpow_mono_of_neg_exp (by linarith) hT0 hle
      have hkg : (0:ℝ) ≤ (k:ℝ) * γ := by positivity
      have h1 := mul_le_mul_of_nonneg_left hmono hkg
      linarith [h1, hslopeT]
    have hsplit : Finset.Ico A B = Finset.Ico A T' ∪ Finset.Ico T' B := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    rw [hsplit, Finset.sum_union (by
      simp only [Finset.disjoint_left, Finset.mem_Ico]; omega)]
    refine (norm_add_le _ _).trans ?_
    -- first piece: dyadic chain up to `T`
    have hpiece1 : ‖∑ x ∈ Finset.Ico A T', eC ((k:ℝ) * (x:ℝ) ^ γ)‖
        ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
      rcases eq_or_lt_of_le hAT' with heq | hlt
      · rw [← heq, Finset.Ico_self, Finset.sum_empty, norm_zero]
        exact mul_nonneg hK1 (mul_nonneg hsqk hnpow)
      · have hT'eq : T' = T := by
          rcases le_or_gt A T with h | h
          · rw [hT'def, max_eq_right h]
          · exfalso
            rw [hT'def, max_eq_left (le_of_lt h)] at hlt
            omega
        rw [hT'eq]
        exact chain_top hγ0 hγ1 hk hslope hA (by omega : A ≤ T) le_rfl hTn
    -- second piece: flat at the left end
    have hpiece2 : ‖∑ x ∈ Finset.Ico T' B, eC ((k:ℝ) * (x:ℝ) ^ γ)‖
        ≤ 1 / γ * (n:ℝ) ^ (1 - γ) * (k:ℝ)⁻¹ :=
      flat_case hγ0 hγ1 hT'1 (le_trans hT'1 hT'B) hBn hk hslopeT'
    have hfin : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) + 1 / γ * (n:ℝ) ^ (1 - γ) * (k:ℝ)⁻¹
        ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
          * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
      set A1 : ℝ := (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
        with hA1
      set S : ℝ := Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) with hS
      set X : ℝ := (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) with hX
      have hS0 : (0:ℝ) ≤ S := mul_nonneg hsqk hnpow
      have hX0 : (0:ℝ) ≤ X := mul_nonneg hkinv hn1g
      have hA10 : (0:ℝ) ≤ A1 := hK1
      have hnn1 : (0:ℝ) ≤ A1 * X := mul_nonneg hA10 hX0
      have hnn2 : (0:ℝ) ≤ 1 / γ * S := by positivity
      have e : 1 / γ * (n:ℝ) ^ (1 - γ) * (k:ℝ)⁻¹ = 1 / γ * X := by
        rw [hX]; ring
      rw [e]
      calc A1 * S + 1 / γ * X ≤ A1 * S + 1 / γ * X + (A1 * X + 1 / γ * S) := by linarith
        _ = (A1 + 1 / γ) * (S + X) := by ring

    linarith [hpiece1, hpiece2, hfin]

/-! ### The window as an interval -/

/-- The window filter is `Ico a (ceil (n/3 + y))`, with `a ≥ 1` when `y ≤ n/3`. -/
private theorem window_Ico_fixed (n : ℕ) (y : ℝ) :
    ∃ a : ℕ, (Finset.range (Nat.ceil ((n:ℝ)/3 + y) + 1)).filter
      (fun x : ℕ => |(x:ℝ) - (n:ℝ)/3| < y) = Finset.Ico a (Nat.ceil ((n:ℝ)/3 + y)) := by
  by_cases h0 : 0 ≤ (n : ℝ)/3 - y
  · refine ⟨Nat.floor ((n:ℝ)/3 - y) + 1, ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, abs_lt]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt h0).2 (by linarith)), Nat.lt_ceil.2 (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.floor_lt h0).1 (Nat.lt_of_succ_le h1)
      have h4 := Nat.lt_ceil.1 h2
      exact ⟨by omega, by linarith, by linarith⟩
  · refine ⟨0, ?_⟩
    rw [not_le] at h0
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, abs_lt]
    have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg x
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Nat.zero_le _, Nat.lt_ceil.2 (by linarith)⟩
    · rintro ⟨_, h2⟩
      have h4 := Nat.lt_ceil.1 h2
      exact ⟨by omega, by linarith, by linarith⟩

/-- The sub-window, when nonempty, is an interval `Ico A C` inside `[1, n]`. -/
private theorem subWindow_bounds {n : ℕ} {y : ℝ} (hn : 1 ≤ n) (hy : y ≤ (n:ℝ)/3) {t : ℝ}
    (hne : (subWindow n y t).Nonempty) :
    ∃ A C : ℕ, 1 ≤ A ∧ subWindow n y t = Finset.Ico A C ∧ C ≤ n := by
  obtain ⟨a, ha⟩ := window_Ico_fixed n y
  have hceil : Nat.ceil ((n:ℝ)/3 + y) ≤ n := by
    refine Nat.ceil_le.mpr ?_
    have : (n:ℝ)/3 + y ≤ (n:ℝ)/3 + (n:ℝ)/3 := by linarith
    have h2 : (n:ℝ)/3 + (n:ℝ)/3 ≤ (n:ℝ) := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    linarith
  have hsubi : subWindow n y t = (Finset.Ico a (Nat.ceil ((n:ℝ)/3 + y))).filter
      (fun x : ℕ => (x:ℝ) ≤ t) := by
    unfold subWindow
    rw [← ha, Finset.filter_filter]
  -- the window is nonempty, so `a ≥ 1`
  have hne2 := hne
  obtain ⟨x, hx⟩ := hne2
  have hxw : x ∈ (Finset.range (Nat.ceil ((n:ℝ)/3 + y) + 1)).filter
      (fun x : ℕ => |(x:ℝ) - (n:ℝ)/3| < y) := by
    simp only [subWindow, Finset.mem_filter] at hx
    exact Finset.mem_filter.mpr ⟨hx.1, hx.2.1⟩
  have hx1 : 1 ≤ x := (window_mem_bounds' n y hy x hxw).1
  have hxI : x ∈ Finset.Ico a (Nat.ceil ((n:ℝ)/3 + y)) := by
    rw [← ha]; exact hxw
  have hax : a ≤ x := (Finset.mem_Ico.mp hxI).1
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      have hcx : 0 < Nat.ceil ((n:ℝ)/3 + y) := by
        have := (Finset.mem_Ico.mp hxI).2
        omega
      have h0mem : (0:ℕ) ∈ Finset.Ico a (Nat.ceil ((n:ℝ)/3 + y)) := by
        rw [h]; simp only [Finset.mem_Ico]; omega
      have h0w : (0:ℕ) ∈ (Finset.range (Nat.ceil ((n:ℝ)/3 + y) + 1)).filter
          (fun x : ℕ => |(x:ℝ) - (n:ℝ)/3| < y) := by
        rw [ha]; exact h0mem
      simp only [Finset.mem_filter] at h0w
      have hlt : (n:ℝ)/3 < y := by
        have h2 := h0w.2
        rw [show (((0:ℕ):ℝ)) = 0 from by norm_num, zero_sub, abs_neg,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)/3)] at h2
        linarith
      linarith [hy]
    · exact h
  rcases lt_or_ge t 0 with ht | ht
  · -- empty window for `t < 0`
    exfalso
    obtain ⟨x, hx⟩ := hne
    have hxt : (x:ℝ) ≤ t := by
      simp only [subWindow, Finset.mem_filter] at hx
      exact hx.2.2
    have : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg x
    linarith
  · refine ⟨a, min (Nat.ceil ((n:ℝ)/3 + y)) (Nat.floor t + 1), ha1, ?_, ?_⟩
    · rw [hsubi]
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico]
      have hfe : x ≤ Nat.floor t ↔ (x:ℝ) ≤ t := Nat.le_floor_iff ht
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hxfl : x ≤ Nat.floor t := hfe.mpr h3
        exact ⟨h1, lt_min h2 (by omega)⟩
      · rintro ⟨h1, h2⟩
        have hxb : x < Nat.ceil ((n:ℝ)/3 + y) := lt_of_lt_of_le h2 (min_le_left _ _)
        have hxfl : x ≤ Nat.floor t := by
          have := lt_of_lt_of_le h2 (min_le_right _ _)
          omega
        exact ⟨⟨h1, hxb⟩, hfe.mp hxfl⟩
    · exact le_trans (min_le_left _ _) hceil

/-- The exponent pair bound for the sub-window. -/
private theorem subWindow_pow_bound {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : y ≤ (n:ℝ)/3) (t : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ‖∑ x ∈ subWindow n y t, eC ((k:ℝ) * (x:ℝ) ^ γ)‖ ≤
      ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
        * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hq : (1:ℝ) < (2:ℝ)^(γ/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq0 : (0:ℝ) < (2:ℝ)^(γ/2) - 1 := by linarith
  have hKB : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
  have hK1 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) :=
    div_nonneg (mul_nonneg hKB (le_trans (by norm_num) (le_of_lt hq))) hq0.le
  have hC0 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
      + 1 / γ := add_nonneg hK1 (by positivity)
  have hinner : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := by
    have h1 : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hnpos.le _)
    have h2 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hnpos.le _)
    linarith
  by_cases hne : (subWindow n y t).Nonempty
  · obtain ⟨A, C, hA1, hsub, hCn⟩ := subWindow_bounds hn hy hne
    rw [hsub]
    rcases le_or_gt C A with hCA | hAC
    · rw [Finset.Ico_eq_empty_of_le hCA, Finset.sum_empty, norm_zero]
      exact mul_nonneg hC0 hinner
    · exact interval_bound hγ0 hγ1 hk hA1 (le_of_lt hAC) hCn
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, norm_zero]
    exact mul_nonneg hC0 hinner

/-- Shifting the summation index. -/
private theorem sum_Ico_shift (f : ℕ → ℂ) (a c : ℕ) :
    ∑ x ∈ Finset.Ico a c, f (x + 1) = ∑ y ∈ Finset.Ico (a + 1) (c + 1), f y := by
  refine Finset.sum_bij (fun x _ => x + 1) (fun x hx => ?_)
    (fun x1 _ x2 _ h => by omega) (fun y hy => ?_) (fun x _ => rfl)
  · simp only [Finset.mem_Ico] at hx ⊢; omega
  · simp only [Finset.mem_Ico] at hy
    exact ⟨y - 1, by simp only [Finset.mem_Ico]; omega, by omega⟩

/-- The exponent pair bound for the sub-window with the shifted phase `(x+1)^γ`. -/
private theorem subWindow_shift_bound {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : y ≤ (n:ℝ)/3) (t : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ‖∑ x ∈ subWindow n y t, eC ((k:ℝ) * ((x:ℝ) + 1) ^ γ)‖ ≤
      (2 * (((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)))
        * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hq : (1:ℝ) < (2:ℝ)^(γ/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq0 : (0:ℝ) < (2:ℝ)^(γ/2) - 1 := by linarith
  have hKB : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
  have hK1 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) :=
    div_nonneg (mul_nonneg hKB (le_trans (by norm_num) (le_of_lt hq))) hq0.le
  have hC0 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
      + 1 / γ := add_nonneg hK1 (by positivity)
  by_cases hne : (subWindow n y t).Nonempty
  · obtain ⟨A, C, hA1, hsub, hCn⟩ := subWindow_bounds hn hy hne
    rw [hsub]
    rcases le_or_gt C A with hCA | hAC
    · rw [Finset.Ico_eq_empty_of_le hCA, Finset.sum_empty, norm_zero]
      have hinner : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := by
        have h1 : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hnpos.le _)
        have h2 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg hnpos.le _)
        linarith
      have hinner : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := by
        have h1 : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hnpos.le _)
        have h2 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg hnpos.le _)
        linarith
      exact mul_nonneg (by linarith : (0:ℝ) ≤ 2 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)) hinner
    · have hshift : ∑ x ∈ Finset.Ico A C, eC ((k:ℝ) * ((x:ℝ) + 1) ^ γ)
          = ∑ y ∈ Finset.Ico (A + 1) (C + 1), eC ((k:ℝ) * (y:ℝ) ^ γ) := by
        rw [← sum_Ico_shift (fun y => eC ((k:ℝ) * (y:ℝ) ^ γ)) A C]
        exact Finset.sum_congr rfl fun x _ => by congr 2; push_cast; ring
      rw [hshift]
      have hb := interval_bound hγ0 hγ1 (k := k) (n := n + 1) (A := A + 1) (B := C + 1) hk
        (by omega) (by omega) (by omega)
      refine hb.trans ?_
      rw [show ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 from by push_cast; ring]
      -- `2 C0 (√k n^(γ/2) + k⁻¹ n^(1-γ))`
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have harg1 : ((n:ℝ) + 1) ^ (γ/2) ≤ 2 * (n:ℝ) ^ (γ/2) := by
        have h1 : ((n:ℝ) + 1) ≤ 2 * (n:ℝ) := by linarith
        have h2 : ((n:ℝ) + 1) ^ (γ/2) ≤ (2 * (n:ℝ)) ^ (γ/2) :=
          Real.rpow_le_rpow (by positivity) h1 (by linarith)
        have h3 : (2 * (n:ℝ)) ^ (γ/2) = (2:ℝ)^(γ/2) * (n:ℝ)^(γ/2) :=
          Real.mul_rpow (by norm_num) hnpos.le
        rw [h3] at h2
        have h4 : (2:ℝ)^(γ/2) ≤ 2 := by
          have h5 : (2:ℝ)^(γ/2) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)
          rwa [Real.rpow_one] at h5
        have h6 : (0:ℝ) ≤ (n:ℝ)^(γ/2) := (Real.rpow_pos_of_pos hnpos _).le
        nlinarith [h2, h4, h6]
      have harg2 : ((n:ℝ) + 1) ^ (1 - γ) ≤ 2 * (n:ℝ) ^ (1 - γ) := by
        have h1 : ((n:ℝ) + 1) ≤ 2 * (n:ℝ) := by linarith
        have h2 : ((n:ℝ) + 1) ^ (1 - γ) ≤ (2 * (n:ℝ)) ^ (1 - γ) :=
          Real.rpow_le_rpow (by positivity) h1 (by linarith)
        have h3 : (2 * (n:ℝ)) ^ (1 - γ) = (2:ℝ)^(1 - γ) * (n:ℝ)^(1 - γ) :=
          Real.mul_rpow (by norm_num) hnpos.le
        rw [h3] at h2
        have h4 : (2:ℝ)^(1 - γ) ≤ 2 := by
          have h5 : (2:ℝ)^(1 - γ) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)
          rwa [Real.rpow_one] at h5
        have h6 : (0:ℝ) ≤ (n:ℝ)^(1 - γ) := (Real.rpow_pos_of_pos hnpos _).le
        nlinarith [h2, h4, h6]
      have hfin : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
            * (Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2)
              + (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ))
          ≤ 2 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
            * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
        have hs : (0:ℝ) ≤ Real.sqrt (k:ℝ) := Real.sqrt_nonneg _
        have hk0 : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
        have hu : (0:ℝ) ≤ ((n:ℝ) + 1) ^ (γ/2) := (Real.rpow_pos_of_pos (by linarith) _).le
        have hv : (0:ℝ) ≤ ((n:ℝ) + 1) ^ (1 - γ) := (Real.rpow_pos_of_pos (by linarith) _).le
        have e1 : Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2) ≤ 2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
          nlinarith [harg1, hs, hu]
        have e2 : (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ) ≤ 2 * ((k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
          nlinarith [harg2, hk0, hv]
        have e3 : Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2) + (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ)
            ≤ 2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
          linarith [e1, e2]
        have e4 : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
              * (Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2) + (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ))
            ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
              * (2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ))) :=
          mul_le_mul_of_nonneg_left e3 hK1
        have e5 : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
              * (2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)))
            ≤ 2 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
              * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
          have hw : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := by
            have h1 : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) :=
              mul_nonneg hs (Real.rpow_nonneg hnpos.le _)
            have h2 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) :=
              mul_nonneg hk0 (Real.rpow_nonneg hnpos.le _)
            linarith
          have hcoe : (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) * 2
              ≤ 2 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ) := by
            nlinarith [hK1, show (0:ℝ) < 1 / γ from by positivity]
          nlinarith [hcoe, hw, hK1]
        linarith [e4, e5]
      have hs : (0:ℝ) ≤ Real.sqrt (k:ℝ) := Real.sqrt_nonneg _
      have hk0 : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
      have hu : (0:ℝ) ≤ ((n:ℝ) + 1) ^ (γ/2) := (Real.rpow_pos_of_pos (by linarith) _).le
      have hv : (0:ℝ) ≤ ((n:ℝ) + 1) ^ (1 - γ) := (Real.rpow_pos_of_pos (by linarith) _).le
      have f1 : Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2) ≤ 2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2)) := by
        nlinarith [harg1, hs, hu]
      have f2 : (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ) ≤ 2 * ((k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
        nlinarith [harg2, hk0, hv]
      have hY : Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2) + (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ)
          ≤ 2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by
        linarith [f1, f2]
      calc ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
            * (Real.sqrt (k:ℝ) * ((n:ℝ) + 1) ^ (γ/2) + (k:ℝ)⁻¹ * ((n:ℝ) + 1) ^ (1 - γ))
          ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
            * (2 * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ))) :=
            mul_le_mul_of_nonneg_left hY hC0
        _ = 2 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
            * (Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) := by ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, norm_zero]
    have hinner : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := by
      have h1 : (0:ℝ) ≤ Real.sqrt (k:ℝ) * (n:ℝ) ^ (γ/2) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hnpos.le _)
      have h2 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg hnpos.le _)
      linarith
    exact mul_nonneg (by linarith : (0:ℝ) ≤ 2 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)) hinner

/-- Song 2020, page 4, last display, "Using the exponent pair (1/2, 1/2)
([2], eqn. 3.3.4)": the unweighted sum of e of k x to the γ over any initial segment of the
window is at most a constant times k to the 1/2 times n to the γ/2, plus k to the minus 1
times n to the 1 minus γ, both for the points x and x plus 1. This is Graham and Kolesnik
display 3.3.4, proved through the ported BakerHarmanPintz1997.PortedVanDerCorput
second derivative test and Kusmin Landau inequality, over dyadic blocks. -/
theorem exponent_pair_half (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, y ≤ (n : ℝ) / 3 →
      ∀ t : ℝ, ∀ k : ℕ, 1 ≤ k →
        ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * (x : ℝ) ^ γ)‖ ≤
            C * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
              (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)) ∧
        ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * ((x : ℝ) + 1) ^ γ)‖ ≤
            C * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
              (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)) := by
  have hγ0 : 0 < γ := by linarith
  have hq : (1:ℝ) < (2:ℝ)^(γ/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq0 : (0:ℝ) < (2:ℝ)^(γ/2) - 1 := by linarith
  have hKB : (0:ℝ) ≤ 16 + 64 * Real.sqrt (γ / (1 - γ)) := by positivity
  have hK1 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) :=
    div_nonneg (mul_nonneg hKB (le_trans (by norm_num) (le_of_lt hq))) hq0.le
  have hC0 : (0:ℝ) ≤ (16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1)
      + 1 / γ := add_nonneg hK1 (by positivity)
  refine ⟨4 * ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ),
    by positivity, 3, ?_⟩
  intro n hn y hy t k hk
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hskeq : Real.sqrt (k:ℝ) = (k:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have hinner : (0:ℝ) ≤ (k:ℝ) ^ ((1:ℝ)/2) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) := by
    have h1 : (0:ℝ) ≤ (k:ℝ) ^ ((1:ℝ)/2) * (n:ℝ) ^ (γ/2) :=
      mul_nonneg (Real.rpow_nonneg hkpos.le _) (Real.rpow_nonneg hnpos.le _)
    have h2 : (0:ℝ) ≤ (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hnpos.le _)
    linarith
  constructor
  · have h1 := subWindow_pow_bound hγ0 hγ1 hn1 hy t hk
    rw [hskeq] at h1
    refine h1.trans ?_
    have hprod : (0:ℝ) ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
        * ((k:ℝ) ^ ((1:ℝ)/2) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) :=
      mul_nonneg hC0 hinner
    nlinarith [hprod, hC0, hinner]
  · have h1 := subWindow_shift_bound hγ0 hγ1 hn1 hy t hk
    rw [hskeq] at h1
    refine h1.trans ?_
    have hprod : (0:ℝ) ≤ ((16 + 64 * Real.sqrt (γ / (1 - γ))) * ((2:ℝ)^(γ/2)) / ((2:ℝ)^(γ/2) - 1) + 1 / γ)
        * ((k:ℝ) ^ ((1:ℝ)/2) * (n:ℝ) ^ (γ/2) + (k:ℝ)⁻¹ * (n:ℝ) ^ (1 - γ)) :=
      mul_nonneg hC0 hinner
    nlinarith [hprod, hC0, hinner]


/-- Proved STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the frequency h = 0 term
H to the minus 1 times y times n to the 1 minus γ: the weighted count of the window is at
most 1/γ times n to the 1 minus γ times 2y plus 1. -/
theorem zero_frequency_term (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ (n : ℝ) / 3) (φ : ℕ → ℝ) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        (psWeight γ x : ℂ) * eC (φ x * ((0 : ℤ) : ℝ))‖ ≤
      1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) := by
  have hsimp : ∀ x : ℕ, (psWeight γ x : ℂ) * eC (φ x * ((0 : ℤ) : ℝ)) =
      (psWeight γ x : ℂ) := by
    intro x; simp [eC]
  simp only [hsimp]
  refine (norm_sum_le _ _).trans ?_
  set S := (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y) with hS
  set A := Nat.ceil ((n : ℝ) / 3 - y) with hAdef
  set m := Nat.floor (2 * y) with hmdef
  have hAr : (n : ℝ) / 3 - y ≤ A := Nat.le_ceil _
  have hsub : S ⊆ Finset.Icc A (A + m) := by
    intro x hx
    rw [hS, Finset.mem_filter, abs_lt] at hx
    obtain ⟨_, h1, h2⟩ := hx
    have hA : A ≤ x := Nat.ceil_le.mpr (by linarith)
    have hm : x - A ≤ m := by
      apply Nat.le_floor
      rw [Nat.cast_sub hA]
      linarith
    exact Finset.mem_Icc.mpr ⟨hA, by omega⟩
  have hcard : (S.card : ℝ) ≤ 2 * y + 1 := by
    have h1 : S.card ≤ m + 1 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have h2 : (m : ℝ) ≤ 2 * y := Nat.floor_le (by positivity)
    have h3 : (S.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hw : ∀ x ∈ S, ‖(psWeight γ x : ℂ)‖ ≤ 1 / γ * (n : ℝ) ^ (1 - γ) := by
    intro x hx
    rw [hS, Finset.mem_filter, abs_lt] at hx
    obtain ⟨_, _, h2⟩ := hx
    have hxn : (x : ℝ) ≤ n := by linarith
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      unfold psWeight
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
    unfold psWeight
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hxn (by linarith)) (by positivity)
  have hB0 : 0 ≤ 1 / γ * (n : ℝ) ^ (1 - γ) := by positivity
  calc ∑ x ∈ S, ‖(psWeight γ x : ℂ)‖ ≤ S.card • (1 / γ * (n : ℝ) ^ (1 - γ)) :=
        Finset.sum_le_card_nsmul _ _ _ hw
    _ = (S.card : ℝ) * (1 / γ * (n : ℝ) ^ (1 - γ)) := nsmul_eq_mul _ _
    _ ≤ (2 * y + 1) * (1 / γ * (n : ℝ) ^ (1 - γ)) :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ = 1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) := by ring

/-- Proved STEP: Song 2020, page 4, display after "By Lemma 3.1, we have", the sum over |h| at most H split into the
term h = 0 and the 2H nonzero frequencies. Proved here. -/
theorem sum_Icc_split (H : ℕ) (g : ℤ → ℝ) (G : ℝ)
    (hg : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, h ≠ 0 → g h ≤ G) :
    ∑ h ∈ Finset.Icc (-(H : ℤ)) H, g h ≤ g 0 + 2 * H * G := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := by simp
  rw [← Finset.add_sum_erase _ _ h0]
  refine add_le_add le_rfl ?_
  have hcard : ((Finset.Icc (-(H : ℤ)) H).erase 0).card = 2 * H := by
    rw [Finset.card_erase_of_mem h0, Int.card_Icc]
    omega
  calc ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, g h
      ≤ ∑ _h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, G :=
        Finset.sum_le_sum fun h hh =>
          hg h (Finset.mem_of_mem_erase hh) (Finset.ne_of_mem_erase hh)
    _ = 2 * H * G := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring

/-- Proved STEP: Song 2020, page 5, the display "Concluding the above estimate": the final
arithmetic. With the trivial bounds |h| to the 1/2 at most H to the 1/2 and |h| inverse at
most 1 per frequency, the two majorant sums are at most an explicit constant times
H to the 1/2 times n to the 1 minus γ/2 plus H inverse times y times n to the 1 minus γ.
It uses n to the 2 minus 2γ at most n to the 1 minus γ/2 and 2y plus 1 at most 3y. -/
theorem s2_final_arith (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (C0 CE : ℝ)
    (hC0 : 0 ≤ C0) (hCE : 0 ≤ CE) (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 1 ≤ y)
    (H : ℕ) (hH : 1 ≤ H) :
    2 * (C0 / H * (1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) +
      2 * H * (2 / γ * (n : ℝ) ^ (1 - γ) *
        (CE * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ)))))) ≤
      (6 * C0 / γ + 16 * C0 * CE / γ) * tailBudget γ n y H := by
  have hγ0 : 0 < γ := by linarith
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set P := (n : ℝ) ^ (1 - γ) with hP
  set Q := (n : ℝ) ^ (γ / 2) with hQ
  set R := (H : ℝ) ^ ((1 : ℝ) / 2) with hR
  have hP0 : 0 ≤ P := Real.rpow_nonneg hnpos.le _
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hnpos.le _
  have hPQ : P ≤ Q := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hR1 : 1 ≤ R := Real.one_le_rpow hHr (by norm_num)
  have hsplit : (n : ℝ) ^ (1 - γ / 2) = P * Q := by
    rw [hP, hQ, ← Real.rpow_add hnpos]; congr 1; ring
  unfold tailBudget
  rw [hsplit]
  have hHpos : (0 : ℝ) < H := by linarith
  have e1 : 2 * (C0 / H * (1 / γ * P * (2 * y + 1) +
      2 * H * (2 / γ * P * (CE * (R * Q + P))))) =
      (2 * C0 * P * (2 * y + 1) / γ) / H + 8 * C0 * CE * P * (R * Q + P) / γ := by
    field_simp; ring
  have e2 : (6 * C0 / γ + 16 * C0 * CE / γ) * (R * (P * Q) + (H : ℝ)⁻¹ * y * P) =
      (6 * C0 * y * P / γ) / H + 16 * C0 * CE * R * P * Q / γ +
        (6 * C0 / γ) * (R * (P * Q)) + 16 * C0 * CE / γ * ((H : ℝ)⁻¹ * y * P) := by
    field_simp; ring
  rw [e1, e2]
  have t1 : (2 * C0 * P * (2 * y + 1) / γ) / H ≤ (6 * C0 * y * P / γ) / H := by
    apply div_le_div_of_nonneg_right _ hHpos.le
    apply div_le_div_of_nonneg_right _ hγ0.le
    nlinarith [mul_nonneg (mul_nonneg hC0 hP0) (sub_nonneg.mpr hy)]
  have t2 : 8 * C0 * CE * P * (R * Q + P) / γ ≤ 16 * C0 * CE * R * P * Q / γ := by
    apply div_le_div_of_nonneg_right _ hγ0.le
    have h1 : R * Q + P ≤ 2 * (R * Q) := by
      nlinarith [mul_le_mul_of_nonneg_right hR1 hQ0]
    have hc : 0 ≤ 8 * C0 * CE * P := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hc]
  have t3 : 0 ≤ (6 * C0 / γ) * (R * (P * Q)) := by positivity
  have t4 : 0 ≤ 16 * C0 * CE / γ * ((H : ℝ)⁻¹ * y * P) := by positivity
  linarith

/-! ## Proved glue -/

/-- Conditional on weighted_window_bound. Proved from the leaves. Page 4, the per frequency bound for h nonzero. -/
theorem per_h_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy : y ≤ (n : ℝ) / 3) (H : ℕ) (v : ℕ → ℝ) (CE : ℝ) (hCE : 0 ≤ CE)
    (hv : ∀ t : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * v x)‖ ≤
        CE * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)))
    (h : ℤ) (hh : h ∈ Finset.Icc (-(H : ℤ)) H) (h0 : h ≠ 0) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        (psWeight γ x : ℂ) * eC (-(v x) * h)‖ ≤
      2 / γ * (n : ℝ) ^ (1 - γ) *
        (CE * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ))) := by
  rw [conj_phase]
  set k := h.natAbs with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact Int.natAbs_pos.mpr h0
  have hkH : k ≤ H := by
    rw [Finset.mem_Icc] at hh; rw [hk]; omega
  have hB := weighted_window_bound γ hγ0 hγ1 n hn y hy (fun x => (k : ℝ) * v x) _
    (fun t => hv t k hk1)
  refine hB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine mul_le_mul_of_nonneg_left ?_ hCE
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkHR : (k : ℝ) ≤ H := by exact_mod_cast hkH
  have hnp : 0 ≤ (n : ℝ) ^ (γ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnq : 0 ≤ (n : ℝ) ^ (1 - γ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine add_le_add (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by linarith) hkHR (by norm_num)) hnp) ?_
  have : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hkR
  calc (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ) ≤ 1 * (n : ℝ) ^ (1 - γ) :=
        mul_le_mul_of_nonneg_right this hnq
    _ = (n : ℝ) ^ (1 - γ) := one_mul _

/-- Conditional on weighted_window_bound. Proved from the leaves. Page 4, the bound of one of the two majorant sums. -/
theorem majorant_sum_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 3 ≤ n)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ (n : ℝ) / 3) (H : ℕ) (b : ℤ → ℂ) (C0 : ℝ)
    (hb : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b h‖ ≤ C0 / H) (hC0 : 0 ≤ C0)
    (v : ℕ → ℝ) (CE : ℝ) (hCE : 0 ≤ CE)
    (hv : ∀ t : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖∑ x ∈ subWindow n y t, eC ((k : ℝ) * v x)‖ ≤
        CE * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (k : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ))) :
    ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        psWeight γ x * (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b h * eC (-(v x) * h)).re ≤
      C0 / H * (1 / γ * (n : ℝ) ^ (1 - γ) * (2 * y + 1) +
        2 * H * (2 / γ * (n : ℝ) ^ (1 - γ) *
          (CE * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ))))) := by
  refine (majorant_expand _ (psWeight γ) (fun x => -(v x)) b H (C0 / H) hb).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sum_Icc_split H _ _ fun h hh h0 =>
    per_h_bound γ hγ0 hγ1 n hn y hy H v CE hCE hv h hh h0).trans ?_
  exact add_le_add (zero_frequency_term γ hγ0 hγ1 n hn y hy0 hy _) le_rfl

/-- Conditional on weighted_window_bound and exponent_pair_half. Proved from the leaves. The exact statement of
`Decomp139.fourier_approximation`, Song 2020 pages 4 and 5, the S2 bound. -/
theorem fourier_approximation_of_leaves :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  intro γ hγ hγ1
  have hγ0 : 0 < γ := by linarith
  obtain ⟨C0, hC0, a, b, hab⟩ := Repair591FourierMajorant.song_lemma1_majorant591
  obtain ⟨CE, hCE, NE, hNE⟩ := exponent_pair_half γ hγ hγ1
  refine ⟨fun H h => if |h| ≤ (H : ℤ) then a H h else 0, C0 + 1, by linarith, ?_, ?_⟩
  · intro H h h0
    have hpos : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast h0)
    by_cases hh : |h| ≤ (H : ℤ)
    · by_cases hH : 1 ≤ H
      · simp only [hh, ite_true]
        refine ((hab H hH).1 h h0 hh).trans ?_
        exact div_le_div_of_nonneg_right (by linarith) hpos.le
      · have : H = 0 := by omega
        subst this
        exfalso; apply h0; simp at hh; omega
    · simp only [hh, ite_false, norm_zero]
      positivity
  refine ⟨6 * C0 / γ + 16 * C0 * CE / γ, by positivity, max NE 3, ?_⟩
  intro n hn y hy hy3 H hH α
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have hnE : NE ≤ n := le_of_max_le_left hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy1 : 1 ≤ y := (Real.one_le_rpow hn1 hexp).trans hy.le
  set M : ℝ → ℝ := fun x => (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re with hMdef
  have hM : ∀ x : ℝ, ‖((saw x : ℝ) : ℂ) -
      Decomp139.fourier (fun H h => if |h| ≤ (H : ℤ) then a H h else 0) H x‖ ≤ M x := by
    intro x
    have hf : Decomp139.fourier (fun H h => if |h| ≤ (H : ℤ) then a H h else 0) H x =
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (x * h) := by
      unfold Decomp139.fourier
      refine Finset.sum_congr rfl fun h hh => ?_
      have hh' : |h| ≤ (H : ℤ) := by
        rw [Finset.mem_filter, Finset.mem_Icc] at hh
        exact abs_le.mpr hh.1
      simp only [hh', ite_true, mul_comm (h : ℝ) x]
    rw [hf]
    exact ((hab H hH).2.2 x).2
  have hM0 : ∀ x, 0 ≤ M x := fun x => (norm_nonneg _).trans (hM x)
  have hw0 : ∀ x : ℕ, 0 ≤ psWeight γ x := fun x => by
    unfold psWeight
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hbH : ∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ ≤ C0 / H := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact (hab H hH).2.1 h (abs_le.mpr hh)
  have hy0 : 0 ≤ y := by linarith
  have hE := hNE n hnE y hy3
  have hA := majorant_sum_bound γ hγ0 hγ1 n hn3 y hy0 hy3 H (b H) C0 hbH hC0
    (fun x => ((x : ℝ) + 1) ^ γ) CE hCE (fun t k hk => (hE t k hk).2)
  have hB := majorant_sum_bound γ hγ0 hγ1 n hn3 y hy0 hy3 H (b H) C0 hbH hC0
    (fun x => (x : ℝ) ^ γ) CE hCE (fun t k hk => (hE t k hk).1)
  refine (s2_pointwise_majorant γ hγ0 n y α _ H M hM).trans ?_
  refine (primes_to_window n y _ fun x =>
    mul_nonneg (hw0 x) (add_nonneg (hM0 _) (hM0 _))).trans ?_
  refine le_trans ?_ (s2_final_arith γ hγ hγ1 C0 CE hC0 hCE n (by omega) y hy1 H hH)
  have hsum : ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y),
        psWeight γ x * (M (-((x : ℝ) + 1) ^ γ) + M (-(x : ℝ) ^ γ)) =
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), psWeight γ x * M (-((x : ℝ) + 1) ^ γ) +
      ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y), psWeight γ x * M (-(x : ℝ) ^ γ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => mul_add _ _ _
  rw [hsum, two_mul]
  exact add_le_add hA hB

end

end LeanLab.Song2020.Prep1121FourierS2
