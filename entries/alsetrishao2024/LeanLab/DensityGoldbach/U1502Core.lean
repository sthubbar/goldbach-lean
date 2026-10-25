module

public import LeanLab.DensityGoldbach.U1502Pairs
public import LeanLab.DensityGoldbach.U1502Moment

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

The deterministic core of the large spectrum bound. For a frequency set `R ⊆ Z_N`, `k = |R|`,

  `Σ_{r, r' ∈ R} Φ_T(r - r') ≤ 32 ((J+1) T k² / 2^J + 42 (M_T k^{10})^{1/8}) + 8 T k² / N`,

where `Φ_T(s) = Σ_{q ≤ T sqfree} Σ_{(a,q)=1} φ(q)⁻¹ ψ_N(s/N - a/q)` is the major arc profile,
`J = log₂ N - 1` and `M_T = (e S(T))^8 exp(6560 Σ_{p ≤ T} 1/p)`. Then the TT* dichotomy: if a
function `F` on `Z_N` with `F(0) ≤ A` and `F(s) ≤ η + C Φ_T(s)` for `s ≠ 0` satisfies
`(kδ)² ≤ A Σ_{r,r'} F(r - r')`, and the error terms are below `δ²/4`, then
`k δ² ≤ 4 A²` or `k^6 δ^{16} ≤ (3584 A C)^8 M_T`.

Proof: `ψ_N ≤ 32 Kd + 8/N` (U1502Fejer), the pair expansion of each Fejer level (U1502Pairs),
Cauchy-Schwarz three times with the eighth moment of the Ramanujan majorant (U1502Moment),
and a geometric sum over the dyadic levels with ratio `2^{1/4}`.

Known mathematics in the style of Bourgain 1989 and Green 2005 Section 4, no cited input.
AI-written Lean code, Claude, 2026-10-23. Checked only by the Lean kernel. Binary Goldbach is
OPEN.
-/

@[expose] public section

open Finset Real
open LeanLab.PNTPort.LargeSieve

noncomputable section
namespace LeanLab.DensityGoldbach.U1502

variable {N : ℕ} [NeZero N]

/-- The major arc profile `Φ_T(s) = Σ_{q ≤ T sqfree} Σ_{(a,q)=1} φ(q)⁻¹ ψ_N(s/N - a/q)`. -/
def PhiT (N : ℕ) [NeZero N] (T : ℕ) (s : ZMod N) : ℝ :=
  ∑ j ∈ Fs T, wF j * psiN N (thetaN N s - bF j)

/-- `M_T = (e S(T))^8 exp(6560 Σ_{p ≤ T} 1/p)`. -/
def MT (T : ℕ) : ℝ := (ST T * Real.exp 1) ^ 8 * Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p)

lemma MT_nonneg (T : ℕ) : 0 ≤ MT T := by
  unfold MT
  have := ST_nonneg T
  positivity

lemma PhiT_nonneg (T : ℕ) (s : ZMod N) : 0 ≤ PhiT N T s :=
  sum_nonneg fun j _ => mul_nonneg (wF_nonneg j) (psiN_nonneg _ _)

lemma sum_wF_le (T : ℕ) : ∑ j ∈ Fs T, wF j ≤ T := by
  unfold Fs
  rw [sum_sigma]
  have : ∀ q ∈ Qs T, ∑ a ∈ Us q, wF ⟨q, a⟩ = 1 := by
    intro q hq
    rw [mem_Qs] at hq
    unfold wF
    simp only
    rw [sum_const, card_Us, nsmul_eq_mul]
    have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
    field_simp
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
  have : (Qs T).card ≤ T := by
    unfold Qs
    exact (card_filter_le _ _).trans (by simp)
  exact_mod_cast this

lemma GT_eq_Gz (T : ℕ) (t : ℤ) : Gz (Fs T) wF bF t = GT T t := rfl

/-- One dyadic level. -/
theorem level_bound (R : Finset (ZMod N)) (T i : ℕ) :
    ∑ j ∈ Fs T, wF j * ∑ r ∈ R, ∑ r' ∈ R, fej (2 ^ i) (thetaN N (r - r') - bF j) ≤
      T * (R.card : ℝ) ^ 2 + 2 * ∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ * ‖Pz R (m : ℤ)‖ ^ 2 := by
  have h := pair_bound R (2 ^ i) Nat.one_le_two_pow (Fs T) wF bF (fun j _ => wF_nonneg j)
  simp only [GT_eq_Gz] at h
  refine h.trans ?_
  have h0 : ‖GT T 0‖ * ‖Pz R 0‖ ^ 2 ≤ T * (R.card : ℝ) ^ 2 := by
    have := GT_le_T T 0
    have h2 := norm_Pz_le R 0
    exact mul_le_mul this (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity)
      (Nat.cast_nonneg _)
  push_cast at h0 ⊢
  linarith

/-- The eighth power bound at one level: `X^8 ≤ M_T 4^i N^6 k^{10}`. -/
theorem level_X_bound (R : Finset (ZMod N)) (T i : ℕ) (hi : 2 ^ i ≤ N) :
    (∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ * ‖Pz R (m : ℤ)‖ ^ 2) ^ 8 ≤
      MT T * 4 ^ i * (N : ℝ) ^ 6 * (R.card : ℝ) ^ 10 := by
  set k := (R.card : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hcs := cs_chain (Ico 1 (2 ^ i)) (fun m : ℕ => ‖GT T m‖) (fun m : ℕ => ‖Pz R m‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) k (fun m _ => norm_Pz_le R m)
  have hG8 : ∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ ^ 8 ≤ MT T * 2 ^ i := by
    have hpt : ∀ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ ^ 8 ≤
        (ST T * Real.exp 1) ^ 8 * ((3 : ℝ) ^ (Bset T m).card) ^ 8 := by
      intro m _
      have h := GT_le_omega T m
      have : ‖GT T (m : ℤ)‖ ^ 8 ≤ (ST T * (Real.exp 1 * 3 ^ (Bset T m).card)) ^ 8 :=
        pow_le_pow_left₀ (norm_nonneg _) h 8
      calc ‖GT T (m : ℤ)‖ ^ 8 ≤ (ST T * (Real.exp 1 * 3 ^ (Bset T m).card)) ^ 8 := this
        _ = (ST T * Real.exp 1) ^ 8 * ((3 : ℝ) ^ (Bset T m).card) ^ 8 := by ring
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum]
    have hm := moment8 T (2 ^ i)
    have hc : 0 ≤ (ST T * Real.exp 1) ^ 8 := by have := ST_nonneg T; positivity
    calc (ST T * Real.exp 1) ^ 8 * ∑ m ∈ Ico 1 (2 ^ i), ((3 : ℝ) ^ (Bset T m).card) ^ 8
        ≤ (ST T * Real.exp 1) ^ 8 * ((2 ^ i : ℕ) * Real.exp (6560 * ∑ p ∈ PT T, (1 : ℝ) / p)) :=
          mul_le_mul_of_nonneg_left hm hc
      _ = MT T * 2 ^ i := by unfold MT; push_cast; ring
  have hI : ((Ico 1 (2 ^ i)).card : ℝ) ≤ 2 ^ i := by
    rw [Nat.card_Ico]; push_cast
    have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    rw [Nat.cast_sub this]; push_cast; linarith
  have hP := sum_Pz_sq_le R (2 ^ i) hi
  have hP0 : 0 ≤ ∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖Pz R (m : ℤ)‖ ^ 2 := sum_nonneg fun _ _ => by positivity
  have hG0 : 0 ≤ ∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ ^ 8 := sum_nonneg fun _ _ => by positivity
  have hM0 := MT_nonneg T
  calc (∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ * ‖Pz R (m : ℤ)‖ ^ 2) ^ 8
      ≤ (∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ ^ 8) * ((Ico 1 (2 ^ i)).card : ℝ) * k ^ 4 *
          (∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖Pz R (m : ℤ)‖ ^ 2) ^ 6 := hcs
    _ ≤ (MT T * 2 ^ i) * 2 ^ i * k ^ 4 * ((N : ℝ) * k) ^ 6 := by
        apply mul_le_mul _ (pow_le_pow_left₀ hP0 hP 6) (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hG8 hI (Nat.cast_nonneg _) (by positivity)
    _ = MT T * 4 ^ i * (N : ℝ) ^ 6 * k ^ 10 := by
        rw [show (4 : ℝ) ^ i = 2 ^ i * 2 ^ i by rw [← mul_pow]; norm_num]; ring

/-- `ρ = 2^{1/4}`. -/
lemma exists_rho : ∃ ρ : ℝ, 7 / 6 ≤ ρ ∧ ρ ≤ 6 / 5 ∧ ρ ^ 4 = 2 := by
  refine ⟨(2 : ℝ) ^ ((1 : ℝ) / 4), ?_, ?_, ?_⟩
  · have h : ((7 : ℝ) / 6) ^ 4 ≤ ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)), ← Real.rpow_mul (by norm_num)]
      norm_num
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).1 h
  · have h : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 ≤ ((6 : ℝ) / 5) ^ 4 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)), ← Real.rpow_mul (by norm_num)]
      norm_num
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).1 h
  · rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)), ← Real.rpow_mul (by norm_num)]
    norm_num

/-- The geometric sum over the dyadic levels. -/
theorem dyadic_geom (J : ℕ) (Nr Wc : ℝ) (hN0 : 0 ≤ Nr) (hN : Nr ≤ 4 * 2 ^ J) (hW : 0 ≤ Wc)
    (X : ℕ → ℝ) (hX0 : ∀ i, 0 ≤ X i) (hX : ∀ i ≤ J, X i ^ 8 ≤ Wc * 4 ^ i * Nr ^ 6) :
    (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1), 2 * X i ≤ 42 * Wc ^ ((1 : ℝ) / 8) := by
  obtain ⟨ρ, hρ1, hρ2, hρ4⟩ := exists_rho
  set Z := Wc ^ ((1 : ℝ) / 8) with hZ
  have hZ0 : 0 ≤ Z := Real.rpow_nonneg hW _
  have hZ8 : Z ^ 8 = Wc := by
    rw [hZ, ← Real.rpow_natCast, ← Real.rpow_mul hW]; norm_num
  have hρ0 : 0 < ρ := by linarith
  have h2J : (2 : ℝ) ^ J = ρ ^ (4 * J) := by rw [pow_mul, hρ4]
  have hXi : ∀ i ≤ J, X i ≤ Z * ρ ^ (i + 3 * J + 6) := by
    intro i hi
    have h1 : Nr ^ 6 ≤ (4 * 2 ^ J) ^ 6 := pow_le_pow_left₀ hN0 hN 6
    have h2 : Wc * 4 ^ i * Nr ^ 6 ≤ (Z * ρ ^ (i + 3 * J + 6)) ^ 8 := by
      have e : (Z * ρ ^ (i + 3 * J + 6)) ^ 8 = Wc * 4 ^ i * (4 * 2 ^ J) ^ 6 := by
        have h1 : (Z * ρ ^ (i + 3 * J + 6)) ^ 8 = Z ^ 8 * (ρ ^ 4) ^ (2 * i + 6 * J + 12) := by
          ring
        rw [h1, hZ8, hρ4, show (4 : ℝ) ^ i = 2 ^ (2 * i) by rw [pow_mul]; norm_num]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    exact (pow_le_pow_iff_left₀ (hX0 i) (by positivity) (by norm_num)).1 ((hX i hi).trans h2)
  have hgeom : ∑ i ∈ range (J + 1), ρ ^ i ≤ 6 * ρ ^ (J + 1) := by
    have h := geom_sum_eq (show ρ ≠ 1 by intro h; rw [h] at hρ4; norm_num at hρ4) (J + 1)
    rw [h]
    have hρ1' : 0 < ρ - 1 := by linarith
    rw [div_le_iff₀ hρ1']
    have : 0 ≤ ρ ^ (J + 1) := by positivity
    nlinarith
  calc (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1), 2 * X i
      ≤ (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1), 2 * (Z * ρ ^ (i + 3 * J + 6)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun i hi => by
          have := hXi i (by rw [mem_range] at hi; omega); linarith
    _ = (1 / (2 : ℝ) ^ J) * (2 * Z * ρ ^ (3 * J + 6)) * ∑ i ∈ range (J + 1), ρ ^ i := by
        have : ∑ i ∈ range (J + 1), 2 * (Z * ρ ^ (i + 3 * J + 6)) =
            2 * Z * ρ ^ (3 * J + 6) * ∑ i ∈ range (J + 1), ρ ^ i := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [show i + 3 * J + 6 = i + (3 * J + 6) by ring, pow_add]; ring
        rw [this]; ring
    _ ≤ (1 / (2 : ℝ) ^ J) * (2 * Z * ρ ^ (3 * J + 6)) * (6 * ρ ^ (J + 1)) := by
        apply mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 12 * Z * ρ ^ 7 := by
        rw [h2J]
        have h47 : ρ ^ (3 * J + 6) * ρ ^ (J + 1) = ρ ^ (4 * J) * ρ ^ 7 := by
          rw [← pow_add, ← pow_add]; ring_nf
        have hne : ρ ^ (4 * J) ≠ 0 := by positivity
        calc (1 / ρ ^ (4 * J)) * (2 * Z * ρ ^ (3 * J + 6)) * (6 * ρ ^ (J + 1))
            = 12 * Z * (ρ ^ (3 * J + 6) * ρ ^ (J + 1)) / ρ ^ (4 * J) := by ring
          _ = 12 * Z * ρ ^ 7 := by rw [h47]; field_simp
    _ ≤ 42 * Z := by
        have h7 : ρ ^ 7 ≤ 7 / 2 := by
          have : ρ ^ 7 = ρ ^ 4 * ρ ^ 3 := by ring
          rw [this, hρ4]
          have : ρ ^ 3 ≤ (6 / 5) ^ 3 := pow_le_pow_left₀ hρ0.le hρ2 3
          nlinarith
        nlinarith

/-- **Pair sum of the major arc profile.** -/
theorem pair_sum_PhiT (R : Finset (ZMod N)) (hN : 4 ≤ N) (T : ℕ) :
    ∑ r ∈ R, ∑ r' ∈ R, PhiT N T (r - r') ≤
      32 * (((Jn N + 1 : ℕ) : ℝ) * T * (R.card : ℝ) ^ 2 / 2 ^ Jn N +
        42 * (MT T * (R.card : ℝ) ^ 10) ^ ((1 : ℝ) / 8)) + 8 * T * (R.card : ℝ) ^ 2 / N := by
  obtain ⟨hJ1, hJ2⟩ := Jn_spec N hN
  set J := Jn N
  set k := (R.card : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- pointwise: `Φ_T ≤ 32 Σ_j w_j Kd + 8 T / N`
  have hpt : ∀ s : ZMod N, PhiT N T s ≤
      32 * ∑ j ∈ Fs T, wF j * Kd N (thetaN N s - bF j) + 8 * T / N := by
    intro s
    unfold PhiT
    have h1 : ∑ j ∈ Fs T, wF j * psiN N (thetaN N s - bF j) ≤
        ∑ j ∈ Fs T, wF j * (32 * Kd N (thetaN N s - bF j) + 8 / N) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (psi_le_Kd N hN _) (wF_nonneg j)
    have h2 : ∑ j ∈ Fs T, wF j * (32 * Kd N (thetaN N s - bF j) + 8 / N) =
        32 * ∑ j ∈ Fs T, wF j * Kd N (thetaN N s - bF j) + (8 / N) * ∑ j ∈ Fs T, wF j := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    have h3 : (8 / (N : ℝ)) * ∑ j ∈ Fs T, wF j ≤ 8 * T / N := by
      rw [div_mul_eq_mul_div, mul_comm]
      apply div_le_div_of_nonneg_right _ hNr.le
      nlinarith [sum_wF_le T]
    linarith
  -- the Kd part, level by level
  have hKd : ∑ r ∈ R, ∑ r' ∈ R, ∑ j ∈ Fs T, wF j * Kd N (thetaN N (r - r') - bF j) =
      (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1),
        ∑ j ∈ Fs T, wF j * ∑ r ∈ R, ∑ r' ∈ R, fej (2 ^ i) (thetaN N (r - r') - bF j) := by
    unfold Kd
    simp only [mul_sum]
    rw [sum4_comm, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun r _ =>
      sum_congr rfl fun r' _ => ?_
    ring
  set X : ℕ → ℝ := fun i => ∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ * ‖Pz R (m : ℤ)‖ ^ 2 with hXdef
  have hX0 : ∀ i, 0 ≤ X i := fun i => sum_nonneg fun _ _ => by positivity
  have hlev : ∑ i ∈ range (J + 1),
      ∑ j ∈ Fs T, wF j * ∑ r ∈ R, ∑ r' ∈ R, fej (2 ^ i) (thetaN N (r - r') - bF j) ≤
      ∑ i ∈ range (J + 1), (T * k ^ 2 + 2 * X i) :=
    sum_le_sum fun i _ => level_bound R T i
  have hgeo : (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1), 2 * X i ≤
      42 * (MT T * k ^ 10) ^ ((1 : ℝ) / 8) := by
    apply dyadic_geom J N (MT T * k ^ 10) (Nat.cast_nonneg _)
      (by have : (N : ℝ) < 2 ^ (J + 2) := by exact_mod_cast hJ2
          rw [pow_add] at this; linarith)
      (by have := MT_nonneg T; positivity) X hX0
    intro i hi
    have h2i : 2 ^ i ≤ N := by
      have : 2 ^ i ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := level_X_bound R T i h2i
    simp only [X]
    calc (∑ m ∈ Ico (1 : ℕ) (2 ^ i), ‖GT T (m : ℤ)‖ * ‖Pz R (m : ℤ)‖ ^ 2) ^ 8
        ≤ MT T * 4 ^ i * (N : ℝ) ^ 6 * (R.card : ℝ) ^ 10 := this
      _ = MT T * k ^ 10 * 4 ^ i * (N : ℝ) ^ 6 := by ring
  have hsplit : ∑ i ∈ range (J + 1), (T * k ^ 2 + 2 * X i) =
      ((J + 1 : ℕ) : ℝ) * T * k ^ 2 + ∑ i ∈ range (J + 1), 2 * X i := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]; ring
  have hKdb : ∑ r ∈ R, ∑ r' ∈ R, ∑ j ∈ Fs T, wF j * Kd N (thetaN N (r - r') - bF j) ≤
      ((J + 1 : ℕ) : ℝ) * T * k ^ 2 / 2 ^ J + 42 * (MT T * k ^ 10) ^ ((1 : ℝ) / 8) := by
    rw [hKd]
    calc (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1),
          ∑ j ∈ Fs T, wF j * ∑ r ∈ R, ∑ r' ∈ R, fej (2 ^ i) (thetaN N (r - r') - bF j)
        ≤ (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1), (T * k ^ 2 + 2 * X i) :=
          mul_le_mul_of_nonneg_left hlev (by positivity)
      _ = ((J + 1 : ℕ) : ℝ) * T * k ^ 2 / 2 ^ J +
            (1 / (2 : ℝ) ^ J) * ∑ i ∈ range (J + 1), 2 * X i := by
          rw [hsplit]; ring
      _ ≤ _ := by linarith
  calc ∑ r ∈ R, ∑ r' ∈ R, PhiT N T (r - r')
      ≤ ∑ r ∈ R, ∑ r' ∈ R, (32 * ∑ j ∈ Fs T, wF j * Kd N (thetaN N (r - r') - bF j) +
          8 * T / N) := sum_le_sum fun r _ => sum_le_sum fun r' _ => hpt _
    _ = 32 * ∑ r ∈ R, ∑ r' ∈ R, ∑ j ∈ Fs T, wF j * Kd N (thetaN N (r - r') - bF j) +
          8 * T * k ^ 2 / N := by
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        ring
    _ ≤ _ := by linarith

/-! ### The TT* dichotomy -/

/-- Real-variable end game. -/
theorem dichotomy (k δ A C Z M E : ℝ) (hk : 0 ≤ k) (hδ : 0 < δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (_hZ0 : 0 ≤ Z) (hZ8 : Z ^ 8 = M * k ^ 10)
    (h : (k * δ) ^ 2 ≤ A ^ 2 * k + A * k ^ 2 * E + 1344 * A * C * Z) (hE : A * E ≤ δ ^ 2 / 4) :
    k * δ ^ 2 ≤ 4 * A ^ 2 ∨ k ^ 6 * δ ^ 16 ≤ (3584 * A * C) ^ 8 * M := by
  have hk2 : A * k ^ 2 * E ≤ k ^ 2 * (δ ^ 2 / 4) := by
    have := mul_le_mul_of_nonneg_left hE (sq_nonneg k)
    nlinarith
  have h' : 3 / 4 * (k ^ 2 * δ ^ 2) ≤ A ^ 2 * k + 1344 * A * C * Z := by nlinarith
  rcases le_or_gt (1344 * A * C * Z) (A ^ 2 * k) with h1 | h1
  · left
    rcases hk.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; positivity
    · have : 3 / 4 * (k ^ 2 * δ ^ 2) ≤ 2 * A ^ 2 * k := by linarith
      have : k * (3 / 4 * (k * δ ^ 2)) ≤ k * (2 * A ^ 2) := by nlinarith
      have := le_of_mul_le_mul_left this hpos
      nlinarith
  · right
    set c₀ := 2688 * A * C
    have h2 : 3 / 4 * (k ^ 2 * δ ^ 2) ≤ c₀ * Z := by simp only [c₀]; linarith
    have hc0 : 0 ≤ c₀ := by positivity
    have h3 : (3 / 4 * (k ^ 2 * δ ^ 2)) ^ 8 ≤ (c₀ * Z) ^ 8 :=
      pow_le_pow_left₀ (by positivity) h2 8
    rw [show (c₀ * Z) ^ 8 = c₀ ^ 8 * (M * k ^ 10) by rw [mul_pow, hZ8]] at h3
    rcases hk.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
      have : 0 ≤ M := by
        by_contra hM; push Not at hM
        -- `k = 0` forces `Z = 0`, contradicting `h1`
        have hZ : Z = 0 := by
          have : Z ^ 8 = 0 := by rw [hZ8, ← h0]; ring
          exact pow_eq_zero_iff (by norm_num) |>.1 this
        rw [hZ, ← h0] at h1; simp at h1
      positivity
    · have hk10 : 0 < k ^ 10 := by positivity
      have e1 : (3 / 4 * (k ^ 2 * δ ^ 2)) ^ 8 = (3 / 4) ^ 8 * k ^ 10 * (k ^ 6 * δ ^ 16) := by ring
      have e2 : c₀ ^ 8 * (M * k ^ 10) = k ^ 10 * (c₀ ^ 8 * M) := by ring
      rw [e1, e2] at h3
      have h4 : (3 / 4) ^ 8 * (k ^ 6 * δ ^ 16) ≤ c₀ ^ 8 * M := by
        have : k ^ 10 * ((3 / 4) ^ 8 * (k ^ 6 * δ ^ 16)) ≤ k ^ 10 * (c₀ ^ 8 * M) := by
          linarith
        exact le_of_mul_le_mul_left this hk10
      have e3 : (3584 * A * C) ^ 8 = (4 / 3) ^ 8 * c₀ ^ 8 := by
        simp only [c₀]; rw [← mul_pow]; ring
      rw [e3]
      have : (4 / 3 : ℝ) ^ 8 * ((3 / 4) ^ 8 * (k ^ 6 * δ ^ 16)) = k ^ 6 * δ ^ 16 := by ring
      nlinarith [pow_pos (show (0 : ℝ) < 4 / 3 by norm_num) 8]

/-- **Large spectrum dichotomy from a major arc majorant.** `F` plays `|ν̂|`. -/
theorem spec_dichotomy (hN : 4 ≤ N) (R : Finset (ZMod N)) (F : ZMod N → ℝ) (A C η δ : ℝ)
    (T : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hη : 0 ≤ η) (hδ : 0 < δ) (hF0 : F 0 ≤ A)
    (hmaj : ∀ s : ZMod N, s ≠ 0 → F s ≤ η + C * PhiT N T s)
    (htt : ((R.card : ℝ) * δ) ^ 2 ≤ A * ∑ r ∈ R, ∑ r' ∈ R, F (r - r'))
    (hE : A * (η + C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N) + 8 * T / N)) ≤ δ ^ 2 / 4) :
    (R.card : ℝ) * δ ^ 2 ≤ 4 * A ^ 2 ∨
      (R.card : ℝ) ^ 6 * δ ^ 16 ≤ (3584 * A * C) ^ 8 * MT T := by
  set k := (R.card : ℝ)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hpt : ∀ r ∈ R, ∀ r' ∈ R,
      F (r - r') ≤ (if r = r' then A else 0) + (η + C * PhiT N T (r - r')) := by
    intro r _ r' _
    by_cases h : r = r'
    · subst h
      rw [sub_self, if_pos rfl]
      have : 0 ≤ η + C * PhiT N T 0 := add_nonneg hη (mul_nonneg hC (PhiT_nonneg T 0))
      linarith
    · rw [if_neg h, zero_add]; exact hmaj _ (sub_ne_zero.2 h)
  have hsumF : ∑ r ∈ R, ∑ r' ∈ R, F (r - r') ≤
      k * A + k ^ 2 * η + C * ∑ r ∈ R, ∑ r' ∈ R, PhiT N T (r - r') := by
    calc ∑ r ∈ R, ∑ r' ∈ R, F (r - r')
        ≤ ∑ r ∈ R, ∑ r' ∈ R, ((if r = r' then A else 0) + (η + C * PhiT N T (r - r'))) :=
          sum_le_sum fun r hr => sum_le_sum fun r' hr' => hpt r hr r' hr'
      _ = ∑ r ∈ R, (A + (k * η + C * ∑ r' ∈ R, PhiT N T (r - r'))) := by
          refine sum_congr rfl fun r hr => ?_
          rw [sum_add_distrib, sum_ite_eq R r (fun _ => A), if_pos hr, sum_add_distrib,
            sum_const, nsmul_eq_mul, mul_sum]
      _ = k * A + k ^ 2 * η + C * ∑ r ∈ R, ∑ r' ∈ R, PhiT N T (r - r') := by
          rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_const,
            nsmul_eq_mul, ← mul_sum]
          ring
  have hPhi := pair_sum_PhiT R hN T
  set Z := (MT T * k ^ 10) ^ ((1 : ℝ) / 8) with hZ
  have hZ0 : 0 ≤ Z := Real.rpow_nonneg (by have := MT_nonneg T; positivity) _
  have hZ8 : Z ^ 8 = MT T * k ^ 10 := by
    rw [hZ, ← Real.rpow_natCast, ← Real.rpow_mul (by have := MT_nonneg T; positivity)]
    norm_num
  set E := η + C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T / 2 ^ Jn N) + 8 * T / N)
  have hmain : (k * δ) ^ 2 ≤ A ^ 2 * k + A * k ^ 2 * E + 1344 * A * C * Z := by
    have h1 : A * ∑ r ∈ R, ∑ r' ∈ R, F (r - r') ≤
        A * (k * A + k ^ 2 * η + C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T * k ^ 2 / 2 ^ Jn N +
          42 * Z) + 8 * T * k ^ 2 / N)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      refine hsumF.trans ?_
      have := mul_le_mul_of_nonneg_left hPhi hC
      linarith
    have e : A * (k * A + k ^ 2 * η + C * (32 * (((Jn N + 1 : ℕ) : ℝ) * T * k ^ 2 / 2 ^ Jn N +
          42 * Z) + 8 * T * k ^ 2 / N)) = A ^ 2 * k + A * k ^ 2 * E + 1344 * A * C * Z := by
      simp only [E]; ring
    linarith
  exact dichotomy k δ A C Z (MT T) E hk hδ hA hC hZ0 hZ8 hmain hE

end LeanLab.DensityGoldbach.U1502
