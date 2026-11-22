module

public import LeanLab.Song2020.RouteTypeIIThree
public import LeanLab.Song2020.SPLIT_lambda_sum_per_h

/-!
AI wrote the Lean code, 2026-11-15, the split of the
Type II display typeII_bound.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 6 and 7, from
"By Lemma 2.5 in [2], we have" to the five term display for T(R,S).
This new file holds the last step, "using Lemma 2.4 in [2] to choose L optimally we
obtain" the five term display, from the three term bound in RouteTypeIIThree and the lab's
proved Lemma 2.4, SPLIT_lambda_sum_per_h.gk_lemma_2_4_two_three, the same statement as
Decomp139.gk_lemma_2_4_two_three; Decomp139 is not imported because it sits above this route.
Reading common to the files of this split: x of the print is R S, the size of r s on the
dyadic block, and the passage from R S to n is made at the end by monotonicity; r ~ R is
R at most r < 2 R; the window is |r s - n/3| < y and r s at most t; the phase R_b(m) is
alpha m + h m^gamma. The file defines nothing.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteTypeIIChoose

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Song 2020, page 7, counting step behind the trivial estimate of T(R,S) used when the
window is shorter than S: a set of naturals inside a real interval from a to b has at most
b - a + 1 elements. -/
theorem card_le_of_mem_interval (F : Finset ℕ) (a b : ℝ) (hab : a ≤ b) (hb : 0 ≤ b)
    (hF : ∀ x ∈ F, a ≤ (x : ℝ) ∧ (x : ℝ) < b) : (F.card : ℝ) ≤ b - a + 1 := by
  rcases F.eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
  · subst h0; simp; linarith
  have hsub : F ⊆ Finset.Ico ⌈a⌉₊ ⌈b⌉₊ := by
    intro x hx
    obtain ⟨h1, h2⟩ := hF x hx
    exact Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr h1, Nat.lt_ceil.mpr h2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hx := Finset.mem_Ico.mp (hsub hx0)
  have hle : ⌈a⌉₊ ≤ ⌈b⌉₊ := by omega
  have h1 : (F.card : ℝ) ≤ (⌈b⌉₊ : ℝ) - ⌈a⌉₊ := by
    rw [← Nat.cast_sub hle]; exact_mod_cast hc
  have h2 := Nat.ceil_lt_add_one hb
  have h3 := Nat.le_ceil a
  linarith

/-- Song 2020, page 7: the additive character e(R_b(r s)) in T(R,S) has modulus one. -/
theorem norm_eC_eq (θ : ℝ) : ‖eC θ‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- Song 2020, page 7, the trivial estimate of T(R,S): for each r ~ R the window
|r s - n/3| < y holds at most 2 y / R + 1 values of s, and there are at most 2 R values of
r, so T(R,S) is at most 4 y + 2 R in modulus. It covers the range y < S, where the
differencing step with the interval length y R / x is not available. -/
theorem trivial_bound (γ : ℝ) (n : ℕ) (y : ℝ) (hy : 0 < y) (α : ℝ) (h : ℤ) (t : ℝ)
    (a b : ℕ → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1) (hb : ∀ s, ‖b s‖ ≤ 1) (R S : ℝ) (hR : 1 ≤ R) :
    ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
      ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
        if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
          a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
        else 0‖ ≤ 4 * y + 2 * R := by
  set FR := (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R) with hFR
  set FS := (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S) with hFS
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hR0 : (0 : ℝ) < R := by linarith
  have hin : ∀ r ∈ FR, ‖∑ s ∈ FS,
        if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
          a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
        else 0‖ ≤ 2 * y / R + 1 := by
    intro r hr
    have hrR : R ≤ r := (Finset.mem_filter.mp hr).2.1
    have hr0 : (0 : ℝ) < r := by linarith
    calc _ ≤ ∑ s ∈ FS, ‖(if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
          a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
        else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ FS, (if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro s _
          split_ifs with h1 h2 h2
          · rw [norm_mul, norm_mul, norm_eC_eq, mul_one]
            calc ‖a r‖ * ‖b s‖ ≤ 1 * 1 := mul_le_mul (ha r) (hb s) (norm_nonneg _) zero_le_one
              _ = 1 := mul_one 1
          · exact absurd h1.1 h2
          · simp
          · simp
      _ = ((FS.filter (fun s : ℕ => |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y)).card : ℝ) := by
          rw [Finset.sum_boole]
      _ ≤ ((n : ℝ) / 3 + y) / r - ((n : ℝ) / 3 - y) / r + 1 := by
          apply card_le_of_mem_interval
          · exact div_le_div_of_nonneg_right (by linarith) hr0.le
          · positivity
          · intro s hs
            have hw := abs_lt.mp (Finset.mem_filter.mp hs).2
            push_cast at hw
            constructor
            · rw [div_le_iff₀ hr0]; nlinarith [hw.1]
            · rw [lt_div_iff₀ hr0]; nlinarith [hw.2]
      _ = 2 * y / r + 1 := by ring
      _ ≤ 2 * y / R + 1 := by
          have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * y) hR0 hrR
          linarith
  have hcard : (FR.card : ℝ) ≤ 2 * R - R + 1 := by
    apply card_le_of_mem_interval
    · linarith
    · linarith
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
  calc _ ≤ ∑ r ∈ FR, ‖∑ s ∈ FS,
        if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
          a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ FR, (2 * y / R + 1) := Finset.sum_le_sum hin
    _ = (FR.card : ℝ) * (2 * y / R + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * R) * (2 * y / R + 1) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 4 * y + 2 * R := by field_simp; ring

/-- Song 2020, page 7, "choose L optimally": passing from the real u of Lemma 2.4 to the
integer L equal to its floor costs at most a factor 2 in the negative powers. -/
theorem rpow_neg_floor_le (L u b : ℝ) (hL : 0 < L) (hLu : L ≤ u) (hu : u ≤ 2 * L) (hb : 0 < b)
    (hb1 : b ≤ 1) : L ^ (-b) ≤ 2 * u ^ (-b) := by
  have hu0 : 0 < u := by linarith
  have h1 : u ^ b ≤ (2 * L) ^ b := Real.rpow_le_rpow hu0.le hu hb.le
  rw [Real.mul_rpow (by norm_num) hL.le] at h1
  have h2 : (2 : ℝ) ^ b ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
    rwa [Real.rpow_one] at this
  have hLb : 0 < L ^ b := Real.rpow_pos_of_pos hL b
  have hub : 0 < u ^ b := Real.rpow_pos_of_pos hu0 b
  have h3 : u ^ b ≤ 2 * L ^ b := by nlinarith
  rw [Real.rpow_neg hL.le, Real.rpow_neg hu0.le, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hLb hub]
  linarith

/-- Song 2020, page 7, the five balances of Lemma 2.4 in [2] for the three term bound, with
x = R S: the two cross terms and the three end point terms are the five monomials of the
display for T(R,S). -/
theorem balance_identities (γ R S y A : ℝ) (hR : 0 < R) (hS : 0 < S) (hy : 0 < y)
    (hA : 0 < A) :
    ((R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (γ / 4 - 3 / 4) * y ^ ((1 : ℝ) / 2) *
        A ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 : ℝ) / 4)) ^
        (1 / ((1 : ℝ) / 4 + 1 / 2)) =
      R ^ (-(1 : ℝ) / 6) * ((R * S) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) * A ^ ((1 : ℝ) / 6)) ∧
    ((R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (γ / 4 - 3 / 4) * y ^ ((1 : ℝ) / 2) *
        A ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 4) *
        (R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (1 / 4 - γ / 4) * A ^ (-(1 : ℝ) / 4)) ^
          ((1 : ℝ) / 4)) ^ (1 / ((1 : ℝ) / 4 + 1 / 4)) =
      R ^ (-(1 : ℝ) / 4) * ((R * S) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) ∧
    R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (γ / 4 - 3 / 4) * y ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 4) =
      R ^ (-(1 : ℝ) / 4) * ((R * S) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 4)) ∧
    R * S * S ^ (-((1 : ℝ) / 2)) = R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 : ℝ) / 2) ∧
    R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (1 / 4 - γ / 4) * A ^ (-(1 : ℝ) / 4) *
        S ^ (-((1 : ℝ) / 4)) = (R * S) ^ (1 - γ / 4) * A ^ (-(1 : ℝ) / 4) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, R = Real.exp ρ := ⟨Real.log R, (Real.exp_log hR).symm⟩
  obtain ⟨σ, rfl⟩ : ∃ σ, S = Real.exp σ := ⟨Real.log S, (Real.exp_log hS).symm⟩
  obtain ⟨η, rfl⟩ : ∃ η, y = Real.exp η := ⟨Real.log y, (Real.exp_log hy).symm⟩
  obtain ⟨κ, rfl⟩ : ∃ κ, A = Real.exp κ := ⟨Real.log A, (Real.exp_log hA).symm⟩
  simp only [← Real.exp_mul, ← Real.exp_add]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> · congr 1; ring

/-- Song 2020, page 7, "using Lemma 2.4 in [2] to choose L optimally we obtain": from the
three term bound valid for every integer L with 1 <= L <= S, the five term bound with
x = R S in place of n, by SPLIT_lambda_sum_per_h.gk_lemma_2_4_two_three and L the floor of its u. -/
theorem choose_L : ∃ C4 : ℝ, 0 ≤ C4 ∧ ∀ (γ R S y A T C3 : ℝ), 1 ≤ R → 1 ≤ S → 0 < y → 0 < A →
    0 ≤ C3 →
    (∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ S → T ≤ C3 * (R * S * (L : ℝ) ^ (-(1 : ℝ) / 2) +
        R ^ ((3 : ℝ) / 4) * S * (L : ℝ) ^ ((1 : ℝ) / 4) * (R * S) ^ (γ / 4 - 3 / 4) *
          y ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 4) +
        R ^ ((3 : ℝ) / 4) * S * (L : ℝ) ^ (-(1 : ℝ) / 4) * (R * S) ^ (1 / 4 - γ / 4) *
          A ^ (-(1 : ℝ) / 4))) →
    T ≤ 2 * C3 * C4 *
      (R ^ (-(1 : ℝ) / 6) * ((R * S) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
          A ^ ((1 : ℝ) / 6)) +
        (R * S) ^ (1 - γ / 4) * A ^ (-(1 : ℝ) / 4) +
        R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 : ℝ) / 2) +
        R ^ (-(1 : ℝ) / 4) * ((R * S) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
          A ^ ((1 : ℝ) / 4)) +
        R ^ (-(1 : ℝ) / 4) * ((R * S) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))) := by
  obtain ⟨C4, hC4, hgk⟩ := LeanLab.Song2020.SPLIT_lambda_sum_per_h.gk_lemma_2_4_two_three ((1 : ℝ) / 4) (1 : ℝ) ((1 : ℝ) / 2)
    ((1 : ℝ) / 4) (1 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C4, hC4, ?_⟩
  intro γ R S y A T C3 hR hS hy hA hC3 hT
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  obtain ⟨i1, i2, i3, i4, i5⟩ := balance_identities γ R S y A hR0 hS0 hy hA
  set P1 : ℝ := R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (γ / 4 - 3 / 4) * y ^ ((1 : ℝ) / 2) *
    A ^ ((1 : ℝ) / 4) with hP1
  set Q2 : ℝ := R ^ ((3 : ℝ) / 4) * S * (R * S) ^ (1 / 4 - γ / 4) * A ^ (-(1 : ℝ) / 4) with hQ2
  have hP1n : 0 ≤ P1 := by positivity
  have hQ2n : 0 ≤ Q2 := by positivity
  have hXn : 0 ≤ R * S := by positivity
  obtain ⟨u, hu1, huS, hu⟩ := hgk P1 0 (R * S) Q2 0 hP1n le_rfl hXn hQ2n le_rfl S hS
  have z1 : (0 : ℝ) ^ ((1 : ℝ) / 4) = 0 := Real.zero_rpow (by norm_num)
  have z2 : (0 : ℝ) ^ ((1 : ℝ) / 2) = 0 := Real.zero_rpow (by norm_num)
  have z3 : (0 : ℝ) ^ (1 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have z4 : (0 : ℝ) ^ (1 / ((1 : ℝ) / 4 + 1)) = 0 := Real.zero_rpow (by norm_num)
  have z5 : (0 : ℝ) ^ (1 / ((1 : ℝ) + 1 / 2)) = 0 := Real.zero_rpow (by norm_num)
  have z6 : (0 : ℝ) ^ (1 / ((1 : ℝ) + 1 / 4)) = 0 := Real.zero_rpow (by norm_num)
  have z7 : (0 : ℝ) ^ (1 / ((1 : ℝ) + 1)) = 0 := Real.zero_rpow (by norm_num)
  simp only [z1, z2, z3, z4, z5, z6, z7, zero_mul, mul_zero, add_zero] at hu
  rw [i1, i2, i4, i5] at hu
  have hu0 : 0 < u := by linarith
  have hL1 : 1 ≤ ⌊u⌋₊ := Nat.floor_pos.mpr hu1
  have hLu : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le hu0.le
  have hLt : u < ((⌊u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one u
  have hL1r : (1 : ℝ) ≤ ((⌊u⌋₊ : ℕ) : ℝ) := by exact_mod_cast hL1
  have hL := hT ⌊u⌋₊ hL1 (hLu.trans huS)
  have e1 : ((⌊u⌋₊ : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) ≤ 2 * u ^ (-((1 : ℝ) / 2)) := by
    rw [neg_div]
    exact rpow_neg_floor_le _ u _ (by linarith) hLu (by linarith) (by norm_num) (by norm_num)
  have e3 : ((⌊u⌋₊ : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) ≤ 2 * u ^ (-((1 : ℝ) / 4)) := by
    rw [neg_div]
    exact rpow_neg_floor_le _ u _ (by linarith) hLu (by linarith) (by norm_num) (by norm_num)
  have e2 : ((⌊u⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ u ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by linarith) hLu (by norm_num)
  have a1 := mul_le_mul_of_nonneg_left e1 hXn
  have a2 := mul_le_mul_of_nonneg_left e2 hP1n
  have a3 := mul_le_mul_of_nonneg_left e3 hQ2n
  have p1 : 0 ≤ P1 * u ^ ((1 : ℝ) / 4) := by positivity
  have hL' : T ≤ C3 * (R * S * ((⌊u⌋₊ : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) +
      P1 * ((⌊u⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / 4) + Q2 * ((⌊u⌋₊ : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) := by
    rw [hP1, hQ2]
    calc T ≤ _ := hL
      _ = _ := by ring
  have b1 : T ≤ C3 * (2 * (P1 * u ^ ((1 : ℝ) / 4) + R * S * u ^ (-((1 : ℝ) / 2)) +
      Q2 * u ^ (-((1 : ℝ) / 4)))) :=
    le_trans hL' (mul_le_mul_of_nonneg_left (by linarith) hC3)
  have b2 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)) hC3
  have b3 := b1.trans b2
  rw [i3] at b3
  calc T ≤ _ := b3
    _ = _ := by ring

/-- Proved from three_term and gk_lemma_2_4_two_three: Song 2020, page 7, "using Lemma 2.4
in [2] to choose L optimally we obtain
T(R,S) << R^(-1/6) n^((gamma+3)/6) y^(1/3) |h|^(1/6) + n^(1-gamma/4) |h|^(-1/4) + R^(1/2)
n^(1/2) + R^(-1/4) n^((gamma+1)/4) y^(1/2) |h|^(1/4) + n^(3/4) y^(1/4) R^(-1/4)". Same
statement as RouteVaughanTypeII.typeII_bound. Proof: N0 = 1; if no pair r, s passes the
window test then T = 0; otherwise R S <= n; for y < S the trivial bound 4 y + 2 R is below
the third and fifth terms; for S <= y the three term bound and Lemma 2.4, then R S <= n. -/
theorem typeII_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ a b : ℕ → ℂ, (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖b s‖ ≤ 1) →
            ∀ R S : ℝ, 1 ≤ R → 1 ≤ S →
            ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
                if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
                  a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
                else 0‖ ≤
              C * (n : ℝ) ^ ε *
                (R ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                R ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4)) +
                R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))) := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C3, hC3, h3⟩ := RouteTypeIIThree.three_term γ (by linarith) hγ1
  obtain ⟨C4, hC4, h4⟩ := choose_L
  refine ⟨4 + 2 * C3 * C4, by positivity, 1, ?_⟩
  intro n hn y hny hy3 α h hh t a b ha hb R S hR hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy : 0 < y := lt_of_le_of_lt (Real.rpow_nonneg (Nat.cast_nonneg n) _) hny
  have hA : (1 : ℝ) ≤ |(h : ℝ)| := by
    have := Int.one_le_abs hh
    exact_mod_cast this
  have hA0 : (0 : ℝ) < |(h : ℝ)| := by linarith
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hne : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  have hCC : 0 ≤ C3 * C4 := mul_nonneg hC3 hC4
  have t1 : 0 ≤ R ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
      |(h : ℝ)| ^ ((1 : ℝ) / 6)) := by positivity
  have t2 : 0 ≤ (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) := by positivity
  have t3 : 0 ≤ R ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have t4 : 0 ≤ R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
      |(h : ℝ)| ^ ((1 : ℝ) / 4)) := by positivity
  have t5 : 0 ≤ R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) := by
    positivity
  have key : ∀ T E : ℝ, 0 ≤ E → T ≤ (4 + 2 * C3 * C4) * E →
      T ≤ (4 + 2 * C3 * C4) * (n : ℝ) ^ ε * E := by
    intro T E hE hTE
    have hc : 0 ≤ (4 + 2 * C3 * C4) * E := by positivity
    calc T ≤ (4 + 2 * C3 * C4) * E := hTE
      _ ≤ ((4 + 2 * C3 * C4) * E) * (n : ℝ) ^ ε := le_mul_of_one_le_right hc hne
      _ = _ := by ring
  apply key _ _ (by linarith)
  by_cases hex : ∃ r s : ℕ, R ≤ (r : ℝ) ∧ S ≤ (s : ℝ) ∧ |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y
  swap
  · rw [Finset.sum_eq_zero, norm_zero]
    · have : 0 ≤ 4 + 2 * C3 * C4 := by positivity
      apply mul_nonneg this (by linarith)
    · intro r hr
      apply Finset.sum_eq_zero
      intro s hs
      split_ifs with hw
      · exact absurd ⟨r, s, (Finset.mem_filter.mp hr).2.1, (Finset.mem_filter.mp hs).2.1,
          hw.1⟩ hex
      · rfl
  obtain ⟨r, s, hrR, hsS, hw⟩ := hex
  have hX : R * S ≤ n := by
    have h1 : R * S ≤ (r : ℝ) * s := mul_le_mul hrR hsS hS0.le (by linarith)
    have h2 := (abs_lt.mp hw).2
    push_cast at h2
    linarith
  have hX0 : 0 ≤ R * S := by positivity
  by_cases hyS : S ≤ y
  · have hbd := h4 γ R S y |(h : ℝ)| _ C3 hR hS hy hA0 hC3
      (fun L hL1 hLS => h3 n y hy α t h hh a b ha hb R S hR hS hyS L hL1 hLS)
    have m1 := Real.rpow_le_rpow hX0 hX (show 0 ≤ (γ + 3) / 6 by linarith)
    have m2 := Real.rpow_le_rpow hX0 hX (show 0 ≤ 1 - γ / 4 by linarith)
    have m3 := Real.rpow_le_rpow hX0 hX (show 0 ≤ (1 : ℝ) / 2 by norm_num)
    have m4 := Real.rpow_le_rpow hX0 hX (show 0 ≤ (γ + 1) / 4 by linarith)
    have m5 := Real.rpow_le_rpow hX0 hX (show 0 ≤ (3 : ℝ) / 4 by norm_num)
    have hmono : (R ^ (-(1 : ℝ) / 6) * ((R * S) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
          |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
        (R * S) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
        R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 : ℝ) / 2) +
        R ^ (-(1 : ℝ) / 4) * ((R * S) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
          |(h : ℝ)| ^ ((1 : ℝ) / 4)) +
        R ^ (-(1 : ℝ) / 4) * ((R * S) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))) ≤
        (R ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
          |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
        (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
        R ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) +
        R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
          |(h : ℝ)| ^ ((1 : ℝ) / 4)) +
        R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4))) := by
      gcongr
    have hc : 0 ≤ 2 * C3 * C4 := by positivity
    have := mul_le_mul_of_nonneg_left hmono hc
    linarith [hbd, this, t1, t2, t3, t4, t5]
  · have hyS : y < S := not_le.mp hyS
    have htr := trivial_bound γ n y hy α h t a b ha hb R S hR
    have hRn : R ≤ n := le_trans (le_mul_of_one_le_right hR0.le hS) hX
    have c3 : R ≤ R ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have e : R = R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hR0]; norm_num
      have m := Real.rpow_le_rpow hR0.le hRn (show 0 ≤ (1 : ℝ) / 2 by norm_num)
      calc R = R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) := e
        _ ≤ _ := mul_le_mul_of_nonneg_left m (by positivity)
    have c5 : y ≤ R ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) := by
      have k1 : R ^ (-(1 : ℝ) / 4) * R ^ ((1 : ℝ) / 4) = 1 := by
        rw [← Real.rpow_add hR0]; norm_num
      have k2 : R ^ ((1 : ℝ) / 4) ≤ R ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
      have k3 : (R * S) ^ ((3 : ℝ) / 4) = R ^ ((3 : ℝ) / 4) * S ^ ((3 : ℝ) / 4) :=
        Real.mul_rpow hR0.le hS0.le
      have k4 : y ^ ((3 : ℝ) / 4) ≤ S ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow hy.le hyS.le (by norm_num)
      have k5 := Real.rpow_le_rpow hX0 hX (show 0 ≤ (3 : ℝ) / 4 by norm_num)
      have k6 : y = y ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hy]; norm_num
      have k7 : y ^ ((3 : ℝ) / 4) ≤ R ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) := by
        calc y ^ ((3 : ℝ) / 4) ≤ S ^ ((3 : ℝ) / 4) := k4
          _ = R ^ (-(1 : ℝ) / 4) * (R ^ ((1 : ℝ) / 4) * S ^ ((3 : ℝ) / 4)) := by
              rw [← mul_assoc, k1, one_mul]
          _ ≤ R ^ (-(1 : ℝ) / 4) * (R ^ ((3 : ℝ) / 4) * S ^ ((3 : ℝ) / 4)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right k2 (by positivity)
          _ ≤ _ := by
              rw [← k3]
              exact mul_le_mul_of_nonneg_left k5 (by positivity)
      calc y = y ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) := k6
        _ ≤ (R ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4)) * y ^ ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right k7 (by positivity)
        _ = _ := by ring
    linarith [htr, c3, c5, t1, t2, t3, t4, t5, mul_nonneg hCC t1, mul_nonneg hCC t2,
      mul_nonneg hCC t3, mul_nonneg hCC t4, mul_nonneg hCC t5]

end
end LeanLab.Song2020.RouteTypeIIChoose
