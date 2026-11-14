module

public import LeanLab.Linnik.MajorArcEnergy.Display13
public import LeanLab.Linnik.MajorArcEnergy.Leaves1517
public import LeanLab.Linnik.MajorArcEnergy.Display17

/-!
Gallagher 1975 P0094 pp.131 and 132 displays 15 to 17, the positive exceptional
conductor case of the major arc reduction.
CONDITIONAL ON the leaves in Leaves13.lean and Leaves1517.lean.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries ramanujanSum excSet)
open LeanLab.Linnik.U7204 (Sg)

set_option maxHeartbeats 1000000 in
/-- Gallagher 1975 pp.131 and 132, the real arithmetic of displays 15 to 17 combined with
display 13: the terms of displays 3 and 11, the pairs bounded by display 8 with
||A(1)|| at most Km N^(1/2) L^(-1) + ||R|| and ||A(chi~)|| at most Km N^(1/2) L^(-1) + ||R~||,
and the three exceptional pairs bounded by W M^2 with W the sum of C_n(chi~, 1), C_n(1, chi~)
and C_n(chi~, chi~), at most K5 n/phi(n) r phi((n, r))/phi(r)^2 by display 17 and at most
3 K2 n/phi(n) by display 7, combine to the normalized form. Here E is ||R|| + ||R~|| + S. -/
theorem display1517_algebra {cfe K1 K2 K3 K5 Km Q tw lp d sN R Rt S a1 ae W ew Pw : ℝ}
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK5 : 0 ≤ K5) (hKm : 0 ≤ Km)
    (hsN : 0 < sN) (hQ : Q = sN ^ 2) (htw : 0 ≤ tw) (hR : 0 ≤ R) (hRt : 0 ≤ Rt)
    (hS : 0 ≤ S) (ha1 : a1 ≤ Km * sN + R) (hae : ae ≤ Km * sN + Rt)
    (hX : 0 ≤ lp * d) (hPw : Pw ≤ Q * tw * (lp * d)) (hew : 0 ≤ ew)
    (hW0 : 0 ≤ W) (hW1 : W ≤ K5 * tw * ew) (hW2 : W ≤ 3 * K2 * tw)
    (hcfe : cfe ≤ K1 * Pw + K3 * tw * (Q * d * lp + sN * R + R ^ 2) +
      K2 * tw * (a1 + ae) * S + K2 * tw * S * (a1 + ae + S) +
      W * (Km * sN + (R + Rt + S)) ^ 2) :
    cfe ≤ (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * Q * tw *
      (lp * d + (1 + (R + Rt + S) / sN) * ((R + Rt + S) / sN) + ew) := by
  set E := R + Rt + S with hE
  have hE0 : 0 ≤ E := by positivity
  have hY : Q * ((1 + E / sN) * (E / sN)) = sN * E + E ^ 2 := by
    rw [hQ]; field_simp
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set X := Q * tw * (lp * d) with hXdef
  set Y := sN * E + E ^ 2 with hYdef
  have hX0 : 0 ≤ X := by positivity
  have hsE : 0 ≤ sN * E := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hZ0 : 0 ≤ Q * tw * ew := by positivity
  have hRE : R ≤ E := by rw [hE]; linarith
  have hSE : S ≤ E := by rw [hE]; linarith
  have hRRtE : R + Rt ≤ E := by rw [hE]; linarith
  have t1 : K1 * Pw ≤ K1 * X := mul_le_mul_of_nonneg_left hPw hK1
  have t2 : K3 * tw * (Q * d * lp + sN * R + R ^ 2) ≤ K3 * X + K3 * tw * Y := by
    have : sN * R + R ^ 2 ≤ Y := by
      rw [hYdef]; gcongr
    have hK3tw : 0 ≤ K3 * tw := mul_nonneg hK3 htw
    have := mul_le_mul_of_nonneg_left this hK3tw
    have e : K3 * tw * (Q * d * lp + sN * R + R ^ 2) =
      K3 * X + K3 * tw * (sN * R + R ^ 2) := by rw [hXdef]; ring
    linarith
  have hsum : a1 + ae ≤ 2 * Km * sN + (R + Rt) := by linarith
  have hu1 : (a1 + ae) * S ≤ 2 * Km * (sN * E) + E ^ 2 := by
    have h1 : (a1 + ae) * S ≤ (2 * Km * sN + (R + Rt)) * S :=
      mul_le_mul_of_nonneg_right hsum hS
    have h2 : sN * S ≤ sN * E := mul_le_mul_of_nonneg_left hSE hsN.le
    have h3 : (R + Rt) * S ≤ E * E := mul_le_mul hRRtE hSE hS hE0
    have h4 : 2 * Km * (sN * S) ≤ 2 * Km * (sN * E) := by
      apply mul_le_mul_of_nonneg_left h2; positivity
    have e1 : (2 * Km * sN + (R + Rt)) * S = 2 * Km * (sN * S) + (R + Rt) * S := by ring
    have e2 : E ^ 2 = E * E := by ring
    linarith
  have hu2 : S * (a1 + ae + S) ≤ 2 * Km * (sN * E) + E ^ 2 := by
    have h1 : S * (a1 + ae + S) ≤ S * (2 * Km * sN + E) := by
      apply mul_le_mul_of_nonneg_left _ hS; linarith
    have h2 : sN * S ≤ sN * E := mul_le_mul_of_nonneg_left hSE hsN.le
    have h3 : S * E ≤ E * E := mul_le_mul_of_nonneg_right hSE hE0
    have h4 : 2 * Km * (sN * S) ≤ 2 * Km * (sN * E) := by
      apply mul_le_mul_of_nonneg_left h2; positivity
    have e1 : S * (2 * Km * sN + E) = 2 * Km * (sN * S) + S * E := by ring
    have e2 : E ^ 2 = E * E := by ring
    linarith
  have hK2tw : 0 ≤ K2 * tw := mul_nonneg hK2 htw
  have t3 : K2 * tw * (a1 + ae) * S ≤ K2 * tw * (2 * Km * (sN * E) + E ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hu1 hK2tw
  have t4 : K2 * tw * S * (a1 + ae + S) ≤ K2 * tw * (2 * Km * (sN * E) + E ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hu2 hK2tw
  have hM : (Km * sN + E) ^ 2 ≤ 2 * Km ^ 2 * Q + 2 * E ^ 2 := by
    rw [hQ]; nlinarith [sq_nonneg (Km * sN - E)]
  have t5 : W * (Km * sN + E) ^ 2 ≤ 2 * Km ^ 2 * K5 * (Q * tw * ew) + 6 * K2 * tw * E ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hM hW0
    have hKQ : 0 ≤ 2 * Km ^ 2 * Q := by positivity
    have h2 : W * (2 * Km ^ 2 * Q) ≤ K5 * tw * ew * (2 * Km ^ 2 * Q) :=
      mul_le_mul_of_nonneg_right hW1 hKQ
    have h3 : W * (2 * E ^ 2) ≤ 3 * K2 * tw * (2 * E ^ 2) :=
      mul_le_mul_of_nonneg_right hW2 (by positivity)
    have e1 : W * (2 * Km ^ 2 * Q + 2 * E ^ 2) = W * (2 * Km ^ 2 * Q) + W * (2 * E ^ 2) := by
      ring
    have e2 : K5 * tw * ew * (2 * Km ^ 2 * Q) = 2 * Km ^ 2 * K5 * (Q * tw * ew) := by ring
    have e3 : 3 * K2 * tw * (2 * E ^ 2) = 6 * K2 * tw * E ^ 2 := by ring
    linarith
  have hgoal : (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * Q * tw *
      (lp * d + (1 + E / sN) * (E / sN) + ew) =
      (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * X +
      (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * (tw * Y) +
      (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * (Q * tw * ew) := by
    rw [← hY, hXdef]; ring
  rw [hgoal]
  have hA : (K1 + K3) * X ≤ (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * X := by
    apply mul_le_mul_of_nonneg_right _ hX0
    have : 0 ≤ 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5 := by positivity
    linarith
  have htY : 0 ≤ tw * Y := mul_nonneg htw hY0
  have hsEY : sN * E ≤ Y := by rw [hYdef]; linarith [sq_nonneg E]
  have hE2Y : E ^ 2 ≤ Y := by rw [hYdef]; linarith
  have hB : K3 * tw * Y + K2 * tw * (2 * Km * (sN * E) + E ^ 2) +
      K2 * tw * (2 * Km * (sN * E) + E ^ 2) + 6 * K2 * tw * E ^ 2 ≤
      (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * (tw * Y) := by
    have e1 : K2 * tw * Km * (sN * E) ≤ K2 * tw * Km * Y :=
      mul_le_mul_of_nonneg_left hsEY (by positivity)
    have e2 : K2 * tw * E ^ 2 ≤ K2 * tw * Y := mul_le_mul_of_nonneg_left hE2Y hK2tw
    have e3 : 0 ≤ K1 * (tw * Y) := mul_nonneg hK1 htY
    have e4 : 0 ≤ 2 * Km ^ 2 * K5 * (tw * Y) := by positivity
    have e5 : (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * (tw * Y) =
      K1 * (tw * Y) + K3 * tw * Y + 4 * (K2 * tw * Km * Y) + 8 * (K2 * tw * Y) +
        2 * Km ^ 2 * K5 * (tw * Y) := by ring
    have e6 : K2 * tw * (2 * Km * (sN * E) + E ^ 2) =
      2 * (K2 * tw * Km * (sN * E)) + K2 * tw * E ^ 2 := by ring
    have e7 : 6 * K2 * tw * E ^ 2 = 6 * (K2 * tw * E ^ 2) := by ring
    linarith
  have hC : 2 * Km ^ 2 * K5 * (Q * tw * ew) ≤
      (K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5) * (Q * tw * ew) := by
    apply mul_le_mul_of_nonneg_right _ hZ0
    have : 0 ≤ K1 + K3 + 4 * K2 * Km + 8 * K2 := by positivity
    linarith
  linarith


/-- Gallagher 1975 p.131 before display 15: ||T~|| is at most 2 N^(1/2) L^(-1) for N large,
uniformly in gamma at most 1, by Parseval on the full period as for T, since m^(gamma - 1)
is at most 1, and J(0) asymptotic to N L^(-2). -/
theorem exceptionalMain_norm_eventually :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ γ : ℝ, γ ≤ 1 → ∀ R : ℝ, R ≤ 1 / 2 →
      Real.sqrt (∫ β in Set.Icc (-R) R, ‖exceptionalMain N γ β‖ ^ 2) ≤
        2 * (Real.sqrt N / Real.log N) := by
  have h := LeanLab.Linnik.Decomp1532b.J0_asymp.eventually
    (gt_mem_nhds (by norm_num : (1 : ℝ) < 4))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max 2 N₀, fun N hN γ hγ R hR => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hJ := ((div_lt_iff₀ (div_pos hn (sq_pos_of_pos hl))).mp
    (hN₀ N ((le_max_right _ _).trans hN))).le
  have hK : 2 * (Real.sqrt N / Real.log N) =
      Real.sqrt (4 * ((N : ℝ) / Real.log N ^ 2)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq hl.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hK]
  exact Real.sqrt_le_sqrt ((LeanLab.Linnik.Decomp486c.exceptionalMain_window_mean_le N γ hγ R hR).trans hJ)

/-- Gallagher 1975 p.131 before display 15: from A(chi~) = -T~ + R~, the triangle inequality
in L2 gives ||A(chi~)|| at most ||T~|| + ||R~||. -/
theorem exc_ampNorm_le (N : ℕ) (P γ : ℝ) (e : PChar) :
    ampNorm N P e ≤
      Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N), ‖exceptionalMain N γ β‖ ^ 2) +
      Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N),
        ‖primeAmplitude e.2 N β + exceptionalMain N γ β‖ ^ 2) := by
  have hmink := sqrt_integral_add_le
    (fun β => primeAmplitude e.2 N β + exceptionalMain N γ β)
    (fun β => -exceptionalMain N γ β)
    ((continuous_primeAmplitude e.2 N).add (continuous_exceptionalMain N γ))
    (continuous_exceptionalMain N γ).neg (-(P / N)) (P / N)
  simp only [add_neg_cancel_right, norm_neg] at hmink
  unfold ampNorm
  linarith

/-- Gallagher 1975 p.129 below display 4: C_n(chi, chi') is nonnegative. -/
theorem pairWeight_nonneg (P : ℝ) (n : ℤ) (x y : PChar) : 0 ≤ pairWeight P n x y := by
  unfold pairWeight
  exact Finset.sum_nonneg fun q _ => by positivity

/-- Gallagher 1975 p.131 after display 14: the split of the pairs into the four pairs
from 1 and chi~, the pairs (1 or chi~, chi) with chi not 1 or chi~, and the pairs
(chi, chi') with chi not 1 or chi~. -/
theorem double_sum_split_two (F : Finset PChar) (u v : PChar) (hu : u ∈ F) (hv : v ∈ F)
    (huv : u ≠ v) (f : PChar → PChar → ℂ) :
    ∑ x ∈ F, ∑ y ∈ F, f x y =
      f u u + f u v + f v u + f v v +
        ∑ x ∈ ({u, v} : Finset PChar), ∑ y ∈ (F.erase u).erase v, f x y +
        ∑ x ∈ (F.erase u).erase v, ∑ y ∈ F, f x y := by
  have hs : ∀ g : PChar → ℂ, ∑ x ∈ F, g x = g u + g v + ∑ x ∈ (F.erase u).erase v, g x := by
    intro g
    rw [← Finset.add_sum_erase F g hu,
      ← Finset.add_sum_erase (F.erase u) g (Finset.mem_erase.mpr ⟨huv.symm, hv⟩)]
    ring
  have h1 := hs (fun x => ∑ y ∈ F, f x y)
  have h2 := hs (f u)
  have h3 := hs (f v)
  rw [h1, h2, h3, Finset.sum_pair huv]
  ring

/-- Gallagher 1975 p.127 exceptional zero convention: the character to modulus 1 has
no exceptional zero, since zeta has no zero in a real neighborhood of 1. -/
theorem zeta_ne_zero_near_one : ∃ ε : ℝ, 0 < ε ∧ ∀ γ : ℝ, 1 - ε < γ → γ < 1 →
    riemannZeta (γ : ℂ) ≠ 0 := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp riemannZeta_eventually_ne_zero_nhds_one
  refine ⟨ε, hε, fun γ h1 h2 => h ?_⟩
  rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

/-- Gallagher 1975 p.131 after display 14: when chi~ to conductor r other than 1 is the
only primitive character to modulus r with a zero at gamma, the corrected energy is
||R|| + ||R~|| + the sum of ||A(chi)|| over chi not 1 or chi~, with A(chi~) = -T~ + R~. -/
theorem correctedEnergy_exc_eq (N : ℕ) (θ γ : ℝ) (r : ℕ) (e : PChar)
    (hP : 1 ≤ (N : ℝ) ^ θ) (he : e ∈ family ((N : ℝ) ^ θ)) (hre : r = e.1 + 1)
    (hr1 : r ≠ 1) (hz : e.2.LFunction (γ : ℂ) = 0)
    (hU : ∀ x ∈ family ((N : ℝ) ^ θ), x.1 + 1 = r → x.2.LFunction (γ : ℂ) = 0 → x = e) :
    correctedEnergy N θ r γ = remNorm N ((N : ℝ) ^ θ) +
      Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
        ‖primeAmplitude e.2 N β + exceptionalMain N γ β‖ ^ 2) +
      ∑ x ∈ ((family ((N : ℝ) ^ θ)).erase one).erase e, ampNorm N ((N : ℝ) ^ θ) x := by
  have hone : one ∈ family ((N : ℝ) ^ θ) := one_mem_family hP
  have hne : e ≠ one := by
    rintro rfl
    exact hr1 (by simp [hre, one])
  unfold correctedEnergy
  rw [← Finset.sum_sigma (range ⌊(N : ℝ) ^ θ⌋₊)
    (fun k => (univ : Finset (DirichletCharacter ℂ (k + 1))).filter fun χ => χ.IsPrimitive)
    (fun x => Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
      ‖correctedAmplitude x.2 N r γ β‖ ^ 2))]
  change ∑ x ∈ family ((N : ℝ) ^ θ), _ = _
  rw [← Finset.add_sum_erase _ _ hone,
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, he⟩), ← add_assoc]
  have hr1' : ¬ (0 + 1 = r) := by omega
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · simp [remNorm, one, correctedAmplitude, hr1']
  · simp [correctedAmplitude, ← hre, hz, hr1]
  · apply Finset.sum_congr rfl
    intro x hx
    have hxe := (Finset.mem_erase.mp hx).1
    have hx1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have hxF := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    have hx0 : x.1 + 1 ≠ 1 := by
      intro h0
      apply hx1
      obtain ⟨k, χ⟩ := x
      simp only at h0
      have : k = 0 := by omega
      subst this
      simp only [one, DirichletCharacter.level_one χ]
    have hxr : ¬ (x.1 + 1 = r ∧ x.2.LFunction (γ : ℂ) = 0) := fun h => hxe (hU x hxF h.1 h.2)
    have hx0' : x.1 ≠ 0 := by omega
    simp [ampNorm, correctedAmplitude, hx0', hxr]


set_option maxHeartbeats 1000000 in
/-- CONDITIONAL ON `major_arc_pair_expansion_of_steps`, `pair_weight_bound_of_cited`,
`principal_pair_sum_of_leaves` and `exceptional_weight_bound_of_cited`, hence only on the
CITED-LEFT leaves induced_cn_bound, singular_tail_cited and singular_weighted_sums_cited. Gallagher 1975 pp.131 and 132 displays 15 to 17: with the
exceptional character chi~ to conductor r, the pairs avoiding chi~ are treated as in
display 13, display 15 bounds the pairs of chi~ with chi not 1 or chi~, and displays 16 and
17 bound the remaining pairs by N L^(-2) n/phi(n) r phi((n, r))/phi(r)^2.
The statement is exactly that of `Decomp486b.major_arc_energy_exceptional`. -/
theorem major_arc_energy_exceptional_split
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  obtain ⟨K1, θ1, hK1, hθ1, hexp⟩ := major_arc_pair_expansion_of_steps hExpansion
  obtain ⟨K2, hK2, hpw⟩ := pair_weight_bound_of_cited
  obtain ⟨K3, θ3, hK3, hθ3, hpp⟩ := principal_pair_sum_of_leaves
  obtain ⟨K4, hK4, N4, hamp⟩ := principal_amp_norm
  obtain ⟨K5, hK5, hexw⟩ := exceptional_weight_bound_of_cited
  obtain ⟨N6, hTt⟩ := exceptionalMain_norm_eventually
  obtain ⟨ε, hε, hzeta⟩ := zeta_ne_zero_near_one
  have hb0 := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton).2
  have hsb : exceptionalStrip ≤
      Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hstrip0 := exceptionalStrip_pos
  set Km := K4 + 2 with hKm
  have hKm0 : 0 ≤ Km := by rw [hKm]; linarith
  refine ⟨K1 + K3 + 4 * K2 * Km + 8 * K2 + 2 * Km ^ 2 * K5, min θ1 (min θ3 (1 / 8)),
    by positivity, lt_min hθ1 (lt_min hθ3 (by norm_num)), (min_le_right _ _).trans
      ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro θ hθ hθle
  have hθ1' : θ ≤ θ1 := hθle.trans (min_le_left _ _)
  have hθ3' : θ ≤ θ3 := hθle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ8 : θ ≤ 1 / 8 := hθle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N1, h1⟩ := hexp θ hθ hθ1'
  obtain ⟨N3, h3⟩ := hpp θ hθ hθ3'
  obtain ⟨N5, h5⟩ := large_N_facts θ hθ hθ8
  have hev : ∀ᶠ N : ℕ in Filter.atTop, exceptionalStrip / (5 * θ * ε) < Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨N7, h7⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N1 (max N3 (max N4 (max N5 (max N6 N7)))),
    fun N hN r γ hcase hr0 n hn => ?_⟩
  obtain ⟨hN1, hN3, hN4, hN5, hN6, hN7⟩ :
      N1 ≤ N ∧ N3 ≤ N ∧ N4 ≤ N ∧ N5 ≤ N ∧ N6 ≤ N ∧ N7 ≤ N := by
    simpa only [max_le_iff] using hN
  obtain ⟨h4, hlogP1, hPN, hPw⟩ := h5 N hN5
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast h4
  have hN0 : (0 : ℝ) < N := by linarith
  have hP1 : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by linarith) hθ.le
  have hP0 : 0 < (N : ℝ) ^ θ := by linarith
  rcases hcase with h0 | ⟨e, he, hre, hrP, hLz, hγlo, hγ1⟩
  · omega
  set P := (N : ℝ) ^ θ with hPdef
  have hP2 : 2 ≤ P := by
    have h1e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ≤ Real.exp 1 := h1e
      _ ≤ Real.exp (Real.log P) := Real.exp_le_exp.mpr hlogP1
      _ = P := Real.exp_log hP0
  set T := P ^ 5 with hTdef
  have hPT : P ≤ T := le_self_pow₀ hP1 (by norm_num)
  have hT2 : 2 ≤ T := hP2.trans hPT
  have hlogT : Real.log T = 5 * θ * Real.log N := by
    rw [hTdef, Real.log_pow, hPdef, Real.log_rpow hN0]; push_cast; ring
  have hsmall : exceptionalStrip / Real.log T < ε := by
    have hL := h7 N hN7
    have h5θε : 0 < 5 * θ * ε := by positivity
    rw [div_lt_iff₀ h5θε] at hL
    have hlT : 0 < Real.log T := by rw [hlogT]; nlinarith
    rw [div_lt_iff₀ hlT, hlogT]
    linarith
  have hr1 : r ≠ 1 := by
    intro h1r
    have hk : e.1 = 0 := by omega
    obtain ⟨k, χ⟩ := e
    simp only at hk
    subst hk
    have hz : riemannZeta (γ : ℂ) = 0 := by
      have h := hLz
      rwa [DirichletCharacter.LFunction_modOne_eq] at h
    exact hzeta γ (by linarith) hγ1 hz
  have heF : e ∈ family P := by
    unfold family
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.2.1⟩⟩
    rw [Finset.mem_range]
    have : e.1 + 1 ≤ ⌊P⌋₊ := Nat.le_floor (by rw [← hre]; exact hrP)
    omega
  have hU : ∀ x ∈ family P, x.1 + 1 = r → x.2.LFunction (γ : ℂ) = 0 → x = e := by
    intro x hxF hxr hxz
    have hx : x ∈ excSet exceptionalStrip T := by
      refine ⟨?_, isPrimitive_of_mem_family hxF, (γ : ℂ), hxz, ?_, ?_⟩
      · have : ((x.1 : ℝ) + 1) = (r : ℝ) := by rw [← hxr]; push_cast; ring
        linarith
      · simpa using hγlo
      · simp only [Complex.ofReal_im, abs_zero]; linarith
    exact hb0 T hT2 (LeanLab.Linnik.Decomp1532b.excSet_mono hsb hT2 hx)
      (LeanLab.Linnik.Decomp1532b.excSet_mono hsb hT2 he)
  have hEeq := correctedEnergy_exc_eq N θ γ r e hP1 heF hre hr1 hLz hU
  have hone : one ∈ family P := one_mem_family hP1
  have hne : one ≠ e := by
    rintro rfl
    exact hr1 (by simp [hre, one])
  set F := family P with hF
  set G := (F.erase one).erase e with hG
  set f : PChar → PChar → ℂ := fun x y => pairSum N P n x y with hf
  set a : PChar → ℝ := fun x => ampNorm N P x with ha
  set R := remNorm N P with hRdef
  set Rt := Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N),
    ‖primeAmplitude e.2 N β + exceptionalMain N γ β‖ ^ 2) with hRtdef
  set S := ∑ x ∈ G, a x with hSdef
  set I := ∫ α in majorArcs N P,
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α) with hI
  set JS := (Jn N n : ℂ) * singSeries n with hJS
  set tw := totientWeight n with htw
  set sN := Real.sqrt N / Real.log N with hsNdef
  have hpair : ∀ x ∈ F, ∀ y ∈ F, ‖f x y‖ ≤ K2 * tw * a x * a y := fun x hx y hy =>
    pairSum_le_of_mem_family hpw N hP0.le hn hx hy
  have hdec := double_sum_split_two F one e hone heF hne f
  have hsplit : I - JS = (I - ∑ x ∈ F, ∑ y ∈ F, f x y) + (f one one - JS) +
      (f one e + f e one + f e e) +
      (∑ x ∈ ({one, e} : Finset PChar), ∑ y ∈ G, f x y + ∑ x ∈ G, ∑ y ∈ F, f x y) := by
    rw [hdec]; ring
  have hsumF : ∑ x ∈ F, a x = a one + a e + S := by
    rw [← Finset.add_sum_erase F a hone,
      ← Finset.add_sum_erase (F.erase one) a (Finset.mem_erase.mpr ⟨hne.symm, heF⟩)]
    ring
  have hcrossA : ‖∑ x ∈ ({one, e} : Finset PChar), ∑ y ∈ G, f x y‖ ≤
      K2 * tw * (a one + a e) * S := by
    have := norm_double_sum_le {one, e} G f a (K2 * tw) (fun x hx y hy => by
      have hxF : x ∈ F := by
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]; exact hone
        · rw [Finset.mem_singleton.mp h]; exact heF
      exact hpair x hxF y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)))
    have hpa : ∑ x ∈ ({one, e} : Finset PChar), a x = a one + a e := Finset.sum_pair hne
    rwa [hpa] at this
  have hcrossB : ‖∑ x ∈ G, ∑ y ∈ F, f x y‖ ≤ K2 * tw * S * (a one + a e + S) := by
    have := norm_double_sum_le G F f a (K2 * tw) (fun x hx y hy =>
      hpair x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) y hy)
    rwa [hsumF] at this
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRt0 : 0 ≤ Rt := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => Real.sqrt_nonneg _
  have ha10 : 0 ≤ a one := Real.sqrt_nonneg _
  have hae0 : 0 ≤ a e := Real.sqrt_nonneg _
  have ha1 : a one ≤ Km * sN + R := by
    have := hamp N hN4 P hPN
    have : K4 * sN ≤ Km * sN := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); rw [hKm]; linarith
    linarith
  have hae : a e ≤ Km * sN + Rt := by
    have h1 := exc_ampNorm_le N P γ e
    have h2 := hTt N hN6 γ hγ1.le (P / N) hPN
    have : 2 * sN ≤ Km * sN := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); rw [hKm]; linarith
    change a e ≤ _ + Rt at h1
    linarith
  set M := Km * sN + (R + Rt + S) with hM
  have ha1M : a one ≤ M := by rw [hM]; linarith
  have haeM : a e ≤ M := by rw [hM]; linarith
  set W := pairWeight P n e one + pairWeight P n one e + pairWeight P n e e with hW
  have hexc : ‖f one e + f e one + f e e‖ ≤ W * M ^ 2 := by
    have hb : ∀ x y : PChar, a x ≤ M → a y ≤ M → ‖f x y‖ ≤ pairWeight P n x y * (M * M) := by
      intro x y hx hy
      have h := pair_sum_schwarz N P hP0.le n x y
      have hw := pairWeight_nonneg P n x y
      have hax : 0 ≤ a x := Real.sqrt_nonneg _
      have hay : 0 ≤ a y := Real.sqrt_nonneg _
      calc ‖f x y‖ ≤ pairWeight P n x y * a x * a y := h
        _ = pairWeight P n x y * (a x * a y) := by ring
        _ ≤ pairWeight P n x y * (M * M) := by gcongr
    have e1 := hb one e ha1M haeM
    have e2 := hb e one haeM ha1M
    have e3 := hb e e haeM haeM
    calc ‖f one e + f e one + f e e‖ ≤ ‖f one e‖ + ‖f e one‖ + ‖f e e‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by rw [hW, sq]; linarith
  have hW0 : 0 ≤ W := by
    rw [hW]
    have := pairWeight_nonneg P n e one
    have := pairWeight_nonneg P n one e
    have := pairWeight_nonneg P n e e
    linarith
  have hW1 : W ≤ K5 * tw * exceptionalWeight r n := by
    have := hexw P n e hn he.2.1
    rw [hW, hre]; linarith
  have hW2 : W ≤ 3 * K2 * tw := by
    have hep := he.2.1
    have hop := isPrimitive_of_mem_family hone
    have := hpw P n e one hn hep hop
    have := hpw P n one e hn hop hep
    have := hpw P n e e hn hep hep
    rw [hW]; linarith
  have hcfe : complexFrequencyError N θ n ≤ K1 * P ^ (5 / 2 : ℝ) +
      K3 * tw * ((N : ℝ) / Real.log N ^ 2 * n.natAbs.divisors.card *
        (Real.log P / P) + Real.sqrt N / Real.log N * R + R ^ 2) +
      W * M ^ 2 +
      (K2 * tw * (a one + a e) * S + K2 * tw * S * (a one + a e + S)) := by
    have e : complexFrequencyError N θ n = ‖I - JS‖ := rfl
    rw [e, hsplit]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
      (add_le_add (h1 N hN1 n) (h3 N hN3 n hn))) hexc)) ((norm_add_le _ _).trans
      (add_le_add hcrossA hcrossB)))
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hsN : 0 < sN := div_pos (Real.sqrt_pos.mpr hN0) hL0
  have hQ : (N : ℝ) / Real.log N ^ 2 = sN ^ 2 := by
    rw [hsNdef, div_pow, Real.sq_sqrt hN0.le]
  have htw1 : 1 ≤ tw := one_le_totientWeight hn
  have hd1 := one_le_divisors_card hn
  have hlp : 0 ≤ Real.log P / P * n.natAbs.divisors.card := by positivity
  have hPw' : P ^ (5 / 2 : ℝ) ≤
      (N : ℝ) / Real.log N ^ 2 * tw * (Real.log P / P * n.natAbs.divisors.card) := by
    have hX0 : 0 ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) := by positivity
    calc P ^ (5 / 2 : ℝ) ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) := hPw
      _ = (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) * 1 * 1 := by ring
      _ ≤ (N : ℝ) / Real.log N ^ 2 * (Real.log P / P) * tw * n.natAbs.divisors.card := by
        gcongr
      _ = (N : ℝ) / Real.log N ^ 2 * tw * (Real.log P / P * n.natAbs.divisors.card) := by
        ring
  have hew0 : 0 ≤ exceptionalWeight r n := by unfold exceptionalWeight; positivity
  have hE : normalizedEnergy N θ r γ = (R + Rt + S) / sN := by
    unfold normalizedEnergy; rw [hEeq]
  rw [hE]
  have key := display1517_algebra hK1.le hK2.le hK3.le hK5.le hKm0 hsN hQ (by linarith)
    hR0 hRt0 hS0 ha1 hae hlp hPw' hew0 hW0 hW1 hW2 (by
      refine hcfe.trans (le_of_eq ?_)
      rw [hM]; ring)
  refine key.trans (le_of_eq ?_)
  ring

end LeanLab.Linnik.MajorArcEnergy

