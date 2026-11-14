module

public import LeanLab.Linnik.Decomp466b
public import LeanLab.Linnik.Decomp486a

/-!
Gallagher 1975 P0094 p.138 before display 5.
Averaging Theorem 3 with the proved Lemmas 8 and 10.
CONDITIONAL ON Decomp466a.gallagher_theorem3.
The shared fiber estimate keeps this module below Decomp1532c.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp466c

open Finset Filter MeasureTheory
open scoped Topology
open LeanLab.Linnik.Decomp1532a (pairs dif)
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries excSet)
open LeanLab.Linnik.U7204 (Sg)
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp466b

/-- Gallagher 1975 p.138 before display 5, finite weighted averaging step.
The divisor and exceptional errors retain separate budgets. -/
theorem weighted_error_sum {ι : Type*} (s : Finset ι) (w t e : ι → ℝ)
    {K B V A d z ε : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hd : 0 ≤ d) (hz : 0 ≤ z)
    (hw : ∀ x ∈ s, 0 ≤ w x) (ht : ∀ x ∈ s, t x ≤ d)
    (hweight : ∑ x ∈ s, w x ≤ A * V) (he : ∑ x ∈ s, w x * e x ≤ ε * V) :
    (∑ x ∈ s, K * B * w x * (t x + z + e x)) ≤
      K * B * V * (A * (d + z) + ε) := by
  have hp : (∑ x ∈ s, w x * (t x + z + e x)) ≤
      (d + z) * (∑ x ∈ s, w x) + ∑ x ∈ s, w x * e x := by
    calc
      _ ≤ ∑ x ∈ s, ((d + z) * w x + w x * e x) := by
        apply sum_le_sum
        intro x hx
        have h := mul_le_mul_of_nonneg_left (ht x hx) (hw x hx)
        nlinarith
      _ = _ := by rw [sum_add_distrib, mul_sum]
  have hs : (∑ x ∈ s, K * B * w x * (t x + z + e x)) =
      K * B * ∑ x ∈ s, w x * (t x + z + e x) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    ring
  rw [hs]
  calc
    _ ≤ K * B * ((d + z) * (∑ x ∈ s, w x) + ∑ x ∈ s, w x * e x) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hK hB)
    _ ≤ K * B * ((d + z) * (A * V) + ε * V) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hB)
      exact add_le_add (mul_le_mul_of_nonneg_left hweight (add_nonneg hd hz)) he
    _ = _ := by ring

/-- Gallagher 1975 p.138 before display 5.
The exact sealed remainder statement from Theorem 3 and the proved averaging estimates.
CONDITIONAL ON the supplied Theorem 3 estimate. -/
theorem major_arc_remainder_bound_of_theorem3
    (h3 : ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ) ∧
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n)) : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
            (C * Real.exp (-c / θ) + δ) := by
  classical
  have hescape := exceptional_conductor_escape
  obtain ⟨c, K, θ₀, hc, hK, hθ₀, hθ₀1, hfreq⟩ := h3
  obtain ⟨A₀, hA₀⟩ := LeanLab.Linnik.Decomp1532a.lemma8
  let A : ℝ := |A₀| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨c, K * A, θ₀, hc, hθ₀, fun θ hθ hθmax k hk δ hδ => ?_⟩
  let d : ℝ := δ / (K * A)
  let ε : ℝ := δ / K
  have hd : 0 < d := div_pos hδ (mul_pos hK hA)
  have hε : 0 < ε := div_pos hδ hK
  obtain ⟨Nf, hNf⟩ := hfreq θ hθ hθmax
  obtain ⟨Nd, hNd⟩ := divisor_error_small (by omega : 1 ≤ k) hθ hd
  obtain ⟨R, hR2, hR⟩ := exceptional_average_small hε
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (hescape θ hθ R)
  refine ⟨max k (max 2 (max Nf (max Nd Ne))), fun N hN => ?_⟩
  have hkN : k ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨r, hr, hper⟩ := hNf N (by omega)
  let V : ℝ := (Nat.log 2 N : ℝ) ^ (2 * k)
  let B : ℝ := (N : ℝ) / Real.log N ^ 2
  let z : ℝ := Real.exp (-c / θ)
  let T := (univ : Finset (pairs k (Nat.log 2 N))).filter (fun x => dif x ≠ 0)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hw (x : pairs k (Nat.log 2 N)) : 0 ≤ totientWeight (dif x) := by
    unfold totientWeight
    positivity
  have hweight : (∑ x ∈ T, totientWeight (dif x)) ≤ A * V := by
    have hh := hA₀ k N (by omega) hkN hN2
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self A₀).trans (by dsimp [A]; linarith)) hV)
  have hex : (∑ x ∈ T, totientWeight (dif x) * exceptionalWeight r (dif x)) ≤ ε * V := by
    rcases hr with hr0 | ⟨x, hx, hrx, hrP⟩
    · subst r
      simpa [exceptionalWeight] using mul_nonneg hε.le hV
    · obtain ⟨hrlarge, hshape⟩ := hNe N (by omega) x hx
      have hrN : r ≤ N := by
        have hP : (N : ℝ) ^ θ ≤ N := by
          calc _ ≤ (N : ℝ) ^ (1 : ℝ) :=
                 Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
                   (hθmax.trans hθ₀1)
               _ = N := Real.rpow_one _
        exact_mod_cast hrP.trans hP
      apply hR k N r (by omega) hkN (by omega) hrN
      simpa only [← hrx] using hshape
  have ht (x : pairs k (Nat.log 2 N)) (hx : x ∈ T) :
      Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * (dif x).natAbs.divisors.card ≤ d := by
    apply hNd N (by omega) (dif x).natAbs
    · exact Int.natAbs_pos.mpr (mem_filter.mp hx).2
    · exact difference_le (by omega) x
  have hsum := weighted_error_sum T (fun x => totientWeight (dif x))
    (fun x => Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * (dif x).natAbs.divisors.card)
    (fun x => exceptionalWeight r (dif x)) hK.le hB hd.le hz
    (fun x _ => hw x) ht hweight hex
  have herr := LeanLab.Linnik.Decomp1532c.major_arc_remainder_le_fiber_sum k (Nat.log 2 N) N
    ((N : ℝ) ^ θ) (fun n => K * B * totientWeight n *
      (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card + z + exceptionalWeight r n))
    (fun n hn => (frequencyError_le_complexFrequencyError N θ n).trans (hper n hn))
  have hbudget : K * (A * (d + z) + ε) ≤ 2 * (K * A * z + δ) := by
    have hdEq : K * A * d = δ := by dsimp [d]; field_simp
    have heEq : K * ε = δ := by dsimp [ε]; field_simp
    have hpos : 0 ≤ K * A * z := by positivity
    nlinarith
  calc
    _ ≤ ∑ x ∈ T, K * B * totientWeight (dif x) *
        (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * (dif x).natAbs.divisors.card + z +
          exceptionalWeight r (dif x)) := herr
    _ ≤ K * B * V * (A * (d + z) + ε) := hsum
    _ = (B * V) * (K * (A * (d + z) + ε)) := by ring
    _ ≤ (B * V) * (2 * (K * A * z + δ)) :=
      mul_le_mul_of_nonneg_left hbudget (mul_nonneg hB hV)
    _ = _ := by dsimp [B, V, z]; ring

/-- Gallagher 1975 p.138 before display 5.
Exact sealed parent statement from the cited Theorem 3 leaf and the clean averaging proof.
CONDITIONAL ON Decomp466a.gallagher_theorem3. -/
theorem major_arc_remainder_bound_split : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
            (C * Real.exp (-c / θ) + δ) :=
  major_arc_remainder_bound_of_theorem3 gallagher_theorem3

end LeanLab.Linnik.Decomp466c
