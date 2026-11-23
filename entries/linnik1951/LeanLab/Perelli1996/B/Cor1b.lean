module

public import Mathlib
public import LeanLab.Perelli1996.B.Links
public import LeanLab.Perelli1996.B.Sing
public import LeanLab.Perelli1996.B.RBound

/-!
P0083 Perelli 1996, page 478: **Corollary 1, second assertion, from the first.** The paper
says the second assertion follows from the first; here it is derived in Lean, so `Cor1b`
is no longer a separate cited input but CONDITIONAL ON Theorem 1 only.
Ingredients: `F(n) ≥ N/2` on the window for large `N` (from `F(n) ~ a_k n^k`), `𝔖(m) ≥ 1`
for even `m` (`Sing.lean`), and `R(m) ≤ m/4` when `m ≥ 17408^8` is not a sum of two primes
(`RBound.lean`). So a non-Goldbach even `F(n)` has `|Δ| ≥ 3N/8`, an exception of part 1.
The hypothesis `ρ_F(2) ≠ 0` is not needed for the bound; it only makes `A_F` nonempty.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Perelli1996.B
open Finset Real Polynomial Filter Topology Asymptotics

attribute [local instance] Classical.propDecidable

/-- **Growth on the window**: for admissible `F` there is `X₀ ≥ 0` with
`F(n) ≥ n^k / 2` for every natural `n ≥ X₀`. -/
theorem poly_lower (F : ℤ[X]) (hF : Admissible F) :
    ∃ X₀ : ℝ, 0 ≤ X₀ ∧ ∀ n : ℕ, X₀ ≤ n → (n : ℝ) ^ F.natDegree / 2 ≤ (Fv F n : ℝ) := by
  set G := F.map (Int.castRingHom ℝ) with hGdef
  have hinj : Function.Injective (Int.castRingHom ℝ) := (Int.castRingHom ℝ).injective_int
  have hdeg : G.natDegree = F.natDegree := natDegree_map_eq_of_injective hinj F
  have hlc : G.leadingCoeff = (F.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj F
  have hlc1 : (1 : ℝ) ≤ F.leadingCoeff := by exact_mod_cast hF.2
  have hE := (isEquivalent_atTop_lead (P := G)).isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hE
  refine ⟨max X 1, by positivity, fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hb := hX n hnX
  rw [hdeg, hlc] at hb
  have hev : eval (n : ℝ) G = (Fv F n : ℝ) := by
    have := eval_intCast_map (Int.castRingHom ℝ) F (n : ℤ)
    simp [Fv, hGdef]
  simp only [Pi.sub_apply, hev, Real.norm_eq_abs] at hb
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ F.natDegree := one_le_pow₀ hn1
  have hv : 0 < (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by positivity
  rw [abs_of_pos hv] at hb
  have := (abs_le.1 hb).1
  nlinarith

/-- `(N^{1/k})^k = N`. -/
theorem rpow_k (N : ℝ) (hN : 0 ≤ N) (k : ℕ) (hk : k ≠ 0) :
    (N ^ (1 / (k : ℝ))) ^ k = N := by
  rw [one_div]; exact Real.rpow_inv_natCast_pow hN hk

/-- **Corollary 1, second assertion, from the first assertion.** -/
theorem cor1b_of_cor1a (h : Cor1a) : Cor1b := by
  intro F hF _hrho A ε hA hε
  obtain ⟨C₁, C₂, N₁, hC⟩ := h F hF A ε hA hε
  obtain ⟨X₀, hX₀, hX⟩ := poly_lower F hF
  set k := F.natDegree with hk
  have hk0 : k ≠ 0 := by have := hF.1; omega
  -- `C₁ L^{-A} < 3/8` for large `N`
  have htend : Tendsto (fun N : ℝ => Real.log N ^ (-A)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hA).comp Real.tendsto_log_atTop
  have hc : (0 : ℝ) < 3 / (8 * (max C₁ 1)) := by positivity
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (htend.eventually (gt_mem_nhds hc))
  refine ⟨C₂, max (max N₁ N₂) (max (X₀ ^ k) (2 * 17408 ^ 8)), fun N H hN h1 h2 => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNX : X₀ ^ k ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNb : 2 * 17408 ^ 8 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hLA := hN₂ N hN2
  have hLApos : 0 ≤ Real.log N ^ (-A) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  -- every non-Goldbach `n ∈ A_F` is an exception of part 1
  have hsub : (AF F N H).filter (fun n => ¬ IsGoldbachSum (Fv F n).toNat) ⊆
      (win F N H).filter (fun n => C₁ * N * Real.log N ^ (-A) < |Delta F n|) := by
    intro n hn
    simp only [AF, Finset.mem_filter] at hn
    obtain ⟨⟨hnw, hev⟩, hng⟩ := hn
    refine Finset.mem_filter.2 ⟨hnw, ?_⟩
    have hnlo : N ^ (1 / (k : ℝ)) ≤ n := by
      simp only [win, Finset.mem_Icc] at hnw
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnw.1)
    have hXn : X₀ ≤ n := by
      have := Real.rpow_le_rpow (by positivity) hNX (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))
      rw [one_div, Real.pow_rpow_inv_natCast hX₀ hk0] at this
      rw [one_div] at hnlo
      linarith
    have hFn := hX n hXn
    have hnk : N ≤ (n : ℝ) ^ k := by
      have := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hnlo k
      rwa [rpow_k N hN0.le k hk0] at this
    have hFN : N / 2 ≤ (Fv F n : ℝ) := by linarith
    set m := (Fv F n).toNat with hm
    have hFpos : 0 ≤ Fv F n := by
      have : (0 : ℝ) ≤ (Fv F n : ℝ) := by linarith
      exact_mod_cast this
    have hmc : (m : ℝ) = (Fv F n : ℝ) := by
      rw [hm]; exact_mod_cast Int.toNat_of_nonneg hFpos
    have hmeven : Even m := by
      obtain ⟨r, hr⟩ := hev
      refine ⟨r.toNat, ?_⟩
      rw [hm]; omega
    have hmbig : (17408 : ℝ) ^ 8 ≤ m := by rw [hmc]; linarith
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hmbig; norm_num at hmbig
    have hS := one_le_sing hmeven hm0
    have hR := R_le_quarter hmbig hng
    have hm0' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hD : Delta F n ≤ -(3 / 4 * (m : ℝ)) := by
      unfold Delta
      rw [← hm, ← hmc]
      nlinarith
    have habs : 3 / 4 * (m : ℝ) ≤ |Delta F n| := by
      rw [abs_of_neg (by linarith [show (0 : ℝ) < m by rw [hmc]; linarith])]; linarith
    -- `C₁ N L^{-A} < 3N/8 ≤ 3m/4`
    have hC1 : C₁ * Real.log N ^ (-A) < 3 / 8 := by
      have hmx : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      have : max C₁ 1 * Real.log N ^ (-A) < 3 / 8 := by
        rw [lt_div_iff₀ (by positivity)] at hLA
        nlinarith
      nlinarith [le_max_left C₁ 1]
    calc C₁ * N * Real.log N ^ (-A) = (C₁ * Real.log N ^ (-A)) * N := by ring
      _ < 3 / 8 * N := by gcongr
      _ ≤ 3 / 4 * (m : ℝ) := by rw [hmc]; linarith
      _ ≤ |Delta F n| := habs
  calc (((AF F N H).filter (fun n => ¬ IsGoldbachSum (Fv F n).toNat)).card : ℝ)
      ≤ (((win F N H).filter (fun n => C₁ * N * Real.log N ^ (-A) < |Delta F n|)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C₂ * H * Real.log N ^ (-A) := hC N H hN1 h1 h2

/-- **Corollary 1, second assertion, from Theorem 1**: CONDITIONAL ON Theorem 1 only. -/
theorem cor1b_of (h : Theorem1) : Cor1b := cor1b_of_cor1a (cor1a_of h)

/-- Vacuity test: the hypotheses of `Cor1b` hold for `F = X`, which is admissible with
`ρ_F(2) = 1 ≠ 0`, so `cor1b_of` is not vacuous. -/
theorem vacuity_X : Admissible (X : ℤ[X]) ∧ rho (X : ℤ[X]) 2 ≠ 0 := by
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  have h := rho_two (X : ℤ[X])
  have h0 : Even (Fv (X : ℤ[X]) 0) := by simp [Fv]
  have h1 : ¬ Even (Fv (X : ℤ[X]) 1) := by simp [Fv]
  rw [if_pos h0, if_neg h1] at h
  intro hz
  rw [hz] at h
  norm_num at h

end LeanLab.Perelli1996.B

