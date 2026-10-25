module

public import LeanLab.DensityGoldbach.U1494TT
public import LeanLab.DensityGoldbach.U1488Spec

/-!
Unit U-1494, run 20261022T1603Z-23862. P0047 Alsetri and Shao 2024, Theorem 1.2.

Before: `alsetriShao_1_2_U1488 : GreenLargeSpec → AlsetriShao12`.

The large spectrum bound `#{r : |f̂(r)| ≥ δ} ≤ K δ^{-q}` for `0 ≤ f ≤ ν_b` is now PROVED at every
level `δ ≥ δ₀`, for any fixed `δ₀ > 0`, from the lab's unconditional `green62` by the TT* lemma
`U1494.tt_star_count`, and at every level below the Parseval line `K δ^{-q} ≥ 2 log(WN) δ^{-2}`
from Parseval and `ν_b ≤ log(WN)`. The cited input shrinks in two steps:

* `GreenLargeSpecSmall`: the bound only for `δ < δ₀`, some fixed `δ₀ > 0`;
* `GreenLargeSpecMid`: the bound only for `δ < δ₀` AND above the Parseval line, the window
  `(K / (2 log WN))^{1/(q-2)} < δ < δ₀` when `q > 2`, which is exactly the range of Bourgain's
  large spectrum lemma with Green's enveloping sieve.

Results:
* `largeSpecSmall_of_largeSpec`, `largeSpecMid_of_small`: the new inputs are implied by the old.
* `largeSpec_of_small : GreenLargeSpecSmall → GreenLargeSpec`, TT* plus `green62`.
* `small_of_mid : GreenLargeSpecMid → GreenLargeSpecSmall`, Parseval.
* `alsetriShao_1_2_U1494 : GreenLargeSpecSmall → AlsetriShao12`,
  `alsetriShao_1_2_U1494_mid : GreenLargeSpecMid → AlsetriShao12`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1494
open LeanLab.DensityGoldbach.U1446

/-- **Large spectrum bound at small levels only**: some `δ₀ > 0`, `0 < q < 4`, `K` with
`#{r : δ ≤ |f̂(r)|} ≤ K δ^{-q}` for `0 < δ < δ₀`, all `0 ≤ f ≤ ν_b`, large `z`, large prime `N`. -/
def GreenLargeSpecSmall : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ q : ℝ, 0 < q ∧ q < 4 ∧ ∃ K : ℝ, 0 < K ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z →
    ∀ b : ℕ, b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
      N.Prime → N₀ ≤ N → ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ K * δ ^ (-q)

/-- **Large spectrum bound in the middle window only**: as `GreenLargeSpecSmall`, but only at
levels `δ < δ₀` where the claimed bound beats Parseval, `K δ^{-q} < 2 log(z# N) δ^{-2}`. -/
def GreenLargeSpecMid : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ q : ℝ, 0 < q ∧ q < 4 ∧ ∃ K : ℝ, 0 < K ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z →
    ∀ b : ℕ, b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
      N.Prime → N₀ ≤ N → ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          K * δ ^ (-q) < 2 * Real.log ((primorial z : ℝ) * N) * δ ^ (-(2 : ℝ)) →
          ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ K * δ ^ (-q)

theorem largeSpecSmall_of_largeSpec (H : U1488.GreenLargeSpec) : GreenLargeSpecSmall := by
  obtain ⟨q, hq, hq4, K, hK, z₁, hG⟩ := H
  refine ⟨1, one_pos, q, hq, hq4, K, hK, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hG z hz b hb hcop
  exact ⟨N₀, fun N _ hNp hN f hf δ hδ _ => hN₀ N hNp hN f hf δ hδ⟩

theorem largeSpecMid_of_small (H : GreenLargeSpecSmall) : GreenLargeSpecMid := by
  obtain ⟨δ₀, hδ₀, q, hq, hq4, K, hK, z₁, hG⟩ := H
  refine ⟨δ₀, hδ₀, q, hq, hq4, K, hK, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hG z hz b hb hcop
  exact ⟨N₀, fun N _ hNp hN f hf δ hδ hδ' _ => hN₀ N hNp hN f hf δ hδ hδ'⟩

/-! ### Large levels: TT* with `green62` -/

theorem largeSpec_of_small (H : GreenLargeSpecSmall) : U1488.GreenLargeSpec := by
  obtain ⟨δ₀, hδ₀, q, hq, hq4, K, hK, z₁, hG⟩ := H
  set c : ℝ := δ₀ ^ 2 / 4 with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨z₀, hz₀⟩ := LeanLab.DensityGoldbach.U1484.green62 c hc
  set K' : ℝ := K + 8 * 2 ^ q / δ₀ ^ 2
  have hK' : 0 < K' := by positivity
  refine ⟨q, hq, hq4, K', hK', max z₁ z₀, fun z hz b hb hcop => ?_⟩
  obtain ⟨Na, hNa⟩ := hG z (le_of_max_le_left hz) b hb hcop
  obtain ⟨Nb, hNb⟩ := hz₀ z (le_of_max_le_right hz) b hb hcop
  obtain ⟨Nc, hNc⟩ := nu_avg_close (primorial z) b hb hcop 1 one_pos
  refine ⟨max Na (max Nb Nc), fun N _ hNp hN f hf δ hδ => ?_⟩
  set ν := nuW (primorial z) b N
  have hA : avg N ν ≤ 2 := by
    have := hNc N (le_of_max_le_right (le_of_max_le_right hN))
    linarith [(abs_le.1 this).2]
  have hqpos : 0 < δ ^ (-q) := Real.rpow_pos_of_pos hδ _
  set S := univ.filter (fun r : ZMod N => δ ≤ ‖hatE N f r‖)
  rcases lt_or_ge δ δ₀ with hsm | hlg
  · have := hNa N hNp (le_of_max_le_left hN) f hf δ hδ hsm
    have : K * δ ^ (-q) ≤ K' * δ ^ (-q) := by
      apply mul_le_mul_of_nonneg_right _ hqpos.le
      simp only [K']; have : 0 ≤ 8 * 2 ^ q / δ₀ ^ 2 := by positivity
      linarith
    linarith
  rcases lt_or_ge 2 δ with hbig | hmid
  · -- empty spectrum
    have hS : S.card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _ hr
      have h1 := LeanLab.DensityGoldbach.U1467.norm_hatE_le f (fun n => (hf n).1) r
      have h2 := LeanLab.DensityGoldbach.U1467.avg_mono f ν (fun n => (hf n).2)
      linarith
    rw [hS, Nat.cast_zero]; positivity
  · have hcnt := tt_star_count f ν hf 2 c hA hc.le
      (fun s hs => hNb N hNp (le_of_max_le_left (le_of_max_le_right hN)) s hs) δ hδ
      (by
        have : δ₀ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hδ₀.le hlg 2
        simp only [hcdef]; linarith)
      S (fun r hr => (mem_filter.1 hr).2)
    have hS8 : (S.card : ℝ) ≤ 8 / δ₀ ^ 2 := by
      have h2 : δ₀ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hδ₀.le hlg 2
      rw [le_div_iff₀ (by positivity)]
      have : (S.card : ℝ) * δ₀ ^ 2 ≤ (S.card : ℝ) * δ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      linarith
    have hone : 1 ≤ 2 ^ q * δ ^ (-q) := by
      rw [Real.rpow_neg hδ.le, ← div_eq_mul_inv, ← Real.div_rpow zero_le_two hδ.le]
      exact Real.one_le_rpow (by rw [le_div_iff₀ hδ]; linarith) hq.le
    have : 8 / δ₀ ^ 2 ≤ K' * δ ^ (-q) := by
      have e : 8 / δ₀ ^ 2 * (2 ^ q * δ ^ (-q)) = 8 * 2 ^ q / δ₀ ^ 2 * δ ^ (-q) := by ring
      have h1 : 8 / δ₀ ^ 2 ≤ 8 / δ₀ ^ 2 * (2 ^ q * δ ^ (-q)) :=
        le_mul_of_one_le_right (by positivity) hone
      have h2 : 8 * 2 ^ q / δ₀ ^ 2 * δ ^ (-q) ≤ K' * δ ^ (-q) := by
        apply mul_le_mul_of_nonneg_right _ hqpos.le
        simp only [K']; linarith
      linarith
    linarith

/-! ### Very small levels: Parseval -/

/-- `ν_b(n) ≤ log(WN)` for `b < W`. -/
lemma nuW_le_log (W b N : ℕ) [NeZero N] (hb : b < W) (n : ZMod N) :
    nuW W b N n ≤ Real.log ((W : ℝ) * N) := by
  unfold nuW
  have hW : 0 < W := by omega
  have hφ : (Nat.totient W : ℝ) / W ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hW)]; exact_mod_cast Nat.totient_le W
  have hlt : W * n.val + b < W * N := by
    have := ZMod.val_lt n
    have : W * n.val + W ≤ W * N := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega
  split_ifs with hp
  · have hpos : (0 : ℝ) < (W * n.val + b : ℕ) := by exact_mod_cast hp.pos
    have hlog0 : 0 ≤ Real.log ((W : ℝ) * n.val + b) :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hle : Real.log ((W : ℝ) * n.val + b) ≤ Real.log ((W : ℝ) * N) := by
      apply Real.log_le_log (by push_cast at hpos; exact hpos)
      exact_mod_cast hlt.le
    calc (Nat.totient W : ℝ) / W * Real.log ((W : ℝ) * n.val + b)
        ≤ 1 * Real.log ((W : ℝ) * n.val + b) := mul_le_mul_of_nonneg_right hφ hlog0
      _ ≤ _ := by rw [one_mul]; exact hle
  · apply Real.log_nonneg
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    nlinarith

/-- **Parseval count**: `#{r : δ ≤ |f̂(r)|} δ² ≤ L E ν` when `0 ≤ f ≤ ν ≤ L`. -/
theorem parseval_count {N : ℕ} [NeZero N] (f ν : ZMod N → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ ν n)
    (L : ℝ) (hL : ∀ n, ν n ≤ L) (δ : ℝ) (hδ : 0 < δ) :
    ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) * δ ^ 2 ≤ L * avg N ν := by
  set S := univ.filter (fun r : ZMod N => δ ≤ ‖hatE N f r‖)
  have h1 : (S.card : ℝ) * δ ^ 2 ≤ ∑ r ∈ S, ‖hatE N f r‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun r hr => pow_le_pow_left₀ hδ.le (mem_filter.1 hr).2 2
  have h2 : ∑ r ∈ S, ‖hatE N f r‖ ^ 2 ≤ ∑ r : ZMod N, ‖hatE N f r‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => by positivity
  rw [LeanLab.DensityGoldbach.U1467.parseval] at h2
  have h3 : ∀ n, f n ^ 2 ≤ L * ν n := fun n => by
    have := (hf n).1; have := (hf n).2
    have : ν n ≤ L := hL n
    nlinarith
  have h4 : (1 / (N : ℝ)) * ∑ n : ZMod N, f n ^ 2 ≤ L * avg N ν := by
    unfold avg
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_le_sum fun n _ => ?_
    have : (0 : ℝ) ≤ 1 / N := by positivity
    nlinarith [h3 n]
  linarith

theorem small_of_mid (H : GreenLargeSpecMid) : GreenLargeSpecSmall := by
  obtain ⟨δ₀, hδ₀, q, hq, hq4, K, hK, z₁, hG⟩ := H
  refine ⟨δ₀, hδ₀, q, hq, hq4, K, hK, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨Na, hNa⟩ := hG z hz b hb hcop
  obtain ⟨Nc, hNc⟩ := nu_avg_close (primorial z) b hb hcop 1 one_pos
  refine ⟨max Na Nc, fun N _ hNp hN f hf δ hδ hδ₀' => ?_⟩
  set ν := nuW (primorial z) b N
  set L := Real.log ((primorial z : ℝ) * N)
  rcases lt_or_ge (K * δ ^ (-q)) (2 * L * δ ^ (-(2 : ℝ))) with hw | hp
  · exact hNa N hNp (le_of_max_le_left hN) f hf δ hδ hδ₀' hw
  · have hA : avg N ν ≤ 2 := by
      have := hNc N (le_of_max_le_right hN)
      linarith [(abs_le.1 this).2]
    have hL0 : 0 ≤ L := (nuW_nonneg _ _ _ 0).trans (nuW_le_log _ b N hb 0)
    have hc := parseval_count f ν hf L (nuW_le_log _ b N hb) δ hδ
    have hd2 : δ ^ (-(2 : ℝ)) = (δ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hδ.le]; norm_cast
    have hδ2 : 0 < δ ^ 2 := by positivity
    have : ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ 2 * L * δ ^ (-(2 : ℝ)) := by
      rw [hd2, ← div_eq_mul_inv, le_div_iff₀ hδ2]
      nlinarith
    linarith

/-! ### Theorem 1.2 -/

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenLargeSpecSmall` only. -/
theorem alsetriShao_1_2_U1494 (H : GreenLargeSpecSmall) : AlsetriShao12 :=
  U1488.alsetriShao_1_2_U1488 (largeSpec_of_small H)

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenLargeSpecMid` only. -/
theorem alsetriShao_1_2_U1494_mid (H : GreenLargeSpecMid) : AlsetriShao12 :=
  alsetriShao_1_2_U1494 (small_of_mid H)

/-! ### Faithfulness tests -/

/-- Vacuity: `f = 0` meets the hypotheses and has empty spectrum, so the conclusion of
`GreenLargeSpecSmall` is satisfiable for every admissible `f`-slot instance with `K > 0`. -/
theorem vacuity_Small (N W b : ℕ) [NeZero N] (δ q K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    ((univ.filter (fun r => δ ≤ ‖hatE N (fun _ => (0 : ℝ)) r‖)).card : ℝ) ≤ K * δ ^ (-q) := by
  rw [U1488.vacuity_Spec N W b δ hδ, Nat.cast_zero]
  have := Real.rpow_pos_of_pos hδ (-q)
  positivity

end LeanLab.DensityGoldbach.U1494
