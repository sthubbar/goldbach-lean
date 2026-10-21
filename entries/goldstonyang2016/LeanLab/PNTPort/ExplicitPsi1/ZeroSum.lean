module

public import LeanLab.PNTPort.ExplicitPsi1.Residues
public import LeanLab.PNTPort.ZetaZeros.Sym

/-!
# `Σ_ρ m(ρ)/|ρ(ρ + 1)|` converges

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
Davenport chapter 15, no cited input: from the lab's window count `ZetaZeros.zero_count`,
zeros with `n - 1 < |Im ρ| ≤ n` number `O(log n)` with multiplicity, so
`Σ_ρ m(ρ)/|ρ(ρ + 1)| ≪ Σ_n log n/n² < ∞`.

* `zero_sum_bound`: the sums over the zeros in `[-1/2, 2] × [-T, T]` are bounded uniformly in `T`.
* `summable_hw`: `ρ ↦ m(ρ)/‖ρ(ρ + 1)‖` is summable over `Zall`, the zeros with `Re ρ ≥ -1/2`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology Set

local notation "ζ" => riemannZeta

/-- `m(ρ)/‖ρ(ρ + 1)‖`. -/
noncomputable def hw (ρ : ℂ) : ℝ := (analyticOrderNatAt ζ ρ : ℝ) / ‖ρ * (ρ + 1)‖

lemma hw_nonneg (ρ : ℂ) : 0 ≤ hw ρ := by unfold hw; positivity

/-- The zeros of ζ with `Re ρ ≥ -1/2`: the nontrivial zeros, proved as `Zall_eq` in Nontrivial.lean: ζ has no zero on
`[-1/2, 0]` or on `Re s ≥ 1`. -/
def Zall : Set ℂ := {ρ | ζ ρ = 0 ∧ -1 / 2 ≤ ρ.re}

lemma sum_union_le' {A B : Finset ℂ} {f : ℂ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have h0 : 0 ≤ ∑ x ∈ A ∩ B, f x := Finset.sum_nonneg (fun x _ => hf x)
  linarith

/-- Zeros with `n - 1 < |Im ρ| ≤ n`, `n ≥ 5`, number at most `4 C log n` with multiplicity. -/
lemma fiber_count : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → ∀ s : Finset ℂ,
    (∀ ρ ∈ s, ζ ρ = 0 ∧ (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n) →
    ∑ ρ ∈ s, (analyticOrderNatAt ζ ρ : ℝ) ≤ 4 * C * Real.log n := by
  obtain ⟨C, hC, hA⟩ := ZetaZeros.zero_count
  refine ⟨C, hC, fun n hn s hs => ?_⟩
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hW : ∀ t : ℝ, 3 ≤ |t| → |t| ≤ n → ∃ W : Finset ℂ, (∀ ρ, ρ ∈ W ↔ ρ ∈ ZetaZeros.ZA t) ∧
      ∑ ρ ∈ W, (analyticOrderNatAt ζ ρ : ℝ) ≤ C * Real.log n := by
    intro t h3 htn
    obtain ⟨hfin, hsum⟩ := hA t h3
    refine ⟨hfin.toFinset, fun ρ => hfin.mem_toFinset, hsum.trans ?_⟩
    gcongr
  obtain ⟨W1, hW1, hs1⟩ := hW ((n : ℝ) - 7 / 10) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨W2, hW2, hs2⟩ := hW ((n : ℝ) - 3 / 10) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨W3, hW3, hs3⟩ := hW (-((n : ℝ) - 7 / 10))
    (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  obtain ⟨W4, hW4, hs4⟩ := hW (-((n : ℝ) - 3 / 10))
    (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have hsub : s ⊆ W1 ∪ W2 ∪ W3 ∪ W4 := by
    intro ρ hρ
    obtain ⟨hz, hlo, hhi⟩ := hs ρ hρ
    simp only [Finset.mem_union, hW1, hW2, hW3, hW4, ZetaZeros.ZA, mem_ofPred_eq]
    rcases le_or_gt 0 ρ.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at hlo hhi
      rcases le_or_gt ρ.im ((n : ℝ) - 3 / 10) with h | h
      · left; left; left; refine ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · left; left; right; refine ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · rw [abs_of_neg hneg] at hlo hhi
      rcases le_or_gt (-ρ.im) ((n : ℝ) - 3 / 10) with h | h
      · left; right; refine ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · right; refine ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hnn : ∀ x : ℂ, 0 ≤ (analyticOrderNatAt ζ x : ℝ) := fun x => by positivity
  calc ∑ ρ ∈ s, (analyticOrderNatAt ζ ρ : ℝ)
      ≤ ∑ ρ ∈ W1 ∪ W2 ∪ W3 ∪ W4, (analyticOrderNatAt ζ ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hnn x)
    _ ≤ ∑ ρ ∈ W1 ∪ W2 ∪ W3, (analyticOrderNatAt ζ ρ : ℝ) +
          ∑ ρ ∈ W4, (analyticOrderNatAt ζ ρ : ℝ) := sum_union_le' hnn
    _ ≤ ∑ ρ ∈ W1, (analyticOrderNatAt ζ ρ : ℝ) + ∑ ρ ∈ W2, (analyticOrderNatAt ζ ρ : ℝ) +
          ∑ ρ ∈ W3, (analyticOrderNatAt ζ ρ : ℝ) + ∑ ρ ∈ W4, (analyticOrderNatAt ζ ρ : ℝ) := by
        have a := sum_union_le' (A := W1 ∪ W2) (B := W3) hnn
        have b := sum_union_le' (A := W1) (B := W2) hnn
        linarith
    _ ≤ 4 * C * Real.log n := by linarith

/-- The majorant `4 C log n/(n - 1)²`. -/
noncomputable def aSeq (C : ℝ) (n : ℕ) : ℝ := 4 * C * Real.log n / ((n : ℝ) - 1) ^ 2

lemma aSeq_nonneg {C : ℝ} (hC : 0 < C) (n : ℕ) : 0 ≤ aSeq C n := by
  unfold aSeq
  have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  positivity

lemma aSeq_summable {C : ℝ} (hC : 0 < C) : Summable (aSeq C) := by
  have hs : Summable (fun n : ℕ => 32 * C * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (aSeq_nonneg hC) (fun n => ?_) hs
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [aSeq] <;> linarith
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hn0.le (by norm_num)
  have hsq : (n : ℝ) ^ 2 / 4 ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith
  have hpow : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have hp1 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hp3 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hn2 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by norm_cast
  unfold aSeq
  have hd : 0 < ((n : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_iff₀ hd]
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  calc 4 * C * Real.log n ≤ 4 * C * ((n : ℝ) ^ (1 / 2 : ℝ) * 2) := by
        gcongr; linarith [show (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) = (n : ℝ) ^ (1 / 2 : ℝ) * 2 by ring]
    _ = 32 * C * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) ^ 2 / 4) := by
        rw [← hn2, hpow]; field_simp; ring
    _ ≤ 32 * C * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) - 1) ^ 2 := by gcongr

lemma norm_mul_add_one_ge (ρ : ℂ) : |ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
  rw [norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ‖ := abs_im_le_norm ρ
  have h2 : |ρ.im| ≤ ‖ρ + 1‖ := by
    have := abs_im_le_norm (ρ + 1); simpa using this
  calc |ρ.im| ^ 2 = |ρ.im| * |ρ.im| := by ring
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- **Uniform bound** for the zero sums over the rectangles `[-1/2, 2] × [-T, T]`. -/
theorem zero_sum_bound : ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T →
    ∑ ρ ∈ (zeros_rect_finite 2 T).toFinset, hw ρ ≤ B := by
  obtain ⟨C, hC, hfib⟩ := fiber_count
  set Z4 := (zeros_rect_finite 2 4).toFinset
  refine ⟨∑ ρ ∈ Z4, hw ρ + ∑' n, aSeq C n, fun T hT => ?_⟩
  set s := (zeros_rect_finite 2 T).toFinset with hs
  have hmemT := fun z => mem_rect (c := 2) (T := T) (by norm_num) hT (z := z)
  have hmem4 := fun z => mem_rect (c := 2) (T := 4) (by norm_num) (by norm_num) (z := z)
  have hsZ : ∀ ρ ∈ s, ζ ρ = 0 ∧ ((-1 / 2 ≤ ρ.re ∧ ρ.re ≤ 2) ∧ (-T ≤ ρ.im ∧ ρ.im ≤ T)) := by
    intro ρ hρ
    rw [hs, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.2, (hmemT ρ).mp hρ.1⟩
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.im| ≤ 4)]
  have hA : ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 4), hw ρ ≤ ∑ ρ ∈ Z4, hw ρ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun x _ _ => hw_nonneg x)
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, hre, _⟩ := hsZ ρ hρ.1
    rw [Set.Finite.mem_toFinset]
    exact ⟨(hmem4 ρ).mpr ⟨hre, abs_le.mp hρ.2⟩, hz⟩
  set N := ⌈T⌉₊
  have hmaps : ∀ ρ ∈ s.filter (fun ρ => ¬ |ρ.im| ≤ 4), ⌈|ρ.im|⌉₊ ∈ Finset.Icc 5 N := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨_, _, him⟩ := hsZ ρ hρ.1
    rw [Finset.mem_Icc]
    constructor
    · have : (4 : ℝ) < |ρ.im| := lt_of_not_ge hρ.2
      have h4 : 4 < ⌈|ρ.im|⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast this)
      omega
    · exact Nat.ceil_mono (abs_le.mpr him)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hB : ∀ n ∈ Finset.Icc 5 N,
      ∑ ρ ∈ (s.filter (fun ρ => ¬ |ρ.im| ≤ 4)).filter (fun ρ => ⌈|ρ.im|⌉₊ = n), hw ρ ≤
        aSeq C n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn.1
    set u := (s.filter (fun ρ => ¬ |ρ.im| ≤ 4)).filter (fun ρ => ⌈|ρ.im|⌉₊ = n)
    have hu : ∀ ρ ∈ u, ζ ρ = 0 ∧ (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n := by
      intro ρ hρ
      simp only [u, Finset.mem_filter] at hρ
      have hc := (Nat.ceil_eq_iff (by omega)).mp hρ.2
      rw [Nat.cast_sub (by omega)] at hc
      push_cast at hc
      exact ⟨(hsZ ρ hρ.1.1).1, hc⟩
    have hcount := hfib n hn.1 u hu
    have hd : 0 < ((n : ℝ) - 1) ^ 2 := by nlinarith
    calc ∑ ρ ∈ u, hw ρ ≤ ∑ ρ ∈ u, (analyticOrderNatAt ζ ρ : ℝ) / ((n : ℝ) - 1) ^ 2 := by
          apply Finset.sum_le_sum
          intro ρ hρ
          obtain ⟨_, hlo, _⟩ := hu ρ hρ
          unfold hw
          apply div_le_div_of_nonneg_left (by positivity) hd
          calc ((n : ℝ) - 1) ^ 2 ≤ |ρ.im| ^ 2 := by
                apply pow_le_pow_left₀ (by linarith) hlo.le
            _ ≤ ‖ρ * (ρ + 1)‖ := norm_mul_add_one_ge ρ
      _ = (∑ ρ ∈ u, (analyticOrderNatAt ζ ρ : ℝ)) / ((n : ℝ) - 1) ^ 2 := by
          rw [Finset.sum_div]
      _ ≤ aSeq C n := by
          unfold aSeq
          exact div_le_div_of_nonneg_right hcount hd.le
  have hC2 : ∑ n ∈ Finset.Icc 5 N, aSeq C n ≤ ∑' n, aSeq C n :=
    (aSeq_summable hC).sum_le_tsum _ (fun n _ => aSeq_nonneg hC n)
  linarith [Finset.sum_le_sum hB]

/-- **Summability**: `Σ_{ρ ∈ Zall} m(ρ)/‖ρ(ρ + 1)‖ < ∞`. -/
theorem summable_hw : Summable (fun ρ : Zall => hw ρ) := by
  obtain ⟨B, hB⟩ := zero_sum_bound
  refine summable_of_sum_le (fun ρ => hw_nonneg ρ) (c := B) (fun u => ?_)
  set T := ∑ ρ ∈ u, |(ρ : ℂ).im| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hmap := Finset.sum_map u (Function.Embedding.subtype (· ∈ Zall)) hw
  simp only [Function.Embedding.coe_subtype] at hmap
  rw [← hmap]
  refine le_trans ?_ (hB T hT0)
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun x _ _ => hw_nonneg x)
  intro ρ hρ
  rw [Finset.mem_map] at hρ
  obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
  obtain ⟨hz, hre⟩ := hρ'Z
  have hre1 : ρ'.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have him : |ρ'.im| ≤ T :=
    Finset.single_le_sum (f := fun ρ : Zall => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ'u
  rw [Set.Finite.mem_toFinset]
  refine ⟨(mem_rect (by norm_num) hT0).mpr ⟨⟨hre, by simp; linarith⟩, abs_le.mp ?_⟩, hz⟩
  simpa using him

end LeanLab.PNTPort.ExplicitPsi1

