module

public import LeanLab.Tolev2009.Displays14to16

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Dyadic

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16

/-- Block zero contains modulus one. Every later block is a natural dyadic interval. -/
def block : ℕ → Finset ℕ
  | 0 => {1}
  | j + 1 => Ioc (2 ^ j) (2 * 2 ^ j)

theorem sum_blocks (f : ℕ → ℝ) (r : ℕ) :
    ∑ k ∈ Icc 1 (2 ^ r), f k = ∑ j ∈ range (r + 1), ∑ k ∈ block j, f k := by
  induction r with
  | zero => simp [block]
  | succ r ih =>
    have hp : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by norm_num)
    have hU : Icc 1 (2 ^ (r + 1)) = Icc 1 (2 ^ r) ∪ block (r + 1) := by
      ext k
      simp only [block, mem_union, mem_Icc, mem_Ioc, pow_succ]
      omega
    have hd : Disjoint (Icc 1 (2 ^ r)) (block (r + 1)) := by
      simp only [disjoint_left, mem_Icc, block, mem_Ioc]
      omega
    rw [hU, sum_union hd, ih]
    rw [sum_range_succ (f := fun j => ∑ k ∈ block j, f k) (r + 1)]

theorem rectangle_cover (f : ℕ → ℕ → ℝ) (hf : ∀ x y, 0 ≤ f x y) (H : ℕ) :
    ∑ x ∈ Icc 1 H, ∑ y ∈ Icc 1 H, f x y ≤
      ∑ i ∈ range (Nat.clog 2 H + 1), ∑ j ∈ range (Nat.clog 2 H + 1),
        ∑ x ∈ block i, ∑ y ∈ block j, f x y := by
  have hH := Nat.le_pow_clog (by norm_num : 1 < 2) H
  have hsub : Icc 1 H ⊆ Icc 1 (2 ^ Nat.clog 2 H) := by
    intro k hk
    simp only [mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hH⟩
  calc
    _ ≤ ∑ x ∈ Icc 1 (2 ^ Nat.clog 2 H), ∑ y ∈ Icc 1 (2 ^ Nat.clog 2 H), f x y := by
      refine (sum_le_sum fun x _ => sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hf x y)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => sum_nonneg fun y _ => hf x y)
    _ = _ := by
      rw [sum_blocks]
      simp_rw [sum_blocks (fun y => f _ y)]
      congr 1
      funext i
      rw [sum_comm]

/-- The corrected display 11 includes singleton blocks and mixed singleton blocks. -/
noncomputable def V (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) : ℝ :=
  ∑ x ∈ block i, ∑ y ∈ block j,
    innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ x y

theorem V_succ_succ (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) :
    V Q τ lam l₃ K₃ N (i + 1) (j + 1) = Vblk Q τ lam l₃ K₃ N (2 ^ i) (2 ^ j) := rfl

theorem rectangle_le (f : ℕ → ℕ → ℝ) (hf : ∀ x y, 0 ≤ f x y) (H : ℕ) (M : ℝ)
    (hM : ∀ i ∈ range (Nat.clog 2 H + 1), ∀ j ∈ range (Nat.clog 2 H + 1),
      ∑ x ∈ block i, ∑ y ∈ block j, f x y ≤ M) :
    ∑ x ∈ Icc 1 H, ∑ y ∈ Icc 1 H, f x y ≤ (Nat.clog 2 H + 1 : ℝ) ^ 2 * M := by
  refine (rectangle_cover f hf H).trans ?_
  calc
    _ ≤ ∑ i ∈ range (Nat.clog 2 H + 1), ∑ j ∈ range (Nat.clog 2 H + 1), M :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hM i hi j hj
    _ = _ := by simp [pow_two, mul_assoc]

/-- There are at most a constant times log N blocks in either coordinate. -/
theorem block_count_le (H N : ℕ) (hHN : H ≤ N) (hL : 1 ≤ Real.log N) :
    (Nat.clog 2 H + 1 : ℝ) ≤ (1 / Real.log 2 + 2) * Real.log N := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 H by
    rw [Real.logb]; exact div_nonneg (Real.log_natCast_nonneg H) h2.le)
  have heq := Real.natCeil_logb_natCast 2 H
  norm_num only [Nat.cast_ofNat] at heq
  rw [heq] at hceil
  have hlog : Real.log H ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos H with h | h
    · simp [h]; linarith
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hHN)
  have hdiv : Real.log H / Real.log 2 ≤ Real.log N / Real.log 2 :=
    div_le_div_of_nonneg_right hlog h2.le
  change (Nat.clog 2 H : ℝ) < Real.log H / Real.log 2 + 1 at hceil
  have he : Real.log N / Real.log 2 + 2 ≤ (1 / Real.log 2 + 2) * Real.log N := by
    simp only [add_mul, div_eq_mul_inv]
    linarith
  exact le_trans (by linarith) he

noncomputable def dyadicConstant : ℝ := (1 / Real.log 2 + 2) ^ 2

/-- Display 10 for nonnegative weights, including all singleton cases. -/
theorem display10 (f : ℕ → ℕ → ℝ) (hf : ∀ x y, 0 ≤ f x y) (H N : ℕ)
    (hHN : H ≤ N) (hL : 1 ≤ Real.log N) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ range (Nat.clog 2 H + 1), ∀ j ∈ range (Nat.clog 2 H + 1),
      ∑ x ∈ block i, ∑ y ∈ block j, f x y ≤ M) :
    ∑ x ∈ Icc 1 H, ∑ y ∈ Icc 1 H, f x y ≤ dyadicConstant * Real.log N ^ 2 * M := by
  refine (rectangle_le f hf H M hM).trans ?_
  have hc := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Nat.clog 2 H + 1)
    (block_count_le H N hHN hL) 2
  have he : ((1 / Real.log 2 + 2) * Real.log N) ^ 2 = dyadicConstant * Real.log N ^ 2 := by
    simp only [dyadicConstant, mul_pow]
  rw [he] at hc
  exact mul_le_mul_of_nonneg_right hc hM0

/-- Display 10 as an actual finite maximum, with no chosen block hypothesis. -/
theorem exists_max_block (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N H : ℕ)
    (hHN : H ≤ N) (hL : 1 ≤ Real.log N) :
    ∃ i ∈ range (Nat.clog 2 H + 1), ∃ j ∈ range (Nat.clog 2 H + 1),
      (∑ x ∈ Icc 1 H, ∑ y ∈ Icc 1 H,
        innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ x y) ≤
          dyadicConstant * Real.log N ^ 2 * V Q τ lam l₃ K₃ N i j := by
  obtain ⟨⟨i, j⟩, hij, hmax⟩ := exists_max_image
    (range (Nat.clog 2 H + 1) ×ˢ range (Nat.clog 2 H + 1))
    (fun ij : ℕ × ℕ => V Q τ lam l₃ K₃ N ij.1 ij.2) ⟨(0, 0), by simp⟩
  rcases mem_product.mp hij with ⟨hi, hj⟩
  refine ⟨i, hi, j, hj, display10 _ (fun x y => innerF_nonneg _ _ _ _ _ _) H N hHN hL _
    (sum_nonneg fun x _ => sum_nonneg fun y _ => innerF_nonneg _ _ _ _ _ _) ?_⟩
  intro i' hi' j' hj'
  exact hmax (i', j') (mem_product.mpr ⟨hi', hj'⟩)

/-- The paper's first two modulus cutoffs. -/
noncomputable def cutoff (B : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊

/-- The paper's third modulus cutoff. -/
noncomputable def cutoff3 (B : ℝ) (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊

theorem cutoff_le (B : ℝ) (N : ℕ) (hB : 0 ≤ B) (hL : 1 ≤ Real.log N) : cutoff B N ≤ N := by
  have hN : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    norm_num [this] at hL
  have hs : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
  have hp : Real.log N ^ (-B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hn : 0 ≤ Real.sqrt N * Real.log N ^ (-B) := by positivity
  have hf := Nat.floor_le hn
  have hx : Real.sqrt N * Real.log N ^ (-B) ≤ N :=
    le_trans (mul_le_of_le_one_right (Real.sqrt_nonneg _) hp) hs
  exact_mod_cast hf.trans hx

/-- Display 10 for Faithful.E2 with singleton blocks included. -/
theorem E2_display10 (lam : ℕ → ℝ) (l₃ N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hL : 1 ≤ Real.log N) :
    ∃ i ∈ range (Nat.clog 2 (cutoff (10 ^ 4 * A) N) + 1),
      ∃ j ∈ range (Nat.clog 2 (cutoff (10 ^ 4 * A) N) + 1),
        E2 lam l₃ A N ≤ dyadicConstant * Real.log N ^ 2 *
          V (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N i j := by
  exact exists_max_block _ _ _ _ _ _ _ (cutoff_le _ _ (by positivity) hL) hL

end LeanLab.Tolev2009.Dyadic
