module

public import Mathlib
public import LeanLab.DensityGoldbach.U1502Fejer

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

The pair sum of a Fejer kernel over a frequency set `R ⊆ Z_N`, expanded on the physical side:
for shifts `β_j` with weights `w_j`,

  `Σ_j w_j Σ_{r, r' ∈ R} fej(L, θ(r - r') - β_j) = (1/L) Σ_{n, n' < L} G(n - n') |P(n - n')|²`,

`θ(s) = s/N`, `P(t) = Σ_{r ∈ R} e(t r / N)`, `G(t) = Σ_j w_j e(-t β_j)`; then the bound by
`H(0) + 2 Σ_{1 ≤ m < L} H(m)`, `H(m) = |G(m)| |P(m)|²`, and Parseval `Σ_{1 ≤ m < L} |P(m)|² ≤ N |R|`.

Known mathematics, no cited input. AI-written Lean code, Claude, 2026-10-23. Checked only by
the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real Complex
open LeanLab.PNTPort.LargeSieve
open scoped ComplexConjugate

noncomputable section
namespace LeanLab.DensityGoldbach.U1502

variable {N : ℕ} [NeZero N]

/-- `θ(s) = s/N ∈ [0, 1)`. -/
def thetaN (N : ℕ) [NeZero N] (s : ZMod N) : ℝ := (s.val : ℝ) / N

/-- `P(t) = Σ_{r ∈ R} e(t r / N)`. -/
def Pz (R : Finset (ZMod N)) (t : ℤ) : ℂ := ∑ r ∈ R, ZMod.stdAddChar ((t : ZMod N) * r)

lemma stdAddChar_eq_e (j : ZMod N) : ZMod.stdAddChar j = e ((j.val : ℝ) / N) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  unfold e
  congr 1
  push_cast
  ring

lemma e_intCast_div (x : ℤ) : e ((x : ℝ) / N) = ZMod.stdAddChar (x : ZMod N) := by
  rw [stdAddChar_eq_e]
  have hv : (((x : ZMod N).val : ℤ)) = x % (N : ℤ) := ZMod.val_intCast x
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have : (x : ℝ) / N = (((x : ZMod N).val : ℕ) : ℝ) / N + ((x / (N : ℤ) : ℤ) : ℝ) := by
    have h1 : ((((x : ZMod N).val : ℕ) : ℤ) : ℝ) = ((x % (N : ℤ) : ℤ) : ℝ) := by rw [hv]
    push_cast at h1
    rw [h1, Int.emod_def]
    push_cast
    field_simp
    ring
  rw [this, e_add, e_int, mul_one]

lemma e_mul_theta (t : ℤ) (s : ZMod N) :
    e ((t : ℝ) * thetaN N s) = ZMod.stdAddChar ((t : ZMod N) * s) := by
  have h : (t : ℝ) * thetaN N s = ((t * (s.val : ℤ) : ℤ) : ℝ) / N := by
    unfold thetaN; push_cast; ring
  rw [h, e_intCast_div]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]

lemma e_sub' (x y : ℝ) : e (x - y) = e x * conj (e y) := by
  rw [sub_eq_add_neg, e_add, e_neg]

lemma normsq_eq_sum (D : ℂ) : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by
  rw [Complex.mul_conj']; push_cast; ring

/-- `|Σ_{n<L} e(nβ)|² = Σ_{n, n'} e((n - n')β)`. -/
lemma fej_expand (L : ℕ) (β : ℝ) :
    ((fej L β : ℝ) : ℂ) = (1 / (L : ℂ)) *
      ∑ n ∈ range L, ∑ n' ∈ range L, e (((n : ℤ) - n' : ℤ) * β) := by
  unfold fej
  push_cast
  rw [← Complex.ofReal_pow, normsq_eq_sum, map_sum, sum_mul_sum]
  congr 1
  refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
  rw [← e_sub']
  congr 1
  push_cast; ring

/-- `Σ_{r, r'} e(t θ(r - r')) = |P(t)|²`. -/
lemma pair_char (R : Finset (ZMod N)) (t : ℤ) :
    ∑ r ∈ R, ∑ r' ∈ R, e ((t : ℝ) * thetaN N (r - r')) = ((‖Pz R t‖ ^ 2 : ℝ) : ℂ) := by
  rw [normsq_eq_sum, Pz, map_sum, sum_mul_sum]
  refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
  rw [e_mul_theta, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1; ring

/-- `G(t) = Σ_j w_j e(-t β_j)` for a finite family of shifts. -/
def Gz {ι : Type*} (F : Finset ι) (w : ι → ℝ) (β : ι → ℝ) (t : ℤ) : ℂ :=
  ∑ j ∈ F, (w j : ℂ) * e (-((t : ℝ) * β j))

lemma sum4_comm {α β γ δ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d
      = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, f a b c d :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, f a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, f a b c d := sum_comm
    _ = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d :=
        sum_congr rfl fun c _ => sum_comm

/-- One shift of the pair expansion. -/
lemma pair_expand_one (R : Finset (ZMod N)) (L : ℕ) (w β : ℝ) :
    ((w * ∑ r ∈ R, ∑ r' ∈ R, fej L (thetaN N (r - r') - β) : ℝ) : ℂ) =
      ∑ n ∈ range L, ∑ n' ∈ range L, (1 / (L : ℂ)) * ((w : ℂ) * e (-((((n : ℤ) - n' : ℤ) : ℝ) * β)))
        * ((‖Pz R ((n : ℤ) - n')‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [← pair_char]
  push_cast
  simp_rw [fej_expand]
  rw [mul_sum]
  simp_rw [mul_sum]
  rw [sum4_comm]
  refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => sum_congr rfl fun r _ =>
    sum_congr rfl fun r' _ => ?_
  push_cast
  rw [show ((n : ℝ) - n') * (thetaN N (r - r') - β) =
    ((n : ℝ) - n') * thetaN N (r - r') + -(((n : ℝ) - n') * β) by ring, e_add]
  ring

/-- **Pair expansion.** -/
theorem pair_expand {ι : Type*} (R : Finset (ZMod N)) (L : ℕ) (F : Finset ι) (w β : ι → ℝ) :
    ((∑ j ∈ F, w j * ∑ r ∈ R, ∑ r' ∈ R, fej L (thetaN N (r - r') - β j) : ℝ) : ℂ) =
      (1 / (L : ℂ)) * ∑ n ∈ range L, ∑ n' ∈ range L,
        Gz F w β ((n : ℤ) - n') * ((‖Pz R ((n : ℤ) - n')‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  simp_rw [pair_expand_one]
  rw [sum_comm]
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun n' _ => ?_
  unfold Gz
  rw [sum_mul, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma Gz_neg {ι : Type*} (F : Finset ι) (w β : ι → ℝ) (t : ℤ) :
    Gz F w β (-t) = conj (Gz F w β t) := by
  unfold Gz
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← e_neg]
  push_cast; ring_nf

lemma Pz_neg (R : Finset (ZMod N)) (t : ℤ) : Pz R (-t) = conj (Pz R t) := by
  unfold Pz
  rw [map_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [← AddChar.map_neg_eq_conj]
  congr 1; push_cast; ring

lemma norm_Gz_natAbs {ι : Type*} (F : Finset ι) (w β : ι → ℝ) (t : ℤ) :
    ‖Gz F w β t‖ = ‖Gz F w β (t.natAbs : ℤ)‖ := by
  rcases Int.natAbs_eq t with h | h
  · rw [← h]
  · conv_lhs => rw [h]
    rw [Gz_neg, Complex.norm_conj]

lemma norm_Pz_natAbs (R : Finset (ZMod N)) (t : ℤ) :
    ‖Pz R t‖ = ‖Pz R (t.natAbs : ℤ)‖ := by
  rcases Int.natAbs_eq t with h | h
  · rw [← h]
  · conv_lhs => rw [h]
    rw [Pz_neg, Complex.norm_conj]

lemma norm_Pz_le (R : Finset (ZMod N)) (t : ℤ) : ‖Pz R t‖ ≤ R.card := by
  unfold Pz
  refine (norm_sum_le _ _).trans ?_
  have : ∀ r ∈ R, ‖ZMod.stdAddChar ((t : ZMod N) * r)‖ = 1 := fun r _ => by
    rw [stdAddChar_eq_e, norm_e]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]

/-- Reindexing a sum over `n' < L` by the distance `|n - n'|`. -/
lemma sum_natAbs_le (H : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m) (L n : ℕ) (hn : n < L) :
    ∑ n' ∈ range L, H ((n : ℤ) - n').natAbs ≤ H 0 + 2 * ∑ m ∈ Ico 1 L, H m := by
  rw [← sum_filter_add_sum_filter_not (range L) (fun n' => n' < n)]
  have hA : ∑ n' ∈ (range L).filter (fun n' => n' < n), H ((n : ℤ) - n').natAbs ≤
      ∑ m ∈ Ico 1 L, H m := by
    have e1 : ∀ n' ∈ (range L).filter (fun n' => n' < n), H ((n : ℤ) - n').natAbs = H (n - n') :=
      fun n' hn' => by
        rw [mem_filter] at hn'
        congr 1; omega
    rw [sum_congr rfl e1]
    rw [← sum_image (f := H) (g := fun n' => n - n')]
    · apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [mem_image] at hm
        obtain ⟨n', hn', rfl⟩ := hm
        rw [mem_filter, mem_range] at hn'
        rw [mem_Ico]; omega
      · intro m _ _; exact hH m
    · intro a ha b hb hab
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      omega
  have hB : ∑ n' ∈ (range L).filter (fun n' => ¬ n' < n), H ((n : ℤ) - n').natAbs ≤
      H 0 + ∑ m ∈ Ico 1 L, H m := by
    have e1 : ∀ n' ∈ (range L).filter (fun n' => ¬ n' < n),
        H ((n : ℤ) - n').natAbs = H (n' - n) := fun n' hn' => by
      rw [mem_filter] at hn'
      congr 1; omega
    rw [sum_congr rfl e1]
    rw [← sum_image (f := H) (g := fun n' => n' - n)]
    · have hsplit : H 0 + ∑ m ∈ Ico 1 L, H m = ∑ m ∈ range L, H m := by
        have hL0 : 0 < L := by omega
        rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hL0]
      rw [hsplit]
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [mem_image] at hm
        obtain ⟨n', hn', rfl⟩ := hm
        rw [mem_filter, mem_range] at hn'
        rw [mem_range]; omega
      · intro m _ _; exact hH m
    · intro a ha b hb hab
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      omega
  linarith

/-- **Pair bound**: with nonnegative weights the pair sum is at most `H(0) + 2 Σ_{1 ≤ m < L} H(m)`,
`H(m) = |G(m)| |P(m)|²`. -/
theorem pair_bound {ι : Type*} (R : Finset (ZMod N)) (L : ℕ) (hL : 1 ≤ L) (F : Finset ι)
    (w β : ι → ℝ) (hw : ∀ j ∈ F, 0 ≤ w j) :
    ∑ j ∈ F, w j * ∑ r ∈ R, ∑ r' ∈ R, fej L (thetaN N (r - r') - β j) ≤
      ‖Gz F w β 0‖ * ‖Pz R 0‖ ^ 2 +
        2 * ∑ m ∈ Ico 1 L, ‖Gz F w β m‖ * ‖Pz R m‖ ^ 2 := by
  set S := ∑ j ∈ F, w j * ∑ r ∈ R, ∑ r' ∈ R, fej L (thetaN N (r - r') - β j)
  set H : ℕ → ℝ := fun m => ‖Gz F w β m‖ * ‖Pz R m‖ ^ 2 with hHdef
  have hH : ∀ m, 0 ≤ H m := fun m => by positivity
  have hS0 : 0 ≤ S := sum_nonneg fun j hj => mul_nonneg (hw j hj)
    (sum_nonneg fun r _ => sum_nonneg fun r' _ => fej_nonneg _ _)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have e := congrArg norm (pair_expand R L F w β)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0, norm_mul] at e
  have hn1 : ‖(1 / (L : ℂ))‖ = 1 / (L : ℝ) := by rw [norm_div, norm_one]; simp
  rw [hn1] at e
  have h1 : ‖∑ n ∈ range L, ∑ n' ∈ range L,
      Gz F w β ((n : ℤ) - n') * ((‖Pz R ((n : ℤ) - n')‖ ^ 2 : ℝ) : ℂ)‖ ≤
      ∑ n ∈ range L, ∑ n' ∈ range L, H ((n : ℤ) - n').natAbs := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => (norm_sum_le _ _).trans
      (sum_le_sum fun n' _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      norm_Gz_natAbs, norm_Pz_natAbs]
  have h2 : ∑ n ∈ range L, ∑ n' ∈ range L, H ((n : ℤ) - n').natAbs ≤
      L * (H 0 + 2 * ∑ m ∈ Ico 1 L, H m) := by
    calc ∑ n ∈ range L, ∑ n' ∈ range L, H ((n : ℤ) - n').natAbs
        ≤ ∑ n ∈ range L, (H 0 + 2 * ∑ m ∈ Ico 1 L, H m) :=
          sum_le_sum fun n hn => sum_natAbs_le H hH L n (mem_range.1 hn)
      _ = L * (H 0 + 2 * ∑ m ∈ Ico 1 L, H m) := by rw [sum_const, card_range, nsmul_eq_mul]
  have : S ≤ 1 / (L : ℝ) * (L * (H 0 + 2 * ∑ m ∈ Ico 1 L, H m)) := by
    rw [e]; exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  rw [show 1 / (L : ℝ) * (L * (H 0 + 2 * ∑ m ∈ Ico 1 L, H m)) =
    H 0 + 2 * ∑ m ∈ Ico 1 L, H m by field_simp] at this
  simpa [H] using this

/-- **Parseval for `P`**: `Σ_{1 ≤ m < L} |P(m)|² ≤ N |R|` for `L ≤ N`. -/
theorem sum_Pz_sq_le (R : Finset (ZMod N)) (L : ℕ) (hLN : L ≤ N) :
    ∑ m ∈ Ico 1 L, ‖Pz R m‖ ^ 2 ≤ N * R.card := by
  -- full Parseval over `Z_N`
  have hfull : ∑ j : ZMod N, ‖∑ r ∈ R, ZMod.stdAddChar (j * r)‖ ^ 2 = N * R.card := by
    have : ∀ j : ZMod N, ((‖∑ r ∈ R, ZMod.stdAddChar (j * r)‖ ^ 2 : ℝ) : ℂ) =
        ∑ r ∈ R, ∑ r' ∈ R, ZMod.stdAddChar (j * (r - r')) := by
      intro j
      rw [normsq_eq_sum, map_sum, sum_mul_sum]
      refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      congr 1; ring
    apply Complex.ofReal_injective
    push_cast
    simp_rw [← Complex.ofReal_pow, this]
    rw [sum_comm]
    have h2 : ∀ r ∈ R, ∑ r' ∈ R, ∑ j : ZMod N, ZMod.stdAddChar (j * (r - r')) = (N : ℂ) := by
      intro r hr
      have : ∀ r' ∈ R, ∑ j : ZMod N, ZMod.stdAddChar (j * (r - r')) =
          if r' = r then (N : ℂ) else 0 := by
        intro r' _
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
        by_cases h : r' = r
        · subst h; simp
        · rw [if_neg (sub_ne_zero.2 (Ne.symm h)), if_neg h]; simp
      rw [sum_congr rfl this, sum_ite_eq' R r, if_pos hr]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (ZMod N)))]
    rw [sum_congr rfl h2, sum_const, nsmul_eq_mul]
    ring
  have hinj : Set.InjOn (fun m : ℕ => (m : ZMod N)) (Ico 1 L : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_Ico, Set.mem_Ico] at ha hb
    simp only at hab
    rw [ZMod.natCast_eq_natCast_iff'] at hab
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
  calc ∑ m ∈ Ico 1 L, ‖Pz R m‖ ^ 2
      = ∑ j ∈ (Ico 1 L).image (fun m : ℕ => (m : ZMod N)),
          ‖∑ r ∈ R, ZMod.stdAddChar (j * r)‖ ^ 2 := by
        rw [sum_image hinj]
        exact sum_congr rfl fun m _ => by simp [Pz]
    _ ≤ ∑ j : ZMod N, ‖∑ r ∈ R, ZMod.stdAddChar (j * r)‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => by positivity
    _ = N * R.card := hfull

end LeanLab.DensityGoldbach.U1502
