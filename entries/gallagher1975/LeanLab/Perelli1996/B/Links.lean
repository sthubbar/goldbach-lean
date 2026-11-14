module

public import Mathlib
public import LeanLab.Perelli1996.B.Definitions

/-!
P0083 Perelli 1996, page 478: Corollary 1 first assertion from Theorem 1 by counting, and the
"standard techniques" count `|A_F(N, H)| = ρ_F(2) H / 2 + O(1)` with an explicit `O(1)`: at most
`2` for every real `N ≥ 0` and `H ≥ 0`.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Perelli1996.B
open Finset Real Polynomial

attribute [local instance] Classical.propDecidable

/-- **Corollary 1, first assertion, from Theorem 1**, no placeholder proof as an implication: apply
Theorem 1 with `3A`; each exception has `Δ² > N² L^{-2A}`, so there are at most `K H L^{-A}`. -/
theorem cor1a_of (h : Theorem1) : Cor1a := by
  intro F hF A ε hA hε
  obtain ⟨K, N₀, hK⟩ := h F hF (3 * A) ε (by linarith) hε
  refine ⟨1, max K 0, max N₀ 3, fun N H hN h1 h2 => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  set ex := (win F N H).filter (fun n => 1 * N * L ^ (-A) < |Delta F n|) with hex
  have hsum := hK N H hN0 h1 h2
  have ht : N ^ 2 * L ^ (-(2 * A)) > 0 := by positivity
  have hsq : ∀ n ∈ ex, N ^ 2 * L ^ (-(2 * A)) ≤ Delta F n ^ 2 := by
    intro n hn
    rw [hex, Finset.mem_filter] at hn
    have h0 : 0 ≤ N * L ^ (-A) := by positivity
    have := hn.2
    rw [one_mul] at this
    have hlt : (N * L ^ (-A)) ^ 2 ≤ |Delta F n| ^ 2 := pow_le_pow_left₀ h0 this.le 2
    rw [sq_abs] at hlt
    calc N ^ 2 * L ^ (-(2 * A)) = (N * L ^ (-A)) ^ 2 := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ (-A)), ← Real.rpow_mul hL.le]
          push_cast; ring_nf
      _ ≤ Delta F n ^ 2 := hlt
  have hcount : (ex.card : ℝ) * (N ^ 2 * L ^ (-(2 * A))) ≤ ∑ n ∈ win F N H, Delta F n ^ 2 := by
    calc (ex.card : ℝ) * (N ^ 2 * L ^ (-(2 * A)))
        = ∑ _n ∈ ex, N ^ 2 * L ^ (-(2 * A)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ ex, Delta F n ^ 2 := Finset.sum_le_sum hsq
      _ ≤ ∑ n ∈ win F N H, Delta F n ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)
  have hsplit : L ^ (-(3 * A)) = L ^ (-(2 * A)) * L ^ (-A) := by
    rw [← Real.rpow_add hL]; ring_nf
  have hH : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) h1
  have hmain : (ex.card : ℝ) * (N ^ 2 * L ^ (-(2 * A))) ≤
      (max K 0 * H * L ^ (-A)) * (N ^ 2 * L ^ (-(2 * A))) := by
    calc _ ≤ K * H * N ^ 2 * L ^ (-(3 * A)) := le_trans hcount hsum
      _ ≤ max K 0 * H * N ^ 2 * L ^ (-(3 * A)) := by gcongr; exact le_max_left _ _
      _ = (max K 0 * H * L ^ (-A)) * (N ^ 2 * L ^ (-(2 * A))) := by rw [hsplit]; ring
  exact le_of_mul_le_mul_right hmain ht

/-! ### Counting `A_F(N, H)` -/

/-- Exactly `m` of `a, …, a + 2m - 1` have a given parity `r < 2`. -/
theorem card_parity_even_len (a r : ℕ) (hr : r < 2) :
    ∀ m : ℕ, ((Ico a (a + 2 * m)).filter (fun n => n % 2 = r)).card = m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hU : Ico a (a + 2 * (m + 1)) = Ico a (a + 2 * m) ∪ Ico (a + 2 * m) (a + 2 * m + 2) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]; congr 1
    have hD : Disjoint (Ico a (a + 2 * m)) (Ico (a + 2 * m) (a + 2 * m + 2)) :=
      Finset.Ico_disjoint_Ico_consecutive _ _ _
    have h1 : ((Ico (a + 2 * m) (a + 2 * m + 2)).filter (fun n => n % 2 = r)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨a + 2 * m + (r + a) % 2, ?_⟩
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [hU, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hD), ih, h1]

/-- For any length `L`, the count `c` of a given parity in `a, …, a + L - 1` has
`L ≤ 2c + 1` and `2c ≤ L + 1`. -/
theorem card_parity (a r L : ℕ) (hr : r < 2) :
    L ≤ 2 * ((Ico a (a + L)).filter (fun n => n % 2 = r)).card + 1 ∧
      2 * ((Ico a (a + L)).filter (fun n => n % 2 = r)).card ≤ L + 1 := by
  set c := ((Ico a (a + L)).filter (fun n => n % 2 = r)).card
  have hlo : L / 2 ≤ c := by
    rw [← card_parity_even_len a r hr (L / 2)]
    exact Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.Ico_subset_Ico le_rfl (by omega)))
  have hhi : c ≤ L / 2 + L % 2 := by
    rcases Nat.mod_two_eq_zero_or_one L with h0 | h1
    · have : L = 2 * (L / 2) := by omega
      have e := card_parity_even_len a r hr (L / 2)
      rw [← this] at e
      omega
    · have := card_parity_even_len a r hr (L / 2 + 1)
      have hle : c ≤ ((Ico a (a + 2 * (L / 2 + 1))).filter (fun n => n % 2 = r)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.Ico_subset_Ico le_rfl (by omega)))
      omega
  constructor <;> omega

/-- `F(n)` is even iff `F(n mod 2)` is even. -/
theorem even_Fv_iff (F : ℤ[X]) (n : ℕ) : Even (Fv F n) ↔ Even (Fv F (n % 2)) := by
  have hd : (2 : ℤ) ∣ Fv F n - Fv F (n % 2) := by
    have h1 := Polynomial.sub_dvd_eval_sub (n : ℤ) ((n % 2 : ℕ) : ℤ) F
    have h2 : (2 : ℤ) ∣ (n : ℤ) - ((n % 2 : ℕ) : ℤ) := by
      have := Nat.mod_add_div n 2
      refine ⟨(n / 2 : ℕ), ?_⟩
      push_cast; omega
    exact dvd_trans h2 h1
  rw [even_iff_two_dvd, even_iff_two_dvd]
  constructor
  · intro h
    have := dvd_sub h hd
    simpa using this
  · intro h
    have := dvd_add hd h
    simpa using this

/-- `ρ_F(2)` counts the residues `0, 1` where `F` is even. -/
theorem rho_two (F : ℤ[X]) :
    (rho F 2 : ℝ) = (if Even (Fv F 0) then 1 else 0) + (if Even (Fv F 1) then 1 else 0) := by
  have hz : ∀ i : ℕ, ((F.map (Int.castRingHom (ZMod 2))).eval ((i : ℤ) : ZMod 2) = 0 ↔
      Even (Fv F i)) := by
    intro i
    rw [Polynomial.eval_intCast_map, eq_intCast, ZMod.intCast_eq_zero_iff_even]
    rfl
  have h0 := hz 0
  have h1 := hz 1
  simp only [Nat.cast_zero, Int.cast_zero, Nat.cast_one, Int.cast_one] at h0 h1
  unfold rho
  rw [Finset.card_filter, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl,
    Finset.sum_pair (by decide)]
  by_cases e0 : Even (Fv F 0) <;> by_cases e1 : Even (Fv F 1)
  · rw [if_pos (h0.2 e0), if_pos (h1.2 e1), if_pos e0, if_pos e1]; norm_num
  · rw [if_pos (h0.2 e0), if_neg (fun h => e1 (h1.1 h)), if_pos e0, if_neg e1]; norm_num
  · rw [if_neg (fun h => e0 (h0.1 h)), if_pos (h1.2 e1), if_neg e0, if_pos e1]; norm_num
  · rw [if_neg (fun h => e0 (h0.1 h)), if_neg (fun h => e1 (h1.1 h)), if_neg e0, if_neg e1]
    norm_num

/-- **`|A_F(N, H)| = ρ_F(2) H / 2 + O(1)`**, with `|O(1)| ≤ 2`, for every polynomial `F` and real
`N ≥ 0`, `H ≥ 0`. -/
theorem card_AF (F : ℤ[X]) {N H : ℝ} (hN : 0 ≤ N) (hH : 0 ≤ H) :
    |((AF F N H).card : ℝ) - (rho F 2 : ℝ) / 2 * H| ≤ 2 := by
  set x := N ^ (1 / (F.natDegree : ℝ)) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN _
  set a := ⌈x⌉₊ with ha
  set b := ⌊x + H⌋₊ with hb
  have hab : a ≤ b + 1 := by
    have h1 : (a : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have h2 : x + H < (b : ℝ) + 1 := Nat.lt_floor_add_one _
    have : (a : ℝ) < (b : ℝ) + 2 := by linarith
    have : a < b + 2 := by exact_mod_cast this
    omega
  set L := b + 1 - a with hL
  have hwin : win F N H = Ico a (a + L) := by
    unfold win; rw [← hx, ← ha, ← hb]
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  -- `H - 1 ≤ L ≤ H + 1`
  have hLlo : H - 1 ≤ (L : ℝ) := by
    have h1 : (a : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have h2 : x + H < (b : ℝ) + 1 := Nat.lt_floor_add_one _
    have : ((L : ℕ) : ℝ) = (b : ℝ) + 1 - a := by rw [hL, Nat.cast_sub hab]; push_cast; ring
    linarith
  have hLhi : (L : ℝ) ≤ H + 1 := by
    have h1 : x ≤ (a : ℝ) := Nat.le_ceil _
    have h2 : (b : ℝ) ≤ x + H := Nat.floor_le (by linarith)
    have : ((L : ℕ) : ℝ) = (b : ℝ) + 1 - a := by rw [hL, Nat.cast_sub hab]; push_cast; ring
    linarith
  set c0 := ((Ico a (a + L)).filter (fun n => n % 2 = 0)).card
  set c1 := ((Ico a (a + L)).filter (fun n => n % 2 = 1)).card
  have p0 := card_parity a 0 L (by norm_num)
  have p1 := card_parity a 1 L (by norm_num)
  have hc0 : |(c0 : ℝ) - H / 2| ≤ 1 := by
    have e1 : (L : ℝ) ≤ 2 * c0 + 1 := by exact_mod_cast p0.1
    have e2 : 2 * (c0 : ℝ) ≤ L + 1 := by exact_mod_cast p0.2
    rw [abs_le]; constructor <;> linarith
  have hc1 : |(c1 : ℝ) - H / 2| ≤ 1 := by
    have e1 : (L : ℝ) ≤ 2 * c1 + 1 := by exact_mod_cast p1.1
    have e2 : 2 * (c1 : ℝ) ≤ L + 1 := by exact_mod_cast p1.2
    rw [abs_le]; constructor <;> linarith
  -- split `A_F` by the parity of `n`
  have hAF : (AF F N H).card = (if Even (Fv F 0) then c0 else 0) + (if Even (Fv F 1) then c1 else 0) := by
    unfold AF
    rw [hwin]
    have hsplit : (Ico a (a + L)).filter (fun n => Even (Fv F n)) =
        ((Ico a (a + L)).filter (fun n => n % 2 = 0 ∧ Even (Fv F 0))) ∪
          ((Ico a (a + L)).filter (fun n => n % 2 = 1 ∧ Even (Fv F 1))) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_union]
      rw [even_Fv_iff F n]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    rw [hsplit, Finset.card_union_of_disjoint (Finset.disjoint_filter.2 (fun n _ h1 h2 => by
      omega))]
    by_cases e0 : Even (Fv F 0) <;> by_cases e1 : Even (Fv F 1) <;> simp [e0, e1, c0, c1]
  rw [hAF, rho_two]
  by_cases e0 : Even (Fv F 0) <;> by_cases e1 : Even (Fv F 1) <;> simp only [e0, e1, if_true,
    if_false] <;> push_cast
  · have := abs_add_le ((c0 : ℝ) - H / 2) ((c1 : ℝ) - H / 2)
    calc |(c0 : ℝ) + c1 - (1 + 1) / 2 * H| = |((c0 : ℝ) - H / 2) + ((c1 : ℝ) - H / 2)| := by
          ring_nf
      _ ≤ 2 := by linarith
  · calc |(c0 : ℝ) + 0 - (1 + 0) / 2 * H| = |(c0 : ℝ) - H / 2| := by ring_nf
      _ ≤ 2 := by linarith
  · calc |(0 : ℝ) + c1 - (0 + 1) / 2 * H| = |(c1 : ℝ) - H / 2| := by ring_nf
      _ ≤ 2 := by linarith
  · simp

end LeanLab.Perelli1996.B

