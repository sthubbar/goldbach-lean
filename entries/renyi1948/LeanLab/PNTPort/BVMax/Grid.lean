module

public import LeanLab.PNTPort.BV.Statements
public import LeanLab.PNTPort.BV.Helpers

/-!
# Bombieri-Vinogradov with the maximum over `y ≤ x`

Lab proof, unit U-5300, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
no cited input beyond the hypothesis named in each theorem.

The lab's `BV.BombieriVinogradov` is the form at `y = x`: for every choice of residues `a_q`,
`Σ_{q ≤ √x/(log x)^B} |ψ(x; q, a_q) - x/φ(q)| ≪ x/(log x)^A`. The classical statement, Bombieri
1965 and A. I. Vinogradov 1965, also takes the maximum over `y ≤ x` inside the sum. This file shows
the classical form follows from the `y = x` form by a grid argument:

* `card_filter_mod_le`, `psi_sub_bounds`, `err_sub_le`: `ψ(v; q, a) - ψ(u; q, a)` lies in
  `[0, ((v - u)/q + 2) log x]` for `0 ≤ u ≤ v ≤ x`, so `E(y; q, a) = ψ(y; q, a) - y/φ(q)` moves by at
  most `((v - u)/q + 2) log x + (v - u)/φ(q)`;
* `bvMax_eventually`: with `M = ⌈(log x)^{A+3}⌉` grid points `jx/M`, the error at `y_q` is the error
  at the grid point below plus a short interval term; the grid points are summed by the `y = x` form
  with `A' = 2A + 4`, the short interval terms by `Σ_{q ≤ Q} 1/φ(q) ≪ log Q`;
* `bombieriVinogradovMax_of`: `BV.BombieriVinogradov → BombieriVinogradovMax`, every `x ≥ 2`.

`BombieriVinogradovMax` quantifies over every choice function `y : ℕ → ℝ` with `0 ≤ y q ≤ x`
and every choice of residues; a bound for every choice is a bound for the sum of the suprema,
which is the usual `Σ_q max_{y ≤ x} max_{(a,q)=1} |ψ(y; q, a) - y/φ(q)|`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real Filter
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.HeathBrown1985 (psi)

/-- Bombieri-Vinogradov, classical form: the maximum over `y ≤ x` and over the residue class is
inside the sum, written with choice functions `y` and `a`. -/
def BombieriVinogradovMax : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |psi (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A

/-- `E(y; q, a) = ψ(y; q, a) - y/φ(q)`. -/
noncomputable def err (y : ℝ) (q a : ℕ) : ℝ := psi y q a - y / q.totient

lemma err_zero (q a : ℕ) : err 0 q a = 0 := by
  simp [err, psi]

/-- At most `(M - m)/q + 1` integers of `(m, M]` lie in one residue class mod `q`. -/
lemma card_filter_mod_le (m M q r : ℕ) (hq : 0 < q) (hmM : m ≤ M) :
    (((Ioc m M).filter (fun n => n % q = r)).card : ℝ) ≤ ((M : ℝ) - m) / q + 1 := by
  set c := m + 1 with hc
  have hinj : Set.InjOn (fun n => (n - c) / q)
      (((Ioc m M).filter (fun n => n % q = r) : Finset ℕ) : Set ℕ) := by
    intro n1 h1 n2 h2 he
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at h1 h2
    simp only at he
    have hmod : (n1 - c) % q = (n2 - c) % q := by
      have : n1 - c + c ≡ n2 - c + c [MOD q] := by
        rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
        exact h1.2.trans h2.2.symm
      exact Nat.ModEq.add_right_cancel' c this
    have e1 := Nat.div_add_mod (n1 - c) q
    have e2 := Nat.div_add_mod (n2 - c) q
    rw [he, hmod] at e1
    omega
  have hmaps : ∀ n ∈ (Ioc m M).filter (fun n => n % q = r),
      (fun n => (n - c) / q) n ∈ range ((M - c) / q + 1) := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    rw [mem_range]
    show (n - c) / q < (M - c) / q + 1
    have : (n - c) / q ≤ (M - c) / q := Nat.div_le_div_right (by omega)
    omega
  have hcard := card_le_card_of_injOn _ hmaps hinj
  rw [card_range] at hcard
  have h1 : (((M - c) / q : ℕ) : ℝ) ≤ ((M - c : ℕ) : ℝ) / q := Nat.cast_div_le
  have h2 : ((M - c : ℕ) : ℝ) ≤ (M : ℝ) - m := by
    rcases Nat.lt_or_ge M c with h | h
    · rw [Nat.sub_eq_zero_of_le h.le]
      have : (m : ℝ) ≤ M := by exact_mod_cast hmM
      simp; linarith
    · rw [Nat.cast_sub h, hc]; push_cast; linarith
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  calc (((Ioc m M).filter (fun n => n % q = r)).card : ℝ)
      ≤ (((M - c) / q + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (((M - c) / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ ((M : ℝ) - m) / q + 1 := by
        gcongr
        exact h1.trans (div_le_div_of_nonneg_right h2 hq'.le)

/-- `0 ≤ ψ(v; q, a) - ψ(u; q, a) ≤ ((v - u)/q + 2) log x` for `0 ≤ u ≤ v ≤ x`, `x ≥ 1`. -/
lemma psi_sub_bounds {u v x : ℝ} (q a : ℕ) (hq : 0 < q) (hu : 0 ≤ u) (huv : u ≤ v)
    (hvx : v ≤ x) (hx : 1 ≤ x) :
    0 ≤ psi v q a - psi u q a ∧ psi v q a - psi u q a ≤ ((v - u) / q + 2) * Real.log x := by
  have hv : 0 ≤ v := hu.trans huv
  have hfl : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_le_floor huv
  have hU : Icc 1 ⌊v⌋₊ = Icc 1 ⌊u⌋₊ ∪ Ioc ⌊u⌋₊ ⌊v⌋₊ := by
    ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hD : Disjoint (Icc 1 ⌊u⌋₊) (Ioc ⌊u⌋₊ ⌊v⌋₊) := by
    rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  have hdiff : psi v q a - psi u q a =
      ∑ n ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n => n % q = a % q), Λ n := by
    unfold psi
    rw [hU, filter_union, sum_union (disjoint_filter_filter hD)]
    ring
  rw [hdiff]
  refine ⟨sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg), ?_⟩
  have hterm : ∀ n ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n => n % q = a % q), Λ n ≤ Real.log x := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hnv : (n : ℝ) ≤ v := by
      have : (n : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast hn.1.2
      exact this.trans (Nat.floor_le hv)
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by linarith) (hnv.trans hvx))
  have hsum := sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hcard := card_filter_mod_le ⌊u⌋₊ ⌊v⌋₊ q (a % q) hq hfl
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hfv : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv
  have hfu : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  have hcard2 : ((⌊v⌋₊ : ℝ) - ⌊u⌋₊) / q + 1 ≤ (v - u) / q + 2 := by
    have : ((⌊v⌋₊ : ℝ) - ⌊u⌋₊) / q ≤ (v - u) / q + 1 / q := by
      rw [← add_div]; gcongr; linarith
    have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
    linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc _ ≤ _ := hsum
    _ ≤ ((v - u) / q + 2) * Real.log x := by
        apply mul_le_mul_of_nonneg_right (hcard.trans hcard2) hlog

/-- `|E(v) - E(u)| ≤ ((v - u)/q + 2) log x + (v - u)/φ(q)`. -/
lemma err_sub_le {u v x : ℝ} (q a : ℕ) (hq : 0 < q) (hu : 0 ≤ u) (huv : u ≤ v)
    (hvx : v ≤ x) (hx : 1 ≤ x) :
    |err v q a - err u q a| ≤ ((v - u) / q + 2) * Real.log x + (v - u) / q.totient := by
  obtain ⟨h0, h1⟩ := psi_sub_bounds q a hq hu huv hvx hx
  have hT : 0 ≤ (v - u) / (q.totient : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have e : err v q a - err u q a = (psi v q a - psi u q a) - (v - u) / q.totient := by
    unfold err; ring
  rw [e, abs_le]
  constructor <;> linarith

lemma sqrt_le_self' {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

set_option maxHeartbeats 1000000 in
/-- The grid step. Under `log x ≥ 2` and `(log x)^{A+4} ≤ √x`, the classical form follows from the
`y = x` form, with `B = B₁ + A + 4` where `B₁` is the `y = x` exponent at `A' = 2A + 4`. -/
theorem bvMax_eventually (hBV : BV.BombieriVinogradov) (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → 2 ≤ Real.log x →
      Real.log x ^ (A + 4) ≤ Real.sqrt x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
        ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
          |psi (y q) q (a q) - y q / q.totient| ≤ K * x / Real.log x ^ A := by
  obtain ⟨B1, hB1, K1, hK1⟩ := hBV (2 * A + 4) (by linarith)
  obtain ⟨C, hC, hCsum⟩ := BV.sum_inv_totient_le
  -- `K1 ≥ 0`, from the bound at `x = 2`
  have hK1nn : 0 ≤ K1 := by
    have h := hK1 2 le_rfl (fun _ => 1) (fun q => Nat.coprime_one_left q)
    have hs : 0 ≤ ∑ q ∈ Icc 1 ⌊Real.sqrt 2 / Real.log 2 ^ B1⌋₊,
        |psi 2 q 1 - 2 / q.totient| := sum_nonneg (fun _ _ => abs_nonneg _)
    have hl : 0 < Real.log 2 ^ (2 * A + 4) := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
    by_contra hneg
    push Not at hneg
    have : K1 * 2 / Real.log 2 ^ (2 * A + 4) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hl
    linarith
  refine ⟨B1 + A + 4, by linarith, K1 * 2 ^ (2 * A + 4) + 4 * C + 2, ?_⟩
  intro x hx hL hLx a ha y hy
  set L := Real.log x with hLdef
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hLA0 : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hLA3 : 1 ≤ L ^ (A + 3) := Real.one_le_rpow hL1 (by linarith)
  have hLA4 : L ^ (A + 4) = L ^ (A + 3) * L := by
    rw [show A + 4 = (A + 3) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  set M : ℕ := ⌈L ^ (A + 3)⌉₊ with hMdef
  have hM1 : L ^ (A + 3) ≤ M := Nat.le_ceil _
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : (1 : ℝ) ≤ M := by linarith
  have hM2 : (M : ℝ) ≤ L ^ (A + 4) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ L ^ (A + 3) by linarith)
    rw [hLA4]; nlinarith
  -- grid points and the index below `y q`
  set g : ℕ → ℝ := fun j => j * x / M with hg
  set J : ℕ → ℕ := fun q => ⌊y q * M / x⌋₊ with hJ
  have hJle : ∀ q, g (J q) ≤ y q := by
    intro q
    have h := Nat.floor_le (show 0 ≤ y q * M / x by
      have := (hy q).1; positivity)
    simp only [hg, hJ]
    rw [div_le_iff₀ hMpos]
    rw [le_div_iff₀ hx0] at h
    linarith
  have hJgap : ∀ q, y q - g (J q) ≤ x / M := by
    intro q
    have h := Nat.lt_floor_add_one (y q * M / x)
    simp only [hg, hJ]
    rw [div_lt_iff₀ hx0] at h
    have : y q * M ≤ (⌊y q * M / x⌋₊ : ℝ) * x + x := by linarith
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hMpos]
    linarith
  have hJM : ∀ q, J q ≤ M := by
    intro q
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hx0]
    have := (hy q).2
    nlinarith
  set Q : ℕ := ⌊Real.sqrt x / L ^ (B1 + A + 4)⌋₊ with hQdef
  have hLB : 1 ≤ L ^ (B1 + A + 4) := Real.one_le_rpow hL1 (by linarith)
  have hQx : (Q : ℝ) ≤ Real.sqrt x := by
    have h := Nat.floor_le (show 0 ≤ Real.sqrt x / L ^ (B1 + A + 4) by positivity)
    exact h.trans (div_le_self hsx0.le hLB)
  have hsxL : L ^ (A + 1) ≤ Real.sqrt x :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)).trans hLx
  -- Step 1: pass to the grid point below
  have hstep : ∀ q ∈ Icc 1 Q, |psi (y q) q (a q) - y q / q.totient| ≤
      (∑ j ∈ Icc 1 M, |err (g j) q (a q)|) + (x / M * (L + 1)) * (1 / q.totient) + 2 * L := by
    intro q hq
    rw [mem_Icc] at hq
    have hq0 : 0 < q := by omega
    have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hg0 : 0 ≤ g (J q) := by simp only [hg]; positivity
    have hd := err_sub_le q (a q) hq0 hg0 (hJle q) (hy q).2 (by linarith)
    have hgap := hJgap q
    have hgap0 : 0 ≤ y q - g (J q) := by linarith [hJle q]
    have hxM : 0 ≤ x / M := by positivity
    have h1 : (y q - g (J q)) / q ≤ x / M * (1 / q.totient) := by
      rw [mul_one_div]
      calc (y q - g (J q)) / q ≤ (y q - g (J q)) / q.totient :=
            div_le_div_of_nonneg_left hgap0 (by linarith) hφq
        _ ≤ x / M / q.totient := div_le_div_of_nonneg_right hgap (by linarith)
    have h2 : (y q - g (J q)) / q.totient ≤ x / M * (1 / q.totient) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hgap (by linarith)
    have hgrid : |err (g (J q)) q (a q)| ≤ ∑ j ∈ Icc 1 M, |err (g j) q (a q)| := by
      rcases Nat.eq_zero_or_pos (J q) with h0 | hpos
      · have : g (J q) = 0 := by simp only [hg, h0]; simp
        rw [this, err_zero, abs_zero]
        exact sum_nonneg (fun _ _ => abs_nonneg _)
      · exact single_le_sum (f := fun j => |err (g j) q (a q)|)
          (fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hpos, hJM q⟩)
    have htri : |err (y q) q (a q)| ≤ |err (g (J q)) q (a q)| +
        |err (y q) q (a q) - err (g (J q)) q (a q)| := by
      have := abs_add_le (err (g (J q)) q (a q)) (err (y q) q (a q) - err (g (J q)) q (a q))
      simpa using this
    have hX : 0 ≤ x / M * (1 / q.totient) := by positivity
    show |err (y q) q (a q)| ≤ _
    nlinarith
  -- Step 2: each grid point by the `y = x` form
  have hgrid_bound : ∀ j ∈ Icc 1 M, ∑ q ∈ Icc 1 Q, |err (g j) q (a q)| ≤
      K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4) := by
    intro j hj
    rw [mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hjM : (j : ℝ) ≤ M := by exact_mod_cast hj.2
    have hgx : g j ≤ x := by
      simp only [hg]; rw [div_le_iff₀ hMpos]; nlinarith
    have hgxM : x / M ≤ g j := by
      simp only [hg]; rw [mul_div_assoc]; nlinarith [show 0 ≤ x / M by positivity]
    have hxMs : Real.sqrt x ≤ x / M := by
      rw [le_div_iff₀ hMpos]
      calc Real.sqrt x * M ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_left (hM2.trans hLx) hsx0.le
        _ = x := Real.mul_self_sqrt hx0.le
    have hgs : Real.sqrt x ≤ g j := hxMs.trans hgxM
    have hs2 : 2 ≤ Real.sqrt x := by
      have : L ≤ L ^ (A + 4) := by
        conv_lhs => rw [← Real.rpow_one L]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      linarith
    have hg2 : 2 ≤ g j := by linarith
    have hg0 : 0 < g j := by linarith
    have hlogg : L / 2 ≤ Real.log (g j) := by
      have := Real.log_le_log hsx0 hgs
      rwa [Real.log_sqrt hx0.le] at this
    have hloggx : Real.log (g j) ≤ L := Real.log_le_log hg0 hgx
    -- the range `q ≤ Q` is inside the `y = x` range at `g j`
    have hsub : Icc 1 Q ⊆ Icc 1 ⌊Real.sqrt (g j) / Real.log (g j) ^ B1⌋₊ := by
      apply Icc_subset_Icc_right
      apply Nat.floor_le_floor
      have hlg0 : 0 < Real.log (g j) := by linarith
      have hp1 : Real.log (g j) ^ B1 ≤ L ^ B1 := Real.rpow_le_rpow hlg0.le hloggx hB1.le
      have hp0 : 0 < Real.log (g j) ^ B1 := Real.rpow_pos_of_pos hlg0 B1
      have hsM : Real.sqrt (M : ℝ) ≤ M := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have hsg : Real.sqrt x / L ^ (A + 4) ≤ Real.sqrt (g j) := by
        have h1 : Real.sqrt (x / M) ≤ Real.sqrt (g j) := Real.sqrt_le_sqrt hgxM
        rw [Real.sqrt_div' x (Nat.cast_nonneg M)] at h1
        refine le_trans ?_ h1
        apply div_le_div_of_nonneg_left hsx0.le (Real.sqrt_pos.mpr hMpos)
        exact hsM.trans hM2
      have hsplit : L ^ (B1 + A + 4) = L ^ (A + 4) * L ^ B1 := by
        rw [show B1 + A + 4 = (A + 4) + B1 by ring, Real.rpow_add hL0]
      rw [hsplit, ← div_div]
      calc Real.sqrt x / L ^ (A + 4) / L ^ B1
          ≤ Real.sqrt (g j) / L ^ B1 := div_le_div_of_nonneg_right hsg (by positivity)
        _ ≤ Real.sqrt (g j) / Real.log (g j) ^ B1 :=
            div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hp0 hp1
    have hmain := hK1 (g j) hg2 a ha
    have hle : ∑ q ∈ Icc 1 Q, |err (g j) q (a q)| ≤
        ∑ q ∈ Icc 1 ⌊Real.sqrt (g j) / Real.log (g j) ^ B1⌋₊,
          |psi (g j) q (a q) - g j / q.totient| :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    refine hle.trans (hmain.trans ?_)
    have hl2 : (L / 2) ^ (2 * A + 4) ≤ Real.log (g j) ^ (2 * A + 4) :=
      Real.rpow_le_rpow (by linarith) hlogg (by linarith)
    have hl2' : (L / 2) ^ (2 * A + 4) = L ^ (2 * A + 4) / 2 ^ (2 * A + 4) :=
      Real.div_rpow hL0.le (by norm_num) _
    have hpos2 : 0 < (L / 2) ^ (2 * A + 4) := Real.rpow_pos_of_pos (by linarith) _
    have h2p : 0 < (2 : ℝ) ^ (2 * A + 4) := Real.rpow_pos_of_pos (by norm_num) _
    have hLp : 0 < L ^ (2 * A + 4) := Real.rpow_pos_of_pos hL0 _
    calc K1 * g j / Real.log (g j) ^ (2 * A + 4) ≤ K1 * x / (L / 2) ^ (2 * A + 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hgx hK1nn) hpos2 hl2
      _ = K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4) := by
          rw [hl2']; field_simp
  -- Step 3: assemble
  have hsum1 : ∑ q ∈ Icc 1 Q, |psi (y q) q (a q) - y q / q.totient| ≤
      (∑ j ∈ Icc 1 M, ∑ q ∈ Icc 1 Q, |err (g j) q (a q)|) +
      (x / M * (L + 1)) * (∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient) + 2 * L * Q := by
    refine (sum_le_sum hstep).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_add_distrib, sum_comm, ← mul_sum, sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    simp only [add_tsub_cancel_right]
    ring
  have hA1 : ∑ j ∈ Icc 1 M, ∑ q ∈ Icc 1 Q, |err (g j) q (a q)| ≤ K1 * 2 ^ (2 * A + 4) * x / L ^ A := by
    refine (sum_le_sum hgrid_bound).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, add_tsub_cancel_right]
    have hsplit : L ^ (2 * A + 4) = L ^ (A + 4) * L ^ A := by
      rw [show 2 * A + 4 = (A + 4) + A by ring, Real.rpow_add hL0]
    have hLA4p : 0 < L ^ (A + 4) := Real.rpow_pos_of_pos hL0 _
    have hX : 0 ≤ K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4) := by positivity
    calc (M : ℝ) * (K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4))
        ≤ L ^ (A + 4) * (K1 * 2 ^ (2 * A + 4) * x / L ^ (2 * A + 4)) :=
          mul_le_mul_of_nonneg_right hM2 hX
      _ = K1 * 2 ^ (2 * A + 4) * x / L ^ A := by
          rw [hsplit]; field_simp
  have hA2 : (x / M * (L + 1)) * (∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient) ≤ 4 * C * x / L ^ A := by
    have hc := hCsum Q
    have hlogQ : Real.log Q ≤ L := by
      rcases Nat.eq_zero_or_pos Q with h0 | hpos
      · rw [h0]; simp; linarith
      · have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hpos
        have := Real.log_le_log hQ0 (hQx.trans (sqrt_le_self' ?_))
        · exact this
        · nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx0.le]
    have hxM0 : 0 ≤ x / M * (L + 1) := by positivity
    have hstep1 : (x / M * (L + 1)) * (∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient) ≤
        (x / M * (L + 1)) * (C * (1 + L)) :=
      mul_le_mul_of_nonneg_left (hc.trans (by nlinarith)) hxM0
    refine hstep1.trans ?_
    have hLA3' : L ^ (A + 3) = L ^ A * L ^ 3 := by
      rw [Real.rpow_add hL0]; norm_cast
    have hxM : x / M ≤ x / (L ^ A * L ^ 3) := by
      rw [← hLA3']; exact div_le_div_of_nonneg_left hx0.le (by linarith) hM1
    calc x / M * (L + 1) * (C * (1 + L)) ≤ x / (L ^ A * L ^ 3) * (L + 1) * (C * (1 + L)) := by
          have : 0 ≤ (L + 1) * (C * (1 + L)) := by positivity
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hxM this
      _ ≤ x / (L ^ A * L ^ 3) * (4 * C * L ^ 2) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have e : (L + 1) * (C * (1 + L)) = C * (L + 1) ^ 2 := by ring
          have h4 : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
          rw [e]
          calc C * (L + 1) ^ 2 ≤ C * (4 * L ^ 2) := mul_le_mul_of_nonneg_left h4 hC.le
            _ = 4 * C * L ^ 2 := by ring
      _ = 4 * C * x / L ^ A * (1 / L) := by field_simp
      _ ≤ 4 * C * x / L ^ A := by
          have : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL1
          have : 0 ≤ 4 * C * x / L ^ A := by positivity
          nlinarith
  have hA3 : 2 * L * Q ≤ 2 * x / L ^ A := by
    have hLA1 : L ^ (A + 1) = L ^ A * L := by rw [Real.rpow_add hL0, Real.rpow_one]
    rw [le_div_iff₀ hLA0]
    have h1 : L * Q * L ^ A ≤ L ^ (A + 1) * Real.sqrt x := by
      rw [hLA1]
      have := mul_le_mul_of_nonneg_left hQx (show 0 ≤ L * L ^ A by positivity)
      nlinarith
    have h2 : L ^ (A + 1) * Real.sqrt x ≤ x := by
      calc L ^ (A + 1) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hsxL hsx0.le
        _ = x := Real.mul_self_sqrt hx0.le
    nlinarith
  calc ∑ q ∈ Icc 1 Q, |psi (y q) q (a q) - y q / q.totient|
      ≤ _ := hsum1
    _ ≤ K1 * 2 ^ (2 * A + 4) * x / L ^ A + 4 * C * x / L ^ A + 2 * x / L ^ A := by
        linarith
    _ = (K1 * 2 ^ (2 * A + 4) + 4 * C + 2) * x / L ^ A := by ring

/-- The classical Bombieri-Vinogradov form from the lab's `y = x` form, for every `x ≥ 2`. -/
theorem bombieriVinogradovMax_of (hBV : BV.BombieriVinogradov) : BombieriVinogradovMax := by
  intro A hA
  obtain ⟨B, hB, K, hK⟩ := bvMax_eventually hBV A hA
  have h1 : ∀ᶠ x in atTop, 2 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 2
  have h2 : ∀ᶠ x in atTop, Real.log x ^ (A + 4) ≤ Real.sqrt x := by
    have ho := (isLittleO_log_rpow_rpow_atTop (A + 4) (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      zero_lt_one
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hx
    rw [Real.sqrt_eq_rpow]
    exact (le_abs_self _).trans (hx.trans (le_of_eq (abs_of_nonneg (by positivity))))
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (h1.and h2)
  set X1 := max X0 2 with hX1
  have hX12 : 2 ≤ X1 := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set T := ((X1 + 2) * Real.log X1 + X1) * Real.log X1 ^ A / Real.log 2 ^ B with hT
  refine ⟨B, hB, max K T, ?_⟩
  intro x hx a ha y hy
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have hxL : 0 ≤ x / Real.log x ^ A := by positivity
  by_cases hxX : X0 ≤ x
  · refine (hK x hx (hX0 x hxX).1 (hX0 x hxX).2 a ha y hy).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxL
  · push Not at hxX
    have hxX1 : x ≤ X1 := (hxX.le).trans (le_max_left _ _)
    set L := Real.log x with hLdef
    have hLX : L ≤ Real.log X1 := Real.log_le_log hx0 hxX1
    have hlog2L : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
    have hterm : ∀ q ∈ Icc 1 ⌊Real.sqrt x / L ^ B⌋₊,
        |psi (y q) q (a q) - y q / q.totient| ≤ (x + 2) * L + x := by
      intro q hq
      rw [mem_Icc] at hq
      have hq0 : 0 < q := by omega
      have hd := err_sub_le q (a q) hq0 le_rfl (hy q).1 (hy q).2 (by linarith)
      rw [err_zero, sub_zero, sub_zero] at hd
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
      have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have hy0 := (hy q).1
      have hyx := (hy q).2
      have e1 : y q / q ≤ x := (div_le_self hy0 hq1).trans hyx
      have e2 : y q / q.totient ≤ x := (div_le_self hy0 hφ1).trans hyx
      show |err (y q) q (a q)| ≤ _
      nlinarith
    have hsum := sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul, Nat.card_Icc, add_tsub_cancel_right] at hsum
    have hLB : Real.log 2 ^ B ≤ L ^ B := Real.rpow_le_rpow hlog2.le hlog2L hB.le
    have hl2B : 0 < Real.log 2 ^ B := Real.rpow_pos_of_pos hlog2 B
    have hQ : (⌊Real.sqrt x / L ^ B⌋₊ : ℝ) ≤ x / Real.log 2 ^ B := by
      refine (Nat.floor_le (by positivity)).trans ?_
      calc Real.sqrt x / L ^ B ≤ x / L ^ B :=
            div_le_div_of_nonneg_right (sqrt_le_self' (by nlinarith)) (by positivity)
        _ ≤ x / Real.log 2 ^ B := div_le_div_of_nonneg_left hx0.le hl2B hLB
    have hW : 0 ≤ (x + 2) * L + x := by positivity
    have hLAX : L ^ A ≤ Real.log X1 ^ A := Real.rpow_le_rpow hL0.le hLX hA.le
    have hWX : (x + 2) * L + x ≤ (X1 + 2) * Real.log X1 + X1 := by
      have : (x + 2) * L ≤ (X1 + 2) * Real.log X1 :=
        mul_le_mul (by linarith) hLX hL0.le (by linarith)
      linarith
    calc _ ≤ _ := hsum
      _ ≤ x / Real.log 2 ^ B * ((x + 2) * L + x) := mul_le_mul_of_nonneg_right hQ hW
      _ ≤ T * x / L ^ A := by
          rw [hT, le_div_iff₀ hLA0]
          have hlX : 0 ≤ Real.log X1 := Real.log_nonneg (by linarith)
          have : x / Real.log 2 ^ B * ((x + 2) * L + x) * L ^ A ≤
              x / Real.log 2 ^ B * (((X1 + 2) * Real.log X1 + X1) * Real.log X1 ^ A) := by
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hWX hLAX hLA0.le (by positivity)
          calc _ ≤ _ := this
            _ = _ := by field_simp
      _ ≤ max K T * x / L ^ A := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxL

end LeanLab.PNTPort.BVMax

