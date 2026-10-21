module

public import LeanLab.PNTPort.BVMax.PrimesUncond

/-!
# Bombieri-Vinogradov against `π(y)/φ(q)`

Lab proof, unit U-5319, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

`bvPiPi`: for every `A > 0` there are `B > 0` and `K` with
`Σ_{q ≤ √x/(log x)^B} |π(y_q; q, a_q) - π(y_q)/φ(q)| ≤ K x/(log x)^A` for every `x ≥ 2`, every choice of
`0 ≤ y_q ≤ x` and of residues `a_q` coprime to `q`: the form `E(x; q) = max_{y ≤ x} max_a |π(y; q, a) -
π(y)/φ(q)|` that sieve papers use as the level of distribution `1/2` input. From `bvPi`, whose
`q = 1` term compares `π(y)` with `liD(y)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real

/-- Bombieri-Vinogradov against `π(y)/φ(q)`, classical form with the maximum over `y ≤ x`. -/
def BVPiPi : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) → ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ x) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |piAP (y q) q (a q) - piAP (y q) 1 1 / q.totient| ≤ K * x / Real.log x ^ A

theorem bvPiPi : BVPiPi := by
  intro A hA
  obtain ⟨B, hB, K1, hK1⟩ := bvPi (A + 1) (by linarith)
  obtain ⟨C, hC, hCsum⟩ := BV.sum_inv_totient_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c' : ℝ := 1 / Real.log 2 + 1 / 2 + B * (-Real.log (Real.log 2)) / Real.log 2 with hc'
  refine ⟨B, hB, max K1 0 / Real.log 2 + max K1 0 * C * c', ?_⟩
  intro x hx a ha y hy
  set L := Real.log x with hL
  set Q := ⌊Real.sqrt x / L ^ B⌋₊ with hQ
  have hx0 : 0 < x := by linarith
  have hlog2L : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hLA1 : L ^ (A + 1) = L ^ A * L := by rw [Real.rpow_add hL0, Real.rpow_one]
  have hK1nn : 0 ≤ max K1 0 := le_max_right _ _
  -- the q = 1 comparison, for each y ≤ x, whenever the range is nonempty
  have hone : ∀ q ∈ Icc 1 Q, |piAP (y q) 1 1 - liD (y q)| ≤ K1 * x / L ^ (A + 1) := by
    intro q hq
    have h := hK1 x hx (fun _ => 1) (fun q => Nat.coprime_one_left q) (fun _ => y q)
      (fun _ => hy q)
    have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, (mem_Icc.mp hq).1.trans (mem_Icc.mp hq).2⟩
    have := single_le_sum (f := fun q' => |piAP (y q) q' 1 - liD (y q) / q'.totient|)
      (fun _ _ => abs_nonneg _) h1
    simp only [Nat.totient_one, Nat.cast_one, div_one] at this
    exact this.trans h
  have hterm : ∀ q ∈ Icc 1 Q, |piAP (y q) q (a q) - piAP (y q) 1 1 / q.totient| ≤
      |piAP (y q) q (a q) - liD (y q) / q.totient| + K1 * x / L ^ (A + 1) * (1 / q.totient) := by
    intro q hq
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hq).1
    have e : piAP (y q) q (a q) - piAP (y q) 1 1 / q.totient =
        (piAP (y q) q (a q) - liD (y q) / q.totient) + (liD (y q) - piAP (y q) 1 1) / q.totient := by
      field_simp; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_div, abs_of_pos hφ, abs_sub_comm, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hone q hq) (by positivity)
  have hs := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hs
  have hmain := hK1 x hx a ha y hy
  -- Σ_q 1/φ(q) ≤ C c' L
  have hlogQ : Real.log Q ≤ L / 2 + B * (-Real.log (Real.log 2)) := by
    rcases Nat.eq_zero_or_pos Q with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      have : 0 ≤ -Real.log (Real.log 2) := by
        have := Real.log_le_sub_one_of_pos hlog2
        have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        linarith [Real.log_nonpos hlog2.le h2.le]
      positivity
    · have hQ1 : (Q : ℝ) ≤ Real.sqrt x / L ^ B := Nat.floor_le (by positivity)
      have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hpos
      have h1 := Real.log_le_log hQ0 hQ1
      rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (Real.rpow_pos_of_pos hL0 B).ne',
        Real.log_sqrt hx0.le, Real.log_rpow hL0] at h1
      have h2 : Real.log (Real.log 2) ≤ Real.log L := Real.log_le_log hlog2 hlog2L
      nlinarith
  have hsumφ : ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient ≤ C * (c' * L) := by
    refine (hCsum Q).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have hd : 1 ≤ L / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
    have hnn : 0 ≤ -Real.log (Real.log 2) := by
      have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      linarith [Real.log_nonpos hlog2.le h2.le]
    have e : c' * L = L / Real.log 2 + L / 2 + B * (-Real.log (Real.log 2)) * (L / Real.log 2) := by
      rw [hc']; field_simp
    rw [e]
    have : B * (-Real.log (Real.log 2)) ≤ B * (-Real.log (Real.log 2)) * (L / Real.log 2) := by
      nlinarith [mul_nonneg hB.le hnn]
    linarith
  have hfin : K1 * x / L ^ (A + 1) * ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient ≤
      max K1 0 * C * c' * x / L ^ A := by
    have hs0 : 0 ≤ ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient := sum_nonneg (fun _ _ => by positivity)
    calc K1 * x / L ^ (A + 1) * ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient
        ≤ max K1 0 * x / L ^ (A + 1) * ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient := by
          apply mul_le_mul_of_nonneg_right _ hs0
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
      _ ≤ max K1 0 * x / L ^ (A + 1) * (C * (c' * L)) :=
          mul_le_mul_of_nonneg_left hsumφ (by positivity)
      _ = max K1 0 * C * c' * x / L ^ A := by rw [hLA1]; field_simp
  have hmain' : K1 * x / L ^ (A + 1) ≤ max K1 0 / Real.log 2 * x / L ^ A := by
    calc K1 * x / L ^ (A + 1) ≤ max K1 0 * x / L ^ (A + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
      _ = max K1 0 * x / L ^ A / L := by rw [hLA1]; field_simp
      _ ≤ max K1 0 * x / L ^ A / Real.log 2 :=
          div_le_div_of_nonneg_left (by positivity) hlog2 hlog2L
      _ = max K1 0 / Real.log 2 * x / L ^ A := by field_simp
  calc _ ≤ _ := hs
    _ ≤ K1 * x / L ^ (A + 1) + max K1 0 * C * c' * x / L ^ A := add_le_add hmain hfin
    _ ≤ max K1 0 / Real.log 2 * x / L ^ A + max K1 0 * C * c' * x / L ^ A := by linarith
    _ = (max K1 0 / Real.log 2 + max K1 0 * C * c') * x / L ^ A := by ring

end LeanLab.PNTPort.BVMax

