module

public import LeanLab.PNTPort.Vinogradov.Final
public import LeanLab.Routes.R0001Markov

/-!
# Minor arcs: the sup bound and the unconditional minor arc exceptional count

Lab proof, unit U-5251. AI wrote this file. Known mathematics, no cited input: the minor arc
half of the Estermann, Chudakov, van der Corput theorem, Montgomery-Vaughan 1975 style.

* `MinorAt P Q α`: no `a/q` with `q ≤ P` has `|α - a/q| ≤ 1/(q(Q + 1))`.
* `minor_sup`: for `1 ≤ P`, `1 ≤ Q ≤ N` and `α` minor,
  `‖S(α)‖ ≤ 300 (N/√P + N^{4/5} + √(NQ)) (1 + log N)⁴`, from Dirichlet's theorem and
  `vinogradov_minor`.
* `dft_PhiL_norm`: on `ZMod M`, `M > N`, the DFT of `n ↦ Λ(n) 1_{1 ≤ n ≤ N}` has modulus
  `‖S(k/M)‖`.
* `minor_exceptional`: with `m` the minor frequencies `k`, `k/M` minor, and `T ≥ 0`,
  `#{n mod M : ‖∑_{k ∈ m} S(k)² e(nk/M)‖ ≥ T} · T² ≤ M² B² ∑_{n ≤ N} Λ(n)²`, `B` the sup bound.
  The minor arc part of the binary count `∑_{a + b = n} Λ(a)Λ(b)` is small for all but few `n`;
  the major arcs still need Siegel-Walfisz. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open LeanLab.PNTPort.LargeSieve

/-- `α` is on the minor arcs: no fraction `a/q` with `q ≤ P` is within `1/(q(Q+1))`. -/
def MinorAt (P Q : ℕ) (α : ℝ) : Prop :=
  ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ P → 1 / ((q : ℝ) * (Q + 1)) < |α - a / q|

/-- Dirichlet's theorem in reduced form. -/
lemma dirichlet_reduced (α : ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ Q ∧ IsCoprime a (q : ℤ) ∧
      |α - a / q| ≤ 1 / ((q : ℝ) * (Q + 1)) := by
  obtain ⟨j, k, hk0, hkQ, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α (n := Q) (by omega)
  set g : ℕ := Int.gcd j k with hg
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  have hgj : (g : ℤ) ∣ j := Int.gcd_dvd_left j k
  have hgk : (g : ℤ) ∣ k := Int.gcd_dvd_right j k
  obtain ⟨a, ha⟩ := hgj
  obtain ⟨q', hq'⟩ := hgk
  have hq'pos : 0 < q' := by
    rcases lt_or_ge 0 q' with h | h
    · exact h
    · exfalso; have : (g : ℤ) * q' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      omega
  have hcop : Int.gcd a q' = 1 := by
    have := Int.gcd_div_gcd_div_gcd (i := j) (j := k) (by omega)
    rw [← hg] at this
    have e1 : j / (g : ℤ) = a := by rw [ha]; exact Int.mul_ediv_cancel_left _ (by omega)
    have e2 : k / (g : ℤ) = q' := by rw [hq']; exact Int.mul_ediv_cancel_left _ (by omega)
    rwa [e1, e2] at this
  refine ⟨a, q'.toNat, by omega, ?_, ?_, ?_⟩
  · have : (g : ℤ) * q' ≤ Q := by omega
    have h1 : (1 : ℤ) ≤ g := by exact_mod_cast hg0
    have : q' ≤ Q := by nlinarith
    omega
  · rw [Int.toNat_of_nonneg hq'pos.le, Int.isCoprime_iff_gcd_eq_one]; exact hcop
  · have hqr : ((q'.toNat : ℕ) : ℝ) = (q' : ℝ) := by
      rw [show ((q'.toNat : ℕ) : ℝ) = ((q'.toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg hq'pos.le]
    rw [hqr]
    have hgr : (1 : ℝ) ≤ g := by exact_mod_cast hg0
    have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'pos
    have hQ1 : (0 : ℝ) < Q + 1 := by positivity
    have hjk' : |(g : ℝ) * (q' * α - a)| ≤ 1 / (Q + 1) := by
      have : (k : ℝ) * α - j = (g : ℝ) * (q' * α - a) := by
        rw [ha, hq']; push_cast; ring
      rw [← this]; exact hjk
    rw [abs_mul, abs_of_pos (by linarith)] at hjk'
    have h2 : |(q' : ℝ) * α - a| ≤ 1 / (Q + 1) := by
      calc |(q' : ℝ) * α - a| ≤ g * |(q' : ℝ) * α - a| := le_mul_of_one_le_left (abs_nonneg _) hgr
        _ ≤ _ := hjk'
    have h3 : α - a / q' = ((q' : ℝ) * α - a) / q' := by field_simp
    rw [h3, abs_div, abs_of_pos hq'r, div_le_iff₀ hq'r]
    calc |(q' : ℝ) * α - a| ≤ 1 / (Q + 1) := h2
      _ = 1 / (q' * (Q + 1)) * q' := by field_simp

/-- The sup of `‖S‖` over the minor arcs. -/
theorem minor_sup {P Q N : ℕ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hQN : Q ≤ N) {α : ℝ}
    (h : MinorAt P Q α) :
    ‖S N α‖ ≤ 300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
      (1 + Real.log N) ^ 4 := by
  obtain ⟨a, q, hq1, hqQ, hcop, hα⟩ := dirichlet_reduced α hQ
  have hPq : P < q := by
    by_contra hle
    exact absurd hα (not_le.2 (h a q hq1 (by omega)))
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hα2 : |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine hα.trans ?_
    have : (q : ℝ) ≤ Q + 1 := by
      have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
      linarith
    rw [sq]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left this (by linarith))
  refine (vinogradov_minor hq1 hcop hα2 (le_trans hqQ hQN)).trans ?_
  have hL : 0 ≤ (1 + Real.log N) ^ 4 := by
    have := Real.log_natCast_nonneg N; positivity
  apply mul_le_mul_of_nonneg_right _ hL
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h1 : (N : ℝ) / Real.sqrt q ≤ N / Real.sqrt P := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg N)
      (Real.sqrt_pos.2 (by exact_mod_cast hP))
    exact Real.sqrt_le_sqrt (by exact_mod_cast hPq.le)
  have h2 : Real.sqrt (N * q) ≤ Real.sqrt (N * Q) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqQ) (Nat.cast_nonneg N)
  linarith

lemma S_neg (N : ℕ) (θ : ℝ) : S N (-θ) = (starRingEnd ℂ) (S N θ) := by
  unfold S
  rw [map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, mul_neg, e_neg]

lemma norm_S_neg (N : ℕ) (θ : ℝ) : ‖S N (-θ)‖ = ‖S N θ‖ := by
  rw [S_neg, Complex.norm_conj]

/-- The weight `Λ(n) 1_{1 ≤ n ≤ N}` on `ZMod M`. -/
noncomputable def PhiL (N M : ℕ) : ZMod M → ℂ :=
  fun j => if 1 ≤ j.val ∧ j.val ≤ N then (ArithmeticFunction.vonMangoldt j.val : ℂ) else 0

lemma sum_zmod_eq_range {M : ℕ} [NeZero M] (F : ℕ → ℂ) :
    ∑ j : ZMod M, F j.val = ∑ n ∈ range M, F n := by
  refine sum_nbij' (fun j => j.val) (fun n => (n : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact mem_range.2 (ZMod.val_lt j)
  · intro n _; exact mem_univ _
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro n hn
    exact ZMod.val_natCast_of_lt (mem_range.1 hn)
  · intro j _; rfl

lemma sum_zmod_eq_range_real {M : ℕ} [NeZero M] (F : ℕ → ℝ) :
    ∑ j : ZMod M, F j.val = ∑ n ∈ range M, F n := by
  refine sum_nbij' (fun j => j.val) (fun n => (n : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact mem_range.2 (ZMod.val_lt j)
  · intro n _; exact mem_univ _
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro n hn
    exact ZMod.val_natCast_of_lt (mem_range.1 hn)
  · intro j _; rfl

lemma stdAddChar_neg_mul {M : ℕ} [NeZero M] (n : ℕ) (k : ZMod M) :
    (stdAddChar (-((n : ZMod M) * k)) : ℂ) = e (n * (-(k.val : ℝ) / M)) := by
  set z : ℤ := -((n : ℤ) * (k.val : ℤ)) with hz
  have h1 : -((n : ZMod M) * k) = (Int.cast z : ZMod M) := by
    rw [hz]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, stdAddChar_apply, toCircle_intCast, hz]
  unfold e
  congr 1
  push_cast
  ring

theorem dft_PhiL {N M : ℕ} [NeZero M] (hNM : N < M) (k : ZMod M) :
    𝓕 (PhiL N M) k = S N (-(k.val : ℝ) / M) := by
  rw [dft_apply]
  have h := sum_zmod_eq_range (M := M) (fun n => (stdAddChar (-((n : ZMod M) * k)) : ℂ) *
    (if 1 ≤ n ∧ n ≤ N then (ArithmeticFunction.vonMangoldt n : ℂ) else 0))
  simp only [ZMod.natCast_zmod_val] at h
  simp only [smul_eq_mul, PhiL]
  rw [h]
  unfold S
  have hf : (range M).filter (fun n => 1 ≤ n ∧ n ≤ N) = Icc 1 N := by
    ext n; simp only [mem_filter, mem_range, mem_Icc]; omega
  simp only [mul_ite, mul_zero]
  rw [← sum_filter, hf]
  refine sum_congr rfl fun n _ => ?_
  rw [stdAddChar_neg_mul, mul_comm]

theorem dft_PhiL_norm {N M : ℕ} [NeZero M] (hNM : N < M) (k : ZMod M) :
    ‖𝓕 (PhiL N M) k‖ = ‖S N ((k.val : ℝ) / M)‖ := by
  rw [dft_PhiL hNM, neg_div, norm_S_neg]

theorem sum_PhiL_sq {N M : ℕ} [NeZero M] (hNM : N < M) :
    ∑ j, ‖PhiL N M j‖ ^ 2 = ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  have h := sum_zmod_eq_range_real (M := M) (fun n =>
    ‖(if 1 ≤ n ∧ n ≤ N then (ArithmeticFunction.vonMangoldt n : ℂ) else 0)‖ ^ 2)
  simp only [PhiL]
  rw [h]
  have hf : (range M).filter (fun n => 1 ≤ n ∧ n ≤ N) = Icc 1 N := by
    ext n; simp only [mem_filter, mem_range, mem_Icc]; omega
  rw [← hf, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp

open Classical in
/-- The minor frequencies mod `M`. -/
noncomputable def minorSet (P Q M : ℕ) [NeZero M] : Finset (ZMod M) :=
  univ.filter (fun k : ZMod M => MinorAt P Q ((k.val : ℝ) / M))

/-- **The minor arc exceptional count**, unconditional. -/
theorem minor_exceptional {N M P Q : ℕ} [NeZero M] (hNM : N < M) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hQN : Q ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    ((univ.filter fun n =>
        T ≤ ‖LeanLab.Routes.R0001.minorPart (PhiL N M) (minorSet P Q M) n‖).card : ℝ) * T ^ 2
      ≤ (M : ℝ) ^ 2 * (300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt (N * Q)) * (1 + Real.log N) ^ 4) ^ 2 *
        ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  set B := 300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt (N * Q)) * (1 + Real.log N) ^ 4 with hB
  refine (LeanLab.Routes.R0001.card_large_minor_le (PhiL N M) (minorSet P Q M) T hT).trans ?_
  have hk : ∀ k ∈ minorSet P Q M, ‖𝓕 (PhiL N M) k‖ ^ 4 ≤ B ^ 2 * ‖𝓕 (PhiL N M) k‖ ^ 2 := by
    intro k hk
    have hm : MinorAt P Q ((k.val : ℝ) / M) := by
      simp only [minorSet, Finset.mem_filter] at hk; exact hk.2
    have h1 : ‖𝓕 (PhiL N M) k‖ ≤ B := by
      rw [dft_PhiL_norm hNM]; exact minor_sup hP hQ hQN hm
    have h2 : ‖𝓕 (PhiL N M) k‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have : ‖𝓕 (PhiL N M) k‖ ^ 4 = ‖𝓕 (PhiL N M) k‖ ^ 2 * ‖𝓕 (PhiL N M) k‖ ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hpar := LeanLab.Routes.R0001.dft_parseval_norm (PhiL N M)
  rw [sum_PhiL_sq hNM] at hpar
  calc (M : ℝ) * ∑ k ∈ minorSet P Q M, ‖𝓕 (PhiL N M) k‖ ^ 4
      ≤ (M : ℝ) * ∑ k ∈ minorSet P Q M, B ^ 2 * ‖𝓕 (PhiL N M) k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum hk) (Nat.cast_nonneg M)
    _ ≤ (M : ℝ) * ∑ k, B ^ 2 * ‖𝓕 (PhiL N M) k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ => by positivity
    _ = (M : ℝ) * (B ^ 2 * ((M : ℝ) * ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)) := by
        rw [← mul_sum, hpar]
    _ = _ := by ring

/-- Vacuity: `MinorAt 1 Q α` holds at `α = 1/2` for `Q ≥ 2`, so the minor set is not empty
in general; `q = 1` is the only `q ≤ P = 1`, and `|1/2 - a| ≥ 1/2 > 1/(Q + 1)`. -/
example (Q : ℕ) (hQ : 2 ≤ Q) : MinorAt 1 Q (1 / 2) := by
  intro a q hq1 hqP
  have hq : q = 1 := by omega
  subst hq
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h1 : (1 : ℝ) / 2 ≤ |1 / 2 - (a : ℝ) / ((1 : ℕ) : ℝ)| := by
    simp only [Nat.cast_one, div_one]
    rcases le_or_gt a 0 with h | h
    · have : (a : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
    · have : (1 : ℝ) ≤ a := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
  have h2 : (1 : ℝ) / (((1 : ℕ) : ℝ) * (Q + 1)) < 1 / 2 := by
    simp only [Nat.cast_one, one_mul]
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

end LeanLab.PNTPort.Vinogradov

