module

public import LeanLab.LanguascoPintzZaccagnini2007.Links
public import LeanLab.LanguascoPintzZaccagnini2007.Lemma61
public import LeanLab.ChenExplicit.TwinCNumeric

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5790, paper P0045.

# F-0038 in Lean: the corrected constant `2c₀ C(1, N)` leaves `[1, 2]`

Languasco, Pintz, Zaccagnini, Bull. LMS 39, 2007, version of record `papers/P0045-journal.pdf`.
(23), p. 777: `C(k, N) = Σ'_{d ≥ 1} f(d) j(d, k, N)/ξ(d)^k`. The Theorem, p. 772, claims
`C(k, N) ∈ [1, 2]`. The display after (15), p. 777, drops the factor `2c₀ = 2 ∏_{p>2}(1 - 1/(p-1)²)`
of (2), so the asymptotic constant the proof gives is `2c₀ C(k, N)`, F-0038.

`C1` is the paper's `C(1, N)`, with `jcount d 0 N = j(d, 1, N)` from Links.lean. `C1_summable`
by comparison with the series (26), PROVED as `lemma61_proved`. `C1_ge`: for `N ≡ 2 mod 105`, the
terms `d = 1, 3, 5, 7` already give `C(1, N) ≥ 1 + 1/2 + 1/12 + 1/15 = 1.65`; with
`twinC_ge_065`, `true_constant_gt_two`: `2c₀ C(1, N) > 2.14 > 2`. These `N` have density `1/105`,
far more than the `X^{3/5}` exceptions the Theorem allows, so the corrected constant leaves the
printed range `[1, 2]` on a positive share of `N`; that the corrected constant is the true one rests
on the repaired chain `lpz_main_J_twoC0`, CONDITIONAL ON its cited inputs. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.LPZ2007
open Finset Real

attribute [local instance] Classical.propDecidable

/-- The term of (23) at `k = 1`. -/
noncomputable def C1term (N d : ℕ) : ℝ := if OddSqf d then fd d * (jcount d 0 N : ℝ) / xi d else 0

/-- The paper's `C(1, N)`, (23). -/
noncomputable def C1 (N : ℕ) : ℝ := ∑' d, C1term N d

theorem C1term_nonneg (N d : ℕ) : 0 ≤ C1term N d := by
  unfold C1term
  split_ifs with h
  · exact div_nonneg (mul_nonneg (fd_nonneg h) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact le_rfl

theorem C1term_le (N d : ℕ) : C1term N d ≤ seriesTerm d := by
  unfold C1term seriesTerm
  split_ifs with h
  · have hj : (jcount d 0 N : ℝ) ≤ 1 := by
      have := jcount_le h.2.1 0 N; simp at this; exact_mod_cast this
    have hxi : (0 : ℝ) ≤ xi d := Nat.cast_nonneg _
    have hf := fd_nonneg h
    rw [mul_div_assoc, div_eq_mul_one_div (fd d)]
    by_cases hx : (xi d : ℝ) = 0
    · rw [hx]; simp
    · have hx0 : 0 < (xi d : ℝ) := lt_of_le_of_ne hxi (Ne.symm hx)
      apply mul_le_mul_of_nonneg_left _ hf
      exact div_le_div_of_nonneg_right hj hx0.le
  · exact le_rfl

theorem C1_summable (N : ℕ) : Summable (C1term N) :=
  Summable.of_nonneg_of_le (C1term_nonneg N) (C1term_le N) lemma61_proved

/-- If `d ∣ N - 2`, the tuple `ν = (1)` counts, so `j(d, 1, N) ≥ 1`. -/
theorem jcount_pos {d N : ℕ} (hd : Odd d) (h : (d : ℤ) ∣ (N : ℤ) - 2) : 1 ≤ jcount d 0 N := by
  unfold jcount
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 1, ?_⟩
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun _ => ⟨le_rfl, (xi_spec hd).1⟩, ?_⟩
  simpa using h

/-- A term with `d ∣ N - 2`: `C1term N d ≥ f(d)/μ` whenever `2^μ ≡ 1 mod d`, `μ ≥ 1`. -/
theorem term_ge {d N μ : ℕ} (hd : OddSqf d) (h : (d : ℤ) ∣ (N : ℤ) - 2) (hμ1 : 1 ≤ μ)
    (hμ : 2 ^ μ ≡ 1 [MOD d]) : fd d / μ ≤ C1term N d := by
  unfold C1term
  rw [if_pos hd]
  have hj : (1 : ℝ) ≤ jcount d 0 N := by exact_mod_cast jcount_pos hd.2.1 h
  have hxi1 : (1 : ℝ) ≤ xi d := by exact_mod_cast (xi_spec hd.2.1).1
  have hxiμ : (xi d : ℝ) ≤ μ := by exact_mod_cast xi_le hμ1 hμ
  have hf := fd_nonneg hd
  calc fd d / μ ≤ fd d / xi d := div_le_div_of_nonneg_left hf (by linarith) hxiμ
    _ ≤ fd d * jcount d 0 N / xi d := by
        apply div_le_div_of_nonneg_right _ (by linarith); nlinarith

theorem oddSqf_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : OddSqf p :=
  ⟨hp.pos, hp.odd_of_ne_two h2, hp.squarefree⟩

theorem fd_prime {p : ℕ} (hp : p.Prime) (h2 : 2 < p) : fd p = 1 / ((p : ℝ) - 2) := by
  unfold fd
  rw [hp.primeFactors, Finset.filter_singleton, if_pos h2, Finset.prod_singleton]

/-- `C(1, N) ≥ 1.65` for `N ≡ 2 mod 105`. -/
theorem C1_ge (N : ℕ) (h : (105 : ℤ) ∣ (N : ℤ) - 2) : 1.65 ≤ C1 N := by
  have hdvd : ∀ d : ℕ, d ∣ 105 → (d : ℤ) ∣ (N : ℤ) - 2 := fun d hd =>
    (Int.natCast_dvd_natCast.mpr hd).trans h
  have t1 : 1 ≤ C1term N 1 := by
    have := term_ge (d := 1) (N := N) (μ := 1) ⟨one_pos, odd_one, squarefree_one⟩
      (by simp) le_rfl (by decide)
    simpa [fd] using this
  have t3 : 1 / 2 ≤ C1term N 3 := by
    have := term_ge (d := 3) (N := N) (μ := 2) (oddSqf_prime Nat.prime_three (by norm_num))
      (hdvd 3 (by norm_num)) (by norm_num) (by decide)
    rw [fd_prime Nat.prime_three (by norm_num)] at this; norm_num at this ⊢; linarith
  have t5 : 1 / 12 ≤ C1term N 5 := by
    have := term_ge (d := 5) (N := N) (μ := 4) (oddSqf_prime Nat.prime_five (by norm_num))
      (hdvd 5 (by norm_num)) (by norm_num) (by decide)
    rw [fd_prime Nat.prime_five (by norm_num)] at this; norm_num at this ⊢; linarith
  have t7 : 1 / 15 ≤ C1term N 7 := by
    have h7 : Nat.Prime 7 := by norm_num
    have := term_ge (d := 7) (N := N) (μ := 3) (oddSqf_prime h7 (by norm_num))
      (hdvd 7 (by norm_num)) (by norm_num) (by decide)
    rw [fd_prime h7 (by norm_num)] at this; norm_num at this ⊢; linarith
  have hsum : C1term N 1 + C1term N 3 + C1term N 5 + C1term N 7 ≤ C1 N := by
    have := (C1_summable N).sum_le_tsum ({1, 3, 5, 7} : Finset ℕ)
      (fun d _ => C1term_nonneg N d)
    rw [C1]
    simpa [Finset.sum_insert, add_assoc] using this
  linarith

/-- **F-0038 in Lean**: for every `N ≡ 2 mod 105`, `2c₀ C(1, N) > 2`, with `2c₀ = 2 twinC`. -/
theorem true_constant_gt_two (N : ℕ) (h : (105 : ℤ) ∣ (N : ℤ) - 2) :
    2 < 2 * LeanLab.ChenExplicit.twinC * C1 N := by
  have hT := LeanLab.ChenExplicit.twinC_ge_065
  have hC := C1_ge N h
  nlinarith

/-- Vacuity: `N = 212 = 2 · 106` is even and `≡ 2 mod 105`. -/
example : (105 : ℤ) ∣ ((212 : ℕ) : ℤ) - 2 ∧ Even 212 := by decide

end LeanLab.LPZ2007
