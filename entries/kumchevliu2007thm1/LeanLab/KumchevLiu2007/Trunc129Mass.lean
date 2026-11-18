module

public import LeanLab.KumchevLiu2007.Decomp506b

/-!
Truncated window version of the page 16 display 57 mass bound and of the page 17
display 58 sieve assembly, for the transition regime of the residual extension.
The semiprime sequence is cut at a real point a between half the square root of Y
and the square root of Y, and the main term carries the truncated window length
sqrt Y minus a in place of sqrt Y. The distribution estimate, the Rosser upper
bound and the support bridge enter the combined theorem as hypotheses.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Trunc129

open Real MeasureTheory LeanLab.KumchevLiu2007 Task506b
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 16 display 57, truncated window version. A logarithmic integral over an
interval that starts at or above c and has clamped length at most len is at most
len over log c. -/
theorem trunc_integral_inv_log_le (lo hi c len : ℝ) (hc : 1 < c) (hclo : c ≤ lo)
    (hlen : hi ≤ lo + len) (hlen0 : 0 ≤ len) :
    (∫ u in lo..max lo hi, 1 / Real.log u) ≤ (1 / Real.log c) * len := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hlc : 0 < Real.log c := Real.log_pos hc
  have hab : lo ≤ max lo hi := le_max_left _ _
  have hlen' : |max lo hi - lo| ≤ len := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab), sub_le_iff_le_add]
    exact max_le (by linarith) (by linarith)
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := lo) (b := max lo hi) (C := 1 / Real.log c) (f := fun u => 1 / Real.log u) ?_
  · exact (le_norm_self _).trans (hn.trans (mul_le_mul_of_nonneg_left hlen' (by positivity)))
  intro u hu
  rw [Set.uIoc_of_le hab] at hu
  have hcu : c ≤ u := hclo.trans hu.1.le
  have hlu : Real.log c ≤ Real.log u := Real.log_le_log hc0 hcu
  have hlu0 : 0 < Real.log u := hlc.trans_le hlu
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.log u)]
  exact one_div_le_one_div_of_le hlc hlu

/-- Page 16 display 57, truncated window version. For a cut a at most the square
root of Y, the logarithmic integral over the truncated interval J of p is at most
the truncated length, sqrt Y minus a over p, divided by log p. -/
theorem trunc_j_integral_bound (X ε a : ℝ) (p : ℕ) (hp : p.Prime)
    (ha : a ≤ Real.sqrt (Y X ε)) :
    (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
        1 / Real.log u) ≤
      (1 / Real.log p) * ((Real.sqrt (Y X ε) - a) / p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hroot : 0 ≤ (Real.sqrt (Y X ε) - a) / p := div_nonneg (sub_nonneg.mpr ha) hp0.le
  have hpj : (p : ℝ) ≤ jlo X ε p := le_max_left _ _
  have hjl : jlo X ε p ≤ max (jlo X ε p) (a / p) := le_max_left _ _
  have hap : a / p ≤ max (jlo X ε p) (a / p) := le_max_right _ _
  have hsplit : Real.sqrt (Y X ε) / p = a / p + (Real.sqrt (Y X ε) - a) / p := by ring
  have hhi : jhi X ε p ≤ max (jlo X ε p) (a / p) + (Real.sqrt (Y X ε) - a) / p := by
    unfold jhi
    exact max_le (by linarith) (by linarith)
  exact trunc_integral_inv_log_le _ _ (p : ℝ) _ hp1 (hpj.trans hjl) hhi hroot

/-- Page 16 display 57, truncated window version. Once log p is large on the prime
window, the truncated mass reduces to the truncated length times a reciprocal
prime sum. -/
theorem trunc_mass_bound_of_logs (X B ε L a : ℝ) (hL : 0 < L)
    (ha : a ≤ Real.sqrt (Y X ε))
    (hlogs : ∀ p ∈ primeWindow X B ε, L / 32 ≤ Real.log p) :
    (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u) ≤
      (32 * (Real.sqrt (Y X ε) - a) / L) * ∑ p ∈ primeWindow X B ε, (1 : ℝ) / p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlp : 0 < Real.log p := lt_of_lt_of_le (by positivity) (hlogs p hp)
  have hinv : 1 / Real.log p ≤ 32 / L := by
    rw [div_le_div_iff₀ hlp hL]
    linarith [hlogs p hp]
  have hroot : 0 ≤ (Real.sqrt (Y X ε) - a) / p := div_nonneg (sub_nonneg.mpr ha) hp0.le
  calc _ ≤ (1 / Real.log p) * ((Real.sqrt (Y X ε) - a) / p) :=
         trunc_j_integral_bound X ε a p hpp ha
       _ ≤ (32 / L) * ((Real.sqrt (Y X ε) - a) / p) :=
         mul_le_mul_of_nonneg_right hinv hroot
       _ = (32 * (Real.sqrt (Y X ε) - a) / L) * (1 / p) := by ring

/-- Page 16 display 57, truncated window version. The truncated mass N, with the
semiprime window cut at a, is at most a constant times the truncated window length
sqrt Y minus a, times log X to the minus two, times log log X. -/
theorem trunc_mass_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ a : ℝ,
      Real.sqrt (Y X ε) / 2 ≤ a → a ≤ Real.sqrt (Y X ε) →
      (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u) ≤
        C * ((Real.sqrt (Y X ε) - a) * Real.log X ^ (-2 : ℝ) * Real.log (Real.log X)) := by
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp (prime_reciprocal_bound B ε hB hε)
  refine ⟨1024 * (2 * B + 18), X0, by positivity, ?_⟩
  intro X hX a _ ha2
  obtain ⟨hL, hlogs, hsum⟩ := hX0 X hX
  have hpre : 0 ≤ 32 * (Real.sqrt (Y X ε) - a) / Real.log X :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ha2)) hL.le
  have hbound := (trunc_mass_bound_of_logs X B ε (Real.log X) a hL ha2 hlogs).trans
    (mul_le_mul_of_nonneg_left hsum hpre)
  have h2 : Real.log X ^ (-2 : ℝ) = (Real.log X ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hL.le, Real.rpow_two]
  refine hbound.trans (le_of_eq ?_)
  rw [h2]
  have hL0 : Real.log X ≠ 0 := hL.ne'
  field_simp
  ring

/-- Page 17 display 58 with N bounded by display 57, truncated window version.
The sifted count of an integer n strictly between X and X plus Y is bounded by the
truncated main term, with window length sqrt Y minus the cut max of sqrt Y over two
and sqrt of n minus X, plus the logarithmic error scale.
CONDITIONAL on the truncated Bombieri Vinogradov remainder bound hbv, pages 16 and
17 displays 56 to 59, the truncated Rosser upper bound hros, page 13 Lemma 3.7, and
the truncated support bridge hle. -/
theorem trunc_sifted_sieve_bound_of
    (hbv : ∀ (A B ε : ℝ), 0 < A → 0 < B → 0 < ε → ε ≤ 11 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → ∀ a : ℝ,
        Real.sqrt (Y X ε) / 2 ≤ a → a ≤ Real.sqrt (Y X ε) →
        (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter (fun q => d ∣ n - q ^ 2)).card : ℝ) -
            density n d * (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u)|) ≤
          C * errorScale X ε A)
    (hros : ∀ (B δ ε : ℝ), 0 < B → 0 < δ → δ < 1 → 0 < ε → ε ≤ 11 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → ∀ a : ℝ,
        Real.sqrt (Y X ε) / 2 ≤ a → a ≤ Real.sqrt (Y X ε) →
        ((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
            (fun q => (Task506e.primeProduct X δ n).Coprime (n - q ^ 2))).card : ℝ) ≤
          C * ((∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u) *
                sieveProduct X δ n +
              (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
                |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter (fun q => d ∣ n - q ^ 2)).card : ℝ) -
                  density n d * (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u)|)))
    (hle : ∀ (B δ ε : ℝ), 0 < B → 0 < ε →
      ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → (n : ℝ) < X + Y X ε →
        siftedCount X B δ ε n ≤
          ((((semiprimes X B ε).filter (fun q : ℕ => max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) ≤ (q : ℝ))).filter
            (fun q => (Task506e.primeProduct X δ n).Coprime (n - q ^ 2))).card : ℝ))
    (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → (n : ℝ) < X + Y X ε →
      siftedCount X B δ ε n ≤ K *
        ((Real.sqrt (Y X ε) - max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X))) * Real.log X ^ (-2 : ℝ) *
            Real.log (Real.log X) * sieveProduct X δ n + errorScale X ε A) := by
  obtain ⟨Cs, Xs, hCs, hs⟩ := hros B δ ε hB hδ hδ1 hε hε1
  obtain ⟨Cr, Xr, hCr, hr⟩ := hbv A B ε hA hB hε hε1
  obtain ⟨Xl, hl⟩ := hle B δ ε hB hε
  obtain ⟨Cm, Xm, hCm, hm⟩ := trunc_mass_bound B ε hB hε
  refine ⟨Cs * (Cm + Cr), max (max Xs Xr) (max (max Xm Xl) (Real.exp (Real.exp 1))),
    by positivity, ?_⟩
  intro X hX n hn hXn hnlt
  have hXs : Xs ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXr : Xr ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXm : Xm ≤ X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have hXl : Xl ≤ X :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
  have hXe : Real.exp (Real.exp 1) ≤ X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos _).trans_le hXe
  have hLe : Real.exp 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos _) hXe
    simpa only [Real.log_exp] using hh
  have hll : 0 ≤ Real.log (Real.log X) :=
    Real.log_nonneg ((by linarith [Real.add_one_le_exp (1 : ℝ)] : 1 ≤ Real.exp 1).trans hLe)
  have hL : 0 < Real.log X := (Real.exp_pos 1).trans_le hLe
  have hE : 0 ≤ errorScale X ε A := by unfold errorScale Y; positivity
  have hV := sieveProduct_nonneg X δ n
  have ha1 : Real.sqrt (Y X ε) / 2 ≤
      max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) := le_max_left _ _
  have ha2 : max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) ≤ Real.sqrt (Y X ε) :=
    max_le (by linarith [Real.sqrt_nonneg (Y X ε)]) (Real.sqrt_le_sqrt (by linarith))
  have hW : 0 ≤ Real.sqrt (Y X ε) -
      max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) := sub_nonneg.mpr ha2
  have hLr : 0 ≤ Real.log X ^ (-2 : ℝ) := Real.rpow_nonneg hL.le _
  have hM : 0 ≤ (Real.sqrt (Y X ε) -
      max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X))) * Real.log X ^ (-2 : ℝ) *
        Real.log (Real.log X) := mul_nonneg (mul_nonneg hW hLr) hll
  have hl' := hl X hXl n hn hXn hnlt
  have hs' := hs X hXs n hn hXn _ ha1 ha2
  have hr' := hr X hXr n hn hXn _ ha1 ha2
  have hm' := mul_le_mul_of_nonneg_right (hm X hXm _ ha1 ha2) hV
  refine hl'.trans (hs'.trans ?_)
  refine (mul_le_mul_of_nonneg_left (add_le_add hm' hr') hCs.le).trans ?_
  have hME := mul_nonneg hM hV
  have h1 := mul_nonneg hCs.le (mul_nonneg hCr.le hME)
  have h2 := mul_nonneg hCs.le (mul_nonneg hCm.le hE)
  nlinarith [h1, h2]

end LeanLab.KumchevLiu2007.Trunc129

