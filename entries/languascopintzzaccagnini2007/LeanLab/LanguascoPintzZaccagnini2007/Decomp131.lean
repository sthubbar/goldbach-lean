module

public import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218
public import LeanLab.LanguascoPintzZaccagnini2007.Decomp383a

@[expose] public section

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory

noncomputable section

/-- LEAF. Display 3 on page 3. The tuples removed by replacing L with L-sqrt L
have weighted count o(N L^k), uniformly on J(X).
Source: the standard sieve upper bound R(n) << n S(n) invoked after display 3.
The exact Fourier inversion and the arc split are proved in Convolution131. -/
theorem truncation_tail131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |Rpp k X N - truncatedCount131 k X N| ≤ ε * N * Lg X ^ k := by
  exact truncation_tail_proved131 k hk ε hε

/-- LEAF. Displays 3 to 6 on pages 3 and 4. Truncating the powers of two
and Fourier inversion leave an error o(N L^k), uniformly on J(X).
The bound for the prime pair sum used after display 3 is an outside sieve input.
Source: the standard upper bound R(n) << n S(n) invoked on page 3. -/
theorem truncation131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ N ∈ evenJ131 X,
        |Rpp k X N - majorContribution131 k X N P - minorContribution131 k X N P| ≤
          ε * N * Lg X ^ k := by
  obtain ⟨X₁, hX₁⟩ := truncation_tail131 k hk ε hε
  obtain ⟨X₂, hX₂⟩ := admissible_gap_eventually131
  refine ⟨max X₁ X₂, fun X hX P hP N hN => ?_⟩
  obtain ⟨hX2, hpar⟩ := hX₂ X (by omega)
  obtain ⟨hP1, _, hQ⟩ := hpar P hP
  have he := arc_split131 k X N P (by omega) (by linarith) hQ
  rw [show Rpp k X N - majorContribution131 k X N P - minorContribution131 k X N P =
      Rpp k X N - (majorContribution131 k X N P + minorContribution131 k X N P) by ring,
    he]
  exact hX₁ X (by omega) N hN

/-- LEAF. Page 4 before display 7. The Bessel and prime number theorem argument
with Lemma 6.3 gives the minor arc mean square bound.
Source outside P0045: Vaughan Theorem 3.1 cited as Lemma 6.3 on page 10,
and the prime number theorem invoked on page 4. -/
theorem minor_mean_square131 (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ P : ℝ, AdmissibleP131 X P →
        ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
          K * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k + 9) := by
  exact minor_mean_square_proved131 k

/-- LEAF. Page 9 conclusion: three error contributions combine by the triangle inequality.
This elementary statement is independent of the cited analytic inputs. -/
theorem combine_errors131 {R A B C t : ℝ}
    (h₁ : |R - A - B| ≤ t / 3) (h₂ : |A - C| ≤ t / 3) (h₃ : |B| ≤ t / 3) :
    |R - C| ≤ t := by
  have h := abs_add_three (R - A - B) (A - C) B
  have he : R - A - B + (A - C) + B = R - C := by ring
  rw [he] at h
  linarith

/-- LEAF. Display 7 on page 4. The already proved mean square counting lemma
bounds the exceptional set with an explicit factor 9/4. -/
theorem minor_count131 {k X : ℕ} {P K : ℝ} (hX : 0 < X) (hL : 0 < Lg X)
    (hsum : ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
      K * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k + 9)) :
    (((evenJ131 X).filter (fun N : ℕ =>
      (N : ℝ) * Lg X ^ ((k : ℝ) - 1 / 2) ≤ |minorContribution131 k X N P|)).card : ℝ) ≤
        9 / 4 * K / Real.log 2 ^ 10 * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  classical
  have hc := count_le_of_sq_sum (S := (evenJ131 X).filter (fun N : ℕ =>
      (N : ℝ) * Lg X ^ ((k : ℝ) - 1 / 2) ≤ |minorContribution131 k X N P|))
    (a := fun N => minorContribution131 k X N P) (K := K) (k := k) (X := (X : ℝ))
    (by exact_mod_cast hX) hL
  have he : 9 / 4 * K * (X : ℝ) ^ ((3 : ℝ) / 5) * Lg X ^ 10 =
      9 / 4 * K / Real.log 2 ^ 10 * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
    simp only [Lg, Real.logb, div_pow]
    ring
  rw [← he]
  apply hc
  · intro N hN
    exact (mem_filter.mp (mem_filter.mp hN).1).2.2
  · intro N hN
    exact (mem_filter.mp hN).2
  · refine le_trans ?_ hsum
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- LEAF. Page 9: the minor arc cutoff N L^(k-1/2) is eventually at most
any fixed positive multiple of N L^k. -/
theorem cutoff_small131 (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      Lg X ^ ((k : ℝ) - 1 / 2) ≤ ε * Lg X ^ k := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀, hX₀⟩ := (ht.eventually_ge_atTop (max 1 ((1 / ε) ^ 2))).exists_forall_of_atTop
  refine ⟨X₀, fun X hX => ?_⟩
  have hL := hX₀ X hX
  have hL1 : 1 ≤ Lg X := (le_max_left _ _).trans hL
  have hL0 : 0 < Lg X := by linarith
  have hs : 1 / ε ≤ Real.sqrt (Lg X) := by
    calc 1 / ε = Real.sqrt ((1 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Lg X) := Real.sqrt_le_sqrt ((le_max_right _ _).trans hL)
  rw [Real.rpow_sub hL0, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hL0)).2
  have he : 1 ≤ ε * Real.sqrt (Lg X) := by
    have := (div_le_iff₀ hε).1 hs
    linarith
  nlinarith [mul_le_mul_of_nonneg_left he (pow_nonneg hL0.le k)]

/-- U-1619, the narrow window J'(X) of U-1617 section 4: N in J(X) with every shift N - M still in
J(X). Display 12 then needs Corollary 4.2 only on the printed J(X). -/
def evenJNarrow1619 (k X : ℕ) : Finset ℕ :=
  (evenJ131 X).filter (fun N : ℕ =>
    2 * X + 3 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) ≤ 3 * N)

/-- On the narrow window every shifted argument stays in the printed J(X). -/
theorem narrow_shift_mem1619 {k X N : ℕ} (hN : N ∈ evenJNarrow1619 k X) {ν : Fin k → ℕ}
    (hν : ν ∈ tuples131 k X) : N - tuplePower131 ν ∈ evenJ131 X := by
  obtain ⟨hJ, hw⟩ := mem_filter.mp hN
  obtain ⟨h1, h2, h3, h4⟩ := evenJ_nat131 hJ
  have hle := tuplePower_le131 hν
  have hev := tuplePower_even131 hν
  have hmul : 3 * tuplePower131 ν ≤ 3 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) :=
    Nat.mul_le_mul_left 3 hle
  have hMN : tuplePower131 ν ≤ N := by omega
  have hX0 : 1 ≤ X := by omega
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (Nat.even_sub hMN).mpr ?_, ?_⟩
  · exact iff_of_true h3 hev
  · have hb : 2 * X ≤ 3 * (N - tuplePower131 ν) := by omega
    have hb' : 2 * (X : ℝ) ≤ 3 * ((N - tuplePower131 ν : ℕ) : ℝ) := by exact_mod_cast hb
    linarith

/-- Display 25 on the narrow window, from the printed Corollary 4.2 on J(X) alone. -/
theorem major_asymptotic_narrow1619 (hj1 : Cor42OnWindow131 evenJ131)
    (hcomb : SingularAverageStatement131) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJNarrow1619 k X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k := by
  classical
  set B : ℝ := 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d with hB
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (coefficient_le131 hk 0)
    exact mul_nonneg (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
      (by linarith [Ck_ge_one131 hk 0])
  have hB1 : 0 < B + 1 := by linarith
  set η : ℝ := ε / (3 * (B + 1)) with hηdef
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hB1)
  obtain ⟨K₁, Cstar, c, A, hC, hc, hA, X₁, hX₁⟩ := hj1 η hη
  have hA1 : 0 < A + 1 := by linarith
  have hε₂ : 0 < ε / (3 * (A + 1)) := div_pos hε (mul_pos (by norm_num) hA1)
  obtain ⟨X₂, hX₂⟩ := major_arcs_j2_131 k hk K₁ Cstar hC c hc _ hε₂
  obtain ⟨X₃, hX₃⟩ := hcomb k hk (ε / 3) (by positivity)
  obtain ⟨X₄, hX₄⟩ := hcomb k hk 1 one_pos
  obtain ⟨X₅, hX₅⟩ := tuple_window131 k
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ X₅))), fun X hX => ?_⟩
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  have hx5 : X₅ ≤ X := by omega
  obtain ⟨P, E, hP, hE, hgood, hup⟩ := hX₁ X hx1
  refine ⟨P, hP, fun N hN' => ?_⟩
  have hN : N ∈ evenJ131 X := (mem_filter.mp hN').1
  obtain ⟨hL, hw⟩ := hX₅ X hx5
  have hL0 : 0 ≤ Lg X := by linarith
  have hLk : 0 ≤ Lg X ^ k := by positivity
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsm : ∀ ν ∈ tuples131 k X, 6 * tuplePower131 ν ≤ X := by
    intro ν hν
    have := tuplePower_le131 hν
    have h6 : 6 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) =
        6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
    omega
  have hle : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N := by
    intro ν hν
    have := hsm ν hν
    omega
  have hwin : ∀ ν ∈ tuples131 k X, N - tuplePower131 ν ∈ evenJ131 X := fun ν hν =>
    narrow_shift_mem1619 hN' hν
  set Bad := (tuples131 k X).filter
    (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) with hBad
  have hsplit : |∑ ν ∈ tuples131 k X, binaryMajor131 X (N - tuplePower131 ν) P -
      ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
      η * ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) +
        (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) := by
    refine split_bound131 (tuples131 k X)
      (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν))
      (fun ν => binaryMajor131 X (N - tuplePower131 ν) P)
      (fun ν => ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν))
      (fun ν => Sing (N - tuplePower131 ν)) η ((A + 1) * N) hη.le
      (mul_nonneg hA1.le hNr)
      (fun ν _ => mul_nonneg (Nat.cast_nonneg _) (Sing_nonneg131 _))
      (fun ν _ => Sing_nonneg131 _) ?_ ?_
    · intro ν hν hb
      have h := hgood _ (hwin ν hν) (not_not.mp hb)
      have e : η * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) =
          η * (((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)) := by ring
      rw [e] at h
      exact h
    · intro ν hν _
      show |binaryMajor131 X (N - tuplePower131 ν) P -
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
        (A + 1) * N * Sing (N - tuplePower131 ν)
      have hu := abs_le.mp (hup _ (hwin ν hν))
      have hS := Sing_nonneg131 (N - tuplePower131 ν)
      have hn : ((N - tuplePower131 ν : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le _ _
      have hn0 : (0 : ℝ) ≤ ((N - tuplePower131 ν : ℕ) : ℝ) := Nat.cast_nonneg _
      have h0 := mul_nonneg hn0 hS
      have h1 : A * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          A * N * Sing (N - tuplePower131 ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA) hS
      have h2 : ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          N * Sing (N - tuplePower131 ν) := mul_le_mul_of_nonneg_right hn hS
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
  have hjj := hX₂ X hx2 E hE N hN Bad (filter_subset _ _) (fun ν hν => (mem_filter.mp hν).2)
  have hc3 := hX₃ X hx3 N hN
  have hc1 := hX₄ X hx4 N hN
  rw [← major_expand131 k X N P hle] at hsplit
  set W := ∑ ν ∈ tuples131 k X,
    ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) with hW
  set M := majorContribution131 k X N P with hM
  have hNL : 0 ≤ (N : ℝ) * Lg X ^ k := mul_nonneg hNr hLk
  have hcoef : coefficient131 k N * N * Lg X ^ k ≤ B * ((N : ℝ) * Lg X ^ k) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (coefficient_le131 hk N) hNL
  have hWup : W ≤ (B + 1) * ((N : ℝ) * Lg X ^ k) := by
    have := (abs_le.mp hc1).2
    nlinarith
  have hterm1 : η * W ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hWup hη.le
    have he : η * ((B + 1) * ((N : ℝ) * Lg X ^ k)) = ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      rw [hηdef]
      field_simp
    rw [he] at h
    exact h
  have hterm2 : (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) ≤
      ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hjj (mul_nonneg hA1.le hNr)
    have he : (A + 1) * N * (ε / (3 * (A + 1)) * Lg X ^ k) =
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      field_simp
    rw [he] at h
    exact h
  have hfin := abs_sub_le M W (coefficient131 k N * N * Lg X ^ k)
  have hc3' : |W - coefficient131 k N * N * Lg X ^ k| ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    calc _ ≤ _ := hc3
      _ = _ := by ring
  calc _ ≤ _ := hfin
    _ ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) + ε / 3 * ((N : ℝ) * Lg X ^ k) +
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by linarith
    _ = ε * N * Lg X ^ k := by ring

/-- The exceptional count on the narrow window, the proof of `repaired_mainJ131` restricted. -/
theorem narrow_count1619 (hmaj : ∀ (k : ℕ), 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
        ∀ N ∈ evenJNarrow1619 k X,
          |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k)
    (k : ℕ) (hk : 1 ≤ k) : ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((evenJNarrow1619 k X).filter (fun N : ℕ =>
        η * N * Lg X ^ k < |Rpp k X N - coefficient131 k N * N * Lg X ^ k|)).card : ℝ) ≤
      K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  classical
  obtain ⟨K, hK, X₁, hX₁⟩ := minor_mean_square131 k hk
  refine ⟨9 / 4 * K / Real.log 2 ^ 10, by positivity, fun η hη => ?_⟩
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨X₂, hX₂⟩ := truncation131 k hk (η / 3) hη3
  obtain ⟨X₃, hX₃⟩ := hmaj k hk (η / 3) hη3
  obtain ⟨X₄, hX₄⟩ := cutoff_small131 k (η / 3) hη3
  refine ⟨max 2 (max X₁ (max X₂ (max X₃ X₄))), fun X hX => ?_⟩
  have h2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hx1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  have hL : 0 < Lg X := Real.logb_pos (by norm_num) (by exact_mod_cast h2)
  obtain ⟨P, hP, hmajor⟩ := hX₃ X hx3
  have hcount := minor_count131 (by omega : 0 < X) hL (hX₁ X hx1 P hP)
  refine le_trans ?_ (by simpa [mul_assoc] using hcount)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro N hN
  obtain ⟨hN', hbad⟩ := mem_filter.mp hN
  have hN : N ∈ evenJ131 X := (mem_filter.mp hN').1
  refine mem_filter.mpr ⟨hN, ?_⟩
  by_contra hminor
  have hminor' : |minorContribution131 k X N P| ≤
      η * N * Lg X ^ k / 3 := by
    have hcut := mul_le_mul_of_nonneg_left (hX₄ X hx4) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hm : |minorContribution131 k X N P| < (N : ℝ) * Lg X ^ ((k : ℝ) - 1 / 2) := by
      simpa only [one_div] using (not_le.mp hminor)
    have := hm.le.trans hcut
    nlinarith
  have htrunc : |Rpp k X N - majorContribution131 k X N P - minorContribution131 k X N P| ≤
      η * N * Lg X ^ k / 3 := by
    have := hX₂ X hx2 P hP N hN
    nlinarith
  have hmajor' : |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
      η * N * Lg X ^ k / 3 := by
    have := hmajor N hN'
    nlinarith
  exact (not_lt_of_ge (combine_errors131 htrunc hmajor' hminor')) hbad

/-- The pair sum does not see X once N is at most Y and Y at most X. -/
theorem tuplePair_congr1619 {k Y X N : ℕ} (hNY : N ≤ Y) (hYX : Y ≤ X) (ν : Fin k → ℕ) :
    tuplePair131 Y N ν = tuplePair131 X N ν := by
  unfold tuplePair131
  have hsub : Icc 1 Y ⊆ Icc 1 X := Icc_subset_Icc le_rfl hYX
  rw [← sum_subset hsub (fun m₁ hm₁ hn => ?_)]
  · refine sum_congr rfl fun m₁ hm₁ => ?_
    refine sum_subset hsub (fun m₂ hm₂ hn => ?_)
    have h1 := (mem_Icc.mp hm₂).1
    have h2 : Y < m₂ := by
      by_contra hc
      exact hn (mem_Icc.mpr ⟨h1, by omega⟩)
    exact ite_eq_right (by omega)
  · have h1 := (mem_Icc.mp hm₁).1
    have h2 : Y < m₁ := by
      by_contra hc
      exact hn (mem_Icc.mpr ⟨h1, by omega⟩)
    exact sum_eq_zero fun m₂ _ => ite_eq_right (by omega)

/-- Exponent tuples are monotone in the range. -/
theorem exponentTuples_mono1619 (k : ℕ) {m M : ℕ} (h : m ≤ M) :
    exponentTuples131 k m ⊆ exponentTuples131 k M := by
  intro ν hν
  simp only [exponentTuples131, Fintype.mem_piFinset, mem_Icc] at hν ⊢
  exact fun i => ⟨(hν i).1, (hν i).2.trans h⟩

/-- Lg grows by at most 1 on doubling. -/
theorem Lg_le_succ1619 {Y X : ℕ} (hY : 1 ≤ Y) (hXY : X ≤ 2 * Y) : Lg X ≤ Lg Y + 1 := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have he : Lg Y + 1 = Real.logb 2 (2 * (Y : ℝ)) := by
    unfold Lg
    rw [Real.logb_mul (by norm_num) hY0.ne', Real.logb_self_eq_one (by norm_num)]
    ring
  rw [he]
  unfold Lg
  by_cases hX : X = 0
  · subst hX
    simp only [Nat.cast_zero, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) (by
      have : (1 : ℝ) ≤ Y := by exact_mod_cast hY
      linarith)
  · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hX)
      (by exact_mod_cast hXY)

/-- The floors of Lg differ by at most 1. -/
theorem Lp_le_succ1619 {Y X : ℕ} (hY : 1 ≤ Y) (hXY : X ≤ 2 * Y) : Lp X ≤ Lp Y + 1 := by
  have hL : 0 ≤ Lg Y := Real.logb_nonneg (by norm_num) (by exact_mod_cast hY)
  have h := Lg_le_succ1619 hY hXY
  unfold Lp
  calc ⌊Lg X⌋₊ ≤ ⌊Lg Y + 1⌋₊ := Nat.floor_mono h
    _ = ⌊Lg Y⌋₊ + 1 := Nat.floor_add_one hL

/-- Lg is monotone on positive naturals. -/
theorem Lg_mono1619 {Y X : ℕ} (hY : 1 ≤ Y) (hYX : Y ≤ X) : Lg Y ≤ Lg X :=
  Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hY) (by exact_mod_cast hYX)

/-- The transfer of U-1617 section 4: passing from X to a nearby Y moves `Rpp` by at most the
tuples with a top exponent, each bounded by the proved `tuplePair_bound131`. No new leaf. -/
theorem Rpp_transfer1619 {k Y X N : ℕ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYX : Y ≤ X) (hXY : X ≤ 2 * Y)
    (hNY : N ≤ Y) (hN : 3 ≤ N) :
    |Rpp k X N - Rpp k Y N| ≤
      k * Lg X ^ (k - 1) * (pairConstant131 * N * (Real.log (Real.log N) + 2)) := by
  have hmono : Lp Y ≤ Lp X := Nat.floor_mono (Lg_mono1619 hY hYX)
  have hsub := exponentTuples_mono1619 k hmono
  have hid : Rpp k X N - Rpp k Y N =
      ∑ ν ∈ exponentTuples131 k (Lp X) \ exponentTuples131 k (Lp Y), tuplePair131 X N ν := by
    rw [Rpp_tuple_sum131 k X N, Rpp_tuple_sum131 k Y N, ← sum_sdiff hsub]
    have : ∑ ν ∈ exponentTuples131 k (Lp Y), tuplePair131 Y N ν =
        ∑ ν ∈ exponentTuples131 k (Lp Y), tuplePair131 X N ν :=
      sum_congr rfl fun ν _ => tuplePair_congr1619 hNY hYX ν
    rw [this]
    ring
  rw [hid]
  have h0 : 0 ≤ ∑ ν ∈ exponentTuples131 k (Lp X) \ exponentTuples131 k (Lp Y),
      tuplePair131 X N ν := sum_nonneg fun ν _ => (tuplePair_bound131 hN ν).1
  rw [abs_of_nonneg h0]
  have hs := sum_le_card_nsmul
    (exponentTuples131 k (Lp X) \ exponentTuples131 k (Lp Y))
    (tuplePair131 X N) (pairConstant131 * N * (Real.log (Real.log N) + 2))
    (fun ν _ => (tuplePair_bound131 hN ν).2)
  rw [nsmul_eq_mul] at hs
  have hC : 0 ≤ pairConstant131 := by
    unfold pairConstant131
    norm_num [LeanLab.SchnirelmannExplicit.C1]
    positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog1 : 1 ≤ Real.log N :=
    (Real.le_log_iff_exp_le hN0).mpr (Real.exp_one_lt_three.le.trans (by exact_mod_cast hN))
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlog1
  refine hs.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hLX0 : 0 ≤ Lg X := Real.logb_nonneg (by norm_num) (by exact_mod_cast hY.trans hYX)
  have hML : (Lp X : ℝ) ≤ Lg X := Nat.floor_le hLX0
  have hmM : (Lp Y : ℝ) ≤ Lp X := by exact_mod_cast hmono
  have hdiff : (Lp X : ℝ) - Lp Y ≤ 1 := by
    have : (Lp X : ℝ) ≤ Lp Y + 1 := by exact_mod_cast Lp_le_succ1619 hY hXY
    linarith
  have hp := abs_pow_sub_pow_le (a := (Lp X : ℝ)) (b := (Lp Y : ℝ)) (n := j + 1)
  have hpow : (Lp Y : ℝ) ^ (j + 1) ≤ (Lp X : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hmM _
  simp only [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg (sub_nonneg.mpr hmM),
    abs_of_nonneg (Nat.cast_nonneg (Lp X) : (0 : ℝ) ≤ Lp X),
    abs_of_nonneg (Nat.cast_nonneg (Lp Y) : (0 : ℝ) ≤ Lp Y),
    max_eq_left hmM, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hp
  rw [card_sdiff_of_subset hsub, exponentTuples_card131, exponentTuples_card131,
    Nat.cast_sub (Nat.pow_le_pow_left hmono _)]
  push_cast
  calc (Lp X : ℝ) ^ (j + 1) - (Lp Y : ℝ) ^ (j + 1)
      ≤ ((Lp X : ℝ) - Lp Y) * (j + 1) * (Lp X : ℝ) ^ j := hp
    _ ≤ 1 * (j + 1) * Lg X ^ j := by
        have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
        have hpw : (Lp X : ℝ) ^ j ≤ Lg X ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hML _
        have hnn : (0 : ℝ) ≤ (Lp X : ℝ) ^ j := by positivity
        calc ((Lp X : ℝ) - Lp Y) * (j + 1) * (Lp X : ℝ) ^ j
            ≤ 1 * (j + 1) * (Lp X : ℝ) ^ j := by gcongr
          _ ≤ 1 * (j + 1) * Lg X ^ j := by gcongr
    _ = _ := by ring

/-- `Lg` tends to infinity along the naturals. -/
theorem Lg_tendsto1619 : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
  (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop

/-- Eventually `D (log L + 2) ≤ ε L` along L = Lg X. -/
theorem Lg_absorb1619 (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      1 ≤ Lg X ∧ D * (Real.log (Lg X) + 2) ≤ ε * Lg X := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun y : ℝ => 2 / y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h3 : Tendsto (fun y : ℝ => (D + 1) * (Real.log y / y + 2 / y)) atTop (nhds 0) := by
    simpa using (h1.add h2).const_mul (D + 1)
  have h4 : ∀ᶠ y : ℝ in atTop, (D + 1) * (Real.log y / y + 2 / y) < ε :=
    h3.eventually (gt_mem_nhds hε)
  have h5 := (Lg_tendsto1619.eventually h4).and (Lg_tendsto1619.eventually_ge_atTop 1)
  obtain ⟨X₀, hX₀⟩ := h5.exists_forall_of_atTop
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨h6, h7⟩ := hX₀ X hX
  refine ⟨h7, ?_⟩
  have hL : 0 < Lg X := by linarith
  have he : (D + 1) * (Real.log (Lg X) / Lg X + 2 / Lg X) * Lg X =
      (D + 1) * (Real.log (Lg X) + 2) := by
    field_simp
  have h8 := mul_le_mul_of_nonneg_right h6.le hL.le
  rw [he] at h8
  have hlogL : 0 ≤ Real.log (Lg X) := Real.log_nonneg h7
  nlinarith

/-- `RepairedMainJ131` on all of J(X) from the narrow window, by the two parameter transfer of
U-1617 section 4 at Y = 9X/10. The boundary N near 2X/3 lie in the narrow window of Y. -/
theorem repaired_main_of_narrow1619
    (hcount : ∀ k : ℕ, 1 ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        (((evenJNarrow1619 k X).filter (fun N : ℕ =>
          η * N * Lg X ^ k < |Rpp k X N - coefficient131 k N * N * Lg X ^ k|)).card : ℝ) ≤
        K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10) :
    RepairedMainJ131 := by
  classical
  intro k hk
  obtain ⟨K, hK, hc⟩ := hcount k hk
  refine ⟨2 * K, by positivity, fun η hη => ?_⟩
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨X₁, hX₁⟩ := hc η hη
  obtain ⟨X₂, hX₂⟩ := hc (η / 3) hη3
  set B : ℝ := 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d with hB
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (coefficient_le131 hk 0)
    exact mul_nonneg (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
      (by linarith [Ck_ge_one131 hk 0])
  have hPC : 0 ≤ pairConstant131 := by
    unfold pairConstant131
    norm_num [LeanLab.SchnirelmannExplicit.C1]
    positivity
  obtain ⟨X₃, hX₃⟩ := Lg_absorb1619 ((k : ℝ) * pairConstant131 + k * B) (η / 3)
    (by positivity) hη3
  obtain ⟨X₄, hX₄⟩ := tuple_window131 (3 * k)
  refine ⟨max 40 (2 * max X₁ (max X₂ (max X₃ X₄))), fun X hX => ?_⟩
  have h40 : 40 ≤ X := le_trans (le_max_left _ _) hX
  have hhalf : 2 * max X₁ (max X₂ (max X₃ X₄)) ≤ X := le_trans (le_max_right _ _) hX
  set Y := X * 9 / 10 with hYdef
  have hYX : Y ≤ X := by omega
  have hXY : X ≤ 2 * Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hYm : max X₁ (max X₂ (max X₃ X₄)) ≤ Y := by omega
  have hYX₂ : X₂ ≤ Y := by omega
  have hXX₁ : X₁ ≤ X := by omega
  have hXX₃ : X₃ ≤ X := by omega
  have hXX₄ : X₄ ≤ X := by omega
  have hYX₄ : X₄ ≤ Y := by omega
  obtain ⟨hL1, habs⟩ := hX₃ X hXX₃
  have hXw := (hX₄ X hXX₄).2
  have hYw := (hX₄ Y hYX₄).2
  have hL0 : 0 < Lg X := by linarith
  have hLY : Lg Y ≤ Lg X := Lg_mono1619 hY1 hYX
  have hLY0 : 0 ≤ Lg Y := Real.logb_nonneg (by norm_num) (by exact_mod_cast hY1)
  have hLYs : Lg X ≤ Lg Y + 1 := Lg_le_succ1619 hY1 hXY
  set F : Finset ℕ := (evenJ131 X).filter (fun N : ℕ =>
    η * N * Lg X ^ k < |Rpp k X N - coefficient131 k N * N * Lg X ^ k|) with hF
  set A₁ : Finset ℕ := (evenJNarrow1619 k X).filter (fun N : ℕ =>
    η * N * Lg X ^ k < |Rpp k X N - coefficient131 k N * N * Lg X ^ k|) with hA₁
  set A₂ : Finset ℕ := (evenJNarrow1619 k Y).filter (fun N : ℕ =>
    η / 3 * N * Lg Y ^ k < |Rpp k Y N - coefficient131 k N * N * Lg Y ^ k|) with hA₂
  have hsub : F ⊆ A₁ ∪ A₂ := by
    intro N hN
    obtain ⟨hJ, hbad⟩ := mem_filter.mp hN
    by_cases hnarrow : N ∈ evenJNarrow1619 k X
    · exact mem_union_left _ (mem_filter.mpr ⟨hnarrow, hbad⟩)
    refine mem_union_right _ ?_
    obtain ⟨hN1, hN2, hN3, hN4⟩ := evenJ_nat131 hJ
    have hnw : ¬ (2 * X + 3 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) ≤ 3 * N) :=
      fun h => hnarrow (mem_filter.mpr ⟨hJ, h⟩)
    set a := k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ with ha
    set b := k * 2 ^ ⌊Lg Y - Real.sqrt (Lg Y)⌋₊ with hb
    have ha18 : 18 * a ≤ X := by
      have : 18 * a = 6 * (3 * k) * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by rw [ha]; ring
      omega
    have hb18 : 18 * b ≤ Y := by
      have : 18 * b = 6 * (3 * k) * 2 ^ ⌊Lg Y - Real.sqrt (Lg Y)⌋₊ := by rw [hb]; ring
      omega
    have hNY : N ≤ Y := by omega
    have hNwY : 2 * Y + 3 * b ≤ 3 * N := by omega
    have hJY : N ∈ evenJ131 Y := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hN1, hNY⟩, hN3, ?_⟩
      have h2 : 2 * Y ≤ 3 * N := by omega
      have h2' : 2 * (Y : ℝ) ≤ 3 * N := by exact_mod_cast h2
      linarith
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hJY, hNwY⟩, ?_⟩
    have hN3' : 3 ≤ N := by omega
    have htr := Rpp_transfer1619 hk hY1 hYX hXY hNY hN3'
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlogX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
    have hlogXL : Real.log X ≤ Lg X := by
      unfold Lg
      rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      nlinarith [mul_nonneg hlogX (sub_nonneg.mpr (show Real.log 2 ≤ 1 by
        linarith [Real.log_two_lt_d9]))]
    have hlogNL : Real.log N ≤ Lg X :=
      (Real.log_le_log hNr (by exact_mod_cast hN2)).trans hlogXL
    have hLL : Real.log (Real.log N) ≤ Real.log (Lg X) := Real.log_le_log hlogN0 hlogNL
    have hlogL0 : 0 ≤ Real.log (Lg X) := Real.log_nonneg hL1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at htr
    have hLj : 0 ≤ Lg X ^ j := by positivity
    have hlogsum : ((j + 1 : ℕ) : ℝ) * pairConstant131 * (Real.log (Lg X) + 2) +
        ((j + 1 : ℕ) : ℝ) * B * 1 ≤ η / 3 * Lg X := by
      have : (0:ℝ) ≤ ((j + 1 : ℕ) : ℝ) * B := by positivity
      nlinarith
    have hpair : ((j + 1 : ℕ) : ℝ) * pairConstant131 * (Real.log (Lg X) + 2) ≤ η / 3 * Lg X := by
      have : (0:ℝ) ≤ ((j + 1 : ℕ) : ℝ) * B := by positivity
      linarith
    have hbB : ((j + 1 : ℕ) : ℝ) * B ≤ η / 3 * Lg X := by
      have : (0:ℝ) ≤ ((j + 1 : ℕ) : ℝ) * pairConstant131 * (Real.log (Lg X) + 2) := by positivity
      linarith
    have hterm1 : |Rpp (j + 1) X N - Rpp (j + 1) Y N| ≤ η / 3 * N * Lg X ^ (j + 1) := by
      refine htr.trans ?_
      have h1 : Real.log (Real.log N) + 2 ≤ Real.log (Lg X) + 2 := by linarith
      calc ((j + 1 : ℕ) : ℝ) * Lg X ^ j * (pairConstant131 * N * (Real.log (Real.log N) + 2))
          ≤ ((j + 1 : ℕ) : ℝ) * Lg X ^ j * (pairConstant131 * N * (Real.log (Lg X) + 2)) := by
            gcongr
        _ = (((j + 1 : ℕ) : ℝ) * pairConstant131 * (Real.log (Lg X) + 2)) * (N * Lg X ^ j) := by
            ring
        _ ≤ (η / 3 * Lg X) * (N * Lg X ^ j) := by gcongr
        _ = η / 3 * N * Lg X ^ (j + 1) := by ring
    have hdiffL : Lg X ^ (j + 1) - Lg Y ^ (j + 1) ≤ ((j + 1 : ℕ) : ℝ) * Lg X ^ j := by
      have hp := abs_pow_sub_pow_le (a := Lg X) (b := Lg Y) (n := j + 1)
      have hpow : Lg Y ^ (j + 1) ≤ Lg X ^ (j + 1) := pow_le_pow_left₀ hLY0 hLY _
      simp only [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg (sub_nonneg.mpr hLY),
        abs_of_nonneg hL0.le, abs_of_nonneg hLY0, max_eq_left hLY, Nat.add_sub_cancel] at hp
      push_cast at hp ⊢
      calc _ ≤ _ := hp
        _ ≤ 1 * ((j : ℝ) + 1) * Lg X ^ j := by
            have : Lg X - Lg Y ≤ 1 := by linarith
            gcongr
        _ = _ := by ring
    have hcoef0 : 0 ≤ coefficient131 (j + 1) N :=
      mul_nonneg (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
        (by linarith [Ck_ge_one131 hk N])
    have hcoefB : coefficient131 (j + 1) N ≤ B := coefficient_le131 hk N
    have hpowle : Lg Y ^ (j + 1) ≤ Lg X ^ (j + 1) := pow_le_pow_left₀ hLY0 hLY _
    have hterm3 : |coefficient131 (j + 1) N * N * Lg Y ^ (j + 1) -
        coefficient131 (j + 1) N * N * Lg X ^ (j + 1)| ≤ η / 3 * N * Lg X ^ (j + 1) := by
      have he : coefficient131 (j + 1) N * N * Lg Y ^ (j + 1) -
          coefficient131 (j + 1) N * N * Lg X ^ (j + 1) =
          -(coefficient131 (j + 1) N * N * (Lg X ^ (j + 1) - Lg Y ^ (j + 1))) := by ring
      rw [he, abs_neg, abs_of_nonneg (by
        have : 0 ≤ Lg X ^ (j + 1) - Lg Y ^ (j + 1) := sub_nonneg.mpr hpowle
        positivity)]
      calc coefficient131 (j + 1) N * N * (Lg X ^ (j + 1) - Lg Y ^ (j + 1))
          ≤ B * N * (((j + 1 : ℕ) : ℝ) * Lg X ^ j) := by
            have : 0 ≤ Lg X ^ (j + 1) - Lg Y ^ (j + 1) := sub_nonneg.mpr hpowle
            gcongr
        _ = (((j + 1 : ℕ) : ℝ) * B) * (N * Lg X ^ j) := by ring
        _ ≤ (η / 3 * Lg X) * (N * Lg X ^ j) := by gcongr
        _ = η / 3 * N * Lg X ^ (j + 1) := by ring
    have htri : |Rpp (j + 1) X N - coefficient131 (j + 1) N * N * Lg X ^ (j + 1)| ≤
        |Rpp (j + 1) X N - Rpp (j + 1) Y N| +
        |Rpp (j + 1) Y N - coefficient131 (j + 1) N * N * Lg Y ^ (j + 1)| +
        |coefficient131 (j + 1) N * N * Lg Y ^ (j + 1) -
          coefficient131 (j + 1) N * N * Lg X ^ (j + 1)| := by
      have h := abs_add_three (Rpp (j + 1) X N - Rpp (j + 1) Y N)
        (Rpp (j + 1) Y N - coefficient131 (j + 1) N * N * Lg Y ^ (j + 1))
        (coefficient131 (j + 1) N * N * Lg Y ^ (j + 1) -
          coefficient131 (j + 1) N * N * Lg X ^ (j + 1))
      have he : Rpp (j + 1) X N - Rpp (j + 1) Y N +
          (Rpp (j + 1) Y N - coefficient131 (j + 1) N * N * Lg Y ^ (j + 1)) +
          (coefficient131 (j + 1) N * N * Lg Y ^ (j + 1) -
            coefficient131 (j + 1) N * N * Lg X ^ (j + 1)) =
          Rpp (j + 1) X N - coefficient131 (j + 1) N * N * Lg X ^ (j + 1) := by ring
      rwa [he] at h
    have hYbound : η / 3 * N * Lg Y ^ (j + 1) ≤ η / 3 * N * Lg X ^ (j + 1) := by gcongr
    have h3eq : η * N * Lg X ^ (j + 1) = 3 * (η / 3 * N * Lg X ^ (j + 1)) := by ring
    rw [h3eq] at hbad
    linarith
  have hcard : (F.card : ℝ) ≤ (A₁.card : ℝ) + A₂.card := by
    have := (card_le_card hsub).trans (card_union_le A₁ A₂)
    exact_mod_cast this
  have hA1 := hX₁ X hXX₁
  have hA2 := hX₂ Y hYX₂
  have hX1' : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
  have hYr : (Y : ℝ) ≤ X := by exact_mod_cast hYX
  have hmono1 : (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ (X : ℝ) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow (by linarith) hYr (by norm_num)
  have hmono2 : Real.log Y ^ 10 ≤ Real.log X ^ 10 :=
    pow_le_pow_left₀ (Real.log_natCast_nonneg Y) (Real.log_le_log (by linarith) hYr) _
  have hprod : K * (Y : ℝ) ^ ((3 : ℝ) / 5) * Real.log Y ^ 10 ≤
      K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
    have h0 : 0 ≤ (Y : ℝ) ^ ((3 : ℝ) / 5) := Real.rpow_nonneg (by linarith) _
    have h1 : 0 ≤ Real.log X ^ 10 := pow_nonneg (Real.log_natCast_nonneg X) _
    gcongr
  calc (F.card : ℝ) ≤ (A₁.card : ℝ) + A₂.card := hcard
    _ ≤ K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 +
        K * (Y : ℝ) ^ ((3 : ℝ) / 5) * Real.log Y ^ 10 := add_le_add hA1 hA2
    _ ≤ 2 * K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by linarith

end

end LeanLab.LPZ2007
