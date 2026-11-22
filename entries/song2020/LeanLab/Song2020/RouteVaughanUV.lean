module

public import LeanLab.Song2020.RouteVaughanLeaves
public import LeanLab.Song2020.RouteVaughanSigma1

/-!
AI wrote the Lean code, 2026-11-15, assembly for the target vaughan_uv.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 5 to 7, from
"Apply Lemma 3.2 with uv <= n" to the display for x^(-epsilon) (Sigma2 + Sigma3).
This file proves the statement of SPLIT_vaughan_per_u.vaughan_uv, word for word, from the
page 6 display RouteVaughanSigma1.sigma1_route, itself proved from the one leaf
RouteVaughanSigma1.inner_sum_bound, and the two page 7 leaves sigma2_bound and sigma3_bound
of RouteVaughanLeaves. The glue is: the lab's
proved Vaughan identity Akeno2026.Vaughan86.vaughan_weighted_identity, which is the paper's
Lemma 3.2; the splitting of its double convolution mu_u * Lambda_v * zeta at r at most u,
which separates the second half of Sigma 1 from Sigma 3; and the trivial bound of the short
term Lambda_v, which the paper does not display because its window sits above v, and which
is absorbed in the term n^(1/2) (u v)^(1/2) since v is at most n^(1/2) (u v)^(1/2) when
1 at most u and u v at most n. It defines nothing and has no leaf of its own; the open leaves it rests on are
inner_sum_bound, sigma2_bound and sigma3_bound.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteVaughanUV

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Akeno2026.Vaughan86
open scoped Classical

noncomputable section

/-- Song 2020, page 5, the definitions of Sigma 1 and Sigma 3: the double convolution of the
Vaughan identity, summed against any weight, splits at r at most u into the part that
belongs to Sigma 1 and the part u < r that is Sigma 3. Here g is mu_u * Lambda_v and r is
its argument. -/
theorem split_at_u (u : ℝ) (g : ArithmeticFunction ℝ) (s : Finset ℕ) (F : ℕ → ℂ) :
    (∑ x ∈ s, ((g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * F x) =
      (∑ x ∈ s, ((shortPart g u *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * F x) +
      (∑ x ∈ s, (((g - shortPart g u) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * F x) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← add_mul, ← Complex.ofReal_add, ← ArithmeticFunction.add_apply, ← add_mul,
    add_sub_cancel]

/-- The modulus of the additive character is one; used for the trivial bound of the short
term of the Vaughan identity on page 5. -/
private theorem norm_eC (θ : ℝ) : ‖eC θ‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- The value of the cut arithmetic function Lambda_v of the Vaughan identity, page 5: it is
the function at arguments at most the cut and zero beyond. -/
private theorem shortPart_apply (f : ArithmeticFunction ℝ) (U : ℝ) (x : ℕ) :
    shortPart f U x = if (x : ℝ) ≤ U then f x else 0 := rfl

/-- Song 2020, page 5, "Apply Lemma 3.2 with uv <= n": the short von Mangoldt term of the
Vaughan identity, which the print omits. Every term has modulus Lambda of x at most log n,
there are at most v terms with x at most v, log n is at most n^epsilon over epsilon, and
v is at most n^(1/2) (u v)^(1/2) because v is at most u v and u v is at most n. -/
theorem short_term_bound (γ ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) (y α : ℝ) (h : ℤ)
    (t u v : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u * v ≤ n) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
        (shortPart ArithmeticFunction.vonMangoldt v x : ℂ) *
          eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
      (1 / ε) * (n : ℝ) ^ ε * ((n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hv0 : 0 < v := by linarith
  have hvuv : v ≤ u * v := by nlinarith
  have hvn : v ≤ (n : ℝ) := hvuv.trans huv
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  -- each term is at most log n on the integers 1 to floor v, and vanishes elsewhere
  have hterm : ∀ x : ℕ,
      ‖(shortPart ArithmeticFunction.vonMangoldt v x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
        if x ∈ Finset.Icc 1 ⌊v⌋₊ then Real.log (n : ℝ) else 0 := by
    intro x
    rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs, shortPart_apply]
    by_cases hx : (x : ℝ) ≤ v
    · rw [ite_eq_left hx, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rcases Nat.eq_zero_or_pos x with h0 | hp
      · subst h0
        rw [ArithmeticFunction.map_zero]
        split_ifs
        · exact hlogn
        · exact le_rfl
      · have hmem : x ∈ Finset.Icc 1 ⌊v⌋₊ :=
          Finset.mem_Icc.mpr ⟨hp, Nat.le_floor hx⟩
        rw [ite_eq_left hmem]
        have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hp
        exact (ArithmeticFunction.vonMangoldt_le_log (n := x)).trans
          (Real.log_le_log hxpos (hx.trans hvn))
    · rw [ite_eq_right hx, abs_zero]
      split_ifs
      · exact hlogn
      · exact le_rfl
  have hsum : ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
        (shortPart ArithmeticFunction.vonMangoldt v x : ℂ) *
          eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ v * Real.log (n : ℝ) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun x _ => hterm x)).trans ?_)
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_card_nsmul _ _ (Real.log (n : ℝ)) (fun _ _ => le_rfl)).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hlogn
    have hcard : (Finset.filter (fun x => x ∈ Finset.Icc 1 ⌊v⌋₊)
        ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t))).card ≤ ⌊v⌋₊ := by
      have hsub : Finset.filter (fun x => x ∈ Finset.Icc 1 ⌊v⌋₊)
          ((Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)) ⊆
          Finset.Icc 1 ⌊v⌋₊ := fun x hx => (Finset.mem_filter.mp hx).2
      simpa using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hv0.le)
  have hlog : Real.log (n : ℝ) ≤ (1 / ε) * (n : ℝ) ^ ε := by
    have := Real.log_le_rpow_div hn0.le hε
    rw [div_eq_inv_mul] at this
    simpa using this
  have hv2 : v ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) := by
    have hsplit : v = v ^ ((1 : ℝ) / 2) * v ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hv0]
      norm_num
    calc v = v ^ ((1 : ℝ) / 2) * v ^ ((1 : ℝ) / 2) := hsplit
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) :=
        mul_le_mul (Real.rpow_le_rpow hv0.le hvn (by norm_num))
          (Real.rpow_le_rpow hv0.le hvuv (by norm_num))
          (Real.rpow_nonneg hv0.le _) (Real.rpow_nonneg hn0.le _)
  calc _ ≤ v * Real.log (n : ℝ) := hsum
    _ ≤ ((n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2)) * ((1 / ε) * (n : ℝ) ^ ε) :=
        mul_le_mul hv2 hlog hlogn (hv0.le.trans hv2)
    _ = (1 / ε) * (n : ℝ) ^ ε * ((n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2)) := by
        ring

/-- Song 2020, pages 5 to 7: the bounds for the three Vaughan pieces with u and v free, the
statement of SPLIT_vaughan_per_u.vaughan_uv word for word, proved from
RouteVaughanSigma1.sigma1_route and the leaves sigma2_bound and sigma3_bound of
RouteVaughanLeaves through the Vaughan
identity, the splitting at r at most u and the trivial bound of the short term. -/
theorem vaughan_uv_route :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ C * (n : ℝ) ^ ε *
              (u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) +
                (n : ℝ) * v ^ (-(1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  intro γ hγ1 hγ2 ε hε
  obtain ⟨C1, hC1, N1, H1⟩ := RouteVaughanSigma1.sigma1_route γ hγ1 hγ2 ε hε
  obtain ⟨C2, hC2, N2, H2⟩ := RouteVaughanLeaves.sigma2_bound γ hγ1 hγ2 ε hε
  obtain ⟨C3, hC3, N3, H3⟩ := RouteVaughanLeaves.sigma3_bound γ hγ1 hγ2 ε hε
  refine ⟨C1 + C2 + C3 + 1 / ε, by positivity, max (max N1 N2) (max N3 1), ?_⟩
  intro n hn y hy1 hy2 α h hh t u v hu hv huv
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have b1 := H1 n hn1 y hy1 hy2 α h hh t u v hu hv huv
  have b2 := H2 n hn2 y hy1 hy2 α h hh t u v hu hv huv
  have b3 := H3 n hn3 y hy1 hy2 α h hh t u v hu hv huv
  have b4 := short_term_bound γ ε hε n hn4 y α h t u v hu hv huv
  rw [vaughan_weighted_identity u v, split_at_u u]
  have tri : ∀ a b1 b3 e d : ℂ,
      ‖a - (b1 + b3) + e + d‖ ≤ ‖a - b1‖ + ‖b3‖ + ‖e‖ + ‖d‖ := by
    intro a b1 b3 e d
    have hre : a - (b1 + b3) + e + d = (a - b1) - b3 + e + d := by ring
    rw [hre]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  refine (tri _ _ _ _ _).trans ?_
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy0 : 0 ≤ y := (Real.rpow_nonneg hn0 _).trans hy1.le
  have hh0 : 0 ≤ |(h : ℝ)| := abs_nonneg _
  have hP : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hn0 _
  have hE : 0 ≤ 1 / ε := by positivity
  have hT1 : 0 ≤ u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) :=
    mul_nonneg hu0 (mul_nonneg (mul_nonneg (Real.rpow_nonneg hh0 _)
      (Real.rpow_nonneg hn0 _)) hy0)
  have hT2 : 0 ≤ (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hh0 _)
  have hT3 : 0 ≤ (n : ℝ) * v ^ (-(1 : ℝ) / 2) := mul_nonneg hn0 (Real.rpow_nonneg hv0 _)
  have hT4 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg (mul_nonneg hu0 hv0) _)
  have hT5 : 0 ≤ (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) :=
    mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hh0 _)
  have hT6 : 0 ≤ u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) :=
    mul_nonneg (Real.rpow_nonneg hu0 _)
      (mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hy0 _))
  have hT7 : 0 ≤ u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
      |(h : ℝ)| ^ ((1 : ℝ) / 6)) :=
    mul_nonneg (Real.rpow_nonneg hu0 _) (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hy0 _)) (Real.rpow_nonneg hh0 _))
  have hT8 : 0 ≤ u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
      |(h : ℝ)| ^ ((1 : ℝ) / 4)) :=
    mul_nonneg (Real.rpow_nonneg hu0 _) (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hy0 _)) (Real.rpow_nonneg hh0 _))
  generalize u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) = T1 at b1 hT1 ⊢
  generalize (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) = T2 at b1 hT2 ⊢
  generalize (n : ℝ) * v ^ (-(1 : ℝ) / 2) = T3 at b2 hT3 ⊢
  generalize (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) = T4 at b3 b4 hT4 ⊢
  generalize (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) = T5 at b2 b3 hT5 ⊢
  generalize u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) = T6
    at b2 b3 hT6 ⊢
  generalize u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
      |(h : ℝ)| ^ ((1 : ℝ) / 6)) = T7 at b2 b3 hT7 ⊢
  generalize u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
      |(h : ℝ)| ^ ((1 : ℝ) / 4)) = T8 at b2 b3 hT8 ⊢
  generalize (n : ℝ) ^ ε = P at b1 b2 b3 b4 hP ⊢
  generalize 1 / ε = E at b4 hE ⊢
  have e1 : C1 * P * (T1 + T2) ≤ C1 * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC1 hP)
  have e2 : C2 * P * (T3 + T5 + T6 + T7 + T8) ≤
      C2 * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC2 hP)
  have e3 : C3 * P * (T4 + T5 + T6 + T7 + T8) ≤
      C3 * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC3 hP)
  have e4 : E * P * T4 ≤ E * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hE hP)
  have e5 : (C1 + C2 + C3 + E) * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) =
      C1 * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) +
      C2 * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) +
      C3 * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) +
      E * P * (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8) := by ring
  rw [e5]
  linarith

end

end LeanLab.Song2020.RouteVaughanUV
