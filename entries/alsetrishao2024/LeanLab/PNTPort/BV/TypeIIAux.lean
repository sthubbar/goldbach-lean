module

public import LeanLab.PNTPort.BV.S4Blocks
public import LeanLab.HeathBrown1985.DivMoments

/-!
lab proof, AI wrote this file, known mathematics, no cited input

Auxiliary bounds for the Type II sum: mean values of `Λ` and `g_v` on intervals, a
sum conversion `ℕ → ℤ`, and the square root estimate used per dyadic block.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction

lemma sum_Ioc_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a n : ℕ) :
    ∑ m ∈ Ioc (a : ℤ) (a + (n : ℤ)), f m = ∑ t ∈ Ioc a (a + n), f t := by
  have h := Finset.sum_map (Ioc a (a + n)) Nat.castEmbedding f
  simp only [Nat.castEmbedding_apply] at h
  rw [← h]
  congr 1
  ext m
  simp only [mem_Ioc, mem_map, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨m.toNat, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma sum_vonMangoldt_block (M : ℕ) :
    ∑ t ∈ Ioc M (M + M), vonMangoldt t ≤ (Real.log 4 + 4) * (2 * M) := by
  have h := Chebyshev.psi_le_const_mul_self (x := ((M + M : ℕ) : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at h
  calc _ ≤ ∑ t ∈ Ioc 0 (M + M), vonMangoldt t :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
          (fun _ _ _ => vonMangoldt_nonneg)
    _ ≤ _ := by push_cast at h; linarith

lemma sum_vonMangoldt_sq_block (M : ℕ) :
    ∑ t ∈ Ioc M (M + M), vonMangoldt t ^ 2 ≤
      Real.log (2 * M) * ((Real.log 4 + 4) * (2 * M)) := by
  have hl : 0 ≤ Real.log (2 * M) := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h]
    · apply Real.log_nonneg; have : (1 : ℝ) ≤ M := by exact_mod_cast h
      linarith
  calc _ ≤ ∑ t ∈ Ioc M (M + M), Real.log (2 * M) * vonMangoldt t := by
        apply sum_le_sum
        intro t ht
        have ht' := mem_Ioc.1 ht
        have h1 : vonMangoldt t ≤ Real.log (2 * M) := by
          refine vonMangoldt_le_log.trans ?_
          rcases Nat.eq_zero_or_pos t with h | h
          · simp [h]; exact hl
          · apply Real.log_le_log (by exact_mod_cast h)
            have : (t : ℝ) ≤ (M + M : ℕ) := by exact_mod_cast ht'.2
            push_cast at this; linarith
        rw [sq]
        exact mul_le_mul_of_nonneg_right h1 vonMangoldt_nonneg
    _ = Real.log (2 * M) * ∑ t ∈ Ioc M (M + M), vonMangoldt t := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_vonMangoldt_block M) hl

lemma abs_gV_le (v r : ℕ) : |gV v r| ≤ (r.divisors.card : ℝ) := by
  unfold gV; exact abs_trunc_moebius_sum_le v r

lemma sum_divisors_sq_Ioc (w N₂ : ℕ) :
    ∑ r ∈ Ioc w (w + N₂), (r.divisors.card : ℝ) ^ 2 ≤
      (w + N₂ : ℕ) * (1 + Real.log ((w + N₂ : ℕ) : ℝ)) ^ 3 := by
  calc _ ≤ ∑ r ∈ Icc 1 (w + N₂), (r.divisors.card : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun r hr => by
          simp only [mem_Ioc, mem_Icc] at hr ⊢; omega) (fun _ _ _ => by positivity)
    _ ≤ _ := by
        refine (HeathBrown1985.sum_sq_divisors_le _).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (HeathBrown1985.Hn_nonneg _) (HeathBrown1985.Hn_le _) 3

lemma sum_gV_sq_le (w N₂ : ℕ) :
    ∑ r ∈ Ioc w (w + N₂), gV w r ^ 2 ≤
      (w + N₂ : ℕ) * (1 + Real.log ((w + N₂ : ℕ) : ℝ)) ^ 3 := by
  refine le_trans (sum_le_sum fun r _ => ?_) (sum_divisors_sq_Ioc w N₂)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_gV_le w r) 2

lemma sum_abs_gV_le (w N₂ : ℕ) :
    ∑ r ∈ Ioc w (w + N₂), |gV w r| ≤
      (w + N₂ : ℕ) * (1 + Real.log ((w + N₂ : ℕ) : ℝ)) ^ 3 := by
  refine le_trans (sum_le_sum fun r _ => ?_) (sum_divisors_sq_Ioc w N₂)
  refine (abs_gV_le w r).trans ?_
  set d : ℕ := r.divisors.card
  have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  exact this

/-- The square root estimate of one block. -/
lemma sqrt_block_le {M N₂ R x w Sa Sb c ℓ : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N₂) (hR : 0 ≤ R)
    (hw : 0 < w) (hc : 0 ≤ c) (hℓ : 0 ≤ ℓ) (hSa0 : 0 ≤ Sa) (hSb0 : 0 ≤ Sb)
    (hSa : Sa ≤ 2 * c * ℓ * M) (hSb : Sb ≤ 2 * N₂ * ℓ ^ 3)
    (hMN : M * N₂ ≤ x) (hMw : M * w ≤ x) (hNw : N₂ * w ≤ x) :
    Real.sqrt (((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb)) ≤
      2 * Real.sqrt c * ℓ ^ 2 * (x + 4 * R * x / Real.sqrt w + 4 * R ^ 2 * Real.sqrt x) := by
  set m := Real.sqrt M
  set n := Real.sqrt N₂
  set s := Real.sqrt x
  set ω := Real.sqrt w
  have hx : 0 ≤ x := le_trans (mul_nonneg hM hN) hMN
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hω : 0 < ω := Real.sqrt_pos.2 hw
  have hmm : m ^ 2 = M := Real.sq_sqrt hM
  have hnn : n ^ 2 = N₂ := Real.sq_sqrt hN
  have hss : s ^ 2 = x := Real.sq_sqrt hx
  have hcc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  have hmn : m * n ≤ s := by
    rw [← Real.sqrt_mul hM]; exact Real.sqrt_le_sqrt hMN
  have hmω : m * ω ≤ s := by
    rw [← Real.sqrt_mul hM]; exact Real.sqrt_le_sqrt hMw
  have hnω : n * ω ≤ s := by
    rw [← Real.sqrt_mul hN]; exact Real.sqrt_le_sqrt hNw
  set F := (M + 2 * R * m) * (N₂ + 2 * R * n) with hF
  have hF0 : 0 ≤ F := by positivity
  have hP : ((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb) ≤
      (2 * Real.sqrt c * ℓ ^ 2 * F) ^ 2 := by
    have e1 : ((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb) ≤
        ((M + 2 * R ^ 2) * (2 * c * ℓ * M)) * ((N₂ + 2 * R ^ 2) * (2 * N₂ * ℓ ^ 3)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hSa (by positivity))
        (mul_le_mul_of_nonneg_left hSb (by positivity)) (by positivity) (by positivity)
    have e2 : M * (M + 2 * R ^ 2) ≤ (M + 2 * R * m) ^ 2 := by
      rw [← hmm]; nlinarith [mul_nonneg hR hm0, pow_nonneg hm0 3, mul_nonneg (mul_nonneg hR hR) (sq_nonneg m)]
    have e3 : N₂ * (N₂ + 2 * R ^ 2) ≤ (N₂ + 2 * R * n) ^ 2 := by
      rw [← hnn]; nlinarith [mul_nonneg hR hn0, pow_nonneg hn0 3, mul_nonneg (mul_nonneg hR hR) (sq_nonneg n)]
    have e4 : ((M + 2 * R ^ 2) * (2 * c * ℓ * M)) * ((N₂ + 2 * R ^ 2) * (2 * N₂ * ℓ ^ 3)) =
        4 * c * ℓ ^ 4 * ((M * (M + 2 * R ^ 2)) * (N₂ * (N₂ + 2 * R ^ 2))) := by ring
    have e5 : (2 * Real.sqrt c * ℓ ^ 2 * F) ^ 2 =
        4 * c * ℓ ^ 4 * ((M + 2 * R * m) ^ 2 * (N₂ + 2 * R * n) ^ 2) := by
      have : (2 * Real.sqrt c * ℓ ^ 2 * F) ^ 2 = 4 * Real.sqrt c ^ 2 * ℓ ^ 4 * F ^ 2 := by ring
      rw [this, hcc, hF]; ring
    rw [e5]
    refine e1.trans ?_
    rw [e4]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul e2 e3 (by positivity) (by positivity)
  have hsq : Real.sqrt (((M + 2 * R ^ 2) * Sa) * ((N₂ + 2 * R ^ 2) * Sb)) ≤
      2 * Real.sqrt c * ℓ ^ 2 * F := by
    rw [← Real.sqrt_sq (show 0 ≤ 2 * Real.sqrt c * ℓ ^ 2 * F by positivity)]
    exact Real.sqrt_le_sqrt hP
  refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- F ≤ x + 4 R x / ω + 4 R² s
  have k1 : M * n ≤ x / ω := by
    rw [le_div_iff₀ hω, ← hmm, ← hss]
    nlinarith [mul_le_mul hmn hmω (by positivity) (Real.sqrt_nonneg x)]
  have k2 : m * N₂ ≤ x / ω := by
    rw [le_div_iff₀ hω, ← hnn, ← hss]
    nlinarith [mul_le_mul hmn hnω (by positivity) (Real.sqrt_nonneg x)]
  have e : F = M * N₂ + 2 * R * (M * n + m * N₂) + 4 * R ^ 2 * (m * n) := by rw [hF]; ring
  rw [e]
  have h4 : 4 * R * x / ω = 2 * R * (x / ω + x / ω) := by ring
  rw [h4]
  have := mul_le_mul_of_nonneg_left (add_le_add k1 k2) (show 0 ≤ 2 * R by positivity)
  have := mul_le_mul_of_nonneg_left hmn (show 0 ≤ 4 * R ^ 2 by positivity)
  linarith

end LeanLab.PNTPort.BV
