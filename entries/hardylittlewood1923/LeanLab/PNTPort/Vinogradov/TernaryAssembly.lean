module

public import LeanLab.PNTPort.Vinogradov.TernaryArcs

/-!
# The ternary major arcs: the approximation on each arc

Lab proof, unit U-5254. AI wrote this file. Known mathematics, no cited input.

* `arc_approx`: on the arc of `a/q`, `𝓕Φ(k)` is within
  `E(1 + 2πN/(q(Q + 1)))` of `μ(q)/φ(q) V(-(k/M - a/q))`, whenever the major arc
  approximation `S(a'/q + β) ≈ μ(q)/φ(q) V(β)` holds with error `E(1 + 2π|β|N)`.
* `sum_majIdx`: `∑_{(q, a) reduced, q ≤ P} g(q) = ∑_{q ≤ P} φ(q) g(q)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve

lemma V_add_int (N : ℕ) (x : ℝ) (j : ℤ) : V N (x + j) = V N x := by
  unfold V
  refine sum_congr rfl fun n _ => ?_
  rw [mul_add, e_add, show ((n : ℝ) * (j : ℝ)) = (((n : ℤ) * j : ℤ) : ℝ) by push_cast; ring, e_int,
    mul_one]

lemma stdAddChar_nat_mul {M : ℕ} [NeZero M] (n : ℕ) (k : ZMod M) :
    (stdAddChar ((n : ZMod M) * k) : ℂ) = e (n * ((k.val : ℝ) / M)) := by
  have h := stdAddChar_neg_mul (M := M) n (-k)
  rw [mul_neg, neg_neg] at h
  rw [h]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp
  · rw [ZMod.neg_val, if_neg hk, Nat.cast_sub (ZMod.val_lt k).le]
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have : (n : ℝ) * (-(((M : ℝ) - k.val)) / M) = n * ((k.val : ℝ) / M) + ((-(n : ℤ) : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    rw [this, e_add, e_int, mul_one]

lemma norm_S_le (N : ℕ) (α : ℝ) : ‖S N α‖ ≤ (Real.log 4 + 4) * N := by
  have h := norm_Aq_le 1 0 N
  unfold Aq at h
  unfold S
  refine (norm_sum_le _ _).trans ?_
  have hψ := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at hψ
  have : Ioc 0 N = Icc 1 N := by ext m; simp only [mem_Ioc, mem_Icc]; omega
  rw [this] at hψ
  refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) hψ
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

lemma norm_V_le (N : ℕ) (β : ℝ) : ‖V N β‖ ≤ N := by
  unfold V
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

lemma cube_diff {x y : ℂ} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖x ^ 3 - y ^ 3‖ ≤ 3 * R ^ 2 * ‖x - y‖ := by
  have h : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [h, norm_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hx
  calc ‖x ^ 2 + x * y + y ^ 2‖ ≤ ‖x ^ 2‖ + ‖x * y‖ + ‖y ^ 2‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _) |>.trans (by linarith)
    _ = ‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by rw [norm_pow, norm_mul, norm_pow]
    _ ≤ R ^ 2 + R * R + R ^ 2 := by
        gcongr
    _ = 3 * R ^ 2 := by ring

/-- The approximation on one arc. -/
theorem arc_approx {N M Q q a : ℕ} [NeZero M] (hNM : N < M) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) {E : ℝ}
    (hmaj : ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S N (a' / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤ E * (1 + 2 * π * |β| * N))
    {k : ZMod M} (hk : k ∈ arcSet M Q q a) :
    ‖𝓕 (PhiL N M) k - (μ q : ℂ) / q.totient * V N (-((k.val : ℝ) / M - (a : ℝ) / q))‖ ≤
      E * (1 + 2 * π * N / (q * (Q + 1))) := by
  have hd : dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1)) := by
    simp only [arcSet, Finset.mem_filter] at hk; exact hk.2
  set θ := (k.val : ℝ) / M - (a : ℝ) / q with hθ
  set j := round θ with hj
  set β := θ - j with hβ
  have hβd : |β| = dist0 θ := rfl
  have hc : IsCoprime (-((a : ℤ) + q * j)) (q : ℤ) := by
    have : IsCoprime (a : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
    exact (this.add_mul_left_left j).neg_left
  have h1 := hmaj _ hc (-β)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have e1 : ((-((a : ℤ) + q * j) : ℤ) : ℝ) / q + -β = -((k.val : ℝ) / M) := by
    rw [hβ, hθ]; push_cast; field_simp; ring
  have e2 : V N (-β) = V N (-θ) := by
    rw [hβ, show -(θ - (j : ℝ)) = -θ + ((j : ℤ) : ℝ) by ring, V_add_int]
  rw [e1, e2, abs_neg] at h1
  rw [dft_PhiL hNM, neg_div]
  refine h1.trans ?_
  have hE : 0 ≤ E := by
    have := le_trans (norm_nonneg _) h1
    have hpos : 0 < 1 + 2 * π * |β| * N := by positivity
    exact nonneg_of_mul_nonneg_left this hpos
  apply mul_le_mul_of_nonneg_left _ hE
  rw [hβd]
  have h2 := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * π * N by positivity)
  have : 2 * π * dist0 θ * N ≤ 2 * π * N / (q * (Q + 1)) := by
    calc 2 * π * dist0 θ * N = 2 * π * N * dist0 θ := by ring
      _ ≤ 2 * π * N * (1 / ((q : ℝ) * (Q + 1))) := h2
      _ = 2 * π * N / (q * (Q + 1)) := by ring
  linarith

/-- Summing a function of `q` over the reduced fractions. -/
lemma sum_majIdx (P : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ majIdx P, g p.1 = ∑ q ∈ Icc 1 P, (q.totient : ℝ) * g q := by
  unfold majIdx
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun q hq => ?_
  rw [mem_Icc] at hq
  dsimp only
  have hset : (range P).filter (fun a => a < q ∧ Nat.Coprime a q) =
      (range q).filter (fun a => Nat.Coprime q a) := by
    ext a
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, Nat.Coprime.symm h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, Nat.Coprime.symm h2⟩
  rw [← sum_filter, hset, sum_const, nsmul_eq_mul, Nat.totient_eq_card_coprime]

/-- The truncated singular series `𝔖_P(n) = ∑_{q ≤ P} ∑_{(a, q) = 1} (μ(q)/φ(q))³ e(an/q)`. -/
noncomputable def singP (P n : ℕ) : ℂ :=
  ∑ p ∈ majIdx P, ((μ p.1 : ℂ) / p.1.totient) ^ 3 * e (n * ((p.2 : ℝ) / p.1))

lemma norm_mu_div_le (q : ℕ) (hq : 1 ≤ q) : ‖(μ q : ℂ) / q.totient‖ ≤ 1 / q.totient := by
  have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by linarith)
  rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- One arc: its contribution against the main term. -/
theorem arc_sum {N M Q q a n : ℕ} [NeZero M] (h3 : 3 * N < M) (hn : n < M) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) {E : ℝ}
    (hmaj : ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S N (a' / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤ E * (1 + 2 * π * |β| * N)) :
    ‖∑ k ∈ arcSet M Q q a, (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
        ((μ q : ℂ) / q.totient) ^ 3 * e (n * ((a : ℝ) / q)) * ((M : ℂ) * (J N n : ℂ))‖ ≤
      (arcSet M Q q a).card * (3 * ((Real.log 4 + 4) * N) ^ 2 *
        (E * (1 + 2 * π * N / (q * (Q + 1))))) + 1 / q.totient * ((M : ℝ) * N * (q * (Q + 1)) / 2) := by
  have hNM : N < M := by omega
  set c : ℂ := (μ q : ℂ) / q.totient with hc
  set θ : ZMod M → ℝ := fun k => (k.val : ℝ) / M - (a : ℝ) / q with hθ
  set R := (Real.log 4 + 4) * N with hR
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hNR : (N : ℝ) ≤ R := by rw [hR]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hcn : ‖c‖ ≤ 1 / q.totient := norm_mu_div_le q hq
  have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hc1 : ‖c‖ ≤ 1 := hcn.trans (by rw [div_le_one (by linarith)]; exact ht)
  -- model term
  have hG : ∀ k : ZMod M, (c * V N (-θ k)) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) =
      c ^ 3 * e (n * ((a : ℝ) / q)) * (V N (-θ k) ^ 3 * e (n * θ k)) := by
    intro k
    rw [stdAddChar_nat_mul]
    have : e (n * ((k.val : ℝ) / M)) = e (n * ((a : ℝ) / q)) * e (n * θ k) := by
      rw [← e_add]; congr 1; simp only [hθ]; ring
    rw [this]; ring
  -- the arc sum of the model
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (ZMod M))
    (fun k => dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1)))
    (fun k => V N (-θ k) ^ 3 * e (n * θ k))
  have hfull := full_sum_V3 (N := N) (M := M) h3 hn ((a : ℝ) / q)
  have harc_eq : arcSet M Q q a = univ.filter
      (fun k => dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1))) := rfl
  have hmodel : ∑ k ∈ arcSet M Q q a, (c * V N (-θ k)) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ)
      = c ^ 3 * e (n * ((a : ℝ) / q)) * ((M : ℂ) * (J N n : ℂ) -
        ∑ k ∈ univ.filter (fun k => ¬ dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤
          1 / ((q : ℝ) * (Q + 1))), V N (-θ k) ^ 3 * e (n * θ k)) := by
    simp_rw [hG]
    rw [← mul_sum, ← hfull]
    congr 1
    rw [harc_eq, ← hsplit]
    ring
  have htail : ‖∑ k ∈ univ.filter (fun k => ¬ dist0 ((k.val : ℝ) / M - (a : ℝ) / q) ≤
          1 / ((q : ℝ) * (Q + 1))), V N (-θ k) ^ 3 * e (n * θ k)‖ ≤
        (M : ℝ) * N / (2 * (1 / ((q : ℝ) * (Q + 1)))) := by
    apply tail_V3_le hNM ((a : ℝ) / q) n (by positivity)
    intro k hk
    rw [mem_filter] at hk
    exact lt_of_not_ge hk.2
  -- the difference
  have hdiff : ∀ k ∈ arcSet M Q q a,
      ‖(𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
        (c * V N (-θ k)) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ)‖ ≤
        3 * R ^ 2 * (E * (1 + 2 * π * N / (q * (Q + 1)))) := by
    intro k hk
    rw [← sub_mul, norm_mul, stdAddChar_apply, Circle.norm_coe, mul_one]
    have hx : ‖𝓕 (PhiL N M) k‖ ≤ R := by rw [dft_PhiL hNM]; exact norm_S_le N _
    have hy : ‖c * V N (-θ k)‖ ≤ R := by
      rw [norm_mul]
      calc ‖c‖ * ‖V N (-θ k)‖ ≤ 1 * N := mul_le_mul hc1 (norm_V_le _ _) (norm_nonneg _) zero_le_one
        _ ≤ R := by linarith
    refine (cube_diff hx hy).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact arc_approx hNM hq hcop hmaj hk
  calc _ = ‖∑ k ∈ arcSet M Q q a, ((𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
          (c * V N (-θ k)) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ)) +
        (-(c ^ 3 * e (n * ((a : ℝ) / q))) * ∑ k ∈ univ.filter (fun k => ¬ dist0 ((k.val : ℝ) / M -
          (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1))), V N (-θ k) ^ 3 * e (n * θ k))‖ := by
        rw [sum_sub_distrib, hmodel]; congr 1; ring
    _ ≤ ‖∑ k ∈ arcSet M Q q a, ((𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
          (c * V N (-θ k)) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ))‖ +
        ‖c‖ ^ 3 * ‖∑ k ∈ univ.filter (fun k => ¬ dist0 ((k.val : ℝ) / M -
          (a : ℝ) / q) ≤ 1 / ((q : ℝ) * (Q + 1))), V N (-θ k) ^ 3 * e (n * θ k)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_neg, norm_mul, norm_pow, norm_e, mul_one]
    _ ≤ _ := by
        apply add_le_add
        · refine (norm_sum_le _ _).trans ((sum_le_sum hdiff).trans (le_of_eq ?_))
          rw [sum_const, nsmul_eq_mul]
        · have hc3 : ‖c‖ ^ 3 ≤ 1 / q.totient := by
            calc ‖c‖ ^ 3 ≤ ‖c‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hc1 (by norm_num)
              _ ≤ _ := by rw [pow_one]; exact hcn
          refine mul_le_mul hc3 (htail.trans (le_of_eq ?_)) (norm_nonneg _) (by positivity)
          field_simp

lemma card_majIdx_le (P : ℕ) : ((majIdx P).card : ℝ) ≤ (P : ℝ) ^ 2 := by
  have h := card_le_card (filter_subset (fun p : ℕ × ℕ => p.2 < p.1 ∧ Nat.Coprime p.2 p.1)
    (Icc 1 P ×ˢ range P))
  rw [card_product, Nat.card_Icc, card_range, Nat.add_sub_cancel] at h
  have : (majIdx P).card ≤ P * P := by unfold majIdx; exact h
  calc ((majIdx P).card : ℝ) ≤ ((P * P : ℕ) : ℝ) := by exact_mod_cast this
    _ = (P : ℝ) ^ 2 := by push_cast; ring

/-- **The ternary circle method, explicit form.** For `3N < M`, `n < M`, `1 ≤ P`, `1 ≤ Q ≤ N`
with `2/(Q + 1) < 1/P²`, and the major arc approximation with error `E` for every `q ≤ P`:
`‖r₃(n) - J(n) 𝔖_P(n)‖ ≤ B ∑ Λ² + P² (2/(Q + 1) + 1/M) 3R² E (1 + 2πN/(Q + 1)) + N P² (Q + 1)/2`,
with `B = 300 (N/√P + N^{4/5} + √(NQ))(1 + log N)⁴` and `R = (log 4 + 4) N`. -/
theorem ternary_explicit {N M P Q n : ℕ} [NeZero M] (h3 : 3 * N < M) (hn : n < M) (hP : 1 ≤ P)
    (hQ : 1 ≤ Q) (hQN : Q ≤ N) (hPQ : 2 / ((Q : ℝ) + 1) < 1 / (P : ℝ) ^ 2) {E : ℝ} (hE : 0 ≤ E)
    (hmaj : ∀ q ∈ Icc 1 P, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S N (a' / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤ E * (1 + 2 * π * |β| * N)) :
    ‖(r3 N n : ℂ) - (J N n : ℂ) * singP P n‖ ≤
      300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
          (1 + Real.log N) ^ 4 * ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2
        + (P : ℝ) ^ 2 * (2 / ((Q : ℝ) + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * N) ^ 2 *
          (E * (1 + 2 * π * N / (Q + 1))))
        + N * (P : ℝ) ^ 2 * (Q + 1) / 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  set R := (Real.log 4 + 4) * N with hR
  set E' := E * (1 + 2 * π * N / (Q + 1)) with hE'
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hQ1 : (1 : ℝ) ≤ Q + 1 := by have : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q; linarith
  -- minor arcs
  have hmin := r3_minor (P := P) (Q := Q) h3 hP hQ hQN hn
  -- major arcs as a union of arcs
  have hnm := nonminor_eq (M := M) (P := P) (Q := Q)
  rw [hnm, sum_biUnion (arcs_disjoint hPQ)] at hmin
  -- each arc
  have harc : ∀ p ∈ majIdx P,
      ‖∑ k ∈ arcSet M Q p.1 p.2, (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
        ((μ p.1 : ℂ) / p.1.totient) ^ 3 * e (n * ((p.2 : ℝ) / p.1)) * ((M : ℂ) * (J N n : ℂ))‖ ≤
      (2 * M / ((Q : ℝ) + 1) + 1) * (3 * R ^ 2 * E') +
        1 / (p.1.totient : ℝ) * ((M : ℝ) * N * (p.1 * (Q + 1)) / 2) := by
    intro p hp
    have hp' := hp
    simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range] at hp'
    have hq1 : 1 ≤ p.1 := hp'.1.1.1
    have hqr : (1 : ℝ) ≤ p.1 := by exact_mod_cast hq1
    have h1 := arc_sum (Q := Q) (n := n) h3 hn hq1 hp'.2.2 (hmaj p.1 (mem_Icc.2 hp'.1.1))
    refine h1.trans (add_le_add ?_ le_rfl)
    have hcard := card_arc_le (M := M) ((p.2 : ℝ) / p.1) (δ := 1 / ((p.1 : ℝ) * (Q + 1)))
      (by positivity)
    have hc' : ((arcSet M Q p.1 p.2).card : ℝ) ≤ 2 * M / ((Q : ℝ) + 1) + 1 := by
      refine hcard.trans ?_
      have : 2 * (1 / ((p.1 : ℝ) * (Q + 1))) * M ≤ 2 * M / ((Q : ℝ) + 1) := by
        rw [div_eq_mul_one_div (2 * (M : ℝ))]
        have : 1 / ((p.1 : ℝ) * (Q + 1)) ≤ 1 / ((Q : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
        nlinarith
      linarith
    have hE'' : E * (1 + 2 * π * N / (p.1 * (Q + 1))) ≤ E' := by
      apply mul_le_mul_of_nonneg_left _ hE
      have : 2 * π * N / ((p.1 : ℝ) * (Q + 1)) ≤ 2 * π * N / (Q + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      linarith
    exact mul_le_mul hc' (mul_le_mul_of_nonneg_left hE'' (by positivity)) (by positivity)
      (by positivity)
  -- combine the arcs
  have hsumarc : ‖∑ p ∈ majIdx P, ∑ k ∈ arcSet M Q p.1 p.2,
        (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
        (M : ℂ) * ((J N n : ℂ) * singP P n)‖ ≤
      (P : ℝ) ^ 2 * ((2 * M / ((Q : ℝ) + 1) + 1) * (3 * R ^ 2 * E')) +
        M * N * (P : ℝ) ^ 2 * (Q + 1) / 2 := by
    have e1 : (M : ℂ) * ((J N n : ℂ) * singP P n) = ∑ p ∈ majIdx P,
        ((μ p.1 : ℂ) / p.1.totient) ^ 3 * e (n * ((p.2 : ℝ) / p.1)) * ((M : ℂ) * (J N n : ℂ)) := by
      unfold singP; rw [mul_sum, mul_sum]; refine sum_congr rfl fun p _ => ?_; ring
    rw [e1, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((sum_le_sum harc).trans ?_)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    have h2 : ∑ p ∈ majIdx P, 1 / (p.1.totient : ℝ) * ((M : ℝ) * N * (p.1 * (Q + 1)) / 2) ≤
        M * N * (P : ℝ) ^ 2 * (Q + 1) / 2 := by
      have := sum_majIdx P (fun q => 1 / (q.totient : ℝ) * ((M : ℝ) * N * (q * (Q + 1)) / 2))
      rw [this]
      have hs : ∑ q ∈ Icc 1 P, (q : ℝ) ≤ (P : ℝ) * P := by
        calc ∑ q ∈ Icc 1 P, (q : ℝ) ≤ ∑ q ∈ Icc 1 P, (P : ℝ) :=
              sum_le_sum fun q hq => by exact_mod_cast (mem_Icc.1 hq).2
          _ = P * P := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      calc ∑ q ∈ Icc 1 P, (q.totient : ℝ) * (1 / (q.totient : ℝ) * ((M : ℝ) * N * (q * (Q + 1)) / 2))
          = ∑ q ∈ Icc 1 P, (q : ℝ) * ((M : ℝ) * N * (Q + 1) / 2) := by
            refine sum_congr rfl fun q hq => ?_
            have : (q.totient : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.totient_pos.2 (by rw [mem_Icc] at hq; omega)).ne'
            field_simp
        _ = (∑ q ∈ Icc 1 P, (q : ℝ)) * ((M : ℝ) * N * (Q + 1) / 2) := by rw [sum_mul]
        _ ≤ ((P : ℝ) * P) * ((M : ℝ) * N * (Q + 1) / 2) :=
            mul_le_mul_of_nonneg_right hs (by positivity)
        _ = M * N * (P : ℝ) ^ 2 * (Q + 1) / 2 := by ring
    have hE'0 : 0 ≤ E' := by rw [hE']; positivity
    have h3' : ((majIdx P).card : ℝ) * ((2 * M / ((Q : ℝ) + 1) + 1) * (3 * R ^ 2 * E')) ≤
        (P : ℝ) ^ 2 * ((2 * M / ((Q : ℝ) + 1) + 1) * (3 * R ^ 2 * E')) :=
      mul_le_mul_of_nonneg_right (card_majIdx_le P) (by positivity)
    linarith
  -- assemble
  have htot : ‖(M : ℂ) * ((r3 N n : ℂ) - (J N n : ℂ) * singP P n)‖ ≤
      300 * ((N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * Q)) *
          (1 + Real.log N) ^ 4 * ((M : ℝ) * ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ^ 2) +
        ((P : ℝ) ^ 2 * ((2 * M / ((Q : ℝ) + 1) + 1) * (3 * R ^ 2 * E')) +
          M * N * (P : ℝ) ^ 2 * (Q + 1) / 2) := by
    have : (M : ℂ) * ((r3 N n : ℂ) - (J N n : ℂ) * singP P n) =
        ((M : ℂ) * (r3 N n : ℂ) - ∑ p ∈ majIdx P, ∑ k ∈ arcSet M Q p.1 p.2,
          (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ)) +
        (∑ p ∈ majIdx P, ∑ k ∈ arcSet M Q p.1 p.2,
          (𝓕 (PhiL N M) k) ^ 3 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
          (M : ℂ) * ((J N n : ℂ) * singP P n)) := by ring
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add hmin hsumarc)
  rw [norm_mul, Complex.norm_natCast] at htot
  rw [← le_div_iff₀' hMpos] at htot
  refine htot.trans (le_of_eq ?_)
  field_simp
  ring

end LeanLab.PNTPort.Vinogradov

