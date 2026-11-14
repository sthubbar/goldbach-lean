module

public import LeanLab.Linnik.ExplicitFormula.Defs

/-!
# From `n χ(n) Λ(n)` to `χ(p)`, Gallagher 1975 p.130

AI wrote the Lean code. Binary Goldbach is OPEN.
Partial summation with the decreasing weight `g(n) = 1/(n log n)`: on primes `b(p) g(p) = χ(p)`,
`n g(n) = 1/log n`, `n^γ g(n) = n^(γ-1)/log n`, and the prime powers `p^k`, `k ≥ 2`, cost at most
`2 √a log a`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- Abel summation with a decreasing positive weight: if every partial window sum of `f` is
at most `M`, then `‖Σ_{b < n ≤ a} f(n) g(n)‖ ≤ M g(b + 1)`. -/
theorem abel_window_le (f : ℕ → ℂ) (g : ℕ → ℝ) {a b : ℕ} (hba : b ≤ a)
    (hg : ∀ n m, b < n → n ≤ m → g m ≤ g n) (hg0 : ∀ n, b < n → 0 ≤ g n) {M : ℝ}
    (hM : ∀ u ∈ Icc b a, ‖∑ n ∈ Ioc b u, f n‖ ≤ M) :
    ‖∑ n ∈ Ioc b a, f n * (g n : ℂ)‖ ≤ M * g (b + 1) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM b (mem_Icc.2 ⟨le_rfl, hba⟩))
  have key : ∀ k, b + k ≤ a →
      ‖(∑ n ∈ Ioc b (b + k), f n * (g n : ℂ)) - (∑ n ∈ Ioc b (b + k), f n) * (g (b + k + 1) : ℂ)‖
        ≤ M * (g (b + 1) - g (b + k + 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hSb : ‖∑ n ∈ Ioc b (b + k + 1), f n‖ ≤ M := hM _ (mem_Icc.2 ⟨by omega, by omega⟩)
      have hgm : g (b + k + 1 + 1) ≤ g (b + k + 1) := hg _ _ (by omega) (by omega)
      have hT : ∑ n ∈ Ioc b (b + k + 1), f n * (g n : ℂ)
          = ∑ n ∈ Ioc b (b + k), f n * (g n : ℂ) + f (b + k + 1) * (g (b + k + 1) : ℂ) :=
        Finset.sum_Ioc_succ_top (by omega) _
      have hS : ∑ n ∈ Ioc b (b + k + 1), f n
          = ∑ n ∈ Ioc b (b + k), f n + f (b + k + 1) :=
        Finset.sum_Ioc_succ_top (by omega) _
      have eq : (∑ n ∈ Ioc b (b + (k + 1)), f n * (g n : ℂ)) -
          (∑ n ∈ Ioc b (b + (k + 1)), f n) * (g (b + (k + 1) + 1) : ℂ)
          = ((∑ n ∈ Ioc b (b + k), f n * (g n : ℂ)) -
              (∑ n ∈ Ioc b (b + k), f n) * (g (b + k + 1) : ℂ)) +
            (∑ n ∈ Ioc b (b + k + 1), f n) * ((g (b + k + 1) - g (b + k + 1 + 1) : ℝ) : ℂ) := by
        rw [show b + (k + 1) = b + k + 1 by ring, hT]
        conv_lhs => rw [hS]
        rw [hS]; push_cast; ring
      rw [eq]
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ M * (g (b + 1) - g (b + k + 1)) + M * (g (b + k + 1) - g (b + k + 1 + 1)) := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          exact mul_le_mul_of_nonneg_right hSb (by linarith)
        _ = M * (g (b + 1) - g (b + (k + 1) + 1)) := by ring_nf
  have hk := key (a - b) (by omega)
  rw [show b + (a - b) = a by omega] at hk
  have hSa : ‖∑ n ∈ Ioc b a, f n‖ ≤ M := hM a (mem_Icc.2 ⟨hba, le_rfl⟩)
  have hga : 0 ≤ g (a + 1) := hg0 _ (by omega)
  calc ‖∑ n ∈ Ioc b a, f n * (g n : ℂ)‖
      ≤ ‖(∑ n ∈ Ioc b a, f n * (g n : ℂ)) - (∑ n ∈ Ioc b a, f n) * (g (a + 1) : ℂ)‖ +
        ‖(∑ n ∈ Ioc b a, f n) * (g (a + 1) : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ M * (g (b + 1) - g (a + 1)) + M * g (a + 1) := by
        gcongr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hga]
        exact mul_le_mul_of_nonneg_right hSa hga
    _ = M * g (b + 1) := by ring

/-- Prime powers `p^k ≤ a` with `k ≥ 2` number at most `√a log a / log 2`... in the
form used here: at most `2 √a log a` for `a ≥ 2`. -/
theorem prime_power_count_le {a : ℕ} (ha : 2 ≤ a) :
    ((Finset.Icc 1 a).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card ≤
      2 * Real.sqrt a * Real.log a := by
  set s := (Finset.Icc 1 a).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hs
  have hmem : ∀ n ∈ s, IsPrimePow n ∧ ¬ n.Prime ∧ n ≤ a := by
    intro n hn
    simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hn.2.1, hn.2.2, hn.1.2⟩
  have hmaps : ∀ n ∈ s, (n.minFac, n.factorization n.minFac) ∈
      Finset.Icc 1 (Nat.sqrt a) ×ˢ Finset.Icc 1 (Nat.log 2 a) := by
    intro n hn
    obtain ⟨hpp, hnp, hna⟩ := hmem n hn
    have hp : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
    have heq := hpp.minFac_pow_factorization_eq
    set k := n.factorization n.minFac
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, pow_zero] at heq; exact hpp.ne_one heq.symm
    have hk1 : k ≠ 1 := by
      intro h1; rw [h1, pow_one] at heq; exact hnp (heq ▸ hp)
    have hk2 : 2 ≤ k := by omega
    have hpk : n.minFac ^ 2 ≤ n :=
      calc n.minFac ^ 2 ≤ n.minFac ^ k := Nat.pow_le_pow_right hp.pos hk2
        _ = n := heq
    have h2k : 2 ^ k ≤ n :=
      calc 2 ^ k ≤ n.minFac ^ k := Nat.pow_le_pow_left hp.two_le k
        _ = n := heq
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨hp.pos, Nat.le_sqrt.2 (by nlinarith)⟩, ⟨by omega, ?_⟩⟩
    exact Nat.le_log_of_pow_le (by norm_num) (h2k.trans hna)
  have hinj : Set.InjOn (fun n => (n.minFac, n.factorization n.minFac)) (s : Set ℕ) := by
    intro n hn m hm hnm
    simp only [Prod.mk.injEq] at hnm
    rw [← (hmem n hn).1.minFac_pow_factorization_eq, ← (hmem m hm).1.minFac_pow_factorization_eq,
      hnm.2, hnm.1]
  have hcard : s.card ≤ Nat.sqrt a * Nat.log 2 a := by
    calc s.card ≤ (Finset.Icc 1 (Nat.sqrt a) ×ˢ Finset.Icc 1 (Nat.log 2 a)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = Nat.sqrt a * Nat.log 2 a := by simp
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL : (Nat.log 2 a : ℝ) ≤ 2 * Real.log a := by
    have hpow : ((2 : ℝ)) ^ Nat.log 2 a ≤ (a : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : a ≠ 0)
    have := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 a)]
  calc (s.card : ℝ) ≤ (Nat.sqrt a : ℝ) * (Nat.log 2 a : ℝ) := by exact_mod_cast hcard
    _ ≤ Real.sqrt a * (2 * Real.log a) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
    _ = 2 * Real.sqrt a * Real.log a := by ring

/-- Elementary: `1 / log n ≤ 3/2` for `n ≥ 2`, from `log 2 > 0.69`. -/
lemma one_div_log_le {n : ℕ} (hn : 1 < n) : 0 < Real.log n ∧ 1 / Real.log n ≤ 3 / 2 := by
  have h2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl := Real.log_two_gt_d9
  have hpos : 0 < Real.log n := by linarith
  refine ⟨hpos, ?_⟩
  rw [div_le_iff₀ hpos]; linarith

/-- Gallagher 1975 p.130, elementary: the corrected coefficient minus the weighted `b(n)` window
summand is `[n prime] χ(n) - χ(n) Λ(n)/log n`. -/
lemma corrCoef_sub_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℕ) (γ : ℝ) {n : ℕ}
    (hn : 1 < n) :
    corrCoef χ r γ n = (bCoef χ n - (if q = 1 then (n : ℂ) else 0) +
          (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then (((n : ℝ) ^ γ : ℝ) : ℂ) else 0)) *
        ((1 / ((n : ℝ) * Real.log n) : ℝ) : ℂ) +
      ((if n.Prime then χ n else 0) -
        χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog : Real.log n ≠ 0 := (one_div_log_le hn).1.ne'
  have hn0c : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hlogc : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hlog
  unfold corrCoef bCoef
  rw [if_pos hn, if_pos hn, Real.rpow_sub_one hn0]
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- Elementary: the error term `[n prime] χ(n) - χ(n) Λ(n)/log n` vanishes unless `n` is a proper
prime power, and has norm at most `1`. -/
lemma norm_err_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 < n) :
    ‖(if n.Prime then χ n else 0) -
        χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)‖ ≤
      if IsPrimePow n ∧ ¬ n.Prime then 1 else 0 := by
  have hlog : 0 < Real.log n := (one_div_log_le hn).1
  have hlogc : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  by_cases hp : n.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp, mul_div_assoc, div_self hlogc]
    simp [hp]
  · rw [if_neg hp, zero_sub, norm_neg]
    by_cases hpp : IsPrimePow n
    · rw [if_pos ⟨hpp, hp⟩, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.norm_of_nonneg hlog.le,
        div_le_one hlog]
      calc ‖χ n‖ * ArithmeticFunction.vonMangoldt n ≤ 1 * Real.log n := by
            gcongr
            · exact χ.norm_le_one _
            · exact ArithmeticFunction.vonMangoldt_le_log
        _ = Real.log n := one_mul _
    · rw [if_neg (fun h => hpp h.1),
        ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]
      simp

/-- Gallagher 1975 p.130: the corrected prime window from the `b(n)` windows. -/
theorem corrCoef_window_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℕ) (γ : ℝ)
    {a b : ℕ} (hb : 2 ≤ b) (hba : b ≤ a) {M : ℝ}
    (hM : ∀ u ∈ Icc b a, ‖∑ n ∈ Ioc b u, (bCoef χ n - (if q = 1 then (n : ℂ) else 0) +
          (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then (((n : ℝ) ^ γ : ℝ) : ℂ) else 0))‖ ≤ M) :
    ‖∑ n ∈ Ioc b a, corrCoef χ r γ n‖ ≤ M / (b * Real.log b) + 2 * Real.sqrt a * Real.log a := by
  set h : ℕ → ℂ := fun n => bCoef χ n - (if q = 1 then (n : ℂ) else 0) +
          (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then (((n : ℝ) ^ γ : ℝ) : ℂ) else 0) with hh
  set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log n) with hgdef
  set e : ℕ → ℂ := fun n => (if n.Prime then χ n else 0) -
        χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) with hedef
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM b (mem_Icc.2 ⟨le_rfl, hba⟩))
  have hpos : ∀ n : ℕ, 1 < n → 0 < (n : ℝ) * Real.log n := fun n hn =>
    mul_pos (by positivity) (one_div_log_le hn).1
  have hmono : ∀ n m : ℕ, 1 < n → n ≤ m → g m ≤ g n := by
    intro n m hn hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    simp only [hgdef]
    apply one_div_le_one_div_of_le (hpos n hn)
    exact mul_le_mul hnm' (Real.log_le_log (by positivity) hnm') (one_div_log_le hn).1.le
      (by positivity)
  have hg0 : ∀ n, b < n → 0 ≤ g n := fun n hn => by
    simp only [hgdef]; exact (one_div_pos.2 (hpos n (by omega))).le
  have habel : ‖∑ n ∈ Ioc b a, h n * (g n : ℂ)‖ ≤ M * g (b + 1) :=
    abel_window_le h g hba (fun n m hn hnm => hmono n m (by omega) hnm) hg0 hM
  have hgb : g (b + 1) ≤ 1 / ((b : ℝ) * Real.log b) := hmono b (b + 1) (by omega) (by omega)
  have hsplit : ∑ n ∈ Ioc b a, corrCoef χ r γ n =
      ∑ n ∈ Ioc b a, h n * (g n : ℂ) + ∑ n ∈ Ioc b a, e n := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [mem_Ioc] at hn
    exact corrCoef_sub_eq χ r γ (by omega)
  have he : ‖∑ n ∈ Ioc b a, e n‖ ≤ 2 * Real.sqrt a * Real.log a := by
    calc ‖∑ n ∈ Ioc b a, e n‖ ≤ ∑ n ∈ Ioc b a, ‖e n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc b a, (if IsPrimePow n ∧ ¬ n.Prime then (1 : ℝ) else 0) := by
          apply sum_le_sum
          intro n hn
          rw [mem_Ioc] at hn
          exact norm_err_le χ (by omega)
      _ = (((Ioc b a).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ) := by
          rw [Finset.sum_boole]
      _ ≤ (((Icc 1 a).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ) := by
          exact_mod_cast card_le_card (filter_subset_filter _ (fun n hn => by
            rw [mem_Ioc] at hn; rw [mem_Icc]; omega))
      _ ≤ 2 * Real.sqrt a * Real.log a := prime_power_count_le (by omega)
  rw [hsplit]
  calc _ ≤ ‖∑ n ∈ Ioc b a, h n * (g n : ℂ)‖ + ‖∑ n ∈ Ioc b a, e n‖ := norm_add_le _ _
    _ ≤ M * (1 / ((b : ℝ) * Real.log b)) + 2 * Real.sqrt a * Real.log a := by
        gcongr
        exact habel.trans (mul_le_mul_of_nonneg_left hgb hM0)
    _ = M / (b * Real.log b) + 2 * Real.sqrt a * Real.log a := by rw [mul_one_div]

/-- Trivial bound: `‖corrCoef χ r γ n‖ ≤ 4` when `γ ≤ 1`. -/
theorem norm_corrCoef_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℕ) {γ : ℝ}
    (hγ : γ ≤ 1) (n : ℕ) : ‖corrCoef χ r γ n‖ ≤ 4 := by
  have hχ : ‖(if n.Prime then χ n else 0)‖ ≤ 1 := by
    split_ifs
    · exact χ.norm_le_one _
    · simp
  have hB : ‖(if q = 1 then (if 1 < n then (1 / Real.log n : ℂ) else 0) else 0)‖ ≤ 3 / 2 := by
    split_ifs with h1 h2
    · obtain ⟨hl, hl'⟩ := one_div_log_le h2
      rw [show (1 / (Real.log n : ℂ)) = ((1 / Real.log n : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact hl'
    · norm_num
    · norm_num
  have hC : ‖(if q = r ∧ χ.LFunction (γ : ℂ) = 0 then
      (if 1 < n then (((n : ℝ) ^ (γ - 1) / Real.log n : ℝ) : ℂ) else 0) else 0)‖ ≤ 3 / 2 := by
    split_ifs with h1 h2
    · obtain ⟨hl, hl'⟩ := one_div_log_le h2
      have hr0 : 0 ≤ (n : ℝ) ^ (γ - 1) := by positivity
      have hr1 : (n : ℝ) ^ (γ - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h2.le) (by linarith)
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc (n : ℝ) ^ (γ - 1) / Real.log n ≤ 1 / Real.log n :=
            div_le_div_of_nonneg_right hr1 hl.le
        _ ≤ 3 / 2 := hl'
    · norm_num
    · norm_num
  unfold corrCoef
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ (_ + _) + _ := by gcongr; exact norm_sub_le _ _
    _ ≤ 1 + 3 / 2 + 3 / 2 := by gcongr
    _ ≤ 4 := by norm_num

end LeanLab.Linnik.ExplicitFormula
