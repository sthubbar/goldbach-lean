module

public import LeanLab.RieselVaughan1983.Lemma10Sum
public import LeanLab.RieselVaughan1983.Page65

/-!
P0032 Riesel-Vaughan 1983, Lemma 13 support, unit U-6712, T1. Session 20261020T1816Z-cloud48.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Elementary replacement for the cited Montgomery-Vaughan input `Page65.MVLemma38`, with a weaker
additive constant, as planned in SCOPE_LS_U6710.md. KNOWN mathematics, classical:
`μ(m)²/φ(m) = Σ_{rad n = m} 1/n` gives `Σ_{m ≤ X} μ(m)²/φ(m) ≥ Σ_{n ≤ X} 1/n ≥ log X`, and
(8.14) `r/φ(r) = Σ_{d ∣ r} μ(d)²/φ(d)` removes the coprimality condition.

PROVED unconditional:
* `sum_divisors_inv_le`: `Σ_{k ∣ n} 1/k ≤ Π_{p ∣ n} p/(p - 1) = n/φ(n)` for `n ≠ 0`.
* `fiber_le`: for squarefree `m`, `Σ_{n ≤ N, rad n = m} V(n)/n ≤ μ(m)²/φ(m) · V(m)`, `V` antitone.
* `weighted_harmonic_le`: `Σ_{n ≤ N} V(n)/n ≤ Σ_{m ≤ N} μ(m)²/φ(m) V(m)`.
* `weighted_coprime_le`: `Σ_{n ≤ N} μ(n)²/φ(n) V(n) ≤ r/φ(r) Σ_{m ≤ N, (m, r) = 1} μ(m)²/φ(m) V(m)`.
* `log_le_mu_phi_sum`: for `r ≥ 1`, `X ≥ 0`, `log X ≤ r/φ(r) Σ_{m ≤ X, (m, r) = 1} μ(m)²/φ(m)`,
  the bound with additive constant `a = 0`.
* `log_sub_log_two_le_mSum`: the weighted sum of (8.18), `r ≥ 1`, `z > 0`:
  `log(z/r) - log 2 ≤ r/φ(r) · mSum r z`, i.e. `MVLemma38` with `0.361` replaced by `-log 2`.
* `mvLemma38_weak`: that bound in exactly the range and shape of `Page65.MVLemma38`.
-/

@[expose] public section

open Finset Real ArithmeticFunction UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section
namespace LeanLab.RieselVaughan1983.MuPhi

open LeanLab.RieselVaughan1983.Page65 LeanLab.RieselVaughan1983.Xi LeanLab.RieselVaughan1983.Lemma13Red

/-- `b(n) = μ(n)²/φ(n)`. -/
def b (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ)

lemma b_nonneg (n : ℕ) : 0 ≤ b n := by unfold b; positivity

lemma b_mul {m n : ℕ} (h : m.Coprime n) : b (m * n) = b m * b n := by
  unfold b
  rw [isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  rw [mul_pow, mul_div_mul_comm]

lemma b_of_squarefree {m : ℕ} (hm : Squarefree m) : b m = 1 / (m.totient : ℝ) := by
  unfold b
  rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree hm, Int.cast_one]

lemma b_of_not_squarefree {m : ℕ} (hm : ¬ Squarefree m) : b m = 0 := by
  unfold b
  rw [moebius_eq_zero_of_not_squarefree hm]
  simp

/-- Euler's product: `m/φ(m) = Π_{p ∣ m} p/(p - 1)`. -/
lemma div_totient_eq_prod (m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) / m.totient = ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors m
  have h' : (m.totient : ℝ) * ∏ p ∈ m.primeFactors, (p : ℝ) =
      (m : ℝ) * ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hm)
  have hP : (0 : ℝ) < ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := prod_pos fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hP.ne']
  linarith [h']

lemma sum_inv_prime_pow_le (p e : ℕ) (hp : p.Prime) :
    ∑ i ∈ range (e + 1), ((p : ℝ) ^ i)⁻¹ ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := e + 1) hx0 hx1
  rw [← range_eq_Ico] at h
  simp only [inv_pow, pow_zero] at h
  calc _ ≤ 1 / (1 - (p : ℝ)⁻¹) := h
    _ = (p : ℝ) / ((p : ℝ) - 1) := by
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp

/-- `n ↦ 1/n` as a real arithmetic function. -/
def w : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

lemma w_apply (n : ℕ) : w n = (n : ℝ)⁻¹ := rfl

lemma w_mult : w.IsMultiplicative :=
  ⟨by simp [w_apply], fun {m n} _ => by rw [w_apply, w_apply, w_apply, Nat.cast_mul, mul_inv]⟩

/-- `Σ_{k ∣ n} 1/k ≤ Π_{p ∣ n} p/(p - 1)` for `n ≠ 0`. -/
theorem sum_divisors_inv_le (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ n.divisors, (k : ℝ)⁻¹ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hm : ((ζ : ArithmeticFunction ℝ) * w).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul w_mult
  have h1 : ((ζ : ArithmeticFunction ℝ) * w) n = ∑ k ∈ n.divisors, (k : ℝ)⁻¹ := by
    rw [coe_zeta_mul_apply]; rfl
  rw [← h1, hm.multiplicative_factorization _ hn, Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_le_prod₀
  · intro p _
    rw [coe_zeta_mul_apply]
    exact sum_nonneg fun k _ => by rw [w_apply]; positivity
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp]
    simpa [w_apply] using sum_inv_prime_pow_le p (n.factorization p) hpp

/-- The fiber of the radical over a squarefree `m`. -/
theorem fiber_le (N m : ℕ) (hm : Squarefree m) (V : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n)
    (hVa : ∀ a c, 1 ≤ a → a ≤ c → V c ≤ V a) :
    ∑ n ∈ (Icc 1 N).filter (fun n => radical n = m), V n / n ≤ b m * V m := by
  set F := (Icc 1 N).filter (fun n => radical n = m) with hF
  have hm0 : m ≠ 0 := hm.ne_zero
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
  have hbm := b_nonneg m
  have hVm := hV0 m
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [F]; positivity
  have hmem : ∀ n ∈ F, 1 ≤ n ∧ n ≤ N ∧ m ∣ n ∧ n ∣ m ^ N := by
    intro n hn
    simp only [F, mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    refine ⟨h1, h2, h3 ▸ radical_dvd_self, ?_⟩
    have := Nat.dvd_radical_pow_self (n := n) (by omega)
    rw [h3] at this
    exact this.trans (pow_dvd_pow m h2)
  have s1 : ∑ n ∈ F, V n / n ≤ ∑ n ∈ F, V m * ((m : ℝ)⁻¹ * ((n / m : ℕ) : ℝ)⁻¹) := by
    apply sum_le_sum
    intro n hn
    obtain ⟨h1, -, hmn, -⟩ := hmem n hn
    have hle : m ≤ n := Nat.le_of_dvd h1 hmn
    have hn' : (n : ℝ) = m * ((n / m : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hmn]
    rw [hn', div_eq_mul_inv, mul_inv]
    have : 0 ≤ (m : ℝ)⁻¹ * ((n / m : ℕ) : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (hVa m n hm1 hle) this
  have s2 : ∑ n ∈ F, ((n / m : ℕ) : ℝ)⁻¹ ≤ ∑ k ∈ (m ^ N).divisors, (k : ℝ)⁻¹ := by
    have hinj : Set.InjOn (fun n => n / m) (F : Set ℕ) := by
      intro x hx y hy hxy
      obtain ⟨-, -, hx', -⟩ := hmem x hx
      obtain ⟨-, -, hy', -⟩ := hmem y hy
      exact (Nat.div_left_inj hx' hy').1 hxy
    rw [← sum_image (f := fun k : ℕ => (k : ℝ)⁻¹) (g := fun n => n / m) hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [mem_image] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      obtain ⟨-, -, hmn, hnN⟩ := hmem n hn
      rw [Nat.mem_divisors]
      exact ⟨(Nat.div_dvd_of_dvd hmn).trans hnN, pow_ne_zero _ hm0⟩
    · intro k _ _; positivity
  have s3 := sum_divisors_inv_le (m ^ N) (pow_ne_zero _ hm0)
  rw [Nat.primeFactors_pow _ (by omega : N ≠ 0), ← div_totient_eq_prod m hm0] at s3
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hb : b m = (m : ℝ)⁻¹ * ((m : ℝ) / m.totient) := by
    rw [b_of_squarefree hm]; field_simp
  calc ∑ n ∈ F, V n / n ≤ ∑ n ∈ F, V m * ((m : ℝ)⁻¹ * ((n / m : ℕ) : ℝ)⁻¹) := s1
    _ = V m * ((m : ℝ)⁻¹ * ∑ n ∈ F, ((n / m : ℕ) : ℝ)⁻¹) := by rw [mul_sum, mul_sum]
    _ ≤ V m * ((m : ℝ)⁻¹ * ((m : ℝ) / m.totient)) := by
      gcongr; exact s2.trans s3
    _ = b m * V m := by rw [hb]; ring

/-- `Σ_{n ≤ N} V(n)/n ≤ Σ_{m ≤ N} μ(m)²/φ(m) V(m)` for `V ≥ 0` antitone on `n ≥ 1`. -/
theorem weighted_harmonic_le (N : ℕ) (V : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n)
    (hVa : ∀ a c, 1 ≤ a → a ≤ c → V c ≤ V a) :
    ∑ n ∈ Icc 1 N, V n / n ≤ ∑ m ∈ Icc 1 N, b m * V m := by
  have hmaps : ∀ n ∈ Icc 1 N, radical n ∈ Icc 1 N := by
    intro n hn
    simp only [mem_Icc] at hn ⊢
    have h1 := Nat.radical_le_self_iff.2 (by omega : n ≠ 0)
    have h2 := Nat.radical_pos n
    omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_le_sum
  intro m _
  by_cases hsq : Squarefree m
  · exact fiber_le N m hsq V hV0 hVa
  · have : (Icc 1 N).filter (fun n => radical n = m) = ∅ := by
      apply filter_eq_empty_iff.2
      intro n _ h
      exact hsq (h ▸ squarefree_radical)
    rw [this, sum_empty]
    exact mul_nonneg (b_nonneg m) (hV0 m)

/-- Removing the coprimality condition with (8.14). -/
theorem weighted_coprime_le (r : ℕ) (hr : 1 ≤ r) (N : ℕ) (V : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n)
    (hVa : ∀ a c, 1 ≤ a → a ≤ c → V c ≤ V a) :
    ∑ n ∈ Icc 1 N, b n * V n ≤
      (r : ℝ) / r.totient * ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime r), b m * V m := by
  set M := (Icc 1 N).filter (fun m => m.Coprime r) with hM
  set S := (Icc 1 N).filter Squarefree with hS
  have h814 : (r : ℝ) / r.totient = ∑ d ∈ r.divisors, b d := by
    rw [← L10.sum_divisors_sq_moebius_div_totient]; rfl
  have hR : (r : ℝ) / r.totient * ∑ m ∈ M, b m * V m =
      ∑ q ∈ r.divisors ×ˢ M, b q.1 * b q.2 * V q.2 := by
    rw [h814, sum_mul, sum_product]
    apply sum_congr rfl; intro d _
    rw [mul_sum]; apply sum_congr rfl; intro m _; ring
  have hL : ∑ n ∈ Icc 1 N, b n * V n = ∑ n ∈ S, b n * V n := by
    rw [hS, sum_filter_of_ne]
    intro n _ hne
    by_contra hsq
    exact hne (by rw [b_of_not_squarefree hsq, zero_mul])
  set f : ℕ → ℕ × ℕ := fun n => (Nat.gcd n r, n / Nat.gcd n r) with hf
  have key : ∀ n ∈ S, f n ∈ r.divisors ×ˢ M ∧ b n * V n ≤ b (f n).1 * b (f n).2 * V (f n).2 := by
    intro n hn
    simp only [hS, mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, hsq⟩ := hn
    set d := Nat.gcd n r with hd
    set m := n / d with hmdef
    have hdn : d ∣ n := Nat.gcd_dvd_left n r
    have hnd : n = d * m := (Nat.mul_div_cancel' hdn).symm
    have hcop : d.Coprime m := Nat.coprime_of_squarefree_mul (hnd ▸ hsq)
    have hmn : m ∣ n := Nat.div_dvd_of_dvd hdn
    have hm1 : 1 ≤ m :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (Nat.gcd_pos_of_pos_left r (by omega))
    have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmn
    have hmr : m.Coprime r := by
      have hg1 : Nat.gcd m r ∣ d := Nat.gcd_dvd_gcd_of_dvd_left r hmn
      have hg2 : Nat.gcd m r ∣ Nat.gcd d m := Nat.dvd_gcd hg1 (Nat.gcd_dvd_left m r)
      rw [hcop] at hg2
      exact Nat.eq_one_of_dvd_one hg2
    refine ⟨?_, ?_⟩
    · simp only [hf, mem_product, Nat.mem_divisors, hM, mem_filter, mem_Icc]
      exact ⟨⟨Nat.gcd_dvd_right n r, by omega⟩, ⟨hm1, hmle.trans h2⟩, hmr⟩
    · simp only [hf]
      rw [← b_mul hcop, ← hnd]
      exact mul_le_mul_of_nonneg_left (hVa m n hm1 hmle) (b_nonneg n)
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro x _ y _ hxy
    simp only [hf, Prod.mk.injEq] at hxy
    calc x = Nat.gcd x r * (x / Nat.gcd x r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x r)).symm
      _ = Nat.gcd y r * (y / Nat.gcd y r) := by rw [hxy.2, hxy.1]
      _ = y := Nat.mul_div_cancel' (Nat.gcd_dvd_left y r)
  rw [hL, hR]
  calc ∑ n ∈ S, b n * V n ≤ ∑ n ∈ S, b (f n).1 * b (f n).2 * V (f n).2 :=
        sum_le_sum fun n hn => (key n hn).2
    _ = ∑ q ∈ S.image f, b q.1 * b q.2 * V q.2 := by rw [sum_image hinj]
    _ ≤ ∑ q ∈ r.divisors ×ˢ M, b q.1 * b q.2 * V q.2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        simp only [mem_image] at hq
        obtain ⟨n, hn, rfl⟩ := hq
        exact (key n hn).1
      · intro q _ _
        exact mul_nonneg (mul_nonneg (b_nonneg _) (b_nonneg _)) (hV0 _)

lemma log_le_sum_inv (X : ℝ) (hX : 0 ≤ X) : Real.log X ≤ ∑ n ∈ Icc 1 ⌊X⌋₊, 1 / (n : ℝ) := by
  have h := log_le_harmonic_floor X hX
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- **The unweighted bound, additive constant `a = 0`**: for `r ≥ 1` and `X ≥ 0`,
`log X ≤ r/φ(r) Σ_{m ≤ X, (m, r) = 1} μ(m)²/φ(m)`. -/
theorem log_le_mu_phi_sum (r : ℕ) (hr : 1 ≤ r) (X : ℝ) (hX : 0 ≤ X) :
    Real.log X ≤ (r : ℝ) / r.totient *
      ∑ m ∈ (Icc 1 ⌊X⌋₊).filter (fun m => m.Coprime r), ((μ m : ℤ) : ℝ) ^ 2 / (m.totient : ℝ) := by
  have h1 := weighted_harmonic_le ⌊X⌋₊ (fun _ => 1) (fun _ => zero_le_one) (fun _ _ _ _ => le_rfl)
  have h2 := weighted_coprime_le r hr ⌊X⌋₊ (fun _ => 1) (fun _ => zero_le_one)
    (fun _ _ _ _ => le_rfl)
  simp only [mul_one] at h1 h2
  exact (log_le_sum_inv X hX).trans (h1.trans h2)

/-- `1/t ≤ log t - log (t - 1)` for `t > 1`. -/
lemma inv_le_log_sub_real {t : ℝ} (ht : 1 < t) :
    1 / t ≤ Real.log t - Real.log (t - 1) := by
  have hpos : 0 < t - 1 := by linarith
  rw [← Real.log_div (by linarith) hpos.ne']
  have := Real.one_sub_inv_le_log_of_pos (x := t / (t - 1)) (by positivity)
  rw [inv_div] at this
  calc 1 / t = 1 - (t - 1) / t := by field_simp; ring
    _ ≤ _ := this

lemma sum_inv_shift_le (X : ℝ) (hX : 0 < X) (N : ℕ) :
    ∑ n ∈ Icc 1 N, 1 / ((n : ℝ) + X) ≤ Real.log (N + X) - Real.log X := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have ht : 1 < ((N + 1 : ℕ) : ℝ) + X := by push_cast; linarith
    have h := inv_le_log_sub_real ht
    have he : ((N + 1 : ℕ) : ℝ) + X - 1 = (N : ℝ) + X := by push_cast; ring
    rw [he] at h
    linarith

/-- **The weighted sum of (8.18)**: for `r ≥ 1` and `z > 0`,
`log(z/r) - log 2 ≤ r/φ(r) Σ_{m ≤ z/r, (m, r) = 1} μ(m)²/φ(m) · 1/(1 + rm/z)`. -/
theorem log_sub_log_two_le_mSum (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : 0 < z) :
    Real.log (z / r) - Real.log 2 ≤ (r : ℝ) / r.totient * mSum r z := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set X := z / r with hXdef
  have hX : 0 < X := by positivity
  set N := ⌊X⌋₊ with hN
  set V : ℕ → ℝ := fun m => 1 / (1 + r * m * z⁻¹) with hV
  have hVeq : ∀ m : ℕ, V m = X / (X + m) := by
    intro m
    simp only [hV, hXdef]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    field_simp
  have hV0 : ∀ n, 0 ≤ V n := fun n => by rw [hVeq]; positivity
  have hVa : ∀ a c, 1 ≤ a → a ≤ c → V c ≤ V a := by
    intro a c _ hac
    rw [hVeq, hVeq]
    have : (a : ℝ) ≤ c := by exact_mod_cast hac
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    gcongr
  have h1 := weighted_harmonic_le N V hV0 hVa
  have h2 := weighted_coprime_le r hr N V hV0 hVa
  have hm : mSum r z = ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime r), b m * V m := by
    unfold mSum; rfl
  -- `V(n)/n = 1/n - 1/(n + X)`
  have hsplit : ∑ n ∈ Icc 1 N, V n / n =
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) - ∑ n ∈ Icc 1 N, 1 / ((n : ℝ) + X) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [hVeq]
    field_simp
    ring
  have h3 := log_le_sum_inv X hX.le
  have h4 := sum_inv_shift_le X hX N
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX.le
  have h5 : Real.log ((N : ℝ) + X) ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul (by norm_num) hX.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hm]
  linarith

/-- **`MVLemma38` with `0.361` replaced by `-log 2`**, in the exact range and shape of
`Page65.MVLemma38`, PROVED. -/
theorem mvLemma38_weak :
    ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ wk (x / 202) k →
        -Real.log 2 + Real.log (zk (x / 202) k / r) ≤
          (r : ℝ) / r.totient * mSum r (zk (x / 202) k) := by
  intro x hx hL k _ r hr _
  have hy7 : 10 ^ 7 ≤ x / 202 := y_big (by positivity) hL
  obtain ⟨hz, _, _⟩ := z_facts (k := k) hy7
  have := log_sub_log_two_le_mSum r hr _ hz
  linarith

end LeanLab.RieselVaughan1983.MuPhi
