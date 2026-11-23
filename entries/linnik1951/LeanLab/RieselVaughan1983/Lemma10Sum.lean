module

public import Mathlib

/-!
P0032 Riesel-Vaughan 1983, Lemma 10, page 63: the elementary core.
PC run 20261020T0503Z-11094, unit U-1170. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

* `sum_divisors_sq_moebius_div_totient`: (8.14), `Σ_{r ∣ d} μ(r)²/φ(r) = d/φ(d)` for `d ≥ 1`,
  equivalently `1/φ(d) = (1/d) Σ_{r ∣ d} μ(r)²/φ(r)`.
* `harmonic_window`: `Σ_{u < m ≤ v} 1/m ≤ 1 + log(v/u)` for `0 < u ≤ v`.
* `lemma10_sum`: the display of page 63,
  `Σ_{a < d ≤ b, d odd} μ(d)²/φ(d) ≤ Σ_{r ≤ b, r odd} μ(r)²/(r φ(r)) · (1 + log(b/a))`.
With `a = y/2`, `b = x/2`, `x = 202 y` by (7.1), and the odd sum below `A₁₀` of (2.25), this is
the bound `|Ξ_k| ≤ A₁₀ (1 + log 202) S_k` of Lemma 10 once `Σ_{d ∣ n} R_k(n) ≤ S_k` is supplied.
KNOWN mathematics.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section
namespace LeanLab.RieselVaughan1983.L10

/-- `g(n) = μ(n)²/φ(n)` as a real arithmetic function. -/
def g : ArithmeticFunction ℝ :=
  ⟨fun n => ((μ n : ℝ)) ^ 2 / (n.totient : ℝ), by simp⟩

lemma g_apply (n : ℕ) : g n = ((μ n : ℝ)) ^ 2 / (n.totient : ℝ) := rfl

lemma g_mult : g.IsMultiplicative := by
  refine ⟨by simp [g_apply], fun {m n} hmn => ?_⟩
  simp only [g_apply]
  rw [isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_pow, mul_div_mul_comm]

/-- `h(n) = n/φ(n)` as a real arithmetic function. -/
def h : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) / (n.totient : ℝ), by simp⟩

lemma h_apply (n : ℕ) : h n = (n : ℝ) / (n.totient : ℝ) := rfl

lemma h_mult : h.IsMultiplicative := by
  refine ⟨by simp [h_apply], fun {m n} hmn => ?_⟩
  simp only [h_apply]
  rw [Nat.totient_mul hmn]
  push_cast
  rw [mul_div_mul_comm]

lemma gz_mult : (g * (ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
  g_mult.mul isMultiplicative_zeta.natCast

lemma on_prime_pow (p k : ℕ) (hp : p.Prime) :
    (g * (ζ : ArithmeticFunction ℝ)) (p ^ k) = h (p ^ k) := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [g_apply, h_apply]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  -- only `j = 0, 1` contribute
  have hsum : ∑ j ∈ range (k + 1), g (p ^ j) = 1 + 1 / ((p : ℝ) - 1) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∑ j ∈ range k', g (p ^ (j + 1 + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [g_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp
    rw [hz, zero_add]
    simp only [zero_add, pow_one, pow_zero, g_apply]
    rw [moebius_apply_prime hp, Nat.totient_prime hp]
    simp [Nat.cast_sub hp.one_le]
    ring
  rw [hsum, h_apply, Nat.totient_prime_pow hp hk]
  push_cast
  rw [Nat.cast_sub hp.one_le]
  have hpk : (p : ℝ) ^ k = (p : ℝ) ^ (k - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [hpk]
  have hp0 : (p : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by linarith)
  push_cast
  rw [eq_div_iff (mul_ne_zero hp0 hpm1)]
  field_simp
  ring

/-- (8.14): `Σ_{r ∣ d} μ(r)²/φ(r) = d/φ(d)`. -/
theorem sum_divisors_sq_moebius_div_totient (d : ℕ) :
    ∑ r ∈ d.divisors, ((μ r : ℝ)) ^ 2 / (r.totient : ℝ) = (d : ℝ) / (d.totient : ℝ) := by
  have hEq : g * (ζ : ArithmeticFunction ℝ) = h :=
    (IsMultiplicative.eq_iff_eq_on_prime_powers _ gz_mult _ h_mult).2 (fun p i hp => on_prime_pow p i hp)
  have h1 : (g * (ζ : ArithmeticFunction ℝ)) d = h d := by rw [hEq]
  rw [coe_mul_zeta_apply] at h1
  simpa [g_apply, h_apply] using h1

/-- (8.14) in the paper's form `1/φ(d) = (1/d) Σ_{r ∣ d} μ(r)²/φ(r)`, `d ≥ 1`. -/
theorem inv_totient_eq (d : ℕ) (hd : 1 ≤ d) :
    1 / (d.totient : ℝ) = (1 / (d : ℝ)) * ∑ r ∈ d.divisors, ((μ r : ℝ)) ^ 2 / (r.totient : ℝ) := by
  rw [sum_divisors_sq_moebius_div_totient]
  have : (d : ℝ) ≠ 0 := by positivity
  field_simp


/-- `1/m ≤ log m - log (m - 1)` for `m ≥ 2`. -/
lemma inv_le_log_sub (m : ℕ) (hm : 2 ≤ m) :
    1 / (m : ℝ) ≤ Real.log m - Real.log ((m - 1 : ℕ) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m - 1)
  have hmr : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) < (m : ℝ) - 1 := by rw [← hmr]; linarith
  rw [← Real.log_div (by positivity) (by linarith), hmr]
  have := Real.one_sub_inv_le_log_of_pos (x := (m : ℝ) / ((m : ℝ) - 1)) (by positivity)
  rw [inv_div] at this
  have hm0 : (0 : ℝ) < m := by linarith
  calc 1 / (m : ℝ) = 1 - ((m : ℝ) - 1) / m := by field_simp; ring
    _ ≤ _ := this

/-- `Σ_{m₀ < m ≤ n} 1/m ≤ log n - log m₀` for `1 ≤ m₀`. -/
lemma sum_Ioc_inv_le (m0 n : ℕ) (h0 : 1 ≤ m0) (hn : m0 ≤ n) :
    ∑ m ∈ Ioc m0 n, 1 / (m : ℝ) ≤ Real.log n - Real.log m0 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have h1 := inv_le_log_sub (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    linarith

/-- `Σ_{u < m ≤ v} 1/m ≤ 1 + log(v/u)` for `0 < u ≤ v`, the window written `⌊u⌋ + 1 ≤ m ≤ ⌊v⌋`. -/
theorem harmonic_window {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∑ m ∈ Icc (⌊u⌋₊ + 1) ⌊v⌋₊, 1 / (m : ℝ) ≤ 1 + Real.log (v / u) := by
  have hlog0 : 0 ≤ Real.log (v / u) :=
    Real.log_nonneg (by rw [le_div_iff₀ hu]; linarith)
  set m0 := ⌊u⌋₊ + 1 with hm0
  set n := ⌊v⌋₊ with hn
  rcases Nat.lt_or_ge n m0 with hlt | hle
  · rw [Finset.Icc_eq_empty (by omega), sum_empty]; linarith
  rw [Finset.Icc_eq_cons_Ioc hle, Finset.sum_cons]
  have hm1 : 1 ≤ m0 := by omega
  have h1 := sum_Ioc_inv_le m0 n hm1 hle
  have hm0r : (1 : ℝ) ≤ m0 := by exact_mod_cast hm1
  have hinv : 1 / (m0 : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hm0r
  have hum : u < (m0 : ℝ) := by rw [hm0]; push_cast; exact Nat.lt_floor_add_one u
  have hnv : (n : ℝ) ≤ v := Nat.floor_le (by linarith)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans hm1 hle)
  have hlogn : Real.log n ≤ Real.log v := Real.log_le_log (by linarith) hnv
  have hlogm : Real.log u ≤ Real.log m0 := Real.log_le_log hu hum.le
  rw [Real.log_div (by linarith) hu.ne']
  linarith

/-- **Lemma 10, the sum on page 63**: for `0 < a ≤ b`,
`Σ_{a < d ≤ b, d odd} μ(d)²/φ(d) ≤ (Σ_{r ≤ b, r odd} μ(r)²/(r φ(r))) (1 + log(b/a))`. -/
theorem lemma10_sum {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ d ∈ (Icc (⌊a⌋₊ + 1) ⌊b⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ≤
      (∑ r ∈ (Icc 1 ⌊b⌋₊).filter Odd, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ))) *
        (1 + Real.log (b / a)) := by
  set D := (Icc (⌊a⌋₊ + 1) ⌊b⌋₊).filter Odd with hD
  set R := (Icc 1 ⌊b⌋₊).filter Odd with hR
  set G : ℕ → ℝ := fun r => ((μ r : ℝ)) ^ 2 / (r.totient : ℝ) with hG
  have hGnn : ∀ r, 0 ≤ G r := fun r => by simp only [hG]; positivity
  -- step 1: μ(d)²/φ(d) ≤ 1/φ(d) = (1/d) Σ_{r ∣ d} G r
  have step1 : ∑ d ∈ D, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ≤
      ∑ d ∈ D, ∑ r ∈ d.divisors, G r * (1 / (d : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := by
      simp only [hD, mem_filter, mem_Icc] at hd; omega
    have hmu : ((μ d : ℝ)) ^ 2 ≤ 1 := by
      have h := (abs_moebius_le_one (n := d))
      have h' : |((μ d : ℝ))| ≤ 1 := by exact_mod_cast h
      nlinarith [abs_nonneg ((μ d : ℝ)), sq_abs ((μ d : ℝ))]
    have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    calc ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ≤ 1 / (d.totient : ℝ) := by gcongr
      _ = (1 / (d : ℝ)) * ∑ r ∈ d.divisors, G r := inv_totient_eq d hd1
      _ = ∑ r ∈ d.divisors, G r * (1 / (d : ℝ)) := by rw [Finset.mul_sum]; simp [mul_comm]
  -- step 2: swap the sums
  have step2 : ∑ d ∈ D, ∑ r ∈ d.divisors, G r * (1 / (d : ℝ)) =
      ∑ r ∈ R, ∑ d ∈ D.filter (fun d => r ∣ d), G r * (1 / (d : ℝ)) := by
    apply Finset.sum_comm'
    intro d r
    simp only [hD, hR, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hodd⟩, hrd, hd0⟩
      have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrd (by omega)
      exact ⟨⟨⟨⟨h1, h2⟩, hodd⟩, hrd⟩, ⟨⟨hr0, le_trans (Nat.le_of_dvd (by omega) hrd) h2⟩,
        Odd.of_dvd_nat hodd hrd⟩⟩
    · rintro ⟨⟨⟨⟨h1, h2⟩, hodd⟩, hrd⟩, _⟩
      exact ⟨⟨⟨h1, h2⟩, hodd⟩, hrd, by omega⟩
  -- step 3: the inner sum for one r
  have step3 : ∀ r ∈ R, ∑ d ∈ D.filter (fun d => r ∣ d), G r * (1 / (d : ℝ)) ≤
      G r / r * (1 + Real.log (b / a)) := by
    intro r hr
    have hr1 : 1 ≤ r := by simp only [hR, mem_filter, mem_Icc] at hr; omega
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    set M := Icc (⌊a / r⌋₊ + 1) ⌊b / r⌋₊ with hM
    have hsub : D.filter (fun d => r ∣ d) ⊆ M.image (fun m => r * m) := by
      intro d hd
      simp only [hD, mem_filter, mem_Icc] at hd
      obtain ⟨⟨⟨h1, h2⟩, _⟩, ⟨m, rfl⟩⟩ := hd
      refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
      have hda : a < ((r * m : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one a
        have h1' : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ ((r * m : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h1' this ⊢; linarith
      have hdb : ((r * m : ℕ) : ℝ) ≤ b := by
        have h2' : ((r * m : ℕ) : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast h2
        exact h2'.trans (Nat.floor_le (by linarith))
      push_cast at hda hdb
      simp only [hM, mem_Icc]
      constructor
      · have : a / r < m := by rw [div_lt_iff₀ hrpos]; linarith
        have h3 := (Nat.floor_lt (div_nonneg ha.le hrpos.le)).2 this
        omega
      · apply Nat.le_floor
        rw [le_div_iff₀ hrpos]; linarith
    have hinj : Set.InjOn (fun m => r * m) (M : Set ℕ) := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
    calc ∑ d ∈ D.filter (fun d => r ∣ d), G r * (1 / (d : ℝ))
        ≤ ∑ d ∈ M.image (fun m => r * m), G r * (1 / (d : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro d _ _; exact mul_nonneg (hGnn r) (by positivity)
      _ = ∑ m ∈ M, G r * (1 / ((r * m : ℕ) : ℝ)) := Finset.sum_image (fun x hx y hy h => hinj hx hy h)
      _ = G r / r * ∑ m ∈ M, 1 / (m : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          push_cast
          field_simp
      _ ≤ G r / r * (1 + Real.log (b / a)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (hGnn r) hrpos.le)
          have hw := harmonic_window (u := a / r) (v := b / r) (div_pos ha hrpos)
            (div_le_div_of_nonneg_right hab hrpos.le)
          rwa [div_div_div_cancel_right₀ hrpos.ne'] at hw
  -- step 4: assemble
  calc ∑ d ∈ D, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ)
      ≤ ∑ r ∈ R, G r / r * (1 + Real.log (b / a)) := by
        exact step1.trans (step2 ▸ Finset.sum_le_sum step3)
    _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        simp only [hG]
        rw [div_div, mul_comm (r.totient : ℝ)]

/-- `1 + log 202 ≤ 6.31`, the constant of Lemma 10: `202 < e^{5.31}`. -/
theorem one_add_log_202_le : 1 + Real.log 202 ≤ 6.31 := by
  have he := Real.exp_one_gt_d9
  have h5 : (148.4 : ℝ) ≤ Real.exp 5 := by
    have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (148.4 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := by gcongr
  have h031 : (1.363 : ℝ) ≤ Real.exp 0.31 := by
    have := Real.sum_le_exp_of_nonneg (x := (0.31 : ℝ)) (by norm_num) 4
    simp [Finset.sum_range_succ, Nat.factorial] at this
    norm_num at this
    linarith
  have h : (202 : ℝ) ≤ Real.exp 5.31 := by
    have : Real.exp 5.31 = Real.exp 5 * Real.exp 0.31 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have := Real.log_le_log (by norm_num) h
  rw [Real.log_exp] at this
  linarith

/-- **Lemma 10's sum at the paper's window**: `a = y/2`, `b = x/2 = 101 y`, so `b/a = 202`, and
the sum is at most `(Σ_{r ≤ 101y, r odd} μ(r)²/(rφ(r))) · 6.31`. -/
theorem lemma10_window {y : ℝ} (hy : 0 < y) :
    ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊101 * y⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ≤
      (∑ r ∈ (Icc 1 ⌊101 * y⌋₊).filter Odd, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ))) *
        6.31 := by
  have h := lemma10_sum (a := y / 2) (b := 101 * y) (by positivity) (by linarith)
  have hq : 101 * y / (y / 2) = 202 := by field_simp; ring
  rw [hq] at h
  refine h.trans (mul_le_mul_of_nonneg_left one_add_log_202_le ?_)
  apply Finset.sum_nonneg; intro r _; positivity

/-- Vacuity: at `y = 2` the window is `2 ≤ d ≤ 202`, odd `d`, nonempty, so `lemma10_window` is
not vacuous. -/
theorem lemma10_vacuity : 3 ∈ (Icc (⌊(2 : ℝ) / 2⌋₊ + 1) ⌊101 * (2 : ℝ)⌋₊).filter Odd := by
  have h1 : ⌊(2 : ℝ) / 2⌋₊ = 1 := by norm_num
  have h2 : ⌊101 * (2 : ℝ)⌋₊ = 202 := by
    rw [show (101 * (2 : ℝ)) = ((202 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  rw [h1, h2]
  decide

end LeanLab.RieselVaughan1983.L10
