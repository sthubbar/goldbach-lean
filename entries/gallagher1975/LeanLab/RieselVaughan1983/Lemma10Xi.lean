module

public import LeanLab.RieselVaughan1983.Final
public import LeanLab.RieselVaughan1983.OddSumsApply
public import LeanLab.RieselVaughan1983.Lemma14

/-!
P0032 Riesel-Vaughan 1983, Section 8 for the paper's own objects: (7.4) as a divisor sum, (8.5)
Ψ_k = Rest_k + Ξ_k, Lemma 10 for the paper's Ξ_k, and Lemma 14 from Lemmas 11 to 13 on the
d ≤ y/2 part.
Unit U-1214, PC run 20261020T1103Z-23466. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Pages 62 to 63: by (7.4) w(n) = Σ_{d∣n, 2∤d} μ(d)/φ(d); (8.2) Ψ_k = Σ_{2∤d} μ(d)/φ(d) Σ_{d∣n} R_k(n);
(8.4) Ξ_k is the part y/2 < d ≤ x/2, and (8.3) vanishes for d > x/2; (8.5) Ψ_k = Ξ_k + the part
d ≤ y/2. Lemma 10: |Ξ_k| ≤ 6.31 A₁₀ S_k, since for d > y/2 the partner p' is fixed by p modulo 2d.

What is here, all PROVED unconditional unless marked:
* `wn_eq_sum`: (7.4), w(n) = Σ_{d∣n, d odd} μ(d)/φ(d) for n ≥ 1, by multiplicativity.
* `psi_swap`: (8.2), Ψ_k = Σ_{d odd} μ(d)/φ(d) Σ_{d∣n} R_k(n), the lab's `PsiK`.
* `even_of_parts`, `rk_even`: both primes exceed 2, so n = p + p' is even.
* `T_eq_zero_of_large`: (8.3) vanishes for odd d > x/2.
* `psi_split`: (8.5), Ψ_k = Rest_k + Ξ_k for k ≥ 1, y > 4, y ≤ x.
* `primeCounting_eq_card`, `Pset`, `card_Pset_le`, `Sk_nonneg`: the primes of I_k number at most
  S_k = π(ky/2 + y) − π(ky/2), (8.13).
* `T_le_Sk`: for odd d with 2d > y, Σ_{d∣n} R_k(n) ≤ S_k, the page 63 argument that p' is fixed
  by p modulo 2d.
* `abs_coef`, `lemma10`: **Lemma 10** for the paper's Ξ_k, |Ξ_k| ≤ 6.31 A₁₀ S_k, y = x/202.
* `Nk`, `wk`, `Nk_bounds`: (8.6) and y − 1 < N_k < y + 1.
* `Lemma11to13P`: Lemmas 11 to 13 with (8.7) to (8.12) on the part d ≤ y/2, a Prop, NOT proved.
* `lemma14P_of`: the lab's `Lemma14P` from `Lemma11to13P`, via `Lemma14.lemma14_of_N`.
* `theorem_of_lemma5_11to13`: the Theorem, 18 primes, CONDITIONAL ON Lemma 5 at five rows,
  Lemma 6, (2.30) and (2.31), (3.3) and `Lemma11to13P`.
* `lemma10_vacuity`: the Lemma 10 window is nonempty.
KNOWN mathematics, the paper's route.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section
namespace LeanLab.RieselVaughan1983.Xi

/-- `μ(d)/φ(d)` on odd `d`, zero on even `d`. -/
def hw : ArithmeticFunction ℝ :=
  ⟨fun n => if Odd n then ((μ n : ℝ)) / (n.totient : ℝ) else 0, by simp⟩

lemma hw_apply (n : ℕ) : hw n = if Odd n then ((μ n : ℝ)) / (n.totient : ℝ) else 0 := rfl

lemma hw_mult : hw.IsMultiplicative := by
  refine ⟨by simp [hw_apply], fun {m n} hmn => ?_⟩
  simp only [hw_apply, Nat.odd_mul]
  by_cases hm : Odd m <;> by_cases hn : Odd n <;> simp only [hm, hn, and_self, and_false,
    false_and, if_true, if_false, mul_zero, zero_mul]
  rw [isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_div_mul_comm]

/-- `w(n)` as an arithmetic function, zero at `0`. -/
def W : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else wn n, by simp⟩

lemma W_apply {n : ℕ} (hn : n ≠ 0) : W n = wn n := by
  show (if n = 0 then 0 else wn n) = wn n
  rw [if_neg hn]

lemma W_mult : W.IsMultiplicative := by
  refine ⟨by rw [W_apply one_ne_zero]; simp [wn], fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [W]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [W]
  rw [W_apply (by positivity), W_apply hm.ne', W_apply hn.ne']
  unfold wn
  rw [Nat.Coprime.primeFactors_mul hmn, filter_union, prod_union]
  exact disjoint_filter_filter (Nat.Coprime.disjoint_primeFactors hmn)

lemma hwz_mult : (hw * (ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
  hw_mult.mul isMultiplicative_zeta.natCast

lemma on_prime_pow (p k : ℕ) (hp : p.Prime) :
    (hw * (ζ : ArithmeticFunction ℝ)) (p ^ k) = W (p ^ k) := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hw_apply, W_apply, wn]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsum : ∑ j ∈ range (k + 1), hw (p ^ j) = 1 + hw p := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∑ j ∈ range k', hw (p ^ (j + 1 + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [hw_apply, moebius_apply_prime_pow hp (show j + 1 + 1 ≠ 0 by omega)]
    rw [hz, zero_add]
    simp [hw_apply]
    ring
  rw [hsum, W_apply (pow_ne_zero _ hp.ne_zero)]
  unfold wn
  rw [Nat.primeFactors_prime_pow hk.ne' hp, hw_apply]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · simp [show ¬ Odd 2 by decide, filter_singleton]
  · have h2 : 2 < p := by
      rcases hodd with ⟨r, hr⟩
      have := hp.two_le; omega
    rw [filter_singleton, if_pos h2, prod_singleton, if_pos hodd, moebius_apply_prime hp,
      Nat.totient_prime hp]
    rw [Nat.cast_sub hp.one_le]
    push_cast
    field_simp
    ring

/-- (7.4): `w(n) = Σ_{d ∣ n, d odd} μ(d)/φ(d)` for `n ≥ 1`. -/
theorem wn_eq_sum {n : ℕ} (hn : n ≠ 0) :
    wn n = ∑ d ∈ n.divisors.filter Odd, ((μ d : ℝ)) / (d.totient : ℝ) := by
  have hEq : hw * (ζ : ArithmeticFunction ℝ) = W :=
    (IsMultiplicative.eq_iff_eq_on_prime_powers _ hwz_mult _ W_mult).2
      (fun p i hp => on_prime_pow p i hp)
  have h1 : (hw * (ζ : ArithmeticFunction ℝ)) n = W n := by rw [hEq]
  rw [coe_mul_zeta_apply, W_apply hn] at h1
  rw [← h1, sum_filter]
  rfl


/-- `μ(d)/φ(d)`. -/
def coef (d : ℕ) : ℝ := ((μ d : ℝ)) / (d.totient : ℝ)

/-- (8.3): `Σ_{1 ≤ n ≤ x, d ∣ n} R_k(n)`. -/
def T (x y : ℝ) (k d : ℕ) : ℝ :=
  ∑ n ∈ (range (⌊x⌋₊ + 1)).filter (fun n => d ∣ n ∧ n ≠ 0), (Rk y k n : ℝ)

/-- The part `d ≤ y/2` of (8.5), that is `Φ_k − Δ_k + Θ_k` by (8.7) to (8.12). -/
def RestK (x y : ℝ) (k : ℕ) : ℝ := ∑ d ∈ (Icc 1 ⌊y / 2⌋₊).filter Odd, coef d * T x y k d

/-- (8.4): `Ξ_k = Σ_{y/2 < d ≤ x/2, 2∤d} μ(d)/φ(d) Σ_{d∣n} R_k(n)`. -/
def XiK (x y : ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊x / 2⌋₊).filter Odd, coef d * T x y k d

lemma Rk_zero (y : ℝ) (k : ℕ) : Rk y k 0 = 0 := by
  unfold Rk
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp
  rw [mem_range] at hp
  have : p = 0 := by omega
  subst this
  simp [Nat.not_prime_zero]

/-- (8.2) with (7.4): `Ψ_k = Σ_{d odd} μ(d)/φ(d) Σ_{d∣n} R_k(n)`. -/
theorem psi_swap (x y : ℝ) (k : ℕ) :
    PsiK x y k = ∑ d ∈ (range (⌊x⌋₊ + 1)).filter Odd, coef d * T x y k d := by
  unfold PsiK T
  set X := ⌊x⌋₊
  have step0 : ∑ n ∈ range (X + 1), (Rk y k n : ℝ) * wn n =
      ∑ n ∈ (range (X + 1)).filter (· ≠ 0), (Rk y k n : ℝ) * wn n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : n = 0
    · subst hn; simp [Rk_zero]
    · rw [if_pos hn]
  have step1 : ∑ n ∈ (range (X + 1)).filter (· ≠ 0), (Rk y k n : ℝ) * wn n =
      ∑ n ∈ (range (X + 1)).filter (· ≠ 0), ∑ d ∈ n.divisors.filter Odd,
        coef d * (Rk y k n : ℝ) := by
    apply sum_congr rfl
    intro n hn
    rw [mem_filter] at hn
    rw [wn_eq_sum hn.2, mul_sum]
    apply sum_congr rfl
    intro d _
    unfold coef; ring
  rw [step0, step1]
  simp_rw [mul_sum]
  apply sum_comm'
  intro n d
  simp only [mem_filter, mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hnX, hn0⟩, ⟨hdn, -⟩, hd⟩
    exact ⟨⟨hnX, hdn, hn0⟩, lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hnX, hd⟩
  · rintro ⟨⟨hnX, hdn, hn0⟩, -, hd⟩
    exact ⟨⟨hnX, hn0⟩, ⟨hdn, hn0⟩, hd⟩

/-- Two primes above `ky/2 ≥ y/2 > 2` are odd, so their sum is even. -/
theorem even_of_parts {y : ℝ} {k n p : ℕ} (hy : 4 < y) (hk : 1 ≤ k) (hpn : p ≤ n) (hp : p.Prime)
    (hq : (n - p).Prime) (h1 : (k : ℝ) * y / 2 < p) (h3 : (k : ℝ) * y / 2 < ((n - p : ℕ) : ℝ)) :
    Even n := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 2 < (k : ℝ) * y / 2 := by nlinarith
  have hp2 : p ≠ 2 := by
    intro e; subst e; norm_num at h1; linarith
  have hq2 : n - p ≠ 2 := by
    intro e; rw [e] at h3; norm_num at h3; linarith
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd (n - p) := hq.odd_of_ne_two hq2
  have : n = p + (n - p) := by omega
  rw [this]
  exact hpo.add_odd hqo

/-- In `R_k(n) ≠ 0` with `k ≥ 1`, `y > 4`, both primes exceed `2`, so `n` is even. -/
theorem rk_even {y : ℝ} {k n : ℕ} (hy : 4 < y) (hk : 1 ≤ k) (h : Rk y k n ≠ 0) : Even n := by
  obtain ⟨p, hpn, hp, hq, ⟨h1, -⟩, ⟨h3, -⟩⟩ := rk_pos_elim h
  exact even_of_parts hy hk hpn hp hq h1 h3

/-- (8.3) vanishes for odd `d > x/2`. -/
theorem T_eq_zero_of_large {x y : ℝ} {k d : ℕ} (hx : 0 ≤ x) (hy : 4 < y) (hk : 1 ≤ k)
    (hd : Odd d) (hdx : ⌊x / 2⌋₊ < d) : T x y k d = 0 := by
  unfold T
  apply sum_eq_zero
  intro n hn
  rw [mem_filter, mem_range] at hn
  obtain ⟨hnX, ⟨m, rfl⟩, hn0⟩ := hn
  by_contra hR
  have hR' : Rk y k (d * m) ≠ 0 := by
    intro h0; apply hR; rw [h0]; simp
  have hev := rk_even hy hk hR'
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp at hn0
    · rw [mul_one] at hev
      exact (Nat.not_even_iff_odd.mpr hd) hev
  · have h1 : (x / 2) < (⌊x / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((⌊x / 2⌋₊ : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast hdx
    have h3 : (d : ℝ) * 2 ≤ (d * m : ℕ) := by
      push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm) (by positivity)
    have h4 : ((d * m : ℕ) : ℝ) ≤ x := by
      have := Nat.floor_le hx
      have h5 : ((d * m : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (show d * m ≤ ⌊x⌋₊ by omega)
      linarith
    linarith

/-- (8.5): `Ψ_k = Rest_k + Ξ_k`, the `d ≤ y/2` part plus the `y/2 < d ≤ x/2` part. -/
theorem psi_split {x y : ℝ} {k : ℕ} (hx : 0 ≤ x) (hy : 4 < y) (hk : 1 ≤ k) (hyx : y ≤ x) :
    PsiK x y k = RestK x y k + XiK x y k := by
  rw [psi_swap]
  unfold RestK XiK
  rw [← sum_union]
  · symm
    apply sum_subset
    · intro d hd
      rw [mem_union, mem_filter, mem_filter, mem_Icc, mem_Icc] at hd
      rw [mem_filter, mem_range]
      have hyX : ⌊y / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
      have hxX : ⌊x / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
      rcases hd with ⟨⟨-, h⟩, ho⟩ | ⟨⟨-, h⟩, ho⟩
      · exact ⟨by omega, ho⟩
      · exact ⟨by omega, ho⟩
    · intro d hd hnot
      rw [mem_filter, mem_range] at hd
      rw [mem_union, mem_filter, mem_filter, mem_Icc, mem_Icc] at hnot
      have hd1 : 1 ≤ d := by
        rcases hd.2 with ⟨r, hr⟩; omega
      have hbig : ⌊x / 2⌋₊ < d := by
        by_contra hc
        push_neg at hc
        rcases Nat.lt_or_ge ⌊y / 2⌋₊ d with h | h
        · exact hnot (Or.inr ⟨⟨h, hc⟩, hd.2⟩)
        · exact hnot (Or.inl ⟨⟨hd1, h⟩, hd.2⟩)
      rw [T_eq_zero_of_large hx hy hk hd.2 hbig, mul_zero]
  · rw [disjoint_left]
    intro d h1 h2
    rw [mem_filter, mem_Icc] at h1 h2
    omega

/-- `π(n) = #{p ≤ n prime}`. -/
lemma primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = #((range (n + 1)).filter Nat.Prime) := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, ← Nat.primesBelow_card_eq_primeCounting',
    Nat.primesBelow_eq_filter_range]

/-- The primes of `I_k = (ky/2, ky/2 + y]`. -/
def Pset (y : ℝ) (k : ℕ) : Finset ℕ :=
  (range (⌊k * y / 2 + y⌋₊ + 1)).filter (fun p => p.Prime ∧ k * y / 2 < p ∧ (p : ℝ) ≤ k * y / 2 + y)

/-- `#(primes in I_k) ≤ S_k`, (8.13). -/
theorem card_Pset_le (y : ℝ) (k : ℕ) (hy : 0 ≤ y) : (#(Pset y k) : ℝ) ≤ Sk y k := by
  unfold Sk
  set a := (k : ℝ) * y / 2
  have ha : 0 ≤ a := by positivity
  have hdisj : Disjoint (Pset y k) ((range (⌊a⌋₊ + 1)).filter Nat.Prime) := by
    rw [disjoint_left]
    intro p hp hp'
    rw [Pset, mem_filter] at hp
    rw [mem_filter, mem_range] at hp'
    have : (p : ℝ) ≤ a := by
      have h1 : (p : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (show p ≤ ⌊a⌋₊ by omega)
      linarith [Nat.floor_le ha]
    have h' : a < (p : ℝ) := hp.2.2.1
    linarith
  have hsub : Pset y k ∪ (range (⌊a⌋₊ + 1)).filter Nat.Prime ⊆
      (range (⌊a + y⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    rw [mem_union] at hp
    rw [mem_filter, mem_range]
    rcases hp with hp | hp
    · rw [Pset, mem_filter, mem_range] at hp
      exact ⟨hp.1, hp.2.1⟩
    · rw [mem_filter, mem_range] at hp
      have : ⌊a⌋₊ ≤ ⌊a + y⌋₊ := Nat.floor_le_floor (by linarith)
      exact ⟨by omega, hp.2⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at hc
  rw [primeCounting_eq_card, primeCounting_eq_card]
  have : (#(Pset y k) : ℝ) + #((range (⌊a⌋₊ + 1)).filter Nat.Prime) ≤
      #((range (⌊a + y⌋₊ + 1)).filter Nat.Prime) := by exact_mod_cast hc
  linarith

theorem Sk_nonneg (y : ℝ) (k : ℕ) (hy : 0 ≤ y) : 0 ≤ Sk y k :=
  le_trans (Nat.cast_nonneg _) (card_Pset_le y k hy)

/-- Page 63, proof of Lemma 10: for odd `d` with `2d > y`, `Σ_{d∣n} R_k(n) ≤ S_k`, since `p'` is
determined by `p` modulo `2d`. -/
theorem T_le_Sk {x y : ℝ} {k d : ℕ} (hy : 4 < y) (hk : 1 ≤ k) (hd : Odd d) (hdy : y < 2 * d) :
    T x y k d ≤ Sk y k := by
  refine le_trans ?_ (card_Pset_le y k (by linarith))
  unfold T Rk
  rw [← Nat.cast_sum]
  apply Nat.cast_le.mpr
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun np => np.2)
  · rintro ⟨n, p⟩ hnp
    simp only [mem_coe, mem_sigma, mem_filter, mem_range] at hnp
    obtain ⟨-, hpn, hp, -, ⟨h1, h2⟩, -⟩ := hnp
    simp only [mem_coe, Pset, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2), hp, h1, h2⟩
  · rintro ⟨n1, p1⟩ hn1 ⟨n2, p2⟩ hn2 hpp
    simp only at hpp
    subst hpp
    simp only [mem_coe, mem_sigma, mem_filter, mem_range] at hn1 hn2
    obtain ⟨⟨-, ⟨m1, rfl⟩, -⟩, hpn1, hp, hq1, ⟨h11, -⟩, ⟨h13, h14⟩⟩ := hn1
    obtain ⟨⟨-, ⟨m2, rfl⟩, -⟩, hpn2, -, hq2, -, ⟨h23, h24⟩⟩ := hn2
    have hev1 := even_of_parts hy hk (by omega) hp hq1 h11 h13
    have hev2 := even_of_parts hy hk (by omega) hp hq2 h11 h23
    have hdne : ¬ Even d := Nat.not_even_iff_odd.mpr hd
    obtain ⟨t1, rfl⟩ : Even m1 := (Nat.even_mul.mp hev1).resolve_left hdne
    obtain ⟨t2, rfl⟩ : Even m2 := (Nat.even_mul.mp hev2).resolve_left hdne
    rw [Nat.cast_sub (by omega)] at h13 h14
    rw [Nat.cast_sub (by omega)] at h23 h24
    push_cast at h13 h14 h23 h24
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := by rcases hd with ⟨r, hr⟩; omega
      exact_mod_cast this
    have a1 : (t1 : ℝ) < t2 + 1 := by nlinarith
    have a2 : (t2 : ℝ) < t1 + 1 := by nlinarith
    have b1 : t1 < t2 + 1 := by exact_mod_cast a1
    have b2 : t2 < t1 + 1 := by exact_mod_cast a2
    have : t1 = t2 := by omega
    subst this
    rfl


/-- `|μ(d)/φ(d)| = μ(d)²/φ(d)`. -/
lemma abs_coef (d : ℕ) : |coef d| = ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) := by
  unfold coef
  rw [abs_div, Nat.abs_cast]
  congr 1
  have h1 : |(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) := by push_cast; rfl
  have h2 : ((μ d : ℝ)) ^ 2 = ((μ d ^ 2 : ℤ) : ℝ) := by push_cast; rfl
  rw [h1, h2, abs_moebius, moebius_sq]

lemma T_nonneg (x y : ℝ) (k d : ℕ) : 0 ≤ T x y k d :=
  sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- **Lemma 10**, page 63, for the paper's `Ξ_k` of (8.4), with `K = 200`, `y = x/202`:
`|Ξ_k| ≤ 6.31 A₁₀ S_k`. -/
theorem lemma10 {x : ℝ} {k : ℕ} (hy : 4 < x / 202) (hk : 1 ≤ k) :
    |XiK x (x / 202) k| ≤ 6.31 * OddSums.A10 * Sk (x / 202) k := by
  set y := x / 202 with hydef
  have hy0 : 0 ≤ y := by linarith
  have hS := Sk_nonneg y k hy0
  have hxy : ⌊x / 2⌋₊ = ⌊101 * y⌋₊ := by rw [hydef]; congr 1; ring
  unfold XiK
  rw [hxy]
  calc |∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊101 * y⌋₊).filter Odd, coef d * T x y k d|
      ≤ ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊101 * y⌋₊).filter Odd, |coef d * T x y k d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊101 * y⌋₊).filter Odd,
          ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) * Sk y k := by
        apply sum_le_sum
        intro d hd
        rw [mem_filter, mem_Icc] at hd
        rw [abs_mul, abs_coef, abs_of_nonneg (T_nonneg _ _ _ _)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply T_le_Sk (by linarith) hk hd.2
        have h1 : y / 2 < (⌊y / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : ((⌊y / 2⌋₊ : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast hd.1.1
        linarith
    _ = (∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊101 * y⌋₊).filter Odd,
          ((μ d : ℝ)) ^ 2 / (d.totient : ℝ)) * Sk y k := by rw [sum_mul]
    _ ≤ OddSums.A10 * 6.31 * Sk y k :=
        mul_le_mul_of_nonneg_right (OddSumsApply.lemma10_window_A10 (by linarith)) hS
    _ = 6.31 * OddSums.A10 * Sk y k := by ring

/-- (8.6): `N_k = [ky/2 + y] − [ky/2]`. -/
def Nk (y : ℝ) (k : ℕ) : ℝ := (⌊k * y / 2 + y⌋₊ : ℝ) - ⌊k * y / 2⌋₊

/-- (8.6): `w_k = (2N_k/3)^{1/2}/100`. -/
def wk (y : ℝ) (k : ℕ) : ℝ := Real.sqrt (2 / 3 * Nk y k) / 100

theorem Nk_bounds (y : ℝ) (k : ℕ) (hy : 0 ≤ y) : y - 1 < Nk y k ∧ Nk y k < y + 1 := by
  unfold Nk
  have ha : 0 ≤ (k : ℝ) * y / 2 := by positivity
  have h1 := Nat.floor_le ha
  have h2 := Nat.lt_floor_add_one ((k : ℝ) * y / 2)
  have h3 := Nat.floor_le (show 0 ≤ (k : ℝ) * y / 2 + y by positivity)
  have h4 := Nat.lt_floor_add_one ((k : ℝ) * y / 2 + y)
  constructor <;> linarith

lemma A11_nonneg : 0 ≤ OddSums.A11 := by
  have hb := OddSums.bdd OddSums.h11 OddSums.h11_nonneg 4 (by norm_num) OddSums.h11_le
  have h0 : ∏ p ∈ OddSums.S 0, (1 + OddSums.h11 p) ≤ OddSums.A11 := le_ciSup hb 0
  have hS0 : OddSums.S 0 = ∅ := by
    unfold OddSums.S; rw [filter_eq_empty_iff]; intro p hp; rw [mem_Icc] at hp; omega
  rw [hS0, prod_empty] at h0
  linarith

/-- Lemmas 11, 12 and 13 with (8.7) to (8.12), on the `d ≤ y/2` part of (8.5), as the paper
uses them in the proof of Lemma 14: `Rest_k = Φ_k − Δ_k + Θ_k` with Lemma 13's lower bound for
`Φ_k`, `|Δ_k| ≤ 8A₁₁ w S_k` and `|Θ_k| ≤ 3A₁₀ (y/w) S_k`. NOT proved here: it needs the
character expansion (8.7), primitive characters, and Lemma 13 cites Montgomery-Vaughan. -/
def Lemma11to13P : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-(29024 / 10000) + Real.log (Nk (x / 202) k)))) -
      8 * OddSums.A11 * wk (x / 202) k * Sk (x / 202) k -
      3 * OddSums.A10 * (x / 202 / wk (x / 202) k) * Sk (x / 202) k ≤ RestK x (x / 202) k

/-- **Lemma 14** for the paper's `Ψ_k`, CONDITIONAL ON Lemmas 11 to 13 on the `d ≤ y/2` part;
(8.5) and Lemma 10 are PROVED. -/
theorem lemma14P_of (h : Lemma11to13P) : Lemma14P := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hy0 : 0 < y := by positivity
  have hy4 : 4 < y := by
    by_contra hc
    push_neg at hc
    have : Real.log y ≤ Real.log 4 := Real.log_le_log hy0 hc
    have : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have hS := Sk_nonneg y k hy0.le
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k hy0.le
  have hsplit := psi_split (x := x) (y := y) (k := k) hx.le hy4 hk1 (by rw [hydef]; linarith)
  have h10 := lemma10 (x := x) (k := k) hy4 hk1
  have hA10 : 0 ≤ OddSums.A10 := by have := OddSums.A10_ge; linarith
  have hA11 := A11_nonneg
  have hw0 : 0 ≤ wk y k := by unfold wk; positivity
  set S := Sk y k
  set N := Nk y k
  set w := wk y k
  have hH := h x hx hL k hk
  have key := Lemma14.lemma14_of_N (y := y) (N := N) (C := Ctw) (S := S)
    (Ψ := PsiK x y k) (Ξ := XiK x y k)
    (Δ := 8 * OddSums.A11 * w * S) (Θ := -(3 * OddSums.A10 * (y / w) * S))
    (Φ := RestK x y k + 8 * OddSums.A11 * w * S + 3 * OddSums.A10 * (y / w) * S)
    hy0 hL.le hN1 hN2 (by have := Ctw_ge; linarith) hS
    (by rw [hsplit]; ring) h10
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; unfold w wk; exact le_refl _)
    (by rw [abs_of_nonneg (by positivity)]; unfold w wk; exact le_refl _)
    (by linarith)
  have e : (2.9267 : ℝ) = 29267 / 10000 := by norm_num
  rw [e] at key
  exact key

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at five rows, Lemma 6 (i) and (ii), (2.30) and (2.31), Rosser-Schoenfeld (3.3), and
Lemmas 11 to 13 on the `d ≤ y/2` part of Section 8. Lemmas 9, 10, 14, 15 and Section 9 are
PROVED from these. -/
theorem theorem_of_lemma5_11to13 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33)
    (h1113 : Lemma11to13P) : Theorem :=
  theorem_of_lemma5_14 h24 h42 h278 h396 h5 h6 h6' hTab hRS (lemma14P_of h1113)

/-- Vacuity of the Lemma 10 window: at `x = 202·10`, `y = 10`, `d = 7` lies in
`y/2 < d ≤ x/2` and `2d > y`. -/
theorem lemma10_vacuity : 7 ∈ (Icc (⌊(202 * 10 : ℝ) / 202 / 2⌋₊ + 1) ⌊(202 * 10 : ℝ) / 2⌋₊).filter Odd := by
  have h1 : ⌊(202 * 10 : ℝ) / 202 / 2⌋₊ = 5 := by norm_num
  have h2 : ⌊(202 * 10 : ℝ) / 2⌋₊ = 1010 := by norm_num
  rw [h1, h2, mem_filter, mem_Icc]
  exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩

end LeanLab.RieselVaughan1983.Xi
