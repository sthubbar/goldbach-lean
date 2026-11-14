module

public import LeanLab.PNTPort.Vinogradov.MinorArcs
public import LeanLab.PNTPort.LargeSieve.Parseval
public import LeanLab.PNTPort.BV.Helpers
public import LeanLab.HeathBrown1985.Statements

/-!
# Major arcs: `S(a/q + β) ≈ μ(q)/φ(q) V(β)`

Lab proof, unit U-5252. AI wrote this file. Known mathematics, no cited input: Davenport ch. 26,
Vaughan Lemma 3.1.

* `abel_e`: Abel summation against `e(nβ)`: if every partial sum of `f` up to `N` has norm at
  most `E`, then `‖∑_{n ≤ N} f(n) e(nβ)‖ ≤ E (1 + 2π|β| N)`.
* `ramanujan_coprime`: for `(a, q) = 1`, `∑_{r < q, (r, q) = 1} e(ar/q) = μ(q)`.
* `sum_e_residue`: `∑_{n ≤ X} Λ(n) e(an/q) = ∑_{r < q} e(ar/q) ψ(X; q, r)`.
* `norm_A_sub_le`: `‖∑_{n ≤ X} Λ(n) e(an/q) - μ(q) X/φ(q)‖ ≤ ∑_{r coprime} |ψ(X; q, r) - X/φ(q)| + ψ_bad`.
* `major_of_bound`: if those partial sums are within `E` of `μ(q) n/φ(q)` for all `n ≤ N`,
  `‖S(a/q + β) - μ(q)/φ(q) V(β)‖ ≤ E (1 + 2π|β| N)`, `V(β) = ∑_{n ≤ N} e(nβ)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve

/-- `V(β) = ∑_{1 ≤ n ≤ N} e(nβ)`. -/
noncomputable def V (N : ℕ) (β : ℝ) : ℂ := ∑ n ∈ Icc 1 N, e (n * β)

/-- Abel summation identity. -/
lemma abel_id (f g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n * g n = (∑ m ∈ Icc 1 N, f m) * g N +
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, f m) * (g n - g (n + 1)) - (∑ m ∈ Icc 1 N, f m) * (g N - g (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega) (fun n => (∑ m ∈ Icc 1 n, f m) * (g n - g (n + 1))),
      sum_Icc_succ_top (by omega)]
    ring

lemma norm_e_sub_succ (n : ℕ) (β : ℝ) : ‖e (n * β) - e ((n + 1 : ℕ) * β)‖ ≤ 2 * π * |β| := by
  have h1 : e (n * β) - e ((n + 1 : ℕ) * β) = - (e (n * β) * (e β - 1)) := by
    rw [mul_sub, mul_one, ← e_add]; push_cast; ring_nf
  rw [h1, norm_neg, norm_mul, norm_e, one_mul]
  unfold e
  refine (norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- Abel summation bound against `e(nβ)`. -/
theorem abel_e (f : ℕ → ℂ) (N : ℕ) (β : ℝ) {E : ℝ}
    (hE : ∀ n ≤ N, ‖∑ m ∈ Icc 1 n, f m‖ ≤ E) :
    ‖∑ n ∈ Icc 1 N, f n * e (n * β)‖ ≤ E * (1 + 2 * π * |β| * N) := by
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (hE 0 (Nat.zero_le _))
  set g : ℕ → ℂ := fun n => e (n * β) with hg
  have h := abel_id f g N
  simp only [hg] at h
  rw [h]
  have hlast : (∑ m ∈ Icc 1 N, f m) * e (N * β) - (∑ m ∈ Icc 1 N, f m) * (e (N * β) - e ((N + 1 : ℕ) * β))
      = (∑ m ∈ Icc 1 N, f m) * e ((N + 1 : ℕ) * β) := by ring
  have hrw : (∑ m ∈ Icc 1 N, f m) * e (N * β) + ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, f m) *
      (e (n * β) - e ((n + 1 : ℕ) * β)) - (∑ m ∈ Icc 1 N, f m) * (e (N * β) - e ((N + 1 : ℕ) * β)) =
      (∑ m ∈ Icc 1 N, f m) * e ((N + 1 : ℕ) * β) + ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, f m) *
      (e (n * β) - e ((n + 1 : ℕ) * β)) := by rw [← hlast]; ring
  push_cast at hrw ⊢
  rw [hrw]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(∑ m ∈ Icc 1 N, f m) * e ((N + 1) * β)‖ ≤ E := by
    rw [norm_mul, norm_e, mul_one]; exact hE N le_rfl
  have h2 : ‖∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, f m) * (e (n * β) - e ((n + 1) * β))‖ ≤
      ∑ n ∈ Icc 1 N, E * (2 * π * |β|) := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    rw [norm_mul]
    have := norm_e_sub_succ n β
    push_cast at this
    exact mul_le_mul (hE n (mem_Icc.1 hn).2) this (norm_nonneg _) hE0
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at h2
  have : ((N + 1 - 1 : ℕ) : ℝ) = N := by simp
  rw [this] at h2
  nlinarith

/-- `∑_{d ∣ n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) (coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [coe_mul_zeta_apply, one_apply] at h
  rw [← h]
  simp

/-- The coprime Ramanujan sum: `∑_{r < q, (r, q) = 1} e(ar/q) = μ(q)` for `(a, q) = 1`. -/
theorem ramanujan_coprime {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) :
    ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), e (a * r / q) = (μ q : ℂ) := by
  rw [sum_filter]
  have step1 : ∀ r ∈ range q, (if Nat.Coprime r q then e (a * r / q) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (μ d : ℂ) * e (a * r / q) := by
    intro r _
    rw [← sum_mul, sum_moebius_divisors]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl step1]
  rw [sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun r => d ∣ r))]
  · have step2 : ∀ d ∈ q.divisors, ∑ r ∈ (range q).filter (fun r => d ∣ r), (μ d : ℂ) * e (a * r / q)
        = (μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← mul_sum, ← sum_e_mul_div a hqd]
      congr 1
      refine sum_nbij' (fun r => r / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [mem_filter, mem_range] at hr
        rw [mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [mem_range] at hs
        rw [mem_filter, mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro r hr
        rw [mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        rw [mem_filter] at hr
        obtain ⟨s, rfl⟩ := hr.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [sum_congr rfl step2]
    rw [sum_eq_single q]
    · rw [Nat.div_self (by omega)]; simp
    · intro d hd hne
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      rw [if_neg, mul_zero]
      intro hdiv
      have h1 : ((q / d : ℕ) : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.div_dvd_of_dvd hdq
      have hu : IsUnit ((q / d : ℕ) : ℤ) := hcop.isUnit_of_dvd' hdiv h1
      rw [Int.isUnit_iff] at hu
      have h2 : q / d = 1 := by
        generalize q / d = t at hu
        rcases hu with h | h <;> omega
      have : q = d := by
        have := Nat.div_mul_cancel hdq
        rw [h2, one_mul] at this; exact this.symm
      exact hne this.symm
    · intro h; exact absurd (Nat.mem_divisors_self q (by omega)) h
  · intro r d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, by omega⟩

/-- `A(n) = ∑_{m ≤ n} Λ(m) e(am/q)`. -/
noncomputable def Aq (q : ℕ) (a : ℤ) (n : ℕ) : ℂ := ∑ m ∈ Icc 1 n, (Λ m : ℂ) * e (a * m / q)

lemma e_mod (q : ℕ) (hq : 1 ≤ q) (a : ℤ) (m : ℕ) : e (a * m / q) = e (a * (m % q : ℕ) / q) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h := Nat.div_add_mod m q
  have : (a : ℝ) * m / q = (a : ℝ) * (m % q : ℕ) / q + ((a * (m / q : ℕ) : ℤ) : ℝ) := by
    have hm : (m : ℝ) = q * (m / q : ℕ) + (m % q : ℕ) := by exact_mod_cast h.symm
    rw [Int.cast_mul, Int.cast_natCast, hm]; field_simp; ring
  rw [this, e_add, e_int, mul_one]

open LeanLab.HeathBrown1985 in
/-- The residue split: `A(n) = ∑_{r < q} e(ar/q) ψ(n; q, r)`. -/
theorem Aq_eq (q : ℕ) (hq : 1 ≤ q) (a : ℤ) (n : ℕ) :
    Aq q a n = ∑ r ∈ range q, e (a * r / q) * (psi n q r : ℂ) := by
  unfold Aq psi
  rw [Nat.floor_natCast]
  rw [← sum_fiberwise_of_maps_to (s := Icc 1 n) (t := range q) (g := fun m => m % q)
    (fun m _ => mem_range.2 (Nat.mod_lt m (by omega)))]
  refine sum_congr rfl fun r hr => ?_
  have hr' : r % q = r := Nat.mod_eq_of_lt (mem_range.1 hr)
  rw [hr', Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_filter] at hm
  rw [e_mod q hq a m, hm.2, mul_comm]

lemma coprime_mod_iff (m q : ℕ) : Nat.Coprime (m % q) q ↔ Nat.Coprime m q := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm m q, Nat.gcd_rec q m]

open LeanLab.HeathBrown1985 in
lemma sum_psi_bad (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    ∑ r ∈ (range q).filter (fun r => ¬ Nat.Coprime r q), psi n q r = BV.psiBad n q := by
  unfold psi BV.psiBad
  rw [Nat.floor_natCast]
  rw [← sum_fiberwise_of_maps_to (s := (Icc 1 n).filter (fun m => ¬ Nat.Coprime m q))
    (t := (range q).filter (fun r => ¬ Nat.Coprime r q)) (g := fun m => m % q)]
  · refine sum_congr rfl fun r hr => ?_
    rw [mem_filter, mem_range] at hr
    have hr' : r % q = r := Nat.mod_eq_of_lt hr.1
    rw [hr', filter_filter]
    congr 1
    ext m
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_, h2⟩
      rw [← coprime_mod_iff, h2]; exact hr.2
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  · intro m hm
    rw [mem_filter] at hm ⊢
    exact ⟨mem_range.2 (Nat.mod_lt m (by omega)), by rw [coprime_mod_iff]; exact hm.2⟩

open LeanLab.HeathBrown1985 in
/-- `‖A(n) - μ(q) n/φ(q)‖ ≤ ∑_{r coprime} |ψ(n; q, r) - n/φ(q)| + ψ_bad(n, q)`. -/
theorem norm_Aq_sub_le (q : ℕ) (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) (n : ℕ) :
    ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ ≤
      ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), |psi n q r - (n : ℝ) / q.totient|
        + BV.psiBad n q := by
  rw [Aq_eq q hq a n, ← ramanujan_coprime hq hcop, sum_mul,
    ← sum_filter_add_sum_filter_not (range q) (fun r => Nat.Coprime r q), add_sub_right_comm,
    ← sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    rw [← mul_sub, norm_mul, norm_e, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  · rw [← sum_psi_bad q hq n]
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (by unfold psi; exact sum_nonneg fun _ _ => vonMangoldt_nonneg))

/-- The major arc approximation from partial sum bounds. -/
theorem major_of_bound {q : ℕ} (_hq : 1 ≤ q) (a : ℤ) (N : ℕ) (β : ℝ) {E : ℝ}
    (hE : ∀ n ≤ N, ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ ≤ E) :
    ‖S N (a / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤ E * (1 + 2 * π * |β| * N) := by
  set f : ℕ → ℂ := fun m => (Λ m : ℂ) * e (a * m / q) - (μ q : ℂ) / q.totient with hf
  have hpart : ∀ n, ∑ m ∈ Icc 1 n, f m = Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ) := by
    intro n
    rw [hf, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
    unfold Aq
    congr 1
    push_cast
    ring
  have h := abel_e f N β (E := E) (fun n hn => by rw [hpart]; exact hE n hn)
  refine le_of_eq_of_le ?_ h
  congr 1
  unfold S V
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [hf]
  have : e (n * (a / q + β)) = e (a * n / q) * e (n * β) := by
    rw [← e_add]; congr 1; ring
  rw [this]
  ring

lemma norm_Aq_le (q : ℕ) (a : ℤ) (n : ℕ) : ‖Aq q a n‖ ≤ (Real.log 4 + 4) * n := by
  unfold Aq
  refine (norm_sum_le _ _).trans ?_
  have hψ := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at hψ
  have : Ioc 0 n = Icc 1 n := by ext m; simp only [mem_Ioc, mem_Icc]; omega
  rw [this] at hψ
  refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) hψ
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

open LeanLab.HeathBrown1985 in
/-- **The major arc approximation**, from Siegel-Walfisz: for `q ≤ (log N)^A`, `(a, q) = 1`,
`N ≥ e⁴` and every real `β`,
`‖S(a/q + β) - μ(q)/φ(q) V(β)‖ ≤ (7√N + q K N e^{-c √(log N / 2)} + (log q/log 2) log N)(1 + 2π|β|N)`. -/
theorem major_arc_of_SW (hSW : SiegelWalfisz) (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, Real.exp 4 ≤ N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ A → ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ β : ℝ,
      ‖S N (a / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤
        (7 * Real.sqrt N + q * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) +
          Real.log q / Real.log 2 * Real.log N) * (1 + 2 * π * |β| * N) := by
  obtain ⟨c, hc, K₀, hK₀⟩ := hSW (2 * A) (by linarith)
  set K := max K₀ 0 with hK
  refine ⟨c, hc, K, le_max_right _ _, ?_⟩
  intro N hN q hq hqA a hcop β
  apply major_of_bound hq a N β
  intro n hn
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN
  have hlogN : 4 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 4) hN; rwa [Real.log_exp] at this
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log q / Real.log 2 * Real.log N :=
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg q) (Real.log_nonneg (by norm_num)))
      (by linarith)
  have hmid : 0 ≤ q * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by positivity
  have hsq : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have htot : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rcases lt_or_ge ((n : ℝ) ^ 2) N with hsmall | hbig
  · -- small n: trivial bound
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnsq : (n : ℝ) ≤ Real.sqrt N := by
      rw [← Real.sqrt_sq hn0]; exact Real.sqrt_le_sqrt hsmall.le
    have h1 := norm_Aq_le q a n
    have h2 : ‖(μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ ≤ n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
      calc ‖(μ q : ℂ)‖ * ((n : ℝ) / q.totient) ≤ 1 * n :=
            mul_le_mul hμ (div_le_self hn0 htot) (by positivity) zero_le_one
        _ = n := one_mul _
    have h4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ‖Aq q a n‖ + ‖(μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ := norm_sub_le _ _
      _ ≤ (Real.log 4 + 4) * n + n := add_le_add h1 h2
      _ ≤ 7 * Real.sqrt N := by nlinarith
      _ ≤ _ := by linarith
  · -- large n: Siegel-Walfisz
    have hn2 : (2 : ℝ) ≤ n := by
      by_contra h
      push_neg at h
      have : (n : ℝ) ^ 2 < 4 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have : (4 : ℝ) < N := by
        have := Real.add_one_le_exp 4; linarith
      linarith
    have hlogn : Real.log N / 2 ≤ Real.log n := by
      have h := Real.log_le_log (by linarith) hbig
      rw [Real.log_pow] at h; push_cast at h; linarith
    have hqn : (q : ℝ) ≤ Real.log n ^ (2 * A) := by
      refine hqA.trans ?_
      have hl0 : 0 ≤ Real.log N := by linarith
      calc Real.log N ^ A ≤ (Real.log N / 2) ^ (2 * A) := by
            rw [Real.rpow_mul (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
            apply Real.rpow_le_rpow hl0 _ hA.le
            nlinarith
        _ ≤ Real.log n ^ (2 * A) := Real.rpow_le_rpow (by linarith) hlogn (by linarith)
    have hexp : Real.exp (-c * Real.sqrt (Real.log n)) ≤
        Real.exp (-c * Real.sqrt (Real.log N / 2)) := by
      apply Real.exp_le_exp.2
      have := Real.sqrt_le_sqrt hlogn
      nlinarith
    have hterm : ∀ r ∈ (range q).filter (fun r => Nat.Coprime r q),
        |psi n q r - (n : ℝ) / q.totient| ≤ K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by
      intro r hr
      have hcr : Nat.Coprime r q := (mem_filter.1 hr).2
      refine (hK₀ n hn2 q r hq hcr hqn).trans ?_
      have hK0 : K₀ ≤ K := le_max_left _ _
      have hKn : 0 ≤ K := le_max_right _ _
      calc K₀ * n * Real.exp (-c * Real.sqrt (Real.log n))
          ≤ K * n * Real.exp (-c * Real.sqrt (Real.log n)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right hK0 (Nat.cast_nonneg n)
        _ ≤ K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hnN hKn) hexp (Real.exp_pos _).le
            positivity
    have hsum := sum_le_sum hterm
    rw [sum_const] at hsum
    have hcard : (((range q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ q := by
      have := (card_filter_le (range q) (fun r => Nat.Coprime r q)).trans (card_range q).le
      exact_mod_cast this
    have hbad := BV.psiBad_le (x := (n : ℝ)) (by linarith) hq
    have hbad' : Real.log q / Real.log 2 * Real.log n ≤ Real.log q / Real.log 2 * Real.log N :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hnN)
        (div_nonneg (Real.log_natCast_nonneg q) (Real.log_nonneg (by norm_num)))
    have hX : 0 ≤ K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by positivity
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), |psi n q r - (n : ℝ) / q.totient|
          + BV.psiBad n q := norm_Aq_sub_le q hq hcop n
      _ ≤ q * (K * N * Real.exp (-c * Real.sqrt (Real.log N / 2))) +
          Real.log q / Real.log 2 * Real.log N := by
          rw [nsmul_eq_mul] at hsum
          have := mul_le_mul_of_nonneg_right hcard hX
          linarith
      _ ≤ _ := by
          have : q * (K * N * Real.exp (-c * Real.sqrt (Real.log N / 2))) =
              q * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) := by ring
          linarith

end LeanLab.PNTPort.Vinogradov

