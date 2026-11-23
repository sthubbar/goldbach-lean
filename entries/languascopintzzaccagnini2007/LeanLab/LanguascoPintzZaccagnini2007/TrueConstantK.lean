module

public import LeanLab.LanguascoPintzZaccagnini2007.TrueConstant

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5914, paper P0045.

# F-0038 for `k = 2, 3, 4`: the corrected constant `2c₀ C(k, N)` leaves `[1, 2]`

Languasco, Pintz, Zaccagnini, Bull. LMS 39, 2007, version of record `papers/P0045-journal.pdf`.
(23), p. 777: `C(k, N) = Σ'_{d ≥ 1} f(d) j(d, k, N)/ξ(d)^k` over odd squarefree `d`. The Theorem,
p. 772, claims `C(k, N) ∈ [1, 2]`, but the proof drops the factor `2c₀ = 2 twinC` of (2), so the
asymptotic constant the proof gives is `2c₀ C(k, N)`. TrueConstant.lean treats `k = 1`; this file
treats `k = 2, 3, 4`.

`Ck k N` is the paper's `C(k, N)`; the paper's `j(d, k, N)` is `jcount d (k - 1) N` of Links.lean.
`Ck_summable` by comparison with the series (26), PROVED as `lemma61_proved`, through
`jcount_le`. The count `jcount` is turned into the recursion `Gcount`, a sum over the first
exponent, and evaluated by the kernel on each residue class. Certificates, all exact:

* `k = 2`, `N ≡ 6 mod 15`: `d = 1, 3, 5` give `C(2, N) ≥ 1.5625`.
* `k = 3`, `N ≡ 791 mod 1155`: `d = 1, 3, 5, 7, 15, 21, 11` give `C(3, N) ≥ 1.5451`.
* `k = 4`, `N ≡ 13035 mod 15015`: `d = 1, 3, 5, 7, 15, 21, 11, 13, 33` give
  `C(4, N) ≥ 1.5395`.

Each exceeds `20/13`, so with `twinC_ge_065` the corrected constant `2c₀ C(k, N)` is above `2`
on a residue class of positive density. That the corrected constant is the true one rests on the
repaired chain, CONDITIONAL ON its cited inputs. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.LPZ2007
open Finset Real

attribute [local instance] Classical.propDecidable

/-- The term of (23) for general `k ≥ 1`. -/
noncomputable def Ckterm (k N d : ℕ) : ℝ :=
  if OddSqf d then fd d * (jcount d (k - 1) N : ℝ) / (xi d : ℝ) ^ k else 0

/-- The paper's `C(k, N)`, (23). -/
noncomputable def Ck (k N : ℕ) : ℝ := ∑' d, Ckterm k N d

theorem Ck_one (N : ℕ) : Ck 1 N = C1 N := by
  unfold Ck C1
  congr 1
  funext d
  simp [Ckterm, C1term]

theorem Ckterm_nonneg (k N d : ℕ) : 0 ≤ Ckterm k N d := by
  unfold Ckterm
  split_ifs with h
  · exact div_nonneg (mul_nonneg (fd_nonneg h) (Nat.cast_nonneg _)) (by positivity)
  · exact le_rfl

theorem Ckterm_le {k : ℕ} (hk : 1 ≤ k) (N d : ℕ) : Ckterm k N d ≤ seriesTerm d := by
  unfold Ckterm seriesTerm
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hj : (jcount d m N : ℝ) ≤ (xi d : ℝ) ^ m := by exact_mod_cast jcount_le h.2.1 m N
    have hx0 : (0 : ℝ) < xi d := by exact_mod_cast (xi_spec h.2.1).1
    have hf := fd_nonneg h
    have hxm : (0 : ℝ) < (xi d : ℝ) ^ (m + 1) := by positivity
    calc fd d * (jcount d m N : ℝ) / (xi d : ℝ) ^ (m + 1)
        ≤ fd d * (xi d : ℝ) ^ m / (xi d : ℝ) ^ (m + 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj hf) hxm.le
      _ = fd d / xi d := by
          rw [pow_succ]; field_simp
  · exact le_rfl

theorem Ck_summable {k : ℕ} (hk : 1 ≤ k) (N : ℕ) : Summable (Ckterm k N) :=
  Summable.of_nonneg_of_le (Ckterm_nonneg k N) (Ckterm_le hk N) lemma61_proved

/-! ### `jcount` as a recursion over the exponents -/

/-- The number of `ν ∈ [1, ξ]^k` with `d ∣ r - Σ 2^{ν i}`, by recursion on `k`. -/
def Gcount (d ξ : ℕ) : ℕ → ℤ → ℕ
  | 0, r => if (d : ℤ) ∣ r then 1 else 0
  | k + 1, r => ∑ a ∈ Icc 1 ξ, Gcount d ξ k (r - 2 ^ a)

theorem card_eq_Gcount (d ξ : ℕ) (k : ℕ) (r : ℤ) :
    ((Fintype.piFinset (fun _ : Fin k => Icc 1 ξ)).filter
      (fun ν => (d : ℤ) ∣ r - ∑ i, (2 : ℤ) ^ ν i)).card = Gcount d ξ k r := by
  induction k generalizing r with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, Gcount]
    split_ifs with h
    · rw [Finset.filter_true_of_mem (fun _ _ => h), Fintype.card_piFinset]
      simp
    · rw [Finset.filter_false_of_mem (fun _ _ => h)]
      simp
  | succ k ih =>
    have hpi : Fintype.piFinset (fun _ : Fin (k + 1) => Icc 1 ξ) =
        ((Icc 1 ξ) ×ˢ Fintype.piFinset (fun _ : Fin k => Icc 1 ξ)).map
          (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).toEmbedding := by
      have := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (k + 1) => Icc 1 ξ)
        (fun _ => True)
      simp only [Finset.filter_true] at this
      exact this
    rw [Finset.card_filter, hpi, Finset.sum_map, Finset.sum_product, Gcount]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← ih (r - 2 ^ a), Finset.card_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.toEmbedding_apply, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    congr 1
    apply propext
    constructor <;> intro h <;> convert h using 1 <;> ring

theorem jcount_eq_Gcount (d k N : ℕ) : jcount d k N = Gcount d (xi d) (k + 1) N :=
  card_eq_Gcount d (xi d) (k + 1) N

/-- `j(d, k, N)` depends on `N` only modulo `d`. -/
theorem jcount_congr {d k N r : ℕ} (h : (d : ℤ) ∣ (N : ℤ) - r) : jcount d k N = jcount d k r := by
  unfold jcount
  congr 1
  apply Finset.filter_congr
  intro ν _
  have e : (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i = ((N : ℤ) - r) + ((r : ℤ) - ∑ i, (2 : ℤ) ^ ν i) := by ring
  rw [e]
  exact ⟨fun h' => by simpa using dvd_sub h' h, fun h' => dvd_add h h'⟩

/-! ### The orders `ξ(d)` -/

theorem xi_eq_of {d m : ℕ} (hd : Odd d) (h1 : 1 ≤ m) (hm : 2 ^ m ≡ 1 [MOD d])
    (hlt : ∀ μ, 1 ≤ μ → μ < m → ¬ 2 ^ μ ≡ 1 [MOD d]) : xi d = m := by
  have hle := xi_le h1 hm
  obtain ⟨h1', h2'⟩ := xi_spec hd
  by_contra hne
  exact hlt (xi d) h1' (lt_of_le_of_ne hle hne) h2'

theorem xi_1 : xi 1 = 1 := xi_eq_of (by decide) le_rfl (by decide) (fun μ h1 h2 => by omega)
theorem xi_3 : xi 3 = 2 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ; decide)
theorem xi_5 : xi 5 = 4 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)
theorem xi_7 : xi 7 = 3 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)
theorem xi_11 : xi 11 = 10 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)
theorem xi_13 : xi 13 = 12 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)
theorem xi_15 : xi 15 = 4 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)
theorem xi_21 : xi 21 = 6 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)
theorem xi_33 : xi 33 = 10 := xi_eq_of (by decide) (by norm_num) (by decide)
  (fun μ h1 h2 => by interval_cases μ <;> decide)

/-! ### The weights `f(d)` -/

theorem fd_one : fd 1 = 1 := by simp [fd]

theorem fd_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    fd (p * q) = 1 / ((p : ℝ) - 2) * (1 / ((q : ℝ) - 2)) := by
  unfold fd
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
    ← Finset.insert_eq, Finset.filter_true_of_mem (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega),
    Finset.prod_insert (by simp; omega), Finset.prod_singleton]

theorem prime_7 : Nat.Prime 7 := by norm_num
theorem prime_11 : Nat.Prime 11 := by norm_num
theorem prime_13 : Nat.Prime 13 := by norm_num

theorem fd_3 : fd 3 = 1 := by rw [fd_prime Nat.prime_three (by norm_num)]; norm_num
theorem fd_5 : fd 5 = 1 / 3 := by rw [fd_prime Nat.prime_five (by norm_num)]; norm_num
theorem fd_7 : fd 7 = 1 / 5 := by rw [fd_prime prime_7 (by norm_num)]; norm_num
theorem fd_11 : fd 11 = 1 / 9 := by rw [fd_prime prime_11 (by norm_num)]; norm_num
theorem fd_13 : fd 13 = 1 / 11 := by rw [fd_prime prime_13 (by norm_num)]; norm_num
theorem fd_15 : fd 15 = 1 / 3 := by
  rw [show (15 : ℕ) = 3 * 5 by rfl, fd_mul_primes Nat.prime_three Nat.prime_five (by norm_num)
    (by norm_num)]; norm_num
theorem fd_21 : fd 21 = 1 / 5 := by
  rw [show (21 : ℕ) = 3 * 7 by rfl, fd_mul_primes Nat.prime_three prime_7 (by norm_num)
    (by norm_num)]; norm_num
theorem fd_33 : fd 33 = 1 / 9 := by
  rw [show (33 : ℕ) = 3 * 11 by rfl, fd_mul_primes Nat.prime_three prime_11 (by norm_num)
    (by norm_num)]; norm_num

/-! ### Odd squarefree -/

theorem oddSqf_1 : OddSqf 1 := ⟨one_pos, odd_one, squarefree_one⟩
theorem oddSqf_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    OddSqf (p * q) := by
  refine ⟨Nat.mul_pos hp.pos hq.pos, (hp.odd_of_ne_two (by omega)).mul
    (hq.odd_of_ne_two (by omega)), ?_⟩
  exact Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hp hq).mpr (by omega), hp.squarefree,
    hq.squarefree⟩
theorem oddSqf_3 : OddSqf 3 := oddSqf_prime Nat.prime_three (by norm_num)
theorem oddSqf_5 : OddSqf 5 := oddSqf_prime Nat.prime_five (by norm_num)
theorem oddSqf_7 : OddSqf 7 := oddSqf_prime prime_7 (by norm_num)
theorem oddSqf_11 : OddSqf 11 := oddSqf_prime prime_11 (by norm_num)
theorem oddSqf_13 : OddSqf 13 := oddSqf_prime prime_13 (by norm_num)
theorem oddSqf_15 : OddSqf 15 :=
  oddSqf_mul_primes (p := 3) (q := 5) Nat.prime_three Nat.prime_five (by norm_num) (by norm_num)
theorem oddSqf_21 : OddSqf 21 :=
  oddSqf_mul_primes (p := 3) (q := 7) Nat.prime_three prime_7 (by norm_num) (by norm_num)
theorem oddSqf_33 : OddSqf 33 :=
  oddSqf_mul_primes (p := 3) (q := 11) Nat.prime_three prime_11 (by norm_num) (by norm_num)

/-- A term of (23) on a residue class, from its three exact ingredients. -/
theorem Ckterm_eq {k N d r : ℕ} (hd : OddSqf d) (h : (d : ℤ) ∣ (N : ℤ) - r) {f : ℝ} {x j : ℕ}
    (hf : fd d = f) (hx : xi d = x) (hj : jcount d (k - 1) r = j) :
    Ckterm k N d = f * j / (x : ℝ) ^ k := by
  unfold Ckterm
  rw [if_pos hd, jcount_congr h, hj, hf, hx]

/-! ### The counts `j(d, k, N)`, evaluated by the kernel -/

set_option maxRecDepth 100000

-- k = 2, residue 6
theorem j2_1 : jcount 1 1 6 = 1 := by rw [jcount_eq_Gcount, xi_1]; decide +kernel
theorem j2_3 : jcount 3 1 6 = 2 := by rw [jcount_eq_Gcount, xi_3]; decide +kernel
theorem j2_5 : jcount 5 1 6 = 3 := by rw [jcount_eq_Gcount, xi_5]; decide +kernel

-- k = 3, residue 791
theorem j3_1 : jcount 1 2 791 = 1 := by rw [jcount_eq_Gcount, xi_1]; decide +kernel
theorem j3_3 : jcount 3 2 791 = 3 := by rw [jcount_eq_Gcount, xi_3]; decide +kernel
theorem j3_5 : jcount 5 2 791 = 13 := by rw [jcount_eq_Gcount, xi_5]; decide +kernel
theorem j3_7 : jcount 7 2 791 = 6 := by rw [jcount_eq_Gcount, xi_7]; decide +kernel
theorem j3_15 : jcount 15 2 791 = 6 := by rw [jcount_eq_Gcount, xi_15]; decide +kernel
theorem j3_21 : jcount 21 2 791 = 18 := by rw [jcount_eq_Gcount, xi_21]; decide +kernel
theorem j3_11 : jcount 11 2 791 = 91 := by rw [jcount_eq_Gcount, xi_11]; decide +kernel

-- k = 4, residue 13035
theorem j4_1 : jcount 1 3 13035 = 1 := by rw [jcount_eq_Gcount, xi_1]; decide +kernel
theorem j4_3 : jcount 3 3 13035 = 6 := by rw [jcount_eq_Gcount, xi_3]; decide +kernel
theorem j4_5 : jcount 5 3 13035 = 52 := by rw [jcount_eq_Gcount, xi_5]; decide +kernel
theorem j4_7 : jcount 7 3 13035 = 13 := by rw [jcount_eq_Gcount, xi_7]; decide +kernel
theorem j4_15 : jcount 15 3 13035 = 24 := by rw [jcount_eq_Gcount, xi_15]; decide +kernel
theorem j4_21 : jcount 21 3 13035 = 78 := by rw [jcount_eq_Gcount, xi_21]; decide +kernel
theorem j4_11 : jcount 11 3 13035 = 910 := by rw [jcount_eq_Gcount, xi_11]; decide +kernel
theorem j4_13 : jcount 13 3 13035 = 1595 := by rw [jcount_eq_Gcount, xi_13]; decide +kernel
theorem j4_33 : jcount 33 3 13035 = 390 := by rw [jcount_eq_Gcount, xi_33]; decide +kernel

/-! ### The lower bounds for `C(k, N)` -/

theorem dvd_of_dvd {m d r N : ℕ} (hd : d ∣ m) (h : (m : ℤ) ∣ (N : ℤ) - r) :
    (d : ℤ) ∣ (N : ℤ) - r :=
  (Int.natCast_dvd_natCast.mpr hd).trans h

/-- `C(2, N) ≥ 1.5625` for `N ≡ 6 mod 15`. -/
theorem C2_ge (N : ℕ) (h : ((15 : ℕ) : ℤ) ∣ (N : ℤ) - (6 : ℕ)) : 1.5625 ≤ Ck 2 N := by
  have t1 := Ckterm_eq (k := 2) oddSqf_1 (dvd_of_dvd (by norm_num) h) fd_one xi_1 j2_1
  have t3 := Ckterm_eq (k := 2) oddSqf_3 (dvd_of_dvd (by norm_num) h) fd_3 xi_3 j2_3
  have t5 := Ckterm_eq (k := 2) oddSqf_5 (dvd_of_dvd (by norm_num) h) fd_5 xi_5 j2_5
  have hsum := (Ck_summable (k := 2) (by norm_num) N).sum_le_tsum ({1, 3, 5} : Finset ℕ)
    (fun d _ => Ckterm_nonneg 2 N d)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    t1, t3, t5] at hsum
  rw [Ck]
  norm_num at hsum ⊢
  linarith

/-- `C(3, N) ≥ 1.5451` for `N ≡ 791 mod 1155`. -/
theorem C3_ge (N : ℕ) (h : ((1155 : ℕ) : ℤ) ∣ (N : ℤ) - (791 : ℕ)) : 1.5451 ≤ Ck 3 N := by
  have t1 := Ckterm_eq (k := 3) oddSqf_1 (dvd_of_dvd (by norm_num) h) fd_one xi_1 j3_1
  have t3 := Ckterm_eq (k := 3) oddSqf_3 (dvd_of_dvd (by norm_num) h) fd_3 xi_3 j3_3
  have t5 := Ckterm_eq (k := 3) oddSqf_5 (dvd_of_dvd (by norm_num) h) fd_5 xi_5 j3_5
  have t7 := Ckterm_eq (k := 3) oddSqf_7 (dvd_of_dvd (by norm_num) h) fd_7 xi_7 j3_7
  have t15 := Ckterm_eq (k := 3) oddSqf_15 (dvd_of_dvd (by norm_num) h) fd_15 xi_15 j3_15
  have t21 := Ckterm_eq (k := 3) oddSqf_21 (dvd_of_dvd (by norm_num) h) fd_21 xi_21 j3_21
  have t11 := Ckterm_eq (k := 3) oddSqf_11 (dvd_of_dvd (by norm_num) h) fd_11 xi_11 j3_11
  have hsum := (Ck_summable (k := 3) (by norm_num) N).sum_le_tsum
    ({1, 3, 5, 7, 15, 21, 11} : Finset ℕ) (fun d _ => Ckterm_nonneg 3 N d)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, t1, t3, t5, t7, t15, t21, t11] at hsum
  rw [Ck]
  norm_num at hsum ⊢
  linarith

/-- `C(4, N) ≥ 1.5395` for `N ≡ 13035 mod 15015`. -/
theorem C4_ge (N : ℕ) (h : ((15015 : ℕ) : ℤ) ∣ (N : ℤ) - (13035 : ℕ)) : 1.5395 ≤ Ck 4 N := by
  have t1 := Ckterm_eq (k := 4) oddSqf_1 (dvd_of_dvd (by norm_num) h) fd_one xi_1 j4_1
  have t3 := Ckterm_eq (k := 4) oddSqf_3 (dvd_of_dvd (by norm_num) h) fd_3 xi_3 j4_3
  have t5 := Ckterm_eq (k := 4) oddSqf_5 (dvd_of_dvd (by norm_num) h) fd_5 xi_5 j4_5
  have t7 := Ckterm_eq (k := 4) oddSqf_7 (dvd_of_dvd (by norm_num) h) fd_7 xi_7 j4_7
  have t15 := Ckterm_eq (k := 4) oddSqf_15 (dvd_of_dvd (by norm_num) h) fd_15 xi_15 j4_15
  have t21 := Ckterm_eq (k := 4) oddSqf_21 (dvd_of_dvd (by norm_num) h) fd_21 xi_21 j4_21
  have t11 := Ckterm_eq (k := 4) oddSqf_11 (dvd_of_dvd (by norm_num) h) fd_11 xi_11 j4_11
  have t13 := Ckterm_eq (k := 4) oddSqf_13 (dvd_of_dvd (by norm_num) h) fd_13 xi_13 j4_13
  have t33 := Ckterm_eq (k := 4) oddSqf_33 (dvd_of_dvd (by norm_num) h) fd_33 xi_33 j4_33
  have hsum := (Ck_summable (k := 4) (by norm_num) N).sum_le_tsum
    ({1, 3, 5, 7, 15, 21, 11, 13, 33} : Finset ℕ) (fun d _ => Ckterm_nonneg 4 N d)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    t1, t3, t5, t7, t15, t21, t11, t13, t33] at hsum
  rw [Ck]
  norm_num at hsum ⊢
  linarith

/-! ### F-0038 for `k = 2, 3, 4` -/

/-- **F-0038, `k = 2`**: for every `N ≡ 6 mod 15`, `2c₀ C(2, N) > 2`, with `2c₀ = 2 twinC`. -/
theorem true_constant_gt_two_k2 (N : ℕ) (h : (15 : ℤ) ∣ (N : ℤ) - 6) :
    2 < 2 * LeanLab.ChenExplicit.twinC * Ck 2 N := by
  have hT := LeanLab.ChenExplicit.twinC_ge_065
  have hC := C2_ge N (by exact_mod_cast h)
  nlinarith

/-- **F-0038, `k = 3`**: for every `N ≡ 791 mod 1155`, `2c₀ C(3, N) > 2`. -/
theorem true_constant_gt_two_k3 (N : ℕ) (h : (1155 : ℤ) ∣ (N : ℤ) - 791) :
    2 < 2 * LeanLab.ChenExplicit.twinC * Ck 3 N := by
  have hT := LeanLab.ChenExplicit.twinC_ge_065
  have hC := C3_ge N (by exact_mod_cast h)
  nlinarith

/-- **F-0038, `k = 4`**: for every `N ≡ 13035 mod 15015`, `2c₀ C(4, N) > 2`. -/
theorem true_constant_gt_two_k4 (N : ℕ) (h : (15015 : ℤ) ∣ (N : ℤ) - 13035) :
    2 < 2 * LeanLab.ChenExplicit.twinC * Ck 4 N := by
  have hT := LeanLab.ChenExplicit.twinC_ge_065
  have hC := C4_ge N (by exact_mod_cast h)
  nlinarith

/-- Vacuity, `k = 2`: `N = 36` is even and `≡ 6 mod 15`. -/
example : (15 : ℤ) ∣ ((36 : ℕ) : ℤ) - 6 ∧ Even 36 := by decide

/-- Vacuity, `k = 3`: `N = 1946 = 791 + 1155` is even and `≡ 791 mod 1155`. -/
example : (1155 : ℤ) ∣ ((1946 : ℕ) : ℤ) - 791 ∧ Even 1946 := by decide

/-- Vacuity, `k = 4`: `N = 28050 = 13035 + 15015` is even and `≡ 13035 mod 15015`. -/
example : (15015 : ℤ) ∣ ((28050 : ℕ) : ℤ) - 13035 ∧ Even 28050 := by decide

end LeanLab.LPZ2007
