module

public import Mathlib
public import LeanLab.LPZ2007.Statements
public import LeanLab.Linnik.ExactAtMost

/-!
P0045 Languasco, Pintz, Zaccagnini 2007, preprint: elementary pieces, no placeholder proof.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Theorems taking a cited `Prop` as a hypothesis are implications:
their conclusions are CONDITIONAL ON that `Prop`.
-/

@[expose] public section

open Finset Real Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.LPZ2007

/-! ### `ξ`, `f`, `j` -/

theorem xi_one : xi 1 = 1 := by
  unfold xi
  rw [orderOf_eq_one_iff]; exact Subsingleton.elim _ _

theorem fd_one : fd 1 = 1 := by simp [fd]

theorem fd_nonneg (d : ℕ) : 0 ≤ fd d := by
  unfold fd
  refine prod_nonneg fun p hp => ?_
  have : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  exact div_nonneg zero_le_one (by linarith)

theorem oddSqf_one : OddSqf 1 := ⟨odd_one, squarefree_one⟩

theorem card_tuples (k M : ℕ) : #(tuples k M) = M ^ k := by
  simp [tuples, Fintype.card_piFinset]

/-- `2` is a unit mod odd `d`. -/
theorem isUnit_two {d : ℕ} (hd : Odd d) : IsUnit (2 : ZMod d) := by
  have hc : Nat.Coprime 2 d := (Nat.coprime_two_left).mpr hd
  have := (ZMod.unitOfCoprime 2 hc).isUnit
  simpa using this

/-- `ξ(d) ≥ 1` for odd `d`. -/
theorem xi_pos {d : ℕ} (hd : Odd d) : 0 < xi d := by
  have : NeZero d := ⟨by rintro rfl; simp at hd⟩
  obtain ⟨u, hu⟩ := isUnit_two hd
  unfold xi
  rw [← hu, orderOf_units]
  exact orderOf_pos u

/-- `2^{ξ(d)} ≡ 1 mod d`, the defining property of `ξ`. -/
theorem two_pow_xi (d : ℕ) : (2 : ZMod d) ^ xi d = 1 := pow_orderOf_eq_one _

theorem jd_one (k N : ℕ) : jd 1 k N = 1 := by
  unfold jd
  rw [filter_true_of_mem (fun _ _ => by simp), card_tuples, xi_one, one_pow]

/-- (19) p.8: `j(d, k, N) ≤ ξ(d)^{k-1}` for odd `d` and `k ≥ 1`. -/
theorem eq19 {d : ℕ} (hd : Odd d) (k N : ℕ) : jd d (k + 1) N ≤ xi d ^ k := by
  unfold jd
  rw [← card_tuples k (xi d)]
  refine card_le_card_of_injOn (fun ν => Fin.tail ν) ?_ ?_
  · intro ν hν
    have hν' := (mem_filter.mp (mem_coe.mp hν)).1
    simp only [tuples, Fintype.mem_piFinset] at hν'
    rw [mem_coe, tuples, Fintype.mem_piFinset]
    exact fun i : Fin k => hν' i.succ
  · intro ν hν μ hμ htail
    simp only [mem_coe, mem_filter, tuples, Fintype.mem_piFinset, mem_Icc] at hν hμ
    simp only at htail
    have key : ν 0 = μ 0 := by
      have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr hν.2
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr hμ.2
      have hs : ∀ ρ : Fin (k + 1) → ℕ, (pow2sum ρ : ZMod d) =
          2 ^ ρ 0 + ∑ i : Fin k, 2 ^ Fin.tail ρ i := by
        intro ρ; simp [pow2sum, Fin.sum_univ_succ, Fin.tail]
      push_cast at h1 h2
      rw [hs] at h1 h2
      rw [htail] at h1
      have heq : (2 : ZMod d) ^ ν 0 = 2 ^ μ 0 := by linear_combination h2 - h1
      obtain ⟨a, ha⟩ : ∃ a, ν 0 = a + 1 := ⟨ν 0 - 1, by have := (hν.1 0).1; omega⟩
      obtain ⟨b, hb⟩ : ∃ b, μ 0 = b + 1 := ⟨μ 0 - 1, by have := (hμ.1 0).1; omega⟩
      rw [ha, hb, pow_succ, pow_succ] at heq
      have heq' : (2 : ZMod d) ^ a = 2 ^ b := (isUnit_two hd).mul_left_inj.mp heq
      have hab : a = b := by
        refine pow_injOn_Iio_orderOf ?_ ?_ heq'
        · show a < orderOf (2 : ZMod d); have := (hν.1 0).2; unfold xi at this; omega
        · show b < orderOf (2 : ZMod d); have := (hμ.1 0).2; unfold xi at this; omega
      omega
    rw [← Fin.cons_self_tail ν, ← Fin.cons_self_tail μ, key, htail]

/-! ### `C(k, N)` lies in `[1, 2]`, Theorem p.2, from Lemma 6.1 and Khalfallah-Pintz -/

open Classical in
/-- The term of (23). -/
def cTerm (k N d : ℕ) : ℝ := if OddSqf d then fd d * jd d k N / (xi d : ℝ) ^ k else 0

theorem Ckn_eq (k N : ℕ) : Ckn k N = ∑' d, cTerm k N d := rfl

theorem cTerm_nonneg (k N d : ℕ) : 0 ≤ cTerm k N d := by
  unfold cTerm; split_ifs
  · exact div_nonneg (mul_nonneg (fd_nonneg d) (Nat.cast_nonneg _)) (by positivity)
  · exact le_rfl

theorem cTerm_le (k N d : ℕ) : cTerm (k + 1) N d ≤ romanovTerm d := by
  unfold cTerm romanovTerm; split_ifs with h
  · have hx : (0 : ℝ) < xi d := by exact_mod_cast xi_pos h.1
    have hj : (jd d (k + 1) N : ℝ) ≤ (xi d : ℝ) ^ k := by exact_mod_cast eq19 h.1 k N
    rw [div_le_div_iff₀ (by positivity) hx, pow_succ]
    have := fd_nonneg d
    have : fd d * jd d (k + 1) N ≤ fd d * (xi d : ℝ) ^ k := mul_le_mul_of_nonneg_left hj this
    nlinarith
  · exact le_rfl

theorem cTerm_one (k N : ℕ) : cTerm k N 1 = 1 := by
  simp [cTerm, oddSqf_one, fd_one, jd_one, xi_one]

/-- (23) converges, by Lemma 6.1 and (19), as p.8 says. CONDITIONAL ON Lemma 6.1. -/
theorem Ckn_summable (h61 : Lemma61) (k N : ℕ) : Summable (cTerm (k + 1) N) :=
  Summable.of_nonneg_of_le (cTerm_nonneg _ _) (cTerm_le k N) h61

/-- `C(k, N) ≥ 1`: the `d = 1` term is `1`. CONDITIONAL ON Lemma 6.1. -/
theorem one_le_Ckn (h61 : Lemma61) (k N : ℕ) : 1 ≤ Ckn (k + 1) N := by
  rw [Ckn_eq, ← cTerm_one (k + 1) N]
  exact (Ckn_summable h61 k N).le_tsum 1 (fun j _ => cTerm_nonneg _ _ _)

/-- `C(k, N) ≤ Σ' f(d)/ξ(d)`. CONDITIONAL ON Lemma 6.1. -/
theorem Ckn_le_romanov (h61 : Lemma61) (k N : ℕ) : Ckn (k + 1) N ≤ ∑' d, romanovTerm d := by
  rw [Ckn_eq]
  exact Summable.tsum_le_tsum (cTerm_le k N) (Ckn_summable h61 k N) h61

/-- Theorem p.2: `C(k, N) ∈ [1, 2]`, indeed `≤ 1.9378`, for `k ≥ 1`.
CONDITIONAL ON Lemma 6.1 and the Khalfallah-Pintz bound. -/
theorem Ckn_mem (h61 : Lemma61) (hKP : KPBound) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    1 ≤ Ckn k N ∧ Ckn k N ≤ 1.9378 ∧ Ckn k N ≤ 2 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := (Ckn_le_romanov h61 k N).trans hKP
  exact ⟨one_le_Ckn h61 k N, h, h.trans (by norm_num)⟩

/-! ### Singular series and `R` -/

/-- The factor of `2c0` at `p`. -/
def gC0 (p : Nat.Primes) : ℝ := if (p : ℕ) = 2 then 1 else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2

theorem twoC0_eq : twoC0 = 2 * ∏' p, gC0 p := rfl

theorem gC0_multipliable : Multipliable gC0 := by
  set a : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then 0 else -(1 / (((p : ℕ) : ℝ) - 1) ^ 2)
    with ha
  have hfun : gC0 = fun p => 1 + a p := by
    funext p; simp only [ha, gC0]; split_ifs <;> ring
  rw [hfun]
  apply multipliable_one_add_of_summable
  have hs : Summable (fun p : Nat.Primes => 4 * (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Subtype.val_injective).mul_left 4
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hs
  simp only [ha]
  split_ifs with h2
  · rw [norm_zero]; positivity
  · have hp3 : 3 ≤ (p : ℕ) := by have := p.2.two_le; omega
    set q : ℝ := ((p : ℕ) : ℝ) with hq
    have hq3 : (3 : ℝ) ≤ q := by rw [hq]; exact_mod_cast hp3
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by nlinarith)]
    have : 4 * (1 / q ^ 2) * (q - 1) ^ 2 = (4 * (q - 1) ^ 2) / q ^ 2 := by ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith

/-- (2) p.2, PROVED: for even `n ≠ 0`, `𝔖(n) = 2c0 ∏_{p | n, p > 2} (p-1)/(p-2)`. -/
theorem eq2_proof : Eq2 := by
  intro n hn hn0
  have h2n : 2 ∣ n := even_iff_two_dvd.mp hn
  set f' : ℕ → ℝ := fun m => if m ∣ n then (if m = 2 then 2 else ((m : ℝ) - 1) / ((m : ℝ) - 2))
    else 1 with hf'
  let emb : {x // x ∈ n.primeFactors} ↪ Nat.Primes :=
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩, fun a b h => by
      apply Subtype.ext; have := congrArg Subtype.val h; simpa using this⟩
  set S : Finset Nat.Primes := n.primeFactors.attach.map emb with hS
  have hu : HasProd (fun p : Nat.Primes => f' p) (∏ p ∈ S, f' p) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    simp only [hf']
    rw [if_neg]; intro hd
    apply hp
    rw [hS, Finset.mem_map]
    exact ⟨⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hd, hn0⟩⟩, mem_attach _ _, rfl⟩
  have hterm : ∀ p : Nat.Primes, (if (p : ℕ) ∣ n then ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) = gC0 p * f' p := by
    intro p
    simp only [gC0, hf']
    by_cases hd : (p : ℕ) ∣ n
    · rw [if_pos hd, if_pos hd]
      by_cases h2 : (p : ℕ) = 2
      · rw [if_pos h2, if_pos h2, h2]; norm_num
      · rw [if_neg h2, if_neg h2]
        have hp3 : 3 ≤ (p : ℕ) := by have := p.2.two_le; omega
        set q : ℝ := ((p : ℕ) : ℝ) with hq
        have hq3 : (3 : ℝ) ≤ q := by rw [hq]; exact_mod_cast hp3
        have h1 : q - 1 ≠ 0 := by linarith
        have h2' : q - 2 ≠ 0 := by linarith
        field_simp
        ring
    · rw [if_neg hd, if_neg hd]
      have h2 : (p : ℕ) ≠ 2 := by rintro h; exact hd (h ▸ h2n)
      rw [if_neg h2, mul_one]
  have hsing : sing n = ∏' p : Nat.Primes, gC0 p * f' p := by
    unfold sing; exact tprod_congr hterm
  have hfin : ∏ p ∈ S, f' p =
      2 * ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [hS, Finset.prod_map]
    have hemb : ∀ x : {x // x ∈ n.primeFactors}, f' ((emb x : Nat.Primes) : ℕ) = f' x.1 :=
      fun x => rfl
    rw [prod_congr rfl (fun x _ => hemb x), Finset.prod_attach n.primeFactors (fun m : ℕ => f' m)]
    rw [← prod_filter_mul_prod_filter_not n.primeFactors (fun p => 2 < p)]
    have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn0⟩
    have hnot : n.primeFactors.filter (fun p => ¬ 2 < p) = {2} := by
      ext p
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hp, hlt⟩; have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
      · rintro rfl; exact ⟨h2mem, by omega⟩
    rw [hnot, prod_singleton, mul_comm]
    have h22 : f' 2 = 2 := by simp [hf', h2n]
    rw [h22]
    congr 1
    refine prod_congr rfl fun p hp => ?_
    simp only [mem_filter, Nat.mem_primeFactors] at hp
    simp only [hf', if_pos hp.1.2.1, if_neg (show p ≠ 2 by omega)]
  rw [hsing, gC0_multipliable.tprod_mul hu.multipliable, hu.tprod_eq, twoC0_eq, hfin]
  ring


/-- p.2: `𝔖(n) = 0` for odd `n`; the factor at `p = 2` is `1 - 1/1² = 0`. -/
theorem sing_odd {n : ℕ} (hn : ¬ 2 ∣ n) : sing n = 0 := by
  unfold sing
  refine (hasProd_zero_of_exists_eq_zero ⟨⟨2, Nat.prime_two⟩, ?_⟩).tprod_eq
  simp [hn]; norm_num

/-- p.3: `R(0) = 0`. -/
theorem Rg_zero (X : ℝ) : Rg X 0 = 0 := by
  unfold Rg
  refine sum_eq_zero fun m1 hm1 => sum_eq_zero fun m2 _ => ?_
  have := (mem_Icc.mp hm1).1
  rw [if_neg (by omega)]

theorem Rpp_nonneg (k : ℕ) (X : ℝ) (N : ℕ) : 0 ≤ Rpp k X N := by
  unfold Rpp
  refine sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => ?_
  split_ifs
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

/-- `t_k(N) ≤ ⌊L⌋^k`. -/
theorem tk_le (k : ℕ) (X : ℝ) (N : ℕ) : tk k X N ≤ ⌊Lg X⌋₊ ^ k :=
  (card_filter_le _ _).trans (card_tuples k _).le

/-! ### Links to the Linnik folder -/

/-- A power of two up to `X` has exponent at most `⌊log_2 X⌋`. -/
theorem le_floor_Lg {ν : ℕ} {X : ℝ} (h : (2 : ℝ) ^ ν ≤ X) : ν ≤ ⌊Lg X⌋₊ := by
  have hX : 0 < X := lt_of_lt_of_le (by positivity) h
  apply Nat.le_floor
  unfold Lg
  rw [le_logb_iff_rpow_le (by norm_num) hX, rpow_natCast]
  exact h

theorem pow_le_pow2sum {k : ℕ} (ν : Fin k → ℕ) (i : Fin k) : 2 ^ ν i ≤ pow2sum ν :=
  single_le_sum (f := fun j => 2 ^ ν j) (fun _ _ => Nat.zero_le _) (mem_univ i)

/-- `r''_k(N) > 0` exactly when `N` is two primes plus `k` powers of two, for `N ≤ X`. -/
theorem rpp_pos_iff {k N : ℕ} {X : ℝ} (hN : (N : ℝ) ≤ X) :
    0 < rpp k X N ↔ LeanLab.Linnik.LinnikExact k N := by
  unfold rpp
  rw [card_pos]
  constructor
  · rintro ⟨⟨⟨p, q⟩, ν⟩, hx⟩
    simp only [mem_filter, mem_product, tuples, Fintype.mem_piFinset, mem_Icc] at hx
    exact ⟨p, q, hx.2.1, hx.2.2.1, ν, fun i => (hx.1.2 i).1, hx.2.2.2⟩
  · rintro ⟨p, q, hp, hq, ν, hν, hN'⟩
    refine ⟨⟨⟨p, q⟩, ν⟩, ?_⟩
    simp only [mem_filter, mem_product, mem_range, tuples, Fintype.mem_piFinset, mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, fun i => ⟨hν i, le_floor_Lg ?_⟩⟩, hp, hq, hN'⟩
    have h1 : 2 ^ ν i ≤ N := (pow_le_pow2sum ν i).trans (by unfold pow2sum; omega)
    exact le_trans (by exact_mod_cast h1) hN

/-- A representation by primes gives `R''_k(N) > 0`, for `N ≤ X`. -/
theorem Rpp_pos_of_linnikExact {k N : ℕ} {X : ℝ} (hN : (N : ℝ) ≤ X)
    (h : LeanLab.Linnik.LinnikExact k N) : 0 < Rpp k X N := by
  obtain ⟨p, q, hp, hq, ν, hν, hN'⟩ := h
  have hpX : p ≤ ⌊X⌋₊ := Nat.le_floor (le_trans (by exact_mod_cast (by omega : p ≤ N)) hN)
  have hqX : q ≤ ⌊X⌋₊ := Nat.le_floor (le_trans (by exact_mod_cast (by omega : q ≤ N)) hN)
  have hνL : ν ∈ tuples k ⌊Lg X⌋₊ := by
    simp only [tuples, Fintype.mem_piFinset, mem_Icc]
    refine fun i => ⟨hν i, le_floor_Lg ?_⟩
    have h1 : 2 ^ ν i ≤ N := (pow_le_pow2sum ν i).trans (by unfold pow2sum; omega)
    exact le_trans (by exact_mod_cast h1) hN
  have hterm : ∀ (m1 m2 : ℕ) (μ : Fin k → ℕ),
      0 ≤ (if m1 + m2 + pow2sum μ = N then Λ m1 * Λ m2 else 0) := by
    intro m1 m2 μ; split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  unfold Rpp
  refine sum_pos' (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hterm _ _ _)
    ⟨p, mem_Icc.mpr ⟨hp.one_lt.le, hpX⟩, ?_⟩
  refine sum_pos' (fun _ _ => sum_nonneg fun _ _ => hterm _ _ _)
    ⟨q, mem_Icc.mpr ⟨hq.one_lt.le, hqX⟩, ?_⟩
  refine sum_pos' (fun _ _ => hterm _ _ _) ⟨ν, hνL, ?_⟩
  rw [if_pos (by unfold pow2sum; omega), ArithmeticFunction.vonMangoldt_apply_prime hp,
    ArithmeticFunction.vonMangoldt_apply_prime hq]
  exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
    (Real.log_pos (by exact_mod_cast hq.one_lt))

/-- The paper's (1) p.1, `r''_k(N) > 0` for all large even `N`, is the Linnik folder's
`AllLargeEven (LinnikExact k)`, with `X = N`. -/
theorem eq1_iff (k : ℕ) : LeanLab.Linnik.AllLargeEven (LeanLab.Linnik.LinnikExact k) ↔
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N → 0 < rpp k N N := by
  constructor
  · rintro ⟨N0, h⟩; exact ⟨N0, fun N he hN => (rpp_pos_iff le_rfl).mpr (h N he hN)⟩
  · rintro ⟨N0, h⟩; exact ⟨N0, fun N he hN => (rpp_pos_iff le_rfl).mp (h N he hN)⟩

/-- The paper's (1) with `k0 = 13`, p.2: CONDITIONAL ON `Linnik.heathBrownPuchta`, through
`Linnik.exact_mono`. -/
theorem eq1_of_hbp (h : LeanLab.Linnik.AllLargeEven (LeanLab.Linnik.LinnikExact 13)) {k : ℕ}
    (hk : 13 ≤ k) : ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N → 0 < rpp k N N :=
  (eq1_iff k).mp (LeanLab.Linnik.exact_mono hk h)

/-! ### (30): `X^L < exp(L²)` -/

/-- (30) p.10, second inequality: `X^L < exp(L²)` for `X > 1`, as `log 2 < 1`. -/
theorem xpow_Lg_lt_exp {X : ℝ} (hX : 1 < X) : X ^ Lg X < Real.exp (Lg X ^ 2) := by
  have hl : 0 < Real.log X := Real.log_pos hX
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hL : Real.log X = Lg X * Real.log 2 := by
    unfold Lg Real.logb; field_simp
  have hLpos : 0 < Lg X := by unfold Lg Real.logb; positivity
  rw [rpow_def_of_pos (by linarith), hL]
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_pos hLpos hLpos]

/-! ### Consequences of the main theorem -/

/-- If `|R - C N L^k| ≤ η N L^k` with `C ≥ 1`, `η < 1`, then `R > 0`. -/
theorem pos_of_bound {R C η N Lk : ℝ} (hC : 1 ≤ C) (hη : η < 1) (hN : 0 < N) (hL : 0 < Lk)
    (h : |R - C * N * Lk| ≤ η * N * Lk) : 0 < R := by
  have h1 := (abs_le.mp h).1
  have : 0 < N * Lk := mul_pos hN hL
  nlinarith

theorem Lg_pos {X : ℝ} (hX : 1 < X) : 0 < Lg X := by
  unfold Lg Real.logb; exact div_pos (Real.log_pos hX) (Real.log_pos (by norm_num))

open Classical in
/-- Almost every even `N ∈ J(X)` has `R''_k(N) > 0`, so is two prime powers plus `k` powers of
two: at most `B X^{3/5} (log X)^{10}` exceptions. CONDITIONAL ON `MainJ` and Lemma 6.1. -/
theorem few_Rpp_zero (hM : MainJ) (h61 : Lemma61) {k : ℕ} (hk : 1 ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧ Rpp k X N ≤ 0)).card : ℝ) ≤
        B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10 := by
  obtain ⟨B, hB, H⟩ := hM k hk
  obtain ⟨X0, H⟩ := H (1 / 2) (by norm_num)
  refine ⟨B, hB, max X0 2, fun X hX => le_trans ?_ (H X ((le_max_left _ _).trans hX))⟩
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Lg X ^ k := pow_pos (Lg_pos (by linarith)) k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hC := one_le_Ckn h61 j
  exact_mod_cast card_le_card fun N hN => by
    simp only [ExcJ, mem_filter, mem_Icc] at hN ⊢
    obtain ⟨⟨h1, h2⟩, he, hJ, hR⟩ := hN
    refine ⟨⟨h1, h2⟩, he, hJ, ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast h1
    have hc := hC N
    have hNL : 0 < (N : ℝ) * Lg X ^ (j + 1) := mul_pos hN0 hL
    rw [abs_sub_comm, abs_of_pos (by nlinarith)]
    nlinarith

/-! ### Section 5 p.9: (3), (7) and (25) give the main theorem -/

/-- `A log log X + 1 ≤ (η/2) √L` for large `X`. -/
theorem asymp_aux (A : ℝ) (hA : 0 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∃ Xa : ℝ, ∀ X : ℝ, Xa ≤ X → A * Real.log (Real.log X) + 1 ≤ η / 2 * √(Lg X) := by
  have hc : 0 < η / (4 * (A + 1)) := by positivity
  have h1 := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound hc
  have h2 := (tendsto_rpow_atTop (y := (1 / 2 : ℝ)) (by norm_num)).eventually_ge_atTop (4 / η)
  have h3 : ∀ᶠ u : ℝ in atTop, 1 ≤ u := eventually_ge_atTop 1
  have hu := (h1.and (h2.and h3))
  obtain ⟨Xa, HXa⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually hu)
  refine ⟨max Xa 3, fun X hX => ?_⟩
  obtain ⟨hb, hg, hu1⟩ := HXa X ((le_max_left _ _).trans hX)
  set u := Real.log X
  have hu0 : 0 ≤ u := by linarith
  have hs : u ^ (1 / 2 : ℝ) = √u := (Real.sqrt_eq_rpow u).symm
  rw [hs] at hb hg
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hb
  have hlog : Real.log u ≤ η / (4 * (A + 1)) * √u := (le_abs_self _).trans hb
  have hsq : √u ≤ √(Lg X) := by
    apply Real.sqrt_le_sqrt
    unfold Lg Real.logb
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    rw [le_div_iff₀ hl2]; nlinarith
  have hsu : 0 ≤ √u := Real.sqrt_nonneg _
  have hAlog : A * Real.log u ≤ η / 4 * √u := by
    calc A * Real.log u ≤ A * (η / (4 * (A + 1)) * √u) := mul_le_mul_of_nonneg_left hlog hA
      _ = η / 4 * √u * (A / (A + 1)) := by field_simp
      _ ≤ η / 4 * √u * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by linarith)]; linarith
      _ = η / 4 * √u := by ring
  have hone : 1 ≤ η / 4 * √u := by
    rw [div_le_iff₀ hη] at hg; nlinarith
  nlinarith

/-- Section 5 p.9: (3), (7) and (25) give the main theorem on `J(X)`. An implication, so
`lpz_main_J` is CONDITIONAL ON `eq3`, `eq7`, `eq25`. -/
theorem mainJ_of_sec5 (h3 : Eq3) (h7 : Eq7) (h25 : Eq25) : MainJ := by
  intro k hk
  obtain ⟨B7, X07, H7⟩ := h7 k hk
  obtain ⟨B1, X01, H3⟩ := h3 k hk
  obtain ⟨B2, η0, hη0, H25⟩ := h25 k hk
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(|B7| + 1) / Real.log 2 ^ 10, by positivity, fun η hη => ?_⟩
  set B2' := |B2| + 1 with hB2'
  have hB2'pos : 0 < B2' := by positivity
  set η2 := min (η0 / 2) (η / (4 * B2')) with hη2
  have hη2pos : 0 < η2 := lt_min (by linarith) (by positivity)
  have hη2lt : η2 < η0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hB2η : B2 * η2 ≤ η / 4 := by
    have h1 : B2 * η2 ≤ B2' * η2 :=
      mul_le_mul_of_nonneg_right (by rw [hB2']; linarith [le_abs_self B2]) hη2pos.le
    have h2 : B2' * η2 ≤ B2' * (η / (4 * B2')) := mul_le_mul_of_nonneg_left (min_le_right _ _)
      hB2'pos.le
    have h3 : B2' * (η / (4 * B2')) = η / 4 := by field_simp
    linarith
  obtain ⟨X025, H25'⟩ := H25 η2 hη2pos hη2lt
  obtain ⟨Xa, HA⟩ := asymp_aux |B1| (abs_nonneg _) hη
  refine ⟨max (max (max X07 X01) (max X025 Xa)) 6, fun X hX => ?_⟩
  have hX6 : 6 ≤ X := (le_max_right _ _).trans hX
  have hXm := (le_max_left _ _).trans hX
  have hX07 : X07 ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hXm)
  have hX01 : X01 ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hXm)
  have hX025 : X025 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hXm)
  have hXa : Xa ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hXm)
  obtain ⟨P, hP, HP⟩ := H25' X hX025
  have hLpos : 0 < Lg X := Lg_pos (by linarith)
  have hA := HA X hXa
  have hsub : ExcJ k X η ⊆ Exc7 k X P := by
    intro N hN
    simp only [ExcJ, Exc7, mem_filter, mem_Icc] at hN ⊢
    obtain ⟨hNI, he, hJ, hR⟩ := hN
    refine ⟨hNI, he, hJ, ?_⟩
    by_contra hlt
    push_neg at hlt
    have hN4 : (4 : ℝ) ≤ N := by
      have := hJ.1
      have h' : (4 : ℝ) ≤ 2 * X / 3 := by linarith
      linarith
    have hN0 : (0 : ℝ) < N := by linarith
    have hlogN : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hll0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlogN
    have hll : Real.log (Real.log N) ≤ Real.log (Real.log X) :=
      Real.log_le_log (by linarith) (Real.log_le_log hN0 hJ.2)
    set a := Lg X ^ ((k : ℝ) - 1 / 2) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos hLpos _
    have hak : a * √(Lg X) = Lg X ^ k := by
      rw [ha, Real.sqrt_eq_rpow, ← Real.rpow_add hLpos, ← Real.rpow_natCast]; congr 1; ring
    have e3 := H3 X hX01 P hP N he hJ
    have e25 := HP N he hJ
    set z1 := RMpp k X P N
    set z2 := Rmpp k X P N
    set c := Ckn k N * N * Lg X ^ k with hc
    have hz1 : |z1.re - c| ≤ ‖z1 - (Ckn k N * N * Lg X ^ k : ℂ)‖ := by
      have : z1.re - c = (z1 - (Ckn k N * N * Lg X ^ k : ℂ)).re := by
        rw [hc, ← Complex.ofReal_pow, Complex.sub_re]
        simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [this]; exact Complex.abs_re_le_norm _
    have hz2 : |z2.re| ≤ ‖z2‖ := Complex.abs_re_le_norm _
    have htri : |Rpp k X N - c| ≤ |Rpp k X N - (z1 + z2).re| + |z1.re - c| + |z2.re| := by
      have : Rpp k X N - c = (Rpp k X N - (z1 + z2).re) + (z1.re - c) + z2.re := by
        rw [Complex.add_re]; ring
      rw [this]
      exact abs_add_three _ _ _
    have hNa : 0 ≤ (N : ℝ) * a := by positivity
    have hB1 : B1 * N * a * Real.log (Real.log N) ≤ |B1| * N * a * Real.log (Real.log X) := by
      have i1 : B1 * (N * a * Real.log (Real.log N)) ≤ |B1| * (N * a * Real.log (Real.log N)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have i2 : |B1| * (N * a * Real.log (Real.log N)) ≤ |B1| * (N * a * Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hll hNa) (abs_nonneg _)
      nlinarith
    have hfin : |Rpp k X N - c| ≤ 3 / 4 * (η * N * Lg X ^ k) := by
      have s1 : |Rpp k X N - c| ≤ (|B1| * Real.log (Real.log X) + 1) * (N * a) +
          B2 * η2 * N * Lg X ^ k := by
        nlinarith
      have s2 : (|B1| * Real.log (Real.log X) + 1) * (N * a) ≤ η / 2 * √(Lg X) * (N * a) :=
        mul_le_mul_of_nonneg_right hA hNa
      have s3 : η / 2 * √(Lg X) * (N * a) = η / 2 * (N * Lg X ^ k) := by rw [← hak]; ring
      have hNL : 0 ≤ (N : ℝ) * Lg X ^ k := by positivity
      have s4 : B2 * η2 * N * Lg X ^ k ≤ η / 4 * (N * Lg X ^ k) := by
        have := mul_le_mul_of_nonneg_right hB2η hNL
        linarith
      nlinarith
    have hpos : 0 < η * N * Lg X ^ k := by positivity
    linarith
  have hc := card_le_card hsub
  have hcard : ((ExcJ k X η).card : ℝ) ≤ (Exc7 k X P).card := by exact_mod_cast hc
  have h7 := H7 X hX07 P hP
  have hLg : Lg X ^ 10 = Real.log X ^ 10 / Real.log 2 ^ 10 := by
    unfold Lg Real.logb; rw [div_pow]
  have hXp : 0 ≤ X ^ (3 / 5 : ℝ) * Lg X ^ 10 := by positivity
  calc ((ExcJ k X η).card : ℝ) ≤ B7 * X ^ (3 / 5 : ℝ) * Lg X ^ 10 := hcard.trans h7
    _ ≤ (|B7| + 1) * X ^ (3 / 5 : ℝ) * Lg X ^ 10 := by
        have : B7 ≤ |B7| + 1 := by linarith [le_abs_self B7]
        nlinarith
    _ = (|B7| + 1) / Real.log 2 ^ 10 * X ^ (3 / 5 : ℝ) * Real.log X ^ 10 := by
        rw [hLg]; ring

/- `mainJ_conditional : MainJ := mainJ_of_sec5 eq3 eq7 eq25` is retired, kept as text: `eq25`
is no longer cited, see Statements.lean and Repaired.lean, VERIFY U-0999. -/

end LeanLab.LPZ2007

