module

public import Mathlib
public import LeanLab.Linnik.U1474R0

/-!
Unit U-1537, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0035, J. Pintz and I. Z. Ruzsa 2020, On Linnik's approximation to Goldbach's problem II,
Acta Math. Hungar. Read from the PC copy copies/P0035.pdf, 14 pages, page numbers as printed;
page images of pp. 6, 7, 9, 11 checked for every display used here.

File a: Lemma 1 of p. 6, display (2.34), with its proof on p. 7, displays (2.35) to (2.40),
and the transfer from one class `H_i = {h : r_i | C(ε) h}` of (4.3), p. 9, to Lemma 1.

Lemma 1 is stated here in the general form needed by BOTH of its applications: the sum runs over
all `ν ∈ [1, L]` with `m - 2^ν ≠ 0`, and `m` is any integer with `|m| ≤ 2^{2L}`. The paper states
it for `0 < m ≤ N` and `2^ν < m`; that covers (4.5) on p. 9, where `m = 2^{ν₂}`, but the
application in (6.3) on p. 11 takes `m = 2^{ν₁} + ... + 2^{ν_k} - 2^{μ₁} - ... - 2^{μ_{k-1}}`,
which can be negative or exceed `N`. The proof of p. 7 works verbatim with `|m - 2^ν|`.

Notation. `kf d = k(d) = ∏_{p | d} 1/(p - 2)` on odd squarefree `d`, 0 otherwise, so the primed
sums of the paper are sums of `kf`; `xi d = ξ(d)`, the order of 2 mod `d`; `sfac h` is
`∏_{p | h, p > 2} (1 + 1/(p - 2))`, so that `𝔖(h) = 2 C₀ sfac h` for `h ≠ 0`, (2.13) p. 4.
`Aq m q L` is `A(m, q)/(2 C₀)` of (2.34) in the general form; `Pm m L = ∏ |m - 2^ν|`, (2.39).

Assemblies, CONDITIONAL ON the leaves of this file, no placeholder proof of their own:
* `lemma1_general`: Lemma 1, (2.34), in the general form above.
* `lemma1_class`: the per class bound used in (4.5) and (6.3): for one modulus `r` whose odd
  squarefree part is large, `∑_{ν : r | C (m - 2^ν)} sfac (m - 2^ν) ≤ η L`.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp1537a

open Finset Real

/-! ### Definitions, p. 4 and p. 7 -/

/-- `k(d) = ∏_{p | d, p > 2} 1/(p - 2)` for odd squarefree `d`, (2.35) p. 7, and `0` for other
`d`, so that `∑'` of the paper is a plain sum of `kf`. -/
noncomputable def kf (d : ℕ) : ℝ :=
  if Odd d ∧ Squarefree d then ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) else 0

/-- `ξ(d) = min {ν ≥ 1 : 2^ν ≡ 1 mod d}`, (2.35) p. 7, as the order of 2 in `ZMod d`. -/
noncomputable def xi (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- `∏_{p | h, p > 2} (1 + 1/(p - 2))`, the product in `𝔖(h)` of (2.13) p. 4. -/
noncomputable def sfac (h : ℤ) : ℝ :=
  ∏ p ∈ h.natAbs.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

/-- The exponents of (2.34): `ν ∈ [1, L]` with `m - 2^ν ≠ 0` and `q | m - 2^ν`. -/
def nus (m : ℤ) (q L : ℕ) : Finset ℕ :=
  (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (q : ℤ) ∣ m - 2 ^ ν)

/-- `A(m, q)/(2 C₀)` of (2.34) p. 6, general form: `∑_{ν ∈ nus} sfac (m - 2^ν)`. -/
noncomputable def Aq (m : ℤ) (q L : ℕ) : ℝ := ∑ ν ∈ nus m q L, sfac (m - 2 ^ ν)

/-- `P(m) = ∏_{ν ≤ L, m ≠ 2^ν} |m - 2^ν|`, (2.39) p. 7. -/
def Pm (m : ℤ) (L : ℕ) : ℕ :=
  ∏ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0), (m - 2 ^ ν).natAbs

/-- The odd squarefree part `r' = ∏_{p | r, p > 2} p`, (2.27) p. 5. -/
def oddSqf (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p

/-- `q = r'/(r', C)`: the odd squarefree modulus that `r | C h` forces to divide `h`. -/
def qOf (r C : ℕ) : ℕ := oddSqf r / Nat.gcd (oddSqf r) C

/-! ### Small proved facts -/

lemma kf_nonneg (d : ℕ) : 0 ≤ kf d := by
  unfold kf
  split_ifs with h
  · refine prod_nonneg fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr h.1) (even_iff_two_dvd.mpr hpd)
    have h3 : (3 : ℝ) ≤ p := by
      have := hpp.two_le
      exact_mod_cast (by omega : 3 ≤ p)
    exact div_nonneg zero_le_one (by linarith)
  · exact le_refl 0

lemma odd_of_kf_ne {d : ℕ} (h : kf d ≠ 0) : Odd d := by
  unfold kf at h
  split_ifs at h with h1
  · exact h1.1
  · exact absurd rfl h

lemma sfac_nonneg (h : ℤ) : 0 ≤ sfac h := by
  unfold sfac
  refine prod_nonneg fun p hp => ?_
  have h2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  have : 0 < 1 / ((p : ℝ) - 2) := one_div_pos.mpr (by linarith)
  linarith

lemma Pm_pos (m : ℤ) (L : ℕ) : 0 < Pm m L := by
  unfold Pm
  apply Finset.prod_pos
  intro ν hν
  exact Int.natAbs_pos.mpr (mem_filter.mp hν).2

/-! ### Leaves for Lemma 1, p. 7 -/

/-- LEAF. Unit U-1537. For `h ≠ 0`, `∏_{p | h, p > 2} (1 + 1/(p - 2)) = ∑'_{d | h} k(d)`, the sum
over odd squarefree divisors; this is how `𝔖(m - 2^ν)/(2C₀)` becomes the divisor sum in the first
inequality of (2.36) p. 7, and how `∑'_{d | P(m)} k(d)` becomes the product in (2.40) p. 7. -/
theorem sfac_eq_sum_kf (h : ℤ) (hh : h ≠ 0) :
    sfac h = ∑ d ∈ h.natAbs.divisors, kf d := by
  change sfac h = ∑ d ∈ h.natAbs.divisors, U1464Display20.wt d
  rw [← U1464Display20.prod_expand (Int.natAbs_ne_zero.mpr hh)]
  unfold sfac
  apply prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  field_simp [ne_of_gt (sub_pos.mpr hp2)]
  ring

/-- LEAF. Unit U-1537. The interchange in (2.36) p. 7: expanding each `sfac (m - 2^ν)` as a
divisor sum and swapping, `A(m, q)/(2C₀) = ∑_{d | P(m)} k(d) · #{ν ≤ L : m ≠ 2^ν, [d, q] | m - 2^ν}`;
every divisor of some `m - 2^ν ≠ 0` divides `P(m)`. -/
theorem Aq_eq_sum (m : ℤ) (q L : ℕ) :
    Aq m q L = ∑ d ∈ (Pm m L).divisors, kf d * ((nus m (Nat.lcm d q) L).card : ℝ) := by
  have hexpand : ∀ ν ∈ nus m q L, sfac (m - 2 ^ ν) =
      ∑ d ∈ (Pm m L).divisors, if (d : ℤ) ∣ m - 2 ^ ν then kf d else 0 := by
    intro ν hν
    have hν' := (mem_filter.mp hν).2
    rw [sfac_eq_sum_kf _ hν'.1, ← sum_filter]
    apply sum_congr
    · ext d
      simp only [mem_filter, Nat.mem_divisors, Int.natCast_dvd]
      constructor
      · rintro ⟨hd, _⟩
        refine ⟨⟨?_, (Pm_pos m L).ne'⟩, hd⟩
        exact hd.trans (dvd_prod_of_mem _ (mem_filter.mpr ⟨(mem_filter.mp hν).1, hν'.1⟩))
      · rintro ⟨_, hd⟩
        exact ⟨hd, Int.natAbs_ne_zero.mpr hν'.1⟩
    · intro d _
      rfl
  unfold Aq
  rw [sum_congr rfl hexpand, sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter]
  have hs : (nus m q L).filter (fun ν => (d : ℤ) ∣ m - 2 ^ ν) = nus m (Nat.lcm d q) L := by
    ext ν
    simp only [nus, mem_filter, Int.natCast_dvd, Nat.lcm_dvd_iff]
    aesop
  rw [hs, sum_const, nsmul_eq_mul, mul_comm]

/-- LEAF. Unit U-1537. For odd `n`, the `ν ∈ [1, L]` with `2^ν ≡ m mod n` lie in one class mod
`ξ(n)`, so there are at most `L/ξ(n) + 1` of them; second inequality of (2.36) p. 7. -/
theorem card_nus_le (m : ℤ) {n : ℕ} (L : ℕ) (hn : Odd n) :
    ((nus m n L).card : ℝ) ≤ L / xi n + 1 := by
  have he : 0 < orderOf (2 : ZMod n) := U1464Display20.eps_pos hn
  set s := (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (n : ℤ) ∣ m - 2 ^ ν)
  set e := orderOf (2 : ZMod n)
  have hfin : IsOfFinOrder (2 : ZMod n) := orderOf_pos_iff.mp he
  have key : ∀ a ∈ s, (2 : ZMod n) ^ a = (m : ZMod n) := by
    intro a ha
    have hh := (mem_filter.mp ha).2.2
    have hh' := (ZMod.intCast_eq_intCast_iff_dvd_sub (2 ^ a) m n).mpr hh
    simpa using hh'
  have hinj : Set.InjOn (fun a => a / e) (s : Set ℕ) := by
    intro a ha b hb hab
    have hmod : a % e = b % e := hfin.pow_inj_mod.mp ((key a ha).trans (key b hb).symm)
    have ha' := Nat.mod_add_div a e
    have hb' := Nat.mod_add_div b e
    change a / e = b / e at hab
    rw [hmod, hab] at ha'
    omega
  have hcard : s.card ≤ L / e + 1 := by
    calc s.card ≤ (range (L / e + 1)).card := card_le_card_of_injOn (fun a => a / e)
          (by
            intro a ha
            have haL := (mem_Icc.mp (mem_filter.mp ha).1).2
            exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right haL))) hinj
      _ = _ := card_range _
  calc (s.card : ℝ) ≤ (L / e + 1 : ℕ) := by exact_mod_cast hcard
    _ ≤ (L : ℝ) / e + 1 := by
      push_cast
      linarith [Nat.cast_div_le (α := ℝ) (m := L) (n := e)]

/-- LEAF. Unit U-1537. For odd `n` and `d | n`, `ξ(d) ≤ ξ(n)`, since `ξ(d) | ξ(n)`; used with
`n = [d, q]` for both `ξ([d, q]) ≥ ξ(q)` and `ξ([d, q]) ≥ ξ(d)` in (2.38) p. 7. -/
theorem xi_le_of_dvd {d n : ℕ} (hn : Odd n) (hd : d ∣ n) : xi d ≤ xi n := by
  have hpos : 0 < xi n := U1464Display20.eps_pos hn
  apply Nat.le_of_dvd hpos
  have hh := orderOf_map_dvd (ZMod.castHom hd (ZMod d)).toMonoidHom (2 : ZMod n)
  change orderOf ((ZMod.castHom hd (ZMod d)) (2 : ZMod n)) ∣ orderOf (2 : ZMod n) at hh
  rw [map_ofNat] at hh
  exact hh

/-- LEAF. Unit U-1537. `ξ(q) ≥ log₂ q` for odd `q`, since `q | 2^{ξ(q)} - 1`; the trivial bound
"ξ(m) ≥ log₂ m" stated before (2.38) p. 7. -/
theorem log_le_xi_mul {q : ℕ} (hq : Odd q) : Real.log q ≤ xi q * Real.log 2 := by
  have hxi : 0 < xi q := U1464Display20.eps_pos hq
  have hqpos : 0 < q := hq.pos
  have hpow : 1 < 2 ^ xi q := one_lt_pow₀ (by norm_num) (by omega)
  have hdvd : q ∣ 2 ^ xi q - 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rw [show (2 : ZMod q) ^ xi q = 1 from pow_orderOf_eq_one _, sub_self]
  have hqle : q ≤ 2 ^ xi q :=
    (Nat.le_of_dvd (Nat.sub_pos_of_lt hpow) hdvd).trans (Nat.sub_le _ _)
  calc Real.log q ≤ Real.log ((2 ^ xi q : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hqpos) (by exact_mod_cast hqle)
    _ = _ := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- LEAF. Unit U-1537. Romanov's series `∑' k(d)/ξ(d)` converges, the sentence after (2.37)
p. 7; its value is below 1.94 by (8.14) of part I. The lab's `U1474R0.r0Summable` proves the same
series summable with `wt = kf` and `eps = xi` by definition, so a prover can bridge to it. -/
theorem summable_kf_div_xi : Summable (fun d : ℕ => kf d / (xi d : ℝ)) := by
  change U1466Display17.R0Summable
  exact U1474R0.r0Summable

/-- LEAF. Unit U-1537. Choice of `D(η)` in (2.37) p. 7: the tail of a summable nonnegative series
is eventually below any `η > 0`, uniformly over finite sets beyond `D`. -/
theorem tail_small {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ d, 0 ≤ f d) {η : ℝ} (hη : 0 < η) :
    ∃ D : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, D < d) → ∑ d ∈ s, f d < η := by
  obtain ⟨t, ht⟩ := hf.vanishing (show Set.Iio η ∈ nhds (0 : ℝ) from Iio_mem_nhds hη)
  refine ⟨t.sup id, fun s hs => ht s ?_⟩
  refine disjoint_left.mpr fun d hd hdt => ?_
  have := le_sup (f := id) hdt
  exact (not_lt_of_ge this) (hs d hd)

/-- LEAF. Unit U-1537. The split at `D` in (2.38) p. 7: for odd `q`,
`∑_{d ∈ s} k(d)/ξ([d, q]) ≤ (∑_{d ≤ D} k(d))/ξ(q) + ∑_{d ∈ s, d > D} k(d)/ξ(d)`. -/
theorem sum_div_xi_lcm_le {q : ℕ} (hq : Odd q) (D : ℕ) (s : Finset ℕ) :
    ∑ d ∈ s, kf d / (xi (Nat.lcm d q) : ℝ) ≤
      (∑ d ∈ range (D + 1), kf d) / xi q + ∑ d ∈ s.filter (fun d => D < d), kf d / xi d := by
  have hpos : ∀ d, Odd d → 0 < xi d := fun d hd => U1464Display20.eps_pos hd
  have hterm : ∀ d, kf d / (xi (Nat.lcm d q) : ℝ) ≤
      if d ≤ D then kf d / xi q else kf d / xi d := by
    intro d
    by_cases hk : kf d = 0
    · simp [hk]
    have hd := odd_of_kf_ne hk
    have hlo : Odd (Nat.lcm d q) :=
      (hd.mul hq).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right d q) (dvd_mul_left q d))
    have hqle : (xi q : ℝ) ≤ xi (Nat.lcm d q) := by
      exact_mod_cast xi_le_of_dvd hlo (Nat.dvd_lcm_right d q)
    have hdle : (xi d : ℝ) ≤ xi (Nat.lcm d q) := by
      exact_mod_cast xi_le_of_dvd hlo (Nat.dvd_lcm_left d q)
    split_ifs
    · exact div_le_div_of_nonneg_left (kf_nonneg d) (by exact_mod_cast hpos q hq) hqle
    · exact div_le_div_of_nonneg_left (kf_nonneg d) (by exact_mod_cast hpos d hd) hdle
  calc _ ≤ ∑ d ∈ s, if d ≤ D then kf d / xi q else kf d / xi d := sum_le_sum fun d _ => hterm d
    _ = (∑ d ∈ s.filter (fun d => d ≤ D), kf d) / xi q +
        ∑ d ∈ s.filter (fun d => D < d), kf d / xi d := by
      rw [sum_ite, sum_div]
      simp only [not_le]
    _ ≤ _ := by
      refine add_le_add ?_ le_rfl
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_range.mpr (by have := (mem_filter.mp hd).2; omega)
      · intro d _ _
        exact kf_nonneg d

/-- LEAF. Unit U-1537. (2.39) p. 7 in the general form: if `|m| ≤ 2^{2L}` then
`P(m) = ∏ |m - 2^ν| ≤ (2^{2L+1})^L`, so `log P(m) ≪ L²`. -/
theorem Pm_le {m : ℤ} {L : ℕ} (hm : |m| ≤ 2 ^ (2 * L)) : Pm m L ≤ 2 ^ ((2 * L + 1) * L) := by
  unfold Pm
  have hb : ∀ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0),
      (m - 2 ^ ν).natAbs ≤ 2 ^ (2 * L + 1) := by
    intro ν hν
    have hνL := (mem_Icc.mp (mem_filter.mp hν).1).2
    have hpow : (2 : ℤ) ^ ν ≤ 2 ^ (2 * L) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hab : |m - 2 ^ ν| ≤ (2 : ℤ) ^ (2 * L + 1) := by
      calc |m - 2 ^ ν| ≤ |m| + |(2 : ℤ) ^ ν| := abs_sub _ _
        _ ≤ 2 ^ (2 * L) + 2 ^ (2 * L) := by simpa using add_le_add hm hpow
        _ = _ := by rw [pow_succ]; ring
    have hh : ((m - 2 ^ ν).natAbs : ℤ) ≤ (2 : ℤ) ^ (2 * L + 1) := by
      simpa only [Int.natCast_natAbs] using hab
    exact_mod_cast hh
  calc _ ≤ (2 ^ (2 * L + 1)) ^ ((Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0)).card :=
      prod_le_pow_card _ _ _ hb
    _ ≤ (2 ^ (2 * L + 1)) ^ L := by
      apply Nat.pow_le_pow_right (by positivity)
      exact (card_filter_le _ _).trans (by simp [Nat.card_Icc])
    _ = _ := by rw [← pow_mul]

/-- LEAF. Unit U-1537. The primes `p > L³` in (2.40) p. 7: if `0 < P ≤ 2^{(2L+1)L}` and `L ≥ 2`,
then `P` has at most `3L²` prime factors, each above `L³`, so
`∏_{p | P, p > 2, p > L³} (1 + 1/(p - 2)) ≤ exp(6/L) ≤ e³`. -/
theorem large_prime_prod_le {L P : ℕ} (hL : 2 ≤ L) (hP : 0 < P)
    (hPle : P ≤ 2 ^ ((2 * L + 1) * L)) :
    ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2)) ≤ Real.exp 3 := by
  have hcard := U1466Display17.card_pf_le hP.ne' hPle
  set s := (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3)
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLsq : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hc : s.card ≤ 3 * L ^ 2 := by
    have hs : s.card ≤ P.primeFactors.card :=
      card_le_card ((filter_subset _ _).trans (filter_subset _ _))
    nlinarith
  have hb : ∀ p ∈ s, 1 / ((p : ℝ) - 2) ≤ 1 / (L : ℝ) ^ 2 := by
    intro p hp
    have hpx : L ^ 3 + 1 ≤ p := by
      have := (mem_filter.mp hp).2
      omega
    have hpxr : (L : ℝ) ^ 3 + 1 ≤ p := by exact_mod_cast hpx
    have hden : (L : ℝ) ^ 2 ≤ (p : ℝ) - 2 := by
      nlinarith [mul_nonneg (show 0 ≤ (L : ℝ) - 2 by linarith) (sq_nonneg (L : ℝ)),
        sq_nonneg ((L : ℝ) - 1)]
    exact div_le_div_of_nonneg_left zero_le_one hLsq hden
  calc _ ≤ ∏ p ∈ s, Real.exp (1 / ((p : ℝ) - 2)) := by
        apply prod_le_prod₀
        · intro p hp
          have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2
          positivity
        · intro p _
          linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 2))]
    _ = Real.exp (∑ p ∈ s, 1 / ((p : ℝ) - 2)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 3 := by
      apply Real.exp_le_exp.mpr
      calc ∑ p ∈ s, 1 / ((p : ℝ) - 2) ≤ ∑ _p ∈ s, 1 / (L : ℝ) ^ 2 := sum_le_sum hb
        _ = (s.card : ℝ) / (L : ℝ) ^ 2 := by simp [div_eq_mul_inv]
        _ ≤ 3 := by
          apply (div_le_iff₀ hLsq).mpr
          exact_mod_cast hc

/-- LEAF. Unit U-1537. The primes `p ≤ L³` in (2.40) p. 7: the product over odd prime factors
`p ≤ x` of `P` is at most the product over all odd primes `p ≤ x`, all factors being `≥ 1`. -/
theorem small_prime_prod_le (P x : ℕ) :
    ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ x),
      (1 + 1 / ((p : ℝ) - 2)) ≤
    ∏ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
  apply prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    obtain ⟨hp, hpx⟩ := mem_filter.mp hp
    obtain ⟨hp, hp2⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors hp, hp2⟩
  · intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2
    positivity
  · intro p hp _
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.2
    have : 0 ≤ 1 / ((p : ℝ) - 2) := by positivity
    linarith

/-- LEAF. Unit U-1537. Mertens: `∏_{2 < p ≤ x} (1 + 1/(p - 2)) ≤ C log x` for `x ≥ 2`, the step
`∑_{p ≤ L³} 1/p ≤ log log L + O(1)` of (2.40) p. 7, and also the bound `∑_{d ≤ x} k(d) ≤ C log x`
before (2.38). Since `1 + 1/(p - 2) = (p - 1)/(p - 2)` this is the lab's `MertensProd`, proved in
`U1469Mertens.mertensProd` with `C = e^24`. -/
theorem mertens_prod : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∏ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ 2 < p), (1 + 1 / ((p : ℝ) - 2)) ≤
      C * Real.log x := by
  obtain ⟨C, hC⟩ := U1469Mertens.mertensProd
  refine ⟨C, fun x hx => ?_⟩
  calc _ = ∏ p ∈ U1466Display17.oddPrimesUpTo x, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        apply prod_congr rfl
        intro p hp
        have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.2
        field_simp [ne_of_gt (sub_pos.mpr hp2)]
        ring
    _ ≤ C * Real.log x := hC x hx

/-- LEAF. Unit U-1537. `log L = o(L)`, the last line of (2.40) p. 7: for every `c > 0`,
`log L ≤ c L` for all large natural `L`. -/
theorem log_le_mul_eventually {c : ℝ} (hc : 0 < c) :
    ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → Real.log L ≤ c * L := by
  have h := Real.isLittleO_log_id_atTop.bound hc
  have hnat := Filter.Tendsto.eventually (show Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop from tendsto_natCast_atTop_atTop) h
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨L0, fun L hL => ?_⟩
  have hh := hL0 L hL
  change |Real.log (L : ℝ)| ≤ c * |(L : ℝ)| at hh
  rw [abs_of_nonneg (show (0 : ℝ) ≤ L from Nat.cast_nonneg L)] at hh
  exact (le_abs_self _).trans hh

/-! ### Leaves for the classes `H_i` of (4.3), p. 9 -/

/-- LEAF. Unit U-1537. If `r | C h` then `q = r'/(r', C)` divides `h`, where `r'` is the odd
squarefree part of `r`; this is how `h ∈ H_i`, (4.3) p. 9, i.e. `r_i | C(ε) h`, puts `h` into
the range of Lemma 1, whose modulus must be odd squarefree, p. 6. -/

lemma oddSqf_dvd_r (r : ℕ) : oddSqf r ∣ r := by
  unfold oddSqf
  have hdvd : ∏ p ∈ r.primeFactors, p ∣ r := Nat.prod_primeFactors_dvd r
  apply dvd_trans _ hdvd
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hp.1

lemma oddSqf_pos (r : ℕ) : 0 < oddSqf r := by
  unfold oddSqf
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact Nat.pos_of_ne_zero (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp.1))

theorem qOf_dvd {r C : ℕ} {h : ℤ} (hr : 0 < r) (hdvd : (r : ℤ) ∣ C * h) :
    (qOf r C : ℤ) ∣ h := by
  have hd : (oddSqf r : ℤ) ∣ C * h :=
    (Int.natCast_dvd_natCast.mpr (oddSqf_dvd_r r)).trans hdvd
  have hnat : oddSqf r ∣ C * h.natAbs := by
    simpa only [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] using hd
  have hmod : C * h.natAbs ≡ C * 0 [MOD oddSqf r] := by
    simpa only [mul_zero] using Nat.modEq_zero_iff_dvd.mpr hnat
  have hh := hmod.cancel_left_div_gcd (oddSqf_pos r)
  exact Int.natCast_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hh)

/-- LEAF. Unit U-1537. `q = r'/(r', C)` is odd, as a divisor of the odd number `r'`; Lemma 1
p. 6 needs an odd modulus. -/
theorem qOf_odd (r C : ℕ) : Odd (qOf r C) := by
  have ho : Odd (oddSqf r) := by
    unfold oddSqf
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro htwo
    obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp htwo
    obtain ⟨hp, hp2⟩ := mem_filter.mp hp
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_of_mem_primeFactors hp)).mp h2p
    omega
  exact ho.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))

/-- LEAF. Unit U-1537. `r' ≤ q · C` for `C ≥ 1`, so `q ≥ r'/C` is large when `r'` is, by (2.27)
p. 5; this is the "min(q, N) > C₀(η)" of Lemma 1 p. 6 for `q = r'/(r', C(ε))`. -/
theorem le_qOf_mul (r C : ℕ) (hC : 0 < C) : oddSqf r ≤ qOf r C * C := by
  have he := Nat.div_mul_cancel (Nat.gcd_dvd_left (oddSqf r) C)
  have hg : Nat.gcd (oddSqf r) C ≤ C := Nat.le_of_dvd hC (Nat.gcd_dvd_right _ _)
  change oddSqf r ≤ oddSqf r / Nat.gcd (oddSqf r) C * C
  calc oddSqf r = oddSqf r / Nat.gcd (oddSqf r) C * Nat.gcd (oddSqf r) C := he.symm
    _ ≤ _ := Nat.mul_le_mul_left _ hg

/-! ### Assemblies -/

/-- **Lemma 1, (2.34) p. 6, general form. CONDITIONAL ON the leaves above.** For every `η > 0`
there are `Q₀, L₀` with `A(m, q)/(2C₀) ≤ η L` whenever `L ≥ L₀`, `q ≥ Q₀` is odd and
`|m| ≤ 2^{2L}`. The proof is the paper's: (2.36), (2.37), (2.38), then (2.39), (2.40). -/
theorem lemma1_general {η : ℝ} (hη : 0 < η) :
    ∃ Q0 L0 : ℕ, ∀ L q : ℕ, L0 ≤ L → Q0 ≤ q → Odd q → ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
      Aq m q L ≤ η * L := by
  obtain ⟨D, hD⟩ := tail_small summable_kf_div_xi
    (fun d => div_nonneg (kf_nonneg d) (Nat.cast_nonneg _)) (by positivity : 0 < η / 8)
  set K := ∑ d ∈ range (D + 1), kf d with hK
  have hK0 : 0 ≤ K := sum_nonneg fun d _ => kf_nonneg d
  obtain ⟨C, hC⟩ := mertens_prod
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have he3 : 0 < Real.exp 3 := Real.exp_pos 3
  obtain ⟨L1, hL1⟩ := log_le_mul_eventually (c := η / (6 * C' * Real.exp 3)) (by positivity)
  obtain ⟨Q0, hQ0⟩ := exists_nat_gt (Real.exp (8 * K * Real.log 2 / η))
  refine ⟨Q0, max L1 2, ?_⟩
  intro L q hL hq hqodd m hm
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLL1 : L1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set P := Pm m L with hPdef
  have hP0 : 0 < P := Pm_pos m L
  -- (2.36): divisor expansion, interchange, and the count of `ν`
  have step1 : Aq m q L ≤
      ∑ d ∈ P.divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d q)) + kf d) := by
    rw [Aq_eq_sum]
    apply sum_le_sum
    intro d _
    by_cases hk : kf d = 0
    · simp [hk]
    · have hdodd := odd_of_kf_ne hk
      have hlo : Odd (Nat.lcm d q) :=
        (hdodd.mul hqodd).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right d q) (dvd_mul_left q d))
      have hc := card_nus_le m L hlo
      have hk0 := kf_nonneg d
      calc kf d * ((nus m (Nat.lcm d q) L).card : ℝ)
          ≤ kf d * ((L : ℝ) / xi (Nat.lcm d q) + 1) := mul_le_mul_of_nonneg_left hc hk0
        _ = kf d * ((L : ℝ) / xi (Nat.lcm d q)) + kf d := by ring
  have step2 : ∑ d ∈ P.divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d q)) + kf d) =
      (L : ℝ) * ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) + ∑ d ∈ P.divisors, kf d := by
    rw [sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro d _
    ring
  -- Σ₂ is the product of (2.40)
  have hS2 : ∑ d ∈ P.divisors, kf d = sfac (P : ℤ) := by
    rw [sfac_eq_sum_kf (P : ℤ) (by exact_mod_cast hP0.ne')]
    simp
  -- (2.37), (2.38)
  have hS1 : ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) ≤ K / xi q + η / 8 := by
    have h8 := sum_div_xi_lcm_le hqodd D P.divisors
    have h9 := hD (P.divisors.filter (fun d => D < d)) (fun d hd => (mem_filter.mp hd).2)
    linarith
  have hxi : K / xi q ≤ η / 8 := by
    have hq1 : (Q0 : ℝ) ≤ q := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (lt_trans (Real.exp_pos _) hQ0) hq1
    have hlogq : 8 * K * Real.log 2 / η < Real.log q := by
      rw [Real.lt_log_iff_exp_lt hqpos]
      linarith
    have hl5 := log_le_xi_mul hqodd
    have hlog2 := Real.log_pos one_lt_two
    have h0 : 0 ≤ 8 * K * Real.log 2 / η := by positivity
    have hlq_pos : 0 < Real.log q := lt_of_le_of_lt h0 hlogq
    have hxi_pos : (0 : ℝ) < xi q := by
      rcases le_or_gt (xi q : ℝ) 0 with hcon | hcon
      · have : (xi q : ℝ) * Real.log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hlog2.le
        linarith
      · exact hcon
    rw [div_le_iff₀ hxi_pos]
    have h1 : 8 * K * Real.log 2 < Real.log q * η := (div_lt_iff₀ hη).mp hlogq
    have h2 : 8 * K * Real.log 2 < η * (xi q * Real.log 2) := by
      calc 8 * K * Real.log 2 < Real.log q * η := h1
        _ ≤ (xi q * Real.log 2) * η := mul_le_mul_of_nonneg_right hl5 hη.le
        _ = η * (xi q * Real.log 2) := by ring
    have h3 : K * Real.log 2 < (η / 8 * xi q) * Real.log 2 := by linarith
    exact (lt_of_mul_lt_mul_right h3 hlog2.le).le
  -- (2.39), (2.40)
  have hsfac : sfac (P : ℤ) ≤ η / 2 * L := by
    have hPle : P ≤ 2 ^ ((2 * L + 1) * L) := Pm_le hm
    have hnat : (P : ℤ).natAbs = P := Int.natAbs_natCast P
    unfold sfac
    rw [hnat, ← prod_filter_mul_prod_filter_not (P.primeFactors.filter (fun p => 2 < p))
      (fun p => p ≤ L ^ 3)]
    have hsmall := small_prime_prod_le P (L ^ 3)
    have hL3 : 2 ≤ L ^ 3 := le_trans hL2 (Nat.le_self_pow (by norm_num) L)
    have hmert := hC (L ^ 3) hL3
    have hlogL3 : Real.log ((L ^ 3 : ℕ) : ℝ) = 3 * Real.log L := by
      push_cast
      rw [Real.log_pow]
      norm_num
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
    have hlarge := large_prime_prod_le hL2 hP0 hPle
    have hfac_nonneg : ∀ s : Finset ℕ, (∀ p ∈ s, 2 < p) →
        0 ≤ ∏ p ∈ s, (1 + 1 / ((p : ℝ) - 2)) := by
      intro s hs
      refine prod_nonneg fun p hp => ?_
      have h2 : (2 : ℝ) < p := by exact_mod_cast hs p hp
      have : 0 < 1 / ((p : ℝ) - 2) := one_div_pos.mpr (by linarith)
      linarith
    have hA0 := hfac_nonneg ((P.primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ L ^ 3))
      (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    have hB0 := hfac_nonneg
      ((P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3))
      (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    set Asm := ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2))
    set Blg := ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2))
    have hAsm : Asm ≤ C' * (3 * Real.log L) := by
      calc Asm ≤ _ := hsmall
        _ ≤ C * Real.log ((L ^ 3 : ℕ) : ℝ) := hmert
        _ = C * (3 * Real.log L) := by rw [hlogL3]
        _ ≤ C' * (3 * Real.log L) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hlogc := hL1 L hLL1
    calc Asm * Blg ≤ (C' * (3 * Real.log L)) * Real.exp 3 :=
          mul_le_mul hAsm hlarge hB0 (by positivity)
      _ = 3 * C' * Real.exp 3 * Real.log L := by ring
      _ ≤ 3 * C' * Real.exp 3 * (η / (6 * C' * Real.exp 3) * L) :=
          mul_le_mul_of_nonneg_left hlogc (by positivity)
      _ = η / 2 * L := by field_simp; ring
  calc Aq m q L ≤ (L : ℝ) * ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) +
        ∑ d ∈ P.divisors, kf d := by rw [← step2]; exact step1
    _ ≤ (L : ℝ) * (η / 8 + η / 8) + η / 2 * L := by
        rw [hS2]
        have : ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) ≤ η / 8 + η / 8 := by linarith
        have := mul_le_mul_of_nonneg_left this hLpos
        linarith
    _ ≤ η * L := by nlinarith

/-- **The per class bound of (4.5) p. 9 and (6.3) p. 11. CONDITIONAL ON the leaves above.**
For every `η > 0` there are `T, L₀` such that, for `L ≥ L₀`, any modulus `r` and constant
`C ≥ 1` with `T C ≤ r'`, the odd squarefree part, and any `|m| ≤ 2^{2L}`,
`∑_{ν ≤ L, m ≠ 2^ν, r | C (m - 2^ν)} sfac(m - 2^ν) ≤ η L`. In the paper `r = r_i`,
`C = C(ε)`, and `r_i' ≫ L²` by (2.27) p. 5 makes `T C ≤ r_i'` hold for large `N`. -/
theorem lemma1_class {η : ℝ} (hη : 0 < η) :
    ∃ T L0 : ℕ, ∀ L : ℕ, L0 ≤ L → ∀ r C : ℕ, 0 < r → 0 < C → T * C ≤ oddSqf r →
      ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
        ∑ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (r : ℤ) ∣ C * (m - 2 ^ ν)),
          sfac (m - 2 ^ ν) ≤ η * L := by
  obtain ⟨Q0, L0, h⟩ := lemma1_general hη
  refine ⟨Q0, L0, fun L hL r C hr hC hT m hm => ?_⟩
  have hq : Q0 ≤ qOf r C :=
    Nat.le_of_mul_le_mul_right (hT.trans (le_qOf_mul r C hC)) hC
  calc _ ≤ Aq m (qOf r C) L := by
        unfold Aq nus
        apply sum_le_sum_of_subset_of_nonneg
        · intro ν hν
          simp only [mem_filter] at hν ⊢
          exact ⟨hν.1, hν.2.1, qOf_dvd hr hν.2.2⟩
        · intro ν _ _
          exact sfac_nonneg _
    _ ≤ η * L := h L _ hL hq (qOf_odd r C) m hm

open LeanLab.Linnik.U1464Display20 in
/-- P0035 p.7 before display 2.38. The partial sums of k are bounded by a constant times log x. -/
theorem sum_kf_le_log : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∑ d ∈ range (x + 1), kf d ≤ C * Real.log x := by
  change ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∑ d ∈ range (x + 1), wt d ≤ C * Real.log x
  obtain ⟨C, hC⟩ := U1469Mertens.mertensProd
  refine ⟨C, fun x hx => ?_⟩
  set s := U1466Display17.oddPrimesUpTo x
  set P := ∏ p ∈ s, p
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (mem_filter.mp hp).2.1
  have hP : P ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact (hs p hp).ne_zero
  have hpf : P.primeFactors = s := Nat.primeFactors_prod hs
  have hsum : ∑ d ∈ range (x + 1), wt d ≤ ∑ d ∈ P.divisors, wt d := by
    rw [← sum_filter_ne_zero (range (x + 1))]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdx, hkd⟩ := mem_filter.mp hd
      have hd' : Odd d ∧ Squarefree d := by
        by_contra hh
        exact hkd (by simp [wt, hh])
      have hsub : d.primeFactors ⊆ s := by
        intro p hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        have hple := Nat.le_of_dvd hd'.1.pos hpd
        have hp3 := U1464Display20.three_le_of_mem hd'.1 hp
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hdx; omega),
          Nat.prime_of_mem_primeFactors hp, by omega⟩
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hP⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd'.2]
      exact prod_dvd_prod_of_subset _ _ _ hsub
    · intro d _ _
      exact wt_nonneg d
  have hprod : ∑ d ∈ P.divisors, wt d =
      ∏ p ∈ s, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [← U1464Display20.prod_expand hP, hpf]
    congr 1
    exact filter_eq_self.mpr fun p hp => (mem_filter.mp hp).2.2
  exact hsum.trans (hprod ▸ hC x hx)

/-- P0035 p.7 display 2.40 in the general form of this file. The divisor product is uniformly logarithmic in L. -/
theorem sfac_Pm_le_log : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 2 ≤ L → ∀ m : ℤ,
    |m| ≤ 2 ^ (2 * L) → sfac (Pm m L : ℤ) ≤ C * Real.log L := by
  obtain ⟨A, hA⟩ := mertens_prod
  refine ⟨3 * max A 1 * Real.exp 3, by positivity, fun L hL m hm => ?_⟩
  have hLlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
  have hL3 : 2 ≤ L ^ 3 := le_trans hL (Nat.le_self_pow (by norm_num) L)
  have hlog : Real.log ((L ^ 3 : ℕ) : ℝ) = 3 * Real.log L := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hsmall := (small_prime_prod_le (Pm m L) (L ^ 3)).trans (hA (L ^ 3) hL3)
  have hAsm : ∏ p ∈ ((Pm m L).primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2)) ≤ max A 1 * (3 * Real.log L) := by
    calc _ ≤ A * Real.log ((L ^ 3 : ℕ) : ℝ) := hsmall
      _ = A * (3 * Real.log L) := by rw [hlog]
      _ ≤ max A 1 * (3 * Real.log L) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hlarge := large_prime_prod_le hL (Pm_pos m L) (Pm_le hm)
  have hB0 : 0 ≤ ∏ p ∈ ((Pm m L).primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2)) := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2
    positivity
  unfold sfac
  rw [Int.natAbs_natCast, ← prod_filter_mul_prod_filter_not
    ((Pm m L).primeFactors.filter (fun p => 2 < p)) (fun p => p ≤ L ^ 3)]
  calc _ ≤ (max A 1 * (3 * Real.log L)) * Real.exp 3 :=
      mul_le_mul hAsm hlarge hB0 (by positivity)
    _ = (3 * max A 1 * Real.exp 3) * Real.log L := by ring

/-- P0035 p.7 last line of display 2.40 in the general form of this file. The divisor product is uniformly small compared with L. -/
theorem sfac_Pm_small {η : ℝ} (hη : 0 < η) : ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → ∀ m : ℤ,
    |m| ≤ 2 ^ (2 * L) → sfac (Pm m L : ℤ) ≤ η * L := by
  obtain ⟨C, hC, hbound⟩ := sfac_Pm_le_log
  obtain ⟨L0, hL0⟩ := log_le_mul_eventually (c := η / C) (div_pos hη hC)
  refine ⟨max L0 2, fun L hL m hm => ?_⟩
  calc sfac (Pm m L : ℤ) ≤ C * Real.log L :=
      hbound L ((le_max_right _ _).trans hL) m hm
    _ ≤ C * (η / C * L) := mul_le_mul_of_nonneg_left
      (hL0 L ((le_max_left _ _).trans hL)) hC.le
    _ = η * L := by field_simp

end LeanLab.Linnik.Decomp1537a
