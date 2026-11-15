module

public import LeanLab.Tolev2009.Decomp314b
public import LeanLab.Tolev2009.CRT355

/-!
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 12 to 18.
Finite CRT domination is proved. The local prime product estimate is proved.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Decomp355a
open LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Decomp314b

/-- Halupczok page 18, the three pairwise gcds divided by the common gcd. -/
noncomputable def gcdWeight (k : Fin 3 → ℕ) : ℝ :=
  ((Nat.gcd (k 0) (k 1) : ℝ) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) /
    Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)

/-- Halupczok page 18, the residue independent coefficient envelope before totients. -/
noncomputable def rawWeight (k : Fin 3 → ℕ) : ℝ :=
  gcdWeight k * ∏ i : Fin 3, ((k i).divisors.card : ℝ) ^ 4

/-- Halupczok pages 16 to 17, a finite product of prime power first moments.
The exponent cutoff Q contains every prime power dividing an integer at most Q. -/
noncomputable def primeProduct (k l : Fin 3 → ℕ) (N Q : ℕ) : ℝ :=
  ∏ p ∈ (range (Q + 1)).filter Nat.Prime,
    (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖)

/-- Halupczok pages 12 to 14, Propositions 1 and 2 with the totient factors.
This is the finite CRT multiplicativity identity for the explicit coefficient. -/
theorem ssTerm_multiplicative (k l : Fin 3 → ℕ) (N m n : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    ssTerm k l N (m * n) = ssTerm k l N m * ssTerm k l N n := by
  exact CRT355.ssTerm_mul k l N m n hk hl hm hn hmn

/-- Halupczok page 16, a finite Euler bound for any nonnegative multiplicative function. -/
theorem finite_euler_bound (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hf0 : ∀ n, 0 ≤ f n) (Q : ℕ) :
    ∑ n ∈ Icc 1 Q, f n ≤
      ∏ p ∈ (range (Q + 1)).filter Nat.Prime, (1 + ∑ j ∈ Icc 1 Q, f (p ^ j)) := by
  let P := (range (Q + 1)).filter Nat.Prime
  let M := ∏ p ∈ P, p ^ Q
  have hp (p : ℕ) (h : p ∈ P) : p.Prime := (mem_filter.mp h).2
  have hM : M ≠ 0 := by
    exact prod_ne_zero_iff.mpr (fun p h => pow_ne_zero _ (hp p h).ne_zero)
  have hsub : Icc 1 Q ⊆ M.divisors := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hP : n.primeFactors ⊆ P := by
      intro p hpn
      refine mem_filter.mpr ⟨mem_range.mpr ?_, Nat.prime_of_mem_primeFactors hpn⟩
      have hpn' := Nat.le_of_dvd (by omega : 0 < n) (Nat.dvd_of_mem_primeFactors hpn)
      have := (mem_Icc.mp hn).2
      omega
    have hd := Nat.dvd_prod_primeFactors_pow_self hn0
    rw [← prod_pow] at hd
    apply Nat.mem_divisors.mpr ⟨hd.trans ?_, hM⟩
    apply dvd_trans (prod_dvd_prod_of_dvd _ _ (fun p _ => pow_dvd_pow p (mem_Icc.mp hn).2))
    exact prod_dvd_prod_of_subset _ _ _ hP
  have hpair : (P : Set ℕ).Pairwise (fun p q => Nat.Coprime (p ^ Q) (q ^ Q)) := by
    intro p hp' q hq' hpq
    exact ((Nat.coprime_primes (hp p hp') (hp q hq')).mpr hpq).pow Q Q
  calc
    _ ≤ ∑ n ∈ M.divisors, f n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
    _ = (f * ArithmeticFunction.zeta) M := by rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = ∏ p ∈ P, (f * ArithmeticFunction.zeta) (p ^ Q) :=
      ArithmeticFunction.IsMultiplicative.map_prod (fun p => p ^ Q)
        (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast) P hpair
    _ = _ := by
      apply prod_congr rfl
      intro p hp'
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow (hp p hp')]
      have he : range (Q + 1) = insert 0 (Icc 1 Q) := by
        ext j
        simp only [mem_range, mem_insert, mem_Icc]
        omega
      rw [he, sum_insert (by simp), pow_zero, hf.map_one]

/-- Halupczok page 16, finite Euler domination of the first absolute coefficients.
The finite CRT multiplicativity identity is proved. -/
theorem finite_euler_domination (k l : Fin 3 → ℕ) (N Q : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    ∑ q ∈ Icc 1 Q, (q : ℝ) * ‖ssTerm k l N q‖ ≤ primeProduct k l N Q := by
  let f : ArithmeticFunction ℝ := ⟨fun q => (q : ℝ) * ‖ssTerm k l N q‖, by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f, ssTerm_one hk hl]
    · intro m n hmn
      by_cases hm : m = 0
      · subst m; simp
      by_cases hn : n = 0
      · subst n; simp
      change ((m * n : ℕ) : ℝ) * ‖ssTerm k l N (m * n)‖ =
        ((m : ℝ) * ‖ssTerm k l N m‖) * ((n : ℝ) * ‖ssTerm k l N n‖)
      rw [ssTerm_multiplicative k l N m n hk hl (by omega) (by omega) hmn, norm_mul]
      push_cast
      ring
  exact finite_euler_bound f hf (fun q => by change 0 ≤ (q : ℝ) * ‖ssTerm k l N q‖; positivity) Q

section Decomp355aLocalProductBound
open LeanLab.Tolev2009.SeriesIdentification

/-- Geometric (Gauss) sum: over a complete residue system modulo `n`. -/
private theorem gauss_sum (n : ℕ) (hn : n ≠ 0) (a : ℕ) :
    ∑ s ∈ range n, ee ((a : ℝ) * s / n) = if n ∣ a then (n : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * (π : ℂ) * Complex.I / (n : ℂ))) n :=
    Complex.isPrimitiveRoot_exp n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hkey : ∀ s : ℕ, 2 * (π : ℂ) * Complex.I * (((a : ℝ) * s / n : ℝ) : ℂ) =
      ((a * s : ℕ) : ℂ) * (2 * (π : ℂ) * Complex.I / (n : ℂ)) := by
    intro s
    push_cast
    field_simp
  have hpow : ∀ s : ℕ, ee ((a : ℝ) * s / n) =
      (Complex.exp (2 * (π : ℂ) * Complex.I / (n : ℂ)) ^ a) ^ s := by
    intro s
    rw [ee, hkey s, Complex.exp_nat_mul, pow_mul]
  rw [sum_congr rfl (fun s _ => hpow s)]
  by_cases h : n ∣ a
  · rw [if_pos h]
    have hx : Complex.exp (2 * (π : ℂ) * Complex.I / (n : ℂ)) ^ a = 1 :=
      (hprim.pow_eq_one_iff_dvd a).mpr h
    rw [hx]
    simp
  · rw [if_neg h]
    have hx : Complex.exp (2 * (π : ℂ) * Complex.I / (n : ℂ)) ^ a ≠ 1 := by
      intro hh
      exact h ((hprim.pow_eq_one_iff_dvd a).mp hh)
    rw [geom_sum_eq hx n]
    have hxp : (Complex.exp (2 * (π : ℂ) * Complex.I / (n : ℂ)) ^ a) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [hxp]
    simp



/-! ### Coefficient at prime powers -/

/-- A denominator dividing the modulus fixes the coefficient residue. -/
private theorem coeffRes_of_dvd (k l q : ℕ) (hq : 1 ≤ q) (hqk : q ∣ k) (hl : Nat.Coprime l k) :
    coeffRes k l q = {l % q} := by
  have hlq : Nat.Coprime l q := hl.coprime_dvd_right hqk
  ext r
  simp only [coeffRes, Nat.gcd_eq_right hqk, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hr, hcop, he⟩
    simpa only [Nat.mod_eq_of_lt hr] using he
  · rintro rfl
    refine ⟨Nat.mod_lt _ (by omega), ?_, Nat.mod_mod _ _⟩
    exact (coprime_modEq q (l % q) l (Nat.mod_mod _ _)).mpr hlq

/-- With a denominator dividing the modulus the coefficient is a single exponential. -/
private theorem coeff_of_dvd (k l q a : ℕ) (hq : 1 ≤ q) (hqk : q ∣ k) (hl : Nat.Coprime l k) :
    coeff k l q a = ee ((a : ℝ) * l / q) := by
  rw [coeff, coeffRes_of_dvd k l q hq hqk hl, sum_singleton]
  exact (ee_rat_mod a l q hq).symm

/-- A residue that is not coprime to a prime power is a multiple of the prime. -/
private theorem not_coprime_prime_pow {p j r : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hr : r < p ^ j) :
    ¬ Nat.Coprime r (p ^ j) ↔ p ∣ r := by
  have hp0 : 0 < p ^ j := pow_pos hp.pos j
  constructor
  · intro h
    have hg1 : Nat.gcd r (p ^ j) ≠ 1 := by
      intro hh
      exact h (by rw [Nat.Coprime, hh])
    have hg0 : 0 < Nat.gcd r (p ^ j) := Nat.gcd_pos_of_pos_right r hp0
    obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hg1
    have hqp : q ∣ p := by
      have := hqg.trans (Nat.gcd_dvd_right r (p ^ j))
      exact hq.dvd_of_dvd_pow this
    have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    rw [hqe] at hqg
    exact hqg.trans (Nat.gcd_dvd_left _ _)
  · intro h
    have hgcd : p ∣ Nat.gcd r (p ^ j) := Nat.dvd_gcd h (dvd_pow_self p (by omega))
    intro hc
    have h1 : Nat.gcd r (p ^ j) = 1 := hc
    rw [h1] at hgcd
    exact hp.ne_one (Nat.dvd_one.mp hgcd)



/-- Sum over the residue classes modulo a prime power: the arithmetic progression. -/
private theorem sum_ap_prime_pow (p j m l a : ℕ) (hp : p.Prime) (hmj : m ≤ j) :
    ∑ r ∈ (range (p ^ j)).filter (fun r => r % p ^ m = l % p ^ m), ee ((a : ℝ) * r / p ^ j)
      = ee ((a : ℝ) * ((l % p ^ m : ℕ) : ℝ) / p ^ j) *
        ∑ t ∈ range (p ^ (j - m)), ee ((a : ℝ) * t / p ^ (j - m)) := by
  have hp0 : 0 < p := hp.pos
  have hpm : 0 < p ^ m := pow_pos hp0 m
  set x : ℕ := l % p ^ m with hxdef
  have hlt : x < p ^ m := by rw [hxdef]; exact Nat.mod_lt l hpm
  have hsplit : p ^ (j - m) * p ^ m = p ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit' : p ^ m * p ^ (j - m) = p ^ j := by rw [Nat.mul_comm]; exact hsplit
  have hψmem : ∀ t : ℕ, t < p ^ (j - m) →
      x + p ^ m * t < p ^ j ∧ (x + p ^ m * t) % p ^ m = x := by
    intro t ht
    constructor
    · have h1 : x + p ^ m * t < p ^ m * (t + 1) := by
        rw [Nat.mul_succ]; omega
      have h2 : p ^ m * (t + 1) ≤ p ^ m * p ^ (j - m) := Nat.mul_le_mul_left _ (by omega)
      rw [hsplit'] at h2
      omega
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hinj : Set.InjOn (fun t => x + p ^ m * t) ↑(range (p ^ (j - m))) := by
    intro t1 ht1 t2 ht2 he
    have d1 : (x + p ^ m * t1) / p ^ m = t1 := by
      rw [Nat.add_mul_div_left _ _ hpm, Nat.div_eq_of_lt hlt, Nat.zero_add]
    have d2 : (x + p ^ m * t2) / p ^ m = t2 := by
      rw [Nat.add_mul_div_left _ _ hpm, Nat.div_eq_of_lt hlt, Nat.zero_add]
    calc t1 = (x + p ^ m * t1) / p ^ m := d1.symm
      _ = (x + p ^ m * t2) / p ^ m := by simpa using congrArg (fun u : ℕ => u / p ^ m) he
      _ = t2 := d2
  have hST : (range (p ^ j)).filter (fun r => r % p ^ m = x)
      = (range (p ^ (j - m))).image (fun t => x + p ^ m * t) := by
    ext r
    constructor
    · intro hr
      obtain ⟨hrr, hmod⟩ := Finset.mem_filter.mp hr
      have hrt : r < p ^ j := Finset.mem_range.mp hrr
      have hdiv : r / p ^ m < p ^ (j - m) := by
        rw [Nat.div_lt_iff_lt_mul hpm, hsplit]
        exact hrt
      refine Finset.mem_image.mpr ⟨r / p ^ m, Finset.mem_range.mpr hdiv, ?_⟩
      rw [← hmod, Nat.mod_add_div]
    · intro hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      have ht' : t < p ^ (j - m) := Finset.mem_range.mp ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hψmem t ht').1, (hψmem t ht').2⟩
  rw [hST, Finset.sum_image hinj]
  have hfac : ∀ t ∈ range (p ^ (j - m)),
      ee ((a : ℝ) * ((x + p ^ m * t : ℕ) : ℝ) / p ^ j)
        = ee ((a : ℝ) * (x : ℝ) / p ^ j) * ee ((a : ℝ) * t / p ^ (j - m)) := by
    intro t _
    rw [← ee_add]
    congr 1
    push_cast
    have hm0 : ((p : ℝ)) ^ m ≠ 0 := by positivity
    have hn0 : ((p : ℝ)) ^ (j - m) ≠ 0 := by positivity
    have h1 : ((p : ℝ)) ^ j = ((p : ℝ)) ^ m * ((p : ℝ)) ^ (j - m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1]
    field_simp
    try ring
  rw [Finset.sum_congr rfl hfac, Finset.mul_sum]


/-- Sum over the multiples of `p` below `p ^ j`, reindexed by `p ^ (j - 1)`. -/
private theorem sum_multiples_prime_pow (p j a : ℕ) (hp : p.Prime) (hj : 1 ≤ j) :
    ∑ r ∈ (range (p ^ j)).filter (fun r => p ∣ r), ee ((a : ℝ) * r / p ^ j)
      = ∑ t ∈ range (p ^ (j - 1)), ee ((a : ℝ) * t / p ^ (j - 1)) := by
  have hp0 : 0 < p := hp.pos
  have hsplit : p * p ^ (j - 1) = p ^ j := by
    rw [Nat.mul_comm, ← pow_succ, show j - 1 + 1 = j by omega]
  have hinj : Set.InjOn (fun t => p * t) ↑(range (p ^ (j - 1))) := by
    intro t1 _ t2 _ he
    exact Nat.eq_of_mul_eq_mul_left hp0 he
  have hST : (range (p ^ j)).filter (fun r => p ∣ r)
      = (range (p ^ (j - 1))).image (fun t => p * t) := by
    ext r
    constructor
    · intro hr
      obtain ⟨hrr, hpd⟩ := Finset.mem_filter.mp hr
      have hrt : r < p ^ j := Finset.mem_range.mp hrr
      have hdiv : r / p < p ^ (j - 1) := by
        rw [Nat.div_lt_iff_lt_mul hp0, Nat.mul_comm, hsplit]
        exact hrt
      refine Finset.mem_image.mpr ⟨r / p, Finset.mem_range.mpr hdiv, ?_⟩
      exact Nat.mul_div_cancel' hpd
    · intro hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      have ht' : t < p ^ (j - 1) := Finset.mem_range.mp ht
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, dvd_mul_right p t⟩
      rw [← hsplit]
      exact Nat.mul_lt_mul_of_pos_left ht' hp0
  rw [hST, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  push_cast
  have hp0R : ((p : ℝ)) ≠ 0 := by positivity
  have hn0 : ((p : ℝ)) ^ (j - 1) ≠ 0 := by positivity
  have h1 : ((p : ℝ)) ^ j = (p : ℝ) * ((p : ℝ)) ^ (j - 1) := by
    have hc := congrArg (fun m : ℕ => ((m : ℕ) : ℝ)) hsplit
    push_cast at hc
    exact hc.symm
  rw [h1]
  field_simp


/-- A prime dividing `r` divides the remainder of `r` modulo a prime power. -/
private theorem dvd_mod_of_dvd_prime_pow {p m r : ℕ} (hm : 1 ≤ m) (h : p ∣ r) : p ∣ r % p ^ m := by
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [Nat.mod_mod_of_dvd r (dvd_pow_self p (Nat.ne_of_gt hm)), h]

/-- A prime dividing a remainder modulo a prime power divides the number. -/
private theorem dvd_of_dvd_mod_prime_pow {p m l : ℕ} (hm : 1 ≤ m) (h : p ∣ l % p ^ m) : p ∣ l := by
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [← Nat.mod_mod_of_dvd l (dvd_pow_self p (Nat.ne_of_gt hm))]
  exact h


/-- Halupczok page 14: away from the common modulus, a prime power coefficient vanishes. -/
private theorem coeff_prime_pow_vanish (p j k l a : ℕ) (hp : p.Prime) (hj : 2 ≤ j)
    (hk : 1 ≤ k) (hl : Nat.Coprime l k) (ha : ¬ p ∣ a) (hnd : ¬ p ^ j ∣ k) :
    coeff k l (p ^ j) a = 0 := by
  have hp0 : 0 < p := hp.pos
  have hqpos : 0 < p ^ j := pow_pos hp0 j
  set g : ℕ := Nat.gcd k (p ^ j) with hgdef
  obtain ⟨m, hmj, hgm⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right k (p ^ j))
  have hmj' : m < j := by
    rcases lt_or_eq_of_le hmj with h | h
    · exact h
    · exfalso
      apply hnd
      rw [← h, ← hgm]
      exact Nat.gcd_dvd_left k (p ^ j)
  have hgm' : g = p ^ m := by rw [hgdef, hgm]
  set x : ℕ := l % p ^ m with hxdef
  have hc : coeff k l (p ^ j) a
      = ∑ r ∈ (range (p ^ j)).filter (fun r => Nat.Coprime r (p ^ j) ∧ r % p ^ m = x),
          ee ((a : ℝ) * r / p ^ j) := by
    have hfs : ((range (p ^ j)).filter (fun r => Nat.Coprime r (p ^ j) ∧
        r % Nat.gcd k (p ^ j) = l % Nat.gcd k (p ^ j)))
        = (range (p ^ j)).filter (fun r => Nat.Coprime r (p ^ j) ∧ r % p ^ m = x) := by
      apply Finset.filter_congr
      intro r _
      rw [← hgdef, hgm', ← hxdef]
    rw [coeff, coeffRes, hfs]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Nat.cast_pow]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hx0 : x = 0 := by rw [hxdef]; exact Nat.mod_one l
    have hpred : ∀ r : ℕ, (Nat.Coprime r (p ^ j) ∧ r % p ^ 0 = x) ↔ Nat.Coprime r (p ^ j) := by
      intro r
      rw [pow_zero, Nat.mod_one, hx0]
      simp
    rw [hc, Finset.filter_congr (fun r _ => hpred r)]
    have hAB : (∑ r ∈ (range (p ^ j)).filter (fun r => Nat.Coprime r (p ^ j)),
          ee ((a : ℝ) * r / p ^ j))
        + (∑ r ∈ (range (p ^ j)).filter (fun r => ¬ Nat.Coprime r (p ^ j)),
            ee ((a : ℝ) * r / p ^ j))
        = ∑ r ∈ range (p ^ j), ee ((a : ℝ) * r / p ^ j) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hfull : ∑ r ∈ range (p ^ j), ee ((a : ℝ) * r / p ^ j) = 0 := by
      have h1 := gauss_sum (p ^ j) hqpos.ne' a
      have h2 : ¬ (p ^ j ∣ a) := fun hd => ha ((dvd_pow_self p (by omega)).trans hd)
      rw [if_neg h2] at h1
      simpa only [Nat.cast_pow] using h1
    have hnc : ∑ r ∈ (range (p ^ j)).filter (fun r => ¬ Nat.Coprime r (p ^ j)),
        ee ((a : ℝ) * r / p ^ j) = 0 := by
      have hset : (range (p ^ j)).filter (fun r => ¬ Nat.Coprime r (p ^ j))
          = (range (p ^ j)).filter (fun r => p ∣ r) := by
        apply Finset.filter_congr
        intro r hr
        exact not_coprime_prime_pow hp (by omega) (Finset.mem_range.mp hr)
      rw [hset, sum_multiples_prime_pow p j a hp (by omega)]
      have hn1 : 0 < p ^ (j - 1) := pow_pos hp0 _
      have h1 := gauss_sum (p ^ (j - 1)) hn1.ne' a
      have h2 : ¬ (p ^ (j - 1) ∣ a) := fun hd => ha ((dvd_pow_self p (by omega)).trans hd)
      rw [if_neg h2] at h1
      simpa only [Nat.cast_pow] using h1
    rw [hnc, add_zero] at hAB
    rw [hAB, hfull]
  · have hpl : ¬ p ∣ l := by
      intro hpl'
      have hpg : p ∣ g := by rw [hgm']; exact dvd_pow_self p (Nat.ne_of_gt hm)
      have hpk : p ∣ k := hpg.trans (Nat.gcd_dvd_left k (p ^ j))
      exact ((hp.coprime_iff_not_dvd).mp (hl.coprime_dvd_right hpk).symm) hpl'
    have hpred : ∀ r : ℕ, (Nat.Coprime r (p ^ j) ∧ r % p ^ m = x) ↔ (r % p ^ m = x) := by
      intro r
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      have hpr : ¬ p ∣ r := by
        intro hpr
        have hxl : p ∣ l % p ^ m := by
          rw [← hxdef, ← h]
          exact dvd_mod_of_dvd_prime_pow hm hpr
        exact hpl (dvd_of_dvd_mod_prime_pow hm hxl)
      have hcp : Nat.Coprime r p := ((hp.coprime_iff_not_dvd).mpr hpr).symm
      exact hcp.pow_right j
    rw [hc, Finset.filter_congr (fun r _ => hpred r), hxdef,
      sum_ap_prime_pow p j m l a hp (le_of_lt hmj')]
    have hnpos : 0 < p ^ (j - m) := pow_pos hp0 _
    have hnm : ¬ (p ^ (j - m) ∣ a) := fun hd => ha ((dvd_pow_self p (by omega)).trans hd)
    have hzero : ∑ t ∈ range (p ^ (j - m)), ee ((a : ℝ) * t / p ^ (j - m)) = 0 := by
      have h1 := gauss_sum (p ^ (j - m)) hnpos.ne' a
      rw [if_neg hnm] at h1
      simpa only [Nat.cast_pow] using h1
    rw [hzero, mul_zero]


/-- The residue set at a prime not dividing the modulus: `r` ranges over the units. -/
private theorem coeffRes_prime_not_dvd (k l p : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : Nat.Coprime l k) (hpk : ¬ p ∣ k) :
    coeffRes k l p = (range p).filter (fun r => Nat.Coprime r p) := by
  have hgcd : Nat.gcd k p = 1 := by
    rw [Nat.coprime_iff_gcd_eq_one.symm]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk).symm
  ext r
  simp only [coeffRes, hgcd, Nat.mod_one, mem_filter, mem_range]
  simp

/-- Halupczok page 12: at a prime not dividing the modulus the coefficient is `-1`. -/
private theorem coeff_prime_not_dvd (k l p a : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : Nat.Coprime l k) (hpk : ¬ p ∣ k) (ha : ¬ p ∣ a) :
    coeff k l p a = -1 := by
  have hppos : 0 < p := hp.pos
  have hfs : coeffRes k l p = (range p).filter (fun r => Nat.Coprime r p) :=
    coeffRes_prime_not_dvd k l p hp hk hl hpk
  have hAB : (∑ r ∈ (range p).filter (fun r => Nat.Coprime r p), ee ((a : ℝ) * r / p))
      + (∑ r ∈ (range p).filter (fun r => ¬ Nat.Coprime r p), ee ((a : ℝ) * r / p))
      = ∑ r ∈ range p, ee ((a : ℝ) * r / p) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hfull : ∑ r ∈ range p, ee ((a : ℝ) * r / p) = 0 := by
    have h1 := gauss_sum p hp.ne_zero a
    rw [if_neg ha] at h1
    simpa only [Nat.cast_pow, pow_one] using h1
  have hnc : (range p).filter (fun r => ¬ Nat.Coprime r p) = {0} := by
    ext r
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hr, hcop⟩
      by_contra hr0
      have hnr : ¬ p ∣ r := by
        intro hpd
        exact hr0 (Nat.eq_zero_of_dvd_of_lt hpd hr)
      exact hcop ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnr).symm
    · rintro rfl
      refine ⟨hppos, ?_⟩
      intro hc
      have h1 : Nat.Coprime 0 p := hc
      rw [Nat.coprime_zero_left] at h1
      exact hp.ne_one h1
  have hA : (∑ r ∈ (range p).filter (fun r => Nat.Coprime r p), ee ((a : ℝ) * r / p))
      = ∑ r ∈ range p, ee ((a : ℝ) * r / p)
        - ∑ r ∈ (range p).filter (fun r => ¬ Nat.Coprime r p), ee ((a : ℝ) * r / p) := by
    rw [← hAB]; ring
  rw [coeff, hfs, hA, hnc, sum_singleton, hfull]
  simp [ee]


/-! ### Local factors at a prime -/

/-- With the modulus dividing `k` the normalized local factor has norm one. -/
private theorem localSum_of_dvd (k l q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hqk : q ∣ k) (hl : Nat.Coprime l k) :
    localSum k l q a = ee ((a : ℝ) * l / q) := by
  have hφ : (k.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  rw [localSum_eq_coeff k l q a hk hq hl, Nat.lcm_eq_left hqk,
    div_self hφ, one_mul, coeff_of_dvd k l q a hq hqk hl]

/-- Norm one for the local factor when the prime modulus divides `k`. -/
private theorem norm_localSum_prime_dvd (k l p a : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : Nat.Coprime l k) (hpk : p ∣ k) : ‖localSum k l p a‖ = 1 := by
  rw [localSum_of_dvd k l p a hk hp.one_le hpk hl,
    LeanLab.Tolev2009.Displays14to16.norm_ee]

/-- Halupczok page 14: the local factor at a prime not dividing `k`. -/
private theorem localSum_prime_not_dvd (k l p a : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : Nat.Coprime l k) (hpk : ¬ p ∣ k) (ha : ¬ p ∣ a) :
    localSum k l p a = -(((p - 1 : ℕ) : ℂ))⁻¹ := by
  have hp1 : 1 ≤ p := hp.one_le
  have hφ : (k.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  have hcop : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk).symm
  have hlc : Nat.lcm k p = k * p := Nat.Coprime.lcm_eq_mul hcop
  have hφp : ((k * p).totient : ℂ) = (k.totient : ℂ) * ((p - 1 : ℕ) : ℂ) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul]
  have hpm : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
    have h2 : 0 < p - 1 := by have := hp.two_le; omega
    exact_mod_cast h2.ne'
  rw [localSum_eq_coeff k l p a hk hp1 hl, hlc, hφp,
    coeff_prime_not_dvd k l p a hp hk hl hpk ha]
  field_simp


/-! ### The unit sum modulo a prime -/

/-- A negative numerator is the same phase as the multiple `N (p - 1)`. -/
private theorem ee_neg_eq_shift (a N p : ℕ) (hp : 1 ≤ p) :
    ee (-((a : ℝ) * N / p)) = ee (((N * (p - 1) : ℕ) : ℝ) * a / p) := by
  have hsub : ((N * (p - 1) : ℕ) : ℝ) = (N : ℝ) * ((p : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one]
  have hpne : (p : ℝ) ≠ 0 := by
    have : (0:ℝ) < p := by
      have := hp
      positivity
    exact this.ne'
  have key : ((N * (p - 1) : ℕ) : ℝ) * a / p
      = -((a : ℝ) * N / p) + ((a * N : ℕ) : ℝ) := by
    rw [hsub]
    push_cast
    field_simp
    ring
  rw [key, ee_add, show ee (((a * N : ℕ) : ℝ)) = 1 from ee_int ((a * N : ℕ) : ℤ), mul_one]

/-- The sum of the unit phases modulo a prime. -/
private theorem sum_units_ee_eq (N p : ℕ) (hp : p.Prime) :
    ∑ a ∈ (range p).filter (fun a => Nat.Coprime a p), ee (-((a : ℝ) * N / p))
      = (if p ∣ N then (p : ℂ) else 0) - 1 := by
  have hppos : 0 < p := hp.pos
  have hAB : (∑ a ∈ (range p).filter (fun a => Nat.Coprime a p), ee (-((a : ℝ) * N / p)))
      + (∑ a ∈ (range p).filter (fun a => ¬ Nat.Coprime a p), ee (-((a : ℝ) * N / p)))
      = ∑ a ∈ range p, ee (-((a : ℝ) * N / p)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hfull : ∑ a ∈ range p, ee (-((a : ℝ) * N / p))
      = (if p ∣ N then (p : ℂ) else 0) := by
    have hshift : ∑ a ∈ range p, ee (-((a : ℝ) * N / p))
        = ∑ a ∈ range p, ee (((N * (p - 1) : ℕ) : ℝ) * a / p) := by
      apply Finset.sum_congr rfl
      intro a _
      exact ee_neg_eq_shift a N p hp.one_le
    rw [hshift, gauss_sum p hp.ne_zero (N * (p - 1))]
    by_cases hd : p ∣ N
    · rw [if_pos (hd.mul_right (p - 1)), if_pos hd]
    · rw [if_neg, if_neg hd]
      intro h
      have hcop : Nat.Coprime p (p - 1) := by
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
          intro hd
          have h1 : p ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hd
          have := hp.two_le
          omega)
      exact hd (hcop.dvd_of_dvd_mul_right h)
  have hnc : (range p).filter (fun a => ¬ Nat.Coprime a p) = {0} := by
    ext a
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨ha, hcop⟩
      by_contra ha0
      have hnr : ¬ p ∣ a := by
        intro hpd
        exact ha0 (Nat.eq_zero_of_dvd_of_lt hpd ha)
      exact hcop ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnr).symm
    · rintro rfl
      refine ⟨hppos, ?_⟩
      intro hc
      have h1 : Nat.Coprime 0 p := hc
      rw [Nat.coprime_zero_left] at h1
      exact hp.ne_one h1
  have hzero : ∑ a ∈ (range p).filter (fun a => ¬ Nat.Coprime a p), ee (-((a : ℝ) * N / p)) = 1 := by
    rw [hnc, sum_singleton]
    simp [ee]
  have hfin : ∑ a ∈ (range p).filter (fun a => Nat.Coprime a p), ee (-((a : ℝ) * N / p))
      = ∑ a ∈ range p, ee (-((a : ℝ) * N / p)) - 1 := by
    rw [hzero] at hAB
    rw [← hAB]; ring
  rw [hfin, hfull]


/-! ### Prime power and prime bounds for the full coefficient -/

/-- Away from the common modulus, a prime power coefficient of the series vanishes. -/
private theorem ssTerm_prime_pow_vanish (k l : Fin 3 → ℕ) (N p j : ℕ) (hp : p.Prime)
    (hj : 2 ≤ j) (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ∃ i, ¬ p ^ j ∣ k i) :
    ssTerm k l N (p ^ j) = 0 := by
  obtain ⟨i0, hi0⟩ := hnd
  have hq1 : 1 ≤ p ^ j := Nat.one_le_pow j p hp.pos
  unfold ssTerm
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨-, hcop⟩ := Finset.mem_filter.mp ha
  have hpa : ¬ p ∣ a := by
    intro h
    have h1 : p ∣ Nat.gcd a (p ^ j) := Nat.dvd_gcd h (dvd_pow_self p (by omega))
    have h2 : Nat.gcd a (p ^ j) = 1 := hcop
    rw [h2] at h1
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have hcoef : coeff (k i0) (l i0) (p ^ j) a = 0 :=
    coeff_prime_pow_vanish p j (k i0) (l i0) a hp hj (hk i0) (hl i0) hpa hi0
  have hzero : localSum (k i0) (l i0) (p ^ j) a = 0 := by
    rw [localSum_eq_coeff (k i0) (l i0) (p ^ j) a (hk i0) hq1 (hl i0), hcoef, mul_zero]
  rw [Finset.prod_eq_zero (mem_univ i0) hzero, mul_zero]

/-- The normalized local factor at a prime not dividing `k`. -/
private theorem norm_localSum_prime_not_dvd (k l p a : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : Nat.Coprime l k) (ha : ¬ p ∣ a) (hpk : ¬ p ∣ k) :
    ‖localSum k l p a‖ = ((p - 1 : ℕ) : ℝ)⁻¹ := by
  rw [localSum_prime_not_dvd k l p a hp hk hl hpk ha, norm_neg, norm_inv,
    Complex.norm_natCast]

/-- The normalized local factor is at most one in modulus. -/
private theorem norm_localSum_prime_le_one (k l p a : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : Nat.Coprime l k) (ha : ¬ p ∣ a) : ‖localSum k l p a‖ ≤ 1 := by
  by_cases hpk : p ∣ k
  · rw [norm_localSum_prime_dvd k l p a hp hk hl hpk]
  · rw [norm_localSum_prime_not_dvd k l p a hp hk hl ha hpk]
    exact inv_le_one_of_one_le₀ (by
      have h2 : 1 ≤ p - 1 := by have := hp.two_le; omega
      calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
        _ ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h2)

/-- The series coefficient at a prime has modulus at most one away from the common modulus. -/
private theorem ssTerm_prime_norm_le_one (k l : Fin 3 → ℕ) (N p : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) (hnd : ∃ i, ¬ p ∣ k i) :
    ‖ssTerm k l N p‖ ≤ 1 := by
  obtain ⟨i0, hi0⟩ := hnd
  have hppos : 0 < p := hp.pos
  have hinv1 : ((p - 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    have h2 : 1 ≤ p - 1 := by have := hp.two_le; omega
    calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      _ ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h2
  have hterm : ∀ a ∈ (range p).filter (fun a => Nat.Coprime a p),
      ‖ee (-((a : ℝ) * N / p)) * ∏ i : Fin 3, localSum (k i) (l i) p a‖
        ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by
    intro a ha
    obtain ⟨-, hcop⟩ := Finset.mem_filter.mp ha
    have hpa : ¬ p ∣ a := fun h => ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm) h
    rw [norm_mul, norm_prod, LeanLab.Tolev2009.Displays14to16.norm_ee, one_mul]
    have hb : ∀ i : Fin 3, (0:ℝ) ≤ ‖localSum (k i) (l i) p a‖ := fun i => norm_nonneg _
    have h1 : ∀ i : Fin 3, ‖localSum (k i) (l i) p a‖ ≤ 1 := fun i =>
      norm_localSum_prime_le_one (k i) (l i) p a hp (hk i) (hl i) hpa
    have hc : ‖localSum (k i0) (l i0) p a‖ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by
      rw [norm_localSum_prime_not_dvd (k i0) (l i0) p a hp (hk i0) (hl i0) hpa hi0]
    have hp1 : (0:ℝ) ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hsplit : (∏ i : Fin 3, ‖localSum (k i) (l i) p a‖)
        = ‖localSum (k i0) (l i0) p a‖ * ∏ i ∈ (univ \ {i0}), ‖localSum (k i) (l i) p a‖ :=
      Finset.prod_eq_mul_prod_diff_singleton (s := univ) i0
        (fun i => ‖localSum (k i) (l i) p a‖) (fun h => absurd (mem_univ i0) h)
    have hrest : (∏ i ∈ (univ \ {i0}), ‖localSum (k i) (l i) p a‖) ≤ 1 := by
      have h := Finset.prod_le_prod₀ (s := (univ \ {i0}))
        (f := fun i : Fin 3 => ‖localSum (k i) (l i) p a‖) (g := fun _ => (1:ℝ))
        (fun i _ => norm_nonneg _) (fun i _ => h1 i)
      simpa using h
    calc (∏ i : Fin 3, ‖localSum (k i) (l i) p a‖)
        = ‖localSum (k i0) (l i0) p a‖ * ∏ i ∈ (univ \ {i0}), ‖localSum (k i) (l i) p a‖ := hsplit
      _ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ * 1 := mul_le_mul hc hrest (by positivity) hp1
      _ = ((p - 1 : ℕ) : ℝ)⁻¹ := by ring
  have hstep := Finset.sum_le_sum hterm
  refine (norm_sum_le _ _).trans ?_
  refine hstep.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : (((range p).filter (fun a => Nat.Coprime a p)).card : ℝ) = ((p - 1 : ℕ) : ℝ) := by
    rw [show (range p).filter (fun a => Nat.Coprime a p)
        = (range p).filter (fun a => p.Coprime a) from by
      apply Finset.filter_congr
      intro a _
      exact Nat.coprime_comm]
    rw [← Nat.totient_eq_card_coprime, Nat.totient_prime hp]
  rw [hcast]
  have hpos : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have h2 : 0 < p - 1 := by have := hp.two_le; omega
    exact_mod_cast h2.ne'
  exact le_of_eq (mul_inv_cancel₀ hpos)


/-- Halupczok page 14: at a prime dividing none of the moduli the series term factors. -/
private theorem ssTerm_prime_eq_not_dvd (k l : Fin 3 → ℕ) (N p : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ∀ i, ¬ p ∣ k i) :
    ssTerm k l N p = (-(((p - 1 : ℕ) : ℂ))⁻¹) ^ 3 *
      ∑ a ∈ (range p).filter (fun a => Nat.Coprime a p), ee (-((a : ℝ) * N / p)) := by
  have hconst : ∀ a, ¬ p ∣ a →
      (∏ i : Fin 3, localSum (k i) (l i) p a) = (-(((p - 1 : ℕ) : ℂ))⁻¹) ^ 3 := by
    intro a ha
    rw [Fin.prod_univ_three,
      localSum_prime_not_dvd (k 0) (l 0) p a hp (hk 0) (hl 0) (hnd 0) ha,
      localSum_prime_not_dvd (k 1) (l 1) p a hp (hk 1) (hl 1) (hnd 1) ha,
      localSum_prime_not_dvd (k 2) (l 2) p a hp (hk 2) (hl 2) (hnd 2) ha]
    ring
  unfold ssTerm
  have hstep : ∑ a ∈ (range p).filter (fun a => Nat.Coprime a p),
        ee (-((a : ℝ) * N / p)) * ∏ i : Fin 3, localSum (k i) (l i) p a
      = ∑ a ∈ (range p).filter (fun a => Nat.Coprime a p),
        ee (-((a : ℝ) * N / p)) * (-(((p - 1 : ℕ) : ℂ))⁻¹) ^ 3 := by
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨-, hcop⟩ := Finset.mem_filter.mp ha
    have hpa : ¬ p ∣ a := fun h => ((hp.coprime_iff_not_dvd).mp hcop.symm) h
    rw [hconst a hpa]
  rw [hstep, ← Finset.sum_mul]
  ring

/-- The norm of the series term at a prime dividing none of the moduli. -/
private theorem ssTerm_prime_norm_le_not_dvd (k l : Fin 3 → ℕ) (N p : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ∀ i, ¬ p ∣ k i) :
    ‖ssTerm k l N p‖ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ ^ 2 *
      (if p ∣ N then 1 else ((p - 1 : ℕ) : ℝ)⁻¹) := by
  have hp1 : ((p - 1 : ℕ) : ℝ)⁻¹ = ((p : ℝ) - 1)⁻¹ := by
    congr 1
    have := hp.one_le
    push_cast [Nat.cast_sub this]
    ring
  rw [ssTerm_prime_eq_not_dvd k l N p hp hk hl hnd, norm_mul, norm_pow,
    norm_neg, norm_inv, Complex.norm_natCast]
  have hc0 : (0:ℝ) ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hsum : ‖∑ a ∈ (range p).filter (fun a => Nat.Coprime a p), ee (-((a : ℝ) * N / p))‖
      = if p ∣ N then ((p - 1 : ℕ) : ℝ)⁻¹⁻¹ else 1 := by
    rw [sum_units_ee_eq N p hp]
    by_cases hd : p ∣ N
    · rw [if_pos hd, if_pos hd]
      have h2 : ((p : ℂ) - 1) = (((p - 1 : ℕ)) : ℂ) := by
        push_cast [Nat.cast_sub hp.one_le]
        ring
      rw [h2, Complex.norm_natCast, inv_inv]
    · rw [if_neg hd, if_neg hd]
      simp
  rw [hsum]
  by_cases hd : p ∣ N
  · rw [if_pos hd, if_pos hd]
    have hne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      have h2 : 0 < p - 1 := by have := hp.two_le; omega
      exact_mod_cast h2.ne'
    refine le_of_eq ?_
    rw [inv_inv]
    field_simp
    try ring
  · rw [if_neg hd, if_neg hd]
    exact le_of_eq (by ring)


/-- The series coefficient is bounded by `phi q` when all moduli are divisible by `q`. -/
private theorem ssTerm_norm_of_dvd (k l : Fin 3 → ℕ) (N q : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hq : 1 ≤ q) (hqk : ∀ i, q ∣ k i) : ‖ssTerm k l N q‖ ≤ q.totient := by
  unfold ssTerm
  calc _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖ee (-((a : ℝ) * N / q)) * ∏ i : Fin 3, localSum (k i) (l i) q a‖ := norm_sum_le _ _
    _ = ∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [norm_mul, norm_prod, localSum_of_dvd _ _ _ _ (hk _) hq (hqk _) (hl _),
        LeanLab.Tolev2009.Displays14to16.norm_ee]
      simp
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) = (q.totient : ℝ) := by
        rw [show (range q).filter (fun a => Nat.Coprime a q)
            = (range q).filter (fun a => q.Coprime a) from by
          apply Finset.filter_congr
          intro a _
          exact Nat.coprime_comm]
        rw [← Nat.totient_eq_card_coprime]
      rw [this]

/-- Two of three nonnegative factors below `c` force the product below `c ^ 2`. -/
private theorem three_prod_le_sq {c f0 f1 f2 : ℝ} (hc : 0 ≤ c)
    (h0 : 0 ≤ f0) (h1 : 0 ≤ f1) (h2 : 0 ≤ f2)
    (g0 : f0 ≤ 1) (g1 : f1 ≤ 1) (g2 : f2 ≤ 1)
    (e0 : f0 ≤ c) (e1 : f1 ≤ c) : f0 * f1 * f2 ≤ c ^ 2 := by
  have hab : f0 * f1 ≤ c * c := mul_le_mul e0 e1 h1 hc
  have := mul_le_mul hab g2 h2 (by positivity : (0:ℝ) ≤ c * c)
  calc f0 * f1 * f2 = (f0 * f1) * f2 := by ring
    _ ≤ c * c * 1 := this
    _ = c ^ 2 := by ring

/-- The series coefficient at a prime where two moduli are coprime to it. -/
private theorem ssTerm_prime_norm_le_inv (k l : Fin 3 → ℕ) (N p : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ∃ i j : Fin 3, i ≠ j ∧ ¬ p ∣ k i ∧ ¬ p ∣ k j) :
    ‖ssTerm k l N p‖ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by
  obtain ⟨i0, i1, hne, hi0, hi1⟩ := hnd
  have hppos : 0 < p := hp.pos
  have hc0 : (0:ℝ) ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hcf : ((p - 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    have h2 : 1 ≤ p - 1 := by have := hp.two_le; omega
    calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      _ ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h2
  have hterm : ∀ a ∈ (range p).filter (fun a => Nat.Coprime a p),
      ‖ee (-((a : ℝ) * N / p)) * ∏ i : Fin 3, localSum (k i) (l i) p a‖
        ≤ ((p - 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
    intro a ha
    obtain ⟨-, hcop⟩ := Finset.mem_filter.mp ha
    have hpa : ¬ p ∣ a := fun h => ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm) h
    rw [norm_mul, norm_prod, LeanLab.Tolev2009.Displays14to16.norm_ee, one_mul]
    set f : Fin 3 → ℝ := fun i => ‖localSum (k i) (l i) p a‖ with hf
    have hb : ∀ i : Fin 3, 0 ≤ f i := fun i => norm_nonneg _
    have h1 : ∀ i : Fin 3, f i ≤ 1 := fun i =>
      norm_localSum_prime_le_one (k i) (l i) p a hp (hk i) (hl i) hpa
    have hci : ∀ i : Fin 3, ¬ p ∣ k i → f i ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := fun i hi => by
      show ‖localSum (k i) (l i) p a‖ ≤ ((p - 1 : ℕ) : ℝ)⁻¹
      rw [norm_localSum_prime_not_dvd (k i) (l i) p a hp (hk i) (hl i) hpa hi]
    have hpp : ({i0, i1} : Finset (Fin 3)) ⊆ univ := fun i _ => mem_univ i
    have hsplit : (∏ i : Fin 3, f i)
        = (f i0 * f i1) * ∏ i ∈ (univ \ ({i0, i1} : Finset (Fin 3))), f i := by
      have h1' : (∏ i ∈ (univ \ ({i0, i1} : Finset (Fin 3))), f i) * (∏ i ∈ ({i0, i1} : Finset (Fin 3)), f i)
          = ∏ i : Fin 3, f i := Finset.prod_sdiff hpp
      rw [← h1', Finset.prod_pair hne, mul_comm]
    have hrest : (∏ i ∈ (univ \ ({i0, i1} : Finset (Fin 3))), f i) ≤ 1 := by
      have h := Finset.prod_le_prod₀ (s := (univ \ ({i0, i1} : Finset (Fin 3))))
        (f := f) (g := fun _ => (1:ℝ)) (fun i _ => hb i) (fun i _ => h1 i)
      simpa using h
    rw [hsplit]
    have hpair : f i0 * f i1 ≤ ((p - 1 : ℕ) : ℝ)⁻¹ * ((p - 1 : ℕ) : ℝ)⁻¹ :=
      mul_le_mul (hci i0 hi0) (hci i1 hi1) (hb i1) hc0
    have := mul_le_mul hpair hrest (Finset.prod_nonneg (fun i _ => hb i))
      (by positivity : (0:ℝ) ≤ ((p - 1 : ℕ) : ℝ)⁻¹ * ((p - 1 : ℕ) : ℝ)⁻¹)
    calc (f i0 * f i1) * ∏ i ∈ (univ \ ({i0, i1} : Finset (Fin 3))), f i
        ≤ (((p - 1 : ℕ) : ℝ)⁻¹ * ((p - 1 : ℕ) : ℝ)⁻¹) * 1 := this
      _ = ((p - 1 : ℕ) : ℝ)⁻¹ ^ 2 := by ring
  have hstep := Finset.sum_le_sum hterm
  refine (norm_sum_le _ _).trans ?_
  refine hstep.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : (((range p).filter (fun a => Nat.Coprime a p)).card : ℝ) = ((p - 1 : ℕ) : ℝ) := by
    rw [show (range p).filter (fun a => Nat.Coprime a p)
        = (range p).filter (fun a => p.Coprime a) from by
      apply Finset.filter_congr
      intro a _
      exact Nat.coprime_comm]
    rw [← Nat.totient_eq_card_coprime, Nat.totient_prime hp]
  rw [hcast]
  have hpos : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have h2 : 0 < p - 1 := by have := hp.two_le; omega
    exact_mod_cast h2.ne'
  have hsq : ((p - 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)⁻¹ ^ 2 = ((p - 1 : ℕ) : ℝ)⁻¹ := by
    field_simp
  rw [hsq]

/-! ### The common prime power factor -/

/-- The scalar sum of common prime power first moments telescopes. -/
private theorem prime_power_moment (p γ : ℕ) (hp : p.Prime) :
    1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ((p ^ j).totient : ℝ) ≤
      (p : ℝ) ^ (2 * γ) := by
  induction γ with
  | zero => simp
  | succ γ ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have he : (p : ℝ) ^ (2 * (γ + 1)) = (p : ℝ) ^ (2 * γ) * (p : ℝ) ^ 2 := by
      rw [show 2 * (γ + 1) = 2 * γ + 2 by omega, pow_add]
    have ht : ((p ^ (γ + 1) : ℕ) : ℝ) * ((p ^ (γ + 1)).totient : ℝ) =
        (p : ℝ) ^ (2 * γ) * p * ((p : ℝ) - 1) := by
      rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_pow,
        show 2 * γ = γ + γ by omega, pow_add, pow_succ]
      ring
    rw [ht]
    calc _ ≤ (p : ℝ) ^ (2 * γ) + (p : ℝ) ^ (2 * γ) * p * ((p : ℝ) - 1) := by linarith
      _ = (p : ℝ) ^ (2 * γ) * (1 + p * ((p : ℝ) - 1)) := by ring
      _ ≤ (p : ℝ) ^ (2 * γ) * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg (Nat.cast_nonneg p) _)
      _ = _ := he.symm

/-- The complete common prime power Euler factor is bounded by the prime power. -/
private theorem common_prime_factor (k l : Fin 3 → ℕ) (N p γ : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hpk : ∀ i, p ^ γ ∣ k i) :
    1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤
      (p : ℝ) ^ (2 * γ) := by
  calc _ ≤ 1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ((p ^ j).totient : ℝ) := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (ssTerm_norm_of_dvd k l N (p ^ j) hk hl (Nat.one_le_pow _ _ hp.one_le)
            (fun i => (pow_dvd_pow p (mem_Icc.mp hj).2).trans (hpk i))) (Nat.cast_nonneg _)
    _ ≤ _ := prime_power_moment p γ hp

/-- The prime power sum over `Icc 1 Q` is at most the sum over the common valuation. -/
private theorem sum_Icc_prime_pow_le (k l : Fin 3 → ℕ) (N p Q γ : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hγ1 : 1 ≤ γ) (hγ : ∀ j, γ < j → ∃ i, ¬ p ^ j ∣ k i) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤
      1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ := by
  have hf : ∀ j, 0 ≤ ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ := fun j =>
    mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  by_cases hQ : Q ≤ γ
  · exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hQ)
      (fun j _ _ => hf j))
  · have hQ' : γ < Q := Nat.lt_of_not_le hQ
    have hsub : Icc 1 γ ⊆ Icc 1 Q := Icc_subset_Icc_right (le_of_lt hQ')
    have hzero : ∀ j ∈ Icc 1 Q, j ∉ Icc 1 γ → ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ = 0 := by
      intro j hj hjn
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      have hjg : γ < j := by
        rcases Nat.lt_or_ge γ j with h | h
        · exact h
        · exact absurd (mem_Icc.mpr ⟨hj1, h⟩) hjn
      obtain ⟨i, hi⟩ := hγ j hjg
      rw [ssTerm_prime_pow_vanish k l N p j hp (by omega) hk hl ⟨i, hi⟩, norm_zero, mul_zero]
    have heq : ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
        = ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
      (Finset.sum_subset hsub hzero).symm
    rw [heq]

/-! ### Elementary harmonic estimates -/

/-- The truncated harmonic sum is at most `1 + log k`. -/
private theorem sum_range_inv_le_log (k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ range k, (1 : ℝ) / (n + 1) ≤ 1 + Real.log k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
    · have hIH := ih (by omega)
      have hkey : (1:ℝ) / ((k:ℝ) + 1) ≤ Real.log ((k:ℝ) + 1) - Real.log (k:ℝ) := by
        have h1 : Real.log ((k:ℝ)+1) - Real.log (k:ℝ) = Real.log (((k:ℝ)+1)/(k:ℝ)) := by
          rw [Real.log_div (by positivity) (by positivity)]
        rw [h1]
        have hkRk : (0:ℝ) < k := by exact_mod_cast hkpos
        have hinner : (1 - 1/((k:ℝ)+1)) = (k:ℝ)/((k:ℝ)+1) := by
          have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
          field_simp
          ring
        have he : ((k:ℝ)+1)/(k:ℝ) = (1 - 1/((k:ℝ)+1))⁻¹ := by
          rw [hinner, inv_div]
        rw [he, Real.log_inv]
        have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
        have hpos : (0:ℝ) < 1 - 1/((k:ℝ)+1) := by
          have h3 : (1:ℝ)/((k:ℝ)+1) < 1 := by
            rw [div_lt_one (by positivity)]
            linarith
          linarith
        have hle := Real.log_le_sub_one_of_pos hpos
        have hv : 1 - 1/((k:ℝ)+1) - 1 = -(1/((k:ℝ)+1)) := by ring
        rw [hv] at hle
        linarith
      have hcast : ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- The truncated sum of reciprocal squares is at most `2 - 1/k`. -/
private theorem sum_range_inv_sq_le (k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ range k, (1 : ℝ) / ((n + 1) ^ 2) ≤ 2 - 1/(k:ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
      norm_num
    · have hIH := ih (by omega)
      have hstep : (1:ℝ) / (((k:ℝ) + 1) ^ 2) ≤ 1/(k:ℝ) - 1/((k:ℝ) + 1) := by
        have he : (1:ℝ)/(k:ℝ) - 1/((k:ℝ)+1) = 1/((k:ℝ)*((k:ℝ)+1)) := by
          field_simp
          ring
        rw [he]
        have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
        have h1 : (0:ℝ) < (k:ℝ) * ((k:ℝ)+1) := by positivity
        have h2 : ((k:ℝ)*((k:ℝ)+1)) ≤ ((k:ℝ)+1)^2 := by nlinarith
        exact one_div_le_one_div_of_le h1 h2
      have hcast : ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-! ### The common gcd denominator versus the pairwise gcd envelope -/

/-- The cube of the common gcd times the pairwise-only primes divides the pairwise envelope. -/
private theorem d3_prod_dvd (k : Fin 3 → ℕ)
    (hk : ∀ i, 1 ≤ k i) :
    Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2) ^ 3 *
        (∏ p ∈ (Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) *
          Nat.gcd (k 1) (k 2)).primeFactors.filter
            (fun p => ¬ p ∣ Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)), p)
      ∣ Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2) := by
  set g01 := Nat.gcd (k 0) (k 1) with hg01
  set g02 := Nat.gcd (k 0) (k 2) with hg02
  set g12 := Nat.gcd (k 1) (k 2) with hg12
  set d := Nat.gcd g01 (k 2) with hd
  set A := g01 * g02 * g12 with hA
  have hdg01 : d ∣ g01 := Nat.gcd_dvd_left _ _
  have hdk2 : d ∣ k 2 := Nat.gcd_dvd_right _ _
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left (k 2) (Nat.gcd_pos_of_pos_left _ (hk 0))
  have hdg02 : d ∣ g02 := Nat.dvd_gcd (hdg01.trans (Nat.gcd_dvd_left _ _)) hdk2
  have hdg12 : d ∣ g12 := Nat.dvd_gcd (hdg01.trans (Nat.gcd_dvd_right _ _)) hdk2
  have hd3 : d ^ 3 ∣ A := by
    rw [pow_succ, pow_two]
    exact mul_dvd_mul (mul_dvd_mul hdg01 hdg02) hdg12
  suffices hsuff : ∀ s ⊆ A.primeFactors.filter (fun p => ¬ p ∣ d),
      (∏ p ∈ s, p) * d ^ 3 ∣ A by
    simpa [mul_comm] using hsuff _ (Finset.Subset.refl _)
  intro s hs
  induction s using Finset.induction_on with
  | empty => simpa using hd3
  | insert p s' hp ih =>
    have hsub' : s' ⊆ A.primeFactors.filter (fun p => ¬ p ∣ d) :=
      (Finset.insert_subset_iff.mp hs).2
    have hpS : p ∈ A.primeFactors.filter (fun p => ¬ p ∣ d) :=
      (Finset.insert_subset_iff.mp hs).1
    obtain ⟨hpA, hpd⟩ := Finset.mem_filter.mp hpS
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpA
    have hpA' : p ∣ A := Nat.dvd_of_mem_primeFactors hpA
    have hcopd : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hpprime).mpr hpd
    have hcopd3 : Nat.Coprime p (d ^ 3) := hcopd.pow_right 3
    have ih' := ih hsub'
    have hcopP : Nat.Coprime p (∏ q ∈ s', q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqS : q ∈ A.primeFactors.filter (fun p => ¬ p ∣ d) := hsub' hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hqS).1
      have hqp : p ≠ q := by
        intro h
        exact hp (h ▸ hq)
      exact (Nat.Prime.coprime_iff_not_dvd hpprime).mpr (fun hpq =>
        hqp ((Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp hpq))
    have hcop : Nat.Coprime p ((∏ q ∈ s', q) * d ^ 3) := Nat.Coprime.mul_right hcopP hcopd3
    have hstep : p * ((∏ q ∈ s', q) * d ^ 3) ∣ A :=
      hcop.mul_dvd_of_dvd_of_dvd hpA' ih'
    rw [Finset.prod_insert hp, mul_assoc]
    exact hstep

/-! ### The reciprocal prime divisor product -/

/-- The sum of reciprocal divisors is at most `1 + log N`. -/
private theorem sum_divisors_inv_le_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ N.divisors, 1/(d:ℝ) ≤ 1 + Real.log N := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hinj : Set.InjOn (fun d : ℕ => d - 1) ↑(N.divisors) := by
    intro a ha b hb he
    have ha1 : 1 ≤ a := Nat.pos_of_mem_divisors ha
    have hb1 : 1 ≤ b := Nat.pos_of_mem_divisors hb
    have he' : a - 1 = b - 1 := he
    omega
  have himg := Finset.sum_image (s := N.divisors) (f := fun m : ℕ => (1:ℝ)/((m:ℝ)+1))
    (g := fun d : ℕ => d - 1) hinj
  have heq : ∑ d ∈ N.divisors, (1:ℝ)/(d:ℝ)
      = ∑ m ∈ N.divisors.image (fun d : ℕ => d - 1), (1:ℝ)/((m:ℝ)+1) := by
    rw [himg]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have h1 : ((d - 1 : ℕ) : ℝ) = (d:ℝ) - 1 := by
      rw [Nat.cast_sub hd1, Nat.cast_one]
    show (1:ℝ)/(d:ℝ) = (1:ℝ)/(((d - 1 : ℕ) : ℝ) + 1)
    rw [h1]
    norm_num
  rw [heq]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_range_inv_le_log N hN)
  · intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    refine Finset.mem_range.mpr ?_
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hd).1
    have hle : d ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
    omega
  · intro m _ _
    positivity

/-- The divisor sum normalised by `N` is the reciprocal divisor sum. -/
private theorem sigma_div_eq_sum_inv (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ N.divisors, (d:ℝ)) / (N:ℝ) = ∑ e ∈ N.divisors, 1/(e:ℝ) := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  rw [Finset.sum_div]
  refine Finset.sum_bij' (fun d _ => N / d) (fun e _ => N / e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.mem_divisors.mpr ⟨⟨d, (Nat.div_mul_cancel hdvd).symm⟩, hN0⟩
  · intro e he
    obtain ⟨hevd, -⟩ := Nat.mem_divisors.mp he
    exact Nat.mem_divisors.mpr ⟨⟨e, (Nat.div_mul_cancel hevd).symm⟩, hN0⟩
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.div_div_self hdvd hN0
  · intro e he
    obtain ⟨hevd, -⟩ := Nat.mem_divisors.mp he
    exact Nat.div_div_self hevd hN0
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have h1 : ((N/d : ℕ) : ℝ) * (d:ℝ) = (N:ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    have hd0 : (d:ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      positivity
    have hNd0 : ((N/d:ℕ) : ℝ) ≠ 0 := by
      have hpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd) (Nat.pos_of_mem_divisors hd)
      positivity
    field_simp
    linarith [h1]

/-- The normalised divisor sum is at most `1 + log N`. -/
private theorem sigma_div_le_log (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ N.divisors, (d:ℝ)) / (N:ℝ) ≤ 1 + Real.log N := by
  rw [sigma_div_eq_sum_inv N hN]
  exact sum_divisors_inv_le_log N hN

/-- The reciprocal prime factor product is dominated by the normalised divisor sum. -/
private theorem prod_one_add_inv_le_sigma (N : ℕ) (hN : 1 ≤ N) :
    (∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ))) ≤ (∑ d ∈ N.divisors, (d:ℝ)) / (N:ℝ) := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hA : (∑ d ∈ N.divisors, (d:ℝ))
      = ∏ p ∈ N.primeFactors, ((∑ k ∈ range (N.factorization p + 1), p^k : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, Nat.sum_divisors hN0, Nat.cast_prod]
  have hB : ((N:ℕ) : ℝ) = ∏ p ∈ N.primeFactors, ((p:ℝ))^(N.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN0]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p _
    rw [Nat.cast_pow]
  rw [hA, hB, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpprime.pos
    positivity
  · intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hv : 1 ≤ N.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpprime hN0).mp hpN
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpprime.pos
    have hpow : (0:ℝ) < (p:ℝ)^(N.factorization p) := by positivity
    have hcast : ((∑ k ∈ range (N.factorization p + 1), p^k : ℕ) : ℝ)
        = ∑ k ∈ range (N.factorization p + 1), (p:ℝ)^k := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.cast_pow]
    rw [hcast]
    have hmem1 : N.factorization p ∈ range (N.factorization p + 1) :=
      Finset.mem_range.mpr (by omega)
    have hmem2 : N.factorization p - 1 ∈ range (N.factorization p + 1) :=
      Finset.mem_range.mpr (by omega)
    have hsub : ({N.factorization p, N.factorization p - 1} : Finset ℕ)
        ⊆ range (N.factorization p + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hmem1
      · exact hmem2
    have hne : N.factorization p ∉ ({N.factorization p - 1} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    have htwo : ∑ k ∈ ({N.factorization p, N.factorization p - 1} : Finset ℕ), (p:ℝ)^k
        = (p:ℝ)^(N.factorization p) + (p:ℝ)^(N.factorization p - 1) := by
      rw [Finset.sum_insert hne, Finset.sum_singleton]
      try ring
    have hlow : (p:ℝ)^(N.factorization p) + (p:ℝ)^(N.factorization p - 1)
        ≤ ∑ k ∈ range (N.factorization p + 1), (p:ℝ)^k := by
      rw [← htwo]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    have hkey : (1 + 1/(p:ℝ))
        = ((p:ℝ)^(N.factorization p) + (p:ℝ)^(N.factorization p - 1)) / (p:ℝ)^(N.factorization p) := by
      have hsplit : (p:ℝ)^(N.factorization p)
          = (p:ℝ)^(N.factorization p - 1) * (p:ℝ) := by
        conv_lhs => rw [show N.factorization p = (N.factorization p - 1) + 1 from by omega]
        rw [pow_succ]
      rw [hsplit]
      field_simp
      try ring
    rw [hkey]
    gcongr

/-- The reciprocal prime divisor product grows at most like a fourth power of the logarithm. -/
private theorem prod_primeFactors_four_le_log (N : ℕ) (hN : 1 ≤ N) :
    (∏ p ∈ N.primeFactors, (1 + 4/(p:ℝ))) ≤ (1 + Real.log N)^4 := by
  have hpoint : ∀ p ∈ N.primeFactors, (1 + 4/(p:ℝ)) ≤ (1 + 1/(p:ℝ))^4 := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpprime.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hident : (1 + 1/(p:ℝ))^4 - 1 = 4/p + 6/p^2 + 4/p^3 + 1/p^4 := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 6/p^2 + 4/p^3 + 1/p^4 := by positivity
    linarith
  have hstep1 : (∏ p ∈ N.primeFactors, (1 + 4/(p:ℝ)))
      ≤ ∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ))^4 := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast hpprime.pos
      positivity
    · exact hpoint
  have hstep2 : (∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ))^4)
      = (∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ)))^4 := Finset.prod_pow _ _ _
  have hstep3 : (∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ)))
      ≤ 1 + Real.log N :=
    (prod_one_add_inv_le_sigma N hN).trans (sigma_div_le_log N hN)
  have hnonneg : (0:ℝ) ≤ ∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpprime.pos
    positivity
  calc (∏ p ∈ N.primeFactors, (1 + 4/(p:ℝ)))
      ≤ ∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ))^4 := hstep1
    _ = (∏ p ∈ N.primeFactors, (1 + 1/(p:ℝ)))^4 := hstep2
    _ ≤ (1 + Real.log N)^4 := pow_le_pow_left₀ hnonneg hstep3 4

/-! ### Per-prime factor bounds for the three classes -/

/-- A prime dividing the common gcd contributes at most its prime power. -/
private theorem factor_le_prime_pow (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hpd : p ∣ Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
      ≤ (p : ℝ) ^ (2 * (Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)).factorization p) := by
  set d := Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2) with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left (k 2) (Nat.gcd_pos_of_pos_left _ (hk 0))
  have hddk : ∀ i, d ∣ k i := by
    intro i
    fin_cases i
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    · exact Nat.gcd_dvd_right _ _
  have hγ1 : 1 ≤ d.factorization p := (hp.dvd_iff_one_le_factorization hd0.ne').mp hpd
  have hpk : ∀ i, p ^ d.factorization p ∣ k i := fun i =>
    (((hp.pow_dvd_iff_le_factorization hd0.ne').mpr le_rfl).trans (hddk i))
  have hγ : ∀ j, d.factorization p < j → ∃ i, ¬ p ^ j ∣ k i := by
    intro j hj
    have hnd : ¬ p ^ j ∣ d := by
      intro h
      have := (hp.pow_dvd_iff_le_factorization hd0.ne').mp h
      omega
    by_contra hcon
    push_neg at hcon
    exact hnd (Nat.dvd_gcd (Nat.dvd_gcd (hcon 0) (hcon 1)) (hcon 2))
  calc 1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
      ≤ 1 + ∑ j ∈ Icc 1 (d.factorization p), ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
        sum_Icc_prime_pow_le k l N p Q (d.factorization p) hp hk hl hγ1 hγ
    _ ≤ (p : ℝ) ^ (2 * (d.factorization p)) := common_prime_factor k l N p (d.factorization p) hp hk hl hpk

/-- The product of the prime factors of the common gcd is its square. -/
private theorem prod_primeFactors_pow_sq (d : ℕ) (hd0 : d ≠ 0) :
    (∏ p ∈ d.primeFactors, ((p : ℝ) ^ (2 * d.factorization p))) = (d : ℝ) ^ 2 := by
  have h1 : (∏ p ∈ d.primeFactors, ((p : ℝ) ^ d.factorization p)) = (d : ℝ) := by
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hd0]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p _
    rw [Nat.cast_pow]
  rw [← h1, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul, Nat.mul_comm 2 (d.factorization p)]

/-- The factors over primes dividing the common gcd multiply to at most its square. -/
private theorem prod_filter_dvd_le (k l : Fin 3 → ℕ) (N Q d : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hd : d = Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)) :
    (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter (fun p => p ∣ d),
        (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ (d : ℝ) ^ 2 := by
  have hd0 : 0 < d := by
    rw [hd]
    exact Nat.gcd_pos_of_pos_left (k 2) (Nat.gcd_pos_of_pos_left _ (hk 0))
  set S := ((range (Q + 1)).filter Nat.Prime).filter (fun p => p ∣ d) with hS
  set T := d.primeFactors with hT
  have hST : S ⊆ T := by
    intro p hp
    obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    exact Nat.mem_primeFactors.mpr ⟨hpprime, hpd, hd0.ne'⟩
  have hstep1 : (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, (p : ℝ) ^ (2 * d.factorization p) := by
    apply Finset.prod_le_prod₀
    · intro p _
      have : (0:ℝ) ≤ ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
        Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      linarith
    · intro p hp
      obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
      have hfac := factor_le_prime_pow k l N p Q (Finset.mem_filter.mp hpP).2 hk hl (hd ▸ hpd)
      rw [← hd] at hfac
      exact hfac
  have hstep2 : (∏ p ∈ S, (p : ℝ) ^ (2 * d.factorization p))
      ≤ ∏ p ∈ T, (p : ℝ) ^ (2 * d.factorization p) := by
    have hsplit := Finset.prod_sdiff hST (f := fun p : ℕ => (p : ℝ) ^ (2 * d.factorization p))
    have hone : (1:ℝ) ≤ ∏ p ∈ (T \ S), (p : ℝ) ^ (2 * d.factorization p) := by
      have h := Finset.prod_le_prod₀ (s := T \ S) (f := fun _ : ℕ => (1:ℝ))
        (g := fun p : ℕ => (p : ℝ) ^ (2 * d.factorization p))
        (fun i _ => zero_le_one) (fun p hp => ?_)
      · simpa using h
      · have hpT : p ∈ T := (Finset.mem_sdiff.mp hp).1
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpT
        have hv : 1 ≤ d.factorization p :=
          (hpprime.dvd_iff_one_le_factorization hd0.ne').mp (Nat.dvd_of_mem_primeFactors hpT)
        have hp1 : (1:ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
        calc (1:ℝ) = (1:ℝ) ^ (2 * d.factorization p) := by simp
          _ ≤ (p : ℝ) ^ (2 * d.factorization p) := by
            apply pow_le_pow_left₀ (by norm_num) hp1
    calc (∏ p ∈ S, (p : ℝ) ^ (2 * d.factorization p))
        = (∏ p ∈ S, (p : ℝ) ^ (2 * d.factorization p)) * 1 := by ring
      _ ≤ (∏ p ∈ S, (p : ℝ) ^ (2 * d.factorization p))
            * (∏ p ∈ (T \ S), (p : ℝ) ^ (2 * d.factorization p)) := by
          apply mul_le_mul_of_nonneg_left hone
          exact Finset.prod_nonneg fun p _ => by positivity
      _ = ∏ p ∈ T, (p : ℝ) ^ (2 * d.factorization p) := by rw [mul_comm]; exact hsplit
  calc (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, (p : ℝ) ^ (2 * d.factorization p) := hstep1
    _ ≤ ∏ p ∈ T, (p : ℝ) ^ (2 * d.factorization p) := hstep2
    _ = (d : ℝ) ^ 2 := prod_primeFactors_pow_sq d hd0.ne'

/-! ### Divisor count versus prime factor count -/

/-- The number of squarefree divisors is at most the number of divisors. -/
private theorem two_pow_card_primeFactors_le (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm, ← Finset.prod_const (2:ℕ)]
  apply Finset.prod_le_prod₀
  · intro p _
    norm_num
  · intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hv : 1 ≤ m.factorization p :=
      (hpprime.dvd_iff_one_le_factorization hm).mp (Nat.dvd_of_mem_primeFactors hp)
    omega

/-- The prime factor count of a product is at most the sum. -/
private theorem card_primeFactors_mul_le (m n : ℕ) :
    (m * n).primeFactors.card ≤ m.primeFactors.card + n.primeFactors.card := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · rw [Nat.primeFactors_mul hm.ne' hn.ne']
      exact Finset.card_union_le _ _

/-- `2 e^2 ≤ 16`, the ratio between the prime divisor counts and the divisor count. -/
private theorem two_mul_exp_two_le_sixteen : 2 * Real.exp 2 ≤ 16 := by
  have hlog2 : (2:ℝ)/3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 from by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 : (2:ℝ) < Real.log 8 := by rw [hlog8]; linarith
  have hexp : Real.exp 2 < Real.exp (Real.log 8) := Real.exp_lt_exp.mpr h2
  rw [Real.exp_log (by norm_num : (0:ℝ) < 8)] at hexp
  linarith

/-- A prime not dividing the common gcd contributes at most `1 + p`. -/
private theorem factor_le_one_add (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ¬ p ∣ Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤ 1 + (p:ℝ) := by
  set d := Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2) with hd
  have hex : ∃ i, ¬ p ∣ k i := by
    by_contra hcon
    push_neg at hcon
    exact hnd (Nat.dvd_gcd (Nat.dvd_gcd (hcon 0) (hcon 1)) (hcon 2))
  have hvanish : ∀ j, 2 ≤ j → ∃ i, ¬ p ^ j ∣ k i := by
    intro j hj
    by_contra hcon
    push_neg at hcon
    apply hnd
    have : p ^ j ∣ Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2) :=
      Nat.dvd_gcd (Nat.dvd_gcd (hcon 0) (hcon 1)) (hcon 2)
    exact dvd_trans (dvd_pow_self p (by omega)) this
  have hss : ‖ssTerm k l N p‖ ≤ 1 := ssTerm_prime_norm_le_one k l N p hp hk hl hex
  have hzero : ∀ j ∈ Icc 1 Q, j ≠ 1 → ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ = 0 := by
    intro j hj hj1
    have hj2 : 2 ≤ j := by
      have h1 : 1 ≤ j := (mem_Icc.mp hj).1
      omega
    rw [ssTerm_prime_pow_vanish k l N p j hp hj2 hk hl (hvanish j hj2), norm_zero, mul_zero]
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp
  · have hmem : (1:ℕ) ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
    have hsub : ({1} : Finset ℕ) ⊆ Icc 1 Q := by
      intro x hx
      rw [mem_singleton.mp hx]
      exact hmem
    have hzero' : ∀ x ∈ Icc 1 Q, x ∉ ({1} : Finset ℕ) →
        ((p ^ x : ℕ) : ℝ) * ‖ssTerm k l N (p ^ x)‖ = 0 := by
      intro x hx hx1
      exact hzero x hx (by simpa using hx1)
    have hsingle : ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
        = (p:ℝ) * ‖ssTerm k l N p‖ := by
      rw [← Finset.sum_subset hsub hzero', Finset.sum_singleton]
      simp only [pow_one]
    rw [hsingle]
    have hh := mul_le_mul_of_nonneg_left hss (Nat.cast_nonneg p : (0:ℝ) ≤ (p:ℝ))
    rw [mul_one] at hh
    linarith

/-- A product of `1 + x` is bounded by the exponential of the sum. -/
private theorem prod_one_add_le_exp {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1 + f i)) ≤ Real.exp (∑ i ∈ s, f i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i hi
    linarith [hf i hi]
  · intro i hi
    simpa [add_comm] using Real.add_one_le_exp (f i)

/-- The reciprocal prime power sum over the primes below `Q` is bounded by `4`. -/
private theorem sum_primes_inv_sq_le (Q : ℕ) :
    ∑ p ∈ (range (Q + 1)).filter Nat.Prime, (p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3 ≤ 4 := by
  set P := (range (Q + 1)).filter Nat.Prime with hP
  have hstep : ∀ p ∈ P, (p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3 ≤ 2 / (((p - 2 : ℕ) : ℝ) + 1)^2 := by
    intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp2 : 2 ≤ p := hpprime.two_le
    have hpR : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.one_le
    have hsub : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
      rw [Nat.cast_sub hpprime.one_le, Nat.cast_one]
    have hsub2 : ((p - 2 : ℕ) : ℝ) = (p:ℝ) - 2 := by
      rw [Nat.cast_sub hp2, Nat.cast_ofNat]
    have hpos : (0:ℝ) < (p:ℝ) - 1 := by linarith
    rw [hsub, hsub2]
    have hpos2 : (0:ℝ) < (p:ℝ) - 2 + 1 := by linarith
    rw [show (p:ℝ) - 2 + 1 = (p:ℝ) - 1 by ring]
    have hkey : (p:ℝ) * (((p:ℝ) - 1)⁻¹)^3 = (p:ℝ) / ((p:ℝ) - 1)^3 := by
      rw [inv_pow]
      field_simp
    rw [hkey]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hpR]
  have hinj : Set.InjOn (fun p : ℕ => p - 2) ↑P := by
    intro a ha b hb he
    have ha2 : 2 ≤ a := (Finset.mem_filter.mp ha).2.two_le
    have hb2 : 2 ≤ b := (Finset.mem_filter.mp hb).2.two_le
    have he' : a - 2 = b - 2 := he
    omega
  have himg : ∑ p ∈ P, (2 / (((p - 2 : ℕ) : ℝ) + 1)^2)
      = ∑ m ∈ P.image (fun p => p - 2), (2 / (((m:ℕ) : ℝ) + 1)^2) :=
    (Finset.sum_image (f := fun m : ℕ => 2 / (((m:ℕ) : ℝ) + 1)^2) hinj).symm
  have hsub : P.image (fun p => p - 2) ⊆ range Q := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have hpQ : p ≤ Q := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      omega
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    exact Finset.mem_range.mpr (by omega)
  have hbound : ∑ m ∈ range Q, (2 / (((m:ℕ) : ℝ) + 1)^2) ≤ 4 := by
    have hQ : ∑ m ∈ range Q, (2 / (((m:ℕ) : ℝ) + 1)^2)
        = 2 * ∑ m ∈ range Q, (1 / (((m:ℕ) : ℝ) + 1)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [hQ]
    have h2 : ∑ m ∈ range Q, (1:ℝ) / (((m:ℕ) : ℝ) + 1)^2 ≤ 2 := by
      rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
      · subst hQ0; simp
      · exact (sum_range_inv_sq_le Q hQpos).trans (by
          have hpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQpos
          have : (0:ℝ) < 1/(Q:ℝ) := by positivity
          linarith)
    linarith
  calc ∑ p ∈ P, (p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3
      ≤ ∑ p ∈ P, (2 / (((p - 2 : ℕ) : ℝ) + 1)^2) := Finset.sum_le_sum hstep
    _ = ∑ m ∈ P.image (fun p => p - 2), (2 / (((m:ℕ) : ℝ) + 1)^2) := himg
    _ ≤ ∑ m ∈ range Q, (2 / (((m:ℕ) : ℝ) + 1)^2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    _ ≤ 4 := hbound

/-- The factors over the pairwise-only primes are bounded by the pairwise gcd envelope. -/
private theorem prod_pair_le (k l : Fin 3 → ℕ) (N Q d A : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hd : d = Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2))
    (hA : A = Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) :
    (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ d ∧ p ∣ A),
        (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ 2 ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ d ∧ p ∣ A)).card * ((A : ℝ) / (d : ℝ) ^ 3) := by
  have hd0 : 0 < d := by
    rw [hd]
    exact Nat.gcd_pos_of_pos_left (k 2) (Nat.gcd_pos_of_pos_left _ (hk 0))
  set S := ((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ d ∧ p ∣ A) with hS
  set T := A.primeFactors.filter (fun p => ¬ p ∣ d) with hT
  have hST : S ⊆ T := by
    intro p hp
    obtain ⟨hpP, hpd, hpA⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hA0 : A ≠ 0 := by
      rw [hA]
      have h1 : 0 < Nat.gcd (k 0) (k 1) := Nat.gcd_pos_of_pos_left _ (hk 0)
      have h2 : 0 < Nat.gcd (k 0) (k 2) := Nat.gcd_pos_of_pos_left _ (hk 0)
      have h3 : 0 < Nat.gcd (k 1) (k 2) := Nat.gcd_pos_of_pos_left _ (hk 1)
      positivity
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hpA, hA0⟩, hpd⟩
  -- step 1: per-prime bound
  have hstep1 : (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, (2 * (p:ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro p _
      have : (0:ℝ) ≤ ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
        Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      linarith
    · intro p hp
      obtain ⟨hpP, hpd, -⟩ := Finset.mem_filter.mp hp
      have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
      have hfac := factor_le_one_add k l N p Q hpprime hk hl (hd ▸ hpd)
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.one_le
      linarith
  -- step 2: the product of the primes is at most A/d^3
  have hprod : (∏ p ∈ S, (p:ℝ)) ≤ (A : ℝ) / (d : ℝ) ^ 3 := by
    have hT1 : (∏ p ∈ T, (p:ℝ)) ≤ (A : ℝ) / (d : ℝ) ^ 3 := by
      have hdvd := d3_prod_dvd k hk
      rw [← hA, ← hd] at hdvd
      have hApos : 0 < A := by
        rw [hA]
        have h1 : 0 < Nat.gcd (k 0) (k 1) := Nat.gcd_pos_of_pos_left _ (hk 0)
        have h2 : 0 < Nat.gcd (k 0) (k 2) := Nat.gcd_pos_of_pos_left _ (hk 0)
        have h3 : 0 < Nat.gcd (k 1) (k 2) := Nat.gcd_pos_of_pos_left _ (hk 1)
        positivity
      have hcast : (d:ℝ) ^ 3 * (∏ p ∈ T, (p:ℝ)) ≤ (A:ℝ) := by
        have hnat : d ^ 3 * (∏ p ∈ T, p) ≤ A := Nat.le_of_dvd hApos hdvd
        have h : ((d ^ 3 * (∏ p ∈ T, p) : ℕ) : ℝ) ≤ ((A : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at h
        exact h
      have hpos : (0:ℝ) < (d:ℝ)^3 :=
        pow_pos (by exact_mod_cast hd0 : (0:ℝ) < (d:ℝ)) 3
      rw [le_div_iff₀ hpos]
      calc (∏ p ∈ T, (p:ℝ)) * (d:ℝ)^3 = (d:ℝ)^3 * (∏ p ∈ T, (p:ℝ)) := by ring
        _ ≤ (A:ℝ) := hcast
    have hsub : (∏ p ∈ S, (p:ℝ)) ≤ ∏ p ∈ T, (p:ℝ) := by
      have hsplit := Finset.prod_sdiff (s₁ := S) (s₂ := T) (f := fun p : ℕ => (p:ℝ)) hST
      have hone : (1:ℝ) ≤ ∏ p ∈ (T \ S), (p:ℝ) := by
        have h := Finset.prod_le_prod₀ (s := T \ S) (f := fun _ : ℕ => (1:ℝ))
          (g := fun p : ℕ => (p:ℝ))
          (fun i _ => zero_le_one)
          (fun p hp => by
            have := (Finset.mem_sdiff.mp hp).1
            have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp this).1
            have : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.one_le
            simpa using this)
        simpa using h
      calc (∏ p ∈ S, (p:ℝ)) = (∏ p ∈ S, (p:ℝ)) * 1 := by ring
        _ ≤ (∏ p ∈ S, (p:ℝ)) * (∏ p ∈ (T \ S), (p:ℝ)) := by
            apply mul_le_mul_of_nonneg_left hone
            exact Finset.prod_nonneg fun p _ => by positivity
        _ = ∏ p ∈ T, (p:ℝ) := by
            rw [mul_comm]; exact hsplit
    exact hsub.trans hT1
  -- combine
  calc (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, (2 * (p:ℝ)) := hstep1
    _ = (2:ℝ) ^ S.card * (∏ p ∈ S, (p:ℝ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ (2:ℝ) ^ S.card * ((A : ℝ) / (d : ℝ) ^ 3) := by
        apply mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((2:ℕ) : ℝ) ^ S.card * ((A : ℝ) / (d : ℝ) ^ 3) := by norm_num

/-- If a prime misses the pairwise envelope then it misses at least two moduli. -/
private theorem two_not_dvd_of_not_dvd_prod (p : ℕ) (k : Fin 3 → ℕ)
    (h : ¬ p ∣ Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) :
    ∃ i j : Fin 3, i ≠ j ∧ ¬ p ∣ k i ∧ ¬ p ∣ k j := by
  have key01 : p ∣ Nat.gcd (k 0) (k 1) →
      p ∣ Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2) :=
    fun hh => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hh _) _
  have key02 : p ∣ Nat.gcd (k 0) (k 2) →
      p ∣ Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2) :=
    fun hh => dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hh _) _
  have key12 : p ∣ Nat.gcd (k 1) (k 2) →
      p ∣ Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2) :=
    fun hh => dvd_mul_of_dvd_right hh _
  by_cases h0 : p ∣ k 0
  · by_cases h1 : p ∣ k 1
    · exact absurd (key01 (Nat.dvd_gcd h0 h1)) h
    · by_cases h2 : p ∣ k 2
      · exact absurd (key02 (Nat.dvd_gcd h0 h2)) h
      · exact ⟨1, 2, by decide, h1, h2⟩
  · by_cases h1 : p ∣ k 1
    · by_cases h2 : p ∣ k 2
      · exact absurd (key12 (Nat.dvd_gcd h1 h2)) h
      · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 1, by decide, h0, h1⟩

/-- The factor over a prime that is coprime to two moduli is at most two. -/
private theorem factor_le_two (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ∃ i j : Fin 3, i ≠ j ∧ ¬ p ∣ k i ∧ ¬ p ∣ k j) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤ 2 * (1 + 1/(p:ℝ)) := by
  have hss : ‖ssTerm k l N p‖ ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := ssTerm_prime_norm_le_inv k l N p hp hk hl hnd
  obtain ⟨i0, j0, -, hi0, -⟩ := hnd
  have hvan : ∃ i, ¬ p ∣ k i := ⟨i0, hi0⟩
  have hvanish : ∀ j, 2 ≤ j → ∃ i, ¬ p ^ j ∣ k i := by
    intro j hj
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := hvan
    exact hi (dvd_trans (dvd_pow_self p (by omega)) (hcon i))
  have hzero : ∀ j ∈ Icc 1 Q, j ≠ 1 → ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ = 0 := by
    intro j hj hj1
    have hj2 : 2 ≤ j := by
      have h1 : 1 ≤ j := (mem_Icc.mp hj).1
      omega
    rw [ssTerm_prime_pow_vanish k l N p j hp hj2 hk hl (hvanish j hj2), norm_zero, mul_zero]
  have hpprime2 : 2 ≤ p := hp.two_le
  have hpR : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_le
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp only [Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.sum_empty, add_zero]
    have h1 : (0:ℝ) ≤ 1/(p:ℝ) := by positivity
    linarith
  · have hmem : (1:ℕ) ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
    have hsub : ({1} : Finset ℕ) ⊆ Icc 1 Q := by
      intro x hx
      rw [mem_singleton.mp hx]
      exact hmem
    have hzero' : ∀ x ∈ Icc 1 Q, x ∉ ({1} : Finset ℕ) →
        ((p ^ x : ℕ) : ℝ) * ‖ssTerm k l N (p ^ x)‖ = 0 := by
      intro x hx hx1
      exact hzero x hx (by simpa using hx1)
    have hsingle : ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
        = (p:ℝ) * ‖ssTerm k l N p‖ := by
      rw [← Finset.sum_subset hsub hzero', Finset.sum_singleton]
      simp only [pow_one]
    rw [hsingle]
    have hcpos : (0:ℝ) ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hbound : (p:ℝ) * ((p - 1 : ℕ) : ℝ)⁻¹ ≤ 1 + 2/(p:ℝ) := by
      have hsub2 : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
        rw [Nat.cast_sub hp.one_le, Nat.cast_one]
      rw [hsub2, inv_eq_one_div]
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
      have hpos : (0:ℝ) < (p:ℝ) - 1 := by linarith
      rw [mul_one_div, div_le_iff₀ hpos]
      have hp1 : (0:ℝ) < (p:ℝ) := by linarith
      field_simp
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hss (Nat.cast_nonneg p : (0:ℝ) ≤ (p:ℝ))
    have hmain : 1 + (p:ℝ) * ‖ssTerm k l N p‖ ≤ 2 + 2/(p:ℝ) := by linarith
    calc 1 + (p:ℝ) * ‖ssTerm k l N p‖
        ≤ 2 + 2/(p:ℝ) := hmain
      _ = 2 * (1 + 1/(p:ℝ)) := by
          rw [mul_add, mul_one, mul_one_div]

/-- Outside the common modulus only the `j = 1` term of the prime power sum survives. -/
private theorem sum_Icc_eq_prime (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hnd : ∃ i, ¬ p ∣ k i) (hQ : 1 ≤ Q) :
    ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
      = (p:ℝ) * ‖ssTerm k l N p‖ := by
  have hvanish : ∀ j, 2 ≤ j → ∃ i, ¬ p ^ j ∣ k i := by
    intro j hj
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := hnd
    exact hi (dvd_trans (dvd_pow_self p (by omega)) (hcon i))
  have hzero : ∀ j ∈ Icc 1 Q, j ≠ 1 → ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ = 0 := by
    intro j hj hj1
    have hj2 : 2 ≤ j := by
      have h1 : 1 ≤ j := (mem_Icc.mp hj).1
      omega
    rw [ssTerm_prime_pow_vanish k l N p j hp hj2 hk hl (hvanish j hj2), norm_zero, mul_zero]
  have hmem : (1:ℕ) ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  have hsub : ({1} : Finset ℕ) ⊆ Icc 1 Q := by
    intro x hx
    rw [mem_singleton.mp hx]
    exact hmem
  have hzero' : ∀ x ∈ Icc 1 Q, x ∉ ({1} : Finset ℕ) →
      ((p ^ x : ℕ) : ℝ) * ‖ssTerm k l N (p ^ x)‖ = 0 := by
    intro x hx hx1
    exact hzero x hx (by simpa using hx1)
  rw [← Finset.sum_subset hsub hzero', Finset.sum_singleton]
  simp only [pow_one]

/-- A prime missing the pairwise envelope gives a factor at most three. -/
private theorem factor_le_three (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hndA : ¬ p ∣ Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤ 3 := by
  obtain ⟨i0, j0, hne, hi0, hj0⟩ := two_not_dvd_of_not_dvd_prod p k hndA
  have htwo : ∃ i j : Fin 3, i ≠ j ∧ ¬ p ∣ k i ∧ ¬ p ∣ k j := ⟨i0, j0, hne, hi0, hj0⟩
  have hfac := factor_le_two k l N p Q hp hk hl htwo
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) := by linarith
  have h3 : 2 * (1 + 1/(p:ℝ)) ≤ 3 := by
    rw [mul_add, mul_one, mul_one_div, show (3:ℝ) = 2 + 1 by norm_num]
    have h2 : 2/(p:ℝ) ≤ 1 := by
      rw [div_le_one hp1]
      linarith
    linarith
  linarith

/-- A prime missing both the pairwise envelope and the moduli, but dividing `N`. -/
private theorem factor_le_one_add_four (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hndK : ∀ i, ¬ p ∣ k i) (hpN : p ∣ N) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤ 1 + 4/(p:ℝ) := by
  have hss := ssTerm_prime_norm_le_not_dvd k l N p hp hk hl hndK
  rw [if_pos hpN] at hss
  have hc2 : ‖ssTerm k l N p‖ ≤ (((p - 1 : ℕ) : ℝ)⁻¹)^2 := by
    simpa using hss
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hsub : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hbound : (p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^2 ≤ 4/(p:ℝ) := by
    rw [hsub]
    have hp1 : (0:ℝ) < (p:ℝ) := by linarith
    have hp2' : (0:ℝ) < (p:ℝ) - 1 := by linarith
    field_simp
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hc2 (Nat.cast_nonneg p : (0:ℝ) ≤ (p:ℝ))
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp only [Icc_eq_empty (by omega : ¬ (1:ℕ) ≤ 0), Finset.sum_empty, add_zero]
    have h4 : (0:ℝ) ≤ 4/(p:ℝ) := by positivity
    linarith
  · have hsum := sum_Icc_eq_prime k l N p Q hp hk hl ⟨0, hndK 0⟩ hQ
    rw [hsum]
    linarith

/-- A prime missing both the pairwise envelope and the moduli, and not dividing `N`. -/
private theorem factor_le_exp (k l : Fin 3 → ℕ) (N p Q : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hndK : ∀ i, ¬ p ∣ k i) (hpN : ¬ p ∣ N) :
    1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖
      ≤ Real.exp ((p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3) := by
  have hss := ssTerm_prime_norm_le_not_dvd k l N p hp hk hl hndK
  rw [if_neg hpN] at hss
  have hexp := Real.add_one_le_exp ((p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3)
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp only [Icc_eq_empty (by omega : ¬ (1:ℕ) ≤ 0), Finset.sum_empty, add_zero]
    have hbase : (0:ℝ) ≤ (p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3 := by positivity
    linarith
  · have hsum := sum_Icc_eq_prime k l N p Q hp hk hl ⟨0, hndK 0⟩ hQ
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hss (Nat.cast_nonneg p : (0:ℝ) ≤ (p:ℝ))
    linarith

/-- The class of primes that miss the pairwise envelope but divide a modulus. -/
private theorem prod_filter_three_le (k l : Fin 3 → ℕ) (N Q A : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hA : A = Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) :
    (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
        (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2),
        (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ 3 ^ (((range (Q + 1)).filter Nat.Prime).filter
        (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2)).card := by
  set S := ((range (Q + 1)).filter Nat.Prime).filter
    (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2) with hS
  have hstep : ∀ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖) ≤ 3 := by
    intro p hp
    obtain ⟨hpP, hndA, -⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    exact factor_le_three k l N p Q hpprime hk hl (hA ▸ hndA)
  have h := Finset.prod_le_prod₀ (s := S)
    (f := fun p => (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
    (g := fun _ => (3:ℝ))
    (fun p _ => by
      have : (0:ℝ) ≤ ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
        Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      linarith)
    hstep
  rwa [Finset.prod_const] at h

/-- The class of primes that miss the pairwise envelope and the moduli but divide `N`. -/
private theorem prod_filter_four_le (k l : Fin 3 → ℕ) (N Q A : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hA : A = Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2))
    (hN : 1 ≤ N) :
    (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
        (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ p ∣ N),
        (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ (1 + Real.log N) ^ 4 := by
  set S := ((range (Q + 1)).filter Nat.Prime).filter
    (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ p ∣ N) with hS
  set T := N.primeFactors with hT
  have hST : S ⊆ T := by
    intro p hp
    obtain ⟨hpP, -, -, hpN⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    exact Nat.mem_primeFactors.mpr ⟨hpprime, hpN, (Nat.ne_of_gt hN)⟩
  have hstep1 : (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, (1 + 4/(p:ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro p _
      have : (0:ℝ) ≤ ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
        Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      linarith
    · intro p hp
      obtain ⟨hpP, hndA, hndK, hpN⟩ := Finset.mem_filter.mp hp
      have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
      refine factor_le_one_add_four k l N p Q hpprime hk hl ?_ hpN
      intro i
      fin_cases i
      · intro h
        exact hndK (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h (k 1)) (k 2))
      · intro h
        exact hndK (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h (k 0)) (k 2))
      · intro h
        exact hndK (dvd_mul_of_dvd_right h (k 0 * k 1))
  have hstep2 : (∏ p ∈ S, (1 + 4/(p:ℝ))) ≤ ∏ p ∈ T, (1 + 4/(p:ℝ)) := by
    have hsplit := Finset.prod_sdiff (s₁ := S) (s₂ := T) (f := fun p : ℕ => 1 + 4/(p:ℝ)) hST
    have hone : (1:ℝ) ≤ ∏ p ∈ (T \ S), (1 + 4/(p:ℝ)) := by
      have h := Finset.prod_le_prod₀ (s := T \ S) (f := fun _ : ℕ => (1:ℝ))
        (g := fun p : ℕ => 1 + 4/(p:ℝ))
        (fun i _ => zero_le_one)
        (fun p hp => by
          have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
          have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.one_le
          have : (0:ℝ) ≤ 4/(p:ℝ) := by positivity
          linarith)
      simpa using h
    calc (∏ p ∈ S, (1 + 4/(p:ℝ))) = (∏ p ∈ S, (1 + 4/(p:ℝ))) * 1 := by ring
      _ ≤ (∏ p ∈ S, (1 + 4/(p:ℝ))) * (∏ p ∈ (T \ S), (1 + 4/(p:ℝ))) := by
          apply mul_le_mul_of_nonneg_left hone
          exact Finset.prod_nonneg fun p _ => by positivity
      _ = ∏ p ∈ T, (1 + 4/(p:ℝ)) := by
          rw [mul_comm]; exact hsplit
  exact hstep1.trans (hstep2.trans (prod_primeFactors_four_le_log N hN))

/-- The class of primes that miss the pairwise envelope, the moduli and `N`. -/
private theorem prod_filter_exp_le (k l : Fin 3 → ℕ) (N Q A : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hA : A = Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2)) :
    (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
        (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ ¬ p ∣ N),
        (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ Real.exp 4 := by
  set S := ((range (Q + 1)).filter Nat.Prime).filter
    (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ ¬ p ∣ N) with hS
  set g : ℕ → ℝ := fun p => (p:ℝ) * (((p - 1 : ℕ) : ℝ)⁻¹)^3 with hg
  have hpoint : ∀ p ∈ S,
      (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖) ≤ Real.exp (g p) := by
    intro p hp
    obtain ⟨hpP, hndA, hndK, hpN⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hndKi : ∀ i, ¬ p ∣ k i := by
      intro i
      fin_cases i
      · intro h
        exact hndK (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h (k 1)) (k 2))
      · intro h
        exact hndK (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h (k 0)) (k 2))
      · intro h
        exact hndK (dvd_mul_of_dvd_right h (k 0 * k 1))
    have := factor_le_exp k l N p Q hpprime hk hl hndKi hpN
    rw [hg]
    exact this
  have hstep1 : (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, Real.exp (g p) := by
    apply Finset.prod_le_prod₀
    · intro p _
      have : (0:ℝ) ≤ ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ :=
        Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      linarith
    · exact hpoint
  have hstep2 : (∏ p ∈ S, Real.exp (g p)) = Real.exp (∑ p ∈ S, g p) := by
    rw [Real.exp_sum]
  have hsub : S ⊆ (range (Q + 1)).filter Nat.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hstep3 : (∑ p ∈ S, g p) ≤ 4 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans (sum_primes_inv_sq_le Q)
    intro p _ _
    rw [hg]
    positivity
  calc (∏ p ∈ S, (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      ≤ ∏ p ∈ S, Real.exp (g p) := hstep1
    _ = Real.exp (∑ p ∈ S, g p) := hstep2
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hstep3

/-- The prime divisor counts of the two middle classes are absorbed by the divisor counts. -/
private theorem pow_card_mul_le_divisor_prod (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i)
    (s2 s3 : Finset ℕ) (h2 : s2 ⊆ (k 0 * k 1 * k 2).primeFactors)
    (h3 : s3 ⊆ (k 0 * k 1 * k 2).primeFactors) :
    (2:ℝ) ^ s2.card * (3:ℝ) ^ s3.card
      ≤ ∏ i : Fin 3, ((k i).divisors.card : ℝ) ^ 4 := by
  set ωK := (k 0 * k 1 * k 2).primeFactors.card with hωKdef
  set ω := (k 0).primeFactors.card + (k 1).primeFactors.card + (k 2).primeFactors.card with hωdef
  have hω : ωK ≤ ω := by
    have h1 := card_primeFactors_mul_le (k 0 * k 1) (k 2)
    have h2' := card_primeFactors_mul_le (k 0) (k 1)
    rw [hωKdef, hωdef]
    omega
  have hc2 : s2.card ≤ ωK := Finset.card_le_card h2
  have hc3 : s3.card ≤ ωK := Finset.card_le_card h3
  have step1 : (2:ℝ) ^ s2.card * (3:ℝ) ^ s3.card ≤ (2:ℝ) ^ ωK * (3:ℝ) ^ ωK :=
    mul_le_mul (pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) hc2)
      (pow_le_pow_right₀ (a := (3:ℝ)) (by norm_num) hc3)
      (by positivity) (by positivity)
  have step2 : (2:ℝ) ^ ωK * (3:ℝ) ^ ωK = (6:ℝ) ^ ωK := by
    rw [← mul_pow]
    norm_num
  have step3 : (6:ℝ) ^ ωK ≤ (6:ℝ) ^ ω :=
    pow_le_pow_right₀ (a := (6:ℝ)) (by norm_num) hω
  have step4 : (6:ℝ) ^ ω ≤ (16:ℝ) ^ ω :=
    pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (6:ℝ) ≤ 16) ω
  have step5 : (16:ℝ) ^ ω = ((2:ℝ) ^ ω) ^ 4 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have step6 : ((2:ℝ) ^ ω) = ∏ i : Fin 3, (2:ℝ) ^ ((k i).primeFactors.card) := by
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [hωdef, Fin.sum_univ_three]
  have step7 : (∏ i : Fin 3, (2:ℝ) ^ ((k i).primeFactors.card))
      ≤ ∏ i : Fin 3, ((k i).divisors.card : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    · intro i _
      have hki : k i ≠ 0 := by have := hk i; omega
      have h := two_pow_card_primeFactors_le (k i) hki
      have h' : (2:ℝ) ^ ((k i).primeFactors.card) ≤ ((k i).divisors.card : ℝ) := by
        exact_mod_cast h
      exact h'
  have step8 : (∏ i : Fin 3, ((k i).divisors.card : ℝ)) ^ 4
      = ∏ i : Fin 3, ((k i).divisors.card : ℝ) ^ 4 :=
    (Finset.prod_pow (univ : Finset (Fin 3)) 4
      (fun i => ((k i).divisors.card : ℝ))).symm
  calc (2:ℝ) ^ s2.card * (3:ℝ) ^ s3.card ≤ (2:ℝ) ^ ωK * (3:ℝ) ^ ωK := step1
    _ = (6:ℝ) ^ ωK := step2
    _ ≤ (6:ℝ) ^ ω := step3
    _ ≤ (16:ℝ) ^ ω := step4
    _ = ((2:ℝ) ^ ω) ^ 4 := step5
    _ = (∏ i : Fin 3, (2:ℝ) ^ ((k i).primeFactors.card)) ^ 4 := by rw [step6]
    _ ≤ (∏ i : Fin 3, ((k i).divisors.card : ℝ)) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity) step7
    _ = ∏ i : Fin 3, ((k i).divisors.card : ℝ) ^ 4 := step8



/-- Splitting a product over primes into the five disjoint classes used below. -/
private theorem prod_filter_chain (P : Finset ℕ) (F : ℕ → ℝ) (d A K N : ℕ) (hdvdA : d ∣ A) :
    ∏ p ∈ P, F p
      = (∏ p ∈ P.filter (fun p => p ∣ d), F p)
        * ((∏ p ∈ P.filter (fun p => ¬ p ∣ d ∧ p ∣ A), F p)
        * ((∏ p ∈ P.filter (fun p => ¬ p ∣ A ∧ p ∣ K), F p)
        * ((∏ p ∈ P.filter (fun p => ¬ p ∣ A ∧ ¬ p ∣ K ∧ p ∣ N), F p)
        * (∏ p ∈ P.filter (fun p => ¬ p ∣ A ∧ ¬ p ∣ K ∧ ¬ p ∣ N), F p)))) := by
  have h2b : (P.filter (fun p => ¬ p ∣ d)).filter (fun p => ¬ p ∣ A)
      = P.filter (fun p => ¬ p ∣ A) := by
    rw [Finset.filter_filter]
    congr 1
    funext p
    apply propext
    exact ⟨fun h => h.2, fun h => ⟨fun hpd => h (hpd.trans hdvdA), h⟩⟩
  rw [← Finset.prod_filter_mul_prod_filter_not (s := P) (p := fun p => p ∣ d) (f := F)]
  rw [← Finset.prod_filter_mul_prod_filter_not (s := P.filter (fun p => ¬ p ∣ d))
    (p := fun p => p ∣ A) (f := F)]
  rw [Finset.filter_filter (s := P) (p := fun p => ¬ p ∣ d) (q := fun p => p ∣ A), h2b]
  rw [← Finset.prod_filter_mul_prod_filter_not (s := P.filter (fun p => ¬ p ∣ A))
    (p := fun p => p ∣ K) (f := F)]
  rw [Finset.filter_filter (s := P) (p := fun p => ¬ p ∣ A) (q := fun p => p ∣ K)]
  rw [Finset.filter_filter (s := P) (p := fun p => ¬ p ∣ A) (q := fun p => ¬ p ∣ K)]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (s := P.filter (fun p => ¬ p ∣ A ∧ ¬ p ∣ K)) (p := fun p => p ∣ N) (f := F)]
  rw [Finset.filter_filter (s := P) (p := fun p => ¬ p ∣ A ∧ ¬ p ∣ K) (q := fun p => p ∣ N)]
  rw [Finset.filter_filter (s := P) (p := fun p => ¬ p ∣ A ∧ ¬ p ∣ K) (q := fun p => ¬ p ∣ N)]
  have hre1 : (P.filter (fun p => (¬ p ∣ A ∧ ¬ p ∣ K) ∧ p ∣ N))
      = P.filter (fun p => ¬ p ∣ A ∧ ¬ p ∣ K ∧ p ∣ N) := by
    congr 1
    funext p
    apply propext
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  have hre2 : (P.filter (fun p => (¬ p ∣ A ∧ ¬ p ∣ K) ∧ ¬ p ∣ N))
      = P.filter (fun p => ¬ p ∣ A ∧ ¬ p ∣ K ∧ ¬ p ∣ N) := by
    congr 1
    funext p
    apply propext
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  rw [hre1, hre2]

/-- The five class bounds combine into the coefficient envelope. -/
private theorem class_product_le_envelope (k : Fin 3 → ℕ) (N : ℕ) (X : ℝ) (d A : ℕ)
    (s2 s3 : Finset ℕ)
    (hk : ∀ i, 1 ≤ k i) (hL : 1 ≤ Real.log X)
    (hlogN : 1 + Real.log N ≤ 2 * Real.log X)
    (hd : d = Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2))
    (hA : A = Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2))
    (h2 : s2 ⊆ (k 0 * k 1 * k 2).primeFactors)
    (h3 : s3 ⊆ (k 0 * k 1 * k 2).primeFactors) :
    ((d:ℝ)^2 * ((2:ℝ)^s2.card * ((A:ℝ)/(d:ℝ)^3)))
        * ((3:ℝ)^s3.card * ((1 + Real.log N)^4 * Real.exp 4))
      ≤ 10000 * ((A:ℝ)/(d:ℝ)) * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4)
        * (Real.log X)^11 := by
  have hd0 : (0:ℝ) < (d:ℝ) := by
    rw [hd]
    exact_mod_cast Nat.gcd_pos_of_pos_left (k 2) (Nat.gcd_pos_of_pos_left _ (hk 0))
  have he4 : Real.exp 4 ≤ 100 := by
    have h1 : Real.exp 4 = (Real.exp 2)^2 := by
      rw [show (4:ℝ) = ((2:ℕ) : ℝ) * 2 by norm_num, Real.exp_nat_mul]
    have h2 : Real.exp 2 ≤ 8 := by linarith [two_mul_exp_two_le_sixteen]
    have h3 : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
    nlinarith [h1, h2, h3]
  have hA2 : (d:ℝ)^2 * ((2:ℝ)^s2.card * ((A:ℝ)/(d:ℝ)^3))
      = ((A:ℝ)/(d:ℝ)) * (2:ℝ)^s2.card := by
    have hdne : (d:ℝ) ≠ 0 := hd0.ne'
    field_simp
    try ring
  have hAd : (0:ℝ) ≤ (A:ℝ)/(d:ℝ) := by positivity
  have hR : (0:ℝ) ≤ ∏ i : Fin 3, ((k i).divisors.card : ℝ)^4 := by positivity
  have hB4 : (1 + Real.log N)^4 ≤ 16 * (Real.log X)^4 := by
    have hlogpos : (0:ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h
        simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    have h3 := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1 + Real.log N) hlogN 4
    have h4 : (2 * Real.log X)^4 = 16 * (Real.log X)^4 := by ring
    linarith
  have hpow4 : (Real.log X)^4 ≤ (Real.log X)^11 := by
    have := pow_le_pow_right₀ (a := Real.log X) hL (by norm_num : 4 ≤ 11)
    simpa using this
  have hkey : (2:ℝ)^s2.card * ((3:ℝ)^s3.card * ((1 + Real.log N)^4 * Real.exp 4))
      ≤ 1600 * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^4 := by
    have h1 : (2:ℝ)^s2.card * (3:ℝ)^s3.card
        ≤ ∏ i : Fin 3, ((k i).divisors.card : ℝ)^4 :=
      pow_card_mul_le_divisor_prod k hk s2 s3 h2 h3
    have hL4 : (1 + Real.log N)^4 * Real.exp 4 ≤ (16 * (Real.log X)^4) * 100 :=
      mul_le_mul hB4 he4 (by positivity) (by positivity)
    have step1 : (2:ℝ)^s2.card * ((3:ℝ)^s3.card * ((1 + Real.log N)^4 * Real.exp 4))
        = ((2:ℝ)^s2.card * (3:ℝ)^s3.card) * ((1 + Real.log N)^4 * Real.exp 4) := by ring
    have step2 : ((2:ℝ)^s2.card * (3:ℝ)^s3.card) * ((1 + Real.log N)^4 * Real.exp 4)
        ≤ (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * ((16 * (Real.log X)^4) * 100) :=
      mul_le_mul h1 hL4 (by positivity) (by positivity)
    have step3 : (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * ((16 * (Real.log X)^4) * 100)
        = 1600 * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^4 := by ring
    linarith [step2, step3]
  have hkey2 : 1600 * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^4
      ≤ 10000 * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^11 := by
    have h5 : (0:ℝ) ≤ (Real.log X)^4 := by positivity
    have h6 : (0:ℝ) ≤ (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^4 := by
      positivity
    nlinarith [hR, hpow4, h5, h6]
  have hh := mul_le_mul_of_nonneg_left (hkey.trans hkey2) hAd
  calc ((d:ℝ)^2 * ((2:ℝ)^s2.card * ((A:ℝ)/(d:ℝ)^3)))
        * ((3:ℝ)^s3.card * ((1 + Real.log N)^4 * Real.exp 4))
      = ((A:ℝ)/(d:ℝ)) * ((2:ℝ)^s2.card * ((3:ℝ)^s3.card * ((1 + Real.log N)^4 * Real.exp 4))) := by
        rw [hA2]; ring
    _ ≤ ((A:ℝ)/(d:ℝ)) * (10000 * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^11) := hh
    _ = 10000 * ((A:ℝ)/(d:ℝ)) * (∏ i : Fin 3, ((k i).divisors.card : ℝ)^4) * (Real.log X)^11 := by
        ring


private theorem local_product_bound_proof :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k l : Fin 3 → ℕ) (N : ℕ) (X : ℝ),
      (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) → Odd N →
      (N : ℝ) ≤ X → (∀ i, (k i : ℝ) ≤ X) → 1 ≤ Real.log X →
      ∀ Q : ℕ, primeProduct k l N Q ≤ C * rawWeight k * Real.log X ^ 11 := by
  refine ⟨10000, by (norm_num), ?_⟩
  intro k l N X hk hl hNodd hNX hkX hL Q
  set d : ℕ := Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2) with hd
  set A : ℕ := Nat.gcd (k 0) (k 1) * Nat.gcd (k 0) (k 2) * Nat.gcd (k 1) (k 2) with hA
  have hdvdA : d ∣ A := by
    rw [hd, hA]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _) _
  obtain ⟨mN, hmN⟩ := hNodd
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 1 + Real.log N ≤ 2 * Real.log X := by
    have h : Real.log N ≤ Real.log X := Real.log_le_log hNpos hNX
    linarith
  -- the five bounds
  have hb1 := prod_filter_dvd_le k l N Q d hk hl hd
  have hb2 := prod_pair_le k l N Q d A hk hl hd hA
  have hb3 := prod_filter_three_le k l N Q A hk hl hA
  have hb4 := prod_filter_four_le k l N Q A hk hl hA hN1
  have hb5 := prod_filter_exp_le k l N Q A hk hl hA
  have hs2 : ((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ d ∧ p ∣ A)
      ⊆ (k 0 * k 1 * k 2).primeFactors := by
    intro p hp
    obtain ⟨hpP, -, hpA⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hpm : p ∣ A := hpA
    rw [hA] at hpm
    have h0 : p ∣ (k 0 * k 1 * k 2 : ℕ) := by
      rcases hpprime.dvd_mul.mp hpm with hx | hx
      · rcases hpprime.dvd_mul.mp hx with hy | hy
        · exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left (hy.trans (Nat.gcd_dvd_left _ _)) (k 1)) (k 2)
        · exact dvd_mul_of_dvd_right (hy.trans (Nat.gcd_dvd_right _ _)) (k 0 * k 1)
      · exact dvd_mul_of_dvd_right (hx.trans (Nat.gcd_dvd_right _ _)) (k 0 * k 1)
    refine Nat.mem_primeFactors.mpr ⟨hpprime, h0, ?_⟩
    have h1 := hk 0
    have h2 := hk 1
    have h3 := hk 2
    positivity
  have hs3 : ((range (Q + 1)).filter Nat.Prime).filter
      (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2) ⊆ (k 0 * k 1 * k 2).primeFactors := by
    intro p hp
    obtain ⟨hpP, -, hpK⟩ := Finset.mem_filter.mp hp
    refine Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hpP).2, hpK, ?_⟩
    have h1 := hk 0
    have h2 := hk 1
    have h3 := hk 2
    positivity
  -- the split
  have hsplit := prod_filter_chain ((range (Q + 1)).filter Nat.Prime)
    (fun p => 1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖) d A
    (k 0 * k 1 * k 2) N hdvdA
  have hprod : primeProduct k l N Q
      = ∏ p ∈ (range (Q + 1)).filter Nat.Prime,
          (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖) := rfl
  rw [hprod, hsplit]
  -- combine the five bounds
  have hrest : (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ d ∧ p ∣ A),
        (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
      * ((∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2),
          (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
        * ((∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
              (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ p ∣ N),
            (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
          * (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
              (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ ¬ p ∣ N),
            (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))))
      ≤ ((2:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ d ∧ p ∣ A)).card * ((A:ℝ)/(d:ℝ)^3))
        * ((3:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2)).card
          * ((1 + Real.log N)^4 * Real.exp 4)) := by
    refine mul_le_mul hb2 ?_ (by positivity) (by positivity)
    refine mul_le_mul hb3 ?_ (by positivity) (by positivity)
    exact mul_le_mul hb4 hb5 (by positivity) (by positivity)
  have hcombine :
      (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter (fun p => p ∣ d),
          (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
        * ((∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ d ∧ p ∣ A),
            (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
          * ((∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
                (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2),
              (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
            * ((∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
                  (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ p ∣ N),
                (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖))
              * (∏ p ∈ ((range (Q + 1)).filter Nat.Prime).filter
                  (fun p => ¬ p ∣ A ∧ ¬ p ∣ k 0 * k 1 * k 2 ∧ ¬ p ∣ N),
                (1 + ∑ j ∈ Icc 1 Q, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖)))))
      ≤ (d:ℝ)^2 * (((2:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ d ∧ p ∣ A)).card * ((A:ℝ)/(d:ℝ)^3))
        * ((3:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2)).card
          * ((1 + Real.log N)^4 * Real.exp 4))) :=
    mul_le_mul hb1 hrest (by positivity) (by positivity)
  have hreassoc : (d:ℝ)^2 * (((2:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ d ∧ p ∣ A)).card * ((A:ℝ)/(d:ℝ)^3))
        * ((3:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2)).card
          * ((1 + Real.log N)^4 * Real.exp 4)))
      = ((d:ℝ)^2 * ((2:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ d ∧ p ∣ A)).card * ((A:ℝ)/(d:ℝ)^3)))
        * ((3:ℝ) ^ (((range (Q + 1)).filter Nat.Prime).filter
            (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2)).card
          * ((1 + Real.log N)^4 * Real.exp 4)) := by ring
  have hfin := (hcombine.trans (le_of_eq hreassoc)).trans
    (class_product_le_envelope k N X d A
      (((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ d ∧ p ∣ A))
      (((range (Q + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ A ∧ p ∣ k 0 * k 1 * k 2))
      hk hL hlogN hd hA hs2 hs3)
  refine hfin.trans (le_of_eq ?_)
  rw [rawWeight, gcdWeight, hA, hd]
  push_cast
  ring

end Decomp355aLocalProductBound

/-- Halupczok pages 14 to 18, the prime power cases and products A to D.
The auxiliary scale X bounds the fixed moduli and N. The result is uniform in Q.
Noncompatible residues have zero coefficients and satisfy the same upper bound. -/
theorem local_product_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k l : Fin 3 → ℕ) (N : ℕ) (X : ℝ),
      (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) → Odd N →
      (N : ℝ) ≤ X → (∀ i, (k i : ℝ) ≤ X) → 1 ≤ Real.log X →
      ∀ Q : ℕ, primeProduct k l N Q ≤ C * rawWeight k * Real.log X ^ 11 := by
  exact local_product_bound_proof

/-- Halupczok page 18, the arithmetic envelope is nonnegative. -/
theorem rawWeight_nonneg (k : Fin 3 → ℕ) : 0 ≤ rawWeight k := by
  unfold rawWeight gcdWeight
  positivity

/-- Halupczok page 18, positive moduli give a positive arithmetic denominator. -/
theorem phiProduct_pos (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) : 0 < phiProduct k := by
  apply prod_pos
  intro i _
  exact_mod_cast Nat.totient_pos.mpr (by have := hk i; omega)

/-- Halupczok page 11 and page 18, the first weighted coefficient is nonzero. -/
theorem weightedCoeff_one (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    weightedCoeff k l N 1 = 1 / phiProduct k := by
  simp [weightedCoeff, ssTerm_one hk hl]

/-- Halupczok page 18, every summable admissible coefficient moment is positive.
This implication has a summability premise and has clean axioms on its own. -/
theorem coefficientMass_pos_of_summable (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hs : Summable (fun q : ℕ => weightedCoeff k l N q)) : 0 < coefficientMass k l N := by
  have hp : 0 < weightedCoeff k l N 1 := by
    rw [weightedCoeff_one k l N hk hl]
    exact one_div_pos.mpr (phiProduct_pos k hk)
  exact hp.trans_le (hs.le_tsum 1 (fun q _ => weightedCoeff_nonneg k l N q))

/-- Halupczok page 18, remove the zero term before using positive partial moments. -/
theorem range_sum_le_positive (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    ∑ q ∈ range Q, f q ≤ ∑ q ∈ Icc 1 Q, f q := by
  have he : ∑ q ∈ Icc 1 Q, f q = ∑ q ∈ range (Q + 1), f q := by
    apply sum_subset
    · intro q hq
      exact mem_range.mpr (by have := mem_Icc.mp hq; omega)
    · intro q hq hn
      have hq0 : q = 0 := by
        have := mem_range.mp hq
        simp only [mem_Icc, not_and, not_le] at hn
        omega
      simpa [hq0] using h0
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun q _ _ => hf q)

/-- Halupczok page 18, bounded raw partial moments imply weighted convergence.
This generic transfer uses no unproved coefficient estimate. -/
theorem summable_of_raw_bound (k l : Fin 3 → ℕ) (N : ℕ) (C : ℝ)
    (hC : ∀ Q : ℕ, ∑ q ∈ Icc 1 Q, (q : ℝ) * ‖ssTerm k l N q‖ ≤ C) :
    Summable (fun q : ℕ => weightedCoeff k l N q) := by
  have hs : Summable (fun q : ℕ => (q : ℝ) * ‖ssTerm k l N q‖) := by
    apply summable_of_sum_range_le (fun q => mul_nonneg (Nat.cast_nonneg q) (norm_nonneg _))
    intro Q
    exact (range_sum_le_positive _ (by simp)
      (fun q => mul_nonneg (Nat.cast_nonneg q) (norm_nonneg _)) Q).trans (hC Q)
  exact hs.div_const _

/-- Exact supply for the sealed weighted coefficient convergence leaf.
Derived from local_product_bound only. -/
theorem weighted_coeff_summable (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) (hN : Odd N) :
    Summable (fun q : ℕ => weightedCoeff k l N q) := by
  obtain ⟨C, hC, hb⟩ := local_product_bound
  let X : ℝ := max (Real.exp 1) (max (N : ℝ) (∑ i : Fin 3, (k i : ℝ)))
  have hNX : (N : ℝ) ≤ X := (le_max_left _ _).trans (le_max_right _ _)
  have hkX : ∀ i, (k i : ℝ) ≤ X := by
    intro i
    exact (single_le_sum (fun j _ => Nat.cast_nonneg (k j)) (mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hX : 0 < X := (Real.exp_pos 1).trans_le (le_max_left _ _)
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX).mpr (le_max_left _ _)
  apply summable_of_raw_bound k l N (C * rawWeight k * Real.log X ^ 11)
  intro Q
  exact (finite_euler_domination k l N Q hk hl).trans (hb k l N X hk hl hN hNX hkX hL Q)

/-- Halupczok page 18, the same finite estimates control the actual infinite moment.
Derived from local_product_bound, with an explicit auxiliary scale. -/
theorem coefficientMass_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k l : Fin 3 → ℕ) (N : ℕ) (X : ℝ),
      (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) → Odd N →
      (N : ℝ) ≤ X → (∀ i, (k i : ℝ) ≤ X) → 1 ≤ Real.log X →
      coefficientMass k l N ≤ C * Real.log X ^ 11 * (rawWeight k / phiProduct k) := by
  obtain ⟨C, hC, hb⟩ := local_product_bound
  refine ⟨C, hC, fun k l N X hk hl hN hNX hkX hL => ?_⟩
  have hs := weighted_coeff_summable k l N hk hl hN
  unfold coefficientMass
  apply hs.tsum_le_of_sum_range_le
  intro Q
  calc
    _ ≤ (∑ q ∈ Icc 1 Q, (q : ℝ) * ‖ssTerm k l N q‖) / phiProduct k := by
      rw [sum_div]
      exact range_sum_le_positive (fun q => weightedCoeff k l N q)
        (by simp [weightedCoeff]) (weightedCoeff_nonneg k l N) Q
    _ ≤ (C * rawWeight k * Real.log X ^ 11) / phiProduct k :=
      div_le_div_of_nonneg_right
        ((finite_euler_domination k l N Q hk hl).trans (hb k l N X hk hl hN hNX hkX hL Q))
        (phiProduct_nonneg k)
    _ = _ := by ring

end LeanLab.Tolev2009.Decomp355a
