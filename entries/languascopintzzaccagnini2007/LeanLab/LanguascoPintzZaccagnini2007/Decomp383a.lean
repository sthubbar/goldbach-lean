module

public import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218
public import LeanLab.LanguascoPintzZaccagnini2007.PeriodCount131
public import LeanLab.LanguascoPintzZaccagnini2007.Decomp131b
public import LeanLab.LPZ2007.D4Limits
public import LeanLab.LanguascoPintzZaccagnini2007.Tail383

/-!
Supply for the sealed major_arcs_combine131 in DecompJ218.
Journal pages 777 to 779, displays 16 to 24 and 30.
Separate the divisor expansion, finite period averages, and uniform divisor tail.
The final assembly restores the weight N minus M without another open input.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Display 17 on journal page 777, restricted to the odd squarefree d below D.
M is the upper exponent cutoff. No singular series or weight N occurs here. -/
def divisorBlock383 (k M N D : ℕ) : ℝ :=
  ∑ d ∈ (range D).filter OddSqf, fd d * (residueTupleCount131 d k M N : ℝ)

/-- Journal page 772 display 2. For positive even n, the Euler product
is the twin prime constant times the finite factor H of n. -/
theorem singular_factorization383 {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    Sing n = 2 * LeanLab.ChenExplicit.twinC * H n := by
  classical
  have h2n : 2 ∣ n := even_iff_two_dvd.mp hn
  let g : {p : ℕ // p.Prime} → ℝ := fun p =>
    if p.1 = 2 then 1 else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2
  have hg : Multipliable g := by
    let a : {p : ℕ // p.Prime} → ℝ := fun p =>
      if p.1 = 2 then 0 else 1 / ((p.1 : ℝ) - 1) ^ 2
    have ha : Summable a := Summable.of_nonneg_of_le
      (fun p => by dsimp [a]; split_ifs <;> positivity)
      (fun p => by
        dsimp [a]
        split_ifs
        · positivity
        · exact le_rfl)
      (LeanLab.ChenExplicit.summable_inv_sub_one_sq.subtype Nat.Prime)
    exact (Real.multipliable_one_add_of_summable ha.neg).congr fun p => by
      dsimp [g, a]; split_ifs <;> ring
  have hgt : (∏' p, g p) = LeanLab.ChenExplicit.twinC := by
    let e : {p : ℕ // p.Prime ∧ 2 < p} → {p : ℕ // p.Prime} :=
      fun p => ⟨p.1, p.2.1⟩
    have he : Function.Injective e := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg (fun r : {p : ℕ // p.Prime} => r.1) hpq
    have hsupport : Function.mulSupport g ⊆ Set.range e := by
      intro p hp
      have hp2 : p.1 ≠ 2 := by intro h; exact hp (by simp [g, h])
      have hlarge : 2 < p.1 := by have := p.2.two_le; omega
      exact ⟨⟨p.1, p.2, hlarge⟩, rfl⟩
    rw [← he.tprod_eq hsupport]
    unfold LeanLab.ChenExplicit.twinC
    apply tprod_congr
    intro p
    dsimp [g, e]
    rw [ite_eq_right (by have := p.2.2; omega)]
  let f : ℕ → ℝ := fun p => if p ∣ n then
    (if p = 2 then 2 else 1 + 1 / ((p : ℝ) - 2)) else 1
  let emb : {p // p ∈ n.primeFactors} ↪ {p : ℕ // p.Prime} :=
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
      fun p q hpq => by
        apply Subtype.ext
        exact congrArg (fun r : {p : ℕ // p.Prime} => r.1) hpq⟩
  let S := n.primeFactors.attach.map emb
  have hf : HasProd (fun p : {p : ℕ // p.Prime} => f p.1) (∏ p ∈ S, f p.1) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    dsimp [f]
    rw [ite_eq_right]
    intro hd
    apply hp
    exact mem_map.mpr ⟨⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hd, h0⟩⟩,
      mem_attach _ _, rfl⟩
  have hlocal : ∀ p : {p : ℕ // p.Prime}, singF n p = g p * f p.1 := by
    intro p
    dsimp [singF, g, f]
    by_cases hd : p.1 ∣ n
    · rw [ite_eq_left hd, ite_eq_left hd]
      by_cases hp2 : p.1 = 2
      · norm_num [hp2]
      · rw [ite_eq_right hp2, ite_eq_right hp2]
        have hp3 : (3 : ℝ) ≤ p.1 := by have := p.2.two_le; exact_mod_cast (by omega : 3 ≤ p.1)
        have ha : (p.1 : ℝ) - 1 ≠ 0 := by linarith
        have hb : (p.1 : ℝ) - 2 ≠ 0 := by linarith
        field_simp
        ring
    · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right (by intro h; exact hd (h ▸ h2n)), mul_one]
  have hfin : (∏ p ∈ S, f p.1) = 2 * H n := by
    change (∏ p ∈ n.primeFactors.attach.map emb, f p.1) = _
    rw [prod_map]
    change (∏ p ∈ n.primeFactors.attach, f p.1) = _
    rw [prod_attach]
    rw [← prod_filter_mul_prod_filter_not n.primeFactors (fun p => 2 < p)]
    have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, h0⟩
    have hnot : n.primeFactors.filter (fun p => ¬ 2 < p) = {2} := by
      ext p
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hp, hlt⟩; have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
      · rintro rfl; exact ⟨h2mem, by omega⟩
    rw [hnot, prod_singleton, mul_comm]
    have hf2 : f 2 = 2 := by simp [f, h2n]
    rw [hf2]
    congr 1
    apply prod_congr rfl
    intro p hp
    simp only [mem_filter] at hp
    simp [f, Nat.dvd_of_mem_primeFactors hp.1, show p ≠ 2 by omega]
  change (∏' p, singF n p) = _
  rw [tprod_congr hlocal, hg.tprod_mul hf.multipliable, hgt, hf.tprod_eq, hfin]
  ring

/-- LEAF. Journal page 772 display 2 and page 778 proof of Lemma 6.2.
The Euler product equals the sum over odd squarefree divisors for positive even n.
The factor 2c0 is retained. This is independent of all exponent averages. -/
theorem singular_divisors383 {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    Sing n = 2 * LeanLab.ChenExplicit.twinC *
      ∑ d ∈ n.divisors.filter OddSqf, fd d := by
  classical
  rw [singular_factorization383 hn h0]
  congr 1
  unfold H
  rw [prod_one_add]
  symm
  refine sum_nbij' (fun d => d.primeFactors) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    rw [mem_powerset]
    intro p hp
    refine mem_filter.mpr ⟨Nat.primeFactors_mono hd.1.1 h0 hp, ?_⟩
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hd.2.2.1) (even_iff_two_dvd.mpr hpd)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  · intro T hT
    rw [mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime ∧ 2 < p := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp (hT hp)).1, (mem_filter.mp (hT hp)).2⟩
    obtain ⟨hsq, _, _⟩ := set_facts hTp
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨prod_dvd_of_subset h0 hT, h0⟩, hsq⟩
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (mem_filter.mp hd).2.2.2
  · intro T hT
    rw [mem_powerset] at hT
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp (hT hp)).1
  · intro d hd
    exact fd_eq (mem_filter.mp hd).2

/-- Journal page 777 display 20. A residue independent normalized error envelope
for a single modulus. The period endpoints come from block_jcount_bounds131. -/
def periodEnvelope383 (k d : ℕ) (L : ℝ) : ℝ :=
  fd d * (xi d : ℝ) ^ (k - 1) *
    (|(((⌊L - √L⌋₊ / xi d : ℕ) : ℝ) / L) ^ k - (1 / (xi d : ℝ)) ^ k| +
     |((((⌊L - √L⌋₊ / xi d : ℕ) : ℝ) + 1) / L) ^ k - (1 / (xi d : ℝ)) ^ k|)

/-- Journal page 777 displays 20 and 21. For fixed odd d the period error tends to zero. -/
theorem periodEnvelope_tendsto383 {d : ℕ} (hd : Odd d) (k : ℕ) :
    Tendsto (periodEnvelope383 k d) atTop (𝓝 0) := by
  unfold periodEnvelope383
  simpa only [mul_zero] using
    (D4Limits.period_error_tendsto (xi d) k (xi_spec hd).1).const_mul
      (fd d * (xi d : ℝ) ^ (k - 1))

/-- Journal page 777 displays 19 to 21. The normalized count error is bounded
independently of the target residue N. -/
theorem normalized_block_error383 {d k X : ℕ} (hd : OddSqf d) (hk : 1 ≤ k)
    (hL : 0 < Lg X) (N : ℕ) :
    |fd d * (residueTupleCount131 d k ⌊Lg X - √(Lg X)⌋₊ N : ℝ) / Lg X ^ k -
      Ckterm k N d| ≤ periodEnvelope383 k d (Lg X) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hQ : 0 < Lg X ^ (j + 1) := pow_pos hL _
  obtain ⟨hlo, hhi⟩ := block_jcount_bounds131 hd.2.1 j ⌊Lg X - √(Lg X)⌋₊ N
  have hlo' : (((⌊Lg X - √(Lg X)⌋₊ / xi d : ℕ) : ℝ) / Lg X) ^ (j + 1) *
      jcount d j N ≤ (residueTupleCount131 d (j + 1) ⌊Lg X - √(Lg X)⌋₊ N : ℝ) /
        Lg X ^ (j + 1) := by
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hQ]
    exact_mod_cast hlo
  have hhi' : (residueTupleCount131 d (j + 1) ⌊Lg X - √(Lg X)⌋₊ N : ℝ) /
      Lg X ^ (j + 1) ≤
      ((((⌊Lg X - √(Lg X)⌋₊ / xi d : ℕ) : ℝ) + 1) / Lg X) ^ (j + 1) * jcount d j N := by
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hQ]
    exact_mod_cast hhi
  have hb := D4Limits.between_mul_error (t := (1 / (xi d : ℝ)) ^ (j + 1))
    (J := (xi d : ℝ) ^ j) (Nat.cast_nonneg (jcount d j N))
    (by exact_mod_cast jcount_le hd.2.1 j N) hlo' hhi'
  have he : fd d * (residueTupleCount131 d (j + 1) ⌊Lg X - √(Lg X)⌋₊ N : ℝ) /
        Lg X ^ (j + 1) - Ckterm (j + 1) N d =
      fd d * ((residueTupleCount131 d (j + 1) ⌊Lg X - √(Lg X)⌋₊ N : ℝ) /
        Lg X ^ (j + 1) - (1 / (xi d : ℝ)) ^ (j + 1) * jcount d j N) := by
    simp only [Ckterm, ite_eq_left hd, Nat.add_sub_cancel, one_div_pow]
    ring
  rw [he, abs_mul, abs_of_nonneg (fd_nonneg hd)]
  have := mul_le_mul_of_nonneg_left hb (fd_nonneg hd)
  simpa [periodEnvelope383, mul_assoc] using this

/-- LEAF. Journal page 777 displays 18 to 21 and 24.
For a fixed finite divisor cutoff, period counting and L' divided by L tending to one
approximate the finite coefficient sum uniformly in N. No large divisors occur. -/
theorem divisor_finite_average383 (k : ℕ) (hk : 1 ≤ k) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N D -
        partialC131 D k N * Lg X ^ k| ≤ ε * Lg X ^ k := by
  classical
  let E : ℝ → ℝ := fun L => ∑ d ∈ (range D).filter OddSqf, periodEnvelope383 k d L
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := tendsto_finsetSum ((range D).filter OddSqf)
      (fun d hd => periodEnvelope_tendsto383 (mem_filter.mp hd).2.2.1 k)
    simpa [E] using h
  have hLg : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀, hX₀⟩ := ((tendsto_order.1 (hE.comp hLg)).2 ε hε).exists_forall_of_atTop
  refine ⟨max X₀ 2, fun X hX N _ => ?_⟩
  have hL : 0 < Lg X := Real.logb_pos (by norm_num)
    (by exact_mod_cast (by omega : 1 < X))
  have hQ : 0 < Lg X ^ k := pow_pos hL _
  have hp : partialC131 D k N = ∑ d ∈ (range D).filter OddSqf, Ckterm k N d := by
    unfold partialC131
    symm
    exact sum_subset (filter_subset _ _) fun d hd hdn => by
      have hnot : ¬ OddSqf d := fun h => hdn (mem_filter.mpr ⟨hd, h⟩)
      simp [Ckterm, hnot]
  have hb : |divisorBlock383 k ⌊Lg X - √(Lg X)⌋₊ N D / Lg X ^ k -
      partialC131 D k N| ≤ ε := by
    rw [divisorBlock383, sum_div, hp, ← sum_sub_distrib]
    calc |∑ d ∈ (range D).filter OddSqf,
          (fd d * (residueTupleCount131 d k ⌊Lg X - √(Lg X)⌋₊ N : ℝ) / Lg X ^ k -
            Ckterm k N d)|
        ≤ ∑ d ∈ (range D).filter OddSqf,
          |fd d * (residueTupleCount131 d k ⌊Lg X - √(Lg X)⌋₊ N : ℝ) / Lg X ^ k -
            Ckterm k N d| := abs_sum_le_sum_abs _ _
      _ ≤ E (Lg X) := sum_le_sum fun d hd => normalized_block_error383 (mem_filter.mp hd).2 hk hL N
      _ ≤ ε := (hX₀ X (by omega)).le
  have he : divisorBlock383 k ⌊Lg X - √(Lg X)⌋₊ N D - partialC131 D k N * Lg X ^ k =
      (divisorBlock383 k ⌊Lg X - √(Lg X)⌋₊ N D / Lg X ^ k - partialC131 D k N) *
        Lg X ^ k := by field_simp
  rw [he, abs_mul, abs_of_pos hQ]
  exact mul_le_mul_of_nonneg_right hb hQ.le

/-- Display 17 on journal page 777. With no shift exceeding N, the signed
modular count agrees with natural divisibility of the remaining argument. -/
theorem residueTupleCount_nat383 (d k M N : ℕ)
    (hle : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N) :
    residueTupleCount131 d k M N =
      ((exponentTuples131 k M).filter (fun ν => d ∣ N - tuplePower131 ν)).card := by
  classical
  unfold residueTupleCount131
  congr 1
  apply filter_congr
  intro ν hν
  have he : (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i = ((N - tuplePower131 ν : ℕ) : ℤ) := by
    rw [Nat.cast_sub (hle ν hν)]
    simp [tuplePower131]
  rw [he]
  exact Int.natCast_dvd_natCast

/-- LEAF. Journal page 777 displays 20 and 22, using pages 778 and 779 displays 28 to 30.
The part of the divisor count above D is uniformly small after first choosing D large
and then X large. The quantifier over every D above D0 lets the coefficient tail use
the same cutoff. There is no main term or singular series in this bound. -/
theorem divisor_tail_average383 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      0 ≤ divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) -
        divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N D ∧
      divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) -
        divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N D ≤ ε * Lg X ^ k := by
  classical
  obtain ⟨D₀, hD₀⟩ := Tail383.uniform_count_tail k hk ε hε
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨X₀, hX₀⟩ := hD₀ D hD
  obtain ⟨X₁, hX₁⟩ := tuple_window131 k
  refine ⟨max X₀ (max X₁ (3 * D)), fun X hX N hN => ?_⟩
  have h3D : 3 * D ≤ X := by omega
  obtain ⟨_, _, _, hNJ⟩ := evenJ_nat131 hN
  have hDN : D ≤ N + 1 := by omega
  obtain ⟨_, hw⟩ := hX₁ X (by omega)
  have hle : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N := by
    intro ν hν
    have hp := tuplePower_le131 hν
    have h6 : 6 * tuplePower131 ν ≤ X := by
      calc 6 * tuplePower131 ν ≤ 6 * (k * 2 ^ ⌊Lg X - √(Lg X)⌋₊) := Nat.mul_le_mul_left _ hp
        _ = 6 * k * 2 ^ ⌊Lg X - √(Lg X)⌋₊ := by ring
        _ ≤ X := hw
    omega
  have he : divisorBlock383 k ⌊Lg X - √(Lg X)⌋₊ N (N + 1) -
      divisorBlock383 k ⌊Lg X - √(Lg X)⌋₊ N D =
      ∑ d ∈ (Ico D (N + 1)).filter OddSqf,
        fd d * (residueTupleCount131 d k ⌊Lg X - √(Lg X)⌋₊ N : ℝ) := by
    simp only [divisorBlock383, sum_filter]
    exact (sum_Ico_eq_sub _ hDN).symm
  rw [he]
  constructor
  · exact sum_nonneg fun d hd => mul_nonneg (fd_nonneg (mem_filter.mp hd).2) (Nat.cast_nonneg _)
  · have htail := hX₀ X (by omega) N hN
    convert htail using 1
    apply sum_congr rfl
    intro d _
    rw [residueTupleCount_nat383 d k _ N hle]

/-- Journal page 777, display 16 to 17. The unweighted singular series sum is
exactly 2c0 times the full divisor block when all remaining arguments are positive. -/
theorem singular_tuple_divisor383
    (hsing : ∀ n : ℕ, Even n → n ≠ 0 →
      Sing n = 2 * LeanLab.ChenExplicit.twinC * ∑ d ∈ n.divisors.filter OddSqf, fd d)
    (k X N : ℕ) (hN : Even N)
    (hlt : ∀ ν ∈ tuples131 k X, tuplePower131 ν < N) :
    (∑ ν ∈ tuples131 k X, Sing (N - tuplePower131 ν)) =
      2 * LeanLab.ChenExplicit.twinC *
        divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) := by
  classical
  have hev : ∀ ν ∈ tuples131 k X, Even (N - tuplePower131 ν) := by
    intro ν hν
    exact (Nat.even_sub (hlt ν hν).le).mpr (iff_of_true hN (tuplePower_even131 hν))
  simp_rw [divisorBlock383, residueTupleCount_nat383 _ _ _ N (fun ν hν => (hlt ν hν).le)]
  rw [sum_congr rfl (fun ν hν => hsing _ (hev ν hν)
    (by have := hlt ν hν; omega)), ← mul_sum]
  congr 1
  have hdiv : ∀ ν ∈ tuples131 k X,
      (N - tuplePower131 ν).divisors.filter OddSqf =
        ((range (N + 1)).filter OddSqf).filter (fun d => d ∣ N - tuplePower131 ν) := by
    intro ν hν
    have hp := hlt ν hν
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_range]
    constructor
    · rintro ⟨⟨hd, _⟩, ho⟩
      have := Nat.le_of_dvd (by omega : 0 < N - tuplePower131 ν) hd
      exact ⟨⟨by omega, ho⟩, hd⟩
    · rintro ⟨⟨_, ho⟩, hd⟩
      exact ⟨⟨hd, by omega⟩, ho⟩
  rw [sum_congr rfl (fun ν hν => by rw [hdiv ν hν, sum_filter]), sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- Journal page 777 displays 20 to 24. The full divisor block has coefficient
C of k and N, assembled from the finite block and tail bounds. -/
theorem divisor_average_of_parts383
    (hfinite : ∀ k : ℕ, 1 ≤ k → ∀ D : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
        |divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N D -
          partialC131 D k N * Lg X ^ k| ≤ ε * Lg X ^ k)
    (htail : ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
        0 ≤ divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) -
          divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N D ∧
        divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) -
          divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N D ≤ ε * Lg X ^ k)
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) -
        Ck k N * Lg X ^ k| ≤ ε * Lg X ^ k := by
  obtain ⟨D₀, hD₀⟩ := htail k hk (ε / 3) (by positivity)
  obtain ⟨D₁, hD₁⟩ := ((tendsto_order.1 (tendsto_sum_nat_add seriesTerm)).2
    (ε / 3) (by positivity)).exists_forall_of_atTop
  let D := max D₀ D₁
  obtain ⟨X₁, hX₁⟩ := hfinite k hk D (ε / 3) (by positivity)
  obtain ⟨X₂, hX₂⟩ := hD₀ D (le_max_left _ _)
  obtain ⟨X₃, hX₃⟩ := tuple_window131 k
  refine ⟨max X₁ (max X₂ X₃), fun X hX N hN => ?_⟩
  have hL : 0 ≤ Lg X ^ k := pow_nonneg (by linarith [(hX₃ X (by omega)).1]) k
  have hf := hX₁ X (by omega) N hN
  obtain ⟨ht0, ht⟩ := hX₂ X (by omega) N hN
  obtain ⟨hc0, hc⟩ := coefficient_tail131 hk D N
  have hcs : Ck k N - partialC131 D k N ≤ ε / 3 :=
    hc.trans (hD₁ D (le_max_right _ _)).le
  have he := mul_le_mul_of_nonneg_right hcs hL
  have he0 := mul_nonneg hc0 hL
  apply abs_le.mpr
  obtain ⟨hflo, hfhi⟩ := abs_le.mp hf
  constructor <;> nlinarith

/-- Pages 773 and 777, displays 3 and 16. Every tuple shift is at most δ N
uniformly on J of X once X is large. This uses the proved tuple_window131. -/
theorem tuple_shift_small383 (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      ∀ ν ∈ tuples131 k X, (tuplePower131 ν : ℝ) ≤ δ * N := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmδ : 1 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hm
  obtain ⟨X₀, hX₀⟩ := tuple_window131 (m * k)
  refine ⟨X₀, fun X hX N hN ν hν => ?_⟩
  have hw := (hX₀ X hX).2
  have hp := tuplePower_le131 hν
  have hNnat := (evenJ_nat131 hN).2.2.2
  have hmul : 6 * m * tuplePower131 ν ≤ X := by
    calc 6 * m * tuplePower131 ν ≤ 6 * m * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) :=
        Nat.mul_le_mul_left _ hp
      _ = 6 * (m * k) * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
      _ ≤ X := hw
  have hmulr : 6 * (m : ℝ) * tuplePower131 ν ≤ X := by exact_mod_cast hmul
  have hNr : 2 * (X : ℝ) ≤ 3 * N := by exact_mod_cast hNnat
  have hstep : 4 * (m : ℝ) * tuplePower131 ν ≤ N := by linarith
  have hnonneg : 0 ≤ (tuplePower131 ν : ℝ) := Nat.cast_nonneg _
  have hδstep := mul_le_mul_of_nonneg_left hstep hδ.le
  have hstrong := mul_le_mul_of_nonneg_right hmδ.le hnonneg
  nlinarith

/-- Journal page 777 display 16. A uniform unweighted singular average implies
its weighted version because every shift is o of N. No cited input is used. -/
theorem weighted_of_unweighted383
    (havg : ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
        |(∑ ν ∈ tuples131 k X, Sing (N - tuplePower131 ν)) -
          coefficient131 k N * Lg X ^ k| ≤ ε * Lg X ^ k) :
    SingularAverageStatement131 := by
  intro k hk ε hε
  let B := 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
    (tsum_nonneg seriesTerm_nonneg)
  have hB1 : 0 < B + 1 := by linarith
  let η := min (ε / 2) 1
  have hη : 0 < η := lt_min (by positivity) one_pos
  obtain ⟨X₁, hX₁⟩ := havg k hk η hη
  obtain ⟨X₂, hX₂⟩ := tuple_shift_small383 k (ε / (2 * (B + 1))) (by positivity)
  obtain ⟨X₃, hX₃⟩ := tuple_window131 k
  refine ⟨max X₁ (max X₂ X₃), fun X hX N hN => ?_⟩
  obtain ⟨hL1, hw⟩ := hX₃ X (by omega)
  have hL : 0 ≤ Lg X ^ k := pow_nonneg (by linarith) _
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  obtain ⟨hN1, _, _, hNJ⟩ := evenJ_nat131 hN
  have hle : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N := by
    intro ν hν
    have hp := tuplePower_le131 hν
    have h6 : 6 * tuplePower131 ν ≤ X := by
      calc 6 * tuplePower131 ν ≤ 6 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) :=
          Nat.mul_le_mul_left _ hp
        _ = 6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
        _ ≤ X := hw
    omega
  let S := ∑ ν ∈ tuples131 k X, Sing (N - tuplePower131 ν)
  let E := ∑ ν ∈ tuples131 k X, (tuplePower131 ν : ℝ) * Sing (N - tuplePower131 ν)
  have hE0 : 0 ≤ E := sum_nonneg fun ν _ =>
    mul_nonneg (Nat.cast_nonneg _) (Sing_nonneg131 _)
  have hEle : E ≤ (ε / (2 * (B + 1))) * N * S := by
    dsimp [E, S]
    rw [mul_sum]
    exact sum_le_sum fun ν hν => mul_le_mul_of_nonneg_right
      (hX₂ X (by omega) N hN ν hν) (Sing_nonneg131 _)
  have hmain := hX₁ X (by omega) N hN
  have hc : coefficient131 k N ≤ B := coefficient_le131 hk N
  have hSup : S ≤ (B + 1) * Lg X ^ k := by
    have h1 := (abs_le.mp hmain).2
    have h2 := mul_le_mul_of_nonneg_right hc hL
    have h3 := mul_le_mul_of_nonneg_right (min_le_right (ε / 2) 1) hL
    dsimp [S, η] at *
    nlinarith
  have hEbound : E ≤ ε / 2 * ((N : ℝ) * Lg X ^ k) := by
    calc E ≤ ε / (2 * (B + 1)) * N * S := hEle
      _ ≤ ε / (2 * (B + 1)) * N * ((B + 1) * Lg X ^ k) :=
        mul_le_mul_of_nonneg_left hSup (by positivity)
      _ = ε / 2 * ((N : ℝ) * Lg X ^ k) := by field_simp
  have hErr : |S - coefficient131 k N * Lg X ^ k| ≤ ε / 2 * Lg X ^ k :=
    hmain.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
  have hErrN := mul_le_mul_of_nonneg_left hErr hN0
  have hW : (∑ ν ∈ tuples131 k X,
      ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)) = N * S - E := by
    dsimp [S, E]
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun ν hν => by rw [Nat.cast_sub (hle ν hν)]; ring
  rw [hW]
  have he : (N : ℝ) * S - E - coefficient131 k N * N * Lg X ^ k =
      N * (S - coefficient131 k N * Lg X ^ k) - E := by ring
  rw [he]
  calc |(N : ℝ) * (S - coefficient131 k N * Lg X ^ k) - E|
      ≤ |(N : ℝ) * (S - coefficient131 k N * Lg X ^ k)| + |E| := abs_sub _ _
    _ = (N : ℝ) * |S - coefficient131 k N * Lg X ^ k| + E := by
      rw [abs_mul, abs_of_nonneg hN0, abs_of_nonneg hE0]
    _ ≤ ε * N * Lg X ^ k := by nlinarith

/-- Journal page 777 displays 16 to 24. The exact divisor identity and the
finite and tail averages give the unweighted singular average. -/
theorem singular_unweighted_supply383 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |(∑ ν ∈ tuples131 k X, Sing (N - tuplePower131 ν)) -
        coefficient131 k N * Lg X ^ k| ≤ ε * Lg X ^ k := by
  let c := 2 * LeanLab.ChenExplicit.twinC
  have hc : 0 < c := mul_pos (by norm_num) LeanLab.ChenExplicit.twinC_pos
  obtain ⟨X₁, hX₁⟩ := divisor_average_of_parts383
    divisor_finite_average383 divisor_tail_average383 k hk (ε / c) (div_pos hε hc)
  obtain ⟨X₂, hX₂⟩ := tuple_window131 k
  refine ⟨max X₁ X₂, fun X hX N hN => ?_⟩
  obtain ⟨_, hw⟩ := hX₂ X (by omega)
  obtain ⟨hN1, _, hNe, hNJ⟩ := evenJ_nat131 hN
  have hlt : ∀ ν ∈ tuples131 k X, tuplePower131 ν < N := by
    intro ν hν
    have hp := tuplePower_le131 hν
    have h6 : 6 * tuplePower131 ν ≤ X := by
      calc 6 * tuplePower131 ν ≤ 6 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) :=
          Nat.mul_le_mul_left _ hp
        _ = 6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
        _ ≤ X := hw
    omega
  rw [singular_tuple_divisor383 (fun n hn h0 => singular_divisors383 hn h0) k X N hNe hlt]
  change |c * divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) -
    c * Ck k N * Lg X ^ k| ≤ ε * Lg X ^ k
  rw [mul_assoc c, ← mul_sub, abs_mul, abs_of_pos hc]
  calc c * |divisorBlock383 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N (N + 1) - Ck k N * Lg X ^ k|
      ≤ c * (ε / c * Lg X ^ k) := mul_le_mul_of_nonneg_left (hX₁ X (by omega) N hN) hc.le
    _ = ε * Lg X ^ k := by field_simp

/-- The exact sealed statement of major_arcs_combine131, supplied from the three
strictly smaller leaves above. No open proof of its own. DecompJ218 stays unchanged. -/
theorem major_arcs_combine_supply383 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ tuples131 k X,
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) -
        coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k :=
  weighted_of_unweighted383 singular_unweighted_supply383 k hk ε hε

end

end LeanLab.LPZ2007

