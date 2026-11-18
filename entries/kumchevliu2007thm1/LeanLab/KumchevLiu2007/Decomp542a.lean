module

public import LeanLab.KumchevLiu2007.MaximalBV634

/-!
Maximal prime distribution and the weighted transfer on page 17.
Source https://arxiv.org/abs/0801.0130 between displays 57 and 58.
The shared definitions and elementary estimates are in PrimeError634Base.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task542a

open Real Task506b
open scoped BigOperators Topology

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 28.
Maximal Bombieri Vinogradov for prime counting, used on page 17 between
57 and 58 of Kumchev and Liu. The maximum is over every real endpoint
between 2 and T and every reduced residue class. CITED analytic input. -/
theorem maximal_bombieri_vinogradov (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ Finset.Icc 1 D, primeError T d) ≤
          C * T * Real.log T ^ (-A) := by
  exact Task506b.maximal_bv_pi A hA


/-- Page 17, maximal Bombieri Vinogradov with the divisor weight inserted.
CONDITIONAL ON maximal_bombieri_vinogradov. -/
theorem weighted_maximal_bombieri_vinogradov (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (d.divisors.card : ℝ) * primeError T d) ≤ C * T * Real.log T ^ (-A) := by
  obtain ⟨b, C, T0, hb, hC, hT0, hBV⟩ :=
    maximal_bombieri_vinogradov (2 * A + 6) (by linarith)
  refine ⟨b, Real.sqrt (Real.exp 48 * (2 + 2 * Real.exp 24) * C),
    max T0 (Real.exp 1), hb, Real.sqrt_pos.mpr (by positivity),
    hT0.trans (le_max_left _ _), ?_⟩
  intro T hT D hD
  have hTbase : T0 ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := hT0.trans hTbase
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hL : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hTe
    simpa only [Real.log_exp] using h
  have hlpow : Real.log T ^ (-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hroot : Real.sqrt T ≤ T := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ T)
    nlinarith [Real.sqrt_nonneg T]
  have hDT : (D : ℝ) ≤ T := hD.trans ((mul_le_of_le_one_right
    (Real.sqrt_nonneg T) hlpow).trans hroot)
  apply weighted_prime_errors_of_sum D T A C hT2 hL hDT hC.le
  simpa only [neg_add_rev, neg_mul, neg_neg, add_comm, sub_eq_add_neg] using hBV T hTbase D hD


/-- Page 17, the prime factor window permits the maximal BV level uniformly. -/
theorem prime_window_bv_parameters (b T0 B ε : ℝ) (hb : 0 < b)
    (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∀ᶠ X : ℝ in Filter.atTop, 0 < Real.log X ∧
      ∀ p ∈ primeWindow X B ε,
        T0 ≤ Real.sqrt (Y X ε) / p ∧
        1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
        Real.log X / 8 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
        Real.log (Real.sqrt (Y X ε) / p) ≤ Real.log X ∧
        Y X ε ^ (1 / 9 : ℝ) ≤
          Real.sqrt (Real.sqrt (Y X ε) / p) *
            Real.log (Real.sqrt (Y X ε) / p) ^ (-b) := by
  let θ : ℝ := 7 / 12 + ε / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have ht := (tendsto_rpow_atTop (show 0 < θ / 4 by positivity)).eventually
    (Filter.eventually_ge_atTop T0)
  filter_upwards [Task506c.sieve_level_margin b ε hε,
    prime_window_parameters B ε hB hε,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (8 : ℝ)),
    ht, Filter.eventually_gt_atTop (1 : ℝ)] with X hmargin hparams hL8 hT0 hX
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := by linarith
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hU : 0 < Y X ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hY _
  have hUeq : Y X ε ^ (1 / 4 : ℝ) = X ^ (θ / 4) := by
    unfold Y
    rw [← Real.rpow_mul hXp.le]
    congr 1
    dsimp [θ]
    ring
  have hU2 : (Y X ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Y X ε) := by
    rw [← Real.rpow_mul_natCast hY.le, Real.sqrt_eq_rpow]
    norm_num
  refine ⟨hL, ?_⟩
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpU := (Finset.mem_filter.mp hp).2.2.2
  have hTlow : Y X ε ^ (1 / 4 : ℝ) ≤ Real.sqrt (Y X ε) / p := by
    apply (le_div_iff₀ hp0).mpr
    rw [← hU2]
    nlinarith
  have hpLog : Real.log p ≤ θ / 4 * Real.log X := by
    have hh := Real.log_le_log hp0 hpU.le
    rw [Real.log_rpow hY, Y, Real.log_rpow hXp] at hh
    dsimp [θ]
    nlinarith
  have hpLog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
  have hlogT : Real.log (Real.sqrt (Y X ε) / p) = θ / 2 * Real.log X - Real.log p := by
    rw [Real.log_div (Real.sqrt_pos.mpr hY).ne' hp0.ne', Real.sqrt_eq_rpow,
      Real.log_rpow hY, Y, Real.log_rpow hXp]
    dsimp [θ]
    ring
  have hloglo : Real.log X / 8 ≤ Real.log (Real.sqrt (Y X ε) / p) := by
    rw [hlogT]
    dsimp [θ] at *
    nlinarith [mul_nonneg hε.le hL.le]
  have hloghi : Real.log (Real.sqrt (Y X ε) / p) ≤ Real.log X := by
    rw [hlogT]
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    nlinarith
  have hlog1 : 1 ≤ Real.log (Real.sqrt (Y X ε) / p) := by linarith
  have hroot : Y X ε ^ (1 / 8 : ℝ) ≤ Real.sqrt (Real.sqrt (Y X ε) / p) := by
    have hh := Real.sqrt_le_sqrt hTlow
    have heq : Real.sqrt (Y X ε ^ (1 / 4 : ℝ)) = Y X ε ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hY.le]
      norm_num
    rwa [heq] at hh
  refine ⟨(hT0.trans_eq hUeq.symm).trans hTlow, hlog1, hloglo, hloghi, ?_⟩
  apply hmargin.trans
  apply mul_le_mul hroot
    (Real.rpow_le_rpow_of_nonpos (by linarith) hloghi (by linarith))
    (by positivity) (Real.sqrt_nonneg _)


/-- Page 17, summing the divisor weighted prime errors over the smaller prime.
CONDITIONAL ON maximal_bombieri_vinogradov. -/
theorem prime_window_weighted_bv (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in Filter.atTop,
      (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * primeError (Real.sqrt (Y X ε) / p) d) ≤
        K * errorScale X ε A := by
  obtain ⟨b, C, T0, hb, hC, hT0, hBV⟩ := weighted_maximal_bombieri_vinogradov A hA
  let R : ℝ := 32 * (2 * B + 18)
  refine ⟨C * (8 : ℝ) ^ A * R, by dsimp [R]; positivity, ?_⟩
  filter_upwards [prime_window_bv_parameters b T0 B ε hb hB hε hε1,
    prime_reciprocal_bound B ε hB hε,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop (1 : ℝ)]
    with X hparams hrec hL1 hX
  have hL : 0 < Real.log X := hparams.1
  have hrecR : (∑ p ∈ primeWindow X B ε, (1 : ℝ) / p) ≤ R := by
    apply hrec.2.2.trans
    have hlog := Real.log_le_sub_one_of_pos hL
    apply (div_le_iff₀ hL).mpr
    dsimp [R]
    have hR : (0 : ℝ) ≤ 32 * (2 * B + 18) := by positivity
    nlinarith
  have hpow : (Real.log X / 8) ^ (-A) = (8 : ℝ) ^ A * Real.log X ^ (-A) := by
    rw [Real.div_rpow hL.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      div_inv_eq_mul]
    ring
  have hlocal (p : ℕ) (hp : p ∈ primeWindow X B ε) :
      (∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
        (d.divisors.card : ℝ) * primeError (Real.sqrt (Y X ε) / p) d) ≤
      C * (Real.sqrt (Y X ε) / p) * ((8 : ℝ) ^ A * Real.log X ^ (-A)) := by
    obtain ⟨hT, hlog1, hloglo, hloghi, hlevel⟩ := hparams.2 p hp
    have hD : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤
        Real.sqrt (Real.sqrt (Y X ε) / p) * Real.log (Real.sqrt (Y X ε) / p) ^ (-b) :=
      (Nat.floor_le (Real.rpow_nonneg (by unfold Y; exact Real.rpow_nonneg (by linarith : 0 ≤ X) _) _)).trans hlevel
    apply (hBV _ hT _ hD).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← hpow]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hloglo (by linarith)
  calc
    _ ≤ ∑ p ∈ primeWindow X B ε,
        C * (Real.sqrt (Y X ε) / p) * ((8 : ℝ) ^ A * Real.log X ^ (-A)) :=
      Finset.sum_le_sum hlocal
    _ = (C * (8 : ℝ) ^ A * Real.sqrt (Y X ε) * Real.log X ^ (-A)) *
        ∑ p ∈ primeWindow X B ε, (1 : ℝ) / p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (C * (8 : ℝ) ^ A * Real.sqrt (Y X ε) * Real.log X ^ (-A)) * R :=
      mul_le_mul_of_nonneg_left hrecR (by positivity)
    _ = (C * (8 : ℝ) ^ A * R) * errorScale X ε A := by
      unfold errorScale
      rw [Real.sqrt_eq_rpow]
      ring


/-- Page 17, the full square root residue count as a numerical arithmetic function. -/
noncomputable def rootCount (n : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun d => ((Finset.range d).filter (fun x => x ^ 2 % d = n % d)).card, by simp⟩

/-- Page 17, CRT multiplicativity of the root residue count. -/
theorem rootCount_isMultiplicative (n : ℕ) : (rootCount n).IsMultiplicative := by
  refine ⟨by simp [rootCount, Nat.mod_one], ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a
    simp [rootCount]
  by_cases hb : b = 0
  · subst b
    simp [rootCount]
  exact Task506d.root_count_coprime_mul n a b (by omega) (by omega) hab


/-- Page 17, a squarefree reduced modulus has at most tau d square roots. -/
theorem squarefree_root_count_le_tau (n d : ℕ) (hd : Squarefree d)
    (hnd : Nat.Coprime n d) :
    ((Finset.range d).filter (fun x => x ^ 2 % d = n % d)).card ≤ d.divisors.card := by
  classical
  have heq := (rootCount_isMultiplicative n).prod_primeFactors hd
  change (∏ p ∈ d.primeFactors, (rootCount n) p) = (rootCount n) d at heq
  change (rootCount n) d ≤ d.divisors.card
  rw [← heq, Nat.card_divisors hd.ne_zero]
  apply Finset.prod_le_prod
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  rw [Nat.factorization_eq_one_of_squarefree hd hpp hpd]
  haveI : Fact p.Prime := ⟨hpp⟩
  have hnot : ¬ p ∣ n := hpp.coprime_iff_not_dvd.mp (hnd.of_dvd_right hpd).symm
  change ((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card ≤ 1 + 1
  rw [Task129s.root_count_range_eq p n hnot]
  exact Task129a.nonzero_square_roots_le_two p n


/-- Page 16, ordering the two prime factors removes product multiplicity. -/
theorem ordered_prime_products_injective (p r q s : ℕ)
    (hp : p.Prime) (hr : r.Prime) (hq : q.Prime) (hs : s.Prime)
    (hpr : p ≤ r) (hqs : q ≤ s) (heq : p * r = q * s) : p = q ∧ r = s := by
  have hdiv : p ∣ q * s := by rw [← heq]; exact dvd_mul_right p r
  rcases hp.dvd_mul.mp hdiv with h | h
  · have hpq := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    subst q
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos heq⟩
  · have hps := (Nat.prime_dvd_prime_iff_eq hp hs).mp h
    subst s
    have hrq : r = q := by nlinarith [hp.pos]
    subst q
    have h : p = r := Nat.le_antisymm hpr hqs
    exact ⟨h, h.symm⟩


/-- Page 16, the allowed larger prime factors for a fixed smaller prime. -/
noncomputable def factorPrimes (X ε : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1)).filter (fun r : ℕ =>
    r.Prime ∧ p ≤ r ∧ Real.sqrt (Y X ε) / 2 ≤ ((p * r : ℕ) : ℝ) ∧
      ((p * r : ℕ) : ℝ) < Real.sqrt (Y X ε))

/-- Page 17, the semiprime progression count is the exact sum over its smaller prime. -/
theorem progressionCount_factor_sum (X B ε : ℝ) (n d : ℕ) :
    progressionCount X B ε n d =
      ∑ p ∈ primeWindow X B ε,
        (((factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) := by
  classical
  let S := (primeWindow X B ε).sigma (fun p : ℕ =>
    (factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2))
  have hcard : S.card = ((semiprimes X B ε).filter (fun q => d ∣ n - q ^ 2)).card := by
    apply Finset.card_bij (fun v _ => v.1 * v.2)
    · intro v hv
      obtain ⟨hp, hr⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hrF, hdiv⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrange, hrp, hpr, hlo, hhi⟩ := Finset.mem_filter.mp hrF
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hlo, hhi,
        v.1, hp, v.2, hrp, hpr, rfl⟩, hdiv⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hhi.le))
    · intro v hv w hw heq
      obtain ⟨hp, hr⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hq, hs⟩ := Finset.mem_sigma.mp hw
      have hrf := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
      have hsf := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
      have hh := ordered_prime_products_injective v.1 v.2 w.1 w.2
        (Finset.mem_filter.mp hp).2.1 hrf.1 (Finset.mem_filter.mp hq).2.1 hsf.1
        hrf.2.1 hsf.2.1 heq
      exact Sigma.ext hh.1 (heq_of_eq hh.2)
    · intro q hq
      obtain ⟨hqsem, hdiv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqrange, hlo, hhi, p, hp, r, hr, hpr, heq⟩ := Finset.mem_filter.mp hqsem
      have hp1 := (Finset.mem_filter.mp hp).2.1.one_le
      have hrq : r ≤ q := by rw [heq]; nlinarith
      have hrange : r ∈ Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1) :=
        Finset.mem_range.mpr (hrq.trans_lt (Finset.mem_range.mp hqrange))
      refine ⟨⟨p, r⟩, Finset.mem_sigma.mpr ⟨hp, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hrange, hr, hpr, ?_, ?_⟩, ?_⟩⟩, heq.symm⟩
      · simpa only [← heq] using hlo
      · simpa only [← heq] using hhi
      · simpa only [← heq] using hdiv
  have hh := congrArg (fun k : ℕ => (k : ℝ)) hcard
  rw [Finset.card_sigma] at hh
  simpa only [Nat.cast_sum, progressionCount] using hh.symm


/-- Page 16, prime counting with a strict upper endpoint for J. -/
noncomputable def primeAPOpen (x : ℝ) (d a : ℕ) : ℝ :=
  ((((Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).filter
    (fun p : ℕ => (p : ℝ) < x)).card : ℝ)

/-- Page 17, changing the upper endpoint convention costs at most one prime. -/
theorem primeAP_open_endpoint (x : ℝ) (d a : ℕ) (hx : 0 ≤ x) :
    0 ≤ primeAP x d a - primeAPOpen x d a ∧
      primeAP x d a - primeAPOpen x d a ≤ 1 := by
  classical
  let S := (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)
  have hcard : (S.filter (fun p : ℕ => ¬ (p : ℝ) < x)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpS := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    have hqS := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have hplo : x ≤ p := le_of_not_gt (Finset.mem_filter.mp hp).2
    have hqlo : x ≤ q := le_of_not_gt (Finset.mem_filter.mp hq).2
    have hphi : (p : ℝ) ≤ x := (by exact_mod_cast hpS.2 : (p : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx)
    have hqhi : (q : ℝ) ≤ x := (by exact_mod_cast hqS.2 : (q : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx)
    exact_mod_cast (show (p : ℝ) = q by linarith)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun p : ℕ => (p : ℝ) < x)
  have hsplitR := congrArg (fun k : ℕ => (k : ℝ)) hsplit
  have hcardR : ((S.filter (fun p : ℕ => ¬ (p : ℝ) < x)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  have hnn : (0 : ℝ) ≤ (S.filter (fun p : ℕ => ¬ (p : ℝ) < x)).card := by positivity
  change 0 ≤ (S.card : ℝ) - ((S.filter (fun p : ℕ => (p : ℝ) < x)).card : ℝ) ∧
    (S.card : ℝ) - ((S.filter (fun p : ℕ => (p : ℝ) < x)).card : ℝ) ≤ 1
  push_cast at hsplitR
  constructor <;> linarith


/-- Page 17, the maximal closed endpoint error controls the strict endpoint count. -/
theorem primeAPOpen_error (T x : ℝ) (d a : ℕ)
    (hT : 2 ≤ T) (hL : 1 ≤ Real.log T) (hd : 0 < d) (hdT : (d : ℝ) ≤ T)
    (ha : a < d) (hcop : Nat.Coprime a d) (hx : 2 ≤ x) (hxT : x ≤ T) :
    |primeAPOpen x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d| ≤
      primeError T d + 1 := by
  have he := primeAP_open_endpoint x d a (by linarith)
  have hc := primeError_majorizes T x d a hT hL hd hdT ha hcop hx hxT
  have habs : |primeAPOpen x d a - primeAP x d a| ≤ 1 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  calc
    _ = |(primeAPOpen x d a - primeAP x d a) +
        (primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d)| := by congr 1; ring
    _ ≤ |primeAPOpen x d a - primeAP x d a| +
        |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d| := abs_add_le _ _
    _ ≤ primeError T d + 1 := by linarith


/-- Page 16, prime count in the half open interval J with a prescribed residue. -/
noncomputable def intervalAP (lo hi : ℝ) (d a : ℕ) : ℝ :=
  ((((Finset.Icc 1 ⌊hi⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).filter
    (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) < hi)).card : ℝ)

/-- Page 17, a half open prime count is the difference of strict prefix counts. -/
theorem intervalAP_eq_sub (lo hi : ℝ) (d a : ℕ) (hlohi : lo ≤ hi) :
    intervalAP lo hi d a = primeAPOpen hi d a - primeAPOpen lo d a := by
  classical
  let S := ((Finset.Icc 1 ⌊hi⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).filter
    (fun p : ℕ => (p : ℝ) < hi)
  have hleft : S.filter (fun p : ℕ => (p : ℝ) < lo) =
      ((Finset.Icc 1 ⌊lo⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).filter
        (fun p : ℕ => (p : ℝ) < lo) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpS, hplt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpI, hphi⟩ := Finset.mem_filter.mp hpS
      obtain ⟨hpR, hpp, hmod⟩ := Finset.mem_filter.mp hpI
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpR).1, Nat.le_floor hplt.le⟩, hpp, hmod⟩, hplt⟩
    · intro hp
      obtain ⟨hpI, hplt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpR, hpp, hmod⟩ := Finset.mem_filter.mp hpI
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpR).1,
          (Finset.mem_Icc.mp hpR).2.trans (Nat.floor_mono hlohi)⟩, hpp, hmod⟩,
        hplt.trans_le hlohi⟩, hplt⟩
  have hright : S.filter (fun p : ℕ => ¬ (p : ℝ) < lo) =
      ((Finset.Icc 1 ⌊hi⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).filter
        (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) < hi) := by
    ext p
    simp only [S, Finset.mem_filter, not_lt]
    tauto
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun p : ℕ => (p : ℝ) < lo)
  rw [hleft, hright] at hsplit
  have hh := congrArg (fun k : ℕ => (k : ℝ)) hsplit
  push_cast at hh
  change _ = _ - _
  unfold intervalAP primeAPOpen
  dsimp [S] at hh
  linarith


/-- Page 17, integrability of the logarithmic main term away from its singularity. -/
theorem log_reciprocal_intervalIntegrable (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx2 : 2 ≤ x := ha.trans hx.1
  exact continuousAt_const.div (Real.continuousAt_log (by linarith))
    (Real.log_pos (by linarith)).ne'


/-- Page 17, each reduced residue prime count in J has controlled endpoint error. -/
theorem intervalAP_error (T lo hi : ℝ) (d a : ℕ)
    (hT : 2 ≤ T) (hL : 1 ≤ Real.log T) (hd : 0 < d) (hdT : (d : ℝ) ≤ T)
    (ha : a < d) (hcop : Nat.Coprime a d) (hlo : 2 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ T) :
    |intervalAP lo hi d a - (∫ t in lo..hi, 1 / Real.log t) / Nat.totient d| ≤
      2 * primeError T d + 2 := by
  have hl := primeAPOpen_error T lo d a hT hL hd hdT ha hcop hlo (hlohi.trans hhi)
  have hh := primeAPOpen_error T hi d a hT hL hd hdT ha hcop (hlo.trans hlohi) hhi
  have hint := intervalIntegral.integral_add_adjacent_intervals
    (log_reciprocal_intervalIntegrable 2 lo le_rfl hlo)
    (log_reciprocal_intervalIntegrable lo hi hlo hlohi)
  rw [intervalAP_eq_sub lo hi d a hlohi]
  have heq : primeAPOpen hi d a - primeAPOpen lo d a -
      (∫ t in lo..hi, 1 / Real.log t) / Nat.totient d =
      (primeAPOpen hi d a - (∫ t in (2 : ℝ)..hi, 1 / Real.log t) / Nat.totient d) -
      (primeAPOpen lo d a - (∫ t in (2 : ℝ)..lo, 1 / Real.log t) / Nat.totient d) := by
    rw [← hint]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)


/-- Page 16, the clamped upper endpoint equals the actual upper endpoint on I3. -/
theorem jhi_eq_prime_endpoint (X B ε : ℝ) (p : ℕ) (hp : p ∈ primeWindow X B ε)
    (hY : 0 < Y X ε) : jhi X ε p = Real.sqrt (Y X ε) / p := by
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpU := (Finset.mem_filter.mp hp).2.2.2
  have hU : 0 < Y X ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hY _
  have hU2 : (Y X ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Y X ε) := by
    rw [← Real.rpow_mul_natCast hY.le, Real.sqrt_eq_rpow]
    norm_num
  have hpT : (p : ℝ) ≤ Real.sqrt (Y X ε) / p := by
    apply (le_div_iff₀ hp0).mpr
    nlinarith
  unfold jhi jlo
  apply max_eq_right
  apply max_le hpT
  have hroot : 0 ≤ Real.sqrt (Y X ε) := Real.sqrt_nonneg _
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (p : ℝ)) hp0).mpr
  nlinarith


/-- Page 16, factor counts in a residue class equal the prime count in J exactly. -/
theorem factorPrimes_residue_eq_intervalAP (X B ε : ℝ) (p d a : ℕ)
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε) :
    (((factorPrimes X ε p).filter (fun r : ℕ => r % d = a % d)).card : ℝ) =
      intervalAP (jlo X ε p) (jhi X ε p) d a := by
  classical
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
  have hT := jhi_eq_prime_endpoint X B ε p hp hY
  have hTroot : Real.sqrt (Y X ε) / p ≤ Real.sqrt (Y X ε) := by
    apply (div_le_iff₀ hp0).mpr
    nlinarith [Real.sqrt_nonneg (Y X ε)]
  unfold intervalAP
  congr 1
  apply congrArg Finset.card
  ext r
  constructor
  · intro hr
    obtain ⟨hrF, hmod⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrange, hrp, hpr, hlo, hhi⟩ := Finset.mem_filter.mp hrF
    have hrlo : jlo X ε p ≤ (r : ℝ) := by
      apply max_le (by exact_mod_cast hpr)
      apply (div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))).mpr
      push_cast at hlo
      nlinarith
    have hrhi : (r : ℝ) < jhi X ε p := by
      rw [hT]
      apply (lt_div_iff₀ hp0).mpr
      simpa only [Nat.cast_mul, mul_comm] using hhi
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hrp.pos, Nat.le_floor hrhi.le⟩, hrp, hmod⟩, hrlo, hrhi⟩
  · intro hr
    obtain ⟨hrI, hrlo, hrhi⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrange, hrp, hmod⟩ := Finset.mem_filter.mp hrI
    have hpr : p ≤ r := by exact_mod_cast ((le_max_left _ _).trans hrlo : (p : ℝ) ≤ r)
    have hrT : (r : ℝ) < Real.sqrt (Y X ε) / p := by rwa [hT] at hrhi
    have hbound : r ∈ Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor (hrT.le.trans hTroot)))
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbound, hrp, hpr, ?_, ?_⟩, hmod⟩
    · have hh : Real.sqrt (Y X ε) / (2 * p) ≤ (r : ℝ) := (le_max_right _ _).trans hrlo
      have hh' := (div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))).mp hh
      push_cast
      nlinarith
    · have hh := (lt_div_iff₀ hp0).mp hrT
      simpa only [Nat.cast_mul, mul_comm] using hh


/-- Page 17, the root classes after fixing the smaller prime factor. -/
noncomputable def twistedRoots (p n d : ℕ) [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter (fun a => ((p : ZMod d) * a) ^ 2 = (n : ZMod d))

/-- Page 17, multiplication by a unit preserves the number of root classes. -/
theorem twistedRoots_card (p n d : ℕ) [NeZero d] (hpd : Nat.Coprime p d) :
    (twistedRoots p n d).card =
      ((Finset.range d).filter (fun x => x ^ 2 % d = n % d)).card := by
  classical
  rw [Task506d.root_count_zmod]
  let e := (ZMod.unitOfCoprime p hpd).mulLeft
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp ha).2
  · intro a ha b hb hab
    exact e.injective hab
  · intro a ha
    refine ⟨e.symm a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply a⟩
    change (e (e.symm a)) ^ 2 = (n : ZMod d)
    rw [e.apply_symm_apply]
    exact (Finset.mem_filter.mp ha).2


/-- Page 17, fixing a smaller prime does not increase the tau bound on root classes. -/
theorem twistedRoots_card_le_tau (p n d : ℕ) [NeZero d]
    (hpd : Nat.Coprime p d) (hd : Squarefree d) (hnd : Nat.Coprime n d) :
    (twistedRoots p n d).card ≤ d.divisors.card := by
  rw [twistedRoots_card p n d hpd]
  exact squarefree_root_count_le_tau n d hd hnd


/-- Page 17, root classes are reduced when n is coprime to the modulus. -/
theorem twistedRoots_coprime (p n d : ℕ) [NeZero d]
    (hnd : Nat.Coprime n d) (a : ZMod d) (ha : a ∈ twistedRoots p n d) :
    Nat.Coprime a.val d := by
  have hnunit := (ZMod.isUnit_iff_coprime n d).mpr hnd
  have hpow : IsUnit (((p : ZMod d) * a) ^ 2) := by
    rw [(Finset.mem_filter.mp ha).2]
    exact hnunit
  have hm : IsUnit ((p : ZMod d) * a) := (isUnit_pow_iff (by norm_num : 2 ≠ 0)).mp hpow
  have haunit : IsUnit a := ((Commute.all (p : ZMod d) a).isUnit_mul_iff.mp hm).2
  apply (ZMod.isUnit_iff_coprime a.val d).mp
  simpa only [ZMod.natCast_zmod_val] using haunit


/-- Page 17, split the fixed smaller prime progression count by its root residue. -/
theorem factor_progression_residues (X ε : ℝ) (p n d : ℕ) [NeZero d]
    (hsmall : ∀ r ∈ factorPrimes X ε p, (p * r) ^ 2 ≤ n) :
    ((factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card =
      ∑ a ∈ twistedRoots p n d,
        ((factorPrimes X ε p).filter (fun r : ℕ => (r : ZMod d) = a)).card := by
  classical
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r hr
  have hiff : d ∣ n - (p * r) ^ 2 ↔
      (((p * r) ^ 2 : ℕ) : ZMod d) = (n : ZMod d) :=
    (Nat.modEq_iff_dvd' (hsmall r hr)).symm.trans
      (ZMod.natCast_eq_natCast_iff' ((p * r) ^ 2) n d).symm
  simpa only [twistedRoots, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.cast_pow, Nat.cast_mul] using hiff


/-- Page 17, a residue fiber of the larger prime count is the corresponding J count. -/
theorem factor_residue_cast_eq (X B ε : ℝ) (p d : ℕ) [NeZero d]
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε) (a : ZMod d) :
    (((factorPrimes X ε p).filter (fun r : ℕ => (r : ZMod d) = a)).card : ℝ) =
      intervalAP (jlo X ε p) (jhi X ε p) d a.val := by
  rw [← factorPrimes_residue_eq_intervalAP X B ε p d a.val hp hY]
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r hr
  have hh := ZMod.natCast_eq_natCast_iff' r a.val d
  simpa only [ZMod.natCast_zmod_val] using hh


/-- Page 17, the finite prime to semiprime transfer at a coprime squarefree modulus. -/
theorem factor_progression_error_coprime (X B ε : ℝ) (p n d : ℕ) [NeZero d]
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε)
    (hpd : Nat.Coprime p d) (hd : Squarefree d) (hnd : Nat.Coprime n d)
    (hsmall : ∀ r ∈ factorPrimes X ε p, (p * r) ^ 2 ≤ n)
    (hT : 2 ≤ Real.sqrt (Y X ε) / p)
    (hL : 1 ≤ Real.log (Real.sqrt (Y X ε) / p))
    (hdT : (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    |(((factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) -
      density n d * (∫ t in jlo X ε p..jhi X ε p, 1 / Real.log t)| ≤
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
  classical
  let T := Real.sqrt (Y X ε) / p
  let I := ∫ t in jlo X ε p..jhi X ε p, 1 / Real.log t
  let R := twistedRoots p n d
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hlo : 2 ≤ jlo X ε p :=
    (by exact_mod_cast hpp.two_le : (2 : ℝ) ≤ p).trans (le_max_left _ _)
  have hhi : jhi X ε p = T := jhi_eq_prime_endpoint X B ε p hp hY
  have hclass (a : ZMod d) (ha : a ∈ R) :
      |intervalAP (jlo X ε p) (jhi X ε p) d a.val - I / Nat.totient d| ≤
        2 * primeError T d + 2 := by
    apply intervalAP_error T _ _ d a.val hT hL hd0 hdT (ZMod.val_lt a)
      (twistedRoots_coprime p n d hnd a ha) hlo (le_max_left _ _) hhi.le
  have hpart := congrArg (fun k : ℕ => (k : ℝ))
    (factor_progression_residues X ε p n d hsmall)
  push_cast at hpart
  simp_rw [factor_residue_cast_eq X B ε p d hp hY] at hpart
  have hmain : density n d * I = ∑ a ∈ R, I / Nat.totient d := by
    rw [Finset.sum_const, nsmul_eq_mul]
    dsimp [R]
    rw [twistedRoots_card p n d hpd]
    simp only [density, if_pos hnd]
    ring
  have hnn : 0 ≤ 2 * primeError T d + 2 := by
    have h := primeError_nonneg T d hT hL hd0 hdT
    linarith
  change |(((factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) -
    density n d * I| ≤ _
  calc
    _ = |∑ a ∈ R, (intervalAP (jlo X ε p) (jhi X ε p) d a.val - I / Nat.totient d)| := by
      rw [hpart, hmain, Finset.sum_sub_distrib]
    _ ≤ ∑ a ∈ R, |intervalAP (jlo X ε p) (jhi X ε p) d a.val - I / Nat.totient d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ R, (2 * primeError T d + 2) := Finset.sum_le_sum hclass
    _ = (R.card : ℝ) * (2 * primeError T d + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d.divisors.card : ℝ) * (2 * primeError T d + 2) := by
      apply mul_le_mul_of_nonneg_right _ hnn
      exact_mod_cast twistedRoots_card_le_tau p n d hpd hd hnd


/-- Page 17, the progression fiber vanishes at a noncoprime modulus in the rough range. -/
theorem factor_progression_zero (X ε : ℝ) (p n d : ℕ)
    (hnd : ¬ Nat.Coprime n d)
    (hsmall : ∀ r ∈ factorPrimes X ε p, (p * r) ^ 2 ≤ n)
    (hrough : ∀ r ∈ factorPrimes X ε p, Nat.Coprime (p * r) d) :
    ((factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hrF, hdiv⟩ := Finset.mem_filter.mp hr
  have hmod := (Nat.modEq_iff_dvd' (hsmall r hrF)).mpr hdiv
  have heq := (ZMod.natCast_eq_natCast_iff' ((p * r) ^ 2) n d).mpr hmod
  have hunit : IsUnit (((p * r) ^ 2 : ℕ) : ZMod d) :=
    (ZMod.isUnit_iff_coprime ((p * r) ^ 2) d).mpr ((hrough r hrF).pow_left 2)
  rw [heq] at hunit
  exact hnd ((ZMod.isUnit_iff_coprime n d).mp hunit)


/-- Page 17, every larger prime factor remains coprime to a modulus below p. -/
theorem factorPrimes_coprime (X ε : ℝ) (p d : ℕ) (hp : p.Prime)
    (hd : 0 < d) (hdp : d < p) (r : ℕ) (hr : r ∈ factorPrimes X ε p) :
    Nat.Coprime (p * r) d := by
  have hpC : p.Coprime d := hp.coprime_iff_not_dvd.mpr (fun h =>
    (not_le_of_gt hdp) (Nat.le_of_dvd hd h))
  have hrf := (Finset.mem_filter.mp hr).2
  have hrC : r.Coprime d := hrf.1.coprime_iff_not_dvd.mpr (fun h =>
    (not_le_of_gt (hdp.trans_le hrf.2.1)) (Nat.le_of_dvd hd h))
  exact hpC.mul_left hrC


/-- Page 17, the full finite transfer includes the vanishing noncoprime case. -/
theorem factor_progression_error (X B ε : ℝ) (p n d : ℕ) [NeZero d]
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε)
    (hd : Squarefree d) (hdp : d < p)
    (hsmall : ∀ r ∈ factorPrimes X ε p, (p * r) ^ 2 ≤ n)
    (hT : 2 ≤ Real.sqrt (Y X ε) / p)
    (hL : 1 ≤ Real.log (Real.sqrt (Y X ε) / p))
    (hdT : (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    |(((factorPrimes X ε p).filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) -
      density n d * (∫ t in jlo X ε p..jhi X ε p, 1 / Real.log t)| ≤
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hpd : p.Coprime d := hpp.coprime_iff_not_dvd.mpr (fun h =>
    (not_le_of_gt hdp) (Nat.le_of_dvd hd0 h))
  by_cases hnd : Nat.Coprime n d
  · exact factor_progression_error_coprime X B ε p n d hp hY hpd hd hnd hsmall hT hL hdT
  · rw [factor_progression_zero X ε p n d hnd hsmall
      (factorPrimes_coprime X ε p d hpp hd0 hdp)]
    simp only [Nat.cast_zero, density, if_neg hnd, zero_mul, sub_self, abs_zero]
    have hE := primeError_nonneg (Real.sqrt (Y X ε) / p) d hT hL hd0 hdT
    positivity


/-- Page 17, summing the fixed smaller prime transfer gives the sequence error. -/
theorem progressionCount_error (X B ε : ℝ) (n d : ℕ) [NeZero d]
    (hY : 0 < Y X ε) (hYX : Y X ε ≤ X) (hXn : X < (n : ℝ)) (hd : Squarefree d)
    (hparams : ∀ p ∈ primeWindow X B ε, d < p ∧
      2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
        (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    |progressionCount X B ε n d - density n d * primeMass X B ε| ≤
      ∑ p ∈ primeWindow X B ε,
        (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
  rw [progressionCount_factor_sum, primeMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hdp, hT, hL, hdT⟩ := hparams p hp
  apply factor_progression_error X B ε p n d hp hY hd hdp _ hT hL hdT
  intro r hr
  have hhi := (Finset.mem_filter.mp hr).2.2.2.2
  have hs := Real.sq_sqrt hY.le
  have hnn : (0 : ℝ) ≤ (p * r : ℕ) := by positivity
  have hreal : (((p * r : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) := by nlinarith [Real.sqrt_nonneg (Y X ε)]
  exact_mod_cast hreal


/-- Page 17, a crude divisor sum bound suffices for the two endpoint corrections. -/
theorem divisor_sum_trivial (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, d.divisors.card) ≤ D ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, D := Finset.sum_le_sum fun d hd =>
      (Nat.card_divisors_le_self d).trans (Finset.mem_Icc.mp hd).2
    _ = D ^ 2 := by simp [pow_two]


/-- Page 17, the explicit remainder transfers to prime errors with an endpoint term. -/
theorem remainder_prime_transfer (X B ε : ℝ) (n : ℕ)
    (hY : 0 < Y X ε) (hYX : Y X ε ≤ X) (hXn : X < (n : ℝ))
    (hparams : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      ∀ p ∈ primeWindow X B ε, d < p ∧
        2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
          (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    remainder X B ε n ≤
      2 * (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * primeError (Real.sqrt (Y X ε) / p) d) +
      2 * ((primeWindow X B ε).card : ℝ) * (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ^ 2 := by
  classical
  let D := ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊
  let P := primeWindow X B ε
  let S := (Finset.Icc 1 D).filter Squarefree
  have hrewrite : remainder X B ε n =
      ∑ d ∈ S, |progressionCount X B ε n d - density n d * primeMass X B ε| := by
    unfold remainder
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : Squarefree d
    · have hm : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
      simp only [hs, ite_true, hm, one_mul]
    · simp only [hs, ite_false, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,
        Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  have hbound : remainder X B ε n ≤ ∑ d ∈ S, ∑ p ∈ P,
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
    rw [hrewrite]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hdI, hds⟩ := Finset.mem_filter.mp hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hdI).1
    letI : NeZero d := ⟨hd0.ne'⟩
    exact progressionCount_error X B ε n d hY hYX hXn hds (hparams d hdI)
  have hterm (d p : ℕ) :
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) =
        2 * ((d.divisors.card : ℝ) * primeError (Real.sqrt (Y X ε) / p) d) +
          2 * (d.divisors.card : ℝ) := by ring
  have hsplit : (∑ d ∈ S, ∑ p ∈ P,
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2)) =
      2 * (∑ p ∈ P, ∑ d ∈ S, (d.divisors.card : ℝ) * primeError (Real.sqrt (Y X ε) / p) d) +
        2 * (P.card : ℝ) * ∑ d ∈ S, (d.divisors.card : ℝ) := by
    rw [Finset.sum_comm]
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hfull : (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ)) ≤ (D : ℝ) ^ 2 := by
    exact_mod_cast divisor_sum_trivial D
  have hmoment : (∑ d ∈ S, (d.divisors.card : ℝ)) ≤ (D : ℝ) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)).trans hfull
  rw [hsplit] at hbound
  have hcard : (0 : ℝ) ≤ P.card := by positivity
  change remainder X B ε n ≤ 2 * _ + 2 * (P.card : ℝ) * (D : ℝ) ^ 2
  nlinarith [mul_le_mul_of_nonneg_left hmoment (show (0 : ℝ) ≤ 2 * P.card by positivity)]


/-- Page 17, the chosen modulus level lies below every rough prime factor. -/
theorem rough_level_parameters (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 18) :
    ∀ᶠ X : ℝ in Filter.atTop, 0 < Y X ε ∧ Y X ε ≤ X ∧
      Y X ε ^ (1 / 9 : ℝ) < z0 X B ε := by
  filter_upwards [Task506c.sieve_level_margin (2 * B) ε hε,
    Filter.eventually_gt_atTop (1 : ℝ)] with X hmargin hX
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hθ : 0 < 7 / 12 + ε / 2 := by linarith
  have hY1 : 1 < Y X ε := Real.one_lt_rpow hX hθ
  have hz : z0 X B ε = Y X ε ^ (1 / 4 : ℝ) * Real.log X ^ (-(2 * B)) := by
    unfold z0
    congr 1
    rw [← Real.rpow_intCast, ← Real.rpow_mul hL.le]
    congr 1
    norm_num
    ring
  refine ⟨by linarith, Real.rpow_le_self_of_one_le hX.le (by linarith), ?_⟩
  rw [hz]
  apply hmargin.trans_lt
  apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hL _)
  exact Real.rpow_lt_rpow_of_exponent_lt hY1 (by norm_num)


/-- Page 17, the endpoint correction is absorbed by every prescribed logarithmic error. -/
theorem endpoint_correction_bound (A B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      2 * ((primeWindow X B ε).card : ℝ) * (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ^ 2 ≤
        4 * errorScale X ε A := by
  filter_upwards [Task506c.sieve_level_margin (A / 2) ε hε,
    Filter.eventually_gt_atTop (1 : ℝ)] with X hmargin hX
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hY1 : 1 ≤ Y X ε := Real.one_le_rpow hX.le (by linarith)
  have hY : 0 < Y X ε := by linarith
  have hU : 1 ≤ Y X ε ^ (1 / 4 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have hcard : ((primeWindow X B ε).card : ℝ) ≤ 2 * Y X ε ^ (1 / 4 : ℝ) := by
    have hc := Finset.card_filter_le (Finset.range (⌊Y X ε ^ (1 / 4 : ℝ)⌋₊ + 1))
      (fun p : ℕ => p.Prime ∧ z0 X B ε ≤ (p : ℝ) ∧ (p : ℝ) < Y X ε ^ (1 / 4 : ℝ))
    rw [Finset.card_range] at hc
    have hcR : ((primeWindow X B ε).card : ℝ) ≤ (⌊Y X ε ^ (1 / 4 : ℝ)⌋₊ : ℝ) + 1 := by
      exact_mod_cast hc
    have hf := Nat.floor_le (Real.rpow_nonneg hY.le (1 / 4 : ℝ))
    linarith
  have hD : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤
      Y X ε ^ (1 / 8 : ℝ) * Real.log X ^ (-(A / 2)) :=
    (Nat.floor_le (Real.rpow_nonneg hY.le _)).trans hmargin
  have hpowY : (Y X ε ^ (1 / 8 : ℝ)) ^ 2 = Y X ε ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  have hpowL : (Real.log X ^ (-(A / 2))) ^ 2 = Real.log X ^ (-A) := by
    rw [← Real.rpow_mul_natCast hL.le]
    congr 1
    push_cast
    ring
  have hDsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ by positivity) hD 2
  rw [mul_pow, hpowY, hpowL] at hDsq
  have hU2 : (Y X ε ^ (1 / 4 : ℝ)) ^ 2 = Y X ε ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  calc
    _ ≤ 2 * (2 * Y X ε ^ (1 / 4 : ℝ)) *
        (Y X ε ^ (1 / 4 : ℝ) * Real.log X ^ (-A)) := by
      gcongr
    _ = 4 * errorScale X ε A := by
      unfold errorScale
      rw [← hU2]
      ring


/-- Page 17 between 57 and 58, the full remainder estimate.
CONDITIONAL ON maximal_bombieri_vinogradov alone. -/
theorem bv_remainder_from_maximal (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  obtain ⟨K, hK, hprime⟩ := prime_window_weighted_bv A B ε hA hB hε hε1
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      ∀ n : ℕ, X < (n : ℝ) → remainder X B ε n ≤ (2 * K + 4) * errorScale X ε A := by
    filter_upwards [hprime, rough_level_parameters B ε hB hε hε1,
      prime_window_bv_parameters 1 2 B ε (by norm_num) hB hε hε1,
      endpoint_correction_bound A B ε hε] with X hp hr hw he
    intro n hXn
    have hparams : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        ∀ p ∈ primeWindow X B ε, d < p ∧
          2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
            (d : ℝ) ≤ Real.sqrt (Y X ε) / p := by
      intro d hd p hpp
      obtain ⟨hT, hlog, hlo, hhi, hlevel⟩ := hw.2 p hpp
      have hdD : (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) :=
        (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d : ℝ) ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).trans
          (Nat.floor_le (Real.rpow_nonneg hr.1.le _))
      have hpz := (Finset.mem_filter.mp hpp).2.2.1
      have hdp : d < p := by exact_mod_cast (hdD.trans_lt (hr.2.2.trans_le hpz))
      have hlogpow : Real.log (Real.sqrt (Y X ε) / p) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
      have hroot : Real.sqrt (Real.sqrt (Y X ε) / p) ≤ Real.sqrt (Y X ε) / p := by
        have hh := Real.sq_sqrt (show 0 ≤ Real.sqrt (Y X ε) / p by positivity)
        nlinarith [Real.sqrt_nonneg (Real.sqrt (Y X ε) / p)]
      have hdT := hdD.trans (hlevel.trans ((mul_le_of_le_one_right
        (Real.sqrt_nonneg _) hlogpow).trans hroot))
      exact ⟨hdp, hT, hlog, hdT⟩
    have ht := remainder_prime_transfer X B ε n hr.1 hr.2.1 hXn hparams
    nlinarith
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨2 * K + 4, X0, by positivity, ?_⟩
  intro X hX n hn hXn hnhi
  exact hX0 X hX n hXn


end LeanLab.KumchevLiu2007.Task542a
