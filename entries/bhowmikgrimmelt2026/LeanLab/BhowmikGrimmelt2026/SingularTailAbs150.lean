module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.HeathBrown1985.DivisorEps

/-!
ROUTE BURST 7, 20261112. COPY of SingularTail150.lean with a different final theorem, said
plainly: every private lemma below and the body of `singular_tail_abs150` up to the partial
sum bound `hpartial` are copied verbatim from SingularTail150.lean, which keeps them private.
New here: `singular_tail_abs150`, the ABSOLUTE tail bound
`N Σ_{q > N^{1/2}} μ(q)² |c_q(N)| / φ(q)² ≪ N^{1/2+ε}` for every finite range of `q`, which the
proof of `singular_tail150` establishes on the way as `hpartial`; and the two facts
`ramanujan_neg_eq_re150`, `c_q(-N) = c_q(N)` is real, and `norm_ramanujan_le150`,
`|c_q(N)| ≤ φ(q)`, used by `truncation_level150` in Decomp150a.lean.

Source of the original: P0029 Bhowmik and Grimmelt 2026, Section 3, page 12, the unnumbered
display after 3.7.  AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

private lemma ee_add' (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma ee_nat_mul (k : ℕ) (x : ℝ) : ee ((k : ℝ) * x) = (ee x) ^ k := by
  induction k with
  | zero => simp [ee]
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, ee_add', ih, pow_succ]

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma ee_one : ee (1 : ℝ) = 1 := by unfold ee; norm_num

private lemma ee_int_mul (k : ℤ) (x : ℝ) : ee ((k : ℝ) * x) = (ee x) ^ k := by
  unfold ee
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma ee_int_cast (k : ℤ) : ee ((k : ℝ)) = 1 := by
  have h := ee_int_mul k 1
  rw [mul_one] at h
  rw [h, ee_one, one_zpow]

private lemma ee_eq_one_iff {x : ℝ} : ee x = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    have h' : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = 1 := h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero hx)
  · rintro ⟨k, rfl⟩
    exact ee_int_cast k

/-- The orthogonality relation `Σ_{b<m} e(bN/m) = m` if `m ∣ N`, else `0`. -/
private lemma sum_ee_orth {m : ℕ} (hm : 0 < m) (N : ℤ) :
    ∑ b ∈ Finset.range m, ee (((b : ℝ) * (N : ℝ)) / m) =
      if (m : ℤ) ∣ N then (m : ℝ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := ee ((N : ℝ) / m) with hc
  have hterm : ∀ b ∈ Finset.range m, ee (((b : ℝ) * (N : ℝ)) / m) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (N : ℝ)) / m = (b : ℝ) * ((N : ℝ) / m) := by field_simp
    rw [harg, ee_nat_mul]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = ee ((m : ℝ) * ((N : ℝ) / m)) := by
      rw [hc]; exact (ee_nat_mul m ((N : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (N : ℝ) hmR, ee_int_cast]
  have hiff : c = 1 ↔ (m : ℤ) ∣ N := by
    rw [hc, ee_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      have h2 : (N : ℝ) = (k : ℝ) * (m : ℝ) := by
        rw [div_eq_iff hmR] at hk
        linarith [hk]
      have h3 : N = k * (m : ℤ) := by exact_mod_cast h2
      exact ⟨k, by rw [h3]; ring⟩
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      push_cast
      field_simp
  by_cases h1 : c = 1
  · rw [ite_eq_left (hiff.mp h1)]
    simp [h1]
  · rw [ite_eq_right (fun h => h1 (hiff.mpr h))]
    rw [geom_sum_eq h1 m, hcm]
    simp

private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := moebius) (x := n)
  rw [moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma divisors_filter_dvd_eq_gcd {q a : ℕ} (hq : q ≠ 0) :
    q.divisors.filter (fun d => d ∣ a) = (a.gcd q).divisors := by
  have hg : a.gcd q ∣ q := Nat.gcd_dvd_right a q
  have hg0 : a.gcd q ≠ 0 := by
    rcases Nat.eq_zero_or_pos (a.gcd q) with h | h
    · rw [h] at hg; exact absurd (Nat.eq_zero_of_zero_dvd hg) hq
    · exact h.ne'
  rw [← Nat.divisors_filter_dvd_of_dvd hq hg]
  refine Finset.filter_congr (fun d hd => ?_)
  simp only [Nat.mem_divisors] at hd
  exact ⟨fun h => Nat.dvd_gcd h hd.1, fun h => Nat.dvd_trans h (Nat.gcd_dvd_left a q)⟩

private lemma indicator_coprime {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, divisors_filter_dvd_eq_gcd hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors (a.gcd q))
  push_cast at h
  exact h.symm

private lemma sum_range_filter_dvd {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
    ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), g a
      = ∑ b ∈ Finset.range (q / d), g (d * b) := by
  have hdq' : d * (q / d) = q := Nat.mul_div_cancel' hdq
  have hset : (Finset.range q).filter (fun a => d ∣ a)
      = (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨haq, b, rfl⟩
      refine ⟨b, ?_, rfl⟩
      rw [← hdq'] at haq
      exact Nat.lt_of_mul_lt_mul_left haq
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, ⟨b, rfl⟩⟩
      rw [← hdq']
      exact Nat.mul_lt_mul_of_pos_left hb hd
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hd hxy

/-- The Ramanujan sum as a divisor sum: `c_q(N) = Σ_{d ∣ q, (q/d) ∣ N} μ(d)·(q/d)`. -/
private lemma ramanujan_eq_complex (q : ℕ) (N : ℤ) :
    ramanujan q N = ∑ d ∈ q.divisors,
      (moebius d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ N then ((q / d : ℕ) : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [ramanujan]
  have hq0 : q ≠ 0 := hq.ne'
  have hfilter : (Finset.range q).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => a.gcd q = 1) :=
    Finset.filter_congr (fun a _ => Nat.coprime_iff_gcd_eq_one)
  rw [ramanujan, hfilter, Finset.sum_filter]
  have hstep1 : ∑ a ∈ Finset.range q, (if a.gcd q = 1 then ee (((a : ℝ) * (N : ℝ)) / q) else 0)
      = ∑ a ∈ Finset.range q,
          (∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0))
            * ee (((a : ℝ) * (N : ℝ)) / q) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (if a.gcd q = 1 then (1:ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q)
        = (if a.gcd q = 1 then ee (((a : ℝ) * (N : ℝ)) / q) else 0) := by
      by_cases h : a.gcd q = 1 <;> simp [h]
    rw [← h1, indicator_coprime hq0 a]
  rw [hstep1]
  have hstep2 : ∀ a ∈ Finset.range q,
      (∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0))
        * ee (((a : ℝ) * (N : ℝ)) / q)
      = ∑ d ∈ q.divisors,
          (if d ∣ a then (moebius d : ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q) := by
    intro a _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq
  have hm0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hd0
  have hfac : ∑ a ∈ Finset.range q,
        (if d ∣ a then (moebius d : ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q)
      = ∑ a ∈ Finset.range q,
          (if d ∣ a then (moebius d : ℂ) * ee (((a : ℝ) * (N : ℝ)) / q) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : d ∣ a <;> simp [h]
  rw [hfac, ← Finset.sum_filter, sum_range_filter_dvd hd0 hdvd, ← Finset.mul_sum]
  congr 1
  have hqd : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  have hqd0 : ((q / d : ℕ) : ℝ) ≠ 0 := by positivity
  have harg : ∀ b : ℕ, ee (((d * b : ℕ) : ℝ) * (N : ℝ) / q)
      = ee (((b : ℝ) * (N : ℝ)) / (((q / d : ℕ)) : ℝ)) := by
    intro b
    congr 1
    rw [Nat.cast_div hdvd (by positivity : ((d : ℕ) : ℝ) ≠ 0), ← hqd]
    push_cast
    have hdR : ((d : ℕ) : ℝ) ≠ 0 := by positivity
    have hmR : ((q / d : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl (fun b _ => harg b), sum_ee_orth hm0 N]
  have hcd : ((q : ℤ) / (d : ℤ)) = (((q / d : ℕ)) : ℤ) := (Int.natCast_div q d).symm
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ N
  · rw [ite_eq_left h, ite_eq_left h]
    norm_num
  · rw [ite_eq_right h, ite_eq_right h]
    norm_num

/-- The Ramanujan sum, with the real divisor sum written out. -/
private lemma ramanujan_eq_real (N q : ℕ) :
    ramanujan q (N : ℤ) = ∑ d ∈ q.divisors,
      ((((moebius d : ℤ)) : ℝ) : ℂ) *
        ((if (q / d : ℕ) ∣ N then ((((q / d : ℕ)) : ℝ) : ℂ) else 0)) := by
  rw [ramanujan_eq_complex]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hiff : ((((q / d : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ)) ↔ (q / d : ℕ) ∣ N := Int.natCast_dvd_natCast
  have hmc : (moebius d : ℂ) = ((((moebius d : ℤ)) : ℝ) : ℂ) := by push_cast; ring
  have hif : (if ((((q / d : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ)) then (((q / d : ℕ)) : ℂ) else 0)
      = ((if (q / d : ℕ) ∣ N then ((((q / d : ℕ)) : ℝ) : ℂ) else 0)) := by
    by_cases hd : (q / d : ℕ) ∣ N
    · rw [ite_eq_left (hiff.mpr hd), ite_eq_left hd]
      norm_num
    · rw [ite_eq_right (fun hh => hd (hiff.mp hh)), ite_eq_right hd]
  rw [hmc, hif]

private lemma cN_eq (N q : ℕ) :
    (ramanujan q (N : ℤ)).re = ∑ d ∈ q.divisors,
      ((moebius d : ℤ) : ℝ) * (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
  rw [ramanujan_eq_real, Complex.re_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : (q / d : ℕ) ∣ N
  · rw [ite_eq_left hd, ite_eq_left hd, ← Complex.ofReal_mul, Complex.ofReal_re]
  · rw [ite_eq_right hd, ite_eq_right hd]
    simp

/-! ### New in this pass: the tail bound -/

/-- `|c_q(N)| ≤ Σ_{e ∣ N, e ∣ q} e`. -/
private lemma cN_abs_le_dvd (N q : ℕ) (hN : 1 ≤ N) :
    |(ramanujan q (N : ℤ)).re| ≤ ∑ e ∈ N.divisors, (if e ∣ q then (e : ℝ) else 0) := by
  rw [cN_eq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hmu1 : ∀ d : ℕ, |((moebius d : ℤ) : ℝ)| ≤ 1 := by
    intro d
    have h := abs_moebius_le_one (n := d)
    rw [abs_le] at h ⊢
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hstep1 : ∑ d ∈ q.divisors,
      |((moebius d : ℤ) : ℝ) * (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)|
      ≤ ∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro d _
    rw [abs_mul]
    have hmu := hmu1 d
    have hnn : (0 : ℝ) ≤ (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
      split_ifs <;> positivity
    calc |((moebius d : ℤ) : ℝ)| * |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)|
        ≤ 1 * |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ = |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)| := one_mul _
      _ = (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := abs_of_nonneg hnn
  refine le_trans hstep1 ?_
  have himg : (q.divisors.filter (fun d => (q / d : ℕ) ∣ N)).image (fun d => q / d) ⊆
      N.divisors.filter (fun e => e ∣ q) := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have hdN : (q / d : ℕ) ∣ N := (Finset.mem_filter.mp hd).2
    have hdq : d ∣ q := (Nat.mem_divisors.mp (Finset.mem_of_mem_filter d hd)).1
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdN, by omega⟩, Nat.div_dvd_of_dvd hdq⟩
  have hinj : Set.InjOn (fun d => q / d) ↑(q.divisors.filter (fun d => (q / d : ℕ) ∣ N)) := by
    intro d hd d' hd' heq
    have hd1 : d ∈ q.divisors := Finset.mem_of_mem_filter d hd
    have hd1' : d' ∈ q.divisors := Finset.mem_of_mem_filter d' hd'
    obtain ⟨hdq, hq0⟩ := Nat.mem_divisors.mp hd1
    obtain ⟨hdq', -⟩ := Nat.mem_divisors.mp hd1'
    have h1 : q / (q / d) = d := Nat.div_div_self hdq hq0
    have h2 : q / (q / d') = d' := Nat.div_div_self hdq' hq0
    have heq' : q / d = q / d' := heq
    rw [heq'] at h1
    rw [h1] at h2
    exact h2
  calc ∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)
      = ∑ d ∈ q.divisors.filter (fun d => (q / d : ℕ) ∣ N), ((q / d : ℕ) : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ = ∑ e ∈ (q.divisors.filter (fun d => (q / d : ℕ) ∣ N)).image (fun d => q / d), (e : ℝ) :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ e ∈ N.divisors.filter (fun e => e ∣ q), (e : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun e _ _ => by positivity)
    _ = ∑ e ∈ N.divisors, (if e ∣ q then (e : ℝ) else 0) := Finset.sum_filter _ _

/-- `n ≤ φ(n) d(n)`, since `n / φ(n) = Π_{p ∣ n} p/(p-1) ≤ 2 ^ ω(n) ≤ d(n)`. -/
private lemma le_totient_mul_card_divisors (n : ℕ) :
    n ≤ Nat.totient n * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hid := Nat.totient_mul_prod_primeFactors n
  have h2 : ∏ p ∈ n.primeFactors, p ≤
      2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h3 : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    rw [Nat.card_divisors hn.ne', ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hp' : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
    have : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    omega
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ Nat.totient n * (n.divisors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
      _ = (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

/-- `n ^ a / φ(n)² ≤ D² n ^ (a - 2 + 2/k)`, from `φ(n) ≥ n ^ (1 - 1/k) / D`. -/
private lemma totient_rpow_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ℝ,
      (n : ℝ) ^ a / (Nat.totient n : ℝ) ^ 2 ≤ D ^ 2 * (n : ℝ) ^ (a - 2 + 2 * (k : ℝ)⁻¹) := by
  obtain ⟨D, hD, hDb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨D, hD, fun n hn a => ?_⟩
  set t : ℝ := (k : ℝ)⁻¹ with ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have h1 : (n : ℝ) ≤ (Nat.totient n : ℝ) * (D * (n : ℝ) ^ t) := by
    have h0 := le_totient_mul_card_divisors n
    have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * (n.divisors.card : ℝ) := by exact_mod_cast h0
    exact h'.trans (mul_le_mul_of_nonneg_left (hDb n hn) hφ.le)
  have hsplit : (n : ℝ) = (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t := by
    rw [← Real.rpow_add hnR]; simp
  have hnt : 0 < (n : ℝ) ^ t := Real.rpow_pos_of_pos hnR t
  have h2 : (n : ℝ) ^ (1 - t) ≤ D * (Nat.totient n : ℝ) := by
    have h4 : (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t ≤ (D * (Nat.totient n : ℝ)) * (n : ℝ) ^ t := by
      rw [← hsplit]; linarith [h1]
    exact le_of_mul_le_mul_right h4 hnt
  have h3 : (n : ℝ) ^ (2 - 2 * t) ≤ D ^ 2 * (Nat.totient n : ℝ) ^ 2 := by
    have e : (n : ℝ) ^ (2 - 2 * t) = ((n : ℝ) ^ (1 - t)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
      congr 1
      push_cast
      ring
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have e2 : (n : ℝ) ^ a = (n : ℝ) ^ (a - 2 + 2 * t) * (n : ℝ) ^ (2 - 2 * t) := by
    rw [← Real.rpow_add hnR]; congr 1; ring
  rw [e2, div_le_iff₀ (by positivity)]
  calc (n : ℝ) ^ (a - 2 + 2 * t) * (n : ℝ) ^ (2 - 2 * t)
      ≤ (n : ℝ) ^ (a - 2 + 2 * t) * (D ^ 2 * (Nat.totient n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = D ^ 2 * (n : ℝ) ^ (a - 2 + 2 * t) * (Nat.totient n : ℝ) ^ 2 := by ring

/-- `c_q(-N) = c_q(N)` and it is real: the divisor formula depends on `N` only through
divisibility. PROVED. -/
theorem ramanujan_neg_eq_re150 (q N : ℕ) :
    ramanujan q (-(N : ℤ)) = (((ramanujan q (N : ℤ)).re : ℝ) : ℂ) := by
  have h1 : ramanujan q (-(N : ℤ)) = ramanujan q (N : ℤ) := by
    rw [ramanujan_eq_complex, ramanujan_eq_complex]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Int.dvd_neg]
  rw [h1, ramanujan_eq_real, Complex.re_sum]
  push_cast
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : (q / d : ℕ) ∣ N
  · simp [hd]
  · simp [hd]

/-- `|c_q(n)| ≤ φ(q)`. PROVED. -/
theorem norm_ramanujan_le150 (q : ℕ) (n : ℤ) : ‖ramanujan q n‖ ≤ (Nat.totient q : ℝ) := by
  unfold ramanujan
  refine (norm_sum_le _ _).trans ?_
  have hn : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖ee ((a : ℝ) * n / q)‖ = 1 := by
    intro a _
    unfold ee
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (((a : ℝ) * n / q : ℝ) : ℂ) =
      ((2 * Real.pi * ((a : ℝ) * n / q) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [Finset.sum_congr rfl hn, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.totient_eq_card_coprime]
  have : (Finset.range q).filter (fun a => Nat.Coprime a q) =
      (Finset.range q).filter (fun a => q.Coprime a) :=
    Finset.filter_congr (fun a _ => Nat.coprime_comm)
  rw [this]

/-- The ABSOLUTE tail of the singular series beyond the Farey level `⌊N^{1/2}⌋`, for every
finite range of `q`: `N Σ_{q < M, q > ⌊N^{1/2}⌋} μ(q)² |c_q(N)| / φ(q)² ≤ C N^{1/2+ε}`.
P0029 page 12, the display after 3.7.  PROVED, the proof of `singular_tail150` up to its
partial sum bound, copied. -/
theorem singular_tail_abs150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ,
      (N : ℝ) * ∑ q ∈ Finset.range M, |(if q ≤ Nat.sqrt N then 0 else
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
            (ramanujan q (N : ℤ)).re)| ≤
        C * (N : ℝ) ^ (1 / 2 + ε) := by
  intro ε hε
  set k : ℕ := ⌈3 / ε⌉₊ + 8 with hk
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set t : ℝ := (k : ℝ)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hkpos
  have ht8 : t ≤ 1 / 8 := by
    have h8 : (8 : ℝ) ≤ k := by exact_mod_cast (by omega : 8 ≤ k)
    rw [ht, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h8
  have h3t : 3 * t ≤ ε := by
    have hc : 3 / ε ≤ (k : ℝ) := by
      have h1 := Nat.le_ceil (3 / ε)
      have h2 : (⌈3 / ε⌉₊ : ℝ) ≤ k := by exact_mod_cast (by omega : ⌈3 / ε⌉₊ ≤ k)
      linarith
    rw [div_le_iff₀ hε] at hc
    have e : 3 * t = 3 / k := by rw [ht]; ring
    rw [e, div_le_iff₀ hkpos]
    linarith
  set α : ℝ := 1 - 4 * t with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  set p : ℝ := 1 + 2 * t with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hpne : p ≠ 0 := by linarith
  obtain ⟨D, hD, hDphi⟩ := totient_rpow_bound k hk1
  obtain ⟨D', hD', hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk1
  have hZs : Summable (fun m : ℕ => 1 / (m : ℝ) ^ p) :=
    Real.summable_one_div_nat_rpow.mpr hp1
  set Z : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ p with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun m => by positivity)
  refine ⟨D' * D ^ 4 * Z, ?_⟩
  intro N hN M0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set Q : ℕ := Nat.sqrt N with hQ
  set f : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      (Nat.totient q : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re with hf
  set g : ℕ → ℝ := fun q => if q ≤ Q then f q else 0 with hg
  set h : ℕ → ℝ := fun q => if q ≤ Q then 0 else f q with hh
  -- the majorant of the tail
  set G : ℕ → ℝ := fun q => ∑ e ∈ N.divisors,
      (if e ∣ q then (e : ℝ) * (q : ℝ) ^ α / (Nat.totient q : ℝ) ^ 2 else 0) with hG
  have hG0 : ∀ q, 0 ≤ G q := fun q =>
    Finset.sum_nonneg (fun e _ => by split_ifs <;> positivity)
  have hpt : ∀ q, |h q| ≤ (N : ℝ) ^ (-(α / 2)) * G q := by
    intro q
    by_cases hqQ : q ≤ Q
    · simp only [hh, ite_eq_left hqQ, abs_zero]
      exact mul_nonneg (by positivity) (hG0 q)
    · simp only [hh, ite_eq_right hqQ]
      have hQq : Nat.sqrt N < q := by omega
      have hNq : N < q * q := Nat.sqrt_lt.mp hQq
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · subst h0; simp at hNq
        · exact h0
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
      have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hNq' : (N : ℝ) ≤ (q : ℝ) ^ 2 := by
        have : N ≤ q ^ 2 := by rw [sq]; omega
        exact_mod_cast this
      have hqpow : (N : ℝ) ^ (α / 2) ≤ (q : ℝ) ^ α := by
        have h1 := Real.rpow_le_rpow hNpos.le hNq' (by positivity : (0 : ℝ) ≤ α / 2)
        have e : ((q : ℝ) ^ 2) ^ (α / 2) = (q : ℝ) ^ α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
          congr 1
          push_cast
          ring
        rwa [e] at h1
      have hratio : 1 ≤ (N : ℝ) ^ (-(α / 2)) * (q : ℝ) ^ α := by
        rw [Real.rpow_neg hNpos.le, inv_mul_eq_div, one_le_div (by positivity)]
        exact hqpow
      have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 ≤ 1 := by
        have hm : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
          have h := abs_moebius_le_one (n := q)
          rw [abs_le] at h ⊢
          constructor
          · exact_mod_cast h.1
          · exact_mod_cast h.2
        exact (sq_le_one_iff_abs_le_one _).mpr hm
      have hA0 : 0 ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 := by
        positivity
      have hA : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
          1 / (Nat.totient q : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmu (by positivity)
      have hc := cN_abs_le_dvd N q hN
      set S : ℝ := ∑ e ∈ N.divisors, (if e ∣ q then (e : ℝ) else 0) with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg (fun e _ => by split_ifs <;> positivity)
      have hfq : |f q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 * S := by
        simp only [hf]
        rw [abs_mul, abs_of_nonneg hA0]
        exact mul_le_mul hA hc (abs_nonneg _) (by positivity)
      have hGq : (N : ℝ) ^ (-(α / 2)) * G q =
          ((N : ℝ) ^ (-(α / 2)) * (q : ℝ) ^ α) * (1 / (Nat.totient q : ℝ) ^ 2 * S) := by
        simp only [hG, hS]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        split_ifs <;> ring
      rw [hGq]
      calc |f q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 * S := hfq
        _ = 1 * (1 / (Nat.totient q : ℝ) ^ 2 * S) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)
  -- one divisor at a time
  have hdiv : ∀ e ∈ N.divisors, ∀ M : ℕ, ∑ q ∈ Finset.range M,
      (if e ∣ q then (e : ℝ) * (q : ℝ) ^ α / (Nat.totient q : ℝ) ^ 2 else 0) ≤ D ^ 4 * Z := by
    intro e he M
    have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
    have heR : (0 : ℝ) < e := by exact_mod_cast he1
    have hφe : (0 : ℝ) < (Nat.totient e : ℝ) := by exact_mod_cast Nat.totient_pos.mpr he1
    set F : ℕ → ℝ := fun q => (e : ℝ) * (q : ℝ) ^ α / (Nat.totient q : ℝ) ^ 2 with hF
    have hF0 : ∀ q, 0 ≤ F q := fun q => by simp only [hF]; positivity
    -- the bound at `q = e m`
    have hEm : ∀ m : ℕ, F (e * m) ≤ D ^ 4 * (1 / (m : ℝ) ^ p) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · subst hm0
        simp [hF, Real.zero_rpow hpne]
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      have hφm : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm1
      have hsup : (Nat.totient e : ℝ) * (Nat.totient m : ℝ) ≤ (Nat.totient (e * m) : ℝ) := by
        exact_mod_cast Nat.totient_super_multiplicative e m
      have hsup2 : ((Nat.totient e : ℝ) * (Nat.totient m : ℝ)) ^ 2 ≤
          (Nat.totient (e * m) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hsup 2
      have hstep : F (e * m) ≤ (e : ℝ) * ((e : ℝ) ^ α * (m : ℝ) ^ α) /
          ((Nat.totient e : ℝ) * (Nat.totient m : ℝ)) ^ 2 := by
        simp only [hF]
        rw [Nat.cast_mul, Real.mul_rpow heR.le hmR.le]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsup2
      have hsplit : (e : ℝ) * ((e : ℝ) ^ α * (m : ℝ) ^ α) /
          ((Nat.totient e : ℝ) * (Nat.totient m : ℝ)) ^ 2 =
          ((e : ℝ) ^ (1 + α) / (Nat.totient e : ℝ) ^ 2) *
            ((m : ℝ) ^ α / (Nat.totient m : ℝ) ^ 2) := by
        rw [Real.rpow_add heR, Real.rpow_one]
        field_simp
      have hbe : (e : ℝ) ^ (1 + α) / (Nat.totient e : ℝ) ^ 2 ≤ D ^ 2 := by
        have h1 := hDphi e he1 (1 + α)
        have h2 : (e : ℝ) ^ (1 + α - 2 + 2 * (k : ℝ)⁻¹) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast he1)
          rw [← ht, hα]; linarith
        calc _ ≤ D ^ 2 * (e : ℝ) ^ (1 + α - 2 + 2 * (k : ℝ)⁻¹) := h1
          _ ≤ D ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = D ^ 2 := mul_one _
      have hbm : (m : ℝ) ^ α / (Nat.totient m : ℝ) ^ 2 ≤ D ^ 2 * (1 / (m : ℝ) ^ p) := by
        have h1 := hDphi m hm1 α
        have e : α - 2 + 2 * (k : ℝ)⁻¹ = -p := by rw [← ht, hα, hp]; ring
        rw [e, Real.rpow_neg hmR.le, ← one_div] at h1
        exact h1
      calc F (e * m) ≤ _ := hstep
        _ = _ := hsplit
        _ ≤ D ^ 2 * (D ^ 2 * (1 / (m : ℝ) ^ p)) :=
            mul_le_mul hbe hbm (by positivity) (by positivity)
        _ = D ^ 4 * (1 / (m : ℝ) ^ p) := by ring
    have hsub : (Finset.range M).filter (fun q => e ∣ q) ⊆
        (Finset.range M).image (fun m => e * m) := by
      intro q hq
      obtain ⟨hqM, hdq⟩ := Finset.mem_filter.mp hq
      rw [Finset.mem_range] at hqM
      refine Finset.mem_image.mpr ⟨q / e, ?_, Nat.mul_div_cancel' hdq⟩
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (Nat.div_le_self q e) hqM
    have hinj : Set.InjOn (fun m => e * m) ↑(Finset.range M) := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left he1 hxy
    calc ∑ q ∈ Finset.range M,
          (if e ∣ q then (e : ℝ) * (q : ℝ) ^ α / (Nat.totient q : ℝ) ^ 2 else 0)
        = ∑ q ∈ (Finset.range M).filter (fun q => e ∣ q), F q := (Finset.sum_filter _ _).symm
      _ ≤ ∑ q ∈ (Finset.range M).image (fun m => e * m), F q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hF0 q)
      _ = ∑ m ∈ Finset.range M, F (e * m) := Finset.sum_image hinj
      _ ≤ ∑ m ∈ Finset.range M, D ^ 4 * (1 / (m : ℝ) ^ p) :=
          Finset.sum_le_sum (fun m _ => hEm m)
      _ = D ^ 4 * ∑ m ∈ Finset.range M, 1 / (m : ℝ) ^ p := (Finset.mul_sum _ _ _).symm
      _ ≤ D ^ 4 * Z :=
          mul_le_mul_of_nonneg_left
            (hZs.sum_le_tsum _ (fun m _ => by positivity)) (by positivity)
  set B : ℝ := (N : ℝ) ^ (-(α / 2)) * ((D' * (N : ℝ) ^ t) * (D ^ 4 * Z)) with hB
  have hpartial : ∀ M : ℕ, ∑ q ∈ Finset.range M, |h q| ≤ B := by
    intro M
    calc ∑ q ∈ Finset.range M, |h q|
        ≤ ∑ q ∈ Finset.range M, (N : ℝ) ^ (-(α / 2)) * G q := Finset.sum_le_sum (fun q _ => hpt q)
      _ = (N : ℝ) ^ (-(α / 2)) * ∑ e ∈ N.divisors, ∑ q ∈ Finset.range M,
            (if e ∣ q then (e : ℝ) * (q : ℝ) ^ α / (Nat.totient q : ℝ) ^ 2 else 0) := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [hG]
          exact Finset.sum_comm
      _ ≤ (N : ℝ) ^ (-(α / 2)) * ∑ e ∈ N.divisors, D ^ 4 * Z :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e he => hdiv e he M)) (by positivity)
      _ = (N : ℝ) ^ (-(α / 2)) * ((N.divisors.card : ℝ) * (D ^ 4 * Z)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right (hτ N hN) (by positivity)
  have hexp : (N : ℝ) * (N : ℝ) ^ (-(α / 2)) * (N : ℝ) ^ t = (N : ℝ) ^ (1 / 2 + 3 * t) := by
    have e : (1 / 2 + 3 * t : ℝ) = 1 + -(α / 2) + t := by rw [hα]; ring
    rw [e, Real.rpow_add hNpos, Real.rpow_add hNpos, Real.rpow_one]
  have hmono : (N : ℝ) ^ (1 / 2 + 3 * t) ≤ (N : ℝ) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  show (N : ℝ) * ∑ q ∈ Finset.range M0, |h q| ≤ _
  calc (N : ℝ) * ∑ q ∈ Finset.range M0, |h q| ≤ (N : ℝ) * B :=
        mul_le_mul_of_nonneg_left (hpartial M0) hNpos.le
    _ = D' * D ^ 4 * Z * ((N : ℝ) * (N : ℝ) ^ (-(α / 2)) * (N : ℝ) ^ t) := by rw [hB]; ring
    _ = D' * D ^ 4 * Z * (N : ℝ) ^ (1 / 2 + 3 * t) := by rw [hexp]
    _ ≤ D' * D ^ 4 * Z * (N : ℝ) ^ (1 / 2 + ε) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

end LeanLab.BhowmikGrimmelt2026
