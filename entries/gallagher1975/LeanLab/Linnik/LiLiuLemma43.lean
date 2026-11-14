module

public import LeanLab.PNTPort.Vinogradov.MajorArc
public import LeanLab.PNTPort.LargeSieve.MontgomeryBT

/-!
Li-Liu, arXiv 2610.15784 v1, Lemma 4.3, the lower bound half: the arithmetic step of the proof.
Read in Claude in Chrome on arxiv.org/html/2610.15784v1, Section 4, run 20261019T1902Z-2936.

The proof of Lemma 4.3 writes: since every prime p in S exceeds P ≥ q, "the Ramanujan sum
identity and Cauchy's inequality give"
  ∑_{a mod q, (a, q) = 1} |S(a/q + β)|² ≥ (1/φ(q)) |∑_{(a,q)=1} S(a/q + β)|² = μ(q)²/φ(q) |S(β)|²,
and then sums over q ≤ P/T using ∑_{q ≤ P/T} μ(q)²/φ(q) = log P + O_T(1).

Here, for any finite set A of primes above Q and any complex weights:
* `twisted_sum`: ∑_{(r,q)=1} S(r/q + β) = μ(q) S(β), from the lab's `ramanujan_coprime`;
* `cauchy_units`: μ(q)²/φ(q) ‖S(β)‖² ≤ ∑_{(r,q)=1} ‖S(r/q + β)‖²;
* `lemma43_core`: log(Q + 1) ‖S(β)‖² ≤ ∑_{q ≤ Q} ∑_{(r,q)=1} ‖S(r/q + β)‖², with the lab's
  `log_le_sum_sqf` for the lower bound log(Q + 1) ≤ ∑_{q ≤ Q} μ(q)²/φ(q).
The integral over β and the disjointness of the arcs are not formalized here.

Unit U-1102, PC run 20261019T1902Z-2936. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own step. Nothing here is progress on Goldbach; Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.LiLiuLemma43

open Complex Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve

/-- `S(α) = ∑_{p ∈ A} w(p) e(pα)`. -/
noncomputable def SA (A : Finset ℕ) (w : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ p ∈ A, w p * e (p * α)

/-- The reduced residues `r < q`, `(r, q) = 1`. -/
def units (q : ℕ) : Finset ℕ := (range q).filter (fun r => Nat.Coprime r q)

lemma card_units (q : ℕ) : (units q).card = q.totient := by
  rw [units, Nat.totient]
  congr 1
  ext r; simp [Nat.coprime_comm]

/-- **The Ramanujan sum identity.** If every `p ∈ A` is prime to `q`, then
`∑_{(r,q)=1} S(r/q + β) = μ(q) S(β)`. -/
theorem twisted_sum (A : Finset ℕ) (w : ℕ → ℂ) {q : ℕ} (hq : 1 ≤ q)
    (hA : ∀ p ∈ A, Nat.Coprime p q) (β : ℝ) :
    ∑ r ∈ units q, SA A w (r / q + β) = (μ q : ℂ) * SA A w β := by
  unfold SA
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hsplit : ∀ r ∈ units q, w p * e (p * ((r : ℝ) / q + β)) =
      w p * e (p * β) * e (((p : ℤ) : ℝ) * r / q) := by
    intro r _
    rw [show (p : ℝ) * ((r : ℝ) / q + β) = ((p : ℤ) : ℝ) * r / q + p * β by
      push_cast; ring, e_add]
    ring
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hA p hp)
  have := LeanLab.PNTPort.Vinogradov.ramanujan_coprime hq hcop
  rw [show ∑ r ∈ units q, e (((p : ℤ) : ℝ) * r / q) =
      ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), e (((p : ℤ) : ℝ) * r / q) from rfl,
    this]
  ring

/-- **Cauchy's inequality over the reduced residues.** -/
theorem cauchy_units (A : Finset ℕ) (w : ℕ → ℂ) {q : ℕ} (hq : 1 ≤ q)
    (hA : ∀ p ∈ A, Nat.Coprime p q) (β : ℝ) :
    ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) * ‖SA A w β‖ ^ 2 ≤
      ∑ r ∈ units q, ‖SA A w (r / q + β)‖ ^ 2 := by
  have htot : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have h1 : ‖(μ q : ℂ) * SA A w β‖ ≤ ∑ r ∈ units q, ‖SA A w (r / q + β)‖ := by
    rw [← twisted_sum A w hq hA β]; exact norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := units q) (f := fun r => ‖SA A w (r / q + β)‖)
  rw [card_units] at h2
  have h3 : ‖(μ q : ℂ) * SA A w β‖ ^ 2 = ((μ q : ℝ)) ^ 2 * ‖SA A w β‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [show ((μ q : ℂ)) = (((μ q : ℝ)) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have h4 : ((μ q : ℝ)) ^ 2 * ‖SA A w β‖ ^ 2 ≤
      (q.totient : ℝ) * ∑ r ∈ units q, ‖SA A w (r / q + β)‖ ^ 2 := by
    rw [← h3]
    calc ‖(μ q : ℂ) * SA A w β‖ ^ 2 ≤ (∑ r ∈ units q, ‖SA A w (r / q + β)‖) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _) h1
      _ ≤ _ := by exact_mod_cast h2
  rw [div_mul_eq_mul_div, div_le_iff₀ htot]
  linarith

/-- For squarefree `q`, `μ(q)²/φ(q) = ∏_{p ∣ q} 1/(p - 1)`. -/
lemma mu_sq_div_totient_sqf {q : ℕ} (hq : Squarefree q) :
    ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hmu : ((μ q : ℝ)) ^ 2 = 1 := by
    rw [moebius_apply_of_squarefree hq]; push_cast
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hprod : ∏ p ∈ q.primeFactors, p = q := Nat.prod_primeFactors_of_squarefree hq
  have htm := Nat.totient_mul_prod_primeFactors q
  rw [hprod] at htm
  have htot : q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    exact Nat.eq_of_mul_eq_mul_right hqpos (htm.trans (mul_comm _ _))
  rw [hmu, htot]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have := (Nat.prime_of_mem_primeFactors hp).one_le
  rw [Nat.cast_sub this]; simp

/-- **The arithmetic core of Li-Liu Lemma 4.3.** For a finite set `A` of primes all above `Q`
and any weights, `log(Q + 1) ‖S(β)‖² ≤ ∑_{q ≤ Q} ∑_{(r,q)=1} ‖S(r/q + β)‖²`. -/
theorem lemma43_core (A : Finset ℕ) (w : ℕ → ℂ) (Q : ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ Q < p) (β : ℝ) :
    Real.log ((Q : ℝ) + 1) * ‖SA A w β‖ ^ 2 ≤
      ∑ q ∈ Icc 1 Q, ∑ r ∈ units q, ‖SA A w (r / q + β)‖ ^ 2 := by
  have hcop : ∀ q ∈ Icc 1 Q, ∀ p ∈ A, Nat.Coprime p q := by
    intro q hq p hp
    rw [Finset.mem_Icc] at hq
    apply (Nat.Prime.coprime_iff_not_dvd (hA p hp).1).mpr
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    have := (hA p hp).2
    omega
  have hlog := log_le_sum_sqf Q
  have hsqf : ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) ≤
      ∑ q ∈ Icc 1 Q, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro q _
    split_ifs with h
    · rw [mu_sq_div_totient_sqf h]
    · positivity
  have hS : 0 ≤ ‖SA A w β‖ ^ 2 := by positivity
  calc Real.log ((Q : ℝ) + 1) * ‖SA A w β‖ ^ 2
      ≤ (∑ q ∈ Icc 1 Q, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ)) * ‖SA A w β‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hlog.trans hsqf) hS
    _ = ∑ q ∈ Icc 1 Q, ((μ q : ℝ)) ^ 2 / (q.totient : ℝ) * ‖SA A w β‖ ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        exact cauchy_units A w (Finset.mem_Icc.mp hq).1 (hcop q hq) β

/-- Vacuity: the hypothesis holds for `A = {5, 7}`, `Q = 4`. -/
theorem lemma43_vacuity : ∀ p ∈ ({5, 7} : Finset ℕ), p.Prime ∧ 4 < p := by
  decide

end LeanLab.Linnik.LiLiuLemma43
