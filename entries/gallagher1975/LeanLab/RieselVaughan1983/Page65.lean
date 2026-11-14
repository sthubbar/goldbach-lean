module

public import LeanLab.RieselVaughan1983.Lemma13Red
public import LeanLab.RieselVaughan1983.GaussImprim

/-!
P0032 Riesel-Vaughan 1983, Lemma 13, page 65 and the top of page 66: the lower bound for the
additive sums by the primitive character sums, the passage from (8.17) to the display before
(8.18), and (8.18) itself from (8.17) and Montgomery-Vaughan's Lemmas 3 and 8.
Unit U-6703, CLOUD 20261020T1816Z-cloud48, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

Page 65: with S(α) = Σ_{p ∈ I_k} e(αp), the paper shows
  Σ_{(a, q) = 1} |S(a/q)|² = Σ_{r ∣ q, (q/r, r) = 1} μ(q/r)² r/φ(q) Σ*_{χ mod r}|S_k(χ)|²,
from φ(q) Σ_a |S(a/q)|² = Σ_χ |τ(χ)|²|S_k(χ)|² and |τ(χ)|² = q* when q/q* is squarefree and
prime to q*. Here only the direction ≥ is proved, which is the one (8.18) needs: the characters
off those hypotheses are dropped, so the zero case |τ(χ)|² = 0 is never used. Then (8.17) with
z² = 2N_k/3 from (8.6) and the swap q = rm give, page 65 last display,
  Σ_{r ≤ z} r/φ(r) (Σ_{m ≤ z/r, (m, r) = 1} μ(m)²/φ(m) · 1/(1 + rmz⁻¹)) Σ*_{χ mod r}|S_k(χ)|² ≤ S_k N_k,
and with Montgomery-Vaughan's Lemmas 3 and 8, page 66, the bracket times r/φ(r) exceeds
0.361 + log(z/r) for r ≤ w, which gives (8.18).

DECISION: Montgomery-Vaughan's paper is not in papers/, so their (2.6) is cited in the form the
page states it for I_k, display (8.17), `Eq817`, and their Lemmas 3 and 8 in the form the page
states them, `MVLemma38`. Both are NOT proved here.

What is here:
PROVED unconditional:
* `fiber_sq`: Σ_{χ mod q, q* = r}|Σ_{p ∈ P} χ(p)|² = Σ*_{ψ mod r}|Σ_{p ∈ P} ψ(p)|² for P prime to q.
* `page65_mul`, `page65_lower`: the page 65 identity in the direction ≥, for any finite P prime to q.
* `sum_swap`: Σ_{q ≤ Z} Σ_{r ∣ q, (q/r, r) = 1} h(r, q/r) = Σ_{r ≤ Z} Σ_{m, rm ≤ Z, (m, r) = 1} h(r, m).
* `weighted_char_le`: the last display of page 65 from any weighted bound of the shape (8.17).
* `Qr_eq_primSq`, `Qr_one`, `Pset_coprime`: bookkeeping for the paper's objects.
CONDITIONAL, counted apart:
* `eq817_char`: the last display of page 65, CONDITIONAL ON `Eq817`.
* `eq818_of`: (8.18), Lemma13Red.Eq818, CONDITIONAL ON `Eq817` and `MVLemma38`.
* `lemma13_of_817_38`: Lemma13P CONDITIONAL ON `Eq817` and `MVLemma38`.
* `theorem_of_lemma5_817_38`: the 18-prime Theorem CONDITIONAL ON Lemma 5 at five rows, Lemma 6,
  (2.30), (2.31), Rosser-Schoenfeld (3.3), `Eq817` and `MVLemma38`.
KNOWN mathematics, the paper's route.
-/

@[expose] public section

open Finset DirichletCharacter ZMod AddChar Real
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Page65

open LeanLab.RieselVaughan1983.GaussImprim LeanLab.RieselVaughan1983.Delta
  LeanLab.RieselVaughan1983.Euler23 LeanLab.RieselVaughan1983.Eq816
  LeanLab.RieselVaughan1983.Xi LeanLab.RieselVaughan1983.Lemma13Red

/-! ### Page 65, generic in the finite set `P` of primes -/

/-- `Σ_{a mod q, (a, q) = 1} |Σ_{p ∈ P} e(ap/q)|²`, the inner sum of (8.17) with `S(a/q)`,
zero at `q = 0`. -/
def addSq (P : Finset ℕ) (q : ℕ) : ℝ :=
  if h : q ≠ 0 then
    haveI : NeZero q := ⟨h⟩
    ∑ a ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖∑ p ∈ P, stdAddChar (a * (p : ZMod q))‖ ^ 2
  else 0

/-- `Σ*_{χ mod r}|Σ_{p ∈ P} χ(p)|²` over the primitive characters mod `r`, zero at `r = 0`. -/
def primSq (P : Finset ℕ) (r : ℕ) : ℝ :=
  if h : r ≠ 0 then
    haveI : NeZero r := ⟨h⟩
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
      ‖∑ p ∈ P, ψ (p : ZMod r)‖ ^ 2
  else 0

lemma primSq_nonneg (P : Finset ℕ) (r : ℕ) : 0 ≤ primSq P r := by
  unfold primSq; split_ifs
  · exact sum_nonneg fun _ _ => sq_nonneg _
  · exact le_rfl

/-- The characters mod `q` of conductor `r` are the lifts of the primitive ones mod `r`, and
they agree with them on `P` when `P` is prime to `q`. -/
theorem fiber_sq (P : Finset ℕ) {q r : ℕ} [NeZero q] (hrq : r ∣ q)
    (hP : ∀ p ∈ P, p.Coprime q) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = r),
      ‖∑ p ∈ P, χ (p : ZMod q)‖ ^ 2 = primSq P r := by
  have hr : r ≠ 0 := by
    rintro rfl; exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hrq)
  have : NeZero r := ⟨hr⟩
  unfold primSq
  rw [dif_pos hr]
  symm
  apply sum_bij (fun ψ _ => changeLevel hrq ψ)
  · intro ψ hψ
    rw [mem_filter] at hψ ⊢
    exact ⟨mem_univ _, by rw [conductor_changeLevel]; exact hψ.2⟩
  · intro ψ1 _ ψ2 _ h
    exact changeLevel_injective hrq h
  · intro χ hχ
    rw [mem_filter] at hχ
    have hf : χ.FactorsThrough r := by
      have := χ.factorsThrough_conductor
      rwa [hχ.2] at this
    obtain ⟨_, χ₀, hχ₀⟩ := hf
    refine ⟨χ₀, ?_, hχ₀.symm⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← conductor_changeLevel χ₀ hrq, ← hχ₀, hχ.2]
  · intro ψ _
    congr 2
    refine sum_congr rfl fun p hp => ?_
    have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr (hP p hp)
    have e := changeLevel_eq_cast_of_dvd ψ hrq hu.unit
    rw [hu.unit_spec] at e
    rw [e, ZMod.cast_natCast hrq]

/-- **Page 65, the identity before "Therefore", direction ≥**, times `φ(q)`: for `q ≥ 1` and
a finite `P` prime to `q`,
`Σ_{r ∣ q, (q/r, r) = 1} μ(q/r)² r Σ*_{χ mod r}|Σ_{p ∈ P} χ(p)|² ≤ φ(q) Σ_{(a, q) = 1}|S(a/q)|²`.
Route: `totient_mul_sum_additive_eq`, keep the χ with `q/q*` squarefree and prime to `q*`,
where `|τ(χ)|² = q*` by `norm_sq_gaussSum_eq_conductor`, and group them by `q*`. -/
theorem page65_mul (P : Finset ℕ) {q : ℕ} (hq : q ≠ 0) (hP : ∀ p ∈ P, p.Coprime q) :
    ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * primSq P r ≤ (q.totient : ℝ) * addSq P q := by
  have : NeZero q := ⟨hq⟩
  have hPu : ∀ p ∈ P, IsUnit (p : ZMod q) := fun p hp =>
    (ZMod.isUnit_iff_coprime p q).mpr (hP p hp)
  unfold addSq
  rw [dif_pos hq, totient_mul_sum_additive_eq P hPu]
  set good : DirichletCharacter ℂ q → Prop :=
    fun χ => Squarefree (q / χ.conductor) ∧ χ.conductor.Coprime (q / χ.conductor)
  calc ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * primSq P r
      = ∑ r ∈ q.divisors.filter (fun r => Squarefree (q / r) ∧ r.Coprime (q / r)),
          ∑ χ ∈ (univ.filter good).filter (fun χ => χ.conductor = r),
            ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ p ∈ P, χ (p : ZMod q)‖ ^ 2 := by
        rw [sum_filter, sum_filter]
        refine sum_congr rfl fun r hr => ?_
        have hrq : r ∣ q := Nat.dvd_of_mem_divisors hr
        by_cases hsq : Squarefree (q / r)
        · by_cases hc : r.Coprime (q / r)
          · rw [if_pos hc.symm, if_pos ⟨hsq, hc⟩, filter_filter]
            have hf : univ.filter (fun χ : DirichletCharacter ℂ q => good χ ∧ χ.conductor = r) =
                univ.filter (fun χ => χ.conductor = r) := by
              ext χ; simp only [mem_filter, mem_univ, true_and, good]
              constructor
              · exact fun h => h.2
              · intro h; refine ⟨?_, h⟩; rw [h]; exact ⟨hsq, hc⟩
            rw [hf, ← fiber_sq P hrq hP, mul_sum]
            refine sum_congr rfl fun χ hχ => ?_
            rw [mem_filter] at hχ
            have hg : good χ := by simp only [good]; rw [hχ.2]; exact ⟨hsq, hc⟩
            have hm : ((μ (q / r) : ℤ) : ℝ) ^ 2 = 1 := by
              exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
            rw [norm_sq_gaussSum_eq_conductor χ hg.1 hg.2, hχ.2, hm]
            ring
          · rw [if_neg (fun h => hc h.symm), if_neg (fun h => hc h.2)]
        · have hm0 : ((μ (q / r) : ℤ) : ℝ) = 0 := by
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
          simp [hsq]
      _ = ∑ χ ∈ univ.filter good,
            ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ p ∈ P, χ (p : ZMod q)‖ ^ 2 := by
        refine sum_fiberwise_of_maps_to
          (g := fun χ : DirichletCharacter ℂ q => χ.conductor) (fun χ hχ => ?_) _
        rw [mem_filter] at hχ ⊢
        exact ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq⟩, hχ.2⟩
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))


/-- **Page 65, the identity before "Therefore", direction ≥**, the paper's form:
`Σ_{r ∣ q, (q/r, r) = 1} μ(q/r)² r/φ(q) Σ*_{χ mod r}|S(χ)|² ≤ Σ_{a = 1, (a, q) = 1}^q |S(a/q)|²`. -/
theorem page65_lower (P : Finset ℕ) {q : ℕ} (hq : q ≠ 0) (hP : ∀ p ∈ P, p.Coprime q) :
    ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r / q.totient * primSq P r ≤ addSq P q := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have e : ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r / q.totient * primSq P r =
      (q.totient : ℝ)⁻¹ * ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * primSq P r := by
    rw [mul_sum]; exact sum_congr rfl fun r _ => by ring
  rw [e, inv_mul_le_iff₀ hφ]
  exact page65_mul P hq hP

/-- The swap `q = r m` of the double sum. -/
theorem sum_swap (Z : ℕ) (h : ℕ → ℕ → ℝ) :
    ∑ q ∈ Icc 1 Z, ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r), h r (q / r) =
      ∑ r ∈ Icc 1 Z, ∑ m ∈ (Icc 1 Z).filter (fun m => r * m ≤ Z ∧ m.Coprime r), h r m := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1 / x.2⟩) (fun x _ => ⟨x.1 * x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, r⟩ hx
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨h1, h2⟩, ⟨hrq, hq0⟩, hc⟩ := hx
    have hr : 0 < r := Nat.pos_of_dvd_of_pos hrq (by omega)
    have hle : r ≤ q := Nat.le_of_dvd (by omega) hrq
    have hm : 0 < q / r := Nat.div_pos hle hr
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, (Nat.div_le_self _ _).trans h2⟩, ?_, hc⟩
    rw [Nat.mul_div_cancel' hrq]; exact h2
  · rintro ⟨r, m⟩ hx
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, hc⟩ := hx
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), h5⟩,
      ⟨Dvd.intro m rfl, Nat.mul_ne_zero (by omega) (by omega)⟩, ?_⟩
    rw [Nat.mul_div_cancel_left _ (by omega)]; exact hc
  · rintro ⟨q, r⟩ hx
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hx
    simp only [Nat.mul_div_cancel' hx.2.1.1]
  · rintro ⟨r, m⟩ hx
    simp only [mem_sigma, mem_Icc, mem_filter] at hx
    simp only [Nat.mul_div_cancel_left _ (show 0 < r by omega)]
  · rintro ⟨q, r⟩ _
    rfl


/-- The inner sum on page 65 after (8.17): `Σ_{m ≤ z/r, (m, r) = 1} μ(m)²/φ(m) · 1/(1 + rmz⁻¹)`. -/
def mSum (r : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ (Icc 1 ⌊z / r⌋₊).filter (fun m => m.Coprime r),
    ((μ m : ℤ) : ℝ) ^ 2 / (m.totient : ℝ) * (1 / (1 + r * m * z⁻¹))

lemma mSum_nonneg (r : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ mSum r z := by
  unfold mSum
  refine sum_nonneg fun m _ => mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
  have : 0 ≤ (r : ℝ) * m * z⁻¹ := by positivity
  positivity

lemma m_range {r : ℕ} (hr : 1 ≤ r) {z : ℝ} (hz : 0 ≤ z) :
    (Icc 1 ⌊z / r⌋₊).filter (fun m => m.Coprime r) =
      (Icc 1 ⌊z⌋₊).filter (fun m => r * m ≤ ⌊z⌋₊ ∧ m.Coprime r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  ext m
  simp only [mem_filter, mem_Icc]
  have key : m ≤ ⌊z / r⌋₊ ↔ r * m ≤ ⌊z⌋₊ := by
    rw [Nat.le_floor_iff (div_nonneg hz hr0.le), Nat.le_floor_iff hz, le_div_iff₀ hr0]
    push_cast; rw [mul_comm]
  rw [key]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, le_trans (Nat.le_mul_of_pos_left m hr) h2⟩, h2, h3⟩
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-- **The step after (8.17)**, generic form: if the weighted large sieve bound
`Σ_{q ≤ z} (N + 3/2 q z)⁻¹ Σ_{(a, q) = 1} |S(a/q)|² ≤ S` holds with `z² = 2N/3`, and every
`p ∈ P` is prime to every `q ≤ z`, then
`Σ_{r ≤ z} r/φ(r) (Σ_{m ≤ z/r, (m, r) = 1} μ(m)²/φ(m) · 1/(1 + rmz⁻¹)) Σ*_{χ mod r}|S(χ)|² ≤ S N`. -/
theorem weighted_char_le (P : Finset ℕ) {z N S : ℝ} (hz : 0 < z) (hN : z ^ 2 = 2 / 3 * N)
    (hP : ∀ p ∈ P, ∀ q ∈ Icc 1 ⌊z⌋₊, p.Coprime q)
    (h817 : ∑ q ∈ Icc 1 ⌊z⌋₊, (N + 3 / 2 * q * z)⁻¹ * addSq P q ≤ S) :
    ∑ r ∈ Icc 1 ⌊z⌋₊, (r : ℝ) / r.totient * mSum r z * primSq P r ≤ S * N := by
  set Z := ⌊z⌋₊
  have hN0 : 0 < N := by nlinarith
  set g : ℕ → ℝ := fun q => 1 / (1 + q * z⁻¹) with hg
  have hg0 : ∀ q : ℕ, 0 ≤ g q := fun q => by simp only [hg]; positivity
  set h : ℕ → ℕ → ℝ := fun r m =>
    g (r * m) * (((μ m : ℤ) : ℝ) ^ 2 * r / ((r * m).totient : ℝ) * primSq P r) with hh
  -- the left side in the (r, m) form
  have e1 : ∑ r ∈ Icc 1 Z, (r : ℝ) / r.totient * mSum r z * primSq P r =
      ∑ r ∈ Icc 1 Z, ∑ m ∈ (Icc 1 Z).filter (fun m => r * m ≤ Z ∧ m.Coprime r), h r m := by
    refine sum_congr rfl fun r hr => ?_
    rw [mem_Icc] at hr
    unfold mSum
    rw [m_range hr.1 hz.le, mul_sum, sum_mul]
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_filter, mem_Icc] at hm
    have hφr : (r.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    have hφm : (m.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    simp only [hh, hg]
    rw [Nat.totient_mul hm.2.2.symm]
    push_cast
    field_simp
  -- the q form
  have e2 : ∑ q ∈ Icc 1 Z, ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r), h r (q / r) =
      ∑ q ∈ Icc 1 Z, g q * ((q.totient : ℝ)⁻¹ * ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * primSq P r) := by
    refine sum_congr rfl fun q _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun r hr => ?_
    rw [mem_filter, Nat.mem_divisors] at hr
    simp only [hh, Nat.mul_div_cancel' hr.1.1]
    ring
  rw [e1, ← sum_swap, e2]
  calc ∑ q ∈ Icc 1 Z, g q * ((q.totient : ℝ)⁻¹ *
          ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
            ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * primSq P r)
      ≤ ∑ q ∈ Icc 1 Z, g q * addSq P q := by
        refine sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (hg0 q)
        rw [mem_Icc] at hq
        have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
        rw [inv_mul_le_iff₀ hφ]
        exact page65_mul P (by omega) fun p hp => hP p hp q (mem_Icc.mpr hq)
    _ = N * ∑ q ∈ Icc 1 Z, (N + 3 / 2 * q * z)⁻¹ * addSq P q := by
        rw [mul_sum]
        refine sum_congr rfl fun q _ => ?_
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        have hd : 0 < N + 3 / 2 * q * z := by positivity
        simp only [hg]
        rw [show N = 3 / 2 * z ^ 2 by linarith]
        field_simp
    _ ≤ N * S := mul_le_mul_of_nonneg_left h817 hN0.le
    _ = S * N := mul_comm _ _


/-! ### The paper's objects -/

/-- `Lemma13Red.Qr` is `primSq` of the primes in `I_k`. -/
lemma Qr_eq_primSq (y : ℝ) (k r : ℕ) : Qr y k r = primSq (Xi.Pset y k) r := rfl

/-- The `r = 1` term: `Σ*_{χ mod 1}|S_k(χ)|² = S_k²`. -/
theorem Qr_one (y : ℝ) (k : ℕ) (hy : 0 ≤ y) : Qr y k 1 = Sk y k ^ 2 := by
  unfold Qr
  rw [dif_pos one_ne_zero]
  have hfil : (univ : Finset (DirichletCharacter ℂ 1)).filter (fun ψ => ψ.conductor = 1) =
      {1} := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    have hψ : ψ = 1 := MulChar.ext' fun a => by rw [char_one_apply, char_one_apply]
    subst hψ
    simp [DirichletCharacter.conductor_one]
  rw [hfil, sum_singleton]
  have hS : Spsi y k (1 : DirichletCharacter ℂ 1) = (#(Xi.Pset y k) : ℂ) := by
    unfold Spsi
    simp [char_one_apply]
  rw [hS, Complex.norm_natCast, card_Pset_eq y k hy]

/-- In the range of Lemma 13 every prime of `I_k` is prime to every `q ≤ z`, since
`z < y/2 < p`. -/
theorem Pset_coprime {y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 10 ^ 7 ≤ y) :
    ∀ p ∈ Xi.Pset y k, ∀ q ∈ Icc 1 ⌊zk y k⌋₊, p.Coprime q := by
  intro p hp q hq
  rw [Xi.Pset, mem_filter] at hp
  rw [mem_Icc] at hq
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k (by linarith)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : zk y k < y / 2 := by
    unfold zk
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  have hz0 : 0 ≤ zk y k := Real.sqrt_nonneg _
  have hq' : (q : ℝ) ≤ zk y k := (Nat.le_floor_iff hz0).mp hq.2
  have hqp : (q : ℝ) < p := by
    have : y / 2 ≤ k * y / 2 := by nlinarith
    linarith [hp.2.2.1]
  have hqp' : q < p := by exact_mod_cast hqp
  rw [Nat.Prime.coprime_iff_not_dvd hp.2.1]
  intro hd
  exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)

/-- **(8.17)**, page 65, cited: by (2.6) of Montgomery and Vaughan, (7.2) and (8.6),
`Σ_{q ≤ z} (N_k + 3/2 qz)⁻¹ Σ_{a = 1, (a, q) = 1}^q |S(a/q)|² ≤ S_k`, `S(α) = Σ_{p ∈ I_k} e(αp)`,
in the range of Lemma 13 with `y = x/202`. NOT proved here. -/
def Eq817 : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    ∑ q ∈ Icc 1 ⌊zk (x / 202) k⌋₊,
        (Nk (x / 202) k + 3 / 2 * q * zk (x / 202) k)⁻¹ * addSq (Xi.Pset (x / 202) k) q ≤
      Sk (x / 202) k

/-- **Montgomery-Vaughan Lemmas 3 and 8 with (8.6)**, page 66, cited: for `1 ≤ r ≤ w`,
`r/φ(r) Σ_{m ≤ z/r, (m, r) = 1} μ(m)²/φ(m) · 1/(1 + rmz⁻¹) > 0.361 + log(z/r)`, in the range of
Lemma 13 with `y = x/202`, `z` and `w = z/100` of (8.6). NOT proved here. -/
def MVLemma38 : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200, ∀ r : ℕ, 1 ≤ r →
    (r : ℝ) ≤ wk (x / 202) k →
      0.361 + Real.log (zk (x / 202) k / r) < (r : ℝ) / r.totient * mSum r (zk (x / 202) k)

lemma z_facts {y : ℝ} {k : ℕ} (hy : 10 ^ 7 ≤ y) :
    0 < zk y k ∧ zk y k ^ 2 = 2 / 3 * Nk y k ∧ 500 ≤ zk y k := by
  obtain ⟨hN1, _⟩ := Nk_bounds y k (by linarith)
  have hN0 : 0 ≤ 2 / 3 * Nk y k := by nlinarith
  refine ⟨Real.sqrt_pos.mpr (by nlinarith), Real.sq_sqrt hN0, ?_⟩
  unfold zk
  rw [Real.le_sqrt (by norm_num) hN0]; nlinarith

/-- **The last display of page 65**, CONDITIONAL ON `Eq817`:
`Σ_{r ≤ z} r/φ(r) (Σ_{m ≤ z/r, (m, r) = 1} μ(m)²/φ(m) · 1/(1 + rmz⁻¹)) Σ*_{χ mod r}|S_k(χ)|² ≤ S_k N_k`. -/
theorem eq817_char (h817 : Eq817) {x : ℝ} (hx : 0 < x) (hL : 350 < Real.log (x / 202))
    {k : ℕ} (hk : k ∈ Icc 1 200) :
    ∑ r ∈ Icc 1 ⌊zk (x / 202) k⌋₊, (r : ℝ) / r.totient * mSum r (zk (x / 202) k) *
        Qr (x / 202) k r ≤ Sk (x / 202) k * Nk (x / 202) k := by
  have hy7 : 10 ^ 7 ≤ x / 202 := y_big (by positivity) hL
  obtain ⟨hz, hN, _⟩ := z_facts (k := k) hy7
  exact weighted_char_le (Xi.Pset (x / 202) k) hz hN
    (Pset_coprime (mem_Icc.mp hk).1 hy7) (h817 x hx hL k hk)

/-- **(8.18)**, page 66, CONDITIONAL ON `Eq817` and `MVLemma38`: `Lemma13Red.Eq818`. The
terms `r = 2, 3, 4` and `w < r ≤ z` are dropped as nonnegative, and the term `r = 1` is
`> (0.361 + log z) S_k²`. -/
theorem eq818_of (h817 : Eq817) (h38 : MVLemma38) : Eq818 := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hy7 : 10 ^ 7 ≤ y := y_big (by positivity) hL
  obtain ⟨hz, _, hz5⟩ := z_facts (k := k) hy7
  have hmain := eq817_char h817 hx hL hk
  simp only [← hydef] at hmain
  set z := zk y k with hzdef
  set c : ℕ → ℝ := fun r => (r : ℝ) / r.totient * mSum r z with hc
  have hc0 : ∀ r, 0 ≤ c r := fun r =>
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mSum_nonneg r hz.le)
  have hw : wk y k = z / 100 := wk_eq y k
  set W := ⌊wk y k⌋₊ with hWdef
  set Z := ⌊z⌋₊ with hZdef
  have hWZ : W ≤ Z := Nat.floor_le_floor (by rw [hw]; linarith)
  have h1Z : 1 ≤ Z := Nat.le_floor (by push_cast; linarith)
  have hsub : insert 1 (Icc 5 W) ⊆ Icc 1 Z := by
    intro r hr
    rw [mem_insert, mem_Icc] at hr
    rw [mem_Icc]
    rcases hr with rfl | hr
    · exact ⟨le_rfl, h1Z⟩
    · omega
  have hnot : 1 ∉ Icc 5 W := by simp
  have hle := sum_le_sum_of_subset_of_nonneg hsub (f := fun r => c r * Qr y k r)
    (fun r _ _ => mul_nonneg (hc0 r) (Qr_nonneg y k r))
  rw [sum_insert hnot] at hle
  have hS0 : 0 ≤ Sk y k ^ 2 := sq_nonneg _
  have h1 : Sk y k ^ 2 * (0.361 + Real.log z) ≤ c 1 * Qr y k 1 := by
    rw [Qr_one y k (by linarith)]
    have := h38 x hx hL k hk 1 le_rfl (by rw [← hydef, hw]; push_cast; linarith)
    simp only [← hydef, ← hzdef, Nat.cast_one, div_one] at this
    have hc1 : c 1 = 1 / ((Nat.totient 1 : ℕ) : ℝ) * mSum 1 z := by
      simp only [hc, Nat.cast_one]
    rw [hc1]
    nlinarith
  have hr : ∑ r ∈ Icc 5 W, (0.361 + Real.log (z / r)) * Qr y k r ≤
      ∑ r ∈ Icc 5 W, c r * Qr y k r := by
    refine sum_le_sum fun r hr => mul_le_mul_of_nonneg_right ?_ (Qr_nonneg y k r)
    rw [mem_Icc] at hr
    have hrw : (r : ℝ) ≤ wk y k :=
      (Nat.le_floor_iff (by rw [hw]; linarith)).mp hr.2
    have := h38 x hx hL k hk r (by omega) (by rw [← hydef]; exact hrw)
    simp only [← hydef, ← hzdef] at this
    exact this.le
  have hmain' : ∑ r ∈ Icc 1 Z, c r * Qr y k r ≤ Sk y k * Nk y k := hmain
  show ∑ r ∈ Icc 5 W, (0.361 + Real.log (z / r)) * Qr y k r ≤
    Sk y k * Nk y k - Sk y k ^ 2 * (0.361 + Real.log z)
  linarith

/-- **Lemma 13**, page 64, CONDITIONAL ON `Eq817` and `MVLemma38`. -/
theorem lemma13_of_817_38 (h817 : Eq817) (h38 : MVLemma38) : Lemma13P :=
  lemma13_of_818 (eq818_of h817 h38)

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at five rows, Lemma 6 (i) and (ii), (2.30) and (2.31), Rosser-Schoenfeld (3.3), (8.17)
and Montgomery-Vaughan's Lemmas 3 and 8. -/
theorem theorem_of_lemma5_817_38 (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h5 : Lemma5Neg) (h6 : Lemma6i) (h6' : Lemma6ii) (hTab : Table230) (hRS : RS33)
    (h817 : Eq817) (h38 : MVLemma38) : Theorem :=
  theorem_of_lemma5_818 h24 h42 h278 h396 h5 h6 h6' hTab hRS (eq818_of h817 h38)

end LeanLab.RieselVaughan1983.Page65
