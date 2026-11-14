module

public import LeanLab.RieselVaughan1983.Lemma12Delta
public import LeanLab.RieselVaughan1983.Euler23

/-!
P0032 Riesel-Vaughan 1983, display (8.16), page 65: the sum (8.10) regrouped by conductor,
  Φ_k = ½ C Σ_{q ≤ w} μ(q) f(q) Σ*_{χ mod q} χ(−1)|S_k(χ)|²,
with Σ* over primitive characters. Proved as the limit of the lab's partial sums `Delta.PhiD`.
Unit U-1241, PC run 20261020T1503Z-30533. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Route: each χ mod d with conductor q ≤ w is `changeLevel` of exactly one primitive ψ mod q,
with the same primitive character, so the inner sum of (8.10) at d is Σ_{q ∣ d, q ≤ w} P(q);
swapping the finite sums leaves Σ_{q ≤ w} P(q) Σ_{d ≤ D, q ∣ d, 2 ∤ d} μ(d)/φ(d)², and the inner
sums tend to ½ C μ(q) f(q) by (2.3), `Euler23.eq23`.

What is here, all PROVED unconditional:
* `Pq`: P(q) = Σ_{ψ mod q primitive} ψ*(−1)|S_k(ψ*)|²; `Pq_eq_plain` shows ψ* may be read as ψ.
* `fiber_eq`: Σ_{χ mod d, d* = q} χ*(−1)|S_k(χ*)|² = P(q) for q ∣ d.
* `charSmallP_eq_sum`: the inner sum of (8.10) is Σ_{q ∣ d, q ≤ w} P(q).
* `eq23_all`: (2.3) for every q ≥ 1, value 0 unless q is odd and squarefree.
* `phiD_eq`: Φ_k^{(D)} = Σ_{q ≤ w} P(q) Σ_{d ≤ D} [q ∣ d, 2 ∤ d] μ(d)/φ(d)².
* `eq816`: **(8.16)**, Φ_k^{(D)} → ½ C Σ_{q ≤ w} μ(q) f(q) P(q) as D → ∞.
KNOWN mathematics, the paper's route.
-/

@[expose] public section

open Finset Real ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Eq816

open LeanLab.RieselVaughan1983.Delta LeanLab.RieselVaughan1983.Euler23

/-- `P(q) = Σ_{ψ mod q primitive} ψ*(−1)|S_k(ψ*)|²`, zero at `q = 0`. -/
def Pq (y : ℝ) (k : ℕ) (q : ℕ) : ℂ :=
  if h : q ≠ 0 then
    haveI : NeZero q := ⟨h⟩
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ => ψ.conductor = q),
      ψ.primitiveCharacter (-1) * ((‖Spsi y k ψ.primitiveCharacter‖ ^ 2 : ℝ) : ℂ)
  else 0

/-- For a primitive `ψ`, `ψ*` agrees with `ψ` everywhere. -/
lemma prim_apply_self {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive)
    (a : ℤ) : ψ.primitiveCharacter a = ψ a := by
  by_cases ha : IsCoprime a q
  · exact ψ.primitiveCharacter_apply_of_isCoprime ha
  · have hc : ψ.conductor = q := hψ
    rw [(ψ.apply_eq_zero_iff a).mpr ha, (ψ.primitiveCharacter.apply_eq_zero_iff a).mpr]
    rwa [hc]

/-- The plain form of `P(q)`: `Σ_{ψ mod q primitive} ψ(−1)|S_k(ψ)|²`. -/
theorem Pq_eq_plain (y : ℝ) (k : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Pq y k q = haveI : NeZero q := ⟨hq⟩
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ => ψ.conductor = q),
        ψ (-1) * ((‖Spsi y k ψ‖ ^ 2 : ℝ) : ℂ) := by
  haveI : NeZero q := ⟨hq⟩
  unfold Pq
  rw [dif_pos hq]
  apply sum_congr rfl
  intro ψ hψ
  rw [mem_filter] at hψ
  have h1 : ψ.primitiveCharacter (-1) = ψ (-1) := by
    have := prim_apply_self hψ.2 (-1); simpa using this
  have h2 : Spsi y k ψ.primitiveCharacter = Spsi y k ψ := by
    unfold Spsi
    apply sum_congr rfl
    intro p _
    have := prim_apply_self hψ.2 (p : ℤ); simpa using this
  rw [h1, h2]

/-- The summand of (8.10) at a character `χ`. -/
def F (y : ℝ) (k : ℕ) {d : ℕ} (χ : DirichletCharacter ℂ d) : ℂ :=
  χ.primitiveCharacter (-1) * ((‖Spsi y k χ.primitiveCharacter‖ ^ 2 : ℝ) : ℂ)

/-- The characters mod `d` of conductor `q ∣ d` are the lifts of the primitive ones mod `q`. -/
theorem fiber_eq (y : ℝ) (k : ℕ) {d q : ℕ} [NeZero d] (hqd : q ∣ d) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.conductor = q), F y k χ =
      Pq y k q := by
  have hq : q ≠ 0 := by
    rintro rfl; exact NeZero.ne d (Nat.eq_zero_of_zero_dvd hqd)
  haveI : NeZero q := ⟨hq⟩
  unfold Pq
  rw [dif_pos hq]
  symm
  apply sum_bij (fun ψ _ => DirichletCharacter.changeLevel hqd ψ)
  · intro ψ hψ
    rw [mem_filter] at hψ ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [DirichletCharacter.conductor_changeLevel]
    exact hψ.2
  · intro ψ1 _ ψ2 _ h
    exact DirichletCharacter.changeLevel_injective hqd h
  · intro χ hχ
    rw [mem_filter] at hχ
    have hf : χ.FactorsThrough q := by
      have := χ.factorsThrough_conductor
      rwa [hχ.2] at this
    obtain ⟨_, χ₀, hχ₀⟩ := hf
    refine ⟨χ₀, ?_, hχ₀.symm⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    show χ₀.conductor = q
    rw [← DirichletCharacter.conductor_changeLevel χ₀ hqd, ← hχ₀, hχ.2]
  · intro ψ _
    unfold F
    have key : ∀ a : ℤ, (DirichletCharacter.changeLevel hqd ψ).primitiveCharacter a =
        ψ.primitiveCharacter a := fun a =>
      DirichletCharacter.primitiveCharacter_changeLevel_apply hqd ψ a
    have h1 := key (-1)
    push_cast at h1
    have h2 : Spsi y k (DirichletCharacter.changeLevel hqd ψ).primitiveCharacter =
        Spsi y k ψ.primitiveCharacter := by
      unfold Spsi
      apply sum_congr rfl
      intro p _
      have := key (p : ℤ); simpa using this
    rw [h1, h2]

/-- The inner sum of (8.10) at `d ≠ 0` is `Σ_{q ∣ d, q ≤ w} P(q)`. -/
theorem charSmallP_eq_sum (y : ℝ) (k : ℕ) (w : ℝ) {d : ℕ} (hd : d ≠ 0) :
    charSmallP y k w d = ∑ q ∈ d.divisors.filter (fun q : ℕ => (q : ℝ) ≤ w), Pq y k q := by
  haveI : NeZero d := ⟨hd⟩
  unfold charSmallP
  rw [dif_pos hd]
  have hmaps : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter
      (fun χ => ¬ w < (χ.conductor : ℝ)),
      χ.conductor ∈ d.divisors.filter (fun q : ℕ => (q : ℝ) ≤ w) := by
    intro χ hχ
    rw [mem_filter] at hχ ⊢
    exact ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hd⟩, not_lt.mp hχ.2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro q hq
  rw [mem_filter, Nat.mem_divisors] at hq
  rw [← fiber_eq y k hq.1.1, filter_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext χ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; refine ⟨?_, h⟩; rw [h]; exact not_lt.mpr hq.2

/-- (2.3) for every `q ≥ 1`: zero unless `q` is odd and squarefree. -/
theorem eq23_all {q : ℕ} (hq : q ≠ 0) :
    HasSum (T q) ((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ q : ℤ) : ℝ) *
      LeanLab.RieselVaughan1983.Lemma13Max.fq q) := by
  by_cases h : Odd q ∧ Squarefree q
  · exact eq23 h.1 h.2
  · have hf : LeanLab.RieselVaughan1983.Lemma13Max.fq q = 0 := by
      unfold LeanLab.RieselVaughan1983.Lemma13Max.fq; rw [if_neg h]
    rw [hf, mul_zero]
    convert hasSum_zero with d
    unfold T
    split_ifs with hd
    · obtain ⟨hqd, hodd⟩ := hd
      have hqo : Odd q := Odd.of_dvd_nat hodd hqd
      have hns : ¬ Squarefree q := fun hs => h ⟨hqo, hs⟩
      have hnd : ¬ Squarefree d := fun hs => hns (hs.squarefree_of_dvd hqd)
      rw [moebius_eq_zero_of_not_squarefree hnd]; simp
    · rfl

/-- The partial sums of (2.3) are the inner sums of (8.10) after the swap. -/
lemma sum_T_eq (q D : ℕ) :
    ∑ d ∈ range (D + 1), T q d =
      ∑ d ∈ (Icc 1 D).filter Odd, if q ∣ d then ((μ d : ℤ) : ℝ) / (d.totient : ℝ) ^ 2 else 0 := by
  unfold T
  rw [sum_ite, sum_const_zero, add_zero, sum_ite, sum_const_zero, add_zero, filter_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext d
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have : d % 2 = 1 := Nat.odd_iff.mp h3
    exact ⟨⟨by omega, by omega⟩, h3, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h4, h3⟩

/-- `Φ_k^{(D)} = Σ_{q ≤ w} P(q) Σ_{d ≤ D} [q ∣ d, 2 ∤ d] μ(d)/φ(d)²` for `w ≥ 0`. -/
theorem phiD_eq (y : ℝ) (k : ℕ) {w : ℝ} (hw : 0 ≤ w) (D : ℕ) :
    PhiD y k w D = ∑ q ∈ Icc 1 ⌊w⌋₊,
      (((∑ d ∈ range (D + 1), T q d : ℝ)) : ℂ) * Pq y k q := by
  unfold PhiD
  have hin : ∀ d ∈ (Icc 1 D).filter Odd, charSmallP y k w d =
      ∑ q ∈ Icc 1 ⌊w⌋₊, if q ∣ d then Pq y k q else 0 := by
    intro d hd
    rw [mem_filter, mem_Icc] at hd
    have hd0 : d ≠ 0 := by omega
    rw [charSmallP_eq_sum y k w hd0, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext q
    simp only [mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨⟨hqd, -⟩, hqw⟩
      have hq0 : q ≠ 0 := by rintro rfl; exact hd0 (Nat.eq_zero_of_zero_dvd hqd)
      exact ⟨⟨by omega, Nat.le_floor hqw⟩, hqd⟩
    · rintro ⟨⟨h1, h2⟩, hqd⟩
      exact ⟨⟨hqd, hd0⟩, (Nat.le_floor_iff hw).mp h2⟩
  rw [sum_congr rfl (fun d hd => by rw [hin d hd])]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [sum_T_eq, Complex.ofReal_sum, sum_mul]
  apply sum_congr rfl
  intro d _
  split_ifs
  · push_cast; ring
  · simp

/-- **(8.16)**, page 65: `Φ_k^{(D)} → ½ C Σ_{q ≤ w} μ(q) f(q) P(q)` as `D → ∞`. -/
theorem eq816 (y : ℝ) (k : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun D => PhiD y k w D) atTop
      (𝓝 (∑ q ∈ Icc 1 ⌊w⌋₊, ((((1 / 2) * LeanLab.RieselVaughan1983.Ctw *
        ((μ q : ℤ) : ℝ) * LeanLab.RieselVaughan1983.Lemma13Max.fq q : ℝ)) : ℂ) * Pq y k q)) := by
  simp_rw [phiD_eq y k hw]
  apply tendsto_finset_sum
  intro q hq
  rw [mem_Icc] at hq
  have hq0 : q ≠ 0 := by omega
  have h1 := (eq23_all hq0).tendsto_sum_nat
  have h2 : Tendsto (fun D => ∑ d ∈ range (D + 1), T q d) atTop
      (𝓝 ((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ q : ℤ) : ℝ) *
        LeanLab.RieselVaughan1983.Lemma13Max.fq q)) :=
    (tendsto_add_atTop_iff_nat 1).mpr h1
  exact ((Complex.continuous_ofReal.tendsto _).comp h2).mul_const _

end LeanLab.RieselVaughan1983.Eq816
