module

public import LeanLab.PNTPort.BV.TypeI

/-!
lab proof, AI wrote this file, known mathematics, no cited input

`S4_eq_blocks`: the Vaughan Type II sum `S₄` as a sum of dyadic blocks
`∑_{M < t ≤ 2M} ∑_{v < r ≤ v + N/M} [t r ≤ x] Λ(t) g_v(r) χ(t r)`, `M = u 2^j`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction

variable {q : ℕ}

/-- The summand of the blocks. -/
noncomputable def gS4 (x : ℝ) (v : ℕ) (χ : DirichletCharacter ℂ q) (t r : ℕ) : ℂ :=
  if ((t * r : ℕ) : ℝ) ≤ x then (vonMangoldt t : ℂ) * (gV v r : ℂ) * χ ((t * r : ℕ) : ZMod q)
  else 0

/-- One dyadic block. -/
noncomputable def blk (x : ℝ) (v M N₂ : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ Ioc M (M + M), ∑ r ∈ Ioc v (v + N₂), gS4 x v χ t r

lemma gS4_eq_zero {x : ℝ} (_hx : 0 ≤ x) {v : ℕ} (χ : DirichletCharacter ℂ q) {t r : ℕ}
    (h : ⌊x⌋₊ < t * r) : gS4 x v χ t r = 0 := by
  unfold gS4
  rw [ite_eq_right_iff]
  intro h'
  exfalso
  have := Nat.le_floor h'
  omega

lemma S4_eq_Ioc (x : ℝ) (hx : 0 ≤ x) (u v : ℕ) (χ : DirichletCharacter ℂ q) :
    S4 x u v χ = ∑ t ∈ Ioc u ⌊x⌋₊, ∑ r ∈ Ioc v (v + ⌊x⌋₊), gS4 x v χ t r := by
  set N := ⌊x⌋₊
  unfold S4
  rw [sum_conv_eq χ (fun p => if u < p.1 ∧ v < p.2 then vonMangoldt p.1 * gV v p.2 else 0) N]
  have hset : Ioc u N = (Icc 1 N).filter (fun t => u < t) := by
    ext t; simp only [mem_Ioc, mem_filter, mem_Icc]; omega
  rw [hset, sum_filter]
  refine sum_congr rfl fun t ht => ?_
  have ht1 : 1 ≤ t := (mem_Icc.1 ht).1
  split_ifs with hut
  · have hs2 : (Icc 1 (N / t)).filter (fun r => v < r) =
        (Ioc v (v + N)).filter (fun r => t * r ≤ N) := by
      ext r
      simp only [mem_filter, mem_Icc, mem_Ioc, Nat.le_div_iff_mul_le ht1]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h3, ?_⟩, by rw [mul_comm]; exact h2⟩
        have : r ≤ r * t := Nat.le_mul_of_pos_right r ht1
        omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by omega, by rw [mul_comm]; exact h3⟩, h1⟩
    have e1 : ∑ r ∈ Icc 1 (N / t),
        (((if u < (t, r).1 ∧ v < (t, r).2 then vonMangoldt (t, r).1 * gV v (t, r).2 else 0 : ℝ)
          : ℂ) * χ (t : ZMod q) * χ (r : ZMod q)) =
        ∑ r ∈ (Icc 1 (N / t)).filter (fun r => v < r),
          (vonMangoldt t : ℂ) * (gV v r : ℂ) * χ ((t * r : ℕ) : ZMod q) := by
      rw [sum_filter]
      refine sum_congr rfl fun r _ => ?_
      simp only [hut, true_and]
      split_ifs
      · push_cast; rw [map_mul]; ring
      · simp
    have e2 : ∑ r ∈ Ioc v (v + N), gS4 x v χ t r =
        ∑ r ∈ (Ioc v (v + N)).filter (fun r => t * r ≤ N),
          (vonMangoldt t : ℂ) * (gV v r : ℂ) * χ ((t * r : ℕ) : ZMod q) := by
      rw [sum_filter]
      refine sum_congr rfl fun r _ => ?_
      unfold gS4
      have : ((t * r : ℕ) : ℝ) ≤ x ↔ t * r ≤ N := (Nat.le_floor_iff hx).symm
      simp only [this]
    rw [e1, e2, hs2]
  · apply sum_eq_zero
    intro r _
    simp [hut]

lemma sum_Ioc_dyadic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (u J : ℕ) :
    ∑ t ∈ Ioc u (u * 2 ^ J), f t = ∑ j ∈ range J, ∑ t ∈ Ioc (u * 2 ^ j) (u * 2 ^ j + u * 2 ^ j), f t := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ← ih, show u * 2 ^ (J + 1) = u * 2 ^ J + u * 2 ^ J by ring]
    rw [sum_Ioc_consecutive _ (by nlinarith [Nat.one_le_two_pow (n := J)]) (by omega)]

/-- **The dyadic block decomposition of `S₄`.** -/
theorem S4_eq_blocks {x : ℝ} (hx : 0 ≤ x) {u : ℕ} (hu : 1 ≤ u) (v : ℕ) {J : ℕ}
    (hJ : ⌊x⌋₊ ≤ u * 2 ^ J) (χ : DirichletCharacter ℂ q) :
    S4 x u v χ = ∑ j ∈ range J, blk x v (u * 2 ^ j) (⌊x⌋₊ / (u * 2 ^ j)) χ := by
  set N := ⌊x⌋₊
  rw [S4_eq_Ioc x hx u v χ]
  have hsub : Ioc u N ⊆ Ioc u (u * 2 ^ J) := Ioc_subset_Ioc le_rfl hJ
  rw [sum_subset hsub]
  swap
  · intro t ht hn
    simp only [mem_Ioc, not_and, not_le] at ht hn
    apply sum_eq_zero
    intro r hr
    have hr1 : 1 ≤ r := by simp only [mem_Ioc] at hr; omega
    apply gS4_eq_zero hx
    have : t ≤ t * r := Nat.le_mul_of_pos_right t hr1
    have := hn ht.1
    omega
  rw [sum_Ioc_dyadic]
  refine sum_congr rfl fun j _ => ?_
  unfold blk
  refine sum_congr rfl fun t ht => ?_
  set M := u * 2 ^ j
  have hM : M < t := (mem_Ioc.1 ht).1
  have hdiv : N / M ≤ N := Nat.div_le_self _ _
  symm
  apply sum_subset (Ioc_subset_Ioc le_rfl (by omega))
  intro r hr hn
  simp only [mem_Ioc, not_and, not_le] at hr hn
  apply gS4_eq_zero hx
  show N < t * r
  by_contra hc
  push Not at hc
  have h1 : r ≤ N / t := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hc)
  have h2 : N / t ≤ N / M := Nat.div_le_div_left hM.le (Nat.mul_pos hu (by positivity))
  have := hn hr.1
  omega

end LeanLab.PNTPort.BV
