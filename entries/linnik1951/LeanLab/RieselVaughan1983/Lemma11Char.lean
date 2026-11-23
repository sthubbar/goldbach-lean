module

public import Mathlib
public import LeanLab.RieselVaughan1983.Lemma10Sum

/-!
P0032 Riesel-Vaughan 1983, Lemma 11, page 63: the character-sum step.
PC run 20261020T0503Z-11094, unit U-1174. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

* `conj_apply_unit`: for a unit `b` mod `d`, `conj χ(b) = χ(b⁻¹)`.
* `sum_norm_sq`: for a finite set `T` of integers prime to `d`,
  `Σ_χ |Σ_{p ∈ T} χ(p)|² = φ(d) · #{(p, p') ∈ T² : p ≡ p' mod d}`, by orthogonality.
* `card_pairs_le`: if `T ⊆ (L, L + y]`, the pair count is at most `#T (y/d + 1)`.
* `lemma11_char`: page 63, `Σ_{χ mod d} |S_k(χ)|² ≤ φ(d) S_k (y/d + 1)` for primes in an interval of
  length `y` that are prime to `d`; the paper then uses `y/d + 1 ≤ 3y/(2d)` for `d ≤ y/2`.
KNOWN mathematics.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.L11

variable {d : ℕ} [NeZero d]

/-- `conj χ(b) = χ(b⁻¹)` for a unit `b`. -/
theorem conj_apply_unit (χ : DirichletCharacter ℂ d) {b : ZMod d} (hb : IsUnit b) :
    starRingEnd ℂ (χ b) = χ b⁻¹ := by
  have hn : ‖χ b‖ = 1 := by
    have := χ.unit_norm_eq_one hb.unit
    simpa using this
  have hmul : χ b⁻¹ * χ b = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit b hb, map_one]
  have hne : χ b ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have hinv : χ b⁻¹ = (χ b)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [hinv, Complex.inv_def]
  have hns : Complex.normSq (χ b) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn]; norm_num
  rw [hns]; simp

/-- **Orthogonality**: `Σ_χ |Σ_{p ∈ T} χ(p)|² = φ(d) · #{(p, p') ∈ T² : p ≡ p' mod d}`. -/
theorem sum_norm_sq (T : Finset ℕ) (hT : ∀ p ∈ T, IsUnit (p : ZMod d)) :
    ∑ χ : DirichletCharacter ℂ d, ‖∑ p ∈ T, χ p‖ ^ 2 =
      (d.totient : ℝ) * ((T ×ˢ T).filter (fun q : ℕ × ℕ => ((q.1 : ℕ) : ZMod d) = ((q.2 : ℕ) : ZMod d))).card := by
  have key : ∀ χ : DirichletCharacter ℂ d, ((‖∑ p ∈ T, χ p‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ T ×ˢ T, χ (q.2 : ZMod d)⁻¹ * χ (q.1 : ZMod d) := by
    intro χ
    have hz : ((‖∑ p ∈ T, χ p‖ ^ 2 : ℝ) : ℂ) =
        (∑ p ∈ T, χ p) * starRingEnd ℂ (∑ p ∈ T, χ p) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hz, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro q hq
    rw [conj_apply_unit χ (hT q.2 (Finset.mem_product.1 hq).2), mul_comm]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [key]
  push_cast
  rw [Finset.sum_comm]
  have h2 : ∀ q ∈ T ×ˢ T, ∑ χ : DirichletCharacter ℂ d, χ (q.2 : ZMod d)⁻¹ * χ (q.1 : ZMod d) =
      if (q.1 : ZMod d) = q.2 then (d.totient : ℂ) else 0 := by
    intro q hq
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (hT q.2 (Finset.mem_product.1 hq).2)]
    simp only [eq_comm]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Integers in `(L, L + y]` in one residue class mod `d` number at most `y/d + 1`. -/
theorem card_class_le (L : ℕ) (y : ℝ) (hy : 0 ≤ y) (a : ZMod d) :
    (((Ioc L (L + ⌊y⌋₊)).filter (fun m : ℕ => (m : ZMod d) = a)).card : ℝ) ≤ y / d + 1 := by
  set S := (Ioc L (L + ⌊y⌋₊)).filter (fun m : ℕ => (m : ZMod d) = a)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rcases S.eq_empty_or_nonempty with h | ⟨m0, hm0⟩
  · rw [h]; simp; positivity
  -- every element is m0 + d j or m0 - d j; inject into the quotients (m - L - 1) / d
  have hinj : Set.InjOn (fun m : ℕ => (m - (L + 1)) / d) S := by
    intro x hx y' hy' hxy
    simp only [S, coe_filter, Set.mem_ofPred_eq, mem_Ioc] at hx hy'
    have hx1 : L + 1 ≤ x := hx.1.1
    have hy1 : L + 1 ≤ y' := hy'.1.1
    have hxy2 : (x : ZMod d) = y' := hx.2.trans hy'.2.symm
    have hc1 : ((x - (L + 1) : ℕ) : ZMod d) = ((y' - (L + 1) : ℕ) : ZMod d) := by
      rw [Nat.cast_sub hx1, Nat.cast_sub hy1, hxy2]
    have hm2 := (ZMod.natCast_eq_natCast_iff' _ _ d).1 hc1
    simp only at hxy
    have e1 := Nat.div_add_mod (x - (L + 1)) d
    have e2 := Nat.div_add_mod (y' - (L + 1)) d
    rw [hxy, hm2] at e1
    have := e1.symm.trans e2
    omega
  have hsub : S.image (fun m : ℕ => (m - (L + 1)) / d) ⊆ range (⌊y⌋₊ / d + 1) := by
    intro j hj
    simp only [mem_image, S, mem_filter, mem_Ioc] at hj
    obtain ⟨m, ⟨⟨h1, h2⟩, _⟩, rfl⟩ := hj
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hc : S.card ≤ ⌊y⌋₊ / d + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using card_le_card hsub
  have hcr : (S.card : ℝ) ≤ ((⌊y⌋₊ / d : ℕ) : ℝ) + 1 := by exact_mod_cast hc
  have hdiv : ((⌊y⌋₊ / d : ℕ) : ℝ) ≤ y / d := by
    rw [le_div_iff₀ (by exact_mod_cast hd)]
    have := Nat.div_mul_le_self ⌊y⌋₊ d
    have h' : ((⌊y⌋₊ / d * d : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'.trans (Nat.floor_le hy)
  linarith

/-- The pair count for `T ⊆ (L, L + y]`: at most `#T (y/d + 1)`. -/
theorem card_pairs_le (T : Finset ℕ) (L : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hT : T ⊆ Ioc L (L + ⌊y⌋₊)) :
    (((T ×ˢ T).filter (fun q : ℕ × ℕ => ((q.1 : ℕ) : ZMod d) = ((q.2 : ℕ) : ZMod d))).card : ℝ) ≤ T.card * (y / d + 1) := by
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro p _
  have hc : ∑ p' ∈ T, (if ((p : ℕ) : ZMod d) = ((p' : ℕ) : ZMod d) then (1 : ℝ) else 0) =
      ((T.filter (fun p' : ℕ => ((p' : ℕ) : ZMod d) = (p : ZMod d))).card : ℝ) := by
    rw [Finset.card_filter]; push_cast
    apply Finset.sum_congr rfl; intro x _; simp only [eq_comm]
  rw [hc]
  refine le_trans ?_ (card_class_le (d := d) L y hy (p : ZMod d))
  exact_mod_cast card_le_card (fun m hm => by
    simp only [mem_filter] at hm ⊢
    exact ⟨hT hm.1, hm.2⟩)

/-- **Lemma 11's character step**, page 63: for a finite set `T` of integers prime to `d` in an
interval `(L, L + y]`, `Σ_χ |Σ_{p ∈ T} χ(p)|² ≤ φ(d) · #T · (y/d + 1)`. -/
theorem lemma11_char (T : Finset ℕ) (L : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hT : T ⊆ Ioc L (L + ⌊y⌋₊)) (hu : ∀ p ∈ T, IsUnit (p : ZMod d)) :
    ∑ χ : DirichletCharacter ℂ d, ‖∑ p ∈ T, χ p‖ ^ 2 ≤ d.totient * (T.card * (y / d + 1)) := by
  rw [sum_norm_sq T hu]
  exact mul_le_mul_of_nonneg_left (card_pairs_le T L y hy hT) (by positivity)

/-- Vacuity: with `d = 3`, `T = {5, 7}`, both units mod 3 in `(4, 4 + 3]`. -/
theorem lemma11_vacuity : ({5, 7} : Finset ℕ) ⊆ Ioc 4 (4 + ⌊(3 : ℝ)⌋₊) ∧
    ∀ p ∈ ({5, 7} : Finset ℕ), IsUnit (p : ZMod 3) := by
  refine ⟨?_, ?_⟩
  · have : ⌊(3 : ℝ)⌋₊ = 3 := by norm_num
    rw [this]; decide
  · intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl <;> decide

/-- `Σ_{k < m ≤ M} 1/m² ≤ 1/k - 1/M` for `1 ≤ k ≤ M`, by `1/m² ≤ 1/(m-1) - 1/m`. -/
lemma sum_inv_sq_Ioc_le (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    ∑ m ∈ Ioc k M, 1 / ((m : ℝ) ^ 2) ≤ 1 / (k : ℝ) - 1 / (M : ℝ) := by
  induction M, hkM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans hk hM
    have key : 1 / (((M + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `Σ_{t < m ≤ M} 1/m² ≤ 2/t` for `t > 0`. -/
theorem sum_inv_sq_window (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ∑ m ∈ Icc (⌊t⌋₊ + 1) M, 1 / ((m : ℝ) ^ 2) ≤ 2 / t := by
  set k := ⌊t⌋₊ with hk
  have h2pos : 0 ≤ 2 / t := by positivity
  rcases Nat.lt_or_ge M (k + 1) with hlt | hge
  · rw [Finset.Icc_eq_empty (by omega), sum_empty]; exact h2pos
  have hIcc : Icc (k + 1) M = Ioc k M := by ext x; simp
  rw [hIcc]
  have htk : t < k + 1 := Nat.lt_floor_add_one t
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0] at htk ⊢
    have h2t : 2 ≤ 2 / t := by rw [le_div_iff₀ ht]; push_cast at htk; linarith
    refine le_trans ?_ h2t
    have hsplit : Ioc 0 M = insert 1 (Ioc 1 M) := by ext x; simp; omega
    rw [hsplit, sum_insert (by simp)]
    have := sum_inv_sq_Ioc_le 1 M le_rfl (by omega)
    have hp : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    simp only [Nat.cast_one, one_pow, div_one] at this ⊢
    linarith
  · have h1 := sum_inv_sq_Ioc_le k M hpos (by omega)
    have hp : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hpos
    have : 1 / (k : ℝ) ≤ 2 / t := by
      rw [div_le_div_iff₀ (by linarith) ht]; push_cast at htk; linarith
    linarith

/-- **Lemma 11's tail**: `Σ_{w < d ≤ D, d odd} μ(d)²/(d φ(d)) ≤ (2/w) Σ_{r ≤ D, r odd} μ(r)²/(r φ(r))`,
so with the odd sum below `A₁₀` the tail is at most `2 A₁₀ / w`, the factor behind `3 A₁₀ y/w`. -/
theorem lemma11_tail {w D : ℝ} (hw : 0 < w) :
    ∑ d ∈ (Icc (⌊w⌋₊ + 1) ⌊D⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ)) ≤
      (2 / w) * ∑ r ∈ (Icc 1 ⌊D⌋₊).filter Odd, ((μ r : ℝ)) ^ 2 / ((r : ℝ) * (r.totient : ℝ)) := by
  set Dset := (Icc (⌊w⌋₊ + 1) ⌊D⌋₊).filter Odd with hD
  set R := (Icc 1 ⌊D⌋₊).filter Odd with hR
  set G : ℕ → ℝ := fun r => ((μ r : ℝ)) ^ 2 / (r.totient : ℝ) with hG
  have hGnn : ∀ r, 0 ≤ G r := fun r => by simp only [hG]; positivity
  have step1 : ∑ d ∈ Dset, ((μ d : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ)) ≤
      ∑ d ∈ Dset, ∑ r ∈ d.divisors, G r * (1 / ((d : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := by simp only [hD, mem_filter, mem_Icc] at hd; omega
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hmu : ((μ d : ℝ)) ^ 2 ≤ 1 := by
      have h := (abs_moebius_le_one (n := d))
      have h' : |((μ d : ℝ))| ≤ 1 := by exact_mod_cast h
      nlinarith [abs_nonneg ((μ d : ℝ)), sq_abs ((μ d : ℝ))]
    have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hinv := L10.inv_totient_eq d hd1
    calc ((μ d : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ)) ≤ 1 / ((d : ℝ) * (d.totient : ℝ)) := by
          gcongr
      _ = (1 / (d : ℝ)) * (1 / (d.totient : ℝ)) := by rw [one_div_mul_one_div]
      _ = (1 / (d : ℝ)) * ((1 / (d : ℝ)) * ∑ r ∈ d.divisors, G r) := by rw [hinv]
      _ = ∑ r ∈ d.divisors, G r * (1 / ((d : ℝ) ^ 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _; field_simp
  have step2 : ∑ d ∈ Dset, ∑ r ∈ d.divisors, G r * (1 / ((d : ℝ) ^ 2)) =
      ∑ r ∈ R, ∑ d ∈ Dset.filter (fun d => r ∣ d), G r * (1 / ((d : ℝ) ^ 2)) := by
    apply Finset.sum_comm'
    intro d r
    simp only [hD, hR, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hodd⟩, hrd, hd0⟩
      have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrd (by omega)
      exact ⟨⟨⟨⟨h1, h2⟩, hodd⟩, hrd⟩, ⟨⟨hr0, le_trans (Nat.le_of_dvd (by omega) hrd) h2⟩,
        Odd.of_dvd_nat hodd hrd⟩⟩
    · rintro ⟨⟨⟨⟨h1, h2⟩, hodd⟩, hrd⟩, _⟩
      exact ⟨⟨⟨h1, h2⟩, hodd⟩, hrd, by omega⟩
  have step3 : ∀ r ∈ R, ∑ d ∈ Dset.filter (fun d => r ∣ d), G r * (1 / ((d : ℝ) ^ 2)) ≤
      G r / r * (2 / w) := by
    intro r hr
    have hr1 : 1 ≤ r := by simp only [hR, mem_filter, mem_Icc] at hr; omega
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    set M := Icc (⌊w / r⌋₊ + 1) ⌊D⌋₊ with hM
    have hsub : Dset.filter (fun d => r ∣ d) ⊆ M.image (fun m => r * m) := by
      intro d hd
      simp only [hD, mem_filter, mem_Icc] at hd
      obtain ⟨⟨⟨h1, h2⟩, _⟩, ⟨m, rfl⟩⟩ := hd
      refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
      have hda : w < ((r * m : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one w
        have h1' : ((⌊w⌋₊ + 1 : ℕ) : ℝ) ≤ ((r * m : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h1' this ⊢; linarith
      push_cast at hda
      simp only [hM, mem_Icc]
      constructor
      · have : w / r < m := by rw [div_lt_iff₀ hrpos]; linarith
        have h3 := (Nat.floor_lt (div_nonneg hw.le hrpos.le)).2 this
        omega
      · have : m ≤ r * m := Nat.le_mul_of_pos_left m (by omega)
        omega
    have hinj : Set.InjOn (fun m => r * m) (M : Set ℕ) := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
    calc ∑ d ∈ Dset.filter (fun d => r ∣ d), G r * (1 / ((d : ℝ) ^ 2))
        ≤ ∑ d ∈ M.image (fun m => r * m), G r * (1 / ((d : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro d _ _; exact mul_nonneg (hGnn r) (by positivity)
      _ = ∑ m ∈ M, G r * (1 / (((r * m : ℕ) : ℝ) ^ 2)) :=
          Finset.sum_image (fun x hx y hy h => hinj hx hy h)
      _ = G r / r ^ 2 * ∑ m ∈ M, 1 / ((m : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          have hm1 : (0 : ℝ) < m := by
            simp only [hM, mem_Icc] at hm; exact_mod_cast (by omega : 0 < m)
          push_cast
          field_simp
      _ ≤ G r / r ^ 2 * (2 / (w / r)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (hGnn r) (by positivity))
          exact sum_inv_sq_window (w / r) (div_pos hw hrpos) _
      _ = G r / r * (2 / w) := by field_simp
  calc ∑ d ∈ Dset, ((μ d : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ))
      ≤ ∑ r ∈ R, G r / r * (2 / w) := step1.trans (step2 ▸ Finset.sum_le_sum step3)
    _ = _ := by
        rw [← Finset.sum_mul, mul_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        simp only [hG]
        rw [div_div, mul_comm (r.totient : ℝ)]

/-- Real-endpoint form: integers of a finite set `T ⊆ (L, L + y]`, `L` real, in one class mod `d`,
number at most `y/d + 1`; the paper's `I_k = (ky/2, ky/2 + y]` has real endpoints. -/
theorem card_class_le_real (T : Finset ℕ) (L y : ℝ) (hy : 0 ≤ y)
    (hT : ∀ p ∈ T, L < p ∧ (p : ℝ) ≤ L + y) (a : ZMod d) :
    ((T.filter (fun m : ℕ => (m : ZMod d) = a)).card : ℝ) ≤ y / d + 1 := by
  set S := T.filter (fun m : ℕ => (m : ZMod d) = a) with hS
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]; simp; positivity
  set m0 := S.min' hne with hm0
  have hm0S : m0 ∈ S := S.min'_mem hne
  have hm0T := (Finset.mem_filter.1 hm0S)
  have hinj : Set.InjOn (fun m : ℕ => (m - m0) / d) S := by
    intro x hx y' hy' hxy
    have hx' := Finset.mem_filter.1 hx
    have hy'' := Finset.mem_filter.1 hy'
    have hx1 : m0 ≤ x := S.min'_le x hx
    have hy1 : m0 ≤ y' := S.min'_le y' hy'
    have hxy2 : (x : ZMod d) = y' := hx'.2.trans hy''.2.symm
    have hc1 : ((x - m0 : ℕ) : ZMod d) = ((y' - m0 : ℕ) : ZMod d) := by
      rw [Nat.cast_sub hx1, Nat.cast_sub hy1, hxy2]
    have hm2 := (ZMod.natCast_eq_natCast_iff' _ _ d).1 hc1
    simp only at hxy
    have e1 := Nat.div_add_mod (x - m0) d
    have e2 := Nat.div_add_mod (y' - m0) d
    rw [hxy, hm2] at e1
    have := e1.symm.trans e2
    omega
  have hsub : S.image (fun m : ℕ => (m - m0) / d) ⊆ range (⌊y / d⌋₊ + 1) := by
    intro j hj
    simp only [mem_image] at hj
    obtain ⟨m, hm, rfl⟩ := hj
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have hmT := (hT m (Finset.mem_filter.1 hm).1)
    have hm0T' := (hT m0 hm0T.1)
    have hle : m0 ≤ m := S.min'_le m hm
    have hdiff : ((m - m0 : ℕ) : ℝ) ≤ y := by
      rw [Nat.cast_sub hle]; linarith [hmT.2, hm0T'.1]
    have hdiv : (((m - m0) / d : ℕ) : ℝ) ≤ ((m - m0 : ℕ) : ℝ) / d := Nat.cast_div_le
    calc (((m - m0) / d : ℕ) : ℝ) ≤ ((m - m0 : ℕ) : ℝ) / d := hdiv
      _ ≤ y / d := by gcongr
  have hc : S.card ≤ ⌊y / d⌋₊ + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using card_le_card hsub
  have hcr : (S.card : ℝ) ≤ (⌊y / d⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  have := Nat.floor_le (div_nonneg hy hdr.le)
  linarith

/-- **Lemma 11's character step with real endpoints**, page 63, for `T ⊆ (L, L + y]`. -/
theorem lemma11_char_real (T : Finset ℕ) (L y : ℝ) (hy : 0 ≤ y)
    (hT : ∀ p ∈ T, L < p ∧ (p : ℝ) ≤ L + y) (hu : ∀ p ∈ T, IsUnit (p : ZMod d)) :
    ∑ χ : DirichletCharacter ℂ d, ‖∑ p ∈ T, χ p‖ ^ 2 ≤ d.totient * (T.card * (y / d + 1)) := by
  rw [sum_norm_sq T hu]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro p _
  have hc : ∑ p' ∈ T, (if ((p : ℕ) : ZMod d) = ((p' : ℕ) : ZMod d) then (1 : ℝ) else 0) =
      ((T.filter (fun p' : ℕ => ((p' : ℕ) : ZMod d) = (p : ZMod d))).card : ℝ) := by
    rw [Finset.card_filter]; push_cast
    apply Finset.sum_congr rfl; intro x _; simp only [eq_comm]
  rw [hc]
  exact card_class_le_real T L y hy hT (p : ZMod d)

end LeanLab.RieselVaughan1983.L11
