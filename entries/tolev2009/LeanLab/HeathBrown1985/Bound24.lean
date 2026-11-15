module

public import Mathlib
public import LeanLab.HeathBrown1985.Lemma1

/-!
P0096 Heath-Brown 1985, 2.4 from the Siegel-Walfisz theorem 1.1, as on page 48.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt Nat

attribute [local instance] Classical.propDecidable

/-- `(log x)^B ≤ B^B x` for `x ≥ 1`, `B > 0`. -/
theorem log_rpow_le (x B : ℝ) (hx : 1 ≤ x) (hB : 0 < B) : Real.log x ^ B ≤ B ^ B * x := by
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ x) (by positivity : (0:ℝ) < 1 / B)
  rw [div_eq_mul_inv, one_div, inv_inv] at h
  have h2 : Real.log x ≤ B * x ^ B⁻¹ := by linarith [mul_comm (x ^ B⁻¹) B]
  calc Real.log x ^ B ≤ (B * x ^ B⁻¹) ^ B := Real.rpow_le_rpow hL0 h2 hB.le
    _ = B ^ B * x := by
        rw [Real.mul_rpow hB.le (by positivity), ← Real.rpow_mul (by linarith),
          inv_mul_cancel₀ hB.ne', Real.rpow_one]

/-- `L^A ≤ C exp(c √L)` for `L ≥ 0`. -/
theorem rpow_le_exp_sqrt (A c : ℝ) (hA : 0 < A) (hc : 0 < c) : ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 ≤ L →
    L ^ A ≤ C * Real.exp (c * Real.sqrt L) := by
  set N := ⌈2 * A⌉₊
  refine ⟨max 1 (N ! / c ^ N), by positivity, fun L hL => ?_⟩
  have he : 0 < Real.exp (c * Real.sqrt L) := Real.exp_pos _
  rcases le_or_gt L 1 with h1 | h1
  · have : L ^ A ≤ 1 := Real.rpow_le_one hL h1 hA.le
    have : 1 ≤ Real.exp (c * Real.sqrt L) := Real.one_le_exp (by positivity)
    calc L ^ A ≤ 1 * 1 := by linarith
      _ ≤ max 1 (N ! / c ^ N) * Real.exp (c * Real.sqrt L) :=
          mul_le_mul (le_max_left _ _) (by linarith) zero_le_one (by positivity)
  · have hs : 0 ≤ c * Real.sqrt L := by positivity
    have hf := Real.pow_div_factorial_le_exp (c * Real.sqrt L) hs N
    have hN : 2 * A ≤ N := Nat.le_ceil _
    have hLA : L ^ A ≤ L ^ ((N : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have hsq : (Real.sqrt L) ^ N = L ^ ((N : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL]; congr 1; ring
    have hcN : 0 < c ^ N := by positivity
    have hfac : (0 : ℝ) < N ! := by exact_mod_cast Nat.factorial_pos N
    rw [mul_pow, hsq] at hf
    calc L ^ A ≤ L ^ ((N : ℝ) / 2) := hLA
      _ = (N ! / c ^ N) * (c ^ N * L ^ ((N : ℝ) / 2) / N !) := by field_simp
      _ ≤ (N ! / c ^ N) * Real.exp (c * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ max 1 (N ! / c ^ N) * Real.exp (c * Real.sqrt L) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) he.le

/-- Non-coprime classes: `ψ(x; k, l) ≤ L³/(log 2)²` when `(l, k) > 1`. -/
theorem psi_noncoprime_le (x : ℝ) (hx : 2 ≤ x) (k l : ℕ) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x)
    (hc : ¬ Nat.Coprime l k) :
    psi x k l ≤ Real.log x ^ 3 / Real.log 2 ^ 2 := by
  set L := Real.log x
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hx0 : 0 < x := by linarith
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  set E := ⌊L / l2⌋₊
  set S := ((Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k)).filter (fun n => Λ n ≠ 0)
  have hsub : S ⊆ (k.primeFactors ×ˢ Icc 1 E).image (fun pe => pe.1 ^ pe.2) := by
    intro n hn
    simp only [S, mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hmod⟩, hΛ⟩ := hn
    obtain ⟨p, e, hp, he, rfl⟩ := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hp' := hp.nat_prime
    simp only [mem_image, mem_product, mem_Icc, Prod.exists]
    refine ⟨p, e, ⟨?_, he, ?_⟩, rfl⟩
    · -- p ∣ k, since (p^e, k) = (l, k) > 1
      have hg : Nat.gcd (p ^ e) k = Nat.gcd l k := by
        rw [Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec, Nat.gcd_comm]
      by_contra hpk
      have hpk' : ¬ p ∣ k := fun h => hpk (Nat.mem_primeFactors.mpr ⟨hp', h, by omega⟩)
      have : Nat.Coprime (p ^ e) k :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp').mpr hpk')
      exact hc (by rw [Nat.Coprime, ← hg]; exact this)
    · -- e ≤ L / log 2
      have h2e : (2 : ℝ) ^ e ≤ x := by
        have : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp'.two_le e
        have h' : ((p ^ e : ℕ) : ℝ) ≤ x := le_trans (by exact_mod_cast hnN) (Nat.floor_le hx0.le)
        calc (2 : ℝ) ^ e = ((2 ^ e : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((p ^ e : ℕ) : ℝ) := by exact_mod_cast this
          _ ≤ x := h'
      have := Real.log_le_log (by positivity) h2e
      rw [Real.log_pow] at this
      apply Nat.le_floor
      rw [le_div_iff₀ hl2]; exact this
  have hcard : (S.card : ℝ) ≤ (L / l2) * (L / l2) := by
    have h1 := card_le_card hsub
    have h2 := card_image_le (s := k.primeFactors ×ˢ Icc 1 E) (f := fun pe => pe.1 ^ pe.2)
    rw [card_product, Nat.card_Icc, add_tsub_cancel_right] at h2
    have hω : (k.primeFactors.card : ℝ) ≤ L / l2 := by
      rw [le_div_iff₀ hl2]
      exact (card_primeFactors_mul_log_two_le k hk).trans
        (Real.log_le_log (by exact_mod_cast hk) hkx)
    have hLl : 0 ≤ L / l2 := div_nonneg (by linarith) hl2.le
    have hE : (E : ℝ) ≤ L / l2 := Nat.floor_le hLl
    calc (S.card : ℝ) ≤ (k.primeFactors.card * E : ℕ) := by exact_mod_cast h1.trans h2
      _ = (k.primeFactors.card : ℝ) * E := by push_cast; ring
      _ ≤ (L / l2) * (L / l2) := mul_le_mul hω hE (by positivity) hLl
  unfold psi
  rw [← sum_filter_ne_zero]
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, L := by
        apply sum_le_sum; intro n hn
        simp only [S, mem_filter, mem_Icc] at hn
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        exact Real.log_le_log (by exact_mod_cast hn.1.1.1) (le_trans
          (by exact_mod_cast hn.1.1.2) (Nat.floor_le hx0.le))
    _ = S.card * L := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (L / l2) * (L / l2) * L := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = L ^ 3 / l2 ^ 2 := by field_simp

/-- Coprime classes with a large modulus: `|ψ(x;k,l) - x/φ(k)| ≤ (2 + 2e/log 2) x L / k`. -/
theorem abs_err_le' (x : ℝ) (hx : 2 ≤ x) (k l : ℕ) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x) :
    |psi x k l - x / (Nat.totient k : ℝ)| ≤
      (2 + 2 * Real.exp 1 / Real.log 2) * x * Real.log x / k := by
  set L := Real.log x
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hφ : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hψ0 := psi_nonneg x k l
  have hψ := psi_le x (by linarith) k l hk
  have hxk : 1 ≤ x / k := by rw [le_div_iff₀ hkR]; linarith
  have hω : (k.primeFactors.card : ℝ) ≤ L / l2 := by
    rw [le_div_iff₀ hl2]
    exact (card_primeFactors_mul_log_two_le k hk).trans (Real.log_le_log hkR hkx)
  have h1 : 1 ≤ L / l2 := by rw [le_div_iff₀ hl2]; linarith
  have hdt := div_totient_le k hk
  have hxφ : x / (Nat.totient k : ℝ) = (x / k) * ((k : ℝ) / Nat.totient k) := by field_simp
  have he := Real.exp_pos 1
  have hxφ_le : x / (Nat.totient k : ℝ) ≤ (x / k) * (2 * Real.exp 1 / l2 * L) := by
    rw [hxφ]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine hdt.trans ?_
    have e : 2 * Real.exp 1 / l2 * L = Real.exp 1 * (L / l2 + L / l2) := by ring
    rw [e]; apply mul_le_mul_of_nonneg_left _ he.le; linarith
  have habs : |psi x k l - x / (Nat.totient k : ℝ)| ≤ psi x k l + x / (Nat.totient k : ℝ) := by
    rw [abs_le]; constructor <;> nlinarith [div_nonneg hx0.le hφ.le]
  have hψ2 : psi x k l ≤ 2 * L * (x / k) := by nlinarith
  calc _ ≤ _ := habs
    _ ≤ 2 * L * (x / k) + (x / k) * (2 * Real.exp 1 / l2 * L) := add_le_add hψ2 hxφ_le
    _ = _ := by field_simp

/-- **2.4 from the Siegel-Walfisz theorem 1.1**, as on page 48. -/
theorem bound2_4_of (hSW : SiegelWalfisz) : Bound2_4 := by
  intro A hA
  obtain ⟨c, hc, K, hK⟩ := hSW (A + 1) (by linarith)
  obtain ⟨C1, hC1, hC1b⟩ := rpow_le_exp_sqrt A c hA hc
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set C2 := 2 + 2 * Real.exp 1 / l2
  set C3 := (A + 3) ^ (A + 3) / l2 ^ 2
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  refine ⟨|K| * C1 + C2 + C3, fun x hx k l hk hkx => ?_⟩
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set R := x * L ^ (-A)
  have hR : 0 < R := by positivity
  have hKC : 0 ≤ |K| * C1 := by positivity
  have hfin : ∀ b, b ≤ |K| * C1 * R ∨ b ≤ C2 * R ∨ b ≤ C3 * R →
      b ≤ (|K| * C1 + C2 + C3) * x * L ^ (-A) := by
    intro b hb
    have e : (|K| * C1 + C2 + C3) * x * L ^ (-A) = |K| * C1 * R + C2 * R + C3 * R := by ring
    rw [e]
    have h1 : 0 ≤ |K| * C1 * R := by positivity
    have h2 : 0 ≤ C2 * R := by positivity
    have h3 : 0 ≤ C3 * R := by positivity
    rcases hb with hb | hb | hb <;> linarith
  apply hfin
  split_ifs with hcop
  · rcases le_or_gt (k : ℝ) (L ^ (A + 1)) with hsmall | hbig
    · left
      have h1 := hK x hx k l hk hcop hsmall
      have h2 : Real.exp (-c * Real.sqrt L) ≤ C1 * L ^ (-A) := by
        have hb := hC1b L hL0.le
        have he : 0 < Real.exp (c * Real.sqrt L) := Real.exp_pos _
        rw [show -c * Real.sqrt L = -(c * Real.sqrt L) by ring, Real.exp_neg,
          Real.rpow_neg hL0.le]
        rw [inv_le_iff_one_le_mul₀ he]
        have hLA : 0 < L ^ A := by positivity
        calc (1 : ℝ) = (L ^ A)⁻¹ * L ^ A := by field_simp
          _ ≤ (L ^ A)⁻¹ * (C1 * Real.exp (c * Real.sqrt L)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = C1 * (L ^ A)⁻¹ * Real.exp (c * Real.sqrt L) := by ring
      calc _ ≤ K * x * Real.exp (-c * Real.sqrt L) := h1
        _ ≤ |K| * x * Real.exp (-c * Real.sqrt L) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right (le_abs_self _) hx0.le
        _ ≤ |K| * x * (C1 * L ^ (-A)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = |K| * C1 * R := by ring
    · right; left
      have h1 := abs_err_le' x hx k l hk hkx
      refine h1.trans ?_
      rw [div_le_iff₀ hkR]
      have hpos : 0 ≤ C2 * x * L ^ (-A) := by positivity
      calc C2 * x * L = C2 * x * (L ^ (A + 1) * L ^ (-A)) := by
            rw [← Real.rpow_add hL0]; simp
        _ = C2 * x * L ^ (-A) * L ^ (A + 1) := by ring
        _ ≤ C2 * x * L ^ (-A) * k := mul_le_mul_of_nonneg_left hbig.le hpos
        _ = C2 * R * k := by ring
  · right; right
    rw [sub_zero, abs_of_nonneg (psi_nonneg x k l)]
    refine (psi_noncoprime_le x hx k l hk hkx hcop).trans ?_
    have hb := log_rpow_le x (A + 3) (by linarith) (by linarith)
    have e1 : L ^ 3 = L ^ (A + 3) * L ^ (-A) := by
      rw [← Real.rpow_add hL0, show A + 3 + -A = (3 : ℕ) by push_cast; ring, Real.rpow_natCast]
    rw [e1, div_le_iff₀ (by positivity)]
    have hLA : 0 < L ^ (-A) := by positivity
    calc L ^ (A + 3) * L ^ (-A) ≤ (A + 3) ^ (A + 3) * x * L ^ (-A) :=
          mul_le_mul_of_nonneg_right hb hLA.le
      _ = C3 * R * l2 ^ 2 := by simp only [C3, R]; field_simp

/-- **Theorem 2 of Heath-Brown 1985 from the Siegel-Walfisz theorem 1.1 alone.** Fully proved. -/
theorem theorem2_of_siegelWalfisz (hSW : SiegelWalfisz) : Theorem2 :=
  theorem2_of_bound2_4 (bound2_4_of hSW)

end LeanLab.HeathBrown1985
