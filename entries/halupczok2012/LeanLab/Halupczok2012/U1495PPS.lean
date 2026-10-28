module

public import LeanLab.Halupczok2012.U1493Theorem5Min
public import Mathlib.NumberTheory.Chebyshev

/-!
# P0077 Halupczok 2012, `Theorem3` from the printed Perelli-Pintz-Salerno 1984, unit U-1495

AI wrote the Lean code, Claude, run 20261022T2003Z-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Source: A. Perelli, J. Pintz, S. Salerno, Bombieri's theorem in short intervals,
Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 11 (1984), no. 4, 529-539, numdam
ASNSP_1984_4_11_4_529_0, read from page images.

* Display (2), p. 529: with `y = x^θ`, `Q = x^ψ / (log x)^B`,
  `∑_{q ≤ Q} max_{(a,q)=1} max_{h ≤ y} max_{x/2 < z ≤ x} |ψ(z+h;q,a) - ψ(z;q,a) - h/φ(q)|
   ≪ y / (log x)^A`.
* THEOREM, p. 530: "The estimate (2) holds if `ψ ⩽ θ - 1/2` and `θ > 3/5`."
* REMARK, p. 530: "Indeed, as it is clear from the proof, we obtain (2) if (3) holds and
  `y ⩾ x^{3/5} (log x)^C`, `C = C(A)`." Here (3) is `ψ ⩽ θ - 1/2`.

Lean:

* `PPS1984Printed`: the THEOREM, fixed `θ ∈ (3/5, 1]`, fixed `ψ ≤ θ - 1/2`. Cited input.
* `PPS1984Remark`: the REMARK, uniform in `y ≥ x^{3/5} (log x)^D`, `D = D(A)`. Cited input.
* `PPS1984Uniform`: the THEOREM with constants uniform for `θ` in `[3/5 + ε, 1]`, i.e.
  `x^{3/5+ε} ≤ y ≤ x`. The narrowest cited input that gives `Theorem3`.
* `uniform_of_remark : PPS1984Remark → PPS1984Uniform`. PROVED.
* `printed_of_uniform : PPS1984Uniform → PPS1984Printed`. PROVED.
* `theorem3_of_uniform : PPS1984Uniform → Theorem3`. PROVED: theta from psi by removing prime
  powers, bounded by Mathlib's `ψ x - θ x ≤ C √x` times `Q ≪ Y X^{-1/2} L^{-B}`; the max over
  `h, z` used at `h = Y`, `z = X`, `x = X`, `y = Y`; `log X` to `log Y`.
* `theorem2Zeroed_U1495`: the F-0008 repair CONDITIONAL ON `PPS1984Uniform` and `Theorem5Min`.
* `theorem2Zeroed_U1495_remark`: CONDITIONAL ON `PPS1984Remark` and `Theorem5Min`.

`PPS1984Printed` alone does NOT give `Theorem3` by these steps: its constants may depend on the
fixed `θ`, while `Theorem3` needs one constant for all `Y` with `X^{3/5+ε} ≪ Y ≤ X`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-- `ψ(z; q, a) = ∑_{n ≤ z, n ≡ a (q)} Λ(n)`, as printed on p. 529. -/
noncomputable def psiAP (z : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ n ∈ (Ioc 0 ⌊z⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]),
    ArithmeticFunction.vonMangoldt n

/-- The PPS summand `|ψ(z+h;q,a) - ψ(z;q,a) - h/φ(q)|`. -/
noncomputable def ppsTerm (z h : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  |psiAP (z + h) q a - psiAP z q a - h / q.totient|

/-- **The printed THEOREM of Perelli-Pintz-Salerno 1984, p. 530, with (2) of p. 529.**
For fixed `θ ∈ (3/5, 1]` and `ψ ≤ θ - 1/2`, every `A > 0` has a `B > 0` with
`∑_{q ≤ x^ψ/(log x)^B} max_{(a,q)=1} max_{0<h ≤ x^θ} max_{x/2<z≤x} |…| ≪ x^θ (log x)^{-A}`.
The three maxima are encoded by arbitrary choice functions `a, h, z` of `q`.
The restriction `θ ≤ 1` and `h > 0` only weaken the Prop. Cited input. -/
def PPS1984Printed : Prop :=
  ∀ θ ψ A : ℝ, 3 / 5 < θ → θ ≤ 1 → ψ ≤ θ - 1 / 2 → 0 < A →
  ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
    (∀ q, 0 < h q ∧ h q ≤ x ^ θ) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
    ∑ q ∈ Icc 1 ⌊x ^ ψ * Real.log x ^ (-B)⌋₊, ppsTerm (z q) (h q) q (a q) ≤
      C * x ^ θ * Real.log x ^ (-A)

/-- **The printed REMARK, p. 530**, in its uniform reading: for every `A > 0` there are
`D = C(A)` and `B` with (2) for all `x^{3/5} (log x)^D ≤ y ≤ x` and all
`Q ≤ y x^{-1/2} (log x)^{-B}`, which is (3), one implied constant. Cited input. -/
def PPS1984Remark : Prop :=
  ∀ A : ℝ, 0 < A → ∃ D B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ, x0 ≤ x →
    x ^ (3 / 5 : ℝ) * Real.log x ^ D ≤ y → y ≤ x →
    Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
    ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
    (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A)

/-- **The THEOREM uniform in `θ ∈ [3/5+ε, 1]`.** The narrowest cited input used here. -/
def PPS1984Uniform : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ, x0 ≤ x →
    x ^ (3 / 5 + ε) ≤ y → y ≤ x →
    Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
    ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
    (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A)

/-! ### The Remark implies the uniform Theorem, which implies the fixed `θ` Theorem -/

/-- Eventually `(log x)^D ≤ x^ε`. -/
theorem eventually_log_rpow_le (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x1 : ℝ, ∀ x : ℝ, x1 ≤ x → Real.log x ^ D ≤ x ^ ε := by
  have h := (isLittleO_log_rpow_rpow_atTop D hε).bound one_pos
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp
    (h.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x1, fun x hx => ?_⟩
  obtain ⟨hb, hx⟩ := hx1 x hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hb
  exact hb

/-- **`PPS1984Remark → PPS1984Uniform`.** PROVED. -/
theorem uniform_of_remark (hR : PPS1984Remark) : PPS1984Uniform := by
  intro A ε hA hε
  obtain ⟨D, B, hB, C, x0, hC⟩ := hR A hA
  obtain ⟨x1, hx1⟩ := eventually_log_rpow_le D hε
  refine ⟨B, hB, C, max (max x0 x1) 1, ?_⟩
  intro x y Q hx hy1 hy2 hQ a h z ha hh hz
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  apply hC x y Q hx0 _ hy2 hQ a h z ha hh hz
  calc x ^ (3 / 5 : ℝ) * Real.log x ^ D ≤ x ^ (3 / 5 : ℝ) * x ^ ε :=
        mul_le_mul_of_nonneg_left (hx1 x hx1') (Real.rpow_nonneg hxpos.le _)
    _ = x ^ (3 / 5 + ε) := (Real.rpow_add hxpos _ _).symm
    _ ≤ y := hy1

/-- **`PPS1984Uniform → PPS1984Printed`.** PROVED: take `ε = θ - 3/5`, `y = x^θ`. -/
theorem printed_of_uniform (hU : PPS1984Uniform) : PPS1984Printed := by
  intro θ ψ A hθ hθ1 hψ hA
  obtain ⟨B, hB, C, x0, hC⟩ := hU A (θ - 3 / 5) hA (by linarith)
  refine ⟨B, hB, C, max x0 1, ?_⟩
  intro x hx a h z ha hh hz
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  apply hC x (x ^ θ) (x ^ ψ * Real.log x ^ (-B)) hx0 _ _ _ a h z ha hh hz
  · rw [show (3 / 5 : ℝ) + (θ - 3 / 5) = θ by ring]
  · calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ1
      _ = x := Real.rpow_one x
  · have h1 : x ^ ψ ≤ x ^ (θ + (-(1 / 2) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_add hxpos] at h1
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hlog _)

/-! ### Theta from psi: removing prime powers -/

/-- For `X, Y ≥ 0`: `0 ≤ ψ(X+Y;q,a) - ψ(X;q,a) - θ(X,Y;q,a) ≤ ψ(X+Y) - θ(X+Y)`. -/
theorem psiDiff_sub_thetaAP (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (q : ℕ) (a : ℤ) :
    0 ≤ psiAP (X + Y) q a - psiAP X q a - thetaAP X Y q a ∧
    psiAP (X + Y) q a - psiAP X q a - thetaAP X Y q a ≤
      Chebyshev.psi (X + Y) - Chebyshev.theta (X + Y) := by
  set g : ℕ → ℝ := fun n => if (n : ℤ) ≡ a [ZMOD q] then ArithmeticFunction.vonMangoldt n
    else 0 with hg
  set t : ℕ → ℝ := fun n => if n.Prime ∧ (n : ℤ) ≡ a [ZMOD q] then Real.log n else 0 with ht
  set d : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n - if n.Prime then Real.log n
    else 0 with hd
  have hfl : ⌊X⌋₊ ≤ ⌊X + Y⌋₊ := Nat.floor_mono (by linarith)
  have hpsi : ∀ w : ℝ, psiAP w q a = ∑ n ∈ Ioc 0 ⌊w⌋₊, g n := fun w => by
    unfold psiAP; rw [sum_filter]
  have hdiff : psiAP (X + Y) q a - psiAP X q a = ∑ n ∈ Ioc ⌊X⌋₊ ⌊X + Y⌋₊, g n := by
    rw [hpsi, hpsi, ← sum_Ioc_consecutive g (Nat.zero_le _) hfl]; ring
  have htheta : thetaAP X Y q a = ∑ n ∈ Ioc ⌊X⌋₊ ⌊X + Y⌋₊, t n := by
    unfold thetaAP; rw [ht, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter, mem_range, mem_Ioc]
    rw [Nat.floor_lt hX, Nat.le_floor_iff (by linarith)]
    constructor
    · rintro ⟨_, hp, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, hp, h3⟩
    · rintro ⟨⟨h1, h2⟩, hp, h3⟩
      refine ⟨?_, hp, h1, h2, h3⟩
      have := Nat.le_ceil (X + Y)
      have h4 : (n : ℝ) ≤ (⌈X + Y⌉₊ : ℝ) := le_trans h2 this
      have h5 : n ≤ ⌈X + Y⌉₊ := by exact_mod_cast h4
      omega
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    rw [hd]; dsimp only
    split_ifs with hp
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    · rw [sub_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
  have hgt : ∀ n, 0 ≤ g n - t n ∧ g n - t n ≤ d n := fun n => by
    rw [hg, ht, hd]; dsimp only
    by_cases hc : (n : ℤ) ≡ a [ZMOD q]
    · by_cases hp : n.Prime
      · simp only [hc, hp, and_self, if_true, ArithmeticFunction.vonMangoldt_apply_prime hp,
          sub_self, le_refl]
      · simp only [hc, hp, and_true, if_true, if_false, sub_zero, le_refl, and_true]
        exact ArithmeticFunction.vonMangoldt_nonneg
    · have := hd0 n
      rw [hd] at this
      simp only [hc, and_false, if_false, sub_self, le_refl, true_and]
      exact this
  have hpt : Chebyshev.psi (X + Y) - Chebyshev.theta (X + Y) =
      ∑ n ∈ Ioc 0 ⌊X + Y⌋₊, d n := by
    unfold Chebyshev.psi Chebyshev.theta
    rw [sum_filter, ← sum_sub_distrib]
  rw [hdiff, htheta, ← sum_sub_distrib, hpt]
  refine ⟨sum_nonneg fun n _ => (hgt n).1, ?_⟩
  calc ∑ n ∈ Ioc ⌊X⌋₊ ⌊X + Y⌋₊, (g n - t n) ≤ ∑ n ∈ Ioc ⌊X⌋₊ ⌊X + Y⌋₊, d n :=
        sum_le_sum fun n _ => (hgt n).2
    _ ≤ ∑ n ∈ Ioc 0 ⌊X + Y⌋₊, d n :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _))
          (fun n _ _ => hd0 n)

/-! ### `Theorem3` from the uniform PPS theorem -/

/-- `1 ≤ log X` for `X ≥ 3`. -/
theorem one_le_log_of_three_le {X : ℝ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- **`PPS1984Uniform → Theorem3`.** PROVED. -/
theorem theorem3_of_uniform (hU : PPS1984Uniform) : Theorem3 := by
  intro A ε hA hε
  obtain ⟨B, hB, C, x0, hC⟩ := hU A (ε / 2) hA (by positivity)
  obtain ⟨Cp, hCp⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨B + (A + 1), by positivity, ?_⟩
  intro c1 c2 hc1 hc2
  -- thresholds
  have e1 : ∀ᶠ X : ℝ in Filter.atTop, 1 / c1 ≤ X ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e2 : ∀ᶠ X : ℝ in Filter.atTop, c2 ≤ Real.log X ^ (A + 1) :=
    ((tendsto_rpow_atTop (by positivity)).comp Real.tendsto_log_atTop).eventually_ge_atTop _
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (e1.and e2)
  refine ⟨|C| + 2 * |Cp| * c2, max (max X1 x0) 3, ?_⟩
  intro X Y Q hY hYX hXY hQ a ha
  have hY3 : 3 ≤ Y := le_trans (le_max_right _ _) hY
  have hX3 : 3 ≤ X := le_trans hY3 hYX
  have hXX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hY hYX)
  have hXx0 : x0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hY hYX)
  obtain ⟨hX1a, hX1b⟩ := hX1 X hXX1
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  have hlogX : 1 ≤ Real.log X := one_le_log_of_three_le hX3
  have hlogY : 1 ≤ Real.log Y := one_le_log_of_three_le hY3
  have hlogXpos : 0 < Real.log X := by linarith
  -- Y ≥ X^{3/5+ε/2}
  have hYlow : X ^ (3 / 5 + ε / 2) ≤ Y := by
    have h1 : X ^ (3 / 5 + ε / 2) * 1 ≤ X ^ (3 / 5 + ε / 2) * (c1 * X ^ (ε / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hXpos.le _)
      rw [div_le_iff₀' hc1] at hX1a; linarith
    calc X ^ (3 / 5 + ε / 2) = X ^ (3 / 5 + ε / 2) * 1 := (mul_one _).symm
      _ ≤ X ^ (3 / 5 + ε / 2) * (c1 * X ^ (ε / 2)) := h1
      _ = c1 * X ^ (3 / 5 + ε / 2 + ε / 2) := by
          rw [Real.rpow_add hXpos (3 / 5 + ε / 2) (ε / 2)]; ring
      _ = c1 * X ^ (3 / 5 + ε) := by rw [show (3 / 5 : ℝ) + ε / 2 + ε / 2 = 3 / 5 + ε by ring]
      _ ≤ Y := hXY
  -- the Q bound
  set Qm : ℝ := c2 * Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-(B + (A + 1))) with hQm
  have hQm0 : 0 ≤ Qm := by positivity
  have hsplit : Real.log X ^ (-(B + (A + 1))) =
      Real.log X ^ (-B) * (Real.log X ^ (A + 1))⁻¹ := by
    rw [show -(B + (A + 1)) = -B + -(A + 1) by ring, Real.rpow_add hlogXpos,
      Real.rpow_neg hlogXpos.le (A + 1)]
  have hc2le : c2 * (Real.log X ^ (A + 1))⁻¹ ≤ 1 := by
    have hp : 0 < Real.log X ^ (A + 1) := Real.rpow_pos_of_pos hlogXpos _
    rw [← div_eq_mul_inv, div_le_one hp]; exact hX1b
  have hQ' : Q ≤ Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B) := by
    have hnn : 0 ≤ Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B) := by positivity
    calc Q ≤ Qm := hQ
      _ = (Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B)) * (c2 * (Real.log X ^ (A + 1))⁻¹) := by
          rw [hQm, hsplit]; ring
      _ ≤ (Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B)) * 1 :=
          mul_le_mul_of_nonneg_left hc2le hnn
      _ = _ := mul_one _
  -- apply the uniform PPS theorem at x = X, y = Y, h = Y, z = X
  have hmain := hC X Y Q hXx0 hYlow hYX hQ' a (fun _ => Y) (fun _ => X) ha
    (fun _ => ⟨hYpos, le_rfl⟩) (fun _ => ⟨by linarith, le_rfl⟩)
  -- the prime power error
  set E : ℝ := Chebyshev.psi (X + Y) - Chebyshev.theta (X + Y) with hE
  have hE : E ≤ |Cp| * (2 * Real.sqrt X) := by
    have h1 := hCp (X + Y)
    have h2 : Real.sqrt (X + Y) ≤ 2 * Real.sqrt X := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      calc Real.sqrt (X + Y) ≤ Real.sqrt (4 * X) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 * Real.sqrt X := by rw [Real.sqrt_mul (by norm_num), h4]
    calc E ≤ Cp * Real.sqrt (X + Y) := h1
      _ ≤ |Cp| * Real.sqrt (X + Y) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
      _ ≤ |Cp| * (2 * Real.sqrt X) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hterm : ∀ q, |thetaAP X Y q (a q) - Y / q.totient| ≤
      ppsTerm X Y q (a q) + |Cp| * (2 * Real.sqrt X) := by
    intro q
    obtain ⟨h0, h1⟩ := psiDiff_sub_thetaAP X Y hXpos.le hYpos.le q (a q)
    unfold ppsTerm
    have e : thetaAP X Y q (a q) - Y / q.totient =
        (psiAP (X + Y) q (a q) - psiAP X q (a q) - Y / q.totient) -
        (psiAP (X + Y) q (a q) - psiAP X q (a q) - thetaAP X Y q (a q)) := by ring
    rw [e]
    calc _ ≤ |psiAP (X + Y) q (a q) - psiAP X q (a q) - Y / q.totient| +
          |psiAP (X + Y) q (a q) - psiAP X q (a q) - thetaAP X Y q (a q)| := abs_sub _ _
      _ ≤ _ := by
          rw [abs_of_nonneg h0]
          have : psiAP (X + Y) q (a q) - psiAP X q (a q) - thetaAP X Y q (a q) ≤
              |Cp| * (2 * Real.sqrt X) := le_trans h1 hE
          linarith
  have hcard : ((Icc 1 ⌊Q⌋₊).card : ℝ) ≤ Qm := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    calc (⌊Q⌋₊ : ℝ) ≤ (⌊Qm⌋₊ : ℝ) := by exact_mod_cast Nat.floor_mono hQ
      _ ≤ Qm := Nat.floor_le hQm0
  have hsqrt : X ^ (-(1 / 2) : ℝ) * Real.sqrt X = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]; norm_num
  have hLB : Real.log X ^ (-(B + (A + 1))) ≤ Real.log X ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogX (by linarith)
  have hXY_L : Real.log X ^ (-A) ≤ Real.log Y ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (Real.log_le_log hYpos hYX) (by linarith)
  have hLpos : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlogXpos.le _
  calc ∑ q ∈ Icc 1 ⌊Q⌋₊, |thetaAP X Y q (a q) - Y / q.totient|
      ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, (ppsTerm X Y q (a q) + |Cp| * (2 * Real.sqrt X)) :=
        sum_le_sum fun q _ => hterm q
    _ = ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm X Y q (a q) +
          ((Icc 1 ⌊Q⌋₊).card : ℝ) * (|Cp| * (2 * Real.sqrt X)) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ C * Y * Real.log X ^ (-A) + Qm * (|Cp| * (2 * Real.sqrt X)) := by
        gcongr
    _ = C * Y * Real.log X ^ (-A) + 2 * |Cp| * c2 * Y * Real.log X ^ (-(B + (A + 1))) *
          (X ^ (-(1 / 2) : ℝ) * Real.sqrt X) := by rw [hQm]; ring
    _ = C * Y * Real.log X ^ (-A) + 2 * |Cp| * c2 * Y * Real.log X ^ (-(B + (A + 1))) := by
        rw [hsqrt, mul_one]
    _ ≤ C * Y * Real.log X ^ (-A) + 2 * |Cp| * c2 * Y * Real.log X ^ (-A) := by
        gcongr
    _ ≤ (|C| + 2 * |Cp| * c2) * Y * Real.log X ^ (-A) := by
        have : C * Y * Real.log X ^ (-A) ≤ |C| * Y * Real.log X ^ (-A) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        linarith
    _ ≤ (|C| + 2 * |Cp| * c2) * Y * Real.log Y ^ (-A) := by
        gcongr

/-! ### Vacuity: the hypotheses of the PPS Props hold for every large `x` -/

/-- For every `x ≥ 1`, `0 < ε ≤ 2/5`: `y = x`, `h q = x`, `z q = x`, `a q = 1` satisfy the
hypotheses of `PPS1984Uniform` on `y`, `a`, `h`, `z`. -/
theorem pps_hyp_instance (x ε : ℝ) (hx : 1 ≤ x) (hε : ε ≤ 2 / 5) :
    x ^ (3 / 5 + ε) ≤ x ∧ x ≤ x ∧ (∀ q : ℕ, Int.gcd (1 : ℤ) q = 1) ∧
    (∀ _q : ℕ, 0 < x ∧ x ≤ x) ∧ (∀ _q : ℕ, x / 2 < x ∧ x ≤ x) := by
  refine ⟨?_, le_rfl, fun q => Int.gcd_one_left _, fun _ => ⟨by linarith, le_rfl⟩,
    fun _ => ⟨by linarith, le_rfl⟩⟩
  calc x ^ (3 / 5 + ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = x := Real.rpow_one x

/-- And `Q = 1` is admissible for every large `x`: `1 ≤ x · x^{-1/2} (log x)^{-B}`, so the sum
over `q ≤ Q` is not empty. -/
theorem pps_Q_one_eventually (B : ℝ) :
    ∃ x1 : ℝ, ∀ x : ℝ, x1 ≤ x → 1 ≤ x * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) := by
  obtain ⟨x1, hx1⟩ := eventually_log_rpow_le B (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨max x1 3, fun x hx => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hl : 0 < Real.log x := by linarith [one_le_log_of_three_le hx3]
  have hb := hx1 x (le_trans (le_max_left _ _) hx)
  have hp : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hl _
  have e : x * x ^ (-(1 / 2) : ℝ) = x ^ (1 / 2 : ℝ) := by
    calc x * x ^ (-(1 / 2) : ℝ) = x ^ (1 : ℝ) * x ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
  rw [e, Real.rpow_neg hl.le, ← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
  exact hb

/-! ### Headline -/

/-- **HEADLINE. The F-0008 repair, CONDITIONAL ON `PPS1984Uniform` and `Theorem5Min`.** -/
theorem theorem2Zeroed_U1495 (hP : PPS1984Uniform) (h5 : Theorem5Min) : Theorem2Zeroed :=
  theorem2Zeroed_U1493 (theorem3_of_uniform hP) h5

/-- The F-0008 repair, CONDITIONAL ON the printed Remark `PPS1984Remark` and `Theorem5Min`. -/
theorem theorem2Zeroed_U1495_remark (hR : PPS1984Remark) (h5 : Theorem5Min) :
    Theorem2Zeroed :=
  theorem2Zeroed_U1495 (uniform_of_remark hR) h5

/-- Theorem 2 in the lab's coprime reading, CONDITIONAL ON `PPS1984Uniform`, `Theorem5Min`. -/
theorem theorem2_U1495 (hP : PPS1984Uniform) (h5 : Theorem5Min) : Theorem2 :=
  theorem2_U1493 (theorem3_of_uniform hP) h5

end LeanLab.Halupczok2012
