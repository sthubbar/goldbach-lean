module

public import LeanLab.DensityGoldbach.U1472Green
public import LeanLab.PNTPort.Vinogradov.MajorArcUncond

/-!
Unit U-1478, run 20261022T1302Z-31860. P0047 Alsetri and Shao 2024, Theorem 1.2.

Before: `alsetriShao_1_2_U1472 : GreenThm21Circle3 → Green62 → AlsetriShao12`.

Here `Green62`, Green 2005 Lemma 6.2 in the regime Alsetri and Shao use, is rewritten in the
language of the lab's circle method, the von Mangoldt sum `S X α = Σ_{1 ≤ n ≤ X} Λ(n) e(nα)` of
PNTPort/Vinogradov, through the class indicator `1_{n ≡ b (W)} = W⁻¹ Σ_{k < W} e(k(n - b)/W)`:

  `ν̂_b(r) = φ(W)/(W² N) · e(rb/(WN)) · Σ_{k<W} e(-kb/W) S(X, k/W - r/(WN))  +  O(φ(W)/(WN) (ψ - θ)(X))`

with `X = W(N - 1) + b`. The cited Prop `ArcClassBound` says the twisted sum
`twS = Σ_{k<W} e(-kb/W) S(X, k/W - r/(WN))` is at most `c W² N/φ(W)` for `0 < r < N`.

* `green62_of_arcs : ArcClassBound → Green62`, PROVED.
* `arcs_of_green62 : Green62 → ArcClassBound`, PROVED: the reduction is lossless, the two Props are
  equivalent, so `ArcClassBound` is exactly the circle method content of Lemma 6.2.
* Sub-lemmas PROVED: `class_orth`, the class indicator as a `k`-average; `twS_eq`; `hatE_nuW_eq`,
  the exact identity for `ν̂_b`; `prime_sub_vm`, primes against `Λ` costs `ψ - θ`; `V_period`, the
  full period geometric sum kills the `q = 1` main term for `r ≠ 0`; `twS_minor`, if every
  `α_k = k/W - r/(WN)` is on the lab's minor arcs then `twS` is at most `W` times the lab's
  `minor_sup` bound.

What is not done: the major arc bookkeeping, the evaluation of
`Σ_k e(-kb/W) μ(q_k)/φ(q_k)` for the reduced denominators `q_k` of `k/W + a/q`, which is a
Ramanujan sum computation over the divisors of `W q`.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1478
open LeanLab.DensityGoldbach.U1446

local notation "eL" => LeanLab.PNTPort.LargeSieve.e
local notation "SV" => LeanLab.PNTPort.Vinogradov.S

/-- `X = W(N - 1) + b`, the largest `Wn + b` with `n < N`. -/
def Xc (W b N : ℕ) : ℕ := W * (N - 1) + b

/-- The twisted sum `Σ_{k<W} e(-kb/W) S(X, k/W - r/(WN))`. -/
def twS (W b N r : ℕ) : ℂ :=
  ∑ k ∈ range W, eL (-((k : ℝ) * b / W)) * SV (Xc W b N) ((k : ℝ) / W - (r : ℝ) / (W * N))

/-- **Green 2005 Lemma 6.2 in circle method form**, cited: for every `c > 0`, once `z` is large,
for `W = z#`, `b < W` reduced, all large primes `N` and `0 < r < N`, the twisted von Mangoldt sum
is at most `c W² N / φ(W)`. Equivalent to `Green62`, see `green62_of_arcs`, `arcs_of_green62`. -/
def ArcClassBound : Prop :=
  ∀ c : ℝ, 0 < c → ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ b : ℕ, b < primorial z →
    Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N →
      ∀ r : ℕ, 0 < r → r < N →
        ‖twS (primorial z) b N r‖ ≤ c * ((primorial z : ℝ) ^ 2 * N / Nat.totient (primorial z))

/-! ### Additive characters -/

lemma eL_eq_one_iff_int {t : ℝ} (h : eL t = 1) : ∃ m : ℤ, t = m := by
  have h4 := LeanLab.PNTPort.LargeSieve.four_dist0_le t
  rw [h, sub_self, norm_zero] at h4
  have h0 : LeanLab.PNTPort.LargeSieve.dist0 t = 0 :=
    le_antisymm (by linarith) (LeanLab.PNTPort.LargeSieve.dist0_nonneg t)
  unfold LeanLab.PNTPort.LargeSieve.dist0 at h0
  exact ⟨round t, by linarith [abs_eq_zero.1 h0]⟩

/-- Geometric sum of a nontrivial root of unity of order dividing `M`. -/
lemma geom_root {x : ℂ} (hx : x ≠ 1) {M : ℕ} (hM : x ^ M = 1) : ∑ k ∈ range M, x ^ k = 0 := by
  rw [geom_sum_eq hx, hM, sub_self, zero_div]

/-- **Class indicator**: `Σ_{k<W} e(k(n - b)/W) = W · 1_{n ≡ b (W)}` for `b < W`. -/
theorem class_orth {W : ℕ} (hW : 0 < W) {b : ℕ} (hb : b < W) (n : ℕ) :
    ∑ k ∈ range W, eL ((k : ℝ) * (((n : ℝ) - b) / W)) = if n % W = b then (W : ℂ) else 0 := by
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  simp_rw [LeanLab.PNTPort.LargeSieve.e_nat_mul]
  split_ifs with h
  · have hn := Nat.div_add_mod n W
    rw [h] at hn
    have : ((n : ℝ) - b) / W = ((n / W : ℕ) : ℤ) := by
      rw [div_eq_iff hWr, Int.cast_natCast]
      have : (n : ℝ) = W * (n / W : ℕ) + b := by exact_mod_cast hn.symm
      linarith
    rw [this, LeanLab.PNTPort.LargeSieve.e_int]; simp
  · apply geom_root
    · intro h1
      obtain ⟨m, hm⟩ := eL_eq_one_iff_int h1
      apply h
      rw [div_eq_iff hWr] at hm
      have hz : (n : ℤ) = W * m + b := by
        have : (n : ℝ) = W * m + b := by linarith
        exact_mod_cast this
      have h2 : (n : ℤ) % W = b := by
        rw [hz, add_comm, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb)
      have h3 : ((n % W : ℕ) : ℤ) = b := by rw [Int.natCast_mod]; exact h2
      exact_mod_cast h3
    · rw [← LeanLab.PNTPort.LargeSieve.e_nat_mul]
      have : (W : ℝ) * (((n : ℝ) - b) / W) = (((n : ℤ) - b : ℤ) : ℝ) := by
        field_simp; push_cast; ring
      rw [this, LeanLab.PNTPort.LargeSieve.e_int]

/-- `twS = W Σ_{n ≤ X, n ≡ b} Λ(n) e(-nr/(WN))`. -/
theorem twS_eq {W : ℕ} (hW : 0 < W) {b : ℕ} (hb : b < W) (N r : ℕ) :
    twS W b N r = W * ∑ n ∈ Icc 1 (Xc W b N),
      (if n % W = b then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) *
        eL ((n : ℝ) * (-((r : ℝ) / (W * N)))) := by
  unfold twS LeanLab.PNTPort.Vinogradov.S
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hk : ∀ k : ℕ, eL (-((k : ℝ) * b / W)) *
      ((ArithmeticFunction.vonMangoldt n : ℂ) * eL ((n : ℝ) * ((k : ℝ) / W - (r : ℝ) / (W * N)))) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * eL ((n : ℝ) * (-((r : ℝ) / (W * N)))) *
        eL ((k : ℝ) * (((n : ℝ) - b) / W)) := by
    intro k
    rw [mul_left_comm, ← LeanLab.PNTPort.LargeSieve.e_add, mul_assoc,
      ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 2; ring
  simp_rw [hk, ← Finset.mul_sum, class_orth hW hb n]
  split_ifs <;> ring

/-! ### The Fourier coefficient of `ν_b` -/

/-- The prime sum over the class: `Σ_{n ≤ X, n ≡ b} 1_{n prime} log n e(nθ)`. -/
def P1 (W b N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 (Xc W b N),
    (if n % W = b then (if n.Prime then (Real.log n : ℂ) else 0) else 0) * eL ((n : ℝ) * θ)

/-- The von Mangoldt sum over the class. -/
def L1 (W b N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 (Xc W b N),
    (if n % W = b then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) * eL ((n : ℝ) * θ)

/-- Reindexing `n ↦ Wn + b` from `range N` to the class `b` in `[1, X]`. -/
lemma reindex {W b N : ℕ} (hW : 0 < W) (hb : b < W) (hb1 : 1 ≤ b) (hN : 1 ≤ N) (G : ℕ → ℂ) :
    ∑ m ∈ range N, G (W * m + b) =
      ∑ n ∈ Icc 1 (Xc W b N), (if n % W = b then G n else 0) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun m _ => W * m + b) ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_range] at hm
    rw [mem_filter, mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · unfold Xc; have := Nat.mul_le_mul_left W (show m ≤ N - 1 by omega); omega
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · intro m₁ _ m₂ _ h
    exact Nat.eq_of_mul_eq_mul_left hW (by omega)
  · intro n hn
    rw [mem_filter, mem_Icc] at hn
    have hd := Nat.div_add_mod n W
    rw [hn.2] at hd
    refine ⟨n / W, ?_, hd⟩
    rw [mem_range]
    by_contra hc
    have : W * N ≤ W * (n / W) := Nat.mul_le_mul_left W (by omega)
    have hX := hn.1.2
    unfold Xc at hX
    have : W * (N - 1) + W = W * N := by rw [← Nat.mul_succ]; congr 1; omega
    omega
  · intro m _; rfl

/-- **The exact identity** `ν̂_b(r) = φ(W)/(WN) · e(rb/(WN)) · P1(-r/(WN))`. -/
theorem hatE_nuW_eq {W b N : ℕ} [NeZero N] (hW : 0 < W) (hb : b < W) (hb1 : 1 ≤ b)
    (r : ZMod N) :
    hatE N (nuW W b N) r = (((Nat.totient W : ℝ) / (W * N) : ℝ) : ℂ) *
      eL ((r.val : ℝ) * b / (W * N)) * P1 W b N (-((r.val : ℝ) / (W * N))) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  set F : ℕ → ℂ := fun m => (((if (W * m + b).Prime then (Nat.totient W : ℝ) / W *
      Real.log (W * m + b) else 0 : ℝ)) : ℂ) * eL ((m : ℝ) * (-(r.val : ℝ) / N)) with hF
  have h1 : ∑ n : ZMod N, (nuW W b N n : ℂ) * (ZMod.stdAddChar (-(r * n)) : ℂ) =
      ∑ m ∈ range N, F m := by
    rw [← LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range F]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hs : (ZMod.stdAddChar (-(r * n)) : ℂ) = eL ((n.val : ℝ) * (-(r.val : ℝ) / N)) := by
      rw [← LeanLab.PNTPort.Vinogradov.stdAddChar_neg_mul, ZMod.natCast_zmod_val, mul_comm]
    rw [hs]; rfl
  have h2 : ∑ m ∈ range N, F m = (((Nat.totient W : ℝ) / W : ℝ) : ℂ) *
      eL ((r.val : ℝ) * b / (W * N)) * P1 W b N (-((r.val : ℝ) / (W * N))) := by
    have hG : ∀ m ∈ range N, F m = (((Nat.totient W : ℝ) / W : ℝ) : ℂ) *
        eL ((r.val : ℝ) * b / (W * N)) * ((if (W * m + b).Prime then
          (Real.log ((W * m + b : ℕ) : ℝ) : ℂ) else 0) *
          eL (((W * m + b : ℕ) : ℝ) * (-((r.val : ℝ) / (W * N))))) := by
      intro m _
      simp only [hF]
      have he : eL ((m : ℝ) * (-(r.val : ℝ) / N)) = eL ((r.val : ℝ) * b / (W * N)) *
          eL (((W * m + b : ℕ) : ℝ) * (-((r.val : ℝ) / (W * N)))) := by
        rw [← LeanLab.PNTPort.LargeSieve.e_add]; congr 1; push_cast; field_simp; ring
      rw [he]
      split_ifs
      · push_cast; ring
      · push_cast; ring
    rw [Finset.sum_congr rfl hG, ← Finset.mul_sum]
    congr 1
    unfold P1
    rw [reindex hW hb hb1 hN (fun n => (if n.Prime then (Real.log n : ℂ) else 0) *
      eL ((n : ℝ) * (-((r.val : ℝ) / (W * N)))))]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  unfold hatE
  rw [h1, h2]
  push_cast
  field_simp

/-- **Primes against von Mangoldt**: `‖P1 - L1‖ ≤ ψ(X) - θ(X)`. -/
theorem prime_sub_vm (W b N : ℕ) (θ : ℝ) :
    ‖P1 W b N θ - L1 W b N θ‖ ≤ Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N) := by
  have hpsi : Chebyshev.psi (Xc W b N) =
      ∑ n ∈ Icc 1 (Xc W b N), ArithmeticFunction.vonMangoldt n := by
    unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
  have htheta : Chebyshev.theta (Xc W b N) =
      ∑ n ∈ (Icc 1 (Xc W b N)).filter Nat.Prime, Real.log n := by
    unfold Chebyshev.theta; rw [Nat.floor_natCast]; congr 1
  rw [hpsi, htheta, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold P1 L1
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← sub_mul, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one]
  have hΛ := @ArithmeticFunction.vonMangoldt_nonneg n
  by_cases hc : n % W = b
  · by_cases hp : n.Prime
    · simp [hc, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [hc, hp, if_true, if_false, zero_sub, norm_neg, sub_zero, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hΛ, le_refl]
  · by_cases hp : n.Prime
    · simp [hc, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [hc, hp, if_false, sub_zero, norm_zero]; exact hΛ

/-! ### The reduction -/

lemma two_le_primorial {z : ℕ} (hz : 2 ≤ z) : 2 ≤ primorial z := by
  have h := prime_dvd_primorial' Nat.prime_two hz
  exact Nat.le_of_dvd (primorial_pos z) h

lemma one_le_b {W b : ℕ} (hW : 2 ≤ W) (hcop : Nat.Coprime b W) : 1 ≤ b := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; rw [Nat.coprime_zero_left] at hcop; omega
  · exact h

lemma totient_le_real (W : ℕ) : (Nat.totient W : ℝ) ≤ W := by exact_mod_cast Nat.totient_le W

lemma Xc_le {W b N : ℕ} (hb : b < W) (hN : 1 ≤ N) : (Xc W b N : ℝ) ≤ W * N := by
  have : Xc W b N ≤ W * N := by
    unfold Xc
    have : W * (N - 1) + W = W * N := by rw [← Nat.mul_succ]; congr 1; omega
    omega
  exact_mod_cast this

/-- The `ψ - θ` error is `o(N)`: `C √(WN) ≤ ε N` once `N ≥ C² W/ε²`. -/
lemma sqrt_err {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (W N : ℕ)
    (hN : C ^ 2 * W / ε ^ 2 ≤ N) : C * Real.sqrt (W * N) ≤ ε * N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : C ^ 2 * (W * N) ≤ (ε * N) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hN
    nlinarith
  have h2 : C * Real.sqrt (W * N) = Real.sqrt (C ^ 2 * (W * N)) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ C ^ 2) ((W : ℝ) * N), Real.sqrt_sq hC.le]
  rw [h2, ← Real.sqrt_sq (show 0 ≤ ε * N by positivity)]
  exact Real.sqrt_le_sqrt h1

/-- The main estimate, both directions: `‖ν̂_b(r)‖` and `‖twS‖ φ(W)/(W² N)` differ by at most
`φ(W)/(WN)` times `ψ(X) - θ(X)`. -/
lemma hat_vs_twS {W b N : ℕ} [NeZero N] (hW : 0 < W) (hb : b < W) (hb1 : 1 ≤ b) (r : ZMod N) :
    |‖hatE N (nuW W b N) r‖ - (Nat.totient W : ℝ) / (W ^ 2 * N) * ‖twS W b N r.val‖| ≤
      (Nat.totient W : ℝ) / (W * N) *
        (Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N)) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set θ : ℝ := -((r.val : ℝ) / (W * N))
  have hc : (0 : ℝ) ≤ (Nat.totient W : ℝ) / (W * N) := by positivity
  have hH : ‖hatE N (nuW W b N) r‖ = (Nat.totient W : ℝ) / (W * N) * ‖P1 W b N θ‖ := by
    rw [hatE_nuW_eq hW hb hb1, norm_mul, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hT : ‖twS W b N r.val‖ = W * ‖L1 W b N θ‖ := by
    rw [twS_eq hW hb, norm_mul, Complex.norm_natCast]; rfl
  rw [hH, hT]
  have e1 : (Nat.totient W : ℝ) / (W ^ 2 * N) * (W * ‖L1 W b N θ‖) =
      (Nat.totient W : ℝ) / (W * N) * ‖L1 W b N θ‖ := by field_simp
  rw [e1, ← mul_sub, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (abs_norm_sub_norm_le _ _).trans (prime_sub_vm W b N θ)

/-- **`Green62` from the circle method form, PROVED.** -/
theorem green62_of_arcs (H : ArcClassBound) : Green62 := by
  intro c hc
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₀ 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨z₀, hz₀⟩ := H (c / 2) (by positivity)
  refine ⟨max z₀ 2, fun z hz b hb hcop => ?_⟩
  set W := primorial z
  have hW2 : 2 ≤ W := two_le_primorial (le_of_max_le_right hz)
  have hW : 0 < W := by omega
  have hb1 : 1 ≤ b := one_le_b hW2 hcop
  obtain ⟨N₁, hN₁⟩ := hz₀ z (le_of_max_le_left hz) b hb hcop
  refine ⟨max N₁ (⌈C ^ 2 * W / (c / 2) ^ 2⌉₊ + 1), fun N _ hNp hN r hr => ?_⟩
  have hN1 : 1 ≤ N := hNp.one_lt.le
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  have hφW := totient_le_real W
  have hrv : 0 < r.val := by
    rcases Nat.eq_zero_or_pos r.val with h | h
    · exact absurd ((ZMod.val_eq_zero r).1 h) hr
    · exact h
  have hT := hN₁ N hNp (le_of_max_le_left hN) r.val hrv (ZMod.val_lt r)
  have hmain := hat_vs_twS hW hb hb1 r
  -- the twisted term
  have h1 : (Nat.totient W : ℝ) / (W ^ 2 * N) * ‖twS W b N r.val‖ ≤ c / 2 := by
    calc (Nat.totient W : ℝ) / (W ^ 2 * N) * ‖twS W b N r.val‖
        ≤ (Nat.totient W : ℝ) / (W ^ 2 * N) * (c / 2 * ((W : ℝ) ^ 2 * N / Nat.totient W)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = c / 2 := by field_simp
  -- the ψ - θ term
  have hX := Xc_le (N := N) hb hN1
  have hNc : C ^ 2 * W / (c / 2) ^ 2 ≤ (N : ℝ) := by
    have := Nat.le_ceil (C ^ 2 * W / (c / 2) ^ 2)
    have h' : ((⌈C ^ 2 * W / (c / 2) ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (show ⌈C ^ 2 * W / (c / 2) ^ 2⌉₊ ≤ N by omega)
    linarith
  have hsq := sqrt_err hC (show 0 < c / 2 by positivity) W N hNc
  have hpt : Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N) ≤
      C * Real.sqrt (W * N) := by
    refine (hC₀ _).trans ?_
    have hs : Real.sqrt (Xc W b N) ≤ Real.sqrt (W * N) := Real.sqrt_le_sqrt hX
    have hs0 : 0 ≤ Real.sqrt (Xc W b N) := Real.sqrt_nonneg _
    rcases le_or_gt C₀ 0 with h0 | h0
    · nlinarith [Real.sqrt_nonneg ((W : ℝ) * N)]
    · calc C₀ * Real.sqrt (Xc W b N) ≤ C * Real.sqrt (Xc W b N) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
        _ ≤ C * Real.sqrt (W * N) := mul_le_mul_of_nonneg_left hs hC.le
  have h2 : (Nat.totient W : ℝ) / (W * N) *
      (Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N)) ≤ c / 2 := by
    have hfac : (Nat.totient W : ℝ) / (W * N) ≤ 1 / N := by
      rw [div_le_div_iff₀ (by positivity) hNr]; nlinarith
    have hpt0 : 0 ≤ Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N) :=
      sub_nonneg.2 (Chebyshev.theta_le_psi _)
    calc (Nat.totient W : ℝ) / (W * N) * (Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N))
        ≤ 1 / N * (C * Real.sqrt (W * N)) :=
          mul_le_mul hfac hpt hpt0 (by positivity)
      _ ≤ 1 / N * (c / 2 * N) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = c / 2 := by field_simp
  have := (abs_le.1 hmain).2
  linarith

/-- **The converse, PROVED**: `Green62` gives `ArcClassBound`, so the reduction is lossless. -/
theorem arcs_of_green62 (H : Green62) : ArcClassBound := by
  intro c hc
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₀ 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨z₀, hz₀⟩ := H (c / 2) (by positivity)
  refine ⟨max z₀ 2, fun z hz b hb hcop => ?_⟩
  set W := primorial z
  have hW2 : 2 ≤ W := two_le_primorial (le_of_max_le_right hz)
  have hW : 0 < W := by omega
  have hb1 : 1 ≤ b := one_le_b hW2 hcop
  obtain ⟨N₁, hN₁⟩ := hz₀ z (le_of_max_le_left hz) b hb hcop
  refine ⟨max N₁ (⌈C ^ 2 * W / (c / 2) ^ 2⌉₊ + 1), fun N hNp hN r hr0 hrN => ?_⟩
  haveI : NeZero N := ⟨hNp.ne_zero⟩
  have hN1 : 1 ≤ N := hNp.one_lt.le
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  have hφW := totient_le_real W
  set rr : ZMod N := (r : ZMod N)
  have hval : rr.val = r := ZMod.val_natCast_of_lt hrN
  have hrr : rr ≠ 0 := by
    intro h; have := congrArg ZMod.val h; rw [hval, ZMod.val_zero] at this; omega
  have hG := hN₁ N hNp (le_of_max_le_left hN) rr hrr
  have hmain := hat_vs_twS hW hb hb1 rr
  rw [hval] at hmain
  have hX := Xc_le (N := N) hb hN1
  have hNc : C ^ 2 * W / (c / 2) ^ 2 ≤ (N : ℝ) := by
    have := Nat.le_ceil (C ^ 2 * W / (c / 2) ^ 2)
    have h' : ((⌈C ^ 2 * W / (c / 2) ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (show ⌈C ^ 2 * W / (c / 2) ^ 2⌉₊ ≤ N by omega)
    linarith
  have hsq := sqrt_err hC (show 0 < c / 2 by positivity) W N hNc
  have hpt : Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N) ≤
      C * Real.sqrt (W * N) := by
    refine (hC₀ _).trans ?_
    have hs : Real.sqrt (Xc W b N) ≤ Real.sqrt (W * N) := Real.sqrt_le_sqrt hX
    have hs0 : 0 ≤ Real.sqrt (Xc W b N) := Real.sqrt_nonneg _
    rcases le_or_gt C₀ 0 with h0 | h0
    · nlinarith [Real.sqrt_nonneg ((W : ℝ) * N)]
    · calc C₀ * Real.sqrt (Xc W b N) ≤ C * Real.sqrt (Xc W b N) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
        _ ≤ C * Real.sqrt (W * N) := mul_le_mul_of_nonneg_left hs hC.le
  have h2 : (Nat.totient W : ℝ) / (W * N) *
      (Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N)) ≤ c / 2 := by
    have hfac : (Nat.totient W : ℝ) / (W * N) ≤ 1 / N := by
      rw [div_le_div_iff₀ (by positivity) hNr]; nlinarith
    have hpt0 : 0 ≤ Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N) :=
      sub_nonneg.2 (Chebyshev.theta_le_psi _)
    calc (Nat.totient W : ℝ) / (W * N) * (Chebyshev.psi (Xc W b N) - Chebyshev.theta (Xc W b N))
        ≤ 1 / N * (C * Real.sqrt (W * N)) :=
          mul_le_mul hfac hpt hpt0 (by positivity)
      _ ≤ 1 / N * (c / 2 * N) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = c / 2 := by field_simp
  have hlow := (abs_le.1 hmain).1
  have hk : (Nat.totient W : ℝ) / (W ^ 2 * N) * ‖twS W b N r‖ ≤ c := by linarith
  have hpos : (0 : ℝ) < (Nat.totient W : ℝ) / (W ^ 2 * N) := by positivity
  calc ‖twS W b N r‖ = ((W : ℝ) ^ 2 * N / Nat.totient W) *
        ((Nat.totient W : ℝ) / (W ^ 2 * N) * ‖twS W b N r‖) := by field_simp
    _ ≤ ((W : ℝ) ^ 2 * N / Nat.totient W) * c := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = c * ((W : ℝ) ^ 2 * N / Nat.totient W) := by ring

/-! ### Sub-lemmas towards `ArcClassBound` -/

/-- **The `q = 1` main term vanishes**: the geometric sum `V(β) = Σ_{n ≤ X} e(nβ)` at
`β = -r/(WN)`, `0 < r < N`, is at most `W` in norm, since the full period sum over `n ≤ WN`
vanishes and `WN - X < W`. -/
theorem V_period {W b N r : ℕ} (hW : 0 < W) (hb : b < W) (hr : 0 < r) (hrN : r < N) :
    ‖LeanLab.PNTPort.Vinogradov.V (Xc W b N) (-((r : ℝ) / (W * N)))‖ ≤ W := by
  have hN1 : 1 ≤ N := by omega
  set M := W * N with hM
  have hXM : Xc W b N ≤ M := by
    unfold Xc; have : W * (N - 1) + W = W * N := by rw [← Nat.mul_succ]; congr 1; omega
    omega
  have hMX : M - Xc W b N ≤ W := by
    unfold Xc; have : W * (N - 1) + W = W * N := by rw [← Nat.mul_succ]; congr 1; omega
    omega
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set x : ℂ := eL (-((r : ℝ) / (W * N))) with hx
  -- the full period sum vanishes
  have hfull : ∑ n ∈ Icc 1 M, eL ((n : ℝ) * (-((r : ℝ) / (W * N)))) = 0 := by
    have hx1 : x ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := eL_eq_one_iff_int h1
      have hm' : (r : ℝ) = -(m : ℝ) * (W * N) := by
        field_simp at hm; linarith
      have hz : (r : ℤ) = -m * (W * N) := by exact_mod_cast hm'
      have hpos : (0 : ℤ) < W * N := by positivity
      have hlt : (r : ℤ) < W * N := by
        have : r < W * N := lt_of_lt_of_le hrN (Nat.le_mul_of_pos_left N hW)
        exact_mod_cast this
      have hr0 : (0 : ℤ) < r := by exact_mod_cast hr
      rcases lt_trichotomy (-m) 0 with h | h | h
      · nlinarith
      · rw [h] at hz; omega
      · have : (1 : ℤ) ≤ -m := h
        nlinarith
    have hxM : x ^ M = 1 := by
      rw [hx, ← LeanLab.PNTPort.LargeSieve.e_nat_mul]
      have : (M : ℝ) * (-((r : ℝ) / (W * N))) = ((-(r : ℤ) : ℤ) : ℝ) := by
        rw [hM]; push_cast; field_simp
      rw [this, LeanLab.PNTPort.LargeSieve.e_int]
    have hshift : ∑ n ∈ Icc 1 M, eL ((n : ℝ) * (-((r : ℝ) / (W * N)))) =
        x * ∑ k ∈ range M, x ^ k := by
      rw [Finset.mul_sum]
      have : Icc 1 M = (range M).map ⟨fun k => k + 1, add_left_injective 1⟩ := by
        ext n; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
        constructor
        · intro h; exact ⟨n - 1, by omega, by omega⟩
        · rintro ⟨k, hk, rfl⟩; omega
      rw [this, Finset.sum_map]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.Embedding.coeFn_mk]
      rw [LeanLab.PNTPort.LargeSieve.e_nat_mul, pow_succ, mul_comm]
    rw [hshift, geom_root hx1 hxM, mul_zero]
  -- split off the tail
  have hsplit : Icc 1 M = Icc 1 (Xc W b N) ∪ Ioc (Xc W b N) (Xc W b N + (M - Xc W b N)) := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 (Xc W b N)) (Ioc (Xc W b N) (Xc W b N + (M - Xc W b N))) := by
    rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj] at hfull
  unfold LeanLab.PNTPort.Vinogradov.V
  rw [eq_neg_of_add_eq_zero_left hfull, norm_neg]
  refine (LeanLab.PNTPort.Vinogradov.norm_sum_Ioc_e_le _ _ _).trans ?_
  refine (LeanLab.PNTPort.Vinogradov.G_le _ _).trans ?_
  exact_mod_cast hMX

/-- **Minor arcs**: if every `α_k = k/W - r/(WN)` lies on the lab's minor arcs, then `twS` is at
most `W` times the lab's `minor_sup` bound. -/
theorem twS_minor {W b N r P Q : ℕ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hQX : Q ≤ Xc W b N)
    (hmin : ∀ k < W, LeanLab.PNTPort.Vinogradov.MinorAt P Q ((k : ℝ) / W - (r : ℝ) / (W * N))) :
    ‖twS W b N r‖ ≤ W * (300 * (((Xc W b N : ℕ) : ℝ) / Real.sqrt P +
      ((Xc W b N : ℕ) : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt ((Xc W b N : ℕ) * Q)) *
      (1 + Real.log (Xc W b N : ℕ)) ^ 4) := by
  unfold twS
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ range W, ‖eL (-((k : ℝ) * b / W)) *
      SV (Xc W b N) ((k : ℝ) / W - (r : ℝ) / (W * N))‖ ≤
      300 * (((Xc W b N : ℕ) : ℝ) / Real.sqrt P + ((Xc W b N : ℕ) : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((Xc W b N : ℕ) * Q)) * (1 + Real.log (Xc W b N : ℕ)) ^ 4 := by
    intro k hk
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
    exact LeanLab.PNTPort.Vinogradov.minor_sup hP hQ hQX (hmin k (mem_range.1 hk))
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-! ### Headline and vacuity -/

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenThm21Circle3` and `ArcClassBound`. -/
theorem alsetriShao_1_2_U1478 (H21 : LeanLab.DensityGoldbach.U1472.GreenThm21Circle3)
    (HA : ArcClassBound) : AlsetriShao12 :=
  LeanLab.DensityGoldbach.U1472.alsetriShao_1_2_U1472 H21 (green62_of_arcs HA)

/-- Vacuity of `ArcClassBound`: its hypotheses hold at `z = 2`, `W = 2`, `b = 1`, `N = 3`,
`r = 1`, and then the right side `c W² N/φ(W) = 12 c` is positive. -/
theorem vacuity_Arc : 1 < primorial 2 ∧ Nat.Coprime 1 (primorial 2) ∧ Nat.Prime 3 ∧
    (0 : ℕ) < 1 ∧ 1 < 3 ∧ Nat.totient (primorial 2) = 1 := by
  have h : primorial 2 = 2 := by decide
  rw [h]; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by decide⟩

end LeanLab.DensityGoldbach.U1478
