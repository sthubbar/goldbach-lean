module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.ExceptionalSet.Statements
public import LeanLab.ChenExplicit.Statements
public import LeanLab.Brun1919.Statements
public import LeanLab.DERZ1997.Statements

/-!
P0070 A. Perelli, J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82 (1992), 355-372, numdam CM_1992__82_3_355_0.
Every formula below was read on rendered page images, the text layer drops displays.

* Theorem, p. 356: mean square of `Ψ(N,2k) - 𝔖(2k)(N-2k)` over `V ≤ k ≤ V+H`
  is `≪ H N² L^{-A}` for `N^{1/2+ε} < H < N/4`, `0 ≤ V < N/4`. CITED, not proved.
* Corollary, p. 356: conjecture (1) holds for all `k` in `[V, V+H]` but `O(H L^{-B})`.
  PROVED here from the Theorem, Chebyshev counting.
* Goldbach remark, p. 356, the short interval exceptional set for `r(2n)`. CITED, Prop only.
* The implicit exponential sum result, p. 357. CITED, Prop only.
* Reductions (6) and (7), p. 359. CITED, Prop only.
* Hardy and Littlewood under GRH, `E(X) ≪ X^{1/2+ε}`, as quoted p. 356. CITED, not proved.
* PROVED: basic facts on `Ψ`, `𝔖`, the link to twin primes for `k = 1`, the relation
  of `Ψ` with `Ψ₂` with its boundary term, and the exponent arithmetic of Section 6.

AI-written Lean code, Claude, 2026-10-18, run 20261018T1603Z-12862.
Checked only by the Lean kernel. Binary Goldbach and the twin prime conjecture are OPEN.
-/

@[expose] public section

namespace LeanLab.PerelliPintz1992
open Real Filter Topology ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ### Definitions, Section 1 p. 355 and Section 2 p. 357 -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `Ψ(N,2k) = Σ_{N ≤ m,n ≤ 2N, n - m = 2k} Λ(m)Λ(n)`, p. 355. -/
noncomputable def Psi (N k : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc N (2 * N)).filter (fun m => m + 2 * k ≤ 2 * N), Λ m * Λ (m + 2 * k)

/-- Wolke's `Ψ₂(N,2k) = Σ_{2k < n ≤ N} Λ(n)Λ(n-2k)`, p. 355. -/
noncomputable def Psi2 (N k : ℕ) : ℝ := ∑ n ∈ Finset.Ioc (2 * k) N, Λ n * Λ (n - 2 * k)

/-- The twin prime constant `∏_{p>2} (1 - 1/(p-1)²)`, reused from `ChenExplicit`. -/
noncomputable abbrev twinC : ℝ := LeanLab.ChenExplicit.twinC

/-- `S2k k` is the paper's `𝔖(2k) = 2 ∏_{p>2} (1 - 1/(p-1)²) ∏_{p ∣ k, p>2} (p-1)/(p-2)`. -/
noncomputable def S2k (k : ℕ) : ℝ :=
  2 * twinC * ∏ p ∈ k.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- `L = log N`. -/
noncomputable def L (N : ℝ) : ℝ := Real.log N

/-- The error in conjecture (1): `Ψ(N,2k) - 𝔖(2k)(N-2k)`. -/
noncomputable def err (N k : ℕ) : ℝ := Psi N k - S2k k * ((N : ℝ) - 2 * k)

/-- The positive `k` in `[V, V+H]`, the paper takes `k` a positive integer. -/
def kRange (V H : ℕ) : Finset ℕ := (Finset.Icc V (V + H)).filter (1 ≤ ·)

/-- Conjecture (1), p. 355, OPEN: `Ψ(N,2k) = 𝔖(2k)(N-2k) + O(N L^{-A})` for every `A`,
uniformly in `1 ≤ k`, `2k ≤ N`. -/
def Conjecture1 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ N k : ℕ, 2 ≤ N → 1 ≤ k → 2 * k ≤ N →
    |err N k| ≤ C * N / L N ^ A

/-! ### The Theorem and the Corollary, p. 356 -/

/-- **Theorem**, p. 356. Let `0 < ε < 1/2`, `A > 0`, `N^{1/2+ε} < H < N/4`. Then for any
`0 ≤ V < N/4`, `Σ_{k=V}^{V+H} |Ψ(N,2k) - 𝔖(2k)(N-2k)|² ≪_{ε,A} H N² L^{-A}`.
The constant is ineffective, Siegel's theorem. -/
def MainTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N H V : ℕ, N0 ≤ N →
    (N : ℝ) ^ (1 / 2 + ε) < H → (H : ℝ) < N / 4 → (V : ℝ) < N / 4 →
    ∑ k ∈ kRange V H, err N k ^ 2 ≤ C * H * N ^ 2 / L N ^ A


/-- The `k` in `[V, V+H]` where (1) fails at level `A`: `|Ψ(N,2k) - 𝔖(2k)(N-2k)| > N L^{-A}`. -/
noncomputable def twinExc (N V H : ℕ) (A : ℝ) : ℕ :=
  ((kRange V H).filter (fun k => (N : ℝ) / L N ^ A < |err N k|)).card

/-- **Corollary**, p. 356. For `A, B > 0`, `0 ≤ V < N/4`, `N^{1/2+ε} < H < N/4`, (1) holds for
all `V ≤ k ≤ V+H` but `O(H L^{-B})` exceptions. -/
def Corollary : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A B : ℝ, 0 < A → 0 < B → ∃ C N0 : ℝ, ∀ N H V : ℕ, N0 ≤ N →
    (N : ℝ) ^ (1 / 2 + ε) < H → (H : ℝ) < N / 4 → (V : ℝ) < N / 4 →
    (twinExc N V H A : ℝ) ≤ C * H / L N ^ B

/-! ### The Goldbach remark, the exponential sum form, p. 356-357 -/

/-- `r(m) = Σ_{h+k=m} Λ(h)Λ(k)`. -/
noncomputable def r (m : ℕ) : ℝ := ∑ h ∈ Finset.range (m + 1), Λ h * Λ (m - h)

/-- The Goldbach remark, p. 356: for `I = [x, x + x^{1/2+ε}]`, all even `2n ∈ I` but
`O(|I| L^{-B})` exceptions satisfy `r(2n) = 2n𝔖(2n) + O(x log^{-A} x)`. -/
def GoldbachRemark : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A B : ℝ, 0 < A → 0 < B → ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    ((((Finset.Icc ⌈x / 2⌉₊ ⌊(x + x ^ (1 / 2 + ε)) / 2⌋₊).filter
        (fun n => C * x / Real.log x ^ A < |r (2 * n) - 2 * n * S2k n|)).card : ℕ) : ℝ) ≤
      C * x ^ (1 / 2 + ε) / Real.log x ^ B


/-- The result proved implicitly, p. 357: for `N^{1/2+ε} < H < N/2`, `ξ = a/q + η`,
`|η| ≤ 1/(q√N)`, `q ≤ N^{1/2}`, `(a,q) = 1`, for any `A > 0`,
`Σ_{n=N}^{2N} |Σ_{m=n}^{n+H} Λ(m)e(mξ) - μ(q)/φ(q) Σ_{m=n}^{n+H} e(mη)|² ≪ H² N L^{-A}`
uniformly for `ξ ∈ [0,1]`. -/
def ExpSumAverage : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N H : ℕ, N0 ≤ N →
    (N : ℝ) ^ (1 / 2 + ε) < H → (H : ℝ) < N / 2 →
    ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) → Nat.Coprime a q →
    ∀ η : ℝ, |η| ≤ 1 / (q * Real.sqrt N) → 0 ≤ (a : ℝ) / q + η → (a : ℝ) / q + η ≤ 1 →
      ∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc n (n + H), (Λ m : ℂ) * e (m * ((a : ℝ) / q + η)) -
          ((((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) * ∑ m ∈ Finset.Icc n (n + H), e (m * η)‖ ^ 2 ≤
        C * (H : ℝ) ^ 2 * N / L N ^ A


/-! ### The reductions (6) and (7), Sections 2 and 3, p. 357-359 -/

/-- `S(α) = Σ_{n=N}^{2N} Λ(n)e(nα)`. -/
noncomputable def S (N : ℕ) (α : ℝ) : ℂ := ∑ n ∈ Finset.Icc N (2 * N), (Λ n : ℂ) * e (n * α)

/-- `B = 2A + 100`. -/
def Bexp (A : ℝ) : ℝ := 2 * A + 100

/-- The major arcs `𝔐 = ⋃_{q ≤ L^{B/2}} ⋃_{(a,q)=1} (a/q - L^B/(qN), a/q + L^B/(qN))`,
`a` from `1` to `q`, p. 357. -/
noncomputable def majorArcs (N : ℕ) (A : ℝ) : Set ℝ :=
  ⋃ q ∈ {q : ℕ | 1 ≤ q ∧ (q : ℝ) ≤ L N ^ (Bexp A / 2)},
    ⋃ a ∈ {a : ℕ | 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q},
      Set.Ioo ((a : ℝ) / q - L N ^ Bexp A / (q * N)) ((a : ℝ) / q + L N ^ Bexp A / (q * N))

/-- `Q = N^{1/2}/2`, the minor arcs `𝔪 = (1/Q, 1 + 1/Q) \ 𝔐`. -/
noncomputable def minorArcs (N : ℕ) (A : ℝ) : Set ℝ :=
  Set.Ioo (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2)) (1 + 1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2)) \ majorArcs N A

/-- Estimate (6), p. 359, with `H = N^{1/2+ε}` and `ε` small as Section 2 assumes:
`Σ_{k=V}^{V+H} |∫_𝔐 |S(α)|² e(-2kα) dα - 𝔖(2k)(N-2k)|² ≪ H N² L^{-A}`. -/
def Estimate6 : Prop :=
  ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N V : ℕ,
    N0 ≤ N → (V : ℝ) < N / 4 →
    ∑ k ∈ (Finset.Icc V (V + ⌊(N : ℝ) ^ (1 / 2 + ε)⌋₊)).filter (1 ≤ ·),
      ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (S2k k * ((N : ℝ) - 2 * k) : ℝ)‖ ^ 2 ≤
      C * (N : ℝ) ^ (1 / 2 + ε) * N ^ 2 / L N ^ A

/-- Estimate (7), p. 359: `∫_{(ξ - 1/H, ξ + 1/H) ∩ 𝔪} |S(α)|² dα ≪ N L^{-A-1}` uniformly for
`ξ ∈ [0,1]`, with `H = N^{1/2+ε}`. -/
def Estimate7 : Prop :=
  ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N : ℕ,
    N0 ≤ N → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
    ∫ α in Set.Ioo (ξ - 1 / (N : ℝ) ^ (1 / 2 + ε)) (ξ + 1 / (N : ℝ) ^ (1 / 2 + ε)) ∩
        minorArcs N A, ‖S N α‖ ^ 2 ≤ C * N / L N ^ (A + 1)



/-! ### Hardy and Littlewood under GRH, quoted p. 356 -/

/-- `E(X) ≪ X^{1/2+ε}` for every `ε > 0`, on the lab's count `ExceptionalSet.E`. -/
def HLBound : Prop := ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (1 / 2 + ε)


/-! ### PROVED: the Corollary from the Theorem -/

theorem L_pos {N : ℕ} (hN : 2 ≤ N) : 0 < L N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))

theorem twinExc_le_of_sum {N V H : ℕ} {A M : ℝ} (hN : 2 ≤ N)
    (hsum : ∑ k ∈ kRange V H, err N k ^ 2 ≤ M) :
    (twinExc N V H A : ℝ) * ((N : ℝ) / L N ^ A) ^ 2 ≤ M := by
  have hL := L_pos hN
  have hpos : 0 ≤ (N : ℝ) / L N ^ A := by positivity
  unfold twinExc
  set T := (kRange V H).filter (fun k => (N : ℝ) / L N ^ A < |err N k|)
  calc (T.card : ℝ) * ((N : ℝ) / L N ^ A) ^ 2 = ∑ _k ∈ T, ((N : ℝ) / L N ^ A) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ T, err N k ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := (Finset.mem_filter.mp hk).2
        have : ((N : ℝ) / L N ^ A) ^ 2 ≤ |err N k| ^ 2 :=
          pow_le_pow_left₀ hpos hk'.le 2
        simpa [sq_abs] using this
    _ ≤ ∑ k ∈ kRange V H, err N k ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
    _ ≤ M := hsum

/-- The Corollary follows from the Theorem, take `A' = 2A + B` and count. -/
theorem corollary_of_mainTheorem (h : MainTheorem) : Corollary := by
  intro ε hε hε2 A B hA hB
  obtain ⟨C, N0, hC⟩ := h ε hε hε2 (2 * A + B) (by linarith)
  refine ⟨C, max N0 2, fun N H V hN h1 h2 h3 => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hN2' : 2 ≤ N := by exact_mod_cast hN2
  have hL := L_pos hN2'
  have hNpos : (0 : ℝ) < N := by linarith
  have key := twinExc_le_of_sum (A := A) hN2' (hC N H V hN0 h1 h2 h3)
  have hLA : 0 < L N ^ A := Real.rpow_pos_of_pos hL A
  have hLB : 0 < L N ^ B := Real.rpow_pos_of_pos hL B
  have hsplit : L N ^ (2 * A + B) = (L N ^ A) ^ 2 * L N ^ B := by
    rw [Real.rpow_add hL, show 2 * A = A + A by ring, Real.rpow_add hL]; ring
  rw [hsplit, div_pow] at key
  have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hLB]
  have e1 : (twinExc N V H A : ℝ) * ((N : ℝ) ^ 2 / (L N ^ A) ^ 2) * ((L N ^ A) ^ 2 * L N ^ B) ≤
      C * H * N ^ 2 / ((L N ^ A) ^ 2 * L N ^ B) * ((L N ^ A) ^ 2 * L N ^ B) := by
    gcongr
  have hD : (0 : ℝ) < (L N ^ A) ^ 2 * L N ^ B := by positivity
  rw [div_mul_cancel₀ _ hD.ne'] at e1
  have e2 : (twinExc N V H A : ℝ) * ((N : ℝ) ^ 2 / (L N ^ A) ^ 2) * ((L N ^ A) ^ 2 * L N ^ B) =
      ((twinExc N V H A : ℝ) * L N ^ B) * (N : ℝ) ^ 2 := by
    field_simp
  rw [e2] at e1
  have e3 : C * H * (N : ℝ) ^ 2 = (C * H) * (N : ℝ) ^ 2 := by ring
  rw [e3] at e1
  exact le_of_mul_le_mul_right e1 hN2pos

/-! ### PROVED: basic facts on `Ψ`, `𝔖`, and the case `k = 1` -/

theorem Psi_nonneg (N k : ℕ) : 0 ≤ Psi N k :=
  Finset.sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-- `Ψ(N,2k) = 0` once `2k > N`, the difference `n - m` never exceeds `N`. -/
theorem Psi_eq_zero_of_lt {N k : ℕ} (h : N < 2 * k) : Psi N k = 0 := by
  unfold Psi
  rw [Finset.sum_eq_zero]
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  omega

/-- A prime pair `p, p + 2k` with `N ≤ p` and `p + 2k ≤ 2N` makes `Ψ(N,2k) ≥ log p log(p+2k)`. -/
theorem Psi_ge_of_primes {N k p : ℕ} (hp : p.Prime) (hq : (p + 2 * k).Prime) (h1 : N ≤ p)
    (h2 : p + 2 * k ≤ 2 * N) : Real.log p * Real.log (p + 2 * k : ℕ) ≤ Psi N k := by
  unfold Psi
  have hmem : p ∈ (Finset.Icc N (2 * N)).filter (fun m => m + 2 * k ≤ 2 * N) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have := Finset.single_le_sum (f := fun m => Λ m * Λ (m + 2 * k))
    (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) hmem
  simpa [vonMangoldt_apply_prime hp, vonMangoldt_apply_prime hq] using this

/-- The case `k = 1`: a twin pair `p, p + 2` in `[N, 2N]`, Brun's `IsTwin`, gives `Ψ(N,2) > 0`. -/
theorem Psi_one_pos_of_twin {N p : ℕ} (hp : LeanLab.Brun1919.IsTwin p) (h1 : N ≤ p)
    (h2 : p + 2 ≤ 2 * N) : 0 < Psi N 1 := by
  have h := Psi_ge_of_primes (k := 1) hp.1 hp.2 h1 (by omega)
  have a : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.1.one_lt)
  have b : 0 < Real.log (p + 2 * 1 : ℕ) := Real.log_pos (by exact_mod_cast (by
    have := hp.1.one_lt; omega))
  exact lt_of_lt_of_le (mul_pos a b) h

/-- Contrapositive: `Ψ(N,2) = 0` means no twin pair in `[N, 2N]`. -/
theorem no_twin_of_Psi_one_eq_zero {N : ℕ} (h : Psi N 1 = 0) :
    ∀ p, LeanLab.Brun1919.IsTwin p → N ≤ p → p + 2 ≤ 2 * N → False :=
  fun p hp h1 h2 => (Psi_one_pos_of_twin hp h1 h2).ne' h

/-- `𝔖(2) = 2 C₂`, the twin prime constant times two. -/
theorem S2k_one : S2k 1 = 2 * twinC := by simp [S2k]

/-- `𝔖(2k)` only sees the odd prime factors of `k`: `𝔖(2·2^j) = 2 C₂`. -/
theorem S2k_two_pow (j : ℕ) : S2k (2 ^ j) = 2 * twinC := by
  unfold S2k
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [Nat.primeFactors_prime_pow hj.ne' Nat.prime_two]
    simp [Finset.filter_singleton]

theorem twinC_nonneg : 0 ≤ twinC := by
  apply tprod_nonneg
  intro p
  have h3 : (3 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.2
  have h4 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

/-- Each factor `(p-1)/(p-2)` is at least `1`, so `𝔖(2k) ≥ 𝔖(2) = 2 C₂`. -/
theorem S2k_ge (k : ℕ) : 2 * twinC ≤ S2k k := by
  unfold S2k
  have hprod : 1 ≤ ∏ p ∈ k.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    rw [le_div_iff₀ (by linarith)]; linarith
  have := twinC_nonneg
  nlinarith

/-- Conjecture (1) makes the exceptional count of the Corollary vanish for `N` large, so
the Corollary is a statement about how often (1) can fail. -/
theorem twinExc_eq_zero_of_conjecture1 (h : Conjecture1) (A : ℝ) (hA : 0 < A) :
    ∃ N0 : ℕ, ∀ N V H : ℕ, N0 ≤ N → 2 * (V + H) ≤ N → twinExc N V H A = 0 := by
  obtain ⟨C, hC⟩ := h (A + 1) (by linarith)
  -- `C N / L^{A+1} ≤ N / L^A` once `L N ≥ max C 1`
  have hlog : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N1, hN1⟩ := (hlog.eventually_ge_atTop (max C 1)).exists_forall_of_atTop
  refine ⟨max N1 2, fun N V H hN hVH => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hL := L_pos hN2
  have hLbig : max C 1 ≤ L N := hN1 N (le_of_max_le_left hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold twinExc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hlt
  simp only [kRange, Finset.mem_filter, Finset.mem_Icc] at hk
  have hb := hC N k hN2 hk.2 (by omega)
  have hLA : 0 < L N ^ A := Real.rpow_pos_of_pos hL A
  have hsplit : L N ^ (A + 1) = L N ^ A * L N := by
    rw [Real.rpow_add hL, Real.rpow_one]
  rw [hsplit] at hb
  have : C * N / (L N ^ A * L N) ≤ N / L N ^ A := by
    rw [div_le_div_iff₀ (by positivity) hLA]
    have hC1 : C ≤ L N := le_trans (le_max_left _ _) hLbig
    have : C * N * L N ^ A ≤ L N * N * L N ^ A := by gcongr
    nlinarith
  linarith

/-! ### PROVED: `Ψ` and `Ψ₂`, the relation of p. 356 with its boundary term -/

theorem Psi_eq_sum_range {N k : ℕ} (hk : 2 * k ≤ N) :
    Psi N k = ∑ i ∈ Finset.range (N - 2 * k + 1), Λ (N + i) * Λ (N + i + 2 * k) := by
  unfold Psi
  have hset : (Finset.Icc N (2 * N)).filter (fun m => m + 2 * k ≤ 2 * N) =
      Finset.Ico N (2 * N - 2 * k + 1) := by
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have : 2 * N - 2 * k + 1 - N = N - 2 * k + 1 := by omega
  rw [this]

theorem Psi2_diff_eq_sum_range {N k : ℕ} (hk : 2 * k ≤ N) :
    Psi2 (2 * N) k - Psi2 (N + 2 * k) k =
      ∑ i ∈ Finset.range (N - 2 * k), Λ (N + 1 + i) * Λ (N + 1 + i + 2 * k) := by
  unfold Psi2
  rw [← Finset.sum_Ioc_consecutive _ (by omega : 2 * k ≤ N + 2 * k) (by omega : N + 2 * k ≤ 2 * N)]
  rw [add_sub_cancel_left]
  have hset : Finset.Ioc (N + 2 * k) (2 * N) = Finset.Ico (N + 2 * k + 1) (2 * N + 1) := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have : 2 * N + 1 - (N + 2 * k + 1) = N - 2 * k := by omega
  rw [this]
  apply Finset.sum_congr rfl
  intro i _
  have e1 : N + 2 * k + 1 + i - 2 * k = N + 1 + i := by omega
  have e2 : N + 2 * k + 1 + i = N + 1 + i + 2 * k := by omega
  rw [e1, e2, mul_comm]

/-- The relation `Ψ(N,2k) = Ψ₂(2N,2k) - Ψ₂(N+2k,2k)` of p. 356 holds up to the boundary
term `m = N`: with `Σ_{m,n=N}^{2N}` read as `N ≤ m, n ≤ 2N`, the exact identity is this one. -/
theorem Psi_eq_Psi2_diff {N k : ℕ} (hk : 2 * k ≤ N) :
    Psi N k = Psi2 (2 * N) k - Psi2 (N + 2 * k) k + Λ N * Λ (N + 2 * k) := by
  rw [Psi_eq_sum_range hk, Psi2_diff_eq_sum_range hk]
  have : N - 2 * k + 1 = (N - 2 * k) + 1 := rfl
  rw [this, Finset.sum_range_succ']
  simp only [add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show N + (i + 1) = N + 1 + i by ring]

/-- The boundary term is not zero for `N = 3`, `k = 1`, so the printed relation needs the
reading `N < m` or an `O(L²)` slack; the paper's use is unaffected. PRELIMINARY. -/
theorem Psi_ne_Psi2_diff_example : Psi 3 1 ≠ Psi2 (2 * 3) 1 - Psi2 (3 + 2 * 1) 1 := by
  rw [Psi_eq_Psi2_diff (by norm_num)]
  have h3 : Λ 3 = Real.log 3 := vonMangoldt_apply_prime Nat.prime_three
  have h5 : Λ (3 + 2 * 1) = Real.log 5 := by
    norm_num [vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)]
  rw [h3, h5]
  have a : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have b : 0 < Real.log 5 := Real.log_pos (by norm_num)
  intro h
  nlinarith [mul_pos a b]

/-! ### PROVED: the exponents of Section 6, p. 368-371 -/

/-- Ingham's exponent `3(1-σ)/(2-σ)` in (39) is `(1-σ)/(1/2 + c(1/2-σ))` with `c = 1/3`,
the threshold named on p. 356. -/
theorem ingham_exponent_form (σ : ℝ) (hσ : σ < 2) :
    3 * (1 - σ) / (2 - σ) = (1 - σ) / (1 / 2 + 1 / 3 * (1 / 2 - σ)) := by
  have h : (2 - σ) ≠ 0 := by linarith
  have h' : (1 / 2 + 1 / 3 * (1 / 2 - σ)) ≠ 0 := by intro h0; apply h; linarith
  rw [div_eq_div_iff h h']
  ring

/-- At `σ = 1/2` Ingham's exponent is `1`, the density hypothesis value. -/
theorem ingham_exponent_half : 3 * (1 - (1 / 2 : ℝ)) / (2 - 1 / 2) = 1 := by norm_num

/-- (39) and (40) agree at `σ = 4/5`: `3(1-σ)/(2-σ) = (5/2)(1-σ) = 1/2`. -/
theorem density_exponents_match :
    3 * (1 - (4 / 5 : ℝ)) / (2 - 4 / 5) = 1 / 2 ∧ (5 / 2 : ℝ) * (1 - 4 / 5) = 1 / 2 := by
  norm_num

/-- `f₁(δ) = 3δ/(2(1+δ)) - δ`, p. 368. -/
noncomputable def f1 (δ : ℝ) : ℝ := 3 * δ / (2 * (1 + δ)) - δ

/-- `f₂(δ) = 3δ/(4(1+δ)) - δ`, p. 368. -/
noncomputable def f2 (δ : ℝ) : ℝ := 3 * δ / (4 * (1 + δ)) - δ

/-- `f₁ ≤ 5/2 - √6` for `δ > -1`, AM-GM; the maximum is at `δ = √(3/2) - 1`. -/
theorem f1_le_max {δ : ℝ} (hδ : -1 < δ) : f1 δ ≤ 5 / 2 - Real.sqrt 6 := by
  unfold f1
  have hu : 0 < 1 + δ := by linarith
  have hs : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  rw [show 3 * δ / (2 * (1 + δ)) - δ = (3 * δ - 2 * δ * (1 + δ)) / (2 * (1 + δ)) by
    field_simp]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * (1 + δ) - Real.sqrt 6)]

theorem f1_at_max : f1 (Real.sqrt (3 / 2) - 1) = 5 / 2 - Real.sqrt 6 := by
  unfold f1
  have hs : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have h6 : Real.sqrt 6 = 2 * Real.sqrt (3 / 2) := by
    rw [show (6 : ℝ) = 2 ^ 2 * (3 / 2) by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h6, show 1 + (Real.sqrt (3 / 2) - 1) = Real.sqrt (3 / 2) by ring]
  field_simp
  nlinarith [hs]

/-- `f₁` increases on `[1/5, √(3/2) - 1]`, p. 368. -/
theorem f1_monotoneOn : MonotoneOn f1 (Set.Icc (1 / 5) (Real.sqrt (3 / 2) - 1)) := by
  intro x hx y hy hxy
  unfold f1
  have hs : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have ux : 0 < 1 + x := by linarith [hx.1]
  have uy : 0 < 1 + y := by linarith [hy.1]
  have hxy' : (1 + x) * (1 + y) ≤ 3 / 2 := by
    have a : 1 + x ≤ Real.sqrt (3 / 2) := by linarith [hx.2]
    have b : 1 + y ≤ Real.sqrt (3 / 2) := by linarith [hy.2]
    nlinarith
  rw [show 3 * x / (2 * (1 + x)) - x = (3 * x - 2 * x * (1 + x)) / (2 * (1 + x)) by field_simp,
    show 3 * y / (2 * (1 + y)) - y = (3 * y - 2 * y * (1 + y)) / (2 * (1 + y)) by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy')]

/-- `f₁` decreases on `[√(3/2) - 1, 1/2]`, p. 368. -/
theorem f1_antitoneOn : AntitoneOn f1 (Set.Icc (Real.sqrt (3 / 2) - 1) (1 / 2)) := by
  intro x hx y hy hxy
  unfold f1
  have hs : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have ux : 0 < 1 + x := by linarith [hx.1]
  have uy : 0 < 1 + y := by linarith [hy.1]
  have hxy' : 3 / 2 ≤ (1 + x) * (1 + y) := by
    have a : Real.sqrt (3 / 2) ≤ 1 + x := by linarith [hx.1]
    have b : Real.sqrt (3 / 2) ≤ 1 + y := by linarith [hy.1]
    nlinarith
  rw [show 3 * x / (2 * (1 + x)) - x = (3 * x - 2 * x * (1 + x)) / (2 * (1 + x)) by field_simp,
    show 3 * y / (2 * (1 + y)) - y = (3 * y - 2 * y * (1 + y)) / (2 * (1 + y)) by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy')]

/-- `f₂` decreases on `[0, ∞)`, in particular on `[1/5, 1/2]`, p. 368-369. -/
theorem f2_antitoneOn : AntitoneOn f2 (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold f2
  have ux : 0 < 1 + x := by linarith
  have uy : 0 < 1 + y := by linarith
  rw [show 3 * y / (4 * (1 + y)) - y = (3 * y - 4 * y * (1 + y)) / (4 * (1 + y)) by field_simp,
    show 3 * x / (4 * (1 + x)) - x = (3 * x - 4 * x * (1 + x)) / (4 * (1 + x)) by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hx hy), mul_nonneg (sub_nonneg.mpr hxy) hx,
    mul_nonneg (sub_nonneg.mpr hxy) hy]

/-- `g₀(δ) = 3δ/(1+δ) - 2δ + (2δ-1)/(2(2-δ))`, (49) at `ε = 0`, p. 370. -/
noncomputable def g0 (δ : ℝ) : ℝ := 3 * δ / (1 + δ) - 2 * δ + (2 * δ - 1) / (2 * (2 - δ))

/-- Identity (50), p. 370: `2(2-δ)(1+δ)g₀(δ) = (2δ-1)²(δ-1)`. -/
theorem identity50 {δ : ℝ} (h1 : δ ≠ -1) (h2 : δ ≠ 2) :
    2 * (2 - δ) * (1 + δ) * g0 δ = (2 * δ - 1) ^ 2 * (δ - 1) := by
  unfold g0
  have a : 1 + δ ≠ 0 := by intro h; apply h1; linarith
  have b : 2 - δ ≠ 0 := by intro h; apply h2; linarith
  field_simp
  ring

/-- Hence `g₀ < 0` on `(-1, 1/2)`, in particular on `[1/5, 1/2)`, and `g₀(1/2) = 0`. -/
theorem g0_neg {δ : ℝ} (h1 : -1 < δ) (h2 : δ < 1 / 2) : g0 δ < 0 := by
  have hid := identity50 (δ := δ) (by intro h; linarith) (by intro h; linarith)
  have hp : 0 < 2 * (2 - δ) * (1 + δ) := by
    have : 0 < 2 - δ := by linarith
    have : 0 < 1 + δ := by linarith
    positivity
  have hr : (2 * δ - 1) ^ 2 * (δ - 1) < 0 := by
    have : 0 < (2 * δ - 1) ^ 2 := by
      have : 2 * δ - 1 ≠ 0 := by intro h; linarith
      positivity
    nlinarith
  by_contra hc
  push Not at hc
  nlinarith

theorem g0_half : g0 (1 / 2) = 0 := by unfold g0; norm_num

/-- p. 371: for `δ ≥ 1/5` the exponent `9δ/(4(1+δ)) - 2δ` of `N` is at most `-1/40`. -/
theorem exponent_le_neg_one_fortieth {δ : ℝ} (h : 1 / 5 ≤ δ) :
    9 * δ / (4 * (1 + δ)) - 2 * δ ≤ -1 / 40 := by
  have hu : 0 < 1 + δ := by linarith
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 80 * δ + 5)]

theorem exponent_at_one_fifth : 9 * (1 / 5 : ℝ) / (4 * (1 + 1 / 5)) - 2 * (1 / 5) = -1 / 40 := by
  norm_num

/-! ### PROVED: links to the lab's exceptional set chain -/

/-- Under GRH, Hardy and Littlewood would give Zhao's exponent `7/10` and every older bound. -/
theorem zhao_of_HL (h : HLBound) : LeanLab.ExceptionalSet.PowerBound (7 / 10) :=
  LeanLab.ExceptionalSet.powerBound_mono (by norm_num) (h (1 / 5) (by norm_num))

theorem chain_of_HL (h : HLBound) :
    LeanLab.ExceptionalSet.EventuallyBelow 0.72 ∧ LeanLab.ExceptionalSet.PowerBound 0.879 ∧
    LeanLab.ExceptionalSet.PowerSaving ∧ LeanLab.ExceptionalSet.LogPowerSaving ∧
    LeanLab.ExceptionalSet.DensityZero :=
  LeanLab.ExceptionalSet.all_of_zhao (zhao_of_HL h)

end LeanLab.PerelliPintz1992

open LeanLab.PerelliPintz1992 in
section
end
