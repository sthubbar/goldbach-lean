module

public import LeanLab.HardyLittlewood1923.U1438Sing
public import LeanLab.HardyLittlewood1923.TheoremBAll
public import LeanLab.HardyLittlewood1923.TheoremBUnlike
public import LeanLab.VanDerCorput1939.Unweight
public import LeanLab.PNTPort.BV.Helpers

/-!
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1603Z-28836, unit U-1438, paper P0004.

# Hardy-Littlewood 1923, Partitio numerorum III, Theorem A for r = 3

Theorem A is the asymptotic formula with a power saving, on Hypothesis R,
`ν₃(n) = ½ 𝔖₃(n) n² + O(n^{2-δ})`, `𝔖₃(n) = Σ_q (μ(q)/φ(q))³ c_q(n)`, for every large `n`, odd or
even, `𝔖₃(n) = 0` for even `n`. The paper copy was not available in this run, so the printed
exponent is not quoted; `theoremA3_stmt` asks for SOME `δ > 0`, which every printed form with a
power saving implies. See STATEMENTS.md, QUESTION U-1438-Q1.

* `NoZerosRight Θ`, `HypothesisR`: no zero of any Dirichlet `L(s, χ)` in `Re s > Θ`, for some
  `Θ < 3/4`. `noZerosRight_one`: the predicate holds at `Θ = 1`, Mathlib's nonvanishing on
  `Re s ≥ 1`; `HypothesisR` itself is open, GRH strength.
* `theoremA3_main`: the main term of Theorem A WITHOUT the power saving,
  `ν₃(n) = ½ 𝔖₃(n) n² + o(n²)`, PROVED with no hypothesis, from `theoremB3`, `theoremB_unlike` and
  `sing3_odd`, `sing3_even`.
* `abs_r3_sub_nur3`: von Mangoldt weights against prime weights,
  `|r₃(n) - ν₃(n)| ≤ 3 (log n)³ n √n log₂ n`.
* `theoremA3_of_r3Power`: the reduction from the von Mangoldt form `R3Power` to Theorem A.

Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1438

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PNTPort.Vinogradov (r3)
open LeanLab.VanDerCorput1939 (ppNP ppNP_nonneg card_ppNP natLog_le collapse third_bound)

/-! ### Hypothesis R -/

/-- No Dirichlet `L`-function vanishes in the half plane `Re s > Θ`; the point `s = 1`, the pole
of the principal `L`-functions, is excluded. -/
def NoZerosRight (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), Θ < s.re → s ≠ 1 →
    DirichletCharacter.LFunction χ s ≠ 0

/-- **Hypothesis R** of Hardy and Littlewood: there is `Θ < 3/4` such that no `L(s, χ)` has a zero
with `Re s > Θ`. -/
def HypothesisR : Prop := ∃ Θ : ℝ, Θ < 3 / 4 ∧ NoZerosRight Θ

/-- The predicate is not vacuous in form: it holds at `Θ = 1`. -/
theorem noZerosRight_one : NoZerosRight 1 :=
  fun _ _ χ _ hs hs1 => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le

theorem noZerosRight_mono {Θ Θ' : ℝ} (h : Θ ≤ Θ') (hΘ : NoZerosRight Θ) : NoZerosRight Θ' :=
  fun q _ χ s hs hs1 => hΘ q χ s (lt_of_le_of_lt h hs) hs1

/-! ### Statements -/

/-- **Theorem A, r = 3**, with a power saving: for some `δ > 0`,
`ν₃(n) = ½ 𝔖₃(n) n² + O(n^{2-δ})` for every large `n`. -/
def theoremA3_stmt : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    |nur 3 n - sing3 n * (n : ℝ) ^ 2 / 2| ≤ C * (n : ℝ) ^ (2 - δ)

/-- The same with von Mangoldt weights, `r₃(n) = Σ_{a+b+c=n} Λ(a)Λ(b)Λ(c)`. -/
def R3Power : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| ≤ C * (n : ℝ) ^ (2 - δ)

/-! ### The main term without the power saving, unconditional -/

/-- **Theorem A's main term, `ν₃(n) = ½ 𝔖₃(n) n² + o(n²)`**, every large `n`, no hypothesis. -/
theorem theoremA3_main : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    |nur 3 n - sing3 n * (n : ℝ) ^ 2 / 2| ≤ ε * (n : ℝ) ^ 2 := by
  intro ε hε
  have hC3 := C3_pos
  obtain ⟨n₁, h1⟩ := theoremB3 (ε / (C3 + 1)) (by positivity)
  obtain ⟨n₂, h2⟩ := theoremB_unlike 3 le_rfl ε hε
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · rw [sing3_even he]
    have h := h2 n (by rw [Nat.even_iff.1 he]; norm_num) (le_trans (le_max_right _ _) hn)
    simp only [zero_mul, zero_div, sub_zero]
    rw [abs_of_nonneg (nur_nonneg 3 n)]
    simpa using h
  · have h := h1 n ho (le_trans (le_max_left _ _) hn)
    have eM : 2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n = sing3 n * (n : ℝ) ^ 2 / 2 := by
      rw [Cr3_eq, Br3_eq n ho, sing3_odd ho]; ring
    rw [eM] at h
    have hP := ThmE.Pi3_bounds n
    have hM : sing3 n * (n : ℝ) ^ 2 / 2 ≤ C3 * (n : ℝ) ^ 2 := by
      rw [sing3_odd ho]
      have h0 : 0 ≤ (n : ℝ) ^ 2 := by positivity
      have := mul_nonneg (mul_nonneg hC3.le h0) (sub_nonneg.2 hP.2)
      nlinarith
    have hM0 : 0 ≤ sing3 n * (n : ℝ) ^ 2 / 2 := by
      have := (sing3_pos ho).le; positivity
    calc |nur 3 n - sing3 n * (n : ℝ) ^ 2 / 2| ≤ ε / (C3 + 1) * (sing3 n * (n : ℝ) ^ 2 / 2) := h
      _ ≤ ε / (C3 + 1) * (C3 * (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = (ε / (C3 + 1) * C3) * (n : ℝ) ^ 2 := by ring
      _ ≤ ε * (n : ℝ) ^ 2 := by
          have : ε / (C3 + 1) * C3 ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
          exact mul_le_mul_of_nonneg_right this (by positivity)

/-! ### Prime weights against von Mangoldt weights -/

lemma le_sqrt_of_sq {y x : ℝ} (hy : 0 ≤ y) (h : y ^ 2 ≤ x) : y ≤ Real.sqrt x := by
  calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy).symm
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h

/-- `log p` on primes, `0` elsewhere. -/
noncomputable def th (m : ℕ) : ℝ := if m.Prime then Real.log m else 0

lemma th_nonneg (m : ℕ) : 0 ≤ th m := by
  unfold th; split_ifs; exact Real.log_natCast_nonneg m; exact le_rfl

lemma th_le_vonMangoldt (m : ℕ) : th m ≤ Λ m := by
  unfold th; split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma vonMangoldt_sub_th_le {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    Λ m - th m ≤ Real.log N * ppNP m := by
  by_cases hp : m.Prime
  · rw [th, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    exact mul_nonneg (Real.log_natCast_nonneg N) (ppNP_nonneg m)
  · rw [th, if_neg hp, sub_zero]
    by_cases hpp : IsPrimePow m
    · rw [ppNP, if_pos ⟨hpp, hp⟩, mul_one]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN))
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
      exact mul_nonneg (Real.log_natCast_nonneg N) (ppNP_nonneg m)

lemma vonMangoldt_le_logN {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) : Λ m ≤ Real.log N :=
  ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN))

lemma pw_diff {N a b c : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (hb : 1 ≤ b) (hbN : b ≤ N)
    (hc : 1 ≤ c) (hcN : c ≤ N) :
    Λ a * Λ b * Λ c - th a * th b * th c ≤
      Real.log N ^ 3 * (ppNP a + ppNP b + ppNP c) := by
  set L := Real.log N
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have ea := vonMangoldt_sub_th_le ha haN
  have eb := vonMangoldt_sub_th_le hb hbN
  have ec := vonMangoldt_sub_th_le hc hcN
  have la := vonMangoldt_le_logN ha haN
  have lb := vonMangoldt_le_logN hb hbN
  have lc := vonMangoldt_le_logN hc hcN
  have ta := th_le_vonMangoldt a
  have tb := th_le_vonMangoldt b
  have tc := th_le_vonMangoldt c
  have t0a := th_nonneg a
  have t0b := th_nonneg b
  have l0b : 0 ≤ Λ b := ArithmeticFunction.vonMangoldt_nonneg
  have l0c : 0 ≤ Λ c := ArithmeticFunction.vonMangoldt_nonneg
  have e : Λ a * Λ b * Λ c - th a * th b * th c =
      (Λ a - th a) * (Λ b * Λ c) + th a * ((Λ b - th b) * Λ c) + th a * th b * (Λ c - th c) := by
    ring
  rw [e]
  have k1 : (Λ a - th a) * (Λ b * Λ c) ≤ (L * ppNP a) * (L * L) :=
    mul_le_mul ea (mul_le_mul lb lc l0c hL) (mul_nonneg l0b l0c)
      (mul_nonneg hL (ppNP_nonneg a))
  have k2 : th a * ((Λ b - th b) * Λ c) ≤ L * ((L * ppNP b) * L) := by
    apply mul_le_mul (ta.trans la) _ (mul_nonneg (by linarith) l0c) hL
    exact mul_le_mul eb lc l0c (mul_nonneg hL (ppNP_nonneg b))
  have k3 : th a * th b * (Λ c - th c) ≤ (L * L) * (L * ppNP c) := by
    apply mul_le_mul (mul_le_mul (ta.trans la) (tb.trans lb) t0b hL) ec (by linarith) (mul_nonneg hL hL)
  have : (L * ppNP a) * (L * L) + L * ((L * ppNP b) * L) + (L * L) * (L * ppNP c) =
      L ^ 3 * (ppNP a + ppNP b + ppNP c) := by ring
  linarith

/-- `ν₃(N)` as a sum over triples. -/
theorem nur3_eq_prod (N : ℕ) : nur 3 N =
    ∑ x ∈ Icc 1 N ×ˢ (Icc 1 N ×ˢ Icc 1 N),
      if x.1 + x.2.1 + x.2.2 = N then th x.1 * th x.2.1 * th x.2.2 else 0 := by
  rw [nur_eq, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij_ne_zero (fun x _ _ => ![x.1, x.2.1, x.2.2])
  · intro x hx hne
    rw [mem_filter, mem_product, mem_product, mem_Icc, mem_Icc, mem_Icc] at hx
    obtain ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩, hs⟩ := hx
    rw [mem_Sr]
    have hpa : x.1.Prime := by by_contra h; apply hne; simp [th, h]
    have hpb : x.2.1.Prime := by by_contra h; apply hne; simp [th, h]
    have hpc : x.2.2.Prime := by by_contra h; apply hne; simp [th, h]
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · fin_cases i <;> (try simp) <;> omega
    · fin_cases i <;> simpa
    · simpa [Fin.sum_univ_three] using hs
  · intro x _ _ y _ _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    exact Prod.ext h0 (Prod.ext h1 h2)
  · intro t ht hne
    rw [mem_Sr] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨(t 0, t 1, t 2), ?_, ?_, ?_⟩
    · rw [mem_filter, mem_product, mem_product, mem_Icc, mem_Icc, mem_Icc]
      rw [Fin.sum_univ_three] at h3
      have := (h2 0).two_le
      have := (h2 1).two_le
      have := (h2 2).two_le
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> dsimp only <;> omega
    · show th (t 0) * th (t 1) * th (t 2) ≠ 0
      simp only [th, if_pos (h2 0), if_pos (h2 1), if_pos (h2 2)]
      rw [Fin.prod_univ_three] at hne
      exact hne
    · funext i; fin_cases i <;> rfl
  · intro x _ hne
    have hpa : x.1.Prime := by by_contra h; apply hne; simp [th, h]
    have hpb : x.2.1.Prime := by by_contra h; apply hne; simp [th, h]
    have hpc : x.2.2.Prime := by by_contra h; apply hne; simp [th, h]
    simp [Fin.prod_univ_three, th, hpa, hpb, hpc]

/-- `ν₃(N)` as a triple sum. -/
theorem nur3_eq (N : ℕ) : nur 3 N =
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
      if a + b + c = N then th a * th b * th c else 0 := by
  rw [nur3_eq_prod, Finset.sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product]

/-- **Prime powers are few**: `|r₃(N) - ν₃(N)| ≤ 3 (log N)³ N √N log₂ N`. -/
theorem abs_r3_sub_nur3 (N : ℕ) :
    |r3 N N - nur 3 N| ≤ 3 * Real.log N ^ 3 * N * ((Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ)) := by
  set L := Real.log N
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have er : r3 N N = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      if a + b < N then Λ a * Λ b * Λ (N - a - b) else 0 := by
    unfold r3
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    exact collapse N a b (fun c => Λ a * Λ b * Λ c)
  have en : nur 3 N = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      if a + b < N then th a * th b * th (N - a - b) else 0 := by
    rw [nur3_eq]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    exact collapse N a b (fun c => th a * th b * th c)
  have hdiff : r3 N N - nur 3 N = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      if a + b < N then Λ a * Λ b * Λ (N - a - b) - th a * th b * th (N - a - b) else 0 := by
    rw [er, en, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hnn : 0 ≤ r3 N N - nur 3 N := by
    rw [hdiff]
    refine sum_nonneg fun a ha => sum_nonneg fun b hb => ?_
    split_ifs
    · have h1 : th a * th b ≤ Λ a * Λ b := mul_le_mul (th_le_vonMangoldt a)
        (th_le_vonMangoldt b) (th_nonneg b) ArithmeticFunction.vonMangoldt_nonneg
      have := mul_le_mul h1 (th_le_vonMangoldt (N - a - b)) (th_nonneg _)
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
      linarith
    · exact le_rfl
  rw [abs_of_nonneg hnn, hdiff]
  calc _ ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        L ^ 3 * (if a + b < N then ppNP a + ppNP b + ppNP (N - a - b) else 0) := by
        refine sum_le_sum fun a ha => sum_le_sum fun b hb => ?_
        rw [mem_Icc] at ha hb
        split_ifs with h
        · exact pw_diff ha.1 ha.2 hb.1 hb.2 (by omega) (by omega)
        · simp
    _ = L ^ 3 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (if a + b < N then ppNP a + ppNP b + ppNP (N - a - b) else 0) := by
        rw [mul_sum]; refine sum_congr rfl fun a _ => ?_; rw [mul_sum]
    _ ≤ L ^ 3 * (3 * N * ∑ n ∈ Icc 1 N, ppNP n) :=
        mul_le_mul_of_nonneg_left (third_bound N ppNP ppNP_nonneg) (by positivity)
    _ ≤ L ^ 3 * (3 * N * ((Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (card_ppNP N) (by positivity)
    _ = _ := by ring

/-- The prime power error is `O(N^{7/4})`. -/
theorem r3_sub_nur3_power : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    |r3 N N - nur 3 N| ≤ C * (N : ℝ) ^ ((7 : ℝ) / 4) := by
  obtain ⟨K, hK, hlog⟩ := LeanLab.PNTPort.BV.log_rpow_le_rpow 4 (1 / 4) (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 * K / Real.log 2, by positivity, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have h1 := abs_r3_sub_nur3 N
  have hsq : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    apply le_sqrt_of_sq (Nat.cast_nonneg _)
    exact_mod_cast Nat.sqrt_le' N
  have hlg : (Nat.log 2 N : ℝ) ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact natLog_le N (by omega)
  have h4 : L ^ 4 ≤ K * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have := hlog N hN2
    have e : Real.log N ^ (4 : ℝ) = Real.log N ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at this
    exact this
  have hprod : (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * (L / Real.log 2) :=
    mul_le_mul hsq hlg (Nat.cast_nonneg _) (by positivity)
  have hsplit : (N : ℝ) ^ ((7 : ℝ) / 4) = N * (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show (7 : ℝ) / 4 = 1 + 1 / 2 + 1 / 4 by norm_num, Real.rpow_add hN0, Real.rpow_add hN0,
      Real.rpow_one]
  calc |r3 N N - nur 3 N|
      ≤ 3 * L ^ 3 * N * ((Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ)) := h1
    _ ≤ 3 * L ^ 3 * N * ((N : ℝ) ^ ((1 : ℝ) / 2) * (L / Real.log 2)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 3 / Real.log 2 * (L ^ 4) * (N * (N : ℝ) ^ ((1 : ℝ) / 2)) := by ring
    _ ≤ 3 / Real.log 2 * (K * (N : ℝ) ^ ((1 : ℝ) / 4)) * (N * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 3 * K / Real.log 2 * (N : ℝ) ^ ((7 : ℝ) / 4) := by rw [hsplit]; ring

lemma rpow_le_rpow_of_le_exp {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

/-- **The reduction**: the von Mangoldt form gives Theorem A. -/
theorem theoremA3_of_r3Power (h : R3Power) : theoremA3_stmt := by
  obtain ⟨δ, hδ, C, n₀, hC⟩ := h
  obtain ⟨C₁, hC₁, hpp⟩ := r3_sub_nur3_power
  refine ⟨min δ (1 / 4), lt_min hδ (by norm_num), C₁ + |C|, max n₀ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have e1 := hC n (le_trans (le_max_left _ _) hn)
  have e2 := hpp n hn2
  have k1 : (n : ℝ) ^ ((7 : ℝ) / 4) ≤ (n : ℝ) ^ (2 - min δ (1 / 4)) :=
    rpow_le_rpow_of_le_exp hn1 (by have := min_le_right δ (1 / 4); linarith)
  have k2 : (n : ℝ) ^ (2 - δ) ≤ (n : ℝ) ^ (2 - min δ (1 / 4)) :=
    rpow_le_rpow_of_le_exp hn1 (by have := min_le_left δ (1 / 4); linarith)
  have hp0 : 0 ≤ (n : ℝ) ^ (2 - δ) := by positivity
  have e1' : |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| ≤ |C| * (n : ℝ) ^ (2 - δ) :=
    e1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp0)
  calc |nur 3 n - sing3 n * (n : ℝ) ^ 2 / 2|
      = |(r3 n n - sing3 n * (n : ℝ) ^ 2 / 2) - (r3 n n - nur 3 n)| := by congr 1; ring
    _ ≤ |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| + |r3 n n - nur 3 n| := abs_sub _ _
    _ ≤ |C| * (n : ℝ) ^ (2 - min δ (1 / 4)) + C₁ * (n : ℝ) ^ (2 - min δ (1 / 4)) := by
        have := mul_le_mul_of_nonneg_left k2 (abs_nonneg C)
        have := mul_le_mul_of_nonneg_left k1 hC₁
        linarith
    _ = (C₁ + |C|) * (n : ℝ) ^ (2 - min δ (1 / 4)) := by ring

/-! ### Vacuity: the objects at a concrete `n` -/

/-- `𝔖₃(7) > 0` and `𝔖₃(7) = 2 C₃ · 30/31`, the factor at `7` being `6 · 5/31`. -/
theorem sing3_seven : 0 < sing3 7 ∧ sing3 7 = 2 * C3 * (30 / 31) := by
  refine ⟨sing3_pos ⟨3, by norm_num⟩, ?_⟩
  rw [sing3_odd ⟨3, by norm_num⟩]
  congr 1
  unfold Pi3
  rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 7), Finset.prod_singleton]
  norm_num

end LeanLab.HardyLittlewood1923.U1438
