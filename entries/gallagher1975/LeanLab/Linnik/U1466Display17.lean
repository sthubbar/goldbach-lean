module

public import LeanLab.Linnik.U1464Display20

/-!
Li-Liu, arXiv 2610.15784, Lemma 3.1, display (17), and its proof.
Read by WebFetch on the unversioned arxiv.org/html/2610.15784, 2026-10-22.

Display (17), for `1 ≤ i, j ≤ 3` and fixed `D ≥ 1`:
`(1/L^{i+j}) ∑_{h ≠ 0} r_{i,j}(h) ∑'_{d > D, d | h} 1/∏_{p | d}(p-2)
   ≤ ∑'_{d > D} 1/(ε(d)∏_{p | d}(p-2)) + O(log L / L)`.

The paper's proof, followed here.
1. Fix all exponents but one, so `h = 2^ν - m` with `|h| ≪ 2^L`.
2. For odd `d`, `2^ν ≡ m mod d` has at most `L/ε(d) + 1` solutions `ν ≤ L`, all in one residue
   class mod `ε(d)`; the `+1` occurs only if some `h ≠ 0` is divisible by `d`, so only for
   `d | P_m := ∏_{ν, h ≠ 0} |2^ν - m|`. Hence
   `∑_ν ∑'_{d > D, d | h} w(d) ≤ L ∑'_{d > D} w(d)/ε(d) + ∏_{p | P_m, p > 2}(1 + 1/(p-2))`.
3. Mertens: the product is `≪ log L`, since `log P_m = O(L²)`. Here the split is at
   `p < L² + 2`: the small primes give `≤ C log(L² + 1) ≤ 3C log L` by the cited Mertens product
   bound, and the at most `2L²` large prime factors of `P_m ≤ 2^{2L²}` give
   `≤ (1 + 1/L²)^{2L²} ≤ e²`.
4. Summing over the other `i + j - 1` exponents gives (17) with `O(log L / L)`.

Cited inputs, the smallest standard facts the proof uses.
* `MertensProd`: `∏_{2 < p ≤ n}(p-1)/(p-2) ≤ C log n`, a form of Mertens' third theorem,
  Hardy-Wright Theorem 429, since `(p-1)/(p-2) = (1-1/p)^{-1} (p-1)²/(p(p-2))` and
  `∏_{p > 2}(p-1)²/(p(p-2)) = 1/C₀` converges.
* `R0Summable`: the series `R₀ = ∑'_d 1/(ε(d)∏_{p|d}(p-2))` of (15) converges, Pintz-Ruzsa
  2003 Lemma 1, cited by Li-Liu right after (15). It is needed because the right side of (17)
  is this series' tail; in Lean a non-summable `tsum` is `0`.

Contents.
* `cntX_le`: the solution count of step 2, PROVED.
* `one_coord`: steps 2 and 3 for one free exponent, PROVED, CONDITIONAL ON both inputs.
* `display17_of`: `U1464Display20.Display17`, PROVED, CONDITIONAL ON `MertensProd` and
  `R0Summable`.
* `r6_lower8`: `U1464Display20.r6_lower7` with `Display17` replaced by the two inputs.

Unit U-1466, run 20261022T0403Z-7595. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1466Display17

open Set Real Filter Finset Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1447Display30
open LeanLab.Linnik.U1458Lemma42
open LeanLab.Linnik.U1464Display20
open LeanLab.Linnik.U1434Lemma21 (sv sv_le sv_even)

/-! ### The two cited inputs -/

/-- The odd primes `p ≤ n`. -/
def oddPrimesUpTo (n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun p => p.Prime ∧ 2 < p)

/-- **Mertens product bound, CITED, a named Prop**: `∏_{2 < p ≤ n}(p-1)/(p-2) ≤ C log n` for
`n ≥ 2`. A form of Mertens' third theorem, Hardy-Wright Theorem 429. -/
def MertensProd : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∏ p ∈ oddPrimesUpTo n, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ C * Real.log n

/-- **Convergence of `R₀` in (15), CITED, a named Prop**: `∑'_d 1/(ε(d)∏_{p|d}(p-2)) < ∞`,
Pintz-Ruzsa 2003 Lemma 1, as cited by Li-Liu after display (15). -/
def R0Summable : Prop := Summable (fun d : ℕ => wt d / (eps d : ℝ))

/-! ### One free exponent -/

/-- `F_D(h) = ∑'_{d > D, d | h} w(d)` for `h ≠ 0`, and `0` at `h = 0`. -/
noncomputable def FD (D : ℕ) (h : ℤ) : ℝ :=
  if h = 0 then 0 else ∑ d ∈ h.natAbs.divisors.filter (fun d => D < d), wt d

/-- `h_x = 2^{x+1} - m`. -/
def hval (m : ℤ) (x : ℕ) : ℤ := 2 ^ (x + 1) - m

/-- `P_m = ∏_{x < L, h_x ≠ 0} |h_x|`. -/
def Pm (L : ℕ) (m : ℤ) : ℕ :=
  ∏ x ∈ (univ : Finset (Fin L)).filter (fun x : Fin L => hval m (x : ℕ) ≠ 0), (hval m x).natAbs

lemma Pm_ne_zero (L : ℕ) (m : ℤ) : Pm L m ≠ 0 := by
  unfold Pm
  rw [Finset.prod_ne_zero_iff]
  intro x hx
  exact Int.natAbs_ne_zero.mpr (Finset.mem_filter.mp hx).2

/-- `#{x < L : h_x ≠ 0, d | h_x}`. -/
def cntX (L d : ℕ) (m : ℤ) : ℕ :=
  ((univ : Finset (Fin L)).filter (fun x : Fin L => hval m (x : ℕ) ≠ 0 ∧ (d : ℤ) ∣ hval m (x : ℕ))).card

/-- **The solution count of step 2, PROVED**: for odd `d`,
`#{x < L : h_x ≠ 0, d | h_x} ≤ L/ε(d) + [d | P_m]`. -/
lemma cntX_le {L d : ℕ} (hd : Odd d) (m : ℤ) :
    (cntX L d m : ℝ) ≤ (L : ℝ) / eps d + (if d ∣ Pm L m then 1 else 0) := by
  have he := eps_pos hd
  have hfin : IsOfFinOrder (2 : ZMod d) := orderOf_pos_iff.mp he
  by_cases hne : ((univ : Finset (Fin L)).filter
      (fun x : Fin L => hval m (x : ℕ) ≠ 0 ∧ (d : ℤ) ∣ hval m (x : ℕ))).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hx0' := (Finset.mem_filter.mp hx0).2
    have hdP : d ∣ Pm L m := by
      have h1 : d ∣ (hval m x0).natAbs := Int.natCast_dvd.mp hx0'.2
      exact h1.trans (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0'.1⟩))
    rw [if_pos hdP]
    have key : ∀ y : ℕ, (d : ℤ) ∣ hval m y → (2 : ZMod d) ^ (y + 1) = (m : ZMod d) := by
      intro y hy
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub m (2 ^ (y + 1)) d).mpr hy
      push_cast at this
      exact this.symm
    have hsub : (univ : Finset (Fin L)).filter (fun x : Fin L => hval m (x : ℕ) ≠ 0 ∧ (d : ℤ) ∣ hval m (x : ℕ)) ⊆
        (univ : Finset (Fin L)).filter (fun x : Fin L => (x : ℕ) % eps d = (x0 : ℕ) % eps d) := by
      intro x hxm
      have hxm' := (Finset.mem_filter.mp hxm).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h2 : (2 : ZMod d) ^ ((x : ℕ) + 1) = (2 : ZMod d) ^ ((x0 : ℕ) + 1) := by
        rw [key _ hxm'.2, key _ hx0'.2]
      have h3 : ((x : ℕ) + 1) ≡ ((x0 : ℕ) + 1) [MOD orderOf (2 : ZMod d)] :=
        hfin.pow_inj_mod.mp h2
      exact Nat.ModEq.add_right_cancel' 1 h3
    have hc : ((((univ : Finset (Fin L)).filter
        (fun x : Fin L => (x : ℕ) % eps d = (x0 : ℕ) % eps d)).card : ℕ) : ℝ) =
        cntRes L (eps d) ((x0 : ℕ) % eps d) := by
      unfold cntRes; rw [Finset.sum_boole]
    have hb := (cntRes_bounds (L := L) he (Nat.mod_lt (x0 : ℕ) he)).2
    calc (cntX L d m : ℝ) ≤ ((((univ : Finset (Fin L)).filter
          (fun x : Fin L => (x : ℕ) % eps d = (x0 : ℕ) % eps d)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = cntRes L (eps d) ((x0 : ℕ) % eps d) := hc
      _ ≤ _ := hb
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold cntX
    rw [hne, Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ L / eps d := by positivity
    split_ifs <;> linarith

lemma FD_eq (D B : ℕ) (h : ℤ) (hB : h.natAbs ≤ B) :
    FD D h = ∑ d ∈ (range (B + 1)).filter (fun d => D < d),
      wt d * (if h ≠ 0 ∧ (d : ℤ) ∣ h then 1 else 0) := by
  unfold FD
  by_cases h0 : h = 0
  · simp [h0]
  rw [if_neg h0]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  have hpos : 0 < h.natAbs := Int.natAbs_pos.mpr h0
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range, Int.natCast_dvd]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    have := Nat.le_of_dvd hpos h1
    exact ⟨⟨by omega, h2⟩, h0, h1⟩
  · rintro ⟨⟨_, h2⟩, _, h3⟩
    exact ⟨⟨h3, by omega⟩, h2⟩

lemma sum_FD_le (D L B : ℕ) (m : ℤ) (hB : ∀ x : Fin L, (hval m x).natAbs ≤ B) :
    ∑ x : Fin L, FD D (hval m x) ≤
      (L : ℝ) * ∑ d ∈ (range (B + 1)).filter (fun d => D < d), wt d / eps d +
      ∑ d ∈ (range (B + 1)).filter (fun d => D < d), wt d * (if d ∣ Pm L m then 1 else 0) := by
  have e1 : ∑ x : Fin L, FD D (hval m x) = ∑ d ∈ (range (B + 1)).filter (fun d => D < d),
      wt d * (cntX L d m : ℝ) := by
    rw [Finset.sum_congr rfl fun (x : Fin L) _ => FD_eq D B (hval m (x : ℕ)) (hB x),
      Finset.sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, cntX, Finset.sum_boole]
  rw [e1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_le_sum fun d _ => ?_
  by_cases hd : Odd d
  · have := cntX_le (L := L) hd m
    have hw := wt_nonneg d
    calc wt d * (cntX L d m : ℝ) ≤ wt d * ((L : ℝ) / eps d + if d ∣ Pm L m then 1 else 0) :=
          mul_le_mul_of_nonneg_left this hw
      _ = _ := by ring
  · have : wt d = 0 := by simp [wt, hd]
    simp [this]

/-- The main term: a finite part of the tail is at most the tail `R0tail D`. -/
lemma sum_tail_le (hR : R0Summable) (D B : ℕ) :
    ∑ d ∈ (range (B + 1)).filter (fun d => D < d), wt d / (eps d : ℝ) ≤ R0tail D := by
  have hs : Summable (fun n : ℕ => wt (n + (D + 1)) / (eps (n + (D + 1)) : ℝ)) :=
    (summable_nat_add_iff (D + 1)).mpr hR
  have hnn : ∀ n, 0 ≤ wt (n + (D + 1)) / (eps (n + (D + 1)) : ℝ) :=
    fun n => div_nonneg (wt_nonneg _) (Nat.cast_nonneg _)
  have e : ∑ d ∈ (range (B + 1)).filter (fun d => D < d), wt d / (eps d : ℝ) =
      ∑ n ∈ range (B - D), wt (n + (D + 1)) / (eps (n + (D + 1)) : ℝ) := by
    symm
    refine Finset.sum_nbij' (fun n => n + (D + 1)) (fun d => d - (D + 1)) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
      omega
    · intro d hd
      simp only [Finset.mem_range, Finset.mem_filter] at hd ⊢
      omega
    · intro n _; simp
    · intro d hd
      simp only [Finset.mem_range, Finset.mem_filter] at hd
      omega
    · intro n _; rfl
  rw [e, R0tail]
  exact hs.sum_le_tsum _ (fun n _ => hnn n)

/-- The `+1` terms: only `d | P_m` count, and `∑'_{d | P} w(d) = ∏_{p | P, p > 2}(p-1)/(p-2)`. -/
lemma sum_dvd_le (D B : ℕ) {P : ℕ} (hP : P ≠ 0) :
    ∑ d ∈ (range (B + 1)).filter (fun d => D < d), wt d * (if d ∣ P then 1 else 0) ≤
      ∏ p ∈ P.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [prod_expand hP]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => wt_nonneg d)
  simp only [Finset.mem_filter] at hd
  exact Nat.mem_divisors.mpr ⟨hd.2, hP⟩

lemma card_pf_le {P k : ℕ} (hP : P ≠ 0) (hk : P ≤ 2 ^ k) : P.primeFactors.card ≤ k := by
  have h1 : 2 ^ P.primeFactors.card ≤ ∏ p ∈ P.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ P.primeFactors, p ≤ P :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hP) (Nat.prod_primeFactors_dvd P)
  exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp (h1.trans (h2.trans hk))

lemma Pm_le {L : ℕ} {m : ℤ} (hB : ∀ x : Fin L, (hval m x).natAbs ≤ 2 ^ (L + 2)) :
    Pm L m ≤ 2 ^ ((L + 2) * L) := by
  unfold Pm
  calc _ ≤ (2 ^ (L + 2)) ^ ((univ : Finset (Fin L)).filter (fun x : Fin L => hval m (x : ℕ) ≠ 0)).card :=
        Finset.prod_le_pow_card _ _ _ fun x _ => hB x
    _ ≤ (2 ^ (L + 2)) ^ L :=
        Nat.pow_le_pow_right (by positivity) ((Finset.card_filter_le _ _).trans (by simp))
    _ = _ := by rw [← pow_mul]

/-- **Step 3, the Mertens step, PROVED, CONDITIONAL ON the Mertens product bound with constant
`C`**: if `P ≠ 0` has at most `2L²` prime factors, then
`∏_{p | P, p > 2}(p-1)/(p-2) ≤ 3e² max(C, 0) log L`. -/
lemma prod_bound {C : ℝ}
    (hC : ∀ n : ℕ, 2 ≤ n → ∏ p ∈ oddPrimesUpTo n, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ C * Real.log n)
    {L P : ℕ} (hL : 2 ≤ L) (hcard : P.primeFactors.card ≤ 2 * L ^ 2) :
    ∏ p ∈ P.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤
      max C 0 * 3 * Real.exp 2 * Real.log L := by
  set f : ℕ → ℝ := fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2) with hf
  set A := P.primeFactors.filter (fun p => 2 < p) with hA
  have hf1 : ∀ p : ℕ, 2 < p → 1 ≤ f p := by
    intro p hp
    have : (2 : ℝ) < p := by exact_mod_cast hp
    simp only [hf]
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hsmall : ∏ p ∈ A.filter (fun p => p < L ^ 2 + 2), f p ≤ max C 0 * 3 * Real.log L := by
    have hsub : A.filter (fun p => p < L ^ 2 + 2) ⊆ oddPrimesUpTo (L ^ 2 + 1) := by
      intro p hp
      simp only [hA, Finset.mem_filter, Nat.mem_primeFactors] at hp
      simp only [oddPrimesUpTo, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.1.1.1, hp.1.2⟩
    have h1 := prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => zero_le_one.trans (hf1 p (Finset.mem_filter.mp
        (Finset.mem_filter.mp hp).1).2))
      (fun p hp _ => hf1 p (by
        simp only [oddPrimesUpTo, Finset.mem_filter] at hp; exact hp.2.2))
    have h2 := hC (L ^ 2 + 1) (by nlinarith)
    have h3 : Real.log ((L ^ 2 + 1 : ℕ) : ℝ) ≤ 3 * Real.log L := by
      rw [show (3 : ℝ) * Real.log L = Real.log ((L : ℝ) ^ 3) by rw [Real.log_pow]; norm_num]
      apply Real.log_le_log (by positivity)
      push_cast
      nlinarith
    have hl0 : 0 ≤ Real.log ((L ^ 2 + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_cast; omega)
    have h4 : C * Real.log ((L ^ 2 + 1 : ℕ) : ℝ) ≤ max C 0 * (3 * Real.log L) :=
      calc C * Real.log ((L ^ 2 + 1 : ℕ) : ℝ)
          ≤ max C 0 * Real.log ((L ^ 2 + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hl0
        _ ≤ max C 0 * (3 * Real.log L) := mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    have : max C 0 * (3 * Real.log L) = max C 0 * 3 * Real.log L := by ring
    linarith
  have hlarge : ∏ p ∈ A.filter (fun p => ¬ p < L ^ 2 + 2), f p ≤ Real.exp 2 := by
    have hLsq : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
    have hb : ∀ p ∈ A.filter (fun p => ¬ p < L ^ 2 + 2), f p ≤ 1 + 1 / (L : ℝ) ^ 2 := by
      intro p hp
      simp only [Finset.mem_filter, not_lt] at hp
      have hp2 : (L : ℝ) ^ 2 + 2 ≤ p := by exact_mod_cast hp.2
      simp only [hf]
      rw [div_le_iff₀ (by linarith)]
      have h1 : 1 ≤ ((p : ℝ) - 2) / (L : ℝ) ^ 2 := by rw [le_div_iff₀ hLsq]; linarith
      have e : (1 + 1 / (L : ℝ) ^ 2) * ((p : ℝ) - 2) = ((p : ℝ) - 2) + ((p : ℝ) - 2) / (L : ℝ) ^ 2 := by
        field_simp
      rw [e]; linarith
    have hcardA : (A.filter (fun p => ¬ p < L ^ 2 + 2)).card ≤ 2 * L ^ 2 :=
      (Finset.card_le_card ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))).trans
        hcard
    have hq : (0 : ℝ) ≤ 1 / (L : ℝ) ^ 2 := by positivity
    calc ∏ p ∈ A.filter (fun p => ¬ p < L ^ 2 + 2), f p
        ≤ ∏ _p ∈ A.filter (fun p => ¬ p < L ^ 2 + 2), (1 + 1 / (L : ℝ) ^ 2) :=
          Finset.prod_le_prod₀ (fun p hp => zero_le_one.trans (hf1 p (Finset.mem_filter.mp
            (Finset.mem_filter.mp hp).1).2)) hb
      _ = (1 + 1 / (L : ℝ) ^ 2) ^ (A.filter (fun p => ¬ p < L ^ 2 + 2)).card :=
          Finset.prod_const _
      _ ≤ (1 + 1 / (L : ℝ) ^ 2) ^ (2 * L ^ 2) := pow_le_pow_right₀ (by linarith) hcardA
      _ ≤ Real.exp (1 / (L : ℝ) ^ 2) ^ (2 * L ^ 2) :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (1 / (L : ℝ) ^ 2)]) _
      _ = Real.exp 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun p => p < L ^ 2 + 2)]
  have hs0 : 0 ≤ ∏ p ∈ A.filter (fun p => p < L ^ 2 + 2), f p :=
    prod_nonneg fun p hp => zero_le_one.trans (hf1 p (Finset.mem_filter.mp
      (Finset.mem_filter.mp hp).1).2)
  have hl0 : 0 ≤ ∏ p ∈ A.filter (fun p => ¬ p < L ^ 2 + 2), f p :=
    prod_nonneg fun p hp => zero_le_one.trans (hf1 p (Finset.mem_filter.mp
      (Finset.mem_filter.mp hp).1).2)
  calc (∏ p ∈ A.filter (fun p => p < L ^ 2 + 2), f p) *
        ∏ p ∈ A.filter (fun p => ¬ p < L ^ 2 + 2), f p
      ≤ (max C 0 * 3 * Real.log L) * Real.exp 2 :=
        mul_le_mul hsmall hlarge hl0 (by positivity)
    _ = max C 0 * 3 * Real.exp 2 * Real.log L := by ring

/-- **Steps 2 and 3 for one free exponent, PROVED, CONDITIONAL ON** the Mertens product bound
with constant `C` and `R0Summable`: if `|2^{x+1} - m| ≤ 2^{L+2}` for all `x < L`, then
`∑_{x < L} ∑'_{d > D, d | h_x, h_x ≠ 0} w(d) ≤ L R0tail(D) + 3e² max(C, 0) log L`. -/
theorem one_coord {C : ℝ}
    (hC : ∀ n : ℕ, 2 ≤ n → ∏ p ∈ oddPrimesUpTo n, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ C * Real.log n)
    (hR : R0Summable) (D : ℕ) {L : ℕ} (hL : 2 ≤ L) (m : ℤ)
    (hB : ∀ x : Fin L, (hval m x).natAbs ≤ 2 ^ (L + 2)) :
    ∑ x : Fin L, FD D (hval m x) ≤ (L : ℝ) * R0tail D + max C 0 * 3 * Real.exp 2 * Real.log L := by
  have h1 := sum_FD_le D L (2 ^ (L + 2)) m hB
  have h2 := sum_tail_le hR D (2 ^ (L + 2))
  have h3 := sum_dvd_le D (2 ^ (L + 2)) (Pm_ne_zero L m)
  have hcard : (Pm L m).primeFactors.card ≤ 2 * L ^ 2 :=
    card_pf_le (Pm_ne_zero L m)
      ((Pm_le hB).trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith)))
  have h4 := prod_bound hC hL hcard
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_left h2 hL0
  linarith

/-! ### Summing over the other exponents -/

lemma T17_eq_FD (I J L D : ℕ) :
    T17 I J L D = ∑ ν : Fin I → Fin L, ∑ μ : Fin J → Fin L, FD D ((sv ν : ℤ) - sv μ) := by
  unfold T17 FD
  refine sum_congr rfl fun ν _ => sum_congr rfl fun μ _ => ?_
  by_cases hs : sv ν = sv μ
  · simp [hs]
  · have h0 : ((sv ν : ℤ) - sv μ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hs)
    rw [if_neg hs, if_neg h0]

lemma sv_cons {n L : ℕ} (x : Fin L) (ν : Fin n → Fin L) :
    sv (Fin.cons x ν : Fin (n + 1) → Fin L) = 2 ^ ((x : ℕ) + 1) + sv ν := by
  unfold sv
  rw [Fin.sum_univ_succ]
  simp

lemma sum_cons {n L : ℕ} (g : (Fin (n + 1) → Fin L) → ℝ) :
    ∑ ν : Fin (n + 1) → Fin L, g ν = ∑ ν' : Fin n → Fin L, ∑ x : Fin L, g (Fin.cons x ν') := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma natAbs_sub_le {a b t : ℕ} (ha : a ≤ 3 * t) (hb : b ≤ 3 * t) :
    ((a : ℤ) - b).natAbs ≤ 4 * t := by
  omega

/-- **The sum (17) before normalising, PROVED, CONDITIONAL ON** the Mertens product bound with
constant `C` and `R0Summable`. -/
theorem T17_le {C : ℝ}
    (hC : ∀ n : ℕ, 2 ≤ n → ∏ p ∈ oddPrimesUpTo n, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ C * Real.log n)
    (hR : R0Summable) (i j : Fin 3) (D : ℕ) {L : ℕ} (hL : 2 ≤ L) :
    T17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D ≤ (L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) *
      ((L : ℝ) * R0tail D + max C 0 * 3 * Real.exp 2 * Real.log L) := by
  set K := (L : ℝ) * R0tail D + max C 0 * 3 * Real.exp 2 * Real.log L with hK
  rw [T17_eq_FD, sum_cons]
  have key : ∀ (ν' : Fin (i : ℕ) → Fin L) (μ : Fin ((j : ℕ) + 1) → Fin L),
      ∑ x : Fin L, FD D ((sv (Fin.cons x ν' : Fin ((i : ℕ) + 1) → Fin L) : ℤ) - sv μ) ≤ K := by
    intro ν' μ
    have e : ∀ x : Fin L, ((sv (Fin.cons x ν' : Fin ((i : ℕ) + 1) → Fin L) : ℤ) - sv μ) =
        hval ((sv μ : ℤ) - sv ν') x := by
      intro x; rw [sv_cons]; unfold hval; push_cast; ring
    rw [Finset.sum_congr rfl fun x _ => congrArg (FD D) (e x)]
    refine one_coord hC hR D hL _ fun x => ?_
    rw [← e x]
    have hi := i.isLt
    have hj := j.isLt
    have ha := sv_le (Fin.cons x ν' : Fin ((i : ℕ) + 1) → Fin L)
    have hb := sv_le μ
    have ha' : sv (Fin.cons x ν' : Fin ((i : ℕ) + 1) → Fin L) ≤ 3 * 2 ^ L :=
      ha.trans (Nat.mul_le_mul_right _ (by omega))
    have hb' : sv μ ≤ 3 * 2 ^ L := hb.trans (Nat.mul_le_mul_right _ (by omega))
    have := natAbs_sub_le ha' hb'
    rw [pow_add]
    omega
  calc ∑ ν' : Fin (i : ℕ) → Fin L, ∑ x : Fin L, ∑ μ : Fin ((j : ℕ) + 1) → Fin L,
        FD D ((sv (Fin.cons x ν' : Fin ((i : ℕ) + 1) → Fin L) : ℤ) - sv μ)
      = ∑ ν' : Fin (i : ℕ) → Fin L, ∑ μ : Fin ((j : ℕ) + 1) → Fin L, ∑ x : Fin L,
        FD D ((sv (Fin.cons x ν' : Fin ((i : ℕ) + 1) → Fin L) : ℤ) - sv μ) :=
        sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ _ν' : Fin (i : ℕ) → Fin L, ∑ _μ : Fin ((j : ℕ) + 1) → Fin L, K :=
        sum_le_sum fun ν' _ => sum_le_sum fun μ _ => key ν' μ
    _ = (L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) * K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        rw [pow_add]; ring

/-- **Lemma 3.1, display (17), PROVED, CONDITIONAL ON `MertensProd` and `R0Summable`**. The
constant in `O(log L / L)` is `3e² max(C, 0)`, independent of `i, j, D`. -/
theorem display17_of (hM : MertensProd) (hR : R0Summable) : Display17 := by
  obtain ⟨C, hC⟩ := hM
  intro i j D _
  refine ⟨max C 0 * 3 * Real.exp 2, fun L hL => ?_⟩
  have hT := T17_le hC hR i j D hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  unfold Lhs17
  have e : (L : ℝ) ^ ((i : ℕ) + 1 + ((j : ℕ) + 1)) =
      (L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) * L := by
    rw [← pow_succ]; congr 1; omega
  rw [e, div_le_iff₀ (by positivity)]
  calc T17 ((i : ℕ) + 1) ((j : ℕ) + 1) L D
      ≤ (L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) *
        ((L : ℝ) * R0tail D + max C 0 * 3 * Real.exp 2 * Real.log L) := hT
    _ = (R0tail D + max C 0 * 3 * Real.exp 2 * (Real.log L / L)) *
        ((L : ℝ) ^ ((i : ℕ) + ((j : ℕ) + 1)) * L) := by
        field_simp

/-! ### The Section 6 conclusion -/

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON** the cited Lemma 4.1 `Lemma41 κ P ε` for every `ε > 0`,
display (18) `Lemma31_18`, the Mertens product bound `MertensProd`, the convergence of `R₀`
`R0Summable`, Proposition 3.2 `Prop32 Bdef (A_* + T)`, the cited (31) `Display31 6.7814`,
`MinorSup1924 P`, the conditions (24) on `P` and the cited constants of `k6_wired`. This is
`U1464Display20.r6_lower7` with `Display17` discharged. -/
theorem r6_lower8 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814)
    (h18 : Lemma31_18) (hM : MertensProd) (hR : R0Summable)
    (h32 : Prop32 Bdef (fun i j => (LiLiu.Astar i j : ℝ) + T i j)) :
    ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      (∀ ε > 0, Lemma41 κ P ε) →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) :=
  r6_lower7 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h18 (display17_of hM hR) h32

/-! ### Vacuity -/

/-- The Mertens bound holds at `n = 2` with `C = 2`: the product is empty and `1 ≤ 2 log 2`. -/
theorem mertens_instance :
    ∏ p ∈ oddPrimesUpTo 2, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ 2 * Real.log (2 : ℕ) := by
  have h : oddPrimesUpTo 2 = ∅ := by decide
  rw [h, Finset.prod_empty]
  have := Real.log_two_gt_d9
  push_cast
  linarith

/-- A term of `R₀`: `w(15)/ε(15) = 1/12`. -/
theorem R0_term_instance : wt 15 / (eps 15 : ℝ) = 1 / 12 := by
  rw [wt_eps_instance.1, wt_eps_instance.2]
  norm_num

/-- The solution count at `d = 3`, `m = 0`, `L = 4`: `2^{x+1} ≡ 0 mod 3` never holds. -/
theorem cntX_instance : cntX 4 3 0 = 0 := by unfold cntX hval; decide

end LeanLab.Linnik.U1466Display17
