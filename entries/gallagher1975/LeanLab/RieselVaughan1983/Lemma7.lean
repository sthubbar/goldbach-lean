module

public import LeanLab.RieselVaughan1983.Statements
public import LeanLab.Verifications.Statements

/-!
P0032 Riesel-Vaughan 1983, Lemma 7, page 58: `N(x) > x/18` for `2 ≤ x ≤ e^27`.
The paper's counting argument with the even numbers `p + 3` and `p + 5`, and the twin
prime bound `Σ_{3 ≤ p ≤ x-3, p-2 prime} 2 ≤ π(x - 3)`, both PROVED here. The one cited
input is Rosser-Schoenfeld 1962 (3.3), `π(x) > x/(log x - 1/2)` for `x ≥ 67`, the same
Prop as the lab's `ChenExplicit.Yamada.RS62`. The lab applies it at `x - 5` instead of the
paper's step `π(x - 5) ≥ π(x) - 2`; the margin is the same `3/53 > 1/18`.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.RieselVaughan1983
open LeanLab.SchnirelmannConstant

/-- Rosser-Schoenfeld 1962 (3.3), CITED, at natural `n`; identical to
`LeanLab.ChenExplicit.Yamada.RS62`. -/
def RS33 : Prop := ∀ n : ℕ, 67 ≤ n → (n : ℝ) / (Real.log n - 1 / 2) < (Nat.primeCounting n : ℝ)

/-- Odd primes up to `m`. -/
def oddPrimes (m : ℕ) : Finset ℕ := (Icc 3 m).filter Nat.Prime

lemma primeCounting_eq_oddPrimes (m : ℕ) (hm : 2 ≤ m) :
    Nat.primeCounting m = #(oddPrimes m) + 1 := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have : Nat.primesLE m = insert 2 (oddPrimes m) := by
    ext p
    simp only [Nat.primesLE, Nat.primesBelow, oddPrimes, mem_filter, mem_range, mem_insert,
      mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      have := h2.two_le
      by_cases hp : p = 2
      · exact Or.inl hp
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, h3⟩
  rw [this, card_insert_of_notMem]
  simp [oddPrimes]

/-- Three primes `r, r+2, r+4` with `r ≥ 3` force `r = 3`. -/
lemma prime_triple {r : ℕ} (hr : 3 ≤ r) (h0 : r.Prime) (h2 : (r + 2).Prime)
    (h4 : (r + 4).Prime) : r = 3 := by
  have hmod : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have : 3 ∣ r := Nat.dvd_of_mod_eq_zero h
    rcases h0.eq_one_or_self_of_dvd 3 this with h' | h' <;> omega
  · have : 3 ∣ r + 2 := by omega
    rcases h2.eq_one_or_self_of_dvd 3 this with h' | h' <;> omega
  · have : 3 ∣ r + 4 := by omega
    rcases h4.eq_one_or_self_of_dvd 3 this with h' | h' <;> omega

/-- Lower tw-prime members: odd primes `q ≤ n - 5` with `q + 2` prime. -/
def twins (n : ℕ) : Finset ℕ := (oddPrimes (n - 5)).filter (fun q => (q + 2).Prime)

/-- Page 58: `Σ_{3 ≤ p ≤ x-3, p-2 prime} 2 ≤ π(x - 3)`, as `2·#twins ≤ #oddPrimes(n-3) + 1`. -/
lemma two_twins_le (n : ℕ) : 2 * #(twins n) ≤ #(oddPrimes (n - 3)) + 1 := by
  set T := twins n
  set T2 := T.image (· + 2)
  have hT2 : #T2 = #T := card_image_of_injective _ (add_left_injective 2)
  have hsub : T ∪ T2 ⊆ oddPrimes (n - 3) := by
    intro a ha
    simp only [T2, T, twins, oddPrimes, mem_union, mem_image, mem_filter, mem_Icc] at ha ⊢
    rcases ha with ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ | ⟨q, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩
    · exact ⟨⟨h1, by omega⟩, h3⟩
    · exact ⟨⟨by omega, by omega⟩, h4⟩
  have hint : T ∩ T2 ⊆ {5} := by
    intro a ha
    simp only [T2, T, twins, oddPrimes, mem_inter, mem_image, mem_filter, mem_Icc,
      mem_singleton] at ha ⊢
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, q, ⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, rfl⟩ := ha
    have := prime_triple h5 h7 h8 (by simpa [add_assoc] using h4)
    omega
  have h1 := card_union_add_card_inter T T2
  have h2 := card_le_card hsub
  have h3 := (card_le_card hint).trans (by simp : #({5} : Finset ℕ) ≤ 1)
  omega

/-- Page 58: the counting step. For `n ≥ 8`,
`N(n) ≥ #oddPrimes(n-3) + #oddPrimes(n-5) - #twins + 2`, from the even numbers `p + 3`,
`p + 5` and the two numbers `2 = 2`, `4 = 2 + 2`. -/
lemma ncount_ge (x : ℝ) (n : ℕ) (hn : ⌊x⌋₊ = n) (h8 : 8 ≤ n) :
    (#(oddPrimes (n - 3)) : ℝ) + #(oddPrimes (n - 5)) - #(twins n) + 2 ≤ NCount x := by
  unfold NCount
  rw [hn]
  set S3 := (oddPrimes (n - 3)).image (· + 3)
  set S5 := (oddPrimes (n - 5)).image (· + 5)
  have c3 : #S3 = #(oddPrimes (n - 3)) := card_image_of_injective _ (add_left_injective 3)
  have c5 : #S5 = #(oddPrimes (n - 5)) := card_image_of_injective _ (add_left_injective 5)
  have hinter : S3 ∩ S5 ⊆ (twins n).image (· + 5) := by
    intro a ha
    simp only [S3, S5, twins, oddPrimes, mem_inter, mem_image, mem_filter, mem_Icc] at ha ⊢
    obtain ⟨⟨p, ⟨⟨h1, h2⟩, h3⟩, rfl⟩, q, ⟨⟨h4, h5⟩, h6⟩, h7⟩ := ha
    refine ⟨q, ⟨⟨⟨h4, h5⟩, h6⟩, ?_⟩, h7⟩
    have : p = q + 2 := by omega
    rw [← this]; exact h3
  have hci : #(S3 ∩ S5) ≤ #(twins n) :=
    (card_le_card hinter).trans card_image_le
  have hsub : S3 ∪ S5 ∪ {2, 4} ⊆ (Icc 1 n).filter (fun k => Even k ∧ AtMostPrimes 2 k) := by
    intro a ha
    simp only [S3, S5, oddPrimes, mem_union, mem_image, mem_filter, mem_Icc, mem_insert,
      mem_singleton] at ha ⊢
    rcases ha with (⟨p, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ | ⟨p, ⟨⟨h1, h2⟩, h3⟩, rfl⟩) | rfl | rfl
    · have hodd : Odd p := h3.odd_of_ne_two (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · obtain ⟨k, rfl⟩ := hodd; exact ⟨k + 2, by ring⟩
      · exact (AtMostPrimes.prime h3).add (AtMostPrimes.prime Nat.prime_three)
    · have hodd : Odd p := h3.odd_of_ne_two (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · obtain ⟨k, rfl⟩ := hodd; exact ⟨k + 3, by ring⟩
      · exact (AtMostPrimes.prime h3).add (AtMostPrimes.prime Nat.prime_five)
    · exact ⟨⟨by omega, by omega⟩, ⟨1, rfl⟩, (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)⟩
    · exact ⟨⟨by omega, by omega⟩, ⟨2, rfl⟩,
        (AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_two)⟩
  have hdisj : Disjoint (S3 ∪ S5) {2, 4} := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [S3, S5, oddPrimes, mem_union, mem_image, mem_filter, mem_Icc, mem_insert,
      mem_singleton] at ha hb
    rcases ha with ⟨p, ⟨⟨h1, _⟩, _⟩, rfl⟩ | ⟨p, ⟨⟨h1, _⟩, _⟩, rfl⟩ <;> rcases hb with rfl | rfl <;>
      omega
  have h1 := card_union_add_card_inter S3 S5
  have h2 := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at h2
  have h24 : #({2, 4} : Finset ℕ) = 2 := by decide
  rw [h24] at h2
  have : (#(oddPrimes (n - 3)) : ℝ) + #(oddPrimes (n - 5)) ≤ #(S3 ∪ S5) + #(twins n) := by
    rw [← c3, ← c5]; exact_mod_cast (by omega : #S3 + #S5 ≤ #(S3 ∪ S5) + #(twins n))
  have : ((#(S3 ∪ S5) + 2 : ℕ) : ℝ) ≤
      #((Icc 1 n).filter (fun k => Even k ∧ AtMostPrimes 2 k)) := by exact_mod_cast h2
  push_cast at this
  linarith

/-- Page 58, combined: `N(x) ≥ (3/2) π(n - 5)` for `n = ⌊x⌋ ≥ 8`; the paper's
`N(x) ≥ (3/2)π(x) - 4` with `π(x - 5)` in place of `π(x) - 2`. -/
lemma ncount_ge_pi (x : ℝ) (n : ℕ) (hn : ⌊x⌋₊ = n) (h8 : 8 ≤ n) :
    (3 / 2 : ℝ) * Nat.primeCounting (n - 5) ≤ NCount x := by
  have h1 := ncount_ge x n hn h8
  have h2 := two_twins_le n
  have hmono : #(oddPrimes (n - 5)) ≤ #(oddPrimes (n - 3)) := by
    apply card_le_card
    intro a ha
    simp only [oddPrimes, mem_filter, mem_Icc] at ha ⊢
    exact ⟨⟨ha.1.1, by omega⟩, ha.2⟩
  have hpi := primeCounting_eq_oddPrimes (n - 5) (by omega)
  have h2' : (2 : ℝ) * #(twins n) ≤ #(oddPrimes (n - 3)) + 1 := by exact_mod_cast h2
  have hm' : (#(oddPrimes (n - 5)) : ℝ) ≤ #(oddPrimes (n - 3)) := by exact_mod_cast hmono
  rw [hpi]; push_cast
  linarith

/-- 2, 4, 6, 8 are each a sum of at most two primes, so `N(x) ≥ 1` for `x ≥ 2` and
`N(x) ≥ 4` for `x ≥ 8`. -/
lemma ncount_small (x : ℝ) (n : ℕ) (hn : ⌊x⌋₊ = n) :
    (2 ≤ n → 1 ≤ NCount x) ∧ (8 ≤ n → 4 ≤ NCount x) := by
  unfold NCount; rw [hn]
  have hA : ∀ a ∈ ({2, 4, 6, 8} : Finset ℕ), Even a ∧ AtMostPrimes 2 a := by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨⟨1, rfl⟩, (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)⟩
    · exact ⟨⟨2, rfl⟩, (AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_two)⟩
    · exact ⟨⟨3, rfl⟩, (AtMostPrimes.prime Nat.prime_three).add
        (AtMostPrimes.prime Nat.prime_three)⟩
    · exact ⟨⟨4, rfl⟩, (AtMostPrimes.prime Nat.prime_three).add
        (AtMostPrimes.prime Nat.prime_five)⟩
  constructor
  · intro h2
    apply card_pos.mpr
    exact ⟨2, by simp only [mem_filter, mem_Icc]; exact ⟨⟨by omega, h2⟩, hA 2 (by simp)⟩⟩
  · intro h8
    have : ({2, 4, 6, 8} : Finset ℕ) ⊆ (Icc 1 n).filter (fun k => Even k ∧ AtMostPrimes 2 k) := by
      intro a ha
      simp only [mem_filter, mem_Icc]
      refine ⟨?_, hA a ha⟩
      simp only [mem_insert, mem_singleton] at ha
      omega
    exact (by decide : #({2, 4, 6, 8} : Finset ℕ) = 4) ▸ card_le_card this

/-- `e^6 > 403` and `e^27`-free bounds used below. -/
lemma exp_six_gt : (403 : ℝ) < Real.exp 6 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (403 : ℝ) < 2.7182818283 ^ 6 := by norm_num
    _ ≤ Real.exp 1 ^ 6 := by gcongr

/-- **Lemma 7**, CONDITIONAL ON Rosser-Schoenfeld (3.3). -/
theorem lemma7_of_RS (hRS : RS33) : Lemma7 := by
  intro x hx2 hxe
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) < n + 1 := by linarith
    have : (1 : ℝ) < n := by linarith
    exact_mod_cast (show (1 : ℝ) < n from this)
  have hs := ncount_small x n hn.symm
  by_cases h18 : x < 18
  · have := hs.1 hn2
    have : (1 : ℝ) ≤ NCount x := by exact_mod_cast this
    linarith
  by_cases h72 : x < 72
  · have h8 : 8 ≤ n := by
      have : (8 : ℝ) < n + 1 := by linarith
      have : (7 : ℝ) < n := by linarith
      exact_mod_cast this
    have := hs.2 h8
    have : (4 : ℝ) ≤ NCount x := by exact_mod_cast this
    linarith
  push Not at h18 h72
  have h72n : 72 ≤ n := Nat.le_floor (by exact_mod_cast h72)
  have hm := hRS (n - 5) (by omega)
  have hN := ncount_ge_pi x n hn.symm (by omega)
  set m : ℕ := n - 5 with hmdef
  have hmR : (m : ℝ) = n - 5 := by rw [hmdef]; push_cast [show 5 ≤ n by omega]; ring
  have h72R : (72 : ℝ) ≤ n := by exact_mod_cast h72n
  have hm67 : (67 : ℝ) ≤ m := by rw [hmR]; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hlogm_le : Real.log m ≤ 27 := by
    have : (m : ℝ) ≤ Real.exp 27 := by rw [hmR]; linarith
    calc Real.log m ≤ Real.log (Real.exp 27) := Real.log_le_log hmpos this
      _ = 27 := Real.log_exp 27
  have hlogm_ge : (4 : ℝ) < Real.log m := by
    rw [Real.lt_log_iff_exp_lt hmpos]
    have := Real.exp_one_lt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
      _ < 67 := by norm_num
      _ ≤ m := hm67
  have hden : 0 < Real.log m - 1 / 2 := by linarith
  -- `π(m) > m/(log m - 1/2)`, and `N(x) ≥ (3/2) π(m)`
  have key : (3 / 2 : ℝ) * (m / (Real.log m - 1 / 2)) < NCount x := by
    have : (3 / 2 : ℝ) * (m / (Real.log m - 1 / 2)) < 3 / 2 * Nat.primeCounting m := by
      linarith
    linarith
  by_cases hbig : (323 : ℝ) < m
  · -- `log m ≤ 27` gives `(3/2) m/(log m - 1/2) ≥ 3m/53 > (m + 6)/18 > x/18`
    have : (3 / 2 : ℝ) * (m / (53 / 2)) ≤ (3 / 2 : ℝ) * (m / (Real.log m - 1 / 2)) := by
      gcongr; linarith
    have hx : x < m + 6 := by rw [hmR]; linarith
    nlinarith
  · push Not at hbig
    -- `m ≤ 323 < e^6`, so `log m < 6`
    have hlog6 : Real.log m < 6 := by
      rw [Real.log_lt_iff_lt_exp hmpos]; linarith [exp_six_gt]
    have : (3 / 2 : ℝ) * (m / (11 / 2)) ≤ (3 / 2 : ℝ) * (m / (Real.log m - 1 / 2)) := by
      gcongr; linarith
    have hx : x < m + 6 := by rw [hmR]; linarith
    nlinarith

/-- Not in the paper, a modern shortcut: a verification of even Goldbach up to `M` gives
`N(x) > x/18` for `2 ≤ x ≤ M`, since then every even number up to `x` counts. -/
theorem ncount_of_verified {M : ℕ} (hG : EvenGoldbachUpTo M) (x : ℝ) (hx2 : 2 ≤ x)
    (hxM : x ≤ M) : x / 18 < NCount x := by
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := by linarith
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hnM : n ≤ M := Nat.floor_le_of_le (by exact_mod_cast hxM)
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx2)
  have hsub : (Icc 1 (n / 2)).image (2 * ·) ⊆
      (Icc 1 n).filter (fun k => Even k ∧ AtMostPrimes 2 k) := by
    intro a ha
    simp only [mem_image, mem_Icc, mem_filter] at ha ⊢
    obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := ha
    refine ⟨⟨by omega, by omega⟩, ⟨j, by ring⟩, ?_⟩
    by_cases hj : j = 1
    · subst hj; exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
    · exact atMost2_of_even hG ⟨j, by ring⟩ (by omega) |>.mono le_rfl
  have hc := card_le_card hsub
  rw [card_image_of_injective _ (fun a b h => by simpa using h), Nat.card_Icc] at hc
  have h1 : ((n / 2 + 1 - 1 : ℕ) : ℝ) ≤ NCount x := by
    unfold NCount; rw [← hn]; exact_mod_cast hc
  have h2 : ((n : ℝ) - 1) / 2 ≤ ((n / 2 + 1 - 1 : ℕ) : ℝ) := by
    rw [show n / 2 + 1 - 1 = n / 2 by omega]
    have : n - 1 ≤ 2 * (n / 2) := by omega
    have h' : ((n - 1 : ℕ) : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h'
    linarith
  have h2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  linarith

/-- Lemma 7 CONDITIONAL ON the Oliveira e Silva, Herzog, Pardi 4·10^18 verification instead
of Rosser-Schoenfeld: `e^27 < 4·10^18`. The same input covers Lemma 8's first range
`24 ≤ log x ≤ 42`, since `e^42 < 4·10^18`. -/
theorem lemma7_of_oesilva (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) : Lemma7 := by
  intro x hx2 hxe
  apply ncount_of_verified hG x hx2
  refine hxe.trans ?_
  have : Real.exp 27 ≤ Real.exp 42 := Real.exp_le_exp.mpr (by norm_num)
  refine this.trans ?_
  have h := Real.exp_one_lt_d9
  have : Real.exp 42 = Real.exp 1 ^ 42 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 42 ≤ 2.7182818286 ^ 42 := by gcongr
    _ ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) := by norm_num

/-- Lemma 8's first range, `24 ≤ log x ≤ 42`, CONDITIONAL ON the 4·10^18 verification. -/
theorem lemma8_low_of_oesilva (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) (x : ℝ) (hx : 0 < x)
    (hl : Real.log x ≤ 42) (hl24 : 24 ≤ Real.log x) : x / 18 < NCount x := by
  apply ncount_of_verified hG x
  · have : Real.exp 24 ≤ x := by
      rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hl24
    have : (2 : ℝ) ≤ Real.exp 24 := by
      have := Real.add_one_le_exp 24; linarith
    linarith
  · have hx42 : x ≤ Real.exp 42 := by
      rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hl
    refine hx42.trans ?_
    have h := Real.exp_one_lt_d9
    have : Real.exp 42 = Real.exp 1 ^ 42 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 42 ≤ 2.7182818286 ^ 42 := by gcongr
      _ ≤ ((4 * 10 ^ 18 : ℕ) : ℝ) := by norm_num

end LeanLab.RieselVaughan1983
