module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.KadiriLumley2014.RowDefinition92
public import LeanLab.Verifications.PrattCertificates

/-!
Kadiri and Lumley 2014, the arithmetic around Corollary 1.2. The proof of the corollary on
page 13 needs one Goldbach partition at the top of the verified even range, since there the
even remainder `n - p` can be `4 · 10^18 + 2`. Here `4 · 10^18 + 2 = 241 + 3999999999999999761`,
with the larger prime certified by Lucas certificates whose modular powers are proved by
`reduce_mod_char`. Also the bound `e^60 ≤ 1.15 · 10^26`, and the natural number form of the
row with `log x0 = 45` of Table 2.
AI wrote this Lean code. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014
open Real LeanLab.Verifications.Pratt

/-! ### `4 · 10^18 + 2 = 241 + 3999999999999999761` -/

theorem p777448979 : Nat.Prime 777448979 := by
  refine prattZ 777448979 2 [(2, 1), (73, 1), (1301, 1), (4093, 1)] (by norm_num) ?_
    (by reduce_mod_char) ?_
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact zmod_ne_one (c := 777448978) (by norm_num) (by norm_num) (by reduce_mod_char)
    · exact zmod_ne_one (c := 230267872) (by norm_num) (by norm_num) (by reduce_mod_char)
    · exact zmod_ne_one (c := 746192081) (by norm_num) (by norm_num) (by reduce_mod_char)
    · exact zmod_ne_one (c := 286835243) (by norm_num) (by norm_num) (by reduce_mod_char)

theorem p13994081623 : Nat.Prime 13994081623 := by
  refine prattZ 13994081623 3 [(2, 1), (3, 2), (777448979, 1)] (by norm_num) ?_
    (by reduce_mod_char) ?_
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact p777448979
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact zmod_ne_one (c := 13994081622) (by norm_num) (by norm_num) (by reduce_mod_char)
    · exact zmod_ne_one (c := 392986110) (by norm_num) (by norm_num) (by reduce_mod_char)
    · exact zmod_ne_one (c := 387420489) (by norm_num) (by norm_num) (by reduce_mod_char)

theorem pBig : Nat.Prime 3999999999999999761 := by
  refine prattZ 3999999999999999761 7 [(2, 4), (5, 1), (3572939, 1), (13994081623, 1)]
    (by norm_num) ?_ (by reduce_mod_char) ?_
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · norm_num
    · exact p13994081623
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact zmod_ne_one (c := 3999999999999999760) (by norm_num) (by norm_num)
        (by reduce_mod_char)
    · exact zmod_ne_one (c := 3021132259357594081) (by norm_num) (by norm_num)
        (by reduce_mod_char)
    · exact zmod_ne_one (c := 1205079373114391672) (by norm_num) (by norm_num)
        (by reduce_mod_char)
    · exact zmod_ne_one (c := 516539784875482545) (by norm_num) (by norm_num)
        (by reduce_mod_char)

/-- `4 · 10^18 + 2 = 241 + 3999999999999999761` is a sum of two primes. -/
theorem goldbach_top : IsGoldbachSum (4 * 10 ^ 18 + 2) :=
  ⟨241, 3999999999999999761, by norm_num, pBig, by norm_num⟩

/-- `e^60 ≤ 1.15 · 10^26`. -/
theorem exp60_le : Real.exp 60 ≤ 1.15 * 10 ^ 26 := by
  have h1 : Real.exp 60 = Real.exp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  calc Real.exp 1 ^ 60 ≤ (2.7182818286 : ℝ) ^ 60 := by gcongr; exact Real.exp_one_lt_d9.le
    _ ≤ 1.15 * 10 ^ 26 := by norm_num

/-- The row with `log x0 = 45` of Table 2 in natural number form: every natural `y > e^45` has
a prime `p < y` with `95381241 (y - p) < y`. -/
theorem kl45_of_row (h : KLRow (Real.exp 45) 95381241) :
    ∀ y : ℕ, Real.exp 45 < y → ∃ p : ℕ, p.Prime ∧ p < y ∧ 95381241 * (y - p) < y := by
  intro y hy
  obtain ⟨p, hp, hl, hu⟩ := h y hy
  have hpy : p < y := by exact_mod_cast hu
  refine ⟨p, hp, hpy, ?_⟩
  have : (95381241 : ℝ) * ((y : ℝ) - p) < y := by
    have : (1 - 1 / (95381241 : ℝ)) * y = y - y / 95381241 := by ring
    rw [this] at hl
    have : (y : ℝ) - p < y / 95381241 := by linarith
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  have hc : ((y - p : ℕ) : ℝ) = (y : ℝ) - p := by
    rw [Nat.cast_sub hpy.le]
  rw [← hc] at this
  exact_mod_cast this

end LeanLab.KadiriLumley2014
