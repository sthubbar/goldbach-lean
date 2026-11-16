module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Verifications.PrattCertificates

/-!
The prime `3999999999999999761`, certified by Lucas certificates whose modular powers are proved by `reduce_mod_char`, with
its two large auxiliary primes. It is the prime just below `4 · 10^18` used to close the top
of the finite range in `Dudek2014/MaxGap.lean`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014
open Real LeanLab.Verifications.Pratt

/-! ### The prime `3999999999999999761` -/

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

end LeanLab.KadiriLumley2014
