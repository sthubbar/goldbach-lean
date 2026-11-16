module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 48 to 51, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 31, part 1: every even n in [35650002, 36640000] is x + y, x among the first 150 odd primes, y prime. -/
theorem chk_31_1 : oem 35649125 35650002 36640000 &&& gmo (opm 35649125 495438) (QKo 150) = oem 35649125 35650002 36640000 := by
  decide +kernel

/-- Block 32, part 0: every even n in [36640002, 37630000] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_32_0 : oem 36638963 36640002 37630000 &&& gmo (opm 36638963 495519) (QKo 174) = oem 36638963 36640002 37630000 := by
  decide +kernel

/-- Block 32, part 1: every even n in [37630002, 38620000] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_32_1 : oem 37628963 37630002 38620000 &&& gmo (opm 37628963 495519) (QKo 174) = oem 37628963 37630002 38620000 := by
  decide +kernel

/-- Block 33, part 0: every even n in [38620002, 39610000] is x + y, x among the first 137 odd primes, y prime. -/
theorem chk_33_0 : oem 38619215 38620002 39610000 &&& gmo (opm 38619215 495393) (QKo 137) = oem 38619215 38620002 39610000 := by
  decide +kernel

end LeanLab.GvLtR1989
