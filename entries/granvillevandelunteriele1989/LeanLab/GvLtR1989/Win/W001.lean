module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 4 to 7, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 4, part 0: every even n in [98, 552] is x + y, x among the first 10 odd primes, y prime. -/
theorem chk_4_0 : oem 67 98 552 &&& gmo (opm 67 243) (QKo 10) = oem 67 98 552 := by
  decide +kernel

/-- Block 5, part 0: every even n in [554, 2638] is x + y, x among the first 20 odd primes, y prime. -/
theorem chk_5_0 : oem 481 554 2638 &&& gmo (opm 481 1079) (QKo 20) = oem 481 554 2638 := by
  decide +kernel

/-- Block 6, part 0: every even n in [2640, 7424] is x + y, x among the first 33 odd primes, y prime. -/
theorem chk_6_0 : oem 2501 2640 7424 &&& gmo (opm 2501 2462) (QKo 33) = oem 2501 2640 7424 := by
  decide +kernel

/-- Block 7, part 0: every even n in [7426, 54242] is x + y, x among the first 46 odd primes, y prime. -/
theorem chk_7_0 : oem 7215 7426 54242 &&& gmo (opm 7215 23514) (QKo 46) = oem 7215 7426 54242 := by
  decide +kernel

end LeanLab.GvLtR1989
