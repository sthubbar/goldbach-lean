module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 12 to 15, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 12, part 0: every even n in [1000002, 1990000] is x + y, x among the first 109 odd primes, y prime. -/
theorem chk_12_0 : oem 999401 1000002 1990000 &&& gmo (opm 999401 495300) (QKo 109) = oem 999401 1000002 1990000 := by
  decide +kernel

/-- Block 12, part 1: every even n in [1990002, 2980000] is x + y, x among the first 109 odd primes, y prime. -/
theorem chk_12_1 : oem 1989401 1990002 2980000 &&& gmo (opm 1989401 495300) (QKo 109) = oem 1989401 1990002 2980000 := by
  decide +kernel

/-- Block 13, part 0: every even n in [2980002, 3475000] is x + y, x among the first 98 odd primes, y prime. -/
theorem chk_13_0 : oem 2979479 2980002 3475000 &&& gmo (opm 2979479 247761) (QKo 98) = oem 2979479 2980002 3475000 := by
  decide +kernel

/-- Block 14, part 0: every even n in [3475002, 3970000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_14_0 : oem 3474251 3475002 3970000 &&& gmo (opm 3474251 247875) (QKo 132) = oem 3474251 3475002 3970000 := by
  decide +kernel

end LeanLab.GvLtR1989
