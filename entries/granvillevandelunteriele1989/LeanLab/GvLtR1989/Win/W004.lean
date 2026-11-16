module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 16 to 19, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 15, part 0: every even n in [3970002, 4960000] is x + y, x among the first 110 odd primes, y prime. -/
theorem chk_15_0 : oem 3969395 3970002 4960000 &&& gmo (opm 3969395 495303) (QKo 110) = oem 3969395 3970002 4960000 := by
  decide +kernel

/-- Block 16, part 0: every even n in [4960002, 5950000] is x + y, x among the first 115 odd primes, y prime. -/
theorem chk_16_0 : oem 4959361 4960002 5950000 &&& gmo (opm 4959361 495320) (QKo 115) = oem 4959361 4960002 5950000 := by
  decide +kernel

/-- Block 16, part 1: every even n in [5950002, 6940000] is x + y, x among the first 115 odd primes, y prime. -/
theorem chk_16_1 : oem 5949361 5950002 6940000 &&& gmo (opm 5949361 495320) (QKo 115) = oem 5949361 5950002 6940000 := by
  decide +kernel

/-- Block 17, part 0: every even n in [6940002, 7930000] is x + y, x among the first 129 odd primes, y prime. -/
theorem chk_17_0 : oem 6939269 6940002 7930000 &&& gmo (opm 6939269 495366) (QKo 129) = oem 6939269 6940002 7930000 := by
  decide +kernel

end LeanLab.GvLtR1989
