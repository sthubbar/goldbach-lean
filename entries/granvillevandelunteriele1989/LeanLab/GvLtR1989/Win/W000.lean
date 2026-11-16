module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 0 to 3, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 0, part 0: every even n in [6, 6] is x + y, x among the first 1 odd primes, y prime. -/
theorem chk_0_0 : oem 3 6 6 &&& gmo (opm 3 2) (QKo 1) = oem 3 6 6 := by
  decide +kernel

/-- Block 1, part 0: every even n in [8, 8] is x + y, x among the first 1 odd primes, y prime. -/
theorem chk_1_0 : oem 5 8 8 &&& gmo (opm 5 2) (QKo 1) = oem 5 8 8 := by
  decide +kernel

/-- Block 2, part 0: every even n in [10, 28] is x + y, x among the first 2 odd primes, y prime. -/
theorem chk_2_0 : oem 5 10 28 &&& gmo (opm 5 12) (QKo 2) = oem 5 10 28 := by
  decide +kernel

/-- Block 3, part 0: every even n in [30, 96] is x + y, x among the first 3 odd primes, y prime. -/
theorem chk_3_0 : oem 23 30 96 &&& gmo (opm 23 37) (QKo 3) = oem 23 30 96 := by
  decide +kernel

end LeanLab.GvLtR1989
