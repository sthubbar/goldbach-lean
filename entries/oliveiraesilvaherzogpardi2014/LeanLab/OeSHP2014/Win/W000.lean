module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 0 to 3, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 0, part 0: every even n in [6, 10] is x + y, x among the first 1 odd primes, y prime. -/
theorem chk_0_0 : oem 3 6 10 &&& gmo (opm 3 4) (QKo 1) = oem 3 6 10 := by
  decide +kernel

/-- Segment 1, part 0: every even n in [12, 28] is x + y, x among the first 2 odd primes, y prime. -/
theorem chk_1_0 : oem 7 12 28 &&& gmo (opm 7 11) (QKo 2) = oem 7 12 28 := by
  decide +kernel

/-- Segment 2, part 0: every even n in [30, 96] is x + y, x among the first 3 odd primes, y prime. -/
theorem chk_2_0 : oem 23 30 96 &&& gmo (opm 23 37) (QKo 3) = oem 23 30 96 := by
  decide +kernel

/-- Segment 3, part 0: every even n in [98, 218] is x + y, x among the first 7 odd primes, y prime. -/
theorem chk_3_0 : oem 79 98 218 &&& gmo (opm 79 70) (QKo 7) = oem 79 98 218 := by
  decide +kernel

end LeanLab.OeSHP2014
