module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 8 to 11, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 8, part 0: every even n in [2642, 5370] is x + y, x among the first 26 odd primes, y prime. -/
theorem chk_8_0 : oem 2539 2642 5370 &&& gmo (opm 2539 1416) (QKo 26) = oem 2539 2642 5370 := by
  decide +kernel

/-- Segment 9, part 0: every even n in [5372, 7424] is x + y, x among the first 33 odd primes, y prime. -/
theorem chk_9_0 : oem 5233 5372 7424 &&& gmo (opm 5233 1096) (QKo 33) = oem 5233 5372 7424 := by
  decide +kernel

/-- Segment 10, part 0: every even n in [7426, 43530] is x + y, x among the first 39 odd primes, y prime. -/
theorem chk_10_0 : oem 7253 7426 43530 &&& gmo (opm 7253 18139) (QKo 39) = oem 7253 7426 43530 := by
  decide +kernel

/-- Segment 11, part 0: every even n in [43532, 54242] is x + y, x among the first 46 odd primes, y prime. -/
theorem chk_11_0 : oem 43321 43532 54242 &&& gmo (opm 43321 5461) (QKo 46) = oem 43321 43532 54242 := by
  decide +kernel

end LeanLab.OeSHP2014
