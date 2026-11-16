module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 4 to 7, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 4, part 0: every even n in [220, 306] is x + y, x among the first 8 odd primes, y prime. -/
theorem chk_4_0 : oem 197 220 306 &&& gmo (opm 197 55) (QKo 8) = oem 197 220 306 := by
  decide +kernel

/-- Segment 5, part 0: every even n in [308, 554] is x + y, x among the first 10 odd primes, y prime. -/
theorem chk_5_0 : oem 277 308 554 &&& gmo (opm 277 139) (QKo 10) = oem 277 308 554 := by
  decide +kernel

/-- Segment 6, part 0: every even n in [556, 990] is x + y, x among the first 14 odd primes, y prime. -/
theorem chk_6_0 : oem 509 556 990 &&& gmo (opm 509 241) (QKo 14) = oem 509 556 990 := by
  decide +kernel

/-- Segment 7, part 0: every even n in [992, 2640] is x + y, x among the first 20 odd primes, y prime. -/
theorem chk_7_0 : oem 919 992 2640 &&& gmo (opm 919 861) (QKo 20) = oem 919 992 2640 := by
  decide +kernel

end LeanLab.OeSHP2014
