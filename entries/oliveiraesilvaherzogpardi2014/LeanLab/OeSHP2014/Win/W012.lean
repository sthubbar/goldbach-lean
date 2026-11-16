module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 48 to 51, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 24, part 2: every even n in [26086882, 27076880] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_24_2 : oem 26085953 26086882 27076880 &&& gmo (opm 26085953 495464) (QKo 157) = oem 26085953 26086882 27076880 := by
  decide +kernel

/-- Segment 24, part 3: every even n in [27076882, 27789876] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_24_3 : oem 27075953 27076882 27789876 &&& gmo (opm 27075953 356962) (QKo 157) = oem 27075953 27076882 27789876 := by
  decide +kernel

/-- Segment 25, part 0: every even n in [27789878, 28779876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_0 : oem 27788881 27789878 28779876 &&& gmo (opm 27788881 495498) (QKo 167) = oem 27788881 27789878 28779876 := by
  decide +kernel

/-- Segment 25, part 1: every even n in [28779878, 29769876] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_1 : oem 28778881 28779878 29769876 &&& gmo (opm 28778881 495498) (QKo 167) = oem 28778881 28779878 29769876 := by
  decide +kernel

end LeanLab.OeSHP2014
