module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 12 to 15, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 12, part 0: every even n in [54244, 63272] is x + y, x among the first 50 odd primes, y prime. -/
theorem chk_12_0 : oem 54011 54244 63272 &&& gmo (opm 54011 4631) (QKo 50) = oem 54011 54244 63272 := by
  decide +kernel

/-- Segment 13, part 0: every even n in [63274, 113670] is x + y, x among the first 61 odd primes, y prime. -/
theorem chk_13_0 : oem 62981 63274 113670 &&& gmo (opm 62981 25345) (QKo 61) = oem 62981 63274 113670 := by
  decide +kernel

/-- Segment 14, part 0: every even n in [113672, 128166] is x + y, x among the first 64 odd primes, y prime. -/
theorem chk_14_0 : oem 113359 113672 128166 &&& gmo (opm 113359 7404) (QKo 64) = oem 113359 113672 128166 := by
  decide +kernel

/-- Segment 15, part 0: every even n in [128168, 194426] is x + y, x among the first 66 odd primes, y prime. -/
theorem chk_15_0 : oem 127837 128168 194426 &&& gmo (opm 127837 33295) (QKo 66) = oem 127837 128168 194426 := by
  decide +kernel

end LeanLab.OeSHP2014
