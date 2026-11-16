module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 8 to 11, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 8, part 0: every even n in [54244, 194426] is x + y, x among the first 66 odd primes, y prime. -/
theorem chk_8_0 : oem 53913 54244 194426 &&& gmo (opm 53913 70257) (QKo 66) = oem 53913 54244 194426 := by
  decide +kernel

/-- Block 9, part 0: every even n in [194428, 503218] is x + y, x among the first 76 odd primes, y prime. -/
theorem chk_9_0 : oem 194039 194428 503218 &&& gmo (opm 194039 154590) (QKo 76) = oem 194039 194428 503218 := by
  decide +kernel

/-- Block 10, part 0: every even n in [503220, 999998] is x + y, x among the first 98 odd primes, y prime. -/
theorem chk_10_0 : oem 502697 503220 999998 &&& gmo (opm 502697 248651) (QKo 98) = oem 502697 503220 999998 := by
  decide +kernel

/-- Block 11, part 0: every even n in [1000000, 1000000] is x + y, x among the first 6 odd primes, y prime. -/
theorem chk_11_0 : oem 999983 1000000 1000000 &&& gmo (opm 999983 9) (QKo 6) = oem 999983 1000000 1000000 := by
  decide +kernel

end LeanLab.GvLtR1989
