module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 60 to 63, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 37, part 1: every even n in [47530002, 48520000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_37_1 : oem 47529191 47530002 48520000 &&& gmo (opm 47529191 495405) (QKo 140) = oem 47529191 47530002 48520000 := by
  decide +kernel

/-- Block 38, part 0: every even n in [48520002, 49510000] is x + y, x among the first 134 odd primes, y prime. -/
theorem chk_38_0 : oem 48519241 48520002 49510000 &&& gmo (opm 48519241 495380) (QKo 134) = oem 48519241 48520002 49510000 := by
  decide +kernel

/-- Block 38, part 1: every even n in [49510002, 50500000] is x + y, x among the first 134 odd primes, y prime. -/
theorem chk_38_1 : oem 49509241 49510002 50500000 &&& gmo (opm 49509241 495380) (QKo 134) = oem 49509241 49510002 50500000 := by
  decide +kernel

/-- Block 39, part 0: every even n in [50500002, 51490000] is x + y, x among the first 141 odd primes, y prime. -/
theorem chk_39_0 : oem 50499181 50500002 51490000 &&& gmo (opm 50499181 495410) (QKo 141) = oem 50499181 50500002 51490000 := by
  decide +kernel

end LeanLab.GvLtR1989
