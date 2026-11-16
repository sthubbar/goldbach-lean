module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 32 to 35, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 23, part 1: every even n in [19810002, 20800000] is x + y, x among the first 129 odd primes, y prime. -/
theorem chk_23_1 : oem 19809269 19810002 20800000 &&& gmo (opm 19809269 495366) (QKo 129) = oem 19809269 19810002 20800000 := by
  decide +kernel

/-- Block 24, part 0: every even n in [20800002, 21790000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_24_0 : oem 20799179 20800002 21790000 &&& gmo (opm 20799179 495411) (QKo 142) = oem 20799179 20800002 21790000 := by
  decide +kernel

/-- Block 24, part 1: every even n in [21790002, 22780000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_24_1 : oem 21789179 21790002 22780000 &&& gmo (opm 21789179 495411) (QKo 142) = oem 21789179 21790002 22780000 := by
  decide +kernel

/-- Block 25, part 0: every even n in [22780002, 23770000] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_25_0 : oem 22779073 22780002 23770000 &&& gmo (opm 22779073 495464) (QKo 157) = oem 22779073 22780002 23770000 := by
  decide +kernel

end LeanLab.GvLtR1989
