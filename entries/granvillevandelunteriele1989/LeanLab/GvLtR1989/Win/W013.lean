module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 52 to 55, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 33, part 1: every even n in [39610002, 40600000] is x + y, x among the first 137 odd primes, y prime. -/
theorem chk_33_1 : oem 39609215 39610002 40600000 &&& gmo (opm 39609215 495393) (QKo 137) = oem 39609215 39610002 40600000 := by
  decide +kernel

/-- Block 34, part 0: every even n in [40600002, 41590000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_34_0 : oem 40599179 40600002 41590000 &&& gmo (opm 40599179 495411) (QKo 142) = oem 40599179 40600002 41590000 := by
  decide +kernel

/-- Block 34, part 1: every even n in [41590002, 42580000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_34_1 : oem 41589179 41590002 42580000 &&& gmo (opm 41589179 495411) (QKo 142) = oem 41589179 41590002 42580000 := by
  decide +kernel

/-- Block 35, part 0: every even n in [42580002, 43570000] is x + y, x among the first 135 odd primes, y prime. -/
theorem chk_35_0 : oem 42579233 42580002 43570000 &&& gmo (opm 42579233 495384) (QKo 135) = oem 42579233 42580002 43570000 := by
  decide +kernel

end LeanLab.GvLtR1989
