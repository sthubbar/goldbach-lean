module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 112 to 115, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 63, part 1: every even n in [99010002, 100000000] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_63_1 : oem 99009173 99010002 100000000 &&& gmo (opm 99009173 495414) (QKo 144) = oem 99009173 99010002 100000000 := by
  decide +kernel

/-- Block 64, part 0: every even n in [100000002, 100990000] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_64_0 : oem 99998963 100000002 100990000 &&& gmo (opm 99998963 495519) (QKo 174) = oem 99998963 100000002 100990000 := by
  decide +kernel

/-- Block 64, part 1: every even n in [100990002, 101980000] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_64_1 : oem 100988963 100990002 101980000 &&& gmo (opm 100988963 495519) (QKo 174) = oem 100988963 100990002 101980000 := by
  decide +kernel

/-- Block 65, part 0: every even n in [101980002, 102970000] is x + y, x among the first 161 odd primes, y prime. -/
theorem chk_65_0 : oem 101979049 101980002 102970000 &&& gmo (opm 101979049 495476) (QKo 161) = oem 101979049 101980002 102970000 := by
  decide +kernel

end LeanLab.GvLtR1989
