module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 56 to 59, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 35, part 1: every even n in [43570002, 44560000] is x + y, x among the first 135 odd primes, y prime. -/
theorem chk_35_1 : oem 43569233 43570002 44560000 &&& gmo (opm 43569233 495384) (QKo 135) = oem 43569233 43570002 44560000 := by
  decide +kernel

/-- Block 36, part 0: every even n in [44560002, 45550000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_36_0 : oem 44559179 44560002 45550000 &&& gmo (opm 44559179 495411) (QKo 142) = oem 44559179 44560002 45550000 := by
  decide +kernel

/-- Block 36, part 1: every even n in [45550002, 46540000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_36_1 : oem 45549179 45550002 46540000 &&& gmo (opm 45549179 495411) (QKo 142) = oem 45549179 45550002 46540000 := by
  decide +kernel

/-- Block 37, part 0: every even n in [46540002, 47530000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_37_0 : oem 46539191 46540002 47530000 &&& gmo (opm 46539191 495405) (QKo 140) = oem 46539191 46540002 47530000 := by
  decide +kernel

end LeanLab.GvLtR1989
