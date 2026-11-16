module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 36 to 39, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 25, part 1: every even n in [23770002, 24760000] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_25_1 : oem 23769073 23770002 24760000 &&& gmo (opm 23769073 495464) (QKo 157) = oem 23769073 23770002 24760000 := by
  decide +kernel

/-- Block 26, part 0: every even n in [24760002, 25750000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_26_0 : oem 24759251 24760002 25750000 &&& gmo (opm 24759251 495375) (QKo 132) = oem 24759251 24760002 25750000 := by
  decide +kernel

/-- Block 26, part 1: every even n in [25750002, 26740000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_26_1 : oem 25749251 25750002 26740000 &&& gmo (opm 25749251 495375) (QKo 132) = oem 25749251 25750002 26740000 := by
  decide +kernel

/-- Block 27, part 0: every even n in [26740002, 27730000] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_27_0 : oem 26739005 26740002 27730000 &&& gmo (opm 26739005 495498) (QKo 167) = oem 26739005 26740002 27730000 := by
  decide +kernel

end LeanLab.GvLtR1989
