module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 256 to 259, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 135, part 1: every even n in [241570002, 242560000] is x + y, x among the first 150 odd primes, y prime. -/
theorem chk_135_1 : oem 241569125 241570002 242560000 &&& gmo (opm 241569125 495438) (QKo 150) = oem 241569125 241570002 242560000 := by
  decide +kernel

/-- Block 136, part 0: every even n in [242560002, 243550000] is x + y, x among the first 148 odd primes, y prime. -/
theorem chk_136_0 : oem 242559143 242560002 243550000 &&& gmo (opm 242559143 495429) (QKo 148) = oem 242559143 242560002 243550000 := by
  decide +kernel

/-- Block 136, part 1: every even n in [243550002, 244540000] is x + y, x among the first 148 odd primes, y prime. -/
theorem chk_136_1 : oem 243549143 243550002 244540000 &&& gmo (opm 243549143 495429) (QKo 148) = oem 243549143 243550002 244540000 := by
  decide +kernel

/-- Block 137, part 0: every even n in [244540002, 245530000] is x + y, x among the first 170 odd primes, y prime. -/
theorem chk_137_0 : oem 244538983 244540002 245530000 &&& gmo (opm 244538983 495509) (QKo 170) = oem 244538983 244540002 245530000 := by
  decide +kernel

end LeanLab.GvLtR1989
