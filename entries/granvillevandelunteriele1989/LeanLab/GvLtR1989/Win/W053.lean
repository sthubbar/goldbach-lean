module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 212 to 215, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 113, part 1: every even n in [198010002, 199000000] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_113_1 : oem 198009173 198010002 199000000 &&& gmo (opm 198009173 495414) (QKo 144) = oem 198009173 198010002 199000000 := by
  decide +kernel

/-- Block 114, part 0: every even n in [199000002, 199990000] is x + y, x among the first 149 odd primes, y prime. -/
theorem chk_114_0 : oem 198999139 199000002 199990000 &&& gmo (opm 198999139 495431) (QKo 149) = oem 198999139 199000002 199990000 := by
  decide +kernel

/-- Block 114, part 1: every even n in [199990002, 200980000] is x + y, x among the first 149 odd primes, y prime. -/
theorem chk_114_1 : oem 199989139 199990002 200980000 &&& gmo (opm 199989139 495431) (QKo 149) = oem 199989139 199990002 200980000 := by
  decide +kernel

/-- Block 115, part 0: every even n in [200980002, 201970000] is x + y, x among the first 180 odd primes, y prime. -/
theorem chk_115_0 : oem 200978915 200980002 201970000 &&& gmo (opm 200978915 495543) (QKo 180) = oem 200978915 200980002 201970000 := by
  decide +kernel

end LeanLab.GvLtR1989
