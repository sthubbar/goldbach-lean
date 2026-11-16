module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 100 to 103, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 57, part 1: every even n in [87130002, 88120000] is x + y, x among the first 154 odd primes, y prime. -/
theorem chk_57_1 : oem 87129095 87130002 88120000 &&& gmo (opm 87129095 495453) (QKo 154) = oem 87129095 87130002 88120000 := by
  decide +kernel

/-- Block 58, part 0: every even n in [88120002, 89110000] is x + y, x among the first 147 odd primes, y prime. -/
theorem chk_58_0 : oem 88119145 88120002 89110000 &&& gmo (opm 88119145 495428) (QKo 147) = oem 88119145 88120002 89110000 := by
  decide +kernel

/-- Block 58, part 1: every even n in [89110002, 90100000] is x + y, x among the first 147 odd primes, y prime. -/
theorem chk_58_1 : oem 89109145 89110002 90100000 &&& gmo (opm 89109145 495428) (QKo 147) = oem 89109145 89110002 90100000 := by
  decide +kernel

/-- Block 59, part 0: every even n in [90100002, 91090000] is x + y, x among the first 141 odd primes, y prime. -/
theorem chk_59_0 : oem 90099181 90100002 91090000 &&& gmo (opm 90099181 495410) (QKo 141) = oem 90099181 90100002 91090000 := by
  decide +kernel

end LeanLab.GvLtR1989
