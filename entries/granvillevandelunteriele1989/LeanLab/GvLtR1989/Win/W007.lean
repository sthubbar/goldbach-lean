module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 28 to 31, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 21, part 1: every even n in [15850002, 16840000] is x + y, x among the first 121 odd primes, y prime. -/
theorem chk_21_1 : oem 15849329 15850002 16840000 &&& gmo (opm 15849329 495336) (QKo 121) = oem 15849329 15850002 16840000 := by
  decide +kernel

/-- Block 22, part 0: every even n in [16840002, 17830000] is x + y, x among the first 129 odd primes, y prime. -/
theorem chk_22_0 : oem 16839269 16840002 17830000 &&& gmo (opm 16839269 495366) (QKo 129) = oem 16839269 16840002 17830000 := by
  decide +kernel

/-- Block 22, part 1: every even n in [17830002, 18820000] is x + y, x among the first 129 odd primes, y prime. -/
theorem chk_22_1 : oem 17829269 17830002 18820000 &&& gmo (opm 17829269 495366) (QKo 129) = oem 17829269 17830002 18820000 := by
  decide +kernel

/-- Block 23, part 0: every even n in [18820002, 19810000] is x + y, x among the first 129 odd primes, y prime. -/
theorem chk_23_0 : oem 18819269 18820002 19810000 &&& gmo (opm 18819269 495366) (QKo 129) = oem 18819269 18820002 19810000 := by
  decide +kernel

end LeanLab.GvLtR1989
