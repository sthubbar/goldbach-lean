module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 24 to 27, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 19, part 1: every even n in [11890002, 12880000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_19_1 : oem 11889251 11890002 12880000 &&& gmo (opm 11889251 495375) (QKo 132) = oem 11889251 11890002 12880000 := by
  decide +kernel

/-- Block 20, part 0: every even n in [12880002, 13870000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_20_0 : oem 12879251 12880002 13870000 &&& gmo (opm 12879251 495375) (QKo 132) = oem 12879251 12880002 13870000 := by
  decide +kernel

/-- Block 20, part 1: every even n in [13870002, 14860000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_20_1 : oem 13869251 13870002 14860000 &&& gmo (opm 13869251 495375) (QKo 132) = oem 13869251 13870002 14860000 := by
  decide +kernel

/-- Block 21, part 0: every even n in [14860002, 15850000] is x + y, x among the first 121 odd primes, y prime. -/
theorem chk_21_0 : oem 14859329 14860002 15850000 &&& gmo (opm 14859329 495336) (QKo 121) = oem 14859329 14860002 15850000 := by
  decide +kernel

end LeanLab.GvLtR1989
