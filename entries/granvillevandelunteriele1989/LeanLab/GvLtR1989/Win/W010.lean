module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 40 to 43, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 27, part 1: every even n in [27730002, 28720000] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_27_1 : oem 27729005 27730002 28720000 &&& gmo (opm 27729005 495498) (QKo 167) = oem 27729005 27730002 28720000 := by
  decide +kernel

/-- Block 28, part 0: every even n in [28720002, 29710000] is x + y, x among the first 138 odd primes, y prime. -/
theorem chk_28_0 : oem 28719205 28720002 29710000 &&& gmo (opm 28719205 495398) (QKo 138) = oem 28719205 28720002 29710000 := by
  decide +kernel

/-- Block 28, part 1: every even n in [29710002, 30700000] is x + y, x among the first 138 odd primes, y prime. -/
theorem chk_28_1 : oem 29709205 29710002 30700000 &&& gmo (opm 29709205 495398) (QKo 138) = oem 29709205 29710002 30700000 := by
  decide +kernel

/-- Block 29, part 0: every even n in [30700002, 31690000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_29_0 : oem 30699191 30700002 31690000 &&& gmo (opm 30699191 495405) (QKo 140) = oem 30699191 30700002 31690000 := by
  decide +kernel

end LeanLab.GvLtR1989
