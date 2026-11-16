module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 68 to 71, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 41, part 1: every even n in [55450002, 56440000] is x + y, x among the first 147 odd primes, y prime. -/
theorem chk_41_1 : oem 55449145 55450002 56440000 &&& gmo (opm 55449145 495428) (QKo 147) = oem 55449145 55450002 56440000 := by
  decide +kernel

/-- Block 42, part 0: every even n in [56440002, 57430000] is x + y, x among the first 139 odd primes, y prime. -/
theorem chk_42_0 : oem 56439193 56440002 57430000 &&& gmo (opm 56439193 495404) (QKo 139) = oem 56439193 56440002 57430000 := by
  decide +kernel

/-- Block 42, part 1: every even n in [57430002, 58420000] is x + y, x among the first 139 odd primes, y prime. -/
theorem chk_42_1 : oem 57429193 57430002 58420000 &&& gmo (opm 57429193 495404) (QKo 139) = oem 57429193 57430002 58420000 := by
  decide +kernel

/-- Block 43, part 0: every even n in [58420002, 59410000] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_43_0 : oem 58418909 58420002 59410000 &&& gmo (opm 58418909 495546) (QKo 182) = oem 58418909 58420002 59410000 := by
  decide +kernel

end LeanLab.GvLtR1989
