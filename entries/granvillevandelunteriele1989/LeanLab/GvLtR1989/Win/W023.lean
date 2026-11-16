module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 92 to 95, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 53, part 1: every even n in [79210002, 80200000] is x + y, x among the first 168 odd primes, y prime. -/
theorem chk_53_1 : oem 79208993 79210002 80200000 &&& gmo (opm 79208993 495504) (QKo 168) = oem 79208993 79210002 80200000 := by
  decide +kernel

/-- Block 54, part 0: every even n in [80200002, 81190000] is x + y, x among the first 130 odd primes, y prime. -/
theorem chk_54_0 : oem 80199263 80200002 81190000 &&& gmo (opm 80199263 495369) (QKo 130) = oem 80199263 80200002 81190000 := by
  decide +kernel

/-- Block 54, part 1: every even n in [81190002, 82180000] is x + y, x among the first 130 odd primes, y prime. -/
theorem chk_54_1 : oem 81189263 81190002 82180000 &&& gmo (opm 81189263 495369) (QKo 130) = oem 81189263 81190002 82180000 := by
  decide +kernel

/-- Block 55, part 0: every even n in [82180002, 83170000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_55_0 : oem 82179191 82180002 83170000 &&& gmo (opm 82179191 495405) (QKo 140) = oem 82179191 82180002 83170000 := by
  decide +kernel

end LeanLab.GvLtR1989
