module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 96 to 99, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 55, part 1: every even n in [83170002, 84160000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_55_1 : oem 83169191 83170002 84160000 &&& gmo (opm 83169191 495405) (QKo 140) = oem 83169191 83170002 84160000 := by
  decide +kernel

/-- Block 56, part 0: every even n in [84160002, 85150000] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_56_0 : oem 84159073 84160002 85150000 &&& gmo (opm 84159073 495464) (QKo 157) = oem 84159073 84160002 85150000 := by
  decide +kernel

/-- Block 56, part 1: every even n in [85150002, 86140000] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_56_1 : oem 85149073 85150002 86140000 &&& gmo (opm 85149073 495464) (QKo 157) = oem 85149073 85150002 86140000 := by
  decide +kernel

/-- Block 57, part 0: every even n in [86140002, 87130000] is x + y, x among the first 154 odd primes, y prime. -/
theorem chk_57_0 : oem 86139095 86140002 87130000 &&& gmo (opm 86139095 495453) (QKo 154) = oem 86139095 86140002 87130000 := by
  decide +kernel

end LeanLab.GvLtR1989
