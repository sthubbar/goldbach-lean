module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 20 to 23, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 17, part 1: every even n in [7930002, 8920000] is x + y, x among the first 129 odd primes, y prime. -/
theorem chk_17_1 : oem 7929269 7930002 8920000 &&& gmo (opm 7929269 495366) (QKo 129) = oem 7929269 7930002 8920000 := by
  decide +kernel

/-- Block 18, part 0: every even n in [8920002, 9910000] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_18_0 : oem 8919173 8920002 9910000 &&& gmo (opm 8919173 495414) (QKo 144) = oem 8919173 8920002 9910000 := by
  decide +kernel

/-- Block 18, part 1: every even n in [9910002, 10900000] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_18_1 : oem 9909173 9910002 10900000 &&& gmo (opm 9909173 495414) (QKo 144) = oem 9909173 9910002 10900000 := by
  decide +kernel

/-- Block 19, part 0: every even n in [10900002, 11890000] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_19_0 : oem 10899251 10900002 11890000 &&& gmo (opm 10899251 495375) (QKo 132) = oem 10899251 10900002 11890000 := by
  decide +kernel

end LeanLab.GvLtR1989
