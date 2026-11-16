module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 120 to 123, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 36: every even n in [95759912, 96749910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_36 : oem 95758819 95759912 96749910 &&& gmo (opm 95758819 495546) (QKo 182) = oem 95758819 95759912 96749910 := by
  decide +kernel

/-- Segment 27, part 37: every even n in [96749912, 97739910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_37 : oem 96748819 96749912 97739910 &&& gmo (opm 96748819 495546) (QKo 182) = oem 96748819 96749912 97739910 := by
  decide +kernel

/-- Segment 27, part 38: every even n in [97739912, 98729910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_38 : oem 97738819 97739912 98729910 &&& gmo (opm 97738819 495546) (QKo 182) = oem 97738819 97739912 98729910 := by
  decide +kernel

/-- Segment 27, part 39: every even n in [98729912, 99719910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_39 : oem 98728819 98729912 99719910 &&& gmo (opm 98728819 495546) (QKo 182) = oem 98728819 98729912 99719910 := by
  decide +kernel

end LeanLab.OeSHP2014
