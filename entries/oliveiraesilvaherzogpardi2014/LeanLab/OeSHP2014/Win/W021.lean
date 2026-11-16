module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 84 to 87, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 0: every even n in [60119912, 61109910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_0 : oem 60118819 60119912 61109910 &&& gmo (opm 60118819 495546) (QKo 182) = oem 60118819 60119912 61109910 := by
  decide +kernel

/-- Segment 27, part 1: every even n in [61109912, 62099910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_1 : oem 61108819 61109912 62099910 &&& gmo (opm 61108819 495546) (QKo 182) = oem 61108819 61109912 62099910 := by
  decide +kernel

/-- Segment 27, part 2: every even n in [62099912, 63089910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_2 : oem 62098819 62099912 63089910 &&& gmo (opm 62098819 495546) (QKo 182) = oem 62098819 62099912 63089910 := by
  decide +kernel

/-- Segment 27, part 3: every even n in [63089912, 64079910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_3 : oem 63088819 63089912 64079910 &&& gmo (opm 63088819 495546) (QKo 182) = oem 63088819 63089912 64079910 := by
  decide +kernel

end LeanLab.OeSHP2014
