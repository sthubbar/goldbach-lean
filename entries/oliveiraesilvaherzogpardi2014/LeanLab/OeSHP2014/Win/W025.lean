module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 100 to 103, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 16: every even n in [75959912, 76949910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_16 : oem 75958819 75959912 76949910 &&& gmo (opm 75958819 495546) (QKo 182) = oem 75958819 75959912 76949910 := by
  decide +kernel

/-- Segment 27, part 17: every even n in [76949912, 77939910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_17 : oem 76948819 76949912 77939910 &&& gmo (opm 76948819 495546) (QKo 182) = oem 76948819 76949912 77939910 := by
  decide +kernel

/-- Segment 27, part 18: every even n in [77939912, 78929910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_18 : oem 77938819 77939912 78929910 &&& gmo (opm 77938819 495546) (QKo 182) = oem 77938819 77939912 78929910 := by
  decide +kernel

/-- Segment 27, part 19: every even n in [78929912, 79919910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_19 : oem 78928819 78929912 79919910 &&& gmo (opm 78928819 495546) (QKo 182) = oem 78928819 78929912 79919910 := by
  decide +kernel

end LeanLab.OeSHP2014
