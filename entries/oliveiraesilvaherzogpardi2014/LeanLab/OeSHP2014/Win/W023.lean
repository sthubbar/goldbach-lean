module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 92 to 95, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 27, part 8: every even n in [68039912, 69029910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_8 : oem 68038819 68039912 69029910 &&& gmo (opm 68038819 495546) (QKo 182) = oem 68038819 68039912 69029910 := by
  decide +kernel

/-- Segment 27, part 9: every even n in [69029912, 70019910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_9 : oem 69028819 69029912 70019910 &&& gmo (opm 69028819 495546) (QKo 182) = oem 69028819 69029912 70019910 := by
  decide +kernel

/-- Segment 27, part 10: every even n in [70019912, 71009910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_10 : oem 70018819 70019912 71009910 &&& gmo (opm 70018819 495546) (QKo 182) = oem 70018819 70019912 71009910 := by
  decide +kernel

/-- Segment 27, part 11: every even n in [71009912, 71999910] is x + y, x among the first 182 odd primes, y prime. -/
theorem chk_27_11 : oem 71008819 71009912 71999910 &&& gmo (opm 71008819 495546) (QKo 182) = oem 71008819 71009912 71999910 := by
  decide +kernel

end LeanLab.OeSHP2014
