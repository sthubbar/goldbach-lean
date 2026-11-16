module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 28 to 31, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 22, part 4: every even n in [7767404, 8757402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_4 : oem 7766653 7767404 8757402 &&& gmo (opm 7766653 495375) (QKo 132) = oem 7766653 7767404 8757402 := by
  decide +kernel

/-- Segment 22, part 5: every even n in [8757404, 9747402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_5 : oem 8756653 8757404 9747402 &&& gmo (opm 8756653 495375) (QKo 132) = oem 8756653 8757404 9747402 := by
  decide +kernel

/-- Segment 22, part 6: every even n in [9747404, 10737402] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_6 : oem 9746653 9747404 10737402 &&& gmo (opm 9746653 495375) (QKo 132) = oem 9746653 9747404 10737402 := by
  decide +kernel

/-- Segment 22, part 7: every even n in [10737404, 10759920] is x + y, x among the first 132 odd primes, y prime. -/
theorem chk_22_7 : oem 10736653 10737404 10759920 &&& gmo (opm 10736653 11634) (QKo 132) = oem 10736653 10737404 10759920 := by
  decide +kernel

end LeanLab.OeSHP2014
