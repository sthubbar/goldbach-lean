module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 60 to 63, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 25, part 10: every even n in [37689878, 37998936] is x + y, x among the first 167 odd primes, y prime. -/
theorem chk_25_10 : oem 37688881 37689878 37998936 &&& gmo (opm 37688881 155028) (QKo 167) = oem 37688881 37689878 37998936 := by
  decide +kernel

/-- Segment 26, part 0: every even n in [37998938, 38988936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_0 : oem 37997899 37998938 38988936 &&& gmo (opm 37997899 495519) (QKo 174) = oem 37997899 37998938 38988936 := by
  decide +kernel

/-- Segment 26, part 1: every even n in [38988938, 39978936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_1 : oem 38987899 38988938 39978936 &&& gmo (opm 38987899 495519) (QKo 174) = oem 38987899 38988938 39978936 := by
  decide +kernel

/-- Segment 26, part 2: every even n in [39978938, 40968936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_2 : oem 39977899 39978938 40968936 &&& gmo (opm 39977899 495519) (QKo 174) = oem 39977899 39978938 40968936 := by
  decide +kernel

end LeanLab.OeSHP2014
