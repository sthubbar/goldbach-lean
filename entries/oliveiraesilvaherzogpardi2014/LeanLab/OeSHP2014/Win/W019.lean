module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 76 to 79, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 26, part 15: every even n in [52848938, 53838936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_15 : oem 52847899 52848938 53838936 &&& gmo (opm 52847899 495519) (QKo 174) = oem 52847899 52848938 53838936 := by
  decide +kernel

/-- Segment 26, part 16: every even n in [53838938, 54828936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_16 : oem 53837899 53838938 54828936 &&& gmo (opm 53837899 495519) (QKo 174) = oem 53837899 53838938 54828936 := by
  decide +kernel

/-- Segment 26, part 17: every even n in [54828938, 55818936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_17 : oem 54827899 54828938 55818936 &&& gmo (opm 54827899 495519) (QKo 174) = oem 54827899 54828938 55818936 := by
  decide +kernel

/-- Segment 26, part 18: every even n in [55818938, 56808936] is x + y, x among the first 174 odd primes, y prime. -/
theorem chk_26_18 : oem 55817899 55818938 56808936 &&& gmo (opm 55817899 495519) (QKo 174) = oem 55817899 55818938 56808936 := by
  decide +kernel

end LeanLab.OeSHP2014
