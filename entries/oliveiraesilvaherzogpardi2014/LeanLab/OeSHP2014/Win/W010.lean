module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 40 to 43, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 23, part 8: every even n in [18679922, 19669920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_8 : oem 18679093 18679922 19669920 &&& gmo (opm 18679093 495414) (QKo 144) = oem 18679093 18679922 19669920 := by
  decide +kernel

/-- Segment 23, part 9: every even n in [19669922, 20659920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_9 : oem 19669093 19669922 20659920 &&& gmo (opm 19669093 495414) (QKo 144) = oem 19669093 19669922 20659920 := by
  decide +kernel

/-- Segment 23, part 10: every even n in [20659922, 21649920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_10 : oem 20659093 20659922 21649920 &&& gmo (opm 20659093 495414) (QKo 144) = oem 20659093 20659922 21649920 := by
  decide +kernel

/-- Segment 23, part 11: every even n in [21649922, 22639920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_11 : oem 21649093 21649922 22639920 &&& gmo (opm 21649093 495414) (QKo 144) = oem 21649093 21649922 22639920 := by
  decide +kernel

end LeanLab.OeSHP2014
