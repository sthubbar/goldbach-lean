module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 20 to 23, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 20, part 0: every even n in [1077422, 2067420] is x + y, x among the first 109 odd primes, y prime. -/
theorem chk_20_0 : oem 1076821 1077422 2067420 &&& gmo (opm 1076821 495300) (QKo 109) = oem 1076821 1077422 2067420 := by
  decide +kernel

/-- Segment 20, part 1: every even n in [2067422, 3057420] is x + y, x among the first 109 odd primes, y prime. -/
theorem chk_20_1 : oem 2066821 2067422 3057420 &&& gmo (opm 2066821 495300) (QKo 109) = oem 2066821 2067422 3057420 := by
  decide +kernel

/-- Segment 20, part 2: every even n in [3057422, 3526956] is x + y, x among the first 109 odd primes, y prime. -/
theorem chk_20_2 : oem 3056821 3057422 3526956 &&& gmo (opm 3056821 235068) (QKo 109) = oem 3056821 3057422 3526956 := by
  decide +kernel

/-- Segment 21, part 0: every even n in [3526958, 3807402] is x + y, x among the first 128 odd primes, y prime. -/
theorem chk_21_0 : oem 3526231 3526958 3807402 &&& gmo (opm 3526231 140586) (QKo 128) = oem 3526231 3526958 3807402 := by
  decide +kernel

end LeanLab.OeSHP2014
