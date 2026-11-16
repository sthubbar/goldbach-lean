module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 44 to 47, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 23, part 12: every even n in [22639922, 23629920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_12 : oem 22639093 22639922 23629920 &&& gmo (opm 22639093 495414) (QKo 144) = oem 22639093 22639922 23629920 := by
  decide +kernel

/-- Segment 23, part 13: every even n in [23629922, 24106880] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_13 : oem 23629093 23629922 24106880 &&& gmo (opm 23629093 238894) (QKo 144) = oem 23629093 23629922 24106880 := by
  decide +kernel

/-- Segment 24, part 0: every even n in [24106882, 25096880] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_24_0 : oem 24105953 24106882 25096880 &&& gmo (opm 24105953 495464) (QKo 157) = oem 24105953 24106882 25096880 := by
  decide +kernel

/-- Segment 24, part 1: every even n in [25096882, 26086880] is x + y, x among the first 157 odd primes, y prime. -/
theorem chk_24_1 : oem 25095953 25096882 26086880 &&& gmo (opm 25095953 495464) (QKo 157) = oem 25095953 25096882 26086880 := by
  decide +kernel

end LeanLab.OeSHP2014
