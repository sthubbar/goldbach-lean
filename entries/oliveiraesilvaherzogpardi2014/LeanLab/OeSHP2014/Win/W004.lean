module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 16 to 19, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 16, part 0: every even n in [194428, 194468] is x + y, x among the first 71 odd primes, y prime. -/
theorem chk_16_0 : oem 194069 194428 194468 &&& gmo (opm 194069 200) (QKo 71) = oem 194069 194428 194468 := by
  decide +kernel

/-- Segment 17, part 0: every even n in [194470, 413570] is x + y, x among the first 75 odd primes, y prime. -/
theorem chk_17_0 : oem 194087 194470 413570 &&& gmo (opm 194087 109742) (QKo 75) = oem 194087 194470 413570 := by
  decide +kernel

/-- Segment 18, part 0: every even n in [413572, 503220] is x + y, x among the first 76 odd primes, y prime. -/
theorem chk_18_0 : oem 413183 413572 503220 &&& gmo (opm 413183 45019) (QKo 76) = oem 413183 413572 503220 := by
  decide +kernel

/-- Segment 19, part 0: every even n in [503222, 1077420] is x + y, x among the first 98 odd primes, y prime. -/
theorem chk_19_0 : oem 502699 503222 1077420 &&& gmo (opm 502699 287361) (QKo 98) = oem 502699 503222 1077420 := by
  decide +kernel

end LeanLab.OeSHP2014
