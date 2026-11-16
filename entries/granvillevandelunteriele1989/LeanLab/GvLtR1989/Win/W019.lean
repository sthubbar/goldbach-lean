module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 76 to 79, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 45, part 1: every even n in [63370002, 64360000] is x + y, x among the first 166 odd primes, y prime. -/
theorem chk_45_1 : oem 63369011 63370002 64360000 &&& gmo (opm 63369011 495495) (QKo 166) = oem 63369011 63370002 64360000 := by
  decide +kernel

/-- Block 46, part 0: every even n in [64360002, 65350000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_46_0 : oem 64359179 64360002 65350000 &&& gmo (opm 64359179 495411) (QKo 142) = oem 64359179 64360002 65350000 := by
  decide +kernel

/-- Block 46, part 1: every even n in [65350002, 66340000] is x + y, x among the first 142 odd primes, y prime. -/
theorem chk_46_1 : oem 65349179 65350002 66340000 &&& gmo (opm 65349179 495411) (QKo 142) = oem 65349179 65350002 66340000 := by
  decide +kernel

/-- Block 47, part 0: every even n in [66340002, 67330000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_47_0 : oem 66339191 66340002 67330000 &&& gmo (opm 66339191 495405) (QKo 140) = oem 66339191 66340002 67330000 := by
  decide +kernel

end LeanLab.GvLtR1989
