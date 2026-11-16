module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 80 to 83, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 47, part 1: every even n in [67330002, 68320000] is x + y, x among the first 140 odd primes, y prime. -/
theorem chk_47_1 : oem 67329191 67330002 68320000 &&& gmo (opm 67329191 495405) (QKo 140) = oem 67329191 67330002 68320000 := by
  decide +kernel

/-- Block 48, part 0: every even n in [68320002, 69310000] is x + y, x among the first 161 odd primes, y prime. -/
theorem chk_48_0 : oem 68319049 68320002 69310000 &&& gmo (opm 68319049 495476) (QKo 161) = oem 68319049 68320002 69310000 := by
  decide +kernel

/-- Block 48, part 1: every even n in [69310002, 70300000] is x + y, x among the first 161 odd primes, y prime. -/
theorem chk_48_1 : oem 69309049 69310002 70300000 &&& gmo (opm 69309049 495476) (QKo 161) = oem 69309049 69310002 70300000 := by
  decide +kernel

/-- Block 49, part 0: every even n in [70300002, 71290000] is x + y, x among the first 165 odd primes, y prime. -/
theorem chk_49_0 : oem 70299019 70300002 71290000 &&& gmo (opm 70299019 495491) (QKo 165) = oem 70299019 70300002 71290000 := by
  decide +kernel

end LeanLab.GvLtR1989
