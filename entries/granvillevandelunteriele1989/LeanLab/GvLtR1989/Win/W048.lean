module

public import LeanLab.GvLtR1989.Core

/-!
Window checks 192 to 195, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.GvLtR1989

/-- Block 103, part 1: every even n in [178210002, 179200000] is x + y, x among the first 180 odd primes, y prime. -/
theorem chk_103_1 : oem 178208915 178210002 179200000 &&& gmo (opm 178208915 495543) (QKo 180) = oem 178208915 178210002 179200000 := by
  decide +kernel

/-- Block 104, part 0: every even n in [179200002, 180190000] is x + y, x among the first 190 odd primes, y prime. -/
theorem chk_104_0 : oem 179198849 179200002 180190000 &&& gmo (opm 179198849 495576) (QKo 190) = oem 179198849 179200002 180190000 := by
  decide +kernel

/-- Block 104, part 1: every even n in [180190002, 181180000] is x + y, x among the first 190 odd primes, y prime. -/
theorem chk_104_1 : oem 180188849 180190002 181180000 &&& gmo (opm 180188849 495576) (QKo 190) = oem 180188849 180190002 181180000 := by
  decide +kernel

/-- Block 105, part 0: every even n in [181180002, 182170000] is x + y, x among the first 154 odd primes, y prime. -/
theorem chk_105_0 : oem 181179095 181180002 182170000 &&& gmo (opm 181179095 495453) (QKo 154) = oem 181179095 181180002 182170000 := by
  decide +kernel

end LeanLab.GvLtR1989
