module

public import LeanLab.OeSHP2014.Core

/-!
Window checks 36 to 39, generated. Each theorem is one equality of natural numbers
checked by the kernel; see `Core.lean`.
-/

@[expose] public section

set_option Elab.async false

namespace LeanLab.OeSHP2014

/-- Segment 23, part 4: every even n in [14719922, 15709920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_4 : oem 14719093 14719922 15709920 &&& gmo (opm 14719093 495414) (QKo 144) = oem 14719093 14719922 15709920 := by
  decide +kernel

/-- Segment 23, part 5: every even n in [15709922, 16699920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_5 : oem 15709093 15709922 16699920 &&& gmo (opm 15709093 495414) (QKo 144) = oem 15709093 15709922 16699920 := by
  decide +kernel

/-- Segment 23, part 6: every even n in [16699922, 17689920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_6 : oem 16699093 16699922 17689920 &&& gmo (opm 16699093 495414) (QKo 144) = oem 16699093 16699922 17689920 := by
  decide +kernel

/-- Segment 23, part 7: every even n in [17689922, 18679920] is x + y, x among the first 144 odd primes, y prime. -/
theorem chk_23_7 : oem 17689093 17689922 18679920 &&& gmo (opm 17689093 495414) (QKo 144) = oem 17689093 17689922 18679920 := by
  decide +kernel

end LeanLab.OeSHP2014
