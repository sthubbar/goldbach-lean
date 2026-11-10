import TernaryGoldbach.Ladder.Check
import LadderHints

/-! Negative control (not imported anywhere): the first rung's hint is lowered by one. Hints are the
least passing offset, so `t₀ − 1` fails the Proth test and the kernel must reject the chunk. -/

namespace TernaryGoldbach.Ladder.NegControl
open TernaryGoldbach.Ladder

#eval (ladder_hints% 1) &&& 2047
#eval ((ladder_hints% 4385435649) >>> (11 * 4095)) &&& 2047

theorem good : ChunkOK 1 := ⟨ladder_hints% 1, by decide +kernel⟩
theorem bad_first : ChunkOK 1 := ⟨ladder_hints% 1 - 1, by decide +kernel⟩
theorem bad_last : ChunkOK 4385435649 :=
  ⟨ladder_hints% 4385435649 - 2 ^ (11 * 4095), by decide +kernel⟩

end TernaryGoldbach.Ladder.NegControl
