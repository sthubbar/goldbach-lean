module

public import LeanLab.BS2022GRH.Cert1567
public import LeanLab.BS2022GRH.Cert1575

/-!
BS2022GRH, P0021, idea I-0088, unit U-1575, PC run 20261027T0807Z-9485: the GRH Chen threshold
with the numeric leaf `Eps1500` closed by `Cert1575.eps1500_proved`.

`chenThreshold13375_of_deep_closed`: `ChenThreshold13375`, CONDITIONAL ON `Thm5J`, `Thm6J`,
`Thm7J` and `LinearSieveT4 (1/8349) 112 114` only; `Bracket13375` and `Eps1500` are PROVED.

AI-written Lean code, Claude, unit U-1575. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Cert1575
open LeanLab.BS2022GRH.ChenThresholdGRH

/-- **`Eps1500`, PROVED**, the copy in `Cert1575` unfolds to the sealed statement. -/
theorem eps1500 : Eps1500 := eps1500_proved

/-- **The GRH Chen threshold at exp(exp 13.375), CONDITIONAL** ON the cited Theorems 5, 6, 7 of
P0021 and the cited linear sieve Theorem 4 at ε = 1/8349, C₁ = 112, C₂ = 114. -/
theorem chenThreshold13375_of_deep_closed (h5 : Thm5J) (h6 : Thm6J) (h7 : Thm7J)
    (hT4 : LinearSieveT4 (1 / 8349) 112 114) : ChenThreshold13375 :=
  Cert1567.chenThreshold13375_of_deep h5 h6 h7 hT4 eps1500

end LeanLab.BS2022GRH.Cert1575

