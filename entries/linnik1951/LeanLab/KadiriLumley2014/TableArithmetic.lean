module

public import LeanLab.KadiriLumley2014.Ladder

/-!
Kadiri and Lumley 2014, Table 2, arXiv 1407.7902v1 page 13, journal A61 page 17.
Every row is transcribed. Arithmetic does not certify the cited analytic theorem.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- A zero log index denotes the special threshold 4 times 10^18.
Delta is stored in units of 10^-12, sigma in hundredths, a in ten thousandths. -/
structure PrintedRow where
  logIndex : ℕ
  m : ℕ
  deltaUnits : ℕ
  height : ℕ
  sigmaUnits : ℕ
  aUnits : ℕ
  gapDenom : ℕ
  deriving DecidableEq, Repr

/-- All twenty Table 2 rows, including the initial and final rows. -/
def tableTwo : List PrintedRow := [
  ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩,
  ⟨43, 5, 33490, 291316980, 92, 2147, 38753947⟩,
  ⟨44, 6, 23300, 488509984, 92, 2324, 61162616⟩,
  ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩,
  ⟨46, 8, 11340, 1284120197, 92, 2651, 148306019⟩,
  ⟨47, 9, 8080, 1996029891, 92, 2836, 227619375⟩,
  ⟨48, 11, 6000, 3204848430, 93, 3050, 346582570⟩,
  ⟨49, 15, 4682, 5415123831, 93, 3275, 518958776⟩,
  ⟨50, 20, 3889, 8466793105, 93, 3543, 753575355⟩,
  ⟨51, 28, 3625, 12399463961, 93, 3849, 1037917449⟩,
  ⟨52, 39, 3803, 16139006408, 93, 4127, 1313524036⟩,
  ⟨53, 48, 4088, 18290358817, 93, 4301, 1524171138⟩,
  ⟨54, 54, 4311, 19412056863, 93, 4398, 1670398039⟩,
  ⟨55, 56, 4386, 19757119193, 93, 4445, 1770251249⟩,
  ⟨56, 59, 4508, 20210075547, 93, 4481, 1838818070⟩,
  ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩,
  ⟨58, 61, 4590, 20495459359, 93, 4514, 1920768795⟩,
  ⟨59, 61, 4589, 20499925573, 93, 4522, 1946282821⟩,
  ⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩,
  ⟨150, 64, 4685, 21029543983, 96, 4641, 2442159714⟩]

/-- Threshold associated to a printed row. -/
noncomputable def PrintedRow.threshold (r : PrintedRow) : ℝ :=
  if r.logIndex = 0 then evenBase else Real.exp r.logIndex

/-- The cited Theorem 1.1 for all printed rows. This is an input, not a theorem. -/
def TableTwoIntervals : Prop :=
  ∀ r ∈ tableTwo, KLRow r.threshold r.gapDenom

/-- Count and ordering of the printed data. -/
theorem tableTwo_shape : tableTwo.length = 20 ∧
    (tableTwo.map PrintedRow.logIndex).Pairwise (· < ·) ∧
    (tableTwo.map PrintedRow.gapDenom).Pairwise (· < ·) := by
  decide +kernel

/-- All printed parameters satisfy the elementary size conditions in 2.1,
with u = delta / m. The zero density and interval inputs are not proved here. -/
theorem tableTwo_parameters : ∀ r ∈ tableTwo,
    2 ≤ r.m ∧ 0 < r.deltaUnits ∧ r.deltaUnits ≤ 100000000 ∧
    r.aUnits ≤ 5000 ∧ 50 < r.sigmaUnits ∧ r.sigmaUnits < 100 ∧
    1132491 < r.height ∧ r.height < 30610000000 ∧ 2 ≤ r.gapDenom := by
  decide +kernel

/-- Uniform bounds on the printed denominators, with the exceptional last row isolated. -/
theorem tableTwo_denominators : ∀ r ∈ tableTwo,
    36082898 ≤ r.gapDenom ∧ r.gapDenom ≤ 2442159714 ∧
    (r.logIndex ≤ 60 ∧ r.gapDenom ≤ 1966196911 ∨
      r.logIndex = 150 ∧ r.gapDenom = 2442159714) := by
  decide +kernel

/-- Every printed product with the even base is below the rounded odd verification. -/
theorem tableTwo_reach_lt_oddBase : ∀ r ∈ tableTwo,
    r.gapDenom * evenBase < oddBase := by
  decide +kernel

/-- The printed row 60 occurs in the table. -/
theorem row60_mem :
    (⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩ : PrintedRow) ∈ tableTwo := by
  decide +kernel

/-- The printed row 150 occurs in the table. -/
theorem row150_mem :
    (⟨150, 64, 4685, 21029543983, 96, 4641, 2442159714⟩ : PrintedRow) ∈ tableTwo := by
  decide +kernel

end LeanLab.KadiriLumley2014.Task64
