module

public import LeanLab.Schnirelmann.Mann

/-!
# Proof of the Mann 1942 entry

`LeanLab/Schnirelmann/Mann.lean` proves Mann's theorem `σ(A + B) ≥ min(1, σ(A) + σ(B))` for
Mathlib's `schnirelmannDensity`, and its form for finitely many sets, from the rank `h` case of
Dyson's theorem with a real `δ ≤ 1`, following M. B. Nathanson, arXiv:2407.12253, Sections 3 to 5.
The Dyson transform lemmas are those of `LeanLab/Ramare1995/Theorem91.lean`. AI wrote the Lean
code, Claude, Anthropic; it was checked by the Lean kernel.
-/
