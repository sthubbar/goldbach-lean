module

public import LeanLab.ChirreHagen2025.U6759DiagSpS7

/-!
U-1381 PC 20261021T0903Z-24128: re-export of the seven-way split U6759DiagSpS1 to U6759DiagSpS7 of
U6759Diag.lean, rewired onto U6743DiagSplit in place of U6743Diag. The lemma text of the seven parts
concatenates byte for byte to the body of U6759Diag.lean, same namespace LeanLab.ChirreHagen2025.U6759
and same declaration names, so importing this module provides exactly the declarations of U6759Diag,
including diag_u6759 and u6759_c668. Split because the unsplit 22558-line module cannot be elaborated
within the memory of this box. AI-written.
-/

@[expose] public section

