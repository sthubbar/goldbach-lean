module

public import LeanLab.PNTPort.BV.Assembly
public import LeanLab.PNTPort.BV.LargeConductorProof

/-!
# Bombieri-Vinogradov from Siegel-Walfisz

Lab proof, unit U-5000. AI wrote this file. Known mathematics, Bombieri 1965 and
A. I. Vinogradov 1965. The result is CONDITIONAL ON `HeathBrown1985.SiegelWalfisz`, the lab's
statement of the Siegel-Walfisz theorem for moduli above 1, which no source in the lab proves.
The large sieve, Vaughan's identity, Polya-Vinogradov and the large conductor estimate are all
proved in this lab; the prime number theorem with error term is the StrongPNT port.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

/-- **Bombieri-Vinogradov**, CONDITIONAL ON Siegel-Walfisz. -/
theorem bombieriVinogradov_of_siegelWalfisz (hSW : HeathBrown1985.SiegelWalfisz) :
    BombieriVinogradov :=
  bombieriVinogradov_of hSW largeConductor

end LeanLab.PNTPort.BV
