# Note on the sieve input of PALOMAR-2026-10-28-000016, version 2

Added 2026-11-05. The registered source at commit dda6b8b is unchanged; this note sits beside it and is not part of that version.

The Lean theorem `chenThreshold13375_of_deep_closed` takes the sieve input `LinearSieveT4 1/8349 112 114` at one fixed sifting level z, which is how Theorem 4 of Bordignon and Starichkova, Ramanujan J. 64, 2024, is printed.

The induction in the proof of that Theorem 4 passes to sifting level p below z, so the proof uses the condition at every level. The hypothesis as stated here is the printed fixed z form.

Whether this affects the threshold is an open question. No error in the paper is claimed. The Lean theorem stands as a theorem from its stated hypotheses, which remain explicit hypotheses and are not proved here.

See the Lean Lab preprint I-0088, version 1.8, Remark 1, Level of the sieve input. Lab reference F-0075.

AI wrote the Lean code. The binary Goldbach conjecture is still open, and nothing here claims to prove it.
