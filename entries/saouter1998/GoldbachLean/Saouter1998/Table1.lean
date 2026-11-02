module

public import Mathlib
public import GoldbachLean.Saouter1998.Paper
public import GoldbachLean.Saouter1998.Theorem2

/-!
# Saouter 1998, Table 1

Table 1 of the paper, page 865: the first 100 rungs of Saouter's own ladder,
`N = 2^22 (10 k + 3) + 1`, are prime by the paper's own Theorem 2 test, one modular power per rung,
and each gap is at most `95360 * 2^22 < 4 * 10^11`.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.Table1

open GoldbachLean.Saouter1998 GoldbachLean.Saouter1998.Paper

/-- The 100 values of `k` in Table 1, page 865, as printed. -/
def T1 : List Nat := [3, 9537, 19059, 28575, 38107, 47622, 57147, 66651, 76182, 85713, 95230, 104764, 114297, 123819, 133347, 142879, 152415, 161950, 171471, 181003, 190501, 200022, 209541, 219066, 228594, 238104, 247624, 257157, 266683, 276219, 285727, 295258, 304785, 314305, 323839, 333355, 342882, 352405, 361941, 371467, 381000, 390522, 400048, 409575, 419098, 428604, 438132, 447663, 457194, 466710, 476242, 485761, 495291, 504813, 514347, 523878, 533397, 542932, 552466, 561991, 571519, 581038, 590565, 600090, 609625, 619159, 628675, 638196, 647704, 657232, 666751, 676285, 685821, 695353, 704887, 714405, 723936, 733452, 742983, 752485, 761989, 771520, 781054, 790588, 800116, 809623, 819151, 828679, 838198, 847726, 857232, 866748, 876268, 885804, 895333, 904851, 914377, 923910, 933445, 942973]

/-- Table 1 starts at the paper's first prime `138412033`. -/
theorem table1_head : (T1.map N).head? = some 138412033 := by decide +kernel

/-- Consecutive rungs rise by at most the nominal step `95360 * 2^22`. -/
theorem table1_steps :
    List.IsChain (fun a b => a < b ∧ b ≤ a + 95360 * 2 ^ 22) (T1.map N) := by decide +kernel

/-- Hence every gap is below Sinisalo's `4 * 10^11`, as the paper's method needs. -/
theorem table1_gaps :
    List.IsChain (fun a b => a < b ∧ b - a < 4 * 10 ^ 11) (T1.map N) := by
  refine List.IsChain.imp (fun a b h => ⟨h.1, ?_⟩) table1_steps
  have := nominal_step.1
  omega

/-- The printed formula at `k = 3` is composite, `127087333 = 19 * 6688807`. -/
theorem printed_three_composite : ¬ (Nprinted 3).Prime := by
  norm_num [Nprinted]

end GoldbachLean.Saouter1998.Table1

namespace GoldbachLean.Saouter1998.Table1Thm2

open GoldbachLean.Saouter1998.Paper GoldbachLean.Saouter1998.Thm2

/-- `R = 10 k + 3` for each Table 1 value `k`, with the square witness for `r^2 - 8 s`. -/
def W : List (ℕ × ℕ) := [(33, 0), (95373, 0), (190593, 0), (285753, 0), (381073, 0), (476223, 0), (571473, 0), (666513, 0), (761823, 0), (857133, 0), (952303, 0), (1047643, 0), (1142973, 0), (1238193, 0), (1333473, 0), (1428793, 0), (1524153, 0), (1619503, 0), (1714713, 0), (1810033, 0), (1905013, 0), (2000223, 0), (2095413, 0), (2190663, 0), (2285943, 0), (2381043, 0), (2476243, 0), (2571573, 0), (2666833, 0), (2762193, 0), (2857273, 0), (2952583, 0), (3047853, 0), (3143053, 0), (3238393, 0), (3333553, 0), (3428823, 0), (3524053, 0), (3619413, 0), (3714673, 0), (3810003, 0), (3905223, 0), (4000483, 0), (4095753, 0), (4190983, 0), (4286043, 0), (4381323, 0), (4476633, 0), (4571943, 0), (4667103, 0), (4762423, 0), (4857613, 0), (4952913, 0), (5048133, 0), (5143473, 0), (5238783, 0), (5333973, 0), (5429323, 0), (5524663, 0), (5619913, 0), (5715193, 0), (5810383, 0), (5905653, 0), (6000903, 0), (6096253, 0), (6191593, 0), (6286753, 0), (6381963, 0), (6477043, 0), (6572323, 0), (6667513, 0), (6762853, 0), (6858213, 0), (6953533, 0), (7048873, 0), (7144053, 0), (7239363, 0), (7334523, 0), (7429833, 0), (7524853, 0), (7619893, 0), (7715203, 0), (7810543, 0), (7905883, 0), (8001163, 0), (8096233, 0), (8191513, 0), (8286793, 0), (8381983, 0), (8477263, 88654), (8572323, 183714), (8667483, 278874), (8762683, 374074), (8858043, 469434), (8953333, 564724), (9048513, 659904), (9143773, 755164), (9239103, 850494), (9334453, 945844), (9429733, 1041124)]

theorem W_ok : W.all (fun x => thm2B x.1 x.2) = true := by decide +kernel

theorem W_match : W.map Prod.fst = GoldbachLean.Saouter1998.Table1.T1.map (fun k => 10 * k + 3) := by
  decide +kernel

/-- Every Table 1 rung is prime by Theorem 2. -/
theorem table1_prime_thm2 : ∀ k ∈ GoldbachLean.Saouter1998.Table1.T1, (N k).Prime := by
  intro k hk
  have hmem : 10 * k + 3 ∈ W.map Prod.fst := by
    rw [W_match]; exact List.mem_map_of_mem hk
  obtain ⟨x, hx, hx1⟩ := List.mem_map.mp hmem
  have h := prime_of_thm2B (List.all_eq_true.mp W_ok x hx)
  rw [N_form, ← hx1]
  exact h

end GoldbachLean.Saouter1998.Table1Thm2
