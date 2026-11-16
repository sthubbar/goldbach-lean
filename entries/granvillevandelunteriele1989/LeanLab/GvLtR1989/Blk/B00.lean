module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W000
public import LeanLab.GvLtR1989.Win.W001
public import LeanLab.GvLtR1989.Win.W002
public import LeanLab.GvLtR1989.Win.W003

/-!
Blocks 0 to 14, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_0 : GBBound 6 6 3 := by
  have hq : ∀ x ∈ QKo 1, x ≤ 3 := take_le 1 3 (by decide +kernel)
  have w0 : GBBound 6 6 3 :=
    gbBound_of_owcheck (lo := 3) (Wb := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_0_0
  exact w0

theorem lr_0 : (1 + 7917593/10000000 : ℝ) ≤ Real.log ((6 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((6 : ℕ) : ℝ)) 1 (f := (7917593/10000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_0 : (0 + 2915989/5000000 : ℝ) ≤ Real.log (1 + 7917593/10000000 : ℝ) := by
  have h := le_log_of (x := (1 + 7917593/10000000 : ℝ)) 0 (f := (2915989/5000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_0 : ∀ n, Even n → 6 ≤ n → n ≤ 6 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_0 ls_0 (by norm_num) (by norm_num) bnd_0

theorem bnd_1 : GBBound 8 8 3 := by
  have hq : ∀ x ∈ QKo 1, x ≤ 3 := take_le 1 3 (by decide +kernel)
  have w0 : GBBound 8 8 3 :=
    gbBound_of_owcheck (lo := 5) (Wb := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_1_0
  exact w0

theorem lr_1 : (2 + 993/12500 : ℝ) ≤ Real.log ((8 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((8 : ℕ) : ℝ)) 2 (f := (993/12500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_1 : (0 + 732097/1000000 : ℝ) ≤ Real.log (2 + 993/12500 : ℝ) := by
  have h := le_log_of (x := (2 + 993/12500 : ℝ)) 0 (f := (732097/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_1 : ∀ n, Even n → 8 ≤ n → n ≤ 8 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_1 ls_1 (by norm_num) (by norm_num) bnd_1

theorem bnd_2 : GBBound 10 28 5 := by
  have hq : ∀ x ∈ QKo 2, x ≤ 5 := take_le 2 5 (by decide +kernel)
  have w0 : GBBound 10 28 5 :=
    gbBound_of_owcheck (lo := 5) (Wb := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_2_0
  exact w0

theorem lr_2 : (2 + 37823/125000 : ℝ) ≤ Real.log ((10 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((10 : ℕ) : ℝ)) 2 (f := (37823/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_2 : (0 + 83403/100000 : ℝ) ≤ Real.log (2 + 37823/125000 : ℝ) := by
  have h := le_log_of (x := (2 + 37823/125000 : ℝ)) 0 (f := (83403/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_2 : ∀ n, Even n → 10 ≤ n → n ≤ 28 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_2 ls_2 (by norm_num) (by norm_num) bnd_2

theorem bnd_3 : GBBound 30 96 7 := by
  have hq : ∀ x ∈ QKo 3, x ≤ 7 := take_le 3 7 (by decide +kernel)
  have w0 : GBBound 30 96 7 :=
    gbBound_of_owcheck (lo := 23) (Wb := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_3_0
  exact w0

theorem lr_3 : (3 + 100299/250000 : ℝ) ≤ Real.log ((30 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((30 : ℕ) : ℝ)) 3 (f := (100299/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_3 : (1 + 112063/500000 : ℝ) ≤ Real.log (3 + 100299/250000 : ℝ) := by
  have h := le_log_of (x := (3 + 100299/250000 : ℝ)) 1 (f := (112063/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_3 : ∀ n, Even n → 30 ≤ n → n ≤ 96 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_3 ls_3 (by norm_num) (by norm_num) bnd_3

theorem bnd_4 : GBBound 98 552 31 := by
  have hq : ∀ x ∈ QKo 10, x ≤ 31 := take_le 10 31 (by decide +kernel)
  have w0 : GBBound 98 552 31 :=
    gbBound_of_owcheck (lo := 67) (Wb := 243) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_4_0
  exact w0

theorem lr_4 : (4 + 292483/500000 : ℝ) ≤ Real.log ((98 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((98 : ℕ) : ℝ)) 4 (f := (292483/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_4 : (1 + 522781/1000000 : ℝ) ≤ Real.log (4 + 292483/500000 : ℝ) := by
  have h := le_log_of (x := (4 + 292483/500000 : ℝ)) 1 (f := (522781/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_4 : ∀ n, Even n → 98 ≤ n → n ≤ 552 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_4 ls_4 (by norm_num) (by norm_num) bnd_4

theorem bnd_5 : GBBound 554 2638 73 := by
  have hq : ∀ x ∈ QKo 20, x ≤ 73 := take_le 20 73 (by decide +kernel)
  have w0 : GBBound 554 2638 73 :=
    gbBound_of_owcheck (lo := 481) (Wb := 1079) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_5_0
  exact w0

theorem lr_5 : (6 + 317163/1000000 : ℝ) ≤ Real.log ((554 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((554 : ℕ) : ℝ)) 6 (f := (317163/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_5 : (1 + 843269/1000000 : ℝ) ≤ Real.log (6 + 317163/1000000 : ℝ) := by
  have h := le_log_of (x := (6 + 317163/1000000 : ℝ)) 1 (f := (843269/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_5 : ∀ n, Even n → 554 ≤ n → n ≤ 2638 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_5 ls_5 (by norm_num) (by norm_num) bnd_5

theorem bnd_6 : GBBound 2640 7424 139 := by
  have hq : ∀ x ∈ QKo 33, x ≤ 139 := take_le 33 139 (by decide +kernel)
  have w0 : GBBound 2640 7424 139 :=
    gbBound_of_owcheck (lo := 2501) (Wb := 2462) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_6_0
  exact w0

theorem lr_6 : (7 + 878533/1000000 : ℝ) ≤ Real.log ((2640 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((2640 : ℕ) : ℝ)) 7 (f := (878533/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_6 : (2 + 3207/50000 : ℝ) ≤ Real.log (7 + 878533/1000000 : ℝ) := by
  have h := le_log_of (x := (7 + 878533/1000000 : ℝ)) 2 (f := (3207/50000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_6 : ∀ n, Even n → 2640 ≤ n → n ≤ 7424 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_6 ls_6 (by norm_num) (by norm_num) bnd_6

theorem bnd_7 : GBBound 7426 54242 211 := by
  have hq : ∀ x ∈ QKo 46, x ≤ 211 := take_le 46 211 (by decide +kernel)
  have w0 : GBBound 7426 54242 211 :=
    gbBound_of_owcheck (lo := 7215) (Wb := 23514) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_7_0
  exact w0

theorem lr_7 : (8 + 912741/1000000 : ℝ) ≤ Real.log ((7426 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((7426 : ℕ) : ℝ)) 8 (f := (912741/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_7 : (2 + 4687/25000 : ℝ) ≤ Real.log (8 + 912741/1000000 : ℝ) := by
  have h := le_log_of (x := (8 + 912741/1000000 : ℝ)) 2 (f := (4687/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_7 : ∀ n, Even n → 7426 ≤ n → n ≤ 54242 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_7 ls_7 (by norm_num) (by norm_num) bnd_7

theorem bnd_8 : GBBound 54244 194426 331 := by
  have hq : ∀ x ∈ QKo 66, x ≤ 331 := take_le 66 331 (by decide +kernel)
  have w0 : GBBound 54244 194426 331 :=
    gbBound_of_owcheck (lo := 53913) (Wb := 70257) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_8_0
  exact w0

theorem lr_8 : (10 + 450623/500000 : ℝ) ≤ Real.log ((54244 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((54244 : ℕ) : ℝ)) 10 (f := (450623/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_8 : (2 + 97219/250000 : ℝ) ≤ Real.log (10 + 450623/500000 : ℝ) := by
  have h := le_log_of (x := (10 + 450623/500000 : ℝ)) 2 (f := (97219/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_8 : ∀ n, Even n → 54244 ≤ n → n ≤ 194426 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_8 ls_8 (by norm_num) (by norm_num) bnd_8

theorem bnd_9 : GBBound 194428 503218 389 := by
  have hq : ∀ x ∈ QKo 76, x ≤ 389 := take_le 76 389 (by decide +kernel)
  have w0 : GBBound 194428 503218 389 :=
    gbBound_of_owcheck (lo := 194039) (Wb := 154590) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_9_0
  exact w0

theorem lr_9 : (12 + 22227/125000 : ℝ) ≤ Real.log ((194428 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((194428 : ℕ) : ℝ)) 12 (f := (22227/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_9 : (2 + 249807/500000 : ℝ) ≤ Real.log (12 + 22227/125000 : ℝ) := by
  have h := le_log_of (x := (12 + 22227/125000 : ℝ)) 2 (f := (249807/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_9 : ∀ n, Even n → 194428 ≤ n → n ≤ 503218 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_9 ls_9 (by norm_num) (by norm_num) bnd_9

theorem bnd_10 : GBBound 503220 999998 523 := by
  have hq : ∀ x ∈ QKo 98, x ≤ 523 := take_le 98 523 (by decide +kernel)
  have w0 : GBBound 503220 999998 523 :=
    gbBound_of_owcheck (lo := 502697) (Wb := 248651) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_10_0
  exact w0

theorem lr_10 : (13 + 128781/1000000 : ℝ) ≤ Real.log ((503220 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((503220 : ℕ) : ℝ)) 13 (f := (128781/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_10 : (2 + 114961/200000 : ℝ) ≤ Real.log (13 + 128781/1000000 : ℝ) := by
  have h := le_log_of (x := (13 + 128781/1000000 : ℝ)) 2 (f := (114961/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_10 : ∀ n, Even n → 503220 ≤ n → n ≤ 999998 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_10 ls_10 (by norm_num) (by norm_num) bnd_10

theorem bnd_11 : GBBound 1000000 1000000 17 := by
  have hq : ∀ x ∈ QKo 6, x ≤ 17 := take_le 6 17 (by decide +kernel)
  have w0 : GBBound 1000000 1000000 17 :=
    gbBound_of_owcheck (lo := 999983) (Wb := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_11_0
  exact w0

theorem lr_11 : (13 + 815509/1000000 : ℝ) ≤ Real.log ((1000000 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((1000000 : ℕ) : ℝ)) 13 (f := (815509/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_11 : (2 + 62579/100000 : ℝ) ≤ Real.log (13 + 815509/1000000 : ℝ) := by
  have h := le_log_of (x := (13 + 815509/1000000 : ℝ)) 2 (f := (62579/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_11 : ∀ n, Even n → 1000000 ≤ n → n ≤ 1000000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_11 ls_11 (by norm_num) (by norm_num) bnd_11

theorem bnd_12 : GBBound 1000002 2980000 601 := by
  have hq : ∀ x ∈ QKo 109, x ≤ 601 := take_le 109 601 (by decide +kernel)
  have w0 : GBBound 1000002 1990000 601 :=
    gbBound_of_owcheck (lo := 999401) (Wb := 495300) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_12_0
  have w1 : GBBound 1990002 2980000 601 :=
    gbBound_of_owcheck (lo := 1989401) (Wb := 495300) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_12_1
  have v1 : GBBound 1000002 2980000 601 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_12 : (13 + 815511/1000000 : ℝ) ≤ Real.log ((1000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((1000002 : ℕ) : ℝ)) 13 (f := (815511/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_12 : (2 + 62579/100000 : ℝ) ≤ Real.log (13 + 815511/1000000 : ℝ) := by
  have h := le_log_of (x := (13 + 815511/1000000 : ℝ)) 2 (f := (62579/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_12 : ∀ n, Even n → 1000002 ≤ n → n ≤ 2980000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_12 ls_12 (by norm_num) (by norm_num) bnd_12

theorem bnd_13 : GBBound 2980002 3475000 523 := by
  have hq : ∀ x ∈ QKo 98, x ≤ 523 := take_le 98 523 (by decide +kernel)
  have w0 : GBBound 2980002 3475000 523 :=
    gbBound_of_owcheck (lo := 2979479) (Wb := 247761) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_13_0
  exact w0

theorem lr_13 : (14 + 907433/1000000 : ℝ) ≤ Real.log ((2980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((2980002 : ℕ) : ℝ)) 14 (f := (907433/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_13 : (2 + 350929/500000 : ℝ) ≤ Real.log (14 + 907433/1000000 : ℝ) := by
  have h := le_log_of (x := (14 + 907433/1000000 : ℝ)) 2 (f := (350929/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_13 : ∀ n, Even n → 2980002 ≤ n → n ≤ 3475000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_13 ls_13 (by norm_num) (by norm_num) bnd_13

theorem bnd_14 : GBBound 3475002 3970000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 3475002 3970000 751 :=
    gbBound_of_owcheck (lo := 3474251) (Wb := 247875) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_14_0
  exact w0

theorem lr_14 : (15 + 3819/62500 : ℝ) ≤ Real.log ((3475002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((3475002 : ℕ) : ℝ)) 15 (f := (3819/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_14 : (2 + 356057/500000 : ℝ) ≤ Real.log (15 + 3819/62500 : ℝ) := by
  have h := le_log_of (x := (15 + 3819/62500 : ℝ)) 2 (f := (356057/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_14 : ∀ n, Even n → 3475002 ≤ n → n ≤ 3970000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_14 ls_14 (by norm_num) (by norm_num) bnd_14

end LeanLab.GvLtR1989
