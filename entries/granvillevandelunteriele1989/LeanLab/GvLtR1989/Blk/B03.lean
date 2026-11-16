module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W018
public import LeanLab.GvLtR1989.Win.W019
public import LeanLab.GvLtR1989.Win.W020
public import LeanLab.GvLtR1989.Win.W021
public import LeanLab.GvLtR1989.Win.W022
public import LeanLab.GvLtR1989.Win.W023
public import LeanLab.GvLtR1989.Win.W024
public import LeanLab.GvLtR1989.Win.W025
public import LeanLab.GvLtR1989.Win.W026

/-!
Blocks 45 to 59, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_45 : GBBound 62380002 64360000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 62380002 63370000 991 :=
    gbBound_of_owcheck (lo := 62379011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_45_0
  have w1 : GBBound 63370002 64360000 991 :=
    gbBound_of_owcheck (lo := 63369011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_45_1
  have v1 : GBBound 62380002 64360000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_45 : (17 + 474377/500000 : ℝ) ≤ Real.log ((62380002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((62380002 : ℕ) : ℝ)) 17 (f := (474377/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_45 : (2 + 887519/1000000 : ℝ) ≤ Real.log (17 + 474377/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 474377/500000 : ℝ)) 2 (f := (887519/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_45 : ∀ n, Even n → 62380002 ≤ n → n ≤ 64360000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_45 ls_45 (by norm_num) (by norm_num) bnd_45

theorem bnd_46 : GBBound 64360002 66340000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 64360002 65350000 823 :=
    gbBound_of_owcheck (lo := 64359179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_46_0
  have w1 : GBBound 65350002 66340000 823 :=
    gbBound_of_owcheck (lo := 65349179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_46_1
  have v1 : GBBound 64360002 66340000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_46 : (17 + 980001/1000000 : ℝ) ≤ Real.log ((64360002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((64360002 : ℕ) : ℝ)) 17 (f := (980001/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_46 : (2 + 889259/1000000 : ℝ) ≤ Real.log (17 + 980001/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 980001/1000000 : ℝ)) 2 (f := (889259/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_46 : ∀ n, Even n → 64360002 ≤ n → n ≤ 66340000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_46 ls_46 (by norm_num) (by norm_num) bnd_46

theorem bnd_47 : GBBound 66340002 68320000 811 := by
  have hq : ∀ x ∈ QKo 140, x ≤ 811 := take_le 140 811 (by decide +kernel)
  have w0 : GBBound 66340002 67330000 811 :=
    gbBound_of_owcheck (lo := 66339191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_47_0
  have w1 : GBBound 67330002 68320000 811 :=
    gbBound_of_owcheck (lo := 67329191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_47_1
  have v1 : GBBound 66340002 68320000 811 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_47 : (18 + 5151/500000 : ℝ) ≤ Real.log ((66340002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((66340002 : ℕ) : ℝ)) 18 (f := (5151/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_47 : (2 + 445471/500000 : ℝ) ≤ Real.log (18 + 5151/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 5151/500000 : ℝ)) 2 (f := (445471/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_47 : ∀ n, Even n → 66340002 ≤ n → n ≤ 68320000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_47 ls_47 (by norm_num) (by norm_num) bnd_47

theorem bnd_48 : GBBound 68320002 70300000 953 := by
  have hq : ∀ x ∈ QKo 161, x ≤ 953 := take_le 161 953 (by decide +kernel)
  have w0 : GBBound 68320002 69310000 953 :=
    gbBound_of_owcheck (lo := 68319049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_48_0
  have w1 : GBBound 69310002 70300000 953 :=
    gbBound_of_owcheck (lo := 69309049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_48_1
  have v1 : GBBound 68320002 70300000 953 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_48 : (18 + 1241/31250 : ℝ) ≤ Real.log ((68320002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((68320002 : ℕ) : ℝ)) 18 (f := (1241/31250 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_48 : (2 + 446287/500000 : ℝ) ≤ Real.log (18 + 1241/31250 : ℝ) := by
  have h := le_log_of (x := (18 + 1241/31250 : ℝ)) 2 (f := (446287/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_48 : ∀ n, Even n → 68320002 ≤ n → n ≤ 70300000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_48 ls_48 (by norm_num) (by norm_num) bnd_48

theorem bnd_49 : GBBound 70300002 72280000 983 := by
  have hq : ∀ x ∈ QKo 165, x ≤ 983 := take_le 165 983 (by decide +kernel)
  have w0 : GBBound 70300002 71290000 983 :=
    gbBound_of_owcheck (lo := 70299019) (Wb := 495491) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_49_0
  have w1 : GBBound 71290002 72280000 983 :=
    gbBound_of_owcheck (lo := 71289019) (Wb := 495491) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_49_1
  have v1 : GBBound 70300002 72280000 983 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_49 : (18 + 68281/1000000 : ℝ) ≤ Real.log ((70300002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((70300002 : ℕ) : ℝ)) 18 (f := (68281/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_49 : (2 + 223539/250000 : ℝ) ≤ Real.log (18 + 68281/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 68281/1000000 : ℝ)) 2 (f := (223539/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_49 : ∀ n, Even n → 70300002 ≤ n → n ≤ 72280000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_49 ls_49 (by norm_num) (by norm_num) bnd_49

theorem bnd_50 : GBBound 72280002 74260000 937 := by
  have hq : ∀ x ∈ QKo 158, x ≤ 937 := take_le 158 937 (by decide +kernel)
  have w0 : GBBound 72280002 73270000 937 :=
    gbBound_of_owcheck (lo := 72279065) (Wb := 495468) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_50_0
  have w1 : GBBound 73270002 74260000 937 :=
    gbBound_of_owcheck (lo := 73269065) (Wb := 495468) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_50_1
  have v1 : GBBound 72280002 74260000 937 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_50 : (18 + 96057/1000000 : ℝ) ≤ Real.log ((72280002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((72280002 : ℕ) : ℝ)) 18 (f := (96057/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_50 : (2 + 895693/1000000 : ℝ) ≤ Real.log (18 + 96057/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 96057/1000000 : ℝ)) 2 (f := (895693/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_50 : ∀ n, Even n → 72280002 ≤ n → n ≤ 74260000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_50 ls_50 (by norm_num) (by norm_num) bnd_50

theorem bnd_51 : GBBound 74260002 76240000 883 := by
  have hq : ∀ x ∈ QKo 152, x ≤ 883 := take_le 152 883 (by decide +kernel)
  have w0 : GBBound 74260002 75250000 883 :=
    gbBound_of_owcheck (lo := 74259119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_51_0
  have w1 : GBBound 75250002 76240000 883 :=
    gbBound_of_owcheck (lo := 75249119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_51_1
  have v1 : GBBound 74260002 76240000 883 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_51 : (18 + 61541/500000 : ℝ) ≤ Real.log ((74260002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((74260002 : ℕ) : ℝ)) 18 (f := (61541/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_51 : (2 + 179437/200000 : ℝ) ≤ Real.log (18 + 61541/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 61541/500000 : ℝ)) 2 (f := (179437/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_51 : ∀ n, Even n → 74260002 ≤ n → n ≤ 76240000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_51 ls_51 (by norm_num) (by norm_num) bnd_51

theorem bnd_52 : GBBound 76240002 78220000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 76240002 77230000 751 :=
    gbBound_of_owcheck (lo := 76239251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_52_0
  have w1 : GBBound 77230002 78220000 751 :=
    gbBound_of_owcheck (lo := 77229251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_52_1
  have v1 : GBBound 76240002 78220000 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_52 : (18 + 29879/200000 : ℝ) ≤ Real.log ((76240002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((76240002 : ℕ) : ℝ)) 18 (f := (29879/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_52 : (2 + 224659/250000 : ℝ) ≤ Real.log (18 + 29879/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 29879/200000 : ℝ)) 2 (f := (224659/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_52 : ∀ n, Even n → 76240002 ≤ n → n ≤ 78220000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_52 ls_52 (by norm_num) (by norm_num) bnd_52

theorem bnd_53 : GBBound 78220002 80200000 1009 := by
  have hq : ∀ x ∈ QKo 168, x ≤ 1009 := take_le 168 1009 (by decide +kernel)
  have w0 : GBBound 78220002 79210000 1009 :=
    gbBound_of_owcheck (lo := 78218993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_53_0
  have w1 : GBBound 79210002 80200000 1009 :=
    gbBound_of_owcheck (lo := 79208993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_53_1
  have v1 : GBBound 78220002 80200000 1009 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_53 : (18 + 87517/500000 : ℝ) ≤ Real.log ((78220002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((78220002 : ℕ) : ℝ)) 18 (f := (87517/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_53 : (2 + 900047/1000000 : ℝ) ≤ Real.log (18 + 87517/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 87517/500000 : ℝ)) 2 (f := (900047/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_53 : ∀ n, Even n → 78220002 ≤ n → n ≤ 80200000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_53 ls_53 (by norm_num) (by norm_num) bnd_53

theorem bnd_54 : GBBound 80200002 82180000 739 := by
  have hq : ∀ x ∈ QKo 130, x ≤ 739 := take_le 130 739 (by decide +kernel)
  have w0 : GBBound 80200002 81190000 739 :=
    gbBound_of_owcheck (lo := 80199263) (Wb := 495369) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_54_0
  have w1 : GBBound 81190002 82180000 739 :=
    gbBound_of_owcheck (lo := 81189263) (Wb := 495369) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_54_1
  have v1 : GBBound 80200002 82180000 739 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_54 : (18 + 200033/1000000 : ℝ) ≤ Real.log ((80200002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((80200002 : ℕ) : ℝ)) 18 (f := (200033/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_54 : (2 + 450711/500000 : ℝ) ≤ Real.log (18 + 200033/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 200033/1000000 : ℝ)) 2 (f := (450711/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_54 : ∀ n, Even n → 80200002 ≤ n → n ≤ 82180000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_54 ls_54 (by norm_num) (by norm_num) bnd_54

theorem bnd_55 : GBBound 82180002 84160000 811 := by
  have hq : ∀ x ∈ QKo 140, x ≤ 811 := take_le 140 811 (by decide +kernel)
  have w0 : GBBound 82180002 83170000 811 :=
    gbBound_of_owcheck (lo := 82179191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_55_0
  have w1 : GBBound 83170002 84160000 811 :=
    gbBound_of_owcheck (lo := 83169191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_55_1
  have v1 : GBBound 82180002 84160000 811 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_55 : (18 + 224421/1000000 : ℝ) ≤ Real.log ((82180002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((82180002 : ℕ) : ℝ)) 18 (f := (224421/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_55 : (2 + 902761/1000000 : ℝ) ≤ Real.log (18 + 224421/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 224421/1000000 : ℝ)) 2 (f := (902761/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_55 : ∀ n, Even n → 82180002 ≤ n → n ≤ 84160000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_55 ls_55 (by norm_num) (by norm_num) bnd_55

theorem bnd_56 : GBBound 84160002 86140000 929 := by
  have hq : ∀ x ∈ QKo 157, x ≤ 929 := take_le 157 929 (by decide +kernel)
  have w0 : GBBound 84160002 85150000 929 :=
    gbBound_of_owcheck (lo := 84159073) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_56_0
  have w1 : GBBound 85150002 86140000 929 :=
    gbBound_of_owcheck (lo := 85149073) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_56_1
  have v1 : GBBound 84160002 86140000 929 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_56 : (18 + 248229/1000000 : ℝ) ≤ Real.log ((84160002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((84160002 : ℕ) : ℝ)) 18 (f := (248229/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_56 : (2 + 904067/1000000 : ℝ) ≤ Real.log (18 + 248229/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 248229/1000000 : ℝ)) 2 (f := (904067/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_56 : ∀ n, Even n → 84160002 ≤ n → n ≤ 86140000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_56 ls_56 (by norm_num) (by norm_num) bnd_56

theorem bnd_57 : GBBound 86140002 88120000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 86140002 87130000 907 :=
    gbBound_of_owcheck (lo := 86139095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_57_0
  have w1 : GBBound 87130002 88120000 907 :=
    gbBound_of_owcheck (lo := 87129095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_57_1
  have v1 : GBBound 86140002 88120000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_57 : (18 + 271483/1000000 : ℝ) ≤ Real.log ((86140002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((86140002 : ℕ) : ℝ)) 18 (f := (271483/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_57 : (2 + 45267/50000 : ℝ) ≤ Real.log (18 + 271483/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 271483/1000000 : ℝ)) 2 (f := (45267/50000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_57 : ∀ n, Even n → 86140002 ≤ n → n ≤ 88120000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_57 ls_57 (by norm_num) (by norm_num) bnd_57

theorem bnd_58 : GBBound 88120002 90100000 857 := by
  have hq : ∀ x ∈ QKo 147, x ≤ 857 := take_le 147 857 (by decide +kernel)
  have w0 : GBBound 88120002 89110000 857 :=
    gbBound_of_owcheck (lo := 88119145) (Wb := 495428) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_58_0
  have w1 : GBBound 89110002 90100000 857 :=
    gbBound_of_owcheck (lo := 89109145) (Wb := 495428) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_58_1
  have v1 : GBBound 88120002 90100000 857 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_58 : (18 + 294209/1000000 : ℝ) ≤ Real.log ((88120002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((88120002 : ℕ) : ℝ)) 18 (f := (294209/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_58 : (2 + 906583/1000000 : ℝ) ≤ Real.log (18 + 294209/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 294209/1000000 : ℝ)) 2 (f := (906583/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_58 : ∀ n, Even n → 88120002 ≤ n → n ≤ 90100000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_58 ls_58 (by norm_num) (by norm_num) bnd_58

theorem bnd_59 : GBBound 90100002 92080000 821 := by
  have hq : ∀ x ∈ QKo 141, x ≤ 821 := take_le 141 821 (by decide +kernel)
  have w0 : GBBound 90100002 91090000 821 :=
    gbBound_of_owcheck (lo := 90099181) (Wb := 495410) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_59_0
  have w1 : GBBound 91090002 92080000 821 :=
    gbBound_of_owcheck (lo := 91089181) (Wb := 495410) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_59_1
  have v1 : GBBound 90100002 92080000 821 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_59 : (18 + 316429/1000000 : ℝ) ≤ Real.log ((90100002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((90100002 : ℕ) : ℝ)) 18 (f := (316429/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_59 : (2 + 907797/1000000 : ℝ) ≤ Real.log (18 + 316429/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 316429/1000000 : ℝ)) 2 (f := (907797/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_59 : ∀ n, Even n → 90100002 ≤ n → n ≤ 92080000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_59 ls_59 (by norm_num) (by norm_num) bnd_59

end LeanLab.GvLtR1989
