module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W011
public import LeanLab.GvLtR1989.Win.W012
public import LeanLab.GvLtR1989.Win.W013
public import LeanLab.GvLtR1989.Win.W014
public import LeanLab.GvLtR1989.Win.W015
public import LeanLab.GvLtR1989.Win.W016
public import LeanLab.GvLtR1989.Win.W017
public import LeanLab.GvLtR1989.Win.W018

/-!
Blocks 30 to 44, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_30 : GBBound 32680002 34660000 769 := by
  have hq : ∀ x ∈ QKo 135, x ≤ 769 := take_le 135 769 (by decide +kernel)
  have w0 : GBBound 32680002 33670000 769 :=
    gbBound_of_owcheck (lo := 32679233) (Wb := 495384) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_30_0
  have w1 : GBBound 33670002 34660000 769 :=
    gbBound_of_owcheck (lo := 33669233) (Wb := 495384) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_30_1
  have v1 : GBBound 32680002 34660000 769 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_30 : (17 + 4723/15625 : ℝ) ≤ Real.log ((32680002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((32680002 : ℕ) : ℝ)) 17 (f := (4723/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_30 : (2 + 212709/250000 : ℝ) ≤ Real.log (17 + 4723/15625 : ℝ) := by
  have h := le_log_of (x := (17 + 4723/15625 : ℝ)) 2 (f := (212709/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_30 : ∀ n, Even n → 32680002 ≤ n → n ≤ 34660000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_30 ls_30 (by norm_num) (by norm_num) bnd_30

theorem bnd_31 : GBBound 34660002 36640000 877 := by
  have hq : ∀ x ∈ QKo 150, x ≤ 877 := take_le 150 877 (by decide +kernel)
  have w0 : GBBound 34660002 35650000 877 :=
    gbBound_of_owcheck (lo := 34659125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_31_0
  have w1 : GBBound 35650002 36640000 877 :=
    gbBound_of_owcheck (lo := 35649125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_31_1
  have v1 : GBBound 34660002 36640000 877 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_31 : (17 + 72219/200000 : ℝ) ≤ Real.log ((34660002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((34660002 : ℕ) : ℝ)) 17 (f := (72219/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_31 : (2 + 85423/100000 : ℝ) ≤ Real.log (17 + 72219/200000 : ℝ) := by
  have h := le_log_of (x := (17 + 72219/200000 : ℝ)) 2 (f := (85423/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_31 : ∀ n, Even n → 34660002 ≤ n → n ≤ 36640000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_31 ls_31 (by norm_num) (by norm_num) bnd_31

theorem bnd_32 : GBBound 36640002 38620000 1039 := by
  have hq : ∀ x ∈ QKo 174, x ≤ 1039 := take_le 174 1039 (by decide +kernel)
  have w0 : GBBound 36640002 37630000 1039 :=
    gbBound_of_owcheck (lo := 36638963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_32_0
  have w1 : GBBound 37630002 38620000 1039 :=
    gbBound_of_owcheck (lo := 37628963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_32_1
  have v1 : GBBound 36640002 38620000 1039 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_32 : (17 + 8333/20000 : ℝ) ≤ Real.log ((36640002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((36640002 : ℕ) : ℝ)) 17 (f := (8333/20000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_32 : (2 + 34297/40000 : ℝ) ≤ Real.log (17 + 8333/20000 : ℝ) := by
  have h := le_log_of (x := (17 + 8333/20000 : ℝ)) 2 (f := (34297/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_32 : ∀ n, Even n → 36640002 ≤ n → n ≤ 38620000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_32 ls_32 (by norm_num) (by norm_num) bnd_32

theorem bnd_33 : GBBound 38620002 40600000 787 := by
  have hq : ∀ x ∈ QKo 137, x ≤ 787 := take_le 137 787 (by decide +kernel)
  have w0 : GBBound 38620002 39610000 787 :=
    gbBound_of_owcheck (lo := 38619215) (Wb := 495393) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_33_0
  have w1 : GBBound 39610002 40600000 787 :=
    gbBound_of_owcheck (lo := 39609215) (Wb := 495393) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_33_1
  have v1 : GBBound 38620002 40600000 787 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_33 : (17 + 469279/1000000 : ℝ) ≤ Real.log ((38620002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((38620002 : ℕ) : ℝ)) 17 (f := (469279/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_33 : (2 + 430221/500000 : ℝ) ≤ Real.log (17 + 469279/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 469279/1000000 : ℝ)) 2 (f := (430221/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_33 : ∀ n, Even n → 38620002 ≤ n → n ≤ 40600000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_33 ls_33 (by norm_num) (by norm_num) bnd_33

theorem bnd_34 : GBBound 40600002 42580000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 40600002 41590000 823 :=
    gbBound_of_owcheck (lo := 40599179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_34_0
  have w1 : GBBound 41590002 42580000 823 :=
    gbBound_of_owcheck (lo := 41589179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_34_1
  have v1 : GBBound 40600002 42580000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_34 : (17 + 519277/1000000 : ℝ) ≤ Real.log ((40600002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((40600002 : ℕ) : ℝ)) 17 (f := (519277/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_34 : (2 + 8633/10000 : ℝ) ≤ Real.log (17 + 519277/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 519277/1000000 : ℝ)) 2 (f := (8633/10000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_34 : ∀ n, Even n → 40600002 ≤ n → n ≤ 42580000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_34 ls_34 (by norm_num) (by norm_num) bnd_34

theorem bnd_35 : GBBound 42580002 44560000 769 := by
  have hq : ∀ x ∈ QKo 135, x ≤ 769 := take_le 135 769 (by decide +kernel)
  have w0 : GBBound 42580002 43570000 769 :=
    gbBound_of_owcheck (lo := 42579233) (Wb := 495384) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_35_0
  have w1 : GBBound 43570002 44560000 769 :=
    gbBound_of_owcheck (lo := 43569233) (Wb := 495384) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_35_1
  have v1 : GBBound 42580002 44560000 769 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_35 : (17 + 283447/500000 : ℝ) ≤ Real.log ((42580002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((42580002 : ℕ) : ℝ)) 17 (f := (283447/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_35 : (2 + 173203/200000 : ℝ) ≤ Real.log (17 + 283447/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 283447/500000 : ℝ)) 2 (f := (173203/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_35 : ∀ n, Even n → 42580002 ≤ n → n ≤ 44560000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_35 ls_35 (by norm_num) (by norm_num) bnd_35

theorem bnd_36 : GBBound 44560002 46540000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 44560002 45550000 823 :=
    gbBound_of_owcheck (lo := 44559179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_36_0
  have w1 : GBBound 45550002 46540000 823 :=
    gbBound_of_owcheck (lo := 45549179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_36_1
  have v1 : GBBound 44560002 46540000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_36 : (17 + 306173/500000 : ℝ) ≤ Real.log ((44560002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((44560002 : ℕ) : ℝ)) 17 (f := (306173/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_36 : (2 + 868599/1000000 : ℝ) ≤ Real.log (17 + 306173/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 306173/500000 : ℝ)) 2 (f := (868599/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_36 : ∀ n, Even n → 44560002 ≤ n → n ≤ 46540000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_36 ls_36 (by norm_num) (by norm_num) bnd_36

theorem bnd_37 : GBBound 46540002 48520000 811 := by
  have hq : ∀ x ∈ QKo 140, x ≤ 811 := take_le 140 811 (by decide +kernel)
  have w0 : GBBound 46540002 47530000 811 :=
    gbBound_of_owcheck (lo := 46539191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_37_0
  have w1 : GBBound 47530002 48520000 811 :=
    gbBound_of_owcheck (lo := 47529191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_37_1
  have v1 : GBBound 46540002 48520000 811 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_37 : (17 + 655821/1000000 : ℝ) ≤ Real.log ((46540002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((46540002 : ℕ) : ℝ)) 17 (f := (655821/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_37 : (2 + 108883/125000 : ℝ) ≤ Real.log (17 + 655821/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 655821/1000000 : ℝ)) 2 (f := (108883/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_37 : ∀ n, Even n → 46540002 ≤ n → n ≤ 48520000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_37 ls_37 (by norm_num) (by norm_num) bnd_37

theorem bnd_38 : GBBound 48520002 50500000 761 := by
  have hq : ∀ x ∈ QKo 134, x ≤ 761 := take_le 134 761 (by decide +kernel)
  have w0 : GBBound 48520002 49510000 761 :=
    gbBound_of_owcheck (lo := 48519241) (Wb := 495380) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_38_0
  have w1 : GBBound 49510002 50500000 761 :=
    gbBound_of_owcheck (lo := 49509241) (Wb := 495380) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_38_1
  have v1 : GBBound 48520002 50500000 761 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_38 : (17 + 139497/200000 : ℝ) ≤ Real.log ((48520002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((48520002 : ℕ) : ℝ)) 17 (f := (139497/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_38 : (2 + 873421/1000000 : ℝ) ≤ Real.log (17 + 139497/200000 : ℝ) := by
  have h := le_log_of (x := (17 + 139497/200000 : ℝ)) 2 (f := (873421/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_38 : ∀ n, Even n → 48520002 ≤ n → n ≤ 50500000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_38 ls_38 (by norm_num) (by norm_num) bnd_38

theorem bnd_39 : GBBound 50500002 52480000 821 := by
  have hq : ∀ x ∈ QKo 141, x ≤ 821 := take_le 141 821 (by decide +kernel)
  have w0 : GBBound 50500002 51490000 821 :=
    gbBound_of_owcheck (lo := 50499181) (Wb := 495410) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_39_0
  have w1 : GBBound 51490002 52480000 821 :=
    gbBound_of_owcheck (lo := 51489181) (Wb := 495410) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_39_1
  have v1 : GBBound 50500002 52480000 821 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_39 : (17 + 368741/500000 : ℝ) ≤ Real.log ((50500002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((50500002 : ℕ) : ℝ)) 17 (f := (368741/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_39 : (2 + 875679/1000000 : ℝ) ≤ Real.log (17 + 368741/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 368741/500000 : ℝ)) 2 (f := (875679/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_39 : ∀ n, Even n → 50500002 ≤ n → n ≤ 52480000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_39 ls_39 (by norm_num) (by norm_num) bnd_39

theorem bnd_40 : GBBound 52480002 54460000 761 := by
  have hq : ∀ x ∈ QKo 134, x ≤ 761 := take_le 134 761 (by decide +kernel)
  have w0 : GBBound 52480002 53470000 761 :=
    gbBound_of_owcheck (lo := 52479241) (Wb := 495380) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_40_0
  have w1 : GBBound 53470002 54460000 761 :=
    gbBound_of_owcheck (lo := 53469241) (Wb := 495380) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_40_1
  have v1 : GBBound 52480002 54460000 761 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_40 : (17 + 775941/1000000 : ℝ) ≤ Real.log ((52480002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((52480002 : ℕ) : ℝ)) 17 (f := (775941/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_40 : (2 + 219461/250000 : ℝ) ≤ Real.log (17 + 775941/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 775941/1000000 : ℝ)) 2 (f := (219461/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_40 : ∀ n, Even n → 52480002 ≤ n → n ≤ 54460000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_40 ls_40 (by norm_num) (by norm_num) bnd_40

theorem bnd_41 : GBBound 54460002 56440000 857 := by
  have hq : ∀ x ∈ QKo 147, x ≤ 857 := take_le 147 857 (by decide +kernel)
  have w0 : GBBound 54460002 55450000 857 :=
    gbBound_of_owcheck (lo := 54459145) (Wb := 495428) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_41_0
  have w1 : GBBound 55450002 56440000 857 :=
    gbBound_of_owcheck (lo := 55449145) (Wb := 495428) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_41_1
  have v1 : GBBound 54460002 56440000 857 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_41 : (17 + 50811/62500 : ℝ) ≤ Real.log ((54460002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((54460002 : ℕ) : ℝ)) 17 (f := (50811/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_41 : (2 + 439963/500000 : ℝ) ≤ Real.log (17 + 50811/62500 : ℝ) := by
  have h := le_log_of (x := (17 + 50811/62500 : ℝ)) 2 (f := (439963/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_41 : ∀ n, Even n → 54460002 ≤ n → n ≤ 56440000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_41 ls_41 (by norm_num) (by norm_num) bnd_41

theorem bnd_42 : GBBound 56440002 58420000 809 := by
  have hq : ∀ x ∈ QKo 139, x ≤ 809 := take_le 139 809 (by decide +kernel)
  have w0 : GBBound 56440002 57430000 809 :=
    gbBound_of_owcheck (lo := 56439193) (Wb := 495404) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_42_0
  have w1 : GBBound 57430002 58420000 809 :=
    gbBound_of_owcheck (lo := 57429193) (Wb := 495404) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_42_1
  have v1 : GBBound 56440002 58420000 809 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_42 : (17 + 848687/1000000 : ℝ) ≤ Real.log ((56440002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((56440002 : ℕ) : ℝ)) 17 (f := (848687/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_42 : (2 + 110241/125000 : ℝ) ≤ Real.log (17 + 848687/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 848687/1000000 : ℝ)) 2 (f := (110241/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_42 : ∀ n, Even n → 56440002 ≤ n → n ≤ 58420000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_42 ls_42 (by norm_num) (by norm_num) bnd_42

theorem bnd_43 : GBBound 58420002 60400000 1093 := by
  have hq : ∀ x ∈ QKo 182, x ≤ 1093 := take_le 182 1093 (by decide +kernel)
  have w0 : GBBound 58420002 59410000 1093 :=
    gbBound_of_owcheck (lo := 58418909) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_43_0
  have w1 : GBBound 59410002 60400000 1093 :=
    gbBound_of_owcheck (lo := 59408909) (Wb := 495546) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_43_1
  have v1 : GBBound 58420002 60400000 1093 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_43 : (17 + 883167/1000000 : ℝ) ≤ Real.log ((58420002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((58420002 : ℕ) : ℝ)) 17 (f := (883167/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_43 : (2 + 441929/500000 : ℝ) ≤ Real.log (17 + 883167/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 883167/1000000 : ℝ)) 2 (f := (441929/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_43 : ∀ n, Even n → 58420002 ≤ n → n ≤ 60400000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_43 ls_43 (by norm_num) (by norm_num) bnd_43

theorem bnd_44 : GBBound 60400002 62380000 769 := by
  have hq : ∀ x ∈ QKo 135, x ≤ 769 := take_le 135 769 (by decide +kernel)
  have w0 : GBBound 60400002 61390000 769 :=
    gbBound_of_owcheck (lo := 60399233) (Wb := 495384) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_44_0
  have w1 : GBBound 61390002 62380000 769 :=
    gbBound_of_owcheck (lo := 61389233) (Wb := 495384) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_44_1
  have v1 : GBBound 60400002 62380000 769 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_44 : (17 + 458249/500000 : ℝ) ≤ Real.log ((60400002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((60400002 : ℕ) : ℝ)) 17 (f := (458249/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_44 : (2 + 22143/25000 : ℝ) ≤ Real.log (17 + 458249/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 458249/500000 : ℝ)) 2 (f := (22143/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_44 : ∀ n, Even n → 60400002 ≤ n → n ≤ 62380000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_44 ls_44 (by norm_num) (by norm_num) bnd_44

end LeanLab.GvLtR1989
