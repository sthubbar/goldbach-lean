module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W004
public import LeanLab.GvLtR1989.Win.W005
public import LeanLab.GvLtR1989.Win.W006
public import LeanLab.GvLtR1989.Win.W007
public import LeanLab.GvLtR1989.Win.W008
public import LeanLab.GvLtR1989.Win.W009
public import LeanLab.GvLtR1989.Win.W010
public import LeanLab.GvLtR1989.Win.W011

/-!
Blocks 15 to 29, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_15 : GBBound 3970002 4960000 607 := by
  have hq : ∀ x ∈ QKo 110, x ≤ 607 := take_le 110 607 (by decide +kernel)
  have w0 : GBBound 3970002 4960000 607 :=
    gbBound_of_owcheck (lo := 3969395) (Wb := 495303) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_15_0
  exact w0

theorem lr_15 : (15 + 48569/250000 : ℝ) ≤ Real.log ((3970002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((3970002 : ℕ) : ℝ)) 15 (f := (48569/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_15 : (2 + 720917/1000000 : ℝ) ≤ Real.log (15 + 48569/250000 : ℝ) := by
  have h := le_log_of (x := (15 + 48569/250000 : ℝ)) 2 (f := (720917/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_15 : ∀ n, Even n → 3970002 ≤ n → n ≤ 4960000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_15 ls_15 (by norm_num) (by norm_num) bnd_15

theorem bnd_16 : GBBound 4960002 6940000 641 := by
  have hq : ∀ x ∈ QKo 115, x ≤ 641 := take_le 115 641 (by decide +kernel)
  have w0 : GBBound 4960002 5950000 641 :=
    gbBound_of_owcheck (lo := 4959361) (Wb := 495320) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_16_0
  have w1 : GBBound 5950002 6940000 641 :=
    gbBound_of_owcheck (lo := 5949361) (Wb := 495320) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_16_1
  have v1 : GBBound 4960002 6940000 641 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_16 : (15 + 83383/200000 : ℝ) ≤ Real.log ((4960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((4960002 : ℕ) : ℝ)) 15 (f := (83383/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_16 : (2 + 91933/125000 : ℝ) ≤ Real.log (15 + 83383/200000 : ℝ) := by
  have h := le_log_of (x := (15 + 83383/200000 : ℝ)) 2 (f := (91933/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_16 : ∀ n, Even n → 4960002 ≤ n → n ≤ 6940000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_16 ls_16 (by norm_num) (by norm_num) bnd_16

theorem bnd_17 : GBBound 6940002 8920000 733 := by
  have hq : ∀ x ∈ QKo 129, x ≤ 733 := take_le 129 733 (by decide +kernel)
  have w0 : GBBound 6940002 7930000 733 :=
    gbBound_of_owcheck (lo := 6939269) (Wb := 495366) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_17_0
  have w1 : GBBound 7930002 8920000 733 :=
    gbBound_of_owcheck (lo := 7929269) (Wb := 495366) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_17_1
  have v1 : GBBound 6940002 8920000 733 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_17 : (15 + 752811/1000000 : ℝ) ≤ Real.log ((6940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((6940002 : ℕ) : ℝ)) 15 (f := (752811/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_17 : (2 + 757017/1000000 : ℝ) ≤ Real.log (15 + 752811/1000000 : ℝ) := by
  have h := le_log_of (x := (15 + 752811/1000000 : ℝ)) 2 (f := (757017/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_17 : ∀ n, Even n → 6940002 ≤ n → n ≤ 8920000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_17 ls_17 (by norm_num) (by norm_num) bnd_17

theorem bnd_18 : GBBound 8920002 10900000 829 := by
  have hq : ∀ x ∈ QKo 144, x ≤ 829 := take_le 144 829 (by decide +kernel)
  have w0 : GBBound 8920002 9910000 829 :=
    gbBound_of_owcheck (lo := 8919173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_18_0
  have w1 : GBBound 9910002 10900000 829 :=
    gbBound_of_owcheck (lo := 9909173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_18_1
  have v1 : GBBound 8920002 10900000 829 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_18 : (16 + 761/200000 : ℝ) ≤ Real.log ((8920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((8920002 : ℕ) : ℝ)) 16 (f := (761/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_18 : (2 + 30913/40000 : ℝ) ≤ Real.log (16 + 761/200000 : ℝ) := by
  have h := le_log_of (x := (16 + 761/200000 : ℝ)) 2 (f := (30913/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_18 : ∀ n, Even n → 8920002 ≤ n → n ≤ 10900000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_18 ls_18 (by norm_num) (by norm_num) bnd_18

theorem bnd_19 : GBBound 10900002 12880000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 10900002 11890000 751 :=
    gbBound_of_owcheck (lo := 10899251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_19_0
  have w1 : GBBound 11890002 12880000 751 :=
    gbBound_of_owcheck (lo := 11889251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_19_1
  have v1 : GBBound 10900002 12880000 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_19 : (16 + 12767/62500 : ℝ) ≤ Real.log ((10900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((10900002 : ℕ) : ℝ)) 16 (f := (12767/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_19 : (2 + 785273/1000000 : ℝ) ≤ Real.log (16 + 12767/62500 : ℝ) := by
  have h := le_log_of (x := (16 + 12767/62500 : ℝ)) 2 (f := (785273/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_19 : ∀ n, Even n → 10900002 ≤ n → n ≤ 12880000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_19 ls_19 (by norm_num) (by norm_num) bnd_19

theorem bnd_20 : GBBound 12880002 14860000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 12880002 13870000 751 :=
    gbBound_of_owcheck (lo := 12879251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_20_0
  have w1 : GBBound 13870002 14860000 751 :=
    gbBound_of_owcheck (lo := 13869251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_20_1
  have v1 : GBBound 12880002 14860000 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_20 : (16 + 74237/200000 : ℝ) ≤ Real.log ((12880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((12880002 : ℕ) : ℝ)) 16 (f := (74237/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_20 : (2 + 795521/1000000 : ℝ) ≤ Real.log (16 + 74237/200000 : ℝ) := by
  have h := le_log_of (x := (16 + 74237/200000 : ℝ)) 2 (f := (795521/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_20 : ∀ n, Even n → 12880002 ≤ n → n ≤ 14860000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_20 ls_20 (by norm_num) (by norm_num) bnd_20

theorem bnd_21 : GBBound 14860002 16840000 673 := by
  have hq : ∀ x ∈ QKo 121, x ≤ 673 := take_le 121 673 (by decide +kernel)
  have w0 : GBBound 14860002 15850000 673 :=
    gbBound_of_owcheck (lo := 14859329) (Wb := 495336) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_21_0
  have w1 : GBBound 15850002 16840000 673 :=
    gbBound_of_owcheck (lo := 15849329) (Wb := 495336) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_21_1
  have v1 : GBBound 14860002 16840000 673 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_21 : (16 + 257091/500000 : ℝ) ≤ Real.log ((14860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((14860002 : ℕ) : ℝ)) 16 (f := (257091/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_21 : (2 + 402109/500000 : ℝ) ≤ Real.log (16 + 257091/500000 : ℝ) := by
  have h := le_log_of (x := (16 + 257091/500000 : ℝ)) 2 (f := (402109/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_21 : ∀ n, Even n → 14860002 ≤ n → n ≤ 16840000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_21 ls_21 (by norm_num) (by norm_num) bnd_21

theorem bnd_22 : GBBound 16840002 18820000 733 := by
  have hq : ∀ x ∈ QKo 129, x ≤ 733 := take_le 129 733 (by decide +kernel)
  have w0 : GBBound 16840002 17830000 733 :=
    gbBound_of_owcheck (lo := 16839269) (Wb := 495366) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_0
  have w1 : GBBound 17830002 18820000 733 :=
    gbBound_of_owcheck (lo := 17829269) (Wb := 495366) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_22_1
  have v1 : GBBound 16840002 18820000 733 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_22 : (16 + 319633/500000 : ℝ) ≤ Real.log ((16840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((16840002 : ℕ) : ℝ)) 16 (f := (319633/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_22 : (2 + 202941/250000 : ℝ) ≤ Real.log (16 + 319633/500000 : ℝ) := by
  have h := le_log_of (x := (16 + 319633/500000 : ℝ)) 2 (f := (202941/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_22 : ∀ n, Even n → 16840002 ≤ n → n ≤ 18820000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_22 ls_22 (by norm_num) (by norm_num) bnd_22

theorem bnd_23 : GBBound 18820002 20800000 733 := by
  have hq : ∀ x ∈ QKo 129, x ≤ 733 := take_le 129 733 (by decide +kernel)
  have w0 : GBBound 18820002 19810000 733 :=
    gbBound_of_owcheck (lo := 18819269) (Wb := 495366) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_0
  have w1 : GBBound 19810002 20800000 733 :=
    gbBound_of_owcheck (lo := 19809269) (Wb := 495366) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_1
  have v1 : GBBound 18820002 20800000 733 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_23 : (16 + 750429/1000000 : ℝ) ≤ Real.log ((18820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((18820002 : ℕ) : ℝ)) 16 (f := (750429/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_23 : (2 + 409211/500000 : ℝ) ≤ Real.log (16 + 750429/1000000 : ℝ) := by
  have h := le_log_of (x := (16 + 750429/1000000 : ℝ)) 2 (f := (409211/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_23 : ∀ n, Even n → 18820002 ≤ n → n ≤ 20800000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_23 ls_23 (by norm_num) (by norm_num) bnd_23

theorem bnd_24 : GBBound 20800002 22780000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 20800002 21790000 823 :=
    gbBound_of_owcheck (lo := 20799179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_24_0
  have w1 : GBBound 21790002 22780000 823 :=
    gbBound_of_owcheck (lo := 21789179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_24_1
  have v1 : GBBound 20800002 22780000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_24 : (16 + 425231/500000 : ℝ) ≤ Real.log ((20800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((20800002 : ℕ) : ℝ)) 16 (f := (425231/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_24 : (2 + 824377/1000000 : ℝ) ≤ Real.log (16 + 425231/500000 : ℝ) := by
  have h := le_log_of (x := (16 + 425231/500000 : ℝ)) 2 (f := (824377/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_24 : ∀ n, Even n → 20800002 ≤ n → n ≤ 22780000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_24 ls_24 (by norm_num) (by norm_num) bnd_24

theorem bnd_25 : GBBound 22780002 24760000 929 := by
  have hq : ∀ x ∈ QKo 157, x ≤ 929 := take_le 157 929 (by decide +kernel)
  have w0 : GBBound 22780002 23770000 929 :=
    gbBound_of_owcheck (lo := 22779073) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_0
  have w1 : GBBound 23770002 24760000 929 :=
    gbBound_of_owcheck (lo := 23769073) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_1
  have v1 : GBBound 22780002 24760000 929 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_25 : (16 + 58837/62500 : ℝ) ≤ Real.log ((22780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((22780002 : ℕ) : ℝ)) 16 (f := (58837/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_25 : (2 + 414879/500000 : ℝ) ≤ Real.log (16 + 58837/62500 : ℝ) := by
  have h := le_log_of (x := (16 + 58837/62500 : ℝ)) 2 (f := (414879/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_25 : ∀ n, Even n → 22780002 ≤ n → n ≤ 24760000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_25 ls_25 (by norm_num) (by norm_num) bnd_25

theorem bnd_26 : GBBound 24760002 26740000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 24760002 25750000 751 :=
    gbBound_of_owcheck (lo := 24759251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_0
  have w1 : GBBound 25750002 26740000 751 :=
    gbBound_of_owcheck (lo := 25749251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_26_1
  have v1 : GBBound 24760002 26740000 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_26 : (17 + 24739/1000000 : ℝ) ≤ Real.log ((24760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((24760002 : ℕ) : ℝ)) 17 (f := (24739/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_26 : (2 + 417333/500000 : ℝ) ≤ Real.log (17 + 24739/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 24739/1000000 : ℝ)) 2 (f := (417333/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_26 : ∀ n, Even n → 24760002 ≤ n → n ≤ 26740000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_26 ls_26 (by norm_num) (by norm_num) bnd_26

theorem bnd_27 : GBBound 26740002 28720000 997 := by
  have hq : ∀ x ∈ QKo 167, x ≤ 997 := take_le 167 997 (by decide +kernel)
  have w0 : GBBound 26740002 27730000 997 :=
    gbBound_of_owcheck (lo := 26739005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_0
  have w1 : GBBound 27730002 28720000 997 :=
    gbBound_of_owcheck (lo := 27729005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_27_1
  have v1 : GBBound 26740002 28720000 997 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_27 : (17 + 10167/100000 : ℝ) ≤ Real.log ((26740002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((26740002 : ℕ) : ℝ)) 17 (f := (10167/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_27 : (2 + 33567/40000 : ℝ) ≤ Real.log (17 + 10167/100000 : ℝ) := by
  have h := le_log_of (x := (17 + 10167/100000 : ℝ)) 2 (f := (33567/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_27 : ∀ n, Even n → 26740002 ≤ n → n ≤ 28720000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_27 ls_27 (by norm_num) (by norm_num) bnd_27

theorem bnd_28 : GBBound 28720002 30700000 797 := by
  have hq : ∀ x ∈ QKo 138, x ≤ 797 := take_le 138 797 (by decide +kernel)
  have w0 : GBBound 28720002 29710000 797 :=
    gbBound_of_owcheck (lo := 28719205) (Wb := 495398) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_28_0
  have w1 : GBBound 29710002 30700000 797 :=
    gbBound_of_owcheck (lo := 29709205) (Wb := 495398) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_28_1
  have v1 : GBBound 28720002 30700000 797 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_28 : (17 + 173103/1000000 : ℝ) ≤ Real.log ((28720002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((28720002 : ℕ) : ℝ)) 17 (f := (173103/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_28 : (2 + 843343/1000000 : ℝ) ≤ Real.log (17 + 173103/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 173103/1000000 : ℝ)) 2 (f := (843343/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_28 : ∀ n, Even n → 28720002 ≤ n → n ≤ 30700000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_28 ls_28 (by norm_num) (by norm_num) bnd_28

theorem bnd_29 : GBBound 30700002 32680000 811 := by
  have hq : ∀ x ∈ QKo 140, x ≤ 811 := take_le 140 811 (by decide +kernel)
  have w0 : GBBound 30700002 31690000 811 :=
    gbBound_of_owcheck (lo := 30699191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_29_0
  have w1 : GBBound 31690002 32680000 811 :=
    gbBound_of_owcheck (lo := 31689191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_29_1
  have v1 : GBBound 30700002 32680000 811 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_29 : (17 + 59943/250000 : ℝ) ≤ Real.log ((30700002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((30700002 : ℕ) : ℝ)) 17 (f := (59943/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_29 : (2 + 423609/500000 : ℝ) ≤ Real.log (17 + 59943/250000 : ℝ) := by
  have h := le_log_of (x := (17 + 59943/250000 : ℝ)) 2 (f := (423609/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_29 : ∀ n, Even n → 30700002 ≤ n → n ≤ 32680000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_29 ls_29 (by norm_num) (by norm_num) bnd_29

end LeanLab.GvLtR1989
