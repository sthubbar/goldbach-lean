module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W026
public import LeanLab.GvLtR1989.Win.W027
public import LeanLab.GvLtR1989.Win.W028
public import LeanLab.GvLtR1989.Win.W029
public import LeanLab.GvLtR1989.Win.W030
public import LeanLab.GvLtR1989.Win.W031
public import LeanLab.GvLtR1989.Win.W032
public import LeanLab.GvLtR1989.Win.W033

/-!
Blocks 60 to 74, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_60 : GBBound 92080002 94060000 827 := by
  have hq : ∀ x ∈ QKo 143, x ≤ 827 := take_le 143 827 (by decide +kernel)
  have w0 : GBBound 92080002 93070000 827 :=
    gbBound_of_owcheck (lo := 92079175) (Wb := 495413) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_60_0
  have w1 : GBBound 93070002 94060000 827 :=
    gbBound_of_owcheck (lo := 93069175) (Wb := 495413) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_60_1
  have v1 : GBBound 92080002 94060000 827 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_60 : (18 + 338167/1000000 : ℝ) ≤ Real.log ((92080002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((92080002 : ℕ) : ℝ)) 18 (f := (338167/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_60 : (2 + 908983/1000000 : ℝ) ≤ Real.log (18 + 338167/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 338167/1000000 : ℝ)) 2 (f := (908983/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_60 : ∀ n, Even n → 92080002 ≤ n → n ≤ 94060000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_60 ls_60 (by norm_num) (by norm_num) bnd_60

theorem bnd_61 : GBBound 94060002 96040000 859 := by
  have hq : ∀ x ∈ QKo 148, x ≤ 859 := take_le 148 859 (by decide +kernel)
  have w0 : GBBound 94060002 95050000 859 :=
    gbBound_of_owcheck (lo := 94059143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_61_0
  have w1 : GBBound 95050002 96040000 859 :=
    gbBound_of_owcheck (lo := 95049143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_61_1
  have v1 : GBBound 94060002 96040000 859 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_61 : (18 + 179721/500000 : ℝ) ≤ Real.log ((94060002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((94060002 : ℕ) : ℝ)) 18 (f := (179721/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_61 : (2 + 455071/500000 : ℝ) ≤ Real.log (18 + 179721/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 179721/500000 : ℝ)) 2 (f := (455071/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_61 : ∀ n, Even n → 94060002 ≤ n → n ≤ 96040000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_61 ls_61 (by norm_num) (by norm_num) bnd_61

theorem bnd_62 : GBBound 96040002 98020000 919 := by
  have hq : ∀ x ∈ QKo 156, x ≤ 919 := take_le 156 919 (by decide +kernel)
  have w0 : GBBound 96040002 97030000 919 :=
    gbBound_of_owcheck (lo := 96039083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_62_0
  have w1 : GBBound 97030002 98020000 919 :=
    gbBound_of_owcheck (lo := 97029083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_62_1
  have v1 : GBBound 96040002 98020000 919 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_62 : (18 + 190137/500000 : ℝ) ≤ Real.log ((96040002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((96040002 : ℕ) : ℝ)) 18 (f := (190137/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_62 : (2 + 911277/1000000 : ℝ) ≤ Real.log (18 + 190137/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 190137/500000 : ℝ)) 2 (f := (911277/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_62 : ∀ n, Even n → 96040002 ≤ n → n ≤ 98020000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_62 ls_62 (by norm_num) (by norm_num) bnd_62

theorem bnd_63 : GBBound 98020002 100000000 829 := by
  have hq : ∀ x ∈ QKo 144, x ≤ 829 := take_le 144 829 (by decide +kernel)
  have w0 : GBBound 98020002 99010000 829 :=
    gbBound_of_owcheck (lo := 98019173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_63_0
  have w1 : GBBound 99010002 100000000 829 :=
    gbBound_of_owcheck (lo := 99009173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_63_1
  have v1 : GBBound 98020002 100000000 829 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_63 : (18 + 400681/1000000 : ℝ) ≤ Real.log ((98020002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((98020002 : ℕ) : ℝ)) 18 (f := (400681/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_63 : (2 + 456193/500000 : ℝ) ≤ Real.log (18 + 400681/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 400681/1000000 : ℝ)) 2 (f := (456193/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_63 : ∀ n, Even n → 98020002 ≤ n → n ≤ 100000000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_63 ls_63 (by norm_num) (by norm_num) bnd_63

theorem bnd_64 : GBBound 100000002 101980000 1039 := by
  have hq : ∀ x ∈ QKo 174, x ≤ 1039 := take_le 174 1039 (by decide +kernel)
  have w0 : GBBound 100000002 100990000 1039 :=
    gbBound_of_owcheck (lo := 99998963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_64_0
  have w1 : GBBound 100990002 101980000 1039 :=
    gbBound_of_owcheck (lo := 100988963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_64_1
  have v1 : GBBound 100000002 101980000 1039 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_64 : (18 + 420679/1000000 : ℝ) ≤ Real.log ((100000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((100000002 : ℕ) : ℝ)) 18 (f := (420679/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_64 : (2 + 14273/15625 : ℝ) ≤ Real.log (18 + 420679/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 420679/1000000 : ℝ)) 2 (f := (14273/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_64 : ∀ n, Even n → 100000002 ≤ n → n ≤ 101980000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_64 ls_64 (by norm_num) (by norm_num) bnd_64

theorem bnd_65 : GBBound 101980002 103960000 953 := by
  have hq : ∀ x ∈ QKo 161, x ≤ 953 := take_le 161 953 (by decide +kernel)
  have w0 : GBBound 101980002 102970000 953 :=
    gbBound_of_owcheck (lo := 101979049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_65_0
  have w1 : GBBound 102970002 103960000 953 :=
    gbBound_of_owcheck (lo := 102969049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_65_1
  have v1 : GBBound 101980002 103960000 953 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_65 : (18 + 220143/500000 : ℝ) ≤ Real.log ((101980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((101980002 : ℕ) : ℝ)) 18 (f := (220143/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_65 : (2 + 114317/125000 : ℝ) ≤ Real.log (18 + 220143/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 220143/500000 : ℝ)) 2 (f := (114317/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_65 : ∀ n, Even n → 101980002 ≤ n → n ≤ 103960000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_65 ls_65 (by norm_num) (by norm_num) bnd_65

theorem bnd_66 : GBBound 103960002 105940000 1009 := by
  have hq : ∀ x ∈ QKo 168, x ≤ 1009 := take_le 168 1009 (by decide +kernel)
  have w0 : GBBound 103960002 104950000 1009 :=
    gbBound_of_owcheck (lo := 103958993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_66_0
  have w1 : GBBound 104950002 105940000 1009 :=
    gbBound_of_owcheck (lo := 104948993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_66_1
  have v1 : GBBound 103960002 105940000 1009 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_66 : (18 + 91903/200000 : ℝ) ≤ Real.log ((103960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((103960002 : ℕ) : ℝ)) 18 (f := (91903/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_66 : (2 + 457789/500000 : ℝ) ≤ Real.log (18 + 91903/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 91903/200000 : ℝ)) 2 (f := (457789/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_66 : ∀ n, Even n → 103960002 ≤ n → n ≤ 105940000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_66 ls_66 (by norm_num) (by norm_num) bnd_66

theorem bnd_67 : GBBound 105940002 107920000 863 := by
  have hq : ∀ x ∈ QKo 149, x ≤ 863 := take_le 149 863 (by decide +kernel)
  have w0 : GBBound 105940002 106930000 863 :=
    gbBound_of_owcheck (lo := 105939139) (Wb := 495431) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_67_0
  have w1 : GBBound 106930002 107920000 863 :=
    gbBound_of_owcheck (lo := 106929139) (Wb := 495431) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_67_1
  have v1 : GBBound 105940002 107920000 863 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_67 : (18 + 239191/500000 : ℝ) ≤ Real.log ((105940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((105940002 : ℕ) : ℝ)) 18 (f := (239191/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_67 : (2 + 4583/5000 : ℝ) ≤ Real.log (18 + 239191/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 239191/500000 : ℝ)) 2 (f := (4583/5000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_67 : ∀ n, Even n → 105940002 ≤ n → n ≤ 107920000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_67 ls_67 (by norm_num) (by norm_num) bnd_67

theorem bnd_68 : GBBound 107920002 109900000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 107920002 108910000 823 :=
    gbBound_of_owcheck (lo := 107919179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_68_0
  have w1 : GBBound 108910002 109900000 823 :=
    gbBound_of_owcheck (lo := 108909179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_68_1
  have v1 : GBBound 107920002 109900000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_68 : (18 + 496899/1000000 : ℝ) ≤ Real.log ((107920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((107920002 : ℕ) : ℝ)) 18 (f := (496899/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_68 : (2 + 458801/500000 : ℝ) ≤ Real.log (18 + 496899/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 496899/1000000 : ℝ)) 2 (f := (458801/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_68 : ∀ n, Even n → 107920002 ≤ n → n ≤ 109900000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_68 ls_68 (by norm_num) (by norm_num) bnd_68

theorem bnd_69 : GBBound 109900002 111880000 739 := by
  have hq : ∀ x ∈ QKo 130, x ≤ 739 := take_le 130 739 (by decide +kernel)
  have w0 : GBBound 109900002 110890000 739 :=
    gbBound_of_owcheck (lo := 109899263) (Wb := 495369) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_69_0
  have w1 : GBBound 110890002 111880000 739 :=
    gbBound_of_owcheck (lo := 110889263) (Wb := 495369) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_69_1
  have v1 : GBBound 109900002 111880000 739 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_69 : (18 + 12877/25000 : ℝ) ≤ Real.log ((109900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((109900002 : ℕ) : ℝ)) 18 (f := (12877/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_69 : (2 + 114823/125000 : ℝ) ≤ Real.log (18 + 12877/25000 : ℝ) := by
  have h := le_log_of (x := (18 + 12877/25000 : ℝ)) 2 (f := (114823/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_69 : ∀ n, Even n → 109900002 ≤ n → n ≤ 111880000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_69 ls_69 (by norm_num) (by norm_num) bnd_69

theorem bnd_70 : GBBound 111880002 113860000 1163 := by
  have hq : ∀ x ∈ QKo 191, x ≤ 1163 := take_le 191 1163 (by decide +kernel)
  have w0 : GBBound 111880002 112870000 1163 :=
    gbBound_of_owcheck (lo := 111878839) (Wb := 495581) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_70_0
  have w1 : GBBound 112870002 113860000 1163 :=
    gbBound_of_owcheck (lo := 112868839) (Wb := 495581) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_70_1
  have v1 : GBBound 111880002 113860000 1163 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_70 : (18 + 66617/125000 : ℝ) ≤ Real.log ((111880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((111880002 : ℕ) : ℝ)) 18 (f := (66617/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_70 : (2 + 229887/250000 : ℝ) ≤ Real.log (18 + 66617/125000 : ℝ) := by
  have h := le_log_of (x := (18 + 66617/125000 : ℝ)) 2 (f := (229887/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_70 : ∀ n, Even n → 111880002 ≤ n → n ≤ 113860000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_70 ls_70 (by norm_num) (by norm_num) bnd_70

theorem bnd_71 : GBBound 113860002 115840000 1039 := by
  have hq : ∀ x ∈ QKo 174, x ≤ 1039 := take_le 174 1039 (by decide +kernel)
  have w0 : GBBound 113860002 114850000 1039 :=
    gbBound_of_owcheck (lo := 113858963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_71_0
  have w1 : GBBound 114850002 115840000 1039 :=
    gbBound_of_owcheck (lo := 114848963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_71_1
  have v1 : GBBound 113860002 115840000 1039 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_71 : (18 + 550479/1000000 : ℝ) ≤ Real.log ((113860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((113860002 : ℕ) : ℝ)) 18 (f := (550479/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_71 : (2 + 460247/500000 : ℝ) ≤ Real.log (18 + 550479/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 550479/1000000 : ℝ)) 2 (f := (460247/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_71 : ∀ n, Even n → 113860002 ≤ n → n ≤ 115840000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_71 ls_71 (by norm_num) (by norm_num) bnd_71

theorem bnd_72 : GBBound 115840002 117820000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 115840002 116830000 751 :=
    gbBound_of_owcheck (lo := 115839251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_72_0
  have w1 : GBBound 116830002 117820000 751 :=
    gbBound_of_owcheck (lo := 116829251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_72_1
  have v1 : GBBound 115840002 117820000 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_72 : (18 + 567719/1000000 : ℝ) ≤ Real.log ((115840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((115840002 : ℕ) : ℝ)) 18 (f := (567719/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_72 : (2 + 921423/1000000 : ℝ) ≤ Real.log (18 + 567719/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 567719/1000000 : ℝ)) 2 (f := (921423/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_72 : ∀ n, Even n → 115840002 ≤ n → n ≤ 117820000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_72 ls_72 (by norm_num) (by norm_num) bnd_72

theorem bnd_73 : GBBound 117820002 119800000 751 := by
  have hq : ∀ x ∈ QKo 132, x ≤ 751 := take_le 132 751 (by decide +kernel)
  have w0 : GBBound 117820002 118810000 751 :=
    gbBound_of_owcheck (lo := 117819251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_73_0
  have w1 : GBBound 118810002 119800000 751 :=
    gbBound_of_owcheck (lo := 118809251) (Wb := 495375) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_73_1
  have v1 : GBBound 117820002 119800000 751 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_73 : (18 + 584667/1000000 : ℝ) ≤ Real.log ((117820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((117820002 : ℕ) : ℝ)) 18 (f := (584667/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_73 : (2 + 184467/200000 : ℝ) ≤ Real.log (18 + 584667/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 584667/1000000 : ℝ)) 2 (f := (184467/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_73 : ∀ n, Even n → 117820002 ≤ n → n ≤ 119800000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_73 ls_73 (by norm_num) (by norm_num) bnd_73

theorem bnd_74 : GBBound 119800002 121780000 1051 := by
  have hq : ∀ x ∈ QKo 176, x ≤ 1051 := take_le 176 1051 (by decide +kernel)
  have w0 : GBBound 119800002 120790000 1051 :=
    gbBound_of_owcheck (lo := 119798951) (Wb := 495525) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_74_0
  have w1 : GBBound 120790002 121780000 1051 :=
    gbBound_of_owcheck (lo := 120788951) (Wb := 495525) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_74_1
  have v1 : GBBound 119800002 121780000 1051 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_74 : (18 + 601333/1000000 : ℝ) ≤ Real.log ((119800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((119800002 : ℕ) : ℝ)) 18 (f := (601333/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_74 : (2 + 28851/31250 : ℝ) ≤ Real.log (18 + 601333/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 601333/1000000 : ℝ)) 2 (f := (28851/31250 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_74 : ∀ n, Even n → 119800002 ≤ n → n ≤ 121780000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_74 ls_74 (by norm_num) (by norm_num) bnd_74

end LeanLab.GvLtR1989
