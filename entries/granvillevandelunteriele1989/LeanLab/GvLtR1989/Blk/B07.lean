module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W048
public import LeanLab.GvLtR1989.Win.W049
public import LeanLab.GvLtR1989.Win.W050
public import LeanLab.GvLtR1989.Win.W051
public import LeanLab.GvLtR1989.Win.W052
public import LeanLab.GvLtR1989.Win.W053
public import LeanLab.GvLtR1989.Win.W054
public import LeanLab.GvLtR1989.Win.W055
public import LeanLab.GvLtR1989.Win.W056

/-!
Blocks 105 to 119, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_105 : GBBound 181180002 183160000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 181180002 182170000 907 :=
    gbBound_of_owcheck (lo := 181179095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_105_0
  have w1 : GBBound 182170002 183160000 907 :=
    gbBound_of_owcheck (lo := 182169095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_105_1
  have v1 : GBBound 181180002 183160000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_105 : (19 + 3/200 : ℝ) ≤ Real.log ((181180002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((181180002 : ℕ) : ℝ)) 19 (f := (3/200 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_105 : (2 + 945227/1000000 : ℝ) ≤ Real.log (19 + 3/200 : ℝ) := by
  have h := le_log_of (x := (19 + 3/200 : ℝ)) 2 (f := (945227/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_105 : ∀ n, Even n → 181180002 ≤ n → n ≤ 183160000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_105 ls_105 (by norm_num) (by norm_num) bnd_105

theorem bnd_106 : GBBound 183160002 185140000 1033 := by
  have hq : ∀ x ∈ QKo 173, x ≤ 1033 := take_le 173 1033 (by decide +kernel)
  have w0 : GBBound 183160002 184150000 1033 :=
    gbBound_of_owcheck (lo := 183158969) (Wb := 495516) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_106_0
  have w1 : GBBound 184150002 185140000 1033 :=
    gbBound_of_owcheck (lo := 184148969) (Wb := 495516) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_106_1
  have v1 : GBBound 183160002 185140000 1033 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_106 : (19 + 25869/1000000 : ℝ) ≤ Real.log ((183160002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((183160002 : ℕ) : ℝ)) 19 (f := (25869/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_106 : (2 + 472899/500000 : ℝ) ≤ Real.log (19 + 25869/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 25869/1000000 : ℝ)) 2 (f := (472899/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_106 : ∀ n, Even n → 183160002 ≤ n → n ≤ 185140000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_106 ls_106 (by norm_num) (by norm_num) bnd_106

theorem bnd_107 : GBBound 185140002 187120000 859 := by
  have hq : ∀ x ∈ QKo 148, x ≤ 859 := take_le 148 859 (by decide +kernel)
  have w0 : GBBound 185140002 186130000 859 :=
    gbBound_of_owcheck (lo := 185139143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_107_0
  have w1 : GBBound 186130002 187120000 859 :=
    gbBound_of_owcheck (lo := 186129143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_107_1
  have v1 : GBBound 185140002 187120000 859 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_107 : (19 + 36621/1000000 : ℝ) ≤ Real.log ((185140002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((185140002 : ℕ) : ℝ)) 19 (f := (36621/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_107 : (2 + 946363/1000000 : ℝ) ≤ Real.log (19 + 36621/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 36621/1000000 : ℝ)) 2 (f := (946363/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_107 : ∀ n, Even n → 185140002 ≤ n → n ≤ 187120000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_107 ls_107 (by norm_num) (by norm_num) bnd_107

theorem bnd_108 : GBBound 187120002 189100000 1321 := by
  have hq : ∀ x ∈ QKo 215, x ≤ 1321 := take_le 215 1321 (by decide +kernel)
  have w0 : GBBound 187120002 188110000 1321 :=
    gbBound_of_owcheck (lo := 187118681) (Wb := 495660) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_108_0
  have w1 : GBBound 188110002 189100000 1321 :=
    gbBound_of_owcheck (lo := 188108681) (Wb := 495660) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_108_1
  have v1 : GBBound 187120002 189100000 1321 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_108 : (19 + 47259/1000000 : ℝ) ≤ Real.log ((187120002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((187120002 : ℕ) : ℝ)) 19 (f := (47259/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_108 : (2 + 473461/500000 : ℝ) ≤ Real.log (19 + 47259/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 47259/1000000 : ℝ)) 2 (f := (473461/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_108 : ∀ n, Even n → 187120002 ≤ n → n ≤ 189100000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_108 ls_108 (by norm_num) (by norm_num) bnd_108

theorem bnd_109 : GBBound 189100002 191080000 757 := by
  have hq : ∀ x ∈ QKo 133, x ≤ 757 := take_le 133 757 (by decide +kernel)
  have w0 : GBBound 189100002 190090000 757 :=
    gbBound_of_owcheck (lo := 189099245) (Wb := 495378) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_109_0
  have w1 : GBBound 190090002 191080000 757 :=
    gbBound_of_owcheck (lo := 190089245) (Wb := 495378) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_109_1
  have v1 : GBBound 189100002 191080000 757 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_109 : (19 + 11557/200000 : ℝ) ≤ Real.log ((189100002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((189100002 : ℕ) : ℝ)) 19 (f := (11557/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_109 : (2 + 473737/500000 : ℝ) ≤ Real.log (19 + 11557/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 11557/200000 : ℝ)) 2 (f := (473737/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_109 : ∀ n, Even n → 189100002 ≤ n → n ≤ 191080000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_109 ls_109 (by norm_num) (by norm_num) bnd_109

theorem bnd_110 : GBBound 191080002 193060000 911 := by
  have hq : ∀ x ∈ QKo 155, x ≤ 911 := take_le 155 911 (by decide +kernel)
  have w0 : GBBound 191080002 192070000 911 :=
    gbBound_of_owcheck (lo := 191079091) (Wb := 495455) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_110_0
  have w1 : GBBound 192070002 193060000 911 :=
    gbBound_of_owcheck (lo := 192069091) (Wb := 495455) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_110_1
  have v1 : GBBound 191080002 193060000 911 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_110 : (19 + 68201/1000000 : ℝ) ≤ Real.log ((191080002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((191080002 : ℕ) : ℝ)) 19 (f := (68201/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_110 : (2 + 948021/1000000 : ℝ) ≤ Real.log (19 + 68201/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 68201/1000000 : ℝ)) 2 (f := (948021/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_110 : ∀ n, Even n → 191080002 ≤ n → n ≤ 193060000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_110 ls_110 (by norm_num) (by norm_num) bnd_110

theorem bnd_111 : GBBound 193060002 195040000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 193060002 194050000 991 :=
    gbBound_of_owcheck (lo := 193059011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_111_0
  have w1 : GBBound 194050002 195040000 991 :=
    gbBound_of_owcheck (lo := 194049011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_111_1
  have v1 : GBBound 193060002 195040000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_111 : (19 + 7851/100000 : ℝ) ≤ Real.log ((193060002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((193060002 : ℕ) : ℝ)) 19 (f := (7851/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_111 : (2 + 948561/1000000 : ℝ) ≤ Real.log (19 + 7851/100000 : ℝ) := by
  have h := le_log_of (x := (19 + 7851/100000 : ℝ)) 2 (f := (948561/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_111 : ∀ n, Even n → 193060002 ≤ n → n ≤ 195040000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_111 ls_111 (by norm_num) (by norm_num) bnd_111

theorem bnd_112 : GBBound 195040002 197020000 773 := by
  have hq : ∀ x ∈ QKo 136, x ≤ 773 := take_le 136 773 (by decide +kernel)
  have w0 : GBBound 195040002 196030000 773 :=
    gbBound_of_owcheck (lo := 195039229) (Wb := 495386) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_112_0
  have w1 : GBBound 196030002 197020000 773 :=
    gbBound_of_owcheck (lo := 196029229) (Wb := 495386) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_112_1
  have v1 : GBBound 195040002 197020000 773 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_112 : (19 + 44357/500000 : ℝ) ≤ Real.log ((195040002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((195040002 : ℕ) : ℝ)) 19 (f := (44357/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_112 : (2 + 118637/125000 : ℝ) ≤ Real.log (19 + 44357/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 44357/500000 : ℝ)) 2 (f := (118637/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_112 : ∀ n, Even n → 195040002 ≤ n → n ≤ 197020000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_112 ls_112 (by norm_num) (by norm_num) bnd_112

theorem bnd_113 : GBBound 197020002 199000000 829 := by
  have hq : ∀ x ∈ QKo 144, x ≤ 829 := take_le 144 829 (by decide +kernel)
  have w0 : GBBound 197020002 198010000 829 :=
    gbBound_of_owcheck (lo := 197019173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_113_0
  have w1 : GBBound 198010002 199000000 829 :=
    gbBound_of_owcheck (lo := 198009173) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_113_1
  have v1 : GBBound 197020002 199000000 829 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_113 : (19 + 49407/500000 : ℝ) ≤ Real.log ((197020002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((197020002 : ℕ) : ℝ)) 19 (f := (49407/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_113 : (2 + 7597/8000 : ℝ) ≤ Real.log (19 + 49407/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 49407/500000 : ℝ)) 2 (f := (7597/8000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_113 : ∀ n, Even n → 197020002 ≤ n → n ≤ 199000000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_113 ls_113 (by norm_num) (by norm_num) bnd_113

theorem bnd_114 : GBBound 199000002 200980000 863 := by
  have hq : ∀ x ∈ QKo 149, x ≤ 863 := take_le 149 863 (by decide +kernel)
  have w0 : GBBound 199000002 199990000 863 :=
    gbBound_of_owcheck (lo := 198999139) (Wb := 495431) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_114_0
  have w1 : GBBound 199990002 200980000 863 :=
    gbBound_of_owcheck (lo := 199989139) (Wb := 495431) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_114_1
  have v1 : GBBound 199000002 200980000 863 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_114 : (19 + 54407/500000 : ℝ) ≤ Real.log ((199000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((199000002 : ℕ) : ℝ)) 19 (f := (54407/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_114 : (2 + 237537/250000 : ℝ) ≤ Real.log (19 + 54407/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 54407/500000 : ℝ)) 2 (f := (237537/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_114 : ∀ n, Even n → 199000002 ≤ n → n ≤ 200980000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_114 ls_114 (by norm_num) (by norm_num) bnd_114

theorem bnd_115 : GBBound 200980002 202960000 1087 := by
  have hq : ∀ x ∈ QKo 180, x ≤ 1087 := take_le 180 1087 (by decide +kernel)
  have w0 : GBBound 200980002 201970000 1087 :=
    gbBound_of_owcheck (lo := 200978915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_115_0
  have w1 : GBBound 201970002 202960000 1087 :=
    gbBound_of_owcheck (lo := 201968915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_115_1
  have v1 : GBBound 200980002 202960000 1087 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_115 : (19 + 59357/500000 : ℝ) ≤ Real.log ((200980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((200980002 : ℕ) : ℝ)) 19 (f := (59357/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_115 : (2 + 475333/500000 : ℝ) ≤ Real.log (19 + 59357/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 59357/500000 : ℝ)) 2 (f := (475333/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_115 : ∀ n, Even n → 200980002 ≤ n → n ≤ 202960000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_115 ls_115 (by norm_num) (by norm_num) bnd_115

theorem bnd_116 : GBBound 202960002 204940000 1021 := by
  have hq : ∀ x ∈ QKo 171, x ≤ 1021 := take_le 171 1021 (by decide +kernel)
  have w0 : GBBound 202960002 203950000 1021 :=
    gbBound_of_owcheck (lo := 202958981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_116_0
  have w1 : GBBound 203950002 204940000 1021 :=
    gbBound_of_owcheck (lo := 203948981) (Wb := 495510) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_116_1
  have v1 : GBBound 202960002 204940000 1021 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_116 : (19 + 64259/500000 : ℝ) ≤ Real.log ((202960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((202960002 : ℕ) : ℝ)) 19 (f := (64259/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_116 : (2 + 951179/1000000 : ℝ) ≤ Real.log (19 + 64259/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 64259/500000 : ℝ)) 2 (f := (951179/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_116 : ∀ n, Even n → 202960002 ≤ n → n ≤ 204940000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_116 ls_116 (by norm_num) (by norm_num) bnd_116

theorem bnd_117 : GBBound 204940002 206920000 967 := by
  have hq : ∀ x ∈ QKo 162, x ≤ 967 := take_le 162 967 (by decide +kernel)
  have w0 : GBBound 204940002 205930000 967 :=
    gbBound_of_owcheck (lo := 204939035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_117_0
  have w1 : GBBound 205930002 206920000 967 :=
    gbBound_of_owcheck (lo := 205929035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_117_1
  have v1 : GBBound 204940002 206920000 967 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_117 : (19 + 69113/500000 : ℝ) ≤ Real.log ((204940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((204940002 : ℕ) : ℝ)) 19 (f := (69113/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_117 : (2 + 475843/500000 : ℝ) ≤ Real.log (19 + 69113/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 69113/500000 : ℝ)) 2 (f := (475843/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_117 : ∀ n, Even n → 204940002 ≤ n → n ≤ 206920000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_117 ls_117 (by norm_num) (by norm_num) bnd_117

theorem bnd_118 : GBBound 206920002 208900000 929 := by
  have hq : ∀ x ∈ QKo 157, x ≤ 929 := take_le 157 929 (by decide +kernel)
  have w0 : GBBound 206920002 207910000 929 :=
    gbBound_of_owcheck (lo := 206919073) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_118_0
  have w1 : GBBound 207910002 208900000 929 :=
    gbBound_of_owcheck (lo := 207909073) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_118_1
  have v1 : GBBound 206920002 208900000 929 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_118 : (19 + 147841/1000000 : ℝ) ≤ Real.log ((206920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((206920002 : ℕ) : ℝ)) 19 (f := (147841/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_118 : (2 + 238047/250000 : ℝ) ≤ Real.log (19 + 147841/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 147841/1000000 : ℝ)) 2 (f := (238047/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_118 : ∀ n, Even n → 206920002 ≤ n → n ≤ 208900000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_118 ls_118 (by norm_num) (by norm_num) bnd_118

theorem bnd_119 : GBBound 208900002 210880000 919 := by
  have hq : ∀ x ∈ QKo 156, x ≤ 919 := take_le 156 919 (by decide +kernel)
  have w0 : GBBound 208900002 209890000 919 :=
    gbBound_of_owcheck (lo := 208899083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_119_0
  have w1 : GBBound 209890002 210880000 919 :=
    gbBound_of_owcheck (lo := 209889083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_119_1
  have v1 : GBBound 208900002 210880000 919 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_119 : (19 + 31473/200000 : ℝ) ≤ Real.log ((208900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((208900002 : ℕ) : ℝ)) 19 (f := (31473/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_119 : (2 + 476343/500000 : ℝ) ≤ Real.log (19 + 31473/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 31473/200000 : ℝ)) 2 (f := (476343/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_119 : ∀ n, Even n → 208900002 ≤ n → n ≤ 210880000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_119 ls_119 (by norm_num) (by norm_num) bnd_119

end LeanLab.GvLtR1989
