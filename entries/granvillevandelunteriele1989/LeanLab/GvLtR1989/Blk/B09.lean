module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W063
public import LeanLab.GvLtR1989.Win.W064
public import LeanLab.GvLtR1989.Win.W065
public import LeanLab.GvLtR1989.Win.W066
public import LeanLab.GvLtR1989.Win.W067
public import LeanLab.GvLtR1989.Win.W068
public import LeanLab.GvLtR1989.Win.W069
public import LeanLab.GvLtR1989.Win.W070
public import LeanLab.GvLtR1989.Win.W071

/-!
Blocks 135 to 149, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_135 : GBBound 240580002 242560000 877 := by
  have hq : ∀ x ∈ QKo 150, x ≤ 877 := take_le 150 877 (by decide +kernel)
  have w0 : GBBound 240580002 241570000 877 :=
    gbBound_of_owcheck (lo := 240579125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_135_0
  have w1 : GBBound 241570002 242560000 877 :=
    gbBound_of_owcheck (lo := 241569125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_135_1
  have v1 : GBBound 240580002 242560000 877 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_135 : (19 + 149281/500000 : ℝ) ≤ Real.log ((240580002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((240580002 : ℕ) : ℝ)) 19 (f := (149281/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_135 : (2 + 960029/1000000 : ℝ) ≤ Real.log (19 + 149281/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 149281/500000 : ℝ)) 2 (f := (960029/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_135 : ∀ n, Even n → 240580002 ≤ n → n ≤ 242560000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_135 ls_135 (by norm_num) (by norm_num) bnd_135

theorem bnd_136 : GBBound 242560002 244540000 859 := by
  have hq : ∀ x ∈ QKo 148, x ≤ 859 := take_le 148 859 (by decide +kernel)
  have w0 : GBBound 242560002 243550000 859 :=
    gbBound_of_owcheck (lo := 242559143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_136_0
  have w1 : GBBound 243550002 244540000 859 :=
    gbBound_of_owcheck (lo := 243549143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_136_1
  have v1 : GBBound 242560002 244540000 859 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_136 : (19 + 153379/500000 : ℝ) ≤ Real.log ((242560002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((242560002 : ℕ) : ℝ)) 19 (f := (153379/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_136 : (2 + 480227/500000 : ℝ) ≤ Real.log (19 + 153379/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 153379/500000 : ℝ)) 2 (f := (480227/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_136 : ∀ n, Even n → 242560002 ≤ n → n ≤ 244540000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_136 ls_136 (by norm_num) (by norm_num) bnd_136

theorem bnd_137 : GBBound 244540002 246520000 1019 := by
  have hq : ∀ x ∈ QKo 170, x ≤ 1019 := take_le 170 1019 (by decide +kernel)
  have w0 : GBBound 244540002 245530000 1019 :=
    gbBound_of_owcheck (lo := 244538983) (Wb := 495509) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_137_0
  have w1 : GBBound 245530002 246520000 1019 :=
    gbBound_of_owcheck (lo := 245528983) (Wb := 495509) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_137_1
  have v1 : GBBound 244540002 246520000 1019 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_137 : (19 + 39361/125000 : ℝ) ≤ Real.log ((244540002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((244540002 : ℕ) : ℝ)) 19 (f := (39361/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_137 : (2 + 7687/8000 : ℝ) ≤ Real.log (19 + 39361/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 39361/125000 : ℝ)) 2 (f := (7687/8000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_137 : ∀ n, Even n → 244540002 ≤ n → n ≤ 246520000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_137 ls_137 (by norm_num) (by norm_num) bnd_137

theorem bnd_138 : GBBound 246520002 248500000 1123 := by
  have hq : ∀ x ∈ QKo 187, x ≤ 1123 := take_le 187 1123 (by decide +kernel)
  have w0 : GBBound 246520002 247510000 1123 :=
    gbBound_of_owcheck (lo := 246518879) (Wb := 495561) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_138_0
  have w1 : GBBound 247510002 248500000 1123 :=
    gbBound_of_owcheck (lo := 247508879) (Wb := 495561) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_138_1
  have v1 : GBBound 246520002 248500000 1123 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_138 : (19 + 40369/125000 : ℝ) ≤ Real.log ((246520002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((246520002 : ℕ) : ℝ)) 19 (f := (40369/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_138 : (2 + 240323/250000 : ℝ) ≤ Real.log (19 + 40369/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 40369/125000 : ℝ)) 2 (f := (240323/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_138 : ∀ n, Even n → 246520002 ≤ n → n ≤ 248500000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_138 ls_138 (by norm_num) (by norm_num) bnd_138

theorem bnd_139 : GBBound 248500002 250480000 1013 := by
  have hq : ∀ x ∈ QKo 169, x ≤ 1013 := take_le 169 1013 (by decide +kernel)
  have w0 : GBBound 248500002 249490000 1013 :=
    gbBound_of_owcheck (lo := 248498989) (Wb := 495506) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_139_0
  have w1 : GBBound 249490002 250480000 1013 :=
    gbBound_of_owcheck (lo := 249488989) (Wb := 495506) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_139_1
  have v1 : GBBound 248500002 250480000 1013 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_139 : (19 + 41369/125000 : ℝ) ≤ Real.log ((248500002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((248500002 : ℕ) : ℝ)) 19 (f := (41369/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_139 : (2 + 480853/500000 : ℝ) ≤ Real.log (19 + 41369/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 41369/125000 : ℝ)) 2 (f := (480853/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_139 : ∀ n, Even n → 248500002 ≤ n → n ≤ 250480000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_139 ls_139 (by norm_num) (by norm_num) bnd_139

theorem bnd_140 : GBBound 250480002 252460000 1009 := by
  have hq : ∀ x ∈ QKo 168, x ≤ 1009 := take_le 168 1009 (by decide +kernel)
  have w0 : GBBound 250480002 251470000 1009 :=
    gbBound_of_owcheck (lo := 250478993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_140_0
  have w1 : GBBound 251470002 252460000 1009 :=
    gbBound_of_owcheck (lo := 251468993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_140_1
  have v1 : GBBound 250480002 252460000 1009 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_140 : (19 + 42361/125000 : ℝ) ≤ Real.log ((250480002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((250480002 : ℕ) : ℝ)) 19 (f := (42361/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_140 : (2 + 240529/250000 : ℝ) ≤ Real.log (19 + 42361/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 42361/125000 : ℝ)) 2 (f := (240529/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_140 : ∀ n, Even n → 250480002 ≤ n → n ≤ 252460000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_140 ls_140 (by norm_num) (by norm_num) bnd_140

theorem bnd_141 : GBBound 252460002 254440000 877 := by
  have hq : ∀ x ∈ QKo 150, x ≤ 877 := take_le 150 877 (by decide +kernel)
  have w0 : GBBound 252460002 253450000 877 :=
    gbBound_of_owcheck (lo := 252459125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_141_0
  have w1 : GBBound 253450002 254440000 877 :=
    gbBound_of_owcheck (lo := 253449125) (Wb := 495438) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_141_1
  have v1 : GBBound 252460002 254440000 877 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_141 : (19 + 173381/500000 : ℝ) ≤ Real.log ((252460002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((252460002 : ℕ) : ℝ)) 19 (f := (173381/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_141 : (2 + 240631/250000 : ℝ) ≤ Real.log (19 + 173381/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 173381/500000 : ℝ)) 2 (f := (240631/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_141 : ∀ n, Even n → 252460002 ≤ n → n ≤ 254440000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_141 ls_141 (by norm_num) (by norm_num) bnd_141

theorem bnd_142 : GBBound 254440002 256420000 953 := by
  have hq : ∀ x ∈ QKo 161, x ≤ 953 := take_le 161 953 (by decide +kernel)
  have w0 : GBBound 254440002 255430000 953 :=
    gbBound_of_owcheck (lo := 254439049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_142_0
  have w1 : GBBound 255430002 256420000 953 :=
    gbBound_of_owcheck (lo := 255429049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_142_1
  have v1 : GBBound 254440002 256420000 953 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_142 : (19 + 177287/500000 : ℝ) ≤ Real.log ((254440002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((254440002 : ℕ) : ℝ)) 19 (f := (177287/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_142 : (2 + 962927/1000000 : ℝ) ≤ Real.log (19 + 177287/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 177287/500000 : ℝ)) 2 (f := (962927/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_142 : ∀ n, Even n → 254440002 ≤ n → n ≤ 256420000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_142 ls_142 (by norm_num) (by norm_num) bnd_142

theorem bnd_143 : GBBound 256420002 258400000 937 := by
  have hq : ∀ x ∈ QKo 158, x ≤ 937 := take_le 158 937 (by decide +kernel)
  have w0 : GBBound 256420002 257410000 937 :=
    gbBound_of_owcheck (lo := 256419065) (Wb := 495468) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_143_0
  have w1 : GBBound 257410002 258400000 937 :=
    gbBound_of_owcheck (lo := 257409065) (Wb := 495468) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_143_1
  have v1 : GBBound 256420002 258400000 937 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_143 : (19 + 181163/500000 : ℝ) ≤ Real.log ((256420002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((256420002 : ℕ) : ℝ)) 19 (f := (181163/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_143 : (2 + 15052/15625 : ℝ) ≤ Real.log (19 + 181163/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 181163/500000 : ℝ)) 2 (f := (15052/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_143 : ∀ n, Even n → 256420002 ≤ n → n ≤ 258400000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_143 ls_143 (by norm_num) (by norm_num) bnd_143

theorem bnd_144 : GBBound 258400002 260380000 997 := by
  have hq : ∀ x ∈ QKo 167, x ≤ 997 := take_le 167 997 (by decide +kernel)
  have w0 : GBBound 258400002 259390000 997 :=
    gbBound_of_owcheck (lo := 258399005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_144_0
  have w1 : GBBound 259390002 260380000 997 :=
    gbBound_of_owcheck (lo := 259389005) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_144_1
  have v1 : GBBound 258400002 260380000 997 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_144 : (19 + 185009/500000 : ℝ) ≤ Real.log ((258400002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((258400002 : ℕ) : ℝ)) 19 (f := (185009/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_144 : (2 + 38549/40000 : ℝ) ≤ Real.log (19 + 185009/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 185009/500000 : ℝ)) 2 (f := (38549/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_144 : ∀ n, Even n → 258400002 ≤ n → n ≤ 260380000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_144 ls_144 (by norm_num) (by norm_num) bnd_144

theorem bnd_145 : GBBound 260380002 262360000 1039 := by
  have hq : ∀ x ∈ QKo 174, x ≤ 1039 := take_le 174 1039 (by decide +kernel)
  have w0 : GBBound 260380002 261370000 1039 :=
    gbBound_of_owcheck (lo := 260378963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_145_0
  have w1 : GBBound 261370002 262360000 1039 :=
    gbBound_of_owcheck (lo := 261368963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_145_1
  have v1 : GBBound 260380002 262360000 1039 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_145 : (19 + 377651/1000000 : ℝ) ≤ Real.log ((260380002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((260380002 : ℕ) : ℝ)) 19 (f := (377651/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_145 : (2 + 964119/1000000 : ℝ) ≤ Real.log (19 + 377651/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 377651/1000000 : ℝ)) 2 (f := (964119/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_145 : ∀ n, Even n → 260380002 ≤ n → n ≤ 262360000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_145 ls_145 (by norm_num) (by norm_num) bnd_145

theorem bnd_146 : GBBound 262360002 264340000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 262360002 263350000 907 :=
    gbBound_of_owcheck (lo := 262359095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_146_0
  have w1 : GBBound 263350002 264340000 907 :=
    gbBound_of_owcheck (lo := 263349095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_146_1
  have v1 : GBBound 262360002 264340000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_146 : (19 + 385227/1000000 : ℝ) ≤ Real.log ((262360002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((262360002 : ℕ) : ℝ)) 19 (f := (385227/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_146 : (2 + 96451/100000 : ℝ) ≤ Real.log (19 + 385227/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 385227/1000000 : ℝ)) 2 (f := (96451/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_146 : ∀ n, Even n → 262360002 ≤ n → n ≤ 264340000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_146 ls_146 (by norm_num) (by norm_num) bnd_146

theorem bnd_147 : GBBound 264340002 266320000 853 := by
  have hq : ∀ x ∈ QKo 146, x ≤ 853 := take_le 146 853 (by decide +kernel)
  have w0 : GBBound 264340002 265330000 853 :=
    gbBound_of_owcheck (lo := 264339149) (Wb := 495426) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_147_0
  have w1 : GBBound 265330002 266320000 853 :=
    gbBound_of_owcheck (lo := 265329149) (Wb := 495426) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_147_1
  have v1 : GBBound 264340002 266320000 853 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_147 : (19 + 78549/200000 : ℝ) ≤ Real.log ((264340002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((264340002 : ℕ) : ℝ)) 19 (f := (78549/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_147 : (2 + 482449/500000 : ℝ) ≤ Real.log (19 + 78549/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 78549/200000 : ℝ)) 2 (f := (482449/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_147 : ∀ n, Even n → 264340002 ≤ n → n ≤ 266320000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_147 ls_147 (by norm_num) (by norm_num) bnd_147

theorem bnd_148 : GBBound 266320002 268300000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 266320002 267310000 907 :=
    gbBound_of_owcheck (lo := 266319095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_148_0
  have w1 : GBBound 267310002 268300000 907 :=
    gbBound_of_owcheck (lo := 267309095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_148_1
  have v1 : GBBound 266320002 268300000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_148 : (19 + 25013/62500 : ℝ) ≤ Real.log ((266320002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((266320002 : ℕ) : ℝ)) 19 (f := (25013/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_148 : (2 + 482641/500000 : ℝ) ≤ Real.log (19 + 25013/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 25013/62500 : ℝ)) 2 (f := (482641/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_148 : ∀ n, Even n → 266320002 ≤ n → n ≤ 268300000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_148 ls_148 (by norm_num) (by norm_num) bnd_148

theorem bnd_149 : GBBound 268300002 270280000 1063 := by
  have hq : ∀ x ∈ QKo 178, x ≤ 1063 := take_le 178 1063 (by decide +kernel)
  have w0 : GBBound 268300002 269290000 1063 :=
    gbBound_of_owcheck (lo := 268298939) (Wb := 495531) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_149_0
  have w1 : GBBound 269290002 270280000 1063 :=
    gbBound_of_owcheck (lo := 269288939) (Wb := 495531) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_149_1
  have v1 : GBBound 268300002 270280000 1063 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_149 : (19 + 81523/200000 : ℝ) ≤ Real.log ((268300002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((268300002 : ℕ) : ℝ)) 19 (f := (81523/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_149 : (2 + 30177/31250 : ℝ) ≤ Real.log (19 + 81523/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 81523/200000 : ℝ)) 2 (f := (30177/31250 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_149 : ∀ n, Even n → 268300002 ≤ n → n ≤ 270280000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_149 ls_149 (by norm_num) (by norm_num) bnd_149

end LeanLab.GvLtR1989
