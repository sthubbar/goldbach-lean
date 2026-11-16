module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W041
public import LeanLab.GvLtR1989.Win.W042
public import LeanLab.GvLtR1989.Win.W043
public import LeanLab.GvLtR1989.Win.W044
public import LeanLab.GvLtR1989.Win.W045
public import LeanLab.GvLtR1989.Win.W046
public import LeanLab.GvLtR1989.Win.W047
public import LeanLab.GvLtR1989.Win.W048

/-!
Blocks 90 to 104, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_90 : GBBound 151480002 153460000 947 := by
  have hq : ∀ x ∈ QKo 160, x ≤ 947 := take_le 160 947 (by decide +kernel)
  have w0 : GBBound 151480002 152470000 947 :=
    gbBound_of_owcheck (lo := 151479055) (Wb := 495473) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_90_0
  have w1 : GBBound 152470002 153460000 947 :=
    gbBound_of_owcheck (lo := 152469055) (Wb := 495473) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_90_1
  have v1 : GBBound 151480002 153460000 947 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_90 : (18 + 835963/1000000 : ℝ) ≤ Real.log ((151480002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((151480002 : ℕ) : ℝ)) 18 (f := (835963/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_90 : (2 + 467883/500000 : ℝ) ≤ Real.log (18 + 835963/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 835963/1000000 : ℝ)) 2 (f := (467883/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_90 : ∀ n, Even n → 151480002 ≤ n → n ≤ 153460000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_90 ls_90 (by norm_num) (by norm_num) bnd_90

theorem bnd_91 : GBBound 153460002 155440000 883 := by
  have hq : ∀ x ∈ QKo 152, x ≤ 883 := take_le 152 883 (by decide +kernel)
  have w0 : GBBound 153460002 154450000 883 :=
    gbBound_of_owcheck (lo := 153459119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_91_0
  have w1 : GBBound 154450002 155440000 883 :=
    gbBound_of_owcheck (lo := 154449119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_91_1
  have v1 : GBBound 153460002 155440000 883 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_91 : (18 + 848949/1000000 : ℝ) ≤ Real.log ((153460002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((153460002 : ℕ) : ℝ)) 18 (f := (848949/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_91 : (2 + 117057/125000 : ℝ) ≤ Real.log (18 + 848949/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 848949/1000000 : ℝ)) 2 (f := (117057/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_91 : ∀ n, Even n → 153460002 ≤ n → n ≤ 155440000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_91 ls_91 (by norm_num) (by norm_num) bnd_91

theorem bnd_92 : GBBound 155440002 157420000 919 := by
  have hq : ∀ x ∈ QKo 156, x ≤ 919 := take_le 156 919 (by decide +kernel)
  have w0 : GBBound 155440002 156430000 919 :=
    gbBound_of_owcheck (lo := 155439083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_92_0
  have w1 : GBBound 156430002 157420000 919 :=
    gbBound_of_owcheck (lo := 156429083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_92_1
  have v1 : GBBound 155440002 157420000 919 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_92 : (18 + 861769/1000000 : ℝ) ≤ Real.log ((155440002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((155440002 : ℕ) : ℝ)) 18 (f := (861769/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_92 : (2 + 58571/62500 : ℝ) ≤ Real.log (18 + 861769/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 861769/1000000 : ℝ)) 2 (f := (58571/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_92 : ∀ n, Even n → 155440002 ≤ n → n ≤ 157420000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_92 ls_92 (by norm_num) (by norm_num) bnd_92

theorem bnd_93 : GBBound 157420002 159400000 919 := by
  have hq : ∀ x ∈ QKo 156, x ≤ 919 := take_le 156 919 (by decide +kernel)
  have w0 : GBBound 157420002 158410000 919 :=
    gbBound_of_owcheck (lo := 157419083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_93_0
  have w1 : GBBound 158410002 159400000 919 :=
    gbBound_of_owcheck (lo := 158409083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_93_1
  have v1 : GBBound 157420002 159400000 919 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_93 : (18 + 437213/500000 : ℝ) ≤ Real.log ((157420002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((157420002 : ℕ) : ℝ)) 18 (f := (437213/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_93 : (2 + 468903/500000 : ℝ) ≤ Real.log (18 + 437213/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 437213/500000 : ℝ)) 2 (f := (468903/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_93 : ∀ n, Even n → 157420002 ≤ n → n ≤ 159400000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_93 ls_93 (by norm_num) (by norm_num) bnd_93

theorem bnd_94 : GBBound 159400002 161380000 919 := by
  have hq : ∀ x ∈ QKo 156, x ≤ 919 := take_le 156 919 (by decide +kernel)
  have w0 : GBBound 159400002 160390000 919 :=
    gbBound_of_owcheck (lo := 159399083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_94_0
  have w1 : GBBound 160390002 161380000 919 :=
    gbBound_of_owcheck (lo := 160389083) (Wb := 495459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_94_1
  have v1 : GBBound 159400002 161380000 919 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_94 : (18 + 443463/500000 : ℝ) ≤ Real.log ((159400002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((159400002 : ℕ) : ℝ)) 18 (f := (443463/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_94 : (2 + 234617/250000 : ℝ) ≤ Real.log (18 + 443463/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 443463/500000 : ℝ)) 2 (f := (234617/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_94 : ∀ n, Even n → 159400002 ≤ n → n ≤ 161380000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_94 ls_94 (by norm_num) (by norm_num) bnd_94

theorem bnd_95 : GBBound 161380002 163360000 967 := by
  have hq : ∀ x ∈ QKo 162, x ≤ 967 := take_le 162 967 (by decide +kernel)
  have w0 : GBBound 161380002 162370000 967 :=
    gbBound_of_owcheck (lo := 161379035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_95_0
  have w1 : GBBound 162370002 163360000 967 :=
    gbBound_of_owcheck (lo := 162369035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_95_1
  have v1 : GBBound 161380002 163360000 967 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_95 : (18 + 899271/1000000 : ℝ) ≤ Real.log ((161380002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((161380002 : ℕ) : ℝ)) 18 (f := (899271/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_95 : (2 + 469561/500000 : ℝ) ≤ Real.log (18 + 899271/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 899271/1000000 : ℝ)) 2 (f := (469561/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_95 : ∀ n, Even n → 161380002 ≤ n → n ≤ 163360000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_95 ls_95 (by norm_num) (by norm_num) bnd_95

theorem bnd_96 : GBBound 163360002 165340000 797 := by
  have hq : ∀ x ∈ QKo 138, x ≤ 797 := take_le 138 797 (by decide +kernel)
  have w0 : GBBound 163360002 164350000 797 :=
    gbBound_of_owcheck (lo := 163359205) (Wb := 495398) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_96_0
  have w1 : GBBound 164350002 165340000 797 :=
    gbBound_of_owcheck (lo := 164349205) (Wb := 495398) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_96_1
  have v1 : GBBound 163360002 165340000 797 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_96 : (18 + 182293/200000 : ℝ) ≤ Real.log ((163360002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((163360002 : ℕ) : ℝ)) 18 (f := (182293/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_96 : (2 + 939767/1000000 : ℝ) ≤ Real.log (18 + 182293/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 182293/200000 : ℝ)) 2 (f := (939767/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_96 : ∀ n, Even n → 163360002 ≤ n → n ≤ 165340000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_96 ls_96 (by norm_num) (by norm_num) bnd_96

theorem bnd_97 : GBBound 165340002 167320000 859 := by
  have hq : ∀ x ∈ QKo 148, x ≤ 859 := take_le 148 859 (by decide +kernel)
  have w0 : GBBound 165340002 166330000 859 :=
    gbBound_of_owcheck (lo := 165339143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_97_0
  have w1 : GBBound 166330002 167320000 859 :=
    gbBound_of_owcheck (lo := 166329143) (Wb := 495429) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_97_1
  have v1 : GBBound 165340002 167320000 859 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_97 : (18 + 923513/1000000 : ℝ) ≤ Real.log ((165340002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((165340002 : ℕ) : ℝ)) 18 (f := (923513/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_97 : (2 + 235101/250000 : ℝ) ≤ Real.log (18 + 923513/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 923513/1000000 : ℝ)) 2 (f := (235101/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_97 : ∀ n, Even n → 165340002 ≤ n → n ≤ 167320000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_97 ls_97 (by norm_num) (by norm_num) bnd_97

theorem bnd_98 : GBBound 167320002 169300000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 167320002 168310000 823 :=
    gbBound_of_owcheck (lo := 167319179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_98_0
  have w1 : GBBound 168310002 169300000 823 :=
    gbBound_of_owcheck (lo := 168309179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_98_1
  have v1 : GBBound 167320002 169300000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_98 : (18 + 935417/1000000 : ℝ) ≤ Real.log ((167320002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((167320002 : ℕ) : ℝ)) 18 (f := (935417/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_98 : (2 + 941033/1000000 : ℝ) ≤ Real.log (18 + 935417/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 935417/1000000 : ℝ)) 2 (f := (941033/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_98 : ∀ n, Even n → 167320002 ≤ n → n ≤ 169300000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_98 ls_98 (by norm_num) (by norm_num) bnd_98

theorem bnd_99 : GBBound 169300002 171280000 887 := by
  have hq : ∀ x ∈ QKo 153, x ≤ 887 := take_le 153 887 (by decide +kernel)
  have w0 : GBBound 169300002 170290000 887 :=
    gbBound_of_owcheck (lo := 169299115) (Wb := 495443) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_99_0
  have w1 : GBBound 170290002 171280000 887 :=
    gbBound_of_owcheck (lo := 170289115) (Wb := 495443) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_99_1
  have v1 : GBBound 169300002 171280000 887 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_99 : (18 + 947181/1000000 : ℝ) ≤ Real.log ((169300002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((169300002 : ℕ) : ℝ)) 18 (f := (947181/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_99 : (2 + 470827/500000 : ℝ) ≤ Real.log (18 + 947181/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 947181/1000000 : ℝ)) 2 (f := (470827/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_99 : ∀ n, Even n → 169300002 ≤ n → n ≤ 171280000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_99 ls_99 (by norm_num) (by norm_num) bnd_99

theorem bnd_100 : GBBound 171280002 173260000 907 := by
  have hq : ∀ x ∈ QKo 154, x ≤ 907 := take_le 154 907 (by decide +kernel)
  have w0 : GBBound 171280002 172270000 907 :=
    gbBound_of_owcheck (lo := 171279095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_100_0
  have w1 : GBBound 172270002 173260000 907 :=
    gbBound_of_owcheck (lo := 172269095) (Wb := 495453) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_100_1
  have v1 : GBBound 171280002 173260000 907 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_100 : (18 + 958809/1000000 : ℝ) ≤ Real.log ((171280002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((171280002 : ℕ) : ℝ)) 18 (f := (958809/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_100 : (2 + 942267/1000000 : ℝ) ≤ Real.log (18 + 958809/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 958809/1000000 : ℝ)) 2 (f := (942267/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_100 : ∀ n, Even n → 171280002 ≤ n → n ≤ 173260000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_100 ls_100 (by norm_num) (by norm_num) bnd_100

theorem bnd_101 : GBBound 173260002 175240000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 173260002 174250000 823 :=
    gbBound_of_owcheck (lo := 173259179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_101_0
  have w1 : GBBound 174250002 175240000 823 :=
    gbBound_of_owcheck (lo := 174249179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_101_1
  have v1 : GBBound 173260002 175240000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_101 : (18 + 485151/500000 : ℝ) ≤ Real.log ((173260002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((173260002 : ℕ) : ℝ)) 18 (f := (485151/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_101 : (2 + 942873/1000000 : ℝ) ≤ Real.log (18 + 485151/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 485151/500000 : ℝ)) 2 (f := (942873/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_101 : ∀ n, Even n → 173260002 ≤ n → n ≤ 175240000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_101 ls_101 (by norm_num) (by norm_num) bnd_101

theorem bnd_102 : GBBound 175240002 177220000 967 := by
  have hq : ∀ x ∈ QKo 162, x ≤ 967 := take_le 162 967 (by decide +kernel)
  have w0 : GBBound 175240002 176230000 967 :=
    gbBound_of_owcheck (lo := 175239035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_102_0
  have w1 : GBBound 176230002 177220000 967 :=
    gbBound_of_owcheck (lo := 176229035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_102_1
  have v1 : GBBound 175240002 177220000 967 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_102 : (18 + 490833/500000 : ℝ) ≤ Real.log ((175240002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((175240002 : ℕ) : ℝ)) 18 (f := (490833/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_102 : (2 + 58967/62500 : ℝ) ≤ Real.log (18 + 490833/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 490833/500000 : ℝ)) 2 (f := (58967/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_102 : ∀ n, Even n → 175240002 ≤ n → n ≤ 177220000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_102 ls_102 (by norm_num) (by norm_num) bnd_102

theorem bnd_103 : GBBound 177220002 179200000 1087 := by
  have hq : ∀ x ∈ QKo 180, x ≤ 1087 := take_le 180 1087 (by decide +kernel)
  have w0 : GBBound 177220002 178210000 1087 :=
    gbBound_of_owcheck (lo := 177218915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_103_0
  have w1 : GBBound 178210002 179200000 1087 :=
    gbBound_of_owcheck (lo := 178208915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_103_1
  have v1 : GBBound 177220002 179200000 1087 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_103 : (18 + 992901/1000000 : ℝ) ≤ Real.log ((177220002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((177220002 : ℕ) : ℝ)) 18 (f := (992901/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_103 : (2 + 14751/15625 : ℝ) ≤ Real.log (18 + 992901/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 992901/1000000 : ℝ)) 2 (f := (14751/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_103 : ∀ n, Even n → 177220002 ≤ n → n ≤ 179200000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_103 ls_103 (by norm_num) (by norm_num) bnd_103

theorem bnd_104 : GBBound 179200002 181180000 1153 := by
  have hq : ∀ x ∈ QKo 190, x ≤ 1153 := take_le 190 1153 (by decide +kernel)
  have w0 : GBBound 179200002 180190000 1153 :=
    gbBound_of_owcheck (lo := 179198849) (Wb := 495576) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_104_0
  have w1 : GBBound 180190002 181180000 1153 :=
    gbBound_of_owcheck (lo := 180188849) (Wb := 495576) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_104_1
  have v1 : GBBound 179200002 181180000 1153 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_104 : (19 + 1003/250000 : ℝ) ≤ Real.log ((179200002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((179200002 : ℕ) : ℝ)) 19 (f := (1003/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_104 : (2 + 944649/1000000 : ℝ) ≤ Real.log (19 + 1003/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 1003/250000 : ℝ)) 2 (f := (944649/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_104 : ∀ n, Even n → 179200002 ≤ n → n ≤ 181180000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_104 ls_104 (by norm_num) (by norm_num) bnd_104

end LeanLab.GvLtR1989
