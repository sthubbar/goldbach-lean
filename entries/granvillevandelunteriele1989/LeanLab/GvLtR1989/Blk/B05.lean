module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Win.W033
public import LeanLab.GvLtR1989.Win.W034
public import LeanLab.GvLtR1989.Win.W035
public import LeanLab.GvLtR1989.Win.W036
public import LeanLab.GvLtR1989.Win.W037
public import LeanLab.GvLtR1989.Win.W038
public import LeanLab.GvLtR1989.Win.W039
public import LeanLab.GvLtR1989.Win.W040
public import LeanLab.GvLtR1989.Win.W041

/-!
Blocks 75 to 89, generated: for each block the window checks are joined to a bound
on the least Goldbach prime, and certified lower bounds for log n and log log n turn it into
the ratio bound with constant 1.603.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem bnd_75 : GBBound 121780002 123760000 811 := by
  have hq : ∀ x ∈ QKo 140, x ≤ 811 := take_le 140 811 (by decide +kernel)
  have w0 : GBBound 121780002 122770000 811 :=
    gbBound_of_owcheck (lo := 121779191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_75_0
  have w1 : GBBound 122770002 123760000 811 :=
    gbBound_of_owcheck (lo := 122769191) (Wb := 495405) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_75_1
  have v1 : GBBound 121780002 123760000 811 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_75 : (18 + 24709/40000 : ℝ) ≤ Real.log ((121780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((121780002 : ℕ) : ℝ)) 18 (f := (24709/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_75 : (2 + 924113/1000000 : ℝ) ≤ Real.log (18 + 24709/40000 : ℝ) := by
  have h := le_log_of (x := (18 + 24709/40000 : ℝ)) 2 (f := (924113/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_75 : ∀ n, Even n → 121780002 ≤ n → n ≤ 123760000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_75 ls_75 (by norm_num) (by norm_num) bnd_75

theorem bnd_76 : GBBound 123760002 125740000 953 := by
  have hq : ∀ x ∈ QKo 161, x ≤ 953 := take_le 161 953 (by decide +kernel)
  have w0 : GBBound 123760002 124750000 953 :=
    gbBound_of_owcheck (lo := 123759049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_76_0
  have w1 : GBBound 124750002 125740000 953 :=
    gbBound_of_owcheck (lo := 124749049) (Wb := 495476) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_76_1
  have v1 : GBBound 123760002 125740000 953 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_76 : (18 + 633853/1000000 : ℝ) ≤ Real.log ((123760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((123760002 : ℕ) : ℝ)) 18 (f := (633853/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_76 : (2 + 462489/500000 : ℝ) ≤ Real.log (18 + 633853/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 633853/1000000 : ℝ)) 2 (f := (462489/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_76 : ∀ n, Even n → 123760002 ≤ n → n ≤ 125740000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_76 ls_76 (by norm_num) (by norm_num) bnd_76

theorem bnd_77 : GBBound 125740002 127720000 1009 := by
  have hq : ∀ x ∈ QKo 168, x ≤ 1009 := take_le 168 1009 (by decide +kernel)
  have w0 : GBBound 125740002 126730000 1009 :=
    gbBound_of_owcheck (lo := 125738993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_77_0
  have w1 : GBBound 126730002 127720000 1009 :=
    gbBound_of_owcheck (lo := 126728993) (Wb := 495504) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_77_1
  have v1 : GBBound 125740002 127720000 1009 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_77 : (18 + 25989/40000 : ℝ) ≤ Real.log ((125740002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((125740002 : ℕ) : ℝ)) 18 (f := (25989/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_77 : (2 + 92583/100000 : ℝ) ≤ Real.log (18 + 25989/40000 : ℝ) := by
  have h := le_log_of (x := (18 + 25989/40000 : ℝ)) 2 (f := (92583/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_77 : ∀ n, Even n → 125740002 ≤ n → n ≤ 127720000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_77 ls_77 (by norm_num) (by norm_num) bnd_77

theorem bnd_78 : GBBound 127720002 129700000 881 := by
  have hq : ∀ x ∈ QKo 151, x ≤ 881 := take_le 151 881 (by decide +kernel)
  have w0 : GBBound 127720002 128710000 881 :=
    gbBound_of_owcheck (lo := 127719121) (Wb := 495440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_78_0
  have w1 : GBBound 128710002 129700000 881 :=
    gbBound_of_owcheck (lo := 128709121) (Wb := 495440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_78_1
  have v1 : GBBound 127720002 129700000 881 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_78 : (18 + 665349/1000000 : ℝ) ≤ Real.log ((127720002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((127720002 : ℕ) : ℝ)) 18 (f := (665349/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_78 : (2 + 926667/1000000 : ℝ) ≤ Real.log (18 + 665349/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 665349/1000000 : ℝ)) 2 (f := (926667/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_78 : ∀ n, Even n → 127720002 ≤ n → n ≤ 129700000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_78 ls_78 (by norm_num) (by norm_num) bnd_78

theorem bnd_79 : GBBound 129700002 131680000 881 := by
  have hq : ∀ x ∈ QKo 151, x ≤ 881 := take_le 151 881 (by decide +kernel)
  have w0 : GBBound 129700002 130690000 881 :=
    gbBound_of_owcheck (lo := 129699121) (Wb := 495440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_79_0
  have w1 : GBBound 130690002 131680000 881 :=
    gbBound_of_owcheck (lo := 130689121) (Wb := 495440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_79_1
  have v1 : GBBound 129700002 131680000 881 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_79 : (18 + 680733/1000000 : ℝ) ≤ Real.log ((129700002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((129700002 : ℕ) : ℝ)) 18 (f := (680733/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_79 : (2 + 927491/1000000 : ℝ) ≤ Real.log (18 + 680733/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 680733/1000000 : ℝ)) 2 (f := (927491/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_79 : ∀ n, Even n → 129700002 ≤ n → n ≤ 131680000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_79 ls_79 (by norm_num) (by norm_num) bnd_79

theorem bnd_80 : GBBound 131680002 133660000 883 := by
  have hq : ∀ x ∈ QKo 152, x ≤ 883 := take_le 152 883 (by decide +kernel)
  have w0 : GBBound 131680002 132670000 883 :=
    gbBound_of_owcheck (lo := 131679119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_80_0
  have w1 : GBBound 132670002 133660000 883 :=
    gbBound_of_owcheck (lo := 132669119) (Wb := 495441) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_80_1
  have v1 : GBBound 131680002 133660000 883 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_80 : (18 + 173971/250000 : ℝ) ≤ Real.log ((131680002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((131680002 : ℕ) : ℝ)) 18 (f := (173971/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_80 : (2 + 464151/500000 : ℝ) ≤ Real.log (18 + 173971/250000 : ℝ) := by
  have h := le_log_of (x := (18 + 173971/250000 : ℝ)) 2 (f := (464151/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_80 : ∀ n, Even n → 131680002 ≤ n → n ≤ 133660000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_80 ls_80 (by norm_num) (by norm_num) bnd_80

theorem bnd_81 : GBBound 133660002 135640000 857 := by
  have hq : ∀ x ∈ QKo 147, x ≤ 857 := take_le 147 857 (by decide +kernel)
  have w0 : GBBound 133660002 134650000 857 :=
    gbBound_of_owcheck (lo := 133659145) (Wb := 495428) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_81_0
  have w1 : GBBound 134650002 135640000 857 :=
    gbBound_of_owcheck (lo := 134649145) (Wb := 495428) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_81_1
  have v1 : GBBound 133660002 135640000 857 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_81 : (18 + 88851/125000 : ℝ) ≤ Real.log ((133660002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((133660002 : ℕ) : ℝ)) 18 (f := (88851/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_81 : (2 + 9291/10000 : ℝ) ≤ Real.log (18 + 88851/125000 : ℝ) := by
  have h := le_log_of (x := (18 + 88851/125000 : ℝ)) 2 (f := (9291/10000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_81 : ∀ n, Even n → 133660002 ≤ n → n ≤ 135640000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_81 ls_81 (by norm_num) (by norm_num) bnd_81

theorem bnd_82 : GBBound 135640002 137620000 971 := by
  have hq : ∀ x ∈ QKo 163, x ≤ 971 := take_le 163 971 (by decide +kernel)
  have w0 : GBBound 135640002 136630000 971 :=
    gbBound_of_owcheck (lo := 135639031) (Wb := 495485) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_82_0
  have w1 : GBBound 136630002 137620000 971 :=
    gbBound_of_owcheck (lo := 136629031) (Wb := 495485) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_82_1
  have v1 : GBBound 135640002 137620000 971 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_82 : (18 + 725513/1000000 : ℝ) ≤ Real.log ((135640002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((135640002 : ℕ) : ℝ)) 18 (f := (725513/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_82 : (2 + 185977/200000 : ℝ) ≤ Real.log (18 + 725513/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 725513/1000000 : ℝ)) 2 (f := (185977/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_82 : ∀ n, Even n → 135640002 ≤ n → n ≤ 137620000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_82 ls_82 (by norm_num) (by norm_num) bnd_82

theorem bnd_83 : GBBound 137620002 139600000 839 := by
  have hq : ∀ x ∈ QKo 145, x ≤ 839 := take_le 145 839 (by decide +kernel)
  have w0 : GBBound 137620002 138610000 839 :=
    gbBound_of_owcheck (lo := 137619163) (Wb := 495419) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_83_0
  have w1 : GBBound 138610002 139600000 839 :=
    gbBound_of_owcheck (lo := 138609163) (Wb := 495419) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_83_1
  have v1 : GBBound 137620002 139600000 839 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_83 : (18 + 148001/200000 : ℝ) ≤ Real.log ((137620002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((137620002 : ℕ) : ℝ)) 18 (f := (148001/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_83 : (2 + 930659/1000000 : ℝ) ≤ Real.log (18 + 148001/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 148001/200000 : ℝ)) 2 (f := (930659/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_83 : ∀ n, Even n → 137620002 ≤ n → n ≤ 139600000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_83 ls_83 (by norm_num) (by norm_num) bnd_83

theorem bnd_84 : GBBound 139600002 141580000 823 := by
  have hq : ∀ x ∈ QKo 142, x ≤ 823 := take_le 142 823 (by decide +kernel)
  have w0 : GBBound 139600002 140590000 823 :=
    gbBound_of_owcheck (lo := 139599179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_84_0
  have w1 : GBBound 140590002 141580000 823 :=
    gbBound_of_owcheck (lo := 140589179) (Wb := 495411) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_84_1
  have v1 : GBBound 139600002 141580000 823 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_84 : (18 + 75429/100000 : ℝ) ≤ Real.log ((139600002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((139600002 : ℕ) : ℝ)) 18 (f := (75429/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_84 : (2 + 931421/1000000 : ℝ) ≤ Real.log (18 + 75429/100000 : ℝ) := by
  have h := le_log_of (x := (18 + 75429/100000 : ℝ)) 2 (f := (931421/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_84 : ∀ n, Even n → 139600002 ≤ n → n ≤ 141580000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_84 ls_84 (by norm_num) (by norm_num) bnd_84

theorem bnd_85 : GBBound 141580002 143560000 1087 := by
  have hq : ∀ x ∈ QKo 180, x ≤ 1087 := take_le 180 1087 (by decide +kernel)
  have w0 : GBBound 141580002 142570000 1087 :=
    gbBound_of_owcheck (lo := 141578915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_85_0
  have w1 : GBBound 142570002 143560000 1087 :=
    gbBound_of_owcheck (lo := 142568915) (Wb := 495543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_85_1
  have v1 : GBBound 141580002 143560000 1087 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_85 : (18 + 384187/500000 : ℝ) ≤ Real.log ((141580002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((141580002 : ℕ) : ℝ)) 18 (f := (384187/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_85 : (2 + 233043/250000 : ℝ) ≤ Real.log (18 + 384187/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 384187/500000 : ℝ)) 2 (f := (233043/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_85 : ∀ n, Even n → 141580002 ≤ n → n ≤ 143560000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_85 ls_85 (by norm_num) (by norm_num) bnd_85

theorem bnd_86 : GBBound 143560002 145540000 991 := by
  have hq : ∀ x ∈ QKo 166, x ≤ 991 := take_le 166 991 (by decide +kernel)
  have w0 : GBBound 143560002 144550000 991 :=
    gbBound_of_owcheck (lo := 143559011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_86_0
  have w1 : GBBound 144550002 145540000 991 :=
    gbBound_of_owcheck (lo := 144549011) (Wb := 495495) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_86_1
  have v1 : GBBound 143560002 145540000 991 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_86 : (18 + 391131/500000 : ℝ) ≤ Real.log ((143560002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((143560002 : ℕ) : ℝ)) 18 (f := (391131/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_86 : (2 + 932911/1000000 : ℝ) ≤ Real.log (18 + 391131/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 391131/500000 : ℝ)) 2 (f := (932911/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_86 : ∀ n, Even n → 143560002 ≤ n → n ≤ 145540000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_86 ls_86 (by norm_num) (by norm_num) bnd_86

theorem bnd_87 : GBBound 145540002 147520000 1039 := by
  have hq : ∀ x ∈ QKo 174, x ≤ 1039 := take_le 174 1039 (by decide +kernel)
  have w0 : GBBound 145540002 146530000 1039 :=
    gbBound_of_owcheck (lo := 145538963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_87_0
  have w1 : GBBound 146530002 147520000 1039 :=
    gbBound_of_owcheck (lo := 146528963) (Wb := 495519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_87_1
  have v1 : GBBound 145540002 147520000 1039 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_87 : (18 + 19899/25000 : ℝ) ≤ Real.log ((145540002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((145540002 : ℕ) : ℝ)) 18 (f := (19899/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_87 : (2 + 23341/25000 : ℝ) ≤ Real.log (18 + 19899/25000 : ℝ) := by
  have h := le_log_of (x := (18 + 19899/25000 : ℝ)) 2 (f := (23341/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_87 : ∀ n, Even n → 145540002 ≤ n → n ≤ 147520000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_87 ls_87 (by norm_num) (by norm_num) bnd_87

theorem bnd_88 : GBBound 147520002 149500000 967 := by
  have hq : ∀ x ∈ QKo 162, x ≤ 967 := take_le 162 967 (by decide +kernel)
  have w0 : GBBound 147520002 148510000 967 :=
    gbBound_of_owcheck (lo := 147519035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_88_0
  have w1 : GBBound 148510002 149500000 967 :=
    gbBound_of_owcheck (lo := 148509035) (Wb := 495483) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_88_1
  have v1 : GBBound 147520002 149500000 967 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_88 : (18 + 809473/1000000 : ℝ) ≤ Real.log ((147520002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((147520002 : ℕ) : ℝ)) 18 (f := (809473/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_88 : (2 + 934359/1000000 : ℝ) ≤ Real.log (18 + 809473/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 809473/1000000 : ℝ)) 2 (f := (934359/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_88 : ∀ n, Even n → 147520002 ≤ n → n ≤ 149500000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_88 ls_88 (by norm_num) (by norm_num) bnd_88

theorem bnd_89 : GBBound 149500002 151480000 911 := by
  have hq : ∀ x ∈ QKo 155, x ≤ 911 := take_le 155 911 (by decide +kernel)
  have w0 : GBBound 149500002 150490000 911 :=
    gbBound_of_owcheck (lo := 149499091) (Wb := 495455) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_89_0
  have w1 : GBBound 150490002 151480000 911 :=
    gbBound_of_owcheck (lo := 150489091) (Wb := 495455) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_89_1
  have v1 : GBBound 149500002 151480000 911 := GBBound.join w0 w1 (by norm_num) (by decide)
  exact v1

theorem lr_89 : (18 + 164561/200000 : ℝ) ≤ Real.log ((149500002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((149500002 : ℕ) : ℝ)) 18 (f := (164561/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_89 : (2 + 233767/250000 : ℝ) ≤ Real.log (18 + 164561/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 164561/200000 : ℝ)) 2 (f := (233767/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r_89 : ∀ n, Even n → 149500002 ≤ n → n ≤ 151480000 → GoodRatio 1.603 n :=
  goodRatio_of_bound (by norm_num) (by norm_num) lr_89 ls_89 (by norm_num) (by norm_num) bnd_89

end LeanLab.GvLtR1989
