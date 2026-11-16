module

public import LeanLab.GvLtR1989.Base
public import LeanLab.GvLtR1989.Blk.B00
public import LeanLab.GvLtR1989.Blk.B01
public import LeanLab.GvLtR1989.Blk.B02
public import LeanLab.GvLtR1989.Blk.B03
public import LeanLab.GvLtR1989.Blk.B04
public import LeanLab.GvLtR1989.Blk.B05
public import LeanLab.GvLtR1989.Blk.B06
public import LeanLab.GvLtR1989.Blk.B07
public import LeanLab.GvLtR1989.Blk.B08
public import LeanLab.GvLtR1989.Blk.B09
public import LeanLab.GvLtR1989.Blk.B10
public import LeanLab.GvLtR1989.Blk.B11

/-!
# The ratio bound on the even range from 6 to 323740000

The blocks of `Blk/` are joined in order. The block boundaries, the number `K` of small primes
tried and the bound `q` in each block, and the decimal lower bounds for the logarithms were
computed by the lab's Python scripts and are checked here by the kernel.
-/

@[expose] public section

namespace LeanLab.GvLtR1989

theorem c_0 : ∀ n, Even n → 6 ≤ n → n ≤ 6 → GoodRatio 1.603 n := r_0

theorem c_1 : ∀ n, Even n → 6 ≤ n → n ≤ 8 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_0 r_1 (by norm_num) (by decide)

theorem c_2 : ∀ n, Even n → 6 ≤ n → n ≤ 28 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_1 r_2 (by norm_num) (by decide)

theorem c_3 : ∀ n, Even n → 6 ≤ n → n ≤ 96 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_2 r_3 (by norm_num) (by decide)

theorem c_4 : ∀ n, Even n → 6 ≤ n → n ≤ 552 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_3 r_4 (by norm_num) (by decide)

theorem c_5 : ∀ n, Even n → 6 ≤ n → n ≤ 2638 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_4 r_5 (by norm_num) (by decide)

theorem c_6 : ∀ n, Even n → 6 ≤ n → n ≤ 7424 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_5 r_6 (by norm_num) (by decide)

theorem c_7 : ∀ n, Even n → 6 ≤ n → n ≤ 54242 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_6 r_7 (by norm_num) (by decide)

theorem c_8 : ∀ n, Even n → 6 ≤ n → n ≤ 194426 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_7 r_8 (by norm_num) (by decide)

theorem c_9 : ∀ n, Even n → 6 ≤ n → n ≤ 503218 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_8 r_9 (by norm_num) (by decide)

theorem c_10 : ∀ n, Even n → 6 ≤ n → n ≤ 999998 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_9 r_10 (by norm_num) (by decide)

theorem c_11 : ∀ n, Even n → 6 ≤ n → n ≤ 1000000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_10 r_11 (by norm_num) (by decide)

theorem c_12 : ∀ n, Even n → 6 ≤ n → n ≤ 2980000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_11 r_12 (by norm_num) (by decide)

theorem c_13 : ∀ n, Even n → 6 ≤ n → n ≤ 3475000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_12 r_13 (by norm_num) (by decide)

theorem c_14 : ∀ n, Even n → 6 ≤ n → n ≤ 3970000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_13 r_14 (by norm_num) (by decide)

theorem c_15 : ∀ n, Even n → 6 ≤ n → n ≤ 4960000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_14 r_15 (by norm_num) (by decide)

theorem c_16 : ∀ n, Even n → 6 ≤ n → n ≤ 6940000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_15 r_16 (by norm_num) (by decide)

theorem c_17 : ∀ n, Even n → 6 ≤ n → n ≤ 8920000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_16 r_17 (by norm_num) (by decide)

theorem c_18 : ∀ n, Even n → 6 ≤ n → n ≤ 10900000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_17 r_18 (by norm_num) (by decide)

theorem c_19 : ∀ n, Even n → 6 ≤ n → n ≤ 12880000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_18 r_19 (by norm_num) (by decide)

theorem c_20 : ∀ n, Even n → 6 ≤ n → n ≤ 14860000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_19 r_20 (by norm_num) (by decide)

theorem c_21 : ∀ n, Even n → 6 ≤ n → n ≤ 16840000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_20 r_21 (by norm_num) (by decide)

theorem c_22 : ∀ n, Even n → 6 ≤ n → n ≤ 18820000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_21 r_22 (by norm_num) (by decide)

theorem c_23 : ∀ n, Even n → 6 ≤ n → n ≤ 20800000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_22 r_23 (by norm_num) (by decide)

theorem c_24 : ∀ n, Even n → 6 ≤ n → n ≤ 22780000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_23 r_24 (by norm_num) (by decide)

theorem c_25 : ∀ n, Even n → 6 ≤ n → n ≤ 24760000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_24 r_25 (by norm_num) (by decide)

theorem c_26 : ∀ n, Even n → 6 ≤ n → n ≤ 26740000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_25 r_26 (by norm_num) (by decide)

theorem c_27 : ∀ n, Even n → 6 ≤ n → n ≤ 28720000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_26 r_27 (by norm_num) (by decide)

theorem c_28 : ∀ n, Even n → 6 ≤ n → n ≤ 30700000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_27 r_28 (by norm_num) (by decide)

theorem c_29 : ∀ n, Even n → 6 ≤ n → n ≤ 32680000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_28 r_29 (by norm_num) (by decide)

theorem c_30 : ∀ n, Even n → 6 ≤ n → n ≤ 34660000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_29 r_30 (by norm_num) (by decide)

theorem c_31 : ∀ n, Even n → 6 ≤ n → n ≤ 36640000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_30 r_31 (by norm_num) (by decide)

theorem c_32 : ∀ n, Even n → 6 ≤ n → n ≤ 38620000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_31 r_32 (by norm_num) (by decide)

theorem c_33 : ∀ n, Even n → 6 ≤ n → n ≤ 40600000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_32 r_33 (by norm_num) (by decide)

theorem c_34 : ∀ n, Even n → 6 ≤ n → n ≤ 42580000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_33 r_34 (by norm_num) (by decide)

theorem c_35 : ∀ n, Even n → 6 ≤ n → n ≤ 44560000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_34 r_35 (by norm_num) (by decide)

theorem c_36 : ∀ n, Even n → 6 ≤ n → n ≤ 46540000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_35 r_36 (by norm_num) (by decide)

theorem c_37 : ∀ n, Even n → 6 ≤ n → n ≤ 48520000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_36 r_37 (by norm_num) (by decide)

theorem c_38 : ∀ n, Even n → 6 ≤ n → n ≤ 50500000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_37 r_38 (by norm_num) (by decide)

theorem c_39 : ∀ n, Even n → 6 ≤ n → n ≤ 52480000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_38 r_39 (by norm_num) (by decide)

theorem c_40 : ∀ n, Even n → 6 ≤ n → n ≤ 54460000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_39 r_40 (by norm_num) (by decide)

theorem c_41 : ∀ n, Even n → 6 ≤ n → n ≤ 56440000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_40 r_41 (by norm_num) (by decide)

theorem c_42 : ∀ n, Even n → 6 ≤ n → n ≤ 58420000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_41 r_42 (by norm_num) (by decide)

theorem c_43 : ∀ n, Even n → 6 ≤ n → n ≤ 60400000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_42 r_43 (by norm_num) (by decide)

theorem c_44 : ∀ n, Even n → 6 ≤ n → n ≤ 62380000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_43 r_44 (by norm_num) (by decide)

theorem c_45 : ∀ n, Even n → 6 ≤ n → n ≤ 64360000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_44 r_45 (by norm_num) (by decide)

theorem c_46 : ∀ n, Even n → 6 ≤ n → n ≤ 66340000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_45 r_46 (by norm_num) (by decide)

theorem c_47 : ∀ n, Even n → 6 ≤ n → n ≤ 68320000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_46 r_47 (by norm_num) (by decide)

theorem c_48 : ∀ n, Even n → 6 ≤ n → n ≤ 70300000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_47 r_48 (by norm_num) (by decide)

theorem c_49 : ∀ n, Even n → 6 ≤ n → n ≤ 72280000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_48 r_49 (by norm_num) (by decide)

theorem c_50 : ∀ n, Even n → 6 ≤ n → n ≤ 74260000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_49 r_50 (by norm_num) (by decide)

theorem c_51 : ∀ n, Even n → 6 ≤ n → n ≤ 76240000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_50 r_51 (by norm_num) (by decide)

theorem c_52 : ∀ n, Even n → 6 ≤ n → n ≤ 78220000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_51 r_52 (by norm_num) (by decide)

theorem c_53 : ∀ n, Even n → 6 ≤ n → n ≤ 80200000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_52 r_53 (by norm_num) (by decide)

theorem c_54 : ∀ n, Even n → 6 ≤ n → n ≤ 82180000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_53 r_54 (by norm_num) (by decide)

theorem c_55 : ∀ n, Even n → 6 ≤ n → n ≤ 84160000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_54 r_55 (by norm_num) (by decide)

theorem c_56 : ∀ n, Even n → 6 ≤ n → n ≤ 86140000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_55 r_56 (by norm_num) (by decide)

theorem c_57 : ∀ n, Even n → 6 ≤ n → n ≤ 88120000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_56 r_57 (by norm_num) (by decide)

theorem c_58 : ∀ n, Even n → 6 ≤ n → n ≤ 90100000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_57 r_58 (by norm_num) (by decide)

theorem c_59 : ∀ n, Even n → 6 ≤ n → n ≤ 92080000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_58 r_59 (by norm_num) (by decide)

theorem c_60 : ∀ n, Even n → 6 ≤ n → n ≤ 94060000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_59 r_60 (by norm_num) (by decide)

theorem c_61 : ∀ n, Even n → 6 ≤ n → n ≤ 96040000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_60 r_61 (by norm_num) (by decide)

theorem c_62 : ∀ n, Even n → 6 ≤ n → n ≤ 98020000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_61 r_62 (by norm_num) (by decide)

theorem c_63 : ∀ n, Even n → 6 ≤ n → n ≤ 100000000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_62 r_63 (by norm_num) (by decide)

theorem c_64 : ∀ n, Even n → 6 ≤ n → n ≤ 101980000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_63 r_64 (by norm_num) (by decide)

theorem c_65 : ∀ n, Even n → 6 ≤ n → n ≤ 103960000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_64 r_65 (by norm_num) (by decide)

theorem c_66 : ∀ n, Even n → 6 ≤ n → n ≤ 105940000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_65 r_66 (by norm_num) (by decide)

theorem c_67 : ∀ n, Even n → 6 ≤ n → n ≤ 107920000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_66 r_67 (by norm_num) (by decide)

theorem c_68 : ∀ n, Even n → 6 ≤ n → n ≤ 109900000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_67 r_68 (by norm_num) (by decide)

theorem c_69 : ∀ n, Even n → 6 ≤ n → n ≤ 111880000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_68 r_69 (by norm_num) (by decide)

theorem c_70 : ∀ n, Even n → 6 ≤ n → n ≤ 113860000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_69 r_70 (by norm_num) (by decide)

theorem c_71 : ∀ n, Even n → 6 ≤ n → n ≤ 115840000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_70 r_71 (by norm_num) (by decide)

theorem c_72 : ∀ n, Even n → 6 ≤ n → n ≤ 117820000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_71 r_72 (by norm_num) (by decide)

theorem c_73 : ∀ n, Even n → 6 ≤ n → n ≤ 119800000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_72 r_73 (by norm_num) (by decide)

theorem c_74 : ∀ n, Even n → 6 ≤ n → n ≤ 121780000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_73 r_74 (by norm_num) (by decide)

theorem c_75 : ∀ n, Even n → 6 ≤ n → n ≤ 123760000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_74 r_75 (by norm_num) (by decide)

theorem c_76 : ∀ n, Even n → 6 ≤ n → n ≤ 125740000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_75 r_76 (by norm_num) (by decide)

theorem c_77 : ∀ n, Even n → 6 ≤ n → n ≤ 127720000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_76 r_77 (by norm_num) (by decide)

theorem c_78 : ∀ n, Even n → 6 ≤ n → n ≤ 129700000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_77 r_78 (by norm_num) (by decide)

theorem c_79 : ∀ n, Even n → 6 ≤ n → n ≤ 131680000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_78 r_79 (by norm_num) (by decide)

theorem c_80 : ∀ n, Even n → 6 ≤ n → n ≤ 133660000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_79 r_80 (by norm_num) (by decide)

theorem c_81 : ∀ n, Even n → 6 ≤ n → n ≤ 135640000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_80 r_81 (by norm_num) (by decide)

theorem c_82 : ∀ n, Even n → 6 ≤ n → n ≤ 137620000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_81 r_82 (by norm_num) (by decide)

theorem c_83 : ∀ n, Even n → 6 ≤ n → n ≤ 139600000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_82 r_83 (by norm_num) (by decide)

theorem c_84 : ∀ n, Even n → 6 ≤ n → n ≤ 141580000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_83 r_84 (by norm_num) (by decide)

theorem c_85 : ∀ n, Even n → 6 ≤ n → n ≤ 143560000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_84 r_85 (by norm_num) (by decide)

theorem c_86 : ∀ n, Even n → 6 ≤ n → n ≤ 145540000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_85 r_86 (by norm_num) (by decide)

theorem c_87 : ∀ n, Even n → 6 ≤ n → n ≤ 147520000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_86 r_87 (by norm_num) (by decide)

theorem c_88 : ∀ n, Even n → 6 ≤ n → n ≤ 149500000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_87 r_88 (by norm_num) (by decide)

theorem c_89 : ∀ n, Even n → 6 ≤ n → n ≤ 151480000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_88 r_89 (by norm_num) (by decide)

theorem c_90 : ∀ n, Even n → 6 ≤ n → n ≤ 153460000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_89 r_90 (by norm_num) (by decide)

theorem c_91 : ∀ n, Even n → 6 ≤ n → n ≤ 155440000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_90 r_91 (by norm_num) (by decide)

theorem c_92 : ∀ n, Even n → 6 ≤ n → n ≤ 157420000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_91 r_92 (by norm_num) (by decide)

theorem c_93 : ∀ n, Even n → 6 ≤ n → n ≤ 159400000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_92 r_93 (by norm_num) (by decide)

theorem c_94 : ∀ n, Even n → 6 ≤ n → n ≤ 161380000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_93 r_94 (by norm_num) (by decide)

theorem c_95 : ∀ n, Even n → 6 ≤ n → n ≤ 163360000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_94 r_95 (by norm_num) (by decide)

theorem c_96 : ∀ n, Even n → 6 ≤ n → n ≤ 165340000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_95 r_96 (by norm_num) (by decide)

theorem c_97 : ∀ n, Even n → 6 ≤ n → n ≤ 167320000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_96 r_97 (by norm_num) (by decide)

theorem c_98 : ∀ n, Even n → 6 ≤ n → n ≤ 169300000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_97 r_98 (by norm_num) (by decide)

theorem c_99 : ∀ n, Even n → 6 ≤ n → n ≤ 171280000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_98 r_99 (by norm_num) (by decide)

theorem c_100 : ∀ n, Even n → 6 ≤ n → n ≤ 173260000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_99 r_100 (by norm_num) (by decide)

theorem c_101 : ∀ n, Even n → 6 ≤ n → n ≤ 175240000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_100 r_101 (by norm_num) (by decide)

theorem c_102 : ∀ n, Even n → 6 ≤ n → n ≤ 177220000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_101 r_102 (by norm_num) (by decide)

theorem c_103 : ∀ n, Even n → 6 ≤ n → n ≤ 179200000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_102 r_103 (by norm_num) (by decide)

theorem c_104 : ∀ n, Even n → 6 ≤ n → n ≤ 181180000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_103 r_104 (by norm_num) (by decide)

theorem c_105 : ∀ n, Even n → 6 ≤ n → n ≤ 183160000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_104 r_105 (by norm_num) (by decide)

theorem c_106 : ∀ n, Even n → 6 ≤ n → n ≤ 185140000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_105 r_106 (by norm_num) (by decide)

theorem c_107 : ∀ n, Even n → 6 ≤ n → n ≤ 187120000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_106 r_107 (by norm_num) (by decide)

theorem c_108 : ∀ n, Even n → 6 ≤ n → n ≤ 189100000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_107 r_108 (by norm_num) (by decide)

theorem c_109 : ∀ n, Even n → 6 ≤ n → n ≤ 191080000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_108 r_109 (by norm_num) (by decide)

theorem c_110 : ∀ n, Even n → 6 ≤ n → n ≤ 193060000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_109 r_110 (by norm_num) (by decide)

theorem c_111 : ∀ n, Even n → 6 ≤ n → n ≤ 195040000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_110 r_111 (by norm_num) (by decide)

theorem c_112 : ∀ n, Even n → 6 ≤ n → n ≤ 197020000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_111 r_112 (by norm_num) (by decide)

theorem c_113 : ∀ n, Even n → 6 ≤ n → n ≤ 199000000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_112 r_113 (by norm_num) (by decide)

theorem c_114 : ∀ n, Even n → 6 ≤ n → n ≤ 200980000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_113 r_114 (by norm_num) (by decide)

theorem c_115 : ∀ n, Even n → 6 ≤ n → n ≤ 202960000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_114 r_115 (by norm_num) (by decide)

theorem c_116 : ∀ n, Even n → 6 ≤ n → n ≤ 204940000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_115 r_116 (by norm_num) (by decide)

theorem c_117 : ∀ n, Even n → 6 ≤ n → n ≤ 206920000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_116 r_117 (by norm_num) (by decide)

theorem c_118 : ∀ n, Even n → 6 ≤ n → n ≤ 208900000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_117 r_118 (by norm_num) (by decide)

theorem c_119 : ∀ n, Even n → 6 ≤ n → n ≤ 210880000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_118 r_119 (by norm_num) (by decide)

theorem c_120 : ∀ n, Even n → 6 ≤ n → n ≤ 212860000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_119 r_120 (by norm_num) (by decide)

theorem c_121 : ∀ n, Even n → 6 ≤ n → n ≤ 214840000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_120 r_121 (by norm_num) (by decide)

theorem c_122 : ∀ n, Even n → 6 ≤ n → n ≤ 216820000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_121 r_122 (by norm_num) (by decide)

theorem c_123 : ∀ n, Even n → 6 ≤ n → n ≤ 218800000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_122 r_123 (by norm_num) (by decide)

theorem c_124 : ∀ n, Even n → 6 ≤ n → n ≤ 220780000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_123 r_124 (by norm_num) (by decide)

theorem c_125 : ∀ n, Even n → 6 ≤ n → n ≤ 222760000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_124 r_125 (by norm_num) (by decide)

theorem c_126 : ∀ n, Even n → 6 ≤ n → n ≤ 224740000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_125 r_126 (by norm_num) (by decide)

theorem c_127 : ∀ n, Even n → 6 ≤ n → n ≤ 226720000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_126 r_127 (by norm_num) (by decide)

theorem c_128 : ∀ n, Even n → 6 ≤ n → n ≤ 228700000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_127 r_128 (by norm_num) (by decide)

theorem c_129 : ∀ n, Even n → 6 ≤ n → n ≤ 230680000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_128 r_129 (by norm_num) (by decide)

theorem c_130 : ∀ n, Even n → 6 ≤ n → n ≤ 232660000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_129 r_130 (by norm_num) (by decide)

theorem c_131 : ∀ n, Even n → 6 ≤ n → n ≤ 234640000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_130 r_131 (by norm_num) (by decide)

theorem c_132 : ∀ n, Even n → 6 ≤ n → n ≤ 236620000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_131 r_132 (by norm_num) (by decide)

theorem c_133 : ∀ n, Even n → 6 ≤ n → n ≤ 238600000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_132 r_133 (by norm_num) (by decide)

theorem c_134 : ∀ n, Even n → 6 ≤ n → n ≤ 240580000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_133 r_134 (by norm_num) (by decide)

theorem c_135 : ∀ n, Even n → 6 ≤ n → n ≤ 242560000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_134 r_135 (by norm_num) (by decide)

theorem c_136 : ∀ n, Even n → 6 ≤ n → n ≤ 244540000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_135 r_136 (by norm_num) (by decide)

theorem c_137 : ∀ n, Even n → 6 ≤ n → n ≤ 246520000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_136 r_137 (by norm_num) (by decide)

theorem c_138 : ∀ n, Even n → 6 ≤ n → n ≤ 248500000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_137 r_138 (by norm_num) (by decide)

theorem c_139 : ∀ n, Even n → 6 ≤ n → n ≤ 250480000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_138 r_139 (by norm_num) (by decide)

theorem c_140 : ∀ n, Even n → 6 ≤ n → n ≤ 252460000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_139 r_140 (by norm_num) (by decide)

theorem c_141 : ∀ n, Even n → 6 ≤ n → n ≤ 254440000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_140 r_141 (by norm_num) (by decide)

theorem c_142 : ∀ n, Even n → 6 ≤ n → n ≤ 256420000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_141 r_142 (by norm_num) (by decide)

theorem c_143 : ∀ n, Even n → 6 ≤ n → n ≤ 258400000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_142 r_143 (by norm_num) (by decide)

theorem c_144 : ∀ n, Even n → 6 ≤ n → n ≤ 260380000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_143 r_144 (by norm_num) (by decide)

theorem c_145 : ∀ n, Even n → 6 ≤ n → n ≤ 262360000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_144 r_145 (by norm_num) (by decide)

theorem c_146 : ∀ n, Even n → 6 ≤ n → n ≤ 264340000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_145 r_146 (by norm_num) (by decide)

theorem c_147 : ∀ n, Even n → 6 ≤ n → n ≤ 266320000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_146 r_147 (by norm_num) (by decide)

theorem c_148 : ∀ n, Even n → 6 ≤ n → n ≤ 268300000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_147 r_148 (by norm_num) (by decide)

theorem c_149 : ∀ n, Even n → 6 ≤ n → n ≤ 270280000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_148 r_149 (by norm_num) (by decide)

theorem c_150 : ∀ n, Even n → 6 ≤ n → n ≤ 272260000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_149 r_150 (by norm_num) (by decide)

theorem c_151 : ∀ n, Even n → 6 ≤ n → n ≤ 274240000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_150 r_151 (by norm_num) (by decide)

theorem c_152 : ∀ n, Even n → 6 ≤ n → n ≤ 276220000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_151 r_152 (by norm_num) (by decide)

theorem c_153 : ∀ n, Even n → 6 ≤ n → n ≤ 278200000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_152 r_153 (by norm_num) (by decide)

theorem c_154 : ∀ n, Even n → 6 ≤ n → n ≤ 280180000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_153 r_154 (by norm_num) (by decide)

theorem c_155 : ∀ n, Even n → 6 ≤ n → n ≤ 282160000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_154 r_155 (by norm_num) (by decide)

theorem c_156 : ∀ n, Even n → 6 ≤ n → n ≤ 284140000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_155 r_156 (by norm_num) (by decide)

theorem c_157 : ∀ n, Even n → 6 ≤ n → n ≤ 286120000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_156 r_157 (by norm_num) (by decide)

theorem c_158 : ∀ n, Even n → 6 ≤ n → n ≤ 288100000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_157 r_158 (by norm_num) (by decide)

theorem c_159 : ∀ n, Even n → 6 ≤ n → n ≤ 290080000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_158 r_159 (by norm_num) (by decide)

theorem c_160 : ∀ n, Even n → 6 ≤ n → n ≤ 292060000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_159 r_160 (by norm_num) (by decide)

theorem c_161 : ∀ n, Even n → 6 ≤ n → n ≤ 294040000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_160 r_161 (by norm_num) (by decide)

theorem c_162 : ∀ n, Even n → 6 ≤ n → n ≤ 296020000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_161 r_162 (by norm_num) (by decide)

theorem c_163 : ∀ n, Even n → 6 ≤ n → n ≤ 298000000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_162 r_163 (by norm_num) (by decide)

theorem c_164 : ∀ n, Even n → 6 ≤ n → n ≤ 299980000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_163 r_164 (by norm_num) (by decide)

theorem c_165 : ∀ n, Even n → 6 ≤ n → n ≤ 301960000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_164 r_165 (by norm_num) (by decide)

theorem c_166 : ∀ n, Even n → 6 ≤ n → n ≤ 303940000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_165 r_166 (by norm_num) (by decide)

theorem c_167 : ∀ n, Even n → 6 ≤ n → n ≤ 305920000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_166 r_167 (by norm_num) (by decide)

theorem c_168 : ∀ n, Even n → 6 ≤ n → n ≤ 307900000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_167 r_168 (by norm_num) (by decide)

theorem c_169 : ∀ n, Even n → 6 ≤ n → n ≤ 309880000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_168 r_169 (by norm_num) (by decide)

theorem c_170 : ∀ n, Even n → 6 ≤ n → n ≤ 311860000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_169 r_170 (by norm_num) (by decide)

theorem c_171 : ∀ n, Even n → 6 ≤ n → n ≤ 313840000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_170 r_171 (by norm_num) (by decide)

theorem c_172 : ∀ n, Even n → 6 ≤ n → n ≤ 315820000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_171 r_172 (by norm_num) (by decide)

theorem c_173 : ∀ n, Even n → 6 ≤ n → n ≤ 317800000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_172 r_173 (by norm_num) (by decide)

theorem c_174 : ∀ n, Even n → 6 ≤ n → n ≤ 319780000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_173 r_174 (by norm_num) (by decide)

theorem c_175 : ∀ n, Even n → 6 ≤ n → n ≤ 321760000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_174 r_175 (by norm_num) (by decide)

theorem c_176 : ∀ n, Even n → 6 ≤ n → n ≤ 323740000 → GoodRatio 1.603 n :=
  join (P := GoodRatio 1.603) c_175 r_176 (by norm_num) (by decide)

/-- For every even `n` with `6 ≤ n ≤ 323740000`, the least prime `p(n)` with `n - p(n)` prime
exists, and `p(n) < 1.603 · log² n · log log n`. -/
theorem gvltr_ratio_upTo2 : ∀ n : ℕ, Even n → 6 ≤ n → n ≤ 323740000 →
    (minGB n).Prime ∧ (n - minGB n).Prime ∧
      (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) :=
  c_176

end LeanLab.GvLtR1989
