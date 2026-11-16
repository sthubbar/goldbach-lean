module

public import LeanLab.OeSHP2014.Base
public import LeanLab.OeSHP2014.Win.W008
public import LeanLab.OeSHP2014.Win.W009
public import LeanLab.OeSHP2014.Win.W010
public import LeanLab.OeSHP2014.Win.W011
public import LeanLab.OeSHP2014.Win.W012
public import LeanLab.OeSHP2014.Win.W013
public import LeanLab.OeSHP2014.Win.W014
public import LeanLab.OeSHP2014.Win.W015

/-!
Segments 23 to 25, generated: for the Table 4 row n, p of each segment, the
window checks are joined to a bound p on the least Goldbach prime of every even number from n
up to the number before the next row, or up to 10^8.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

theorem seg_23 : GBBound 10759922 24106880 829 := by
  have hq : ∀ x ∈ QKo 144, x ≤ 829 := take_le 144 829 (by decide +kernel)
  have w0 : GBBound 10759922 11749920 829 :=
    gbBound_of_owcheck (lo := 10759093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_0
  have w1 : GBBound 11749922 12739920 829 :=
    gbBound_of_owcheck (lo := 11749093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_1
  have w2 : GBBound 12739922 13729920 829 :=
    gbBound_of_owcheck (lo := 12739093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_2
  have w3 : GBBound 13729922 14719920 829 :=
    gbBound_of_owcheck (lo := 13729093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_3
  have w4 : GBBound 14719922 15709920 829 :=
    gbBound_of_owcheck (lo := 14719093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_4
  have w5 : GBBound 15709922 16699920 829 :=
    gbBound_of_owcheck (lo := 15709093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_5
  have w6 : GBBound 16699922 17689920 829 :=
    gbBound_of_owcheck (lo := 16699093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_6
  have w7 : GBBound 17689922 18679920 829 :=
    gbBound_of_owcheck (lo := 17689093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_7
  have w8 : GBBound 18679922 19669920 829 :=
    gbBound_of_owcheck (lo := 18679093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_8
  have w9 : GBBound 19669922 20659920 829 :=
    gbBound_of_owcheck (lo := 19669093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_9
  have w10 : GBBound 20659922 21649920 829 :=
    gbBound_of_owcheck (lo := 20659093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_10
  have w11 : GBBound 21649922 22639920 829 :=
    gbBound_of_owcheck (lo := 21649093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_11
  have w12 : GBBound 22639922 23629920 829 :=
    gbBound_of_owcheck (lo := 22639093) (Wb := 495414) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_12
  have w13 : GBBound 23629922 24106880 829 :=
    gbBound_of_owcheck (lo := 23629093) (Wb := 238894) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_23_13
  have v1 : GBBound 10759922 12739920 829 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 10759922 13729920 829 := GBBound.join v1 w2 (by norm_num) (by decide)
  have v3 : GBBound 10759922 14719920 829 := GBBound.join v2 w3 (by norm_num) (by decide)
  have v4 : GBBound 10759922 15709920 829 := GBBound.join v3 w4 (by norm_num) (by decide)
  have v5 : GBBound 10759922 16699920 829 := GBBound.join v4 w5 (by norm_num) (by decide)
  have v6 : GBBound 10759922 17689920 829 := GBBound.join v5 w6 (by norm_num) (by decide)
  have v7 : GBBound 10759922 18679920 829 := GBBound.join v6 w7 (by norm_num) (by decide)
  have v8 : GBBound 10759922 19669920 829 := GBBound.join v7 w8 (by norm_num) (by decide)
  have v9 : GBBound 10759922 20659920 829 := GBBound.join v8 w9 (by norm_num) (by decide)
  have v10 : GBBound 10759922 21649920 829 := GBBound.join v9 w10 (by norm_num) (by decide)
  have v11 : GBBound 10759922 22639920 829 := GBBound.join v10 w11 (by norm_num) (by decide)
  have v12 : GBBound 10759922 23629920 829 := GBBound.join v11 w12 (by norm_num) (by decide)
  have v13 : GBBound 10759922 24106880 829 := GBBound.join v12 w13 (by norm_num) (by decide)
  exact v13

theorem seg_24 : GBBound 24106882 27789876 929 := by
  have hq : ∀ x ∈ QKo 157, x ≤ 929 := take_le 157 929 (by decide +kernel)
  have w0 : GBBound 24106882 25096880 929 :=
    gbBound_of_owcheck (lo := 24105953) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_24_0
  have w1 : GBBound 25096882 26086880 929 :=
    gbBound_of_owcheck (lo := 25095953) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_24_1
  have w2 : GBBound 26086882 27076880 929 :=
    gbBound_of_owcheck (lo := 26085953) (Wb := 495464) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_24_2
  have w3 : GBBound 27076882 27789876 929 :=
    gbBound_of_owcheck (lo := 27075953) (Wb := 356962) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_24_3
  have v1 : GBBound 24106882 26086880 929 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 24106882 27076880 929 := GBBound.join v1 w2 (by norm_num) (by decide)
  have v3 : GBBound 24106882 27789876 929 := GBBound.join v2 w3 (by norm_num) (by decide)
  exact v3

theorem seg_25 : GBBound 27789878 37998936 997 := by
  have hq : ∀ x ∈ QKo 167, x ≤ 997 := take_le 167 997 (by decide +kernel)
  have w0 : GBBound 27789878 28779876 997 :=
    gbBound_of_owcheck (lo := 27788881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_0
  have w1 : GBBound 28779878 29769876 997 :=
    gbBound_of_owcheck (lo := 28778881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_1
  have w2 : GBBound 29769878 30759876 997 :=
    gbBound_of_owcheck (lo := 29768881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_2
  have w3 : GBBound 30759878 31749876 997 :=
    gbBound_of_owcheck (lo := 30758881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_3
  have w4 : GBBound 31749878 32739876 997 :=
    gbBound_of_owcheck (lo := 31748881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_4
  have w5 : GBBound 32739878 33729876 997 :=
    gbBound_of_owcheck (lo := 32738881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_5
  have w6 : GBBound 33729878 34719876 997 :=
    gbBound_of_owcheck (lo := 33728881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_6
  have w7 : GBBound 34719878 35709876 997 :=
    gbBound_of_owcheck (lo := 34718881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_7
  have w8 : GBBound 35709878 36699876 997 :=
    gbBound_of_owcheck (lo := 35708881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_8
  have w9 : GBBound 36699878 37689876 997 :=
    gbBound_of_owcheck (lo := 36698881) (Wb := 495498) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_9
  have w10 : GBBound 37689878 37998936 997 :=
    gbBound_of_owcheck (lo := 37688881) (Wb := 155028) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hq chk_25_10
  have v1 : GBBound 27789878 29769876 997 := GBBound.join w0 w1 (by norm_num) (by decide)
  have v2 : GBBound 27789878 30759876 997 := GBBound.join v1 w2 (by norm_num) (by decide)
  have v3 : GBBound 27789878 31749876 997 := GBBound.join v2 w3 (by norm_num) (by decide)
  have v4 : GBBound 27789878 32739876 997 := GBBound.join v3 w4 (by norm_num) (by decide)
  have v5 : GBBound 27789878 33729876 997 := GBBound.join v4 w5 (by norm_num) (by decide)
  have v6 : GBBound 27789878 34719876 997 := GBBound.join v5 w6 (by norm_num) (by decide)
  have v7 : GBBound 27789878 35709876 997 := GBBound.join v6 w7 (by norm_num) (by decide)
  have v8 : GBBound 27789878 36699876 997 := GBBound.join v7 w8 (by norm_num) (by decide)
  have v9 : GBBound 27789878 37689876 997 := GBBound.join v8 w9 (by norm_num) (by decide)
  have v10 : GBBound 27789878 37998936 997 := GBBound.join v9 w10 (by norm_num) (by decide)
  exact v10

end LeanLab.OeSHP2014
