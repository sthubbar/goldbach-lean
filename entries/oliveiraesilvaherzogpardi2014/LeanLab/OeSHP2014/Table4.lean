module

public import LeanLab.OeSHP2014.Base
public import LeanLab.OeSHP2014.Seg.S00
public import LeanLab.OeSHP2014.Seg.S01
public import LeanLab.OeSHP2014.Seg.S02
public import LeanLab.OeSHP2014.Seg.S03

/-!
# Table 4 of Oliveira e Silva, Herzog and Pardi on the even numbers up to 10^8

`seg_i` bounds the least Goldbach prime by the row value `p` on the segment that starts at the
row `n`. The divisor certificates `cert_i` show that `n - x` is composite for every prime
`x < p`, so `minGB n = p`. Joining the segments gives the leastness of each row and the
completeness of the rows up to 10^8.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

set_option maxRecDepth 20000

/-- Table 4 of the paper, page 2043: the rows `(n, p(n))`, the even `n` at which the least
prime `p(n)` of a Goldbach partition reaches a new record, from 6 to 3325581707333960528. -/
def table4 : List (ℕ × ℕ) := [
    (6, 3),
    (12, 5),
    (30, 7),
    (98, 19),
    (220, 23),
    (308, 31),
    (556, 47),
    (992, 73),
    (2642, 103),
    (5372, 139),
    (7426, 173),
    (43532, 211),
    (54244, 233),
    (63274, 293),
    (113672, 313),
    (128168, 331),
    (194428, 359),
    (194470, 383),
    (413572, 389),
    (503222, 523),
    (1077422, 601),
    (3526958, 727),
    (3807404, 751),
    (10759922, 829),
    (24106882, 929),
    (27789878, 997),
    (37998938, 1039),
    (60119912, 1093),
    (113632822, 1163),
    (187852862, 1321),
    (335070838, 1427),
    (419911924, 1583),
    (721013438, 1789),
    (1847133842, 1861),
    (7473202036, 1877),
    (11001080372, 1879),
    (12703943222, 2029),
    (21248558888, 2089),
    (35884080836, 2803),
    (105963812462, 3061),
    (244885595672, 3163),
    (599533546358, 3457),
    (3132059294006, 3463),
    (3620821173302, 3529),
    (4438327672994, 3613),
    (5320503815888, 3769),
    (8342945544436, 3917),
    (10591605900482, 4003),
    (12982270197518, 4027),
    (15197900994218, 4057),
    (28998050650046, 4327),
    (46878442766282, 4519),
    (76903574497118, 4909),
    (184162477860248, 5077),
    (217361316706568, 5209),
    (389965026819938, 5569),
    (1047610575836828, 6469),
    (6253262345930828, 6961),
    (24925556008175266, 7559),
    (31284177910528922, 7753),
    (121005022304007026, 8443),
    (255329126688555994, 8501),
    (258549426916149682, 8933),
    (555274351556750822, 8941),
    (887123803077837868, 9161),
    (906030579562279642, 9341),
    (2795935116574469638, 9629),
    (3325581707333960528, 9781)]

/-- Divisors of `6 - x` for the primes `x < 3`. -/
def cert_0 : List (ℕ × ℕ) := [(2, 2)]

theorem row_0 : minGB 6 = 3 :=
  minGB_eq_of_cert cert_0 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_0.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `12 - x` for the primes `x < 5`. -/
def cert_1 : List (ℕ × ℕ) := [(2, 2), (3, 3)]

theorem row_1 : minGB 12 = 5 :=
  minGB_eq_of_cert cert_1 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_1.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `30 - x` for the primes `x < 7`. -/
def cert_2 : List (ℕ × ℕ) := [(2, 2), (3, 3), (5, 5)]

theorem row_2 : minGB 30 = 7 :=
  minGB_eq_of_cert cert_2 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_2.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `98 - x` for the primes `x < 19`. -/
def cert_3 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 3), (7, 7), (11, 3), (13, 5), (17, 3)]

theorem row_3 : minGB 98 = 19 :=
  minGB_eq_of_cert cert_3 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_3.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `220 - x` for the primes `x < 23`. -/
def cert_4 : List (ℕ × ℕ) := [(2, 2), (3, 7), (5, 5), (7, 3), (11, 11), (13, 3), (17, 7), (19, 3)]

theorem row_4 : minGB 220 = 23 :=
  minGB_eq_of_cert cert_4 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_4.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `308 - x` for the primes `x < 31`. -/
def cert_5 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 3), (7, 7), (11, 3), (13, 5), (17, 3), (19, 17), (23, 3), (29, 3)]

theorem row_5 : minGB 308 = 31 :=
  minGB_eq_of_cert cert_5 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_5.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `556 - x` for the primes `x < 47`. -/
def cert_6 : List (ℕ × ℕ) := [(2, 2), (3, 7), (5, 19), (7, 3), (11, 5), (13, 3), (17, 7), (19, 3), (23, 13), (29, 17), (31, 3), (37, 3), (41, 5), (43, 3)]

theorem row_6 : minGB 556 = 47 :=
  minGB_eq_of_cert cert_6 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_6.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `992 - x` for the primes `x < 73`. -/
def cert_7 : List (ℕ × ℕ) := [(2, 2), (3, 23), (5, 3), (7, 5), (11, 3), (13, 11), (17, 3), (19, 7), (23, 3), (29, 3), (31, 31), (37, 5), (41, 3), (43, 13), (47, 3), (53, 3), (59, 3), (61, 7), (67, 5), (71, 3)]

theorem row_7 : minGB 992 = 73 :=
  minGB_eq_of_cert cert_7 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_7.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `2642 - x` for the primes `x < 103`. -/
def cert_8 : List (ℕ × ℕ) := [(2, 2), (3, 7), (5, 3), (7, 5), (11, 3), (13, 11), (17, 3), (19, 43), (23, 3), (29, 3), (31, 7), (37, 5), (41, 3), (43, 23), (47, 3), (53, 3), (59, 3), (61, 29), (67, 5), (71, 3), (73, 7), (79, 11), (83, 3), (89, 3), (97, 5), (101, 3)]

theorem row_8 : minGB 2642 = 103 :=
  minGB_eq_of_cert cert_8 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_8.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `5372 - x` for the primes `x < 139`. -/
def cert_9 : List (ℕ × ℕ) := [(2, 2), (3, 7), (5, 3), (7, 5), (11, 3), (13, 23), (17, 3), (19, 53), (23, 3), (29, 3), (31, 7), (37, 5), (41, 3), (43, 73), (47, 3), (53, 3), (59, 3), (61, 47), (67, 5), (71, 3), (73, 7), (79, 67), (83, 3), (89, 3), (97, 5), (101, 3), (103, 11), (107, 3), (109, 19), (113, 3), (127, 5), (131, 3), (137, 3)]

theorem row_9 : minGB 5372 = 139 :=
  minGB_eq_of_cert cert_9 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_9.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `7426 - x` for the primes `x < 173`. -/
def cert_10 : List (ℕ × ℕ) := [(2, 2), (3, 13), (5, 41), (7, 3), (11, 5), (13, 3), (17, 31), (19, 3), (23, 11), (29, 13), (31, 3), (37, 3), (41, 5), (43, 3), (47, 47), (53, 73), (59, 53), (61, 3), (67, 3), (71, 5), (73, 3), (79, 3), (83, 7), (89, 11), (97, 3), (101, 5), (103, 3), (107, 13), (109, 3), (113, 71), (127, 3), (131, 5), (137, 37), (139, 3), (149, 19), (151, 3), (157, 3), (163, 3), (167, 7)]

theorem row_10 : minGB 7426 = 173 :=
  minGB_eq_of_cert cert_10 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_10.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `43532 - x` for the primes `x < 211`. -/
def cert_11 : List (ℕ × ℕ) := [(2, 2), (3, 19), (5, 3), (7, 5), (11, 3), (13, 7), (17, 3), (19, 53), (23, 3), (29, 3), (31, 41), (37, 5), (41, 3), (43, 157), (47, 3), (53, 3), (59, 3), (61, 29), (67, 5), (71, 3), (73, 13), (79, 19), (83, 3), (89, 3), (97, 5), (101, 3), (103, 137), (107, 3), (109, 173), (113, 3), (127, 5), (131, 3), (137, 3), (139, 7), (149, 3), (151, 13), (157, 5), (163, 31), (167, 3), (173, 3), (179, 3), (181, 7), (191, 3), (193, 19), (197, 3), (199, 17)]

theorem row_11 : minGB 43532 = 211 :=
  minGB_eq_of_cert cert_11 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_11.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `54244 - x` for the primes `x < 233`. -/
def cert_12 : List (ℕ × ℕ) := [(2, 2), (3, 11), (5, 73), (7, 3), (11, 193), (13, 3), (17, 211), (19, 3), (23, 59), (29, 5), (31, 3), (37, 3), (41, 67), (43, 3), (47, 11), (53, 47), (59, 5), (61, 3), (67, 3), (71, 7), (73, 3), (79, 3), (83, 41), (89, 5), (97, 3), (101, 29), (103, 3), (107, 43), (109, 3), (113, 7), (127, 3), (131, 53), (137, 61), (139, 3), (149, 5), (151, 3), (157, 3), (163, 3), (167, 17), (173, 139), (179, 5), (181, 3), (191, 191), (193, 3), (197, 7), (199, 3), (211, 3), (223, 3), (227, 19), (229, 3)]

theorem row_12 : minGB 54244 = 233 :=
  minGB_eq_of_cert cert_12 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_12.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `63274 - x` for the primes `x < 293`. -/
def cert_13 : List (ℕ × ℕ) := [(2, 2), (3, 13), (5, 151), (7, 3), (11, 41), (13, 3), (17, 17), (19, 3), (23, 19), (29, 5), (31, 3), (37, 3), (41, 37), (43, 3), (47, 23), (53, 191), (59, 5), (61, 3), (67, 3), (71, 7), (73, 3), (79, 3), (83, 29), (89, 5), (97, 3), (101, 11), (103, 3), (107, 13), (109, 3), (113, 7), (127, 3), (131, 233), (137, 19), (139, 3), (149, 5), (151, 3), (157, 3), (163, 3), (167, 11), (173, 89), (179, 5), (181, 3), (191, 199), (193, 3), (197, 7), (199, 3), (211, 3), (223, 3), (227, 67), (229, 3), (233, 11), (239, 5), (241, 3), (251, 19), (257, 29), (263, 13), (269, 5), (271, 3), (277, 3), (281, 7), (283, 3)]

theorem row_13 : minGB 63274 = 293 :=
  minGB_eq_of_cert cert_13 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_13.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `113672 - x` for the primes `x < 313`. -/
def cert_14 : List (ℕ × ℕ) := [(2, 2), (3, 197), (5, 3), (7, 5), (11, 3), (13, 7), (17, 3), (19, 89), (23, 3), (29, 3), (31, 11), (37, 5), (41, 3), (43, 199), (47, 3), (53, 3), (59, 3), (61, 17), (67, 5), (71, 3), (73, 47), (79, 29), (83, 3), (89, 3), (97, 5), (101, 3), (103, 337), (107, 3), (109, 19), (113, 3), (127, 5), (131, 3), (137, 3), (139, 7), (149, 3), (151, 61), (157, 5), (163, 11), (167, 3), (173, 3), (179, 3), (181, 7), (191, 3), (193, 37), (197, 3), (199, 53), (211, 83), (223, 7), (227, 3), (229, 11), (233, 3), (239, 3), (241, 67), (251, 3), (257, 3), (263, 3), (269, 3), (271, 151), (277, 5), (281, 3), (283, 149), (293, 3), (307, 5), (311, 3)]

theorem row_14 : minGB 113672 = 313 :=
  minGB_eq_of_cert cert_14 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_14.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `128168 - x` for the primes `x < 331`. -/
def cert_15 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 3), (7, 11), (11, 3), (13, 5), (17, 3), (19, 7), (23, 3), (29, 3), (31, 97), (37, 37), (41, 3), (43, 5), (47, 3), (53, 3), (59, 3), (61, 7), (67, 53), (71, 3), (73, 5), (79, 13), (83, 3), (89, 3), (97, 89), (101, 3), (103, 5), (107, 3), (109, 79), (113, 3), (127, 19), (131, 3), (137, 3), (139, 11), (149, 3), (151, 313), (157, 13), (163, 5), (167, 3), (173, 3), (179, 3), (181, 131), (191, 3), (193, 5), (197, 3), (199, 73), (211, 199), (223, 5), (227, 3), (229, 7), (233, 3), (239, 3), (241, 19), (251, 3), (257, 3), (263, 3), (269, 3), (271, 7), (277, 17), (281, 3), (283, 5), (293, 3), (307, 29), (311, 3), (313, 5), (317, 3)]

theorem row_15 : minGB 128168 = 331 :=
  minGB_eq_of_cert cert_15 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_15.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `194428 - x` for the primes `x < 359`. -/
def cert_16 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 199), (7, 3), (11, 433), (13, 3), (17, 7), (19, 3), (23, 5), (29, 73), (31, 3), (37, 3), (41, 29), (43, 3), (47, 11), (53, 5), (59, 7), (61, 3), (67, 3), (71, 263), (73, 3), (79, 3), (83, 5), (89, 31), (97, 3), (101, 7), (103, 3), (107, 317), (109, 3), (113, 5), (127, 3), (131, 331), (137, 97), (139, 3), (149, 173), (151, 3), (157, 3), (163, 3), (167, 79), (173, 5), (179, 11), (181, 3), (191, 19), (193, 3), (197, 43), (199, 3), (211, 3), (223, 3), (227, 7), (229, 3), (233, 5), (239, 23), (241, 3), (251, 277), (257, 281), (263, 5), (269, 7), (271, 3), (277, 3), (281, 149), (283, 3), (293, 5), (307, 3), (311, 7), (313, 3), (317, 389), (331, 3), (337, 3), (347, 421), (349, 3), (353, 5)]

theorem row_16 : minGB 194428 = 359 :=
  minGB_eq_of_cert cert_16 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_16.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `194470 - x` for the primes `x < 383`. -/
def cert_17 : List (ℕ × ℕ) := [(2, 2), (3, 7), (5, 5), (7, 3), (11, 163), (13, 3), (17, 7), (19, 3), (23, 11), (29, 13), (31, 3), (37, 3), (41, 17), (43, 3), (47, 199), (53, 433), (59, 7), (61, 3), (67, 3), (71, 73), (73, 3), (79, 3), (83, 29), (89, 11), (97, 3), (101, 7), (103, 3), (107, 13), (109, 3), (113, 263), (127, 3), (131, 31), (137, 373), (139, 3), (149, 317), (151, 3), (157, 3), (163, 3), (167, 83), (173, 331), (179, 97), (181, 3), (191, 173), (193, 3), (197, 131), (199, 3), (211, 3), (223, 3), (227, 7), (229, 3), (233, 19), (239, 43), (241, 3), (251, 359), (257, 29), (263, 13), (269, 7), (271, 3), (277, 3), (281, 23), (283, 3), (293, 277), (307, 3), (311, 7), (313, 3), (317, 31), (331, 3), (337, 3), (347, 17), (349, 3), (353, 7), (359, 389), (367, 3), (373, 3), (379, 3)]

theorem row_17 : minGB 194470 = 383 :=
  minGB_eq_of_cert cert_17 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_17.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `413572 - x` for the primes `x < 389`. -/
def cert_18 : List (ℕ × ℕ) := [(2, 2), (3, 13), (5, 7), (7, 3), (11, 277), (13, 3), (17, 5), (19, 3), (23, 37), (29, 13), (31, 3), (37, 3), (41, 43), (43, 3), (47, 5), (53, 61), (59, 257), (61, 3), (67, 3), (71, 11), (73, 3), (79, 3), (83, 379), (89, 7), (97, 3), (101, 23), (103, 3), (107, 5), (109, 3), (113, 19), (127, 3), (131, 7), (137, 5), (139, 3), (149, 17), (151, 3), (157, 3), (163, 3), (167, 5), (173, 7), (179, 101), (181, 3), (191, 157), (193, 3), (197, 5), (199, 3), (211, 3), (223, 3), (227, 5), (229, 3), (233, 103), (239, 23), (241, 3), (251, 17), (257, 5), (263, 13), (269, 11), (271, 3), (277, 3), (281, 71), (283, 3), (293, 29), (307, 3), (311, 31), (313, 3), (317, 5), (331, 3), (337, 3), (347, 5), (349, 3), (353, 17), (359, 193), (367, 3), (373, 3), (379, 3), (383, 7)]

theorem row_18 : minGB 413572 = 389 :=
  minGB_eq_of_cert cert_18 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_18.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `503222 - x` for the primes `x < 523`. -/
def cert_19 : List (ℕ × ℕ) := [(2, 2), (3, 419), (5, 3), (7, 5), (11, 3), (13, 7), (17, 3), (19, 607), (23, 3), (29, 3), (31, 13), (37, 5), (41, 3), (43, 29), (47, 3), (53, 3), (59, 3), (61, 31), (67, 5), (71, 3), (73, 17), (79, 43), (83, 3), (89, 3), (97, 5), (101, 3), (103, 263), (107, 3), (109, 13), (113, 3), (127, 5), (131, 3), (137, 3), (139, 7), (149, 3), (151, 487), (157, 5), (163, 587), (167, 3), (173, 3), (179, 3), (181, 7), (191, 3), (193, 41), (197, 3), (199, 53), (211, 677), (223, 7), (227, 3), (229, 79), (233, 3), (239, 3), (241, 151), (251, 3), (257, 3), (263, 3), (269, 3), (271, 461), (277, 5), (281, 3), (283, 89), (293, 3), (307, 5), (311, 3), (313, 11), (317, 3), (331, 283), (337, 5), (347, 3), (349, 7), (353, 3), (359, 3), (367, 5), (373, 23), (379, 11), (383, 3), (389, 3), (397, 5), (401, 3), (409, 211), (419, 3), (421, 13), (431, 3), (433, 7), (439, 41), (443, 3), (449, 3), (457, 5), (461, 3), (463, 19), (467, 3), (479, 3), (487, 5), (491, 3), (499, 13), (503, 3), (509, 3), (521, 3)]

theorem row_19 : minGB 503222 = 523 :=
  minGB_eq_of_cert cert_19 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_19.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `1077422 - x` for the primes `x < 601`. -/
def cert_20 : List (ℕ × ℕ) := [(2, 2), (3, 7), (5, 3), (7, 5), (11, 3), (13, 17), (17, 3), (19, 37), (23, 3), (29, 3), (31, 7), (37, 5), (41, 3), (43, 29), (47, 3), (53, 3), (59, 3), (61, 293), (67, 5), (71, 3), (73, 7), (79, 23), (83, 3), (89, 3), (97, 5), (101, 3), (103, 19), (107, 3), (109, 223), (113, 3), (127, 5), (131, 3), (137, 3), (139, 71), (149, 3), (151, 13), (157, 5), (163, 577), (167, 3), (173, 3), (179, 3), (181, 11), (191, 3), (193, 113), (197, 3), (199, 7), (211, 757), (223, 61), (227, 3), (229, 13), (233, 3), (239, 3), (241, 7), (251, 3), (257, 3), (263, 3), (269, 3), (271, 449), (277, 5), (281, 3), (283, 7), (293, 3), (307, 5), (311, 3), (313, 11), (317, 3), (331, 19), (337, 5), (347, 3), (349, 281), (353, 3), (359, 3), (367, 5), (373, 191), (379, 11), (383, 3), (389, 3), (397, 5), (401, 3), (409, 7), (419, 3), (421, 17), (431, 3), (433, 89), (439, 167), (443, 3), (449, 3), (457, 5), (461, 3), (463, 13), (467, 3), (479, 3), (487, 5), (491, 3), (499, 503), (503, 3), (509, 3), (521, 3), (523, 17), (541, 13), (547, 5), (557, 3), (563, 3), (569, 3), (571, 373), (577, 5), (587, 3), (593, 3), (599, 3)]

theorem row_20 : minGB 1077422 = 601 :=
  minGB_eq_of_cert cert_20 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_20.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `3526958 - x` for the primes `x < 727`. -/
def cert_21 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 3), (7, 19), (11, 3), (13, 5), (17, 3), (19, 13), (23, 3), (29, 3), (31, 47), (37, 233), (41, 3), (43, 5), (47, 3), (53, 3), (59, 3), (61, 11), (67, 197), (71, 3), (73, 5), (79, 1399), (83, 3), (89, 3), (97, 13), (101, 3), (103, 5), (107, 3), (109, 73), (113, 3), (127, 7), (131, 3), (137, 3), (139, 101), (149, 3), (151, 409), (157, 251), (163, 5), (167, 3), (173, 3), (179, 3), (181, 29), (191, 3), (193, 5), (197, 3), (199, 1019), (211, 7), (223, 5), (227, 3), (229, 37), (233, 3), (239, 3), (241, 421), (251, 3), (257, 3), (263, 3), (269, 3), (271, 1237), (277, 149), (281, 3), (283, 5), (293, 3), (307, 131), (311, 3), (313, 5), (317, 3), (331, 13), (337, 7), (347, 3), (349, 19), (353, 3), (359, 3), (367, 31), (373, 5), (379, 7), (383, 3), (389, 3), (397, 347), (401, 3), (409, 13), (419, 3), (421, 7), (431, 3), (433, 5), (439, 1693), (443, 3), (449, 3), (457, 11), (461, 3), (463, 5), (467, 3), (479, 3), (487, 13), (491, 3), (499, 1259), (503, 3), (509, 3), (521, 3), (523, 5), (541, 877), (547, 7), (557, 3), (563, 3), (569, 3), (571, 43), (577, 19), (587, 3), (593, 3), (599, 3), (601, 71), (607, 1361), (613, 5), (617, 3), (619, 1447), (631, 7), (641, 3), (643, 5), (647, 3), (653, 3), (659, 3), (661, 257), (673, 5), (677, 3), (683, 3), (691, 19), (701, 3), (709, 53), (719, 3)]

theorem row_21 : minGB 3526958 = 727 :=
  minGB_eq_of_cert cert_21 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_21.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `3807404 - x` for the primes `x < 751`. -/
def cert_22 : List (ℕ × ℕ) := [(2, 2), (3, 13), (5, 3), (7, 11), (11, 3), (13, 7), (17, 3), (19, 5), (23, 3), (29, 3), (31, 1489), (37, 137), (41, 3), (43, 53), (47, 3), (53, 3), (59, 3), (61, 613), (67, 17), (71, 3), (73, 11), (79, 5), (83, 3), (89, 3), (97, 7), (101, 3), (103, 41), (107, 3), (109, 5), (113, 3), (127, 19), (131, 3), (137, 3), (139, 5), (149, 3), (151, 131), (157, 79), (163, 349), (167, 3), (173, 3), (179, 3), (181, 7), (191, 3), (193, 59), (197, 3), (199, 5), (211, 13), (223, 7), (227, 3), (229, 5), (233, 3), (239, 3), (241, 19), (251, 3), (257, 3), (263, 3), (269, 3), (271, 11), (277, 83), (281, 3), (283, 23), (293, 3), (307, 7), (311, 3), (313, 29), (317, 3), (331, 211), (337, 11), (347, 3), (349, 5), (353, 3), (359, 3), (367, 13), (373, 17), (379, 5), (383, 3), (389, 3), (397, 67), (401, 3), (409, 5), (419, 3), (421, 23), (431, 3), (433, 7), (439, 5), (443, 3), (449, 3), (457, 521), (461, 3), (463, 257), (467, 3), (479, 3), (487, 29), (491, 3), (499, 5), (503, 3), (509, 3), (521, 3), (523, 13), (541, 1193), (547, 59), (557, 3), (563, 3), (569, 3), (571, 43), (577, 17), (587, 3), (593, 3), (599, 3), (601, 7), (607, 89), (613, 101), (617, 3), (619, 5), (631, 79), (641, 3), (643, 7), (647, 3), (653, 3), (659, 3), (661, 29), (673, 73), (677, 3), (683, 3), (691, 1747), (701, 3), (709, 5), (719, 3), (727, 7), (733, 11), (739, 5), (743, 3)]

theorem row_22 : minGB 3807404 = 751 :=
  minGB_eq_of_cert cert_22 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_22.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `10759922 - x` for the primes `x < 829`. -/
def cert_23 : List (ℕ × ℕ) := [(2, 2), (3, 97), (5, 3), (7, 5), (11, 3), (13, 19), (17, 3), (19, 7), (23, 3), (29, 3), (31, 397), (37, 5), (41, 3), (43, 13), (47, 3), (53, 3), (59, 3), (61, 7), (67, 5), (71, 3), (73, 2887), (79, 137), (83, 3), (89, 3), (97, 5), (101, 3), (103, 7), (107, 3), (109, 107), (113, 3), (127, 5), (131, 3), (137, 3), (139, 29), (149, 3), (151, 11), (157, 5), (163, 17), (167, 3), (173, 3), (179, 3), (181, 907), (191, 3), (193, 61), (197, 3), (199, 13), (211, 37), (223, 23), (227, 3), (229, 7), (233, 3), (239, 3), (241, 19), (251, 3), (257, 3), (263, 3), (269, 3), (271, 7), (277, 5), (281, 3), (283, 11), (293, 3), (307, 5), (311, 3), (313, 7), (317, 3), (331, 829), (337, 5), (347, 3), (349, 11), (353, 3), (359, 3), (367, 5), (373, 197), (379, 73), (383, 3), (389, 3), (397, 5), (401, 3), (409, 271), (419, 3), (421, 419), (431, 3), (433, 13), (439, 7), (443, 3), (449, 3), (457, 5), (461, 3), (463, 2447), (467, 3), (479, 3), (487, 5), (491, 3), (499, 23), (503, 3), (509, 3), (521, 3), (523, 7), (541, 47), (547, 5), (557, 3), (563, 3), (569, 3), (571, 17), (577, 5), (587, 3), (593, 3), (599, 3), (601, 349), (607, 5), (613, 11), (617, 3), (619, 1423), (631, 487), (641, 3), (643, 461), (647, 3), (653, 3), (659, 3), (661, 29), (673, 17), (677, 3), (683, 3), (691, 7), (701, 3), (709, 467), (719, 3), (727, 5), (733, 7), (739, 181), (743, 3), (751, 107), (757, 5), (761, 3), (769, 179), (773, 3), (787, 5), (797, 3), (809, 3), (811, 11), (821, 3), (823, 13), (827, 3)]

theorem row_23 : minGB 10759922 = 829 :=
  minGB_eq_of_cert cert_23 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_23.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `24106882 - x` for the primes `x < 929`. -/
def cert_24 : List (ℕ × ℕ) := [(2, 2), (3, 157), (5, 19), (7, 3), (11, 31), (13, 3), (17, 5), (19, 3), (23, 7), (29, 1747), (31, 3), (37, 3), (41, 11), (43, 3), (47, 5), (53, 23), (59, 13), (61, 3), (67, 3), (71, 41), (73, 3), (79, 3), (83, 17), (89, 251), (97, 3), (101, 101), (103, 3), (107, 5), (109, 3), (113, 83), (127, 3), (131, 59), (137, 5), (139, 3), (149, 7), (151, 3), (157, 3), (163, 3), (167, 5), (173, 11), (179, 43), (181, 3), (191, 7), (193, 3), (197, 5), (199, 3), (211, 3), (223, 3), (227, 5), (229, 3), (233, 7), (239, 11), (241, 3), (251, 139), (257, 5), (263, 3391), (269, 79), (271, 3), (277, 3), (281, 229), (283, 3), (293, 13), (307, 3), (311, 73), (313, 3), (317, 5), (331, 3), (337, 3), (347, 5), (349, 3), (353, 61), (359, 7), (367, 3), (373, 3), (379, 3), (383, 31), (389, 17), (397, 3), (401, 7), (409, 3), (419, 997), (421, 3), (431, 89), (433, 3), (439, 3), (443, 7), (449, 13), (457, 3), (461, 19), (463, 3), (467, 5), (479, 113), (487, 3), (491, 17), (499, 3), (503, 11), (509, 3343), (521, 53), (523, 3), (541, 3), (547, 3), (557, 5), (563, 41), (569, 7), (571, 3), (577, 3), (587, 5), (593, 17), (599, 167), (601, 3), (607, 3), (613, 3), (617, 5), (619, 3), (631, 3), (641, 3779), (643, 3), (647, 5), (653, 7), (659, 103), (661, 3), (673, 3), (677, 5), (683, 13), (691, 3), (701, 11), (709, 3), (719, 29), (727, 3), (733, 3), (739, 3), (743, 23), (751, 3), (757, 3), (761, 13), (769, 3), (773, 137), (787, 3), (797, 5), (809, 41), (811, 3), (821, 7), (823, 3), (827, 5), (829, 3), (839, 13), (853, 3), (857, 5), (859, 3), (863, 7), (877, 3), (881, 23), (883, 3), (887, 5), (907, 3), (911, 47), (919, 3)]

theorem row_24 : minGB 24106882 = 929 :=
  minGB_eq_of_cert cert_24 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_24.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `27789878 - x` for the primes `x < 997`. -/
def cert_25 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 3), (7, 631), (11, 3), (13, 5), (17, 3), (19, 29), (23, 3), (29, 3), (31, 101), (37, 41), (41, 3), (43, 5), (47, 3), (53, 3), (59, 3), (61, 11), (67, 7), (71, 3), (73, 5), (79, 19), (83, 3), (89, 3), (97, 17), (101, 3), (103, 5), (107, 3), (109, 7), (113, 3), (127, 11), (131, 3), (137, 3), (139, 43), (149, 3), (151, 7), (157, 653), (163, 5), (167, 3), (173, 3), (179, 3), (181, 13), (191, 3), (193, 5), (197, 3), (199, 17), (211, 257), (223, 5), (227, 3), (229, 53), (233, 3), (239, 3), (241, 1787), (251, 3), (257, 3), (263, 3), (269, 3), (271, 367), (277, 7), (281, 3), (283, 5), (293, 3), (307, 19), (311, 3), (313, 5), (317, 3), (331, 31), (337, 13), (347, 3), (349, 1747), (353, 3), (359, 3), (367, 29), (373, 5), (379, 877), (383, 3), (389, 3), (397, 43), (401, 3), (409, 241), (419, 3), (421, 19), (431, 3), (433, 5), (439, 2777), (443, 3), (449, 3), (457, 11), (461, 3), (463, 5), (467, 3), (479, 3), (487, 7), (491, 3), (499, 229), (503, 3), (509, 3), (521, 3), (523, 5), (541, 29), (547, 37), (557, 3), (563, 3), (569, 3), (571, 7), (577, 167), (587, 3), (593, 3), (599, 3), (601, 79), (607, 17), (613, 5), (617, 3), (619, 2713), (631, 239), (641, 3), (643, 5), (647, 3), (653, 3), (659, 3), (661, 137), (673, 5), (677, 3), (683, 3), (691, 71), (701, 3), (709, 17), (719, 3), (727, 13), (733, 5), (739, 7), (743, 3), (751, 491), (757, 67), (761, 3), (769, 37), (773, 3), (787, 11), (797, 3), (809, 3), (811, 17), (821, 3), (823, 5), (827, 3), (829, 971), (839, 3), (853, 5), (857, 3), (859, 139), (863, 3), (877, 19), (881, 3), (883, 5), (887, 3), (907, 7), (911, 3), (919, 11), (929, 3), (937, 59), (941, 3), (947, 3), (953, 3), (967, 211), (971, 3), (977, 3), (983, 3), (991, 7)]

theorem row_25 : minGB 27789878 = 997 :=
  minGB_eq_of_cert cert_25 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_25.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `37998938 - x` for the primes `x < 1039`. -/
def cert_26 : List (ℕ × ℕ) := [(2, 2), (3, 5), (5, 3), (7, 173), (11, 3), (13, 5), (17, 3), (19, 7), (23, 3), (29, 3), (31, 661), (37, 31), (41, 3), (43, 5), (47, 3), (53, 3), (59, 3), (61, 7), (67, 3881), (71, 3), (73, 5), (79, 17), (83, 3), (89, 3), (97, 19), (101, 3), (103, 5), (107, 3), (109, 11), (113, 3), (127, 83), (131, 3), (137, 3), (139, 43), (149, 3), (151, 29), (157, 127), (163, 5), (167, 3), (173, 3), (179, 3), (181, 17), (191, 3), (193, 5), (197, 3), (199, 197), (211, 13), (223, 5), (227, 3), (229, 7), (233, 3), (239, 3), (241, 11), (251, 3), (257, 3), (263, 3), (269, 3), (271, 7), (277, 997), (281, 3), (283, 5), (293, 3), (307, 11), (311, 3), (313, 5), (317, 3), (331, 47), (337, 3187), (347, 3), (349, 107), (353, 3), (359, 3), (367, 13), (373, 5), (379, 563), (383, 3), (389, 3), (397, 7), (401, 3), (409, 31), (419, 3), (421, 4507), (431, 3), (433, 5), (439, 7), (443, 3), (449, 3), (457, 3137), (461, 3), (463, 5), (467, 3), (479, 3), (487, 17), (491, 3), (499, 29), (503, 3), (509, 3), (521, 3), (523, 5), (541, 113), (547, 1217), (557, 3), (563, 3), (569, 3), (571, 11), (577, 773), (587, 3), (593, 3), (599, 3), (601, 13), (607, 7), (613, 5), (617, 3), (619, 3461), (631, 1301), (641, 3), (643, 5), (647, 3), (653, 3), (659, 3), (661, 23), (673, 5), (677, 3), (683, 3), (691, 7), (701, 3), (709, 241), (719, 3), (727, 227), (733, 5), (739, 229), (743, 3), (751, 4451), (757, 13), (761, 3), (769, 11), (773, 3), (787, 1499), (797, 3), (809, 3), (811, 283), (821, 3), (823, 5), (827, 3), (829, 727), (839, 3), (853, 5), (857, 3), (859, 7), (863, 3), (877, 397), (881, 3), (883, 5), (887, 3), (907, 613), (911, 3), (919, 127), (929, 3), (937, 23), (941, 3), (947, 3), (953, 3), (967, 11), (971, 3), (977, 3), (983, 3), (991, 13), (997, 17), (1009, 19), (1013, 3), (1019, 3), (1021, 29), (1031, 3), (1033, 5)]

theorem row_26 : minGB 37998938 = 1039 :=
  minGB_eq_of_cert cert_26 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_26.sub le_rfl (by norm_num)) (by decide)

/-- Divisors of `60119912 - x` for the primes `x < 1093`. -/
def cert_27 : List (ℕ × ℕ) := [(2, 2), (3, 47), (5, 3), (7, 5), (11, 3), (13, 7), (17, 3), (19, 383), (23, 3), (29, 3), (31, 31), (37, 5), (41, 3), (43, 79), (47, 3), (53, 3), (59, 3), (61, 11), (67, 5), (71, 3), (73, 13), (79, 167), (83, 3), (89, 3), (97, 5), (101, 3), (103, 2719), (107, 3), (109, 17), (113, 3), (127, 5), (131, 3), (137, 3), (139, 7), (149, 3), (151, 13), (157, 5), (163, 173), (167, 3), (173, 3), (179, 3), (181, 7), (191, 3), (193, 11), (197, 3), (199, 109), (211, 17), (223, 7), (227, 3), (229, 13), (233, 3), (239, 3), (241, 283), (251, 3), (257, 3), (263, 3), (269, 3), (271, 127), (277, 5), (281, 3), (283, 19), (293, 3), (307, 5), (311, 3), (313, 17), (317, 3), (331, 29), (337, 5), (347, 3), (349, 7), (353, 3), (359, 3), (367, 5), (373, 23), (379, 47), (383, 3), (389, 3), (397, 5), (401, 3), (409, 113), (419, 3), (421, 1069), (431, 3), (433, 7), (439, 83), (443, 3), (449, 3), (457, 5), (461, 3), (463, 13), (467, 3), (479, 3), (487, 5), (491, 3), (499, 37), (503, 3), (509, 3), (521, 3), (523, 11), (541, 13), (547, 5), (557, 3), (563, 3), (569, 3), (571, 101), (577, 5), (587, 3), (593, 3), (599, 3), (601, 7), (607, 5), (613, 137), (617, 3), (619, 13), (631, 2969), (641, 3), (643, 7), (647, 3), (653, 3), (659, 3), (661, 47), (673, 223), (677, 3), (683, 3), (691, 61), (701, 3), (709, 43), (719, 3), (727, 5), (733, 71), (739, 19), (743, 3), (751, 41), (757, 5), (761, 3), (769, 7), (773, 3), (787, 5), (797, 3), (809, 3), (811, 7), (821, 3), (823, 17), (827, 3), (829, 4027), (839, 3), (853, 7), (857, 3), (859, 59), (863, 3), (877, 5), (881, 3), (883, 139), (887, 3), (907, 5), (911, 3), (919, 11), (929, 3), (937, 5), (941, 3), (947, 3), (953, 3), (967, 5), (971, 3), (977, 3), (983, 3), (991, 79), (997, 5), (1009, 13), (1013, 3), (1019, 3), (1021, 7), (1031, 3), (1033, 127), (1039, 4507), (1049, 3), (1051, 11), (1061, 3), (1063, 7), (1069, 2531), (1087, 5), (1091, 3)]

theorem row_27 : minGB 60119912 = 1093 :=
  minGB_eq_of_cert cert_27 (by norm_num) (by decide +kernel) (by decide +kernel)
    (seg_27.sub le_rfl (by norm_num)) (by decide)

theorem cum_0 : GBBound 6 10 3 := seg_0

theorem cum_1 : GBBound 6 28 5 :=
  GBBound.join (cum_0.mono (by norm_num)) seg_1 (by norm_num) (by decide)

theorem cum_2 : GBBound 6 96 7 :=
  GBBound.join (cum_1.mono (by norm_num)) seg_2 (by norm_num) (by decide)

theorem cum_3 : GBBound 6 218 19 :=
  GBBound.join (cum_2.mono (by norm_num)) seg_3 (by norm_num) (by decide)

theorem cum_4 : GBBound 6 306 23 :=
  GBBound.join (cum_3.mono (by norm_num)) seg_4 (by norm_num) (by decide)

theorem cum_5 : GBBound 6 554 31 :=
  GBBound.join (cum_4.mono (by norm_num)) seg_5 (by norm_num) (by decide)

theorem cum_6 : GBBound 6 990 47 :=
  GBBound.join (cum_5.mono (by norm_num)) seg_6 (by norm_num) (by decide)

theorem cum_7 : GBBound 6 2640 73 :=
  GBBound.join (cum_6.mono (by norm_num)) seg_7 (by norm_num) (by decide)

theorem cum_8 : GBBound 6 5370 103 :=
  GBBound.join (cum_7.mono (by norm_num)) seg_8 (by norm_num) (by decide)

theorem cum_9 : GBBound 6 7424 139 :=
  GBBound.join (cum_8.mono (by norm_num)) seg_9 (by norm_num) (by decide)

theorem cum_10 : GBBound 6 43530 173 :=
  GBBound.join (cum_9.mono (by norm_num)) seg_10 (by norm_num) (by decide)

theorem cum_11 : GBBound 6 54242 211 :=
  GBBound.join (cum_10.mono (by norm_num)) seg_11 (by norm_num) (by decide)

theorem cum_12 : GBBound 6 63272 233 :=
  GBBound.join (cum_11.mono (by norm_num)) seg_12 (by norm_num) (by decide)

theorem cum_13 : GBBound 6 113670 293 :=
  GBBound.join (cum_12.mono (by norm_num)) seg_13 (by norm_num) (by decide)

theorem cum_14 : GBBound 6 128166 313 :=
  GBBound.join (cum_13.mono (by norm_num)) seg_14 (by norm_num) (by decide)

theorem cum_15 : GBBound 6 194426 331 :=
  GBBound.join (cum_14.mono (by norm_num)) seg_15 (by norm_num) (by decide)

theorem cum_16 : GBBound 6 194468 359 :=
  GBBound.join (cum_15.mono (by norm_num)) seg_16 (by norm_num) (by decide)

theorem cum_17 : GBBound 6 413570 383 :=
  GBBound.join (cum_16.mono (by norm_num)) seg_17 (by norm_num) (by decide)

theorem cum_18 : GBBound 6 503220 389 :=
  GBBound.join (cum_17.mono (by norm_num)) seg_18 (by norm_num) (by decide)

theorem cum_19 : GBBound 6 1077420 523 :=
  GBBound.join (cum_18.mono (by norm_num)) seg_19 (by norm_num) (by decide)

theorem cum_20 : GBBound 6 3526956 601 :=
  GBBound.join (cum_19.mono (by norm_num)) seg_20 (by norm_num) (by decide)

theorem cum_21 : GBBound 6 3807402 727 :=
  GBBound.join (cum_20.mono (by norm_num)) seg_21 (by norm_num) (by decide)

theorem cum_22 : GBBound 6 10759920 751 :=
  GBBound.join (cum_21.mono (by norm_num)) seg_22 (by norm_num) (by decide)

theorem cum_23 : GBBound 6 24106880 829 :=
  GBBound.join (cum_22.mono (by norm_num)) seg_23 (by norm_num) (by decide)

theorem cum_24 : GBBound 6 27789876 929 :=
  GBBound.join (cum_23.mono (by norm_num)) seg_24 (by norm_num) (by decide)

theorem cum_25 : GBBound 6 37998936 997 :=
  GBBound.join (cum_24.mono (by norm_num)) seg_25 (by norm_num) (by decide)

theorem cum_26 : GBBound 6 60119910 1039 :=
  GBBound.join (cum_25.mono (by norm_num)) seg_26 (by norm_num) (by decide)

theorem cum_27 : GBBound 6 100000000 1093 :=
  GBBound.join (cum_26.mono (by norm_num)) seg_27 (by norm_num) (by decide)

theorem least_0 : ∀ m, Even m → 6 ≤ m → m < 6 → minGB m < 3 := by
  intro m hm h6 hlt
  omega

theorem least_1 : ∀ m, Even m → 6 ≤ m → m < 12 → minGB m < 5 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_0 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_2 : ∀ m, Even m → 6 ≤ m → m < 30 → minGB m < 7 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_1 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_3 : ∀ m, Even m → 6 ≤ m → m < 98 → minGB m < 19 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_2 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_4 : ∀ m, Even m → 6 ≤ m → m < 220 → minGB m < 23 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_3 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_5 : ∀ m, Even m → 6 ≤ m → m < 308 → minGB m < 31 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_4 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_6 : ∀ m, Even m → 6 ≤ m → m < 556 → minGB m < 47 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_5 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_7 : ∀ m, Even m → 6 ≤ m → m < 992 → minGB m < 73 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_6 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_8 : ∀ m, Even m → 6 ≤ m → m < 2642 → minGB m < 103 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_7 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_9 : ∀ m, Even m → 6 ≤ m → m < 5372 → minGB m < 139 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_8 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_10 : ∀ m, Even m → 6 ≤ m → m < 7426 → minGB m < 173 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_9 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_11 : ∀ m, Even m → 6 ≤ m → m < 43532 → minGB m < 211 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_10 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_12 : ∀ m, Even m → 6 ≤ m → m < 54244 → minGB m < 233 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_11 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_13 : ∀ m, Even m → 6 ≤ m → m < 63274 → minGB m < 293 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_12 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_14 : ∀ m, Even m → 6 ≤ m → m < 113672 → minGB m < 313 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_13 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_15 : ∀ m, Even m → 6 ≤ m → m < 128168 → minGB m < 331 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_14 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_16 : ∀ m, Even m → 6 ≤ m → m < 194428 → minGB m < 359 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_15 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_17 : ∀ m, Even m → 6 ≤ m → m < 194470 → minGB m < 383 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_16 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_18 : ∀ m, Even m → 6 ≤ m → m < 413572 → minGB m < 389 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_17 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_19 : ∀ m, Even m → 6 ≤ m → m < 503222 → minGB m < 523 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_18 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_20 : ∀ m, Even m → 6 ≤ m → m < 1077422 → minGB m < 601 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_19 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_21 : ∀ m, Even m → 6 ≤ m → m < 3526958 → minGB m < 727 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_20 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_22 : ∀ m, Even m → 6 ≤ m → m < 3807404 → minGB m < 751 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_21 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_23 : ∀ m, Even m → 6 ≤ m → m < 10759922 → minGB m < 829 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_22 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_24 : ∀ m, Even m → 6 ≤ m → m < 24106882 → minGB m < 929 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_23 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_25 : ∀ m, Even m → 6 ≤ m → m < 27789878 → minGB m < 997 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_24 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_26 : ∀ m, Even m → 6 ≤ m → m < 37998938 → minGB m < 1039 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_25 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

theorem least_27 : ∀ m, Even m → 6 ≤ m → m < 60119912 → minGB m < 1093 := by
  intro m hm h6 hlt
  have := (minGB_of_bound cum_26 hm h6 (by obtain ⟨k, hk⟩ := hm; omega)).2.2
  omega

/-- Every row of Table 4 with `n ≤ 10^8` is exact and is a record: `p(n)` equals the printed
`p`, and every even `m` with `6 ≤ m < n` has `p(m) < p`. -/
theorem table4_least : ∀ x ∈ table4, x.1 ≤ 100000000 →
    minGB x.1 = x.2 ∧ ∀ m, Even m → 6 ≤ m → m < x.1 → minGB m < x.2 := by
  intro x hx
  simp only [table4, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro _; exact ⟨row_0, least_0⟩
  · intro _; exact ⟨row_1, least_1⟩
  · intro _; exact ⟨row_2, least_2⟩
  · intro _; exact ⟨row_3, least_3⟩
  · intro _; exact ⟨row_4, least_4⟩
  · intro _; exact ⟨row_5, least_5⟩
  · intro _; exact ⟨row_6, least_6⟩
  · intro _; exact ⟨row_7, least_7⟩
  · intro _; exact ⟨row_8, least_8⟩
  · intro _; exact ⟨row_9, least_9⟩
  · intro _; exact ⟨row_10, least_10⟩
  · intro _; exact ⟨row_11, least_11⟩
  · intro _; exact ⟨row_12, least_12⟩
  · intro _; exact ⟨row_13, least_13⟩
  · intro _; exact ⟨row_14, least_14⟩
  · intro _; exact ⟨row_15, least_15⟩
  · intro _; exact ⟨row_16, least_16⟩
  · intro _; exact ⟨row_17, least_17⟩
  · intro _; exact ⟨row_18, least_18⟩
  · intro _; exact ⟨row_19, least_19⟩
  · intro _; exact ⟨row_20, least_20⟩
  · intro _; exact ⟨row_21, least_21⟩
  · intro _; exact ⟨row_22, least_22⟩
  · intro _; exact ⟨row_23, least_23⟩
  · intro _; exact ⟨row_24, least_24⟩
  · intro _; exact ⟨row_25, least_25⟩
  · intro _; exact ⟨row_26, least_26⟩
  · intro _; exact ⟨row_27, least_27⟩
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)

/-- Every even `m` with `6 ≤ m ≤ 10^8` has a Goldbach partition, and `p(m)` is at most the
`p` of a Table 4 row `(n, p)` with `n ≤ m`: no record below 10^8 is missing. -/
theorem table4_complete : ∀ m, Even m → 6 ≤ m → m ≤ 100000000 →
    (minGB m).Prime ∧ (m - minGB m).Prime ∧ ∃ x ∈ table4, x.1 ≤ m ∧ minGB m ≤ x.2 := by
  intro m hm h6 hmN
  obtain ⟨k, hk⟩ := id hm
  rcases Nat.lt_or_ge m 12 with h0 | h0
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_0 hm (by omega) (by omega)
    exact ⟨a, b, (6, 3), by simp [table4], show 6 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 30 with h1 | h1
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_1 hm (by omega) (by omega)
    exact ⟨a, b, (12, 5), by simp [table4], show 12 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 98 with h2 | h2
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_2 hm (by omega) (by omega)
    exact ⟨a, b, (30, 7), by simp [table4], show 30 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 220 with h3 | h3
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_3 hm (by omega) (by omega)
    exact ⟨a, b, (98, 19), by simp [table4], show 98 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 308 with h4 | h4
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_4 hm (by omega) (by omega)
    exact ⟨a, b, (220, 23), by simp [table4], show 220 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 556 with h5 | h5
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_5 hm (by omega) (by omega)
    exact ⟨a, b, (308, 31), by simp [table4], show 308 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 992 with h6 | h6
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_6 hm (by omega) (by omega)
    exact ⟨a, b, (556, 47), by simp [table4], show 556 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 2642 with h7 | h7
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_7 hm (by omega) (by omega)
    exact ⟨a, b, (992, 73), by simp [table4], show 992 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 5372 with h8 | h8
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_8 hm (by omega) (by omega)
    exact ⟨a, b, (2642, 103), by simp [table4], show 2642 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 7426 with h9 | h9
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_9 hm (by omega) (by omega)
    exact ⟨a, b, (5372, 139), by simp [table4], show 5372 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 43532 with h10 | h10
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_10 hm (by omega) (by omega)
    exact ⟨a, b, (7426, 173), by simp [table4], show 7426 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 54244 with h11 | h11
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_11 hm (by omega) (by omega)
    exact ⟨a, b, (43532, 211), by simp [table4], show 43532 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 63274 with h12 | h12
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_12 hm (by omega) (by omega)
    exact ⟨a, b, (54244, 233), by simp [table4], show 54244 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 113672 with h13 | h13
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_13 hm (by omega) (by omega)
    exact ⟨a, b, (63274, 293), by simp [table4], show 63274 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 128168 with h14 | h14
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_14 hm (by omega) (by omega)
    exact ⟨a, b, (113672, 313), by simp [table4], show 113672 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 194428 with h15 | h15
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_15 hm (by omega) (by omega)
    exact ⟨a, b, (128168, 331), by simp [table4], show 128168 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 194470 with h16 | h16
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_16 hm (by omega) (by omega)
    exact ⟨a, b, (194428, 359), by simp [table4], show 194428 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 413572 with h17 | h17
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_17 hm (by omega) (by omega)
    exact ⟨a, b, (194470, 383), by simp [table4], show 194470 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 503222 with h18 | h18
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_18 hm (by omega) (by omega)
    exact ⟨a, b, (413572, 389), by simp [table4], show 413572 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 1077422 with h19 | h19
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_19 hm (by omega) (by omega)
    exact ⟨a, b, (503222, 523), by simp [table4], show 503222 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 3526958 with h20 | h20
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_20 hm (by omega) (by omega)
    exact ⟨a, b, (1077422, 601), by simp [table4], show 1077422 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 3807404 with h21 | h21
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_21 hm (by omega) (by omega)
    exact ⟨a, b, (3526958, 727), by simp [table4], show 3526958 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 10759922 with h22 | h22
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_22 hm (by omega) (by omega)
    exact ⟨a, b, (3807404, 751), by simp [table4], show 3807404 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 24106882 with h23 | h23
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_23 hm (by omega) (by omega)
    exact ⟨a, b, (10759922, 829), by simp [table4], show 10759922 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 27789878 with h24 | h24
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_24 hm (by omega) (by omega)
    exact ⟨a, b, (24106882, 929), by simp [table4], show 24106882 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 37998938 with h25 | h25
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_25 hm (by omega) (by omega)
    exact ⟨a, b, (27789878, 997), by simp [table4], show 27789878 ≤ m by omega, c⟩
  rcases Nat.lt_or_ge m 60119912 with h26 | h26
  · obtain ⟨a, b, c⟩ := minGB_of_bound seg_26 hm (by omega) (by omega)
    exact ⟨a, b, (37998938, 1039), by simp [table4], show 37998938 ≤ m by omega, c⟩
  obtain ⟨a, b, c⟩ := minGB_of_bound seg_27 hm (by omega) (by omega)
  exact ⟨a, b, (60119912, 1093), by simp [table4], show 60119912 ≤ m by omega, c⟩

end LeanLab.OeSHP2014
