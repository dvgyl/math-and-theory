import InfoE3.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace InfoE3

/-- The prescribed CI model has no numerically self-adhesive real-valued
polymatroid realization. The proof uses only literal submodularity,
normalization, equal numerical copy restrictions, and two adhesions. -/
theorem no_selfadhesive_inducer : ¬ HasSelfAdhesiveInducer := by
  rintro ⟨h, hp, hm, hs⟩
  obtain ⟨g12, p12, l12, r12, a12⟩ := hs (12 : Mask 5)
  obtain ⟨g25, p25, l25, r25, a25⟩ := hs (25 : Mask 5)
  have n0 : 0 ≤ (h 1 + h 2 - h 0 - h 3) := by
    have hh := hp.submod (1 : Mask 5) (2 : Mask 5)
    change h 0 + h 3 ≤ h 1 + h 2 at hh
    linarith only [hh]
  have n1 : 0 ≤ (h 19 + h 22 - h 18 - h 23) := by
    have hh := hp.submod (19 : Mask 5) (22 : Mask 5)
    change h 18 + h 23 ≤ h 19 + h 22 at hh
    linarith only [hh]
  have n2 : 0 ≤ (h 7 + h 14 - h 6 - h 15) := by
    have hh := hp.submod (7 : Mask 5) (14 : Mask 5)
    change h 6 + h 15 ≤ h 7 + h 14 at hh
    linarith only [hh]
  have n3 : 0 ≤ (h 22 + h 26 - h 18 - h 30) := by
    have hh := hp.submod (22 : Mask 5) (26 : Mask 5)
    change h 18 + h 30 ≤ h 22 + h 26 at hh
    linarith only [hh]
  have n4 : 0 ≤ (h 12 + h 20 - h 4 - h 28) := by
    have hh := hp.submod (12 : Mask 5) (20 : Mask 5)
    change h 4 + h 28 ≤ h 12 + h 20 at hh
    linarith only [hh]
  have n5 : 0 ≤ (g12 49 + g12 52 - g12 48 - g12 53) := by
    have hh := p12.submod (49 : Mask 8) (52 : Mask 8)
    change g12 48 + g12 53 ≤ g12 49 + g12 52 at hh
    linarith only [hh]
  have n6 : 0 ≤ (g12 5 + g12 36 - g12 4 - g12 37) := by
    have hh := p12.submod (5 : Mask 8) (36 : Mask 8)
    change g12 4 + g12 37 ≤ g12 5 + g12 36 at hh
    linarith only [hh]
  have n7 : 0 ≤ (g12 9 + g12 40 - g12 8 - g12 41) := by
    have hh := p12.submod (9 : Mask 8) (40 : Mask 8)
    change g12 8 + g12 41 ≤ g12 9 + g12 40 at hh
    linarith only [hh]
  have n8 : 0 ≤ (g12 31 + g12 62 - g12 30 - g12 63) := by
    have hh := p12.submod (31 : Mask 8) (62 : Mask 8)
    change g12 30 + g12 63 ≤ g12 31 + g12 62 at hh
    linarith only [hh]
  have n9 : 0 ≤ (g12 45 + g12 108 - g12 44 - g12 109) := by
    have hh := p12.submod (45 : Mask 8) (108 : Mask 8)
    change g12 44 + g12 109 ≤ g12 45 + g12 108 at hh
    linarith only [hh]
  have n10 : 0 ≤ (g12 189 + g12 252 - g12 188 - g12 253) := by
    have hh := p12.submod (189 : Mask 8) (252 : Mask 8)
    change g12 188 + g12 253 ≤ g12 189 + g12 252 at hh
    linarith only [hh]
  have n11 : 0 ≤ (g12 191 + g12 254 - g12 190 - g12 255) := by
    have hh := p12.submod (191 : Mask 8) (254 : Mask 8)
    change g12 190 + g12 255 ≤ g12 191 + g12 254 at hh
    linarith only [hh]
  have n12 : 0 ≤ (g12 61 + g12 188 - g12 60 - g12 189) := by
    have hh := p12.submod (61 : Mask 8) (188 : Mask 8)
    change g12 60 + g12 189 ≤ g12 61 + g12 188 at hh
    linarith only [hh]
  have n13 : 0 ≤ (g12 63 + g12 190 - g12 62 - g12 191) := by
    have hh := p12.submod (63 : Mask 8) (190 : Mask 8)
    change g12 62 + g12 191 ≤ g12 63 + g12 190 at hh
    linarith only [hh]
  have n14 : 0 ≤ (g12 125 + g12 252 - g12 124 - g12 253) := by
    have hh := p12.submod (125 : Mask 8) (252 : Mask 8)
    change g12 124 + g12 253 ≤ g12 125 + g12 252 at hh
    linarith only [hh]
  have n15 : 0 ≤ (g12 23 + g12 53 - g12 21 - g12 55) := by
    have hh := p12.submod (23 : Mask 8) (53 : Mask 8)
    change g12 21 + g12 55 ≤ g12 23 + g12 53 at hh
    linarith only [hh]
  have n16 : 0 ≤ (g12 79 + g12 109 - g12 77 - g12 111) := by
    have hh := p12.submod (79 : Mask 8) (109 : Mask 8)
    change g12 77 + g12 111 ≤ g12 79 + g12 109 at hh
    linarith only [hh]
  have n17 : 0 ≤ (g12 94 + g12 124 - g12 92 - g12 126) := by
    have hh := p12.submod (94 : Mask 8) (124 : Mask 8)
    change g12 92 + g12 126 ≤ g12 94 + g12 124 at hh
    linarith only [hh]
  have n18 : 0 ≤ (g12 30 + g12 92 - g12 28 - g12 94) := by
    have hh := p12.submod (30 : Mask 8) (92 : Mask 8)
    change g12 28 + g12 94 ≤ g12 30 + g12 92 at hh
    linarith only [hh]
  have n19 : 0 ≤ (g12 31 + g12 93 - g12 29 - g12 95) := by
    have hh := p12.submod (31 : Mask 8) (93 : Mask 8)
    change g12 29 + g12 95 ≤ g12 31 + g12 93 at hh
    linarith only [hh]
  have n20 : 0 ≤ (g12 191 + g12 253 - g12 189 - g12 255) := by
    have hh := p12.submod (191 : Mask 8) (253 : Mask 8)
    change g12 189 + g12 255 ≤ g12 191 + g12 253 at hh
    linarith only [hh]
  have n21 : 0 ≤ (g12 46 + g12 172 - g12 44 - g12 174) := by
    have hh := p12.submod (46 : Mask 8) (172 : Mask 8)
    change g12 44 + g12 174 ≤ g12 46 + g12 172 at hh
    linarith only [hh]
  have n22 : 0 ≤ (g12 63 + g12 189 - g12 61 - g12 191) := by
    have hh := p12.submod (63 : Mask 8) (189 : Mask 8)
    change g12 61 + g12 191 ≤ g12 63 + g12 189 at hh
    linarith only [hh]
  have n23 : 0 ≤ (g12 127 + g12 253 - g12 125 - g12 255) := by
    have hh := p12.submod (127 : Mask 8) (253 : Mask 8)
    change g12 125 + g12 255 ≤ g12 127 + g12 253 at hh
    linarith only [hh]
  have n24 : 0 ≤ (g12 37 + g12 41 - g12 33 - g12 45) := by
    have hh := p12.submod (37 : Mask 8) (41 : Mask 8)
    change g12 33 + g12 45 ≤ g12 37 + g12 41 at hh
    linarith only [hh]
  have n25 : 0 ≤ (g12 28 + g12 56 - g12 24 - g12 60) := by
    have hh := p12.submod (28 : Mask 8) (56 : Mask 8)
    change g12 24 + g12 60 ≤ g12 28 + g12 56 at hh
    linarith only [hh]
  have n26 : 0 ≤ (g12 40 + g12 48 - g12 32 - g12 56) := by
    have hh := p12.submod (40 : Mask 8) (48 : Mask 8)
    change g12 32 + g12 56 ≤ g12 40 + g12 48 at hh
    linarith only [hh]
  have n27 : 0 ≤ (g12 31 + g12 55 - g12 23 - g12 63) := by
    have hh := p12.submod (31 : Mask 8) (55 : Mask 8)
    change g12 23 + g12 63 ≤ g12 31 + g12 55 at hh
    linarith only [hh]
  have n28 : 0 ≤ (g12 17 + g12 33 - g12 1 - g12 49) := by
    have hh := p12.submod (17 : Mask 8) (33 : Mask 8)
    change g12 1 + g12 49 ≤ g12 17 + g12 33 at hh
    linarith only [hh]
  have n29 : 0 ≤ (g12 20 + g12 36 - g12 4 - g12 52) := by
    have hh := p12.submod (20 : Mask 8) (36 : Mask 8)
    change g12 4 + g12 52 ≤ g12 20 + g12 36 at hh
    linarith only [hh]
  have n30 : 0 ≤ (g12 95 + g12 111 - g12 79 - g12 127) := by
    have hh := p12.submod (95 : Mask 8) (111 : Mask 8)
    change g12 79 + g12 127 ≤ g12 95 + g12 111 at hh
    linarith only [hh]
  have n31 : 0 ≤ (g12 29 + g12 77 - g12 13 - g12 93) := by
    have hh := p12.submod (29 : Mask 8) (77 : Mask 8)
    change g12 13 + g12 93 ≤ g12 29 + g12 77 at hh
    linarith only [hh]
  have n32 : 0 ≤ (g12 188 + g12 236 - g12 172 - g12 252) := by
    have hh := p12.submod (188 : Mask 8) (236 : Mask 8)
    change g12 172 + g12 252 ≤ g12 188 + g12 236 at hh
    linarith only [hh]
  have n33 : 0 ≤ (g12 60 + g12 172 - g12 44 - g12 188) := by
    have hh := p12.submod (60 : Mask 8) (172 : Mask 8)
    change g12 44 + g12 188 ≤ g12 60 + g12 172 at hh
    linarith only [hh]
  have n34 : 0 ≤ (g12 126 + g12 238 - g12 110 - g12 254) := by
    have hh := p12.submod (126 : Mask 8) (238 : Mask 8)
    change g12 110 + g12 254 ≤ g12 126 + g12 238 at hh
    linarith only [hh]
  have n35 : 0 ≤ (g12 110 + g12 174 - g12 46 - g12 238) := by
    have hh := p12.submod (110 : Mask 8) (174 : Mask 8)
    change g12 46 + g12 238 ≤ g12 110 + g12 174 at hh
    linarith only [hh]
  have n36 : 0 ≤ (g25 121 + g25 122 - g25 120 - g25 123) := by
    have hh := p25.submod (121 : Mask 7) (122 : Mask 7)
    change g25 120 + g25 123 ≤ g25 121 + g25 122 at hh
    linarith only [hh]
  have n37 : 0 ≤ (g25 43 + g25 58 - g25 42 - g25 59) := by
    have hh := p25.submod (43 : Mask 7) (58 : Mask 7)
    change g25 42 + g25 59 ≤ g25 43 + g25 58 at hh
    linarith only [hh]
  have n38 : 0 ≤ (g25 11 + g25 74 - g25 10 - g25 75) := by
    have hh := p25.submod (11 : Mask 7) (74 : Mask 7)
    change g25 10 + g25 75 ≤ g25 11 + g25 74 at hh
    linarith only [hh]
  have n39 : 0 ≤ (g25 107 + g25 121 - g25 105 - g25 123) := by
    have hh := p25.submod (107 : Mask 7) (121 : Mask 7)
    change g25 105 + g25 123 ≤ g25 107 + g25 121 at hh
    linarith only [hh]
  have n40 : 0 ≤ (g25 11 + g25 41 - g25 9 - g25 43) := by
    have hh := p25.submod (11 : Mask 7) (41 : Mask 7)
    change g25 9 + g25 43 ≤ g25 11 + g25 41 at hh
    linarith only [hh]
  have n41 : 0 ≤ (g25 26 + g25 56 - g25 24 - g25 58) := by
    have hh := p25.submod (26 : Mask 7) (56 : Mask 7)
    change g25 24 + g25 58 ≤ g25 26 + g25 56 at hh
    linarith only [hh]
  have n42 : 0 ≤ (g25 75 + g25 105 - g25 73 - g25 107) := by
    have hh := p25.submod (75 : Mask 7) (105 : Mask 7)
    change g25 73 + g25 107 ≤ g25 75 + g25 105 at hh
    linarith only [hh]
  have n43 : 0 ≤ (g25 26 + g25 88 - g25 24 - g25 90) := by
    have hh := p25.submod (26 : Mask 7) (88 : Mask 7)
    change g25 24 + g25 90 ≤ g25 26 + g25 88 at hh
    linarith only [hh]
  have n44 : 0 ≤ (g25 42 + g25 104 - g25 40 - g25 106) := by
    have hh := p25.submod (42 : Mask 7) (104 : Mask 7)
    change g25 40 + g25 106 ≤ g25 42 + g25 104 at hh
    linarith only [hh]
  have n45 : 0 ≤ (g25 63 + g25 125 - g25 61 - g25 127) := by
    have hh := p25.submod (63 : Mask 7) (125 : Mask 7)
    change g25 61 + g25 127 ≤ g25 63 + g25 125 at hh
    linarith only [hh]
  have n46 : 0 ≤ (g25 31 + g25 59 - g25 27 - g25 63) := by
    have hh := p25.submod (31 : Mask 7) (59 : Mask 7)
    change g25 27 + g25 63 ≤ g25 31 + g25 59 at hh
    linarith only [hh]
  have n47 : 0 ≤ (g25 95 + g25 123 - g25 91 - g25 127) := by
    have hh := p25.submod (95 : Mask 7) (123 : Mask 7)
    change g25 91 + g25 127 ≤ g25 95 + g25 123 at hh
    linarith only [hh]
  have n48 : 0 ≤ (g25 31 + g25 91 - g25 27 - g25 95) := by
    have hh := p25.submod (31 : Mask 7) (91 : Mask 7)
    change g25 27 + g25 95 ≤ g25 31 + g25 91 at hh
    linarith only [hh]
  have n49 : 0 ≤ (g25 61 + g25 121 - g25 57 - g25 125) := by
    have hh := p25.submod (61 : Mask 7) (121 : Mask 7)
    change g25 57 + g25 125 ≤ g25 61 + g25 121 at hh
    linarith only [hh]
  have n50 : 0 ≤ (g25 90 + g25 106 - g25 74 - g25 122) := by
    have hh := p25.submod (90 : Mask 7) (106 : Mask 7)
    change g25 74 + g25 122 ≤ g25 90 + g25 106 at hh
    linarith only [hh]
  have eadh12 : (g12 31 + g12 236 - g12 255 - g12 12) = 0 := by
    change g12 31 + g12 236 = g12 255 + g12 12 at a12
    linarith only [a12]
  have eadh25 : (g25 31 + g25 121 - g25 127 - g25 25) = 0 := by
    change g25 31 + g25 121 = g25 127 + g25 25 at a25
    linarith only [a25]
  have z6 : (h 25 + h 26 - h 24 - h 27) = 0 := by
    have hh := (hm (6 : Fin 80)).mpr (by decide)
    change (h 25 + h 26 - h 24 - h 27) = 0 at hh
    exact hh
  have z10 : (h 9 + h 12 - h 8 - h 13) = 0 := by
    have hh := (hm (10 : Fin 80)).mpr (by decide)
    change (h 9 + h 12 - h 8 - h 13) = 0 at hh
    exact hh
  have z11 : (h 17 + h 20 - h 16 - h 21) = 0 := by
    have hh := (hm (11 : Fin 80)).mpr (by decide)
    change (h 17 + h 20 - h 16 - h 21) = 0 at hh
    exact hh
  have z12 : (h 11 + h 14 - h 10 - h 15) = 0 := by
    have hh := (hm (12 : Fin 80)).mpr (by decide)
    change (h 11 + h 14 - h 10 - h 15) = 0 at hh
    exact hh
  have z18 : (h 5 + h 12 - h 4 - h 13) = 0 := by
    have hh := (hm (18 : Fin 80)).mpr (by decide)
    change (h 5 + h 12 - h 4 - h 13) = 0 at hh
    exact hh
  have z21 : (h 19 + h 26 - h 18 - h 27) = 0 := by
    have hh := (hm (21 : Fin 80)).mpr (by decide)
    change (h 19 + h 26 - h 18 - h 27) = 0 at hh
    exact hh
  have z26 : (h 5 + h 20 - h 4 - h 21) = 0 := by
    have hh := (hm (26 : Fin 80)).mpr (by decide)
    change (h 5 + h 20 - h 4 - h 21) = 0 at hh
    exact hh
  have z40 : (h 2 + h 8 - h 0 - h 10) = 0 := by
    have hh := (hm (40 : Fin 80)).mpr (by decide)
    change (h 2 + h 8 - h 0 - h 10) = 0 at hh
    exact hh
  have z48 : (h 2 + h 16 - h 0 - h 18) = 0 := by
    have hh := (hm (48 : Fin 80)).mpr (by decide)
    change (h 2 + h 16 - h 0 - h 18) = 0 at hh
    exact hh
  have z55 : (h 15 + h 29 - h 13 - h 31) = 0 := by
    have hh := (hm (55 : Fin 80)).mpr (by decide)
    change (h 15 + h 29 - h 13 - h 31) = 0 at hh
    exact hh
  have z60 : (h 7 + h 11 - h 3 - h 15) = 0 := by
    have hh := (hm (60 : Fin 80)).mpr (by decide)
    change (h 7 + h 11 - h 3 - h 15) = 0 at hh
    exact hh
  have z78 : (h 14 + h 22 - h 6 - h 30) = 0 := by
    have hh := (hm (78 : Fin 80)).mpr (by decide)
    change (h 14 + h 22 - h 6 - h 30) = 0 at hh
    exact hh
  have v12_1 : g12 1 = h 1 := by
    have hh := congrFun l12 (1 : Mask 5)
    change g12 1 = h 1 at hh
    exact hh
  have v12_4 : g12 4 = h 4 := by
    have hh := congrFun l12 (4 : Mask 5)
    change g12 4 = h 4 at hh
    exact hh
  have v12_5 : g12 5 = h 5 := by
    have hh := congrFun l12 (5 : Mask 5)
    change g12 5 = h 5 at hh
    exact hh
  have v12_8 : g12 8 = h 8 := by
    have hh := congrFun l12 (8 : Mask 5)
    change g12 8 = h 8 at hh
    exact hh
  have v12_9 : g12 9 = h 9 := by
    have hh := congrFun l12 (9 : Mask 5)
    change g12 9 = h 9 at hh
    exact hh
  have v12_12 : g12 12 = h 12 := by
    have hh := congrFun l12 (12 : Mask 5)
    change g12 12 = h 12 at hh
    exact hh
  have v12_13 : g12 13 = h 13 := by
    have hh := congrFun l12 (13 : Mask 5)
    change g12 13 = h 13 at hh
    exact hh
  have v12_17 : g12 17 = h 17 := by
    have hh := congrFun l12 (17 : Mask 5)
    change g12 17 = h 17 at hh
    exact hh
  have v12_20 : g12 20 = h 20 := by
    have hh := congrFun l12 (20 : Mask 5)
    change g12 20 = h 20 at hh
    exact hh
  have v12_21 : g12 21 = h 21 := by
    have hh := congrFun l12 (21 : Mask 5)
    change g12 21 = h 21 at hh
    exact hh
  have v12_23 : g12 23 = h 23 := by
    have hh := congrFun l12 (23 : Mask 5)
    change g12 23 = h 23 at hh
    exact hh
  have v12_24 : g12 24 = h 24 := by
    have hh := congrFun l12 (24 : Mask 5)
    change g12 24 = h 24 at hh
    exact hh
  have v12_28 : g12 28 = h 28 := by
    have hh := congrFun l12 (28 : Mask 5)
    change g12 28 = h 28 at hh
    exact hh
  have v12_29 : g12 29 = h 29 := by
    have hh := congrFun l12 (29 : Mask 5)
    change g12 29 = h 29 at hh
    exact hh
  have v12_30 : g12 30 = h 30 := by
    have hh := congrFun l12 (30 : Mask 5)
    change g12 30 = h 30 at hh
    exact hh
  have v12_31 : g12 31 = h 31 := by
    have hh := congrFun l12 (31 : Mask 5)
    change g12 31 = h 31 at hh
    exact hh
  have v12_32 : g12 32 = h 1 := by
    have hh := congrFun r12 (1 : Mask 5)
    change g12 32 = h 1 at hh
    exact hh
  have v12_36 : g12 36 = h 5 := by
    have hh := congrFun r12 (5 : Mask 5)
    change g12 36 = h 5 at hh
    exact hh
  have v12_40 : g12 40 = h 9 := by
    have hh := congrFun r12 (9 : Mask 5)
    change g12 40 = h 9 at hh
    exact hh
  have v12_44 : g12 44 = h 13 := by
    have hh := congrFun r12 (13 : Mask 5)
    change g12 44 = h 13 at hh
    exact hh
  have v12_108 : g12 108 = h 15 := by
    have hh := congrFun r12 (15 : Mask 5)
    change g12 108 = h 15 at hh
    exact hh
  have v12_172 : g12 172 = h 29 := by
    have hh := congrFun r12 (29 : Mask 5)
    change g12 172 = h 29 at hh
    exact hh
  have v12_236 : g12 236 = h 31 := by
    have hh := congrFun r12 (31 : Mask 5)
    change g12 236 = h 31 at hh
    exact hh
  have v25_9 : g25 9 = h 9 := by
    have hh := congrFun l25 (9 : Mask 5)
    change g25 9 = h 9 at hh
    exact hh
  have v25_10 : g25 10 = h 10 := by
    have hh := congrFun l25 (10 : Mask 5)
    change g25 10 = h 10 at hh
    exact hh
  have v25_11 : g25 11 = h 11 := by
    have hh := congrFun l25 (11 : Mask 5)
    change g25 11 = h 11 at hh
    exact hh
  have v25_24 : g25 24 = h 24 := by
    have hh := congrFun l25 (24 : Mask 5)
    change g25 24 = h 24 at hh
    exact hh
  have v25_25 : g25 25 = h 25 := by
    have hh := congrFun l25 (25 : Mask 5)
    change g25 25 = h 25 at hh
    exact hh
  have v25_26 : g25 26 = h 26 := by
    have hh := congrFun l25 (26 : Mask 5)
    change g25 26 = h 26 at hh
    exact hh
  have v25_27 : g25 27 = h 27 := by
    have hh := congrFun l25 (27 : Mask 5)
    change g25 27 = h 27 at hh
    exact hh
  have v25_31 : g25 31 = h 31 := by
    have hh := congrFun l25 (31 : Mask 5)
    change g25 31 = h 31 at hh
    exact hh
  have v25_40 : g25 40 = h 10 := by
    have hh := congrFun r25 (10 : Mask 5)
    change g25 40 = h 10 at hh
    exact hh
  have v25_41 : g25 41 = h 11 := by
    have hh := congrFun r25 (11 : Mask 5)
    change g25 41 = h 11 at hh
    exact hh
  have v25_56 : g25 56 = h 26 := by
    have hh := congrFun r25 (26 : Mask 5)
    change g25 56 = h 26 at hh
    exact hh
  have v25_57 : g25 57 = h 27 := by
    have hh := congrFun r25 (27 : Mask 5)
    change g25 57 = h 27 at hh
    exact hh
  have v25_73 : g25 73 = h 13 := by
    have hh := congrFun r25 (13 : Mask 5)
    change g25 73 = h 13 at hh
    exact hh
  have v25_88 : g25 88 = h 28 := by
    have hh := congrFun r25 (28 : Mask 5)
    change g25 88 = h 28 at hh
    exact hh
  have v25_104 : g25 104 = h 14 := by
    have hh := congrFun r25 (14 : Mask 5)
    change g25 104 = h 14 at hh
    exact hh
  have v25_105 : g25 105 = h 15 := by
    have hh := congrFun r25 (15 : Mask 5)
    change g25 105 = h 15 at hh
    exact hh
  have v25_120 : g25 120 = h 30 := by
    have hh := congrFun r25 (30 : Mask 5)
    change g25 120 = h 30 at hh
    exact hh
  have v25_121 : g25 121 = h 31 := by
    have hh := congrFun r25 (31 : Mask 5)
    change g25 121 = h 31 at hh
    exact hh
  have hsum : 0 ≤ 2 * (h 1 + h 2 - h 0 - h 3) + (h 19 + h 22 - h 18 - h 23) + 2 * (h 7 + h 14 - h 6 - h 15) + (h 22 + h 26 - h 18 - h 30) + (h 12 + h 20 - h 4 - h 28) + (g12 49 + g12 52 - g12 48 - g12 53) + (g12 5 + g12 36 - g12 4 - g12 37) + (g12 9 + g12 40 - g12 8 - g12 41) + (g12 31 + g12 62 - g12 30 - g12 63) + (g12 45 + g12 108 - g12 44 - g12 109) + (g12 189 + g12 252 - g12 188 - g12 253) + (g12 191 + g12 254 - g12 190 - g12 255) + (g12 61 + g12 188 - g12 60 - g12 189) + (g12 63 + g12 190 - g12 62 - g12 191) + (g12 125 + g12 252 - g12 124 - g12 253) + (g12 23 + g12 53 - g12 21 - g12 55) + (g12 79 + g12 109 - g12 77 - g12 111) + (g12 94 + g12 124 - g12 92 - g12 126) + (g12 30 + g12 92 - g12 28 - g12 94) + (g12 31 + g12 93 - g12 29 - g12 95) + (g12 191 + g12 253 - g12 189 - g12 255) + (g12 46 + g12 172 - g12 44 - g12 174) + (g12 63 + g12 189 - g12 61 - g12 191) + (g12 127 + g12 253 - g12 125 - g12 255) + (g12 37 + g12 41 - g12 33 - g12 45) + (g12 28 + g12 56 - g12 24 - g12 60) + (g12 40 + g12 48 - g12 32 - g12 56) + (g12 31 + g12 55 - g12 23 - g12 63) + (g12 17 + g12 33 - g12 1 - g12 49) + (g12 20 + g12 36 - g12 4 - g12 52) + (g12 95 + g12 111 - g12 79 - g12 127) + (g12 29 + g12 77 - g12 13 - g12 93) + 2 * (g12 188 + g12 236 - g12 172 - g12 252) + 2 * (g12 60 + g12 172 - g12 44 - g12 188) + (g12 126 + g12 238 - g12 110 - g12 254) + (g12 110 + g12 174 - g12 46 - g12 238) + (g25 121 + g25 122 - g25 120 - g25 123) + (g25 43 + g25 58 - g25 42 - g25 59) + (g25 11 + g25 74 - g25 10 - g25 75) + (g25 107 + g25 121 - g25 105 - g25 123) + (g25 11 + g25 41 - g25 9 - g25 43) + (g25 26 + g25 56 - g25 24 - g25 58) + (g25 75 + g25 105 - g25 73 - g25 107) + (g25 26 + g25 88 - g25 24 - g25 90) + (g25 42 + g25 104 - g25 40 - g25 106) + (g25 63 + g25 125 - g25 61 - g25 127) + (g25 31 + g25 59 - g25 27 - g25 63) + 2 * (g25 95 + g25 123 - g25 91 - g25 127) + 2 * (g25 31 + g25 91 - g25 27 - g25 95) + (g25 61 + g25 121 - g25 57 - g25 125) + (g25 90 + g25 106 - g25 74 - g25 122) := by
    exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) n0) n1) (mul_nonneg (by norm_num) n2)) n3) n4) n5) n6) n7) n8) n9) n10) n11) n12) n13) n14) n15) n16) n17) n18) n19) n20) n21) n22) n23) n24) n25) n26) n27) n28) n29) n30) n31) (mul_nonneg (by norm_num) n32)) (mul_nonneg (by norm_num) n33)) n34) n35) n36) n37) n38) n39) n40) n41) n42) n43) n44) n45) n46) (mul_nonneg (by norm_num) n47)) (mul_nonneg (by norm_num) n48)) n49) n50)
  have hid : (h 23 + h 29 - h 21 - h 31) + (2 * (h 1 + h 2 - h 0 - h 3) + (h 19 + h 22 - h 18 - h 23) + 2 * (h 7 + h 14 - h 6 - h 15) + (h 22 + h 26 - h 18 - h 30) + (h 12 + h 20 - h 4 - h 28) + (g12 49 + g12 52 - g12 48 - g12 53) + (g12 5 + g12 36 - g12 4 - g12 37) + (g12 9 + g12 40 - g12 8 - g12 41) + (g12 31 + g12 62 - g12 30 - g12 63) + (g12 45 + g12 108 - g12 44 - g12 109) + (g12 189 + g12 252 - g12 188 - g12 253) + (g12 191 + g12 254 - g12 190 - g12 255) + (g12 61 + g12 188 - g12 60 - g12 189) + (g12 63 + g12 190 - g12 62 - g12 191) + (g12 125 + g12 252 - g12 124 - g12 253) + (g12 23 + g12 53 - g12 21 - g12 55) + (g12 79 + g12 109 - g12 77 - g12 111) + (g12 94 + g12 124 - g12 92 - g12 126) + (g12 30 + g12 92 - g12 28 - g12 94) + (g12 31 + g12 93 - g12 29 - g12 95) + (g12 191 + g12 253 - g12 189 - g12 255) + (g12 46 + g12 172 - g12 44 - g12 174) + (g12 63 + g12 189 - g12 61 - g12 191) + (g12 127 + g12 253 - g12 125 - g12 255) + (g12 37 + g12 41 - g12 33 - g12 45) + (g12 28 + g12 56 - g12 24 - g12 60) + (g12 40 + g12 48 - g12 32 - g12 56) + (g12 31 + g12 55 - g12 23 - g12 63) + (g12 17 + g12 33 - g12 1 - g12 49) + (g12 20 + g12 36 - g12 4 - g12 52) + (g12 95 + g12 111 - g12 79 - g12 127) + (g12 29 + g12 77 - g12 13 - g12 93) + 2 * (g12 188 + g12 236 - g12 172 - g12 252) + 2 * (g12 60 + g12 172 - g12 44 - g12 188) + (g12 126 + g12 238 - g12 110 - g12 254) + (g12 110 + g12 174 - g12 46 - g12 238) + (g25 121 + g25 122 - g25 120 - g25 123) + (g25 43 + g25 58 - g25 42 - g25 59) + (g25 11 + g25 74 - g25 10 - g25 75) + (g25 107 + g25 121 - g25 105 - g25 123) + (g25 11 + g25 41 - g25 9 - g25 43) + (g25 26 + g25 56 - g25 24 - g25 58) + (g25 75 + g25 105 - g25 73 - g25 107) + (g25 26 + g25 88 - g25 24 - g25 90) + (g25 42 + g25 104 - g25 40 - g25 106) + (g25 63 + g25 125 - g25 61 - g25 127) + (g25 31 + g25 59 - g25 27 - g25 63) + 2 * (g25 95 + g25 123 - g25 91 - g25 127) + 2 * (g25 31 + g25 91 - g25 27 - g25 95) + (g25 61 + g25 121 - g25 57 - g25 125) + (g25 90 + g25 106 - g25 74 - g25 122)) = 3 * (h 25 + h 26 - h 24 - h 27) + 2 * (h 9 + h 12 - h 8 - h 13) + (h 17 + h 20 - h 16 - h 21) + (h 11 + h 14 - h 10 - h 15) + 2 * (h 5 + h 12 - h 4 - h 13) + (h 19 + h 26 - h 18 - h 27) + (h 5 + h 20 - h 4 - h 21) + (h 2 + h 8 - h 0 - h 10) + (h 2 + h 16 - h 0 - h 18) + 2 * (h 15 + h 29 - h 13 - h 31) + 2 * (h 7 + h 11 - h 3 - h 15) + 2 * (h 14 + h 22 - h 6 - h 30) + 3 * (g12 31 + g12 236 - g12 255 - g12 12) + 3 * (g25 31 + g25 121 - g25 127 - g25 25) := by
    simp only [v12_1, v12_4, v12_5, v12_8, v12_9, v12_12, v12_13, v12_17, v12_20, v12_21, v12_23, v12_24, v12_28, v12_29, v12_30, v12_31, v12_32, v12_36, v12_40, v12_44, v12_108, v12_172, v12_236, v25_9, v25_10, v25_11, v25_24, v25_25, v25_26, v25_27, v25_31, v25_40, v25_41, v25_56, v25_57, v25_73, v25_88, v25_104, v25_105, v25_120, v25_121, hp.empty]
    ring
  have hz : (h 23 + h 29 - h 21 - h 31) = 0 := by
    have nn := hp.submod (23 : Mask 5) (29 : Mask 5)
    change h 21 + h 31 ≤ h 23 + h 29 at nn
    linarith only [hid, hsum, nn, z6, z10, z11, z12, z18, z21, z26, z40, z48, z55, z60, z78, eadh12, eadh25]
  have bad := (hm (47 : Fin 80)).mp (show cmi h 47 = 0 from hz)
  change false = true at bad
  cases bad

#print axioms no_selfadhesive_inducer

end InfoE3
