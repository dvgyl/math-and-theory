import BinaryData
import BinaryTilingDefs

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BinaryFuglede

private theorem tiling_code_0 : xorFin (pointCode 0) (tileCode 0) = (0 : Fin 512) := by decide
private theorem tiling_code_1 : xorFin (pointCode 0) (tileCode 1) = (1 : Fin 512) := by decide
private theorem tiling_code_2 : xorFin (pointCode 0) (tileCode 2) = (2 : Fin 512) := by decide
private theorem tiling_code_3 : xorFin (pointCode 1) (tileCode 4) = (3 : Fin 512) := by decide
private theorem tiling_code_4 : xorFin (pointCode 0) (tileCode 3) = (4 : Fin 512) := by decide
private theorem tiling_code_5 : xorFin (pointCode 4) (tileCode 6) = (5 : Fin 512) := by decide
private theorem tiling_code_6 : xorFin (pointCode 2) (tileCode 5) = (6 : Fin 512) := by decide
private theorem tiling_code_7 : xorFin (pointCode 7) (tileCode 7) = (7 : Fin 512) := by decide
private theorem tiling_code_8 : xorFin (pointCode 0) (tileCode 4) = (8 : Fin 512) := by decide
private theorem tiling_code_9 : xorFin (pointCode 1) (tileCode 2) = (9 : Fin 512) := by decide
private theorem tiling_code_10 : xorFin (pointCode 1) (tileCode 1) = (10 : Fin 512) := by decide
private theorem tiling_code_11 : xorFin (pointCode 1) (tileCode 0) = (11 : Fin 512) := by decide
private theorem tiling_code_12 : xorFin (pointCode 6) (tileCode 7) = (12 : Fin 512) := by decide
private theorem tiling_code_13 : xorFin (pointCode 3) (tileCode 5) = (13 : Fin 512) := by decide
private theorem tiling_code_14 : xorFin (pointCode 5) (tileCode 6) = (14 : Fin 512) := by decide
private theorem tiling_code_15 : xorFin (pointCode 1) (tileCode 3) = (15 : Fin 512) := by decide
private theorem tiling_code_16 : xorFin (pointCode 0) (tileCode 5) = (16 : Fin 512) := by decide
private theorem tiling_code_17 : xorFin (pointCode 5) (tileCode 7) = (17 : Fin 512) := by decide
private theorem tiling_code_18 : xorFin (pointCode 2) (tileCode 3) = (18 : Fin 512) := by decide
private theorem tiling_code_19 : xorFin (pointCode 6) (tileCode 6) = (19 : Fin 512) := by decide
private theorem tiling_code_20 : xorFin (pointCode 2) (tileCode 2) = (20 : Fin 512) := by decide
private theorem tiling_code_21 : xorFin (pointCode 3) (tileCode 4) = (21 : Fin 512) := by decide
private theorem tiling_code_22 : xorFin (pointCode 2) (tileCode 0) = (22 : Fin 512) := by decide
private theorem tiling_code_23 : xorFin (pointCode 2) (tileCode 1) = (23 : Fin 512) := by decide
private theorem tiling_code_24 : xorFin (pointCode 7) (tileCode 6) = (24 : Fin 512) := by decide
private theorem tiling_code_25 : xorFin (pointCode 3) (tileCode 3) = (25 : Fin 512) := by decide
private theorem tiling_code_26 : xorFin (pointCode 4) (tileCode 7) = (26 : Fin 512) := by decide
private theorem tiling_code_27 : xorFin (pointCode 1) (tileCode 5) = (27 : Fin 512) := by decide
private theorem tiling_code_28 : xorFin (pointCode 3) (tileCode 1) = (28 : Fin 512) := by decide
private theorem tiling_code_29 : xorFin (pointCode 3) (tileCode 0) = (29 : Fin 512) := by decide
private theorem tiling_code_30 : xorFin (pointCode 2) (tileCode 4) = (30 : Fin 512) := by decide
private theorem tiling_code_31 : xorFin (pointCode 3) (tileCode 2) = (31 : Fin 512) := by decide
private theorem tiling_code_32 : xorFin (pointCode 0) (tileCode 6) = (32 : Fin 512) := by decide
private theorem tiling_code_33 : xorFin (pointCode 4) (tileCode 3) = (33 : Fin 512) := by decide
private theorem tiling_code_34 : xorFin (pointCode 3) (tileCode 7) = (34 : Fin 512) := by decide
private theorem tiling_code_35 : xorFin (pointCode 6) (tileCode 5) = (35 : Fin 512) := by decide
private theorem tiling_code_36 : xorFin (pointCode 4) (tileCode 1) = (36 : Fin 512) := by decide
private theorem tiling_code_37 : xorFin (pointCode 4) (tileCode 0) = (37 : Fin 512) := by decide
private theorem tiling_code_38 : xorFin (pointCode 5) (tileCode 4) = (38 : Fin 512) := by decide
private theorem tiling_code_39 : xorFin (pointCode 4) (tileCode 2) = (39 : Fin 512) := by decide
private theorem tiling_code_40 : xorFin (pointCode 7) (tileCode 5) = (40 : Fin 512) := by decide
private theorem tiling_code_41 : xorFin (pointCode 2) (tileCode 7) = (41 : Fin 512) := by decide
private theorem tiling_code_42 : xorFin (pointCode 5) (tileCode 3) = (42 : Fin 512) := by decide
private theorem tiling_code_43 : xorFin (pointCode 1) (tileCode 6) = (43 : Fin 512) := by decide
private theorem tiling_code_44 : xorFin (pointCode 5) (tileCode 2) = (44 : Fin 512) := by decide
private theorem tiling_code_45 : xorFin (pointCode 4) (tileCode 4) = (45 : Fin 512) := by decide
private theorem tiling_code_46 : xorFin (pointCode 5) (tileCode 0) = (46 : Fin 512) := by decide
private theorem tiling_code_47 : xorFin (pointCode 5) (tileCode 1) = (47 : Fin 512) := by decide
private theorem tiling_code_48 : xorFin (pointCode 7) (tileCode 4) = (48 : Fin 512) := by decide
private theorem tiling_code_49 : xorFin (pointCode 6) (tileCode 2) = (49 : Fin 512) := by decide
private theorem tiling_code_50 : xorFin (pointCode 6) (tileCode 1) = (50 : Fin 512) := by decide
private theorem tiling_code_51 : xorFin (pointCode 6) (tileCode 0) = (51 : Fin 512) := by decide
private theorem tiling_code_52 : xorFin (pointCode 1) (tileCode 7) = (52 : Fin 512) := by decide
private theorem tiling_code_53 : xorFin (pointCode 4) (tileCode 5) = (53 : Fin 512) := by decide
private theorem tiling_code_54 : xorFin (pointCode 2) (tileCode 6) = (54 : Fin 512) := by decide
private theorem tiling_code_55 : xorFin (pointCode 6) (tileCode 3) = (55 : Fin 512) := by decide
private theorem tiling_code_56 : xorFin (pointCode 7) (tileCode 0) = (56 : Fin 512) := by decide
private theorem tiling_code_57 : xorFin (pointCode 7) (tileCode 1) = (57 : Fin 512) := by decide
private theorem tiling_code_58 : xorFin (pointCode 7) (tileCode 2) = (58 : Fin 512) := by decide
private theorem tiling_code_59 : xorFin (pointCode 6) (tileCode 4) = (59 : Fin 512) := by decide
private theorem tiling_code_60 : xorFin (pointCode 7) (tileCode 3) = (60 : Fin 512) := by decide
private theorem tiling_code_61 : xorFin (pointCode 3) (tileCode 6) = (61 : Fin 512) := by decide
private theorem tiling_code_62 : xorFin (pointCode 5) (tileCode 5) = (62 : Fin 512) := by decide
private theorem tiling_code_63 : xorFin (pointCode 0) (tileCode 7) = (63 : Fin 512) := by decide
private theorem tiling_code_64 : xorFin (pointCode 8) (tileCode 0) = (64 : Fin 512) := by decide
private theorem tiling_code_65 : xorFin (pointCode 8) (tileCode 1) = (65 : Fin 512) := by decide
private theorem tiling_code_66 : xorFin (pointCode 8) (tileCode 2) = (66 : Fin 512) := by decide
private theorem tiling_code_67 : xorFin (pointCode 9) (tileCode 3) = (67 : Fin 512) := by decide
private theorem tiling_code_68 : xorFin (pointCode 8) (tileCode 3) = (68 : Fin 512) := by decide
private theorem tiling_code_69 : xorFin (pointCode 9) (tileCode 2) = (69 : Fin 512) := by decide
private theorem tiling_code_70 : xorFin (pointCode 9) (tileCode 1) = (70 : Fin 512) := by decide
private theorem tiling_code_71 : xorFin (pointCode 9) (tileCode 0) = (71 : Fin 512) := by decide
private theorem tiling_code_72 : xorFin (pointCode 8) (tileCode 4) = (72 : Fin 512) := by decide
private theorem tiling_code_73 : xorFin (pointCode 15) (tileCode 7) = (73 : Fin 512) := by decide
private theorem tiling_code_74 : xorFin (pointCode 10) (tileCode 5) = (74 : Fin 512) := by decide
private theorem tiling_code_75 : xorFin (pointCode 12) (tileCode 6) = (75 : Fin 512) := by decide
private theorem tiling_code_76 : xorFin (pointCode 13) (tileCode 6) = (76 : Fin 512) := by decide
private theorem tiling_code_77 : xorFin (pointCode 11) (tileCode 5) = (77 : Fin 512) := by decide
private theorem tiling_code_78 : xorFin (pointCode 14) (tileCode 7) = (78 : Fin 512) := by decide
private theorem tiling_code_79 : xorFin (pointCode 9) (tileCode 4) = (79 : Fin 512) := by decide
private theorem tiling_code_80 : xorFin (pointCode 8) (tileCode 5) = (80 : Fin 512) := by decide
private theorem tiling_code_81 : xorFin (pointCode 14) (tileCode 6) = (81 : Fin 512) := by decide
private theorem tiling_code_82 : xorFin (pointCode 10) (tileCode 4) = (82 : Fin 512) := by decide
private theorem tiling_code_83 : xorFin (pointCode 13) (tileCode 7) = (83 : Fin 512) := by decide
private theorem tiling_code_84 : xorFin (pointCode 12) (tileCode 7) = (84 : Fin 512) := by decide
private theorem tiling_code_85 : xorFin (pointCode 11) (tileCode 4) = (85 : Fin 512) := by decide
private theorem tiling_code_86 : xorFin (pointCode 15) (tileCode 6) = (86 : Fin 512) := by decide
private theorem tiling_code_87 : xorFin (pointCode 9) (tileCode 5) = (87 : Fin 512) := by decide
private theorem tiling_code_88 : xorFin (pointCode 10) (tileCode 2) = (88 : Fin 512) := by decide
private theorem tiling_code_89 : xorFin (pointCode 11) (tileCode 3) = (89 : Fin 512) := by decide
private theorem tiling_code_90 : xorFin (pointCode 10) (tileCode 0) = (90 : Fin 512) := by decide
private theorem tiling_code_91 : xorFin (pointCode 10) (tileCode 1) = (91 : Fin 512) := by decide
private theorem tiling_code_92 : xorFin (pointCode 11) (tileCode 1) = (92 : Fin 512) := by decide
private theorem tiling_code_93 : xorFin (pointCode 11) (tileCode 0) = (93 : Fin 512) := by decide
private theorem tiling_code_94 : xorFin (pointCode 10) (tileCode 3) = (94 : Fin 512) := by decide
private theorem tiling_code_95 : xorFin (pointCode 11) (tileCode 2) = (95 : Fin 512) := by decide
private theorem tiling_code_96 : xorFin (pointCode 8) (tileCode 6) = (96 : Fin 512) := by decide
private theorem tiling_code_97 : xorFin (pointCode 14) (tileCode 5) = (97 : Fin 512) := by decide
private theorem tiling_code_98 : xorFin (pointCode 11) (tileCode 7) = (98 : Fin 512) := by decide
private theorem tiling_code_99 : xorFin (pointCode 12) (tileCode 4) = (99 : Fin 512) := by decide
private theorem tiling_code_100 : xorFin (pointCode 13) (tileCode 4) = (100 : Fin 512) := by decide
private theorem tiling_code_101 : xorFin (pointCode 10) (tileCode 7) = (101 : Fin 512) := by decide
private theorem tiling_code_102 : xorFin (pointCode 15) (tileCode 5) = (102 : Fin 512) := by decide
private theorem tiling_code_103 : xorFin (pointCode 9) (tileCode 6) = (103 : Fin 512) := by decide
private theorem tiling_code_104 : xorFin (pointCode 13) (tileCode 3) = (104 : Fin 512) := by decide
private theorem tiling_code_105 : xorFin (pointCode 12) (tileCode 2) = (105 : Fin 512) := by decide
private theorem tiling_code_106 : xorFin (pointCode 12) (tileCode 1) = (106 : Fin 512) := by decide
private theorem tiling_code_107 : xorFin (pointCode 12) (tileCode 0) = (107 : Fin 512) := by decide
private theorem tiling_code_108 : xorFin (pointCode 13) (tileCode 0) = (108 : Fin 512) := by decide
private theorem tiling_code_109 : xorFin (pointCode 13) (tileCode 1) = (109 : Fin 512) := by decide
private theorem tiling_code_110 : xorFin (pointCode 13) (tileCode 2) = (110 : Fin 512) := by decide
private theorem tiling_code_111 : xorFin (pointCode 12) (tileCode 3) = (111 : Fin 512) := by decide
private theorem tiling_code_112 : xorFin (pointCode 14) (tileCode 1) = (112 : Fin 512) := by decide
private theorem tiling_code_113 : xorFin (pointCode 14) (tileCode 0) = (113 : Fin 512) := by decide
private theorem tiling_code_114 : xorFin (pointCode 15) (tileCode 3) = (114 : Fin 512) := by decide
private theorem tiling_code_115 : xorFin (pointCode 14) (tileCode 2) = (115 : Fin 512) := by decide
private theorem tiling_code_116 : xorFin (pointCode 15) (tileCode 2) = (116 : Fin 512) := by decide
private theorem tiling_code_117 : xorFin (pointCode 14) (tileCode 3) = (117 : Fin 512) := by decide
private theorem tiling_code_118 : xorFin (pointCode 15) (tileCode 0) = (118 : Fin 512) := by decide
private theorem tiling_code_119 : xorFin (pointCode 15) (tileCode 1) = (119 : Fin 512) := by decide
private theorem tiling_code_120 : xorFin (pointCode 9) (tileCode 7) = (120 : Fin 512) := by decide
private theorem tiling_code_121 : xorFin (pointCode 14) (tileCode 4) = (121 : Fin 512) := by decide
private theorem tiling_code_122 : xorFin (pointCode 10) (tileCode 6) = (122 : Fin 512) := by decide
private theorem tiling_code_123 : xorFin (pointCode 12) (tileCode 5) = (123 : Fin 512) := by decide
private theorem tiling_code_124 : xorFin (pointCode 13) (tileCode 5) = (124 : Fin 512) := by decide
private theorem tiling_code_125 : xorFin (pointCode 11) (tileCode 6) = (125 : Fin 512) := by decide
private theorem tiling_code_126 : xorFin (pointCode 15) (tileCode 4) = (126 : Fin 512) := by decide
private theorem tiling_code_127 : xorFin (pointCode 8) (tileCode 7) = (127 : Fin 512) := by decide
private theorem tiling_code_128 : xorFin (pointCode 16) (tileCode 0) = (128 : Fin 512) := by decide
private theorem tiling_code_129 : xorFin (pointCode 16) (tileCode 1) = (129 : Fin 512) := by decide
private theorem tiling_code_130 : xorFin (pointCode 16) (tileCode 2) = (130 : Fin 512) := by decide
private theorem tiling_code_131 : xorFin (pointCode 20) (tileCode 6) = (131 : Fin 512) := by decide
private theorem tiling_code_132 : xorFin (pointCode 16) (tileCode 3) = (132 : Fin 512) := by decide
private theorem tiling_code_133 : xorFin (pointCode 23) (tileCode 7) = (133 : Fin 512) := by decide
private theorem tiling_code_134 : xorFin (pointCode 17) (tileCode 4) = (134 : Fin 512) := by decide
private theorem tiling_code_135 : xorFin (pointCode 18) (tileCode 5) = (135 : Fin 512) := by decide
private theorem tiling_code_136 : xorFin (pointCode 16) (tileCode 4) = (136 : Fin 512) := by decide
private theorem tiling_code_137 : xorFin (pointCode 19) (tileCode 5) = (137 : Fin 512) := by decide
private theorem tiling_code_138 : xorFin (pointCode 17) (tileCode 3) = (138 : Fin 512) := by decide
private theorem tiling_code_139 : xorFin (pointCode 22) (tileCode 7) = (139 : Fin 512) := by decide
private theorem tiling_code_140 : xorFin (pointCode 17) (tileCode 2) = (140 : Fin 512) := by decide
private theorem tiling_code_141 : xorFin (pointCode 21) (tileCode 6) = (141 : Fin 512) := by decide
private theorem tiling_code_142 : xorFin (pointCode 17) (tileCode 0) = (142 : Fin 512) := by decide
private theorem tiling_code_143 : xorFin (pointCode 17) (tileCode 1) = (143 : Fin 512) := by decide
private theorem tiling_code_144 : xorFin (pointCode 16) (tileCode 5) = (144 : Fin 512) := by decide
private theorem tiling_code_145 : xorFin (pointCode 19) (tileCode 4) = (145 : Fin 512) := by decide
private theorem tiling_code_146 : xorFin (pointCode 21) (tileCode 7) = (146 : Fin 512) := by decide
private theorem tiling_code_147 : xorFin (pointCode 18) (tileCode 3) = (147 : Fin 512) := by decide
private theorem tiling_code_148 : xorFin (pointCode 22) (tileCode 6) = (148 : Fin 512) := by decide
private theorem tiling_code_149 : xorFin (pointCode 18) (tileCode 2) = (149 : Fin 512) := by decide
private theorem tiling_code_150 : xorFin (pointCode 18) (tileCode 1) = (150 : Fin 512) := by decide
private theorem tiling_code_151 : xorFin (pointCode 18) (tileCode 0) = (151 : Fin 512) := by decide
private theorem tiling_code_152 : xorFin (pointCode 19) (tileCode 1) = (152 : Fin 512) := by decide
private theorem tiling_code_153 : xorFin (pointCode 19) (tileCode 0) = (153 : Fin 512) := by decide
private theorem tiling_code_154 : xorFin (pointCode 23) (tileCode 6) = (154 : Fin 512) := by decide
private theorem tiling_code_155 : xorFin (pointCode 19) (tileCode 2) = (155 : Fin 512) := by decide
private theorem tiling_code_156 : xorFin (pointCode 20) (tileCode 7) = (156 : Fin 512) := by decide
private theorem tiling_code_157 : xorFin (pointCode 19) (tileCode 3) = (157 : Fin 512) := by decide
private theorem tiling_code_158 : xorFin (pointCode 17) (tileCode 5) = (158 : Fin 512) := by decide
private theorem tiling_code_159 : xorFin (pointCode 18) (tileCode 4) = (159 : Fin 512) := by decide
private theorem tiling_code_160 : xorFin (pointCode 16) (tileCode 6) = (160 : Fin 512) := by decide
private theorem tiling_code_161 : xorFin (pointCode 20) (tileCode 2) = (161 : Fin 512) := by decide
private theorem tiling_code_162 : xorFin (pointCode 20) (tileCode 1) = (162 : Fin 512) := by decide
private theorem tiling_code_163 : xorFin (pointCode 20) (tileCode 0) = (163 : Fin 512) := by decide
private theorem tiling_code_164 : xorFin (pointCode 22) (tileCode 5) = (164 : Fin 512) := by decide
private theorem tiling_code_165 : xorFin (pointCode 21) (tileCode 4) = (165 : Fin 512) := by decide
private theorem tiling_code_166 : xorFin (pointCode 19) (tileCode 7) = (166 : Fin 512) := by decide
private theorem tiling_code_167 : xorFin (pointCode 20) (tileCode 3) = (167 : Fin 512) := by decide
private theorem tiling_code_168 : xorFin (pointCode 18) (tileCode 7) = (168 : Fin 512) := by decide
private theorem tiling_code_169 : xorFin (pointCode 21) (tileCode 3) = (169 : Fin 512) := by decide
private theorem tiling_code_170 : xorFin (pointCode 23) (tileCode 5) = (170 : Fin 512) := by decide
private theorem tiling_code_171 : xorFin (pointCode 20) (tileCode 4) = (171 : Fin 512) := by decide
private theorem tiling_code_172 : xorFin (pointCode 21) (tileCode 1) = (172 : Fin 512) := by decide
private theorem tiling_code_173 : xorFin (pointCode 21) (tileCode 0) = (173 : Fin 512) := by decide
private theorem tiling_code_174 : xorFin (pointCode 17) (tileCode 6) = (174 : Fin 512) := by decide
private theorem tiling_code_175 : xorFin (pointCode 21) (tileCode 2) = (175 : Fin 512) := by decide
private theorem tiling_code_176 : xorFin (pointCode 22) (tileCode 3) = (176 : Fin 512) := by decide
private theorem tiling_code_177 : xorFin (pointCode 17) (tileCode 7) = (177 : Fin 512) := by decide
private theorem tiling_code_178 : xorFin (pointCode 23) (tileCode 4) = (178 : Fin 512) := by decide
private theorem tiling_code_179 : xorFin (pointCode 20) (tileCode 5) = (179 : Fin 512) := by decide
private theorem tiling_code_180 : xorFin (pointCode 22) (tileCode 0) = (180 : Fin 512) := by decide
private theorem tiling_code_181 : xorFin (pointCode 22) (tileCode 1) = (181 : Fin 512) := by decide
private theorem tiling_code_182 : xorFin (pointCode 22) (tileCode 2) = (182 : Fin 512) := by decide
private theorem tiling_code_183 : xorFin (pointCode 18) (tileCode 6) = (183 : Fin 512) := by decide
private theorem tiling_code_184 : xorFin (pointCode 23) (tileCode 2) = (184 : Fin 512) := by decide
private theorem tiling_code_185 : xorFin (pointCode 19) (tileCode 6) = (185 : Fin 512) := by decide
private theorem tiling_code_186 : xorFin (pointCode 23) (tileCode 0) = (186 : Fin 512) := by decide
private theorem tiling_code_187 : xorFin (pointCode 23) (tileCode 1) = (187 : Fin 512) := by decide
private theorem tiling_code_188 : xorFin (pointCode 22) (tileCode 4) = (188 : Fin 512) := by decide
private theorem tiling_code_189 : xorFin (pointCode 21) (tileCode 5) = (189 : Fin 512) := by decide
private theorem tiling_code_190 : xorFin (pointCode 23) (tileCode 3) = (190 : Fin 512) := by decide
private theorem tiling_code_191 : xorFin (pointCode 16) (tileCode 7) = (191 : Fin 512) := by decide
private theorem tiling_code_192 : xorFin (pointCode 24) (tileCode 0) = (192 : Fin 512) := by decide
private theorem tiling_code_193 : xorFin (pointCode 24) (tileCode 1) = (193 : Fin 512) := by decide
private theorem tiling_code_194 : xorFin (pointCode 24) (tileCode 2) = (194 : Fin 512) := by decide
private theorem tiling_code_195 : xorFin (pointCode 31) (tileCode 7) = (195 : Fin 512) := by decide
private theorem tiling_code_196 : xorFin (pointCode 24) (tileCode 3) = (196 : Fin 512) := by decide
private theorem tiling_code_197 : xorFin (pointCode 25) (tileCode 4) = (197 : Fin 512) := by decide
private theorem tiling_code_198 : xorFin (pointCode 26) (tileCode 5) = (198 : Fin 512) := by decide
private theorem tiling_code_199 : xorFin (pointCode 28) (tileCode 6) = (199 : Fin 512) := by decide
private theorem tiling_code_200 : xorFin (pointCode 24) (tileCode 4) = (200 : Fin 512) := by decide
private theorem tiling_code_201 : xorFin (pointCode 25) (tileCode 3) = (201 : Fin 512) := by decide
private theorem tiling_code_202 : xorFin (pointCode 29) (tileCode 6) = (202 : Fin 512) := by decide
private theorem tiling_code_203 : xorFin (pointCode 27) (tileCode 5) = (203 : Fin 512) := by decide
private theorem tiling_code_204 : xorFin (pointCode 25) (tileCode 1) = (204 : Fin 512) := by decide
private theorem tiling_code_205 : xorFin (pointCode 25) (tileCode 0) = (205 : Fin 512) := by decide
private theorem tiling_code_206 : xorFin (pointCode 30) (tileCode 7) = (206 : Fin 512) := by decide
private theorem tiling_code_207 : xorFin (pointCode 25) (tileCode 2) = (207 : Fin 512) := by decide
private theorem tiling_code_208 : xorFin (pointCode 24) (tileCode 5) = (208 : Fin 512) := by decide
private theorem tiling_code_209 : xorFin (pointCode 30) (tileCode 6) = (209 : Fin 512) := by decide
private theorem tiling_code_210 : xorFin (pointCode 26) (tileCode 3) = (210 : Fin 512) := by decide
private theorem tiling_code_211 : xorFin (pointCode 27) (tileCode 4) = (211 : Fin 512) := by decide
private theorem tiling_code_212 : xorFin (pointCode 26) (tileCode 2) = (212 : Fin 512) := by decide
private theorem tiling_code_213 : xorFin (pointCode 29) (tileCode 7) = (213 : Fin 512) := by decide
private theorem tiling_code_214 : xorFin (pointCode 26) (tileCode 0) = (214 : Fin 512) := by decide
private theorem tiling_code_215 : xorFin (pointCode 26) (tileCode 1) = (215 : Fin 512) := by decide
private theorem tiling_code_216 : xorFin (pointCode 28) (tileCode 7) = (216 : Fin 512) := by decide
private theorem tiling_code_217 : xorFin (pointCode 27) (tileCode 2) = (217 : Fin 512) := by decide
private theorem tiling_code_218 : xorFin (pointCode 27) (tileCode 1) = (218 : Fin 512) := by decide
private theorem tiling_code_219 : xorFin (pointCode 27) (tileCode 0) = (219 : Fin 512) := by decide
private theorem tiling_code_220 : xorFin (pointCode 31) (tileCode 6) = (220 : Fin 512) := by decide
private theorem tiling_code_221 : xorFin (pointCode 25) (tileCode 5) = (221 : Fin 512) := by decide
private theorem tiling_code_222 : xorFin (pointCode 26) (tileCode 4) = (222 : Fin 512) := by decide
private theorem tiling_code_223 : xorFin (pointCode 27) (tileCode 3) = (223 : Fin 512) := by decide
private theorem tiling_code_224 : xorFin (pointCode 24) (tileCode 6) = (224 : Fin 512) := by decide
private theorem tiling_code_225 : xorFin (pointCode 30) (tileCode 5) = (225 : Fin 512) := by decide
private theorem tiling_code_226 : xorFin (pointCode 29) (tileCode 4) = (226 : Fin 512) := by decide
private theorem tiling_code_227 : xorFin (pointCode 28) (tileCode 3) = (227 : Fin 512) := by decide
private theorem tiling_code_228 : xorFin (pointCode 27) (tileCode 7) = (228 : Fin 512) := by decide
private theorem tiling_code_229 : xorFin (pointCode 28) (tileCode 2) = (229 : Fin 512) := by decide
private theorem tiling_code_230 : xorFin (pointCode 28) (tileCode 1) = (230 : Fin 512) := by decide
private theorem tiling_code_231 : xorFin (pointCode 28) (tileCode 0) = (231 : Fin 512) := by decide
private theorem tiling_code_232 : xorFin (pointCode 29) (tileCode 2) = (232 : Fin 512) := by decide
private theorem tiling_code_233 : xorFin (pointCode 26) (tileCode 7) = (233 : Fin 512) := by decide
private theorem tiling_code_234 : xorFin (pointCode 29) (tileCode 0) = (234 : Fin 512) := by decide
private theorem tiling_code_235 : xorFin (pointCode 29) (tileCode 1) = (235 : Fin 512) := by decide
private theorem tiling_code_236 : xorFin (pointCode 31) (tileCode 5) = (236 : Fin 512) := by decide
private theorem tiling_code_237 : xorFin (pointCode 25) (tileCode 6) = (237 : Fin 512) := by decide
private theorem tiling_code_238 : xorFin (pointCode 29) (tileCode 3) = (238 : Fin 512) := by decide
private theorem tiling_code_239 : xorFin (pointCode 28) (tileCode 4) = (239 : Fin 512) := by decide
private theorem tiling_code_240 : xorFin (pointCode 30) (tileCode 1) = (240 : Fin 512) := by decide
private theorem tiling_code_241 : xorFin (pointCode 30) (tileCode 0) = (241 : Fin 512) := by decide
private theorem tiling_code_242 : xorFin (pointCode 25) (tileCode 7) = (242 : Fin 512) := by decide
private theorem tiling_code_243 : xorFin (pointCode 30) (tileCode 2) = (243 : Fin 512) := by decide
private theorem tiling_code_244 : xorFin (pointCode 31) (tileCode 4) = (244 : Fin 512) := by decide
private theorem tiling_code_245 : xorFin (pointCode 30) (tileCode 3) = (245 : Fin 512) := by decide
private theorem tiling_code_246 : xorFin (pointCode 26) (tileCode 6) = (246 : Fin 512) := by decide
private theorem tiling_code_247 : xorFin (pointCode 28) (tileCode 5) = (247 : Fin 512) := by decide
private theorem tiling_code_248 : xorFin (pointCode 31) (tileCode 3) = (248 : Fin 512) := by decide
private theorem tiling_code_249 : xorFin (pointCode 30) (tileCode 4) = (249 : Fin 512) := by decide
private theorem tiling_code_250 : xorFin (pointCode 29) (tileCode 5) = (250 : Fin 512) := by decide
private theorem tiling_code_251 : xorFin (pointCode 27) (tileCode 6) = (251 : Fin 512) := by decide
private theorem tiling_code_252 : xorFin (pointCode 31) (tileCode 0) = (252 : Fin 512) := by decide
private theorem tiling_code_253 : xorFin (pointCode 31) (tileCode 1) = (253 : Fin 512) := by decide
private theorem tiling_code_254 : xorFin (pointCode 31) (tileCode 2) = (254 : Fin 512) := by decide
private theorem tiling_code_255 : xorFin (pointCode 24) (tileCode 7) = (255 : Fin 512) := by decide
private theorem tiling_code_256 : xorFin (pointCode 32) (tileCode 0) = (256 : Fin 512) := by decide
private theorem tiling_code_257 : xorFin (pointCode 32) (tileCode 1) = (257 : Fin 512) := by decide
private theorem tiling_code_258 : xorFin (pointCode 32) (tileCode 2) = (258 : Fin 512) := by decide
private theorem tiling_code_259 : xorFin (pointCode 33) (tileCode 3) = (259 : Fin 512) := by decide
private theorem tiling_code_260 : xorFin (pointCode 32) (tileCode 3) = (260 : Fin 512) := by decide
private theorem tiling_code_261 : xorFin (pointCode 33) (tileCode 2) = (261 : Fin 512) := by decide
private theorem tiling_code_262 : xorFin (pointCode 33) (tileCode 1) = (262 : Fin 512) := by decide
private theorem tiling_code_263 : xorFin (pointCode 33) (tileCode 0) = (263 : Fin 512) := by decide
private theorem tiling_code_264 : xorFin (pointCode 32) (tileCode 4) = (264 : Fin 512) := by decide
private theorem tiling_code_265 : xorFin (pointCode 39) (tileCode 7) = (265 : Fin 512) := by decide
private theorem tiling_code_266 : xorFin (pointCode 34) (tileCode 5) = (266 : Fin 512) := by decide
private theorem tiling_code_267 : xorFin (pointCode 36) (tileCode 6) = (267 : Fin 512) := by decide
private theorem tiling_code_268 : xorFin (pointCode 37) (tileCode 6) = (268 : Fin 512) := by decide
private theorem tiling_code_269 : xorFin (pointCode 35) (tileCode 5) = (269 : Fin 512) := by decide
private theorem tiling_code_270 : xorFin (pointCode 38) (tileCode 7) = (270 : Fin 512) := by decide
private theorem tiling_code_271 : xorFin (pointCode 33) (tileCode 4) = (271 : Fin 512) := by decide
private theorem tiling_code_272 : xorFin (pointCode 32) (tileCode 5) = (272 : Fin 512) := by decide
private theorem tiling_code_273 : xorFin (pointCode 38) (tileCode 6) = (273 : Fin 512) := by decide
private theorem tiling_code_274 : xorFin (pointCode 34) (tileCode 4) = (274 : Fin 512) := by decide
private theorem tiling_code_275 : xorFin (pointCode 37) (tileCode 7) = (275 : Fin 512) := by decide
private theorem tiling_code_276 : xorFin (pointCode 36) (tileCode 7) = (276 : Fin 512) := by decide
private theorem tiling_code_277 : xorFin (pointCode 35) (tileCode 4) = (277 : Fin 512) := by decide
private theorem tiling_code_278 : xorFin (pointCode 39) (tileCode 6) = (278 : Fin 512) := by decide
private theorem tiling_code_279 : xorFin (pointCode 33) (tileCode 5) = (279 : Fin 512) := by decide
private theorem tiling_code_280 : xorFin (pointCode 34) (tileCode 2) = (280 : Fin 512) := by decide
private theorem tiling_code_281 : xorFin (pointCode 35) (tileCode 3) = (281 : Fin 512) := by decide
private theorem tiling_code_282 : xorFin (pointCode 34) (tileCode 0) = (282 : Fin 512) := by decide
private theorem tiling_code_283 : xorFin (pointCode 34) (tileCode 1) = (283 : Fin 512) := by decide
private theorem tiling_code_284 : xorFin (pointCode 35) (tileCode 1) = (284 : Fin 512) := by decide
private theorem tiling_code_285 : xorFin (pointCode 35) (tileCode 0) = (285 : Fin 512) := by decide
private theorem tiling_code_286 : xorFin (pointCode 34) (tileCode 3) = (286 : Fin 512) := by decide
private theorem tiling_code_287 : xorFin (pointCode 35) (tileCode 2) = (287 : Fin 512) := by decide
private theorem tiling_code_288 : xorFin (pointCode 32) (tileCode 6) = (288 : Fin 512) := by decide
private theorem tiling_code_289 : xorFin (pointCode 38) (tileCode 5) = (289 : Fin 512) := by decide
private theorem tiling_code_290 : xorFin (pointCode 35) (tileCode 7) = (290 : Fin 512) := by decide
private theorem tiling_code_291 : xorFin (pointCode 36) (tileCode 4) = (291 : Fin 512) := by decide
private theorem tiling_code_292 : xorFin (pointCode 37) (tileCode 4) = (292 : Fin 512) := by decide
private theorem tiling_code_293 : xorFin (pointCode 34) (tileCode 7) = (293 : Fin 512) := by decide
private theorem tiling_code_294 : xorFin (pointCode 39) (tileCode 5) = (294 : Fin 512) := by decide
private theorem tiling_code_295 : xorFin (pointCode 33) (tileCode 6) = (295 : Fin 512) := by decide
private theorem tiling_code_296 : xorFin (pointCode 37) (tileCode 3) = (296 : Fin 512) := by decide
private theorem tiling_code_297 : xorFin (pointCode 36) (tileCode 2) = (297 : Fin 512) := by decide
private theorem tiling_code_298 : xorFin (pointCode 36) (tileCode 1) = (298 : Fin 512) := by decide
private theorem tiling_code_299 : xorFin (pointCode 36) (tileCode 0) = (299 : Fin 512) := by decide
private theorem tiling_code_300 : xorFin (pointCode 37) (tileCode 0) = (300 : Fin 512) := by decide
private theorem tiling_code_301 : xorFin (pointCode 37) (tileCode 1) = (301 : Fin 512) := by decide
private theorem tiling_code_302 : xorFin (pointCode 37) (tileCode 2) = (302 : Fin 512) := by decide
private theorem tiling_code_303 : xorFin (pointCode 36) (tileCode 3) = (303 : Fin 512) := by decide
private theorem tiling_code_304 : xorFin (pointCode 38) (tileCode 1) = (304 : Fin 512) := by decide
private theorem tiling_code_305 : xorFin (pointCode 38) (tileCode 0) = (305 : Fin 512) := by decide
private theorem tiling_code_306 : xorFin (pointCode 39) (tileCode 3) = (306 : Fin 512) := by decide
private theorem tiling_code_307 : xorFin (pointCode 38) (tileCode 2) = (307 : Fin 512) := by decide
private theorem tiling_code_308 : xorFin (pointCode 39) (tileCode 2) = (308 : Fin 512) := by decide
private theorem tiling_code_309 : xorFin (pointCode 38) (tileCode 3) = (309 : Fin 512) := by decide
private theorem tiling_code_310 : xorFin (pointCode 39) (tileCode 0) = (310 : Fin 512) := by decide
private theorem tiling_code_311 : xorFin (pointCode 39) (tileCode 1) = (311 : Fin 512) := by decide
private theorem tiling_code_312 : xorFin (pointCode 33) (tileCode 7) = (312 : Fin 512) := by decide
private theorem tiling_code_313 : xorFin (pointCode 38) (tileCode 4) = (313 : Fin 512) := by decide
private theorem tiling_code_314 : xorFin (pointCode 34) (tileCode 6) = (314 : Fin 512) := by decide
private theorem tiling_code_315 : xorFin (pointCode 36) (tileCode 5) = (315 : Fin 512) := by decide
private theorem tiling_code_316 : xorFin (pointCode 37) (tileCode 5) = (316 : Fin 512) := by decide
private theorem tiling_code_317 : xorFin (pointCode 35) (tileCode 6) = (317 : Fin 512) := by decide
private theorem tiling_code_318 : xorFin (pointCode 39) (tileCode 4) = (318 : Fin 512) := by decide
private theorem tiling_code_319 : xorFin (pointCode 32) (tileCode 7) = (319 : Fin 512) := by decide
private theorem tiling_code_320 : xorFin (pointCode 40) (tileCode 0) = (320 : Fin 512) := by decide
private theorem tiling_code_321 : xorFin (pointCode 40) (tileCode 1) = (321 : Fin 512) := by decide
private theorem tiling_code_322 : xorFin (pointCode 40) (tileCode 2) = (322 : Fin 512) := by decide
private theorem tiling_code_323 : xorFin (pointCode 41) (tileCode 4) = (323 : Fin 512) := by decide
private theorem tiling_code_324 : xorFin (pointCode 40) (tileCode 3) = (324 : Fin 512) := by decide
private theorem tiling_code_325 : xorFin (pointCode 42) (tileCode 5) = (325 : Fin 512) := by decide
private theorem tiling_code_326 : xorFin (pointCode 47) (tileCode 7) = (326 : Fin 512) := by decide
private theorem tiling_code_327 : xorFin (pointCode 44) (tileCode 6) = (327 : Fin 512) := by decide
private theorem tiling_code_328 : xorFin (pointCode 40) (tileCode 4) = (328 : Fin 512) := by decide
private theorem tiling_code_329 : xorFin (pointCode 41) (tileCode 2) = (329 : Fin 512) := by decide
private theorem tiling_code_330 : xorFin (pointCode 41) (tileCode 1) = (330 : Fin 512) := by decide
private theorem tiling_code_331 : xorFin (pointCode 41) (tileCode 0) = (331 : Fin 512) := by decide
private theorem tiling_code_332 : xorFin (pointCode 45) (tileCode 6) = (332 : Fin 512) := by decide
private theorem tiling_code_333 : xorFin (pointCode 46) (tileCode 7) = (333 : Fin 512) := by decide
private theorem tiling_code_334 : xorFin (pointCode 43) (tileCode 5) = (334 : Fin 512) := by decide
private theorem tiling_code_335 : xorFin (pointCode 41) (tileCode 3) = (335 : Fin 512) := by decide
private theorem tiling_code_336 : xorFin (pointCode 40) (tileCode 5) = (336 : Fin 512) := by decide
private theorem tiling_code_337 : xorFin (pointCode 42) (tileCode 3) = (337 : Fin 512) := by decide
private theorem tiling_code_338 : xorFin (pointCode 46) (tileCode 6) = (338 : Fin 512) := by decide
private theorem tiling_code_339 : xorFin (pointCode 45) (tileCode 7) = (339 : Fin 512) := by decide
private theorem tiling_code_340 : xorFin (pointCode 42) (tileCode 1) = (340 : Fin 512) := by decide
private theorem tiling_code_341 : xorFin (pointCode 42) (tileCode 0) = (341 : Fin 512) := by decide
private theorem tiling_code_342 : xorFin (pointCode 43) (tileCode 4) = (342 : Fin 512) := by decide
private theorem tiling_code_343 : xorFin (pointCode 42) (tileCode 2) = (343 : Fin 512) := by decide
private theorem tiling_code_344 : xorFin (pointCode 44) (tileCode 7) = (344 : Fin 512) := by decide
private theorem tiling_code_345 : xorFin (pointCode 47) (tileCode 6) = (345 : Fin 512) := by decide
private theorem tiling_code_346 : xorFin (pointCode 43) (tileCode 3) = (346 : Fin 512) := by decide
private theorem tiling_code_347 : xorFin (pointCode 41) (tileCode 5) = (347 : Fin 512) := by decide
private theorem tiling_code_348 : xorFin (pointCode 43) (tileCode 2) = (348 : Fin 512) := by decide
private theorem tiling_code_349 : xorFin (pointCode 42) (tileCode 4) = (349 : Fin 512) := by decide
private theorem tiling_code_350 : xorFin (pointCode 43) (tileCode 0) = (350 : Fin 512) := by decide
private theorem tiling_code_351 : xorFin (pointCode 43) (tileCode 1) = (351 : Fin 512) := by decide
private theorem tiling_code_352 : xorFin (pointCode 40) (tileCode 6) = (352 : Fin 512) := by decide
private theorem tiling_code_353 : xorFin (pointCode 43) (tileCode 7) = (353 : Fin 512) := by decide
private theorem tiling_code_354 : xorFin (pointCode 46) (tileCode 5) = (354 : Fin 512) := by decide
private theorem tiling_code_355 : xorFin (pointCode 44) (tileCode 3) = (355 : Fin 512) := by decide
private theorem tiling_code_356 : xorFin (pointCode 45) (tileCode 4) = (356 : Fin 512) := by decide
private theorem tiling_code_357 : xorFin (pointCode 44) (tileCode 2) = (357 : Fin 512) := by decide
private theorem tiling_code_358 : xorFin (pointCode 44) (tileCode 1) = (358 : Fin 512) := by decide
private theorem tiling_code_359 : xorFin (pointCode 44) (tileCode 0) = (359 : Fin 512) := by decide
private theorem tiling_code_360 : xorFin (pointCode 45) (tileCode 3) = (360 : Fin 512) := by decide
private theorem tiling_code_361 : xorFin (pointCode 47) (tileCode 5) = (361 : Fin 512) := by decide
private theorem tiling_code_362 : xorFin (pointCode 42) (tileCode 7) = (362 : Fin 512) := by decide
private theorem tiling_code_363 : xorFin (pointCode 41) (tileCode 6) = (363 : Fin 512) := by decide
private theorem tiling_code_364 : xorFin (pointCode 45) (tileCode 0) = (364 : Fin 512) := by decide
private theorem tiling_code_365 : xorFin (pointCode 45) (tileCode 1) = (365 : Fin 512) := by decide
private theorem tiling_code_366 : xorFin (pointCode 45) (tileCode 2) = (366 : Fin 512) := by decide
private theorem tiling_code_367 : xorFin (pointCode 44) (tileCode 4) = (367 : Fin 512) := by decide
private theorem tiling_code_368 : xorFin (pointCode 46) (tileCode 2) = (368 : Fin 512) := by decide
private theorem tiling_code_369 : xorFin (pointCode 47) (tileCode 4) = (369 : Fin 512) := by decide
private theorem tiling_code_370 : xorFin (pointCode 46) (tileCode 0) = (370 : Fin 512) := by decide
private theorem tiling_code_371 : xorFin (pointCode 46) (tileCode 1) = (371 : Fin 512) := by decide
private theorem tiling_code_372 : xorFin (pointCode 41) (tileCode 7) = (372 : Fin 512) := by decide
private theorem tiling_code_373 : xorFin (pointCode 42) (tileCode 6) = (373 : Fin 512) := by decide
private theorem tiling_code_374 : xorFin (pointCode 46) (tileCode 3) = (374 : Fin 512) := by decide
private theorem tiling_code_375 : xorFin (pointCode 44) (tileCode 5) = (375 : Fin 512) := by decide
private theorem tiling_code_376 : xorFin (pointCode 47) (tileCode 1) = (376 : Fin 512) := by decide
private theorem tiling_code_377 : xorFin (pointCode 47) (tileCode 0) = (377 : Fin 512) := by decide
private theorem tiling_code_378 : xorFin (pointCode 46) (tileCode 4) = (378 : Fin 512) := by decide
private theorem tiling_code_379 : xorFin (pointCode 47) (tileCode 2) = (379 : Fin 512) := by decide
private theorem tiling_code_380 : xorFin (pointCode 45) (tileCode 5) = (380 : Fin 512) := by decide
private theorem tiling_code_381 : xorFin (pointCode 47) (tileCode 3) = (381 : Fin 512) := by decide
private theorem tiling_code_382 : xorFin (pointCode 43) (tileCode 6) = (382 : Fin 512) := by decide
private theorem tiling_code_383 : xorFin (pointCode 40) (tileCode 7) = (383 : Fin 512) := by decide
private theorem tiling_code_384 : xorFin (pointCode 48) (tileCode 0) = (384 : Fin 512) := by decide
private theorem tiling_code_385 : xorFin (pointCode 48) (tileCode 1) = (385 : Fin 512) := by decide
private theorem tiling_code_386 : xorFin (pointCode 48) (tileCode 2) = (386 : Fin 512) := by decide
private theorem tiling_code_387 : xorFin (pointCode 50) (tileCode 5) = (387 : Fin 512) := by decide
private theorem tiling_code_388 : xorFin (pointCode 48) (tileCode 3) = (388 : Fin 512) := by decide
private theorem tiling_code_389 : xorFin (pointCode 55) (tileCode 7) = (389 : Fin 512) := by decide
private theorem tiling_code_390 : xorFin (pointCode 52) (tileCode 6) = (390 : Fin 512) := by decide
private theorem tiling_code_391 : xorFin (pointCode 49) (tileCode 4) = (391 : Fin 512) := by decide
private theorem tiling_code_392 : xorFin (pointCode 48) (tileCode 4) = (392 : Fin 512) := by decide
private theorem tiling_code_393 : xorFin (pointCode 53) (tileCode 6) = (393 : Fin 512) := by decide
private theorem tiling_code_394 : xorFin (pointCode 54) (tileCode 7) = (394 : Fin 512) := by decide
private theorem tiling_code_395 : xorFin (pointCode 49) (tileCode 3) = (395 : Fin 512) := by decide
private theorem tiling_code_396 : xorFin (pointCode 51) (tileCode 5) = (396 : Fin 512) := by decide
private theorem tiling_code_397 : xorFin (pointCode 49) (tileCode 2) = (397 : Fin 512) := by decide
private theorem tiling_code_398 : xorFin (pointCode 49) (tileCode 1) = (398 : Fin 512) := by decide
private theorem tiling_code_399 : xorFin (pointCode 49) (tileCode 0) = (399 : Fin 512) := by decide
private theorem tiling_code_400 : xorFin (pointCode 48) (tileCode 5) = (400 : Fin 512) := by decide
private theorem tiling_code_401 : xorFin (pointCode 50) (tileCode 2) = (401 : Fin 512) := by decide
private theorem tiling_code_402 : xorFin (pointCode 50) (tileCode 1) = (402 : Fin 512) := by decide
private theorem tiling_code_403 : xorFin (pointCode 50) (tileCode 0) = (403 : Fin 512) := by decide
private theorem tiling_code_404 : xorFin (pointCode 51) (tileCode 4) = (404 : Fin 512) := by decide
private theorem tiling_code_405 : xorFin (pointCode 54) (tileCode 6) = (405 : Fin 512) := by decide
private theorem tiling_code_406 : xorFin (pointCode 53) (tileCode 7) = (406 : Fin 512) := by decide
private theorem tiling_code_407 : xorFin (pointCode 50) (tileCode 3) = (407 : Fin 512) := by decide
private theorem tiling_code_408 : xorFin (pointCode 51) (tileCode 3) = (408 : Fin 512) := by decide
private theorem tiling_code_409 : xorFin (pointCode 52) (tileCode 7) = (409 : Fin 512) := by decide
private theorem tiling_code_410 : xorFin (pointCode 55) (tileCode 6) = (410 : Fin 512) := by decide
private theorem tiling_code_411 : xorFin (pointCode 50) (tileCode 4) = (411 : Fin 512) := by decide
private theorem tiling_code_412 : xorFin (pointCode 51) (tileCode 0) = (412 : Fin 512) := by decide
private theorem tiling_code_413 : xorFin (pointCode 51) (tileCode 1) = (413 : Fin 512) := by decide
private theorem tiling_code_414 : xorFin (pointCode 51) (tileCode 2) = (414 : Fin 512) := by decide
private theorem tiling_code_415 : xorFin (pointCode 49) (tileCode 5) = (415 : Fin 512) := by decide
private theorem tiling_code_416 : xorFin (pointCode 48) (tileCode 6) = (416 : Fin 512) := by decide
private theorem tiling_code_417 : xorFin (pointCode 53) (tileCode 4) = (417 : Fin 512) := by decide
private theorem tiling_code_418 : xorFin (pointCode 52) (tileCode 3) = (418 : Fin 512) := by decide
private theorem tiling_code_419 : xorFin (pointCode 51) (tileCode 7) = (419 : Fin 512) := by decide
private theorem tiling_code_420 : xorFin (pointCode 52) (tileCode 2) = (420 : Fin 512) := by decide
private theorem tiling_code_421 : xorFin (pointCode 54) (tileCode 5) = (421 : Fin 512) := by decide
private theorem tiling_code_422 : xorFin (pointCode 52) (tileCode 0) = (422 : Fin 512) := by decide
private theorem tiling_code_423 : xorFin (pointCode 52) (tileCode 1) = (423 : Fin 512) := by decide
private theorem tiling_code_424 : xorFin (pointCode 53) (tileCode 1) = (424 : Fin 512) := by decide
private theorem tiling_code_425 : xorFin (pointCode 53) (tileCode 0) = (425 : Fin 512) := by decide
private theorem tiling_code_426 : xorFin (pointCode 55) (tileCode 5) = (426 : Fin 512) := by decide
private theorem tiling_code_427 : xorFin (pointCode 53) (tileCode 2) = (427 : Fin 512) := by decide
private theorem tiling_code_428 : xorFin (pointCode 50) (tileCode 7) = (428 : Fin 512) := by decide
private theorem tiling_code_429 : xorFin (pointCode 53) (tileCode 3) = (429 : Fin 512) := by decide
private theorem tiling_code_430 : xorFin (pointCode 52) (tileCode 4) = (430 : Fin 512) := by decide
private theorem tiling_code_431 : xorFin (pointCode 49) (tileCode 6) = (431 : Fin 512) := by decide
private theorem tiling_code_432 : xorFin (pointCode 49) (tileCode 7) = (432 : Fin 512) := by decide
private theorem tiling_code_433 : xorFin (pointCode 54) (tileCode 3) = (433 : Fin 512) := by decide
private theorem tiling_code_434 : xorFin (pointCode 55) (tileCode 4) = (434 : Fin 512) := by decide
private theorem tiling_code_435 : xorFin (pointCode 50) (tileCode 6) = (435 : Fin 512) := by decide
private theorem tiling_code_436 : xorFin (pointCode 54) (tileCode 1) = (436 : Fin 512) := by decide
private theorem tiling_code_437 : xorFin (pointCode 54) (tileCode 0) = (437 : Fin 512) := by decide
private theorem tiling_code_438 : xorFin (pointCode 52) (tileCode 5) = (438 : Fin 512) := by decide
private theorem tiling_code_439 : xorFin (pointCode 54) (tileCode 2) = (439 : Fin 512) := by decide
private theorem tiling_code_440 : xorFin (pointCode 55) (tileCode 2) = (440 : Fin 512) := by decide
private theorem tiling_code_441 : xorFin (pointCode 53) (tileCode 5) = (441 : Fin 512) := by decide
private theorem tiling_code_442 : xorFin (pointCode 55) (tileCode 0) = (442 : Fin 512) := by decide
private theorem tiling_code_443 : xorFin (pointCode 55) (tileCode 1) = (443 : Fin 512) := by decide
private theorem tiling_code_444 : xorFin (pointCode 51) (tileCode 6) = (444 : Fin 512) := by decide
private theorem tiling_code_445 : xorFin (pointCode 54) (tileCode 4) = (445 : Fin 512) := by decide
private theorem tiling_code_446 : xorFin (pointCode 55) (tileCode 3) = (446 : Fin 512) := by decide
private theorem tiling_code_447 : xorFin (pointCode 48) (tileCode 7) = (447 : Fin 512) := by decide
private theorem tiling_code_448 : xorFin (pointCode 56) (tileCode 0) = (448 : Fin 512) := by decide
private theorem tiling_code_449 : xorFin (pointCode 56) (tileCode 1) = (449 : Fin 512) := by decide
private theorem tiling_code_450 : xorFin (pointCode 56) (tileCode 2) = (450 : Fin 512) := by decide
private theorem tiling_code_451 : xorFin (pointCode 57) (tileCode 4) = (451 : Fin 512) := by decide
private theorem tiling_code_452 : xorFin (pointCode 56) (tileCode 3) = (452 : Fin 512) := by decide
private theorem tiling_code_453 : xorFin (pointCode 63) (tileCode 7) = (453 : Fin 512) := by decide
private theorem tiling_code_454 : xorFin (pointCode 60) (tileCode 6) = (454 : Fin 512) := by decide
private theorem tiling_code_455 : xorFin (pointCode 58) (tileCode 5) = (455 : Fin 512) := by decide
private theorem tiling_code_456 : xorFin (pointCode 56) (tileCode 4) = (456 : Fin 512) := by decide
private theorem tiling_code_457 : xorFin (pointCode 57) (tileCode 2) = (457 : Fin 512) := by decide
private theorem tiling_code_458 : xorFin (pointCode 57) (tileCode 1) = (458 : Fin 512) := by decide
private theorem tiling_code_459 : xorFin (pointCode 57) (tileCode 0) = (459 : Fin 512) := by decide
private theorem tiling_code_460 : xorFin (pointCode 59) (tileCode 5) = (460 : Fin 512) := by decide
private theorem tiling_code_461 : xorFin (pointCode 61) (tileCode 6) = (461 : Fin 512) := by decide
private theorem tiling_code_462 : xorFin (pointCode 62) (tileCode 7) = (462 : Fin 512) := by decide
private theorem tiling_code_463 : xorFin (pointCode 57) (tileCode 3) = (463 : Fin 512) := by decide
private theorem tiling_code_464 : xorFin (pointCode 56) (tileCode 5) = (464 : Fin 512) := by decide
private theorem tiling_code_465 : xorFin (pointCode 62) (tileCode 6) = (465 : Fin 512) := by decide
private theorem tiling_code_466 : xorFin (pointCode 61) (tileCode 7) = (466 : Fin 512) := by decide
private theorem tiling_code_467 : xorFin (pointCode 58) (tileCode 3) = (467 : Fin 512) := by decide
private theorem tiling_code_468 : xorFin (pointCode 59) (tileCode 4) = (468 : Fin 512) := by decide
private theorem tiling_code_469 : xorFin (pointCode 58) (tileCode 2) = (469 : Fin 512) := by decide
private theorem tiling_code_470 : xorFin (pointCode 58) (tileCode 1) = (470 : Fin 512) := by decide
private theorem tiling_code_471 : xorFin (pointCode 58) (tileCode 0) = (471 : Fin 512) := by decide
private theorem tiling_code_472 : xorFin (pointCode 59) (tileCode 3) = (472 : Fin 512) := by decide
private theorem tiling_code_473 : xorFin (pointCode 60) (tileCode 7) = (473 : Fin 512) := by decide
private theorem tiling_code_474 : xorFin (pointCode 63) (tileCode 6) = (474 : Fin 512) := by decide
private theorem tiling_code_475 : xorFin (pointCode 57) (tileCode 5) = (475 : Fin 512) := by decide
private theorem tiling_code_476 : xorFin (pointCode 59) (tileCode 0) = (476 : Fin 512) := by decide
private theorem tiling_code_477 : xorFin (pointCode 59) (tileCode 1) = (477 : Fin 512) := by decide
private theorem tiling_code_478 : xorFin (pointCode 59) (tileCode 2) = (478 : Fin 512) := by decide
private theorem tiling_code_479 : xorFin (pointCode 58) (tileCode 4) = (479 : Fin 512) := by decide
private theorem tiling_code_480 : xorFin (pointCode 56) (tileCode 6) = (480 : Fin 512) := by decide
private theorem tiling_code_481 : xorFin (pointCode 62) (tileCode 5) = (481 : Fin 512) := by decide
private theorem tiling_code_482 : xorFin (pointCode 60) (tileCode 3) = (482 : Fin 512) := by decide
private theorem tiling_code_483 : xorFin (pointCode 59) (tileCode 7) = (483 : Fin 512) := by decide
private theorem tiling_code_484 : xorFin (pointCode 60) (tileCode 2) = (484 : Fin 512) := by decide
private theorem tiling_code_485 : xorFin (pointCode 61) (tileCode 4) = (485 : Fin 512) := by decide
private theorem tiling_code_486 : xorFin (pointCode 60) (tileCode 0) = (486 : Fin 512) := by decide
private theorem tiling_code_487 : xorFin (pointCode 60) (tileCode 1) = (487 : Fin 512) := by decide
private theorem tiling_code_488 : xorFin (pointCode 58) (tileCode 7) = (488 : Fin 512) := by decide
private theorem tiling_code_489 : xorFin (pointCode 61) (tileCode 3) = (489 : Fin 512) := by decide
private theorem tiling_code_490 : xorFin (pointCode 63) (tileCode 5) = (490 : Fin 512) := by decide
private theorem tiling_code_491 : xorFin (pointCode 57) (tileCode 6) = (491 : Fin 512) := by decide
private theorem tiling_code_492 : xorFin (pointCode 61) (tileCode 1) = (492 : Fin 512) := by decide
private theorem tiling_code_493 : xorFin (pointCode 61) (tileCode 0) = (493 : Fin 512) := by decide
private theorem tiling_code_494 : xorFin (pointCode 60) (tileCode 4) = (494 : Fin 512) := by decide
private theorem tiling_code_495 : xorFin (pointCode 61) (tileCode 2) = (495 : Fin 512) := by decide
private theorem tiling_code_496 : xorFin (pointCode 62) (tileCode 1) = (496 : Fin 512) := by decide
private theorem tiling_code_497 : xorFin (pointCode 62) (tileCode 0) = (497 : Fin 512) := by decide
private theorem tiling_code_498 : xorFin (pointCode 63) (tileCode 4) = (498 : Fin 512) := by decide
private theorem tiling_code_499 : xorFin (pointCode 62) (tileCode 2) = (499 : Fin 512) := by decide
private theorem tiling_code_500 : xorFin (pointCode 57) (tileCode 7) = (500 : Fin 512) := by decide
private theorem tiling_code_501 : xorFin (pointCode 62) (tileCode 3) = (501 : Fin 512) := by decide
private theorem tiling_code_502 : xorFin (pointCode 60) (tileCode 5) = (502 : Fin 512) := by decide
private theorem tiling_code_503 : xorFin (pointCode 58) (tileCode 6) = (503 : Fin 512) := by decide
private theorem tiling_code_504 : xorFin (pointCode 63) (tileCode 2) = (504 : Fin 512) := by decide
private theorem tiling_code_505 : xorFin (pointCode 62) (tileCode 4) = (505 : Fin 512) := by decide
private theorem tiling_code_506 : xorFin (pointCode 63) (tileCode 0) = (506 : Fin 512) := by decide
private theorem tiling_code_507 : xorFin (pointCode 63) (tileCode 1) = (507 : Fin 512) := by decide
private theorem tiling_code_508 : xorFin (pointCode 59) (tileCode 6) = (508 : Fin 512) := by decide
private theorem tiling_code_509 : xorFin (pointCode 61) (tileCode 5) = (509 : Fin 512) := by decide
private theorem tiling_code_510 : xorFin (pointCode 63) (tileCode 3) = (510 : Fin 512) := by decide
private theorem tiling_code_511 : xorFin (pointCode 56) (tileCode 7) = (511 : Fin 512) := by decide

private theorem tiling_block_0 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨0 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨0, 0, tiling_code_0⟩
  · exact ⟨0, 1, tiling_code_1⟩
  · exact ⟨0, 2, tiling_code_2⟩
  · exact ⟨1, 4, tiling_code_3⟩
  · exact ⟨0, 3, tiling_code_4⟩
  · exact ⟨4, 6, tiling_code_5⟩
  · exact ⟨2, 5, tiling_code_6⟩
  · exact ⟨7, 7, tiling_code_7⟩
  · exact ⟨0, 4, tiling_code_8⟩
  · exact ⟨1, 2, tiling_code_9⟩
  · exact ⟨1, 1, tiling_code_10⟩
  · exact ⟨1, 0, tiling_code_11⟩
  · exact ⟨6, 7, tiling_code_12⟩
  · exact ⟨3, 5, tiling_code_13⟩
  · exact ⟨5, 6, tiling_code_14⟩
  · exact ⟨1, 3, tiling_code_15⟩
  · exact ⟨0, 5, tiling_code_16⟩
  · exact ⟨5, 7, tiling_code_17⟩
  · exact ⟨2, 3, tiling_code_18⟩
  · exact ⟨6, 6, tiling_code_19⟩
  · exact ⟨2, 2, tiling_code_20⟩
  · exact ⟨3, 4, tiling_code_21⟩
  · exact ⟨2, 0, tiling_code_22⟩
  · exact ⟨2, 1, tiling_code_23⟩
  · exact ⟨7, 6, tiling_code_24⟩
  · exact ⟨3, 3, tiling_code_25⟩
  · exact ⟨4, 7, tiling_code_26⟩
  · exact ⟨1, 5, tiling_code_27⟩
  · exact ⟨3, 1, tiling_code_28⟩
  · exact ⟨3, 0, tiling_code_29⟩
  · exact ⟨2, 4, tiling_code_30⟩
  · exact ⟨3, 2, tiling_code_31⟩
  · exact ⟨0, 6, tiling_code_32⟩
  · exact ⟨4, 3, tiling_code_33⟩
  · exact ⟨3, 7, tiling_code_34⟩
  · exact ⟨6, 5, tiling_code_35⟩
  · exact ⟨4, 1, tiling_code_36⟩
  · exact ⟨4, 0, tiling_code_37⟩
  · exact ⟨5, 4, tiling_code_38⟩
  · exact ⟨4, 2, tiling_code_39⟩
  · exact ⟨7, 5, tiling_code_40⟩
  · exact ⟨2, 7, tiling_code_41⟩
  · exact ⟨5, 3, tiling_code_42⟩
  · exact ⟨1, 6, tiling_code_43⟩
  · exact ⟨5, 2, tiling_code_44⟩
  · exact ⟨4, 4, tiling_code_45⟩
  · exact ⟨5, 0, tiling_code_46⟩
  · exact ⟨5, 1, tiling_code_47⟩
  · exact ⟨7, 4, tiling_code_48⟩
  · exact ⟨6, 2, tiling_code_49⟩
  · exact ⟨6, 1, tiling_code_50⟩
  · exact ⟨6, 0, tiling_code_51⟩
  · exact ⟨1, 7, tiling_code_52⟩
  · exact ⟨4, 5, tiling_code_53⟩
  · exact ⟨2, 6, tiling_code_54⟩
  · exact ⟨6, 3, tiling_code_55⟩
  · exact ⟨7, 0, tiling_code_56⟩
  · exact ⟨7, 1, tiling_code_57⟩
  · exact ⟨7, 2, tiling_code_58⟩
  · exact ⟨6, 4, tiling_code_59⟩
  · exact ⟨7, 3, tiling_code_60⟩
  · exact ⟨3, 6, tiling_code_61⟩
  · exact ⟨5, 5, tiling_code_62⟩
  · exact ⟨0, 7, tiling_code_63⟩
private theorem tiling_block_1 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨64 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨8, 0, tiling_code_64⟩
  · exact ⟨8, 1, tiling_code_65⟩
  · exact ⟨8, 2, tiling_code_66⟩
  · exact ⟨9, 3, tiling_code_67⟩
  · exact ⟨8, 3, tiling_code_68⟩
  · exact ⟨9, 2, tiling_code_69⟩
  · exact ⟨9, 1, tiling_code_70⟩
  · exact ⟨9, 0, tiling_code_71⟩
  · exact ⟨8, 4, tiling_code_72⟩
  · exact ⟨15, 7, tiling_code_73⟩
  · exact ⟨10, 5, tiling_code_74⟩
  · exact ⟨12, 6, tiling_code_75⟩
  · exact ⟨13, 6, tiling_code_76⟩
  · exact ⟨11, 5, tiling_code_77⟩
  · exact ⟨14, 7, tiling_code_78⟩
  · exact ⟨9, 4, tiling_code_79⟩
  · exact ⟨8, 5, tiling_code_80⟩
  · exact ⟨14, 6, tiling_code_81⟩
  · exact ⟨10, 4, tiling_code_82⟩
  · exact ⟨13, 7, tiling_code_83⟩
  · exact ⟨12, 7, tiling_code_84⟩
  · exact ⟨11, 4, tiling_code_85⟩
  · exact ⟨15, 6, tiling_code_86⟩
  · exact ⟨9, 5, tiling_code_87⟩
  · exact ⟨10, 2, tiling_code_88⟩
  · exact ⟨11, 3, tiling_code_89⟩
  · exact ⟨10, 0, tiling_code_90⟩
  · exact ⟨10, 1, tiling_code_91⟩
  · exact ⟨11, 1, tiling_code_92⟩
  · exact ⟨11, 0, tiling_code_93⟩
  · exact ⟨10, 3, tiling_code_94⟩
  · exact ⟨11, 2, tiling_code_95⟩
  · exact ⟨8, 6, tiling_code_96⟩
  · exact ⟨14, 5, tiling_code_97⟩
  · exact ⟨11, 7, tiling_code_98⟩
  · exact ⟨12, 4, tiling_code_99⟩
  · exact ⟨13, 4, tiling_code_100⟩
  · exact ⟨10, 7, tiling_code_101⟩
  · exact ⟨15, 5, tiling_code_102⟩
  · exact ⟨9, 6, tiling_code_103⟩
  · exact ⟨13, 3, tiling_code_104⟩
  · exact ⟨12, 2, tiling_code_105⟩
  · exact ⟨12, 1, tiling_code_106⟩
  · exact ⟨12, 0, tiling_code_107⟩
  · exact ⟨13, 0, tiling_code_108⟩
  · exact ⟨13, 1, tiling_code_109⟩
  · exact ⟨13, 2, tiling_code_110⟩
  · exact ⟨12, 3, tiling_code_111⟩
  · exact ⟨14, 1, tiling_code_112⟩
  · exact ⟨14, 0, tiling_code_113⟩
  · exact ⟨15, 3, tiling_code_114⟩
  · exact ⟨14, 2, tiling_code_115⟩
  · exact ⟨15, 2, tiling_code_116⟩
  · exact ⟨14, 3, tiling_code_117⟩
  · exact ⟨15, 0, tiling_code_118⟩
  · exact ⟨15, 1, tiling_code_119⟩
  · exact ⟨9, 7, tiling_code_120⟩
  · exact ⟨14, 4, tiling_code_121⟩
  · exact ⟨10, 6, tiling_code_122⟩
  · exact ⟨12, 5, tiling_code_123⟩
  · exact ⟨13, 5, tiling_code_124⟩
  · exact ⟨11, 6, tiling_code_125⟩
  · exact ⟨15, 4, tiling_code_126⟩
  · exact ⟨8, 7, tiling_code_127⟩
private theorem tiling_block_2 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨128 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨16, 0, tiling_code_128⟩
  · exact ⟨16, 1, tiling_code_129⟩
  · exact ⟨16, 2, tiling_code_130⟩
  · exact ⟨20, 6, tiling_code_131⟩
  · exact ⟨16, 3, tiling_code_132⟩
  · exact ⟨23, 7, tiling_code_133⟩
  · exact ⟨17, 4, tiling_code_134⟩
  · exact ⟨18, 5, tiling_code_135⟩
  · exact ⟨16, 4, tiling_code_136⟩
  · exact ⟨19, 5, tiling_code_137⟩
  · exact ⟨17, 3, tiling_code_138⟩
  · exact ⟨22, 7, tiling_code_139⟩
  · exact ⟨17, 2, tiling_code_140⟩
  · exact ⟨21, 6, tiling_code_141⟩
  · exact ⟨17, 0, tiling_code_142⟩
  · exact ⟨17, 1, tiling_code_143⟩
  · exact ⟨16, 5, tiling_code_144⟩
  · exact ⟨19, 4, tiling_code_145⟩
  · exact ⟨21, 7, tiling_code_146⟩
  · exact ⟨18, 3, tiling_code_147⟩
  · exact ⟨22, 6, tiling_code_148⟩
  · exact ⟨18, 2, tiling_code_149⟩
  · exact ⟨18, 1, tiling_code_150⟩
  · exact ⟨18, 0, tiling_code_151⟩
  · exact ⟨19, 1, tiling_code_152⟩
  · exact ⟨19, 0, tiling_code_153⟩
  · exact ⟨23, 6, tiling_code_154⟩
  · exact ⟨19, 2, tiling_code_155⟩
  · exact ⟨20, 7, tiling_code_156⟩
  · exact ⟨19, 3, tiling_code_157⟩
  · exact ⟨17, 5, tiling_code_158⟩
  · exact ⟨18, 4, tiling_code_159⟩
  · exact ⟨16, 6, tiling_code_160⟩
  · exact ⟨20, 2, tiling_code_161⟩
  · exact ⟨20, 1, tiling_code_162⟩
  · exact ⟨20, 0, tiling_code_163⟩
  · exact ⟨22, 5, tiling_code_164⟩
  · exact ⟨21, 4, tiling_code_165⟩
  · exact ⟨19, 7, tiling_code_166⟩
  · exact ⟨20, 3, tiling_code_167⟩
  · exact ⟨18, 7, tiling_code_168⟩
  · exact ⟨21, 3, tiling_code_169⟩
  · exact ⟨23, 5, tiling_code_170⟩
  · exact ⟨20, 4, tiling_code_171⟩
  · exact ⟨21, 1, tiling_code_172⟩
  · exact ⟨21, 0, tiling_code_173⟩
  · exact ⟨17, 6, tiling_code_174⟩
  · exact ⟨21, 2, tiling_code_175⟩
  · exact ⟨22, 3, tiling_code_176⟩
  · exact ⟨17, 7, tiling_code_177⟩
  · exact ⟨23, 4, tiling_code_178⟩
  · exact ⟨20, 5, tiling_code_179⟩
  · exact ⟨22, 0, tiling_code_180⟩
  · exact ⟨22, 1, tiling_code_181⟩
  · exact ⟨22, 2, tiling_code_182⟩
  · exact ⟨18, 6, tiling_code_183⟩
  · exact ⟨23, 2, tiling_code_184⟩
  · exact ⟨19, 6, tiling_code_185⟩
  · exact ⟨23, 0, tiling_code_186⟩
  · exact ⟨23, 1, tiling_code_187⟩
  · exact ⟨22, 4, tiling_code_188⟩
  · exact ⟨21, 5, tiling_code_189⟩
  · exact ⟨23, 3, tiling_code_190⟩
  · exact ⟨16, 7, tiling_code_191⟩
private theorem tiling_block_3 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨192 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨24, 0, tiling_code_192⟩
  · exact ⟨24, 1, tiling_code_193⟩
  · exact ⟨24, 2, tiling_code_194⟩
  · exact ⟨31, 7, tiling_code_195⟩
  · exact ⟨24, 3, tiling_code_196⟩
  · exact ⟨25, 4, tiling_code_197⟩
  · exact ⟨26, 5, tiling_code_198⟩
  · exact ⟨28, 6, tiling_code_199⟩
  · exact ⟨24, 4, tiling_code_200⟩
  · exact ⟨25, 3, tiling_code_201⟩
  · exact ⟨29, 6, tiling_code_202⟩
  · exact ⟨27, 5, tiling_code_203⟩
  · exact ⟨25, 1, tiling_code_204⟩
  · exact ⟨25, 0, tiling_code_205⟩
  · exact ⟨30, 7, tiling_code_206⟩
  · exact ⟨25, 2, tiling_code_207⟩
  · exact ⟨24, 5, tiling_code_208⟩
  · exact ⟨30, 6, tiling_code_209⟩
  · exact ⟨26, 3, tiling_code_210⟩
  · exact ⟨27, 4, tiling_code_211⟩
  · exact ⟨26, 2, tiling_code_212⟩
  · exact ⟨29, 7, tiling_code_213⟩
  · exact ⟨26, 0, tiling_code_214⟩
  · exact ⟨26, 1, tiling_code_215⟩
  · exact ⟨28, 7, tiling_code_216⟩
  · exact ⟨27, 2, tiling_code_217⟩
  · exact ⟨27, 1, tiling_code_218⟩
  · exact ⟨27, 0, tiling_code_219⟩
  · exact ⟨31, 6, tiling_code_220⟩
  · exact ⟨25, 5, tiling_code_221⟩
  · exact ⟨26, 4, tiling_code_222⟩
  · exact ⟨27, 3, tiling_code_223⟩
  · exact ⟨24, 6, tiling_code_224⟩
  · exact ⟨30, 5, tiling_code_225⟩
  · exact ⟨29, 4, tiling_code_226⟩
  · exact ⟨28, 3, tiling_code_227⟩
  · exact ⟨27, 7, tiling_code_228⟩
  · exact ⟨28, 2, tiling_code_229⟩
  · exact ⟨28, 1, tiling_code_230⟩
  · exact ⟨28, 0, tiling_code_231⟩
  · exact ⟨29, 2, tiling_code_232⟩
  · exact ⟨26, 7, tiling_code_233⟩
  · exact ⟨29, 0, tiling_code_234⟩
  · exact ⟨29, 1, tiling_code_235⟩
  · exact ⟨31, 5, tiling_code_236⟩
  · exact ⟨25, 6, tiling_code_237⟩
  · exact ⟨29, 3, tiling_code_238⟩
  · exact ⟨28, 4, tiling_code_239⟩
  · exact ⟨30, 1, tiling_code_240⟩
  · exact ⟨30, 0, tiling_code_241⟩
  · exact ⟨25, 7, tiling_code_242⟩
  · exact ⟨30, 2, tiling_code_243⟩
  · exact ⟨31, 4, tiling_code_244⟩
  · exact ⟨30, 3, tiling_code_245⟩
  · exact ⟨26, 6, tiling_code_246⟩
  · exact ⟨28, 5, tiling_code_247⟩
  · exact ⟨31, 3, tiling_code_248⟩
  · exact ⟨30, 4, tiling_code_249⟩
  · exact ⟨29, 5, tiling_code_250⟩
  · exact ⟨27, 6, tiling_code_251⟩
  · exact ⟨31, 0, tiling_code_252⟩
  · exact ⟨31, 1, tiling_code_253⟩
  · exact ⟨31, 2, tiling_code_254⟩
  · exact ⟨24, 7, tiling_code_255⟩
private theorem tiling_block_4 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨256 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨32, 0, tiling_code_256⟩
  · exact ⟨32, 1, tiling_code_257⟩
  · exact ⟨32, 2, tiling_code_258⟩
  · exact ⟨33, 3, tiling_code_259⟩
  · exact ⟨32, 3, tiling_code_260⟩
  · exact ⟨33, 2, tiling_code_261⟩
  · exact ⟨33, 1, tiling_code_262⟩
  · exact ⟨33, 0, tiling_code_263⟩
  · exact ⟨32, 4, tiling_code_264⟩
  · exact ⟨39, 7, tiling_code_265⟩
  · exact ⟨34, 5, tiling_code_266⟩
  · exact ⟨36, 6, tiling_code_267⟩
  · exact ⟨37, 6, tiling_code_268⟩
  · exact ⟨35, 5, tiling_code_269⟩
  · exact ⟨38, 7, tiling_code_270⟩
  · exact ⟨33, 4, tiling_code_271⟩
  · exact ⟨32, 5, tiling_code_272⟩
  · exact ⟨38, 6, tiling_code_273⟩
  · exact ⟨34, 4, tiling_code_274⟩
  · exact ⟨37, 7, tiling_code_275⟩
  · exact ⟨36, 7, tiling_code_276⟩
  · exact ⟨35, 4, tiling_code_277⟩
  · exact ⟨39, 6, tiling_code_278⟩
  · exact ⟨33, 5, tiling_code_279⟩
  · exact ⟨34, 2, tiling_code_280⟩
  · exact ⟨35, 3, tiling_code_281⟩
  · exact ⟨34, 0, tiling_code_282⟩
  · exact ⟨34, 1, tiling_code_283⟩
  · exact ⟨35, 1, tiling_code_284⟩
  · exact ⟨35, 0, tiling_code_285⟩
  · exact ⟨34, 3, tiling_code_286⟩
  · exact ⟨35, 2, tiling_code_287⟩
  · exact ⟨32, 6, tiling_code_288⟩
  · exact ⟨38, 5, tiling_code_289⟩
  · exact ⟨35, 7, tiling_code_290⟩
  · exact ⟨36, 4, tiling_code_291⟩
  · exact ⟨37, 4, tiling_code_292⟩
  · exact ⟨34, 7, tiling_code_293⟩
  · exact ⟨39, 5, tiling_code_294⟩
  · exact ⟨33, 6, tiling_code_295⟩
  · exact ⟨37, 3, tiling_code_296⟩
  · exact ⟨36, 2, tiling_code_297⟩
  · exact ⟨36, 1, tiling_code_298⟩
  · exact ⟨36, 0, tiling_code_299⟩
  · exact ⟨37, 0, tiling_code_300⟩
  · exact ⟨37, 1, tiling_code_301⟩
  · exact ⟨37, 2, tiling_code_302⟩
  · exact ⟨36, 3, tiling_code_303⟩
  · exact ⟨38, 1, tiling_code_304⟩
  · exact ⟨38, 0, tiling_code_305⟩
  · exact ⟨39, 3, tiling_code_306⟩
  · exact ⟨38, 2, tiling_code_307⟩
  · exact ⟨39, 2, tiling_code_308⟩
  · exact ⟨38, 3, tiling_code_309⟩
  · exact ⟨39, 0, tiling_code_310⟩
  · exact ⟨39, 1, tiling_code_311⟩
  · exact ⟨33, 7, tiling_code_312⟩
  · exact ⟨38, 4, tiling_code_313⟩
  · exact ⟨34, 6, tiling_code_314⟩
  · exact ⟨36, 5, tiling_code_315⟩
  · exact ⟨37, 5, tiling_code_316⟩
  · exact ⟨35, 6, tiling_code_317⟩
  · exact ⟨39, 4, tiling_code_318⟩
  · exact ⟨32, 7, tiling_code_319⟩
private theorem tiling_block_5 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨320 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨40, 0, tiling_code_320⟩
  · exact ⟨40, 1, tiling_code_321⟩
  · exact ⟨40, 2, tiling_code_322⟩
  · exact ⟨41, 4, tiling_code_323⟩
  · exact ⟨40, 3, tiling_code_324⟩
  · exact ⟨42, 5, tiling_code_325⟩
  · exact ⟨47, 7, tiling_code_326⟩
  · exact ⟨44, 6, tiling_code_327⟩
  · exact ⟨40, 4, tiling_code_328⟩
  · exact ⟨41, 2, tiling_code_329⟩
  · exact ⟨41, 1, tiling_code_330⟩
  · exact ⟨41, 0, tiling_code_331⟩
  · exact ⟨45, 6, tiling_code_332⟩
  · exact ⟨46, 7, tiling_code_333⟩
  · exact ⟨43, 5, tiling_code_334⟩
  · exact ⟨41, 3, tiling_code_335⟩
  · exact ⟨40, 5, tiling_code_336⟩
  · exact ⟨42, 3, tiling_code_337⟩
  · exact ⟨46, 6, tiling_code_338⟩
  · exact ⟨45, 7, tiling_code_339⟩
  · exact ⟨42, 1, tiling_code_340⟩
  · exact ⟨42, 0, tiling_code_341⟩
  · exact ⟨43, 4, tiling_code_342⟩
  · exact ⟨42, 2, tiling_code_343⟩
  · exact ⟨44, 7, tiling_code_344⟩
  · exact ⟨47, 6, tiling_code_345⟩
  · exact ⟨43, 3, tiling_code_346⟩
  · exact ⟨41, 5, tiling_code_347⟩
  · exact ⟨43, 2, tiling_code_348⟩
  · exact ⟨42, 4, tiling_code_349⟩
  · exact ⟨43, 0, tiling_code_350⟩
  · exact ⟨43, 1, tiling_code_351⟩
  · exact ⟨40, 6, tiling_code_352⟩
  · exact ⟨43, 7, tiling_code_353⟩
  · exact ⟨46, 5, tiling_code_354⟩
  · exact ⟨44, 3, tiling_code_355⟩
  · exact ⟨45, 4, tiling_code_356⟩
  · exact ⟨44, 2, tiling_code_357⟩
  · exact ⟨44, 1, tiling_code_358⟩
  · exact ⟨44, 0, tiling_code_359⟩
  · exact ⟨45, 3, tiling_code_360⟩
  · exact ⟨47, 5, tiling_code_361⟩
  · exact ⟨42, 7, tiling_code_362⟩
  · exact ⟨41, 6, tiling_code_363⟩
  · exact ⟨45, 0, tiling_code_364⟩
  · exact ⟨45, 1, tiling_code_365⟩
  · exact ⟨45, 2, tiling_code_366⟩
  · exact ⟨44, 4, tiling_code_367⟩
  · exact ⟨46, 2, tiling_code_368⟩
  · exact ⟨47, 4, tiling_code_369⟩
  · exact ⟨46, 0, tiling_code_370⟩
  · exact ⟨46, 1, tiling_code_371⟩
  · exact ⟨41, 7, tiling_code_372⟩
  · exact ⟨42, 6, tiling_code_373⟩
  · exact ⟨46, 3, tiling_code_374⟩
  · exact ⟨44, 5, tiling_code_375⟩
  · exact ⟨47, 1, tiling_code_376⟩
  · exact ⟨47, 0, tiling_code_377⟩
  · exact ⟨46, 4, tiling_code_378⟩
  · exact ⟨47, 2, tiling_code_379⟩
  · exact ⟨45, 5, tiling_code_380⟩
  · exact ⟨47, 3, tiling_code_381⟩
  · exact ⟨43, 6, tiling_code_382⟩
  · exact ⟨40, 7, tiling_code_383⟩
private theorem tiling_block_6 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨384 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨48, 0, tiling_code_384⟩
  · exact ⟨48, 1, tiling_code_385⟩
  · exact ⟨48, 2, tiling_code_386⟩
  · exact ⟨50, 5, tiling_code_387⟩
  · exact ⟨48, 3, tiling_code_388⟩
  · exact ⟨55, 7, tiling_code_389⟩
  · exact ⟨52, 6, tiling_code_390⟩
  · exact ⟨49, 4, tiling_code_391⟩
  · exact ⟨48, 4, tiling_code_392⟩
  · exact ⟨53, 6, tiling_code_393⟩
  · exact ⟨54, 7, tiling_code_394⟩
  · exact ⟨49, 3, tiling_code_395⟩
  · exact ⟨51, 5, tiling_code_396⟩
  · exact ⟨49, 2, tiling_code_397⟩
  · exact ⟨49, 1, tiling_code_398⟩
  · exact ⟨49, 0, tiling_code_399⟩
  · exact ⟨48, 5, tiling_code_400⟩
  · exact ⟨50, 2, tiling_code_401⟩
  · exact ⟨50, 1, tiling_code_402⟩
  · exact ⟨50, 0, tiling_code_403⟩
  · exact ⟨51, 4, tiling_code_404⟩
  · exact ⟨54, 6, tiling_code_405⟩
  · exact ⟨53, 7, tiling_code_406⟩
  · exact ⟨50, 3, tiling_code_407⟩
  · exact ⟨51, 3, tiling_code_408⟩
  · exact ⟨52, 7, tiling_code_409⟩
  · exact ⟨55, 6, tiling_code_410⟩
  · exact ⟨50, 4, tiling_code_411⟩
  · exact ⟨51, 0, tiling_code_412⟩
  · exact ⟨51, 1, tiling_code_413⟩
  · exact ⟨51, 2, tiling_code_414⟩
  · exact ⟨49, 5, tiling_code_415⟩
  · exact ⟨48, 6, tiling_code_416⟩
  · exact ⟨53, 4, tiling_code_417⟩
  · exact ⟨52, 3, tiling_code_418⟩
  · exact ⟨51, 7, tiling_code_419⟩
  · exact ⟨52, 2, tiling_code_420⟩
  · exact ⟨54, 5, tiling_code_421⟩
  · exact ⟨52, 0, tiling_code_422⟩
  · exact ⟨52, 1, tiling_code_423⟩
  · exact ⟨53, 1, tiling_code_424⟩
  · exact ⟨53, 0, tiling_code_425⟩
  · exact ⟨55, 5, tiling_code_426⟩
  · exact ⟨53, 2, tiling_code_427⟩
  · exact ⟨50, 7, tiling_code_428⟩
  · exact ⟨53, 3, tiling_code_429⟩
  · exact ⟨52, 4, tiling_code_430⟩
  · exact ⟨49, 6, tiling_code_431⟩
  · exact ⟨49, 7, tiling_code_432⟩
  · exact ⟨54, 3, tiling_code_433⟩
  · exact ⟨55, 4, tiling_code_434⟩
  · exact ⟨50, 6, tiling_code_435⟩
  · exact ⟨54, 1, tiling_code_436⟩
  · exact ⟨54, 0, tiling_code_437⟩
  · exact ⟨52, 5, tiling_code_438⟩
  · exact ⟨54, 2, tiling_code_439⟩
  · exact ⟨55, 2, tiling_code_440⟩
  · exact ⟨53, 5, tiling_code_441⟩
  · exact ⟨55, 0, tiling_code_442⟩
  · exact ⟨55, 1, tiling_code_443⟩
  · exact ⟨51, 6, tiling_code_444⟩
  · exact ⟨54, 4, tiling_code_445⟩
  · exact ⟨55, 3, tiling_code_446⟩
  · exact ⟨48, 7, tiling_code_447⟩
private theorem tiling_block_7 (k : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8, xorFin (pointCode i) (tileCode j) = (⟨448 + k.val, by omega⟩ : Fin 512) := by
  fin_cases k
  · exact ⟨56, 0, tiling_code_448⟩
  · exact ⟨56, 1, tiling_code_449⟩
  · exact ⟨56, 2, tiling_code_450⟩
  · exact ⟨57, 4, tiling_code_451⟩
  · exact ⟨56, 3, tiling_code_452⟩
  · exact ⟨63, 7, tiling_code_453⟩
  · exact ⟨60, 6, tiling_code_454⟩
  · exact ⟨58, 5, tiling_code_455⟩
  · exact ⟨56, 4, tiling_code_456⟩
  · exact ⟨57, 2, tiling_code_457⟩
  · exact ⟨57, 1, tiling_code_458⟩
  · exact ⟨57, 0, tiling_code_459⟩
  · exact ⟨59, 5, tiling_code_460⟩
  · exact ⟨61, 6, tiling_code_461⟩
  · exact ⟨62, 7, tiling_code_462⟩
  · exact ⟨57, 3, tiling_code_463⟩
  · exact ⟨56, 5, tiling_code_464⟩
  · exact ⟨62, 6, tiling_code_465⟩
  · exact ⟨61, 7, tiling_code_466⟩
  · exact ⟨58, 3, tiling_code_467⟩
  · exact ⟨59, 4, tiling_code_468⟩
  · exact ⟨58, 2, tiling_code_469⟩
  · exact ⟨58, 1, tiling_code_470⟩
  · exact ⟨58, 0, tiling_code_471⟩
  · exact ⟨59, 3, tiling_code_472⟩
  · exact ⟨60, 7, tiling_code_473⟩
  · exact ⟨63, 6, tiling_code_474⟩
  · exact ⟨57, 5, tiling_code_475⟩
  · exact ⟨59, 0, tiling_code_476⟩
  · exact ⟨59, 1, tiling_code_477⟩
  · exact ⟨59, 2, tiling_code_478⟩
  · exact ⟨58, 4, tiling_code_479⟩
  · exact ⟨56, 6, tiling_code_480⟩
  · exact ⟨62, 5, tiling_code_481⟩
  · exact ⟨60, 3, tiling_code_482⟩
  · exact ⟨59, 7, tiling_code_483⟩
  · exact ⟨60, 2, tiling_code_484⟩
  · exact ⟨61, 4, tiling_code_485⟩
  · exact ⟨60, 0, tiling_code_486⟩
  · exact ⟨60, 1, tiling_code_487⟩
  · exact ⟨58, 7, tiling_code_488⟩
  · exact ⟨61, 3, tiling_code_489⟩
  · exact ⟨63, 5, tiling_code_490⟩
  · exact ⟨57, 6, tiling_code_491⟩
  · exact ⟨61, 1, tiling_code_492⟩
  · exact ⟨61, 0, tiling_code_493⟩
  · exact ⟨60, 4, tiling_code_494⟩
  · exact ⟨61, 2, tiling_code_495⟩
  · exact ⟨62, 1, tiling_code_496⟩
  · exact ⟨62, 0, tiling_code_497⟩
  · exact ⟨63, 4, tiling_code_498⟩
  · exact ⟨62, 2, tiling_code_499⟩
  · exact ⟨57, 7, tiling_code_500⟩
  · exact ⟨62, 3, tiling_code_501⟩
  · exact ⟨60, 5, tiling_code_502⟩
  · exact ⟨58, 6, tiling_code_503⟩
  · exact ⟨63, 2, tiling_code_504⟩
  · exact ⟨62, 4, tiling_code_505⟩
  · exact ⟨63, 0, tiling_code_506⟩
  · exact ⟨63, 1, tiling_code_507⟩
  · exact ⟨59, 6, tiling_code_508⟩
  · exact ⟨61, 5, tiling_code_509⟩
  · exact ⟨63, 3, tiling_code_510⟩
  · exact ⟨56, 7, tiling_code_511⟩

lemma code_tiling (k : Fin 512) : ∃ i : Fin 64, ∃ j : Fin 8,
    xorFin (pointCode i) (tileCode j) = k := by
  have hall (t : Fin 8) (l : Fin 64) : ∃ i : Fin 64, ∃ j : Fin 8,
      xorFin (pointCode i) (tileCode j) = (⟨64*t.val + l.val, by omega⟩ : Fin 512) := by
    fin_cases t
    · exact tiling_block_0 l
    · exact tiling_block_1 l
    · exact tiling_block_2 l
    · exact tiling_block_3 l
    · exact tiling_block_4 l
    · exact tiling_block_5 l
    · exact tiling_block_6 l
    · exact tiling_block_7 l
  let t : Fin 8 := ⟨k.val / 64, by omega⟩
  let l : Fin 64 := ⟨k.val % 64, Nat.mod_lt _ (by decide)⟩
  have hk : (⟨64*t.val + l.val, by omega⟩ : Fin 512) = k := by
    apply Fin.ext
    dsimp [t,l]
    omega
  simpa only [hk] using hall t l

end BinaryFuglede
