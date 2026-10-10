/-
# Chamber certificate: all `270` chambers.
-/
import Chamber_cert0
import Chamber_cert1
import Chamber_cert2
import Chamber_cert3
import Chamber_cert4
import Chamber_cert5
import Chamber_cert6
import Chamber_cert7
import Chamber_cert8
import Chamber_cert9
import Chamber_cert10
import Chamber_cert11
import Chamber_cert12
import Chamber_cert13
import Chamber_cert14
import Chamber_cert15
import Chamber_cert16
import Chamber_cert17
import Chamber_cert18
import Chamber_cert19
import Chamber_cert20
import Chamber_cert21
import Chamber_cert22
import Chamber_cert23
import Chamber_cert24
import Chamber_cert25
import Chamber_cert26
import Chamber_cert27
import Chamber_cert28
import Chamber_cert29

namespace ZetasIrr.CH

theorem chambers_ok_a : ∀ i < 135, chamberOK i = true := by
  intro i hi
  match i with
  | 0 => exact chamber_0
  | 1 => exact chamber_1
  | 2 => exact chamber_2
  | 3 => exact chamber_3
  | 4 => exact chamber_4
  | 5 => exact chamber_5
  | 6 => exact chamber_6
  | 7 => exact chamber_7
  | 8 => exact chamber_8
  | 9 => exact chamber_9
  | 10 => exact chamber_10
  | 11 => exact chamber_11
  | 12 => exact chamber_12
  | 13 => exact chamber_13
  | 14 => exact chamber_14
  | 15 => exact chamber_15
  | 16 => exact chamber_16
  | 17 => exact chamber_17
  | 18 => exact chamber_18
  | 19 => exact chamber_19
  | 20 => exact chamber_20
  | 21 => exact chamber_21
  | 22 => exact chamber_22
  | 23 => exact chamber_23
  | 24 => exact chamber_24
  | 25 => exact chamber_25
  | 26 => exact chamber_26
  | 27 => exact chamber_27
  | 28 => exact chamber_28
  | 29 => exact chamber_29
  | 30 => exact chamber_30
  | 31 => exact chamber_31
  | 32 => exact chamber_32
  | 33 => exact chamber_33
  | 34 => exact chamber_34
  | 35 => exact chamber_35
  | 36 => exact chamber_36
  | 37 => exact chamber_37
  | 38 => exact chamber_38
  | 39 => exact chamber_39
  | 40 => exact chamber_40
  | 41 => exact chamber_41
  | 42 => exact chamber_42
  | 43 => exact chamber_43
  | 44 => exact chamber_44
  | 45 => exact chamber_45
  | 46 => exact chamber_46
  | 47 => exact chamber_47
  | 48 => exact chamber_48
  | 49 => exact chamber_49
  | 50 => exact chamber_50
  | 51 => exact chamber_51
  | 52 => exact chamber_52
  | 53 => exact chamber_53
  | 54 => exact chamber_54
  | 55 => exact chamber_55
  | 56 => exact chamber_56
  | 57 => exact chamber_57
  | 58 => exact chamber_58
  | 59 => exact chamber_59
  | 60 => exact chamber_60
  | 61 => exact chamber_61
  | 62 => exact chamber_62
  | 63 => exact chamber_63
  | 64 => exact chamber_64
  | 65 => exact chamber_65
  | 66 => exact chamber_66
  | 67 => exact chamber_67
  | 68 => exact chamber_68
  | 69 => exact chamber_69
  | 70 => exact chamber_70
  | 71 => exact chamber_71
  | 72 => exact chamber_72
  | 73 => exact chamber_73
  | 74 => exact chamber_74
  | 75 => exact chamber_75
  | 76 => exact chamber_76
  | 77 => exact chamber_77
  | 78 => exact chamber_78
  | 79 => exact chamber_79
  | 80 => exact chamber_80
  | 81 => exact chamber_81
  | 82 => exact chamber_82
  | 83 => exact chamber_83
  | 84 => exact chamber_84
  | 85 => exact chamber_85
  | 86 => exact chamber_86
  | 87 => exact chamber_87
  | 88 => exact chamber_88
  | 89 => exact chamber_89
  | 90 => exact chamber_90
  | 91 => exact chamber_91
  | 92 => exact chamber_92
  | 93 => exact chamber_93
  | 94 => exact chamber_94
  | 95 => exact chamber_95
  | 96 => exact chamber_96
  | 97 => exact chamber_97
  | 98 => exact chamber_98
  | 99 => exact chamber_99
  | 100 => exact chamber_100
  | 101 => exact chamber_101
  | 102 => exact chamber_102
  | 103 => exact chamber_103
  | 104 => exact chamber_104
  | 105 => exact chamber_105
  | 106 => exact chamber_106
  | 107 => exact chamber_107
  | 108 => exact chamber_108
  | 109 => exact chamber_109
  | 110 => exact chamber_110
  | 111 => exact chamber_111
  | 112 => exact chamber_112
  | 113 => exact chamber_113
  | 114 => exact chamber_114
  | 115 => exact chamber_115
  | 116 => exact chamber_116
  | 117 => exact chamber_117
  | 118 => exact chamber_118
  | 119 => exact chamber_119
  | 120 => exact chamber_120
  | 121 => exact chamber_121
  | 122 => exact chamber_122
  | 123 => exact chamber_123
  | 124 => exact chamber_124
  | 125 => exact chamber_125
  | 126 => exact chamber_126
  | 127 => exact chamber_127
  | 128 => exact chamber_128
  | 129 => exact chamber_129
  | 130 => exact chamber_130
  | 131 => exact chamber_131
  | 132 => exact chamber_132
  | 133 => exact chamber_133
  | 134 => exact chamber_134
  | n + 135 => omega

theorem chambers_ok_b : ∀ i < 135, chamberOK (135 + i) = true := by
  intro i hi
  match i with
  | 0 => exact chamber_135
  | 1 => exact chamber_136
  | 2 => exact chamber_137
  | 3 => exact chamber_138
  | 4 => exact chamber_139
  | 5 => exact chamber_140
  | 6 => exact chamber_141
  | 7 => exact chamber_142
  | 8 => exact chamber_143
  | 9 => exact chamber_144
  | 10 => exact chamber_145
  | 11 => exact chamber_146
  | 12 => exact chamber_147
  | 13 => exact chamber_148
  | 14 => exact chamber_149
  | 15 => exact chamber_150
  | 16 => exact chamber_151
  | 17 => exact chamber_152
  | 18 => exact chamber_153
  | 19 => exact chamber_154
  | 20 => exact chamber_155
  | 21 => exact chamber_156
  | 22 => exact chamber_157
  | 23 => exact chamber_158
  | 24 => exact chamber_159
  | 25 => exact chamber_160
  | 26 => exact chamber_161
  | 27 => exact chamber_162
  | 28 => exact chamber_163
  | 29 => exact chamber_164
  | 30 => exact chamber_165
  | 31 => exact chamber_166
  | 32 => exact chamber_167
  | 33 => exact chamber_168
  | 34 => exact chamber_169
  | 35 => exact chamber_170
  | 36 => exact chamber_171
  | 37 => exact chamber_172
  | 38 => exact chamber_173
  | 39 => exact chamber_174
  | 40 => exact chamber_175
  | 41 => exact chamber_176
  | 42 => exact chamber_177
  | 43 => exact chamber_178
  | 44 => exact chamber_179
  | 45 => exact chamber_180
  | 46 => exact chamber_181
  | 47 => exact chamber_182
  | 48 => exact chamber_183
  | 49 => exact chamber_184
  | 50 => exact chamber_185
  | 51 => exact chamber_186
  | 52 => exact chamber_187
  | 53 => exact chamber_188
  | 54 => exact chamber_189
  | 55 => exact chamber_190
  | 56 => exact chamber_191
  | 57 => exact chamber_192
  | 58 => exact chamber_193
  | 59 => exact chamber_194
  | 60 => exact chamber_195
  | 61 => exact chamber_196
  | 62 => exact chamber_197
  | 63 => exact chamber_198
  | 64 => exact chamber_199
  | 65 => exact chamber_200
  | 66 => exact chamber_201
  | 67 => exact chamber_202
  | 68 => exact chamber_203
  | 69 => exact chamber_204
  | 70 => exact chamber_205
  | 71 => exact chamber_206
  | 72 => exact chamber_207
  | 73 => exact chamber_208
  | 74 => exact chamber_209
  | 75 => exact chamber_210
  | 76 => exact chamber_211
  | 77 => exact chamber_212
  | 78 => exact chamber_213
  | 79 => exact chamber_214
  | 80 => exact chamber_215
  | 81 => exact chamber_216
  | 82 => exact chamber_217
  | 83 => exact chamber_218
  | 84 => exact chamber_219
  | 85 => exact chamber_220
  | 86 => exact chamber_221
  | 87 => exact chamber_222
  | 88 => exact chamber_223
  | 89 => exact chamber_224
  | 90 => exact chamber_225
  | 91 => exact chamber_226
  | 92 => exact chamber_227
  | 93 => exact chamber_228
  | 94 => exact chamber_229
  | 95 => exact chamber_230
  | 96 => exact chamber_231
  | 97 => exact chamber_232
  | 98 => exact chamber_233
  | 99 => exact chamber_234
  | 100 => exact chamber_235
  | 101 => exact chamber_236
  | 102 => exact chamber_237
  | 103 => exact chamber_238
  | 104 => exact chamber_239
  | 105 => exact chamber_240
  | 106 => exact chamber_241
  | 107 => exact chamber_242
  | 108 => exact chamber_243
  | 109 => exact chamber_244
  | 110 => exact chamber_245
  | 111 => exact chamber_246
  | 112 => exact chamber_247
  | 113 => exact chamber_248
  | 114 => exact chamber_249
  | 115 => exact chamber_250
  | 116 => exact chamber_251
  | 117 => exact chamber_252
  | 118 => exact chamber_253
  | 119 => exact chamber_254
  | 120 => exact chamber_255
  | 121 => exact chamber_256
  | 122 => exact chamber_257
  | 123 => exact chamber_258
  | 124 => exact chamber_259
  | 125 => exact chamber_260
  | 126 => exact chamber_261
  | 127 => exact chamber_262
  | 128 => exact chamber_263
  | 129 => exact chamber_264
  | 130 => exact chamber_265
  | 131 => exact chamber_266
  | 132 => exact chamber_267
  | 133 => exact chamber_268
  | 134 => exact chamber_269
  | n + 135 => omega

theorem chambers_ok : ∀ i < 270, chamberOK i = true := by
  intro i hi
  rcases Nat.lt_or_ge i 135 with h | h
  · exact chambers_ok_a i h
  · have := chambers_ok_b (i - 135) (by omega)
    rwa [show 135 + (i - 135) = i by omega] at this

end ZetasIrr.CH
