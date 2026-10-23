/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all Init.Util

public import Cryptids.Compilation.RuntimeModel
public import Cryptids.Compilation.RuntimeSupport
public import Cryptids.Compilation.NumberTM2

/-! # Complete local certification of the literal numeric TM2 runtime

Every row is checked separately by structural equality and finite function enumeration
in the Lean kernel. The decoder reads the fixed source label list; it performs no search
for a first occurrence and assumes no global construction or hash-order identity.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.RuntimeCertificate
open Turing PartrecToTM2 StateTransition Relation

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

/-- A local row decoder, independent of source first-occurrence numbering. -/
def decode (state : RuntimeModel.Label) : Λ' :=
  (Runtime.label .start :: Runtime.labels).get ⟨state.val, by
    rw [List.length_cons, RuntimeSupport.labels_length]
    exact state.isLt⟩

theorem decode_zero : decode 0 = Runtime.label .start := rfl

theorem row_000 :
    TM2Number.mapStmt decode (RuntimeModel.machine 0) =
      Runtime.machine (decode 0) := by decide +kernel

theorem row_001 :
    TM2Number.mapStmt decode (RuntimeModel.machine 1) =
      Runtime.machine (decode 1) := by decide +kernel

theorem row_002 :
    TM2Number.mapStmt decode (RuntimeModel.machine 2) =
      Runtime.machine (decode 2) := by decide +kernel

theorem row_003 :
    TM2Number.mapStmt decode (RuntimeModel.machine 3) =
      Runtime.machine (decode 3) := by decide +kernel

theorem row_004 :
    TM2Number.mapStmt decode (RuntimeModel.machine 4) =
      Runtime.machine (decode 4) := by decide +kernel

theorem row_005 :
    TM2Number.mapStmt decode (RuntimeModel.machine 5) =
      Runtime.machine (decode 5) := by decide +kernel

theorem row_006 :
    TM2Number.mapStmt decode (RuntimeModel.machine 6) =
      Runtime.machine (decode 6) := by decide +kernel

theorem row_007 :
    TM2Number.mapStmt decode (RuntimeModel.machine 7) =
      Runtime.machine (decode 7) := by decide +kernel

theorem row_008 :
    TM2Number.mapStmt decode (RuntimeModel.machine 8) =
      Runtime.machine (decode 8) := by decide +kernel

theorem row_009 :
    TM2Number.mapStmt decode (RuntimeModel.machine 9) =
      Runtime.machine (decode 9) := by decide +kernel

theorem row_010 :
    TM2Number.mapStmt decode (RuntimeModel.machine 10) =
      Runtime.machine (decode 10) := by decide +kernel

theorem row_011 :
    TM2Number.mapStmt decode (RuntimeModel.machine 11) =
      Runtime.machine (decode 11) := by decide +kernel

theorem row_012 :
    TM2Number.mapStmt decode (RuntimeModel.machine 12) =
      Runtime.machine (decode 12) := by decide +kernel

theorem row_013 :
    TM2Number.mapStmt decode (RuntimeModel.machine 13) =
      Runtime.machine (decode 13) := by decide +kernel

theorem row_014 :
    TM2Number.mapStmt decode (RuntimeModel.machine 14) =
      Runtime.machine (decode 14) := by decide +kernel

theorem row_015 :
    TM2Number.mapStmt decode (RuntimeModel.machine 15) =
      Runtime.machine (decode 15) := by decide +kernel

theorem row_016 :
    TM2Number.mapStmt decode (RuntimeModel.machine 16) =
      Runtime.machine (decode 16) := by decide +kernel

theorem row_017 :
    TM2Number.mapStmt decode (RuntimeModel.machine 17) =
      Runtime.machine (decode 17) := by decide +kernel

theorem row_018 :
    TM2Number.mapStmt decode (RuntimeModel.machine 18) =
      Runtime.machine (decode 18) := by decide +kernel

theorem row_019 :
    TM2Number.mapStmt decode (RuntimeModel.machine 19) =
      Runtime.machine (decode 19) := by decide +kernel

theorem row_020 :
    TM2Number.mapStmt decode (RuntimeModel.machine 20) =
      Runtime.machine (decode 20) := by decide +kernel

theorem row_021 :
    TM2Number.mapStmt decode (RuntimeModel.machine 21) =
      Runtime.machine (decode 21) := by decide +kernel

theorem row_022 :
    TM2Number.mapStmt decode (RuntimeModel.machine 22) =
      Runtime.machine (decode 22) := by decide +kernel

theorem row_023 :
    TM2Number.mapStmt decode (RuntimeModel.machine 23) =
      Runtime.machine (decode 23) := by decide +kernel

theorem row_024 :
    TM2Number.mapStmt decode (RuntimeModel.machine 24) =
      Runtime.machine (decode 24) := by decide +kernel

theorem row_025 :
    TM2Number.mapStmt decode (RuntimeModel.machine 25) =
      Runtime.machine (decode 25) := by decide +kernel

theorem row_026 :
    TM2Number.mapStmt decode (RuntimeModel.machine 26) =
      Runtime.machine (decode 26) := by decide +kernel

theorem row_027 :
    TM2Number.mapStmt decode (RuntimeModel.machine 27) =
      Runtime.machine (decode 27) := by decide +kernel

theorem row_028 :
    TM2Number.mapStmt decode (RuntimeModel.machine 28) =
      Runtime.machine (decode 28) := by decide +kernel

theorem row_029 :
    TM2Number.mapStmt decode (RuntimeModel.machine 29) =
      Runtime.machine (decode 29) := by decide +kernel

theorem row_030 :
    TM2Number.mapStmt decode (RuntimeModel.machine 30) =
      Runtime.machine (decode 30) := by decide +kernel

theorem row_031 :
    TM2Number.mapStmt decode (RuntimeModel.machine 31) =
      Runtime.machine (decode 31) := by decide +kernel

theorem row_032 :
    TM2Number.mapStmt decode (RuntimeModel.machine 32) =
      Runtime.machine (decode 32) := by decide +kernel

theorem row_033 :
    TM2Number.mapStmt decode (RuntimeModel.machine 33) =
      Runtime.machine (decode 33) := by decide +kernel

theorem row_034 :
    TM2Number.mapStmt decode (RuntimeModel.machine 34) =
      Runtime.machine (decode 34) := by decide +kernel

theorem row_035 :
    TM2Number.mapStmt decode (RuntimeModel.machine 35) =
      Runtime.machine (decode 35) := by decide +kernel

theorem row_036 :
    TM2Number.mapStmt decode (RuntimeModel.machine 36) =
      Runtime.machine (decode 36) := by decide +kernel

theorem row_037 :
    TM2Number.mapStmt decode (RuntimeModel.machine 37) =
      Runtime.machine (decode 37) := by decide +kernel

theorem row_038 :
    TM2Number.mapStmt decode (RuntimeModel.machine 38) =
      Runtime.machine (decode 38) := by decide +kernel

theorem row_039 :
    TM2Number.mapStmt decode (RuntimeModel.machine 39) =
      Runtime.machine (decode 39) := by decide +kernel

theorem row_040 :
    TM2Number.mapStmt decode (RuntimeModel.machine 40) =
      Runtime.machine (decode 40) := by decide +kernel

theorem row_041 :
    TM2Number.mapStmt decode (RuntimeModel.machine 41) =
      Runtime.machine (decode 41) := by decide +kernel

theorem row_042 :
    TM2Number.mapStmt decode (RuntimeModel.machine 42) =
      Runtime.machine (decode 42) := by decide +kernel

theorem row_043 :
    TM2Number.mapStmt decode (RuntimeModel.machine 43) =
      Runtime.machine (decode 43) := by decide +kernel

theorem row_044 :
    TM2Number.mapStmt decode (RuntimeModel.machine 44) =
      Runtime.machine (decode 44) := by decide +kernel

theorem row_045 :
    TM2Number.mapStmt decode (RuntimeModel.machine 45) =
      Runtime.machine (decode 45) := by decide +kernel

theorem row_046 :
    TM2Number.mapStmt decode (RuntimeModel.machine 46) =
      Runtime.machine (decode 46) := by decide +kernel

theorem row_047 :
    TM2Number.mapStmt decode (RuntimeModel.machine 47) =
      Runtime.machine (decode 47) := by decide +kernel

theorem row_048 :
    TM2Number.mapStmt decode (RuntimeModel.machine 48) =
      Runtime.machine (decode 48) := by decide +kernel

theorem row_049 :
    TM2Number.mapStmt decode (RuntimeModel.machine 49) =
      Runtime.machine (decode 49) := by decide +kernel

theorem row_050 :
    TM2Number.mapStmt decode (RuntimeModel.machine 50) =
      Runtime.machine (decode 50) := by decide +kernel

theorem row_051 :
    TM2Number.mapStmt decode (RuntimeModel.machine 51) =
      Runtime.machine (decode 51) := by decide +kernel

theorem row_052 :
    TM2Number.mapStmt decode (RuntimeModel.machine 52) =
      Runtime.machine (decode 52) := by decide +kernel

theorem row_053 :
    TM2Number.mapStmt decode (RuntimeModel.machine 53) =
      Runtime.machine (decode 53) := by decide +kernel

theorem row_054 :
    TM2Number.mapStmt decode (RuntimeModel.machine 54) =
      Runtime.machine (decode 54) := by decide +kernel

theorem row_055 :
    TM2Number.mapStmt decode (RuntimeModel.machine 55) =
      Runtime.machine (decode 55) := by decide +kernel

theorem row_056 :
    TM2Number.mapStmt decode (RuntimeModel.machine 56) =
      Runtime.machine (decode 56) := by decide +kernel

theorem row_057 :
    TM2Number.mapStmt decode (RuntimeModel.machine 57) =
      Runtime.machine (decode 57) := by decide +kernel

theorem row_058 :
    TM2Number.mapStmt decode (RuntimeModel.machine 58) =
      Runtime.machine (decode 58) := by decide +kernel

theorem row_059 :
    TM2Number.mapStmt decode (RuntimeModel.machine 59) =
      Runtime.machine (decode 59) := by decide +kernel

theorem row_060 :
    TM2Number.mapStmt decode (RuntimeModel.machine 60) =
      Runtime.machine (decode 60) := by decide +kernel

theorem row_061 :
    TM2Number.mapStmt decode (RuntimeModel.machine 61) =
      Runtime.machine (decode 61) := by decide +kernel

theorem row_062 :
    TM2Number.mapStmt decode (RuntimeModel.machine 62) =
      Runtime.machine (decode 62) := by decide +kernel

theorem row_063 :
    TM2Number.mapStmt decode (RuntimeModel.machine 63) =
      Runtime.machine (decode 63) := by decide +kernel

theorem row_064 :
    TM2Number.mapStmt decode (RuntimeModel.machine 64) =
      Runtime.machine (decode 64) := by decide +kernel

theorem row_065 :
    TM2Number.mapStmt decode (RuntimeModel.machine 65) =
      Runtime.machine (decode 65) := by decide +kernel

theorem row_066 :
    TM2Number.mapStmt decode (RuntimeModel.machine 66) =
      Runtime.machine (decode 66) := by decide +kernel

theorem row_067 :
    TM2Number.mapStmt decode (RuntimeModel.machine 67) =
      Runtime.machine (decode 67) := by decide +kernel

theorem row_068 :
    TM2Number.mapStmt decode (RuntimeModel.machine 68) =
      Runtime.machine (decode 68) := by decide +kernel

theorem row_069 :
    TM2Number.mapStmt decode (RuntimeModel.machine 69) =
      Runtime.machine (decode 69) := by decide +kernel

theorem row_070 :
    TM2Number.mapStmt decode (RuntimeModel.machine 70) =
      Runtime.machine (decode 70) := by decide +kernel

theorem row_071 :
    TM2Number.mapStmt decode (RuntimeModel.machine 71) =
      Runtime.machine (decode 71) := by decide +kernel

theorem row_072 :
    TM2Number.mapStmt decode (RuntimeModel.machine 72) =
      Runtime.machine (decode 72) := by decide +kernel

theorem row_073 :
    TM2Number.mapStmt decode (RuntimeModel.machine 73) =
      Runtime.machine (decode 73) := by decide +kernel

theorem row_074 :
    TM2Number.mapStmt decode (RuntimeModel.machine 74) =
      Runtime.machine (decode 74) := by decide +kernel

theorem row_075 :
    TM2Number.mapStmt decode (RuntimeModel.machine 75) =
      Runtime.machine (decode 75) := by decide +kernel

theorem row_076 :
    TM2Number.mapStmt decode (RuntimeModel.machine 76) =
      Runtime.machine (decode 76) := by decide +kernel

theorem row_077 :
    TM2Number.mapStmt decode (RuntimeModel.machine 77) =
      Runtime.machine (decode 77) := by decide +kernel

theorem row_078 :
    TM2Number.mapStmt decode (RuntimeModel.machine 78) =
      Runtime.machine (decode 78) := by decide +kernel

theorem row_079 :
    TM2Number.mapStmt decode (RuntimeModel.machine 79) =
      Runtime.machine (decode 79) := by decide +kernel

theorem row_080 :
    TM2Number.mapStmt decode (RuntimeModel.machine 80) =
      Runtime.machine (decode 80) := by decide +kernel

theorem row_081 :
    TM2Number.mapStmt decode (RuntimeModel.machine 81) =
      Runtime.machine (decode 81) := by decide +kernel

theorem row_082 :
    TM2Number.mapStmt decode (RuntimeModel.machine 82) =
      Runtime.machine (decode 82) := by decide +kernel

theorem row_083 :
    TM2Number.mapStmt decode (RuntimeModel.machine 83) =
      Runtime.machine (decode 83) := by decide +kernel

theorem row_084 :
    TM2Number.mapStmt decode (RuntimeModel.machine 84) =
      Runtime.machine (decode 84) := by decide +kernel

theorem row_085 :
    TM2Number.mapStmt decode (RuntimeModel.machine 85) =
      Runtime.machine (decode 85) := by decide +kernel

theorem row_086 :
    TM2Number.mapStmt decode (RuntimeModel.machine 86) =
      Runtime.machine (decode 86) := by decide +kernel

theorem row_087 :
    TM2Number.mapStmt decode (RuntimeModel.machine 87) =
      Runtime.machine (decode 87) := by decide +kernel

theorem row_088 :
    TM2Number.mapStmt decode (RuntimeModel.machine 88) =
      Runtime.machine (decode 88) := by decide +kernel

theorem row_089 :
    TM2Number.mapStmt decode (RuntimeModel.machine 89) =
      Runtime.machine (decode 89) := by decide +kernel

theorem row_090 :
    TM2Number.mapStmt decode (RuntimeModel.machine 90) =
      Runtime.machine (decode 90) := by decide +kernel

theorem row_091 :
    TM2Number.mapStmt decode (RuntimeModel.machine 91) =
      Runtime.machine (decode 91) := by decide +kernel

theorem row_092 :
    TM2Number.mapStmt decode (RuntimeModel.machine 92) =
      Runtime.machine (decode 92) := by decide +kernel

theorem row_093 :
    TM2Number.mapStmt decode (RuntimeModel.machine 93) =
      Runtime.machine (decode 93) := by decide +kernel

theorem row_094 :
    TM2Number.mapStmt decode (RuntimeModel.machine 94) =
      Runtime.machine (decode 94) := by decide +kernel

theorem row_095 :
    TM2Number.mapStmt decode (RuntimeModel.machine 95) =
      Runtime.machine (decode 95) := by decide +kernel

theorem row_096 :
    TM2Number.mapStmt decode (RuntimeModel.machine 96) =
      Runtime.machine (decode 96) := by decide +kernel

theorem row_097 :
    TM2Number.mapStmt decode (RuntimeModel.machine 97) =
      Runtime.machine (decode 97) := by decide +kernel

theorem row_098 :
    TM2Number.mapStmt decode (RuntimeModel.machine 98) =
      Runtime.machine (decode 98) := by decide +kernel

theorem row_099 :
    TM2Number.mapStmt decode (RuntimeModel.machine 99) =
      Runtime.machine (decode 99) := by decide +kernel

theorem row_100 :
    TM2Number.mapStmt decode (RuntimeModel.machine 100) =
      Runtime.machine (decode 100) := by decide +kernel

theorem row_101 :
    TM2Number.mapStmt decode (RuntimeModel.machine 101) =
      Runtime.machine (decode 101) := by decide +kernel

theorem row_102 :
    TM2Number.mapStmt decode (RuntimeModel.machine 102) =
      Runtime.machine (decode 102) := by decide +kernel

theorem row_103 :
    TM2Number.mapStmt decode (RuntimeModel.machine 103) =
      Runtime.machine (decode 103) := by decide +kernel

theorem row_104 :
    TM2Number.mapStmt decode (RuntimeModel.machine 104) =
      Runtime.machine (decode 104) := by decide +kernel

theorem row_105 :
    TM2Number.mapStmt decode (RuntimeModel.machine 105) =
      Runtime.machine (decode 105) := by decide +kernel

theorem row_106 :
    TM2Number.mapStmt decode (RuntimeModel.machine 106) =
      Runtime.machine (decode 106) := by decide +kernel

theorem row_107 :
    TM2Number.mapStmt decode (RuntimeModel.machine 107) =
      Runtime.machine (decode 107) := by decide +kernel

theorem row_108 :
    TM2Number.mapStmt decode (RuntimeModel.machine 108) =
      Runtime.machine (decode 108) := by decide +kernel

theorem row_109 :
    TM2Number.mapStmt decode (RuntimeModel.machine 109) =
      Runtime.machine (decode 109) := by decide +kernel

theorem row_110 :
    TM2Number.mapStmt decode (RuntimeModel.machine 110) =
      Runtime.machine (decode 110) := by decide +kernel

theorem row_111 :
    TM2Number.mapStmt decode (RuntimeModel.machine 111) =
      Runtime.machine (decode 111) := by decide +kernel

theorem row_112 :
    TM2Number.mapStmt decode (RuntimeModel.machine 112) =
      Runtime.machine (decode 112) := by decide +kernel

theorem row_113 :
    TM2Number.mapStmt decode (RuntimeModel.machine 113) =
      Runtime.machine (decode 113) := by decide +kernel

theorem row_114 :
    TM2Number.mapStmt decode (RuntimeModel.machine 114) =
      Runtime.machine (decode 114) := by decide +kernel

theorem row_115 :
    TM2Number.mapStmt decode (RuntimeModel.machine 115) =
      Runtime.machine (decode 115) := by decide +kernel

theorem row_116 :
    TM2Number.mapStmt decode (RuntimeModel.machine 116) =
      Runtime.machine (decode 116) := by decide +kernel

theorem row_117 :
    TM2Number.mapStmt decode (RuntimeModel.machine 117) =
      Runtime.machine (decode 117) := by decide +kernel

theorem row_118 :
    TM2Number.mapStmt decode (RuntimeModel.machine 118) =
      Runtime.machine (decode 118) := by decide +kernel

theorem row_119 :
    TM2Number.mapStmt decode (RuntimeModel.machine 119) =
      Runtime.machine (decode 119) := by decide +kernel

theorem row_120 :
    TM2Number.mapStmt decode (RuntimeModel.machine 120) =
      Runtime.machine (decode 120) := by decide +kernel

theorem row_121 :
    TM2Number.mapStmt decode (RuntimeModel.machine 121) =
      Runtime.machine (decode 121) := by decide +kernel

theorem row_122 :
    TM2Number.mapStmt decode (RuntimeModel.machine 122) =
      Runtime.machine (decode 122) := by decide +kernel

theorem row_123 :
    TM2Number.mapStmt decode (RuntimeModel.machine 123) =
      Runtime.machine (decode 123) := by decide +kernel

theorem row_124 :
    TM2Number.mapStmt decode (RuntimeModel.machine 124) =
      Runtime.machine (decode 124) := by decide +kernel

theorem row_125 :
    TM2Number.mapStmt decode (RuntimeModel.machine 125) =
      Runtime.machine (decode 125) := by decide +kernel

theorem row_126 :
    TM2Number.mapStmt decode (RuntimeModel.machine 126) =
      Runtime.machine (decode 126) := by decide +kernel

theorem row_127 :
    TM2Number.mapStmt decode (RuntimeModel.machine 127) =
      Runtime.machine (decode 127) := by decide +kernel

theorem row_128 :
    TM2Number.mapStmt decode (RuntimeModel.machine 128) =
      Runtime.machine (decode 128) := by decide +kernel

theorem row_129 :
    TM2Number.mapStmt decode (RuntimeModel.machine 129) =
      Runtime.machine (decode 129) := by decide +kernel

theorem row_130 :
    TM2Number.mapStmt decode (RuntimeModel.machine 130) =
      Runtime.machine (decode 130) := by decide +kernel

theorem row_131 :
    TM2Number.mapStmt decode (RuntimeModel.machine 131) =
      Runtime.machine (decode 131) := by decide +kernel

theorem row_132 :
    TM2Number.mapStmt decode (RuntimeModel.machine 132) =
      Runtime.machine (decode 132) := by decide +kernel

theorem row_133 :
    TM2Number.mapStmt decode (RuntimeModel.machine 133) =
      Runtime.machine (decode 133) := by decide +kernel

theorem row_134 :
    TM2Number.mapStmt decode (RuntimeModel.machine 134) =
      Runtime.machine (decode 134) := by decide +kernel

theorem row_135 :
    TM2Number.mapStmt decode (RuntimeModel.machine 135) =
      Runtime.machine (decode 135) := by decide +kernel

theorem row_136 :
    TM2Number.mapStmt decode (RuntimeModel.machine 136) =
      Runtime.machine (decode 136) := by decide +kernel

theorem row_137 :
    TM2Number.mapStmt decode (RuntimeModel.machine 137) =
      Runtime.machine (decode 137) := by decide +kernel

theorem row_138 :
    TM2Number.mapStmt decode (RuntimeModel.machine 138) =
      Runtime.machine (decode 138) := by decide +kernel

theorem row_139 :
    TM2Number.mapStmt decode (RuntimeModel.machine 139) =
      Runtime.machine (decode 139) := by decide +kernel

theorem row_140 :
    TM2Number.mapStmt decode (RuntimeModel.machine 140) =
      Runtime.machine (decode 140) := by decide +kernel

theorem row_141 :
    TM2Number.mapStmt decode (RuntimeModel.machine 141) =
      Runtime.machine (decode 141) := by decide +kernel

theorem row_142 :
    TM2Number.mapStmt decode (RuntimeModel.machine 142) =
      Runtime.machine (decode 142) := by decide +kernel

theorem row_143 :
    TM2Number.mapStmt decode (RuntimeModel.machine 143) =
      Runtime.machine (decode 143) := by decide +kernel

theorem row_144 :
    TM2Number.mapStmt decode (RuntimeModel.machine 144) =
      Runtime.machine (decode 144) := by decide +kernel

theorem row_145 :
    TM2Number.mapStmt decode (RuntimeModel.machine 145) =
      Runtime.machine (decode 145) := by decide +kernel

theorem row_146 :
    TM2Number.mapStmt decode (RuntimeModel.machine 146) =
      Runtime.machine (decode 146) := by decide +kernel

theorem row_147 :
    TM2Number.mapStmt decode (RuntimeModel.machine 147) =
      Runtime.machine (decode 147) := by decide +kernel

theorem row_148 :
    TM2Number.mapStmt decode (RuntimeModel.machine 148) =
      Runtime.machine (decode 148) := by decide +kernel

theorem row_149 :
    TM2Number.mapStmt decode (RuntimeModel.machine 149) =
      Runtime.machine (decode 149) := by decide +kernel

theorem row_150 :
    TM2Number.mapStmt decode (RuntimeModel.machine 150) =
      Runtime.machine (decode 150) := by decide +kernel

theorem row_151 :
    TM2Number.mapStmt decode (RuntimeModel.machine 151) =
      Runtime.machine (decode 151) := by decide +kernel

theorem row_152 :
    TM2Number.mapStmt decode (RuntimeModel.machine 152) =
      Runtime.machine (decode 152) := by decide +kernel

theorem row_153 :
    TM2Number.mapStmt decode (RuntimeModel.machine 153) =
      Runtime.machine (decode 153) := by decide +kernel

theorem row_154 :
    TM2Number.mapStmt decode (RuntimeModel.machine 154) =
      Runtime.machine (decode 154) := by decide +kernel

theorem row_155 :
    TM2Number.mapStmt decode (RuntimeModel.machine 155) =
      Runtime.machine (decode 155) := by decide +kernel

theorem row_156 :
    TM2Number.mapStmt decode (RuntimeModel.machine 156) =
      Runtime.machine (decode 156) := by decide +kernel

theorem row_157 :
    TM2Number.mapStmt decode (RuntimeModel.machine 157) =
      Runtime.machine (decode 157) := by decide +kernel

theorem row_158 :
    TM2Number.mapStmt decode (RuntimeModel.machine 158) =
      Runtime.machine (decode 158) := by decide +kernel

theorem row_159 :
    TM2Number.mapStmt decode (RuntimeModel.machine 159) =
      Runtime.machine (decode 159) := by decide +kernel

theorem row_160 :
    TM2Number.mapStmt decode (RuntimeModel.machine 160) =
      Runtime.machine (decode 160) := by decide +kernel

theorem row_161 :
    TM2Number.mapStmt decode (RuntimeModel.machine 161) =
      Runtime.machine (decode 161) := by decide +kernel

theorem row_162 :
    TM2Number.mapStmt decode (RuntimeModel.machine 162) =
      Runtime.machine (decode 162) := by decide +kernel

theorem row_163 :
    TM2Number.mapStmt decode (RuntimeModel.machine 163) =
      Runtime.machine (decode 163) := by decide +kernel

theorem row_164 :
    TM2Number.mapStmt decode (RuntimeModel.machine 164) =
      Runtime.machine (decode 164) := by decide +kernel

theorem row_165 :
    TM2Number.mapStmt decode (RuntimeModel.machine 165) =
      Runtime.machine (decode 165) := by decide +kernel

theorem row_166 :
    TM2Number.mapStmt decode (RuntimeModel.machine 166) =
      Runtime.machine (decode 166) := by decide +kernel

theorem row_167 :
    TM2Number.mapStmt decode (RuntimeModel.machine 167) =
      Runtime.machine (decode 167) := by decide +kernel

theorem row_168 :
    TM2Number.mapStmt decode (RuntimeModel.machine 168) =
      Runtime.machine (decode 168) := by decide +kernel

theorem row_169 :
    TM2Number.mapStmt decode (RuntimeModel.machine 169) =
      Runtime.machine (decode 169) := by decide +kernel

theorem row_170 :
    TM2Number.mapStmt decode (RuntimeModel.machine 170) =
      Runtime.machine (decode 170) := by decide +kernel

theorem row_171 :
    TM2Number.mapStmt decode (RuntimeModel.machine 171) =
      Runtime.machine (decode 171) := by decide +kernel

theorem row_172 :
    TM2Number.mapStmt decode (RuntimeModel.machine 172) =
      Runtime.machine (decode 172) := by decide +kernel

theorem row_173 :
    TM2Number.mapStmt decode (RuntimeModel.machine 173) =
      Runtime.machine (decode 173) := by decide +kernel

theorem row_174 :
    TM2Number.mapStmt decode (RuntimeModel.machine 174) =
      Runtime.machine (decode 174) := by decide +kernel

theorem row_175 :
    TM2Number.mapStmt decode (RuntimeModel.machine 175) =
      Runtime.machine (decode 175) := by decide +kernel

theorem row_176 :
    TM2Number.mapStmt decode (RuntimeModel.machine 176) =
      Runtime.machine (decode 176) := by decide +kernel

theorem row_177 :
    TM2Number.mapStmt decode (RuntimeModel.machine 177) =
      Runtime.machine (decode 177) := by decide +kernel

theorem row_178 :
    TM2Number.mapStmt decode (RuntimeModel.machine 178) =
      Runtime.machine (decode 178) := by decide +kernel

theorem row_179 :
    TM2Number.mapStmt decode (RuntimeModel.machine 179) =
      Runtime.machine (decode 179) := by decide +kernel

theorem row_180 :
    TM2Number.mapStmt decode (RuntimeModel.machine 180) =
      Runtime.machine (decode 180) := by decide +kernel

theorem row_181 :
    TM2Number.mapStmt decode (RuntimeModel.machine 181) =
      Runtime.machine (decode 181) := by decide +kernel

theorem row_182 :
    TM2Number.mapStmt decode (RuntimeModel.machine 182) =
      Runtime.machine (decode 182) := by decide +kernel

theorem row_183 :
    TM2Number.mapStmt decode (RuntimeModel.machine 183) =
      Runtime.machine (decode 183) := by decide +kernel

theorem row_184 :
    TM2Number.mapStmt decode (RuntimeModel.machine 184) =
      Runtime.machine (decode 184) := by decide +kernel

theorem row_185 :
    TM2Number.mapStmt decode (RuntimeModel.machine 185) =
      Runtime.machine (decode 185) := by decide +kernel

theorem row_186 :
    TM2Number.mapStmt decode (RuntimeModel.machine 186) =
      Runtime.machine (decode 186) := by decide +kernel

theorem row_187 :
    TM2Number.mapStmt decode (RuntimeModel.machine 187) =
      Runtime.machine (decode 187) := by decide +kernel

theorem row_188 :
    TM2Number.mapStmt decode (RuntimeModel.machine 188) =
      Runtime.machine (decode 188) := by decide +kernel

theorem row_189 :
    TM2Number.mapStmt decode (RuntimeModel.machine 189) =
      Runtime.machine (decode 189) := by decide +kernel

theorem row_190 :
    TM2Number.mapStmt decode (RuntimeModel.machine 190) =
      Runtime.machine (decode 190) := by decide +kernel

theorem row_191 :
    TM2Number.mapStmt decode (RuntimeModel.machine 191) =
      Runtime.machine (decode 191) := by decide +kernel

theorem row_192 :
    TM2Number.mapStmt decode (RuntimeModel.machine 192) =
      Runtime.machine (decode 192) := by decide +kernel

theorem row_193 :
    TM2Number.mapStmt decode (RuntimeModel.machine 193) =
      Runtime.machine (decode 193) := by decide +kernel

theorem row_194 :
    TM2Number.mapStmt decode (RuntimeModel.machine 194) =
      Runtime.machine (decode 194) := by decide +kernel

theorem row_195 :
    TM2Number.mapStmt decode (RuntimeModel.machine 195) =
      Runtime.machine (decode 195) := by decide +kernel

theorem row_196 :
    TM2Number.mapStmt decode (RuntimeModel.machine 196) =
      Runtime.machine (decode 196) := by decide +kernel

theorem row_197 :
    TM2Number.mapStmt decode (RuntimeModel.machine 197) =
      Runtime.machine (decode 197) := by decide +kernel

theorem row_198 :
    TM2Number.mapStmt decode (RuntimeModel.machine 198) =
      Runtime.machine (decode 198) := by decide +kernel

theorem row_199 :
    TM2Number.mapStmt decode (RuntimeModel.machine 199) =
      Runtime.machine (decode 199) := by decide +kernel

theorem row_200 :
    TM2Number.mapStmt decode (RuntimeModel.machine 200) =
      Runtime.machine (decode 200) := by decide +kernel

theorem row_201 :
    TM2Number.mapStmt decode (RuntimeModel.machine 201) =
      Runtime.machine (decode 201) := by decide +kernel

theorem row_202 :
    TM2Number.mapStmt decode (RuntimeModel.machine 202) =
      Runtime.machine (decode 202) := by decide +kernel

theorem row_203 :
    TM2Number.mapStmt decode (RuntimeModel.machine 203) =
      Runtime.machine (decode 203) := by decide +kernel

theorem row_204 :
    TM2Number.mapStmt decode (RuntimeModel.machine 204) =
      Runtime.machine (decode 204) := by decide +kernel

theorem row_205 :
    TM2Number.mapStmt decode (RuntimeModel.machine 205) =
      Runtime.machine (decode 205) := by decide +kernel

theorem row_206 :
    TM2Number.mapStmt decode (RuntimeModel.machine 206) =
      Runtime.machine (decode 206) := by decide +kernel

theorem row_207 :
    TM2Number.mapStmt decode (RuntimeModel.machine 207) =
      Runtime.machine (decode 207) := by decide +kernel

theorem row_208 :
    TM2Number.mapStmt decode (RuntimeModel.machine 208) =
      Runtime.machine (decode 208) := by decide +kernel

theorem row_209 :
    TM2Number.mapStmt decode (RuntimeModel.machine 209) =
      Runtime.machine (decode 209) := by decide +kernel

theorem row_210 :
    TM2Number.mapStmt decode (RuntimeModel.machine 210) =
      Runtime.machine (decode 210) := by decide +kernel

theorem row_211 :
    TM2Number.mapStmt decode (RuntimeModel.machine 211) =
      Runtime.machine (decode 211) := by decide +kernel

theorem row_212 :
    TM2Number.mapStmt decode (RuntimeModel.machine 212) =
      Runtime.machine (decode 212) := by decide +kernel

theorem row_213 :
    TM2Number.mapStmt decode (RuntimeModel.machine 213) =
      Runtime.machine (decode 213) := by decide +kernel

theorem row_214 :
    TM2Number.mapStmt decode (RuntimeModel.machine 214) =
      Runtime.machine (decode 214) := by decide +kernel

theorem row_215 :
    TM2Number.mapStmt decode (RuntimeModel.machine 215) =
      Runtime.machine (decode 215) := by decide +kernel

theorem row_216 :
    TM2Number.mapStmt decode (RuntimeModel.machine 216) =
      Runtime.machine (decode 216) := by decide +kernel

theorem row_217 :
    TM2Number.mapStmt decode (RuntimeModel.machine 217) =
      Runtime.machine (decode 217) := by decide +kernel

theorem row_218 :
    TM2Number.mapStmt decode (RuntimeModel.machine 218) =
      Runtime.machine (decode 218) := by decide +kernel

theorem row_219 :
    TM2Number.mapStmt decode (RuntimeModel.machine 219) =
      Runtime.machine (decode 219) := by decide +kernel

theorem row_220 :
    TM2Number.mapStmt decode (RuntimeModel.machine 220) =
      Runtime.machine (decode 220) := by decide +kernel

theorem row_221 :
    TM2Number.mapStmt decode (RuntimeModel.machine 221) =
      Runtime.machine (decode 221) := by decide +kernel

theorem row_222 :
    TM2Number.mapStmt decode (RuntimeModel.machine 222) =
      Runtime.machine (decode 222) := by decide +kernel

theorem row_223 :
    TM2Number.mapStmt decode (RuntimeModel.machine 223) =
      Runtime.machine (decode 223) := by decide +kernel

theorem row_224 :
    TM2Number.mapStmt decode (RuntimeModel.machine 224) =
      Runtime.machine (decode 224) := by decide +kernel

theorem row_225 :
    TM2Number.mapStmt decode (RuntimeModel.machine 225) =
      Runtime.machine (decode 225) := by decide +kernel

theorem row_226 :
    TM2Number.mapStmt decode (RuntimeModel.machine 226) =
      Runtime.machine (decode 226) := by decide +kernel

theorem row_227 :
    TM2Number.mapStmt decode (RuntimeModel.machine 227) =
      Runtime.machine (decode 227) := by decide +kernel

theorem row_228 :
    TM2Number.mapStmt decode (RuntimeModel.machine 228) =
      Runtime.machine (decode 228) := by decide +kernel

theorem row_229 :
    TM2Number.mapStmt decode (RuntimeModel.machine 229) =
      Runtime.machine (decode 229) := by decide +kernel

theorem row_230 :
    TM2Number.mapStmt decode (RuntimeModel.machine 230) =
      Runtime.machine (decode 230) := by decide +kernel

theorem row_231 :
    TM2Number.mapStmt decode (RuntimeModel.machine 231) =
      Runtime.machine (decode 231) := by decide +kernel

theorem row_232 :
    TM2Number.mapStmt decode (RuntimeModel.machine 232) =
      Runtime.machine (decode 232) := by decide +kernel

theorem row_233 :
    TM2Number.mapStmt decode (RuntimeModel.machine 233) =
      Runtime.machine (decode 233) := by decide +kernel

theorem row_234 :
    TM2Number.mapStmt decode (RuntimeModel.machine 234) =
      Runtime.machine (decode 234) := by decide +kernel

theorem row_235 :
    TM2Number.mapStmt decode (RuntimeModel.machine 235) =
      Runtime.machine (decode 235) := by decide +kernel

theorem row_236 :
    TM2Number.mapStmt decode (RuntimeModel.machine 236) =
      Runtime.machine (decode 236) := by decide +kernel

theorem row_237 :
    TM2Number.mapStmt decode (RuntimeModel.machine 237) =
      Runtime.machine (decode 237) := by decide +kernel

theorem row_238 :
    TM2Number.mapStmt decode (RuntimeModel.machine 238) =
      Runtime.machine (decode 238) := by decide +kernel

theorem row_239 :
    TM2Number.mapStmt decode (RuntimeModel.machine 239) =
      Runtime.machine (decode 239) := by decide +kernel

theorem row_240 :
    TM2Number.mapStmt decode (RuntimeModel.machine 240) =
      Runtime.machine (decode 240) := by decide +kernel

theorem row_241 :
    TM2Number.mapStmt decode (RuntimeModel.machine 241) =
      Runtime.machine (decode 241) := by decide +kernel

theorem row_242 :
    TM2Number.mapStmt decode (RuntimeModel.machine 242) =
      Runtime.machine (decode 242) := by decide +kernel

theorem row_243 :
    TM2Number.mapStmt decode (RuntimeModel.machine 243) =
      Runtime.machine (decode 243) := by decide +kernel

theorem row_244 :
    TM2Number.mapStmt decode (RuntimeModel.machine 244) =
      Runtime.machine (decode 244) := by decide +kernel

theorem row_245 :
    TM2Number.mapStmt decode (RuntimeModel.machine 245) =
      Runtime.machine (decode 245) := by decide +kernel

theorem row_246 :
    TM2Number.mapStmt decode (RuntimeModel.machine 246) =
      Runtime.machine (decode 246) := by decide +kernel

theorem row_247 :
    TM2Number.mapStmt decode (RuntimeModel.machine 247) =
      Runtime.machine (decode 247) := by decide +kernel

theorem row_248 :
    TM2Number.mapStmt decode (RuntimeModel.machine 248) =
      Runtime.machine (decode 248) := by decide +kernel

theorem row_249 :
    TM2Number.mapStmt decode (RuntimeModel.machine 249) =
      Runtime.machine (decode 249) := by decide +kernel

theorem row_250 :
    TM2Number.mapStmt decode (RuntimeModel.machine 250) =
      Runtime.machine (decode 250) := by decide +kernel

theorem row_251 :
    TM2Number.mapStmt decode (RuntimeModel.machine 251) =
      Runtime.machine (decode 251) := by decide +kernel

theorem row_252 :
    TM2Number.mapStmt decode (RuntimeModel.machine 252) =
      Runtime.machine (decode 252) := by decide +kernel

theorem row_253 :
    TM2Number.mapStmt decode (RuntimeModel.machine 253) =
      Runtime.machine (decode 253) := by decide +kernel

theorem row_254 :
    TM2Number.mapStmt decode (RuntimeModel.machine 254) =
      Runtime.machine (decode 254) := by decide +kernel

theorem row_255 :
    TM2Number.mapStmt decode (RuntimeModel.machine 255) =
      Runtime.machine (decode 255) := by decide +kernel

theorem row_256 :
    TM2Number.mapStmt decode (RuntimeModel.machine 256) =
      Runtime.machine (decode 256) := by decide +kernel

theorem row_257 :
    TM2Number.mapStmt decode (RuntimeModel.machine 257) =
      Runtime.machine (decode 257) := by decide +kernel

theorem row_258 :
    TM2Number.mapStmt decode (RuntimeModel.machine 258) =
      Runtime.machine (decode 258) := by decide +kernel

theorem row_259 :
    TM2Number.mapStmt decode (RuntimeModel.machine 259) =
      Runtime.machine (decode 259) := by decide +kernel

theorem row_260 :
    TM2Number.mapStmt decode (RuntimeModel.machine 260) =
      Runtime.machine (decode 260) := by decide +kernel

theorem row_261 :
    TM2Number.mapStmt decode (RuntimeModel.machine 261) =
      Runtime.machine (decode 261) := by decide +kernel

theorem row_262 :
    TM2Number.mapStmt decode (RuntimeModel.machine 262) =
      Runtime.machine (decode 262) := by decide +kernel

theorem row_263 :
    TM2Number.mapStmt decode (RuntimeModel.machine 263) =
      Runtime.machine (decode 263) := by decide +kernel

theorem row_264 :
    TM2Number.mapStmt decode (RuntimeModel.machine 264) =
      Runtime.machine (decode 264) := by decide +kernel

theorem row_265 :
    TM2Number.mapStmt decode (RuntimeModel.machine 265) =
      Runtime.machine (decode 265) := by decide +kernel

theorem row_266 :
    TM2Number.mapStmt decode (RuntimeModel.machine 266) =
      Runtime.machine (decode 266) := by decide +kernel

theorem row_267 :
    TM2Number.mapStmt decode (RuntimeModel.machine 267) =
      Runtime.machine (decode 267) := by decide +kernel

theorem row_268 :
    TM2Number.mapStmt decode (RuntimeModel.machine 268) =
      Runtime.machine (decode 268) := by decide +kernel

theorem row_269 :
    TM2Number.mapStmt decode (RuntimeModel.machine 269) =
      Runtime.machine (decode 269) := by decide +kernel

theorem row_270 :
    TM2Number.mapStmt decode (RuntimeModel.machine 270) =
      Runtime.machine (decode 270) := by decide +kernel

theorem row_271 :
    TM2Number.mapStmt decode (RuntimeModel.machine 271) =
      Runtime.machine (decode 271) := by decide +kernel

theorem row_272 :
    TM2Number.mapStmt decode (RuntimeModel.machine 272) =
      Runtime.machine (decode 272) := by decide +kernel

theorem row_273 :
    TM2Number.mapStmt decode (RuntimeModel.machine 273) =
      Runtime.machine (decode 273) := by decide +kernel

theorem row_274 :
    TM2Number.mapStmt decode (RuntimeModel.machine 274) =
      Runtime.machine (decode 274) := by decide +kernel

theorem row_275 :
    TM2Number.mapStmt decode (RuntimeModel.machine 275) =
      Runtime.machine (decode 275) := by decide +kernel

theorem row_276 :
    TM2Number.mapStmt decode (RuntimeModel.machine 276) =
      Runtime.machine (decode 276) := by decide +kernel

theorem row_277 :
    TM2Number.mapStmt decode (RuntimeModel.machine 277) =
      Runtime.machine (decode 277) := by decide +kernel

theorem row_278 :
    TM2Number.mapStmt decode (RuntimeModel.machine 278) =
      Runtime.machine (decode 278) := by decide +kernel

theorem row_279 :
    TM2Number.mapStmt decode (RuntimeModel.machine 279) =
      Runtime.machine (decode 279) := by decide +kernel

theorem row_280 :
    TM2Number.mapStmt decode (RuntimeModel.machine 280) =
      Runtime.machine (decode 280) := by decide +kernel

theorem row_281 :
    TM2Number.mapStmt decode (RuntimeModel.machine 281) =
      Runtime.machine (decode 281) := by decide +kernel

theorem row_282 :
    TM2Number.mapStmt decode (RuntimeModel.machine 282) =
      Runtime.machine (decode 282) := by decide +kernel

theorem row_283 :
    TM2Number.mapStmt decode (RuntimeModel.machine 283) =
      Runtime.machine (decode 283) := by decide +kernel

theorem row_284 :
    TM2Number.mapStmt decode (RuntimeModel.machine 284) =
      Runtime.machine (decode 284) := by decide +kernel

theorem row_285 :
    TM2Number.mapStmt decode (RuntimeModel.machine 285) =
      Runtime.machine (decode 285) := by decide +kernel

theorem row_286 :
    TM2Number.mapStmt decode (RuntimeModel.machine 286) =
      Runtime.machine (decode 286) := by decide +kernel

theorem row_287 :
    TM2Number.mapStmt decode (RuntimeModel.machine 287) =
      Runtime.machine (decode 287) := by decide +kernel

theorem row_288 :
    TM2Number.mapStmt decode (RuntimeModel.machine 288) =
      Runtime.machine (decode 288) := by decide +kernel

theorem row_289 :
    TM2Number.mapStmt decode (RuntimeModel.machine 289) =
      Runtime.machine (decode 289) := by decide +kernel

theorem row_290 :
    TM2Number.mapStmt decode (RuntimeModel.machine 290) =
      Runtime.machine (decode 290) := by decide +kernel

theorem row_291 :
    TM2Number.mapStmt decode (RuntimeModel.machine 291) =
      Runtime.machine (decode 291) := by decide +kernel

theorem row_292 :
    TM2Number.mapStmt decode (RuntimeModel.machine 292) =
      Runtime.machine (decode 292) := by decide +kernel

theorem row_293 :
    TM2Number.mapStmt decode (RuntimeModel.machine 293) =
      Runtime.machine (decode 293) := by decide +kernel

theorem row_294 :
    TM2Number.mapStmt decode (RuntimeModel.machine 294) =
      Runtime.machine (decode 294) := by decide +kernel

theorem row_295 :
    TM2Number.mapStmt decode (RuntimeModel.machine 295) =
      Runtime.machine (decode 295) := by decide +kernel

theorem row_296 :
    TM2Number.mapStmt decode (RuntimeModel.machine 296) =
      Runtime.machine (decode 296) := by decide +kernel

theorem row_297 :
    TM2Number.mapStmt decode (RuntimeModel.machine 297) =
      Runtime.machine (decode 297) := by decide +kernel

theorem row_298 :
    TM2Number.mapStmt decode (RuntimeModel.machine 298) =
      Runtime.machine (decode 298) := by decide +kernel

theorem row_299 :
    TM2Number.mapStmt decode (RuntimeModel.machine 299) =
      Runtime.machine (decode 299) := by decide +kernel

theorem row_300 :
    TM2Number.mapStmt decode (RuntimeModel.machine 300) =
      Runtime.machine (decode 300) := by decide +kernel

theorem row_301 :
    TM2Number.mapStmt decode (RuntimeModel.machine 301) =
      Runtime.machine (decode 301) := by decide +kernel

theorem row_302 :
    TM2Number.mapStmt decode (RuntimeModel.machine 302) =
      Runtime.machine (decode 302) := by decide +kernel

theorem row_303 :
    TM2Number.mapStmt decode (RuntimeModel.machine 303) =
      Runtime.machine (decode 303) := by decide +kernel

theorem row_304 :
    TM2Number.mapStmt decode (RuntimeModel.machine 304) =
      Runtime.machine (decode 304) := by decide +kernel

theorem row_305 :
    TM2Number.mapStmt decode (RuntimeModel.machine 305) =
      Runtime.machine (decode 305) := by decide +kernel

theorem row_306 :
    TM2Number.mapStmt decode (RuntimeModel.machine 306) =
      Runtime.machine (decode 306) := by decide +kernel

theorem row_307 :
    TM2Number.mapStmt decode (RuntimeModel.machine 307) =
      Runtime.machine (decode 307) := by decide +kernel

theorem row_308 :
    TM2Number.mapStmt decode (RuntimeModel.machine 308) =
      Runtime.machine (decode 308) := by decide +kernel

theorem row_309 :
    TM2Number.mapStmt decode (RuntimeModel.machine 309) =
      Runtime.machine (decode 309) := by decide +kernel

theorem row_310 :
    TM2Number.mapStmt decode (RuntimeModel.machine 310) =
      Runtime.machine (decode 310) := by decide +kernel

theorem row_311 :
    TM2Number.mapStmt decode (RuntimeModel.machine 311) =
      Runtime.machine (decode 311) := by decide +kernel

theorem row_312 :
    TM2Number.mapStmt decode (RuntimeModel.machine 312) =
      Runtime.machine (decode 312) := by decide +kernel

theorem row_313 :
    TM2Number.mapStmt decode (RuntimeModel.machine 313) =
      Runtime.machine (decode 313) := by decide +kernel

theorem row_314 :
    TM2Number.mapStmt decode (RuntimeModel.machine 314) =
      Runtime.machine (decode 314) := by decide +kernel

theorem row_315 :
    TM2Number.mapStmt decode (RuntimeModel.machine 315) =
      Runtime.machine (decode 315) := by decide +kernel

theorem row_316 :
    TM2Number.mapStmt decode (RuntimeModel.machine 316) =
      Runtime.machine (decode 316) := by decide +kernel

theorem row_317 :
    TM2Number.mapStmt decode (RuntimeModel.machine 317) =
      Runtime.machine (decode 317) := by decide +kernel

theorem row_318 :
    TM2Number.mapStmt decode (RuntimeModel.machine 318) =
      Runtime.machine (decode 318) := by decide +kernel

theorem row_319 :
    TM2Number.mapStmt decode (RuntimeModel.machine 319) =
      Runtime.machine (decode 319) := by decide +kernel

theorem row_320 :
    TM2Number.mapStmt decode (RuntimeModel.machine 320) =
      Runtime.machine (decode 320) := by decide +kernel

theorem row_321 :
    TM2Number.mapStmt decode (RuntimeModel.machine 321) =
      Runtime.machine (decode 321) := by decide +kernel

theorem row_322 :
    TM2Number.mapStmt decode (RuntimeModel.machine 322) =
      Runtime.machine (decode 322) := by decide +kernel

theorem row_323 :
    TM2Number.mapStmt decode (RuntimeModel.machine 323) =
      Runtime.machine (decode 323) := by decide +kernel

theorem row_324 :
    TM2Number.mapStmt decode (RuntimeModel.machine 324) =
      Runtime.machine (decode 324) := by decide +kernel

theorem row_325 :
    TM2Number.mapStmt decode (RuntimeModel.machine 325) =
      Runtime.machine (decode 325) := by decide +kernel

theorem row_326 :
    TM2Number.mapStmt decode (RuntimeModel.machine 326) =
      Runtime.machine (decode 326) := by decide +kernel

theorem row_327 :
    TM2Number.mapStmt decode (RuntimeModel.machine 327) =
      Runtime.machine (decode 327) := by decide +kernel

theorem row_328 :
    TM2Number.mapStmt decode (RuntimeModel.machine 328) =
      Runtime.machine (decode 328) := by decide +kernel

theorem row_329 :
    TM2Number.mapStmt decode (RuntimeModel.machine 329) =
      Runtime.machine (decode 329) := by decide +kernel

theorem row_330 :
    TM2Number.mapStmt decode (RuntimeModel.machine 330) =
      Runtime.machine (decode 330) := by decide +kernel

theorem row_331 :
    TM2Number.mapStmt decode (RuntimeModel.machine 331) =
      Runtime.machine (decode 331) := by decide +kernel

theorem row_332 :
    TM2Number.mapStmt decode (RuntimeModel.machine 332) =
      Runtime.machine (decode 332) := by decide +kernel

theorem row_333 :
    TM2Number.mapStmt decode (RuntimeModel.machine 333) =
      Runtime.machine (decode 333) := by decide +kernel

theorem row_334 :
    TM2Number.mapStmt decode (RuntimeModel.machine 334) =
      Runtime.machine (decode 334) := by decide +kernel

theorem row_335 :
    TM2Number.mapStmt decode (RuntimeModel.machine 335) =
      Runtime.machine (decode 335) := by decide +kernel

theorem row_336 :
    TM2Number.mapStmt decode (RuntimeModel.machine 336) =
      Runtime.machine (decode 336) := by decide +kernel

theorem row_337 :
    TM2Number.mapStmt decode (RuntimeModel.machine 337) =
      Runtime.machine (decode 337) := by decide +kernel

theorem row_338 :
    TM2Number.mapStmt decode (RuntimeModel.machine 338) =
      Runtime.machine (decode 338) := by decide +kernel

theorem row_339 :
    TM2Number.mapStmt decode (RuntimeModel.machine 339) =
      Runtime.machine (decode 339) := by decide +kernel

theorem row_340 :
    TM2Number.mapStmt decode (RuntimeModel.machine 340) =
      Runtime.machine (decode 340) := by decide +kernel

theorem row_341 :
    TM2Number.mapStmt decode (RuntimeModel.machine 341) =
      Runtime.machine (decode 341) := by decide +kernel

theorem row_342 :
    TM2Number.mapStmt decode (RuntimeModel.machine 342) =
      Runtime.machine (decode 342) := by decide +kernel

theorem row_343 :
    TM2Number.mapStmt decode (RuntimeModel.machine 343) =
      Runtime.machine (decode 343) := by decide +kernel

theorem row_344 :
    TM2Number.mapStmt decode (RuntimeModel.machine 344) =
      Runtime.machine (decode 344) := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Aggregate 345 already checked rows without reducing source first-occurrence numbering.
/-- All 345 literal rows preserve every constructor and finite function field exactly. -/
theorem rows (state : RuntimeModel.Label) :
    TM2Number.mapStmt decode (RuntimeModel.machine state) = Runtime.machine (decode state) := by
  fin_cases state
  · exact row_000
  · exact row_001
  · exact row_002
  · exact row_003
  · exact row_004
  · exact row_005
  · exact row_006
  · exact row_007
  · exact row_008
  · exact row_009
  · exact row_010
  · exact row_011
  · exact row_012
  · exact row_013
  · exact row_014
  · exact row_015
  · exact row_016
  · exact row_017
  · exact row_018
  · exact row_019
  · exact row_020
  · exact row_021
  · exact row_022
  · exact row_023
  · exact row_024
  · exact row_025
  · exact row_026
  · exact row_027
  · exact row_028
  · exact row_029
  · exact row_030
  · exact row_031
  · exact row_032
  · exact row_033
  · exact row_034
  · exact row_035
  · exact row_036
  · exact row_037
  · exact row_038
  · exact row_039
  · exact row_040
  · exact row_041
  · exact row_042
  · exact row_043
  · exact row_044
  · exact row_045
  · exact row_046
  · exact row_047
  · exact row_048
  · exact row_049
  · exact row_050
  · exact row_051
  · exact row_052
  · exact row_053
  · exact row_054
  · exact row_055
  · exact row_056
  · exact row_057
  · exact row_058
  · exact row_059
  · exact row_060
  · exact row_061
  · exact row_062
  · exact row_063
  · exact row_064
  · exact row_065
  · exact row_066
  · exact row_067
  · exact row_068
  · exact row_069
  · exact row_070
  · exact row_071
  · exact row_072
  · exact row_073
  · exact row_074
  · exact row_075
  · exact row_076
  · exact row_077
  · exact row_078
  · exact row_079
  · exact row_080
  · exact row_081
  · exact row_082
  · exact row_083
  · exact row_084
  · exact row_085
  · exact row_086
  · exact row_087
  · exact row_088
  · exact row_089
  · exact row_090
  · exact row_091
  · exact row_092
  · exact row_093
  · exact row_094
  · exact row_095
  · exact row_096
  · exact row_097
  · exact row_098
  · exact row_099
  · exact row_100
  · exact row_101
  · exact row_102
  · exact row_103
  · exact row_104
  · exact row_105
  · exact row_106
  · exact row_107
  · exact row_108
  · exact row_109
  · exact row_110
  · exact row_111
  · exact row_112
  · exact row_113
  · exact row_114
  · exact row_115
  · exact row_116
  · exact row_117
  · exact row_118
  · exact row_119
  · exact row_120
  · exact row_121
  · exact row_122
  · exact row_123
  · exact row_124
  · exact row_125
  · exact row_126
  · exact row_127
  · exact row_128
  · exact row_129
  · exact row_130
  · exact row_131
  · exact row_132
  · exact row_133
  · exact row_134
  · exact row_135
  · exact row_136
  · exact row_137
  · exact row_138
  · exact row_139
  · exact row_140
  · exact row_141
  · exact row_142
  · exact row_143
  · exact row_144
  · exact row_145
  · exact row_146
  · exact row_147
  · exact row_148
  · exact row_149
  · exact row_150
  · exact row_151
  · exact row_152
  · exact row_153
  · exact row_154
  · exact row_155
  · exact row_156
  · exact row_157
  · exact row_158
  · exact row_159
  · exact row_160
  · exact row_161
  · exact row_162
  · exact row_163
  · exact row_164
  · exact row_165
  · exact row_166
  · exact row_167
  · exact row_168
  · exact row_169
  · exact row_170
  · exact row_171
  · exact row_172
  · exact row_173
  · exact row_174
  · exact row_175
  · exact row_176
  · exact row_177
  · exact row_178
  · exact row_179
  · exact row_180
  · exact row_181
  · exact row_182
  · exact row_183
  · exact row_184
  · exact row_185
  · exact row_186
  · exact row_187
  · exact row_188
  · exact row_189
  · exact row_190
  · exact row_191
  · exact row_192
  · exact row_193
  · exact row_194
  · exact row_195
  · exact row_196
  · exact row_197
  · exact row_198
  · exact row_199
  · exact row_200
  · exact row_201
  · exact row_202
  · exact row_203
  · exact row_204
  · exact row_205
  · exact row_206
  · exact row_207
  · exact row_208
  · exact row_209
  · exact row_210
  · exact row_211
  · exact row_212
  · exact row_213
  · exact row_214
  · exact row_215
  · exact row_216
  · exact row_217
  · exact row_218
  · exact row_219
  · exact row_220
  · exact row_221
  · exact row_222
  · exact row_223
  · exact row_224
  · exact row_225
  · exact row_226
  · exact row_227
  · exact row_228
  · exact row_229
  · exact row_230
  · exact row_231
  · exact row_232
  · exact row_233
  · exact row_234
  · exact row_235
  · exact row_236
  · exact row_237
  · exact row_238
  · exact row_239
  · exact row_240
  · exact row_241
  · exact row_242
  · exact row_243
  · exact row_244
  · exact row_245
  · exact row_246
  · exact row_247
  · exact row_248
  · exact row_249
  · exact row_250
  · exact row_251
  · exact row_252
  · exact row_253
  · exact row_254
  · exact row_255
  · exact row_256
  · exact row_257
  · exact row_258
  · exact row_259
  · exact row_260
  · exact row_261
  · exact row_262
  · exact row_263
  · exact row_264
  · exact row_265
  · exact row_266
  · exact row_267
  · exact row_268
  · exact row_269
  · exact row_270
  · exact row_271
  · exact row_272
  · exact row_273
  · exact row_274
  · exact row_275
  · exact row_276
  · exact row_277
  · exact row_278
  · exact row_279
  · exact row_280
  · exact row_281
  · exact row_282
  · exact row_283
  · exact row_284
  · exact row_285
  · exact row_286
  · exact row_287
  · exact row_288
  · exact row_289
  · exact row_290
  · exact row_291
  · exact row_292
  · exact row_293
  · exact row_294
  · exact row_295
  · exact row_296
  · exact row_297
  · exact row_298
  · exact row_299
  · exact row_300
  · exact row_301
  · exact row_302
  · exact row_303
  · exact row_304
  · exact row_305
  · exact row_306
  · exact row_307
  · exact row_308
  · exact row_309
  · exact row_310
  · exact row_311
  · exact row_312
  · exact row_313
  · exact row_314
  · exact row_315
  · exact row_316
  · exact row_317
  · exact row_318
  · exact row_319
  · exact row_320
  · exact row_321
  · exact row_322
  · exact row_323
  · exact row_324
  · exact row_325
  · exact row_326
  · exact row_327
  · exact row_328
  · exact row_329
  · exact row_330
  · exact row_331
  · exact row_332
  · exact row_333
  · exact row_334
  · exact row_335
  · exact row_336
  · exact row_337
  · exact row_338
  · exact row_339
  · exact row_340
  · exact row_341
  · exact row_342
  · exact row_343
  · exact row_344

/-- Decode only optional control, retaining the exact finite store and all four stacks. -/
def decodeCfg (config : TM2.Cfg RuntimeModel.Alphabet RuntimeModel.Label RuntimeModel.Store) :
    Cfg' := TM2Number.mapCfg decode config

/-- Exact one-step decoding includes the absence of a successor after halt. -/
theorem step_decode
    (config : TM2.Cfg RuntimeModel.Alphabet RuntimeModel.Label RuntimeModel.Store) :
    (TM2.step RuntimeModel.machine config).map decodeCfg =
      TM2.step Runtime.machine (decodeCfg config) := by
  rcases config with ⟨pc, store, tapes⟩
  cases pc with
  | none => rfl
  | some pc =>
    simp only [TM2.step, decodeCfg, TM2Number.mapCfg, Option.map_some]
    rw [← rows pc, TM2Number.stepAux_map]
    rfl

theorem respects : Respects (TM2.step RuntimeModel.machine) (TM2.step Runtime.machine)
    (fun first second ↦ decodeCfg first = second) := by
  apply fun_respects.mpr
  intro config
  have equal := step_decode config
  cases stepped : TM2.step RuntimeModel.machine config with
  | none => simpa only [stepped, Option.map_none, FRespects] using equal.symm
  | some next =>
    exact TransGen.single
      (by simpa only [stepped, Option.map_some, Option.mem_def] using equal.symm)

/-- Both termination directions at every literal numeric configuration. -/
theorem dom_cfg
    (config : TM2.Cfg RuntimeModel.Alphabet RuntimeModel.Label RuntimeModel.Store) :
    (StateTransition.eval (TM2.step RuntimeModel.machine) config).Dom ↔
      (StateTransition.eval (TM2.step Runtime.machine) (decodeCfg config)).Dom :=
  (tr_eval_dom respects rfl).symm

/-- Ordinary initialization decodes state zero without changing store or input stacks. -/
theorem decode_init (inputStack : K') (input : List Γ') :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    decodeCfg (TM2.init inputStack input) = (TM2.init inputStack input : Cfg') := by
  change TM2.Cfg.mk (some (decode 0)) _ _ = TM2.Cfg.mk (some (Runtime.label .start)) _ _
  rw [decode_zero]
  rfl

/-- The complete literal machine and unchanged Runtime halt on exactly the same finite inputs. -/
theorem eval_dom (inputStack : K') (input : List Γ') :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    (TM2.eval RuntimeModel.machine inputStack input).Dom ↔
      (TM2.eval Runtime.machine inputStack input).Dom :=
  (tr_eval_dom respects (decode_init inputStack input)).symm

/-- All literal numeric controls are supported; no source support oracle is required. -/
theorem supports : TM2.Supports RuntimeModel.machine Finset.univ := by
  refine ⟨Finset.mem_univ _, fun state _ ↦ ?_⟩
  generalize RuntimeModel.machine state = stmt
  induction stmt <;> simp_all [TM2.SupportsStmt]

end ConjectureMachines.Compilation.RuntimeCertificate
