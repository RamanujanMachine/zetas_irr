import cas_spec

namespace Pfq54.CF

theorem cas_3_0 : checkCas 192 8 = true := by decide +kernel

theorem cas_3_1 : checkCas 200 8 = true := by decide +kernel

theorem cas_3_2 : checkCas 208 8 = true := by decide +kernel

theorem cas_3_3 : checkCas 216 8 = true := by decide +kernel

theorem cas_3_4 : checkCas 224 8 = true := by decide +kernel

theorem cas_3_5 : checkCas 232 8 = true := by decide +kernel

theorem cas_3_6 : checkCas 240 8 = true := by decide +kernel

theorem cas_3_7 : checkCas 248 8 = true := by decide +kernel

theorem cas_range_3 (k : Nat) (ha : 192 ≤ k) (hb : k < 256) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 200 with g0 | g0
  · exact checkCas_spec _ _ cas_3_0 k ha g0
  rcases Nat.lt_or_ge k 208 with g1 | g1
  · exact checkCas_spec _ _ cas_3_1 k g0 g1
  rcases Nat.lt_or_ge k 216 with g2 | g2
  · exact checkCas_spec _ _ cas_3_2 k g1 g2
  rcases Nat.lt_or_ge k 224 with g3 | g3
  · exact checkCas_spec _ _ cas_3_3 k g2 g3
  rcases Nat.lt_or_ge k 232 with g4 | g4
  · exact checkCas_spec _ _ cas_3_4 k g3 g4
  rcases Nat.lt_or_ge k 240 with g5 | g5
  · exact checkCas_spec _ _ cas_3_5 k g4 g5
  rcases Nat.lt_or_ge k 248 with g6 | g6
  · exact checkCas_spec _ _ cas_3_6 k g5 g6
  exact checkCas_spec _ _ cas_3_7 k g6 hb

end Pfq54.CF
