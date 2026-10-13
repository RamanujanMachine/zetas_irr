import cas_spec

namespace Pfq54.CF

theorem cas_4_0 : checkCas 256 8 = true := by decide +kernel

theorem cas_4_1 : checkCas 264 8 = true := by decide +kernel

theorem cas_4_2 : checkCas 272 8 = true := by decide +kernel

theorem cas_4_3 : checkCas 280 8 = true := by decide +kernel

theorem cas_4_4 : checkCas 288 8 = true := by decide +kernel

theorem cas_4_5 : checkCas 296 8 = true := by decide +kernel

theorem cas_4_6 : checkCas 304 8 = true := by decide +kernel

theorem cas_4_7 : checkCas 312 8 = true := by decide +kernel

theorem cas_range_4 (k : Nat) (ha : 256 ≤ k) (hb : k < 320) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 264 with g0 | g0
  · exact checkCas_spec _ _ cas_4_0 k ha g0
  rcases Nat.lt_or_ge k 272 with g1 | g1
  · exact checkCas_spec _ _ cas_4_1 k g0 g1
  rcases Nat.lt_or_ge k 280 with g2 | g2
  · exact checkCas_spec _ _ cas_4_2 k g1 g2
  rcases Nat.lt_or_ge k 288 with g3 | g3
  · exact checkCas_spec _ _ cas_4_3 k g2 g3
  rcases Nat.lt_or_ge k 296 with g4 | g4
  · exact checkCas_spec _ _ cas_4_4 k g3 g4
  rcases Nat.lt_or_ge k 304 with g5 | g5
  · exact checkCas_spec _ _ cas_4_5 k g4 g5
  rcases Nat.lt_or_ge k 312 with g6 | g6
  · exact checkCas_spec _ _ cas_4_6 k g5 g6
  exact checkCas_spec _ _ cas_4_7 k g6 hb

end Pfq54.CF
