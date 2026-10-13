import cas_spec

namespace Pfq54.CF

theorem cas_1_0 : checkCas 64 8 = true := by decide +kernel

theorem cas_1_1 : checkCas 72 8 = true := by decide +kernel

theorem cas_1_2 : checkCas 80 8 = true := by decide +kernel

theorem cas_1_3 : checkCas 88 8 = true := by decide +kernel

theorem cas_1_4 : checkCas 96 8 = true := by decide +kernel

theorem cas_1_5 : checkCas 104 8 = true := by decide +kernel

theorem cas_1_6 : checkCas 112 8 = true := by decide +kernel

theorem cas_1_7 : checkCas 120 8 = true := by decide +kernel

theorem cas_range_1 (k : Nat) (ha : 64 ≤ k) (hb : k < 128) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 72 with g0 | g0
  · exact checkCas_spec _ _ cas_1_0 k ha g0
  rcases Nat.lt_or_ge k 80 with g1 | g1
  · exact checkCas_spec _ _ cas_1_1 k g0 g1
  rcases Nat.lt_or_ge k 88 with g2 | g2
  · exact checkCas_spec _ _ cas_1_2 k g1 g2
  rcases Nat.lt_or_ge k 96 with g3 | g3
  · exact checkCas_spec _ _ cas_1_3 k g2 g3
  rcases Nat.lt_or_ge k 104 with g4 | g4
  · exact checkCas_spec _ _ cas_1_4 k g3 g4
  rcases Nat.lt_or_ge k 112 with g5 | g5
  · exact checkCas_spec _ _ cas_1_5 k g4 g5
  rcases Nat.lt_or_ge k 120 with g6 | g6
  · exact checkCas_spec _ _ cas_1_6 k g5 g6
  exact checkCas_spec _ _ cas_1_7 k g6 hb

end Pfq54.CF
