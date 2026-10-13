import cas_spec

namespace Pfq54.CF

theorem cas_0_0 : checkCas 0 8 = true := by decide +kernel

theorem cas_0_1 : checkCas 8 8 = true := by decide +kernel

theorem cas_0_2 : checkCas 16 8 = true := by decide +kernel

theorem cas_0_3 : checkCas 24 8 = true := by decide +kernel

theorem cas_0_4 : checkCas 32 8 = true := by decide +kernel

theorem cas_0_5 : checkCas 40 8 = true := by decide +kernel

theorem cas_0_6 : checkCas 48 8 = true := by decide +kernel

theorem cas_0_7 : checkCas 56 8 = true := by decide +kernel

theorem cas_range_0 (k : Nat) (ha : 0 ≤ k) (hb : k < 64) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 8 with g0 | g0
  · exact checkCas_spec _ _ cas_0_0 k ha g0
  rcases Nat.lt_or_ge k 16 with g1 | g1
  · exact checkCas_spec _ _ cas_0_1 k g0 g1
  rcases Nat.lt_or_ge k 24 with g2 | g2
  · exact checkCas_spec _ _ cas_0_2 k g1 g2
  rcases Nat.lt_or_ge k 32 with g3 | g3
  · exact checkCas_spec _ _ cas_0_3 k g2 g3
  rcases Nat.lt_or_ge k 40 with g4 | g4
  · exact checkCas_spec _ _ cas_0_4 k g3 g4
  rcases Nat.lt_or_ge k 48 with g5 | g5
  · exact checkCas_spec _ _ cas_0_5 k g4 g5
  rcases Nat.lt_or_ge k 56 with g6 | g6
  · exact checkCas_spec _ _ cas_0_6 k g5 g6
  exact checkCas_spec _ _ cas_0_7 k g6 hb

end Pfq54.CF
