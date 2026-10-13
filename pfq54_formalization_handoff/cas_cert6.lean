import cas_spec

namespace Pfq54.CF

theorem cas_6_0 : checkCas 384 8 = true := by decide +kernel

theorem cas_6_1 : checkCas 392 8 = true := by decide +kernel

theorem cas_6_2 : checkCas 400 8 = true := by decide +kernel

theorem cas_6_3 : checkCas 408 8 = true := by decide +kernel

theorem cas_6_4 : checkCas 416 8 = true := by decide +kernel

theorem cas_6_5 : checkCas 424 8 = true := by decide +kernel

theorem cas_6_6 : checkCas 432 8 = true := by decide +kernel

theorem cas_6_7 : checkCas 440 8 = true := by decide +kernel

theorem cas_range_6 (k : Nat) (ha : 384 ≤ k) (hb : k < 448) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 392 with g0 | g0
  · exact checkCas_spec _ _ cas_6_0 k ha g0
  rcases Nat.lt_or_ge k 400 with g1 | g1
  · exact checkCas_spec _ _ cas_6_1 k g0 g1
  rcases Nat.lt_or_ge k 408 with g2 | g2
  · exact checkCas_spec _ _ cas_6_2 k g1 g2
  rcases Nat.lt_or_ge k 416 with g3 | g3
  · exact checkCas_spec _ _ cas_6_3 k g2 g3
  rcases Nat.lt_or_ge k 424 with g4 | g4
  · exact checkCas_spec _ _ cas_6_4 k g3 g4
  rcases Nat.lt_or_ge k 432 with g5 | g5
  · exact checkCas_spec _ _ cas_6_5 k g4 g5
  rcases Nat.lt_or_ge k 440 with g6 | g6
  · exact checkCas_spec _ _ cas_6_6 k g5 g6
  exact checkCas_spec _ _ cas_6_7 k g6 hb

end Pfq54.CF
