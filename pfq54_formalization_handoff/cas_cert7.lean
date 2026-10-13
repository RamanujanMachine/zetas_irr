import cas_spec

namespace Pfq54.CF

theorem cas_7_0 : checkCas 448 8 = true := by decide +kernel

theorem cas_7_1 : checkCas 456 8 = true := by decide +kernel

theorem cas_7_2 : checkCas 464 8 = true := by decide +kernel

theorem cas_7_3 : checkCas 472 8 = true := by decide +kernel

theorem cas_7_4 : checkCas 480 8 = true := by decide +kernel

theorem cas_7_5 : checkCas 488 8 = true := by decide +kernel

theorem cas_7_6 : checkCas 496 8 = true := by decide +kernel

theorem cas_7_7 : checkCas 504 8 = true := by decide +kernel

theorem cas_range_7 (k : Nat) (ha : 448 ≤ k) (hb : k < 512) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 456 with g0 | g0
  · exact checkCas_spec _ _ cas_7_0 k ha g0
  rcases Nat.lt_or_ge k 464 with g1 | g1
  · exact checkCas_spec _ _ cas_7_1 k g0 g1
  rcases Nat.lt_or_ge k 472 with g2 | g2
  · exact checkCas_spec _ _ cas_7_2 k g1 g2
  rcases Nat.lt_or_ge k 480 with g3 | g3
  · exact checkCas_spec _ _ cas_7_3 k g2 g3
  rcases Nat.lt_or_ge k 488 with g4 | g4
  · exact checkCas_spec _ _ cas_7_4 k g3 g4
  rcases Nat.lt_or_ge k 496 with g5 | g5
  · exact checkCas_spec _ _ cas_7_5 k g4 g5
  rcases Nat.lt_or_ge k 504 with g6 | g6
  · exact checkCas_spec _ _ cas_7_6 k g5 g6
  exact checkCas_spec _ _ cas_7_7 k g6 hb

end Pfq54.CF
