import cas_spec

namespace Pfq54.CF

theorem cas_5_0 : checkCas 320 8 = true := by decide +kernel

theorem cas_5_1 : checkCas 328 8 = true := by decide +kernel

theorem cas_5_2 : checkCas 336 8 = true := by decide +kernel

theorem cas_5_3 : checkCas 344 8 = true := by decide +kernel

theorem cas_5_4 : checkCas 352 8 = true := by decide +kernel

theorem cas_5_5 : checkCas 360 8 = true := by decide +kernel

theorem cas_5_6 : checkCas 368 8 = true := by decide +kernel

theorem cas_5_7 : checkCas 376 8 = true := by decide +kernel

theorem cas_range_5 (k : Nat) (ha : 320 ≤ k) (hb : k < 384) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 328 with g0 | g0
  · exact checkCas_spec _ _ cas_5_0 k ha g0
  rcases Nat.lt_or_ge k 336 with g1 | g1
  · exact checkCas_spec _ _ cas_5_1 k g0 g1
  rcases Nat.lt_or_ge k 344 with g2 | g2
  · exact checkCas_spec _ _ cas_5_2 k g1 g2
  rcases Nat.lt_or_ge k 352 with g3 | g3
  · exact checkCas_spec _ _ cas_5_3 k g2 g3
  rcases Nat.lt_or_ge k 360 with g4 | g4
  · exact checkCas_spec _ _ cas_5_4 k g3 g4
  rcases Nat.lt_or_ge k 368 with g5 | g5
  · exact checkCas_spec _ _ cas_5_5 k g4 g5
  rcases Nat.lt_or_ge k 376 with g6 | g6
  · exact checkCas_spec _ _ cas_5_6 k g5 g6
  exact checkCas_spec _ _ cas_5_7 k g6 hb

end Pfq54.CF
