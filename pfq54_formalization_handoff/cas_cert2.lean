import cas_spec

namespace Pfq54.CF

theorem cas_2_0 : checkCas 128 8 = true := by decide +kernel

theorem cas_2_1 : checkCas 136 8 = true := by decide +kernel

theorem cas_2_2 : checkCas 144 8 = true := by decide +kernel

theorem cas_2_3 : checkCas 152 8 = true := by decide +kernel

theorem cas_2_4 : checkCas 160 8 = true := by decide +kernel

theorem cas_2_5 : checkCas 168 8 = true := by decide +kernel

theorem cas_2_6 : checkCas 176 8 = true := by decide +kernel

theorem cas_2_7 : checkCas 184 8 = true := by decide +kernel

theorem cas_range_2 (k : Nat) (ha : 128 ≤ k) (hb : k < 192) :
    PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 136 with g0 | g0
  · exact checkCas_spec _ _ cas_2_0 k ha g0
  rcases Nat.lt_or_ge k 144 with g1 | g1
  · exact checkCas_spec _ _ cas_2_1 k g0 g1
  rcases Nat.lt_or_ge k 152 with g2 | g2
  · exact checkCas_spec _ _ cas_2_2 k g1 g2
  rcases Nat.lt_or_ge k 160 with g3 | g3
  · exact checkCas_spec _ _ cas_2_3 k g2 g3
  rcases Nat.lt_or_ge k 168 with g4 | g4
  · exact checkCas_spec _ _ cas_2_4 k g3 g4
  rcases Nat.lt_or_ge k 176 with g5 | g5
  · exact checkCas_spec _ _ cas_2_5 k g4 g5
  rcases Nat.lt_or_ge k 184 with g6 | g6
  · exact checkCas_spec _ _ cas_2_6 k g5 g6
  exact checkCas_spec _ _ cas_2_7 k g6 hb

end Pfq54.CF
