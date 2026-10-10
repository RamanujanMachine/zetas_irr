/-
# Block certificates at `n = 12, …, 17` (kernel-checked)
-/
import GW_fast

namespace ZetasIrr.GW

theorem checkAll_2 : checkAll [12, 13, 14, 15, 16, 17] = true := by decide +kernel

end ZetasIrr.GW
