/-
# Block certificates at `n = 24, …, 29` (kernel-checked)
-/
import GW_fast

namespace ZetasIrr.GW

theorem checkAll_4 : checkAll [24, 25, 26, 27, 28, 29] = true := by decide +kernel

end ZetasIrr.GW
