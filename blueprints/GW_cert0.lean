/-
# Block certificates at `n = 0, …, 5` (kernel-checked)
-/
import GW_fast

namespace ZetasIrr.GW

theorem checkAll_0 : checkAll [0, 1, 2, 3, 4, 5] = true := by decide +kernel

end ZetasIrr.GW
