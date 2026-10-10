/-
# Block certificates at `n = 6, …, 11` (kernel-checked)
-/
import GW_fast

namespace ZetasIrr.GW

theorem checkAll_1 : checkAll [6, 7, 8, 9, 10, 11] = true := by decide +kernel

end ZetasIrr.GW
