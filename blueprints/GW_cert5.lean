/-
# Block certificates at `n = 30, …, 35` (kernel-checked)
-/
import GW_fast

namespace ZetasIrr.GW

theorem checkAll_5 : checkAll [30, 31, 32, 33, 34, 35] = true := by decide +kernel

end ZetasIrr.GW
