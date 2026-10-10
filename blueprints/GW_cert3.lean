/-
# Block certificates at `n = 18, …, 23` (kernel-checked)
-/
import GW_fast

namespace ZetasIrr.GW

theorem checkAll_3 : checkAll [18, 19, 20, 21, 22, 23] = true := by decide +kernel

end ZetasIrr.GW
