/-
# Chamber certificate: chambers `0` to `8` (kernel-checked).
-/
import Chamber_cert

namespace ZetasIrr.CH

theorem chamber_0 : chamberOK 0 = true := by decide +kernel
theorem chamber_1 : chamberOK 1 = true := by decide +kernel
theorem chamber_2 : chamberOK 2 = true := by decide +kernel
theorem chamber_3 : chamberOK 3 = true := by decide +kernel
theorem chamber_4 : chamberOK 4 = true := by decide +kernel
theorem chamber_5 : chamberOK 5 = true := by decide +kernel
theorem chamber_6 : chamberOK 6 = true := by decide +kernel
theorem chamber_7 : chamberOK 7 = true := by decide +kernel
theorem chamber_8 : chamberOK 8 = true := by decide +kernel

end ZetasIrr.CH
