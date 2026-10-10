/-
# Chamber certificate: chambers `9` to `17` (kernel-checked).
-/
import Chamber_cert

namespace ZetasIrr.CH

theorem chamber_9 : chamberOK 9 = true := by decide +kernel
theorem chamber_10 : chamberOK 10 = true := by decide +kernel
theorem chamber_11 : chamberOK 11 = true := by decide +kernel
theorem chamber_12 : chamberOK 12 = true := by decide +kernel
theorem chamber_13 : chamberOK 13 = true := by decide +kernel
theorem chamber_14 : chamberOK 14 = true := by decide +kernel
theorem chamber_15 : chamberOK 15 = true := by decide +kernel
theorem chamber_16 : chamberOK 16 = true := by decide +kernel
theorem chamber_17 : chamberOK 17 = true := by decide +kernel

end ZetasIrr.CH
