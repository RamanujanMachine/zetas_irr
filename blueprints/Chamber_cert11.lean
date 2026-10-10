/-
# Chamber certificate: chambers `99` to `107` (kernel-checked).
-/
import Chamber_cert

namespace ZetasIrr.CH

theorem chamber_99 : chamberOK 99 = true := by decide +kernel
theorem chamber_100 : chamberOK 100 = true := by decide +kernel
theorem chamber_101 : chamberOK 101 = true := by decide +kernel
theorem chamber_102 : chamberOK 102 = true := by decide +kernel
theorem chamber_103 : chamberOK 103 = true := by decide +kernel
theorem chamber_104 : chamberOK 104 = true := by decide +kernel
theorem chamber_105 : chamberOK 105 = true := by decide +kernel
theorem chamber_106 : chamberOK 106 = true := by decide +kernel
theorem chamber_107 : chamberOK 107 = true := by decide +kernel

end ZetasIrr.CH
