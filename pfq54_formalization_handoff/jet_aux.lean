/-
# Jets of products of binomials (sorry-free)

Logarithmic jets `jet a (a x)` multiply by adding the logarithmic derivatives.
-/
import Pfq54_aux

open Finset

noncomputable section

namespace Pfq54.RA

open Pfq54

theorem jet_mul_log (a x b y : ℚ) :
    jet a (a * x) * jet b (b * y) = jet (a * b) (a * b * (x + y)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst]
  · rw [DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd, Aux.jet_snd, Aux.jet_snd]
    ring

theorem jet_mul_zero (a x s : ℚ) : jet a x * jet 0 s = jet 0 (a * s) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst, mul_zero]
  · rw [DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd, Aux.jet_snd, Aux.jet_snd,
      mul_zero, add_zero]

theorem jet_zero_mul (s b y : ℚ) : jet 0 s * jet b y = jet 0 (s * b) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst, zero_mul]
  · rw [DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd, Aux.jet_snd, Aux.jet_snd,
      zero_mul, zero_add]

theorem upperJet_log (N M : ℕ) (h : M ≤ N) :
    upperJet N M = jet (N.choose M) (N.choose M * -(harm 1 N - harm 1 (N - M))) := by
  rw [upperJet, ite_eq_left h, neg_mul, mul_neg]

theorem lowerJet_log (M m : ℕ) (h : m ≤ M) :
    lowerJet M (m : ℤ) = jet (M.choose m) (M.choose m * (harm 1 m - harm 1 (M - m))) := by
  rw [lowerJet, ite_eq_left ⟨Int.natCast_nonneg m, Int.ofNat_le.mpr h⟩, Int.toNat_natCast]

theorem lowerJet_neg (M d : ℕ) (hd : 0 < d) :
    lowerJet M (-(d : ℤ)) =
      jet 0 ((-1 : ℚ) ^ d * M.factorial * (d - 1).factorial / (M + d).factorial) := by
  rw [lowerJet, ite_eq_right (by omega), ite_eq_left (by omega), neg_neg, Int.toNat_natCast]

theorem lowerJet_big (M d : ℕ) (hd : 0 < d) :
    lowerJet M ((M + d : ℕ) : ℤ) =
      jet 0 ((-1 : ℚ) ^ (d - 1) * M.factorial * (d - 1).factorial / (M + d).factorial) := by
  rw [lowerJet, ite_eq_right (by omega), ite_eq_right (by omega),
    show ((M + d : ℕ) : ℤ) - M = d by push_cast; ring, Int.toNat_natCast]

/-- The value of the three upper binomials. -/
def Cu (n j : ℕ) : ℚ :=
  ((j + 10 * n).choose (10 * n) : ℚ) * ((j + 11 * n).choose (10 * n) : ℚ) *
    ((j + 12 * n).choose (10 * n) : ℚ)

/-- The logarithmic derivative of the three upper binomials. -/
def Xu (n j : ℕ) : ℚ :=
  -(harm 1 (j + 10 * n) - harm 1 (j + 10 * n - 10 * n)) +
    -(harm 1 (j + 11 * n) - harm 1 (j + 11 * n - 10 * n)) +
      -(harm 1 (j + 12 * n) - harm 1 (j + 12 * n - 10 * n))

theorem upper_jets (n j : ℕ) :
    ∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n) = jet (Cu n j) (Cu n j * Xu n j) := by
  rw [Aux.prod_Icc_10_12, upperJet_log (j + 10 * n) (10 * n) (by omega),
    upperJet_log (j + 11 * n) (10 * n) (by omega), upperJet_log (j + 12 * n) (10 * n) (by omega),
    jet_mul_log, jet_mul_log]
  rfl

end Pfq54.RA
