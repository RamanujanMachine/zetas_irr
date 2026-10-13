/-
# Mellin inversion for `Γ(w+j) Γ(L-w)` and power bounds (sorry-free)

`(1/2π) ∫ Γ(w+j) Γ(L-w) v^w dy = Γ(L+j) v^L / (1+v)^{L+j}` on `w = 1/2 + iy`, `v > 0`.
-/
import mg_aux1
import mg_aux2

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

/-- **Mellin inversion** for the pair `Γ(w+j) Γ(L-w)`, `(1+u)^{-L-j} u^j`. -/
theorem mellin_point (L j : ℕ) (hL : 2 ≤ L) (v : ℝ) (hv : 0 < v) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ y : ℝ, Complex.Gamma (wl y + j) * Complex.Gamma (L - wl y) * (v : ℂ) ^ (wl y) =
      Complex.Gamma (L + j) * ((v ^ L / (1 + v) ^ (L + j) : ℝ) : ℂ) := by
  have hL1 : 1 ≤ L := by omega
  have hre : ∀ y : ℝ, 0 < (wl y).re ∧ (wl y).re < L := fun y => by
    rw [wl_re]
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    constructor <;> linarith
  have hne : Complex.Gamma ((L : ℂ) + j) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    rw [Complex.add_re, Complex.natCast_re, Complex.natCast_re]
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity)
  have hM : ∀ y : ℝ, mellin (fj L j) (wl y) =
      Complex.Gamma (wl y + j) * Complex.Gamma (L - wl y) / Complex.Gamma (L + j) := fun y =>
    (mellin_fj L j hL (wl y) (hre y).1 (hre y).2).2
  have hconv : MellinConvergent (fj L j) ((1 / 2 : ℝ) : ℂ) := by
    have := (mellin_fj L j hL ((1 / 2 : ℝ) : ℂ) (by norm_num) (by
      rw [Complex.ofReal_re]
      have : (2 : ℝ) ≤ L := by exact_mod_cast hL
      linarith)).1
    exact this
  have hvert : Complex.VerticalIntegrable (mellin (fj L j)) (1 / 2) := by
    unfold Complex.VerticalIntegrable
    refine ((gamma_line_integrable L j hL1).div_const (Complex.Gamma (L + j))).congr ?_
    exact Eventually.of_forall fun y => (hM y).symm
  have hinv := mellinInv_mellin_eq (1 / 2) (fj L j) (by positivity : (0 : ℝ) < 1 / v) hconv hvert
    (fj_continuousAt L j _ (by positivity))
  unfold mellinInv at hinv
  have hpow : ∀ y : ℝ, (((1 / v : ℝ) : ℂ)) ^ (-(((1 / 2 : ℝ) : ℂ) + y * Complex.I)) =
      (v : ℂ) ^ (wl y) := fun y => by
    rw [show ((1 / 2 : ℝ) : ℂ) + y * Complex.I = wl y from rfl, Complex.cpow_neg,
      one_div, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg hv.le]; exact Real.pi_ne_zero.symm), inv_inv]
  have hint : ∀ y : ℝ, (((1 / v : ℝ) : ℂ)) ^ (-(((1 / 2 : ℝ) : ℂ) + y * Complex.I)) •
      mellin (fj L j) (((1 / 2 : ℝ) : ℂ) + y * Complex.I) =
      Complex.Gamma (wl y + j) * Complex.Gamma (L - wl y) * (v : ℂ) ^ (wl y) /
        Complex.Gamma (L + j) := fun y => by
    rw [hpow, show ((1 / 2 : ℝ) : ℂ) + y * Complex.I = wl y from rfl, hM, smul_eq_mul]
    ring
  simp_rw [hint] at hinv
  rw [integral_div] at hinv
  have hf : fj L j (1 / v) = ((v ^ L / (1 + v) ^ (L + j) : ℝ) : ℂ) := by
    unfold fj
    congr 1
    rw [one_div, inv_pow, show 1 + v⁻¹ = (v + 1) / v by field_simp, div_pow, pow_add]
    field_simp
    ring
  rw [hf, Complex.real_smul] at hinv
  rw [← hinv]
  push_cast
  field_simp

/-- `‖x^s‖ ≤ 1` for `0 ≤ x ≤ 1` and `0 ≤ Re s`. -/
theorem norm_cpow_le_one (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖(x : ℂ) ^ s‖ ≤ 1 := by
  rcases h0.lt_or_eq with h0 | rfl
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h0]
    exact Real.rpow_le_one h0.le h1 hs
  · rcases eq_or_ne s 0 with rfl | hs0
    · rw [Complex.cpow_zero, norm_one]
    · rw [Complex.ofReal_zero, Complex.zero_cpow hs0, norm_zero]
      exact zero_le_one

/-- `x^{(w + a) - 1} = x^{a-1} x^w` for `x > 0` and `a ≥ 1`. -/
theorem cpow_split (x : ℝ) (hx : 0 < x) (w : ℂ) (a : ℕ) (ha : 1 ≤ a) :
    (x : ℂ) ^ ((w + a) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) * (x : ℂ) ^ w := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show (w + a) - 1 = w + ((a - 1 : ℕ) : ℂ) by rw [Nat.cast_sub ha]; push_cast; ring,
    Complex.cpow_add _ _ hxc, Complex.cpow_natCast, mul_comm]
  push_cast
  rfl

/-- `x^{(a : ℕ) - 1} = x^{a - 1}` for natural `a ≥ 1`. -/
theorem cpow_nat_sub (x : ℂ) (a : ℕ) (ha : 1 ≤ a) : x ^ ((a : ℂ) - 1) = x ^ (a - 1) := by
  rw [show (a : ℂ) - 1 = ((a - 1 : ℕ) : ℂ) by rw [Nat.cast_sub ha]; push_cast; ring,
    Complex.cpow_natCast]

end Pfq54.MG
