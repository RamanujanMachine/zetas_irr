/-
# The state `𝒮_G(n)` through the positive integral (sorry-free)

`𝒮_G(n)_0 = 𝔠_n X₀` and `‖𝒮_G(n)_k‖ ≤ (16n+1)^k 𝔠_n X₀` (`k ≤ 3`), `X_j = ∫ P q^j`,
from `(w+2n)^k Γ(w) = ∑ c_j Γ(w+j)` with `c_j ≥ 0` and `∑ c_j (L)_j = (L+2n)^k`.
-/
import mg_aux6

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

open Pfq54

/-- `X_j = ∫ P q^j`. -/
def Xj (n j : ℕ) : ℝ := ∫ z, Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j ∂μ4

/-- `𝔠_n = (16n)! (14n)! / ((11n)!² (8n+1)!)`. -/
def cfR (n : ℕ) : ℝ :=
  ((16 * n).factorial * (14 * n).factorial : ℝ) / ((11 * n).factorial ^ 2 * (8 * n + 1).factorial)

/-- The value `J_j = 𝔠_n (L)_j X_j`. -/
theorem J_real (n j : ℕ) (hn : 1 ≤ n) (P : ℝ)
    (hP : ((14 * n + j).factorial : ℝ) = (14 * n).factorial * P) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, Complex.Gamma (wl y + j) * Rf n (wl y) =
      ((cfR n * P * Xj n j : ℝ) : ℂ) := by
  rw [J_eq n j hn]
  unfold c0 cfR Xj
  rw [show ((16 * n + 1 : ℕ) : ℂ) = ((16 * n : ℕ) : ℂ) + 1 by push_cast; ring,
    show ((11 * n + 1 : ℕ) : ℂ) = ((11 * n : ℕ) : ℂ) + 1 by push_cast; ring,
    show ((8 * n + 2 : ℕ) : ℂ) = ((8 * n + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
    show ((14 * n + 1 : ℕ) : ℂ) + j = ((14 * n + j : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial]
  have hc : ((14 * n + j).factorial : ℂ) = ((14 * n).factorial : ℂ) * (P : ℂ) := by
    exact_mod_cast hP
  rw [hc]
  push_cast
  ring

/-- `0 ≤ X_j ≤ X₀`. -/
theorem Xj_bounds (n j : ℕ) (_hn : 1 ≤ n)
    (hPint : Integrable (fun z : ℝ × ℝ × ℝ × ℝ => Pd n z.1 z.2.1 z.2.2.1 z.2.2.2) μ4) :
    0 ≤ Xj n j ∧ Xj n j ≤ Xj n 0 := by
  have hpos : ∀ᵐ z ∂μ4, 0 ≤ Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 ∧ 0 ≤ qd z ∧ qd z ≤ 1 :=
    ae_cube.mono fun z hz => by
      obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, ⟨ht0, ht1⟩, ⟨hr0, hr1⟩⟩ := hz
      have hb : 0 < 1 - z.2.2.2 := sub_pos.mpr hr1
      have hD : 0 < (1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2 := by positivity
      have hN : 0 < z.1 * z.2.1 * z.2.2.1 * z.2.2.2 := by positivity
      refine ⟨?_, div_nonneg hb.le hD.le, (div_le_one hD).mpr (by linarith)⟩
      unfold Pd
      have : 0 < 1 - z.1 := sub_pos.mpr hx1
      have : 0 < 1 - z.2.1 := sub_pos.mpr hy1
      have : 0 < 1 - z.2.2.1 := sub_pos.mpr ht1
      positivity
  have hmq : Measurable fun z : ℝ × ℝ × ℝ × ℝ => Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j := by
    unfold Pd qd
    fun_prop
  have hle : ∀ᵐ z ∂μ4, ‖Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j‖ ≤
      Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 := hpos.mono fun z h => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.1 (pow_nonneg h.2.1 j))]
    exact mul_le_of_le_one_right h.1 (pow_le_one₀ h.2.1 h.2.2)
  have hi : Integrable (fun z : ℝ × ℝ × ℝ × ℝ => Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j) μ4 :=
    hPint.mono' hmq.aestronglyMeasurable hle
  unfold Xj
  refine ⟨integral_nonneg_of_ae (hpos.mono fun z h => mul_nonneg h.1 (pow_nonneg h.2.1 j)), ?_⟩
  refine integral_mono_ae hi (hPint.congr (Eventually.of_forall fun z => by
    beta_reduce; rw [pow_zero, mul_one])) (hle.mono fun z h => ?_)
  beta_reduce
  rw [pow_zero, mul_one]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le h)

/-- `𝒮_G(n)_k` as an integral of `(−(2n+w))^k Γ(w) R(w)`. -/
theorem SG_expr (n k : ℕ) :
    SG n k = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ y : ℝ, (-(2 * n + wl y)) ^ k * (Complex.Gamma (wl y) * Rf n (wl y)) := by
  unfold SG
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (-mbContour n y) ^ k * mbIntegrand n (mbContour n y) = _
  rw [contour_eq, mb_expand]

/-- The shifts `Γ(w+j) = (w)_j Γ(w)`, `j ≤ 3`. -/
theorem Gamma_shifts (w : ℂ) (hw : w.re = 1 / 2) :
    Complex.Gamma (w + ((1 : ℕ) : ℂ)) = w * Complex.Gamma w ∧
      Complex.Gamma (w + ((2 : ℕ) : ℂ)) = (w + 1) * w * Complex.Gamma w ∧
        Complex.Gamma (w + ((3 : ℕ) : ℂ)) = (w + 2) * (w + 1) * w * Complex.Gamma w := by
  have ne : ∀ c : ℝ, 0 ≤ c → w + c ≠ 0 := fun c hc h => by
    have := congrArg Complex.re h
    rw [Complex.add_re, hw, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  have h1 : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w (by simpa using ne 0 le_rfl)
  have h2 : Complex.Gamma (w + 2) = (w + 1) * w * Complex.Gamma w := by
    rw [show w + 2 = (w + 1) + 1 by ring, Complex.Gamma_add_one _ (by simpa using ne 1 zero_le_one),
      h1]
    ring
  have h3 : Complex.Gamma (w + 3) = (w + 2) * (w + 1) * w * Complex.Gamma w := by
    rw [show w + 3 = (w + 2) + 1 by ring,
      Complex.Gamma_add_one _ (by simpa using ne 2 zero_le_two), h2]
    ring
  push_cast
  exact ⟨h1, h2, h3⟩

end Pfq54.MG
