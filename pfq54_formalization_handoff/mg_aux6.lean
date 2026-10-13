/-
# The Mellin–Barnes integrand on `s = 2n + w` (sorry-free)

`𝓜(2n + w) = Γ(w) R(w)` with the three beta ratios and `Γ(w+n) Γ(15n+1-w)`, and
`(1/2π) ∫ Γ(w+j) R(w) dy = c₀ Γ(L+j) ∫ P q^j`, `c₀ = (16n)!/((11n)!² (8n+1)!)`, `L = 14n+1`.
-/
import mg_aux5
import Pfq54_defs

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

open Pfq54

/-- `R(w) = Γ(L-w)Γ(15n+1-w)Γ(w+n)Γ(w+2n)Γ(w+3n)Γ(w+4n) / (Γ(w+13n+1)Γ(w+14n+1)Γ(w+12n+2))`. -/
def Rf (n : ℕ) (w : ℂ) : ℂ :=
  Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - w) * Complex.Gamma (((15 * n + 1 : ℕ) : ℂ) - w) *
      Complex.Gamma (w + (n : ℂ)) * Complex.Gamma (w + ((2 * n : ℕ) : ℂ)) *
      Complex.Gamma (w + ((3 * n : ℕ) : ℂ)) * Complex.Gamma (w + ((4 * n : ℕ) : ℂ)) /
    (Complex.Gamma (w + ((13 * n + 1 : ℕ) : ℂ)) * Complex.Gamma (w + ((14 * n + 1 : ℕ) : ℂ)) *
      Complex.Gamma (w + ((12 * n + 2 : ℕ) : ℂ)))

theorem mb_expand (n : ℕ) (w : ℂ) :
    mbIntegrand n (2 * n + w) = Complex.Gamma w * Rf n w := by
  unfold mbIntegrand Rf
  rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by rfl, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton,
    show Complex.Gamma (16 * n + 1 - (2 * n + w)) = Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - w) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (17 * n + 1 - (2 * n + w)) = Complex.Gamma (((15 * n + 1 : ℕ) : ℂ) - w) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + 11 * n + 1) = Complex.Gamma (w + ((13 * n + 1 : ℕ) : ℂ)) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + 12 * n + 1) = Complex.Gamma (w + ((14 * n + 1 : ℕ) : ℂ)) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + 10 * n + 2) = Complex.Gamma (w + ((12 * n + 2 : ℕ) : ℂ)) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + ((-2 : ℤ) : ℂ) * n) = Complex.Gamma w from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + ((-1 : ℤ) : ℂ) * n) = Complex.Gamma (w + (n : ℂ)) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + ((0 : ℤ) : ℂ) * n) = Complex.Gamma (w + ((2 * n : ℕ) : ℂ)) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + ((1 : ℤ) : ℂ) * n) = Complex.Gamma (w + ((3 * n : ℕ) : ℂ)) from
      congrArg _ (by push_cast; ring),
    show Complex.Gamma (2 * n + w + ((2 : ℤ) : ℂ) * n) = Complex.Gamma (w + ((4 * n : ℕ) : ℂ)) from
      congrArg _ (by push_cast; ring)]
  ring

/-- `c₀ = Γ(16n+1) / (Γ(11n+1)² Γ(8n+2))`. -/
def c0 (n : ℕ) : ℂ :=
  Complex.Gamma ((16 * n + 1 : ℕ) : ℂ) /
    (Complex.Gamma ((11 * n + 1 : ℕ) : ℂ) ^ 2 * Complex.Gamma ((8 * n + 2 : ℕ) : ℂ))

theorem Gamma_pos_ne (s : ℂ) (hs : 0 < s.re) : Complex.Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hs

/-- `Γ(w+j) R(w) = c₀ Γ(w+j) Γ(L-w) ∫ (beta integrands)`. -/
theorem Gj_eq (n j : ℕ) (hn : 1 ≤ n) (w : ℂ) (hw : w.re = 1 / 2) :
    Complex.Gamma (w + j) * Rf n w = c0 n * (Complex.Gamma (w + j) *
      Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - w) * ∫ z, bprod n w z ∂μ4) := by
  have hpos : ∀ c : ℕ, 0 < (w + (c : ℂ)).re := fun c => by
    rw [Complex.add_re, hw, Complex.natCast_re]
    positivity
  have hnat : ∀ c : ℕ, 0 < c → Complex.Gamma (c : ℂ) ≠ 0 := fun c hc =>
    Gamma_pos_ne _ (by rw [Complex.natCast_re]; exact_mod_cast hc)
  rw [bprod_integral n hn w hw,
    show Complex.Gamma (w + ((2 * n : ℕ) : ℂ) + ((11 * n + 1 : ℕ) : ℂ)) =
      Complex.Gamma (w + ((13 * n + 1 : ℕ) : ℂ)) from congrArg _ (by push_cast; ring),
    show Complex.Gamma (w + ((3 * n : ℕ) : ℂ) + ((11 * n + 1 : ℕ) : ℂ)) =
      Complex.Gamma (w + ((14 * n + 1 : ℕ) : ℂ)) from congrArg _ (by push_cast; ring),
    show Complex.Gamma (w + ((4 * n : ℕ) : ℂ) + ((8 * n + 2 : ℕ) : ℂ)) =
      Complex.Gamma (w + ((12 * n + 2 : ℕ) : ℂ)) from congrArg _ (by push_cast; ring),
    show Complex.Gamma (w + (n : ℂ) + (((15 * n + 1 : ℕ) : ℂ) - w)) =
      Complex.Gamma ((16 * n + 1 : ℕ) : ℂ) from congrArg _ (by push_cast; ring)]
  have h1 := hnat (11 * n + 1) (by omega)
  have h2 := hnat (8 * n + 2) (by omega)
  have h3 := hnat (16 * n + 1) (by omega)
  have h4 := Gamma_pos_ne _ (hpos (13 * n + 1))
  have h5 := Gamma_pos_ne _ (hpos (14 * n + 1))
  have h6 := Gamma_pos_ne _ (hpos (12 * n + 2))
  unfold Rf c0
  field_simp

theorem integral_bprod_le (n : ℕ) (hn : 1 ≤ n) (y : ℝ) :
    ‖∫ z, bprod n (wl y) z ∂μ4‖ ≤ μ4.real univ := by
  calc ‖∫ z, bprod n (wl y) z ∂μ4‖ ≤ ∫ _z, (1 : ℝ) ∂μ4 :=
        norm_integral_le_of_norm_le (integrable_const 1)
          (ae_cube.mono fun z hz => bprod_le n hn y z hz)
    _ = μ4.real univ := by rw [integral_const, smul_eq_mul, mul_one]

/-- `y ↦ Γ(w+j) R(w)` is integrable on the line. -/
theorem Gj_integrable (n j : ℕ) (hn : 1 ≤ n) :
    Integrable fun y : ℝ => Complex.Gamma (wl y + j) * Rf n (wl y) := by
  have hAi := gamma_line_integrable (14 * n + 1) j (by omega)
  have hAc := gamma_line_continuous (14 * n + 1) j (by omega)
  have hI : StronglyMeasurable fun y : ℝ => ∫ z, bprod n (wl y) z ∂μ4 :=
    (bprod_measurable n).stronglyMeasurable.integral_prod_right'
  have hint : Integrable fun y : ℝ => c0 n * (Complex.Gamma (wl y + j) *
      Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - wl y) * ∫ z, bprod n (wl y) z ∂μ4) := by
    refine (hAi.norm.const_mul (‖c0 n‖ * μ4.real univ)).mono'
      (aestronglyMeasurable_const.mul (hAc.aestronglyMeasurable.mul hI.aestronglyMeasurable))
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_mul]
    calc ‖c0 n‖ * (‖Complex.Gamma (wl y + j) * Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - wl y)‖ *
          ‖∫ z, bprod n (wl y) z ∂μ4‖)
        ≤ ‖c0 n‖ * (‖Complex.Gamma (wl y + j) * Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - wl y)‖ *
          μ4.real univ) := by gcongr; exact integral_bprod_le n hn y
      _ = _ := by ring
  exact hint.congr (Eventually.of_forall fun y => (Gj_eq n j hn (wl y) (wl_re y)).symm)

/-- `J_j = c₀ Γ(L+j) ∫ P q^j`. -/
theorem J_eq (n j : ℕ) (hn : 1 ≤ n) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, Complex.Gamma (wl y + j) * Rf n (wl y) =
      c0 n * Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) + j) *
        ((∫ z, Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j ∂μ4 : ℝ) : ℂ) := by
  rw [integral_congr_ae (Eventually.of_forall fun y => Gj_eq n j hn (wl y) (wl_re y)),
    integral_const_mul, mul_left_comm, rep_j n j hn]
  ring

theorem contour_eq (n : ℕ) (y : ℝ) : mbContour n y = 2 * n + wl y := by
  unfold mbContour wl
  push_cast
  ring

end Pfq54.MG
