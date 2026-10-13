/-
# The Mellin transform of `u^j (1+u)^{-L-j}` (sorry-free)

`∫₀^∞ u^{w-1} u^j (1+u)^{-L-j} du = Γ(w+j) Γ(L-w) / Γ(L+j)` for `0 < Re w < L`, via
`u = x/(1-x)` and Euler's beta integral.
-/
import Mathlib

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

/-- `u^j / (1+u)^(L+j)`. -/
def fj (L j : ℕ) (u : ℝ) : ℂ := ((u ^ j / (1 + u) ^ (L + j) : ℝ) : ℂ)

/-- The substitution `x ↦ x/(1-x)`. -/
def φ (x : ℝ) : ℝ := x / (1 - x)

theorem phi_image : φ '' Ioo 0 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨x, ⟨h0, h1⟩, rfl⟩
    exact div_pos h0 (sub_pos.mpr h1)
  · intro ht
    have ht' : (0 : ℝ) < t := ht
    refine ⟨t / (1 + t), ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩, ?_⟩
    have h1 : (1 : ℝ) - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
    unfold φ
    rw [h1]
    field_simp

theorem phi_inj : InjOn φ (Ioo 0 1) := by
  intro a ha b hb h
  unfold φ at h
  rw [div_eq_div_iff (sub_pos.mpr ha.2).ne' (sub_pos.mpr hb.2).ne'] at h
  linarith

theorem phi_deriv (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivWithinAt φ (1 / (1 - x) ^ 2) (Ioo 0 1) x := by
  have hb : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have h2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have h := (hasDerivAt_id' x).div h2 hb
  show HasDerivWithinAt (fun y : ℝ => y / (1 - y)) _ _ _
  convert h.hasDerivWithinAt using 1
  ring

/-- The substituted integrand is the beta integrand. -/
theorem fj_beta (L j : ℕ) (hL : 2 ≤ L) (w : ℂ) (x : ℝ) (hx : x ∈ Ioo 0 1) :
    |1 / (1 - x) ^ 2| • (((φ x : ℝ) : ℂ) ^ (w - 1) • fj L j (φ x)) =
      (x : ℂ) ^ ((w + j) - 1) * (1 - (x : ℂ)) ^ (((L : ℂ) - w) - 1) := by
  obtain ⟨ha, hb⟩ := hx
  have hb' : 0 < 1 - x := sub_pos.mpr hb
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbc : ((1 - x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb'.ne'
  have hreal : |1 / (1 - x) ^ 2| * ((x / (1 - x)) ^ j / (1 + x / (1 - x)) ^ (L + j)) =
      x ^ j * (1 - x) ^ (L - 2) := by
    have hb0 : 1 - x ≠ 0 := hb'.ne'
    rw [abs_of_pos (by positivity), show L + j = (L - 2) + j + 2 by omega]
    have e : 1 + x / (1 - x) = 1 / (1 - x) := by field_simp; ring
    rw [e, div_pow, one_div_pow, pow_add, pow_add]
    field_simp
  have h1 : (((x / (1 - x) : ℝ)) : ℂ) ^ (w - 1) =
      (x : ℂ) ^ (w - 1) * ((1 - x : ℝ) : ℂ) ^ (1 - w) := by
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg ha.le hb'.le,
      show (1 : ℂ) - w = -(w - 1) by ring, Complex.cpow_neg, div_eq_mul_inv]
  have h2 : (x : ℂ) ^ ((w + j) - 1) = (x : ℂ) ^ (w - 1) * (x : ℂ) ^ j := by
    rw [show (w + j) - 1 = (w - 1) + (j : ℂ) by ring, Complex.cpow_add _ _ hxc,
      Complex.cpow_natCast]
  have h3 : (1 - (x : ℂ)) ^ (((L : ℂ) - w) - 1) =
      ((1 - x : ℝ) : ℂ) ^ (1 - w) * ((1 - x : ℝ) : ℂ) ^ (L - 2) := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      show ((L : ℂ) - w) - 1 = (1 - w) + ((L - 2 : ℕ) : ℂ) by
        rw [Nat.cast_sub hL]; push_cast; ring,
      Complex.cpow_add _ _ hbc, Complex.cpow_natCast]
  unfold fj φ
  rw [h2, h3, h1, Complex.real_smul, smul_eq_mul]
  have h4 : ((|1 / (1 - x) ^ 2| : ℝ) : ℂ) * (((x / (1 - x)) ^ j / (1 + x / (1 - x)) ^ (L + j) : ℝ) : ℂ) =
      (x : ℂ) ^ j * ((1 - x : ℝ) : ℂ) ^ (L - 2) := by
    rw [← Complex.ofReal_mul, hreal]
    push_cast
    ring
  rw [show ((|1 / (1 - x) ^ 2| : ℝ) : ℂ) * ((x : ℂ) ^ (w - 1) * ((1 - x : ℝ) : ℂ) ^ (1 - w) *
      (((x / (1 - x)) ^ j / (1 + x / (1 - x)) ^ (L + j) : ℝ) : ℂ)) =
      (x : ℂ) ^ (w - 1) * ((1 - x : ℝ) : ℂ) ^ (1 - w) *
        (((|1 / (1 - x) ^ 2| : ℝ) : ℂ) *
          (((x / (1 - x)) ^ j / (1 + x / (1 - x)) ^ (L + j) : ℝ) : ℂ)) by ring, h4]
  ring

/-- **The Mellin transform** of `u^j (1+u)^{-L-j}` for `0 < Re w < L`. -/
theorem mellin_fj (L j : ℕ) (hL : 2 ≤ L) (w : ℂ) (h0 : 0 < w.re) (h1 : w.re < L) :
    MellinConvergent (fj L j) w ∧
      mellin (fj L j) w = Complex.Gamma (w + j) * Complex.Gamma (L - w) / Complex.Gamma (L + j) := by
  have hu : 0 < (w + j).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have hv : 0 < ((L : ℂ) - w).re := by
    rw [Complex.sub_re, Complex.natCast_re]
    linarith
  have hB := Complex.betaIntegral_convergent hu hv
  have hBo : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((w + j) - 1) * (1 - (x : ℂ)) ^ (((L : ℂ) - w) - 1))
      (Ioo 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hB).mono_set
      Ioo_subset_Ioc_self
  have heq : EqOn (fun x => |1 / (1 - x) ^ 2| • (((φ x : ℝ) : ℂ) ^ (w - 1) • fj L j (φ x)))
      (fun x : ℝ => (x : ℂ) ^ ((w + j) - 1) * (1 - (x : ℂ)) ^ (((L : ℂ) - w) - 1)) (Ioo 0 1) :=
    fun x hx => fj_beta L j hL w x hx
  constructor
  · unfold MellinConvergent
    rw [← phi_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      phi_deriv phi_inj]
    exact hBo.congr_fun heq.symm measurableSet_Ioo
  · unfold mellin
    rw [← phi_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo phi_deriv phi_inj,
      setIntegral_congr_fun measurableSet_Ioo heq, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
    rw [show w + (j : ℂ) + ((L : ℂ) - w) = (L : ℂ) + j by ring] at hG
    have hne : Complex.Gamma ((L : ℂ) + j) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.add_re, Complex.natCast_re, Complex.natCast_re]
      positivity)
    rw [eq_div_iff hne, hG, mul_comm]
    rfl

theorem fj_continuousAt (L j : ℕ) (x : ℝ) (hx : 0 < x) : ContinuousAt (fj L j) x := by
  unfold fj
  refine Complex.continuous_ofReal.continuousAt.comp ?_
  exact ((continuous_pow j).continuousAt).div
    ((continuous_const.add continuous_id).pow (L + j)).continuousAt (by positivity)

end Pfq54.MG
