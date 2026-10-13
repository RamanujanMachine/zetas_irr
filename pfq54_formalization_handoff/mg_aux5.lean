/-
# The representation by the positive integral (sorry-free)

`(1/2π) ∫ Γ(w+j) Γ(L-w) (∫_{(0,1)⁴} beta integrands) dy = Γ(L+j) ∫_{(0,1)⁴} P q^j`,
`L = 14n+1` (Fubini, then Mellin inversion at `u = (1-r)/(xytr)`).
-/
import mg_aux4

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

theorem bprod_measurable (n : ℕ) :
    Measurable fun p : ℝ × (ℝ × ℝ × ℝ × ℝ) => bprod n (wl p.1) p.2 := by
  unfold bprod bint wl
  fun_prop

theorem bprod_le (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (z : ℝ × ℝ × ℝ × ℝ) (hz : z ∈ cube) :
    ‖bprod n (wl y) z‖ ≤ 1 := by
  obtain ⟨hx, hy, ht, hr⟩ := hz
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have r1 : ∀ c : ℕ, 1 ≤ c → 0 ≤ (wl y + (c : ℂ) - 1).re := fun c hc => by
    rw [Complex.sub_re, Complex.add_re, wl_re, Complex.natCast_re, Complex.one_re]
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  have r2 : ∀ c : ℕ, 1 ≤ c → 0 ≤ ((c : ℂ) - 1).re := fun c hc => by
    rw [Complex.sub_re, Complex.natCast_re, Complex.one_re]
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  have r3 : 0 ≤ (((15 * n + 1 : ℕ) : ℂ) - wl y - 1).re := by
    rw [Complex.sub_re, Complex.sub_re, wl_re, Complex.natCast_re, Complex.one_re]
    push_cast
    linarith
  unfold bprod
  rw [norm_mul, norm_mul, norm_mul]
  have b1 := bint_le _ _ _ hx (r1 (2 * n) (by omega)) (r2 (11 * n + 1) (by omega))
  have b2 := bint_le _ _ _ hy (r1 (3 * n) (by omega)) (r2 (11 * n + 1) (by omega))
  have b3 := bint_le _ _ _ ht (r1 (4 * n) (by omega)) (r2 (8 * n + 2) (by omega))
  have b4 := bint_le _ _ _ hr (r1 n hn) r3
  have le1 : ∀ a b : ℝ, a ≤ 1 → b ≤ 1 → 0 ≤ b → a * b ≤ 1 := fun a b ha hb hb0 =>
    (mul_le_mul ha hb hb0 zero_le_one).trans_eq (one_mul 1)
  exact le1 _ _ b1 (le1 _ _ b2 (le1 _ _ b3 b4 (norm_nonneg _)) (by positivity)) (by positivity)

/-- **The representation.** -/
theorem rep_j (n j : ℕ) (hn : 1 ≤ n) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, Complex.Gamma (wl y + j) *
        Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - wl y) * ∫ z, bprod n (wl y) z ∂μ4 =
      Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) + j) *
        ((∫ z, Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j ∂μ4 : ℝ) : ℂ) := by
  set A : ℝ → ℂ := fun y => Complex.Gamma (wl y + j) * Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - wl y)
  have hAi : Integrable A := gamma_line_integrable (14 * n + 1) j (by omega)
  have hAc : Continuous A := gamma_line_continuous (14 * n + 1) j (by omega)
  have hmeas : Measurable (fun p : ℝ × (ℝ × ℝ × ℝ × ℝ) => A p.1 * bprod n (wl p.1) p.2) :=
    (hAc.measurable.comp measurable_fst).mul (bprod_measurable n)
  have hm : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ × ℝ × ℝ) => A p.1 * bprod n (wl p.1) p.2)
      (volume.prod μ4) := hmeas.aestronglyMeasurable
  have hb : ∀ y : ℝ, ∀ᵐ z ∂μ4, ‖A y * bprod n (wl y) z‖ ≤ ‖A y‖ := fun y =>
    ae_cube.mono fun z hz => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (bprod_le n hn y z hz))
  have hsec : ∀ y : ℝ, Integrable (fun z => A y * bprod n (wl y) z) μ4 := fun y =>
    (integrable_const ‖A y‖).mono' (hmeas.comp measurable_prodMk_left).aestronglyMeasurable (hb y)
  have hint : Integrable (fun p : ℝ × (ℝ × ℝ × ℝ × ℝ) => A p.1 * bprod n (wl p.1) p.2)
      (volume.prod μ4) := by
    refine (integrable_prod_iff hm).mpr ⟨Eventually.of_forall hsec, ?_⟩
    refine (hAi.norm.mul_const (μ4.real univ)).mono' hm.norm.integral_prod_right' ?_
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
    calc ∫ z, ‖A y * bprod n (wl y) z‖ ∂μ4 ≤ ∫ _z, ‖A y‖ ∂μ4 :=
          integral_mono_ae (hsec y).norm (integrable_const _) (hb y)
      _ = ‖A y‖ * μ4.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hswap := integral_integral_swap (f := fun y z => A y * bprod n (wl y) z) hint
  have hin : ∀ y : ℝ, A y * ∫ z, bprod n (wl y) z ∂μ4 = ∫ z, A y * bprod n (wl y) z ∂μ4 :=
    fun y => (integral_const_mul _ _).symm
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hpt : ∀ᵐ z ∂μ4, ∫ y, A y * bprod n (wl y) z =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) + j) *
        ((Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j : ℝ) : ℂ) := by
    refine ae_cube.mono fun z hz => ?_
    have hv : 0 < vv z := by
      obtain ⟨⟨hx0, -⟩, ⟨hy0, -⟩, ⟨ht0, -⟩, ⟨hr0, hr1⟩⟩ := hz
      unfold vv
      exact div_pos (by positivity) (sub_pos.mpr hr1)
    have hM := mellin_point (14 * n + 1) j (by omega) (vv z) hv
    have e : ∀ y : ℝ, A y * bprod n (wl y) z = ((gg n z : ℝ) : ℂ) *
        (Complex.Gamma (wl y + j) * Complex.Gamma (((14 * n + 1 : ℕ) : ℂ) - wl y) *
          ((vv z : ℝ) : ℂ) ^ (wl y)) := fun y => by
      rw [bprod_factor n hn (wl y) z hz]
      ring
    rw [integral_congr_ae (Eventually.of_forall e), integral_const_mul,
      ← real_identity n j hn z hz]
    rw [inv_mul_eq_iff_eq_mul₀ h2pi] at hM
    rw [hM]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hin), hswap, integral_congr_ae hpt,
    integral_const_mul, integral_complex_ofReal]
  field_simp

end Pfq54.MG
