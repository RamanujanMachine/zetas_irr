/-
# Blueprint of `meijerG_initial` (manuscript Proposition `z34-initial-values`)

Node `Pfq54.meijerG_initial` of `Blueprint_pfq54.lean`:
`𝒮_G(0) = (1 - 2ζ(3) + 3ζ(4), 1 - 2ζ(3), 1, 1 - ζ(2))`.

Proof (manuscript Appendix A): at `n = 0` the reflection formula turns the Mellin–Barnes
integrand into `π² / (sin²(πs) s³ (s+1))` ([1]). For `k ≤ 3` the integrals of
`(-s)^k · integrand` converge absolutely ([2]); closing the contour to the right along the lines
`Re s = m + 1/2` (whose integrals tend to `0`, [3]) picks up the double poles at the positive
integers, so `(θ^k 𝒢₀)(1) = (-1)^{k+1} ∑_{ℓ ≥ 1} [d/ds 1/(s^{3-k}(s+1))]_{s=ℓ}` ([4]). Partial
fractions evaluate the four series ([5]).
-/
import Pfq54_aux
import mi_aux

open Finset Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- `-[d/ds 1/(s^{3-k}(s+1))]_{s=ℓ} = (3-k)/(ℓ^{4-k}(ℓ+1)) + 1/(ℓ^{3-k}(ℓ+1)²)`. -/
def resTerm (k : ℕ) (ℓ : ℂ) : ℂ :=
  ((3 - k : ℕ) : ℂ) / (ℓ ^ (4 - k) * (ℓ + 1)) + 1 / (ℓ ^ (3 - k) * (ℓ + 1) ^ 2)

/-- **[1] The integrand at `n = 0`**: `Γ(1-s)² Γ(s)⁵ / (Γ(s+1)² Γ(s+2)) = π²/(sin²(πs) s³ (s+1))`
away from the integers (reflection `Γ(s)Γ(1-s) = π/sin(πs)`, `Γ(s+1) = sΓ(s)`).
* Estimated proof length: ≈ 25 lines (`Complex.Gamma_mul_Gamma_one_sub`, `Complex.Gamma_add_one`).
* Directly from the manuscript: yes. -/
theorem mbIntegrand_zero (s : ℂ) (hs : ∀ m : ℤ, s ≠ m) :
    mbIntegrand 0 s = (Real.pi : ℂ) ^ 2 / (Complex.sin (Real.pi * s) ^ 2 * s ^ 3 * (s + 1)) := by
  have hs0 : s ≠ 0 := fun h => hs 0 (by rw [h, Int.cast_zero])
  have hs1 : s + 1 ≠ 0 := fun h => hs (-1) (by push_cast; linear_combination h)
  have hΓ : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero fun m hm => hs (-m) (by push_cast; exact hm)
  have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact hs k (mul_left_cancel₀ hpi (by rw [hk]; ring))
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hcard : (Icc (-2 : ℤ) 2).card = 5 := by rw [Int.card_Icc]; rfl
  unfold mbIntegrand
  simp only [Nat.cast_zero, mul_zero, zero_add, add_zero, Finset.prod_const, hcard]
  rw [show s + 2 = (s + 1) + 1 by ring, Complex.Gamma_add_one _ hs1,
    Complex.Gamma_add_one _ hs0,
    show (Real.pi : ℂ) ^ 2 / (Complex.sin (Real.pi * s) ^ 2 * s ^ 3 * (s + 1)) =
      ((Real.pi : ℂ) / Complex.sin (Real.pi * s)) ^ 2 / (s ^ 3 * (s + 1)) by field_simp, ← hrefl]
  field_simp

/-- Closed form of the integrand on the line `Re s = m + 1/2`. -/
theorem line_integrand_eq (k m : ℕ) (y : ℝ) :
    (-((m : ℂ) + 1 / 2 + y * Complex.I)) ^ k * mbIntegrand 0 ((m : ℂ) + 1 / 2 + y * Complex.I) =
      (-((m : ℂ) + 1 / 2 + y * Complex.I)) ^ k * ((Real.pi : ℂ) ^ 2 /
        (((Real.cosh (Real.pi * y) : ℝ) : ℂ) ^ 2 * ((m : ℂ) + 1 / 2 + y * Complex.I) ^ 3 *
          ((m : ℂ) + 1 / 2 + y * Complex.I + 1))) := by
  set s : ℂ := (m : ℂ) + 1 / 2 + y * Complex.I with hs
  have hre : s.re = m + 1 / 2 := by simp [hs]
  have hnot : ∀ j : ℤ, s ≠ j := by
    intro j h
    have := congrArg Complex.re h
    rw [hre, Complex.intCast_re] at this
    have h2 : ((2 * (m : ℤ) + 1 : ℤ) : ℝ) = ((2 * j : ℤ) : ℝ) := by push_cast; linarith
    have h3 : (2 * (m : ℤ) + 1 : ℤ) = 2 * j := by exact_mod_cast h2
    omega
  have hsin : Complex.sin (Real.pi * s) ^ 2 = ((Real.cosh (Real.pi * y) : ℝ) : ℂ) ^ 2 := by
    rw [show (Real.pi : ℂ) * s = (Real.pi / 2 + ((Real.pi * y : ℝ) : ℂ) * Complex.I) +
        m * Real.pi by rw [hs]; push_cast; ring, Aux.sin_sq_add_nat_mul_pi, Complex.sin_add,
      Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
    ring
  rw [mbIntegrand_zero s hnot, hsin]

/-- Pointwise bound on the line `Re s = m + 1/2`. -/
theorem line_integrand_bound (k : ℕ) (hk : k ≤ 3) (m : ℕ) (y : ℝ) :
    ‖(-((m : ℂ) + 1 / 2 + y * Complex.I)) ^ k * mbIntegrand 0 ((m : ℂ) + 1 / 2 + y * Complex.I)‖ ≤
      8 * Real.pi ^ 2 / ((m : ℝ) + 1) * (1 + (Real.pi * y) ^ 2)⁻¹ := by
  rw [line_integrand_eq]
  set s : ℂ := (m : ℂ) + 1 / 2 + y * Complex.I with hs
  have hre : s.re = m + 1 / 2 := by simp [hs]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hns : 1 / 2 ≤ ‖s‖ := by have := Complex.re_le_norm s; rw [hre] at this; linarith
  have hns1 : (m : ℝ) + 1 ≤ ‖s + 1‖ := by
    have := Complex.re_le_norm (s + 1)
    rw [Complex.add_re, hre, Complex.one_re] at this
    linarith
  have hc := Aux.one_add_sq_le_cosh_sq (Real.pi * y)
  have hcpos : 0 < Real.cosh (Real.pi * y) := Real.cosh_pos _
  have hx0 : 0 < ‖s‖ := by linarith
  have hxk := Aux.pow_div_cube_le ‖s‖ hns k hk
  have hz : 1 / ‖s + 1‖ ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hns1
  have hcc : 1 / Real.cosh (Real.pi * y) ^ 2 ≤ (1 + (Real.pi * y) ^ 2)⁻¹ := by
    rw [one_div]; exact inv_anti₀ (by positivity) hc
  have hz0 : 0 < ‖s + 1‖ := by linarith
  rw [norm_mul, norm_pow, norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos hcpos]
  calc ‖s‖ ^ k * (Real.pi ^ 2 / (Real.cosh (Real.pi * y) ^ 2 * ‖s‖ ^ 3 * ‖s + 1‖))
      = Real.pi ^ 2 * (‖s‖ ^ k / ‖s‖ ^ 3) * (1 / ‖s + 1‖) *
          (1 / Real.cosh (Real.pi * y) ^ 2) := by field_simp
    _ ≤ Real.pi ^ 2 * 8 * (1 / ((m : ℝ) + 1)) * (1 + (Real.pi * y) ^ 2)⁻¹ := by
        gcongr
    _ = _ := by ring

/-- Continuity on the line `Re s = m + 1/2`. -/
theorem line_integrand_continuous (k m : ℕ) :
    Continuous (fun y : ℝ => (-((m : ℂ) + 1 / 2 + y * Complex.I)) ^ k *
      mbIntegrand 0 ((m : ℂ) + 1 / 2 + y * Complex.I)) := by
  simp_rw [line_integrand_eq]
  refine Continuous.mul (by fun_prop) (continuous_const.div (by fun_prop) fun y => ?_)
  have hre : ((m : ℂ) + 1 / 2 + y * Complex.I).re = m + 1 / 2 := by simp
  have h1 : (m : ℂ) + 1 / 2 + y * Complex.I ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hre; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h2 : (m : ℂ) + 1 / 2 + y * Complex.I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.add_re, hre, Complex.one_re, Complex.zero_re] at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h3 : ((Real.cosh (Real.pi * y) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h1)) h2

/-- **[2] Absolute convergence on the contour** `Re s = 1/2` for `k ≤ 3`
(`|sin(π(1/2 + iy))|² ≥ cosh²(πy)`, the integrand is `O(|y|^{k-4} e^{-2π|y|})`).
* Estimated proof length: ≈ 30 lines.
* Directly from the manuscript: yes. -/
theorem mb_integrable (k : ℕ) (hk : k ≤ 3) :
    Integrable (fun y : ℝ => (-mbContour 0 y) ^ k * mbIntegrand 0 (mbContour 0 y)) := by
  have hfun : (fun y : ℝ => (-mbContour 0 y) ^ k * mbIntegrand 0 (mbContour 0 y)) =
      fun y : ℝ => (-(((0 : ℕ) : ℂ) + 1 / 2 + y * Complex.I)) ^ k *
        mbIntegrand 0 (((0 : ℕ) : ℂ) + 1 / 2 + y * Complex.I) := by
    funext y
    simp only [mbContour, Nat.cast_zero, mul_zero, zero_add]
  rw [hfun]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  exact Integrable.mono' ((integrable_inv_one_add_sq.comp_mul_left' hpi).const_mul
      (8 * Real.pi ^ 2 / (((0 : ℕ) : ℝ) + 1)))
    (line_integrand_continuous k 0).aestronglyMeasurable
    (Eventually.of_forall fun y => line_integrand_bound k hk 0 y)

/-- **[3] The shifted vertical lines vanish**: the integrals over `Re s = m + 1/2` tend to `0`
as `m → ∞` (they are `O(m^{k-4})`), and the horizontal connecting integrals vanish by the
exponential decay of `1/sin²`.
* Estimated proof length: ≈ 60 lines.
* Directly from the manuscript: yes. -/
theorem shifted_contour_vanish (k : ℕ) (hk : k ≤ 3) :
    Tendsto (fun m : ℕ => ∫ y : ℝ, (-((m : ℂ) + 1 / 2 + y * Complex.I)) ^ k *
      mbIntegrand 0 ((m : ℂ) + 1 / 2 + y * Complex.I)) atTop (𝓝 0) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hint : Integrable (fun y : ℝ => (1 + (Real.pi * y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hpi
  set J := ∫ y : ℝ, (1 + (Real.pi * y) ^ 2)⁻¹
  have hbound : ∀ m : ℕ, ‖∫ y : ℝ, (-((m : ℂ) + 1 / 2 + y * Complex.I)) ^ k *
      mbIntegrand 0 ((m : ℂ) + 1 / 2 + y * Complex.I)‖ ≤ 8 * Real.pi ^ 2 / ((m : ℝ) + 1) * J :=
    fun m => (norm_integral_le_of_norm_le (hint.const_mul _)
      (Eventually.of_forall fun y => line_integrand_bound k hk m y)).trans
        (le_of_eq (integral_const_mul _ _))
  refine squeeze_zero_norm hbound ?_
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (8 * Real.pi ^ 2 * J)
  rw [mul_zero] at h
  exact h.congr fun m => by ring

/-- **[4] Closing the contour to the right**: `(θ^k 𝒢₀)(1) = (-1)^k ∑_{ℓ ≥ 1} resTerm k ℓ`
(double poles at the positive integers, clockwise orientation).
* Uses: [1], [2], [3]; the residue of `π²/sin²(πs) · h(s)` at `ℓ` is `h'(ℓ)`.
* Estimated proof length: ≈ 200 lines (Mathlib has Cauchy's theorem on rectangles,
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, but no residue theorem: the
  double-pole contributions must be extracted by hand).
* Directly from the manuscript: partially (contour closing and residues are only sketched). -/
theorem contour_residue_sum (k : ℕ) (hk : k ≤ 3) :
    SG 0 k = (-1) ^ k * ∑' ℓ : ℕ, resTerm k ((ℓ : ℂ) + 1) := by
  have hFc : ∀ (j : ℕ) (y : ℝ), (-((j : ℂ) + 1 / 2 + y * Complex.I)) ^ k *
      mbIntegrand 0 ((j : ℂ) + 1 / 2 + y * Complex.I) =
        MI.Fc k ((j : ℂ) + 1 / 2 + y * Complex.I) := by
    intro j y
    rw [mbIntegrand_zero _ (MI.not_int_of_re_half _ j (by simp))]
    unfold MI.Fc MI.hh
    rw [div_mul_div_comm, ← mul_div_assoc, mul_comm ((-((j : ℂ) + 1 / 2 + y * Complex.I)) ^ k),
      mul_assoc]
  have hint : ∀ j : ℕ, Integrable (fun y : ℝ => MI.Fc k ((j : ℂ) + 1 / 2 + y * Complex.I)) := by
    intro j
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    exact (Integrable.mono' ((integrable_inv_one_add_sq.comp_mul_left' hpi).const_mul
      (8 * Real.pi ^ 2 / ((j : ℝ) + 1))) (line_integrand_continuous k j).aestronglyMeasurable
      (Eventually.of_forall fun y => line_integrand_bound k hk j y)).congr
      (Eventually.of_forall fun y => hFc j y)
  have hvan : Tendsto (fun j : ℕ => ∫ y : ℝ, MI.Fc k ((j : ℂ) + 1 / 2 + y * Complex.I)) atTop
      (𝓝 0) := by
    refine (shifted_contour_vanish k hk).congr fun j => ?_
    exact integral_congr_ae (Eventually.of_forall fun y => hFc j y)
  have hSG : SG 0 k = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ y : ℝ, MI.Fc k (((0 : ℕ) : ℂ) + 1 / 2 + y * Complex.I) := by
    unfold SG
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [← hFc 0 y]
    simp only [mbContour, Nat.cast_zero, mul_zero, zero_add]
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [hSG, MI.main k hk hint hvan]
  change _ = (-1) ^ k * ∑' ℓ : ℕ, MI.resT k ((ℓ : ℂ) + 1)
  push_cast at hpi ⊢
  field_simp

/-- **[5] The four residue series** (partial fractions, `∑_{ℓ ≥ 1} ℓ^{-s} = ζ(s)`, telescoping):
`∑ resTerm 0 = 1 - 2ζ(3) + 3ζ(4)`, `∑ resTerm 1 = 2ζ(3) - 1`, `∑ resTerm 2 = 1`,
`∑ resTerm 3 = ζ(2) - 1`.
* Estimated proof length: ≈ 60 lines (`zeta_nat_eq_tsum_of_gt_one`, `tsum_sub`, telescoping
  `∑ (1/ℓ² - 1/(ℓ+1)²) = 1`).
* Directly from the manuscript: yes ("Partial fractions give …"). -/
theorem residue_series :
    ∑' ℓ : ℕ, resTerm 0 ((ℓ : ℂ) + 1) = 1 - 2 * riemannZeta 3 + 3 * riemannZeta 4 ∧
      ∑' ℓ : ℕ, resTerm 1 ((ℓ : ℂ) + 1) = 2 * riemannZeta 3 - 1 ∧
      ∑' ℓ : ℕ, resTerm 2 ((ℓ : ℂ) + 1) = 1 ∧
      ∑' ℓ : ℕ, resTerm 3 ((ℓ : ℂ) + 1) = riemannZeta 2 - 1 := by
  have hz : ∀ m : ℕ, 1 < m → HasSum (fun n : ℕ => 1 / (n : ℂ) ^ m) (riemannZeta m) := by
    intro m hm
    rw [zeta_nat_eq_tsum_of_gt_one hm]
    have h := (Complex.summable_one_div_nat_cpow (p := (m : ℂ))).mpr
      (by rw [Complex.natCast_re]; exact_mod_cast hm)
    simp only [Complex.cpow_natCast] at h
    exact h.hasSum
  have ha : ∀ m : ℕ, 1 < m →
      HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℂ) + 1) ^ m) (riemannZeta m) := by
    intro m hm
    have h := (hasSum_nat_add_iff' 1).mpr (hz m hm)
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
      zero_pow (by omega : m ≠ 0), div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
    exact h
  have hb : HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℂ) + 2) ^ 2) (riemannZeta 2 - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr (ha 2 (by norm_num))
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, one_pow,
      div_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
    convert h using 3
    ring
  have h2 := ha 2 (by norm_num)
  have h3 := ha 3 (by norm_num)
  have h4 := ha 4 (by norm_num)
  simp only [Nat.cast_ofNat] at h2 h3 h4
  have hne : ∀ ℓ : ℕ, ((ℓ : ℂ) + 1) ≠ 0 ∧ ((ℓ : ℂ) + 1 + 1) ≠ 0 ∧ ((ℓ : ℂ) + 2) ≠ 0 := fun ℓ =>
    ⟨Nat.cast_add_one_ne_zero ℓ, by exact_mod_cast Nat.succ_ne_zero (ℓ + 1),
      by exact_mod_cast Nat.succ_ne_zero (ℓ + 1)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tsum_congr (g := fun ℓ : ℕ => 3 * (1 / ((ℓ : ℂ) + 1) ^ 4) - 2 * (1 / ((ℓ : ℂ) + 1) ^ 3) +
        1 / ((ℓ : ℂ) + 1) ^ 2 - 1 / ((ℓ : ℂ) + 2) ^ 2) (fun ℓ => by
        obtain ⟨e1, e2, e3⟩ := hne ℓ
        unfold resTerm; push_cast; field_simp; ring),
      (((h4.mul_left 3).sub (h3.mul_left 2)).add h2).sub hb |>.tsum_eq]
    ring
  · rw [tsum_congr (g := fun ℓ : ℕ => 2 * (1 / ((ℓ : ℂ) + 1) ^ 3) - 1 / ((ℓ : ℂ) + 1) ^ 2 +
        1 / ((ℓ : ℂ) + 2) ^ 2) (fun ℓ => by
        obtain ⟨e1, e2, e3⟩ := hne ℓ
        unfold resTerm; push_cast; field_simp; ring),
      ((h3.mul_left 2).sub h2).add hb |>.tsum_eq]
    ring
  · rw [tsum_congr (g := fun ℓ : ℕ => 1 / ((ℓ : ℂ) + 1) ^ 2 - 1 / ((ℓ : ℂ) + 2) ^ 2) (fun ℓ => by
        obtain ⟨e1, e2, e3⟩ := hne ℓ
        unfold resTerm; push_cast; field_simp; ring),
      h2.sub hb |>.tsum_eq]
    ring
  · rw [tsum_congr (g := fun ℓ : ℕ => 1 / ((ℓ : ℂ) + 2) ^ 2) (fun ℓ => by
        obtain ⟨e1, e2, e3⟩ := hne ℓ
        unfold resTerm; push_cast; field_simp; ring),
      hb.tsum_eq]

/-- **`meijerG_initial`** (node of `Blueprint_pfq54.lean`). Proved from [4] and [5]. -/
theorem meijerG_initial :
    SG 0 0 = 1 - 2 * riemannZeta 3 + 3 * riemannZeta 4 ∧ SG 0 1 = 1 - 2 * riemannZeta 3 ∧
      SG 0 2 = 1 ∧ SG 0 3 = 1 - riemannZeta 2 := by
  obtain ⟨r0, r1, r2, r3⟩ := residue_series
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [contour_residue_sum 0 (by norm_num), r0]; ring
  · rw [contour_residue_sum 1 (by norm_num), r1]; ring
  · rw [contour_residue_sum 2 (by norm_num), r2]; ring
  · rw [contour_residue_sum 3 (by norm_num), r3]; ring

end Pfq54.BP
