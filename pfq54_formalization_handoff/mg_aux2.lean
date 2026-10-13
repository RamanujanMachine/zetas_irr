/-
# Decay of `Γ(w+j) Γ(L-w)` on the line `Re w = 1/2` (sorry-free)

By the reflection formula `|Γ(w)Γ(1-w)| = π / cosh(π Im w)`, and the shifts are polynomial.
-/
import Mathlib

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

/-- The line `w = 1/2 + iy`. -/
def wl (y : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + y * Complex.I

theorem wl_re (y : ℝ) : (wl y).re = 1 / 2 := by
  unfold wl
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem wl_im (y : ℝ) : (wl y).im = y := by
  unfold wl
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem Gamma_add_nat (z : ℂ) (hz : 0 < z.re) (m : ℕ) :
    Complex.Gamma (z + m) = (∏ i ∈ Finset.range m, (z + i)) * Complex.Gamma z := by
  induction m with
  | zero => rw [Nat.cast_zero, add_zero, Finset.prod_range_zero, one_mul]
  | succ m ih =>
    have hne : z + m ≠ 0 := fun h => by
      have := congrArg Complex.re h
      rw [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih, Finset.prod_range_succ]
    ring

theorem norm_prod_le (z : ℂ) (m : ℕ) (c : ℝ) (hc : ∀ i < m, ‖z + i‖ ≤ c) :
    ‖∏ i ∈ Finset.range m, (z + i)‖ ≤ c ^ m := by
  rw [norm_prod]
  calc ∏ i ∈ Finset.range m, ‖z + i‖ ≤ ∏ _i ∈ Finset.range m, c :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi => hc i (Finset.mem_range.mp hi)
    _ = c ^ m := by rw [Finset.prod_const, Finset.card_range]

theorem reflect_norm (y : ℝ) :
    ‖Complex.Gamma (wl y) * Complex.Gamma (1 - wl y)‖ = Real.pi / Real.cosh (Real.pi * y) := by
  rw [Complex.Gamma_mul_Gamma_one_sub]
  have hs : Complex.sin (Real.pi * wl y) = ((Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
    unfold wl
    rw [mul_add, Complex.sin_add, show (Real.pi : ℂ) * ((1 / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_two,
      Real.cos_pi_div_two, show (Real.pi : ℂ) * (y * Complex.I) = ((Real.pi * y : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.cos_mul_I, Complex.ofReal_cosh]
    push_cast
    ring
  rw [hs, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos (Real.cosh_pos _)]

theorem cosh_bound (N : ℕ) (c : ℝ) (hc : 1 ≤ c) :
    ∃ K : ℝ, ∀ y : ℝ, (|y| + c) ^ N * (1 + y ^ 2) ≤ K * Real.cosh (Real.pi * y) := by
  set M := N + 2
  refine ⟨2 ^ M * (2 * M.factorial / Real.pi ^ M + c ^ M), fun y => ?_⟩
  have hy := abs_nonneg y
  have hch : Real.exp (Real.pi * |y|) ≤ 2 * Real.cosh (Real.pi * y) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * |y|))]
  have h1 : |y| ^ M ≤ 2 * M.factorial / Real.pi ^ M * Real.cosh (Real.pi * y) := by
    have := Real.pow_div_factorial_le_exp _ (mul_nonneg Real.pi_pos.le hy) M
    rw [mul_pow, div_le_iff₀ (by positivity)] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, pow_pos Real.pi_pos M]
  have h2 : (|y| + c) ^ M ≤ 2 ^ M * (|y| ^ M + c ^ M) := by
    rcases le_total |y| c with h | h
    · calc (|y| + c) ^ M ≤ (2 * c) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
        _ = 2 ^ M * c ^ M := mul_pow 2 c M
        _ ≤ _ := by gcongr; linarith [pow_nonneg hy M]
    · calc (|y| + c) ^ M ≤ (2 * |y|) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
        _ = 2 ^ M * |y| ^ M := mul_pow 2 |y| M
        _ ≤ _ := by gcongr; linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ c) M]
  have h3 : (|y| + c) ^ N * (1 + y ^ 2) ≤ (|y| + c) ^ M := by
    rw [show M = N + 2 from rfl, pow_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [sq_abs y]
  have hc1 : c ^ M ≤ c ^ M * Real.cosh (Real.pi * y) :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_cosh _)
  calc (|y| + c) ^ N * (1 + y ^ 2) ≤ 2 ^ M * (|y| ^ M + c ^ M) := h3.trans h2
    _ ≤ 2 ^ M * (2 * M.factorial / Real.pi ^ M * Real.cosh (Real.pi * y) +
        c ^ M * Real.cosh (Real.pi * y)) := by gcongr
    _ = _ := by ring

/-- `‖Γ(w+j) Γ(L-w)‖ ≤ K / (1 + y²)` on the line. -/
theorem gamma_line_bound (L j : ℕ) (hL : 1 ≤ L) :
    ∃ K : ℝ, ∀ y : ℝ, ‖Complex.Gamma (wl y + j) * Complex.Gamma (L - wl y)‖ ≤ K * (1 + y ^ 2)⁻¹ := by
  obtain ⟨K, hK⟩ := cosh_bound (j + (L - 1)) ((L : ℝ) + j) (by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  refine ⟨Real.pi * K, fun y => ?_⟩
  have hw : 0 < (wl y).re := by rw [wl_re]; norm_num
  have hw1 : 0 < (1 - wl y).re := by rw [Complex.sub_re, Complex.one_re, wl_re]; norm_num
  have hcj : ∀ i < j, ‖wl y + i‖ ≤ |y| + ((L : ℝ) + j) := fun i hi => by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.add_re, Complex.add_im, wl_re, wl_im, Complex.natCast_re, Complex.natCast_im,
      add_zero, abs_of_pos (by positivity)]
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hi
    linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hcL : ∀ i < L - 1, ‖(1 - wl y) + i‖ ≤ |y| + ((L : ℝ) + j) := fun i hi => by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, wl_re, wl_im, Complex.natCast_re, Complex.natCast_im, add_zero, zero_sub,
      abs_neg, abs_of_pos (by positivity)]
    have : (i : ℝ) + 1 ≤ L := by exact_mod_cast (by omega : i + 1 ≤ L)
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have eL : (L : ℂ) - wl y = (1 - wl y) + ((L - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hL]
    push_cast
    ring
  rw [Gamma_add_nat _ hw, eL, Gamma_add_nat _ hw1,
    show (∏ i ∈ Finset.range j, (wl y + i)) * Complex.Gamma (wl y) *
      ((∏ i ∈ Finset.range (L - 1), (1 - wl y + i)) * Complex.Gamma (1 - wl y)) =
      (∏ i ∈ Finset.range j, (wl y + i)) * (∏ i ∈ Finset.range (L - 1), (1 - wl y + i)) *
        (Complex.Gamma (wl y) * Complex.Gamma (1 - wl y)) by ring,
    norm_mul, norm_mul, reflect_norm]
  have hp1 := norm_prod_le _ j _ hcj
  have hp2 := norm_prod_le _ (L - 1) _ hcL
  have hcos := Real.cosh_pos (Real.pi * y)
  have hK' := hK y
  rw [pow_add] at hK'
  have h0 : 0 ≤ |y| + ((L : ℝ) + j) := by positivity
  calc ‖∏ i ∈ Finset.range j, (wl y + i)‖ * ‖∏ i ∈ Finset.range (L - 1), (1 - wl y + i)‖ *
        (Real.pi / Real.cosh (Real.pi * y))
      ≤ (|y| + ((L : ℝ) + j)) ^ j * (|y| + ((L : ℝ) + j)) ^ (L - 1) *
        (Real.pi / Real.cosh (Real.pi * y)) := by gcongr
    _ ≤ Real.pi * K * (1 + y ^ 2)⁻¹ := by
      rw [div_eq_mul_inv, le_mul_inv_iff₀ (by positivity)]
      calc _ = Real.pi * (((|y| + ((L : ℝ) + j)) ^ j * (|y| + ((L : ℝ) + j)) ^ (L - 1)) *
            (1 + y ^ 2)) * (Real.cosh (Real.pi * y))⁻¹ := by ring
        _ ≤ Real.pi * (K * Real.cosh (Real.pi * y)) * (Real.cosh (Real.pi * y))⁻¹ := by gcongr
        _ = Real.pi * K := by field_simp

theorem gamma_line_continuous (L j : ℕ) (hL : 1 ≤ L) :
    Continuous fun y : ℝ => Complex.Gamma (wl y + j) * Complex.Gamma (L - wl y) := by
  have hwl : Continuous wl := by unfold wl; fun_prop
  have hnp : ∀ s : ℂ, 0 < s.re → ∀ m : ℕ, s ≠ -m := fun s hs m h => by
    rw [h, Complex.neg_re, Complex.natCast_re] at hs
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  refine continuous_iff_continuousAt.mpr fun y => ContinuousAt.mul ?_ ?_
  · refine ((Complex.differentiableAt_Gamma _ (hnp _ ?_)).continuousAt).comp
      ((hwl.add continuous_const).continuousAt)
    rw [Complex.add_re, wl_re, Complex.natCast_re]
    positivity
  · refine ((Complex.differentiableAt_Gamma _ (hnp _ ?_)).continuousAt).comp
      ((continuous_const.sub hwl).continuousAt)
    rw [Complex.sub_re, wl_re, Complex.natCast_re]
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith

theorem gamma_line_integrable (L j : ℕ) (hL : 1 ≤ L) :
    Integrable fun y : ℝ => Complex.Gamma (wl y + j) * Complex.Gamma (L - wl y) := by
  obtain ⟨K, hK⟩ := gamma_line_bound L j hL
  have hi : Integrable fun y : ℝ => K * (1 + y ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul K
  exact hi.mono' (gamma_line_continuous L j hL).aestronglyMeasurable
    (Eventually.of_forall fun y => hK y)

end Pfq54.MG
