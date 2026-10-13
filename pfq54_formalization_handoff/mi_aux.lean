/-
# Contour shifting for `𝒮_G(0)` (sorry-free)

The Mellin–Barnes integrand at `n = 0` is `Fc k s = π²/sin²(πs) · h_k(s)`,
`h_k(s) = (-s)^k/(s³(s+1))`. Moving the vertical line `Re s = j + 1/2` to `Re s = j + 3/2`
across the double pole at `j + 1` picks up `2πi h_k'(j+1)`: Cauchy's theorem on a rectangle for
`Fc k` minus its principal part (Riemann's removable singularity theorem), the explicit rectangle
integrals of `(s-p)⁻²` and `(s-p)⁻¹`, and the exponential decay of `1/sin²` on the horizontal
edges. Telescoping gives `∫_{Re s = 1/2} Fc k = -2π ∑_{m ≥ 1} h_k'(m)`.
-/
import Pfq54_aux

open Filter Topology MeasureTheory Set intervalIntegral
open Complex (I)

noncomputable section

namespace Pfq54.MI

open Pfq54

/-- `h_k(s) = (-s)^k / (s³ (s+1))`. -/
def hh (k : ℕ) (s : ℂ) : ℂ := (-s) ^ k / (s ^ 3 * (s + 1))

/-- The integrand `π²/sin²(πs) · h_k(s)`. -/
def Fc (k : ℕ) (s : ℂ) : ℂ := (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * s) ^ 2 * hh k s

/-- `-[d/ds 1/(s^{3-k}(s+1))]_{s=ℓ}` (the same expression as `Pfq54.BP.resTerm`). -/
def resT (k : ℕ) (ℓ : ℂ) : ℂ :=
  ((3 - k : ℕ) : ℂ) / (ℓ ^ (4 - k) * (ℓ + 1)) + 1 / (ℓ ^ (3 - k) * (ℓ + 1) ^ 2)

/-- The boundary sum of Mathlib's rectangle theorem (counterclockwise). -/
def rectSum (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I)) +
    I • (∫ y in c..d, f (b + y * I)) - I • (∫ y in c..d, f (a + y * I))

/-- The boundary of the rectangle. -/
def onBdry (a b c d : ℝ) (s : ℂ) : Prop := s.im = c ∨ s.im = d ∨ s.re = a ∨ s.re = b

theorem sin_pi_ne_zero (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) : Complex.sin (Real.pi * s) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact hs k (mul_left_cancel₀ hpi (by rw [hk]; ring))

theorem not_int_of_im (s : ℂ) (h : s.im ≠ 0) (j : ℤ) : s ≠ j := by
  intro hj
  apply h
  rw [hj, Complex.intCast_im]

theorem not_int_of_re_half (s : ℂ) (j : ℕ) (h : s.re = j + 1 / 2) (i : ℤ) : s ≠ i := by
  intro hi
  have := congrArg Complex.re hi
  rw [h, Complex.intCast_re] at this
  have h2 : ((2 * (j : ℤ) + 1 : ℤ) : ℝ) = ((2 * i : ℤ) : ℝ) := by push_cast; linarith
  have h3 : (2 * (j : ℤ) + 1 : ℤ) = 2 * i := by exact_mod_cast h2
  omega

theorem not_int_of_re_near (s : ℂ) (j : ℕ) (h1 : (j : ℝ) < s.re) (h2 : s.re < j + 2)
    (hne : s ≠ (j : ℂ) + 1) (i : ℤ) : s ≠ i := by
  intro hi
  have := congrArg Complex.re hi
  rw [Complex.intCast_re] at this
  rw [this] at h1 h2
  have h3 : (j : ℤ) < i := by exact_mod_cast h1
  have h4 : i < (j : ℤ) + 2 := by exact_mod_cast h2
  have h5 : i = (j : ℤ) + 1 := by omega
  apply hne
  rw [hi, h5]
  push_cast
  rfl

theorem Fc_differentiableAt (k : ℕ) (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) :
    DifferentiableAt ℂ (Fc k) s := by
  have hs0 : s ≠ 0 := fun h => hs 0 (by rw [h, Int.cast_zero])
  have hs1 : s + 1 ≠ 0 := fun h => hs (-1) (by push_cast; linear_combination h)
  have hsin : Complex.sin (Real.pi * s) ^ 2 ≠ 0 := pow_ne_zero 2 (sin_pi_ne_zero s hs)
  have hden : s ^ 3 * (s + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 3 hs0) hs1
  unfold Fc hh
  fun_prop (disch := assumption)

theorem hasDerivAt_hh (k : ℕ) (hk : k ≤ 3) (p : ℂ) (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0) :
    HasDerivAt (hh k) (-(-1) ^ k * resT k p) p := by
  have hden : p ^ 3 * (p + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 3 hp0) hp1
  have h := (((hasDerivAt_id p).neg).pow k).div
    (((hasDerivAt_id p).pow 3).mul ((hasDerivAt_id p).add_const 1)) hden
  refine h.congr_deriv ?_
  simp only [id, resT]
  interval_cases k <;> norm_num <;> field_simp <;> ring

/-! ### Segments and primitives -/

theorem seg_h (Φ f : ℂ → ℂ) (a b c : ℝ)
    (hΦ : ∀ x ∈ uIcc a b, HasDerivAt Φ (f (x + c * I)) (x + c * I))
    (hf : ContinuousOn (fun x : ℝ => f (x + c * I)) (uIcc a b)) :
    ∫ x in a..b, f (x + c * I) = Φ (b + c * I) - Φ (a + c * I) := by
  have key : ∫ x in a..b, f (x + c * I) =
      (fun x : ℝ => Φ (x + c * I)) b - (fun x : ℝ => Φ (x + c * I)) a := by
    refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => Φ (x + c * I)) (fun x hx => ?_)
      hf.intervalIntegrable
    have h1 : HasDerivAt (fun w : ℂ => Φ (w + c * I)) (f (x + c * I) * 1) x :=
      (hΦ x hx).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const _)
    exact h1.comp_ofReal.congr_deriv (mul_one _)
  exact key

theorem seg_v (Φ f : ℂ → ℂ) (a c d : ℝ)
    (hΦ : ∀ y ∈ uIcc c d, HasDerivAt Φ (f (a + y * I)) (a + y * I))
    (hf : ContinuousOn (fun y : ℝ => f (a + y * I)) (uIcc c d)) :
    I • ∫ y in c..d, f (a + y * I) = Φ (a + d * I) - Φ (a + c * I) := by
  have h : ∫ y in c..d, I * f (a + y * I) =
      (fun y : ℝ => Φ (a + y * I)) d - (fun y : ℝ => Φ (a + y * I)) c := by
    refine integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Φ (a + y * I)) (fun y hy => ?_)
      (continuousOn_const.mul hf).intervalIntegrable
    have h1 : HasDerivAt (fun w : ℂ => Φ (a + w * I)) (f (a + y * I) * (1 * I)) y :=
      (hΦ y hy).comp (y : ℂ) (((hasDerivAt_id (y : ℂ)).mul_const I).const_add _)
    exact h1.comp_ofReal.congr_deriv (by ring)
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul, h]

theorem bdry_bot (a b c d x : ℝ) : onBdry a b c d ((x : ℂ) + c * I) := by
  left; simp
theorem bdry_top (a b c d x : ℝ) : onBdry a b c d ((x : ℂ) + d * I) := by
  right; left; simp
theorem bdry_right (a b c d y : ℝ) : onBdry a b c d ((b : ℂ) + y * I) := by
  right; right; right; simp
theorem bdry_left (a b c d y : ℝ) : onBdry a b c d ((a : ℂ) + y * I) := by
  right; right; left; simp

theorem contOn_h (f : ℂ → ℂ) (a b c : ℝ) (hf : ∀ x : ℝ, ContinuousAt f ((x : ℂ) + c * I)) :
    ContinuousOn (fun x : ℝ => f (x + c * I)) (uIcc a b) := fun x _ => by
  have h1 : ContinuousAt (fun x : ℝ => (x : ℂ) + c * I) x := by fun_prop
  exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + c * I) (hf x) h1).continuousWithinAt

theorem contOn_v (f : ℂ → ℂ) (a c d : ℝ) (hf : ∀ y : ℝ, ContinuousAt f ((a : ℂ) + y * I)) :
    ContinuousOn (fun y : ℝ => f (a + y * I)) (uIcc c d) := fun y _ => by
  have h1 : ContinuousAt (fun y : ℝ => (a : ℂ) + y * I) y := by fun_prop
  exact (ContinuousAt.comp (f := fun y : ℝ => (a : ℂ) + y * I) (hf y) h1).continuousWithinAt

/-- The rectangle sum of a function with primitives on the four edges. -/
theorem rectSum_of_primitives (Φ₁ Φ₂ Φ₃ Φ₄ f : ℂ → ℂ) (a b c d : ℝ)
    (hf : ∀ s, onBdry a b c d s → ContinuousAt f s)
    (h₁ : ∀ x : ℝ, HasDerivAt Φ₁ (f (x + c * I)) (x + c * I))
    (h₂ : ∀ x : ℝ, HasDerivAt Φ₂ (f (x + d * I)) (x + d * I))
    (h₃ : ∀ y : ℝ, HasDerivAt Φ₃ (f (b + y * I)) (b + y * I))
    (h₄ : ∀ y : ℝ, HasDerivAt Φ₄ (f (a + y * I)) (a + y * I)) :
    rectSum f a b c d = (Φ₁ (b + c * I) - Φ₁ (a + c * I)) - (Φ₂ (b + d * I) - Φ₂ (a + d * I)) +
      (Φ₃ (b + d * I) - Φ₃ (b + c * I)) - (Φ₄ (a + d * I) - Φ₄ (a + c * I)) := by
  unfold rectSum
  rw [seg_h Φ₁ f a b c (fun x _ => h₁ x) (contOn_h f a b c fun x => hf _ (bdry_bot a b c d x)),
    seg_h Φ₂ f a b d (fun x _ => h₂ x) (contOn_h f a b d fun x => hf _ (bdry_top a b c d x)),
    seg_v Φ₃ f b c d (fun y _ => h₃ y) (contOn_v f b c d fun y => hf _ (bdry_right a b c d y)),
    seg_v Φ₄ f a c d (fun y _ => h₄ y) (contOn_v f a c d fun y => hf _ (bdry_left a b c d y))]

theorem rectSum_congr (f g : ℂ → ℂ) (a b c d : ℝ) (h : ∀ s, onBdry a b c d s → f s = g s) :
    rectSum f a b c d = rectSum g a b c d := by
  unfold rectSum
  rw [integral_congr fun x _ => h _ (bdry_bot a b c d x),
    integral_congr fun x _ => h _ (bdry_top a b c d x),
    integral_congr fun y _ => h _ (bdry_right a b c d y),
    integral_congr fun y _ => h _ (bdry_left a b c d y)]

theorem rectSum_sub (f g : ℂ → ℂ) (a b c d : ℝ) (hf : ∀ s, onBdry a b c d s → ContinuousAt f s)
    (hg : ∀ s, onBdry a b c d s → ContinuousAt g s) :
    rectSum (fun s => f s - g s) a b c d = rectSum f a b c d - rectSum g a b c d := by
  unfold rectSum
  rw [integral_sub (contOn_h f a b c fun x => hf _ (bdry_bot a b c d x)).intervalIntegrable
      (contOn_h g a b c fun x => hg _ (bdry_bot a b c d x)).intervalIntegrable,
    integral_sub (contOn_h f a b d fun x => hf _ (bdry_top a b c d x)).intervalIntegrable
      (contOn_h g a b d fun x => hg _ (bdry_top a b c d x)).intervalIntegrable,
    integral_sub (contOn_v f b c d fun y => hf _ (bdry_right a b c d y)).intervalIntegrable
      (contOn_v g b c d fun y => hg _ (bdry_right a b c d y)).intervalIntegrable,
    integral_sub (contOn_v f a c d fun y => hf _ (bdry_left a b c d y)).intervalIntegrable
      (contOn_v g a c d fun y => hg _ (bdry_left a b c d y)).intervalIntegrable,
    smul_sub, smul_sub]
  ring

theorem rectSum_add (f g : ℂ → ℂ) (a b c d : ℝ) (hf : ∀ s, onBdry a b c d s → ContinuousAt f s)
    (hg : ∀ s, onBdry a b c d s → ContinuousAt g s) :
    rectSum (fun s => f s + g s) a b c d = rectSum f a b c d + rectSum g a b c d := by
  unfold rectSum
  rw [integral_add (contOn_h f a b c fun x => hf _ (bdry_bot a b c d x)).intervalIntegrable
      (contOn_h g a b c fun x => hg _ (bdry_bot a b c d x)).intervalIntegrable,
    integral_add (contOn_h f a b d fun x => hf _ (bdry_top a b c d x)).intervalIntegrable
      (contOn_h g a b d fun x => hg _ (bdry_top a b c d x)).intervalIntegrable,
    integral_add (contOn_v f b c d fun y => hf _ (bdry_right a b c d y)).intervalIntegrable
      (contOn_v g b c d fun y => hg _ (bdry_right a b c d y)).intervalIntegrable,
    integral_add (contOn_v f a c d fun y => hf _ (bdry_left a b c d y)).intervalIntegrable
      (contOn_v g a c d fun y => hg _ (bdry_left a b c d y)).intervalIntegrable,
    smul_add, smul_add]
  ring

theorem rectSum_const_mul (e : ℂ) (f : ℂ → ℂ) (a b c d : ℝ) :
    rectSum (fun s => e * f s) a b c d = e * rectSum f a b c d := by
  unfold rectSum
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

theorem rect_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (H : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc c d)) : rectSum f a b c d = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, c⟩ ⟨b, d⟩ H

/-! ### The principal parts -/

theorem bdry_ne (p : ℂ) (hp : p.im = 0) (a b c d : ℝ) (ha : a ≠ p.re) (hb : b ≠ p.re)
    (hc : c ≠ 0) (hd : d ≠ 0) (s : ℂ) (hs : onBdry a b c d s) : s ≠ p := by
  intro h
  subst h
  rcases hs with h | h | h | h
  · exact hc (h.symm.trans hp)
  · exact hd (h.symm.trans hp)
  · exact ha h.symm
  · exact hb h.symm

theorem contAt_inv_sq (p s : ℂ) (hs : s ≠ p) : ContinuousAt (fun s => ((s - p) ^ 2)⁻¹) s :=
  ((continuousAt_id.sub continuousAt_const).pow 2).inv₀ (pow_ne_zero 2 (sub_ne_zero.mpr hs))

theorem contAt_inv (p s : ℂ) (hs : s ≠ p) : ContinuousAt (fun s => (s - p)⁻¹) s :=
  (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs)

theorem hasDerivAt_neg_inv (p s : ℂ) (hs : s ≠ p) :
    HasDerivAt (fun s => -(s - p)⁻¹) (((s - p) ^ 2)⁻¹) s := by
  have h := (((hasDerivAt_id s).sub_const p).inv (sub_ne_zero.mpr hs)).neg
  refine h.congr_deriv ?_
  simp only [id]
  ring

theorem rectSum_inv_sq (p : ℂ) (hp : p.im = 0) (a b c d : ℝ) (ha : a ≠ p.re) (hb : b ≠ p.re)
    (hc : c ≠ 0) (hd : d ≠ 0) : rectSum (fun s => ((s - p) ^ 2)⁻¹) a b c d = 0 := by
  have hne := bdry_ne p hp a b c d ha hb hc hd
  rw [rectSum_of_primitives (fun s => -(s - p)⁻¹) (fun s => -(s - p)⁻¹) (fun s => -(s - p)⁻¹)
    (fun s => -(s - p)⁻¹) _ a b c d (fun s hs => contAt_inv_sq p s (hne s hs))
    (fun x => hasDerivAt_neg_inv p _ (hne _ (bdry_bot a b c d x)))
    (fun x => hasDerivAt_neg_inv p _ (hne _ (bdry_top a b c d x)))
    (fun y => hasDerivAt_neg_inv p _ (hne _ (bdry_right a b c d y)))
    (fun y => hasDerivAt_neg_inv p _ (hne _ (bdry_left a b c d y)))]
  ring

theorem log_eq_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    Complex.log z = Complex.log (-z) + Real.pi * I := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.log_re, norm_neg, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    ring

theorem log_eq_of_im_neg (z : ℂ) (hz : z.im < 0) :
    Complex.log z = Complex.log (-z) - Real.pi * I := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.log_re, norm_neg, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  · simp only [Complex.sub_im, Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    ring

theorem hasDerivAt_log_sub (p s : ℂ) (hs : s - p ∈ Complex.slitPlane) :
    HasDerivAt (fun s => Complex.log (s - p)) ((s - p)⁻¹) s := by
  have h := ((hasDerivAt_id s).sub_const p).clog hs
  refine h.congr_deriv ?_
  simp only [id, one_div]

theorem hasDerivAt_log_sub' (p s : ℂ) (hs : p - s ∈ Complex.slitPlane) :
    HasDerivAt (fun s => Complex.log (p - s)) ((s - p)⁻¹) s := by
  have h := ((hasDerivAt_id s).const_sub p).clog hs
  refine h.congr_deriv ?_
  simp only [id]
  rw [neg_div, one_div, neg_inv, neg_sub]

theorem rectSum_inv (p : ℂ) (hp : p.im = 0) (a b c d : ℝ) (ha : a < p.re) (hb : p.re < b)
    (hc : c < 0) (hd : 0 < d) :
    rectSum (fun s => (s - p)⁻¹) a b c d = 2 * Real.pi * I := by
  have hne := bdry_ne p hp a b c d ha.ne hb.ne' hc.ne hd.ne'
  have hsl1 : ∀ x : ℝ, (x : ℂ) + c * I - p ∈ Complex.slitPlane := fun x => by
    rw [Complex.mem_slitPlane_iff]; right; simp [hp, hc.ne]
  have hsl2 : ∀ x : ℝ, (x : ℂ) + d * I - p ∈ Complex.slitPlane := fun x => by
    rw [Complex.mem_slitPlane_iff]; right; simp [hp, hd.ne']
  have hsl3 : ∀ y : ℝ, (b : ℂ) + y * I - p ∈ Complex.slitPlane := fun y => by
    rw [Complex.mem_slitPlane_iff]; left; simp [hb]
  have hsl4 : ∀ y : ℝ, p - ((a : ℂ) + y * I) ∈ Complex.slitPlane := fun y => by
    rw [Complex.mem_slitPlane_iff]; left; simp [ha]
  rw [rectSum_of_primitives (fun s => Complex.log (s - p)) (fun s => Complex.log (s - p))
    (fun s => Complex.log (s - p)) (fun s => Complex.log (p - s)) _ a b c d
    (fun s hs => contAt_inv p s (hne s hs)) (fun x => hasDerivAt_log_sub p _ (hsl1 x))
    (fun x => hasDerivAt_log_sub p _ (hsl2 x)) (fun y => hasDerivAt_log_sub p _ (hsl3 y))
    (fun y => hasDerivAt_log_sub' p _ (hsl4 y))]
  have h1 : Complex.log ((a : ℂ) + d * I - p) = Complex.log (p - ((a : ℂ) + d * I)) + Real.pi * I := by
    have := log_eq_of_im_pos ((a : ℂ) + d * I - p) (by simp [hp, hd])
    rwa [neg_sub] at this
  have h2 : Complex.log ((a : ℂ) + c * I - p) = Complex.log (p - ((a : ℂ) + c * I)) - Real.pi * I := by
    have := log_eq_of_im_neg ((a : ℂ) + c * I - p) (by simp [hp, hc])
    rwa [neg_sub] at this
  rw [h1, h2]
  ring

/-! ### The double pole -/

theorem sin_sub_self_le (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖Complex.sin x - x‖ ≤ ‖x‖ ^ 3 := by
  have h := Complex.sin_bound hx
  have h3 : ‖x‖ ^ 5 ≤ ‖x‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hx (by norm_num)
  calc ‖Complex.sin x - x‖ = ‖(Complex.sin x - (x - x ^ 3 / 6)) + (-(x ^ 3 / 6))‖ := by
        congr 1; ring
    _ ≤ ‖Complex.sin x - (x - x ^ 3 / 6)‖ + ‖-(x ^ 3 / 6)‖ := norm_add_le _ _
    _ ≤ ‖x‖ ^ 5 / 100 + ‖x‖ ^ 3 / 6 := by
        rw [norm_neg, norm_div, norm_pow, Complex.norm_ofNat]
        exact add_le_add h le_rfl
    _ ≤ ‖x‖ ^ 3 := by have : 0 ≤ ‖x‖ ^ 3 := by positivity
                      linarith

theorem norm_sin_ge (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) : ‖x‖ / 2 ≤ ‖Complex.sin x‖ := by
  have h := sin_sub_self_le x (by linarith)
  have h3 : ‖x‖ ^ 3 ≤ ‖x‖ / 4 := by
    have : ‖x‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg x]
    nlinarith [norm_nonneg x]
  have h4 := norm_sub_norm_le x (Complex.sin x)
  rw [norm_sub_rev] at h4
  linarith [norm_nonneg x]

theorem sq_sub_sin_sq_le (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖x ^ 2 - Complex.sin x ^ 2‖ ≤ 3 * ‖x‖ ^ 4 := by
  have h1 := sin_sub_self_le x hx
  have h3 : ‖x‖ ^ 3 ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg _) hx (by norm_num)
  have h2 : ‖x + Complex.sin x‖ ≤ 3 * ‖x‖ := by
    calc ‖x + Complex.sin x‖ = ‖2 * x + (Complex.sin x - x)‖ := by congr 1; ring
      _ ≤ ‖2 * x‖ + ‖Complex.sin x - x‖ := norm_add_le _ _
      _ ≤ 2 * ‖x‖ + ‖x‖ ^ 3 := by rw [norm_mul, Complex.norm_ofNat]; exact add_le_add le_rfl h1
      _ ≤ 3 * ‖x‖ := by linarith
  calc ‖x ^ 2 - Complex.sin x ^ 2‖ = ‖x - Complex.sin x‖ * ‖x + Complex.sin x‖ := by
        rw [← norm_mul]; congr 1; ring
    _ ≤ ‖x‖ ^ 3 * (3 * ‖x‖) := by rw [norm_sub_rev]; gcongr
    _ = 3 * ‖x‖ ^ 4 := by ring

/-- `v(z) = π(z-p)/sin(πz)`. -/
def vv (p z : ℂ) : ℂ := Real.pi * (z - p) / Complex.sin (Real.pi * z)

theorem sin_pi_sq_eq (j : ℕ) (z : ℂ) :
    Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - ((j : ℂ) + 1))) ^ 2 := by
  have := Aux.sin_sq_add_nat_mul_pi (Real.pi * (z - ((j : ℂ) + 1))) (j + 1)
  rw [← this]
  congr 2
  push_cast
  ring

theorem vsq_bound (p : ℂ)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (z : ℂ) (hz : z ≠ p) (hz' : ‖z - p‖ ≤ 1 / (2 * Real.pi)) :
    ‖(vv p z ^ 2 - 1) / (z - p)‖ ≤ 12 * Real.pi ^ 2 * ‖z - p‖ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hw : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hxn : ‖(Real.pi : ℂ) * (z - p)‖ = Real.pi * ‖z - p‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have hx1 : ‖(Real.pi : ℂ) * (z - p)‖ ≤ 1 / 2 := by
    rw [hxn]
    calc Real.pi * ‖z - p‖ ≤ Real.pi * (1 / (2 * Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hsin := norm_sin_ge _ hx1
  have hnum := sq_sub_sin_sq_le ((Real.pi : ℂ) * (z - p)) (by linarith)
  have hx0 : 0 < ‖(Real.pi : ℂ) * (z - p)‖ := by rw [hxn]; positivity
  have hsin0 : Complex.sin (Real.pi * (z - p)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hsin
    linarith
  have heq : (vv p z ^ 2 - 1) / (z - p) =
      (((Real.pi : ℂ) * (z - p)) ^ 2 - Complex.sin (Real.pi * (z - p)) ^ 2) /
        (Complex.sin (Real.pi * (z - p)) ^ 2 * (z - p)) := by
    unfold vv
    rw [div_pow, hsq z, div_sub_one (pow_ne_zero 2 hsin0), div_div]
  rw [heq, norm_div, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
  calc ‖((Real.pi : ℂ) * (z - p)) ^ 2 - Complex.sin (Real.pi * (z - p)) ^ 2‖
      ≤ 3 * ‖(Real.pi : ℂ) * (z - p)‖ ^ 4 := hnum
    _ = 12 * Real.pi ^ 2 * ‖z - p‖ * ((‖(Real.pi : ℂ) * (z - p)‖ / 2) ^ 2 * ‖z - p‖) := by
        rw [hxn]; ring
    _ ≤ 12 * Real.pi ^ 2 * ‖z - p‖ * (‖Complex.sin (Real.pi * (z - p))‖ ^ 2 * ‖z - p‖) := by
        gcongr

theorem vsq_tendsto (p : ℂ)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2) :
    Tendsto (fun z => (vv p z ^ 2 - 1) / (z - p)) (𝓝[≠] p) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun z => 12 * Real.pi ^ 2 * ‖z - p‖) ?_ ?_
  · have hball : ∀ᶠ z in 𝓝 p, z ∈ Metric.closedBall p (1 / (2 * Real.pi)) :=
      Metric.closedBall_mem_nhds p (by positivity)
    filter_upwards [eventually_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hball]
      with z hz hz'
    exact vsq_bound p hsq z hz (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz')
  · have h : Tendsto (fun z : ℂ => 12 * Real.pi ^ 2 * ‖z - p‖) (𝓝 p)
        (𝓝 (12 * Real.pi ^ 2 * ‖p - p‖)) :=
      tendsto_const_nhds.mul ((continuous_id.sub continuous_const).norm.tendsto p)
    rw [sub_self, norm_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds

theorem vsq_sq_tendsto (p : ℂ)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2) :
    Tendsto (fun z => vv p z ^ 2) (𝓝[≠] p) (𝓝 1) := by
  have h1 : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 p)).sub_const p
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (h1.mul (vsq_tendsto p hsq)).const_add 1
  rw [zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

theorem key_tendsto (k : ℕ) (hk : k ≤ 3) (p : ℂ) (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (hint : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i) :
    Tendsto (fun z => (z - p) * Fc k z - hh k p / (z - p)) (𝓝[≠] p)
      (𝓝 (-(-1) ^ k * resT k p)) := by
  have hslope : Tendsto (fun z => (hh k z - hh k p) / (z - p)) (𝓝[≠] p)
      (𝓝 (-(-1) ^ k * resT k p)) := by
    have := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_hh k hk p hp0 hp1)
    refine this.congr fun z => ?_
    rw [slope_def_field]
  have hB := vsq_sq_tendsto p hsq
  have hA := vsq_tendsto p hsq
  have h := (hB.mul hslope).add (hA.const_mul (hh k p))
  rw [one_mul, mul_zero, add_zero] at h
  refine h.congr' ?_
  have hball : ∀ᶠ z in 𝓝 p, z ∈ Metric.ball p 1 := Metric.ball_mem_nhds _ one_pos
  filter_upwards [eventually_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hball]
    with z hz hz'
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
  have hre : p.re - 1 < z.re ∧ z.re < p.re + 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    have h1 := Complex.abs_re_le_norm (z - p)
    rw [Complex.sub_re] at h1
    obtain ⟨h3, h4⟩ := abs_lt.mp (lt_of_le_of_lt h1 hz')
    constructor <;> linarith
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := sin_pi_ne_zero z (hint z hre.1 hre.2 hz)
  unfold vv Fc
  field_simp
  ring

theorem G_extends (k : ℕ) (hk : k ≤ 3) (p : ℂ) (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (hint : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i) :
    ∃ Gt : ℂ → ℂ, DifferentiableOn ℂ Gt {s : ℂ | p.re - 1 < s.re ∧ s.re < p.re + 1} ∧
      ∀ s, s ≠ p → Gt s = Fc k s - (hh k p * ((s - p) ^ 2)⁻¹ +
        (-(-1) ^ k * resT k p) * (s - p)⁻¹) := by
  set G : ℂ → ℂ := fun s => Fc k s - (hh k p * ((s - p) ^ 2)⁻¹ +
    (-(-1) ^ k * resT k p) * (s - p)⁻¹) with hG
  set U : Set ℂ := {s : ℂ | p.re - 1 < s.re ∧ s.re < p.re + 1} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hpU : p ∈ U := ⟨by linarith, by linarith⟩
  have hU : U ∈ 𝓝 p := hUo.mem_nhds hpU
  have hd : DifferentiableOn ℂ G (U \ {p}) := by
    intro s hs
    have hsne : s ≠ p := hs.2
    have hsint := hint s hs.1.1 hs.1.2 hsne
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr hsne
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (Fc_differentiableAt k s hsint).sub
      (((differentiableAt_const _).mul (((differentiableAt_id.sub_const p).pow 2).inv
        (pow_ne_zero 2 hsp))).add
        ((differentiableAt_const _).mul ((differentiableAt_id.sub_const p).inv hsp)))
  have ho : (fun z => G z - G p) =o[𝓝[≠] p] fun z => (z - p)⁻¹ := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_mem_nhdsWithin] with z hz h
      exact absurd (sub_eq_zero.mp (inv_eq_zero.mp h)) hz
    · have key := key_tendsto k hk p hp0 hp1 hsq hint
      have h2 : Tendsto (fun z : ℂ => (z - p) * G p) (𝓝[≠] p) (𝓝 0) := by
        have := ((tendsto_id (x := 𝓝 p)).sub_const p).mul_const (G p)
        rw [sub_self, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h3 := (key.sub_const (-(-1) ^ k * resT k p)).sub h2
      rw [sub_self, sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_mem_nhdsWithin] with z hz
      have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
      simp only [hG, div_inv_eq_mul]
      field_simp
      ring
  refine ⟨Function.update G p (limUnder (𝓝[≠] p) G),
    Complex.differentiableOn_update_limUnder_of_isLittleO hU hd ho, fun s hs => ?_⟩
  rw [Function.update_of_ne hs]

/-- **Cauchy on the rectangle** `[p - 1/2, p + 1/2] × [-T, T]` around the double pole `p`. -/
theorem rect_Fc (k : ℕ) (hk : k ≤ 3) (p : ℂ) (hpim : p.im = 0) (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (hint : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i)
    (a b : ℝ) (ha : a = p.re - 1 / 2) (hb : b = p.re + 1 / 2) (T : ℝ) (hT : 0 < T) :
    rectSum (Fc k) a b (-T) T = 2 * Real.pi * I * (-(-1) ^ k * resT k p) := by
  obtain ⟨Gt, hGt, hGeq⟩ := G_extends k hk p hp0 hp1 hsq hint
  have hbd : ∀ s, onBdry a b (-T) T s → s ≠ p :=
    bdry_ne p hpim a b (-T) T (ne_of_lt (by linarith)) (ne_of_gt (by linarith))
      (neg_ne_zero.mpr hT.ne') hT.ne'
  have hbdint : ∀ s, onBdry a b (-T) T s → ∀ i : ℤ, s ≠ i := by
    intro s hs
    rcases hs with h | h | h | h
    · exact not_int_of_im s (by rw [h]; exact neg_ne_zero.mpr hT.ne')
    · exact not_int_of_im s (by rw [h]; exact hT.ne')
    · exact hint s (by rw [h]; linarith) (by rw [h]; linarith) (hbd s (Or.inr (Or.inr (Or.inl h))))
    · exact hint s (by rw [h]; linarith) (by rw [h]; linarith) (hbd s (Or.inr (Or.inr (Or.inr h))))
  have hsub : uIcc a b ×ℂ uIcc (-T) T ⊆ {s : ℂ | p.re - 1 < s.re ∧ s.re < p.re + 1} := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le (by linarith : a ≤ b)] at hs
    obtain ⟨⟨h1, h2⟩, _⟩ := hs
    exact ⟨by linarith, by linarith⟩
  have h0 := rect_zero Gt a b (-T) T (hGt.mono hsub)
  rw [rectSum_congr Gt _ a b (-T) T (fun s hs => hGeq s (hbd s hs)),
    rectSum_sub (Fc k) (fun s => hh k p * ((s - p) ^ 2)⁻¹ + (-(-1) ^ k * resT k p) * (s - p)⁻¹)
      a b (-T) T (fun s hs => (Fc_differentiableAt k s (hbdint s hs)).continuousAt)
      (fun s hs => ((contAt_inv_sq p s (hbd s hs)).const_mul _).add
        ((contAt_inv p s (hbd s hs)).const_mul _)),
    rectSum_add (fun s => hh k p * ((s - p) ^ 2)⁻¹) (fun s => (-(-1) ^ k * resT k p) * (s - p)⁻¹)
      a b (-T) T (fun s hs => (contAt_inv_sq p s (hbd s hs)).const_mul _)
      (fun s hs => (contAt_inv p s (hbd s hs)).const_mul _),
    rectSum_const_mul, rectSum_const_mul,
    rectSum_inv_sq p hpim a b (-T) T (ne_of_lt (by linarith)) (ne_of_gt (by linarith))
      (neg_ne_zero.mpr hT.ne') hT.ne',
    rectSum_inv p hpim a b (-T) T (by linarith) (by linarith) (by linarith) hT, sub_eq_zero] at h0
  rw [h0]
  ring

/-! ### Horizontal edges -/

theorem sq_le_sinh_sq (t : ℝ) : t ^ 2 ≤ Real.sinh t ^ 2 := by
  rcases le_total 0 t with h | h
  · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.mpr h) 2
  · have h' := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr h)
    rw [Real.sinh_neg] at h'
    nlinarith

theorem sinh_sq_le_norm_sin_sq (x y : ℝ) :
    Real.sinh y ^ 2 ≤ ‖Complex.sin ((x : ℂ) + y * I)‖ ^ 2 := by
  have h : Complex.sin ((x : ℂ) + y * I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I]
    push_cast
    ring
  rw [h, Complex.sq_norm, Complex.normSq_add_mul_I, mul_pow, mul_pow, Real.cosh_sq']
  have e : (Real.sin x) ^ 2 * (1 + Real.sinh y ^ 2) + (Real.cos x) ^ 2 * Real.sinh y ^ 2 =
      Real.sin x ^ 2 + Real.sinh y ^ 2 := by
    linear_combination (Real.sinh y ^ 2) * Real.sin_sq_add_cos_sq x
  rw [e]
  nlinarith [sq_nonneg (Real.sin x)]

theorem hh_norm_le (k : ℕ) (hk : k ≤ 3) (s : ℂ) (hs : 1 / 2 ≤ s.re) : ‖hh k s‖ ≤ 8 := by
  have hns : 1 / 2 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have hns1 : 1 ≤ ‖s + 1‖ := by
    have := Complex.re_le_norm (s + 1)
    rw [Complex.add_re, Complex.one_re] at this
    linarith
  have h8 := Aux.pow_div_cube_le ‖s‖ hns k hk
  have hs3 : 0 < ‖s‖ ^ 3 := by positivity
  rw [div_le_iff₀ hs3] at h8
  unfold hh
  rw [norm_div, norm_pow, norm_neg, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
  calc ‖s‖ ^ k ≤ 8 * ‖s‖ ^ 3 := h8
    _ ≤ 8 * (‖s‖ ^ 3 * ‖s + 1‖) := by
        rw [← mul_assoc]
        exact le_mul_of_one_le_right (by positivity) hns1

theorem Fc_horiz_bound (k : ℕ) (hk : k ≤ 3) (x y : ℝ) (hx : 1 / 2 ≤ x) (hy : y ≠ 0) :
    ‖Fc k ((x : ℂ) + y * I)‖ ≤ 8 / y ^ 2 := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hhh := hh_norm_le k hk _ (by rw [hre]; exact hx)
  have hsin : (Real.pi * y) ^ 2 ≤ ‖Complex.sin (Real.pi * ((x : ℂ) + y * I))‖ ^ 2 := by
    have e : (Real.pi : ℂ) * ((x : ℂ) + y * I) =
        ((Real.pi * x : ℝ) : ℂ) + ((Real.pi * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact (sq_le_sinh_sq _).trans (sinh_sq_le_norm_sin_sq _ _)
  have hpos : 0 < (Real.pi * y) ^ 2 := by positivity
  unfold Fc
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  calc Real.pi ^ 2 / ‖Complex.sin (Real.pi * ((x : ℂ) + y * I))‖ ^ 2 * ‖hh k ((x : ℂ) + y * I)‖
      ≤ Real.pi ^ 2 / (Real.pi * y) ^ 2 * 8 := by gcongr
    _ = 8 / y ^ 2 := by field_simp

theorem horiz_tendsto (k : ℕ) (hk : k ≤ 3) (a b : ℝ) (ha : 1 / 2 ≤ a) (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : ∀ T, T ≤ |g T|) :
    Tendsto (fun T : ℝ => ∫ x in a..b, Fc k ((x : ℂ) + (g T : ℂ) * I)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => 8 / T ^ 2 * |b - a|) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have hgT : g T ≠ 0 := by
      intro h
      have := hg T
      rw [h, abs_zero] at this
      linarith
    have hT2 : T ^ 2 ≤ (g T) ^ 2 := by
      have := pow_le_pow_left₀ hT.le (hg T) 2
      rwa [sq_abs] at this
    refine norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hab] at hx
    exact (Fc_horiz_bound k hk x (g T) (by linarith [hx.1]) hgT).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hT2)
  · have h := ((tendsto_const_nhds (x := (8 : ℝ))).div_atTop
      (tendsto_pow_atTop two_ne_zero)).mul_const |b - a|
    rwa [zero_mul] at h

/-! ### Shifting the line and telescoping -/

theorem shift_step (k : ℕ) (hk : k ≤ 3) (j : ℕ)
    (hint : ∀ i : ℕ, Integrable (fun y : ℝ => Fc k ((i : ℂ) + 1 / 2 + y * I))) :
    ∫ y : ℝ, Fc k ((j : ℂ) + 1 / 2 + y * I) =
      (∫ y : ℝ, Fc k (((j + 1 : ℕ) : ℂ) + 1 / 2 + y * I)) -
        2 * Real.pi * (-(-1) ^ k * resT k ((j : ℂ) + 1)) := by
  have hpim : ((j : ℂ) + 1).im = 0 := by simp
  have hpre : ((j : ℂ) + 1).re = j + 1 := by simp
  have hp0 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hp1 : (j : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (j + 1)
  have hint' : ∀ s : ℂ, ((j : ℂ) + 1).re - 1 < s.re → s.re < ((j : ℂ) + 1).re + 1 →
      s ≠ (j : ℂ) + 1 → ∀ i : ℤ, s ≠ i := by
    intro s h1 h2 h3
    rw [hpre] at h1 h2
    exact not_int_of_re_near s j (by linarith) (by linarith) h3
  have hrect := fun T (hT : 0 < T) => rect_Fc k hk ((j : ℂ) + 1) hpim hp0 hp1 (sin_pi_sq_eq j) hint'
    ((j : ℝ) + 1 / 2) ((j : ℝ) + 3 / 2) (by rw [hpre]; ring) (by rw [hpre]; ring) T hT
  simp only [rectSum] at hrect
  have efa : (fun y : ℝ => Fc k ((((j : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fc k ((j : ℂ) + 1 / 2 + y * I) := funext fun y => by congr 1; push_cast; ring
  have efb : (fun y : ℝ => Fc k ((((j : ℝ) + 3 / 2 : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fc k (((j + 1 : ℕ) : ℂ) + 1 / 2 + y * I) := funext fun y => by
    congr 1; push_cast; ring
  simp only [efa, efb] at hrect
  have ha : (1 : ℝ) / 2 ≤ (j : ℝ) + 1 / 2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hab : (j : ℝ) + 1 / 2 ≤ (j : ℝ) + 3 / 2 := by linarith
  have hbot := horiz_tendsto k hk _ _ ha hab (fun T => -T) fun T => by
    rw [abs_neg]; exact le_abs_self T
  have htop := horiz_tendsto k hk _ _ ha hab (fun T => T) fun T => le_abs_self T
  have hright := (intervalIntegral_tendsto_integral (hint (j + 1)) tendsto_neg_atTop_atBot
    tendsto_id).const_smul I
  have hleft := (intervalIntegral_tendsto_integral (hint j) tendsto_neg_atTop_atBot
    tendsto_id).const_smul I
  have hlim := ((hbot.sub htop).add hright).sub hleft
  have hconst : Tendsto (fun T : ℝ => (∫ x in ((j : ℝ) + 1 / 2)..((j : ℝ) + 3 / 2),
      Fc k ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
      (∫ x in ((j : ℝ) + 1 / 2)..((j : ℝ) + 3 / 2), Fc k ((x : ℂ) + (T : ℂ) * I)) +
      I • (∫ y in (-T)..T, Fc k (((j + 1 : ℕ) : ℂ) + 1 / 2 + y * I)) -
      I • (∫ y in (-T)..T, Fc k ((j : ℂ) + 1 / 2 + y * I))) atTop
      (𝓝 (2 * Real.pi * I * (-(-1) ^ k * resT k ((j : ℂ) + 1)))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact (hrect T hT).symm
  have := tendsto_nhds_unique hlim hconst
  simp only [smul_eq_mul] at this
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination (-1 : ℂ) * this

theorem telescope (k : ℕ) (hk : k ≤ 3)
    (hint : ∀ i : ℕ, Integrable (fun y : ℝ => Fc k ((i : ℂ) + 1 / 2 + y * I))) (M : ℕ) :
    ∫ y : ℝ, Fc k (((0 : ℕ) : ℂ) + 1 / 2 + y * I) =
      (∫ y : ℝ, Fc k ((M : ℂ) + 1 / 2 + y * I)) -
        2 * Real.pi * ∑ j ∈ Finset.range M, (-(-1) ^ k * resT k ((j : ℂ) + 1)) := by
  induction M with
  | zero => simp
  | succ M ih => rw [ih, shift_step k hk M hint, Finset.sum_range_succ]; ring

theorem summable_resT (k : ℕ) (hk : k ≤ 3) : Summable (fun j : ℕ => resT k ((j : ℂ) + 1)) := by
  have hg : Summable (fun j : ℕ => 4 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left 4).congr fun j => ?_
    push_cast
    ring
  refine Summable.of_norm_bounded hg fun j => ?_
  have hx1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hxpos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have e : resT k ((j : ℂ) + 1) =
      ((((3 - k : ℕ) : ℝ) / (((j : ℝ) + 1) ^ (4 - k) * ((j : ℝ) + 1 + 1)) +
        1 / (((j : ℝ) + 1) ^ (3 - k) * ((j : ℝ) + 1 + 1) ^ 2) : ℝ) : ℂ) := by
    simp only [resT]
    push_cast
    rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ (4 - k) * ((j : ℝ) + 1 + 1) := by
    rw [sq]
    exact mul_le_mul (le_self_pow₀ hx1 (by omega)) (by linarith) hxpos.le (by positivity)
  have h2 : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ (3 - k) * ((j : ℝ) + 1 + 1) ^ 2 := by
    rw [← one_mul (((j : ℝ) + 1) ^ 2)]
    exact mul_le_mul (one_le_pow₀ hx1) (by nlinarith) (by positivity) (by positivity)
  have h3 : ((3 - k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.sub_le 3 k
  calc ((3 - k : ℕ) : ℝ) / (((j : ℝ) + 1) ^ (4 - k) * ((j : ℝ) + 1 + 1)) +
        1 / (((j : ℝ) + 1) ^ (3 - k) * ((j : ℝ) + 1 + 1) ^ 2)
      ≤ 3 / ((j : ℝ) + 1) ^ 2 + 1 / ((j : ℝ) + 1) ^ 2 :=
        add_le_add (div_le_div₀ (by norm_num) h3 (by positivity) h1)
          (div_le_div₀ (by norm_num) le_rfl (by positivity) h2)
    _ = 4 / ((j : ℝ) + 1) ^ 2 := by ring

/-- **The line integral as a residue sum**: `∫_{Re s = 1/2} Fc k = 2π (-1)^k ∑_{ℓ ≥ 1} resT k ℓ`. -/
theorem main (k : ℕ) (hk : k ≤ 3)
    (hint : ∀ i : ℕ, Integrable (fun y : ℝ => Fc k ((i : ℂ) + 1 / 2 + y * I)))
    (hvan : Tendsto (fun i : ℕ => ∫ y : ℝ, Fc k ((i : ℂ) + 1 / 2 + y * I)) atTop (𝓝 0)) :
    ∫ y : ℝ, Fc k (((0 : ℕ) : ℂ) + 1 / 2 + y * I) =
      2 * Real.pi * (-1) ^ k * ∑' j : ℕ, resT k ((j : ℂ) + 1) := by
  have hs : Summable (fun j : ℕ => -(-1) ^ k * resT k ((j : ℂ) + 1)) :=
    (summable_resT k hk).mul_left _
  have hpart := hs.hasSum.tendsto_sum_nat
  have hL := hvan.sub (hpart.const_mul (2 * (Real.pi : ℂ)))
  have := tendsto_nhds_unique
    (tendsto_const_nhds (x := ∫ y : ℝ, Fc k (((0 : ℕ) : ℂ) + 1 / 2 + y * I)))
    (hL.congr fun M => (telescope k hk hint M).symm)
  rw [this, tsum_mul_left]
  ring

end Pfq54.MI
