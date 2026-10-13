import mi_aux

open Filter Topology MeasureTheory Set intervalIntegral
open Complex (I)

noncomputable section

namespace Pfq54.MC

open Pfq54 Pfq54.MI

/-- The integrand `π²/sin²(πs) · h(s)`. -/
def Fc (h : ℂ → ℂ) (s : ℂ) : ℂ := (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * s) ^ 2 * h s

theorem Fc_differentiableAt (h : ℂ → ℂ) (s : ℂ) (hs : ∀ j : ℤ, s ≠ j)
    (hh : DifferentiableAt ℂ h s) : DifferentiableAt ℂ (Fc h) s := by
  have hsin : Complex.sin (Real.pi * s) ^ 2 ≠ 0 := pow_ne_zero 2 (sin_pi_ne_zero s hs)
  have hsd : DifferentiableAt ℂ (fun s : ℂ => Complex.sin (Real.pi * s) ^ 2) s :=
    (Complex.differentiable_sin.differentiableAt.comp s
      ((differentiableAt_const _).mul differentiableAt_id)).pow 2
  unfold Fc
  exact ((differentiableAt_const _).div hsd hsin).mul hh

theorem key_tendsto (h : ℂ → ℂ) (p d : ℂ) (hd : HasDerivAt h d p)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (hint : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i) :
    Tendsto (fun z => (z - p) * Fc h z - h p / (z - p)) (𝓝[≠] p) (𝓝 d) := by
  have hslope : Tendsto (fun z => (h z - h p) / (z - p)) (𝓝[≠] p) (𝓝 d) := by
    have := hasDerivAt_iff_tendsto_slope.mp hd
    refine this.congr fun z => ?_
    rw [slope_def_field]
  have hB := vsq_sq_tendsto p hsq
  have hA := vsq_tendsto p hsq
  have hlim := (hB.mul hslope).add (hA.const_mul (h p))
  rw [one_mul, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
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

theorem G_extends (h : ℂ → ℂ) (p d : ℂ) (hd : HasDerivAt h d p)
    (hdiff : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → DifferentiableAt ℂ h s)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (hint : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i) :
    ∃ Gt : ℂ → ℂ, DifferentiableOn ℂ Gt {s : ℂ | p.re - 1 < s.re ∧ s.re < p.re + 1} ∧
      ∀ s, s ≠ p → Gt s = Fc h s - (h p * ((s - p) ^ 2)⁻¹ + d * (s - p)⁻¹) := by
  set G : ℂ → ℂ := fun s => Fc h s - (h p * ((s - p) ^ 2)⁻¹ + d * (s - p)⁻¹) with hG
  set U : Set ℂ := {s : ℂ | p.re - 1 < s.re ∧ s.re < p.re + 1} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hpU : p ∈ U := ⟨by linarith, by linarith⟩
  have hU : U ∈ 𝓝 p := hUo.mem_nhds hpU
  have hdd : DifferentiableOn ℂ G (U \ {p}) := by
    intro s hs
    have hsne : s ≠ p := hs.2
    have hsint := hint s hs.1.1 hs.1.2 hsne
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr hsne
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (Fc_differentiableAt h s hsint (hdiff s hs.1.1 hs.1.2)).sub
      (((differentiableAt_const _).mul (((differentiableAt_id.sub_const p).pow 2).inv
        (pow_ne_zero 2 hsp))).add
        ((differentiableAt_const _).mul ((differentiableAt_id.sub_const p).inv hsp)))
  have ho : (fun z => G z - G p) =o[𝓝[≠] p] fun z => (z - p)⁻¹ := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_mem_nhdsWithin] with z hz h
      exact absurd (sub_eq_zero.mp (inv_eq_zero.mp h)) hz
    · have key := key_tendsto h p d hd hsq hint
      have h2 : Tendsto (fun z : ℂ => (z - p) * G p) (𝓝[≠] p) (𝓝 0) := by
        have := ((tendsto_id (x := 𝓝 p)).sub_const p).mul_const (G p)
        rw [sub_self, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h3 := (key.sub_const d).sub h2
      rw [sub_self, sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_mem_nhdsWithin] with z hz
      have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
      simp only [hG, div_inv_eq_mul]
      field_simp
      ring
  refine ⟨Function.update G p (limUnder (𝓝[≠] p) G),
    Complex.differentiableOn_update_limUnder_of_isLittleO hU hdd ho, fun s hs => ?_⟩
  rw [Function.update_of_ne hs]

/-- **Cauchy on the rectangle** `[p - 1/2, p + 1/2] × [-T, T]` around the double pole `p`. -/
theorem rect_Fc (h : ℂ → ℂ) (K : ℝ)
    (hdiff : ∀ s : ℂ, K < s.re ∨ s.im ≠ 0 → DifferentiableAt ℂ h s)
    (p d : ℂ) (hpim : p.im = 0) (hpK : K ≤ p.re - 1) (hd : HasDerivAt h d p)
    (hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2)
    (hint : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i)
    (a b : ℝ) (ha : a = p.re - 1 / 2) (hb : b = p.re + 1 / 2) (T : ℝ) (hT : 0 < T) :
    rectSum (Fc h) a b (-T) T = 2 * Real.pi * I * d := by
  obtain ⟨Gt, hGt, hGeq⟩ := G_extends h p d hd (fun s h1 _ => hdiff s (Or.inl (by linarith)))
    hsq hint
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
  have hbddiff : ∀ s, onBdry a b (-T) T s → DifferentiableAt ℂ h s := by
    intro s hs
    rcases hs with h | h | h | h
    · exact hdiff s (Or.inr (by rw [h]; exact neg_ne_zero.mpr hT.ne'))
    · exact hdiff s (Or.inr (by rw [h]; exact hT.ne'))
    · exact hdiff s (Or.inl (by rw [h]; linarith))
    · exact hdiff s (Or.inl (by rw [h]; linarith))
  have hsub : uIcc a b ×ℂ uIcc (-T) T ⊆ {s : ℂ | p.re - 1 < s.re ∧ s.re < p.re + 1} := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le (by linarith : a ≤ b)] at hs
    obtain ⟨⟨h1, h2⟩, _⟩ := hs
    exact ⟨by linarith, by linarith⟩
  have h0 := rect_zero Gt a b (-T) T (hGt.mono hsub)
  rw [rectSum_congr Gt _ a b (-T) T (fun s hs => hGeq s (hbd s hs)),
    rectSum_sub (Fc h) (fun s => h p * ((s - p) ^ 2)⁻¹ + d * (s - p)⁻¹)
      a b (-T) T (fun s hs => (Fc_differentiableAt h s (hbdint s hs) (hbddiff s hs)).continuousAt)
      (fun s hs => ((contAt_inv_sq p s (hbd s hs)).const_mul _).add
        ((contAt_inv p s (hbd s hs)).const_mul _)),
    rectSum_add (fun s => h p * ((s - p) ^ 2)⁻¹) (fun s => d * (s - p)⁻¹)
      a b (-T) T (fun s hs => (contAt_inv_sq p s (hbd s hs)).const_mul _)
      (fun s hs => (contAt_inv p s (hbd s hs)).const_mul _),
    rectSum_const_mul, rectSum_const_mul,
    rectSum_inv_sq p hpim a b (-T) T (ne_of_lt (by linarith)) (ne_of_gt (by linarith))
      (neg_ne_zero.mpr hT.ne') hT.ne',
    rectSum_inv p hpim a b (-T) T (by linarith) (by linarith) (by linarith) hT, sub_eq_zero] at h0
  rw [h0]
  ring

/-! ### Bounds on the edges -/

theorem Fc_horiz_bound (h : ℂ → ℂ) (K C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, K + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖)
    (hK : 0 ≤ K) (x y : ℝ) (hx : K + 1 / 2 ≤ x) (hy : y ≠ 0) :
    ‖Fc h ((x : ℂ) + y * I)‖ ≤ 2 * C / y ^ 2 := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hns : 1 / 2 ≤ ‖(x : ℂ) + y * I‖ := by
    have := Complex.re_le_norm ((x : ℂ) + y * I)
    rw [hre] at this
    linarith
  have hh := hbound _ (by rw [hre]; exact hx)
  have hh2 : ‖h ((x : ℂ) + y * I)‖ ≤ 2 * C := by
    refine hh.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hsin : (Real.pi * y) ^ 2 ≤ ‖Complex.sin (Real.pi * ((x : ℂ) + y * I))‖ ^ 2 := by
    have e : (Real.pi : ℂ) * ((x : ℂ) + y * I) =
        ((Real.pi * x : ℝ) : ℂ) + ((Real.pi * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact (sq_le_sinh_sq _).trans (sinh_sq_le_norm_sin_sq _ _)
  have hpos : 0 < (Real.pi * y) ^ 2 := by positivity
  unfold Fc
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  calc Real.pi ^ 2 / ‖Complex.sin (Real.pi * ((x : ℂ) + y * I))‖ ^ 2 * ‖h ((x : ℂ) + y * I)‖
      ≤ Real.pi ^ 2 / (Real.pi * y) ^ 2 * (2 * C) := by gcongr
    _ = 2 * C / y ^ 2 := by field_simp

theorem horiz_tendsto (h : ℂ → ℂ) (K C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, K + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖) (hK : 0 ≤ K)
    (a b : ℝ) (ha : K + 1 / 2 ≤ a) (hab : a ≤ b) (g : ℝ → ℝ) (hg : ∀ T, T ≤ |g T|) :
    Tendsto (fun T : ℝ => ∫ x in a..b, Fc h ((x : ℂ) + (g T : ℂ) * I)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => 2 * C / T ^ 2 * |b - a|) ?_ ?_
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
    exact (Fc_horiz_bound h K C hC hbound hK x (g T) (by linarith [hx.1]) hgT).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hT2)
  · have h := ((tendsto_const_nhds (x := (2 * C : ℝ))).div_atTop
      (tendsto_pow_atTop two_ne_zero)).mul_const |b - a|
    rwa [zero_mul] at h

/-! ### The vertical lines `Re s = m + 1/2` -/

theorem sin_sq_half_line (m : ℕ) (y : ℝ) :
    Complex.sin (Real.pi * ((m : ℂ) + 1 / 2 + y * I)) ^ 2 =
      ((Real.cosh (Real.pi * y) : ℝ) : ℂ) ^ 2 := by
  rw [show (Real.pi : ℂ) * ((m : ℂ) + 1 / 2 + y * I) = (Real.pi / 2 + ((Real.pi * y : ℝ) : ℂ) * I) +
      m * Real.pi by push_cast; ring, Aux.sin_sq_add_nat_mul_pi, Complex.sin_add,
    Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  ring

theorem line_bound (h : ℂ → ℂ) (K C : ℝ)
    (hbound : ∀ s : ℂ, K + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖) (m : ℕ) (hm : K ≤ m) (y : ℝ) :
    ‖Fc h ((m : ℂ) + 1 / 2 + y * I)‖ ≤ Real.pi ^ 2 * C / ((m : ℝ) + 1 / 2) * (1 + (Real.pi * y) ^ 2)⁻¹ := by
  have hre : ((m : ℂ) + 1 / 2 + y * I).re = m + 1 / 2 := by simp
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hns : (m : ℝ) + 1 / 2 ≤ ‖(m : ℂ) + 1 / 2 + y * I‖ := by
    have := Complex.re_le_norm ((m : ℂ) + 1 / 2 + y * I)
    rw [hre] at this
    linarith
  have hh := hbound ((m : ℂ) + 1 / 2 + y * I) (by rw [hre]; linarith)
  have hC : 0 ≤ C := by
    have := (norm_nonneg (h ((m : ℂ) + 1 / 2 + y * I))).trans hh
    rw [div_nonneg_iff] at this
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith [norm_nonneg ((m : ℂ) + 1 / 2 + y * I)]
  have hc := Aux.one_add_sq_le_cosh_sq (Real.pi * y)
  have hcpos : 0 < Real.cosh (Real.pi * y) := Real.cosh_pos _
  have hcc : 1 / Real.cosh (Real.pi * y) ^ 2 ≤ (1 + (Real.pi * y) ^ 2)⁻¹ := by
    rw [one_div]; exact inv_anti₀ (by positivity) hc
  have hh2 : ‖h ((m : ℂ) + 1 / 2 + y * I)‖ ≤ C / ((m : ℝ) + 1 / 2) :=
    hh.trans (div_le_div_of_nonneg_left hC (by positivity) hns)
  unfold Fc
  rw [norm_mul, norm_div, norm_pow, sin_sq_half_line, norm_pow, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    abs_of_pos hcpos]
  calc Real.pi ^ 2 / Real.cosh (Real.pi * y) ^ 2 * ‖h ((m : ℂ) + 1 / 2 + y * I)‖
      = Real.pi ^ 2 * ‖h ((m : ℂ) + 1 / 2 + y * I)‖ * (1 / Real.cosh (Real.pi * y) ^ 2) := by
        ring
    _ ≤ Real.pi ^ 2 * (C / ((m : ℝ) + 1 / 2)) * (1 + (Real.pi * y) ^ 2)⁻¹ := by gcongr
    _ = _ := by ring

theorem line_continuous (h : ℂ → ℂ) (K : ℝ)
    (hdiff : ∀ s : ℂ, K < s.re ∨ s.im ≠ 0 → DifferentiableAt ℂ h s) (m : ℕ) (hm : K ≤ m) :
    Continuous (fun y : ℝ => Fc h ((m : ℂ) + 1 / 2 + y * I)) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : ContinuousAt (fun y : ℝ => (m : ℂ) + 1 / 2 + y * I) y := by fun_prop
  have hre : ((m : ℂ) + 1 / 2 + y * I).re = m + 1 / 2 := by simp
  have h1 : ContinuousAt (Fc h) ((m : ℂ) + 1 / 2 + y * I) :=
    (Fc_differentiableAt h _ (not_int_of_re_half _ m hre)
      (hdiff _ (Or.inl (by rw [hre]; linarith)))).continuousAt
  exact ContinuousAt.comp (g := Fc h) h1 hc

theorem line_integrable (h : ℂ → ℂ) (K C : ℝ)
    (hdiff : ∀ s : ℂ, K < s.re ∨ s.im ≠ 0 → DifferentiableAt ℂ h s)
    (hbound : ∀ s : ℂ, K + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖) (m : ℕ) (hm : K ≤ m) :
    Integrable (fun y : ℝ => Fc h ((m : ℂ) + 1 / 2 + y * I)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  exact Integrable.mono' ((integrable_inv_one_add_sq.comp_mul_left' hpi).const_mul
      (Real.pi ^ 2 * C / ((m : ℝ) + 1 / 2)))
    (line_continuous h K hdiff m hm).aestronglyMeasurable
    (Eventually.of_forall fun y => line_bound h K C hbound m hm y)

theorem line_tendsto_zero (h : ℂ → ℂ) (K C : ℝ)
    (hbound : ∀ s : ℂ, K + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖) :
    Tendsto (fun m : ℕ => ∫ y : ℝ, Fc h ((m : ℂ) + 1 / 2 + y * I)) atTop (𝓝 0) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hint : Integrable (fun y : ℝ => (1 + (Real.pi * y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hpi
  set J := ∫ y : ℝ, (1 + (Real.pi * y) ^ 2)⁻¹
  obtain ⟨M, hM⟩ : ∃ M : ℕ, K ≤ M := ⟨⌈K⌉₊, Nat.le_ceil K⟩
  have hbd : ∀ᶠ m : ℕ in atTop, ‖∫ y : ℝ, Fc h ((m : ℂ) + 1 / 2 + y * I)‖ ≤
      Real.pi ^ 2 * C / ((m : ℝ) + 1 / 2) * J := by
    filter_upwards [eventually_ge_atTop M] with m hm
    exact (norm_integral_le_of_norm_le (hint.const_mul _)
      (Eventually.of_forall fun y => line_bound h K C hbound m (hM.trans (by exact_mod_cast hm)) y)).trans
        (le_of_eq (integral_const_mul _ _))
  refine squeeze_zero_norm' hbd ?_
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 := ((tendsto_const_nhds (x := Real.pi ^ 2 * C)).div_atTop h1).mul_const J
  rwa [zero_mul] at h2

/-! ### Shifting the line and telescoping -/

theorem not_int_of_re_near' (s : ℂ) (K : ℕ) (j : ℕ) (h1 : ((K + j : ℕ) : ℝ) < s.re)
    (h2 : s.re < ((K + j : ℕ) : ℝ) + 2) (hne : s ≠ ((K + j : ℕ) : ℂ) + 1) (i : ℤ) : s ≠ i :=
  not_int_of_re_near s (K + j) h1 h2 hne i

theorem shift_step (h : ℂ → ℂ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ s : ℂ, (K : ℝ) < s.re ∨ s.im ≠ 0 → DifferentiableAt ℂ h s)
    (hbound : ∀ s : ℂ, (K : ℝ) + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖)
    (d : ℕ → ℂ) (hd : ∀ j : ℕ, HasDerivAt h (d j) ((K : ℂ) + 1 + j)) (j : ℕ) :
    ∫ y : ℝ, Fc h (((K + j : ℕ) : ℂ) + 1 / 2 + y * I) =
      (∫ y : ℝ, Fc h (((K + j + 1 : ℕ) : ℂ) + 1 / 2 + y * I)) - 2 * Real.pi * d j := by
  set p : ℂ := (K : ℂ) + 1 + j with hp
  have hpim : p.im = 0 := by simp [hp]
  have hpre : p.re = K + 1 + j := by simp [hp]
  have hint' : ∀ s : ℂ, p.re - 1 < s.re → s.re < p.re + 1 → s ≠ p → ∀ i : ℤ, s ≠ i := by
    intro s h1 h2 h3
    rw [hpre] at h1 h2
    refine not_int_of_re_near' s K j (by push_cast; linarith) (by push_cast; linarith) ?_
    rw [hp] at h3
    intro e
    apply h3
    rw [e]
    push_cast
    ring
  have hsq : ∀ z, Complex.sin (Real.pi * z) ^ 2 = Complex.sin (Real.pi * (z - p)) ^ 2 := by
    intro z
    have := sin_pi_sq_eq (K + j) z
    rw [this, hp]
    congr 2
    push_cast
    ring
  have hrect := fun T (hT : 0 < T) => rect_Fc h K hdiff p (d j) hpim (by rw [hpre]; linarith)
    (hd j) hsq hint' ((K + j : ℕ) + 1 / 2 : ℝ) ((K + j : ℕ) + 3 / 2 : ℝ)
    (by rw [hpre]; push_cast; ring) (by rw [hpre]; push_cast; ring) T hT
  simp only [rectSum] at hrect
  have efa : (fun y : ℝ => Fc h ((((K + j : ℕ) + 1 / 2 : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fc h (((K + j : ℕ) : ℂ) + 1 / 2 + y * I) := funext fun y => by
    congr 1; push_cast; ring
  have efb : (fun y : ℝ => Fc h ((((K + j : ℕ) + 3 / 2 : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fc h (((K + j + 1 : ℕ) : ℂ) + 1 / 2 + y * I) := funext fun y => by
    congr 1; push_cast; ring
  simp only [efa, efb] at hrect
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ha : (K : ℝ) + 1 / 2 ≤ ((K + j : ℕ) : ℝ) + 1 / 2 := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hab : ((K + j : ℕ) : ℝ) + 1 / 2 ≤ ((K + j : ℕ) : ℝ) + 3 / 2 := by linarith
  have hbot := horiz_tendsto h K C hC hbound hK0 _ _ ha hab (fun T => -T) fun T => by
    rw [abs_neg]; exact le_abs_self T
  have htop := horiz_tendsto h K C hC hbound hK0 _ _ ha hab (fun T => T) fun T => le_abs_self T
  have hi1 : (K : ℝ) ≤ ((K + j + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hi2 : (K : ℝ) ≤ ((K + j : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hright := (intervalIntegral_tendsto_integral (line_integrable h K C hdiff hbound _ hi1)
    tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hleft := (intervalIntegral_tendsto_integral (line_integrable h K C hdiff hbound _ hi2)
    tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hlim := ((hbot.sub htop).add hright).sub hleft
  have hconst : Tendsto (fun T : ℝ => (∫ x in (((K + j : ℕ) : ℝ) + 1 / 2)..(((K + j : ℕ) : ℝ) + 3 / 2),
      Fc h ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
      (∫ x in (((K + j : ℕ) : ℝ) + 1 / 2)..(((K + j : ℕ) : ℝ) + 3 / 2), Fc h ((x : ℂ) + (T : ℂ) * I)) +
      I • (∫ y in (-T)..T, Fc h (((K + j + 1 : ℕ) : ℂ) + 1 / 2 + y * I)) -
      I • (∫ y in (-T)..T, Fc h (((K + j : ℕ) : ℂ) + 1 / 2 + y * I))) atTop
      (𝓝 (2 * Real.pi * I * d j)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact (hrect T hT).symm
  have := tendsto_nhds_unique hlim hconst
  simp only [smul_eq_mul] at this
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination (-1 : ℂ) * this

theorem telescope (h : ℂ → ℂ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ s : ℂ, (K : ℝ) < s.re ∨ s.im ≠ 0 → DifferentiableAt ℂ h s)
    (hbound : ∀ s : ℂ, (K : ℝ) + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖)
    (d : ℕ → ℂ) (hd : ∀ j : ℕ, HasDerivAt h (d j) ((K : ℂ) + 1 + j)) (M : ℕ) :
    ∫ y : ℝ, Fc h ((K : ℂ) + 1 / 2 + y * I) =
      (∫ y : ℝ, Fc h (((K + M : ℕ) : ℂ) + 1 / 2 + y * I)) -
        2 * Real.pi * ∑ j ∈ Finset.range M, d j := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, shift_step h K C hC hdiff hbound d hd M, Finset.sum_range_succ,
      show K + (M + 1) = K + M + 1 from rfl]
    ring

/-- **The line integral as a residue sum.** -/
theorem main (h : ℂ → ℂ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ s : ℂ, (K : ℝ) < s.re ∨ s.im ≠ 0 → DifferentiableAt ℂ h s)
    (hbound : ∀ s : ℂ, (K : ℝ) + 1 / 2 ≤ s.re → ‖h s‖ ≤ C / ‖s‖)
    (d : ℕ → ℂ) (hd : ∀ j : ℕ, HasDerivAt h (d j) ((K : ℂ) + 1 + j)) (L : ℂ) (hL : HasSum d L) :
    ∫ y : ℝ, Fc h ((K : ℂ) + 1 / 2 + y * I) = -(2 * Real.pi * L) := by
  have hvan : Tendsto (fun M : ℕ => ∫ y : ℝ, Fc h (((K + M : ℕ) : ℂ) + 1 / 2 + y * I)) atTop
      (𝓝 0) := by
    have := (line_tendsto_zero h K C hbound).comp (tendsto_add_atTop_nat K)
    refine this.congr fun M => ?_
    show (∫ y : ℝ, Fc h (((M + K : ℕ) : ℂ) + 1 / 2 + y * I)) = _
    rw [Nat.add_comm M K]
  have hpart := hL.tendsto_sum_nat
  have hLim := hvan.sub (hpart.const_mul (2 * (Real.pi : ℂ)))
  have := tendsto_nhds_unique
    (tendsto_const_nhds (x := ∫ y : ℝ, Fc h ((K : ℂ) + 1 / 2 + y * I)))
    (hLim.congr fun M => (telescope h K C hC hdiff hbound d hd M).symm)
  rw [this]
  ring

end Pfq54.MC
