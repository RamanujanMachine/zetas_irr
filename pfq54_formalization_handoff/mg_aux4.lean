/-
# The four beta integrals and the Fubini swap (sorry-free)

On `(0,1)⁴` with `dμ = dx dy dt dr`, the product of the four beta integrals times `Γ(w+j)Γ(L-w)`
integrates over the line `Re w = 1/2` to `2π Γ(L+j) ∫ P q^j dμ`, where `P` is the positive
integrand and `q = (1-r)/(1-r+xytr)`.
-/
import mg_aux3

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

/-- `dx` on `(0,1)`. -/
abbrev ρ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- `dx dy dt dr` on `(0,1)⁴`. -/
abbrev μ4 : Measure (ℝ × ℝ × ℝ × ℝ) := ρ.prod (ρ.prod (ρ.prod ρ))

/-- The open cube. -/
def cube : Set (ℝ × ℝ × ℝ × ℝ) := Ioo 0 1 ×ˢ (Ioo 0 1 ×ˢ (Ioo 0 1 ×ˢ Ioo 0 1))

theorem ae_cube : ∀ᵐ z ∂μ4, z ∈ cube := by
  have h : μ4 = (volume.prod (volume.prod (volume.prod volume))).restrict cube := by
    unfold μ4 ρ cube
    rw [Measure.prod_restrict, Measure.prod_restrict, Measure.prod_restrict]
  rw [h]
  exact ae_restrict_mem (measurableSet_Ioo.prod (measurableSet_Ioo.prod
    (measurableSet_Ioo.prod measurableSet_Ioo)))

/-- The beta integrand. -/
def bint (a b : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)

theorem beta_rho (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ x, bint a b x ∂ρ = Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hne : Complex.Gamma (a + b) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.add_re]; linarith)
  rw [h, mul_div_cancel_left₀ _ hne]
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

theorem bint_le (a b : ℂ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ (a - 1).re)
    (hb : 0 ≤ (b - 1).re) : ‖bint a b x‖ ≤ 1 := by
  unfold bint
  rw [norm_mul, show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
  exact (mul_le_mul (norm_cpow_le_one x hx.1.le hx.2.le _ ha)
    (norm_cpow_le_one _ (by linarith [hx.2]) (by linarith [hx.1]) _ hb) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

/-- The four beta integrands. -/
def bprod (n : ℕ) (w : ℂ) (z : ℝ × ℝ × ℝ × ℝ) : ℂ :=
  bint (w + ((2 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) z.1 *
    (bint (w + ((3 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) z.2.1 *
      (bint (w + ((4 * n : ℕ) : ℂ)) ((8 * n + 2 : ℕ) : ℂ) z.2.2.1 *
        bint (w + (n : ℂ)) (((15 * n + 1 : ℕ) : ℂ) - w) z.2.2.2))

/-- The product of the four beta integrals. -/
theorem bprod_integral (n : ℕ) (hn : 1 ≤ n) (w : ℂ) (hw : w.re = 1 / 2) :
    ∫ z, bprod n w z ∂μ4 =
      Complex.Gamma (w + ((2 * n : ℕ) : ℂ)) * Complex.Gamma ((11 * n + 1 : ℕ) : ℂ) /
          Complex.Gamma (w + ((2 * n : ℕ) : ℂ) + ((11 * n + 1 : ℕ) : ℂ)) *
        (Complex.Gamma (w + ((3 * n : ℕ) : ℂ)) * Complex.Gamma ((11 * n + 1 : ℕ) : ℂ) /
          Complex.Gamma (w + ((3 * n : ℕ) : ℂ) + ((11 * n + 1 : ℕ) : ℂ)) *
        (Complex.Gamma (w + ((4 * n : ℕ) : ℂ)) * Complex.Gamma ((8 * n + 2 : ℕ) : ℂ) /
          Complex.Gamma (w + ((4 * n : ℕ) : ℂ) + ((8 * n + 2 : ℕ) : ℂ)) *
        (Complex.Gamma (w + (n : ℂ)) * Complex.Gamma (((15 * n + 1 : ℕ) : ℂ) - w) /
          Complex.Gamma (w + (n : ℂ) + (((15 * n + 1 : ℕ) : ℂ) - w))))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hre : ∀ c : ℕ, 0 < (w + (c : ℂ)).re := fun c => by
    rw [Complex.add_re, hw, Complex.natCast_re]
    positivity
  have hnat : ∀ c : ℕ, 0 < c → 0 < ((c : ℂ)).re := fun c hc => by
    rw [Complex.natCast_re]
    exact_mod_cast hc
  have hlast : 0 < (((15 * n + 1 : ℕ) : ℂ) - w).re := by
    rw [Complex.sub_re, hw, Complex.natCast_re]
    push_cast
    linarith
  rw [show (fun z => bprod n w z) = fun z : ℝ × ℝ × ℝ × ℝ =>
      bint (w + ((2 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) z.1 *
        (fun z' : ℝ × ℝ × ℝ => bint (w + ((3 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) z'.1 *
          (fun z'' : ℝ × ℝ => bint (w + ((4 * n : ℕ) : ℂ)) ((8 * n + 2 : ℕ) : ℂ) z''.1 *
            bint (w + (n : ℂ)) (((15 * n + 1 : ℕ) : ℂ) - w) z''.2) z'.2) z.2 from rfl,
    show μ4 = ρ.prod (ρ.prod (ρ.prod ρ)) from rfl,
    integral_prod_mul (fun x => bint (w + ((2 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) x)
      (fun z' : ℝ × ℝ × ℝ => bint (w + ((3 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) z'.1 *
        (fun z'' : ℝ × ℝ => bint (w + ((4 * n : ℕ) : ℂ)) ((8 * n + 2 : ℕ) : ℂ) z''.1 *
          bint (w + (n : ℂ)) (((15 * n + 1 : ℕ) : ℂ) - w) z''.2) z'.2),
    integral_prod_mul (fun x => bint (w + ((3 * n : ℕ) : ℂ)) ((11 * n + 1 : ℕ) : ℂ) x)
      (fun z'' : ℝ × ℝ => bint (w + ((4 * n : ℕ) : ℂ)) ((8 * n + 2 : ℕ) : ℂ) z''.1 *
          bint (w + (n : ℂ)) (((15 * n + 1 : ℕ) : ℂ) - w) z''.2),
    integral_prod_mul (fun x => bint (w + ((4 * n : ℕ) : ℂ)) ((8 * n + 2 : ℕ) : ℂ) x)
      (fun x => bint (w + (n : ℂ)) (((15 * n + 1 : ℕ) : ℂ) - w) x),
    beta_rho _ _ (hre _) (hnat _ (by omega)), beta_rho _ _ (hre _) (hnat _ (by omega)),
    beta_rho _ _ (hre _) (hnat _ (by omega)), beta_rho _ _ (hre _) hlast]

/-- The real part of the integrand. -/
def gg (n : ℕ) (z : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  z.1 ^ (2 * n - 1) * (1 - z.1) ^ (11 * n) * (z.2.1 ^ (3 * n - 1) * (1 - z.2.1) ^ (11 * n) *
    (z.2.2.1 ^ (4 * n - 1) * (1 - z.2.2.1) ^ (8 * n + 1) *
      (z.2.2.2 ^ (n - 1) * (1 - z.2.2.2) ^ (15 * n))))

/-- `v = xytr/(1-r)`. -/
def vv (z : ℝ × ℝ × ℝ × ℝ) : ℝ := z.1 * z.2.1 * z.2.2.1 * z.2.2.2 / (1 - z.2.2.2)

/-- On the open cube the four beta integrands are `g · v^w`. -/
theorem bprod_factor (n : ℕ) (hn : 1 ≤ n) (w : ℂ) (z : ℝ × ℝ × ℝ × ℝ) (hz : z ∈ cube) :
    bprod n w z = ((gg n z : ℝ) : ℂ) * ((vv z : ℝ) : ℂ) ^ w := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, ⟨ht0, ht1⟩, ⟨hr0, hr1⟩⟩ := hz
  have hb : 0 < 1 - z.2.2.2 := sub_pos.mpr hr1
  have hbc : ((1 - z.2.2.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have e1 : ∀ x : ℝ, (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := fun x => by push_cast; ring
  have hr : (1 - (z.2.2.2 : ℂ)) ^ (((15 * n + 1 : ℕ) : ℂ) - w - 1) =
      (((1 - z.2.2.2) ^ (15 * n) : ℝ) : ℂ) * (((1 - z.2.2.2 : ℝ) : ℂ) ^ w)⁻¹ := by
    rw [e1, show ((15 * n + 1 : ℕ) : ℂ) - w - 1 = ((15 * n : ℕ) : ℂ) + -w by push_cast; ring,
      Complex.cpow_add _ _ hbc, Complex.cpow_natCast, Complex.cpow_neg]
    push_cast
    rfl
  have hv : ((vv z : ℝ) : ℂ) ^ w = (z.1 : ℂ) ^ w * (z.2.1 : ℂ) ^ w * (z.2.2.1 : ℂ) ^ w *
      (z.2.2.2 : ℂ) ^ w * (((1 - z.2.2.2 : ℝ) : ℂ) ^ w)⁻¹ := by
    unfold vv
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (by positivity) hb.le, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hr0.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) ht0.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx0.le hy0.le]
  unfold bprod bint
  rw [cpow_split _ hx0 w (2 * n) (by omega), cpow_split _ hy0 w (3 * n) (by omega),
    cpow_split _ ht0 w (4 * n) (by omega), cpow_split _ hr0 w n hn,
    cpow_nat_sub _ (11 * n + 1) (by omega), cpow_nat_sub _ (11 * n + 1) (by omega),
    cpow_nat_sub _ (8 * n + 2) (by omega), hr, hv, e1, e1, e1]
  unfold gg
  push_cast
  ring

/-- The positive integrand (same as `Pfq54.BP.posIntegrand`). -/
def Pd (n : ℕ) (x y t r : ℝ) : ℝ :=
  x ^ (16 * n) * y ^ (17 * n) * t ^ (18 * n) * r ^ (15 * n) * (1 - x) ^ (11 * n) *
      (1 - y) ^ (11 * n) * (1 - t) ^ (8 * n + 1) * (1 - r) ^ (15 * n) /
    ((1 - r) + x * y * t * r) ^ (14 * n + 1)

/-- `q = (1-r)/(1-r+xytr)`. -/
def qd (z : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (1 - z.2.2.2) / ((1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2)

theorem real_identity (n j : ℕ) (hn : 1 ≤ n) (z : ℝ × ℝ × ℝ × ℝ) (hz : z ∈ cube) :
    gg n z * (vv z ^ (14 * n + 1) / (1 + vv z) ^ (14 * n + 1 + j)) =
      Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 * qd z ^ j := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, ⟨ht0, ht1⟩, ⟨hr0, hr1⟩⟩ := hz
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hb : 0 < 1 - z.2.2.2 := sub_pos.mpr hr1
  have hD : 0 < (1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2 := by positivity
  have h1v : 1 + vv z = ((1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2) / (1 - z.2.2.2) := by
    unfold vv
    field_simp
  have hb' : 1 - z.2.2.2 ≠ 0 := hb.ne'
  have hD' : (1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2 ≠ 0 := hD.ne'
  have hvv : vv z ^ (14 * (k + 1) + 1) / (1 + vv z) ^ (14 * (k + 1) + 1 + j) =
      (z.1 * z.2.1 * z.2.2.1 * z.2.2.2) ^ (14 * (k + 1) + 1) * (1 - z.2.2.2) ^ j /
        ((1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2) ^ (14 * (k + 1) + 1 + j) := by
    rw [h1v]
    unfold vv
    rw [div_pow, div_pow, pow_add (1 - z.2.2.2)]
    field_simp
    ring
  rw [hvv]
  unfold gg Pd qd
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show 3 * (k + 1) - 1 = 3 * k + 2 by omega,
    show 4 * (k + 1) - 1 = 4 * k + 3 by omega, show k + 1 - 1 = k by omega, div_pow,
    pow_add ((1 - z.2.2.2) + z.1 * z.2.1 * z.2.2.1 * z.2.2.2)]
  field_simp
  ring

end Pfq54.MG
