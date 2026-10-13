/-
# Auxiliary lemmas for `log_Z0_le.lean` (sorry-free)

The function `g` of the termwise Stirling bound, its derivative, concavity, and the rational
logarithm certificate at `y = 12`.
-/
import Mathlib

noncomputable section

namespace Pfq54.LZ

/-- `x log x` (same as `Pfq54.BP.xlogx`). -/
def xl (x : ℝ) : ℝ := x * Real.log x

/-- The Stirling exponent `g` (same as `Pfq54.BP.gfun`). -/
def gA (y : ℝ) : ℝ :=
  xl (y + 10) + xl (y + 11) + xl (y + 12) - xl y - xl (y + 1) - xl (y + 2) -
    xl (y - 1) - xl (y - 2) - xl (16 - y) - xl (17 - y)

/-- `g'(y) = log[(y+10)(y+11)(y+12)(16-y)(17-y) / (y(y+1)(y+2)(y-1)(y-2))]`. -/
def gpfun (y : ℝ) : ℝ :=
  Real.log (y + 10) + Real.log (y + 11) + Real.log (y + 12) + Real.log (16 - y) +
    Real.log (17 - y) - Real.log y - Real.log (y + 1) - Real.log (y + 2) - Real.log (y - 1) -
    Real.log (y - 2)

/-- The derivative of `g` on `(2, 16)`. -/
theorem gfun_deriv (y : ℝ) (hy : y ∈ Set.Ioo (2 : ℝ) 16) : HasDerivAt gA (gpfun y) y := by
  obtain ⟨h1, h2⟩ := hy
  have p1 : 0 < y - 2 := sub_pos.mpr h1
  have p2 : 0 < 16 - y := sub_pos.mpr h2
  have hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt xl (Real.log x + 1) x :=
    fun x hx => Real.hasDerivAt_mul_log hx
  have e1 := HasDerivAt.comp_add_const y 10 (hd (y + 10) (by positivity))
  have e2 := HasDerivAt.comp_add_const y 11 (hd (y + 11) (by positivity))
  have e3 := HasDerivAt.comp_add_const y 12 (hd (y + 12) (by positivity))
  have e4 := hd y (by linarith)
  have e5 := HasDerivAt.comp_add_const y 1 (hd (y + 1) (by positivity))
  have e6 := HasDerivAt.comp_add_const y 2 (hd (y + 2) (by positivity))
  have e7 := HasDerivAt.comp_sub_const y 1 (hd (y - 1) (by linarith))
  have e8 := HasDerivAt.comp_sub_const y 2 (hd (y - 2) (by linarith))
  have e9 := HasDerivAt.comp_const_sub 16 y (hd (16 - y) (by linarith))
  have e10 := HasDerivAt.comp_const_sub 17 y (hd (17 - y) (by linarith))
  exact (((((((((e1.add e2).add e3).sub e4).sub e5).sub e6).sub e7).sub e8).sub e9).sub
    e10).congr_deriv (by unfold gpfun; ring)

/-- `g'` is antitone on `(2, 16)`. -/
theorem gpfun_antitone : AntitoneOn gpfun (Set.Ioo (2 : ℝ) 16) := by
  have hd : ∀ x ∈ Set.Ioo (2 : ℝ) 16, HasDerivAt gpfun ((x + 10)⁻¹ + (x + 11)⁻¹ + (x + 12)⁻¹ +
      -(16 - x)⁻¹ + -(17 - x)⁻¹ - x⁻¹ - (x + 1)⁻¹ - (x + 2)⁻¹ - (x - 1)⁻¹ - (x - 2)⁻¹) x := by
    intro x ⟨h1, h2⟩
    have l : ∀ z : ℝ, z ≠ 0 → HasDerivAt Real.log z⁻¹ z := fun z hz => Real.hasDerivAt_log hz
    exact ((((((((((HasDerivAt.comp_add_const x 10 (l _ (by linarith))).add
      (HasDerivAt.comp_add_const x 11 (l _ (by linarith)))).add
      (HasDerivAt.comp_add_const x 12 (l _ (by linarith)))).add
      (HasDerivAt.comp_const_sub 16 x (l _ (by linarith)))).add
      (HasDerivAt.comp_const_sub 17 x (l _ (by linarith)))).sub (l x (by linarith))).sub
      (HasDerivAt.comp_add_const x 1 (l _ (by linarith)))).sub
      (HasDerivAt.comp_add_const x 2 (l _ (by linarith)))).sub
      (HasDerivAt.comp_sub_const x 1 (l _ (by linarith)))).sub
      (HasDerivAt.comp_sub_const x 2 (l _ (by linarith))))
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 2 16)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (by rwa [interior_Ioo] at hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_)
  rw [interior_Ioo] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [(hd x ⟨h1, h2⟩).deriv]
  have i1 : (x + 10)⁻¹ ≤ x⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have i2 : (x + 11)⁻¹ ≤ (x + 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have i3 : (x + 12)⁻¹ ≤ (x + 2)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have i4 : 0 < (16 - x)⁻¹ := inv_pos.mpr (by linarith)
  have i5 : 0 < (17 - x)⁻¹ := inv_pos.mpr (by linarith)
  have i6 : 0 < (x - 1)⁻¹ := inv_pos.mpr (by linarith)
  have i7 : 0 < (x - 2)⁻¹ := inv_pos.mpr (by linarith)
  linarith

/-- The rational-logarithm certificate at `y₀ = 12`, with the slope correction `(1/91)(3/200)`. -/
theorem g12_numeric : 30 * Real.log (3 / 2) + gA 12 + 1 / 91 * (3 / 200) < 65.46 := by
  have hser : ∀ (x : ℝ) (n : ℕ), 0 ≤ x → x < 1 →
      |∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1) + Real.log (1 - x)| ≤ x ^ (n + 1) / (1 - x) :=
    fun x n h0 h1 => by
      have := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
      rwa [abs_of_nonneg h0] at this
  have hinv : ∀ q : ℝ, 0 < q → Real.log q⁻¹ = -Real.log q := fun q _ => Real.log_inv q
  have sA := hser (1 / 3) 10 (by norm_num) (by norm_num)
  have sB := hser (1 / 5) 6 (by norm_num) (by norm_num)
  have sC := hser (1 / 8) 5 (by norm_num) (by norm_num)
  have sD := hser (1 / 11) 4 (by norm_num) (by norm_num)
  have sE := hser (1 / 13) 4 (by norm_num) (by norm_num)
  have sF := hser (1 / 24) 3 (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 3 = (3 / 2)⁻¹ by norm_num, hinv _ (by norm_num)] at sA
  rw [show (1 : ℝ) - 1 / 5 = (5 / 4)⁻¹ by norm_num, hinv _ (by norm_num)] at sB
  rw [show (1 : ℝ) - 1 / 8 = (8 / 7)⁻¹ by norm_num, hinv _ (by norm_num)] at sC
  rw [show (1 : ℝ) - 1 / 11 = (11 / 10)⁻¹ by norm_num, hinv _ (by norm_num)] at sD
  rw [show (1 : ℝ) - 1 / 13 = (13 / 12)⁻¹ by norm_num, hinv _ (by norm_num)] at sE
  rw [show (1 : ℝ) - 1 / 24 = (24 / 23)⁻¹ by norm_num, hinv _ (by norm_num)] at sF
  norm_num [Finset.sum_range_succ] at sA sB sC sD sE sF
  have sL := Real.log_two_near_10
  rw [abs_le] at sA sB sC sD sE sF sL
  set L := Real.log 2
  set A := Real.log (3 / 2)
  set B := Real.log (5 / 4)
  set C := Real.log (8 / 7)
  set Dd := Real.log (11 / 10)
  set E := Real.log (13 / 12)
  set F := Real.log (24 / 23)
  have lm : ∀ p q : ℝ, 0 < p → 0 < q → Real.log (p * q) = Real.log p + Real.log q :=
    fun p q hp hq => Real.log_mul hp.ne' hq.ne'
  have h22 : Real.log 22 = 4 * L + B + Dd := by
    rw [show (22 : ℝ) = 2 ^ 4 * (5 / 4) * (11 / 10) by norm_num, lm _ _ (by norm_num) (by norm_num),
      lm _ _ (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have h23 : Real.log 23 = 4 * L + A - F := by
    rw [show (23 : ℝ) = 2 ^ 4 * (3 / 2) * (24 / 23)⁻¹ by norm_num,
      lm _ _ (by norm_num) (by norm_num), lm _ _ (by norm_num) (by norm_num), Real.log_pow,
      hinv _ (by norm_num)]; push_cast; ring
  have h24 : Real.log 24 = 4 * L + A := by
    rw [show (24 : ℝ) = 2 ^ 4 * (3 / 2) by norm_num, lm _ _ (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h12 : Real.log 12 = 3 * L + A := by
    rw [show (12 : ℝ) = 2 ^ 3 * (3 / 2) by norm_num, lm _ _ (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h13 : Real.log 13 = 3 * L + A + E := by
    rw [show (13 : ℝ) = 2 ^ 3 * (3 / 2) * (13 / 12) by norm_num,
      lm _ _ (by norm_num) (by norm_num), lm _ _ (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h14 : Real.log 14 = 4 * L - C := by
    rw [show (14 : ℝ) = 2 ^ 4 * (8 / 7)⁻¹ by norm_num, lm _ _ (by norm_num) (by norm_num),
      Real.log_pow, hinv _ (by norm_num)]; push_cast; ring
  have h11 : Real.log 11 = 3 * L + B + Dd := by
    rw [show (11 : ℝ) = 2 ^ 3 * (5 / 4) * (11 / 10) by norm_num,
      lm _ _ (by norm_num) (by norm_num), lm _ _ (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h10 : Real.log 10 = 3 * L + B := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num, lm _ _ (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h4 : Real.log 4 = 2 * L := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h5 : Real.log 5 = 2 * L + B := by
    rw [show (5 : ℝ) = 2 ^ 2 * (5 / 4) by norm_num, lm _ _ (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have hg : gA 12 = 22 * Real.log 22 + 23 * Real.log 23 + 24 * Real.log 24 -
      12 * Real.log 12 - 13 * Real.log 13 - 14 * Real.log 14 - 11 * Real.log 11 -
      10 * Real.log 10 - 4 * Real.log 4 - 5 * Real.log 5 := by
    unfold gA xl; norm_num
  rw [hg, h22, h23, h24, h12, h13, h14, h11, h10, h4, h5]
  linarith only [sA.1, sA.2, sB.1, sB.2, sC.1, sC.2, sD.1, sD.2, sE.1, sE.2, sF.1, sF.2, sL.1,
    sL.2]

end Pfq54.LZ
