/-
# `𝒮_G(n)_k` for `k ≤ 3` (sorry-free)

`(-s)^k Γ(w) = (-1)^k ∑_j b_j Γ(w+j)` with `b_j ≥ 0` and `∑_j b_j (L)_j = (L+2n)^k`,
`L = 14n+1`; hence `𝒮_G(n)_0 = 𝔠_n X₀` and `‖𝒮_G(n)_k‖ ≤ (16n+1)^k 𝔠_n X₀`.
-/
import mg_aux7

open Set Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.MG

open Pfq54

/-- `(L)_j = (14n+1)⋯(14n+j)`. -/
def Pj (n j : ℕ) : ℝ := ∏ i ∈ Finset.range j, ((14 * n + 1 + i : ℕ) : ℝ)

theorem fact_Pj (n j : ℕ) : ((14 * n + j).factorial : ℝ) = (14 * n).factorial * Pj n j := by
  induction j with
  | zero => rw [add_zero, Pj, Finset.prod_range_zero, mul_one]
  | succ j ih =>
    rw [Pj, Finset.prod_range_succ, ← Pj, ← mul_assoc, ← ih, ← add_assoc, Nat.factorial_succ,
      Nat.cast_mul, mul_comm, show 14 * n + j + 1 = 14 * n + 1 + j by omega]

/-- The real value `J_j = 𝔠_n (L)_j X_j`. -/
def Jr (n j : ℕ) : ℝ := cfR n * Pj n j * Xj n j

theorem J_val (n j : ℕ) (hn : 1 ≤ n) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, Complex.Gamma (wl y + j) * Rf n (wl y) = (Jr n j : ℂ) :=
  J_real n j hn (Pj n j) (fact_Pj n j)

/-- A four-term combination of shifts. -/
theorem SG_comb4 (n k : ℕ) (hn : 1 ≤ n) (b0 b1 b2 b3 : ℝ)
    (h : ∀ w : ℂ, w.re = 1 / 2 → (-(2 * n + w)) ^ k * (Complex.Gamma w * Rf n w) =
      (-1) ^ k * ((b0 : ℂ) * (Complex.Gamma (w + ((0 : ℕ) : ℂ)) * Rf n w) +
        (b1 : ℂ) * (Complex.Gamma (w + ((1 : ℕ) : ℂ)) * Rf n w) +
        (b2 : ℂ) * (Complex.Gamma (w + ((2 : ℕ) : ℂ)) * Rf n w) +
        (b3 : ℂ) * (Complex.Gamma (w + ((3 : ℕ) : ℂ)) * Rf n w))) :
    SG n k = (-1) ^ k * ((b0 * Jr n 0 + b1 * Jr n 1 + b2 * Jr n 2 + b3 * Jr n 3 : ℝ) : ℂ) := by
  have i0 := (Gj_integrable n 0 hn).const_mul (b0 : ℂ)
  have i1 := (Gj_integrable n 1 hn).const_mul (b1 : ℂ)
  have i2 := (Gj_integrable n 2 hn).const_mul (b2 : ℂ)
  have i3 := (Gj_integrable n 3 hn).const_mul (b3 : ℂ)
  have hJv : ∀ j : ℕ, ∫ y : ℝ, Complex.Gamma (wl y + j) * Rf n (wl y) =
      ((2 * Real.pi : ℝ) : ℂ) * (Jr n j : ℂ) := fun j => by
    rw [← J_val n j hn, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity)),
      one_mul]
  have i01 : Integrable (fun y : ℝ => (b0 : ℂ) * (Complex.Gamma (wl y + ((0 : ℕ) : ℂ)) *
      Rf n (wl y)) + (b1 : ℂ) * (Complex.Gamma (wl y + ((1 : ℕ) : ℂ)) * Rf n (wl y))) := i0.add i1
  have i012 : Integrable (fun y : ℝ => (b0 : ℂ) * (Complex.Gamma (wl y + ((0 : ℕ) : ℂ)) *
      Rf n (wl y)) + (b1 : ℂ) * (Complex.Gamma (wl y + ((1 : ℕ) : ℂ)) * Rf n (wl y)) +
      (b2 : ℂ) * (Complex.Gamma (wl y + ((2 : ℕ) : ℂ)) * Rf n (wl y))) := i01.add i2
  rw [SG_expr, integral_congr_ae (Eventually.of_forall fun y => h (wl y) (wl_re y)),
    integral_const_mul, integral_add i012 i3, integral_add i01 i2,
    integral_add i0 i1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, hJv 0, hJv 1, hJv 2, hJv 3]
  have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp
  push_cast
  ring

theorem norm_comb (k : ℕ) (a : ℝ) (ha : 0 ≤ a) : ‖(-1 : ℂ) ^ k * (a : ℂ)‖ = a := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ha]

/-- **`𝒮_G(n)_0 = 𝔠_n X₀`.** -/
theorem SG_zero_aux (n : ℕ) (hn : 1 ≤ n) : SG n 0 = ((cfR n * Xj n 0 : ℝ) : ℂ) := by
  rw [SG_comb4 n 0 hn 1 0 0 0 fun w _ => by push_cast; ring]
  unfold Jr Pj
  push_cast
  ring

/-- **`‖𝒮_G(n)_k‖ ≤ (16n+1)^k 𝔠_n X₀`** for `k ≤ 3`. -/
theorem SG_bound_aux (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 3)
    (hPint : Integrable (fun z : ℝ × ℝ × ℝ × ℝ => Pd n z.1 z.2.1 z.2.2.1 z.2.2.2) μ4) :
    ‖SG n k‖ ≤ (16 * n + 1 : ℝ) ^ k * (cfR n * Xj n 0) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 ≤ cfR n := by unfold cfR; positivity
  have hX := fun j => Xj_bounds n j hn hPint
  have hJ : ∀ j, 0 ≤ Jr n j ∧ Jr n j ≤ cfR n * Pj n j * Xj n 0 := fun j => by
    have hP : 0 ≤ Pj n j := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    exact ⟨mul_nonneg (mul_nonneg hc hP) (hX j).1,
      mul_le_mul_of_nonneg_left (hX j).2 (mul_nonneg hc hP)⟩
  have p1 : Pj n 1 = 14 * n + 1 := by unfold Pj; rw [Finset.prod_range_one]; push_cast; ring
  have p2 : Pj n 2 = (14 * n + 1) * (14 * n + 2) := by
    unfold Pj; rw [Finset.prod_range_succ, Finset.prod_range_one]; push_cast; ring
  have p3 : Pj n 3 = (14 * n + 1) * (14 * n + 2) * (14 * n + 3) := by
    unfold Pj; rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
    push_cast; ring
  have p0 : Pj n 0 = 1 := by unfold Pj; rw [Finset.prod_range_zero]
  obtain ⟨j0, j0'⟩ := hJ 0
  obtain ⟨j1, j1'⟩ := hJ 1
  obtain ⟨j2, j2'⟩ := hJ 2
  obtain ⟨j3, j3'⟩ := hJ 3
  rw [p0] at j0'
  rw [p1] at j1'
  rw [p2] at j2'
  rw [p3] at j3'
  have hX0 := (hX 0).1
  have L0 : 0 ≤ cfR n * Xj n 0 := mul_nonneg hc hX0
  have c1 : 0 ≤ 4 * (n : ℝ) - 1 := by linarith
  have c2 : 0 ≤ 12 * (n : ℝ) ^ 2 - 6 * n + 1 := by nlinarith
  have c3 : 0 ≤ 6 * (n : ℝ) - 3 := by linarith
  have m0 : ∀ b : ℝ, 0 ≤ b → b * Jr n 0 ≤ b * (cfR n * 1 * Xj n 0) := fun b hb =>
    mul_le_mul_of_nonneg_left j0' hb
  have m1 : ∀ b : ℝ, 0 ≤ b → b * Jr n 1 ≤ b * (cfR n * (14 * n + 1) * Xj n 0) := fun b hb =>
    mul_le_mul_of_nonneg_left j1' hb
  have m2 : ∀ b : ℝ, 0 ≤ b → b * Jr n 2 ≤
      b * (cfR n * ((14 * n + 1) * (14 * n + 2)) * Xj n 0) := fun b hb =>
    mul_le_mul_of_nonneg_left j2' hb
  have m3 : ∀ b : ℝ, 0 ≤ b → b * Jr n 3 ≤
      b * (cfR n * ((14 * n + 1) * (14 * n + 2) * (14 * n + 3)) * Xj n 0) := fun b hb =>
    mul_le_mul_of_nonneg_left j3' hb
  interval_cases k
  · rw [SG_comb4 n 0 hn 1 0 0 0 fun w _ => by push_cast; ring, norm_comb 0 _ (by positivity)]
    linarith [m0 1 zero_le_one]
  · rw [SG_comb4 n 1 hn (2 * n) 1 0 0 fun w hw => by
        rw [(Gamma_shifts w hw).1]; push_cast; ring,
      norm_comb 1 _ (by positivity)]
    linarith [m0 (2 * n) (by positivity), m1 1 zero_le_one]
  · rw [SG_comb4 n 2 hn (4 * n ^ 2) (4 * n - 1) 1 0 fun w hw => by
        rw [(Gamma_shifts w hw).1, (Gamma_shifts w hw).2.1]; push_cast; ring,
      norm_comb 2 _ (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) j0)
        (mul_nonneg c1 j1)) (mul_nonneg zero_le_one j2)) (mul_nonneg le_rfl j3))]
    linarith [m0 (4 * n ^ 2) (by positivity), m1 (4 * n - 1) c1, m2 1 zero_le_one]
  · rw [SG_comb4 n 3 hn (8 * n ^ 3) (12 * n ^ 2 - 6 * n + 1) (6 * n - 3) 1 fun w hw => by
        rw [(Gamma_shifts w hw).1, (Gamma_shifts w hw).2.1, (Gamma_shifts w hw).2.2]
        push_cast; ring,
      norm_comb 3 _ (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) j0)
        (mul_nonneg c2 j1)) (mul_nonneg c3 j2)) (mul_nonneg zero_le_one j3))]
    linarith [m0 (8 * n ^ 3) (by positivity), m1 _ c2, m2 _ c3, m3 1 zero_le_one]

end Pfq54.MG
