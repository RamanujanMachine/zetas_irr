/-
# Diagonalization and shearing (sorry-free)

From `Bal(n) = Q_∞ + A₁/n + O(1/n²)` and a left eigenbasis `Y Q_∞ = D Y`, `D = diag(ρ)`, the
conjugated matrices `M'(n) = Y Bal(n) Y⁻¹ = D + A'/n + E(n)` are sheared by `S(n) = 1 + P/n`,
`P_{ij} = A'_{ij}/(ρ_i - ρ_j)`, into `N(n) = S(n) M'(n) S(n+1)⁻¹ = Λ(n) + O(1/n²)` with
`Λ(n) = diag(ρ_j + A'_{jj}/n) = diag(ρ_j (1 + α_j/n))`, `α_j = A'_{jj}/ρ_j`.
-/
import lev_aux4

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.LV

/-- The data of the shearing. -/
structure Shear where
  Bal : ℕ → Matrix (Fin 3) (Fin 3) ℂ
  Qinf : Matrix (Fin 3) (Fin 3) ℂ
  A₁ : Matrix (Fin 3) (Fin 3) ℂ
  C₁ : ℝ
  hC₁ : 0 ≤ C₁
  n₁ : ℕ
  hBal : ∀ n, n₁ ≤ n → ∀ i j, ‖(Bal n - Qinf - ((n : ℂ)⁻¹) • A₁) i j‖ ≤ C₁ / (n : ℝ) ^ 2
  Y : Matrix (Fin 3) (Fin 3) ℂ
  hY : Y.det ≠ 0
  ρ : Fin 3 → ℂ
  hρ : Function.Injective ρ
  hρ0 : ∀ j, ρ j ≠ 0
  hYQ : Y * Qinf = Matrix.diagonal ρ * Y

namespace Shear

variable (T : Shear)

/-- `M'(n) = Y Bal(n) Y⁻¹`. -/
def Mp (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := T.Y * T.Bal n * T.Y⁻¹

/-- `A' = Y A₁ Y⁻¹`. -/
def Ap : Matrix (Fin 3) (Fin 3) ℂ := T.Y * T.A₁ * T.Y⁻¹

/-- `E(n) = M'(n) - D - A'/n`. -/
def Ep (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  T.Mp n - Matrix.diagonal T.ρ - ((n : ℂ)⁻¹) • T.Ap

/-- The shearing matrix `P`. -/
def P : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => if i = j then 0 else T.Ap i j / (T.ρ i - T.ρ j)

/-- `Δ = diag(A'_{jj})`. -/
def Δ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal fun j => T.Ap j j

/-- `S(n) = 1 + P/n`. -/
def S (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := 1 + ((n : ℂ)⁻¹) • T.P

/-- The exponents `α_j = A'_{jj}/ρ_j`. -/
def α (j : Fin 3) : ℂ := T.Ap j j / T.ρ j

/-- `Λ(n) = diag(λ_j(n))`. -/
def Λ (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal fun j => lamA T.ρ T.α j n

/-- The sheared matrices `N(n) = S(n) M'(n) S(n+1)⁻¹`. -/
def Nm (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := T.S n * T.Mp n * (T.S (n + 1))⁻¹

/-- `C' = 9 C₁ nrm Y nrm Y⁻¹`. -/
def Cp : ℝ := 9 * T.C₁ * nrm T.Y * nrm T.Y⁻¹

/-- The constant `K₃`. -/
def K₃ : ℝ :=
  T.Cp + nrm (T.P * T.Ap) + nrm T.P * T.Cp + nrm (T.Δ * T.P) +
    (nrm (Matrix.diagonal T.ρ) + nrm T.Δ) * nrm T.P

theorem hYu : IsUnit T.Y.det := isUnit_iff_ne_zero.mpr T.hY

theorem YQY : T.Y * T.Qinf * T.Y⁻¹ = Matrix.diagonal T.ρ := by
  rw [T.hYQ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ T.hYu, Matrix.mul_one]

theorem Ep_eq (n : ℕ) : T.Ep n = T.Y * (T.Bal n - T.Qinf - ((n : ℂ)⁻¹) • T.A₁) * T.Y⁻¹ := by
  unfold Ep Mp Ap
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, T.YQY]

theorem Λ_eq (n : ℕ) : T.Λ n = Matrix.diagonal T.ρ + ((n : ℂ)⁻¹) • T.Δ := by
  unfold Λ Δ
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, lamA, α,
      smul_eq_mul, mul_add, mul_one, mul_div_assoc', mul_div_assoc',
      mul_div_cancel_left₀ _ (T.hρ0 i), div_eq_inv_mul]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
      smul_zero, add_zero]

theorem key : T.Ap + T.P * Matrix.diagonal T.ρ - Matrix.diagonal T.ρ * T.P = T.Δ := by
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold P Δ
  by_cases h : i = j
  · subst h
    rw [Matrix.of_apply, if_pos rfl, Matrix.diagonal_apply_eq]
    ring
  · rw [Matrix.of_apply, if_neg h, Matrix.diagonal_apply_ne _ h]
    have hne : T.ρ i - T.ρ j ≠ 0 := sub_ne_zero.mpr fun e => h (T.hρ e)
    field_simp
    ring

theorem Mp_eq (n : ℕ) : T.Mp n = Matrix.diagonal T.ρ + ((n : ℂ)⁻¹) • T.Ap + T.Ep n := by
  unfold Ep
  abel

theorem SM_sub (n : ℕ) : T.S n * T.Mp n - T.Λ n * T.S n =
    T.Ep n + ((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.P * T.Ap) + (n : ℂ)⁻¹ • (T.P * T.Ep n) -
      ((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.Δ * T.P) := by
  have hkey : T.P * Matrix.diagonal T.ρ = T.Δ - T.Ap + Matrix.diagonal T.ρ * T.P := by
    rw [← T.key]
    abel
  rw [T.Mp_eq, T.Λ_eq]
  unfold S
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul, hkey]
  module

theorem S_succ (n : ℕ) : T.S (n + 1) = T.S n + ((((n : ℂ) + 1)⁻¹ - (n : ℂ)⁻¹)) • T.P := by
  unfold S
  push_cast
  rw [sub_smul]
  abel

theorem SM_sub' (n : ℕ) : T.S n * T.Mp n - T.Λ n * T.S (n + 1) =
    (T.S n * T.Mp n - T.Λ n * T.S n) - ((((n : ℂ) + 1)⁻¹ - (n : ℂ)⁻¹)) • (T.Λ n * T.P) := by
  rw [T.S_succ, Matrix.mul_add, Matrix.mul_smul]
  abel

/-! ### Norm bounds -/

theorem nrm_one : nrm (1 : Matrix (Fin 3) (Fin 3) ℂ) = 3 := by
  unfold nrm
  simp [Fin.sum_univ_three, Matrix.one_apply]
  norm_num

theorem nrm_Ep_le (n : ℕ) (hn : T.n₁ ≤ n) : nrm (T.Ep n) ≤ T.Cp / (n : ℝ) ^ 2 := by
  rw [T.Ep_eq]
  have h1 := nrm_le_of_entries _ _ (T.hBal n hn)
  have hY1 := nrm_nonneg T.Y
  have hY2 := nrm_nonneg T.Y⁻¹
  calc nrm (T.Y * (T.Bal n - T.Qinf - ((n : ℂ)⁻¹) • T.A₁) * T.Y⁻¹)
      ≤ nrm (T.Y * (T.Bal n - T.Qinf - ((n : ℂ)⁻¹) • T.A₁)) * nrm T.Y⁻¹ := nrm_mul_le _ _
    _ ≤ nrm T.Y * nrm (T.Bal n - T.Qinf - ((n : ℂ)⁻¹) • T.A₁) * nrm T.Y⁻¹ :=
        mul_le_mul_of_nonneg_right (nrm_mul_le _ _) hY2
    _ ≤ nrm T.Y * (9 * (T.C₁ / (n : ℝ) ^ 2)) * nrm T.Y⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hY1) hY2
    _ = T.Cp / (n : ℝ) ^ 2 := by unfold Cp; ring

theorem Cp_nonneg : 0 ≤ T.Cp := by
  unfold Cp
  have := nrm_nonneg T.Y
  have := nrm_nonneg T.Y⁻¹
  have := T.hC₁
  positivity

theorem norm_inv_nat (n : ℕ) : ‖((n : ℂ))⁻¹‖ = 1 / (n : ℝ) := by
  rw [norm_inv, Complex.norm_natCast, one_div]

theorem norm_inv_sub (n : ℕ) (hn : 1 ≤ n) :
    ‖((n : ℂ) + 1)⁻¹ - (n : ℂ)⁻¹‖ ≤ 1 / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have e : ((n : ℂ) + 1)⁻¹ - (n : ℂ)⁻¹ = -(((n : ℂ) * ((n : ℂ) + 1))⁻¹) := by
    field_simp
    ring
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [e, norm_neg, norm_inv, norm_mul, Complex.norm_natCast,
    show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
  push_cast
  rw [one_div]
  exact inv_anti₀ (by positivity) (by nlinarith)

theorem nrm_Λ_le (n : ℕ) (hn : 1 ≤ n) :
    nrm (T.Λ n) ≤ nrm (Matrix.diagonal T.ρ) + nrm T.Δ := by
  rw [T.Λ_eq]
  refine (nrm_add_le _ _).trans ?_
  rw [nrm_smul, norm_inv_nat]
  have h1 : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hn
  have := nrm_nonneg T.Δ
  nlinarith

theorem nrm_diff_le (n : ℕ) (hn : T.n₁ ≤ n) (hn1 : 1 ≤ n) :
    nrm (T.S n * T.Mp n - T.Λ n * T.S (n + 1)) ≤ T.K₃ / (n : ℝ) ^ 2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hE := T.nrm_Ep_le n hn
  have hCp := T.Cp_nonneg
  have hP := nrm_nonneg T.P
  have hinv : ‖(n : ℂ)⁻¹‖ = 1 / (n : ℝ) := norm_inv_nat n
  have hinv2 : ‖(n : ℂ)⁻¹ * (n : ℂ)⁻¹‖ = 1 / (n : ℝ) ^ 2 := by
    rw [norm_mul, hinv]; ring
  have h1 : nrm (T.Ep n + ((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.P * T.Ap) +
      (n : ℂ)⁻¹ • (T.P * T.Ep n) - ((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.Δ * T.P)) ≤
      (T.Cp + nrm (T.P * T.Ap) + nrm T.P * T.Cp + nrm (T.Δ * T.P)) / (n : ℝ) ^ 2 := by
    have hPE : nrm (T.P * T.Ep n) ≤ nrm T.P * (T.Cp / (n : ℝ) ^ 2) :=
      (nrm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hE hP)
    have hn3 : 1 / (n : ℝ) * (nrm T.P * (T.Cp / (n : ℝ) ^ 2)) ≤ nrm T.P * T.Cp / (n : ℝ) ^ 2 := by
      rw [show 1 / (n : ℝ) * (nrm T.P * (T.Cp / (n : ℝ) ^ 2)) =
        (nrm T.P * T.Cp / (n : ℝ) ^ 2) * (1 / n) by ring]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one hnr]
      exact hnr1
    calc nrm (T.Ep n + ((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.P * T.Ap) + (n : ℂ)⁻¹ • (T.P * T.Ep n) -
          ((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.Δ * T.P))
        ≤ nrm (T.Ep n) + nrm (((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.P * T.Ap)) +
          nrm ((n : ℂ)⁻¹ • (T.P * T.Ep n)) + nrm (((n : ℂ)⁻¹ * (n : ℂ)⁻¹) • (T.Δ * T.P)) := by
          refine (nrm_sub_le _ _).trans (add_le_add_left ?_ _)
          exact (nrm_add_le _ _).trans (add_le_add_left (nrm_add_le _ _) _)
      _ ≤ T.Cp / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 * nrm (T.P * T.Ap) +
          1 / (n : ℝ) * (nrm T.P * (T.Cp / (n : ℝ) ^ 2)) + 1 / (n : ℝ) ^ 2 * nrm (T.Δ * T.P) := by
          rw [nrm_smul, nrm_smul, nrm_smul, hinv2, hinv]
          gcongr
      _ ≤ T.Cp / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 * nrm (T.P * T.Ap) +
          nrm T.P * T.Cp / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 * nrm (T.Δ * T.P) := by gcongr
      _ = _ := by ring
  have h2 : nrm ((((n : ℂ) + 1)⁻¹ - (n : ℂ)⁻¹) • (T.Λ n * T.P)) ≤
      (nrm (Matrix.diagonal T.ρ) + nrm T.Δ) * nrm T.P / (n : ℝ) ^ 2 := by
    rw [nrm_smul]
    have hΛ := (nrm_mul_le (T.Λ n) T.P).trans
      (mul_le_mul_of_nonneg_right (T.nrm_Λ_le n hn1) hP)
    have hc := norm_inv_sub n hn1
    calc ‖((n : ℂ) + 1)⁻¹ - (n : ℂ)⁻¹‖ * nrm (T.Λ n * T.P)
        ≤ 1 / (n : ℝ) ^ 2 * ((nrm (Matrix.diagonal T.ρ) + nrm T.Δ) * nrm T.P) :=
          mul_le_mul hc hΛ (nrm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [T.SM_sub', T.SM_sub]
  refine (nrm_sub_le _ _).trans ?_
  unfold K₃
  calc _ ≤ (T.Cp + nrm (T.P * T.Ap) + nrm T.P * T.Cp + nrm (T.Δ * T.P)) / (n : ℝ) ^ 2 +
        (nrm (Matrix.diagonal T.ρ) + nrm T.Δ) * nrm T.P / (n : ℝ) ^ 2 := add_le_add h1 h2
    _ = _ := by ring

/-! ### Invertibility of `S(n)` -/

theorem S_tendsto : Tendsto T.S atTop (𝓝 1) := by
  refine tendsto_of_nrm (b := fun n => 1 / (n : ℝ) * nrm T.P) ?_
    (Eventually.of_forall fun n => ?_)
  · have := tendsto_one_div_atTop_nhds_zero_nat.mul_const (nrm T.P)
    rwa [zero_mul] at this
  · unfold S
    rw [add_sub_cancel_left, nrm_smul, norm_inv_nat]

theorem Sinv_tendsto : Tendsto (fun n => (T.S n)⁻¹) atTop (𝓝 1) := by
  have hri : ContinuousAt (Ring.inverse : ℂ → ℂ) (1 : Matrix (Fin 3) (Fin 3) ℂ).det := by
    rw [Matrix.det_one, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have := (continuousAt_matrix_inv (1 : Matrix (Fin 3) (Fin 3) ℂ) hri).tendsto.comp T.S_tendsto
  rwa [inv_one] at this

theorem eventually_S : ∀ᶠ n in atTop, (T.S n).det ≠ 0 ∧ nrm ((T.S n)⁻¹) ≤ 4 := by
  have h1 : ∀ᶠ n in atTop, (T.S n).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto (1 : Matrix (Fin 3) (Fin 3) ℂ)).comp
      T.S_tendsto).eventually_ne (by simp)
  have h2 := nrm_tendsto_zero_of_tendsto T.Sinv_tendsto
  have h3 : ∀ᶠ n in atTop, nrm ((T.S n)⁻¹ - 1) ≤ 1 :=
    (h2.eventually (gt_mem_nhds one_pos)).mono fun n hn => hn.le
  filter_upwards [h1, h3] with n hn1 hn3
  refine ⟨hn1, ?_⟩
  calc nrm ((T.S n)⁻¹) = nrm (((T.S n)⁻¹ - 1) + 1) := by rw [sub_add_cancel]
    _ ≤ nrm ((T.S n)⁻¹ - 1) + nrm 1 := nrm_add_le _ _
    _ ≤ 1 + 3 := by rw [nrm_one]; linarith
    _ = 4 := by norm_num

theorem Nm_sub_Λ (n : ℕ) (hdet : (T.S (n + 1)).det ≠ 0) :
    T.Nm n - T.Λ n = (T.S n * T.Mp n - T.Λ n * T.S (n + 1)) * (T.S (n + 1))⁻¹ := by
  unfold Nm
  rw [Matrix.sub_mul, Matrix.mul_assoc (T.Λ n), Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.mul_one]

theorem Nm_mul_S (n : ℕ) (hdet : (T.S (n + 1)).det ≠ 0) :
    T.Nm n * T.S (n + 1) = T.S n * T.Mp n := by
  unfold Nm
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]

/-- **The sheared system is `Λ(n) + O(1/n²)`.** -/
theorem exists_bound : ∃ (K₂ : ℝ) (n₀ : ℕ), 0 ≤ K₂ ∧ 1 ≤ n₀ ∧
    (∀ n, n₀ ≤ n → (T.S n).det ≠ 0) ∧
    ∀ n, n₀ ≤ n → nrm (RR T.Nm (lamA T.ρ T.α) n) ≤ K₂ / (n : ℝ) ^ 2 := by
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp T.eventually_S
  have hK₃ : 0 ≤ T.K₃ := by
    unfold K₃
    have := T.Cp_nonneg
    have := nrm_nonneg (T.P * T.Ap)
    have := nrm_nonneg T.P
    have := nrm_nonneg (T.Δ * T.P)
    have := nrm_nonneg (Matrix.diagonal T.ρ)
    have := nrm_nonneg T.Δ
    positivity
  refine ⟨4 * T.K₃, T.n₁ + n₂ + 1, by positivity, by omega, fun n hn => (hn₂ n (by omega)).1,
    fun n hn => ?_⟩
  have hdet := (hn₂ (n + 1) (by omega)).1
  have hinv := (hn₂ (n + 1) (by omega)).2
  show nrm (T.Nm n - T.Λ n) ≤ _
  rw [T.Nm_sub_Λ n hdet]
  calc nrm ((T.S n * T.Mp n - T.Λ n * T.S (n + 1)) * (T.S (n + 1))⁻¹)
      ≤ nrm (T.S n * T.Mp n - T.Λ n * T.S (n + 1)) * nrm ((T.S (n + 1))⁻¹) := nrm_mul_le _ _
    _ ≤ T.K₃ / (n : ℝ) ^ 2 * 4 :=
        mul_le_mul (T.nrm_diff_le n (by omega) (by omega)) hinv (nrm_nonneg _) (by positivity)
    _ = 4 * T.K₃ / (n : ℝ) ^ 2 := by ring

end Shear

end Pfq54.LV
