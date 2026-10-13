import Z_integral

open Finset
open scoped Matrix

noncomputable section

namespace Pfq54.CA

open Pfq54

/-- The companion matrix `[[0,0,c₀],[1,0,c₁],[0,1,c₂]]` (copy of `BP.companionMat`). -/
def companionMat' (c₀ c₁ c₂ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, c₀; 1, 0, c₁; 0, 1, c₂]

/-- The readout rows `R` (copy of `BP.Rbr`). -/
def Rbr' : Matrix (Fin 3) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 0, -1/2, 1/4; 0, 0, 0, -1/6]

/-- `y_n = (S_{0,n}, S_{3,n}, S_{4,n}) / C_n`. -/
def y (n : ℕ) : Fin 3 → ℚ := ![S0 n / Cn n, S3 n / Cn n, S4 n / Cn n]

/-- The lift `x_n = (y₀, 0, -2y₁ - 3y₂, -6y₂)` with `R x_n = y_n`. -/
def Lx : Matrix (Fin 4) (Fin 3) ℚ := !![1, 0, 0; 0, 0, 0; 0, -2, -3; 0, 0, -6]

def x (n : ℕ) : Fin 4 → ℚ := Lx *ᵥ y n

theorem Rbr_Lx : Rbr' * Lx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rbr', Lx, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem Rbr_x (n : ℕ) : Rbr' *ᵥ x n = y n := by
  rw [x, Matrix.mulVec_mulVec, Rbr_Lx, Matrix.one_mulVec]

/-- The matrix `X_n`: the identity with first column replaced by `x_n`. -/
def Xm (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of fun i j => if j = 0 then x n i else if i = j then 1 else 0

theorem Xm_mulVec_e0 (n : ℕ) : Xm n *ᵥ ![1, 0, 0, 0] = x n := by
  ext i
  simp [Xm, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem Xm_det (n : ℕ) : (Xm n).det = y n 0 := by
  have h0 : (Xm n).submatrix Fin.succ Fin.succ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Fin.succAbove_zero, h0, Matrix.det_one, mul_one]
  simp [Xm, x, Lx, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem S0_zero : S0 0 = 1 := by
  simp [S0, U, coeffJet, upperJet, lowerJet, jet]

theorem S3_zero : S3 0 = 0 := by
  simp [S3, harm]

theorem S4_zero : S4 0 = 0 := by
  simp [S4, harm]

theorem Cn_zero : Cn 0 = 1 := by
  simp [Cn]

theorem y_zero : y 0 = ![1, 0, 0] := by
  ext i
  fin_cases i <;> simp [y, S0_zero, S3_zero, S4_zero, Cn_zero]

theorem y0_pos (n : ℕ) : 0 < y n 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [y_zero]; norm_num
  · have hS := (BP.Z_integral n hn).2.2.2
    have hC : 0 < Cn n := by unfold Cn; positivity
    simp only [y, Matrix.cons_val_zero]
    positivity

theorem Xm_isUnit (n : ℕ) : IsUnit (Xm n).det := by
  rw [Xm_det]
  exact isUnit_iff_ne_zero.mpr (y0_pos n).ne'

theorem Xm_zero : Xm 0 = 1 := by
  ext i j
  simp only [Xm, Matrix.of_apply, Matrix.one_apply, x, y_zero, Lx]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The step matrices. -/
def MG (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := (Xm n)⁻¹ * Xm (n + 1)

theorem walk_MG (n : ℕ) : walk MG n = Xm n := by
  induction n with
  | zero => rw [Aux.walk_zero, Xm_zero]
  | succ n ih =>
    rw [Aux.walk_succ, ih, MG, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Xm_isUnit n),
      Matrix.one_mul]

/-- The Krylov matrices (columns `x_n, x_{n+1}, x_{n+2}`), and their readouts. -/
def Ym (n : ℕ) : Matrix (Fin 4) (Fin 3) ℚ := Matrix.of fun i j => x (n + j) i

def Y3 (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i j => y (n + j) i

def Um (n : ℕ) : Matrix (Fin 4) (Fin 3) ℚ := (Xm n)⁻¹ * Ym n

def cvec (n : ℕ) : Fin 3 → ℚ := (Y3 n)⁻¹ *ᵥ y (n + 3)

theorem Y3_mulVec (n : ℕ) (c : Fin 3 → ℚ) :
    Y3 n *ᵥ c = c 0 • y n + c 1 • y (n + 1) + c 2 • y (n + 2) := by
  ext i
  simp [Y3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem y_rec (n : ℕ) (hCas : (Y3 n).det ≠ 0) :
    y (n + 3) = cvec n 0 • y n + cvec n 1 • y (n + 1) + cvec n 2 • y (n + 2) := by
  rw [← Y3_mulVec, cvec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCas),
    Matrix.one_mulVec]

theorem x_rec (n : ℕ) (hCas : (Y3 n).det ≠ 0) :
    x (n + 3) = cvec n 0 • x n + cvec n 1 • x (n + 1) + cvec n 2 • x (n + 2) := by
  simp only [x]
  rw [y_rec n hCas, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul]

theorem Ym_succ (n : ℕ) (hCas : (Y3 n).det ≠ 0) :
    Ym (n + 1) = Ym n * companionMat' (cvec n 0) (cvec n 1) (cvec n 2) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases j
  · simp [Ym, companionMat', add_assoc]
  · simp [Ym, companionMat', add_assoc]
  · simp only [Ym, Matrix.of_apply, companionMat']
    show x (n + 3) i = _
    rw [x_rec n hCas]
    simp
    ring

theorem Y3_succ (n : ℕ) (hCas : (Y3 n).det ≠ 0) :
    Y3 (n + 1) = Y3 n * companionMat' (cvec n 0) (cvec n 1) (cvec n 2) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases j
  · simp [Y3, companionMat', add_assoc]
  · simp [Y3, companionMat', add_assoc]
  · simp only [Y3, Matrix.of_apply, companionMat']
    show y (n + 3) i = _
    rw [y_rec n hCas]
    simp
    ring

theorem det_companion (c₀ c₁ c₂ : ℚ) : (companionMat' c₀ c₁ c₂).det = c₀ := by
  rw [Matrix.det_fin_three]
  simp [companionMat']

theorem c0_ne (n : ℕ) (hCas : ∀ n, (Y3 n).det ≠ 0) : cvec n 0 ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (Y3_succ n (hCas n))
  rw [Matrix.det_mul, det_companion, h0, mul_zero] at h
  exact hCas (n + 1) h

theorem Um_e0 (n : ℕ) : Um n *ᵥ ![1, 0, 0] = ![1, 0, 0, 0] := by
  have h : Ym n *ᵥ ![1, 0, 0] = x n := by
    ext i; simp [Ym, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [Um, ← Matrix.mulVec_mulVec, h, ← Xm_mulVec_e0, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (Xm_isUnit n), Matrix.one_mulVec]

theorem cob (n : ℕ) (hCas : (Y3 n).det ≠ 0) :
    MG n * Um (n + 1) = Um n * companionMat' (cvec n 0) (cvec n 1) (cvec n 2) := by
  rw [MG, Um, Um, Matrix.mul_assoc, ← Matrix.mul_assoc (Xm (n + 1)),
    Matrix.mul_nonsing_inv _ (Xm_isUnit (n + 1)), Matrix.one_mul, Matrix.mul_assoc, ← Ym_succ n hCas]

theorem bridge (n : ℕ) : ![Qa n, P3a n, P4a n] =
    ((-1 : ℚ) ^ n) • (Rbr' *ᵥ (walk MG n *ᵥ ![1, 0, 0, 0])) := by
  rw [walk_MG, Xm_mulVec_e0, Rbr_x]
  ext i
  fin_cases i <;> simp [y, Qa, P3a, P4a, mul_div_assoc]

theorem det_RU0 : (Rbr' * Um 0).det = (Y3 0).det := by
  rw [Um, Xm_zero, inv_one, Matrix.one_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  have h := congrFun (Rbr_x (0 + j)) i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h
  simp only [Ym, Y3, Matrix.of_apply]
  exact h

/-- **The companion data, from the nonvanishing of the Casoratians.** -/
theorem companion_data_of (hCas : ∀ n, (Y3 n).det ≠ 0) :
    ∃ (MG : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (Um : ℕ → Matrix (Fin 4) (Fin 3) ℚ) (c₀ c₁ c₂ : ℕ → ℚ),
    (∀ n, MG n * Um (n + 1) = Um n * companionMat' (c₀ n) (c₁ n) (c₂ n)) ∧
      (∀ n, Um n *ᵥ ![1, 0, 0] = ![1, 0, 0, 0]) ∧ (∀ n, c₀ n ≠ 0) ∧
      (∀ n, ![Qa n, P3a n, P4a n] = ((-1 : ℚ) ^ n) • (Rbr' *ᵥ (walk MG n *ᵥ ![1, 0, 0, 0]))) ∧
      (Rbr' * Um 0).det ≠ 0 :=
  ⟨MG, Um, fun n => cvec n 0, fun n => cvec n 1, fun n => cvec n 2, fun n => cob n (hCas n), Um_e0,
    fun n => c0_ne n hCas, bridge, by rw [det_RU0]; exact hCas 0⟩

end Pfq54.CA
