/-
# Auxiliary lemmas for `dual_limit` in `error_bound.lean` (sorry-free)

Casting the rational dual walk to `ℂ`, the determinant of the block matrix `G(n)`, the
eigenvalues of `Q_∞` as roots of `χ`, separability of `χ`, the cyclic-determinant criterion
`(Y^{-T} w)₁ ≠ 0`, decay of the balanced Meijer-G state, the selection of the recessive mode and
the reindexing of the modal basis so that the recessive mode comes first.
-/
import Pfq54_aux
import dual_mode_transfer
import modal_basis
import meijerG_initial
import meijerG_decay
import spectral_certificate

open Finset Filter Topology Polynomial
open scoped Matrix

noncomputable section

namespace Pfq54.DL

open Pfq54 Pfq54.BP

/-- `Î_G`. -/
def IGh (A B : ℤ) : Matrix (Fin 2) (Fin 3) ℚ := !![2 * B, -3 * A - 2 * B, 3 * A; 0, 0, 6]

/-- `Δ(n)⁻¹ (1, 10n+1, (10n+1)²)`. -/
def hvD (n : ℕ) : Fin 3 → ℚ :=
  (∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1))⁻¹ • ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]

/-- The cast `ℚ → ℂ` on `3 × 3` matrices. -/
def cC (M : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℂ := (Rat.castHom ℂ).mapMatrix M

/-- The cast `ℚ → ℂ` on vectors. -/
def castV (u : Fin 3 → ℚ) : Fin 3 → ℂ := fun i => (u i : ℂ)

/-! ### Casting -/

theorem cC_apply (M : Matrix (Fin 3) (Fin 3) ℚ) (i j : Fin 3) : cC M i j = (M i j : ℂ) := rfl

theorem cC_det (M : Matrix (Fin 3) (Fin 3) ℚ) : (cC M).det = (M.det : ℂ) :=
  ((Rat.castHom ℂ).map_det M).symm

theorem walk_cC (Q : ℕ → Matrix (Fin 3) (Fin 3) ℚ) (n : ℕ) :
    walk (fun m => cC (Q m)) n = cC (walk Q n) := by
  induction n with
  | zero => rw [Aux.walk_zero, Aux.walk_zero]; exact (map_one _).symm
  | succ n ih => rw [Aux.walk_succ, Aux.walk_succ, ih]; exact (map_mul _ _ _).symm

theorem inv_cC (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : M.det ≠ 0) : (cC M)⁻¹ = cC M⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [cC, cC, ← map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM), map_one]

theorem transpose_cC (M : Matrix (Fin 3) (Fin 3) ℚ) : (cC M)ᵀ = cC Mᵀ :=
  (Matrix.transpose_map (f := ⇑(Rat.castHom ℂ)) (M := M)).symm

theorem cC_mulVec (M : Matrix (Fin 3) (Fin 3) ℚ) (u : Fin 3 → ℚ) :
    cC M *ᵥ castV u = castV (M *ᵥ u) :=
  funext fun i => ((Rat.castHom ℂ).map_mulVec M u i).symm

theorem castV_dot (v u : Fin 3 → ℚ) : castV v ⬝ᵥ castV u = ((v ⬝ᵥ u : ℚ) : ℂ) :=
  ((Rat.castHom ℂ).map_dotProduct v u).symm

theorem castV_smul (q : ℚ) (u : Fin 3 → ℚ) : castV (q • u) = (q : ℂ) • castV u := by
  funext i
  simp [castV]

/-! ### The block determinant -/

theorem det_block (M : Matrix (Fin 4) (Fin 4) ℚ)
    (hrow : ∀ j : Fin 4, M 3 j = if j = 3 then -1 else 0) :
    M.det = -(M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row M 3, Fin.sum_univ_four, hrow, hrow, hrow, hrow]
  simp
  rw [show Fin.succAbove (3 : Fin 4) = Fin.castSucc from Fin.succAbove_last]
  norm_num

/-! ### Spectral facts -/

theorem eig_root (Qinf Y : Matrix (Fin 3) (Fin 3) ℂ) (hY : Y.det ≠ 0) (ρ : Fin 3 → ℂ)
    (heig : ∀ i, Y i ᵥ* Qinf = ρ i • Y i) (i : Fin 3) : Qinf.charpoly.eval (ρ i) = 0 := by
  rw [Matrix.eval_charpoly]
  have hYi : Y i ≠ 0 := fun h => hY (Matrix.det_eq_zero_of_row_eq_zero i fun j => congrFun h j)
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨Y i, hYi, ?_⟩
  rw [Matrix.vecMul_sub, heig i, sub_eq_zero, Matrix.scalar_apply]
  funext j
  rw [Matrix.vecMul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem root_of_charpoly (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hchar : Qinf.charpoly = chi.map (algebraMap ℚ ℂ)) (z : ℂ) (hz : Qinf.charpoly.eval z = 0) :
    z ^ 3 - ((chiA : ℝ) : ℂ) * z ^ 2 + ((chiB : ℝ) : ℂ) * z - ((chiC : ℝ) : ℂ) = 0 := by
  rw [hchar, chi_eval.2] at hz
  exact hz

theorem real_root_is_eig (Qinf : Matrix (Fin 3) (Fin 3) ℂ) (ρ : Fin 3 → ℂ)
    (hρ : Function.Injective ρ) (hroot : ∀ i, Qinf.charpoly.eval (ρ i) = 0) (r : ℂ)
    (hr : Qinf.charpoly.eval r = 0) : ∃ i, ρ i = r := by
  have hne : Qinf.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hcard : Qinf.charpoly.roots.card = 3 := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  by_contra hcon
  have hcon' : ∀ i, ρ i ≠ r := fun i h => hcon ⟨i, h⟩
  have hsub : insert r (Finset.univ.image ρ) ⊆ Qinf.charpoly.roots.toFinset := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_image] at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    rcases hz with rfl | ⟨i, _, rfl⟩
    · exact hr
    · exact hroot i
  have h1 : (insert r (Finset.univ.image ρ)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hρ, Finset.card_univ,
      Fintype.card_fin]
    rw [Finset.mem_image]
    rintro ⟨i, _, hi⟩
    exact hcon' i hi
  have h2 := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  rw [h1, hcard] at h2
  omega

theorem chi_deriv_eval (t : ℂ) :
    (derivative (chi.map (algebraMap ℚ ℂ))).eval t =
      3 * t ^ 2 - 2 * ((chiA : ℝ) : ℂ) * t + ((chiB : ℝ) : ℂ) := by
  simp [chi]
  ring

theorem no_common_root (t : ℂ)
    (h1 : t ^ 3 - ((chiA : ℝ) : ℂ) * t ^ 2 + ((chiB : ℝ) : ℂ) * t - ((chiC : ℝ) : ℂ) = 0)
    (h2 : 3 * t ^ 2 - 2 * ((chiA : ℝ) : ℂ) * t + ((chiB : ℝ) : ℂ) = 0) : False := by
  obtain ⟨r, _, _, hroot⟩ := ivt_root
  have hdisc := disc_neg
  set a : ℝ := (chiA : ℝ) with ha
  set b : ℝ := (chiB : ℝ) with hb
  set c : ℝ := (chiC : ℝ) with hc
  have hc' : c = r ^ 3 - a * r ^ 2 + b * r := by linarith
  set p := r - a with hp
  set q := b + (r - a) * r with hq
  have hid : 18 * a * b * c - 4 * a ^ 3 * c + a ^ 2 * b ^ 2 - 4 * b ^ 3 - 27 * c ^ 2 =
      (p ^ 2 - 4 * q) * (r ^ 2 + p * r + q) ^ 2 := by
    rw [hc', hp, hq]; ring
  have hneg : p ^ 2 - 4 * q < 0 := by
    rw [hid] at hdisc
    nlinarith [sq_nonneg (r ^ 2 + p * r + q)]
  have hfac : t ^ 3 - (a : ℂ) * t ^ 2 + (b : ℂ) * t - (c : ℂ) =
      (t - r) * (t ^ 2 + (p : ℂ) * t + (q : ℂ)) := by
    rw [hc', hp, hq]; push_cast; ring
  have hd : 3 * t ^ 2 - 2 * (a : ℂ) * t + (b : ℂ) =
      (t ^ 2 + (p : ℂ) * t + (q : ℂ)) + (t - r) * (2 * t + (p : ℂ)) := by
    rw [hp, hq]; push_cast; ring
  by_cases ht : t = (r : ℂ)
  · rw [ht] at h2
    have h2r : 3 * r ^ 2 - 2 * a * r + b = 0 := by exact_mod_cast h2
    have h3 : r ^ 2 + p * r + q = 0 := by rw [hp, hq]; linarith
    rw [hid, h3] at hdisc
    simp at hdisc
  · rw [hfac] at h1
    have hquad : t ^ 2 + (p : ℂ) * t + (q : ℂ) = 0 :=
      (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr ht)
    rw [hd, hquad, zero_add] at h2
    have h2t : 2 * t + (p : ℂ) = 0 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ht)
    have ht' : t = ((-p / 2 : ℝ) : ℂ) := by push_cast; linear_combination (1 / 2 : ℂ) * h2t
    rw [ht'] at hquad
    have hreal : (-p / 2) ^ 2 + p * (-p / 2) + q = 0 := by exact_mod_cast hquad
    nlinarith

theorem chi_separable (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hchar : Qinf.charpoly = chi.map (algebraMap ℚ ℂ)) : Qinf.charpoly.Separable := by
  have hne : Qinf.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  rw [← Polynomial.nodup_roots_iff_of_splits hne (IsAlgClosed.splits _),
    Multiset.nodup_iff_count_le_one]
  intro t
  rw [Polynomial.count_roots]
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨h1, h2⟩ := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mp hlt
  rw [Polynomial.IsRoot, hchar] at h1 h2
  rw [chi_eval.2] at h1
  rw [chi_deriv_eval] at h2
  exact no_common_root t h1 h2

theorem det_of_charpoly (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hchar : Qinf.charpoly = chi.map (algebraMap ℚ ℂ)) : Qinf.det ≠ 0 := by
  have hc : (chiC : ℚ) ≠ 0 := by
    have := chiC_pos
    exact_mod_cast this.ne'
  have hcoeff : chi.coeff 0 = -chiC := by simp [chi]
  rw [Matrix.det_eq_sign_charpoly_coeff, hchar, Polynomial.coeff_map, hcoeff, Fintype.card_fin]
  simp [hc]

/-! ### The cyclic determinant -/

theorem cyclic_ne_zero (Y Qinf : Matrix (Fin 3) (Fin 3) ℂ) (hY : Y.det ≠ 0) (hQ : Qinf.det ≠ 0)
    (ρ : Fin 3 → ℂ) (heig : ∀ i, Y i ᵥ* Qinf = ρ i • Y i) (w : Fin 3 → ℂ)
    (hcyc : (Matrix.of ![w, (Qinf⁻¹)ᵀ *ᵥ w, ((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ w]).det ≠ 0) :
    ((Y⁻¹)ᵀ *ᵥ w) 0 ≠ 0 := by
  set D := Matrix.diagonal ρ with hD
  have hYQ : Y * Qinf = D * Y := by
    ext i j
    have h := congrFun (heig i) j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, hD, Matrix.diagonal_mul]
    exact h
  have hρ0 : ∀ i, ρ i ≠ 0 := by
    have h := congrArg Matrix.det hYQ
    rw [Matrix.det_mul, Matrix.det_mul, hD, Matrix.det_diagonal] at h
    have hprod : ∏ i, ρ i ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      exact mul_ne_zero hY hQ h
    exact fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  have hDinv : D⁻¹ = Matrix.diagonal fun i => (ρ i)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hρ0 i)
  have hDu : IsUnit D.det := by
    rw [isUnit_iff_ne_zero, hD, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hρ0 i
  have hQu : IsUnit Qinf.det := isUnit_iff_ne_zero.mpr hQ
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have h1 : Y * Qinf⁻¹ = D⁻¹ * Y := by
    calc Y * Qinf⁻¹ = D⁻¹ * (D * Y) * Qinf⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.one_mul]
      _ = D⁻¹ * (Y * Qinf) * Qinf⁻¹ := by rw [hYQ]
      _ = D⁻¹ * Y := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.mul_one]
  have key : (Qinf⁻¹)ᵀ * Yᵀ = Yᵀ * D⁻¹ := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_mul, hDinv, Matrix.diagonal_transpose]
  have hstep : ∀ x : Fin 3 → ℂ, (Qinf⁻¹)ᵀ *ᵥ (x ᵥ* Y) = (D⁻¹ *ᵥ x) ᵥ* Y := by
    intro x
    rw [← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, key,
      ← Matrix.mulVec_mulVec]
  set b := (Y⁻¹)ᵀ *ᵥ w with hb
  have hw : w = b ᵥ* Y := by
    rw [hb, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hYu, Matrix.transpose_one, Matrix.one_mulVec]
  set N : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.of ![b, D⁻¹ *ᵥ b, D⁻¹ *ᵥ (D⁻¹ *ᵥ b)] with hN
  have hM : Matrix.of ![w, (Qinf⁻¹)ᵀ *ᵥ w, ((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ w] = N * Y := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i
    · show w j = ∑ k, b k * Y k j
      rw [hw]; rfl
    · show ((Qinf⁻¹)ᵀ *ᵥ w) j = ∑ k, (D⁻¹ *ᵥ b) k * Y k j
      rw [hw, hstep]; rfl
    · show (((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ w) j = ∑ k, (D⁻¹ *ᵥ (D⁻¹ *ᵥ b)) k * Y k j
      rw [hw, ← Matrix.mulVec_mulVec, hstep, hstep]; rfl
  intro hb0
  apply hcyc
  rw [hM, Matrix.det_mul]
  refine mul_eq_zero_of_left (Matrix.det_eq_zero_of_column_eq_zero 0 fun i => ?_) _
  fin_cases i
  · exact hb0
  · show (D⁻¹ *ᵥ b) 0 = 0
    rw [hDinv, Matrix.mulVec_diagonal, hb0, mul_zero]
  · show (D⁻¹ *ᵥ (D⁻¹ *ᵥ b)) 0 = 0
    rw [hDinv, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal, hb0, mul_zero, mul_zero]

/-! ### Balancing -/

theorem balance_inv (n : ℕ) (hn : 1 ≤ n) :
    (balance n)⁻¹ = Matrix.diagonal ![1, (n : ℂ)⁻¹, ((n : ℂ) ^ 2)⁻¹] := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine Matrix.inv_eq_left_inv ?_
  rw [balance, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp [hn0]

theorem hv_tendsto :
    Tendsto (fun n : ℕ => ((balance n)⁻¹)ᵀ *ᵥ
      castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]) atTop (𝓝 ![1, 10, 100]) := by
  have he : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * (10 * n + 1)) atTop (𝓝 10) := by
    have h := (tendsto_const_nhds (x := (10 : ℂ))).add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hev : ∀ᶠ n : ℕ in atTop, (((balance n)⁻¹)ᵀ *ᵥ
      castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]) i =
      (![1, (n : ℂ)⁻¹ * (10 * n + 1), ((n : ℂ)⁻¹ * (10 * n + 1)) ^ 2] : Fin 3 → ℂ) i := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [balance_inv n hn, Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
    fin_cases i <;> simp [castV] <;> ring
  refine Tendsto.congr' (f₁ := fun n : ℕ =>
    (![1, (n : ℂ)⁻¹ * (10 * n + 1), ((n : ℂ)⁻¹ * (10 * n + 1)) ^ 2] : Fin 3 → ℂ) i) ?_ ?_
  · filter_upwards [hev] with n hn
    exact hn.symm
  fin_cases i
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  · simpa using he
  · have := he.pow 2
    norm_num at this
    simpa using this

/-! ### Decay of the balanced state -/

theorem state_decay
    (hdec : ∀ n ≥ 1, ∀ k ≤ 3, ‖SG n k‖ ≤ (16 * n + 1 : ℝ) ^ k * dfrak n)
    (hrat : ∀ n ≥ 2, dfrak (n + 1) ≤ eta * dfrak n) (heta : eta < 1) :
    Tendsto (fun n : ℕ => (fun k : Fin 3 => SG n k) ᵥ* (balance n)⁻¹) atTop (𝓝 0) := by
  have hd0 : ∀ n, 0 ≤ dfrak n := fun n => by unfold dfrak; positivity
  have heta0 : 0 ≤ eta := by unfold eta; positivity
  have hgeo : ∀ m : ℕ, dfrak (m + 2) ≤ eta ^ m * dfrak 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc dfrak (m + 1 + 2) = dfrak (m + 2 + 1) := rfl
        _ ≤ eta * dfrak (m + 2) := hrat _ (by omega)
        _ ≤ eta * (eta ^ m * dfrak 2) := by gcongr
        _ = eta ^ (m + 1) * dfrak 2 := by ring
  have hdf : Tendsto dfrak atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one heta0 heta).mul_const (dfrak 2)
    rw [zero_mul] at h
    exact (tendsto_add_atTop_iff_nat 2).mp (squeeze_zero (fun m => hd0 _) hgeo h)
  have hb : Tendsto (fun n : ℕ => 17 ^ 3 * dfrak n) atTop (𝓝 0) := by
    have := hdf.const_mul (17 ^ 3 : ℝ)
    rwa [mul_zero] at this
  refine tendsto_pi_nhds.mpr fun k => ?_
  rw [Pi.zero_apply]
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [balance_inv n hn, Matrix.vecMul_diagonal]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h16 : (16 * n + 1 : ℝ) ≤ 17 * n := by linarith
  have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by rw [Complex.norm_natCast]
  fin_cases k
  · have h := hdec n hn 0 (by norm_num)
    simp only [pow_zero, one_mul] at h
    show ‖SG n 0 * 1‖ ≤ 17 ^ 3 * dfrak n
    rw [mul_one]
    nlinarith [hd0 n]
  · have h := hdec n hn 1 (by norm_num)
    simp only [pow_one] at h
    show ‖SG n 1 * ((n : ℂ))⁻¹‖ ≤ 17 ^ 3 * dfrak n
    rw [norm_mul, norm_inv, hnn]
    calc ‖SG n 1‖ * (n : ℝ)⁻¹ ≤ (17 * n) * dfrak n * (n : ℝ)⁻¹ := by
          gcongr
          exact h.trans (mul_le_mul_of_nonneg_right h16 (hd0 n))
      _ = 17 * dfrak n := by field_simp
      _ ≤ 17 ^ 3 * dfrak n := by nlinarith [hd0 n]
  · have h := hdec n hn 2 (by norm_num)
    show ‖SG n 2 * ((n : ℂ) ^ 2)⁻¹‖ ≤ 17 ^ 3 * dfrak n
    rw [norm_mul, norm_inv, norm_pow, hnn]
    calc ‖SG n 2‖ * ((n : ℝ) ^ 2)⁻¹ ≤ (17 * n) ^ 2 * dfrak n * ((n : ℝ) ^ 2)⁻¹ := by
          gcongr
          exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h16 2)
            (hd0 n))
      _ = 17 ^ 2 * dfrak n := by field_simp
      _ ≤ 17 ^ 3 * dfrak n := by nlinarith [hd0 n]

/-! ### Selecting the recessive mode -/

theorem state_select (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ)
    (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (hB₀ : B₀.det ≠ 0) (hY : Y.det ≠ 0)
    (a : Fin 3 → ℕ → ℂ) (ha : ∀ i n, a i n ≠ 0) (hconv : Tendsto (Yn Q B₀ a) atTop (𝓝 Y))
    (S : ℕ → Fin 3 → ℂ) (hS : ∀ n, S (n + 1) = S n ᵥ* Q n)
    (hdecay : Tendsto (fun n => S n ᵥ* (balance n)⁻¹) atTop (𝓝 0))
    (R : ℝ) (hR : 1 < R)
    (hrate : ∀ i, i ≠ 0 → Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 R)) :
    S 0 = (S 0 ᵥ* B₀⁻¹) 0 • B₀ 0 := by
  obtain ⟨cvec, hcvec⟩ : ∃ c : Fin 3 → ℂ, c = S 0 ᵥ* B₀⁻¹ := ⟨_, rfl⟩
  rw [← hcvec]
  have hBu : IsUnit B₀.det := isUnit_iff_ne_zero.mpr hB₀
  have hSn : ∀ n, S n = cvec ᵥ* (B₀ * walk Q n) := by
    intro n
    induction n with
    | zero =>
      rw [Aux.walk_zero, Matrix.mul_one, hcvec, Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul _ hBu, Matrix.vecMul_one]
    | succ n ih => rw [hS, ih, Aux.walk_succ, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have hdetY : ∀ᶠ n in atTop, (Yn Q B₀ a n).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto Y).comp hconv).eventually_ne hY
  have hinv : Tendsto (fun n => (Yn Q B₀ a n)⁻¹) atTop (𝓝 Y⁻¹) := by
    have hri : ContinuousAt (Ring.inverse : ℂ → ℂ) Y.det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hY
    exact (continuousAt_matrix_inv Y hri).tendsto.comp hconv
  have hkey : ∀ᶠ n in atTop, ∀ i, cvec i * a i n =
      ((S n ᵥ* (balance n)⁻¹) ᵥ* (Yn Q B₀ a n)⁻¹) i := by
    filter_upwards [hdetY, eventually_ge_atTop 1] with n hdn hn i
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hTu : IsUnit (balance n).det := by
      rw [isUnit_iff_ne_zero, balance, Matrix.det_diagonal, Fin.prod_univ_three]
      simp [hnC]
    have hYu : IsUnit (Yn Q B₀ a n).det := isUnit_iff_ne_zero.mpr hdn
    have hDD : Matrix.diagonal (fun i => a i n) * Matrix.diagonal (fun i => (a i n)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (ha i n)
    have hW : B₀ * walk Q n = Matrix.diagonal (fun i => a i n) * (Yn Q B₀ a n * balance n) := by
      unfold Yn
      rw [Matrix.mul_assoc _ _ (balance n), Matrix.nonsing_inv_mul _ hTu, Matrix.mul_one,
        ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    have hM : B₀ * walk Q n * (balance n)⁻¹ * (Yn Q B₀ a n)⁻¹ =
        Matrix.diagonal (fun i => a i n) := by
      rw [hW, Matrix.mul_assoc _ _ (balance n)⁻¹, Matrix.mul_assoc (Yn Q B₀ a n),
        Matrix.mul_nonsing_inv _ hTu, Matrix.mul_one, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
    rw [hSn n, Matrix.vecMul_vecMul cvec (B₀ * walk Q n) (balance n)⁻¹,
      Matrix.vecMul_vecMul cvec (B₀ * walk Q n * (balance n)⁻¹) (Yn Q B₀ a n)⁻¹, hM,
      Matrix.vecMul_diagonal]
  have hlim : ∀ i, Tendsto (fun n => cvec i * a i n) atTop (𝓝 0) := by
    intro i
    have h := Aux.tendsto_mulVec3 (Aux.tendsto_transpose3 hinv) hdecay
    rw [Matrix.mulVec_zero] at h
    refine (tendsto_pi_nhds.mp h i).congr' ?_
    filter_upwards [hkey] with n hn
    rw [hn i, ← Matrix.mulVec_transpose ((Yn Q B₀ a n)⁻¹) (S n ᵥ* (balance n)⁻¹)]
  have hzero : ∀ i, i ≠ 0 → cvec i = 0 := by
    intro i hi
    by_contra hc
    have hnorm : Tendsto (fun n => ‖a i n‖) atTop (𝓝 0) := by
      have h := ((hlim i).norm).const_mul ‖cvec i‖⁻¹
      rw [norm_zero, mul_zero] at h
      refine h.congr fun n => ?_
      rw [norm_mul, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]
    have hev : ∀ᶠ n : ℕ in atTop, ‖a i n‖ ^ ((n : ℝ)⁻¹) ≤ 1 := by
      filter_upwards [hnorm.eventually (gt_mem_nhds one_pos)] with n hn
      exact Real.rpow_le_one (norm_nonneg _) hn.le (by positivity)
    exact absurd (le_of_tendsto (hrate i hi) hev) (not_le.mpr hR)
  rw [hSn 0, Aux.walk_zero, Matrix.mul_one]
  funext j
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hzero 1 (by decide), hzero 2 (by decide),
    zero_mul, zero_mul, add_zero, add_zero, Pi.smul_apply, smul_eq_mul]

/-! ### Reindexing the modal basis -/

theorem reindex (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ)
    (a : Fin 3 → ℕ → ℂ) (σ : Equiv.Perm (Fin 3)) (hconv : Tendsto (Yn Q B₀ a) atTop (𝓝 Y)) :
    Tendsto (Yn Q (B₀.submatrix σ id) (fun i => a (σ i))) atTop (𝓝 (Y.submatrix σ id)) := by
  have h : ∀ n, Yn Q (B₀.submatrix σ id) (fun i => a (σ i)) n = (Yn Q B₀ a n).submatrix σ id := by
    intro n
    unfold Yn
    rw [Matrix.submatrix_mul _ _ σ id id Function.bijective_id,
      Matrix.submatrix_mul _ _ σ σ id σ.bijective,
      Matrix.submatrix_mul _ _ σ id id Function.bijective_id, Matrix.submatrix_id_id,
      Matrix.submatrix_id_id, Matrix.submatrix_diagonal_equiv]
    rfl
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  refine (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hconv (σ i)) j).congr fun n => ?_
  rw [h n]
  rfl

theorem det_submatrix_ne_zero (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M.det ≠ 0)
    (σ : Equiv.Perm (Fin 3)) : (M.submatrix σ id).det ≠ 0 := by
  rw [Matrix.det_permute]
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero _)) hM

theorem walk_det_ne_zero3 (Q : ℕ → Matrix (Fin 3) (Fin 3) ℚ) (hQ : ∀ n, (Q n).det ≠ 0) (n : ℕ) :
    (walk Q n).det ≠ 0 := by
  induction n with
  | zero => rw [Aux.walk_zero, Matrix.det_one]; exact one_ne_zero
  | succ n ih => rw [Aux.walk_succ, Matrix.det_mul]; exact mul_ne_zero ih (hQ n)

/-! ### The modal basis with the recessive mode first -/

theorem modal_reindexed (Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ))
    (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
      Q n i j = (((Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) : ℚ) : ℂ))
    (hdet : ∀ n, (Q n).det ≠ 0) (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hlim : Tendsto (fun n => balance n * Q n * (balance (n + 1))⁻¹) atTop (𝓝 Qinf))
    (hchar : Qinf.charpoly = chi.map (algebraMap ℚ ℂ)) :
    ∃ (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3 → ℕ → ℂ) (ρ : Fin 3 → ℂ) (r R : ℝ),
      B₀.det ≠ 0 ∧ Y.det ≠ 0 ∧ (∀ i n, a i n ≠ 0) ∧ Tendsto (Yn Q B₀ a) atTop (𝓝 Y) ∧
      (∀ i, Y i ᵥ* Qinf = ρ i • Y i) ∧ 0 < r ∧ r < R ∧ 1 < R ∧ r < 102 / 10 ^ 51 * R ∧
      Tendsto (fun n : ℕ => ‖a 0 n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 r) ∧
      ∀ i, i ≠ 0 → Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 R) := by
  have hinf := det_of_charpoly Qinf hchar
  have hsep := chi_separable Qinf hchar
  obtain ⟨B₀, Y, a, ρ, hB₀, hY, hρ, ha, hconv, heig, hrate⟩ :=
    modal_basis Qr Q hQ hdet Qinf hlim hinf hsep
  obtain ⟨r, hr0, hru, hrroot, hother, _⟩ := spectral_certificate
  have hrr : r ^ 3 - (chiA : ℝ) * r ^ 2 + (chiB : ℝ) * r - (chiC : ℝ) = 0 := by
    rw [chi_eval.1] at hrroot
    exact hrroot
  have hroot : ∀ i, Qinf.charpoly.eval (ρ i) = 0 := eig_root Qinf Y hY ρ heig
  have hrroot' : Qinf.charpoly.eval (r : ℂ) = 0 := by
    rw [hchar, chi_eval.2]
    exact_mod_cast hrr
  obtain ⟨i₀, hi₀⟩ := real_root_is_eig Qinf ρ hρ hroot r hrroot'
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3), σ = Equiv.swap 0 i₀ := ⟨_, rfl⟩
  have hρ'0 : ρ (σ 0) = r := by rw [hσ, Equiv.swap_apply_left, hi₀]
  have hρ' : Function.Injective (fun i => ρ (σ i)) := hρ.comp σ.injective
  have hcubic : ∀ i, (ρ (σ i)) ^ 3 - ((chiA : ℝ) : ℂ) * (ρ (σ i)) ^ 2 +
      ((chiB : ℝ) : ℂ) * (ρ (σ i)) - ((chiC : ℝ) : ℂ) = 0 :=
    fun i => root_of_charpoly Qinf hchar _ (hroot (σ i))
  have hne : ∀ i, i ≠ 0 → ρ (σ i) ≠ (r : ℂ) := fun i hi h => hi (hρ' (h.trans hρ'0.symm))
  have hmod : ∀ i, i ≠ 0 → ‖ρ (σ i)‖ ^ 2 * r = chiC := fun i hi =>
    cubic_conj_modulus chiA chiB chiC disc_neg r hrr _ (hcubic i) (hne i hi)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖ρ (σ 1)‖ := ⟨_, rfl⟩
  have hR2 : ∀ i, i ≠ 0 → ‖ρ (σ i)‖ = R := fun i hi => by
    have h1 := hmod 1 (by decide)
    have h2 := hmod i hi
    have hsq : ‖ρ (σ i)‖ ^ 2 = ‖ρ (σ 1)‖ ^ 2 := mul_right_cancel₀ hr0.ne' (h2.trans h1.symm)
    rw [hR]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  have hcu : (7203 / 10 ^ 27 : ℝ) < chiC := by
    have : (7203 / 10 ^ 27 : ℚ) < chiC := by unfold chiC; norm_num
    have h := (Rat.cast_lt (K := ℝ)).mpr this
    push_cast at h
    exact h
  have hRpos : 0 ≤ R := by rw [hR]; exact norm_nonneg _
  have hR1 : 1 < R := by
    have h1 := hmod 1 (by decide)
    rw [← hR] at h1
    by_contra hle
    rw [not_lt] at hle
    have : R ^ 2 ≤ 1 := pow_le_one₀ hRpos hle
    nlinarith
  have hε := hother (ρ (σ 1)) (by rw [← hchar]; exact hroot (σ 1)) (hne 1 (by decide))
  rw [← hR] at hε
  have hrR : r < R := by
    have : (102 / 10 ^ 51 : ℝ) * R < 1 * R := mul_lt_mul_of_pos_right (by norm_num) (by linarith)
    linarith
  refine ⟨B₀.submatrix σ id, Y.submatrix σ id, fun i => a (σ i), fun i => ρ (σ i), r, R,
    det_submatrix_ne_zero B₀ hB₀ σ, det_submatrix_ne_zero Y hY σ, fun i n => ha _ n,
    reindex Q B₀ Y a σ hconv, fun i => heig (σ i), hr0, hrR, hR1, hε, ?_, fun i hi => ?_⟩
  · have h := hrate (σ 0)
    rw [hρ'0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h
    exact h
  · have h := hrate (σ i)
    rw [hR2 i hi] at h
    exact h

/-! ### The dual limit over `ℂ` -/

theorem zeta_real (k : ℕ) [k.AtLeastTwo] :
    riemannZeta (OfNat.ofNat k) = (((riemannZeta (OfNat.ofNat k)).re : ℝ) : ℂ) := by
  have h := riemannZeta_conj (OfNat.ofNat k)
  rw [map_ofNat] at h
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

theorem core1 (A B : ℤ) (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (hdet : ∀ n, (Q n).det ≠ 0)
    (Qinf : Matrix (Fin 3) (Fin 3) ℂ) (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3 → ℕ → ℂ)
    (ρ : Fin 3 → ℂ) (r R : ℝ) (hB₀ : B₀.det ≠ 0) (hY : Y.det ≠ 0) (ha : ∀ i n, a i n ≠ 0)
    (hconv : Tendsto (Yn Q B₀ a) atTop (𝓝 Y)) (heig : ∀ i, Y i ᵥ* Qinf = ρ i • Y i)
    (hr0 : 0 < r) (hrR : r < R) (hR1 : 1 < R) (hε : r < 102 / 10 ^ 51 * R)
    (ha0 : Tendsto (fun n : ℕ => ‖a 0 n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 r))
    (hai : ∀ i, i ≠ 0 → Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 R))
    (hinf : Qinf.det ≠ 0)
    (hcyc : (Matrix.of ![(![1, 10, 100] : Fin 3 → ℂ), (Qinf⁻¹)ᵀ *ᵥ ![1, 10, 100],
      ((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ ![1, 10, 100]]).det ≠ 0)
    (hres : ∀ n, (fun k : Fin 3 => SG (n + 1) k) = (fun k : Fin 3 => SG n k) ᵥ* Q n) :
    ∀ᶠ n in atTop,
      castV (IGh A B 1) ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ
        castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]) ≠ 0 ∧
      ‖(castV (IGh A B 0) ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ
          castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2])) /
        (castV (IGh A B 1) ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ
          castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2])) -
        ((alpha A B : ℝ) : ℂ)‖ ≤ (102 / 10 ^ 51 : ℝ) ^ n := by
  obtain ⟨hd1, hd2, hd3⟩ := meijerG_decay
  have hdecay := state_decay (fun n hn k hk => (hd1 n hn).2.2 k hk) hd2 hd3
  have hS0 := state_select Q B₀ Y hB₀ hY a ha hconv (fun n k => SG n k) hres hdecay R hR1 hai
  obtain ⟨z0, z1, z2, _⟩ := meijerG_initial
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((fun k : Fin 3 => SG 0 k) ᵥ* B₀⁻¹) 0 := ⟨_, rfl⟩
  rw [← hc] at hS0
  have hB2 : c * B₀ 0 2 = 1 := by
    have := congrFun hS0 2
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    exact z2
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_mul] at hB2; exact zero_ne_one hB2
  have hℓ₂ : castV (IGh A B 1) ⬝ᵥ B₀ 0 ≠ 0 := by
    have : castV (IGh A B 1) ⬝ᵥ B₀ 0 = 6 * B₀ 0 2 := by
      simp [castV, IGh, dotProduct, Fin.sum_univ_three]
    rw [this]
    exact mul_ne_zero (by norm_num) fun h => by rw [h, mul_zero] at hB2; exact zero_ne_one hB2
  have hw := cyclic_ne_zero Y Qinf hY hinf ρ heig _ hcyc
  obtain ⟨hne, hbound⟩ := dual_mode_transfer Q hdet B₀ Y hB₀ hY a ha hconv r R hr0 hrR ha0 hai
    (fun n => castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]) ![1, 10, 100] hv_tendsto hw
    (castV (IGh A B 0)) (castV (IGh A B 1)) hℓ₂
  have hθ : (102 / 10 ^ 51 : ℝ) > r / R := by
    rw [gt_iff_lt, div_lt_iff₀ (by linarith)]
    exact hε
  have hval : (castV (IGh A B 0) ⬝ᵥ B₀ 0) / (castV (IGh A B 1) ⬝ᵥ B₀ 0) =
      ((alpha A B : ℝ) : ℂ) := by
    have e1 : castV (IGh A B 0) ⬝ᵥ B₀ 0 = c⁻¹ * (castV (IGh A B 0) ⬝ᵥ (c • B₀ 0)) := by
      rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel_left₀ hc0]
    have e2 : castV (IGh A B 1) ⬝ᵥ B₀ 0 = c⁻¹ * (castV (IGh A B 1) ⬝ᵥ (c • B₀ 0)) := by
      rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel_left₀ hc0]
    rw [e1, e2, ← hS0, mul_div_mul_left _ _ (inv_ne_zero hc0)]
    have hz3 := zeta_real 3
    have hz4 := zeta_real 4
    simp only [castV, IGh, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.val_zero, Fin.val_one,
      Fin.val_two, z0, z1, z2]
    unfold alpha ζ3 ζ4
    push_cast
    rw [← hz3, ← hz4]
    field_simp
    ring
  filter_upwards [hne, hbound _ hθ] with n hn1 hn2
  exact ⟨hn1, by rw [← hval]; exact hn2⟩

/-- **The dual limit** (`error_bound.lean` [5]) in terms of the data of `DualData`. -/
theorem dual_limit_core (A B : ℤ) (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (hdet : ∀ n, (G n).det ≠ 0)
    (hblock : ∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0)
    (Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ))
    (hQr : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
      (G n).submatrix Fin.castSucc Fin.castSucc i j =
        (Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ))
    (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hlim : Tendsto (fun n => balance n * cC ((G n).submatrix Fin.castSucc Fin.castSucc) *
      (balance (n + 1))⁻¹) atTop (𝓝 Qinf))
    (hchar : Qinf.charpoly = chi.map (algebraMap ℚ ℂ))
    (hcyc : (Matrix.of ![(![1, 10, 100] : Fin 3 → ℂ), (Qinf⁻¹)ᵀ *ᵥ ![1, 10, 100],
      ((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ ![1, 10, 100]]).det ≠ 0)
    (hres : ∀ n, (fun k : Fin 3 => SG (n + 1) k) =
      (fun k : Fin 3 => SG n k) ᵥ* cC ((G n).submatrix Fin.castSucc Fin.castSucc)) :
    ∀ᶠ n in atTop,
      (IGh A B *ᵥ (((walk (fun m => (G m).submatrix Fin.castSucc Fin.castSucc) n)⁻¹)ᵀ *ᵥ
        hvD n)) 1 ≠ 0 ∧
      |alpha A B - (((IGh A B *ᵥ (((walk (fun m => (G m).submatrix Fin.castSucc Fin.castSucc)
          n)⁻¹)ᵀ *ᵥ hvD n)) 0 /
        (IGh A B *ᵥ (((walk (fun m => (G m).submatrix Fin.castSucc Fin.castSucc) n)⁻¹)ᵀ *ᵥ
          hvD n)) 1 : ℚ) : ℝ)| ≤ (102 / 10 ^ 51 : ℝ) ^ n := by
  set Qb : ℕ → Matrix (Fin 3) (Fin 3) ℚ := fun m => (G m).submatrix Fin.castSucc Fin.castSucc
    with hQb
  have hQbdet : ∀ n, (Qb n).det ≠ 0 := fun n h => hdet n (by
    rw [det_block (G n) (hblock n)]
    change -(Qb n).det = 0
    rw [h, neg_zero])
  have hQdet : ∀ n, (cC (Qb n)).det ≠ 0 := fun n => by
    rw [cC_det]
    exact_mod_cast hQbdet n
  have hQ : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧ cC (Qb n) i j =
      (((Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) : ℚ) : ℂ) :=
    fun n i j => ⟨(hQr n i j).1, by
      rw [cC_apply]
      change (((G n).submatrix Fin.castSucc Fin.castSucc i j : ℚ) : ℂ) = _
      rw [(hQr n i j).2]⟩
  obtain ⟨B₀, Y, a, ρ, r, R, hB₀, hY, ha, hconv, heig, hr0, hrR, hR1, hε, ha0, hai⟩ :=
    modal_reindexed Qr (fun m => cC (Qb m)) hQ hQdet Qinf hlim hchar
  have hmain := core1 A B (fun m => cC (Qb m)) hQdet Qinf B₀ Y a ρ r R hB₀ hY ha hconv heig
    hr0 hrR hR1 hε ha0 hai (det_of_charpoly Qinf hchar) hcyc hres
  filter_upwards [hmain] with n hn
  obtain ⟨hn1, hn2⟩ := hn
  set y : Fin 3 → ℚ := ((walk Qb n)⁻¹)ᵀ *ᵥ hvD n with hy
  have hD : (∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1)) ≠ 0 := by positivity
  have hDc : ((∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hD
  have hvec : castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2] =
      ((∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1) : ℚ) : ℂ) • castV (hvD n) := by
    rw [← castV_smul, hvD, smul_smul, mul_inv_cancel₀ hD, one_smul]
  have hwalk : ((walk (fun m => cC (Qb m)) n)⁻¹)ᵀ = cC (((walk Qb n)⁻¹)ᵀ) := by
    rw [walk_cC, inv_cC _ (walk_det_ne_zero3 Qb hQbdet n), transpose_cC]
  have hx : ((walk (fun m => cC (Qb m)) n)⁻¹)ᵀ *ᵥ
      castV ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2] =
      ((∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1) : ℚ) : ℂ) • castV y := by
    rw [hvec, Matrix.mulVec_smul, hwalk, cC_mulVec]
  rw [hx, dotProduct_smul, castV_dot, smul_eq_mul] at hn1
  rw [hx, dotProduct_smul, dotProduct_smul, castV_dot, castV_dot, smul_eq_mul, smul_eq_mul] at hn2
  have e0 : (IGh A B 0 ⬝ᵥ y : ℚ) = (IGh A B *ᵥ y) 0 := rfl
  have e1 : (IGh A B 1 ⬝ᵥ y : ℚ) = (IGh A B *ᵥ y) 1 := rfl
  rw [e1] at hn1
  rw [e0, e1, mul_div_mul_left _ _ hDc, ← Rat.cast_div, ← Complex.ofReal_ratCast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hn2
  refine ⟨fun h => hn1 ?_, hn2⟩
  rw [h, Rat.cast_zero, mul_zero]

end Pfq54.DL
