/-
# CMF transport, part 7: assembly of the three transport theorems

* `WW N = W_0 ⋯ W_{N-1}` and `DD N = D_0 ⋯ D_{N-1}` are the original and dual transports from
  `p_0` to `p_N`; the moment vectors satisfy `m_N = m_0 WW N` (`mO_eq`, `mM_eq`, `mL_eq`) and the
  concomitant identity `WW N · J_N · (DD N)ᵀ = J_0` holds (`chain_pairing`).
* The `Z₂`-coefficients of the moments (`0, 0, 0, -1`) give the block form
  `WW N = [[V, *], [0, 1]]` (`lastRow_WW`), hence `𝓒_N = 𝓒₀ V` and `V_N = (-1)^N V`
  (`coeffMat_eq`, `V_eq`), and `det V = det WW N`.
* `exists_transport_blocks'`: `𝓒_{N+1} = -𝓒_N B_N` with `det B_N = F_{N+1}/F_N` (from `det_Wmat`
  and `Vpot_pN`).
* `dual_transport'`: the dual second-functional moments transport by `D_N = (-1)^N DD N`, and the
  concomitant identity in the readout form of the blueprint.
* `dual_first_identity'`: the dual formula for the first functional.
-/
import CMF_kernel
import CMF_det
import coeffMat_zero

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-! ### The chains over `N` -/

def WW : ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => 1
  | N + 1 => WW N * Wmat N

def DD : ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => 1
  | N + 1 => DD N * Dmat N

/-- The original moments `𝓛_{2N}[(-t)^j R_N]`. -/
def mO (N : ℕ) : Fin 4 → FormalZ := mv Lfun (2 * N) (pN N).ker
/-- The dual second-functional moments. -/
def mM (N : ℕ) : Fin 4 → FormalZ := mv Mfun (2 * N) (pN N).dual.ker
/-- The dual first-functional moments. -/
def mL (N : ℕ) : Fin 4 → FormalZ := mv Lfun (N : ℤ) (pN N).dual.ker

theorem mO_eq (N : ℕ) : mO N = vm (mO 0) (WW N) := by
  induction N with
  | zero => rw [WW, vm_one]
  | succ N ih => rw [mO, transport_orig, ← mO, ih, vm_mul, WW]

theorem mM_eq (N : ℕ) : mM N = vm (mM 0) (DD N) := by
  induction N with
  | zero => rw [DD, vm_one]
  | succ N ih => rw [mM, transport_dualM, ← mM, ih, vm_mul, DD]

theorem mL_eq (N : ℕ) : mL N = vm (mL 0) (DD N) := by
  induction N with
  | zero => rw [DD, vm_one]
  | succ N ih => rw [mL, transport_dualL, ← mL, ih, vm_mul, DD]

/-! ### The concomitant identity along the chain -/

theorem pok_walk (N t : ℕ) (ht : t < 72) : (edge t).pok (vtx N t) := by
  refine ⟨?_, ?_, fun hf => ?_, fun hf => ?_⟩
  · rw [src_eq]; split_ifs
    · exact dc4_vtx N t (by omega)
    · rw [← vtx_succ N t ht]; exact dc4_vtx N (t + 1) ht
  · rw [dual_src]; split_ifs
    · exact dc4_dual N t (by omega)
    · rw [← vtx_succ N t ht]; exact dc4_dual N (t + 1) ht
  · rw [show (edge t).src (vtx N t) = (edge t).apply (vtx N t) from if_neg hf]
    exact inv_walk N t ht hf
  · rw [show (edge t).dual.src (vtx N t).dual = ((edge t).apply (vtx N t)).dual by
      rw [dual_src, if_neg hf]]
    by_cases h : t < 66
    · exact inv_dual_of_a N t h hf
    · exact inv_dual_of_b N t (by omega) ht hf

theorem step_pairing (N : ℕ) :
    Wmat N * Jm (pN (N + 1)).a (pN (N + 1)).b * (Dmat N)ᵀ = Jm (pN N).a (pN N).b := by
  have := walk_pairing edge (vtx N) 72 (vtx_succ N) (pok_walk N)
  rw [vtx_72, vtx_zero, show ((-1 : ℚ) ^ 72) = 1 by norm_num, one_smul] at this
  exact this

theorem chain_pairing (N : ℕ) : WW N * Jm (pN N).a (pN N).b * (DD N)ᵀ = Jm (pN 0).a (pN 0).b := by
  induction N with
  | zero => rw [WW, DD, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  | succ N ih =>
    rw [WW, DD, Matrix.transpose_mul, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Wmat N), ← Matrix.mul_assoc (Wmat N * _), step_pairing]

/-! ### The block form -/

/-- The symbols indexing the rows of the coefficient matrix: `Z₄, Z₃, Z₀ = 1, Z₂`. -/
def sym : Fin 4 → ℕ := ![4, 3, 0, 2]

/-- The `4 × 4` coefficient matrix of the first four moments. -/
def CM4 (N : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := fun r j => mO N j (sym r)

theorem vm_coord (m : Fin 4 → FormalZ) (A : Matrix (Fin 4) (Fin 4) ℚ) (j : Fin 4) (s : ℕ) :
    (vm m A) j s = ∑ i, A i j * m i s := by
  simp only [vm, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem CM4_eq (N : ℕ) : CM4 N = CM4 0 * WW N := by
  ext r j
  rw [CM4, mO_eq, vm_coord, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem CM4_succ (N : ℕ) : CM4 (N + 1) = CM4 N * Wmat N := by
  ext r j
  rw [CM4, mO, transport_orig, ← mO, vm_coord, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem CM4_row3 (N : ℕ) (j : Fin 4) : CM4 N 3 j = if j = 3 then -1 else 0 := by
  show mO N j 2 = _
  rw [mO, mv, ker_pN]
  fin_cases j
  · rw [ite_eq_right (by decide)]
    exact Lfun_linFormKernel_support N 0 2 (by decide) (by decide) (by decide)
  · rw [ite_eq_right (by decide)]
    exact Lfun_linFormKernel_support N 1 2 (by decide) (by decide) (by decide)
  · rw [ite_eq_right (by decide)]
    exact Lfun_linFormKernel_support N 2 2 (by decide) (by decide) (by decide)
  · rw [ite_eq_left (by decide)]
    exact Lfun_cubic_Z2 N

/-- Last row `(0, 0, 0, 1)`. -/
def lastRow (W : Matrix (Fin 4) (Fin 4) ℚ) : Prop := ∀ j, W 3 j = if j = 3 then 1 else 0

theorem lastRow_mul {A B : Matrix (Fin 4) (Fin 4) ℚ} (hA : lastRow A) (hB : lastRow B) :
    lastRow (A * B) := by
  intro j
  rw [Matrix.mul_apply, Fin.sum_univ_four, hA, hA, hA, hA, hB]
  simp

theorem lastRow_Wmat (N : ℕ) : lastRow (Wmat N) := by
  intro j
  have h := congrFun (congrFun (CM4_succ N) 3) j
  rw [Matrix.mul_apply, Fin.sum_univ_four, CM4_row3, CM4_row3, CM4_row3, CM4_row3, CM4_row3] at h
  simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true, zero_mul, zero_add, neg_one_mul] at h
  split_ifs at h ⊢ <;> linarith

theorem lastRow_WW (N : ℕ) : lastRow (WW N) := by
  induction N with
  | zero => intro j; rw [WW, Matrix.one_apply]; simp [eq_comm]
  | succ N ih => rw [WW]; exact lastRow_mul ih (lastRow_Wmat N)

/-- The upper-left `3 × 3` block. -/
def blk (W : Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  W.submatrix Fin.castSucc Fin.castSucc

theorem blk_mul (A B : Matrix (Fin 4) (Fin 4) ℚ) (hB : lastRow B) : blk (A * B) = blk A * blk B := by
  ext i j
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [hB, ite_eq_right (by first | exact Fin.castSucc_ne_last j |
    (rw [Fin.ext_iff, Fin.val_castSucc]; omega)), mul_zero, add_zero]
  rfl

theorem det_lastRow (W : Matrix (Fin 4) (Fin 4) ℚ) (hW : lastRow W) : W.det = (blk W).det := by
  rw [Matrix.det_succ_row W 3, Fin.sum_univ_four, hW 0, hW 1, hW 2, hW 3]
  simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true, zero_mul, mul_zero, zero_add,
    add_zero, mul_one]
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, Fin.succAbove_last, Fin.val_last,
    show (-1 : ℚ) ^ (3 + 3) = 1 by norm_num, one_mul]
  rfl

/-- `𝓒_N = 𝓒₀ · blk (WW N)`. -/
theorem coeffMat_eq_blk (N : ℕ) : coeffMat N = blk (CM4 N) := by
  ext i j
  simp only [coeffMat, blk, Matrix.submatrix_apply, CM4, mO, mv, ker_pN, linFormKernel,
    Fin.val_castSucc]
  fin_cases i <;> rfl

theorem coeffMat_eq (N : ℕ) : coeffMat N = C0 * blk (WW N) := by
  rw [coeffMat_eq_blk, CM4_eq, blk_mul _ _ (lastRow_WW N), ← coeffMat_eq_blk, coeffMat_zero]

theorem coeffMat_succ' (N : ℕ) : coeffMat (N + 1) = coeffMat N * blk (Wmat N) := by
  rw [coeffMat_eq_blk, CM4_succ, blk_mul _ _ (lastRow_Wmat N), ← coeffMat_eq_blk]

theorem det_C0' : C0.det = -6 := by
  rw [Matrix.det_fin_three]; simp [C0]; norm_num

theorem V_eq (N : ℕ) : V N = ((-1 : ℚ) ^ N) • blk (WW N) := by
  rw [V, coeffMat_eq, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (by rw [det_C0']; exact isUnit_iff_ne_zero.mpr (by norm_num)),
    Matrix.one_mul]

/-! ### The determinant -/

theorem det_Wmat' (N : ℕ) : (Wmat N).det = -(F (N + 1) / F N) := by
  rw [det_Wmat, Vpot_pN, Vpot_pN]

theorem F_ne_zero (N : ℕ) : F N ≠ 0 := by
  unfold F
  refine div_ne_zero (List.prod_ne_zero ?_) (mul_ne_zero (List.prod_ne_zero ?_)
    (List.prod_ne_zero ?_)) <;> simp [Nat.factorial_ne_zero]

theorem det_WW (N : ℕ) : (WW N).det = ((-1 : ℚ) ^ N) * (F N / F 0) := by
  induction N with
  | zero => rw [WW, Matrix.det_one, pow_zero, div_self (F_ne_zero 0), mul_one]
  | succ N ih =>
    rw [WW, Matrix.det_mul, ih, det_Wmat', pow_succ]
    have h1 : F N / F 0 * (F (N + 1) / F N) = F (N + 1) / F 0 := by
      rw [div_mul_div_comm, mul_comm (F N), mul_div_mul_right _ _ (F_ne_zero N)]
    rw [mul_neg, mul_assoc, h1, mul_neg_one, neg_mul]

theorem det_blk_WW (N : ℕ) : (blk (WW N)).det ≠ 0 := by
  rw [← det_lastRow _ (lastRow_WW N), det_WW]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (div_ne_zero (F_ne_zero N) (F_ne_zero 0))

/-- **Node `exists_transport_blocks` of `det_V_eq.lean`.** -/
theorem exists_transport_blocks' :
    ∃ B : ℕ → Matrix (Fin 3) (Fin 3) ℚ, ∀ N,
      coeffMat (N + 1) = -(coeffMat N * B N) ∧ (B N).det = F (N + 1) / F N := by
  refine ⟨fun N => -blk (Wmat N), fun N => ⟨?_, ?_⟩⟩
  · rw [Matrix.mul_neg, neg_neg, coeffMat_succ']
  · rw [Matrix.det_neg, ← det_lastRow _ (lastRow_Wmat N), det_Wmat', Fintype.card_fin]
    ring

/-! ### Solving the block system -/

theorem inv_sign_smul (c : ℚ) (hc : c * c = 1) (A : Matrix (Fin 3) (Fin 3) ℚ) (hA : A.det ≠ 0) :
    (c • A)⁻¹ = c • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]

/-- From `W M = J` with `W = [[V, *], [0, 1]]` and `J` with last row zero: the first three rows
of `M` are `V⁻¹ J[0:3,:]`. -/
theorem block_solve (W M J : Matrix (Fin 4) (Fin 4) ℚ) (hW : lastRow W) (hWM : W * M = J)
    (hJ : ∀ i, J 3 i = 0) (hV : (blk W).det ≠ 0) (j : Fin 3) (i : Fin 4) :
    M (Fin.castSucc j) i = ∑ k : Fin 3, (blk W)⁻¹ j k * J (Fin.castSucc k) i := by
  have hM3 : ∀ i, M 3 i = 0 := by
    intro i
    have h := congrFun (congrFun hWM 3) i
    rw [Matrix.mul_apply, Fin.sum_univ_four, hW, hW, hW, hW, hJ] at h
    simpa using h
  have hsys : blk W * Matrix.of (fun k i => M (Fin.castSucc k) i) =
      Matrix.of (fun k i => J (Fin.castSucc k) i) := by
    ext k i
    have h := congrFun (congrFun hWM (Fin.castSucc k)) i
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, blk, Matrix.submatrix_apply]
    rw [← h, show Fin.last 3 = 3 from rfl, hM3, mul_zero, add_zero]
  have hsol : Matrix.of (fun k i => M (Fin.castSucc k) i) =
      (blk W)⁻¹ * Matrix.of (fun k i => J (Fin.castSucc k) i) := by
    rw [← hsys, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hV),
      Matrix.one_mul]
  have := congrFun (congrFun hsol j) i
  rw [Matrix.of_apply, Matrix.mul_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.of_apply]

theorem Jm_zero_row3 (N : ℕ) (i : Fin 4) : Jm (pN N).a (pN N).b 3 i = 0 := by
  rw [Jm_pN]
  fin_cases i <;> rfl

theorem T_eq (N : ℕ) (k j : Fin 3) : T N k j = ((-1 : ℚ) ^ N) * (blk (WW N))⁻¹ j k := by
  rw [T, V_eq, inv_sign_smul _ (by rw [← pow_add, ← two_mul, pow_mul]; norm_num) _ (det_blk_WW N),
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]

/-- The dual kernel of the blueprint. -/
def dK (N : ℕ) : ℚ⟮X⟯ := ((-1 : ℚ) ^ N) • RatFunc.laurent (-(12 * (N : ℚ) + 1)) (RkerStar N)
/-- The dual second-functional moments of the blueprint. -/
def dM (N : ℕ) (r : Fin 4) : FormalZ := Mfun (2 * N) ((-RatFunc.X) ^ (r : ℕ) * dK N)

theorem dM_eq (N : ℕ) (r : Fin 4) : dM N r = ((-1 : ℚ) ^ N) • mM N r := by
  rw [dM, dK, ← dual_ker_eq, RatFunc.smul_eq_C_mul, mul_left_comm, ← RatFunc.smul_eq_C_mul,
    Aux.Mfun_smul]
  rfl

/-- The readout block of the concomitant identity: `J_N DD_Nᵀ` on the first three rows. -/
theorem JD_row (N : ℕ) (j : Fin 3) (i : Fin 4) :
    (Jm (pN N).a (pN N).b * (DD N)ᵀ) (Fin.castSucc j) i =
      ∑ k : Fin 3, (blk (WW N))⁻¹ j k * Jm (pN 0).a (pN 0).b (Fin.castSucc k) i :=
  block_solve (WW N) _ _ (lastRow_WW N) (by rw [← Matrix.mul_assoc]; exact chain_pairing N)
    (Jm_zero_row3 0) (det_blk_WW N) j i

theorem Jmat_cast (N : ℕ) (r s : Fin 4) : (Jmat N r s : ℚ) = Jm (pN N).a (pN N).b r s := by
  rw [Jm_pN, Matrix.map_apply]

/-- **Node `dual_transport` of `pairing_identity.lean`.** -/
theorem dual_transport' :
    ∃ D : ℕ → Matrix (Fin 4) (Fin 4) ℚ, ∀ N,
      (∀ r, dM N r = ∑ i : Fin 4, D N i r • dM 0 i) ∧
      ∀ j : Fin 3, ∀ i : Fin 4, ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) * D N i r =
        ∑ k : Fin 3, T N k j * (Jmat 0 (Fin.castSucc k) i : ℚ) := by
  refine ⟨fun N => ((-1 : ℚ) ^ N) • DD N, fun N => ⟨fun r => ?_, fun j i => ?_⟩⟩
  · rw [dM_eq, mM_eq, vm]
    simp only [dM_eq, pow_zero, one_smul, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  · have h := JD_row N j i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply] at h
    simp only [Jmat_cast, Matrix.smul_apply, smul_eq_mul, T_eq]
    rw [show ∑ r, Jm (pN N).a (pN N).b (Fin.castSucc j) r * ((-1 : ℚ) ^ N * DD N i r) =
      ((-1 : ℚ) ^ N) * ∑ r, Jm (pN N).a (pN N).b (Fin.castSucc j) r * DD N i r by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The dual identity for the first functional -/

theorem mL_zero : mL 0 = ![Zsym 2 - (2 : ℚ) • Zsym 3, Zsym 2 - Zsym 0, (-1 / 2 : ℚ) • Zsym 0,
    (1 / 3 : ℚ) • Zsym 0] := by
  rw [mL, Nat.cast_zero]; exact dualL_zero

theorem Jmat_zero_pairing (k : Fin 3) :
    ∑ i : Fin 4, (Jmat 0 (Fin.castSucc k) i : ℚ) • mL 0 i =
      ![(0 : FormalZ), Zsym 0, (2 : ℚ) • Zsym 3 - Zsym 0] k := by
  rw [mL_zero]
  fin_cases k <;> simp [Fin.sum_univ_four, Jmat] <;> module

/-- `Q_{Nj}(t) R*_N(t)` as a translate of `∑_r J_{jr} (-s)^r r_N(s)`. -/
theorem Qmul_eq (N : ℕ) (j : Fin 3) :
    algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N =
      RatFunc.laurent ((12 * (N : ℤ) + 1 : ℤ) : ℚ)
        (∑ r : Fin 4, RatFunc.C (Jmat N (Fin.castSucc j) r : ℚ) *
          ((-RatFunc.X) ^ (r : ℕ) * (pN N).dual.ker)) := by
  have hR : RkerStar N = RatFunc.laurent ((12 * (N : ℤ) + 1 : ℤ) : ℚ) (pN N).dual.ker := by
    rw [dual_ker_eq, RatFunc.laurent_laurent, show ((12 * (N : ℤ) + 1 : ℤ) : ℚ) + -(12 * (N : ℚ) + 1) = 0
      by push_cast; ring, RatFunc.laurent_at_zero]
  have hQ : algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) =
      RatFunc.laurent ((12 * (N : ℤ) + 1 : ℤ) : ℚ) (∑ r : Fin 4,
        RatFunc.C (Jmat N (Fin.castSucc j) r : ℚ) * (-RatFunc.X) ^ (r : ℕ)) := by
    simp only [Qpoly, map_sum, Polynomial.smul_eq_C_mul, map_mul, map_pow, map_sub, map_neg,
      RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.laurent_C, RatFunc.laurent_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    push_cast
    ring
  rw [hQ, hR, ← map_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **Node `dual_first_identity` of `valuation_bound.lean`.** -/
theorem dual_first_identity' (N : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ N * 3) • Lfun (-11 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) =
      q N j • Zsym 3 - p3 N j • Zsym 0 := by
  rw [Qmul_eq, Aux.Lfun_laurent, show (-11 * (N : ℤ) - 1 + (12 * N + 1)) = N by ring,
    isMom_Lfun.sum]
  -- the moments `mL N`
  have hm : ∀ r : Fin 4, Lfun (N : ℤ) ((-RatFunc.X) ^ (r : ℕ) * (pN N).dual.ker) = mL N r :=
    fun r => rfl
  simp only [hm]
  have hrow : ∀ i : Fin 4, ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) * DD N i r =
      ∑ k : Fin 3, (blk (WW N))⁻¹ j k * Jmat 0 (Fin.castSucc k) i := by
    intro i
    have h := JD_row N j i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply, Jmat_cast] at h ⊢
    exact h
  have hsum : ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) • mL N r =
      ∑ k : Fin 3, (blk (WW N))⁻¹ j k • ![(0 : FormalZ), Zsym 0, (2 : ℚ) • Zsym 3 - Zsym 0] k := by
    rw [mL_eq]
    simp only [vm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    simp only [hrow, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_smul, ← Finset.smul_sum, Jmat_zero_pairing]
  rw [hsum]
  -- the readouts
  have hq : q N j = 6 * T N 2 j := by
    simp [q, Rmat, U34, Matrix.mul_apply, Fin.sum_univ_three]
  have hp : p3 N j = -3 * T N 1 j + 3 * T N 2 j := by
    simp [p3, Rmat, U34, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hq, hp, T_eq, T_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  module

end ZetasIrr.CMF
