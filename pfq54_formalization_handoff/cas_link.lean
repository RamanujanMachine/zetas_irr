import gdual
import cas_aux
import cas_poly
import cas_cert0
import cas_cert1
import cas_cert2
import cas_cert3
import cas_cert4
import cas_cert5
import cas_cert6
import cas_cert7

open Finset Polynomial
open scoped Matrix

noncomputable section

namespace Pfq54.CL

open Pfq54 Pfq54.ST Pfq54.GD Pfq54.CA Pfq54.CF ZetasIrr ZetasIrr.CMF ZetasIrr.GW

/-! ### The Casoratian polynomial is positive -/

theorem Pval_all (k : ℕ) (hk : k < 511) : PvalS k = Int.ofNat (PfacN k) := by
  rcases Nat.lt_or_ge k 64 with h | h
  · exact cas_range_0 k (Nat.zero_le _) h
  rcases Nat.lt_or_ge k 128 with h' | h'
  · exact cas_range_1 k h h'
  rcases Nat.lt_or_ge k 192 with h | h
  · exact cas_range_2 k h' h
  rcases Nat.lt_or_ge k 256 with h' | h'
  · exact cas_range_3 k h h'
  rcases Nat.lt_or_ge k 320 with h | h
  · exact cas_range_4 k h' h
  rcases Nat.lt_or_ge k 384 with h' | h'
  · exact cas_range_5 k h h'
  rcases Nat.lt_or_ge k 448 with h | h
  · exact cas_range_6 k h' h
  exact cas_range_7 k h (by omega)

theorem PvalZ_eq_PfacZ (n : ℤ) : PvalZ n = PfacZ n :=
  PD.eq_of' PD_PvalZ PD_PfacZ le_rfl (fun k => by
    have h := Pval_all k k.isLt
    rw [PvalS_eq, Int.ofNat_eq_natCast, PfacN_cast] at h
    exact h) n

theorem PvalZ_pos (n : ℕ) : 0 < PvalZ n := by
  rw [PvalZ_eq_PfacZ, ← PfacN_cast]
  exact_mod_cast PfacN_pos n

/-! ### The integer matrices -/

def toV (v : V3) : Fin 3 → ℤ := ![v.x0, v.x1, v.x2]

def toM (A : M3) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![A.r0.x0, A.r0.x1, A.r0.x2; A.r1.x0, A.r1.x1, A.r1.x2; A.r2.x0, A.r2.x1, A.r2.x2]

theorem toM_tmulVec (A : M3) (v : V3) : (toM A)ᵀ *ᵥ toV v = toV (A.tmulVec v) := by
  ext i
  fin_cases i <;> simp [toM, toV, M3.tmulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem Np_eval (b : ℕ) (n : ℕ) :
    (Polynomial.evalRingHom (n : ℤ)).mapMatrix (Np b) = toM (blockNZ b n) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Np, blockNZ, toM, eval_listPoly]

def NZ (m : ℕ) : Matrix (Fin 3) (Fin 3) ℤ := (Polynomial.evalRingHom (m : ℤ)).mapMatrix Nprod

theorem NZ_eq (m : ℕ) : NZ m = toM (blockNZ 0 m) * (toM (blockNZ 1 m) * (toM (blockNZ 2 m) *
    (toM (blockNZ 3 m) * (toM (blockNZ 4 m) * (toM (blockNZ 5 m) * (toM (blockNZ 6 m) *
    (toM (blockNZ 7 m) * (toM (blockNZ 8 m) * (toM (blockNZ 9 m) * (toM (blockNZ 10 m) *
    toM (blockNZ 11 m))))))))))) := by
  rw [NZ, Nprod, map_list_prod, show List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Np_eval]

theorem NZ_tmulVec (m : ℕ) (v : V3) : (NZ m)ᵀ *ᵥ toV v = toV (NTspec (blocksZ m) v) := by
  rw [NZ_eq]
  simp only [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, toM_tmulVec, NTspec, blocksZ]

def MZ (n : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => ![(NZ (n + 1))ᵀ *ᵥ ((NZ n)ᵀ *ᵥ toV (hvZ n)),
    (NZ (n + 1))ᵀ *ᵥ toV (hvZ ((n + 1 : ℕ) : ℤ)), toV (hvZ ((n + 2 : ℕ) : ℤ))] j i

theorem det_cols (a b c : V3) : (Matrix.of fun i j => ![toV a, toV b, toV c] j i).det = det3 a b c := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, toV, CF.det3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

attribute [local irreducible] NZ in
theorem MZ_det (n : ℕ) : (MZ n).det = PvalZ n := by
  have e0 : (NZ (n + 1))ᵀ *ᵥ ((NZ n)ᵀ *ᵥ toV (hvZ n)) =
      toV (NTspec (blocksZ ((n : ℤ) + 1)) (NTspec (blocksZ n) (hvZ n))) := by
    rw [NZ_tmulVec, NZ_tmulVec]
    push_cast
    rfl
  have e1 : (NZ (n + 1))ᵀ *ᵥ toV (hvZ ((n + 1 : ℕ) : ℤ)) =
      toV (NTspec (blocksZ ((n : ℤ) + 1)) (hvZ ((n : ℤ) + 1))) := by
    rw [NZ_tmulVec]
    push_cast
    rfl
  have e2 : toV (hvZ ((n + 2 : ℕ) : ℤ)) = toV (hvZ ((n : ℤ) + 2)) := by
    push_cast
    rfl
  have h : MZ n = Matrix.of fun i j => ![toV (NTspec (blocksZ ((n : ℤ) + 1)) (NTspec (blocksZ n) (hvZ n))),
      toV (NTspec (blocksZ ((n : ℤ) + 1)) (hvZ ((n : ℤ) + 1))), toV (hvZ ((n : ℤ) + 2))] j i := by
    simp only [MZ, e0, e1, e2]
  rw [h, det_cols, PvalZ]

/-! ### The rational matrices -/

def NQ (m : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := (ev m).mapMatrix Nprod

theorem NQ_eq (m : ℕ) : NQ m = (Int.castRingHom ℚ).mapMatrix (NZ m) := by
  ext i j
  simp [NQ, NZ, ev]

theorem transpose_cast (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ((Int.castRingHom ℚ).mapMatrix M)ᵀ = (Int.castRingHom ℚ).mapMatrix Mᵀ := by
  simp [Matrix.transpose_map]

theorem mulVec_cast (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    (Int.castRingHom ℚ).mapMatrix M *ᵥ ((Int.castRingHom ℚ) ∘ v) =
      (Int.castRingHom ℚ) ∘ (M *ᵥ v) :=
  funext fun i => (RingHom.map_mulVec _ _ _ i).symm

theorem hv_cast (m : ℕ) : ST.hv m = (Int.castRingHom ℚ) ∘ toV (hvZ m) := by
  ext i
  fin_cases i <;> simp [ST.hv, toV, hvZ] <;> ring

def Mq (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun i j => ![(NQ (n + 1))ᵀ *ᵥ ((NQ n)ᵀ *ᵥ ST.hv n), (NQ (n + 1))ᵀ *ᵥ ST.hv (n + 1),
    ST.hv (n + 2)] j i

theorem Mq_eq (n : ℕ) : Mq n = (Int.castRingHom ℚ).mapMatrix (MZ n) := by
  have c0 : (NQ (n + 1))ᵀ *ᵥ ((NQ n)ᵀ *ᵥ ST.hv n) =
      (Int.castRingHom ℚ) ∘ ((NZ (n + 1))ᵀ *ᵥ ((NZ n)ᵀ *ᵥ toV (hvZ n))) := by
    rw [NQ_eq, NQ_eq, hv_cast, transpose_cast, transpose_cast, mulVec_cast, mulVec_cast]
  have c1 : (NQ (n + 1))ᵀ *ᵥ ST.hv (n + 1) =
      (Int.castRingHom ℚ) ∘ ((NZ (n + 1))ᵀ *ᵥ toV (hvZ ((n + 1 : ℕ) : ℤ))) := by
    rw [NQ_eq, hv_cast, transpose_cast, mulVec_cast]
  have c2 : ST.hv (n + 2) = (Int.castRingHom ℚ) ∘ toV (hvZ ((n + 2 : ℕ) : ℤ)) := hv_cast _
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Mq, MZ, Matrix.of_apply, Matrix.of_apply]
  fin_cases j
  · exact congrFun c0 i
  · exact congrFun c1 i
  · exact congrFun c2 i

theorem Mq_det (n : ℕ) : (Mq n).det = ((PvalZ n : ℤ) : ℚ) := by
  rw [Mq_eq, ← RingHom.map_det, MZ_det]
  rfl

/-! ### The transport matrices -/

theorem walk_det (m : ℕ) : (walk Qb m).det ≠ 0 := by
  rw [walk_Qb, Matrix.det_smul, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (det_blk_WW m)

theorem Qb_det (m : ℕ) : (Qb m).det ≠ 0 := by
  have h := walk_det (m + 1)
  rw [Aux.walk_succ, Matrix.det_mul] at h
  exact right_ne_zero_of_mul h

theorem T_eq' (m : ℕ) : T m = ((walk Qb m)⁻¹)ᵀ := (walk_Qb_inv_transpose m).symm

theorem T_det (m : ℕ) : (T m).det ≠ 0 := by
  rw [T_eq', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (walk_det m)

theorem T_succ (m : ℕ) : T (m + 1) = T m * ((Qb m)⁻¹)ᵀ := by
  rw [T_eq', T_eq', Aux.walk_succ, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem QbT_inv (m : ℕ) (w : Fin 3 → ℚ) : (Qb m)ᵀ *ᵥ (((Qb m)⁻¹)ᵀ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Qb_det m)), Matrix.transpose_one,
    Matrix.one_mulVec]

theorem Qb_eq' (m : ℕ) : Qb m = -((ev m Dprod)⁻¹ • NQ m) := by
  rw [Qb_eq, blk_Wmat_eq]
  rfl

theorem QbT_mulVec (m : ℕ) (w : Fin 3 → ℚ) :
    (Qb m)ᵀ *ᵥ w = -((ev m Dprod)⁻¹ • ((NQ m)ᵀ *ᵥ w)) := by
  rw [Qb_eq', Matrix.transpose_neg, Matrix.transpose_smul, Matrix.neg_mulVec,
    Matrix.smul_mulVec]

/-! ### The vectors `y_n` -/

def PU : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 6; 0, -3, 3; 2, -2, 0]

def Pm : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem PU_eq : PU = Pm * U34 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PU, Pm, U34, Matrix.mul_apply, Fin.sum_univ_three]

theorem PU_det : PU.det = 36 := by
  rw [Matrix.det_fin_three]
  norm_num [PU]

theorem Pm_mulVec (z : Fin 3 → ℚ) : Pm *ᵥ z = ![z 2, z 0, z 1] := by
  ext i
  fin_cases i <;> simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem Rmat_mulVec (m : ℕ) : Rmat m *ᵥ ST.hv m =
    ![∑ k, p3 m k * ST.hv m k, ∑ k, p4 m k * ST.hv m k, ∑ k, q m k * ST.hv m k] := by
  ext i
  fin_cases i <;> rfl

theorem comp_eq (D S C : ℚ) (hD : D ≠ 0) (m : ℕ) :
    (6 * D)⁻¹ * ((-1 : ℚ) ^ m * 6 * D * ((-1) ^ m * S / C)) = S / C := by
  have h : (-1 : ℚ) ^ m * 6 * D * ((-1) ^ m * S / C) = 6 * D * (S / C) := by
    linear_combination (6 * D * (S / C)) * neg_one_pow_sq m
  rw [h, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero (by norm_num) hD), one_mul]

theorem y_eq (m : ℕ) : y m = (6 * Del m)⁻¹ • (PU *ᵥ (T m *ᵥ ST.hv m)) := by
  have hD := (Del_pos m).ne'
  have key : PU *ᵥ (T m *ᵥ ST.hv m) = Pm *ᵥ (Rmat m *ᵥ ST.hv m) := by
    rw [PU_eq, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := U34), Rmat]
  rw [key, Rmat_mulVec, Pm_mulVec, sum_q_hv, sum_p3_hv, sum_p4_hv]
  unfold Qa P3a P4a
  ext i
  fin_cases i
  · exact (comp_eq (Del m) (S0 m) (Cn m) hD m).symm
  · exact (comp_eq (Del m) (S3 m) (Cn m) hD m).symm
  · exact (comp_eq (Del m) (S4 m) (Cn m) hD m).symm

/-! ### The Casoratian -/

theorem col_mul (A : Matrix (Fin 3) (Fin 3) ℚ) (c : Fin 3 → Fin 3 → ℚ) :
    A * Matrix.of (fun i j => c j i) = Matrix.of fun i j => (A *ᵥ c j) i := by
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

def Km (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun i j => ![ST.hv n, ((Qb n)⁻¹)ᵀ *ᵥ ST.hv (n + 1),
    ((Qb n)⁻¹)ᵀ *ᵥ (((Qb (n + 1))⁻¹)ᵀ *ᵥ ST.hv (n + 2))] j i

theorem colT (n : ℕ) (j : Fin 3) : T (n + j) *ᵥ ST.hv (n + j) =
    T n *ᵥ (![ST.hv n, ((Qb n)⁻¹)ᵀ *ᵥ ST.hv (n + 1),
      ((Qb n)⁻¹)ᵀ *ᵥ (((Qb (n + 1))⁻¹)ᵀ *ᵥ ST.hv (n + 2))] j) := by
  fin_cases j
  · rfl
  · show T (n + 1) *ᵥ ST.hv (n + 1) = T n *ᵥ (((Qb n)⁻¹)ᵀ *ᵥ ST.hv (n + 1))
    rw [T_succ, ← Matrix.mulVec_mulVec]
  · show T (n + 2) *ᵥ ST.hv (n + 2) =
      T n *ᵥ (((Qb n)⁻¹)ᵀ *ᵥ (((Qb (n + 1))⁻¹)ᵀ *ᵥ ST.hv (n + 2)))
    rw [show n + 2 = n + 1 + 1 from rfl, T_succ, T_succ, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]

theorem Y3_eq (n : ℕ) :
    Y3 n = Matrix.of fun (i j : Fin 3) => (6 * Del (n + (j : ℕ)))⁻¹ * (PU * T n * Km n) i j := by
  ext i j
  rw [Y3, Matrix.of_apply, Matrix.of_apply, y_eq, Pi.smul_apply, smul_eq_mul, Km, col_mul,
    Matrix.of_apply, ← Matrix.mulVec_mulVec, colT]

theorem Y3_det (n : ℕ) :
    (Y3 n).det = (∏ j : Fin 3, (6 * Del (n + (j : ℕ)))⁻¹) * (PU.det * (T n).det * (Km n).det) := by
  rw [Y3_eq, Matrix.det_mul_row, Matrix.det_mul, Matrix.det_mul]

def Mc (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun i j => ![(Qb (n + 1))ᵀ *ᵥ ((Qb n)ᵀ *ᵥ ST.hv n), (Qb (n + 1))ᵀ *ᵥ ST.hv (n + 1),
    ST.hv (n + 2)] j i

theorem QQ_Km (n : ℕ) : (Qb (n + 1))ᵀ * (Qb n)ᵀ * Km n = Mc n := by
  rw [Km, col_mul, Mc]
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply, ← Matrix.mulVec_mulVec]
  fin_cases j
  · rfl
  · show ((Qb (n + 1))ᵀ *ᵥ ((Qb n)ᵀ *ᵥ (((Qb n)⁻¹)ᵀ *ᵥ ST.hv (n + 1)))) i =
      ((Qb (n + 1))ᵀ *ᵥ ST.hv (n + 1)) i
    rw [QbT_inv]
  · show ((Qb (n + 1))ᵀ *ᵥ ((Qb n)ᵀ *ᵥ (((Qb n)⁻¹)ᵀ *ᵥ
      (((Qb (n + 1))⁻¹)ᵀ *ᵥ ST.hv (n + 2))))) i = ST.hv (n + 2) i
    rw [QbT_inv, QbT_inv]

theorem Km_det (n : ℕ) : (Qb (n + 1)).det * (Qb n).det * (Km n).det = (Mc n).det := by
  rw [← QQ_Km, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]

theorem Mc_eq (n : ℕ) : Mc n = Matrix.of fun i j =>
    (![(ev (n + 1) Dprod * ev n Dprod)⁻¹, -(ev (n + 1) Dprod)⁻¹, 1] : Fin 3 → ℚ) j * Mq n i j := by
  ext i j
  rw [Mc, Mq, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply]
  fin_cases j
  · show ((Qb (n + 1))ᵀ *ᵥ ((Qb n)ᵀ *ᵥ ST.hv n)) i =
      (ev (n + 1) Dprod * ev n Dprod)⁻¹ * ((NQ (n + 1))ᵀ *ᵥ ((NQ n)ᵀ *ᵥ ST.hv n)) i
    rw [QbT_mulVec, QbT_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul, smul_neg, neg_neg, smul_smul,
      Pi.smul_apply, smul_eq_mul, mul_inv]
  · show ((Qb (n + 1))ᵀ *ᵥ ST.hv (n + 1)) i =
      -(ev (n + 1) Dprod)⁻¹ * ((NQ (n + 1))ᵀ *ᵥ ST.hv (n + 1)) i
    rw [QbT_mulVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  · show ST.hv (n + 2) i = 1 * ST.hv (n + 2) i
    rw [one_mul]

theorem Mc_det_ne (n : ℕ) (h : (Mq n).det ≠ 0) : (Mc n).det ≠ 0 := by
  rw [Mc_eq, Matrix.det_mul_row]
  have h1 := (Dprod_pos n).ne'
  have h2 := (Dprod_pos (n + 1)).ne'
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => ?_) h
  fin_cases j <;> simp [h1, h2]

theorem Cas_ne (n : ℕ) : (Y3 n).det ≠ 0 := by
  have hMq : (Mq n).det ≠ 0 := by
    rw [Mq_det]
    exact_mod_cast (PvalZ_pos n).ne'
  have hMc := Mc_det_ne n hMq
  have hKm : (Km n).det ≠ 0 := by
    intro h
    rw [← Km_det, h, mul_zero] at hMc
    exact hMc rfl
  rw [Y3_det]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
    inv_ne_zero (mul_ne_zero (by norm_num) (Del_pos _).ne')) ?_
  refine mul_ne_zero (mul_ne_zero ?_ (T_det n)) hKm
  rw [PU_det]
  norm_num

end Pfq54.CL
