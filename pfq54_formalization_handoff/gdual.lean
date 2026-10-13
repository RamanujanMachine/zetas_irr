import star_aux
import dl_aux
import GW_limit

open Finset Filter Topology Polynomial
open scoped Matrix

noncomputable section

namespace Pfq54.GD

open Pfq54 Pfq54.ST ZetasIrr ZetasIrr.CMF ZetasIrr.GW

/-! ### The dual matrix `G(n) = -W(n)` -/

def G (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := -(Wmat n)

theorem G_det (n : ℕ) : (G n).det ≠ 0 := by
  rw [G, Matrix.det_neg, det_Wmat', Fintype.card_fin]
  exact mul_ne_zero (by norm_num) (neg_ne_zero.mpr (div_ne_zero (F_ne_zero _) (F_ne_zero _)))

theorem G_block (n : ℕ) (j : Fin 4) : G n 3 j = if j = 3 then -1 else 0 := by
  rw [G, Matrix.neg_apply, lastRow_Wmat n j]
  split_ifs <;> simp

def Qb (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := (G n).submatrix Fin.castSucc Fin.castSucc

theorem Qb_eq (n : ℕ) : Qb n = -blk (Wmat n) := by
  ext i j
  rfl

theorem walk_Qb (n : ℕ) : walk Qb n = ((-1 : ℚ) ^ n) • blk (WW n) := by
  induction n with
  | zero =>
    rw [Aux.walk_zero, WW, pow_zero, one_smul]
    ext i j
    simp [blk, Matrix.one_apply, Fin.castSucc_inj]
  | succ n ih =>
    rw [Aux.walk_succ, ih, Qb_eq, WW, blk_mul _ _ (lastRow_Wmat n), Matrix.smul_mul,
      Matrix.mul_neg, smul_neg, pow_succ, mul_comm ((-1 : ℚ) ^ n) (-1), mul_smul, neg_one_smul]

theorem walk_Qb_inv_transpose (n : ℕ) : ((walk Qb n)⁻¹)ᵀ = T n := by
  rw [walk_Qb, inv_sign_smul _ (neg_one_pow_sq n) _ (det_blk_WW n), Matrix.transpose_smul]
  ext k j
  rw [Matrix.smul_apply, Matrix.transpose_apply, T_eq, smul_eq_mul]

/-! ### Rational entries of `Q(n)` -/

def listPoly : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * listPoly l

theorem eval_listPoly (l : List ℤ) (n : ℤ) : (listPoly l).eval n = peval l n := by
  induction l with
  | nil => simp [listPoly, peval]
  | cons a l ih => simp [listPoly, peval, ih]

theorem peval_nonneg (l : List ℤ) (hl : ∀ a ∈ l, 0 ≤ a) (n : ℤ) (hn : 0 ≤ n) :
    0 ≤ peval l n := by
  induction l with
  | nil => simp [peval]
  | cons a l ih =>
    have h1 : 0 ≤ a := hl a List.mem_cons_self
    have h2 := ih fun b hb => hl b (List.mem_cons_of_mem a hb)
    show 0 ≤ a + n * peval l n
    positivity

theorem peval_pos (l : List ℤ) (hl : ∀ a ∈ l, 0 < a) (hne : l ≠ []) (n : ℤ) (hn : 0 ≤ n) :
    0 < peval l n := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a l =>
    have h1 : 0 < a := hl a List.mem_cons_self
    have h2 := peval_nonneg l (fun b hb => (hl b (List.mem_cons_of_mem a hb)).le) n hn
    show 0 < a + n * peval l n
    positivity

theorem cert_D_pos : ∀ b < 12, ∀ a ∈ (cert b).D, 0 < a := by decide +kernel

theorem D_pos (b : ℕ) (hb : b < 12) (n : ℕ) : 0 < peval (cert b).D n :=
  peval_pos _ (cert_D_pos b hb) (certD_ne_nil b) n (by positivity)

def Np (b : ℕ) : Matrix (Fin 3) (Fin 3) ℤ[X] := Matrix.of fun i j => listPoly ((cert b).N i j)

def Dp (b : ℕ) : ℤ[X] := listPoly (cert b).D

def ev (n : ℕ) : ℤ[X] →+* ℚ := (Int.castRingHom ℚ).comp (Polynomial.evalRingHom (n : ℤ))

theorem ev_listPoly (n : ℕ) (l : List ℤ) : ev n (listPoly l) = ((peval l n : ℤ) : ℚ) := by
  simp [ev, eval_listPoly]

theorem blk_blockW_eq (n b : ℕ) (hb : b < 12) :
    blk (blockW b n) = (ev n (Dp b))⁻¹ • (ev n).mapMatrix (Np b) := by
  ext i j
  rw [blk_blockW n b hb i j (D_pos b hb n).ne', Matrix.smul_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, smul_eq_mul, Np, Matrix.of_apply, Dp, ev_listPoly, ev_listPoly,
    div_eq_inv_mul]

def Nprod : Matrix (Fin 3) (Fin 3) ℤ[X] := ((List.range 12).map Np).prod

def Dprod : ℤ[X] := ((List.range 12).map Dp).prod

theorem blk_Wmat_eq (n : ℕ) : blk (Wmat n) = (ev n Dprod)⁻¹ • (ev n).mapMatrix Nprod := by
  rw [blk_Wmat, Nprod, Dprod]
  have key : ∀ m ≤ 12, ((List.range m).map fun b => blk (blockW b n)).prod =
      (ev n ((List.range m).map Dp).prod)⁻¹ • (ev n).mapMatrix ((List.range m).map Np).prod := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.map_append, List.prod_append,
        List.prod_append, List.prod_append, List.map_singleton, List.map_singleton,
        List.map_singleton, List.prod_singleton, List.prod_singleton, List.prod_singleton,
        ih (by omega), blk_blockW_eq n m (by omega), map_mul, map_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, mul_inv]
  exact key 12 le_rfl

def Dq : ℚ[X] := Dprod.map (Int.castRingHom ℚ)

def Nq : Matrix (Fin 3) (Fin 3) ℚ[X] := Nprod.map fun p => p.map (Int.castRingHom ℚ)

def Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ) :=
  Matrix.of fun i j => algebraMap ℚ[X] (RatFunc ℚ) (-(Nq i j)) / algebraMap ℚ[X] (RatFunc ℚ) Dq

theorem eval_map_nat (p : ℤ[X]) (n : ℕ) :
    (p.map (Int.castRingHom ℚ)).eval (n : ℚ) = ev n p := by
  show _ = Int.castRingHom ℚ (p.eval (n : ℤ))
  rw [← Int.cast_natCast (R := ℚ), Polynomial.eval_intCast_map, Int.cast_id]

theorem Dq_eval (n : ℕ) : Dq.eval (n : ℚ) = ev n Dprod := eval_map_nat _ _

theorem Dprod_pos (n : ℕ) : 0 < ev n Dprod := by
  rw [Dprod, map_list_prod]
  refine List.prod_pos fun x hx => ?_
  rw [List.map_map, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [Function.comp_apply, Dp, ev_listPoly]
  exact_mod_cast D_pos b (List.mem_range.mp hb) n

theorem Qb_entry (n : ℕ) (i j : Fin 3) : Qb n i j = -(ev n (Nprod i j)) / ev n Dprod := by
  rw [Qb_eq, Matrix.neg_apply, blk_Wmat_eq, Matrix.smul_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, smul_eq_mul, neg_div, div_eq_inv_mul]

theorem Qr_spec (n : ℕ) (i j : Fin 3) : (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
    Qb n i j = (Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) := by
  have hDq : Dq.eval (n : ℚ) ≠ 0 := by rw [Dq_eval]; exact (Dprod_pos n).ne'
  have hDq0 : Dq ≠ 0 := fun h => hDq (by rw [h, eval_zero])
  set f := Qr i j with hf
  have hden : f.denom.eval (n : ℚ) ≠ 0 := fun h =>
    hDq (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd _ _) h)
  refine ⟨hden, ?_⟩
  have hmul : f.num * Dq = -(Nq i j) * f.denom := by
    have h := RatFunc.num_div_denom f
    rw [hf, Qr, Matrix.of_apply] at h
    rw [div_eq_div_iff (Aux.algebraMap_ne_zero' (RatFunc.denom_ne_zero _))
      (Aux.algebraMap_ne_zero' hDq0), ← map_mul, ← map_mul] at h
    exact RatFunc.algebraMap_injective ℚ h
  have hev := congrArg (Polynomial.eval (n : ℚ)) hmul
  rw [eval_mul, eval_mul, eval_neg, Nq, Matrix.map_apply, eval_map_nat, Dq_eval] at hev
  rw [Qb_entry, div_eq_div_iff (Dprod_pos n).ne' hden]
  linear_combination -hev

/-! ### The limit `Q_∞` -/

def A0 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![14466306412825156665266776467520094021933183105111689813906983 /
        92786114074383579646017531797307392,
      5125772321945341752911611092953750128476881497478301328650225 /
        4217550639744708165728069627150336,
      18356189444388229338248270673811057516850492206894821934114525 /
        2108775319872354082864034813575168;
    -15809894448509004925724088829522086378781546108561063820451375 /
        2969155650380274548672561017513836544,
      -44426254723032064174209467699247987858265927388368593313662147 /
        1484577825190137274336280508756918272,
      -85858973785574548222683957436441014324433584050216734964312775 /
        742288912595068637168140254378459136;
    -4522740284069419193745539199665073642773718968363207054691375 /
        2969155650380274548672561017513836544,
      -16196637745048437651395532947480344867809257829613078177159875 /
        1484577825190137274336280508756918272,
      -51906963227438167781329877586671292853449936381808273314957511 /
        742288912595068637168140254378459136]

theorem Lq_eq : Lq = -A0 := by decide +kernel

def Qinf : Matrix (Fin 3) (Fin 3) ℂ := DL.cC A0

theorem Qinf_entry (k j : Fin 3) :
    -((((Lq.map (Rat.cast : ℚ → ℝ)) k j : ℝ) : ℂ)) = Qinf k j := by
  rw [Qinf, DL.cC_apply, Lq_eq, Matrix.map_apply, Matrix.neg_apply]
  push_cast
  try ring

theorem hlim :
    Tendsto (fun n => balance n * DL.cC (Qb n) * (balance (n + 1))⁻¹) atTop (𝓝 Qinf) := by
  refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 tendsto_gauged k)) j
  have h2 := ((Complex.continuous_ofReal.tendsto _).comp h).neg
  rw [Qinf_entry] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n _
  rw [DL.balance_inv (n + 1) (by omega), balance, Matrix.mul_diagonal, Matrix.diagonal_mul,
    DL.cC_apply, Qb_eq, Matrix.neg_apply]
  simp only [Function.comp_apply, Matrix.of_apply]
  fin_cases k <;> fin_cases j <;> simp <;> ring

/-! ### The characteristic polynomial -/

theorem charpoly_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C (M 0 0 + M 1 1 + M 2 2) * X ^ 2 +
      C (M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0 + M 1 1 * M 2 2 -
        M 1 2 * M 2 1) * X - C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.det_fin_three]
  simp [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne]
  ring

theorem A0_trace : A0 0 0 + A0 1 1 + A0 2 2 = chiA := by
  norm_num [A0, chiA]

theorem A0_minors : A0 0 0 * A0 1 1 - A0 0 1 * A0 1 0 + A0 0 0 * A0 2 2 - A0 0 2 * A0 2 0 +
    A0 1 1 * A0 2 2 - A0 1 2 * A0 2 1 = chiB := by
  norm_num [A0, chiB]

theorem A0_det : A0.det = chiC := by
  rw [Matrix.det_fin_three]
  norm_num [A0, chiC]

theorem A0_charpoly : A0.charpoly = chi := by
  rw [charpoly_fin_three, chi, A0_trace, A0_minors, A0_det]

theorem hchar : Qinf.charpoly = chi.map (algebraMap ℚ ℂ) := by
  rw [Qinf, DL.cC, RingHom.mapMatrix_apply, Matrix.charpoly_map, A0_charpoly]
  rfl

/-! ### The cyclic determinant -/

def wq : Fin 3 → ℚ := ![1, 10, 100]

def B0 : Matrix (Fin 3) (Fin 3) ℚ := A0ᵀ

theorem wq_cast : (![1, 10, 100] : Fin 3 → ℂ) = DL.castV wq := by
  funext i
  fin_cases i <;> simp [DL.castV, wq]

theorem cyc_num : (Matrix.of ![(B0 * B0) *ᵥ wq, B0 *ᵥ wq, wq]).det ≠ 0 := by
  rw [Matrix.det_fin_three]
  norm_num [B0, A0, wq, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply]

theorem of3_cast (a b c : Fin 3 → ℚ) :
    Matrix.of ![DL.castV a, DL.castV b, DL.castV c] = DL.cC (Matrix.of ![a, b, c]) := by
  ext i j
  fin_cases i <;> rfl

theorem cyc_reduce (N : Matrix (Fin 3) (Fin 3) ℂ) (hN : N.det ≠ 0) (w : Fin 3 → ℂ) :
    (Matrix.of ![w, N⁻¹ *ᵥ w, (N⁻¹ * N⁻¹) *ᵥ w]) * (N * N)ᵀ =
      Matrix.of ![(N * N) *ᵥ w, N *ᵥ w, w] := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have hrow : ∀ (R B : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3), (R * B) i = R i ᵥ* B :=
    fun R B i => rfl
  ext i j
  rw [hrow, Matrix.vecMul_transpose]
  fin_cases i
  · rfl
  · show ((N * N) *ᵥ (N⁻¹ *ᵥ w)) j = (N *ᵥ w) j
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  · show ((N * N) *ᵥ ((N⁻¹ * N⁻¹) *ᵥ w)) j = w j
    rw [Matrix.mulVec_mulVec, show N * N * (N⁻¹ * N⁻¹) = 1 by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc N N⁻¹, Matrix.mul_nonsing_inv _ hu,
        Matrix.one_mul, Matrix.mul_nonsing_inv _ hu], Matrix.one_mulVec]

theorem chiC_ne : chiC ≠ 0 := by unfold chiC; norm_num

theorem cC_mul (A B : Matrix (Fin 3) (Fin 3) ℚ) : DL.cC (A * B) = DL.cC A * DL.cC B :=
  map_mul (Rat.castHom ℂ).mapMatrix A B

theorem Qinf_det_ne : Qinf.det ≠ 0 := by
  rw [Qinf, DL.cC_det, A0_det]
  exact_mod_cast chiC_ne

theorem hcyc : (Matrix.of ![(![1, 10, 100] : Fin 3 → ℂ), (Qinf⁻¹)ᵀ *ᵥ ![1, 10, 100],
    ((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ ![1, 10, 100]]).det ≠ 0 := by
  have hN : (Qinfᵀ).det ≠ 0 := by rw [Matrix.det_transpose]; exact Qinf_det_ne
  rw [Matrix.transpose_nonsing_inv]
  intro h0
  have hdet := congrArg Matrix.det (cyc_reduce Qinfᵀ hN ![1, 10, 100])
  rw [Matrix.det_mul, h0, zero_mul] at hdet
  have hcast : Matrix.of ![(Qinfᵀ * Qinfᵀ) *ᵥ ![1, 10, 100], Qinfᵀ *ᵥ ![1, 10, 100],
      (![1, 10, 100] : Fin 3 → ℂ)] = DL.cC (Matrix.of ![(B0 * B0) *ᵥ wq, B0 *ᵥ wq, wq]) := by
    rw [wq_cast, Qinf, DL.transpose_cC, show A0ᵀ = B0 from rfl, ← cC_mul, DL.cC_mulVec,
      DL.cC_mulVec, of3_cast]
  rw [hcast, DL.cC_det] at hdet
  exact cyc_num (by exact_mod_cast hdet.symm)

/-! ### The forward matrix and the intertwining -/

def Emat' (n : ℕ) : Matrix (Fin 4) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, -(n : ℚ) * (450 * n + 29), -(n : ℚ) ^ 2 * (101250 * n ^ 2 + 12975 * n + 406);
     0, 1, 0;
     0, 0, 1]

def Hmat' (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-6 * (n : ℚ) ^ 2 * (10 * n + 1) * (12 * n + 1) * (193 * n + 13),
       -(n : ℚ) * (12 * n + 1) * (2550 * n ^ 2 + 523 * n + 23),
       (12 * (n : ℚ) + 1) * (450 * n ^ 2 + 41 * n + 1);
     (10 * (n : ℚ) + 1) * (450 * n ^ 2 + 21 * n - 1), (-25 * (n : ℚ) - 2) * (18 * n - 1), -1;
     -20 * (n : ℚ) - 2, 2, 0]

def Jmat' : Matrix (Fin 3) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

def Kmat' (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := Emat' n * Hmat' n * Jmat'

def Lsel : Matrix (Fin 3) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem Lsel_Emat (n : ℕ) : Lsel * Emat' n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lsel, Emat', Matrix.mul_apply, Fin.sum_univ_four]

theorem Hmat'_det (n : ℕ) : (Hmat' n).det = 2 * Del n := by
  rw [Matrix.det_fin_three, Del, Aux.prod_Icc_8_12]
  simp [Hmat']
  ring

theorem Hmat'_det_ne (n : ℕ) : (Hmat' n).det ≠ 0 := by
  rw [Hmat'_det]
  exact mul_ne_zero two_ne_zero (Del_pos n).ne'

theorem Kmat'_col3 (n : ℕ) (i : Fin 4) : Kmat' n i 3 = 0 := by
  simp [Kmat', Jmat', Matrix.mul_apply, Fin.sum_univ_three]

theorem Ginv_row3 (n : ℕ) (k : Fin 4) : (G n)⁻¹ 3 k = if k = 3 then -1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv (G n) (isUnit_iff_ne_zero.mpr (G_det n))) 3) k
  rw [Matrix.mul_apply, Fin.sum_univ_four, G_block, G_block, G_block, G_block,
    Matrix.one_apply] at h
  simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true, zero_mul, zero_add,
    neg_one_mul] at h
  by_cases hk : k = 3
  · subst hk
    simp only [ite_true] at h ⊢
    linarith
  · rw [if_neg hk]
    rw [if_neg (Ne.symm hk)] at h
    linarith

theorem KG_P (n : ℕ) :
    Kmat' n * ((G n)ᵀ)⁻¹ * (Jmat'ᵀ * Jmat') = Kmat' n * ((G n)ᵀ)⁻¹ := by
  have hcol : ∀ i : Fin 4, (Kmat' n * ((G n)ᵀ)⁻¹) i 3 = 0 := by
    intro i
    rw [← Matrix.transpose_nonsing_inv, Matrix.mul_apply, Fin.sum_univ_four]
    simp only [Matrix.transpose_apply, Ginv_row3, Fin.isValue, Fin.reduceEq, ite_false, ite_true,
      mul_zero, zero_add, Kmat'_col3, zero_mul]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases j <;> simp [Jmat', Matrix.mul_apply, Fin.sum_univ_three, hcol]

def Fm (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  ST.Rsc n • (Kmat' n * ((G n)ᵀ)⁻¹ * Jmat'ᵀ * (Hmat' (n + 1))⁻¹ * Lsel)

theorem intertwine (n : ℕ) : Fm n * Kmat' (n + 1) * (G n)ᵀ = ST.Rsc n • Kmat' n := by
  rw [Fm, Matrix.smul_mul, Matrix.smul_mul]
  congr 1
  have h1 : Lsel * Emat' (n + 1) = 1 := Lsel_Emat (n + 1)
  have h2 : (Hmat' (n + 1))⁻¹ * Hmat' (n + 1) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Hmat'_det_ne _))
  have h3 : ((G n)ᵀ)⁻¹ * (G n)ᵀ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr (G_det n))
  calc Kmat' n * ((G n)ᵀ)⁻¹ * Jmat'ᵀ * (Hmat' (n + 1))⁻¹ * Lsel * Kmat' (n + 1) * (G n)ᵀ
      = Kmat' n * ((G n)ᵀ)⁻¹ * (Jmat'ᵀ * (((Hmat' (n + 1))⁻¹ * ((Lsel * Emat' (n + 1)) *
          Hmat' (n + 1))) * Jmat')) * (G n)ᵀ := by
        simp only [Kmat', Matrix.mul_assoc]
    _ = Kmat' n * ((G n)ᵀ)⁻¹ * (Jmat'ᵀ * Jmat') * (G n)ᵀ := by
        rw [h1, Matrix.one_mul, h2, Matrix.one_mul]
    _ = Kmat' n * ((G n)ᵀ)⁻¹ * (G n)ᵀ := by rw [KG_P]
    _ = Kmat' n := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]

end Pfq54.GD
