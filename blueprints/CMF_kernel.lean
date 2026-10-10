/-
# CMF transport, part 5: the kernels at `p_N`

* `ker_pN`: the kernel of the point `p_N` is `R_N` (PDF Part I / VII §2).
* `dual_ker_eq`: the kernel of the dual point `p_N* = (1 - a, -b)` is `R*_N(t - 12N - 1)`, the
  dual kernel at the end of the walk ("at the endpoint substitute `s = t + 12N + 1`").
* `Jm_pN`: the concomitant of `p_N` is the integer matrix `J_N` of the PDF.
* `dualL_zero`: the four first-functional moments of the initial dual kernel `(s-1)/s²` are
  `g₀ = (Z₂ - 2Z₃, Z₂ - 1, -1/2, 1/3)` (PDF Part VII §7).
* `Lfun_cubic_Z2`: the `Z₂`-coefficient of the fourth moment `𝓛_{2N}[(-t)³ R_N]` is `-1`
  (the residue sum of `-t³ R_N(t)`); the first three moments have no `Z₂` part
  (`Lfun_linFormKernel_support`). This gives the block form `W_N = [[V_N, *], [0, 1]]`.
-/
import CMF_path
import CMF_pairing

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-- Shortcut instance (otherwise re-synthesised slowly inside every `field_simp`). -/
instance faithfulSMul_polynomial_ratFunc : FaithfulSMul ℚ[X] ℚ⟮X⟯ := inferInstance
instance addMonoidHomClass_algebraMap_ratFunc :
    AddMonoidHomClass (ℚ[X] →+* ℚ⟮X⟯) ℚ[X] ℚ⟮X⟯ := inferInstance
instance addMonoidHomClass_C_polynomial : AddMonoidHomClass (ℚ →+* ℚ[X]) ℚ ℚ[X] := inferInstance

/-! ### Pochhammer symbols as products of linear factors -/

theorem poch_succ (c : ℚ) (r : ℕ) : poch c (r + 1) = poch c r * (X + C c + (r : ℚ[X])) := by
  rw [poch, ascPochhammer_succ_right, Polynomial.mul_comp, ← poch, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.natCast_comp]

theorem poch_eq_lp (c : ℤ) (r : ℕ) : poch (c : ℚ) r = lp (ival (1 - c - r) r) := by
  induction r with
  | zero => simp [poch, ascPochhammer_zero, ival_zero, lp_zero]
  | succ r ih =>
    rw [poch_succ, ih, show (1 - c - ((r + 1 : ℕ) : ℤ)) = (1 - c - r) - 1 by push_cast; ring,
      ival_succ', show (1 - c - (r : ℤ) - 1 + 1) = 1 - c - r by ring, lp_cons, mul_comm]
    congr 1
    push_cast
    simp only [map_sub, map_add, map_one, map_natCast]
    ring

theorem taylor_poch (c d : ℚ) (r : ℕ) : taylor c (poch d r) = poch (d + c) r := by
  rw [poch, poch, Polynomial.taylor_apply, Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_add]
  ring

theorem pairKer_eval (b a zl pl : ℤ) (zn pn : ℕ) (hzl : 1 - b = zl) (hpl : 1 - a = pl)
    (hz : (b - a).toNat = zn) (hp : (a - b).toNat = pn) :
    pairKer b a = lin (ival zl zn) (ival pl pn) := by
  rw [pairKer, hzl, hpl, hz, hp]

/-! ### The kernel of `p_N` -/

theorem pN_a (N : ℕ) : (pN N).a = ![1 + 11 * (N : ℤ), 1 + 12 * (N : ℤ), -16 * (N : ℤ), -17 * (N : ℤ),
    2 + 10 * (N : ℤ)] := by
  funext i; fin_cases i <;> simp [pN, Off.toPt, baseA, Off.vecA]
theorem pN_b (N : ℕ) : (pN N).b = ![0, (N : ℤ), 2 * (N : ℤ), -(N : ℤ), -2 * (N : ℤ)] := by
  funext i; fin_cases i <;> simp [pN, Off.toPt, baseB, Off.vecB]

/-- **The kernel of `p_N` is `R_N`.** -/
theorem ker_pN (N : ℕ) : (pN N).ker = Rker N := by
  rw [Pt.ker, ker, pN_a, pN_b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  rw [pairKer_eval 0 (2 + 10 * N) 1 (-1 - 10 * N) 0 (10 * N + 2) (by ring) (by ring) (by omega)
      (by omega),
    pairKer_eval N (1 + 11 * N) (1 - N) (-11 * N) 0 (10 * N + 1) (by ring) (by ring) (by omega)
      (by omega),
    pairKer_eval (2 * N) (1 + 12 * N) (1 - 2 * N) (-12 * N) 0 (10 * N + 1) (by ring) (by ring)
      (by omega) (by omega),
    pairKer_eval (-N) (-16 * N) (1 + N) (1 + 16 * N) (15 * N) 0 (by ring) (by ring) (by omega)
      (by omega),
    pairKer_eval (-2 * N) (-17 * N) (1 + 2 * N) (1 + 17 * N) (15 * N) 0 (by ring) (by ring)
      (by omega) (by omega)]
  have p1 : poch (-17 * (N : ℚ)) (15 * N) = lp (ival (1 + 2 * N) (15 * N)) := by
    rw [show (-17 * (N : ℚ)) = ((-17 * (N : ℤ) : ℤ) : ℚ) by push_cast; ring, poch_eq_lp]
    congr 2; push_cast; ring
  have p2 : poch (-16 * (N : ℚ)) (15 * N) = lp (ival (1 + N) (15 * N)) := by
    rw [show (-16 * (N : ℚ)) = ((-16 * (N : ℤ) : ℤ) : ℚ) by push_cast; ring, poch_eq_lp]
    congr 2; push_cast; ring
  have p3 : poch (0 : ℚ) (10 * N + 2) = lp (ival (-1 - 10 * N) (10 * N + 2)) := by
    rw [show (0 : ℚ) = ((0 : ℤ) : ℚ) by norm_num, poch_eq_lp]
    congr 2; push_cast; ring
  have p4 : poch (N : ℚ) (10 * N + 1) = lp (ival (-11 * N) (10 * N + 1)) := by
    rw [show ((N : ℚ)) = ((N : ℤ) : ℚ) by norm_num, poch_eq_lp]
    congr 2; push_cast; ring
  have p5 : poch (2 * (N : ℚ)) (10 * N + 1) = lp (ival (-12 * N) (10 * N + 1)) := by
    rw [show (2 * (N : ℚ)) = ((2 * (N : ℤ) : ℤ) : ℚ) by push_cast; ring, poch_eq_lp]
    congr 2; push_cast; ring
  rw [Rker, p1, p2, p3, p4, p5]
  simp only [lin, ival_zero, lp_zero, map_one, map_mul]
  have h1 := Aux.algebraMap_ne_zero' (lp_ne_zero (ival (-1 - 10 * N) (10 * N + 2)))
  have h2 := Aux.algebraMap_ne_zero' (lp_ne_zero (ival (-11 * N) (10 * N + 1)))
  have h3 := Aux.algebraMap_ne_zero' (lp_ne_zero (ival (-12 * N) (10 * N + 1)))
  field_simp
  try ring

/-! ### The kernel of the dual point -/

theorem count_ival' (lo : ℤ) (n : ℕ) (k : ℤ) :
    (ival lo n).count k = if lo ≤ k ∧ k < lo + n then 1 else 0 := count_ival lo n k

/-- **The kernel of `p_N*` is `R*_N(t - 12N - 1)`.** -/
theorem dual_ker_eq (N : ℕ) :
    (pN N).dual.ker = RatFunc.laurent (-(12 * (N : ℚ) + 1)) (RkerStar N) := by
  rw [Pt.ker, ker]
  simp only [Pt.dual_a, Pt.dual_b, pN_a, pN_b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val]
  rw [pairKer_eval (-0) (1 - (2 + 10 * N)) 1 (2 + 10 * N) (10 * N + 1) 0 (by ring) (by ring)
      (by omega) (by omega),
    pairKer_eval (-N) (1 - (1 + 11 * N)) (1 + N) (1 + 11 * N) (10 * N) 0 (by ring) (by ring)
      (by omega) (by omega),
    pairKer_eval (-(2 * N)) (1 - (1 + 12 * N)) (1 + 2 * N) (1 + 12 * N) (10 * N) 0 (by ring)
      (by ring) (by omega) (by omega),
    pairKer_eval (- -N) (1 - -16 * N) (1 - N) (-16 * N) 0 (15 * N + 1) (by ring) (by ring)
      (by omega) (by omega),
    pairKer_eval (-(-2 * N)) (1 - -17 * N) (1 - 2 * N) (-17 * N) 0 (15 * N + 1) (by ring) (by ring)
      (by omega) (by omega)]
  have hZ : ival 1 (10 * N + 1) + ival (1 + N) (10 * N) + ival (1 + 2 * N) (10 * N) =
      ival 1 (11 * N) + ival (1 + N) (11 * N) + ival (1 + 2 * N) (8 * N + 1) := by
    refine Multiset.ext.mpr fun k => ?_
    simp only [Multiset.count_add, count_ival']
    push_cast
    split_ifs <;> omega
  have p1 : poch ((N : ℚ) + 1 + -(12 * (N : ℚ) + 1)) (11 * N) = lp (ival 1 (11 * N)) := by
    rw [show ((N : ℚ) + 1 + -(12 * (N : ℚ) + 1)) = ((-11 * (N : ℤ) : ℤ) : ℚ) by push_cast; ring,
      poch_eq_lp]
    congr 2; push_cast; ring
  have p2 : poch ((1 : ℚ) + -(12 * (N : ℚ) + 1)) (11 * N) = lp (ival (1 + N) (11 * N)) := by
    rw [show ((1 : ℚ) + -(12 * (N : ℚ) + 1)) = ((-12 * (N : ℤ) : ℤ) : ℚ) by push_cast; ring,
      poch_eq_lp]
    congr 2; push_cast; ring
  have p3 : poch (2 * (N : ℚ) + -(12 * (N : ℚ) + 1)) (8 * N + 1) =
      lp (ival (1 + 2 * N) (8 * N + 1)) := by
    rw [show (2 * (N : ℚ) + -(12 * (N : ℚ) + 1)) = ((-10 * (N : ℤ) - 1 : ℤ) : ℚ) by
      push_cast; ring, poch_eq_lp]
    congr 2; push_cast; ring
  have p4 : poch (13 * (N : ℚ) + 1 + -(12 * (N : ℚ) + 1)) (15 * N + 1) =
      lp (ival (-16 * N) (15 * N + 1)) := by
    rw [show (13 * (N : ℚ) + 1 + -(12 * (N : ℚ) + 1)) = ((N : ℤ) : ℚ) by push_cast; ring,
      poch_eq_lp]
    congr 2; push_cast; ring
  have p5 : poch (14 * (N : ℚ) + 1 + -(12 * (N : ℚ) + 1)) (15 * N + 1) =
      lp (ival (-17 * N) (15 * N + 1)) := by
    rw [show (14 * (N : ℚ) + 1 + -(12 * (N : ℚ) + 1)) = ((2 * (N : ℤ) : ℤ) : ℚ) by push_cast; ring,
      poch_eq_lp]
    congr 2; push_cast; ring
  rw [RkerStar, RatFunc.laurent_div, Polynomial.taylor_mul, Polynomial.taylor_mul, Polynomial.taylor_mul, taylor_poch, taylor_poch,
    taylor_poch, taylor_poch, taylor_poch, p1, p2, p3, p4, p5, ← lp_add, ← lp_add, ← hZ, lp_add,
    lp_add]
  simp only [lin, ival_zero, lp_zero, map_one, map_mul]
  have h1 := Aux.algebraMap_ne_zero' (lp_ne_zero (ival (-16 * N) (15 * N + 1)))
  have h2 := Aux.algebraMap_ne_zero' (lp_ne_zero (ival (-17 * N) (15 * N + 1)))
  field_simp
  try ring

/-! ### The concomitant of `p_N` -/

theorem e_al_pN (N : ℕ) :
    e1 (al (pN N).a) = -1 ∧ e2 (al (pN N).a) = -455 * (N : ℚ) ^ 2 - 43 * N - 1 ∧
      e3 (al (pN N).a) = -1650 * (N : ℚ) ^ 3 + 10 * N ^ 2 + 20 * N + 1 ∧
      e4 (al (pN N).a) = 54904 * (N : ℚ) ^ 4 + 11206 * N ^ 3 + 857 * N ^ 2 + 23 * N := by
  simp only [e1, e2, e3, e4, al, pN_a, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem e_bq_pN (N : ℕ) :
    e1 (bq (pN N).b) = 0 ∧ e2 (bq (pN N).b) = -5 * (N : ℚ) ^ 2 ∧ e3 (bq (pN N).b) = 0 ∧
      e4 (bq (pN N).b) = 4 * (N : ℚ) ^ 4 := by
  simp only [e1, e2, e3, e4, bq, pN_b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem Jm_pN (N : ℕ) : Jm (pN N).a (pN N).b = (Jmat N).map (Int.cast : ℤ → ℚ) := by
  obtain ⟨hE1, hE2, hE3, hE4⟩ := e_al_pN N
  obtain ⟨hF1, hF2, hF3, hF4⟩ := e_bq_pN N
  ext i j
  rw [Jm, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [JmE, eS_1, eS_2, eS_3, eS_4, Jmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq,
      ite_true, ite_false, hE1, hE2, hE3, hE4, hF1, hF2, hF3, hF4] <;>
    push_cast <;> ring

/-! ### The initial dual kernel and its first-functional moments -/

theorem dual_ker_zero :
    (pN 0).dual.ker = algebraMap ℚ[X] ℚ⟮X⟯ (X - C 1) / algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 2) := by
  rw [Pt.ker, ker]
  simp only [Pt.dual_a, Pt.dual_b, pN_a, pN_b, Nat.cast_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  rw [pairKer_eval (-0) (1 - (2 + 10 * 0)) 1 2 1 0 (by ring) (by ring) (by decide) (by decide),
    pairKer_eval (-0) (1 - (1 + 11 * 0)) 1 1 0 0 (by ring) (by ring) (by decide) (by decide),
    pairKer_eval (-(2 * 0)) (1 - (1 + 12 * 0)) 1 1 0 0 (by ring) (by ring) (by decide) (by decide),
    pairKer_eval (- -0) (1 - -16 * 0) 1 0 0 1 (by ring) (by ring) (by decide) (by decide),
    pairKer_eval (-(-2 * 0)) (1 - -17 * 0) 1 0 0 1 (by ring) (by ring) (by decide) (by decide)]
  simp only [ival_succ, ival_zero, lin_cons_left, lin_zero, lin, lp_cons, lp_zero, map_one,
    map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_pow]
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  push_cast
  simp only [map_zero, map_one]
  field_simp
  try ring

theorem dualL_zero_eq (r : ℕ) :
    (-RatFunc.X) ^ r * (pN 0).dual.ker =
      algebraMap ℚ[X] ℚ⟮X⟯ ((-X) ^ r * (X - C 1)) / algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 2) := by
  rw [dual_ker_zero, ← mul_div_assoc]
  congr 1
  simp only [map_mul, map_pow, map_neg, RatFunc.algebraMap_X]

theorem dualL_zero_denom (r : ℕ) : ((-RatFunc.X) ^ r * (pN 0).dual.ker).denom ∣ X ^ 4 := by
  rw [dualL_zero_eq]
  exact (RatFunc.denom_div_dvd _ _).trans (pow_dvd_pow _ (by norm_num))

theorem Icc_one_four' : Finset.Icc (1 : ℕ) 4 = {1, 2, 3, 4} := rfl

theorem sum_Icc14 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + (f 2 + (f 3 + f 4)) := by
  rw [Icc_one_four', Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Simp set for the partial-fraction side goals of `dualL_zero`. -/
macro "pf_simp" : tactic => `(tactic|
  simp only [sum_Icc14, Nat.reduceEqDiff, ite_true, ite_false, map_zero, map_one, map_mul,
    map_pow, map_neg, map_sub, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C, pow_zero,
    pow_one, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, sub_zero, neg_zero])

theorem bsum_one_C' (k : ℚ) : Aux.bsum 1 (C k) = k := by
  rw [Aux.bsum_eq_range 1 _ 0 (by simp)]
  simp

theorem bsum_one_quad (a b c : ℚ) :
    Aux.bsum 1 (C a * X ^ 2 + C b * X + C c) = a / 6 + b / 2 + c := by
  rw [Aux.bsum_eq_range 1 _ 2 (by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))]
  simp [Finset.sum_range_succ, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    Polynomial.bernoulli_eval_one, bernoulli'_one, bernoulli'_two]
  ring

/-- The first-functional moments of `r₀(s) = (s-1)/s²`: `g₀ = (Z₂ - 2Z₃, Z₂ - 1, -1/2, 1/3)`. -/
theorem dualL_zero :
    mv Lfun 0 (pN 0).dual.ker =
      ![Zsym 2 - (2 : ℚ) • Zsym 3, Zsym 2 - Zsym 0, (-1 / 2 : ℚ) • Zsym 0, (1 / 3 : ℚ) • Zsym 0] := by
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  funext j
  fin_cases j
  · show Lfun 0 ((-RatFunc.X) ^ 0 * (pN 0).dual.ker) = _
    rw [Aux.Lfun_zero_of_decomp _ (dualL_zero_denom 0) 0
      (fun k => if k = 1 then 1 else if k = 2 then -1 else 0) ?_]
    · rw [sum_Icc14]; simp only [Aux.bsum, Polynomial.sum_zero_index, Nat.reduceEqDiff, ite_true, ite_false, Nat.cast_one, Nat.cast_ofNat, mul_one, mul_zero, mul_neg, zero_smul, add_zero, zero_add, one_smul, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]; module
    · rw [dualL_zero_eq]; pf_simp; field_simp; ring
  · show Lfun 0 ((-RatFunc.X) ^ 1 * (pN 0).dual.ker) = _
    rw [Aux.Lfun_zero_of_decomp _ (dualL_zero_denom 1) (C (-1)) (fun k => if k = 1 then 1 else 0) ?_]
    · rw [sum_Icc14, bsum_one_C']; simp only [Nat.reduceEqDiff, ite_true, ite_false, Nat.cast_one, Nat.cast_ofNat, mul_one, mul_zero, zero_smul, add_zero, zero_add, one_smul, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]; module
    · rw [dualL_zero_eq]; pf_simp; field_simp; ring
  · show Lfun 0 ((-RatFunc.X) ^ 2 * (pN 0).dual.ker) = _
    rw [Aux.Lfun_zero_of_decomp _ (dualL_zero_denom 2) (C 1 * X + C (-1)) (fun _ => 0) ?_]
    · rw [sum_Icc14, bsum_one_lin']; simp only [mul_zero, zero_smul, add_zero, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]; module
    · rw [dualL_zero_eq]; pf_simp; field_simp; ring
  · show Lfun 0 ((-RatFunc.X) ^ 3 * (pN 0).dual.ker) = _
    rw [Aux.Lfun_zero_of_decomp _ (dualL_zero_denom 3) (C (-1) * X ^ 2 + C 1 * X + C 0)
      (fun _ => 0) ?_]
    · rw [sum_Icc14, bsum_one_quad]; simp only [mul_zero, zero_smul, add_zero, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]; module
    · rw [dualL_zero_eq]; pf_simp; field_simp; ring
where
  bsum_one_lin' (a b : ℚ) : Aux.bsum 1 (C a * X + C b) = a / 2 + b := by
    rw [Aux.bsum_eq_range 1 _ 1 (by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))]
    simp [Finset.sum_range_succ, Polynomial.coeff_C, Polynomial.coeff_X,
      Polynomial.bernoulli_eval_one, bernoulli'_one]
    ring

/-! ### The `Z₂`-coefficient of the fourth moment of `R_N` -/

/-- Generalization of `residue_sum_eq_zero`: if `∑ c_{h,r}(t-h)^{-r} - s/t` has degree `≤ -2`,
the residues sum to `s`. -/
theorem residue_sum_eq (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) (s : ℚ)
    (hdeg : DegLE (-2) (ppSum R b c - RatFunc.C s * RatFunc.X⁻¹)) :
    ∑ h ∈ R, (if 1 ≤ b h then c h 1 else 0) = s := by
  set s₀ := ∑ h ∈ R, (if 1 ≤ b h then c h 1 else 0) with hs₀
  have hsplit : ppSum R b c - RatFunc.C s₀ * RatFunc.X⁻¹ =
      ∑ h ∈ R, (∑ r ∈ Finset.Icc 1 (b h), RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹ -
        RatFunc.C (if 1 ≤ b h then c h 1 else 0) * RatFunc.X⁻¹) := by
    rw [Finset.sum_sub_distrib, hs₀, map_sum, Finset.sum_mul]; rfl
  have h2 : DegLE (-2) (ppSum R b c - RatFunc.C s₀ * RatFunc.X⁻¹) := by
    rw [hsplit]
    refine DegLE.sum _ _ fun h _ => ?_
    by_cases hb : 1 ≤ b h
    · simp only [hb, ↓reduceIte]
      rw [← Finset.insert_Icc_add_one_left_eq_Icc hb, Finset.sum_insert (by simp),
        add_sub_right_comm]
      refine (DegLE.inv_X_sub_C_sub_inv_X h (c h 1)).add (DegLE.sum _ _ fun r hr => ?_)
      exact (DegLE.basic h (c h r) r).mono (by have := (Finset.mem_Icc.mp hr).1; omega)
    · simp only [hb, ↓reduceIte]
      rw [Finset.Icc_eq_empty (by omega)]
      simp [DegLE]
  have h3 : DegLE (-2) (RatFunc.C (s₀ - s) * RatFunc.X⁻¹) := by
    have := hdeg.add h2.neg
    rwa [show ppSum R b c - RatFunc.C s * RatFunc.X⁻¹ +
      -(ppSum R b c - RatFunc.C s₀ * RatFunc.X⁻¹) = RatFunc.C (s₀ - s) * RatFunc.X⁻¹ by
        rw [map_sub]; ring] at this
  by_contra hne
  have hne' : s₀ - s ≠ 0 := sub_ne_zero.mpr hne
  rcases h3 with h0 | h1
  · rcases mul_eq_zero.mp h0 with h | h
    · exact hne' ((_root_.map_eq_zero_iff _ RatFunc.C_injective).mp h)
    · exact RatFunc.X_ne_zero (inv_eq_zero.mp h)
  · rw [RatFunc.intDegree_mul ((_root_.map_ne_zero _).mpr hne') (inv_ne_zero RatFunc.X_ne_zero),
      RatFunc.intDegree_C, RatFunc.intDegree_inv, RatFunc.intDegree_X] at h1
    omega

theorem DegLE_div (P Q : ℚ[X]) (hQ : Q ≠ 0) (h : P = 0 ∨ P.natDegree + 2 ≤ Q.natDegree) :
    DegLE (-2) (algebraMap ℚ[X] ℚ⟮X⟯ P / algebraMap ℚ[X] ℚ⟮X⟯ Q) := by
  rcases h with rfl | h
  · left; simp
  by_cases hP : P = 0
  · left; simp [hP]
  right
  rw [RatFunc.intDegree_div (Aux.algebraMap_ne_zero' hP) (Aux.algebraMap_ne_zero' hQ),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  omega

/-- The numerator and denominator of `R_N`. -/
def Rnum (N : ℕ) : ℚ[X] := poch (-17 * N) (15 * N) * poch (-16 * N) (15 * N)
def Rden (N : ℕ) : ℚ[X] := poch 0 (10 * N + 2) * poch N (10 * N + 1) * poch (2 * N) (10 * N + 1)

theorem Rker_eq (N : ℕ) : Rker N = algebraMap ℚ[X] ℚ⟮X⟯ (Rnum N) / algebraMap ℚ[X] ℚ⟮X⟯ (Rden N) :=
  rfl

theorem Rnum_monic (N : ℕ) : (Rnum N).Monic := by
  rw [Rnum, num_eq]; exact Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem Rden_monic (N : ℕ) : (Rden N).Monic := by
  rw [Rden, den_eq]; exact Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem Rnum_natDegree (N : ℕ) : (Rnum N).natDegree = 30 * N := by
  rw [Rnum, num_eq, natDegree_prod_X_sub_C]; simp [zeroSet]; ring

theorem Rden_natDegree (N : ℕ) : (Rden N).natDegree = 30 * N + 4 := by
  rw [Rden, den_eq, natDegree_prod_X_sub_C]; simp [poleSet]; ring

theorem Rden_splits (N : ℕ) : Polynomial.Splits (Rden N) := by
  rw [Rden, den_eq]
  exact Polynomial.Splits.multisetProd fun f hf => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Polynomial.Splits.X_sub_C a

attribute [irreducible] Rnum Rden

/-- The numerator `X³ R_num` is nonzero. -/
theorem cubic_num_ne_zero (N : ℕ) : X ^ 3 * Rnum N ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Rnum_monic N).ne_zero

theorem cubic_num_natDegree (N : ℕ) : (X ^ 3 * Rnum N).natDegree = 30 * N + 3 := by
  rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (Rnum_monic N).ne_zero,
    Polynomial.natDegree_X_pow, Rnum_natDegree]
  omega

/-- The fraction `X³ R_num / R_den` has integer degree `-1`. -/
theorem cubic_intDegree (N : ℕ) :
    (algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 3 * Rnum N) / algebraMap ℚ[X] ℚ⟮X⟯ (Rden N)).intDegree = -1 := by
  rw [RatFunc.intDegree_div (Aux.algebraMap_ne_zero' (cubic_num_ne_zero N))
      (Aux.algebraMap_ne_zero' (Rden_monic N).ne_zero),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, cubic_num_natDegree,
    Rden_natDegree]
  omega

/-- The degree bound for `X⁴ R_num - R_den`. -/
theorem cubic_sub_degree (N : ℕ) :
    X ^ 3 * Rnum N * X - Rden N * 1 = 0 ∨
      (X ^ 3 * Rnum N * X - Rden N * 1).natDegree + 2 ≤ (Rden N * X).natDegree := by
  have hden0 : Rden N ≠ 0 := (Rden_monic N).ne_zero
  have hnum1 : X ^ 3 * Rnum N * X ≠ 0 := mul_ne_zero (cubic_num_ne_zero N) Polynomial.X_ne_zero
  by_cases h0 : X ^ 3 * Rnum N * X - Rden N * 1 = 0
  · exact Or.inl h0
  right
  have e1 : (X ^ 3 * Rnum N * X).natDegree = 30 * N + 4 := by
    rw [Polynomial.natDegree_mul (cubic_num_ne_zero N) Polynomial.X_ne_zero,
      cubic_num_natDegree, Polynomial.natDegree_X]
  have hlt : (X ^ 3 * Rnum N * X - Rden N * 1).degree < (X ^ 3 * Rnum N * X).degree := by
    rw [mul_one]
    refine Polynomial.degree_sub_lt_left ?_ hnum1 ?_
    · rw [Polynomial.degree_eq_natDegree hnum1, Polynomial.degree_eq_natDegree hden0, e1,
        Rden_natDegree]
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_pow,
        Polynomial.leadingCoeff_X, (Rnum_monic N).leadingCoeff, (Rden_monic N).leadingCoeff]
      rw [one_mul, one_mul]
  rw [Polynomial.natDegree_mul hden0 Polynomial.X_ne_zero, Polynomial.natDegree_X, Rden_natDegree]
  have := Polynomial.natDegree_lt_natDegree h0 hlt
  omega

/-- `X³ R_num / R_den - 1/X` has degree `≤ -2`. -/
theorem cubic_DegLE (N : ℕ) :
    DegLE (-2) (algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 3 * Rnum N) / algebraMap ℚ[X] ℚ⟮X⟯ (Rden N) -
      RatFunc.C 1 * RatFunc.X⁻¹) := by
  have hden0 : Rden N ≠ 0 := (Rden_monic N).ne_zero
  rw [map_one, one_mul, ← RatFunc.algebraMap_X, inv_eq_one_div,
    ← map_one (algebraMap ℚ[X] ℚ⟮X⟯),
    div_sub_div _ _ (Aux.algebraMap_ne_zero' hden0) (Aux.algebraMap_ne_zero' Polynomial.X_ne_zero),
    ← map_mul, ← map_mul, ← map_sub, ← map_mul]
  exact DegLE_div _ _ (mul_ne_zero hden0 Polynomial.X_ne_zero) (cubic_sub_degree N)

/-- `(-t)³ R_N = -(X³ R_num / R_den)`. -/
theorem cubic_eq (N : ℕ) : (-RatFunc.X) ^ 3 * Rker N =
    RatFunc.C (-1) * (algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 3 * Rnum N) / algebraMap ℚ[X] ℚ⟮X⟯ (Rden N)) := by
  rw [Rker_eq, ← mul_div_assoc, ← mul_div_assoc]
  congr 1
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_neg, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  rw [map_neg, map_one]
  ring

/-- The `Z₂`-coefficient of a proper fraction with split denominator equals the residue sum. -/
theorem Lfun_Z2_eq_residue (K : ℤ) (g : ℚ⟮X⟯) (hproper : g.num.natDegree < g.denom.natDegree)
    (hsplit : g.denom.roots.card = g.denom.natDegree) (s : ℚ)
    (hdeg : DegLE (-2) (g - RatFunc.C s * RatFunc.X⁻¹)) : Lfun K g 2 = s := by
  have hpoly : polyPart g = 0 := polyPart_eq_zero_of_proper g hproper
  obtain ⟨c, hc⟩ := exists_eq_ppSum g hproper hsplit
  have hD : 1 ≤ g.denom.natDegree := by omega
  rw [Lfun_apply_of_ne_zero _ _ hpoly 2 two_ne_zero]
  have hinner : ∀ h ∈ g.denom.roots.toFinset, ∑ s ∈ Finset.range (g.denom.natDegree + 1),
      (s : ℚ) * pfCoeff g h s * (if s + 1 = 2 then 1 else 0) = c h 1 := by
    intro h hh
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))]
    · have hb : 1 ≤ g.denom.roots.count h :=
        Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hh)
      have := pfCoeff_ppSum g.denom.roots.toFinset (fun h => g.denom.roots.count h) c hh (le_refl 1)
      rw [← hc] at this
      rw [this, ite_eq_left hb, ite_eq_left rfl, Nat.cast_one, one_mul, mul_one]
    · intro s _ hs
      rw [if_neg (by omega), mul_zero]
  rw [Finset.sum_congr rfl hinner]
  have key := residue_sum_eq g.denom.roots.toFinset (fun h => g.denom.roots.count h) c s
    (by rw [← hc]; exact hdeg)
  rw [← key]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hb : 1 ≤ g.denom.roots.count h :=
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hh)
  rw [ite_eq_left hb]

/-- The `Z₂`-coefficient of the fourth moment: `𝓛_{2N}[(-t)³ R_N(t)]` has `Z₂`-coefficient `-1`. -/
theorem Lfun_cubic_Z2 (N : ℕ) : Lfun (2 * N) ((-RatFunc.X) ^ 3 * Rker N) 2 = -1 := by
  rw [cubic_eq, Aux.Lfun_C_mul, Finsupp.smul_apply, smul_eq_mul]
  have hden0 : Rden N ≠ 0 := (Rden_monic N).ne_zero
  have hdeg := cubic_intDegree N
  have hproper : (algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 3 * Rnum N) /
      algebraMap ℚ[X] ℚ⟮X⟯ (Rden N)).num.natDegree <
      (algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 3 * Rnum N) / algebraMap ℚ[X] ℚ⟮X⟯ (Rden N)).denom.natDegree := by
    unfold RatFunc.intDegree at hdeg; omega
  have hdvd : (algebraMap ℚ[X] ℚ⟮X⟯ (X ^ 3 * Rnum N) /
      algebraMap ℚ[X] ℚ⟮X⟯ (Rden N)).denom ∣ Rden N := RatFunc.denom_div_dvd _ _
  have hsplit := Polynomial.splits_iff_card_roots.mp ((Rden_splits N).of_dvd hden0 hdvd)
  rw [Lfun_Z2_eq_residue _ _ hproper hsplit 1 (cubic_DegLE N)]
  norm_num

end ZetasIrr.CMF
