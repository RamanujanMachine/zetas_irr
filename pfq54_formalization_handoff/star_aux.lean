import pf_aux
import pairing_identity

open Polynomial Finset
open scoped RatFunc Matrix

noncomputable section

namespace Pfq54.ST

open Pfq54 Pfq54.RA Pfq54.PF ZetasIrr ZetasIrr.CMF

/-! ### The parameter point of `F_n` and its companion relation -/

def wpt (n : ℕ) : Pt :=
  ⟨![-11 * (n : ℤ), -12 * (n : ℤ), 1 + 17 * (n : ℤ), 1 + 16 * (n : ℤ), -10 * (n : ℤ)],
   ![0, -(n : ℤ), -2 * (n : ℤ), (n : ℤ), 2 * (n : ℤ)]⟩

theorem wpt_a (n : ℕ) : (wpt n).a =
    ![-11 * (n : ℤ), -12 * (n : ℤ), 1 + 17 * (n : ℤ), 1 + 16 * (n : ℤ), -10 * (n : ℤ)] := rfl
theorem wpt_b (n : ℕ) : (wpt n).b = ![0, -(n : ℤ), -2 * (n : ℤ), (n : ℤ), 2 * (n : ℤ)] := rfl

theorem Zk_wpt (n : ℕ) : Zk (wpt n) = nR n := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Zk, wpt_a, wpt_b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Multiset.count_add, count_ival, nR, count_Icc]
  split_ifs <;> omega

theorem Pk_wpt (n : ℕ) : Pk (wpt n) = dR n := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Pk, wpt_a, wpt_b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Multiset.count_add, count_ival, dR, count_Icc]
  split_ifs <;> omega

theorem wpt_ker (n : ℕ) : (wpt n).ker = Fn n := by
  rw [ker_eq_lin, Zk_wpt, Pk_wpt, Fn]

theorem VC_wpt (n ord : ℕ) (hord : ord ≤ 3) : VC ord (2 * n) (wpt n) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [Pk_wpt] at hq
    simp only [dR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hq
    omega
  · rw [Pk_wpt, Zk_wpt, Multiset.count_add, bro, wpt_b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, dR, nR,
      Multiset.count_add, count_Icc]
    split_ifs <;> omega

theorem companion_L (n : ℕ) :
    ∑ k : Fin 5, (wpt n).dc k • mom Lfun (2 * n) (Fn n) k = 0 := by
  have := companion_of_VC isMom_Lfun (2 * n) (wpt n) (VC_wpt n 2 (by norm_num))
  rwa [wpt_ker] at this

theorem companion_M (n : ℕ) :
    ∑ k : Fin 5, (wpt n).dc k • mom Mfun (2 * n) (Fn n) k = 0 := by
  have := companion_of_VC isMom_Mfun (2 * n) (wpt n) (VC_wpt n 3 le_rfl)
  rwa [wpt_ker] at this

theorem dc4_wpt (n : ℕ) : (wpt n).dc 4 = 3 := by
  rw [Pt.dc, dc_four, wpt_a, wpt_b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-! ### The dual kernel of `p_n` is `(t - 10n - 1) F_n(t)` -/

theorem Zk_dual (n : ℕ) : Zk (pN n).dual = ((10 * n + 1 : ℤ) ::ₘ nR n) := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Zk, Pt.dual_a, Pt.dual_b, pN_a, pN_b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Multiset.count_add, count_ival, nR, count_Icc, Multiset.count_cons]
  split_ifs <;> omega

theorem Pk_dual (n : ℕ) : Pk (pN n).dual = dR n := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Pk, Pt.dual_a, Pt.dual_b, pN_a, pN_b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Multiset.count_add, count_ival, dR, count_Icc]
  split_ifs <;> omega

theorem dker_eq (n : ℕ) :
    (pN n).dual.ker = (RatFunc.X - RatFunc.C ((10 * n + 1 : ℤ) : ℚ)) * Fn n := by
  rw [ker_eq_lin, Zk_dual, Pk_dual, lin_cons_left, Fn]

/-! ### Monomial terms and the cutoff move -/

def mt (n r : ℕ) : ℚ⟮X⟯ := (-RatFunc.X) ^ r * (pN n).dual.ker

theorem mt_eq_lin (n r : ℕ) : mt n r = RatFunc.C ((-1 : ℚ) ^ r) *
    lin (Multiset.replicate r 0 + ((10 * n + 1 : ℤ) ::ₘ nR n)) (dR n) := by
  rw [mt, dker_eq, Fn, ← lin_cons_left, negX_pow_mul_lin]

theorem Lfun_cut_many (Z P : Multiset ℤ) (K : ℤ) (m : ℕ) (hP : ∀ p ∈ P, p ≤ K)
    (hZ : ∀ k : ℤ, K ≤ k → k < K + m → 2 ≤ Z.count (k + 1)) :
    Lfun (K + m) (lin Z P) = Lfun K (lin Z P) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, Lfun_cut (K + m) Z P
      (fun p hp => (hP p hp).trans (by omega)) (hZ (K + m) (by omega) (by push_cast; omega)),
      ih (fun k hk1 hk2 => hZ k hk1 (by push_cast at hk2 ⊢; omega))]

theorem Lfun_mt_cut (n r : ℕ) : Lfun (2 * n) (mt n r) = Lfun n (mt n r) := by
  rw [mt_eq_lin, Aux.Lfun_C_mul, Aux.Lfun_C_mul]
  congr 1
  rw [show (2 * n : ℤ) = (n : ℤ) + (n : ℕ) by push_cast; ring]
  refine Lfun_cut_many _ _ _ _ (fun p hp => ?_) (fun k hk1 hk2 => ?_)
  · simp only [dR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hp
    omega
  · simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_cons, nR, count_Icc]
    split_ifs <;> omega

/-! ### The weighted readouts -/

def hv (n : ℕ) : Fin 3 → ℚ := ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]

def Del (n : ℕ) : ℚ := ∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1)

theorem Del_pos (n : ℕ) : 0 < Del n := by unfold Del; positivity

def Jq (n : ℕ) (j : Fin 3) (r : Fin 4) : ℚ := (Jmat n (Fin.castSucc j) r : ℚ)

def Wj (n : ℕ) (j : Fin 3) : ℚ⟮X⟯ := ∑ r : Fin 4, RatFunc.C (Jq n j r) * mt n r

def W (n : ℕ) : ℚ⟮X⟯ := ∑ j : Fin 3, RatFunc.C (hv n j) * Wj n j

theorem Qmul_eq' (n : ℕ) (j : Fin 3) :
    algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly n j) * RkerStar n =
      RatFunc.laurent ((12 * (n : ℤ) + 1 : ℤ) : ℚ) (Wj n j) := by
  rw [Qmul_eq, Wj]
  rfl

theorem identity_L (n : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ n * 3) • Lfun n (Wj n j) = q n j • Zsym 3 - p3 n j • Zsym 0 := by
  have h := dual_first_identity' n j
  rwa [Qmul_eq', Aux.Lfun_laurent, show (-11 * (n : ℤ) - 1 + (12 * n + 1)) = n by ring] at h

theorem identity_M (n : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ n) • Mfun (2 * n) (Wj n j) = q n j • Zsym 4 - p4 n j • Zsym 0 := by
  have h := BP.pairing_identity n j
  rwa [Qmul_eq', Aux.Mfun_laurent, show (-10 * (n : ℤ) - 1 + (12 * n + 1)) = 2 * n by ring] at h

theorem Lfun_Wj_cut (n : ℕ) (j : Fin 3) : Lfun (2 * n) (Wj n j) = Lfun n (Wj n j) := by
  rw [Wj, isMom_Lfun.sum, isMom_Lfun.sum]
  exact Finset.sum_congr rfl fun r _ => by rw [Lfun_mt_cut]

theorem weighted_L (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 3 - p3 n j • Zsym 0) =
      ((-1 : ℚ) ^ n * 3) • Lfun (2 * n) (W n) := by
  rw [W, isMom_Lfun.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Lfun_Wj_cut, ← identity_L, smul_comm]

theorem weighted_M (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 4 - p4 n j • Zsym 0) =
      ((-1 : ℚ) ^ n) • Mfun (2 * n) (W n) := by
  rw [W, isMom_Mfun.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← identity_M, smul_comm]

/-! ### Reduction of the weight modulo the companion relation -/

theorem Phi_mt {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (n r : ℕ) :
    Φ (2 * n) (mt n r) =
      -mom Φ (2 * n) (Fn n) (r + 1) - (10 * (n : ℚ) + 1) • mom Φ (2 * n) (Fn n) r := by
  have h : mt n r = RatFunc.C (-1) * ((-RatFunc.X) ^ (r + 1) * Fn n) +
      RatFunc.C (-(10 * (n : ℚ) + 1)) * ((-RatFunc.X) ^ r * Fn n) := by
    rw [mt, dker_eq]
    push_cast
    simp only [map_neg, map_one, map_add, map_mul, map_natCast]
    ring
  rw [h, hΦ.add, hΦ.C_mul, hΦ.C_mul, neg_one_smul, neg_smul, sub_eq_add_neg]
  rfl

theorem Phi_W {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (n : ℕ) :
    Φ (2 * n) (W n) = ∑ j : Fin 3, hv n j • ∑ r : Fin 4, Jq n j r • Φ (2 * n) (mt n r) := by
  rw [W, hΦ.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Wj, hΦ.sum]

theorem mom_zero_eq {Φ : ℤ → ℚ⟮X⟯ → FormalZ} (K : ℤ) (f : ℚ⟮X⟯) : Φ K f = mom Φ K f 0 := by
  rw [mom, pow_zero, one_mul]

theorem W_reduce {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (n : ℕ)
    (hcomp : ∑ k : Fin 5, (wpt n).dc k • mom Φ (2 * n) (Fn n) k = 0) :
    Φ (2 * n) (W n) = Del n • Φ (2 * n) (Fn n) := by
  set m := mom Φ (2 * n) (Fn n) with hm
  rw [Fin.sum_univ_five, dc4_wpt] at hcomp
  have h4 : m 4 = (-1 / 3 : ℚ) • ((wpt n).dc 0 • m 0 + (wpt n).dc 1 • m 1 +
      (wpt n).dc 2 • m 2 + (wpt n).dc 3 • m 3) := by
    have h3 : (3 : ℚ) • m 4 = -((wpt n).dc 0 • m 0 + (wpt n).dc 1 • m 1 +
        (wpt n).dc 2 • m 2 + (wpt n).dc 3 • m 3) := by
      rw [eq_neg_iff_add_eq_zero, ← hcomp]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, fv3, fv4]
      abel
    rw [neg_div, neg_smul, ← smul_neg, ← h3, smul_smul]
    norm_num
  rw [Phi_W hΦ, mom_zero_eq (Φ := Φ) (2 * n) (Fn n), ← hm]
  simp only [Phi_mt hΦ, ← hm, Fin.sum_univ_three, Fin.sum_univ_four, Fin.val_zero, Fin.val_one,
    Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl, zero_add]
  rw [h4]
  simp only [Jq, Jmat, hv, Pt.dc, dc, e1, e2, e3, e4, e5, al, bq, wpt_a, wpt_b, Del,
    Aux.prod_Icc_8_12, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, Fin.castSucc_zero, Fin.castSucc_one,
    show Fin.castSucc (2 : Fin 3) = (2 : Fin 4) from rfl, Matrix.cons_val']
  push_cast
  module

/-! ### Extracting the coefficients -/

theorem sum_apply (c u v : Fin 3 → ℚ) (a k : ℕ) :
    (∑ j : Fin 3, c j • (u j • Zsym a - v j • Zsym 0)) k =
      ∑ j : Fin 3, c j * (u j * (if a = k then 1 else 0) - v j * (if 0 = k then 1 else 0)) := by
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finsupp.smul_apply, Finsupp.sub_apply, Zsym, Finsupp.single_apply, smul_eq_mul]

theorem Lfun_W (n : ℕ) : Lfun (2 * n) (W n) = Del n • Lfun (2 * n) (Fn n) :=
  W_reduce isMom_Lfun n (companion_L n)

theorem Mfun_W (n : ℕ) : Mfun (2 * n) (W n) = Del n • Mfun (2 * n) (Fn n) :=
  W_reduce isMom_Mfun n (companion_M n)

theorem sum_q_hv (n : ℕ) : ∑ j : Fin 3, q n j * hv n j = (-1) ^ n * 6 * Del n * Qa n := by
  have h := congrFun (congrArg (⇑) (weighted_L n)) 3
  rw [sum_apply, Lfun_W, Finsupp.smul_apply, Finsupp.smul_apply, Lfun_Fn_three] at h
  simp only [ite_true, ite_false, mul_one, mul_zero, sub_zero, smul_eq_mul,
    show (0 : ℕ) ≠ 3 by decide, show (3 : ℕ) = 3 from rfl] at h
  rw [show ∑ j : Fin 3, q n j * hv n j = ∑ j : Fin 3, hv n j * q n j from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, h]
  ring

theorem sum_p3_hv (n : ℕ) : ∑ j : Fin 3, p3 n j * hv n j = (-1) ^ n * 6 * Del n * P3a n := by
  have h := congrFun (congrArg (⇑) (weighted_L n)) 0
  rw [sum_apply, Lfun_W, Finsupp.smul_apply, Finsupp.smul_apply, Lfun_Fn_zero] at h
  simp only [ite_true, ite_false, mul_one, mul_zero, zero_sub, smul_eq_mul,
    show (3 : ℕ) ≠ 0 by decide, mul_neg, Finset.sum_neg_distrib] at h
  rw [show ∑ j : Fin 3, p3 n j * hv n j = ∑ j : Fin 3, hv n j * p3 n j from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, ← neg_inj, h]
  ring

theorem sum_p4_hv (n : ℕ) : ∑ j : Fin 3, p4 n j * hv n j = (-1) ^ n * 6 * Del n * P4a n := by
  have h := congrFun (congrArg (⇑) (weighted_M n)) 0
  rw [sum_apply, Mfun_W, Finsupp.smul_apply, Finsupp.smul_apply, Mfun_Fn_zero] at h
  simp only [ite_true, ite_false, mul_one, mul_zero, zero_sub, smul_eq_mul,
    show (4 : ℕ) ≠ 0 by decide, mul_neg, Finset.sum_neg_distrib] at h
  rw [show ∑ j : Fin 3, p4 n j * hv n j = ∑ j : Fin 3, hv n j * p4 n j from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, ← neg_inj, h]
  ring

/-! ### The scalar `∏ R(m) = C_n / E_n` -/

def Rsc (n : ℕ) : ℚ :=
  1125 * ((n : ℚ) + 1) ^ 3 * (2 * n + 1) * (3 * n + 1) * (3 * n + 2) *
      (∏ j ∈ Icc (1 : ℕ) 4, (5 * (n : ℚ) + j)) *
      (∏ j ∈ ({1, 2, 4, 7, 8, 11, 13, 14} : Finset ℕ), (15 * (n : ℚ) + j)) /
    (416 * (6 * (n : ℚ) + 1) * (6 * n + 5) *
      (∏ j ∈ ({1, 5, 7, 11} : Finset ℕ), (12 * (n : ℚ) + j)) *
      (∏ j ∈ Icc (1 : ℕ) 12, (13 * (n : ℚ) + j)))

def kinv (n : ℕ) : ℚ :=
  ((n.factorial * (2 * n).factorial * (3 * n).factorial * (4 * n).factorial *
      (15 * n).factorial : ℕ) : ℚ) / (((12 * n).factorial * (13 * n).factorial : ℕ) : ℚ)

theorem Cn_div_E (n : ℕ) : Cn n / (E n : ℚ) = kinv n := by
  have hc : ∀ a b : ℕ, b ≤ a →
      ((a.choose b : ℕ) : ℚ) = a.factorial / (b.factorial * (a - b).factorial) :=
    fun a b h => Nat.cast_choose ℚ h
  unfold Cn E kinv
  push_cast
  rw [hc _ _ (by omega : 10 * n ≤ 12 * n), hc _ _ (by omega : 10 * n ≤ 13 * n),
    hc _ _ (by omega : 10 * n ≤ 14 * n), hc _ _ (by omega : n ≤ 15 * n),
    show 12 * n - 10 * n = 2 * n by omega, show 13 * n - 10 * n = 3 * n by omega,
    show 14 * n - 10 * n = 4 * n by omega, show 15 * n - n = 14 * n by omega]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((3 * n).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((4 * n).factorial : ℚ) ≠ 0 := by positivity
  have h10 : ((10 * n).factorial : ℚ) ≠ 0 := by positivity
  have h12 : ((12 * n).factorial : ℚ) ≠ 0 := by positivity
  have h13 : ((13 * n).factorial : ℚ) ≠ 0 := by positivity
  have h14 : ((14 * n).factorial : ℚ) ≠ 0 := by positivity
  have h15 : ((15 * n).factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem fact_add (m k : ℕ) :
    ((m + k).factorial : ℚ) = m.factorial * ∏ i ∈ range k, ((m : ℚ) + i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring

theorem Icc_1_4 : Finset.Icc (1 : ℕ) 4 = {1, 2, 3, 4} := by decide
theorem Icc_1_12 : Finset.Icc (1 : ℕ) 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide

theorem kinv_succ (n : ℕ) : kinv (n + 1) = Rsc n * kinv n := by
  have e1 : 2 * (n + 1) = 2 * n + 2 := by ring
  have e2 : 3 * (n + 1) = 3 * n + 3 := by ring
  have e3 : 4 * (n + 1) = 4 * n + 4 := by ring
  have e4 : 15 * (n + 1) = 15 * n + 15 := by ring
  have e5 : 12 * (n + 1) = 12 * n + 12 := by ring
  have e6 : 13 * (n + 1) = 13 * n + 13 := by ring
  unfold kinv Rsc
  rw [e1, e2, e3, e4, e5, e6]
  push_cast
  rw [fact_add n 1, fact_add (2 * n) 2, fact_add (3 * n) 3, fact_add (4 * n) 4,
    fact_add (15 * n) 15, fact_add (12 * n) 12, fact_add (13 * n) 13, Icc_1_4, Icc_1_12]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.prod_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.prod_singleton]
  norm_num
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((3 * n).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((4 * n).factorial : ℚ) ≠ 0 := by positivity
  have h12 : ((12 * n).factorial : ℚ) ≠ 0 := by positivity
  have h13 : ((13 * n).factorial : ℚ) ≠ 0 := by positivity
  have h15 : ((15 * n).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem kinv_zero : kinv 0 = 1 := by
  simp [kinv]

theorem prod_Rsc (n : ℕ) : ∏ m ∈ range n, Rsc m = kinv n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, kinv_zero]
  | succ n ih => rw [Finset.prod_range_succ, ih, kinv_succ, mul_comm]

theorem prod_Rsc_eq (n : ℕ) : ∏ m ∈ range n, Rsc m = Cn n / (E n : ℚ) := by
  rw [prod_Rsc, Cn_div_E]

/-! ### The identity (★) -/

def IG2 (A B : ℤ) : Matrix (Fin 2) (Fin 3) ℚ := !![2 * B, -3 * A - 2 * B, 3 * A; 0, 0, 6]

theorem IG2_T (A B : ℤ) (n : ℕ) :
    IG2 A B * T n = Matrix.of ![fun j => A * p3 n j + B * p4 n j, fun j => q n j] := by
  ext i j
  fin_cases i <;>
    simp [IG2, Matrix.mul_apply, Fin.sum_univ_three, p3, p4, q, Rmat, U34] <;> ring

theorem E_pos (n : ℕ) : (0 : ℚ) < E n := by
  unfold E
  exact Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
    (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega)))

theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; norm_num

theorem star (A B : ℤ) (n : ℕ) :
    (12 / (E n : ℚ)) • ![(A : ℚ) * S3 n + B * S4 n, S0 n] =
      (2 * ∏ m ∈ range n, Rsc m) • (IG2 A B *ᵥ (T n *ᵥ ((Del n)⁻¹ • hv n))) := by
  rw [prod_Rsc_eq, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, IG2_T,
    smul_smul]
  have hD := (Del_pos n).ne'
  have hC := Cn_ne_zero n
  have hE := (E_pos n).ne'
  have hs2 : (-1 : ℚ) ^ (n * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  have hq := sum_q_hv n
  have hp3 := sum_p3_hv n
  have hp4 := sum_p4_hv n
  unfold Qa at hq
  unfold P3a at hp3
  unfold P4a at hp4
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons]
    rw [show ∑ j : Fin 3, (A * p3 n j + B * p4 n j) * hv n j =
      A * ∑ j : Fin 3, p3 n j * hv n j + B * ∑ j : Fin 3, p4 n j * hv n j by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring, hp3, hp4]
    field_simp
    linear_combination (-(12 * ((A : ℚ) * S3 n + B * S4 n))) * hs2
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    rw [hq]
    field_simp
    linear_combination (-(12 * S0 n)) * hs2

end Pfq54.ST
