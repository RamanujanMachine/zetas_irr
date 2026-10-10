/-
# Chamber certificate, part 2: `E₃₄(N,p)` through the step-function expressions

For a prime `p` with `p² > 30N + 10` every factorial valuation `f_p(m)` occurring in `E₃₄(N,p)` is
`⌊m/p⌋` and every `ℓ_p(m)` is `[m ≥ p]`.  The five minimised/maximised functions of `k`
(`A_p, B_p, C_p` and the two dual losses) are, region by region in `k`, expressions of
`Chamber_dsl`.  With the lower bounds `boundE`/`boundP` this gives
`E₃₄(N,p) ≤ certI v` (for `N < p`) and `E₃₄(N,p) ≤ certP w` (for `N > p`, `w` the data of the
fractional part), where `v c = ⌊cN/p⌋`.
-/
import Chamber_dsl
import E34_le

namespace ZetasIrr.CH
open ZetasIrr

/-! ### Floors and indicators -/

theorem fp_eq_div {p : ℕ} (hp : p.Prime) (m : ℤ) (h0 : 0 ≤ m) (hm : m < (p : ℤ) ^ 2) :
    fp p m = m / p := by
  by_cases hlt : m < p
  · rw [Aux.fp_eq_zero_of_lt hp hlt, Int.ediv_eq_zero_of_lt h0 hlt]
  · have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg h0
    have h1 : p ^ 1 ≤ m.toNat := by rw [pow_one]; omega
    have h2 : m.toNat < p ^ (1 + 1) := by
      have : (m.toNat : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by rw [hmn]; exact_mod_cast hm
      exact_mod_cast this
    rw [fp_eq_sum_levels hp m.toNat m (by omega), Nat.log_eq_of_pow_le_of_lt_pow h1 h2,
      show Finset.Ico 1 (1 + 1) = {1} by decide, Finset.sum_singleton, pow_one,
      Int.natCast_ediv, hmn]

theorem ellp_eq_ind {p : ℕ} (hp : p.Prime) (m : ℤ) (hm : m < (p : ℤ) ^ 2) :
    ellp p m = ind p m := by
  unfold ind
  split_ifs with h
  · rw [Aux.ellp_eq_log hp]
    have h1 : p ^ 1 ≤ m.toNat := by rw [pow_one]; omega
    have h2 : m.toNat < p ^ (1 + 1) := by
      have : (m.toNat : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega)]; exact_mod_cast hm
      exact_mod_cast this
    rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]; rfl
  · exact Aux.ellp_eq_zero_of_lt hp (by omega)

theorem ind_max (p a b : ℤ) : ind p (max a b) = max (ind p a) (ind p b) := by
  unfold ind
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right]
    split_ifs <;> omega
  · rw [max_eq_left h, max_eq_left]
    split_ifs <;> omega

theorem Gp_eq {p : ℕ} (hp : p.Prime) (k a b : ℤ) (hab : a ≤ b) (h1 : b - k < (p : ℤ) ^ 2)
    (h2 : k - a < (p : ℤ) ^ 2) :
    Gp p k a b = (k - a) / p - (k - b - 1) / p - (if a ≤ k ∧ k ≤ b then 1 else 0) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  by_cases hk : k < a
  · rw [Gp_left p k a b hk, fp_eq_div hp _ (by omega) h1, fp_eq_div hp _ (by omega) (by omega),
      ite_eq_right (by omega), show b - k = -(k - b - 1) - 1 by ring,
      show a - k - 1 = -(k - a) - 1 by ring, ediv_neg_pred _ _ hp0, ediv_neg_pred _ _ hp0]
    ring
  · by_cases hkb : k ≤ b
    · rw [Gp_mid p k a b (by omega) hkb, fp_eq_div hp _ (by omega) h2,
        fp_eq_div hp _ (by omega) h1, ite_eq_left ⟨by omega, hkb⟩,
        show b - k = -(k - b - 1) - 1 by ring, ediv_neg_pred _ _ hp0]
      ring
    · rw [Gp_right p k a b hk (by omega), fp_eq_div hp _ (by omega) h2,
        fp_eq_div hp _ (by omega) (by omega), ite_eq_right (by omega), sub_zero]

/-! ### The multiplicities -/

theorem mult_Io_eq (N : ℕ) (k : ℤ) : mult (Io N) k =
    (if 0 ≤ k ∧ k ≤ 10 * N + 1 then 1 else 0) + (if N ≤ k ∧ k ≤ 11 * N then 1 else 0) +
      (if 2 * N ≤ k ∧ k ≤ 12 * N then 1 else 0) := by
  unfold mult Io
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  push_cast
  omega

theorem mult_Id_eq (N : ℕ) (k : ℤ) : mult (Id N) k =
    (if 13 * N + 1 ≤ k ∧ k ≤ 28 * N + 1 then 1 else 0) +
      (if 14 * N + 1 ≤ k ∧ k ≤ 29 * N + 1 then 1 else 0) := by
  unfold mult Id
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  push_cast
  omega

/-! ### The expressions -/

def VoE : List Term :=
  [.fl 1 17 0, .fl 1 16 0, .fl (-1) 2 0, .fl (-1) 1 0, .fl (-1) 0 0, .fl 1 (-10) (-2),
    .fl (-1) (-1) 0, .fl 1 (-11) (-1), .fl (-1) (-2) 0, .fl 1 (-12) (-1)]

def VdE : List Term :=
  [.fl 1 (-1) (-1), .fl 1 0 (-1), .fl 1 (-2) 0, .fl (-1) (-12) (-1), .fl (-1) (-11) (-1),
    .fl (-1) (-10) (-1), .fl (-1) (-13) (-1), .fl 1 (-28) (-2), .fl (-1) (-14) (-1),
    .fl 1 (-29) (-2)]

def AX : List Term := [.one 3]
def BX (m : ℤ) : List Term := [.one m, .up (-(m - 2)) 17 0]
def CX (m : ℤ) : List Term := [.one m, .up (-(m - 1)) 17 0, .up (-2) 2 0]
def DX (m : ℤ) : List Term := [.one m, .mx (-(m - 1)) 0 (-1) 29 1, .up (-2) (-11) (-1)]
def D4X (m : ℤ) : List Term := [.one m, .mx (-(m - 1)) 0 (-1) 29 1, .up (-3) (-10) (-1)]
def BXP : List Term := [.one 2]
def CXP : List Term := [.one (-1)]
def DXP : List Term := [.one (-1)]
def D4XP : List Term := [.one (-2)]
def AE : List Term := VoE ++ AX
def BE (m : ℤ) : List Term := VoE ++ BX m
def CE (m : ℤ) : List Term := VoE ++ CX m
def DE (m : ℤ) : List Term := VdE ++ DX m
def D4E (m : ℤ) : List Term := VdE ++ D4X m
def BEP : List Term := VoE ++ BXP
def CEP : List Term := VoE ++ CXP
def DEP : List Term := VdE ++ DXP
def D4EP : List Term := VdE ++ D4XP

theorem evalE_append (N p k : ℤ) (E F : List Term) :
    evalE N p k (E ++ F) = evalE N p k E + evalE N p k F := by
  unfold evalE; rw [List.map_append, List.sum_append]

theorem ediv_congr {a b : ℤ} (p : ℤ) (h : a = b) : a / p = b / p := by rw [h]

/-- `V_o(k) = evalE VoE + m_o(k)` on `0 ≤ k ≤ 12N`. -/
theorem Vo_eq {N p : ℕ} (hp : p.Prime) (hsq : 30 * N + 10 < p ^ 2) (k : ℤ) (hk0 : 0 ≤ k)
    (hk : k ≤ 12 * N) : Vo N p k = evalE N p k VoE + mult (Io N) k := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  rw [mult_Io_eq]
  unfold Vo Io
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [fp_eq_div hp _ (by omega) (by omega), fp_eq_div hp _ (by omega) (by omega),
    fp_eq_div hp _ (by omega) (by omega), fp_eq_div hp _ (by omega) (by omega),
    Gp_eq hp _ _ _ (by omega) (by omega) (by omega), Gp_eq hp _ _ _ (by omega) (by omega) (by omega),
    Gp_eq hp _ _ _ (by omega) (by omega) (by omega)]
  unfold evalE VoE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  rw [ediv_congr (p : ℤ) (show k + 17 * (N : ℤ) + 0 = k + 17 * N by ring),
    ediv_congr (p : ℤ) (show k + 16 * (N : ℤ) + 0 = k + 16 * N by ring),
    ediv_congr (p : ℤ) (show k + 2 * (N : ℤ) + 0 = k + 2 * N by ring),
    ediv_congr (p : ℤ) (show k + 1 * (N : ℤ) + 0 = k + N by ring),
    ediv_congr (p : ℤ) (show k + 0 * (N : ℤ) + 0 = k - 0 by ring),
    ediv_congr (p : ℤ) (show k + -10 * (N : ℤ) + -2 = k - (10 * N + 1) - 1 by ring),
    ediv_congr (p : ℤ) (show k + -1 * (N : ℤ) + 0 = k - N by ring),
    ediv_congr (p : ℤ) (show k + -11 * (N : ℤ) + -1 = k - 11 * N - 1 by ring),
    ediv_congr (p : ℤ) (show k + -2 * (N : ℤ) + 0 = k - 2 * N by ring),
    ediv_congr (p : ℤ) (show k + -12 * (N : ℤ) + -1 = k - 12 * N - 1 by ring)]
  omega

/-- `V_d(k) = evalE VdE + m_d(k)` on `13N + 1 ≤ k ≤ 29N + 1`. -/
theorem Vd_eq {N p : ℕ} (hp : p.Prime) (hsq : 30 * N + 10 < p ^ 2) (k : ℤ)
    (hk0 : 13 * N + 1 ≤ k) (hk : k ≤ 29 * N + 1) : Vd N p k = evalE N p k VdE + mult (Id N) k := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  rw [mult_Id_eq]
  unfold Vd Id
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [fp_eq_div hp _ (by omega) (by omega), fp_eq_div hp _ (by omega) (by omega),
    fp_eq_div hp _ (by omega) (by omega), fp_eq_div hp _ (by omega) (by omega),
    fp_eq_div hp _ (by omega) (by omega), fp_eq_div hp _ (by omega) (by omega),
    Gp_eq hp _ _ _ (by omega) (by omega) (by omega), Gp_eq hp _ _ _ (by omega) (by omega) (by omega)]
  unfold evalE VdE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  rw [ediv_congr (p : ℤ) (show k + -1 * (N : ℤ) + -1 = k - N - 1 by ring),
    ediv_congr (p : ℤ) (show k + 0 * (N : ℤ) + -1 = k - 1 by ring),
    ediv_congr (p : ℤ) (show k + -2 * (N : ℤ) + 0 = k - 2 * N by ring),
    ediv_congr (p : ℤ) (show k + -12 * (N : ℤ) + -1 = k - 12 * N - 1 by ring),
    ediv_congr (p : ℤ) (show k + -11 * (N : ℤ) + -1 = k - 11 * N - 1 by ring),
    ediv_congr (p : ℤ) (show k + -10 * (N : ℤ) + -1 = k - 10 * N - 1 by ring),
    ediv_congr (p : ℤ) (show k + -13 * (N : ℤ) + -1 = k - (13 * N + 1) by ring),
    ediv_congr (p : ℤ) (show k + -28 * (N : ℤ) + -2 = k - (28 * N + 1) - 1 by ring),
    ediv_congr (p : ℤ) (show k + -14 * (N : ℤ) + -1 = k - (14 * N + 1) by ring),
    ediv_congr (p : ℤ) (show k + -29 * (N : ℤ) + -2 = k - (29 * N + 1) - 1 by ring)]
  omega

/-- The data `v c = ⌊cN/p⌋`. -/
def vpFc (v : ℤ → ℤ) : ℤ :=
  (v 16 + v 17 + v 18 + v 15 + v 14 + v 17 + v 18 + v 19 + v 16 + v 15) -
    (v 11 + v 10 + v 9 + v 12 + v 13 + v 12 + v 11 + v 10 + v 13 + v 14) -
    (v 10 + v 9 + v 8 + v 11 + v 12)

theorem vpF_eq {N p : ℕ} (hp : p.Prime) (hp10 : 10 < p) (hsq : 30 * N + 10 < p ^ 2)
    (hNB : NB N p) {v : ℤ → ℤ} (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) :
    vpF N p = vpFc v := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have key : ∀ r : ℕ, 1 ≤ r → r ≤ 19 →
      fp p ((r : ℤ) * N) = v r ∧ fp p ((r : ℤ) * N + 1) = v r := by
    intro r hr1 hr
    have hr' : (r : ℤ) ≤ 19 := by exact_mod_cast hr
    have hr1' : (1 : ℤ) ≤ r := by exact_mod_cast hr1
    have hc : |(r : ℤ)| ≤ 29 := by rw [abs_of_nonneg (by omega)]; omega
    constructor
    · rw [fp_eq_div hp _ (by positivity) (by nlinarith), hv r hc]
    · rw [fp_eq_div hp _ (by positivity) (by nlinarith), sh_true hp10' hNB hv r 1 hc (by norm_num),
        sh, ite_eq_right (by omega)]
  have k8 := key 8 (by norm_num) (by norm_num)
  have k9 := key 9 (by norm_num) (by norm_num)
  have k10 := key 10 (by norm_num) (by norm_num)
  have k11 := key 11 (by norm_num) (by norm_num)
  have k12 := key 12 (by norm_num) (by norm_num)
  have k13 := key 13 (by norm_num) (by norm_num)
  have k14 := key 14 (by norm_num) (by norm_num)
  have k15 := key 15 (by norm_num) (by norm_num)
  have k16 := key 16 (by norm_num) (by norm_num)
  have k17 := key 17 (by norm_num) (by norm_num)
  have k18 := key 18 (by norm_num) (by norm_num)
  have k19 := key 19 (by norm_num) (by norm_num)
  try push_cast at k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19
  unfold vpF listA listB listE vpFc
  simp only [bind, List.flatMap_cons, List.flatMap_nil, pure, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.nil_append, List.cons_append]
  try push_cast
  rw [k16.1, k17.1, k18.1, k15.1, k14.1, k19.1, k11.1, k10.1, k9.1, k12.1, k13.1, k10.2, k9.2,
    k8.2, k11.2, k12.2]
  omega

/-! ### The five objectives, region by region -/

section Objectives
variable {N p : ℕ} (hp : p.Prime) (hp10 : 10 < p) (hN : 1 ≤ N) (hsq : 30 * N + 10 < p ^ 2)
include hp hN hsq

theorem Aobj_eq (k : ℤ) (h1 : 2 * N ≤ k) (h2 : k ≤ 10 * N + 1) :
    Vo N p k = evalE N p k AE := by
  rw [Vo_eq hp hsq k (by omega) (by omega), mult_Io_eq, AE, AX, evalE_append,
    ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩,
    ite_eq_left ⟨by omega, by omega⟩]
  rfl

/-- The `C_p` objective. -/
def Cobj (N p : ℕ) (k : ℤ) : ℤ :=
  Vo N p k - (mult (Io N) k - 1) * ellp p (k + 17 * N) - 2 * ellp p (k + 2 * N)

theorem Cobj_eq (m : ℤ) (k : ℤ) (hk0 : 0 ≤ k) (hk : k ≤ 12 * N) (hm : mult (Io N) k = m) :
    Cobj N p k = evalE N p k (CE m) := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  unfold Cobj
  rw [Vo_eq hp hsq k hk0 hk, hm, ellp_eq_ind hp _ (by omega), ellp_eq_ind hp _ (by omega), CE, CX,
    evalE_append]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval, add_zero]
  ring

/-- The `B_p` objective. -/
def Bobj (N p : ℕ) (k : ℤ) : ℤ := Vo N p k - (mult (Io N) k - 2) * ellp p (k + 17 * N)

theorem Bobj_eq (m : ℤ) (k : ℤ) (hk0 : 0 ≤ k) (hk : k ≤ 12 * N) (hm : mult (Io N) k = m) :
    Bobj N p k = evalE N p k (BE m) := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  unfold Bobj
  rw [Vo_eq hp hsq k hk0 hk, hm, ellp_eq_ind hp _ (by omega), BE, BX, evalE_append]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval, add_zero]
  ring

/-- The `E_d` objective (the function maximised in `Ed`). -/
def Dobj (N p : ℕ) (k : ℤ) : ℤ :=
  (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) - Vd N p k

theorem Dobj_eq (m : ℤ) (k : ℤ) (hk0 : 13 * N + 1 ≤ k) (hk : k ≤ 29 * N + 1)
    (hm : mult (Id N) k = m) : Dobj N p k = -evalE N p k (DE m) := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  unfold Dobj Ld
  rw [Vd_eq hp hsq k hk0 hk, hm, ellp_eq_ind hp _ (by omega), ellp_eq_ind hp _ (by omega),
    ind_max, DE, DX, evalE_append]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  rw [show k + 0 * (N : ℤ) + -1 = k - 1 by ring, show k + -11 * (N : ℤ) + -1 = k - 11 * N - 1 by ring]
  ring

/-- The `E_{d4}` objective. -/
def D4obj (N p : ℕ) (k : ℤ) : ℤ :=
  (mult (Id N) k - 1) * ellp p (Ld N k) + 3 * ellp p (k - 10 * N - 1) - Vd N p k

theorem D4obj_eq (m : ℤ) (k : ℤ) (hk0 : 13 * N + 1 ≤ k) (hk : k ≤ 29 * N + 1)
    (hm : mult (Id N) k = m) : D4obj N p k = -evalE N p k (D4E m) := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  unfold D4obj Ld
  rw [Vd_eq hp hsq k hk0 hk, hm, ellp_eq_ind hp _ (by omega), ellp_eq_ind hp _ (by omega),
    ind_max, D4E, D4X, evalE_append]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  rw [show k + 0 * (N : ℤ) + -1 = k - 1 by ring, show k + -10 * (N : ℤ) + -1 = k - 10 * N - 1 by ring]
  ring

/-! The periodic regime `N > p`: all loss indicators equal `1`. -/

theorem Cobj_eqP (hpN : p < N) (k : ℤ) (hk0 : 0 ≤ k) (hk : k ≤ 12 * N) :
    Cobj N p k = evalE N p k CEP := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  have hN' : (p : ℤ) < N := by exact_mod_cast hpN
  unfold Cobj
  rw [Vo_eq hp hsq k hk0 hk, ellp_eq_ind hp _ (by omega), ellp_eq_ind hp _ (by omega), CEP, CXP,
    evalE_append]
  unfold ind
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  ring

theorem Bobj_eqP (hpN : p < N) (k : ℤ) (hk0 : 0 ≤ k) (hk : k ≤ 12 * N) :
    Bobj N p k = evalE N p k BEP := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  have hN' : (p : ℤ) < N := by exact_mod_cast hpN
  unfold Bobj
  rw [Vo_eq hp hsq k hk0 hk, ellp_eq_ind hp _ (by omega), BEP, BXP, evalE_append]
  unfold ind
  rw [ite_eq_left (by omega)]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  ring

theorem Dobj_eqP (hpN : p < N) (k : ℤ) (hk0 : 13 * N + 1 ≤ k) (hk : k ≤ 29 * N + 1) :
    Dobj N p k = -evalE N p k DEP := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  have hN' : (p : ℤ) < N := by exact_mod_cast hpN
  unfold Dobj Ld
  rw [Vd_eq hp hsq k hk0 hk, ellp_eq_ind hp _ (by omega), ellp_eq_ind hp _ (by omega), DEP, DXP,
    evalE_append]
  unfold ind
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  ring

theorem D4obj_eqP (hpN : p < N) (k : ℤ) (hk0 : 13 * N + 1 ≤ k) (hk : k ≤ 29 * N + 1) :
    D4obj N p k = -evalE N p k D4EP := by
  have hp2 : (30 * N + 10 : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsq
  have hN' : (p : ℤ) < N := by exact_mod_cast hpN
  unfold D4obj Ld
  rw [Vd_eq hp hsq k hk0 hk, ellp_eq_ind hp _ (by omega), ellp_eq_ind hp _ (by omega), D4EP, D4XP,
    evalE_append]
  unfold ind
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  unfold evalE
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Term.eval]
  ring

end Objectives

/-! ### Region values of the multiplicities -/

theorem mult_Io_val (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    (0 ≤ k → k ≤ N - 1 → mult (Io N) k = 1) ∧ (N ≤ k → k ≤ 2 * N - 1 → mult (Io N) k = 2) ∧
    (2 * N ≤ k → k ≤ 10 * N + 1 → mult (Io N) k = 3) ∧
    (10 * N + 2 ≤ k → k ≤ 11 * N → mult (Io N) k = 2) ∧
    (11 * N + 1 ≤ k → k ≤ 12 * N → mult (Io N) k = 1) := by
  rw [mult_Io_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    split_ifs <;> omega

theorem mult_Id_val (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    (13 * N + 1 ≤ k → k ≤ 14 * N → mult (Id N) k = 1) ∧
    (14 * N + 1 ≤ k → k ≤ 28 * N + 1 → mult (Id N) k = 2) ∧
    (28 * N + 2 ≤ k → k ≤ 29 * N + 1 → mult (Id N) k = 1) := by
  rw [mult_Id_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;> split_ifs <;> omega

/-! ### The certificates -/

def certA (v : ℤ → ℤ) : ℤ := boundE v 2 0 10 1 VoE AX
def certB (v : ℤ → ℤ) : ℤ :=
  min (boundE v 1 0 2 (-1) VoE (BX 2)) (min (boundE v 2 0 10 1 VoE (BX 3)) (boundE v 10 2 11 0 VoE (BX 2)))
def certC (v : ℤ → ℤ) : ℤ :=
  min (boundE v 0 0 1 (-1) VoE (CX 1)) (min (boundE v 1 0 2 (-1) VoE (CX 2)) (min (boundE v 2 0 10 1 VoE (CX 3))
    (min (boundE v 10 2 11 0 VoE (CX 2)) (boundE v 11 1 12 0 VoE (CX 1)))))
def certD (v : ℤ → ℤ) : ℤ :=
  min (boundE v 13 1 14 0 VdE (DX 1)) (min (boundE v 14 1 28 1 VdE (DX 2)) (boundE v 28 2 29 1 VdE (DX 1)))
def certD4 (v : ℤ → ℤ) : ℤ :=
  min (boundE v 13 1 14 0 VdE (D4X 1)) (min (boundE v 14 1 28 1 VdE (D4X 2)) (boundE v 28 2 29 1 VdE (D4X 1)))

/-- The certified upper bound for `E₃₄(N,p)` when `N < p`. -/
def certI (v : ℤ → ℤ) : ℤ :=
  max (min (max 0 (vpFc v - certA v - certC v)) (max 0 (-certD v)))
    (min (max 0 (vpFc v - certB v - certC v)) (max 0 (-certD4 v)))

def certAP (w : ℤ → ℤ) : ℤ := boundP w 2 0 VoE AX
def certBP (w : ℤ → ℤ) : ℤ :=
  min (boundP w 1 0 VoE BXP) (min (boundP w 2 0 VoE BXP) (boundP w 10 2 VoE BXP))
def certCP (w : ℤ → ℤ) : ℤ :=
  min (boundP w 0 0 VoE CXP) (min (boundP w 1 0 VoE CXP) (min (boundP w 2 0 VoE CXP)
    (min (boundP w 10 2 VoE CXP) (boundP w 11 1 VoE CXP))))
def certDP (w : ℤ → ℤ) : ℤ := min (boundP w 13 1 VdE DXP) (min (boundP w 14 1 VdE DXP) (boundP w 28 2 VdE DXP))
def certD4P (w : ℤ → ℤ) : ℤ :=
  min (boundP w 13 1 VdE D4XP) (min (boundP w 14 1 VdE D4XP) (boundP w 28 2 VdE D4XP))

/-- The certified upper bound for `E₃₄(N,p)` when `N > p`, in terms of the data of `N mod p`. -/
def certP (w : ℤ → ℤ) : ℤ :=
  max (min (max 0 (vpFc w - certAP w - certCP w)) (max 0 (-certDP w)))
    (min (max 0 (vpFc w - certBP w - certCP w)) (max 0 (-certD4P w)))

/-- All range conditions of the regions, checked once by `decide`. -/
theorem regions_ok :
    regionOK 2 0 10 1 VoE AX ∧
    regionOK 1 0 2 (-1) VoE (BX 2) ∧ regionOK 2 0 10 1 VoE (BX 3) ∧ regionOK 10 2 11 0 VoE (BX 2) ∧
    regionOK 0 0 1 (-1) VoE (CX 1) ∧ regionOK 1 0 2 (-1) VoE (CX 2) ∧ regionOK 2 0 10 1 VoE (CX 3) ∧
      regionOK 10 2 11 0 VoE (CX 2) ∧ regionOK 11 1 12 0 VoE (CX 1) ∧
    regionOK 13 1 14 0 VdE (DX 1) ∧ regionOK 14 1 28 1 VdE (DX 2) ∧ regionOK 28 2 29 1 VdE (DX 1) ∧
    regionOK 13 1 14 0 VdE (D4X 1) ∧ regionOK 14 1 28 1 VdE (D4X 2) ∧ regionOK 28 2 29 1 VdE (D4X 1) := by
  decide +kernel

theorem regionsP_ok :
    regionOKP 2 0 VoE AX ∧ regionOKP 1 0 VoE BXP ∧ regionOKP 2 0 VoE BXP ∧ regionOKP 10 2 VoE BXP ∧
    regionOKP 0 0 VoE CXP ∧ regionOKP 1 0 VoE CXP ∧ regionOKP 2 0 VoE CXP ∧ regionOKP 10 2 VoE CXP ∧
      regionOKP 11 1 VoE CXP ∧
    regionOKP 13 1 VdE DXP ∧ regionOKP 14 1 VdE DXP ∧ regionOKP 28 2 VdE DXP ∧
    regionOKP 13 1 VdE D4XP ∧ regionOKP 14 1 VdE D4XP ∧ regionOKP 28 2 VdE D4XP := by
  decide +kernel

theorem slopes_zero :
    (AE.map Term.slope).sum = 0 ∧ (BEP.map Term.slope).sum = 0 ∧ (CEP.map Term.slope).sum = 0 ∧
    (DEP.map Term.slope).sum = 0 ∧ (D4EP.map Term.slope).sum = 0 := by
  decide +kernel

/-! ### Lower bounds on the minima -/

theorem minOn_ge (s : Finset ℤ) (f : ℤ → ℤ) (m : ℤ) (hs : s.Nonempty) (h : ∀ k ∈ s, m ≤ f k) :
    m ≤ minOn s f := by
  unfold minOn
  rw [dite_eq_left hs]
  exact Finset.le_inf' hs f h

theorem boundP_shift (v w : ℤ → ℤ) (n : ℤ) (hvw : ∀ c, |c| ≤ 29 → v c = n * c + w c)
    (clo dlo : ℤ) (E₁ E₂ : List Term) (hok : regionOKP clo dlo E₁ E₂)
    (hs : ((E₁ ++ E₂).map Term.slope).sum = 0) :
    boundP v clo dlo E₁ E₂ = boundP w clo dlo E₁ E₂ := by
  unfold boundP classMinP
  rw [evalCandE_shift v w n hvw _ _ _ (E₁ ++ E₂) hok.1 hok.2.2.1, hs, hok.2.1]
  congr 1
  · ring
  · congr 1
    refine List.map_congr_left fun cd hcd => ?_
    have h := evalCandE_shift v w n hvw cd.1 cd.2 0 (E₁ ++ E₂) hok.1 (hok.2.2.2 cd hcd)
    rw [hs, hok.2.1, evalCandE_append, evalCandE_append] at h
    linarith

section Bounds
variable {N p : ℕ} (hp : p.Prime) (hp10 : 10 < p) (hN : 1 ≤ N) (hsq : 30 * N + 10 < p ^ 2)
  (hNB : NB N p) {v : ℤ → ℤ} (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c)
include hp hp10 hN hsq hNB hv

theorem certA_le : certA v ≤ Ap N p := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  refine minOn_ge _ _ _ ⟨2 * N, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  rw [Aobj_eq hp hN hsq k h1 h2]
  exact region_ge_bound hp10' hNB hv 2 0 10 1 VoE AX regions_ok.1 k (by push_cast; omega)
    (by push_cast; omega)

theorem certC_le : certC v ≤ Cp N p := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  refine minOn_ge _ _ _ ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  change certC v ≤ Cobj N p k
  obtain ⟨m1, m2, m3, m4, m5⟩ := mult_Io_val N hN k
  obtain ⟨-, r1, r2, r3, r4, r5, r6, r7, r8, -⟩ := regions_ok
  unfold certC
  rcases (by omega : k ≤ N - 1 ∨ (N ≤ k ∧ k ≤ 2 * N - 1) ∨ (2 * N ≤ k ∧ k ≤ 10 * N + 1) ∨
    (10 * N + 2 ≤ k ∧ k ≤ 11 * N) ∨ 11 * N + 1 ≤ k) with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · rw [Cobj_eq hp hN hsq 1 k h1 h2 (m1 h1 h)]
    exact (min_le_left _ _).trans (region_ge_bound hp10' hNB hv 0 0 1 (-1) VoE (CX 1) r4 k
      (by push_cast; omega) (by push_cast; omega))
  · rw [Cobj_eq hp hN hsq 2 k h1 h2 (m2 h h')]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans (region_ge_bound hp10' hNB hv 1 0 2 (-1)
      VoE (CX 2) r5 k (by push_cast; omega) (by push_cast; omega))
  · rw [Cobj_eq hp hN hsq 3 k h1 h2 (m3 h h')]
    exact ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans
      (region_ge_bound hp10' hNB hv 2 0 10 1 VoE (CX 3) r6 k (by push_cast; omega)
        (by push_cast; omega))
  · rw [Cobj_eq hp hN hsq 2 k h1 h2 (m4 h h')]
    exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))).trans (region_ge_bound hp10' hNB hv 10 2 11 0 VoE (CX 2) r7 k
        (by push_cast; omega) (by push_cast; omega))
  · rw [Cobj_eq hp hN hsq 1 k h1 h2 (m5 h h2)]
    exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))).trans (region_ge_bound hp10' hNB hv 11 1 12 0 VoE (CX 1) r8 k
        (by push_cast; omega) (by push_cast; omega))

theorem certB_le : certB v ≤ Bp N p := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  refine minOn_ge _ _ _ ⟨2 * N, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    by rw [(mult_Io_val N hN (2 * N)).2.2.1 le_rfl (by omega)]; norm_num⟩⟩ fun k hk => ?_
  obtain ⟨hk, hm⟩ := Finset.mem_filter.mp hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  change certB v ≤ Bobj N p k
  obtain ⟨m1, m2, m3, m4, m5⟩ := mult_Io_val N hN k
  obtain ⟨-, r1, r2, r3, -⟩ := regions_ok
  unfold certB
  rcases (by omega : k ≤ N - 1 ∨ (N ≤ k ∧ k ≤ 2 * N - 1) ∨ (2 * N ≤ k ∧ k ≤ 10 * N + 1) ∨
    (10 * N + 2 ≤ k ∧ k ≤ 11 * N) ∨ 11 * N + 1 ≤ k) with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · rw [m1 h1 h] at hm; omega
  · rw [Bobj_eq hp hN hsq 2 k h1 h2 (m2 h h')]
    exact (min_le_left _ _).trans (region_ge_bound hp10' hNB hv 1 0 2 (-1) VoE (BX 2) r1 k
      (by push_cast; omega) (by push_cast; omega))
  · rw [Bobj_eq hp hN hsq 3 k h1 h2 (m3 h h')]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans (region_ge_bound hp10' hNB hv 2 0 10 1
      VoE (BX 3) r2 k (by push_cast; omega) (by push_cast; omega))
  · rw [Bobj_eq hp hN hsq 2 k h1 h2 (m4 h h')]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (region_ge_bound hp10' hNB hv 10 2 11 0
      VoE (BX 2) r3 k (by push_cast; omega) (by push_cast; omega))
  · rw [m5 h h2] at hm; omega

theorem certD_le (k : ℤ) (h1 : 13 * N + 1 ≤ k) (h2 : k ≤ 29 * N + 1) : Dobj N p k ≤ -certD v := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  obtain ⟨m1, m2, m3⟩ := mult_Id_val N hN k
  obtain ⟨-, -, -, -, -, -, -, -, -, r1, r2, r3, -⟩ := regions_ok
  unfold certD
  rw [le_neg]
  rcases (by omega : k ≤ 14 * N ∨ (14 * N + 1 ≤ k ∧ k ≤ 28 * N + 1) ∨ 28 * N + 2 ≤ k) with
    h | ⟨h, h'⟩ | h
  · rw [Dobj_eq hp hN hsq 1 k h1 h2 (m1 h1 h), neg_neg]
    exact (min_le_left _ _).trans (region_ge_bound hp10' hNB hv 13 1 14 0 VdE (DX 1) r1 k
      (by push_cast; omega) (by push_cast; omega))
  · rw [Dobj_eq hp hN hsq 2 k h1 h2 (m2 h h'), neg_neg]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans (region_ge_bound hp10' hNB hv 14 1 28 1
      VdE (DX 2) r2 k (by push_cast; omega) (by push_cast; omega))
  · rw [Dobj_eq hp hN hsq 1 k h1 h2 (m3 h h2), neg_neg]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (region_ge_bound hp10' hNB hv 28 2 29 1
      VdE (DX 1) r3 k (by push_cast; omega) (by push_cast; omega))

theorem certD4_le (k : ℤ) (h1 : 13 * N + 1 ≤ k) (h2 : k ≤ 29 * N + 1) :
    D4obj N p k ≤ -certD4 v := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  obtain ⟨m1, m2, m3⟩ := mult_Id_val N hN k
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r1, r2, r3⟩ := regions_ok
  unfold certD4
  rw [le_neg]
  rcases (by omega : k ≤ 14 * N ∨ (14 * N + 1 ≤ k ∧ k ≤ 28 * N + 1) ∨ 28 * N + 2 ≤ k) with
    h | ⟨h, h'⟩ | h
  · rw [D4obj_eq hp hN hsq 1 k h1 h2 (m1 h1 h), neg_neg]
    exact (min_le_left _ _).trans (region_ge_bound hp10' hNB hv 13 1 14 0 VdE (D4X 1) r1 k
      (by push_cast; omega) (by push_cast; omega))
  · rw [D4obj_eq hp hN hsq 2 k h1 h2 (m2 h h'), neg_neg]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans (region_ge_bound hp10' hNB hv 14 1 28 1
      VdE (D4X 2) r2 k (by push_cast; omega) (by push_cast; omega))
  · rw [D4obj_eq hp hN hsq 1 k h1 h2 (m3 h h2), neg_neg]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (region_ge_bound hp10' hNB hv 28 2 29 1
      VdE (D4X 1) r3 k (by push_cast; omega) (by push_cast; omega))

end Bounds

/-! ### Assembly -/

theorem padicValNat_six {p : ℕ} (hp : p.Prime) (hp10 : 10 < p) : padicValNat p 6 = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => by have := Nat.le_of_dvd (by norm_num) h; omega

theorem E34_le_of_bounds {N p : ℕ} (hp : p.Prime) (hp10 : 10 < p) (hN : 1 ≤ N)
    (A B C D D4 F : ℤ) (hA : A ≤ Ap N p) (hB : B ≤ Bp N p) (hC : C ≤ Cp N p)
    (hD : ∀ k : ℤ, 13 * N + 1 ≤ k → k ≤ 29 * N + 1 → Dobj N p k ≤ -D)
    (hD4 : ∀ k : ℤ, 13 * N + 1 ≤ k → k ≤ 29 * N + 1 → D4obj N p k ≤ -D4) (hF : vpF N p = F) :
    E34 N p ≤ max (min (max 0 (F - A - C)) (max 0 (-D))) (min (max 0 (F - B - C)) (max 0 (-D4))) := by
  unfold E34
  rw [ite_eq_left (by omega)]
  have hEo : Eo N p ≤ max 0 (F - A - C) := by
    unfold Eo; rw [hF]; exact max_le_max le_rfl (by omega)
  have hEo4 : Eo4 N p ≤ max 0 (F - B - C) := by
    unfold Eo4; rw [hF]; exact max_le_max le_rfl (by omega)
  have hEd : Ed N p ≤ max 0 (-D) := by
    unfold Ed
    rw [padicValNat_six hp hp10, Nat.cast_zero, max_self]
    refine max_le (le_max_left _ _) (maxOn_le _ _ _ (le_max_left _ _) fun k hk => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    exact (hD k h1 h2).trans (le_max_right _ _)
  have hEd4 : Ed4 N p ≤ max 0 (-D4) := by
    unfold Ed4
    refine max_le (le_max_left _ _) (maxOn_le _ _ _ (le_max_left _ _) fun k hk => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    exact (hD4 k h1 h2).trans (le_max_right _ _)
  exact max_le_max (min_le_min hEo hEd) (min_le_min hEo4 hEd4)

/-- **`E₃₄(N,p) ≤ certI v` for `N < p`.** -/
theorem E34_le_certI {N p : ℕ} (hp : p.Prime) (hp10 : 10 < p) (hN : 1 ≤ N)
    (hsq : 30 * N + 10 < p ^ 2) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) : E34 N p ≤ certI v :=
  E34_le_of_bounds hp hp10 hN _ _ _ _ _ _ (certA_le hp hp10 hN hsq hNB hv)
    (certB_le hp hp10 hN hsq hNB hv) (certC_le hp hp10 hN hsq hNB hv)
    (certD_le hp hp10 hN hsq hNB hv) (certD4_le hp hp10 hN hsq hNB hv)
    (vpF_eq hp hp10 hsq hNB hv)

section Periodic
variable {N p : ℕ} (hp : p.Prime) (hp10 : 10 < p) (hN : p < N) (hsq : 30 * N + 10 < p ^ 2)
  (hNB : NB N p) {w : ℤ → ℤ} (n : ℤ) (hv : ∀ c, |c| ≤ 29 → (c * N) / p = n * c + w c)
include hp hp10 hN hsq hNB hv

theorem certAP_le : certAP w ≤ Ap N p := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  refine minOn_ge _ _ _ ⟨2 * N, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  rw [Aobj_eq hp (by omega) hsq k h1 h2, certAP,
    ← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 2 0 VoE AX regionsP_ok.1 slopes_zero.1]
  exact region_ge_boundP hp10' hNB hv 2 0 VoE AX regionsP_ok.1 _ k (by push_cast; omega) le_rfl

theorem certCP_le : certCP w ≤ Cp N p := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  refine minOn_ge _ _ _ ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  change certCP w ≤ Cobj N p k
  obtain ⟨-, -, -, -, r1, r2, r3, r4, r5, -⟩ := regionsP_ok
  have hs := slopes_zero.2.2.1
  rw [Cobj_eqP hp (by omega) hsq hN k h1 h2]
  unfold certCP
  rcases (by omega : k ≤ N - 1 ∨ (N ≤ k ∧ k ≤ 2 * N - 1) ∨ (2 * N ≤ k ∧ k ≤ 10 * N + 1) ∨
    (10 * N + 2 ≤ k ∧ k ≤ 11 * N) ∨ 11 * N + 1 ≤ k) with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · refine (min_le_left _ _).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 0 0 VoE CXP r1 hs]
    exact region_ge_boundP hp10' hNB hv 0 0 VoE CXP r1 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_left _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 1 0 VoE CXP r2 hs]
    exact region_ge_boundP hp10' hNB hv 1 0 VoE CXP r2 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 2 0 VoE CXP r3 hs]
    exact region_ge_boundP hp10' hNB hv 2 0 VoE CXP r3 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 10 2 VoE CXP r4 hs]
    exact region_ge_boundP hp10' hNB hv 10 2 VoE CXP r4 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 11 1 VoE CXP r5 hs]
    exact region_ge_boundP hp10' hNB hv 11 1 VoE CXP r5 _ k (by push_cast; omega) le_rfl

theorem certBP_le : certBP w ≤ Bp N p := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  refine minOn_ge _ _ _ ⟨2 * N, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    by rw [(mult_Io_val N (by omega) (2 * N)).2.2.1 le_rfl (by omega)]; norm_num⟩⟩ fun k hk => ?_
  obtain ⟨hk, hm⟩ := Finset.mem_filter.mp hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  change certBP w ≤ Bobj N p k
  obtain ⟨m1, -, -, -, m5⟩ := mult_Io_val N (by omega) k
  obtain ⟨-, r1, r2, r3, -⟩ := regionsP_ok
  have hs := slopes_zero.2.1
  rw [Bobj_eqP hp (by omega) hsq hN k h1 h2]
  unfold certBP
  rcases (by omega : k ≤ N - 1 ∨ (N ≤ k ∧ k ≤ 2 * N - 1) ∨ (2 * N ≤ k ∧ k ≤ 10 * N + 1) ∨
    (10 * N + 2 ≤ k ∧ k ≤ 11 * N) ∨ 11 * N + 1 ≤ k) with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · rw [m1 h1 h] at hm; omega
  · refine (min_le_left _ _).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 1 0 VoE BXP r1 hs]
    exact region_ge_boundP hp10' hNB hv 1 0 VoE BXP r1 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_left _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 2 0 VoE BXP r2 hs]
    exact region_ge_boundP hp10' hNB hv 2 0 VoE BXP r2 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_right _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 10 2 VoE BXP r3 hs]
    exact region_ge_boundP hp10' hNB hv 10 2 VoE BXP r3 _ k (by push_cast; omega) le_rfl
  · rw [m5 h h2] at hm; omega

theorem certDP_le (k : ℤ) (h1 : 13 * N + 1 ≤ k) (h2 : k ≤ 29 * N + 1) :
    Dobj N p k ≤ -certDP w := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  obtain ⟨-, -, -, -, -, -, -, -, -, r1, r2, r3, -⟩ := regionsP_ok
  have hs := slopes_zero.2.2.2.1
  rw [Dobj_eqP hp (by omega) hsq hN k h1 h2, neg_le, neg_neg]
  unfold certDP
  rcases (by omega : k ≤ 14 * N ∨ (14 * N + 1 ≤ k ∧ k ≤ 28 * N + 1) ∨ 28 * N + 2 ≤ k) with
    h | ⟨h, h'⟩ | h
  · refine (min_le_left _ _).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 13 1 VdE DXP r1 hs]
    exact region_ge_boundP hp10' hNB hv 13 1 VdE DXP r1 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_left _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 14 1 VdE DXP r2 hs]
    exact region_ge_boundP hp10' hNB hv 14 1 VdE DXP r2 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_right _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 28 2 VdE DXP r3 hs]
    exact region_ge_boundP hp10' hNB hv 28 2 VdE DXP r3 _ k (by push_cast; omega) le_rfl

theorem certD4P_le (k : ℤ) (h1 : 13 * N + 1 ≤ k) (h2 : k ≤ 29 * N + 1) :
    D4obj N p k ≤ -certD4P w := by
  have hp10' : (10 : ℤ) < p := by exact_mod_cast hp10
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r1, r2, r3⟩ := regionsP_ok
  have hs := slopes_zero.2.2.2.2
  rw [D4obj_eqP hp (by omega) hsq hN k h1 h2, neg_le, neg_neg]
  unfold certD4P
  rcases (by omega : k ≤ 14 * N ∨ (14 * N + 1 ≤ k ∧ k ≤ 28 * N + 1) ∨ 28 * N + 2 ≤ k) with
    h | ⟨h, h'⟩ | h
  · refine (min_le_left _ _).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 13 1 VdE D4XP r1 hs]
    exact region_ge_boundP hp10' hNB hv 13 1 VdE D4XP r1 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_left _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 14 1 VdE D4XP r2 hs]
    exact region_ge_boundP hp10' hNB hv 14 1 VdE D4XP r2 _ k (by push_cast; omega) le_rfl
  · refine ((min_le_right _ _).trans (min_le_right _ _)).trans ?_
    rw [← boundP_shift (fun c => n * c + w c) w n (fun _ _ => rfl) 28 2 VdE D4XP r3 hs]
    exact region_ge_boundP hp10' hNB hv 28 2 VdE D4XP r3 _ k (by push_cast; omega) le_rfl

/-- `vpF` through the data of the fractional part (the slope sums `165 - 115 - 50` cancel). -/
theorem vpF_eqP : vpF N p = vpFc w := by
  rw [vpF_eq hp hp10 hsq hNB hv]
  unfold vpFc
  ring

/-- **`E₃₄(N,p) ≤ certP w` for `N > p`.** -/
theorem E34_le_certP : E34 N p ≤ certP w :=
  E34_le_of_bounds hp hp10 (by omega) _ _ _ _ _ _ (certAP_le hp hp10 hN hsq hNB n hv)
    (certBP_le hp hp10 hN hsq hNB n hv) (certCP_le hp hp10 hN hsq hNB n hv)
    (certDP_le hp hp10 hN hsq hNB n hv) (certD4P_le hp hp10 hN hsq hNB n hv)
    (vpF_eqP hp hp10 hN hsq hNB n hv)

end Periodic

end ZetasIrr.CH
