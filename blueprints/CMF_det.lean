/-
# CMF transport, part 6: the axis determinants

The determinant of the transport matrix `W_N` of the walk `p_N → p_{N+1}` is computed by the
"axis determinants" (PDF Part VII §2): the potential
  `V(p) = ∏_{i ∈ {2,3}} ∏_j (b_j - a_i)! / (∏_{i ∈ {0,1,4}} ∏_j (a_i - b_j - 1)! · (d₄ - 1)!)`
satisfies `det (step matrix of e at p) = σ(e) · V(e.apply p)/V(p)` for every edge of the walk
(`det_edge`), where `σ(e) = +1` for the moves of `a₂, a₃` and `-1` otherwise, so that
`det W_N = -V(p_{N+1})/V(p_N)` (`det_Wmat`), and `V(p_N) = F_N` (`Vpot_pN`).
-/
import CMF_path
import CMF_pairing

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-! ### Factorials of integers -/

/-- `z! = (max z 0)!`. -/
def fact (z : ℤ) : ℚ := (z.toNat.factorial : ℚ)

theorem fact_pos (z : ℤ) : 0 < fact z := by unfold fact; exact_mod_cast Nat.factorial_pos _

@[simp] theorem fact_ne_zero (z : ℤ) : fact z ≠ 0 := (fact_pos z).ne'

theorem fact_succ (z : ℤ) (hz : 0 ≤ z) : fact (z + 1) = ((z : ℚ) + 1) * fact z := by
  unfold fact
  rw [show (z + 1).toNat = z.toNat + 1 by omega, Nat.factorial_succ]
  have h : ((z.toNat : ℕ) : ℚ) = (z : ℚ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, h]

/-- `(x - (y - 1))! = (x - y + 1) (x - y)!`. -/
theorem fact_A (x y : ℤ) (h : 0 ≤ x - y) :
    fact (x - (y - 1)) = ((x - y : ℤ) + 1 : ℚ) * fact (x - y) := by
  rw [show x - (y - 1) = x - y + 1 by ring, fact_succ _ h]

/-- `(x - y - 1)! = (x - y - 1) (x - 1 - y - 1)!`. -/
theorem fact_B (x y : ℤ) (h : 1 ≤ x - y - 1) :
    fact (x - y - 1) = ((x - y - 1 : ℤ) : ℚ) * fact (x - 1 - y - 1) := by
  have := fact_succ (x - 1 - y - 1) (by omega)
  rw [show x - 1 - y - 1 + 1 = x - y - 1 by ring] at this
  rw [this]; push_cast; try ring

/-- `(x + 1 - y)! = (x - y + 1) (x - y)!`. -/
theorem fact_C (x y : ℤ) (h : 0 ≤ x - y) :
    fact (x + 1 - y) = ((x - y : ℤ) + 1 : ℚ) * fact (x - y) := by
  rw [show x + 1 - y = x - y + 1 by ring, fact_succ _ h]

/-- `(x - y - 1)! = (x - y - 1) (x - (y + 1) - 1)!`. -/
theorem fact_D (x y : ℤ) (h : 1 ≤ x - y - 1) :
    fact (x - y - 1) = ((x - y - 1 : ℤ) : ℚ) * fact (x - (y + 1) - 1) := by
  have := fact_succ (x - (y + 1) - 1) (by omega)
  rw [show x - (y + 1) - 1 + 1 = x - y - 1 by ring] at this
  rw [this]; push_cast; try ring

/-- `(d + 1 - 1)! = d (d - 1)!`. -/
theorem fact_E (d : ℤ) (h : 1 ≤ d) : fact (d + 1 - 1) = (d : ℚ) * fact (d - 1) := by
  have := fact_succ (d - 1) (by omega)
  rw [show d - 1 + 1 = d by ring] at this
  rw [add_sub_cancel_right, this]; push_cast; try ring

/-! ### The potential -/

/-- `∏_j (b_j - a_i)!`. -/
def ZA (p : Pt) (i : Fin 5) : ℚ :=
  fact (p.b 0 - p.a i) * fact (p.b 1 - p.a i) * fact (p.b 2 - p.a i) * fact (p.b 3 - p.a i) *
    fact (p.b 4 - p.a i)

/-- `∏_j (a_i - b_j - 1)!`. -/
def PA (p : Pt) (i : Fin 5) : ℚ :=
  fact (p.a i - p.b 0 - 1) * fact (p.a i - p.b 1 - 1) * fact (p.a i - p.b 2 - 1) *
    fact (p.a i - p.b 3 - 1) * fact (p.a i - p.b 4 - 1)

/-- `d₄ = 5 - ∑ a_i + ∑ b_j`. -/
def d4 (p : Pt) : ℤ :=
  5 - (p.a 0 + p.a 1 + p.a 2 + p.a 3 + p.a 4) + (p.b 0 + p.b 1 + p.b 2 + p.b 3 + p.b 4)

theorem dc4_eq_d4 (p : Pt) : p.dc 4 = (d4 p : ℚ) := by
  show dc _ _ 4 = _
  rw [dc_four, d4]; push_cast; ring

/-- The potential `V`. -/
def Vpot (p : Pt) : ℚ := ZA p 2 * ZA p 3 / (PA p 0 * PA p 1 * PA p 4 * fact (d4 p - 1))

theorem ZA_ne_zero (p : Pt) (i : Fin 5) : ZA p i ≠ 0 := by
  unfold ZA
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (fact_ne_zero _) (fact_ne_zero _))
    (fact_ne_zero _)) (fact_ne_zero _)) (fact_ne_zero _)

theorem PA_ne_zero (p : Pt) (i : Fin 5) : PA p i ≠ 0 := by
  unfold PA
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (fact_ne_zero _) (fact_ne_zero _))
    (fact_ne_zero _)) (fact_ne_zero _)) (fact_ne_zero _)

theorem Vpot_ne_zero (p : Pt) : Vpot p ≠ 0 := by
  unfold Vpot
  exact div_ne_zero (mul_ne_zero (ZA_ne_zero _ _) (ZA_ne_zero _ _))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (PA_ne_zero _ _) (PA_ne_zero _ _)) (PA_ne_zero _ _))
      (fact_ne_zero _))

/-- The sign conditions on the parameters that hold along the whole walk. -/
def Typ (p : Pt) : Prop :=
  (∀ j, 1 ≤ p.a 0 - p.b j) ∧ (∀ j, 1 ≤ p.a 1 - p.b j) ∧ (∀ j, 1 ≤ p.a 4 - p.b j) ∧
    (∀ j, p.a 2 - p.b j ≤ 0) ∧ (∀ j, p.a 3 - p.b j ≤ 0) ∧ 1 ≤ d4 p

/-- The sign of an edge: `+1` for the moves of `a₂, a₃`, `-1` otherwise. -/
def sgn (e : Edge) : ℚ := if e.isA ∧ (e.i = 2 ∨ e.i = 3) then 1 else -1

theorem sgn_sq (e : Edge) : sgn e * sgn e = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_dual (e : Edge) : sgn e.dual = sgn e := rfl

theorem d4_apply (e : Edge) (p : Pt) : d4 (e.apply p) = d4 p + (if e.fwd then 1 else -1) := by
  rcases e with ⟨isA, i, up⟩
  rcases p with ⟨a, b⟩
  cases isA <;> cases up <;> fin_cases i <;>
    simp only [Edge.apply, Edge.fwd, d4, Function.update_apply, Fin.reduceEq, ite_true, ite_false,
      Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_true_eq_false, not_false_eq_true,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

/-! ### The determinant across a forward edge -/

macro "upd_simp" : tactic => `(tactic|
  simp only [Edge.apply, Function.update_apply, Fin.reduceEq, ite_true, ite_false,
    Bool.false_eq_true, Bool.true_eq_false, Edge.cval, sub_zero])

/-- `det (Amat p.dc c) = Deval(c)/d₄`. -/
theorem det_Amat' (p : Pt) (c : ℚ) (hd : 1 ≤ d4 p) :
    (Amat p.dc c).det = Deval p.a p.b c / (d4 p : ℚ) := by
  unfold Deval
  rw [det_Amat _ _ (by rw [dc4_eq_d4]; exact_mod_cast (show d4 p ≠ 0 by omega)), dc4_eq_d4,
    show dc p.a p.b 4 = (d4 p : ℚ) from dc4_eq_d4 p]
  rfl

theorem Deval_lower (a b : Fin 5 → ℤ) (i : Fin 5) :
    Deval a b ((a i : ℚ) - 1) = -∏ j, (((a i : ℚ) - 1) - bq b j) := by
  rw [Deval_eq', Finset.prod_eq_zero (Finset.mem_univ i) (by rw [al]; ring), zero_sub]

theorem Deval_raise (a b : Fin 5 → ℤ) (j : Fin 5) :
    Deval a b (b j : ℚ) = ∏ i, ((b j : ℚ) - al a i) := by
  rw [Deval_eq', Finset.prod_eq_zero (f := fun i => (b j : ℚ) - bq b i) (Finset.mem_univ j)
    (by show (b j : ℚ) - (b j : ℚ) = 0; exact sub_self _), sub_zero]

theorem cval_lower (i : Fin 5) (p : Pt) :
    ((Edge.cval ⟨true, i, false⟩ p : ℤ) : ℚ) = (p.a i : ℚ) - 1 := by
  simp only [Edge.cval, ite_true, Bool.false_eq_true, ite_false]; push_cast; ring

theorem cval_raise (j : Fin 5) (p : Pt) :
    ((Edge.cval ⟨false, j, true⟩ p : ℤ) : ℚ) = (p.b j : ℚ) := by
  simp only [Edge.cval, ite_true, Bool.false_eq_true, ite_false, sub_zero]

/-- The statement `det (Amat p.dc (cval e p)) = sgn e · V(e.apply p)/V(p)` for a forward edge. -/
def DetFwd (e : Edge) (p : Pt) : Prop :=
  (Amat p.dc ((e.cval p : ℤ) : ℚ)).det = sgn e * Vpot (e.apply p) / Vpot p

/-! ### Potential ratios across an edge -/

theorem ZA_eq_prod (p : Pt) (i : Fin 5) : ZA p i = ∏ j, fact (p.b j - p.a i) := by
  rw [Fin.prod_univ_five]; rfl

theorem PA_eq_prod (p : Pt) (i : Fin 5) : PA p i = ∏ j, fact (p.a i - p.b j - 1) := by
  rw [Fin.prod_univ_five]; rfl

theorem prodZ_update (c : ℤ) (b : Fin 5 → ℤ) (j : Fin 5) (x : ℤ) :
    ∏ k, fact (Function.update b j x k - c) = fact (x - c) * ∏ k ∈ {j}ᶜ, fact (b k - c) := by
  rw [Fintype.prod_eq_mul_prod_compl j, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (by simpa using hk)]

theorem prodZ_split (c : ℤ) (b : Fin 5 → ℤ) (j : Fin 5) :
    ∏ k, fact (b k - c) = fact (b j - c) * ∏ k ∈ {j}ᶜ, fact (b k - c) :=
  Fintype.prod_eq_mul_prod_compl j _

theorem prodP_update (c : ℤ) (b : Fin 5 → ℤ) (j : Fin 5) (x : ℤ) :
    ∏ k, fact (c - Function.update b j x k - 1) =
      fact (c - x - 1) * ∏ k ∈ {j}ᶜ, fact (c - b k - 1) := by
  rw [Fintype.prod_eq_mul_prod_compl j, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (by simpa using hk)]

theorem prodP_split (c : ℤ) (b : Fin 5 → ℤ) (j : Fin 5) :
    ∏ k, fact (c - b k - 1) = fact (c - b j - 1) * ∏ k ∈ {j}ᶜ, fact (c - b k - 1) :=
  Fintype.prod_eq_mul_prod_compl j _

/-- Lowering `a_i` with `a_i ≤ b_j` for all `j` multiplies `ZA i` by `∏_j (b_j - a_i + 1)`. -/
theorem ZA_lower (a b : Fin 5 → ℤ) (i : Fin 5) (h : ∀ j, a i - b j ≤ 0) :
    ZA (Edge.apply ⟨true, i, false⟩ ⟨a, b⟩) i =
      (∏ j, (((b j - a i : ℤ) : ℚ) + 1)) * ZA ⟨a, b⟩ i := by
  simp only [Edge.apply, ZA, Function.update_self, Fin.prod_univ_five, ite_true,
    Bool.false_eq_true, ite_false]
  rw [fact_A _ _ (by have := h 0; omega), fact_A _ _ (by have := h 1; omega),
    fact_A _ _ (by have := h 2; omega), fact_A _ _ (by have := h 3; omega),
    fact_A _ _ (by have := h 4; omega)]
  ring

theorem ZA_lower_ne (a b : Fin 5 → ℤ) (i i' : Fin 5) (h : i' ≠ i) :
    ZA (Edge.apply ⟨true, i, false⟩ ⟨a, b⟩) i' = ZA ⟨a, b⟩ i' := by
  simp only [Edge.apply, ZA, Function.update_of_ne h, ite_true, Bool.false_eq_true, ite_false]

theorem PA_lower_ne (a b : Fin 5 → ℤ) (i i' : Fin 5) (h : i' ≠ i) :
    PA (Edge.apply ⟨true, i, false⟩ ⟨a, b⟩) i' = PA ⟨a, b⟩ i' := by
  simp only [Edge.apply, PA, Function.update_of_ne h, ite_true, Bool.false_eq_true, ite_false]

/-- Lowering `a_i` with `a_i - 1 > b_j` for all `j` divides `PA i` by `∏_j (a_i - b_j - 1)`. -/
theorem PA_lower (a b : Fin 5 → ℤ) (i : Fin 5) (h : ∀ j, 1 ≤ a i - 1 - b j) :
    PA ⟨a, b⟩ i =
      (∏ j, ((a i - b j - 1 : ℤ) : ℚ)) * PA (Edge.apply ⟨true, i, false⟩ ⟨a, b⟩) i := by
  simp only [Edge.apply, PA, Function.update_self, Fin.prod_univ_five, ite_true,
    Bool.false_eq_true, ite_false]
  rw [fact_B (a i) (b 0) (by have := h 0; omega), fact_B (a i) (b 1) (by have := h 1; omega),
    fact_B (a i) (b 2) (by have := h 2; omega), fact_B (a i) (b 3) (by have := h 3; omega),
    fact_B (a i) (b 4) (by have := h 4; omega)]
  ring

/-- Raising `b_j` multiplies `ZA i` by `b_j - a_i + 1`. -/
theorem ZA_raise (a b : Fin 5 → ℤ) (j i : Fin 5) (h : a i - b j ≤ 0) :
    ZA (Edge.apply ⟨false, j, true⟩ ⟨a, b⟩) i = (((b j - a i : ℤ) : ℚ) + 1) * ZA ⟨a, b⟩ i := by
  simp only [Edge.apply, Bool.false_eq_true, ite_false, ite_true]
  rw [ZA_eq_prod, ZA_eq_prod]
  dsimp only
  rw [prodZ_update, prodZ_split (a i) b j, fact_C _ _ (by omega), mul_assoc]

/-- Raising `b_j` divides `PA i` by `a_i - b_j - 1`. -/
theorem PA_raise (a b : Fin 5 → ℤ) (j i : Fin 5) (h : 1 ≤ a i - (b j + 1)) :
    PA ⟨a, b⟩ i = ((a i - b j - 1 : ℤ) : ℚ) * PA (Edge.apply ⟨false, j, true⟩ ⟨a, b⟩) i := by
  simp only [Edge.apply, Bool.false_eq_true, ite_false, ite_true]
  rw [PA_eq_prod, PA_eq_prod]
  dsimp only
  rw [prodP_update, prodP_split (a i) b j, fact_D _ _ (by omega), mul_assoc]

theorem fact_d4_apply (e : Edge) (p : Pt) (hf : e.fwd) (hd : 1 ≤ d4 p) :
    fact (d4 (e.apply p) - 1) = (d4 p : ℚ) * fact (d4 p - 1) := by
  rw [d4_apply, ite_eq_left hf, fact_E _ hd]

/-- The generic ratio computation. -/
theorem key_ratio (s X Y d Nn Dn Nm Dm : ℚ) (hNm : Nm ≠ 0) (hDn : Dn ≠ 0) (hd : d ≠ 0)
    (hY : Y ≠ 0) (hN : Nn = X * Nm) (hD : Y * Dn = d * Dm) :
    s * (Nn / Dn) / (Nm / Dm) = s * (X * Y) / d := by
  subst hN
  obtain rfl : Dm = Y * Dn / d := by rw [eq_div_iff hd, hD, mul_comm]
  field_simp
  try ring

/-- `DetFwd` from the ratios of the `ZA`/`PA` factors. -/
theorem DetFwd_of_key (e : Edge) (p : Pt) (hd : 1 ≤ d4 p) (X Y : ℚ) (hY : Y ≠ 0)
    (hN : ZA (e.apply p) 2 * ZA (e.apply p) 3 = X * (ZA p 2 * ZA p 3))
    (hD : Y * (PA (e.apply p) 0 * PA (e.apply p) 1 * PA (e.apply p) 4 *
        fact (d4 (e.apply p) - 1)) =
      (d4 p : ℚ) * (PA p 0 * PA p 1 * PA p 4 * fact (d4 p - 1)))
    (hDev : Deval p.a p.b ((e.cval p : ℤ) : ℚ) = sgn e * (X * Y)) : DetFwd e p := by
  unfold DetFwd
  rw [det_Amat' _ _ hd, Vpot, Vpot, hDev,
    key_ratio _ X Y _ _ _ _ _ (mul_ne_zero (ZA_ne_zero _ _) (ZA_ne_zero _ _))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (PA_ne_zero _ _) (PA_ne_zero _ _)) (PA_ne_zero _ _))
        (fact_ne_zero _))
      (by exact_mod_cast (show d4 p ≠ 0 by omega)) hY hN hD]

/-- Lowering `a₂`. -/
theorem det_lower_a2 (p : Pt) (hT : Typ p) : DetFwd ⟨true, 2, false⟩ p := by
  obtain ⟨-, -, -, h2, -, hd⟩ := hT
  rcases p with ⟨a, b⟩
  have hs : sgn ⟨true, 2, false⟩ = 1 := by simp [sgn]
  refine DetFwd_of_key _ _ hd (∏ j, (((b j - a 2 : ℤ) : ℚ) + 1)) 1 one_ne_zero ?_ ?_ ?_
  · rw [ZA_lower a b 2 h2, ZA_lower_ne a b 2 3 (by decide), mul_assoc]
  · rw [PA_lower_ne a b 2 0 (by decide), PA_lower_ne a b 2 1 (by decide),
      PA_lower_ne a b 2 4 (by decide), fact_d4_apply ⟨true, 2, false⟩ ⟨a, b⟩ (by decide) hd]
    ring
  · dsimp only
    rw [cval_lower, Deval_lower, hs, one_mul, mul_one]
    simp only [bq, Fin.prod_univ_five]
    push_cast
    ring

/-- Lowering `a₃`. -/
theorem det_lower_a3 (p : Pt) (hT : Typ p) : DetFwd ⟨true, 3, false⟩ p := by
  obtain ⟨-, -, -, -, h3, hd⟩ := hT
  rcases p with ⟨a, b⟩
  have hs : sgn ⟨true, 3, false⟩ = 1 := by simp [sgn]
  refine DetFwd_of_key _ _ hd (∏ j, (((b j - a 3 : ℤ) : ℚ) + 1)) 1 one_ne_zero ?_ ?_ ?_
  · rw [ZA_lower a b 3 h3, ZA_lower_ne a b 3 2 (by decide), mul_left_comm]
  · rw [PA_lower_ne a b 3 0 (by decide), PA_lower_ne a b 3 1 (by decide),
      PA_lower_ne a b 3 4 (by decide), fact_d4_apply ⟨true, 3, false⟩ ⟨a, b⟩ (by decide) hd]
    ring
  · dsimp only
    rw [cval_lower, Deval_lower, hs, one_mul, mul_one]
    simp only [bq, Fin.prod_univ_five]
    push_cast
    ring

/-- The hypothesis `1 ≤ a_i - 1 - b_j` from the type of the endpoint. -/
theorem lower_hb (a b : Fin 5 → ℤ) (i : Fin 5)
    (h : ∀ j, 1 ≤ (Edge.apply ⟨true, i, false⟩ ⟨a, b⟩).a i -
      (Edge.apply ⟨true, i, false⟩ ⟨a, b⟩).b j) : ∀ j, 1 ≤ a i - 1 - b j := fun j => by
  have := h j
  simp only [Edge.apply, Function.update_self, ite_true, ite_false, Bool.false_eq_true] at this
  exact this

/-- Lowering `a_i` for `i ∈ {0, 1, 4}` (the reverse of a raising step). -/
theorem det_lower_a0 (p : Pt) (hT : Typ p) (hT' : Typ (Edge.apply ⟨true, 0, false⟩ p)) :
    DetFwd ⟨true, 0, false⟩ p := by
  obtain ⟨-, -, -, -, -, hd⟩ := hT
  obtain ⟨h0, -, -, -, -, -⟩ := hT'
  rcases p with ⟨a, b⟩
  have hb := lower_hb a b 0 h0
  have hs : sgn ⟨true, 0, false⟩ = -1 := by simp [sgn]
  refine DetFwd_of_key _ _ hd 1 (∏ j, ((a 0 - b j - 1 : ℤ) : ℚ))
    (Finset.prod_ne_zero_iff.mpr fun j _ => Int.cast_ne_zero.mpr (by have := hb j; omega))
    ?_ ?_ ?_
  · rw [ZA_lower_ne a b 0 2 (by decide), ZA_lower_ne a b 0 3 (by decide), one_mul]
  · rw [PA_lower_ne a b 0 1 (by decide), PA_lower_ne a b 0 4 (by decide),
      fact_d4_apply ⟨true, 0, false⟩ ⟨a, b⟩ (by decide) hd, PA_lower a b 0 hb]
    ring
  · dsimp only
    rw [cval_lower, Deval_lower, hs, one_mul]
    simp only [bq, Fin.prod_univ_five]
    push_cast
    ring

theorem det_lower_a1 (p : Pt) (hT : Typ p) (hT' : Typ (Edge.apply ⟨true, 1, false⟩ p)) :
    DetFwd ⟨true, 1, false⟩ p := by
  obtain ⟨-, -, -, -, -, hd⟩ := hT
  obtain ⟨-, h1, -, -, -, -⟩ := hT'
  rcases p with ⟨a, b⟩
  have hb := lower_hb a b 1 h1
  have hs : sgn ⟨true, 1, false⟩ = -1 := by simp [sgn]
  refine DetFwd_of_key _ _ hd 1 (∏ j, ((a 1 - b j - 1 : ℤ) : ℚ))
    (Finset.prod_ne_zero_iff.mpr fun j _ => Int.cast_ne_zero.mpr (by have := hb j; omega))
    ?_ ?_ ?_
  · rw [ZA_lower_ne a b 1 2 (by decide), ZA_lower_ne a b 1 3 (by decide), one_mul]
  · rw [PA_lower_ne a b 1 0 (by decide), PA_lower_ne a b 1 4 (by decide),
      fact_d4_apply ⟨true, 1, false⟩ ⟨a, b⟩ (by decide) hd, PA_lower a b 1 hb]
    ring
  · dsimp only
    rw [cval_lower, Deval_lower, hs, one_mul]
    simp only [bq, Fin.prod_univ_five]
    push_cast
    ring

theorem det_lower_a4 (p : Pt) (hT : Typ p) (hT' : Typ (Edge.apply ⟨true, 4, false⟩ p)) :
    DetFwd ⟨true, 4, false⟩ p := by
  obtain ⟨-, -, -, -, -, hd⟩ := hT
  obtain ⟨-, -, h4, -, -, -⟩ := hT'
  rcases p with ⟨a, b⟩
  have hb := lower_hb a b 4 h4
  have hs : sgn ⟨true, 4, false⟩ = -1 := by simp [sgn]
  refine DetFwd_of_key _ _ hd 1 (∏ j, ((a 4 - b j - 1 : ℤ) : ℚ))
    (Finset.prod_ne_zero_iff.mpr fun j _ => Int.cast_ne_zero.mpr (by have := hb j; omega))
    ?_ ?_ ?_
  · rw [ZA_lower_ne a b 4 2 (by decide), ZA_lower_ne a b 4 3 (by decide), one_mul]
  · rw [PA_lower_ne a b 4 0 (by decide), PA_lower_ne a b 4 1 (by decide),
      fact_d4_apply ⟨true, 4, false⟩ ⟨a, b⟩ (by decide) hd, PA_lower a b 4 hb]
    ring
  · dsimp only
    rw [cval_lower, Deval_lower, hs, one_mul]
    simp only [bq, Fin.prod_univ_five]
    push_cast
    ring

/-- Raising `b_j`. -/
theorem det_raise_b (j : Fin 5) (p : Pt) (hT : Typ p) (hT' : Typ (Edge.apply ⟨false, j, true⟩ p)) :
    DetFwd ⟨false, j, true⟩ p := by
  obtain ⟨-, -, -, h2, h3, hd⟩ := hT
  obtain ⟨h0, h1, h4, -, -, -⟩ := hT'
  rcases p with ⟨a, b⟩
  have hb : ∀ i, 1 ≤ (Edge.apply ⟨false, j, true⟩ ⟨a, b⟩).a i -
      (Edge.apply ⟨false, j, true⟩ ⟨a, b⟩).b j → 1 ≤ a i - (b j + 1) := fun i h => by
    simp only [Edge.apply, Function.update_self, ite_true, ite_false, Bool.false_eq_true] at h
    exact h
  have hb0 := hb 0 (h0 j)
  have hb1 := hb 1 (h1 j)
  have hb4 := hb 4 (h4 j)
  have hs : sgn ⟨false, j, true⟩ = -1 := by simp [sgn]
  refine DetFwd_of_key _ _ hd ((((b j - a 2 : ℤ) : ℚ) + 1) * (((b j - a 3 : ℤ) : ℚ) + 1))
    (((a 0 - b j - 1 : ℤ) : ℚ) * ((a 1 - b j - 1 : ℤ) : ℚ) * ((a 4 - b j - 1 : ℤ) : ℚ))
    (mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr (by omega)) (Int.cast_ne_zero.mpr (by omega)))
      (Int.cast_ne_zero.mpr (by omega))) ?_ ?_ ?_
  · rw [ZA_raise a b j 2 (h2 j), ZA_raise a b j 3 (h3 j)]
    ring
  · rw [fact_d4_apply ⟨false, j, true⟩ ⟨a, b⟩ Bool.false_ne_true hd, PA_raise a b j 0 hb0,
      PA_raise a b j 1 hb1, PA_raise a b j 4 hb4]
    ring
  · dsimp only
    rw [cval_raise, Deval_raise, hs]
    simp only [al, Fin.prod_univ_five]
    push_cast
    ring

/-- The determinant across any forward edge. -/
theorem det_fwd (e : Edge) (hf : e.fwd) (p : Pt) (hT : Typ p) (hT' : Typ (e.apply p)) :
    DetFwd e p := by
  rcases e with ⟨isA, i, up⟩
  cases isA <;> cases up <;> simp only [Edge.fwd, ne_eq, not_true_eq_false, not_false_eq_true,
    Bool.false_eq_true, Bool.true_eq_false] at hf
  · exact det_raise_b i p hT hT'
  · fin_cases i
    · exact det_lower_a0 p hT hT'
    · exact det_lower_a1 p hT hT'
    · exact det_lower_a2 p hT
    · exact det_lower_a3 p hT
    · exact det_lower_a4 p hT hT'

/-- **The determinant across any edge of the walk.** -/
theorem det_edge (e : Edge) (p : Pt) (hT : Typ p) (hT' : Typ (e.apply p))
    (hd : (e.src p).dc 4 ≠ 0) (hinv : ¬ e.fwd → Deval (e.src p).a (e.src p).b (e.cval p) ≠ 0) :
    (e.mat p).det = sgn e * Vpot (e.apply p) / Vpot p := by
  by_cases hf : e.fwd
  · have hs : e.src p = p := ite_eq_left hf
    rw [Edge.mat, ite_eq_left hf, hs]
    exact det_fwd e hf p hT hT'
  · have hs : e.src p = e.apply p := ite_eq_right hf
    rw [hs] at hd hinv
    have hdf : e.dual.fwd := (Edge.dual_fwd e).mpr hf
    have key := det_fwd e.dual hdf (e.apply p) hT' (by rw [Edge.dual_apply_apply]; exact hT)
    unfold DetFwd at key
    rw [Edge.dual_apply_apply, Edge.cval_dual_apply, sgn_dual] at key
    rw [Edge.mat, ite_eq_right hf, hs, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', key]
    have h1 := Vpot_ne_zero p
    have h2 := Vpot_ne_zero (e.apply p)
    have h3 := sgn_sq e
    have hs0 : sgn e ≠ 0 := fun h => by rw [h, zero_mul] at h3; exact zero_ne_one h3
    rw [inv_div, div_eq_div_iff (mul_ne_zero hs0 h1) h1]
    linear_combination (-(Vpot (e.apply p) * Vpot p)) * h3

/-! ### Along the walk -/

theorem Typ_toPt_A (N : ℕ) (o : Off) (ho : AShape o) (hd : 0 ≤ d4o o) : Typ (o.toPt N) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ho
  unfold d4o at hd
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩ <;>
    (try fin_cases j) <;> simp only [d4] <;> coord_simp <;> omega

theorem Typ_toPt_B (N : ℕ) (o : Off) (ho : BShape o) (hd : 0 ≤ d4o o) : Typ (o.toPt N) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ho
  unfold d4o at hd
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩ <;>
    (try fin_cases j) <;> simp only [d4] <;> coord_simp <;> omega

theorem Typ_vtx (N t : ℕ) (ht : t ≤ 72) : Typ (vtx N t) := by
  by_cases h : t ≤ 66
  · exact Typ_toPt_A N _ (ashape_off t h) (d4o_off t ht).1
  · exact Typ_toPt_B N _ (bshape_off t (by omega) ht) (d4o_off t ht).1

/-- The invertibility hypothesis of `det_edge` along the original walk. -/
theorem inv_walk (N t : ℕ) (ht : t < 72) (hf : ¬ (edge t).fwd) :
    Deval ((edge t).apply (vtx N t)).a ((edge t).apply (vtx N t)).b ((edge t).cval (vtx N t)) ≠ 0 := by
  by_cases h : t < 66
  · obtain ⟨hA, -, hra⟩ := edge_a t h
    rw [fwd_iff_up_false _ hA] at hf
    have hu : (edge t).up = true := by cases hu : (edge t).up <;> simp_all
    exact inv_orig_a N _ (ashape_off t (by omega)) _ hA hu (hra hu)
  · obtain ⟨hA, -, hlo⟩ := edge_b t (by omega) ht
    rw [fwd_iff_up_true _ hA] at hf
    have hu : (edge t).up = false := by cases hu : (edge t).up <;> simp_all
    exact inv_orig_b N _ (bshape_off t (by omega) (by omega)) _ hA hu (hlo hu)

theorem det_edge_walk (N t : ℕ) (ht : t < 72) :
    ((edge t).mat (vtx N t)).det = sgn (edge t) * Vpot (vtx N (t + 1)) / Vpot (vtx N t) := by
  rw [vtx_succ N t ht]
  refine det_edge _ _ (Typ_vtx N t (by omega)) (by rw [← vtx_succ N t ht]; exact Typ_vtx N _ ht)
    ?_ fun hf => ?_
  · rw [src_eq]; split_ifs
    · exact dc4_vtx N t (by omega)
    · rw [← vtx_succ N t ht]; exact dc4_vtx N (t + 1) ht
  · have hs : (edge t).src (vtx N t) = (edge t).apply (vtx N t) := ite_eq_right hf
    rw [hs]; exact inv_walk N t ht hf

/-- The product of the signs along the walk. -/
def sgnProd (T : ℕ) : ℚ := ((List.range T).map fun t => sgn (edge t)).prod

theorem det_wmat_walk (N T : ℕ) (hT : T ≤ 72) :
    (wmat edge (vtx N) T).det = sgnProd T * Vpot (vtx N T) / Vpot (vtx N 0) := by
  induction T with
  | zero => rw [wmat_zero, Matrix.det_one, sgnProd, List.range_zero, List.map_nil, List.prod_nil,
      one_mul, div_self (Vpot_ne_zero _)]
  | succ T ih =>
    rw [wmat_succ, Matrix.det_mul, ih (by omega), det_edge_walk N T (by omega), sgnProd, sgnProd,
      List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    have := Vpot_ne_zero (vtx N T)
    field_simp
    try ring

/-- The sign of the walk is `-1`: 33 lowerings of `a₂, a₃` and 39 other steps. -/
theorem sgnProd_72 : sgnProd 72 = -1 := by
  have h : ((List.range 72).map fun t => (if (edge t).isA ∧ ((edge t).i = 2 ∨ (edge t).i = 3)
      then (1 : ℤ) else -1)).prod = -1 := by decide
  unfold sgnProd sgn
  have hc : ((List.range 72).map fun t => (if (edge t).isA ∧ ((edge t).i = 2 ∨ (edge t).i = 3)
      then (1 : ℚ) else -1)).prod =
      (((List.range 72).map fun t => (if (edge t).isA ∧ ((edge t).i = 2 ∨ (edge t).i = 3)
        then (1 : ℤ) else -1)).prod : ℤ) := by
    rw [Int.cast_list_prod, List.map_map]
    congr 1 <;> (try (funext t; simp only [Function.comp_apply]; split_ifs <;> simp))
  rw [hc, h]; try norm_num

/-- **`det W_N = -V(p_{N+1})/V(p_N)`.** -/
theorem det_Wmat (N : ℕ) : (Wmat N).det = -(Vpot (pN (N + 1)) / Vpot (pN N)) := by
  rw [Wmat, det_wmat_walk N 72 le_rfl, sgnProd_72, vtx_72, vtx_zero]; ring

/-! ### `V(p_N) = F_N` -/

theorem fact_natCast (n : ℕ) : fact (n : ℤ) = (n.factorial : ℚ) := by
  unfold fact; rw [Int.toNat_natCast]

/-- **`V(p_N) = F_N`.** -/
theorem Vpot_pN (N : ℕ) : Vpot (pN N) = F N := by
  have e : ∀ (c : ℤ) (n : ℕ), c = n → fact c = (n.factorial : ℚ) := fun c n h => by
    rw [h, fact_natCast]
  rw [Vpot, ZA, ZA, PA, PA, PA, d4, pN]
  coord_simp
  rw [e _ (16 * N) (by push_cast; ring), e _ (17 * N) (by push_cast; ring),
    e _ (18 * N) (by push_cast; ring), e _ (15 * N) (by push_cast; ring),
    e _ (14 * N) (by push_cast; ring), e _ (17 * N) (by push_cast; ring),
    e _ (18 * N) (by push_cast; ring), e _ (19 * N) (by push_cast; ring),
    e _ (16 * N) (by push_cast; ring), e _ (15 * N) (by push_cast; ring),
    e _ (11 * N) (by push_cast; ring), e _ (10 * N) (by push_cast; ring),
    e _ (9 * N) (by push_cast; ring), e _ (12 * N) (by push_cast; ring),
    e _ (13 * N) (by push_cast; ring), e _ (12 * N) (by push_cast; ring),
    e _ (11 * N) (by push_cast; ring), e _ (10 * N) (by push_cast; ring),
    e _ (13 * N) (by push_cast; ring), e _ (14 * N) (by push_cast; ring),
    e _ (10 * N + 1) (by push_cast; ring), e _ (9 * N + 1) (by push_cast; ring),
    e _ (8 * N + 1) (by push_cast; ring), e _ (11 * N + 1) (by push_cast; ring),
    e _ (12 * N + 1) (by push_cast; ring), e _ 0 (by push_cast; ring)]
  simp only [F, listA, listB, listE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Nat.factorial_zero, Nat.cast_one]
  ring

end ZetasIrr.CMF
