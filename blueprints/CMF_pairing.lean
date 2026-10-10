/-
# CMF transport, part 3: the concomitant matrix and the pairing identity

`Jm a b` is the Lagrange concomitant `J` of the PDF (Part VII §2 and `verify_pairing.py`), written
in terms of the elementary symmetric functions `E_k = e_k(α)`, `F_k = e_k(b)` of `α_i = a_i - 1`
and of `b_j`. It satisfies, for every forward edge `s → u` (`ker u = (t + c) ker s`) and the
corresponding dual edge (`ker (dual s) = (t + c*) ker (dual u)`), the exact identity
  `A(s, c) · J(u) = -J(s) · A(dual u, c*)ᵀ`
(`pair_fwd`). This is the generic identity certified symbolically in `verify_pairing.py`; it is
proved here as two polynomial identities (`pair_a_gen`, `pair_b_gen`) in the symmetric functions
of the four parameters that do not move and the one that does. Across any edge one gets
`M · J(end) · M*ᵀ = -J(start)` (`edge_pairing`), and multiplying along a walk gives
`W · J(end) · Dᵀ = (-1)^T J(start)` (`walk_pairing`).
-/
import CMF_transport

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-! ### Symmetric data -/

/-- `(0, e₁ v, …, e₅ v)`. -/
def eS (v : Fin 5 → ℚ) : Fin 6 → ℚ := fun k =>
  if k = 1 then e1 v else if k = 2 then e2 v else if k = 3 then e3 v else if k = 4 then e4 v
  else if k = 5 then e5 v else 0

/-- The `D`-coefficients from symmetric data. -/
def dcE (E F : Fin 6 → ℚ) : Fin 5 → ℚ := fun k =>
  if k = 0 then F 5 - E 5 else if k = 1 then E 4 - F 4 else if k = 2 then F 3 - E 3
  else if k = 3 then E 2 - F 2 else F 1 - E 1

/-- The concomitant matrix from symmetric data. -/
def JmE (E F : Fin 6 → ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![E 1 + E 2 + E 3 + E 4 - F 4 + 1, 3 * E 1 + 2 * E 2 + E 3 - F 3 + 4, 3 * E 1 + E 2 - F 2 + 6,
      E 1 - F 1 + 4;
    -E 1 - E 2 - E 3 + F 3 - 1, -2 * E 1 - E 2 + F 2 - 3, -E 1 + F 1 - 3, 0;
    E 1 + E 2 - F 2 + 1, E 1 - F 1 + 2, 0, 0;
    -E 1 + F 1 - 1, 0, 0, 0]

/-- The concomitant matrix of a point. -/
def Jm (a b : Fin 5 → ℤ) : Matrix (Fin 4) (Fin 4) ℚ := JmE (eS (al a)) (eS (bq b))

theorem dc_eq (a b : Fin 5 → ℤ) : dc a b = dcE (eS (al a)) (eS (bq b)) := by
  funext k; fin_cases k <;> rfl

/-- `d₄ · Amat d c`, a matrix with polynomial entries. -/
def Am (d : Fin 5 → ℚ) (c : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![c * d 4, 0, 0, d 0; -d 4, c * d 4, 0, d 1; 0, -d 4, c * d 4, d 2; 0, 0, -d 4, c * d 4 + d 3]

theorem Amat_eq (d : Fin 5 → ℚ) (c : ℚ) (hd : d 4 ≠ 0) : Amat d c = (d 4)⁻¹ • Am d c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Amat, Am] <;> field_simp

/-- Elementary symmetric functions of four variables. -/
def f1 (w : Fin 4 → ℚ) : ℚ := w 0 + w 1 + w 2 + w 3
def f2 (w : Fin 4 → ℚ) : ℚ := w 0 * w 1 + w 0 * w 2 + w 0 * w 3 + w 1 * w 2 + w 1 * w 3 + w 2 * w 3
def f3 (w : Fin 4 → ℚ) : ℚ := w 0 * w 1 * w 2 + w 0 * w 1 * w 3 + w 0 * w 2 * w 3 + w 1 * w 2 * w 3
def f4 (w : Fin 4 → ℚ) : ℚ := w 0 * w 1 * w 2 * w 3

/-- `(0, f₁ w, …, f₄ w, 0)`. -/
def oS (w : Fin 4 → ℚ) : Fin 6 → ℚ := fun k =>
  if k = 1 then f1 w else if k = 2 then f2 w else if k = 3 then f3 w else if k = 4 then f4 w
  else 0

/-- The symmetric functions of `(r, w)` from those of `w`: `e_k = o_k + r o_{k-1}`. -/
def Es (o : Fin 6 → ℚ) (r : ℚ) : Fin 6 → ℚ := fun k =>
  if k = 1 then o 1 + r else if k = 2 then o 2 + r * o 1 else if k = 3 then o 3 + r * o 2
  else if k = 4 then o 4 + r * o 3 else if k = 5 then r * o 4 else 0

/-- The symmetric functions of `-(v + 1)` from those of `v`. -/
def Edual (E : Fin 6 → ℚ) : Fin 6 → ℚ := fun k =>
  if k = 1 then -(E 1 + 5) else if k = 2 then E 2 + 4 * E 1 + 10
  else if k = 3 then -(E 3 + 3 * E 2 + 6 * E 1 + 10)
  else if k = 4 then E 4 + 2 * E 3 + 3 * E 2 + 4 * E 1 + 5
  else if k = 5 then -(E 5 + E 4 + E 3 + E 2 + E 1 + 1) else 0

/-- The symmetric functions of `-v` from those of `v`. -/
def Fdual (F : Fin 6 → ℚ) : Fin 6 → ℚ := fun k =>
  if k = 1 then -F 1 else if k = 2 then F 2 else if k = 3 then -F 3 else if k = 4 then F 4
  else if k = 5 then -F 5 else 0

/-- The four coordinates of `v` other than `v i`. -/
def others (i : Fin 5) (v : Fin 5 → ℚ) : Fin 4 → ℚ :=
  if i = 0 then ![v 1, v 2, v 3, v 4] else if i = 1 then ![v 0, v 2, v 3, v 4]
  else if i = 2 then ![v 0, v 1, v 3, v 4] else if i = 3 then ![v 0, v 1, v 2, v 4]
  else ![v 0, v 1, v 2, v 3]


/-! ### Equation lemmas for the symmetric data (avoid unfolding `if`-chains inside `simp`) -/

theorem eS_0 (v : Fin 5 → ℚ) : eS v 0 = 0 := by simp only [eS, Fin.reduceEq, ite_true, ite_false]
theorem eS_1 (v : Fin 5 → ℚ) : eS v 1 = e1 v := by simp only [eS, Fin.reduceEq, ite_true, ite_false]
theorem eS_2 (v : Fin 5 → ℚ) : eS v 2 = e2 v := by simp only [eS, Fin.reduceEq, ite_true, ite_false]
theorem eS_3 (v : Fin 5 → ℚ) : eS v 3 = e3 v := by simp only [eS, Fin.reduceEq, ite_true, ite_false]
theorem eS_4 (v : Fin 5 → ℚ) : eS v 4 = e4 v := by simp only [eS, Fin.reduceEq, ite_true, ite_false]
theorem eS_5 (v : Fin 5 → ℚ) : eS v 5 = e5 v := by simp only [eS, Fin.reduceEq, ite_true, ite_false]

theorem dcE_0 (E F : Fin 6 → ℚ) : dcE E F 0 = F 5 - E 5 := by
  simp only [dcE, Fin.reduceEq, ite_true, ite_false]
theorem dcE_1 (E F : Fin 6 → ℚ) : dcE E F 1 = E 4 - F 4 := by
  simp only [dcE, Fin.reduceEq, ite_true, ite_false]
theorem dcE_2 (E F : Fin 6 → ℚ) : dcE E F 2 = F 3 - E 3 := by
  simp only [dcE, Fin.reduceEq, ite_true, ite_false]
theorem dcE_3 (E F : Fin 6 → ℚ) : dcE E F 3 = E 2 - F 2 := by
  simp only [dcE, Fin.reduceEq, ite_true, ite_false]
theorem dcE_4 (E F : Fin 6 → ℚ) : dcE E F 4 = F 1 - E 1 := by
  simp only [dcE, Fin.reduceEq, ite_true, ite_false]

theorem oS_0 (w : Fin 4 → ℚ) : oS w 0 = 0 := by simp only [oS, Fin.reduceEq, ite_true, ite_false]
theorem oS_1 (w : Fin 4 → ℚ) : oS w 1 = f1 w := by simp only [oS, Fin.reduceEq, ite_true, ite_false]
theorem oS_2 (w : Fin 4 → ℚ) : oS w 2 = f2 w := by simp only [oS, Fin.reduceEq, ite_true, ite_false]
theorem oS_3 (w : Fin 4 → ℚ) : oS w 3 = f3 w := by simp only [oS, Fin.reduceEq, ite_true, ite_false]
theorem oS_4 (w : Fin 4 → ℚ) : oS w 4 = f4 w := by simp only [oS, Fin.reduceEq, ite_true, ite_false]
theorem oS_5 (w : Fin 4 → ℚ) : oS w 5 = 0 := by simp only [oS, Fin.reduceEq, ite_true, ite_false]

theorem Es_0 (o : Fin 6 → ℚ) (r : ℚ) : Es o r 0 = 0 := by
  simp only [Es, Fin.reduceEq, ite_true, ite_false]
theorem Es_1 (o : Fin 6 → ℚ) (r : ℚ) : Es o r 1 = o 1 + r := by
  simp only [Es, Fin.reduceEq, ite_true, ite_false]
theorem Es_2 (o : Fin 6 → ℚ) (r : ℚ) : Es o r 2 = o 2 + r * o 1 := by
  simp only [Es, Fin.reduceEq, ite_true, ite_false]
theorem Es_3 (o : Fin 6 → ℚ) (r : ℚ) : Es o r 3 = o 3 + r * o 2 := by
  simp only [Es, Fin.reduceEq, ite_true, ite_false]
theorem Es_4 (o : Fin 6 → ℚ) (r : ℚ) : Es o r 4 = o 4 + r * o 3 := by
  simp only [Es, Fin.reduceEq, ite_true, ite_false]
theorem Es_5 (o : Fin 6 → ℚ) (r : ℚ) : Es o r 5 = r * o 4 := by
  simp only [Es, Fin.reduceEq, ite_true, ite_false]

theorem Edual_0 (E : Fin 6 → ℚ) : Edual E 0 = 0 := by
  simp only [Edual, Fin.reduceEq, ite_true, ite_false]
theorem Edual_1 (E : Fin 6 → ℚ) : Edual E 1 = -(E 1 + 5) := by
  simp only [Edual, Fin.reduceEq, ite_true, ite_false]
theorem Edual_2 (E : Fin 6 → ℚ) : Edual E 2 = E 2 + 4 * E 1 + 10 := by
  simp only [Edual, Fin.reduceEq, ite_true, ite_false]
theorem Edual_3 (E : Fin 6 → ℚ) : Edual E 3 = -(E 3 + 3 * E 2 + 6 * E 1 + 10) := by
  simp only [Edual, Fin.reduceEq, ite_true, ite_false]
theorem Edual_4 (E : Fin 6 → ℚ) : Edual E 4 = E 4 + 2 * E 3 + 3 * E 2 + 4 * E 1 + 5 := by
  simp only [Edual, Fin.reduceEq, ite_true, ite_false]
theorem Edual_5 (E : Fin 6 → ℚ) : Edual E 5 = -(E 5 + E 4 + E 3 + E 2 + E 1 + 1) := by
  simp only [Edual, Fin.reduceEq, ite_true, ite_false]

theorem Fdual_0 (F : Fin 6 → ℚ) : Fdual F 0 = 0 := by
  simp only [Fdual, Fin.reduceEq, ite_true, ite_false]
theorem Fdual_1 (F : Fin 6 → ℚ) : Fdual F 1 = -F 1 := by
  simp only [Fdual, Fin.reduceEq, ite_true, ite_false]
theorem Fdual_2 (F : Fin 6 → ℚ) : Fdual F 2 = F 2 := by
  simp only [Fdual, Fin.reduceEq, ite_true, ite_false]
theorem Fdual_3 (F : Fin 6 → ℚ) : Fdual F 3 = -F 3 := by
  simp only [Fdual, Fin.reduceEq, ite_true, ite_false]
theorem Fdual_4 (F : Fin 6 → ℚ) : Fdual F 4 = F 4 := by
  simp only [Fdual, Fin.reduceEq, ite_true, ite_false]
theorem Fdual_5 (F : Fin 6 → ℚ) : Fdual F 5 = -F 5 := by
  simp only [Fdual, Fin.reduceEq, ite_true, ite_false]

macro "sym_simp" : tactic => `(tactic|
  simp only [eS_0, eS_1, eS_2, eS_3, eS_4, eS_5, oS_0, oS_1, oS_2, oS_3, oS_4, oS_5,
    Es_0, Es_1, Es_2, Es_3, Es_4, Es_5, Edual_0, Edual_1, Edual_2, Edual_3, Edual_4, Edual_5,
    Fdual_0, Fdual_1, Fdual_2, Fdual_3, Fdual_4, Fdual_5, others, e1, e2, e3, e4, e5, f1, f2, f3, f4,
    Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ite_true, ite_false,
    Fin.reduceEq, neg_add_rev])

theorem eS_split (v : Fin 5 → ℚ) (i : Fin 5) : eS v = Es (oS (others i v)) (v i) := by
  fin_cases i <;> funext k <;> fin_cases k <;> sym_simp <;> ring

theorem others_update (i : Fin 5) (v : Fin 5 → ℚ) (x : ℚ) :
    others i (Function.update v i x) = others i v := by
  fin_cases i <;> funext k <;> fin_cases k <;> sym_simp

theorem eS_neg_succ (w : Fin 5 → ℚ) : eS (fun i => -(w i + 1)) = Edual (eS w) := by
  funext k; fin_cases k <;> sym_simp <;> ring

theorem eS_neg (w : Fin 5 → ℚ) : eS (fun i => -w i) = Fdual (eS w) := by
  funext k; fin_cases k <;> sym_simp <;> ring

/-! ### The generic identities -/

macro "pair_simp" : tactic => `(tactic|
  simp only [Am, JmE, dcE_0, dcE_1, dcE_2, dcE_3, dcE_4, Es_1, Es_2, Es_3, Es_4, Es_5,
    Edual_1, Edual_2, Edual_3, Edual_4, Edual_5, Fdual_1, Fdual_2, Fdual_3, Fdual_4, Fdual_5,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val, smul_eq_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.reduceEq, ite_true, ite_false])

/-- Lowering the parameter `r = α_i` by one. -/
theorem pair_a_gen (o : Fin 6 → ℚ) (r : ℚ) (F : Fin 6 → ℚ) :
    dcE (Edual (Es o (r - 1))) (Fdual F) 4 • (Am (dcE (Es o r) F) r * JmE (Es o (r - 1)) F) +
      dcE (Es o r) F 4 •
        (JmE (Es o r) F * (Am (dcE (Edual (Es o (r - 1))) (Fdual F)) (-r))ᵀ) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> pair_simp <;> ring

set_option maxHeartbeats 4000000 in
/-- Raising the parameter `s = b_j` by one. -/
theorem pair_b_gen (E : Fin 6 → ℚ) (q : Fin 6 → ℚ) (s : ℚ) :
    dcE (Edual E) (Fdual (Es q (s + 1))) 4 • (Am (dcE E (Es q s)) s * JmE E (Es q (s + 1))) +
      dcE E (Es q s) 4 •
        (JmE E (Es q s) * (Am (dcE (Edual E) (Fdual (Es q (s + 1)))) (-s - 1))ᵀ) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> pair_simp <;> ring

/-! ### The identity across an edge -/

theorem smul_combine {M N : Matrix (Fin 4) (Fin 4) ℚ} {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y • M + x • N = 0) : x⁻¹ • M = -(y⁻¹ • N) := by
  rw [eq_neg_iff_add_eq_zero]
  have := congrArg (fun Z => (x * y)⁻¹ • Z) h
  simp only [smul_add, smul_smul, smul_zero] at this
  rw [show (x * y)⁻¹ * y = x⁻¹ by field_simp, show (x * y)⁻¹ * x = y⁻¹ by field_simp] at this
  exact this

theorem Pt.dual_a' (p : Pt) : p.dual.a = fun i => 1 - p.a i := rfl
theorem Pt.dual_b' (p : Pt) : p.dual.b = fun j => -p.b j := rfl

theorem al_update_sub (a : Fin 5 → ℤ) (i : Fin 5) :
    al (Function.update a i (a i - 1)) = Function.update (al a) i (al a i - 1) := by
  funext j; by_cases h : j = i
  · subst h; simp only [al, Function.update_self]; push_cast; ring
  · simp only [al, Function.update_of_ne h]

theorem al_dual_update (a : Fin 5 → ℤ) (i : Fin 5) :
    al (fun j => 1 - Function.update a i (a i - 1) j) =
      fun j => -(Function.update (al a) i (al a i - 1) j + 1) := by
  funext j; by_cases h : j = i
  · subst h; simp only [al, Function.update_self]; push_cast; ring
  · simp only [al, Function.update_of_ne h]; push_cast; ring

theorem bq_update_add (b : Fin 5 → ℤ) (j : Fin 5) :
    bq (Function.update b j (b j + 1)) = Function.update (bq b) j (bq b j + 1) := by
  funext k; by_cases h : k = j
  · subst h; simp only [bq, Function.update_self]; push_cast; ring
  · simp only [bq, Function.update_of_ne h]

theorem bq_neg (b : Fin 5 → ℤ) : bq (fun j => -b j) = fun j => -bq b j := by
  funext j; simp only [bq]; push_cast; ring

theorem al_dual (a : Fin 5 → ℤ) : al (fun i => 1 - a i) = fun i => -(al a i + 1) := by
  funext i; simp only [al]; push_cast; ring

/-- **The pairing identity across a forward edge** `p → e.apply p`. -/
theorem pair_fwd (e : Edge) (hf : e.fwd) (p : Pt) (hd : p.dc 4 ≠ 0)
    (hd' : (e.apply p).dual.dc 4 ≠ 0) :
    Amat p.dc (e.cval p) * Jm (e.apply p).a (e.apply p).b =
      -(Jm p.a p.b * (Amat (e.apply p).dual.dc (e.dual.cval p.dual))ᵀ) := by
  rw [Amat_eq _ _ hd, Amat_eq _ _ hd', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  apply smul_combine hd hd'
  rcases e with ⟨isA, i, up⟩
  rcases p with ⟨a, b⟩
  cases isA <;> cases up <;> simp only [Edge.fwd, ne_eq, not_true_eq_false, not_false_eq_true,
    Bool.false_eq_true, Bool.true_eq_false] at hf
  · -- raise `b_i`
    simp only [Edge.apply, Edge.cval, Edge.dual, Pt.dual_a', Pt.dual_b', Pt.dc, Bool.false_eq_true,
      Bool.true_eq_false, ite_false, ite_true, Bool.not_true, sub_zero, Jm, dc_eq, bq_update_add,
      al_dual, bq_neg, eS_neg_succ, eS_neg]
    rw [eS_split (bq b) i, eS_split (Function.update (bq b) i (bq b i + 1)) i, others_update,
      Function.update_self]
    have h1 : ((b i : ℤ) : ℚ) = bq b i := rfl
    have h2 : ((-b i - 1 : ℤ) : ℚ) = -(bq b i) - 1 := by simp only [bq]; push_cast; ring
    rw [h1, h2]
    exact pair_b_gen _ _ _
  · -- lower `a_i`
    simp only [Edge.apply, Edge.cval, Edge.dual, Pt.dual_a', Pt.dual_b', Pt.dc, ite_false,
      ite_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, sub_zero, Jm, dc_eq,
      al_update_sub, al_dual_update, bq_neg, eS_neg_succ, eS_neg]
    rw [eS_split (al a) i, eS_split (Function.update (al a) i (al a i - 1)) i, others_update,
      Function.update_self]
    have h1 : ((a i - 1 : ℤ) : ℚ) = al a i := by simp only [al]; push_cast; ring
    have h2 : ((1 - a i : ℤ) : ℚ) = -(al a i) := by simp only [al]; push_cast; ring
    rw [h1, h2]
    exact pair_a_gen _ _ _

theorem Edge.dual_dual (e : Edge) : e.dual.dual = e := by
  rcases e with ⟨isA, i, up⟩; simp [Edge.dual]

theorem Edge.dual_apply_apply (e : Edge) (p : Pt) : e.dual.apply (e.apply p) = p := by
  rcases e with ⟨isA, i, up⟩; rcases p with ⟨a, b⟩
  cases isA <;> cases up <;>
    simp [Edge.apply, Edge.dual, Function.update_idem, Function.update_eq_self]

theorem Edge.cval_dual_apply (e : Edge) (p : Pt) : e.dual.cval (e.apply p) = e.cval p := by
  rcases e with ⟨isA, i, up⟩; rcases p with ⟨a, b⟩
  cases isA <;> cases up <;> simp [Edge.apply, Edge.dual, Edge.cval]

/-- The hypotheses for the pairing identity across the edge `e` at `p`. -/
def Edge.pok (e : Edge) (p : Pt) : Prop :=
  (e.src p).dc 4 ≠ 0 ∧ (e.dual.src p.dual).dc 4 ≠ 0 ∧
    (¬ e.fwd → Deval (e.src p).a (e.src p).b (e.cval p) ≠ 0) ∧
    (¬ e.dual.fwd → Deval (e.dual.src p.dual).a (e.dual.src p.dual).b (e.dual.cval p.dual) ≠ 0)

/-- **The pairing identity across any edge.** -/
theorem edge_pairing (e : Edge) (p : Pt) (h : e.pok p) :
    e.mat p * Jm (e.apply p).a (e.apply p).b * (e.dual.mat p.dual)ᵀ = -Jm p.a p.b := by
  obtain ⟨hd, hd', hinv, hinv'⟩ := h
  by_cases hf : e.fwd
  · have hdf : ¬ e.dual.fwd := fun h => (Edge.dual_fwd e).mp h hf
    have hs : e.src p = p := if_pos hf
    have hs' : e.dual.src p.dual = (e.apply p).dual := by
      rw [Edge.src, if_neg hdf, Edge.dual_apply]
    rw [hs] at hd
    rw [hs'] at hd' hinv'
    have hU : IsUnit (Amat (e.apply p).dual.dc (e.dual.cval p.dual)).det :=
      isUnit_det_Amat _ _ _ hd' (hinv' hdf)
    rw [Edge.mat, if_pos hf, hs, Edge.mat, if_neg hdf, hs', pair_fwd e hf p hd hd', Matrix.neg_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.transpose_one,
      Matrix.mul_one]
  · have hdf : e.dual.fwd := (Edge.dual_fwd e).mpr hf
    have hs : e.src p = e.apply p := if_neg hf
    have hs' : e.dual.src p.dual = p.dual := if_pos hdf
    rw [hs] at hd hinv
    rw [hs'] at hd'
    have hU : IsUnit (Amat (e.apply p).dc (e.cval p)).det := isUnit_det_Amat _ _ _ hd (hinv hf)
    have key := pair_fwd e.dual hdf (e.apply p) hd (by rw [Edge.dual_apply_apply]; exact hd')
    rw [Edge.dual_apply_apply, Edge.cval_dual_apply, Edge.dual_dual,
      show e.cval (e.apply p).dual = e.dual.cval p.dual by
        rw [← Edge.cval_dual_apply e.dual p.dual, Edge.dual_dual, Edge.dual_apply]] at key
    rw [Edge.mat, if_neg hf, hs, Edge.mat, if_pos hdf, hs', Matrix.mul_assoc,
      ← neg_neg (Jm (e.apply p).a (e.apply p).b * _), ← key, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

/-- **The pairing identity along a walk.** -/
theorem walk_pairing (edge : ℕ → Edge) (vtx : ℕ → Pt) (T : ℕ)
    (hv : ∀ t < T, vtx (t + 1) = (edge t).apply (vtx t))
    (hok : ∀ t < T, (edge t).pok (vtx t)) :
    wmat edge vtx T * Jm (vtx T).a (vtx T).b *
      (wmat (fun t => (edge t).dual) (fun t => (vtx t).dual) T)ᵀ =
      ((-1 : ℚ) ^ T) • Jm (vtx 0).a (vtx 0).b := by
  induction T with
  | zero => rw [wmat_zero, wmat_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
      pow_zero, one_smul]
  | succ T ih =>
    have hp := edge_pairing _ _ (hok T (by omega))
    rw [Matrix.mul_assoc] at hp
    rw [wmat_succ, wmat_succ, Matrix.transpose_mul, hv T (by omega),
      Matrix.mul_assoc (wmat edge vtx T), Matrix.mul_assoc (wmat edge vtx T),
      Matrix.mul_assoc ((edge T).mat (vtx T)),
      ← Matrix.mul_assoc (Jm ((edge T).apply (vtx T)).a ((edge T).apply (vtx T)).b),
      ← Matrix.mul_assoc ((edge T).mat (vtx T)), hp, Matrix.neg_mul, Matrix.mul_neg,
      ← Matrix.mul_assoc, ih (fun t ht => hv t (by omega)) (fun t ht => hok t (by omega)),
      pow_succ, mul_neg_one, neg_smul]

end ZetasIrr.CMF
