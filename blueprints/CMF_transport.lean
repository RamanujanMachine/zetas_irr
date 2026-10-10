/-
# CMF transport, part 2: moments, the companion relation and the axis step matrices

For a parameter point `p = (a, b)` with kernel `r = ker a b` and a functional `Φ` satisfying
`IsMom Φ ord`, the four moments are `m_j = Φ_K[(-t)^j r]`, `j = 0..3`.

* `dc a b` are the coefficients of `D(θ) = ∏_i (θ - a_i + 1) - ∏_j (θ - b_j)` (degree `≤ 4`);
  `Dneg_eq` is the identity `D(-t) = ∏_j (t + b_j) - ∏_i (t + a_i - 1)`.
* `companion`: with `g(t) = ∏_j (t + b_j) r(t)` one has `D(-t) r(t) = g(t) - g(t-1)`, so when the
  boundary condition at `K` holds, `∑_k d_k m_k = 0` (this determines the fifth moment `m_4`).
* An edge of the parameter lattice changes one coordinate by `±1`; across it the kernels differ
  by a linear factor `t + c` (`ker_edge`). The moments then transform by the explicit matrix
  `Amat d c` (`step_fwd`) or its inverse (`step_bwd`); `edge_transport` packages both cases,
  and `walk_transport` composes them along a walk given by an edge sequence.
* `det_Amat`: `det (Amat d c) = D(c)/d_4`, with `Deval_eq` the factorized value of `D(c)`.
* `Pt.dual`: the dual point `(1 - a, -b)`; `Edge.dual`: the corresponding dual edge.
-/
import CMF_basic

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-! ### Moments -/

/-- `m_j = Φ_K[(-t)^j r]`. -/
def mom (Φ : ℤ → ℚ⟮X⟯ → FormalZ) (K : ℤ) (r : ℚ⟮X⟯) (j : ℕ) : FormalZ :=
  Φ K ((-RatFunc.X) ^ j * r)

/-- The vector of the first four moments. -/
def mv (Φ : ℤ → ℚ⟮X⟯ → FormalZ) (K : ℤ) (r : ℚ⟮X⟯) : Fin 4 → FormalZ := fun j => mom Φ K r j

/-- Row vector times matrix, for vectors with `FormalZ` entries. -/
def vm (m : Fin 4 → FormalZ) (A : Matrix (Fin 4) (Fin 4) ℚ) : Fin 4 → FormalZ :=
  fun j => ∑ i, A i j • m i

theorem vm_mul (m : Fin 4 → FormalZ) (A B : Matrix (Fin 4) (Fin 4) ℚ) :
    vm (vm m A) B = vm m (A * B) := by
  funext j
  simp only [vm, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem vm_one (m : Fin 4 → FormalZ) : vm m 1 = m := by
  funext j
  simp [vm, Matrix.one_apply]

theorem IsMom.zero {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) : Φ K 0 = 0 := by
  have := hΦ.add K 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem IsMom.sum {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) {ι : Type*}
    (s : Finset ι) (c : ι → ℚ) (f : ι → ℚ⟮X⟯) :
    Φ K (∑ i ∈ s, RatFunc.C (c i) * f i) = ∑ i ∈ s, c i • Φ K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hΦ.zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hΦ.add, hΦ.C_mul, ih]

theorem IsMom.sub {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (f g : ℚ⟮X⟯) :
    Φ K (f - g) = Φ K f - Φ K g := by
  rw [sub_eq_add_neg, hΦ.add, show -g = RatFunc.C (-1) * g by simp, hΦ.C_mul, neg_one_smul,
    sub_eq_add_neg]

/-! ### Elementary symmetric functions and the coefficients of `D` -/

def e1 (v : Fin 5 → ℚ) : ℚ := v 0 + v 1 + v 2 + v 3 + v 4
def e2 (v : Fin 5 → ℚ) : ℚ :=
  v 0 * v 1 + v 0 * v 2 + v 0 * v 3 + v 0 * v 4 + v 1 * v 2 + v 1 * v 3 + v 1 * v 4 + v 2 * v 3 +
    v 2 * v 4 + v 3 * v 4
def e3 (v : Fin 5 → ℚ) : ℚ :=
  v 0 * v 1 * v 2 + v 0 * v 1 * v 3 + v 0 * v 1 * v 4 + v 0 * v 2 * v 3 + v 0 * v 2 * v 4 +
    v 0 * v 3 * v 4 + v 1 * v 2 * v 3 + v 1 * v 2 * v 4 + v 1 * v 3 * v 4 + v 2 * v 3 * v 4
def e4 (v : Fin 5 → ℚ) : ℚ :=
  v 0 * v 1 * v 2 * v 3 + v 0 * v 1 * v 2 * v 4 + v 0 * v 1 * v 3 * v 4 + v 0 * v 2 * v 3 * v 4 +
    v 1 * v 2 * v 3 * v 4
def e5 (v : Fin 5 → ℚ) : ℚ := v 0 * v 1 * v 2 * v 3 * v 4

/-- `α_i = a_i - 1`. -/
def al (a : Fin 5 → ℤ) : Fin 5 → ℚ := fun i => (a i : ℚ) - 1
/-- `b_j` as rationals. -/
def bq (b : Fin 5 → ℤ) : Fin 5 → ℚ := fun j => (b j : ℚ)

/-- The coefficients `d_0, …, d_4` of `D(θ) = ∏_i (θ - α_i) - ∏_j (θ - b_j)`. -/
def dc (a b : Fin 5 → ℤ) : Fin 5 → ℚ :=
  ![e5 (bq b) - e5 (al a), e4 (al a) - e4 (bq b), e3 (bq b) - e3 (al a), e2 (al a) - e2 (bq b),
    e1 (bq b) - e1 (al a)]

theorem fv3 : ((3 : Fin 5) : ℕ) = 3 := rfl
theorem fv4 : ((4 : Fin 5) : ℕ) = 4 := rfl

/-- `D(c)`. -/
def Deval (a b : Fin 5 → ℤ) (c : ℚ) : ℚ :=
  dc a b 0 + dc a b 1 * c + dc a b 2 * c ^ 2 + dc a b 3 * c ^ 3 + dc a b 4 * c ^ 4

theorem Deval_eq (a b : Fin 5 → ℤ) (c : ℚ) :
    Deval a b c = (c - al a 0) * (c - al a 1) * (c - al a 2) * (c - al a 3) * (c - al a 4) -
      (c - bq b 0) * (c - bq b 1) * (c - bq b 2) * (c - bq b 3) * (c - bq b 4) := by
  simp [Deval, dc, e1, e2, e3, e4, e5]
  ring

/-- `d_4 = 5 - ∑ a_i + ∑ b_j`. -/
theorem dc_four (a b : Fin 5 → ℤ) :
    dc a b 4 = 5 - ((a 0 + a 1 + a 2 + a 3 + a 4 : ℤ) : ℚ) + ((b 0 + b 1 + b 2 + b 3 + b 4 : ℤ) : ℚ) := by
  simp [dc, e1, al, bq]
  push_cast; ring

/-- The products `∏_j (X + b_j)` and `∏_i (X + a_i - 1)`. -/
def Bprod (b : Fin 5 → ℤ) : ℚ⟮X⟯ := lf (-b 0) * lf (-b 1) * lf (-b 2) * lf (-b 3) * lf (-b 4)
def Aprod (a : Fin 5 → ℤ) : ℚ⟮X⟯ :=
  lf (1 - a 0) * lf (1 - a 1) * lf (1 - a 2) * lf (1 - a 3) * lf (1 - a 4)

/-- `D(-t) = ∏_j (t + b_j) - ∏_i (t + a_i - 1)`. -/
theorem Dneg_eq (a b : Fin 5 → ℤ) :
    ∑ k : Fin 5, RatFunc.C (dc a b k) * (-RatFunc.X) ^ (k : ℕ) = Bprod b - Aprod a := by
  simp only [Fin.sum_univ_five, Fin.val_zero, Fin.val_one, Fin.val_two, fv3, fv4]
  simp [dc, Bprod, Aprod, lf, e1, e2, e3, e4, e5, al, bq, map_sub, map_add, map_mul, map_neg,
    map_one]
  ring

/-! ### The boundary function and the companion relation -/

/-- The roots `-b_j` of `∏_j (t + b_j)`. -/
def bro (b : Fin 5 → ℤ) : Multiset ℤ := {-b 0, -b 1, -b 2, -b 3, -b 4}

theorem lin_bro (b : Fin 5 → ℤ) (Z P : Multiset ℤ) :
    lin (bro b + Z) P = Bprod b * lin Z P := by
  simp only [bro, Bprod, lf, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
    lin_cons_left]
  ring

theorem lf_laurent (c : ℤ) : RatFunc.laurent (-1 : ℚ) (lf (-c)) = lf (1 - c) := by
  simp only [lf, map_sub, RatFunc.laurent_X, RatFunc.laurent_C, Int.cast_neg, Int.cast_sub,
    Int.cast_one, map_neg, map_one]
  ring

theorem Bprod_laurent (b : Fin 5 → ℤ) :
    RatFunc.laurent (-1 : ℚ) (Bprod b) =
      lf (1 - b 0) * lf (1 - b 1) * lf (1 - b 2) * lf (1 - b 3) * lf (1 - b 4) := by
  simp only [Bprod, map_mul, lf_laurent]

/-- **The companion relation.** If `ker a b = lin Z P`, all poles are `≤ K`, and
`g = ∏_j (t + b_j) ker a b` has a zero of order `≥ ord` at `K` (after cancellation), then
`∑_k d_k Φ_K[(-t)^k r] = 0`. -/
theorem companion {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (a b : Fin 5 → ℤ)
    (K : ℤ) (Z P : Multiset ℤ) (hker : ker a b = lin Z P) (hP : ∀ p ∈ P, p ≤ K)
    (hc : P.count K + ord ≤ (bro b + Z).count K) :
    ∑ k : Fin 5, dc a b k • mom Φ K (ker a b) k = 0 := by
  have hsum : ∑ k : Fin 5, dc a b k • mom Φ K (ker a b) k =
      Φ K (∑ k : Fin 5, RatFunc.C (dc a b k) * ((-RatFunc.X) ^ (k : ℕ) * ker a b)) :=
    (hΦ.sum K _ _ _).symm
  have hg : Bprod b * ker a b = lin (bro b + Z) P := by rw [hker, lin_bro]
  have hg' : Aprod a * ker a b = RatFunc.laurent (-1 : ℚ) (lin (bro b + Z) P) := by
    rw [← hg, map_mul, Bprod_laurent, mul_comm _ (RatFunc.laurent (-1 : ℚ) (ker a b)), ker_laurent,
      mul_comm]
    rfl
  have hre : ∑ k : Fin 5, RatFunc.C (dc a b k) * ((-RatFunc.X) ^ (k : ℕ) * ker a b) =
      (∑ k : Fin 5, RatFunc.C (dc a b k) * (-RatFunc.X) ^ (k : ℕ)) * ker a b := by
    rw [Finset.sum_mul]; simp_rw [mul_assoc]
  rw [hsum, hre, Dneg_eq, sub_mul, hg, hg', hΦ.sub, hΦ.shift K (bro b + Z) P hP hc, sub_self]

/-! ### Axis step matrices -/

/-- The step matrix: if `r' = (t + c) r` and `∑_k d_k m_k(r) = 0`, then `m(r') = m(r) A`. -/
def Amat (d : Fin 5 → ℚ) (c : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![c, 0, 0, d 0 / d 4; -1, c, 0, d 1 / d 4; 0, -1, c, d 2 / d 4; 0, 0, -1, c + d 3 / d 4]

theorem mom_mul_linear {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ)
    (r : ℚ⟮X⟯) (c : ℚ) (j : ℕ) :
    mom Φ K ((RatFunc.X + RatFunc.C c) * r) j = c • mom Φ K r j - mom Φ K r (j + 1) := by
  have h : (-RatFunc.X) ^ j * ((RatFunc.X + RatFunc.C c) * r) =
      RatFunc.C c * ((-RatFunc.X) ^ j * r) + RatFunc.C (-1) * ((-RatFunc.X) ^ (j + 1) * r) := by
    rw [pow_succ, map_neg, map_one]; ring
  rw [mom, h, hΦ.add, hΦ.C_mul, hΦ.C_mul, neg_one_smul, ← sub_eq_add_neg]
  rfl

/-- Forward step: `m((t + c) r) = m(r) · Amat d c`. -/
theorem step_fwd {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (r : ℚ⟮X⟯)
    (d : Fin 5 → ℚ) (hd : d 4 ≠ 0) (c : ℚ)
    (hcomp : ∑ k : Fin 5, d k • mom Φ K r k = 0) :
    mv Φ K ((RatFunc.X + RatFunc.C c) * r) = vm (mv Φ K r) (Amat d c) := by
  have h4 : mom Φ K r 4 = -(d 4)⁻¹ • (d 0 • mom Φ K r 0 + d 1 • mom Φ K r 1 +
      d 2 • mom Φ K r 2 + d 3 • mom Φ K r 3) := by
    rw [Fin.sum_univ_five] at hcomp
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, fv3, fv4] at hcomp
    have : d 4 • mom Φ K r 4 = -(d 0 • mom Φ K r 0 + d 1 • mom Φ K r 1 +
        d 2 • mom Φ K r 2 + d 3 • mom Φ K r 3) := by
      rw [eq_neg_iff_add_eq_zero, ← hcomp]
      abel
    rw [neg_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have h0 := mom_mul_linear hΦ K r c 0
  have h1 := mom_mul_linear hΦ K r c 1
  have h2 := mom_mul_linear hΦ K r c 2
  have h3 := mom_mul_linear hΦ K r c 3
  funext j
  fin_cases j
  · show mom Φ K _ 0 = ∑ i : Fin 4, Amat d c i 0 • mom Φ K r i
    rw [h0, Fin.sum_univ_four]; simp [Amat, sub_eq_add_neg]
  · show mom Φ K _ 1 = ∑ i : Fin 4, Amat d c i 1 • mom Φ K r i
    rw [h1, Fin.sum_univ_four]; simp [Amat, sub_eq_add_neg]
  · show mom Φ K _ 2 = ∑ i : Fin 4, Amat d c i 2 • mom Φ K r i
    rw [h2, Fin.sum_univ_four]; simp [Amat, sub_eq_add_neg]
  · show mom Φ K _ 3 = ∑ i : Fin 4, Amat d c i 3 • mom Φ K r i
    rw [h3, Fin.sum_univ_four, h4]; simp [Amat]; module

/-- Backward step: if `m = m' A` and `A` is invertible then `m' = m A⁻¹`. -/
theorem step_bwd (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : IsUnit A.det) (m m' : Fin 4 → FormalZ)
    (h : m = vm m' A) : m' = vm m A⁻¹ := by
  rw [h, vm_mul, Matrix.mul_nonsing_inv _ hA, vm_one]

theorem det_Amat (d : Fin 5 → ℚ) (c : ℚ) (hd : d 4 ≠ 0) :
    (Amat d c).det = (d 0 + d 1 * c + d 2 * c ^ 2 + d 3 * c ^ 3 + d 4 * c ^ 4) / d 4 := by
  have h32 : (3 : Fin 4).succAbove 2 = 2 := by decide
  simp [Amat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, h32]
  field_simp
  ring

/-! ### Points and edges of the parameter lattice -/

/-- A parameter point `(a, b)` of the CMF. -/
structure Pt where
  a : Fin 5 → ℤ
  b : Fin 5 → ℤ

/-- The dual point `(1 - a, -b)`. -/
def Pt.dual (p : Pt) : Pt := ⟨fun i => 1 - p.a i, fun j => -p.b j⟩

/-- The kernel of a point. -/
def Pt.ker (p : Pt) : ℚ⟮X⟯ := CMF.ker p.a p.b
/-- The `D`-coefficients of a point. -/
def Pt.dc (p : Pt) : Fin 5 → ℚ := CMF.dc p.a p.b

theorem ker_lower_a (a b : Fin 5 → ℤ) (i : Fin 5) :
    ker (Function.update a i (a i - 1)) b =
      (RatFunc.X - RatFunc.C ((1 - a i : ℤ) : ℚ)) * ker a b := by
  fin_cases i <;> simp only [ker, Function.update_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Fin.reduceEq, ite_true, ite_false] <;> rw [pairKer_lower] <;> ring

theorem ker_raise_a (a b : Fin 5 → ℤ) (i : Fin 5) :
    ker a b = (RatFunc.X - RatFunc.C ((-a i : ℤ) : ℚ)) * ker (Function.update a i (a i + 1)) b := by
  have h := ker_lower_a (Function.update a i (a i + 1)) b i
  rw [Function.update_self, add_sub_cancel_right, Function.update_idem, Function.update_eq_self] at h
  rw [h]
  congr 3
  push_cast; ring

theorem ker_raise_b (a b : Fin 5 → ℤ) (j : Fin 5) :
    ker a (Function.update b j (b j + 1)) = (RatFunc.X - RatFunc.C ((-b j : ℤ) : ℚ)) * ker a b := by
  fin_cases j <;> simp only [ker, Function.update_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Fin.reduceEq, ite_true, ite_false] <;> rw [pairKer_raise] <;> ring

theorem ker_lower_b (a b : Fin 5 → ℤ) (j : Fin 5) :
    ker a b = (RatFunc.X - RatFunc.C ((-(b j - 1) : ℤ) : ℚ)) * ker a (Function.update b j (b j - 1)) := by
  have h := ker_raise_b a (Function.update b j (b j - 1)) j
  rw [Function.update_self, sub_add_cancel, Function.update_idem, Function.update_eq_self] at h
  exact h

/-- An edge: change coordinate `i` of `a` (if `isA`) or of `b` by `+1` (if `up`) or `-1`. -/
structure Edge where
  isA : Bool
  i : Fin 5
  up : Bool

/-- The endpoint of the edge `e` starting at `p`. -/
def Edge.apply (e : Edge) (p : Pt) : Pt :=
  if e.isA then ⟨Function.update p.a e.i (if e.up then p.a e.i + 1 else p.a e.i - 1), p.b⟩
  else ⟨p.a, Function.update p.b e.i (if e.up then p.b e.i + 1 else p.b e.i - 1)⟩

/-- An edge is *forward* if it multiplies the kernel by a linear factor (lowering an upper
parameter or raising a lower one); otherwise it divides. -/
abbrev Edge.fwd (e : Edge) : Prop := e.isA ≠ e.up

/-- The constant `c` of the linear factor `t + c` relating the two kernels. -/
def Edge.cval (e : Edge) (p : Pt) : ℤ :=
  (if e.isA then p.a e.i else p.b e.i) - (if e.up then 0 else 1)

/-- The point whose kernel is divided by the linear factor. -/
def Edge.src (e : Edge) (p : Pt) : Pt := if e.fwd then p else e.apply p
/-- The point whose kernel is multiplied by the linear factor. -/
def Edge.tgt (e : Edge) (p : Pt) : Pt := if e.fwd then e.apply p else p

/-- The dual edge (upper and lower parameters move in opposite directions). -/
def Edge.dual (e : Edge) : Edge := ⟨e.isA, e.i, !e.up⟩

theorem Edge.dual_apply (e : Edge) (p : Pt) : (e.dual).apply p.dual = (e.apply p).dual := by
  rcases e with ⟨isA, i, up⟩
  cases isA <;> cases up <;> (
    simp only [Edge.apply, Edge.dual, Pt.dual, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true, Bool.true_eq_false]
    congr 1 <;> funext j <;> by_cases h : j = i <;> simp [Function.update_apply, h] <;> ring)

theorem Edge.dual_fwd (e : Edge) : e.dual.fwd ↔ ¬ e.fwd := by
  rcases e with ⟨isA, i, up⟩
  cases isA <;> cases up <;> simp [Edge.dual, Edge.fwd]

/-- Across an edge the kernels differ by the linear factor `t + c`. -/
theorem ker_edge (e : Edge) (p : Pt) :
    (e.tgt p).ker = (RatFunc.X + RatFunc.C ((e.cval p : ℤ) : ℚ)) * (e.src p).ker := by
  rcases e with ⟨isA, i, up⟩
  rcases p with ⟨a, b⟩
  cases isA <;> cases up <;>
    simp only [Edge.tgt, Edge.src, Edge.fwd, Edge.cval, Edge.apply, Pt.ker, ne_eq, not_true_eq_false,
      not_false_eq_true, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, sub_zero]
  · rw [ker_lower_b a b i]; congr 1; push_cast; simp only [map_neg, map_sub, map_add, map_one]; ring
  · rw [ker_raise_b a b i]; congr 1; push_cast; simp only [map_neg, map_sub, map_add, map_one]; ring
  · rw [ker_lower_a a b i]; congr 1; push_cast; simp only [map_neg, map_sub, map_add, map_one]; ring
  · rw [ker_raise_a a b i]; congr 1; push_cast; simp only [map_neg, map_sub, map_add, map_one]; ring

/-- The step matrix of an edge. -/
def Edge.mat (e : Edge) (p : Pt) : Matrix (Fin 4) (Fin 4) ℚ :=
  if e.fwd then Amat (e.src p).dc (e.cval p) else (Amat (e.src p).dc (e.cval p))⁻¹

/-- Conditions for the transport across `e` from `p` with cutoff `K`: the companion relation
at the multiplicative source, `d_4 ≠ 0` there, and invertibility for a dividing edge. -/
def Edge.ok (Φ : ℤ → ℚ⟮X⟯ → FormalZ) (K : ℤ) (e : Edge) (p : Pt) : Prop :=
  (∑ k : Fin 5, (e.src p).dc k • mom Φ K (e.src p).ker k = 0) ∧ (e.src p).dc 4 ≠ 0 ∧
    (¬ e.fwd → Deval (e.src p).a (e.src p).b (e.cval p) ≠ 0)

theorem isUnit_det_Amat (a b : Fin 5 → ℤ) (c : ℚ) (hd : dc a b 4 ≠ 0) (hD : Deval a b c ≠ 0) :
    IsUnit (Amat (dc a b) c).det := by
  rw [isUnit_iff_ne_zero, det_Amat _ _ hd]
  exact div_ne_zero hD hd

theorem edge_transport {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (e : Edge)
    (p : Pt) (h : e.ok Φ K p) :
    mv Φ K (e.apply p).ker = vm (mv Φ K p.ker) (e.mat p) := by
  obtain ⟨hc, hd, hinv⟩ := h
  by_cases hf : e.fwd
  · have hs : e.src p = p := if_pos hf
    have ht : e.tgt p = e.apply p := if_pos hf
    rw [hs] at hc hd
    rw [Edge.mat, if_pos hf, hs, ← ht, ker_edge, hs, step_fwd hΦ K _ _ hd _ hc]
  · have hs : e.src p = e.apply p := if_neg hf
    have ht : e.tgt p = p := if_neg hf
    rw [Edge.mat, if_neg hf, ← hs]
    refine step_bwd _ (isUnit_det_Amat _ _ _ hd (hinv hf)) _ _ ?_
    have key := step_fwd hΦ K (e.src p).ker _ hd ((e.cval p : ℤ) : ℚ) hc
    rw [← ker_edge, ht] at key
    exact key

/-! ### Walks -/

/-- Ordered product of the step matrices along `edge 0, …, edge (T-1)` from the vertices `vtx`. -/
def wmat (edge : ℕ → Edge) (vtx : ℕ → Pt) (T : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  ((List.range T).map fun t => (edge t).mat (vtx t)).prod

theorem wmat_zero (edge : ℕ → Edge) (vtx : ℕ → Pt) : wmat edge vtx 0 = 1 := by simp [wmat]

theorem wmat_succ (edge : ℕ → Edge) (vtx : ℕ → Pt) (T : ℕ) :
    wmat edge vtx (T + 1) = wmat edge vtx T * (edge T).mat (vtx T) := by
  simp [wmat, List.range_succ]

theorem det_wmat (edge : ℕ → Edge) (vtx : ℕ → Pt) (T : ℕ) :
    (wmat edge vtx T).det = ((List.range T).map fun t => ((edge t).mat (vtx t)).det).prod := by
  induction T with
  | zero => simp [wmat]
  | succ T ih => rw [wmat_succ, Matrix.det_mul, ih, List.range_succ]; simp

/-- **Transport along a walk.** If every edge satisfies `Edge.ok`, the moment vector at the end
is the moment vector at the start times the product of the step matrices. -/
theorem walk_transport {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (edge : ℕ → Edge)
    (vtx : ℕ → Pt) (K : ℤ) (T : ℕ) (hv : ∀ t < T, vtx (t + 1) = (edge t).apply (vtx t))
    (hok : ∀ t < T, (edge t).ok Φ K (vtx t)) :
    mv Φ K (vtx T).ker = vm (mv Φ K (vtx 0).ker) (wmat edge vtx T) := by
  induction T with
  | zero => rw [wmat_zero, vm_one]
  | succ T ih =>
    rw [hv T (by omega), edge_transport hΦ K _ _ (hok T (by omega)),
      ih (fun t ht => hv t (by omega)) (fun t ht => hok t (by omega)), vm_mul, wmat_succ]

end ZetasIrr.CMF
