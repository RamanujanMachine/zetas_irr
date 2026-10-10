/-
# CMF transport, part 4: the walk from `p_N` to `p_{N+1}` and its boundary conditions

The parameter point of `R_N` is `p_N = (1+11N, 1+12N, -16N, -17N, 2+10N; 0, N, 2N, -N, -2N)`
(PDF Part I; `ker_pN` in `CMF_kernel.lean`). The 72 axis steps from `p_N` to `p_{N+1}` are
taken in the following order ("zigzag"), chosen so that the companion coefficient
`d₄ = 5 - ∑a + ∑b` stays in `{1,2,3,4}` at every vertex, both for the original point and for
its dual (`d₄* = 5 - d₄`); the PDF's two paths are nonsingular only on one side each.

* `a`-phase (steps `0 ≤ t < 66`, eleven blocks of six): three lowerings (`a₂` sixteen times,
  then `a₃` seventeen times) followed by three raisings (`a₀` eleven times, then `a₁` twelve
  times, then `a₄` ten times);
* `b`-phase (steps `66 ≤ t < 72`): raise `b₁`, raise `b₂` twice, lower `b₃`, lower `b₄` twice.

The vertices are `p_N + off t`, with the offsets `off t` tabulated (`offTable`); all per-step
facts (`off_succ`, the shapes `AShape`/`BShape` of the offsets, the types of the edges) are
checked by `decide`. The cutoffs are moved after the `a`-phase: `2N ↦ 2N+2` for the first
functional on the original kernel and for the second functional on the dual kernel, `N ↦ N+1`
for the first functional on the dual kernel (PDF Part VII §7 and Lemma 1).

The boundary conditions (`g'(K) = 0`, resp. `g''(K) = 0`, after cancellation) are proved once
per phase and functional for an arbitrary offset of the right shape (`VC_*`), as are the
nonvanishing of `d₄` and the invertibility of the axis matrices on the dividing steps.
`transport_orig`, `transport_dualM`, `transport_dualL` are the resulting transports.
-/
import CMF_transport

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-! ### Offsets, vertices and the walk -/

/-- Offsets of a vertex relative to `p_N`. -/
structure Off where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  b0 : ℤ
  b1 : ℤ
  b2 : ℤ
  b3 : ℤ
  b4 : ℤ
  deriving DecidableEq

def Off.vecA (o : Off) : Fin 5 → ℤ := ![o.a0, o.a1, o.a2, o.a3, o.a4]
def Off.vecB (o : Off) : Fin 5 → ℤ := ![o.b0, o.b1, o.b2, o.b3, o.b4]

/-- The coordinates of `p_N`. -/
def baseA (N : ℕ) : Fin 5 → ℤ :=
  ![1 + 11 * (N : ℤ), 1 + 12 * (N : ℤ), -16 * (N : ℤ), -17 * (N : ℤ), 2 + 10 * (N : ℤ)]
def baseB (N : ℕ) : Fin 5 → ℤ := ![0, (N : ℤ), 2 * (N : ℤ), -(N : ℤ), -2 * (N : ℤ)]

/-- The point `p_N + o`. -/
def Off.toPt (N : ℕ) (o : Off) : Pt :=
  ⟨fun i => baseA N i + o.vecA i, fun j => baseB N j + o.vecB j⟩

/-- The parameter point of `R_N`. -/
def pN (N : ℕ) : Pt := Off.toPt N ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `t`-th edge of the walk from `p_N` to `p_{N+1}`. -/
def edge (t : ℕ) : Edge :=
  if t < 66 then
    if t % 6 < 3 then
      (if 3 * (t / 6) + t % 6 < 16 then ⟨true, 2, false⟩ else ⟨true, 3, false⟩)
    else
      (if 3 * (t / 6) + (t % 6 - 3) < 11 then ⟨true, 0, true⟩
       else if 3 * (t / 6) + (t % 6 - 3) < 23 then ⟨true, 1, true⟩ else ⟨true, 4, true⟩)
  else if t = 66 then ⟨false, 1, true⟩
  else if t ≤ 68 then ⟨false, 2, true⟩
  else if t = 69 then ⟨false, 3, false⟩
  else ⟨false, 4, false⟩

/-- The edge `e` acting on offsets. -/
def applyOff (e : Edge) (o : Off) : Off :=
  if e.isA then
    if e.i = 0 then { o with a0 := if e.up then o.a0 + 1 else o.a0 - 1 }
    else if e.i = 1 then { o with a1 := if e.up then o.a1 + 1 else o.a1 - 1 }
    else if e.i = 2 then { o with a2 := if e.up then o.a2 + 1 else o.a2 - 1 }
    else if e.i = 3 then { o with a3 := if e.up then o.a3 + 1 else o.a3 - 1 }
    else { o with a4 := if e.up then o.a4 + 1 else o.a4 - 1 }
  else
    if e.i = 0 then { o with b0 := if e.up then o.b0 + 1 else o.b0 - 1 }
    else if e.i = 1 then { o with b1 := if e.up then o.b1 + 1 else o.b1 - 1 }
    else if e.i = 2 then { o with b2 := if e.up then o.b2 + 1 else o.b2 - 1 }
    else if e.i = 3 then { o with b3 := if e.up then o.b3 + 1 else o.b3 - 1 }
    else { o with b4 := if e.up then o.b4 + 1 else o.b4 - 1 }

theorem vecA_applyOff (e : Edge) (o : Off) :
    (applyOff e o).vecA =
      if e.isA then Function.update o.vecA e.i (if e.up then o.vecA e.i + 1 else o.vecA e.i - 1)
      else o.vecA := by
  rcases e with ⟨isA, i, up⟩
  cases isA <;> cases up <;> fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem vecB_applyOff (e : Edge) (o : Off) :
    (applyOff e o).vecB =
      if e.isA then o.vecB
      else Function.update o.vecB e.i (if e.up then o.vecB e.i + 1 else o.vecB e.i - 1) := by
  rcases e with ⟨isA, i, up⟩
  cases isA <;> cases up <;> fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem update_add (f g : Fin 5 → ℤ) (i : Fin 5) (d : ℤ) :
    Function.update (fun k => f k + g k) i (f i + g i + d) =
      fun k => f k + Function.update g i (g i + d) k := by
  funext k
  by_cases h : k = i
  · subst h; rw [Function.update_self, Function.update_self, add_assoc]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem update_sub (f g : Fin 5 → ℤ) (i : Fin 5) :
    Function.update (fun k => f k + g k) i (f i + g i - 1) =
      fun k => f k + Function.update g i (g i - 1) k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, update_add]

theorem apply_toPt (e : Edge) (N : ℕ) (o : Off) :
    e.apply (o.toPt N) = (applyOff e o).toPt N := by
  rcases e with ⟨isA, i, up⟩
  cases isA <;> cases up <;>
    simp only [Edge.apply, Off.toPt, vecA_applyOff, vecB_applyOff, ite_true, ite_false,
      Bool.false_eq_true, Bool.true_eq_false, update_add, update_sub]

/-- The offsets of the 73 vertices of the walk. -/
def offTable : List Off := [
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, -1, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, -2, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, -3, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨1, 0, -3, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨2, 0, -3, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨3, 0, -3, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨3, 0, -4, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨3, 0, -5, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨3, 0, -6, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨4, 0, -6, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨5, 0, -6, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨6, 0, -6, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨6, 0, -7, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨6, 0, -8, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨6, 0, -9, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨7, 0, -9, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨8, 0, -9, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨9, 0, -9, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨9, 0, -10, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨9, 0, -11, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨9, 0, -12, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨10, 0, -12, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 0, -12, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 1, -12, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 1, -13, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 1, -14, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 1, -15, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 2, -15, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 3, -15, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 4, -15, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 4, -16, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 4, -16, -1, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 4, -16, -2, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 5, -16, -2, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 6, -16, -2, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 7, -16, -2, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 7, -16, -3, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 7, -16, -4, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 7, -16, -5, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 8, -16, -5, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 9, -16, -5, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 10, -16, -5, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 10, -16, -6, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 10, -16, -7, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 10, -16, -8, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 11, -16, -8, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -8, 0, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -8, 1, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -9, 1, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -10, 1, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -11, 1, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -11, 2, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -11, 3, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -11, 4, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -12, 4, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -13, 4, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -14, 4, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -14, 5, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -14, 6, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -14, 7, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -15, 7, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -16, 7, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -17, 7, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -17, 8, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -17, 9, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -17, 10, 0, 0, 0, 0, 0⟩,
  ⟨11, 12, -16, -17, 10, 0, 1, 0, 0, 0⟩,
  ⟨11, 12, -16, -17, 10, 0, 1, 1, 0, 0⟩,
  ⟨11, 12, -16, -17, 10, 0, 1, 2, 0, 0⟩,
  ⟨11, 12, -16, -17, 10, 0, 1, 2, -1, 0⟩,
  ⟨11, 12, -16, -17, 10, 0, 1, 2, -1, -1⟩,
  ⟨11, 12, -16, -17, 10, 0, 1, 2, -1, -2⟩
]

def off (t : ℕ) : Off := offTable.getD t ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem off_succ : ∀ t < 72, off (t + 1) = applyOff (edge t) (off t) := by decide

/-- The vertices of the walk. -/
def vtx (N t : ℕ) : Pt := (off t).toPt N

theorem vtx_zero (N : ℕ) : vtx N 0 = pN N := rfl

theorem vtx_succ (N t : ℕ) (ht : t < 72) : vtx N (t + 1) = (edge t).apply (vtx N t) := by
  rw [vtx, vtx, off_succ t ht, apply_toPt]

theorem Pt.ext' {p q : Pt} (ha : ∀ i, p.a i = q.a i) (hb : ∀ j, p.b j = q.b j) : p = q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨a', b'⟩
  simp only [Pt.mk.injEq]
  exact ⟨funext ha, funext hb⟩

theorem toPt_a (N : ℕ) (o : Off) (i : Fin 5) : (o.toPt N).a i = baseA N i + o.vecA i := rfl
theorem toPt_b (N : ℕ) (o : Off) (j : Fin 5) : (o.toPt N).b j = baseB N j + o.vecB j := rfl
theorem Pt.dual_a (p : Pt) (i : Fin 5) : p.dual.a i = 1 - p.a i := rfl
theorem Pt.dual_b (p : Pt) (j : Fin 5) : p.dual.b j = -p.b j := rfl

/-- Simp set for coordinates of `p_N + o`. -/
macro "coord_simp" : tactic => `(tactic|
  simp only [Pt.dual_a, Pt.dual_b, toPt_a, toPt_b, baseA, baseB, Off.vecA, Off.vecB,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, Fin.isValue,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at *)

theorem vtx_72 (N : ℕ) : vtx N 72 = pN (N + 1) := by
  rw [vtx, show off 72 = ⟨11, 12, -16, -17, 10, 0, 1, 2, -1, -2⟩ from rfl, pN]
  refine Pt.ext' (fun i => ?_) (fun i => ?_) <;> fin_cases i <;> coord_simp <;> push_cast <;> ring

/-! ### Zeros and poles of the kernel of a point -/

/-- The zeros of `ker p`, with multiplicity. -/
def Zk (p : Pt) : Multiset ℤ :=
  ival (1 - p.b 0) (p.b 0 - p.a 4).toNat + ival (1 - p.b 1) (p.b 1 - p.a 0).toNat +
    ival (1 - p.b 2) (p.b 2 - p.a 1).toNat + ival (1 - p.b 3) (p.b 3 - p.a 2).toNat +
    ival (1 - p.b 4) (p.b 4 - p.a 3).toNat

/-- The poles of `ker p`, with multiplicity. -/
def Pk (p : Pt) : Multiset ℤ :=
  ival (1 - p.a 4) (p.a 4 - p.b 0).toNat + ival (1 - p.a 0) (p.a 0 - p.b 1).toNat +
    ival (1 - p.a 1) (p.a 1 - p.b 2).toNat + ival (1 - p.a 2) (p.a 2 - p.b 3).toNat +
    ival (1 - p.a 3) (p.a 3 - p.b 4).toNat

theorem ker_eq_lin (p : Pt) : p.ker = lin (Zk p) (Pk p) := by
  simp only [Pt.ker, ker, pairKer, Zk, Pk]
  rw [lin_add, lin_add, lin_add, lin_add]

/-- The boundary condition at a vertex: poles `≤ K` and a zero of order `≥ ord` of
`∏_j (t + b_j) ker p` at `K`. -/
def VC (ord : ℕ) (K : ℤ) (p : Pt) : Prop :=
  (∀ q ∈ Pk p, q ≤ K) ∧ (Pk p).count K + ord ≤ (bro p.b + Zk p).count K

/-- The condition for moving the cutoff from `K` to `K + 1`. -/
def CutC (ord : ℕ) (K : ℤ) (p : Pt) : Prop :=
  (∀ q ∈ Pk p, q ≤ K) ∧ ord ≤ (Zk p).count (K + 1)

theorem companion_of_VC {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (p : Pt)
    (h : VC ord K p) : ∑ k : Fin 5, p.dc k • mom Φ K p.ker k = 0 :=
  companion hΦ p.a p.b K (Zk p) (Pk p) (ker_eq_lin p) h.1 h.2

theorem ok_of {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (e : Edge) (p : Pt)
    (h1 : VC ord K (e.src p)) (h2 : (e.src p).dc 4 ≠ 0)
    (h3 : ¬ e.fwd → Deval (e.src p).a (e.src p).b (e.cval p) ≠ 0) : e.ok Φ K p :=
  ⟨companion_of_VC hΦ K _ h1, h2, h3⟩

theorem negX_pow_mul_lin (j : ℕ) (Z P : Multiset ℤ) :
    (-RatFunc.X) ^ j * lin Z P = RatFunc.C ((-1 : ℚ) ^ j) * lin (Multiset.replicate j 0 + Z) P := by
  induction j with
  | zero => rw [pow_zero, pow_zero, map_one, one_mul, one_mul, Multiset.replicate_zero, zero_add]
  | succ j ih =>
    rw [pow_succ, mul_comm _ (-RatFunc.X), mul_assoc, ih, Multiset.replicate_succ,
      Multiset.cons_add, lin_cons_left, pow_succ, map_mul, map_neg, map_one, Int.cast_zero,
      map_zero, sub_zero]
    ring

/-- Moving the cutoff by one. -/
theorem mv_cut {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (p : Pt)
    (h : CutC ord K p) (hK : K + 1 ≠ 0) : mv Φ (K + 1) p.ker = mv Φ K p.ker := by
  funext j
  show Φ (K + 1) ((-RatFunc.X) ^ (j : ℕ) * p.ker) = Φ K ((-RatFunc.X) ^ (j : ℕ) * p.ker)
  rw [ker_eq_lin, negX_pow_mul_lin, hΦ.C_mul, hΦ.C_mul]
  congr 1
  refine hΦ.cut K _ _ h.1 ?_
  rw [Multiset.count_add, Multiset.count_replicate, if_neg (Ne.symm hK), zero_add]
  exact h.2

/-! ### Shapes of the offsets along the walk -/

/-- Offsets occurring in the `a`-phase. -/
def AShape (o : Off) : Prop :=
  0 ≤ o.a0 ∧ o.a0 ≤ 11 ∧ 0 ≤ o.a1 ∧ o.a1 ≤ 12 ∧ -16 ≤ o.a2 ∧ o.a2 ≤ 0 ∧ -17 ≤ o.a3 ∧ o.a3 ≤ 0 ∧
    0 ≤ o.a4 ∧ o.a4 ≤ 10 ∧ o.b0 = 0 ∧ o.b1 = 0 ∧ o.b2 = 0 ∧ o.b3 = 0 ∧ o.b4 = 0

/-- Offsets occurring in the `b`-phase. -/
def BShape (o : Off) : Prop :=
  o.a0 = 11 ∧ o.a1 = 12 ∧ o.a2 = -16 ∧ o.a3 = -17 ∧ o.a4 = 10 ∧ o.b0 = 0 ∧ 0 ≤ o.b1 ∧ o.b1 ≤ 1 ∧
    0 ≤ o.b2 ∧ o.b2 ≤ 2 ∧ -1 ≤ o.b3 ∧ o.b3 ≤ 0 ∧ -2 ≤ o.b4 ∧ o.b4 ≤ 0

instance (o : Off) : Decidable (AShape o) := by unfold AShape; infer_instance
instance (o : Off) : Decidable (BShape o) := by unfold BShape; infer_instance

theorem ashape_off : ∀ t ≤ 66, AShape (off t) := by decide
theorem bshape_off : ∀ t, 66 ≤ t → t ≤ 72 → BShape (off t) := by decide

/-- The companion coefficient `d₄ - 1` of `p_N + o`. -/
def d4o (o : Off) : ℤ := o.b0 + o.b1 + o.b2 + o.b3 + o.b4 - (o.a0 + o.a1 + o.a2 + o.a3 + o.a4)

theorem d4o_off : ∀ t ≤ 72, 0 ≤ d4o (off t) ∧ d4o (off t) ≤ 3 := by decide

theorem off_66 : off 66 = ⟨11, 12, -16, -17, 10, 0, 0, 0, 0, 0⟩ := rfl

/-- The edges of the `a`-phase. -/
theorem edge_a : ∀ t < 66, (edge t).isA = true ∧
    ((edge t).up = false → (edge t).i = 2 ∨ (edge t).i = 3) ∧
    ((edge t).up = true → (edge t).i = 0 ∨ (edge t).i = 1 ∨ (edge t).i = 4) := by decide

/-- The edges of the `b`-phase. -/
theorem edge_b : ∀ t, 66 ≤ t → t < 72 → (edge t).isA = false ∧
    ((edge t).up = true → (edge t).i = 1 ∨ (edge t).i = 2) ∧
    ((edge t).up = false → (edge t).i = 3 ∨ (edge t).i = 4) := by decide

/-! ### Evaluation of the boundary conditions -/

theorem ite_pos' {c : Prop} [Decidable c] (h : c) : (if c then (1 : ℕ) else 0) = 1 := if_pos h
theorem ite_neg' {c : Prop} [Decidable c] (h : ¬ c) : (if c then (1 : ℕ) else 0) = 0 := if_neg h

theorem count_bro (b : Fin 5 → ℤ) (K : ℤ) :
    (bro b).count K = (if K = -b 0 then 1 else 0) + (if K = -b 1 then 1 else 0) +
      (if K = -b 2 then 1 else 0) + (if K = -b 3 then 1 else 0) + (if K = -b 4 then 1 else 0) := by
  simp only [bro, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  ring

/-- The simp set turning `VC`/`CutC` at `p_N + o` (or its dual) into integer arithmetic. -/
macro "vc_simp" : tactic => `(tactic|
  (simp only [VC, CutC, Pk, Zk, bro, Pt.dual_a, Pt.dual_b, toPt_a, toPt_b, baseA, baseB,
    Off.vecA, Off.vecB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val]
   simp only [Multiset.mem_add, mem_ival, Multiset.count_add, count_ival, Multiset.insert_eq_cons,
    Multiset.count_cons, Multiset.count_singleton, Int.toNat_eq_max]))

/-- Finish a `VC`/`CutC` goal after `vc_simp`. -/
macro "vc_finish" : tactic => `(tactic|
  (refine ⟨fun q hq => by omega, ?_⟩
   simp (disch := omega) only [ite_pos', ite_neg']
   first | omega | (split_ifs <;> omega)))

section Shapes
variable (N : ℕ) (o : Off)

theorem VC_orig_a (ho : AShape o) : VC 2 (2 * N) (o.toPt N) := by
  rcases o with ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4⟩
  dsimp only [AShape] at ho
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl, rfl, rfl, rfl, rfl⟩ := ho
  rcases Nat.eq_zero_or_pos N with rfl | hN <;> (vc_simp; vc_finish)

theorem VC_orig_b (ho : BShape o) : VC 2 (2 * N + 2) (o.toPt N) := by
  rcases o with ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4⟩
  dsimp only [BShape] at ho
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ho
  vc_simp
  vc_finish

theorem VC_dualM_a (ho : AShape o) : VC 3 (2 * N) (o.toPt N).dual := by
  rcases o with ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4⟩
  dsimp only [AShape] at ho
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl, rfl, rfl, rfl, rfl⟩ := ho
  rcases Nat.eq_zero_or_pos N with rfl | hN <;> (vc_simp; vc_finish)

theorem VC_dualM_b (ho : BShape o) : VC 3 (2 * N + 2) (o.toPt N).dual := by
  rcases o with ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4⟩
  dsimp only [BShape] at ho
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ho
  vc_simp
  vc_finish

theorem VC_dualL_a (ho : AShape o) : VC 2 (N : ℤ) (o.toPt N).dual := by
  rcases o with ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4⟩
  dsimp only [AShape] at ho
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl, rfl, rfl, rfl, rfl⟩ := ho
  rcases Nat.eq_zero_or_pos N with rfl | hN <;> (vc_simp; vc_finish)

theorem VC_dualL_b (ho : BShape o) : VC 2 ((N : ℤ) + 1) (o.toPt N).dual := by
  rcases o with ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4⟩
  dsimp only [BShape] at ho
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ho
  vc_simp
  vc_finish

end Shapes

theorem Cut_orig (N : ℕ) : CutC 2 (2 * N) (vtx N 66) ∧ CutC 2 (2 * N + 1) (vtx N 66) := by
  rw [vtx, off_66]
  constructor <;> (vc_simp; vc_finish)

theorem Cut_dualM (N : ℕ) :
    CutC 3 (2 * N) (vtx N 66).dual ∧ CutC 3 (2 * N + 1) (vtx N 66).dual := by
  rw [vtx, off_66]
  constructor <;> (vc_simp; vc_finish)

theorem Cut_dualL (N : ℕ) : CutC 2 (N : ℤ) (vtx N 66).dual := by
  rw [vtx, off_66]
  vc_simp; vc_finish

/-! ### `d₄ ≠ 0` and invertibility -/

theorem dc4_toPt (N : ℕ) (o : Off) (h : 0 ≤ d4o o) : (o.toPt N).dc 4 ≠ 0 := by
  show dc _ _ 4 ≠ 0
  rw [dc_four]
  have : (5 : ℤ) - ((o.toPt N).a 0 + (o.toPt N).a 1 + (o.toPt N).a 2 + (o.toPt N).a 3 +
      (o.toPt N).a 4) + ((o.toPt N).b 0 + (o.toPt N).b 1 + (o.toPt N).b 2 + (o.toPt N).b 3 +
      (o.toPt N).b 4) = 1 + d4o o := by
    coord_simp; unfold d4o; ring
  intro hq
  have h' : (5 : ℤ) - ((o.toPt N).a 0 + (o.toPt N).a 1 + (o.toPt N).a 2 + (o.toPt N).a 3 +
      (o.toPt N).a 4) + ((o.toPt N).b 0 + (o.toPt N).b 1 + (o.toPt N).b 2 + (o.toPt N).b 3 +
      (o.toPt N).b 4) = 0 := by exact_mod_cast hq
  omega

theorem dc4_toPt_dual (N : ℕ) (o : Off) (h : d4o o ≤ 3) : (o.toPt N).dual.dc 4 ≠ 0 := by
  show dc _ _ 4 ≠ 0
  rw [dc_four]
  have : (5 : ℤ) - ((o.toPt N).dual.a 0 + (o.toPt N).dual.a 1 + (o.toPt N).dual.a 2 +
      (o.toPt N).dual.a 3 + (o.toPt N).dual.a 4) + ((o.toPt N).dual.b 0 + (o.toPt N).dual.b 1 +
      (o.toPt N).dual.b 2 + (o.toPt N).dual.b 3 + (o.toPt N).dual.b 4) = 4 - d4o o := by
    coord_simp; unfold d4o; ring
  intro hq
  have h' : (5 : ℤ) - ((o.toPt N).dual.a 0 + (o.toPt N).dual.a 1 + (o.toPt N).dual.a 2 +
      (o.toPt N).dual.a 3 + (o.toPt N).dual.a 4) + ((o.toPt N).dual.b 0 + (o.toPt N).dual.b 1 +
      (o.toPt N).dual.b 2 + (o.toPt N).dual.b 3 + (o.toPt N).dual.b 4) = 0 := by exact_mod_cast hq
  omega

theorem dc4_vtx (N t : ℕ) (ht : t ≤ 72) : (vtx N t).dc 4 ≠ 0 :=
  dc4_toPt N _ (d4o_off t ht).1

theorem dc4_dual (N t : ℕ) (ht : t ≤ 72) : (vtx N t).dual.dc 4 ≠ 0 :=
  dc4_toPt_dual N _ (d4o_off t ht).2

theorem Deval_eq' (a b : Fin 5 → ℤ) (c : ℚ) :
    Deval a b c = (∏ i, (c - al a i)) - ∏ j, (c - bq b j) := by
  rw [Deval_eq, Fin.prod_univ_five, Fin.prod_univ_five]

theorem Deval_ne_zero_a (a b : Fin 5 → ℤ) (i : Fin 5) (c : ℤ) (hc : c = a i - 1)
    (h : ∀ j, c ≠ b j) : Deval a b (c : ℚ) ≠ 0 := by
  rw [Deval_eq', Finset.prod_eq_zero (Finset.mem_univ i) (by rw [al, hc]; push_cast; ring),
    zero_sub, neg_ne_zero]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_
  show (c : ℚ) ≠ (b j : ℚ)
  exact_mod_cast h j

theorem Deval_ne_zero_b (a b : Fin 5 → ℤ) (j : Fin 5) (c : ℤ) (hc : c = b j)
    (h : ∀ i, c ≠ a i - 1) : Deval a b (c : ℚ) ≠ 0 := by
  rw [Deval_eq', Finset.prod_eq_zero (f := fun j => (c : ℚ) - bq b j) (Finset.mem_univ j)
    (by show (c : ℚ) - (b j : ℚ) = 0; rw [hc, sub_self]), sub_zero]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr ?_
  show (c : ℚ) ≠ (a i : ℚ) - 1
  rw [← Int.cast_one, ← Int.cast_sub]
  exact_mod_cast h i

theorem apply_a_self (e : Edge) (p : Pt) (hA : e.isA = true) :
    (e.apply p).a e.i = if e.up then p.a e.i + 1 else p.a e.i - 1 := by
  rw [Edge.apply, if_pos hA]; exact Function.update_self _ _ _

theorem apply_b_self (e : Edge) (p : Pt) (hA : e.isA = false) :
    (e.apply p).b e.i = if e.up then p.b e.i + 1 else p.b e.i - 1 := by
  rw [Edge.apply, if_neg (by rw [hA]; exact Bool.false_ne_true)]; exact Function.update_self _ _ _

theorem apply_b_of_a (e : Edge) (p : Pt) (hA : e.isA = true) : (e.apply p).b = p.b := by
  rw [Edge.apply, if_pos hA]

theorem apply_a_of_b (e : Edge) (p : Pt) (hA : e.isA = false) : (e.apply p).a = p.a := by
  rw [Edge.apply, if_neg (by rw [hA]; exact Bool.false_ne_true)]

/-- Invertibility for a raising `a`-step in the `a`-phase (original walk). -/
theorem inv_orig_a (N : ℕ) (o : Off) (ho : AShape o) (e : Edge) (hA : e.isA = true)
    (hu : e.up = true) (hi : e.i = 0 ∨ e.i = 1 ∨ e.i = 4) :
    Deval (e.apply (o.toPt N)).a (e.apply (o.toPt N)).b (e.cval (o.toPt N)) ≠ 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ho
  refine Deval_ne_zero_a _ _ e.i _ ?_ fun j => ?_
  · rw [apply_a_self e _ hA, if_pos hu, Edge.cval, if_pos hA, if_pos hu]; ring
  · rw [apply_b_of_a e _ hA, Edge.cval, if_pos hA, if_pos hu, sub_zero]
    rcases hi with hi | hi | hi <;> rw [hi] <;> fin_cases j <;> coord_simp <;> omega

/-- Invertibility for a lowering `b`-step in the `b`-phase (original walk). -/
theorem inv_orig_b (N : ℕ) (o : Off) (ho : BShape o) (e : Edge) (hA : e.isA = false)
    (hu : e.up = false) (hi : e.i = 3 ∨ e.i = 4) :
    Deval (e.apply (o.toPt N)).a (e.apply (o.toPt N)).b (e.cval (o.toPt N)) ≠ 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ho
  have hA' : ¬ e.isA = true := by rw [hA]; exact Bool.false_ne_true
  have hu' : ¬ e.up = true := by rw [hu]; exact Bool.false_ne_true
  refine Deval_ne_zero_b _ _ e.i _ ?_ fun i => ?_
  · rw [apply_b_self e _ hA, if_neg hu', Edge.cval, if_neg hA', if_neg hu']
  · rw [apply_a_of_b e _ hA, Edge.cval, if_neg hA', if_neg hu']
    rcases hi with hi | hi <;> rw [hi] <;> fin_cases i <;> coord_simp <;> omega

/-- Invertibility for a raising `a*`-step of the dual walk (a lowering `a`-step of the original
walk, `a`-phase). -/
theorem inv_dual_a (N : ℕ) (o : Off) (ho : AShape o) (e : Edge) (hA : e.isA = true)
    (hu : e.up = false) (hi : e.i = 2 ∨ e.i = 3) :
    Deval (e.apply (o.toPt N)).dual.a (e.apply (o.toPt N)).dual.b
      (e.dual.cval (o.toPt N).dual) ≠ 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ho
  have hu' : ¬ e.up = true := by rw [hu]; exact Bool.false_ne_true
  refine Deval_ne_zero_a _ _ e.i _ ?_ fun j => ?_
  · rw [Pt.dual_a, apply_a_self e _ hA, if_neg hu', Edge.cval, Edge.dual]
    simp only [hA, hu, Bool.not_false, ite_true, Pt.dual_a, sub_zero]
    ring
  · rw [Pt.dual_b, apply_b_of_a e _ hA, Edge.cval, Edge.dual]
    simp only [hA, hu, Bool.not_false, ite_true, Pt.dual_a, sub_zero]
    rcases hi with hi | hi <;> rw [hi] <;> fin_cases j <;> coord_simp <;> omega

/-- Invertibility for a lowering `b*`-step of the dual walk (a raising `b`-step of the original
walk, `b`-phase). -/
theorem inv_dual_b (N : ℕ) (o : Off) (ho : BShape o) (e : Edge) (hA : e.isA = false)
    (hu : e.up = true) (hi : e.i = 1 ∨ e.i = 2) :
    Deval (e.apply (o.toPt N)).dual.a (e.apply (o.toPt N)).dual.b
      (e.dual.cval (o.toPt N).dual) ≠ 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ho
  have hA' : ¬ e.isA = true := by rw [hA]; exact Bool.false_ne_true
  refine Deval_ne_zero_b _ _ e.i _ ?_ fun i => ?_
  · rw [Pt.dual_b, apply_b_self e _ hA, if_pos hu, Edge.cval, Edge.dual]
    simp only [hA, hu, Bool.not_true, ite_false, Bool.false_eq_true, Pt.dual_b]
    ring
  · rw [Pt.dual_a, apply_a_of_b e _ hA, Edge.cval, Edge.dual]
    simp only [hA, hu, Bool.not_true, ite_false, Bool.false_eq_true, Pt.dual_b]
    rcases hi with hi | hi <;> rw [hi] <;> fin_cases i <;> coord_simp <;> omega

/-! ### The conditions `Edge.ok` along the walk -/

theorem src_eq (e : Edge) (p : Pt) : e.src p = if e.fwd then p else e.apply p := rfl

theorem fwd_iff_up_false (e : Edge) (hA : e.isA = true) : e.fwd ↔ e.up = false := by
  unfold Edge.fwd; rw [hA]; cases e.up <;> simp

theorem fwd_iff_up_true (e : Edge) (hA : e.isA = false) : e.fwd ↔ e.up = true := by
  unfold Edge.fwd; rw [hA]; cases e.up <;> simp

theorem ok_orig_a (N t : ℕ) (ht : t < 66) : (edge t).ok Lfun (2 * N) (vtx N t) := by
  obtain ⟨hA, hlo, hra⟩ := edge_a t ht
  have hs := ashape_off t (by omega)
  have hs' := ashape_off (t + 1) (by omega)
  refine ok_of isMom_Lfun _ _ _ ?_ ?_ ?_ <;> rw [src_eq] <;> split_ifs with hf
  · exact VC_orig_a N _ hs
  · rw [← vtx_succ N t (by omega)]; exact VC_orig_a N _ hs'
  · exact dc4_vtx N t (by omega)
  · rw [← vtx_succ N t (by omega)]; exact dc4_vtx N (t + 1) (by omega)
  · exact fun h => absurd hf h
  · intro _
    have hu : (edge t).up = true := by
      rw [fwd_iff_up_false _ hA] at hf; cases h : (edge t).up <;> simp_all
    exact inv_orig_a N _ hs _ hA hu (hra hu)

theorem ok_orig_b (N t : ℕ) (h1 : 66 ≤ t) (h2 : t < 72) :
    (edge t).ok Lfun (2 * N + 2) (vtx N t) := by
  obtain ⟨hA, hra, hlo⟩ := edge_b t h1 h2
  have hs := bshape_off t h1 (by omega)
  have hs' := bshape_off (t + 1) (by omega) (by omega)
  refine ok_of isMom_Lfun _ _ _ ?_ ?_ ?_ <;> rw [src_eq] <;> split_ifs with hf
  · exact VC_orig_b N _ hs
  · rw [← vtx_succ N t (by omega)]; exact VC_orig_b N _ hs'
  · exact dc4_vtx N t (by omega)
  · rw [← vtx_succ N t (by omega)]; exact dc4_vtx N (t + 1) (by omega)
  · exact fun h => absurd hf h
  · intro _
    have hu : (edge t).up = false := by
      rw [fwd_iff_up_true _ hA] at hf; cases h : (edge t).up <;> simp_all
    exact inv_orig_b N _ hs _ hA hu (hlo hu)

theorem dual_src (e : Edge) (p : Pt) :
    e.dual.src p.dual = if e.dual.fwd then p.dual else (e.apply p).dual := by
  rw [src_eq, Edge.dual_apply]

theorem ok_dual_gen {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) (N t : ℕ)
    (ht : t < 72) (hVC : VC ord K (vtx N t).dual) (hVC' : VC ord K (vtx N (t + 1)).dual)
    (hinv : ¬ (edge t).dual.fwd →
      Deval (vtx N (t + 1)).dual.a (vtx N (t + 1)).dual.b
        ((edge t).dual.cval (vtx N t).dual) ≠ 0) :
    (edge t).dual.ok Φ K (vtx N t).dual := by
  refine ok_of hΦ _ _ _ ?_ ?_ ?_ <;> rw [dual_src] <;> split_ifs with hf
  · exact hVC
  · rw [← vtx_succ N t ht]; exact hVC'
  · exact dc4_dual N t (by omega)
  · rw [← vtx_succ N t ht]; exact dc4_dual N (t + 1) (by omega)
  · exact fun h => absurd hf h
  · exact fun _ => by rw [← vtx_succ N t ht]; exact hinv hf

theorem inv_dual_of_a (N t : ℕ) (ht : t < 66) (hf : ¬ (edge t).dual.fwd) :
    Deval ((edge t).apply (vtx N t)).dual.a ((edge t).apply (vtx N t)).dual.b
      ((edge t).dual.cval (vtx N t).dual) ≠ 0 := by
  obtain ⟨hA, hlo, hra⟩ := edge_a t ht
  rw [Edge.dual_fwd, not_not, fwd_iff_up_false _ hA] at hf
  exact inv_dual_a N _ (ashape_off t (by omega)) _ hA hf (hlo hf)

theorem inv_dual_of_b (N t : ℕ) (h1 : 66 ≤ t) (h2 : t < 72) (hf : ¬ (edge t).dual.fwd) :
    Deval ((edge t).apply (vtx N t)).dual.a ((edge t).apply (vtx N t)).dual.b
      ((edge t).dual.cval (vtx N t).dual) ≠ 0 := by
  obtain ⟨hA, hra, hlo⟩ := edge_b t h1 h2
  rw [Edge.dual_fwd, not_not, fwd_iff_up_true _ hA] at hf
  exact inv_dual_b N _ (bshape_off t h1 (by omega)) _ hA hf (hra hf)

theorem ok_dualM_a (N t : ℕ) (ht : t < 66) : (edge t).dual.ok Mfun (2 * N) (vtx N t).dual :=
  ok_dual_gen isMom_Mfun _ N t (by omega) (VC_dualM_a N _ (ashape_off t (by omega)))
    (VC_dualM_a N _ (ashape_off (t + 1) (by omega)))
    (fun hf => by rw [vtx_succ N t (by omega)]; exact inv_dual_of_a N t ht hf)

theorem ok_dualM_b (N t : ℕ) (h1 : 66 ≤ t) (h2 : t < 72) :
    (edge t).dual.ok Mfun (2 * N + 2) (vtx N t).dual :=
  ok_dual_gen isMom_Mfun _ N t h2 (VC_dualM_b N _ (bshape_off t h1 (by omega)))
    (VC_dualM_b N _ (bshape_off (t + 1) (by omega) (by omega)))
    (fun hf => by rw [vtx_succ N t h2]; exact inv_dual_of_b N t h1 h2 hf)

theorem ok_dualL_a (N t : ℕ) (ht : t < 66) : (edge t).dual.ok Lfun (N : ℤ) (vtx N t).dual :=
  ok_dual_gen isMom_Lfun _ N t (by omega) (VC_dualL_a N _ (ashape_off t (by omega)))
    (VC_dualL_a N _ (ashape_off (t + 1) (by omega)))
    (fun hf => by rw [vtx_succ N t (by omega)]; exact inv_dual_of_a N t ht hf)

theorem ok_dualL_b (N t : ℕ) (h1 : 66 ≤ t) (h2 : t < 72) :
    (edge t).dual.ok Lfun ((N : ℤ) + 1) (vtx N t).dual :=
  ok_dual_gen isMom_Lfun _ N t h2 (VC_dualL_b N _ (bshape_off t h1 (by omega)))
    (VC_dualL_b N _ (bshape_off (t + 1) (by omega) (by omega)))
    (fun hf => by rw [vtx_succ N t h2]; exact inv_dual_of_b N t h1 h2 hf)

/-! ### The three transports -/

/-- The dual edge sequence and dual vertices. -/
def dedge (t : ℕ) : Edge := (edge t).dual
def dvtx (N t : ℕ) : Pt := (vtx N t).dual

theorem dvtx_succ (N t : ℕ) (ht : t < 72) : dvtx N (t + 1) = (dedge t).apply (dvtx N t) := by
  rw [dvtx, dvtx, dedge, vtx_succ N t ht, Edge.dual_apply]

/-- The transport matrix of the original walk `p_N → p_{N+1}`. -/
def Wmat (N : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := wmat edge (vtx N) 72
/-- The transport matrix of the dual walk. -/
def Dmat (N : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := wmat dedge (dvtx N) 72

theorem wmat_add (edge : ℕ → Edge) (vtx : ℕ → Pt) (s T : ℕ) :
    wmat edge vtx (s + T) =
      wmat edge vtx s * wmat (fun t => edge (s + t)) (fun t => vtx (s + t)) T := by
  induction T with
  | zero => rw [add_zero, wmat_zero, mul_one]
  | succ T ih => rw [← add_assoc, wmat_succ, ih, wmat_succ, mul_assoc]

/-- A transport with a cutoff move after 66 steps. -/
theorem transport_gen {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (edge : ℕ → Edge)
    (vtx : ℕ → Pt) (hv : ∀ t < 72, vtx (t + 1) = (edge t).apply (vtx t)) (K₀ K₁ : ℤ)
    (hok₀ : ∀ t < 66, (edge t).ok Φ K₀ (vtx t))
    (hcut : mv Φ K₁ (vtx 66).ker = mv Φ K₀ (vtx 66).ker)
    (hok₁ : ∀ t, 66 ≤ t → t < 72 → (edge t).ok Φ K₁ (vtx t)) :
    mv Φ K₁ (vtx 72).ker = vm (mv Φ K₀ (vtx 0).ker) (wmat edge vtx 72) := by
  have h1 := walk_transport hΦ edge vtx K₀ 66 (fun t ht => hv t (by omega)) hok₀
  have h2 := walk_transport hΦ (fun t => edge (66 + t)) (fun t => vtx (66 + t)) K₁ 6
    (fun t ht => by rw [← add_assoc]; exact hv _ (by omega))
    (fun t ht => hok₁ _ (by omega) (by omega))
  rw [add_zero] at h2
  rw [show (72 : ℕ) = 66 + 6 from rfl, wmat_add, ← vm_mul, ← h1, ← hcut, h2]

theorem transport_orig (N : ℕ) :
    mv Lfun (2 * (N + 1 : ℕ)) (pN (N + 1)).ker = vm (mv Lfun (2 * N) (pN N).ker) (Wmat N) := by
  have hc := Cut_orig N
  have hcut : mv Lfun (2 * N + 2) (vtx N 66).ker = mv Lfun (2 * N) (vtx N 66).ker := by
    rw [show (2 * N + 2 : ℤ) = 2 * N + 1 + 1 by ring, mv_cut isMom_Lfun _ _ hc.2 (by omega),
      mv_cut isMom_Lfun _ _ hc.1 (by omega)]
  have := transport_gen isMom_Lfun edge (vtx N) (vtx_succ N) (2 * N) (2 * N + 2)
    (ok_orig_a N) hcut (ok_orig_b N)
  rw [vtx_72, vtx_zero] at this
  rw [show (2 * ((N + 1 : ℕ) : ℤ)) = 2 * N + 2 by push_cast; ring]
  exact this

theorem transport_dualM (N : ℕ) :
    mv Mfun (2 * (N + 1 : ℕ)) (pN (N + 1)).dual.ker =
      vm (mv Mfun (2 * N) (pN N).dual.ker) (Dmat N) := by
  have hc := Cut_dualM N
  have hcut : mv Mfun (2 * N + 2) (dvtx N 66).ker = mv Mfun (2 * N) (dvtx N 66).ker := by
    show mv Mfun (2 * N + 2) (vtx N 66).dual.ker = mv Mfun (2 * N) (vtx N 66).dual.ker
    rw [show (2 * N + 2 : ℤ) = 2 * N + 1 + 1 by ring, mv_cut isMom_Mfun _ _ hc.2 (by omega),
      mv_cut isMom_Mfun _ _ hc.1 (by omega)]
  have := transport_gen isMom_Mfun dedge (dvtx N) (dvtx_succ N) (2 * N) (2 * N + 2)
    (ok_dualM_a N) hcut (ok_dualM_b N)
  rw [dvtx, dvtx, vtx_72, vtx_zero] at this
  rw [show (2 * ((N + 1 : ℕ) : ℤ)) = 2 * N + 2 by push_cast; ring]
  exact this

theorem transport_dualL (N : ℕ) :
    mv Lfun ((N + 1 : ℕ) : ℤ) (pN (N + 1)).dual.ker =
      vm (mv Lfun (N : ℤ) (pN N).dual.ker) (Dmat N) := by
  have hcut : mv Lfun ((N : ℤ) + 1) (dvtx N 66).ker = mv Lfun (N : ℤ) (dvtx N 66).ker := by
    show mv Lfun ((N : ℤ) + 1) (vtx N 66).dual.ker = mv Lfun (N : ℤ) (vtx N 66).dual.ker
    exact mv_cut isMom_Lfun _ _ (Cut_dualL N) (by omega)
  have := transport_gen isMom_Lfun dedge (dvtx N) (dvtx_succ N) (N : ℤ) ((N : ℤ) + 1)
    (ok_dualL_a N) hcut (ok_dualL_b N)
  rw [dvtx, dvtx, vtx_72, vtx_zero] at this
  rw [show ((N + 1 : ℕ) : ℤ) = N + 1 by push_cast; ring]
  exact this

end ZetasIrr.CMF
