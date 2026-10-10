/-
# Polynomiality of the block evaluations

`PD f d`: the function `f : ℤ → ℤ` is a polynomial of degree `≤ d` (the zero polynomial if
`d < 0`). Along a block of three forward and three backward steps the entry `(i, j)` of
`runBlock n b` has degree `≤ 18 + j - i` and the scalar has degree `≤ 15`, so each of the
thirteen identities of `blockOK` is a polynomial identity of degree `≤ 35`; it holds for all
`n` as soon as it holds for `n = 0, …, 35`.
-/
import GW_fast
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace ZetasIrr.GW

def PD (f : ℤ → ℤ) (d : ℤ) : Prop :=
  ∃ p : ℤ[X], (p = 0 ∨ (p.natDegree : ℤ) ≤ d) ∧ ∀ n, f n = p.eval n

theorem PD.mono {f : ℤ → ℤ} {d d' : ℤ} (h : PD f d) (hd : d ≤ d') : PD f d' := by
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p, hp.imp_right fun h => h.trans hd, he⟩

theorem PD.zero (d : ℤ) : PD (fun _ => 0) d := ⟨0, Or.inl rfl, fun n => by rw [eval_zero]⟩

theorem PD.const (c : ℤ) {d : ℤ} (hd : 0 ≤ d) : PD (fun _ => c) d :=
  ⟨C c, Or.inr (by rw [natDegree_C]; exact hd), fun n => by rw [eval_C]⟩

theorem PD.lin (k c : ℤ) : PD (fun n => k * n + c) 1 :=
  ⟨C k * X + C c, Or.inr (by
    have := natDegree_linear_le (a := k) (b := c)
    exact_mod_cast this), fun n => by rw [eval_add, eval_mul, eval_C, eval_X, eval_C]⟩

theorem PD.add {f g : ℤ → ℤ} {d : ℤ} (hf : PD f d) (hg : PD g d) :
    PD (fun n => f n + g n) d := by
  obtain ⟨p, hp, hpe⟩ := hf
  obtain ⟨q, hq, hqe⟩ := hg
  refine ⟨p + q, ?_, fun n => by show f n + g n = _; rw [eval_add, hpe, hqe]⟩
  rcases hp with rfl | hp
  · rw [zero_add]; exact hq
  rcases hq with rfl | hq
  · rw [add_zero]; exact Or.inr hp
  refine Or.inr ((Nat.cast_le.mpr (natDegree_add_le p q)).trans ?_)
  rw [Nat.cast_max]; exact max_le hp hq

theorem PD.neg {f : ℤ → ℤ} {d : ℤ} (hf : PD f d) : PD (fun n => -f n) d := by
  obtain ⟨p, hp, hpe⟩ := hf
  refine ⟨-p, ?_, fun n => by show -f n = _; rw [eval_neg, hpe]⟩
  rcases hp with rfl | hp
  · rw [neg_zero]; exact Or.inl rfl
  · rw [natDegree_neg]; exact Or.inr hp

theorem PD.sub {f g : ℤ → ℤ} {d : ℤ} (hf : PD f d) (hg : PD g d) :
    PD (fun n => f n - g n) d := by
  have := hf.add hg.neg
  simp only [← sub_eq_add_neg] at this
  exact this

theorem PD.mul {f g : ℤ → ℤ} {a b : ℤ} (hf : PD f a) (hg : PD g b) :
    PD (fun n => f n * g n) (a + b) := by
  obtain ⟨p, hp, hpe⟩ := hf
  obtain ⟨q, hq, hqe⟩ := hg
  refine ⟨p * q, ?_, fun n => by show f n * g n = _; rw [eval_mul, hpe, hqe]⟩
  rcases hp with rfl | hp
  · rw [zero_mul]; exact Or.inl rfl
  rcases hq with rfl | hq
  · rw [mul_zero]; exact Or.inl rfl
  refine Or.inr ((Nat.cast_le.mpr natDegree_mul_le).trans ?_)
  rw [Nat.cast_add]; exact add_le_add hp hq

theorem PD.mul' {f g : ℤ → ℤ} {a b d : ℤ} (hf : PD f a) (hg : PD g b) (h : a + b ≤ d) :
    PD (fun n => f n * g n) d := (hf.mul hg).mono h

/-- A polynomial identity of degree `≤ 35` that holds at `0, …, 35` holds everywhere. -/
theorem PD.eq_zero {f : ℤ → ℤ} (hf : PD f 35) (h : ∀ k : Fin 36, f k = 0) (n : ℤ) : f n = 0 := by
  obtain ⟨p, hp, hpe⟩ := hf
  rcases hp with rfl | hp
  · rw [hpe, eval_zero]
  rw [hpe, eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := fun k : Fin 36 => (k : ℤ))
    (fun a b hab => Fin.ext (by simpa using hab)) (fun k => by rw [← hpe]; exact h k)
    (by rw [Fintype.card_fin]; omega), eval_zero]

/-! ### Degrees of the step data -/

/-- Degrees `1, …, 5` of the elementary symmetric functions. -/
def PE (E : ℤ → E5) : Prop :=
  PD (fun n => (E n).e1) 1 ∧ PD (fun n => (E n).e2) 2 ∧ PD (fun n => (E n).e3) 3 ∧
    PD (fun n => (E n).e4) 4 ∧ PD (fun n => (E n).e5) 5

theorem PE.push {E : ℤ → E5} {v : ℤ → ℤ} (hE : PE E) (hv : PD v 1) :
    PE (fun n => (E n).push (v n)) :=
  ⟨hE.1.add hv, hE.2.1.add (hE.1.mul hv), hE.2.2.1.add (hE.2.1.mul hv),
    hE.2.2.2.1.add (hE.2.2.1.mul hv), hE.2.2.2.2.add (hE.2.2.2.1.mul hv)⟩

theorem PE.esym {v0 v1 v2 v3 v4 : ℤ → ℤ} (h0 : PD v0 1) (h1 : PD v1 1) (h2 : PD v2 1)
    (h3 : PD v3 1) (h4 : PD v4 1) :
    PE (fun n => esym (v0 n) (v1 n) (v2 n) (v3 n) (v4 n)) := by
  have h : PE (fun n => E5.mk (v0 n) 0 0 0 0) :=
    ⟨h0, PD.zero _, PD.zero _, PD.zero _, PD.zero _⟩
  exact (((h.push h1).push h2).push h3).push h4

theorem sdDC_d4 (n : ℤ) (sd : SD) :
    (sdDC n sd).d4 = sd.b0 + sd.b1 + sd.b2 + sd.b3 + sd.b4 - (sd.a0 + sd.a1 + sd.a2 + sd.a3 + sd.a4) := by
  simp only [sdDC, mkDC, esym, E5.push]
  ring

/-- Degrees of `d₀, …, d₄` and `c` as functions of `n`. -/
structure PDC (sd : SD) : Prop where
  d0 : PD (fun n => (sdDC n sd).d0) 5
  d1 : PD (fun n => (sdDC n sd).d1) 4
  d2 : PD (fun n => (sdDC n sd).d2) 3
  d3 : PD (fun n => (sdDC n sd).d3) 2
  d4 : PD (fun n => (sdDC n sd).d4) 0
  c : PD (fun n => (sdDC n sd).c) 1

theorem pdc (sd : SD) : PDC sd := by
  have hA := PE.esym (PD.lin 11 sd.a0) (PD.lin 12 sd.a1) (PD.lin (-16) sd.a2)
    (PD.lin (-17) sd.a3) (PD.lin 10 sd.a4)
  have hB := PE.esym (PD.const sd.b0 zero_le_one) (by simpa using PD.lin 1 sd.b1)
    (PD.lin 2 sd.b2) (by simpa using PD.lin (-1) sd.b3) (PD.lin (-2) sd.b4)
  refine ⟨hB.2.2.2.2.sub hA.2.2.2.2, hA.2.2.2.1.sub hB.2.2.2.1, hB.2.2.1.sub hA.2.2.1,
    hA.2.1.sub hB.2.1, ?_, PD.lin sd.ck sd.cc⟩
  simp only [sdDC_d4]
  exact PD.const _ le_rfl

/-! ### The invariant along a block -/

/-- Row `i` with offset `e = σ - i`: entry `j` has degree `≤ e + j`. -/
def InvR (v : ℤ → V4) (e : ℤ) : Prop :=
  PD (fun n => (v n).x0) e ∧ PD (fun n => (v n).x1) (e + 1) ∧ PD (fun n => (v n).x2) (e + 2) ∧
    PD (fun n => (v n).x3) (e + 3)

def InvS (S : ℤ → St) (σ τ : ℤ) : Prop :=
  InvR (fun n => (S n).r0) σ ∧ InvR (fun n => (S n).r1) (σ - 1) ∧
    InvR (fun n => (S n).r2) (σ - 2) ∧ InvR (fun n => (S n).r3) (σ - 3) ∧ PD (fun n => (S n).s) τ

theorem InvR.fwd {v : ℤ → V4} {e : ℤ} (sd : SD) (hv : InvR v e) :
    InvR (fun n => fwdRow (sdDC n sd) ((sdDC n sd).d4 * (sdDC n sd).c) (v n)) (e + 2) := by
  obtain ⟨d0, d1, d2, d3, d4, c⟩ := pdc sd
  have k := d4.mul c
  obtain ⟨h0, h1, h2, h3⟩ := hv
  exact ⟨(h0.mul' k (by omega)).sub (h1.mul' d4 (by omega)),
    (h1.mul' k (by omega)).sub (h2.mul' d4 (by omega)),
    (h2.mul' k (by omega)).sub (h3.mul' d4 (by omega)),
    (((h0.mul' d0 (by omega)).add (h1.mul' d1 (by omega))).add (h2.mul' d2 (by omega))).add
      (h3.mul' (k.mono (by omega : (0 : ℤ) + 1 ≤ 2) |>.add d3) (by omega))⟩

theorem InvR.bwd {v : ℤ → V4} {e : ℤ} (sd : SD) (hv : InvR v e) :
    InvR (fun n => bwdRow (sdDC n sd) (mkHH (sdDC n sd)) (v n)) (e + 4) := by
  obtain ⟨d0, d1, d2, d3, d4, c⟩ := pdc sd
  have h3' : PD (fun n => (mkHH (sdDC n sd)).h3) 2 := d3.add (c.mul' d4 (by omega))
  have h2' : PD (fun n => (mkHH (sdDC n sd)).h2) 3 := d2.add (c.mul' h3' (by omega))
  have h1' : PD (fun n => (mkHH (sdDC n sd)).h1) 4 := d1.add (c.mul' h2' (by omega))
  have dv : PD (fun n => (mkHH (sdDC n sd)).dv) 5 := d0.add (c.mul' h1' (by omega))
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have u0 : PD (fun n => (v n).x0 * (mkHH (sdDC n sd)).h1 + (v n).x1 * (mkHH (sdDC n sd)).h2 +
      (v n).x2 * (mkHH (sdDC n sd)).h3 + (v n).x3 * (sdDC n sd).d4) (e + 4) :=
    (((h0.mul' h1' (by omega)).add (h1.mul' h2' (by omega))).add (h2.mul' h3' (by omega))).add
      (h3.mul' d4 (by omega))
  have u1 := (c.mul' u0 (by omega : 1 + (e + 4) ≤ e + 4 + 1)).sub
    (dv.mul' h0 (by omega : 5 + e ≤ e + 4 + 1))
  have u2 := (c.mul' u1 (by omega : 1 + (e + 4 + 1) ≤ e + 4 + 2)).sub
    (dv.mul' h1 (by omega : 5 + (e + 1) ≤ e + 4 + 2))
  exact ⟨u0, u1, u2, (c.mul' u2 (by omega)).sub (dv.mul' h2 (by omega))⟩

def wF (sd : SD) : ℤ := if sd.fwd then 2 else 4
def wS (sd : SD) : ℤ := if sd.fwd then 0 else 5

theorem InvS.next {S : ℤ → St} {σ τ : ℤ} (sd : SD) (h : InvS S σ τ) :
    InvS (fun n => step n (S n) sd) (σ + wF sd) (τ + wS sd) := by
  obtain ⟨r0, r1, r2, r3, hs⟩ := h
  obtain ⟨d0, d1, d2, d3, d4, c⟩ := pdc sd
  unfold step stepD wF wS
  cases sd.fwd
  · simp only [Bool.false_eq_true, ite_false]
    have dv : PD (fun n => (mkHH (sdDC n sd)).dv) 5 :=
      d0.add (c.mul' (d1.add (c.mul' (d2.add (c.mul' (d3.add (c.mul' d4 (by omega)))
        (by omega))) (by omega))) (by omega))
    exact ⟨r0.bwd sd, by simpa [sub_add_eq_add_sub] using r1.bwd sd,
      by simpa [sub_add_eq_add_sub] using r2.bwd sd, by simpa [sub_add_eq_add_sub] using r3.bwd sd,
      hs.mul dv⟩
  · simp only [ite_true]
    exact ⟨r0.fwd sd, by simpa [sub_add_eq_add_sub] using r1.fwd sd,
      by simpa [sub_add_eq_add_sub] using r2.fwd sd, by simpa [sub_add_eq_add_sub] using r3.fwd sd,
      by simpa using hs.mul d4⟩

theorem InvS.foldl (l : List SD) {S : ℤ → St} {σ τ : ℤ} (h : InvS S σ τ) :
    InvS (fun n => l.foldl (step n) (S n)) (σ + (l.map wF).sum) (τ + (l.map wS).sum) := by
  induction l generalizing S σ τ with
  | nil => simpa using h
  | cons sd l ih =>
    have := ih (h.next sd)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at this ⊢
    rwa [add_assoc, add_assoc] at this

theorem InvS.init : InvS (fun _ => St.init) 0 0 := by
  refine ⟨⟨PD.const 1 le_rfl, PD.zero _, PD.zero _, PD.zero _⟩,
    ⟨PD.zero _, PD.const 1 (by norm_num), PD.zero _, PD.zero _⟩,
    ⟨PD.zero _, PD.zero _, PD.const 1 (by norm_num), PD.zero _⟩,
    ⟨PD.zero _, PD.zero _, PD.zero _, PD.const 1 (by norm_num)⟩, PD.const 1 le_rfl⟩

theorem block_weights : ∀ b < 12, ((blockSD b).map wF).sum = 18 ∧ ((blockSD b).map wS).sum = 15 := by
  decide

theorem InvS.runBlock {b : ℕ} (hb : b < 12) : InvS (fun n => runBlock n b) 18 15 := by
  have h := InvS.init.foldl (blockSD b)
  rw [(block_weights b hb).1, (block_weights b hb).2, zero_add, zero_add] at h
  exact h

/-! ### Degrees of the certificate polynomials -/

theorem PD.pev (l : List ℤ) : PD (fun n => peval l n) (l.length - 1) := by
  induction l with
  | nil => exact PD.zero _
  | cons a l ih =>
    have e : (fun n => peval (a :: l) n) = fun n => (fun _ => a) n + (fun n => 1 * n + 0) n * peval l n := by
      funext n; simp only [peval, List.foldr_cons, one_mul, add_zero]
    rw [e, List.length_cons, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact (PD.const a (show (0 : ℤ) ≤ l.length by omega)).add
      ((PD.lin 1 0).mul' ih (show 1 + ((l.length : ℤ) - 1) ≤ l.length by omega))

theorem dec_length (x k : ℕ) : (dec x k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [dec, ih]

theorem cert_deg : ∀ b < 12, 2 ≤ (cert b).deg ∧ (cert b).deg ≤ 15 := by decide

theorem PD.certD {b : ℕ} (hb : b < 12) : PD (fun n => peval (cert b).D n) 15 := by
  have := PD.pev (cert b).D
  rw [Cert.D, dec_length] at this
  exact this.mono (by have := (cert_deg b hb).2; push_cast; omega)

theorem PD.certN {b : ℕ} (hb : b < 12) (i j : ℕ) (hi : i ≤ 2) :
    PD (fun n => peval ((cert b).N i j) n) ((cert b).deg + j - i) := by
  have := PD.pev ((cert b).N i j)
  rw [Cert.N, dec_length] at this
  exact this.mono (by have := (cert_deg b hb).1; push_cast [show i ≤ (cert b).deg + 1 + j by omega]; omega)

/-! ### From 36 points to all `n` -/

theorem PD.eq_of {f g : ℤ → ℤ} {d : ℤ} (hf : PD f d) (hg : PD g d) (hd : d ≤ 35)
    (h : ∀ k : Fin 36, f k = g k) (n : ℤ) : f n = g n :=
  sub_eq_zero.mp (PD.eq_zero ((hf.sub hg).mono hd) (fun k => sub_eq_zero.mpr (h k)) n)

theorem blockOK_iff (n : ℤ) (R : St) (C : Cert) : blockOK n R C = true ↔
    (R.r0.x0 * peval C.D n = peval (C.N 0 0) n * R.s ∧
    R.r0.x1 * peval C.D n = peval (C.N 0 1) n * R.s ∧
    R.r0.x2 * peval C.D n = peval (C.N 0 2) n * R.s ∧
    R.r1.x0 * peval C.D n = peval (C.N 1 0) n * R.s ∧
    R.r1.x1 * peval C.D n = peval (C.N 1 1) n * R.s ∧
    R.r1.x2 * peval C.D n = peval (C.N 1 2) n * R.s ∧
    R.r2.x0 * peval C.D n = peval (C.N 2 0) n * R.s ∧
    R.r2.x1 * peval C.D n = peval (C.N 2 1) n * R.s ∧
    R.r2.x2 * peval C.D n = peval (C.N 2 2) n * R.s) ∧
    R.r3.x0 = 0 ∧ R.r3.x1 = 0 ∧ R.r3.x2 = 0 ∧ R.r3.x3 = R.s := by
  simp only [blockOK, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- **The block identities for all `n`**, from the checks at `n = 0, …, 35`. -/
theorem check_all (hc : ∀ b < 12, ∀ k : Fin 36, check b k = true) {b : ℕ} (hb : b < 12) (n : ℤ) :
    check b n = true := by
  have H := InvS.runBlock hb
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨e0, e1, e2, e3⟩, hs⟩ := H
  have hD := PD.certD hb
  have hdeg := cert_deg b hb
  have hk := fun k : Fin 36 => (blockOK_iff _ _ _).mp (hc b hb k)
  have E : ∀ (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (P : ℤ → ℤ), PD P (18 + j - i) →
      (∀ k : Fin 36, P k * peval (cert b).D k = peval ((cert b).N i j) k * (runBlock k b).s) →
      P n * peval (cert b).D n = peval ((cert b).N i j) n * (runBlock n b).s := by
    intro i j hi hj P hP h
    exact PD.eq_of (f := fun n => P n * peval (cert b).D n)
      (g := fun n => peval ((cert b).N i j) n * (runBlock n b).s)
      (hP.mul hD) ((PD.certN hb i j hi).mul' hs (by omega)) (by omega) h n
  rw [check, blockOK_iff]
  refine ⟨⟨E 0 0 (by omega) (by omega) _ (a0.mono (by omega)) (fun k => (hk k).1.1),
    E 0 1 (by omega) (by omega) _ (a1.mono (by omega)) (fun k => (hk k).1.2.1),
    E 0 2 (by omega) (by omega) _ (a2.mono (by omega)) (fun k => (hk k).1.2.2.1),
    E 1 0 (by omega) (by omega) _ (b0.mono (by omega)) (fun k => (hk k).1.2.2.2.1),
    E 1 1 (by omega) (by omega) _ (b1.mono (by omega)) (fun k => (hk k).1.2.2.2.2.1),
    E 1 2 (by omega) (by omega) _ (b2.mono (by omega)) (fun k => (hk k).1.2.2.2.2.2.1),
    E 2 0 (by omega) (by omega) _ (c0.mono (by omega)) (fun k => (hk k).1.2.2.2.2.2.2.1),
    E 2 1 (by omega) (by omega) _ (c1.mono (by omega)) (fun k => (hk k).1.2.2.2.2.2.2.2.1),
    E 2 2 (by omega) (by omega) _ (c2.mono (by omega)) (fun k => (hk k).1.2.2.2.2.2.2.2.2)⟩,
    ?_, ?_, ?_, ?_⟩
  · exact PD.eq_of (d := 35) (g := fun _ => 0) (e0.mono (by omega)) (PD.zero _) le_rfl
      (fun k => (hk k).2.1) n
  · exact PD.eq_of (d := 35) (g := fun _ => 0) (e1.mono (by omega)) (PD.zero _) le_rfl
      (fun k => (hk k).2.2.1) n
  · exact PD.eq_of (d := 35) (g := fun _ => 0) (e2.mono (by omega)) (PD.zero _) le_rfl
      (fun k => (hk k).2.2.2.1) n
  · exact PD.eq_of (d := 35) (e3.mono (by omega)) (hs.mono (by omega)) le_rfl (fun k => (hk k).2.2.2.2) n

end ZetasIrr.GW
