/-
# The blocks of the walk and their exact entries

`Wmat N` is the product of the twelve six-step blocks `blockW b N`. Each block is computed
exactly by `runBlock` (`blockW_row`); by the certificates `GW_cert0`–`GW_cert5` and
`check_all`, every block has last row `(0, 0, 0, 1)` and upper-left entries
`N_{b,ij}(N) / D_b(N)`. Hence `blk (Wmat N)` is the product of the twelve blocks
`blk (blockW b N)` (`blk_Wmat`).
-/
import GW_poly
import GW_cert0
import GW_cert1
import GW_cert2
import GW_cert3
import GW_cert4
import GW_cert5
import CMF_main

open Matrix ZetasIrr.CMF

namespace ZetasIrr.GW

/-! ### The step data of the walk -/

def ckOf (e : Edge) : ℤ := if e.isA then ![11, 12, -16, -17, 10] e.i else ![0, 1, 2, -1, -2] e.i

def ccOf (e : Edge) (o : Off) : ℤ :=
  (if e.isA then ![1, 1, 0, 0, 2] e.i + o.vecA e.i else o.vecB e.i) - (if e.up then 0 else 1)

def srcOff (e : Edge) (o : Off) : Off := if e.isA != e.up then o else applyOff e o

def sdOf (e : Edge) (o : Off) : SD :=
  ⟨e.isA != e.up, (srcOff e o).a0, (srcOff e o).a1, (srcOff e o).a2 - 1, (srcOff e o).a3 - 1,
    (srcOff e o).a4 + 1, (srcOff e o).b0, (srcOff e o).b1, (srcOff e o).b2, (srcOff e o).b3,
    (srcOff e o).b4, ckOf e, ccOf e o⟩

theorem blockSD_eq : ∀ b < 12,
    blockSD b = (List.range 6).map fun k => sdOf (edge (6 * b + k)) (off (6 * b + k)) := by
  decide +kernel

theorem fwd_sdOf (e : Edge) (o : Off) : (sdOf e o).fwd = true ↔ e.fwd := by
  simp [sdOf, Edge.fwd]

theorem src_toPt (e : Edge) (o : Off) (n : ℕ) : e.src (o.toPt n) = (srcOff e o).toPt n := by
  by_cases h : e.fwd
  · rw [Edge.src, if_pos h, srcOff, if_pos (by simpa using h)]
  · rw [Edge.src, if_neg h, srcOff, if_neg (by simpa using h), apply_toPt]

/-! ### Coefficients of the points of the walk -/

def dq (D : DC) : Fin 5 → ℚ := ![D.d0, D.d1, D.d2, D.d3, D.d4]

def V4.q (v : V4) : Fin 4 → ℚ := ![(v.x0 : ℚ), v.x1, v.x2, v.x3]

theorem e_vec (a b c d e : ℚ) : e1 ![a, b, c, d, e] = a + b + c + d + e ∧
    e2 ![a, b, c, d, e] = a * b + a * c + a * d + a * e + b * c + b * d + b * e + c * d +
      c * e + d * e ∧
    e3 ![a, b, c, d, e] = a * b * c + a * b * d + a * b * e + a * c * d + a * c * e + a * d * e +
      b * c * d + b * c * e + b * d * e + c * d * e ∧
    e4 ![a, b, c, d, e] = a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e +
      b * c * d * e ∧
    e5 ![a, b, c, d, e] = a * b * c * d * e := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem e_cast (w0 w1 w2 w3 w4 : ℤ) :
    e1 ![(w0 : ℚ), w1, w2, w3, w4] = (esym w0 w1 w2 w3 w4).e1 ∧
    e2 ![(w0 : ℚ), w1, w2, w3, w4] = (esym w0 w1 w2 w3 w4).e2 ∧
    e3 ![(w0 : ℚ), w1, w2, w3, w4] = (esym w0 w1 w2 w3 w4).e3 ∧
    e4 ![(w0 : ℚ), w1, w2, w3, w4] = (esym w0 w1 w2 w3 w4).e4 ∧
    e5 ![(w0 : ℚ), w1, w2, w3, w4] = (esym w0 w1 w2 w3 w4).e5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := e_vec (w0 : ℚ) w1 w2 w3 w4
  rw [h1, h2, h3, h4, h5]
  simp only [esym, E5.push]
  push_cast
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

theorem baseA_eq (n : ℕ) (i : Fin 5) :
    baseA n i = ![11, 12, -16, -17, 10] i * (n : ℤ) + ![1, 1, 0, 0, 2] i := by
  fin_cases i <;> simp [baseA] <;> ring

theorem baseB_eq (n : ℕ) (j : Fin 5) : baseB n j = ![0, 1, 2, -1, -2] j * (n : ℤ) := by
  fin_cases j <;> simp [baseB]

theorem al_toPt (o : Off) (n : ℕ) : al (o.toPt n).a = ![((11 * n + o.a0 : ℤ) : ℚ),
    ((12 * n + o.a1 : ℤ) : ℚ), ((-16 * n + (o.a2 - 1) : ℤ) : ℚ), ((-17 * n + (o.a3 - 1) : ℤ) : ℚ),
    ((10 * n + (o.a4 + 1) : ℤ) : ℚ)] := by
  funext i
  fin_cases i <;> simp [al, toPt_a, baseA, Off.vecA] <;> ring

theorem bq_toPt (o : Off) (n : ℕ) : bq (o.toPt n).b = ![(o.b0 : ℚ), ((n + o.b1 : ℤ) : ℚ),
    ((2 * n + o.b2 : ℤ) : ℚ), ((-n + o.b3 : ℤ) : ℚ), ((-2 * n + o.b4 : ℤ) : ℚ)] := by
  funext j
  fin_cases j <;> simp [bq, toPt_b, baseB, Off.vecB]

theorem dc_toPt (o : Off) (n : ℕ) (f : Bool) (ck cc : ℤ) :
    (o.toPt n).dc = dq (sdDC n ⟨f, o.a0, o.a1, o.a2 - 1, o.a3 - 1, o.a4 + 1, o.b0, o.b1, o.b2,
      o.b3, o.b4, ck, cc⟩) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := e_cast (11 * n + o.a0) (12 * n + o.a1) (-16 * n + (o.a2 - 1))
    (-17 * n + (o.a3 - 1)) (10 * n + (o.a4 + 1))
  obtain ⟨b1, b2, b3, b4, b5⟩ := e_cast o.b0 (n + o.b1) (2 * n + o.b2) (-n + o.b3) (-2 * n + o.b4)
  rw [Pt.dc, CMF.dc, al_toPt, bq_toPt, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5]
  simp only [dq, sdDC, mkDC, Int.cast_sub]

theorem cval_toPt (e : Edge) (o : Off) (n : ℕ) :
    e.cval (o.toPt n) = (sdDC n (sdOf e o)).c := by
  show _ = ckOf e * n + ccOf e o
  rcases e with ⟨isA, i, up⟩
  cases isA
  · simp only [Edge.cval, toPt_b, baseB_eq, ckOf, ccOf, Bool.false_eq_true, ite_false]; ring
  · simp only [Edge.cval, toPt_a, baseA_eq, ckOf, ccOf, ite_true]; ring

/-! ### The step matrices acting on rows -/

theorem vecMul_Amat (v : Fin 4 → ℚ) (d : Fin 5 → ℚ) (c : ℚ) :
    vecMul v (Amat d c) = ![v 0 * c - v 1, v 1 * c - v 2, v 2 * c - v 3,
      v 0 * (d 0 / d 4) + v 1 * (d 1 / d 4) + v 2 * (d 2 / d 4) + v 3 * (c + d 3 / d 4)] := by
  funext j
  rw [vecMul, dotProduct, Fin.sum_univ_four]
  fin_cases j
  · show v 0 * c + v 1 * (-1) + v 2 * 0 + v 3 * 0 = v 0 * c - v 1; ring
  · show v 0 * 0 + v 1 * c + v 2 * (-1) + v 3 * 0 = v 1 * c - v 2; ring
  · show v 0 * 0 + v 1 * 0 + v 2 * c + v 3 * (-1) = v 2 * c - v 3; ring
  · rfl

theorem fwd_vecMul (D : DC) (v : V4) (hd : (D.d4 : ℚ) ≠ 0) :
    vecMul v.q (Amat (dq D) D.c) = (D.d4 : ℚ)⁻¹ • (fwdRow D (D.d4 * D.c) v).q := by
  rw [vecMul_Amat]
  funext j
  fin_cases j
  · show (v.x0 : ℚ) * D.c - v.x1 = (D.d4 : ℚ)⁻¹ * ((v.x0 * (D.d4 * D.c) - v.x1 * D.d4 : ℤ) : ℚ)
    push_cast; field_simp
  · show (v.x1 : ℚ) * D.c - v.x2 = (D.d4 : ℚ)⁻¹ * ((v.x1 * (D.d4 * D.c) - v.x2 * D.d4 : ℤ) : ℚ)
    push_cast; field_simp
  · show (v.x2 : ℚ) * D.c - v.x3 = (D.d4 : ℚ)⁻¹ * ((v.x2 * (D.d4 * D.c) - v.x3 * D.d4 : ℤ) : ℚ)
    push_cast; field_simp
  · show (v.x0 : ℚ) * (D.d0 / D.d4) + v.x1 * (D.d1 / D.d4) + v.x2 * (D.d2 / D.d4) +
        v.x3 * (D.c + D.d3 / D.d4) = (D.d4 : ℚ)⁻¹ * ((v.x0 * D.d0 + v.x1 * D.d1 + v.x2 * D.d2 +
          v.x3 * (D.d4 * D.c + D.d3) : ℤ) : ℚ)
    push_cast; field_simp

theorem bwd_vecMul (D : DC) (v : V4) (hd : (D.d4 : ℚ) ≠ 0) :
    vecMul (bwdRow D (mkHH D) v).q (Amat (dq D) D.c) = ((mkHH D).dv : ℚ) • v.q := by
  rw [vecMul_Amat]
  funext j
  fin_cases j
  · show ((bwdRow D (mkHH D) v).x0 : ℚ) * D.c - (bwdRow D (mkHH D) v).x1 = (mkHH D).dv * v.x0
    exact_mod_cast (show (bwdRow D (mkHH D) v).x0 * D.c - (bwdRow D (mkHH D) v).x1 =
      (mkHH D).dv * v.x0 by simp only [bwdRow, bwdRow3]; ring)
  · show ((bwdRow D (mkHH D) v).x1 : ℚ) * D.c - (bwdRow D (mkHH D) v).x2 = (mkHH D).dv * v.x1
    exact_mod_cast (show (bwdRow D (mkHH D) v).x1 * D.c - (bwdRow D (mkHH D) v).x2 =
      (mkHH D).dv * v.x1 by simp only [bwdRow, bwdRow3]; ring)
  · show ((bwdRow D (mkHH D) v).x2 : ℚ) * D.c - (bwdRow D (mkHH D) v).x3 = (mkHH D).dv * v.x2
    exact_mod_cast (show (bwdRow D (mkHH D) v).x2 * D.c - (bwdRow D (mkHH D) v).x3 =
      (mkHH D).dv * v.x2 by simp only [bwdRow, bwdRow3]; ring)
  · show ((bwdRow D (mkHH D) v).x0 : ℚ) * (D.d0 / D.d4) +
        (bwdRow D (mkHH D) v).x1 * (D.d1 / D.d4) + (bwdRow D (mkHH D) v).x2 * (D.d2 / D.d4) +
        (bwdRow D (mkHH D) v).x3 * (D.c + D.d3 / D.d4) = (mkHH D).dv * v.x3
    simp only [bwdRow, bwdRow3, mkHH, mkHH3]
    push_cast
    field_simp
    ring

def scalZ (sd : SD) (n : ℕ) : ℤ := if sd.fwd then (sdDC n sd).d4 else (mkHH (sdDC n sd)).dv

def St.row (S : St) : Fin 4 → V4 := ![S.r0, S.r1, S.r2, S.r3]

theorem step_row_fwd (n : ℕ) (S : St) (sd : SD) (h : sd.fwd = true) (i : Fin 4) :
    (step n S sd).row i = fwdRow (sdDC n sd) ((sdDC n sd).d4 * (sdDC n sd).c) (S.row i) := by
  simp only [step, stepD, h, ite_true]; fin_cases i <;> rfl

theorem step_row_bwd (n : ℕ) (S : St) (sd : SD) (h : sd.fwd = false) (i : Fin 4) :
    (step n S sd).row i = bwdRow (sdDC n sd) (mkHH (sdDC n sd)) (S.row i) := by
  simp only [step, stepD, h, Bool.false_eq_true, ite_false]; fin_cases i <;> rfl

theorem step_s (n : ℕ) (S : St) (sd : SD) : (step n S sd).s = S.s * scalZ sd n := by
  simp only [step, stepD, scalZ]; cases sd.fwd <;> rfl

/-- **One step of the walk acting on a row.** -/
theorem step_vecMul (n t : ℕ) (ht : t < 72) (S : St) (i : Fin 4) :
    vecMul (S.row i).q ((edge t).mat (vtx n t)) =
      ((scalZ (sdOf (edge t) (off t)) n : ℚ))⁻¹ • ((step n S (sdOf (edge t) (off t))).row i).q ∧
    scalZ (sdOf (edge t) (off t)) n ≠ 0 := by
  set e := edge t
  set sd := sdOf e (off t)
  set D := sdDC n sd
  have hdc : (e.src (vtx n t)).dc = dq D := by rw [vtx, src_toPt, dc_toPt]; rfl
  have hc : ((e.cval (vtx n t) : ℤ) : ℚ) = D.c := by rw [vtx, cval_toPt]
  have h4 : (e.src (vtx n t)).dc 4 ≠ 0 := by
    rw [src_eq]; split_ifs
    · exact dc4_vtx n t (by omega)
    · rw [← vtx_succ n t ht]; exact dc4_vtx n (t + 1) ht
  have hd4 : (D.d4 : ℚ) ≠ 0 := by rw [hdc] at h4; exact h4
  by_cases hf : e.fwd
  · have hs : sd.fwd = true := (fwd_sdOf _ _).mpr hf
    rw [Edge.mat, if_pos hf, hdc, hc, fwd_vecMul D _ hd4, step_row_fwd n S sd hs, scalZ, if_pos hs]
    exact ⟨rfl, by exact_mod_cast hd4⟩
  · have hs : sd.fwd = false := by
      cases h : sd.fwd
      · rfl
      · exact absurd ((fwd_sdOf _ _).mp h) hf
    have hsrc : e.src (vtx n t) = e.apply (vtx n t) := if_neg hf
    have hD := inv_walk n t ht hf
    rw [← hsrc] at hD
    have hu := isUnit_det_Amat _ _ _ h4 hD
    have hdv : Deval (e.src (vtx n t)).a (e.src (vtx n t)).b (e.cval (vtx n t)) = (mkHH D).dv := by
      have h' : CMF.dc (e.src (vtx n t)).a (e.src (vtx n t)).b = dq D := hdc
      rw [Deval, h', hc]
      show (D.d0 : ℚ) + D.d1 * D.c + D.d2 * D.c ^ 2 + D.d3 * D.c ^ 3 + D.d4 * D.c ^ 4 = _
      simp only [mkHH, mkHH3]
      push_cast
      ring
    have hv : ((mkHH D).dv : ℚ) ≠ 0 := by rw [← hdv]; exact hD
    have key := bwd_vecMul D (S.row i) hd4
    rw [← hdc, ← hc] at key
    rw [Edge.mat, if_neg hf, step_row_bwd n S sd hs i, scalZ, if_neg (by rw [hs]; exact Bool.false_ne_true)]
    refine ⟨?_, by exact_mod_cast hv⟩
    calc vecMul (S.row i).q (Amat (e.src (vtx n t)).dc (e.cval (vtx n t)))⁻¹
        = ((mkHH D).dv : ℚ)⁻¹ • (((mkHH D).dv : ℚ) •
          vecMul (S.row i).q (Amat (e.src (vtx n t)).dc (e.cval (vtx n t)))⁻¹) := by
          rw [inv_smul_smul₀ hv]
      _ = ((mkHH D).dv : ℚ)⁻¹ • (bwdRow D (mkHH D) (S.row i)).q := by
          rw [← Matrix.smul_vecMul, ← key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _
            (show IsUnit (Amat (e.src (vtx n t)).dc (e.cval (vtx n t))).det from hu),
            Matrix.vecMul_one]

/-! ### The blocks -/

noncomputable def blockW (b n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  wmat (fun t => edge (6 * b + t)) (fun t => vtx n (6 * b + t)) 6

def runT (n b T : ℕ) : St :=
  ((List.range T).map fun k => sdOf (edge (6 * b + k)) (off (6 * b + k))).foldl (step n) St.init

theorem wmat_runT (n b : ℕ) (hb : b < 12) (T : ℕ) (hT : T ≤ 6) :
    (∀ i, wmat (fun t => edge (6 * b + t)) (fun t => vtx n (6 * b + t)) T i =
      ((runT n b T).s : ℚ)⁻¹ • ((runT n b T).row i).q) ∧ (runT n b T).s ≠ 0 := by
  induction T with
  | zero =>
    refine ⟨fun i => ?_, by simp [runT, St.init]⟩
    funext j
    rw [wmat_zero, show runT n b 0 = St.init from rfl]
    simp only [St.init, Int.cast_one, inv_one, one_smul]
    fin_cases i <;> fin_cases j <;> rfl
  | succ T ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hr : runT n b (T + 1) = step n (runT n b T) (sdOf (edge (6 * b + T)) (off (6 * b + T))) := by
      simp only [runT, List.range_succ, List.map_append, List.foldl_append, List.map_singleton,
        List.foldl_cons, List.foldl_nil]
    have hm := step_vecMul n (6 * b + T) (by omega) (runT n b T)
    refine ⟨fun i => ?_, ?_⟩
    · rw [wmat_succ, hr, step_s]
      show vecMul _ _ = _
      rw [ih1, Matrix.smul_vecMul, (hm i).1, smul_smul, Int.cast_mul, mul_inv]
    · rw [hr, step_s]; exact mul_ne_zero ih2 (hm 0).2

theorem runT_six (n b : ℕ) (hb : b < 12) : runT n b 6 = runBlock n b := by
  rw [runT, runBlock, blockSD_eq b hb]

theorem checks : ∀ b < 12, ∀ k : Fin 36, check b k = true := by
  have h : ∀ k : Fin 36, (k : ℤ) ∈ ([0, 1, 2, 3, 4, 5] : List ℤ) ∨
      (k : ℤ) ∈ ([6, 7, 8, 9, 10, 11] : List ℤ) ∨ (k : ℤ) ∈ ([12, 13, 14, 15, 16, 17] : List ℤ) ∨
      (k : ℤ) ∈ ([18, 19, 20, 21, 22, 23] : List ℤ) ∨ (k : ℤ) ∈ ([24, 25, 26, 27, 28, 29] : List ℤ) ∨
      (k : ℤ) ∈ ([30, 31, 32, 33, 34, 35] : List ℤ) := by
    decide
  have hb : ∀ b < 12, b ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List ℕ) := by decide
  intro b hb12 k
  have A := fun (l : List ℤ) (hl : checkAll l = true) (hk : (k : ℤ) ∈ l) =>
    List.all_eq_true.mp (List.all_eq_true.mp hl b (hb b hb12)) _ hk
  rcases h k with h | h | h | h | h | h
  · exact A _ checkAll_0 h
  · exact A _ checkAll_1 h
  · exact A _ checkAll_2 h
  · exact A _ checkAll_3 h
  · exact A _ checkAll_4 h
  · exact A _ checkAll_5 h

theorem blockW_row (n b : ℕ) (hb : b < 12) (i : Fin 4) :
    blockW b n i = ((runBlock n b).s : ℚ)⁻¹ • ((runBlock n b).row i).q ∧ (runBlock n b).s ≠ 0 := by
  rw [← runT_six n b hb]
  exact ⟨(wmat_runT n b hb 6 le_rfl).1 i, (wmat_runT n b hb 6 le_rfl).2⟩

theorem lastRow_blockW (n b : ℕ) (hb : b < 12) : lastRow (blockW b n) := by
  have h := ((blockOK_iff _ _ _).mp (check_all checks hb n)).2
  obtain ⟨hr, hs⟩ := blockW_row n b hb 3
  have hs' : ((runBlock n b).s : ℚ) ≠ 0 := by exact_mod_cast hs
  intro j
  rw [hr]
  fin_cases j
  · show ((runBlock n b).s : ℚ)⁻¹ * ((runBlock n b).r3.x0 : ℚ) = 0; rw [h.1]; simp
  · show ((runBlock n b).s : ℚ)⁻¹ * ((runBlock n b).r3.x1 : ℚ) = 0; rw [h.2.1]; simp
  · show ((runBlock n b).s : ℚ)⁻¹ * ((runBlock n b).r3.x2 : ℚ) = 0; rw [h.2.2.1]; simp
  · show ((runBlock n b).s : ℚ)⁻¹ * ((runBlock n b).r3.x3 : ℚ) = 1; rw [h.2.2.2]
    exact inv_mul_cancel₀ hs'

/-- **Entries of the blocks.** -/
theorem blk_blockW (n b : ℕ) (hb : b < 12) (i j : Fin 3) (hD : peval (cert b).D n ≠ 0) :
    blk (blockW b n) i j = (peval ((cert b).N i j) n : ℚ) / peval (cert b).D n := by
  have h := ((blockOK_iff _ _ _).mp (check_all checks hb n)).1
  obtain ⟨hr, hs⟩ := blockW_row n b hb (Fin.castSucc i)
  have hs' : ((runBlock n b).s : ℚ) ≠ 0 := by exact_mod_cast hs
  have hD' : (peval (cert b).D n : ℚ) ≠ 0 := by exact_mod_cast hD
  have key : ∀ x y : ℤ, x * peval (cert b).D n = y * (runBlock n b).s →
      ((runBlock n b).s : ℚ)⁻¹ * x = y / peval (cert b).D n := by
    intro x y hxy
    rw [inv_mul_eq_div, div_eq_div_iff hs' hD']
    exact_mod_cast hxy
  rw [blk, Matrix.submatrix_apply, hr, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · exact key _ _ h.1
  · exact key _ _ h.2.1
  · exact key _ _ h.2.2.1
  · exact key _ _ h.2.2.2.1
  · exact key _ _ h.2.2.2.2.1
  · exact key _ _ h.2.2.2.2.2.1
  · exact key _ _ h.2.2.2.2.2.2.1
  · exact key _ _ h.2.2.2.2.2.2.2.1
  · exact key _ _ h.2.2.2.2.2.2.2.2

theorem wmat_blocks (n m : ℕ) :
    wmat edge (vtx n) (6 * m) = ((List.range m).map fun b => blockW b n).prod := by
  induction m with
  | zero => rw [List.range_zero, List.map_nil, List.prod_nil]; exact wmat_zero _ _
  | succ m ih =>
    rw [show 6 * (m + 1) = 6 * m + 6 by ring, wmat_add, ih, List.range_succ, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]
    rfl

/-- **`blk (Wmat N)` is the product of the twelve blocks.** -/
theorem blk_Wmat (n : ℕ) :
    blk (Wmat n) = ((List.range 12).map fun b => blk (blockW b n)).prod := by
  have key : ∀ m ≤ 12, blk (((List.range m).map fun b => blockW b n).prod) =
      ((List.range m).map fun b => blk (blockW b n)).prod := by
    intro m hm
    induction m with
    | zero =>
      ext i j
      simp only [List.range_zero, List.map_nil, List.prod_nil, blk, Matrix.submatrix_apply,
        Matrix.one_apply, Fin.castSucc_inj]
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
        List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton,
        blk_mul _ _ (lastRow_blockW n m (by omega)), ih (by omega)]
  rw [Wmat, show (72 : ℕ) = 6 * 12 from rfl, wmat_blocks, key 12 le_rfl]

end ZetasIrr.GW
