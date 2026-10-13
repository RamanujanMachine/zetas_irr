/-
# Blueprint of `error_bound` (manuscript Theorem `z34-limit` with (walk-readout))

Node `Pfq54.error_bound` of `Blueprint_pfq54.lean`: for all `A, B ∈ ℤ`,
`|A ζ(3) + B ζ(4) - r_n(A,B)| ≤ ε^n` for all large `n`, `ε = 102/10⁵¹`.

The forward `₅F₄` matrix `F(n) = F_{x₀,v_F}(n)` and the dual Meijer-G matrix
`G(n) = G_{y₀,v_G}(n)` are produced by the CMF construction (`ramanujantools`) and are not
printed in the manuscript. They enter only through [1], which packages the exact identities that
the certificate scripts verify, and the readout bridge (walk-readout). All other matrices are the
explicit ones of Proposition `z34-coboundary`.

Proof (manuscript Appendix A). The rank-three intertwining `F(n) K(n+1) G(n)ᵀ = R(n) K(n)`
telescopes ([2]); with `I_F K(0) = 2 I_G` and `K(n) Jᵀ H(n)⁻¹ e₀ = e₀` ([3]) and the block form
`G(n) = [[Q(n), b(n)], [0, -1]]` this gives
`I_F W_F(N) e₀ = 2 (∏ R) Î_G W_Q(N)^{-T} H(N)⁻¹ e₀` ([4]). The restricted Meijer state solves
`Ŝ(n+1) = Ŝ(n) Q(n)` ([6]); with `meijerG_decay`, `modal_basis`, `dual_mode_transfer`,
`meijerG_initial` and `spectral_certificate` the dual ratio tends to `α_{A,B}` at rate
`ϑ < ε` ([5]). By (walk-readout) the forward ratio is `r_n(A,B)`, and the positive scalar
`2 ∏ R(n)` and `12/E_n` cancel ([7]).
-/
import Z_integral
import meijerG_initial
import meijerG_decay
import spectral_certificate
import modal_basis
import dual_mode_transfer
import dl_aux
import gdual
import mc_aux3

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- The invariant basis `E(n)` (`4 × 3`). -/
def Emat (n : ℕ) : Matrix (Fin 4) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, -(n : ℚ) * (450 * n + 29), -(n : ℚ) ^ 2 * (101250 * n ^ 2 + 12975 * n + 406);
     0, 1, 0;
     0, 0, 1]

/-- The gauge `H(n) = (h_{ij})`. -/
def Hmat (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-6 * (n : ℚ) ^ 2 * (10 * n + 1) * (12 * n + 1) * (193 * n + 13),
       -(n : ℚ) * (12 * n + 1) * (2550 * n ^ 2 + 523 * n + 23),
       (12 * (n : ℚ) + 1) * (450 * n ^ 2 + 41 * n + 1);
     (10 * (n : ℚ) + 1) * (450 * n ^ 2 + 21 * n - 1), (-25 * (n : ℚ) - 2) * (18 * n - 1), -1;
     -20 * (n : ℚ) - 2, 2, 0]

/-- `J = [I₃ 0]`. -/
def Jmat : Matrix (Fin 3) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

/-- The rank-three intertwining matrix `K(n) = E(n) H(n) J`. -/
def Kmat (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := Emat n * Hmat n * Jmat

/-- The positive scalar `R(n) = 𝔞(n)/𝔟(n)`. -/
def Rsc (n : ℕ) : ℚ :=
  1125 * ((n : ℚ) + 1) ^ 3 * (2 * n + 1) * (3 * n + 1) * (3 * n + 2) *
      (∏ j ∈ Icc (1 : ℕ) 4, (5 * (n : ℚ) + j)) *
      (∏ j ∈ ({1, 2, 4, 7, 8, 11, 13, 14} : Finset ℕ), (15 * (n : ℚ) + j)) /
    (416 * (6 * (n : ℚ) + 1) * (6 * n + 5) *
      (∏ j ∈ ({1, 5, 7, 11} : Finset ℕ), (12 * (n : ℚ) + j)) *
      (∏ j ∈ Icc (1 : ℕ) 12, (13 * (n : ℚ) + j)))

/-- `Δ(n) = ∏_{j=8}^{12} (jn + 1)`. -/
def Delta (n : ℕ) : ℚ := ∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1)

/-- `H(n)⁻¹ e₀ = Δ(n)⁻¹ (1, 10n+1, (10n+1)²)`. -/
def hvec (n : ℕ) : Fin 3 → ℚ :=
  (Delta n)⁻¹ • ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]

/-- The forward initial condition `I_F`. -/
def IF (A B : ℤ) : Matrix (Fin 2) (Fin 4) ℚ := !![0, 0, -6 * A, 3 * A - 2 * B; 12, 0, 0, 0]

/-- The dual initial condition `I_G`. -/
def IG (A B : ℤ) : Matrix (Fin 2) (Fin 4) ℚ := !![2 * B, -3 * A - 2 * B, 3 * A, 0; 0, 0, 6, 0]

/-- Its first three columns `Î_G`. -/
def IGhat (A B : ℤ) : Matrix (Fin 2) (Fin 3) ℚ := !![2 * B, -3 * A - 2 * B, 3 * A; 0, 0, 6]

/-- The projection `v = e₀`. -/
def e0 : Fin 4 → ℚ := ![1, 0, 0, 0]

/-- The leading `3 × 3` block `Q(n)` of `G(n)`. -/
def Qblock (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (G n).submatrix Fin.castSucc Fin.castSucc

/-- The dual readout `Î_G W_Q(n)^{-T} H(n)⁻¹ e₀`. -/
def dualVec (A B : ℤ) (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (n : ℕ) : Fin 2 → ℚ :=
  IGhat A B *ᵥ (((walk (Qblock G) n)⁻¹)ᵀ *ᵥ hvec n)

/-- The limiting direction `w = (1, 10, 100)ᵀ` of the balanced terminal column. -/
def wvec : Fin 3 → ℂ := ![1, 10, 100]

/-- The analytic data of the dual Meijer-G matrix: the actual Meijer-G state solves the walk;
`Q(n)` has rational-function entries without poles; the balanced limit `Q_∞` exists, has
characteristic polynomial `χ`, and the cyclic determinant `det[w, Q_∞^{-T} w, (Q_∞^{-T})² w]` is
nonzero. -/
def DualData (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ) : Prop :=
  (∀ (n : ℕ) (k : Fin 4), SG (n + 1) k = ∑ j : Fin 4, SG n j * (G n j k : ℂ)) ∧
    (∃ Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ), ∀ (n : ℕ) i j,
      (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
        Qblock G n i j = (Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ)) ∧
    ∃ Qinf : Matrix (Fin 3) (Fin 3) ℂ,
      Tendsto (fun n => balance n * (Qblock G n).map (fun x : ℚ => (x : ℂ)) *
        (balance (n + 1))⁻¹) atTop (𝓝 Qinf) ∧
      Qinf.charpoly = chi.map (algebraMap ℚ ℂ) ∧
      (Matrix.of ![wvec, (Qinf⁻¹)ᵀ *ᵥ wvec, ((Qinf⁻¹)ᵀ * (Qinf⁻¹)ᵀ) *ᵥ wvec]).det ≠ 0

/-- **[2] Telescoping the intertwining** (inverse-free): from `F(n) K(n+1) G(n)ᵀ = R(n) K(n)`,
`W_F(N) K(N) = (∏_{n<N} R(n)) K(0) W_G(N)^{-T}`.
* Estimated proof length: ≈ 25 lines (induction on `N`, `Matrix.mul_inv_rev`,
  `Matrix.transpose_mul`).
* Directly from the manuscript: yes ("This identity does not require `K(n)` to be invertible"). -/
theorem telescoped_walk (F G K : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (R : ℕ → ℚ)
    (hstep : ∀ n, F n * K (n + 1) * (G n)ᵀ = R n • K n) (hG : ∀ n, (G n).det ≠ 0) (N : ℕ) :
    walk F N * K N = (∏ n ∈ range N, R n) • (K 0 * ((walk G N)⁻¹)ᵀ) := by
  induction N with
  | zero =>
    rw [Aux.walk_zero, Aux.walk_zero, Finset.prod_range_zero, one_smul, inv_one,
      Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
  | succ N ih =>
    have hGt : IsUnit ((G N)ᵀ).det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr (hG N)
    have hFK : F N * K (N + 1) = R N • K N * ((G N)ᵀ)⁻¹ := by
      calc F N * K (N + 1) = F N * K (N + 1) * (G N)ᵀ * ((G N)ᵀ)⁻¹ := by
            rw [Matrix.mul_assoc (F N * K (N + 1)), Matrix.mul_nonsing_inv _ hGt, Matrix.mul_one]
        _ = _ := by rw [hstep]
    rw [Aux.walk_succ, Aux.walk_succ, Matrix.mul_assoc, hFK, Matrix.mul_inv_rev,
      Matrix.transpose_mul, Finset.prod_range_succ, ← Matrix.transpose_nonsing_inv,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ih, Matrix.smul_mul, smul_smul,
      mul_comm (R N), Matrix.mul_assoc]

/-- **[3] The explicit identities at the source and at the terminal column**:
`I_F K(0) = 2 I_G`, and `K(n) Jᵀ H(n)⁻¹ e₀ = e₀`.
* Estimated proof length: ≈ 20 lines (`Matrix.ext`, `simp [Kmat, Emat, Hmat, Jmat]`,
  `field_simp`, `ring`; `H(n) hvec(n) = e₀` is a polynomial identity in `n`).
* Directly from the manuscript: yes (exact identities displayed in Appendix A). -/
theorem initial_projection :
    (∀ A B : ℤ, IF A B * Kmat 0 = (2 : ℚ) • IG A B) ∧
      ∀ n, Kmat n *ᵥ ![hvec n 0, hvec n 1, hvec n 2, 0] = e0 := by
  refine ⟨fun A B => ?_, fun n => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [IF, IG, Kmat, Emat, Hmat, Jmat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · have hD : Delta n ≠ 0 := by unfold Delta; positivity
    have hJ : Jmat *ᵥ ![hvec n 0, hvec n 1, hvec n 2, 0] = hvec n := by
      ext i
      fin_cases i <;> simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hH : Hmat n *ᵥ hvec n = ![1, 0, 0] := by
      ext i
      fin_cases i <;> simp [Hmat, hvec, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
        field_simp <;> simp only [Delta, Aux.prod_Icc_8_12] <;> push_cast <;> ring
    have hE : Emat n *ᵥ ![1, 0, 0] = e0 := by
      ext i
      fin_cases i <;> simp [Emat, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [Kmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ, hH, hE]

/-- **[4] Forward = dual**: `I_F W_F(N) e₀ = 2 (∏_{n<N} R(n)) Î_G W_Q(N)^{-T} H(N)⁻¹ e₀`
(the block form makes `I_G W_G(N)^{-T} = (Î_G W_Q(N)^{-T}, 0)`).
* Uses: [2], [3].
* Estimated proof length: ≈ 40 lines.
* Directly from the manuscript: yes. -/
theorem forward_eq_dual (A B : ℤ) (F G : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (hstep : ∀ n, F n * Kmat (n + 1) * (G n)ᵀ = Rsc n • Kmat n) (hdet : ∀ n, (G n).det ≠ 0)
    (hblock : ∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0) (n : ℕ) :
    IF A B *ᵥ (walk F n *ᵥ e0) = (2 * ∏ m ∈ range n, Rsc m) • dualVec A B G n := by
  obtain ⟨hIK, hKx⟩ := initial_projection
  have hW := telescoped_walk F G Kmat Rsc hstep hdet n
  have hrow : ∀ j : Fin 3, walk G n 3 (Fin.castSucc j) = 0 := fun j => by
    rw [Aux.walk_last_row G hblock n,
      ite_eq_right (show Fin.castSucc j ≠ (3 : Fin 4) from (Fin.castSucc_lt_last j).ne)]
  have hinv := Aux.inv_topLeft (walk G n) (Aux.walk_det_ne_zero G hdet n) hrow
  have htl := Aux.walk_topLeft G hblock n
  rw [← hKx n, Matrix.mulVec_mulVec _ (walk F n) (Kmat n), hW, Matrix.smul_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec _ (IF A B), ← Matrix.mul_assoc, hIK, Matrix.smul_mul,
    Matrix.smul_mulVec, smul_smul, mul_comm]
  congr 1
  unfold dualVec Qblock
  rw [htl, ← hinv]
  ext i
  fin_cases i <;>
    simp [IG, IGhat, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_three] <;> ring

/-- **[1] The certificate matrices.** The CMF matrices `F(n)` (forward `₅F₄`, start `x₀`,
direction `v_F`) and `G(n)` (dual `MeijerG(5,2,5,5,1)`, start `y₀`, direction `v_G`) satisfy:
the inverse-free intertwining `F(n) K(n+1) G(n)ᵀ = R(n) K(n)`; `G(n)` is invertible with last row
`(0, 0, 0, -1)`; the readout bridge (walk-readout)
`I_F W_F(n) e₀ = (12/E_n) (A S₃ + B S₄, S₀)` for all `A, B, n`; and `DualData G`.
* Estimated proof length: ≈ 300 lines (definition of both CMFs; the symbolic identities checked
  by `verify_5f4_meijerg_recessive.py`; the contiguity derivation of Appendix H for the bridge;
  `charpoly` and cyclic determinant from `spectral_data.json`).
* Directly from the manuscript: partially (the identities are certificate-checked; the matrices
  `F(n)`, `G(n)` are not printed; the bridge is "proposed" in Appendix H). -/
theorem certificate_matrices : ∃ F G : ℕ → Matrix (Fin 4) (Fin 4) ℚ,
    (∀ n, F n * Kmat (n + 1) * (G n)ᵀ = Rsc n • Kmat n) ∧ (∀ n, (G n).det ≠ 0) ∧
      (∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0) ∧
      (∀ (A B : ℤ) (n : ℕ), IF A B *ᵥ (walk F n *ᵥ e0) =
        ((12 : ℚ) / E n) • ![A * S3 n + B * S4 n, S0 n]) ∧
      DualData G := by
  refine ⟨GD.Fm, GD.G, fun n => GD.intertwine n, GD.G_det, GD.G_block, fun A B n => ?_, ?_⟩
  · rw [forward_eq_dual A B GD.Fm GD.G (fun n => GD.intertwine n) GD.G_det GD.G_block n,
      ST.star A B n]
    show (2 * ∏ m ∈ range n, Rsc m) •
      (IGhat A B *ᵥ (((walk GD.Qb n)⁻¹)ᵀ *ᵥ hvec n)) = _
    rw [GD.walk_Qb_inv_transpose]
    rfl
  · refine ⟨fun n k => MC.SG_step n k, ⟨GD.Qr, GD.Qr_spec⟩, GD.Qinf, GD.hlim, GD.hchar, GD.hcyc⟩

/-- **[5] The dual limit** (conditional on `modal_basis`): eventually the dual denominator is
nonzero and `|α_{A,B} - (dual ratio)| ≤ ε^n`. The decaying restricted state is a nonzero multiple
of the recessive modal row (`modal_basis`, `meijerG_decay`); `dual_mode_transfer` applies with
`r = |ρ₄|`, `R = |ρ₁| = |ρ₂|`, `v_n = Δ(n) h(n)`, `w = (1,10,100)ᵀ` (cyclic determinant `≠ 0`);
the limit is `Î_G Ŝ(0)ᵀ` read as a ratio, `6 α_{A,B} / 6` (`meijerG_initial`); and
`ϑ = r/R < ε` (`spectral_certificate`).
* Uses: [6] and the nodes named above.
* Estimated proof length: ≈ 150 lines.
* Directly from the manuscript: partially (conditional on the modal-basis theorem). -/
theorem dual_limit (A B : ℤ) (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (hdet : ∀ n, (G n).det ≠ 0)
    (hblock : ∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0) (hdata : DualData G) :
    ∀ᶠ n in atTop, dualVec A B G n 1 ≠ 0 ∧
      |alpha A B - ((dualVec A B G n 0 / dualVec A B G n 1 : ℚ) : ℝ)| ≤ (102 / 10 ^ 51 : ℝ) ^ n := by
  obtain ⟨hstate, ⟨Qr, hQr⟩, Qinf, hlim, hchar, hcyc⟩ := hdata
  have hres : ∀ n, (fun k : Fin 3 => SG (n + 1) k) =
      (fun k : Fin 3 => SG n k) ᵥ* (Qblock G n).map (fun x : ℚ => (x : ℂ)) := by
    intro n
    funext k
    have h := hstate n (Fin.castSucc k)
    rw [Fin.val_castSucc] at h
    rw [h, Fin.sum_univ_castSucc, show (Fin.last 3 : Fin 4) = 3 from rfl, hblock n,
      ite_eq_right (show Fin.castSucc k ≠ (3 : Fin 4) from (Fin.castSucc_lt_last k).ne),
      Rat.cast_zero, mul_zero, add_zero]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Qblock, Matrix.submatrix_apply,
      Fin.val_castSucc]
  exact DL.dual_limit_core A B G hdet hblock Qr hQr Qinf hlim hchar hcyc hres

/-- **[6] The restricted Meijer state** `Ŝ(n) = (𝒢_n, θ𝒢_n, θ²𝒢_n)(1)` solves
`Ŝ(n+1) = Ŝ(n) Q(n)` (the last row of `G(n)` is `(0,0,0,-1)`).
* Estimated proof length: ≈ 15 lines (`Fin.sum_univ_four`).
* Directly from the manuscript: yes. -/
theorem restricted_state (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (hblock : ∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0)
    (hstate : ∀ (n : ℕ) (k : Fin 4), SG (n + 1) k = ∑ j : Fin 4, SG n j * (G n j k : ℂ)) (n : ℕ) :
    (fun k : Fin 3 => SG (n + 1) k) =
      (fun k : Fin 3 => SG n k) ᵥ* (Qblock G n).map (fun x : ℚ => (x : ℂ)) := by
  funext k
  have h := hstate n (Fin.castSucc k)
  rw [Fin.val_castSucc] at h
  rw [h, Fin.sum_univ_castSucc, show (Fin.last 3 : Fin 4) = 3 from rfl, hblock n,
    ite_eq_right (show Fin.castSucc k ≠ (3 : Fin 4) from (Fin.castSucc_lt_last k).ne), Rat.cast_zero,
    mul_zero, add_zero]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Qblock, Matrix.submatrix_apply,
    Fin.val_castSucc]

/-- **[7] Positivity of the scalars**: `E_n > 0` and `R(n) > 0`.
* Estimated proof length: ≈ 8 lines (`Nat.choose_pos`, `positivity`).
* Directly from the manuscript: yes. -/
theorem E_Rsc_pos (n : ℕ) : 0 < (E n : ℚ) ∧ 0 < Rsc n := by
  refine ⟨?_, ?_⟩
  · unfold E
    exact Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
      (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega)))
  · have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    have hP : ∀ (s : Finset ℕ) (c : ℚ), 0 ≤ c → (∀ j ∈ s, 1 ≤ j) →
        0 < ∏ j ∈ s, (c * n + j) := fun s c hc hs => Finset.prod_pos fun j hj => by
      have : (1 : ℚ) ≤ j := by exact_mod_cast hs j hj
      nlinarith
    have p1 := hP (Icc 1 4) 5 (by norm_num) fun j hj => (mem_Icc.mp hj).1
    have p2 := hP {1, 2, 4, 7, 8, 11, 13, 14} 15 (by norm_num) fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj; omega
    have p3 := hP {1, 5, 7, 11} 12 (by norm_num) fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj; omega
    have p4 := hP (Icc 1 12) 13 (by norm_num) fun j hj => (mem_Icc.mp hj).1
    unfold Rsc
    exact div_pos (mul_pos (mul_pos (by positivity) p1) p2)
      (mul_pos (mul_pos (by positivity) p3) p4)

/-- **`error_bound`** (node of `Blueprint_pfq54.lean`). Proved from [1], [4], [5], [7] and
`Z_integral` (`S₀ > 0`): the bridge and [4] give `(12/E_n) (A S₃ + B S₄, S₀) = c (dual vector)`
with `c = 2 ∏ R ≠ 0`, so `r_n(A,B)` equals the dual ratio. -/
theorem error_bound (A B : ℤ) :
    ∀ᶠ n : ℕ in atTop, |alpha A B - approx n A B| ≤ (102 / 10 ^ 51 : ℝ) ^ n := by
  obtain ⟨F, G, hstep, hdet, hblock, hbridge, hdata⟩ := certificate_matrices
  filter_upwards [dual_limit A B G hdet hblock hdata, eventually_ge_atTop 1]
    with n ⟨hden, hlim⟩ hn
  have hS0 : 0 < S0 n := (Z_integral n hn).2.2.2
  set c : ℚ := 2 * ∏ m ∈ range n, Rsc m with hc
  have hc0 : c ≠ 0 :=
    mul_ne_zero two_ne_zero (Finset.prod_pos fun m _ => (E_Rsc_pos m).2).ne'
  have hE0 : (12 : ℚ) / E n ≠ 0 := div_ne_zero (by norm_num) (E_Rsc_pos n).1.ne'
  have h := (hbridge A B n).symm.trans (forward_eq_dual A B F G hstep hdet hblock n)
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have heq : approx n A B = dualVec A B G n 0 / dualVec A B G n 1 := by
    rw [approx, div_eq_div_iff hS0.ne' hden]
    have key : (12 / E n * c) * ((A * S3 n + B * S4 n) * dualVec A B G n 1) =
        (12 / E n * c) * (dualVec A B G n 0 * S0 n) := by
      calc (12 / E n * c) * ((A * S3 n + B * S4 n) * dualVec A B G n 1)
          = (12 / E n * (A * S3 n + B * S4 n)) * (c * dualVec A B G n 1) := by ring
        _ = (c * dualVec A B G n 0) * (12 / E n * S0 n) := by rw [h0, h1]
        _ = (12 / E n * c) * (dualVec A B G n 0 * S0 n) := by ring
    exact mul_left_cancel₀ (mul_ne_zero hE0 hc0) key
  rw [heq]
  exact hlim

end Pfq54.BP
