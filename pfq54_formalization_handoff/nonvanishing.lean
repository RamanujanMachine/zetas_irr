/-
# Blueprint of `nonvanishing` (manuscript §8.1, "Nonvanishing for every fixed integer pair")

Node `Pfq54.nonvanishing` of `Blueprint_pfq54.lean`: for `(A, B) ≠ (0, 0)`,
`α_{A,B} ≠ r_n(A,B)` for infinitely many `n` (without assuming `α_{A,B} ≠ 0`).

Proof (manuscript §8.1 and Appendix H). The auxiliary forward Meijer-G matrix `M_G(n)` (start
`(1,1,0,0,0;0,0,0,0,0)`, direction `(16,17,-11,-12,-10;2,1,0,-1,-2)`) has a companion coboundary
`M_G(n) U(n+1) = U(n) C(n)` with `c₀(n) ≠ 0`, `U(n) e₀ = e₀`, the readout bridge
`(Q_n, P_{3,n}, P_{4,n})ᵀ = (-1)^n R W_n^{(G)} e₀`, and `S = R U(0)` invertible ([1]; these are
certificate data). Telescoping shows that `z_n = (-1)^n (α Q_n - A P_{3,n} - B P_{4,n})` solves
`z_{n+3} = c₀(n) z_n + c₁(n) z_{n+1} + c₂(n) z_{n+2}` with initial values `(α, -A, -B) S` ([2]).
An eventually zero solution vanishes identically since `c₀(n) ≠ 0` ([3]); invertibility of `S`
forces `α = A = B = 0` ([4]). Finally `z_n = (S_{0,n}/C_n)(α - r_n(A,B))` ([5]).
-/
import Z_integral
import cas_link

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- The companion matrix `[[0,0,c₀],[1,0,c₁],[0,1,c₂]]`. -/
def companionMat (c₀ c₁ c₂ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, c₀; 1, 0, c₁; 0, 1, c₂]

/-- The readout rows `R = ((1,0,0,0), (0,0,-1/2,1/4), (0,0,0,-1/6))` in Meijer-G coordinates. -/
def Rbr : Matrix (Fin 3) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 0, -1/2, 1/4; 0, 0, 0, -1/6]

/-- `z_n = (-1)^n (x Q_n - A P_{3,n} - B P_{4,n}) = (x S_{0,n} - A S_{3,n} - B S_{4,n}) / C_n`. -/
def zseq (x : ℝ) (A B : ℤ) (n : ℕ) : ℝ :=
  (x * (S0 n : ℝ) - A * (S3 n : ℝ) - B * (S4 n : ℝ)) / (Cn n : ℝ)

/-- **[1] The companion certificate.** There are `M_G(n)` (the native Meijer-G matrices),
`U(n)` (`4 × 3`) and `c₀, c₁, c₂` with: `M_G(n) U(n+1) = U(n) C(n)`; `U(n) e₀ = e₀`;
`c₀(n) ≠ 0` (no poles and no zeros at `n ≥ 0`); the bridge
`(Q_n, P_{3,n}, P_{4,n}) = (-1)^n R W_n^{(G)} e₀` for all `n` (including `n = 0`); and
`det (R U(0)) ≠ 0` (`≡ 1 mod 101`).
* Estimated proof length: ≈ 250 lines (the Meijer-G CMF; the rational-function identities and
  sign checks of `companion_readout.json`; the contiguity derivation of the bridge, Appendix H).
* Directly from the manuscript: partially (certificate obligations; `M_G`, `U`, `C` are not
  printed). -/
theorem companion_data : ∃ (MG : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (Um : ℕ → Matrix (Fin 4) (Fin 3) ℚ) (c₀ c₁ c₂ : ℕ → ℚ),
    (∀ n, MG n * Um (n + 1) = Um n * companionMat (c₀ n) (c₁ n) (c₂ n)) ∧
      (∀ n, Um n *ᵥ ![1, 0, 0] = ![1, 0, 0, 0]) ∧ (∀ n, c₀ n ≠ 0) ∧
      (∀ n, ![Qa n, P3a n, P4a n] = ((-1 : ℚ) ^ n) • (Rbr *ᵥ (walk MG n *ᵥ ![1, 0, 0, 0]))) ∧
      (Rbr * Um 0).det ≠ 0 :=
  CA.companion_data_of CL.Cas_ne

/-- **[2] Telescoping the coboundary.** For the data of [1] and any `x, A, B`: `z_n` solves the
companion recurrence and `(z₀, z₁, z₂) = (x, -A, -B) S` with `S = R U(0)`
(`W_n^{(G)} U(n) = U(0) C(0) ⋯ C(n-1)`, and the first coordinates of a row companion solution
satisfy the scalar recurrence).
* Estimated proof length: ≈ 45 lines.
* Directly from the manuscript: yes ("Telescoping the coboundary identity shows …"). -/
theorem companion_telescope (MG : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (Um : ℕ → Matrix (Fin 4) (Fin 3) ℚ) (c₀ c₁ c₂ : ℕ → ℚ)
    (hcob : ∀ n, MG n * Um (n + 1) = Um n * companionMat (c₀ n) (c₁ n) (c₂ n))
    (hU : ∀ n, Um n *ᵥ ![1, 0, 0] = ![1, 0, 0, 0])
    (hbr : ∀ n, ![Qa n, P3a n, P4a n] = ((-1 : ℚ) ^ n) • (Rbr *ᵥ (walk MG n *ᵥ ![1, 0, 0, 0])))
    (x : ℝ) (A B : ℤ) :
    (∀ n, zseq x A B (n + 3) = (c₀ n : ℝ) * zseq x A B n + (c₁ n : ℝ) * zseq x A B (n + 1) +
        (c₂ n : ℝ) * zseq x A B (n + 2)) ∧
      (fun i : Fin 3 => zseq x A B i) =
        ![x, -(A : ℝ), -(B : ℝ)] ᵥ* (Rbr * Um 0).map (fun q : ℚ => (q : ℝ)) := by
  set Cm : ℕ → Matrix (Fin 3) (Fin 3) ℚ := fun n => companionMat (c₀ n) (c₁ n) (c₂ n) with hCm
  have htel : ∀ n, walk MG n * Um n = Um 0 * walk Cm n := by
    intro n
    induction n with
    | zero => rw [Aux.walk_zero, Aux.walk_zero, Matrix.one_mul, Matrix.mul_one]
    | succ n ih =>
      rw [Aux.walk_succ, Aux.walk_succ, Matrix.mul_assoc, hcob n, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  set row : Fin 3 → ℝ := ![x, -(A : ℝ), -(B : ℝ)] with hrow
  set vr : ℕ → Fin 3 → ℝ := fun n => row ᵥ* ((Rbr * Um 0 * walk Cm n).map (Rat.castHom ℝ))
    with hvr
  have hstep : ∀ n, vr (n + 1) = vr n ᵥ* (Cm n).map (Rat.castHom ℝ) := by
    intro n
    simp only [hvr]
    rw [Aux.walk_succ, ← Matrix.mul_assoc, Matrix.map_mul, Matrix.vecMul_vecMul]
  have hc0 : ∀ n (v : Fin 3 → ℝ), (v ᵥ* (Cm n).map (Rat.castHom ℝ)) 0 = v 1 := by
    intro n v; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hCm, companionMat]
  have hc1 : ∀ n (v : Fin 3 → ℝ), (v ᵥ* (Cm n).map (Rat.castHom ℝ)) 1 = v 2 := by
    intro n v; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hCm, companionMat]
  have hc2 : ∀ n (v : Fin 3 → ℝ), (v ᵥ* (Cm n).map (Rat.castHom ℝ)) 2 =
      (c₀ n : ℝ) * v 0 + (c₁ n : ℝ) * v 1 + (c₂ n : ℝ) * v 2 := by
    intro n v; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hCm, companionMat]; ring
  have hz : ∀ n, zseq x A B n = vr n 0 := by
    intro n
    have hneg : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    have h := hbr n
    rw [← hU n, Matrix.mulVec_mulVec _ (walk MG n) (Um n), htel n,
      Matrix.mulVec_mulVec _ Rbr, ← Matrix.mul_assoc] at h
    set M := Rbr * Um 0 * walk Cm n with hM
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    have hz' : zseq x A B n = (-1) ^ n * (x * (Qa n : ℝ) - A * (P3a n : ℝ) - B * (P4a n : ℝ)) := by
      unfold zseq Qa P3a P4a
      push_cast
      calc _ = ((-1 : ℝ) ^ n * (-1) ^ n) * ((x * S0 n - A * S3 n - B * S4 n) / Cn n) := by
            rw [hneg, one_mul]
        _ = _ := by ring
    have key : zseq x A B n = x * (M 0 0 : ℝ) - A * (M 1 0 : ℝ) - B * (M 2 0 : ℝ) := by
      rw [hz', h0, h1, h2]
      push_cast
      calc _ = ((-1 : ℝ) ^ n * (-1) ^ n) * (x * (M 0 0 : ℝ) - A * (M 1 0 : ℝ) - B * (M 2 0 : ℝ)) :=
            by ring
        _ = _ := by rw [hneg, one_mul]
    rw [key]
    simp [hvr, hrow, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
    ring
  refine ⟨fun n => ?_, ?_⟩
  · have e1 : vr (n + 1) 0 = vr n 1 := by rw [hstep, hc0]
    have e2 : vr (n + 2) 0 = vr n 2 := by
      rw [show n + 2 = n + 1 + 1 from rfl, hstep, hc0, hstep, hc1]
    have e3 : vr (n + 3) 0 = (c₀ n : ℝ) * vr n 0 + c₁ n * vr n 1 + c₂ n * vr n 2 := by
      rw [show n + 3 = n + 2 + 1 from rfl, hstep, hc0, show n + 2 = n + 1 + 1 from rfl, hstep,
        hc1, hstep, hc2]
    rw [hz, hz, hz, hz, e3, e1, e2]
  · have hv0 : vr 0 = row ᵥ* (Rbr * Um 0).map (fun q : ℚ => (q : ℝ)) := by
      simp only [hvr]
      rw [Aux.walk_zero, Matrix.mul_one]
      rfl
    rw [← hv0]
    funext i
    fin_cases i
    · exact hz 0
    · show zseq x A B 1 = vr 0 1
      rw [hz]
      change vr (0 + 1) 0 = vr 0 1
      rw [hstep, hc0]
    · show zseq x A B 2 = vr 0 2
      rw [hz]
      change vr (0 + 1 + 1) 0 = vr 0 2
      rw [hstep, hc0, hstep, hc1]

/-- **[3] Backward propagation of zeros**: a solution of `z_{n+3} = c₀ z_n + c₁ z_{n+1} + c₂ z_{n+2}`
with `c₀(n) ≠ 0` that is eventually zero has `z₀ = z₁ = z₂ = 0`.
* Estimated proof length: ≈ 25 lines (downward induction from three consecutive zeros).
* Directly from the manuscript: yes. -/
theorem backward_zero (z c₀ c₁ c₂ : ℕ → ℝ) (hc₀ : ∀ n, c₀ n ≠ 0)
    (hrec : ∀ n, z (n + 3) = c₀ n * z n + c₁ n * z (n + 1) + c₂ n * z (n + 2))
    (hev : ∀ᶠ n in atTop, z n = 0) : z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have key : ∀ m, z (N - m) = 0 ∧ z (N - m + 1) = 0 ∧ z (N - m + 2) = 0 := by
    intro m
    induction m with
    | zero =>
      rw [Nat.sub_zero]
      exact ⟨hN N le_rfl, hN _ (by omega), hN _ (by omega)⟩
    | succ m ih =>
      by_cases hm : m < N
      · have e1 : N - (m + 1) + 1 = N - m := by omega
        have e2 : N - (m + 1) + 2 = N - m + 1 := by omega
        have e3 : N - (m + 1) + 3 = N - m + 2 := by omega
        refine ⟨?_, by rw [e1]; exact ih.1, by rw [e2]; exact ih.2.1⟩
        have h := hrec (N - (m + 1))
        rw [e3, e1, e2, ih.1, ih.2.1, ih.2.2] at h
        have h' : c₀ (N - (m + 1)) * z (N - (m + 1)) = 0 := by linarith
        exact (mul_eq_zero.mp h').resolve_left (hc₀ _)
      · rw [show N - (m + 1) = N - m by omega]
        exact ih
  obtain ⟨h0, h1, h2⟩ := key N
  rw [Nat.sub_self] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- **[4]** A row annihilated by an invertible matrix is zero.
* Proof length: 2 lines. Proved below (as in `integer_matrix_criterion` of `blueprint.lean`, Mathlib
  `Matrix.exists_vecMul_eq_zero_iff`).
* Directly from the manuscript: yes. -/
theorem row_zero (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.det ≠ 0) (u : Fin 3 → ℝ)
    (hu : u ᵥ* S = 0) : u = 0 := by
  by_contra hne
  exact hS (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hne, hu⟩)

/-- **[5] `z_n` and the error**: `z_n = (S_{0,n}/C_n) (x - r_n(A,B))` for `n ≥ 1`.
* Estimated proof length: ≈ 8 lines (`S_{0,n} > 0`, `field_simp`).
* Directly from the manuscript: yes. -/
theorem zseq_eq (x : ℝ) (A B : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    zseq x A B n = ((S0 n : ℝ) / (Cn n : ℝ)) * (x - (approx n A B : ℝ)) := by
  have hS : (S0 n : ℝ) ≠ 0 := by exact_mod_cast (Z_integral n hn).2.2.2.ne'
  have hC' : Cn n ≠ 0 := by unfold Cn; positivity
  have hC : (Cn n : ℝ) ≠ 0 := by exact_mod_cast hC'
  unfold zseq approx
  push_cast
  field_simp
  ring

/-- **`nonvanishing`** (node of `Blueprint_pfq54.lean`). Proved from [1]–[5]. -/
theorem nonvanishing (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ᶠ n : ℕ in atTop, alpha A B ≠ approx n A B := by
  obtain ⟨MG, Um, c₀, c₁, c₂, hcob, hU, hc₀, hbr, hdet⟩ := companion_data
  obtain ⟨hrec, hinit⟩ := companion_telescope MG Um c₀ c₁ c₂ hcob hU hbr (alpha A B) A B
  set S : Matrix (Fin 3) (Fin 3) ℝ := (Rbr * Um 0).map (fun q : ℚ => (q : ℝ)) with hSdef
  have hSdet : S.det ≠ 0 := by
    have : S.det = (((Rbr * Um 0).det : ℚ) : ℝ) := by
      rw [show S = (Rat.castHom ℝ).mapMatrix (Rbr * Um 0) from rfl, ← RingHom.map_det]
      rfl
    rw [this]
    exact_mod_cast hdet
  by_contra hfreq
  rw [Filter.not_frequently] at hfreq
  have hz : ∀ᶠ n in atTop, zseq (alpha A B) A B n = 0 := by
    filter_upwards [hfreq, eventually_ge_atTop 1] with n hn h1
    rw [zseq_eq _ A B n h1, not_not.mp hn, sub_self, mul_zero]
  obtain ⟨z0, z1, z2⟩ := backward_zero (zseq (alpha A B) A B) (fun n => (c₀ n : ℝ))
    (fun n => (c₁ n : ℝ)) (fun n => (c₂ n : ℝ)) (fun n => by exact_mod_cast hc₀ n) hrec hz
  have hrow : ![alpha A B, -(A : ℝ), -(B : ℝ)] ᵥ* S = 0 := by
    rw [← hinit]
    funext i
    fin_cases i
    · exact z0
    · exact z1
    · exact z2
  have hu := row_zero S hSdet _ hrow
  have hA : (A : ℝ) = 0 := by simpa using congrFun hu 1
  have hB : (B : ℝ) = 0 := by simpa using congrFun hu 2
  exact hAB (Prod.ext (by exact_mod_cast hA) (by exact_mod_cast hB))

end Pfq54.BP
