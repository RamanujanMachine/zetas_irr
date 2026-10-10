/-
# Blueprint for `ZetasIrr.det_V_eq`

Statement (as in `blueprint.lean`): `det V_N = F_N` (equation (14)).

Source: PDF Part VII §2 ("The identity follows either by the axis determinants or by checking the
rational identity `det B(n) = F_{n+1}/F_n` and `F_0 = 1`") and Part VII §7 (transport of the
original moments, which proves (13)).

In `defs.lean`, `V_N` is *defined* through (13) as `(-1)^N 𝓒₀⁻¹ 𝓒_N`, where `𝓒_N = coeffMat N` is
computed with the formal functional `𝓛_{2N}`. The proof therefore goes through the
coefficient matrices: `det 𝓒₀ = -6`, and the CMF transport `𝓒_{N+1} = -𝓒_N B(N)`, where `B(N)` is
the upper-left `3 × 3` block of the single-step matrix `M(N)` of the MeijerG(5,2,5,5,1) walk,
with `det B(N) = F_{N+1}/F_N`. Induction gives `det 𝓒_N = -6 (-1)^N F_N`, hence `det V_N = F_N`.

The single-step matrices are not displayed in the PDF. They are the products of 72 axis matrices
constructed in `certificates/zeta34/verify_matrix.py` (`step`, `build_trajectory`). That script
also checks the block form and the factorial determinant identity, as polynomial identities in `n`.

| # | Supporting lemma            | Est. lines | Directly from PDF? |
|---|-----------------------------|-----------:|--------------------|
| 1 | `F_pos`                     |   (proved) | Yes                |
| 2 | `F_zero`                    |   (proved) | Yes                |
| 3 | `det_C0`                    |   (proved) | Yes                |
| 4 | `coeffMat_zero`             |   (proved, `coeffMat_zero.lean`) | Yes |
| 5 | `exists_transport_blocks`   |       3000 | No (needs the CMF) |

The only open lemma is [5] (≈ 3000 lines).

`coeffMat_zero` [4] is proved in `coeffMat_zero.lean`.
-/
import ZetasAux
import coeffMat_zero
import CMF_main

open Filter Topology Real
open scoped Matrix

noncomputable section

namespace ZetasIrr.BP

/-- **[1] `F_N > 0`.** (Same proof as in `blueprint.lean`.)
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem F_pos (N : ℕ) : 0 < F N := by
  unfold F
  refine div_pos (List.prod_pos ?_) (mul_pos (List.prod_pos ?_) (List.prod_pos ?_)) <;>
  · intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    positivity

/-- **[2] `F_0 = 1`.**
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem F_zero : F 0 = 1 := by
  simp [F, listA, listB, listE]

/-- **[3] `det 𝓒₀ = -6`.**
* Lines: proved here.
* Directly from the PDF: yes (Part VII §3: `det 𝓒_N = -6(-1)^N F_N` at `N = 0`). -/
theorem det_C0 : C0.det = -6 := by
  rw [Matrix.det_fin_three]; simp [C0]; norm_num

/-- **[4] Base case of (13): `𝓒_0 = 𝓒₀`.** At `N = 0`, `R_0(t) = 1/(t³(t+1))`, and
`𝓛_0[(-t)^j R_0]` is computed from its partial fractions
`1/(t³(t+1)) = t⁻³ - t⁻² + t⁻¹ - (t+1)⁻¹`. For example the `j = 0` column is
`3Z₄ - 2Z₃ + 1`, matching the first column `(3, -2, 1)` of `𝓒₀`.
* Lines: ≈ 150. Computing `pfCoeff` through `RatFunc.laurent` and the Laurent-series coercion
  takes ≈ 100 lines. Evaluating `Lfun` on three explicit rational functions takes ≈ 50.
* Directly from the PDF: yes. The PDF states `𝓒_0 = 𝓒₀` (13), and the computation is
  elementary. -/
theorem coeffMat_zero : coeffMat 0 = C0 :=
  ZetasIrr.coeffMat_zero

/-- **[5] CMF transport of the original moments, with the axis determinants.** There are rational
`3 × 3` matrices `B(N)` (the upper-left blocks of the single-step matrices `M(N)` of the
MeijerG(5,2,5,5,1) walk) such that `𝓒_{N+1} = -𝓒_N B(N)` and `det B(N) = F_{N+1}/F_N`.

Proof outline (PDF Part VII §7):
(a) define the axis matrices of the CMF from the θ-polynomial
    `D(θ) = ∏_i(θ - a_i + 1) - ∏_j(θ - b_j)`, as in `verify_matrix.py`; ≈ 400 lines;
(b) prove the companion relation for the four formal moments `𝓛_K[(-t)^r r(t)]`, using
    `D(-t) r(t) = g(t) - g(t-1)` and the `𝓛`-shift identity when `g'(K) = 0`; ≈ 800 lines;
(c) prove each axis transformation from `Γ(t+1) = tΓ(t)`, and check that every axis matrix is
    invertible along the path (the companion coefficient `5 - ∑a_i + ∑b_j` stays positive);
    ≈ 800 lines;
(d) prove the double boundary zeros (so the cutoff moves from `0` to `2N`) and the block form
    `W_N = [[V_N, *], [0, (-1)^N]]`; ≈ 500 lines;
(e) compute the axis determinants and telescope them to `F_{N+1}/F_N`; ≈ 500 lines.
* Lines: ≈ 3000.
* Directly from the PDF: no. The PDF sketches (b)–(d), but the CMF and its axis matrices are
  only specified in `verify_matrix.py`, and (e) is checked there as a polynomial identity. -/
theorem exists_transport_blocks :
    ∃ B : ℕ → Matrix (Fin 3) (Fin 3) ℚ, ∀ N,
      coeffMat (N + 1) = -(coeffMat N * B N) ∧ (B N).det = F (N + 1) / F N :=
  CMF.exists_transport_blocks'

/-- **Main theorem (`blueprint.lean`, `det_V_eq`).** Proved from [1]–[5]. -/
theorem det_V_eq (N : ℕ) : (V N).det = F N := by
  obtain ⟨B, hB⟩ := exists_transport_blocks
  -- `det 𝓒_N = (-1)^N (-6) F_N`, by induction
  have hC : ∀ n, (coeffMat n).det = (-1) ^ n * (-6) * F n := by
    intro n
    induction n with
    | zero => rw [coeffMat_zero, det_C0, F_zero]; ring
    | succ n ih =>
      obtain ⟨h1, h2⟩ := hB n
      have hF := (F_pos n).ne'
      rw [h1, Matrix.det_neg, Matrix.det_mul, ih, h2, Fintype.card_fin]
      field_simp
      ring
  have hC0 : IsUnit C0.det := by rw [det_C0]; norm_num
  rw [V, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_C0,
    hC, Fintype.card_fin]
  have : ((-1 : ℚ) ^ N) ^ 3 * (-1) ^ N = 1 := by
    rw [← pow_mul, ← pow_add, show N * 3 + N = 2 * (2 * N) by ring, pow_mul]; norm_num
  linear_combination F N * this

end ZetasIrr.BP
