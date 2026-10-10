/-
# Blueprint for `ZetasIrr.pairing_identity`

Statement (as in `blueprint.lean`), equation (6), coefficientwise for all `N`:
  `(-1)^N 𝓜_{-10N-1}[Q_{Nj}(t) R*_N(t)] = Z₄ q_{Nj} - p^{(4)}_{Nj}`.

Source: PDF Part III (second functional `𝓜`, the moments `g₀^{[2]} = (2Z₃-6Z₄, 2Z₃, -1, 0)` (5),
Lemma 1, `g₀^{[2]} J₀[0:3,:]ᵀ = (-2, 2, 6Z₄)`) and Part VII §7 (dual parameters, concomitant
`J_N`, `W_N J_N (D_N^{dual})ᵀ = J_0`, endpoint substitution `s = t + 12N + 1`).

Certificates: `certificates/zeta34/verify_pairing.py` (generic concomitant identity for one
upper and one lower shift), `verify_transport.py` (all 72 + 144 axis steps at `N = 1, 2`),
`verify_second_functional.py` (the identity for `N ≤ 20`). These are finite checks. The all-`N`
argument is Lemma 1.

Objects introduced here (they follow the PDF and are not in `defs.lean`):
* `dualKernel N` `= r_N(s) = (-1)^N R*_N(s - 12N - 1)`, the dual Meijer kernel at the end of the
  walk ("At the endpoint substitute `s = t + 12N + 1`. The kernel becomes `(-1)^N R*_N(t)`");
* `dualMoment N r` `= 𝓜_{2N}[(-s)^r r_N(s)]`, `r = 0,…,3`, the four second-functional moments
  `g^{[2]}_N` (cutoff `2N`, as in Lemma 1).

| # | Supporting lemma          | Est. lines | Directly from PDF? |
|---|---------------------------|-----------:|--------------------|
| 1 | `Mfun_linear`             |        150 | Yes                |
| 2 | `Mfun_translate`          |        150 | Yes                |
| 3 | `endpoint_substitution`   |        120 | Yes (given [1], [2]) |
| 4 | `dualMoment_zero`         |   (proved) | Yes                |
| 5 | `dual_transport`          |       2500 | No (needs the CMF) |
| 6 | `pairing_transport`       |   (proved) | Partially          |
| 7 | `initial_pairing`         |         25 | Yes (from [4])     |

[1], [2] are ingredients of [3]; [5] of [6]; [4] of [7]. The main theorem uses [3], [6], [7].
Total estimate: ≈ 3665 lines, dominated by the CMF transport [5]. That part is shared with
`det_V_eq.lean` [5] and `valuation_bound.lean` [4].
-/
import ZetasAux
import CMF_main

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries

noncomputable section

namespace ZetasIrr.BP

/-- The dual kernel at the end of the walk: `r_N(s) = (-1)^N R*_N(s - 12N - 1)`.
(`RatFunc.laurent c f = f(X + c)`.) -/
def dualKernel (N : ℕ) : ℚ⟮X⟯ :=
  ((-1 : ℚ) ^ N) • RatFunc.laurent (-(12 * (N : ℚ) + 1)) (RkerStar N)

/-- The second-functional moments `g^{[2]}_N = (𝓜_{2N}[(-s)^r r_N(s)])_{r=0..3}`. -/
def dualMoment (N : ℕ) (r : Fin 4) : FormalZ :=
  Mfun (2 * N) ((-RatFunc.X) ^ (r : ℕ) * dualKernel N)

/-- **[1] Linearity of `𝓜_K`** on functions with integer poles `≤ K`: `𝓜_K[∑ cᵢ fᵢ] = ∑ cᵢ 𝓜_K[fᵢ]`.
`pfCoeff` and `polyPart` are linear. Poles that cancel contribute zero coefficients, so the
different pole sets of the summands do not matter.
It holds for all rational functions (the pole hypothesis is not needed).
* Lines: proved (`Aux.Mfun_sum` in `ZetasAux.lean`).
* Directly from the PDF: yes (the functionals are defined coefficientwise). -/
theorem Mfun_linear (K : ℤ) {ι : Type*} (s : Finset ι) (c : ι → ℚ) (f : ι → ℚ⟮X⟯)
    (_hpoles : ∀ i ∈ s, ∀ h ∈ (f i).denom.roots, ∃ n : ℤ, n ≤ K ∧ h = n) :
    Mfun K (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Mfun K (f i) :=
  Aux.Mfun_sum K s c f

/-- **[2] Translation.** `𝓜_K[f(t + c)] = 𝓜_{K+c}[f]` for an integer shift `c`. Poles move by
`-c`, so the harmonic indices `K - h` are unchanged. The polynomial parts match by the Appell
property `B_d(x + c) = ∑ C(d,i) B_i(x) c^{d-i}` (Mathlib `Polynomial.bernoulli_eval_add`-type
identity).
* Lines: proved (`Aux.Mfun_laurent` in `ZetasAux.lean`; the Appell step is `Aux.bsum_taylor`).
* Directly from the PDF: yes ("At the endpoint substitute `s = t + 12N + 1` … the cutoff is
  `-10N-1` because … the unshifted cutoff is `2N`"). -/
theorem Mfun_translate (K c : ℤ) (f : ℚ⟮X⟯) :
    Mfun K (RatFunc.laurent (c : ℚ) f) = Mfun (K + c) f :=
  Aux.Mfun_laurent K c f

/-- **[3] Endpoint substitution.** With `s = t + 12N + 1`:
`Q_{Nj}(t) R*_N(t) = (-1)^N ∑_r (J_N)_{jr} (-s)^r r_N(s)`. Hence by [2] (cutoff `2N ↦ -10N-1`)
and [1]: `(-1)^N 𝓜_{-10N-1}[Q_{Nj} R*_N] = ∑_r (J_N)_{jr} g^{[2]}_N(r)`.
* Lines: proved here (from [1], [2]).
* Directly from the PDF: yes (given [1], [2]). -/
theorem endpoint_substitution (N : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ N) • Mfun (-10 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) =
      ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) • dualMoment N r := by
  set c : ℤ := 12 * N + 1 with hc
  set F := ∑ r : Fin 4,
    (Jmat N (Fin.castSucc j) r : ℚ) • ((-RatFunc.X) ^ (r : ℕ) * dualKernel N) with hF
  set L := RatFunc.laurent (c : ℚ) (dualKernel N) with hL
  have hsq : ((-1 : ℚ) ^ N) * (-1) ^ N = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hk : L = RatFunc.C ((-1 : ℚ) ^ N) * RkerStar N := by
    rw [hL, dualKernel, RatFunc.smul_eq_C_mul, map_mul, RatFunc.laurent_C, RatFunc.laurent_laurent,
      show (c : ℚ) + -(12 * (N : ℚ) + 1) = 0 by rw [hc]; push_cast; ring,
      RatFunc.laurent_at_zero]
  have hR : RkerStar N = RatFunc.C ((-1 : ℚ) ^ N) * L := by
    rw [hk, ← mul_assoc, ← map_mul, hsq, map_one, one_mul]
  have hQ : algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) = ∑ r : Fin 4, RatFunc.C (Jmat N (Fin.castSucc j) r : ℚ) *
      (-RatFunc.X - RatFunc.C (12 * (N : ℚ) + 1)) ^ (r : ℕ) := by
    simp only [Qpoly, map_sum, Polynomial.smul_eq_C_mul, map_mul, map_pow, map_sub, map_neg,
      RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hA : algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N =
      RatFunc.C ((-1 : ℚ) ^ N) * RatFunc.laurent (c : ℚ) F := by
    rw [hR, hQ, hF]
    simp only [RatFunc.smul_eq_C_mul, Fin.sum_univ_four, map_add, map_mul, RatFunc.laurent_C,
      map_pow, map_neg, RatFunc.laurent_X, ← hL]
    rw [hc]
    push_cast
    simp only [map_add, map_mul]
    ring
  rw [hA, ← RatFunc.smul_eq_C_mul, Aux.Mfun_smul, smul_smul, hsq, one_smul, Mfun_translate,
    show (-10 * (N : ℤ) - 1 + c) = 2 * N by rw [hc]; ring, hF, Aux.Mfun_sum]
  rfl

/-! ### The initial kernel `r_0(s) = (s-1)/s^2` and its four moments (PDF Part III, (5)) -/

/-- `R*_0(t) = t/(t+1)^2`. -/
theorem RkerStar_zero :
    RkerStar 0 = algebraMap ℚ[X] ℚ⟮X⟯ Polynomial.X /
      algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X + Polynomial.C 1) ^ 2) := by
  simp [RkerStar, poch, ascPochhammer_one, sq]

/-- `r_0(s) = R*_0(s - 1) = (s-1)/s^2`. -/
theorem dualKernel_zero :
    dualKernel 0 = algebraMap ℚ[X] ℚ⟮X⟯ (Polynomial.X - Polynomial.C 1) /
      algebraMap ℚ[X] ℚ⟮X⟯ (Polynomial.X ^ 2) := by
  rw [dualKernel, RkerStar_zero, RatFunc.laurent_div, pow_zero, RatFunc.smul_eq_C_mul, map_one,
    one_mul]
  simp only [Nat.cast_zero, mul_zero, zero_add, Polynomial.taylor_X, Polynomial.taylor_pow,
    map_add, Polynomial.taylor_C]
  congr 2
  · simp [sub_eq_add_neg]
  · simp

theorem moment_zero_eq (r : ℕ) :
    (-RatFunc.X) ^ r * dualKernel 0 =
      algebraMap ℚ[X] ℚ⟮X⟯ ((-Polynomial.X) ^ r * (Polynomial.X - Polynomial.C 1)) /
        algebraMap ℚ[X] ℚ⟮X⟯ (Polynomial.X ^ 2) := by
  rw [dualKernel_zero, ← mul_div_assoc]
  congr 1
  simp only [map_mul, map_pow, map_neg, RatFunc.algebraMap_X]

theorem rfDeriv_moment_zero (r : ℕ) :
    rfDeriv ((-RatFunc.X) ^ r * dualKernel 0) =
      algebraMap ℚ[X] ℚ⟮X⟯
        (derivative ((-Polynomial.X) ^ r * (Polynomial.X - Polynomial.C 1)) * Polynomial.X ^ 2 -
          (-Polynomial.X) ^ r * (Polynomial.X - Polynomial.C 1) * derivative (Polynomial.X ^ 2)) /
        algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X ^ 2) ^ 2) := by
  rw [moment_zero_eq, Aux.rfDeriv_div _ _ (pow_ne_zero _ Polynomial.X_ne_zero)]

/-- All poles of `((-s)^r r_0(s))'` are at `0`, of order `≤ 4`. -/
theorem denom_rfDeriv_moment_zero (r : ℕ) :
    (rfDeriv ((-RatFunc.X) ^ r * dualKernel 0)).denom ∣ Polynomial.X ^ 4 := by
  rw [rfDeriv_moment_zero]
  refine (RatFunc.denom_div_dvd _ _).trans ?_
  rw [← pow_mul]

theorem Icc_one_four : Finset.Icc (1 : ℕ) 4 = {1, 2, 3, 4} := rfl

/-- Bernoulli sums of the polynomial parts: `𝓛_0[0] = 0`. -/
theorem bsum_one_zero : Aux.bsum 1 (0 : ℚ[X]) = 0 := by
  simp [Aux.bsum]

/-- `𝓛_0[k] = k B_0(1) = k`. -/
theorem bsum_one_C (k : ℚ) : Aux.bsum 1 (Polynomial.C k) = k := by
  rw [Aux.bsum_eq_range 1 _ 0 (by simp)]
  simp

/-- `𝓛_0[a t + b] = a B_1(1) + b B_0(1) = a/2 + b`. -/
theorem bsum_one_lin (a b : ℚ) :
    Aux.bsum 1 (Polynomial.C a * Polynomial.X + Polynomial.C b) = a / 2 + b := by
  rw [Aux.bsum_eq_range 1 _ 1 (by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))]
  simp [Finset.sum_range_succ, Polynomial.coeff_C, Polynomial.bernoulli_eval_one,
    bernoulli'_one]
  ring

/-- `𝓜_0[r_0] = -𝓛_0[-s⁻² + 2s⁻³] = 2Z₃ - 6Z₄`. -/
theorem moment_zero_0 :
    Mfun 0 ((-RatFunc.X) ^ ((0 : Fin 4) : ℕ) * dualKernel 0) = 2 • Zsym 3 - 6 • Zsym 4 := by
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  rw [Mfun, Aux.Lfun_zero_of_decomp _ (denom_rfDeriv_moment_zero _) 0
      (fun k => if k = 2 then -1 else if k = 3 then 2 else 0) ?_]
  · rw [bsum_one_zero, Icc_one_four]
    simp
    module
  · rw [rfDeriv_moment_zero, Icc_one_four]
    simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_C,
      derivative_neg]
    simp
    field_simp
    ring

/-- `𝓜_0[-s r_0] = -𝓛_0[-s⁻²] = 2Z₃`. -/
theorem moment_zero_1 :
    Mfun 0 ((-RatFunc.X) ^ ((1 : Fin 4) : ℕ) * dualKernel 0) = 2 • Zsym 3 := by
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  rw [Mfun, Aux.Lfun_zero_of_decomp _ (denom_rfDeriv_moment_zero _) 0
      (fun k => if k = 2 then -1 else 0) ?_]
  · rw [bsum_one_zero, Icc_one_four]
    simp
    module
  · rw [rfDeriv_moment_zero, Icc_one_four]
    simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_C,
      derivative_neg]
    simp
    field_simp
    ring

/-- `𝓜_0[s² r_0] = -𝓛_0[1] = -1` (a polynomial contribution). -/
theorem moment_zero_2 :
    Mfun 0 ((-RatFunc.X) ^ ((2 : Fin 4) : ℕ) * dualKernel 0) = -Zsym 0 := by
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  rw [Mfun, Aux.Lfun_zero_of_decomp _ (denom_rfDeriv_moment_zero _) (Polynomial.C 1)
      (fun _ => 0) ?_]
  · rw [bsum_one_C, Icc_one_four]
    simp
  · rw [rfDeriv_moment_zero, Icc_one_four]
    simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_C,
      derivative_neg]
    simp
    field_simp
    ring

/-- `𝓜_0[-s³ r_0] = -𝓛_0[-2s + 1] = -(-2 B_1(1) + B_0(1)) = 0` (a polynomial contribution). -/
theorem moment_zero_3 :
    Mfun 0 ((-RatFunc.X) ^ ((3 : Fin 4) : ℕ) * dualKernel 0) = 0 := by
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  rw [Mfun, Aux.Lfun_zero_of_decomp _ (denom_rfDeriv_moment_zero _)
      (Polynomial.C (-2) * Polynomial.X + Polynomial.C 1) (fun _ => 0) ?_]
  · rw [bsum_one_lin, Icc_one_four]
    simp
  · rw [rfDeriv_moment_zero, Icc_one_four]
    simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_C,
      derivative_neg]
    simp
    field_simp
    ring

/-- **[4] Initial moments (5).** `g^{[2]}_0 = (2Z₃ - 6Z₄, 2Z₃, -1, 0)` for the initial kernel
`r_0(s) = (s-1)/s²`.
* Lines: proved here (partial fractions of four explicit rational functions, `Mfun` evaluation
  via `Aux.Lfun_zero_of_decomp`; the last two entries are polynomial contributions).
* Directly from the PDF: yes. -/
theorem dualMoment_zero :
    dualMoment 0 = ![2 • Zsym 3 - 6 • Zsym 4, 2 • Zsym 3, -Zsym 0, 0] := by
  funext r
  simp only [dualMoment, Nat.cast_zero, mul_zero]
  fin_cases r
  · exact moment_zero_0
  · exact moment_zero_1
  · exact moment_zero_2
  · exact moment_zero_3

/-- **[5] Lemma 1: the dual transport.** There are rational `4 × 4` matrices `D_N` (the dual CMF
transport) such that `g^{[2]}_N = g^{[2]}_0 D_N` and the concomitant identity
`W_N J_N D_Nᵀ = J_0` holds with the original walk `W_N`. The latter is stated here through
its consequence on the readout block. The index convention of that consequence
(`J_N[0:3,:] D_Nᵀ = T_Nᵀ J_0[0:3,:]`) is read off from the PDF's formula
`g_N J_N[0:3,:]ᵀ = (g_0 J_0[0:3,:]ᵀ) T_N`. Re-derive it from `W_N J_N D_Nᵀ = J_0` and the
block form of `W_N` when formalizing.

Proof (PDF Lemma 1): follow the dual path of axis shifts, check that `s⁵ r_0(s)` keeps a triple
zero at the cutoff (`g''(K) = 0`), move the cutoff `0 → 2N`, and use the shift identity (4) at
each vertex. The companion coefficient stays positive and every axis step is invertible.
* Lines: ≈ 2500 (CMF definitions shared with `det_V_eq.lean` [5] ≈ 800; the second-functional
  companion relation ≈ 600; boundary zeros along the dual path ≈ 500; concomitant identity
  ≈ 600).
* Directly from the PDF: no. The PDF sketches the path. The axis matrices are specified in
  `verify_matrix.py`, the concomitant identity in `verify_pairing.py`. -/
theorem dual_transport :
    ∃ D : ℕ → Matrix (Fin 4) (Fin 4) ℚ, ∀ N,
      (∀ r, dualMoment N r = ∑ i : Fin 4, D N i r • dualMoment 0 i) ∧
      ∀ j : Fin 3, ∀ i : Fin 4, ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) * D N i r =
        ∑ k : Fin 3, T N k j * (Jmat 0 (Fin.castSucc k) i : ℚ) := by
  obtain ⟨D, hD⟩ := CMF.dual_transport'
  exact ⟨D, fun N => ⟨fun r => (hD N).1 r, (hD N).2⟩⟩

/-- **[6] Pairing and transport.** `g^{[2]}_N J_N[0:3,:]ᵀ = (g^{[2]}_0 J_0[0:3,:]ᵀ) T_N`. This
follows from [5] by exchanging the finite sums.
* Lines: proved here (given [5], by exchanging the finite sums).
* Directly from the PDF: partially ("Pairing and transport therefore give …"). -/
theorem pairing_transport (N : ℕ) (j : Fin 3) :
    ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) • dualMoment N r =
      ∑ k : Fin 3, T N k j • ∑ r : Fin 4, (Jmat 0 (Fin.castSucc k) r : ℚ) • dualMoment 0 r := by
  obtain ⟨D, hD⟩ := dual_transport
  obtain ⟨h1, h2⟩ := hD N
  simp_rw [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h2, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- **[7] Initial pairing.** `g^{[2]}_0 J_0[0:3,:]ᵀ = (-2, 2, 6Z₄)`; "the `Z₃` terms cancel
identically".
* Lines: proved here (from [4] and the explicit `J_0`).
* Directly from the PDF: yes. -/
theorem initial_pairing (k : Fin 3) :
    ∑ r : Fin 4, (Jmat 0 (Fin.castSucc k) r : ℚ) • dualMoment 0 r =
      ![(-2 : ℚ) • Zsym 0, (2 : ℚ) • Zsym 0, (6 : ℚ) • Zsym 4] k := by
  rw [dualMoment_zero]
  fin_cases k <;> simp [Fin.sum_univ_four, Jmat] <;> module

/-- **Main theorem (`blueprint.lean`, `pairing_identity`).** Proved from [3], [6], [7].
The final step reads off `q_N = 6 (T_N)_{2,·}` and `p^{(4)}_N = 2(T_N)_{0,·} - 2(T_N)_{1,·}`
from `𝓡_N = U₃₄ T_N`. -/
theorem pairing_identity (N : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ N) • Mfun (-10 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) =
      q N j • Zsym 4 - p4 N j • Zsym 0 := by
  rw [endpoint_substitution, pairing_transport]
  simp only [initial_pairing]
  simp [q, p4, Rmat, U34, Matrix.mul_apply, Fin.sum_univ_three]
  module

end ZetasIrr.BP
