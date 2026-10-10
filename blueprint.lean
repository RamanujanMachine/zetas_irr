/-
# Blueprint: a CMF proof of the linear independence of `1, ζ(3), ζ(4)`

This file is a Lean blueprint of the note
  *"A CMF proof of the linear independence of 1, ζ(3), ζ(4) — Proof development and exact
  certificates"* (6 October 2026),
whose main theorem (Theorem 1 there) is the statement of Theorem 1.6 of Li Lai's preprint
arXiv:2610.06838.

Structure (following the sections of the note):

* §0  The zeta values `ζ(3), ζ(4)`.
* §1  The formal residue functionals `𝓛_K` (Part VII §7) and `𝓜_K = -𝓛_K[f']` (Part III).
* §2  The rational sequences: kernels `R_N`, `R*_N`, the coefficient matrix `𝓒_N`, the block
      `V_N`, `T_N = V_N^{-T}` and the readout matrix `𝓡_N = U₃₄ T_N` (Parts I, VII §2).
* §3  Analytic input (Part II, VII §1, §6).
* §4  The second-derivative pairing identity (Part III).
* §5  The all-prime denominator bound `Δ_N` (Part IV, VII §3, §4).
* §6  The irrationality proof (Part V): Theorem 1 / Theorem 1.6.

All definitions (and the sanity check `zeta4_eq : ζ(4) = π⁴/90`) live in `defs.lean`.
Only `theorem`s count as blueprint nodes; there are 17 of them here. Nodes whose proof is the
mathematical content of the note are proved in `blueprints/*.lean` and imported; the logical glue
(`integer_matrix_criterion`, `det_Rmat`, the main theorem and its corollary) is proved
from the other nodes.

Remark on `V_N`. The note defines `V_N` as the upper-left `3 × 3` block of the forward walk
`W_N = M(0) ⋯ M(N-1)` of the conservative matrix field `MeijerG(5,2,5,5,1)` and proves the
coefficient identity (13) `𝓒_N = (-1)^N 𝓒₀ V_N`. Since the single-step matrices `M(n)` are not
displayed in the note, this blueprint takes (13) as the *definition* of `V_N`
(`𝓒₀` is invertible, `det 𝓒₀ = -6`); identifying it with the CMF walk is the content of
the exact certificate `verify_matrix.py` and is not needed for the deduction below.
-/
import derivSum_eq_realize_Lfun
import Mfun_sub_Mfun_pred
import det_V_eq
import readout_error_bound
import pairing_identity
import valuation_bound
import Delta_mul_Rmat_integral
import E34_le
import log_Delta_le

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr

/-! ## §1. Formal residue functionals (Part VII §7 and Part III)

Formal values are `ℚ`-linear combinations of the symbols `Z_r`; we encode them as
`ℕ →₀ ℚ`, where `single 0 1` stands for the constant `1` and `single r 1` for `Z_r`
(`r ≥ 2`). The realisation map sends `Z_r ↦ ζ(r)`. -/

/-- **Formal = analytic** (Part VII §7). For a proper rational function all of whose poles
are integers `≤ K`, the analytic sum `-∑_{t>K} f'(t)` is the realisation of `𝓛_K[f]`.
The denominator must split over `ℚ` (`hsplit`); without it the statement fails for `1/(t²+1)`. -/
theorem derivSum_eq_realize_Lfun (K : ℤ) (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree)
    (hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, n ≤ K ∧ h = n) :
    derivSum K f = realize (Lfun K f) :=
  BP.derivSum_eq_realize_Lfun K f hproper hsplit hpoles

/- **Shift identity (4)** for `𝓜` is `ZetasIrr.Mfun_sub_Mfun_pred`, imported from
`blueprints/Mfun_sub_Mfun_pred.lean`; it also needs all poles `< K` and a split denominator
(without them the identity fails for `1/(t - 5)` at `K = 0`). -/

/-! ## §2. The precise rational sequences (Parts I and VII §2) -/

theorem F_pos (N : ℕ) : 0 < F N := by
  unfold F
  refine div_pos (List.prod_pos ?_) (mul_pos (List.prod_pos ?_) (List.prod_pos ?_)) <;>
  · intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    positivity

/-- **Determinant formula (14)**: `det V_N = F_N`
(by the axis determinants, or `det B(n) = F_{n+1}/F_n`, `F_0 = 1`). -/
theorem det_V_eq (N : ℕ) : (V N).det = F N := BP.det_V_eq N

/-- **Equation (1)**: `det 𝓡_N = 36 / det V_N ≠ 0`. -/
theorem det_Rmat (N : ℕ) : (Rmat N).det = 36 / (V N).det ∧ (Rmat N).det ≠ 0 := by
  have hV : (V N).det ≠ 0 := by rw [det_V_eq]; exact (F_pos N).ne'
  have hU : U34.det = 36 := by
    rw [Matrix.det_fin_three]; simp [U34]; norm_num
  have h : (Rmat N).det = 36 / (V N).det := by
    rw [Rmat, T, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, hU,
      Ring.inverse_eq_inv', div_eq_mul_inv]
  exact ⟨h, by rw [h]; exact div_ne_zero (by norm_num) hV⟩

/- **Partial-fraction evaluation (13)** is `ZetasIrr.S_eq`, imported from
`blueprints/cross_product_readout.lean`. -/

/-! ## §3. Analytic input (Part II, Part VII §1 and §6) -/

/- **Exact cross-product readouts** (Part II) is `ZetasIrr.cross_product_readout`, imported
from `blueprints/cross_product_readout.lean`. -/

/-- **Spectral/contour estimates** (Part VII §1, §6). With
`a = 53.28758332262…` and `b = 59.51995592483…` (the two spectral rates of the limit matrix,
certified by the exact characteristic polynomial): `‖A_N‖, ‖B_N‖ ≤ e^{bN+o(N)}`,
`‖S_N‖ ≤ e^{-aN+o(N)}`, `|q_{Nj}| ≤ e^{aN+o(N)}` (2), and `det V_N ≥ e^{(2b-a)N-o(N)}`. -/
theorem growth_estimates :
    ∃ a b : ℝ, 53.28758332262 < a ∧ a < 53.28758332263 ∧
      59.51995592483 < b ∧ b < 59.51995592484 ∧
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
        (∀ j, |(coeffMat N 0 j : ℝ)| ≤ exp ((b + ε) * N) ∧
              |(coeffMat N 1 j : ℝ)| ≤ exp ((b + ε) * N) ∧
              |S N j| ≤ exp ((-a + ε) * N) ∧
              |(q N j : ℝ)| ≤ exp ((a + ε) * N)) ∧
        exp ((2 * b - a - ε) * N) ≤ ((V N).det : ℝ) :=
  BP.growth_estimates

/-- **Error estimate (3)**: `|q_{Nj}ζ(3) - p^{(3)}_{Nj}| + |q_{Nj}ζ(4) - p^{(4)}_{Nj}| ≤ e^{-bN+o(N)}`.
Follows from `cross_product_readout` and `growth_estimates`. -/
theorem readout_error_bound :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ j,
      |ζ3 * q N j - p3 N j| + |ζ4 * q N j - p4 N j| ≤ exp ((-59.51995592483 + ε) * N) :=
  BP.readout_error_bound

/-! ## §4. The second-derivative identity (Part III) -/

/-- **Pairing identity (6)**, coefficientwise for all `N` (from Lemma 1 — the dual moments
defined by `𝓜` have the same CMF transport as the first-functional moments, with final
cutoff `K = 2N` — together with `g₀^{[2]} J₀[0:3,:]ᵀ = (-2, 2, 6Z₄)`):
`(-1)^N 𝓜_{-10N-1}[Q_{Nj}(t) R*_N(t)] = Z₄ q_{Nj} - p^{(4)}_{Nj}`. -/
theorem pairing_identity (N : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ N) • Mfun (-10 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) =
      q N j • Zsym 4 - p4 N j • Zsym 0 :=
  BP.pairing_identity N j

/-! ## §5. The all-prime denominator bound (Part IV, Part VII §3–4) -/

/-- **Local denominator bounds** (Lemma 2 and Part IV): at every prime `p`, each entry of
`𝓡_N` has `p`-adic valuation at least `-E₃₄(N,p)` (and is `p`-integral for `p > 29N+1`).
Combines the original-kernel bounds `E_o, E_{o4}` with the dual bounds `E_d` (from (15)) and
`E_{d4}` (from (6)); the better bound is taken at each prime. -/
theorem valuation_bound (N : ℕ) (hN : 1 ≤ N) (p : ℕ) [Fact p.Prime] (i j : Fin 3)
    (hne : Rmat N i j ≠ 0) :
    (if p ≤ 29 * N + 1 then -E34 N p else 0) ≤ padicValRat p (Rmat N i j) :=
  BP.valuation_bound N hN p i j hne

/- **All-`N` integrality theorem (8)** `Delta_mul_Rmat_integral` and the uniform bound `E34_le`
are imported from `blueprints/Delta_mul_Rmat_integral.lean` and `blueprints/E34_le.lean`. -/

/-- **Growth of `Δ_N` (10)**: `limsup (log Δ_N)/N ≤ c₃₄ = c₃ + 19 = 57.78399331966… < 57.784`.
Proof: the floor-chamber profile `e₃₄(x) = e₃(x) + 𝟙_{x > 1/19}` (9) (a finite exact check of
the 270 Farey-29 chambers), `E34_le` for small primes, and the prime number theorem. -/
theorem log_Delta_le : ∀ᶠ N : ℕ in atTop, Real.log (Delta N) ≤ 57.784 * N :=
  BP.log_Delta_le

/-! ## §6. The irrationality proof (Part V) -/

/-- **Elementary integer-matrix lemma** (formalisation obligation 1). If there are integer
matrices `Z_N` with rows `P_N, P'_N, Q_N`, eventually invertible, such that
`‖α Q_N - P_N‖ + ‖β Q_N - P'_N‖ → 0`, then `1, α, β` are linearly independent over `ℚ`. -/
theorem integer_matrix_criterion (α β : ℝ) (Z : ℕ → Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : ∀ᶠ N in atTop, (Z N).det ≠ 0)
    (hsmall : ∀ j, Tendsto (fun N => |α * Z N 2 j - Z N 0 j| + |β * Z N 2 j - Z N 1 j|)
      atTop (𝓝 0)) :
    LinearIndependent ℚ ![(1 : ℝ), α, β] := by
  rw [← LinearIndependent.iff_fractionRing (R := ℤ), Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zsmul_eq_mul, mul_one] at hg
  -- the integer row vector `w = (g₁, g₂, g₀)`
  set w : Fin 3 → ℤ := ![g 1, g 2, g 0] with hw
  have key : ∀ N j, (((w ᵥ* Z N) j : ℤ) : ℝ) =
      -(g 1 * (α * Z N 2 j - Z N 0 j) + g 2 * (β * Z N 2 j - Z N 1 j)) := by
    intro N j
    have : (g 0 : ℝ) = -(g 1 * α + g 2 * β) := by linarith
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hw, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    rw [this]; ring
  -- each component tends to zero, hence is eventually `0`
  have hev : ∀ j, ∀ᶠ N in atTop, (w ᵥ* Z N) j = 0 := by
    intro j
    have ht : Tendsto (fun N => (|(g 1 : ℝ)| + |(g 2 : ℝ)|) *
        (|α * Z N 2 j - Z N 0 j| + |β * Z N 2 j - Z N 1 j|)) atTop (𝓝 0) := by
      simpa using (hsmall j).const_mul (|(g 1 : ℝ)| + |(g 2 : ℝ)|)
    filter_upwards [ht.eventually (gt_mem_nhds one_pos)] with N hN
    have hle : |(((w ᵥ* Z N) j : ℤ) : ℝ)| ≤ (|(g 1 : ℝ)| + |(g 2 : ℝ)|) *
        (|α * Z N 2 j - Z N 0 j| + |β * Z N 2 j - Z N 1 j|) := by
      rw [key, abs_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      nlinarith [abs_nonneg (g 1 : ℝ), abs_nonneg (g 2 : ℝ),
        abs_nonneg (α * Z N 2 j - Z N 0 j), abs_nonneg (β * Z N 2 j - Z N 1 j)]
    have h1 : |(((w ᵥ* Z N) j : ℤ) : ℝ)| < 1 := lt_of_le_of_lt hle hN
    rw [← Int.cast_abs] at h1
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  obtain ⟨N, hN, hdetN⟩ := ((eventually_all.mpr hev).and hdet).exists
  have hw0 : w = 0 := by
    by_contra hne
    exact hdetN (Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hne, funext hN⟩)
  have h1 : g 1 = 0 := by simpa [hw] using congrFun hw0 0
  have h2 : g 2 = 0 := by simpa [hw] using congrFun hw0 1
  have h0 : g 0 = 0 := by simpa [hw] using congrFun hw0 2
  intro i
  fin_cases i <;> assumption

/-- **Theorem 1 (= Theorem 1.6 of Lai, arXiv:2610.06838).**
The numbers `1, ζ(3), ζ(4)` are linearly independent over `ℚ`.

Proof: `𝓩_N = Δ_N 𝓡_N` is an integer matrix (8) with `det 𝓩_N = 36 Δ_N³ / det V_N ≠ 0` (1),
and by (3), (10): `‖ζ(3)Q_N - P^{(3)}_N‖ + ‖ζ(4)Q_N - P^{(4)}_N‖ ≤ e^{-(b - c₃₄)N + o(N)} → 0`.
Conclude with `integer_matrix_criterion`. -/
theorem theorem_1_6 : LinearIndependent ℚ ![(1 : ℝ), ζ3, ζ4] := by
  choose z hz using Delta_mul_Rmat_integral
  set Z : ℕ → Matrix (Fin 3) (Fin 3) ℤ := fun N => Matrix.of fun i j => z N i j with hZ
  have hZQ : ∀ N, (Z N).map (Int.cast : ℤ → ℚ) = (Delta N : ℚ) • Rmat N := by
    intro N; ext i j; simp [hZ, hz]
  have hΔ : ∀ N, (Delta N : ℚ) ≠ 0 := by
    intro N
    unfold Delta
    split_ifs
    · norm_num
    · rw [Nat.cast_prod]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have := (Finset.mem_filter.mp hp).2.pos
      positivity
  apply integer_matrix_criterion ζ3 ζ4 Z
  · refine Eventually.of_forall fun N hdet => ?_
    have h := congrArg Matrix.det (hZQ N)
    have hd : ((Z N).map (Int.cast : ℤ → ℚ)).det = ((Z N).det : ℚ) := by
      rw [show (Z N).map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix (Z N) from rfl,
        ← RingHom.map_det]; rfl
    rw [hd, Matrix.det_smul, hdet] at h
    simp only [Int.cast_zero, Fintype.card_fin] at h
    exact (mul_ne_zero (pow_ne_zero _ (hΔ N)) (det_Rmat N).2) h.symm
  · intro j
    -- `Δ_N · err_N ≤ e^{57.784 N} e^{(-59.51995592483 + 1) N} → 0`
    have hentry : ∀ N i, ((Z N i j : ℤ) : ℝ) = (Delta N : ℝ) * (Rmat N i j : ℝ) := by
      intro N i
      have := congrFun (congrFun (hZQ N) i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact_mod_cast this
    have hlim : Tendsto (fun N : ℕ => exp ((57.784 + (-59.51995592483 + 1)) * N)) atTop
        (𝓝 0) := by
      refine tendsto_exp_atBot.comp ?_
      exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by norm_num)
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
    filter_upwards [log_Delta_le, readout_error_bound 1 one_pos,
      eventually_ge_atTop 1] with N hlog herr hN1
    have hpos : (0 : ℝ) < Delta N := by exact_mod_cast Nat.pos_of_ne_zero (by
      intro h0; exact hΔ N (by exact_mod_cast h0))
    have hD : (Delta N : ℝ) ≤ exp (57.784 * N) := by
      rw [← exp_log hpos]; exact exp_le_exp.mpr hlog
    calc |ζ3 * ((Z N 2 j : ℤ) : ℝ) - ((Z N 0 j : ℤ) : ℝ)| +
          |ζ4 * ((Z N 2 j : ℤ) : ℝ) - ((Z N 1 j : ℤ) : ℝ)|
        = (Delta N : ℝ) * (|ζ3 * q N j - p3 N j| + |ζ4 * q N j - p4 N j|) := by
          rw [hentry, hentry, hentry, mul_add, ← abs_of_pos hpos, ← abs_mul, ← abs_mul,
            abs_of_pos hpos]
          congr 2 <;> ring
      _ ≤ exp (57.784 * N) * exp ((-59.51995592483 + 1) * N) :=
          mul_le_mul hD (herr j) (by positivity) (by positivity)
      _ = exp ((57.784 + (-59.51995592483 + 1)) * N) := by rw [← exp_add]; ring_nf

/-- **Corollary.** For every `(A, B) ∈ ℚ² \ {(0,0)}`, `A ζ(3) + B ζ(4)` is irrational. -/
theorem irrational_combination (A B : ℚ) (hAB : (A, B) ≠ (0, 0)) :
    Irrational (A * ζ3 + B * ζ4) := by
  rintro ⟨r, hr⟩
  have h := Fintype.linearIndependent_iff.mp theorem_1_6 ![-r, A, B] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def, mul_one]
    push_cast; rw [hr]; ring)
  exact hAB (Prod.ext (by simpa using h 1) (by simpa using h 2))

end ZetasIrr
