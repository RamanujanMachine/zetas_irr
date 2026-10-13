/-
# Blueprint: forward `₅F₄` readouts, a uniform common divisor, and `1, ζ(3), ζ(4)`

This file is a Lean blueprint of `manuscript.tex` in this folder,
  *"Hypergeometric readouts, a uniform common divisor, and a conditional irrationality
  criterion"*,
the alternative (simpler) proof of the linear independence of `1, ζ(3), ζ(4)` over `ℚ`.

It imports `Pfq54_defs` and the sixteen node files `<node>.lean` of this folder (lean_libs,
namespace `Pfq54.BP`), and is checked from the project root with
  `lake env lean pfq54_formalization_handoff/Blueprint_pfq54.lean`.

Structure (following the manuscript):

* §1  The conceptual integer obstruction (Proposition 1).
* §2  The forward `₅F₄` polynomial and its coefficient normalization `E_n` (§2–3, eq. (B)).
* §3  Harmonic readouts `S₀, S₃, S₄` from the five-binomial jets, and the integers
      `Z_{i,n} = 6 D_n⁴ S_{i,n}` (§5–6, Proposition 2).
* §4  Factorial permutations (§7, Lemma `arith-integral`).
* §5  The stronger divisor `G_n` (appendix: eight pairings, upper harmonic ranges, one
      complete residue block) and the height bound `Z₀/G_n ≤ e^{112.5 n}`.
* §6  The analytic module (§4 and Appendix A): Meijer-G initial values and decay, the exact
      spectral certificate, the modal-basis theorem, the dual-mode transfer, the error bound.
* §7  Nonvanishing for every nonzero pair, and the main theorem.

Only `theorem`s count as blueprint nodes; there are 20 of them. Each docstring records whether
the manuscript proves the node (`From the manuscript: yes / partially / no`). The sixteen nodes
carrying the mathematical content are proved in their node files and invoked here as
`BP.<node>` (the statements are verbatim copies); the logical glue (`integer_obstruction`,
`height_bound`, `irrational_combination` and `main_theorem`) is proved from the other nodes.
This file is `sorry`-free.

**Conditionality.** The manuscript's result is conditional on the general `modal_basis`
theorem and on exact matrix identities whose matrices (`F(n)`, `G(n)`, `M_G(n)`) are not printed
there. In this formalization `modal_basis` is proved (Levinson's theorem, `lev_aux1`–`lev_aux6`),
the matrices are constructed inside the node files (`G(n) = -W(n)` from the CMF path matrix of
`blueprints/CMF_path.lean`, `F(n)` from the intertwining in `gdual.lean`, `M_G(n)` from the
Krylov matrices in `cas_aux.lean`, with the Casoratian nonvanishing certified at 511 points in
`cas_cert0`–`cas_cert7`), and every statement below is still about explicitly defined objects
(finite sums, factorials, a Mellin–Barnes integral, an explicit cubic).
The only remaining assumption is the prime number theorem `θ(x) ~ x`
(`prime_number_theorem` in `blueprints/log_Delta_le.lean`, used through `log_G_ge` and
`log_Z0_le`), which the manuscript also cites as a black box: `#print axioms main_theorem`
lists `sorryAx` from that single lemma.

**Normalization.** The numerator readouts are defined directly as the explicit finite sums
(15)–(17) of the manuscript, through the dual-number jets of the five binomial factors (`T`).
The manuscript's partial-fraction normalization `(Q_n, P_{3,n}, P_{4,n})` is
`(-1)^n C_n^{-1} (S₀, S₃, S₄)` with `C_n = (15n)!²/(10n)!³` (§8 of the manuscript); it is used
only in `residue_block`.
-/
import Pfq54_defs
import hyp_readout
import Z_integral
import permutation_lemma
import pairing_bound
import upper_range_bound
import residue_block
import G_dvd_Z
import log_G_ge
import log_Z0_le
import meijerG_initial
import meijerG_decay
import spectral_certificate
import modal_basis
import dual_mode_transfer
import error_bound
import nonvanishing

open Filter Topology Real Finset
open scoped Matrix

noncomputable section

namespace Pfq54

/-! ## §1. The conceptual argument (Proposition 1 of the manuscript) -/

/-- **The integer obstruction** (Proposition `conceptual-criterion`, and the Corollary of §8).
If integers `u_n, v_n` satisfy `u_n α - v_n → 0` and `u_n α - v_n ≠ 0` for infinitely many
`n`, then `α` is irrational: if `α = a/b`, then `|u_n α - v_n| = |a u_n - b v_n|/b ≥ 1/b`
whenever it is nonzero.
* From the manuscript: yes. -/
theorem integer_obstruction (α : ℝ) (u v : ℕ → ℤ)
    (hsmall : Tendsto (fun n => (u n : ℝ) * α - v n) atTop (𝓝 0))
    (hne : ∃ᶠ n in atTop, (u n : ℝ) * α - v n ≠ 0) : Irrational α := by
  rintro ⟨q, rfl⟩
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hb : (0 : ℝ) < 1 / q.den := by positivity
  obtain ⟨n, hn, hne⟩ :=
    ((hsmall.eventually (Metric.ball_mem_nhds 0 hb)).and_frequently hne).exists
  have key : (u n : ℝ) * (q : ℝ) - v n = ((u n * q.num - v n * q.den : ℤ) : ℝ) / q.den := by
    rw [Rat.cast_def]; push_cast; field_simp
  rw [Real.dist_eq, sub_zero, key, abs_div, abs_of_pos hd,
    div_lt_div_iff_of_pos_right hd] at hn
  rw [key] at hne
  have hz : (u n * q.num - v n * q.den : ℤ) ≠ 0 := by
    intro h; apply hne; rw [h]; simp
  have h1 : (1 : ℝ) ≤ |((u n * q.num - v n * q.den : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
  linarith

/-! ## §3. Harmonic readouts and the integer normalization (§5–6 of the manuscript)

A *jet* is a pair (value, first `ε`-derivative at `ε = 0`), i.e. a dual number; jets multiply
by `(a,a')(b,b') = (ab, a'b + ab')`. The explicit rational jets below avoid the Gamma function
(`PROOF_STRUCTURE.md`, §C). -/

/-- **Coefficient normalization** (eq. (B) and (S0)). For `n ≥ 1` and `0 ≤ k ≤ 14n`,
`U_{n,2n+k} = B_{n,k} = E_n t_{n,k}` (the five-binomial integer), hence
`S_{0,n} = E_n 𝓕_n(1)`; equivalently `r_Q W_n e₀ = 12 S_{0,n}/E_n`.
* From the manuscript: yes (factorial cancellation; term ratio comparison in Appendix C.1). -/
theorem hyp_readout (n : ℕ) (hn : 1 ≤ n) :
    (∀ k ≤ 14 * n, U n (2 * n + k) = E n * hypTerm n k) ∧ S0 n = E n * hyp n := by
  exact BP.hyp_readout n hn

/-- **Proposition 2 (`integral`).** For `n ≥ 1` and all `j`: `U_{n,j} ∈ ℤ`, `D_n V_{n,j} ∈ ℤ`;
consequently `Z_{i,n} = 6 D_n⁴ S_{i,n} ∈ ℤ`. Moreover `S_{0,n} > 0`.
Proof: binomial products; the derivative of `C(x, M)` at an integer is cleared by `d_M`
(Vandermonde), the exterior derivatives `M!(r-1)!/(M+r)!` by `d_{M+r}`; then
`d_M^r H^{(r)}_m ∈ ℤ` for `m ≤ M`. Positivity: `U_{n,j} ≥ 0` and `U_{n,2n} = E_n > 0`.
* From the manuscript: yes. -/
theorem Z_integral (n : ℕ) (hn : 1 ≤ n) :
    (∀ j, ∃ z : ℤ, U n j = z) ∧ (∀ j, ∃ z : ℤ, (D n : ℚ) * V n j = z) ∧
      (∀ i, ∃ z : ℤ, Zv n i = z) ∧ 0 < S0 n := by
  exact BP.Z_integral n hn

/-! ## §4. Factorial permutations (§7 of the manuscript, Lemma `arith-integral`) -/

/-- **Permutation lemma** ((permutation) and Lemma `arith-integral`). For every permutation `b`
of `(-2,-1,0,1,2)`: `𝒯^b_{n,j} = λ_{n,b} 𝒯_{n,j}` as jets for `j ≤ 17n` (the five Gamma
factors `Γ(j - b_i n + 1 - ε)` are merely permuted), and the integrality proof of `Z_integral`
applies to `𝒯^b`, so `λ_{n,b} U_{n,j} ∈ ℤ`, `D_n λ_{n,b} V_{n,j} ∈ ℤ` and `λ_{n,b} Z_{i,n} ∈ ℤ`.
* From the manuscript: yes. -/
theorem permutation_lemma (σ : Equiv.Perm (Fin 5)) (n : ℕ) (hn : 1 ≤ n) :
    (∀ j ≤ 17 * n, coeffJetPerm σ n j = lam σ n • coeffJet n j) ∧
      (∀ j, ∃ z : ℤ, lam σ n * U n j = z) ∧ (∀ j, ∃ z : ℤ, (D n : ℚ) * lam σ n * V n j = z) ∧
      ∀ i, ∃ z : ℤ, lam σ n * Zv n i = z := by
  exact BP.permutation_lemma σ n hn

/-! ## §5. The stronger divisor `G_n` (Appendix B–G of the manuscript) -/

/-- **Pairing bound** (arith-pairbound). For eligible `p`, `p^{φ(n/p)}` divides all three
`Z_{i,n}`: from `permutation_lemma` for the eight pairings, `v_p(Z_i) ≥ v_p(C_n/C_b)` and
Legendre's formula `v_p(C_n/C_b) = c(n/p) - ∑_D ⌊dn/p⌋ + ∑_L ⌊ln/p⌋` (all factorial
arguments are `< p²`).
* From the manuscript: yes. -/
theorem pairing_bound (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (i : Fin 3) :
    ∃ z : ℤ, Zv n i = (p : ℚ) ^ (phi ((n : ℚ) / p)).toNat * z := by
  exact BP.pairing_bound n p hn hp i

/-- **Upper harmonic ranges** (arith-upperrange). For eligible `p` with `16n < p < 19n`,
`p^{h_n(p)}` divides all three `Z_{i,n}` (gains `3, 2, 1` on `(18n,19n), (17n,18n), (16n,17n)`).
* From the manuscript: partially (the valuation table for `a_j, b_j` is asserted with a short
  justification "logarithmic differentiation loses at most one `p`"). -/
theorem upper_range_bound (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hlo : 16 * n < p) (hhi : p < 19 * n) (i : Fin 3) :
    ∃ z : ℤ, Zv n i = (p : ℚ) ^ hgain n p * z := by
  exact BP.upper_range_bound n p hn hp hlo hhi i

/-- **One complete residue block** (Lemma `arith-block`). For an eligible prime
`8n < p < 11n`: `v_p(Q_n) ≥ 1`, `v_p(P_{3,n}) ≥ -1`, `v_p(P_{4,n}) ≥ -2`.
Proof: root-count lemma (arith-support), `T = (X^p - X) N̄/D̄ ∈ 𝔽_p[X]` of degree `p - 2`, the
local identity (arith-local), and `∑_{k ∈ 𝔽_p} T(k) = 0`.
* From the manuscript: yes. -/
theorem residue_block (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hlo : 8 * n < p) (hhi : p < 11 * n) :
    1 ≤ padicValRat p (Qa n) ∧ -1 ≤ padicValRat p (P3a n) ∧ -2 ≤ padicValRat p (P4a n) := by
  exact BP.residue_block n p hn hp hlo hhi

/-- **Theorem `arith-main`, divisibility.** `G_n` divides `Z_{0,n}, Z_{3,n}, Z_{4,n}`.
Proof: at each eligible prime, combine `pairing_bound`, `upper_range_bound` (where `φ(n/p) = 0`)
and `residue_block` (which gives `c(n/p) + 2 ≥ φ(n/p) + 1` on `8n < p < 11n`), using the
finite profile facts (arith-profilefacts); the two extra ranges are disjoint.
* From the manuscript: partially (the profile facts are finite floor-function checks). -/
theorem G_dvd_Z (n : ℕ) (hn : 1 ≤ n) (i : Fin 3) : ∃ z : ℤ, Zv n i = Gdiv n * z := by
  exact BP.G_dvd_Z n hn i

/-- **Growth of the divisor** (Theorem `arith-main`):
`liminf (log G_n)/n ≥ S₈ + 9 > 29.004`, from the exact rational sum `S₈ > 20.004` over the
profile table, the prime number theorem, and the extra contributions `6 + 3`.
* From the manuscript: partially (uses the prime number theorem, not proved there). -/
theorem log_G_ge : ∀ᶠ n : ℕ in atTop, 29.004 * n ≤ Real.log (Gdiv n) := by
  exact BP.log_G_ge

/-- **Size of the integer normalization**:
`limsup log(Z_{0,n})/n ≤ 65.46 + 76`, from uniform Stirling bounds,
`limsup log(C_n |Q_n|)/n ≤ 30 log(3/2) + max_{[2,16]} g < 65.46` (concavity and rational
log-series bounds), and `log d_{19n} = 19n + o(n)` (prime number theorem).
* From the manuscript: partially (uses the prime number theorem). -/
theorem log_Z0_le : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    Real.log (Zv n 0 : ℝ) ≤ (65.46 + 76 + ε) * n := by
  exact BP.log_Z0_le

/-- **Height bound**: `ũ_n = Z_{0,n}/G_n ≤ e^{112.5 n}` for all large `n`, since
`65.46 + 76 - 29.004 < 112.5`. Proved from `Z_integral`, `log_G_ge`, `log_Z0_le`.
* From the manuscript: yes. -/
theorem height_bound : ∀ᶠ n : ℕ in atTop, (Zv n 0 : ℝ) / Gdiv n ≤ exp (112.5 * n) := by
  filter_upwards [log_G_ge, log_Z0_le 0.04 (by norm_num), eventually_ge_atTop 1]
    with n hG hZ hn
  have hS := (Z_integral n hn).2.2.2
  have hZpos : (0 : ℝ) < (Zv n 0 : ℝ) := by
    have hD : (0 : ℚ) < D n := by
      have : 0 < D n := Nat.pos_of_ne_zero (by
        simp only [D, ne_eq, Finset.lcm_eq_zero_iff, Finset.mem_Icc, id_eq]
        omega)
      exact_mod_cast this
    have : (0 : ℚ) < Zv n 0 := by simp only [Zv, Matrix.cons_val_zero]; positivity
    exact_mod_cast this
  have hGpos : (0 : ℝ) < Gdiv n := by
    have : 0 < Gdiv n := by
      unfold Gdiv
      exact Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp hp).2.1.pos _
    exact_mod_cast this
  rw [div_le_iff₀ hGpos, ← exp_log hZpos, ← exp_log hGpos, ← exp_add]
  exact exp_le_exp.mpr (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-! ## §6. The analytic module (§4 and Appendix A of the manuscript)

The Meijer-G function along the dual trajectory is
`𝒢_n(z) = G^{5,2}_{5,5}(z | -16n,-17n; 1+11n,1+12n,2+10n / -2n,-n,0,n,2n)`, given by the
Mellin–Barnes integral over `Re s = 2n + 1/2`. Since `θ = z d/dz` multiplies the integrand by
`-s`, the state `𝒮_G(n) = (θ^k 𝒢_n)(1)_{k=0..3}` is defined directly by that integral at
`z = 1`. -/

/-- **Initial values** (Proposition `z34-initial-values`):
`𝒮_G(0) = (1 - 2ζ(3) + 3ζ(4), 1 - 2ζ(3), 1, 1 - ζ(2))`; hence, with
`I_G = ((2B, -3A-2B, 3A, 0), (0,0,6,0))`, `I_G 𝒮_G(0)ᵀ = 6 (A ζ(3) + B ζ(4), 1)ᵀ`.
Proof: reflection gives the integrand `π² / (sin²(πs) s³ (s+1))`; close the contour to the right
and sum the double-pole residues.
* From the manuscript: yes. -/
theorem meijerG_initial :
    SG 0 0 = 1 - 2 * riemannZeta 3 + 3 * riemannZeta 4 ∧ SG 0 1 = 1 - 2 * riemannZeta 3 ∧
      SG 0 2 = 1 ∧ SG 0 3 = 1 - riemannZeta 2 := by
  exact BP.meijerG_initial

/-- **Decay of the Meijer-G state** (Proposition `z34-growth`). For `n ≥ 1`, `𝒢_n(1)` is given
by a positive four-variable integral (beta integrals, Mellin inversion, Fubini), so it is real
and positive, and `|(θ^k 𝒢_n)(1)| ≤ (16n+1)^k 𝔡_n` for `k ≤ 3` (nonnegative rising-factorial
expansions of `(w + 2n)^k`). Moreover `𝔡_{n+1} ≤ η 𝔡_n` for `n ≥ 2`, and `η < 1`; hence
`(θ^k 𝒢_n)(1) = O(n^k η^n)`.
* From the manuscript: yes. -/
theorem meijerG_decay :
    (∀ n ≥ 1, 0 < (SG n 0).re ∧ (SG n 0).im = 0 ∧
        ∀ k ≤ 3, ‖SG n k‖ ≤ (16 * n + 1 : ℝ) ^ k * dfrak n) ∧
      (∀ n ≥ 2, dfrak (n + 1) ≤ eta * dfrak n) ∧ eta < 1 := by
  exact BP.meijerG_decay

/-- **Exact spectral certificate** (Appendix A, "Exact spectral data"). `χ` has a real root
`ρ₄ = r` with `0 < r < u = 7203/10²⁷`; every other (complex) root `z` has `r < ε |z|` with
`ε = 102/10⁵¹`, i.e. `ϑ = |ρ₄|/|ρ₁| < ε`; and `ε < e^{-112.8}`.
Proof: negative discriminant, `c > 0`, `χ(0) < 0 < χ(u)`, `u³ < c ε²`, `|ρ₁|² = c/r`; dyadic
reduction and rational log-series bounds.
* From the manuscript: yes (exact rational arithmetic). -/
theorem spectral_certificate :
    ∃ r : ℝ, 0 < r ∧ r < 7203 / 10 ^ 27 ∧ (chi.map (algebraMap ℚ ℝ)).eval r = 0 ∧
      (∀ z : ℂ, (chi.map (algebraMap ℚ ℂ)).eval z = 0 → z ≠ r → r < 102 / 10 ^ 51 * ‖z‖) ∧
      (102 / 10 ^ 51 : ℝ) < exp (-112.8) := by
  exact BP.spectral_certificate

/-- **The modal-basis theorem** (§4.1, the general asymptotic dependency). Let `Q(n)` be
invertible `3 × 3` matrices with rational-function entries (no poles at `n ∈ ℕ`) whose balanced
matrices `T_n Q(n) T_{n+1}^{-1}` tend to an invertible `Q_∞` with distinct eigenvalues. Then
there are independent row solutions `B_n = B₀ W_Q(n)` and nonzero scalars `a_i(n)` with
`diag(a(n))⁻¹ B_n T_n⁻¹ → Y` invertible, the rows of `Y` left eigenvectors of `Q_∞` with
eigenvalues `ρ_i`, and `|a_i(n)|^{1/n} → |ρ_i|` (Birkhoff–Adams theory).
* From the manuscript: no (stated as an external dependency, not proved). -/
theorem modal_basis (Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ))
    (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
      Q n i j = (((Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) : ℚ) : ℂ))
    (hdet : ∀ n, (Q n).det ≠ 0) (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hlim : Tendsto (fun n => balance n * Q n * (balance (n + 1))⁻¹) atTop (𝓝 Qinf))
    (hinf : Qinf.det ≠ 0) (hsep : Qinf.charpoly.Separable) :
    ∃ (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3 → ℕ → ℂ) (ρ : Fin 3 → ℂ),
      B₀.det ≠ 0 ∧ Y.det ≠ 0 ∧ Function.Injective ρ ∧ (∀ i n, a i n ≠ 0) ∧
      Tendsto (fun n => Matrix.diagonal (fun i => (a i n)⁻¹) * (B₀ * walk Q n) *
        (balance n)⁻¹) atTop (𝓝 Y) ∧
      (∀ i, Y i ᵥ* Qinf = ρ i • Y i) ∧
      ∀ i, Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 ‖ρ i‖) := by
  exact BP.modal_basis Qr Q hQ hdet Qinf hlim hinf hsep

/-- **Dual mode transfer** (Lemma `dual-mode-transfer`). Suppose `B_n = B₀ W_Q(n)` and nonzero
`a_i(n)` with `diag(a(n))⁻¹ B_n T_n⁻¹ → Y ∈ GL₃`, `|a₁(n)|^{1/n} → r`,
`|a₂(n)|^{1/n}, |a₃(n)|^{1/n} → R`, `0 < r < R`. Let `s₀` be the first row of `B₀`, columns
`v_n` with `T_n^{-T} v_n → w` and `(Y^{-T} w)₁ ≠ 0`, and rows `ℓ₁, ℓ₂` with `ℓ₂ s₀ᵀ ≠ 0`. Then
the ratio of `ℓ₁, ℓ₂` on `W_Q(n)^{-T} v_n` is eventually defined, and its distance to
`α = ℓ₁ s₀ᵀ / ℓ₂ s₀ᵀ` is eventually `≤ θ^n` for every `θ > r/R`
(i.e. `limsup |ratio - α|^{1/n} ≤ r/R`).
* From the manuscript: yes (elementary linear algebra). -/
theorem dual_mode_transfer (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (hQ : ∀ n, (Q n).det ≠ 0)
    (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (hB₀ : B₀.det ≠ 0) (hY : Y.det ≠ 0)
    (a : Fin 3 → ℕ → ℂ) (ha : ∀ i n, a i n ≠ 0)
    (hconv : Tendsto (fun n => Matrix.diagonal (fun i => (a i n)⁻¹) * (B₀ * walk Q n) *
      (balance n)⁻¹) atTop (𝓝 Y))
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (ha₁ : Tendsto (fun n : ℕ => ‖a 0 n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 r))
    (ha₂₃ : ∀ i ≠ 0, Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 R))
    (v : ℕ → Fin 3 → ℂ) (w : Fin 3 → ℂ)
    (hv : Tendsto (fun n => ((balance n)⁻¹)ᵀ *ᵥ v n) atTop (𝓝 w))
    (hw : ((Y⁻¹)ᵀ *ᵥ w) 0 ≠ 0) (ℓ₁ ℓ₂ : Fin 3 → ℂ) (hℓ₂ : ℓ₂ ⬝ᵥ B₀ 0 ≠ 0) :
    (∀ᶠ n in atTop, ℓ₂ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n) ≠ 0) ∧
      ∀ θ > r / R, ∀ᶠ n in atTop,
        ‖(ℓ₁ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n)) / (ℓ₂ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n)) -
          (ℓ₁ ⬝ᵥ B₀ 0) / (ℓ₂ ⬝ᵥ B₀ 0)‖ ≤ θ ^ n := by
  exact BP.dual_mode_transfer Q hQ B₀ Y hB₀ hY a ha hconv r R hr hrR ha₁ ha₂₃ v w hv hw ℓ₁ ℓ₂ hℓ₂

/-- **The limit and its exponential rate** (Theorem `z34-limit` with (walk-readout), eq.
(geometric-error)). For every `A, B ∈ ℤ`, `|α_{A,B} - r_n(A,B)| ≤ ε^n` for all large `n`, with
`ε = 102/10⁵¹ > ϑ = |ρ₄|/|ρ₁|`.
Proof (walk level; the matrices `F(n)`, `G(n) = [[Q(n), b(n)], [0, -1]]` come from the
certificate script): the forward ratio `R_N = (I_F W_F(N) v)₁ / (I_F W_F(N) v)₂` equals
`r_N(A,B)` by the readout bridge `r_{A,B} W_n e₀ = 12 (A S₃ + B S₄)/E_n`,
`r_Q W_n e₀ = 12 S₀/E_n` (Appendix H, gauge `M_G(n) = (κ_{n+1}/κ_n) K(n)⁻¹ H(n) K(n+1)`);
the rank-three intertwining `F(n) K(n+1) G(n)ᵀ = R(n) K(n)` with `K = E H J` telescopes to
`I_F W_F(N) v = 2 (∏ R) Î_G W_Q(N)^{-T} H(N)⁻¹ e₀`; `meijerG_decay` and `modal_basis` make the
state `𝒮̂_G` the recessive row; `dual_mode_transfer` with `w = (1,10,100)ᵀ` (nonzero cyclic
determinant) and the pairing `meijerG_initial` (`= 6`, `6 α_{A,B}`) give the limit, and
`spectral_certificate` gives the rate.
* From the manuscript: no — conditional on `modal_basis` and on the certificate-checked matrix
  identities (whose matrices are not printed in the manuscript). -/
theorem error_bound (A B : ℤ) :
    ∀ᶠ n : ℕ in atTop, |alpha A B - approx n A B| ≤ (102 / 10 ^ 51 : ℝ) ^ n := by
  exact BP.error_bound A B

/-! ## §7. Nonvanishing and the main theorem -/

/-- **Nonvanishing for every fixed nonzero pair** (§8.1). For `(A, B) ≠ (0, 0)`,
`α_{A,B} ≠ r_n(A,B)` for infinitely many `n`, without assuming `α_{A,B} ≠ 0`.
Proof: by the readout bridge, `z_n = (-1)^n (α Q_n - A P_{3,n} - B P_{4,n})` solves the
companion recurrence `z_{n+3} = c₀(n) z_n + c₁(n) z_{n+1} + c₂(n) z_{n+2}` with `c₀(n) ≠ 0`,
with initial row `(α, -A, -B) S`, `S = R U(0)` invertible (`det S ≡ 1 mod 101`). Eventual zeros
propagate backwards to `z₀ = z₁ = z₂ = 0`, forcing `α = A = B = 0`.
* From the manuscript: partially (the companion `C^{(G)}(n)` and `U(n)` are certificate data,
  not printed). -/
theorem nonvanishing (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ᶠ n : ℕ in atTop, alpha A B ≠ approx n A B := by
  exact BP.nonvanishing A B hAB

/-- **Irrationality of every nonzero combination** (Theorem `conditional-completion`):
for `(A, B) ∈ ℤ² \ {0}`, `A ζ(3) + B ζ(4)` is irrational. Apply `integer_obstruction` to
`ũ_n = Z_{0,n}/G_n`, `ṽ_n = (A Z_{3,n} + B Z_{4,n})/G_n`: `0 < ũ_n |α - r_n| ≤
e^{112.5 n} ε^n → 0`, nonzero infinitely often by `nonvanishing`.
* From the manuscript: yes. -/
theorem irrational_combination (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    Irrational (alpha A B) := by
  -- the integers `ũ_n` and `ṽ_n`
  choose z hz using fun n (hn : 1 ≤ n) (i : Fin 3) => G_dvd_Z n hn i
  let u : ℕ → ℤ := fun n => if h : 1 ≤ n then z n h 0 else 0
  let v : ℕ → ℤ := fun n => if h : 1 ≤ n then A * z n h 1 + B * z n h 2 else 0
  have hD : ∀ n, (0 : ℚ) < D n := fun n => by
    have : 0 < D n := Nat.pos_of_ne_zero (by
      simp only [D, ne_eq, Finset.lcm_eq_zero_iff, Finset.mem_Icc, id_eq]
      omega)
    exact_mod_cast this
  have hG : ∀ n, (0 : ℚ) < Gdiv n := fun n => by
    have : 0 < Gdiv n := by
      unfold Gdiv
      exact Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp hp).2.1.pos _
    exact_mod_cast this
  -- `ũ_n > 0` and `ũ_n α - ṽ_n = ũ_n (α - r_n)`
  have key : ∀ n, 1 ≤ n → 0 < u n ∧ (u n : ℝ) = (Zv n 0 : ℝ) / Gdiv n ∧
      (u n : ℝ) * alpha A B - v n = u n * (alpha A B - approx n A B) := by
    intro n hn
    have h0 := hz n hn 0
    have h1 := hz n hn 1
    have h2 := hz n hn 2
    have hS := (Z_integral n hn).2.2.2
    simp only [Zv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    have hu : u n = z n hn 0 := by simp [u, hn]
    have hv : v n = A * z n hn 1 + B * z n hn 2 := by simp [v, hn]
    have hz0 : (z n hn 0 : ℚ) = 6 * D n ^ 4 * S0 n / Gdiv n := by
      rw [h0]; field_simp [(hG n).ne']
    have hz0pos : (0 : ℚ) < z n hn 0 := by
      rw [hz0]; have := hD n; have := hG n; positivity
    refine ⟨by rw [hu]; exact_mod_cast hz0pos, ?_, ?_⟩
    · rw [hu]; simp only [Zv, Matrix.cons_val_zero]; exact_mod_cast hz0
    · have happrox : (approx n A B : ℚ) = (A * z n hn 1 + B * z n hn 2) / z n hn 0 := by
        rw [approx, hz0]
        have e1 : (z n hn 1 : ℚ) = 6 * D n ^ 4 * S3 n / Gdiv n := by
          rw [h1]; field_simp [(hG n).ne']
        have e2 : (z n hn 2 : ℚ) = 6 * D n ^ 4 * S4 n / Gdiv n := by
          rw [h2]; field_simp [(hG n).ne']
        rw [e1, e2]
        have := (hD n).ne'; have := (hG n).ne'
        field_simp
      have hcast : ((approx n A B : ℚ) : ℝ) =
          ((A : ℝ) * z n hn 1 + B * z n hn 2) / z n hn 0 := by
        rw [happrox]; push_cast; rfl
      rw [hcast, hu, hv]
      have : (z n hn 0 : ℝ) ≠ 0 := by exact_mod_cast hz0pos.ne'
      push_cast
      field_simp
  apply integer_obstruction (alpha A B) u v
  · -- `|ũ_n α - ṽ_n| ≤ (e^{112.5} ε)^n → 0`
    obtain ⟨-, -, -, -, hε⟩ := spectral_certificate.choose_spec
    have hq : exp 112.5 * (102 / 10 ^ 51) < 1 := by
      calc exp 112.5 * (102 / 10 ^ 51) < exp 112.5 * exp (-112.8) :=
            mul_lt_mul_of_pos_left hε (exp_pos _)
        _ = exp (-0.3) := by rw [← exp_add]; norm_num
        _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hlim : Tendsto (fun n : ℕ => (exp 112.5 * (102 / 10 ^ 51 : ℝ)) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [error_bound A B, height_bound, eventually_ge_atTop 1] with n herr hh hn
    obtain ⟨hpos, hu, he⟩ := key n hn
    rw [Real.norm_eq_abs, he, abs_mul, mul_pow, abs_of_pos (by exact_mod_cast hpos : (0:ℝ) < u n),
      ← exp_nat_mul, show (n : ℝ) * 112.5 = 112.5 * n by ring]
    exact mul_le_mul (hu ▸ hh) herr (abs_nonneg _) (exp_pos _).le
  · refine (nonvanishing A B hAB).mp ?_
    filter_upwards [eventually_ge_atTop 1] with n hn hne
    obtain ⟨hpos, -, he⟩ := key n hn
    rw [he]
    exact mul_ne_zero (by exact_mod_cast hpos.ne') (sub_ne_zero.mpr hne)

/-- **Main theorem** (Theorem `conditional-completion`; conditional on `modal_basis` through
`error_bound`). The numbers `1, ζ(3), ζ(4)` are linearly independent over `ℚ`, and for every
fixed `(A, B) ∈ ℤ² \ {0}` the reduced approximants satisfy `δ_n(A,B) ≥ 112.8/112.5 - 1 = 1/375`
for all large `n` (in particular `liminf δ_n(A,B) ≥ 1/375 > 0`).
* From the manuscript: yes (given the other nodes). -/
theorem main_theorem :
    LinearIndependent ℚ ![(1 : ℝ), ζ3, ζ4] ∧
      ∀ A B : ℤ, (A, B) ≠ (0, 0) → ∀ᶠ n : ℕ in atTop, (1 : ℝ) / 375 ≤ delta n A B := by
  constructor
  · rw [← LinearIndependent.iff_fractionRing (R := ℤ), Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zsmul_eq_mul, mul_one] at hg
    have h12 : g 1 = 0 ∧ g 2 = 0 := by
      by_contra hne
      have hAB : (g 1, g 2) ≠ (0, 0) := fun h => hne ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      apply irrational_combination (g 1) (g 2) hAB
      exact ⟨(-g 0 : ℤ), by rw [alpha]; push_cast; linarith⟩
    have h0 : g 0 = 0 := by
      rw [h12.1, h12.2] at hg; simpa using hg
    intro i
    fin_cases i
    exacts [h0, h12.1, h12.2]
  · intro A B hAB
    have hirr := irrational_combination A B hAB
    set α := alpha A B
    -- distance from `α` to the integers
    have hc : 0 < |α - round α| := abs_pos.mpr (sub_ne_zero.mpr fun h =>
      hirr.ne_int (round α) h)
    obtain ⟨-, -, -, -, hε⟩ := spectral_certificate.choose_spec
    have hε0 : (0 : ℝ) < 102 / 10 ^ 51 := by norm_num
    have hlog : Real.log (102 / 10 ^ 51) < -112.8 := by
      rw [Real.log_lt_iff_lt_exp hε0]; exact hε
    have hsmall : ∀ᶠ n : ℕ in atTop, (102 / 10 ^ 51 : ℝ) ^ n < |α - round α| :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hε0.le (by norm_num)).eventually
        (gt_mem_nhds hc)
    choose z hz using fun n (hn : 1 ≤ n) (i : Fin 3) => G_dvd_Z n hn i
    filter_upwards [error_bound A B, height_bound, hsmall, eventually_ge_atTop 1]
      with n herr hh hsm hn
    set x := approx n A B with hx
    -- the error is nonzero and at most `e^{-112.8 n}`
    have herr0 : 0 < |α - x| := abs_pos.mpr (sub_ne_zero.mpr fun h => hirr ⟨x, h.symm⟩)
    have hlogerr : Real.log |α - x| ≤ -112.8 * n := by
      calc Real.log |α - x| ≤ Real.log ((102 / 10 ^ 51 : ℝ) ^ n) :=
            Real.log_le_log herr0 herr
        _ = n * Real.log (102 / 10 ^ 51) := Real.log_pow _ _
        _ ≤ n * (-112.8) := mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg _)
        _ = -112.8 * n := by ring
    -- the reduced denominator satisfies `2 ≤ q_n ≤ ũ_n ≤ e^{112.5 n}`
    have hden2 : 2 ≤ x.den := by
      by_contra h
      have h1 : x.den = 1 := by have := x.den_pos; omega
      have hxint : ((x : ℚ) : ℝ) = ((x.num : ℤ) : ℝ) := by
        rw [← Rat.coe_int_num_of_den_eq_one h1]; push_cast; rfl
      have := round_le α x.num
      rw [← hxint] at this
      linarith
    have hS := (Z_integral n hn).2.2.2
    have h0 := hz n hn 0
    have h1 := hz n hn 1
    have h2 := hz n hn 2
    simp only [Zv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    have hDpos : (0 : ℚ) < D n := by
      have : 0 < D n := Nat.pos_of_ne_zero (by
        simp only [D, ne_eq, Finset.lcm_eq_zero_iff, Finset.mem_Icc, id_eq]
        omega)
      exact_mod_cast this
    have hGpos : (0 : ℚ) < Gdiv n := by
      have : 0 < Gdiv n := by
        unfold Gdiv
        exact Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp hp).2.1.pos _
      exact_mod_cast this
    have hz0 : (z n hn 0 : ℚ) = 6 * D n ^ 4 * S0 n / Gdiv n := by
      rw [h0]; field_simp [hGpos.ne']
    have hz0pos : (0 : ℚ) < z n hn 0 := by rw [hz0]; positivity
    have hxeq : x = ((A * z n hn 1 + B * z n hn 2 : ℤ) : ℚ) / (z n hn 0 : ℤ) := by
      rw [hx, approx, hz0]
      have e1 : (z n hn 1 : ℚ) = 6 * D n ^ 4 * S3 n / Gdiv n := by
        rw [h1]; field_simp [hGpos.ne']
      have e2 : (z n hn 2 : ℚ) = 6 * D n ^ 4 * S4 n / Gdiv n := by
        rw [h2]; field_simp [hGpos.ne']
      push_cast
      rw [e1, e2]
      have := hDpos.ne'; have := hGpos.ne'
      field_simp
    have hdenle : (x.den : ℝ) ≤ (Zv n 0 : ℝ) / Gdiv n := by
      have hdvd : (x.den : ℤ) ∣ z n hn 0 := by
        rw [hxeq, Rat.intCast_div_eq_divInt]; exact Rat.den_dvd _ _
      have hle : (x.den : ℤ) ≤ z n hn 0 :=
        Int.le_of_dvd (by exact_mod_cast hz0pos) hdvd
      have : (x.den : ℚ) ≤ z n hn 0 := by exact_mod_cast hle
      rw [hz0] at this
      simp only [Zv, Matrix.cons_val_zero]
      exact_mod_cast this
    have hlogden_pos : 0 < Real.log x.den :=
      Real.log_pos (by exact_mod_cast (show 1 < x.den by omega))
    have hlogden : Real.log x.den ≤ 112.5 * n := by
      rw [← Real.log_exp (112.5 * n)]
      exact Real.log_le_log (by exact_mod_cast x.den_pos) (hdenle.trans hh)
    -- conclude: `δ_n ≥ -1 + 112.8 n / log q_n ≥ -1 + 112.8/112.5 = 1/375`
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have key : 112.8 / 112.5 ≤ -Real.log |α - x| / Real.log x.den := by
      rw [le_div_iff₀ hlogden_pos]
      calc 112.8 / 112.5 * Real.log x.den ≤ 112.8 / 112.5 * (112.5 * n) :=
            mul_le_mul_of_nonneg_left hlogden (by norm_num)
        _ = 112.8 * n := by ring
        _ ≤ -Real.log |α - x| := by linarith
    simp only [delta]
    rw [← hx, neg_div] at *
    have : -1 - Real.log |α - x| / Real.log x.den = -1 + -Real.log |α - x| / Real.log x.den := by
      ring
    rw [this]
    linarith [show (1 : ℝ) / 375 = -1 + 112.8 / 112.5 by norm_num]
end Pfq54
