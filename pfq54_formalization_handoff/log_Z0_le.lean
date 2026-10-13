/-
# Blueprint of `log_Z0_le` (manuscript Appendix G, "The reduced-denominator bound")

Node `Pfq54.log_Z0_le` of `Blueprint_pfq54.lean`: for every `ε > 0`,
`log Z_{0,n} = log(6 D_n⁴ S_{0,n}) ≤ (65.46 + 76 + ε) n` for all large `n`.

Proof: `log D_n = ψ(19n)` ([1]) and `ψ(x) ≤ (1 + ε) x` eventually (prime number theorem plus
`ψ - θ = O(√x)`, [2]), so `4 log D_n ≤ 76 n + o(n)`. Uniform Stirling bounds ([3]) applied to the
factorial formula of `U_{n,j} = C_n |a_j|` give `log U_{n,j} ≤ n (30 log(3/2) + g(j/n)) + O(log n)`
([4]); the concave function `g` satisfies `30 log(3/2) + g < 65.46` on `[2, 16]` ([5]); summing
over at most `14n + 1` indices gives `log S_{0,n} ≤ (65.46 + ε) n` ([6]).

Reused from the previous proof: `ZetasIrr.BP.pnt_bounds` (`blueprints/log_Delta_le.lean`) and
`ZetasIrr.BP.fact_bounds` (`blueprints/growth_estimates.lean`).
-/
import Z_integral
import log_Delta_le
import growth_estimates
import log_Z0_aux
import stirling_aux

open Finset Filter Topology

noncomputable section

namespace Pfq54.BP

open Pfq54
open Pfq54.LZ (gpfun gfun_deriv gpfun_antitone g12_numeric)

/-- `f(x) = x log x` (with `f(0) = 0`, as `Real.log 0 = 0`). -/
def xlogx (x : ℝ) : ℝ := x * Real.log x

/-- The Stirling exponent of `a_j` at `j = y n`:
`g(y) = ∑_{a=10}^{12} f(y+a) - f(y) - f(y+1) - f(y+2) - f(y-1) - f(y-2) - f(16-y) - f(17-y)`. -/
def gfun (y : ℝ) : ℝ :=
  xlogx (y + 10) + xlogx (y + 11) + xlogx (y + 12) - xlogx y - xlogx (y + 1) - xlogx (y + 2) -
    xlogx (y - 1) - xlogx (y - 2) - xlogx (16 - y) - xlogx (17 - y)

/-- **[1] `log D_n = ψ(19n)`** (`log lcm(1,…,m) = ψ(m)`).
* Proof length: 3 lines. Proved below (Mathlib `Chebyshev.psi_eq_log_lcmUpto`).
* Directly from the manuscript: yes. -/
theorem log_D_eq_psi (n : ℕ) : Real.log (D n : ℝ) = Chebyshev.psi (19 * (n : ℝ)) := by
  rw [show (19 * (n : ℝ)) = ((19 * n : ℕ) : ℝ) by push_cast; ring,
    Chebyshev.psi_eq_log_lcmUpto]
  rfl

/-- **[2] Upper bound for `ψ`**: `ψ(x) ≤ (1 + ε) x` for all large `x`.
* Proof length: 20 lines. Proved below from `ZetasIrr.BP.pnt_bounds` (`blueprints/log_Delta_le.lean`, prime number
  theorem) and Mathlib's `Chebyshev.psi_sub_theta_le_mul_sqrt`.
* Directly from the manuscript: partially ("`log d_{19n} = 19n + o(n)`" is quoted). -/
theorem psi_le_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + ε) * x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨X₀, hX1, hX⟩ := ZetasIrr.BP.pnt_bounds (half_pos hε)
  filter_upwards [eventually_ge_atTop X₀, eventually_ge_atTop ((2 * |C| / ε) ^ 2)]
    with x hx hx2
  have hx0 : 0 ≤ x := by linarith
  have hθ := (hX x hx).2
  have hs : 2 * |C| / ε ≤ Real.sqrt x := by
    have := Real.sqrt_le_sqrt hx2
    rwa [Real.sqrt_sq (by positivity)] at this
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hsq := Real.sqrt_nonneg x
  have hCs : |C| ≤ ε / 2 * Real.sqrt x := by
    rw [div_le_iff₀ hε] at hs; linarith
  have h1 : C * Real.sqrt x ≤ |C| * Real.sqrt x :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hsq
  have h2 : |C| * Real.sqrt x ≤ ε / 2 * x :=
    calc |C| * Real.sqrt x ≤ ε / 2 * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hCs hsq
      _ = ε / 2 * x := by rw [mul_assoc, hsx]
  linarith [hC x]

/-- **[3] Two-sided Stirling bounds** for `m ≥ 1`:
`m log m - m ≤ log m! ≤ m log m - m + 1 + (log m)/2`.
* Proof length: 2 lines. Proved below from `ZetasIrr.BP.fact_bounds` (`blueprints/growth_estimates.lean`).
* Directly from the manuscript: yes ("uniform Stirling bounds"). -/
theorem log_factorial_bounds (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m ≤ Real.log m.factorial ∧
      Real.log m.factorial ≤ m * Real.log m - m + 1 + Real.log m / 2 := by
  have h := ZetasIrr.BP.fact_bounds 1 m le_rfl hm
  simpa using h

/-- **[4] Uniform termwise Stirling bound**: there is `C` with
`log U_{n,j} ≤ n (30 log(3/2) + g(j/n)) + C log(n+1)` for `n ≥ 1`, `2n ≤ j ≤ 16n`, `U_{n,j} > 0`
(all `n log n` and linear Stirling terms cancel; the error is `O(log n)` uniformly, also at
factorial argument `0`).
* Uses: [3], `U_two_n_add` (`hyp_readout.lean`).
* Estimated proof length: ≈ 80 lines.
* Directly from the manuscript: partially (the cancellation is asserted, not displayed). -/
theorem term_stirling : ∃ C : ℝ, ∀ n j : ℕ, 1 ≤ n → 2 * n ≤ j → j ≤ 16 * n → 0 < U n j →
    Real.log (U n j : ℝ) ≤
      n * (30 * Real.log (3 / 2) + gfun ((j : ℝ) / n)) + C * Real.log (n + 1) := by
  exact ST.term_stirling'

/-- **[5] The concavity/rational-logarithm certificate**:
`30 log(3/2) + g(y) < 65.46` on `[2, 16]` (`g'' < 0`; the maximum lies in `[12.014, 12.015]`;
`max g ≤ g(y₀) + (b-a)/2 |g'(y₀)|`; log-series bounds with `M = 35`).
* Estimated proof length: ≈ 100 lines.
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem g_bound : ∀ y ∈ Set.Icc (2 : ℝ) 16, 30 * Real.log (3 / 2) + gfun y < 65.46 := by
  intro y hy
  have hc : Continuous xlogx := Real.continuous_mul_log
  have hcont : ContinuousOn gfun (Set.Icc 2 16) := by
    unfold gfun; fun_prop
  have h12 : (12 : ℝ) ∈ Set.Ioo 2 16 := ⟨by norm_num, by norm_num⟩
  have h12' : (12.015 : ℝ) ∈ Set.Ioo 2 16 := ⟨by norm_num, by norm_num⟩
  have hgp12 : gpfun 12 = Real.log (92 / 91) := by
    unfold gpfun
    rw [Aux.log_ratio5 _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have hgp0 : 0 ≤ gpfun 12 := by rw [hgp12]; exact Real.log_nonneg (by norm_num)
  have hgp1 : gpfun 12 ≤ 1 / 91 := by
    rw [hgp12]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 92 / 91 by norm_num)
    linarith
  have hgpn : gpfun 12.015 < 0 := by
    unfold gpfun
    rw [Aux.log_ratio5 _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    exact Real.log_neg (by norm_num) (by norm_num)
  have hnum : 30 * Real.log (3 / 2) + gfun 12 + 1 / 91 * (3 / 200) < 65.46 := g12_numeric
  have t1 := Aux.tangent_le gfun gpfun hcont gfun_deriv gpfun_antitone h12 hy
  rcases le_or_gt y 12.015 with hy' | hy'
  · have : gpfun 12 * (y - 12) ≤ 1 / 91 * (3 / 200) := by
      rcases le_or_gt y 12 with h | h
      · exact (mul_nonpos_iff.mpr (Or.inl ⟨hgp0, by linarith⟩)).trans (by norm_num)
      · exact mul_le_mul hgp1 (by linarith) (by linarith) (by norm_num)
    linarith
  · have t2 := Aux.tangent_le gfun gpfun hcont gfun_deriv gpfun_antitone h12' hy
    have t3 := Aux.tangent_le gfun gpfun hcont gfun_deriv gpfun_antitone h12
      (Set.Ioo_subset_Icc_self h12')
    have : gpfun 12.015 * (y - 12.015) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hgpn.le, by linarith⟩)
    have : gpfun 12 * (12.015 - 12) ≤ 1 / 91 * (3 / 200) := by
      rw [show (12.015 : ℝ) - 12 = 3 / 200 by norm_num]
      exact mul_le_mul_of_nonneg_right hgp1 (by norm_num)
    linarith

/-- **[6] Growth of the denominator readout**: `log S_{0,n} ≤ (65.46 + ε) n` eventually
(`U_{n,j} = 0` outside `[2n, 16n]`; `S_{0,n} ≤ (14n+1) max_j U_{n,j}`).
* Uses: [4], [5], `U_eq_zero_outside` (`hyp_readout.lean`), `U_nonneg` (`Z_integral.lean`).
* Estimated proof length: ≈ 40 lines.
* Directly from the manuscript: yes. -/
theorem log_S0_le : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (S0 n : ℝ) ≤ (65.46 + ε) * n := by
  intro ε hε
  obtain ⟨C, hC⟩ := term_stirling
  set C' := |C|
  have hC' : 0 ≤ C' := abs_nonneg C
  have hδ : 0 < ε / (2 * (1 + C')) := by positivity
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def hδ
  have hK : ∀ᶠ n : ℕ in atTop, Real.log 18 + C' * Real.log 2 ≤ ε / 2 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2 * (Real.log 18 + C' * Real.log 2) / ε)] with n hn
    rw [div_le_iff₀ hε] at hn
    linarith
  filter_upwards [hlog, hK, eventually_ge_atTop 1] with n h1 hKn hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : Real.log n ≤ ε / (2 * (1 + C')) * n := by
    have := h1
    simp only [Function.comp_apply, id_eq] at this
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (Nat.cast_nonneg n)] at this
  have hl1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  set M := Real.exp (65.46 * n + C' * Real.log ((n : ℝ) + 1))
  have hU : ∀ j ∈ range (17 * n + 1), (U n j : ℝ) ≤ M := by
    intro j _
    rcases (U_nonneg n j).lt_or_eq with hpos | hzero
    · have hj2 : 2 * n ≤ j ∧ j ≤ 16 * n := by
        by_contra hcon
        exact hpos.ne' (U_eq_zero_outside n j (by omega))
      have hposR : (0 : ℝ) < U n j := by exact_mod_cast hpos
      have hst := hC n j hn hj2.1 hj2.2 hpos
      have hjn1 : (2 : ℝ) ≤ (j : ℝ) / n := by
        rw [le_div_iff₀ hn0]; exact_mod_cast hj2.1
      have hjn2 : (j : ℝ) / n ≤ 16 := by
        rw [div_le_iff₀ hn0]; exact_mod_cast hj2.2
      have hg := g_bound ((j : ℝ) / n) ⟨hjn1, hjn2⟩
      have e1 : (n : ℝ) * (30 * Real.log (3 / 2) + gfun ((j : ℝ) / n)) ≤ n * 65.46 :=
        mul_le_mul_of_nonneg_left hg.le hn0.le
      have e2 : C * Real.log ((n : ℝ) + 1) ≤ C' * Real.log ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hl1
      rw [← Real.exp_log hposR]
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [← hzero, Rat.cast_zero]; exact (Real.exp_pos _).le
  have hS : (S0 n : ℝ) ≤ (17 * n + 1) * M := by
    unfold S0
    push_cast
    calc ∑ j ∈ range (17 * n + 1), (U n j : ℝ) ≤ ∑ j ∈ range (17 * n + 1), M :=
          Finset.sum_le_sum hU
      _ = (17 * n + 1) * M := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hS0 : (0 : ℝ) < S0 n := by exact_mod_cast (Z_integral n hn).2.2.2
  have h17 : Real.log (17 * n + 1) ≤ Real.log 18 + Real.log n := by
    rw [← Real.log_mul (by norm_num) hn0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) hn0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have h3 : C' * Real.log ((n : ℝ) + 1) ≤ C' * Real.log 2 + C' * Real.log n := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left h2 hC'
  have h4 : (1 + C') * Real.log n ≤ ε / 2 * n := by
    calc (1 + C') * Real.log n ≤ (1 + C') * (ε / (2 * (1 + C')) * n) :=
          mul_le_mul_of_nonneg_left hlogn (by positivity)
      _ = ε / 2 * n := by field_simp
  calc Real.log (S0 n : ℝ) ≤ Real.log ((17 * n + 1) * M) := Real.log_le_log hS0 hS
    _ = Real.log (17 * n + 1) + (65.46 * n + C' * Real.log ((n : ℝ) + 1)) := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ (65.46 + ε) * n := by linarith

/-- **`log_Z0_le`** (node of `Blueprint_pfq54.lean`). Proved from [1], [2], [6] and
`Z_integral`: `log Z_{0,n} = log 6 + 4 ψ(19n) + log S_{0,n}`. -/
theorem log_Z0_le : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    Real.log (Zv n 0 : ℝ) ≤ (65.46 + 76 + ε) * n := by
  intro ε hε
  have hψ : ∀ᶠ n : ℕ in atTop, Chebyshev.psi (19 * (n : ℝ)) ≤ (1 + ε / 304) * (19 * n) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 19)).eventually
      (psi_le_eventually (ε / 304) (by positivity))
  have h6 : ∀ᶠ n : ℕ in atTop, Real.log 6 ≤ ε / 2 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2 * Real.log 6 / ε)] with n hn
    rw [div_le_iff₀ hε] at hn
    linarith
  filter_upwards [hψ, h6, log_S0_le (ε / 4) (by positivity), eventually_ge_atTop 1]
    with n hψn h6n hS hn
  have hS0 : (0 : ℝ) < S0 n := by exact_mod_cast (Z_integral n hn).2.2.2
  have hD : (0 : ℝ) < D n := by
    have : 0 < D n := Nat.pos_of_ne_zero (by
      simp only [D, ne_eq, Finset.lcm_eq_zero_iff, Finset.mem_Icc, id_eq]
      omega)
    exact_mod_cast this
  have hZ : ((Zv n 0 : ℚ) : ℝ) = 6 * (D n : ℝ) ^ 4 * (S0 n : ℝ) := by simp [Zv]
  rw [hZ, Real.log_mul (mul_pos (by norm_num) (pow_pos hD 4)).ne' hS0.ne',
    Real.log_mul (by norm_num) (pow_pos hD 4).ne', Real.log_pow, log_D_eq_psi]
  push_cast
  linarith

end Pfq54.BP
