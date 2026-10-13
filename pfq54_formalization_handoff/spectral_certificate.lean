/-
# Blueprint of `spectral_certificate` (manuscript Appendix A, "Exact spectral data")

Node `Pfq54.spectral_certificate` of `Blueprint_pfq54.lean`: the restricted characteristic
polynomial `χ(X) = X³ - aX² + bX - c` has a real root `0 < r < u = 7203/10²⁷`, every other
complex root `z` satisfies `r < ε |z|` with `ε = 102/10⁵¹` (i.e. `ϑ = |ρ₄|/|ρ₁| < ε`), and
`ε < e^{-112.8}`.

Proof: `c > 0`, `χ(0) = -c < 0 < χ(u)` ([2], [3]) and the intermediate value theorem give the
real root `r ∈ (0, u)` ([6]). The discriminant is negative ([5]), so the two other roots are a
conjugate pair `z, z̄` with `|z|² r = c` ([7]). Hence `ϑ² = r²/|z|² = r³/c < u³/c < ε²` ([4]).
Finally `ε < e^{-112.8}` by dyadic reduction and rational log-series bounds ([8]).
-/
import Pfq54_defs

open Real

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- **[1] Evaluating `χ`** over `ℝ` and over `ℂ`.
* Estimated proof length: ≈ 6 lines (`simp [chi, Polynomial.eval_map]`).
* Directly from the manuscript: yes. -/
theorem chi_eval :
    (∀ x : ℝ, (chi.map (algebraMap ℚ ℝ)).eval x =
        x ^ 3 - (chiA : ℝ) * x ^ 2 + (chiB : ℝ) * x - (chiC : ℝ)) ∧
      ∀ z : ℂ, (chi.map (algebraMap ℚ ℂ)).eval z =
        z ^ 3 - ((chiA : ℝ) : ℂ) * z ^ 2 + ((chiB : ℝ) : ℂ) * z - ((chiC : ℝ) : ℂ) := by
  refine ⟨fun x => ?_, fun z => ?_⟩ <;> simp [chi]

/-- **[2]** `c > 0`, i.e. `χ(0) < 0`.
* Estimated proof length: ≈ 2 lines (`norm_num [chiC]`).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem chiC_pos : (0 : ℝ) < chiC := by
  have h : (0 : ℚ) < chiC := by unfold chiC; norm_num
  exact_mod_cast h

/-- **[3]** `χ(u) > 0` for `u = 7203/10²⁷`.
* Estimated proof length: ≈ 3 lines (`norm_num [chiA, chiB, chiC]`).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem chi_u_pos :
    (0 : ℝ) < (7203 / 10 ^ 27) ^ 3 - (chiA : ℝ) * (7203 / 10 ^ 27) ^ 2 +
      (chiB : ℝ) * (7203 / 10 ^ 27) - (chiC : ℝ) := by
  unfold chiA chiB chiC
  push_cast
  norm_num

/-- **[4]** `u³ < c ε²`.
* Estimated proof length: ≈ 2 lines (`norm_num [chiC]`).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem u_cube_lt : ((7203 / 10 ^ 27 : ℝ)) ^ 3 < (chiC : ℝ) * (102 / 10 ^ 51) ^ 2 := by
  unfold chiC
  push_cast
  norm_num

/-- **[5]** The discriminant of `χ` is negative.
* Estimated proof length: ≈ 3 lines (`norm_num [chiA, chiB, chiC]`).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem disc_neg :
    18 * (chiA : ℝ) * chiB * chiC - 4 * (chiA : ℝ) ^ 3 * chiC + (chiA : ℝ) ^ 2 * chiB ^ 2 -
      4 * (chiB : ℝ) ^ 3 - 27 * (chiC : ℝ) ^ 2 < 0 := by
  have h : 18 * chiA * chiB * chiC - 4 * chiA ^ 3 * chiC + chiA ^ 2 * chiB ^ 2 -
      4 * chiB ^ 3 - 27 * chiC ^ 2 < 0 := by
    unfold chiA chiB chiC; norm_num
  exact_mod_cast h

/-- **[6] The small real root** `ρ₄ = r ∈ (0, u)` (intermediate value theorem).
* Uses: [2], [3].
* Estimated proof length: ≈ 15 lines (`intermediate_value_Ioo`, continuity of a polynomial).
* Directly from the manuscript: yes. -/
theorem ivt_root : ∃ r : ℝ, 0 < r ∧ r < 7203 / 10 ^ 27 ∧
    r ^ 3 - (chiA : ℝ) * r ^ 2 + (chiB : ℝ) * r - (chiC : ℝ) = 0 := by
  have hc := chiC_pos
  have hu := chi_u_pos
  have hcont : ContinuousOn (fun r : ℝ => r ^ 3 - (chiA : ℝ) * r ^ 2 + (chiB : ℝ) * r - (chiC : ℝ))
      (Set.Icc 0 (7203 / 10 ^ 27)) := by fun_prop
  obtain ⟨r, ⟨hr0, hru⟩, hr⟩ := intermediate_value_Ioo (by norm_num) hcont
    (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨by norm_num [hc], hu⟩)
  exact ⟨r, hr0, hru, hr⟩

/-- **[7] The conjugate pair.** For a real monic cubic `X³ - aX² + bX - c` with negative
discriminant, real root `r` and another complex root `z`: `|z|² r = c` (the other roots are
`z, z̄`, and `r z z̄ = c`).
* Estimated proof length: ≈ 60 lines (factor `X - r`; the quadratic cofactor has negative
  discriminant, so its roots are non-real conjugates; Vieta).
* Directly from the manuscript: yes ("Their common modulus is `√(c/r)`"). -/
theorem cubic_conj_modulus (a b c : ℝ)
    (hdisc : 18 * a * b * c - 4 * a ^ 3 * c + a ^ 2 * b ^ 2 - 4 * b ^ 3 - 27 * c ^ 2 < 0)
    (r : ℝ) (hr : r ^ 3 - a * r ^ 2 + b * r - c = 0) (z : ℂ)
    (hz : z ^ 3 - (a : ℂ) * z ^ 2 + (b : ℂ) * z - (c : ℂ) = 0) (hzr : z ≠ r) :
    ‖z‖ ^ 2 * r = c := by
  have hc : c = r ^ 3 - a * r ^ 2 + b * r := by linarith
  subst hc
  set p := r - a with hp
  set q := b + (r - a) * r with hq
  have hid : 18 * a * b * (r ^ 3 - a * r ^ 2 + b * r) - 4 * a ^ 3 * (r ^ 3 - a * r ^ 2 + b * r) +
      a ^ 2 * b ^ 2 - 4 * b ^ 3 - 27 * (r ^ 3 - a * r ^ 2 + b * r) ^ 2 =
      (p ^ 2 - 4 * q) * (r ^ 2 + p * r + q) ^ 2 := by
    rw [hp, hq]; ring
  have hneg : p ^ 2 - 4 * q < 0 := by nlinarith [sq_nonneg (r ^ 2 + p * r + q)]
  have hquad : z ^ 2 + (p : ℂ) * z + (q : ℂ) = 0 := by
    have hfac : z ^ 3 - (a : ℂ) * z ^ 2 + (b : ℂ) * z - ((r ^ 3 - a * r ^ 2 + b * r : ℝ) : ℂ) =
        (z - r) * (z ^ 2 + (p : ℂ) * z + (q : ℂ)) := by
      rw [hp, hq]; push_cast; ring
    rw [hfac] at hz
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hzr)
  have hre := congrArg Complex.re hquad
  have him := congrArg Complex.im hquad
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
  have hy : z.im ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2 * z.re + p)]
  have hx : 2 * z.re + p = 0 := by
    have : z.im * (2 * z.re + p) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hy
  have hq' : z.re ^ 2 + z.im ^ 2 = q := by linear_combination (-1) * hre + z.re * hx
  rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two, ← pow_two, hq', hq]
  ring

/-- **[8]** `ε = 102/10⁵¹ < e^{-112.8}` (dyadic reduction of `10⁵¹/102` and the rational bounds
`2 ∑_{j<M} u^{2j+1}/(2j+1) ≤ log z` with `u = (z-1)/(z+1)`, `M = 35`).
* Estimated proof length: ≈ 40 lines (compare the exponential bounds `exp_split_lower` of
  `blueprints/growth_estimates.lean`).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem eps_lt_exp : (102 / 10 ^ 51 : ℝ) < exp (-112.8) := by
  have h1 : exp (112.8 : ℝ) = exp 1 ^ 112 * exp 0.8 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 : exp 1 ^ 112 < (2.7182818286 : ℝ) ^ 112 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h3 := Real.exp_bound' (x := (0.8 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  have h4 : (2.7182818286 : ℝ) ^ 112 * ((∑ m ∈ Finset.range 12, (0.8 : ℝ) ^ m / m.factorial) +
      (0.8 : ℝ) ^ 12 * (12 + 1) / (Nat.factorial 12 * 12)) < 10 ^ 51 / 102 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [Real.exp_neg, lt_inv_comm₀ (by positivity) (Real.exp_pos _), inv_div, h1]
  calc exp 1 ^ 112 * exp 0.8 ≤ (2.7182818286 : ℝ) ^ 112 * ((∑ m ∈ Finset.range 12,
        (0.8 : ℝ) ^ m / m.factorial) + (0.8 : ℝ) ^ 12 * (12 + 1) / (Nat.factorial 12 * 12)) :=
        mul_le_mul h2.le h3 (Real.exp_pos _).le (by positivity)
    _ < _ := h4

/-- **`spectral_certificate`** (node of `Blueprint_pfq54.lean`). Proved from [1]–[8]. -/
theorem spectral_certificate :
    ∃ r : ℝ, 0 < r ∧ r < 7203 / 10 ^ 27 ∧ (chi.map (algebraMap ℚ ℝ)).eval r = 0 ∧
      (∀ z : ℂ, (chi.map (algebraMap ℚ ℂ)).eval z = 0 → z ≠ r → r < 102 / 10 ^ 51 * ‖z‖) ∧
      (102 / 10 ^ 51 : ℝ) < exp (-112.8) := by
  obtain ⟨r, hr0, hru, hroot⟩ := ivt_root
  obtain ⟨hevR, hevC⟩ := chi_eval
  refine ⟨r, hr0, hru, by rw [hevR]; exact hroot, fun z hz hzr => ?_, eps_lt_exp⟩
  rw [hevC] at hz
  have hmod := cubic_conj_modulus _ _ _ disc_neg r hroot z hz hzr
  have hr3 : r ^ 3 < (chiC : ℝ) * (102 / 10 ^ 51) ^ 2 :=
    lt_trans (pow_lt_pow_left₀ hru hr0.le (by norm_num)) u_cube_lt
  have key : r ^ 2 < (102 / 10 ^ 51 * ‖z‖) ^ 2 := by
    rw [← hmod] at hr3
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) key

end Pfq54.BP
