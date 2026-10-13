/-
# Auxiliary lemmas for `modal_basis.lean` (sorry-free)

A rational function with a finite limit along the integers has the expansion
`L + a/n + O(1/n²)`.
-/
import Mathlib

open Filter Topology Polynomial

noncomputable section

namespace Pfq54.MB

/-- `E/R → 0` along the integers forces `deg E < deg R`. -/
theorem deg_lt_of_tendsto (E R : ℝ[X]) (hR : R ≠ 0)
    (h : Tendsto (fun n : ℕ => E.eval (n : ℝ) / R.eval (n : ℝ)) atTop (𝓝 0)) :
    E.degree < R.degree := by
  by_contra hd
  rw [not_lt] at hd
  rcases hd.lt_or_eq with hlt | heq
  · have h2 := (Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt E R hlt hR).comp
      tendsto_natCast_atTop_atTop
    have h3 := (continuous_abs.tendsto 0).comp h
    rw [abs_zero] at h3
    exact not_tendsto_nhds_of_tendsto_atTop h2 0 h3
  · have h2 := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq E R heq.symm).comp
      tendsto_natCast_atTop_atTop
    have h3 := tendsto_nhds_unique h h2
    have hE : E ≠ 0 := fun hE => by
      rw [hE, degree_zero] at heq
      exact hR (degree_eq_bot.mp heq)
    exact div_ne_zero (leadingCoeff_ne_zero.mpr hE) (leadingCoeff_ne_zero.mpr hR) h3.symm

/-- `P/R = L + a/n + O(1/n²)` along the integers. -/
theorem rat_expansion (P R : ℝ[X]) (hR : R ≠ 0) (L : ℝ)
    (hlim : Tendsto (fun n : ℕ => P.eval (n : ℝ) / R.eval (n : ℝ)) atTop (𝓝 L)) :
    ∃ a K : ℝ, ∀ᶠ n : ℕ in atTop,
      |P.eval (n : ℝ) / R.eval (n : ℝ) - L - a / n| ≤ K / (n : ℝ) ^ 2 := by
  set E := P - C L * R with hEdef
  have hroot := tendsto_natCast_atTop_atTop.eventually (Polynomial.eventually_atTop_not_isRoot R hR)
  have hE : Tendsto (fun n : ℕ => E.eval (n : ℝ) / R.eval (n : ℝ)) atTop (𝓝 0) := by
    have h := hlim.sub_const L
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [hroot] with n hn
    rw [hEdef, eval_sub, eval_mul, eval_C, sub_div, mul_div_assoc, div_self hn, mul_one]
  have hdeg := deg_lt_of_tendsto E R hR hE
  have hEc : ∀ k : ℕ, R.natDegree ≤ k → E.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg
      ((degree_eq_natDegree hR).trans_le (WithBot.coe_le_coe.mpr hk)))
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  set d := R.natDegree
  set a := E.coeff (d - 1) / R.leadingCoeff
  set F := X * E - C a * R
  have hFdeg : (X * F).degree ≤ R.degree := by
    rw [degree_eq_natDegree hR, degree_le_iff_coeff_zero]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by
      have : d < m := WithBot.coe_lt_coe.mp hm
      omega⟩
    have hk : d ≤ k := by
      have : d < k + 1 := WithBot.coe_lt_coe.mp hm
      omega
    rw [coeff_X_mul, coeff_sub, coeff_C_mul]
    rcases hk.lt_or_eq with hk | rfl
    · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
      rw [coeff_X_mul, hEc l (by omega), coeff_eq_zero_of_natDegree_lt hk, mul_zero, sub_zero]
    · rcases Nat.eq_zero_or_pos d with hd | hd
      · rw [hd, coeff_X_mul_zero, show a = 0 by
          rw [show a = E.coeff (d - 1) / R.leadingCoeff from rfl, hEc _ (by omega), zero_div],
          zero_mul, sub_zero]
      · obtain ⟨l, hl⟩ : ∃ l, d = l + 1 := ⟨d - 1, by omega⟩
        rw [hl, coeff_X_mul, ← hl, show R.coeff d = R.leadingCoeff from rfl, show a = E.coeff l / R.leadingCoeff by
            rw [show a = E.coeff (d - 1) / R.leadingCoeff from rfl, show d - 1 = l by omega],
          div_mul_cancel₀ _ hlc, sub_self]
  obtain ⟨K, hK⟩ := (Polynomial.isBigO_atTop_of_degree_le _ _ hFdeg).bound
  refine ⟨a, K, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hK, hroot, eventually_ge_atTop 1]
    with n h1 h2 hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hR0 : R.eval (n : ℝ) ≠ 0 := h2
  have hid : P.eval (n : ℝ) / R.eval (n : ℝ) - L - a / n =
      (X * F).eval (n : ℝ) / ((n : ℝ) ^ 2 * R.eval (n : ℝ)) := by
    rw [eval_mul, eval_X, eval_sub, eval_mul, eval_X, eval_mul, eval_C, hEdef, eval_sub, eval_mul,
      eval_C]
    field_simp
  rw [hid, abs_div, abs_mul, abs_pow, Nat.abs_cast, div_le_div_iff₀
    (mul_pos (pow_pos (by positivity) 2) (abs_pos.mpr hR0)) (pow_pos (by positivity) 2)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1
  nlinarith [sq_nonneg (n : ℝ)]

end Pfq54.MB
