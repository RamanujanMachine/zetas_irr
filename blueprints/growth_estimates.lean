/-
# Blueprint for `ZetasIrr.growth_estimates`

Statement (as in `blueprint.lean`): there are `a ∈ (53.28758332262, 53.28758332263)` and
`b ∈ (59.51995592483, 59.51995592484)` such that, for every `ε > 0` and all large `N`,
`|A_{Nj}|, |B_{Nj}| ≤ e^{(b+ε)N}`, `|S_{Nj}| ≤ e^{(-a+ε)N}`, `|q_{Nj}| ≤ e^{(a+ε)N}` and
`det V_N ≥ e^{(2b-a-ε)N}`.

Source: PDF Part VII §1 (spectral rates of the limit matrix, characteristic polynomial `χ`,
`a = -log λ₀`, `b = ½ log(c₀/λ₀)`) and Part VII §6 (contour bound, cone argument,
`‖A_N‖ ≤ e^{bN+o(N)}`, `det V_N = e^{(2b-a)N+o(N)}`, `‖S_N‖ ≤ e^{-aN+o(N)}`, and
"the inverse-transpose product bound proves (11)").

Certificates: `certificates/zeta34/verify_numerical_bounds.py` (bracket of `λ₀`, intervals for
`a, b`), `certificates/zeta34/verify_matrix.py` (limit matrix and its characteristic polynomial).

The witnesses are the exact constants `aConst = -log λ₀` and `bConst = ½(log c₀ + aConst)`,
where `λ₀` is the unique real root of `χ`. The coefficients of `χ` are copied verbatim from
`verify_numerical_bounds.py`.

| # | Supporting lemma        | Est. lines | Directly from PDF? |
|---|-------------------------|-----------:|--------------------|
| 1 | `lam0_spec`             |   (proved) | Yes (with exact arithmetic) |
| 2 | `a_b_bounds`            |   (proved) | Yes (with exact arithmetic) |
| 3 | `F_lower_bound`         |   (proved) | Partially          |
| 4 | `coeff_rows_growth`     |   (proved) | Partially          |
| 5 | `S_decay`               |   (proved) | Partially          |
| 6 | `q_eq_cross`            | see `cross_product_readout.lean` | Yes |
| 7 | `det_V_eq`              | imported from `det_V_eq.lean` | No (needs the CMF) |
| 8 | `F_pos`                 | (proved, imported from `det_V_eq.lean`) | Yes |
| 9 | `abs_cross_le`          |   (proved) | Yes                |

All supporting lemmas are proved; [4] and [5] use the transport files `GW_*.lean`.

[7] and [8] are `ZetasIrr.BP.det_V_eq` and `ZetasIrr.BP.F_pos` of `det_V_eq.lean`, which is
imported. (This file used to carry an identical copy of `F_pos`; it was dropped because the two
declarations have the same name.)
-/
import ZetasAux
import det_V_eq
import GW_limit
import GW_cone
import GW_Sbound

open Polynomial Filter Topology Real

noncomputable section

namespace ZetasIrr.BP

/-- `c₂` of the characteristic polynomial `χ(X) = X³ - c₂X² + c₁X - c₀` (PDF Part VII §1). -/
def chiC2 : ℚ := 83220721427294106907399200607730930785765129529801897078934559 /
  1484577825190137274336280508756918272
/-- `c₁` of `χ`. -/
def chiC1 : ℚ :=
  731334801243107466089356596505717853275074571608716447379201100334794667003154611901941573810757 /
  146466868948884247884332915718530654652342544
/-- `c₀ = det A` of `χ`. -/
def chiC0 : ℚ :=
  76623012348334313797938377862237790794460627983667564193521662995163373351121226574589853696 /
  2130520759189220333584634002331004844478493702212809977860478179

/-- The characteristic polynomial `χ` of the limit matrix `A`, as a real function. -/
def chi (x : ℝ) : ℝ := x ^ 3 - chiC2 * x ^ 2 + chiC1 * x - chiC0

/-- `λ₀ = e^{-a}`: the unique real root of `χ` (the smallest point of the root set). -/
def lam0 : ℝ := sInf {x : ℝ | chi x = 0}

/-- `a = -log λ₀`. -/
def aConst : ℝ := -Real.log lam0

/-- `b = ½ log(c₀/λ₀) = ½(log c₀ + a)`. -/
def bConst : ℝ := (Real.log chiC0 + aConst) / 2

/-! ### The unique real root of `χ` (exact rational arithmetic) -/

/-- `c₂² < 3c₁`: the derivative `χ'(x) = 3x² - 2c₂x + c₁` has negative discriminant, so `χ` is
strictly increasing (this is how the negative discriminant of `χ` is used). -/
theorem chiC2_sq_lt : ((chiC2 : ℝ)) ^ 2 < 3 * chiC1 := by
  rw [chiC2, chiC1]; push_cast; norm_num

/-- `χ` is strictly increasing on `ℝ`:
`χ(y) - χ(x) = (y - x)(¾(x + y - 2c₂/3)² + ¼(x - y)² + (c₁ - c₂²/3))`. -/
theorem chi_strictMono : StrictMono chi := by
  intro x y hxy
  have h := chiC2_sq_lt
  have key : chi y - chi x = (y - x) * ((3 / 4) * (x + y - 2 * chiC2 / 3) ^ 2 +
      (1 / 4) * (x - y) ^ 2 + (chiC1 - chiC2 ^ 2 / 3)) := by
    unfold chi; ring
  have hpos : 0 < (3 / 4) * (x + y - 2 * chiC2 / 3) ^ 2 + (1 / 4) * (x - y) ^ 2 +
      ((chiC1 : ℝ) - chiC2 ^ 2 / 3) := by
    have h1 : 0 ≤ (3 / 4) * (x + y - 2 * chiC2 / 3) ^ 2 := by positivity
    have h2 : 0 ≤ (1 / 4) * (x - y) ^ 2 := by positivity
    linarith
  have := mul_pos (sub_pos.mpr hxy) hpos
  rw [← key] at this
  exact sub_pos.mp this

/-- Sign change at the lower end of the bracket. -/
theorem chi_lo_neg : chi (3601360636638255963141132005273498479 / 10 ^ 60 * 2) < 0 := by
  rw [chi, chiC2, chiC1, chiC0]; push_cast; norm_num

/-- Sign change at the upper end of the bracket. -/
theorem chi_hi_pos : 0 < chi (7202721273276511926282264010546996959 / 10 ^ 60) := by
  rw [chi, chiC2, chiC1, chiC0]; push_cast; norm_num

theorem chi_continuous : Continuous chi := by
  unfold chi; fun_prop

/-- **[1] The real root of `χ`.** `χ` has negative discriminant, so it has exactly one real
root. That root lies in `(7.202721273276511926282264010546996958·10⁻²⁴,
7.202721273276511926282264010546996959·10⁻²⁴)`.
* Lines: proved here (sign change at the two rational endpoints by `norm_num`; uniqueness
  from `c₂² < 3c₁`, which makes `χ` strictly increasing).
* Directly from the PDF: yes (it gives `χ`, the discriminant sign and the bracket; certificate
  `verify_numerical_bounds.py`). -/
theorem lam0_spec :
    chi lam0 = 0 ∧ (∀ x, chi x = 0 → x = lam0) ∧
      (3601360636638255963141132005273498479 / 10 ^ 60 * 2 : ℝ) < lam0 ∧
      lam0 < 7202721273276511926282264010546996959 / 10 ^ 60 := by
  have hlohi : (3601360636638255963141132005273498479 / 10 ^ 60 * 2 : ℝ) ≤
      7202721273276511926282264010546996959 / 10 ^ 60 := by norm_num
  -- existence of a root in the bracket, by the intermediate value theorem
  obtain ⟨x₀, -, hx₀⟩ := intermediate_value_Icc hlohi chi_continuous.continuousOn
    ⟨chi_lo_neg.le, chi_hi_pos.le⟩
  -- uniqueness: `χ` is strictly increasing, so the root set is `{x₀}`
  have hset : {x : ℝ | chi x = 0} = {x₀} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx; exact chi_strictMono.injective (hx.trans hx₀.symm)
    · rintro rfl; exact hx₀
  have hlam : lam0 = x₀ := by rw [lam0, hset, csInf_singleton]
  refine ⟨by rw [hlam]; exact hx₀,
    fun x hx => by rw [hlam]; exact chi_strictMono.injective (hx.trans hx₀.symm), ?_, ?_⟩
  · rw [hlam, ← chi_strictMono.lt_iff_lt, hx₀]; exact chi_lo_neg
  · rw [hlam, ← chi_strictMono.lt_iff_lt, hx₀]; exact chi_hi_pos

/-! ### Rational enclosures of `exp` (PDF Part VII §1: "The certificate bounds these
logarithms using an exact rational series with a rational remainder"). The inequalities
`a ≷ α` are rewritten as `e^{-α} ≷ λ₀` and `b ≷ β` as `e^{2β} ≷ c₀/λ₀`, and `exp` is enclosed by
`e^{n + x} = e^n e^x` with `e` to `20` digits (Mathlib `Real.exp_one_near_20`) and the Taylor
series with remainder for `e^x`, `0 ≤ x ≤ 1` (Mathlib `Real.exp_bound`). -/

/-- `e_lo ≤ e ≤ e_hi` with `20` correct digits. -/
theorem exp_one_bounds :
    (363916618873 / 133877442384 - 1 / 10 ^ 20 : ℝ) ≤ exp 1 ∧
      exp 1 ≤ 363916618873 / 133877442384 + 1 / 10 ^ 20 := by
  have h := abs_sub_le_iff.1 Real.exp_one_near_20
  constructor <;> linarith [h.1, h.2]

theorem exp_nat_upper (n : ℕ) :
    exp n ≤ (363916618873 / 133877442384 + 1 / 10 ^ 20 : ℝ) ^ n := by
  rw [show exp (n : ℝ) = exp 1 ^ n by rw [← Real.exp_nat_mul, mul_one]]
  exact pow_le_pow_left₀ (exp_pos 1).le exp_one_bounds.2 n

theorem exp_nat_lower (n : ℕ) :
    (363916618873 / 133877442384 - 1 / 10 ^ 20 : ℝ) ^ n ≤ exp n := by
  rw [show exp (n : ℝ) = exp 1 ^ n by rw [← Real.exp_nat_mul, mul_one]]
  exact pow_le_pow_left₀ (by norm_num) exp_one_bounds.1 n

/-- Taylor series with remainder, upper bound. -/
theorem exp_upper (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (n : ℕ) (hn : 0 < n) :
    exp x ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) + x ^ n * (n + 1) / (n.factorial * n) :=
  Real.exp_bound' h1 h2 hn

/-- Taylor series with remainder, lower bound. -/
theorem exp_lower (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.range n, x ^ m / m.factorial) - x ^ n * (n + 1) / (n.factorial * n) ≤
      exp x := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg h1]; exact h2) hn
  rw [abs_of_nonneg h1] at h
  have := (abs_sub_le_iff.1 h).2
  push_cast at this
  rw [mul_div_assoc]
  linarith

theorem exp_split_upper (n : ℕ) (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (k : ℕ) (hk : 0 < k) :
    exp (n + x) ≤ (363916618873 / 133877442384 + 1 / 10 ^ 20 : ℝ) ^ n *
      ((∑ m ∈ Finset.range k, x ^ m / m.factorial) + x ^ k * (k + 1) / (k.factorial * k)) := by
  rw [Real.exp_add]
  exact mul_le_mul (exp_nat_upper n) (exp_upper x h1 h2 k hk) (exp_pos _).le (by positivity)

theorem exp_split_lower (n : ℕ) (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (k : ℕ) (hk : 0 < k)
    (hS : 0 ≤ (∑ m ∈ Finset.range k, x ^ m / m.factorial) - x ^ k * (k + 1) / (k.factorial * k)) :
    (363916618873 / 133877442384 - 1 / 10 ^ 20 : ℝ) ^ n *
      ((∑ m ∈ Finset.range k, x ^ m / m.factorial) - x ^ k * (k + 1) / (k.factorial * k)) ≤
      exp (n + x) := by
  rw [Real.exp_add]
  exact mul_le_mul (exp_nat_lower n) (exp_lower x h1 h2 k hk) hS (exp_pos _).le

/-- **[2] The numerical intervals for `a` and `b`.**
* Lines: proved here (rational enclosures of `exp` from `Real.exp_one_near_20` and the Taylor
  remainder `Real.exp_bound`; then exact rational arithmetic by `norm_num`).
* Directly from the PDF: yes (PDF Part VII §1; certificate `verify_numerical_bounds.py`). -/
theorem a_b_bounds :
    53.28758332262 < aConst ∧ aConst < 53.28758332263 ∧
      59.51995592483 < bConst ∧ bConst < 59.51995592484 := by
  obtain ⟨-, -, hlo, hhi⟩ := lam0_spec
  have hpos : 0 < lam0 := lt_trans (by norm_num) hlo
  have hc0 : (0 : ℝ) < chiC0 := by rw [chiC0]; push_cast; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `λ₀ < e^{-53.28758332262}`, i.e. `λ₀_hi · e^{53} e^{0.28758332262} < 1`
    rw [aConst, lt_neg, Real.log_lt_iff_lt_exp hpos]
    refine hhi.trans ?_
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (exp_pos _),
      show (53.28758332262 : ℝ) = (53 : ℕ) + 0.28758332262 by norm_num]
    refine (exp_split_upper 53 _ (by norm_num) (by norm_num) 15 (by norm_num)).trans_lt ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- `e^{-53.28758332263} < λ₀`, i.e. `1 < λ₀_lo · e^{53} e^{0.28758332263}`
    rw [aConst, neg_lt, Real.lt_log_iff_exp_lt hpos]
    refine lt_trans ?_ hlo
    rw [Real.exp_neg, inv_lt_comm₀ (exp_pos _) (by norm_num),
      show (53.28758332263 : ℝ) = (53 : ℕ) + 0.28758332263 by norm_num]
    refine lt_of_lt_of_le ?_ (exp_split_lower 53 _ (by norm_num) (by norm_num) 15 (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- `e^{2 · 59.51995592483} < c₀/λ₀`, using `c₀/λ₀_hi < c₀/λ₀`
    rw [bConst, aConst, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_eq_add_neg,
      ← Real.log_div hc0.ne' hpos.ne', Real.lt_log_iff_exp_lt (div_pos hc0 hpos)]
    refine lt_of_lt_of_le ?_ (div_le_div_of_nonneg_left hc0.le hpos hhi.le)
    rw [show (59.51995592483 : ℝ) * 2 = (119 : ℕ) + 0.03991184966 by norm_num]
    refine (exp_split_upper 119 _ (by norm_num) (by norm_num) 10 (by norm_num)).trans_lt ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    rw [chiC0]; push_cast
    norm_num
  · -- `c₀/λ₀ < e^{2 · 59.51995592484}`, using `c₀/λ₀ < c₀/λ₀_lo`
    rw [bConst, aConst, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_eq_add_neg,
      ← Real.log_div hc0.ne' hpos.ne', Real.log_lt_iff_lt_exp (div_pos hc0 hpos)]
    refine lt_of_le_of_lt (div_le_div_of_nonneg_left hc0.le (by norm_num) hlo.le) ?_
    rw [show (59.51995592484 : ℝ) * 2 = (119 : ℕ) + 0.03991184968 by norm_num]
    refine lt_of_lt_of_le ?_ (exp_split_lower 119 _ (by norm_num) (by norm_num) 10 (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    rw [chiC0]; push_cast
    norm_num

/-! ### Stirling bounds for [3] -/

/-- Stirling upper bound: `log n! ≤ n log n - n + 1 + log n / 2` for `n ≥ 1`. -/
theorem log_factorial_upper {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have h2 := Stirling.log_stirlingSeq_formula (m + 1)
  have hpos := Stirling.stirlingSeq'_pos m
  have h3 : Real.log (Stirling.stirlingSeq (m + 1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
    Real.log_le_log hpos h1
  rw [Stirling.stirlingSeq_one, Real.log_div (exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h3
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  rw [Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (exp_pos 1).ne', Real.log_exp] at h2
  push_cast at h2 h3 ⊢
  linarith

/-- Two-sided Stirling bounds for `(rN)!`. -/
theorem fact_bounds (r N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    (r * N : ℝ) * (Real.log r + Real.log N) - r * N ≤ Real.log ((r * N).factorial) ∧
    Real.log ((r * N).factorial) ≤
      (r * N : ℝ) * (Real.log r + Real.log N) - r * N + 1 + (Real.log r + Real.log N) / 2 := by
  have hne : r * N ≠ 0 := by positivity
  have hl := Stirling.le_log_factorial_stirling hne
  have hu := log_factorial_upper hne
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log ((r * N : ℕ) : ℝ) = Real.log r + Real.log N := by
    push_cast; rw [Real.log_mul hr'.ne' hN'.ne']
  rw [hlog] at hl hu
  push_cast at hl hu
  have h2π : 0 ≤ Real.log (2 * π) / 2 := by
    have : (1 : ℝ) ≤ 2 * π := by have := Real.pi_gt_three; linarith
    have := Real.log_nonneg this
    positivity
  have hlr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  constructor <;> linarith

/-- `c₀ = ∏_𝓐 r^r / (∏_𝓑 r^r ∏_𝓔 r^r)` (the Stirling main term of `F_N`). -/
theorem chiC0_eq : chiC0 = (16 ^ 16 * 17 ^ 17 * 18 ^ 18 * 15 ^ 15 * 14 ^ 14 * 17 ^ 17 * 18 ^ 18 *
    19 ^ 19 * 16 ^ 16 * 15 ^ 15 : ℚ) /
    ((11 ^ 11 * 10 ^ 10 * 9 ^ 9 * 12 ^ 12 * 13 ^ 13 * 12 ^ 12 * 11 ^ 11 * 10 ^ 10 * 13 ^ 13 *
      14 ^ 14) * (10 ^ 10 * 9 ^ 9 * 8 ^ 8 * 11 ^ 11 * 12 ^ 12)) := by
  rw [chiC0]; norm_num

theorem log_chiC0 : Real.log chiC0 =
    (16 * Real.log 16 + 17 * Real.log 17 + 18 * Real.log 18 + 15 * Real.log 15 + 14 * Real.log 14 +
      17 * Real.log 17 + 18 * Real.log 18 + 19 * Real.log 19 + 16 * Real.log 16 + 15 * Real.log 15) -
    (11 * Real.log 11 + 10 * Real.log 10 + 9 * Real.log 9 + 12 * Real.log 12 + 13 * Real.log 13 +
      12 * Real.log 12 + 11 * Real.log 11 + 10 * Real.log 10 + 13 * Real.log 13 + 14 * Real.log 14) -
    (10 * Real.log 10 + 9 * Real.log 9 + 8 * Real.log 8 + 11 * Real.log 11 + 12 * Real.log 12) := by
  rw [chiC0_eq]
  push_cast
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow]
  push_cast
  ring

/-- The constant in the Stirling error term of `log F_N`. -/
def FCst : ℝ := 15 + (Real.log 11 + Real.log 10 + Real.log 9 + Real.log 12 + Real.log 13 +
  Real.log 12 + Real.log 11 + Real.log 10 + Real.log 13 + Real.log 14 +
  Real.log 10 + Real.log 9 + Real.log 8 + Real.log 11 + Real.log 12) / 2

/-- `log F_N ≥ N log c₀ - FCst - (15/2) log N - 5 log(13N+1)` for `N ≥ 1`. -/
theorem log_F_ge (N : ℕ) (hN : 1 ≤ N) :
    N * Real.log chiC0 - FCst - 15 / 2 * Real.log N - 5 * Real.log (13 * N + 1) ≤
      Real.log (F N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : ∀ n : ℕ, (0 : ℝ) < (n.factorial : ℝ) := fun n => by positivity
  -- expand `F`
  have hF : (F N : ℝ) = (((16 * N).factorial : ℝ) * (17 * N).factorial * (18 * N).factorial *
      (15 * N).factorial * (14 * N).factorial * (17 * N).factorial * (18 * N).factorial *
      (19 * N).factorial * (16 * N).factorial * (15 * N).factorial) /
      (((11 * N).factorial * (10 * N).factorial * (9 * N).factorial * (12 * N).factorial *
        (13 * N).factorial * (12 * N).factorial * (11 * N).factorial * (10 * N).factorial *
        (13 * N).factorial * (14 * N).factorial) *
       ((10 * N + 1).factorial * (9 * N + 1).factorial * (8 * N + 1).factorial *
        (11 * N + 1).factorial * (12 * N + 1).factorial)) := by
    simp only [F, listA, listB, listE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    push_cast
    ring
  rw [hF]
  simp (disch := positivity) only [Real.log_div, Real.log_mul]
  -- the `(rN+1)!` terms
  have hE : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → Real.log ((r * N + 1).factorial) ≤
      Real.log (13 * N + 1) + Real.log ((r * N).factorial) := by
    intro r hr hr12
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (hf _).ne']
    have : ((r * N + 1 : ℕ) : ℝ) ≤ 13 * N + 1 := by
      push_cast
      have : (r : ℝ) ≤ 12 := by exact_mod_cast hr12
      nlinarith
    have := Real.log_le_log (by positivity) this
    linarith
  have h8 := fact_bounds 8 N (by norm_num) hN
  have h9 := fact_bounds 9 N (by norm_num) hN
  have h10 := fact_bounds 10 N (by norm_num) hN
  have h11 := fact_bounds 11 N (by norm_num) hN
  have h12 := fact_bounds 12 N (by norm_num) hN
  have h13 := fact_bounds 13 N (by norm_num) hN
  have h14 := fact_bounds 14 N (by norm_num) hN
  have h15 := fact_bounds 15 N (by norm_num) hN
  have h16 := fact_bounds 16 N (by norm_num) hN
  have h17 := fact_bounds 17 N (by norm_num) hN
  have h18 := fact_bounds 18 N (by norm_num) hN
  have h19 := fact_bounds 19 N (by norm_num) hN
  have e8 := hE 8 (by norm_num) (by norm_num)
  have e9 := hE 9 (by norm_num) (by norm_num)
  have e10 := hE 10 (by norm_num) (by norm_num)
  have e11 := hE 11 (by norm_num) (by norm_num)
  have e12 := hE 12 (by norm_num) (by norm_num)
  rw [log_chiC0]
  unfold FCst
  push_cast at *
  linarith

/-- **[3] Growth of `F_N = det V_N`.** `log F_N = N log c₀ + o(N)`, and `log c₀ = 2b - a`.
Only the lower bound is needed. Proof: Stirling's formula (Mathlib `Stirling`) for the 25
factorials in `F_N`. The linear terms give `∑_𝓐 r log r - ∑_𝓑 r log r - ∑_𝓔 r log r`, and this
is `log c₀` because `c₀ = det A` is the corresponding ratio of `r^r`.
* Lines: proved here (Mathlib's Stirling bounds `le_log_factorial_stirling` and
  `stirlingSeq'_antitone` for the 25 factorials, the identity `chiC0_eq` for `c₀` by `norm_num`,
  and `Aux.log_affine_isLittleO` for the `o(N)` error).
* Directly from the PDF: partially. The PDF states `det V_N = e^{(2b-a)N+o(N)}` but does not
  write out the Stirling computation or the identity for `c₀`. -/
theorem F_lower_bound :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, exp ((2 * bConst - aConst - ε) * N) ≤ (F N : ℝ) := by
  intro ε hε
  have hb : 2 * bConst - aConst = Real.log chiC0 := by unfold bConst; ring
  -- the error term is `o(N)`
  have hε' : 0 < ε / 2 / (25 / 2) := by positivity
  have ev1 : ∀ᶠ N : ℕ in atTop, FCst ≤ ε / 2 * N := by
    filter_upwards [eventually_ge_atTop ⌈FCst / (ε / 2)⌉₊] with N hN
    have : FCst / (ε / 2) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have ev2 : ∀ᶠ N : ℕ in atTop,
      15 / 2 * Real.log N + 5 * Real.log (13 * N + 1) ≤ ε / 2 * N := by
    filter_upwards [(Aux.log_affine_isLittleO 13 1 (by norm_num) (by norm_num)).def hε',
      eventually_ge_atTop 1] with N hN hN1
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hl0 : 0 ≤ Real.log (13 * N + 1) := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hN
    have hsq : Real.sqrt N ≤ N := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hlN : Real.log N ≤ Real.log (13 * N + 1) := Real.log_le_log (by linarith) (by linarith)
    have : Real.log (13 * N + 1) ≤ ε / 2 / (25 / 2) * N :=
      hN.trans (mul_le_mul_of_nonneg_left hsq hε'.le)
    have e : ε / 2 / (25 / 2) * N * (25 / 2) = ε / 2 * N := by ring
    nlinarith
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with N h1 h2 hN
  have hF : (0 : ℝ) < F N := by exact_mod_cast F_pos N
  rw [← Real.exp_log hF, exp_le_exp, hb]
  have := log_F_ge N hN
  nlinarith


/-! ### The limit matrix and the gauged recurrence (PDF Part VII §1 and §6)

`blk (Wmat N)` is the transport `𝓒_{N+1} = 𝓒_N blk (Wmat N)` (so `blk (Wmat N) = -B(N)` in the
notation of the PDF), and `GW.tendsto_gauged` gives `H(N) blk(Wmat N) H(N+1)⁻¹ → Lq = -A`.
The characteristic identity `χ(A) = 0` is checked on the exact rational matrix `Lq`. -/

/-- `Lq = -A` satisfies `Lq³ + c₂ Lq² + c₁ Lq + c₀ = 0`, i.e. `χ(A) = 0`. -/
theorem Lq_cubic : GW.Lq * GW.Lq * GW.Lq + chiC2 • (GW.Lq * GW.Lq) + chiC1 • GW.Lq +
    chiC0 • (1 : Matrix (Fin 3) (Fin 3) ℚ) = 0 := by
  decide +kernel

/-- The real limit matrix. -/
def Lr : Matrix (Fin 3) (Fin 3) ℝ := GW.Lq.map (Rat.cast : ℚ → ℝ)

theorem Lr_cubic : Lr * Lr * Lr + (chiC2 : ℝ) • (Lr * Lr) + (chiC1 : ℝ) • Lr +
    (chiC0 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  have hm : ∀ A B : Matrix (Fin 3) (Fin 3) ℚ,
      (A * B).map (Rat.cast : ℚ → ℝ) = A.map Rat.cast * B.map Rat.cast :=
    fun A B => Matrix.map_mul (f := Rat.castHom ℝ)
  have hs : ∀ (c : ℚ) (A : Matrix (Fin 3) (Fin 3) ℚ),
      (c • A).map (Rat.cast : ℚ → ℝ) = (c : ℝ) • A.map Rat.cast :=
    fun c A => Matrix.map_smul' _ c A fun a b => Rat.cast_mul a b
  have ha : ∀ A B : Matrix (Fin 3) (Fin 3) ℚ,
      (A + B).map (Rat.cast : ℚ → ℝ) = A.map Rat.cast + B.map Rat.cast :=
    fun A B => Matrix.map_add _ (fun a b => Rat.cast_add a b) A B
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M.map (Rat.cast : ℚ → ℝ)) Lq_cubic
  simp only [ha, hm, hs, Matrix.map_one _ Rat.cast_zero Rat.cast_one,
    Matrix.map_zero _ Rat.cast_zero] at h
  exact h

theorem lam0_pos : 0 < lam0 := lt_trans (by norm_num) lam0_spec.2.2.1

/-- The real eigenvalue of `Lr` is `-λ₀`. -/
def lamR : ℝ := -lam0
/-- `Lr² - τ Lr + σ` vanishes on the plane of the complex pair: `τ = λ₀ - c₂`, `σ = c₀/λ₀`. -/
def tauR : ℝ := lam0 - chiC2
def sigR : ℝ := chiC0 / lam0

theorem chi_lam0 : lam0 ^ 3 - chiC2 * lam0 ^ 2 + chiC1 * lam0 - chiC0 = 0 := lam0_spec.1

theorem Lr_factor : (Lr - lamR • 1) * (Lr * Lr - tauR • Lr + sigR • 1) = 0 := by
  have hl := lam0_pos.ne'
  have e1 : -lamR - tauR = chiC2 := by simp only [lamR, tauR]; ring
  have e2 : sigR + lamR * tauR = chiC1 := by
    simp only [sigR, lamR, tauR]; field_simp; linear_combination -chi_lam0
  have e3 : -lamR * sigR = chiC0 := by simp only [sigR, lamR]; field_simp
  calc (Lr - lamR • 1) * (Lr * Lr - tauR • Lr + sigR • 1)
      = Lr * Lr * Lr + (-lamR - tauR) • (Lr * Lr) + (sigR + lamR * tauR) • Lr +
          (-lamR * sigR) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        simp only [sub_mul, mul_sub, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul,
          mul_one, mul_assoc]
        module
    _ = 0 := by rw [e1, e2, e3]; exact Lr_cubic

/-- The quadratic factor has no real root (`χ` has negative discriminant). -/
theorem tau_disc : tauR ^ 2 < 4 * sigR := by
  have hl := lam0_pos
  by_contra hcon
  have hD : 0 ≤ tauR ^ 2 - 4 * sigR := by linarith [not_lt.mp hcon]
  set r := (-tauR + √(tauR ^ 2 - 4 * sigR)) / 2
  have hsq := Real.sq_sqrt hD
  have hr : r ^ 2 + tauR * r + sigR = 0 := by simp only [r]; nlinarith [hsq]
  have hchi : chi r = 0 := by
    have : chi r = (r - lam0) * (r ^ 2 + tauR * r + sigR) := by
      simp only [chi, tauR, sigR]; field_simp; linear_combination r * chi_lam0
    rw [this, hr, mul_zero]
  have hr0 := lam0_spec.2.1 r hchi
  have hq : lam0 ^ 2 + tauR * lam0 + sigR = 3 * lam0 ^ 2 - 2 * chiC2 * lam0 + chiC1 := by
    simp only [tauR, sigR]; field_simp; linear_combination -chi_lam0
  have hpos : 0 < 3 * lam0 ^ 2 - 2 * chiC2 * lam0 + chiC1 := by
    nlinarith [chiC2_sq_lt, sq_nonneg (3 * lam0 - chiC2)]
  rw [hr0] at hr
  linarith

theorem lam_lt : |lamR| < √sigR := by
  have hl := lam0_pos
  have h1 : lam0 < 1 := lt_trans lam0_spec.2.2.2 (by norm_num)
  have h2 : (1 : ℝ) < chiC0 := by rw [chiC0]; push_cast; norm_num
  rw [lamR, abs_neg, abs_of_pos hl, Real.lt_sqrt hl.le, sigR, lt_div_iff₀ hl]
  nlinarith

theorem sqrt_sig : √sigR = exp bConst := by
  have hc0 : (0 : ℝ) < chiC0 := by rw [chiC0]; push_cast; norm_num
  have h : exp bConst ^ 2 = sigR := by
    rw [← Real.exp_nat_mul, bConst, aConst, sigR]
    rw [show ((2 : ℕ) : ℝ) * ((Real.log chiC0 + -Real.log lam0) / 2) =
      Real.log (chiC0 / lam0) by rw [Real.log_div hc0.ne' lam0_pos.ne']; push_cast; ring,
      Real.exp_log (div_pos hc0 lam0_pos)]
  rw [← h, Real.sqrt_sq (exp_pos _).le]

theorem abs_lam : |lamR| = exp (-aConst) := by
  rw [lamR, abs_neg, abs_of_pos lam0_pos, aConst, neg_neg, Real.exp_log lam0_pos]

/-- The gauged transport `H(N+1) blk(Wmat (N+1)) H(N+2)⁻¹`. -/
def Mg (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun k j : Fin 3 =>
  ((N + 1 : ℕ) : ℝ) ^ (k : ℕ) * (CMF.blk (CMF.Wmat (N + 1)) k j : ℝ) /
    (((N + 1 : ℕ) : ℝ) + 1) ^ (j : ℕ)

theorem Mg_tendsto : Tendsto Mg atTop (𝓝 Lr) :=
  GW.tendsto_gauged.comp (tendsto_add_atTop_nat 1)

/-- The gauged row `x_N = u_{N+1} H(N+1)⁻¹`. -/
def gx (u : ℕ → Fin 3 → ℝ) (N : ℕ) : Fin 3 → ℝ := fun j => u (N + 1) j / ((N : ℝ) + 1) ^ (j : ℕ)

theorem gauge_rec (u : ℕ → Fin 3 → ℝ)
    (hu : ∀ N j, u (N + 1) j = ∑ k, u N k * (CMF.blk (CMF.Wmat N) k j : ℝ)) :
    (∀ N, gx u (N + 1) = Matrix.vecMul (gx u N) (Mg N)) ∧ (∀ N, ‖gx u N‖ ≤ ‖u (N + 1)‖) ∧
      ∀ N j, |u (N + 1) j| ≤ ((N : ℝ) + 1) ^ 2 * ‖gx u N‖ := by
  have hN1 : ∀ N : ℕ, (1 : ℝ) ≤ (N : ℝ) + 1 := fun N => by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  refine ⟨fun N => ?_, fun N => ?_, fun N j => ?_⟩
  · funext j
    have hp : ∀ k : Fin 3, ((N : ℝ) + 1) ^ (k : ℕ) ≠ 0 := fun k => pow_ne_zero _ (by linarith [hN1 N])
    simp only [gx, Matrix.vecMul, dotProduct, Mg, Matrix.of_apply]
    rw [hu (N + 1) j, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    field_simp
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
    have hp : (0 : ℝ) < ((N : ℝ) + 1) ^ (j : ℕ) := pow_pos (by linarith [hN1 N]) _
    rw [gx, Real.norm_eq_abs, abs_div, abs_of_pos hp]
    exact (div_le_self (abs_nonneg _) (one_le_pow₀ (hN1 N))).trans (norm_le_pi_norm (u (N + 1)) j)
  · have hp : 0 < ((N : ℝ) + 1) ^ (j : ℕ) := pow_pos (by linarith [hN1 N]) _
    have e : u (N + 1) j = gx u N j * ((N : ℝ) + 1) ^ (j : ℕ) := by
      rw [gx, div_mul_cancel₀ _ hp.ne']
    rw [e, abs_mul, abs_of_pos hp, mul_comm]
    exact mul_le_mul (pow_le_pow_right₀ (hN1 N) (by omega)) (norm_le_pi_norm (gx u N) j)
      (abs_nonneg _) (by positivity)

theorem ev_exp_bound {C ρ c : ℝ} (hρ : 0 < ρ) (hρc : ρ < exp c) :
    ∀ᶠ N : ℕ in atTop, C * (((N : ℝ) + 1) ^ 2 * ρ ^ N) ≤ exp (c * ((N + 1 : ℕ) : ℝ)) := by
  set q := ρ / exp c
  have hq0 : 0 < q := div_pos hρ (exp_pos c)
  have hq : |q| < 1 := by rw [abs_of_pos hq0]; exact (div_lt_one (exp_pos c)).mpr hρc
  have h := (((tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hq).add
    ((tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq).const_mul 2)).add
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq)).const_mul C
  simp only [mul_zero, add_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds (exp_pos c))] with N hN
  have hρq : ρ = q * exp c := by rw [div_mul_cancel₀ _ (exp_pos c).ne']
  have he : exp (c * ((N + 1 : ℕ) : ℝ)) = exp c * exp c ^ N := by
    rw [mul_comm, Real.exp_nat_mul, pow_succ, mul_comm]
  rw [he, hρq, mul_pow]
  have hcN : 0 < exp c ^ N := pow_pos (exp_pos c) N
  have : C * (((N : ℝ) + 1) ^ 2 * q ^ N) = C * ((N : ℝ) ^ 2 * q ^ N + 2 * ((N : ℝ) ^ 1 * q ^ N) + q ^ N) := by
    ring
  nlinarith

theorem ev_shift {P : ℕ → Prop} (h : ∀ᶠ N in atTop, P (N + 1)) : ∀ᶠ N in atTop, P N := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨N₀ + 1, fun N hN => ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact hN₀ M (by omega)

/-- **[4] Growth of the `ζ(4)`- and `ζ(3)`-rows.** `‖A_N‖, ‖B_N‖ ≤ e^{bN+o(N)}`.

Proof: the rows of `𝓒_N` satisfy the recurrence of the walk, `𝓒_{N+1} = 𝓒_N blk(Wmat N)`. With the
gauge `H(n) = diag(1, n, n²)`, `H(n) blk(Wmat n) H(n+1)⁻¹ → Lq = -A` (`GW.tendsto_gauged`: the
walk is the product of twelve six-step blocks whose exact entries are certified in
`GW_cert0`–`GW_cert5`), where the eigenvalues of `A` are `λ₀ = e^{-a}` and a pair of modulus `e^b`
(`Lr_factor`, `tau_disc`, `sqrt_sig`). The product bound `GW.cone_growth` gives growth at most
`(e^b + δ)^N`.
* Lines: proved here and in `GW_fast`, `GW_poly`, `GW_cert0`–`GW_cert5`, `GW_bridge`, `GW_limit`,
  `GW_cone`.
* Directly from the PDF: partially. The PDF gives the statement and the strategy. The
  matrices come from `verify_matrix.py`. -/
theorem coeff_rows_growth :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ j,
      |(coeffMat N 0 j : ℝ)| ≤ exp ((bConst + ε) * N) ∧
        |(coeffMat N 1 j : ℝ)| ≤ exp ((bConst + ε) * N) := by
  intro ε hε
  have row : ∀ i : Fin 3, ∀ᶠ N : ℕ in atTop, ∀ j,
      |(coeffMat N i j : ℝ)| ≤ exp ((bConst + ε) * N) := by
    intro i
    set u : ℕ → Fin 3 → ℝ := fun N j => (coeffMat N i j : ℝ)
    have hu : ∀ N j, u (N + 1) j = ∑ k, u N k * (CMF.blk (CMF.Wmat N) k j : ℝ) := fun N j => by
      simp only [u, CMF.coeffMat_succ', Matrix.mul_apply]
      push_cast
      rfl
    obtain ⟨hrec, -, hback⟩ := gauge_rec u hu
    have hδ : 0 < exp (bConst + ε / 2) - √sigR := by
      rw [sqrt_sig]; exact sub_pos.mpr (exp_lt_exp.mpr (by linarith))
    obtain ⟨C, hC⟩ := GW.cone_growth Lr_factor tau_disc lam_lt Mg_tendsto hrec hδ
    rw [add_sub_cancel] at hC
    refine ev_shift ?_
    filter_upwards [ev_exp_bound (C := C) (exp_pos (bConst + ε / 2))
      (exp_lt_exp.mpr (by linarith : bConst + ε / 2 < bConst + ε))] with N hN j
    have h1 := hback N j
    have h2 := mul_le_mul_of_nonneg_left (hC N) (sq_nonneg ((N : ℝ) + 1))
    calc |(coeffMat (N + 1) i j : ℝ)| = |u (N + 1) j| := rfl
      _ ≤ C * (((N : ℝ) + 1) ^ 2 * exp (bConst + ε / 2) ^ N) := by linarith
      _ ≤ exp ((bConst + ε) * ((N + 1 : ℕ) : ℝ)) := hN
  filter_upwards [row 0, row 1] with N h0 h1 j
  exact ⟨h0 j, h1 j⟩

/-- **[5] Decay of the linear forms.** `‖S_N‖ ≤ e^{-aN+o(N)}`.

Proof (PDF Part VII §6): (i) a bound `‖S_N‖ ≤ e^{cN}` with `c < b`. Here it is the polynomial
bound `|S_{Nj}| ≤ C (N + 1)` of `GW.S_poly_bound`, read off from the derivative sum (the PDF uses
the contour bound with `c₀' = 48.43… < b`); (ii) the cone argument `GW.cone_decay`: a solution of
the recurrence that grows more slowly than `e^{bN}` contracts at rate `e^{-a}`.
* Lines: proved here and in `GW_Sbound`, `GW_cone` (with the transport files of [4]).
* Directly from the PDF: partially. Part (ii) is sketched. The residue evaluation of the contour
  integral is asserted, not proved. -/
theorem S_decay :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ j, |S N j| ≤ exp ((-aConst + ε) * N) := by
  intro ε hε
  set u : ℕ → Fin 3 → ℝ := fun N j => S N j
  have hu : ∀ N j, u (N + 1) j = ∑ k, u N k * (CMF.blk (CMF.Wmat N) k j : ℝ) := fun N j => by
    simp only [u, ZetasIrr.S_eq, CMF.coeffMat_succ', Matrix.mul_apply, Fin.sum_univ_three]
    push_cast
    ring
  obtain ⟨hrec, hfwd, hback⟩ := gauge_rec u hu
  obtain ⟨C₀, hC₀⟩ := GW.S_poly_bound
  have hb : ∀ N, ‖gx u N‖ ≤ (2 * |C₀|) * 2 ^ N := fun N => by
    have hN : ((N + 1 : ℕ) : ℝ) + 1 ≤ 2 * 2 ^ N := by
      have : N + 2 ≤ 2 * 2 ^ N := by
        have := Nat.lt_two_pow_self (n := N)
        have : 1 ≤ 2 ^ N := Nat.one_le_two_pow
        omega
      exact_mod_cast this
    refine (hfwd N).trans ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_)
    rw [Real.norm_eq_abs]
    calc |u (N + 1) j| ≤ C₀ * (((N + 1 : ℕ) : ℝ) + 1) := hC₀ (N + 1) j
      _ ≤ |C₀| * (2 * 2 ^ N) :=
          mul_le_mul (le_abs_self C₀) hN (by positivity) (abs_nonneg _)
      _ = 2 * |C₀| * 2 ^ N := by ring
  have h2 : (2 : ℝ) < √sigR := by
    rw [sqrt_sig]
    have := a_b_bounds.2.2.1
    have := Real.add_one_lt_exp (by linarith : bConst ≠ 0)
    linarith
  have hδ : 0 < exp (-aConst + ε / 2) - |lamR| := by
    rw [abs_lam]; exact sub_pos.mpr (exp_lt_exp.mpr (by linarith))
  obtain ⟨C, hC⟩ := GW.cone_decay Lr_factor tau_disc lam_lt Mg_tendsto hrec (by norm_num) h2 hb hδ
  rw [add_sub_cancel] at hC
  refine ev_shift ?_
  filter_upwards [ev_exp_bound (C := C) (exp_pos (-aConst + ε / 2))
    (exp_lt_exp.mpr (by linarith : -aConst + ε / 2 < -aConst + ε))] with N hN j
  have h1 := hback N j
  have h3 := mul_le_mul_of_nonneg_left (hC N) (sq_nonneg ((N : ℝ) + 1))
  calc |S (N + 1) j| = |u (N + 1) j| := rfl
    _ ≤ C * (((N : ℝ) + 1) ^ 2 * exp (-aConst + ε / 2) ^ N) := by linarith
    _ ≤ exp ((-aConst + ε) * ((N + 1 : ℕ) : ℝ)) := hN

/-- **[6] `q_N = -(A_N × B_N)/det V_N`.** This is the first component of
`readouts_eq_cross` in `blueprints/cross_product_readout.lean`.
* Lines: see `cross_product_readout.lean`.
* Directly from the PDF: yes. -/
theorem q_eq_cross (N : ℕ) :
    (fun j => (q N j : ℝ)) = -((V N).det : ℝ)⁻¹ •
      crossProduct (fun j => (coeffMat N 0 j : ℝ)) (fun j => (coeffMat N 1 j : ℝ)) :=
  (ZetasIrr.readouts_eq_cross N).1

/- **[7] `det V_N = F_N`** (the node `det_V_eq` of `blueprint.lean`) and **[8] `F_N > 0`** are
`ZetasIrr.BP.det_V_eq` and `ZetasIrr.BP.F_pos`, imported from `blueprints/det_V_eq.lean`. -/

/-- **[9] Size of a cross product.** If `|u_i| ≤ M` and `|v_i| ≤ M'`, then `|(u × v)_j| ≤ 2MM'`.
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem abs_cross_le (u v : Fin 3 → ℝ) (M M' : ℝ) (hu : ∀ i, |u i| ≤ M) (hv : ∀ i, |v i| ≤ M')
    (j : Fin 3) : |crossProduct u v j| ≤ 2 * (M * M') := by
  have key : ∀ a b c d : ℝ, |a| ≤ M → |b| ≤ M' → |c| ≤ M → |d| ≤ M' →
      |a * b - c * d| ≤ 2 * (M * M') := by
    intro a b c d ha hb hc hd
    have hM' : 0 ≤ M' := (abs_nonneg _).trans hb
    calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
      _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
      _ ≤ M * M' + M * M' := add_le_add (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))
          (mul_le_mul hc hd (abs_nonneg _) ((abs_nonneg _).trans ha))
      _ = 2 * (M * M') := by ring
  fin_cases j <;> simp only [cross_apply] <;> exact key _ _ _ _ (hu _) (hv _) (hu _) (hv _)

/-- **Main theorem (`blueprint.lean`, `growth_estimates`).** Proved from [1]–[9]
(with `a = aConst`, `b = bConst`). -/
theorem growth_estimates :
    ∃ a b : ℝ, 53.28758332262 < a ∧ a < 53.28758332263 ∧
      59.51995592483 < b ∧ b < 59.51995592484 ∧
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
        (∀ j, |(coeffMat N 0 j : ℝ)| ≤ exp ((b + ε) * N) ∧
              |(coeffMat N 1 j : ℝ)| ≤ exp ((b + ε) * N) ∧
              |S N j| ≤ exp ((-a + ε) * N) ∧
              |(q N j : ℝ)| ≤ exp ((a + ε) * N)) ∧
        exp ((2 * b - a - ε) * N) ≤ ((V N).det : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := a_b_bounds
  refine ⟨aConst, bConst, h1, h2, h3, h4, fun ε hε => ?_⟩
  set ε' := ε / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  -- `2 ≤ e^{ε' N}` eventually
  have h2N : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ exp (ε' * N) := by
    have : Tendsto (fun N : ℕ => exp (ε' * N)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hε'pos)
    exact this.eventually_ge_atTop 2
  filter_upwards [coeff_rows_growth ε' hε'pos, S_decay ε hε, F_lower_bound ε hε,
    F_lower_bound ε' hε'pos, h2N] with N hAB hS hF hF' h2
  have hdet : ((V N).det : ℝ) = F N := by rw [det_V_eq]
  have hdpos : (0 : ℝ) < (V N).det := by rw [hdet]; exact_mod_cast F_pos N
  refine ⟨fun j => ⟨?_, ?_, hS j, ?_⟩, by rw [hdet]; exact hF⟩
  · exact (hAB j).1.trans (exp_le_exp.mpr (by gcongr; linarith))
  · exact (hAB j).2.trans (exp_le_exp.mpr (by gcongr; linarith))
  · -- `|q| = |A × B| / det V ≤ 2e^{2(b+ε')N} / e^{(2b-a-ε')N} ≤ e^{(a+ε)N}`
    have hq := congrFun (q_eq_cross N) j
    simp only [Pi.smul_apply, smul_eq_mul] at hq
    have hX := abs_cross_le (fun j => (coeffMat N 0 j : ℝ)) (fun j => (coeffMat N 1 j : ℝ))
      _ _ (fun i => (hAB i).1) (fun i => (hAB i).2) j
    rw [hq, abs_mul, abs_neg, abs_inv, abs_of_pos hdpos, inv_mul_le_iff₀ hdpos]
    calc |crossProduct (fun j => (coeffMat N 0 j : ℝ)) (fun j => (coeffMat N 1 j : ℝ)) j|
        ≤ 2 * (exp ((bConst + ε') * N) * exp ((bConst + ε') * N)) := hX
      _ ≤ exp (ε' * N) * (exp ((bConst + ε') * N) * exp ((bConst + ε') * N)) := by gcongr
      _ = exp ((aConst + ε) * N) * exp ((2 * bConst - aConst - ε') * N) := by
          rw [← exp_add, ← exp_add, ← exp_add]; congr 1; rw [hε']; ring
      _ ≤ exp ((aConst + ε) * N) * (V N).det := by
          gcongr; rw [hdet]; exact hF'
      _ = (V N).det * exp ((aConst + ε) * N) := mul_comm _ _

end ZetasIrr.BP
