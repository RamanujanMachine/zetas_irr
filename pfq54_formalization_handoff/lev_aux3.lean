/-
# The products `∏_{m=k}^{n-1} (1 + α/m)` (sorry-free)

Two-sided bounds `e^{-C_α} (n/k)^{Re α} ≤ |∏| ≤ e^{C_α} (n/k)^{Re α}` for `N₁(α) ≤ k ≤ n`, from
`log(1+z) = z + O(z²)` and the Euler–Mascheroni bounds on `∑ 1/m`; and the asymptotics
`∏_{m=N}^{n-1}(1 + α/m) / (n+1)^α → κ ≠ 0`.
-/
import lev_aux2

open Finset Filter Topology

noncomputable section

namespace Pfq54.LV

/-- `∏_{m=k}^{n-1} (1 + α/m)`. -/
def prodA (α : ℂ) (k n : ℕ) : ℂ := ∏ m ∈ Finset.Ico k n, (1 + α / (m : ℂ))

/-- `log(1 + α/m)`. -/
def LA (α : ℂ) (m : ℕ) : ℂ := Complex.log (1 + α / (m : ℂ))

/-- The threshold `N₁ = ⌈2‖α‖⌉ + 1`. -/
def N₁ (α : ℂ) : ℕ := ⌈2 * ‖α‖⌉₊ + 1

/-- The constant `C_α = ‖α‖ + 2‖α‖²`. -/
def CA (α : ℂ) : ℝ := ‖α‖ + 2 * ‖α‖ ^ 2

/-- `∑_{m=k}^{n-1} 1/m`. -/
def HS (k n : ℕ) : ℝ := ∑ m ∈ Finset.Ico k n, (1 / (m : ℝ))

theorem N₁_pos (α : ℂ) : 1 ≤ N₁ α := by
  unfold N₁
  omega

theorem CA_nonneg (α : ℂ) : 0 ≤ CA α := by
  unfold CA
  positivity

theorem two_norm_le (α : ℂ) (m : ℕ) (hm : N₁ α ≤ m) : 2 * ‖α‖ ≤ m := by
  have h1 := Nat.le_ceil (2 * ‖α‖)
  have h2 : (⌈2 * ‖α‖⌉₊ : ℝ) ≤ m := by
    have : ⌈2 * ‖α‖⌉₊ ≤ m := by unfold N₁ at hm; omega
    exact_mod_cast this
  linarith

theorem norm_div_le_half (α : ℂ) (m : ℕ) (hm : N₁ α ≤ m) : ‖α / (m : ℂ)‖ ≤ 1 / 2 := by
  have hm0 : (0 : ℝ) < m := by
    have := N₁_pos α
    exact_mod_cast (show 0 < m by omega)
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hm0]
  linarith [two_norm_le α m hm]

theorem one_add_div_ne_zero (α : ℂ) (m : ℕ) (hm : N₁ α ≤ m) : 1 + α / (m : ℂ) ≠ 0 := by
  intro h
  have := norm_div_le_half α m hm
  have h1 : α / (m : ℂ) = -1 := by linear_combination h
  rw [h1, norm_neg, norm_one] at this
  linarith

theorem LA_sub_le (α : ℂ) (m : ℕ) (hm : N₁ α ≤ m) :
    ‖LA α m - α / (m : ℂ)‖ ≤ ‖α / (m : ℂ)‖ ^ 2 := by
  have h := norm_div_le_half α m hm
  have h1 := Complex.norm_log_one_add_sub_self_le (z := α / (m : ℂ)) (by linarith)
  have h2 : (1 - ‖α / (m : ℂ)‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖LA α m - α / (m : ℂ)‖ ≤ ‖α / (m : ℂ)‖ ^ 2 * (1 - ‖α / (m : ℂ)‖)⁻¹ / 2 := h1
    _ ≤ ‖α / (m : ℂ)‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖α / (m : ℂ)‖ ^ 2 := by ring

theorem norm_div_sq (α : ℂ) (m : ℕ) : ‖α / (m : ℂ)‖ ^ 2 = ‖α‖ ^ 2 * (1 / (m : ℝ) ^ 2) := by
  rw [norm_div, Complex.norm_natCast, div_pow]
  ring

theorem prodA_eq_exp (α : ℂ) (k n : ℕ) (hk : N₁ α ≤ k) :
    prodA α k n = Complex.exp (∑ m ∈ Finset.Ico k n, LA α m) := by
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  unfold LA
  rw [Complex.exp_log (one_add_div_ne_zero α m (by omega))]

theorem norm_prodA (α : ℂ) (k n : ℕ) (hk : N₁ α ≤ k) :
    ‖prodA α k n‖ = Real.exp ((∑ m ∈ Finset.Ico k n, LA α m).re) := by
  rw [prodA_eq_exp α k n hk, Complex.norm_exp]

/-! ### Harmonic sums -/

theorem harmonic_cast (j : ℕ) : (harmonic j : ℝ) = ∑ i ∈ Finset.range j, (1 / ((i + 1 : ℕ) : ℝ)) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem HS_eq (k n : ℕ) (hkn : k ≤ n) :
    HS (k + 1) (n + 1) = (harmonic n : ℝ) - harmonic k := by
  unfold HS
  rw [Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_succ', Finset.sum_range_succ',
    harmonic_cast, harmonic_cast]
  simp

theorem HS_sub_log_bounds (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    0 ≤ HS k n - (Real.log n - Real.log k) ∧ HS k n - (Real.log n - Real.log k) ≤ 1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [HS_eq k' n' (by omega)]
  have e : ∀ j : ℕ, (harmonic j : ℝ) - Real.log ((j + 1 : ℕ) : ℝ) = Real.eulerMascheroniSeq j := by
    intro j
    unfold Real.eulerMascheroniSeq
    push_cast
    rfl
  have h1 : (harmonic n' : ℝ) - harmonic k' -
      (Real.log ((n' + 1 : ℕ) : ℝ) - Real.log ((k' + 1 : ℕ) : ℝ)) =
      Real.eulerMascheroniSeq n' - Real.eulerMascheroniSeq k' := by
    rw [← e, ← e]
    ring
  rw [h1]
  have hmono := Real.strictMono_eulerMascheroniSeq.monotone (show k' ≤ n' by omega)
  have h0 : 0 ≤ Real.eulerMascheroniSeq k' := by
    rw [← Real.eulerMascheroniSeq_zero]
    exact Real.strictMono_eulerMascheroniSeq.monotone (Nat.zero_le _)
  have hlt := (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n').trans
    Real.eulerMascheroniConstant_lt_two_thirds
  constructor <;> linarith

theorem sum_inv_sq_le (k n : ℕ) : ∑ m ∈ Finset.Ico k n, (1 / (m : ℝ) ^ 2) ≤ 2 := by
  have hs := hasSum_zeta_two
  have h1 := hs.summable.sum_le_tsum (Finset.Ico k n) (fun m _ => by positivity)
  rw [hs.tsum_eq] at h1
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

/-! ### The two-sided bound -/

theorem re_sum_LA_bounds (α : ℂ) (k n : ℕ) (hk : N₁ α ≤ k) (hkn : k ≤ n) :
    |(∑ m ∈ Finset.Ico k n, LA α m).re - α.re * (Real.log n - Real.log k)| ≤ CA α := by
  have hk1 : 1 ≤ k := (N₁_pos α).trans hk
  have hsplit : (∑ m ∈ Finset.Ico k n, LA α m) =
      (∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))) + α * (HS k n : ℂ) := by
    unfold HS
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hsplit, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  have hA : ‖∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))‖ ≤ 2 * ‖α‖ ^ 2 := by
    calc ‖∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))‖
        ≤ ∑ m ∈ Finset.Ico k n, ‖LA α m - α / (m : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Ico k n, ‖α‖ ^ 2 * (1 / (m : ℝ) ^ 2) := Finset.sum_le_sum fun m hm => by
          rw [Finset.mem_Ico] at hm
          exact (LA_sub_le α m (by omega)).trans (le_of_eq (norm_div_sq α m))
      _ = ‖α‖ ^ 2 * ∑ m ∈ Finset.Ico k n, (1 / (m : ℝ) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ ‖α‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le k n) (by positivity)
      _ = 2 * ‖α‖ ^ 2 := by ring
  obtain ⟨h0, h1⟩ := HS_sub_log_bounds k n hk1 hkn
  have hre : |(∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))).re| ≤ 2 * ‖α‖ ^ 2 :=
    (Complex.abs_re_le_norm _).trans hA
  have hαre : |α.re| ≤ ‖α‖ := Complex.abs_re_le_norm α
  have habs : |HS k n - (Real.log n - Real.log k)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  unfold CA
  calc |(∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))).re + α.re * HS k n -
        α.re * (Real.log n - Real.log k)|
      = |(∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))).re +
          α.re * (HS k n - (Real.log n - Real.log k))| := by congr 1; ring
    _ ≤ |(∑ m ∈ Finset.Ico k n, (LA α m - α / (m : ℂ))).re| +
          |α.re * (HS k n - (Real.log n - Real.log k))| := abs_add_le _ _
    _ ≤ 2 * ‖α‖ ^ 2 + ‖α‖ * 1 := by
        rw [abs_mul]
        exact add_le_add hre (mul_le_mul hαre habs (abs_nonneg _) (norm_nonneg _))
    _ = ‖α‖ + 2 * ‖α‖ ^ 2 := by ring

theorem prodA_bounds (α : ℂ) (k n : ℕ) (hk : N₁ α ≤ k) (hkn : k ≤ n) :
    Real.exp (-CA α) * ((n : ℝ) / k) ^ α.re ≤ ‖prodA α k n‖ ∧
      ‖prodA α k n‖ ≤ Real.exp (CA α) * ((n : ℝ) / k) ^ α.re := by
  have hk1 : 1 ≤ k := (N₁_pos α).trans hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (hk1.trans hkn)
  rw [norm_prodA α k n hk]
  have hr : ((n : ℝ) / k) ^ α.re = Real.exp (α.re * (Real.log n - Real.log k)) := by
    rw [Real.rpow_def_of_pos (div_pos hnpos hkpos), Real.log_div hnpos.ne' hkpos.ne', mul_comm]
  rw [hr, ← Real.exp_add, ← Real.exp_add]
  have h := re_sum_LA_bounds α k n hk hkn
  rw [abs_le] at h
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith [h.1, h.2]

/-! ### Asymptotics -/

theorem summable_LA_sub (α : ℂ) (N : ℕ) (hN : N₁ α ≤ N) :
    Summable (fun m : ℕ => LA α (m + N) - α / ((m + N : ℕ) : ℂ)) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => ‖α‖ ^ 2 * (1 / ((m : ℝ) + 1) ^ 2)) ?_
    fun m => ?_
  · have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (h.mul_left (‖α‖ ^ 2)).congr fun m => ?_
    push_cast
    ring
  · refine (LA_sub_le α (m + N) (by omega)).trans ?_
    rw [norm_div_sq]
    have hN1 : 1 ≤ N := (N₁_pos α).trans hN
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h1 : ((m : ℝ) + 1) ≤ ((m + N : ℕ) : ℝ) := by push_cast; linarith
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) h1 2)) (by positivity)

theorem tendsto_prodA_div (α : ℂ) (N : ℕ) (hN : N₁ α ≤ N) :
    ∃ κ : ℂ, κ ≠ 0 ∧ Tendsto (fun n : ℕ => prodA α N n / ((n : ℂ) + 1) ^ α) atTop (𝓝 κ) := by
  have hN1 : 1 ≤ N := (N₁_pos α).trans hN
  have hf := summable_LA_sub α N hN
  have h1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n - N),
      (LA α (i + N) - α / ((i + N : ℕ) : ℂ))) atTop
      (𝓝 (∑' m, (LA α (m + N) - α / ((m + N : ℕ) : ℂ)))) :=
    hf.hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat N)
  have h2 : Tendsto (fun n : ℕ => ((harmonic (n - 1) : ℝ) - Real.log n : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have := Real.tendsto_harmonic_sub_log_add_one.comp (tendsto_sub_atTop_nat 1)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp]
    rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
  have h3 : Tendsto (fun n : ℕ => Real.log n - Real.log ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := Real.tendsto_log_nat_add_one_sub_log.neg
    rw [neg_zero] at this
    refine this.congr fun n => ?_
    ring
  refine ⟨Complex.exp (∑' m, (LA α (m + N) - α / ((m + N : ℕ) : ℂ)) +
    α * ((Real.eulerMascheroniConstant : ℂ) - (harmonic (N - 1) : ℂ))), Complex.exp_ne_zero _, ?_⟩
  have key : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n - N),
      (LA α (i + N) - α / ((i + N : ℕ) : ℂ))) +
      α * (((((harmonic (n - 1) : ℝ) - Real.log n : ℝ)) : ℂ) - (harmonic (N - 1) : ℂ) +
        ((Real.log n - Real.log ((n : ℝ) + 1) : ℝ) : ℂ))) atTop
      (𝓝 (∑' m, (LA α (m + N) - α / ((m + N : ℕ) : ℂ)) +
        α * ((Real.eulerMascheroniConstant : ℂ) - (harmonic (N - 1) : ℂ)))) := by
    have h2c := (Complex.continuous_ofReal.tendsto _).comp h2
    have h3c := (Complex.continuous_ofReal.tendsto _).comp h3
    have := h1.add (((h2c.sub_const (harmonic (N - 1) : ℂ)).add h3c).const_mul α)
    simp only [Function.comp, Complex.ofReal_zero, add_zero] at this
    exact this
  have hexp := (Complex.continuous_exp.tendsto _).comp key
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [Function.comp]
  rw [prodA_eq_exp α N n hN, Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n),
    ← Complex.exp_sub]
  congr 1
  have hsplit : ∑ m ∈ Finset.Ico N n, LA α m = (∑ i ∈ Finset.range (n - N),
      (LA α (i + N) - α / ((i + N : ℕ) : ℂ))) + α * (HS N n : ℂ) := by
    unfold HS
    push_cast
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm N i]
    push_cast
    ring
  have hHS : HS N n = (harmonic (n - 1) : ℝ) - harmonic (N - 1) := by
    have := HS_eq (N - 1) (n - 1) (by omega)
    rwa [show N - 1 + 1 = N by omega, show n - 1 + 1 = n by omega] at this
  have hlog : Complex.log ((n : ℂ) + 1) = ((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  rw [hsplit, hHS, hlog]
  push_cast
  ring

end Pfq54.LV
