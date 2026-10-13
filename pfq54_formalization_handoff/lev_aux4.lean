/-
# Levinson's dichotomy for `λ_j(n) = ρ_j (1 + α_j/n)` (sorry-free)

For `q_j = λ_j/λ_i` the products `P_j(k,n) = (ρ_j/ρ_i)^{n-k} ∏(1+α_j/m)/∏(1+α_i/m)` are
uniformly bounded and tend to `0` when `|ρ_j| < |ρ_i|` (or `|ρ_j| = |ρ_i|` and
`Re α_j < Re α_i`), and uniformly bounded below otherwise. This packages the data `LevData` of
`lev_aux2.lean` for a system `M(n) = Λ(n) + O(1/n²)`.
-/
import lev_aux3

open Finset Filter Topology

noncomputable section

namespace Pfq54.LV

/-- `λ_j(n) = ρ_j (1 + α_j/n)`. -/
def lamA (ρ α : Fin 3 → ℂ) (j : Fin 3) (n : ℕ) : ℂ := ρ j * (1 + α j / (n : ℂ))

theorem PP_lamA (ρ α : Fin 3 → ℂ) (i j : Fin 3) (k n : ℕ) :
    PP (lamA ρ α) i j k n = (ρ j / ρ i) ^ (n - k) * (prodA (α j) k n / prodA (α i) k n) := by
  unfold PP qq lamA prodA
  rw [← Finset.prod_div_distrib, ← Nat.card_Ico k n, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [mul_div_mul_comm]

/-! ### Elementary real estimates -/

theorem one_le_div_nat (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : 1 ≤ (n : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk', one_mul]
  exact_mod_cast hkn

theorem div_le_one_add_sub (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n : ℝ) / k ≤ 1 + ((n - k : ℕ) : ℝ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_le_iff₀ (by linarith), Nat.cast_sub hkn]
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h2 : ((n : ℝ) - k) * 1 ≤ ((n : ℝ) - k) * k :=
    mul_le_mul_of_nonneg_left hk' (by linarith)
  nlinarith

theorem rpow_div_le (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (β : ℝ) :
    ((n : ℝ) / k) ^ β ≤ (1 + ((n - k : ℕ) : ℝ)) ^ (max β 0) := by
  rcases le_or_gt 0 β with hβ | hβ
  · rw [max_eq_left hβ]
    exact Real.rpow_le_rpow (by positivity) (div_le_one_add_sub k n hk hkn) hβ
  · rw [max_eq_right hβ.le, Real.rpow_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_div_nat k n hk hkn) hβ.le

theorem rpow_div_ge (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (β : ℝ) :
    (1 + ((n - k : ℕ) : ℝ)) ^ (-(max (-β) 0)) ≤ ((n : ℝ) / k) ^ β := by
  have hpos : 0 < (n : ℝ) / k := by
    have := one_le_div_nat k n hk hkn
    linarith
  rcases le_or_gt 0 β with hβ | hβ
  · rw [max_eq_right (by linarith), neg_zero, Real.rpow_zero]
    exact Real.one_le_rpow (one_le_div_nat k n hk hkn) hβ
  · rw [max_eq_left (by linarith : 0 ≤ -β), Real.rpow_neg (by positivity)]
    have e1 : ((n : ℝ) / k) ^ β = (((n : ℝ) / k) ^ (-β))⁻¹ := by
      rw [← Real.rpow_neg hpos.le, neg_neg]
    rw [e1]
    exact inv_anti₀ (by positivity)
      (Real.rpow_le_rpow hpos.le (div_le_one_add_sub k n hk hkn) (by linarith))

theorem geom_poly_tendsto (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (c : ℝ) :
    Tendsto (fun t : ℕ => θ ^ t * (1 + (t : ℝ)) ^ c) atTop (𝓝 0) := by
  have hb : 0 < -Real.log θ := by
    have := Real.log_neg hθ0 hθ1
    linarith
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c (-Real.log θ) hb).comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have h2 := h.mul_const (Real.exp (-Real.log θ))
  rw [zero_mul] at h2
  refine h2.congr fun t => ?_
  simp only [Function.comp]
  rw [mul_assoc, ← Real.exp_add, show -(-Real.log θ) * (1 + (t : ℝ)) + -Real.log θ =
    (t : ℝ) * Real.log θ by ring, Real.exp_nat_mul, Real.exp_log hθ0]
  ring

theorem geom_poly_bound (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (c : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℕ, θ ^ t * (1 + (t : ℝ)) ^ c ≤ B := by
  have h := geom_poly_tendsto θ hθ0 hθ1 c
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ h)
  refine ⟨max B 1, by positivity, fun t => ?_⟩
  have := hB _ (Set.mem_range_self t)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

theorem geom_poly_lower (θ : ℝ) (hθ1 : 1 < θ) (c : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ t : ℕ, b ≤ θ ^ t * (1 + (t : ℝ)) ^ (-c) := by
  obtain ⟨B, hB0, hB⟩ := geom_poly_bound θ⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hθ1) c
  refine ⟨B⁻¹, by positivity, fun t => ?_⟩
  have h := hB t
  rw [inv_pow] at h
  rw [Real.rpow_neg (by positivity),
    show θ ^ t * ((1 + (t : ℝ)) ^ c)⁻¹ = ((θ ^ t)⁻¹ * (1 + (t : ℝ)) ^ c)⁻¹ by
      rw [mul_inv, inv_inv]]
  exact inv_anti₀ (by positivity) h

/-! ### Bounds on `P_j(k,n)` -/

theorem norm_PP_lamA_le (ρ α : Fin 3 → ℂ) (i j : Fin 3) (k n : ℕ) (hki : N₁ (α i) ≤ k)
    (hkj : N₁ (α j) ≤ k) (hkn : k ≤ n) :
    ‖PP (lamA ρ α) i j k n‖ ≤ ‖ρ j / ρ i‖ ^ (n - k) * Real.exp (CA (α j) + CA (α i)) *
      ((n : ℝ) / k) ^ ((α j).re - (α i).re) := by
  rw [PP_lamA, norm_mul, norm_pow, norm_div (prodA (α j) k n) (prodA (α i) k n)]
  obtain ⟨_, hj2⟩ := prodA_bounds (α j) k n hkj hkn
  obtain ⟨hi1, _⟩ := prodA_bounds (α i) k n hki hkn
  have hk1 : 1 ≤ k := (N₁_pos _).trans hki
  have hpos : 0 < ((n : ℝ) / k) :=
    div_pos (by exact_mod_cast (hk1.trans hkn)) (by exact_mod_cast hk1)
  have h := div_le_div₀ (mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hpos _).le) hj2
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hpos _)) hi1
  have e : Real.exp (CA (α j)) * ((n : ℝ) / k) ^ (α j).re /
      (Real.exp (-CA (α i)) * ((n : ℝ) / k) ^ (α i).re) =
      Real.exp (CA (α j) + CA (α i)) * ((n : ℝ) / k) ^ ((α j).re - (α i).re) := by
    rw [Real.rpow_sub hpos, Real.exp_add, Real.exp_neg]
    field_simp
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.trans e.le) (by positivity)

theorem norm_PP_lamA_ge (ρ α : Fin 3 → ℂ) (i j : Fin 3) (k n : ℕ) (hki : N₁ (α i) ≤ k)
    (hkj : N₁ (α j) ≤ k) (hkn : k ≤ n) :
    ‖ρ j / ρ i‖ ^ (n - k) * Real.exp (-(CA (α j) + CA (α i))) *
      ((n : ℝ) / k) ^ ((α j).re - (α i).re) ≤ ‖PP (lamA ρ α) i j k n‖ := by
  rw [PP_lamA, norm_mul, norm_pow, norm_div (prodA (α j) k n) (prodA (α i) k n)]
  obtain ⟨hj1, _⟩ := prodA_bounds (α j) k n hkj hkn
  obtain ⟨hi1, hi2⟩ := prodA_bounds (α i) k n hki hkn
  have hk1 : 1 ≤ k := (N₁_pos _).trans hki
  have hpos : 0 < ((n : ℝ) / k) :=
    div_pos (by exact_mod_cast (hk1.trans hkn)) (by exact_mod_cast hk1)
  have h := div_le_div₀ (norm_nonneg _) hj1
    (lt_of_lt_of_le (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hpos _)) hi1) hi2
  have e : Real.exp (-CA (α j)) * ((n : ℝ) / k) ^ (α j).re /
      (Real.exp (CA (α i)) * ((n : ℝ) / k) ^ (α i).re) =
      Real.exp (-(CA (α j) + CA (α i))) * ((n : ℝ) / k) ^ ((α j).re - (α i).re) := by
    rw [Real.rpow_sub hpos, Real.exp_neg, Real.exp_neg, Real.exp_add]
    have := Real.exp_pos (CA (α j))
    have := Real.exp_pos (CA (α i))
    have := Real.rpow_pos_of_pos hpos (α i).re
    field_simp
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (e.symm.le.trans h) (by positivity)

/-! ### The three regimes -/

theorem rec_bound (ρ α : Fin 3 → ℂ) (hρ : ∀ j, ρ j ≠ 0) (i j : Fin 3)
    (hθ : ‖ρ j / ρ i‖ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → ‖PP (lamA ρ α) i j k n‖ ≤ K) ∧
      ∀ k, max (N₁ (α i)) (N₁ (α j)) ≤ k →
        Tendsto (fun n => PP (lamA ρ α) i j k n) atTop (𝓝 0) := by
  have hθ0 : 0 < ‖ρ j / ρ i‖ := norm_pos_iff.mpr (div_ne_zero (hρ j) (hρ i))
  obtain ⟨B, hB0, hB⟩ := geom_poly_bound _ hθ0 hθ (max ((α j).re - (α i).re) 0)
  have hbound : ∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → ‖PP (lamA ρ α) i j k n‖ ≤
      Real.exp (CA (α j) + CA (α i)) * (‖ρ j / ρ i‖ ^ (n - k) *
        (1 + ((n - k : ℕ) : ℝ)) ^ (max ((α j).re - (α i).re) 0)) := by
    intro k n hk hkn
    have hk1 : 1 ≤ k := (N₁_pos _).trans ((le_max_left _ _).trans hk)
    calc ‖PP (lamA ρ α) i j k n‖ ≤ ‖ρ j / ρ i‖ ^ (n - k) * Real.exp (CA (α j) + CA (α i)) *
          ((n : ℝ) / k) ^ ((α j).re - (α i).re) :=
          norm_PP_lamA_le ρ α i j k n ((le_max_left _ _).trans hk) ((le_max_right _ _).trans hk) hkn
      _ ≤ ‖ρ j / ρ i‖ ^ (n - k) * Real.exp (CA (α j) + CA (α i)) *
          (1 + ((n - k : ℕ) : ℝ)) ^ (max ((α j).re - (α i).re) 0) :=
          mul_le_mul_of_nonneg_left (rpow_div_le k n hk1 hkn _) (by positivity)
      _ = _ := by ring
  refine ⟨Real.exp (CA (α j) + CA (α i)) * B, by positivity, fun k n hk hkn =>
    (hbound k n hk hkn).trans (mul_le_mul_of_nonneg_left (hB _) (by positivity)), fun k hk => ?_⟩
  refine squeeze_zero_norm' (a := fun n => Real.exp (CA (α j) + CA (α i)) *
    (‖ρ j / ρ i‖ ^ (n - k) * (1 + ((n - k : ℕ) : ℝ)) ^ (max ((α j).re - (α i).re) 0))) ?_ ?_
  · filter_upwards [eventually_ge_atTop k] with n hn
    exact hbound k n hk hn
  · have h := ((geom_poly_tendsto _ hθ0 hθ (max ((α j).re - (α i).re) 0)).comp
      (tendsto_sub_atTop_nat k)).const_mul (Real.exp (CA (α j) + CA (α i)))
    rw [mul_zero] at h
    exact h

theorem rec_bound' (ρ α : Fin 3 → ℂ) (i j : Fin 3) (hθ : ‖ρ j / ρ i‖ = 1)
    (hβ : (α j).re - (α i).re < 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → ‖PP (lamA ρ α) i j k n‖ ≤ K) ∧
      ∀ k, max (N₁ (α i)) (N₁ (α j)) ≤ k →
        Tendsto (fun n => PP (lamA ρ α) i j k n) atTop (𝓝 0) := by
  have hbound : ∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → ‖PP (lamA ρ α) i j k n‖ ≤
      Real.exp (CA (α j) + CA (α i)) * ((n : ℝ) / k) ^ ((α j).re - (α i).re) := by
    intro k n hk hkn
    have h := norm_PP_lamA_le ρ α i j k n ((le_max_left _ _).trans hk)
      ((le_max_right _ _).trans hk) hkn
    rwa [hθ, one_pow, one_mul] at h
  refine ⟨Real.exp (CA (α j) + CA (α i)), by positivity, fun k n hk hkn => ?_, fun k hk => ?_⟩
  · have hk1 : 1 ≤ k := (N₁_pos _).trans ((le_max_left _ _).trans hk)
    refine (hbound k n hk hkn).trans ?_
    calc Real.exp (CA (α j) + CA (α i)) * ((n : ℝ) / k) ^ ((α j).re - (α i).re)
        ≤ Real.exp (CA (α j) + CA (α i)) * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (one_le_div_nat k n hk1 hkn) hβ.le) (by positivity)
      _ = _ := mul_one _
  · have hk1 : 1 ≤ k := (N₁_pos _).trans ((le_max_left _ _).trans hk)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    refine squeeze_zero_norm' (a := fun n : ℕ => Real.exp (CA (α j) + CA (α i)) *
      ((n : ℝ) / k) ^ ((α j).re - (α i).re)) ?_ ?_
    · filter_upwards [eventually_ge_atTop k] with n hn
      exact hbound k n hk hn
    · have h := ((tendsto_rpow_neg_atTop (y := -((α j).re - (α i).re)) (by linarith)).comp
        (tendsto_natCast_atTop_atTop.atTop_div_const hkpos)).const_mul
        (Real.exp (CA (α j) + CA (α i)))
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      simp only [Function.comp, neg_neg]

theorem dom_bound (ρ α : Fin 3 → ℂ) (hρ : ∀ j, ρ j ≠ 0) (i j : Fin 3)
    (h : 1 < ‖ρ j / ρ i‖ ∨ (‖ρ j / ρ i‖ = 1 ∧ 0 ≤ (α j).re - (α i).re)) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → 1 ≤ K * ‖PP (lamA ρ α) i j k n‖ := by
  have hlow : ∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n →
      ‖ρ j / ρ i‖ ^ (n - k) * Real.exp (-(CA (α j) + CA (α i))) *
        (1 + ((n - k : ℕ) : ℝ)) ^ (-(max (-((α j).re - (α i).re)) 0)) ≤
        ‖PP (lamA ρ α) i j k n‖ := by
    intro k n hk hkn
    have hk1 : 1 ≤ k := (N₁_pos _).trans ((le_max_left _ _).trans hk)
    refine le_trans ?_ (norm_PP_lamA_ge ρ α i j k n ((le_max_left _ _).trans hk)
      ((le_max_right _ _).trans hk) hkn)
    exact mul_le_mul_of_nonneg_left (rpow_div_ge k n hk1 hkn _) (by positivity)
  rcases h with hθ | ⟨hθ, hβ⟩
  · obtain ⟨b, hb0, hb⟩ := geom_poly_lower _ hθ (max (-((α j).re - (α i).re)) 0)
    refine ⟨max 1 (Real.exp (CA (α j) + CA (α i)) / b), le_max_left _ _, fun k n hk hkn => ?_⟩
    have h1 : Real.exp (-(CA (α j) + CA (α i))) * b ≤ ‖PP (lamA ρ α) i j k n‖ := by
      refine le_trans ?_ (hlow k n hk hkn)
      calc Real.exp (-(CA (α j) + CA (α i))) * b
          ≤ Real.exp (-(CA (α j) + CA (α i))) * (‖ρ j / ρ i‖ ^ (n - k) *
            (1 + ((n - k : ℕ) : ℝ)) ^ (-(max (-((α j).re - (α i).re)) 0))) :=
            mul_le_mul_of_nonneg_left (hb _) (by positivity)
        _ = _ := by ring
    calc (1 : ℝ) = (Real.exp (CA (α j) + CA (α i)) / b) *
          (Real.exp (-(CA (α j) + CA (α i))) * b) := by
          rw [Real.exp_neg]; field_simp
      _ ≤ (Real.exp (CA (α j) + CA (α i)) / b) * ‖PP (lamA ρ α) i j k n‖ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ max 1 (Real.exp (CA (α j) + CA (α i)) / b) * ‖PP (lamA ρ α) i j k n‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · refine ⟨max 1 (Real.exp (CA (α j) + CA (α i))), le_max_left _ _, fun k n hk hkn => ?_⟩
    have h1 : Real.exp (-(CA (α j) + CA (α i))) ≤ ‖PP (lamA ρ α) i j k n‖ := by
      refine le_trans ?_ (hlow k n hk hkn)
      rw [hθ, one_pow, one_mul, show max (-((α j).re - (α i).re)) 0 = 0 from
        max_eq_right (by linarith), neg_zero, Real.rpow_zero, mul_one]
    calc (1 : ℝ) = Real.exp (CA (α j) + CA (α i)) * Real.exp (-(CA (α j) + CA (α i))) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ ≤ Real.exp (CA (α j) + CA (α i)) * ‖PP (lamA ρ α) i j k n‖ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ max 1 (Real.exp (CA (α j) + CA (α i))) * ‖PP (lamA ρ α) i j k n‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-! ### The Levinson data -/

theorem lamA_ne_zero (ρ α : Fin 3 → ℂ) (hρ : ∀ j, ρ j ≠ 0) (j : Fin 3) (n : ℕ)
    (hn : N₁ (α j) ≤ n) : lamA ρ α j n ≠ 0 :=
  mul_ne_zero (hρ j) (one_add_div_ne_zero (α j) n hn)

theorem norm_lamA_ge (ρ α : Fin 3 → ℂ) (j : Fin 3) (n : ℕ) (hn : N₁ (α j) ≤ n) :
    ‖ρ j‖ / 2 ≤ ‖lamA ρ α j n‖ := by
  unfold lamA
  rw [norm_mul]
  have h1 := norm_div_le_half (α j) n hn
  have h2 : 1 / 2 ≤ ‖1 + α j / (n : ℂ)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(α j / (n : ℂ)))
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  calc ‖ρ j‖ / 2 = ‖ρ j‖ * (1 / 2) := by ring
    _ ≤ ‖ρ j‖ * ‖1 + α j / (n : ℂ)‖ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem per_index (ρ α : Fin 3 → ℂ) (hρ : ∀ j, ρ j ≠ 0) (i j : Fin 3) :
    ∃ K : ℝ, 1 ≤ K ∧
      ((‖ρ j / ρ i‖ < 1 ∨ (‖ρ j / ρ i‖ = 1 ∧ (α j).re - (α i).re < 0)) →
        (∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → ‖PP (lamA ρ α) i j k n‖ ≤ K) ∧
        ∀ k, max (N₁ (α i)) (N₁ (α j)) ≤ k →
          Tendsto (fun n => PP (lamA ρ α) i j k n) atTop (𝓝 0)) ∧
      (¬ (‖ρ j / ρ i‖ < 1 ∨ (‖ρ j / ρ i‖ = 1 ∧ (α j).re - (α i).re < 0)) →
        ∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → 1 ≤ K * ‖PP (lamA ρ α) i j k n‖) := by
  by_cases h : ‖ρ j / ρ i‖ < 1 ∨ (‖ρ j / ρ i‖ = 1 ∧ (α j).re - (α i).re < 0)
  · have hex : ∃ K : ℝ, 0 ≤ K ∧
        (∀ k n, max (N₁ (α i)) (N₁ (α j)) ≤ k → k ≤ n → ‖PP (lamA ρ α) i j k n‖ ≤ K) ∧
        ∀ k, max (N₁ (α i)) (N₁ (α j)) ≤ k →
          Tendsto (fun n => PP (lamA ρ α) i j k n) atTop (𝓝 0) := by
      rcases h with h | ⟨h1, h2⟩
      · exact rec_bound ρ α hρ i j h
      · exact rec_bound' ρ α i j h1 h2
    obtain ⟨K, hK0, hK1, hK2⟩ := hex
    refine ⟨max 1 K, le_max_left _ _, fun _ => ⟨fun k n hk hkn =>
      (hK1 k n hk hkn).trans (le_max_right _ _), hK2⟩, fun h' => absurd h h'⟩
  · have h' : 1 < ‖ρ j / ρ i‖ ∨ (‖ρ j / ρ i‖ = 1 ∧ 0 ≤ (α j).re - (α i).re) := by
      rw [not_or, not_lt, not_and_or, not_lt] at h
      rcases lt_or_eq_of_le h.1 with h1 | h1
      · exact Or.inl h1
      · rcases h.2 with h2 | h2
        · exact absurd h1.symm h2
        · exact Or.inr ⟨h1.symm, h2⟩
    obtain ⟨K, hK1, hK⟩ := dom_bound ρ α hρ i j h'
    exact ⟨K, hK1, fun h'' => absurd h'' h, fun _ => hK⟩

/-- **The Levinson data** for `M(n) = Λ(n) + O(1/n²)`, `Λ(n) = diag(ρ_j(1+α_j/n))`. -/
theorem exists_levData (ρ α : Fin 3 → ℂ) (hρ : ∀ j, ρ j ≠ 0) (i : Fin 3)
    (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (K₂ : ℝ) (hK₂ : 0 ≤ K₂) (n₀ : ℕ)
    (hM : ∀ n, n₀ ≤ n → nrm (RR M (lamA ρ α) n) ≤ K₂ / (n : ℝ) ^ 2) :
    ∃ (rec : Fin 3 → Bool) (N₀ : ℕ) (K : ℝ) (r : ℕ → ℝ), LevData M (lamA ρ α) i rec N₀ K r := by
  classical
  choose Kf hKf using per_index ρ α hρ i
  refine ⟨fun j => decide (‖ρ j / ρ i‖ < 1 ∨ (‖ρ j / ρ i‖ = 1 ∧ (α j).re - (α i).re < 0)),
    n₀ + 1 + N₁ (α i) + N₁ (α 0) + N₁ (α 1) + N₁ (α 2),
    max (max (Kf 0) (Kf 1)) (Kf 2), fun n => (2 * K₂ / ‖ρ i‖) * (1 / (n : ℝ) ^ 2), ?_⟩
  have hKj : ∀ j, Kf j ≤ max (max (Kf 0) (Kf 1)) (Kf 2) := by
    intro j
    fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  have hN₁ : ∀ j, N₁ (α j) ≤ n₀ + 1 + N₁ (α i) + N₁ (α 0) + N₁ (α 1) + N₁ (α 2) := by
    intro j
    fin_cases j
    · show N₁ (α 0) ≤ _; omega
    · show N₁ (α 1) ≤ _; omega
    · show N₁ (α 2) ≤ _; omega
  have hmax : ∀ j, max (N₁ (α i)) (N₁ (α j)) ≤
      n₀ + 1 + N₁ (α i) + N₁ (α 0) + N₁ (α 1) + N₁ (α 2) := fun j =>
    max_le (by omega) (hN₁ j)
  have hρi : 0 < ‖ρ i‖ := norm_pos_iff.mpr (hρ i)
  refine ⟨(hKf 0).1.trans (hKj 0), fun j n hn => lamA_ne_zero ρ α hρ j n ((hN₁ j).trans hn),
    fun j hj k n hk hkn => ?_, fun j hj k hk => ?_, fun j hj k n hk hkn => ?_,
    fun n => by positivity, ?_, fun n hn => ?_⟩
  · rw [decide_eq_true_iff] at hj
    exact (((hKf j).2.1 hj).1 k n ((hmax j).trans hk) hkn).trans (hKj j)
  · rw [decide_eq_true_iff] at hj
    exact ((hKf j).2.1 hj).2 k ((hmax j).trans hk)
  · rw [decide_eq_false_iff_not] at hj
    exact ((hKf j).2.2 hj k n ((hmax j).trans hk) hkn).trans
      (mul_le_mul_of_nonneg_right (hKj j) (norm_nonneg _))
  · exact (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  · have h1 := hM n (by omega)
    have h2 := norm_lamA_ge ρ α i n (by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc nrm (RR M (lamA ρ α) n) ≤ K₂ / (n : ℝ) ^ 2 := h1
      _ = (2 * K₂ / ‖ρ i‖) * (1 / (n : ℝ) ^ 2) * (‖ρ i‖ / 2) := by field_simp
      _ ≤ (2 * K₂ / ‖ρ i‖) * (1 / (n : ℝ) ^ 2) * ‖lamA ρ α i n‖ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

end Pfq54.LV
