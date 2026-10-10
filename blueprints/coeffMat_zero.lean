/-
# `ZetasIrr.coeffMat_zero`: the base case `𝓒_0 = 𝓒₀` of (13)

Sorry-free. These results were moved verbatim from `Delta_mul_Rmat_integral.lean`, so that
`det_V_eq.lean` can use `coeffMat_zero` without importing `Delta_mul_Rmat_integral` (which now
imports `valuation_bound`, which imports `det_V_eq`).

`coeffMat_zero` uses the partial-fraction machinery of `cross_product_readout.lean`. At `N = 0`
the kernel is `(-t)^j/(t³(t+1))`, with `1/(t³(t+1)) = t⁻³ - t⁻² + t⁻¹ - (t+1)⁻¹`. The formal
functional `𝓛_0` is evaluated over the pole set `{0, -1}`, where `H^{(s)}_0 = 0` and
`H^{(s)}_1 = 1`.
-/
import cross_product_readout

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr

/-! ### Auxiliary results for `coeffMat_zero` -/

theorem pfCoeff_ppSum_of_not_mem (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) {h : ℚ} (hh : h ∉ R)
    {r : ℕ} (hr : 1 ≤ r) : pfCoeff (ppSum R b c) h r = 0 := by
  unfold ppSum
  rw [pfCoeff_sum]
  refine Finset.sum_eq_zero fun h' hh' => ?_
  rw [pfCoeff_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : h' ≠ h := fun he => hh (he ▸ hh')
  rw [pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hr]
  simp [this]

/-- For a proper `f` whose denominator splits, `𝓛_K[f]` may be computed over any finite set `T`
containing the poles and any order bound `M ≥ deg(denom f)`. -/
theorem Lfun_eq_sum_superset (K : ℤ) (f : ℚ⟮X⟯) (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree) (T : Finset ℚ)
    (hT : f.denom.roots.toFinset ⊆ T) (M : ℕ) (hM : f.denom.natDegree ≤ M) :
    Lfun K f = ∑ h ∈ T, ∑ r ∈ Finset.range (M + 1),
      ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0) := by
  obtain ⟨c, hc⟩ := exists_eq_ppSum f hproper hsplit
  set R := f.denom.roots.toFinset with hR
  set b : ℚ → ℕ := fun h => f.denom.roots.count h with hb
  have hpf : ∀ h ∈ R, ∀ r, 1 ≤ r → pfCoeff f h r = if r ≤ b h then c h r else 0 := by
    intro h hh r hr
    have := pfCoeff_ppSum R b c hh hr
    rwa [← hc] at this
  have hpf' : ∀ h, h ∉ R → ∀ r, 1 ≤ r → pfCoeff f h r = 0 := by
    intro h hh r hr
    have := pfCoeff_ppSum_of_not_mem R b c hh hr
    rwa [← hc] at this
  have hbD : ∀ h, b h ≤ f.denom.natDegree := fun h =>
    (Multiset.count_le_card h _).trans hsplit.le
  unfold Lfun
  rw [polyPart_eq_zero_of_proper f hproper]
  simp only [Polynomial.natDegree_zero, zero_add, Finset.range_one, Finset.sum_singleton,
    Polynomial.coeff_zero, zero_mul, zero_smul]
  calc ∑ h ∈ R, ∑ r ∈ Finset.range (f.denom.natDegree + 1),
        ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0)
      = ∑ h ∈ R, ∑ r ∈ Finset.range (M + 1),
        ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0) := by
        refine Finset.sum_congr rfl fun h hh => ?_
        refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun r hr hr' => ?_
        have hr1 : f.denom.natDegree < r := by
          simp only [Finset.mem_range, not_lt] at hr'; omega
        have : pfCoeff f h r = 0 := by
          rw [hpf h hh r (by omega)]
          have := hbD h
          simp [show ¬ r ≤ b h by omega]
        simp [this]
    _ = _ := by
        refine Finset.sum_subset hT fun h _ hh => Finset.sum_eq_zero fun r _ => ?_
        rcases Nat.eq_zero_or_pos r with rfl | hpos
        · simp
        · simp [hpf' h hh r hpos]

theorem linFormKernel_zero_eq (j : Fin 3) :
    linFormKernel 0 j = (-RatFunc.X) ^ (j : ℕ) *
      ((RatFunc.X - RatFunc.C 0) ^ 3 * (RatFunc.X - RatFunc.C (-1)))⁻¹ := by
  rw [linFormKernel_eq]
  simp only [zeroSet, poleSet, Multiset.range_succ, Multiset.range_zero, Multiset.map_cons,
    Multiset.map_zero, Multiset.map_add, Multiset.prod_add, Multiset.prod_cons, Multiset.prod_zero,
    map_mul, map_pow, map_neg, map_sub, map_one, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    div_eq_mul_inv, Nat.cast_one, mul_zero, add_zero, zero_add, neg_zero,
    CharP.cast_eq_zero, mul_one]
  ring

/-- Partial fractions of `1/(t³(t+1)) = t⁻³ - t⁻² + t⁻¹ - (t+1)⁻¹`. -/
theorem linFormKernel_zero_zero :
    linFormKernel 0 0 =
      RatFunc.C 1 * ((RatFunc.X - RatFunc.C 0) ^ 3)⁻¹ +
        RatFunc.C (-1) * ((RatFunc.X - RatFunc.C 0) ^ 2)⁻¹ +
        RatFunc.C 1 * ((RatFunc.X - RatFunc.C 0) ^ 1)⁻¹ +
        RatFunc.C (-1) * ((RatFunc.X - RatFunc.C (-1)) ^ 1)⁻¹ := by
  rw [linFormKernel_zero_eq]
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  have h1 : (RatFunc.X - RatFunc.C (-1) : ℚ⟮X⟯) ≠ 0 := X_sub_C_ne_zero' (-1)
  simp only [map_zero, sub_zero, map_one, map_neg, Fin.val_zero, pow_zero, one_mul] at h1 ⊢
  field_simp
  ring

/-- Partial fractions of `-t/(t³(t+1)) = -t⁻² + t⁻¹ - (t+1)⁻¹`. -/
theorem linFormKernel_zero_one :
    linFormKernel 0 1 =
      RatFunc.C (-1) * ((RatFunc.X - RatFunc.C 0) ^ 2)⁻¹ +
        RatFunc.C 1 * ((RatFunc.X - RatFunc.C 0) ^ 1)⁻¹ +
        RatFunc.C (-1) * ((RatFunc.X - RatFunc.C (-1)) ^ 1)⁻¹ := by
  rw [linFormKernel_zero_eq]
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  have h1 : (RatFunc.X - RatFunc.C (-1) : ℚ⟮X⟯) ≠ 0 := X_sub_C_ne_zero' (-1)
  simp only [map_zero, sub_zero, map_one, map_neg, Fin.val_one, pow_one] at h1 ⊢
  field_simp
  ring

/-- Partial fractions of `t²/(t³(t+1)) = t⁻¹ - (t+1)⁻¹`. -/
theorem linFormKernel_zero_two :
    linFormKernel 0 2 =
      RatFunc.C 1 * ((RatFunc.X - RatFunc.C 0) ^ 1)⁻¹ +
        RatFunc.C (-1) * ((RatFunc.X - RatFunc.C (-1)) ^ 1)⁻¹ := by
  rw [linFormKernel_zero_eq]
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  have h1 : (RatFunc.X - RatFunc.C (-1) : ℚ⟮X⟯) ≠ 0 := X_sub_C_ne_zero' (-1)
  simp only [map_zero, sub_zero, map_one, map_neg, Fin.val_two, pow_one] at h1 ⊢
  field_simp
  ring

theorem linFormKernel_zero_roots (j : Fin 3) :
    (linFormKernel 0 j).denom.roots.toFinset ⊆ {0, -1} := by
  intro h hh
  have := Multiset.mem_of_le (roots_denom_le 0 j) (Multiset.mem_toFinset.mp hh)
  simp [poleSet, Multiset.range_succ] at this
  rcases this with h0 | h0 <;> simp [h0]

theorem linFormKernel_zero_natDegree (j : Fin 3) : (linFormKernel 0 j).denom.natDegree ≤ 4 := by
  have := Polynomial.natDegree_le_of_dvd (denom_linFormKernel_dvd 0 j) (prod_X_sub_C_ne_zero _)
  rw [natDegree_prod_X_sub_C] at this
  simpa [poleSet] using this

theorem Lfun_zero_eq (j : Fin 3) :
    Lfun 0 (linFormKernel 0 j) = ∑ h ∈ ({0, -1} : Finset ℚ), ∑ r ∈ Finset.range 5,
      ((r : ℚ) * pfCoeff (linFormKernel 0 j) h r) •
        (Zsym (r + 1) - harm (r + 1) ⌊((0 : ℤ) : ℚ) - h⌋ • Zsym 0) :=
  Lfun_eq_sum_superset 0 _ (linFormKernel_proper 0 j) (linFormKernel_split 0 j) _
    (linFormKernel_zero_roots j) 4 (linFormKernel_zero_natDegree j)

theorem pf_zero_zero (h : ℚ) (r : ℕ) (hr : 1 ≤ r) :
    pfCoeff (linFormKernel 0 0) h r =
      (if (0 : ℚ) = h ∧ 3 = r then 1 else 0) - (if (0 : ℚ) = h ∧ 2 = r then 1 else 0) +
        (if (0 : ℚ) = h ∧ 1 = r then 1 else 0) - (if (-1 : ℚ) = h ∧ 1 = r then 1 else 0) := by
  rw [linFormKernel_zero_zero]
  simp only [pfCoeff_add, pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hr]
  ring

theorem pf_zero_one (h : ℚ) (r : ℕ) (hr : 1 ≤ r) :
    pfCoeff (linFormKernel 0 1) h r =
      -(if (0 : ℚ) = h ∧ 2 = r then 1 else 0) + (if (0 : ℚ) = h ∧ 1 = r then 1 else 0) -
        (if (-1 : ℚ) = h ∧ 1 = r then 1 else 0) := by
  rw [linFormKernel_zero_one]
  simp only [pfCoeff_add, pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hr]
  ring

theorem pf_zero_two (h : ℚ) (r : ℕ) (hr : 1 ≤ r) :
    pfCoeff (linFormKernel 0 2) h r =
      (if (0 : ℚ) = h ∧ 1 = r then 1 else 0) - (if (-1 : ℚ) = h ∧ 1 = r then 1 else 0) := by
  rw [linFormKernel_zero_two]
  simp only [pfCoeff_add, pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hr]
  ring

theorem Lfun_zero_zero :
    Lfun 0 (linFormKernel 0 0) = (3 : ℚ) • Zsym 4 + (-2 : ℚ) • Zsym 3 + Zsym 0 := by
  rw [Lfun_zero_eq, Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [pf_zero_zero, harm]
  module

theorem Lfun_zero_one :
    Lfun 0 (linFormKernel 0 1) = (-2 : ℚ) • Zsym 3 + Zsym 0 := by
  rw [Lfun_zero_eq, Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [pf_zero_one, harm]
  module

theorem Lfun_zero_two : Lfun 0 (linFormKernel 0 2) = Zsym 0 := by
  rw [Lfun_zero_eq, Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [pf_zero_two, harm]

/-- **[2] Base case of (13): `𝓒_0 = 𝓒₀`.** The columns of `𝓒_0` are the `(Z₄, Z₃, 1)`
coefficients of `𝓛_0[(-t)^j R_0] = 3Z₄ - 2Z₃ + 1, -2Z₃ + 1, 1`. -/
theorem coeffMat_zero : coeffMat 0 = C0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coeffMat, C0, Lfun_zero_zero, Lfun_zero_one, Lfun_zero_two, Zsym]

end ZetasIrr
