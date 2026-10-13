/-
# An entrywise norm on `3 × 3` complex matrices (sorry-free)

`nrm M = ∑ ‖M i j‖` is submultiplicative, dominates every entry and every row/column sum, and
controls convergence in the product topology. Used by the Levinson argument of `lev_aux2.lean`.
-/
import Pfq54_aux

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.LV

/-- The sum of the entry norms. -/
def nrm (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem nrm_nonneg (M : Matrix (Fin 3) (Fin 3) ℂ) : 0 ≤ nrm M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem row_sum_le_nrm (M : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) : ∑ j, ‖M i j‖ ≤ nrm M :=
  Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem col_sum_le_nrm (M : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) : ∑ i, ‖M i j‖ ≤ nrm M := by
  unfold nrm
  rw [Finset.sum_comm]
  exact Finset.single_le_sum (f := fun j => ∑ i, ‖M i j‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem entry_le_nrm (M : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) : ‖M i j‖ ≤ nrm M :=
  (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (row_sum_le_nrm M i)

theorem nrm_le_of_entries (M : Matrix (Fin 3) (Fin 3) ℂ) (c : ℝ) (h : ∀ i j, ‖M i j‖ ≤ c) :
    nrm M ≤ 9 * c := by
  unfold nrm
  calc ∑ i, ∑ j, ‖M i j‖ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 9 * c := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                    push_cast; ring

theorem nrm_add_le (A B : Matrix (Fin 3) (Fin 3) ℂ) : nrm (A + B) ≤ nrm A + nrm B := by
  unfold nrm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem nrm_neg (A : Matrix (Fin 3) (Fin 3) ℂ) : nrm (-A) = nrm A := by
  unfold nrm
  simp only [Matrix.neg_apply, norm_neg]

theorem nrm_sub_le (A B : Matrix (Fin 3) (Fin 3) ℂ) : nrm (A - B) ≤ nrm A + nrm B := by
  rw [sub_eq_add_neg]
  exact (nrm_add_le _ _).trans (by rw [nrm_neg])

theorem nrm_smul (c : ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) : nrm (c • A) = ‖c‖ * nrm A := by
  unfold nrm
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Finset.mul_sum]

theorem nrm_zero : nrm (0 : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
  unfold nrm
  simp

theorem nrm_mul_le (A B : Matrix (Fin 3) (Fin 3) ℂ) : nrm (A * B) ≤ nrm A * nrm B := by
  unfold nrm
  calc ∑ i, ∑ k, ‖(A * B) i k‖ ≤ ∑ i, ∑ k, ∑ j, ‖A i j‖ * ‖B j k‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ = ∑ i, ∑ j, ‖A i j‖ * ∑ k, ‖B j k‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ∑ j', ∑ k, ‖B j' k‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (row_sum_le_nrm B j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖A i j‖) * ∑ j, ∑ k, ‖B j k‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

theorem norm_vecMul_le (v : Fin 3 → ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    ‖v ᵥ* M‖ ≤ ‖v‖ * nrm M := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (nrm_nonneg _))]
  intro j
  rw [Matrix.vecMul, dotProduct]
  calc ‖∑ i, v i * M i j‖ ≤ ∑ i, ‖v i‖ * ‖M i j‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ i, ‖v‖ * ‖M i j‖ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _)
    _ = ‖v‖ * ∑ i, ‖M i j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖v‖ * nrm M := mul_le_mul_of_nonneg_left (col_sum_le_nrm M j) (norm_nonneg _)

theorem norm_single_le (i : Fin 3) : ‖(Pi.single i (1 : ℂ) : Fin 3 → ℂ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem tendsto_of_nrm {M : ℕ → Matrix (Fin 3) (Fin 3) ℂ} {L : Matrix (Fin 3) (Fin 3) ℂ}
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0)) (h : ∀ᶠ n in atTop, nrm (M n - L) ≤ b n) :
    Tendsto M atTop (𝓝 L) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [h] with n hn
  rw [norm_norm]
  exact (entry_le_nrm (M n - L) i j).trans hn

theorem nrm_tendsto_zero_of_tendsto {M : ℕ → Matrix (Fin 3) (Fin 3) ℂ} {L : Matrix (Fin 3) (Fin 3) ℂ}
    (h : Tendsto M atTop (𝓝 L)) : Tendsto (fun n => nrm (M n - L)) atTop (𝓝 0) := by
  have : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ‖(M n - L) i j‖) atTop
      (𝓝 (∑ i : Fin 3, ∑ j : Fin 3, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have h1 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp h1)
    exact h2
  rw [show (∑ _i : Fin 3, ∑ _j : Fin 3, (0 : ℝ)) = 0 by simp] at this
  exact this

end Pfq54.LV
