/-
# Auxiliary lemma for `meijerG_decay.lean` (sorry-free)

The exact factorial ratio `𝔡_{n+1}/𝔡_n ≤ η`.
-/
import Pfq54_aux

noncomputable section

namespace Pfq54.MD

open Pfq54

/-- `𝔡_{n+1} ≤ η 𝔡_n` for `n ≥ 2`. -/
theorem dfrak_ratio' (n : ℕ) (hn : 2 ≤ n) : dfrak (n + 1) ≤ eta * dfrak n := by
  have e16 : ((16 * (n + 1)).factorial : ℝ) = ((16 * n).factorial : ℝ) * ((16 * n + 1).ascFactorial 16 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 16 * (n + 1) = 16 * n + 16 by omega]
  have e15 : ((15 * (n + 1)).factorial : ℝ) = ((15 * n).factorial : ℝ) * ((15 * n + 1).ascFactorial 15 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 15 * (n + 1) = 15 * n + 15 by omega]
  have e2 : ((2 * (n + 1) - 1).factorial : ℝ) = ((2 * n - 1).factorial : ℝ) * ((2 * n - 1 + 1).ascFactorial 2 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 2 * (n + 1) - 1 = 2 * n - 1 + 2 by omega]
  have e3 : ((3 * (n + 1) - 1).factorial : ℝ) = ((3 * n - 1).factorial : ℝ) * ((3 * n - 1 + 1).ascFactorial 3 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 3 * (n + 1) - 1 = 3 * n - 1 + 3 by omega]
  have e4 : ((4 * (n + 1) - 1).factorial : ℝ) = ((4 * n - 1).factorial : ℝ) * ((4 * n - 1 + 1).ascFactorial 4 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 4 * (n + 1) - 1 = 4 * n - 1 + 4 by omega]
  have e13 : ((13 * (n + 1)).factorial : ℝ) = ((13 * n).factorial : ℝ) * ((13 * n + 1).ascFactorial 13 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 13 * (n + 1) = 13 * n + 13 by omega]
  have e12 : ((12 * (n + 1) + 1).factorial : ℝ) = ((12 * n + 1).factorial : ℝ) * ((12 * n + 1 + 1).ascFactorial 12 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 12 * (n + 1) + 1 = 12 * n + 1 + 12 by omega]
  have e30 : ((30 * (n + 1) + 1).factorial : ℝ) = ((30 * n + 1).factorial : ℝ) * ((30 * n + 1 + 1).ascFactorial 30 : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, show 30 * (n + 1) + 1 = 30 * n + 1 + 30 by omega]
  have hr : (2 * ((n : ℝ) + 1)) ^ 55 ≤ (3 * (n : ℝ)) ^ 55 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hnR]) 55
  set a16 := (16 * n + 1).ascFactorial 16
  set a15 := (15 * n + 1).ascFactorial 15
  set a2 := (2 * n - 1 + 1).ascFactorial 2
  set a3 := (3 * n - 1 + 1).ascFactorial 3
  set a4 := (4 * n - 1 + 1).ascFactorial 4
  set b13 := (13 * n + 1).ascFactorial 13
  set b12 := (12 * n + 1 + 1).ascFactorial 12
  set b30 := (30 * n + 1 + 1).ascFactorial 30
  have hA : a16 * a15 ^ 2 * a2 * a3 * a4 ≤ (16 * (n + 1)) ^ 16 * ((15 * (n + 1)) ^ 15) ^ 2 *
      (2 * (n + 1)) ^ 2 * (3 * (n + 1)) ^ 3 * (4 * (n + 1)) ^ 4 := by
    have u16 : a16 ≤ (16 * (n + 1)) ^ 16 :=
      (Nat.ascFactorial_le_pow_add _ 16).trans (Nat.pow_le_pow_left (by omega) 16)
    have u15 : a15 ≤ (15 * (n + 1)) ^ 15 :=
      (Nat.ascFactorial_le_pow_add _ 15).trans (Nat.pow_le_pow_left (by omega) 15)
    have u2 : a2 ≤ (2 * (n + 1)) ^ 2 :=
      (Nat.ascFactorial_le_pow_add _ 2).trans (Nat.pow_le_pow_left (by omega) 2)
    have u3 : a3 ≤ (3 * (n + 1)) ^ 3 :=
      (Nat.ascFactorial_le_pow_add _ 3).trans (Nat.pow_le_pow_left (by omega) 3)
    have u4 : a4 ≤ (4 * (n + 1)) ^ 4 :=
      (Nat.ascFactorial_le_pow_add _ 4).trans (Nat.pow_le_pow_left (by omega) 4)
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul u16
      (Nat.pow_le_pow_left u15 2)) u2) u3) u4
  have hB : (13 * n) ^ 13 * (12 * n) ^ 12 * (30 * n) ^ 30 ≤ b13 * b12 * b30 := by
    have l13 : (13 * n) ^ 13 ≤ b13 :=
      (Nat.pow_le_pow_left (by omega) 13).trans (Nat.pow_succ_le_ascFactorial _ 13)
    have l12 : (12 * n) ^ 12 ≤ b12 :=
      (Nat.pow_le_pow_left (by omega) 12).trans (Nat.pow_succ_le_ascFactorial _ 12)
    have l30 : (30 * n) ^ 30 ≤ b30 :=
      (Nat.pow_le_pow_left (by omega) 30).trans (Nat.pow_succ_le_ascFactorial _ 30)
    exact Nat.mul_le_mul (Nat.mul_le_mul l13 l12) l30
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) + 1 with hm
  have hAR : (a16 : ℝ) * (a15 : ℝ) ^ 2 * a2 * a3 * a4 ≤
      16 ^ 16 * 15 ^ 30 * 2 ^ 2 * 3 ^ 3 * 4 ^ 4 * m ^ 55 := by
    have := (Nat.cast_le (α := ℝ)).mpr hA
    push_cast at this
    rw [← hm] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hBR : 13 ^ 13 * 12 ^ 12 * 30 ^ 30 * (n : ℝ) ^ 55 ≤ (b13 : ℝ) * b12 * b30 := by
    have := (Nat.cast_le (α := ℝ)).mpr hB
    push_cast at this
    calc _ = _ := by ring
      _ ≤ _ := this
  have hBpos : (0 : ℝ) < (b13 : ℝ) * b12 * b30 := lt_of_lt_of_le (by positivity) hBR
  have key : (a16 : ℝ) * (a15 : ℝ) ^ 2 * a2 * a3 * a4 ≤ eta * ((b13 : ℝ) * b12 * b30) := by
    calc _ ≤ 16 ^ 16 * 15 ^ 30 * 2 ^ 2 * 3 ^ 3 * 4 ^ 4 * m ^ 55 := hAR
      _ = 16 ^ 16 * 15 ^ 30 * 2 ^ 2 * 3 ^ 3 * 4 ^ 4 / 2 ^ 55 * (2 * m) ^ 55 := by ring
      _ ≤ 16 ^ 16 * 15 ^ 30 * 2 ^ 2 * 3 ^ 3 * 4 ^ 4 / 2 ^ 55 * (3 * (n : ℝ)) ^ 55 :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = eta * (13 ^ 13 * 12 ^ 12 * 30 ^ 30 * (n : ℝ) ^ 55) := by unfold eta; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBR (by unfold eta; positivity)
  have hdf : dfrak (n + 1) = dfrak n * ((a16 : ℝ) * (a15 : ℝ) ^ 2 * a2 * a3 * a4 /
      ((b13 : ℝ) * b12 * b30)) := by
    unfold dfrak
    simp only [e16, e15, e2, e3, e4, e13, e12, e30]
    rw [div_mul_div_comm]
    exact congrArg₂ HDiv.hDiv (by ring) (by ring)
  rw [hdf]
  calc dfrak n * ((a16 : ℝ) * (a15 : ℝ) ^ 2 * a2 * a3 * a4 / ((b13 : ℝ) * b12 * b30))
      ≤ dfrak n * eta := by
        refine mul_le_mul_of_nonneg_left ((div_le_iff₀ hBpos).mpr key) ?_
        unfold dfrak; positivity
    _ = eta * dfrak n := mul_comm _ _


end Pfq54.MD
