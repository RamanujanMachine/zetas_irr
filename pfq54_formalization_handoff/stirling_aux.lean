/-
# The termwise Stirling bound (sorry-free)

`log U_{n,j} ≤ n (30 log(3/2) + g(j/n)) + C log(n+1)` for `2n ≤ j ≤ 16n`: the `m log m`
terms combine to `n g(j/n)`, the `n log n` and linear Stirling terms cancel.
-/
import jet_aux
import log_Z0_aux
import growth_estimates

open Finset

noncomputable section

namespace Pfq54.ST

open Pfq54

/-- Stirling bounds for all `m ≥ 0`. -/
theorem lf (m : ℕ) : (m : ℝ) * Real.log m - m ≤ Real.log m.factorial ∧
    Real.log m.factorial ≤ m * Real.log m - m + 1 + Real.log m / 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, Real.log_zero, mul_zero,
      sub_zero]
    exact ⟨le_rfl, by norm_num⟩
  · have h := ZetasIrr.BP.fact_bounds 1 m le_rfl hm
    simpa using h

theorem logC (N M : ℕ) (h : M ≤ N) : Real.log (N.choose M : ℝ) =
    Real.log N.factorial - Real.log M.factorial - Real.log (N - M).factorial := by
  have key : (N.choose M : ℝ) * M.factorial * (N - M).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have h1 : (0 : ℝ) < N.choose M := by exact_mod_cast Nat.choose_pos h
  have h2 : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have h3 : (0 : ℝ) < (N - M).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [← key, Real.log_mul (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
  ring

/-- `m log m = n · (t log t) + m log n` for `m = n t`. -/
theorem mlog (n : ℝ) (hn : 0 < n) (m : ℕ) (t : ℝ) (hm : (m : ℝ) = n * t) :
    (m : ℝ) * Real.log m = n * LZ.xl t + m * Real.log n := by
  have ht : 0 ≤ t := by
    have : (0 : ℝ) ≤ n * t := hm ▸ Nat.cast_nonneg m
    exact nonneg_of_mul_nonneg_right (by linarith) hn
  rcases ht.lt_or_eq with ht | rfl
  · rw [hm, Real.log_mul hn.ne' ht.ne']
    unfold LZ.xl
    ring
  · rw [mul_zero] at hm
    rw [hm, zero_mul, zero_mul, add_zero]
    unfold LZ.xl
    rw [zero_mul, mul_zero]

theorem log_le29 (n N : ℕ) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 29 * n) :
    Real.log N ≤ Real.log 29 + Real.log ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.log N ≤ Real.log (29 * n) :=
        Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast hN)
    _ = Real.log 29 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
    _ ≤ _ := by gcongr; linarith

/-- **The termwise Stirling bound.** -/
theorem term_stirling' : ∃ C : ℝ, ∀ n j : ℕ, 1 ≤ n → 2 * n ≤ j → j ≤ 16 * n → 0 < U n j →
    Real.log (U n j : ℝ) ≤
      n * (30 * Real.log (3 / 2) + LZ.gA ((j : ℝ) / n)) + C * Real.log (n + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(5 + 5 / 2 * Real.log 29) / Real.log 2 + 5 / 2, fun n j hn h1 h2 _ => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnl : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by
      have h : (1 : ℝ) ≤ n := (by exact_mod_cast hn)
      linarith)
  have hJ : U n j = RA.Cu n j * ((15 * n).choose (j - n) : ℚ) *
      ((15 * n).choose (j - 2 * n) : ℚ) := by
    have h : coeffJet n j = jet (RA.Cu n j * ((15 * n).choose (j - n) : ℚ) *
        ((15 * n).choose (j - 2 * n) : ℚ))
        (RA.Cu n j * ((15 * n).choose (j - n) : ℚ) * ((15 * n).choose (j - 2 * n) : ℚ) *
          (RA.Xu n j + (harm 1 (j - n) - harm 1 (15 * n - (j - n))) +
            (harm 1 (j - 2 * n) - harm 1 (15 * n - (j - 2 * n))))) := by
      unfold coeffJet
      rw [RA.upper_jets, show (j : ℤ) - n = ((j - n : ℕ) : ℤ) by omega,
        show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
        RA.lowerJet_log (15 * n) (j - n) (by omega), RA.lowerJet_log (15 * n) (j - 2 * n) (by omega),
        RA.jet_mul_log, RA.jet_mul_log]
    rw [U, h, Aux.jet_fst]
  have pc : ∀ N M : ℕ, M ≤ N → (0 : ℝ) < N.choose M := fun N M h => by
    exact_mod_cast Nat.choose_pos h
  rw [hJ, Rat.cast_mul, Rat.cast_mul]
  unfold RA.Cu
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast, Rat.cast_natCast,
    Rat.cast_natCast, Rat.cast_natCast,
    Real.log_mul (mul_pos (mul_pos (mul_pos (pc _ _ (by omega)) (pc _ _ (by omega)))
      (pc _ _ (by omega))) (pc _ _ (by omega))).ne' (pc _ _ (by omega)).ne',
    Real.log_mul (mul_pos (mul_pos (pc _ _ (by omega)) (pc _ _ (by omega)))
      (pc _ _ (by omega))).ne' (pc _ _ (by omega)).ne',
    Real.log_mul (mul_pos (pc _ _ (by omega)) (pc _ _ (by omega))).ne' (pc _ _ (by omega)).ne',
    Real.log_mul (pc _ _ (by omega)).ne' (pc _ _ (by omega)).ne',
    logC _ _ (by omega), logC _ _ (by omega), logC _ _ (by omega), logC _ _ (by omega),
    logC _ _ (by omega), show j + 10 * n - 10 * n = j by omega,
    show j + 11 * n - 10 * n = j + n by omega, show j + 12 * n - 10 * n = j + 2 * n by omega,
    show 15 * n - (j - n) = 16 * n - j by omega, show 15 * n - (j - 2 * n) = 17 * n - j by omega]
  set y : ℝ := (j : ℝ) / n
  have hy : (j : ℝ) = n * y := by rw [mul_div_cancel₀ _ hn0.ne']
  have e1 := mlog n hn0 (j + 10 * n) (y + 10) (by push_cast; rw [hy]; ring)
  have e2 := mlog n hn0 (j + 11 * n) (y + 11) (by push_cast; rw [hy]; ring)
  have e3 := mlog n hn0 (j + 12 * n) (y + 12) (by push_cast; rw [hy]; ring)
  have e4 := mlog n hn0 (15 * n) 15 (by push_cast; ring)
  have e5 := mlog n hn0 (10 * n) 10 (by push_cast; ring)
  have e6 := mlog n hn0 j y hy
  have e7 := mlog n hn0 (j + n) (y + 1) (by push_cast; rw [hy]; ring)
  have e8 := mlog n hn0 (j + 2 * n) (y + 2) (by push_cast; rw [hy]; ring)
  have e9 := mlog n hn0 (j - n) (y - 1) (by rw [Nat.cast_sub (by omega), hy]; ring)
  have e10 := mlog n hn0 (16 * n - j) (16 - y) (by rw [Nat.cast_sub (by omega), hy]; push_cast; ring)
  have e11 := mlog n hn0 (j - 2 * n) (y - 2) (by rw [Nat.cast_sub (by omega), hy]; push_cast; ring)
  have e12 := mlog n hn0 (17 * n - j) (17 - y) (by rw [Nat.cast_sub (by omega), hy]; push_cast; ring)
  have c9 : ((j - n : ℕ) : ℝ) = j - n := Nat.cast_sub (by omega)
  have c10 : ((16 * n - j : ℕ) : ℝ) = 16 * n - j := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c11 : ((j - 2 * n : ℕ) : ℝ) = j - 2 * n := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c12 : ((17 * n - j : ℕ) : ℝ) = 17 * n - j := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c1 : ((j + 10 * n : ℕ) : ℝ) = j + 10 * n := by push_cast; ring
  have c2 : ((j + 11 * n : ℕ) : ℝ) = j + 11 * n := by push_cast; ring
  have c3 : ((j + 12 * n : ℕ) : ℝ) = j + 12 * n := by push_cast; ring
  have c4 : ((15 * n : ℕ) : ℝ) = 15 * n := by push_cast; ring
  have c5 : ((10 * n : ℕ) : ℝ) = 10 * n := by push_cast; ring
  have c7 : ((j + n : ℕ) : ℝ) = j + n := by push_cast; ring
  have c8 : ((j + 2 * n : ℕ) : ℝ) = j + 2 * n := by push_cast; ring
  have hsum : ((((j + 10 * n : ℕ) : ℝ) + ((j + 11 * n : ℕ) : ℝ) + ((j + 12 * n : ℕ) : ℝ) +
      ((15 * n : ℕ) : ℝ) + ((15 * n : ℕ) : ℝ) - 3 * ((10 * n : ℕ) : ℝ) - (j : ℝ) -
      ((j + n : ℕ) : ℝ) - ((j + 2 * n : ℕ) : ℝ) - ((j - n : ℕ) : ℝ) - ((16 * n - j : ℕ) : ℝ) -
      ((j - 2 * n : ℕ) : ℝ) - ((17 * n - j : ℕ) : ℝ))) * Real.log n = 0 := by
    rw [c1, c2, c3, c4, c5, c7, c8, c9, c10, c11, c12]
    ring
  have f1 := (lf (j + 10 * n)).2
  have f2 := (lf (j + 11 * n)).2
  have f3 := (lf (j + 12 * n)).2
  have f4 := (lf (15 * n)).2
  have f5 := (lf (10 * n)).1
  have f6 := (lf j).1
  have f7 := (lf (j + n)).1
  have f8 := (lf (j + 2 * n)).1
  have f9 := (lf (j - n)).1
  have f10 := (lf (16 * n - j)).1
  have f11 := (lf (j - 2 * n)).1
  have f12 := (lf (17 * n - j)).1
  have g1 := log_le29 n (j + 10 * n) hn (by omega) (by omega)
  have g2 := log_le29 n (j + 11 * n) hn (by omega) (by omega)
  have g3 := log_le29 n (j + 12 * n) hn (by omega) (by omega)
  have g4 := log_le29 n (15 * n) hn (by omega) (by omega)
  have h32 : 30 * Real.log (3 / 2) = 2 * LZ.xl 15 - 3 * LZ.xl 10 := by
    unfold LZ.xl
    rw [show (3 / 2 : ℝ) = 15 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    ring
  have hn32 : (n : ℝ) * (30 * Real.log (3 / 2)) = n * (2 * LZ.xl 15 - 3 * LZ.xl 10) := by
    rw [h32]
  have hK : 5 + 5 / 2 * Real.log 29 ≤
      (5 + 5 / 2 * Real.log 29) / Real.log 2 * Real.log ((n : ℝ) + 1) := by
    have hA : (0 : ℝ) ≤ (5 + 5 / 2 * Real.log 29) / Real.log 2 :=
      div_nonneg (by positivity) hl2.le
    calc (5 + 5 / 2 * Real.log 29) = (5 + 5 / 2 * Real.log 29) / Real.log 2 * Real.log 2 :=
          (div_mul_cancel₀ _ hl2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hnl hA
  unfold LZ.gA
  linarith

end Pfq54.ST
