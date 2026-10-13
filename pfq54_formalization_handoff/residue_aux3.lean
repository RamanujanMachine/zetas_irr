/-
# Root-product formulas for `U_{n,j}`, `V_{n,j}` (sorry-free)

`(-1)^n U_{n,j}/C_n = N(-j)/R_j(-j)` at the double poles and `(-1)^n V_{n,j}/C_n = N(-j)/R_j(-j)`
at the simple poles, where `N`, `R_j` are the root products of the numerator and of the
denominator of `F_n` with the pole `-j` removed.
-/
import residue_aux2
import jet_aux

open Finset

noncomputable section

namespace Pfq54.RA

open Pfq54

/-- The denominator roots with the pole `-j` removed. -/
def Rj (n j : ℕ) : Multiset ℤ := (dR n).filter fun x => x ≠ -(j : ℤ)

theorem Rj_split (n j : ℕ) :
    Rj n j = (Icc (-(17 * n : ℤ)) (-n)).val.filter (fun x => x ≠ -(j : ℤ)) +
      (Icc (-(16 * n : ℤ)) (-(2 * n))).val.filter (fun x => x ≠ -(j : ℤ)) :=
  Multiset.filter_add _ _ _

theorem harm_one_zero : harm 1 0 = 0 := by
  unfold harm
  rfl

theorem upper_part (j c m N : ℕ) (a b : ℤ) (hN : N = j + c + m) (ha : a = c + 1)
    (hb : b = c + m) :
    ((pr (Icc a b).val (-(j : ℤ)) : ℤ) : ℚ) = (-1) ^ m * (N.choose m : ℚ) * (m.factorial : ℚ) := by
  have h1 := prod_above (-(j : ℤ)) a b (j + c) m (by push_cast; omega) (by push_cast; omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left m (j + c))
  rw [Nat.add_sub_cancel, ← hN] at h2
  have hf : ((j + c).factorial : ℚ) ≠ 0 := by positivity
  have h1' : ((pr (Icc a b).val (-(j : ℤ)) : ℤ) : ℚ) * ((j + c).factorial : ℚ) =
      (-1) ^ m * ((j + c + m).factorial : ℚ) := by exact_mod_cast h1
  have h2' : (N.choose m : ℚ) * (m.factorial : ℚ) * ((j + c).factorial : ℚ) =
      ((j + c + m).factorial : ℚ) := by rw [← hN]; exact_mod_cast h2
  apply mul_right_cancel₀ hf
  rw [h1', ← h2', mul_assoc, mul_assoc, mul_assoc]

theorem pr_nR (n j : ℕ) :
    ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) = Cu n j * ((10 * n).factorial : ℚ) ^ 3 := by
  have e : ∀ (c N : ℕ) (a b : ℤ), N = j + c + 10 * n → a = c + 1 → b = c + 10 * n →
      ((pr (Icc a b).val (-(j : ℤ)) : ℤ) : ℚ) =
        (N.choose (10 * n) : ℚ) * ((10 * n).factorial : ℚ) := fun c N a b hN ha hb => by
    rw [upper_part j c (10 * n) N a b hN ha (by push_cast; exact hb),
      Even.neg_one_pow ⟨5 * n, by ring⟩, one_mul]
  rw [nR, pr_add, pr_add, Int.cast_mul, Int.cast_mul,
    e 0 (j + 10 * n) 1 (10 * (n : ℤ)) (by omega) (by omega) (by omega),
    e n (j + 11 * n) ((n : ℤ) + 1) (11 * (n : ℤ)) (by omega) (by omega) (by omega),
    e (2 * n) (j + 12 * n) (2 * (n : ℤ) + 1) (12 * (n : ℤ)) (by omega) (by push_cast; ring)
      (by omega)]
  unfold Cu
  ring

theorem Ls_nR (n j : ℕ) : Ls (nR n) (-(j : ℤ)) = Xu n j := by
  have e : ∀ (c : ℕ) (a b : ℤ), a = c + 1 → b = c + 10 * n →
      Ls (Icc a b).val (-(j : ℤ)) = -(harm 1 (j + c + 10 * n) - harm 1 (j + c)) :=
    fun c a b ha hb =>
      sum_above (-(j : ℤ)) a b (j + c) (10 * n) (by push_cast; omega) (by push_cast; omega)
  rw [nR, Ls_add, Ls_add, e 0 1 (10 * (n : ℤ)) (by omega) (by omega),
    e n ((n : ℤ) + 1) (11 * (n : ℤ)) (by omega) (by omega),
    e (2 * n) (2 * (n : ℤ) + 1) (12 * (n : ℤ)) (by push_cast; ring) (by omega)]
  unfold Xu
  rw [add_zero, show j + n + 10 * n = j + 11 * n by omega,
    show j + 2 * n + 10 * n = j + 12 * n by omega, show j + 10 * n - 10 * n = j by omega,
    show j + 11 * n - 10 * n = j + n by omega, show j + 12 * n - 10 * n = j + 2 * n by omega]

theorem lower_part (j lo hi : ℕ) (a b : ℤ) (ha : a = -(hi : ℤ)) (hb : b = -(lo : ℤ))
    (h1 : lo ≤ j) (h2 : j ≤ hi) :
    ((pr ((Icc a b).val.filter fun x => x ≠ -(j : ℤ)) (-(j : ℤ)) : ℤ) : ℚ) =
      (-1) ^ (j - lo) * ((j - lo).factorial : ℚ) * ((hi - j).factorial : ℚ) := by
  rw [show pr ((Icc a b).val.filter fun x => x ≠ -(j : ℤ)) (-(j : ℤ)) =
      ∏ x ∈ (Icc a b).filter (fun x => x ≠ -(j : ℤ)), (-(j : ℤ) - x) from rfl,
    Icc_filter_ne a b _ (by omega) (by omega), prod_union (Icc_disj a b _)]
  have e1 := prod_below (-(j : ℤ)) a (-(j : ℤ) - 1) 0 (hi - j) (by omega) (by omega)
  have e2 := prod_above (-(j : ℤ)) (-(j : ℤ) + 1) b 0 (j - lo) (by omega) (by omega)
  rw [Nat.factorial_zero, Nat.cast_one, mul_one, zero_add] at e1 e2
  rw [Int.cast_mul, e1, e2]
  push_cast
  ring

theorem Ls_lower (j lo hi : ℕ) (a b : ℤ) (ha : a = -(hi : ℤ)) (hb : b = -(lo : ℤ))
    (h1 : lo ≤ j) (h2 : j ≤ hi) :
    Ls ((Icc a b).val.filter fun x => x ≠ -(j : ℤ)) (-(j : ℤ)) =
      harm 1 (hi - j) - harm 1 (j - lo) := by
  rw [show Ls ((Icc a b).val.filter fun x => x ≠ -(j : ℤ)) (-(j : ℤ)) =
      ∑ x ∈ (Icc a b).filter (fun x => x ≠ -(j : ℤ)), 1 / ((-(j : ℤ) - x : ℤ) : ℚ) from rfl,
    Icc_filter_ne a b _ (by omega) (by omega), sum_union (Icc_disj a b _),
    sum_below (-(j : ℤ)) a (-(j : ℤ) - 1) 0 (hi - j) (by omega) (by omega),
    sum_above (-(j : ℤ)) (-(j : ℤ) + 1) b 0 (j - lo) (by omega) (by omega), zero_add, zero_add,
    harm_one_zero]
  ring

theorem choose_fact (M m r : ℕ) (h : m ≤ M) (hr : M - m = r) :
    (M.choose m : ℚ) * (m.factorial : ℚ) * (r.factorial : ℚ) = (M.factorial : ℚ) := by
  have := Nat.choose_mul_factorial_mul_factorial h
  rw [hr] at this
  exact_mod_cast this

/-- **Double poles** `2n ≤ j ≤ 16n`. -/
theorem root_double (n j : ℕ) (h1 : 2 * n ≤ j) (h2 : j ≤ 16 * n) :
    (-1) ^ n * U n j * ((10 * n).factorial : ℚ) ^ 3 * ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) =
      ((15 * n).factorial : ℚ) ^ 2 * ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) ∧
    V n j = U n j * (Ls (nR n) (-(j : ℤ)) - Ls (Rj n j) (-(j : ℤ))) := by
  have hJ : coeffJet n j = jet (Cu n j * ((15 * n).choose (j - n) : ℚ) *
      ((15 * n).choose (j - 2 * n) : ℚ))
      (Cu n j * ((15 * n).choose (j - n) : ℚ) * ((15 * n).choose (j - 2 * n) : ℚ) *
        (Xu n j + (harm 1 (j - n) - harm 1 (15 * n - (j - n))) +
          (harm 1 (j - 2 * n) - harm 1 (15 * n - (j - 2 * n))))) := by
    unfold coeffJet
    rw [upper_jets, show (j : ℤ) - n = ((j - n : ℕ) : ℤ) by omega,
      show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
      lowerJet_log (15 * n) (j - n) (by omega), lowerJet_log (15 * n) (j - 2 * n) (by omega),
      jet_mul_log, jet_mul_log]
  have hU : U n j = Cu n j * ((15 * n).choose (j - n) : ℚ) *
      ((15 * n).choose (j - 2 * n) : ℚ) := by rw [U, hJ, Aux.jet_fst]
  refine ⟨?_, ?_⟩
  · rw [hU, Rj_split, pr_add, Int.cast_mul, pr_nR,
      lower_part j n (17 * n) _ _ (by push_cast; ring) rfl (by omega) (by omega),
      lower_part j (2 * n) (16 * n) _ _ (by push_cast; ring) (by push_cast; ring) (by omega)
        (by omega)]
    have eC1 := choose_fact (15 * n) (j - n) (16 * n - j) (by omega) (by omega)
    have eC2 := choose_fact (15 * n) (j - 2 * n) (17 * n - j) (by omega) (by omega)
    have hs : (-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (j - 2 * n) = 1 := by
      rw [← pow_add, ← pow_add]; exact Even.neg_one_pow ⟨j - n, by omega⟩
    set K := Cu n j * ((10 * n).factorial : ℚ) ^ 3
    set X := ((15 * n).choose (j - n) : ℚ) * ((j - n).factorial : ℚ) *
      ((16 * n - j).factorial : ℚ)
    set Y := ((15 * n).choose (j - 2 * n) : ℚ) * ((j - 2 * n).factorial : ℚ) *
      ((17 * n - j).factorial : ℚ)
    linear_combination (K * X * Y) * hs + (K * Y) * eC1 + (K * ((15 * n).factorial : ℚ)) * eC2
  · rw [V, hJ, Aux.jet_snd, hU, Ls_nR, Rj_split, Ls_add,
      Ls_lower j n (17 * n) _ _ (by push_cast; ring) rfl (by omega) (by omega),
      Ls_lower j (2 * n) (16 * n) _ _ (by push_cast; ring) (by push_cast; ring) (by omega)
        (by omega),
      show 15 * n - (j - n) = 16 * n - j by omega, show 15 * n - (j - 2 * n) = 17 * n - j by omega]
    ring

/-- **Simple poles** `n ≤ j < 2n`. -/
theorem root_simple_lo (n j : ℕ) (h1 : n ≤ j) (h2 : j < 2 * n) :
    U n j = 0 ∧
      (-1) ^ n * V n j * ((10 * n).factorial : ℚ) ^ 3 * ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) =
        ((15 * n).factorial : ℚ) ^ 2 * ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) := by
  set s2 : ℚ := (-1 : ℚ) ^ (2 * n - j) * (15 * n).factorial * (2 * n - j - 1).factorial /
    (15 * n + (2 * n - j)).factorial
  have hJ : coeffJet n j = jet 0 (Cu n j * ((15 * n).choose (j - n) : ℚ) * s2) := by
    unfold coeffJet
    rw [upper_jets, show (j : ℤ) - n = ((j - n : ℕ) : ℤ) by omega,
      show (j : ℤ) - 2 * n = -((2 * n - j : ℕ) : ℤ) by omega,
      lowerJet_log (15 * n) (j - n) (by omega), lowerJet_neg (15 * n) (2 * n - j) (by omega),
      jet_mul_log, jet_mul_zero]
  refine ⟨by rw [U, hJ, Aux.jet_fst], ?_⟩
  have hI2 : (Icc (-(16 * n : ℤ)) (-(2 * n))).val.filter (fun x => x ≠ -(j : ℤ)) =
      (Icc (-(16 * n : ℤ)) (-(2 * n))).val :=
    Multiset.filter_eq_self.mpr fun x hx => by rw [Finset.mem_val, mem_Icc] at hx; omega
  have eQ2 := prod_below (-(j : ℤ)) (-(16 * n : ℤ)) (-(2 * n)) (2 * n - j - 1) (14 * n + 1)
    (by omega) (by omega)
  rw [show 2 * n - j - 1 + (14 * n + 1) = 16 * n - j by omega] at eQ2
  have eQ2' : ((pr (Icc (-(16 * n : ℤ)) (-(2 * n))).val (-(j : ℤ)) : ℤ) : ℚ) *
      ((2 * n - j - 1).factorial : ℚ) = ((16 * n - j).factorial : ℚ) := by exact_mod_cast eQ2
  have es : s2 * ((17 * n - j).factorial : ℚ) =
      (-1 : ℚ) ^ (2 * n - j) * (15 * n).factorial * (2 * n - j - 1).factorial := by
    rw [show 17 * n - j = 15 * n + (2 * n - j) by omega]
    exact div_mul_cancel₀ _ (by positivity)
  rw [V, hJ, Aux.jet_snd, Rj_split, hI2, pr_add, Int.cast_mul, pr_nR,
    lower_part j n (17 * n) _ _ (by push_cast; ring) rfl (by omega) (by omega)]
  have eC1 := choose_fact (15 * n) (j - n) (16 * n - j) (by omega) (by omega)
  have hs : (-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (2 * n - j) = 1 := by
    rw [← pow_add, ← pow_add]; exact Even.neg_one_pow ⟨n, by omega⟩
  set K := Cu n j * ((10 * n).factorial : ℚ) ^ 3
  set Q2 := ((pr (Icc (-(16 * n : ℤ)) (-(2 * n))).val (-(j : ℤ)) : ℤ) : ℚ)
  set F15 := ((15 * n).factorial : ℚ)
  set C1 := ((15 * n).choose (j - n) : ℚ)
  set Fa := ((j - n).factorial : ℚ)
  set sg := (-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (2 * n - j)
  linear_combination ((-1 : ℚ) ^ n * (-1) ^ (j - n) * Cu n j * C1 * ((10 * n).factorial : ℚ) ^ 3 *
      Fa * Q2) * es +
    ((-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (2 * n - j) * Cu n j * C1 *
      ((10 * n).factorial : ℚ) ^ 3 * Fa * F15) * eQ2' +
    (sg * K * F15) * eC1 + (K * F15 ^ 2) * hs

/-- **Simple poles** `16n < j ≤ 17n`. -/
theorem root_simple_hi (n j : ℕ) (h1 : 16 * n < j) (h2 : j ≤ 17 * n) :
    U n j = 0 ∧
      (-1) ^ n * V n j * ((10 * n).factorial : ℚ) ^ 3 * ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) =
        ((15 * n).factorial : ℚ) ^ 2 * ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) := by
  set s1 : ℚ := (-1 : ℚ) ^ (j - 16 * n - 1) * (15 * n).factorial * (j - 16 * n - 1).factorial /
    (15 * n + (j - 16 * n)).factorial
  have hJ : coeffJet n j = jet 0 (Cu n j * s1 * ((15 * n).choose (j - 2 * n) : ℚ)) := by
    unfold coeffJet
    rw [upper_jets, show (j : ℤ) - n = ((15 * n + (j - 16 * n) : ℕ) : ℤ) by omega,
      show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
      lowerJet_big (15 * n) (j - 16 * n) (by omega), lowerJet_log (15 * n) (j - 2 * n) (by omega),
      jet_mul_zero, jet_zero_mul]
  refine ⟨by rw [U, hJ, Aux.jet_fst], ?_⟩
  have hI2 : (Icc (-(16 * n : ℤ)) (-(2 * n))).val.filter (fun x => x ≠ -(j : ℤ)) =
      (Icc (-(16 * n : ℤ)) (-(2 * n))).val :=
    Multiset.filter_eq_self.mpr fun x hx => by rw [Finset.mem_val, mem_Icc] at hx; omega
  have eQ2 := prod_above (-(j : ℤ)) (-(16 * n : ℤ)) (-(2 * n)) (j - 16 * n - 1) (14 * n + 1)
    (by omega) (by omega)
  rw [show j - 16 * n - 1 + (14 * n + 1) = j - 2 * n by omega] at eQ2
  have eQ2' : ((pr (Icc (-(16 * n : ℤ)) (-(2 * n))).val (-(j : ℤ)) : ℤ) : ℚ) *
      ((j - 16 * n - 1).factorial : ℚ) = (-1) ^ (14 * n + 1) * ((j - 2 * n).factorial : ℚ) := by
    exact_mod_cast eQ2
  have es : s1 * ((j - n).factorial : ℚ) =
      (-1 : ℚ) ^ (j - 16 * n - 1) * (15 * n).factorial * (j - 16 * n - 1).factorial := by
    rw [show j - n = 15 * n + (j - 16 * n) by omega]
    exact div_mul_cancel₀ _ (by positivity)
  rw [V, hJ, Aux.jet_snd, Rj_split, hI2, pr_add, Int.cast_mul, pr_nR,
    lower_part j n (17 * n) _ _ (by push_cast; ring) rfl (by omega) (by omega)]
  have eC2 := choose_fact (15 * n) (j - 2 * n) (17 * n - j) (by omega) (by omega)
  have hs : (-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (j - 16 * n - 1) * (-1) ^ (14 * n + 1) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add]; exact Even.neg_one_pow ⟨j - n, by omega⟩
  set K := Cu n j * ((10 * n).factorial : ℚ) ^ 3
  set Q2 := ((pr (Icc (-(16 * n : ℤ)) (-(2 * n))).val (-(j : ℤ)) : ℤ) : ℚ)
  set F15 := ((15 * n).factorial : ℚ)
  set C2 := ((15 * n).choose (j - 2 * n) : ℚ)
  set Fb := ((17 * n - j).factorial : ℚ)
  set sg := (-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (j - 16 * n - 1) * (-1) ^ (14 * n + 1)
  linear_combination ((-1 : ℚ) ^ n * (-1) ^ (j - n) * Cu n j * C2 * ((10 * n).factorial : ℚ) ^ 3 *
      Fb * Q2) * es +
    ((-1 : ℚ) ^ n * (-1) ^ (j - n) * (-1) ^ (j - 16 * n - 1) * Cu n j * C2 *
      ((10 * n).factorial : ℚ) ^ 3 * Fb * F15) * eQ2' +
    (sg * K * F15) * eC2 + (K * F15 ^ 2) * hs

/-- **No pole** for `j < n`. -/
theorem root_zero (n j : ℕ) (h : j < n) : U n j = 0 ∧ V n j = 0 := by
  have hJ : coeffJet n j = jet 0 ((Cu n j * ((-1 : ℚ) ^ (n - j) * (15 * n).factorial *
      (n - j - 1).factorial / (15 * n + (n - j)).factorial)) * 0) := by
    unfold coeffJet
    rw [upper_jets, show (j : ℤ) - n = -((n - j : ℕ) : ℤ) by omega,
      show (j : ℤ) - 2 * n = -((2 * n - j : ℕ) : ℤ) by omega,
      lowerJet_neg (15 * n) (n - j) (by omega), lowerJet_neg (15 * n) (2 * n - j) (by omega),
      jet_mul_zero, jet_zero_mul]
  exact ⟨by rw [U, hJ, Aux.jet_fst], by rw [V, hJ, Aux.jet_snd, mul_zero]⟩

end Pfq54.RA
