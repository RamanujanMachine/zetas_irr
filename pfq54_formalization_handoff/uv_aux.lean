/-
# Valuations on the upper harmonic ranges (sorry-free)

For `15n < p`, `29n < 2p` and `p ≤ j + 2n`, the three upper binomials of `U_{n,j}` carry
`3 - t` powers of `p`, `t = 𝟙_{p ≤ j} + 𝟙_{p ≤ j+n} + 1`.
-/
import jet_aux
import pairing_bound

open Finset

noncomputable section

namespace Pfq54.UV

open Pfq54
open ZetasIrr.Aux (ValGE)

variable (p : ℕ) [hp : Fact p.Prime]

theorem valGE_nat (m : ℕ) : ValGE p 0 (m : ℚ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · left
    rw [h, Nat.cast_zero]
  · right
    rw [padicValRat.of_nat]
    exact Nat.cast_nonneg _

theorem div_two (m : ℕ) (hm : m < 2 * p) : m / p = if p ≤ m then 1 else 0 := by
  have hp0 := hp.out.pos
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- `v_p C(N, M) = 𝟙_{p ≤ N} - 𝟙_{p ≤ N - M}` for `M < p` and `N < 2p`. -/
theorem val_choose (N M : ℕ) (hMN : M ≤ N) (hN : N < 2 * p) (hM : M < p) :
    padicValRat p ((N.choose M : ℕ) : ℚ) =
      (if p ≤ N then 1 else 0) - (if p ≤ N - M then 1 else 0) := by
  have h2 : 2 * p ≤ p ^ 2 := by
    have := hp.out.two_le
    nlinarith
  have key := Nat.choose_mul_factorial_mul_factorial hMN
  have hc : N.choose M ≠ 0 := (Nat.choose_pos hMN).ne'
  have e := congrArg (padicValNat p) key
  rw [padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero M)) (Nat.factorial_ne_zero _),
    padicValNat.mul hc (Nat.factorial_ne_zero M), BP.padicValNat_factorial_small p _ (by omega),
    BP.padicValNat_factorial_small p _ (by omega), BP.padicValNat_factorial_small p _ (by omega),
    Nat.div_eq_of_lt hM, div_two p _ (by omega), div_two p _ hN] at e
  rw [padicValRat.of_nat]
  split_ifs at e ⊢ <;> omega

/-- The three upper binomials. -/
theorem val_Cu (n j : ℕ) (h10 : 10 * n < p) (hlo : p ≤ j + 10 * n) (hhi : j + 12 * n < 2 * p) :
    ValGE p (3 - ((if p ≤ j then 1 else 0) + (if p ≤ j + n then 1 else 0) +
      (if p ≤ j + 2 * n then 1 else 0))) (RA.Cu n j) := by
  right
  have c10 : ((j + 10 * n).choose (10 * n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c11 : ((j + 11 * n).choose (10 * n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c12 : ((j + 12 * n).choose (10 * n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  unfold RA.Cu
  rw [padicValRat.mul (mul_ne_zero c10 c11) c12, padicValRat.mul c10 c11,
    val_choose p _ _ (by omega) (by omega) h10, val_choose p _ _ (by omega) (by omega) h10,
    val_choose p _ _ (by omega) (by omega) h10, show j + 10 * n - 10 * n = j by omega,
    show j + 11 * n - 10 * n = j + n by omega, show j + 12 * n - 10 * n = j + 2 * n by omega,
    ite_eq_left (by omega : p ≤ j + 10 * n), ite_eq_left (by omega : p ≤ j + 11 * n),
    ite_eq_left (by omega : p ≤ j + 12 * n)]
  omega

/-- **The upper ranges**: double poles keep `3 - t` powers in `U` and lose one in `V`; at the
simple poles `U = 0` and `V` keeps `3 - t`. -/
theorem UV_active (n j : ℕ) (hH : ∀ m, m < p ^ 2 → ValGE p (-1) (harm 1 m))
    (h15 : 16 * n < p) (h2p : 29 * n < 2 * p) (hsq : 29 * n < p ^ 2) (hj : j ≤ 17 * n)
    (hact : p ≤ j + 2 * n) :
    (j ≤ 16 * n → ValGE p (3 - ((if p ≤ j then 1 else 0) + (if p ≤ j + n then 1 else 0) + 1))
      (U n j) ∧ ValGE p (2 - ((if p ≤ j then 1 else 0) + (if p ≤ j + n then 1 else 0) + 1))
      (V n j)) ∧
    (16 * n < j → U n j = 0 ∧ ValGE p (3 - ((if p ≤ j then 1 else 0) +
      (if p ≤ j + n then 1 else 0) + 1)) (V n j)) := by
  have hCu := val_Cu p n j (by omega) (by omega) (by omega)
  rw [ite_eq_left hact] at hCu
  have hH' : ∀ m, m ≤ 29 * n → ValGE p (-1) (harm 1 m) := fun m hm => hH m (by omega)
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · have hJ : coeffJet n j = jet (RA.Cu n j * ((15 * n).choose (j - n) : ℚ) *
        ((15 * n).choose (j - 2 * n) : ℚ))
        (RA.Cu n j * ((15 * n).choose (j - n) : ℚ) * ((15 * n).choose (j - 2 * n) : ℚ) *
          (RA.Xu n j + (harm 1 (j - n) - harm 1 (15 * n - (j - n))) +
            (harm 1 (j - 2 * n) - harm 1 (15 * n - (j - 2 * n))))) := by
      unfold coeffJet
      rw [RA.upper_jets, show (j : ℤ) - n = ((j - n : ℕ) : ℤ) by omega,
        show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
        RA.lowerJet_log (15 * n) (j - n) (by omega), RA.lowerJet_log (15 * n) (j - 2 * n) (by omega),
        RA.jet_mul_log, RA.jet_mul_log]
    have hU := (hCu.mul (valGE_nat p ((15 * n).choose (j - n)))).mul
      (valGE_nat p ((15 * n).choose (j - 2 * n)))
    rw [add_zero, add_zero] at hU
    have hL : ValGE p (-1) (RA.Xu n j + (harm 1 (j - n) - harm 1 (15 * n - (j - n))) +
        (harm 1 (j - 2 * n) - harm 1 (15 * n - (j - 2 * n)))) := by
      unfold RA.Xu
      exact ((((hH' _ (by omega)).sub (hH' _ (by omega))).neg.add
        ((hH' _ (by omega)).sub (hH' _ (by omega))).neg).add
          ((hH' _ (by omega)).sub (hH' _ (by omega))).neg |>.add
            ((hH' _ (by omega)).sub (hH' _ (by omega)))).add
              ((hH' _ (by omega)).sub (hH' _ (by omega)))
    refine ⟨by rw [U, hJ, Aux.jet_fst]; exact hU, ?_⟩
    rw [V, hJ, Aux.jet_snd]
    exact (hU.mul hL).mono (by omega)
  · have hJ : coeffJet n j = jet 0 (RA.Cu n j * ((-1 : ℚ) ^ (j - 16 * n - 1) *
        (15 * n).factorial * (j - 16 * n - 1).factorial / (15 * n + (j - 16 * n)).factorial) *
          ((15 * n).choose (j - 2 * n) : ℚ)) := by
      unfold coeffJet
      rw [RA.upper_jets, show (j : ℤ) - n = ((15 * n + (j - 16 * n) : ℕ) : ℤ) by omega,
        show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
        RA.lowerJet_big (15 * n) (j - 16 * n) (by omega),
        RA.lowerJet_log (15 * n) (j - 2 * n) (by omega), RA.jet_mul_zero, RA.jet_zero_mul]
    have hden : ValGE p 0 (((15 * n + (j - 16 * n)).factorial : ℚ))⁻¹ := by
      right
      rw [padicValRat.inv, padicValRat.of_nat, BP.padicValNat_factorial_small p _ (by omega),
        Nat.div_eq_of_lt (by omega), Nat.cast_zero, neg_zero]
    have hsgn : ValGE p 0 ((-1 : ℚ) ^ (j - 16 * n - 1)) :=
      Or.inr (by rw [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero])
    have hs1 := ((hsgn.mul (valGE_nat p (15 * n).factorial)).mul
      (valGE_nat p (j - 16 * n - 1).factorial)).mul hden
    rw [← div_eq_mul_inv] at hs1
    refine ⟨by rw [U, hJ, Aux.jet_fst], ?_⟩
    rw [V, hJ, Aux.jet_snd]
    exact ((hCu.mul hs1).mul (valGE_nat p ((15 * n).choose (j - 2 * n)))).mono (by omega)

end Pfq54.UV
