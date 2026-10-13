/-
# Blueprint of `hyp_readout` (manuscript eq. (B) and (S0))

Node `Pfq54.hyp_readout` of `Blueprint_pfq54.lean`: for `n ≥ 1` and `0 ≤ k ≤ 14n`,
`U_{n,2n+k} = E_n t_{n,k}`, and hence `S_{0,n} = E_n 𝓕_n(1)`.

Proof (manuscript §3 and Appendix C.1): the value of each binomial jet is the binomial
coefficient itself (lemmas [1], [2]), so `U_{n,2n+k}` is the five-binomial integer `B_{n,k}` ([3]).
Factorial cancellation in the Pochhammer symbols ([4], [5]) gives `E_n t_{n,k} = B_{n,k}` ([6]).
The values `U_{n,j}` vanish for `j < 2n` and `j > 16n` ([7]), so the sum defining `S_{0,n}` is a
sum over `j = 2n + k`, `0 ≤ k ≤ 14n` ([8]).

Every supporting lemma records an estimate of its proof length and whether its proof can be
formalized directly from `manuscript.tex`.
-/
import Pfq54_aux

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- The five-binomial integer (B):
`B_{n,k} = C(12n+k,10n) C(13n+k,10n) C(14n+k,10n) C(15n,n+k) C(15n,k)`. -/
def Bnk (n k : ℕ) : ℕ :=
  (12 * n + k).choose (10 * n) * (13 * n + k).choose (10 * n) * (14 * n + k).choose (10 * n) *
    (15 * n).choose (n + k) * (15 * n).choose k

/-- **[1] Value of the upper jet.** `(upperJet N M).fst = C(N, M)` (both branches; for `M > N`
the binomial coefficient is `0`).
* Estimated proof length: ≈ 8 lines (`unfold upperJet jet; split_ifs; simp`,
  `Nat.choose_eq_zero_of_lt`).
* Directly from the manuscript: yes (definition of the jet). -/
theorem fst_upperJet (N M : ℕ) : (upperJet N M).fst = (N.choose M : ℚ) := by
  unfold upperJet
  split_ifs with h
  · exact Aux.jet_fst _ _
  · rw [Aux.jet_fst, Nat.choose_eq_zero_of_lt (not_le.mp h), Nat.cast_zero]

/-- **[2] Value of the lower jet.** `(lowerJet M m).fst = C(M, m)` for `0 ≤ m ≤ M`, and `0`
otherwise.
* Estimated proof length: ≈ 10 lines (unfold, `split_ifs`, `simp [jet]`).
* Directly from the manuscript: yes. -/
theorem fst_lowerJet (M : ℕ) (m : ℤ) :
    (lowerJet M m).fst = if 0 ≤ m ∧ m ≤ M then (M.choose m.toNat : ℚ) else 0 := by
  unfold lowerJet
  split_ifs <;> exact Aux.jet_fst _ _

/-- **[3] `U_{n,2n+k}` is the five-binomial integer.** For `k ≤ 14n`,
`U_{n,2n+k} = B_{n,k}` ("Thus `U_{n,2n+k} = B_{n,k}`", §5).
* Uses: [1], [2], `TrivSqZeroExt.fst_mul`, `map_prod` for `TrivSqZeroExt.fstHom`.
* Estimated proof length: ≈ 20 lines (the lower arguments `n + k` and `k` lie in `[0, 15n]`;
  `Icc 10 12` product expanded by `decide`).
* Directly from the manuscript: yes. -/
theorem U_two_n_add (n k : ℕ) (hk : k ≤ 14 * n) : U n (2 * n + k) = (Bnk n k : ℚ) := by
  have h1 : ((2 * n + k : ℕ) : ℤ) - n = ((n + k : ℕ) : ℤ) := by push_cast; ring
  have h2 : ((2 * n + k : ℕ) : ℤ) - 2 * n = ((k : ℕ) : ℤ) := by push_cast; ring
  unfold U coeffJet
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul, Aux.fst_prod, Aux.prod_Icc_10_12,
    fst_upperJet, fst_upperJet, fst_upperJet, fst_lowerJet, fst_lowerJet, h1, h2,
    ite_eq_left (by omega), ite_eq_left (by omega), Int.toNat_natCast, Int.toNat_natCast,
    show 2 * n + k + 10 * n = 12 * n + k by omega, show 2 * n + k + 11 * n = 13 * n + k by omega,
    show 2 * n + k + 12 * n = 14 * n + k by omega, Bnk]
  push_cast
  rfl

/-- **[4] Negative Pochhammer symbols.** `(-N)_k = (-1)^k N!/(N-k)!` for `k ≤ N`.
* Estimated proof length: ≈ 15 lines (induction on `k`, `Nat.factorial` recursion).
* Directly from the manuscript: yes (standard; used implicitly in "factorial cancellation"). -/
theorem poch_neg_nat (N k : ℕ) (hk : k ≤ N) :
    poch (-(N : ℚ)) k = (-1) ^ k * N.factorial / (N - k).factorial := by
  induction k with
  | zero => rw [poch, prod_range_zero, pow_zero, one_mul, Nat.sub_zero, div_self (by positivity)]
  | succ k ih =>
    rw [poch, prod_range_succ, ← poch, ih (by omega)]
    have e : N - k = (N - (k + 1)) + 1 := by omega
    have hc : (((N - (k + 1)) + 1 : ℕ) : ℚ) = (N : ℚ) - k := by
      rw [← e, Nat.cast_sub (by omega : k ≤ N)]
    rw [e, Nat.factorial_succ, Nat.cast_mul, hc]
    have hf : ((N - (k + 1)).factorial : ℚ) ≠ 0 := by positivity
    have hd : (N : ℚ) - k ≠ 0 := by
      rw [← hc]; exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    field_simp
    ring

/-- **[5] Shifted Pochhammer symbols.** `(1 + a)_k = (a + k)!/a!`.
* Estimated proof length: ≈ 10 lines (induction on `k`).
* Directly from the manuscript: yes (standard). -/
theorem poch_one_add_nat (a k : ℕ) :
    poch (1 + a) k = (a + k).factorial / a.factorial := by
  induction k with
  | zero => rw [poch, prod_range_zero, Nat.add_zero, div_self (by positivity)]
  | succ k ih =>
    rw [poch, prod_range_succ, ← poch, ih, ← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul]
    have hf : (a.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- **[6] Coefficient normalization (B)**: `E_n t_{n,k} = B_{n,k}` for `n ≥ 1`, `k ≤ 14n`.
* Uses: [4] (for `-14n, -15n`), [5] (for `1+13n, 1+14n, 1+12n, 1+n, …, 1+4n`).
* Estimated proof length: ≈ 40 lines (rewrite all ten Pochhammer symbols as factorial
  quotients, `Nat.choose_eq_factorial_div_factorial`, `field_simp`, `ring`; the signs
  `(-1)^k (-1)^k` cancel).
* Directly from the manuscript: yes ("Factorial cancellation gives (B)"). -/
theorem E_mul_hypTerm (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 14 * n) :
    (E n : ℚ) * hypTerm n k = (Bnk n k : ℚ) := by
  have hp1 := poch_neg_nat (14 * n) k hk
  have hp2 := poch_neg_nat (15 * n) k (by omega)
  push_cast at hp1 hp2
  have hs : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hp12 : poch (-(14 * n : ℚ)) k * poch (-(15 * n : ℚ)) k =
      (14 * n).factorial / (14 * n - k).factorial *
        ((15 * n).factorial / (15 * n - k).factorial) := by
    rw [hp1, hp2]
    calc _ = ((-1 : ℚ) ^ k * (-1) ^ k) * ((14 * n).factorial / (14 * n - k).factorial *
          ((15 * n).factorial / (15 * n - k).factorial)) := by ring
      _ = _ := by rw [hs, one_mul]
  have q13 := poch_one_add_nat (13 * n) k
  have q14 := poch_one_add_nat (14 * n) k
  have q12 := poch_one_add_nat (12 * n) k
  have q2 := poch_one_add_nat (2 * n) k
  have q3 := poch_one_add_nat (3 * n) k
  have q4 := poch_one_add_nat (4 * n) k
  push_cast at q13 q14 q12 q2 q3 q4
  have hc : ∀ a b : ℕ, b ≤ a →
      ((a.choose b : ℕ) : ℚ) = a.factorial / (b.factorial * (a - b).factorial) :=
    fun a b h => Nat.cast_choose ℚ h
  unfold hypTerm E Bnk
  rw [hp12, q13, q14, q12, q2, q3, q4, poch_one_add_nat n k]
  push_cast
  rw [hc _ _ (by omega : 10 * n ≤ 12 * n), hc _ _ (by omega : 10 * n ≤ 13 * n),
    hc _ _ (by omega : 10 * n ≤ 14 * n), hc _ _ (by omega : n ≤ 15 * n),
    hc _ _ (by omega : 10 * n ≤ 12 * n + k), hc _ _ (by omega : 10 * n ≤ 13 * n + k),
    hc _ _ (by omega : 10 * n ≤ 14 * n + k), hc _ _ (by omega : n + k ≤ 15 * n),
    hc _ _ (by omega : k ≤ 15 * n),
    show 12 * n - 10 * n = 2 * n by omega, show 13 * n - 10 * n = 3 * n by omega,
    show 14 * n - 10 * n = 4 * n by omega, show 15 * n - n = 14 * n by omega,
    show 12 * n + k - 10 * n = 2 * n + k by omega, show 13 * n + k - 10 * n = 3 * n + k by omega,
    show 14 * n + k - 10 * n = 4 * n + k by omega, show 15 * n - (n + k) = 14 * n - k by omega]
  field_simp

/-- **[7] Vanishing outside `[2n, 16n]`.** `U_{n,j} = 0` if `j < 2n` (the factor `C(15n, j-2n)`
vanishes) or `j > 16n` (the factor `C(15n, j-n)` vanishes).
* Uses: [2].
* Estimated proof length: ≈ 15 lines.
* Directly from the manuscript: yes ("both of the last two factors vanish", §5). -/
theorem U_eq_zero_outside (n j : ℕ) (hj : j < 2 * n ∨ 16 * n < j) : U n j = 0 := by
  unfold U coeffJet
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul, fst_lowerJet, fst_lowerJet]
  rcases hj with hj | hj
  · rw [ite_eq_right (show ¬(0 ≤ (j : ℤ) - 2 * n ∧ (j : ℤ) - 2 * n ≤ ((15 * n : ℕ) : ℤ)) by omega),
      mul_zero]
  · rw [ite_eq_right (show ¬(0 ≤ (j : ℤ) - n ∧ (j : ℤ) - n ≤ ((15 * n : ℕ) : ℤ)) by omega),
      mul_zero, zero_mul]

/-- **[8] Re-indexing a finite sum supported on `[a, a+b]`.**
* Estimated proof length: ≈ 20 lines (`Finset.sum_subset`, `Finset.sum_map` with `addLeftEmbedding`).
* Directly from the manuscript: yes (elementary). -/
theorem sum_range_shift (f : ℕ → ℚ) (a b N : ℕ) (hN : a + b < N)
    (h : ∀ j < N, (j < a ∨ a + b < j) → f j = 0) :
    ∑ j ∈ range N, f j = ∑ k ∈ range (b + 1), f (a + k) := by
  obtain ⟨c, rfl⟩ : ∃ c, N = a + (b + 1) + c := ⟨N - (a + (b + 1)), by omega⟩
  rw [sum_range_add, sum_range_add,
    sum_eq_zero (fun j hj => h j (by have := mem_range.mp hj; omega)
      (Or.inl (mem_range.mp hj))),
    sum_eq_zero (s := range c) (fun x hx => h _ (by have := mem_range.mp hx; omega)
      (Or.inr (by omega))), zero_add, add_zero]

/-- **`hyp_readout`** (node of `Blueprint_pfq54.lean`). Proved from [3], [6], [7], [8]. -/
theorem hyp_readout (n : ℕ) (hn : 1 ≤ n) :
    (∀ k ≤ 14 * n, U n (2 * n + k) = E n * hypTerm n k) ∧ S0 n = E n * hyp n := by
  have h1 : ∀ k ≤ 14 * n, U n (2 * n + k) = E n * hypTerm n k := fun k hk => by
    rw [U_two_n_add n k hk, E_mul_hypTerm n k hn hk]
  refine ⟨h1, ?_⟩
  rw [S0, sum_range_shift (U n) (2 * n) (14 * n) (17 * n + 1) (by omega)
    (fun j _ hj => U_eq_zero_outside n j (by omega)), hyp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => h1 k (by simp only [Finset.mem_range] at hk; omega)

end Pfq54.BP
