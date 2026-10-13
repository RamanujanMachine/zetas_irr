/-
# The polynomial `T` and the valuations of the partial-fraction coefficients (sorry-free)
-/
import residue_aux3

open Finset Polynomial

noncomputable section

namespace Pfq54.RA

open Pfq54
open ZetasIrr.Aux (ValGE)

/-- The exponent `1 + c_a - d_a` of `X - a` in `T`. -/
def ex (n p a : ℕ) : ℕ := 1 + rc (nR n) p a - rc (dR n) p a

/-- `T = ∏_{a ∈ 𝔽_p} (X - a)^{1 + c_a - d_a}`, a lift of `(X^p - X) N̄/D̄`. -/
def Tp (n p : ℕ) : Polynomial ℤ := ∏ a ∈ range p, (X - C (a : ℤ)) ^ ex n p a

theorem count_Icc (a b t : ℤ) : (Icc a b).val.count t = if a ≤ t ∧ t ≤ b then 1 else 0 := by
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [ite_eq_left h]
    exact Multiset.count_eq_one_of_mem (Finset.nodup _) (Finset.mem_val.mpr (mem_Icc.mpr h))
  · rw [ite_eq_right h]
    exact Multiset.count_eq_zero.mpr fun hm => h (mem_Icc.mp (Finset.mem_val.mp hm))

theorem card_nR (n : ℕ) : Multiset.card (nR n) = 30 * n := by
  rw [nR, Multiset.card_add, Multiset.card_add, Finset.card_val, Finset.card_val,
    Finset.card_val, Int.card_Icc, Int.card_Icc, Int.card_Icc]
  omega

theorem card_dR (n : ℕ) : Multiset.card (dR n) = 30 * n + 2 := by
  rw [dR, Multiset.card_add, Finset.card_val, Finset.card_val, Int.card_Icc, Int.card_Icc]
  omega

theorem Tp_natDegree (n p : ℕ) [Fact p.Prime] (h8 : 8 * n < p) (h11 : p < 11 * n) :
    (Tp n p).natDegree ≤ p - 2 := by
  rw [Tp, natDegree_prod_of_monic (s := range p) (f := fun a => (X - C (a : ℤ)) ^ ex n p a)
    fun a _ => (monic_X_sub_C _).pow _]
  have hdeg : ∀ a ∈ range p, ((X - C (a : ℤ)) ^ ex n p a).natDegree = ex n p a := fun a _ => by
    rw [(monic_X_sub_C (a : ℤ)).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [Finset.sum_congr rfl hdeg]
  have hle : ∀ a ∈ range p, ex n p a + rc (dR n) p a = 1 + rc (nR n) p a := fun a ha => by
    have := (root_count' n p a h8 h11 (mem_range.mp ha)).1
    unfold ex
    omega
  have hsum := Finset.sum_congr rfl hle
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_rc p, sum_rc p, card_nR, card_dR,
    Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsum
  show ∑ a ∈ range p, ex n p a ≤ p - 2
  omega

theorem Tp_eval (n p : ℕ) (t : ℤ) :
    (Tp n p).eval t = ∏ a ∈ range p, (t - a) ^ ex n p a := by
  rw [Tp, eval_prod]
  exact Finset.prod_congr rfl fun a _ => by rw [eval_pow, eval_sub, eval_X, eval_C]

/-- `T` vanishes on the classes off the support. -/
theorem Tp_zero (n p k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p)
    (hs : ¬ (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p)) :
    (Tp n p).eval (k : ℤ) = 0 := by
  rw [Tp_eval]
  refine Finset.prod_eq_zero (mem_range.mpr hk) ?_
  have h := root_count' n p k h8 h11 hk
  have hex : ex n p k ≠ 0 := by
    unfold ex
    have := h.2.not.mpr hs
    omega
  rw [sub_self, zero_pow hex]

/-- `T(t) ≡ T(k)` for `t ≡ k (mod p)`. -/
theorem Tp_congr (n p : ℕ) (t : ℤ) (k : ℕ) (htk : t % p = k) :
    (p : ℤ) ∣ (Tp n p).eval t - (Tp n p).eval (k : ℤ) := by
  have h : (p : ℤ) ∣ t - k := by
    have := Int.emod_add_mul_ediv t p
    rw [htk] at this
    exact ⟨t / p, by linarith⟩
  exact h.trans (Polynomial.sub_dvd_eval_sub t k _)

/-- On the support, `T(k) D̄*(k) = -N̄*(k)` in `𝔽_p` (Wilson). -/
theorem Tp_supp (n p k : ℕ) [Fact p.Prime] (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p)
    (hs : 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) :
    (((Tp n p).eval (k : ℤ) : ℤ) : ZMod p) *
        ∏ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (dR n) p a =
      -∏ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (nR n) p a := by
  have hk0 : ex n p k = 0 := by
    have := (root_count' n p k h8 h11 hk).2.mpr hs
    unfold ex
    omega
  rw [Tp_eval, ← Finset.mul_prod_erase _ _ (mem_range.mpr hk), sub_self, hk0, pow_zero, one_mul,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  have e : ∀ a ∈ (range p).erase k, ((((k : ℤ) - a) ^ ex n p a : ℤ) : ZMod p) *
      ((k : ZMod p) - a) ^ rc (dR n) p a =
        ((k : ZMod p) - a) * ((k : ZMod p) - a) ^ rc (nR n) p a := fun a ha => by
    have hexp : ex n p a + rc (dR n) p a = 1 + rc (nR n) p a := by
      have := (root_count' n p a h8 h11 (mem_range.mp (Finset.mem_of_mem_erase ha))).1
      unfold ex
      omega
    rw [Int.cast_pow, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ← pow_add, hexp, pow_add,
      pow_one]
  rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, prod_erase_sub p k hk, neg_one_mul]

/-- The class of `-j` modulo `p`. -/
theorem class_neg (p j : ℕ) (hp : 0 < p) (hj : j < 3 * p) :
    ((-(j : ℤ)) % p).toNat < p ∧ ((((-(j : ℤ)) % p).toNat : ℕ) : ℤ) = (-(j : ℤ)) % p ∧
      (((-(j : ℤ)) % p).toNat + j = 0 ∨ ((-(j : ℤ)) % p).toNat + j = p ∨
        ((-(j : ℤ)) % p).toNat + j = 2 * p ∨ ((-(j : ℤ)) % p).toNat + j = 3 * p) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h0 := Int.emod_nonneg (-(j : ℤ)) hp'.ne'
  have h1 := Int.emod_lt_of_pos (-(j : ℤ)) hp'
  have h2 := Int.emod_add_mul_ediv (-(j : ℤ)) p
  set r := (-(j : ℤ)) % p
  set q := (-(j : ℤ)) / p
  have hq1 : q ≤ 0 := by
    by_contra h
    have : (p : ℤ) * 1 ≤ p * q := mul_le_mul_of_nonneg_left (by omega) hp'.le
    omega
  have hq2 : -3 ≤ q := by
    by_contra h
    have : (p : ℤ) * q ≤ p * (-4) := mul_le_mul_of_nonneg_left (by omega) hp'.le
    omega
  refine ⟨by omega, Int.toNat_of_nonneg h0, ?_⟩
  rcases (show q = 0 ∨ q = -1 ∨ q = -2 ∨ q = -3 by omega) with h | h | h | h <;> rw [h] at h2 <;>
    omega

theorem mem_nR (n : ℕ) (x : ℤ) (hx : x ∈ nR n) : 1 ≤ x ∧ x ≤ 12 * n := by
  rw [nR, Multiset.mem_add, Multiset.mem_add, Finset.mem_val, Finset.mem_val, Finset.mem_val,
    mem_Icc, mem_Icc, mem_Icc] at hx
  omega

theorem mem_Rj (n j : ℕ) (x : ℤ) (hx : x ∈ Rj n j) :
    -(17 * n : ℤ) ≤ x ∧ x ≤ -(n : ℤ) ∧ x ≠ -(j : ℤ) := by
  rw [Rj, Multiset.mem_filter, dR, Multiset.mem_add, Finset.mem_val, Finset.mem_val, mem_Icc,
    mem_Icc] at hx
  omega

theorem fac_nR (n p j : ℕ) (hj : j ≤ 17 * n) (hp2 : 30 * n < p ^ 2) :
    ∀ x ∈ nR n, -(j : ℤ) - x ≠ 0 ∧ (-(j : ℤ) - x).natAbs < p ^ 2 := fun x hx => by
  have := mem_nR n x hx
  constructor <;> omega

theorem fac_Rj (n p j : ℕ) (hj : j ≤ 17 * n) (hp2 : 30 * n < p ^ 2) :
    ∀ x ∈ Rj n j, -(j : ℤ) - x ≠ 0 ∧ (-(j : ℤ) - x).natAbs < p ^ 2 := fun x hx => by
  have := mem_Rj n j x hx
  constructor <;> omega

theorem ratio (n : ℕ) (Y R N : ℚ)
    (h : (-1) ^ n * Y * ((10 * n).factorial : ℚ) ^ 3 * R = ((15 * n).factorial : ℚ) ^ 2 * N) :
    (-1) ^ n * Y / Cn n * R = N := by
  have hF : ((15 * n).factorial : ℚ) ^ 2 ≠ 0 := by positivity
  rw [Cn, div_div_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hF]
  linear_combination h

variable (p : ℕ) [hp : Fact p.Prime]

/-- Double poles: `v_p(a_j) = c_k - d_k + 2` and `b_j = a_j L_j`. -/
theorem val_double (n j k : ℕ) (hp2 : 30 * n < p ^ 2) (h1 : 2 * n ≤ j) (h2 : j ≤ 16 * n)
    (htk : (-(j : ℤ)) % p = k) :
    (-1) ^ n * U n j / Cn n ≠ 0 ∧
      padicValRat p ((-1) ^ n * U n j / Cn n) = (rc (nR n) p k : ℤ) - rc (dR n) p k + 2 ∧
      (-1) ^ n * U n j / Cn n * ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) = ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) ∧
      (-1) ^ n * V n j / Cn n =
        (-1) ^ n * U n j / Cn n * (Ls (nR n) (-(j : ℤ)) - Ls (Rj n j) (-(j : ℤ))) := by
  obtain ⟨hrd, hV⟩ := root_double n j h1 h2
  have hAR := ratio n _ _ _ hrd
  obtain ⟨hN0, hNv⟩ := val_pr_rc p (nR n) _ k htk (fac_nR n p j (by omega) hp2)
  obtain ⟨hR0, hRv⟩ := val_pr_rc p (Rj n j) _ k htk (fac_Rj n p j (by omega) hp2)
  have hR0' : ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hR0
  have hN0' : ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hA := eq_div_of_mul_eq hR0' hAR
  have hcnt : rc (Rj n j) p k + (dR n).count (-(j : ℤ)) = rc (dR n) p k :=
    rc_filter_ne p (dR n) _ k htk
  have hc2 : (dR n).count (-(j : ℤ)) = 2 := by
    rw [dR, Multiset.count_add, count_Icc, count_Icc, ite_eq_left (by omega),
      ite_eq_left (by omega)]
  rw [hc2] at hcnt
  refine ⟨by rw [hA]; exact div_ne_zero hN0' hR0', ?_, hAR, by rw [hV]; ring⟩
  rw [hA, padicValRat.div hN0' hR0', hNv, hRv]
  omega

/-- Simple poles: `a_j = 0` and `v_p(b_j) = c_k - d_k + 1`. -/
theorem val_simple (n j k : ℕ) (hp2 : 30 * n < p ^ 2)
    (hj : (n ≤ j ∧ j < 2 * n) ∨ (16 * n < j ∧ j ≤ 17 * n)) (htk : (-(j : ℤ)) % p = k) :
    (-1) ^ n * U n j / Cn n = 0 ∧ (-1) ^ n * V n j / Cn n ≠ 0 ∧
      padicValRat p ((-1) ^ n * V n j / Cn n) = (rc (nR n) p k : ℤ) - rc (dR n) p k + 1 := by
  have hroot : U n j = 0 ∧
      (-1) ^ n * V n j * ((10 * n).factorial : ℚ) ^ 3 * ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) =
        ((15 * n).factorial : ℚ) ^ 2 * ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) := by
    rcases hj with h | h
    · exact root_simple_lo n j h.1 h.2
    · exact root_simple_hi n j h.1 h.2
  have hj17 : j ≤ 17 * n := by omega
  have hAR := ratio n _ _ _ hroot.2
  obtain ⟨hN0, hNv⟩ := val_pr_rc p (nR n) _ k htk (fac_nR n p j hj17 hp2)
  obtain ⟨hR0, hRv⟩ := val_pr_rc p (Rj n j) _ k htk (fac_Rj n p j hj17 hp2)
  have hR0' : ((pr (Rj n j) (-(j : ℤ)) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hR0
  have hN0' : ((pr (nR n) (-(j : ℤ)) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hA := eq_div_of_mul_eq hR0' hAR
  have hcnt : rc (Rj n j) p k + (dR n).count (-(j : ℤ)) = rc (dR n) p k :=
    rc_filter_ne p (dR n) _ k htk
  have hc1 : (dR n).count (-(j : ℤ)) = 1 := by
    rw [dR, Multiset.count_add, count_Icc, count_Icc]
    split_ifs <;> omega
  rw [hc1] at hcnt
  refine ⟨by rw [hroot.1, mul_zero, zero_div], by rw [hA]; exact div_ne_zero hN0' hR0', ?_⟩
  rw [hA, padicValRat.div hN0' hR0', hNv, hRv]
  omega

end Pfq54.RA
