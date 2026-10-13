/-
# Auxiliary lemmas for `residue_block.lean` (sorry-free)

The root multisets of `F_n(t)`, residue-class counts, and the complete-residue polynomial `T`.
-/
import upper_range_bound

open Finset

noncomputable section

namespace Pfq54.RA

open Pfq54

/-- Roots of the numerator of `F_n` (same as `numRoots`). -/
def nR (n : ℕ) : Multiset ℤ :=
  (Icc (1 : ℤ) (10 * n)).val + (Icc ((n : ℤ) + 1) (11 * n)).val +
    (Icc (2 * (n : ℤ) + 1) (12 * n)).val

/-- Roots of the denominator of `F_n` (same as `denRoots`). -/
def dR (n : ℕ) : Multiset ℤ :=
  (Icc (-(17 * n : ℤ)) (-n)).val + (Icc (-(16 * n : ℤ)) (-(2 * n))).val

/-- Number of elements congruent to `k` (same as `resCount`). -/
def rc (s : Multiset ℤ) (p k : ℕ) : ℕ := (s.filter fun x => x % (p : ℤ) = k).card

theorem ite_one {c : Prop} [Decidable c] (h : c) : (if c then (1 : ℤ) else 0) = 1 := ite_eq_left h

theorem ite_zero {c : Prop} [Decidable c] (h : ¬c) : (if c then (1 : ℤ) else 0) = 0 :=
  ite_eq_right h

/-- The elements of `[a, b]` in the class of `k` modulo `p`, when `[a, b]` meets at most the
three candidates `k + j₀p, k + (j₀+1)p, k + (j₀+2)p`. -/
theorem filter_class (a b p k j0 : ℤ) (hp : 0 < p) (hk0 : 0 ≤ k) (hkp : k < p)
    (hlo : k + (j0 - 1) * p < a) (hhi : b < k + (j0 + 3) * p) :
    (Icc a b).filter (fun x => x % p = k) =
      ({k + j0 * p, k + (j0 + 1) * p, k + (j0 + 2) * p} : Finset ℤ).filter
        (fun x => a ≤ x ∧ x ≤ b) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hax, hxb⟩, hx⟩
    have hq : x = k + (x / p) * p := by
      have := Int.emod_add_mul_ediv x p
      rw [hx] at this
      linarith
    have h1 : j0 ≤ x / p := by
      by_contra h
      have : x / p ≤ j0 - 1 := by omega
      nlinarith
    have h2 : x / p ≤ j0 + 2 := by
      by_contra h
      have : j0 + 3 ≤ x / p := by omega
      nlinarith
    refine ⟨?_, hax, hxb⟩
    rcases (show x / p = j0 ∨ x / p = j0 + 1 ∨ x / p = j0 + 2 by omega) with h | h | h <;>
      rw [hq, h] <;> simp
  · rintro ⟨hx, hax, hxb⟩
    refine ⟨⟨hax, hxb⟩, ?_⟩
    rcases hx with rfl | rfl | rfl <;> rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt hk0 hkp]

/-- Elements of `[a, b]` in the class of `k` modulo `p`, when `[a, b]` meets at most the three
candidates `k + j₀p, k + (j₀+1)p, k + (j₀+2)p`. -/
theorem card_class (a b p k j0 : ℤ) (hp : 0 < p) (hk0 : 0 ≤ k) (hkp : k < p)
    (hlo : k + (j0 - 1) * p < a) (hhi : b < k + (j0 + 3) * p) :
    (((Icc a b).filter fun x => x % p = k).card : ℤ) =
      (if a ≤ k + j0 * p ∧ k + j0 * p ≤ b then 1 else 0) +
      (if a ≤ k + (j0 + 1) * p ∧ k + (j0 + 1) * p ≤ b then 1 else 0) +
      (if a ≤ k + (j0 + 2) * p ∧ k + (j0 + 2) * p ≤ b then 1 else 0) := by
  have key := filter_class a b p k j0 hp hk0 hkp hlo hhi
  have hne1 : k + j0 * p ∉ ({k + (j0 + 1) * p, k + (j0 + 2) * p} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h <;> nlinarith
  have hne2 : k + (j0 + 1) * p ∉ ({k + (j0 + 2) * p} : Finset ℤ) := by
    simp only [Finset.mem_singleton]
    intro h; nlinarith
  rw [key, Finset.card_filter, Finset.sum_insert hne1, Finset.sum_insert hne2,
    Finset.sum_singleton]
  push_cast
  split_ifs <;> simp

/-- Residue counts of the root multisets as sums of indicators. -/
theorem rc_num (n p k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p) :
    (rc (nR n) p k : ℤ) =
      ((if 1 ≤ (k : ℤ) + (0) * p ∧ (k : ℤ) + (0) * p ≤ 10 * (n : ℤ) then 1 else 0) +
        (if 1 ≤ (k : ℤ) + (0 + 1) * p ∧ (k : ℤ) + (0 + 1) * p ≤ 10 * (n : ℤ) then 1 else 0) +
        (if 1 ≤ (k : ℤ) + (0 + 2) * p ∧ (k : ℤ) + (0 + 2) * p ≤ 10 * (n : ℤ) then 1 else 0)) +
      ((if (n : ℤ) + 1 ≤ (k : ℤ) + (0) * p ∧ (k : ℤ) + (0) * p ≤ 11 * (n : ℤ) then 1 else 0) +
        (if (n : ℤ) + 1 ≤ (k : ℤ) + (0 + 1) * p ∧ (k : ℤ) + (0 + 1) * p ≤ 11 * (n : ℤ) then 1 else 0) +
        (if (n : ℤ) + 1 ≤ (k : ℤ) + (0 + 2) * p ∧ (k : ℤ) + (0 + 2) * p ≤ 11 * (n : ℤ) then 1 else 0)) +
      ((if 2 * (n : ℤ) + 1 ≤ (k : ℤ) + (0) * p ∧ (k : ℤ) + (0) * p ≤ 12 * (n : ℤ) then 1 else 0) +
        (if 2 * (n : ℤ) + 1 ≤ (k : ℤ) + (0 + 1) * p ∧ (k : ℤ) + (0 + 1) * p ≤ 12 * (n : ℤ) then 1 else 0) +
        (if 2 * (n : ℤ) + 1 ≤ (k : ℤ) + (0 + 2) * p ∧ (k : ℤ) + (0 + 2) * p ≤ 12 * (n : ℤ) then 1 else 0)) := by
  have hp : (0 : ℤ) < p := by omega
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hkp : (k : ℤ) < p := Int.ofNat_lt.mpr hk
  have e : ∀ (a b : ℤ), ((Icc a b).val.filter fun x => x % (p : ℤ) = k).card =
      ((Icc a b).filter fun x => x % (p : ℤ) = k).card := fun a b => rfl
  unfold rc nR
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add, e, e, e,
    Nat.cast_add, Nat.cast_add, card_class 1 (10 * n) p k 0 hp hk0 hkp (by omega) (by omega),
    card_class ((n : ℤ) + 1) (11 * n) p k 0 hp hk0 hkp (by omega) (by omega),
    card_class (2 * (n : ℤ) + 1) (12 * n) p k 0 hp hk0 hkp (by omega) (by omega)]

theorem rc_den (n p k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p) :
    (rc (dR n) p k : ℤ) =
      ((if -(17 * (n : ℤ)) ≤ (k : ℤ) + (-3) * p ∧ (k : ℤ) + (-3) * p ≤ -(n : ℤ) then 1 else 0) +
        (if -(17 * (n : ℤ)) ≤ (k : ℤ) + (-3 + 1) * p ∧ (k : ℤ) + (-3 + 1) * p ≤ -(n : ℤ) then 1 else 0) +
        (if -(17 * (n : ℤ)) ≤ (k : ℤ) + (-3 + 2) * p ∧ (k : ℤ) + (-3 + 2) * p ≤ -(n : ℤ) then 1 else 0)) +
      ((if -(16 * (n : ℤ)) ≤ (k : ℤ) + (-3) * p ∧ (k : ℤ) + (-3) * p ≤ -(2 * (n : ℤ)) then 1 else 0) +
        (if -(16 * (n : ℤ)) ≤ (k : ℤ) + (-3 + 1) * p ∧ (k : ℤ) + (-3 + 1) * p ≤ -(2 * (n : ℤ)) then 1 else 0) +
        (if -(16 * (n : ℤ)) ≤ (k : ℤ) + (-3 + 2) * p ∧ (k : ℤ) + (-3 + 2) * p ≤ -(2 * (n : ℤ)) then 1 else 0)) := by
  have hp : (0 : ℤ) < p := by omega
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hkp : (k : ℤ) < p := Int.ofNat_lt.mpr hk
  have e : ∀ (a b : ℤ), ((Icc a b).val.filter fun x => x % (p : ℤ) = k).card =
      ((Icc a b).filter fun x => x % (p : ℤ) = k).card := fun a b => rfl
  unfold rc dR
  rw [Multiset.filter_add, Multiset.card_add, e, e, Nat.cast_add,
    card_class (-(17 * (n : ℤ))) (-(n : ℤ)) p k (-3) hp hk0 hkp (by omega) (by omega),
    card_class (-(16 * (n : ℤ))) (-(2 * (n : ℤ))) p k (-3) hp hk0 hkp (by omega) (by omega)]

/-- Root counts modulo `p`: `d_k ≤ c_k + 1`, with equality exactly on the support. -/
theorem root_count' (n p k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p) :
    (rc (dR n) p k : ℤ) ≤ rc (nR n) p k + 1 ∧
      ((rc (dR n) p k : ℤ) = rc (nR n) p k + 1 ↔
        (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p)) := by
  rw [rc_num n p k h8 h11 hk, rc_den n p k h8 h11 hk]
  simp (disch := omega) only [ite_zero]
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · (try simp (disch := omega) only [ite_one, ite_zero]); (try split_ifs) <;> omega
  rcases le_or_gt k n with h1 | h1
  · (try simp (disch := omega) only [ite_one, ite_zero]); (try split_ifs) <;> omega
  rcases le_or_gt k (2 * n) with h2 | h2
  · (try simp (disch := omega) only [ite_one, ite_zero]); (try split_ifs) <;> omega
  rcases le_or_gt (k + 2 * n) p with h3 | h3
  · (try simp (disch := omega) only [ite_one, ite_zero]); (try split_ifs) <;> omega
  · (try simp (disch := omega) only [ite_one, ite_zero]); (try split_ifs) <;> omega

end Pfq54.RA
