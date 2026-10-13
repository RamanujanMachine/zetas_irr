/-
# Auxiliary lemmas for `log_G_ge.lean` (sorry-free)

`θ` as a sum over the primes `p ≤ 19n`, prime sums over open intervals, and list sums.
-/
import Mathlib

open Finset Filter Topology

noncomputable section

namespace Pfq54.LG

/-- `θ(X) = ∑_{p ≤ 19n prime, p ≤ X} log p` for `X ≤ 19n`. -/
theorem theta_sum (n : ℕ) (X : ℝ) (hX : X ≤ 19 * n) :
    Chebyshev.theta X = ∑ p ∈ (range (19 * n + 1)).filter Nat.Prime,
      if (p : ℝ) ≤ X then Real.log p else 0 := by
  rw [Chebyshev.theta, ← Finset.sum_filter, Finset.filter_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  rw [mem_filter, mem_filter, mem_Ioc, mem_range]
  constructor
  · rintro ⟨⟨hp0, hpX⟩, hpr⟩
    have hX0 : 0 ≤ X := by
      by_contra h
      rw [Nat.floor_of_nonpos (le_of_lt (not_le.mp h))] at hpX
      omega
    have h1 : (p : ℝ) ≤ X := (Nat.le_floor_iff hX0).mp hpX
    have h2 : p ≤ 19 * n := by exact_mod_cast h1.trans hX
    exact ⟨by omega, hpr, h1⟩
  · rintro ⟨-, hpr, hpX⟩
    exact ⟨⟨hpr.pos, Nat.le_floor hpX⟩, hpr⟩

/-- Primes in `(Y, X)`: `θ(X) - θ(Y) - log(19n) ≤ ∑_{Y < p < X} log p`. -/
theorem interval_sum (n : ℕ) (hn : 1 ≤ n) (Y X : ℝ) (hYX : Y ≤ X) (hX : X ≤ 19 * n) :
    Chebyshev.theta X - Chebyshev.theta Y - Real.log (19 * n) ≤
      ∑ p ∈ (range (19 * n + 1)).filter Nat.Prime,
        if Y < p ∧ (p : ℝ) < X then Real.log p else 0 := by
  rw [theta_sum n X hX, theta_sum n Y (hYX.trans hX)]
  set P := (range (19 * n + 1)).filter Nat.Prime
  have hR : ∑ p ∈ P, (if (p : ℝ) = X then Real.log p else 0) ≤ Real.log (19 * n) := by
    have hn19 : (1 : ℝ) ≤ 19 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    by_cases hm : ∃ m ∈ P, (m : ℝ) = X
    · obtain ⟨m, hm, hmX⟩ := hm
      rw [Finset.sum_eq_single m (fun b _ hb => ite_eq_right fun h => hb (by
        exact_mod_cast h.trans hmX.symm)) (fun h => absurd hm h), ite_eq_left hmX]
      obtain ⟨hm1, hmp⟩ := mem_filter.mp hm
      have hm19 : (m : ℝ) ≤ 19 * n := by
        have : m ≤ 19 * n := by rw [mem_range] at hm1; omega
        exact_mod_cast this
      exact Real.log_le_log (by exact_mod_cast hmp.pos) hm19
    · rw [Finset.sum_eq_zero fun p hp => ite_eq_right fun h => hm ⟨p, hp, h⟩]
      exact Real.log_nonneg hn19
  have hpt : ∀ p ∈ P, (if (p : ℝ) ≤ X then Real.log p else 0) -
      (if (p : ℝ) ≤ Y then Real.log p else 0) -
        (if Y < p ∧ (p : ℝ) < X then Real.log p else 0) ≤
          (if (p : ℝ) = X then Real.log p else 0) := by
    intro p _
    have hl := Real.log_natCast_nonneg p
    have h4 : 0 ≤ (if (p : ℝ) = X then Real.log p else 0) := by
      split_ifs
      · exact hl
      · exact le_rfl
    by_cases h1 : (p : ℝ) ≤ Y
    · rw [ite_eq_left (h1.trans hYX), ite_eq_left h1,
        ite_eq_right fun h => absurd h.1 (not_lt.mpr h1)]
      linarith
    by_cases h2 : (p : ℝ) < X
    · rw [ite_eq_left h2.le, ite_eq_right h1, ite_eq_left ⟨not_le.mp h1, h2⟩]
      linarith
    by_cases h3 : (p : ℝ) ≤ X
    · rw [ite_eq_left h3, ite_eq_right h1, ite_eq_right fun h => h2 h.2,
        ite_eq_left (le_antisymm h3 (not_lt.mp h2))]
      linarith
    · rw [ite_eq_right h3, ite_eq_right h1, ite_eq_right fun h => h2 h.2]
      linarith
  have := (Finset.sum_le_sum hpt).trans hR
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

theorem lsum_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ r ∈ l, f r ≤ g r) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun r hr => h r (List.mem_cons_of_mem a hr))

theorem lsum_swap {α : Type*} (l : List α) (s : Finset ℕ) (g : α → ℕ → ℝ) :
    ∑ p ∈ s, (l.map fun r => g r p).sum = (l.map fun r => ∑ p ∈ s, g r p).sum := by
  induction l with
  | nil => exact Finset.sum_const_zero
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

theorem lsum_lin {α : Type*} (l : List α) (f g : α → ℝ) (c d : ℝ) :
    (l.map fun r => f r * c - d * g r).sum = (l.map f).sum * c - d * (l.map g).sum := by
  induction l with
  | nil => rw [List.map_nil, List.map_nil, List.map_nil, List.sum_nil, zero_mul, mul_zero,
      sub_zero]
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.sum_cons,
      ih]
    ring

theorem eventually_list {α : Type*} (l : List α) (P : α → ℕ → Prop)
    (h : ∀ r ∈ l, ∀ᶠ n in atTop, P r n) : ∀ᶠ n in atTop, ∀ r ∈ l, P r n := by
  induction l with
  | nil => exact Eventually.of_forall fun n r hr => absurd hr List.not_mem_nil
  | cons a l ih =>
    filter_upwards [h a List.mem_cons_self, ih fun r hr => h r (List.mem_cons_of_mem a hr)]
      with n h1 h2
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h1
    · exact h2 r hr

/-- `1/(k+b) · n < p < 1/(k+a) · n` iff `k + a < n/p < k + b`. -/
theorem cond_iff (n p k : ℕ) (hp : 0 < p) (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    (1 / ((k : ℝ) + b) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + a) * n) ↔
      ((k : ℚ) + a < (n : ℚ) / p ∧ (n : ℚ) / p < k + b) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hk : ∀ c : ℚ, 0 < c → (0 : ℝ) < (k : ℝ) + c := fun c hc => by
    have : (0 : ℝ) < c := by exact_mod_cast hc
    positivity
  have e1 : ((k : ℚ) + a < (n : ℚ) / p) ↔ ((k : ℝ) + a < (n : ℝ) / p) := by
    rw [← Rat.cast_lt (K := ℝ)]
    push_cast
    exact Iff.rfl
  have e2 : ((n : ℚ) / p < k + b) ↔ ((n : ℝ) / p < (k : ℝ) + b) := by
    rw [← Rat.cast_lt (K := ℝ)]
    push_cast
    exact Iff.rfl
  rw [e1, e2, one_div_mul_eq_div, one_div_mul_eq_div, div_lt_iff₀ (hk b hb), lt_div_iff₀ (hk a ha),
    div_lt_iff₀ hpR, lt_div_iff₀ hpR, mul_comm (p : ℝ), mul_comm (p : ℝ)]
  exact And.comm

end Pfq54.LG
