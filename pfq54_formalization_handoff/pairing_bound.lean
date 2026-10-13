/-
# Blueprint of `pairing_bound` (manuscript eq. (arith-pairbound))

Node `Pfq54.pairing_bound` of `Blueprint_pfq54.lean`: for an eligible prime `p`
(`p > 29`, `p² > 30n`, `p ∤ n`), `p^{φ(n/p)}` divides `Z_{0,n}, Z_{3,n}, Z_{4,n}`.

Proof (manuscript Appendix D): `φ(x)` is `0` or the value of one of the eight pairing rows
([1]); each row is realized by a permutation `b` ([2]); for eligible `p` every factorial argument
is `< p²`, so Legendre's formula has one level ([3]) and `v_p(λ_{n,b})` is minus the row value
([4]). From `λ_{n,b} Z_{i,n} ∈ ℤ` (`permutation_lemma`) and `λ_{n,b} ≠ 0` ([5]) we get
`v_p(Z_{i,n}) ≥ -v_p(λ_{n,b})` ([6]); an integer with `v_p ≥ k` is divisible by `p^k` ([7]).

The valuation predicate `ValGE p k x` (`x = 0 ∨ k ≤ v_p(x)`) and its closure lemmas are the
proved ones of the previous proof (`blueprints/ZetasAux.lean`, namespace `ZetasIrr.Aux`).
-/
import permutation_lemma
import ZetasAux

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54
open ZetasIrr.Aux (ValGE)

/-- The value of a pairing row `(L, D)` at `x`: `c(x) - ∑_{d∈D} ⌊dx⌋ + ∑_{l∈L} ⌊lx⌋`. -/
def rowVal (LD : List ℤ × List ℤ) (x : ℚ) : ℤ :=
  cfun x - (LD.2.map fun d => ⌊(d : ℚ) * x⌋).sum + (LD.1.map fun l => ⌊(l : ℚ) * x⌋).sum

/-- The same value for the lengths `L_b = (10+b₀, 11+b₁, 12+b₂)`, `J_b = (16-b₃, 17-b₄)` of a
permutation `b = shift ∘ σ`. -/
def rowValPerm (σ : Equiv.Perm (Fin 5)) (x : ℚ) : ℤ :=
  let b : Fin 5 → ℤ := fun i => shift (σ i)
  cfun x - ⌊((16 - b 3 : ℤ) : ℚ) * x⌋ - ⌊((17 - b 4 : ℤ) : ℚ) * x⌋ +
    ⌊((10 + b 0 : ℤ) : ℚ) * x⌋ + ⌊((11 + b 1 : ℤ) : ℚ) * x⌋ + ⌊((12 + b 2 : ℤ) : ℚ) * x⌋

/-- **[1] The profile is a maximum of row values.** `φ(x) ≥ 0`, and `φ(x)` is `0` or equal to
the value of one of the eight rows.
* Estimated proof length: ≈ 15 lines (induction over the `foldr`, `max_choice`).
* Directly from the manuscript: yes (definition of `φ`). -/
theorem phi_cases (x : ℚ) :
    0 ≤ phi x ∧ (phi x = 0 ∨ ∃ LD ∈ pairings, phi x = rowVal LD x) := by
  have key : ∀ l : List (List ℤ × List ℤ),
      0 ≤ l.foldr (fun LD m => max m (rowVal LD x)) 0 ∧
        (l.foldr (fun LD m => max m (rowVal LD x)) 0 = 0 ∨
          ∃ LD ∈ l, l.foldr (fun LD m => max m (rowVal LD x)) 0 = rowVal LD x) := by
    intro l
    induction l with
    | nil => exact ⟨le_rfl, Or.inl rfl⟩
    | cons a l ih =>
      obtain ⟨h0, h1⟩ := ih
      rw [List.foldr_cons]
      refine ⟨le_max_of_le_left h0, ?_⟩
      rcases max_choice (l.foldr (fun LD m => max m (rowVal LD x)) 0) (rowVal a x) with h | h <;>
        rw [h]
      · rcases h1 with h1 | ⟨LD, hLD, h1⟩
        · exact Or.inl h1
        · exact Or.inr ⟨LD, List.mem_cons_of_mem _ hLD, h1⟩
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
  exact key pairings

/-- **[2] Every pairing row is realized by a permutation** (the column `b` of the table in
Appendix B: `(-2,2,1,-1,0)`, `(1,0,-1,2,-2)`, …).
* Estimated proof length: ≈ 25 lines (eight explicit `σ`, each checked by `decide` on
  `shift ∘ σ` and `ring_nf` on the floor sums).
* Directly from the manuscript: yes (the table lists `b` for each row). -/
theorem pairing_realized :
    ∀ LD ∈ pairings, ∃ σ : Equiv.Perm (Fin 5), ∀ x, rowVal LD x = rowValPerm σ x := by
  intro LD hLD
  simp only [pairings, List.mem_cons, List.not_mem_nil, or_false] at hLD
  rcases hLD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Equiv.ofBijective ![0, 4, 3, 1, 2] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![3, 2, 1, 4, 0] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![1, 0, 4, 2, 3] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![4, 3, 2, 0, 1] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![3, 2, 4, 0, 1] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![1, 0, 2, 4, 3] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![2, 1, 0, 4, 3] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩
  · exact ⟨Equiv.ofBijective ![3, 0, 4, 1, 2] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift] <;> ring⟩

/-- **[3] Legendre's formula below `p²`**: `v_p(m!) = ⌊m/p⌋` for `m < p²`.
* Proof length: 5 lines. Proved below (the general level-by-level form is `fp_eq_sum_levels` in
  `blueprints/E34_le.lean`; Mathlib `padicValNat_factorial`).
* Directly from the manuscript: yes. -/
theorem padicValNat_factorial_small (p m : ℕ) [hp : Fact p.Prime] (hm : m < p ^ 2) :
    padicValNat p m.factorial = m / p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow (by omega) hm
  rw [padicValNat_factorial hlog]
  simp

/-- **[4] The valuation of `λ_{n,b}` at an eligible prime**:
`v_p(λ_{n,b}) = -(c(n/p) - ∑_{J_b} ⌊e n/p⌋ + ∑_{L_b} ⌊ℓ n/p⌋)`.
* Uses: [3] (all factorial arguments are `≤ 19n < p²`), `ZetasIrr.Aux.padicValRat_factorial_prod`,
  `⌊(e n)/p⌋ = ⌊e · (n/p)⌋`.
* Estimated proof length: ≈ 30 lines.
* Directly from the manuscript: yes ("Legendre's formula therefore gives …"). -/
theorem padicValRat_lam (σ : Equiv.Perm (Fin 5)) (n p : ℕ) (hp : Eligible n p) :
    padicValRat p (lam σ n) = -rowValPerm σ ((n : ℚ) / p) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hb : ∀ i, -2 ≤ shift i ∧ shift i ≤ 2 := by intro i; fin_cases i <;> decide
  have hsq : 19 * n < p ^ 2 := lt_of_le_of_lt (by omega) hp.2.2.1
  have key : ∀ e : ℤ, 0 ≤ e → e ≤ 19 →
      padicValRat p (((e * n).toNat.factorial : ℕ) : ℚ) = ⌊(e : ℚ) * ((n : ℚ) / p)⌋ := by
    intro e h0 h1
    have hm : (e * n).toNat ≤ 19 * n := Int.toNat_le.mpr (by push_cast; nlinarith)
    rw [padicValRat.of_nat, padicValNat_factorial_small p _ (lt_of_le_of_lt hm hsq)]
    have hc : (e : ℚ) * ((n : ℚ) / p) = (((e * n).toNat : ℕ) : ℚ) / (p : ℕ) := by
      rw [show (((e * n).toNat : ℕ) : ℚ) = ((e * n : ℤ) : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg (mul_nonneg h0 (Int.natCast_nonneg n))]
      push_cast; ring
    rw [hc, Rat.floor_natCast_div_natCast, Int.natCast_div]
  have k10 := key 10 (by norm_num) (by norm_num)
  have k15 := key 15 (by norm_num) (by norm_num)
  have kA := key (16 - shift (σ 3)) (by linarith [hb (σ 3)]) (by linarith [hb (σ 3)])
  have kB := key (17 - shift (σ 4)) (by linarith [hb (σ 4)]) (by linarith [hb (σ 4)])
  have kC := key (10 + shift (σ 0)) (by linarith [hb (σ 0)]) (by linarith [hb (σ 0)])
  have kD := key (11 + shift (σ 1)) (by linarith [hb (σ 1)]) (by linarith [hb (σ 1)])
  have kE := key (12 + shift (σ 2)) (by linarith [hb (σ 2)]) (by linarith [hb (σ 2)])
  simp only [Int.cast_ofNat] at k10 k15
  unfold lam rowValPerm cfun
  dsimp only
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.mul (by positivity)
    (by positivity), padicValRat.mul (by positivity) (by positivity), padicValRat.pow,
    padicValRat.mul (by positivity) (by positivity), padicValRat.mul (by positivity)
    (by positivity), padicValRat.mul (by positivity) (by positivity), padicValRat.pow,
    k10, k15, kA, kB, kC, kD, kE]
  push_cast
  ring

/-- **[5]** `λ_{n,b} ≠ 0` (a quotient of factorials).
* Estimated proof length: ≈ 4 lines (`positivity`).
* Directly from the manuscript: yes. -/
theorem lam_ne_zero (σ : Equiv.Perm (Fin 5)) (n : ℕ) : lam σ n ≠ 0 := by
  unfold lam
  dsimp only
  positivity

/-- **[6] Valuation transfer.** If `λ ≠ 0` and `λ x ∈ ℤ`, then `v_p(x) ≥ -v_p(λ)`
("integrality of `λ_{n,b} Z_{i,n}` gives `v_p(Z_{i,n}) ≥ -v_p(λ_{n,b})`").
* Estimated proof length: ≈ 10 lines (`padicValRat.mul`, `padicValRat.of_int`).
* Directly from the manuscript: yes. -/
theorem valGE_of_lam_mul {p : ℕ} [Fact p.Prime] (l x : ℚ) (hl : l ≠ 0)
    (hlx : ∃ z : ℤ, l * x = z) : ValGE p (-padicValRat p l) x := by
  rcases eq_or_ne x 0 with hx | hx
  · exact Or.inl hx
  right
  obtain ⟨z, hz⟩ := hlx
  have h1 : padicValRat p (l * x) = padicValRat p l + padicValRat p x := padicValRat.mul hl hx
  have h2 : 0 ≤ padicValRat p (l * x) := by
    rw [hz, padicValRat.of_int]; exact Nat.cast_nonneg _
  linarith

/-- **[7] From valuations to divisibility.** An integer `x` with `v_p(x) ≥ k` is `p^k` times an
integer.
* Proof length: 12 lines. Proved below (adapted from `exists_int_of_padicValRat_nonneg` in
  `blueprints/Delta_mul_Rmat_integral.lean`; Mathlib `padicValInt_dvd_iff`).
* Directly from the manuscript: yes. -/
theorem int_dvd_of_valGE {p : ℕ} [Fact p.Prime] (x : ℚ) (hx : ∃ z : ℤ, x = z) (k : ℕ)
    (hv : ValGE p k x) : ∃ z : ℤ, x = (p : ℚ) ^ k * z := by
  obtain ⟨z, rfl⟩ := hx
  have hdvd : (p : ℤ) ^ k ∣ z := by
    refine (padicValInt_dvd_iff k z).mpr ?_
    rcases eq_or_ne z 0 with h | h
    · exact Or.inl h
    · right
      rcases hv with h0 | hv
      · exact absurd (by exact_mod_cast h0) h
      · rw [padicValRat.of_int] at hv
        exact_mod_cast hv
  obtain ⟨w, hw⟩ := hdvd
  exact ⟨w, by rw [hw]; push_cast; ring⟩

/-- **`pairing_bound`** (node of `Blueprint_pfq54.lean`). Proved from [1], [2], [4]–[7],
`permutation_lemma` and `Z_integral`. -/
theorem pairing_bound (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (i : Fin 3) :
    ∃ z : ℤ, Zv n i = (p : ℚ) ^ (phi ((n : ℚ) / p)).toNat * z := by
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨hφ0, hφ⟩ := phi_cases ((n : ℚ) / p)
  have hZ := (Z_integral n hn).2.2.1 i
  rcases hφ with h0 | ⟨LD, hLD, hrow⟩
  · obtain ⟨z, hz⟩ := hZ
    exact ⟨z, by rw [h0, hz]; simp⟩
  · obtain ⟨σ, hσ⟩ := pairing_realized LD hLD
    have hv := valGE_of_lam_mul (p := p) (lam σ n) (Zv n i) (lam_ne_zero σ n)
      ((permutation_lemma σ n hn).2.2.2 i)
    refine int_dvd_of_valGE (Zv n i) hZ _ (hv.mono ?_)
    rw [padicValRat_lam σ n p hp, neg_neg, ← hσ ((n : ℚ) / p), ← hrow,
      Int.toNat_of_nonneg hφ0]

end Pfq54.BP
