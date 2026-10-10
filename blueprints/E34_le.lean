/-
# Blueprint for `ZetasIrr.E34_le`

Statement (as in `blueprint.lean`):
  `E₃₄(N,p) ≤ max(v_p(6), 6 ℓ_p(29N+1))` for every prime `p`.

Source: PDF Part IV ("For completeness, `E_{d4}(N,p) ≤ 6ℓ_p(29N+1)` …") and Part VII §4
("At each Legendre level the dual top-coefficient valuation is at least `m_d(k) - 4` …").

Strategy. `E₃₄ ≤ max(E_d, E_{d4})` in both cases of its definition. Both `E_d` and `E_{d4}` are
maxima over `13N+1 ≤ k ≤ 29N+1` of `loss(k) - V_d(k)`. Level by level in Legendre's formula,
`V_d(k) ≥ (m_d(k) - 4) ℓ_p(29N+1)` while the losses are at most `(m_d(k)+1) ℓ_p(29N+1)` (for `E_d`)
and `(m_d(k)+2) ℓ_p(29N+1)` (for `E_{d4}`). This gives `E_d ≤ max(v_p(6), 5ℓ)` and `E_{d4} ≤ 6ℓ`.

| # | Supporting lemma                  | Est. lines | Directly from PDF? |
|---|-----------------------------------|-----------:|--------------------|
| 1 | `E34_le_max_Ed_Ed4`               |   (proved) | Yes                |
| 2 | `maxOn_le`                        |   (proved) | Yes (definition)   |
| 3 | `ellp_nonneg`                     |   (proved) | Yes (definition)   |
| 4 | `mult_Id_bounds`                  |         25 | Yes                |
| 5 | `Vd_ge`                           |   (proved) | Partially          |
| 6 | `loss_Ed_le`                      |         40 | Yes                |
| 7 | `loss_Ed4_le`                     |         40 | Yes                |

All supporting lemmas are proved; the file contains no `sorry`.
-/
import ZetasAux

open Filter Topology Real

noncomputable section

namespace ZetasIrr

/-- **[1] `E₃₄ ≤ max(E_d, E_{d4})`.** Immediate from the definition of `E₃₄`
(`min(E_o,E_d) ≤ E_d`, `min(E_{o4},E_{d4}) ≤ E_{d4}`).
* Lines: proved here.
* Directly from the PDF: yes (definition of `E₃₄`, Part IV). -/
theorem E34_le_max_Ed_Ed4 (N p : ℕ) : E34 N p ≤ max (Ed N p) (Ed4 N p) := by
  unfold E34
  split_ifs
  · exact max_le_max (min_le_right _ _) (min_le_right _ _)
  · exact le_rfl

/-- **[2] Bounding `maxOn`.** If every value is `≤ c` and `0 ≤ c`, then `maxOn s f ≤ c`.
* Lines: proved here.
* Directly from the PDF: yes (it is the convention for the empty maximum). -/
theorem maxOn_le (s : Finset ℤ) (f : ℤ → ℤ) (c : ℤ) (hc : 0 ≤ c) (h : ∀ k ∈ s, f k ≤ c) :
    maxOn s f ≤ c := by
  unfold maxOn
  split_ifs with hs
  · exact Finset.sup'_le hs f h
  · exact hc

/-- **[3] `ℓ_p ≥ 0`.**
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem ellp_nonneg (p : ℕ) (m : ℤ) : 0 ≤ ellp p m := by
  unfold ellp; positivity

/-- **[4] Pole multiplicity on the dual range.** For `13N+1 ≤ k ≤ 29N+1`, `1 ≤ m_d(k) ≤ 2`.
The two intervals `[13N+1, 28N+1]` and `[14N+1, 29N+1]` cover the range.
Used in the proofs of [6] and [7] (it gives `m_d(k) - 1 ≥ 0`).
* Lines: ≈ 25 (case split on the two interval memberships, `omega`).
* Directly from the PDF: yes (definition of `𝓘_d`). -/
theorem mult_Id_bounds (N : ℕ) (k : ℤ) (hk1 : 13 * N + 1 ≤ k) (hk2 : k ≤ 29 * N + 1) :
    1 ≤ mult (Id N) k ∧ mult (Id N) k ≤ 2 := by
  simp only [mult, Id, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-! ### Legendre's formula, level by level -/

/-- Legendre's formula `f_p(m) = ∑_{1 ≤ i ≤ ℓ_p(M)} ⌊m/p^i⌋` for every `m ≤ M`
(Mathlib `padicValNat_factorial`; the levels `p^i > M` contribute nothing). -/
theorem fp_eq_sum_levels {p : ℕ} (hp : p.Prime) (M : ℕ) (m : ℤ) (hm : m ≤ M) :
    fp p m = ∑ i ∈ Finset.Ico 1 (Nat.log p M + 1), ((m.toNat / p ^ i : ℕ) : ℤ) := by
  have := Fact.mk hp
  have hlog : Nat.log p m.toNat < Nat.log p M + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  unfold fp
  rw [padicValNat_factorial hlog, Nat.cast_sum]

/-- The three branches of `G_p`. -/
theorem Gp_mid (p : ℕ) (k a b : ℤ) (h1 : a ≤ k) (h2 : k ≤ b) :
    Gp p k a b = fp p (k - a) + fp p (b - k) := by
  unfold Gp; simp [not_lt.mpr h1, not_lt.mpr h2]

theorem Gp_left (p : ℕ) (k a b : ℤ) (h : k < a) :
    Gp p k a b = fp p (b - k) - fp p (a - k - 1) := by
  unfold Gp; simp [h]

theorem Gp_right (p : ℕ) (k a b : ℤ) (h1 : ¬ k < a) (h2 : b < k) :
    Gp p k a b = fp p (k - a) - fp p (k - b - 1) := by
  unfold Gp; simp [h1, h2]

/-- `⌊(a+b)/q⌋ ≤ ⌊a/q⌋ + ⌊b/q⌋ + 1`. -/
theorem add_div_le_add_div_succ (a b q : ℕ) (hq : 0 < q) : (a + b) / q ≤ a / q + b / q + 1 := by
  rw [Nat.add_div hq]; split_ifs <;> omega

/-- **Double-pole level.** Three positive and seven negative floors with net linear argument
one contribute at least `-2 = m_d - 4`. -/
theorem level_double (q a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : ℕ) (hq : 0 < q)
    (h : a1 + a2 + a3 = b1 + b2 + b3 + b4 + b5 + b6 + b7 + 1) :
    (-2 : ℤ) ≤ ((a1 / q : ℕ) : ℤ) + ((a2 / q : ℕ) : ℤ) + ((a3 / q : ℕ) : ℤ) -
      ((b1 / q : ℕ) : ℤ) - ((b2 / q : ℕ) : ℤ) - ((b3 / q : ℕ) : ℤ) - ((b4 / q : ℕ) : ℤ) -
      ((b5 / q : ℕ) : ℤ) - ((b6 / q : ℕ) : ℤ) - ((b7 / q : ℕ) : ℤ) := by
  have h1 := add_div_le_add_div_succ (a1 + a2) a3 q hq
  have h2 := add_div_le_add_div_succ a1 a2 q hq
  have h3 : (b1 + b2 + b3 + b4 + b5 + b6 + b7) / q ≤ (a1 + a2 + a3) / q :=
    Nat.div_le_div_right (by omega)
  have h4 : (b1 + b2 + b3 + b4 + b5 + b6) / q + b7 / q ≤ (b1 + b2 + b3 + b4 + b5 + b6 + b7) / q :=
    Nat.div_add_div_le_add_div
  have h5 : (b1 + b2 + b3 + b4 + b5) / q + b6 / q ≤ (b1 + b2 + b3 + b4 + b5 + b6) / q :=
    Nat.div_add_div_le_add_div
  have h6 : (b1 + b2 + b3 + b4) / q + b5 / q ≤ (b1 + b2 + b3 + b4 + b5) / q :=
    Nat.div_add_div_le_add_div
  have h7 : (b1 + b2 + b3) / q + b4 / q ≤ (b1 + b2 + b3 + b4) / q := Nat.div_add_div_le_add_div
  have h8 : (b1 + b2) / q + b3 / q ≤ (b1 + b2 + b3) / q := Nat.div_add_div_le_add_div
  have h9 : b1 / q + b2 / q ≤ (b1 + b2) / q := Nat.div_add_div_le_add_div
  omega

/-- **Simple-pole level.** Four positive and six negative floors with net linear argument
zero contribute at least `-3 = m_d - 4`. -/
theorem level_simple (q a1 a2 a3 a4 b1 b2 b3 b4 b5 b6 : ℕ) (hq : 0 < q)
    (h : a1 + a2 + a3 + a4 = b1 + b2 + b3 + b4 + b5 + b6) :
    (-3 : ℤ) ≤ ((a1 / q : ℕ) : ℤ) + ((a2 / q : ℕ) : ℤ) + ((a3 / q : ℕ) : ℤ) +
      ((a4 / q : ℕ) : ℤ) - ((b1 / q : ℕ) : ℤ) - ((b2 / q : ℕ) : ℤ) - ((b3 / q : ℕ) : ℤ) -
      ((b4 / q : ℕ) : ℤ) - ((b5 / q : ℕ) : ℤ) - ((b6 / q : ℕ) : ℤ) := by
  have h1 := add_div_le_add_div_succ (a1 + a2 + a3) a4 q hq
  have h2 := add_div_le_add_div_succ (a1 + a2) a3 q hq
  have h3 := add_div_le_add_div_succ a1 a2 q hq
  have h4 : (b1 + b2 + b3 + b4 + b5 + b6) / q ≤ (a1 + a2 + a3 + a4) / q :=
    Nat.div_le_div_right (by omega)
  have h5 : (b1 + b2 + b3 + b4 + b5) / q + b6 / q ≤ (b1 + b2 + b3 + b4 + b5 + b6) / q :=
    Nat.div_add_div_le_add_div
  have h6 : (b1 + b2 + b3 + b4) / q + b5 / q ≤ (b1 + b2 + b3 + b4 + b5) / q :=
    Nat.div_add_div_le_add_div
  have h7 : (b1 + b2 + b3) / q + b4 / q ≤ (b1 + b2 + b3 + b4) / q := Nat.div_add_div_le_add_div
  have h8 : (b1 + b2) / q + b3 / q ≤ (b1 + b2 + b3) / q := Nat.div_add_div_le_add_div
  have h9 : b1 / q + b2 / q ≤ (b1 + b2) / q := Nat.div_add_div_le_add_div
  omega

/-- **[5] Level-wise lower bound for the dual top-coefficient valuation.**
`V_d(k) ≥ (m_d(k) - 4) ℓ_p(29N+1)` on the dual range.

Proof idea (PDF Part VII §4): write every `f_p(m)` with Legendre's formula
`f_p(m) = ∑_{i ≥ 1} ⌊m/p^i⌋` (Mathlib `padicValNat_factorial`) and every `G_p` likewise.
For a fixed level `q = p^i`:
* if `q > 29N+1`, every argument is `≤ 29N+1`, so the level contributes `0`;
* if `q ≤ 29N+1`, in the simple-pole case there are four positive and six negative floors with
  zero net linear argument, and in the double-pole case three positive and seven negative floors
  with net linear argument one; `⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋` bookkeeping gives a contribution
  `≥ m_d(k) - 4`.
Summing over the `ℓ_p(29N+1)` levels with `q ≤ 29N+1` gives the claim.
* Lines: proved here (Legendre expansion `fp_eq_sum_levels`, the per-level floor inequalities
  `level_double` and `level_simple`, and a three-way case split on the position of `k`).
* Directly from the PDF: partially. The PDF states the per-level counts but not the floor
  inequalities; they are written out for both pole orders in `level_double`/`level_simple`. -/
theorem Vd_ge (N p : ℕ) (hp : p.Prime) (k : ℤ) (hk1 : 13 * N + 1 ≤ k) (hk2 : k ≤ 29 * N + 1) :
    (mult (Id N) k - 4) * ellp p (29 * N + 1) ≤ Vd N p k := by
  have hq : ∀ i : ℕ, 0 < p ^ i := fun i => pow_pos hp.pos i
  set L := Finset.Ico 1 (Nat.log p (29 * N + 1) + 1) with hL
  have hell : ellp p (29 * N + 1) = (Nat.log p (29 * N + 1) : ℤ) := by
    rw [Aux.ellp_eq_log hp, show (29 * (N : ℤ) + 1).toNat = 29 * N + 1 by omega]
  have hconst : ∀ c : ℤ, c * (Nat.log p (29 * N + 1) : ℤ) = ∑ _i ∈ L, c := by
    intro c; simp [hL, mul_comm]
  have hf : ∀ m : ℤ, m ≤ 29 * N + 1 →
      fp p m = ∑ i ∈ L, ((m.toNat / p ^ i : ℕ) : ℤ) := fun m hm =>
    fp_eq_sum_levels hp (29 * N + 1) m (by push_cast; exact hm)
  have e1 := hf (k - N - 1) (by omega)
  have e2 := hf (k - 1) (by omega)
  have e3 := hf (k - 2 * N) (by omega)
  have e4 := hf (k - 12 * N - 1) (by omega)
  have e5 := hf (k - 11 * N - 1) (by omega)
  have e6 := hf (k - 10 * N - 1) (by omega)
  rcases (show (14 * N + 1 ≤ k ∧ k ≤ 28 * N + 1) ∨ k ≤ 14 * N ∨ 28 * N + 2 ≤ k by omega)
    with hB | hA | hC
  · -- double pole: `14N+1 ≤ k ≤ 28N+1`
    have hm : mult (Id N) k = 2 := by
      simp only [mult, Id, List.countP_cons, List.countP_nil, decide_eq_true_eq]
      split_ifs <;> omega
    have g1 := Gp_mid p k (13 * N + 1) (28 * N + 1) (by omega) (by omega)
    have g2 := Gp_mid p k (14 * N + 1) (29 * N + 1) (by omega) (by omega)
    have e7 := hf (k - (13 * N + 1)) (by omega)
    have e8 := hf (28 * N + 1 - k) (by omega)
    have e9 := hf (k - (14 * N + 1)) (by omega)
    have e10 := hf (29 * N + 1 - k) (by omega)
    rw [hm, hell]
    simp only [Vd, Id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [g1, g2, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
    calc ((2 : ℤ) - 4) * (Nat.log p (29 * N + 1) : ℤ) = ∑ _i ∈ L, (-2 : ℤ) := by
          rw [← hconst]; norm_num
      _ ≤ ∑ i ∈ L, ((((k - N - 1).toNat / p ^ i : ℕ) : ℤ) + (((k - 1).toNat / p ^ i : ℕ) : ℤ) +
            (((k - 2 * N).toNat / p ^ i : ℕ) : ℤ) - (((k - 12 * N - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - 11 * N - 1).toNat / p ^ i : ℕ) : ℤ) - (((k - 10 * N - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - (13 * N + 1)).toNat / p ^ i : ℕ) : ℤ) - (((28 * N + 1 - k).toNat / p ^ i : ℕ) : ℤ) -
            (((k - (14 * N + 1)).toNat / p ^ i : ℕ) : ℤ) - (((29 * N + 1 - k).toNat / p ^ i : ℕ) : ℤ)) :=
          Finset.sum_le_sum fun i _ => level_double (p ^ i) _ _ _ _ _ _ _ _ _ _ (hq i) (by omega)
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  · -- simple pole, left part: `13N+1 ≤ k ≤ 14N`
    have hm : mult (Id N) k = 1 := by
      simp only [mult, Id, List.countP_cons, List.countP_nil, decide_eq_true_eq]
      split_ifs <;> omega
    have g1 := Gp_mid p k (13 * N + 1) (28 * N + 1) (by omega) (by omega)
    have g2 := Gp_left p k (14 * N + 1) (29 * N + 1) (by omega)
    have e7 := hf (k - (13 * N + 1)) (by omega)
    have e8 := hf (28 * N + 1 - k) (by omega)
    have e9 := hf (29 * N + 1 - k) (by omega)
    have e10 := hf (14 * N + 1 - k - 1) (by omega)
    rw [hm, hell]
    simp only [Vd, Id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [g1, g2, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
    calc ((1 : ℤ) - 4) * (Nat.log p (29 * N + 1) : ℤ) = ∑ _i ∈ L, (-3 : ℤ) := by
          rw [← hconst]; norm_num
      _ ≤ ∑ i ∈ L, ((((k - N - 1).toNat / p ^ i : ℕ) : ℤ) + (((k - 1).toNat / p ^ i : ℕ) : ℤ) +
            (((k - 2 * N).toNat / p ^ i : ℕ) : ℤ) + (((14 * N + 1 - k - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - 12 * N - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - 11 * N - 1).toNat / p ^ i : ℕ) : ℤ) - (((k - 10 * N - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - (13 * N + 1)).toNat / p ^ i : ℕ) : ℤ) - (((28 * N + 1 - k).toNat / p ^ i : ℕ) : ℤ) -
            (((29 * N + 1 - k).toNat / p ^ i : ℕ) : ℤ)) :=
          Finset.sum_le_sum fun i _ => level_simple (p ^ i) _ _ _ _ _ _ _ _ _ _ (hq i) (by omega)
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  · -- simple pole, right part: `28N+2 ≤ k ≤ 29N+1`
    have hm : mult (Id N) k = 1 := by
      simp only [mult, Id, List.countP_cons, List.countP_nil, decide_eq_true_eq]
      split_ifs <;> omega
    have g1 := Gp_right p k (13 * N + 1) (28 * N + 1) (by omega) (by omega)
    have g2 := Gp_mid p k (14 * N + 1) (29 * N + 1) (by omega) (by omega)
    have e7 := hf (k - (13 * N + 1)) (by omega)
    have e8 := hf (k - (28 * N + 1) - 1) (by omega)
    have e9 := hf (k - (14 * N + 1)) (by omega)
    have e10 := hf (29 * N + 1 - k) (by omega)
    rw [hm, hell]
    simp only [Vd, Id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [g1, g2, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
    calc ((1 : ℤ) - 4) * (Nat.log p (29 * N + 1) : ℤ) = ∑ _i ∈ L, (-3 : ℤ) := by
          rw [← hconst]; norm_num
      _ ≤ ∑ i ∈ L, ((((k - N - 1).toNat / p ^ i : ℕ) : ℤ) + (((k - 1).toNat / p ^ i : ℕ) : ℤ) +
            (((k - 2 * N).toNat / p ^ i : ℕ) : ℤ) + (((k - (28 * N + 1) - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - 12 * N - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - 11 * N - 1).toNat / p ^ i : ℕ) : ℤ) - (((k - 10 * N - 1).toNat / p ^ i : ℕ) : ℤ) -
            (((k - (13 * N + 1)).toNat / p ^ i : ℕ) : ℤ) - (((k - (14 * N + 1)).toNat / p ^ i : ℕ) : ℤ) -
            (((29 * N + 1 - k).toNat / p ^ i : ℕ) : ℤ)) :=
          Finset.sum_le_sum fun i _ => level_simple (p ^ i) _ _ _ _ _ _ _ _ _ _ (hq i) (by omega)
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring

/-- **[6] Loss bound for `E_d`.** `(m_d(k)-1) ℓ_p(L(k)) + 2 ℓ_p(k-11N-1) ≤ (m_d(k)+1) ℓ_p(29N+1)`,
since `ℓ_p` is monotone, `L(k) ≤ 29N` and `k - 11N - 1 ≤ 18N` on the dual range, and `m_d ≥ 1`.
* Lines: ≈ 40 (monotonicity of `ℓ_p` via `Finset.lcm` divisibility ≈ 25, arithmetic ≈ 15).
* Directly from the PDF: yes ("the loss is at most `m_d(k)+1` per level"). -/
theorem loss_Ed_le (N p : ℕ) (hp : p.Prime) (k : ℤ) (hk1 : 13 * N + 1 ≤ k)
    (hk2 : k ≤ 29 * N + 1) :
    (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) ≤
      (mult (Id N) k + 1) * ellp p (29 * N + 1) := by
  have hm := (mult_Id_bounds N k hk1 hk2).1
  have hL : ellp p (Ld N k) ≤ ellp p (29 * N + 1) :=
    Aux.ellp_mono hp (max_le (by omega) (by omega))
  have hh : ellp p (k - 11 * N - 1) ≤ ellp p (29 * N + 1) := Aux.ellp_mono hp (by omega)
  have h1 : (mult (Id N) k - 1) * ellp p (Ld N k) ≤
      (mult (Id N) k - 1) * ellp p (29 * N + 1) := mul_le_mul_of_nonneg_left hL (by omega)
  linarith

/-- **[7] Loss bound for `E_{d4}`.** `(m_d(k)-1) ℓ_p(L(k)) + 3 ℓ_p(k-10N-1) ≤ (m_d(k)+2) ℓ_p(29N+1)`
(here `k - 10N - 1 ≤ 19N`).
* Lines: ≈ 40 (same argument as [6]).
* Directly from the PDF: yes (Part IV: "the loss is at most `m_d + 2`"). -/
theorem loss_Ed4_le (N p : ℕ) (hp : p.Prime) (k : ℤ) (hk1 : 13 * N + 1 ≤ k)
    (hk2 : k ≤ 29 * N + 1) :
    (mult (Id N) k - 1) * ellp p (Ld N k) + 3 * ellp p (k - 10 * N - 1) ≤
      (mult (Id N) k + 2) * ellp p (29 * N + 1) := by
  have hm := (mult_Id_bounds N k hk1 hk2).1
  have hL : ellp p (Ld N k) ≤ ellp p (29 * N + 1) :=
    Aux.ellp_mono hp (max_le (by omega) (by omega))
  have hh : ellp p (k - 10 * N - 1) ≤ ellp p (29 * N + 1) := Aux.ellp_mono hp (by omega)
  have h1 : (mult (Id N) k - 1) * ellp p (Ld N k) ≤
      (mult (Id N) k - 1) * ellp p (29 * N + 1) := mul_le_mul_of_nonneg_left hL (by omega)
  linarith

/-- **Main theorem (`blueprint.lean`, `E34_le`).** Proved from [1]–[7]. -/
theorem E34_le (N p : ℕ) (hp : p.Prime) :
    E34 N p ≤ max (padicValNat p 6 : ℤ) (6 * ellp p (29 * N + 1)) := by
  have hℓ := ellp_nonneg p (29 * N + 1)
  have hv : (0 : ℤ) ≤ padicValNat p 6 := Int.natCast_nonneg _
  -- `E_d ≤ max(v_p(6), 6ℓ)`
  have hEd : Ed N p ≤ max (padicValNat p 6 : ℤ) (6 * ellp p (29 * N + 1)) := by
    unfold Ed
    refine max_le (max_le (le_max_left _ _) (le_trans hv (le_max_left _ _))) ?_
    refine le_trans ?_ (le_max_right _ _)
    refine maxOn_le _ _ _ (by linarith) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have h5 := Vd_ge N p hp k hk1 hk2
    have h6 := loss_Ed_le N p hp k hk1 hk2
    nlinarith
  -- `E_{d4} ≤ 6ℓ`
  have hEd4 : Ed4 N p ≤ max (padicValNat p 6 : ℤ) (6 * ellp p (29 * N + 1)) := by
    unfold Ed4
    refine max_le (le_trans hv (le_max_left _ _)) ?_
    refine le_trans ?_ (le_max_right _ _)
    refine maxOn_le _ _ _ (by linarith) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have h5 := Vd_ge N p hp k hk1 hk2
    have h7 := loss_Ed4_le N p hp k hk1 hk2
    nlinarith
  exact (E34_le_max_Ed_Ed4 N p).trans (max_le hEd hEd4)

end ZetasIrr
