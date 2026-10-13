/-
# Blueprint of `residue_block` (manuscript Lemma `arith-block`)

Node `Pfq54.residue_block` of `Blueprint_pfq54.lean`: for an eligible prime `8n < p < 11n`,
`v_p(Q_n) ≥ 1`, `v_p(P_{3,n}) ≥ -1`, `v_p(P_{4,n}) ≥ -2`, where
`(Q_n, P_{3,n}, P_{4,n}) = (-1)^n C_n^{-1} (S_{0,n}, S_{3,n}, S_{4,n})`.

Proof (manuscript Appendix F). Write `a_j = (-1)^n U_{n,j}/C_n`, `b_j = (-1)^n V_{n,j}/C_n` (the
partial-fraction coefficients of `F_n(t)`); the three readouts are sums over `j` ([1]). The root
counts of numerator and denominator of `F_n` in each residue class modulo `p` differ by at most
one, with equality exactly on the support ([2]). Hence `T = (X^p - X) N̄/D̄ ∈ 𝔽_p[X]` has degree
`p - 2`, and the local identity `p F_n(k + pV) ≡ -T(k) V³/((V+1)²(V+2)²)` gives `a_j/p`, `b_j`
modulo `p` ([3]). With `p^r H^{(r)}_m ≡ 𝟙_{m ≥ p}` for `m < 2p` ([4]) this yields
`p² P_{3,n} ≡ 10 ∑_k T(k)` and `p³ P_{4,n} ≡ (28/3) ∑_k T(k)` ([5]); a polynomial of degree
`< p - 1` sums to `0` over `𝔽_p` ([6]). Finally `Q_n = ∑ a_j ≠ 0` ([7]).
-/
import residue_aux5

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54
open ZetasIrr.Aux (ValGE)

/-- The double-pole coefficient `a_j = (-1)^n U_{n,j}/C_n`. -/
def aC (n j : ℕ) : ℚ := (-1) ^ n * U n j / Cn n

/-- The simple-pole coefficient `b_j = (-1)^n V_{n,j}/C_n`. -/
def bC (n j : ℕ) : ℚ := (-1) ^ n * V n j / Cn n

/-- Roots of the numerator of `F_n`: `[1,10n] ∪ [n+1,11n] ∪ [2n+1,12n]` (with multiplicity). -/
def numRoots (n : ℕ) : Multiset ℤ :=
  (Icc (1 : ℤ) (10 * n)).val + (Icc ((n : ℤ) + 1) (11 * n)).val +
    (Icc (2 * (n : ℤ) + 1) (12 * n)).val

/-- Roots of the denominator of `F_n`: `[-17n,-n] ∪ [-16n,-2n]`. -/
def denRoots (n : ℕ) : Multiset ℤ :=
  (Icc (-(17 * n : ℤ)) (-n)).val + (Icc (-(16 * n : ℤ)) (-(2 * n))).val

/-- Number of elements of `s` congruent to `k` modulo `p`. -/
def resCount (s : Multiset ℤ) (p k : ℕ) : ℕ := (s.filter fun x => x % (p : ℤ) = k).card

/-- The support (arith-support): `k > 12n - p`, `k ≥ 2p - 16n`, `k ≤ p - 2n`. -/
def supp (n p k : ℕ) : Prop := 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p

/-- **[1] The readouts as sums of partial-fraction coefficients** (arith-readout):
`Q_n = ∑ a_j`, `p² P_{3,n} = ∑ ((a_j/p)(p³ H^{(3)}_{j+2n}) + (b_j/2)(p² H^{(2)}_{j+2n}))`,
`p³ P_{4,n} = ∑ ((a_j/p)(p⁴ H^{(4)}_{j+2n}) + (b_j/3)(p³ H^{(3)}_{j+2n}))`.
* Estimated proof length: ≈ 15 lines (`Finset.mul_sum`, `field_simp`, `ring`).
* Directly from the manuscript: yes (normalization translation of §9). -/
theorem readout_sums (n p : ℕ) (hp : p ≠ 0) :
    Qa n = ∑ j ∈ range (17 * n + 1), aC n j ∧
      (p : ℚ) ^ 2 * P3a n = ∑ j ∈ range (17 * n + 1),
        (aC n j / p * ((p : ℚ) ^ 3 * harm 3 (j + 2 * n)) +
          bC n j / 2 * ((p : ℚ) ^ 2 * harm 2 (j + 2 * n))) ∧
      (p : ℚ) ^ 3 * P4a n = ∑ j ∈ range (17 * n + 1),
        (aC n j / p * ((p : ℚ) ^ 4 * harm 4 (j + 2 * n)) +
          bC n j / 3 * ((p : ℚ) ^ 3 * harm 3 (j + 2 * n))) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hC : Cn n ≠ 0 := by unfold Cn; positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold Qa aC S0
    rw [Finset.mul_sum, Finset.sum_div]
  · unfold P3a aC bC S3
    rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  · unfold P4a aC bC S4
    rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

/-- **[2] Root counts modulo `p`** (arith-support): in every residue class `0 ≤ k < p`,
`c_k - d_k ≥ -1`, with equality exactly on the support.
* Estimated proof length: ≈ 80 lines (explicit counts
  `c_k = 𝟙_{k≤10n} + 𝟙_{k>n} + 𝟙_{k>2n} + ∑_a 𝟙_{k ≤ an-p}`, `d_k = …`; case split on the ranges
  of `k`, `omega`).
* Directly from the manuscript: yes. -/
theorem root_count (n p k : ℕ) (hp : Eligible n p) (hlo : 8 * n < p) (hhi : p < 11 * n)
    (hk : k < p) :
    (resCount (denRoots n) p k : ℤ) ≤ resCount (numRoots n) p k + 1 ∧
      ((resCount (denRoots n) p k : ℤ) = resCount (numRoots n) p k + 1 ↔ supp n p k) := by
  exact RA.root_count' n p k hlo hhi hk

/-- **[3] The local identity** (arith-local) and the polynomial `T`. There is `T ∈ ℤ[X]` of
degree `≤ p - 2` (a lift of `(X^p - X) N̄/D̄`), vanishing modulo `p` off the support, such that
for every `j ≤ 17n`: `a_j/p` and `b_j` are `p`-integral; on the second node `p ≤ j + 2n < 2p`,
`a_j/p ≡ 8 T(-j)` and `b_j ≡ 4 T(-j)` (partial fractions of `V³/((V+1)²(V+2)²)`); and for
`j + 2n ≥ 2p` both reduce to `0`.
* Uses: [2].
* Estimated proof length: ≈ 120 lines (reduction of `F_n(k + pV)` modulo `p`; `(X^p - X)' = -1`;
  partial-fraction extraction at the distinct local poles `V = -1, -2`).
* Directly from the manuscript: yes. -/
theorem local_identity (n p : ℕ) (hp : Eligible n p) (hlo : 8 * n < p) (hhi : p < 11 * n) :
    ∃ T : Polynomial ℤ, T.natDegree ≤ p - 2 ∧
      (∀ k < p, ¬ supp n p k → (p : ℤ) ∣ T.eval (k : ℤ)) ∧
      ∀ j ≤ 17 * n, ValGE p 1 (aC n j) ∧ ValGE p 0 (bC n j) ∧
        (p ≤ j + 2 * n → j + 2 * n < 2 * p →
          ValGE p 1 (aC n j / p - 8 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ)) ∧
            ValGE p 1 (bC n j - 4 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ))) ∧
        (2 * p ≤ j + 2 * n → ValGE p 1 (aC n j / p) ∧ ValGE p 1 (bC n j)) := by
  exact RA.local_identity' p n hp hlo hhi

/-- **[4] Harmonic numbers modulo `p`**: for `r ≥ 1` and `m < 2p`, `p^r H^{(r)}_m` is
`p`-integral and `≡ 𝟙_{m ≥ p} (mod p)` (only the term `k = p` survives).
* Estimated proof length: ≈ 25 lines.
* Directly from the manuscript: yes ("`p^r H^{(r)}_{j+2n}` reduces respectively to `0` and `1`"). -/
theorem harm_reduction (p : ℕ) [Fact p.Prime] (r m : ℕ) (hr : 1 ≤ r) (hm : m < 2 * p) :
    ValGE p 0 ((p : ℚ) ^ r * harm r m) ∧
      ValGE p 1 ((p : ℚ) ^ r * harm r m - if p ≤ m then 1 else 0) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hterm : ∀ k ∈ Icc 1 m, k ≠ p → ValGE p 1 ((p : ℚ) ^ r * (1 / (k : ℚ) ^ r)) := by
    intro k hk hkp
    obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    right
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnd : ¬ p ∣ k := by
      rintro ⟨c, rfl⟩
      have hc : c < 2 := by
        by_contra h
        push_neg at h
        nlinarith
      interval_cases c <;> omega
    rw [padicValRat.mul (pow_ne_zero _ hp0) (by positivity), padicValRat.pow,
      padicValRat.div one_ne_zero (pow_ne_zero _ hk0), padicValRat.one, padicValRat.pow,
      padicValRat.self hp.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    push_cast
    omega
  have hsum : (p : ℚ) ^ r * harm r m = ∑ k ∈ Icc 1 m, (p : ℚ) ^ r * (1 / (k : ℚ) ^ r) := by
    rw [harm, Finset.mul_sum]
  by_cases hpm : p ≤ m
  · have hmem : p ∈ Icc 1 m := mem_Icc.mpr ⟨hp.one_lt.le, hpm⟩
    rw [ite_eq_left hpm, hsum, ← Finset.add_sum_erase _ _ hmem, mul_one_div,
      div_self (pow_ne_zero _ hp0), add_sub_cancel_left]
    have hrest : ValGE p 1 (∑ k ∈ (Icc 1 m).erase p, (p : ℚ) ^ r * (1 / (k : ℚ) ^ r)) :=
      ZetasIrr.BP.ValGE_sum _ _ _ fun k hk =>
        hterm k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
    refine ⟨ValGE.add (Or.inr (by rw [padicValRat.one])) (hrest.mono (by norm_num)), hrest⟩
  · rw [ite_eq_right hpm, sub_zero, hsum]
    have hall : ValGE p 1 (∑ k ∈ Icc 1 m, (p : ℚ) ^ r * (1 / (k : ℚ) ^ r)) :=
      ZetasIrr.BP.ValGE_sum _ _ _ fun k hk => hterm k hk (by
        have := (mem_Icc.mp hk).2; omega)
    exact ⟨hall.mono (by norm_num), hall⟩

/-- One readout term against its share of the complete residue sum (first, second and third
node). -/
theorem node_term (n p : ℕ) [Fact p.Prime] (hlo : 8 * n < p) (hp2 : 30 * n < p ^ 2)
    (T : Polynomial ℤ) (hT : ∀ j ≤ 17 * n, RA.Good n p T j) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (d : ℚ) (hd : ValGE p 0 d⁻¹) (j : ℕ) (hj : j ≤ 17 * n) :
    ValGE p 1 (aC n j / p * ((p : ℚ) ^ r * harm r (j + 2 * n)) +
      bC n j / d * ((p : ℚ) ^ s * harm s (j + 2 * n)) - (8 + 4 / d) *
        (((if p ≤ j + 2 * n ∧ j + 2 * n < 2 * p then T.eval (-(j : ℤ)) else 0 : ℤ)) : ℚ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hA1, hB0, h2nd, h3rd⟩ := hT j hj
  have hAp : ValGE p 0 (aC n j / p) := by
    rw [div_eq_mul_inv]; exact (hA1.mul (RA.valGE_inv_p p)).mono (by norm_num)
  have hBd : ValGE p 0 (bC n j / d) := by
    rw [div_eq_mul_inv]; exact (hB0.mul hd).mono (by norm_num)
  by_cases h1 : p ≤ j + 2 * n
  · by_cases h2 : j + 2 * n < 2 * p
    · rw [ite_eq_left ⟨h1, h2⟩]
      obtain ⟨hX0, hX1⟩ := harm_reduction p r (j + 2 * n) hr h2
      obtain ⟨hY0, hY1⟩ := harm_reduction p s (j + 2 * n) hs h2
      rw [ite_eq_left h1] at hX1 hY1
      obtain ⟨g1, g2⟩ := h2nd h1 h2
      have hTv := RA.valGE_int p (T.eval (-(j : ℤ)))
      rw [show aC n j / p * ((p : ℚ) ^ r * harm r (j + 2 * n)) +
          bC n j / d * ((p : ℚ) ^ s * harm s (j + 2 * n)) -
            (8 + 4 / d) * ((T.eval (-(j : ℤ)) : ℤ) : ℚ) =
          (aC n j / p - 8 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ)) * ((p : ℚ) ^ r * harm r (j + 2 * n)) +
          8 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ) * ((p : ℚ) ^ r * harm r (j + 2 * n) - 1) +
          (bC n j - 4 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ)) * d⁻¹ * ((p : ℚ) ^ s * harm s (j + 2 * n)) +
          4 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ) * d⁻¹ * ((p : ℚ) ^ s * harm s (j + 2 * n) - 1) by ring]
      exact ((((g1.mul hX0).mono (by norm_num)).add
        ((((RA.valGE_ofNat p 8).mul hTv).mul hX1).mono (by norm_num))).add
          (((g2.mul hd).mul hY0).mono (by norm_num))).add
            (((((RA.valGE_ofNat p 4).mul hTv).mul hd).mul hY1).mono (by norm_num))
    · rw [ite_eq_right fun h => h2 h.2, Int.cast_zero, mul_zero, sub_zero]
      obtain ⟨g1, g2⟩ := h3rd (by omega)
      have hm : j + 2 * n < p ^ 2 := by omega
      have hpow : ∀ q : ℕ, ValGE p 0 ((p : ℚ) ^ q * harm q (j + 2 * n)) := fun q => by
        have hq : ValGE p q ((p : ℚ) ^ q) :=
          Or.inr (le_of_eq (by rw [padicValRat.pow, padicValRat.self hp.one_lt, mul_one]))
        exact (hq.mul (harm_valGE p q _ hm).1).mono (by omega)
      exact ((g1.mul (hpow r)).mono (by norm_num)).add
        (((g2.mul hd).mul (hpow s)).mono (by norm_num))
  · rw [ite_eq_right fun h => h1 h.1, Int.cast_zero, mul_zero, sub_zero]
    have h2 : j + 2 * n < 2 * p := by omega
    obtain ⟨-, hX1⟩ := harm_reduction p r (j + 2 * n) hr h2
    obtain ⟨-, hY1⟩ := harm_reduction p s (j + 2 * n) hs h2
    rw [ite_eq_right h1, sub_zero] at hX1 hY1
    exact ((hAp.mul hX1).mono (by norm_num)).add ((hBd.mul hY1).mono (by norm_num))

/-- **[5] The block congruences**: `p² P_{3,n} ≡ 10 ∑_{k ∈ 𝔽_p} T(k)` and
`p³ P_{4,n} ≡ (28/3) ∑_{k ∈ 𝔽_p} T(k)` modulo `p` (`8T + 4T/2 = 10T`, `8T + 4T/3 = 28T/3`;
the first node and the classes off the support contribute `0`).
* Uses: [1], [3], [4] (the second nodes `j = 2p - k` run over the support classes once).
* Estimated proof length: ≈ 60 lines.
* Directly from the manuscript: yes. -/
theorem block_congruence (n p : ℕ) (hp : Eligible n p) (hlo : 8 * n < p) (hhi : p < 11 * n) :
    ∃ T : Polynomial ℤ, T.natDegree ≤ p - 2 ∧
      ValGE p 1 ((p : ℚ) ^ 2 * P3a n - 10 * ∑ k ∈ range p, ((T.eval (k : ℤ) : ℤ) : ℚ)) ∧
      ValGE p 1 ((p : ℚ) ^ 3 * P4a n - 28 / 3 * ∑ k ∈ range p, ((T.eval (k : ℤ) : ℤ) : ℚ)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨T, hdeg, hoff, hloc⟩ := RA.local_identity' p n hp hlo hhi
  obtain ⟨-, h3, h4⟩ := readout_sums n p hp.1.ne_zero
  obtain ⟨w, hw⟩ := RA.window_dvd n p hlo hhi T hoff
  have hS : ∑ k ∈ range p, ((T.eval (k : ℤ) : ℤ) : ℚ) = ∑ j ∈ range (17 * n + 1),
      (((if p ≤ j + 2 * n ∧ j + 2 * n < 2 * p then T.eval (-(j : ℤ)) else 0 : ℤ)) : ℚ) +
        (p : ℚ) * w := by
    have := congrArg (Int.cast : ℤ → ℚ) hw
    rw [Int.cast_sub, Int.cast_sum, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at this
    linarith
  have hpself : ValGE p 1 (p : ℚ) := Or.inr (by rw [padicValRat.self hp.1.one_lt])
  have hpw : ValGE p 1 ((p : ℚ) * w) := (hpself.mul (RA.valGE_int p w)).mono (by norm_num)
  obtain ⟨-, h2inv, h3inv, -⟩ := valGE_consts n p hp.2.1 (by omega) (by have := hp.2.2.1; omega)
  have hmem : ∀ j ∈ range (17 * n + 1), j ≤ 17 * n := fun j hj => by
    rw [mem_range] at hj; omega
  refine ⟨T, hdeg, ?_, ?_⟩
  · rw [h3, hS, mul_add, ← sub_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (ZetasIrr.BP.ValGE_sum _ _ _ fun j hj => ?_).sub
      (((RA.valGE_ofNat p 10).mul hpw).mono (by norm_num))
    have := node_term n p hlo hp.2.2.1 T hloc 3 2 (by norm_num) (by norm_num) 2 h2inv j (hmem j hj)
    rwa [show (8 + 4 / 2 : ℚ) = 10 by norm_num] at this
  · rw [h4, hS, mul_add, ← sub_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h28 : ValGE p 0 (28 / 3 : ℚ) := by
      rw [div_eq_mul_inv]; exact ((RA.valGE_ofNat p 28).mul h3inv).mono (by norm_num)
    refine (ZetasIrr.BP.ValGE_sum _ _ _ fun j hj => ?_).sub ((h28.mul hpw).mono (by norm_num))
    have := node_term n p hlo hp.2.2.1 T hloc 4 3 (by norm_num) (by norm_num) 3 h3inv j (hmem j hj)
    rwa [show (8 + 4 / 3 : ℚ) = 28 / 3 by norm_num] at this

/-- **[6] Complete residue sums vanish**: if `deg T ≤ p - 2` then `p ∣ ∑_{k=0}^{p-1} T(k)`
(monomials: `∑_{x ∈ 𝔽_p} x^i = 0` for `i < p - 1`).
* Estimated proof length: ≈ 25 lines (`FiniteField.sum_pow_lt_card_sub_one`, `ZMod.intCast_cast`,
  `Polynomial.eval_eq_sum_range`).
* Directly from the manuscript: yes. -/
theorem sum_residues_dvd (p : ℕ) [Fact p.Prime] (T : Polynomial ℤ) (hT : T.natDegree ≤ p - 2) :
    (p : ℤ) ∣ ∑ k ∈ range p, T.eval (k : ℤ) := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
  set f := Int.castRingHom (ZMod p)
  have h1 : ∑ k ∈ range p, ((T.eval (k : ℤ) : ℤ) : ZMod p) =
      ∑ x : ZMod p, (T.map f).eval x := by
    refine Finset.sum_bij' (fun k _ => (k : ZMod p)) (fun x _ => x.val) (fun _ _ => mem_univ _)
      (fun x _ => mem_range.mpr (ZMod.val_lt x))
      (fun k hk => ZMod.val_natCast_of_lt (mem_range.mp hk)) (fun x _ => ZMod.natCast_zmod_val x)
      (fun k _ => ?_)
    rw [Polynomial.eval_map, show ((k : ℕ) : ZMod p) = f (k : ℤ) by simp [f],
      Polynomial.eval₂_hom]
    rfl
  rw [h1]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  have hi' := mem_range.mp hi
  have hdeg := Polynomial.natDegree_map_le (f := f) (p := T)
  rw [ZMod.card]
  have := hp.two_le
  omega

/-- **[7]** `Q_n ≠ 0` for `n ≥ 1` (`S_{0,n} > 0` by `Z_integral`, `C_n ≠ 0`).
* Estimated proof length: ≈ 5 lines.
* Directly from the manuscript: yes ("all nonzero `a_j` have the same sign"). -/
theorem Qa_ne_zero (n : ℕ) (hn : 1 ≤ n) : Qa n ≠ 0 := by
  unfold Qa
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Z_integral n hn).2.2.2.ne')
    (by unfold Cn; positivity)

/-- **`residue_block`** (node of `Blueprint_pfq54.lean`, Lemma `arith-block`). Proved from
[1], [3], [5], [6], [7] and `valGE_consts` (`upper_range_bound.lean`). -/
theorem residue_block (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hlo : 8 * n < p) (hhi : p < 11 * n) :
    1 ≤ padicValRat p (Qa n) ∧ -1 ≤ padicValRat p (P3a n) ∧ -2 ≤ padicValRat p (P4a n) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
  have hint : ∀ z : ℤ, ValGE p 0 (z : ℚ) := fun z => by
    rcases eq_or_ne z 0 with h | h
    · left; simp [h]
    · right; rw [padicValRat.of_int]; positivity
  have hpself : ValGE p 1 (p : ℚ) := Or.inr (by rw [padicValRat.self hp.1.one_lt])
  obtain ⟨-, -, h3inv, -⟩ := valGE_consts n p hp.2.1 (by omega)
    (by have := hp.2.2.1; nlinarith)
  obtain ⟨hQ, -, -⟩ := readout_sums n p hp.1.ne_zero
  obtain ⟨T, -, -, hloc⟩ := local_identity n p hp hlo hhi
  obtain ⟨T', hT'deg, h3, h4⟩ := block_congruence n p hp hlo hhi
  obtain ⟨w, hw⟩ := sum_residues_dvd p T' hT'deg
  have hS : ∑ k ∈ range p, ((T'.eval (k : ℤ) : ℤ) : ℚ) = (p : ℚ) * w := by exact_mod_cast hw
  have hSv : ValGE p 1 (∑ k ∈ range p, ((T'.eval (k : ℤ) : ℤ) : ℚ)) := by
    rw [hS]; exact (hpself.mul (hint w)).mono (by norm_num)
  -- the three valuations
  have hQv : ValGE p 1 (Qa n) := by
    rw [hQ]
    exact ZetasIrr.BP.ValGE_sum _ _ _ fun j hj =>
      (hloc j (by simp only [Finset.mem_range] at hj; omega)).1
  have h3v : ValGE p 1 ((p : ℚ) ^ 2 * P3a n) := by
    have h10 : ValGE p 1 (10 * ∑ k ∈ range p, ((T'.eval (k : ℤ) : ℤ) : ℚ)) :=
      ((by simpa using hint 10 : ValGE p 0 (10 : ℚ)).mul hSv).mono (by norm_num)
    have := h3.add h10
    rwa [sub_add_cancel] at this
  have h4v : ValGE p 1 ((p : ℚ) ^ 3 * P4a n) := by
    have h28 : ValGE p 1 (28 / 3 * ∑ k ∈ range p, ((T'.eval (k : ℤ) : ℤ) : ℚ)) := by
      rw [div_eq_mul_inv]
      exact (((by simpa using hint 28 : ValGE p 0 (28 : ℚ)).mul h3inv).mul hSv).mono
        (by norm_num)
    have := h4.add h28
    rwa [sub_add_cancel] at this
  refine ⟨?_, ?_, ?_⟩
  · rcases hQv with h | h
    · exact absurd h (Qa_ne_zero n hn)
    · exact h
  · by_cases h0 : P3a n = 0
    · simp [h0]
    rcases h3v with h | h
    · exact absurd h (mul_ne_zero (pow_ne_zero _ hp0) h0)
    · rw [padicValRat.mul (pow_ne_zero _ hp0) h0, padicValRat.pow,
        padicValRat.self hp.1.one_lt] at h
      push_cast at h
      linarith
  · by_cases h0 : P4a n = 0
    · simp [h0]
    rcases h4v with h | h
    · exact absurd h (mul_ne_zero (pow_ne_zero _ hp0) h0)
    · rw [padicValRat.mul (pow_ne_zero _ hp0) h0, padicValRat.pow,
        padicValRat.self hp.1.one_lt] at h
      push_cast at h
      linarith

end Pfq54.BP
