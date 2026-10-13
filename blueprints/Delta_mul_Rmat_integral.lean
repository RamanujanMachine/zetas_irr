/-
# `ZetasIrr.Delta_mul_Rmat_integral`

Statement (as in `blueprint.lean`), equation (8): `𝓩_N := Δ_N 𝓡_N ∈ Mat₃(ℤ)` for every `N ≥ 0`.

Source: PDF Part IV ("The first pair of bounds clears `p^{(3)}_{Nj}` and `q_{Nj}` … and the
second pair clears `p^{(4)}_{Nj}`. Therefore `𝓩_N ∈ Mat₃(ℤ)` for every `N ≥ 0`"), Part VII
Lemma 2 ("`N = 0` follows directly from `U`"), and Part VII §2, eq. (13) at `N = 0`
(`𝓒_0 = 𝓒₀`).

Strategy. For `N = 0`: `V_0 = 1`, so `𝓡_0 = U₃₄` is an integer matrix and `Δ_0 = 1`.
For `N ≥ 1`: a rational number is an integer iff all its `p`-adic valuations are `≥ 0`. At a
prime `p ≤ 29N+1`, `v_p(Δ_N) = E₃₄(N,p)` and `v_p(𝓡_N[i,j]) ≥ -E₃₄(N,p)` (`valuation_bound`).
At a prime `p > 29N+1`, `v_p(𝓡_N[i,j]) ≥ 0`.

| # | Supporting lemma                   | Status                                   |
|---|------------------------------------|------------------------------------------|
| 1 | `valuation_bound`                  | imported from `valuation_bound.lean` (`ZetasIrr.BP.valuation_bound`) |
| 2 | `coeffMat_zero`                    | imported from `coeffMat_zero.lean` (partial fractions of `R_0`) |
| 3 | `padicValNat_Delta`                | proved                                   |
| 4 | `E34_nonneg`                       | proved                                   |
| 5 | `exists_int_of_padicValRat_nonneg` | proved                                   |

This file contains no `sorry`. The open lemmas behind [1] are those of `valuation_bound.lean`
(and of the files it imports).

`coeffMat_zero` and its auxiliary results live in `coeffMat_zero.lean` (moved there so that
`det_V_eq.lean` can use them without an import cycle). At `N = 0` the kernel is
`(-t)^j/(t³(t+1))`, with `1/(t³(t+1)) = t⁻³ - t⁻² + t⁻¹ - (t+1)⁻¹`.
-/
import coeffMat_zero
import valuation_bound

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr

/- [1] `valuation_bound` is proved in `valuation_bound.lean` (namespace `ZetasIrr.BP`). -/
open ZetasIrr.BP (valuation_bound)

/-- **[3] Valuations of `Δ_N`.** For `N ≥ 1` and `p` prime,
`v_p(Δ_N) = E₃₄(N,p)` if `p ≤ 29N+1`, and `0` otherwise (definition (7), via the prime
factorization of the product). -/
theorem padicValNat_Delta (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (hp : p.Prime) :
    padicValNat p (Delta N) = if p ≤ 29 * N + 1 then (E34 N p).toNat else 0 := by
  rw [← Nat.factorization_def _ hp]
  simp only [Delta, show ¬ N = 0 by omega, ↓reduceIte]
  rw [Nat.factorization_prod fun q hq => pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero,
    Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hq : ∀ q ∈ (Finset.range (29 * N + 2)).filter Nat.Prime, q ≠ p →
      (E34 N q).toNat * q.factorization p = 0 := by
    intro q hq hqp
    rw [(Finset.mem_filter.mp hq).2.factorization, Finsupp.single_eq_of_ne hqp.symm, mul_zero]
  split_ifs with hle
  · rw [Finset.sum_eq_single p hq (fun hn => absurd (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hp⟩) hn), hp.factorization_self, mul_one]
  · refine Finset.sum_eq_zero fun q hqS => hq q hqS fun he => hle ?_
    subst he
    have := Finset.mem_range.mp (Finset.mem_filter.mp hqS).1
    omega

/-- **[4] `E₃₄ ≥ 0`.**
-/
theorem E34_nonneg (N p : ℕ) : 0 ≤ E34 N p := by
  have hEo : 0 ≤ Eo N p := le_max_left _ _
  have hEo4 : 0 ≤ Eo4 N p := le_max_left _ _
  have hEd : 0 ≤ Ed N p := (le_max_right _ _).trans (le_max_left _ _)
  have hEd4 : 0 ≤ Ed4 N p := le_max_left _ _
  unfold E34
  split_ifs
  · exact (le_min hEo hEd).trans (le_max_left _ _)
  · exact hEd.trans (le_max_left _ _)

/-- **[5] Integrality from valuations.** A rational number whose `p`-adic valuation is
nonnegative at every prime is an integer: if `p ∣ x.den`, then `v_p(x) = v_p(num) - v_p(den) < 0`
because `num` and `den` are coprime. -/
theorem exists_int_of_padicValRat_nonneg (x : ℚ)
    (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p x) : ∃ z : ℤ, x = z := by
  refine ⟨x.num, ?_⟩
  suffices hd : x.den = 1 from (Rat.coe_int_num_of_den_eq_one hd).symm
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hval := h p hp
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ x.num := by
    intro hdvd
    have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp hdvd
    exact hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h1 x.reduced).eq_one_of_dvd hpd)
  have hv : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero hpd
  unfold padicValRat at hval
  rw [padicValInt.eq_zero_of_not_dvd hnum] at hval
  omega

/-- **Main theorem (`blueprint.lean`, `Delta_mul_Rmat_integral`).** Proved from [1]–[5]. -/
theorem Delta_mul_Rmat_integral (N : ℕ) (i j : Fin 3) :
    ∃ z : ℤ, (Delta N : ℚ) * Rmat N i j = z := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `N = 0`: `V_0 = 1`, so `𝓡_0 = U₃₄`, and `Δ_0 = 1`
    have hC0 : IsUnit C0.det := by
      rw [Matrix.det_fin_three]; simp [C0]
    have hV : V 0 = 1 := by
      rw [V, coeffMat_zero, pow_zero, one_smul, Matrix.nonsing_inv_mul _ hC0]
    have hR : Rmat 0 = U34 := by
      rw [Rmat, T, hV, inv_one, Matrix.transpose_one, Matrix.mul_one]
    rw [hR, show Delta 0 = 1 from rfl, Nat.cast_one, one_mul]
    -- this should be U34 ; why is U34 defined over the rats?
    refine ⟨(!![0, -3, 3; 2, -2, 0; 0, 0, 6] : Matrix (Fin 3) (Fin 3) ℤ) i j, ?_⟩
    fin_cases i <;> fin_cases j <;> simp [U34]
  · -- `N ≥ 1`: all valuations of `Δ_N 𝓡_N[i,j]` are `≥ 0`
    by_cases hR : Rmat N i j = 0
    · exact ⟨0, by simp [hR]⟩
    have hΔ : (Delta N : ℚ) ≠ 0 := by
      unfold Delta
      simp only [hN.ne', ↓reduceIte]
      rw [Nat.cast_prod]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have := (Finset.mem_filter.mp hp).2.pos
      positivity
    refine exists_int_of_padicValRat_nonneg _ fun p hp => ?_
    have := Fact.mk hp
    rw [padicValRat.mul hΔ hR, padicValRat.of_nat, padicValNat_Delta N hN p hp]
    have hv := valuation_bound N hN p i j hR
    have h0 := E34_nonneg N p
    split_ifs at hv ⊢
    · have := Int.self_le_toNat (E34 N p)
      linarith
    · simpa using hv

end ZetasIrr
