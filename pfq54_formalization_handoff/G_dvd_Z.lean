/-
# Blueprint of `G_dvd_Z` (manuscript Theorem `arith-main`, divisibility)

Node `Pfq54.G_dvd_Z` of `Blueprint_pfq54.lean`: `G_n = ∏_{p eligible} p^{φ(n/p) + h_n(p) + s_n(p)}`
divides `Z_{0,n}, Z_{3,n}, Z_{4,n}`.

Proof (manuscript Appendix G, "Combining the divisors"): distinct prime powers are coprime, so it
suffices to treat one eligible prime at a time ([1]). On the harmonic ranges `16n < p < 19n`
the profile vanishes ([2]) and `upper_range_bound` gives `p^{h_n(p)}`. On `8n < p < 11n`,
`v_p(C_n) = c(n/p)` ([3]) and `residue_block` give a common valuation `≥ c(n/p) + 2` ([4]), which
is `≥ φ(n/p) + 1` by the profile facts ([2]). Elsewhere `pairing_bound` gives `p^{φ(n/p)}`. The two
extra ranges are disjoint, so no two lower bounds are added.
-/
import residue_block
import profile_aux

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54
open ZetasIrr.Aux (ValGE)

/-- **[1] Coprime prime powers.** If `p^{e_p} ∣ Z` for every `p` in a finite set of primes, then
`∏ p^{e_p} ∣ Z`.
* Estimated proof length: ≈ 15 lines (`Finset.prod_dvd_of_coprime`, `Nat.coprime_primes`,
  `Nat.Coprime.pow`, `Int.isCoprime_iff_gcd_eq_one`).
* Directly from the manuscript: yes (standard). -/
theorem prod_prime_pow_dvd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) (Z : ℤ)
    (h : ∀ p ∈ S, (p : ℤ) ^ e p ∣ Z) : ((∏ p ∈ S, p ^ e p : ℕ) : ℤ) ∣ Z := by
  rw [Nat.cast_prod]
  simp only [Nat.cast_pow]
  refine Finset.prod_dvd_of_coprime (fun a ha b hb hab => ?_) h
  exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hS a ha) (hS b hb)).mpr hab)).pow

/-- **[2] Profile facts** (arith-profilefacts): `φ(x) = 0` for `0 < x < 1/16`, and
`φ(x) ≤ c(x) + 1` for `1/11 < x < 1/8`.
* Estimated proof length: ≈ 40 lines (finitely many floor-constancy intervals with denominators
  `≤ 19`; one exact midpoint evaluation per interval).
* Directly from the manuscript: partially (asserted as "finite floor-function statements"). -/
theorem profile_facts :
    (∀ x : ℚ, 0 < x → x < 1 / 16 → phi x = 0) ∧
      ∀ x : ℚ, 1 / 11 < x → x < 1 / 8 → phi x ≤ cfun x + 1 := by
  have ht0 : ∀ F G : ℤ → ℤ, (∀ d ∈ PA.dl, F d = G d) →
      decide (PA.PhiF F = 0) = decide (PA.PhiF G = 0) := fun F G h => by
    rw [PA.PhiF_congr F G h]
  have ht1 : ∀ F G : ℤ → ℤ, (∀ d ∈ PA.dl, F d = G d) →
      decide (PA.PhiF F ≤ 2 * F 15 - 3 * F 10 + 1) =
        decide (PA.PhiF G ≤ 2 * G 15 - 3 * G 10 + 1) := fun F G h => by
    rw [PA.PhiF_congr F G h, h 15 (by decide), h 10 (by decide)]
  have c0 : PA.rowI (fun F => decide (PA.PhiF F = 0)) 0 (1 / 16) = true := by decide +kernel
  have c1 : PA.rowI (fun F => decide (PA.PhiF F ≤ 2 * F 15 - 3 * F 10 + 1)) (1 / 11) (1 / 8) =
      true := by decide +kernel
  refine ⟨fun x h0 h1 => ?_, fun x h0 h1 => ?_⟩
  · rw [PA.phi_eq_PhiF]
    exact of_decide_eq_true (PA.rowI_sound _ ht0 0 (1 / 16) c0 x h0 h1)
  · have h := of_decide_eq_true (PA.rowI_sound _ ht1 _ _ c1 x h0 h1)
    beta_reduce at h
    rw [Int.cast_ofNat, Int.cast_ofNat] at h
    rw [PA.phi_eq_PhiF]
    unfold cfun
    exact h

/-- **[3] `v_p(C_n) = c(n/p)`** at eligible primes (`C_n = (15n)!²/(10n)!³`; Legendre below `p²`).
* Uses: `padicValNat_factorial_small` (`pairing_bound.lean`), `ZetasIrr.Aux.padicValRat_factorial_prod`.
* Estimated proof length: ≈ 15 lines.
* Directly from the manuscript: yes. -/
theorem padicValRat_Cn (n p : ℕ) (hp : Eligible n p) :
    padicValRat p (Cn n) = cfun ((n : ℚ) / p) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hsq : 19 * n < p ^ 2 := lt_of_le_of_lt (by omega) hp.2.2.1
  have key : ∀ c : ℕ, c ≤ 19 →
      padicValRat p (((c * n).factorial : ℕ) : ℚ) = ⌊(c : ℚ) * ((n : ℚ) / p)⌋ := by
    intro c hc
    rw [padicValRat.of_nat, padicValNat_factorial_small p _
      (lt_of_le_of_lt (Nat.mul_le_mul_right n hc) hsq),
      show (c : ℚ) * ((n : ℚ) / p) = ((c * n : ℕ) : ℚ) / (p : ℕ) by push_cast; ring,
      Rat.floor_natCast_div_natCast, Int.natCast_div]
  have k15 := key 15 (by norm_num)
  have k10 := key 10 (by norm_num)
  simp only [Nat.cast_ofNat] at k15 k10
  unfold Cn cfun
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.pow, padicValRat.pow, k15, k10]
  push_cast
  ring

/-- **[4] The residue block in the `Z` normalization.** For eligible `8n < p < 11n`, every
`Z_{i,n}` has valuation `≥ c(n/p) + 2`: `Z = 6 D_n⁴ (-1)^n C_n (Q_n, P_{3,n}, P_{4,n})`,
`v_p(D_n⁴) = 4`, `v_p(C_n) = c(n/p)`, and `residue_block`.
* Uses: [3], `residue_block`, `padicValRat_D`, `valGE_consts` (`upper_range_bound.lean`).
* Estimated proof length: ≈ 30 lines.
* Directly from the manuscript: yes ("the common valuation of `X_n` at least `c(n/p) + 2`"). -/
theorem block_valuation (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (hlo : 8 * n < p)
    (hhi : p < 11 * n) (i : Fin 3) : ValGE p (cfun ((n : ℚ) / p) + 2) (Zv n i) := by
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨hQ, h3, h4⟩ := residue_block n p hn hp hlo hhi
  obtain ⟨h6, -, -, hD4⟩ := valGE_consts n p hp.2.1 (by omega)
    (lt_of_le_of_lt (by omega) hp.2.2.1)
  have hneg : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hC : Cn n ≠ 0 := by unfold Cn; positivity
  have hsgn : ValGE p 0 ((-1 : ℚ) ^ n) :=
    Or.inr (by rw [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero])
  have hCv : ValGE p (cfun ((n : ℚ) / p)) (Cn n) := Or.inr (padicValRat_Cn n p hp).ge
  have hS : ∀ X : ℚ, X = (-1) ^ n * Cn n * ((-1) ^ n * X / Cn n) := fun X => by
    calc X = ((-1 : ℚ) ^ n * (-1) ^ n) * X := by rw [hneg, one_mul]
      _ = _ := by field_simp
  have hc := h6.mul hD4
  fin_cases i
  · show ValGE p _ (6 * (D n : ℚ) ^ 4 * S0 n)
    rw [hS (S0 n)]
    exact (hc.mul ((hsgn.mul hCv).mul (Or.inr hQ))).mono (by omega)
  · show ValGE p _ (6 * (D n : ℚ) ^ 4 * S3 n)
    rw [hS (S3 n)]
    exact (hc.mul ((hsgn.mul hCv).mul (Or.inr h3))).mono (by omega)
  · show ValGE p _ (6 * (D n : ℚ) ^ 4 * S4 n)
    rw [hS (S4 n)]
    exact (hc.mul ((hsgn.mul hCv).mul (Or.inr h4))).mono (by omega)

/-- **`G_dvd_Z`** (node of `Blueprint_pfq54.lean`). Proved from [1], [2], [4], `phi_cases`,
`int_dvd_of_valGE`, `pairing_bound`, `upper_range_bound` and `Z_integral`. -/
theorem G_dvd_Z (n : ℕ) (hn : 1 ≤ n) (i : Fin 3) : ∃ z : ℤ, Zv n i = Gdiv n * z := by
  obtain ⟨Z, hZ⟩ := (Z_integral n hn).2.2.1 i
  have key : ∀ p ∈ (range (19 * n + 1)).filter (Eligible n),
      (p : ℤ) ^ ((phi ((n : ℚ) / p)).toNat + hgain n p + sgain n p) ∣ Z := by
    intro p hp
    obtain ⟨-, hpe⟩ := Finset.mem_filter.mp hp
    have : Fact p.Prime := ⟨hpe.1⟩
    have dvd_of : ∀ k : ℕ, (∃ z : ℤ, Zv n i = (p : ℚ) ^ k * z) → (p : ℤ) ^ k ∣ Z := by
      rintro k ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have : (Z : ℚ) = ((p ^ k * z : ℤ) : ℚ) := by rw [← hZ, hz]; push_cast; ring
      exact_mod_cast this
    have hpq : (0 : ℚ) < p := by exact_mod_cast hpe.1.pos
    have hnq : (0 : ℚ) < n := by exact_mod_cast hn
    by_cases hup : 16 * n < p ∧ p < 19 * n
    · have hx1 : (n : ℚ) / p < 1 / 16 := by
        rw [div_lt_div_iff₀ hpq (by norm_num)]; exact_mod_cast (by omega : n * 16 < 1 * p)
      have hφ := profile_facts.1 _ (by positivity) hx1
      have hs : sgain n p = 0 := by unfold sgain; split_ifs <;> omega
      rw [hφ, hs]
      simpa using dvd_of _ (upper_range_bound n p hn hpe hup.1 hup.2 i)
    · have hh : hgain n p = 0 := by unfold hgain; split_ifs <;> omega
      by_cases hblk : 8 * n < p ∧ p < 11 * n
      · have hs : sgain n p = 1 := by unfold sgain; split_ifs <;> omega
        have hx0 : 1 / 11 < (n : ℚ) / p := by
          rw [div_lt_div_iff₀ (by norm_num) hpq]; exact_mod_cast (by omega : 1 * p < n * 11)
        have hx1 : (n : ℚ) / p < 1 / 8 := by
          rw [div_lt_div_iff₀ hpq (by norm_num)]; exact_mod_cast (by omega : n * 8 < 1 * p)
        have hφle := profile_facts.2 _ hx0 hx1
        have hφ0 := (phi_cases ((n : ℚ) / p)).1
        rw [hh, hs, add_zero]
        refine dvd_of _ (int_dvd_of_valGE (Zv n i) ⟨Z, hZ⟩ _
          ((block_valuation n p hn hpe hblk.1 hblk.2 i).mono ?_))
        push_cast
        rw [Int.toNat_of_nonneg hφ0]
        linarith
      · have hs : sgain n p = 0 := by unfold sgain; split_ifs <;> omega
        rw [hh, hs]
        simpa using dvd_of _ (pairing_bound n p hn hpe i)
  obtain ⟨w, hw⟩ := prod_prime_pow_dvd _ (fun p hp => (Finset.mem_filter.mp hp).2.1) _ Z key
  refine ⟨w, ?_⟩
  rw [hZ, hw, Gdiv]
  push_cast
  ring

end Pfq54.BP
