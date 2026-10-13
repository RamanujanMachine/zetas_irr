/-
# Blueprint of `upper_range_bound` (manuscript eq. (arith-upperrange))

Node `Pfq54.upper_range_bound` of `Blueprint_pfq54.lean`: for an eligible prime
`16n < p < 19n`, `p^{h_n(p)}` divides `Z_{0,n}, Z_{3,n}, Z_{4,n}`, where `h_n(p) = 3, 2, 1` on
`(18n,19n), (17n,18n), (16n,17n)`.

Proof (manuscript Appendix E): `v_p(D_n) = 1` ([1]); `H^{(r)}_m` is `p`-integral for `m < p` and
loses at most `r` powers of `p` for `m < p²` ([2]). For the active indices `j + 2n ≥ p` the
factorial formulas for `a_j, b_j` give `v_p(U_{n,j}) ≥ h`, `v_p(V_{n,j}) ≥ h - 1` ([3]); for all
`j`, `U_{n,j} ∈ ℤ` and `v_p(V_{n,j}) ≥ -1` ([4]). Summing term by term, with the constants of
[5], every term of `6 D_n⁴ S_{i,n}` has valuation `≥ h`.

Reused from the previous proof: `ZetasIrr.Aux.ellp_eq_log` (`blueprints/ZetasAux.lean`),
`ZetasIrr.BP.harm_valuation` and `ZetasIrr.BP.ValGE_sum` (`blueprints/valuation_bound.lean`).
-/
import pairing_bound
import valuation_bound
import uv_aux

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54
open ZetasIrr.Aux (ValGE)

/-- **[1] `v_p(D_n) = 1`** for `p ≤ 19n < p²` (`v_p(lcm(1,…,m)) = ⌊log_p m⌋`).
* Proof length: 8 lines. Proved below from `ZetasIrr.Aux.ellp_eq_log` (`blueprints/ZetasAux.lean`).
* Directly from the manuscript: yes ("`v_p(d_{19n}) = 1`"). -/
theorem padicValRat_D (n p : ℕ) [hp : Fact p.Prime] (h1 : p ≤ 19 * n) (h2 : 19 * n < p ^ 2) :
    padicValRat p (D n : ℚ) = 1 := by
  have he := ZetasIrr.Aux.ellp_eq_log hp.out ((19 * n : ℕ) : ℤ)
  simp only [ZetasIrr.ellp, Int.toNat_natCast] at he
  have hlog : Nat.log p (19 * n) = 1 := by
    rw [Nat.log_eq_iff (Or.inl one_ne_zero)]
    exact ⟨by simpa using h1, by simpa using h2⟩
  rw [padicValRat.of_nat]
  show (padicValNat p ((Icc 1 (19 * n)).lcm id) : ℤ) = 1
  rw [he, hlog, Nat.cast_one]

/-- **[2] Harmonic numbers at `p`**: for `m < p²`, `v_p(H^{(r)}_m) ≥ -r`, and `H^{(r)}_m` is
`p`-integral if `m < p`.
* Proof length: 10 lines. Proved below from `ZetasIrr.BP.harm_valuation` (`blueprints/valuation_bound.lean`).
* Directly from the manuscript: yes ("An order-`r` harmonic number loses at most `r` powers"). -/
theorem harm_valGE (p : ℕ) [hp : Fact p.Prime] (r m : ℕ) (hm : m < p ^ 2) :
    ValGE p (-(r : ℤ)) (harm r m) ∧ (m < p → ValGE p 0 (harm r m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact ⟨Or.inl (by simp [harm]), fun _ => Or.inl (by simp [harm])⟩
  have hh : harm r m = ZetasIrr.harm r (m : ℤ) := by simp [harm, ZetasIrr.harm]
  have hv := ZetasIrr.BP.harm_valuation (p := p) r (m : ℤ)
  rw [← hh, ZetasIrr.Aux.ellp_eq_log hp.out, Int.toNat_natCast] at hv
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow (by omega) hm
  refine ⟨hv.mono ?_, fun hmp => hv.mono ?_⟩
  · have h1 : (Nat.log p m : ℤ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hlog
    nlinarith [(Nat.cast_nonneg (Nat.log p m) : (0 : ℤ) ≤ _), (Nat.cast_nonneg r : (0 : ℤ) ≤ r)]
  · rw [Nat.log_of_lt hmp]; simp

/-- **[3] The valuation table on the upper harmonic ranges.** For eligible `16n < p < 19n` and
an active index `j ≤ 17n` with `j + 2n ≥ p` (so `j > 14n`): `v_p(U_{n,j}) ≥ h_n(p)` and
`v_p(V_{n,j}) ≥ h_n(p) - 1` (`U_{n,j} = 0` on `(18n,19n)`, since no double pole is active).
* Estimated proof length: ≈ 60 lines (`C_n` is a `p`-unit; the three numerator factorials
  `(j+10n)!, (j+11n)!, (j+12n)!` contain `p` once, only `j!, (j+n)!, (j+2n)!` can in the
  denominator; logarithmic differentiation loses at most one `p`).
* Directly from the manuscript: partially (the table is asserted with a short justification). -/
theorem U_V_valuation_active (n p j : ℕ) (hp : Eligible n p) (hlo : 16 * n < p)
    (hhi : p < 19 * n) (hj : j ≤ 17 * n) (hact : p ≤ j + 2 * n) :
    ValGE p (hgain n p) (U n j) ∧ ValGE p ((hgain n p : ℤ) - 1) (V n j) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hsq : 29 * n < p ^ 2 := lt_of_le_of_lt (by omega) hp.2.2.1
  have hH : ∀ m, m < p ^ 2 → ValGE p (-1) (harm 1 m) := fun m hm => by
    have := (harm_valGE p 1 m hm).1
    rwa [Nat.cast_one] at this
  obtain ⟨hd, hs⟩ := UV.UV_active p n j hH hlo (by omega) hsq hj hact
  unfold hgain
  rcases le_or_gt j (16 * n) with h1 | h1
  · obtain ⟨hU, hV⟩ := hd h1
    split_ifs <;> exact ⟨hU.mono (by split_ifs <;> omega), hV.mono (by split_ifs <;> omega)⟩
  · obtain ⟨hU, hV⟩ := hs h1
    split_ifs <;> exact ⟨Or.inl hU, hV.mono (by split_ifs <;> omega)⟩

/-- **[4] Valuations for all indices**: `U_{n,j} ∈ ℤ` and `v_p(V_{n,j}) ≥ -1` for `p ≤ 19n`,
from `Z_integral` (`D_n V_{n,j} ∈ ℤ`) and [1].
* Estimated proof length: ≈ 12 lines.
* Directly from the manuscript: yes (Proposition 2). -/
theorem U_V_valuation_all (n p j : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (h19 : p ≤ 19 * n) :
    ValGE p 0 (U n j) ∧ ValGE p (-1) (V n j) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hsq : 19 * n < p ^ 2 := lt_of_le_of_lt (by omega) hp.2.2.1
  obtain ⟨hU, hV, -, -⟩ := Z_integral n hn
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := hU j
    rcases eq_or_ne (U n j) 0 with h | h
    · exact Or.inl h
    · right; rw [hz, padicValRat.of_int]; exact Nat.cast_nonneg _
  · obtain ⟨z, hz⟩ := hV j
    rcases eq_or_ne (V n j) 0 with h | h
    · exact Or.inl h
    right
    have hD : (D n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero (19 * n))
    have h1 := padicValRat.mul (p := p) hD h
    rw [hz, padicValRat.of_int, padicValRat_D n p h19 hsq] at h1
    have : (0 : ℤ) ≤ (padicValInt p z : ℤ) := Nat.cast_nonneg _
    linarith

/-- **[5] The constants** `6, 1/2, 1/3` are `p`-units and `v_p(D_n⁴) = 4`.
* Proof length: 11 lines. Proved below from [1].
* Directly from the manuscript: yes. -/
theorem valGE_consts (n p : ℕ) [hp : Fact p.Prime] (h29 : 29 < p) (h1 : p ≤ 19 * n)
    (h2 : 19 * n < p ^ 2) :
    ValGE p 0 (6 : ℚ) ∧ ValGE p 0 ((2 : ℚ)⁻¹) ∧ ValGE p 0 ((3 : ℚ)⁻¹) ∧
      ValGE p 4 ((D n : ℚ) ^ 4) := by
  have hnd : ∀ q : ℕ, 0 < q → q < p → padicValRat p (q : ℚ) = 0 := fun q hq hqp => by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd fun h => absurd (Nat.le_of_dvd hq h) (by omega)
  have h6 := hnd 6 (by norm_num) (by omega)
  have h2' := hnd 2 (by norm_num) (by omega)
  have h3' := hnd 3 (by norm_num) (by omega)
  simp only [Nat.cast_ofNat] at h6 h2' h3'
  refine ⟨Or.inr h6.ge, Or.inr ?_, Or.inr ?_, Or.inr ?_⟩
  · rw [padicValRat.inv, h2', neg_zero]
  · rw [padicValRat.inv, h3', neg_zero]
  · rw [padicValRat.pow, padicValRat_D n p h1 h2]; norm_num

/-- **`upper_range_bound`** (node of `Blueprint_pfq54.lean`). Proved from [2]–[5],
`int_dvd_of_valGE` (`pairing_bound.lean`), `Z_integral` and `ZetasIrr.BP.ValGE_sum`. -/
theorem upper_range_bound (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hlo : 16 * n < p) (hhi : p < 19 * n) (i : Fin 3) :
    ∃ z : ℤ, Zv n i = (p : ℚ) ^ hgain n p * z := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hsq : 19 * n < p ^ 2 := by have := hp.2.2.1; nlinarith
  obtain ⟨h6, h2, h3, hD4⟩ := valGE_consts n p hp.2.1 (by omega) hsq
  have hh3 : hgain n p ≤ 3 := by unfold hgain; split_ifs <;> omega
  have hc := h6.mul hD4
  have hH : ∀ j ≤ 17 * n, ∀ r : ℕ, ValGE p (-(r : ℤ)) (harm r (j + 2 * n)) ∧
      (j + 2 * n < p → ValGE p 0 (harm r (j + 2 * n))) := fun j hj r =>
    harm_valGE p r (j + 2 * n) (by omega)
  refine int_dvd_of_valGE (Zv n i) ((Z_integral n hn).2.2.1 i) (hgain n p) ?_
  fin_cases i
  · show ValGE p (hgain n p : ℤ) (6 * (D n : ℚ) ^ 4 * S0 n)
    refine (hc.mul (ZetasIrr.BP.ValGE_sum _ 0 _ fun j _ =>
      (U_V_valuation_all n p j hn hp (by omega)).1)).mono ?_
    omega
  · show ValGE p (hgain n p : ℤ) (6 * (D n : ℚ) ^ 4 * S3 n)
    rw [S3, Finset.mul_sum]
    refine ZetasIrr.BP.ValGE_sum _ _ _ fun j hj => ?_
    have hj' : j ≤ 17 * n := by simp only [Finset.mem_range] at hj; omega
    obtain ⟨hU0, hV0⟩ := U_V_valuation_all n p j hn hp (by omega)
    obtain ⟨hA3, hB3⟩ := hH j hj' 3
    obtain ⟨hA2, hB2⟩ := hH j hj' 2
    rw [mul_add, div_eq_mul_inv]
    by_cases hact : p ≤ j + 2 * n
    · obtain ⟨hUa, hVa⟩ := U_V_valuation_active n p j hp hlo hhi hj' hact
      exact ValGE.add ((hc.mul (hUa.mul hA3)).mono (by omega))
        ((hc.mul ((hVa.mul hA2).mul h2)).mono (by omega))
    · have hlt : j + 2 * n < p := by omega
      exact ValGE.add ((hc.mul (hU0.mul (hB3 hlt))).mono (by omega))
        ((hc.mul ((hV0.mul (hB2 hlt)).mul h2)).mono (by omega))
  · show ValGE p (hgain n p : ℤ) (6 * (D n : ℚ) ^ 4 * S4 n)
    rw [S4, Finset.mul_sum]
    refine ZetasIrr.BP.ValGE_sum _ _ _ fun j hj => ?_
    have hj' : j ≤ 17 * n := by simp only [Finset.mem_range] at hj; omega
    obtain ⟨hU0, hV0⟩ := U_V_valuation_all n p j hn hp (by omega)
    obtain ⟨hA4, hB4⟩ := hH j hj' 4
    obtain ⟨hA3, hB3⟩ := hH j hj' 3
    rw [mul_add, div_eq_mul_inv]
    by_cases hact : p ≤ j + 2 * n
    · obtain ⟨hUa, hVa⟩ := U_V_valuation_active n p j hp hlo hhi hj' hact
      exact ValGE.add ((hc.mul (hUa.mul hA4)).mono (by omega))
        ((hc.mul ((hVa.mul hA3).mul h3)).mono (by omega))
    · have hlt : j + 2 * n < p := by omega
      exact ValGE.add ((hc.mul (hU0.mul (hB4 hlt))).mono (by omega))
        ((hc.mul ((hV0.mul (hB3 hlt)).mul h3)).mono (by omega))

end Pfq54.BP
