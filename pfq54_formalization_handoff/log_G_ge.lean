/-
# Blueprint of `log_G_ge` (manuscript Theorem `arith-main`, growth of the divisor)

Node `Pfq54.log_G_ge` of `Blueprint_pfq54.lean`: `log G_n ≥ 29.004 n` for all large `n`
(`liminf log(G_n)/n ≥ S₈ + 9 > 29.004`).

Proof (manuscript Appendix G): `log G_n` is a sum over eligible primes ([1]). The profile `φ`
is the explicit periodic step function of the table ([2]); summing the table over the periods
`k = 0, …, 7` gives the rational number `S₈ > 20.004` ([3]). The prime number theorem
`∑_{n/b < p ≤ n/a} log p = (1/a - 1/b) n + o(n)` ([4]) and the negligibility of the excluded
primes ([5]) give the three contributions `S₈ n`, `6n` (upper harmonic ranges), `3n` (residue
block) up to `o(n)` ([6]–[8]); all omitted periods contribute nonnegatively.

Reused from the previous proof: `ZetasIrr.BP.pnt_bounds` (`blueprints/log_Delta_le.lean`, proved
there from the prime number theorem, which is the only `sorry` of that file).
-/
import pairing_bound
import log_Delta_le
import profile_aux
import log_G_aux2
import log_G_aux3

open Finset Filter Topology

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- The eligible primes `p ≤ 19n`. -/
def eligSet (n : ℕ) : Finset ℕ := (range (19 * n + 1)).filter (Eligible n)

/-- The nonzero intervals `(a, b)` of the profile on one period, with the value `φ = v`
(manuscript table, Appendix G). -/
def profileRows : List (ℚ × ℚ × ℕ) :=
  [(1/15, 1/13, 1), (1/13, 1/12, 2), (1/12, 1/10, 3), (2/15, 2/13, 1), (2/13, 3/17, 2),
   (3/17, 2/11, 1), (2/11, 1/5, 2), (1/5, 4/15, 1), (4/15, 5/17, 3), (5/17, 3/10, 2),
   (1/3, 2/5, 2), (2/5, 4/9, 1), (5/11, 7/15, 1), (7/15, 9/19, 3), (9/19, 1/2, 2),
   (8/15, 6/11, 1), (6/11, 3/5, 2), (3/5, 2/3, 1), (2/3, 11/16, 3), (11/16, 9/13, 2),
   (9/13, 7/10, 3), (11/15, 14/19, 2), (14/19, 3/4, 1), (3/4, 4/5, 2), (4/5, 13/16, 1),
   (9/11, 16/19, 1), (13/15, 7/8, 2), (7/8, 15/17, 3), (15/17, 9/10, 2), (14/15, 17/18, 2),
   (17/18, 18/19, 1)]

/-- `S₈ = ∑_{(a,b,v)} v ∑_{k=0}^{7} (1/(k+a) - 1/(k+b))`. -/
def S8 : ℝ :=
  (profileRows.map fun r => (r.2.2 : ℝ) *
    ∑ k ∈ range 8, (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))).sum

/-- **[1] `log G_n` as a sum over eligible primes.**
* Estimated proof length: ≈ 10 lines (`Real.log_prod`, `Real.log_pow`, `Nat.cast_prod`).
* Directly from the manuscript: yes. -/
theorem log_Gdiv_eq (n : ℕ) :
    Real.log (Gdiv n) = ∑ p ∈ eligSet n,
      (((phi ((n : ℚ) / p)).toNat + hgain n p + sgain n p : ℕ) : ℝ) * Real.log p := by
  unfold Gdiv eligSet
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (mem_filter.mp hp).2.1.ne_zero)

/-- **[2] The profile table.** On every interval `(k + a, k + b)` of the table (any period
`k ≥ 0`), `φ = v`.
* Estimated proof length: ≈ 60 lines (periodicity `φ(x+1) = φ(x)` from `∑ D = ∑ L` in each row;
  subdivision of `[0,1]` at all `i/j`, `j ≤ 19`, and one exact midpoint evaluation per interval).
* Directly from the manuscript: partially (finite exact check, stated but not displayed). -/
theorem profile_table : ∀ r ∈ profileRows, ∀ k : ℕ, ∀ x : ℚ,
    (k : ℚ) + r.1 < x → x < (k : ℚ) + r.2.1 → phi x = r.2.2 := by
  exact LG3.table_of_check profileRows LG3.rowsA_tab

/-- **[3] The exact rational sum** `S₈ > 20.004`.
* Estimated proof length: ≈ 10 lines (`norm_num [S8, profileRows]` on an explicit rational).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem S8_gt : (20.004 : ℝ) < S8 := by
  unfold S8 profileRows
  norm_num [Finset.sum_range_succ]

/-- **[4] Primes in a dilated interval** (prime number theorem):
`θ(n/a) - θ(n/b) ≥ (1/a - 1/b) n - ε n` for all large `n`.
* Proof length: 14 lines. Proved below from `ZetasIrr.BP.pnt_bounds` (`blueprints/log_Delta_le.lean`).
* Directly from the manuscript: partially (the prime number theorem is quoted, not proved). -/
theorem pnt_interval (a b : ℝ) (ha : 0 < a) (hab : a < b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) / a - n / b) - ε * n ≤
      Chebyshev.theta ((n : ℝ) / a) - Chebyshev.theta ((n : ℝ) / b) := by
  have hb : 0 < b := ha.trans hab
  set δ := ε / (1 / a + 1 / b) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨X₀, -, hX⟩ := ZetasIrr.BP.pnt_bounds hδ0
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) / b) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hb
  filter_upwards [hlim.eventually_ge_atTop X₀] with n hn
  have hna : X₀ ≤ (n : ℝ) / a :=
    hn.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha hab.le)
  obtain ⟨h1, -⟩ := hX _ hna
  obtain ⟨-, h2⟩ := hX _ hn
  have hsum : δ * ((n : ℝ) / a + n / b) = ε * n := by
    rw [hδ]; field_simp
  linarith

/-- **[5] Excluded primes are negligible**: primes `p ≤ 19n` that are not eligible (`p ≤ 29`,
`p² ≤ 30n` or `p ∣ n`) have `∑ log p = o(n)` (the exponents are bounded by `3 + 3 + 1`).
* Estimated proof length: ≈ 30 lines (`O(√n log n) + O(log n) + O(1)`; compare
  `small_primes_negligible` in `blueprints/log_Delta_le.lean`).
* Directly from the manuscript: yes. -/
theorem excluded_small : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p), Real.log p ≤
      ε * n := by
  intro ε hε
  set A := (range 30).filter Nat.Prime
  set K := ∑ p ∈ A, Real.log p
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def (by positivity : 0 < ε / 3)
  have hsmall := ZetasIrr.Aux.small_bound_isLittleO.def (by positivity : 0 < ε / 3)
  have hK : ∀ᶠ n : ℕ in atTop, K ≤ ε / 3 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (3 * K / ε)]
      with n hn
    rw [div_le_iff₀ hε] at hn
    linarith
  filter_upwards [hlog, hsmall, hK, eventually_ge_atTop 1] with n h1 h2 h3 hn
  set B := (range (Nat.sqrt (30 * n) + 1)).filter Nat.Prime
  set C := n.primeFactors
  have hnn : ∀ p ∈ (A ∪ B) ∪ C, 0 ≤ Real.log (p : ℝ) := fun p _ => Real.log_natCast_nonneg p
  have hsub : (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p) ⊆ (A ∪ B) ∪ C := by
    intro p hp
    obtain ⟨-, hpr, hne⟩ := mem_filter.mp hp
    simp only [Eligible, not_and_or, not_lt, not_not] at hne
    simp only [mem_union, A, B, C, mem_filter, mem_range, Nat.mem_primeFactors]
    rcases hne with h | h | h | h
    · exact absurd hpr h
    · exact Or.inl (Or.inl ⟨by omega, hpr⟩)
    · exact Or.inl (Or.inr ⟨Nat.lt_succ_of_le (Nat.le_sqrt'.mpr h), hpr⟩)
    · exact Or.inr ⟨hpr, h, by omega⟩
  have hunion : ∀ s t : Finset ℕ, (∀ p ∈ s ∪ t, 0 ≤ Real.log (p : ℝ)) →
      ∑ p ∈ s ∪ t, Real.log (p : ℝ) ≤ ∑ p ∈ s, Real.log (p : ℝ) + ∑ p ∈ t, Real.log (p : ℝ) := by
    intro s t hst
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun p hp =>
      hst p (mem_union_left _ (mem_inter.mp hp).1))
  have hC : ∑ p ∈ C, Real.log (p : ℝ) ≤ Real.log n := by
    rw [← Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero),
      ← Nat.cast_prod]
    exact Real.log_le_log (by exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).pos)
      (by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : (0 : ℝ) ≤ Real.log 6 + 6 * Real.log (29 * n + 1) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 29 * n + 1)
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)
    linarith
  have hB : ∑ p ∈ B, Real.log (p : ℝ) ≤
      (Real.sqrt (30 * n + 10) + 1) * (Real.log 6 + 6 * Real.log (29 * n + 1)) := by
    have hcard : (B.card : ℝ) ≤ Real.sqrt (30 * n + 10) + 1 := by
      have h1 : B.card ≤ Nat.sqrt (30 * n) + 1 := (card_filter_le _ _).trans (card_range _).le
      have h2 : (Nat.sqrt (30 * n) : ℝ) ≤ Real.sqrt (30 * n + 10) :=
        (Real.nat_sqrt_le_real_sqrt).trans (Real.sqrt_le_sqrt (by push_cast; linarith))
      have : (B.card : ℝ) ≤ (Nat.sqrt (30 * n) : ℝ) + 1 := by exact_mod_cast h1
      linarith
    have hterm : ∀ p ∈ B, Real.log (p : ℝ) ≤ Real.log 6 + 6 * Real.log (29 * n + 1) := by
      intro p hp
      obtain ⟨hpr, hpp⟩ := mem_filter.mp hp
      have hp1 : p ≤ Nat.sqrt (30 * n) := Nat.lt_succ_iff.mp (mem_range.mp hpr)
      have hs := Nat.sqrt_le' (30 * n)
      have hp2 : p ≤ 29 * n + 1 := by nlinarith
      have h1 : Real.log p ≤ Real.log (29 * n + 1) :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hp2)
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 29 * n + 1)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)
      linarith
    calc ∑ p ∈ B, Real.log (p : ℝ) ≤ ∑ p ∈ B, (Real.log 6 + 6 * Real.log (29 * n + 1)) :=
          Finset.sum_le_sum hterm
      _ = B.card * (Real.log 6 + 6 * Real.log (29 * n + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hL
  have hlogn : Real.log n ≤ ε / 3 * n := by
    have := h1
    simp only [Function.comp_apply, id_eq] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (Nat.cast_nonneg n)] at this
    exact this
  have hsm : (Real.sqrt (30 * n + 10) + 1) * (Real.log 6 + 6 * Real.log (29 * n + 1)) ≤
      ε / 3 * n := by
    have := h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hL),
      abs_of_nonneg (Nat.cast_nonneg n)] at this
    exact this
  calc ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p), Real.log (p : ℝ)
      ≤ ∑ p ∈ (A ∪ B) ∪ C, Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp
    _ ≤ ∑ p ∈ A ∪ B, Real.log (p : ℝ) + ∑ p ∈ C, Real.log (p : ℝ) := hunion _ _ hnn
    _ ≤ (K + ∑ p ∈ B, Real.log (p : ℝ)) + ∑ p ∈ C, Real.log (p : ℝ) := by
        gcongr
        exact hunion _ _ fun p hp => hnn p (mem_union_left _ hp)
    _ ≤ ε * n := by linarith

/-- **[6] The profile contribution**: `∑_{p eligible} φ(n/p) log p ≥ (S₈ - ε) n` eventually
(each table interval `(k+a, k+b)`, `k ≤ 7`, contributes `v (1/(k+a) - 1/(k+b)) n + o(n)` from
`n/(k+b) < p < n/(k+a)`; all other periods contribute `≥ 0`).
* Uses: [2], [4], [5], `phi_cases` (`φ ≥ 0`).
* Estimated proof length: ≈ 80 lines.
* Directly from the manuscript: partially (prime number theorem). -/
theorem profile_part : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (S8 - ε) * n ≤ ∑ p ∈ eligSet n, ((phi ((n : ℚ) / p)).toNat : ℝ) * Real.log p := by
  exact LG2.profile_gen (fun a b ha hab ε hε => pnt_interval a b ha hab ε hε) excluded_small
    profileRows LG3.rowsA_bd LG3.rowsA_pw profile_table

/-- **[7] The upper harmonic ranges**: `∑_{p eligible} h_n(p) log p ≥ (6 - ε) n` eventually
(`(3 + 2 + 1) n + o(n)` from `(18n,19n), (17n,18n), (16n,17n)`).
* Uses: [4], [5].
* Estimated proof length: ≈ 40 lines.
* Directly from the manuscript: partially (prime number theorem). -/
theorem harmonic_part : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (6 - ε) * n ≤ ∑ p ∈ eligSet n, (hgain n p : ℝ) * Real.log p := by
  exact LG2.harmonic_gen (fun a b ha hab ε hε => pnt_interval a b ha hab ε hε) excluded_small

/-- **[8] The residue block**: `∑_{p eligible} s_n(p) log p ≥ (3 - ε) n` eventually
(`(11 - 8) n + o(n)` from `8n < p < 11n`).
* Uses: [4], [5].
* Estimated proof length: ≈ 30 lines.
* Directly from the manuscript: partially (prime number theorem). -/
theorem block_part : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (3 - ε) * n ≤ ∑ p ∈ eligSet n, (sgain n p : ℝ) * Real.log p := by
  exact LG2.block_gen (fun a b ha hab ε hε => pnt_interval a b ha hab ε hε) excluded_small

/-- **`log_G_ge`** (node of `Blueprint_pfq54.lean`). Proved from [1], [3], [6], [7], [8]:
`log G_n ≥ (S₈ + 9 - 3δ/4) n ≥ 29.004 n` with `δ = S₈ - 20.004 > 0`. -/
theorem log_G_ge : ∀ᶠ n : ℕ in atTop, 29.004 * n ≤ Real.log (Gdiv n) := by
  have hδ : 0 < S8 - 20.004 := by linarith [S8_gt]
  filter_upwards [profile_part _ (by positivity : 0 < (S8 - 20.004) / 4),
    harmonic_part _ (by positivity : 0 < (S8 - 20.004) / 4),
    block_part _ (by positivity : 0 < (S8 - 20.004) / 4)] with n h1 h2 h3
  rw [log_Gdiv_eq]
  have hsplit : ∑ p ∈ eligSet n,
      (((phi ((n : ℚ) / p)).toNat + hgain n p + sgain n p : ℕ) : ℝ) * Real.log p =
      ∑ p ∈ eligSet n, ((phi ((n : ℚ) / p)).toNat : ℝ) * Real.log p +
        ∑ p ∈ eligSet n, (hgain n p : ℝ) * Real.log p +
        ∑ p ∈ eligSet n, (sgain n p : ℝ) * Real.log p := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    ring
  rw [hsplit]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hδ.le hn]

end Pfq54.BP
