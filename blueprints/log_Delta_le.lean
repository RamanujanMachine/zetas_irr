/-
# Blueprint for `ZetasIrr.log_Delta_le`

Statement (as in `blueprint.lean`), equation (10): `log Δ_N ≤ 57.784 N` for all large `N`.

Source: PDF Part IV ("The same floor-chamber calculation … the new profile is
`e₃₄(x) = e₃(x) + 𝟙_{x>1/19}`" (9); "`E₃₄ ≤ max(v_p(6), 6ℓ_p(29N+1))`. Small primes contribute
`o(N)`, and primes near chamber boundaries contribute `O(log N)` … Applying the prime number
theorem to (9) therefore gives `limsup log Δ_N / N ≤ c₃₄ = c₃ + 19 = 57.78399… < 57.784`")
and Part VII §4 (the chamber argument, the PNT step and the integer-only certificate) and the
Appendix (the profile table `e₀, e₁`).

Certificate: `certificates/zeta34/verify_arithmetic.py` (all 270 Farey-29 chambers with
infinitesimal offsets at every wall, the identity `e₃₄ = e₃ + 𝟙_{x>1/19}`, and the bound
`c₃₄ < 57.784`).

Strategy. Write `log Δ_N = ∑_{p ≤ 29N+1} E₃₄(N,p) log p` and split the primes into
* *small* primes `p ≤ √(30N+10)`: `E₃₄ = O(log N / log p)` by `E34_le`, total `O(√N log N)`;
* *boundary* primes, dividing `∏_{d=1}^{29} ∏_{r=-10}^{10} (dN + r)`: bounded exponents, total
  `O(log N)`;
* all other primes: `E₃₄(N,p) ≤ e₃₄(N/p)` (chamber profile), and
  `∑_p e₃₄(N/p) log p ≤ (c₃₄ + ε)N` by the PNT.

**Note.** The prime number theorem is not in Mathlib (only Chebyshev bounds are, in
`Mathlib/NumberTheory/Chebyshev.lean`). It is the supporting lemma [1] here.

| # | Supporting lemma               | Est. lines | Directly from PDF? |
|---|--------------------------------|-----------:|--------------------|
| 1 | `prime_number_theorem`         | ≈ 10000 (or import PrimeNumberTheoremAnd) | No |
| 2 | `E34_le`                       | imported from `E34_le.lean` | Partially |
| 3 | `log_Delta_eq_sum`             |         30 | Yes                |
| 4 | `chamber_profile`              |       4000 | No (computer certificate) |
| 5 | `small_primes_negligible`      |        120 | Yes                |
| 6 | `boundary_primes_negligible`   |        150 | Yes                |
| 7 | `profile_sum_le`               |   (proved) | Partially          |
| 8 | `c34_lt`                       |   (proved) | Partially (certificate) |
| 9 | `log_Delta_split`              |        100 | Yes (given [3], [4]) |

[1] is the ingredient of [7]; [2] of [5], [6]; [3], [4] of [9]. The main theorem uses
[5]–[9]. Total estimate (excluding PNT and [2]): ≈ 5500 lines, dominated by the chamber
certificate [4].

[2] is `ZetasIrr.E34_le`, the main theorem of `E34_le.lean`, which is imported.
-/
import ZetasAux
import E34_le
import Chamber_main

open Filter Topology Real

noncomputable section

namespace ZetasIrr.BP

/-! ### The profile (PDF Appendix and eq. (9)) -/

/-- The prime-exponent profile table of the PDF appendix, rows `(l, r, e₀, e₁)`: on the open
interval `(l, r) ⊂ (0,1)`, `e₃ = e₀` for `0 < N/p < 1` and `e₃ = e₁` for the fractional part of
`N/p > 1`. Copied verbatim from the TeX source. -/
def profileTable : List (ℚ × ℚ × ℕ × ℕ) :=
  [(0, 1/18, 0, 3), (1/18, 1/17, 1, 3), (1/17, 1/16, 2, 3), (1/16, 1/15, 3, 3),
  (1/15, 1/13, 4, 4), (1/13, 1/12, 3, 3), (1/12, 1/11, 2, 2), (1/11, 1/10, 1, 1),
  (1/10, 2/19, 0, 0), (2/19, 1/8, 1, 1), (1/8, 2/15, 2, 2), (2/15, 2/13, 3, 3),
  (2/13, 3/17, 2, 2), (3/17, 2/11, 3, 3), (2/11, 3/13, 2, 2), (3/13, 4/17, 1, 1),
  (4/17, 3/11, 2, 2), (3/11, 5/18, 1, 1), (5/18, 5/17, 2, 2), (5/17, 3/10, 3, 3),
  (3/10, 4/11, 2, 2), (4/11, 7/19, 1, 1), (7/19, 5/13, 2, 2), (5/13, 7/18, 1, 1),
  (7/18, 5/12, 2, 2), (5/12, 8/19, 1, 1), (8/19, 5/11, 2, 2), (5/11, 8/17, 1, 1),
  (8/17, 9/19, 2, 2), (9/19, 1/2, 3, 3), (1/2, 8/15, 2, 2), (8/15, 7/13, 3, 3),
  (7/13, 6/11, 2, 2), (6/11, 9/16, 1, 1), (9/16, 7/12, 2, 2), (7/12, 10/17, 1, 1),
  (10/17, 7/11, 2, 2), (7/11, 11/17, 1, 1), (11/17, 11/16, 2, 2), (11/16, 9/13, 3, 3),
  (9/13, 8/11, 2, 2), (8/11, 11/15, 1, 1), (11/15, 14/19, 2, 2), (14/19, 3/4, 3, 3),
  (3/4, 13/16, 2, 2), (13/16, 9/11, 3, 3), (9/11, 16/19, 2, 2), (16/19, 7/8, 3, 3),
  (7/8, 15/17, 2, 2), (15/17, 9/10, 3, 3), (9/10, 10/11, 2, 2), (10/11, 11/12, 1, 1),
  (11/12, 15/16, 0, 0), (15/16, 17/18, 2, 2), (17/18, 18/19, 3, 3), (18/19, 1, 4, 4)]

/-- Value of a column of the table at `y ∈ (0,1)` off the walls (sum over the disjoint
chambers). -/
def tableValue (col : ℚ × ℚ × ℕ × ℕ → ℕ) (y : ℝ) : ℝ :=
  (profileTable.map fun row =>
    if (row.1 : ℝ) < y ∧ y < (row.2.1 : ℝ) then (col row : ℝ) else 0).sum

/-- The walls: the endpoints of the table and the new wall `1/19` of (9). -/
def onWall (y : ℝ) : Prop :=
  y = 1 / 19 ∨ ∃ row ∈ profileTable, y = (row.1 : ℝ) ∨ y = (row.2.1 : ℝ)

/-- The profile `e₃₄(x) = e₃(x) + 𝟙_{x > 1/19}` (9). For `0 < x < 1` it uses column `e₀`. For
`x > 1` it is periodic, `e₁({x}) + 1`. On walls it is set to `5`, an upper bound for all
values. -/
def e34 (x : ℝ) : ℝ :=
  haveI := Classical.propDecidable
  if x ≤ 0 then 0
  else if x < 1 then
    (if onWall x then 5 else tableValue (fun row => row.2.2.1) x + if 1 / 19 < x then 1 else 0)
  else if Int.fract x = 0 ∨ onWall (Int.fract x) then 5
  else tableValue (fun row => row.2.2.2) (Int.fract x) + 1

/-- The limiting constant (10):
`c₃₄ = ∫₀¹ e₃₄(x) x⁻² dx + ∫₀¹ e₃₄(1+y) ψ'(1+y) dy`, with `ψ'(1+y) = ∑_{k ≥ 1} (k+y)⁻²`. -/
def c34 : ℝ :=
  (∫ x in (0 : ℝ)..1, e34 x / x ^ 2) +
    ∫ y in (0 : ℝ)..1, e34 (1 + y) * ∑' k : ℕ, 1 / ((k : ℝ) + 1 + y) ^ 2

/-! ### The prime sums -/

/-- The primes `p ≤ 29N+1`. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (29 * N + 2)).filter Nat.Prime

/-- The boundary product `∏_{d=1}^{29} ∏_{r=-10}^{10} (dN + r)` (PDF Part VII §4). -/
def boundaryProd (N : ℕ) : ℤ :=
  ∏ d ∈ Finset.Icc (1 : ℤ) 29, ∏ r ∈ Finset.Icc (-10 : ℤ) 10, (d * N + r)

/-- Contribution of the small primes `p ≤ √(30N+10)`. -/
def smallSum (N : ℕ) : ℝ :=
  ∑ p ∈ (primesUpTo N).filter (fun p : ℕ => (p : ℝ) ≤ √(30 * N + 10)),
    ((E34 N p).toNat : ℝ) * Real.log p

/-- Contribution of the boundary primes. -/
def boundarySum (N : ℕ) : ℝ :=
  ∑ p ∈ (primesUpTo N).filter (fun p : ℕ => (p : ℤ) ∣ boundaryProd N),
    ((E34 N p).toNat : ℝ) * Real.log p

/-- The profile sum `∑_{p ≤ 29N+1} e₃₄(N/p) log p`. -/
def profileSum (N : ℕ) : ℝ := ∑ p ∈ primesUpTo N, e34 ((N : ℝ) / p) * Real.log p

/-! ### Supporting lemmas -/

/-- **[1] The prime number theorem** `θ(x) ~ x`.
* Lines: ≈ 10000 for a self-contained proof (e.g. Selberg–Erdős, or Wiener–Ikehara as in the
  PrimeNumberTheoremAnd project); alternatively import PrimeNumberTheoremAnd.
* Directly from the PDF: no (the PDF uses it as a black box). -/
theorem prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  sorry

/- **[2] Uniform exponent bound** (the node `E34_le` of `blueprint.lean`) is `ZetasIrr.E34_le`,
imported from `blueprints/E34_le.lean`. -/

/-- **[3] `log Δ_N` as a prime sum.** For `N ≥ 1`,
`log Δ_N = ∑_{p ≤ 29N+1} E₃₄(N,p) log p`.
* Lines: ≈ 30 (`Real.log_prod`, `Real.log_pow`, positivity of the factors).
* Directly from the PDF: yes (definition (7)). -/
theorem log_Delta_eq_sum (N : ℕ) (hN : 1 ≤ N) :
    Real.log (Delta N) = ∑ p ∈ primesUpTo N, ((E34 N p).toNat : ℝ) * Real.log p := by
  unfold Delta primesUpTo
  simp only [show N ≠ 0 by omega, ↓reduceIte]
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity


/-- **[5] Small primes are negligible.** For `p ≤ √(30N+10)`, [2] gives
`E₃₄ log p ≤ (v_p(6) + 6 log(29N+1)/log p) log p`. Summing over at most `√(30N+10)` primes
gives `O(√N log N) = o(N)`.
* Lines: ≈ 120 (`ℓ_p(m) = Nat.log p m` via `Chebyshev.factorization_lcmUpto`, `Nat.log` bound,
  counting primes trivially, asymptotics).
* Directly from the PDF: yes. -/
theorem small_primes_negligible :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, smallSum N ≤ ε * N := by
  intro ε hε
  filter_upwards [Aux.small_bound_isLittleO.def hε, eventually_ge_atTop 1] with N hN hN1
  set S := (primesUpTo N).filter (fun p : ℕ => (p : ℝ) ≤ √(30 * N + 10)) with hS
  set c := Real.log 6 + 6 * Real.log (29 * N + 1) with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log (29 * N + 1) := Real.log_nonneg (by have := (Nat.cast_nonneg N : (0:ℝ) ≤ N); linarith)
    have : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    linarith
  have hterm : ∀ p ∈ S, ((E34 N p).toNat : ℝ) * Real.log p ≤ c := fun p hp => by
    have hpr := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact Aux.toNat_mul_log_le hpr N _ (E34_le N p hpr)
  have hcard : (S.card : ℝ) ≤ √(30 * N + 10) + 1 := by
    have hsub : S ⊆ Finset.range (⌊√(30 * (N : ℝ) + 10)⌋₊ + 1) := fun p hp =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (Finset.mem_filter.mp hp).2))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have hfl := Nat.floor_le (Real.sqrt_nonneg (30 * (N : ℝ) + 10))
    have h2 : (S.card : ℝ) ≤ (⌊√(30 * (N : ℝ) + 10)⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hnorm : ‖(N : ℝ)‖ = N := by simp
  calc smallSum N ≤ ∑ p ∈ S, c := Finset.sum_le_sum hterm
    _ = S.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (√(30 * N + 10) + 1) * c := mul_le_mul_of_nonneg_right hcard hc0
    _ ≤ ‖(√(30 * N + 10) + 1) * c‖ := Real.le_norm_self _
    _ ≤ ε * ‖(N : ℝ)‖ := hN
    _ = ε * N := by rw [hnorm]

/-- **[6] Boundary primes are negligible.** For `p > √(29N+1)`, `ℓ_p(29N+1) ≤ 1`, so [2] gives
`E₃₄ ≤ 6`. The boundary primes are bounded by `∑_{p ∣ B_N} log p ≤ log |B_N| = O(log N)`
(`B_N ≠ 0` for `N > 10`). Small boundary primes are already `o(N)` by the argument of [5].
* Lines: ≈ 150.
* Directly from the PDF: yes ("primes near chamber boundaries contribute `O(log N)`"). -/
theorem boundary_primes_negligible :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, boundarySum N ≤ ε * N := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hε' : 0 < ε * Real.log 2 / 609 := by positivity
  filter_upwards [Aux.log_bound_isLittleO.def hε', eventually_ge_atTop 11] with N hN hN11
  set S := (primesUpTo N).filter (fun p : ℕ => (p : ℤ) ∣ boundaryProd N) with hS
  set c := Real.log 6 + 6 * Real.log (29 * N + 1) with hc
  have hNr : (11 : ℝ) ≤ N := by exact_mod_cast hN11
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log (29 * N + 1) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    linarith
  have hprime : ∀ p ∈ S, p.Prime := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hterm : ∀ p ∈ S, ((E34 N p).toNat : ℝ) * Real.log p ≤ c := fun p hp =>
    Aux.toNat_mul_log_le (hprime p hp) N _ (E34_le N p (hprime p hp))
  -- the boundary product is a nonzero integer of size `≤ (29N+10)^609`
  have hfac : ∀ d ∈ Finset.Icc (1 : ℤ) 29, ∀ r ∈ Finset.Icc (-10 : ℤ) 10,
      0 < d * N + r ∧ d * N + r ≤ 29 * N + 10 := by
    intro d hd r hr
    simp only [Finset.mem_Icc] at hd hr
    constructor <;> nlinarith
  have hB0 : boundaryProd N ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun d hd =>
      Finset.prod_ne_zero_iff.mpr fun r hr => (hfac d hd r hr).1.ne'
  have hBle : |boundaryProd N| ≤ (29 * (N : ℤ) + 10) ^ 609 := by
    unfold boundaryProd
    rw [Finset.abs_prod]
    calc ∏ d ∈ Finset.Icc (1 : ℤ) 29, |∏ r ∈ Finset.Icc (-10 : ℤ) 10, (d * N + r)|
        = ∏ d ∈ Finset.Icc (1 : ℤ) 29, ∏ r ∈ Finset.Icc (-10 : ℤ) 10, |d * N + r| := by
          simp only [Finset.abs_prod]
      _ ≤ ∏ d ∈ Finset.Icc (1 : ℤ) 29, ∏ r ∈ Finset.Icc (-10 : ℤ) 10, (29 * (N : ℤ) + 10) := by
          refine Finset.prod_le_prod₀ (fun d _ => Finset.prod_nonneg fun r _ => abs_nonneg _)
            fun d hd => Finset.prod_le_prod₀ (fun r _ => abs_nonneg _) fun r hr => ?_
          rw [abs_of_pos (hfac d hd r hr).1]; exact (hfac d hd r hr).2
      _ = (29 * (N : ℤ) + 10) ^ 609 := by simp [Finset.prod_const, ← pow_mul]
  -- `#S · log 2 ≤ log |B_N| ≤ 609 log(29N+10)`
  have hdvd : (∏ p ∈ S, p) ∣ (boundaryProd N).natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (hprime p hp).prime)
      fun p hp => Int.natCast_dvd.mp (Finset.mem_filter.mp hp).2
  have hle : 2 ^ S.card ≤ (boundaryProd N).natAbs :=
    (Finset.pow_card_le_prod S (fun p => p) 2 fun p hp => (hprime p hp).two_le).trans
      (Nat.le_of_dvd (Int.natAbs_pos.mpr hB0) hdvd)
  have hlogB : (S.card : ℝ) * Real.log 2 ≤ 609 * Real.log (29 * N + 10) := by
    have h1 : ((2 : ℝ) ^ S.card) ≤ |(boundaryProd N : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hle
    have h2 : |(boundaryProd N : ℝ)| ≤ (29 * (N : ℝ) + 10) ^ 609 := by
      rw [← Int.cast_abs]; exact_mod_cast hBle
    have h609 : (609 : ℝ) * Real.log (29 * N + 10) = Real.log ((29 * (N : ℝ) + 10) ^ 609) := by
      rw [Real.log_pow]; norm_num
    rw [← Real.log_pow, h609]
    exact Real.log_le_log (by positivity) (h1.trans h2)
  have hnorm : ‖(N : ℝ)‖ = N := by simp
  have hN' : Real.log (29 * N + 10) * c ≤ ε * Real.log 2 / 609 * N := by
    have := (Real.le_norm_self _).trans hN
    rwa [hnorm] at this
  have hcard : (S.card : ℝ) ≤ 609 * Real.log (29 * N + 10) / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact hlogB
  calc boundarySum N ≤ ∑ p ∈ S, c := Finset.sum_le_sum hterm
    _ = S.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 609 * Real.log (29 * N + 10) / Real.log 2 * c := mul_le_mul_of_nonneg_right hcard hc0
    _ = 609 / Real.log 2 * (Real.log (29 * N + 10) * c) := by ring
    _ ≤ 609 / Real.log 2 * (ε * Real.log 2 / 609 * N) :=
        mul_le_mul_of_nonneg_left hN' (by positivity)
    _ = ε * N := by field_simp

section PNTStep

open MeasureTheory intervalIntegral

/-! ### Supporting lemmas for [7]: the chamber decomposition of `e₃₄` -/

/-! ### Facts about the table -/

theorem profileTable_nodup : profileTable.Nodup := by decide +kernel

theorem profileTable_facts : ∀ row ∈ profileTable,
    0 ≤ row.1 ∧ row.1 < row.2.1 ∧ row.2.1 ≤ 1 ∧ (row.1 = 0 → row.2.2.1 = 0) ∧
      row.2.2.1 ≤ 4 ∧ row.2.2.2 ≤ 4 := by
  simp only [profileTable, List.forall_mem_cons]
  norm_num

/-- The rows as a `Finset`. -/
def T : Finset (ℚ × ℚ × ℕ × ℕ) := profileTable.toFinset

theorem mem_T {row : ℚ × ℚ × ℕ × ℕ} : row ∈ T ↔ row ∈ profileTable := List.mem_toFinset

theorem T_card_le : T.card ≤ 56 := List.toFinset_card_le _

theorem T_facts : ∀ row ∈ T,
    (0 : ℝ) ≤ row.1 ∧ (row.1 : ℝ) < row.2.1 ∧ (row.2.1 : ℝ) ≤ 1 ∧
      ((row.1 : ℝ) = 0 → (row.2.2.1 : ℝ) = 0) ∧ (row.2.2.1 : ℝ) ≤ 4 ∧ (row.2.2.2 : ℝ) ≤ 4 := by
  intro row hrow
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := profileTable_facts row (mem_T.mp hrow)
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, fun h => ?_,
    by exact_mod_cast h5, by exact_mod_cast h6⟩
  exact_mod_cast h4 (by exact_mod_cast h)

/-- The indicator of the open chamber `(a, b)`. -/
def ind (a b x : ℝ) : ℝ := if a < x ∧ x < b then 1 else 0

theorem ind_nonneg (a b x : ℝ) : 0 ≤ ind a b x := by unfold ind; split_ifs <;> norm_num

theorem ind_le_one (a b x : ℝ) : ind a b x ≤ 1 := by unfold ind; split_ifs <;> norm_num

theorem tableValue_eq (col : ℚ × ℚ × ℕ × ℕ → ℕ) (y : ℝ) :
    tableValue col y = ∑ row ∈ T, (col row : ℝ) * ind row.1 row.2.1 y := by
  unfold tableValue T
  rw [List.sum_toFinset _ profileTable_nodup]
  congr 1
  refine List.map_congr_left fun row _ => ?_
  unfold ind; split_ifs <;> simp

theorem tableValue_sub (col : ℚ × ℚ × ℕ × ℕ → ℕ) (c x : ℝ) :
    tableValue col (x - c) = ∑ row ∈ T, (col row : ℝ) * ind (c + row.1) (c + row.2.1) x := by
  rw [tableValue_eq]
  refine Finset.sum_congr rfl fun row _ => ?_
  unfold ind
  congr 1
  simp only [sub_lt_iff_lt_add', lt_sub_iff_add_lt', add_comm c]

theorem tableValue_nonneg (col : ℚ × ℚ × ℕ × ℕ → ℕ) (y : ℝ) : 0 ≤ tableValue col y := by
  rw [tableValue_eq]
  exact Finset.sum_nonneg fun row _ => mul_nonneg (Nat.cast_nonneg _) (ind_nonneg _ _ _)

theorem tableValue_le (col : ℚ × ℚ × ℕ × ℕ → ℕ) (hcol : ∀ row ∈ T, (col row : ℝ) ≤ 4) (y : ℝ) :
    tableValue col y ≤ 224 := by
  rw [tableValue_eq]
  calc ∑ row ∈ T, (col row : ℝ) * ind row.1 row.2.1 y ≤ ∑ _row ∈ T, (4 : ℝ) :=
        Finset.sum_le_sum fun row hrow => by
          calc (col row : ℝ) * ind row.1 row.2.1 y ≤ 4 * 1 :=
                mul_le_mul (hcol row hrow) (ind_le_one _ _ _) (ind_nonneg _ _ _) (by norm_num)
            _ = 4 := by norm_num
    _ = T.card * 4 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 56 * 4 := by
        have := T_card_le
        have : (T.card : ℝ) ≤ 56 := by exact_mod_cast this
        linarith
    _ = 224 := by norm_num

/-- `e₃₄ ≤ 225`. -/
theorem e34_le (x : ℝ) : e34 x ≤ 225 := by
  have h0 := tableValue_le (fun row => row.2.2.1) (fun row hrow => (T_facts row hrow).2.2.2.2.1) x
  have h1 := tableValue_le (fun row => row.2.2.2) (fun row hrow => (T_facts row hrow).2.2.2.2.2)
    (Int.fract x)
  unfold e34
  split_ifs <;> linarith

theorem e34_nonneg (x : ℝ) : 0 ≤ e34 x := by
  have h0 := tableValue_nonneg (fun row => row.2.2.1) x
  have h1 := tableValue_nonneg (fun row => row.2.2.2) (Int.fract x)
  unfold e34
  split_ifs <;> linarith

/-- The walls of `(0,1)` as a finite set. -/
def Wall0 : Finset ℝ :=
  insert (1 / 19) ((T.image fun row => (row.1 : ℝ)) ∪ (T.image fun row => (row.2.1 : ℝ)))

theorem onWall_iff (y : ℝ) : onWall y ↔ y ∈ Wall0 := by
  unfold onWall Wall0
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, mem_T]
  constructor
  · rintro (h | ⟨row, hrow, h | h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨row, hrow, h.symm⟩)
    · exact Or.inr (Or.inr ⟨row, hrow, h.symm⟩)
  · rintro (h | ⟨row, hrow, h⟩ | ⟨row, hrow, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨row, hrow, Or.inl h.symm⟩
    · exact Or.inr ⟨row, hrow, Or.inr h.symm⟩

/-- `e₃₄` on `(0,1)` off the walls. -/
theorem e34_eq_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hw : x ∉ Wall0) :
    e34 x = tableValue (fun row => row.2.2.1) x + ind (1 / 19) 1 x := by
  have hw' : ¬ onWall x := fun h => hw ((onWall_iff x).mp h)
  unfold e34
  rw [ite_eq_right (not_le.mpr hx0), ite_eq_left hx1, ite_eq_right hw']
  congr 1
  unfold ind
  by_cases h : 1 / 19 < x
  · rw [ite_eq_left h, ite_eq_left ⟨h, hx1⟩]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]

/-- `e₃₄` on `(k, k+1)` off the walls, `k ≥ 1`. -/
theorem e34_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) (h0 : Int.fract x ≠ 0)
    (hw : Int.fract x ∉ Wall0) :
    e34 x = tableValue (fun row => row.2.2.2) (Int.fract x) + 1 := by
  have hw' : ¬ onWall (Int.fract x) := fun h => hw ((onWall_iff _).mp h)
  unfold e34
  rw [ite_eq_right (by linarith), ite_eq_right (not_lt.mpr hx), ite_eq_right (not_or.mpr ⟨h0, hw'⟩)]

/-- The chamber step function on `(0, M+1)`:
`G_M(x) = ∑_rows e₀ 𝟙_{(l,r)} + 𝟙_{(1/19,1)} + ∑_{j<M} (∑_rows e₁ 𝟙_{(j+1+l, j+1+r)} + 𝟙_{(j+1,j+2)})`. -/
def G (M : ℕ) (x : ℝ) : ℝ :=
  ∑ row ∈ T, (row.2.2.1 : ℝ) * ind row.1 row.2.1 x + ind (1 / 19) 1 x +
    ∑ j ∈ Finset.range M, (∑ row ∈ T, (row.2.2.2 : ℝ) * ind ((j : ℝ) + 1 + row.1)
      ((j : ℝ) + 1 + row.2.1) x + ind ((j : ℝ) + 1) ((j : ℝ) + 2) x)

theorem G_nonneg (M : ℕ) (x : ℝ) : 0 ≤ G M x := by
  unfold G
  have h1 : ∀ (c : ℝ) (a b : ℝ), 0 ≤ c → 0 ≤ c * ind a b x := fun c a b hc =>
    mul_nonneg hc (ind_nonneg _ _ _)
  refine add_nonneg (add_nonneg (Finset.sum_nonneg fun row _ => h1 _ _ _ (Nat.cast_nonneg _))
    (ind_nonneg _ _ _)) (Finset.sum_nonneg fun j _ => add_nonneg
      (Finset.sum_nonneg fun row _ => h1 _ _ _ (Nat.cast_nonneg _)) (ind_nonneg _ _ _))

/-- The walls of `(0, M+1]`. -/
def WallM (M : ℕ) : Finset ℝ :=
  ((Finset.range (M + 1)) ×ˢ Wall0).image (fun q => (q.1 : ℝ) + q.2) ∪
    (Finset.range (M + 2)).image (fun k : ℕ => (k : ℝ))

theorem fract_eq_sub_floor {x : ℝ} (hx : 0 ≤ x) : Int.fract x = x - (⌊x⌋₊ : ℝ) := by
  rw [Int.fract, ← Int.natCast_floor_eq_floor hx, Int.cast_natCast]

/-- **Pointwise bound.** For `x > 0`:
`e₃₄(x) ≤ 225 𝟙_{x ≥ M+1} + 225 𝟙_{x ∈ Wall_M} + G_M(x)`. -/
theorem e34_le_G (M : ℕ) {x : ℝ} (hx : 0 < x) :
    e34 x ≤ 225 * (if (M : ℝ) + 1 ≤ x then 1 else 0) + 225 * (if x ∈ WallM M then 1 else 0) +
      G M x := by
  have hG := G_nonneg M x
  have hC := e34_le x
  by_cases htail : (M : ℝ) + 1 ≤ x
  · rw [ite_eq_left htail]
    have : (0 : ℝ) ≤ 225 * (if x ∈ WallM M then 1 else 0) := by split_ifs <;> norm_num
    linarith
  rw [ite_eq_right htail]
  by_cases hwall : x ∈ WallM M
  · rw [ite_eq_left hwall]; linarith
  rw [ite_eq_right hwall]
  simp only [mul_zero, zero_add]
  push Not at htail
  by_cases hx1 : x < 1
  · -- first unit interval
    have hw : x ∉ Wall0 := fun h => hwall (by
      unfold WallM
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(0, x), ?_, by simp⟩)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), h⟩)
    rw [e34_eq_of_lt_one hx hx1 hw, tableValue_eq]
    unfold G
    have : 0 ≤ ∑ j ∈ Finset.range M, (∑ row ∈ T, (row.2.2.2 : ℝ) * ind ((j : ℝ) + 1 + row.1)
        ((j : ℝ) + 1 + row.2.1) x + ind ((j : ℝ) + 1) ((j : ℝ) + 2) x) :=
      Finset.sum_nonneg fun j _ => add_nonneg (Finset.sum_nonneg fun row _ =>
        mul_nonneg (Nat.cast_nonneg _) (ind_nonneg _ _ _)) (ind_nonneg _ _ _)
    linarith
  · -- the interval `(k, k+1)` with `k = ⌊x⌋₊`, `1 ≤ k ≤ M`
    push Not at hx1
    set k := ⌊x⌋₊ with hk
    have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hx1)
    have hkM : k < M + 1 := (Nat.floor_lt hx.le).mpr (by push_cast; linarith)
    have hkx : (k : ℝ) ≤ x := Nat.floor_le hx.le
    have hfr : Int.fract x = x - k := fract_eq_sub_floor hx.le
    have h0 : Int.fract x ≠ 0 := by
      intro h
      apply hwall
      unfold WallM
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩)
      rw [hfr] at h; linarith
    have hw : Int.fract x ∉ Wall0 := by
      intro h
      apply hwall
      unfold WallM
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(k, Int.fract x), ?_, ?_⟩)
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hkM, h⟩
      · simp only [hfr]; ring
    have hxk : (k : ℝ) < x := by
      rcases lt_or_eq_of_le hkx with h | h
      · exact h
      · exact absurd (by rw [hfr, ← h, sub_self]) h0
    have hxk1 : x < (k : ℝ) + 1 := by
      exact Nat.lt_floor_add_one x
    rw [e34_eq_of_one_le hx1 h0 hw, hfr, tableValue_sub]
    -- the `j = k - 1` term of `G`
    obtain ⟨j, hjk⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    rw [hjk] at hxk hxk1 ⊢
    have hterm : ∑ row ∈ T, (row.2.2.2 : ℝ) * ind ((j : ℝ) + 1 + row.1) ((j : ℝ) + 1 + row.2.1) x +
        ind ((j : ℝ) + 1) ((j : ℝ) + 2) x ≤ ∑ j ∈ Finset.range M, (∑ row ∈ T, (row.2.2.2 : ℝ) *
          ind ((j : ℝ) + 1 + row.1) ((j : ℝ) + 1 + row.2.1) x + ind ((j : ℝ) + 1) ((j : ℝ) + 2) x) :=
      Finset.single_le_sum (f := fun j : ℕ => ∑ row ∈ T, (row.2.2.2 : ℝ) *
          ind ((j : ℝ) + 1 + row.1) ((j : ℝ) + 1 + row.2.1) x + ind ((j : ℝ) + 1) ((j : ℝ) + 2) x)
        (fun i _ => add_nonneg (Finset.sum_nonneg fun row _ =>
          mul_nonneg (Nat.cast_nonneg _) (ind_nonneg _ _ _)) (ind_nonneg _ _ _)) hj
    have hind : ind ((j : ℝ) + 1) ((j : ℝ) + 2) x = 1 := by
      unfold ind
      rw [ite_eq_left ⟨by push_cast at hxk; linarith, by push_cast at hxk1; linarith⟩]
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hxk hxk1 ⊢
    rw [hind] at hterm
    unfold G
    have h1 : 0 ≤ ∑ row ∈ T, (row.2.2.1 : ℝ) * ind row.1 row.2.1 x :=
      Finset.sum_nonneg fun row _ => mul_nonneg (Nat.cast_nonneg _) (ind_nonneg _ _ _)
    have h2 := ind_nonneg (1 / 19) 1 x
    linarith

/-! ### Integrals of the chamber functions -/

theorem ind_measurable (a b : ℝ) : Measurable (ind a b) := by
  unfold ind
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

/-- Bounded measurable functions are interval integrable. -/
theorem II_of_bounded (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem II_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 1) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume 0 1 := by
  have e : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by funext x; simp [Finset.sum_apply]
  rw [e]; exact IntervalIntegrable.sum s h

/-- The chamber term `e 𝟙_{(a,b)}(x) / (x + c)²`. -/
theorem step_II (a b c e : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (he : 0 ≤ e) (h0 : a + c = 0 → e = 0) :
    IntervalIntegrable (fun x => e * ind a b x / (x + c) ^ 2) volume 0 1 := by
  have hm : Measurable (fun x => e * ind a b x / (x + c) ^ 2) :=
    (measurable_const.mul (ind_measurable a b)).div ((measurable_id.add_const c).pow_const 2)
  refine II_of_bounded _ hm (e / (a + c) ^ 2) (fun x => ?_) 0 1
  unfold ind
  split_ifs with hx
  · rw [mul_one, abs_of_nonneg (by positivity)]
    rcases eq_or_lt_of_le (add_nonneg ha hc) with h | h
    · rw [h0 h.symm]; simp
    · exact div_le_div_of_nonneg_left he (by positivity) (by nlinarith)
  · simp only [mul_zero, zero_div, abs_zero]
    positivity

theorem step_integral (a b c e : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hc : 0 ≤ c)
    (h0 : a + c = 0 → e = 0) :
    ∫ x in (0 : ℝ)..1, e * ind a b x / (x + c) ^ 2 = e * (1 / (a + c) - 1 / (b + c)) := by
  rcases eq_or_lt_of_le (add_nonneg ha hc) with h | hac
  · rw [h0 h.symm]; simp
  have hind : (fun x => e * ind a b x / (x + c) ^ 2) =
      Set.indicator (Set.Ioo a b) (fun x => e / (x + c) ^ 2) := by
    funext x
    unfold ind
    by_cases hx : a < x ∧ x < b
    · rw [ite_eq_left hx, Set.indicator_of_mem (Set.mem_Ioo.mpr hx), mul_one]
    · rw [ite_eq_right hx, Set.indicator_of_notMem (fun h => hx (Set.mem_Ioo.mp h)), mul_zero,
        zero_div]
  have hsub : Set.Ioo a b ∩ Set.Ioc 0 1 = Set.Ioo a b :=
    Set.inter_eq_left.mpr fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hind, integral_of_le zero_le_one, MeasureTheory.integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, hsub, ← integral_Ioc_eq_integral_Ioo,
    ← integral_of_le hab.le]
  have h1 : ∫ x in a..b, e / (x + c) ^ 2 = e * ∫ x in a..b, (fun x => 1 / x ^ 2) (x + c) := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun x _ => ?_
    simp only; ring
  rw [h1, integral_comp_add_right (fun x => 1 / x ^ 2) c]
  have h2 : (fun x : ℝ => 1 / x ^ 2) = fun x => x ^ (-2 : ℤ) := by
    funext x; rw [one_div, ← zpow_natCast, ← zpow_neg]; norm_num
  rw [h2, integral_zpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt hac (by linarith)⟩)]
  have hb' : 0 < b + c := by linarith
  rw [show (-2 : ℤ) + 1 = -1 by norm_num, zpow_neg_one, zpow_neg_one]
  push_cast
  field_simp
  ring

theorem step_integral0 (a b e : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (h0 : a = 0 → e = 0) :
    ∫ x in (0 : ℝ)..1, e * ind a b x / x ^ 2 = e * (1 / a - 1 / b) := by
  have := step_integral a b 0 e ha hab hb le_rfl (by simpa using h0)
  simpa using this

theorem step_II0 (a b e : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e) (h0 : a = 0 → e = 0) :
    IntervalIntegrable (fun x => e * ind a b x / x ^ 2) volume 0 1 := by
  have := step_II a b 0 e ha le_rfl he (by simpa using h0)
  simpa using this

/-- The walls of `(0,1]` have measure zero. -/
theorem ae_notMem_wall : ∀ᵐ x : ℝ, x ∉ (insert (1 : ℝ) Wall0 : Finset ℝ) := by
  have h := Finset.measure_zero (insert (1 : ℝ) Wall0) (volume : Measure ℝ)
  rw [ae_iff]
  simp only [not_not]
  exact h

/-- The first integral: `∫₀¹ e₃₄(x)/x² = ∑_rows e₀(1/l - 1/r) + (19 - 1)`. -/
theorem integral_one :
    ∫ x in (0 : ℝ)..1, e34 x / x ^ 2 =
      ∑ row ∈ T, (row.2.2.1 : ℝ) * (1 / row.1 - 1 / row.2.1) + 1 * (1 / (1 / 19) - 1 / 1) := by
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc (0 : ℝ) 1 → e34 x / x ^ 2 =
      ∑ row ∈ T, (row.2.2.1 : ℝ) * ind row.1 row.2.1 x / x ^ 2 + 1 * ind (1 / 19) 1 x / x ^ 2 := by
    filter_upwards [ae_notMem_wall] with x hx hx'
    rw [Set.uIoc_of_le zero_le_one] at hx'
    simp only [Finset.mem_insert, not_or] at hx
    have hx1 : x < 1 := lt_of_le_of_ne hx'.2 hx.1
    rw [e34_eq_of_lt_one hx'.1 hx1 hx.2, tableValue_eq, add_div, Finset.sum_div, one_mul]
  have hI : ∀ row ∈ T, IntervalIntegrable
      (fun x => (row.2.2.1 : ℝ) * ind row.1 row.2.1 x / x ^ 2) volume 0 1 := fun row hrow => by
    obtain ⟨h1, -, -, h4, -⟩ := T_facts row hrow
    exact step_II0 _ _ _ h1 (Nat.cast_nonneg _) h4
  have hI2 : IntervalIntegrable (fun x => 1 * ind (1 / 19) 1 x / x ^ 2) volume 0 1 :=
    step_II0 _ _ _ (by norm_num) zero_le_one (by norm_num)
  rw [integral_congr_ae hae, integral_add (II_sum _ hI) hI2,
    intervalIntegral.integral_finsetSum hI,
    step_integral0 _ _ _ (by norm_num) (by norm_num) le_rfl (by norm_num)]
  congr 1
  refine Finset.sum_congr rfl fun row hrow => ?_
  obtain ⟨h1, h2, h3, h4, -⟩ := T_facts row hrow
  exact step_integral0 _ _ _ h1 h2 h3 h4

/-- `ψ'(1+y) = ∑_k (k+1+y)⁻²`. -/
def psi1 (y : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1 + y) ^ 2

theorem summable_shift : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

theorem summable_psi1 {y : ℝ} (hy : 0 ≤ y) : Summable fun k : ℕ => 1 / ((k : ℝ) + 1 + y) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summable_shift
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)

theorem psi1_continuousOn : ContinuousOn psi1 (Set.Icc 0 1) := by
  unfold psi1
  refine continuousOn_tsum (fun k => ?_) summable_shift fun k y hy => ?_
  · exact ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => by
      have := hy.1; positivity
  · have := hy.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)

theorem partial_le_psi1 (M : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2 ≤ psi1 y := by
  have : ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2 =
      ∑ j ∈ Finset.range M, 1 / ((j : ℝ) + 1 + y) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  exact (summable_psi1 hy).sum_le_tsum _ (fun j _ => by positivity)

/-- The lower step function for the second integral. -/
def L (M : ℕ) (y : ℝ) : ℝ :=
  (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + ind 0 1 y) *
    ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2

theorem L_eq (M : ℕ) (y : ℝ) : L M y = ∑ j ∈ Finset.range M,
    (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y / (y + ((j : ℝ) + 1)) ^ 2 +
      1 * ind 0 1 y / (y + ((j : ℝ) + 1)) ^ 2) := by
  unfold L
  simp only [Finset.mul_sum, mul_one_div, add_div, Finset.sum_div, one_mul]

theorem L_term_II (M : ℕ) : ∀ j ∈ Finset.range M, IntervalIntegrable (fun y =>
    ∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y / (y + ((j : ℝ) + 1)) ^ 2 +
      1 * ind 0 1 y / (y + ((j : ℝ) + 1)) ^ 2) volume 0 1 := by
  intro j _
  refine IntervalIntegrable.add (II_sum _ fun row hrow => ?_) ?_
  · obtain ⟨h1, -⟩ := T_facts row hrow
    exact step_II _ _ _ _ h1 (by positivity) (Nat.cast_nonneg _) (fun h => by linarith)
  · exact step_II _ _ _ _ le_rfl (by positivity) zero_le_one (fun h => by linarith)

theorem L_row_II (j : ℕ) : ∀ row ∈ T, IntervalIntegrable (fun y =>
    (row.2.2.2 : ℝ) * ind row.1 row.2.1 y / (y + ((j : ℝ) + 1)) ^ 2) volume 0 1 := by
  intro row hrow
  obtain ⟨h1, -⟩ := T_facts row hrow
  exact step_II _ _ _ _ h1 (by positivity) (Nat.cast_nonneg _) (fun h => by linarith)

theorem L_II (M : ℕ) : IntervalIntegrable (L M) volume 0 1 := by
  have : L M = fun y => ∑ j ∈ Finset.range M,
      (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y / (y + ((j : ℝ) + 1)) ^ 2 +
        1 * ind 0 1 y / (y + ((j : ℝ) + 1)) ^ 2) := funext (L_eq M)
  rw [this]
  exact II_sum _ (L_term_II M)

theorem integral_L (M : ℕ) : ∫ y in (0 : ℝ)..1, L M y = ∑ j ∈ Finset.range M,
    (∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) - 1 / (row.2.1 + ((j : ℝ) + 1))) +
      1 * (1 / (0 + ((j : ℝ) + 1)) - 1 / (1 + ((j : ℝ) + 1)))) := by
  rw [integral_congr (fun y _ => L_eq M y), intervalIntegral.integral_finsetSum (L_term_II M)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add (II_sum _ (L_row_II j))
      (step_II _ _ _ _ le_rfl (by positivity) zero_le_one (fun h => by linarith)),
    intervalIntegral.integral_finsetSum (L_row_II j),
    step_integral _ _ _ _ le_rfl zero_lt_one le_rfl (by positivity) (fun h => by linarith)]
  congr 1
  refine Finset.sum_congr rfl fun row hrow => ?_
  obtain ⟨h1, h2, h3, -⟩ := T_facts row hrow
  exact step_integral _ _ _ _ h1 h2 h3 (by positivity) (fun h => by linarith)

/-- The lower step function `S₁(y) = ∑ e₁ 𝟙_{(l,r)}(y) + 1`. -/
def S1 (y : ℝ) : ℝ := ∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + 1

theorem S1_measurable : Measurable S1 := by
  unfold S1
  exact (Finset.measurable_sum _ fun row _ => measurable_const.mul (ind_measurable _ _)).add
    measurable_const

theorem S1_nonneg (y : ℝ) : 0 ≤ S1 y := by
  unfold S1
  exact add_nonneg (Finset.sum_nonneg fun row _ => mul_nonneg (Nat.cast_nonneg _)
    (ind_nonneg _ _ _)) zero_le_one

theorem S1_le (y : ℝ) : |S1 y| ≤ 225 := by
  rw [abs_of_nonneg (S1_nonneg y)]
  have := tableValue_le (fun row => row.2.2.2) (fun row hrow => (T_facts row hrow).2.2.2.2.2) y
  rw [tableValue_eq] at this
  unfold S1
  linarith

theorem L_le (M : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : L M y ≤ S1 y * psi1 y := by
  unfold L S1
  have h1 : ind 0 1 y ≤ 1 := ind_le_one _ _ _
  have h2 : 0 ≤ ∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y :=
    Finset.sum_nonneg fun row _ => mul_nonneg (Nat.cast_nonneg _) (ind_nonneg _ _ _)
  have h3 : 0 ≤ ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have h4 := partial_le_psi1 M hy.1
  have h5 := ind_nonneg 0 1 y
  calc (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + ind 0 1 y) *
        ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2
      ≤ (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + 1) *
        ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) h3
    _ ≤ (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + 1) * psi1 y :=
        mul_le_mul_of_nonneg_left h4 (by linarith)

/-- The second integral is at least the finite chamber sum. -/
theorem integral_two_ge (M : ℕ) :
    ∫ y in (0 : ℝ)..1, L M y ≤ ∫ y in (0 : ℝ)..1, e34 (1 + y) * psi1 y := by
  have hae : ∀ᵐ y : ℝ, y ∈ Set.uIoc (0 : ℝ) 1 → e34 (1 + y) * psi1 y = S1 y * psi1 y := by
    filter_upwards [ae_notMem_wall] with y hy hy'
    rw [Set.uIoc_of_le zero_le_one] at hy'
    simp only [Finset.mem_insert, not_or] at hy
    have hy1 : y < 1 := lt_of_le_of_ne hy'.2 hy.1
    have hy0 : 0 < y := hy'.1
    have hfr : Int.fract (1 + y) = y := by
      rw [show (1 : ℝ) + y = ((1 : ℤ) : ℝ) + y by simp, Int.fract_intCast_add,
        Int.fract_eq_self.mpr ⟨hy'.1.le, hy1⟩]
    rw [e34_eq_of_one_le (by linarith) (by rw [hfr]; exact hy'.1.ne') (by rw [hfr]; exact hy.2),
      hfr, tableValue_eq]
    rfl
  rw [integral_congr_ae hae]
  refine integral_mono_on zero_le_one (L_II M) ?_ fun y hy => L_le M hy
  exact (II_of_bounded S1 S1_measurable 225 S1_le 0 1).mul_continuousOn
    (by rw [Set.uIcc_of_le zero_le_one]; exact psi1_continuousOn)

/-- The finite chamber constant `Σ_M`. -/
def Sig (M : ℕ) : ℝ :=
  ∑ row ∈ T, (row.2.2.1 : ℝ) * (1 / row.1 - 1 / row.2.1) + 1 * (1 / (1 / 19) - 1 / 1) +
    ∑ j ∈ Finset.range M,
      (∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) - 1 / (row.2.1 + ((j : ℝ) + 1))) +
        1 * (1 / (0 + ((j : ℝ) + 1)) - 1 / (1 + ((j : ℝ) + 1))))

theorem Sig_le_c34 (M : ℕ) : Sig M ≤ c34 := by
  unfold Sig c34
  rw [integral_one, ← integral_L M]
  have := integral_two_ge M
  unfold psi1 at this
  linarith

/-! ### The prime sums -/

/-- The prime number theorem as two-sided bounds. -/
theorem pnt_bounds {δ : ℝ} (hδ : 0 < δ) : ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x ≥ X₀,
    (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + δ) * x := by
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp prime_number_theorem δ hδ
  refine ⟨max X 1, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [le_max_right X 1]
  have h := hX x (le_trans (le_max_left _ _) hx)
  rw [Real.dist_eq, abs_lt] at h
  constructor
  · have : 1 - δ < Chebyshev.theta x / x := by linarith [h.1]
    exact ((lt_div_iff₀ hx0).mp this).le
  · have : Chebyshev.theta x / x < 1 + δ := by linarith [h.2]
    exact ((div_lt_iff₀ hx0).mp this).le

/-- `μ_N(a,b) = ∑_{a < N/p < b} log p`. -/
def muN (N : ℕ) (a b : ℝ) : ℝ := ∑ p ∈ primesUpTo N, ind a b ((N : ℝ) / p) * Real.log p

theorem theta_sub_eq (x y : ℝ) (hxy : y ≤ x) :
    Chebyshev.theta x - Chebyshev.theta y =
      ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, Real.log p := by
  unfold Chebyshev.theta
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊y⌋₊) (Nat.floor_mono hxy)]
  ring

/-- `μ_N(a,b) ≤ θ(N/a) - θ(N/b)`. -/
theorem muN_le_theta (N : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    muN N a b ≤ Chebyshev.theta (N / a) - Chebyshev.theta (N / b) := by
  have hb : 0 < b := ha.trans hab
  rw [theta_sub_eq _ _ (div_le_div_of_nonneg_left (Nat.cast_nonneg N) ha hab.le)]
  have hL : muN N a b = ∑ p ∈ (primesUpTo N).filter
      (fun p : ℕ => a < (N : ℝ) / p ∧ (N : ℝ) / p < b), Real.log p := by
    unfold muN ind
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [hL]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
  intro p hp
  simp only [Finset.mem_filter, primesUpTo, Finset.mem_range] at hp
  obtain ⟨⟨-, hprime⟩, h1, h2⟩ := hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime⟩
  · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hb]
    rw [div_lt_iff₀ hp0] at h2
    linarith
  · apply Nat.le_floor
    rw [le_div_iff₀ ha]
    rw [lt_div_iff₀ hp0] at h1
    linarith

/-- The chamber bound from the prime number theorem. -/
theorem chamber_le (N : ℕ) {δ X₀ : ℝ}
    (hpnt : ∀ x ≥ X₀, (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + δ) * x)
    {a b c : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a < b) (h0 : a = 0 → c = 0) (hX : X₀ ≤ N / b) :
    c * muN N a b ≤ c * ((N : ℝ) * (1 / a - 1 / b) + δ * N * (1 / a + 1 / b)) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · rw [h0 h.symm]; simp
  refine mul_le_mul_of_nonneg_left ?_ hc
  have hNa : X₀ ≤ N / a := hX.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg N) ha' hab.le)
  have h1 := (hpnt _ hNa).2
  have h2 := (hpnt _ hX).1
  have h3 := muN_le_theta N ha' hab
  have key : (1 + δ) * ((N : ℝ) / a) - (1 - δ) * ((N : ℝ) / b) =
      (N : ℝ) * (1 / a - 1 / b) + δ * N * (1 / a + 1 / b) := by ring
  linarith

/-- The tail `x ≥ M+1`. -/
theorem tail_le (N M : ℕ) :
    ∑ p ∈ primesUpTo N, (if (M : ℝ) + 1 ≤ (N : ℝ) / p then 1 else 0) * Real.log p ≤
      Chebyshev.theta (N / (M + 1)) := by
  have hL : ∑ p ∈ primesUpTo N, (if (M : ℝ) + 1 ≤ (N : ℝ) / p then 1 else 0) * Real.log p =
      ∑ p ∈ (primesUpTo N).filter (fun p : ℕ => (M : ℝ) + 1 ≤ (N : ℝ) / p), Real.log p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [hL]
  unfold Chebyshev.theta
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
  intro p hp
  simp only [Finset.mem_filter, primesUpTo, Finset.mem_range] at hp
  obtain ⟨⟨-, hprime⟩, h⟩ := hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hprime.pos, ?_⟩, hprime⟩
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hp0] at h
  linarith

/-- The walls: at most one prime per wall. -/
theorem wall_le (N M : ℕ) (hN : 0 < N) :
    ∑ p ∈ primesUpTo N, (if (N : ℝ) / p ∈ WallM M then 1 else 0) * Real.log p ≤
      (WallM M).card * Real.log (29 * N + 2) := by
  set S := (primesUpTo N).filter (fun p : ℕ => (N : ℝ) / p ∈ WallM M) with hS
  have hL : ∑ p ∈ primesUpTo N, (if (N : ℝ) / p ∈ WallM M then 1 else 0) * Real.log p =
      ∑ p ∈ S, Real.log p := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [hL]
  have hmem : ∀ p ∈ S, p.Prime ∧ p < 29 * N + 2 ∧ (N : ℝ) / p ∈ WallM M := by
    intro p hp
    simp only [hS, Finset.mem_filter, primesUpTo, Finset.mem_range] at hp
    exact ⟨hp.1.2, hp.1.1, hp.2⟩
  have hlog : ∀ p ∈ S, Real.log p ≤ Real.log (29 * N + 2) := by
    intro p hp
    obtain ⟨hpr, hpN, -⟩ := hmem p hp
    have : (p : ℝ) ≤ 29 * N + 2 := by exact_mod_cast hpN.le
    exact Real.log_le_log (by exact_mod_cast hpr.pos) this
  have hcard : S.card ≤ (WallM M).card := by
    refine Finset.card_le_card_of_injOn (fun p => (N : ℝ) / p) ?_ ?_
    · intro p hp
      exact (hmem p (Finset.mem_coe.mp hp)).2.2
    · intro p hp q hq hpq
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hmem p (Finset.mem_coe.mp hp)).1.ne_zero
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hmem q (Finset.mem_coe.mp hq)).1.ne_zero
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have := (div_eq_div_iff hp0 hq0).mp hpq
      have : (q : ℝ) = p := mul_left_cancel₀ hN0 this
      exact_mod_cast this.symm
  have hlog0 : 0 ≤ Real.log (29 * N + 2) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith)
  calc ∑ p ∈ S, Real.log p ≤ ∑ _p ∈ S, Real.log (29 * N + 2) := Finset.sum_le_sum hlog
    _ = S.card * Real.log (29 * N + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (WallM M).card * Real.log (29 * N + 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlog0

/-- The chamber sum of `G` over the primes. -/
theorem sum_G_eq (N M : ℕ) :
    ∑ p ∈ primesUpTo N, G M ((N : ℝ) / p) * Real.log p =
      ∑ row ∈ T, (row.2.2.1 : ℝ) * muN N row.1 row.2.1 + 1 * muN N (1 / 19) 1 +
        ∑ j ∈ Finset.range M, (∑ row ∈ T, (row.2.2.2 : ℝ) *
          muN N ((j : ℝ) + 1 + row.1) ((j : ℝ) + 1 + row.2.1) +
            1 * muN N ((j : ℝ) + 1) ((j : ℝ) + 2)) := by
  unfold G muN
  have h1 : ∀ p ∈ primesUpTo N,
      (∑ row ∈ T, (row.2.2.1 : ℝ) * ind row.1 row.2.1 ((N : ℝ) / p) + ind (1 / 19) 1 ((N : ℝ) / p) +
        ∑ j ∈ Finset.range M, (∑ row ∈ T, (row.2.2.2 : ℝ) * ind ((j : ℝ) + 1 + row.1)
          ((j : ℝ) + 1 + row.2.1) ((N : ℝ) / p) + ind ((j : ℝ) + 1) ((j : ℝ) + 2) ((N : ℝ) / p))) *
        Real.log p =
      ∑ row ∈ T, (row.2.2.1 : ℝ) * (ind row.1 row.2.1 ((N : ℝ) / p) * Real.log p) +
        ind (1 / 19) 1 ((N : ℝ) / p) * Real.log p +
        ∑ j ∈ Finset.range M, (∑ row ∈ T, (row.2.2.2 : ℝ) * (ind ((j : ℝ) + 1 + row.1)
          ((j : ℝ) + 1 + row.2.1) ((N : ℝ) / p) * Real.log p) +
            ind ((j : ℝ) + 1) ((j : ℝ) + 2) ((N : ℝ) / p) * Real.log p) := by
    intro p _
    simp only [add_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_congr rfl h1]
  simp only [Finset.mul_sum, one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm,
    Finset.sum_comm (s := primesUpTo N) (t := Finset.range M)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- The constant `D_M` controlling the error term. -/
def Dd (M : ℕ) : ℝ :=
  ∑ row ∈ T, (row.2.2.1 : ℝ) * (1 / row.1 + 1 / row.2.1) + 1 * (1 / (1 / 19) + 1 / 1) +
    ∑ j ∈ Finset.range M,
      (∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) + 1 / (row.2.1 + ((j : ℝ) + 1))) +
        1 * (1 / (0 + ((j : ℝ) + 1)) + 1 / (1 + ((j : ℝ) + 1))))

theorem sum_G_le (N M : ℕ) {δ X₀ : ℝ}
    (hpnt : ∀ x ≥ X₀, (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + δ) * x)
    (hX : X₀ ≤ N / (M + 1)) :
    ∑ p ∈ primesUpTo N, G M ((N : ℝ) / p) * Real.log p ≤ N * Sig M + δ * N * Dd M := by
  rw [sum_G_eq]
  have hXb : ∀ b : ℝ, 0 < b → b ≤ M + 1 → X₀ ≤ N / b := fun b hb hbM =>
    hX.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg N) hb hbM)
  -- the three groups of chambers
  have hA : ∑ row ∈ T, (row.2.2.1 : ℝ) * muN N row.1 row.2.1 ≤
      ∑ row ∈ T, (row.2.2.1 : ℝ) * ((N : ℝ) * (1 / row.1 - 1 / row.2.1) +
        δ * N * (1 / row.1 + 1 / row.2.1)) := by
    refine Finset.sum_le_sum fun row hrow => ?_
    obtain ⟨h1, h2, h3, h4, -⟩ := T_facts row hrow
    exact chamber_le N hpnt (Nat.cast_nonneg _) h1 h2 h4
      (hXb _ (by linarith) (by have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith))
  have hB : 1 * muN N (1 / 19) 1 ≤
      1 * ((N : ℝ) * (1 / (1 / 19) - 1 / 1) + δ * N * (1 / (1 / 19) + 1 / 1)) :=
    chamber_le N hpnt zero_le_one (by norm_num) (by norm_num) (by norm_num)
      (hXb _ one_pos (by have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith))
  have hC : ∀ j ∈ Finset.range M, ∑ row ∈ T, (row.2.2.2 : ℝ) *
      muN N ((j : ℝ) + 1 + row.1) ((j : ℝ) + 1 + row.2.1) + 1 * muN N ((j : ℝ) + 1) ((j : ℝ) + 2) ≤
      ∑ row ∈ T, (row.2.2.2 : ℝ) * ((N : ℝ) * (1 / ((j : ℝ) + 1 + row.1) - 1 / ((j : ℝ) + 1 + row.2.1)) +
        δ * N * (1 / ((j : ℝ) + 1 + row.1) + 1 / ((j : ℝ) + 1 + row.2.1))) +
        1 * ((N : ℝ) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) +
          δ * N * (1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 2))) := by
    intro j hj
    have hjM : (j : ℝ) + 1 ≤ M := by
      have := Finset.mem_range.mp hj
      exact_mod_cast this
    refine add_le_add (Finset.sum_le_sum fun row hrow => ?_) ?_
    · obtain ⟨h1, h2, h3, -⟩ := T_facts row hrow
      exact chamber_le N hpnt (Nat.cast_nonneg _) (by positivity) (by linarith)
        (fun h => by linarith) (hXb _ (by linarith) (by linarith))
    · exact chamber_le N hpnt zero_le_one (by positivity) (by linarith) (fun h => by linarith)
        (hXb _ (by linarith) (by linarith))
  have hsum := add_le_add (add_le_add hA hB) (Finset.sum_le_sum hC)
  refine hsum.trans (le_of_eq ?_)
  -- rearrange
  have eA : ∑ row ∈ T, (row.2.2.1 : ℝ) * ((N : ℝ) * (1 / row.1 - 1 / row.2.1) +
      δ * N * (1 / row.1 + 1 / row.2.1)) =
      N * ∑ row ∈ T, (row.2.2.1 : ℝ) * (1 / row.1 - 1 / row.2.1) +
        δ * N * ∑ row ∈ T, (row.2.2.1 : ℝ) * (1 / row.1 + 1 / row.2.1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have eC : ∀ j : ℕ, ∑ row ∈ T, (row.2.2.2 : ℝ) *
      ((N : ℝ) * (1 / ((j : ℝ) + 1 + row.1) - 1 / ((j : ℝ) + 1 + row.2.1)) +
        δ * N * (1 / ((j : ℝ) + 1 + row.1) + 1 / ((j : ℝ) + 1 + row.2.1))) +
        1 * ((N : ℝ) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) +
          δ * N * (1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 2))) =
      N * (∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) - 1 / (row.2.1 + ((j : ℝ) + 1))) +
        1 * (1 / (0 + ((j : ℝ) + 1)) - 1 / (1 + ((j : ℝ) + 1)))) +
      δ * N * (∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) + 1 / (row.2.1 + ((j : ℝ) + 1))) +
        1 * (1 / (0 + ((j : ℝ) + 1)) + 1 / (1 + ((j : ℝ) + 1)))) := by
    intro j
    have e1 : ∑ row ∈ T, (row.2.2.2 : ℝ) *
        ((N : ℝ) * (1 / ((j : ℝ) + 1 + row.1) - 1 / ((j : ℝ) + 1 + row.2.1)) +
          δ * N * (1 / ((j : ℝ) + 1 + row.1) + 1 / ((j : ℝ) + 1 + row.2.1))) =
        N * ∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) - 1 / (row.2.1 + ((j : ℝ) + 1))) +
        δ * N * ∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + ((j : ℝ) + 1)) + 1 / (row.2.1 + ((j : ℝ) + 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun row _ => ?_
      rw [add_comm (row.1 : ℝ), add_comm (row.2.1 : ℝ)]
      ring
    rw [e1]
    have : (0 : ℝ) + ((j : ℝ) + 1) = (j : ℝ) + 1 := by ring
    have h2 : (1 : ℝ) + ((j : ℝ) + 1) = (j : ℝ) + 2 := by ring
    rw [this, h2]
    ring
  rw [eA, Finset.sum_congr rfl fun j _ => eC j, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold Sig Dd
  ring

/-- `√N ≤ N` for `N ≥ 1`. -/
theorem sqrt_le_self_nat {N : ℕ} (hN : 1 ≤ N) : Real.sqrt N ≤ N := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩

end PNTStep

/-- **[7] The PNT step.** `∑_{p ≤ 29N+1} e₃₄(N/p) log p ≤ (c₃₄ + ε) N` for large `N`.
Proof: on each chamber `(l, r)` of `(0,1)`, and on `(k + l, k + r)` for `1 ≤ k ≤ K`, the PNT
gives `∑_{N/r < p < N/l} log p = (1/l - 1/r)N + o(N)`. Points on walls are finitely many
per unit interval, `O(log N)` in total. For `x > K` the contribution is at most
`5 θ(N/K) ≤ 5(1+ε)N/K`. Let `K → ∞`.
* Lines: proved here. The pointwise bound `e34_le_G` replaces `e₃₄(N/p)` by a finite chamber
  step function `G_M` on `(0, M+1)` plus a tail and a wall term; `chamber_le` applies the prime
  number theorem on each chamber; `Sig_le_c34` identifies the finite chamber sum with a lower
  bound for the integrals defining `c₃₄`.
* Directly from the PDF: partially ("One first applies the prime number theorem on finitely
  many such intervals; the remaining `x`-tail is `O(1/K)` uniformly"). -/
theorem profile_sum_le : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, profileSum N ≤ (c34 + ε) * N := by
  intro ε hε
  -- the cutoff `M`: `450/(M+1) ≤ ε/3`
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1350 / ε ≤ M := exists_nat_ge _
  have hM' : 450 / ((M : ℝ) + 1) ≤ ε / 3 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at hM
    nlinarith
  -- the PNT accuracy `δ`
  set δ := min 1 (ε / (3 * (|Dd M| + 1))) with hδ_def
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδD : δ * Dd M ≤ ε / 3 := by
    have h1 : δ ≤ ε / (3 * (|Dd M| + 1)) := min_le_right _ _
    have h2 : Dd M ≤ |Dd M| := le_abs_self _
    have h3 : 0 ≤ |Dd M| := abs_nonneg _
    calc δ * Dd M ≤ δ * |Dd M| := mul_le_mul_of_nonneg_left h2 hδpos.le
      _ ≤ ε / (3 * (|Dd M| + 1)) * |Dd M| := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  obtain ⟨X₀, hX₀1, hpnt⟩ := pnt_bounds hδpos
  -- eventually: `N/(M+1) ≥ X₀` and the wall term is `≤ εN/3`
  have ev1 : ∀ᶠ N : ℕ in atTop, X₀ ≤ (N : ℝ) / (M + 1) := by
    filter_upwards [eventually_ge_atTop ⌈((M : ℝ) + 1) * X₀⌉₊] with N hN
    have h1 : ((M : ℝ) + 1) * X₀ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have ev2 : ∀ᶠ N : ℕ in atTop,
      225 * ((WallM M).card * Real.log (29 * N + 2)) ≤ ε / 3 * N := by
    have hc : (0 : ℝ) < 225 * ((WallM M).card + 1) := by positivity
    have hε' : 0 < ε / 3 / (225 * ((WallM M).card + 1)) := by positivity
    filter_upwards [(Aux.log_affine_isLittleO 29 2 (by norm_num) (by norm_num)).def hε',
      eventually_ge_atTop 1] with N hN hN1
    have hlog0 : 0 ≤ Real.log (29 * N + 2) :=
      Real.log_nonneg (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hN
    have hsq := sqrt_le_self_nat hN1
    have hcard : ((WallM M).card : ℝ) ≤ (WallM M).card + 1 := by linarith
    have hN' : Real.log (29 * N + 2) ≤ ε / 3 / (225 * ((WallM M).card + 1)) * N :=
      hN.trans (mul_le_mul_of_nonneg_left hsq hε'.le)
    calc 225 * ((WallM M).card * Real.log (29 * N + 2))
        ≤ 225 * (((WallM M).card + 1) * (ε / 3 / (225 * ((WallM M).card + 1)) * N)) := by
          gcongr
      _ = ε / 3 * N := by field_simp
  filter_upwards [ev1, ev2, eventually_gt_atTop 0] with N hX hwall hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- pointwise bound and splitting of the sum
  have hpt : profileSum N ≤ ∑ p ∈ primesUpTo N,
      (225 * (if (M : ℝ) + 1 ≤ (N : ℝ) / p then 1 else 0) +
        225 * (if (N : ℝ) / p ∈ WallM M then 1 else 0) + G M ((N : ℝ) / p)) * Real.log p := by
    unfold profileSum
    refine Finset.sum_le_sum fun p hp => ?_
    have hpr := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    exact mul_le_mul_of_nonneg_right (e34_le_G M (div_pos hNr hp0)) (Real.log_natCast_nonneg p)
  have hsplit : ∑ p ∈ primesUpTo N,
      (225 * (if (M : ℝ) + 1 ≤ (N : ℝ) / p then 1 else 0) +
        225 * (if (N : ℝ) / p ∈ WallM M then 1 else 0) + G M ((N : ℝ) / p)) * Real.log p =
      225 * ∑ p ∈ primesUpTo N, (if (M : ℝ) + 1 ≤ (N : ℝ) / p then 1 else 0) * Real.log p +
      225 * ∑ p ∈ primesUpTo N, (if (N : ℝ) / p ∈ WallM M then 1 else 0) * Real.log p +
      ∑ p ∈ primesUpTo N, G M ((N : ℝ) / p) * Real.log p := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have htail := tail_le N M
  have hwl := wall_le N M hN
  have hG := sum_G_le N M hpnt hX
  have hθ := (hpnt _ hX).2
  have hSig := Sig_le_c34 M
  have hy : (0 : ℝ) ≤ N / (M + 1) := by positivity
  have h1 : (1 + δ) * ((N : ℝ) / (M + 1)) ≤ 2 * ((N : ℝ) / (M + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith) hy
  have h2 : 450 * ((N : ℝ) / (M + 1)) ≤ ε / 3 * N := by
    have := mul_le_mul_of_nonneg_right hM' hNr.le
    calc 450 * ((N : ℝ) / (M + 1)) = 450 / ((M : ℝ) + 1) * N := by ring
      _ ≤ ε / 3 * N := this
  have hSigN : (N : ℝ) * Sig M ≤ N * c34 := mul_le_mul_of_nonneg_left hSig hNr.le
  have hδDN : δ * N * Dd M ≤ ε / 3 * N := by
    have := mul_le_mul_of_nonneg_left hδD hNr.le
    linarith [this]
  calc profileSum N ≤ _ := hpt
    _ = _ := hsplit
    _ ≤ 225 * Chebyshev.theta (N / (M + 1)) +
        225 * ((WallM M).card * Real.log (29 * N + 2)) + (N * Sig M + δ * N * Dd M) := by
        gcongr
    _ ≤ (c34 + ε) * N := by nlinarith

section NumericBound

open MeasureTheory intervalIntegral

/-! ### Supporting lemmas for [8]: the tail of `ψ'` and the rational bound `B_K` -/

/-- Telescoping: `∑_{k ≥ 0} (g k - g (k+1)) = g 0` for `g k = 1/(k + c)`, `c > 0`. -/
theorem hasSum_telescope (c : ℝ) (hc : 0 < c) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + c) - 1 / ((k : ℝ) + 1 + c)) (1 / c) := by
  have hnn : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + c) - 1 / ((k : ℝ) + 1 + c) := fun k => by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + c) - 1 / ((i : ℝ) + 1 + c)) =
      1 / c - 1 / ((n : ℝ) + c) := by
    intro n
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + c)) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at this
    exact this
  simp_rw [hsum]
  have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + c)) atTop (𝓝 0) := by
    have := tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := c))
    exact (tendsto_inv_atTop_zero.comp this).congr fun n => by simp [one_div]
  simpa using tendsto_const_nhds.sub this

/-- Tail of `ψ'`: `∑_{k ≥ 0} (k + 1 + y)⁻² ≤ ∑_{k < M} (k + 1 + y)⁻² + 1/(M + 1/2 + y)`. -/
theorem psi1_le_partial (M : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    psi1 y ≤ ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2 + 1 / ((M : ℝ) + 1 / 2 + y) := by
  unfold psi1
  have hs := summable_psi1 hy
  rw [← hs.sum_add_tsum_nat_add M]
  have h1 : ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 1 + y) ^ 2 =
      ∑ j ∈ Finset.range M, 1 / (y + ((j : ℝ) + 1)) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  gcongr
  -- the tail
  have htel := hasSum_telescope ((M : ℝ) + 1 / 2 + y) (by positivity)
  rw [← htel.tsum_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff M).mpr hs) htel.summable
  have hx : 0 < (k : ℝ) + (M : ℝ) + 1 / 2 + y := by positivity
  have e1 : ((k + M : ℕ) : ℝ) + 1 + y = (k : ℝ) + M + 1 / 2 + y + 1 / 2 := by push_cast; ring
  have e2 : (k : ℝ) + ((M : ℝ) + 1 / 2 + y) = (k : ℝ) + M + 1 / 2 + y := by ring
  have e3 : (k : ℝ) + 1 + ((M : ℝ) + 1 / 2 + y) = (k : ℝ) + M + 1 / 2 + y + 1 := by ring
  rw [e1, e2, e3]
  set x := (k : ℝ) + M + 1 / 2 + y
  rw [div_sub_div _ _ hx.ne' (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `1/(a + y) ≤ 1/a - y/a² + y²/a³` for `a > 0`, `y ≥ 0`. -/
theorem inv_add_le_taylor {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    1 / (a + y) ≤ 1 / a - y / a ^ 2 + y ^ 2 / a ^ 3 := by
  have hay : 0 < a + y := by linarith
  rw [div_le_iff₀ hay]
  have : (1 / a - y / a ^ 2 + y ^ 2 / a ^ 3) * (a + y) = 1 + y ^ 3 / a ^ 3 := by
    field_simp; ring
  rw [this]
  have : 0 ≤ y ^ 3 / a ^ 3 := by positivity
  linarith

/-- `∫₀¹ e 𝟙_{(a,b)}(x) x^n dx = e (b^{n+1} - a^{n+1})/(n+1)`. -/
theorem step_integral_pow (a b e : ℝ) (n : ℕ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∫ x in (0 : ℝ)..1, e * ind a b x * x ^ n = e * ((b ^ (n + 1) - a ^ (n + 1)) / (n + 1)) := by
  have hind : (fun x => e * ind a b x * x ^ n) =
      Set.indicator (Set.Ioo a b) (fun x => e * x ^ n) := by
    funext x
    unfold ind
    by_cases hx : a < x ∧ x < b
    · rw [ite_eq_left hx, Set.indicator_of_mem (Set.mem_Ioo.mpr hx), mul_one]
    · rw [ite_eq_right hx, Set.indicator_of_notMem (fun h => hx (Set.mem_Ioo.mp h)), mul_zero,
        zero_mul]
  have hsub : Set.Ioo a b ∩ Set.Ioc 0 1 = Set.Ioo a b :=
    Set.inter_eq_left.mpr fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hind, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_indicator measurableSet_Ioo,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ioo, hsub,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_const_mul, integral_pow]

theorem step_pow_II (a b e : ℝ) (n : ℕ) :
    IntervalIntegrable (fun x => e * ind a b x * x ^ n) MeasureTheory.volume 0 1 := by
  have hm : Measurable (fun x => e * ind a b x) := measurable_const.mul (ind_measurable a b)
  have h1 : IntervalIntegrable (fun x => e * ind a b x) MeasureTheory.volume 0 1 := by
    refine II_of_bounded _ hm |e| (fun x => ?_) 0 1
    rw [abs_mul, abs_of_nonneg (ind_nonneg a b x)]
    exact mul_le_of_le_one_right (abs_nonneg e) (ind_le_one a b x)
  exact h1.mul_continuousOn (by fun_prop)

/-! ### The integrals of `S₁` against `(y+c)⁻²` and `yⁿ` -/

open MeasureTheory intervalIntegral in
/-- `∫₀¹ (y+c)⁻² dy = 1/c - 1/(1+c)` for `c > 0`. -/
theorem integral_inv_sq_add (c : ℝ) (hc : 0 < c) :
    ∫ y in (0 : ℝ)..1, 1 / (y + c) ^ 2 = 1 / c - 1 / (1 + c) := by
  have := step_integral 0 1 c 1 le_rfl zero_lt_one le_rfl hc.le (fun h => by linarith)
  rw [show 1 / c - 1 / (1 + c) = 1 * (1 / (0 + c) - 1 / (1 + c)) by ring, ← this]
  refine integral_congr_ae ?_
  filter_upwards [ae_notMem_wall] with y hy hy'
  rw [Set.uIoc_of_le zero_le_one] at hy'
  simp only [Finset.mem_insert, not_or] at hy
  have hy1 : y < 1 := lt_of_le_of_ne hy'.2 hy.1
  unfold ind
  rw [ite_eq_left ⟨hy'.1, hy1⟩]
  ring

open MeasureTheory intervalIntegral in
/-- `S₁ = ∑ e₁ 𝟙_{(l,r)} + 𝟙_{(0,1)}` almost everywhere on `(0,1]`. -/
theorem S1_ae_eq (g : ℝ → ℝ) :
    ∫ y in (0 : ℝ)..1, S1 y * g y =
      ∫ y in (0 : ℝ)..1, (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + ind 0 1 y) * g y := by
  refine integral_congr_ae ?_
  filter_upwards [ae_notMem_wall] with y hy hy'
  rw [Set.uIoc_of_le zero_le_one] at hy'
  simp only [Finset.mem_insert, not_or] at hy
  have hy1 : y < 1 := lt_of_le_of_ne hy'.2 hy.1
  unfold S1 ind
  rw [ite_eq_left ⟨hy'.1, hy1⟩]

open MeasureTheory intervalIntegral in
theorem integral_S1_inv_sq (c : ℝ) (hc : 1 ≤ c) :
    ∫ y in (0 : ℝ)..1, S1 y * (1 / (y + c) ^ 2) =
      ∑ row ∈ T, (row.2.2.2 : ℝ) * (1 / (row.1 + c) - 1 / (row.2.1 + c)) +
        1 * (1 / (0 + c) - 1 / (1 + c)) := by
  rw [S1_ae_eq]
  have hI : ∀ row ∈ T, IntervalIntegrable
      (fun y => (row.2.2.2 : ℝ) * ind row.1 row.2.1 y / (y + c) ^ 2) volume 0 1 :=
    fun row hrow => step_II _ _ _ _ (T_facts row hrow).1 (by linarith) (Nat.cast_nonneg _)
      (fun h => by linarith [(T_facts row hrow).1])
  have hI2 : IntervalIntegrable (fun y => 1 * ind 0 1 y / (y + c) ^ 2) volume 0 1 :=
    step_II _ _ _ _ le_rfl (by linarith) zero_le_one (fun h => by linarith)
  have e : (fun y => (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + ind 0 1 y) *
      (1 / (y + c) ^ 2)) = fun y => ∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y / (y + c) ^ 2 +
        1 * ind 0 1 y / (y + c) ^ 2 := by
    funext y
    simp only [mul_one_div, add_div, Finset.sum_div, one_mul]
  rw [e, integral_add (II_sum _ hI) hI2, integral_finsetSum hI,
    step_integral _ _ _ _ le_rfl zero_lt_one le_rfl (by linarith) (fun h => by linarith)]
  congr 1
  refine Finset.sum_congr rfl fun row hrow => ?_
  obtain ⟨h1, h2, h3, -⟩ := T_facts row hrow
  exact step_integral _ _ _ _ h1 h2 h3 (by linarith) (fun h => by linarith)

open MeasureTheory intervalIntegral in
theorem integral_S1_pow (n : ℕ) :
    ∫ y in (0 : ℝ)..1, S1 y * y ^ n =
      ∑ row ∈ T, (row.2.2.2 : ℝ) * ((row.2.1 ^ (n + 1) - row.1 ^ (n + 1)) / (n + 1)) +
        1 * ((1 ^ (n + 1) - 0 ^ (n + 1)) / (n + 1)) := by
  rw [S1_ae_eq]
  have e : (fun y => (∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y + ind 0 1 y) * y ^ n) =
      fun y => ∑ row ∈ T, (row.2.2.2 : ℝ) * ind row.1 row.2.1 y * y ^ n +
        1 * ind 0 1 y * y ^ n := by
    funext y
    simp only [add_mul, Finset.sum_mul, one_mul]
  rw [e, integral_add (II_sum _ fun row _ => step_pow_II _ _ _ n) (step_pow_II _ _ _ n),
    integral_finsetSum (fun row _ => step_pow_II _ _ _ n),
    step_integral_pow _ _ _ n le_rfl zero_lt_one le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun row hrow => ?_
  obtain ⟨h1, h2, h3, -⟩ := T_facts row hrow
  exact step_integral_pow _ _ _ n h1 h2 h3

theorem contOn_inv_sq (c : ℝ) (hc : 0 < c) :
    ContinuousOn (fun y : ℝ => 1 / (y + c) ^ 2) (Set.uIcc 0 1) := by
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => ?_
  rw [Set.uIcc_of_le zero_le_one] at hy
  have := hy.1
  positivity

theorem contOn_sum_inv_sq (K : ℕ) :
    ContinuousOn (fun y : ℝ => ∑ j ∈ Finset.range K, 1 / (y + ((j : ℝ) + 1)) ^ 2)
      (Set.uIcc 0 1) :=
  continuousOn_finsetSum _ fun j _ => contOn_inv_sq _ (by positivity)

/-! ### The rational upper bound -/

/-- The explicit rational upper bound `B_K ≥ c₃₄`. -/
def c34Bound (K : ℕ) : ℚ :=
  (∑ row ∈ T, (row.2.2.1 : ℚ) * (1 / row.1 - 1 / row.2.1) + 1 * (1 / (1 / 19) - 1 / 1)) +
    ∑ j ∈ Finset.range K,
      (∑ row ∈ T, (row.2.2.2 : ℚ) * (1 / (row.1 + ((j : ℚ) + 1)) - 1 / (row.2.1 + ((j : ℚ) + 1))) +
        1 * (1 / (0 + ((j : ℚ) + 1)) - 1 / (1 + ((j : ℚ) + 1)))) +
    ((∑ row ∈ T, (row.2.2.2 : ℚ) * ((row.2.1 ^ 1 - row.1 ^ 1) / 1) + 1 * ((1 ^ 1 - 0 ^ 1) / 1)) /
        ((K : ℚ) + 1 / 2) -
      (∑ row ∈ T, (row.2.2.2 : ℚ) * ((row.2.1 ^ 2 - row.1 ^ 2) / 2) + 1 * ((1 ^ 2 - 0 ^ 2) / 2)) /
        ((K : ℚ) + 1 / 2) ^ 2 +
      (∑ row ∈ T, (row.2.2.2 : ℚ) * ((row.2.1 ^ 3 - row.1 ^ 3) / 3) + 1 * ((1 ^ 3 - 0 ^ 3) / 3)) /
        ((K : ℚ) + 1 / 2) ^ 3)

open MeasureTheory intervalIntegral in
/-- `c₃₄ ≤ B_K` for every `K`. -/
theorem c34_le_bound (K : ℕ) : c34 ≤ (c34Bound K : ℝ) := by
  set a : ℝ := (K : ℝ) + 1 / 2 with ha_def
  have ha : 0 < a := by positivity
  -- the second integral
  have hae : ∀ᵐ y : ℝ, y ∈ Set.uIoc (0 : ℝ) 1 → e34 (1 + y) * psi1 y = S1 y * psi1 y := by
    filter_upwards [ae_notMem_wall] with y hy hy'
    rw [Set.uIoc_of_le zero_le_one] at hy'
    simp only [Finset.mem_insert, not_or] at hy
    have hy1 : y < 1 := lt_of_le_of_ne hy'.2 hy.1
    have hy0 : 0 < y := hy'.1
    have hfr : Int.fract (1 + y) = y := by
      rw [show (1 : ℝ) + y = ((1 : ℤ) : ℝ) + y by simp, Int.fract_intCast_add,
        Int.fract_eq_self.mpr ⟨hy'.1.le, hy1⟩]
    rw [e34_eq_of_one_le (by linarith) (by rw [hfr]; exact hy'.1.ne') (by rw [hfr]; exact hy.2),
      hfr, tableValue_eq]
    rfl
  -- the upper step function
  set U : ℝ → ℝ := fun y => S1 y * (∑ j ∈ Finset.range K, 1 / (y + ((j : ℝ) + 1)) ^ 2) +
    (S1 y * (1 / a) - S1 y * y ^ 1 * (1 / a ^ 2) + S1 y * y ^ 2 * (1 / a ^ 3)) with hU
  have hS1II : IntervalIntegrable S1 volume 0 1 := II_of_bounded S1 S1_measurable 225 S1_le 0 1
  have hUII : IntervalIntegrable U volume 0 1 := by
    rw [hU]
    refine ((hS1II.mul_continuousOn (contOn_sum_inv_sq K)).add
      (((hS1II.mul_continuousOn (by fun_prop)).sub
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop))).add
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop))))
  have hle : ∀ y ∈ Set.Icc (0 : ℝ) 1, S1 y * psi1 y ≤ U y := by
    intro y hy
    have h1 := psi1_le_partial K hy.1
    have h2 := inv_add_le_taylor ha hy.1
    have h3 := S1_nonneg y
    rw [hU]
    simp only
    have : 1 / ((K : ℝ) + 1 / 2 + y) = 1 / (a + y) := by rw [ha_def]
    rw [this] at h1
    calc S1 y * psi1 y ≤ S1 y * (∑ j ∈ Finset.range K, 1 / (y + ((j : ℝ) + 1)) ^ 2 + 1 / (a + y)) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ S1 y * (∑ j ∈ Finset.range K, 1 / (y + ((j : ℝ) + 1)) ^ 2 +
          (1 / a - y / a ^ 2 + y ^ 2 / a ^ 3)) :=
          mul_le_mul_of_nonneg_left (by linarith) h3
      _ = _ := by ring
  have hI2 : ∫ y in (0 : ℝ)..1, e34 (1 + y) * psi1 y ≤ ∫ y in (0 : ℝ)..1, U y := by
    rw [integral_congr_ae hae]
    refine integral_mono_on zero_le_one ?_ hUII hle
    exact hS1II.mul_continuousOn (by rw [Set.uIcc_of_le zero_le_one]; exact psi1_continuousOn)
  -- evaluate `∫ U`
  have hsumII : ∀ j ∈ Finset.range K, IntervalIntegrable
      (fun y => S1 y * (1 / (y + ((j : ℝ) + 1)) ^ 2)) volume 0 1 :=
    fun j _ => hS1II.mul_continuousOn (contOn_inv_sq _ (by positivity))
  have hU1 : ∫ y in (0 : ℝ)..1, S1 y * (∑ j ∈ Finset.range K, 1 / (y + ((j : ℝ) + 1)) ^ 2) =
      ∑ j ∈ Finset.range K, (∑ row ∈ T, (row.2.2.2 : ℝ) *
        (1 / (row.1 + ((j : ℝ) + 1)) - 1 / (row.2.1 + ((j : ℝ) + 1))) +
          1 * (1 / (0 + ((j : ℝ) + 1)) - 1 / (1 + ((j : ℝ) + 1)))) := by
    have e : (fun y => S1 y * (∑ j ∈ Finset.range K, 1 / (y + ((j : ℝ) + 1)) ^ 2)) =
        fun y => ∑ j ∈ Finset.range K, S1 y * (1 / (y + ((j : ℝ) + 1)) ^ 2) := by
      funext y; rw [Finset.mul_sum]
    rw [e, integral_finsetSum hsumII]
    exact Finset.sum_congr rfl fun j _ => integral_S1_inv_sq _ (by
      have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
  have hp0 : ∫ y in (0 : ℝ)..1, S1 y * (1 / a) = (∫ y in (0 : ℝ)..1, S1 y * y ^ 0) * (1 / a) := by
    rw [← intervalIntegral.integral_mul_const]; simp
  have hp1 : ∫ y in (0 : ℝ)..1, S1 y * y ^ 1 * (1 / a ^ 2) =
      (∫ y in (0 : ℝ)..1, S1 y * y ^ 1) * (1 / a ^ 2) := by rw [← intervalIntegral.integral_mul_const]
  have hp2 : ∫ y in (0 : ℝ)..1, S1 y * y ^ 2 * (1 / a ^ 3) =
      (∫ y in (0 : ℝ)..1, S1 y * y ^ 2) * (1 / a ^ 3) := by rw [← intervalIntegral.integral_mul_const]
  have hIU : ∫ y in (0 : ℝ)..1, U y = (∑ j ∈ Finset.range K, (∑ row ∈ T, (row.2.2.2 : ℝ) *
        (1 / (row.1 + ((j : ℝ) + 1)) - 1 / (row.2.1 + ((j : ℝ) + 1))) +
          1 * (1 / (0 + ((j : ℝ) + 1)) - 1 / (1 + ((j : ℝ) + 1))))) +
      ((∫ y in (0 : ℝ)..1, S1 y * y ^ 0) * (1 / a) - (∫ y in (0 : ℝ)..1, S1 y * y ^ 1) * (1 / a ^ 2)
        + (∫ y in (0 : ℝ)..1, S1 y * y ^ 2) * (1 / a ^ 3)) := by
    rw [hU]
    simp only
    rw [integral_add (hS1II.mul_continuousOn (contOn_sum_inv_sq K)) (((hS1II.mul_continuousOn (by fun_prop)).sub
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop))).add
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop))),
      integral_add ((hS1II.mul_continuousOn (by fun_prop)).sub
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop)))
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop)),
      integral_sub (hS1II.mul_continuousOn (by fun_prop))
        ((hS1II.mul_continuousOn (by fun_prop)).mul_continuousOn (by fun_prop)),
      hU1, hp0, hp1, hp2]
  -- assemble
  unfold c34
  rw [integral_one]
  have hfinal := hI2.trans (le_of_eq hIU)
  unfold psi1 at hfinal
  rw [integral_S1_pow 0, integral_S1_pow 1, integral_S1_pow 2] at hfinal
  unfold c34Bound
  push_cast
  rw [ha_def] at hfinal
  norm_num at hfinal ⊢
  simp only [div_eq_mul_inv] at hfinal ⊢
  linarith

/-- The kernel-checked numerical bound. -/
theorem c34Bound_lt : c34Bound 64 < 57784 / 1000 := by
  decide +kernel

end NumericBound

/-- **[8] The numerical bound `c₃₄ < 57.784`.** The first integral is the finite rational sum
`∑ e (1/l - 1/r) = 9967051/272272 + 18`. The second is `∑_{k ≤ 4096}` of rational interval
terms, rounded up, plus a tail `≤ m/4096` with `m = ∫₀¹ e₃₄(1+y) dy = 1313791/604656 + 1`.
* Lines: proved here. `c34_le_bound K` bounds `c₃₄` by the rational number `c34Bound K`: the
  first integral is `integral_one`, the second is bounded by truncating `ψ'(1+y)` after `K`
  terms with the telescoping tail `∑_{k ≥ K} (k+1+y)⁻² ≤ 1/(K+1/2+y)` (`psi1_le_partial`) and
  the expansion `1/(a+y) ≤ 1/a - y/a² + y²/a³`. `c34Bound 64 < 57.784` is a kernel-checked
  rational computation (`decide +kernel`).
* Directly from the PDF: partially. The PDF gives the method and the outcome. The finite sum is
  in `verify_arithmetic.py`. -/
theorem c34_lt : c34 < 57.784 := by
  have h := c34_le_bound 64
  have h2 : ((c34Bound 64 : ℚ) : ℝ) < ((57784 / 1000 : ℚ) : ℝ) := Rat.cast_lt.mpr c34Bound_lt
  push_cast at h2
  calc c34 ≤ _ := h
    _ < 57784 / 1000 := h2
    _ = 57.784 := by norm_num


theorem profileTable_eq : profileTable = CH.ptableN.map CH.toRow := by
  unfold profileTable CH.ptableN CH.toRow
  simp only [List.map_cons, List.map_nil, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_div,
    div_one]

/-- The table value at a point of a cell `(l, r)` contained in `row` and disjoint from the other
rows. -/
theorem tableValue_row (col : ℚ × ℚ × ℕ × ℕ → ℕ) (row : ℚ × ℚ × ℕ × ℕ)
    (hrow : row ∈ profileTable) (l r : ℚ) (hl : row.1 ≤ l) (hr : r ≤ row.2.1)
    (hdisj : ∀ row' ∈ profileTable, row' = row ∨ row'.2.1 ≤ l ∨ r ≤ row'.1)
    (x : ℝ) (hxl : (l : ℝ) < x) (hxr : x < r) : tableValue col x = col row := by
  rw [tableValue_eq, Finset.sum_eq_single row]
  · have h1 : (row.1 : ℝ) < x := lt_of_le_of_lt ((Rat.cast_le (K := ℝ)).mpr hl) hxl
    have h2 : x < (row.2.1 : ℝ) := lt_of_lt_of_le hxr ((Rat.cast_le (K := ℝ)).mpr hr)
    rw [ind, ite_eq_left ⟨h1, h2⟩, mul_one]
  · intro b hb hne
    rcases hdisj b (mem_T.mp hb) with h | h | h
    · exact absurd h hne
    · have h' := (Rat.cast_le (K := ℝ)).mpr h
      rw [ind, ite_eq_right (fun h'' => by linarith [h''.2]), mul_zero]
    · have h' := (Rat.cast_le (K := ℝ)).mpr h
      rw [ind, ite_eq_right (fun h'' => by linarith [h''.1]), mul_zero]
  · intro h; exact absurd (mem_T.mpr hrow) h

/-- **[4] The chamber profile.** For large `N` and every prime `√(30N+10) < p ≤ 29N+1` that
does not divide the boundary product, `E₃₄(N,p) ≤ e₃₄(N/p)`.

Proof outline (PDF Part VII §4, Part IV):
(a) for `p > √(30N+10)`: `f_p(m) = ⌊m/p⌋` and `ℓ_p(m) = 𝟙_{m ≥ p}` on the relevant ranges;
    ≈ 200 lines;
(b) all jumps in `k` have the form `k = cN + jp + s`, `|s| ≤ 2`, with `c ∈ 𝓢_o ∪ 𝓢_d`. Off the
    boundary primes, the order of the jumps depends only on the Farey-29 chamber of `x = N/p`
    (or of `{x}` for `x > 1`, where the profile is periodic); ≈ 800 lines;
(c) on each of the 270 chambers, evaluate `E_o, E_{o4}, E_d, E_{d4}` exactly at the jump points
    with infinitesimal offsets `-3,…,3`. This is the content of `verify_arithmetic.py`
    (functions `original_eps`, `dual_eps`, `original_bc`, `dual_second`, `common`). In Lean
    it would be a kernel-checked (`decide`) certificate over the chamber data; ≈ 3000 lines
    including the reflection layer.
* Lines: ≈ 4000.
* Directly from the PDF: no. The PDF states the result and the method. The finite case analysis
  is only in `verify_arithmetic.py`. -/
theorem chamber_profile : ∀ᶠ N : ℕ in atTop, ∀ p ∈ primesUpTo N,
    √(30 * N + 10) < (p : ℝ) → ¬ (p : ℤ) ∣ boundaryProd N →
      ((E34 N p).toNat : ℝ) ≤ e34 ((N : ℝ) / p) := by
  rw [Filter.eventually_atTop]
  refine ⟨31, fun N hN p hp hsq hnd => ?_⟩
  have hpr : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  have hsq' : 30 * N + 10 < p ^ 2 := by
    have h := (Real.sqrt_lt' hp0).mp hsq
    exact_mod_cast h
  have hNB := CH.NB_of_boundary hnd
  have hp29 : 29 < p := by nlinarith
  have hden : ∀ row ∈ profileTable, row.1.den ≤ 29 ∧ row.2.1.den ≤ 29 := by
    rw [profileTable_eq]
    intro row hrow
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrow
    exact CH.ptable_den q hq
  have hcore := CH.chamber_core hN hpr hsq' hnd
  have hwall : ∀ M : ℕ, CH.NB M p → (M : ℝ) / p ∉ Wall0 := fun M hM hmem => by
    unfold Wall0 at hmem
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hmem
    rcases hmem with h | ⟨row, hrow, h⟩ | ⟨row, hrow, h⟩
    · exact CH.not_wall_real hpr hp29 hM (1 / 19)
        (by have := CH.den_div_le 1 19 (by norm_num); push_cast at this; omega)
        (by rw [h]; push_cast; ring)
    · exact CH.not_wall_real hpr hp29 hM row.1 (hden row (mem_T.mp hrow)).1 h.symm
    · exact CH.not_wall_real hpr hp29 hM row.2.1 (hden row (mem_T.mp hrow)).2 h.symm
  have hmod := CH.mod_ne_zero hNB
  have cast_lt : ∀ (q : ℚ) (M : ℕ), q < (M : ℚ) / p → (q : ℝ) < (M : ℝ) / p := fun q M h => by
    have := (Rat.cast_lt (K := ℝ)).mpr h
    rwa [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at this
  have cast_lt' : ∀ (q : ℚ) (M : ℕ), (M : ℚ) / p < q → (M : ℝ) / p < (q : ℝ) := fun q M h => by
    have := (Rat.cast_lt (K := ℝ)).mpr h
    rwa [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at this
  have hflag : ∀ (i : ℕ), i < 270 → ∀ x : ℝ, x < 1 → ((CH.rat (CH.fareyL i) : ℚ) : ℝ) < x →
      x < ((CH.rat (CH.fareyL (i + 1)) : ℚ) : ℝ) → ind (1 / 19) 1 x = CH.flag i := by
    intro i hi x hx1 hl hr
    rcases CH.flag_spec i hi with ⟨hf, h19⟩ | ⟨hf, h19⟩
    · have := (Rat.cast_le (K := ℝ)).mpr h19
      push_cast at this
      rw [hf, ind, ite_eq_left ⟨by linarith, hx1⟩, Nat.cast_one]
    · have := (Rat.cast_le (K := ℝ)).mpr h19
      push_cast at this
      rw [hf, ind, ite_eq_right (fun h' => by linarith [h'.1]), Nat.cast_zero]
  rcases lt_trichotomy N p with hlt | heq | hgt
  · obtain ⟨i, hi, hl, hr, hE⟩ := hcore.1 hlt
    have hx1 : (N : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact_mod_cast hlt
    have h4 := CH.row_contains i hi
    rw [e34_eq_of_lt_one (by positivity) hx1 (hwall N hNB),
      tableValue_row _ (CH.toRow (CH.rowN i)) (by rw [profileTable_eq]; exact CH.row_mem i hi) _ _
        h4.1 h4.2 (by rw [profileTable_eq]; exact CH.row_disjoint i hi) _ (cast_lt _ _ hl)
        (cast_lt' _ _ hr), hflag i hi _ hx1 (cast_lt _ _ hl) (cast_lt' _ _ hr)]
    exact_mod_cast hE
  · exact absurd (by rw [heq, Nat.mod_self]) hmod
  · obtain ⟨i, hi, hl, hr, hE⟩ := hcore.2 hgt
    have hfr := CH.fract_div N p hpr.pos
    have hx : (1 : ℝ) ≤ (N : ℝ) / p := by rw [le_div_iff₀ hp0, one_mul]; exact_mod_cast hgt.le
    have h0 : Int.fract ((N : ℝ) / p) ≠ 0 := by
      rw [hfr]
      exact div_ne_zero (by exact_mod_cast hmod) hp0.ne'
    have h4 := CH.row_contains i hi
    rw [e34_eq_of_one_le hx h0 (by rw [hfr]; exact hwall _ (CH.NB_mod hpr.pos hNB)), hfr,
      tableValue_row _ (CH.toRow (CH.rowN i)) (by rw [profileTable_eq]; exact CH.row_mem i hi) _ _
        h4.1 h4.2 (by rw [profileTable_eq]; exact CH.row_disjoint i hi) _ (cast_lt _ _ hl)
        (cast_lt' _ _ hr)]
    exact_mod_cast hE

/-- **[9] Splitting `log Δ_N`.** Every prime `p ≤ 29N+1` is small, a boundary prime, or covered
by [4]. All terms are `≥ 0` (`E₃₄ ≥ 0`, `e₃₄ ≥ 0`, `log p ≥ 0`).
* Lines: ≈ 100 (given [3], [4]: `Finset.sum_filter_add_sum_filter_not` twice, termwise bounds).
* Directly from the PDF: yes. -/
theorem log_Delta_split :
    ∀ᶠ N : ℕ in atTop, Real.log (Delta N) ≤ smallSum N + boundarySum N + profileSum N := by
  have htv : ∀ (col : ℚ × ℚ × ℕ × ℕ → ℕ) (y : ℝ), 0 ≤ tableValue col y := fun col y =>
    List.sum_nonneg fun x hx => by
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
      split_ifs <;> positivity
  have he34 : ∀ x : ℝ, 0 ≤ e34 x := fun x => by
    unfold e34
    have h1 := htv (fun row => row.2.2.1) x
    have h2 := htv (fun row => row.2.2.2) (Int.fract x)
    split_ifs <;> linarith
  filter_upwards [chamber_profile, eventually_ge_atTop 1] with N hch hN
  rw [log_Delta_eq_sum N hN]
  unfold smallSum boundarySum profileSum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hpos := mul_nonneg (he34 ((N : ℝ) / p)) hlog
  have ht : 0 ≤ ((E34 N p).toNat : ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg _) hlog
  split_ifs with h1 h2 h2
  · linarith
  · linarith
  · linarith
  · have := mul_le_mul_of_nonneg_right (hch p hp (lt_of_not_ge h1) h2) hlog
    linarith

/-- **Main theorem (`blueprint.lean`, `log_Delta_le`).** Proved from [5]–[9]: with
`ε = (57.784 - c₃₄)/3 > 0`, `log Δ_N ≤ εN + εN + (c₃₄ + ε)N = 57.784 N`. -/
theorem log_Delta_le : ∀ᶠ N : ℕ in atTop, Real.log (Delta N) ≤ 57.784 * N := by
  have hc := c34_lt
  set ε := (57.784 - c34) / 3 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  filter_upwards [log_Delta_split, small_primes_negligible ε hε,
    boundary_primes_negligible ε hε, profile_sum_le ε hε] with N h1 h2 h3 h4
  have key : ε * N * 3 = 57.784 * N - c34 * N := by rw [hε_def]; ring
  nlinarith

end ZetasIrr.BP
