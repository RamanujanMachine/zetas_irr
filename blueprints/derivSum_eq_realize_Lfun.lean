/-
# Blueprint for `ZetasIrr.derivSum_eq_realize_Lfun`

Statement (as in `blueprint.lean`): for a proper `f ∈ ℚ(t)` all of whose poles are integers `≤ K`,
`-∑_{t > K} f'(t) = realize(𝓛_K[f])`.

Source: PDF Part VII §7: "If all poles of `f` are integers at most `K`, write its polynomial and
partial-fraction decomposition and define `𝓛_K[…]` … For a proper rational function this is the
formal value of `-∑_{t>K} f'(t)`." See also Part III.

Strategy. Write `f = ∑_{h,r≥1} c_{h,r}(t-h)^{-r}`, where `c_{h,r}` is the Laurent coefficient
`pfCoeff f h r`. Then `-f'(t) = ∑ r c_{h,r}(t-h)^{-r-1}`. Exchange the finite and the infinite
sums, which is allowed because each series converges absolutely (exponent `≥ 2`). Finally use
`∑_{t>K}(t-h)^{-s} = ζ(s) - H^{(s)}_{K-h}`.

| # | Supporting lemma                  | Est. lines | Directly from PDF? |
|---|-----------------------------------|-----------:|--------------------|
| 1 | `polyPart_eq_zero_of_proper`      |   (proved) | Yes                |
| 2 | `realize_Lfun_of_polyPart_eq_zero`|   (proved) | Yes                |
| 3 | `deriv_rfReal_eq`                 |   (proved) | Partially          |
| 4 | `summable_pole_terms`             |   (proved) | Yes                |
| 5 | `tsum_pole_term`                  |   (proved) | Yes                |
| 6 | `hasLaurentPartialFractions`      |   (proved) | Partially          |

All supporting lemmas are proved; the file contains no `sorry`. [2], [4], [5] are proved, using results of `cross_product_readout.lean`
(imported via `ZetasAux`). The declarations of this file live in the namespace `ZetasIrr.BP`.

**Correction.** The statement in `blueprint.lean` is false. It constrains only the *rational*
roots of the denominator: for `f = 1/(t² + 1)` there are none, so `𝓛_K[f] = 0`, while
`-∑_{t>K} f'(t) ≠ 0`. The main theorem and the two lemmas [3], [6], which are false for the
same reason, now also assume that the denominator splits over `ℚ`
(`hsplit : f.denom.roots.card = f.denom.natDegree`). This is the PDF's standing assumption
that *all* poles are integers. The corrected main theorem is proved without any `sorry` in
`cross_product_readout.lean` (`derivSum_eq_realize_Lfun'`).
-/
import ZetasAux

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries

noncomputable section

namespace ZetasIrr.BP

/-- **[1] Proper functions have no polynomial part.**
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem polyPart_eq_zero_of_proper (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree) : polyPart f = 0 := by
  unfold polyPart
  rw [Polynomial.divByMonic_eq_zero_iff (RatFunc.monic_denom f)]
  exact Polynomial.degree_lt_degree hproper

/-- **[2] Realisation of `𝓛_K[f]` without polynomial part.** Unfolding `Lfun` and `realize`
(`realize` is additive, `realize (Zsym 0) = 1`, `realize (Zsym (r+1)) = ζ(r+1)`).
* Lines: proved (`cross_product_readout.lean`).
* Directly from the PDF: yes (definition of `𝓛_K`, `Z_r ↦ ζ(r)`). -/
theorem realize_Lfun_of_polyPart_eq_zero (K : ℤ) (f : ℚ⟮X⟯) (h0 : polyPart f = 0) :
    realize (Lfun K f) =
      ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.range (f.denom.natDegree + 1),
        (r : ℝ) * (pfCoeff f h r : ℝ) *
          ((riemannZeta ((r + 1 : ℕ) : ℂ)).re - (harm (r + 1) ⌊(K : ℚ) - h⌋ : ℝ)) :=
  ZetasIrr.realize_Lfun_of_polyPart_eq_zero K f h0

/-- **[6] Partial-fraction expansion through Laurent coefficients.** For proper `f` with only
rational poles, `f(x) = ∑_h ∑_{1 ≤ r ≤ deg} c_{h,r} (x - h)^{-r}` at every non-pole `x`, with
`c_{h,r} = pfCoeff f h r`.

This is the key algebraic input of [3]. Mathlib has `div_eq_quo_add_sum_rem_div`
(`Mathlib/Algebra/Polynomial/PartialFractions.lean`) for the existence of a decomposition. What
is missing is the identification of its coefficients with the Laurent coefficients
`(RatFunc.laurent h f).coeff (-r)`. Uniqueness of principal parts gives it.
* Lines: proved here, from `exists_eq_ppSum`, `pfCoeff_ppSum` and `rfReal_ppSum` of
  `cross_product_readout.lean`.
* Directly from the PDF: partially. The PDF takes partial fractions for granted. -/
theorem hasLaurentPartialFractions (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree) (x : ℝ)
    (hx : ∀ h ∈ f.denom.roots, (x : ℝ) ≠ h) :
    rfReal f x = ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.Icc 1 f.denom.natDegree,
      (pfCoeff f h r : ℝ) * ((x - h) ^ r)⁻¹ := by
  obtain ⟨c, hc⟩ := exists_eq_ppSum f hproper hsplit
  set R := f.denom.roots.toFinset with hR
  set b : ℚ → ℕ := fun h => f.denom.roots.count h with hb
  have hpf : ∀ h ∈ R, ∀ r, 1 ≤ r → pfCoeff f h r = if r ≤ b h then c h r else 0 := by
    intro h hh r hr
    have := pfCoeff_ppSum R b c hh hr
    rwa [← hc] at this
  have hbD : ∀ h, b h ≤ f.denom.natDegree := fun h =>
    (Multiset.count_le_card h _).trans hsplit.le
  have hval : rfReal f x = rfReal (ppSum R b c) x := by rw [← hc]
  rw [hval, rfReal_ppSum R b c x (fun h hh => hx h (Multiset.mem_toFinset.mp hh))]
  refine Finset.sum_congr rfl fun h hh => ?_
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_right (hbD h)) ?_ ?_
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_sdiff.mp hr
    have hr1' := Finset.mem_Icc.mp hr1
    have : ¬ r ≤ b h := fun hle => hr2 (Finset.mem_Icc.mpr ⟨hr1'.1, hle⟩)
    rw [hpf h hh r hr1'.1]
    simp [this]
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    rw [hpf h hh r hr1]
    simp [hr2]

/-- **[3] Derivative of `f` beyond the poles.** For `x > K`:
`f'(x) = -∑_h ∑_r r c_{h,r} (x - h)^{-r-1}`. The `r = 0` terms are zero. The proof
differentiates [6] on the open set `(K, ∞)`, which contains no pole.
* Lines: proved here, by differentiating [6] on the neighbourhood `(K, ∞)` of `x`
  (`Filter.EventuallyEq.deriv_eq`, `hasDerivAt_inv_pow_sub`).
* Directly from the PDF: partially (see [6]). -/
theorem deriv_rfReal_eq (K : ℤ) (f : ℚ⟮X⟯) (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree)
    (hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, n ≤ K ∧ h = n) (x : ℝ) (hx : (K : ℝ) < x) :
    deriv (rfReal f) x =
      ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.range (f.denom.natDegree + 1),
        -((r : ℝ) * (pfCoeff f h r : ℝ) * (((x - h) ^ (r + 1))⁻¹)) := by
  set R := f.denom.roots.toFinset with hR
  set D := f.denom.natDegree with hD
  have hxR : ∀ y : ℝ, (K : ℝ) < y → ∀ h ∈ f.denom.roots, y ≠ h := by
    intro y hy h hh
    obtain ⟨n, hn, rfl⟩ := hpoles h hh
    have : ((n : ℚ) : ℝ) ≤ K := by push_cast; exact_mod_cast hn
    exact ne_of_gt (lt_of_le_of_lt this hy)
  have heq : rfReal f =ᶠ[𝓝 x] fun y =>
      ∑ h ∈ R, ∑ r ∈ Finset.Icc 1 D, (pfCoeff f h r : ℝ) * ((y - h) ^ r)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hasLaurentPartialFractions f hproper hsplit y (hxR y hy)
  rw [heq.deriv_eq]
  rw [(HasDerivAt.fun_sum (u := R)
      (A := fun (h : ℚ) (y : ℝ) => ∑ r ∈ Finset.Icc 1 D, (pfCoeff f h r : ℝ) * ((y - (h : ℝ)) ^ r)⁻¹)
      fun h hh => HasDerivAt.fun_sum (u := Finset.Icc 1 D)
        (A := fun (r : ℕ) (y : ℝ) => (pfCoeff f h r : ℝ) * ((y - (h : ℝ)) ^ r)⁻¹) fun r _ =>
          (hasDerivAt_inv_pow_sub _ r x (hxR x hx h (Multiset.mem_toFinset.mp hh))).const_mul
            _).deriv]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    show Finset.Ico (0 + 1) (D + 1) = Finset.Icc 1 D by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  simp only [Nat.cast_zero, zero_mul, neg_zero, zero_add]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **[4] Absolute convergence of each pole term.** For a pole `h ≤ K` and `r ≥ 1`, the series
`∑_n (K + 1 + n - h)^{-(r+1)}` is a tail of `∑ m^{-(r+1)}`. For `r = 0` the term is `0`.
* Lines: proved here.
* Directly from the PDF: yes ("the convergent sum"). -/
theorem summable_pole_terms (K : ℤ) (h : ℚ) (hh : ∃ n : ℤ, n ≤ K ∧ h = n) (c : ℝ) (r : ℕ) :
    Summable fun n : ℕ => (r : ℝ) * c * (((K : ℝ) + 1 + n - h) ^ (r + 1))⁻¹ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · exact (ZetasIrr.summable_pole K h hh (r + 1) (by omega)).mul_left _

/-- **[5] The tail sums are `ζ(s) - H^{(s)}`.** For an integer pole `h ≤ K`:
`r ∑_{n ≥ 0} (K + 1 + n - h)^{-(r+1)} = r (ζ(r+1) - H^{(r+1)}_{K-h})`. Both sides vanish for
`r = 0`.
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem tsum_pole_term (K : ℤ) (h : ℚ) (hh : ∃ n : ℤ, n ≤ K ∧ h = n) (r : ℕ) :
    (r : ℝ) * ∑' n : ℕ, (((K : ℝ) + 1 + n - h) ^ (r + 1))⁻¹ =
      (r : ℝ) * ((riemannZeta ((r + 1 : ℕ) : ℂ)).re - (harm (r + 1) ⌊(K : ℚ) - h⌋ : ℝ)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [ZetasIrr.tsum_pole K h hh (r + 1) (by omega)]

/-- **Main theorem (corrected form of `blueprint.lean`'s `derivSum_eq_realize_Lfun`: the
denominator must split over `ℚ`).** Proved from [1]–[5]. -/
theorem derivSum_eq_realize_Lfun (K : ℤ) (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree)
    (hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, n ≤ K ∧ h = n) :
    derivSum K f = realize (Lfun K f) := by
  set R := f.denom.roots.toFinset
  set D := Finset.range (f.denom.natDegree + 1)
  have hpR : ∀ h ∈ R, ∃ n : ℤ, n ≤ K ∧ h = n := fun h hh =>
    hpoles h (Multiset.mem_toFinset.mp hh)
  -- the derivative at the summation points
  have e1 : (fun n : ℕ => deriv (rfReal f) ((K : ℝ) + 1 + n)) = fun n : ℕ =>
      -∑ h ∈ R, ∑ r ∈ D, (r : ℝ) * (pfCoeff f h r : ℝ) *
        ((((K : ℝ) + 1 + n - h) ^ (r + 1))⁻¹) := by
    funext n
    rw [deriv_rfReal_eq K f hproper hsplit hpoles _
      (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)]
    simp only [Finset.sum_neg_distrib]
    rfl
  rw [derivSum, e1, tsum_neg, neg_neg,
    Summable.tsum_finsetSum fun h hh => summable_sum fun r _ =>
      summable_pole_terms K h (hpR h hh) _ r,
    realize_Lfun_of_polyPart_eq_zero K f (polyPart_eq_zero_of_proper f hproper)]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Summable.tsum_finsetSum fun r _ => summable_pole_terms K h (hpR h hh) _ r]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [tsum_mul_left]
  linear_combination (pfCoeff f h r : ℝ) * tsum_pole_term K h (hpR h hh) r

end ZetasIrr.BP
