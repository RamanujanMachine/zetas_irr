/-
# Blueprint for `ZetasIrr.Mfun_sub_Mfun_pred`

Statement in `blueprint.lean`:
  `𝓜_K[f] - 𝓜_{K-1}[f] = -f''(K) · 1` for `f` with integer poles and no pole at `K`.

## ⚠ The statement in `blueprint.lean` is missing a hypothesis

The PDF (Part III, eq. (4); Part VII §7) always works under the standing assumption that
*all poles of `f` are integers at most the cutoff*. The `blueprint.lean` version only assumes
integer poles and no pole at `K`. With the definitions of `defs.lean` it is then **false**.
For a pole `h > K` the harmonic index `⌊K - h⌋` is negative, `harm` clamps it to `0`, and that pole
contributes the same value to `𝓜_K[f]` and to `𝓜_{K-1}[f]`. Its contribution `-f''(K) ≠ 0`
to the right-hand side has no counterpart on the left.

Counterexample: `f = 1/(t - (K+1))`. Then `𝓜_K[f] = 𝓜_{K-1}[f] = 2Z₃`, but `-f''(K) = 2`.
This is recorded below as `blueprint_statement_counterexample` (not used in the proof).

`blueprint.lean` is left unchanged as requested. The main theorem below is the corrected
statement, with the extra hypothesis `hbelow : ∀ h ∈ roots, h < K`, which is the PDF's standing
assumption. Every use of the shift identity in the PDF (Lemma 1, cutoffs `0 → 2N`) satisfies it.

Source: PDF Part III ("`𝓜_K[f] - 𝓜_{K-1}[f] = -f''(K)` … follow directly by differentiating the
argument of the already proved `𝓛_K` identities") and Part VII §7 (the `𝓛_K` shift identities:
"For proper parts these follow by telescoping harmonic sums; for polynomials they are the
identity `B_m(x+1) - B_m(x) = m x^{m-1}`").

| # | Supporting lemma                         | Est. lines | Directly from PDF? |
|---|------------------------------------------|-----------:|--------------------|
| 1 | `Lfun_sub_Lfun_pred`                     |   (proved) | Yes                |
| 2 | `bernoulli_shift`                        |   (proved) | Yes                |
| 3 | `harm_sub_harm_pred`                     |   (proved) | Yes                |
| 4 | `rfEval_rfDeriv_eq_parts`                |   (proved) | Partially          |
| 5 | `rfDeriv_poles`                          |   (proved) | Yes                |
| 6 | `blueprint_statement_counterexample`     |   (proved) | (remark)           |
| 7 | `rfDeriv_split`                          |   (proved) | Yes                |

[2]–[4] are the ingredients of [1]. The main theorem uses [1], [5], [7]. All supporting lemmas
are proved; the file contains no `sorry`.

**Second correction (splitting).** [1], [4] and the main theorem also need the denominator
to split over `ℚ`, i.e. *all* poles must be rational, as in the PDF. Otherwise they fail: for
`g = 1/(t² + 1)`, `𝓛_K[g] = 0` for every `K`, while `g'(K) ≠ 0` for `K ≠ 0`. So they now
assume `hsplit : denom.roots.card = denom.natDegree`. The new lemma [7] shows that splitting
passes from `f` to `f'`.
-/
import ZetasAux
import derivSum_eq_realize_Lfun

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries

noncomputable section

namespace ZetasIrr

/-- **[2] Bernoulli shift.** `B_m(x+1) - B_m(x) = m x^{m-1}`. This gives the polynomial part
of the `𝓛`-shift identity.
* Lines: proved here (Mathlib `Polynomial.bernoulli_eval_one_add`).
* Directly from the PDF: yes. -/
theorem bernoulli_shift (m : ℕ) (x : ℚ) :
    (Polynomial.bernoulli m).eval (x + 1) - (Polynomial.bernoulli m).eval x =
      m * x ^ (m - 1) := by
  rw [add_comm x 1, Polynomial.bernoulli_eval_one_add]; ring

/-- **[3] Harmonic shift.** `H^{(s)}_n - H^{(s)}_{n-1} = n^{-s}` for `n ≥ 1`. This gives the
telescoping of the principal parts.
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem harm_sub_harm_pred (s : ℕ) (n : ℤ) (hn : 1 ≤ n) :
    harm s n - harm s (n - 1) = 1 / (n : ℚ) ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨(n - 1).toNat, by omega⟩
  have h1 : ((m : ℤ) + 1).toNat = m + 1 := by omega
  have h2 : ((m : ℤ) + 1 - 1).toNat = m := by omega
  unfold harm
  rw [h1, h2, Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

/-- `rfEval` and `rfReal` agree at rational points. -/
theorem rfEval_cast (f : ℚ⟮X⟯) (x : ℚ) : ((rfEval f x : ℚ) : ℝ) = rfReal f (x : ℝ) := by
  unfold rfEval rfReal RatFunc.eval
  push_cast
  rw [show (x : ℝ) = algebraMap ℚ ℝ x from rfl, Polynomial.eval₂_at_apply,
    Polynomial.eval₂_at_apply]
  simp

/-- The real derivative of `g` at a non-pole is the real value of `rfDeriv g`. -/
theorem deriv_rfReal_eq_rfDeriv (g : ℚ⟮X⟯) (x : ℚ) (hx : g.denom.eval x ≠ 0) :
    deriv (rfReal g) (x : ℝ) = ((rfEval (rfDeriv g) x : ℚ) : ℝ) := by
  have hD : (g.denom.map (algebraMap ℚ ℝ)).eval (x : ℝ) ≠ 0 := by
    rw [Polynomial.eval_map, show (x : ℝ) = algebraMap ℚ ℝ x from rfl, Polynomial.eval₂_at_apply]
    simpa using hx
  have hfun : rfReal g = fun y => (g.num.map (algebraMap ℚ ℝ)).eval y /
      (g.denom.map (algebraMap ℚ ℝ)).eval y := by
    funext y
    unfold rfReal RatFunc.eval
    rw [Polynomial.eval_map, Polynomial.eval_map]
  have hd : deriv (fun y => (g.num.map (algebraMap ℚ ℝ)).eval y /
      (g.denom.map (algebraMap ℚ ℝ)).eval y) (x : ℝ) =
      ((derivative (g.num.map (algebraMap ℚ ℝ))).eval (x : ℝ) *
          (g.denom.map (algebraMap ℚ ℝ)).eval (x : ℝ) -
        (g.num.map (algebraMap ℚ ℝ)).eval (x : ℝ) *
          (derivative (g.denom.map (algebraMap ℚ ℝ))).eval (x : ℝ)) /
        (g.denom.map (algebraMap ℚ ℝ)).eval (x : ℝ) ^ 2 :=
    ((Polynomial.hasDerivAt (g.num.map (algebraMap ℚ ℝ)) (x : ℝ)).div
      (Polynomial.hasDerivAt (g.denom.map (algebraMap ℚ ℝ)) (x : ℝ)) hD).deriv
  rw [hfun, hd]
  unfold rfDeriv
  rw [Aux.rfEval_div _ _ _ (by rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hx)]
  push_cast
  rw [show (x : ℝ) = algebraMap ℚ ℝ x from rfl]
  simp only [Polynomial.eval_map, Polynomial.derivative_map]
  simp only [Polynomial.eval₂_at_apply]
  simp only [eq_ratCast, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow]
  push_cast
  ring

/-- **[4] `f'(K)` from the decomposition.** If the denominator of `g` splits and all poles of
`g` are integers `< K`, then
`g'(K) = (polyPart g)'(K) - ∑_h ∑_r r c_{h,r} (K - h)^{-r-1}`.
* Lines: proved here. The real derivative of `g` at `K` is computed twice: as the real value
  of `rfDeriv g` (`deriv_rfReal_eq_rfDeriv`), and through `g = polyPart g + f₀` with `f₀` proper,
  using `BP.deriv_rfReal_eq` of `derivSum_eq_realize_Lfun.lean` (imported).
* Directly from the PDF: partially. The PDF uses the decomposition implicitly. -/
theorem rfEval_rfDeriv_eq_parts (K : ℤ) (g : ℚ⟮X⟯)
    (hsplit : g.denom.roots.card = g.denom.natDegree)
    (hpoles : ∀ h ∈ g.denom.roots, ∃ n : ℤ, n < K ∧ h = n) :
    rfEval (rfDeriv g) K =
      (derivative (polyPart g)).eval (K : ℚ) -
        ∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
          (r : ℚ) * pfCoeff g h r / ((K : ℚ) - h) ^ (r + 1) := by
  set P := polyPart g with hP
  set f₀ := g - algebraMap ℚ[X] ℚ⟮X⟯ P with hf₀
  have hg : g = algebraMap ℚ[X] ℚ⟮X⟯ P + f₀ := by rw [hf₀]; ring
  have hdeg : DegLE (-1) f₀ := Aux.DegLE_sub_polyPart g
  rcases hdeg with h0 | hdeg'
  · -- `g` is a polynomial
    rw [h0, add_zero] at hg
    have hden : g.denom = 1 := by rw [hg, RatFunc.denom_algebraMap]
    have hroots : g.denom.roots.toFinset = ∅ := by rw [hden, Polynomial.roots_one]; rfl
    rw [hroots, Finset.sum_empty, sub_zero, hg, ← div_one (algebraMap ℚ[X] ℚ⟮X⟯ P),
      ← map_one (algebraMap ℚ[X] ℚ⟮X⟯), Aux.rfDeriv_div _ _ one_ne_zero,
      Aux.rfEval_div _ _ _ (by simp)]
    simp
  have hf₀ne : f₀ ≠ 0 := by
    intro h; rw [h, RatFunc.intDegree_zero] at hdeg'; omega
  have hf₀proper : f₀.num.natDegree < f₀.denom.natDegree := by
    unfold RatFunc.intDegree at hdeg'; omega
  -- the denominator of `f₀` divides that of `g`
  have hdvd : f₀.denom ∣ g.denom := by
    have := RatFunc.denom_add_dvd g (-algebraMap ℚ[X] ℚ⟮X⟯ P)
    rw [← sub_eq_add_neg, ← map_neg, RatFunc.denom_algebraMap, mul_one] at this
    exact this
  have hgD : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hroots : ∀ h ∈ f₀.denom.roots, h ∈ g.denom.roots := fun h hh =>
    Multiset.mem_of_le (Polynomial.roots.le_of_dvd hgD hdvd) hh
  have hf₀split : f₀.denom.roots.card = f₀.denom.natDegree :=
    Polynomial.splits_iff_card_roots.mp
      ((Polynomial.splits_iff_card_roots.mpr hsplit).of_dvd hgD hdvd)
  have hf₀deg : f₀.denom.natDegree ≤ g.denom.natDegree := Polynomial.natDegree_le_of_dvd hdvd hgD
  have hf₀poles : ∀ h ∈ f₀.denom.roots, ∃ n : ℤ, n ≤ K - 1 ∧ h = n := fun h hh => by
    obtain ⟨n, hn, rfl⟩ := hpoles h (hroots h hh); exact ⟨n, by omega, rfl⟩
  -- `K` is not a pole of `g` nor of `f₀`
  have hKg : g.denom.eval (K : ℚ) ≠ 0 := by
    intro h0
    obtain ⟨n, hn, hKn⟩ := hpoles _ ((Polynomial.mem_roots hgD).mpr h0)
    have : K = n := by exact_mod_cast hKn
    omega
  have hKf₀ : f₀.denom.eval (K : ℚ) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hdvd
    apply hKg; rw [hk, Polynomial.eval_mul, h0, zero_mul]
  -- the Laurent coefficients of `g` and `f₀` agree for `r ≥ 1`
  have hpf : ∀ h r, 1 ≤ r → pfCoeff g h r = pfCoeff f₀ h r := by
    intro h r hr
    rw [hg, pfCoeff_add, Aux.pfCoeff_algebraMap P h r hr, zero_add]
  have hKcast : ((K : ℤ) : ℝ) = algebraMap ℚ ℝ (K : ℚ) := by simp
  -- the real derivative of `g` at `K`, computed in two ways
  have hreal : deriv (rfReal g) (K : ℝ) = ((rfEval (rfDeriv g) K : ℚ) : ℝ) := by
    have := deriv_rfReal_eq_rfDeriv g K hKg
    simpa using this
  have hsum : deriv (rfReal g) (K : ℝ) = (derivative P).eval (K : ℚ) -
      ∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
        ((r : ℚ) * pfCoeff g h r / ((K : ℚ) - h) ^ (r + 1) : ℚ) := by
    -- split `rfReal g = rfReal P + rfReal f₀` near `K`
    have hP' : ∀ y : ℝ, rfReal (algebraMap ℚ[X] ℚ⟮X⟯ P) y = (P.map (algebraMap ℚ ℝ)).eval y := by
      intro y; unfold rfReal; rw [RatFunc.eval_algebraMap, Polynomial.eval_map]; simp
    have hsplitfun : rfReal g =ᶠ[𝓝 (K : ℝ)] fun y =>
        (P.map (algebraMap ℚ ℝ)).eval y + rfReal f₀ y := by
      filter_upwards [Ioi_mem_nhds (show ((K - 1 : ℤ) : ℝ) < K by push_cast; linarith)] with y hy
      rw [hg]
      unfold rfReal
      rw [RatFunc.eval_add _ _ (RegAt.poly y P) ?_]
      · rw [← hP']; rfl
      · intro h0
        have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
          (RatFunc.monic_denom f₀) hf₀split
        rw [← hprod, Polynomial.eval₂_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map,
          Multiset.mem_map] at h0
        obtain ⟨h, hh, hval⟩ := h0
        simp only [Function.comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
          eq_ratCast] at hval
        obtain ⟨n, hn, rfl⟩ := hf₀poles h hh
        have h1 : ((n : ℚ) : ℝ) ≤ ((K - 1 : ℤ) : ℝ) := by push_cast; exact_mod_cast hn
        have h2 : y = ((n : ℚ) : ℝ) := by linarith
        rw [h2] at hy
        exact absurd hy (not_lt.mpr h1)
    rw [hsplitfun.deriv_eq]
    -- differentiability of `rfReal f₀` at `K`
    have hdiff : DifferentiableAt ℝ (rfReal f₀) (K : ℝ) := by
      have hD : (f₀.denom.map (algebraMap ℚ ℝ)).eval (K : ℝ) ≠ 0 := by
        rw [Polynomial.eval_map, hKcast, Polynomial.eval₂_at_apply]
        simpa using hKf₀
      have hfun : rfReal f₀ = fun y => (f₀.num.map (algebraMap ℚ ℝ)).eval y /
          (f₀.denom.map (algebraMap ℚ ℝ)).eval y := by
        funext y; unfold rfReal RatFunc.eval; rw [Polynomial.eval_map, Polynomial.eval_map]
      rw [hfun]
      exact (Polynomial.differentiable _).differentiableAt.div
        (Polynomial.differentiable _).differentiableAt hD
    rw [show (fun y => (P.map (algebraMap ℚ ℝ)).eval y + rfReal f₀ y) =
        (fun y => (P.map (algebraMap ℚ ℝ)).eval y) + rfReal f₀ from rfl,
      deriv_add (Polynomial.differentiable _).differentiableAt hdiff, Polynomial.deriv,
      BP.deriv_rfReal_eq (K - 1) f₀ hf₀proper hf₀split hf₀poles (K : ℝ) (by push_cast; linarith)]
    -- extend the index sets from `f₀` to `g`
    have hext : ∑ h ∈ f₀.denom.roots.toFinset, ∑ r ∈ Finset.range (f₀.denom.natDegree + 1),
        -((r : ℝ) * (pfCoeff f₀ h r : ℝ) * (((K : ℝ) - h) ^ (r + 1))⁻¹) =
        ∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
        -((r : ℝ) * (pfCoeff g h r : ℝ) * (((K : ℝ) - h) ^ (r + 1))⁻¹) := by
      refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro h hh
        exact Multiset.mem_toFinset.mpr (hroots h (Multiset.mem_toFinset.mp hh))
      · intro h hh
        obtain ⟨-, hh2⟩ := Finset.mem_sdiff.mp hh
        have hev : f₀.denom.eval h ≠ 0 := fun h0 => hh2 (Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (RatFunc.denom_ne_zero f₀)).mpr h0))
        refine Finset.sum_eq_zero fun r _ => ?_
        rcases Nat.eq_zero_or_pos r with rfl | hpos
        · simp
        · rw [hpf h r hpos, Aux.pfCoeff_eq_zero_of_eval_ne_zero f₀ h hev r hpos]; simp
      · intro h _
        refine Finset.sum_subset (s₂ := Finset.range (g.denom.natDegree + 1))
          (Finset.range_subset_range.mpr (by omega)) ?_ |>.trans ?_
        · intro r _ hr
          have hr1 : f₀.denom.natDegree < r := by
            simp only [Finset.mem_range, not_lt] at hr; omega
          rw [Aux.pfCoeff_eq_zero_of_natDegree_lt f₀ h r hr1]; simp
        · refine Finset.sum_congr rfl fun r _ => ?_
          rcases Nat.eq_zero_or_pos r with rfl | hpos
          · simp
          · rw [hpf h r hpos]
    have hPK : (derivative (P.map (algebraMap ℚ ℝ))).eval (K : ℝ) =
        (((derivative P).eval (K : ℚ) : ℚ) : ℝ) := by
      rw [Polynomial.derivative_map, Polynomial.eval_map, hKcast, Polynomial.eval₂_at_apply,
        eq_ratCast]
    rw [hext, hPK]
    push_cast
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hcast := hreal.symm.trans hsum
  exact_mod_cast hcast

/-- `𝓛_K[g] = A_K(g) · 1 + (a part independent of `K`)`. -/
private theorem Lfun_decomp (K : ℤ) (g : ℚ⟮X⟯) :
    Lfun K g =
      (∑ m ∈ Finset.range ((polyPart g).natDegree + 1),
          (polyPart g).coeff m * (Polynomial.bernoulli m).eval ((K : ℚ) + 1) -
        ∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
          (r : ℚ) * pfCoeff g h r * harm (r + 1) ⌊(K : ℚ) - h⌋) • Zsym 0 +
      ∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
        ((r : ℚ) * pfCoeff g h r) • Zsym (r + 1) := by
  unfold Lfun
  simp only [sub_smul, Finset.sum_smul, smul_sub, smul_smul, Finset.sum_sub_distrib]
  abel

/-- **[1] Shift identity for `𝓛`** (PDF Part VII §7): `𝓛_K[g] - 𝓛_{K-1}[g] = g'(K)` when the
denominator of `g` splits and all poles of `g` are integers `< K`.

Proof: the polynomial parts differ by `∑ p_m m K^{m-1} = (polyPart g)'(K)` by [2]. For each
pole `h < K`, the harmonic terms differ by `-(K-h)^{-(r+1)}` by [3]. Compare with [4].
* Lines: proved here (from [2]–[4]).
* Directly from the PDF: yes. -/
theorem Lfun_sub_Lfun_pred (K : ℤ) (g : ℚ⟮X⟯)
    (hsplit : g.denom.roots.card = g.denom.natDegree)
    (hpoles : ∀ h ∈ g.denom.roots, ∃ n : ℤ, n < K ∧ h = n) :
    Lfun K g - Lfun (K - 1) g = rfEval (rfDeriv g) K • Zsym 0 := by
  rw [Lfun_decomp, Lfun_decomp, rfEval_rfDeriv_eq_parts K g hsplit hpoles,
    add_sub_add_right_eq_sub, ← sub_smul]
  congr 1
  -- polynomial part
  have hK : ((K - 1 : ℤ) : ℚ) + 1 = (K : ℚ) := by push_cast; ring
  have hpoly : ∑ m ∈ Finset.range ((polyPart g).natDegree + 1),
      (polyPart g).coeff m * (Polynomial.bernoulli m).eval ((K : ℚ) + 1) -
      ∑ m ∈ Finset.range ((polyPart g).natDegree + 1),
      (polyPart g).coeff m * (Polynomial.bernoulli m).eval (((K - 1 : ℤ) : ℚ) + 1) =
      (derivative (polyPart g)).eval (K : ℚ) := by
    rw [hK, ← Finset.sum_sub_distrib, Polynomial.derivative_eval,
      Polynomial.sum_over_range _ (fun n => by simp)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_sub, bernoulli_shift]; ring
  -- principal parts
  have hprin : ∀ h ∈ g.denom.roots.toFinset, ∀ r : ℕ,
      (r : ℚ) * pfCoeff g h r * harm (r + 1) ⌊((K - 1 : ℤ) : ℚ) - h⌋ -
        (r : ℚ) * pfCoeff g h r * harm (r + 1) ⌊(K : ℚ) - h⌋ =
      -((r : ℚ) * pfCoeff g h r / ((K : ℚ) - h) ^ (r + 1)) := by
    intro h hh r
    obtain ⟨n, hn, rfl⟩ := hpoles h (Multiset.mem_toFinset.mp hh)
    have e1 : ⌊(K : ℚ) - (n : ℚ)⌋ = K - n := by
      rw [show (K : ℚ) - (n : ℚ) = ((K - n : ℤ) : ℚ) by push_cast; ring, Int.floor_intCast]
    have e2 : ⌊((K - 1 : ℤ) : ℚ) - (n : ℚ)⌋ = K - n - 1 := by
      rw [show ((K - 1 : ℤ) : ℚ) - (n : ℚ) = ((K - n - 1 : ℤ) : ℚ) by push_cast; ring,
        Int.floor_intCast]
    have hs := harm_sub_harm_pred (r + 1) (K - n) (by omega)
    rw [e1, e2]
    have : (K : ℚ) - (n : ℚ) = ((K - n : ℤ) : ℚ) := by push_cast; ring
    rw [this]
    rw [show K - n - 1 = (K - n) - 1 by ring]
    rw [div_eq_mul_one_div]
    linear_combination (-((r : ℚ) * pfCoeff g (n : ℚ) r)) * hs
  have hsum : (∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
        (r : ℚ) * pfCoeff g h r * harm (r + 1) ⌊((K - 1 : ℤ) : ℚ) - h⌋) -
      ∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
        (r : ℚ) * pfCoeff g h r * harm (r + 1) ⌊(K : ℚ) - h⌋ =
      -∑ h ∈ g.denom.roots.toFinset, ∑ r ∈ Finset.range (g.denom.natDegree + 1),
        (r : ℚ) * pfCoeff g h r / ((K : ℚ) - h) ^ (r + 1) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => hprin h hh r
  linear_combination hpoly + hsum

/-- **[5] Poles of the derivative.** Every pole of `g'` is a pole of `g`, because
`denom(g') ∣ denom(g)²`.
* Lines: proved here.
* Directly from the PDF: yes (standard). -/
theorem rfDeriv_poles (g : ℚ⟮X⟯) : ∀ h ∈ (rfDeriv g).denom.roots, h ∈ g.denom.roots := by
  intro h hh
  have hdvd : (rfDeriv g).denom ∣ g.denom ^ 2 := RatFunc.denom_div_dvd _ _
  have hne : g.denom ^ 2 ≠ 0 := pow_ne_zero _ (RatFunc.denom_ne_zero g)
  have := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hne hdvd) hh
  rw [Polynomial.roots_pow] at this
  exact Multiset.mem_of_mem_nsmul this

/-- **[7] Splitting passes to the derivative.** `denom(g') ∣ denom(g)²`, and a divisor of a split
polynomial splits.
* Lines: proved here.
* Directly from the PDF: yes (standard). -/
theorem rfDeriv_split (g : ℚ⟮X⟯) (hsplit : g.denom.roots.card = g.denom.natDegree) :
    (rfDeriv g).denom.roots.card = (rfDeriv g).denom.natDegree := by
  have hdvd : (rfDeriv g).denom ∣ g.denom ^ 2 := RatFunc.denom_div_dvd _ _
  have hne : g.denom ^ 2 ≠ 0 := pow_ne_zero _ (RatFunc.denom_ne_zero g)
  have hs : Polynomial.Splits (g.denom ^ 2) :=
    (Polynomial.splits_iff_card_roots.mpr hsplit).pow 2
  exact Polynomial.splits_iff_card_roots.mp (hs.of_dvd hne hdvd)

/-- **[6] Remark: the `blueprint.lean` statement is false as written.** Counterexample
`K = 0`, `f = 1/(t - 1)`: the pole `1` lies above the cutoff and the identity fails. Not used in
the proof of the main theorem.
* Lines: proved here.
* Directly from the PDF: n/a (it concerns the Lean statement, not the PDF). -/
theorem blueprint_statement_counterexample :
    ¬ ∀ (K : ℤ) (f : ℚ⟮X⟯), (∀ h ∈ f.denom.roots, ∃ n : ℤ, h = n) →
      f.denom.eval (K : ℚ) ≠ 0 →
      Mfun K f - Mfun (K - 1) f = (-rfEval (rfDeriv (rfDeriv f)) K) • Zsym 0 := by
  intro H
  have hq : (Polynomial.X - Polynomial.C (1 : ℚ)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hq2 : (Polynomial.X - Polynomial.C (1 : ℚ)) ^ 2 ≠ 0 := pow_ne_zero _ hq
  set f : ℚ⟮X⟯ := algebraMap ℚ[X] ℚ⟮X⟯ 1 /
    algebraMap ℚ[X] ℚ⟮X⟯ (Polynomial.X - Polynomial.C 1) with hf
  -- the only pole of `f` is `1`
  have hroots : ∀ h ∈ f.denom.roots, h = 1 := by
    intro h hh
    have := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hq (RatFunc.denom_div_dvd _ _)) hh
    rw [Polynomial.roots_X_sub_C] at this
    exact Multiset.mem_singleton.mp this
  have hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, h = n := fun h hh => ⟨1, by simp [hroots h hh]⟩
  have hK : f.denom.eval ((0 : ℤ) : ℚ) ≠ 0 := by
    intro h0
    have hmem : (0 : ℚ) ∈ f.denom.roots :=
      (Polynomial.mem_roots (RatFunc.denom_ne_zero f)).mpr (by simpa using h0)
    have := hroots 0 hmem
    norm_num at this
  have e := H 0 f hpoles hK
  -- `f' = -1/(t-1)²`
  set g := rfDeriv f with hg_def
  have hg : g = algebraMap ℚ[X] ℚ⟮X⟯ (-1) /
      algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C 1) ^ 2) := by
    rw [hg_def, hf, Aux.rfDeriv_div _ _ hq]
    simp
  have hgroots : ∀ h ∈ g.denom.roots, h = 1 := by
    intro h hh
    rw [hg] at hh
    have := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hq2 (RatFunc.denom_div_dvd _ _)) hh
    rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C] at this
    exact Multiset.mem_singleton.mp (Multiset.mem_of_mem_nsmul this)
  have hgproper : g.num.natDegree < g.denom.natDegree := by
    have hdeg : g.intDegree = -2 := by
      rw [hg, RatFunc.intDegree_div (Aux.algebraMap_ne_zero' (by norm_num))
        (Aux.algebraMap_ne_zero' hq2), RatFunc.intDegree_polynomial,
        RatFunc.intDegree_polynomial, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      simp
    unfold RatFunc.intDegree at hdeg
    omega
  -- `𝓛_0[g] = 𝓛_{-1}[g]`: the only pole `1` lies above both cutoffs
  have hLeq : Lfun 0 g = Lfun (0 - 1) g := by
    unfold Lfun
    rw [ZetasIrr.polyPart_eq_zero_of_proper g hgproper]
    simp only [Polynomial.natDegree_zero, zero_add, Finset.range_one, Finset.sum_singleton,
      Polynomial.coeff_zero, zero_mul, zero_smul]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun r _ => ?_
    rw [hgroots h (Multiset.mem_toFinset.mp hh)]
    have hfl : ⌊(-1 : ℚ)⌋ = -1 := by norm_num [Int.floor_eq_iff]
    have hfl2 : ⌊(-2 : ℚ)⌋ = -2 := by norm_num [Int.floor_eq_iff]
    norm_num [harm, hfl, hfl2]
  have hLHS : Mfun 0 f - Mfun (0 - 1) f = 0 := by
    simp only [Mfun]
    rw [← hg_def, hLeq, sub_self]
  -- `f'' = 2(t-1)/(t-1)⁴`, so `-f''(0) = 2`
  have hgg : rfDeriv g = algebraMap ℚ[X] ℚ⟮X⟯ (2 * (Polynomial.X - Polynomial.C 1)) /
      algebraMap ℚ[X] ℚ⟮X⟯ (((Polynomial.X - Polynomial.C 1) ^ 2) ^ 2) := by
    rw [hg, Aux.rfDeriv_div _ _ hq2]
    congr 2
    simp [Polynomial.derivative_pow, map_ofNat]
  have hev : rfEval (rfDeriv g) ((0 : ℤ) : ℚ) = -2 := by
    rw [hgg, Aux.rfEval_div _ _ _ (by simp)]
    norm_num
  rw [hLHS, hev] at e
  have := congrArg (fun z : FormalZ => z 0) e
  simp [Zsym] at this

/-- **Main theorem (corrected form of `blueprint.lean`'s `Mfun_sub_Mfun_pred`).** It has the
original hypotheses plus `hbelow` (all poles lie below `K`) and `hsplit` (the denominator splits
over `ℚ`). Proved from [1], [5], [7]. -/
theorem Mfun_sub_Mfun_pred (K : ℤ) (f : ℚ⟮X⟯)
    (hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, h = n) (_hK : f.denom.eval (K : ℚ) ≠ 0)
    (hbelow : ∀ h ∈ f.denom.roots, h < K)
    (hsplit : f.denom.roots.card = f.denom.natDegree) :
    Mfun K f - Mfun (K - 1) f = (-rfEval (rfDeriv (rfDeriv f)) K) • Zsym 0 := by
  have hpoles' : ∀ h ∈ (rfDeriv f).denom.roots, ∃ n : ℤ, n < K ∧ h = n := by
    intro h hh
    have hf := rfDeriv_poles f h hh
    obtain ⟨n, rfl⟩ := hpoles h hf
    exact ⟨n, by exact_mod_cast hbelow _ hf, rfl⟩
  simp only [Mfun]
  rw [show -Lfun K (rfDeriv f) - -Lfun (K - 1) (rfDeriv f) =
      -(Lfun K (rfDeriv f) - Lfun (K - 1) (rfDeriv f)) by abel,
    Lfun_sub_Lfun_pred K (rfDeriv f) (rfDeriv_split f hsplit) hpoles', neg_smul]

end ZetasIrr
