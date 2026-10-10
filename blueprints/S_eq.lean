/-
# Blueprint for `ZetasIrr.S_eq`

Statement (as in `blueprint.lean`): `S_{Nj} = A_{Nj} ζ(4) + B_{Nj} ζ(3) + C_{Nj}`, where
`S_{Nj} = -∑_{t ≥ 2N+1} d/dt((-t)^j R_N(t))` and `(A,B,C)` are the rows of `coeffMat N`.

Source: PDF Part VII §2 ("For j = 0,1,2, expand by partial fractions the convergent sum …") and
Part VII §7 (definition of `𝓛_K`; "for a proper rational function this is the formal value of
`-∑_{t>K} f'(t)`").

Strategy. The kernel `(-t)^j R_N(t)` is proper, of degree `≤ -2`, with integer poles
`-k`, `0 ≤ k ≤ 12N`, of order at most `3`. So `derivSum_eq_realize_Lfun` applies. Its formal value
involves only `Z₄`, `Z₃` and `1`: there is no `Z₂`, because the residues sum to zero, and no `Z₅`
or higher, because the pole orders are `≤ 3`.

| # | Supporting lemma                 | Est. lines | Directly from PDF? |
|---|----------------------------------|-----------:|--------------------|
| 1 | `derivSum_eq_realize_Lfun`       |   (proved) | Yes                |
| 2 | `linFormKernel_proper`           |   (proved) | Yes                |
| 3 | `linFormKernel_poles`            |   (proved) | Yes                |
| 3'| `linFormKernel_split`            |   (proved) | Yes                |
| 4 | `Lfun_linFormKernel_support`     |   (proved) | Partially          |
| 5 | `realize_eq_of_support`          |   (proved) | Yes                |

There are no open lemmas. The proved lemmas [1]–[4] are taken from
`cross_product_readout.lean` (imported via `ZetasAux`); [4] is used directly as
`ZetasIrr.Lfun_linFormKernel_support`. The declarations of this file live in
the namespace `ZetasIrr.BP` to avoid clashes with the imported ones.

**Correction.** As stated before, [1] was false: it constrained only the *rational* roots of
the denominator. For `1/(t² + 1)`, `𝓛_K` is `0` but `-∑ f'(t)` is not. [1] now also assumes
that the denominator splits over `ℚ`. This is the PDF's standing assumption that *all* poles
are integers. The new lemma [3'] checks it for the kernel.
-/
import ZetasAux

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries

noncomputable section

namespace ZetasIrr.BP

/-- **[1] Formal = analytic** (corrected form of the node `derivSum_eq_realize_Lfun` of
`blueprint.lean`: the denominator must split over `ℚ`).
* Lines: proved (`derivSum_eq_realize_Lfun'` in `cross_product_readout.lean`).
* Directly from the PDF: yes (Part VII §7). -/
theorem derivSum_eq_realize_Lfun (K : ℤ) (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree)
    (hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, n ≤ K ∧ h = n) :
    derivSum K f = realize (Lfun K f) :=
  ZetasIrr.derivSum_eq_realize_Lfun' K f hproper hsplit hpoles

/-- **[2] The kernel is proper.** `deg((-t)^j R_N) = j - 4 ≤ -2`: the numerator of `R_N` has degree
`30N` and the denominator `30N + 4`. Because the fraction may cancel, the statement is about
the reduced `num`/`denom` of the `RatFunc`. Use `RatFunc.intDegree` and
`RatFunc.intDegree_mul`/`intDegree_div`.
* Lines: proved (`cross_product_readout.lean`).
* Directly from the PDF: yes (degree count). -/
theorem linFormKernel_proper (N : ℕ) (j : Fin 3) :
    (linFormKernel N j).num.natDegree < (linFormKernel N j).denom.natDegree :=
  ZetasIrr.linFormKernel_proper N j

/-- **[3] The poles are integers `≤ 2N`.** Every root of the reduced denominator divides
`(t)_{10N+2}(t+N)_{10N+1}(t+2N)_{10N+1}`, whose roots are `-k`, `0 ≤ k ≤ 12N`.
* Lines: proved (`cross_product_readout.lean`).
* Directly from the PDF: yes. -/
theorem linFormKernel_poles (N : ℕ) (j : Fin 3) :
    ∀ h ∈ (linFormKernel N j).denom.roots, ∃ n : ℤ, n ≤ 2 * N ∧ h = n :=
  ZetasIrr.linFormKernel_poles N j

/-- **[3'] The denominator splits over `ℚ`.** The reduced denominator divides
`(t)_{10N+2}(t+N)_{10N+1}(t+2N)_{10N+1}`, which is a product of linear factors.
* Lines: proved (`cross_product_readout.lean`).
* Directly from the PDF: yes. -/
theorem linFormKernel_split (N : ℕ) (j : Fin 3) :
    (linFormKernel N j).denom.roots.card = (linFormKernel N j).denom.natDegree :=
  ZetasIrr.linFormKernel_split N j

/- **[4] Only `Z₄`, `Z₃` and `1` occur** (`Lfun (2 * N) (linFormKernel N j) r = 0` for
`r ∉ {0, 3, 4}`) is `ZetasIrr.Lfun_linFormKernel_support`, proved in
`blueprints/cross_product_readout.lean`.
* Directly from the PDF: partially. The PDF states the outcome (`A ζ(4) + B ζ(3) + C`) without
  proving the vanishing of the `ζ(2)` coefficient. -/

/-- **[5] Realisation of a combination of `1, Z₃, Z₄`.**
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem realize_eq_of_support (z : FormalZ)
    (hz : ∀ r, r ≠ 0 → r ≠ 3 → r ≠ 4 → z r = 0) :
    realize z = z 4 * ζ4 + z 3 * ζ3 + z 0 := by
  have hsupp : z.support ⊆ {0, 3, 4} := by
    intro r hr
    rw [Finsupp.mem_support_iff] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    exact hr (hz r h.1 h.2.1 h.2.2)
  unfold realize
  rw [Finsupp.sum_of_support_subset z hsupp _ (by intros; simp)]
  simp [ζ3, ζ4]
  ring

/-- **Main theorem (`blueprint.lean`, `S_eq`).** Proved from [1]–[5]. -/
theorem S_eq (N : ℕ) (j : Fin 3) :
    S N j = coeffMat N 0 j * ζ4 + coeffMat N 1 j * ζ3 + coeffMat N 2 j := by
  rw [S, derivSum_eq_realize_Lfun _ _ (linFormKernel_proper N j) (linFormKernel_split N j)
      (linFormKernel_poles N j),
    realize_eq_of_support _ (Lfun_linFormKernel_support N j)]
  simp [coeffMat]

end ZetasIrr.BP
