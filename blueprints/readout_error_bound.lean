/-
# Blueprint for `ZetasIrr.readout_error_bound`

Statement (as in `blueprint.lean`), equation (3):
  `|ζ(3) q_{Nj} - p^{(3)}_{Nj}| + |ζ(4) q_{Nj} - p^{(4)}_{Nj}| ≤ e^{(-59.51995592483 + ε)N}`
for every `ε > 0` and all large `N`.

Source: PDF Part II ("The bounds `‖A_N‖, ‖B_N‖ ≤ e^{bN+o(N)}`, `‖S_N‖ ≤ e^{-aN+o(N)}`, and
`det V_N = e^{(2b-a)N+o(N)}` prove (3)").

Strategy. By the cross-product readouts, each error is `|(X × S_N)_j| / det V_N` with
`X ∈ {A_N, B_N}`. This is at most `2e^{(b+ε')N}e^{(-a+ε')N} / e^{(2b-a-ε')N} = 2e^{(-b+3ε')N}`.
Take `ε' = ε/4`, absorb the factor `4` for large `N`, and use `b > 59.51995592483`.

| # | Supporting lemma          | Est. lines | Directly from PDF? |
|---|---------------------------|-----------:|--------------------|
| 1 | `cross_product_readout`   | see `cross_product_readout.lean` | Yes |
| 2 | `growth_estimates`        | imported from `growth_estimates.lean` | Partially |
| 3 | `abs_cross_le`            | (proved, imported from `growth_estimates.lean`) | Yes |

The deduction itself is the proof below. There are no new open lemmas beyond the two nodes
[1], [2]. [2] and [3] are `ZetasIrr.BP.growth_estimates` and `ZetasIrr.BP.abs_cross_le` of
`growth_estimates.lean`, which is imported. (This file used to carry its own copy of
`abs_cross_le`, with the same statement; it was dropped because the two declarations have the
same name.)
-/
import ZetasAux
import growth_estimates

open Filter Topology Real

noncomputable section

namespace ZetasIrr.BP

/-- **[1] Cross-product readouts** (the node `cross_product_readout` of `blueprint.lean`).
Proved in `blueprints/cross_product_readout.lean` (imported via `ZetasAux`).
* Lines: proved (see that file).
* Directly from the PDF: yes. -/
theorem cross_product_readout (N : ℕ) :
    (fun j => ζ3 * q N j - p3 N j) =
        -((V N).det : ℝ)⁻¹ • crossProduct (fun j => (coeffMat N 0 j : ℝ)) (S N) ∧
    (fun j => ζ4 * q N j - p4 N j) =
        ((V N).det : ℝ)⁻¹ • crossProduct (fun j => (coeffMat N 1 j : ℝ)) (S N) :=
  ZetasIrr.cross_product_readout N

/- **[2] Spectral estimates** (the node `growth_estimates` of `blueprint.lean`) and **[3] size of
a cross product** (`abs_cross_le`) are `ZetasIrr.BP.growth_estimates` and
`ZetasIrr.BP.abs_cross_le`, imported from `blueprints/growth_estimates.lean`. -/

/-- **Main theorem (`blueprint.lean`, `readout_error_bound`).** Proved from [1]–[3]. -/
theorem readout_error_bound :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ j,
      |ζ3 * q N j - p3 N j| + |ζ4 * q N j - p4 N j| ≤ exp ((-59.51995592483 + ε) * N) := by
  obtain ⟨a, b, -, -, hb, -, hgrowth⟩ := growth_estimates
  intro ε hε
  set ε' := ε / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h4N : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ exp (ε' * N) := by
    have : Tendsto (fun N : ℕ => exp (ε' * N)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hε'pos)
    exact this.eventually_ge_atTop 4
  filter_upwards [hgrowth ε' hε'pos, h4N] with N ⟨hj, hdet⟩ h4 j
  obtain ⟨h1, h2⟩ := cross_product_readout N
  have e1 := congrFun h1 j
  have e2 := congrFun h2 j
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
  rw [e1, e2]
  have hd : (0 : ℝ) < (V N).det := lt_of_lt_of_le (exp_pos _) hdet
  have hX1 := abs_cross_le (fun j => (coeffMat N 0 j : ℝ)) (S N) _ _ (fun i => (hj i).1)
    (fun i => (hj i).2.2.1) j
  have hX2 := abs_cross_le (fun j => (coeffMat N 1 j : ℝ)) (S N) _ _ (fun i => (hj i).2.1)
    (fun i => (hj i).2.2.1) j
  rw [abs_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hd, ← mul_add, inv_mul_le_iff₀ hd]
  calc _ ≤ 2 * (exp ((b + ε') * N) * exp ((-a + ε') * N)) +
        2 * (exp ((b + ε') * N) * exp ((-a + ε') * N)) := add_le_add hX1 hX2
    _ = 4 * (exp ((b + ε') * N) * exp ((-a + ε') * N)) := by ring
    _ ≤ exp (ε' * N) * (exp ((b + ε') * N) * exp ((-a + ε') * N)) := by gcongr
    _ = exp ((2 * b - a - ε') * N) * exp ((-b + ε) * N) := by
        rw [← exp_add, ← exp_add, ← exp_add]; congr 1; rw [hε']; ring
    _ ≤ (V N).det * exp ((-59.51995592483 + ε) * N) :=
        mul_le_mul hdet (exp_le_exp.mpr (by gcongr)) (exp_pos _).le hd.le

end ZetasIrr.BP
