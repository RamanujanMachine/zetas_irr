/-
# Blueprint of `modal_basis` (manuscript §4.1, the general asymptotic dependency)

Node `Pfq54.modal_basis` of `Blueprint_pfq54.lean`: for invertible `3 × 3` matrices `Q(n)` with
rational-function entries whose balanced matrices `T_n Q(n) T_{n+1}^{-1}` tend to an invertible
`Q_∞` with distinct eigenvalues, there are independent row solutions `B_n = B₀ W_Q(n)` and nonzero
scalars `a_i(n)` with `diag(a(n))⁻¹ B_n T_n⁻¹ → Y` invertible, the rows of `Y` left eigenvectors of
`Q_∞` (eigenvalues `ρ_i`), and `|a_i(n)|^{1/n} → |ρ_i|`.

The manuscript does **not** prove this theorem: it isolates it as the general analytic dependency
(Birkhoff–Adams theory of linear difference systems with a regular-singular-free leading term).
The decomposition below is the standard route: the balanced matrices have a full asymptotic
expansion in `1/n` ([1]); `Q_∞` is diagonalizable ([2]); there are actual solutions asymptotic to
the formal solutions `ρ_i^n n^{α_i} (y_i + O(1/n))` ([3]); the root test then gives the rates ([4]).
-/
import Pfq54_defs
import modal_aux
import lev_aux6

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- **[1] Expansion at infinity.** Rational entries without poles and a finite limit give
`T_n Q(n) T_{n+1}^{-1} = Q_∞ + A₁/n + O(1/n²)` entrywise.
* Estimated proof length: ≈ 60 lines (Laurent expansion of a rational function at `∞`; the
  entries of the balanced matrix are rational in `n`).
* Directly from the manuscript: no (stated as a hypothesis check: "the rational matrix entries
  supply full asymptotic expansions at infinity"). -/
theorem balanced_expansion (Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ))
    (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
      Q n i j = (((Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) : ℚ) : ℂ))
    (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hlim : Tendsto (fun n => balance n * Q n * (balance (n + 1))⁻¹) atTop (𝓝 Qinf)) :
    ∃ (A₁ : Matrix (Fin 3) (Fin 3) ℂ) (C : ℝ), ∀ᶠ n : ℕ in atTop, ∀ i j,
      ‖(balance n * Q n * (balance (n + 1))⁻¹ - Qinf - ((n : ℂ)⁻¹) • A₁) i j‖ ≤ C / (n : ℝ) ^ 2 := by
  have hdi : ∀ (m : ℂ) (i : Fin 3), (![1, m, m ^ 2] : Fin 3 → ℂ) i = m ^ (i : ℕ) := by
    intro m i
    fin_cases i
    · exact (pow_zero m).symm
    · exact (pow_one m).symm
    · rfl
  set PP : Fin 3 → Fin 3 → Polynomial ℝ := fun i j =>
    Polynomial.X ^ (i : ℕ) * (Qr i j).num.map (algebraMap ℚ ℝ)
  set RR : Fin 3 → Fin 3 → Polynomial ℝ := fun i j =>
    (Polynomial.X + 1) ^ (j : ℕ) * (Qr i j).denom.map (algebraMap ℚ ℝ)
  have hRR : ∀ i j, RR i j ≠ 0 := fun i j => mul_ne_zero (pow_ne_zero _ (by
    rw [← map_one Polynomial.C]; exact Polynomial.X_add_C_ne_zero 1))
    ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (RatFunc.denom_ne_zero _))
  have hent : ∀ (n : ℕ) (i j : Fin 3), (balance n * Q n * (balance (n + 1))⁻¹) i j =
      (((PP i j).eval (n : ℝ) / (RR i j).eval (n : ℝ) : ℝ) : ℂ) := by
    intro n i j
    obtain ⟨hd, hq⟩ := hQ n i j
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hinv : (balance (n + 1))⁻¹ = Matrix.diagonal fun j : Fin 3 => (((n : ℂ) + 1) ^ (j : ℕ))⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [balance, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      rw [hdi, Nat.cast_succ, inv_mul_cancel₀ (pow_ne_zero _ hn1)]
    have hd' : (((Qr i j).denom.eval (n : ℚ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hd
    rw [hinv, Matrix.mul_diagonal, balance, Matrix.diagonal_mul, hdi, hq]
    simp only [PP, RR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_natCast_map, eq_ratCast]
    push_cast
    field_simp
  have hlimij : ∀ i j, Tendsto (fun n : ℕ => (balance n * Q n * (balance (n + 1))⁻¹) i j) atTop
      (𝓝 (Qinf i j)) := fun i j =>
    ((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp hlim)
  have hre : ∀ i j, Tendsto (fun n : ℕ => (PP i j).eval (n : ℝ) / (RR i j).eval (n : ℝ)) atTop
      (𝓝 (Qinf i j).re) := fun i j => by
    have h := (Complex.continuous_re.tendsto _).comp (hlimij i j)
    refine h.congr fun n => ?_
    rw [Function.comp_apply, hent, Complex.ofReal_re]
  have hQr : ∀ i j, Qinf i j = ((Qinf i j).re : ℂ) := fun i j => by
    have h := (Complex.continuous_im.tendsto _).comp (hlimij i j)
    have h0 : Tendsto (fun n : ℕ => (Complex.im ∘ fun n : ℕ =>
        (balance n * Q n * (balance (n + 1))⁻¹) i j) n) atTop (𝓝 0) :=
      tendsto_const_nhds.congr fun n => by rw [Function.comp_apply, hent, Complex.ofReal_im]
    exact Complex.ext rfl (by rw [Complex.ofReal_im]; exact tendsto_nhds_unique h h0)
  choose a K hK using fun i j => MB.rat_expansion (PP i j) (RR i j) (hRR i j) _ (hre i j)
  refine ⟨Matrix.of fun i j => (a i j : ℂ), ∑ i, ∑ j, |K i j|, ?_⟩
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => hK i j,
    eventually_ge_atTop 1] with n h hn i j
  have hle : K i j ≤ ∑ i, ∑ j, |K i j| := (le_abs_self _).trans
    ((Finset.single_le_sum (f := fun j => |K i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |K i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, hent, hQr i j,
    smul_eq_mul, show ((n : ℂ)⁻¹ * (a i j : ℂ)) = ((a i j / n : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact (h i j).trans (div_le_div_of_nonneg_right hle (by positivity))

/-- **[2] Left eigenbasis.** An invertible `Q_∞` with separable characteristic polynomial has a
basis of left eigenvectors (rows of an invertible `Y`) with distinct nonzero eigenvalues.
* Estimated proof length: ≈ 40 lines (`Matrix.charpoly` roots, `Polynomial.Separable.nodup_roots`,
  eigenvectors for distinct eigenvalues are independent).
* Directly from the manuscript: no (standard linear algebra, not in the manuscript). -/
theorem eigenbasis (Qinf : Matrix (Fin 3) (Fin 3) ℂ) (hinf : Qinf.det ≠ 0)
    (hsep : Qinf.charpoly.Separable) :
    ∃ (Y : Matrix (Fin 3) (Fin 3) ℂ) (ρ : Fin 3 → ℂ), Y.det ≠ 0 ∧ Function.Injective ρ ∧
      (∀ i, ρ i ≠ 0) ∧ ∀ i, Y i ᵥ* Qinf = ρ i • Y i := by
  have hcard : Qinf.charpoly.roots.card = 3 := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hR : Qinf.charpoly.roots.toFinset.card = 3 := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), hcard]
  set e := Qinf.charpoly.roots.toFinset.equivFin.trans (finCongr hR)
  set ρ : Fin 3 → ℂ := fun i => (e.symm i : ℂ)
  have hρ : Function.Injective ρ := fun i j h => e.symm.injective (Subtype.ext h)
  have hv : ∀ i, ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ v ᵥ* Qinf = ρ i • v := by
    intro i
    have hroot : (Matrix.scalar (Fin 3) (ρ i) - Qinf).det = 0 := by
      rw [← Matrix.eval_charpoly]
      have hm := (e.symm i).2
      rw [Multiset.mem_toFinset] at hm
      exact (Polynomial.mem_roots'.mp hm).2
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hroot
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.vecMul_sub, sub_eq_zero, Matrix.scalar_apply] at hv
    rw [← hv]
    funext k
    rw [Matrix.vecMul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm]
  choose Y hY0 hYe using hv
  have hρ0 : ∀ i, ρ i ≠ 0 := by
    intro i h
    apply hinf
    refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨Y i, hY0 i, ?_⟩
    rw [hYe i, h, zero_smul]
  have hli : LinearIndependent ℂ (Matrix.of Y).row :=
    Module.End.eigenvectors_linearIndependent' (Matrix.vecMulLinear Qinf) ρ hρ Y fun i =>
      ⟨Module.End.mem_eigenspace_iff.mpr (hYe i), hY0 i⟩
  refine ⟨Matrix.of Y, ρ, ?_, hρ, hρ0, hYe⟩
  exact ((Matrix.isUnit_iff_isUnit_det Y).mp (Matrix.linearIndependent_row_iff_isUnit.mp hli)).ne_zero

/-- **[3] Asymptotic solutions (Birkhoff–Adams).** Under the hypotheses of `modal_basis`, for
any left eigenbasis `Y` of `Q_∞` there are an invertible `B₀`, exponents `α_i` and corrections
`c_i(n) → 1` such that the row solutions `B₀ W_Q(n)` satisfy
`diag(ρ_i^n (n+1)^{α_i} c_i(n))⁻¹ B₀ W_Q(n) T_n⁻¹ → Y`.
* Uses: [1].
* Estimated proof length: ≈ 400 lines (formal solutions `ρ^n n^α ∑ y_k n^{-k}`, then a
  Levinson-type fixed-point argument for the actual solutions; distinct eigenvalues of equal
  modulus are allowed).
* Directly from the manuscript: no (the external modal-basis theorem). -/
theorem asymptotic_solutions (Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ))
    (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
      Q n i j = (((Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) : ℚ) : ℂ))
    (hdet : ∀ n, (Q n).det ≠ 0) (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hlim : Tendsto (fun n => balance n * Q n * (balance (n + 1))⁻¹) atTop (𝓝 Qinf))
    (hinf : Qinf.det ≠ 0) (hsep : Qinf.charpoly.Separable)
    (Y : Matrix (Fin 3) (Fin 3) ℂ) (ρ : Fin 3 → ℂ) (hY : Y.det ≠ 0) (hρ : Function.Injective ρ)
    (hρ0 : ∀ i, ρ i ≠ 0) (heig : ∀ i, Y i ᵥ* Qinf = ρ i • Y i) :
    ∃ (B₀ : Matrix (Fin 3) (Fin 3) ℂ) (α : Fin 3 → ℂ) (c : Fin 3 → ℕ → ℂ), B₀.det ≠ 0 ∧
      (∀ i n, c i n ≠ 0) ∧ (∀ i, Tendsto (c i) atTop (𝓝 1)) ∧
      Tendsto (fun n : ℕ => Matrix.diagonal (fun i => (ρ i ^ n * ((n : ℂ) + 1) ^ α i * c i n)⁻¹) *
        (B₀ * walk Q n) * (balance n)⁻¹) atTop (𝓝 Y) := by
  obtain ⟨A₁, C, hexp⟩ := balanced_expansion Qr Q hQ Qinf hlim
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hexp
  have hC : 0 ≤ C := by
    have h := hn₁ (max n₁ 1) (le_max_left _ _) 0 0
    have hpos : (0 : ℝ) < ((max n₁ 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((max n₁ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ 1
      positivity
    by_contra hneg
    rw [not_le] at hneg
    have := div_neg_of_neg_of_pos hneg hpos
    linarith [norm_nonneg ((balance (max n₁ 1) * Q (max n₁ 1) * (balance (max n₁ 1 + 1))⁻¹ -
      Qinf - ((max n₁ 1 : ℕ) : ℂ)⁻¹ • A₁) 0 0)]
  have hYQ : Y * Qinf = Matrix.diagonal ρ * Y := by
    ext i j
    have h := congrFun (heig i) j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    exact h
  let T : LV.Shear := ⟨fun n => balance n * Q n * (balance (n + 1))⁻¹, Qinf, A₁, C, hC, n₁,
    fun n hn i j => hn₁ n hn i j, Y, hY, ρ, hρ, hρ0, hYQ⟩
  have hbal : ∀ n, 1 ≤ n → IsUnit (balance n).det := fun n hn => by
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [isUnit_iff_ne_zero, balance, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hnC]
  have hwalk : ∀ n, (walk Q n).det ≠ 0 := fun n => by
    induction n with
    | zero => rw [Aux.walk_zero, Matrix.det_one]; exact one_ne_zero
    | succ n ih => rw [Aux.walk_succ, Matrix.det_mul]; exact mul_ne_zero ih (hdet n)
  let D : LV.WalkData T := ⟨fun n => walk Q n * (balance n)⁻¹, fun n hn => by
      show walk Q (n + 1) * (balance (n + 1))⁻¹ =
        walk Q n * (balance n)⁻¹ * (balance n * Q n * (balance (n + 1))⁻¹)
      rw [Aux.walk_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (balance n)⁻¹, Matrix.nonsing_inv_mul _ (hbal n hn), Matrix.one_mul],
    fun n hn => by
      show (walk Q n * (balance n)⁻¹).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (hwalk n) (inv_ne_zero (hbal n hn).ne_zero)⟩
  obtain ⟨B₀, α, c, hB₀, hc0, hc1, hT⟩ := D.modal
  refine ⟨B₀, α, c, hB₀, hc0, hc1, hT.congr fun n => ?_⟩
  show Matrix.diagonal _ * (B₀ * (walk Q n * (balance n)⁻¹)) = _
  simp only [Matrix.mul_assoc]
  rfl

/-- **[4] Root test for the scalars**: `|ρ^n (n+1)^α c(n)|^{1/n} → |ρ|` when `c(n) → 1`.
* Estimated proof length: ≈ 30 lines (`|(n+1)^α| = (n+1)^{Re α}`, `(n+1)^{x/n} → 1`).
* Directly from the manuscript: no (elementary; not in the manuscript). -/
theorem root_rate (ρ : ℂ) (hρ : ρ ≠ 0) (α : ℂ) (c : ℕ → ℂ) (hc0 : ∀ n, c n ≠ 0)
    (hc1 : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ‖ρ ^ n * ((n : ℂ) + 1) ^ α * c n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 ‖ρ‖) := by
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hlogc : Tendsto (fun n => Real.log ‖c n‖) atTop (𝓝 0) := by
    have h1 := (continuous_norm.tendsto (1 : ℂ)).comp hc1
    rw [norm_one] at h1
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h1
    rwa [Real.log_one] at h2
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hL : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, pow_one, one_mul, add_neg_cancel_right]
  have key : Tendsto (fun n : ℕ => Real.exp (Real.log ‖ρ‖ + α.re * (Real.log ((n : ℝ) + 1) / n) +
      Real.log ‖c n‖ * (n : ℝ)⁻¹)) atTop (𝓝 ‖ρ‖) := by
    have h := ((tendsto_const_nhds (x := Real.log ‖ρ‖)).add (hL.const_mul α.re)).add
      (hlogc.mul hinv)
    rw [mul_zero, mul_zero, add_zero, add_zero] at h
    have h2 := (Real.continuous_exp.tendsto _).comp h
    rwa [Real.exp_log hρn] at h2
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : 0 < ‖c n‖ := norm_pos_iff.mpr (hc0 n)
  have hcp : ‖((n : ℂ) + 1) ^ α‖ = ((n : ℝ) + 1) ^ α.re := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hn1 α
  have hp1 : 0 < ‖ρ‖ ^ n := pow_pos hρn n
  have hp2 : 0 < ((n : ℝ) + 1) ^ α.re := Real.rpow_pos_of_pos hn1 _
  rw [norm_mul, norm_mul, norm_pow, hcp, Real.rpow_def_of_pos (mul_pos (mul_pos hp1 hp2) hc),
    Real.log_mul (mul_pos hp1 hp2).ne' hc.ne', Real.log_mul hp1.ne' hp2.ne', Real.log_pow,
    Real.log_rpow hn1]
  congr 1
  field_simp

/-- **`modal_basis`** (node of `Blueprint_pfq54.lean`). Proved from [2], [3], [4]. -/
theorem modal_basis (Qr : Matrix (Fin 3) (Fin 3) (RatFunc ℚ))
    (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : ∀ (n : ℕ) i j, (Qr i j).denom.eval (n : ℚ) ≠ 0 ∧
      Q n i j = (((Qr i j).num.eval (n : ℚ) / (Qr i j).denom.eval (n : ℚ) : ℚ) : ℂ))
    (hdet : ∀ n, (Q n).det ≠ 0) (Qinf : Matrix (Fin 3) (Fin 3) ℂ)
    (hlim : Tendsto (fun n => balance n * Q n * (balance (n + 1))⁻¹) atTop (𝓝 Qinf))
    (hinf : Qinf.det ≠ 0) (hsep : Qinf.charpoly.Separable) :
    ∃ (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3 → ℕ → ℂ) (ρ : Fin 3 → ℂ),
      B₀.det ≠ 0 ∧ Y.det ≠ 0 ∧ Function.Injective ρ ∧ (∀ i n, a i n ≠ 0) ∧
      Tendsto (fun n => Matrix.diagonal (fun i => (a i n)⁻¹) * (B₀ * walk Q n) *
        (balance n)⁻¹) atTop (𝓝 Y) ∧
      (∀ i, Y i ᵥ* Qinf = ρ i • Y i) ∧
      ∀ i, Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 ‖ρ i‖) := by
  obtain ⟨Y, ρ, hY, hρ, hρ0, heig⟩ := eigenbasis Qinf hinf hsep
  obtain ⟨B₀, α, c, hB₀, hc0, hc1, hconv⟩ :=
    asymptotic_solutions Qr Q hQ hdet Qinf hlim hinf hsep Y ρ hY hρ hρ0 heig
  refine ⟨B₀, Y, fun i n => ρ i ^ n * ((n : ℂ) + 1) ^ α i * c i n, ρ, hB₀, hY, hρ,
    fun i n => ?_, hconv, heig, fun i => root_rate (ρ i) (hρ0 i) (α i) (c i) (hc0 i) (hc1 i)⟩
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hρ0 i)) fun h => hn ?_) (hc0 i n)
  exact ((Complex.cpow_eq_zero_iff _ _).mp h).1

end Pfq54.BP
