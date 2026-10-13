/-
# Blueprint of `dual_mode_transfer` (manuscript Lemma `dual-mode-transfer`)

Node `Pfq54.dual_mode_transfer` of `Blueprint_pfq54.lean` (elementary linear algebra).

Proof (manuscript §4.1). Put `Y_n = diag(a(n))⁻¹ B₀ W_Q(n) T_n⁻¹ → Y` and
`b_n = Y_n^{-T} T_n^{-T} v_n → b = Y^{-T} w` ([1]). The factorization of `B_n` gives the exact
identity `W_Q(n)^{-T} v_n = B₀ᵀ diag(a(n))⁻¹ b_n`; for large `n`, `b_{n,1} ≠ 0`, and dividing by
`b_{n,1}/a₁(n)` leaves `s₀ + ε_n` with `ε_n = ∑_{i=2,3} (a₁ b_{n,i})/(a_i b_{n,1}) (B₀)_i` ([2]),
where `‖ε_n‖ ≤ C θ'^n` for every `θ' > r/R` ([3]). The ratio of two rows on `s₀ + ε_n` differs from
`α = ℓ₁ s₀ᵀ/ℓ₂ s₀ᵀ` by `(ℓ₁ - α ℓ₂) ε_n / (ℓ₂ s₀ᵀ + ℓ₂ ε_n)` ([4]); the common scalar cancels.
-/
import Pfq54_aux

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- `Y_n = diag(a(n))⁻¹ B₀ W_Q(n) T_n⁻¹`. -/
def Yn (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (B₀ : Matrix (Fin 3) (Fin 3) ℂ)
    (a : Fin 3 → ℕ → ℂ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => (a i n)⁻¹) * (B₀ * walk Q n) * (balance n)⁻¹

/-- `b_n = Y_n^{-T} T_n^{-T} v_n`. -/
def bvec (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (B₀ : Matrix (Fin 3) (Fin 3) ℂ)
    (a : Fin 3 → ℕ → ℂ) (v : ℕ → Fin 3 → ℂ) (n : ℕ) : Fin 3 → ℂ :=
  ((Yn Q B₀ a n)⁻¹)ᵀ *ᵥ (((balance n)⁻¹)ᵀ *ᵥ v n)

/-- `ε_n = ∑_{i=2,3} (a₁(n) b_{n,i})/(a_i(n) b_{n,1}) (B₀)_i` (indices `0, 1, 2` in Lean). -/
def evec (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (B₀ : Matrix (Fin 3) (Fin 3) ℂ)
    (a : Fin 3 → ℕ → ℂ) (v : ℕ → Fin 3 → ℂ) (n : ℕ) : Fin 3 → ℂ :=
  (a 0 n * bvec Q B₀ a v n 1 / (a 1 n * bvec Q B₀ a v n 0)) • B₀ 1 +
    (a 0 n * bvec Q B₀ a v n 2 / (a 2 n * bvec Q B₀ a v n 0)) • B₀ 2

/-- **[1] Convergence of `b_n`**: `b_n → Y^{-T} w` (`Y_n → Y` invertible, inversion is
continuous at invertible matrices, `T_n^{-T} v_n → w`).
* Estimated proof length: ≈ 20 lines (`Matrix.continuousAt_inv`-type argument via
  `Matrix.inv_def` and continuity of `det`, `adjugate`).
* Directly from the manuscript: yes. -/
theorem bvec_tendsto (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ)
    (hY : Y.det ≠ 0) (a : Fin 3 → ℕ → ℂ) (hconv : Tendsto (Yn Q B₀ a) atTop (𝓝 Y))
    (v : ℕ → Fin 3 → ℂ) (w : Fin 3 → ℂ)
    (hv : Tendsto (fun n => ((balance n)⁻¹)ᵀ *ᵥ v n) atTop (𝓝 w)) :
    Tendsto (bvec Q B₀ a v) atTop (𝓝 ((Y⁻¹)ᵀ *ᵥ w)) := by
  have hri : ContinuousAt (Ring.inverse : ℂ → ℂ) Y.det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hY
  have hci : ContinuousAt (Inv.inv : Matrix (Fin 3) (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) ℂ) Y :=
    continuousAt_matrix_inv Y hri
  have hinv : Tendsto (fun n => (Yn Q B₀ a n)⁻¹) atTop (𝓝 Y⁻¹) := hci.tendsto.comp hconv
  exact Aux.tendsto_mulVec3 (Aux.tendsto_transpose3 hinv) hv

/-- **[2] The exact factorization**: eventually `b_{n,1} ≠ 0` and
`W_Q(n)^{-T} v_n = (b_{n,1}/a₁(n)) (s₀ + ε_n)`, `s₀ = (B₀)₁`.
* Uses: [1] (`b_{n,1} → (Y^{-T} w)₁ ≠ 0`).
* Estimated proof length: ≈ 40 lines (`W_Q(n) = B₀⁻¹ diag(a(n)) Y_n T_n` for `n ≥ 1`, transpose
  inverse, `Matrix.mulVec` expansion over `Fin 3`).
* Directly from the manuscript: yes ("The factorization of `B_n` gives the exact identity"). -/
theorem factorization (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (hQ : ∀ n, (Q n).det ≠ 0)
    (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (hB₀ : B₀.det ≠ 0) (hY : Y.det ≠ 0)
    (a : Fin 3 → ℕ → ℂ) (ha : ∀ i n, a i n ≠ 0) (hconv : Tendsto (Yn Q B₀ a) atTop (𝓝 Y))
    (v : ℕ → Fin 3 → ℂ) (w : Fin 3 → ℂ)
    (hv : Tendsto (fun n => ((balance n)⁻¹)ᵀ *ᵥ v n) atTop (𝓝 w))
    (hw : ((Y⁻¹)ᵀ *ᵥ w) 0 ≠ 0) :
    ∀ᶠ n in atTop, bvec Q B₀ a v n 0 ≠ 0 ∧
      ((walk Q n)⁻¹)ᵀ *ᵥ v n = (bvec Q B₀ a v n 0 / a 0 n) • (B₀ 0 + evec Q B₀ a v n) := by
  have hb := bvec_tendsto Q B₀ Y hY a hconv v w hv
  have hb0 : ∀ᶠ n in atTop, bvec Q B₀ a v n 0 ≠ 0 :=
    (((continuous_apply 0).tendsto _).comp hb).eventually_ne hw
  have hdetY : ∀ᶠ n in atTop, (Yn Q B₀ a n).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto Y).comp hconv).eventually_ne hY
  filter_upwards [hb0, hdetY, eventually_ge_atTop 1] with n hb0n hdn hn
  refine ⟨hb0n, ?_⟩
  set Dg := Matrix.diagonal (fun i => a i n) with hDg
  set Di := Matrix.diagonal (fun i => (a i n)⁻¹) with hDi
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hTu : IsUnit (balance n).det := by
    rw [isUnit_iff_ne_zero, balance, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hnC]
  have hBu : IsUnit B₀.det := isUnit_iff_ne_zero.mpr hB₀
  have hDD : Dg * Di = 1 := by
    rw [hDg, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (ha i n)
  have hWeq : walk Q n = B₀⁻¹ * (Dg * (Yn Q B₀ a n * balance n)) := by
    unfold Yn
    rw [← hDi, Matrix.mul_assoc (Di * (B₀ * walk Q n)), Matrix.nonsing_inv_mul _ hTu,
      Matrix.mul_one, ← Matrix.mul_assoc Dg, hDD, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hBu, Matrix.one_mul]
  have key : ((walk Q n)⁻¹)ᵀ = B₀ᵀ * (Di * (((Yn Q B₀ a n)⁻¹)ᵀ * ((balance n)⁻¹)ᵀ)) := by
    rw [hWeq, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hBu, Matrix.inv_eq_right_inv hDD, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, hDi, Matrix.diagonal_transpose]
  rw [key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change B₀ᵀ *ᵥ (Di *ᵥ bvec Q B₀ a v n) = _
  funext j
  have h0 := ha 0 n
  have h1 := ha 1 n
  have h2 := ha 2 n
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply, hDi,
    Matrix.diagonal_apply, evec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_zero, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

/-- **[3] Decay of the error vector**: for every `θ' > r/R` there is `C` with `‖ε_n‖ ≤ C θ'^n`
eventually (`|a₁(n)/a_i(n)|^{1/n} → r/R` for `i = 2, 3`, `b_n` bounded, `b_{n,1}` bounded away
from `0`).
* Uses: [1].
* Estimated proof length: ≈ 40 lines.
* Directly from the manuscript: yes ("`limsup ‖ε_n‖^{1/n} ≤ r/R`"). -/
theorem evec_decay (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ)
    (hY : Y.det ≠ 0) (a : Fin 3 → ℕ → ℂ) (ha : ∀ i n, a i n ≠ 0)
    (hconv : Tendsto (Yn Q B₀ a) atTop (𝓝 Y)) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (ha₁ : Tendsto (fun n : ℕ => ‖a 0 n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 r))
    (ha₂₃ : ∀ i ≠ 0, Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 R))
    (v : ℕ → Fin 3 → ℂ) (w : Fin 3 → ℂ)
    (hv : Tendsto (fun n => ((balance n)⁻¹)ᵀ *ᵥ v n) atTop (𝓝 w))
    (hw : ((Y⁻¹)ᵀ *ᵥ w) 0 ≠ 0) :
    ∀ θ' > r / R, ∃ C : ℝ, ∀ᶠ n in atTop, ‖evec Q B₀ a v n‖ ≤ C * θ' ^ n := by
  intro θ' hθ'
  have hR : 0 < R := hr.trans hrR
  have hb := bvec_tendsto Q B₀ Y hY a hconv v w hv
  set binf := (Y⁻¹)ᵀ *ᵥ w with hbinf
  have hrat : ∀ i ≠ (0 : Fin 3), ∀ᶠ n in atTop, ‖a 0 n / a i n‖ ≤ θ' ^ n := by
    intro i hi
    have ht : Tendsto (fun n : ℕ => ‖a 0 n‖ ^ ((n : ℝ)⁻¹) / ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop
        (𝓝 (r / R)) := ha₁.div (ha₂₃ i hi) hR.ne'
    filter_upwards [ht.eventually (gt_mem_nhds hθ'), eventually_ge_atTop 1] with n hn hn1
    rw [← Real.div_rpow (norm_nonneg _) (norm_nonneg _), ← norm_div] at hn
    have hx := norm_nonneg (a 0 n / a i n)
    calc ‖a 0 n / a i n‖ = (‖a 0 n / a i n‖ ^ ((n : ℝ)⁻¹)) ^ n :=
          (Real.rpow_inv_natCast_pow hx (by omega)).symm
      _ ≤ θ' ^ n := pow_le_pow_left₀ (Real.rpow_nonneg hx _) hn.le n
  have hpos : 0 < ‖binf 0‖ := norm_pos_iff.mpr hw
  have hn0 : Tendsto (fun n => ‖bvec Q B₀ a v n 0‖) atTop (𝓝 ‖binf 0‖) :=
    (((continuous_apply 0).tendsto _).comp hb).norm
  have hb0 : ∀ᶠ n in atTop, ‖binf 0‖ / 2 < ‖bvec Q B₀ a v n 0‖ :=
    hn0.eventually_const_lt (by linarith)
  have hbB : ∀ᶠ n in atTop, ‖bvec Q B₀ a v n‖ < ‖binf‖ + 1 :=
    hb.norm.eventually_lt_const (by linarith)
  set K := (‖binf‖ + 1) / (‖binf 0‖ / 2) with hK
  refine ⟨K * (‖B₀ 1‖ + ‖B₀ 2‖), ?_⟩
  filter_upwards [hrat 1 (by decide), hrat 2 (by decide), hb0, hbB] with n h1 h2 h0 hB
  have hc : ∀ i, ‖a 0 n / a i n‖ ≤ θ' ^ n →
      ‖a 0 n * bvec Q B₀ a v n i / (a i n * bvec Q B₀ a v n 0)‖ ≤ θ' ^ n * K := by
    intro i hi
    have hbi : ‖bvec Q B₀ a v n i‖ ≤ ‖binf‖ + 1 := (norm_le_pi_norm _ i).trans hB.le
    have hq : ‖a 0 n * bvec Q B₀ a v n i / (a i n * bvec Q B₀ a v n 0)‖ =
        ‖a 0 n / a i n‖ * (‖bvec Q B₀ a v n i‖ / ‖bvec Q B₀ a v n 0‖) := by
      rw [norm_div, norm_mul, norm_mul, norm_div]; ring
    rw [hq]
    exact mul_le_mul hi (div_le_div₀ (by positivity) hbi (half_pos hpos) h0.le)
      (div_nonneg (norm_nonneg _) (norm_nonneg _))
      (pow_nonneg (le_of_lt (lt_trans (div_pos hr hR) hθ')) n)
  unfold evec
  calc ‖(a 0 n * bvec Q B₀ a v n 1 / (a 1 n * bvec Q B₀ a v n 0)) • B₀ 1 +
        (a 0 n * bvec Q B₀ a v n 2 / (a 2 n * bvec Q B₀ a v n 0)) • B₀ 2‖
      ≤ ‖a 0 n * bvec Q B₀ a v n 1 / (a 1 n * bvec Q B₀ a v n 0)‖ * ‖B₀ 1‖ +
        ‖a 0 n * bvec Q B₀ a v n 2 / (a 2 n * bvec Q B₀ a v n 0)‖ * ‖B₀ 2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ θ' ^ n * K * ‖B₀ 1‖ + θ' ^ n * K * ‖B₀ 2‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (hc 1 h1) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hc 2 h2) (norm_nonneg _))
    _ = K * (‖B₀ 1‖ + ‖B₀ 2‖) * θ' ^ n := by ring

/-- **[4] Perturbation of a ratio**: if `ℓ₂ s₀ᵀ ≠ 0` and `‖e_n‖ ≤ C θ'^n` with `0 ≤ θ' < θ` and
`θ' < 1`,
then eventually `ℓ₂ (s₀ + e_n)ᵀ ≠ 0` and the ratio differs from `ℓ₁ s₀ᵀ/ℓ₂ s₀ᵀ` by at most `θ^n`.
* Estimated proof length: ≈ 40 lines (the error is `(ℓ₁ - α ℓ₂) e_n / (ℓ₂ s₀ᵀ + ℓ₂ e_n)`;
  `C' θ'^n ≤ θ^n` eventually).
* Directly from the manuscript: yes. -/
theorem ratio_perturbation (s₀ ℓ₁ ℓ₂ : Fin 3 → ℂ) (hℓ₂ : ℓ₂ ⬝ᵥ s₀ ≠ 0)
    (e : ℕ → Fin 3 → ℂ) (C θ' θ : ℝ) (hθ'0 : 0 ≤ θ') (hθ : θ' < θ) (hθ'1 : θ' < 1)
    (he : ∀ᶠ n in atTop, ‖e n‖ ≤ C * θ' ^ n) :
    ∀ᶠ n in atTop, ℓ₂ ⬝ᵥ (s₀ + e n) ≠ 0 ∧
      ‖(ℓ₁ ⬝ᵥ (s₀ + e n)) / (ℓ₂ ⬝ᵥ (s₀ + e n)) - (ℓ₁ ⬝ᵥ s₀) / (ℓ₂ ⬝ᵥ s₀)‖ ≤ θ ^ n := by
  set d := ℓ₂ ⬝ᵥ s₀ with hd
  have hθ0 : 0 < θ := lt_of_le_of_lt hθ'0 hθ
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hℓ₂
  have hdot : ∀ ℓ x : Fin 3 → ℂ, ‖ℓ ⬝ᵥ x‖ ≤ 3 * (‖ℓ‖ * ‖x‖) := by
    intro ℓ x
    unfold dotProduct
    calc ‖∑ i, ℓ i * x i‖ ≤ ∑ i, ‖ℓ i * x i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ‖ℓ‖ * ‖x‖ := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm ℓ i) (norm_le_pi_norm x i) (norm_nonneg _)
            (norm_nonneg _)
      _ = 3 * (‖ℓ‖ * ‖x‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have hpow : Tendsto (fun n : ℕ => θ' ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hθ'0 hθ'1
  have he0 : Tendsto (fun n => ‖e n‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) he ?_
    simpa using hpow.const_mul C
  set K1 := 3 * (‖d‖ * ‖ℓ₁‖ + ‖ℓ₁ ⬝ᵥ s₀‖ * ‖ℓ₂‖) with hK1
  set M := 2 * K1 / ‖d‖ ^ 2 * |C| with hM
  have hq : Tendsto (fun n : ℕ => M * (θ' / θ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hθ'0 hθ0.le)
      ((div_lt_one hθ0).mpr hθ)).const_mul M
  have hsmall : ∀ᶠ n in atTop, ‖ℓ₂‖ * ‖e n‖ * 3 ≤ ‖d‖ / 2 := by
    have := (he0.const_mul (‖ℓ₂‖)).mul_const 3
    simp only [mul_zero, zero_mul] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  filter_upwards [he, hsmall, hq.eventually (ge_mem_nhds one_pos)] with n hen hsn hqn
  have hden : ‖d‖ / 2 ≤ ‖ℓ₂ ⬝ᵥ (s₀ + e n)‖ := by
    rw [dotProduct_add]
    have h1 := hdot ℓ₂ (e n)
    have h2 := norm_sub_norm_le d (-(ℓ₂ ⬝ᵥ e n))
    rw [sub_neg_eq_add, norm_neg] at h2
    linarith
  have hden0 : ℓ₂ ⬝ᵥ (s₀ + e n) ≠ 0 := by
    intro h; rw [h, norm_zero] at hden; linarith
  refine ⟨hden0, ?_⟩
  have hid : (ℓ₁ ⬝ᵥ (s₀ + e n)) / (ℓ₂ ⬝ᵥ (s₀ + e n)) - (ℓ₁ ⬝ᵥ s₀) / d =
      (d * (ℓ₁ ⬝ᵥ e n) - (ℓ₁ ⬝ᵥ s₀) * (ℓ₂ ⬝ᵥ e n)) / (d * (ℓ₂ ⬝ᵥ (s₀ + e n))) := by
    rw [div_sub_div _ _ hden0 hℓ₂, dotProduct_add, dotProduct_add]
    rw [dotProduct_add] at hden0
    field_simp
    ring
  rw [hid, norm_div, norm_mul]
  have hnum : ‖d * (ℓ₁ ⬝ᵥ e n) - (ℓ₁ ⬝ᵥ s₀) * (ℓ₂ ⬝ᵥ e n)‖ ≤ K1 * ‖e n‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := hdot ℓ₁ (e n)
    have h2 := hdot ℓ₂ (e n)
    calc ‖d‖ * ‖ℓ₁ ⬝ᵥ e n‖ + ‖ℓ₁ ⬝ᵥ s₀‖ * ‖ℓ₂ ⬝ᵥ e n‖
        ≤ ‖d‖ * (3 * (‖ℓ₁‖ * ‖e n‖)) + ‖ℓ₁ ⬝ᵥ s₀‖ * (3 * (‖ℓ₂‖ * ‖e n‖)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = K1 * ‖e n‖ := by rw [hK1]; ring
  have hK1 : 0 ≤ K1 := by positivity
  have hdd : 0 < ‖d‖ * (‖d‖ / 2) := by positivity
  calc ‖d * (ℓ₁ ⬝ᵥ e n) - (ℓ₁ ⬝ᵥ s₀) * (ℓ₂ ⬝ᵥ e n)‖ / (‖d‖ * ‖ℓ₂ ⬝ᵥ (s₀ + e n)‖)
      ≤ K1 * ‖e n‖ / (‖d‖ * (‖d‖ / 2)) :=
        div_le_div₀ (by positivity) hnum hdd (mul_le_mul_of_nonneg_left hden (norm_nonneg _))
    _ ≤ K1 * (|C| * θ' ^ n) / (‖d‖ * (‖d‖ / 2)) := by
        gcongr
        exact hen.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hθ'0 n))
    _ = M * (θ' / θ) ^ n * θ ^ n := by
        rw [hM, div_pow]
        field_simp
    _ ≤ 1 * θ ^ n := mul_le_mul_of_nonneg_right hqn (pow_nonneg hθ0.le n)
    _ = θ ^ n := one_mul _

/-- **`dual_mode_transfer`** (node of `Blueprint_pfq54.lean`). Proved from [2], [3], [4]. -/
theorem dual_mode_transfer (Q : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (hQ : ∀ n, (Q n).det ≠ 0)
    (B₀ Y : Matrix (Fin 3) (Fin 3) ℂ) (hB₀ : B₀.det ≠ 0) (hY : Y.det ≠ 0)
    (a : Fin 3 → ℕ → ℂ) (ha : ∀ i n, a i n ≠ 0)
    (hconv : Tendsto (fun n => Matrix.diagonal (fun i => (a i n)⁻¹) * (B₀ * walk Q n) *
      (balance n)⁻¹) atTop (𝓝 Y))
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (ha₁ : Tendsto (fun n : ℕ => ‖a 0 n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 r))
    (ha₂₃ : ∀ i ≠ 0, Tendsto (fun n : ℕ => ‖a i n‖ ^ ((n : ℝ)⁻¹)) atTop (𝓝 R))
    (v : ℕ → Fin 3 → ℂ) (w : Fin 3 → ℂ)
    (hv : Tendsto (fun n => ((balance n)⁻¹)ᵀ *ᵥ v n) atTop (𝓝 w))
    (hw : ((Y⁻¹)ᵀ *ᵥ w) 0 ≠ 0) (ℓ₁ ℓ₂ : Fin 3 → ℂ) (hℓ₂ : ℓ₂ ⬝ᵥ B₀ 0 ≠ 0) :
    (∀ᶠ n in atTop, ℓ₂ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n) ≠ 0) ∧
      ∀ θ > r / R, ∀ᶠ n in atTop,
        ‖(ℓ₁ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n)) / (ℓ₂ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n)) -
          (ℓ₁ ⬝ᵥ B₀ 0) / (ℓ₂ ⬝ᵥ B₀ 0)‖ ≤ θ ^ n := by
  have hfac := factorization Q hQ B₀ Y hB₀ hY a ha hconv v w hv hw
  have hrR' : 0 < r / R := div_pos hr (hr.trans hrR)
  have main : ∀ θ > r / R, ∀ᶠ n in atTop, ℓ₂ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n) ≠ 0 ∧
      ‖(ℓ₁ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n)) / (ℓ₂ ⬝ᵥ (((walk Q n)⁻¹)ᵀ *ᵥ v n)) -
        (ℓ₁ ⬝ᵥ B₀ 0) / (ℓ₂ ⬝ᵥ B₀ 0)‖ ≤ θ ^ n := by
    intro θ hθ
    have hrR1 : r / R < 1 := (div_lt_one (hr.trans hrR)).mpr hrR
    have hm1 : r / R < min θ 1 := lt_min hθ hrR1
    obtain ⟨C, hC⟩ := evec_decay Q B₀ Y hY a ha hconv r R hr hrR ha₁ ha₂₃ v w hv hw
      ((r / R + min θ 1) / 2) (by linarith)
    have hpert := ratio_perturbation (B₀ 0) ℓ₁ ℓ₂ hℓ₂ (evec Q B₀ a v) C ((r / R + min θ 1) / 2) θ
      (by linarith) (by linarith [min_le_left θ 1]) (by linarith [min_le_right θ 1]) hC
    filter_upwards [hfac, hpert] with n ⟨hb0, hW⟩ ⟨hne, hbound⟩
    have hc : bvec Q B₀ a v n 0 / a 0 n ≠ 0 := div_ne_zero hb0 (ha 0 n)
    rw [hW, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    refine ⟨mul_ne_zero hc hne, ?_⟩
    rwa [mul_div_mul_left _ _ hc]
  exact ⟨(main (r / R + 1) (by linarith)).mono fun n h => h.1,
    fun θ hθ => (main θ hθ).mono fun n h => h.2⟩

end Pfq54.BP
