/-
# Assembly: the modal basis of the balanced system (sorry-free)

For `W(n+1) = W(n) Bal(n)` with `Bal(n) = Q_∞ + A₁/n + O(1/n²)` and a left eigenbasis `Y` of
`Q_∞` (the data `Shear`), the three Levinson solutions of the sheared system are transported back
(`y = x S(n) Y`) and assembled into `B₀` with
`diag(ρ_i^n (n+1)^{α_i} c_i(n))⁻¹ B₀ W(n) → Y`, `c_i(n) → 1`.
-/
import lev_aux5

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.LV

theorem row_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) : (A * B) i = A i ᵥ* B := by
  funext j
  rfl

theorem diagonal_row (d : Fin 3 → ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    (Matrix.diagonal d * M) i = d i • M i := by
  funext j
  rw [Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]

theorem tendsto_vecMul {v : ℕ → Fin 3 → ℂ} {w : Fin 3 → ℂ} {A : ℕ → Matrix (Fin 3) (Fin 3) ℂ}
    {L : Matrix (Fin 3) (Fin 3) ℂ} (hv : Tendsto v atTop (𝓝 w)) (hA : Tendsto A atTop (𝓝 L)) :
    Tendsto (fun n => v n ᵥ* A n) atTop (𝓝 (w ᵥ* L)) := by
  refine tendsto_pi_nhds.mpr fun j => ?_
  simp only [Matrix.vecMul, dotProduct]
  exact tendsto_finsetSum _ fun k _ =>
    (tendsto_pi_nhds.mp hv k).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA k) j)

theorem single_vecMul (i : Fin 3) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    (Pi.single i (1 : ℂ) : Fin 3 → ℂ) ᵥ* A = A i := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- The hypotheses on the walk `W`. -/
structure WalkData (T : Shear) where
  W : ℕ → Matrix (Fin 3) (Fin 3) ℂ
  hW : ∀ n, 1 ≤ n → W (n + 1) = W n * T.Bal n
  hWdet : ∀ n, 1 ≤ n → (W n).det ≠ 0

namespace WalkData

variable {T : Shear} (D : WalkData T)

/-- One Levinson solution of the sheared system, from `Nst` on, with the tail condition. -/
theorem solution (i : Fin 3) :
    ∃ N₀ : ℕ, ∀ Nst, N₀ ≤ Nst → ∃ x z : ℕ → Fin 3 → ℂ,
      (∀ n, Nst ≤ n → x (n + 1) = x n ᵥ* T.Nm n) ∧
      (∀ n, x n = (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) • (Pi.single i 1 + z n)) ∧
      Tendsto z atTop (𝓝 0) := by
  obtain ⟨K₂, n₀, hK₂, _, _, hbound⟩ := T.exists_bound
  obtain ⟨rec, N₀, K, r, Dl⟩ := exists_levData T.ρ T.α T.hρ0 i T.Nm K₂ hK₂ n₀ hbound
  have hK : 0 < 1 / (4 * K) := by
    have := Dl.hK
    positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((Dl.tail_tendsto.eventually (gt_mem_nhds hK)).and (eventually_ge_atTop N₀))
  refine ⟨N₁, fun Nst hNst => ?_⟩
  obtain ⟨h1, h2⟩ := hN₁ N₁ le_rfl
  exact Dl.exists_solution Nst (h2.trans hNst) ((Dl.tail_mono N₁ Nst hNst).trans h1.le)

/-- The common starting index. -/
theorem common_start : ∃ Nst : ℕ, 1 ≤ Nst ∧ (∀ n, Nst ≤ n → (T.S n).det ≠ 0) ∧
    (∀ i, N₁ (T.α i) ≤ Nst) ∧
    ∀ i, ∃ x z : ℕ → Fin 3 → ℂ,
      (∀ n, Nst ≤ n → x (n + 1) = x n ᵥ* T.Nm n) ∧
      (∀ n, x n = (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) • (Pi.single i 1 + z n)) ∧
      Tendsto z atTop (𝓝 0) := by
  choose N₀ hN₀ using fun i => solution (T := T) i
  obtain ⟨K₂, n₀, _, hn₀, hdet, _⟩ := T.exists_bound
  refine ⟨N₀ 0 + N₀ 1 + N₀ 2 + n₀ + N₁ (T.α 0) + N₁ (T.α 1) + N₁ (T.α 2), by omega,
    fun n hn => hdet n (by omega), fun i => ?_, fun i => hN₀ i _ ?_⟩
  · fin_cases i
    · show N₁ (T.α 0) ≤ _; omega
    · show N₁ (T.α 1) ≤ _; omega
    · show N₁ (T.α 2) ≤ _; omega
  · fin_cases i
    · show N₀ 0 ≤ _; omega
    · show N₀ 1 ≤ _; omega
    · show N₀ 2 ≤ _; omega

theorem prod_lamA (i : Fin 3) (Nst n : ℕ) :
    ∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m = T.ρ i ^ (n - Nst) * prodA (T.α i) Nst n := by
  unfold lamA prodA
  rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]

theorem prod_lamA_ne_zero (i : Fin 3) (Nst n : ℕ) (hN : N₁ (T.α i) ≤ Nst) :
    ∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  exact lamA_ne_zero T.ρ T.α T.hρ0 i m (by omega)

theorem cpow_ne (α : ℂ) (n : ℕ) : ((n : ℂ) + 1) ^ α ≠ 0 := fun h => by
  have := ((Complex.cpow_eq_zero_iff _ _).mp h).1
  exact absurd this (by exact_mod_cast Nat.succ_ne_zero n)

/-- The transported solutions `y = x S(n) Y` solve `y(n+1) = y(n) Bal(n)`. -/
theorem transport (Nst : ℕ) (hSdet : ∀ n, Nst ≤ n → (T.S n).det ≠ 0) (x : ℕ → Fin 3 → ℂ)
    (hrec : ∀ n, Nst ≤ n → x (n + 1) = x n ᵥ* T.Nm n) (n : ℕ) (hn : Nst ≤ n) :
    x (n + 1) ᵥ* (T.S (n + 1) * T.Y) = (x n ᵥ* (T.S n * T.Y)) ᵥ* T.Bal n := by
  rw [hrec n hn, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    T.Nm_mul_S n (hSdet (n + 1) (by omega)), Shear.Mp,
    Matrix.mul_assoc (T.S n) (T.Y * T.Bal n * T.Y⁻¹) T.Y,
    Matrix.mul_assoc (T.Y * T.Bal n) T.Y⁻¹ T.Y, Matrix.nonsing_inv_mul _ T.hYu, Matrix.mul_one,
    ← Matrix.mul_assoc]

/-- **The modal basis of the balanced walk.** -/
theorem modal : ∃ (B₀ : Matrix (Fin 3) (Fin 3) ℂ) (α : Fin 3 → ℂ) (c : Fin 3 → ℕ → ℂ),
    B₀.det ≠ 0 ∧ (∀ i n, c i n ≠ 0) ∧ (∀ i, Tendsto (c i) atTop (𝓝 1)) ∧
    Tendsto (fun n : ℕ => Matrix.diagonal (fun i => (T.ρ i ^ n * ((n : ℂ) + 1) ^ α i * c i n)⁻¹) *
      (B₀ * D.W n)) atTop (𝓝 T.Y) := by
  obtain ⟨Nst, hNst1, hSdet, hNα, hsol⟩ := common_start (T := T)
  choose x z hrec hx hz using hsol
  choose κ hκ0 hκ using fun i => tendsto_prodA_div (T.α i) Nst (hNα i)
  have hκ'0 : ∀ i, κ i / T.ρ i ^ Nst ≠ 0 := fun i =>
    div_ne_zero (hκ0 i) (pow_ne_zero _ (T.hρ0 i))
  have hΦ0 : ∀ i n, (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) ≠ 0 := fun i n =>
    prod_lamA_ne_zero i Nst n (hNα i)
  have hpow0 : ∀ i (n : ℕ), T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i ≠ 0 := fun i n =>
    mul_ne_zero (pow_ne_zero _ (T.hρ0 i)) (cpow_ne _ n)
  obtain ⟨B₀, hB₀⟩ : ∃ B : Matrix (Fin 3) (Fin 3) ℂ, B =
      Matrix.diagonal (fun i => (κ i / T.ρ i ^ Nst)⁻¹) *
        Matrix.of (fun i => x i Nst ᵥ* (T.S Nst * T.Y)) * (D.W Nst)⁻¹ := ⟨_, rfl⟩
  have hrow : ∀ n, Nst ≤ n → ∀ i, (B₀ * D.W n) i =
      (κ i / T.ρ i ^ Nst)⁻¹ • (x i n ᵥ* (T.S n * T.Y)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro i
      rw [hB₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (D.hWdet Nst hNst1)),
        Matrix.mul_one, diagonal_row]
      rfl
    | succ n hn ih =>
      intro i
      rw [D.hW n (by omega), ← Matrix.mul_assoc, row_mul, ih i, Matrix.smul_vecMul,
        ← transport (T := T) Nst hSdet (x i) (hrec i) n hn]
  have hc : ∀ i (n : ℕ), T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i *
      ((κ i / T.ρ i ^ Nst)⁻¹ * (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) /
        (T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i)) =
      (κ i / T.ρ i ^ Nst)⁻¹ * (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) := fun i n =>
    mul_div_cancel₀ _ (hpow0 i n)
  have heq : ∀ n, Nst ≤ n → Matrix.diagonal (fun i => (T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i *
      ((κ i / T.ρ i ^ Nst)⁻¹ * (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) /
        (T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i)))⁻¹) * (B₀ * D.W n) =
      Matrix.of fun i => (Pi.single i 1 + z i n) ᵥ* (T.S n * T.Y) := by
    intro n hn
    ext i j
    have hs : ((κ i / T.ρ i ^ Nst)⁻¹ * ∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m)⁻¹ *
        ((κ i / T.ρ i ^ Nst)⁻¹ * ∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) = 1 :=
      inv_mul_cancel₀ (mul_ne_zero (inv_ne_zero (hκ'0 i)) (hΦ0 i n))
    rw [Matrix.diagonal_mul, hrow n hn i, hc, hx i n, Matrix.smul_vecMul, Matrix.of_apply,
      Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc ((κ i / T.ρ i ^ Nst)⁻¹) (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m), ← mul_assoc,
      hs, one_mul]
  have hlim : Tendsto (fun n => Matrix.of fun i => (Pi.single i 1 + z i n) ᵥ* (T.S n * T.Y))
      atTop (𝓝 T.Y) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have h1 : Tendsto (fun n => Pi.single i (1 : ℂ) + z i n) atTop (𝓝 (Pi.single i 1 + 0)) :=
      tendsto_const_nhds.add (hz i)
    have h2 : Tendsto (fun n => T.S n * T.Y) atTop (𝓝 (1 * T.Y)) :=
      ((continuous_id.matrix_mul continuous_const).tendsto (1 : Matrix (Fin 3) (Fin 3) ℂ)).comp
        T.S_tendsto
    have := tendsto_vecMul h1 h2
    rw [add_zero, Matrix.one_mul, single_vecMul] at this
    exact this
  have hT : Tendsto (fun n : ℕ => Matrix.diagonal (fun i => (T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i *
      ((κ i / T.ρ i ^ Nst)⁻¹ * (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) /
        (T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i)))⁻¹) * (B₀ * D.W n)) atTop (𝓝 T.Y) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop Nst] with n hn
    exact (heq n hn).symm
  refine ⟨B₀, T.α, fun i n => (κ i / T.ρ i ^ Nst)⁻¹ *
    (∏ m ∈ Finset.Ico Nst n, lamA T.ρ T.α i m) / (T.ρ i ^ n * ((n : ℂ) + 1) ^ T.α i), ?_,
    fun i n => div_ne_zero (mul_ne_zero (inv_ne_zero (hκ'0 i)) (hΦ0 i n)) (hpow0 i n),
    fun i => ?_, hT⟩
  · intro h0
    have h := ((continuous_id.matrix_det.tendsto T.Y).comp hT).eventually_ne T.hY
    obtain ⟨n, hn⟩ := h.exists
    apply hn
    simp only [Function.comp, id]
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, mul_zero]
  · have h := (hκ i).div_const (κ i)
    rw [div_self (hκ0 i)] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop Nst] with n hn
    rw [prod_lamA, show T.ρ i ^ n = T.ρ i ^ Nst * T.ρ i ^ (n - Nst) by
      rw [← pow_add, Nat.add_sub_cancel' hn]]
    have h1 := T.hρ0 i
    have h2 := hκ0 i
    have h3 := cpow_ne (T.α i) n
    field_simp

end WalkData

end Pfq54.LV
