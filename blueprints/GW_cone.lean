/-
# Perturbed products of a matrix with one real and two complex eigenvalues

PDF Part VII §6 ("the cone argument"). `L` is a real `3 × 3` matrix with
`(L - λ)(L² - τL + σ) = 0`, `τ² < 4σ` and `|λ| < √σ` (one real eigenvalue `λ` and a complex pair
of modulus `√σ`), and `x (N+1) = x N ᵥ* M N` with `M N → L`. Then:
* `cone_growth`: `‖x N‖ ≤ C (√σ + δ)^N` for every `δ > 0`;
* `cone_decay`: if moreover `‖x N‖ ≤ C₀ r^N` with `r < √σ`, then `‖x N‖ ≤ C (|λ| + δ)^N`.
The proof splits `x = a + b` along `P = q(L)/q(λ)`, `q(X) = X² - τX + σ`; on the plane
`b q(L) = 0` the quadratic form `G` satisfies `G(b L) = σ G(b)` exactly. A vector in the cone
`G(b) ≥ ‖a‖²` stays there and grows at rate `≈ √σ`; the a priori bound excludes this, and outside
the cone `a` contracts at rate `≈ |λ|`.
-/
import Mathlib

open Matrix Filter Topology

noncomputable section

namespace ZetasIrr.GW

/-! ### Scalar recursions -/

theorem bound_of_eventually {Z : ℕ → ℝ} {ρ C : ℝ} (hρ : 0 < ρ)
    (h : ∀ᶠ N in atTop, Z N ≤ C * ρ ^ N) : ∃ C', ∀ N, Z N ≤ C' * ρ ^ N := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  refine ⟨max C (∑ k ∈ Finset.range N₀, |Z k| / ρ ^ k), fun N => ?_⟩
  have hp : 0 < ρ ^ N := pow_pos hρ N
  rcases le_or_gt N₀ N with hN | hN
  · exact (hN₀ N hN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have h1 : |Z N| / ρ ^ N ≤ ∑ k ∈ Finset.range N₀, |Z k| / ρ ^ k :=
      Finset.single_le_sum (f := fun k => |Z k| / ρ ^ k) (fun k _ => by positivity)
        (Finset.mem_range.mpr hN)
    have h2 := (div_le_iff₀ hp).mp (h1.trans (le_max_right C _))
    exact (le_abs_self _).trans h2

theorem geom_of_eventually {Z : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hZ : ∀ N, 0 ≤ Z N)
    (h : ∀ᶠ N in atTop, Z (N + 1) ≤ ρ * Z N) : ∃ C, ∀ N, Z N ≤ C * ρ ^ N := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  refine bound_of_eventually hρ (C := Z N₀ / ρ ^ N₀) (eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => rw [add_zero, div_mul_cancel₀ _ (pow_pos hρ N₀).ne']
  | succ k ih =>
    calc Z (N₀ + (k + 1)) ≤ ρ * Z (N₀ + k) := hN₀ _ (Nat.le_add_right _ _)
      _ ≤ ρ * (Z N₀ / ρ ^ N₀ * ρ ^ (N₀ + k)) :=
        mul_le_mul_of_nonneg_left (ih (Nat.le_add_right _ _)) hρ.le
      _ = Z N₀ / ρ ^ N₀ * ρ ^ (N₀ + (k + 1)) := by ring

/-- The scalar form of the perturbed recursion. -/
structure Rec (X Y ε : ℕ → ℝ) (ℓ s : ℝ) : Prop where
  X0 : ∀ N, 0 ≤ X N
  Y0 : ∀ N, 0 ≤ Y N
  ε0 : ∀ N, 0 ≤ ε N
  εlim : Tendsto ε atTop (𝓝 0)
  hX : ∀ N, X (N + 1) ≤ ℓ * X N + ε N * (X N + Y N)
  hY1 : ∀ N, Y (N + 1) ≤ s * Y N + ε N * (X N + Y N)
  hY2 : ∀ N, s * Y N - ε N * (X N + Y N) ≤ Y (N + 1)

theorem Rec.small {X Y ε : ℕ → ℝ} {ℓ s : ℝ} (h : Rec X Y ε ℓ s) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N in atTop, ε N ≤ η :=
  (h.εlim.eventually (gt_mem_nhds hη)).mono fun _ h => h.le

theorem Rec.growth {X Y ε : ℕ → ℝ} {ℓ s : ℝ} (h : Rec X Y ε ℓ s) (hℓ : ℓ ≤ s) (hs : 0 < s)
    {δ : ℝ} (hδ : 0 < δ) : ∃ C, ∀ N, X N + Y N ≤ C * (s + δ) ^ N := by
  refine geom_of_eventually (by linarith) (fun N => add_nonneg (h.X0 N) (h.Y0 N)) ?_
  filter_upwards [h.small (half_pos hδ)] with N hN
  have h1 := h.hX N
  have h2 := h.hY1 N
  have h3 : ℓ * X N ≤ s * X N := mul_le_mul_of_nonneg_right hℓ (h.X0 N)
  have h4 : ε N * (X N + Y N) ≤ δ / 2 * (X N + Y N) :=
    mul_le_mul_of_nonneg_right hN (add_nonneg (h.X0 N) (h.Y0 N))
  nlinarith

/-- Inside the cone `X ≤ Y` the recursion stays in the cone and `Y` grows at rate `s - 2η`. -/
theorem Rec.cone {X Y ε : ℕ → ℝ} {ℓ s : ℝ} (h : Rec X Y ε ℓ s) (hℓ0 : 0 ≤ ℓ) {η : ℝ}
    (hηs : ℓ + 2 * η ≤ s - 2 * η)
    (M : ℕ) (hM : ∀ N ≥ M, ε N ≤ η) (hXY : X M ≤ Y M) (k : ℕ) :
    X (M + k) ≤ Y (M + k) ∧ (s - 2 * η) ^ k * Y M ≤ Y (M + k) := by
  induction k with
  | zero => simpa using hXY
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    have hε := hM (M + k) (by omega)
    have e0 := h.ε0 (M + k)
    have x0 := h.X0 (M + k)
    have y0 := h.Y0 (M + k)
    have hY := h.hY2 (M + k)
    have hX := h.hX (M + k)
    have hc : ε (M + k) * (X (M + k) + Y (M + k)) ≤ η * (2 * Y (M + k)) :=
      mul_le_mul hε (by linarith) (by positivity) (by linarith)
    have hgrow : (s - 2 * η) * Y (M + k) ≤ Y (M + k + 1) := by nlinarith
    refine ⟨?_, ?_⟩
    · have : X (M + k + 1) ≤ (ℓ + 2 * η) * Y (M + k) := by nlinarith
      exact this.trans ((mul_le_mul_of_nonneg_right hηs y0).trans hgrow)
    · rw [pow_succ, mul_comm _ (s - 2 * η), mul_assoc]
      have hpos : 0 ≤ s - 2 * η := by
        have : 0 ≤ ℓ + 2 * η := by
          have := hM M le_rfl
          linarith [h.ε0 M]
        linarith
      exact (mul_le_mul_of_nonneg_left i2 hpos).trans hgrow

theorem Rec.decay {X Y ε : ℕ → ℝ} {ℓ s : ℝ} (h : Rec X Y ε ℓ s) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < s)
    {C₀ r : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hb : ∀ N, X N + Y N ≤ C₀ * r ^ N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ N, X N + Y N ≤ C * (ℓ + δ) ^ N := by
  obtain ⟨η, hη, hη1, hη2⟩ : ∃ η > 0, ℓ + 2 * η ≤ s - 2 * η ∧ r < s - 2 * η :=
    ⟨min ((s - ℓ) / 4) ((s - r) / 4), lt_min (by linarith) (by linarith),
      by linarith [min_le_left ((s - ℓ) / 4) ((s - r) / 4)],
      by linarith [min_le_right ((s - ℓ) / 4) ((s - r) / 4)]⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h.small hη)
  have hcone : ∀ N ≥ N₀, Y N ≤ X N := by
    intro M hM
    by_contra hlt0
    have hlt := lt_of_not_ge hlt0
    have hYM : 0 < Y M := lt_of_le_of_lt (h.X0 M) hlt
    have hs2 : 0 < s - 2 * η := by linarith
    have hlim : Tendsto (fun k : ℕ => C₀ * r ^ M * (r / (s - 2 * η)) ^ k) atTop (𝓝 0) := by
      rw [← mul_zero (C₀ * r ^ M)]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hs2.le)
        ((div_lt_one hs2).mpr hη2)).const_mul _
    have hle : ∀ k : ℕ, Y M ≤ C₀ * r ^ M * (r / (s - 2 * η)) ^ k := by
      intro k
      have h1 := (h.cone hℓ hη1 M (fun N hN => hN₀ N (by omega)) hlt.le k).2
      have h2 : Y (M + k) ≤ C₀ * r ^ M * r ^ k := by
        have := hb (M + k); rw [pow_add, ← mul_assoc] at this; linarith [h.X0 (M + k)]
      rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hs2 k)]
      linarith [mul_comm ((s - 2 * η) ^ k) (Y M)]
    exact absurd (ge_of_tendsto' hlim hle) (not_le.mpr hYM)
  obtain ⟨C, hC⟩ := geom_of_eventually (Z := X) (ρ := ℓ + δ) (by linarith) h.X0 (by
    filter_upwards [eventually_ge_atTop N₀, h.small (half_pos hδ)] with N hN hε
    have := h.hX N
    have := hcone N hN
    have := h.ε0 N
    have := h.X0 N
    nlinarith)
  refine bound_of_eventually (by linarith) (C := 2 * C) ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  linarith [hcone N hN, hC N]

/-! ### Norms of vector-matrix products -/

def ns (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ k, ∑ j, |A k j|

theorem ns_nonneg (A : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ ns A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem norm_vecMul_le (y : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖y ᵥ* A‖ ≤ ns A * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity [ns_nonneg A])).mpr fun j => ?_
  rw [Real.norm_eq_abs, vecMul, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |y k * A k j| ≤ ∑ k, ‖y‖ * |A k j| := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (norm_le_pi_norm y k) (abs_nonneg _)
    _ = ‖y‖ * ∑ k, |A k j| := by rw [Finset.mul_sum]
    _ ≤ ‖y‖ * ns A := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := fun j => |A k j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) (norm_nonneg _)
    _ = ns A * ‖y‖ := mul_comm _ _

theorem tendsto_ns {M : ℕ → Matrix (Fin 3) (Fin 3) ℝ} {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : Tendsto M atTop (𝓝 L)) : Tendsto (fun N => ns (M N - L)) atTop (𝓝 0) := by
  have h : Tendsto (fun N => M N - L) atTop (𝓝 0) := by
    rw [← sub_self L]; exact hM.sub tendsto_const_nhds
  have hc : Continuous ns := by unfold ns; fun_prop
  have h0 : ns 0 = 0 := by simp [ns]
  rw [← h0]
  exact (hc.tendsto 0).comp h

theorem norm_sq_le_dot (y : Fin 3 → ℝ) : ‖y‖ ^ 2 ≤ y ⬝ᵥ y := by
  have h0 : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
  have : ‖y‖ ≤ √(y ⬝ᵥ y) := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun i => y i * y i) (fun i _ => mul_self_nonneg (y i))
      (Finset.mem_univ i)
  calc ‖y‖ ^ 2 ≤ √(y ⬝ᵥ y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = y ⬝ᵥ y := Real.sq_sqrt h0

theorem dot_le_norm (y z : Fin 3 → ℝ) : |y ⬝ᵥ z| ≤ 3 * (‖y‖ * ‖z‖) := by
  rw [dotProduct, Fin.sum_univ_three]
  have h : ∀ i, |y i * z i| ≤ ‖y‖ * ‖z‖ := fun i => by
    rw [abs_mul]; exact mul_le_mul (norm_le_pi_norm y i) (norm_le_pi_norm z i) (abs_nonneg _)
      (norm_nonneg _)
  calc |y 0 * z 0 + y 1 * z 1 + y 2 * z 2| ≤ |y 0 * z 0| + |y 1 * z 1| + |y 2 * z 2| :=
        abs_add_three _ _ _
    _ ≤ 3 * (‖y‖ * ‖z‖) := by linarith [h 0, h 1, h 2]

/-! ### The invariant quadratic form on the plane -/

section form

variable (L : Matrix (Fin 3) (Fin 3) ℝ) (τ σ : ℝ)

def Bf (y z : Fin 3 → ℝ) : ℝ :=
  (y ᵥ* L) ⬝ᵥ (z ᵥ* L) - τ / 2 * ((y ᵥ* L) ⬝ᵥ z + (z ᵥ* L) ⬝ᵥ y) + σ * (y ⬝ᵥ z)

def Gf (y : Fin 3 → ℝ) : ℝ := Bf L τ σ y y

theorem Gf_add (y z : Fin 3 → ℝ) (t : ℝ) :
    Gf L τ σ (y + t • z) = Gf L τ σ z * (t * t) + 2 * Bf L τ σ y z * t + Gf L τ σ y := by
  simp only [Gf, Bf, Matrix.add_vecMul, Matrix.smul_vecMul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (z ᵥ* L) (y ᵥ* L),
    dotProduct_comm z y]
  ring

theorem Gf_eq (y : Fin 3 → ℝ) : Gf L τ σ y = (y ᵥ* L - (τ / 2) • y) ⬝ᵥ (y ᵥ* L - (τ / 2) • y) +
    (σ - τ ^ 2 / 4) * (y ⬝ᵥ y) := by
  simp only [Gf, Bf, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm y (y ᵥ* L)]
  ring

theorem dot_self_nonneg (y : Fin 3 → ℝ) : 0 ≤ y ⬝ᵥ y :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)

def nu (y : Fin 3 → ℝ) : ℝ := √(Gf L τ σ y)

variable {τ σ}

theorem Gf_ge (h : τ ^ 2 < 4 * σ) (y : Fin 3 → ℝ) : (σ - τ ^ 2 / 4) * ‖y‖ ^ 2 ≤ Gf L τ σ y := by
  rw [Gf_eq]
  have := mul_le_mul_of_nonneg_left (norm_sq_le_dot y) (by linarith : 0 ≤ σ - τ ^ 2 / 4)
  linarith [dot_self_nonneg (y ᵥ* L - (τ / 2) • y)]

theorem Gf_nonneg (h : τ ^ 2 < 4 * σ) (y : Fin 3 → ℝ) : 0 ≤ Gf L τ σ y :=
  le_trans (mul_nonneg (by linarith) (sq_nonneg _)) (Gf_ge L h y)

theorem Bf_le (h : τ ^ 2 < 4 * σ) (y z : Fin 3 → ℝ) :
    Bf L τ σ y z ≤ √(Gf L τ σ y) * √(Gf L τ σ z) := by
  have hd := discrim_le_zero (a := Gf L τ σ z) (b := 2 * Bf L τ σ y z) (c := Gf L τ σ y)
    fun t => by rw [← Gf_add]; exact Gf_nonneg L h _
  rw [discrim] at hd
  rw [← Real.sqrt_mul (Gf_nonneg L h y)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))

theorem nu_add (h : τ ^ 2 < 4 * σ) (y z : Fin 3 → ℝ) :
    nu L τ σ (y + z) ≤ nu L τ σ y + nu L τ σ z := by
  have e := Gf_add L τ σ y z 1
  rw [one_smul, mul_one, mul_one] at e
  rw [nu, nu, nu, Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), e,
    add_sq, Real.sq_sqrt (Gf_nonneg L h y), Real.sq_sqrt (Gf_nonneg L h z)]
  linarith [Bf_le L h y z]

theorem nu_neg (y : Fin 3 → ℝ) : nu L τ σ (-y) = nu L τ σ y := by
  simp only [nu, Gf, Bf, Matrix.neg_vecMul, neg_dotProduct, dotProduct_neg, neg_neg]

theorem nu_sub (h : τ ^ 2 < 4 * σ) (y z : Fin 3 → ℝ) :
    nu L τ σ y - nu L τ σ z ≤ nu L τ σ (y + z) := by
  have := nu_add L h (y + z) (-z)
  rw [add_neg_cancel_right, nu_neg] at this
  linarith

theorem nu_scale (hσ : 0 ≤ σ) (b : Fin 3 → ℝ)
    (hb : b ᵥ* (L * L) = τ • (b ᵥ* L) - σ • b) : nu L τ σ (b ᵥ* L) = √σ * nu L τ σ b := by
  have e : Gf L τ σ (b ᵥ* L) = σ * Gf L τ σ b := by
    simp only [Gf, Bf, Matrix.vecMul_vecMul, hb, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm b (b ᵥ* L)]
    ring
  rw [nu, nu, e, Real.sqrt_mul hσ]

theorem nu_le (y : Fin 3 → ℝ) :
    nu L τ σ y ≤ √(3 * ns L ^ 2 + 3 * |τ| * ns L + 3 * |σ|) * ‖y‖ := by
  have h1 := dot_le_norm (y ᵥ* L) (y ᵥ* L)
  have h2 := dot_le_norm (y ᵥ* L) y
  have h3 := dot_le_norm y y
  have hL := norm_vecMul_le y L
  have hn := ns_nonneg L
  have hy := norm_nonneg y
  have hyL := norm_nonneg (y ᵥ* L)
  have hG : Gf L τ σ y ≤ (3 * ns L ^ 2 + 3 * |τ| * ns L + 3 * |σ|) * ‖y‖ ^ 2 := by
    have e : Gf L τ σ y = (y ᵥ* L) ⬝ᵥ (y ᵥ* L) - τ * ((y ᵥ* L) ⬝ᵥ y) + σ * (y ⬝ᵥ y) := by
      simp only [Gf, Bf]; ring
    rw [e]
    have a1 : (y ᵥ* L) ⬝ᵥ (y ᵥ* L) ≤ 3 * (ns L ^ 2 * ‖y‖ ^ 2) := by
      have := mul_le_mul hL hL hyL (by positivity)
      linarith [le_abs_self ((y ᵥ* L) ⬝ᵥ (y ᵥ* L))]
    have a2 : -(τ * ((y ᵥ* L) ⬝ᵥ y)) ≤ 3 * |τ| * ns L * ‖y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hL hy
      have := neg_abs_le (τ * ((y ᵥ* L) ⬝ᵥ y))
      rw [abs_mul] at this
      nlinarith [abs_nonneg τ]
    have a3 : σ * (y ⬝ᵥ y) ≤ 3 * |σ| * ‖y‖ ^ 2 := by
      have := le_abs_self (σ * (y ⬝ᵥ y))
      rw [abs_mul] at this
      nlinarith [abs_nonneg σ]
    nlinarith
  rw [nu, ← Real.sqrt_sq hy, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hG

end form

/-! ### The splitting along the real eigenvalue -/

/-- `P` projects onto the `λ`-line and `Q = 1 - P` onto the plane `y q(L) = 0`. -/
structure Split (L : Matrix (Fin 3) (Fin 3) ℝ) (lam τ σ : ℝ) (P Q : Matrix (Fin 3) (Fin 3) ℝ) :
    Prop where
  sum : P + Q = 1
  PL : L * P = lam • P
  QL : Q * L = L * Q
  plane : ∀ y : Fin 3 → ℝ, (y ᵥ* Q) ᵥ* (L * L) = τ • ((y ᵥ* Q) ᵥ* L) - σ • (y ᵥ* Q)

theorem split_exists {L : Matrix (Fin 3) (Fin 3) ℝ} {lam τ σ : ℝ}
    (hL : (L - lam • 1) * (L * L - τ • L + σ • 1) = 0) (hd : τ ^ 2 < 4 * σ) :
    ∃ P Q, Split L lam τ σ P Q := by
  set q := L * L - τ • L + σ • (1 : Matrix (Fin 3) (Fin 3) ℝ)
  set ql := lam ^ 2 - τ * lam + σ
  have hql : ql ≠ 0 := by nlinarith [sq_nonneg (lam - τ / 2)]
  have hc : L * q = q * L := by
    simp only [q, mul_sub, sub_mul, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      one_mul, mul_assoc]
  have hLq : L * q = lam • q := by
    rw [sub_mul, Matrix.smul_mul, one_mul, sub_eq_zero] at hL; exact hL
  have hqq : q * q = ql • q := by
    have h2 : q * (L * L) = lam ^ 2 • q := by
      rw [← mul_assoc, ← hc, hLq, Matrix.smul_mul, ← hc, hLq, smul_smul, sq]
    calc q * q = q * (L * L) - τ • (q * L) + σ • q := by
          simp only [q, mul_sub, mul_add, Matrix.mul_smul, mul_one]
      _ = ql • q := by rw [h2, ← hc, hLq, smul_smul, ← sub_smul, ← add_smul]
  refine ⟨ql⁻¹ • q, 1 - ql⁻¹ • q, add_sub_cancel _ _, ?_, ?_, fun y => ?_⟩
  · rw [Matrix.mul_smul, hLq, smul_comm]
  · rw [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hc]
  · have h0 : (1 - ql⁻¹ • q) * q = 0 := by
      rw [sub_mul, one_mul, Matrix.smul_mul, hqq, smul_smul, inv_mul_cancel₀ hql, one_smul,
        sub_self]
    have hb0 : (y ᵥ* (1 - ql⁻¹ • q)) ᵥ* q = 0 := by
      rw [Matrix.vecMul_vecMul, h0, Matrix.vecMul_zero]
    have expand : ∀ v : Fin 3 → ℝ, v ᵥ* q = v ᵥ* (L * L) - τ • (v ᵥ* L) + σ • v := fun v => by
      simp only [q, Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [expand] at hb0
    rw [← sub_eq_zero, ← hb0]
    abel

/-- **The scalar recursion of a perturbed product.** -/
theorem cone_rec {L : Matrix (Fin 3) (Fin 3) ℝ} {lam τ σ : ℝ}
    (hL : (L - lam • 1) * (L * L - τ • L + σ • 1) = 0) (hd : τ ^ 2 < 4 * σ)
    {M : ℕ → Matrix (Fin 3) (Fin 3) ℝ} (hM : Tendsto M atTop (𝓝 L)) {x : ℕ → Fin 3 → ℝ}
    (hx : ∀ N, x (N + 1) = x N ᵥ* M N) :
    ∃ X Y ε : ℕ → ℝ, ∃ c₁ c₂ : ℝ, Rec X Y ε |lam| √σ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      (∀ N, ‖x N‖ ≤ c₁ * (X N + Y N)) ∧ ∀ N, X N + Y N ≤ c₂ * ‖x N‖ := by
  obtain ⟨P, Q, hS⟩ := split_exists hL hd
  have hσ : 0 ≤ σ := by nlinarith [sq_nonneg τ]
  set κ := σ - τ ^ 2 / 4
  have hκ : 0 < κ := by simp only [κ]; linarith
  set K := √(3 * ns L ^ 2 + 3 * |τ| * ns L + 3 * |σ|)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  set c₁ := 1 + (√κ)⁻¹
  have hc₁ : 0 ≤ c₁ := by positivity
  have hb_le : ∀ y, ‖y‖ ≤ (√κ)⁻¹ * nu L τ σ y := fun y => by
    rw [le_inv_mul_iff₀ (Real.sqrt_pos.mpr hκ), nu, ← Real.sqrt_sq (norm_nonneg y),
      ← Real.sqrt_mul hκ.le]
    exact Real.sqrt_le_sqrt (Gf_ge L hd y)
  have hdec : ∀ N, x N = x N ᵥ* P + x N ᵥ* Q := fun N => by
    rw [← Matrix.vecMul_add, hS.sum, Matrix.vecMul_one]
  have hx_le : ∀ N, ‖x N‖ ≤ c₁ * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q)) := fun N => by
    have h1 : ‖x N‖ ≤ ‖x N ᵥ* P‖ + ‖x N ᵥ* Q‖ := by
      conv_lhs => rw [hdec N]
      exact norm_add_le _ _
    have h2 := hb_le (x N ᵥ* Q)
    have h3 : 0 ≤ nu L τ σ (x N ᵥ* Q) := Real.sqrt_nonneg _
    have h4 : 0 ≤ (√κ)⁻¹ := by positivity
    simp only [c₁]
    nlinarith [norm_nonneg (x N ᵥ* P)]
  have hE : ∀ N (R : Matrix (Fin 3) (Fin 3) ℝ), ‖x N ᵥ* ((M N - L) * R)‖ ≤
      ns R * ns (M N - L) * (c₁ * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q))) := fun N R => by
    rw [← Matrix.vecMul_vecMul]
    refine (norm_vecMul_le _ R).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_vecMul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hx_le N) (ns_nonneg _))) (ns_nonneg R)
  have hdx : ∀ N (R : Matrix (Fin 3) (Fin 3) ℝ), x (N + 1) ᵥ* R =
      x N ᵥ* ((M N - L) * R) + x N ᵥ* (L * R) := fun N R => by
    rw [hx, Matrix.vecMul_vecMul, ← Matrix.vecMul_add, sub_mul, sub_add_cancel]
  set e : ℕ → ℝ := fun N => (ns P + K * ns Q) * c₁ * ns (M N - L)
  have hZ0 : ∀ N, 0 ≤ ‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q) :=
    fun N => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hQe : ∀ N, K * (ns Q * ns (M N - L) * (c₁ * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q)))) ≤
      e N * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q)) := fun N => by
    have := mul_nonneg (ns_nonneg P) (mul_nonneg hc₁ (mul_nonneg (ns_nonneg (M N - L)) (hZ0 N)))
    simp only [e]
    nlinarith
  have hnuE : ∀ N, nu L τ σ (x N ᵥ* ((M N - L) * Q)) ≤ e N * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q)) :=
    fun N => ((nu_le L _).trans (mul_le_mul_of_nonneg_left (hE N Q) hK)).trans (hQe N)
  refine ⟨fun N => ‖x N ᵥ* P‖, fun N => nu L τ σ (x N ᵥ* Q), e, c₁, ns P + K * ns Q,
    ⟨fun N => norm_nonneg _, fun N => Real.sqrt_nonneg _,
      fun N => mul_nonneg (mul_nonneg (by positivity [ns_nonneg P, ns_nonneg Q]) hc₁) (ns_nonneg _),
      by simpa using (tendsto_ns hM).const_mul ((ns P + K * ns Q) * c₁), fun N => ?_, fun N => ?_,
      fun N => ?_⟩, hc₁, by positivity [ns_nonneg P, ns_nonneg Q], hx_le, fun N => ?_⟩
  · show ‖x (N + 1) ᵥ* P‖ ≤ _
    rw [hdx, hS.PL, Matrix.vecMul_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := hE N P
    have : ns P * ns (M N - L) * (c₁ * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q))) ≤
        e N * (‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q)) := by
      have := mul_nonneg (mul_nonneg hK (ns_nonneg Q))
        (mul_nonneg hc₁ (mul_nonneg (ns_nonneg (M N - L)) (hZ0 N)))
      simp only [e]
      nlinarith
    linarith
  · show nu L τ σ (x (N + 1) ᵥ* Q) ≤ _
    rw [hdx, ← hS.QL, ← Matrix.vecMul_vecMul (x N) Q L, add_comm]
    refine (nu_add L hd _ _).trans ?_
    rw [nu_scale L hσ _ (hS.plane (x N))]
    linarith [hnuE N]
  · show _ ≤ nu L τ σ (x (N + 1) ᵥ* Q)
    rw [hdx, ← hS.QL, ← Matrix.vecMul_vecMul (x N) Q L, add_comm]
    have h2 := nu_sub L hd ((x N ᵥ* Q) ᵥ* L) (x N ᵥ* ((M N - L) * Q))
    rw [nu_scale L hσ _ (hS.plane (x N)), add_comm] at h2
    linarith [hnuE N]
  · have h1 := norm_vecMul_le (x N) P
    have h2 := (nu_le L (x N ᵥ* Q)).trans (mul_le_mul_of_nonneg_left (norm_vecMul_le (x N) Q) hK)
    show ‖x N ᵥ* P‖ + nu L τ σ (x N ᵥ* Q) ≤ (ns P + K * ns Q) * ‖x N‖
    nlinarith

/-- **Growth** (PDF Part VII §6: products of perturbations of a matrix of spectral radius `√σ`). -/
theorem cone_growth {L : Matrix (Fin 3) (Fin 3) ℝ} {lam τ σ : ℝ}
    (hL : (L - lam • 1) * (L * L - τ • L + σ • 1) = 0) (hd : τ ^ 2 < 4 * σ) (hl : |lam| < √σ)
    {M : ℕ → Matrix (Fin 3) (Fin 3) ℝ} (hM : Tendsto M atTop (𝓝 L)) {x : ℕ → Fin 3 → ℝ}
    (hx : ∀ N, x (N + 1) = x N ᵥ* M N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ N, ‖x N‖ ≤ C * (√σ + δ) ^ N := by
  obtain ⟨X, Y, ε, c₁, c₂, hR, hc₁, -, h1, -⟩ := cone_rec hL hd hM hx
  obtain ⟨C, hC⟩ := hR.growth hl.le (lt_of_le_of_lt (abs_nonneg _) hl) hδ
  exact ⟨c₁ * C, fun N => (h1 N).trans
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hC N) hc₁)⟩

/-- **The cone argument** (PDF Part VII §6): a solution growing more slowly than `√σ`
contracts at the rate `|λ|`. -/
theorem cone_decay {L : Matrix (Fin 3) (Fin 3) ℝ} {lam τ σ : ℝ}
    (hL : (L - lam • 1) * (L * L - τ • L + σ • 1) = 0) (hd : τ ^ 2 < 4 * σ) (hl : |lam| < √σ)
    {M : ℕ → Matrix (Fin 3) (Fin 3) ℝ} (hM : Tendsto M atTop (𝓝 L)) {x : ℕ → Fin 3 → ℝ}
    (hx : ∀ N, x (N + 1) = x N ᵥ* M N) {C₀ r : ℝ} (hr : 0 ≤ r) (hrs : r < √σ)
    (hb : ∀ N, ‖x N‖ ≤ C₀ * r ^ N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ N, ‖x N‖ ≤ C * (|lam| + δ) ^ N := by
  obtain ⟨X, Y, ε, c₁, c₂, hR, hc₁, hc₂, h1, h2⟩ := cone_rec hL hd hM hx
  obtain ⟨C, hC⟩ := hR.decay (abs_nonneg _) hl hr hrs (C₀ := c₂ * C₀) (fun N =>
    (h2 N).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hb N) hc₂)) hδ
  exact ⟨c₁ * C, fun N => (h1 N).trans
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hC N) hc₁)⟩

end ZetasIrr.GW

end
