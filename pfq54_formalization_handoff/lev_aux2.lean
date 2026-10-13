/-
# Levinson's theorem for a diagonal system with a summable perturbation (sorry-free)

Row system `x_{n+1} = x_n M(n)`, `M(n) = Λ(n) + R(n)`, `Λ(n) = diag(λ_j(n))`, with
`∑ nrm R(n)/|λ_i(n)| < ∞` and Levinson's dichotomy for the ratios `q_j = λ_j/λ_i`. For each `i`
there is a solution `x_n = (∏_{m<n} λ_i(m)) (e_i + z_n)`, `z_n → 0`, obtained as the fixed point
of the usual operator (forward sums over the recessive directions, tail sums over the dominant ones)
on the complete space of bounded sequences.
-/
import lev_aux1

open Finset Filter Topology
open scoped Matrix

noncomputable section

namespace Pfq54.LV

/-- `q_j(n) = λ_j(n)/λ_i(n)`. -/
def qq (lam : Fin 3 → ℕ → ℂ) (i j : Fin 3) (n : ℕ) : ℂ := lam j n / lam i n

/-- `P_j(k,n) = ∏_{m=k}^{n-1} q_j(m)`. -/
def PP (lam : Fin 3 → ℕ → ℂ) (i j : Fin 3) (k n : ℕ) : ℂ := ∏ m ∈ Finset.Ico k n, qq lam i j m

/-- `R(n) = M(n) - Λ(n)`. -/
def RR (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (n : ℕ) :
    Matrix (Fin 3) (Fin 3) ℂ := M n - Matrix.diagonal (fun j => lam j n)

/-- `g(z, n) = (e_i + z) R(n) / λ_i(n)`. -/
def gg (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (i : Fin 3) (z : Fin 3 → ℂ)
    (n : ℕ) : Fin 3 → ℂ :=
  (lam i n)⁻¹ • ((Pi.single i 1 + z) ᵥ* RR M lam n)

/-- The Levinson operator (coordinate `j` at time `n`), zero before `N`. -/
def TT (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (i : Fin 3) (rec : Fin 3 → Bool)
    (N : ℕ) (z : ℕ → Fin 3 → ℂ) (n : ℕ) (j : Fin 3) : ℂ :=
  if N ≤ n then
    (if rec j then ∑ k ∈ Finset.Ico N n, PP lam i j (k + 1) n * gg M lam i (z k) k j
    else -∑' k : ℕ, gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1))
  else 0

theorem PP_self (lam : Fin 3 → ℕ → ℂ) (i j : Fin 3) (n : ℕ) : PP lam i j n n = 1 := by
  simp [PP]

theorem PP_succ_top (lam : Fin 3 → ℕ → ℂ) (i j : Fin 3) (k n : ℕ) (h : k ≤ n) :
    PP lam i j k (n + 1) = PP lam i j k n * qq lam i j n := by
  unfold PP
  rw [Finset.prod_Ico_succ_top h]

theorem PP_succ_bot (lam : Fin 3 → ℕ → ℂ) (i j : Fin 3) (n m : ℕ) (h : n + 1 ≤ m) :
    PP lam i j n m = qq lam i j n * PP lam i j (n + 1) m := by
  unfold PP
  rw [← Finset.prod_Ico_consecutive _ (Nat.le_succ n) h, Nat.Ico_succ_singleton,
    Finset.prod_singleton]

/-! ### Bounds on `g` -/

theorem gg_sub (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (i : Fin 3)
    (z z' : Fin 3 → ℂ) (n : ℕ) :
    gg M lam i z n - gg M lam i z' n = (lam i n)⁻¹ • ((z - z') ᵥ* RR M lam n) := by
  unfold gg
  rw [← smul_sub, ← Matrix.sub_vecMul, add_sub_add_left_eq_sub]

theorem gg_norm_le (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (i : Fin 3)
    (r : ℕ → ℝ) (n : ℕ) (hlam : lam i n ≠ 0) (hR : nrm (RR M lam n) ≤ r n * ‖lam i n‖)
    (z : Fin 3 → ℂ) : ‖gg M lam i z n‖ ≤ (1 + ‖z‖) * r n := by
  have hl : 0 < ‖lam i n‖ := norm_pos_iff.mpr hlam
  have hr : 0 ≤ r n := by
    by_contra h
    rw [not_le] at h
    have := (nrm_nonneg (RR M lam n)).trans hR
    nlinarith
  unfold gg
  rw [norm_smul, norm_inv]
  calc ‖lam i n‖⁻¹ * ‖(Pi.single i 1 + z) ᵥ* RR M lam n‖
      ≤ ‖lam i n‖⁻¹ * ((1 + ‖z‖) * (r n * ‖lam i n‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
        refine (norm_vecMul_le _ _).trans ?_
        refine mul_le_mul ?_ hR (nrm_nonneg _) (by positivity)
        exact (norm_add_le _ _).trans (add_le_add_left (norm_single_le i) _)
    _ = (1 + ‖z‖) * r n := by field_simp

theorem gg_sub_norm_le (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (i : Fin 3)
    (r : ℕ → ℝ) (n : ℕ) (hlam : lam i n ≠ 0) (hR : nrm (RR M lam n) ≤ r n * ‖lam i n‖)
    (z z' : Fin 3 → ℂ) : ‖gg M lam i z n - gg M lam i z' n‖ ≤ ‖z - z'‖ * r n := by
  have hl : 0 < ‖lam i n‖ := norm_pos_iff.mpr hlam
  rw [gg_sub, norm_smul, norm_inv]
  calc ‖lam i n‖⁻¹ * ‖(z - z') ᵥ* RR M lam n‖
      ≤ ‖lam i n‖⁻¹ * (‖z - z'‖ * (r n * ‖lam i n‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
        exact (norm_vecMul_le _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
    _ = ‖z - z'‖ * r n := by field_simp

/-! ### The dichotomy data -/

/-- The hypotheses of Levinson's theorem relative to the index `i`, valid from `N₀` on. -/
structure LevData (M : ℕ → Matrix (Fin 3) (Fin 3) ℂ) (lam : Fin 3 → ℕ → ℂ) (i : Fin 3)
    (rec : Fin 3 → Bool) (N₀ : ℕ) (K : ℝ) (r : ℕ → ℝ) : Prop where
  hK : 1 ≤ K
  hlam : ∀ j n, N₀ ≤ n → lam j n ≠ 0
  hrecK : ∀ j, rec j = true → ∀ k n, N₀ ≤ k → k ≤ n → ‖PP lam i j k n‖ ≤ K
  hrec0 : ∀ j, rec j = true → ∀ k, N₀ ≤ k → Tendsto (fun n => PP lam i j k n) atTop (𝓝 0)
  hdomK : ∀ j, rec j = false → ∀ k n, N₀ ≤ k → k ≤ n → 1 ≤ K * ‖PP lam i j k n‖
  hr0 : ∀ n, 0 ≤ r n
  hr : Summable r
  hR : ∀ n, N₀ ≤ n → nrm (RR M lam n) ≤ r n * ‖lam i n‖

variable {M : ℕ → Matrix (Fin 3) (Fin 3) ℂ} {lam : Fin 3 → ℕ → ℂ} {i : Fin 3}
  {rec : Fin 3 → Bool} {N₀ : ℕ} {K : ℝ} {r : ℕ → ℝ}

theorem LevData.inv_PP_le (D : LevData M lam i rec N₀ K r) (j : Fin 3) (hj : rec j = false)
    (k n : ℕ) (hk : N₀ ≤ k) (hkn : k ≤ n) : ‖(PP lam i j k n)⁻¹‖ ≤ K := by
  have h := D.hdomK j hj k n hk hkn
  have hP : 0 < ‖PP lam i j k n‖ := by
    by_contra h0
    rw [not_lt] at h0
    have : K * ‖PP lam i j k n‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [D.hK]) h0
    linarith
  have hKpos : 0 < K := by linarith [D.hK]
  rw [norm_inv, inv_le_comm₀ hP hKpos]
  calc K⁻¹ = K⁻¹ * 1 := (mul_one _).symm
    _ ≤ K⁻¹ * (K * ‖PP lam i j k n‖) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hKpos.le)
    _ = ‖PP lam i j k n‖ := by field_simp

theorem LevData.tail_summable (D : LevData M lam i rec N₀ K r) (n : ℕ) :
    Summable (fun k => r (k + n)) := (summable_nat_add_iff n).mpr D.hr

theorem LevData.tail_mono (D : LevData M lam i rec N₀ K r) (N n : ℕ) (h : N ≤ n) :
    ∑' k, r (k + n) ≤ ∑' k, r (k + N) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := (D.tail_summable N).sum_add_tsum_nat_add d
  have h2 : ∑' k, r (k + (N + d)) = ∑' k, r (k + d + N) := by
    congr 1; funext k; congr 1; omega
  rw [h2, ← h1]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => D.hr0 _)

theorem LevData.sum_Ico_le (D : LevData M lam i rec N₀ K r) (N n : ℕ) :
    ∑ k ∈ Finset.Ico N n, r k ≤ ∑' k, r (k + N) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∀ k, r (N + k) = r (k + N) := fun k => by rw [add_comm]
  simp only [this]
  exact (D.tail_summable N).sum_le_tsum _ (fun _ _ => D.hr0 _)

/-! ### Bounds on the operator -/

/-- The termwise bound for the dominant tail sums. -/
theorem LevData.dom_term_le (D : LevData M lam i rec N₀ K r) (j : Fin 3) (hj : rec j = false)
    (N : ℕ) (hN : N₀ ≤ N) (z : ℕ → Fin 3 → ℂ) (C : ℝ) (hz : ∀ k, ‖z k‖ ≤ C) (n : ℕ)
    (hn : N ≤ n) (k : ℕ) :
    ‖gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1)‖ ≤ K * (1 + C) * r (k + n) := by
  have hkn : N₀ ≤ k + n := by omega
  rw [div_eq_mul_inv, norm_mul]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hz 0)
  have h1 : ‖gg M lam i (z (k + n)) (k + n) j‖ ≤ (1 + C) * r (k + n) :=
    (norm_le_pi_norm _ j).trans ((gg_norm_le M lam i r _ (D.hlam i _ hkn) (D.hR _ hkn) _).trans
      (mul_le_mul_of_nonneg_right (add_le_add_right (hz _) 1) (D.hr0 _)))
  have h2 : ‖(PP lam i j n (k + n + 1))⁻¹‖ ≤ K := D.inv_PP_le j hj n (k + n + 1) (by omega) (by omega)
  calc ‖gg M lam i (z (k + n)) (k + n) j‖ * ‖(PP lam i j n (k + n + 1))⁻¹‖
      ≤ ((1 + C) * r (k + n)) * K :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (by linarith) (D.hr0 _))
    _ = K * (1 + C) * r (k + n) := by ring

theorem LevData.dom_summable (D : LevData M lam i rec N₀ K r) (j : Fin 3) (hj : rec j = false)
    (N : ℕ) (hN : N₀ ≤ N) (z : ℕ → Fin 3 → ℂ) (C : ℝ) (hz : ∀ k, ‖z k‖ ≤ C) (n : ℕ)
    (hn : N ≤ n) :
    Summable (fun k => gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1)) :=
  Summable.of_norm_bounded ((D.tail_summable n).mul_left (K * (1 + C)))
    (D.dom_term_le j hj N hN z C hz n hn)

theorem LevData.TT_norm_le (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (z : ℕ → Fin 3 → ℂ) (C : ℝ) (hC : 0 ≤ C) (hz : ∀ k, ‖z k‖ ≤ C) (n : ℕ) :
    ‖(fun j => TT M lam i rec N z n j)‖ ≤ K * (1 + C) * ∑' k, r (k + N) := by
  have hKC : 0 ≤ K * (1 + C) := mul_nonneg (by linarith [D.hK]) (by linarith)
  have htail0 : 0 ≤ ∑' k, r (k + N) := tsum_nonneg fun _ => D.hr0 _
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hKC htail0)]
  intro j
  unfold TT
  split_ifs with hn hj
  · calc ‖∑ k ∈ Finset.Ico N n, PP lam i j (k + 1) n * gg M lam i (z k) k j‖
        ≤ ∑ k ∈ Finset.Ico N n, K * (1 + C) * r k := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          rw [Finset.mem_Ico] at hk
          rw [norm_mul]
          have h1 := D.hrecK j hj (k + 1) n (by omega) (by omega)
          have h2 : ‖gg M lam i (z k) k j‖ ≤ (1 + C) * r k :=
            (norm_le_pi_norm _ j).trans ((gg_norm_le M lam i r k (D.hlam i k (by omega))
              (D.hR k (by omega)) (z k)).trans
              (mul_le_mul_of_nonneg_right (add_le_add_right (hz k) 1) (D.hr0 _)))
          calc ‖PP lam i j (k + 1) n‖ * ‖gg M lam i (z k) k j‖ ≤ K * ((1 + C) * r k) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by linarith [D.hK])
            _ = K * (1 + C) * r k := by ring
      _ = K * (1 + C) * ∑ k ∈ Finset.Ico N n, r k := by rw [Finset.mul_sum]
      _ ≤ K * (1 + C) * ∑' k, r (k + N) := mul_le_mul_of_nonneg_left (D.sum_Ico_le N n) hKC
  · have hj' : rec j = false := by simpa using hj
    rw [norm_neg]
    calc ‖∑' k, gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1)‖
        ≤ ∑' k, K * (1 + C) * r (k + n) := by
          have hs : Summable (fun k => ‖gg M lam i (z (k + n)) (k + n) j /
              PP lam i j n (k + n + 1)‖) :=
            Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (D.dom_term_le j hj' N hN z C hz n hn)
              ((D.tail_summable n).mul_left (K * (1 + C)))
          exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
            (D.dom_term_le j hj' N hN z C hz n hn) ((D.tail_summable n).mul_left (K * (1 + C))))
      _ = K * (1 + C) * ∑' k, r (k + n) := tsum_mul_left
      _ ≤ K * (1 + C) * ∑' k, r (k + N) := mul_le_mul_of_nonneg_left (D.tail_mono N n hn) hKC
  · simp only [norm_zero]
    exact mul_nonneg hKC htail0

/-! ### Lipschitz bound for the operator -/

theorem LevData.dom_term_sub_le (D : LevData M lam i rec N₀ K r) (j : Fin 3) (hj : rec j = false)
    (N : ℕ) (hN : N₀ ≤ N) (z z' : ℕ → Fin 3 → ℂ) (d : ℝ) (hz : ∀ k, ‖z k - z' k‖ ≤ d) (n : ℕ)
    (hn : N ≤ n) (k : ℕ) :
    ‖gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1) -
      gg M lam i (z' (k + n)) (k + n) j / PP lam i j n (k + n + 1)‖ ≤ K * d * r (k + n) := by
  have hkn : N₀ ≤ k + n := by omega
  have hd : 0 ≤ d := (norm_nonneg _).trans (hz 0)
  rw [← sub_div, div_eq_mul_inv, norm_mul]
  have h1 : ‖gg M lam i (z (k + n)) (k + n) j - gg M lam i (z' (k + n)) (k + n) j‖ ≤
      d * r (k + n) :=
    (norm_le_pi_norm (gg M lam i (z (k + n)) (k + n) - gg M lam i (z' (k + n)) (k + n)) j).trans
      ((gg_sub_norm_le M lam i r _ (D.hlam i _ hkn) (D.hR _ hkn) _ _).trans
        (mul_le_mul_of_nonneg_right (hz _) (D.hr0 _)))
  have h2 : ‖(PP lam i j n (k + n + 1))⁻¹‖ ≤ K := D.inv_PP_le j hj n (k + n + 1) (by omega) (by omega)
  calc ‖gg M lam i (z (k + n)) (k + n) j - gg M lam i (z' (k + n)) (k + n) j‖ *
        ‖(PP lam i j n (k + n + 1))⁻¹‖ ≤ (d * r (k + n)) * K :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hd (D.hr0 _))
    _ = K * d * r (k + n) := by ring

theorem LevData.TT_lip (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (z z' : ℕ → Fin 3 → ℂ) (C : ℝ) (hzC : ∀ k, ‖z k‖ ≤ C) (hz'C : ∀ k, ‖z' k‖ ≤ C)
    (d : ℝ) (hz : ∀ k, ‖z k - z' k‖ ≤ d) (n : ℕ) :
    ‖(fun j => TT M lam i rec N z n j) - (fun j => TT M lam i rec N z' n j)‖ ≤
      K * d * ∑' k, r (k + N) := by
  have hd : 0 ≤ d := (norm_nonneg _).trans (hz 0)
  have hKd : 0 ≤ K * d := mul_nonneg (by linarith [D.hK]) hd
  have htail0 : 0 ≤ ∑' k, r (k + N) := tsum_nonneg fun _ => D.hr0 _
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hKd htail0)]
  intro j
  rw [Pi.sub_apply]
  unfold TT
  split_ifs with hn hj
  · rw [← Finset.sum_sub_distrib]
    calc ‖∑ k ∈ Finset.Ico N n, (PP lam i j (k + 1) n * gg M lam i (z k) k j -
          PP lam i j (k + 1) n * gg M lam i (z' k) k j)‖
        ≤ ∑ k ∈ Finset.Ico N n, K * d * r k := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          rw [Finset.mem_Ico] at hk
          rw [← mul_sub, norm_mul]
          have h1 := D.hrecK j hj (k + 1) n (by omega) (by omega)
          have h2 : ‖gg M lam i (z k) k j - gg M lam i (z' k) k j‖ ≤ d * r k :=
            (norm_le_pi_norm (gg M lam i (z k) k - gg M lam i (z' k) k) j).trans
              ((gg_sub_norm_le M lam i r k (D.hlam i k (by omega)) (D.hR k (by omega)) _ _).trans
                (mul_le_mul_of_nonneg_right (hz k) (D.hr0 k)))
          calc ‖PP lam i j (k + 1) n‖ * ‖gg M lam i (z k) k j - gg M lam i (z' k) k j‖
              ≤ K * (d * r k) := mul_le_mul h1 h2 (norm_nonneg _) (by linarith [D.hK])
            _ = K * d * r k := by ring
      _ = K * d * ∑ k ∈ Finset.Ico N n, r k := by rw [Finset.mul_sum]
      _ ≤ K * d * ∑' k, r (k + N) := mul_le_mul_of_nonneg_left (D.sum_Ico_le N n) hKd
  · have hj' : rec j = false := by simpa using hj
    have hsa := D.dom_summable j hj' N hN z C hzC n hn
    have hsb := D.dom_summable j hj' N hN z' C hz'C n hn
    rw [neg_sub_neg, ← hsb.tsum_sub hsa]
    have hs : Summable (fun k => ‖gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1) -
        gg M lam i (z' (k + n)) (k + n) j / PP lam i j n (k + n + 1)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (D.dom_term_sub_le j hj' N hN z z' d hz n hn)
        ((D.tail_summable n).mul_left (K * d))
    rw [show (∑' k, (gg M lam i (z' (k + n)) (k + n) j / PP lam i j n (k + n + 1) -
        gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1))) =
        -∑' k, (gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1) -
        gg M lam i (z' (k + n)) (k + n) j / PP lam i j n (k + n + 1)) by
          rw [← tsum_neg]; congr 1; funext k; ring, norm_neg]
    calc ‖∑' k, (gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1) -
          gg M lam i (z' (k + n)) (k + n) j / PP lam i j n (k + n + 1))‖
        ≤ ∑' k, K * d * r (k + n) :=
          (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
            (D.dom_term_sub_le j hj' N hN z z' d hz n hn) ((D.tail_summable n).mul_left (K * d)))
      _ = K * d * ∑' k, r (k + n) := tsum_mul_left
      _ ≤ K * d * ∑' k, r (k + N) := mul_le_mul_of_nonneg_left (D.tail_mono N n hn) hKd
  · rw [sub_self, norm_zero]
    exact mul_nonneg hKd htail0

/-! ### The fixed point -/

/-- Bounded sequences `ℕ → (Fin 3 → ℂ)`. -/
abbrev BSeq := BoundedContinuousFunction ℕ (Fin 3 → ℂ)

/-- The Levinson operator on bounded sequences. -/
def LevData.Top (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N) (z : BSeq) : BSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun n => fun j => TT M lam i rec N z n j)
    continuous_of_discreteTopology (K * (1 + ‖z‖) * ∑' k, r (k + N))
    (fun n => D.TT_norm_le N hN z ‖z‖ (norm_nonneg _) (fun k => z.norm_coe_le_norm k) n)

theorem LevData.Top_apply (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N) (z : BSeq)
    (n : ℕ) (j : Fin 3) : D.Top N hN z n j = TT M lam i rec N z n j := rfl

theorem LevData.Top_dist (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (htail : ∑' k, r (k + N) ≤ 1 / (4 * K)) (z z' : BSeq) :
    dist (D.Top N hN z) (D.Top N hN z') ≤ (1 / 2 : ℝ) * dist z z' := by
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro n
  rw [dist_eq_norm]
  have h := D.TT_lip N hN z z' (max ‖z‖ ‖z'‖)
    (fun k => (z.norm_coe_le_norm k).trans (le_max_left _ _))
    (fun k => (z'.norm_coe_le_norm k).trans (le_max_right _ _)) (dist z z')
    (fun k => by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist k) n
  refine le_trans h ?_
  have hKpos : 0 < K := by linarith [D.hK]
  have hKt : K * ∑' k, r (k + N) ≤ 1 / 4 := by
    calc K * ∑' k, r (k + N) ≤ K * (1 / (4 * K)) := mul_le_mul_of_nonneg_left htail hKpos.le
      _ = 1 / 4 := by field_simp
  have hd : 0 ≤ dist z z' := dist_nonneg
  nlinarith

theorem LevData.exists_fixed (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (htail : ∑' k, r (k + N) ≤ 1 / (4 * K)) :
    ∃ z : BSeq, ∀ n j, z n j = TT M lam i rec N z n j := by
  have hc : ContractingWith (1 / 2 : NNReal) (D.Top N hN) :=
    ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' => by
      simpa using D.Top_dist N hN htail z z'⟩
  refine ⟨ContractingWith.fixedPoint _ hc, fun n j => ?_⟩
  have h := hc.fixedPoint_isFixedPt
  exact (congrFun (congrFun (congrArg DFunLike.coe h) n) j).symm

/-! ### The recurrence satisfied by the fixed point -/

theorem LevData.rec_step (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (z : ℕ → Fin 3 → ℂ) (C : ℝ) (hz : ∀ k, ‖z k‖ ≤ C)
    (hfix : ∀ n j, z n j = TT M lam i rec N z n j) (n : ℕ) (hn : N ≤ n) (j : Fin 3) :
    z (n + 1) j = qq lam i j n * z n j + gg M lam i (z n) n j := by
  rw [hfix (n + 1) j, hfix n j]
  unfold TT
  rw [if_pos (by omega : N ≤ n + 1), if_pos hn]
  by_cases hj : rec j = true
  · rw [if_pos hj, if_pos hj, Finset.sum_Ico_succ_top hn, PP_self, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [PP_succ_top lam i j (k + 1) n (by omega)]
    ring
  · rw [if_neg hj, if_neg hj]
    have hj' : rec j = false := by simpa using hj
    have hs := D.dom_summable j hj' N hN z C hz n hn
    have h1 : ∀ k, qq lam i j n * (gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1)) =
        gg M lam i (z (k + n)) (k + n) j / PP lam i j (n + 1) (k + n + 1) := by
      intro k
      rw [PP_succ_bot lam i j n (k + n + 1) (by omega)]
      have hq : qq lam i j n ≠ 0 := div_ne_zero (D.hlam j n (by omega)) (D.hlam i n (by omega))
      field_simp
    have hs' : Summable (fun k => gg M lam i (z (k + n)) (k + n) j /
        PP lam i j (n + 1) (k + n + 1)) := (hs.mul_left (qq lam i j n)).congr h1
    rw [mul_neg, ← tsum_mul_left, tsum_congr h1, hs'.tsum_eq_zero_add]
    rw [zero_add, PP_self, div_one]
    have h2 : ∀ k, gg M lam i (z (k + 1 + n)) (k + 1 + n) j / PP lam i j (n + 1) (k + 1 + n + 1) =
        gg M lam i (z (k + (n + 1))) (k + (n + 1)) j / PP lam i j (n + 1) (k + (n + 1) + 1) := by
      intro k
      rw [show k + 1 + n = k + (n + 1) by omega]
    rw [tsum_congr h2]
    ring

/-! ### Decay of the fixed point -/

theorem LevData.tail_tendsto (D : LevData M lam i rec N₀ K r) :
    Tendsto (fun m => ∑' k, r (k + m)) atTop (𝓝 0) := tendsto_sum_nat_add r

theorem LevData.fixed_tendsto_zero (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (z : ℕ → Fin 3 → ℂ) (C : ℝ) (hC : 0 ≤ C) (hz : ∀ k, ‖z k‖ ≤ C)
    (hfix : ∀ n j, z n j = TT M lam i rec N z n j) : Tendsto z atTop (𝓝 0) := by
  have hKC : 0 ≤ K * (1 + C) := mul_nonneg (by linarith [D.hK]) (by linarith)
  have htt : Tendsto (fun m => K * (1 + C) * ∑' k, r (k + m)) atTop (𝓝 0) := by
    have := D.tail_tendsto.const_mul (K * (1 + C))
    rwa [mul_zero] at this
  refine tendsto_pi_nhds.mpr fun j => ?_
  rw [Pi.zero_apply]
  by_cases hj : rec j = true
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.mp htt) (ε / 2) (by positivity)
    set m' := max m N with hm'
    have hfin : Tendsto (fun n => ∑ k ∈ Finset.Ico N m',
        PP lam i j (k + 1) n * gg M lam i (z k) k j) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.Ico N m') fun k (hk : k ∈ Finset.Ico N m') =>
        (D.hrec0 j hj (k + 1) (by rw [Finset.mem_Ico] at hk; omega)).mul_const
          (gg M lam i (z k) k j)
      simpa using h
    obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.mp hfin) (ε / 2) (by positivity)
    refine ⟨max n₀ m', fun n hn => ?_⟩
    rw [dist_zero_right, hfix n j, TT, if_pos (by omega), if_pos hj,
      ← Finset.sum_Ico_consecutive _ (le_max_right m N) (by omega : m' ≤ n)]
    have hA := hn₀ n (by omega)
    rw [dist_zero_right] at hA
    have hB : ‖∑ k ∈ Finset.Ico m' n, PP lam i j (k + 1) n * gg M lam i (z k) k j‖ ≤
        K * (1 + C) * ∑' k, r (k + m') := by
      calc ‖∑ k ∈ Finset.Ico m' n, PP lam i j (k + 1) n * gg M lam i (z k) k j‖
          ≤ ∑ k ∈ Finset.Ico m' n, K * (1 + C) * r k := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            rw [Finset.mem_Ico] at hk
            rw [norm_mul]
            have h1 := D.hrecK j hj (k + 1) n (by omega) (by omega)
            have h2 : ‖gg M lam i (z k) k j‖ ≤ (1 + C) * r k :=
              (norm_le_pi_norm _ j).trans ((gg_norm_le M lam i r k (D.hlam i k (by omega))
                (D.hR k (by omega)) (z k)).trans
                (mul_le_mul_of_nonneg_right (add_le_add_right (hz k) 1) (D.hr0 _)))
            calc ‖PP lam i j (k + 1) n‖ * ‖gg M lam i (z k) k j‖ ≤ K * ((1 + C) * r k) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (by linarith [D.hK])
              _ = K * (1 + C) * r k := by ring
        _ = K * (1 + C) * ∑ k ∈ Finset.Ico m' n, r k := by rw [Finset.mul_sum]
        _ ≤ K * (1 + C) * ∑' k, r (k + m') := mul_le_mul_of_nonneg_left (D.sum_Ico_le m' n) hKC
    have hm1 := hm m' (le_max_left m N)
    rw [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hKC (tsum_nonneg fun _ => D.hr0 _))] at hm1
    calc ‖_ + _‖ ≤ ‖∑ k ∈ Finset.Ico N m', PP lam i j (k + 1) n * gg M lam i (z k) k j‖ +
          ‖∑ k ∈ Finset.Ico m' n, PP lam i j (k + 1) n * gg M lam i (z k) k j‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hA (hB.trans hm1.le)
      _ = ε := by ring
  · have hj' : rec j = false := by simpa using hj
    refine squeeze_zero_norm' ?_ htt
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hfix n j, TT, if_pos hn, if_neg hj, norm_neg]
    have hs : Summable (fun k => ‖gg M lam i (z (k + n)) (k + n) j /
        PP lam i j n (k + n + 1)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (D.dom_term_le j hj' N hN z C hz n hn)
        ((D.tail_summable n).mul_left (K * (1 + C)))
    calc ‖∑' k, gg M lam i (z (k + n)) (k + n) j / PP lam i j n (k + n + 1)‖
        ≤ ∑' k, K * (1 + C) * r (k + n) :=
          (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
            (D.dom_term_le j hj' N hN z C hz n hn) ((D.tail_summable n).mul_left (K * (1 + C))))
      _ = K * (1 + C) * ∑' k, r (k + n) := tsum_mul_left

/-! ### The solution -/

/-- **Levinson's theorem** (one mode). -/
theorem LevData.exists_solution (D : LevData M lam i rec N₀ K r) (N : ℕ) (hN : N₀ ≤ N)
    (htail : ∑' k, r (k + N) ≤ 1 / (4 * K)) :
    ∃ x z : ℕ → Fin 3 → ℂ, (∀ n, N ≤ n → x (n + 1) = x n ᵥ* M n) ∧
      (∀ n, x n = (∏ m ∈ Finset.Ico N n, lam i m) • (Pi.single i 1 + z n)) ∧
      Tendsto z atTop (𝓝 0) := by
  obtain ⟨zb, hfix⟩ := D.exists_fixed N hN htail
  have hzC : ∀ k, ‖zb k‖ ≤ ‖zb‖ := fun k => zb.norm_coe_le_norm k
  have hrec := D.rec_step N hN zb ‖zb‖ hzC hfix
  refine ⟨fun n => (∏ m ∈ Finset.Ico N n, lam i m) • (Pi.single i 1 + zb n), fun n => zb n,
    fun n hn => ?_, fun n => rfl, D.fixed_tendsto_zero N hN zb ‖zb‖ (norm_nonneg _) hzC hfix⟩
  funext j
  show ((∏ m ∈ Finset.Ico N (n + 1), lam i m) • (Pi.single i 1 + zb (n + 1)) : Fin 3 → ℂ) j =
    (((∏ m ∈ Finset.Ico N n, lam i m) • (Pi.single i 1 + zb n) : Fin 3 → ℂ) ᵥ* M n) j
  have hlam0 := D.hlam i n (by omega)
  have hM : M n = Matrix.diagonal (fun j => lam j n) + RR M lam n := by
    unfold RR
    rw [add_sub_cancel]
  have hgg : (Pi.single i 1 + zb n) ᵥ* RR M lam n = lam i n • gg M lam i (zb n) n := by
    unfold gg
    rw [smul_smul, mul_inv_cancel₀ hlam0, one_smul]
  rw [Finset.prod_Ico_succ_top hn, hM, Matrix.smul_vecMul, Matrix.vecMul_add, hgg]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.vecMul_diagonal]
  rw [hrec n hn j]
  unfold qq
  by_cases hj : j = i
  · subst hj
    simp only [Pi.single_eq_same]
    field_simp
    ring
  · simp only [Pi.single_eq_of_ne hj]
    field_simp
    ring

end Pfq54.LV
