/-
# Auxiliary lemmas for the forward `₅F₄` node blueprints (sorry-free)
-/
import Pfq54_defs

open Finset
open scoped Matrix

noncomputable section

namespace Pfq54.Aux

open Pfq54

theorem jet_fst (a a' : ℚ) : (jet a a').fst = a := add_zero a

theorem jet_snd (a a' : ℚ) : (jet a a').snd = a' := zero_add a'

theorem fst_prod {ι : Type*} (s : Finset ι) (f : ι → Jet) :
    (∏ i ∈ s, f i).fst = ∏ i ∈ s, (f i).fst :=
  map_prod (TrivSqZeroExt.fstHom ℚ ℚ ℚ) f s

theorem prod_Icc_10_12 {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ u ∈ Icc 10 12, f u = f 10 * f 11 * f 12 := by
  rw [show Icc 10 12 = {10, 11, 12} by decide, prod_insert (by decide), prod_insert (by decide),
    prod_singleton, mul_assoc]

theorem harm_succ (r m : ℕ) : harm r (m + 1) = harm r m + 1 / ((m + 1 : ℕ) : ℚ) ^ r := by
  unfold harm
  rw [sum_Icc_succ_top (Nat.le_add_left 1 m)]

/-- `H_N - H_{N-M} = ∑_{s<M} 1/(N-s)`. -/
theorem harm_sub (N M : ℕ) (h : M ≤ N) :
    harm 1 N - harm 1 (N - M) = ∑ s ∈ range M, 1 / ((N - s : ℕ) : ℚ) := by
  induction M with
  | zero => rw [Nat.sub_zero, sub_self, sum_range_zero]
  | succ M ih =>
    rw [sum_range_succ, ← ih (by omega)]
    have e : N - M = (N - (M + 1)) + 1 := by omega
    rw [e, harm_succ, pow_one, ← e]
    ring

theorem lcm_dvd_lcm {M L : ℕ} (h : M ≤ L) : (Icc 1 M).lcm id ∣ (Icc 1 L).lcm id :=
  Finset.lcm_mono (Finset.Icc_subset_Icc le_rfl h)

/-- `k · C(n,k)` divides `lcm(1,…,n)` for `1 ≤ k ≤ n` (Kummer). -/
theorem mul_choose_dvd_lcm {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * n.choose k ∣ (Icc 1 n).lcm id := by
  have hc := (Nat.choose_pos hkn).ne'
  rw [show (Icc 1 n).lcm id = Nat.lcmUpto n from rfl,
    ← Nat.factorization_prime_le_iff_dvd (Nat.mul_ne_zero (by omega) hc)
      (Nat.lcmUpto_ne_zero n)]
  intro p hp
  rw [Nat.factorization_lcmUpto n hp, Nat.factorization_mul (by omega) hc,
    Finsupp.add_apply]
  have hdisj : Disjoint {i ∈ Ico 1 (Nat.log p n).succ | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}
      {i ∈ Ico 1 (Nat.log p n).succ | p ^ i ∣ k} := by
    simp +contextual [Finset.disjoint_right, Nat.dvd_iff_mod_eq_zero,
      Nat.mod_lt _ (pow_pos hp.pos _)]
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _),
    Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega)
      (lt_of_le_of_lt hkn (Nat.lt_pow_succ_log_self hp.one_lt n)),
    add_comm, ← card_union_of_disjoint hdisj, filter_union_right]
  exact (card_filter_le _ _).trans_eq (Nat.card_Ico _ _)

/-- `d_L · M!(r-1)!/(M+r)! ∈ ℤ` for `r ≥ 1`, `M + r ≤ L`. -/
theorem lcm_mul_inv_choose (M r L : ℕ) (hr : 1 ≤ r) (hL : M + r ≤ L) :
    ∃ z : ℤ, (((Icc 1 L).lcm id : ℕ) : ℚ) *
      ((M.factorial : ℚ) * (r - 1).factorial / (M + r).factorial) = z := by
  have hdvd : r * (M + r).choose r ∣ (Icc 1 L).lcm id :=
    (mul_choose_dvd_lcm hr (by omega)).trans (lcm_dvd_lcm hL)
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, ?_⟩
  have hf : (M + r).factorial = r * (M + r).choose r * ((r - 1).factorial * M.factorial) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left r M)
    rw [Nat.add_sub_cancel] at h1
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [← h1, Nat.factorial_succ, Nat.add_sub_cancel]
    ring
  rw [hq, hf]
  push_cast
  have h1 : ((r - 1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (M.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (r : ℚ) * ((M + r).choose r : ℚ) ≠ 0 := by
    have : 0 < r * (M + r).choose r := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    exact_mod_cast this.ne'
  have h4 : ((M + r).choose r : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp

/-- `d_M^r H^{(r)}_m ∈ ℤ` for `m ≤ M`. -/
theorem harm_int (r m M : ℕ) (h : m ≤ M) :
    ∃ z : ℤ, (((Icc 1 M).lcm id : ℕ) : ℚ) ^ r * harm r m = z := by
  set L := (Icc 1 M).lcm id
  have hdiv : ∀ k ∈ Icc 1 m, k ∣ L := fun k hk => by
    have : k ∈ Icc 1 M := by simp only [Finset.mem_Icc] at hk ⊢; omega
    simpa using Finset.dvd_lcm (f := id) this
  refine ⟨∑ k ∈ Icc 1 m, ((L / k : ℕ) : ℤ) ^ r, ?_⟩
  rw [harm, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [Nat.cast_div (hdiv k hk) hk0, div_pow, mul_one_div]

theorem walk_zero {k : ℕ} {R : Type*} [CommRing R] (M : ℕ → Matrix (Fin k) (Fin k) R) :
    walk M 0 = 1 := by
  simp [walk]

theorem walk_succ {k : ℕ} {R : Type*} [CommRing R] (M : ℕ → Matrix (Fin k) (Fin k) R) (n : ℕ) :
    walk M (n + 1) = walk M n * M n := by
  simp [walk, List.range_succ]

theorem walk_last_row (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (hblock : ∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0) (n : ℕ) (j : Fin 4) :
    walk G n 3 j = if j = 3 then (-1) ^ n else 0 := by
  induction n generalizing j with
  | zero => rw [walk_zero]; fin_cases j <;> rfl
  | succ n ih =>
    rw [walk_succ, Matrix.mul_apply, Fin.sum_univ_four, ih, ih, ih, ih, hblock n j]
    fin_cases j <;> simp [pow_succ]

theorem walk_topLeft (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (hblock : ∀ n (j : Fin 4), G n 3 j = if j = 3 then -1 else 0) (n : ℕ) :
    walk (fun m => (G m).submatrix Fin.castSucc Fin.castSucc) n =
      (walk G n).submatrix Fin.castSucc Fin.castSucc := by
  induction n with
  | zero =>
    rw [walk_zero, walk_zero]
    ext i j
    simp [Matrix.one_apply]
  | succ n ih =>
    rw [walk_succ, walk_succ, ih]
    ext i j
    rw [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    rw [show (Fin.last 3 : Fin 4) = 3 from rfl, hblock n,
      ite_eq_right (show Fin.castSucc j ≠ (3 : Fin 4) from (Fin.castSucc_lt_last j).ne),
      mul_zero, add_zero]
    rfl

theorem inv_topLeft (M : Matrix (Fin 4) (Fin 4) ℚ) (hM : M.det ≠ 0)
    (hrow : ∀ j : Fin 3, M 3 (Fin.castSucc j) = 0) :
    (M⁻¹).submatrix Fin.castSucc Fin.castSucc = (M.submatrix Fin.castSucc Fin.castSucc)⁻¹ := by
  have hMP : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have h33 : M 3 3 ≠ 0 := by
    intro h
    apply hM
    refine Matrix.det_eq_zero_of_row_eq_zero 3 fun j => ?_
    refine Fin.lastCases ?_ (fun j' => hrow j') j
    exact h
  have hP3 : ∀ j : Fin 3, M⁻¹ 3 (Fin.castSucc j) = 0 := by
    intro j
    have h := congrFun (congrFun hMP 3) (Fin.castSucc j)
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, show (Fin.last 3 : Fin 4) = 3 from rfl,
      Finset.sum_eq_zero (fun k _ => by rw [hrow k, zero_mul]), zero_add,
      Matrix.one_apply_ne (show (3 : Fin 4) ≠ Fin.castSucc j from (Fin.castSucc_lt_last j).ne')]
      at h
    exact (mul_eq_zero.mp h).resolve_left h33
  refine (Matrix.inv_eq_right_inv ?_).symm
  ext i j
  have h := congrFun (congrFun hMP (Fin.castSucc i)) (Fin.castSucc j)
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc, show (Fin.last 3 : Fin 4) = 3 from rfl, hP3 j,
    mul_zero, add_zero] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply]
  rw [h]
  simp only [Matrix.one_apply, Fin.castSucc_inj]

theorem walk_det_ne_zero (G : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (hG : ∀ n, (G n).det ≠ 0)
    (n : ℕ) : (walk G n).det ≠ 0 := by
  induction n with
  | zero => rw [walk_zero, Matrix.det_one]; exact one_ne_zero
  | succ n ih => rw [walk_succ, Matrix.det_mul]; exact mul_ne_zero ih (hG n)

theorem prod_Icc_8_12 {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ u ∈ Icc 8 12, f u = f 8 * f 9 * f 10 * f 11 * f 12 := by
  rw [show Icc 8 12 = {8, 9, 10, 11, 12} by decide, prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton]
  simp only [mul_assoc]

theorem tendsto_mulVec3 {A : ℕ → Matrix (Fin 3) (Fin 3) ℂ} {Y : Matrix (Fin 3) (Fin 3) ℂ}
    {v : ℕ → Fin 3 → ℂ} {w : Fin 3 → ℂ} (hA : Filter.Tendsto A Filter.atTop (nhds Y))
    (hv : Filter.Tendsto v Filter.atTop (nhds w)) :
    Filter.Tendsto (fun n => A n *ᵥ v n) Filter.atTop (nhds (Y *ᵥ w)) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact tendsto_finsetSum _ fun j _ =>
    ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i) j)).mul (tendsto_pi_nhds.mp hv j)

theorem tendsto_transpose3 {A : ℕ → Matrix (Fin 3) (Fin 3) ℂ} {Y : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : Filter.Tendsto A Filter.atTop (nhds Y)) :
    Filter.Tendsto (fun n => (A n)ᵀ) Filter.atTop (nhds Yᵀ) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA j) i

theorem pow_div_cube_le (x : ℝ) (hx : 1 / 2 ≤ x) (k : ℕ) (hk : k ≤ 3) : x ^ k / x ^ 3 ≤ 8 := by
  have hx0 : 0 < x := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h3 : x ^ 3 = x ^ k * x ^ (3 - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have h4 : (1 / 2 : ℝ) ^ 3 ≤ x ^ (3 - k) :=
    le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le 3 k))
      (pow_le_pow_left₀ (by norm_num) hx _)
  rw [h3]
  nlinarith [pow_pos hx0 k]

theorem one_add_sq_le_cosh_sq (t : ℝ) : 1 + t ^ 2 ≤ Real.cosh t ^ 2 := by
  rw [Real.cosh_sq]
  have : t ^ 2 ≤ Real.sinh t ^ 2 := by
    rcases le_total 0 t with h | h
    · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.mpr h) 2
    · have h' := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr h)
      rw [Real.sinh_neg] at h'
      nlinarith
  linarith

theorem sin_sq_add_nat_mul_pi (x : ℂ) (j : ℕ) :
    Complex.sin (x + j * Real.pi) ^ 2 = Complex.sin x ^ 2 := by
  induction j with
  | zero => rw [Nat.cast_zero, zero_mul, add_zero]
  | succ j ih => rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, Complex.sin_add_pi, neg_sq, ih]

theorem ii_of_bound {g h : ℝ → ℝ} (hg : Measurable g)
    (hh : IntervalIntegrable h MeasureTheory.volume 0 1)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ h x) : IntervalIntegrable g MeasureTheory.volume 0 1 := by
  refine hh.mono_fun' hg.aestronglyMeasurable ?_
  rw [Set.uIoc_of_le zero_le_one]
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
    (Filter.Eventually.of_forall fun x hx => ?_)
  show ‖g x‖ ≤ h x
  rw [Real.norm_eq_abs]
  exact hb x (Set.Ioc_subset_Icc_self hx)

theorem sm_param_int {α : Type*} [MeasurableSpace α] (F : α × ℝ → ℝ)
    (hF : MeasureTheory.StronglyMeasurable F) :
    MeasureTheory.StronglyMeasurable (fun a => ∫ r in (0 : ℝ)..1, F (a, r)) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact hF.integral_prod_right'

theorem beta_nat (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b =
      (a.factorial * b.factorial : ℝ) / (a + b + 1).factorial := by
  have hu : 0 < ((a : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have hv : 0 < ((b : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have hB : Complex.betaIntegral ((a : ℂ) + 1) ((b : ℂ) + 1) =
      ((∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [add_sub_cancel_right, Complex.cpow_natCast]
    push_cast
    rfl
  rw [hB, show ((a : ℂ) + 1) + ((b : ℂ) + 1) = ((a + b + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  have hf : ((a + b + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b : ℝ) : ℂ) =
      ((a.factorial : ℂ) * b.factorial) / (a + b + 1).factorial := by
    rw [eq_div_iff hf, mul_comm]; exact h.symm
  have h3 : ((∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b : ℝ) : ℂ) =
      (((a.factorial * b.factorial : ℝ) / (a + b + 1).factorial : ℝ) : ℂ) := by
    rw [h2]; push_cast; rfl
  exact_mod_cast h3

/-- Tangent-line bound for a function with antitone derivative (mean value theorem). -/
theorem tangent_le (f f' : ℝ → ℝ) {a b : ℝ} (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hanti : AntitoneOn f' (Set.Ioo a b))
    {x0 : ℝ} (hx0 : x0 ∈ Set.Ioo a b) {y : ℝ} (hy : y ∈ Set.Icc a b) :
    f y ≤ f x0 + f' x0 * (y - x0) := by
  rcases lt_trichotomy y x0 with h | h | h
  · obtain ⟨c, hc, hdc⟩ := exists_hasDerivAt_eq_slope f f' h
      (hcont.mono (Set.Icc_subset_Icc hy.1 hx0.2.le))
      (fun x hx => hderiv x ⟨lt_of_le_of_lt hy.1 hx.1, hx.2.trans hx0.2⟩)
    have hcx : f' x0 ≤ f' c := hanti ⟨lt_of_le_of_lt hy.1 hc.1, hc.2.trans hx0.2⟩ hx0 hc.2.le
    rw [hdc, le_div_iff₀ (by linarith)] at hcx
    linarith
  · rw [h, sub_self, mul_zero, add_zero]
  · obtain ⟨c, hc, hdc⟩ := exists_hasDerivAt_eq_slope f f' h
      (hcont.mono (Set.Icc_subset_Icc hx0.1.le hy.2))
      (fun x hx => hderiv x ⟨hx0.1.trans hx.1, lt_of_lt_of_le hx.2 hy.2⟩)
    have hcx : f' c ≤ f' x0 := hanti hx0 ⟨hx0.1.trans hc.1, lt_of_lt_of_le hc.2 hy.2⟩ hc.1.le
    rw [hdc, div_le_iff₀ (by linarith)] at hcx
    linarith

/-- Combining ten logarithms. -/
theorem log_ratio5 (a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (ha3 : 0 < a3) (ha4 : 0 < a4) (ha5 : 0 < a5) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hb4 : 0 < b4) (hb5 : 0 < b5) :
    Real.log a1 + Real.log a2 + Real.log a3 + Real.log a4 + Real.log a5 - Real.log b1 -
      Real.log b2 - Real.log b3 - Real.log b4 - Real.log b5 =
      Real.log (a1 * a2 * a3 * a4 * a5 / (b1 * b2 * b3 * b4 * b5)) := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

end Pfq54.Aux
