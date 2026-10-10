/-
# Auxiliary results (sorry-free)

General lemmas shared by several blueprint files. Everything here is fully proved.
They live in the namespace `ZetasIrr.Aux`.
-/
import cross_product_readout

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.Aux

/-! ### `f_p` and `ℓ_p` -/

theorem ellp_eq_log {p : ℕ} (hp : p.Prime) (m : ℤ) : ellp p m = Nat.log p m.toNat := by
  unfold ellp
  rw [← Nat.factorization_def _ hp]
  have := Nat.factorization_lcmUpto m.toNat hp
  rw [Nat.lcmUpto] at this
  rw [this]

theorem ellp_nonneg (p : ℕ) (m : ℤ) : 0 ≤ ellp p m := by
  unfold ellp; positivity

theorem ellp_mono {p : ℕ} (hp : p.Prime) {a b : ℤ} (hab : a ≤ b) : ellp p a ≤ ellp p b := by
  rw [ellp_eq_log hp, ellp_eq_log hp]
  exact_mod_cast Nat.log_mono_right (Int.toNat_le_toNat hab)

theorem ellp_eq_zero_of_lt {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : m < p) : ellp p m = 0 := by
  rw [ellp_eq_log hp]
  have := hp.two_le
  have : m.toNat < p := by omega
  simp [Nat.log_of_lt this]

theorem fp_eq_zero_of_lt {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : m < p) : fp p m = 0 := by
  unfold fp
  have := hp.two_le
  have : m.toNat < p := by omega
  have hnd : ¬ p ∣ m.toNat.factorial := fun h => by
    have := (Nat.Prime.dvd_factorial hp).mp h; omega
  simp [padicValNat.eq_zero_of_not_dvd hnd]

theorem maxOn_le (s : Finset ℤ) (f : ℤ → ℤ) (c : ℤ) (hc : 0 ≤ c) (h : ∀ k ∈ s, f k ≤ c) :
    maxOn s f ≤ c := by
  unfold maxOn
  split_ifs with hs
  · exact Finset.sup'_le hs f h
  · exact hc

theorem maxOn_congr_zero (s : Finset ℤ) (f : ℤ → ℤ) (h : ∀ k ∈ s, f k = 0) : maxOn s f = 0 := by
  unfold maxOn
  split_ifs with hs
  · apply le_antisymm
    · exact Finset.sup'_le hs f fun k hk => (h k hk).le
    · obtain ⟨k, hk⟩ := hs
      exact (h k hk).symm.le.trans (Finset.le_sup' f hk)
  · rfl


/-! ### `p`-adic valuation bounds -/

/-- `x = 0` or `v_p(x) ≥ k`. -/
def ValGE (p : ℕ) (k : ℤ) (x : ℚ) : Prop := x = 0 ∨ k ≤ padicValRat p x

section ValGE

variable {p : ℕ} [Fact p.Prime]

theorem ValGE.mul {a b : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p b y) :
    ValGE p (a + b) (x * y) := by
  rcases hx with rfl | hx
  · left; simp
  rcases hy with rfl | hy
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  by_cases hy0 : y = 0
  · left; simp [hy0]
  right; rw [padicValRat.mul hx0 hy0]; omega

theorem ValGE.neg {a : ℤ} {x : ℚ} (hx : ValGE p a x) : ValGE p a (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [padicValRat.neg]

theorem ValGE.add {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem ValGE.sub {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem ValGE.mono {a b : ℤ} (hab : b ≤ a) {x : ℚ} (hx : ValGE p a x) : ValGE p b x :=
  hx.imp id fun h => hab.trans h

theorem ValGE.cross {a b : ℤ} {u v : Fin 3 → ℚ} (hu : ∀ i, ValGE p a (u i))
    (hv : ∀ i, ValGE p b (v i)) (j : Fin 3) : ValGE p (a + b) (crossProduct u v j) := by
  fin_cases j <;> simp only [cross_apply] <;>
    exact ((hu _).mul (hv _)).sub ((hu _).mul (hv _))

end ValGE

theorem padicValRat_factorial_prod (p : ℕ) [Fact p.Prime] (l : List ℕ) (g : ℕ → ℕ) :
    padicValRat p ((l.map fun r => ((g r).factorial : ℚ)).prod) =
      (l.map fun r => (padicValNat p (g r).factorial : ℤ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons,
      padicValRat.mul (by positivity) (List.prod_ne_zero (by simp [Nat.factorial_ne_zero])), ih,
      padicValRat.of_nat]


/-! ### Estimates for prime sums -/

theorem padicValNat_six_mul_log_le {p : ℕ} (hp : p.Prime) :
    (padicValNat p 6 : ℝ) * Real.log p ≤ Real.log 6 := by
  have hle : p ^ padicValNat p 6 ≤ 6 := Nat.le_of_dvd (by norm_num) pow_padicValNat_dvd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast hle)

theorem ellp_mul_log_le {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) :
    (ellp p (m : ℤ) : ℝ) * Real.log p ≤ Real.log m := by
  rw [ellp_eq_log hp, Int.toNat_natCast]
  push_cast
  rw [← Real.log_pow]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self p (by omega))

/-- The per-prime bound `E · log p ≤ log 6 + 6 log(29N+1)` for `E ≤ max(v_p(6), 6ℓ_p(29N+1))`. -/
theorem toNat_mul_log_le {p : ℕ} (hp : p.Prime) (N : ℕ) (E : ℤ)
    (hE : E ≤ max (padicValNat p 6 : ℤ) (6 * ellp p (29 * (N : ℤ) + 1))) :
    (E.toNat : ℝ) * Real.log p ≤ Real.log 6 + 6 * Real.log (29 * N + 1) := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have h6 := padicValNat_six_mul_log_le hp
  have hl := ellp_mul_log_le hp (29 * N + 1) (by omega)
  have hl0 := ellp_nonneg p ((29 * N + 1 : ℕ) : ℤ)
  have hcast : (29 * (N : ℤ) + 1) = ((29 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast] at hE
  generalize ellp p ((29 * N + 1 : ℕ) : ℤ) = L at hE hl hl0
  generalize padicValNat p 6 = v at hE h6
  have hE' : (E.toNat : ℤ) ≤ (v : ℤ) + 6 * L := by rw [Int.toNat_eq_max]; omega
  have hE'' : (E.toNat : ℝ) ≤ (v : ℝ) + 6 * (L : ℝ) := by exact_mod_cast hE'
  have hl' : (L : ℝ) * Real.log p ≤ Real.log (29 * N + 1) := by push_cast at hl; exact hl
  calc (E.toNat : ℝ) * Real.log p ≤ ((v : ℝ) + 6 * (L : ℝ)) * Real.log p :=
        mul_le_mul_of_nonneg_right hE'' hlogp
    _ = (v : ℝ) * Real.log p + 6 * ((L : ℝ) * Real.log p) := by ring
    _ ≤ Real.log 6 + 6 * Real.log (29 * N + 1) := by linarith

open Asymptotics in
theorem tendsto_norm_sqrt_nat : Tendsto (fun N : ℕ => ‖Real.sqrt N‖) atTop atTop := by
  have : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine this.congr' (Eventually.of_forall fun N => ?_)
  simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

open Asymptotics in
theorem sqrt_affine_isBigO (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun N : ℕ => Real.sqrt (a * N + b)) =O[atTop] fun N : ℕ => Real.sqrt N := by
  refine IsBigO.of_bound (Real.sqrt (a + b)) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_mul (by linarith)]
  exact Real.sqrt_le_sqrt (by nlinarith)

open Asymptotics in
theorem log_affine_isLittleO (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (fun N : ℕ => Real.log (a * N + b)) =o[atTop] fun N : ℕ => Real.sqrt N := by
  have ht : Tendsto (fun N : ℕ => a * (N : ℝ) + b) atTop atTop :=
    tendsto_atTop_add_const_right _ b (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto ht
  refine h1.trans_isBigO ?_
  refine (sqrt_affine_isBigO a b ha.le hb).congr' (Eventually.of_forall fun N => ?_) EventuallyEq.rfl
  simp only [Function.comp]
  rw [Real.sqrt_eq_rpow]

open Asymptotics in
theorem log_six_add_isLittleO :
    (fun N : ℕ => Real.log 6 + 6 * Real.log (29 * N + 1)) =o[atTop] fun N : ℕ => Real.sqrt N := by
  refine IsLittleO.add ?_ ((log_affine_isLittleO 29 1 (by norm_num) (by norm_num)).const_mul_left 6)
  exact isLittleO_const_left.mpr (Or.inr tendsto_norm_sqrt_nat)

open Asymptotics in
theorem sqrt_mul_sqrt_congr {f : ℕ → ℝ} (h : f =o[atTop] fun N : ℕ => Real.sqrt N * Real.sqrt N) :
    f =o[atTop] fun N : ℕ => (N : ℝ) :=
  h.congr_right fun N => Real.mul_self_sqrt (Nat.cast_nonneg N)

open Asymptotics in
/-- `(√(30N+10) + 1)(log 6 + 6 log(29N+1)) = o(N)`. -/
theorem small_bound_isLittleO :
    (fun N : ℕ => (Real.sqrt (30 * N + 10) + 1) * (Real.log 6 + 6 * Real.log (29 * N + 1)))
      =o[atTop] fun N : ℕ => (N : ℝ) := by
  have h1 : (fun N : ℕ => Real.sqrt (30 * N + 10) + 1) =O[atTop] fun N : ℕ => Real.sqrt N := by
    refine (sqrt_affine_isBigO 30 10 (by norm_num) (by norm_num)).add ?_
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
    simp [abs_of_nonneg (Real.sqrt_nonneg _), this]
  exact sqrt_mul_sqrt_congr (h1.mul_isLittleO log_six_add_isLittleO)

open Asymptotics in
/-- `log(29N+10) (log 6 + 6 log(29N+1)) = o(N)`. -/
theorem log_bound_isLittleO :
    (fun N : ℕ => Real.log (29 * N + 10) * (Real.log 6 + 6 * Real.log (29 * N + 1)))
      =o[atTop] fun N : ℕ => (N : ℝ) :=
  sqrt_mul_sqrt_congr ((log_affine_isLittleO 29 10 (by norm_num) (by norm_num)).mul
    log_six_add_isLittleO)

/-! ### Derivatives and values of rational functions -/

theorem algebraMap_ne_zero' {p : ℚ[X]} (hp : p ≠ 0) : algebraMap ℚ[X] ℚ⟮X⟯ p ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] ℚ⟮X⟯)).mpr hp

/-- `rfDeriv` does not depend on the representation of the fraction. -/
theorem rfDeriv_div (p q : ℚ[X]) (hq : q ≠ 0) :
    rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ p / algebraMap ℚ[X] ℚ⟮X⟯ q) =
      algebraMap ℚ[X] ℚ⟮X⟯ (derivative p * q - p * derivative q) /
        algebraMap ℚ[X] ℚ⟮X⟯ (q ^ 2) := by
  generalize hx : algebraMap ℚ[X] ℚ⟮X⟯ p / algebraMap ℚ[X] ℚ⟮X⟯ q = x
  have hrel : x.num * q = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hx.symm
  have hrel' := congrArg derivative hrel
  simp only [derivative_mul] at hrel'
  have hD : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have key : (derivative x.num * x.denom - x.num * derivative x.denom) * q ^ 2 =
      (derivative p * q - p * derivative q) * x.denom ^ 2 := by
    linear_combination (q * x.denom) * hrel' -
      (derivative x.denom * q + derivative q * x.denom) * hrel
  unfold rfDeriv
  rw [div_eq_div_iff (algebraMap_ne_zero' (pow_ne_zero 2 hD))
    (algebraMap_ne_zero' (pow_ne_zero 2 hq)), ← map_mul, ← map_mul, key]

/-- The value of `p/q` at a point where `q` does not vanish. -/
theorem rfEval_div (p q : ℚ[X]) (x : ℚ) (hq : q.eval x ≠ 0) :
    rfEval (algebraMap ℚ[X] ℚ⟮X⟯ p / algebraMap ℚ[X] ℚ⟮X⟯ q) x = p.eval x / q.eval x := by
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  set y := algebraMap ℚ[X] ℚ⟮X⟯ p / algebraMap ℚ[X] ℚ⟮X⟯ q with hy
  have hrel : y.num * q = p * y.denom := (RatFunc.num_mul_eq_mul_denom_iff hq0).mpr rfl
  have hD : y.denom.eval x ≠ 0 := by
    obtain ⟨k, hk⟩ := RatFunc.denom_div_dvd p q
    intro h; apply hq; rw [hk, eval_mul, h, zero_mul]
  show y.num.eval x / y.denom.eval x = p.eval x / q.eval x
  rw [div_eq_div_iff hD hq]
  have := congrArg (Polynomial.eval x) hrel
  simpa [eval_mul] using this

/-! ### General facts about `pfCoeff`, `polyPart`, `rfDeriv`, `Lfun`, `Mfun` -/


theorem taylor_X_sub_C_self (h : ℚ) : taylor h (Polynomial.X - Polynomial.C h) = Polynomial.X := by
  simp [Polynomial.taylor_X, Polynomial.taylor_C]

theorem coe_algebraMap_poly (p : ℚ[X]) :
    algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (algebraMap ℚ[X] ℚ⟮X⟯ p) = ((p : PowerSeries ℚ) : ℚ⸨X⸩) := by
  rw [RatFunc.coe_coe, RatFunc.coePolynomial_eq_algebraMap]

/-- Laurent coefficients vanish beyond the multiplicity of the pole. -/
theorem pfCoeff_eq_zero_of_rootMultiplicity_lt (f : ℚ⟮X⟯) (h : ℚ) (r : ℕ)
    (hr : f.denom.rootMultiplicity h < r) : pfCoeff f h r = 0 := by
  obtain ⟨E, hE, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.denom (RatFunc.denom_ne_zero f) h
  set m := f.denom.rootMultiplicity h with hm
  have hE0 : E.eval h ≠ 0 := fun h0 => hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
  have hden : taylor h f.denom = Polynomial.X ^ m * taylor h E := by
    rw [hE, Polynomial.taylor_mul, Polynomial.taylor_pow, taylor_X_sub_C_self]
  set Pn : PowerSeries ℚ := (taylor h f.num : PowerSeries ℚ) with hPn
  set Pe : PowerSeries ℚ := (taylor h E : PowerSeries ℚ) with hPe
  have hPe0 : PowerSeries.constantCoeff Pe ≠ 0 := by
    rw [hPe, Polynomial.constantCoeff_coe, Polynomial.taylor_coeff_zero]; exact hE0
  have hcoe : algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (RatFunc.laurent h f) =
      HahnSeries.single (-(m : ℤ)) 1 * ((Pn * Pe⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [RatFunc.laurent_div, map_div₀, coe_algebraMap_poly, coe_algebraMap_poly, hden,
      Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coe_mul,
      PowerSeries.coe_pow, PowerSeries.coe_X, PowerSeries.coe_mul]
    have hinv : ((Pe : ℚ⸨X⸩))⁻¹ = ((Pe⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel _ hPe0, PowerSeries.coe_one]
    rw [div_eq_mul_inv, mul_inv, hinv, HahnSeries.single_pow, one_pow, HahnSeries.inv_single]
    simp only [nsmul_eq_mul, mul_one, inv_one]
    ring
  unfold pfCoeff
  rw [hcoe, show -(r : ℤ) = (-(r : ℤ) + m) + -(m : ℤ) by ring, HahnSeries.coeff_single_mul_add,
    one_mul, PowerSeries.coeff_coe]
  split_ifs with hneg
  · rfl
  · exact absurd (by omega : -(r : ℤ) + m < 0) hneg

theorem pfCoeff_eq_zero_of_eval_ne_zero (f : ℚ⟮X⟯) (h : ℚ) (hh : f.denom.eval h ≠ 0) (r : ℕ)
    (hr : 1 ≤ r) : pfCoeff f h r = 0 :=
  pfCoeff_eq_zero_of_rootMultiplicity_lt f h r
    (by rw [Polynomial.rootMultiplicity_eq_zero (fun h0 => hh h0)]; omega)

theorem rootMultiplicity_le_natDegree' (p : ℚ[X]) (h : ℚ) : p.rootMultiplicity h ≤ p.natDegree := by
  classical
  rw [← Polynomial.count_roots]
  exact (Multiset.count_le_card _ _).trans (Polynomial.card_roots' p)

theorem pfCoeff_eq_zero_of_natDegree_lt (f : ℚ⟮X⟯) (h : ℚ) (r : ℕ)
    (hr : f.denom.natDegree < r) : pfCoeff f h r = 0 :=
  pfCoeff_eq_zero_of_rootMultiplicity_lt f h r
    (lt_of_le_of_lt (rootMultiplicity_le_natDegree' _ _) hr)

/-! ### The polynomial part -/

theorem DegLE_sub_polyPart (f : ℚ⟮X⟯) :
    DegLE (-1) (f - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f)) := by
  have hdiv := Polynomial.modByMonic_add_div f.num f.denom
  have hD' : algebraMap ℚ[X] ℚ⟮X⟯ f.denom ≠ 0 := algebraMap_ne_zero' (RatFunc.denom_ne_zero f)
  have heq : f - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f) =
      algebraMap ℚ[X] ℚ⟮X⟯ (f.num %ₘ f.denom) / algebraMap ℚ[X] ℚ⟮X⟯ f.denom := by
    calc f - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f)
        = algebraMap ℚ[X] ℚ⟮X⟯ f.num / algebraMap ℚ[X] ℚ⟮X⟯ f.denom -
            algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f) := by rw [RatFunc.num_div_denom]
      _ = _ := by
        rw [eq_div_iff hD', sub_mul, div_mul_cancel₀ _ hD', ← map_mul, ← map_sub, polyPart]
        congr 1
        linear_combination (-1 : ℚ[X]) * hdiv
  rw [heq]
  by_cases hR : f.num %ₘ f.denom = 0
  · left; simp [hR]
  right
  have hD1 : f.denom ≠ 1 := fun h1 => hR (by rw [h1, Polynomial.modByMonic_one])
  have := Polynomial.natDegree_modByMonic_lt f.num (RatFunc.monic_denom f) hD1
  rw [RatFunc.intDegree_div (algebraMap_ne_zero' hR) hD', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  omega

theorem polyPart_eq_of (f : ℚ⟮X⟯) (P : ℚ[X]) (h : DegLE (-1) (f - algebraMap ℚ[X] ℚ⟮X⟯ P)) :
    polyPart f = P := by
  have hd : DegLE (-1) (algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f - P)) := by
    have := h.add (DegLE_sub_polyPart f).neg
    rwa [show f - algebraMap ℚ[X] ℚ⟮X⟯ P + -(f - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f)) =
      algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f - P) by rw [map_sub]; ring] at this
  rcases hd with h0 | h1
  · exact sub_eq_zero.mp ((map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] ℚ⟮X⟯)).mp h0)
  · rw [RatFunc.intDegree_polynomial] at h1; omega

theorem polyPart_add (f g : ℚ⟮X⟯) : polyPart (f + g) = polyPart f + polyPart g := by
  apply polyPart_eq_of
  have := (DegLE_sub_polyPart f).add (DegLE_sub_polyPart g)
  rwa [show f - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f) + (g - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart g)) =
    f + g - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f + polyPart g) by rw [map_add]; ring] at this

theorem polyPart_C_mul (k : ℚ) (f : ℚ⟮X⟯) :
    polyPart (RatFunc.C k * f) = Polynomial.C k * polyPart f := by
  apply polyPart_eq_of
  have := (DegLE_sub_polyPart f).C_mul k
  rwa [show RatFunc.C k * (f - algebraMap ℚ[X] ℚ⟮X⟯ (polyPart f)) =
    RatFunc.C k * f - algebraMap ℚ[X] ℚ⟮X⟯ (Polynomial.C k * polyPart f) by
      rw [map_mul, RatFunc.algebraMap_C]; ring] at this

theorem laurent_eq_div (c : ℚ) (f : ℚ⟮X⟯) :
    RatFunc.laurent c f = algebraMap ℚ[X] ℚ⟮X⟯ (taylor c f.num) /
      algebraMap ℚ[X] ℚ⟮X⟯ (taylor c f.denom) := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [RatFunc.laurent_div]

theorem intDegree_laurent (c : ℚ) (x : ℚ⟮X⟯) (hx : x ≠ 0) :
    (RatFunc.laurent c x).intDegree = x.intDegree := by
  have hn : x.num ≠ 0 := RatFunc.num_ne_zero hx
  rw [laurent_eq_div, RatFunc.intDegree_div
    (algebraMap_ne_zero' (mt (Polynomial.taylor_eq_zero c _).mp hn))
    (algebraMap_ne_zero' (mt (Polynomial.taylor_eq_zero c _).mp (RatFunc.denom_ne_zero x))),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, Polynomial.natDegree_taylor,
    Polynomial.natDegree_taylor]
  rfl

theorem DegLE_laurent {k : ℤ} (c : ℚ) {x : ℚ⟮X⟯} (hx : DegLE k x) :
    DegLE k (RatFunc.laurent c x) := by
  rcases hx with rfl | hx
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  right; rw [intDegree_laurent c x hx0]; exact hx

theorem laurent_algebraMap (c : ℚ) (P : ℚ[X]) :
    RatFunc.laurent c (algebraMap ℚ[X] ℚ⟮X⟯ P) = algebraMap ℚ[X] ℚ⟮X⟯ (taylor c P) :=
  RatFunc.laurent_algebraMap c P

theorem polyPart_laurent (c : ℚ) (f : ℚ⟮X⟯) :
    polyPart (RatFunc.laurent c f) = taylor c (polyPart f) := by
  apply polyPart_eq_of
  have := DegLE_laurent c (DegLE_sub_polyPart f)
  rwa [map_sub, laurent_algebraMap] at this

/-! ### Derivatives -/

theorem derivative_taylor (c : ℚ) (p : ℚ[X]) :
    derivative (taylor c p) = taylor c (derivative p) := by
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.derivative_comp]
  simp

theorem exists_eq_div (f : ℚ⟮X⟯) :
    ∃ a b : ℚ[X], b ≠ 0 ∧ f = algebraMap ℚ[X] ℚ⟮X⟯ a / algebraMap ℚ[X] ℚ⟮X⟯ b :=
  ⟨f.num, f.denom, RatFunc.denom_ne_zero f, (RatFunc.num_div_denom f).symm⟩

theorem rfDeriv_add (f g : ℚ⟮X⟯) : rfDeriv (f + g) = rfDeriv f + rfDeriv g := by
  obtain ⟨a, b, hb, rfl⟩ := exists_eq_div f
  obtain ⟨c, d, hd, rfl⟩ := exists_eq_div g
  have hb' := algebraMap_ne_zero' hb
  have hd' := algebraMap_ne_zero' hd
  rw [div_add_div _ _ hb' hd', ← map_mul, ← map_mul, ← map_mul, ← map_add,
    rfDeriv_div _ _ (mul_ne_zero hb hd), rfDeriv_div _ _ hb, rfDeriv_div _ _ hd,
    div_add_div _ _ (algebraMap_ne_zero' (pow_ne_zero 2 hb)) (algebraMap_ne_zero' (pow_ne_zero 2 hd)),
    div_eq_div_iff (algebraMap_ne_zero' (pow_ne_zero 2 (mul_ne_zero hb hd)))
      (mul_ne_zero (algebraMap_ne_zero' (pow_ne_zero 2 hb)) (algebraMap_ne_zero' (pow_ne_zero 2 hd)))]
  simp only [← map_mul, ← map_add]
  congr 1
  simp only [derivative_mul, derivative_add]
  ring

theorem rfDeriv_C_mul (k : ℚ) (f : ℚ⟮X⟯) : rfDeriv (RatFunc.C k * f) = RatFunc.C k * rfDeriv f := by
  obtain ⟨a, b, hb, rfl⟩ := exists_eq_div f
  rw [← RatFunc.algebraMap_C, ← mul_div_assoc, ← map_mul, rfDeriv_div _ _ hb, rfDeriv_div _ _ hb,
    ← mul_div_assoc, ← map_mul]
  congr 2
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem rfDeriv_laurent (c : ℚ) (f : ℚ⟮X⟯) :
    rfDeriv (RatFunc.laurent c f) = RatFunc.laurent c (rfDeriv f) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_eq_div f
  have htb : taylor c b ≠ 0 := mt (Polynomial.taylor_eq_zero c _).mp hb
  rw [RatFunc.laurent_div, rfDeriv_div _ _ htb, rfDeriv_div _ _ hb, RatFunc.laurent_div]
  simp only [map_sub, Polynomial.taylor_mul, Polynomial.taylor_pow, derivative_taylor]

/-! ### Bernoulli sums under translation -/

/-- `β_y(P) = ∑_m P_m B_m(y)`. -/
def bsum (y : ℚ) (P : ℚ[X]) : ℚ := P.sum fun m a => a * (Polynomial.bernoulli m).eval y

theorem bsum_eq_range (y : ℚ) (P : ℚ[X]) (M : ℕ) (hM : P.natDegree ≤ M) :
    bsum y P = ∑ m ∈ Finset.range (M + 1), P.coeff m * (Polynomial.bernoulli m).eval y :=
  Polynomial.sum_over_range' P (fun n => by simp) (M + 1) (by omega)

theorem bsum_add (y : ℚ) (P Q : ℚ[X]) : bsum y (P + Q) = bsum y P + bsum y Q :=
  Polynomial.sum_add_index P Q _ (fun n => by simp) (fun n a b => by ring)

theorem bsum_C_mul_X_add_one_pow (y : ℚ) (k : ℚ) (m : ℕ) :
    bsum y (Polynomial.C k * (Polynomial.X + Polynomial.C 1) ^ m) =
      k * (Polynomial.bernoulli m).eval (y + 1) := by
  rw [bsum_eq_range y _ m (by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [map_one]; exact (Polynomial.natDegree_pow_le).trans (by simp))]
  simp only [map_one, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  -- Appell: `B_m(y+1) = ∑_k C(m,k) B_k(y)`
  rcases m with _ | n
  · simp
  · have h1 := congrArg (Polynomial.eval y) (Polynomial.sum_bernoulli n)
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, Polynomial.eval_monomial,
      smul_eq_mul] at h1
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, h1, add_comm y 1,
      Polynomial.bernoulli_eval_one_add]
    push_cast
    ring

theorem bsum_taylor_one (y : ℚ) (P : ℚ[X]) : bsum y (taylor 1 P) = bsum (y + 1) P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, bsum_add, bsum_add, hp, hq]
  | monomial m k =>
    rw [Polynomial.taylor_monomial, bsum_C_mul_X_add_one_pow]
    unfold bsum
    rw [Polynomial.sum_monomial_index _ _ (by simp)]

theorem bsum_taylor_nat (y : ℚ) (n : ℕ) (P : ℚ[X]) : bsum y (taylor (n : ℚ) P) = bsum (y + n) P := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℚ) = 1 + n by push_cast; ring, ← Polynomial.taylor_taylor,
      bsum_taylor_one, ih]
    ring_nf

theorem bsum_taylor (y : ℚ) (c : ℤ) (P : ℚ[X]) : bsum y (taylor (c : ℚ) P) = bsum (y + c) P := by
  rcases Int.eq_nat_or_neg c with ⟨n, rfl | rfl⟩
  · exact_mod_cast bsum_taylor_nat y n P
  · have := bsum_taylor_nat (y - n) n (taylor (-(n : ℚ)) P)
    rw [Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero, sub_add_cancel] at this
    push_cast; rw [← this]; ring_nf

/-! ### `𝓛_K` and `𝓜_K`: general formula, linearity, translation -/

/-- `𝓛_K[f]` may be computed over any finite set `T` of points containing the poles and any
order bound `M ≥ deg(denom f)` (no splitting needed). -/
theorem Lfun_eq_general (K : ℤ) (f : ℚ⟮X⟯) (T : Finset ℚ) (hT : f.denom.roots.toFinset ⊆ T)
    (M : ℕ) (hM : f.denom.natDegree ≤ M) :
    Lfun K f = bsum ((K : ℚ) + 1) (polyPart f) • Zsym 0 +
      ∑ h ∈ T, ∑ r ∈ Finset.range (M + 1),
        ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0) := by
  unfold Lfun
  rw [bsum_eq_range _ _ _ le_rfl, Finset.sum_smul]
  congr 1
  calc ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.range (f.denom.natDegree + 1),
        ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0)
      = ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.range (M + 1),
        ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun r _ hr' => ?_
        have hr1 : f.denom.natDegree < r := by
          simp only [Finset.mem_range, not_lt] at hr'; omega
        simp [pfCoeff_eq_zero_of_natDegree_lt f h r hr1]
    _ = _ := by
        refine Finset.sum_subset hT fun h _ hh => Finset.sum_eq_zero fun r _ => ?_
        have hev : f.denom.eval h ≠ 0 := fun h0 => hh (Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (RatFunc.denom_ne_zero f)).mpr h0))
        rcases Nat.eq_zero_or_pos r with rfl | hpos
        · simp
        · simp [pfCoeff_eq_zero_of_eval_ne_zero f h hev r hpos]

theorem Lfun_add (K : ℤ) (f g : ℚ⟮X⟯) : Lfun K (f + g) = Lfun K f + Lfun K g := by
  set T := f.denom.roots.toFinset ∪ g.denom.roots.toFinset ∪ (f + g).denom.roots.toFinset
  set M := f.denom.natDegree + g.denom.natDegree + (f + g).denom.natDegree
  rw [Lfun_eq_general K (f + g) T Finset.subset_union_right M (by omega),
    Lfun_eq_general K f T (Finset.subset_union_left.trans Finset.subset_union_left) M (by omega),
    Lfun_eq_general K g T (Finset.subset_union_right.trans Finset.subset_union_left) M (by omega),
    polyPart_add, bsum_add]
  simp only [pfCoeff_add, mul_add, add_smul, Finset.sum_add_distrib]
  abel

theorem bsum_C_mul (y k : ℚ) (P : ℚ[X]) : bsum y (Polynomial.C k * P) = k * bsum y P := by
  rw [bsum_eq_range y _ P.natDegree ((Polynomial.natDegree_C_mul_le k P)),
    bsum_eq_range y P P.natDegree le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_C_mul]; ring

theorem Lfun_C_mul (K : ℤ) (k : ℚ) (f : ℚ⟮X⟯) : Lfun K (RatFunc.C k * f) = k • Lfun K f := by
  set T := f.denom.roots.toFinset ∪ (RatFunc.C k * f).denom.roots.toFinset
  set M := f.denom.natDegree + (RatFunc.C k * f).denom.natDegree
  rw [Lfun_eq_general K (RatFunc.C k * f) T Finset.subset_union_right M (by omega),
    Lfun_eq_general K f T Finset.subset_union_left M (by omega), polyPart_C_mul, bsum_C_mul,
    smul_add, smul_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_smul, pfCoeff_C_mul]
  congr 1; ring

theorem pfCoeff_laurent (c : ℚ) (f : ℚ⟮X⟯) (h : ℚ) (r : ℕ) :
    pfCoeff (RatFunc.laurent c f) h r = pfCoeff f (h + c) r := by
  unfold pfCoeff; rw [RatFunc.laurent_laurent]

theorem Lfun_laurent (K c : ℤ) (f : ℚ⟮X⟯) :
    Lfun K (RatFunc.laurent (c : ℚ) f) = Lfun (K + c) f := by
  set g := RatFunc.laurent (c : ℚ) f with hg
  set T := f.denom.roots.toFinset
  set M := f.denom.natDegree
  have htd : taylor (c : ℚ) f.denom ≠ 0 := mt (Polynomial.taylor_eq_zero _ _).mp
    (RatFunc.denom_ne_zero f)
  have hdvd : g.denom ∣ taylor (c : ℚ) f.denom := by
    rw [hg, laurent_eq_div]; exact RatFunc.denom_div_dvd _ _
  have hT : g.denom.roots.toFinset ⊆ T.image (fun h => h - c) := by
    intro x hx
    have hroot : g.denom.IsRoot x :=
      (Polynomial.mem_roots (RatFunc.denom_ne_zero g)).mp (Multiset.mem_toFinset.mp hx)
    have h2 : (taylor (c : ℚ) f.denom).eval x = 0 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Polynomial.eval_mul, hroot.eq_zero, zero_mul]
    rw [Polynomial.taylor_eval] at h2
    exact Finset.mem_image.mpr ⟨x + c, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (RatFunc.denom_ne_zero f)).mpr h2), by ring⟩
  have hM : g.denom.natDegree ≤ M := by
    have := Polynomial.natDegree_le_of_dvd hdvd htd
    rwa [Polynomial.natDegree_taylor] at this
  rw [Lfun_eq_general K g _ hT M hM, Lfun_eq_general (K + c) f T le_rfl M le_rfl, hg,
    polyPart_laurent, bsum_taylor]
  congr 1
  · push_cast; ring_nf
  · rw [Finset.sum_image fun a _ b _ hab => by simpa using hab]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun r _ => ?_
    rw [pfCoeff_laurent, sub_add_cancel]
    congr 4
    push_cast; ring_nf

theorem Mfun_add (K : ℤ) (f g : ℚ⟮X⟯) : Mfun K (f + g) = Mfun K f + Mfun K g := by
  unfold Mfun; rw [rfDeriv_add, Lfun_add, neg_add]

theorem Mfun_smul (K : ℤ) (k : ℚ) (f : ℚ⟮X⟯) : Mfun K (k • f) = k • Mfun K f := by
  unfold Mfun; rw [RatFunc.smul_eq_C_mul, rfDeriv_C_mul, Lfun_C_mul, smul_neg]

theorem Mfun_zero (K : ℤ) : Mfun K 0 = 0 := by
  have := Mfun_add K 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem Mfun_sum (K : ℤ) {ι : Type*} (s : Finset ι) (c : ι → ℚ) (f : ι → ℚ⟮X⟯) :
    Mfun K (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Mfun K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Mfun_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Mfun_add, Mfun_smul, ih]

theorem Mfun_laurent (K c : ℤ) (f : ℚ⟮X⟯) :
    Mfun K (RatFunc.laurent (c : ℚ) f) = Mfun (K + c) f := by
  unfold Mfun; rw [rfDeriv_laurent, Lfun_laurent]

theorem pfCoeff_algebraMap (P : ℚ[X]) (h : ℚ) (r : ℕ) (hr : 1 ≤ r) :
    pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ P) h r = 0 :=
  pfCoeff_eq_zero_of_eval_ne_zero _ h (by simp [RatFunc.denom_algebraMap]) r hr

/-- `𝓛_0` of `P + ∑_{k=1}^{4} c_k t^{-k}` (all poles at `0`). -/
theorem Lfun_zero_of_decomp (g : ℚ⟮X⟯) (hden : g.denom ∣ Polynomial.X ^ 4) (P : ℚ[X])
    (c : ℕ → ℚ)
    (hg : g = algebraMap ℚ[X] ℚ⟮X⟯ P +
      ∑ k ∈ Finset.Icc (1 : ℕ) 4, RatFunc.C (c k) * ((RatFunc.X - RatFunc.C 0) ^ k)⁻¹) :
    Lfun 0 g = bsum 1 P • Zsym 0 + ∑ k ∈ Finset.Icc (1 : ℕ) 4, ((k : ℚ) * c k) • Zsym (k + 1) := by
  have hX4 : (Polynomial.X ^ 4 : ℚ[X]) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hT : g.denom.roots.toFinset ⊆ {0} := by
    intro x hx
    have := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hX4 hden) (Multiset.mem_toFinset.mp hx)
    rw [Polynomial.roots_X_pow] at this
    exact Finset.mem_singleton.mpr (Multiset.mem_singleton.mp (Multiset.mem_of_mem_nsmul this))
  have hM : g.denom.natDegree ≤ 4 := by
    have := Polynomial.natDegree_le_of_dvd hden hX4
    simpa using this
  have hpoly : polyPart g = P := by
    apply polyPart_eq_of
    rw [hg, add_sub_cancel_left]
    exact DegLE.sum _ _ fun k hk =>
      (DegLE.basic 0 (c k) k).mono (by have := (Finset.mem_Icc.mp hk).1; omega)
  have hpf : ∀ k, 1 ≤ k → pfCoeff g 0 k = if k ≤ 4 then c k else 0 := by
    intro k hk
    rw [hg, pfCoeff_add, pfCoeff_algebraMap P 0 k hk, zero_add, pfCoeff_sum]
    simp only [pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hk, true_and, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 4) k c]
    simp [Finset.mem_Icc, hk]
  rw [Lfun_eq_general 0 g {0} hT 4 hM, hpoly, Finset.sum_singleton]
  push_cast
  rw [zero_add]
  congr 1
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hpf 1 (by norm_num),
    hpf 2 (by norm_num), hpf 3 (by norm_num), hpf 4 (by norm_num)]
  simp [harm]
  abel

end ZetasIrr.Aux
