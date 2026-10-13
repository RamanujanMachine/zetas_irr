import mc_aux1
import pf_aux
import cross_product_readout

open Filter Topology MeasureTheory Set intervalIntegral Polynomial
open scoped RatFunc LaurentSeries Matrix
open Complex (I)

noncomputable section

namespace Pfq54.MC

open Pfq54 Pfq54.MI ZetasIrr ZetasIrr.CMF

/-! ### Complex evaluation of rational functions -/

def cEval (f : ℚ⟮X⟯) (s : ℂ) : ℂ := RatFunc.eval (algebraMap ℚ ℂ) s f

theorem cEval_div (p q : ℚ[X]) (s : ℂ) (hq : q.eval₂ (algebraMap ℚ ℂ) s ≠ 0) :
    cEval (algebraMap ℚ[X] ℚ⟮X⟯ p / algebraMap ℚ[X] ℚ⟮X⟯ q) s =
      p.eval₂ (algebraMap ℚ ℂ) s / q.eval₂ (algebraMap ℚ ℂ) s := by
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  set y := algebraMap ℚ[X] ℚ⟮X⟯ p / algebraMap ℚ[X] ℚ⟮X⟯ q with hy
  have hrel : y.num * q = p * y.denom := (RatFunc.num_mul_eq_mul_denom_iff hq0).mpr rfl
  have hD : y.denom.eval₂ (algebraMap ℚ ℂ) s ≠ 0 := by
    obtain ⟨k, hk⟩ := RatFunc.denom_div_dvd p q
    intro h
    apply hq
    rw [hk, eval₂_mul, h, zero_mul]
  show y.num.eval₂ _ s / y.denom.eval₂ _ s = _
  rw [div_eq_div_iff hD hq]
  have := congrArg (Polynomial.eval₂ (algebraMap ℚ ℂ) s) hrel
  simpa [eval₂_mul] using this

theorem cEval_rat (f : ℚ⟮X⟯) (x : ℚ) : cEval f (x : ℂ) = ((rfEval f x : ℚ) : ℂ) := by
  unfold cEval rfEval RatFunc.eval
  rw [show (x : ℂ) = algebraMap ℚ ℂ x from rfl, eval₂_hom, eval₂_hom]
  show _ = ((Polynomial.eval x f.num / Polynomial.eval x f.denom : ℚ) : ℂ)
  rw [Rat.cast_div]
  rfl

theorem hasDerivAt_cEval (f : ℚ⟮X⟯) (s : ℂ) (hs : f.denom.eval₂ (algebraMap ℚ ℂ) s ≠ 0) :
    HasDerivAt (cEval f) (cEval (rfDeriv f) s) s := by
  have hfun : cEval f = fun s => (f.num.map (algebraMap ℚ ℂ)).eval s /
      (f.denom.map (algebraMap ℚ ℂ)).eval s := by
    funext s
    unfold cEval RatFunc.eval
    rw [eval₂_eq_eval_map, eval₂_eq_eval_map]
  have hs' : (f.denom.map (algebraMap ℚ ℂ)).eval s ≠ 0 := by rwa [← eval₂_eq_eval_map]
  have hd := ((f.num.map (algebraMap ℚ ℂ)).hasDerivAt s).div
    ((f.denom.map (algebraMap ℚ ℂ)).hasDerivAt s) hs'
  rw [hfun]
  refine hd.congr_deriv ?_
  rw [rfDeriv, cEval_div _ _ _ (by rw [eval₂_pow]; exact pow_ne_zero 2 hs)]
  simp only [eval₂_eq_eval_map, Polynomial.derivative_map, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, eval_sub, eval_mul, eval_pow]

/-! ### The kernel and its evaluation -/

def Rk (n k : ℕ) : ℚ⟮X⟯ := (-RatFunc.X) ^ k * Rker n

theorem Rk_eq (n k : ℕ) : Rk n k =
    algebraMap ℚ[X] ℚ⟮X⟯ ((-X) ^ k * Rnum n) / algebraMap ℚ[X] ℚ⟮X⟯ (Rden n) := by
  rw [Rk, Rker_eq, map_mul, map_pow, map_neg, RatFunc.algebraMap_X, mul_div_assoc]

def cpq (S : Multiset ℚ) (s : ℂ) : ℂ := (S.map fun z : ℚ => s - (z : ℂ)).prod

theorem eval₂_prod_X_sub_C (S : Multiset ℚ) (s : ℂ) :
    ((S.map fun a : ℚ => (X - C a : ℚ[X])).prod).eval₂ (algebraMap ℚ ℂ) s = cpq S s := by
  rw [eval₂_multiset_prod, Multiset.map_map, cpq]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [eval₂_sub, eval₂_X, eval₂_C]

theorem Rden_eval (n : ℕ) (s : ℂ) : (Rden n).eval₂ (algebraMap ℚ ℂ) s = cpq (poleSet n) s := by
  rw [Rden, den_eq, eval₂_prod_X_sub_C]

theorem Rnum_eval (n : ℕ) (s : ℂ) : (Rnum n).eval₂ (algebraMap ℚ ℂ) s = cpq (zeroSet n) s := by
  rw [Rnum, num_eq, eval₂_prod_X_sub_C]

theorem mem_poleSet (n : ℕ) (p : ℚ) (hp : p ∈ poleSet n) : ∃ m : ℕ, p = -(m : ℚ) := by
  simp only [poleSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at hp
  rcases hp with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩
  · exact ⟨i, by push_cast; ring⟩
  · exact ⟨n + i, by push_cast; ring⟩
  · exact ⟨2 * n + i, by push_cast; ring⟩

theorem poleSet_nonpos (n : ℕ) (p : ℚ) (hp : p ∈ poleSet n) : p ≤ 0 := by
  obtain ⟨m, rfl⟩ := mem_poleSet n p hp
  simp

theorem zeroSet_nonneg (n : ℕ) (z : ℚ) (hz : z ∈ zeroSet n) : 0 ≤ z := by
  simp only [zeroSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at hz
  rcases hz with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have : (i : ℚ) ≤ 15 * n := by exact_mod_cast hi.le
    linarith
  · have : (i : ℚ) ≤ 15 * n := by exact_mod_cast hi.le
    linarith

theorem card_poleSet (n : ℕ) : Multiset.card (poleSet n) = 30 * n + 4 := by
  simp [poleSet]
  ring

theorem card_zeroSet (n : ℕ) : Multiset.card (zeroSet n) = 30 * n := by
  simp [zeroSet]
  ring

/-! ### Bounds -/

theorem norm_le_norm_sub (s : ℂ) (p : ℚ) (hp : p ≤ 0) (hs : 0 ≤ s.re) : ‖s‖ ≤ ‖s - p‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ratCast_re, Complex.ratCast_im, sub_zero]
  have : (p : ℝ) ≤ 0 := by exact_mod_cast hp
  nlinarith

theorem cpq_lower (S : Multiset ℚ) (hS : ∀ p ∈ S, p ≤ 0) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖s‖ ^ Multiset.card S ≤ ‖cpq S s‖ := by
  induction S using Multiset.induction_on with
  | empty => simp [cpq]
  | cons p S ih =>
    rw [cpq, Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (norm_le_norm_sub s p (hS p (Multiset.mem_cons_self _ _)) hs)
      (ih fun q hq => hS q (Multiset.mem_cons_of_mem hq)) (by positivity) (norm_nonneg _)

theorem cpq_upper (S : Multiset ℚ) (hS : ∀ z ∈ S, 0 ≤ z) (s : ℂ) (hs : 1 / 2 ≤ ‖s‖) :
    ‖cpq S s‖ ≤ (S.map fun z : ℚ => (1 + 2 * z : ℝ)).prod * ‖s‖ ^ Multiset.card S := by
  induction S using Multiset.induction_on with
  | empty => simp [cpq]
  | cons z S ih =>
    have hz : (0 : ℝ) ≤ z := by exact_mod_cast hS z (Multiset.mem_cons_self _ _)
    have h1 : ‖s - (z : ℂ)‖ ≤ (1 + 2 * (z : ℝ)) * ‖s‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_ratCast, abs_of_nonneg hz]
      nlinarith
    rw [cpq, Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.map_cons,
      Multiset.prod_cons, Multiset.card_cons, pow_succ']
    calc ‖s - (z : ℂ)‖ * ‖(S.map fun z : ℚ => s - (z : ℂ)).prod‖
        ≤ ((1 + 2 * (z : ℝ)) * ‖s‖) *
          ((S.map fun z : ℚ => (1 + 2 * z : ℝ)).prod * ‖s‖ ^ Multiset.card S) :=
          mul_le_mul h1 (ih fun q hq => hS q (Multiset.mem_cons_of_mem hq)) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring

theorem cpq_pos (S : Multiset ℚ) (hS : ∀ p ∈ S, p ≤ 0) (s : ℂ) (hs : 0 < s.re) :
    0 < ‖cpq S s‖ := by
  have := cpq_lower S hS s hs.le
  have h0 : 0 < ‖s‖ := lt_of_lt_of_le hs (Complex.re_le_norm s)
  exact lt_of_lt_of_le (pow_pos h0 _) this

theorem cpq_ne_zero_of_im (S : Multiset ℚ) (s : ℂ) (hs : s.im ≠ 0) : cpq S s ≠ 0 := by
  unfold cpq
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp h0
  apply hs
  have := congrArg Complex.im hz
  simpa using this

theorem Rden_ne (n : ℕ) (s : ℂ) (hs : 0 < s.re ∨ s.im ≠ 0) :
    (Rden n).eval₂ (algebraMap ℚ ℂ) s ≠ 0 := by
  rw [Rden_eval]
  rcases hs with hs | hs
  · exact norm_pos_iff.mp (cpq_pos _ (poleSet_nonpos n) s hs)
  · exact cpq_ne_zero_of_im _ s hs

def hC (n k : ℕ) (s : ℂ) : ℂ := cEval (Rk n k) s

theorem hC_eq (n k : ℕ) (s : ℂ) (hs : (Rden n).eval₂ (algebraMap ℚ ℂ) s ≠ 0) :
    hC n k s = (-s) ^ k * cpq (zeroSet n) s / cpq (poleSet n) s := by
  rw [hC, Rk_eq, cEval_div _ _ _ hs, eval₂_mul, eval₂_pow, eval₂_neg, eval₂_X, Rnum_eval,
    Rden_eval]

def Cz (n : ℕ) : ℝ := 8 * ((zeroSet n).map fun z : ℚ => (1 + 2 * z : ℝ)).prod

theorem Cz_nonneg (n : ℕ) : 0 ≤ Cz n := by
  unfold Cz
  refine mul_nonneg (by norm_num) (Multiset.prod_nonneg fun x hx => ?_)
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  have := zeroSet_nonneg n z hz
  have : (0 : ℝ) ≤ z := by exact_mod_cast this
  linarith

theorem hC_bound (n k : ℕ) (hk : k ≤ 3) (s : ℂ) (hs : 0 < s.re) (hs2 : 1 / 2 ≤ ‖s‖) :
    ‖hC n k s‖ ≤ Cz n / ‖s‖ := by
  have hden := Rden_ne n s (Or.inl hs)
  rw [hC_eq n k s hden, norm_div, norm_mul, norm_pow, norm_neg]
  have hs0 : 0 < ‖s‖ := by linarith
  have hP := cpq_lower _ (poleSet_nonpos n) s hs.le
  have hPpos := cpq_pos _ (poleSet_nonpos n) s hs
  have hZ := cpq_upper _ (zeroSet_nonneg n) s hs2
  rw [card_poleSet] at hP
  rw [card_zeroSet] at hZ
  set cz := ((zeroSet n).map fun z : ℚ => (1 + 2 * z : ℝ)).prod with hcz
  have hcz0 : 0 ≤ cz := by
    have := Cz_nonneg n
    unfold Cz at this
    linarith
  have h8 := Aux.pow_div_cube_le ‖s‖ hs2 k hk
  calc ‖s‖ ^ k * ‖cpq (zeroSet n) s‖ / ‖cpq (poleSet n) s‖
      ≤ ‖s‖ ^ k * (cz * ‖s‖ ^ (30 * n)) / ‖s‖ ^ (30 * n + 4) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hZ (by positivity))
          (pow_pos hs0 _) hP
    _ = cz * (‖s‖ ^ k / ‖s‖ ^ 3) / ‖s‖ := by
        field_simp
        ring
    _ ≤ cz * 8 / ‖s‖ := by gcongr
    _ = Cz n / ‖s‖ := by rw [Cz]; ring

/-! ### Differentiability and the derivatives at the integers -/

theorem Rk_denom_dvd (n k : ℕ) : (Rk n k).denom ∣ Rden n := by
  rw [Rk_eq]
  exact RatFunc.denom_div_dvd _ _

theorem Rk_denom_ne (n k : ℕ) (s : ℂ) (hs : 0 < s.re ∨ s.im ≠ 0) :
    (Rk n k).denom.eval₂ (algebraMap ℚ ℂ) s ≠ 0 := by
  obtain ⟨g, hg⟩ := Rk_denom_dvd n k
  intro h
  apply Rden_ne n s hs
  rw [hg, eval₂_mul, h, zero_mul]

theorem hC_diff (n k : ℕ) (s : ℂ) (hs : (2 * n : ℝ) < s.re ∨ s.im ≠ 0) :
    DifferentiableAt ℂ (hC n k) s := by
  have h : 0 < s.re ∨ s.im ≠ 0 := by
    rcases hs with hs | hs
    · left; linarith [(by positivity : (0 : ℝ) ≤ 2 * n)]
    · right; exact hs
  exact (hasDerivAt_cEval _ s (Rk_denom_ne n k s h)).differentiableAt

theorem hC_bound' (n k : ℕ) (hk : k ≤ 3) (s : ℂ) (hs : (2 * n : ℝ) + 1 / 2 ≤ s.re) :
    ‖hC n k s‖ ≤ Cz n / ‖s‖ := by
  have h0 : (0 : ℝ) ≤ 2 * n := by positivity
  exact hC_bound n k hk s (by linarith) (by linarith [Complex.re_le_norm s])

def dv (n k : ℕ) (j : ℕ) : ℂ := cEval (rfDeriv (Rk n k)) ((2 * n : ℂ) + 1 + j)

theorem hC_hasDerivAt (n k j : ℕ) : HasDerivAt (hC n k) (dv n k j) ((2 * n : ℂ) + 1 + j) := by
  refine hasDerivAt_cEval _ _ (Rk_denom_ne n k _ (Or.inl ?_))
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.one_re,
    Complex.ofReal_ofNat, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, mul_zero,
    sub_zero]
  positivity

theorem Rk_denom_eval_rat_ne (n k : ℕ) (x : ℚ) (hx : 0 < x) :
    (Rk n k).denom.eval x ≠ 0 := by
  have h := Rk_denom_ne n k (x : ℂ) (Or.inl (by simp [hx]))
  rw [show (x : ℂ) = algebraMap ℚ ℂ x from rfl, eval₂_hom] at h
  intro h0
  apply h
  rw [h0, map_zero]

theorem dv_eq (n k j : ℕ) :
    dv n k j = ((deriv (rfReal (Rk n k)) ((2 * n : ℝ) + 1 + j) : ℝ) : ℂ) := by
  have hq : (2 * n : ℂ) + 1 + j = ((2 * n + 1 + j : ℚ) : ℂ) := by push_cast; ring
  have hr : (2 * n : ℝ) + 1 + j = ((2 * n + 1 + j : ℚ) : ℝ) := by push_cast; ring
  rw [dv, hq, cEval_rat, hr, deriv_rfReal_eq_rfDeriv _ _ (Rk_denom_eval_rat_ne n k _ (by positivity))]
  push_cast
  rfl

/-! ### Properness, splitting and poles of the kernel -/

theorem Rk_num_natDegree (n k : ℕ) : ((-X) ^ k * Rnum n : ℚ[X]).natDegree = k + 30 * n := by
  rw [natDegree_mul (pow_ne_zero _ (neg_ne_zero.mpr X_ne_zero)) (Rnum_monic n).ne_zero,
    natDegree_pow, natDegree_neg, natDegree_X, mul_one, Rnum_natDegree]

theorem Rk_proper (n k : ℕ) (hk : k ≤ 3) : (Rk n k).num.natDegree < (Rk n k).denom.natDegree := by
  have h : (Rk n k).intDegree = ((k + 30 * n : ℕ) : ℤ) - ((30 * n + 4 : ℕ) : ℤ) := by
    rw [Rk_eq, RatFunc.intDegree_div (Aux.algebraMap_ne_zero' (by
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr X_ne_zero)) (Rnum_monic n).ne_zero))
      (Aux.algebraMap_ne_zero' (Rden_monic n).ne_zero), RatFunc.intDegree_polynomial,
      RatFunc.intDegree_polynomial, Rk_num_natDegree, Rden_natDegree]
  unfold RatFunc.intDegree at h
  omega

theorem Rk_split (n k : ℕ) : (Rk n k).denom.roots.card = (Rk n k).denom.natDegree :=
  Polynomial.splits_iff_card_roots.mp ((Rden_splits n).of_dvd (Rden_monic n).ne_zero
    (Rk_denom_dvd n k))

theorem Rk_poles (n k : ℕ) : ∀ h ∈ (Rk n k).denom.roots, ∃ m : ℤ, m ≤ (2 * n : ℤ) ∧ h = m := by
  intro h hh
  have hmem := Multiset.mem_of_le (Polynomial.roots.le_of_dvd (Rden_monic n).ne_zero
    (Rk_denom_dvd n k)) hh
  rw [Rden, den_eq, Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨m, rfl⟩ := mem_poleSet n h hmem
  exact ⟨-(m : ℤ), by omega, by push_cast; ring⟩

theorem summable_deriv (n k : ℕ) (hk : k ≤ 3) :
    Summable fun j : ℕ => deriv (rfReal (Rk n k)) ((2 * n : ℝ) + 1 + j) := by
  have hK : ((2 * n : ℤ) : ℝ) = (2 * n : ℝ) := by push_cast; ring
  have heq : ∀ j : ℕ, deriv (rfReal (Rk n k)) ((2 * n : ℝ) + 1 + j) =
      ∑ h ∈ (Rk n k).denom.roots.toFinset, ∑ r ∈ Finset.range ((Rk n k).denom.natDegree + 1),
        -((r : ℝ) * (pfCoeff (Rk n k) h r : ℝ) * ((((2 * n : ℤ) : ℝ) + 1 + j - h) ^ (r + 1))⁻¹) := by
    intro j
    rw [← hK, BP.deriv_rfReal_eq (2 * n) (Rk n k) (Rk_proper n k hk) (Rk_split n k) (Rk_poles n k)
      _ (by rw [hK]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])]
  simp_rw [heq]
  refine summable_sum fun h hh => summable_sum fun r _ => ?_
  exact (BP.summable_pole_terms (2 * n) h (Rk_poles n k h (Multiset.mem_toFinset.mp hh))
    (pfCoeff (Rk n k) h r) r).neg

/-! ### The line integral -/

theorem line_integral_eq (n k : ℕ) (hk : k ≤ 3) :
    ∫ y : ℝ, Fc (hC n k) ((2 * n : ℂ) + 1 / 2 + y * I) =
      2 * Real.pi * ((realize (Lfun (2 * n) (Rk n k)) : ℝ) : ℂ) := by
  have hsum := summable_deriv n k hk
  have hL : HasSum (dv n k) (((∑' j : ℕ, deriv (rfReal (Rk n k)) ((2 * n : ℝ) + 1 + j) : ℝ) : ℂ)) := by
    rw [show dv n k = fun j : ℕ => ((deriv (rfReal (Rk n k)) ((2 * n : ℝ) + 1 + j) : ℝ) : ℂ) from
      funext (dv_eq n k)]
    exact Complex.hasSum_ofReal.mpr hsum.hasSum
  have hmain := main (hC n k) (2 * n) (Cz n) (Cz_nonneg n)
    (fun s hs => hC_diff n k s (by push_cast at hs; exact hs))
    (fun s hs => hC_bound' n k hk s (by push_cast at hs; exact hs)) (dv n k)
    (fun j => by have := hC_hasDerivAt n k j; push_cast; exact this) _ hL
  rw [show ((2 * n : ℕ) : ℂ) = (2 * n : ℂ) by push_cast; ring] at hmain
  rw [hmain, ← BP.derivSum_eq_realize_Lfun (2 * n) (Rk n k) (Rk_proper n k hk) (Rk_split n k)
    (Rk_poles n k), derivSum]
  push_cast
  ring

end Pfq54.MC
