import mc_aux2

open Filter Topology MeasureTheory Set intervalIntegral Polynomial Finset
open Complex (I)

noncomputable section

namespace Pfq54.MC

open Pfq54 Pfq54.MI ZetasIrr ZetasIrr.CMF

/-! ### Gamma shifts -/

theorem Gamma_add_nat (s : ℂ) (m : ℕ) (hs : ∀ i : ℕ, i < m → s + i ≠ 0) :
    Complex.Gamma (s + m) = (∏ i ∈ range m, (s + i)) * Complex.Gamma s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (hs m (by omega)),
      ih (fun i hi => hs i (by omega)), prod_range_succ]
    ring

theorem nonint_add_ne (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) (c : ℤ) (i : ℕ) : s + c + i ≠ 0 := by
  intro h
  apply hs (-(c + i))
  push_cast
  linear_combination h

theorem nonint_one_sub_ne (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) (i : ℕ) : 1 - s + i ≠ 0 := by
  intro h
  apply hs (1 + i)
  push_cast
  linear_combination -h

theorem prod_add_ne (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) (c : ℤ) (m : ℕ) :
    ∏ i ∈ range m, (s + c + i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => nonint_add_ne s hs c i

theorem Gamma_sub_nat (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) (m : ℕ) :
    Complex.Gamma (s - m) = Complex.Gamma s / ∏ i ∈ range m, (s - m + i) := by
  have hne : ∀ i : ℕ, s - m + i ≠ 0 := fun i => by
    have := nonint_add_ne s hs (-m) i
    rwa [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg] at this
  have h1 := Gamma_add_nat (s - m) m fun i _ => hne i
  have h2 : ∏ i ∈ range m, (s - m + i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  rw [sub_add_cancel] at h1
  rw [h1, mul_div_cancel_left₀ _ h2]

/-- The rational part of the integrand, as it comes out of the Gamma shifts. -/
def ratPart (n : ℕ) (s : ℂ) : ℂ :=
  (∏ i ∈ range (16 * n), (1 - s + i)) * (∏ i ∈ range (17 * n), (1 - s + i)) *
      (∏ i ∈ range n, (s + i)) * (∏ i ∈ range (2 * n), (s + i)) /
    ((∏ i ∈ range (11 * n + 1), (s + i)) * (∏ i ∈ range (12 * n + 1), (s + i)) *
      (∏ i ∈ range (10 * n + 2), (s + i)) * (∏ i ∈ range n, (s - n + i)) *
      (∏ i ∈ range (2 * n), (s - 2 * n + i)))

theorem Icc_m2_2 : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide

theorem mb_gamma (n : ℕ) (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) :
    mbIntegrand n s = (Complex.Gamma s * Complex.Gamma (1 - s)) ^ 2 * ratPart n s := by
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero fun m h => hs (-m) (by rw [h]; push_cast; rfl)
  have hadd : ∀ (c : ℤ) (m : ℕ), Complex.Gamma (s + c + m) =
      (∏ i ∈ range m, (s + c + i)) * Complex.Gamma (s + c) :=
    fun c m => Gamma_add_nat (s + c) m fun i _ => nonint_add_ne s hs c i
  have hsub : ∀ m : ℕ, Complex.Gamma (1 - s + m) =
      (∏ i ∈ range m, (1 - s + i)) * Complex.Gamma (1 - s) :=
    fun m => Gamma_add_nat (1 - s) m fun i _ => nonint_one_sub_ne s hs i
  have h16 : Complex.Gamma (16 * n + 1 - s) = (∏ i ∈ range (16 * n), (1 - s + i)) *
      Complex.Gamma (1 - s) := by
    rw [← hsub]; congr 1; push_cast; ring
  have h17 : Complex.Gamma (17 * n + 1 - s) = (∏ i ∈ range (17 * n), (1 - s + i)) *
      Complex.Gamma (1 - s) := by
    rw [← hsub]; congr 1; push_cast; ring
  have h11 : Complex.Gamma (s + 11 * n + 1) = (∏ i ∈ range (11 * n + 1), (s + i)) *
      Complex.Gamma s := by
    have := hadd 0 (11 * n + 1); push_cast at this ⊢; simp only [add_zero] at this
    rw [← this]; congr 1; ring
  have h12 : Complex.Gamma (s + 12 * n + 1) = (∏ i ∈ range (12 * n + 1), (s + i)) *
      Complex.Gamma s := by
    have := hadd 0 (12 * n + 1); push_cast at this ⊢; simp only [add_zero] at this
    rw [← this]; congr 1; ring
  have h10 : Complex.Gamma (s + 10 * n + 2) = (∏ i ∈ range (10 * n + 2), (s + i)) *
      Complex.Gamma s := by
    have := hadd 0 (10 * n + 2); push_cast at this ⊢; simp only [add_zero] at this
    rw [← this]; congr 1; ring
  have hn1 : Complex.Gamma (s + n) = (∏ i ∈ range n, (s + i)) * Complex.Gamma s := by
    have := hadd 0 n; push_cast at this ⊢; simp only [add_zero] at this; exact this
  have hn2 : Complex.Gamma (s + 2 * n) = (∏ i ∈ range (2 * n), (s + i)) * Complex.Gamma s := by
    have := hadd 0 (2 * n)
    push_cast at this
    simpa only [add_zero] using this
  have hm1 := Gamma_sub_nat s hs n
  have hm2 : Complex.Gamma (s - 2 * n) = Complex.Gamma s / ∏ i ∈ range (2 * n), (s - 2 * n + i) := by
    have := Gamma_sub_nat s hs (2 * n)
    push_cast at this
    exact this
  have hprod : ∏ j ∈ Finset.Icc (-2 : ℤ) 2, Complex.Gamma (s + j * n) =
      Complex.Gamma (s - 2 * n) * Complex.Gamma (s - n) * Complex.Gamma s * Complex.Gamma (s + n) *
        Complex.Gamma (s + 2 * n) := by
    rw [Icc_m2_2, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), Finset.prod_singleton]
    push_cast
    ring_nf
  have hd1 := prod_add_ne s hs 0 (11 * n + 1)
  have hd2 := prod_add_ne s hs 0 (12 * n + 1)
  have hd3 := prod_add_ne s hs 0 (10 * n + 2)
  have hd4 := prod_add_ne s hs (-n) n
  have hd5 := prod_add_ne s hs (-(2 * n)) (2 * n)
  push_cast at hd1 hd2 hd3 hd4 hd5
  simp only [add_zero] at hd1 hd2 hd3
  rw [mbIntegrand, hprod, h16, h17, h11, h12, h10, hn1, hn2, hm1, hm2, ratPart]
  field_simp

theorem Gamma_sq (s : ℂ) : (Complex.Gamma s * Complex.Gamma (1 - s)) ^ 2 =
    (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * s) ^ 2 := by
  rw [Complex.Gamma_mul_Gamma_one_sub, div_pow]

/-! ### The rational part is `(-1)^n R_n` -/

theorem cpq_map_range (c : ℚ) (m : ℕ) (s : ℂ) :
    cpq ((Multiset.range m).map fun i : ℕ => -(c + i)) s = ∏ i ∈ range m, (s + c + i) := by
  rw [cpq, Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.range_val]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

theorem cpq_add (S T : Multiset ℚ) (s : ℂ) : cpq (S + T) s = cpq S s * cpq T s := by
  simp [cpq, Multiset.map_add, Multiset.prod_add]

theorem prod_reflect (s : ℂ) (m : ℕ) :
    ∏ i ∈ range m, (1 - s + i) = (-1) ^ m * ∏ i ∈ range m, (s - m + i) := by
  have h1 : ∏ i ∈ range m, (1 - s + i) = ∏ i ∈ range m, (-1 : ℂ) * (s - 1 - i) := by
    refine prod_congr rfl fun i _ => ?_; ring
  rw [h1, prod_mul_distrib, prod_const, card_range]
  congr 1
  rw [← prod_range_reflect (fun i : ℕ => s - 1 - (i : ℂ)) m]
  refine prod_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem ratPart_eq (n : ℕ) (s : ℂ) (hs : ∀ j : ℤ, s ≠ j) :
    ratPart n s = (-1) ^ n * (cpq (zeroSet n) s / cpq (poleSet n) s) := by
  have e1 : ∏ i ∈ range (16 * n), (1 - s + i) =
      (∏ i ∈ range (15 * n), (s + (-16 * n : ℚ) + i)) * ∏ i ∈ range n, (s - n + i) := by
    rw [prod_reflect, Even.neg_one_pow ⟨8 * n, by ring⟩, one_mul,
      show 16 * n = 15 * n + n by ring, prod_range_add]
    push_cast
    congr 1
    · refine prod_congr rfl fun i _ => ?_; ring
    · refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have e2 : ∏ i ∈ range (17 * n), (1 - s + i) = (-1) ^ n *
      ((∏ i ∈ range (15 * n), (s + (-17 * n : ℚ) + i)) * ∏ i ∈ range (2 * n), (s - 2 * n + i)) := by
    rw [prod_reflect, show 17 * n = 15 * n + 2 * n by ring, prod_range_add]
    push_cast
    rw [show (-1 : ℂ) ^ (15 * n + 2 * n) = (-1) ^ n by
      rw [show 15 * n + 2 * n = n + 2 * (8 * n) by ring, pow_add, pow_mul]; norm_num]
    congr 2
    · refine prod_congr rfl fun i _ => ?_; ring
    · refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have e3 : ∏ i ∈ range (11 * n + 1), (s + i) =
      (∏ i ∈ range n, (s + i)) * ∏ i ∈ range (10 * n + 1), (s + (n : ℚ) + i) := by
    rw [show 11 * n + 1 = n + (10 * n + 1) by ring, prod_range_add]
    congr 1
    refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have e4 : ∏ i ∈ range (12 * n + 1), (s + i) =
      (∏ i ∈ range (2 * n), (s + i)) * ∏ i ∈ range (10 * n + 1), (s + (2 * n : ℚ) + i) := by
    rw [show 12 * n + 1 = 2 * n + (10 * n + 1) by ring, prod_range_add]
    congr 1
    refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have e5 : ∏ i ∈ range (10 * n + 2), (s + i) = ∏ i ∈ range (10 * n + 2), (s + (0 : ℚ) + i) := by
    refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have hZ : cpq (zeroSet n) s = (∏ i ∈ range (15 * n), (s + (-17 * n : ℚ) + i)) *
      ∏ i ∈ range (15 * n), (s + (-16 * n : ℚ) + i) := by
    rw [zeroSet, cpq_add, cpq_map_range, cpq_map_range]
  have hP : cpq (poleSet n) s = (∏ i ∈ range (10 * n + 2), (s + (0 : ℚ) + i)) *
      (∏ i ∈ range (10 * n + 1), (s + (n : ℚ) + i)) *
      ∏ i ∈ range (10 * n + 1), (s + (2 * n : ℚ) + i) := by
    rw [poleSet, cpq_add, cpq_add, cpq_map_range, cpq_map_range, cpq_map_range]
  have hd1 := prod_add_ne s hs 0 n
  have hd2 := prod_add_ne s hs 0 (2 * n)
  have hd3 := prod_add_ne s hs (-n) n
  have hd4 := prod_add_ne s hs (-(2 * n)) (2 * n)
  have hd5 := prod_add_ne s hs 0 (10 * n + 2)
  have hd6 := prod_add_ne s hs n (10 * n + 1)
  have hd7 := prod_add_ne s hs (2 * n) (10 * n + 1)
  push_cast at hd1 hd2 hd3 hd4 hd5 hd6 hd7
  simp only [add_zero] at hd1 hd2
  simp only [← sub_eq_add_neg] at hd3 hd4
  rw [ratPart, e1, e2, e3, e4, e5, hZ, hP]
  push_cast at hd6 hd7 ⊢
  rw [← mul_div_assoc, div_eq_div_iff]
  · ring
  all_goals (repeat' apply mul_ne_zero) <;> assumption

/-! ### The integrand on the contour -/

theorem mbContour_eq (n : ℕ) (y : ℝ) : mbContour n y = (2 * n : ℂ) + 1 / 2 + y * I := rfl

theorem contour_nonint (n : ℕ) (y : ℝ) : ∀ j : ℤ, mbContour n y ≠ j := by
  rw [mbContour_eq]
  refine not_int_of_re_half _ (2 * n) ?_
  simp

theorem cEval_Rker (n : ℕ) (s : ℂ) (hs : 0 < s.re ∨ s.im ≠ 0) :
    cEval (Rker n) s = cpq (zeroSet n) s / cpq (poleSet n) s := by
  rw [Rker_eq, cEval_div _ _ _ (Rden_ne n s hs), Rnum_eval, Rden_eval]

theorem integrand_eq (n k : ℕ) (y : ℝ) :
    (-mbContour n y) ^ k * mbIntegrand n (mbContour n y) = (-1) ^ n * Fc (hC n k) (mbContour n y) := by
  have hs := contour_nonint n y
  have hre : 0 < (mbContour n y).re := by rw [mbContour_eq]; simp; positivity
  rw [mb_gamma n _ hs, Gamma_sq, ratPart_eq n _ hs, Fc, hC_eq n k _ (Rden_ne n _ (Or.inl hre))]
  ring

/-! ### The state as the realised functional -/

theorem SG_eq (n k : ℕ) (hk : k ≤ 3) :
    SG n k = (((-1 : ℝ) ^ n * realize (Lfun (2 * n) (Rk n k)) : ℝ) : ℂ) := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  unfold SG
  have h : (fun y : ℝ => (-mbContour n y) ^ k * mbIntegrand n (mbContour n y)) =
      fun y : ℝ => (-1) ^ n * Fc (hC n k) ((2 * n : ℂ) + 1 / 2 + y * I) :=
    funext fun y => integrand_eq n k y
  rw [h, MeasureTheory.integral_const_mul, line_integral_eq n k hk]
  push_cast at hpi ⊢
  field_simp

theorem realize_sum {ι : Type*} (s : Finset ι) (f : ι → FormalZ) :
    realize (∑ i ∈ s, f i) = ∑ i ∈ s, realize (f i) := by
  rw [realize_eq_realizeHom, map_sum]
  rfl

theorem SG_step (n : ℕ) (k : Fin 4) :
    SG (n + 1) k = ∑ j : Fin 4, SG n j * ((-(Wmat n j k) : ℚ) : ℂ) := by
  have ht := transport_orig n
  have hk := congrFun ht k
  rw [ker_pN, ker_pN] at hk
  simp only [mv, mom, vm] at hk
  have hk' : Lfun (2 * (n + 1 : ℕ)) (Rk (n + 1) k) = ∑ i : Fin 4, Wmat n i k • Lfun (2 * n) (Rk n i) := hk
  have hr := congrArg realize hk'
  rw [realize_sum] at hr
  simp only [realize_smul] at hr
  rw [SG_eq (n + 1) k (by omega)]
  rw [show (2 * ((n + 1 : ℕ) : ℤ)) = 2 * (n + 1 : ℕ) by push_cast; ring] at hr
  rw [hr]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SG_eq n i (by omega)]
  push_cast
  ring

end Pfq54.MC
