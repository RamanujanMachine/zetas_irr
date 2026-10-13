/-
# Blueprint of `meijerG_decay` (manuscript Proposition `z34-growth`)

Node `Pfq54.meijerG_decay` of `Blueprint_pfq54.lean`: for `n ≥ 1`, `𝒢_n(1)` is real and positive
and `|(θ^k 𝒢_n)(1)| ≤ (16n+1)^k 𝔡_n` for `k ≤ 3`; `𝔡_{n+1} ≤ η 𝔡_n` for `n ≥ 2`; `η < 1`.

Proof (manuscript Appendix A): after `s = 2n + w`, three Euler beta integrals, a fourth beta
integral for `Γ(w+n)Γ(15n+1-w)` and Mellin inversion (with Fubini justified by absolute
convergence) give the positive four-variable integral
`𝒢_n(1) = 𝔠_n ∫_{[0,1]⁴} x^{16n} y^{17n} t^{18n} r^{15n} (1-x)^{11n} (1-y)^{11n} (1-t)^{8n+1}
(1-r)^{15n} / (1 - r + xytr)^{14n+1}` ([1], [3]). The factor `(-s)^k = (-1)^k (w+2n)^k` has a
rising-factorial expansion with nonnegative coefficients, each `(w)_j` contributing at most
`(14n+1)_j`, whence the factor `(16n+1)^k` ([2]). Since `1 - r + xytr ≥ xyt`, Euler's integral
bounds the integral by `𝔡_n` ([4]). Exact factorial ratios give `𝔡_{n+1}/𝔡_n ≤ η` ([5]), and
`η < 1` ([6]).
-/
import Pfq54_aux
import meijerG_aux
import mg_aux8

open Finset Filter Topology MeasureTheory

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- `𝔠_n = (14n)! (16n)! / ((11n)!² (8n+1)!)`. -/
def cfrak (n : ℕ) : ℝ :=
  ((14 * n).factorial * (16 * n).factorial : ℝ) /
    ((11 * n).factorial ^ 2 * (8 * n + 1).factorial : ℝ)

/-- The positive integrand of the four-variable representation at `z = 1`. -/
def posIntegrand (n : ℕ) (x y t r : ℝ) : ℝ :=
  x ^ (16 * n) * y ^ (17 * n) * t ^ (18 * n) * r ^ (15 * n) * (1 - x) ^ (11 * n) *
      (1 - y) ^ (11 * n) * (1 - t) ^ (8 * n + 1) * (1 - r) ^ (15 * n) /
    ((1 - r) + x * y * t * r) ^ (14 * n + 1)

/-- `∫_{[0,1]⁴} posIntegrand`. -/
def Iint (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
    posIntegrand n x y t r

/-- Pointwise bounds for the positive integrand on the closed and on the open cube. -/
theorem posIntegrand_bounds (n : ℕ) (hn : 1 ≤ n) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ r ∈ Set.Icc (0 : ℝ) 1, 0 ≤ posIntegrand n x y t r ∧
        posIntegrand n x y t r ≤ x ^ (2 * n - 1) * (1 - x) ^ (11 * n) *
          (y ^ (3 * n - 1) * (1 - y) ^ (11 * n)) * (t ^ (4 * n - 1) * (1 - t) ^ (8 * n + 1)) *
          (r ^ (15 * n) * (1 - r) ^ (15 * n))) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < posIntegrand n x y t r) := by
  constructor
  · rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ t ⟨ht0, ht1⟩ r ⟨hr0, hr1⟩
    have hx1' : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hy1' : 0 ≤ 1 - y := sub_nonneg.mpr hy1
    have ht1' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hr1' : 0 ≤ 1 - r := sub_nonneg.mpr hr1
    have hxyt0 : 0 ≤ x * y * t := mul_nonneg (mul_nonneg hx0 hy0) ht0
    have hxyt1 : x * y * t ≤ 1 := by
      have h1 : x * y ≤ 1 := (mul_le_mul hx1 hy1 hy0 zero_le_one).trans_eq (one_mul 1)
      exact (mul_le_mul h1 ht1 ht0 zero_le_one).trans_eq (one_mul 1)
    have hD : 0 ≤ (1 - r) + x * y * t * r := add_nonneg hr1' (mul_nonneg hxyt0 hr0)
    have hN : 0 ≤ x ^ (16 * n) * y ^ (17 * n) * t ^ (18 * n) * r ^ (15 * n) *
        (1 - x) ^ (11 * n) * (1 - y) ^ (11 * n) * (1 - t) ^ (8 * n + 1) * (1 - r) ^ (15 * n) := by
      apply_rules [mul_nonneg, pow_nonneg]
    have hbnd : 0 ≤ x ^ (2 * n - 1) * (1 - x) ^ (11 * n) *
        (y ^ (3 * n - 1) * (1 - y) ^ (11 * n)) * (t ^ (4 * n - 1) * (1 - t) ^ (8 * n + 1)) *
        (r ^ (15 * n) * (1 - r) ^ (15 * n)) := by
      apply_rules [mul_nonneg, pow_nonneg]
    unfold posIntegrand
    refine ⟨div_nonneg hN (pow_nonneg hD _), ?_⟩
    rcases eq_or_lt_of_le hxyt0 with h0 | hpos
    · have hN0 : x ^ (16 * n) * y ^ (17 * n) * t ^ (18 * n) * r ^ (15 * n) *
          (1 - x) ^ (11 * n) * (1 - y) ^ (11 * n) * (1 - t) ^ (8 * n + 1) *
          (1 - r) ^ (15 * n) = 0 := by
        rcases mul_eq_zero.mp h0.symm with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rw [h, zero_pow (by omega : 16 * n ≠ 0)]; ring
          · rw [h, zero_pow (by omega : 17 * n ≠ 0)]; ring
        · rw [h, zero_pow (by omega : 18 * n ≠ 0)]; ring
      rw [hN0, zero_div]
      exact hbnd
    · have hxp : 0 < x := lt_of_le_of_ne hx0 fun h => by
        rw [← h, zero_mul, zero_mul] at hpos; exact lt_irrefl 0 hpos
      have hyp : 0 < y := lt_of_le_of_ne hy0 fun h => by
        rw [← h, mul_zero, zero_mul] at hpos; exact lt_irrefl 0 hpos
      have htp : 0 < t := lt_of_le_of_ne ht0 fun h => by
        rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
      have hDge : x * y * t ≤ (1 - r) + x * y * t * r := by
        have h := mul_nonneg hr1' (sub_nonneg.mpr hxyt1)
        rw [show (1 - r) * (1 - x * y * t) = (1 - r) + x * y * t * r - x * y * t by ring] at h
        exact sub_nonneg.mp h
      calc _ ≤ x ^ (16 * n) * y ^ (17 * n) * t ^ (18 * n) * r ^ (15 * n) *
            (1 - x) ^ (11 * n) * (1 - y) ^ (11 * n) * (1 - t) ^ (8 * n + 1) *
            (1 - r) ^ (15 * n) / (x * y * t) ^ (14 * n + 1) :=
            div_le_div_of_nonneg_left hN (pow_pos hpos _) (pow_le_pow_left₀ hxyt0 hDge _)
        _ = _ := by
          have ex : x ^ (16 * n) = x ^ (2 * n - 1) * x ^ (14 * n + 1) := by
            rw [← pow_add]; congr 1; omega
          have ey : y ^ (17 * n) = y ^ (3 * n - 1) * y ^ (14 * n + 1) := by
            rw [← pow_add]; congr 1; omega
          have et : t ^ (18 * n) = t ^ (4 * n - 1) * t ^ (14 * n + 1) := by
            rw [← pow_add]; congr 1; omega
          rw [ex, ey, et, mul_pow, mul_pow, div_eq_iff (by positivity)]
          ring
  · rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ t ⟨ht0, ht1⟩ r ⟨hr0, hr1⟩
    have hx1' : 0 < 1 - x := sub_pos.mpr hx1
    have hy1' : 0 < 1 - y := sub_pos.mpr hy1
    have ht1' : 0 < 1 - t := sub_pos.mpr ht1
    have hr1' : 0 < 1 - r := sub_pos.mpr hr1
    unfold posIntegrand
    apply div_pos
    · apply_rules [mul_pos, pow_pos]
    · apply pow_pos
      exact add_pos hr1' (mul_pos (mul_pos (mul_pos hx0 hy0) ht0) hr0)

/-- The four-level structure of `Iint`: positivity and the factorized upper bound. -/
theorem Iint_levels (n : ℕ) (hn : 1 ≤ n) :
    0 < Iint n ∧ Iint n ≤ (∫ x in (0 : ℝ)..1, x ^ (2 * n - 1) * (1 - x) ^ (11 * n)) *
      (∫ y in (0 : ℝ)..1, y ^ (3 * n - 1) * (1 - y) ^ (11 * n)) *
      (∫ t in (0 : ℝ)..1, t ^ (4 * n - 1) * (1 - t) ^ (8 * n + 1)) *
      (∫ r in (0 : ℝ)..1, r ^ (15 * n) * (1 - r) ^ (15 * n)) := by
  obtain ⟨hb, hpos⟩ := posIntegrand_bounds n hn
  set X : ℝ → ℝ := fun x => x ^ (2 * n - 1) * (1 - x) ^ (11 * n) with hX
  set Yf : ℝ → ℝ := fun y => y ^ (3 * n - 1) * (1 - y) ^ (11 * n) with hYf
  set Tf : ℝ → ℝ := fun t => t ^ (4 * n - 1) * (1 - t) ^ (8 * n + 1) with hTf
  set Rf : ℝ → ℝ := fun r => r ^ (15 * n) * (1 - r) ^ (15 * n) with hRf
  have hcX : Continuous X := by rw [hX]; fun_prop
  have hcY : Continuous Yf := by rw [hYf]; fun_prop
  have hcT : Continuous Tf := by rw [hTf]; fun_prop
  have hcR : Continuous Rf := by rw [hRf]; fun_prop
  set BX := ∫ x in (0 : ℝ)..1, X x
  set BY := ∫ y in (0 : ℝ)..1, Yf y
  set BT := ∫ t in (0 : ℝ)..1, Tf t
  set BR := ∫ r in (0 : ℝ)..1, Rf r
  have hm4 : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ => posIntegrand n q.1.1 q.1.2.1 q.1.2.2 q.2) := by
    unfold posIntegrand; fun_prop
  set φ3 : ℝ × ℝ × ℝ → ℝ := fun p => ∫ r in (0 : ℝ)..1, posIntegrand n p.1 p.2.1 p.2.2 r
  have hm3 : MeasureTheory.StronglyMeasurable φ3 :=
    Aux.sm_param_int (fun q : (ℝ × ℝ × ℝ) × ℝ => posIntegrand n q.1.1 q.1.2.1 q.1.2.2 q.2)
      hm4.stronglyMeasurable
  set φ2 : ℝ × ℝ → ℝ := fun q => ∫ t in (0 : ℝ)..1, φ3 (q.1, q.2, t)
  have hm2 : MeasureTheory.StronglyMeasurable φ2 :=
    Aux.sm_param_int (fun z : (ℝ × ℝ) × ℝ => φ3 (z.1.1, z.1.2, z.2))
      (hm3.comp_measurable (by fun_prop))
  set φ1 : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, φ2 (x, y)
  have hm1 : MeasureTheory.StronglyMeasurable φ1 :=
    Aux.sm_param_int (fun z : ℝ × ℝ => φ2 (z.1, z.2)) (hm2.comp_measurable (by fun_prop))
  have L3 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ φ3 (x, y, t) ∧ φ3 (x, y, t) ≤ X x * Yf y * Tf t * BR ∧
      (x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 →
        0 < φ3 (x, y, t)) := by
    intro x hx y hy t ht
    have hmr : Measurable (fun r => posIntegrand n x y t r) := by
      unfold posIntegrand; fun_prop
    have hgi : IntervalIntegrable (fun r => X x * Yf y * Tf t * Rf r) MeasureTheory.volume 0 1 :=
      (continuous_const.mul hcR).intervalIntegrable 0 1
    have hint : IntervalIntegrable (fun r => posIntegrand n x y t r) MeasureTheory.volume 0 1 :=
      Aux.ii_of_bound hmr hgi fun r hr => by
        rw [abs_of_nonneg (hb x hx y hy t ht r hr).1]; exact (hb x hx y hy t ht r hr).2
    refine ⟨intervalIntegral.integral_nonneg zero_le_one fun r hr => (hb x hx y hy t ht r hr).1,
      ?_, fun hx' hy' ht' => intervalIntegral.intervalIntegral_pos_of_pos_on hint
        (fun r hr => hpos x hx' y hy' t ht' r hr) zero_lt_one⟩
    calc φ3 (x, y, t) ≤ ∫ r in (0 : ℝ)..1, X x * Yf y * Tf t * Rf r :=
          intervalIntegral.integral_mono_on zero_le_one hint hgi fun r hr =>
            (hb x hx y hy t ht r hr).2
      _ = X x * Yf y * Tf t * BR := intervalIntegral.integral_const_mul _ _
  have L2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ φ2 (x, y) ∧ φ2 (x, y) ≤ X x * Yf y * BT * BR ∧
      (x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 → 0 < φ2 (x, y)) := by
    intro x hx y hy
    have hmt : Measurable (fun t => φ3 (x, y, t)) := hm3.measurable.comp (by fun_prop)
    have hgi : IntervalIntegrable (fun t => X x * Yf y * Tf t * BR) MeasureTheory.volume 0 1 :=
      ((continuous_const.mul hcT).mul continuous_const).intervalIntegrable 0 1
    have hint : IntervalIntegrable (fun t => φ3 (x, y, t)) MeasureTheory.volume 0 1 :=
      Aux.ii_of_bound hmt hgi fun t ht => by
        rw [abs_of_nonneg (L3 x hx y hy t ht).1]; exact (L3 x hx y hy t ht).2.1
    refine ⟨intervalIntegral.integral_nonneg zero_le_one fun t ht => (L3 x hx y hy t ht).1, ?_,
      fun hx' hy' => intervalIntegral.intervalIntegral_pos_of_pos_on hint
        (fun t ht => (L3 x hx y hy t (Set.Ioo_subset_Icc_self ht)).2.2 hx' hy' ht) zero_lt_one⟩
    calc φ2 (x, y) ≤ ∫ t in (0 : ℝ)..1, X x * Yf y * Tf t * BR :=
          intervalIntegral.integral_mono_on zero_le_one hint hgi fun t ht => (L3 x hx y hy t ht).2.1
      _ = X x * Yf y * BT * BR := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  have L1 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ φ1 x ∧ φ1 x ≤ X x * BY * BT * BR ∧ (x ∈ Set.Ioo (0 : ℝ) 1 → 0 < φ1 x) := by
    intro x hx
    have hmy : Measurable (fun y => φ2 (x, y)) := hm2.measurable.comp (by fun_prop)
    have hgi : IntervalIntegrable (fun y => X x * Yf y * BT * BR) MeasureTheory.volume 0 1 :=
      (((continuous_const.mul hcY).mul continuous_const).mul continuous_const).intervalIntegrable 0 1
    have hint : IntervalIntegrable (fun y => φ2 (x, y)) MeasureTheory.volume 0 1 :=
      Aux.ii_of_bound hmy hgi fun y hy => by
        rw [abs_of_nonneg (L2 x hx y hy).1]; exact (L2 x hx y hy).2.1
    refine ⟨intervalIntegral.integral_nonneg zero_le_one fun y hy => (L2 x hx y hy).1, ?_,
      fun hx' => intervalIntegral.intervalIntegral_pos_of_pos_on hint
        (fun y hy => (L2 x hx y (Set.Ioo_subset_Icc_self hy)).2.2 hx' hy) zero_lt_one⟩
    calc φ1 x ≤ ∫ y in (0 : ℝ)..1, X x * Yf y * BT * BR :=
          intervalIntegral.integral_mono_on zero_le_one hint hgi fun y hy => (L2 x hx y hy).2.1
      _ = X x * BY * BT * BR := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_const_mul]
  have hgi : IntervalIntegrable (fun x => X x * BY * BT * BR) MeasureTheory.volume 0 1 :=
    (((hcX.mul continuous_const).mul continuous_const).mul continuous_const).intervalIntegrable 0 1
  have hint : IntervalIntegrable φ1 MeasureTheory.volume 0 1 :=
    Aux.ii_of_bound hm1.measurable hgi fun x hx => by
      rw [abs_of_nonneg (L1 x hx).1]; exact (L1 x hx).2.1
  change 0 < ∫ x in (0 : ℝ)..1, φ1 x ∧ ∫ x in (0 : ℝ)..1, φ1 x ≤ BX * BY * BT * BR
  refine ⟨intervalIntegral.intervalIntegral_pos_of_pos_on hint
    (fun x hx => (L1 x (Set.Ioo_subset_Icc_self hx)).2.2 hx) zero_lt_one, ?_⟩
  calc ∫ x in (0 : ℝ)..1, φ1 x ≤ ∫ x in (0 : ℝ)..1, X x * BY * BT * BR :=
        intervalIntegral.integral_mono_on zero_le_one hint hgi fun x hx => (L1 x hx).2.1
    _ = BX * BY * BT * BR := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_mul_const]

/-- The positive integrand is integrable on `(0,1)⁴` (it is bounded by `1`). -/
theorem posIntegrand_integrable (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun z : ℝ × ℝ × ℝ × ℝ => MG.Pd n z.1 z.2.1 z.2.2.1 z.2.2.2) MG.μ4 := by
  have hm : Measurable fun z : ℝ × ℝ × ℝ × ℝ => MG.Pd n z.1 z.2.1 z.2.2.1 z.2.2.2 := by
    unfold MG.Pd
    fun_prop
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (MG.ae_cube.mono fun z hz => ?_)
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, ⟨ht0, ht1⟩, ⟨hr0, hr1⟩⟩ := hz
  obtain ⟨h0, h1⟩ := (posIntegrand_bounds n hn).1 _ ⟨hx0.le, hx1.le⟩ _ ⟨hy0.le, hy1.le⟩ _
    ⟨ht0.le, ht1.le⟩ _ ⟨hr0.le, hr1.le⟩
  change ‖posIntegrand n z.1 z.2.1 z.2.2.1 z.2.2.2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine h1.trans ?_
  have u : ∀ (a : ℝ) (k : ℕ), 0 ≤ a → a ≤ 1 → a ^ k ≤ 1 := fun a k ha ha1 => pow_le_one₀ ha ha1
  have p : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1 := fun a b _ ha1 hb hb1 =>
    (mul_le_mul ha1 hb1 hb zero_le_one).trans_eq (one_mul 1)
  have q : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := fun a b => mul_nonneg
  have ux := u z.1 (2 * n - 1) hx0.le hx1.le
  have uy := u z.2.1 (3 * n - 1) hy0.le hy1.le
  have ut := u z.2.2.1 (4 * n - 1) ht0.le ht1.le
  have ur := u z.2.2.2 (15 * n) hr0.le hr1.le
  have vx := u (1 - z.1) (11 * n) (by linarith) (by linarith)
  have vy := u (1 - z.2.1) (11 * n) (by linarith) (by linarith)
  have vt := u (1 - z.2.2.1) (8 * n + 1) (by linarith) (by linarith)
  have vr := u (1 - z.2.2.2) (15 * n) (by linarith) (by linarith)
  have n1 := pow_nonneg hx0.le (2 * n - 1)
  have n2 := pow_nonneg hy0.le (3 * n - 1)
  have n3 := pow_nonneg ht0.le (4 * n - 1)
  have n4 := pow_nonneg hr0.le (15 * n)
  have m1 := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.1) (11 * n)
  have m2 := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.2.1) (11 * n)
  have m3 := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.2.2.1) (8 * n + 1)
  have m4 := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.2.2.2) (15 * n)
  exact p _ _ (q _ _ (q _ _ (q _ _ n1 m1) (q _ _ n2 m2)) (q _ _ n3 m3))
    (p _ _ (q _ _ (q _ _ n1 m1) (q _ _ n2 m2)) (p _ _ (q _ _ n1 m1) (p _ _ n1 ux m1 vx)
      (q _ _ n2 m2) (p _ _ n2 uy m2 vy)) (q _ _ n3 m3) (p _ _ n3 ut m3 vt)) (q _ _ n4 m4)
    (p _ _ n4 ur m4 vr)

/-- `Iint` is the integral over `(0,1)⁴`. -/
theorem Iint_eq (n : ℕ) (hn : 1 ≤ n) : Iint n = MG.Xj n 0 := by
  have hF := posIntegrand_integrable n hn
  have e1 : ∀ f : ℝ → ℝ, ∫ x in (0 : ℝ)..1, f x = ∫ x, f x ∂MG.ρ := fun f => by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  unfold Iint MG.Xj
  simp only [e1, pow_zero, mul_one]
  rw [show MG.μ4 = MG.ρ.prod (MG.ρ.prod (MG.ρ.prod MG.ρ)) from rfl, integral_prod _ hF]
  refine integral_congr_ae ((hF.prod_right_ae).mono fun x hx => ?_)
  beta_reduce
  rw [integral_prod _ hx]
  refine integral_congr_ae ((hx.prod_right_ae).mono fun y hy => ?_)
  beta_reduce
  rw [integral_prod _ hy]
  rfl

theorem cfrak_eq (n : ℕ) : cfrak n = MG.cfR n := by
  unfold cfrak MG.cfR
  ring

/-- **[1] The positive integral representation**: `𝒢_n(1) = 𝔠_n · Iint n` for `n ≥ 1`.
* Estimated proof length: ≈ 200 lines (substitution `s = 2n + w`; Euler's beta integral
  `Γ(a)Γ(b)/Γ(a+b) = ∫₀¹ x^{a-1}(1-x)^{b-1}`, Mathlib `Complex.betaIntegral`; the Mellin pair
  `∫ Γ(w)Γ(L-w) u^{-w} dw/(2πi) = Γ(L) (1+u)^{-L}`; Fubini with absolute convergence; real part
  conditions on the contour `Re w = 1/2`).
* Directly from the manuscript: partially (the Mellin inversion step and the Fubini/convergence
  checks are only indicated). -/
theorem SG_zero_eq_integral (n : ℕ) (hn : 1 ≤ n) : SG n 0 = ((cfrak n * Iint n : ℝ) : ℂ) := by
  rw [MG.SG_zero_aux n hn, cfrak_eq, Iint_eq n hn]

/-- **[2] The derivatives**: `‖(θ^k 𝒢_n)(1)‖ ≤ (16n+1)^k 𝔠_n Iint n` for `n ≥ 1`, `k ≤ 3`
(`(w+a)^k = ∑_j c_j (w)_j` with `c_j ≥ 0` for `a = 2n ≥ 2`; `(w)_j` shifts `Γ(w)` to `Γ(w+j)`
and multiplies the positive integrand by `(L)_j [(1-r)/(1-r+ur)]^j ≤ (L)_j`, `L = 14n+1`;
evaluating the expansion at `w = L` gives `(a + L)^k = (16n+1)^k`).
* Uses: [1] (its proof, with `Γ(w+j)` in place of `Γ(w)`).
* Estimated proof length: ≈ 120 lines.
* Directly from the manuscript: partially (as for [1]). -/
theorem SG_norm_le (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ 3) :
    ‖SG n k‖ ≤ (16 * n + 1 : ℝ) ^ k * (cfrak n * Iint n) := by
  rw [cfrak_eq, Iint_eq n hn]
  exact MG.SG_bound_aux n k hn hk (posIntegrand_integrable n hn)

/-- **[3] Positivity of the integral** (continuous, nonnegative, positive inside the cube).
* Estimated proof length: ≈ 30 lines.
* Directly from the manuscript: yes. -/
theorem Iint_pos (n : ℕ) (hn : 1 ≤ n) : 0 < Iint n := by
  exact (Iint_levels n hn).1

/-- **[4] The factorial bound**: `𝔠_n Iint n ≤ 𝔡_n` (`1 - r + xytr ≥ xyt`, then four Euler
beta integrals).
* Estimated proof length: ≈ 60 lines.
* Directly from the manuscript: yes. -/
theorem cI_le_dfrak (n : ℕ) (hn : 1 ≤ n) : cfrak n * Iint n ≤ dfrak n := by
  have hle := (Iint_levels n hn).2
  rw [Aux.beta_nat, Aux.beta_nat, Aux.beta_nat, Aux.beta_nat,
    show 2 * n - 1 + 11 * n + 1 = 13 * n by omega, show 3 * n - 1 + 11 * n + 1 = 14 * n by omega,
    show 4 * n - 1 + (8 * n + 1) + 1 = 12 * n + 1 by omega,
    show 15 * n + 15 * n + 1 = 30 * n + 1 by omega] at hle
  have hc : 0 ≤ cfrak n := by unfold cfrak; positivity
  refine (mul_le_mul_of_nonneg_left hle hc).trans (le_of_eq ?_)
  have h1 : ((11 * n).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((8 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((14 * n).factorial : ℝ) ≠ 0 := by positivity
  unfold cfrak dfrak
  field_simp

/-- **[5] The ratio bound**: `𝔡_{n+1} ≤ η 𝔡_n` for `n ≥ 2` (the 55 numerator factors bounded
above using `n + 1`, the 55 denominator factors below using `n`; `((n+1)/n)^55 ≤ (3/2)^55`).
* Estimated proof length: ≈ 50 lines.
* Directly from the manuscript: yes (exact rational comparison). -/
theorem dfrak_ratio (n : ℕ) (hn : 2 ≤ n) : dfrak (n + 1) ≤ eta * dfrak n := by
  exact MD.dfrak_ratio' n hn
/-- **[6]** `η < 1` (`η ≈ 8.517 · 10⁻⁴`).
* Estimated proof length: ≈ 3 lines (`norm_num [eta]`).
* Directly from the manuscript: yes (exact rational arithmetic). -/
theorem eta_lt_one : eta < 1 := by
  unfold eta
  norm_num

/-- **`meijerG_decay`** (node of `Blueprint_pfq54.lean`). Proved from [1]–[6]. -/
theorem meijerG_decay :
    (∀ n ≥ 1, 0 < (SG n 0).re ∧ (SG n 0).im = 0 ∧
        ∀ k ≤ 3, ‖SG n k‖ ≤ (16 * n + 1 : ℝ) ^ k * dfrak n) ∧
      (∀ n ≥ 2, dfrak (n + 1) ≤ eta * dfrak n) ∧ eta < 1 := by
  refine ⟨fun n hn => ?_, fun n hn => dfrak_ratio n hn, eta_lt_one⟩
  have hc : 0 < cfrak n := by unfold cfrak; positivity
  have hI := Iint_pos n hn
  refine ⟨?_, ?_, fun k hk => (SG_norm_le n hn k hk).trans ?_⟩
  · rw [SG_zero_eq_integral n hn, Complex.ofReal_re]; exact mul_pos hc hI
  · rw [SG_zero_eq_integral n hn, Complex.ofReal_im]
  · exact mul_le_mul_of_nonneg_left (cI_le_dfrak n hn) (by positivity)

end Pfq54.BP
