/-
# A polynomial bound for the linear forms `S_{Nj}`

`S_{Nj} = -∑_{t ≥ 2N+1} f'(t)` with `f = (-t)^j R_N(t)`. At `2N+1 ≤ t ≤ 16N` the numerator of
`f` has a double zero, so `f'(t) = 0`. For `t ≥ 16N+1` every zero `z` of `f` satisfies
`|t - z| ≤ t` and every pole is `≤ 0`, so `|f'(t)| ≤ (60N+6)/t³`. Hence `|S_{Nj}| ≤ C (N + 1)`.
This replaces the contour bound `‖S_N‖ ≤ poly(N) e^{c₀N}`, `c₀ < b`, of PDF Part VII §6: all
that the cone argument uses is a bound `e^{cN}` with `c < b`.
-/
import Mfun_sub_Mfun_pred

open Polynomial Filter Topology Real
open scoped RatFunc

noncomputable section

namespace ZetasIrr.GW

/-- `∏_{a ∈ S} (X - a)`. -/
def pq (S : Multiset ℚ) : ℚ[X] := (S.map fun a => X - C a).prod

theorem pq_cons (a : ℚ) (S : Multiset ℚ) : pq (a ::ₘ S) = (X - C a) * pq S := by
  simp [pq]

theorem pq_add (S T : Multiset ℚ) : pq (S + T) = pq S * pq T := by
  simp [pq, Multiset.prod_add]

theorem zero_bound (Z : Multiset ℚ) (x : ℚ) (hx : 0 ≤ x) (hZ : ∀ a ∈ Z, |x - a| ≤ x) :
    |(pq Z).eval x| ≤ x ^ Multiset.card Z ∧
      |(derivative (pq Z)).eval x| * x ≤ Multiset.card Z * x ^ Multiset.card Z := by
  induction Z using Multiset.induction_on with
  | empty => simp [pq]
  | cons a S ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => hZ b (Multiset.mem_cons_of_mem hb)
    have ha := hZ a (Multiset.mem_cons_self a S)
    rw [pq_cons, derivative_mul, Multiset.card_cons]
    simp only [eval_mul, eval_add, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
      one_mul, eval_sub, eval_X, eval_C]
    have hE := abs_nonneg ((pq S).eval x)
    have hD := abs_nonneg ((derivative (pq S)).eval x)
    have hp : 0 ≤ x ^ Multiset.card S := pow_nonneg hx _
    constructor
    · rw [abs_mul, pow_succ]
      calc |x - a| * |(pq S).eval x| ≤ x * x ^ Multiset.card S :=
            mul_le_mul ha h1 hE hx
        _ = x ^ Multiset.card S * x := mul_comm _ _
    · calc |(pq S).eval x + (x - a) * (derivative (pq S)).eval x| * x
          ≤ (|(pq S).eval x| + |x - a| * |(derivative (pq S)).eval x|) * x := by
            refine mul_le_mul_of_nonneg_right ?_ hx
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ x ^ Multiset.card S * x + x * (Multiset.card S * x ^ Multiset.card S) := by
            have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (x - a))
            have := mul_le_mul_of_nonneg_right ha (mul_nonneg hD hx)
            nlinarith
        _ = ((Multiset.card S + 1 : ℕ) : ℚ) * x ^ (Multiset.card S + 1) := by push_cast; ring

theorem pole_bound (P : Multiset ℚ) (x : ℚ) (hx : 0 < x) (hP : ∀ a ∈ P, a ≤ 0) :
    x ^ Multiset.card P ≤ (pq P).eval x ∧
      |(derivative (pq P)).eval x| * x ≤ Multiset.card P * (pq P).eval x := by
  induction P using Multiset.induction_on with
  | empty => simp [pq]
  | cons a S ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => hP b (Multiset.mem_cons_of_mem hb)
    have ha := hP a (Multiset.mem_cons_self a S)
    rw [pq_cons, derivative_mul, Multiset.card_cons]
    simp only [eval_mul, eval_add, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
      one_mul, eval_sub, eval_X, eval_C]
    have hp : 0 < x ^ Multiset.card S := pow_pos hx _
    have hE : 0 < (pq S).eval x := lt_of_lt_of_le hp h1
    constructor
    · rw [pow_succ]; nlinarith
    · calc |(pq S).eval x + (x - a) * (derivative (pq S)).eval x| * x
          ≤ ((pq S).eval x + (x - a) * |(derivative (pq S)).eval x|) * x := by
            refine mul_le_mul_of_nonneg_right ?_ hx.le
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_pos hE, abs_of_nonneg (by linarith : 0 ≤ x - a)]
        _ ≤ (x - a) * (pq S).eval x + (x - a) * (Multiset.card S * (pq S).eval x) := by
            have := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ x - a)
            nlinarith
        _ = ((Multiset.card S + 1 : ℕ) : ℚ) * ((x - a) * (pq S).eval x) := by push_cast; ring

/-- `|(p'q - pq')(x) / q(x)²| ≤ (|Z| + |P|)/x³` for `p = s ∏_Z (X - a)`, `q = ∏_P (X - a)`. -/
theorem frac_bound (Z P : Multiset ℚ) (x s : ℚ) (hx : 1 ≤ x) (hs : |s| = 1)
    (hZ : ∀ a ∈ Z, |x - a| ≤ x) (hP : ∀ a ∈ P, a ≤ 0) (hc : Multiset.card Z + 2 ≤ Multiset.card P) :
    |(derivative (C s * pq Z) * pq P - C s * pq Z * derivative (pq P)).eval x / ((pq P).eval x) ^ 2|
      ≤ (Multiset.card Z + Multiset.card P) / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨a1, a2⟩ := zero_bound Z x hx0.le hZ
  obtain ⟨b1, b2⟩ := pole_bound P x hx0 hP
  set A := (pq Z).eval x
  set A' := (derivative (pq Z)).eval x
  set Q := (pq P).eval x
  set Q' := (derivative (pq P)).eval x
  set a := Multiset.card Z
  set b := Multiset.card P
  have hQ : 0 < Q := lt_of_lt_of_le (pow_pos hx0 _) b1
  have he : (derivative (C s * pq Z) * pq P - C s * pq Z * derivative (pq P)).eval x =
      s * (A' * Q - A * Q') := by
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_sub, eval_mul, eval_C]
    ring
  have hxb : x ^ a * x ^ 3 ≤ x ^ b * x := by
    rw [← pow_succ, ← pow_add]; exact pow_le_pow_right₀ hx (by omega)
  rw [he, abs_div, abs_mul, hs, one_mul, abs_of_pos (pow_pos hQ 2), div_le_div_iff₀ (pow_pos hQ 2)
    (pow_pos hx0 3)]
  have h1 : |A' * Q - A * Q'| * x ≤ (a + b) * x ^ a * Q := by
    calc |A' * Q - A * Q'| * x ≤ (|A'| * Q + |A| * |Q'|) * x := by
          refine mul_le_mul_of_nonneg_right ?_ hx0.le
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hQ]
      _ = |A'| * x * Q + |A| * (|Q'| * x) := by ring
      _ ≤ a * x ^ a * Q + x ^ a * (b * Q) :=
          add_le_add (mul_le_mul_of_nonneg_right a2 hQ.le)
            (mul_le_mul a1 b2 (by positivity) (pow_nonneg hx0.le _))
      _ = (a + b) * x ^ a * Q := by ring
  have hab : (0 : ℚ) ≤ a + b := by positivity
  calc |A' * Q - A * Q'| * x ^ 3 = |A' * Q - A * Q'| * x * x ^ 2 := by ring
    _ ≤ (a + b) * x ^ a * Q * x ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (a + b) * Q ^ 2 := by
        have : x ^ a * x ^ 2 ≤ Q := by
          have h3 : x ^ a * x ^ 3 ≤ Q * x := hxb.trans (mul_le_mul_of_nonneg_right b1 hx0.le)
          have h4 : x ^ a * x ^ 2 * x ≤ Q * x := by rw [mul_assoc, ← pow_succ]; exact h3
          exact le_of_mul_le_mul_right h4 hx0
        have := mul_le_mul_of_nonneg_left this (mul_nonneg hab hQ.le)
        nlinarith

/-! ### The zeros and poles of `(-t)^j R_N(t)` -/

theorem kernel_eq (N : ℕ) (j : Fin 3) :
    linFormKernel N j = algebraMap ℚ[X] ℚ⟮X⟯ (C ((-1) ^ (j : ℕ)) *
      pq (Multiset.replicate j 0 + zeroSet N)) / algebraMap ℚ[X] ℚ⟮X⟯ (pq (poleSet N)) := by
  have h1 : pq (Multiset.replicate (j : ℕ) 0) = X ^ (j : ℕ) := by
    rw [pq, Multiset.map_replicate, Multiset.prod_replicate, map_zero, sub_zero]
  have h2 : (-X : ℚ[X]) ^ (j : ℕ) = C ((-1) ^ (j : ℕ)) * X ^ (j : ℕ) := by
    rw [neg_pow, map_pow, map_neg, map_one]
  rw [linFormKernel_eq, pq_add, h1, h2]
  congr 2
  rw [pq, mul_assoc]

theorem zeroSet_mem (N j : ℕ) (a : ℚ) (ha : a ∈ Multiset.replicate (j : ℕ) 0 + zeroSet N) :
    0 ≤ a ∧ a ≤ 17 * N := by
  simp only [zeroSet, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_map,
    Multiset.mem_range] at ha
  rcases ha with ⟨-, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact ⟨le_rfl, by have := (Nat.cast_nonneg N : (0 : ℚ) ≤ N); linarith⟩
  · have : (i : ℚ) < 15 * N := by exact_mod_cast hi
    constructor <;> linarith
  · have : (i : ℚ) < 15 * N := by exact_mod_cast hi
    constructor <;> linarith

theorem poleSet_nonpos (N : ℕ) (a : ℚ) (ha : a ∈ poleSet N) : a ≤ 0 := by
  simp only [poleSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at ha
  rcases ha with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩ <;>
    nlinarith [(Nat.cast_nonneg i : (0 : ℚ) ≤ i), (Nat.cast_nonneg N : (0 : ℚ) ≤ N)]

theorem card_zero_pole (N j : ℕ) :
    Multiset.card (Multiset.replicate j 0 + zeroSet N) = j + 30 * N ∧
      Multiset.card (poleSet N) = 30 * N + 4 := by
  simp only [zeroSet, poleSet, Multiset.card_add, Multiset.card_replicate, Multiset.card_map,
    Multiset.card_range]
  omega

/-- At `2N+1 ≤ t ≤ 16N` the numerator `∏_Z (X - a)` has a double zero. -/
theorem double_zero (N : ℕ) (t : ℕ) (h1 : 2 * N + 1 ≤ t) (h2 : t ≤ 16 * N) (s : ℚ) (j : ℕ) :
    (derivative (C s * pq (Multiset.replicate j 0 + zeroSet N)) * pq (poleSet N) -
      C s * pq (Multiset.replicate j 0 + zeroSet N) * derivative (pq (poleSet N))).eval (t : ℚ) = 0 := by
  have m1 : (t : ℚ) ∈ (Multiset.range (15 * N)).map (fun i : ℕ => -((-17 * N : ℚ) + i)) :=
    Multiset.mem_map.mpr ⟨17 * N - t, Multiset.mem_range.mpr (by omega), by
      rw [Nat.cast_sub (by omega)]; push_cast; ring⟩
  have m2 : (t : ℚ) ∈ (Multiset.range (15 * N)).map (fun i : ℕ => -((-16 * N : ℚ) + i)) :=
    Multiset.mem_map.mpr ⟨16 * N - t, Multiset.mem_range.mpr (by omega), by
      rw [Nat.cast_sub (by omega)]; push_cast; ring⟩
  set Z1 := (Multiset.range (15 * N)).map (fun i : ℕ => -((-17 * N : ℚ) + i))
  set Z2 := (Multiset.range (15 * N)).map (fun i : ℕ => -((-16 * N : ℚ) + i))
  have hz : pq (Multiset.replicate j 0 + zeroSet N) = (X - C (t : ℚ)) ^ 2 *
      (pq (Multiset.replicate j 0) * pq (Z1.erase (t : ℚ)) * pq (Z2.erase (t : ℚ))) := by
    rw [pq_add, show zeroSet N = Z1 + Z2 from rfl, pq_add, ← Multiset.cons_erase m1,
      ← Multiset.cons_erase m2, pq_cons, pq_cons, Multiset.erase_cons_head, Multiset.erase_cons_head]
    ring
  rw [hz]
  simp [derivative_mul, derivative_pow]

/-- **`|S_{Nj}| ≤ C (N + 1)`.** -/
theorem S_poly_bound : ∃ C : ℝ, ∀ N : ℕ, ∀ j, |S N j| ≤ C * (N + 1) := by
  obtain ⟨z2, hz2⟩ : ∃ z2 : ℝ, HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) z2 := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    exact ⟨_, ((summable_nat_add_iff 1).mpr this).hasSum.congr_fun fun n => by push_cast; rfl⟩
  have hz0 : 0 ≤ z2 := hz2.nonneg fun n => by positivity
  refine ⟨60 * z2, fun N j => ?_⟩
  obtain ⟨cZ, cP⟩ := card_zero_pole N j
  set s : ℚ := (-1) ^ (j : ℕ)
  set Z := Multiset.replicate (j : ℕ) 0 + zeroSet N
  set p := C s * pq Z
  set q := pq (poleSet N)
  have hs : |s| = 1 := by simp [s]
  have hterm : ∀ n : ℕ, |deriv (rfReal (linFormKernel N j)) (((2 * (N : ℤ) : ℤ) : ℝ) + 1 + n)| ≤
      (60 * N + 6) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    set t : ℕ := 2 * N + 1 + n
    have ht1 : (1 : ℚ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    have hq : 0 < q.eval (t : ℚ) :=
      lt_of_lt_of_le (pow_pos (by linarith) _) (pole_bound _ _ (by linarith) (poleSet_nonpos N)).1
    have hden : (linFormKernel N j).denom.eval (t : ℚ) ≠ 0 := fun h0 =>
      hq.ne' (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (denom_linFormKernel_dvd N j) h0)
    have hpt : (((2 * (N : ℤ) : ℤ) : ℝ) + 1 + n) = ((t : ℚ) : ℝ) := by simp only [t]; push_cast; ring
    have hq0 : q ≠ 0 := fun h0 => hq.ne' (by rw [h0, eval_zero])
    rw [hpt, deriv_rfReal_eq_rfDeriv _ _ hden, kernel_eq, Aux.rfDeriv_div _ _ hq0,
      Aux.rfEval_div _ _ _ (by rw [eval_pow]; exact pow_ne_zero 2 hq.ne'), eval_pow, ← Rat.cast_abs]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rcases le_or_gt t (16 * N) with ht | ht
    · rw [double_zero N t (by omega) ht s j, zero_div, abs_zero, Rat.cast_zero]; positivity
    · have hZ : ∀ a ∈ Z, |(t : ℚ) - a| ≤ t := by
        intro a ha
        obtain ⟨h0, h17⟩ := zeroSet_mem N j a ha
        have : (16 * N + 1 : ℚ) ≤ t := by exact_mod_cast ht
        rw [abs_le]; constructor <;> linarith
      have hb := frac_bound Z (poleSet N) t s ht1 hs hZ (poleSet_nonpos N) (by
        rw [cZ, cP]; have := j.isLt; omega)
      rw [cZ, cP] at hb
      have hb' : ((|(derivative p * q - p * derivative q).eval (t : ℚ) / (q.eval (t : ℚ)) ^ 2| : ℚ) : ℝ)
          ≤ (((((j : ℕ) + 30 * N : ℕ) : ℚ) + ((30 * N + 4 : ℕ) : ℚ) : ℚ) : ℝ) / ((t : ℚ) : ℝ) ^ 3 := by
        rw [← Rat.cast_pow, ← Rat.cast_div]; exact_mod_cast hb
      refine hb'.trans ?_
      have hj : ((j : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : (j : ℕ) ≤ 2)
      have htn : (n : ℝ) + 1 ≤ ((t : ℚ) : ℝ) := by
        simp only [t]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have ht3 : ((n : ℝ) + 1) ^ 2 ≤ ((t : ℚ) : ℝ) ^ 3 := by
        have h1 : (1 : ℝ) ≤ ((t : ℚ) : ℝ) := by exact_mod_cast ht1
        calc ((n : ℝ) + 1) ^ 2 ≤ ((t : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ hn.le htn 2
          _ ≤ ((t : ℚ) : ℝ) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
      have hnum : (((((j : ℕ) + 30 * N : ℕ) : ℚ) + ((30 * N + 4 : ℕ) : ℚ) : ℚ) : ℝ) ≤ 60 * N + 6 := by
        push_cast; linarith
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul hnum ht3 (by positivity) (by positivity)
  have hsum : HasSum (fun n : ℕ => (60 * N + 6 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2)) ((60 * N + 6) * z2) :=
    hz2.mul_left _
  have := tsum_of_norm_bounded hsum (fun n => by rw [Real.norm_eq_abs]; exact hterm n)
  rw [S, derivSum, abs_neg]
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  nlinarith

end ZetasIrr.GW
