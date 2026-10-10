/-
# Blueprint for `ZetasIrr.valuation_bound`

Statement (as in `blueprint.lean`): for `N ≥ 1`, a prime `p` and a nonzero entry of `𝓡_N`,
`v_p(𝓡_N[i,j]) ≥ -E₃₄(N,p)` if `p ≤ 29N+1`, and `≥ 0` otherwise.

Source: PDF Part VII §3 (Lemma 2 and its proof: pole argument, `V_o`, `C_p`, `A_p`, cofactors,
`det 𝓒_N = -6(-1)^N F_N`; the dual formula with `m ≤ 2` gives `E_d`) and Part IV (`B_p`,
`E_{o4}`, `E_{d4}`, and the definition of `E₃₄`).

Strategy. There are two formulas for each readout.
* *Original formula* (only `p > 3`): the rows `A, B, C` of `𝓒_N` have valuations `≥ A_p`,
  `≥ max(B_p, C_p)` and `≥ C_p`. The readouts are cofactors divided by `det 𝓒_N = -6(-1)^N F_N`:
  `p^{(3)}` uses the rows `C, A`, `q` uses `A, B`, and `p^{(4)}` uses `B, C`. So
  `v_p(p^{(3)}), v_p(q) ≥ -E_o` and `v_p(p^{(4)}) ≥ -E_{o4}`.
* *Dual formulas* (every prime): `(-1)^N 3 𝓛_{-11N-1}[Q_{Nj} R*_N] = Z₃ q_{Nj} - p^{(3)}_{Nj}` and
  (6) `(-1)^N 𝓜_{-10N-1}[Q_{Nj} R*_N] = Z₄ q_{Nj} - p^{(4)}_{Nj}`. The pole argument with pole
  orders `≤ 2` gives `v_p ≥ -E_d` and `v_p ≥ -E_{d4}` respectively.
At each prime take the better bound. This is exactly how `E₃₄` is defined.

| # | Supporting lemma            | Est. lines | Directly from PDF? |
|---|-----------------------------|-----------:|--------------------|
| 1 | `coeffMat_row_valuations`   |   (proved) | Partially          |
| 2 | `padicValRat_F`             |   (proved) | Yes                |
| 3 | `original_bounds`           |   (proved) | Yes (given [1], [2], [9]) |
| 4 | `dual_first_identity`       |       2500 | No (needs the CMF) |
| 5 | `pairing_identity`          | imported from `pairing_identity.lean` | No (needs the CMF) |
| 6 | `dual_bounds_p3_q`          |   (proved) | Partially          |
| 7 | `dual_bound_p4`             |   (proved) | Partially          |
| 8 | `Ed_Ed4_eq_zero_of_lt`      |   (proved) | Yes                |
| 9 | `det_V_eq`                  | imported from `det_V_eq.lean` | No (needs the CMF) |

[1], [2] are ingredients of [3]; [4] of [6]; [5] of [7]. The main theorem uses [3], [6], [7],
[8]; [9] is an ingredient of [3] (added: [3] also needs `det V_N = F_N`). Total estimate for
the open lemmas (excluding [5], [9]): ≈ 3600 lines, of which ≈ 2500 are the CMF transport in
[4]. That part is shared with `pairing_identity.lean` [4] and `det_V_eq.lean` [5].
[2], [3], [8] are proved. They use `readouts_eq_cross_rat` from `cross_product_readout.lean` and
the helper lemmas of `ZetasAux.lean`. The declarations of this file live in the namespace
`ZetasIrr.BP`.

[5] and [9] are the main theorems of `pairing_identity.lean` and `det_V_eq.lean`, which are
imported (same namespace `ZetasIrr.BP`).
-/
import ZetasAux
import det_V_eq
import pairing_identity
import CMF_main

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries

noncomputable section

namespace ZetasIrr.BP

/-! ### Supporting lemmas for [1]: `p`-adic bounds on Laurent coefficients -/

open Aux in
/-- `ValGE` for finite sums. -/
theorem ValGE_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℚ)
    (h : ∀ i ∈ s, ValGE p a (f i)) : ValGE p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self x s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A power series `f` has `p`-adic base `B` and slope `L`: `v_p(f_n) ≥ B - n L` for all `n`. -/
def PSBound (p : ℕ) (B L : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, Aux.ValGE p (B - n * L) (PowerSeries.coeff n f)

section PSBound

variable {p : ℕ} [Fact p.Prime]

theorem PSBound.mul {B B' L : ℤ} {f g : PowerSeries ℚ} (hf : PSBound p B L f)
    (hg : PSBound p B' L g) : PSBound p (B + B') L (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine ValGE_sum _ _ _ fun x hx => ?_
  have hxn : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have := (hf x.1).mul (hg x.2)
  refine this.mono (le_of_eq ?_)
  rw [← hxn]; push_cast; ring

theorem PSBound.inv {B L : ℤ} {f : PowerSeries ℚ} (hf : PSBound p B L f)
    (h0 : PowerSeries.constantCoeff f ≠ 0) (hv : padicValRat p (PowerSeries.constantCoeff f) = B) :
    PSBound p (-B) L f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · subst hn
      right
      rw [padicValRat.inv, hv]; simp
    · have h1 : Aux.ValGE p (-B) (-(PowerSeries.constantCoeff f)⁻¹) := by
        right; rw [padicValRat.neg, padicValRat.inv, hv]
      have h2 : Aux.ValGE p (-(n : ℤ) * L)
          (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, if x.2 < n then
            PowerSeries.coeff x.1 f * PowerSeries.coeff x.2 f⁻¹ else 0) := by
        refine ValGE_sum _ _ _ fun x hx => ?_
        have hxn : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        split_ifs with hlt
        · have := (hf x.1).mul (ih x.2 hlt)
          refine this.mono (le_of_eq ?_)
          rw [← hxn]; push_cast; ring
        · exact Or.inl rfl
      have := h1.mul h2
      refine this.mono (le_of_eq ?_)
      ring

theorem PSBound.mono {B B' L : ℤ} {f : PowerSeries ℚ} (hf : PSBound p B L f) (hB : B' ≤ B) :
    PSBound p B' L f := fun n => (hf n).mono (by linarith)

/-- A polynomial with `p`-integral coefficients has base `0` for every slope `L ≥ 0`. -/
theorem PSBound.of_int_coeffs {L : ℤ} (hL : 0 ≤ L) (q : ℚ[X])
    (hq : ∀ n, Aux.ValGE p 0 (q.coeff n)) : PSBound p 0 L (q : PowerSeries ℚ) := by
  intro n
  rw [Polynomial.coeff_coe]
  exact (hq n).mono (by nlinarith)

/-- The linear factor `X - a` with `v_p(a) ≤ L`. -/
theorem PSBound.X_sub_C {L : ℤ} (a : ℚ) (ha : a ≠ 0) (hL : padicValRat p a ≤ L) :
    PSBound p (padicValRat p a) L ((Polynomial.X - Polynomial.C a : ℚ[X]) : PowerSeries ℚ) := by
  intro n
  rw [Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  rcases n with _ | _ | n
  · right; simp [padicValRat.neg]
  · right; simp only [Nat.cast_one, one_mul]
    norm_num
    linarith
  · left; simp

end PSBound

/-! ### Laurent coefficients from an explicit representation -/


/-- The Laurent coefficients of `p/((X-h)^m E)` at `h`, for `E(h) ≠ 0`. -/
theorem pfCoeff_div_eq (p E : ℚ[X]) (h : ℚ) (m : ℕ) (hE : E.eval h ≠ 0) (r : ℕ) :
    pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ p /
        algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ m * E)) h r =
      if r ≤ m then PowerSeries.coeff (m - r)
        ((taylor h p : PowerSeries ℚ) * (taylor h E : PowerSeries ℚ)⁻¹) else 0 := by
  have hden : taylor h ((Polynomial.X - Polynomial.C h) ^ m * E) =
      Polynomial.X ^ m * taylor h E := by
    rw [Polynomial.taylor_mul, Polynomial.taylor_pow, Aux.taylor_X_sub_C_self]
  set Pn : PowerSeries ℚ := (taylor h p : PowerSeries ℚ) with hPn
  set Pe : PowerSeries ℚ := (taylor h E : PowerSeries ℚ) with hPe
  have hPe0 : PowerSeries.constantCoeff Pe ≠ 0 := by
    rw [hPe, Polynomial.constantCoeff_coe, Polynomial.taylor_coeff_zero]; exact hE
  have hcoe : algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (RatFunc.laurent h (algebraMap ℚ[X] ℚ⟮X⟯ p /
      algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ m * E))) =
      HahnSeries.single (-(m : ℤ)) 1 * ((Pn * Pe⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
    rw [RatFunc.laurent_div, map_div₀, Aux.coe_algebraMap_poly, Aux.coe_algebraMap_poly, hden,
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
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · congr 2; omega
  · omega

/-- Splitting off the factor `(X - h)^{count h}` of a product of linear factors. -/
theorem prod_X_sub_C_split (S : Multiset ℚ) (h : ℚ) :
    (S.map fun a => Polynomial.X - Polynomial.C a).prod =
      (Polynomial.X - Polynomial.C h) ^ (S.count h) *
        ((S.filter (· ≠ h)).map fun a => Polynomial.X - Polynomial.C a).prod := by
  conv_lhs => rw [← Multiset.filter_add_not (· = h) S]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.prod_replicate]

theorem eval_prod_X_sub_C (S : Multiset ℚ) (x : ℚ) :
    ((S.map fun a => Polynomial.X - Polynomial.C a).prod).eval x = (S.map fun a => x - a).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp

theorem taylor_prod_X_sub_C (h : ℚ) (S : Multiset ℚ) :
    taylor h (S.map fun a => Polynomial.X - Polynomial.C a).prod =
      (S.map fun a => Polynomial.X - Polynomial.C (a - h)).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.taylor_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]
    congr 1
    rw [map_sub, Polynomial.taylor_X, Polynomial.taylor_C, map_sub]
    ring

theorem coe_prod_X_sub_C (S : Multiset ℚ) :
    (((S.map fun a => Polynomial.X - Polynomial.C a).prod : ℚ[X]) : PowerSeries ℚ) =
      (S.map fun a => ((Polynomial.X - Polynomial.C a : ℚ[X]) : PowerSeries ℚ)).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

section PSBound2

variable {p : ℕ} [Fact p.Prime]

theorem PSBound.one {L : ℤ} (hL : 0 ≤ L) : PSBound p 0 L (1 : PowerSeries ℚ) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · right; simp; nlinarith
  · left; rfl

/-- Products of linear factors `X - a`, `a ≠ 0`, `v_p(a) ≤ L`. -/
theorem PSBound.prod_X_sub_C {L : ℤ} (hL : 0 ≤ L) (S : Multiset ℚ) (hS : ∀ a ∈ S, a ≠ 0)
    (hv : ∀ a ∈ S, padicValRat p a ≤ L) :
    PSBound p (S.map fun a => padicValRat p a).sum L
      (S.map fun a => ((Polynomial.X - Polynomial.C a : ℚ[X]) : PowerSeries ℚ)).prod := by
  induction S using Multiset.induction_on with
  | empty => simpa using PSBound.one hL
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (PSBound.X_sub_C a (hS a (Multiset.mem_cons_self a S)) (hv a (Multiset.mem_cons_self a S))).mul
      (ih (fun b hb => hS b (Multiset.mem_cons_of_mem hb)) (fun b hb => hv b (Multiset.mem_cons_of_mem hb)))

theorem padicValRat_prod_neg (S : Multiset ℚ) (hS : ∀ a ∈ S, a ≠ 0) :
    padicValRat p (S.map fun a => -a).prod = (S.map fun a => padicValRat p a).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [padicValRat.mul (neg_ne_zero.mpr (hS a (Multiset.mem_cons_self a S)))
        (Multiset.prod_ne_zero fun h => by
          obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h
          exact hS b (Multiset.mem_cons_of_mem hb) (neg_eq_zero.mp hb0)),
      padicValRat.neg, ih fun b hb => hS b (Multiset.mem_cons_of_mem hb)]

theorem constantCoeff_prod_X_sub_C (S : Multiset ℚ) :
    PowerSeries.constantCoeff
      (S.map fun a => ((Polynomial.X - Polynomial.C a : ℚ[X]) : PowerSeries ℚ)).prod =
      (S.map fun a => -a).prod := by
  rw [← coe_prod_X_sub_C, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    eval_prod_X_sub_C]
  congr 1
  exact Multiset.map_congr rfl fun a _ => by ring

/-- Inverse of a product of linear factors. -/
theorem PSBound.inv_prod_X_sub_C {L : ℤ} (hL : 0 ≤ L) (S : Multiset ℚ) (hS : ∀ a ∈ S, a ≠ 0)
    (hv : ∀ a ∈ S, padicValRat p a ≤ L) :
    PSBound p (-(S.map fun a => padicValRat p a).sum) L
      ((S.map fun a => ((Polynomial.X - Polynomial.C a : ℚ[X]) : PowerSeries ℚ)).prod)⁻¹ := by
  refine (PSBound.prod_X_sub_C hL S hS hv).inv ?_ ?_
  · rw [constantCoeff_prod_X_sub_C]
    exact Multiset.prod_ne_zero fun h => by
      obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h
      exact hS b hb (neg_eq_zero.mp hb0)
  · rw [constantCoeff_prod_X_sub_C, padicValRat_prod_neg S hS]

end PSBound2

/-! ### Valuations of products of consecutive integers -/

section Consecutive

variable {p : ℕ} [Fact p.Prime]

theorem padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      padicValRat.mul (hf x (Finset.mem_insert_self x s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `v_p((m+1)(m+2)⋯(m+n)) = f_p(m+n) - f_p(m)`. -/
theorem padicValNat_ascFactorial (m n : ℕ) :
    (padicValNat p ((m + 1).ascFactorial n) : ℤ) = fp p ((m + n : ℕ) : ℤ) - fp p (m : ℤ) := by
  have h := Nat.factorial_mul_ascFactorial m n
  have h2 : (padicValNat p (m.factorial * (m + 1).ascFactorial n) : ℤ) =
      padicValNat p (m + n).factorial := by rw [h]
  rw [padicValNat.mul (Nat.factorial_ne_zero m) (Nat.ascFactorial_pos _ _).ne', Nat.cast_add] at h2
  unfold fp
  simp only [Int.toNat_natCast]
  omega

/-- `v_p` of `∏_{j<n} (m + 1 + j)`. -/
theorem padicValRat_prod_consecutive (m n : ℕ) :
    padicValRat p (∏ j ∈ Finset.range n, (((m + 1 + j : ℕ) : ℤ) : ℚ)) =
      fp p ((m + n : ℕ) : ℤ) - fp p (m : ℤ) := by
  have : ∏ j ∈ Finset.range n, (((m + 1 + j : ℕ) : ℤ) : ℚ) = (((m + 1).ascFactorial n : ℕ) : ℚ) := by
    rw [Nat.ascFactorial_eq_prod_range]; push_cast; rfl
  rw [this, padicValRat.of_nat, padicValNat_ascFactorial]

/-- `v_p` of `∏_{j<n} (-(m + 1 + j))`. -/
theorem padicValRat_prod_consecutive_neg (m n : ℕ) :
    padicValRat p (∏ j ∈ Finset.range n, -(((m + 1 + j : ℕ) : ℤ) : ℚ)) =
      fp p ((m + n : ℕ) : ℤ) - fp p (m : ℤ) := by
  rw [padicValRat_finset_prod _ _ (fun j _ => neg_ne_zero.mpr (by positivity)),
    ← padicValRat_prod_consecutive, padicValRat_finset_prod _ _ (fun j _ => by positivity)]
  exact Finset.sum_congr rfl fun j _ => padicValRat.neg _

/-- `Icc a b` in `ℤ` as the image of `range`. -/
theorem Icc_eq_image_range (a b : ℤ) :
    Finset.Icc a b = (Finset.range (b + 1 - a).toNat).image (fun j : ℕ => a + j) := by
  ext r
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    exact ⟨(r - a).toNat, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

theorem Icc_eq_image_range' (a b : ℤ) :
    Finset.Icc a b = (Finset.range (b + 1 - a).toNat).image (fun j : ℕ => b - j) := by
  ext r
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    exact ⟨(b - r).toNat, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

theorem prod_Icc_eq_prod_range (a b : ℤ) (g : ℤ → ℚ) :
    ∏ r ∈ Finset.Icc a b, g r = ∏ j ∈ Finset.range (b + 1 - a).toNat, g (a + j) := by
  rw [Icc_eq_image_range, Finset.prod_image]
  intro x _ y _ hxy
  exact_mod_cast (add_left_cancel hxy : (x : ℤ) = y)

theorem prod_Icc_eq_prod_range' (a b : ℤ) (g : ℤ → ℚ) :
    ∏ r ∈ Finset.Icc a b, g r = ∏ j ∈ Finset.range (b + 1 - a).toNat, g (b - j) := by
  rw [Icc_eq_image_range', Finset.prod_image]
  intro x _ y _ hxy
  exact_mod_cast (sub_right_inj.mp hxy : (x : ℤ) = y)

/-- `v_p(∏_{a ≤ r ≤ b} (r - k)) = f_p(b - k) - f_p(a - k - 1)` when `k < a`. -/
theorem padicValRat_prod_sub_of_lt (a b k : ℤ) (hk : k < a) (hab : a ≤ b + 1) :
    padicValRat p (∏ r ∈ Finset.Icc a b, ((r - k : ℤ) : ℚ)) = fp p (b - k) - fp p (a - k - 1) := by
  rw [prod_Icc_eq_prod_range]
  have e : ∀ j : ℕ, ((a + (j : ℤ) - k : ℤ) : ℚ) = ((((a - k - 1).toNat + 1 + j : ℕ) : ℤ) : ℚ) := by
    intro j; congr 1; omega
  simp_rw [e]
  rw [padicValRat_prod_consecutive]
  have e1 : (((a - k - 1).toNat + (b + 1 - a).toNat : ℕ) : ℤ) = b - k := by omega
  have e2 : (((a - k - 1).toNat : ℕ) : ℤ) = a - k - 1 := by omega
  rw [e1, e2]

/-- `v_p(∏_{a ≤ r ≤ b} (r - k)) = f_p(k - a) - f_p(k - b - 1)` when `b < k`. -/
theorem padicValRat_prod_sub_of_gt (a b k : ℤ) (hk : b < k) (hab : a ≤ b + 1) :
    padicValRat p (∏ r ∈ Finset.Icc a b, ((r - k : ℤ) : ℚ)) = fp p (k - a) - fp p (k - b - 1) := by
  rw [prod_Icc_eq_prod_range']
  have e : ∀ j : ℕ, ((b - (j : ℤ) - k : ℤ) : ℚ) = -((((k - b - 1).toNat + 1 + j : ℕ) : ℤ) : ℚ) := by
    intro j; rw [← Int.cast_neg]; congr 1; omega
  simp_rw [e]
  rw [padicValRat_prod_consecutive_neg]
  have e1 : (((k - b - 1).toNat + (b + 1 - a).toNat : ℕ) : ℤ) = k - a := by omega
  have e2 : (((k - b - 1).toNat : ℕ) : ℤ) = k - b - 1 := by omega
  rw [e1, e2]

theorem fp_zero : fp p 0 = 0 := by simp [fp]

/-- The valuation of `∏_{a ≤ r ≤ b, r ≠ k} (r - k)` is `G_p(k; [a, b])`. -/
theorem padicValRat_prod_sub_eq_Gp (a b k : ℤ) (hab : a ≤ b + 1) :
    padicValRat p (∏ r ∈ (Finset.Icc a b).filter (· ≠ k), ((r - k : ℤ) : ℚ)) = Gp p k a b := by
  unfold Gp
  split_ifs with h1 h2
  · rw [Finset.filter_true_of_mem (fun r hr => by have := (Finset.mem_Icc.mp hr).1; omega)]
    exact padicValRat_prod_sub_of_lt a b k h1 hab
  · rw [Finset.filter_true_of_mem (fun r hr => by have := (Finset.mem_Icc.mp hr).2; omega)]
    exact padicValRat_prod_sub_of_gt a b k h2 hab
  · push Not at h1 h2
    have hsplit : (Finset.Icc a b).filter (· ≠ k) = Finset.Icc a (k - 1) ∪ Finset.Icc (k + 1) b := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc a (k - 1)) (Finset.Icc (k + 1) b) := by
      rw [Finset.disjoint_left]
      intro r hr hr'
      simp only [Finset.mem_Icc] at hr hr'
      omega
    rw [hsplit, Finset.prod_union hdisj,
      padicValRat.mul (Finset.prod_ne_zero_iff.mpr fun r hr => by
          have := (Finset.mem_Icc.mp hr).2; exact_mod_cast (by omega : (r - k : ℤ) ≠ 0))
        (Finset.prod_ne_zero_iff.mpr fun r hr => by
          have := (Finset.mem_Icc.mp hr).1; exact_mod_cast (by omega : (r - k : ℤ) ≠ 0)),
      padicValRat_prod_sub_of_gt a (k - 1) k (by omega) (by omega),
      padicValRat_prod_sub_of_lt (k + 1) b k (by omega) (by omega)]
    rw [show k - (k - 1) - 1 = 0 by ring, show k + 1 - k - 1 = 0 by ring, fp_zero]
    ring

end Consecutive

/-! ### The pole and zero multisets of the kernel -/

section Kernel

variable {p : ℕ} [Fact p.Prime]

/-- `v_p(x) ≤ ℓ_p(M)` for an integer `1 ≤ x ≤ M`. -/
theorem padicValRat_int_le_ellp {x M : ℤ} (hx : 0 < x) (hM : x ≤ M) :
    padicValRat p (x : ℚ) ≤ ellp p M := by
  have hp := (Fact.out : p.Prime)
  rw [Aux.ellp_eq_log hp]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = n := ⟨x.toNat, by omega⟩
  rw [Int.cast_natCast, padicValRat.of_nat]
  have h1 : p ^ padicValNat p n ≤ M.toNat :=
    (Nat.le_of_dvd (by omega) pow_padicValNat_dvd).trans (by omega)
  exact_mod_cast Nat.le_log_of_pow_le hp.one_lt h1

theorem padicValRat_int_le_ellp' {x M : ℤ} (hx : x ≠ 0) (hM : |x| ≤ M) :
    padicValRat p (x : ℚ) ≤ ellp p M := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hM' : -x ≤ M := by rw [abs_of_neg h] at hM; exact hM
    have := padicValRat_int_le_ellp (p := p) (x := -x) (M := M) (by omega) hM'
    rwa [Int.cast_neg, padicValRat.neg] at this
  · exact padicValRat_int_le_ellp h (by rw [abs_of_pos h] at hM; exact hM)

/-- `v_p(∏_{i<n} (m - i)) = f_p(m) - f_p(m - n)` for `n ≤ m`. -/
theorem padicValRat_prod_desc (m n : ℕ) (h : n ≤ m) :
    padicValRat p (∏ i ∈ Finset.range n, ((m - i : ℕ) : ℚ)) =
      fp p (m : ℤ) - fp p ((m - n : ℕ) : ℤ) := by
  have e : ∏ i ∈ Finset.range n, ((m - i : ℕ) : ℚ) = ((m.descFactorial n : ℕ) : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range]; push_cast; rfl
  rw [e, padicValRat.of_nat]
  have h2 : (padicValNat p ((m - n).factorial * m.descFactorial n) : ℤ) =
      padicValNat p m.factorial := by rw [Nat.factorial_mul_descFactorial h]
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.descFactorial_pos.mpr h).ne', Nat.cast_add] at h2
  unfold fp
  simp only [Int.toNat_natCast]
  omega

/-- The multiset `{-(c+i) : i < n}` of an interval block. -/
def blk (c n : ℕ) : Multiset ℚ := (Multiset.range n).map fun i : ℕ => -((c : ℚ) + i)

theorem count_blk (c n k : ℕ) :
    (blk c n).count (-(k : ℚ)) = if c ≤ k ∧ k < c + n then 1 else 0 := by
  unfold blk
  rw [Multiset.count_map]
  have hiff : ∀ i : ℕ, (-(k : ℚ) = -((c : ℚ) + i)) ↔ (c ≤ k ∧ i = k - c) := by
    intro i
    constructor
    · intro h
      have : (k : ℚ) = c + i := by linarith
      have : k = c + i := by exact_mod_cast this
      omega
    · rintro ⟨hck, rfl⟩
      push_cast
      rw [Nat.cast_sub hck]; ring
  rw [Multiset.filter_congr (fun i _ => hiff i)]
  have hfin : Multiset.filter (fun i : ℕ => c ≤ k ∧ i = k - c) (Multiset.range n) =
      ((Finset.range n).filter (fun i : ℕ => c ≤ k ∧ i = k - c)).val := rfl
  rw [hfin, Finset.card_val]
  by_cases hck : c ≤ k
  · have : (Finset.range n).filter (fun i : ℕ => c ≤ k ∧ i = k - c) =
        (Finset.range n).filter (fun i => i = k - c) :=
      Finset.filter_congr (fun i _ => by simp [hck])
    rw [this, Finset.filter_eq']
    by_cases hkn : k - c ∈ Finset.range n
    · rw [ite_eq_left hkn, Finset.card_singleton,
        ite_eq_left ⟨hck, by have := Finset.mem_range.mp hkn; omega⟩]
    · rw [ite_eq_right hkn, Finset.card_empty,
        ite_eq_right (fun h => hkn (Finset.mem_range.mpr (by omega)))]
  · rw [Finset.filter_false_of_mem (fun i _ h => hck h.1), Finset.card_empty,
      ite_eq_right (fun h => hck h.1)]

/-- The valuation sum over the other poles of a block is `G_p`. -/
theorem sum_val_blk (c n k : ℕ) :
    (((blk c n).filter (· ≠ -(k : ℚ))).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      Gp p k c ((c : ℤ) + n - 1) := by
  -- left side as a sum over `range n`
  have hL : (((blk c n).filter (· ≠ -(k : ℚ))).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      ∑ i ∈ Finset.range n, if ((c : ℤ) + i ≠ k) then padicValRat p (((c : ℤ) + i - k : ℤ) : ℚ)
        else 0 := by
    unfold blk
    rw [Multiset.filter_map, Multiset.map_map]
    have hfin : Multiset.filter ((fun a : ℚ => a ≠ -(k : ℚ)) ∘ fun i : ℕ => -((c : ℚ) + i))
        (Multiset.range n) = ((Finset.range n).filter
          (fun i : ℕ => (fun a : ℚ => a ≠ -(k : ℚ)) (-((c : ℚ) + i)))).val := rfl
    rw [hfin, ← Finset.sum_eq_multiset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (-((c : ℚ) + i) ≠ -(k : ℚ)) ↔ ((c : ℤ) + i ≠ k) := by
      constructor
      · intro h h'
        apply h
        have : ((c : ℤ) + i : ℤ) = k := h'
        have : ((c : ℚ) + i) = k := by exact_mod_cast this
        rw [this]
      · intro h h'
        apply h
        have : ((c : ℚ) + i) = k := by linarith
        exact_mod_cast this
    simp only [Function.comp]
    by_cases h : (c : ℤ) + i ≠ k
    · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
      rw [show -((c : ℚ) + i) - -(k : ℚ) = -((((c : ℤ) + i - k : ℤ) : ℚ)) by push_cast; ring,
        padicValRat.neg]
    · rw [ite_eq_right (fun h' => h (hc.mp h')), ite_eq_right h]
  -- right side
  have hR : Gp p k c ((c : ℤ) + n - 1) =
      ∑ i ∈ Finset.range n, if ((c : ℤ) + i ≠ k) then padicValRat p (((c : ℤ) + i - k : ℤ) : ℚ)
        else 0 := by
    have hne : ∀ r ∈ (Finset.Icc (c : ℤ) ((c : ℤ) + n - 1)).filter (· ≠ (k : ℤ)),
        ((r - k : ℤ) : ℚ) ≠ 0 := fun r hr => by
      have := (Finset.mem_filter.mp hr).2
      exact_mod_cast (by omega : (r - k : ℤ) ≠ 0)
    have hinj : Set.InjOn (fun j : ℕ => (c : ℤ) + j)
        ↑(Finset.range ((c : ℤ) + n - 1 + 1 - c).toNat) := fun x _ y _ hxy => by
      exact_mod_cast (add_left_cancel hxy : (x : ℤ) = y)
    rw [← padicValRat_prod_sub_eq_Gp (c : ℤ) ((c : ℤ) + n - 1) k (by omega),
      padicValRat_finset_prod _ _ hne, Finset.sum_filter, Icc_eq_image_range,
      Finset.sum_image hinj]
    have : ((c : ℤ) + n - 1 + 1 - c).toNat = n := by omega
    rw [this]
  rw [hL, hR]

end Kernel

/-! ### The Laurent coefficients of `(-t)^j R_N(t)` at `t = -k` -/

section KernelBound

variable {p : ℕ} [Fact p.Prime]

theorem ValGE_int (z : ℤ) : Aux.ValGE p 0 (z : ℚ) := by
  by_cases hz : z = 0
  · left; simp [hz]
  · right; rw [padicValRat.of_int]; exact Int.natCast_nonneg _

theorem poleSet_eq (N : ℕ) :
    poleSet N = blk 0 (10 * N + 2) + blk N (10 * N + 1) + blk (2 * N) (10 * N + 1) := by
  simp [poleSet, blk]

theorem count_poleSet (N k : ℕ) : ((poleSet N).count (-(k : ℚ)) : ℤ) = mult (Io N) k := by
  rw [poleSet_eq, Multiset.count_add, Multiset.count_add, count_blk, count_blk, count_blk]
  simp only [mult, Io, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  push_cast
  split_ifs <;> omega

/-- The valuation sum over the other poles. -/
theorem sum_val_poles (N k : ℕ) :
    (((poleSet N).filter (· ≠ -(k : ℚ))).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      ((Io N).map fun ab => Gp p k ab.1 ab.2).sum := by
  rw [poleSet_eq, Multiset.filter_add, Multiset.filter_add, Multiset.map_add, Multiset.map_add,
    Multiset.sum_add, Multiset.sum_add, sum_val_blk, sum_val_blk, sum_val_blk]
  simp only [Io, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  have e1 : (0 : ℤ) + (10 * (N : ℤ) + 2) - 1 = 10 * N + 1 := by ring
  have e2 : (N : ℤ) + (10 * (N : ℤ) + 1) - 1 = 11 * N := by ring
  have e3 : 2 * (N : ℤ) + (10 * (N : ℤ) + 1) - 1 = 12 * N := by ring
  rw [e1, e2, e3]
  ring

/-- The valuation sum over the zeros. -/
theorem sum_val_zeros (N k : ℕ) :
    ((zeroSet N).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      fp p ((k : ℤ) + 17 * N) + fp p ((k : ℤ) + 16 * N) - fp p ((k : ℤ) + 2 * N) -
        fp p ((k : ℤ) + N) := by
  have key : ∀ c n : ℕ, n ≤ c → ((Multiset.range n).map fun i : ℕ =>
      padicValRat p (-((-(c : ℚ)) + i) - (-(k : ℚ)))).sum =
      fp p ((k : ℤ) + c) - fp p ((k : ℤ) + c - n) := by
    intro c n hcn
    have e : ∀ i ∈ Finset.range n, padicValRat p (-((-(c : ℚ)) + i) - (-(k : ℚ))) =
        padicValRat p (((k + c - i : ℕ) : ℚ)) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have : i ≤ k + c := by omega
      congr 1
      push_cast [this]
      ring
    have hne : ∀ i ∈ Finset.range n, (((k + c - i : ℕ) : ℚ)) ≠ 0 := fun i hi => by
      have := Finset.mem_range.mp hi
      exact_mod_cast (by omega : k + c - i ≠ 0)
    rw [show Multiset.range n = (Finset.range n).val from rfl, ← Finset.sum_eq_multiset_sum,
      Finset.sum_congr rfl e, ← padicValRat_finset_prod _ _ hne,
      padicValRat_prod_desc (k + c) n (by omega)]
    congr 2 <;> push_cast <;> omega
  unfold zeroSet
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_map]
  have h1 := key (17 * N) (15 * N) (by omega)
  have h2 := key (16 * N) (15 * N) (by omega)
  simp only [Function.comp] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  rw [show (-17 * (N : ℚ)) = -(17 * (N : ℚ)) by ring, show (-16 * (N : ℚ)) = -(16 * (N : ℚ)) by ring,
    h1, h2]
  have e1 : (k : ℤ) + 17 * N - 15 * N = k + 2 * N := by ring
  have e2 : (k : ℤ) + 16 * N - 15 * N = k + N := by ring
  rw [e1, e2]
  ring

/-- **Per-pole Laurent bound** (PDF Lemma 2): at the pole `-k` of order `m = m_o(k)`,
`v_p(c_{-k,r}) ≥ V_o(k) - (m - r) ℓ_p(k + 17N)` for `1 ≤ r`. -/
theorem pfCoeff_linFormKernel_valuation (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) (k r : ℕ) (hr : 1 ≤ r) :
    (mult (Io N) k < r → pfCoeff (linFormKernel N j) (-(k : ℚ)) r = 0) ∧
    Aux.ValGE p (Vo N p k - (mult (Io N) k - r) * ellp p ((k : ℤ) + 17 * N))
      (pfCoeff (linFormKernel N j) (-(k : ℚ)) r) := by
  set h : ℚ := -(k : ℚ) with hh
  set m : ℕ := (poleSet N).count h with hm
  set L : ℤ := ellp p ((k : ℤ) + 17 * N) with hL
  have hL0 : 0 ≤ L := Aux.ellp_nonneg _ _
  set E : ℚ[X] := ((poleSet N).filter (· ≠ h)).map (fun a => Polynomial.X - Polynomial.C a) |>.prod
    with hE
  have hEval : E.eval h ≠ 0 := by
    rw [hE, eval_prod_X_sub_C]
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.mp h0
    have := (Multiset.mem_filter.mp ha).2
    exact this (by linarith)
  have hden : ((poleSet N).map fun a => Polynomial.X - Polynomial.C a).prod =
      (Polynomial.X - Polynomial.C h) ^ m * E := prod_X_sub_C_split _ h
  rw [linFormKernel_eq, hden, pfCoeff_div_eq _ _ h m hEval r]
  have hmult : (m : ℤ) = mult (Io N) k := count_poleSet N k
  split_ifs with hrm
  · refine ⟨fun hlt => by omega, ?_⟩
    -- the power series `P = taylor h num * (taylor h E)⁻¹`
    -- integer coefficients of `(-(X + C h))^j`
    have hA : PSBound p 0 L (((-(Polynomial.X + Polynomial.C h)) ^ (j : ℕ) : ℚ[X]) : PowerSeries ℚ) := by
      refine PSBound.of_int_coeffs hL0 _ fun n => ?_
      rw [neg_pow, show ((-1 : ℚ[X]) ^ (j : ℕ)) = Polynomial.C ((-1) ^ (j : ℕ)) by simp,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, hh]
      have : ((-1 : ℚ) ^ (j : ℕ) * ((-(k : ℚ)) ^ ((j : ℕ) - n) * ((j : ℕ).choose n : ℚ))) =
          (((-1 : ℤ) ^ (j : ℕ) * ((-(k : ℤ)) ^ ((j : ℕ) - n) * ((j : ℕ).choose n : ℤ)) : ℤ) : ℚ) := by
        push_cast; ring
      rw [this]
      exact ValGE_int _
    -- the zeros
    have hzero_ne : ∀ a ∈ zeroSet N, a - h ≠ 0 := by
      intro a ha
      simp only [zeroSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at ha
      rcases ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      · rw [hh]; push_cast
        have : (i : ℚ) < 15 * N := by exact_mod_cast hi
        linarith
    have hzero_le : ∀ a ∈ zeroSet N, padicValRat p (a - h) ≤ L := by
      intro a ha
      simp only [zeroSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at ha
      rcases ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · have e : -((-17 * (N : ℚ)) + i) - h = (((k : ℤ) + 17 * N - i : ℤ) : ℚ) := by
          rw [hh]; push_cast; ring
        rw [e]
        exact padicValRat_int_le_ellp (by omega) (by omega)
      · have e : -((-16 * (N : ℚ)) + i) - h = (((k : ℤ) + 16 * N - i : ℤ) : ℚ) := by
          rw [hh]; push_cast; ring
        rw [e]
        exact padicValRat_int_le_ellp (by omega) (by omega)
    have hZ : PSBound p ((zeroSet N).map fun a => padicValRat p (a - h)).sum L
        (((((zeroSet N).map fun a => Polynomial.X - Polynomial.C (a - h)).prod : ℚ[X])) :
          PowerSeries ℚ) := by
      have e : ((zeroSet N).map fun a => Polynomial.X - Polynomial.C (a - h)) =
          ((zeroSet N).map fun a => a - h).map fun b => Polynomial.X - Polynomial.C b := by
        rw [Multiset.map_map]; rfl
      rw [e, coe_prod_X_sub_C]
      have := PSBound.prod_X_sub_C (p := p) hL0 ((zeroSet N).map fun a => a - h)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hzero_ne a ha)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hzero_le a ha)
      rwa [Multiset.map_map] at this
    -- the other poles
    have hpole_ne : ∀ a ∈ (poleSet N).filter (· ≠ h), a - h ≠ 0 := fun a ha =>
      sub_ne_zero.mpr (Multiset.mem_filter.mp ha).2
    have hpole_le : ∀ a ∈ (poleSet N).filter (· ≠ h), padicValRat p (a - h) ≤ L := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Multiset.mem_filter.mp ha
      simp only [poleSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at ha1
      have key : ∀ c i : ℕ, (c : ℚ) + i ≠ k → c + i ≤ 12 * N →
          padicValRat p (-((c : ℚ) + i) - h) ≤ L := by
        intro c i hne hle
        have e : -((c : ℚ) + i) - h = (((k : ℤ) - c - i : ℤ) : ℚ) := by rw [hh]; push_cast; ring
        rw [e]
        refine padicValRat_int_le_ellp' ?_ ?_
        · intro h0
          apply hne
          have : ((c : ℤ) + i : ℤ) = k := by omega
          exact_mod_cast this
        · rw [abs_le]; constructor <;> omega
      rcases ha1 with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
      · have := key 0 i (fun h' => ha2 (by rw [hh, ← h']; push_cast; ring)) (by omega)
        push_cast at this
        exact this
      · exact key N i (fun h' => ha2 (by rw [hh, ← h'])) (by omega)
      · have := key (2 * N) i (fun h' => ha2 (by rw [hh, ← h']; push_cast; ring)) (by omega)
        push_cast at this
        exact this
    have hEinv : PSBound p (-(((poleSet N).filter (· ≠ h)).map fun a => padicValRat p (a - h)).sum) L
        (((taylor h E : ℚ[X]) : PowerSeries ℚ))⁻¹ := by
      rw [hE, taylor_prod_X_sub_C]
      have e : (((poleSet N).filter (· ≠ h)).map fun a => Polynomial.X - Polynomial.C (a - h)) =
          (((poleSet N).filter (· ≠ h)).map fun a => a - h).map fun b =>
            Polynomial.X - Polynomial.C b := by
        rw [Multiset.map_map]; rfl
      rw [e, coe_prod_X_sub_C]
      have := PSBound.inv_prod_X_sub_C (p := p) hL0 (((poleSet N).filter (· ≠ h)).map fun a => a - h)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hpole_ne a ha)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hpole_le a ha)
      rwa [Multiset.map_map] at this
    -- the numerator
    have hnum : ((taylor h ((-Polynomial.X) ^ (j : ℕ) *
        ((zeroSet N).map fun a => Polynomial.X - Polynomial.C a).prod) : ℚ[X]) : PowerSeries ℚ) =
        (((-(Polynomial.X + Polynomial.C h)) ^ (j : ℕ) : ℚ[X]) : PowerSeries ℚ) *
          (((((zeroSet N).map fun a => Polynomial.X - Polynomial.C (a - h)).prod : ℚ[X])) :
            PowerSeries ℚ) := by
      rw [Polynomial.taylor_mul, Polynomial.taylor_pow, map_neg, Polynomial.taylor_X,
        taylor_prod_X_sub_C, Polynomial.coe_mul]
    rw [hnum]
    have hP := (hA.mul hZ).mul hEinv
    have hbase : (0 : ℤ) + ((zeroSet N).map fun a => padicValRat p (a - h)).sum +
        -(((poleSet N).filter (· ≠ h)).map fun a => padicValRat p (a - h)).sum = Vo N p k := by
      rw [hh, sum_val_zeros, sum_val_poles]
      unfold Vo
      ring
    have := hP (m - r)
    rw [hbase] at this
    refine this.mono (le_of_eq ?_)
    rw [hL, ← hmult]
    push_cast [Nat.cast_sub hrm]
    ring
  · exact ⟨fun _ => rfl, Or.inl rfl⟩

end KernelBound

/-! ### The rows of `𝓒_N` -/

section Rows

variable {p : ℕ} [Fact p.Prime]

/-- `v_p(H^{(s)}_n) ≥ -s ℓ_p(n)`. -/
theorem harm_valuation (s : ℕ) (n : ℤ) : Aux.ValGE p (-(s : ℤ) * ellp p n) (harm s n) := by
  unfold harm
  refine ValGE_sum _ _ _ fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  right
  rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have h := padicValRat_int_le_ellp (p := p) (x := i) (M := n) (by omega) (by omega)
  rw [Int.cast_natCast, padicValRat.of_nat] at h
  have hs : (0 : ℤ) ≤ s := Int.natCast_nonneg _
  nlinarith

theorem minOn_le (s : Finset ℤ) (f : ℤ → ℤ) {k : ℤ} (hk : k ∈ s) : minOn s f ≤ f k := by
  unfold minOn
  rw [dite_eq_left ⟨k, hk⟩]
  exact Finset.inf'_le f hk

/-- `m_o(k)` explicitly. -/
theorem mult_Io_eq (N : ℕ) (k : ℤ) : mult (Io N) k =
    (if 0 ≤ k ∧ k ≤ 10 * N + 1 then 1 else 0) + (if N ≤ k ∧ k ≤ 11 * N then 1 else 0) +
      (if 2 * N ≤ k ∧ k ≤ 12 * N then 1 else 0) := by
  simp only [mult, Io, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  push_cast
  split_ifs <;> omega

/-- The constant coefficient of `𝓛_K[f]` for `f` without polynomial part. -/
theorem Lfun_apply_zero (K : ℤ) (f : ℚ⟮X⟯) (hpoly : polyPart f = 0) :
    Lfun K f 0 = ∑ h ∈ f.denom.roots.toFinset, ∑ s ∈ Finset.range (f.denom.natDegree + 1),
      -((s : ℚ) * pfCoeff f h s * harm (s + 1) ⌊(K : ℚ) - h⌋) := by
  unfold Lfun
  rw [hpoly]
  simp [Zsym, Finset.sum_apply]

theorem valuation_of_small (s : ℕ) (h1 : 1 ≤ s) (h3 : s ≤ 3) (hp : 3 < p) :
    Aux.ValGE p 0 (s : ℚ) := by
  right
  rw [padicValRat.of_nat]
  norm_cast
  apply le_of_eq
  symm
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- **[1] Valuations of the rows of `𝓒_N`** (PDF Lemma 2 and Part IV). For `p > 3`, the
`ζ(4)`-row has valuation `≥ A_p`, the `ζ(3)`-row `≥ B_p` and `≥ C_p`, and the rational row
`≥ C_p`.

Pole argument: at a pole `-k` of order `m`, the top partial-fraction coefficient of
`(-t)^j R_N` has valuation `V_o(k)`. The coefficient of `(t+k)^{-r}` loses at most
`(m-r) ℓ_p(k+17N)`. The harmonic numbers `H^{(r+1)}_{2N+k}` lose at most `(r+1) ℓ_p(k+2N)`.
* Lines: proved here. The Laurent coefficients at a pole `-k` are the coefficients of the power
  series `taylor (-k) num · (taylor (-k) E)⁻¹` (`pfCoeff_div_eq`); a power series built from linear
  factors `X - a` and their inverses satisfies `v_p(f_n) ≥ v_p(f_0) - n ℓ_p(M)` (`PSBound`), which is
  the loss bound; the base `v_p(f_0) = V_o(k)` is a sum of valuations of consecutive integers
  (`padicValRat_prod_sub_eq_Gp`, `sum_val_zeros`); harmonic numbers lose `(r+1) ℓ_p`
  (`harm_valuation`).
* Directly from the PDF: partially. The loss bound "each Taylor derivative can lose at most
  `ℓ_p(M)`" needs a precise statement and proof. -/
theorem coeffMat_row_valuations (N : ℕ) (hN : 1 ≤ N) (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (j : Fin 3) :
    (coeffMat N 0 j ≠ 0 → Ap N p ≤ padicValRat p (coeffMat N 0 j)) ∧
    (coeffMat N 1 j ≠ 0 → max (Bp N p) (Cp N p) ≤ padicValRat p (coeffMat N 1 j)) ∧
    (coeffMat N 2 j ≠ 0 → Cp N p ≤ padicValRat p (coeffMat N 2 j)) := by
  set f := linFormKernel N j with hf
  have hpoly : polyPart f = 0 := polyPart_eq_zero_of_proper _ (linFormKernel_proper N j)
  have hroot : ∀ h ∈ f.denom.roots.toFinset, ∃ k : ℕ, k ≤ 12 * N ∧ h = -(k : ℚ) := by
    intro h hh
    have hmem := Multiset.mem_of_le (roots_denom_le N j) (Multiset.mem_toFinset.mp hh)
    simp only [poleSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at hmem
    rcases hmem with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · exact ⟨i, by omega, by push_cast; ring⟩
    · exact ⟨N + i, by omega, by push_cast; ring⟩
    · exact ⟨2 * N + i, by omega, by push_cast; ring⟩
  have hmle : ∀ k : ℤ, mult (Io N) k ≤ 3 := fun k => by rw [mult_Io_eq]; split_ifs <;> omega
  have hm3 : ∀ k : ℤ, mult (Io N) k = 3 → 2 * N ≤ k ∧ k ≤ 10 * N + 1 := fun k h => by
    rw [mult_Io_eq] at h; split_ifs at h <;> omega
  have hm2 : ∀ k : ℤ, 2 ≤ mult (Io N) k → 0 ≤ k ∧ k ≤ 12 * N := fun k h => by
    rw [mult_Io_eq] at h; split_ifs at h <;> omega
  have hL0 : ∀ k : ℤ, 0 ≤ ellp p (k + 17 * N) := fun k => Aux.ellp_nonneg _ _
  have hl0 : ∀ k : ℤ, 0 ≤ ellp p (k + 2 * N) := fun k => Aux.ellp_nonneg _ _
  have hlL : ∀ k : ℤ, 0 ≤ k → ellp p (k + 2 * N) ≤ ellp p (k + 17 * N) := fun k hk =>
    Aux.ellp_mono (Fact.out) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · -- the `Z₄` row: `∑_h 3 c_{h,3}`, bounded by `A_p`
    intro hne
    suffices hV : Aux.ValGE p (Ap N p) (coeffMat N 0 j) by
      rcases hV with h0 | h0
      · exact absurd h0 hne
      · exact h0
    show Aux.ValGE p (Ap N p) (Lfun (2 * N) f 4)
    rw [Lfun_apply_of_ne_zero _ _ hpoly 4 (by norm_num)]
    refine ValGE_sum _ _ _ fun h hh => ValGE_sum _ _ _ fun s _ => ?_
    obtain ⟨k, hk, rfl⟩ := hroot h hh
    by_cases hs : s + 1 = 4
    · have hs3 : s = 3 := by omega
      subst hs3
      rw [ite_eq_left hs, mul_one]
      obtain ⟨hz, hb⟩ := pfCoeff_linFormKernel_valuation (p := p) N hN j k 3 (by norm_num)
      by_cases hm : mult (Io N) k < 3
      · rw [hz hm]; exact Or.inl (by simp)
      · have hm3' : mult (Io N) k = 3 := le_antisymm (hmle k) (not_lt.mp hm)
        obtain ⟨hk1, hk2⟩ := hm3 k hm3'
        have h3 : Aux.ValGE p 0 ((3 : ℕ) : ℚ) := valuation_of_small 3 (by norm_num) le_rfl hp
        have := h3.mul hb
        rw [hm3'] at this
        refine this.mono ?_
        have := minOn_le (Finset.Icc (2 * N : ℤ) (10 * N + 1)) (Vo N p) (k := k)
          (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)
        unfold Ap
        push_cast
        linarith
    · rw [ite_eq_right hs, mul_zero]; exact Or.inl rfl
  · -- the `Z₃` row: `∑_h 2 c_{h,2}`, bounded by `max(B_p, C_p)`
    intro hne
    suffices hV : Aux.ValGE p (max (Bp N p) (Cp N p)) (coeffMat N 1 j) by
      rcases hV with h0 | h0
      · exact absurd h0 hne
      · exact h0
    show Aux.ValGE p (max (Bp N p) (Cp N p)) (Lfun (2 * N) f 3)
    rw [Lfun_apply_of_ne_zero _ _ hpoly 3 (by norm_num)]
    refine ValGE_sum _ _ _ fun h hh => ValGE_sum _ _ _ fun s _ => ?_
    obtain ⟨k, hk, rfl⟩ := hroot h hh
    by_cases hs : s + 1 = 3
    · have hs2 : s = 2 := by omega
      subst hs2
      rw [ite_eq_left hs, mul_one]
      obtain ⟨hz, hb⟩ := pfCoeff_linFormKernel_valuation (p := p) N hN j k 2 (by norm_num)
      by_cases hm : mult (Io N) k < 2
      · rw [hz hm]; exact Or.inl (by simp)
      · have hm2' : 2 ≤ mult (Io N) k := not_lt.mp hm
        obtain ⟨hk1, hk2⟩ := hm2 k hm2'
        have h2 : Aux.ValGE p 0 ((2 : ℕ) : ℚ) := valuation_of_small 2 (by norm_num) (by norm_num) hp
        have := h2.mul hb
        refine this.mono ?_
        have hB := minOn_le ((Finset.Icc 0 (12 * N : ℤ)).filter fun k => 2 ≤ mult (Io N) k)
          (fun k => Vo N p k - (mult (Io N) k - 2) * ellp p (k + 17 * N)) (k := k)
          (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hk2⟩, hm2'⟩)
        have hC := minOn_le (Finset.Icc 0 (12 * N : ℤ))
          (fun k => Vo N p k - (mult (Io N) k - 1) * ellp p (k + 17 * N) - 2 * ellp p (k + 2 * N))
          (k := k) (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)
        unfold Bp Cp
        have := hL0 k
        have := hl0 k
        refine max_le ?_ ?_ <;> push_cast <;> nlinarith
    · rw [ite_eq_right hs, mul_zero]; exact Or.inl rfl
  · -- the rational row, bounded by `C_p`
    intro hne
    suffices hV : Aux.ValGE p (Cp N p) (coeffMat N 2 j) by
      rcases hV with h0 | h0
      · exact absurd h0 hne
      · exact h0
    show Aux.ValGE p (Cp N p) (Lfun (2 * N) f 0)
    rw [Lfun_apply_zero _ _ hpoly]
    refine ValGE_sum _ _ _ fun h hh => ValGE_sum _ _ _ fun s _ => ?_
    obtain ⟨k, hk, rfl⟩ := hroot h hh
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · left; simp
    refine Aux.ValGE.neg ?_
    obtain ⟨hz, hb⟩ := pfCoeff_linFormKernel_valuation (p := p) N hN j k s hs1
    by_cases hm : mult (Io N) k < s
    · rw [hz hm]; exact Or.inl (by simp)
    · have hsm : (s : ℤ) ≤ mult (Io N) k := not_lt.mp hm
      have hs3 : s ≤ 3 := by have := hmle k; omega
      have hs' : Aux.ValGE p 0 (s : ℚ) := valuation_of_small s hs1 hs3 hp
      have hfl : ⌊((2 * N : ℤ) : ℚ) - -(k : ℚ)⌋ = 2 * N + k := by
        rw [show ((2 * N : ℤ) : ℚ) - -(k : ℚ) = ((2 * N + k : ℤ) : ℚ) by push_cast; ring,
          Int.floor_intCast]
      rw [hfl]
      have hh' := harm_valuation (p := p) (s + 1) (2 * N + k)
      have := (hs'.mul hb).mul hh'
      refine this.mono ?_
      have hC := minOn_le (Finset.Icc 0 (12 * N : ℤ))
        (fun k => Vo N p k - (mult (Io N) k - 1) * ellp p (k + 17 * N) - 2 * ellp p (k + 2 * N))
        (k := k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      unfold Cp
      have e : (2 * (N : ℤ) + k) = (k : ℤ) + 2 * N := by ring
      rw [e] at this ⊢
      have := hL0 k
      have := hl0 k
      have := hlL k (by omega)
      have hs1' : (1 : ℤ) ≤ s := by exact_mod_cast hs1
      push_cast
      nlinarith


end Rows

/-- **[2] `v_p(F_N) = vpF(N,p)`.** Legendre and the definition of `F_N`.
* Lines: proved here.
* Directly from the PDF: yes. -/
theorem padicValRat_F (N p : ℕ) [Fact p.Prime] : padicValRat p (F N) = vpF N p := by
  have hne : ∀ (l : List ℕ) (g : ℕ → ℕ), (l.map fun r => ((g r).factorial : ℚ)).prod ≠ 0 :=
    fun l g => List.prod_ne_zero (by simp [Nat.factorial_ne_zero])
  have hfm : ∀ l : List ℕ,
      List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
    intro l; induction l <;> simp_all
  have hv : vpF N p = (listA.map fun r => fp p ((r * N : ℕ) : ℤ)).sum -
      (listB.map fun r => fp p ((r * N : ℕ) : ℤ)).sum -
      (listE.map fun r => fp p ((r * N + 1 : ℕ) : ℤ)).sum := by
    unfold vpF
    simp [hfm, List.map_map, Function.comp_def]
  have hfp : ∀ m : ℕ, fp p (m : ℤ) = padicValNat p m.factorial := fun m => by simp [fp]
  unfold F
  rw [hv, padicValRat.div (hne _ _) (mul_ne_zero (hne _ _) (hne _ _)),
    padicValRat.mul (hne _ _) (hne _ _),
    Aux.padicValRat_factorial_prod p listA (fun r => r * N),
    Aux.padicValRat_factorial_prod p listB (fun r => r * N),
    Aux.padicValRat_factorial_prod p listE (fun r => r * N + 1)]
  simp only [hfp]
  ring

/- **[9] `det V_N = F_N`** (the node `det_V_eq` of `blueprint.lean`) is
`ZetasIrr.BP.det_V_eq`, imported from `blueprints/det_V_eq.lean`. [3] needs it. -/

/-- **[3] Bounds from the original formula** (`p > 3`). The readouts are
`q = -(A×B)/det V`, `p^{(3)} = -(C×A)/det V`, `p^{(4)} = -(B×C)/det V` (see
`readouts_eq_cross` in `cross_product_readout.lean`) with `det V_N = F_N`. A cross-product
component of rows with valuations `≥ α`, `≥ β` has valuation `≥ α + β`. Combine with [1], [2].
* Lines: proved here (from [1], [2], [9]).
* Directly from the PDF: yes (given [1], [2], [9]). -/
theorem original_bounds (N : ℕ) (hN : 1 ≤ N) (p : ℕ) [Fact p.Prime] (hp : 3 < p) (j : Fin 3) :
    (p3 N j ≠ 0 → -Eo N p ≤ padicValRat p (p3 N j)) ∧
    (q N j ≠ 0 → -Eo N p ≤ padicValRat p (q N j)) ∧
    (p4 N j ≠ 0 → -Eo4 N p ≤ padicValRat p (p4 N j)) := by
  have vA : ∀ i, Aux.ValGE p (Ap N p) (coeffMat N 0 i) := fun i =>
    (em (coeffMat N 0 i = 0)).elim Or.inl
      fun h => Or.inr ((coeffMat_row_valuations N hN p hp i).1 h)
  have vB : ∀ i, Aux.ValGE p (max (Bp N p) (Cp N p)) (coeffMat N 1 i) := fun i =>
    (em (coeffMat N 1 i = 0)).elim Or.inl
      fun h => Or.inr ((coeffMat_row_valuations N hN p hp i).2.1 h)
  have vC : ∀ i, Aux.ValGE p (Cp N p) (coeffMat N 2 i) := fun i =>
    (em (coeffMat N 2 i = 0)).elim Or.inl
      fun h => Or.inr ((coeffMat_row_valuations N hN p hp i).2.2 h)
  have hF : F N ≠ 0 := by
    unfold F
    refine div_ne_zero (List.prod_ne_zero ?_) (mul_ne_zero (List.prod_ne_zero ?_)
      (List.prod_ne_zero ?_)) <;> simp [Nat.factorial_ne_zero]
  have hd0 : (V N).det ≠ 0 := by rw [det_V_eq]; exact hF
  have hvd : padicValRat p (V N).det = vpF N p := by rw [det_V_eq, padicValRat_F]
  -- dividing by `-det V_N` lowers the valuation bound by `v_p(F_N)`
  have key : ∀ (X : ℚ) (a : ℤ), Aux.ValGE p a X → -((V N).det)⁻¹ * X ≠ 0 →
      a - vpF N p ≤ padicValRat p (-((V N).det)⁻¹ * X) := by
    intro X a hX hne
    have hX0 : X ≠ 0 := fun h => hne (by rw [h, mul_zero])
    rcases hX with h | hX
    · exact absurd h hX0
    rw [padicValRat.mul (neg_ne_zero.mpr (inv_ne_zero hd0)) hX0, padicValRat.neg,
      padicValRat.inv, hvd]
    linarith
  have hEo : vpF N p - Ap N p - Cp N p ≤ Eo N p := le_max_right _ _
  have hEo4 : vpF N p - Bp N p - Cp N p ≤ Eo4 N p := le_max_right _ _
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_⟩
  · -- `p^{(3)} = -(C × A)/det V`
    have e : p3 N j = -((V N).det)⁻¹ * crossProduct (coeffMat N 2) (coeffMat N 0) j := by
      rw [p3, ZetasIrr.readouts_eq_cross_rat]; rfl
    rw [e] at hne ⊢
    have := key _ _ (Aux.ValGE.cross vC vA j) hne
    linarith
  · -- `q = -(A × B)/det V`
    have e : q N j = -((V N).det)⁻¹ * crossProduct (coeffMat N 0) (coeffMat N 1) j := by
      rw [q, ZetasIrr.readouts_eq_cross_rat]; rfl
    rw [e] at hne ⊢
    have := key _ _ (Aux.ValGE.cross vA (fun i => (vB i).mono (le_max_right _ _)) j) hne
    linarith
  · -- `p^{(4)} = -(B × C)/det V`
    have e : p4 N j = -((V N).det)⁻¹ * crossProduct (coeffMat N 1) (coeffMat N 2) j := by
      rw [p4, ZetasIrr.readouts_eq_cross_rat]; rfl
    rw [e] at hne ⊢
    have := key _ _ (Aux.ValGE.cross (fun i => (vB i).mono (le_max_left _ _)) vC j) hne
    linarith

/-- **[4] The dual formula for the first functional** (PDF Part VII §2 and §7):
`(-1)^N · 3 · 𝓛_{-11N-1}[Q_{Nj}(t) R*_N(t)] = Z₃ q_{Nj} - p^{(3)}_{Nj}`, coefficientwise.
(`q = 3y`, `p^{(3)} = 3x` in the notation of Part VII; for `j = 2` this is (15).)

Proof: the transport of the dual formal moments `g_N` and the concomitant identity
`W_N J_N (D_N^{dual})ᵀ = J_0`. Pairing gives `g_N J_N[0:3,:]ᵀ = Z₃ v T_N - u T_N`. Then substitute
`s = t + 12N + 1`.
* Lines: ≈ 2500 (CMF definitions and transport, shared with `det_V_eq.lean` [5] and
  `pairing_identity.lean` [4]; the generic concomitant identity is certified symbolically in
  `verify_pairing.py`).
* Directly from the PDF: no. The PDF sketches the transport path. The concomitant identity is
  checked by computer algebra (`verify_pairing.py`). -/
theorem dual_first_identity (N : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ N * 3) • Lfun (-11 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) =
      q N j • Zsym 3 - p3 N j • Zsym 0 :=
  CMF.dual_first_identity' N j

/- **[5] Pairing identity (6)** (the node `pairing_identity` of `blueprint.lean`) is
`ZetasIrr.BP.pairing_identity`, imported from `blueprints/pairing_identity.lean`. -/

/-! ### Supporting lemmas for [6] and [7]: the dual kernel `Q_{Nj} R*_N` -/

section DualKernel

variable {p : ℕ} [Fact p.Prime]

/-- The zeros of `R*_N` with multiplicity: `k ∈ [N+1, 12N] ∪ [1, 11N] ∪ [2N, 10N]` (as `-k`). -/
def zeroSetStar (N : ℕ) : Multiset ℚ :=
  blk (N + 1) (11 * N) + blk 1 (11 * N) + blk (2 * N) (8 * N + 1)

/-- The poles of `R*_N`: `k ∈ [13N+1, 28N+1] ∪ [14N+1, 29N+1]`. -/
def poleSetStar (N : ℕ) : Multiset ℚ :=
  blk (13 * N + 1) (15 * N + 1) + blk (14 * N + 1) (15 * N + 1)

theorem RkerStar_eq (N : ℕ) : RkerStar N =
    algebraMap ℚ[X] ℚ⟮X⟯ ((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod /
      algebraMap ℚ[X] ℚ⟮X⟯ ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod := by
  unfold RkerStar zeroSetStar poleSetStar blk
  rw [poch_eq_prod, poch_eq_prod, poch_eq_prod, poch_eq_prod, poch_eq_prod]
  simp only [Multiset.map_add, Multiset.prod_add]
  push_cast
  rfl

theorem count_poleSetStar (N k : ℕ) :
    ((poleSetStar N).count (-(k : ℚ)) : ℤ) = mult (Id N) k := by
  rw [poleSetStar, Multiset.count_add, count_blk, count_blk]
  simp only [mult, Id, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  push_cast
  split_ifs <;> omega

theorem sum_val_polesStar (N k : ℕ) :
    (((poleSetStar N).filter (· ≠ -(k : ℚ))).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      ((Id N).map fun ab => Gp p k ab.1 ab.2).sum := by
  rw [poleSetStar, Multiset.filter_add, Multiset.map_add, Multiset.sum_add, sum_val_blk,
    sum_val_blk]
  simp only [Id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  push_cast
  have e1 : (13 * (N : ℤ) + 1) + (15 * (N : ℤ) + 1) - 1 = 28 * N + 1 := by ring
  have e2 : (14 * (N : ℤ) + 1) + (15 * (N : ℤ) + 1) - 1 = 29 * N + 1 := by ring
  rw [e1, e2]

/-- The valuation sum over a zero block `{-(c+i)}` at `-k` with `c + n ≤ k`. -/
theorem sum_val_blk_zero (c n k : ℕ) (hk : c + n ≤ k) :
    ((blk c n).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      fp p ((k : ℤ) - c) - fp p ((k : ℤ) - c - n) := by
  unfold blk
  rw [Multiset.map_map]
  have e : ∀ i ∈ Finset.range n, padicValRat p (-((c : ℚ) + i) - (-(k : ℚ))) =
      padicValRat p (((k - c - i : ℕ) : ℚ)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    congr 1
    push_cast [show i ≤ k - c by omega, show c ≤ k by omega]
    ring
  have hne : ∀ i ∈ Finset.range n, (((k - c - i : ℕ) : ℚ)) ≠ 0 := fun i hi => by
    have := Finset.mem_range.mp hi
    exact_mod_cast (by omega : k - c - i ≠ 0)
  rw [show Multiset.range n = (Finset.range n).val from rfl, ← Finset.sum_eq_multiset_sum]
  simp only [Function.comp]
  rw [Finset.sum_congr rfl e, ← padicValRat_finset_prod _ _ hne,
    padicValRat_prod_desc (k - c) n (by omega)]
  congr 2 <;> push_cast <;> omega

theorem sum_val_zerosStar (N k : ℕ) (hk : 13 * N + 1 ≤ k) :
    ((zeroSetStar N).map fun a => padicValRat p (a - (-(k : ℚ)))).sum =
      fp p ((k : ℤ) - N - 1) + fp p ((k : ℤ) - 1) + fp p ((k : ℤ) - 2 * N) -
        fp p ((k : ℤ) - 12 * N - 1) - fp p ((k : ℤ) - 11 * N - 1) - fp p ((k : ℤ) - 10 * N - 1) := by
  rw [zeroSetStar, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
    sum_val_blk_zero _ _ _ (by omega), sum_val_blk_zero _ _ _ (by omega),
    sum_val_blk_zero _ _ _ (by omega)]
  push_cast
  have e1 : (k : ℤ) - (N + 1) - 11 * N = k - 12 * N - 1 := by ring
  have e2 : (k : ℤ) - 1 - 11 * N = k - 11 * N - 1 := by ring
  have e3 : (k : ℤ) - 2 * N - (8 * N + 1) = k - 10 * N - 1 := by ring
  have e4 : (k : ℤ) - (N + 1) = k - N - 1 := by ring
  rw [e1, e2, e3, e4]
  ring

/-- The Taylor coefficients of `Q_{Nj}` at an integer point are integers. -/
theorem taylor_Qpoly_int (N : ℕ) (j : Fin 3) (k : ℕ) (n : ℕ) :
    Aux.ValGE p 0 ((taylor (-(k : ℚ)) (Qpoly N j)).coeff n) := by
  unfold Qpoly
  rw [map_sum, Polynomial.finset_sum_coeff]
  refine ValGE_sum _ _ _ fun r _ => ?_
  rw [map_smul, Polynomial.coeff_smul, smul_eq_mul, Polynomial.taylor_pow, map_sub, map_neg,
    Polynomial.taylor_X, Polynomial.taylor_C]
  have e : (-(Polynomial.X + Polynomial.C (-(k : ℚ))) - Polynomial.C (12 * (N : ℚ) + 1)) =
      -(Polynomial.X + Polynomial.C (-(k : ℚ) + (12 * (N : ℚ) + 1))) := by
    simp only [map_add, map_mul, map_neg, map_one, map_ofNat]; ring
  rw [e, neg_pow, show ((-1 : ℚ[X]) ^ (r : ℕ)) = Polynomial.C ((-1) ^ (r : ℕ)) by simp,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  have : ((Jmat N (Fin.castSucc j) r : ℤ) : ℚ) * ((-1 : ℚ) ^ (r : ℕ) *
      ((-(k : ℚ) + (12 * (N : ℚ) + 1)) ^ ((r : ℕ) - n) * ((r : ℕ).choose n : ℚ))) =
      (((Jmat N (Fin.castSucc j) r : ℤ) * ((-1 : ℤ) ^ (r : ℕ) *
        ((-(k : ℤ) + (12 * (N : ℤ) + 1)) ^ ((r : ℕ) - n) * ((r : ℕ).choose n : ℤ))) : ℤ) : ℚ) := by
    push_cast; ring
  rw [this]
  exact ValGE_int _

theorem PSBound_taylor_Qpoly {L : ℤ} (hL : 0 ≤ L) (N : ℕ) (j : Fin 3) (k : ℕ) :
    PSBound p 0 L ((taylor (-(k : ℚ)) (Qpoly N j) : ℚ[X]) : PowerSeries ℚ) :=
  PSBound.of_int_coeffs hL _ (taylor_Qpoly_int N j k)

/-- **Per-pole Laurent bound for the dual kernel** `Q_{Nj} R*_N` at `t = -k`,
`13N+1 ≤ k ≤ 29N+1`: `v_p(c_{-k,r}) ≥ V_d(k) - (m_d(k) - r) ℓ_p(L(k))`. -/
theorem pfCoeff_dual_valuation (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) (k r : ℕ) (hk1 : 13 * N + 1 ≤ k)
    (hk2 : k ≤ 29 * N + 1) (hr : 1 ≤ r) :
    (mult (Id N) k < r →
      pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) (-(k : ℚ)) r = 0) ∧
    Aux.ValGE p (Vd N p k - (mult (Id N) k - r) * ellp p (Ld N k))
      (pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) (-(k : ℚ)) r) := by
  set h : ℚ := -(k : ℚ) with hh
  set m : ℕ := (poleSetStar N).count h with hm
  set L : ℤ := ellp p (Ld N k) with hL
  have hL0 : 0 ≤ L := Aux.ellp_nonneg _ _
  set E : ℚ[X] := ((poleSetStar N).filter (· ≠ h)).map (fun a => Polynomial.X - Polynomial.C a)
    |>.prod with hE
  have hEval : E.eval h ≠ 0 := by
    rw [hE, eval_prod_X_sub_C]
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.mp h0
    have := (Multiset.mem_filter.mp ha).2
    exact this (by linarith)
  have hden : ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod =
      (Polynomial.X - Polynomial.C h) ^ m * E := prod_X_sub_C_split _ h
  rw [RkerStar_eq, ← mul_div_assoc, ← map_mul, hden, pfCoeff_div_eq _ _ h m hEval r]
  have hmult : (m : ℤ) = mult (Id N) k := count_poleSetStar N k
  split_ifs with hrm
  · refine ⟨fun hlt => by omega, ?_⟩
    have hA : PSBound p 0 L ((taylor h (Qpoly N j) : ℚ[X]) : PowerSeries ℚ) :=
      PSBound_taylor_Qpoly hL0 N j k
    -- the zeros: `a = -(c+i)` with `c + i ≤ 12N`, so `0 < a - h = k - c - i ≤ k - 1 ≤ L(k)`
    have hzero : ∀ a ∈ zeroSetStar N, ∃ z : ℕ, 1 ≤ z ∧ z ≤ 12 * N ∧ a = -(z : ℚ) := by
      intro a ha
      simp only [zeroSetStar, blk, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at ha
      rcases ha with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
      · exact ⟨N + 1 + i, by omega, by omega, by push_cast; ring⟩
      · exact ⟨1 + i, by omega, by omega, by push_cast; ring⟩
      · exact ⟨2 * N + i, by omega, by omega, by push_cast; ring⟩
    have hzero_ne : ∀ a ∈ zeroSetStar N, a - h ≠ 0 := by
      intro a ha
      obtain ⟨z, hz1, hz2, rfl⟩ := hzero a ha
      rw [hh]
      have : (z : ℚ) < k := by exact_mod_cast (by omega : z < k)
      intro h0; linarith
    have hzero_le : ∀ a ∈ zeroSetStar N, padicValRat p (a - h) ≤ L := by
      intro a ha
      obtain ⟨z, hz1, hz2, rfl⟩ := hzero a ha
      have e : -(z : ℚ) - h = (((k : ℤ) - z : ℤ) : ℚ) := by rw [hh]; push_cast; ring
      rw [e, hL]
      exact padicValRat_int_le_ellp (by omega) (by unfold Ld; omega)
    have hZ : PSBound p ((zeroSetStar N).map fun a => padicValRat p (a - h)).sum L
        (((((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C (a - h)).prod : ℚ[X])) :
          PowerSeries ℚ) := by
      have e : ((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C (a - h)) =
          ((zeroSetStar N).map fun a => a - h).map fun b => Polynomial.X - Polynomial.C b := by
        rw [Multiset.map_map]; rfl
      rw [e, coe_prod_X_sub_C]
      have := PSBound.prod_X_sub_C (p := p) hL0 ((zeroSetStar N).map fun a => a - h)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hzero_ne a ha)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hzero_le a ha)
      rwa [Multiset.map_map] at this
    -- the other poles: `a = -r'` with `13N+1 ≤ r' ≤ 29N+1`, `|k - r'| ≤ L(k)`
    have hpole : ∀ a ∈ poleSetStar N, ∃ z : ℕ, 13 * N + 1 ≤ z ∧ z ≤ 29 * N + 1 ∧ a = -(z : ℚ) := by
      intro a ha
      simp only [poleSetStar, blk, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at ha
      rcases ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact ⟨13 * N + 1 + i, by omega, by omega, by push_cast; ring⟩
      · exact ⟨14 * N + 1 + i, by omega, by omega, by push_cast; ring⟩
    have hpole_ne : ∀ a ∈ (poleSetStar N).filter (· ≠ h), a - h ≠ 0 := fun a ha =>
      sub_ne_zero.mpr (Multiset.mem_filter.mp ha).2
    have hpole_le : ∀ a ∈ (poleSetStar N).filter (· ≠ h), padicValRat p (a - h) ≤ L := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Multiset.mem_filter.mp ha
      obtain ⟨z, hz1, hz2, rfl⟩ := hpole a ha1
      have e : -(z : ℚ) - h = (((k : ℤ) - z : ℤ) : ℚ) := by rw [hh]; push_cast; ring
      rw [e, hL]
      refine padicValRat_int_le_ellp' ?_ ?_
      · intro h0
        apply ha2
        rw [hh]
        have : (z : ℤ) = k := by omega
        exact_mod_cast congrArg (fun x : ℤ => -(x : ℚ)) this
      · unfold Ld; rw [abs_le]; constructor <;> omega
    have hEinv : PSBound p (-(((poleSetStar N).filter (· ≠ h)).map fun a =>
        padicValRat p (a - h)).sum) L (((taylor h E : ℚ[X]) : PowerSeries ℚ))⁻¹ := by
      rw [hE, taylor_prod_X_sub_C]
      have e : (((poleSetStar N).filter (· ≠ h)).map fun a => Polynomial.X - Polynomial.C (a - h)) =
          (((poleSetStar N).filter (· ≠ h)).map fun a => a - h).map fun b =>
            Polynomial.X - Polynomial.C b := by
        rw [Multiset.map_map]; rfl
      rw [e, coe_prod_X_sub_C]
      have := PSBound.inv_prod_X_sub_C (p := p) hL0
        (((poleSetStar N).filter (· ≠ h)).map fun a => a - h)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hpole_ne a ha)
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb; exact hpole_le a ha)
      rwa [Multiset.map_map] at this
    have hnum : ((taylor h (Qpoly N j *
        ((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod) : ℚ[X]) : PowerSeries ℚ) =
        ((taylor h (Qpoly N j) : ℚ[X]) : PowerSeries ℚ) *
          (((((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C (a - h)).prod : ℚ[X])) :
            PowerSeries ℚ) := by
      rw [Polynomial.taylor_mul, taylor_prod_X_sub_C, Polynomial.coe_mul]
    rw [hnum]
    have hP := (hA.mul hZ).mul hEinv
    have hbase : (0 : ℤ) + ((zeroSetStar N).map fun a => padicValRat p (a - h)).sum +
        -(((poleSetStar N).filter (· ≠ h)).map fun a => padicValRat p (a - h)).sum = Vd N p k := by
      rw [hh, sum_val_zerosStar N k hk1, sum_val_polesStar]
      unfold Vd
      ring
    have := hP (m - r)
    rw [hbase] at this
    refine this.mono (le_of_eq ?_)
    rw [hL, ← hmult]
    push_cast [Nat.cast_sub hrm]
    ring
  · exact ⟨fun _ => rfl, Or.inl rfl⟩

end DualKernel


section DerivLaurent

/-- Coefficients of `X · f'` in a power series: `n f_n`. -/
theorem coeff_X_mul_derivative (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative (R := ℚ) F) = n * PowerSeries.coeff n F := by
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast; ring

/-- The key power-series identity behind `pfCoeff_rfDeriv`. -/
theorem deriv_series_identity (A B : PowerSeries ℚ) (m : ℕ)
    (hB : PowerSeries.constantCoeff B ≠ 0) :
    (PowerSeries.derivative (R := ℚ) A * PowerSeries.X * B -
        A * (PowerSeries.C (m : ℚ) * B + PowerSeries.X * PowerSeries.derivative (R := ℚ) B)) * B⁻¹ * B⁻¹ =
      PowerSeries.X * PowerSeries.derivative (R := ℚ) (A * B⁻¹) - PowerSeries.C (m : ℚ) * (A * B⁻¹) := by
  have hBI : B * B⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hB
  rw [Derivation.leibniz, PowerSeries.derivative_inv']
  simp only [smul_eq_mul]
  linear_combination (PowerSeries.derivative (R := ℚ) A * PowerSeries.X * B⁻¹ -
    PowerSeries.C (m : ℚ) * A * B⁻¹) * hBI

/-- `rfDeriv` of `p/((X-h)^m E)` as `S/((X-h)^{m+1} E²)`. -/
theorem rfDeriv_div_pole (p E : ℚ[X]) (h : ℚ) (m : ℕ) (hm : 1 ≤ m) (hE : E.eval h ≠ 0) :
    rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ p /
        algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ m * E)) =
      algebraMap ℚ[X] ℚ⟮X⟯ (derivative p * (Polynomial.X - Polynomial.C h) * E -
          p * (Polynomial.C (m : ℚ) * E + (Polynomial.X - Polynomial.C h) * derivative E)) /
        algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ (m + 1) * E ^ 2) := by
  have hE0 : E ≠ 0 := fun h0 => hE (by simp [h0])
  have hq : (Polynomial.X - Polynomial.C h) ^ m * E ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero h)) hE0
  rw [Aux.rfDeriv_div _ _ hq]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hX : algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ m') ≠ 0 :=
    Aux.algebraMap_ne_zero' (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero h))
  rw [div_eq_div_iff (Aux.algebraMap_ne_zero' (pow_ne_zero 2 hq))
    (Aux.algebraMap_ne_zero' (mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero h))
      (pow_ne_zero 2 hE0))), ← map_mul, ← map_mul]
  congr 1
  simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_C,
    Polynomial.derivative_X_sub_C]
  push_cast
  ring

/-- **Laurent coefficients of the derivative**: `c'_{h,r+1} = -r c_{h,r}`. -/
theorem pfCoeff_rfDeriv_div (p E : ℚ[X]) (h : ℚ) (m : ℕ) (hm : 1 ≤ m) (hE : E.eval h ≠ 0) (r : ℕ) :
    pfCoeff (rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ p /
        algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ m * E))) h (r + 1) =
      -(r : ℚ) * pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ p /
        algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ m * E)) h r := by
  have hE2 : (E ^ 2).eval h ≠ 0 := by rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hE
  rw [rfDeriv_div_pole p E h m hm hE, pfCoeff_div_eq _ _ h (m + 1) hE2 (r + 1),
    pfCoeff_div_eq _ _ h m hE r]
  by_cases hrm : r ≤ m
  · rw [ite_eq_left (by omega), ite_eq_left hrm]
    -- the power series computation
    set A : PowerSeries ℚ := (taylor h p : PowerSeries ℚ) with hA
    set B : PowerSeries ℚ := (taylor h E : PowerSeries ℚ) with hB
    have hB0 : PowerSeries.constantCoeff B ≠ 0 := by
      rw [hB, Polynomial.constantCoeff_coe, Polynomial.taylor_coeff_zero]; exact hE
    have hS : ((taylor h (derivative p * (Polynomial.X - Polynomial.C h) * E -
        p * (Polynomial.C (m : ℚ) * E + (Polynomial.X - Polynomial.C h) * derivative E)) : ℚ[X]) :
          PowerSeries ℚ) =
        PowerSeries.derivative (R := ℚ) A * PowerSeries.X * B -
          A * (PowerSeries.C (m : ℚ) * B + PowerSeries.X * PowerSeries.derivative (R := ℚ) B) := by
      simp only [map_sub, map_add, Polynomial.taylor_mul, Polynomial.taylor_X,
        Polynomial.taylor_C, ← Aux.derivative_taylor, Polynomial.coe_sub, Polynomial.coe_add,
        Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, hA, hB,
        ← PowerSeries.derivative_coe]
      ring
    have hE2' : ((taylor h (E ^ 2) : ℚ[X]) : PowerSeries ℚ) = B * B := by
      rw [Polynomial.taylor_pow, Polynomial.coe_pow, hB, sq]
    have hinv : B⁻¹ * B⁻¹ = (B * B)⁻¹ := by
      refine (PowerSeries.eq_inv_iff_mul_eq_one (by rw [map_mul]; exact mul_ne_zero hB0 hB0)).mpr ?_
      calc B⁻¹ * B⁻¹ * (B * B) = (B⁻¹ * B) * (B⁻¹ * B) := by ring
        _ = 1 := by rw [PowerSeries.inv_mul_cancel _ hB0, one_mul]
    rw [hS, hE2', ← hinv, ← mul_assoc, deriv_series_identity A B m hB0,
      show m + 1 - (r + 1) = m - r by omega, map_sub, coeff_X_mul_derivative]
    rw [PowerSeries.coeff_C_mul]
    push_cast [Nat.cast_sub hrm]
    ring
  · rw [ite_eq_right (by omega), ite_eq_right hrm, mul_zero]

end DerivLaurent


section PolyPart

/-- `rfDeriv` of a polynomial. -/
theorem rfDeriv_algebraMap (P : ℚ[X]) :
    rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ P) = algebraMap ℚ[X] ℚ⟮X⟯ (derivative P) := by
  rw [← div_one (algebraMap ℚ[X] ℚ⟮X⟯ P), ← map_one (algebraMap ℚ[X] ℚ⟮X⟯),
    Aux.rfDeriv_div _ _ one_ne_zero]
  simp

theorem rfDeriv_neg (g : ℚ⟮X⟯) : rfDeriv (-g) = -rfDeriv g := by
  rw [show -g = RatFunc.C (-1) * g by rw [map_neg, map_one, neg_one_mul], Aux.rfDeriv_C_mul,
    map_neg, map_one, neg_one_mul]

theorem rfDeriv_sub (f g : ℚ⟮X⟯) : rfDeriv (f - g) = rfDeriv f - rfDeriv g := by
  rw [sub_eq_add_neg, Aux.rfDeriv_add, rfDeriv_neg, sub_eq_add_neg]

/-- Differentiation lowers the degree by one. -/
theorem DegLE_rfDeriv {g : ℚ⟮X⟯} {k : ℤ} (hg : DegLE k g) : DegLE (k - 1) (rfDeriv g) := by
  obtain ⟨a, b, hb, rfl⟩ := Aux.exists_eq_div g
  rw [Aux.rfDeriv_div _ _ hb]
  by_cases hnum : derivative a * b - a * derivative b = 0
  · left; simp [hnum]
  have ha : a ≠ 0 := by rintro rfl; simp at hnum
  have hdeg : (a.natDegree : ℤ) - b.natDegree ≤ k := by
    rcases hg with h0 | h
    · exfalso
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact ha ((map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] ℚ⟮X⟯)).mp h)
      · exact Aux.algebraMap_ne_zero' hb h
    · rwa [RatFunc.intDegree_div (Aux.algebraMap_ne_zero' ha) (Aux.algebraMap_ne_zero' hb),
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial] at h
  right
  rw [RatFunc.intDegree_div (Aux.algebraMap_ne_zero' hnum)
    (Aux.algebraMap_ne_zero' (pow_ne_zero 2 hb)), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
  -- `natDegree (a' b - a b') ≤ natDegree a + natDegree b - 1`
  have key : (derivative a * b - a * derivative b).natDegree + 1 ≤ a.natDegree + b.natDegree := by
    have h1 := Polynomial.natDegree_sub_le (derivative a * b) (a * derivative b)
    have h2 := Polynomial.natDegree_mul_le (p := derivative a) (q := b)
    have h3 := Polynomial.natDegree_mul_le (p := a) (q := derivative b)
    have h4 := Polynomial.natDegree_derivative_le a
    have h5 := Polynomial.natDegree_derivative_le b
    rcases Nat.eq_zero_or_pos a.natDegree with ha0 | ha0 <;>
      rcases Nat.eq_zero_or_pos b.natDegree with hb0 | hb0
    · -- both constant: the numerator is zero
      exfalso
      apply hnum
      rw [Polynomial.derivative_of_natDegree_zero ha0, Polynomial.derivative_of_natDegree_zero hb0]
      simp
    · rw [Polynomial.derivative_of_natDegree_zero ha0, zero_mul, zero_sub, Polynomial.natDegree_neg]
      omega
    · rw [Polynomial.derivative_of_natDegree_zero hb0, mul_zero, sub_zero]
      omega
    · omega
  omega

/-- The polynomial part of the derivative is the derivative of the polynomial part. -/
theorem polyPart_rfDeriv (f : ℚ⟮X⟯) : polyPart (rfDeriv f) = derivative (polyPart f) := by
  apply Aux.polyPart_eq_of
  have h := DegLE_rfDeriv (Aux.DegLE_sub_polyPart f)
  rw [rfDeriv_sub, rfDeriv_algebraMap] at h
  exact h.mono (by norm_num)

/-! ### The dual kernel over `ℤ` -/

/-- The integer version of a block. -/
def blkZ (c n : ℕ) : Multiset ℤ := (Multiset.range n).map fun i : ℕ => -((c : ℤ) + i)

theorem blk_eq_map (c n : ℕ) : blk c n = (blkZ c n).map (Int.cast : ℤ → ℚ) := by
  unfold blk blkZ
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp

/-- `Q_{Nj}` over `ℤ`. -/
def QpolyZ (N : ℕ) (j : Fin 3) : ℤ[X] :=
  ∑ r : Fin 4, Polynomial.C (Jmat N (Fin.castSucc j) r) *
    (-Polynomial.X - Polynomial.C (12 * (N : ℤ) + 1)) ^ (r : ℕ)

theorem Qpoly_eq_map (N : ℕ) (j : Fin 3) :
    Qpoly N j = (QpolyZ N j).map (Int.castRingHom ℚ) := by
  unfold Qpoly QpolyZ
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
  simp

theorem natDegree_Qpoly_le (N : ℕ) (j : Fin 3) : (Qpoly N j).natDegree ≤ 3 := by
  unfold Qpoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_pow_le).trans ?_
  have : (-Polynomial.X - Polynomial.C (12 * (N : ℚ) + 1)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
    · rw [Polynomial.natDegree_C]; omega
  have hr : (r : ℕ) ≤ 3 := by omega
  nlinarith

/-- The zeros of `R*_N` over `ℤ`. -/
def zeroSetStarZ (N : ℕ) : Multiset ℤ :=
  blkZ (N + 1) (11 * N) + blkZ 1 (11 * N) + blkZ (2 * N) (8 * N + 1)

theorem zeroSetStar_eq_map (N : ℕ) :
    zeroSetStar N = (zeroSetStarZ N).map (Int.cast : ℤ → ℚ) := by
  unfold zeroSetStar zeroSetStarZ
  rw [Multiset.map_add, Multiset.map_add, blk_eq_map, blk_eq_map, blk_eq_map]

theorem prod_X_sub_C_map (S : Multiset ℤ) :
    ((S.map (Int.cast : ℤ → ℚ)).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((S.map fun a => Polynomial.X - Polynomial.C a).prod).map (Int.castRingHom ℚ) := by
  rw [← Polynomial.coe_mapRingHom, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp

theorem natDegree_prod_X_sub_C' (S : Multiset ℚ) :
    ((S.map fun a => Polynomial.X - Polynomial.C a).prod).natDegree = Multiset.card S :=
  natDegree_prod_X_sub_C S

theorem card_poleSetStar (N : ℕ) : Multiset.card (poleSetStar N) = 30 * N + 2 := by
  simp [poleSetStar, blk]; ring

theorem card_zeroSetStar (N : ℕ) : Multiset.card (zeroSetStar N) = 30 * N + 1 := by
  simp [zeroSetStar, blk]; ring

/-- The polynomial part of `Q_{Nj} R*_N` is the quotient `(Q · Z) /ₘ D`. -/
theorem polyPart_dual_eq (N : ℕ) (j : Fin 3) :
    polyPart (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) =
      (Qpoly N j * ((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod) /ₘ
        ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod := by
  set A := Qpoly N j * ((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod with hA
  set D := ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod with hD
  have hDm : D.Monic := Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have hD0 : D ≠ 0 := hDm.ne_zero
  have hD' : algebraMap ℚ[X] ℚ⟮X⟯ D ≠ 0 := Aux.algebraMap_ne_zero' hD0
  have hdiv := Polynomial.modByMonic_add_div A D
  apply Aux.polyPart_eq_of
  rw [RkerStar_eq, ← mul_div_assoc, ← map_mul, ← hA, ← hD]
  have heq : algebraMap ℚ[X] ℚ⟮X⟯ A / algebraMap ℚ[X] ℚ⟮X⟯ D - algebraMap ℚ[X] ℚ⟮X⟯ (A /ₘ D) =
      algebraMap ℚ[X] ℚ⟮X⟯ (A %ₘ D) / algebraMap ℚ[X] ℚ⟮X⟯ D := by
    rw [eq_div_iff hD', sub_mul, div_mul_cancel₀ _ hD', ← map_mul, ← map_sub]
    congr 1
    linear_combination (-1 : ℚ[X]) * hdiv
  rw [heq]
  by_cases hR : A %ₘ D = 0
  · left; simp [hR]
  right
  have hD1 : D ≠ 1 := by
    intro h1
    have := congrArg Polynomial.natDegree h1
    rw [hD, natDegree_prod_X_sub_C', card_poleSetStar, Polynomial.natDegree_one] at this
    omega
  have := Polynomial.natDegree_modByMonic_lt A hDm hD1
  rw [RatFunc.intDegree_div (Aux.algebraMap_ne_zero' hR) hD', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  omega

/-- The polynomial part has integer coefficients. -/
theorem polyPart_dual_int (N : ℕ) (j : Fin 3) (n : ℕ) :
    ∃ z : ℤ, (polyPart (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N)).coeff n = z := by
  rw [polyPart_dual_eq, Qpoly_eq_map, zeroSetStar_eq_map, prod_X_sub_C_map, ← Polynomial.map_mul]
  have hDm : (((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod).Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  -- write the denominator as a map as well
  have hD : ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((((blkZ (13 * N + 1) (15 * N + 1) + blkZ (14 * N + 1) (15 * N + 1))).map
        fun a => Polynomial.X - Polynomial.C a).prod).map (Int.castRingHom ℚ) := by
    rw [← prod_X_sub_C_map, Multiset.map_add, ← blk_eq_map, ← blk_eq_map]; rfl
  have hDZm : ((((blkZ (13 * N + 1) (15 * N + 1) + blkZ (14 * N + 1) (15 * N + 1))).map
      fun a => Polynomial.X - Polynomial.C a).prod).Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  rw [hD, ← Polynomial.map_divByMonic _ hDZm, Polynomial.coeff_map]
  exact ⟨_, rfl⟩

theorem polyPart_dual_natDegree (N : ℕ) (j : Fin 3) :
    (polyPart (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N)).natDegree ≤ 2 := by
  rw [polyPart_dual_eq]
  have hDm : (((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod).Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  rw [Polynomial.natDegree_divByMonic _ hDm, natDegree_prod_X_sub_C', card_poleSetStar]
  have h1 := Polynomial.natDegree_mul_le (p := Qpoly N j)
    (q := ((zeroSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod)
  rw [natDegree_prod_X_sub_C', card_zeroSetStar] at h1
  have h2 := natDegree_Qpoly_le N j
  omega

/-! ### Bernoulli values -/

theorem bernoulli_two_eval (x : ℚ) : (Polynomial.bernoulli 2).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, _root_.bernoulli_zero, _root_.bernoulli_one,
    _root_.bernoulli_two]
  ring

end PolyPart

/-! ### Assembly: the dual bounds -/

section DualBounds

variable {p : ℕ} [Fact p.Prime]

theorem le_maxOn (s : Finset ℤ) (f : ℤ → ℤ) {k : ℤ} (hk : k ∈ s) : f k ≤ maxOn s f := by
  unfold maxOn
  rw [dite_eq_left ⟨k, hk⟩]
  exact Finset.le_sup' f hk

/-- The `Z_r`-coefficient of `𝓛_K[f]`, `r ≠ 0`, for general `f`. -/
theorem Lfun_apply_ne_zero' (K : ℤ) (f : ℚ⟮X⟯) (r : ℕ) (hr : r ≠ 0) :
    Lfun K f r = ∑ h ∈ f.denom.roots.toFinset, ∑ s ∈ Finset.range (f.denom.natDegree + 1),
      (s : ℚ) * pfCoeff f h s * (if s + 1 = r then 1 else 0) := by
  unfold Lfun
  simp [Zsym, Finsupp.single_apply, hr, Finset.sum_apply]

/-- The constant coefficient of `𝓛_K[f]` for general `f`. -/
theorem Lfun_apply_zero' (K : ℤ) (f : ℚ⟮X⟯) :
    Lfun K f 0 = (∑ m ∈ Finset.range ((polyPart f).natDegree + 1),
        (polyPart f).coeff m * (Polynomial.bernoulli m).eval ((K : ℚ) + 1)) +
      ∑ h ∈ f.denom.roots.toFinset, ∑ s ∈ Finset.range (f.denom.natDegree + 1),
        -((s : ℚ) * pfCoeff f h s * harm (s + 1) ⌊(K : ℚ) - h⌋) := by
  unfold Lfun
  simp [Zsym, Finset.sum_apply]

/-- The Bernoulli sum of an integer polynomial of degree `≤ 2` at an integer has denominator
dividing `6`. -/
theorem bernoulli_sum_val (P : ℚ[X]) (hint : ∀ n, ∃ z : ℤ, P.coeff n = z) (hdeg : P.natDegree ≤ 2)
    (x : ℤ) :
    Aux.ValGE p (-(padicValNat p 6 : ℤ)) (∑ m ∈ Finset.range (P.natDegree + 1),
      P.coeff m * (Polynomial.bernoulli m).eval ((x : ℚ) + 1)) := by
  obtain ⟨z0, h0⟩ := hint 0
  obtain ⟨z1, h1⟩ := hint 1
  obtain ⟨z2, h2⟩ := hint 2
  have hS : ∑ m ∈ Finset.range (P.natDegree + 1), P.coeff m * (Polynomial.bernoulli m).eval ((x : ℚ) + 1)
      = ∑ m ∈ Finset.range 3, P.coeff m * (Polynomial.bernoulli m).eval ((x : ℚ) + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun m _ hm => ?_
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range, not_lt] at hm; omega)]
    simp
  rw [hS]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, Polynomial.bernoulli_zero,
    Polynomial.bernoulli_one, Polynomial.eval_one, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, bernoulli_two_eval, zero_add]
  set w : ℤ := 6 * z0 + z1 * (6 * (x + 1) - 3) + z2 * (6 * (x + 1) ^ 2 - 6 * (x + 1) + 1) with hw
  have e : (z0 : ℚ) * 1 + (z1 : ℚ) * (((x : ℚ) + 1) - 2⁻¹) +
      (z2 : ℚ) * (((x : ℚ) + 1) ^ 2 - ((x : ℚ) + 1) + 1 / 6) = (w : ℚ) / ((6 : ℕ) : ℚ) := by
    rw [hw]; push_cast; ring
  rw [e]
  by_cases hw0 : (w : ℚ) = 0
  · left; rw [hw0, zero_div]
  · right
    rw [padicValRat.div hw0 (by norm_num), padicValRat.of_int, padicValRat.of_nat]
    have := Int.natCast_nonneg (padicValInt p w)
    linarith

/-- The Bernoulli sum of the derivative of an integer polynomial of degree `≤ 2` is an integer. -/
theorem bernoulli_sum_val_deriv (P : ℚ[X]) (hint : ∀ n, ∃ z : ℤ, P.coeff n = z)
    (hdeg : P.natDegree ≤ 2) (x : ℤ) :
    Aux.ValGE p 0 (∑ m ∈ Finset.range ((derivative P).natDegree + 1),
      (derivative P).coeff m * (Polynomial.bernoulli m).eval ((x : ℚ) + 1)) := by
  obtain ⟨z1, h1⟩ := hint 1
  obtain ⟨z2, h2⟩ := hint 2
  have hd : (derivative P).natDegree ≤ 1 := by
    have := Polynomial.natDegree_derivative_le P; omega
  have hS : ∑ m ∈ Finset.range ((derivative P).natDegree + 1),
      (derivative P).coeff m * (Polynomial.bernoulli m).eval ((x : ℚ) + 1)
      = ∑ m ∈ Finset.range 2, (derivative P).coeff m * (Polynomial.bernoulli m).eval ((x : ℚ) + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun m _ hm => ?_
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range, not_lt] at hm; omega)]
    simp
  rw [hS]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.coeff_derivative, h1, h2,
    Polynomial.bernoulli_zero, Polynomial.bernoulli_one, Polynomial.eval_one, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zero_add]
  have e : (z1 : ℚ) * ((0 : ℕ) + 1) * 1 + (z2 : ℚ) * ((1 : ℕ) + 1) * (((x : ℚ) + 1) - 2⁻¹) =
      ((z1 + z2 * (2 * x + 1) : ℤ) : ℚ) := by push_cast; ring
  rw [e]
  exact ValGE_int _

/-- Poles of the dual kernel lie in `[13N+1, 29N+1]`. -/
theorem dual_roots (N : ℕ) (j : Fin 3) :
    ∀ h ∈ (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N).denom.roots.toFinset,
      ∃ k : ℕ, 13 * N + 1 ≤ k ∧ k ≤ 29 * N + 1 ∧ h = -(k : ℚ) := by
  intro h hh
  have hdvd : (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N).denom ∣
      ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [RkerStar_eq, ← mul_div_assoc, ← map_mul]; exact RatFunc.denom_div_dvd _ _
  have hmem := Multiset.mem_of_le (Polynomial.roots.le_of_dvd (prod_X_sub_C_ne_zero _) hdvd)
    (Multiset.mem_toFinset.mp hh)
  rw [Polynomial.roots_multiset_prod_X_sub_C] at hmem
  simp only [poleSetStar, blk, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at hmem
  rcases hmem with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact ⟨13 * N + 1 + i, by omega, by omega, by push_cast; ring⟩
  · exact ⟨14 * N + 1 + i, by omega, by omega, by push_cast; ring⟩

theorem mult_Id_eq (N : ℕ) (k : ℤ) : mult (Id N) k =
    (if 13 * N + 1 ≤ k ∧ k ≤ 28 * N + 1 then 1 else 0) +
      (if 14 * N + 1 ≤ k ∧ k ≤ 29 * N + 1 then 1 else 0) := by
  simp only [mult, Id, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  push_cast
  split_ifs <;> omega

/-- Laurent coefficients of the derivative of the dual kernel. -/
theorem pfCoeff_dual_deriv (N : ℕ) (j : Fin 3) (k : ℕ) (hk1 : 13 * N + 1 ≤ k)
    (hk2 : k ≤ 29 * N + 1) (r : ℕ) :
    pfCoeff (rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N)) (-(k : ℚ)) (r + 1) =
      -(r : ℚ) * pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) (-(k : ℚ)) r := by
  set h : ℚ := -(k : ℚ) with hh
  set m : ℕ := (poleSetStar N).count h with hm
  set E : ℚ[X] := ((poleSetStar N).filter (· ≠ h)).map (fun a => Polynomial.X - Polynomial.C a)
    |>.prod with hE
  have hEval : E.eval h ≠ 0 := by
    rw [hE, eval_prod_X_sub_C]
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.mp h0
    have := (Multiset.mem_filter.mp ha).2
    exact this (by linarith)
  have hden : ((poleSetStar N).map fun a => Polynomial.X - Polynomial.C a).prod =
      (Polynomial.X - Polynomial.C h) ^ m * E := prod_X_sub_C_split _ h
  have hm1 : 1 ≤ m := by
    have hmult : (m : ℤ) = mult (Id N) k := count_poleSetStar N k
    rw [mult_Id_eq] at hmult
    split_ifs at hmult <;> omega
  rw [RkerStar_eq, ← mul_div_assoc, ← map_mul, hden, pfCoeff_rfDeriv_div _ _ h m hm1 hEval r]

/-- The dual kernel is `-k`-regular off its poles: the coefficient bound and the harmonic bound. -/
theorem dual_term_val (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) (k s : ℕ) (hk1 : 13 * N + 1 ≤ k)
    (hk2 : k ≤ 29 * N + 1) (hs : 1 ≤ s) (c : ℤ) (hc : 0 ≤ c) (hcL : c ≤ Ld N k) :
    Aux.ValGE p (Vd N p k - (mult (Id N) k - 1) * ellp p (Ld N k) - 2 * ellp p c)
      ((s : ℚ) * pfCoeff (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) (-(k : ℚ)) s *
        harm (s + 1) c) := by
  obtain ⟨hz, hb⟩ := pfCoeff_dual_valuation (p := p) N hN j k s hk1 hk2 hs
  by_cases hm : mult (Id N) k < s
  · rw [hz hm]; left; simp
  have hsm : (s : ℤ) ≤ mult (Id N) k := not_lt.mp hm
  have hs' : Aux.ValGE p 0 (s : ℚ) := by
    have := ValGE_int (p := p) s; simpa using this
  have hh := harm_valuation (p := p) (s + 1) c
  have := (hs'.mul hb).mul hh
  refine this.mono ?_
  have hL := Aux.ellp_nonneg p (Ld N k)
  have hc0 := Aux.ellp_nonneg p c
  have hmono := Aux.ellp_mono (Fact.out : p.Prime) hcL
  have hs1 : (1 : ℤ) ≤ s := by exact_mod_cast hs
  push_cast
  nlinarith

/-- The `Z₃`-coefficient of `𝓛_{-11N-1}[Q R*]`. -/
theorem dual_Lfun_three_val (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    Aux.ValGE p (-Ed N p)
      (Lfun (-11 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) 3) := by
  rw [Lfun_apply_ne_zero' _ _ 3 (by norm_num)]
  refine ValGE_sum _ _ _ fun h hh => ValGE_sum _ _ _ fun s _ => ?_
  obtain ⟨k, hk1, hk2, rfl⟩ := dual_roots N j h hh
  by_cases hs : s + 1 = 3
  · have hs2 : s = 2 := by omega
    subst hs2
    rw [ite_eq_left hs, mul_one]
    obtain ⟨hz, hb⟩ := pfCoeff_dual_valuation (p := p) N hN j k 2 hk1 hk2 (by norm_num)
    by_cases hm : mult (Id N) k < 2
    · rw [hz hm]; left; simp
    have h2 : Aux.ValGE p 0 ((2 : ℕ) : ℚ) := ValGE_int (p := p) 2
    have hprod := h2.mul hb
    refine hprod.mono ?_
    have hmax := le_maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1)) (fun k =>
      (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) - Vd N p k) (k := k)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hL := Aux.ellp_nonneg p (Ld N k)
    have hh' := Aux.ellp_nonneg p ((k : ℤ) - 11 * N - 1)
    have hm2 : (2 : ℤ) ≤ mult (Id N) k := by exact_mod_cast not_lt.mp hm
    unfold Ed
    have hmr := le_max_right (max (padicValNat p 6 : ℤ) 0)
      (maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1))
        fun k => (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) - Vd N p k)
    simp only [Nat.cast_ofNat, zero_add]
    nlinarith
  · rw [ite_eq_right hs, mul_zero]; exact Or.inl rfl

/-- The constant coefficient of `𝓛_{-11N-1}[Q R*]`. -/
theorem dual_Lfun_zero_val (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    Aux.ValGE p (-Ed N p)
      (Lfun (-11 * N - 1) (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N) 0) := by
  rw [Lfun_apply_zero']
  have hv6 : (padicValNat p 6 : ℤ) ≤ Ed N p := (le_max_left _ _).trans (le_max_left _ _)
  refine Aux.ValGE.add ?_ ?_
  · -- the polynomial part
    have := bernoulli_sum_val (p := p) _ (polyPart_dual_int N j) (polyPart_dual_natDegree N j)
      (-11 * N - 1)
    exact this.mono (by linarith)
  · refine ValGE_sum _ _ _ fun h hh => ValGE_sum _ _ _ fun s _ => ?_
    obtain ⟨k, hk1, hk2, rfl⟩ := dual_roots N j h hh
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · left; simp
    refine Aux.ValGE.neg ?_
    have hfl : ⌊((-11 * N - 1 : ℤ) : ℚ) - -(k : ℚ)⌋ = (k : ℤ) - 11 * N - 1 := by
      rw [show ((-11 * N - 1 : ℤ) : ℚ) - -(k : ℚ) = (((k : ℤ) - 11 * N - 1 : ℤ) : ℚ) by push_cast; ring,
        Int.floor_intCast]
    rw [hfl]
    have := dual_term_val (p := p) N hN j k s hk1 hk2 hs1 ((k : ℤ) - 11 * N - 1) (by omega)
      (by unfold Ld; omega)
    refine this.mono ?_
    have hmax := le_maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1)) (fun k =>
      (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) - Vd N p k) (k := k)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    unfold Ed
    have := le_max_right (max (padicValNat p 6 : ℤ) 0) (maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1))
      fun k => (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) - Vd N p k)
    linarith

/-- The constant coefficient of `𝓛_{-10N-1}[(Q R*)']` (the second functional). -/
theorem dual_Lfun_deriv_zero_val (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    Aux.ValGE p (-Ed4 N p)
      (Lfun (-10 * N - 1) (rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N)) 0) := by
  rw [Lfun_apply_zero', polyPart_rfDeriv]
  have hE4 : (0 : ℤ) ≤ Ed4 N p := le_max_left _ _
  refine Aux.ValGE.add ?_ ?_
  · have := bernoulli_sum_val_deriv (p := p) _ (polyPart_dual_int N j) (polyPart_dual_natDegree N j)
      (-10 * N - 1)
    exact this.mono (by push_cast at this ⊢; linarith)
  · refine ValGE_sum _ _ _ fun h hh => ValGE_sum _ _ _ fun s _ => ?_
    -- the poles of the derivative are poles of `f`
    have hroot : ∃ k : ℕ, 13 * N + 1 ≤ k ∧ k ≤ 29 * N + 1 ∧ h = -(k : ℚ) := by
      refine dual_roots N j h ?_
      rw [Multiset.mem_toFinset] at hh ⊢
      have hdvd : (rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N)).denom ∣
          (algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N).denom ^ 2 := RatFunc.denom_div_dvd _ _
      have := Multiset.mem_of_le (Polynomial.roots.le_of_dvd (pow_ne_zero _
        (RatFunc.denom_ne_zero _)) hdvd) hh
      rw [Polynomial.roots_pow] at this
      exact Multiset.mem_of_mem_nsmul this
    obtain ⟨k, hk1, hk2, rfl⟩ := hroot
    rcases s with _ | _ | s
    · left; simp
    · -- `s = 1`: the residue of a derivative vanishes
      rw [pfCoeff_dual_deriv N j k hk1 hk2 0]; left; simp
    · refine Aux.ValGE.neg ?_
      have hfl : ⌊((-10 * N - 1 : ℤ) : ℚ) - -(k : ℚ)⌋ = (k : ℤ) - 10 * N - 1 := by
        rw [show ((-10 * N - 1 : ℤ) : ℚ) - -(k : ℚ) = (((k : ℤ) - 10 * N - 1 : ℤ) : ℚ) by
          push_cast; ring, Int.floor_intCast]
      rw [hfl, pfCoeff_dual_deriv N j k hk1 hk2 (s + 1)]
      -- `(s+2) · (-(s+1) c_{s+1}) · H^{(s+3)}`
      obtain ⟨hz, hb⟩ := pfCoeff_dual_valuation (p := p) N hN j k (s + 1) hk1 hk2 (by omega)
      by_cases hm : mult (Id N) k < s + 1
      · rw [hz hm]; left; simp
      have hsm : ((s + 1 : ℕ) : ℤ) ≤ mult (Id N) k := not_lt.mp hm
      have h1 : Aux.ValGE p 0 (((s + 1 + 1 : ℕ) : ℚ)) := by
        have := ValGE_int (p := p) ((s + 1 + 1 : ℕ) : ℤ); simpa using this
      have h2 : Aux.ValGE p 0 (-((s + 1 : ℕ) : ℚ)) := by
        have := ValGE_int (p := p) (-((s + 1 : ℕ) : ℤ)); simpa using this
      have hh := harm_valuation (p := p) (s + 1 + 1 + 1) ((k : ℤ) - 10 * N - 1)
      have := (h1.mul (h2.mul hb)).mul hh
      refine this.mono ?_
      have hmax := le_maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1)) (fun k =>
        (mult (Id N) k - 1) * ellp p (Ld N k) + 3 * ellp p (k - 10 * N - 1) - Vd N p k) (k := k)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hL := Aux.ellp_nonneg p (Ld N k)
      have hc0 := Aux.ellp_nonneg p ((k : ℤ) - 10 * N - 1)
      have hmono := Aux.ellp_mono (Fact.out : p.Prime)
        (show (k : ℤ) - 10 * N - 1 ≤ Ld N k by unfold Ld; omega)
      unfold Ed4
      have := le_max_right (0 : ℤ) (maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1))
        fun k => (mult (Id N) k - 1) * ellp p (Ld N k) + 3 * ellp p (k - 10 * N - 1) - Vd N p k)
      push_cast at hsm ⊢
      nlinarith

end DualBounds

/-- **[6] Bounds from the first dual formula** (every prime). By [4], `p^{(3)}_{Nj}` and `q_{Nj}`
are `∓(-1)^N 3` times the `Z₀`- and `Z₃`-coefficients of `𝓛_{-11N-1}[Q_{Nj} R*_N]`. The dual pole
argument (pole orders `m ≤ 2`, top valuation `V_d(k)`, Taylor loss `(m-1) ℓ_p(L(k))`, harmonic
loss `2ℓ_p(k-11N-1)`; the polynomial part has degree `≤ 2`, so its Bernoulli values have
denominator dividing `6`) bounds these coefficients by `-E_d`.
* Lines: proved here (the pole argument is `pfCoeff_dual_valuation`, the same `PSBound`
  machinery as [1] applied to the zeros and poles of `R*_N` and the integer polynomial `Q_{Nj}`;
  the polynomial part is `polyPart_dual_int`/`bernoulli_sum_val`; the assembly uses [4]).
* Directly from the PDF: partially (same caveat as [1]). -/
theorem dual_bounds_p3_q (N : ℕ) (hN : 1 ≤ N) (p : ℕ) [Fact p.Prime] (j : Fin 3) :
    (p3 N j ≠ 0 → -Ed N p ≤ padicValRat p (p3 N j)) ∧
    (q N j ≠ 0 → -Ed N p ≤ padicValRat p (q N j)) := by
  have hid := dual_first_identity N j
  set f := algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N with hf
  set K : ℤ := -11 * N - 1 with hK
  have h3 : (-1 : ℚ) ^ N * 3 * Lfun K f 3 = q N j := by
    have := DFunLike.congr_fun hid 3
    simpa [Zsym, Finsupp.single_apply] using this
  have h0 : (-1 : ℚ) ^ N * 3 * Lfun K f 0 = -p3 N j := by
    have := DFunLike.congr_fun hid 0
    simpa [Zsym, Finsupp.single_apply] using this
  have hc : Aux.ValGE p 0 ((-1 : ℚ) ^ N * 3) := by
    have := ValGE_int (p := p) ((-1) ^ N * 3); simpa using this
  have hL3 := dual_Lfun_three_val (p := p) N hN j
  have hL0 := dual_Lfun_zero_val (p := p) N hN j
  constructor
  · intro hne
    rcases hc.mul hL0 with h | h
    · rw [h0] at h; exact absurd (neg_eq_zero.mp h) hne
    · rw [h0, padicValRat.neg] at h; linarith
  · intro hne
    rcases hc.mul hL3 with h | h
    · rw [h3] at h; exact absurd h hne
    · rw [h3] at h; linarith

/-- **[7] Bound from the second dual formula** (every prime). By [5], `p^{(4)}_{Nj}` is `∓(-1)^N`
times the `Z₀`-coefficient of `𝓜_{-10N-1}[Q_{Nj} R*_N]`. The pole argument with harmonic factor
loss `(r+2) ℓ_p(h₄)` and `L ≥ h₄` gives `v_p ≥ V_d - (m-1)ℓ_p(L) - 3ℓ_p(h₄) ≥ -E_{d4}`. The
polynomial part has integral `𝓜`-value (`𝓜_K[1] = 0`, `𝓜_K[t] = -1`, `𝓜_K[t²] = -(2K+1)`).
* Lines: proved here (the Laurent coefficients of the derivative are `-r c_{h,r}`,
  `pfCoeff_rfDeriv_div`; the polynomial part of `𝓜` is integral, `bernoulli_sum_val_deriv`).
* Directly from the PDF: partially. -/
theorem dual_bound_p4 (N : ℕ) (hN : 1 ≤ N) (p : ℕ) [Fact p.Prime] (j : Fin 3) :
    p4 N j ≠ 0 → -Ed4 N p ≤ padicValRat p (p4 N j) := by
  intro hne
  have hid := pairing_identity N j
  set f := algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly N j) * RkerStar N with hf
  set K : ℤ := -10 * N - 1 with hK
  have h0 : (-1 : ℚ) ^ N * Lfun K (rfDeriv f) 0 = p4 N j := by
    have := DFunLike.congr_fun hid 0
    simp [Zsym, Finsupp.single_apply, Mfun] at this
    linarith
  have hc : Aux.ValGE p 0 ((-1 : ℚ) ^ N) := by
    have := ValGE_int (p := p) ((-1) ^ N); simpa using this
  have hL := dual_Lfun_deriv_zero_val (p := p) N hN j
  rcases hc.mul hL with h | h
  · rw [h0] at h; exact absurd h hne
  · rw [h0] at h; linarith

/-- **[8] Large primes do not occur.** For `p > 29N+1`, every argument of `f_p`, `ℓ_p` and `G_p`
in `E_d`, `E_{d4}` is `< p`, so everything vanishes, and `v_p(6) = 0`.
* Lines: proved here.
* Directly from the PDF: yes ("No prime larger than `29N+1` occurs"). -/
theorem Ed_Ed4_eq_zero_of_lt (N p : ℕ) (hN : 1 ≤ N) (hp : p.Prime) (hlt : 29 * N + 1 < p) :
    Ed N p = 0 ∧ Ed4 N p = 0 := by
  have hfp : ∀ m : ℤ, m < p → fp p m = 0 := fun m hm => Aux.fp_eq_zero_of_lt hp hm
  have hl : ∀ m : ℤ, m < p → ellp p m = 0 := fun m hm => Aux.ellp_eq_zero_of_lt hp hm
  have h6 : padicValNat p 6 = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hVd : ∀ k ∈ Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1), Vd N p k = 0 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    simp only [Vd, Gp, Id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp (disch := omega) only [hfp]
    simp
  have hterm : ∀ (c : ℤ), ∀ k ∈ Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1),
      (mult (Id N) k - 1) * ellp p (Ld N k) + c * ellp p (k - 11 * N - 1) - Vd N p k = 0 ∧
      (mult (Id N) k - 1) * ellp p (Ld N k) + c * ellp p (k - 10 * N - 1) - Vd N p k = 0 := by
    intro c k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hLd : Ld N k < p := by unfold Ld; omega
    rw [hVd k hk, hl _ hLd, hl (k - 11 * N - 1) (by omega), hl (k - 10 * N - 1) (by omega)]
    simp
  constructor
  · unfold Ed
    rw [Aux.maxOn_congr_zero _ _ fun k hk => (hterm 2 k hk).1, h6]
    simp
  · unfold Ed4
    rw [Aux.maxOn_congr_zero _ _ fun k hk => (hterm 3 k hk).2]
    simp

/-- **Main theorem (`blueprint.lean`, `valuation_bound`).** Proved from [3], [6], [7], [8]. -/
theorem valuation_bound (N : ℕ) (hN : 1 ≤ N) (p : ℕ) [hp : Fact p.Prime] (i j : Fin 3)
    (hne : Rmat N i j ≠ 0) :
    (if p ≤ 29 * N + 1 then -E34 N p else 0) ≤ padicValRat p (Rmat N i j) := by
  -- the generic step: a lower bound by `-E` for `E ∈ {E_d, E_{d4}}` and, if `p > 3`, by `-E'`
  -- for the matching original bound, gives the claim
  have key : ∀ (v : ℤ) (Eorig Edual : ℤ),
      -Edual ≤ v → (3 < p → -Eorig ≤ v) →
      (3 < p → min Eorig Edual ≤ E34 N p) → (¬ 3 < p → Edual ≤ E34 N p) →
      (¬ p ≤ 29 * N + 1 → Edual = 0) →
      (if p ≤ 29 * N + 1 then -E34 N p else 0) ≤ v := by
    intro v Eo' Ed' hd ho hmin hle hzero
    split_ifs with hle29
    · by_cases h3 : 3 < p
      · have := hmin h3
        have := ho h3
        have : -v ≤ min Eo' Ed' := le_min (by linarith) (by linarith)
        linarith
      · linarith [hle h3]
    · linarith [hzero hle29]
  have hE34_3 : ¬ 3 < p → E34 N p = max (Ed N p) (Ed4 N p) := fun h => by simp [E34, h]
  have hE34_gt : 3 < p → E34 N p = max (min (Eo N p) (Ed N p)) (min (Eo4 N p) (Ed4 N p)) :=
    fun h => by simp [E34, h]
  have hzero := fun h => Ed_Ed4_eq_zero_of_lt N p hN hp.out (not_le.mp h)
  fin_cases i
  · -- `p^{(3)}`
    exact key _ (Eo N p) (Ed N p) ((dual_bounds_p3_q N hN p j).1 hne)
      (fun h => (original_bounds N hN p h j).1 hne)
      (fun h => by rw [hE34_gt h]; exact le_max_left _ _)
      (fun h => by rw [hE34_3 h]; exact le_max_left _ _) (fun h => (hzero h).1)
  · -- `p^{(4)}`
    exact key _ (Eo4 N p) (Ed4 N p) (dual_bound_p4 N hN p j hne)
      (fun h => (original_bounds N hN p h j).2.2 hne)
      (fun h => by rw [hE34_gt h]; exact le_max_right _ _)
      (fun h => by rw [hE34_3 h]; exact le_max_right _ _) (fun h => (hzero h).2)
  · -- `q`
    exact key _ (Eo N p) (Ed N p) ((dual_bounds_p3_q N hN p j).2 hne)
      (fun h => (original_bounds N hN p h j).2.1 hne)
      (fun h => by rw [hE34_gt h]; exact le_max_left _ _)
      (fun h => by rw [hE34_3 h]; exact le_max_left _ _) (fun h => (hzero h).1)

end ZetasIrr.BP
