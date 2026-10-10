/-
# `ZetasIrr.cross_product_readout`: complete formalization

Statement (as in `blueprint.lean`): as row vectors in `j`,
  `ζ(3) q_N - p^{(3)}_N = -(A_N × S_N)/det V_N`,  `ζ(4) q_N - p^{(4)}_N = (B_N × S_N)/det V_N`.

Source: PDF Part II ("Consequently, as row-vector identities …"), Part VII §2 (the partial
fraction expansion of `-∑_{t ≥ 2N+1} d/dt((-t)^j R_N(t))`), Part VII §6 (the cross-product
identity) and Part VII §7 (the formal functional `𝓛_K`, "for a proper rational function this
is the formal value of `-∑_{t>K} f'(t)`").

This file contains no `sorry`. It proves all the supporting lemmas of the blueprint:

* `S_eq` (`S_{Nj} = A_{Nj} ζ(4) + B_{Nj} ζ(3) + C_{Nj}`), via
  - partial fractions over `ℚ(t)` for denominators that split (`exists_isPF`,
    `exists_eq_ppSum`), with the coefficients identified with the Laurent coefficients
    `pfCoeff` (`pfCoeff_ppSum`);
  - **formal = analytic** (`derivSum_eq_realize_Lfun'`). The hypothesis that the
    denominator splits over `ℚ` is needed. The version in `blueprint.lean` without it is
    false: `1/(t² + 1)` has no rational poles, so `𝓛_K` vanishes, but the sum does not;
  - the kernel facts: `(-t)^j R_N` is proper of degree `j - 4`, its poles are the integers
    `-k`, `0 ≤ k ≤ 12N`, of order `≤ 3`, and its residues sum to zero, so only
    `1, Z₃, Z₄` occur (`Lfun_linFormKernel_support`);
* `det_coeffMat_eq`, `U34_mul_C0_transpose`, `inv_transpose_eq_cross`, `readouts_eq_cross`.
  The readouts are `q = -(A×B)/det V`, `p^{(3)} = -(C×A)/det V`, `p^{(4)} = -(B×C)/det V`.
  When `det V_N = 0`, both sides vanish under Lean's conventions `M⁻¹ = 0` and `0⁻¹ = 0`.
-/
import defs

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr

/-! ## Part 1. Laurent coefficients -/

theorem pfCoeff_add (f g : ℚ⟮X⟯) (h : ℚ) (r : ℕ) :
    pfCoeff (f + g) h r = pfCoeff f h r + pfCoeff g h r := by
  simp [pfCoeff, map_add]

theorem pfCoeff_C_mul (c : ℚ) (f : ℚ⟮X⟯) (h : ℚ) (r : ℕ) :
    pfCoeff (RatFunc.C c * f) h r = c * pfCoeff f h r := by
  simp only [pfCoeff, map_mul, RatFunc.laurent_C]
  rw [show algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (RatFunc.C c) = HahnSeries.C c by
    rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, ← RatFunc.coe_coe,
      Polynomial.coe_C, PowerSeries.coe_C]]
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem pfCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ⟮X⟯) (h : ℚ) (r : ℕ) :
    pfCoeff (∑ i ∈ s, f i) h r = ∑ i ∈ s, pfCoeff (f i) h r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pfCoeff]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pfCoeff_add, ih]

theorem pfCoeff_inv_pow (a h : ℚ) (s r : ℕ) (hr : 1 ≤ r) :
    pfCoeff (((RatFunc.X - RatFunc.C a) ^ s)⁻¹) h r = if a = h ∧ s = r then 1 else 0 := by
  have hC : ∀ x : ℚ, algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (RatFunc.C x) = HahnSeries.C x := fun x => by
    rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, ← RatFunc.coe_coe,
      Polynomial.coe_C, PowerSeries.coe_C]
  simp only [pfCoeff, map_inv₀, map_pow, map_sub, RatFunc.laurent_X, RatFunc.laurent_C, map_add,
    RatFunc.coe_X, hC]
  by_cases hah : a = h
  · subst hah
    rw [add_sub_cancel_right, HahnSeries.single_pow, HahnSeries.inv_single]
    simp only [one_pow, nsmul_eq_mul, mul_one, inv_one, HahnSeries.coeff_single]
    by_cases hsr : s = r
    · subst hsr; simp
    · have : -(r : ℤ) ≠ -(s : ℤ) := by omega
      simp [this, hsr]
  · simp only [hah, false_and, ↓reduceIte]
    have hd : h - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hah)
    set P : PowerSeries ℚ := PowerSeries.X + PowerSeries.C (h - a) with hP
    have hPc : PowerSeries.constantCoeff P ≠ 0 := by simp [hP, hd]
    have hPL : ((P : PowerSeries ℚ) : ℚ⸨X⸩) = HahnSeries.single 1 1 + HahnSeries.C h - HahnSeries.C a := by
      rw [hP, PowerSeries.coe_add, PowerSeries.coe_X, PowerSeries.coe_C, map_sub, add_sub_assoc]
    rw [← hPL]
    have hinv : (((P : ℚ⸨X⸩)) ^ s)⁻¹ = ((P⁻¹ ^ s : PowerSeries ℚ) : ℚ⸨X⸩) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← PowerSeries.coe_pow, ← PowerSeries.coe_mul, ← mul_pow, PowerSeries.mul_inv_cancel _ hPc,
        one_pow, PowerSeries.coe_one]
    rw [hinv, PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · exact absurd (by omega : -(r : ℤ) < 0) hneg

/-! ## Part 2. Partial fractions -/

/-- A sum of principal parts `∑_{h ∈ R} ∑_{1 ≤ r ≤ b h} c_{h,r} (t - h)^{-r}`. -/
def ppSum (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) : ℚ⟮X⟯ :=
  ∑ h ∈ R, ∑ r ∈ Finset.Icc 1 (b h), RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹

/-- `f` is a polynomial plus principal parts at the poles `R` with orders bounded by `b`. -/
def IsPF (R : Finset ℚ) (b : ℚ → ℕ) (f : ℚ⟮X⟯) : Prop :=
  ∃ (P : ℚ[X]) (c : ℚ → ℕ → ℚ), f = algebraMap ℚ[X] ℚ⟮X⟯ P + ppSum R b c

theorem X_sub_C_ne_zero' (h : ℚ) : (RatFunc.X - RatFunc.C h : ℚ⟮X⟯) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] ℚ⟮X⟯)).mpr (Polynomial.X_sub_C_ne_zero h)

theorem ppSum_add (R : Finset ℚ) (b : ℚ → ℕ) (c₁ c₂ : ℚ → ℕ → ℚ) :
    ppSum R b (fun h r => c₁ h r + c₂ h r) = ppSum R b c₁ + ppSum R b c₂ := by
  simp only [ppSum, map_add, add_mul, Finset.sum_add_distrib]

theorem ppSum_C_mul (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) (k : ℚ) :
    ppSum R b (fun h r => k * c h r) = RatFunc.C k * ppSum R b c := by
  simp only [ppSum, map_mul, Finset.mul_sum, mul_assoc]

theorem ppSum_zero (R : Finset ℚ) (b : ℚ → ℕ) : ppSum R b (fun _ _ => 0) = 0 := by
  simp [ppSum]

theorem ppSum_single (R : Finset ℚ) (b : ℚ → ℕ) {h₀ : ℚ} (hh : h₀ ∈ R) {r₀ : ℕ} (hr₁ : 1 ≤ r₀)
    (hr₂ : r₀ ≤ b h₀) (e : ℚ) :
    ppSum R b (fun h r => if h = h₀ ∧ r = r₀ then e else 0) =
      RatFunc.C e * ((RatFunc.X - RatFunc.C h₀) ^ r₀)⁻¹ := by
  unfold ppSum
  rw [Finset.sum_eq_single h₀]
  · rw [Finset.sum_eq_single r₀]
    · simp
    · intro r _ hr; simp [hr]
    · intro hn; exact absurd (Finset.mem_Icc.mpr ⟨hr₁, hr₂⟩) hn
  · intro h _ hne; exact Finset.sum_eq_zero fun r _ => by simp [hne]
  · intro hn; exact absurd hh hn

section IsPF

variable {R : Finset ℚ} {b : ℚ → ℕ}

theorem IsPF.poly (P : ℚ[X]) : IsPF R b (algebraMap ℚ[X] ℚ⟮X⟯ P) :=
  ⟨P, fun _ _ => 0, by rw [ppSum_zero, add_zero]⟩

theorem IsPF.zero : IsPF R b 0 := by simpa using IsPF.poly (R := R) (b := b) 0

theorem IsPF.add {f g : ℚ⟮X⟯} (hf : IsPF R b f) (hg : IsPF R b g) : IsPF R b (f + g) := by
  obtain ⟨P₁, c₁, rfl⟩ := hf
  obtain ⟨P₂, c₂, rfl⟩ := hg
  exact ⟨P₁ + P₂, fun h r => c₁ h r + c₂ h r, by rw [ppSum_add, map_add]; ring⟩

theorem IsPF.C_mul (k : ℚ) {f : ℚ⟮X⟯} (hf : IsPF R b f) : IsPF R b (RatFunc.C k * f) := by
  obtain ⟨P, c, rfl⟩ := hf
  exact ⟨Polynomial.C k * P, fun h r => k * c h r, by
    rw [ppSum_C_mul, map_mul, RatFunc.algebraMap_C]; ring⟩

theorem IsPF.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ⟮X⟯) (hf : ∀ i ∈ s, IsPF R b (f i)) :
    IsPF R b (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPF.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem IsPF.basic {h₀ : ℚ} (hh : h₀ ∈ R) {r₀ : ℕ} (hr₁ : 1 ≤ r₀) (hr₂ : r₀ ≤ b h₀) (e : ℚ) :
    IsPF R b (RatFunc.C e * ((RatFunc.X - RatFunc.C h₀) ^ r₀)⁻¹) :=
  ⟨0, _, by rw [ppSum_single R b hh hr₁ hr₂, map_zero, zero_add]⟩

theorem IsPF.poly_mul_inv {h₀ : ℚ} (hh : h₀ ∈ R) (hb : 1 ≤ b h₀) (P : ℚ[X]) :
    IsPF R b (algebraMap ℚ[X] ℚ⟮X⟯ P * (RatFunc.X - RatFunc.C h₀)⁻¹) := by
  have hdiv := Polynomial.modByMonic_add_div P (Polynomial.X - Polynomial.C h₀)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hdiv
  have hu := X_sub_C_ne_zero' h₀
  have : algebraMap ℚ[X] ℚ⟮X⟯ P * (RatFunc.X - RatFunc.C h₀)⁻¹ =
      algebraMap ℚ[X] ℚ⟮X⟯ (P /ₘ (Polynomial.X - Polynomial.C h₀)) +
        RatFunc.C (P.eval h₀) * ((RatFunc.X - RatFunc.C h₀) ^ 1)⁻¹ := by
    conv_lhs => rw [← hdiv]
    simp only [map_add, map_mul, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X, pow_one]
    field_simp
    ring
  rw [this]
  exact (IsPF.poly _).add (IsPF.basic hh le_rfl hb _)

theorem inv_mul_inv_eq (h h₀ : ℚ) (hne : h ≠ h₀) :
    (RatFunc.X - RatFunc.C h)⁻¹ * (RatFunc.X - RatFunc.C h₀)⁻¹ =
      RatFunc.C (h - h₀)⁻¹ * ((RatFunc.X - RatFunc.C h)⁻¹ - (RatFunc.X - RatFunc.C h₀)⁻¹) := by
  have hu := X_sub_C_ne_zero' h
  have hv := X_sub_C_ne_zero' h₀
  have key : (RatFunc.X - RatFunc.C h₀) - (RatFunc.X - RatFunc.C h) = RatFunc.C (h - h₀) := by
    rw [map_sub]; ring
  have hd : (RatFunc.X - RatFunc.C h₀) - (RatFunc.X - RatFunc.C h) ≠ 0 := by
    rw [key]; exact (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hne)
  rw [map_inv₀, ← key]
  field_simp

theorem IsPF.inv_pow_mul_inv {h h₀ : ℚ} (hh : h ∈ R) (hh₀ : h₀ ∈ R) (r : ℕ) (hr₁ : 1 ≤ r)
    (hr₂ : r ≤ b h) (hb₀ : 1 ≤ b h₀) (heq : h = h₀ → r + 1 ≤ b h₀) :
    IsPF R b (((RatFunc.X - RatFunc.C h) ^ r)⁻¹ * (RatFunc.X - RatFunc.C h₀)⁻¹) := by
  by_cases hhe : h = h₀
  · subst hhe
    have : ((RatFunc.X - RatFunc.C h) ^ r)⁻¹ * (RatFunc.X - RatFunc.C h)⁻¹ =
        RatFunc.C 1 * ((RatFunc.X - RatFunc.C h) ^ (r + 1))⁻¹ := by
      rw [map_one, one_mul, pow_succ, mul_inv]
    rw [this]
    exact IsPF.basic hh (by omega) (heq rfl) 1
  · clear heq
    induction r, hr₁ using Nat.le_induction with
    | base =>
      have : ((RatFunc.X - RatFunc.C h) ^ 1)⁻¹ * (RatFunc.X - RatFunc.C h₀)⁻¹ =
          RatFunc.C (h - h₀)⁻¹ * ((RatFunc.X - RatFunc.C h) ^ 1)⁻¹ +
            RatFunc.C (-(h - h₀)⁻¹) * ((RatFunc.X - RatFunc.C h₀) ^ 1)⁻¹ := by
        rw [pow_one, pow_one, inv_mul_inv_eq h h₀ hhe, map_neg]; ring
      rw [this]
      exact (IsPF.basic hh le_rfl hr₂ _).add (IsPF.basic hh₀ le_rfl hb₀ _)
    | succ r hr ih =>
      have : ((RatFunc.X - RatFunc.C h) ^ (r + 1))⁻¹ * (RatFunc.X - RatFunc.C h₀)⁻¹ =
          RatFunc.C (h - h₀)⁻¹ * ((RatFunc.X - RatFunc.C h) ^ (r + 1))⁻¹ +
            RatFunc.C (-(h - h₀)⁻¹) *
              (((RatFunc.X - RatFunc.C h) ^ r)⁻¹ * (RatFunc.X - RatFunc.C h₀)⁻¹) := by
        rw [pow_succ, mul_inv, mul_assoc, inv_mul_inv_eq h h₀ hhe, map_neg]; ring
      rw [this]
      exact (IsPF.basic hh (by omega) hr₂ _).add (IsPF.C_mul _ (ih (by omega)))

theorem IsPF.mul_inv {h₀ : ℚ} (hh₀ : h₀ ∈ R) {f : ℚ⟮X⟯} (hf : IsPF R b f) :
    IsPF R (fun h => b h + if h = h₀ then 1 else 0) (f * (RatFunc.X - RatFunc.C h₀)⁻¹) := by
  obtain ⟨P, c, rfl⟩ := hf
  have hb₀ : 1 ≤ b h₀ + if h₀ = h₀ then 1 else 0 := by simp
  rw [add_mul]
  refine (IsPF.poly_mul_inv hh₀ hb₀ P).add ?_
  unfold ppSum
  rw [Finset.sum_mul]
  refine IsPF.sum _ _ fun h hh => ?_
  rw [Finset.sum_mul]
  refine IsPF.sum _ _ fun r hr => ?_
  obtain ⟨hr₁, hr₂⟩ := Finset.mem_Icc.mp hr
  rw [mul_assoc]
  refine IsPF.C_mul _ (IsPF.inv_pow_mul_inv hh hh₀ r hr₁ (by omega) hb₀ fun he => ?_)
  subst he; simp; omega

theorem IsPF.multiset_prod (P : ℚ[X]) (S : Multiset ℚ) (hS : ∀ x ∈ S, x ∈ R) :
    IsPF R (fun h => S.count h)
      (algebraMap ℚ[X] ℚ⟮X⟯ P * (S.map fun h => (RatFunc.X - RatFunc.C h)⁻¹).prod) := by
  induction S using Multiset.induction_on with
  | empty => simpa using IsPF.poly (R := R) (b := fun _ => 0) P
  | cons a S ih =>
    have := (ih fun x hx => hS x (Multiset.mem_cons_of_mem hx)).mul_inv
      (hS a (Multiset.mem_cons_self a S))
    have hb : (fun h => (a ::ₘ S).count h) = fun h => S.count h + if h = a then 1 else 0 := by
      funext h; rw [Multiset.count_cons]
    rw [hb, Multiset.map_cons, Multiset.prod_cons, mul_comm _ (Multiset.prod _), ← mul_assoc]
    exact this

end IsPF

/-- Existence of the partial-fraction decomposition when the denominator splits. -/
theorem exists_isPF (f : ℚ⟮X⟯) (hsplit : f.denom.roots.card = f.denom.natDegree) :
    IsPF f.denom.roots.toFinset (fun h => f.denom.roots.count h) f := by
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (RatFunc.monic_denom f) hsplit
  have hden : algebraMap ℚ[X] ℚ⟮X⟯ f.denom =
      (f.denom.roots.map fun h => RatFunc.X - RatFunc.C h).prod := by
    conv_lhs => rw [← hprod]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro h _
    simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hf : f = algebraMap ℚ[X] ℚ⟮X⟯ f.num *
      (f.denom.roots.map fun h => (RatFunc.X - RatFunc.C h)⁻¹).prod := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [div_eq_mul_inv, hden, Multiset.prod_map_inv]
  have := IsPF.multiset_prod (R := f.denom.roots.toFinset) f.num f.denom.roots
    fun x hx => Multiset.mem_toFinset.mpr hx
  rwa [← hf] at this

/-! ## Part 3. Degrees, coefficients, residues -/

/-! ### Degree bounds -/

/-- `g = 0` or `deg g ≤ k`. -/
def DegLE (k : ℤ) (g : ℚ⟮X⟯) : Prop := g = 0 ∨ g.intDegree ≤ k

theorem DegLE.add {k : ℤ} {x y : ℚ⟮X⟯} (hx : DegLE k x) (hy : DegLE k y) : DegLE k (x + y) := by
  rcases hy with rfl | hy
  · rw [add_zero]; exact hx
  rcases hx with rfl | hx
  · rw [zero_add]; exact Or.inr hy
  by_cases hy0 : y = 0
  · subst hy0; rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy))

theorem DegLE.neg {k : ℤ} {x : ℚ⟮X⟯} (hx : DegLE k x) : DegLE k (-x) := by
  rcases hx with rfl | hx
  · simp [DegLE]
  · exact Or.inr (by rwa [RatFunc.intDegree_neg])

theorem DegLE.C_mul {k : ℤ} (c : ℚ) {x : ℚ⟮X⟯} (hx : DegLE k x) : DegLE k (RatFunc.C c * x) := by
  by_cases hc : c = 0
  · simp [DegLE, hc]
  rcases hx with rfl | hx
  · simp [DegLE]
  by_cases hx0 : x = 0
  · simp [DegLE, hx0]
  right
  rw [RatFunc.intDegree_mul ((_root_.map_ne_zero _).mpr hc) hx0, RatFunc.intDegree_C, zero_add]
  exact hx

theorem DegLE.mono {k k' : ℤ} (hk : k ≤ k') {x : ℚ⟮X⟯} (hx : DegLE k x) : DegLE k' x :=
  hx.imp id fun h => h.trans hk

theorem DegLE.sum {k : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ⟮X⟯) (hf : ∀ i ∈ s, DegLE k (f i)) :
    DegLE k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DegLE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem intDegree_X_sub_C_pow (h : ℚ) (r : ℕ) :
    ((RatFunc.X - RatFunc.C h) ^ r : ℚ⟮X⟯).intDegree = r := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub, ← map_pow,
    RatFunc.intDegree_polynomial, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

theorem DegLE.basic (h c : ℚ) (r : ℕ) :
    DegLE (-r) (RatFunc.C c * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹) :=
  DegLE.C_mul c (Or.inr (by rw [RatFunc.intDegree_inv, intDegree_X_sub_C_pow]))

theorem DegLE.ppSum (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) : DegLE (-1) (ppSum R b c) :=
  DegLE.sum _ _ fun h _ => DegLE.sum _ _ fun r hr =>
    (DegLE.basic h (c h r) r).mono (by have := (Finset.mem_Icc.mp hr).1; omega)

theorem DegLE.of_proper {f : ℚ⟮X⟯} (hproper : f.num.natDegree < f.denom.natDegree) :
    DegLE (-1) f := by
  right; unfold RatFunc.intDegree; omega

/-- For a proper `f` whose denominator splits, `f` is the sum of its principal parts. -/
theorem exists_eq_ppSum (f : ℚ⟮X⟯) (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree) :
    ∃ c : ℚ → ℕ → ℚ, f = ppSum f.denom.roots.toFinset (fun h => f.denom.roots.count h) c := by
  obtain ⟨P, c, hf⟩ := exists_isPF f hsplit
  refine ⟨c, ?_⟩
  have hP : algebraMap ℚ[X] ℚ⟮X⟯ P =
      f + -(ppSum f.denom.roots.toFinset (fun h => f.denom.roots.count h) c) := by
    rw [eq_add_neg_iff_add_eq, ← hf]
  have hdeg : DegLE (-1) (algebraMap ℚ[X] ℚ⟮X⟯ P) := by
    rw [hP]; exact (DegLE.of_proper hproper).add (DegLE.ppSum _ _ _).neg
  rcases hdeg with h0 | h1
  · rw [h0, zero_add] at hf; exact hf
  · rw [RatFunc.intDegree_polynomial] at h1; omega

/-! ### Identification of the coefficients -/

theorem pfCoeff_ppSum (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) {h : ℚ} (hh : h ∈ R) {r : ℕ}
    (hr : 1 ≤ r) : pfCoeff (ppSum R b c) h r = if r ≤ b h then c h r else 0 := by
  unfold ppSum
  rw [pfCoeff_sum, Finset.sum_eq_single h]
  · rw [pfCoeff_sum]
    simp only [pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hr, true_and, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 (b h)) r (c h)]
    simp [Finset.mem_Icc, hr]
  · intro h' _ hne
    rw [pfCoeff_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [pfCoeff_C_mul, pfCoeff_inv_pow _ _ _ _ hr]
    simp only [show ¬(h' = h ∧ s = r) by tauto, ↓reduceIte, mul_zero]
  · intro hn; exact absurd hh hn

/-! ### The residue sum -/

theorem inv_sub_inv_X_eq (h : ℚ) :
    (RatFunc.X - RatFunc.C h)⁻¹ - RatFunc.X⁻¹ =
      RatFunc.C h * (RatFunc.X * (RatFunc.X - RatFunc.C h))⁻¹ := by
  have hu := X_sub_C_ne_zero' h
  have hX : (RatFunc.X : ℚ⟮X⟯) ≠ 0 := RatFunc.X_ne_zero
  field_simp
  ring

theorem DegLE.inv_X_sub_C_sub_inv_X (h c : ℚ) :
    DegLE (-2) (RatFunc.C c * ((RatFunc.X - RatFunc.C h) ^ 1)⁻¹ - RatFunc.C c * RatFunc.X⁻¹) := by
  rw [pow_one, ← mul_sub, inv_sub_inv_X_eq, ← mul_assoc, ← map_mul]
  refine DegLE.C_mul _ (Or.inr ?_)
  rw [RatFunc.intDegree_inv, RatFunc.intDegree_mul RatFunc.X_ne_zero (X_sub_C_ne_zero' h),
    RatFunc.intDegree_X, ← pow_one (RatFunc.X - RatFunc.C h), intDegree_X_sub_C_pow]
  norm_num

/-- If a sum of principal parts has degree `≤ -2`, the residues sum to zero. -/
theorem residue_sum_eq_zero (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ)
    (hdeg : DegLE (-2) (ppSum R b c)) : ∑ h ∈ R, (if 1 ≤ b h then c h 1 else 0) = 0 := by
  set s := ∑ h ∈ R, (if 1 ≤ b h then c h 1 else 0) with hs
  by_contra hs0
  have hsplit : ppSum R b c - RatFunc.C s * RatFunc.X⁻¹ =
      ∑ h ∈ R, (∑ r ∈ Finset.Icc 1 (b h), RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹ -
        RatFunc.C (if 1 ≤ b h then c h 1 else 0) * RatFunc.X⁻¹) := by
    rw [Finset.sum_sub_distrib, hs, map_sum, Finset.sum_mul]; rfl
  have h2 : DegLE (-2) (ppSum R b c - RatFunc.C s * RatFunc.X⁻¹) := by
    rw [hsplit]
    refine DegLE.sum _ _ fun h _ => ?_
    by_cases hb : 1 ≤ b h
    · simp only [hb, ↓reduceIte]
      rw [← Finset.insert_Icc_add_one_left_eq_Icc hb,
        Finset.sum_insert (by simp), add_sub_right_comm]
      refine (DegLE.inv_X_sub_C_sub_inv_X h (c h 1)).add (DegLE.sum _ _ fun r hr => ?_)
      exact (DegLE.basic h (c h r) r).mono (by have := (Finset.mem_Icc.mp hr).1; omega)
    · simp only [hb, ↓reduceIte]
      rw [Finset.Icc_eq_empty (by omega)]
      simp [DegLE]
  have h3 : DegLE (-2) (RatFunc.C s * RatFunc.X⁻¹) := by
    have := hdeg.add h2.neg
    rwa [show ppSum R b c + -(ppSum R b c - RatFunc.C s * RatFunc.X⁻¹) =
      RatFunc.C s * RatFunc.X⁻¹ by ring] at this
  rcases h3 with h0 | h1
  · exact hs0 (by
      have := mul_eq_zero.mp h0
      rcases this with h | h
      · exact (_root_.map_eq_zero_iff _ (RatFunc.C_injective)).mp h
      · exact absurd (inv_eq_zero.mp h) RatFunc.X_ne_zero)
  · rw [RatFunc.intDegree_mul ((_root_.map_ne_zero _).mpr hs0) (inv_ne_zero RatFunc.X_ne_zero),
      RatFunc.intDegree_C, RatFunc.intDegree_inv, RatFunc.intDegree_X] at h1
    omega

/-! ## Part 4. Real evaluation and formal = analytic -/

theorem polyPart_eq_zero_of_proper (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree) : polyPart f = 0 := by
  unfold polyPart
  rw [Polynomial.divByMonic_eq_zero_iff (RatFunc.monic_denom f)]
  exact Polynomial.degree_lt_degree hproper

/-! ### Real evaluation of principal parts -/

/-- `g` has no pole at the real point `x`. -/
def RegAt (x : ℝ) (g : ℚ⟮X⟯) : Prop := Polynomial.eval₂ (algebraMap ℚ ℝ) x g.denom ≠ 0

theorem RegAt.add {x : ℝ} {g₁ g₂ : ℚ⟮X⟯} (h₁ : RegAt x g₁) (h₂ : RegAt x g₂) :
    RegAt x (g₁ + g₂) := by
  intro h0
  have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ (RatFunc.denom_add_dvd g₁ g₂) h0
  rw [Polynomial.eval₂_mul] at this
  rcases mul_eq_zero.mp this with h | h
  · exact h₁ h
  · exact h₂ h

theorem RegAt.mul {x : ℝ} {g₁ g₂ : ℚ⟮X⟯} (h₁ : RegAt x g₁) (h₂ : RegAt x g₂) :
    RegAt x (g₁ * g₂) := by
  intro h0
  have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ (RatFunc.denom_mul_dvd g₁ g₂) h0
  rw [Polynomial.eval₂_mul] at this
  rcases mul_eq_zero.mp this with h | h
  · exact h₁ h
  · exact h₂ h

theorem RegAt.C (x : ℝ) (c : ℚ) : RegAt x (RatFunc.C c) := by
  rw [RegAt, RatFunc.denom_C]; simp

theorem RegAt.poly (x : ℝ) (P : ℚ[X]) : RegAt x (algebraMap ℚ[X] ℚ⟮X⟯ P) := by
  simp [RegAt, RatFunc.denom_algebraMap]

theorem X_sub_C_pow_eq_algebraMap (h : ℚ) (r : ℕ) :
    ((RatFunc.X - RatFunc.C h) ^ r : ℚ⟮X⟯) =
      algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ r) := by
  simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem eval_X_sub_C_pow (x : ℝ) (h : ℚ) (r : ℕ) :
    RatFunc.eval (algebraMap ℚ ℝ) x ((RatFunc.X - RatFunc.C h) ^ r) = (x - h) ^ r := by
  rw [X_sub_C_pow_eq_algebraMap, RatFunc.eval_algebraMap]
  simp

theorem RegAt.inv_pow {x : ℝ} {h : ℚ} (hx : x ≠ h) (r : ℕ) :
    RegAt x (((RatFunc.X - RatFunc.C h) ^ r)⁻¹) := by
  intro h0
  have heq : ((RatFunc.X - RatFunc.C h) ^ r : ℚ⟮X⟯)⁻¹ =
      algebraMap ℚ[X] ℚ⟮X⟯ 1 / algebraMap ℚ[X] ℚ⟮X⟯ ((Polynomial.X - Polynomial.C h) ^ r) := by
    rw [map_one, one_div, X_sub_C_pow_eq_algebraMap]
  rw [heq] at h0
  have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ (RatFunc.denom_div_dvd _ _) h0
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    eq_ratCast, pow_eq_zero_iff', sub_eq_zero] at this
  exact hx this.1

theorem eval_inv_pow {x : ℝ} {h : ℚ} (hx : x ≠ h) (r : ℕ) :
    RatFunc.eval (algebraMap ℚ ℝ) x (((RatFunc.X - RatFunc.C h) ^ r)⁻¹) = ((x - h) ^ r)⁻¹ := by
  have hmul := RatFunc.eval_mul _ _ (RegAt.inv_pow hx r)
    (show RegAt x ((RatFunc.X - RatFunc.C h) ^ r) by
      rw [X_sub_C_pow_eq_algebraMap]; exact RegAt.poly x _)
  rw [inv_mul_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero' h)), RatFunc.eval_one,
    eval_X_sub_C_pow] at hmul
  exact eq_inv_of_mul_eq_one_left hmul.symm

theorem regAt_eval_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ⟮X⟯) (x : ℝ)
    (hf : ∀ i ∈ s, RegAt x (f i)) :
    RegAt x (∑ i ∈ s, f i) ∧
      RatFunc.eval (algebraMap ℚ ℝ) x (∑ i ∈ s, f i) =
        ∑ i ∈ s, RatFunc.eval (algebraMap ℚ ℝ) x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [RegAt]
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha' := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨ha'.add h1, by rw [RatFunc.eval_add _ _ ha' h1, h2]⟩

theorem rfReal_ppSum (R : Finset ℚ) (b : ℚ → ℕ) (c : ℚ → ℕ → ℚ) (x : ℝ)
    (hx : ∀ h ∈ R, x ≠ h) :
    rfReal (ppSum R b c) x =
      ∑ h ∈ R, ∑ r ∈ Finset.Icc 1 (b h), (c h r : ℝ) * ((x - h) ^ r)⁻¹ := by
  have hterm : ∀ h ∈ R, ∀ r : ℕ,
      RegAt x (RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹) ∧
      RatFunc.eval (algebraMap ℚ ℝ) x (RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹) =
        (c h r : ℝ) * ((x - h) ^ r)⁻¹ := by
    intro h hh r
    refine ⟨(RegAt.C x _).mul (RegAt.inv_pow (hx h hh) r), ?_⟩
    rw [RatFunc.eval_mul _ _ (RegAt.C x _) (RegAt.inv_pow (hx h hh) r), RatFunc.eval_C,
      eval_inv_pow (hx h hh)]
    simp
  have hinner : ∀ h ∈ R,
      RegAt x (∑ r ∈ Finset.Icc 1 (b h), RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹) ∧
      RatFunc.eval (algebraMap ℚ ℝ) x
        (∑ r ∈ Finset.Icc 1 (b h), RatFunc.C (c h r) * ((RatFunc.X - RatFunc.C h) ^ r)⁻¹) =
        ∑ r ∈ Finset.Icc 1 (b h), (c h r : ℝ) * ((x - h) ^ r)⁻¹ := by
    intro h hh
    obtain ⟨h1, h2⟩ := regAt_eval_sum _ _ x fun r _ => (hterm h hh r).1
    exact ⟨h1, by rw [h2]; exact Finset.sum_congr rfl fun r _ => (hterm h hh r).2⟩
  obtain ⟨-, h2⟩ := regAt_eval_sum _ _ x fun h hh => (hinner h hh).1
  unfold rfReal ppSum
  rw [h2]
  exact Finset.sum_congr rfl fun h hh => (hinner h hh).2

/-! ### Derivatives -/

theorem hasDerivAt_inv_pow_sub (h : ℝ) (r : ℕ) (x : ℝ) (hx : x ≠ h) :
    HasDerivAt (fun y => ((y - h) ^ r)⁻¹) (-(r : ℝ) * ((x - h) ^ (r + 1))⁻¹) x := by
  have hne : x - h ≠ 0 := sub_ne_zero.mpr hx
  have h1 : HasDerivAt (fun y => (y - h) ^ r) ((r : ℝ) * (x - h) ^ (r - 1)) x := by
    have := (hasDerivAt_pow r (x - h)).comp x ((hasDerivAt_id' x).sub_const h)
    simpa [Function.comp_def] using this
  have h2 := h1.inv (pow_ne_zero r hne)
  convert h2 using 1
  rcases r with _ | r
  · simp
  · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    field_simp
    ring

/-! ### Tail sums of `ζ` -/

theorem sum_range_succ_eq_sum_Icc (g : ℕ → ℝ) (hg : g 0 = 0) (d : ℕ) :
    ∑ i ∈ Finset.range (d + 1), g i = ∑ i ∈ Finset.Icc 1 d, g i := by
  induction d with
  | zero => simp [hg]
  | succ d ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem zeta_re_eq_tsum (s : ℕ) (hs : 2 ≤ s) :
    (riemannZeta s).re = ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
  have : (fun n : ℕ => 1 / (n : ℂ) ^ s) = fun n : ℕ => ((((n : ℝ) ^ s)⁻¹ : ℝ) : ℂ) := by
    funext n; push_cast; rw [one_div]
  rw [this, ← Complex.ofReal_tsum, Complex.ofReal_re]

theorem summable_inv_nat_pow (s : ℕ) (hs : 2 ≤ s) : Summable fun n : ℕ => ((n : ℝ) ^ s)⁻¹ := by
  simpa [one_div] using Real.summable_one_div_nat_pow.mpr (by omega : 1 < s)

theorem tsum_inv_pow_shift (d s : ℕ) (hs : 2 ≤ s) :
    ∑' n : ℕ, (((d : ℝ) + 1 + n) ^ s)⁻¹ =
      (riemannZeta s).re - ∑ i ∈ Finset.Icc 1 d, ((i : ℝ) ^ s)⁻¹ := by
  rw [zeta_re_eq_tsum s hs, ← (summable_inv_nat_pow s hs).sum_add_tsum_nat_add (d + 1),
    sum_range_succ_eq_sum_Icc _ (by simp; omega)]
  have : (fun n : ℕ => (((n + (d + 1) : ℕ) : ℝ) ^ s)⁻¹) = fun n : ℕ => (((d : ℝ) + 1 + n) ^ s)⁻¹ := by
    funext n; push_cast; ring_nf
  rw [this]; ring

theorem toNat_cast_real (K m : ℤ) (hm : m ≤ K) : (((K - m).toNat : ℕ) : ℝ) = (K : ℝ) - m := by
  have : (((K - m).toNat : ℤ) : ℝ) = ((K - m : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
  push_cast at this
  exact this

theorem summable_pole (K : ℤ) (h : ℚ) (hh : ∃ n : ℤ, n ≤ K ∧ h = n) (s : ℕ) (hs : 2 ≤ s) :
    Summable fun n : ℕ => (((K : ℝ) + 1 + n - h) ^ s)⁻¹ := by
  obtain ⟨m, hm, rfl⟩ := hh
  have := (summable_nat_add_iff ((K - m).toNat + 1)).mpr (summable_inv_nat_pow s hs)
  convert this using 2 with n
  push_cast
  rw [toNat_cast_real K m hm]
  ring

theorem tsum_pole (K : ℤ) (h : ℚ) (hh : ∃ n : ℤ, n ≤ K ∧ h = n) (s : ℕ) (hs : 2 ≤ s) :
    ∑' n : ℕ, (((K : ℝ) + 1 + n - h) ^ s)⁻¹ =
      (riemannZeta s).re - (harm s ⌊(K : ℚ) - h⌋ : ℝ) := by
  obtain ⟨m, hm, rfl⟩ := hh
  have : (fun n : ℕ => (((K : ℝ) + 1 + n - ((m : ℚ) : ℝ)) ^ s)⁻¹) =
      fun n : ℕ => (((((K - m).toNat : ℕ) : ℝ) + 1 + n) ^ s)⁻¹ := by
    funext n; rw [toNat_cast_real K m hm]; push_cast; ring_nf
  rw [this, tsum_inv_pow_shift _ s hs]
  congr 1
  rw [show ((K : ℚ) - (m : ℚ)) = ((K - m : ℤ) : ℚ) by push_cast; ring, Int.floor_intCast]
  unfold harm
  push_cast
  simp [one_div]

/-! ### Linearity of the realisation -/

/-- The weight of `Z_r` under the realisation. -/
def zetaWeight (r : ℕ) : ℝ := if r = 0 then 1 else (riemannZeta r).re

/-- `realize` as an additive map. -/
def realizeHom : FormalZ →+ ℝ :=
  Finsupp.liftAddHom fun r =>
    (AddMonoidHom.mulRight (zetaWeight r)).comp (Rat.castHom ℝ).toAddMonoidHom

theorem realize_eq_realizeHom (z : FormalZ) : realize z = realizeHom z := by
  unfold realize realizeHom
  rw [Finsupp.liftAddHom_apply]
  rfl

theorem realize_smul (q : ℚ) (z : FormalZ) : realize (q • z) = q * realize z := by
  rw [realize_eq_realizeHom, realize_eq_realizeHom, map_rat_smul, Rat.smul_def]

theorem realize_Zsym (r : ℕ) : realize (Zsym r) = zetaWeight r := by
  simp [realize, Zsym, zetaWeight]

theorem realize_Lfun_of_polyPart_eq_zero (K : ℤ) (f : ℚ⟮X⟯) (h0 : polyPart f = 0) :
    realize (Lfun K f) =
      ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.range (f.denom.natDegree + 1),
        (r : ℝ) * (pfCoeff f h r : ℝ) *
          ((riemannZeta ((r + 1 : ℕ) : ℂ)).re - (harm (r + 1) ⌊(K : ℚ) - h⌋ : ℝ)) := by
  unfold Lfun
  rw [h0]
  simp only [Polynomial.natDegree_zero, zero_add, Finset.range_one, Finset.sum_singleton,
    Polynomial.coeff_zero, zero_mul, zero_smul]
  rw [realize_eq_realizeHom, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← realize_eq_realizeHom, realize_smul, realize_eq_realizeHom, map_sub,
    ← realize_eq_realizeHom, ← realize_eq_realizeHom, realize_smul, realize_Zsym, realize_Zsym]
  simp [zetaWeight]

/-! ### Formal = analytic -/

/-- **Formal = analytic** (corrected form of `derivSum_eq_realize_Lfun`: the denominator must
split over `ℚ`). -/
theorem derivSum_eq_realize_Lfun' (K : ℤ) (f : ℚ⟮X⟯)
    (hproper : f.num.natDegree < f.denom.natDegree)
    (hsplit : f.denom.roots.card = f.denom.natDegree)
    (hpoles : ∀ h ∈ f.denom.roots, ∃ n : ℤ, n ≤ K ∧ h = n) :
    derivSum K f = realize (Lfun K f) := by
  obtain ⟨c, hc⟩ := exists_eq_ppSum f hproper hsplit
  rw [realize_Lfun_of_polyPart_eq_zero K f (polyPart_eq_zero_of_proper f hproper)]
  set R := f.denom.roots.toFinset with hR
  set b : ℚ → ℕ := fun h => f.denom.roots.count h with hb
  have hpR : ∀ h ∈ R, ∃ n : ℤ, n ≤ K ∧ h = n := fun h hh =>
    hpoles h (Multiset.mem_toFinset.mp hh)
  have hpf : ∀ h ∈ R, ∀ r, 1 ≤ r → pfCoeff f h r = if r ≤ b h then c h r else 0 := by
    intro h hh r hr
    have := pfCoeff_ppSum R b c hh hr
    rwa [← hc] at this
  have hbD : ∀ h, b h ≤ f.denom.natDegree := fun h =>
    (Multiset.count_le_card h _).trans hsplit.le
  -- the derivative beyond the poles
  have hderiv : ∀ x : ℝ, (K : ℝ) < x → deriv (rfReal f) x =
      ∑ h ∈ R, ∑ r ∈ Finset.Icc 1 (b h), (c h r : ℝ) * (-(r : ℝ) * ((x - h) ^ (r + 1))⁻¹) := by
    intro x hx
    have hxR : ∀ y : ℝ, (K : ℝ) < y → ∀ h ∈ R, y ≠ h := by
      intro y hy h hh
      obtain ⟨n, hn, rfl⟩ := hpR h hh
      have : ((n : ℚ) : ℝ) ≤ K := by push_cast; exact_mod_cast hn
      exact ne_of_gt (lt_of_le_of_lt this hy)
    have heq : rfReal f =ᶠ[𝓝 x] fun y =>
        ∑ h ∈ R, ∑ r ∈ Finset.Icc 1 (b h), (c h r : ℝ) * ((y - h) ^ r)⁻¹ := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [hc]
      exact rfReal_ppSum R b c y (hxR y hy)
    rw [heq.deriv_eq]
    refine (HasDerivAt.fun_sum (u := R)
      (A := fun (h : ℚ) (y : ℝ) => ∑ r ∈ Finset.Icc 1 (b h), (c h r : ℝ) * ((y - (h : ℝ)) ^ r)⁻¹)
      fun h hh => HasDerivAt.fun_sum (u := Finset.Icc 1 (b h))
        (A := fun (r : ℕ) (y : ℝ) => (c h r : ℝ) * ((y - (h : ℝ)) ^ r)⁻¹) fun r _ => ?_).deriv
    exact (hasDerivAt_inv_pow_sub _ r x (hxR x hx h hh)).const_mul _
  have e1 : (fun n : ℕ => deriv (rfReal f) ((K : ℝ) + 1 + n)) = fun n : ℕ =>
      -∑ h ∈ R, ∑ r ∈ Finset.Icc 1 (b h), ((r : ℝ) * (c h r : ℝ)) *
        (((K : ℝ) + 1 + n - h) ^ (r + 1))⁻¹ := by
    funext n
    rw [hderiv _ (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have hsum : ∀ h ∈ R, ∀ r ∈ Finset.Icc 1 (b h), Summable fun n : ℕ =>
      ((r : ℝ) * (c h r : ℝ)) * (((K : ℝ) + 1 + n - h) ^ (r + 1))⁻¹ := fun h hh r hr =>
    (summable_pole K h (hpR h hh) (r + 1) (by have := (Finset.mem_Icc.mp hr).1; omega)).mul_left _
  rw [derivSum, e1, tsum_neg, neg_neg,
    Summable.tsum_finsetSum fun h hh => summable_sum fun r hr => hsum h hh r hr]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Summable.tsum_finsetSum fun r hr => hsum h hh r hr]
  -- compare the two finite sums over `r`
  apply Finset.sum_subset_zero_on_sdiff
  · intro r hr
    have := Finset.mem_Icc.mp hr
    exact Finset.mem_range.mpr (by have := hbD h; omega)
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_sdiff.mp hr
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · simp
    · have hgt : ¬ r ≤ b h := fun hle => hr2 (Finset.mem_Icc.mpr ⟨hpos, hle⟩)
      rw [hpf h hh r hpos]
      simp [hgt]
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    rw [hpf h hh r hr1, tsum_mul_left, tsum_pole K h (hpR h hh) (r + 1) (by omega)]
    simp [hr2]

/-! ## Part 5. The kernel -/

/-! ### The kernel `(-t)^j R_N(t)` -/

/-- `(t + c)_r = ∏_{i < r} (t - (-(c + i)))`. -/
theorem poch_eq_prod (c : ℚ) (r : ℕ) :
    poch c r = (((Multiset.range r).map fun i : ℕ => -(c + i)).map
      fun a => Polynomial.X - Polynomial.C a).prod := by
  induction r with
  | zero => simp [poch]
  | succ r ih =>
    rw [poch, ascPochhammer_succ_right, Polynomial.mul_comp, ← poch, ih, Multiset.range_succ,
      Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, mul_comm]
    congr 1
    simp only [Polynomial.add_comp, Polynomial.X_comp, map_neg, map_add,
      sub_neg_eq_add, ← Polynomial.C_eq_natCast, Polynomial.C_comp]
    ring

/-- The poles of `R_N`, with multiplicity. -/
def poleSet (N : ℕ) : Multiset ℚ :=
  (Multiset.range (10 * N + 2)).map (fun i : ℕ => -((0 : ℚ) + i)) +
    (Multiset.range (10 * N + 1)).map (fun i : ℕ => -((N : ℚ) + i)) +
    (Multiset.range (10 * N + 1)).map (fun i : ℕ => -((2 * N : ℚ) + i))

/-- The zeros of `R_N`, with multiplicity. -/
def zeroSet (N : ℕ) : Multiset ℚ :=
  (Multiset.range (15 * N)).map (fun i : ℕ => -((-17 * N : ℚ) + i)) +
    (Multiset.range (15 * N)).map (fun i : ℕ => -((-16 * N : ℚ) + i))

theorem den_eq (N : ℕ) :
    poch 0 (10 * N + 2) * poch N (10 * N + 1) * poch (2 * N) (10 * N + 1) =
      ((poleSet N).map fun a => Polynomial.X - Polynomial.C a).prod := by
  rw [poleSet, Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add,
    poch_eq_prod, poch_eq_prod, poch_eq_prod]

theorem num_eq (N : ℕ) :
    poch (-17 * N) (15 * N) * poch (-16 * N) (15 * N) =
      ((zeroSet N).map fun a => Polynomial.X - Polynomial.C a).prod := by
  rw [zeroSet, Multiset.map_add, Multiset.prod_add, poch_eq_prod, poch_eq_prod]

/-- `(-t)^j R_N(t)` as a quotient of two explicit polynomials. -/
theorem linFormKernel_eq (N : ℕ) (j : Fin 3) :
    linFormKernel N j =
      algebraMap ℚ[X] ℚ⟮X⟯ ((-Polynomial.X) ^ (j : ℕ) *
          ((zeroSet N).map fun a => Polynomial.X - Polynomial.C a).prod) /
        algebraMap ℚ[X] ℚ⟮X⟯ (((poleSet N).map fun a => Polynomial.X - Polynomial.C a).prod) := by
  rw [linFormKernel, Rker, num_eq, den_eq, map_mul, map_pow, map_neg, RatFunc.algebraMap_X,
    mul_div_assoc]

theorem prod_X_sub_C_ne_zero (S : Multiset ℚ) :
    ((S.map fun a => Polynomial.X - Polynomial.C a).prod) ≠ 0 :=
  (Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a).ne_zero

theorem natDegree_prod_X_sub_C (S : Multiset ℚ) :
    ((S.map fun a => Polynomial.X - Polynomial.C a).prod).natDegree = Multiset.card S :=
  Polynomial.natDegree_multiset_prod_X_sub_C_eq_card S

theorem denom_linFormKernel_dvd (N : ℕ) (j : Fin 3) :
    (linFormKernel N j).denom ∣ ((poleSet N).map fun a => Polynomial.X - Polynomial.C a).prod := by
  rw [linFormKernel_eq]; exact RatFunc.denom_div_dvd _ _

theorem roots_denom_le (N : ℕ) (j : Fin 3) : (linFormKernel N j).denom.roots ≤ poleSet N := by
  have := Polynomial.roots.le_of_dvd (prod_X_sub_C_ne_zero _) (denom_linFormKernel_dvd N j)
  rwa [Polynomial.roots_multiset_prod_X_sub_C] at this

theorem linFormKernel_split (N : ℕ) (j : Fin 3) :
    (linFormKernel N j).denom.roots.card = (linFormKernel N j).denom.natDegree := by
  have hsplit : Polynomial.Splits
      (((poleSet N).map fun a => Polynomial.X - Polynomial.C a).prod) :=
    Polynomial.Splits.multisetProd fun f hf => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hf
      exact Polynomial.Splits.X_sub_C a
  exact Polynomial.splits_iff_card_roots.mp
    (hsplit.of_dvd (prod_X_sub_C_ne_zero _) (denom_linFormKernel_dvd N j))

theorem linFormKernel_poles (N : ℕ) (j : Fin 3) :
    ∀ h ∈ (linFormKernel N j).denom.roots, ∃ n : ℤ, n ≤ 2 * N ∧ h = n := by
  intro h hh
  have hmem := Multiset.mem_of_le (roots_denom_le N j) hh
  simp only [poleSet, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range] at hmem
  rcases hmem with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩
  · exact ⟨-(i : ℤ), by omega, by push_cast; ring⟩
  · exact ⟨-((N : ℤ) + i), by omega, by push_cast; ring⟩
  · exact ⟨-(2 * (N : ℤ) + i), by omega, by push_cast; ring⟩

theorem count_map_range_le_one (c : ℚ) (r : ℕ) (h : ℚ) :
    ((Multiset.range r).map fun i : ℕ => -(c + i)).count h ≤ 1 := by
  refine Multiset.nodup_iff_count_le_one.mp ?_ h
  refine (Multiset.nodup_range r).map fun a b hab => ?_
  have : ((a : ℕ) : ℚ) = b := by linarith
  exact_mod_cast this

theorem count_roots_le_three (N : ℕ) (j : Fin 3) (h : ℚ) :
    (linFormKernel N j).denom.roots.count h ≤ 3 := by
  refine (Multiset.count_le_of_le h (roots_denom_le N j)).trans ?_
  rw [poleSet, Multiset.count_add, Multiset.count_add]
  have h1 := count_map_range_le_one 0 (10 * N + 2) h
  have h2 := count_map_range_le_one N (10 * N + 1) h
  have h3 := count_map_range_le_one (2 * N) (10 * N + 1) h
  omega

theorem intDegree_linFormKernel (N : ℕ) (j : Fin 3) :
    (linFormKernel N j).intDegree = (j : ℤ) - 4 := by
  have hX : ((-Polynomial.X : ℚ[X]) ^ (j : ℕ)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr Polynomial.X_ne_zero)
  have hP : (-Polynomial.X : ℚ[X]) ^ (j : ℕ) *
      ((zeroSet N).map fun a => Polynomial.X - Polynomial.C a).prod ≠ 0 :=
    mul_ne_zero hX (prod_X_sub_C_ne_zero _)
  have hinj := IsFractionRing.injective ℚ[X] ℚ⟮X⟯
  rw [linFormKernel_eq, RatFunc.intDegree_div ((map_ne_zero_iff _ hinj).mpr hP)
      ((map_ne_zero_iff _ hinj).mpr (prod_X_sub_C_ne_zero _)),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
    Polynomial.natDegree_mul hX (prod_X_sub_C_ne_zero _), natDegree_prod_X_sub_C,
    natDegree_prod_X_sub_C, Polynomial.natDegree_pow, Polynomial.natDegree_neg,
    Polynomial.natDegree_X]
  simp [zeroSet, poleSet]
  omega

theorem linFormKernel_proper (N : ℕ) (j : Fin 3) :
    (linFormKernel N j).num.natDegree < (linFormKernel N j).denom.natDegree := by
  have := intDegree_linFormKernel N j
  unfold RatFunc.intDegree at this
  have hj := j.isLt
  omega

/-- The Laurent coefficients of the kernel: orders `≤ 3` and residues summing to zero. -/
theorem linFormKernel_pfCoeff (N : ℕ) (j : Fin 3) :
    (∀ h ∈ (linFormKernel N j).denom.roots.toFinset, ∀ s, 4 ≤ s →
      pfCoeff (linFormKernel N j) h s = 0) ∧
    ∑ h ∈ (linFormKernel N j).denom.roots.toFinset, pfCoeff (linFormKernel N j) h 1 = 0 := by
  obtain ⟨c, hc⟩ := exists_eq_ppSum _ (linFormKernel_proper N j) (linFormKernel_split N j)
  set f := linFormKernel N j with hf
  set R := f.denom.roots.toFinset
  set b : ℚ → ℕ := fun h => f.denom.roots.count h
  have hpf : ∀ h ∈ R, ∀ r, 1 ≤ r → pfCoeff f h r = if r ≤ b h then c h r else 0 := by
    intro h hh r hr
    have := pfCoeff_ppSum R b c hh hr
    rwa [← hc] at this
  refine ⟨fun h hh s hs => ?_, ?_⟩
  · rw [hpf h hh s (by omega)]
    have := count_roots_le_three N j h
    rw [← hf] at this
    have : ¬ s ≤ b h := by simp only [b]; omega
    simp [this]
  · have hdeg : DegLE (-2) (ppSum R b c) := by
      rw [← hc]; right; rw [hf, intDegree_linFormKernel]; have := j.isLt; omega
    have := residue_sum_eq_zero R b c hdeg
    rw [← this]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [hpf h hh 1 le_rfl]

/-- The coefficients of `𝓛_K[f]` away from `Z₀` (for `f` without polynomial part). -/
theorem Lfun_apply_of_ne_zero (K : ℤ) (f : ℚ⟮X⟯) (hpoly : polyPart f = 0) (r : ℕ) (hr : r ≠ 0) :
    Lfun K f r = ∑ h ∈ f.denom.roots.toFinset, ∑ s ∈ Finset.range (f.denom.natDegree + 1),
      (s : ℚ) * pfCoeff f h s * (if s + 1 = r then 1 else 0) := by
  unfold Lfun
  rw [hpoly]
  simp [Zsym, Finsupp.single_apply, hr, Finset.sum_apply]

theorem Lfun_linFormKernel_support (N : ℕ) (j : Fin 3) (r : ℕ) (h0 : r ≠ 0) (h3 : r ≠ 3)
    (h4 : r ≠ 4) : Lfun (2 * N) (linFormKernel N j) r = 0 := by
  obtain ⟨hord, hres⟩ := linFormKernel_pfCoeff N j
  rw [Lfun_apply_of_ne_zero _ _ (polyPart_eq_zero_of_proper _ (linFormKernel_proper N j)) r h0]
  by_cases h2 : r = 2
  · subst h2
    refine (Finset.sum_congr rfl fun h hh => ?_).trans hres
    have hD : 1 ≤ (linFormKernel N j).denom.natDegree := by
      have := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hh)
      have := Multiset.count_le_card h (linFormKernel N j).denom.roots
      rw [linFormKernel_split] at this
      omega
    rw [Finset.sum_eq_single 1]
    · simp
    · intro s _ hs; simp only [show ¬ (s + 1 = 2) by omega, ↓reduceIte, mul_zero]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  · refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : s + 1 = r
    · rcases Nat.eq_zero_or_pos s with rfl | hpos
      · simp
      · rw [hord h hh s (by omega)]; simp
    · simp [hs]

/-! ## Part 6. `S_eq` -/

/-- Realisation of a combination of `1, Z₃, Z₄`. -/
theorem realize_eq_of_support (z : FormalZ)
    (hz : ∀ r, r ≠ 0 → r ≠ 3 → r ≠ 4 → z r = 0) :
    realize z = z 4 * ζ4 + z 3 * ζ3 + z 0 := by
  have hsupp : z.support ⊆ {0, 3, 4} := by
    intro r hr
    rw [Finsupp.mem_support_iff] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    exact hr (hz r h.1 h.2.1 h.2.2)
  unfold realize
  rw [Finsupp.sum_of_support_subset z hsupp _ (by intros; simp)]
  simp [ζ3, ζ4]
  ring

/-- **[1] Partial-fraction evaluation**: `S_{Nj} = A_{Nj} ζ(4) + B_{Nj} ζ(3) + C_{Nj}`. -/
theorem S_eq (N : ℕ) (j : Fin 3) :
    S N j = coeffMat N 0 j * ζ4 + coeffMat N 1 j * ζ3 + coeffMat N 2 j := by
  rw [S, derivSum_eq_realize_Lfun' _ _ (linFormKernel_proper N j) (linFormKernel_split N j)
    (linFormKernel_poles N j), realize_eq_of_support _ (Lfun_linFormKernel_support N j)]
  simp [coeffMat]

/-! ## Part 7. The readouts as cross products -/

theorem det_coeffMat_eq (N : ℕ) : (coeffMat N).det = -6 * (-1) ^ N * (V N).det := by
  have hC0 : C0.det = -6 := by rw [Matrix.det_fin_three]; simp [C0]; norm_num
  rw [V, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hC0,
    Fintype.card_fin]
  have : ((-1 : ℚ) ^ N) ^ 3 * (-1) ^ N = 1 := by
    rw [← pow_mul, ← pow_add, show N * 3 + N = 2 * (2 * N) by ring, pow_mul]; norm_num
  linear_combination (-(coeffMat N).det) * this

theorem U34_mul_C0_transpose : U34 * C0ᵀ = !![0, 6, 0; 6, 0, 0; 0, 0, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U34, C0, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem inv_transpose_eq_cross (M : Matrix (Fin 3) (Fin 3) ℚ) (_hM : M.det ≠ 0) :
    M⁻¹ᵀ = (M.det)⁻¹ • Matrix.of ![crossProduct (M 1) (M 2), crossProduct (M 2) (M 0),
      crossProduct (M 0) (M 1)] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cross_apply] <;> first | ring1 | (ring_nf; simp)

theorem readouts_eq_cross_rat (N : ℕ) (i j : Fin 3) :
    Rmat N i j = -((V N).det)⁻¹ * ![crossProduct (coeffMat N 2) (coeffMat N 0),
      crossProduct (coeffMat N 1) (coeffMat N 2), crossProduct (coeffMat N 0) (coeffMat N 1)] i j := by
  set Cm := coeffMat N with hCm
  set s : ℚ := (-1) ^ N with hs_def
  have hs : s * s = 1 := by
    rw [hs_def, ← pow_add, show N + N = 2 * N by ring, pow_mul]; norm_num
  have hs0 : s ≠ 0 := by rw [hs_def]; exact pow_ne_zero _ (by norm_num)
  by_cases hd : (V N).det = 0
  · have hV : (V N)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hd]; simp)
    simp [Rmat, T, hV, hd]
  · have hC : Cm.det ≠ 0 := by
      rw [hCm, det_coeffMat_eq]; exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) hd
    have hC0 : IsUnit C0.det := by rw [Matrix.det_fin_three]; simp [C0]
    have hVinv : (V N)⁻¹ = s • (Cm⁻¹ * C0) := by
      apply Matrix.inv_eq_right_inv
      rw [V, ← hs_def, ← hCm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul,
        Matrix.mul_assoc, ← Matrix.mul_assoc Cm, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC),
        Matrix.one_mul, Matrix.nonsing_inv_mul _ hC0]
    have hR : Rmat N = s • (!![0, 6, 0; 6, 0, 0; 0, 0, 6] * ((Cm.det)⁻¹ • Matrix.of
        ![crossProduct (Cm 1) (Cm 2), crossProduct (Cm 2) (Cm 0), crossProduct (Cm 0) (Cm 1)])) := by
      rw [Rmat, T, hVinv, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_smul,
        ← Matrix.mul_assoc, U34_mul_C0_transpose, inv_transpose_eq_cross _ hC]
    have hdet : Cm.det = -6 * s * (V N).det := by rw [hCm, det_coeffMat_eq]
    rw [hR]
    fin_cases i <;>
    · simp [hdet]
      field_simp

/-- **[5] The readouts as cross products.** With `A, B, C` the rows of `𝓒_N` (cast to `ℝ`):
`q_N = -(A×B)/det V_N`, `p^{(3)}_N = -(C×A)/det V_N`, `p^{(4)}_N = -(B×C)/det V_N`. -/
theorem readouts_eq_cross (N : ℕ) :
    let A : Fin 3 → ℝ := fun j => (coeffMat N 0 j : ℝ)
    let B : Fin 3 → ℝ := fun j => (coeffMat N 1 j : ℝ)
    let C : Fin 3 → ℝ := fun j => (coeffMat N 2 j : ℝ)
    (fun j => (q N j : ℝ)) = -((V N).det : ℝ)⁻¹ • crossProduct A B ∧
    (fun j => (p3 N j : ℝ)) = -((V N).det : ℝ)⁻¹ • crossProduct C A ∧
    (fun j => (p4 N j : ℝ)) = -((V N).det : ℝ)⁻¹ • crossProduct B C := by
  intro A B C
  have key := readouts_eq_cross_rat N
  refine ⟨funext fun j => ?_, funext fun j => ?_, funext fun j => ?_⟩ <;>
  · simp only [Pi.smul_apply, smul_eq_mul, q, p3, p4, key]
    fin_cases j <;> simp [A, B, C, cross_apply]

/-- **Main theorem (`blueprint.lean`, `cross_product_readout`).** -/
theorem cross_product_readout (N : ℕ) :
    (fun j => ζ3 * q N j - p3 N j) =
        -((V N).det : ℝ)⁻¹ • crossProduct (fun j => (coeffMat N 0 j : ℝ)) (S N) ∧
    (fun j => ζ4 * q N j - p4 N j) =
        ((V N).det : ℝ)⁻¹ • crossProduct (fun j => (coeffMat N 1 j : ℝ)) (S N) := by
  obtain ⟨hq, hp3, hp4⟩ := readouts_eq_cross N
  have hS : S N = fun j => (coeffMat N 0 j : ℝ) * ζ4 + coeffMat N 1 j * ζ3 + coeffMat N 2 j :=
    funext (S_eq N)
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · have e1 := congrFun hq j
    have e2 := congrFun hp3 j
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2, hS]
    fin_cases j <;> simp [cross_apply] <;> ring
  · have e1 := congrFun hq j
    have e2 := congrFun hp4 j
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2, hS]
    fin_cases j <;> simp [cross_apply] <;> ring

end ZetasIrr
