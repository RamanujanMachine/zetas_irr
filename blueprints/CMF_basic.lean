/-
# CMF transport, part 1: kernels from integer parameters and the two functionals

This file is the foundation of the formalization of the conservative matrix field
MeijerG(5,2,5,5,1) used by the note. It is imported by `CMF_transport.lean`,
`CMF_pairing.lean` and `CMF_path.lean`, which in turn supply the open nodes
`exists_transport_blocks` (`det_V_eq.lean`), `dual_transport` (`pairing_identity.lean`) and
`dual_first_identity` (`valuation_bound.lean`).

Contents.
* `ival lo n = {lo, …, lo+n-1}` (integer intervals as multisets), `lp S = ∏_{z ∈ S} (X - z)`,
  `lin Z P = lp Z / lp P` (rational functions with integer zeros `Z` and poles `P`).
* `pairKer b a = Γ(X+b)/Γ(X+a)` for integers `a, b`, i.e. `(X+a)_{b-a}` or `1/(X+b)_{a-b}`;
  the kernel `ker a b = ∏_j Γ(X + b_j)/∏_i Γ(X + a_i)` of a parameter point `(a, b)` of the
  CMF, with the fixed pairing `(b₀,a₄), (b₁,a₀), (b₂,a₁), (b₃,a₂), (b₄,a₃)`.
* The one-step relations `pairKer b (a-1) = (X + a - 1) pairKer b a`,
  `pairKer (b+1) a = (X + b) pairKer b a` (the axis transformations `Γ(t+1) = tΓ(t)`), and the
  functional equation `r(t-1) ∏_j (t - 1 + b_j) = r(t) ∏_i (t - 1 + a_i)`.
* The interface `IsMom Φ ord` for a functional `Φ_K` (linearity, the boundary identity
  `Φ_K[g(t) - g(t-1)] = 0` when `g` has a zero of order `≥ ord` at `K`, and the cutoff move
  `Φ_{K+1}[f] = Φ_K[f]` when `f` has a zero of order `≥ ord` at `K+1`), with the instances
  `IsMom Lfun 2` (first functional) and `IsMom Mfun 3` (second-derivative functional), both
  derived from `Lfun_sub_Lfun_pred` of `Mfun_sub_Mfun_pred.lean`.
-/
import Mfun_sub_Mfun_pred

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr.CMF

/-! ### Integer intervals -/

/-- `{lo, lo+1, …, lo+n-1}`. -/
def ival (lo : ℤ) (n : ℕ) : Multiset ℤ := (Multiset.range n).map fun i : ℕ => lo + (i : ℤ)

theorem ival_zero (lo : ℤ) : ival lo 0 = 0 := by simp [ival]

theorem ival_succ (lo : ℤ) (n : ℕ) : ival lo (n + 1) = (lo + n) ::ₘ ival lo n := by
  simp [ival, Multiset.range_succ]

theorem ival_succ' (lo : ℤ) (n : ℕ) : ival lo (n + 1) = lo ::ₘ ival (lo + 1) n := by
  induction n generalizing lo with
  | zero => simp [ival_succ, ival_zero]
  | succ n ih =>
    rw [ival_succ, ih, ival_succ, Multiset.cons_swap]
    congr 2
    push_cast; ring

theorem mem_ival (lo : ℤ) (n : ℕ) (k : ℤ) : k ∈ ival lo n ↔ lo ≤ k ∧ k < lo + n := by
  simp only [ival, Multiset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := Multiset.mem_range.mp hi
    omega
  · intro h
    refine ⟨(k - lo).toNat, Multiset.mem_range.mpr ?_, ?_⟩ <;> omega

theorem count_ival (lo : ℤ) (n : ℕ) (k : ℤ) :
    (ival lo n).count k = if lo ≤ k ∧ k < lo + n then 1 else 0 := by
  induction n with
  | zero => simp [ival_zero]
  | succ n ih =>
    rw [ival_succ, Multiset.count_cons, ih]
    push_cast
    split_ifs <;> omega

theorem ival_map_add (lo : ℤ) (n : ℕ) (c : ℤ) : (ival lo n).map (· + c) = ival (lo + c) n := by
  simp only [ival, Multiset.map_map, Function.comp_def]
  congr 1; funext i; ring

theorem ival_nonneg_bound (lo : ℤ) (n : ℕ) (k : ℤ) (hk : k ∈ ival lo n) : lo ≤ k ∧ k < lo + n :=
  (mem_ival lo n k).mp hk

/-! ### Products of linear factors -/

/-- `∏_{z ∈ S} (X - z)`. -/
def lp (S : Multiset ℤ) : ℚ[X] := (S.map fun z : ℤ => X - C (z : ℚ)).prod

theorem lp_zero : lp 0 = 1 := by simp [lp]

theorem lp_cons (z : ℤ) (S : Multiset ℤ) : lp (z ::ₘ S) = (X - C (z : ℚ)) * lp S := by
  simp [lp]

theorem lp_add (S T : Multiset ℤ) : lp (S + T) = lp S * lp T := by
  simp [lp, Multiset.prod_add]

theorem lp_replicate (n : ℕ) (z : ℤ) : lp (Multiset.replicate n z) = (X - C (z : ℚ)) ^ n := by
  simp [lp, Multiset.map_replicate, Multiset.prod_replicate]

theorem lp_monic (S : Multiset ℤ) : (lp S).Monic :=
  Polynomial.monic_multiset_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem lp_ne_zero (S : Multiset ℤ) : lp S ≠ 0 := (lp_monic S).ne_zero

theorem lp_eq_map (S : Multiset ℤ) :
    lp S = ((S.map (Int.cast : ℤ → ℚ)).map fun a => X - C a).prod := by
  rw [lp, Multiset.map_map]; rfl

theorem lp_roots (S : Multiset ℤ) : (lp S).roots = S.map (Int.cast : ℤ → ℚ) := by
  rw [lp_eq_map]; exact Polynomial.roots_multiset_prod_X_sub_C _

theorem lp_splits (S : Multiset ℤ) : Polynomial.Splits (lp S) :=
  Polynomial.Splits.multisetProd fun f hf => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Polynomial.Splits.X_sub_C _

theorem lp_eval (S : Multiset ℤ) (x : ℚ) :
    (lp S).eval x = (S.map fun z : ℤ => x - (z : ℚ)).prod := by
  simp [lp, Polynomial.eval_multiset_prod, Multiset.map_map]

theorem lp_eval_ne_zero (S : Multiset ℤ) (x : ℚ) (h : ∀ z ∈ S, (z : ℚ) ≠ x) :
    (lp S).eval x ≠ 0 := by
  rw [lp_eval]
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0
  exact h z hz (by linarith)

theorem lp_taylor (S : Multiset ℤ) (c : ℤ) :
    taylor (c : ℚ) (lp S) = lp (S.map (· - c)) := by
  rw [lp, lp, Polynomial.taylor_apply, Polynomial.multiset_prod_comp, Multiset.map_map,
    Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    Int.cast_sub, map_sub]
  ring

/-! ### Rational functions with integer zeros and poles -/

/-- `lin Z P = ∏_{z ∈ Z} (X - z) / ∏_{p ∈ P} (X - p)`. -/
def lin (Z P : Multiset ℤ) : ℚ⟮X⟯ := algebraMap ℚ[X] ℚ⟮X⟯ (lp Z) / algebraMap ℚ[X] ℚ⟮X⟯ (lp P)

theorem lin_add (Z₁ P₁ Z₂ P₂ : Multiset ℤ) :
    lin (Z₁ + Z₂) (P₁ + P₂) = lin Z₁ P₁ * lin Z₂ P₂ := by
  simp only [lin, lp_add, map_mul]; rw [div_mul_div_comm]

theorem lin_zero : lin 0 0 = 1 := by simp [lin, lp_zero]

theorem lin_ne_zero (Z P : Multiset ℤ) : lin Z P ≠ 0 :=
  div_ne_zero (Aux.algebraMap_ne_zero' (lp_ne_zero Z)) (Aux.algebraMap_ne_zero' (lp_ne_zero P))

theorem lin_cons_left (z : ℤ) (Z P : Multiset ℤ) :
    lin (z ::ₘ Z) P = (RatFunc.X - RatFunc.C (z : ℚ)) * lin Z P := by
  simp only [lin, lp_cons, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  ring

theorem lin_cons_right (z : ℤ) (Z P : Multiset ℤ) :
    (RatFunc.X - RatFunc.C (z : ℚ)) * lin Z (z ::ₘ P) = lin Z P := by
  simp only [lin, lp_cons, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have h : (RatFunc.X - RatFunc.C (z : ℚ)) ≠ 0 := X_sub_C_ne_zero' (z : ℚ)
  have h2 : algebraMap ℚ[X] ℚ⟮X⟯ (lp P) ≠ 0 := Aux.algebraMap_ne_zero' (lp_ne_zero P)
  field_simp

theorem lin_cancel (z : ℤ) (Z P : Multiset ℤ) : lin (z ::ₘ Z) (z ::ₘ P) = lin Z P := by
  rw [lin_cons_left, lin_cons_right]

theorem lin_replicate_cancel (m : ℕ) (z : ℤ) (Z P : Multiset ℤ) :
    lin (Multiset.replicate m z + Z) (Multiset.replicate m z + P) = lin Z P := by
  induction m with
  | zero => simp
  | succ m ih => rw [Multiset.replicate_succ, Multiset.cons_add, Multiset.cons_add, lin_cancel, ih]

theorem lin_laurent (c : ℤ) (Z P : Multiset ℤ) :
    RatFunc.laurent (c : ℚ) (lin Z P) = lin (Z.map (· - c)) (P.map (· - c)) := by
  simp only [lin, RatFunc.laurent_div, RatFunc.laurent_algebraMap, lp_taylor]

theorem lin_denom_dvd (Z P : Multiset ℤ) : (lin Z P).denom ∣ lp P := RatFunc.denom_div_dvd _ _

theorem lin_roots_le (Z P : Multiset ℤ) : (lin Z P).denom.roots ≤ P.map (Int.cast : ℤ → ℚ) := by
  have := Polynomial.roots.le_of_dvd (lp_ne_zero P) (lin_denom_dvd Z P)
  rwa [lp_roots] at this

theorem lin_split (Z P : Multiset ℤ) : (lin Z P).denom.roots.card = (lin Z P).denom.natDegree :=
  Polynomial.splits_iff_card_roots.mp ((lp_splits P).of_dvd (lp_ne_zero P) (lin_denom_dvd Z P))

theorem lin_poles (Z P : Multiset ℤ) (K : ℤ) (hP : ∀ p ∈ P, p < K) :
    ∀ h ∈ (lin Z P).denom.roots, ∃ n : ℤ, n < K ∧ h = n := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le (lin_roots_le Z P) hh)
  exact ⟨p, hP p hp, rfl⟩

/-- Cancel the common copies of `K` in the zeros and the poles. -/
theorem exists_reduce (Z P : Multiset ℤ) (K : ℤ) (ord : ℕ) (hord : P.count K + ord ≤ Z.count K) :
    ∃ Z' P' : Multiset ℤ, lin Z P = lin Z' P' ∧ K ∉ P' ∧ ord ≤ Z'.count K ∧ ∀ p ∈ P', p ∈ P := by
  classical
  set m := P.count K with hm
  obtain ⟨Z', hZ'⟩ := Multiset.le_iff_exists_add.mp
    (Multiset.le_count_iff_replicate_le.mp (show m ≤ Z.count K by omega))
  have hP : P = Multiset.replicate m K + P.filter (fun a => ¬ a = K) := by
    conv_lhs => rw [← Multiset.filter_add_not (fun a => a = K) P]
    rw [Multiset.filter_eq']
  refine ⟨Z', P.filter (fun a => ¬ a = K), ?_, ?_, ?_, fun p hp => (Multiset.mem_filter.mp hp).1⟩
  · rw [show lin Z P = lin (Multiset.replicate m K + Z')
        (Multiset.replicate m K + P.filter (fun a => ¬ a = K)) by rw [← hZ', ← hP],
      lin_replicate_cancel]
  · simp
  · have := congrArg (Multiset.count K) hZ'
    rw [Multiset.count_add, Multiset.count_replicate_self] at this
    omega

/-! ### Vanishing of derivatives at a multiple zero -/

theorem rfEval_rfDeriv_sq (Q₁ Q₂ : ℚ[X]) (K : ℚ) (h : Q₂.eval K ≠ 0) :
    rfEval (rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ ((X - C K) ^ 2 * Q₁) / algebraMap ℚ[X] ℚ⟮X⟯ Q₂)) K =
      0 := by
  have hQ : Q₂ ≠ 0 := fun h0 => h (by simp [h0])
  rw [Aux.rfDeriv_div _ _ hQ, Aux.rfEval_div _ _ _ (by rw [eval_pow]; exact pow_ne_zero 2 h)]
  simp [derivative_mul, derivative_pow]

theorem rfDeriv_cube (Q₁ Q₂ : ℚ[X]) (K : ℚ) (hQ : Q₂ ≠ 0) :
    rfDeriv (algebraMap ℚ[X] ℚ⟮X⟯ ((X - C K) ^ 3 * Q₁) / algebraMap ℚ[X] ℚ⟮X⟯ Q₂) =
      algebraMap ℚ[X] ℚ⟮X⟯ ((X - C K) ^ 2 *
          (3 * Q₁ * Q₂ + (X - C K) * (derivative Q₁ * Q₂ - Q₁ * derivative Q₂))) /
        algebraMap ℚ[X] ℚ⟮X⟯ (Q₂ ^ 2) := by
  rw [Aux.rfDeriv_div _ _ hQ]
  congr 2
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C,
    Nat.cast_ofNat, map_ofNat]
  ring

theorem deriv_zero_of_count (Z P : Multiset ℤ) (K : ℤ) (hP : K ∉ P) (hZ : 2 ≤ Z.count K) :
    rfEval (rfDeriv (lin Z P)) K = 0 := by
  obtain ⟨Z₀, hZ₀⟩ := Multiset.le_iff_exists_add.mp (Multiset.le_count_iff_replicate_le.mp hZ)
  rw [hZ₀, lin, lp_add, lp_replicate]
  exact rfEval_rfDeriv_sq _ _ _ (lp_eval_ne_zero P K fun z hz h => hP (by
    have : z = K := by exact_mod_cast h
    exact this ▸ hz))

theorem deriv2_zero_of_count (Z P : Multiset ℤ) (K : ℤ) (hP : K ∉ P) (hZ : 3 ≤ Z.count K) :
    rfEval (rfDeriv (rfDeriv (lin Z P))) K = 0 := by
  obtain ⟨Z₀, hZ₀⟩ := Multiset.le_iff_exists_add.mp (Multiset.le_count_iff_replicate_le.mp hZ)
  have hev : (lp P).eval (K : ℚ) ≠ 0 := lp_eval_ne_zero P K fun z hz h => hP (by
    have : z = K := by exact_mod_cast h
    exact this ▸ hz)
  rw [hZ₀, lin, lp_add, lp_replicate, rfDeriv_cube _ _ _ (lp_ne_zero P)]
  exact rfEval_rfDeriv_sq _ _ _ (by rw [eval_pow]; exact pow_ne_zero 2 hev)

/-! ### The interface for the two functionals -/

/-- A functional `Φ_K` on rational functions with the properties used by the transport:
linearity, the boundary identity `Φ_K[g] = Φ_K[g(t-1)]` whenever all poles of `g` are `≤ K`
and `g` has a zero of order `≥ ord` at `K` (after cancellation), and the cutoff move
`Φ_{K+1}[f] = Φ_K[f]` whenever the poles are `≤ K` and `f` has a zero of order `≥ ord` at
`K + 1`. -/
structure IsMom (Φ : ℤ → ℚ⟮X⟯ → FormalZ) (ord : ℕ) : Prop where
  add : ∀ K f g, Φ K (f + g) = Φ K f + Φ K g
  C_mul : ∀ K (c : ℚ) f, Φ K (RatFunc.C c * f) = c • Φ K f
  shift : ∀ K (Z P : Multiset ℤ), (∀ p ∈ P, p ≤ K) → P.count K + ord ≤ Z.count K →
    Φ K (lin Z P) = Φ K (RatFunc.laurent (-1 : ℚ) (lin Z P))
  cut : ∀ K (Z P : Multiset ℤ), (∀ p ∈ P, p ≤ K) → ord ≤ Z.count (K + 1) →
    Φ (K + 1) (lin Z P) = Φ K (lin Z P)

theorem Lfun_laurent_neg_one (K : ℤ) (f : ℚ⟮X⟯) :
    Lfun K (RatFunc.laurent (-1 : ℚ) f) = Lfun (K - 1) f := by
  rw [show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num, Aux.Lfun_laurent, show K + -1 = K - 1 by ring]

theorem Lfun_shift (K : ℤ) (Z P : Multiset ℤ) (hP : ∀ p ∈ P, p ≤ K)
    (h : P.count K + 2 ≤ Z.count K) :
    Lfun K (lin Z P) = Lfun K (RatFunc.laurent (-1 : ℚ) (lin Z P)) := by
  obtain ⟨Z', P', he, hK, hc, hsub⟩ := exists_reduce Z P K 2 h
  rw [he, Lfun_laurent_neg_one, ← sub_eq_zero,
    Lfun_sub_Lfun_pred K _ (lin_split _ _) (lin_poles _ _ _ fun p hp =>
      lt_of_le_of_ne (hP p (hsub p hp)) fun e => hK (e ▸ hp)),
    deriv_zero_of_count _ _ _ hK hc, zero_smul]

theorem Lfun_cut (K : ℤ) (Z P : Multiset ℤ) (hP : ∀ p ∈ P, p ≤ K) (h : 2 ≤ Z.count (K + 1)) :
    Lfun (K + 1) (lin Z P) = Lfun K (lin Z P) := by
  have hc0 : P.count (K + 1) = 0 := Multiset.count_eq_zero.mpr fun hm => by have := hP _ hm; omega
  obtain ⟨Z', P', he, hK, hc, hsub⟩ := exists_reduce Z P (K + 1) 2 (by omega)
  have key := Lfun_sub_Lfun_pred (K + 1) (lin Z' P') (lin_split _ _)
    (lin_poles _ _ _ fun p hp => by have := hP p (hsub p hp); omega)
  rw [show K + 1 - 1 = K by ring, deriv_zero_of_count _ _ _ hK hc, zero_smul, sub_eq_zero] at key
  rw [he, key]

theorem isMom_Lfun : IsMom Lfun 2 :=
  ⟨Aux.Lfun_add, Aux.Lfun_C_mul, Lfun_shift, Lfun_cut⟩

theorem Mfun_C_mul (K : ℤ) (c : ℚ) (f : ℚ⟮X⟯) : Mfun K (RatFunc.C c * f) = c • Mfun K f := by
  rw [← RatFunc.smul_eq_C_mul, Aux.Mfun_smul]

theorem Mfun_shift (K : ℤ) (Z P : Multiset ℤ) (hP : ∀ p ∈ P, p ≤ K)
    (h : P.count K + 3 ≤ Z.count K) :
    Mfun K (lin Z P) = Mfun K (RatFunc.laurent (-1 : ℚ) (lin Z P)) := by
  obtain ⟨Z', P', he, hK, hc, hsub⟩ := exists_reduce Z P K 3 h
  have hpoles := lin_poles Z' P' K fun p hp =>
    lt_of_le_of_ne (hP p (hsub p hp)) fun e => hK (e ▸ hp)
  have key := Lfun_sub_Lfun_pred K (rfDeriv (lin Z' P')) (rfDeriv_split _ (lin_split _ _))
    (fun h hh => hpoles h (rfDeriv_poles _ h hh))
  rw [deriv2_zero_of_count _ _ _ hK hc, zero_smul, sub_eq_zero] at key
  rw [he, Mfun, Mfun, Aux.rfDeriv_laurent, Lfun_laurent_neg_one, key]

theorem Mfun_cut (K : ℤ) (Z P : Multiset ℤ) (hP : ∀ p ∈ P, p ≤ K) (h : 3 ≤ Z.count (K + 1)) :
    Mfun (K + 1) (lin Z P) = Mfun K (lin Z P) := by
  have hc0 : P.count (K + 1) = 0 := Multiset.count_eq_zero.mpr fun hm => by have := hP _ hm; omega
  obtain ⟨Z', P', he, hK, hc, hsub⟩ := exists_reduce Z P (K + 1) 3 (by omega)
  have hpoles := lin_poles Z' P' (K + 1) fun p hp => by have := hP p (hsub p hp); omega
  have key := Lfun_sub_Lfun_pred (K + 1) (rfDeriv (lin Z' P')) (rfDeriv_split _ (lin_split _ _))
    (fun h hh => hpoles h (rfDeriv_poles _ h hh))
  rw [show K + 1 - 1 = K by ring, deriv2_zero_of_count _ _ _ hK hc, zero_smul, sub_eq_zero] at key
  rw [he, Mfun, Mfun, key]

theorem isMom_Mfun : IsMom Mfun 3 :=
  ⟨Aux.Mfun_add, Mfun_C_mul, Mfun_shift, Mfun_cut⟩

/-! ### The kernel of a parameter point -/

/-- `Γ(X + b)/Γ(X + a)` for integers `a, b`: `(X + a)_{b-a}` if `a ≤ b`, `1/(X + b)_{a-b}` if
`a > b`. Zeros `{1-b, …, -a}`, poles `{1-a, …, -b}`. -/
def pairKer (b a : ℤ) : ℚ⟮X⟯ := lin (ival (1 - b) (b - a).toNat) (ival (1 - a) (a - b).toNat)

/-- Lowering `a` by one multiplies the kernel by `X + a - 1`. -/
theorem pairKer_lower (b a : ℤ) :
    pairKer b (a - 1) = (RatFunc.X - RatFunc.C ((1 - a : ℤ) : ℚ)) * pairKer b a := by
  rcases le_or_gt a b with h | h
  · have h1 : (b - (a - 1)).toNat = (b - a).toNat + 1 := by omega
    have h2 : (a - 1 - b).toNat = 0 := by omega
    have h3 : (a - b).toNat = 0 := by omega
    have h4 : 1 - b + ((b - a).toNat : ℤ) = 1 - a := by omega
    rw [pairKer, pairKer, h1, h2, h3, ival_zero, ival_zero, ival_succ, h4, lin_cons_left]
  · have h1 : (b - (a - 1)).toNat = 0 := by omega
    have h2 : (b - a).toNat = 0 := by omega
    have h3 : (a - b).toNat = (a - 1 - b).toNat + 1 := by omega
    have h4 : 1 - a + 1 = 1 - (a - 1) := by ring
    rw [pairKer, pairKer, h1, h2, h3, ival_succ', h4, lin_cons_right]

/-- Raising `b` by one multiplies the kernel by `X + b`. -/
theorem pairKer_raise (b a : ℤ) :
    pairKer (b + 1) a = (RatFunc.X - RatFunc.C ((-b : ℤ) : ℚ)) * pairKer b a := by
  rcases le_or_gt a b with h | h
  · have h1 : (b + 1 - a).toNat = (b - a).toNat + 1 := by omega
    have h2 : (a - (b + 1)).toNat = 0 := by omega
    have h3 : (a - b).toNat = 0 := by omega
    have h4 : 1 - (b + 1) = -b := by ring
    have h5 : -b + 1 = 1 - b := by ring
    rw [pairKer, pairKer, h1, h2, h3, h4, ival_zero, ival_succ', h5, lin_cons_left]
  · have h1 : (b + 1 - a).toNat = 0 := by omega
    have h2 : (b - a).toNat = 0 := by omega
    have h3 : (a - b).toNat = (a - (b + 1)).toNat + 1 := by omega
    have h4 : 1 - a + ((a - (b + 1)).toNat : ℤ) = -b := by omega
    rw [pairKer, pairKer, h1, h2, h3, ival_zero, ival_zero, ival_succ, h4, lin_cons_right]

/-- The functional equation of one pair: `r(t-1)(t - 1 + b) = r(t)(t - 1 + a)`. -/
theorem pairKer_laurent (b a : ℤ) :
    RatFunc.laurent (-1 : ℚ) (pairKer b a) * (RatFunc.X - RatFunc.C ((1 - b : ℤ) : ℚ)) =
      pairKer b a * (RatFunc.X - RatFunc.C ((1 - a : ℤ) : ℚ)) := by
  have hl : RatFunc.laurent (-1 : ℚ) (pairKer b a) =
      lin (ival (2 - b) (b - a).toNat) (ival (2 - a) (a - b).toNat) := by
    rw [pairKer, show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num, lin_laurent]
    simp only [sub_neg_eq_add, ival_map_add]
    congr 2 <;> ring
  rw [hl]
  rcases lt_trichotomy a b with h | rfl | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (b - a).toNat = n + 1 := ⟨(b - a - 1).toNat, by omega⟩
    have h0 : (a - b).toNat = 0 := by omega
    have hZ1 : (1 - b) ::ₘ ival (2 - b) (n + 1) = ival (1 - b) (n + 2) := by
      rw [ival_succ' (1 - b) (n + 1)]; congr 2; ring
    have hZ2 : (1 - a) ::ₘ ival (1 - b) (n + 1) = ival (1 - b) (n + 2) := by
      rw [ival_succ (1 - b) (n + 1)]; congr 1; push_cast; omega
    rw [hn, h0, ival_zero, pairKer, hn, h0, ival_zero, mul_comm, ← lin_cons_left, hZ1, mul_comm,
      ← lin_cons_left, hZ2]
  · simp only [sub_self, Int.toNat_zero, ival_zero, pairKer]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (a - b).toNat = m + 1 := ⟨(a - b - 1).toNat, by omega⟩
    have h0 : (b - a).toNat = 0 := by omega
    have hP1 : ival (2 - a) (m + 1) = (1 - b) ::ₘ ival (2 - a) m := by
      rw [ival_succ]; congr 1; omega
    have hP2 : ival (1 - a) (m + 1) = (1 - a) ::ₘ ival (2 - a) m := by
      rw [ival_succ']; congr 2; ring
    rw [hm, h0, ival_zero, pairKer, hm, h0, ival_zero, hP1, mul_comm, lin_cons_right, hP2,
      mul_comm, lin_cons_right]

/-- The pairing of lower with upper parameters: `(b₀,a₄), (b₁,a₀), (b₂,a₁), (b₃,a₂), (b₄,a₃)`. -/
def σ : Fin 5 → Fin 5 := ![4, 0, 1, 2, 3]

/-- The rational kernel `r_{a,b}(t) = ∏_j Γ(t + b_j) / ∏_i Γ(t + a_i)` of a parameter point. -/
def ker (a b : Fin 5 → ℤ) : ℚ⟮X⟯ :=
  pairKer (b 0) (a 4) * pairKer (b 1) (a 0) * pairKer (b 2) (a 1) * pairKer (b 3) (a 2) *
    pairKer (b 4) (a 3)

theorem ker_ne_zero (a b : Fin 5 → ℤ) : ker a b ≠ 0 := by
  unfold ker pairKer
  repeat' apply mul_ne_zero
  all_goals exact lin_ne_zero _ _

/-- The linear factor `X - C c`, with `c : ℤ`. -/
def lf (c : ℤ) : ℚ⟮X⟯ := RatFunc.X - RatFunc.C (c : ℚ)

theorem lf_ne_zero (c : ℤ) : lf c ≠ 0 := X_sub_C_ne_zero' _

/-- The functional equation of the kernel:
`r(t-1) ∏_j (t - 1 + b_j) = r(t) ∏_i (t - 1 + a_i)`. -/
theorem ker_laurent (a b : Fin 5 → ℤ) :
    RatFunc.laurent (-1 : ℚ) (ker a b) * (lf (1 - b 0) * lf (1 - b 1) * lf (1 - b 2) *
      lf (1 - b 3) * lf (1 - b 4)) =
    ker a b * (lf (1 - a 0) * lf (1 - a 1) * lf (1 - a 2) * lf (1 - a 3) * lf (1 - a 4)) := by
  have h0 := pairKer_laurent (b 0) (a 4)
  have h1 := pairKer_laurent (b 1) (a 0)
  have h2 := pairKer_laurent (b 2) (a 1)
  have h3 := pairKer_laurent (b 3) (a 2)
  have h4 := pairKer_laurent (b 4) (a 3)
  simp only [ker, map_mul, lf] at *
  calc _ = (RatFunc.laurent (-1 : ℚ) (pairKer (b 0) (a 4)) *
            (RatFunc.X - RatFunc.C ((1 - b 0 : ℤ) : ℚ))) *
          (RatFunc.laurent (-1 : ℚ) (pairKer (b 1) (a 0)) *
            (RatFunc.X - RatFunc.C ((1 - b 1 : ℤ) : ℚ))) *
          (RatFunc.laurent (-1 : ℚ) (pairKer (b 2) (a 1)) *
            (RatFunc.X - RatFunc.C ((1 - b 2 : ℤ) : ℚ))) *
          (RatFunc.laurent (-1 : ℚ) (pairKer (b 3) (a 2)) *
            (RatFunc.X - RatFunc.C ((1 - b 3 : ℤ) : ℚ))) *
          (RatFunc.laurent (-1 : ℚ) (pairKer (b 4) (a 3)) *
            (RatFunc.X - RatFunc.C ((1 - b 4 : ℤ) : ℚ))) := by ring
    _ = _ := by rw [h0, h1, h2, h3, h4]; ring

end ZetasIrr.CMF
