/-
# The local identity (sorry-free)

On the second node `p ≤ j + 2n < 2p` of a support class, `a_j/p ≡ 8 T(-j)` and `b_j ≡ 4 T(-j)`.
-/
import residue_aux4

open Finset Polynomial

noncomputable section

namespace Pfq54.RA

open Pfq54
open ZetasIrr.Aux (ValGE)

theorem pr_replicate (m : ℕ) (c t : ℤ) : pr (Multiset.replicate m c) t = (t - c) ^ m := by
  unfold pr
  rw [Multiset.map_replicate, Multiset.prod_replicate]

theorem Ls_replicate (m : ℕ) (c t : ℤ) :
    Ls (Multiset.replicate m c) t = (m : ℚ) * (1 / ((t - c : ℤ) : ℚ)) := by
  unfold Ls
  rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

theorem emod_range (x p q : ℤ) (h1 : q * p ≤ x) (h2 : x < q * p + p) : x % p = x - q * p := by
  have h := Int.add_mul_emod_self_right (x - q * p) q p
  rw [sub_add_cancel] at h
  rw [h, Int.emod_eq_of_lt (by linarith) (by linarith)]

/-- On a support class the numerator roots `≡ k` are `k, k, k`. -/
theorem class_N (n p k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p)
    (hs : 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) :
    (nR n).filter (fun x => x % (p : ℤ) = k) = Multiset.replicate 3 (k : ℤ) := by
  rw [Multiset.eq_replicate]
  refine ⟨?_, fun x hx => ?_⟩
  · have := rc_num n p k h8 h11 hk
    simp (disch := omega) only [ite_one, ite_zero] at this
    show rc (nR n) p k = 3
    omega
  · obtain ⟨hxN, hxk⟩ := Multiset.mem_filter.mp hx
    have hb := mem_nR n x hxN
    rcases lt_or_ge x p with h | h
    · have := emod_range x p 0 (by omega) (by omega)
      omega
    · have := emod_range x p 1 (by omega) (by omega)
      omega

/-- On a support class the denominator roots `≡ k` other than `-j = k - 2p` are `k - p, k - p`. -/
theorem class_R (n p j k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p)
    (hs : 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) (hjk : j + k = 2 * p)
    (htk : (-(j : ℤ)) % p = k) :
    (Rj n j).filter (fun x => x % (p : ℤ) = k) = Multiset.replicate 2 ((k : ℤ) - p) := by
  rw [Multiset.eq_replicate]
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 := rc_den n p k h8 h11 hk
    simp (disch := omega) only [ite_one, ite_zero] at h1
    have h2 : rc (Rj n j) p k + (dR n).count (-(j : ℤ)) = rc (dR n) p k :=
      rc_filter_ne p (dR n) _ k htk
    have h3 : (dR n).count (-(j : ℤ)) = 2 := by
      rw [dR, Multiset.count_add, count_Icc, count_Icc, ite_eq_left (by omega),
        ite_eq_left (by omega)]
    show rc (Rj n j) p k = 2
    omega
  · obtain ⟨hxR, hxk⟩ := Multiset.mem_filter.mp hx
    have hb := mem_Rj n j x hxR
    rcases lt_or_ge x (-2 * p) with h | h
    · have := emod_range x p (-3) (by omega) (by omega)
      omega
    rcases lt_or_ge x (-p) with h' | h'
    · have := emod_range x p (-2) (by omega) (by omega)
      omega
    · have := emod_range x p (-1) (by omega) (by omega)
      omega

variable (p : ℕ) [hp : Fact p.Prime]

theorem valGE_dvd (z : ℤ) (h : (p : ℤ) ∣ z) : ValGE p 1 (z : ℚ) := by
  obtain ⟨w, rfl⟩ := h
  rcases eq_or_ne w 0 with hw | hw
  · left
    rw [hw, mul_zero, Int.cast_zero]
  · right
    rw [Int.cast_mul, Int.cast_natCast, padicValRat.mul (Nat.cast_ne_zero.mpr hp.out.ne_zero)
      (Int.cast_ne_zero.mpr hw), padicValRat.self hp.out.one_lt, padicValRat.of_int]
    omega

omit hp in
theorem valGE_int (z : ℤ) : ValGE p 0 (z : ℚ) := by
  rcases eq_or_ne z 0 with h | h
  · left
    rw [h, Int.cast_zero]
  · right
    rw [padicValRat.of_int]
    exact Nat.cast_nonneg _

theorem valGE_ofNat (c : ℕ) [c.AtLeastTwo] : ValGE p 0 (OfNat.ofNat c : ℚ) := by
  have := valGE_int p (OfNat.ofNat c)
  rwa [Int.cast_ofNat] at this

theorem valGE_inv_p : ValGE p (-1) ((p : ℚ)⁻¹) :=
  Or.inr (by rw [padicValRat.inv, padicValRat.self hp.out.one_lt])

/-- Residues of the unit parts: `N̄*(k) + T(-j) D̄*(k) = 0` on a support class. -/
theorem unit_dvd (n j k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p)
    (hs : 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) (htk : (-(j : ℤ)) % p = k) :
    (p : ℤ) ∣ pr ((nR n).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) +
      (Tp n p).eval (-(j : ℤ)) * pr ((Rj n j).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul]
  have hT : (((Tp n p).eval (-(j : ℤ)) : ℤ) : ZMod p) = (((Tp n p).eval (k : ℤ) : ℤ) : ZMod p) := by
    rw [← sub_eq_zero, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Tp_congr n p _ k htk)
  have hRa : ∀ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (Rj n j) p a =
      ((k : ZMod p) - a) ^ rc (dR n) p a := fun a ha => by
    rw [show rc (Rj n j) p a = rc (dR n) p a from
      rc_filter_ne' p (dR n) _ k a htk (Finset.ne_of_mem_erase ha)]
  rw [unit_part p (nR n) _ k htk, unit_part p (Rj n j) _ k htk, Finset.prod_congr rfl hRa, hT]
  linear_combination Tp_supp n p k h8 h11 hk hs

/-- **The support classes** (second node `j = 2p - k`). -/
theorem supp_case (n j k : ℕ) (h29 : 29 < p) (h8 : 8 * n < p) (h11 : p < 11 * n)
    (hp2 : 30 * n < p ^ 2) (hk : k < p)
    (hs : 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) (hjk : j + k = 2 * p)
    (htk : (-(j : ℤ)) % p = k) :
    ValGE p 1 ((-1) ^ n * U n j / Cn n / p - 8 * (((Tp n p).eval (-(j : ℤ)) : ℤ) : ℚ)) ∧
      ValGE p 1 ((-1) ^ n * V n j / Cn n - 4 * (((Tp n p).eval (-(j : ℤ)) : ℤ) : ℚ)) := by
  obtain ⟨-, hAv, hAR, hB⟩ := val_double p n j k hp2 (by omega) (by omega) htk
  have hdvd := unit_dvd p n j k h8 h11 hk hs htk
  have hfR : ∀ x ∈ (Rj n j).filter (fun x => ¬ x % (p : ℤ) = k),
      -(j : ℤ) - x ≠ 0 ∧ (-(j : ℤ) - x).natAbs < p ^ 2 := fun x hx =>
    fac_Rj n p j (by omega) hp2 x (Multiset.mem_of_mem_filter hx)
  obtain ⟨huR0, huRv⟩ := val_pr_rc p _ _ k htk hfR
  have hrc0 : rc ((Rj n j).filter fun x => ¬ x % (p : ℤ) = k) p k = 0 := by
    unfold rc
    rw [Multiset.filter_filter]
    exact Multiset.card_eq_zero.mpr (Multiset.filter_eq_nil.mpr fun x _ h => h.2 h.1)
  rw [hrc0, Nat.cast_zero] at huRv
  have hnd : ∀ s : Multiset ℤ, ∀ x ∈ s.filter (fun x => ¬ x % (p : ℤ) = k),
      ¬ (p : ℤ) ∣ -(j : ℤ) - x := fun s x hx hd =>
    (Multiset.mem_filter.mp hx).2 (by
      have h' : x % (p : ℤ) = (-(j : ℤ)) % p := Int.modEq_iff_dvd.mpr hd
      rw [h', htk])
  have hL0 := (valGE_Ls0 p _ _ (fun x hx => fac_nR n p j (by omega) hp2 x
      (Multiset.mem_of_mem_filter hx)) (hnd (nR n))).sub (valGE_Ls0 p _ _ hfR (hnd (Rj n j)))
  have hprN : pr (nR n) (-(j : ℤ)) =
      (-2 * p) ^ 3 * pr ((nR n).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) := by
    rw [pr_split (nR n) _ (fun x => x % (p : ℤ) = k), class_N n p k h8 h11 hk hs, pr_replicate,
      show -(j : ℤ) - k = -2 * p by omega]
  have hprR : pr (Rj n j) (-(j : ℤ)) =
      p ^ 2 * pr ((Rj n j).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) := by
    rw [pr_split (Rj n j) _ (fun x => x % (p : ℤ) = k), class_R n p j k h8 h11 hk hs hjk htk,
      pr_replicate, show -(j : ℤ) - (k - p) = -p by omega, neg_sq]
  have hLN : Ls (nR n) (-(j : ℤ)) = ((3 : ℕ) : ℚ) * (1 / ((-2 * p : ℤ) : ℚ)) +
      Ls ((nR n).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) := by
    rw [Ls_split (nR n) _ (fun x => x % (p : ℤ) = k), class_N n p k h8 h11 hk hs, Ls_replicate,
      show -(j : ℤ) - k = -2 * p by omega]
  have hLR : Ls (Rj n j) (-(j : ℤ)) = ((2 : ℕ) : ℚ) * (1 / ((-p : ℤ) : ℚ)) +
      Ls ((Rj n j).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) := by
    rw [Ls_split (Rj n j) _ (fun x => x % (p : ℤ) = k), class_R n p j k h8 h11 hk hs hjk htk,
      Ls_replicate, show -(j : ℤ) - (k - p) = -p by omega]
  rw [hprR, hprN] at hAR
  rw [hLN, hLR] at hB
  have hrc := root_count' n p k h8 h11 hk
  set A := (-1) ^ n * U n j / Cn n
  set uN := pr ((nR n).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ))
  set uR := pr ((Rj n j).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ))
  set Tt := (Tp n p).eval (-(j : ℤ))
  set L' := Ls ((nR n).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ)) -
    Ls ((Rj n j).filter fun x => ¬ x % (p : ℤ) = k) (-(j : ℤ))
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have huR0' : (uR : ℚ) ≠ 0 := Int.cast_ne_zero.mpr huR0
  push_cast at hAR hB
  have hA : A = -8 * p * uN / uR := by
    rw [eq_div_iff huR0']
    apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
    linear_combination hAR
  have e1 : A / p - 8 * (Tt : ℚ) = -8 * ((uN + Tt * uR : ℤ) : ℚ) * (uR : ℚ)⁻¹ := by
    rw [hA]
    push_cast
    field_simp
    ring
  have g1 : ValGE p 1 (A / p - 8 * (Tt : ℚ)) := by
    rw [e1]
    have hm8 : ValGE p 0 (-8 : ℚ) := (valGE_ofNat p 8).neg
    have hinv : ValGE p 0 ((uR : ℚ)⁻¹) := Or.inr (by rw [padicValRat.inv, huRv, neg_zero])
    exact ((hm8.mul (valGE_dvd p _ hdvd)).mul hinv).mono (by norm_num)
  refine ⟨g1, ?_⟩
  have e2 : (-1) ^ n * V n j / Cn n - 4 * (Tt : ℚ) = 2⁻¹ * (A / p - 8 * (Tt : ℚ)) + A * L' := by
    rw [hB]
    field_simp
    ring
  rw [e2]
  have hA1 : ValGE p 1 A := Or.inr (by rw [hAv]; omega)
  have h2inv : ValGE p 0 ((2 : ℚ)⁻¹) := (BP.valGE_consts n p h29 (by omega) (by omega)).2.1
  exact ((h2inv.mul g1).mono (by norm_num)).add ((hA1.mul hL0).mono (by norm_num))

/-- The local conditions at the index `j`. -/
def Good (n p : ℕ) (T : Polynomial ℤ) (j : ℕ) : Prop :=
  ValGE p 1 ((-1) ^ n * U n j / Cn n) ∧ ValGE p 0 ((-1) ^ n * V n j / Cn n) ∧
    (p ≤ j + 2 * n → j + 2 * n < 2 * p →
      ValGE p 1 ((-1) ^ n * U n j / Cn n / p - 8 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ)) ∧
        ValGE p 1 ((-1) ^ n * V n j / Cn n - 4 * ((T.eval (-(j : ℤ)) : ℤ) : ℚ))) ∧
    (2 * p ≤ j + 2 * n →
      ValGE p 1 ((-1) ^ n * U n j / Cn n / p) ∧ ValGE p 1 ((-1) ^ n * V n j / Cn n))

omit hp in
theorem good_zero (n j : ℕ) (h8 : 8 * n < p) (h : j < n) : Good n p (Tp n p) j := by
  obtain ⟨hU, hV⟩ := root_zero n j h
  have hA : (-1) ^ n * U n j / Cn n = 0 := by rw [hU, mul_zero, zero_div]
  have hB : (-1) ^ n * V n j / Cn n = 0 := by rw [hV, mul_zero, zero_div]
  exact ⟨Or.inl hA, Or.inl hB, fun h1 _ => absurd h1 (by omega), fun h1 => absurd h1 (by omega)⟩

theorem T_dvd (n j k : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hk : k < p)
    (hs : ¬ (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p)) (htk : (-(j : ℤ)) % p = k) :
    ValGE p 1 (((Tp n p).eval (-(j : ℤ)) : ℤ) : ℚ) := by
  have := Tp_congr n p _ k htk
  rw [Tp_zero n p k h8 h11 hk hs, sub_zero] at this
  exact valGE_dvd p _ this

theorem good_simple (n j : ℕ) (h8 : 8 * n < p) (h11 : p < 11 * n) (hp2 : 30 * n < p ^ 2)
    (hj : (n ≤ j ∧ j < 2 * n) ∨ (16 * n < j ∧ j ≤ 17 * n)) : Good n p (Tp n p) j := by
  obtain ⟨hkp, hkc, hkj⟩ := class_neg p j hp.out.pos (by omega)
  set k := ((-(j : ℤ)) % p).toNat
  have htk : (-(j : ℤ)) % p = k := hkc.symm
  obtain ⟨hA, hB0, hBv⟩ := val_simple p n j k hp2 hj htk
  have hrc := root_count' n p k h8 h11 hkp
  have hns : p ≤ j + 2 * n → ¬ (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) := by
    intro h
    omega
  have hB1 : p ≤ j + 2 * n → ValGE p 1 ((-1) ^ n * V n j / Cn n) := fun h =>
    Or.inr (by rw [hBv]; have := hrc.2.not.mpr (hns h); omega)
  refine ⟨Or.inl hA, Or.inr (by rw [hBv]; omega), fun h1 _ => ?_,
    fun h1 => ⟨by rw [hA, zero_div]; exact Or.inl rfl, hB1 (by omega)⟩⟩
  have hT := T_dvd p n j k h8 h11 hkp (hns h1) htk
  rw [hA, zero_div, zero_sub]
  exact ⟨(((valGE_ofNat p 8).mul hT).mono (by norm_num)).neg,
    (hB1 h1).sub (((valGE_ofNat p 4).mul hT).mono (by norm_num))⟩

theorem good_double (n j : ℕ) (h29 : 29 < p) (h8 : 8 * n < p) (h11 : p < 11 * n)
    (hp2 : 30 * n < p ^ 2) (h1 : 2 * n ≤ j) (h2 : j ≤ 16 * n) : Good n p (Tp n p) j := by
  obtain ⟨hkp, hkc, hkj⟩ := class_neg p j hp.out.pos (by omega)
  set k := ((-(j : ℤ)) % p).toNat
  have htk : (-(j : ℤ)) % p = k := hkc.symm
  obtain ⟨-, hAv, -, hB⟩ := val_double p n j k hp2 h1 h2 htk
  have hrc := root_count' n p k h8 h11 hkp
  have hL := (valGE_Ls p _ _ (fac_nR n p j (by omega) hp2)).sub
    (valGE_Ls p _ _ (fac_Rj n p j (by omega) hp2))
  have hA1 : ValGE p 1 ((-1) ^ n * U n j / Cn n) := Or.inr (by rw [hAv]; omega)
  have hns : ¬ (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) →
      ValGE p 1 ((-1) ^ n * U n j / Cn n / p) ∧ ValGE p 1 ((-1) ^ n * V n j / Cn n) := by
    intro hs
    have hA2 : ValGE p 2 ((-1) ^ n * U n j / Cn n) :=
      Or.inr (by rw [hAv]; have := hrc.2.not.mpr hs; omega)
    refine ⟨?_, ?_⟩
    · rw [div_eq_mul_inv _ (p : ℚ)]
      exact (hA2.mul (valGE_inv_p p)).mono (by norm_num)
    · rw [hB]
      exact (hA2.mul hL).mono (by norm_num)
  refine ⟨hA1, by rw [hB]; exact (hA1.mul hL).mono (by norm_num), fun h3 h4 => ?_,
    fun h3 => hns (by omega)⟩
  by_cases hs : 12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p
  · exact supp_case p n j k h29 h8 h11 hp2 hkp hs (by omega) htk
  · obtain ⟨hAp, hB1⟩ := hns hs
    have hT := T_dvd p n j k h8 h11 hkp hs htk
    exact ⟨hAp.sub (((valGE_ofNat p 8).mul hT).mono (by norm_num)),
      hB1.sub (((valGE_ofNat p 4).mul hT).mono (by norm_num))⟩

omit hp in
/-- **The local identity** (`T` of degree `≤ p - 2`, vanishing off the support). -/
theorem local_identity' (n : ℕ) (hp : Eligible n p) (h8 : 8 * n < p) (h11 : p < 11 * n) :
    ∃ T : Polynomial ℤ, T.natDegree ≤ p - 2 ∧
      (∀ k < p, ¬ (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) →
        (p : ℤ) ∣ T.eval (k : ℤ)) ∧
      ∀ j ≤ 17 * n, Good n p T j := by
  have : Fact p.Prime := ⟨hp.1⟩
  refine ⟨Tp n p, Tp_natDegree n p h8 h11,
    fun k hk hs => ⟨0, by rw [Tp_zero n p k h8 h11 hk hs, mul_zero]⟩, fun j hj => ?_⟩
  rcases lt_or_ge j n with h | h
  · exact good_zero p n j h8 h
  rcases lt_or_ge j (2 * n) with h' | h'
  · exact good_simple p n j h8 h11 hp.2.2.1 (Or.inl ⟨h, h'⟩)
  rcases le_or_gt j (16 * n) with h'' | h''
  · exact good_double p n j hp.2.1 h8 h11 hp.2.2.1 h' h''
  · exact good_simple p n j h8 h11 hp.2.2.1 (Or.inr ⟨h'', hj⟩)

/-- The second node `j` of the class `k`. -/
def jwin (n p k : ℕ) : ℕ := if k ≤ 2 * n then p - k else 2 * p - k

/-- The class `k = -j mod p` of the second node `j`. -/
def kwin (p j : ℕ) : ℕ := if j ≤ p then p - j else 2 * p - j

/-- The second nodes `p ≤ j + 2n < 2p` run once over the classes `k = -j mod p`; the classes
whose node exceeds `17n` lie off the support. -/
theorem window_dvd (n p : ℕ) (hlo : 8 * n < p) (hhi : p < 11 * n) (T : Polynomial ℤ)
    (hoff : ∀ k < p, ¬ (12 * n < p + k ∧ 2 * p ≤ 16 * n + k ∧ k + 2 * n ≤ p) →
      (p : ℤ) ∣ T.eval (k : ℤ)) :
    (p : ℤ) ∣ ∑ k ∈ range p, T.eval (k : ℤ) - ∑ j ∈ range (17 * n + 1),
      (if p ≤ j + 2 * n ∧ j + 2 * n < 2 * p then T.eval (-(j : ℤ)) else 0) := by
  have hS' : ∑ j ∈ range (17 * n + 1),
      (if p ≤ j + 2 * n ∧ j + 2 * n < 2 * p then T.eval (-(j : ℤ)) else 0) =
      ∑ k ∈ range p, (if jwin n p k ≤ 17 * n then T.eval (-(jwin n p k : ℤ)) else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (kwin p) (jwin n p) (fun j hj => ?_) (fun k hk => ?_) (fun j hj => ?_)
      (fun k hk => ?_) (fun j hj => ?_)
    · rw [Finset.mem_filter, mem_range] at hj
      rw [Finset.mem_filter, mem_range]
      unfold kwin jwin
      split_ifs <;> omega
    · rw [Finset.mem_filter, mem_range] at hk
      rw [Finset.mem_filter, mem_range]
      unfold jwin at hk ⊢
      split_ifs at hk ⊢ <;> omega
    · rw [Finset.mem_filter, mem_range] at hj
      unfold kwin jwin
      split_ifs <;> omega
    · rw [Finset.mem_filter, mem_range] at hk
      unfold jwin at hk
      unfold kwin jwin
      split_ifs at hk ⊢ <;> omega
    · rw [Finset.mem_filter, mem_range] at hj
      have : jwin n p (kwin p j) = j := by
        unfold kwin jwin
        split_ifs <;> omega
      rw [this]
  rw [hS', ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun k hk => ?_
  rw [mem_range] at hk
  by_cases hj : jwin n p k ≤ 17 * n
  · rw [ite_eq_left hj]
    have hdiv : (p : ℤ) ∣ (k : ℤ) - (-(jwin n p k : ℤ)) := by
      unfold jwin
      split_ifs with h
      · exact ⟨1, by omega⟩
      · exact ⟨2, by omega⟩
    exact hdiv.trans (Polynomial.sub_dvd_eval_sub _ _ _)
  · rw [ite_eq_right hj, sub_zero]
    exact hoff k hk (by unfold jwin at hj; split_ifs at hj <;> omega)

end Pfq54.RA
