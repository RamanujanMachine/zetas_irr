/-
# Generic lemmas for `residue_block.lean` (sorry-free)

Root products `∏_{x ∈ s} (t - x)`, their `p`-adic valuations and reductions modulo `p`.
-/
import residue_aux

open Finset

noncomputable section

namespace Pfq54.RA

open Pfq54
open ZetasIrr.Aux (ValGE)

/-- `∏_{x ∈ s} (t - x)`. -/
def pr (s : Multiset ℤ) (t : ℤ) : ℤ := (s.map fun x => t - x).prod

/-- `∑_{x ∈ s} 1/(t - x)`. -/
def Ls (s : Multiset ℤ) (t : ℤ) : ℚ := (s.map fun x => 1 / ((t - x : ℤ) : ℚ)).sum

theorem pr_add (s s' : Multiset ℤ) (t : ℤ) : pr (s + s') t = pr s t * pr s' t := by
  unfold pr; rw [Multiset.map_add, Multiset.prod_add]

theorem Ls_add (s s' : Multiset ℤ) (t : ℤ) : Ls (s + s') t = Ls s t + Ls s' t := by
  unfold Ls; rw [Multiset.map_add, Multiset.sum_add]

theorem pr_cons (x : ℤ) (s : Multiset ℤ) (t : ℤ) : pr (x ::ₘ s) t = (t - x) * pr s t := by
  unfold pr; rw [Multiset.map_cons, Multiset.prod_cons]

theorem Ls_cons (x : ℤ) (s : Multiset ℤ) (t : ℤ) :
    Ls (x ::ₘ s) t = 1 / ((t - x : ℤ) : ℚ) + Ls s t := by
  unfold Ls; rw [Multiset.map_cons, Multiset.sum_cons]

theorem pr_split (s : Multiset ℤ) (t : ℤ) (q : ℤ → Prop) [DecidablePred q] :
    pr s t = pr (s.filter q) t * pr (s.filter fun x => ¬ q x) t := by
  rw [← pr_add, Multiset.filter_add_not]

theorem Ls_split (s : Multiset ℤ) (t : ℤ) (q : ℤ → Prop) [DecidablePred q] :
    Ls s t = Ls (s.filter q) t + Ls (s.filter fun x => ¬ q x) t := by
  rw [← Ls_add, Multiset.filter_add_not]

/-- `∏_{x = t-e-m}^{t-e-1} (t - x) · e! = (e+m)!`. -/
theorem prod_below (t a b : ℤ) (e m : ℕ) (ha : a = t - e - m) (hb : b = t - e - 1) :
    (∏ x ∈ Icc a b, (t - x)) * (e.factorial : ℤ) = ((e + m).factorial : ℤ) := by
  subst ha hb
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty (by push_cast; omega), prod_empty, one_mul, add_zero]
  | succ m ih =>
    rw [show t - e - ((m + 1 : ℕ) : ℤ) = (t - e - m) - 1 by push_cast; ring,
      ← Finset.insert_Icc_left_eq_Icc_sub_one (by omega),
      prod_insert (fun h => by rw [mem_Icc] at h; omega), mul_assoc, ih, ← add_assoc,
      Nat.factorial_succ, Nat.cast_mul]
    congr 1
    push_cast; ring

/-- `∏_{x = t+e+1}^{t+e+m} (t - x) · e! = (-1)^m (e+m)!`. -/
theorem prod_above (t a b : ℤ) (e m : ℕ) (ha : a = t + e + 1) (hb : b = t + e + m) :
    (∏ x ∈ Icc a b, (t - x)) * (e.factorial : ℤ) = (-1) ^ m * ((e + m).factorial : ℤ) := by
  subst ha hb
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty (by push_cast; omega), prod_empty, one_mul, add_zero, pow_zero,
      one_mul]
  | succ m ih =>
    rw [show t + e + ((m + 1 : ℕ) : ℤ) = (t + e + m) + 1 by push_cast; ring,
      ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
      prod_insert (fun h => by rw [mem_Icc] at h; omega), mul_assoc, ih, ← add_assoc,
      Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast; ring

/-- `∑_{x = t-e-m}^{t-e-1} 1/(t - x) = H_{e+m} - H_e`. -/
theorem sum_below (t a b : ℤ) (e m : ℕ) (ha : a = t - e - m) (hb : b = t - e - 1) :
    ∑ x ∈ Icc a b, 1 / ((t - x : ℤ) : ℚ) = harm 1 (e + m) - harm 1 e := by
  subst ha hb
  induction m with
  | zero => rw [Finset.Icc_eq_empty (by push_cast; omega), sum_empty, add_zero, sub_self]
  | succ m ih =>
    rw [show t - e - ((m + 1 : ℕ) : ℤ) = (t - e - m) - 1 by push_cast; ring,
      ← Finset.insert_Icc_left_eq_Icc_sub_one (by omega),
      sum_insert (fun h => by rw [mem_Icc] at h; omega), ih, ← add_assoc, Aux.harm_succ]
    push_cast; ring

/-- `∑_{x = t+e+1}^{t+e+m} 1/(t - x) = -(H_{e+m} - H_e)`. -/
theorem sum_above (t a b : ℤ) (e m : ℕ) (ha : a = t + e + 1) (hb : b = t + e + m) :
    ∑ x ∈ Icc a b, 1 / ((t - x : ℤ) : ℚ) = -(harm 1 (e + m) - harm 1 e) := by
  subst ha hb
  induction m with
  | zero => rw [Finset.Icc_eq_empty (by push_cast; omega), sum_empty, add_zero, sub_self, neg_zero]
  | succ m ih =>
    rw [show t + e + ((m + 1 : ℕ) : ℤ) = (t + e + m) + 1 by push_cast; ring,
      ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
      sum_insert (fun h => by rw [mem_Icc] at h; omega), ih, ← add_assoc, Aux.harm_succ,
      show ((t - (t + e + m + 1) : ℤ) : ℚ) = -((e + m + 1 : ℕ) : ℚ) by push_cast; ring,
      one_div_neg_eq_neg_one_div]
    push_cast; ring

/-- An interval with the point `t` removed splits into the parts below and above `t`. -/
theorem Icc_filter_ne (a b t : ℤ) (ha : a ≤ t) (hb : t ≤ b) :
    (Icc a b).filter (fun x => x ≠ t) = Icc a (t - 1) ∪ Icc (t + 1) b := by
  ext x
  rw [mem_filter, mem_union, mem_Icc, mem_Icc, mem_Icc]
  omega

theorem Icc_disj (a b t : ℤ) : Disjoint (Icc a (t - 1)) (Icc (t + 1) b) :=
  Finset.disjoint_left.mpr fun x h1 h2 => by rw [mem_Icc] at h1 h2; omega

variable (p : ℕ) [hp : Fact p.Prime]

/-- `v_p(z) ∈ {0, 1}` for `0 < |z| < p²`. -/
theorem val_lin (z : ℤ) (hz : z ≠ 0) (hb : z.natAbs < p ^ 2) :
    padicValRat p (z : ℚ) = if (p : ℤ) ∣ z then 1 else 0 := by
  rw [padicValRat.of_int]
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  split_ifs with h
  · have h1 : p ∣ z.natAbs := Int.ofNat_dvd_left.mp h
    have hv1 : 1 ≤ padicValNat p z.natAbs := one_le_padicValNat_of_dvd hz' h1
    have hv2 : padicValNat p z.natAbs < 2 := by
      by_contra hc
      have hc : 2 ≤ padicValNat p z.natAbs := by omega
      have := (pow_dvd_pow p hc).trans (pow_padicValNat_dvd (n := z.natAbs))
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hz') this) (not_le.mpr hb)
    unfold padicValInt
    omega
  · unfold padicValInt
    rw [padicValNat.eq_zero_of_not_dvd fun h' => h (Int.ofNat_dvd_left.mpr h'), Nat.cast_zero]

/-- The valuation of a root product counts the factors divisible by `p`. -/
theorem val_pr (s : Multiset ℤ) (t : ℤ)
    (h : ∀ x ∈ s, t - x ≠ 0 ∧ (t - x).natAbs < p ^ 2) :
    pr s t ≠ 0 ∧ padicValRat p (pr s t) = ((s.filter fun x => (p : ℤ) ∣ t - x).card : ℤ) := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨one_ne_zero, ?_⟩
    rw [Multiset.filter_zero, Multiset.card_zero, Nat.cast_zero]
    exact padicValRat.one
  | cons x s ih =>
    obtain ⟨h0, h1⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    obtain ⟨hx0, hxb⟩ := h x (Multiset.mem_cons_self x s)
    refine ⟨pr_cons x s t ▸ mul_ne_zero hx0 h0, ?_⟩
    rw [pr_cons, Int.cast_mul, padicValRat.mul (Int.cast_ne_zero.mpr hx0) (Int.cast_ne_zero.mpr h0),
      h1, val_lin p _ hx0 hxb]
    by_cases hd : (p : ℤ) ∣ t - x
    · rw [ite_eq_left hd, Multiset.filter_cons_of_pos (p := fun y => (p : ℤ) ∣ t - y) s hd, Multiset.card_cons, Nat.cast_add,
        Nat.cast_one, add_comm]
    · rw [ite_eq_right hd, Multiset.filter_cons_of_neg (p := fun y => (p : ℤ) ∣ t - y) s hd, zero_add]

omit hp in
/-- Divisibility of `t - x` by `p` is the residue condition `x ≡ k`. -/
theorem filter_dvd_eq (s : Multiset ℤ) (t : ℤ) (k : ℕ) (htk : t % p = k) :
    s.filter (fun x => (p : ℤ) ∣ t - x) = s.filter (fun x => x % (p : ℤ) = k) :=
  Multiset.filter_congr fun x _ => by rw [← htk]; exact Int.modEq_iff_dvd.symm

/-- `v_p(∏ (t - x)) = c_k(s)`. -/
theorem val_pr_rc (s : Multiset ℤ) (t : ℤ) (k : ℕ) (htk : t % p = k)
    (h : ∀ x ∈ s, t - x ≠ 0 ∧ (t - x).natAbs < p ^ 2) :
    pr s t ≠ 0 ∧ padicValRat p (pr s t) = (rc s p k : ℤ) := by
  obtain ⟨h0, h1⟩ := val_pr p s t h
  exact ⟨h0, by rw [h1, filter_dvd_eq p s t k htk]; rfl⟩

/-- `v_p(∑ 1/(t - x)) ≥ -1`. -/
theorem valGE_Ls (s : Multiset ℤ) (t : ℤ) (h : ∀ x ∈ s, t - x ≠ 0 ∧ (t - x).natAbs < p ^ 2) :
    ValGE p (-1) (Ls s t) := by
  induction s using Multiset.induction_on with
  | empty => exact Or.inl Multiset.sum_zero
  | cons x s ih =>
    rw [Ls_cons]
    refine ZetasIrr.Aux.ValGE.add ?_ (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))
    obtain ⟨hx0, hxb⟩ := h x (Multiset.mem_cons_self x s)
    right
    rw [one_div, padicValRat.inv, val_lin p _ hx0 hxb]
    split_ifs <;> norm_num

/-- `v_p(∑ 1/(t - x)) ≥ 0` when no factor is divisible by `p`. -/
theorem valGE_Ls0 (s : Multiset ℤ) (t : ℤ) (h : ∀ x ∈ s, t - x ≠ 0 ∧ (t - x).natAbs < p ^ 2)
    (hnd : ∀ x ∈ s, ¬ (p : ℤ) ∣ t - x) : ValGE p 0 (Ls s t) := by
  induction s using Multiset.induction_on with
  | empty => exact Or.inl Multiset.sum_zero
  | cons x s ih =>
    rw [Ls_cons]
    refine ZetasIrr.Aux.ValGE.add ?_ (ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
      fun y hy => hnd y (Multiset.mem_cons_of_mem hy))
    obtain ⟨hx0, hxb⟩ := h x (Multiset.mem_cons_self x s)
    right
    rw [one_div, padicValRat.inv, val_lin p _ hx0 hxb,
      ite_eq_right (hnd x (Multiset.mem_cons_self x s)), neg_zero]

omit hp in
/-- Residue counts after adding one element. -/
theorem rc_cons (x : ℤ) (s : Multiset ℤ) (a : ℕ) :
    rc (x ::ₘ s) p a = rc s p a + if x % (p : ℤ) = a then 1 else 0 := by
  unfold rc
  by_cases h : x % (p : ℤ) = a
  · rw [Multiset.filter_cons_of_pos (p := fun y => y % (p : ℤ) = a) s h, Multiset.card_cons, ite_eq_left h]
  · rw [Multiset.filter_cons_of_neg (p := fun y => y % (p : ℤ) = a) s h, ite_eq_right h,
      add_zero]

theorem cast_class (x : ℤ) : (x : ZMod p) = (((x % p).toNat : ℕ) : ZMod p) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)),
    ZMod.intCast_mod]

theorem class_lt (x : ℤ) : (x % p).toNat < p := by
  have := Int.emod_lt_of_pos x (by exact_mod_cast hp.out.pos : (0 : ℤ) < p)
  have := Int.emod_nonneg x (by exact_mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)
  omega

/-- The `p`-unit part of a root product modulo `p`, grouped by residue classes. -/
theorem unit_part (s : Multiset ℤ) (t : ℤ) (k : ℕ) (htk : t % p = k) :
    ((pr (s.filter fun x => ¬ x % (p : ℤ) = k) t : ℤ) : ZMod p) =
      ∏ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc s p a := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.filter_zero]
    exact (Int.cast_one).trans (Finset.prod_eq_one fun a _ => pow_zero _).symm
  | cons x s ih =>
    have e1 : ∀ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (x ::ₘ s) p a =
        ((k : ZMod p) - a) ^ rc s p a *
          ((k : ZMod p) - a) ^ (if x % (p : ℤ) = a then 1 else 0) := fun a _ => by
      rw [rc_cons, pow_add]
    rw [Finset.prod_congr rfl e1, Finset.prod_mul_distrib, ← ih]
    have hx : x % (p : ℤ) = ((x % p).toNat : ℕ) :=
      (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero))).symm
    by_cases hxk : x % (p : ℤ) = k
    · rw [Multiset.filter_cons_of_neg (p := fun y => ¬ y % (p : ℤ) = k) s (not_not.mpr hxk), Finset.prod_eq_one, mul_one]
      intro a ha
      rw [ite_eq_right fun h => (Finset.ne_of_mem_erase ha) (by rw [hxk] at h; exact_mod_cast h.symm),
        pow_zero]
    · rw [Multiset.filter_cons_of_pos (p := fun y => ¬ y % (p : ℤ) = k) s hxk, pr_cons, Int.cast_mul, mul_comm,
        Finset.prod_eq_single ((x % p).toNat)]
      · rw [ite_eq_left hx, pow_one, Int.cast_sub, cast_class p t, cast_class p x, htk]
        rfl
      · intro a _ hne
        rw [ite_eq_right fun h => hne (by rw [hx] at h; exact_mod_cast h.symm), pow_zero]
      · intro hn
        exfalso
        rcases Finset.mem_erase.not.mp hn |> not_and_or.mp with h | h
        · exact h fun h' => hxk (by rw [hx, h'])
        · exact h (mem_range.mpr (class_lt p x))

/-- Wilson: `∏_{a ≠ k} (k - a) = -1` in `𝔽_p`. -/
theorem prod_erase_sub (k : ℕ) (hk : k < p) :
    ∏ a ∈ (range p).erase k, ((k : ZMod p) - a) = -1 := by
  rw [← ZMod.prod_Ico_one_prime p]
  have hinj : ∀ a b : ℕ, a < p → b < p → (a : ZMod p) = b → a = b := fun a b ha hb h => by
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  refine Finset.prod_nbij' (fun a => ((k : ZMod p) - a).val) (fun b => ((k : ZMod p) - b).val)
    (fun a ha => ?_) (fun b hb => ?_) (fun a ha => ?_) (fun b hb => ?_) (fun a _ => ?_)
  · obtain ⟨hak, ha⟩ := Finset.mem_erase.mp ha
    refine Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr fun h0 => hak ?_, ZMod.val_lt _⟩
    rw [ZMod.val_eq_zero, sub_eq_zero] at h0
    exact (hinj k a hk (mem_range.mp ha) h0).symm
  · obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
    refine Finset.mem_erase.mpr ⟨fun h => ?_, mem_range.mpr (ZMod.val_lt _)⟩
    have h' := congrArg (fun m : ℕ => (m : ZMod p)) h
    simp only [ZMod.natCast_zmod_val] at h'
    have : ((b : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      rw [Nat.cast_zero]; exact (sub_eq_self.mp h')
    exact absurd (hinj b 0 hb2 hp.out.pos this) (by omega)
  · rw [ZMod.natCast_zmod_val, sub_sub_cancel, ZMod.val_cast_of_lt (mem_range.mp
      (Finset.mem_of_mem_erase ha))]
  · rw [ZMod.natCast_zmod_val, sub_sub_cancel, ZMod.val_cast_of_lt (Finset.mem_Ico.mp hb).2]
  · rw [ZMod.natCast_zmod_val]

/-- The residue counts add up to the cardinality. -/
theorem sum_rc (s : Multiset ℤ) : ∑ a ∈ range p, rc s p a = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => exact Finset.sum_eq_zero fun a _ => by rw [rc, Multiset.filter_zero]; rfl
  | cons x s ih =>
    have hx : x % (p : ℤ) = ((x % p).toNat : ℕ) :=
      (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero))).symm
    rw [Finset.sum_congr rfl fun a _ => rc_cons p x s a, Finset.sum_add_distrib, ih,
      Finset.sum_eq_single ((x % p).toNat), ite_eq_left hx, Multiset.card_cons]
    · intro a _ hne
      exact ite_eq_right fun h => hne (by rw [hx] at h; exact_mod_cast h.symm)
    · exact fun h => absurd (mem_range.mpr (class_lt p x)) h

omit hp in
/-- Removing the point `t` from `s` lowers the count of its class by its multiplicity. -/
theorem rc_filter_ne (s : Multiset ℤ) (t : ℤ) (k : ℕ) (htk : t % p = k) :
    rc (s.filter fun x => x ≠ t) p k + s.count t = rc s p k := by
  unfold rc
  rw [Multiset.filter_filter, Multiset.count_eq_card_filter_eq, ← Multiset.card_add]
  congr 1
  conv_rhs => rw [← Multiset.filter_add_not (fun x => x ≠ t) (s.filter fun x => x % (p : ℤ) = k)]
  rw [Multiset.filter_filter, Multiset.filter_filter]
  congr 1
  · exact Multiset.filter_congr fun x _ => and_comm
  · exact Multiset.filter_congr fun x _ => by
      constructor
      · rintro rfl; exact ⟨not_not.mpr rfl, htk⟩
      · rintro ⟨h, -⟩; exact (not_not.mp h).symm

omit hp in
/-- Removing the point `t` does not change the other classes. -/
theorem rc_filter_ne' (s : Multiset ℤ) (t : ℤ) (k a : ℕ) (htk : t % p = k) (hak : a ≠ k) :
    rc (s.filter fun x => x ≠ t) p a = rc s p a := by
  unfold rc
  rw [Multiset.filter_filter]
  congr 1
  exact Multiset.filter_congr fun x _ => ⟨fun h => h.1, fun h => ⟨h, fun hxt => hak (by
    rw [hxt, htk] at h; exact_mod_cast h.symm)⟩⟩

end Pfq54.RA
