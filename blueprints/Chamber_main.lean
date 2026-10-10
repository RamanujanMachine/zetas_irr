/-
# Chamber certificate, part 4: assembly

`chamber_core`: for `N ≥ 31`, a prime `p ≤ 29N + 1` with `p² > 30N + 10` not dividing the boundary
product, the point `x = N/p` (or its fractional part when `x > 1`) lies in a chamber `i`, and
`E₃₄(N,p) ≤ e₀(i) + 𝟙_{x > 1/19}` (resp. `≤ e₁(i) + 1`), where `(e₀(i), e₁(i))` is the table row
containing the chamber.  The identification with `e₃₄` is done in `log_Delta_le.lean`.
-/
import Chamber_certAll

namespace ZetasIrr.CH
open ZetasIrr

/-- `a/b` as a rational. -/
def rat (ab : ℕ × ℕ) : ℚ := (ab.1 : ℚ) / ab.2

/-- A row of `ptableN` as a row of `profileTable`. -/
def toRow (q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℚ × ℚ × ℕ × ℕ :=
  ((q.1 : ℚ) / q.2.1, (q.2.2.1 : ℚ) / q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2)

/-- `𝟙_{x > 1/19}` on chamber `i`. -/
def flag (i : ℕ) : ℕ := if (fareyL i).2 ≤ 19 * (fareyL i).1 then 1 else 0

/-! ### The facts recorded in `chamberOK` -/

theorem chamber_facts (i : ℕ) (hi : i < 270) :
    (0 < (fareyL i).2 ∧ 0 < (fareyL (i + 1)).2 ∧ (fareyL i).2 ≤ 29 ∧ (fareyL (i + 1)).2 ≤ 29 ∧
      (fareyL i).1 * (fareyL (i + 1)).2 < (fareyL (i + 1)).1 * (fareyL i).2) ∧
    certI (wOf (fareyL i).1 (fareyL i).2) ≤ ((rowN i).2.2.2.2.1 : ℤ) + flag i ∧
    certP (wOf (fareyL i).1 (fareyL i).2) ≤ ((rowN i).2.2.2.2.2 : ℤ) + 1 ∧
    (0 < (rowN i).2.1 ∧ 0 < (rowN i).2.2.2.1 ∧ (rowN i).1 * (fareyL i).2 ≤ (fareyL i).1 * (rowN i).2.1 ∧
      (fareyL (i + 1)).1 * (rowN i).2.2.2.1 ≤ (rowN i).2.2.1 * (fareyL (i + 1)).2) ∧
    (∀ q ∈ ptableN, q = rowN i ∨ (0 < q.2.2.2.1 ∧ q.2.2.1 * (fareyL i).2 ≤ (fareyL i).1 * q.2.2.2.1) ∨
      (0 < q.2.1 ∧ (fareyL (i + 1)).1 * q.2.1 ≤ q.1 * (fareyL (i + 1)).2)) ∧
    noFracN (fareyL i).1 (fareyL i).2 (fareyL (i + 1)).1 (fareyL (i + 1)).2 = true ∧
    ((fareyL i).2 ≤ 19 * (fareyL i).1 ∨ 19 * (fareyL (i + 1)).1 ≤ (fareyL (i + 1)).2) ∧
    rowN i ∈ ptableN := by
  have h := chambers_ok i hi
  unfold chamberOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  unfold flag
  exact ⟨h1, by split_ifs with hf <;> simp only [hf, ite_true, ite_false, Nat.cast_one,
    Nat.cast_zero] at h2 ⊢ <;> exact h2, h3, h4, h5, h6, h7, h8⟩

theorem den_div_le (a b : ℕ) (hb : 0 < b) : ((a : ℚ) / b).den ≤ b := by
  have h := Rat.den_dvd (a : ℤ) (b : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  exact Nat.le_of_dvd hb (Int.natCast_dvd_natCast.mp h)

theorem ptable_den : ∀ q ∈ ptableN, (toRow q).1.den ≤ 29 ∧ (toRow q).2.1.den ≤ 29 := by
  have h : ∀ q ∈ ptableN, 0 < q.2.1 ∧ q.2.1 ≤ 29 ∧ 0 < q.2.2.2.1 ∧ q.2.2.2.1 ≤ 29 := by
    decide +kernel
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := h q hq
  exact ⟨(den_div_le _ _ h1).trans h2, (den_div_le _ _ h3).trans h4⟩

/-! ### Chambers cover the non-wall points -/

theorem rat_fareyL_zero : rat (fareyL 0) = 0 := by rw [farey_first]; unfold rat; norm_num
theorem rat_fareyL_last : rat (fareyL 270) = 1 := by rw [farey_last]; unfold rat; norm_num

theorem exists_chamber (x : ℚ) (h0 : 0 < x) (h1 : x < 1) (hw : ∀ i ≤ 270, x ≠ rat (fareyL i)) :
    ∃ i < 270, rat (fareyL i) < x ∧ x < rat (fareyL (i + 1)) := by
  classical
  have hP : ∃ i, x < rat (fareyL i) := ⟨270, by rw [rat_fareyL_last]; exact h1⟩
  let i := Nat.find hP
  have hi : x < rat (fareyL i) := Nat.find_spec hP
  have hi0 : i ≠ 0 := fun h => by
    rw [h, rat_fareyL_zero] at hi; exact absurd (hi.trans h0) (lt_irrefl _)
  have hmin : ¬ x < rat (fareyL (i - 1)) := Nat.find_min hP (by omega)
  have hle : i ≤ 270 := Nat.find_min' hP (by rw [rat_fareyL_last]; exact h1)
  refine ⟨i - 1, by omega, lt_of_le_of_ne (not_lt.mp hmin) (hw _ (by omega)).symm, ?_⟩
  rw [show i - 1 + 1 = i by omega]; exact hi

/-- `⌊c x⌋` is constant on a chamber. -/
theorem floor_chamber (i : ℕ) (hi : i < 270) (x : ℚ) (hl : rat (fareyL i) < x)
    (hr : x < rat (fareyL (i + 1))) (c : ℕ) (hc1 : 1 ≤ c) (hc : c ≤ 29) :
    ⌊(c : ℚ) * x⌋ = ((c * (fareyL i).1 / (fareyL i).2 : ℕ) : ℤ) := by
  obtain ⟨⟨hb, hb', -, -, -⟩, -, -, -, -, hnf, -, -⟩ := chamber_facts i hi
  unfold noFracN at hnf
  rw [List.all_eq_true] at hnf
  have h := hnf (c - 1) (List.mem_range.mpr (by omega))
  rw [decide_eq_true_eq, show c - 1 + 1 = c by omega] at h
  have hc0 : (0 : ℚ) < c := by exact_mod_cast hc1
  have hb0 : (0 : ℚ) < (fareyL i).2 := by exact_mod_cast hb
  have hb0' : (0 : ℚ) < (fareyL (i + 1)).2 := by exact_mod_cast hb'
  have hfl : ⌊(c : ℚ) * rat (fareyL i)⌋ = ((c * (fareyL i).1 / (fareyL i).2 : ℕ) : ℤ) := by
    rw [Int.natCast_ediv, ← Rat.floor_intCast_div_natCast]; unfold rat; congr 1; push_cast; ring
  have hmono : ⌊(c : ℚ) * rat (fareyL i)⌋ ≤ ⌊(c : ℚ) * x⌋ :=
    Int.floor_le_floor (by nlinarith)
  by_contra hne
  have hlt : ⌊(c : ℚ) * rat (fareyL i)⌋ + 1 ≤ ⌊(c : ℚ) * x⌋ := by omega
  apply h
  have key : ((c * (fareyL i).1 / (fareyL i).2 + 1 : ℕ) : ℚ) < (c : ℚ) * rat (fareyL (i + 1)) := by
    calc ((c * (fareyL i).1 / (fareyL i).2 + 1 : ℕ) : ℚ)
        = ((⌊(c : ℚ) * rat (fareyL i)⌋ + 1 : ℤ) : ℚ) := by
          rw [hfl, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
      _ ≤ (⌊(c : ℚ) * x⌋ : ℚ) := by exact_mod_cast hlt
      _ ≤ c * x := Int.floor_le _
      _ < c * rat (fareyL (i + 1)) := by nlinarith
  unfold rat at key
  rw [mul_div_assoc', lt_div_iff₀ hb0'] at key
  have key' : ((c * (fareyL i).1 / (fareyL i).2 + 1 : ℕ) : ℚ) * ((fareyL (i + 1)).2 : ℚ) <
      ((c * (fareyL (i + 1)).1 : ℕ) : ℚ) := by push_cast at key ⊢; exact key
  exact_mod_cast key'

/-! ### The data of `N/p` on a chamber -/

theorem data_eq {N p : ℕ} (hp : 0 < p) (hNB : NB N p) (i : ℕ) (hi : i < 270)
    (hl : rat (fareyL i) < (N : ℚ) / p) (hr : (N : ℚ) / p < rat (fareyL (i + 1))) :
    ∀ c : ℤ, |c| ≤ 29 → (c * N) / p = wOf (fareyL i).1 (fareyL i).2 c := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have key : ∀ c : ℕ, 1 ≤ c → c ≤ 29 →
      ((c : ℤ) * N) / p = ((c : ℤ) * (fareyL i).1) / (fareyL i).2 := by
    intro c hc1 hc
    have h1 : ((c : ℤ) * N) / p = ⌊(c : ℚ) * ((N : ℚ) / p)⌋ := by
      rw [← Rat.floor_intCast_div_natCast]; congr 1; push_cast; ring
    rw [h1, floor_chamber i hi _ hl hr c hc1 hc]
    push_cast
    rfl
  intro c hc
  have hc' := abs_le.mp hc
  unfold wOf
  split_ifs with h1 h2
  · have := key c.toNat (by omega) (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at this
    exact this
  · subst h2; rw [zero_mul, Int.zero_ediv]
  · have := key (-c).toNat (by omega) (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at this
    rw [← this]
    have hne : ((-c) * (N : ℤ)) % p ≠ 0 := by
      have := hNB (-c) 0 (by omega) (by rw [abs_neg]; exact hc) (by norm_num)
      rwa [add_zero] at this
    rw [← ediv_pred _ _ hp' hne, show (-c) * (N : ℤ) - 1 = -(c * N) - 1 by ring,
      ediv_neg_pred _ _ hp']
    ring

/-! ### Non-boundary -/

theorem NB_of_boundary {N p : ℕ}
    (hnd : ¬ (p : ℤ) ∣ ∏ d ∈ Finset.Icc (1 : ℤ) 29, ∏ r ∈ Finset.Icc (-10 : ℤ) 10, (d * N + r)) :
    NB N p := by
  intro c e hc0 hc he h
  apply hnd
  have hc' := abs_le.mp hc
  have he' := abs_le.mp he
  have hd : (p : ℤ) ∣ c * N + e := Int.dvd_of_emod_eq_zero h
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hd' : (p : ℤ) ∣ (-c) * N + (-e) := by
      rw [show (-c) * (N : ℤ) + (-e) = -(c * N + e) by ring]; exact hd.neg_right
    exact hd'.trans ((Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
  · exact hd.trans ((Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))

/-- `N/p` is not a fraction with denominator `≤ 29`. -/
theorem not_wall {N p : ℕ} (hp : p.Prime) (hp29 : 29 < p) (hNB : NB N p) (q : ℚ)
    (hq : q.den ≤ 29) : (N : ℚ) / p ≠ q := by
  intro h
  have hpN : ¬ (p : ℤ) ∣ N := fun hd => hNB 1 0 one_ne_zero (by norm_num) (by norm_num)
    (by rw [one_mul, add_zero]; exact Int.emod_eq_zero_of_dvd hd)
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have h2 : (N : ℚ) * q.den = q.num * p := by
    have := Rat.num_div_den q
    rw [← this] at h
    field_simp at h
    linarith
  have h3 : (N : ℤ) * q.den = q.num * p := by exact_mod_cast h2
  have h4 : (p : ℤ) ∣ (N : ℤ) * q.den := ⟨q.num, by rw [h3]; ring⟩
  rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_or_dvd h4 with h5 | h5
  · exact hpN h5
  · have := Int.le_of_dvd (by exact_mod_cast q.den_pos) h5
    omega

theorem not_wall_real {N p : ℕ} (hp : p.Prime) (hp29 : 29 < p) (hNB : NB N p) (q : ℚ)
    (hq : q.den ≤ 29) : (N : ℝ) / p ≠ (q : ℝ) := by
  intro h
  apply not_wall hp hp29 hNB q hq
  have : (((N : ℚ) / p : ℚ) : ℝ) = (q : ℝ) := by push_cast; exact h
  exact_mod_cast this

theorem nat_decomp (N p : ℕ) :
    (N : ℤ) = ((N % p : ℕ) : ℤ) + (p : ℤ) * ((N / p : ℕ) : ℤ) := by
  exact_mod_cast (Nat.mod_add_div N p).symm

theorem NB_mod {N p : ℕ} (hp : 0 < p) (hNB : NB N p) : NB ((N % p : ℕ) : ℤ) (p : ℤ) := by
  intro c e hc0 hc he
  have := hNB c e hc0 hc he
  rw [nat_decomp N p, show c * (((N % p : ℕ) : ℤ) + (p : ℤ) * ((N / p : ℕ) : ℤ)) + e =
    (c * ((N % p : ℕ) : ℤ) + e) + (p : ℤ) * (c * ((N / p : ℕ) : ℤ)) by ring,
    Int.add_mul_emod_self_left] at this
  exact this

theorem mod_ne_zero {N p : ℕ} (hNB : NB N p) : N % p ≠ 0 := fun h =>
  hNB 1 0 one_ne_zero (by norm_num) (by norm_num) (by rw [one_mul, add_zero]; exact_mod_cast h)

theorem fract_div (N p : ℕ) (hp : 0 < p) :
    Int.fract ((N : ℝ) / p) = ((N % p : ℕ) : ℝ) / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Int.fract_eq_iff]
  refine ⟨by positivity, by rw [div_lt_one hp']; exact_mod_cast Nat.mod_lt N hp, (N / p : ℕ), ?_⟩
  have hN : (N : ℝ) = ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm
  rw [div_sub_div_same, hN, add_sub_cancel_left, mul_div_cancel_left₀ _ hp'.ne']
  push_cast; rfl

/-! ### The chamber facts in rational form -/

theorem row_mem (i : ℕ) (hi : i < 270) : toRow (rowN i) ∈ ptableN.map toRow :=
  List.mem_map_of_mem (chamber_facts i hi).2.2.2.2.2.2.2

theorem row_contains (i : ℕ) (hi : i < 270) :
    (toRow (rowN i)).1 ≤ rat (fareyL i) ∧ rat (fareyL (i + 1)) ≤ (toRow (rowN i)).2.1 := by
  obtain ⟨⟨hb, hb', -, -, -⟩, -, -, ⟨h1, h2, h3, h4⟩, -, -, -, -⟩ := chamber_facts i hi
  unfold toRow rat
  constructor
  · rw [div_le_div_iff₀ (by exact_mod_cast h1) (by exact_mod_cast hb)]; exact_mod_cast h3
  · rw [div_le_div_iff₀ (by exact_mod_cast hb') (by exact_mod_cast h2)]; exact_mod_cast h4

theorem row_disjoint (i : ℕ) (hi : i < 270) :
    ∀ row' ∈ ptableN.map toRow, row' = toRow (rowN i) ∨ row'.2.1 ≤ rat (fareyL i) ∨
      rat (fareyL (i + 1)) ≤ row'.1 := by
  obtain ⟨⟨hb, hb', -, -, -⟩, -, -, -, h5, -, -, -⟩ := chamber_facts i hi
  intro row' hrow'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrow'
  rcases h5 q hq with h | ⟨hd, h⟩ | ⟨hd, h⟩
  · exact Or.inl (by rw [h])
  · right; left
    unfold toRow rat
    rw [div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast hb)]; exact_mod_cast h
  · right; right
    unfold toRow rat
    rw [div_le_div_iff₀ (by exact_mod_cast hb') (by exact_mod_cast hd)]; exact_mod_cast h

/-- The indicator `𝟙_{x > 1/19}` on chamber `i`. -/
theorem flag_spec (i : ℕ) (hi : i < 270) :
    (flag i = 1 ∧ (1 : ℚ) / 19 ≤ rat (fareyL i)) ∨
      (flag i = 0 ∧ rat (fareyL (i + 1)) ≤ 1 / 19) := by
  obtain ⟨⟨hb, hb', -, -, -⟩, -, -, -, -, -, h7, -⟩ := chamber_facts i hi
  have hb0 : (0 : ℚ) < (fareyL i).2 := by exact_mod_cast hb
  have hb0' : (0 : ℚ) < (fareyL (i + 1)).2 := by exact_mod_cast hb'
  unfold flag rat
  by_cases h : (fareyL i).2 ≤ 19 * (fareyL i).1
  · left
    refine ⟨ite_eq_left h, ?_⟩
    rw [div_le_div_iff₀ (by norm_num) hb0]
    exact_mod_cast (by omega : 1 * (fareyL i).2 ≤ (fareyL i).1 * 19)
  · right
    refine ⟨ite_eq_right h, ?_⟩
    rw [div_le_div_iff₀ hb0' (by norm_num)]
    have := h7.resolve_left h
    exact_mod_cast (by omega : (fareyL (i + 1)).1 * 19 ≤ 1 * (fareyL (i + 1)).2)

/-! ### The core statement -/

theorem chamber_core {N p : ℕ} (hN : 31 ≤ N) (hp : p.Prime) (hsq : 30 * N + 10 < p ^ 2)
    (hnd : ¬ (p : ℤ) ∣ ∏ d ∈ Finset.Icc (1 : ℤ) 29, ∏ r ∈ Finset.Icc (-10 : ℤ) 10, (d * N + r)) :
    (N < p → ∃ i < 270, rat (fareyL i) < (N : ℚ) / p ∧ (N : ℚ) / p < rat (fareyL (i + 1)) ∧
      (E34 N p).toNat ≤ (rowN i).2.2.2.2.1 + flag i) ∧
    (p < N → ∃ i < 270, rat (fareyL i) < ((N % p : ℕ) : ℚ) / p ∧
      ((N % p : ℕ) : ℚ) / p < rat (fareyL (i + 1)) ∧ (E34 N p).toNat ≤ (rowN i).2.2.2.2.2 + 1) := by
  have hNB := NB_of_boundary (N := N) (p := p) hnd
  have hp29 : 29 < p := by nlinarith
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hwall : ∀ j ≤ 270, (rat (fareyL j)).den ≤ 29 := fun j hj => by
    unfold rat
    rcases Nat.lt_or_ge j 270 with h | h
    · exact (den_div_le _ _ (chamber_facts j h).1.1).trans (chamber_facts j h).1.2.2.1
    · rw [show j = 270 by omega, farey_last]; norm_num
  constructor
  · intro hNp
    obtain ⟨i, hi, hl, hr⟩ := exists_chamber ((N : ℚ) / p) (by positivity)
      (by rw [div_lt_one hp0]; exact_mod_cast hNp) fun j hj => not_wall hp hp29 hNB _ (hwall j hj)
    refine ⟨i, hi, hl, hr, ?_⟩
    have h1 := E34_le_certI hp (by omega) (by omega) hsq hNB (data_eq hp.pos hNB i hi hl hr)
    have h2 := (chamber_facts i hi).2.1
    omega
  · intro hpN
    have hp' : 0 < p := hp.pos
    have hNB' := NB_mod hp' hNB
    have hmod0 := mod_ne_zero hNB
    obtain ⟨i, hi, hl, hr⟩ := exists_chamber (((N % p : ℕ) : ℚ) / p) (by
        have : (0 : ℚ) < (N % p : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hmod0
        positivity)
      (by rw [div_lt_one hp0]; exact_mod_cast Nat.mod_lt N hp')
      fun j hj => not_wall hp hp29 hNB' _ (hwall j hj)
    refine ⟨i, hi, hl, hr, ?_⟩
    have hdata := data_eq hp' hNB' i hi hl hr
    have hv : ∀ c : ℤ, |c| ≤ 29 → (c * N) / p =
        ((N / p : ℕ) : ℤ) * c + wOf (fareyL i).1 (fareyL i).2 c := by
      intro c hc
      rw [← hdata c hc, nat_decomp N p, show c * (((N % p : ℕ) : ℤ) + (p : ℤ) * ((N / p : ℕ) : ℤ)) =
        c * ((N % p : ℕ) : ℤ) + (((N / p : ℕ) : ℤ) * c) * p by ring,
        Int.add_mul_ediv_right _ _ (by exact_mod_cast hp'.ne')]
      ring
    have h1 := E34_le_certP hp (by omega) hpN hsq hNB _ hv
    have h2 := (chamber_facts i hi).2.2.1
    omega

end ZetasIrr.CH
