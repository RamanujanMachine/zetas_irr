/-
# Auxiliary lemmas for the profile `φ` (sorry-free)

`φ` only depends on the floors `⌊dx⌋`, `8 ≤ d ≤ 19`; it is `1`-periodic; and a finite check on
the subdivision of an interval at the points `i/d` determines it on the whole interval.
-/
import pairing_bound

open Finset

noncomputable section

namespace Pfq54.PA

open Pfq54

/-- The relevant dilations. -/
def dl : List ℤ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

theorem phi_eq_foldr (x : ℚ) :
    phi x = pairings.foldr (fun LD m => max m (BP.rowVal LD x)) 0 := rfl

theorem sum_shift (l : List ℤ) (x y : ℚ) (k : ℤ)
    (h : ∀ d ∈ l, ⌊(d : ℚ) * x⌋ = ⌊(d : ℚ) * y⌋ + d * k) :
    (l.map fun d : ℤ => ⌊(d : ℚ) * x⌋).sum = (l.map fun d : ℤ => ⌊(d : ℚ) * y⌋).sum + l.sum * k := by
  induction l with
  | nil => rw [List.map_nil, List.map_nil, List.sum_nil, zero_mul, add_zero]
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.sum_cons,
      h a List.mem_cons_self, ih fun d hd => h d (List.mem_cons_of_mem a hd), add_mul]
    abel

theorem coe_map (l : List ℤ) (x : ℚ) :
    (List.map (fun d => ⌊d * x⌋) (do let a ← l; pure (a : ℚ))) =
      l.map (fun d : ℤ => ⌊(d : ℚ) * x⌋) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ← ih]
    rfl

/-- `φ` only sees the floors `⌊dx⌋ - dk`. -/
theorem phi_shift (x y : ℚ) (k : ℤ) (h : ∀ d ∈ dl, ⌊(d : ℚ) * x⌋ = ⌊(d : ℚ) * y⌋ + d * k) :
    phi x = phi y := by
  have h15 := h 15 (by decide)
  have h10 := h 10 (by decide)
  rw [Int.cast_ofNat] at h15 h10
  have hc : cfun x = cfun y := by
    unfold cfun
    rw [h15, h10]
    omega
  have hsub : ∀ LD ∈ pairings, (∀ d ∈ LD.1, d ∈ dl) ∧ (∀ d ∈ LD.2, d ∈ dl) ∧
      LD.1.sum = LD.2.sum := by decide
  rw [phi_eq_foldr, phi_eq_foldr]
  refine List.foldr_ext _ _ _ fun LD hLD m => ?_
  obtain ⟨h1, h2, h3⟩ := hsub LD hLD
  unfold BP.rowVal
  rw [coe_map, coe_map, coe_map, coe_map, hc, sum_shift LD.2 x y k fun d hd => h d (h2 d hd),
    sum_shift LD.1 x y k fun d hd => h d (h1 d hd), h3]
  congr 1
  abel

/-- Periodicity `φ(x + k) = φ(x)`. -/
theorem phi_add_int (x : ℚ) (k : ℤ) : phi ((k : ℚ) + x) = phi x := by
  refine phi_shift _ _ k fun d _ => ?_
  rw [mul_add, ← Int.cast_mul, Int.floor_intCast_add, add_comm, mul_comm]

/-- `φ` as a function of the floor vector. -/
def PhiF (F : ℤ → ℤ) : ℤ :=
  pairings.foldr (fun LD m => max m (2 * F 15 - 3 * F 10 - (LD.2.map F).sum + (LD.1.map F).sum)) 0

theorem phi_eq_PhiF (x : ℚ) : phi x = PhiF fun d => ⌊(d : ℚ) * x⌋ := by
  rw [phi_eq_foldr]
  refine List.foldr_ext _ _ _ fun LD _ m => ?_
  unfold BP.rowVal cfun
  rw [coe_map, coe_map]
  beta_reduce
  rw [Int.cast_ofNat, Int.cast_ofNat]

theorem PhiF_congr (F G : ℤ → ℤ) (h : ∀ d ∈ dl, F d = G d) : PhiF F = PhiF G := by
  have hsub : ∀ LD ∈ pairings, (∀ d ∈ LD.1, d ∈ dl) ∧ (∀ d ∈ LD.2, d ∈ dl) := by decide
  unfold PhiF
  refine List.foldr_ext _ _ _ fun LD hLD m => ?_
  rw [h 15 (by decide), h 10 (by decide), List.map_congr_left fun d hd => h d ((hsub LD hLD).2 d hd),
    List.map_congr_left fun d hd => h d ((hsub LD hLD).1 d hd)]

/-- `lcm(8, …, 19)`. -/
def Lc : ℤ := 232792560

/-- The subdivision points `i/d` (`8 ≤ d ≤ 19`, `0 ≤ i ≤ d`), scaled by `Lc`, in increasing
order. -/
def grid : List ℤ :=
  [0, 12252240, 12932920, 13693680, 14549535, 15519504, 16628040, 17907120, 19399380, 21162960,
   23279256, 24504480, 25865840, 27387360, 29099070, 31039008, 33256080, 35814240, 36756720,
   38798760, 41081040, 42325920, 43648605, 46558512, 49008960, 49884120, 51731680, 53721360,
   54774720, 58198140, 61261200, 62078016, 63488880, 64664600, 66512160, 68468400, 69837768,
   71628480, 72747675, 73513440, 77597520, 82162080, 83140200, 84651840, 85765680, 87297210,
   89535600, 90530440, 93117024, 95855760, 96996900, 98017920, 99768240, 101846745, 103463360,
   105814800, 107442720, 108636528, 109549440, 110270160, 116396280, 122522400, 123243120,
   124156032, 125349840, 126977760, 129329200, 130945815, 133024320, 134774640, 135795660,
   136936800, 139675536, 142262120, 143256960, 145495350, 147026880, 148140720, 149652360,
   150630480, 155195040, 159279120, 160044885, 161164080, 162954792, 164324160, 166280400,
   168127960, 169303680, 170714544, 171531360, 174594420, 178017840, 179071200, 181060880,
   182908440, 183783600, 186234048, 189143955, 190466640, 191711520, 193993800, 196035840,
   196978320, 199536480, 201753552, 203693490, 205405200, 206926720, 208288080, 209513304,
   211629600, 213393180, 214885440, 216164520, 217273056, 218243025, 219098880, 219859640,
   220540320, 232792560]

/-- `⌊d m⌋` at the midpoint `m` of `[lo/Lc, hi/Lc)`. -/
def flv (lo hi d : ℤ) : ℤ := d * (lo + hi) / (2 * Lc)

/-- The midpoint floors are valid on all of `[lo/Lc, hi/Lc)`. -/
def okF (lo hi : ℤ) : Bool :=
  dl.all fun d => decide (flv lo hi d * Lc ≤ d * lo) && decide (d * hi ≤ (flv lo hi d + 1) * Lc)

/-- One piece `[lo/Lc, hi/Lc)`. -/
def pc (t : (ℤ → ℤ) → Bool) (lo hi : ℤ) : Bool :=
  if lo < hi then okF lo hi && t (flv lo hi) else true

/-- The check of `t` on the pieces of `[lo/Lc, b/Lc)` cut at the points of the list. -/
def chkL (t : (ℤ → ℤ) → Bool) : List ℤ → ℤ → ℤ → Bool
  | [], lo, b => pc t lo b
  | q :: qs, lo, b =>
    if q ≤ lo then chkL t qs lo b else if b ≤ q then pc t lo b else pc t lo q && chkL t qs q b

theorem Lc_pos : (0 : ℚ) < (Lc : ℚ) := by unfold Lc; norm_num

theorem floors_of_okF (lo hi : ℤ) (h : okF lo hi = true) (x : ℚ) (h1 : (lo : ℚ) / Lc ≤ x)
    (h2 : x < (hi : ℚ) / Lc) : ∀ d ∈ dl, ⌊(d : ℚ) * x⌋ = flv lo hi d := by
  intro d hd
  have hpos : ∀ d ∈ dl, (0 : ℤ) < d := by decide
  have hd0 : (0 : ℚ) < d := Int.cast_pos.mpr (hpos d hd)
  have hh := List.all_eq_true.mp h d hd
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hh
  have e1 : ((flv lo hi d : ℤ) : ℚ) * Lc ≤ d * lo := by exact_mod_cast hh.1
  have e2 : (d : ℚ) * hi ≤ ((flv lo hi d : ℤ) + 1) * Lc := by exact_mod_cast hh.2
  rw [Int.floor_eq_iff]
  constructor
  · calc ((flv lo hi d : ℤ) : ℚ) ≤ d * lo / Lc := (le_div_iff₀ Lc_pos).mpr e1
      _ = d * ((lo : ℚ) / Lc) := mul_div_assoc _ _ _
      _ ≤ d * x := mul_le_mul_of_nonneg_left h1 hd0.le
  · calc (d : ℚ) * x < d * ((hi : ℚ) / Lc) := mul_lt_mul_of_pos_left h2 hd0
      _ = d * hi / Lc := (mul_div_assoc _ _ _).symm
      _ ≤ _ := (div_le_iff₀ Lc_pos).mpr e2

theorem pc_sound (t : (ℤ → ℤ) → Bool) (ht : ∀ F G, (∀ d ∈ dl, F d = G d) → t F = t G)
    (lo hi : ℤ) (h : pc t lo hi = true) (x : ℚ) (h1 : (lo : ℚ) / Lc ≤ x)
    (h2 : x < (hi : ℚ) / Lc) : t (fun d => ⌊(d : ℚ) * x⌋) = true := by
  have hc : lo < hi := by
    have : (lo : ℚ) / Lc < (hi : ℚ) / Lc := h1.trans_lt h2
    exact_mod_cast (div_lt_div_iff_of_pos_right Lc_pos).mp this
  unfold pc at h
  rw [ite_eq_left hc, Bool.and_eq_true] at h
  rw [ht _ _ (floors_of_okF lo hi h.1 x h1 h2)]
  exact h.2

theorem chkL_sound (t : (ℤ → ℤ) → Bool) (ht : ∀ F G, (∀ d ∈ dl, F d = G d) → t F = t G)
    (l : List ℤ) : ∀ (lo b : ℤ) (x : ℚ), chkL t l lo b = true → (lo : ℚ) / Lc ≤ x →
      x < (b : ℚ) / Lc → t (fun d => ⌊(d : ℚ) * x⌋) = true := by
  induction l with
  | nil => exact fun lo b x h h1 h2 => pc_sound t ht lo b h x h1 h2
  | cons q qs ih =>
    intro lo b x h h1 h2
    unfold chkL at h
    by_cases hq : q ≤ lo
    · rw [ite_eq_left hq] at h
      exact ih lo b x h h1 h2
    rw [ite_eq_right hq] at h
    by_cases hb : b ≤ q
    · rw [ite_eq_left hb] at h
      exact pc_sound t ht lo b h x h1 h2
    rw [ite_eq_right hb, Bool.and_eq_true] at h
    rcases lt_or_ge x ((q : ℚ) / Lc) with h3 | h3
    · exact pc_sound t ht lo q h.1 x h1 h3
    · exact ih q b x h.2 h3 h2

/-- The scaled endpoint `a Lc`. -/
def sc (a : ℚ) : ℤ := a.num * Lc / a.den

/-- The check of `t` on the open interval `(a, b)`. -/
def rowI (t : (ℤ → ℤ) → Bool) (a b : ℚ) : Bool :=
  decide (sc a * a.den = a.num * Lc) && decide (sc b * b.den = b.num * Lc) &&
    chkL t grid (sc a) (sc b)

theorem sc_eq (a : ℚ) (h : sc a * a.den = a.num * Lc) : (sc a : ℚ) / Lc = a := by
  have hden : (0 : ℚ) < a.den := by exact_mod_cast a.den_pos
  calc (sc a : ℚ) / Lc = (a.num : ℚ) / a.den := by
        rw [div_eq_div_iff Lc_pos.ne' hden.ne']; exact_mod_cast h
    _ = a := Rat.num_div_den a

theorem rowI_sound (t : (ℤ → ℤ) → Bool) (ht : ∀ F G, (∀ d ∈ dl, F d = G d) → t F = t G)
    (a b : ℚ) (h : rowI t a b = true) (x : ℚ) (h1 : a < x) (h2 : x < b) :
    t (fun d => ⌊(d : ℚ) * x⌋) = true := by
  unfold rowI at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  obtain ⟨⟨ha, hb⟩, hc⟩ := h
  exact chkL_sound t ht _ _ _ x hc (by rw [sc_eq a ha]; exact h1.le) (by rw [sc_eq b hb]; exact h2)

end Pfq54.PA
