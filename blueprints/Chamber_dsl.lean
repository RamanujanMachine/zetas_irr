/-
# Chamber certificate, part 1: step functions of `k` and their jump candidates

For `p > √(30N+10)` every quantity entering `E₃₄(N,p)` is an integer combination of floors
`⌊(k + cN + d)/p⌋` and indicators `[k + cN + d ≥ p]`, `[cN + d - k ≥ p]`.  Such a function of `k`
can only change at `k ≡ -(cN + d) (mod p)`; at those *candidates* `k = -(cN + d) + jp` its value
is an explicit expression in `j` and the chamber data `v c = ⌊cN/p⌋`, provided `p` divides none of
`cN + e` with `|c| ≤ 29`, `|e| ≤ 10` (the non-boundary condition `NB`).

* `Term`, `evalE`: the expressions and their value at `k`.
* `jump`: a change of value forces a candidate class.
* `evalCandE`: the symbolic value at a candidate, `eval_cand`.
* `boundE`: the minimum over the finitely many in-range candidates of a region, and
  `region_ge_bound`: it is a lower bound on the whole region.
* `boundP`, `region_ge_boundP`: the version without indicators (used for `N/p > 1`).
-/
import ZetasAux

namespace ZetasIrr.CH

/-! ### Integer division helpers -/

theorem emod_add_mul_ediv (m p : ℤ) : m % p + p * (m / p) = m := by
  rw [mul_comm]; exact Int.emod_add_ediv_mul m p

theorem ediv_pred (m p : ℤ) (hp : 0 < p) (h : m % p ≠ 0) : (m - 1) / p = m / p := by
  have h1 := emod_add_mul_ediv m p
  have h2 := Int.emod_nonneg m hp.ne'
  have h3 := Int.emod_lt_of_pos m hp
  exact ((Int.ediv_emod_unique (r := m % p - 1) (q := m / p) hp).mpr
    ⟨by omega, by omega, by omega⟩).1

theorem ediv_neg_pred (m p : ℤ) (hp : 0 < p) : (-m - 1) / p = -(m / p) - 1 := by
  have h1 := emod_add_mul_ediv m p
  have h2 := Int.emod_nonneg m hp.ne'
  have h3 := Int.emod_lt_of_pos m hp
  exact ((Int.ediv_emod_unique (r := p - 1 - m % p) (q := -(m / p) - 1) hp).mpr
    ⟨by linear_combination (-1 : ℤ) * h1, by omega, by omega⟩).1

theorem ediv_small (e p : ℤ) (hp : 0 < p) (h1 : -p < e) (h2 : e < p) :
    e / p = if 0 ≤ e then 0 else -1 := by
  split_ifs with h
  · exact Int.ediv_eq_zero_of_lt h h2
  · exact ((Int.ediv_emod_unique (r := e + p) (q := -1) hp).mpr ⟨by omega, by omega, by omega⟩).1

theorem emod_eq_zero_of_eq_mul (m p q : ℤ) (h : m = p * q) : m % p = 0 := by
  rw [h]; exact Int.mul_emod_right p q

/-- `m ≤ j p ↔ (m - 1)/p < j`. -/
theorem le_mul_iff_ediv_lt (m j p : ℤ) (hp : 0 < p) : m ≤ j * p ↔ (m - 1) / p < j := by
  rw [← not_le, Int.le_ediv_iff_mul_le hp]; omega

/-- `j p ≤ m ↔ j ≤ m/p`. -/
theorem mul_le_iff_le_ediv (m j p : ℤ) (hp : 0 < p) : j * p ≤ m ↔ j ≤ m / p :=
  (Int.le_ediv_iff_mul_le hp).symm

/-! ### The non-boundary condition and the shift lemma -/

/-- `p ∤ cN + e` for `1 ≤ |c| ≤ 29`, `|e| ≤ 10`. -/
def NB (N p : ℤ) : Prop := ∀ c e : ℤ, c ≠ 0 → |c| ≤ 29 → |e| ≤ 10 → (c * N + e) % p ≠ 0

/-- `sh v c e = ⌊(cN + e)/p⌋` expressed through `v c = ⌊cN/p⌋`. -/
def sh (v : ℤ → ℤ) (c e : ℤ) : ℤ := if c = 0 then (if 0 ≤ e then 0 else -1) else v c

theorem sh_true {N p : ℤ} (hp : 10 < p) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) (c e : ℤ) (hc : |c| ≤ 29) (he : |e| ≤ 10) :
    (c * N + e) / p = sh v c e := by
  have he' := abs_le.mp he
  by_cases hc0 : c = 0
  · subst hc0
    unfold sh
    rw [ite_eq_left rfl, zero_mul, zero_add]
    exact ediv_small e p (by omega) (by omega) (by omega)
  · unfold sh
    rw [ite_eq_right hc0, ← hv c hc]
    have h1 := emod_add_mul_ediv (c * N) p
    have h2 := Int.emod_nonneg (c * N) (show p ≠ 0 by omega)
    have h3 := Int.emod_lt_of_pos (c * N) (show 0 < p by omega)
    have hlo : 10 < (c * N) % p := by
      by_contra hcon
      have := hNB c (-((c * N) % p)) hc0 hc (abs_le.mpr ⟨by omega, by omega⟩)
      exact this (emod_eq_zero_of_eq_mul _ p ((c * N) / p) (by omega))
    have hhi : (c * N) % p < p - 10 := by
      by_contra hcon
      have := hNB c (p - (c * N) % p) hc0 hc (abs_le.mpr ⟨by omega, by omega⟩)
      exact this (emod_eq_zero_of_eq_mul _ p ((c * N) / p + 1)
        (by linear_combination (-1 : ℤ) * h1))
    exact ((Int.ediv_emod_unique (r := (c * N) % p + e) (q := (c * N) / p) (by omega)).mpr
      ⟨by omega, by omega, by omega⟩).1

/-! ### Terms -/

/-- `fl s c d`: `s ⌊(k + cN + d)/p⌋`; `up s c d`: `s [k + cN + d ≥ p]`;
`dn s c d`: `s [cN + d - k ≥ p]`; `mx s c₁ d₁ c₂ d₂`: `s · max([k + c₁N + d₁ ≥ p], [c₂N + d₂ - k ≥ p])`;
`one s`: the constant `s`. -/
inductive Term
  | fl (s c d : ℤ)
  | up (s c d : ℤ)
  | dn (s c d : ℤ)
  | mx (s c₁ d₁ c₂ d₂ : ℤ)
  | one (s : ℤ)

/-- `[p ≤ m]` as an integer. -/
def ind (p m : ℤ) : ℤ := if p ≤ m then 1 else 0

def Term.eval (N p k : ℤ) : Term → ℤ
  | .fl s c d => s * ((k + c * N + d) / p)
  | .up s c d => s * ind p (k + c * N + d)
  | .dn s c d => s * ind p (c * N + d - k)
  | .mx s c₁ d₁ c₂ d₂ => s * max (ind p (k + c₁ * N + d₁)) (ind p (c₂ * N + d₂ - k))
  | .one s => s

def evalE (N p k : ℤ) (E : List Term) : ℤ := (E.map (Term.eval N p k)).sum

/-- The candidate classes `(c₀, d₀)` of a term: it can only change at `k ≡ -(c₀N + d₀)`. -/
def Term.classes : Term → List (ℤ × ℤ)
  | .fl _ c d => [(c, d)]
  | .up _ c d => [(c, d)]
  | .dn _ c d => [(-c, -d - 1)]
  | .mx _ c₁ d₁ c₂ d₂ => [(c₁, d₁), (-c₂, -d₂ - 1)]
  | .one _ => []

def classesE (E : List Term) : List (ℤ × ℤ) := E.flatMap Term.classes

theorem ind_pred (p m : ℤ) (hp : 0 < p) (h : m % p ≠ 0) : ind p (m - 1) = ind p m := by
  have : m ≠ p := fun hm => h (by rw [hm]; exact Int.emod_self)
  unfold ind
  split_ifs <;> omega

theorem ind_succ (p m : ℤ) (hp : 0 < p) (h : (-m - 1) % p ≠ 0) : ind p (m + 1) = ind p m := by
  have : m + 1 ≠ p := fun hm => h (by rw [show -m - 1 = -p by omega, Int.neg_emod_self])
  unfold ind
  split_ifs <;> omega

/-- A change of value from `k - 1` to `k` forces `k` into a candidate class. -/
theorem Term.jump (N p k : ℤ) (hp : 0 < p) (t : Term)
    (h : Term.eval N p k t ≠ Term.eval N p (k - 1) t) :
    ∃ cd ∈ t.classes, (k + cd.1 * N + cd.2) % p = 0 := by
  cases t with
  | fl s c d =>
    refine ⟨(c, d), List.mem_singleton_self _, ?_⟩
    by_contra hne
    apply h
    simp only [Term.eval]
    rw [show k - 1 + c * N + d = (k + c * N + d) - 1 by ring, ediv_pred _ _ hp hne]
  | up s c d =>
    refine ⟨(c, d), List.mem_singleton_self _, ?_⟩
    by_contra hne
    apply h
    simp only [Term.eval]
    rw [show k - 1 + c * N + d = (k + c * N + d) - 1 by ring, ind_pred _ _ hp hne]
  | dn s c d =>
    refine ⟨(-c, -d - 1), List.mem_singleton_self _, ?_⟩
    by_contra hne
    apply h
    simp only [Term.eval]
    rw [show c * N + d - (k - 1) = (c * N + d - k) + 1 by ring, ind_succ _ _ hp
      (by rw [show -(c * N + d - k) - 1 = k + -c * N + (-d - 1) by ring]; exact hne)]
  | mx s c₁ d₁ c₂ d₂ =>
    by_cases h1 : (k + c₁ * N + d₁) % p = 0
    · exact ⟨(c₁, d₁), List.mem_cons_self .., h1⟩
    by_cases h2 : (k + -c₂ * N + (-d₂ - 1)) % p = 0
    · exact ⟨(-c₂, -d₂ - 1), List.mem_cons_of_mem _ (List.mem_singleton_self _), h2⟩
    exfalso
    apply h
    simp only [Term.eval]
    rw [show k - 1 + c₁ * N + d₁ = (k + c₁ * N + d₁) - 1 by ring, ind_pred _ _ hp h1,
      show c₂ * N + d₂ - (k - 1) = (c₂ * N + d₂ - k) + 1 by ring, ind_succ _ _ hp
      (by rw [show -(c₂ * N + d₂ - k) - 1 = k + -c₂ * N + (-d₂ - 1) by ring]; exact h2)]
  | one s => exact absurd rfl h

theorem jumpE (N p k : ℤ) (hp : 0 < p) (E : List Term)
    (h : evalE N p k E ≠ evalE N p (k - 1) E) :
    ∃ cd ∈ classesE E, (k + cd.1 * N + cd.2) % p = 0 := by
  induction E with
  | nil => exact absurd rfl h
  | cons t E ih =>
    have hs : ∀ k', evalE N p k' (t :: E) = Term.eval N p k' t + evalE N p k' E := fun k' => by
      unfold evalE; rw [List.map_cons, List.sum_cons]
    rw [hs, hs] at h
    by_cases ht : Term.eval N p k t = Term.eval N p (k - 1) t
    · obtain ⟨cd, hcd, hk⟩ := ih (fun hE => h (by rw [ht, hE]))
      obtain ⟨t', ht', hcd'⟩ := List.mem_flatMap.mp hcd
      exact ⟨cd, List.mem_flatMap.mpr ⟨t', List.mem_cons_of_mem _ ht', hcd'⟩, hk⟩
    · obtain ⟨cd, hcd, hk⟩ := Term.jump N p k hp t ht
      exact ⟨cd, List.mem_flatMap.mpr ⟨t, List.mem_cons_self .., hcd⟩, hk⟩

/-! ### Values at candidates -/

/-- The range conditions under which `eval_cand` holds for the class `(c₀, d₀)`. -/
def Term.ok (c₀ d₀ : ℤ) : Term → Prop
  | .fl _ c d => |c - c₀| ≤ 29 ∧ |d - d₀| ≤ 10
  | .up _ c d => |c - c₀| ≤ 29 ∧ |d - d₀| ≤ 10
  | .dn _ c d => |c + c₀| ≤ 29 ∧ |d + d₀| ≤ 10
  | .mx _ c₁ d₁ c₂ d₂ => (|c₁ - c₀| ≤ 29 ∧ |d₁ - d₀| ≤ 10) ∧ (|c₂ + c₀| ≤ 29 ∧ |d₂ + d₀| ≤ 10)
  | .one _ => True

instance (c₀ d₀ : ℤ) : (t : Term) → Decidable (t.ok c₀ d₀)
  | .fl _ c d => inferInstanceAs (Decidable (|c - c₀| ≤ 29 ∧ |d - d₀| ≤ 10))
  | .up _ c d => inferInstanceAs (Decidable (|c - c₀| ≤ 29 ∧ |d - d₀| ≤ 10))
  | .dn _ c d => inferInstanceAs (Decidable (|c + c₀| ≤ 29 ∧ |d + d₀| ≤ 10))
  | .mx _ c₁ d₁ c₂ d₂ => inferInstanceAs
      (Decidable ((|c₁ - c₀| ≤ 29 ∧ |d₁ - d₀| ≤ 10) ∧ (|c₂ + c₀| ≤ 29 ∧ |d₂ + d₀| ≤ 10)))
  | .one _ => inferInstanceAs (Decidable True)

/-- `[1 ≤ m]`. -/
def pos1 (m : ℤ) : ℤ := if 1 ≤ m then 1 else 0

def Term.evalCand (v : ℤ → ℤ) (c₀ d₀ j : ℤ) : Term → ℤ
  | .fl s c d => s * (j + sh v (c - c₀) (d - d₀))
  | .up s c d => s * pos1 (j + sh v (c - c₀) (d - d₀))
  | .dn s c d => s * pos1 (sh v (c + c₀) (d + d₀) - j)
  | .mx s c₁ d₁ c₂ d₂ =>
      s * max (pos1 (j + sh v (c₁ - c₀) (d₁ - d₀))) (pos1 (sh v (c₂ + c₀) (d₂ + d₀) - j))
  | .one s => s

def evalCandE (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term) : ℤ :=
  (E.map (Term.evalCand v c₀ d₀ j)).sum

theorem ind_cand (p m j : ℤ) (hp : 0 < p) : ind p (m + j * p) = pos1 (j + m / p) := by
  unfold ind pos1
  have : p ≤ m + j * p ↔ 1 ≤ j + m / p := by
    rw [show (1 ≤ j + m / p) ↔ (1 - j ≤ m / p) by omega, Int.le_ediv_iff_mul_le hp]
    constructor <;> intro h <;> nlinarith
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl

theorem ind_cand' (p m j : ℤ) (hp : 0 < p) : ind p (m - j * p) = pos1 (m / p - j) := by
  unfold ind pos1
  have : p ≤ m - j * p ↔ 1 ≤ m / p - j := by
    rw [show (1 ≤ m / p - j) ↔ (1 + j ≤ m / p) by omega, Int.le_ediv_iff_mul_le hp]
    constructor <;> intro h <;> nlinarith
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl

theorem Term.eval_cand {N p : ℤ} (hp : 10 < p) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) (c₀ d₀ j : ℤ) (t : Term) (hok : t.ok c₀ d₀) :
    Term.eval N p (-(c₀ * N + d₀) + j * p) t = Term.evalCand v c₀ d₀ j t := by
  cases t with
  | fl s c d =>
    simp only [Term.eval, Term.evalCand]
    rw [show -(c₀ * N + d₀) + j * p + c * N + d = ((c - c₀) * N + (d - d₀)) + j * p by ring,
      Int.add_mul_ediv_right _ _ (by omega), sh_true hp hNB hv _ _ hok.1 hok.2, add_comm]
  | up s c d =>
    simp only [Term.eval, Term.evalCand]
    rw [show -(c₀ * N + d₀) + j * p + c * N + d = ((c - c₀) * N + (d - d₀)) + j * p by ring,
      ind_cand _ _ _ (by omega), sh_true hp hNB hv _ _ hok.1 hok.2]
  | dn s c d =>
    simp only [Term.eval, Term.evalCand]
    rw [show c * N + d - (-(c₀ * N + d₀) + j * p) = ((c + c₀) * N + (d + d₀)) - j * p by ring,
      ind_cand' _ _ _ (by omega), sh_true hp hNB hv _ _ hok.1 hok.2]
  | mx s c₁ d₁ c₂ d₂ =>
    simp only [Term.eval, Term.evalCand]
    rw [show -(c₀ * N + d₀) + j * p + c₁ * N + d₁ = ((c₁ - c₀) * N + (d₁ - d₀)) + j * p by ring,
      ind_cand _ _ _ (by omega), sh_true hp hNB hv _ _ hok.1.1 hok.1.2,
      show c₂ * N + d₂ - (-(c₀ * N + d₀) + j * p) = ((c₂ + c₀) * N + (d₂ + d₀)) - j * p by ring,
      ind_cand' _ _ _ (by omega), sh_true hp hNB hv _ _ hok.2.1 hok.2.2]
  | one s => rfl

theorem eval_candE {N p : ℤ} (hp : 10 < p) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) (c₀ d₀ j : ℤ) (E : List Term)
    (hok : ∀ t ∈ E, t.ok c₀ d₀) :
    evalE N p (-(c₀ * N + d₀) + j * p) E = evalCandE v c₀ d₀ j E := by
  induction E with
  | nil => rfl
  | cons t E ih =>
    simp only [evalE, evalCandE, List.map_cons, List.sum_cons] at ih ⊢
    rw [Term.eval_cand hp hNB hv c₀ d₀ j t (hok t (List.mem_cons_self ..)),
      ih fun t' ht' => hok t' (List.mem_cons_of_mem _ ht')]

/-! ### Minimum over a region -/

/-- Every value on `[lo, k]` is bounded below by the value at `lo` or at a point of decrease. -/
theorem exists_decrease (f : ℤ → ℤ) (lo : ℤ) :
    ∀ k, lo ≤ k → ∃ c, lo ≤ c ∧ c ≤ k ∧ (c = lo ∨ f c < f (c - 1)) ∧ f c ≤ f k := by
  intro k hk
  induction k, hk using Int.leInduction with
  | base => exact ⟨lo, le_rfl, le_rfl, Or.inl rfl, le_rfl⟩
  | succ k hk ih =>
    obtain ⟨c, h1, h2, h3, h4⟩ := ih
    by_cases h : f (k + 1) < f (k + 1 - 1)
    · exact ⟨k + 1, by omega, le_rfl, Or.inr h, le_rfl⟩
    · exact ⟨c, h1, by omega, h3, by rw [show k + 1 - 1 = k by ring] at h; omega⟩

/-- Candidates `j` for which `-(c₀N + d₀) + jp ∈ [c_lo N + d_lo, c_hi N + d_hi]`. -/
def jmin (v : ℤ → ℤ) (clo dlo c₀ d₀ : ℤ) : ℤ := sh v (clo + c₀) (dlo + d₀ - 1) + 1
def jmax (v : ℤ → ℤ) (chi dhi c₀ d₀ : ℤ) : ℤ := sh v (chi + c₀) (dhi + d₀)

theorem in_range_iff {N p : ℤ} (hp : 10 < p) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) (clo dlo chi dhi c₀ d₀ j : ℤ)
    (h1 : |clo + c₀| ≤ 29) (h2 : |dlo + d₀ - 1| ≤ 10) (h3 : |chi + c₀| ≤ 29)
    (h4 : |dhi + d₀| ≤ 10) :
    (clo * N + dlo ≤ -(c₀ * N + d₀) + j * p ∧ -(c₀ * N + d₀) + j * p ≤ chi * N + dhi) ↔
      (jmin v clo dlo c₀ d₀ ≤ j ∧ j ≤ jmax v chi dhi c₀ d₀) := by
  unfold jmin jmax
  rw [← sh_true hp hNB hv _ _ h1 h2, ← sh_true hp hNB hv _ _ h3 h4,
    show clo * N + dlo ≤ -(c₀ * N + d₀) + j * p ↔ (clo + c₀) * N + (dlo + d₀) ≤ j * p by
      constructor <;> intro h <;> linarith,
    le_mul_iff_ediv_lt _ _ _ (by omega),
    show -(c₀ * N + d₀) + j * p ≤ chi * N + dhi ↔ j * p ≤ (chi + c₀) * N + (dhi + d₀) by
      constructor <;> intro h <;> linarith,
    mul_le_iff_le_ediv _ _ _ (by omega), show (clo + c₀) * N + (dlo + d₀) - 1 =
      (clo + c₀) * N + (dlo + d₀ - 1) by ring]
  omega

/-- The integers `a, a+1, …, b`. -/
def jRange (a b : ℤ) : List ℤ := (List.range (b + 1 - a).toNat).map fun i : ℕ => a + (i : ℤ)

theorem mem_jRange {a b j : ℤ} (h1 : a ≤ j) (h2 : j ≤ b) : j ∈ jRange a b := by
  unfold jRange
  have h3 : (j - a).toNat < (b + 1 - a).toNat := by omega
  have h4 : a + ((j - a).toNat : ℤ) = j := by omega
  exact (List.mem_map (f := fun i : ℕ => a + (i : ℤ)) (l := List.range (b + 1 - a).toNat)).mpr
    ⟨(j - a).toNat, List.mem_range.mpr h3, h4⟩

/-- Minimum of a list with a starting value. -/
def listMin (l : List ℤ) (m : ℤ) : ℤ := l.foldl min m

theorem listMin_le_init (l : List ℤ) (m : ℤ) : listMin l m ≤ m := by
  induction l generalizing m with
  | nil => exact le_rfl
  | cons x l ih => exact (ih (min m x)).trans (min_le_left _ _)

theorem listMin_le_mem (l : List ℤ) (m : ℤ) {x : ℤ} (hx : x ∈ l) : listMin l m ≤ x := by
  induction l generalizing m with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact (listMin_le_init l _).trans (min_le_right _ _)
    · exact ih (min m y) hx'

/-! ### Splitting a candidate value into its floor part and its indicator part -/

def Term.coef : Term → ℤ
  | .fl s _ _ => s
  | _ => 0

/-- The `j`-independent part (floors at `j = 0` and constants). -/
def Term.flPart (v : ℤ → ℤ) (c₀ d₀ : ℤ) : Term → ℤ
  | .fl s c d => s * sh v (c - c₀) (d - d₀)
  | .one s => s
  | _ => 0

/-- The indicator part. -/
def Term.indPart (v : ℤ → ℤ) (c₀ d₀ j : ℤ) : Term → ℤ
  | .up s c d => s * pos1 (j + sh v (c - c₀) (d - d₀))
  | .dn s c d => s * pos1 (sh v (c + c₀) (d + d₀) - j)
  | .mx s c₁ d₁ c₂ d₂ =>
      s * max (pos1 (j + sh v (c₁ - c₀) (d₁ - d₀))) (pos1 (sh v (c₂ + c₀) (d₂ + d₀) - j))
  | _ => 0

theorem Term.evalCand_split (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (t : Term) :
    t.evalCand v c₀ d₀ j = t.flPart v c₀ d₀ + j * t.coef + t.indPart v c₀ d₀ j := by
  cases t <;> simp only [Term.evalCand, Term.flPart, Term.coef, Term.indPart] <;> ring

def flPartE (v : ℤ → ℤ) (c₀ d₀ : ℤ) (E : List Term) : ℤ := (E.map (Term.flPart v c₀ d₀)).sum
def indPartE (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term) : ℤ := (E.map (Term.indPart v c₀ d₀ j)).sum

theorem evalCandE_split (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term) :
    evalCandE v c₀ d₀ j E = flPartE v c₀ d₀ E + j * (E.map Term.coef).sum + indPartE v c₀ d₀ j E := by
  induction E with
  | nil => simp [evalCandE, flPartE, indPartE]
  | cons t E ih =>
    simp only [evalCandE, flPartE, indPartE, List.map_cons, List.sum_cons] at ih ⊢
    rw [Term.evalCand_split, ih]
    ring

def Term.isInd : Term → Bool
  | .up _ _ _ => true
  | .dn _ _ _ => true
  | .mx _ _ _ _ _ => true
  | _ => false

def Term.isFlOne : Term → Bool
  | .fl _ _ _ => true
  | .one _ => true
  | _ => false

/-- `flPartE` restricted to the floor/constant terms (the others contribute `0`). -/
def flPartE' (v : ℤ → ℤ) (c₀ d₀ : ℤ) (E : List Term) : ℤ :=
  ((E.filter Term.isFlOne).map (Term.flPart v c₀ d₀)).sum

/-- `indPartE` restricted to the indicator terms. -/
def indPartE' (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term) : ℤ :=
  ((E.filter Term.isInd).map (Term.indPart v c₀ d₀ j)).sum

theorem flPartE'_eq (v : ℤ → ℤ) (c₀ d₀ : ℤ) (E : List Term) :
    flPartE' v c₀ d₀ E = flPartE v c₀ d₀ E := by
  induction E with
  | nil => rfl
  | cons t E ih =>
    unfold flPartE' flPartE at ih ⊢
    cases t <;> simp only [List.filter_cons, Term.isFlOne, ite_true, ite_false, Bool.false_eq_true,
      List.map_cons, List.sum_cons, Term.flPart, ih, zero_add]

theorem indPartE'_eq (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term) :
    indPartE' v c₀ d₀ j E = indPartE v c₀ d₀ j E := by
  induction E with
  | nil => rfl
  | cons t E ih =>
    unfold indPartE' indPartE at ih ⊢
    cases t <;> simp only [List.filter_cons, Term.isInd, ite_true, ite_false, Bool.false_eq_true,
      List.map_cons, List.sum_cons, Term.indPart, ih, zero_add]

/-- The points where the indicator part of a term can change. -/
def Term.bps (v : ℤ → ℤ) (c₀ d₀ : ℤ) : Term → List ℤ
  | .up _ c d => [1 - sh v (c - c₀) (d - d₀)]
  | .dn _ c d => [sh v (c + c₀) (d + d₀)]
  | .mx _ c₁ d₁ c₂ d₂ => [1 - sh v (c₁ - c₀) (d₁ - d₀), sh v (c₂ + c₀) (d₂ + d₀)]
  | _ => []

def bpsE (v : ℤ → ℤ) (c₀ d₀ : ℤ) (E : List Term) : List ℤ := E.flatMap (Term.bps v c₀ d₀)

theorem pos1_change (s j : ℤ) (h : pos1 (j + s) ≠ pos1 (j - 1 + s)) : j = 1 - s := by
  unfold pos1 at h
  split_ifs at h <;> omega

theorem pos1_change' (s j : ℤ) (h : pos1 (s - j) ≠ pos1 (s - (j - 1))) : j = s := by
  unfold pos1 at h
  split_ifs at h <;> omega

theorem Term.indPart_change (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (t : Term)
    (h : t.indPart v c₀ d₀ j ≠ t.indPart v c₀ d₀ (j - 1)) : j ∈ t.bps v c₀ d₀ := by
  cases t with
  | up s c d =>
    simp only [Term.indPart] at h
    rw [Term.bps, List.mem_singleton]
    exact pos1_change _ _ fun h' => h (by rw [h'])
  | dn s c d =>
    simp only [Term.indPart] at h
    rw [Term.bps, List.mem_singleton]
    exact pos1_change' _ _ fun h' => h (by rw [h'])
  | mx s c₁ d₁ c₂ d₂ =>
    simp only [Term.indPart] at h
    rw [Term.bps, List.mem_cons, List.mem_singleton]
    by_contra hne
    rw [not_or] at hne
    apply h
    rw [show pos1 (j + sh v (c₁ - c₀) (d₁ - d₀)) = pos1 (j - 1 + sh v (c₁ - c₀) (d₁ - d₀)) by
        by_contra h'; exact hne.1 (pos1_change _ _ h'),
      show pos1 (sh v (c₂ + c₀) (d₂ + d₀) - j) = pos1 (sh v (c₂ + c₀) (d₂ + d₀) - (j - 1)) by
        by_contra h'; exact hne.2 (pos1_change' _ _ h')]
  | fl s c d => exact absurd rfl h
  | one s => exact absurd rfl h

theorem indPartE_change (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term)
    (h : indPartE v c₀ d₀ j E ≠ indPartE v c₀ d₀ (j - 1) E) : j ∈ bpsE v c₀ d₀ E := by
  induction E with
  | nil => exact absurd rfl h
  | cons t E ih =>
    simp only [indPartE, List.map_cons, List.sum_cons] at h ih
    by_cases ht : t.indPart v c₀ d₀ j = t.indPart v c₀ d₀ (j - 1)
    · obtain hmem := ih (fun hE => h (by rw [ht, hE]))
      obtain ⟨t', ht', hj⟩ := List.mem_flatMap.mp hmem
      exact List.mem_flatMap.mpr ⟨t', List.mem_cons_of_mem _ ht', hj⟩
    · exact List.mem_flatMap.mpr ⟨t, List.mem_cons_self .., Term.indPart_change v c₀ d₀ j t ht⟩

theorem flPartE_append (v : ℤ → ℤ) (c₀ d₀ : ℤ) (E₁ E₂ : List Term) :
    flPartE v c₀ d₀ (E₁ ++ E₂) = flPartE v c₀ d₀ E₁ + flPartE v c₀ d₀ E₂ := by
  unfold flPartE; rw [List.map_append, List.sum_append]

/-- The candidate values of one class: the floor part (computed on the shared list `E₁` and the
region-specific list `E₂`) plus the indicator part at `jmin` and at the breakpoints in
`(jmin, jmax]`. -/
def classVals (v : ℤ → ℤ) (clo dlo chi dhi : ℤ) (E₁ E₂ : List Term) (cd : ℤ × ℤ) : List ℤ :=
  let a := jmin v clo dlo cd.1 cd.2
  let b := jmax v chi dhi cd.1 cd.2
  let base := flPartE' v cd.1 cd.2 E₁ + flPartE' v cd.1 cd.2 E₂
  ((if a ≤ b then [a] else []) ++
      (bpsE v cd.1 cd.2 (E₁ ++ E₂)).filter fun θ => a < θ ∧ θ ≤ b).map fun j =>
    base + indPartE' v cd.1 cd.2 j (E₁ ++ E₂)

/-- The lower bound over a region `[c_lo N + d_lo, c_hi N + d_hi]` for the expression `E₁ ++ E₂`. -/
def boundE (v : ℤ → ℤ) (clo dlo chi dhi : ℤ) (E₁ E₂ : List Term) : ℤ :=
  listMin ((classesE (E₁ ++ E₂)).flatMap (classVals v clo dlo chi dhi E₁ E₂))
    (evalCandE v (-clo) (-dlo) 0 (E₁ ++ E₂))

/-- All range conditions needed for a region. -/
def regionOK (clo dlo chi dhi : ℤ) (E₁ E₂ : List Term) : Prop :=
  ((E₁ ++ E₂).map Term.coef).sum = 0 ∧ (∀ t ∈ E₁ ++ E₂, t.ok (-clo) (-dlo)) ∧
    ∀ cd ∈ classesE (E₁ ++ E₂), (∀ t ∈ E₁ ++ E₂, t.ok cd.1 cd.2) ∧
      |clo + cd.1| ≤ 29 ∧ |dlo + cd.2 - 1| ≤ 10 ∧ |chi + cd.1| ≤ 29 ∧ |dhi + cd.2| ≤ 10

instance (clo dlo chi dhi : ℤ) (E₁ E₂ : List Term) : Decidable (regionOK clo dlo chi dhi E₁ E₂) := by
  unfold regionOK; infer_instance

theorem region_ge_bound {N p : ℤ} (hp : 10 < p) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) (clo dlo chi dhi : ℤ) (E₁ E₂ : List Term)
    (hok : regionOK clo dlo chi dhi E₁ E₂) :
    ∀ k, clo * N + dlo ≤ k → k ≤ chi * N + dhi →
      boundE v clo dlo chi dhi E₁ E₂ ≤ evalE N p k (E₁ ++ E₂) := by
  intro k hk1 hk2
  obtain ⟨c, h1, h2, h3, h4⟩ := exists_decrease (fun k => evalE N p k (E₁ ++ E₂)) _ k hk1
  refine le_trans ?_ h4
  rcases h3 with rfl | hlt
  · rw [show clo * N + dlo = -((-clo) * N + (-dlo)) + 0 * p by ring,
      eval_candE hp hNB hv _ _ _ (E₁ ++ E₂) hok.2.1]
    exact listMin_le_init _ _
  · obtain ⟨cd, hcd, hc⟩ := jumpE N p c (by omega) (E₁ ++ E₂) (ne_of_lt hlt)
    obtain ⟨hokc, r1, r2, r3, r4⟩ := hok.2.2 cd hcd
    have hc' : c = -(cd.1 * N + cd.2) + ((c + cd.1 * N + cd.2) / p) * p := by
      have := Int.emod_add_ediv_mul (c + cd.1 * N + cd.2) p
      rw [hc] at this; linarith
    rw [hc', eval_candE hp hNB hv _ _ _ (E₁ ++ E₂) hokc, evalCandE_split, hok.1, mul_zero,
      add_zero]
    have hin := (in_range_iff hp hNB hv clo dlo chi dhi cd.1 cd.2 _ r1 r2 r3 r4).mp
      ⟨by rw [← hc']; exact h1, by rw [← hc']; omega⟩
    obtain ⟨j', g1, g2, g3, g4⟩ :=
      exists_decrease (fun j => indPartE v cd.1 cd.2 j (E₁ ++ E₂)) _ _ hin.1
    refine le_trans ?_ (show flPartE v cd.1 cd.2 (E₁ ++ E₂) + indPartE v cd.1 cd.2 j' (E₁ ++ E₂) ≤
      flPartE v cd.1 cd.2 (E₁ ++ E₂) + indPartE v cd.1 cd.2 ((c + cd.1 * N + cd.2) / p) (E₁ ++ E₂)
      by omega)
    refine listMin_le_mem _ _ (List.mem_flatMap.mpr ⟨cd, hcd, ?_⟩)
    dsimp only [classVals]
    refine List.mem_map.mpr ⟨j', ?_, by rw [flPartE'_eq, flPartE'_eq, indPartE'_eq, flPartE_append]⟩
    rw [List.mem_append]
    by_cases hj : j' = jmin v clo dlo cd.1 cd.2
    · left
      rw [hj, ite_eq_left (hin.1.trans hin.2)]
      exact List.mem_singleton_self _
    · right
      rcases g3 with rfl | hlt'
      · exact absurd rfl hj
      · exact List.mem_filter.mpr
          ⟨indPartE_change v cd.1 cd.2 j' (E₁ ++ E₂) (ne_of_lt hlt'), by
            rw [decide_eq_true_eq]; exact ⟨lt_of_le_of_ne g1 (Ne.symm hj), g2.trans hin.2⟩⟩

/-! ### The indicator-free version -/

def Term.isFl : Term → Bool
  | .fl _ _ _ => true
  | .one _ => true
  | _ => false

def Term.slope : Term → ℤ
  | .fl s c _ => s * c
  | _ => 0

theorem Term.evalCand_j (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (t : Term) (ht : t.isFl = true) :
    t.evalCand v c₀ d₀ j = t.evalCand v c₀ d₀ 0 + j * t.coef := by
  cases t with
  | fl s c d => simp only [Term.evalCand, Term.coef]; ring
  | one s => simp only [Term.evalCand, Term.coef]; ring
  | _ => exact absurd ht (by simp [Term.isFl])

theorem evalCandE_j (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E : List Term) (hE : ∀ t ∈ E, t.isFl = true) :
    evalCandE v c₀ d₀ j E = evalCandE v c₀ d₀ 0 E + j * (E.map Term.coef).sum := by
  induction E with
  | nil => simp [evalCandE]
  | cons t E ih =>
    simp only [evalCandE, List.map_cons, List.sum_cons] at ih ⊢
    rw [Term.evalCand_j v c₀ d₀ j t (hE t (List.mem_cons_self ..)),
      ih fun t' ht' => hE t' (List.mem_cons_of_mem _ ht')]
    ring

/-- Shifting the data by `n·c` (the passage from `N/p` to its fractional part). -/
theorem Term.evalCand_shift (v w : ℤ → ℤ) (n : ℤ) (hvw : ∀ c, |c| ≤ 29 → v c = n * c + w c)
    (c₀ d₀ j : ℤ) (t : Term) (ht : t.isFl = true) (hok : t.ok c₀ d₀) :
    t.evalCand v c₀ d₀ j = t.evalCand w c₀ d₀ j + n * (t.slope - c₀ * t.coef) := by
  cases t with
  | fl s c d =>
    simp only [Term.evalCand, Term.slope, Term.coef, sh]
    by_cases h : c - c₀ = 0
    · rw [ite_eq_left h, ite_eq_left h, show c = c₀ by omega]; ring
    · rw [ite_eq_right h, ite_eq_right h, hvw _ hok.1]; ring
  | one s => simp only [Term.evalCand, Term.slope, Term.coef]; ring
  | _ => exact absurd ht (by simp [Term.isFl])

theorem evalCandE_shift (v w : ℤ → ℤ) (n : ℤ) (hvw : ∀ c, |c| ≤ 29 → v c = n * c + w c)
    (c₀ d₀ j : ℤ) (E : List Term) (hE : ∀ t ∈ E, t.isFl = true) (hok : ∀ t ∈ E, t.ok c₀ d₀) :
    evalCandE v c₀ d₀ j E = evalCandE w c₀ d₀ j E +
      n * ((E.map Term.slope).sum - c₀ * (E.map Term.coef).sum) := by
  induction E with
  | nil => simp [evalCandE]
  | cons t E ih =>
    simp only [evalCandE, List.map_cons, List.sum_cons] at ih ⊢
    rw [Term.evalCand_shift v w n hvw c₀ d₀ j t (hE t (List.mem_cons_self ..))
      (hok t (List.mem_cons_self ..)),
      ih (fun t' ht' => hE t' (List.mem_cons_of_mem _ ht'))
        (fun t' ht' => hok t' (List.mem_cons_of_mem _ ht'))]
    ring

/-- Minimum of a nonempty list (`0` for the empty list). -/
def listMinD (l : List ℤ) : ℤ := listMin l (l.headD 0)

theorem listMinD_le_mem {l : List ℤ} {x : ℤ} (hx : x ∈ l) : listMinD l ≤ x :=
  listMin_le_mem l _ hx

theorem evalCandE_append (v : ℤ → ℤ) (c₀ d₀ j : ℤ) (E₁ E₂ : List Term) :
    evalCandE v c₀ d₀ j (E₁ ++ E₂) = evalCandE v c₀ d₀ j E₁ + evalCandE v c₀ d₀ j E₂ := by
  unfold evalCandE; rw [List.map_append, List.sum_append]

/-- The class values of an indicator-free expression (shared by all regions). -/
def classMinP (v : ℤ → ℤ) (E₁ E₂ : List Term) : ℤ :=
  listMinD ((classesE (E₁ ++ E₂)).map fun cd =>
    evalCandE v cd.1 cd.2 0 E₁ + evalCandE v cd.1 cd.2 0 E₂)

/-- The lower bound for an indicator-free expression with zero total slope: the candidates
with `j = 0` suffice. -/
def boundP (v : ℤ → ℤ) (clo dlo : ℤ) (E₁ E₂ : List Term) : ℤ :=
  min (evalCandE v (-clo) (-dlo) 0 (E₁ ++ E₂)) (classMinP v E₁ E₂)

def regionOKP (clo dlo : ℤ) (E₁ E₂ : List Term) : Prop :=
  (∀ t ∈ E₁ ++ E₂, t.isFl = true) ∧ ((E₁ ++ E₂).map Term.coef).sum = 0 ∧
    (∀ t ∈ E₁ ++ E₂, t.ok (-clo) (-dlo)) ∧ ∀ cd ∈ classesE (E₁ ++ E₂), ∀ t ∈ E₁ ++ E₂, t.ok cd.1 cd.2

instance (clo dlo : ℤ) (E₁ E₂ : List Term) : Decidable (regionOKP clo dlo E₁ E₂) := by
  unfold regionOKP; infer_instance

theorem region_ge_boundP {N p : ℤ} (hp : 10 < p) (hNB : NB N p) {v : ℤ → ℤ}
    (hv : ∀ c, |c| ≤ 29 → (c * N) / p = v c) (clo dlo : ℤ) (E₁ E₂ : List Term)
    (hok : regionOKP clo dlo E₁ E₂) (hi : ℤ) :
    ∀ k, clo * N + dlo ≤ k → k ≤ hi → boundP v clo dlo E₁ E₂ ≤ evalE N p k (E₁ ++ E₂) := by
  intro k hk1 _
  obtain ⟨c, h1, h2, h3, h4⟩ := exists_decrease (fun k => evalE N p k (E₁ ++ E₂)) _ k hk1
  refine le_trans ?_ h4
  rcases h3 with rfl | hlt
  · rw [show clo * N + dlo = -((-clo) * N + (-dlo)) + 0 * p by ring,
      eval_candE hp hNB hv _ _ _ (E₁ ++ E₂) hok.2.2.1]
    exact min_le_left _ _
  · obtain ⟨cd, hcd, hc⟩ := jumpE N p c (by omega) (E₁ ++ E₂) (ne_of_lt hlt)
    have hc' : c = -(cd.1 * N + cd.2) + ((c + cd.1 * N + cd.2) / p) * p := by
      have := Int.emod_add_ediv_mul (c + cd.1 * N + cd.2) p
      rw [hc] at this; linarith
    rw [hc', eval_candE hp hNB hv _ _ _ (E₁ ++ E₂) (hok.2.2.2 cd hcd),
      evalCandE_j v _ _ _ (E₁ ++ E₂) hok.1, hok.2.1, mul_zero, add_zero, evalCandE_append]
    exact (min_le_right _ _).trans (listMinD_le_mem (List.mem_map.mpr ⟨cd, hcd, rfl⟩))

end ZetasIrr.CH
