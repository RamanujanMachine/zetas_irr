/-
# Auxiliary lemmas for `log_G_ge.lean`, part 2 (sorry-free)

Eligible primes in dilated intervals (from the prime number theorem and the negligibility of the
excluded primes, taken as hypotheses) and the profile contribution of a table of disjoint
intervals.
-/
import log_G_aux
import profile_aux

open Finset Filter Topology

noncomputable section

namespace Pfq54.LG2

open Pfq54

/-- The prime number theorem in the form `θ(n/a) - θ(n/b) ≥ (1/a - 1/b - ε) n` eventually. -/
def PNT : Prop := ∀ (a b : ℝ), 0 < a → a < b → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
  ((n : ℝ) / a - n / b) - ε * n ≤ Chebyshev.theta ((n : ℝ) / a) - Chebyshev.theta ((n : ℝ) / b)

/-- The excluded primes are negligible. -/
def EXC : Prop := ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
  ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p), Real.log p ≤ ε * n

/-- The prime number theorem on `(c₁ n, c₂ n)` (from [4]). -/
theorem prime_interval (hP : PNT) (c₁ c₂ : ℝ) (h0 : 0 < c₁) (h12 : c₁ < c₂) (h19 : c₂ ≤ 19) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, (c₂ - c₁ - ε) * n ≤
      ∑ p ∈ (range (19 * n + 1)).filter Nat.Prime,
        if c₁ * n < p ∧ (p : ℝ) < c₂ * n then Real.log p else 0 := by
  have hpi := hP (1 / c₂) (1 / c₁) (one_div_pos.mpr (h0.trans h12))
    (one_div_lt_one_div_of_lt h0 h12)
    (ε / 2) (by positivity)
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def (by positivity : 0 < ε / 4)
  filter_upwards [hpi, hlog, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (4 * Real.log 19 / ε), eventually_ge_atTop 1] with n h1 h2 h3 hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e : ∀ c : ℝ, (n : ℝ) / (1 / c) = c * n := fun c => by
    rw [div_div_eq_mul_div, div_one, mul_comm]
  rw [e, e] at h1
  have hI := LG.interval_sum n hn (c₁ * n) (c₂ * n) (mul_le_mul_of_nonneg_right h12.le hn0)
    (mul_le_mul_of_nonneg_right h19 hn0)
  simp only [Function.comp_apply, id_eq] at h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg hn0] at h2
  rw [div_le_iff₀ hε] at h3
  have hl : Real.log (19 * n) ≤ ε / 2 * n := by
    rw [Real.log_mul (by norm_num) (by exact_mod_cast (by omega : n ≠ 0))]
    linarith
  linarith

/-- The eligible primes on `(c₁ n, c₂ n)` (from [4], [5]). -/
theorem elig_interval (hP : PNT) (hE : EXC) (c₁ c₂ : ℝ) (h0 : 0 < c₁) (h12 : c₁ < c₂) (h19 : c₂ ≤ 19) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, (c₂ - c₁ - ε) * n ≤
      ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), if c₁ * n < p ∧ (p : ℝ) < c₂ * n then Real.log p else 0 := by
  filter_upwards [prime_interval hP c₁ c₂ h0 h12 h19 (ε / 2) (by positivity),
    hE (ε / 2) (by positivity)] with n h1 h2
  have hsplit := Finset.sum_filter_add_sum_filter_not ((range (19 * n + 1)).filter Nat.Prime)
    (Eligible n) fun p => if c₁ * n < p ∧ (p : ℝ) < c₂ * n then Real.log p else 0
  have hA : ((range (19 * n + 1)).filter Nat.Prime).filter (Eligible n) = (range (19 * n + 1)).filter (Eligible n) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun p _ => ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hB : ((range (19 * n + 1)).filter Nat.Prime).filter (fun p => ¬ Eligible n p) =
      (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p) := by
    rw [Finset.filter_filter]
  rw [hA, hB] at hsplit
  have hE : ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p),
      (if c₁ * n < p ∧ (p : ℝ) < c₂ * n then Real.log p else 0) ≤
        ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p), Real.log p :=
    Finset.sum_le_sum fun p _ => by
      split_ifs
      · exact le_rfl
      · exact Real.log_natCast_nonneg p
  linarith

theorem natc1 (c n p : ℕ) : ((c : ℝ) * n < p ↔ c * n < p) := by
  rw [← Nat.cast_mul, Nat.cast_lt]

theorem natc2 (c n p : ℕ) : ((p : ℝ) < c * n ↔ p < c * n) := by
  rw [← Nat.cast_mul, Nat.cast_lt]

/-- The eligible primes on `(c₁ n, c₂ n)` for integers `c₁ < c₂`. -/
theorem elig_interval_nat (hP : PNT) (hE : EXC) (c₁ c₂ : ℕ) (h0 : 0 < c₁) (h12 : c₁ < c₂) (h19 : c₂ ≤ 19) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ((c₂ : ℝ) - c₁ - ε) * n ≤
      ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), if c₁ * n < p ∧ p < c₂ * n then Real.log p else 0 := by
  filter_upwards [elig_interval hP hE c₁ c₂ (by exact_mod_cast h0) (by exact_mod_cast h12)
    (by exact_mod_cast h19) ε hε] with n h
  simp only [natc1, natc2] at h
  exact h

/-- At most one table interval contains `y` (the rows are disjoint and lie in `(0, 1]`). -/
theorem rows_le (rows : List (ℚ × ℚ × ℕ))
    (hbd : ∀ r ∈ rows, 0 < r.1 ∧ r.2.1 ≤ 1)
    (htab : ∀ r ∈ rows, ∀ k : ℕ, ∀ x : ℚ, (k : ℚ) + r.1 < x → x < (k : ℚ) + r.2.1 → phi x = r.2.2)
    (y : ℚ) (w : ℝ) (hw : 0 ≤ w) (l : List (ℚ × ℚ × ℕ))
    (hl : ∀ r ∈ l, r ∈ rows) (hpw : l.Pairwise fun r s => r.2.1 ≤ s.1) :
    (l.map fun r => (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (if (k : ℚ) + r.1 < y ∧ y < k + r.2.1 then w else 0)).sum ≤ ((phi y).toNat : ℝ) * w := by
  have huniq : ∀ r ∈ rows, ∀ s ∈ rows, ∀ k k' : ℕ, (k : ℚ) + r.1 < y →
      y < k + r.2.1 → (k' : ℚ) + s.1 < y → y < k' + s.2.1 → k = k' := by
    intro r hr s hs k k' h1 h2 h3 h4
    obtain ⟨hr1, hr2⟩ := hbd r hr
    obtain ⟨hs1, hs2⟩ := hbd s hs
    have b1 : k < k' + 1 := by
      have : (k : ℚ) < k' + 1 := by linarith
      exact_mod_cast this
    have b2 : k' < k + 1 := by
      have : (k' : ℚ) < k + 1 := by linarith
      exact_mod_cast this
    omega
  induction l with
  | nil =>
    rw [List.map_nil, List.sum_nil]
    exact mul_nonneg (Nat.cast_nonneg _) hw
  | cons r l ih =>
    rw [List.map_cons, List.sum_cons]
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    have hr := hl r List.mem_cons_self
    by_cases h : ∃ k ∈ range 8, (k : ℚ) + r.1 < y ∧ y < k + r.2.1
    · obtain ⟨k0, hk0, hk⟩ := h
      have hin : ∑ k ∈ range 8, (if (k : ℚ) + r.1 < y ∧ y < k + r.2.1 then w else 0) = w := by
        rw [Finset.sum_eq_single k0 (fun k _ hk' => ite_eq_right fun h' =>
          hk' (huniq r hr r hr k k0 h'.1 h'.2 hk.1 hk.2)) (fun h' => absurd hk0 h'),
          ite_eq_left hk]
      have hrest : (l.map fun s => (s.2.2 : ℝ) * ∑ k ∈ range 8,
          (if (k : ℚ) + s.1 < y ∧ y < k + s.2.1 then w else 0)).sum = 0 := by
        refine List.sum_eq_zero fun z hz => ?_
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
        have hsr := hl s (List.mem_cons_of_mem r hs)
        have hz0 : ∀ k ∈ range 8, ¬ ((k : ℚ) + s.1 < y ∧ y < k + s.2.1) := by
          intro k _ h'
          have hkk := huniq s hsr r hr k k0 h'.1 h'.2 hk.1 hk.2
          rw [hkk] at h'
          have := hhead s hs
          linarith [h'.1, hk.2]
        rw [Finset.sum_eq_zero fun k hk => ite_eq_right (hz0 k hk), mul_zero]
      rw [hin, hrest, add_zero, htab r hr k0 y hk.1 hk.2, Int.toNat_natCast]
    · rw [Finset.sum_eq_zero fun k hk => ite_eq_right fun h' => h ⟨k, hk, h'⟩, mul_zero,
        zero_add]
      exact ih (fun s hs => hl s (List.mem_cons_of_mem r hs)) htail

/-- The profile contribution of a table of disjoint intervals `(a, b) ⊆ (0, 1]` on which
`φ = v` (all periods `k < 8`). -/
theorem profile_gen (hP : PNT) (hE : EXC) (rows : List (ℚ × ℚ × ℕ))
    (hbd : ∀ r ∈ rows, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1)
    (hpw : rows.Pairwise fun r s => r.2.1 ≤ s.1)
    (htab : ∀ r ∈ rows, ∀ k : ℕ, ∀ x : ℚ, (k : ℚ) + r.1 < x → x < (k : ℚ) + r.2.1 →
      phi x = r.2.2) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ((rows.map fun r => (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))).sum - ε) * n ≤
        ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), ((phi ((n : ℚ) / p)).toNat : ℝ) * Real.log p := by
  intro ε hε
  set K : ℝ := (rows.map fun r => (r.2.2 : ℝ) * 8).sum
  have hK0 : 0 ≤ K := List.sum_nonneg fun z hz => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hz
    positivity
  set ε' := ε / (K + 1)
  have hε' : 0 < ε' := by positivity
  have hεK : ε' * K ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hev := LG.eventually_list rows (fun r n => ∀ k ∈ range 8,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1) - ε') * n ≤ ∑ p ∈ (range (19 * n + 1)).filter (Eligible n),
        if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
        else 0)
    fun r hr => (eventually_all_finset (range 8)).mpr fun k _ => by
      obtain ⟨h1, h2, -⟩ := hbd r hr
      have a1 : (1 / 19 : ℝ) ≤ r.1 := by
        have := (Rat.cast_le (K := ℝ)).mpr h1
        push_cast at this
        exact this
      have a2 : (r.1 : ℝ) < r.2.1 := by exact_mod_cast h2
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact elig_interval hP hE _ _ (one_div_pos.mpr (by linarith))
        (one_div_lt_one_div_of_lt (by linarith) (by linarith))
        (by rw [div_le_iff₀ (by linarith)]; linarith) ε' hε'
  filter_upwards [hev] with n hn
  have step1 : ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), (rows.map fun r => (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
        else 0)).sum ≤ ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), ((phi ((n : ℚ) / p)).toNat : ℝ) * Real.log p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp0 : 0 < p := (mem_filter.mp hp).2.1.pos
    have e : ∀ r ∈ rows, (r.2.2 : ℝ) * ∑ k ∈ range 8,
        (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
          else 0) = (r.2.2 : ℝ) * ∑ k ∈ range 8,
        (if (k : ℚ) + r.1 < (n : ℚ) / p ∧ (n : ℚ) / p < k + r.2.1 then Real.log p else 0) := by
      intro r hr
      obtain ⟨h1, h2, -⟩ := hbd r hr
      have ha : 0 < r.1 := lt_of_lt_of_le (by norm_num) h1
      refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
      have hci := LG.cond_iff n p k hp0 r.1 r.2.1 ha (ha.trans h2)
      by_cases hc : (k : ℚ) + r.1 < (n : ℚ) / p ∧ (n : ℚ) / p < k + r.2.1
      · rw [ite_eq_left (hci.mpr hc), ite_eq_left hc]
      · rw [ite_eq_right fun h => hc (hci.mp h), ite_eq_right hc]
    rw [List.map_congr_left e]
    exact rows_le rows (fun r hr => ⟨lt_of_lt_of_le (by norm_num) (hbd r hr).1, (hbd r hr).2.2⟩)
      htab _ _ (Real.log_natCast_nonneg p) rows (fun r hr => hr) hpw
  have hs := LG.lsum_swap rows ((range (19 * n + 1)).filter (Eligible n)) fun r p => (r.2.2 : ℝ) * ∑ k ∈ range 8,
    (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p else 0)
  beta_reduce at hs
  rw [hs] at step1
  have step3 := LG.lsum_le rows
    (fun r => (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1) - ε') * n)
    (fun r => ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
        else 0))
    fun r hr => by
      rw [← Finset.mul_sum, Finset.sum_comm]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => hn r hr k hk)
        (Nat.cast_nonneg _)
  have e4 : ∀ r : ℚ × ℚ × ℕ, (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1) - ε') * n =
      ((r.2.2 : ℝ) * ∑ k ∈ range 8, (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))) * n -
        (ε' * n) * ((r.2.2 : ℝ) * 8) := fun r => by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [List.map_congr_left fun r _ => e4 r, LG.lsum_lin] at step3
  have hfin : ((rows.map fun r => (r.2.2 : ℝ) * ∑ k ∈ range 8,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))).sum - ε) * n ≤
        (rows.map fun r => (r.2.2 : ℝ) * ∑ k ∈ range 8,
          (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))).sum * n - ε' * n * K := by
    have := mul_le_mul_of_nonneg_right hεK (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  exact hfin.trans (step3.trans step1)


/-- The upper harmonic ranges. -/
theorem harmonic_gen (hP : PNT) (hE : EXC) : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (6 - ε) * n ≤ ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), (hgain n p : ℝ) * Real.log p := by
  intro ε hε
  filter_upwards [elig_interval_nat hP hE 18 19 (by norm_num) (by norm_num) le_rfl
      (ε / 6) (by positivity),
    elig_interval_nat hP hE 17 18 (by norm_num) (by norm_num) (by norm_num)
      (ε / 6) (by positivity),
    elig_interval_nat hP hE 16 17 (by norm_num) (by norm_num) (by norm_num)
      (ε / 6) (by positivity)]
    with n h1 h2 h3
  have e : ∀ p ∈ (range (19 * n + 1)).filter (Eligible n), (hgain n p : ℝ) * Real.log p =
      3 * (if 18 * n < p ∧ p < 19 * n then Real.log p else 0) +
        2 * (if 17 * n < p ∧ p < 18 * n then Real.log p else 0) +
          (if 16 * n < p ∧ p < 17 * n then Real.log p else 0) := fun p _ => by
    unfold hgain
    split_ifs <;> first | omega | (push_cast; ring)
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  push_cast at h1 h2 h3
  linarith


/-- The residue block. -/
theorem block_gen (hP : PNT) (hE : EXC) : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (3 - ε) * n ≤ ∑ p ∈ (range (19 * n + 1)).filter (Eligible n), (sgain n p : ℝ) * Real.log p := by
  intro ε hε
  filter_upwards [elig_interval_nat hP hE 8 11 (by norm_num) (by norm_num) (by norm_num) ε hε] with n h
  have e : ∀ p ∈ (range (19 * n + 1)).filter (Eligible n), (sgain n p : ℝ) * Real.log p =
      if 8 * n < p ∧ p < 11 * n then Real.log p else 0 := fun p _ => by
    unfold sgain
    by_cases hc : 8 * n < p ∧ p < 11 * n
    · rw [ite_eq_left hc, ite_eq_left hc, Nat.cast_one, one_mul]
    · rw [ite_eq_right hc, ite_eq_right hc, Nat.cast_zero, zero_mul]
  rw [Finset.sum_congr rfl e]
  push_cast at h
  linarith


end Pfq54.LG2
