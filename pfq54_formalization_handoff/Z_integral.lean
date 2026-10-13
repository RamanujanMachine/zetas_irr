/-
# Blueprint of `Z_integral` (manuscript Proposition 2, `integral`)

Node `Pfq54.Z_integral` of `Blueprint_pfq54.lean`: for `n ≥ 1` and all `j`,
`U_{n,j} ∈ ℤ`, `D_n V_{n,j} ∈ ℤ`, `Z_{i,n} = 6 D_n⁴ S_{i,n} ∈ ℤ`, and `S_{0,n} > 0`.

Proof (manuscript §6): each binomial jet has integral value and its derivative is cleared by
`d_L` for suitable `L` ([1] polynomial binomials via Vandermonde, [2] fixed-upper binomials via
the digamma identity and the simple zeros of `1/Γ`); jets with these two properties are closed
under products ([3]); for `j ≤ 17n` all the relevant `L` are `≤ 19n` ([5]), and for `j > 17n`
the jet vanishes ([4]). The harmonic numbers are cleared by `d_M^r H^{(r)}_m ∈ ℤ` ([6]), which
gives the integrality of the three readouts ([7]). Positivity: `U_{n,j} ≥ 0` ([8]) and
`U_{n,2n} = E_n > 0` ([9]).

`d_L = lcm(1,…,L)` is written `(Icc 1 L).lcm id`, so that `D n = d_{19n}` definitionally.
-/
import hyp_readout

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- **[1] Upper jets.** The jet of `ε ↦ C(N - ε, M)` has integral value, and its derivative
is cleared by `d_L` for every `L ≥ M`: `d/dx C(x,M)|_{x=N} = ∑_{h=1}^{M} C(N, M-h) (-1)^{h-1}/h`.
* Estimated proof length: ≈ 35 lines (case `M ≤ N`: `C(N,M)(H_N - H_{N-M})` as the Vandermonde
  sum; case `N < M`: `N!(M-1-N)!/M! = 1/(M·C(M-1,N))` and `M·C(M-1,N) ∣ d_M`).
* Directly from the manuscript: yes (proof of Proposition 2). -/
theorem upperJet_integral (N M L : ℕ) (hML : M ≤ L) :
    (∃ z : ℤ, (upperJet N M).fst = z) ∧
      ∃ z : ℤ, (((Icc 1 L).lcm id : ℕ) : ℚ) * (upperJet N M).snd = z := by
  refine ⟨⟨N.choose M, by rw [fst_upperJet]; exact (Int.cast_natCast _).symm⟩, ?_⟩
  unfold upperJet
  split_ifs with h
  · set L' := (Icc 1 L).lcm id
    rw [Aux.jet_snd, Aux.harm_sub N M h]
    have key : ∀ s ∈ range M, (L' : ℚ) * ((N.choose M : ℚ) * (1 / ((N - s : ℕ) : ℚ))) =
        ((N.choose s * (N - s - 1).choose (M - s - 1) * (L' / ((s + 1) * M.choose (s + 1))) :
          ℕ) : ℚ) := by
      intro s hs
      have hs' := mem_range.mp hs
      have h1 := Nat.choose_mul (n := N) (k := M) (s := s + 1) (by omega)
      have h2 := Nat.choose_succ_right_eq N s
      have hid : (s + 1) * M.choose (s + 1) * N.choose M =
          (N - s) * (N.choose s * (N - s - 1).choose (M - s - 1)) := by
        rw [show N - s - 1 = N - (s + 1) by omega, show M - s - 1 = M - (s + 1) by omega]
        calc (s + 1) * M.choose (s + 1) * N.choose M
            = (s + 1) * (N.choose M * M.choose (s + 1)) := by ring
          _ = (s + 1) * (N.choose (s + 1) * (N - (s + 1)).choose (M - (s + 1))) := by rw [h1]
          _ = (N.choose (s + 1) * (s + 1)) * (N - (s + 1)).choose (M - (s + 1)) := by ring
          _ = _ := by rw [h2]; ring
      obtain ⟨q, hq⟩ := (Aux.mul_choose_dvd_lcm (by omega) (by omega : s + 1 ≤ M)).trans
        (Aux.lcm_dvd_lcm hML)
      have hK : 0 < (s + 1) * M.choose (s + 1) :=
        Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
      have hq' : L' = (s + 1) * M.choose (s + 1) * q := hq
      rw [hq', Nat.mul_div_cancel_left q hK]
      have hNs : ((N - s : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hcast : (((s + 1) * M.choose (s + 1) : ℕ) : ℚ) * (N.choose M : ℚ) =
          ((N - s : ℕ) : ℚ) * ((N.choose s * (N - s - 1).choose (M - s - 1) : ℕ) : ℚ) := by
        exact_mod_cast hid
      calc ((((s + 1) * M.choose (s + 1)) * q : ℕ) : ℚ) *
            ((N.choose M : ℚ) * (1 / ((N - s : ℕ) : ℚ)))
          = (q : ℚ) * ((((s + 1) * M.choose (s + 1) : ℕ) : ℚ) * (N.choose M : ℚ)) /
              ((N - s : ℕ) : ℚ) := by rw [Nat.cast_mul _ q]; ring
        _ = (q : ℚ) * (((N - s : ℕ) : ℚ) *
              ((N.choose s * (N - s - 1).choose (M - s - 1) : ℕ) : ℚ)) /
              ((N - s : ℕ) : ℚ) := by rw [hcast]
        _ = _ := by rw [Nat.cast_mul _ q]; field_simp
    refine ⟨-∑ s ∈ range M, ((N.choose s * (N - s - 1).choose (M - s - 1) *
      (L' / ((s + 1) * M.choose (s + 1))) : ℕ) : ℤ), ?_⟩
    rw [Int.cast_neg, Int.cast_sum, neg_mul, mul_neg, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s hs => by rw [Int.cast_natCast]; exact key s hs
  · obtain ⟨z, hz⟩ := Aux.lcm_mul_inv_choose N (M - N) L (by omega) (by omega)
    rw [show N + (M - N) = M by omega, show M - N - 1 = M - 1 - N by omega] at hz
    refine ⟨(-1) ^ (M - N) * z, ?_⟩
    rw [Aux.jet_snd, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← hz]
    ring

/-- **[2] Lower jets.** The jet of `ε ↦ C(M, m - ε)` has integral value; its derivative is
cleared by `d_L` whenever `M ≤ L` and `m` lies at most `L - M` outside `[0, M]`
(interior: `C(M,m)(H_m - H_{M-m})`; exterior `m = -r` or `m = M + r`: `±M!(r-1)!/(M+r)!`,
the derivative of `C(x, M+r)` at `x = r - 1`, cleared by `d_{M+r}`).
* Estimated proof length: ≈ 40 lines (three cases; `r·C(M+r, r) ∣ d_{M+r}`).
* Directly from the manuscript: yes (proof of Proposition 2). -/
theorem lowerJet_integral (M L : ℕ) (m : ℤ) (h1 : M ≤ L) (h2 : -m ≤ (L : ℤ) - M)
    (h3 : m ≤ L) :
    (∃ z : ℤ, (lowerJet M m).fst = z) ∧
      ∃ z : ℤ, (((Icc 1 L).lcm id : ℕ) : ℚ) * (lowerJet M m).snd = z := by
  refine ⟨?_, ?_⟩
  · rw [fst_lowerJet]
    split_ifs
    · exact ⟨M.choose m.toNat, (Int.cast_natCast _).symm⟩
    · exact ⟨0, Int.cast_zero.symm⟩
  unfold lowerJet
  split_ifs with ha hb
  · obtain ⟨z1, hz1⟩ := Aux.harm_int 1 m.toNat L (by omega)
    obtain ⟨z2, hz2⟩ := Aux.harm_int 1 (M - m.toNat) L (by omega)
    rw [pow_one] at hz1 hz2
    refine ⟨(M.choose m.toNat : ℤ) * (z1 - z2), ?_⟩
    rw [Aux.jet_snd, Int.cast_mul, Int.cast_sub, ← hz1, ← hz2, Int.cast_natCast]
    ring
  · obtain ⟨z, hz⟩ := Aux.lcm_mul_inv_choose M (-m).toNat L (by omega) (by omega)
    refine ⟨(-1) ^ (-m).toNat * z, ?_⟩
    rw [Aux.jet_snd, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← hz]
    ring
  · obtain ⟨z, hz⟩ := Aux.lcm_mul_inv_choose M (m - M).toNat L (by omega) (by omega)
    refine ⟨(-1) ^ ((m - M).toNat - 1) * z, ?_⟩
    rw [Aux.jet_snd, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← hz]
    ring

/-- **[3] Product rule.** If two jets have integral values and `d`-cleared derivatives, so does
their product (`(a,a')(b,b') = (ab, a'b + ab')`).
* Estimated proof length: ≈ 12 lines.
* Directly from the manuscript: yes ("The product rule proves `D_n V_{n,j} ∈ ℤ`"). -/
theorem jet_mul_integral (d : ℚ) (a b : Jet) (ha : ∃ z : ℤ, a.fst = z)
    (ha' : ∃ z : ℤ, d * a.snd = z) (hb : ∃ z : ℤ, b.fst = z) (hb' : ∃ z : ℤ, d * b.snd = z) :
    (∃ z : ℤ, (a * b).fst = z) ∧ ∃ z : ℤ, d * (a * b).snd = z := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨x', hx'⟩ := ha'
  obtain ⟨y, hy⟩ := hb
  obtain ⟨y', hy'⟩ := hb'
  refine ⟨⟨x * y, by rw [TrivSqZeroExt.fst_mul, hx, hy, Int.cast_mul]⟩, ⟨x * y' + x' * y, ?_⟩⟩
  rw [DualNumber.snd_mul, Int.cast_add, Int.cast_mul, Int.cast_mul, ← hx, ← hy, ← hx', ← hy']
  ring

/-- **[4] Vanishing beyond `17n`.** For `j > 17n` both fixed-upper factors `C(15n, j-n-ε)` and
`C(15n, j-2n-ε)` vanish at `ε = 0`, so their product, hence the whole jet, is `0` (`ε² = 0`).
* Estimated proof length: ≈ 15 lines.
* Directly from the manuscript: yes ("For `j > 17n` … `U_{n,j} = V_{n,j} = 0`"). -/
theorem coeffJet_eq_zero (n j : ℕ) (hj : 17 * n < j) : coeffJet n j = 0 := by
  unfold coeffJet
  set P := ∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n)
  have h1 : (lowerJet (15 * n) ((j : ℤ) - n)).fst = 0 := by
    rw [fst_lowerJet]; exact ite_eq_right (by omega)
  have h2 : (lowerJet (15 * n) ((j : ℤ) - 2 * n)).fst = 0 := by
    rw [fst_lowerJet]; exact ite_eq_right (by omega)
  have h3 : (P * lowerJet (15 * n) ((j : ℤ) - n)).fst = 0 := by
    rw [TrivSqZeroExt.fst_mul, h1, mul_zero]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, h2, mul_zero]; rfl
  · rw [DualNumber.snd_mul, h3, h2, zero_mul, mul_zero, add_zero]; rfl

/-- **[5] Integrality of the coefficient jet** for `j ≤ 17n`: the polynomial factors have
degree `10n ≤ 19n`; the fixed-upper factors have `M = 15n` and lower arguments at most `2n`
outside `[0, 15n]`, so [1]–[3] apply with `L = 19n`.
* Uses: [1], [2], [3].
* Estimated proof length: ≈ 20 lines.
* Directly from the manuscript: yes. -/
theorem coeffJet_integral (n j : ℕ) (hj : j ≤ 17 * n) :
    (∃ z : ℤ, (coeffJet n j).fst = z) ∧ ∃ z : ℤ, (D n : ℚ) * (coeffJet n j).snd = z := by
  let Q : Jet → Prop := fun c => (∃ z : ℤ, c.fst = z) ∧ ∃ z : ℤ, (D n : ℚ) * c.snd = z
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := fun a b ha hb =>
    jet_mul_integral _ a b ha.1 ha.2 hb.1 hb.2
  have hone : Q 1 := ⟨⟨1, by rw [TrivSqZeroExt.fst_one, Int.cast_one]⟩,
    ⟨0, by rw [TrivSqZeroExt.snd_one, mul_zero, Int.cast_zero]⟩⟩
  have hP : Q (∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n)) :=
    Finset.prod_induction _ Q hmul hone fun u _ => upperJet_integral _ _ _ (by omega)
  have hl1 : Q (lowerJet (15 * n) ((j : ℤ) - n)) :=
    lowerJet_integral (15 * n) (19 * n) _ (by omega) (by push_cast; omega) (by push_cast; omega)
  have hl2 : Q (lowerJet (15 * n) ((j : ℤ) - 2 * n)) :=
    lowerJet_integral (15 * n) (19 * n) _ (by omega) (by push_cast; omega) (by push_cast; omega)
  exact hmul _ _ (hmul _ _ hP hl1) hl2

/-- **[6] Harmonic integrality** (harmonic-integrality): `d_M^r H^{(r)}_m ∈ ℤ` for `m ≤ M`,
since `d_M^r H^{(r)}_m = ∑_{k ≤ m} (d_M/k)^r`.
* Proof length: 10 lines. Proved below (the `p`-adic form is `harm_valuation` in `blueprints/valuation_bound.lean`).
* Directly from the manuscript: yes. -/
theorem harm_integral (r m M : ℕ) (h : m ≤ M) :
    ∃ z : ℤ, (((Icc 1 M).lcm id : ℕ) : ℚ) ^ r * harm r m = z := by
  set L := (Icc 1 M).lcm id
  have hdiv : ∀ k ∈ Icc 1 m, k ∣ L := fun k hk => by
    have : k ∈ Icc 1 M := by simp only [Finset.mem_Icc] at hk ⊢; omega
    simpa using Finset.dvd_lcm (f := id) this
  refine ⟨∑ k ∈ Icc 1 m, ((L / k : ℕ) : ℤ) ^ r, ?_⟩
  rw [harm, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [Nat.cast_div (hdiv k hk) hk0, div_pow, mul_one_div]

/-- **[7] Integrality of the three readouts.** If `u_j ∈ ℤ` and `D_n v_j ∈ ℤ` for `j ≤ 17n`,
then `6 D_n⁴ ∑ u_j`, `6 D_n⁴ ∑ (u_j H^{(3)}_{j+2n} + v_j H^{(2)}_{j+2n}/2)` and
`6 D_n⁴ ∑ (u_j H^{(4)}_{j+2n} + v_j H^{(3)}_{j+2n}/3)` are integers (`j + 2n ≤ 19n`; one power
of `D_n` clears `v_j`, three clear the harmonic number, `6` clears `1/2, 1/3`).
* Uses: [6].
* Estimated proof length: ≈ 30 lines (subring `(Int.castRingHom ℚ).range`, `Subring.sum_mem`).
* Directly from the manuscript: yes. -/
theorem readout_integral (n : ℕ) (u v : ℕ → ℚ) (hu : ∀ j ≤ 17 * n, ∃ z : ℤ, u j = z)
    (hv : ∀ j ≤ 17 * n, ∃ z : ℤ, (D n : ℚ) * v j = z) :
    (∃ z : ℤ, 6 * (D n : ℚ) ^ 4 * ∑ j ∈ range (17 * n + 1), u j = z) ∧
      (∃ z : ℤ, 6 * (D n : ℚ) ^ 4 * ∑ j ∈ range (17 * n + 1),
        (u j * harm 3 (j + 2 * n) + v j * harm 2 (j + 2 * n) / 2) = z) ∧
      ∃ z : ℤ, 6 * (D n : ℚ) ^ 4 * ∑ j ∈ range (17 * n + 1),
        (u j * harm 4 (j + 2 * n) + v j * harm 3 (j + 2 * n) / 3) = z := by
  set R := (Int.castRingHom ℚ).range
  have mem : ∀ x : ℚ, (∃ z : ℤ, x = z) → x ∈ R := fun x ⟨z, hz⟩ => ⟨z, hz.symm⟩
  have out : ∀ x : ℚ, x ∈ R → ∃ z : ℤ, x = z := fun x ⟨z, hz⟩ => ⟨z, hz.symm⟩
  have hD : (D n : ℚ) ∈ R := ⟨D n, map_natCast _ _⟩
  have hk : ∀ k : ℕ, (k : ℚ) ∈ R := fun k => ⟨k, map_natCast _ _⟩
  have h6 : (6 : ℚ) ∈ R := by exact_mod_cast hk 6
  have h3 : (3 : ℚ) ∈ R := by exact_mod_cast hk 3
  have h2 : (2 : ℚ) ∈ R := by exact_mod_cast hk 2
  have hH : ∀ r j, j ≤ 17 * n → (D n : ℚ) ^ r * harm r (j + 2 * n) ∈ R := fun r j hj =>
    mem _ (harm_integral r (j + 2 * n) (19 * n) (by omega))
  have hj : ∀ j ∈ range (17 * n + 1), j ≤ 17 * n := fun j hj => by
    have := mem_range.mp hj; omega
  refine ⟨out _ ?_, out _ ?_, out _ ?_⟩
  · exact R.mul_mem (R.mul_mem h6 (R.pow_mem hD 4))
      (R.sum_mem fun j hj' => mem _ (hu j (hj j hj')))
  · rw [Finset.mul_sum]
    refine R.sum_mem fun j hj' => ?_
    rw [show 6 * (D n : ℚ) ^ 4 * (u j * harm 3 (j + 2 * n) + v j * harm 2 (j + 2 * n) / 2) =
      6 * D n * u j * (D n ^ 3 * harm 3 (j + 2 * n)) +
        3 * D n * (D n * v j) * (D n ^ 2 * harm 2 (j + 2 * n)) by ring]
    exact R.add_mem (R.mul_mem (R.mul_mem (R.mul_mem h6 hD) (mem _ (hu j (hj j hj'))))
        (hH 3 j (hj j hj')))
      (R.mul_mem (R.mul_mem (R.mul_mem h3 hD) (mem _ (hv j (hj j hj')))) (hH 2 j (hj j hj')))
  · rw [Finset.mul_sum]
    refine R.sum_mem fun j hj' => ?_
    rw [show 6 * (D n : ℚ) ^ 4 * (u j * harm 4 (j + 2 * n) + v j * harm 3 (j + 2 * n) / 3) =
      6 * u j * (D n ^ 4 * harm 4 (j + 2 * n)) +
        2 * (D n * v j) * (D n ^ 3 * harm 3 (j + 2 * n)) by ring]
    exact R.add_mem (R.mul_mem (R.mul_mem h6 (mem _ (hu j (hj j hj')))) (hH 4 j (hj j hj')))
      (R.mul_mem (R.mul_mem h2 (mem _ (hv j (hj j hj')))) (hH 3 j (hj j hj')))

/-- **[8] Nonnegativity.** `U_{n,j} ≥ 0`: it is a product of binomial coefficients.
* Uses: `fst_upperJet`, `fst_lowerJet` (from `hyp_readout.lean`).
* Estimated proof length: ≈ 10 lines.
* Directly from the manuscript: yes. -/
theorem U_nonneg (n j : ℕ) : 0 ≤ U n j := by
  unfold U coeffJet
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul, Aux.fst_prod, fst_lowerJet, fst_lowerJet]
  refine mul_nonneg (mul_nonneg (prod_nonneg fun u _ => ?_) ?_) ?_
  · rw [fst_upperJet]; exact Nat.cast_nonneg _
  · split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  · split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl

/-- **[9] The leading term.** `U_{n,2n} = B_{n,0} = E_n > 0` for `n ≥ 1`.
* Uses: `U_two_n_add` (from `hyp_readout.lean`), `Nat.choose_pos`.
* Estimated proof length: ≈ 8 lines.
* Directly from the manuscript: yes ("Since `B_{n,0} = E_n`"). -/
theorem U_two_n_pos (n : ℕ) (hn : 1 ≤ n) : 0 < U n (2 * n) := by
  have h := U_two_n_add n 0 (Nat.zero_le _)
  rw [Nat.add_zero] at h
  rw [h, Bnk]
  exact Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
    (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega)))
    (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega)))

/-- **`Z_integral`** (node of `Blueprint_pfq54.lean`, Proposition 2). Proved from [4], [5],
[7], [8], [9]. -/
theorem Z_integral (n : ℕ) (hn : 1 ≤ n) :
    (∀ j, ∃ z : ℤ, U n j = z) ∧ (∀ j, ∃ z : ℤ, (D n : ℚ) * V n j = z) ∧
      (∀ i, ∃ z : ℤ, Zv n i = z) ∧ 0 < S0 n := by
  have hU : ∀ j, ∃ z : ℤ, U n j = z := fun j => by
    rcases le_or_gt j (17 * n) with hj | hj
    · exact (coeffJet_integral n j hj).1
    · exact ⟨0, by simp [U, coeffJet_eq_zero n j hj]⟩
  have hV : ∀ j, ∃ z : ℤ, (D n : ℚ) * V n j = z := fun j => by
    rcases le_or_gt j (17 * n) with hj | hj
    · exact (coeffJet_integral n j hj).2
    · exact ⟨0, by simp [V, coeffJet_eq_zero n j hj]⟩
  refine ⟨hU, hV, ?_, ?_⟩
  · obtain ⟨h0, h3, h4⟩ := readout_integral n (U n) (V n) (fun j _ => hU j) (fun j _ => hV j)
    intro i
    fin_cases i
    · exact h0
    · exact h3
    · exact h4
  · exact Finset.sum_pos' (fun j _ => U_nonneg n j)
      ⟨2 * n, Finset.mem_range.mpr (by omega), U_two_n_pos n hn⟩

end Pfq54.BP
