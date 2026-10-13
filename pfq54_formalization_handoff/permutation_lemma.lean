/-
# Blueprint of `permutation_lemma` (manuscript eq. (permutation), Lemma `arith-integral`)

Node `Pfq54.permutation_lemma` of `Blueprint_pfq54.lean`: for every permutation `b` of
`(-2,-1,0,1,2)`, `𝒯^b_{n,j} = λ_{n,b} 𝒯_{n,j}` as jets (`j ≤ 17n`), and
`λ_{n,b} U_{n,j}`, `D_n λ_{n,b} V_{n,j}`, `λ_{n,b} Z_{i,n}` are integers.

Proof (manuscript §7): "Expansion into Gamma factors". Every binomial jet factors through the
jets of `Γ(x+1-ε)` and `1/Γ(x+1∓ε)`, normalized by `e^{∓γε}` so that Euler's constant drops out
(`gJet`, `rgJet`, `rgpJet`; lemmas [1], [2]). Then `𝒯^b` is a constant times the `b`-independent
`core` jet, because the five factors `1/Γ(j - b_i n + 1 - ε)` are merely permuted ([3]); `𝒯` is
the reference permutation `b = (0,-1,-2,1,2)` ([4]); and `λ_{n,b}` is the quotient of the two
constants ([5], [6]). The integrality proof of Proposition 2 applies verbatim to `𝒯^b` ([7]).
-/
import Z_integral

open Finset

noncomputable section

namespace Pfq54.BP

open Pfq54

/-- Jet of `ε ↦ e^{-γε} Γ(x+1-ε)` at `ε = 0`: `(x!, -x! H_x)`. -/
def gJet (x : ℕ) : Jet := jet (x.factorial : ℚ) (-(x.factorial : ℚ) * harm 1 x)

/-- Jet of `ε ↦ e^{γε} / Γ(x+1-ε)`: `(1/x!, H_x/x!)` for `x ≥ 0`, and `(0, (-1)^{-x} (-x-1)!)`
for `x < 0` (simple zero of `1/Γ`). -/
def rgJet (x : ℤ) : Jet :=
  if 0 ≤ x then jet ((x.toNat.factorial : ℚ)⁻¹) (harm 1 x.toNat / x.toNat.factorial)
  else jet 0 ((-1 : ℚ) ^ (-x).toNat * ((-x).toNat - 1).factorial)

/-- Jet of `ε ↦ e^{-γε} / Γ(y+1+ε)`: `(1/y!, -H_y/y!)` for `y ≥ 0`, and
`(0, (-1)^{-y-1} (-y-1)!)` for `y < 0`. -/
def rgpJet (y : ℤ) : Jet :=
  if 0 ≤ y then jet ((y.toNat.factorial : ℚ)⁻¹) (-harm 1 y.toNat / y.toNat.factorial)
  else jet 0 ((-1 : ℚ) ^ ((-y).toNat - 1) * ((-y).toNat - 1).factorial)

/-- The permutation-invariant part of `𝒯^b_{n,j}`:
`∏_{i=0}^{2} Γ(j+(10+i)n+1-ε) · ∏_{k} 1/Γ(j - s_k n + 1 - ε) · 1/Γ(16n-j+1+ε) Γ(17n-j+1+ε)`
(all `γ`-normalized), `s = (-2,-1,0,1,2)`. -/
def core (n j : ℕ) : Jet :=
  gJet (j + 10 * n) * gJet (j + 11 * n) * gJet (j + 12 * n) *
    (∏ k : Fin 5, rgJet ((j : ℤ) - shift k * n)) *
    rgpJet (16 * n - (j : ℤ)) * rgpJet (17 * n - (j : ℤ))

/-- The constant factorials of `𝒯^b`: `((16-b₃)n)! ((17-b₄)n)! / ∏_{i=0}^{2} ((10+i+b_i)n)!`. -/
def permConst (σ : Equiv.Perm (Fin 5)) (n : ℕ) : ℚ :=
  let b : Fin 5 → ℤ := fun i => shift (σ i)
  let fac : ℤ → ℚ := fun e => ((e * n).toNat.factorial : ℚ)
  fac (16 - b 3) * fac (17 - b 4) / (fac (10 + b 0) * fac (11 + b 1) * fac (12 + b 2))

/-- **[1] Upper jets through Gamma jets.**
`C(N-ε, M) = Γ(N+1-ε) / (M! Γ(N-M+1-ε))`, i.e. `upperJet N M = (1/M!) • gJet N * rgJet (N-M)`.
* Estimated proof length: ≈ 20 lines (two cases `M ≤ N`, `N < M`; `TrivSqZeroExt.ext`,
  `Nat.choose_eq_factorial_div_factorial`, `field_simp`).
* Directly from the manuscript: partially (the manuscript expands into Gamma factors
  informally; the `γ`-normalization is not written out). -/
theorem upperJet_eq_gamma (N M : ℕ) :
    upperJet N M = (M.factorial : ℚ)⁻¹ • (gJet N * rgJet ((N : ℤ) - M)) := by
  have hM : (M.factorial : ℚ) ≠ 0 := by positivity
  unfold upperJet gJet rgJet
  by_cases h : M ≤ N
  · have h0 : (0 : ℤ) ≤ (N : ℤ) - M := by omega
    rw [ite_eq_left h, ite_eq_left h0, show ((N : ℤ) - M).toNat = N - M by omega]
    have hNM : ((N - M).factorial : ℚ) ≠ 0 := by positivity
    have hc : (N.choose M : ℚ) * M.factorial * (N - M).factorial = N.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst,
        smul_eq_mul, ← hc]
      field_simp
    · rw [TrivSqZeroExt.snd_smul, DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd,
        Aux.jet_snd, Aux.jet_snd, smul_eq_mul, ← hc]
      field_simp
      ring
  · have h0 : ¬ (0 : ℤ) ≤ (N : ℤ) - M := by omega
    rw [ite_eq_right h, ite_eq_right h0, show (-((N : ℤ) - M)).toNat = M - N by omega,
      show M - 1 - N = M - N - 1 by omega]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst,
        smul_eq_mul, mul_zero, mul_zero]
    · rw [TrivSqZeroExt.snd_smul, DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd,
        Aux.jet_snd, Aux.jet_snd, smul_eq_mul, mul_zero, add_zero]
      field_simp

/-- **[2] Lower jets through Gamma jets.**
`C(M, m-ε) = M! / (Γ(m+1-ε) Γ(M-m+1+ε))`, i.e. `lowerJet M m = M! • rgJet m * rgpJet (M-m)`.
* Estimated proof length: ≈ 25 lines (three cases `m < 0`, `0 ≤ m ≤ M`, `m > M`).
* Directly from the manuscript: partially (as for [1]). -/
theorem lowerJet_eq_gamma (M : ℕ) (m : ℤ) :
    lowerJet M m = (M.factorial : ℚ) • (rgJet m * rgpJet ((M : ℤ) - m)) := by
  unfold lowerJet rgJet rgpJet
  by_cases h1 : 0 ≤ m ∧ m ≤ M
  · rw [ite_eq_left h1, ite_eq_left h1.1, ite_eq_left (by omega : (0 : ℤ) ≤ (M : ℤ) - m),
      show ((M : ℤ) - m).toNat = M - m.toNat by omega]
    have hc : (M.choose m.toNat : ℚ) * m.toNat.factorial * (M - m.toNat).factorial =
        M.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
    have h2 : (m.toNat.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((M - m.toNat).factorial : ℚ) ≠ 0 := by positivity
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst,
        smul_eq_mul, ← hc]
      field_simp
    · rw [TrivSqZeroExt.snd_smul, DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd,
        Aux.jet_snd, Aux.jet_snd, smul_eq_mul, ← hc]
      field_simp
      ring
  rw [ite_eq_right h1]
  by_cases h2 : m < 0
  · rw [ite_eq_left h2, ite_eq_right (by omega : ¬ (0 : ℤ) ≤ m),
      ite_eq_left (by omega : (0 : ℤ) ≤ (M : ℤ) - m),
      show ((M : ℤ) - m).toNat = M + (-m).toNat by omega]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst,
        smul_eq_mul, zero_mul, mul_zero]
    · rw [TrivSqZeroExt.snd_smul, DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd,
        Aux.jet_snd, Aux.jet_snd, smul_eq_mul, zero_mul, zero_add]
      have : ((M + (-m).toNat).factorial : ℚ) ≠ 0 := by positivity
      field_simp
  · rw [ite_eq_right h2, ite_eq_left (by omega : (0 : ℤ) ≤ m),
      ite_eq_right (by omega : ¬ (0 : ℤ) ≤ (M : ℤ) - m),
      show (-((M : ℤ) - m)).toNat = (m - M).toNat by omega,
      show m.toNat = M + (m - M).toNat by omega]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_fst,
        smul_eq_mul, mul_zero, mul_zero]
    · rw [TrivSqZeroExt.snd_smul, DualNumber.snd_mul, Aux.jet_fst, Aux.jet_fst, Aux.jet_snd,
        Aux.jet_snd, Aux.jet_snd, smul_eq_mul, mul_zero, add_zero]
      have : ((M + (m - M).toNat).factorial : ℚ) ≠ 0 := by positivity
      field_simp

/-- **[3] Factorization of the permuted product.** `𝒯^b_{n,j} = permConst • core`: the five
lower Gamma factors `1/Γ(j - b_i n + 1 - ε)` are a permutation of `1/Γ(j - s_k n + 1 - ε)`
(`Equiv.prod_comp`), and the other varying factors do not depend on `b`.
* Uses: [1], [2].
* Estimated proof length: ≈ 35 lines (`Int.toNat_of_nonneg` for the lengths `(10+i+b_i)n ≥ 8n`,
  `(16-b₃)n`, `(17-b₄)n`; `smul_mul_smul`, `Fin.prod_univ_five`, `ring`).
* Directly from the manuscript: yes ("the five factors … are merely permuted"). -/
theorem coeffJetPerm_eq_core (σ : Equiv.Perm (Fin 5)) (n j : ℕ) :
    coeffJetPerm σ n j = permConst σ n • core n j := by
  have hb : ∀ i, -2 ≤ shift i ∧ shift i ≤ 2 := by intro i; fin_cases i <;> decide
  have hnn : ∀ e : ℤ, 0 ≤ e → ((e * n).toNat : ℤ) = e * n := fun e he =>
    Int.toNat_of_nonneg (mul_nonneg he (Int.natCast_nonneg n))
  unfold coeffJetPerm core permConst
  dsimp only
  rw [upperJet_eq_gamma, upperJet_eq_gamma, upperJet_eq_gamma, lowerJet_eq_gamma,
    lowerJet_eq_gamma, hnn _ (by linarith [(hb (σ 0)).1]), hnn _ (by linarith [(hb (σ 1)).1]),
    hnn _ (by linarith [(hb (σ 2)).1]), hnn _ (by linarith [(hb (σ 3)).2]),
    hnn _ (by linarith [(hb (σ 4)).2]),
    show ((j + 10 * n : ℕ) : ℤ) - (10 + shift (σ 0)) * n = j - shift (σ 0) * n by push_cast; ring,
    show ((j + 11 * n : ℕ) : ℤ) - (11 + shift (σ 1)) * n = j - shift (σ 1) * n by push_cast; ring,
    show ((j + 12 * n : ℕ) : ℤ) - (12 + shift (σ 2)) * n = j - shift (σ 2) * n by push_cast; ring,
    show (16 - shift (σ 3)) * (n : ℤ) - (j - shift (σ 3) * n) = 16 * n - j by ring,
    show (17 - shift (σ 4)) * (n : ℤ) - (j - shift (σ 4) * n) = 17 * n - j by ring,
    ← Equiv.prod_comp σ (fun k => rgJet ((j : ℤ) - shift k * n)), Fin.prod_univ_five]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  · ring
  · ring

/-- **[4] The reference permutation.** `𝒯_{n,j}` is `𝒯^b_{n,j}` for `b = (0,-1,-2,1,2)`,
i.e. for the transposition `σ = (0 2)`.
* Estimated proof length: ≈ 15 lines (`decide` for `shift ∘ σ`, `Finset.prod_Icc` expansion).
* Directly from the manuscript: yes ("The reference `C_n` corresponds to `b = (0,-1,-2,1,2)`"). -/
theorem coeffJet_eq_perm_ref (n j : ℕ) : coeffJet n j = coeffJetPerm (Equiv.swap 0 2) n j := by
  have e0 : shift (Equiv.swap (0 : Fin 5) 2 0) = 0 := by decide
  have e1 : shift (Equiv.swap (0 : Fin 5) 2 1) = -1 := by decide
  have e2 : shift (Equiv.swap (0 : Fin 5) 2 2) = -2 := by decide
  have e3 : shift (Equiv.swap (0 : Fin 5) 2 3) = 1 := by decide
  have e4 : shift (Equiv.swap (0 : Fin 5) 2 4) = 2 := by decide
  unfold coeffJet coeffJetPerm
  dsimp only
  rw [e0, e1, e2, e3, e4, Aux.prod_Icc_10_12, show ((10 + 0) * (n : ℤ)).toNat = 10 * n by omega,
    show ((11 + -1) * (n : ℤ)).toNat = 10 * n by omega,
    show ((12 + -2) * (n : ℤ)).toNat = 10 * n by omega,
    show ((16 - 1) * (n : ℤ)).toNat = 15 * n by omega,
    show ((17 - 2) * (n : ℤ)).toNat = 15 * n by omega, one_mul]

/-- **[5] The multiplier as a quotient of constants.**
`λ_{n,b} = permConst_b / permConst_ref`, with `permConst_ref = (15n)!²/(10n)!³`.
* Estimated proof length: ≈ 10 lines (`decide` for the reference shifts, `field_simp`).
* Directly from the manuscript: yes ("`λ_{n,b}` is exactly the ratio of the constant
  factorials"). -/
theorem lam_eq (σ : Equiv.Perm (Fin 5)) (n : ℕ) :
    lam σ n = permConst σ n / permConst (Equiv.swap 0 2) n := by
  have e0 : shift (Equiv.swap (0 : Fin 5) 2 0) = 0 := by decide
  have e1 : shift (Equiv.swap (0 : Fin 5) 2 1) = -1 := by decide
  have e2 : shift (Equiv.swap (0 : Fin 5) 2 2) = -2 := by decide
  have e3 : shift (Equiv.swap (0 : Fin 5) 2 3) = 1 := by decide
  have e4 : shift (Equiv.swap (0 : Fin 5) 2 4) = 2 := by decide
  unfold lam permConst
  dsimp only
  rw [e0, e1, e2, e3, e4, show ((10 + 0) * (n : ℤ)).toNat = 10 * n by omega,
    show ((11 + -1) * (n : ℤ)).toNat = 10 * n by omega,
    show ((12 + -2) * (n : ℤ)).toNat = 10 * n by omega,
    show ((16 - 1) * (n : ℤ)).toNat = 15 * n by omega,
    show ((17 - 2) * (n : ℤ)).toNat = 15 * n by omega,
    show (10 * (n : ℤ)).toNat = 10 * n by omega, show (15 * (n : ℤ)).toNat = 15 * n by omega]
  field_simp

/-- **[6]** The constants are nonzero (quotients of factorials).
* Estimated proof length: ≈ 4 lines (`positivity`).
* Directly from the manuscript: yes. -/
theorem permConst_ne_zero (σ : Equiv.Perm (Fin 5)) (n : ℕ) : permConst σ n ≠ 0 := by
  unfold permConst
  dsimp only
  positivity

/-- **[7] Integrality of the permuted jets** for `j ≤ 17n`: the polynomial factors have degree
`(10+i+b_i)n ≤ 14n`; each fixed-upper factor has `M = (16-b₃)n` or `(17-b₄)n` and lower
argument `m` with `M, m, M - m ≤ 19n`, so `upperJet_integral`, `lowerJet_integral`,
`jet_mul_integral` (from `Z_integral.lean`) apply with `L = 19n`.
* Estimated proof length: ≈ 25 lines.
* Directly from the manuscript: yes ("The proof of Proposition 2 applies to every
  permutation"). -/
theorem coeffJetPerm_integral (σ : Equiv.Perm (Fin 5)) (n j : ℕ) (hj : j ≤ 17 * n) :
    (∃ z : ℤ, (coeffJetPerm σ n j).fst = z) ∧
      ∃ z : ℤ, (D n : ℚ) * (coeffJetPerm σ n j).snd = z := by
  have hb : ∀ i, -2 ≤ shift i ∧ shift i ≤ 2 := by intro i; fin_cases i <;> decide
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  let Q : Jet → Prop := fun c => (∃ z : ℤ, c.fst = z) ∧ ∃ z : ℤ, (D n : ℚ) * c.snd = z
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := fun a b ha hb =>
    jet_mul_integral _ a b ha.1 ha.2 hb.1 hb.2
  have hup : ∀ (c : ℤ) (i : Fin 5) (N : ℕ), c ≤ 12 →
      Q (upperJet N ((c + shift (σ i)) * n).toNat) := fun c i N hc =>
    upperJet_integral _ _ _ (Int.toNat_le.mpr (by push_cast; nlinarith [hb (σ i)]))
  have hlo : ∀ (c : ℤ) (i : Fin 5), (c = 16 ∨ c = 17) →
      Q (lowerJet ((c - shift (σ i)) * n).toNat ((j : ℤ) - shift (σ i) * n)) := by
    intro c i hc
    have hb' := hb (σ i)
    have h0 : 0 ≤ (c - shift (σ i)) * (n : ℤ) := mul_nonneg (by omega) hn
    refine lowerJet_integral _ (19 * n) _
      (Int.toNat_le.mpr (by push_cast; rcases hc with rfl | rfl <;> nlinarith)) ?_ ?_
    · rw [Int.toNat_of_nonneg h0]; push_cast; rcases hc with rfl | rfl <;> nlinarith
    · push_cast; nlinarith
  unfold coeffJetPerm
  dsimp only
  exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hup 10 0 _ (by norm_num)) (hup 11 1 _ (by norm_num)))
    (hup 12 2 _ (by norm_num))) (hlo 16 3 (Or.inl rfl))) (hlo 17 4 (Or.inr rfl))

/-- **`permutation_lemma`** (node of `Blueprint_pfq54.lean`). Proved from [3]–[7] together with
`coeffJet_eq_zero` and `readout_integral` of `Z_integral.lean`. -/
theorem permutation_lemma (σ : Equiv.Perm (Fin 5)) (n : ℕ) (hn : 1 ≤ n) :
    (∀ j ≤ 17 * n, coeffJetPerm σ n j = lam σ n • coeffJet n j) ∧
      (∀ j, ∃ z : ℤ, lam σ n * U n j = z) ∧ (∀ j, ∃ z : ℤ, (D n : ℚ) * lam σ n * V n j = z) ∧
      ∀ i, ∃ z : ℤ, lam σ n * Zv n i = z := by
  have hid : ∀ j, coeffJetPerm σ n j = lam σ n • coeffJet n j := fun j => by
    rw [coeffJet_eq_perm_ref n j, coeffJetPerm_eq_core, coeffJetPerm_eq_core, smul_smul,
      lam_eq, div_mul_cancel₀ _ (permConst_ne_zero _ n)]
  have hU : ∀ j, ∃ z : ℤ, lam σ n * U n j = z := fun j => by
    rcases le_or_gt j (17 * n) with hj | hj
    · obtain ⟨z, hz⟩ := (coeffJetPerm_integral σ n j hj).1
      refine ⟨z, ?_⟩
      show lam σ n * (coeffJet n j).fst = _
      rw [← hz, hid j, TrivSqZeroExt.fst_smul, smul_eq_mul]
    · exact ⟨0, by simp [U, coeffJet_eq_zero n j hj]⟩
  have hV : ∀ j, ∃ z : ℤ, (D n : ℚ) * lam σ n * V n j = z := fun j => by
    rcases le_or_gt j (17 * n) with hj | hj
    · obtain ⟨z, hz⟩ := (coeffJetPerm_integral σ n j hj).2
      refine ⟨z, ?_⟩
      show (D n : ℚ) * lam σ n * (coeffJet n j).snd = _
      rw [← hz, hid j, TrivSqZeroExt.snd_smul, smul_eq_mul, mul_assoc]
    · exact ⟨0, by simp [V, coeffJet_eq_zero n j hj]⟩
  refine ⟨fun j _ => hid j, hU, hV, ?_⟩
  obtain ⟨h0, h3, h4⟩ := readout_integral n (fun j => lam σ n * U n j)
    (fun j => lam σ n * V n j) (fun j _ => hU j)
    (fun j _ => by obtain ⟨z, hz⟩ := hV j; exact ⟨z, by rw [← hz, mul_assoc]⟩)
  intro i
  fin_cases i
  · obtain ⟨z, hz⟩ := h0
    refine ⟨z, ?_⟩
    rw [← hz]
    show lam σ n * (6 * (D n : ℚ) ^ 4 * S0 n) = _
    simp only [S0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · obtain ⟨z, hz⟩ := h3
    refine ⟨z, ?_⟩
    rw [← hz]
    show lam σ n * (6 * (D n : ℚ) ^ 4 * S3 n) = _
    simp only [S3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · obtain ⟨z, hz⟩ := h4
    refine ⟨z, ?_⟩
    rw [← hz]
    show lam σ n * (6 * (D n : ℚ) ^ 4 * S4 n) = _
    simp only [S4, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

end Pfq54.BP
