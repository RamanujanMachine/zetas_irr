/-
# Definitions for the forward `₅F₄` blueprint

All definitions of `Blueprint_pfq54.lean`, shared by that file and by the node blueprints
(`hyp_readout.lean`, `Z_integral.lean`, …) in this folder. There are no theorems here.
-/
import Mathlib

open Filter Topology Real Finset
open scoped Matrix

noncomputable section

namespace Pfq54

/-! ## §0. Zeta values -/

/-- `ζ(3)` as a real number. -/
def ζ3 : ℝ := (riemannZeta 3).re

/-- `ζ(4)` as a real number. -/
def ζ4 : ℝ := (riemannZeta 4).re

/-- The target `α_{A,B} = A ζ(3) + B ζ(4)`. -/
def alpha (A B : ℤ) : ℝ := A * ζ3 + B * ζ4

/-! ## §2. The forward hypergeometric trajectory (§2–3 of the manuscript)

Start `x₀ = (0,0,1,1,1;1,1,1,1)`, direction `v_F = (-14,-15,13,14,12;1,2,3,4)`; at depth `n`
the parameters are `a_n = (-14n,-15n,1+13n,1+14n,1+12n)`, `b_n = (1+n,1+2n,1+3n,1+4n)`. -/

/-- Pochhammer symbol `(x)_k = x (x+1) ⋯ (x+k-1)`. -/
def poch (x : ℚ) (k : ℕ) : ℚ := ∏ i ∈ range k, (x + i)

/-- The coefficient `t_{n,k}` of `z^k` in `𝓕_n(z) = ₅F₄(a_n; b_n; z)`. -/
def hypTerm (n k : ℕ) : ℚ :=
  (poch (-(14 * n : ℚ)) k * poch (-(15 * n : ℚ)) k * poch (1 + 13 * n) k *
      poch (1 + 14 * n) k * poch (1 + 12 * n) k) /
    ((k.factorial : ℚ) * poch (1 + n) k * poch (1 + 2 * n) k * poch (1 + 3 * n) k *
      poch (1 + 4 * n) k)

/-- The terminating value `𝓕_n(1) = ∑_{k=0}^{14n} t_{n,k}`. -/
def hyp (n : ℕ) : ℚ := ∑ k ∈ range (14 * n + 1), hypTerm n k

/-- The coefficient multiplier (E): `E_n = C(12n,10n) C(13n,10n) C(14n,10n) C(15n,n)`. -/
def E (n : ℕ) : ℕ :=
  (12 * n).choose (10 * n) * (13 * n).choose (10 * n) * (14 * n).choose (10 * n) *
    (15 * n).choose n

/-! ## §3. Harmonic readouts and the integer normalization (§5–6 of the manuscript)

A *jet* is a pair (value, first `ε`-derivative at `ε = 0`), i.e. a dual number; jets multiply
by `(a,a')(b,b') = (ab, a'b + ab')`. The explicit rational jets below avoid the Gamma function
(`PROOF_STRUCTURE.md`, §C). -/

/-- Jets: dual numbers over `ℚ`. -/
abbrev Jet := DualNumber ℚ

/-- The jet with value `a` and derivative `a'`. -/
def jet (a a' : ℚ) : Jet := TrivSqZeroExt.inl a + TrivSqZeroExt.inr a'

/-- Generalised harmonic number `H^{(r)}_m = ∑_{k=1}^m k^{-r}`. -/
def harm (r m : ℕ) : ℚ := ∑ k ∈ Icc 1 m, 1 / (k : ℚ) ^ r

/-- Upper jet: the jet of `ε ↦ C(N - ε, M)` (binomial polynomial in the upper argument). -/
def upperJet (N M : ℕ) : Jet :=
  if M ≤ N then jet (N.choose M) (-(N.choose M : ℚ) * (harm 1 N - harm 1 (N - M)))
  else jet 0 ((-1 : ℚ) ^ (M - N) * N.factorial * (M - 1 - N).factorial / M.factorial)

/-- Lower jet: the jet of `ε ↦ C(M, m - ε) = M!/(Γ(m-ε+1) Γ(M-m+ε+1))`. -/
def lowerJet (M : ℕ) (m : ℤ) : Jet :=
  if 0 ≤ m ∧ m ≤ M then
    jet (M.choose m.toNat) (M.choose m.toNat * (harm 1 m.toNat - harm 1 (M - m.toNat)))
  else if m < 0 then
    jet 0 ((-1 : ℚ) ^ (-m).toNat * M.factorial * ((-m).toNat - 1).factorial /
      (M + (-m).toNat).factorial)
  else
    jet 0 ((-1 : ℚ) ^ ((m - M).toNat - 1) * M.factorial * ((m - M).toNat - 1).factorial /
      (M + (m - M).toNat).factorial)

/-- The jet of the five-binomial product (T):
`𝒯_{n,j}(ε) = ∏_{u=10}^{12} C(j+un-ε, 10n) · C(15n, j-n-ε) · C(15n, j-2n-ε)`. -/
def coeffJet (n j : ℕ) : Jet :=
  (∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n)) *
    lowerJet (15 * n) ((j : ℤ) - n) * lowerJet (15 * n) ((j : ℤ) - 2 * n)

/-- `U_{n,j} = 𝒯_{n,j}(0)`. -/
def U (n j : ℕ) : ℚ := (coeffJet n j).fst

/-- `V_{n,j} = 𝒯'_{n,j}(0)`. -/
def V (n j : ℕ) : ℚ := (coeffJet n j).snd

/-- (S0): `S_{0,n} = ∑_j U_{n,j}` (the terms vanish outside `n ≤ j ≤ 17n`). -/
def S0 (n : ℕ) : ℚ := ∑ j ∈ range (17 * n + 1), U n j

/-- (S3): `S_{3,n} = ∑_j (U_{n,j} H^{(3)}_{j+2n} + V_{n,j} H^{(2)}_{j+2n} / 2)`. -/
def S3 (n : ℕ) : ℚ :=
  ∑ j ∈ range (17 * n + 1), (U n j * harm 3 (j + 2 * n) + V n j * harm 2 (j + 2 * n) / 2)

/-- (S4): `S_{4,n} = ∑_j (U_{n,j} H^{(4)}_{j+2n} + V_{n,j} H^{(3)}_{j+2n} / 3)`. -/
def S4 (n : ℕ) : ℚ :=
  ∑ j ∈ range (17 * n + 1), (U n j * harm 4 (j + 2 * n) + V n j * harm 3 (j + 2 * n) / 3)

/-- `D_n = d_{19n} = lcm(1, …, 19n)`. -/
def D (n : ℕ) : ℕ := (Icc 1 (19 * n)).lcm id

/-- The integer vector `(Z_{0,n}, Z_{3,n}, Z_{4,n}) = 6 D_n⁴ (S_{0,n}, S_{3,n}, S_{4,n})`. -/
def Zv (n : ℕ) : Fin 3 → ℚ :=
  ![6 * D n ^ 4 * S0 n, 6 * D n ^ 4 * S3 n, 6 * D n ^ 4 * S4 n]

/-- The approximants `r_n(A,B) = (A S_{3,n} + B S_{4,n}) / S_{0,n}`. By the readout identities
(walk-readout) this is the forward-walk ratio `r_{A,B} W_n e₀ / r_Q W_n e₀`. -/
def approx (n : ℕ) (A B : ℤ) : ℚ := (A * S3 n + B * S4 n) / S0 n

/-! ## §4. Factorial permutations (§7 of the manuscript, Lemma `arith-integral`) -/

/-- The five shifts `(-2,-1,0,1,2)`; a permutation `σ` gives `b_i = shift (σ i)`. -/
def shift : Fin 5 → ℤ := ![-2, -1, 0, 1, 2]

/-- The permuted coefficient product `𝒯^b_{n,j}(ε)`:
`∏_{i=0}^2 C(j+(10+i)n-ε, (10+i+b_i)n) · C((16-b₃)n, j-b₃n-ε) · C((17-b₄)n, j-b₄n-ε)`. -/
def coeffJetPerm (σ : Equiv.Perm (Fin 5)) (n j : ℕ) : Jet :=
  let b : Fin 5 → ℤ := fun i => shift (σ i)
  upperJet (j + 10 * n) ((10 + b 0) * n).toNat * upperJet (j + 11 * n) ((11 + b 1) * n).toNat *
    upperJet (j + 12 * n) ((12 + b 2) * n).toNat *
    lowerJet ((16 - b 3) * n).toNat ((j : ℤ) - b 3 * n) *
    lowerJet ((17 - b 4) * n).toNat ((j : ℤ) - b 4 * n)

/-- The relative factorial multiplier
`λ_{n,b} = (10n)!³ ∏_{e ∈ J_b} (en)! / ((15n)!² ∏_{ℓ ∈ L_b} (ℓn)!)`,
`L_b = (10+b₀, 11+b₁, 12+b₂)`, `J_b = (16-b₃, 17-b₄)`. -/
def lam (σ : Equiv.Perm (Fin 5)) (n : ℕ) : ℚ :=
  let b : Fin 5 → ℤ := fun i => shift (σ i)
  let fac : ℤ → ℚ := fun e => ((e * n).toNat.factorial : ℚ)
  fac 10 ^ 3 * fac (16 - b 3) * fac (17 - b 4) /
    (fac 15 ^ 2 * fac (10 + b 0) * fac (11 + b 1) * fac (12 + b 2))

/-! ## §5. The stronger divisor `G_n` (Appendix B–G of the manuscript) -/

/-- The eight factorial pairings `(L, D)` (the realised unordered lengths). -/
def pairings : List (List ℤ × List ℤ) :=
  [([8, 13, 13], [17, 17]), ([11, 11, 11], [14, 19]), ([9, 9, 14], [16, 16]),
   ([12, 12, 12], [18, 18]), ([11, 11, 14], [18, 18]), ([9, 9, 12], [14, 16]),
   ([10, 10, 10], [14, 16]), ([9, 11, 14], [17, 17])]

/-- `c(x) = 2⌊15x⌋ - 3⌊10x⌋`. -/
def cfun (x : ℚ) : ℤ := 2 * ⌊15 * x⌋ - 3 * ⌊10 * x⌋

/-- The profile `φ(x) = max(0, max_{(L,D)} [c(x) - ∑_{d∈D} ⌊dx⌋ + ∑_{l∈L} ⌊lx⌋])`. -/
def phi (x : ℚ) : ℤ :=
  pairings.foldr (fun LD m => max m
    (cfun x - (LD.2.map fun d => ⌊(d : ℚ) * x⌋).sum + (LD.1.map fun l => ⌊(l : ℚ) * x⌋).sum)) 0

/-- Eligible primes: `p > 29`, `p² > 30n`, `p ∤ n`. -/
def Eligible (n p : ℕ) : Prop := p.Prime ∧ 29 < p ∧ 30 * n < p ^ 2 ∧ ¬ p ∣ n

instance (n : ℕ) : DecidablePred (Eligible n) := fun p => by unfold Eligible; infer_instance

/-- The upper harmonic gain `h_n(p)`. -/
def hgain (n p : ℕ) : ℕ :=
  if 18 * n < p ∧ p < 19 * n then 3 else if 17 * n < p ∧ p < 18 * n then 2
  else if 16 * n < p ∧ p < 17 * n then 1 else 0

/-- The residue-block gain `s_n(p) = 𝟙_{8n < p < 11n}`. -/
def sgain (n p : ℕ) : ℕ := if 8 * n < p ∧ p < 11 * n then 1 else 0

/-- The explicit divisor (arith-G): `G_n = ∏_{p eligible} p^{φ(n/p) + h_n(p) + s_n(p)}`
(only primes `p ≤ 19n` have nonzero exponent). -/
def Gdiv (n : ℕ) : ℕ :=
  ∏ p ∈ (range (19 * n + 1)).filter (Eligible n),
    p ^ ((phi ((n : ℚ) / p)).toNat + hgain n p + sgain n p)

/-- `C_n = (15n)!² / (10n)!³`. -/
def Cn (n : ℕ) : ℚ := ((15 * n).factorial : ℚ) ^ 2 / ((10 * n).factorial : ℚ) ^ 3

/-- The appendix normalization `Q_n = (-1)^n S_{0,n} / C_n`. -/
def Qa (n : ℕ) : ℚ := (-1) ^ n * S0 n / Cn n

/-- The appendix normalization `P_{3,n} = (-1)^n S_{3,n} / C_n`. -/
def P3a (n : ℕ) : ℚ := (-1) ^ n * S3 n / Cn n

/-- The appendix normalization `P_{4,n} = (-1)^n S_{4,n} / C_n`. -/
def P4a (n : ℕ) : ℚ := (-1) ^ n * S4 n / Cn n

/-! ## §6. The analytic module (§4 and Appendix A of the manuscript)

The Meijer-G function along the dual trajectory is
`𝒢_n(z) = G^{5,2}_{5,5}(z | -16n,-17n; 1+11n,1+12n,2+10n / -2n,-n,0,n,2n)`, given by the
Mellin–Barnes integral over `Re s = 2n + 1/2`. Since `θ = z d/dz` multiplies the integrand by
`-s`, the state `𝒮_G(n) = (θ^k 𝒢_n)(1)_{k=0..3}` is defined directly by that integral at
`z = 1`. -/

/-- The Mellin–Barnes integrand
`Γ(16n+1-s) Γ(17n+1-s) / (Γ(s+11n+1) Γ(s+12n+1) Γ(s+10n+2)) · ∏_{j=-2}^{2} Γ(s+jn)`. -/
def mbIntegrand (n : ℕ) (s : ℂ) : ℂ :=
  Complex.Gamma (16 * n + 1 - s) * Complex.Gamma (17 * n + 1 - s) /
      (Complex.Gamma (s + 11 * n + 1) * Complex.Gamma (s + 12 * n + 1) *
        Complex.Gamma (s + 10 * n + 2)) *
    ∏ j ∈ Icc (-2 : ℤ) 2, Complex.Gamma (s + j * n)

/-- The contour `s = 2n + 1/2 + i y`. -/
def mbContour (n : ℕ) (y : ℝ) : ℂ := 2 * n + 1 / 2 + y * Complex.I

/-- The state `𝒮_G(n)_k = (θ^k 𝒢_n)(1) = (1/2πi) ∫ (-s)^k (integrand) ds`. -/
def SG (n k : ℕ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, (-mbContour n y) ^ k * mbIntegrand n (mbContour n y)

/-- The factorial bound `𝔡_n = (16n)!(15n)!²(2n-1)!(3n-1)!(4n-1)! / ((13n)!(12n+1)!(30n+1)!)`. -/
def dfrak (n : ℕ) : ℝ :=
  ((16 * n).factorial * (15 * n).factorial ^ 2 * (2 * n - 1).factorial *
      (3 * n - 1).factorial * (4 * n - 1).factorial : ℝ) /
    ((13 * n).factorial * (12 * n + 1).factorial * (30 * n + 1).factorial : ℝ)

/-- `η = 16¹⁶ 15³⁰ 2² 3³ 4⁴ / (13¹³ 12¹² 30³⁰) · (3/2)⁵⁵ ≈ 8.517·10⁻⁴`. -/
def eta : ℝ :=
  16 ^ 16 * 15 ^ 30 * 2 ^ 2 * 3 ^ 3 * 4 ^ 4 / (13 ^ 13 * 12 ^ 12 * 30 ^ 30) * (3 / 2) ^ 55

/-- Coefficients of the restricted characteristic polynomial `χ(X) = X³ - aX² + bX - c` of
`Q_∞ = lim T_n Q(n) T_{n+1}^{-1}` (`certificates/spectral_data.json`). -/
def chiA : ℚ :=
  83220721427294106907399200607730930785765129529801897078934559 /
    1484577825190137274336280508756918272

/-- See `chiA`. -/
def chiB : ℚ :=
  731334801243107466089356596505717853275074571608716447379201100334794667003154611901941573810757 /
    146466868948884247884332915718530654652342544

/-- See `chiA`. -/
def chiC : ℚ :=
  76623012348334313797938377862237790794460627983667564193521662995163373351121226574589853696 /
    2130520759189220333584634002331004844478493702212809977860478179

/-- The restricted characteristic polynomial `χ`. -/
def chi : Polynomial ℚ :=
  .X ^ 3 - .C chiA * .X ^ 2 + .C chiB * .X - .C chiC

/-- The walk `W_Q(n) = Q(0) Q(1) ⋯ Q(n-1)`, `W_Q(0) = 1`. -/
def walk {k : ℕ} {R : Type*} [CommRing R] (Q : ℕ → Matrix (Fin k) (Fin k) R) (n : ℕ) :
    Matrix (Fin k) (Fin k) R :=
  ((List.range n).map Q).prod

/-- The balancing matrix `T_n = diag(1, n, n²)` (only used for `n ≥ 1`). -/
def balance (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, (n : ℂ), (n : ℂ) ^ 2]

/-! ## §7. Nonvanishing and the main theorem -/

/-- The irrationality exponent `δ_n(A,B) = -1 - log|α_{A,B} - p_n/q_n| / log q_n` of the reduced
approximant `r_n(A,B) = p_n/q_n`. -/
def delta (n : ℕ) (A B : ℤ) : ℝ :=
  -1 - Real.log |alpha A B - approx n A B| / Real.log (approx n A B).den

end Pfq54
