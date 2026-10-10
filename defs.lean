/-
# Blueprint: a CMF proof of the linear independence of `1, ζ(3), ζ(4)`

This file is a Lean blueprint of the note
  *"A CMF proof of the linear independence of 1, ζ(3), ζ(4) — Proof development and exact
  certificates"* (6 October 2026),
whose main theorem (Theorem 1 there) is the statement of Theorem 1.6 of Li Lai's preprint
arXiv:2610.06838.

Structure (following the sections of the note):

* §0  The zeta values `ζ(3), ζ(4)`.
* §1  The formal residue functionals `𝓛_K` (Part VII §7) and `𝓜_K = -𝓛_K[f']` (Part III).
* §2  The rational sequences: kernels `R_N`, `R*_N`, the coefficient matrix `𝓒_N`, the block
      `V_N`, `T_N = V_N^{-T}` and the readout matrix `𝓡_N = U₃₄ T_N` (Parts I, VII §2).
* §3  Analytic input (Part II, VII §1, §6).
* §4  The second-derivative pairing identity (Part III).
* §5  The all-prime denominator bound `Δ_N` (Part IV, VII §3, §4).
* §6  The irrationality proof (Part V): Theorem 1 / Theorem 1.6.

Only `theorem`s count as blueprint nodes; there are 18 of them. Nodes whose proof is the
mathematical content of the note are left as `sorry`; the logical glue
(`integer_matrix_criterion`, `det_Rmat`, the main theorem and its corollary) is proved
from the other nodes.

Remark on `V_N`. The note defines `V_N` as the upper-left `3 × 3` block of the forward walk
`W_N = M(0) ⋯ M(N-1)` of the conservative matrix field `MeijerG(5,2,5,5,1)` and proves the
coefficient identity (13) `𝓒_N = (-1)^N 𝓒₀ V_N`. Since the single-step matrices `M(n)` are not
displayed in the note, this blueprint takes (13) as the *definition* of `V_N`
(`𝓒₀` is invertible, `det 𝓒₀ = -6`); identifying it with the CMF walk is the content of
the exact certificate `verify_matrix.py` and is not needed for the deduction below.
-/
import Mathlib

open Polynomial Filter Topology Real
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace ZetasIrr

/-! ## §0. Zeta values -/

/-- `ζ(3)` as a real number. -/
def ζ3 : ℝ := (riemannZeta 3).re

/-- `ζ(4)` as a real number. -/
def ζ4 : ℝ := (riemannZeta 4).re

/-- Sanity check against Mathlib: `ζ(4) = π⁴/90`. -/
theorem zeta4_eq : ζ4 = π ^ 4 / 90 := by
  rw [ζ4, riemannZeta_four]
  norm_cast

/-! ## §1. Formal residue functionals (Part VII §7 and Part III)

Formal values are `ℚ`-linear combinations of the symbols `Z_r`; we encode them as
`ℕ →₀ ℚ`, where `single 0 1` stands for the constant `1` and `single r 1` for `Z_r`
(`r ≥ 2`). The realisation map sends `Z_r ↦ ζ(r)`. -/

/-- Formal combinations `c₀ + ∑ c_r Z_r`. -/
abbrev FormalZ := ℕ →₀ ℚ

/-- The formal symbol `Z_r` (`Z_0 = 1`). -/
def Zsym (r : ℕ) : FormalZ := Finsupp.single r 1

/-- Realisation `Z_r ↦ ζ(r)`, `Z_0 ↦ 1`. -/
def realize (z : FormalZ) : ℝ :=
  z.sum fun r q => (q : ℝ) * (if r = 0 then 1 else (riemannZeta r).re)

/-- Generalised harmonic number `H^{(s)}_n = ∑_{i=1}^{n} i^{-s}` (zero for `n ≤ 0`). -/
def harm (s : ℕ) (n : ℤ) : ℚ := ∑ i ∈ Finset.Icc 1 n.toNat, 1 / (i : ℚ) ^ s

/-- Partial-fraction coefficient `c_{h,r}` of `f`: the coefficient of `(t - h)^{-r}`,
read off from the Laurent expansion of `f(X + h)` at `0`. -/
def pfCoeff (f : ℚ⟮X⟯) (h : ℚ) (r : ℕ) : ℚ :=
  ((RatFunc.laurent h f : ℚ⟮X⟯) : ℚ⸨X⸩).coeff (-(r : ℤ))

/-- Polynomial part of a rational function. -/
def polyPart (f : ℚ⟮X⟯) : ℚ[X] := f.num /ₘ f.denom

/-- Derivative of a rational function. -/
def rfDeriv (f : ℚ⟮X⟯) : ℚ⟮X⟯ :=
  algebraMap ℚ[X] ℚ⟮X⟯ (derivative f.num * f.denom - f.num * derivative f.denom) /
    algebraMap ℚ[X] ℚ⟮X⟯ (f.denom ^ 2)

/-- Value of a rational function at a rational point. -/
def rfEval (f : ℚ⟮X⟯) (x : ℚ) : ℚ := RatFunc.eval (RingHom.id ℚ) x f

/-- The first formal functional (Part VII §7): for integer poles `h ≤ K`,
`𝓛_K[∑ p_m t^m + ∑ c_{hr}(t-h)^{-r}] = ∑ p_m B_m(K+1) + ∑ r c_{hr} (Z_{r+1} - H^{(r+1)}_{K-h})`.
For proper `f` this is the formal value of `-∑_{t>K} f'(t)`. -/
def Lfun (K : ℤ) (f : ℚ⟮X⟯) : FormalZ :=
  (∑ m ∈ Finset.range ((polyPart f).natDegree + 1),
      ((polyPart f).coeff m * (Polynomial.bernoulli m).eval ((K : ℚ) + 1)) • Zsym 0) +
  ∑ h ∈ f.denom.roots.toFinset, ∑ r ∈ Finset.range (f.denom.natDegree + 1),
      ((r : ℚ) * pfCoeff f h r) • (Zsym (r + 1) - harm (r + 1) ⌊(K : ℚ) - h⌋ • Zsym 0)

/-- The second-derivative dual residue functional (Part III): `𝓜_K[f] := -𝓛_K[f']`.
Explicitly `𝓜_K[(t-h)^{-r}] = r(r+1)(Z_{r+2} - H^{(r+2)}_{K-h})`, `𝓜_K[t^d] = -d B_{d-1}(K+1)`. -/
def Mfun (K : ℤ) (f : ℚ⟮X⟯) : FormalZ := -Lfun K (rfDeriv f)

/-- The real function `t ↦ f(t)` attached to `f ∈ ℚ(X)`. -/
def rfReal (f : ℚ⟮X⟯) (x : ℝ) : ℝ := RatFunc.eval (algebraMap ℚ ℝ) x f

/-- The analytic sum `-∑_{t > K} f'(t)`. -/
def derivSum (K : ℤ) (f : ℚ⟮X⟯) : ℝ := -∑' n : ℕ, deriv (rfReal f) ((K : ℝ) + 1 + n)

/-! ## §2. The precise rational sequences (Parts I and VII §2) -/

/-- `(t + c)_r = (t+c)(t+c+1)⋯(t+c+r-1)` as a polynomial in `t`. -/
def poch (c : ℚ) (r : ℕ) : ℚ[X] := (ascPochhammer ℚ r).comp (X + C c)

/-- The original kernel
`R_N(t) = (t-17N)_{15N} (t-16N)_{15N} / ((t)_{10N+2} (t+N)_{10N+1} (t+2N)_{10N+1})`. -/
def Rker (N : ℕ) : ℚ⟮X⟯ :=
  algebraMap ℚ[X] ℚ⟮X⟯ (poch (-17 * N) (15 * N) * poch (-16 * N) (15 * N)) /
    algebraMap ℚ[X] ℚ⟮X⟯ (poch 0 (10 * N + 2) * poch N (10 * N + 1) * poch (2 * N) (10 * N + 1))

/-- The dual kernel
`R*_N(t) = (t+N+1)_{11N} (t+1)_{11N} (t+2N)_{8N+1} / ((t+13N+1)_{15N+1} (t+14N+1)_{15N+1})`. -/
def RkerStar (N : ℕ) : ℚ⟮X⟯ :=
  algebraMap ℚ[X] ℚ⟮X⟯ (poch (N + 1) (11 * N) * poch 1 (11 * N) * poch (2 * N) (8 * N + 1)) /
    algebraMap ℚ[X] ℚ⟮X⟯ (poch (13 * N + 1) (15 * N + 1) * poch (14 * N + 1) (15 * N + 1))

/-- The kernel of the `j`-th linear form: `(-t)^j R_N(t)`. -/
def linFormKernel (N : ℕ) (j : Fin 3) : ℚ⟮X⟯ := (-RatFunc.X) ^ (j : ℕ) * Rker N

/-- The coefficient matrix `𝓒_N = (A_{Nj}, B_{Nj}, C_{Nj})_rows`: the `Z₄`, `Z₃` and rational
coefficients of `𝓛_{2N}[(-t)^j R_N(t)]`. -/
def coeffMat (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => Lfun (2 * N) (linFormKernel N j) (![4, 3, 0] i)

/-- The linear forms `S_{Nj} = -∑_{t ≥ 2N+1} d/dt((-t)^j R_N(t))`. -/
def S (N : ℕ) (j : Fin 3) : ℝ := derivSum (2 * N) (linFormKernel N j)

/-- `𝓒₀`. -/
def C0 : Matrix (Fin 3) (Fin 3) ℚ := !![3, 0, 0; -2, -2, 0; 1, 1, 1]

/-- The `3 × 3` block `V_N` of the CMF walk, via identity (13): `𝓒_N = (-1)^N 𝓒₀ V_N`. -/
def V (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := ((-1 : ℚ) ^ N) • (C0⁻¹ * coeffMat N)

/-- `T_N = V_N^{-T}`. -/
def T (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := (V N)⁻¹ᵀ

/-- The readout matrix `U₃₄`. -/
def U34 : Matrix (Fin 3) (Fin 3) ℚ := !![0, -3, 3; 2, -2, 0; 0, 0, 6]

/-- `𝓡_N = U₃₄ T_N`, with rows `p^{(3)}_N`, `p^{(4)}_N`, `q_N`. -/
def Rmat (N : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := U34 * T N

/-- `p^{(3)}_{Nj}`. -/
abbrev p3 (N : ℕ) (j : Fin 3) : ℚ := Rmat N 0 j
/-- `p^{(4)}_{Nj}`. -/
abbrev p4 (N : ℕ) (j : Fin 3) : ℚ := Rmat N 1 j
/-- `q_{Nj}`. -/
abbrev q (N : ℕ) (j : Fin 3) : ℚ := Rmat N 2 j

/-- The exponent lists `𝓐, 𝓑, 𝓔` of the factorial formula (14). -/
def listA : List ℕ := [16, 17, 18, 15, 14, 17, 18, 19, 16, 15]
/-- See `listA`. -/
def listB : List ℕ := [11, 10, 9, 12, 13, 12, 11, 10, 13, 14]
/-- See `listA`. -/
def listE : List ℕ := [10, 9, 8, 11, 12]

/-- `F_N = ∏_{r∈𝓐}(rN)! / (∏_{r∈𝓑}(rN)! ∏_{r∈𝓔}(rN+1)!)`. -/
def F (N : ℕ) : ℚ :=
  (listA.map fun r => ((r * N).factorial : ℚ)).prod /
    ((listB.map fun r => ((r * N).factorial : ℚ)).prod *
      (listE.map fun r => ((r * N + 1).factorial : ℚ)).prod)

/-! ## §4. The second-derivative identity (Part III) -/

/-- The integer polynomial concomitant matrix `J_N` (Part VII §2). -/
def Jmat (N : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  let n : ℤ := N
  !![4 * n ^ 2 * (13725 * n ^ 2 + 2389 * n + 103), -6 * n * (275 * n ^ 2 + 150 * n + 11),
      -450 * n ^ 2 - 43 * n + 2, 3;
    n * (5 * n + 1) * (330 * n + 23), n * (450 * n + 43), -2, 0;
    -(18 * n + 1) * (25 * n + 1), 1, 0, 0;
    0, 0, 0, 0]

/-- `Q_{Nj}(t) = ∑_{r=0}^{3} (J_N)_{jr} (-t-12N-1)^r ∈ ℤ[t]`. -/
def Qpoly (N : ℕ) (j : Fin 3) : ℚ[X] :=
  ∑ r : Fin 4, (Jmat N (Fin.castSucc j) r : ℚ) • (-X - C (12 * (N : ℚ) + 1)) ^ (r : ℕ)

/-! ## §5. The all-prime denominator bound (Part IV, Part VII §3–4) -/

/-- `f_p(m) = v_p(m!)` (for `m ≥ 0`). -/
def fp (p : ℕ) (m : ℤ) : ℤ := padicValNat p m.toNat.factorial

/-- `ℓ_p(m) = v_p(lcm(1, …, m))`, `ℓ_p(0) = 0`. -/
def ellp (p : ℕ) (m : ℤ) : ℤ := padicValNat p ((Finset.Icc 1 m.toNat).lcm id)

/-- `G_p(k; [a,b]) = v_p(∏_{r=a, r≠k}^{b} (r - k))`. -/
def Gp (p : ℕ) (k a b : ℤ) : ℤ :=
  if k < a then fp p (b - k) - fp p (a - k - 1)
  else if b < k then fp p (k - a) - fp p (k - b - 1)
  else fp p (k - a) + fp p (b - k)

/-- Minimum of `f` on a finite set (`0` on the empty set). -/
def minOn (s : Finset ℤ) (f : ℤ → ℤ) : ℤ := if h : s.Nonempty then s.inf' h f else 0
/-- Maximum of `f` on a finite set (`0` on the empty set). -/
def maxOn (s : Finset ℤ) (f : ℤ → ℤ) : ℤ := if h : s.Nonempty then s.sup' h f else 0

/-- Number of intervals of a family containing `k`. -/
def mult (I : List (ℤ × ℤ)) (k : ℤ) : ℤ := I.countP fun ab => decide (ab.1 ≤ k ∧ k ≤ ab.2)

/-- `𝓘_o = ([0,10N+1], [N,11N], [2N,12N])`. -/
def Io (N : ℕ) : List (ℤ × ℤ) := [(0, 10 * N + 1), (N, 11 * N), (2 * N, 12 * N)]

/-- `V_o(k)`: valuation of the top partial-fraction coefficient of the original kernel. -/
def Vo (N p : ℕ) (k : ℤ) : ℤ :=
  fp p (k + 17 * N) + fp p (k + 16 * N) - fp p (k + 2 * N) - fp p (k + N) -
    ((Io N).map fun ab => Gp p k ab.1 ab.2).sum

/-- `A_p = min_{2N ≤ k ≤ 10N+1} V_o(k)`. -/
def Ap (N p : ℕ) : ℤ := minOn (Finset.Icc (2 * N) (10 * N + 1)) (Vo N p)

/-- `B_p = min_{0 ≤ k ≤ 12N, m_o(k) ≥ 2} {V_o(k) - (m_o(k) - 2) ℓ_p(k + 17N)}`. -/
def Bp (N p : ℕ) : ℤ :=
  minOn ((Finset.Icc 0 (12 * N : ℤ)).filter fun k => 2 ≤ mult (Io N) k)
    fun k => Vo N p k - (mult (Io N) k - 2) * ellp p (k + 17 * N)

/-- `C_p = min_{0 ≤ k ≤ 12N} {V_o(k) - (m_o(k) - 1) ℓ_p(k + 17N) - 2 ℓ_p(k + 2N)}`. -/
def Cp (N p : ℕ) : ℤ :=
  minOn (Finset.Icc 0 (12 * N : ℤ))
    fun k => Vo N p k - (mult (Io N) k - 1) * ellp p (k + 17 * N) - 2 * ellp p (k + 2 * N)

/-- `v_p(F_N)`. -/
def vpF (N p : ℕ) : ℤ :=
  (listA.map fun r => fp p (r * N)).sum - (listB.map fun r => fp p (r * N)).sum -
    (listE.map fun r => fp p (r * N + 1)).sum

/-- `E_o(N,p) = max{0, v_p(F_N) - A_p - C_p}`. -/
def Eo (N p : ℕ) : ℤ := max 0 (vpF N p - Ap N p - Cp N p)

/-- `E_{o4}(N,p) = max{0, v_p(F_N) - B_p - C_p}`. -/
def Eo4 (N p : ℕ) : ℤ := max 0 (vpF N p - Bp N p - Cp N p)

/-- `𝓘_d = ([13N+1, 28N+1], [14N+1, 29N+1])`. -/
def Id (N : ℕ) : List (ℤ × ℤ) := [(13 * N + 1, 28 * N + 1), (14 * N + 1, 29 * N + 1)]

/-- `V_d(k)`: valuation of the top partial-fraction coefficient of the dual kernel. -/
def Vd (N p : ℕ) (k : ℤ) : ℤ :=
  fp p (k - N - 1) + fp p (k - 1) + fp p (k - 2 * N) -
    fp p (k - 12 * N - 1) - fp p (k - 11 * N - 1) - fp p (k - 10 * N - 1) -
    ((Id N).map fun ab => Gp p k ab.1 ab.2).sum

/-- `L(k) = max{k - 1, 29N + 1 - k}`. -/
def Ld (N : ℕ) (k : ℤ) : ℤ := max (k - 1) (29 * N + 1 - k)

/-- `E_d(N,p)`: dual bound for the first functional (harmonic index `h(k) = k - 11N - 1`). -/
def Ed (N p : ℕ) : ℤ :=
  max (max (padicValNat p 6) 0)
    (maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1)) fun k =>
      (mult (Id N) k - 1) * ellp p (Ld N k) + 2 * ellp p (k - 11 * N - 1) - Vd N p k)

/-- `E_{d4}(N,p)`: dual bound for the second functional (harmonic index `h₄(k) = k - 10N - 1`). -/
def Ed4 (N p : ℕ) : ℤ :=
  max 0
    (maxOn (Finset.Icc (13 * N + 1 : ℤ) (29 * N + 1)) fun k =>
      (mult (Id N) k - 1) * ellp p (Ld N k) + 3 * ellp p (k - 10 * N - 1) - Vd N p k)

/-- `E₃₄(N,p) = max{min(E_o, E_d), min(E_{o4}, E_{d4})}` for `p > 3`,
`E₃₄(N,p) = max{E_d, E_{d4}}` for `p = 2, 3`. -/
def E34 (N p : ℕ) : ℤ :=
  if 3 < p then max (min (Eo N p) (Ed N p)) (min (Eo4 N p) (Ed4 N p))
  else max (Ed N p) (Ed4 N p)

/-- **The all-prime integer multiplier (7)**: `Δ_N = ∏_{p ≤ 29N+1} p^{E₃₄(N,p)}`, `Δ₀ = 1`. -/
def Delta (N : ℕ) : ℕ :=
  if N = 0 then 1
  else ∏ p ∈ (Finset.range (29 * N + 2)).filter Nat.Prime, p ^ (E34 N p).toNat

end ZetasIrr
