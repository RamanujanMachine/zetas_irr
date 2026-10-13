"""Verify a rational coboundary after polynomial scalar multiplication.

Run from the repository root:
    python3.12 -m research.verify_4f3_meijerg_coboundary

The coboundary H(n) has only rational entries. With polynomial
scalars A(n) = n+1 and B(n) defined below, the exact identity is
    B(n) MF(n) H(n+1) = A(n) H(n) MG(n)^(-T).

Scalar multiplication preserves the projected numerator/denominator
ratios of a walk. All matrix comparisons below use exact symbolic ==.
The script also verifies the single rational multiplier A/B, leaving
MF unscaled and using the same rational coboundary H.
"""

from sympy import Poly, PurePoly, Rational, invert, log, oo, prod, rem, symbols, zeta
from sympy.abc import n

from ramanujantools import Matrix, Position
from ramanujantools.cmf import MeijerG, pFq


# Meijer G: inverse-transpose walk.
cmfG = MeijerG(4, 1, 4, 4, -1)
axesG = symbols("a0:4") + symbols("b0:4")
initialPointG = Position(dict(zip(axesG, (0, 1, 1, 2, 0, 0, 0, 0), strict=True)))
trajectoryG = Position(dict(zip(axesG, (-11, 10, 9, 11, 0, 2, 1, 3), strict=True)))
initialValuesG = Matrix(
    [
        [0, 1, -1],
        [0, 0, -1],
    ]
)
MG = cmfG.trajectory_matrix(trajectoryG, initialPointG)
MGdual = MG.inverse().T
print("Meijer G rank:", cmfG.rank())

# Original 4F3: forward walk.
cmfF = pFq(4, 3, 1)
axesF = symbols("x0:4") + symbols("y0:3")
initialPointF = Position(dict(zip(axesF, (0, 1, 1, 1, 1, 1, 1), strict=True)))
trajectoryF = Position(dict(zip(axesF, (-11, 10, 9, 11, 2, 1, 3), strict=True)))
initialValuesF = Matrix(
    [
        [0, 2, -1],
        [2, 0, 0],
    ]
)
MF = cmfF.trajectory_matrix(trajectoryF, initialPointF)
print("4F3 rank:", cmfF.rank())

# Basis transformation for this particular G starting point.
a = 11 * n + 1
H = Matrix(
    [
        [
            n * a * (1315 * n**2 + 240 * n + 11),
            -3 * n * a * (14 * n + 1),
            -a * (13 * n + 1),
        ],
        [a * (42 * n**2 - 8 * n - 1), 101 * n**2 + 32 * n + 2, -13 * n - 1],
        [-a * (13 * n + 2), 13 * n + 2, 0],
    ]
)

# Keep the coboundary rational and put all scalar factors on the matrices.
A = n + 1
B = (
    10800
    * prod(5 * n + j for j in range(1, 5))
    * prod(9 * n + j for j in (1, 2, 4, 5, 7, 8))
    * prod(10 * n + j for j in (1, 3, 7, 9))
)
rational_check = all(entry.is_rational_function(n) for entry in H)
print("Coboundary H has only rational entries:", rational_check)
assert rational_check

MF_scaled = (B * MF).factor()
MGdual_scaled = (A * MGdual).factor()


A_combined = A / B
equal_combined = (A_combined * MGdual).coboundary(H.inverse(), n) == MF
print("MF == (A/B)*H*MGdual*H(n+1)^(-1):", equal_combined)
assert equal_combined

# First isolate zeta(2) in the Meijer G state vector at the source point.
# Its entries are derived from an absolutely convergent series in the proof.
stateG0 = Matrix([[zeta(2) - zeta(3) - 1, zeta(2) - 1, -1]])
assert initialValuesG * stateG0.T == Matrix([zeta(2), 1])
print("Meijer G initial ratio is zeta(2):", True)

# Then transport the identity to the 4F3 side using the source coboundary.
H0 = H.subs({n: 0})
initial_check = initialValuesF * H0 == 2 * initialValuesG
print("Initial conditions match up to the common factor 2:", initial_check)
assert initial_check
stateF0 = stateG0 * H0.T
assert stateF0 == Matrix([[1, zeta(2) + zeta(3), 2 * zeta(3)]])
assert initialValuesF * stateF0.T == Matrix([2 * zeta(2), 2])
print("Transported 4F3 initial ratio is zeta(2):", True)

# The projection used by the forward scheme is the last coordinate.
# Balance the state coordinates to obtain a finite matrix limit. A
# nonzero Krylov determinant shows that the projection couples to every
# limiting mode, since the limiting characteristic roots are distinct.
projection = Matrix([0, 0, 1])
MF_infinity = Matrix(
    3, 3, lambda i, j: (n**i * MF[i, j] / (n + 1)**j).limit(n, oo)
)
assert all(entry.is_Rational for entry in MF_infinity)
projection_check = Matrix.hstack(
    projection, MF_infinity * projection, MF_infinity**2 * projection
).det() != 0
print("Projection vector couples to every limiting mode:", projection_check)
assert projection_check

# Growth rates for the RAW FORWARD Meijer G matrix, not MGdual.
# First take the unscaled limit using RT's direct Poincare helper.
P_raw = MG.charpoly()
P_raw_infinity = Matrix.poincare_poly(P_raw)
print("Unscaled forward G limiting polynomial:", P_raw_infinity.as_expr())


def degree_at_infinity(coefficient):
    numerator, denominator = coefficient.as_numer_denom()
    return Poly(numerator, n).degree() - Poly(denominator, n).degree()


# Infer the common one-step scale from the coefficient degrees instead
# of multiplying MG by a hardcoded power. For this trajectory, the
# coefficient of lambda^(3-i) has degree -13*i at infinity.
coefficients = P_raw.all_coeffs()
step_powers = {
    Rational(degree_at_infinity(coefficient), i)
    for i, coefficient in enumerate(coefficients)
    if i > 0 and coefficient != 0
}
assert len(step_powers) == 1, "The modes do not share a common power of n."
step_power = next(iter(step_powers))
print("Common one-step power of n (inferred):", step_power)

# Normalization is still needed to expose the nonzero exponential
# constants; the unscaled limit above has only zero roots.
P_infinity = PurePoly(
    [
        (coefficient / n**(step_power * i)).limit(n, oo)
        for i, coefficient in enumerate(coefficients)
    ],
    P_raw.gen,
)
print(P_infinity)
print("Normalized forward G limiting polynomial:", P_infinity.as_expr())

limiting_check = n not in P_infinity.as_expr().free_symbols and P_infinity.nth(0) != 0
print("Polynomial is independent of n and has a nonzero constant:", limiting_check)
assert limiting_check

# Exact algebraic roots first, then numerical evaluation. This preserves
# the very small root without subtracting approximate cubic radicals.
rates = sorted(
    (root.evalf(60) for root in P_infinity.all_roots(radicals=False)),
    key=lambda value: abs(complex(value)),
    reverse=True,
)
for index, rate in enumerate(rates, start=1):
    print(f"rho_{index} =", rate.evalf(40))

dominant_modulus = abs(rates[0])
error_factor = abs(rates[-1]) / dominant_modulus
separation_digits = -log(error_factor) / log(10)
print("Dominant modulus:", dominant_modulus.evalf(40))
print("Exponential error factor:", error_factor.evalf(40))
print("Separation digits per trajectory step:", separation_digits.evalf(40))

# Certify with rational arithmetic that the limiting root is nonzero:
# -1.60211 * 10^(-27) < rho_3 < -1.60210 * 10^(-27).
x = symbols("x")
scale = 10**27
scaled_poly = Poly(scale * P_infinity.as_expr().subs({P_infinity.gen: x / scale}), x)
root_count = scaled_poly.count_roots(
    Rational(-160211, 100000), Rational(-160210, 100000)
)
print("Exactly one root in the certified small interval:", root_count == 1)
assert root_count == 1

# The positive Euler integral in meijerg_recessive_proof.md proves decay
# of the actual G-function, after multiplying its values by (n!)^13.
# Its crude bound already has an exponential base strictly below 1.
bound_base = Rational(11**11, 8**24)
print("Normalized G decay bound base:", bound_base.evalf(40))
assert 0 < bound_base < 1

# Maximizing the positive integral kernel gives a unique critical point.
# With w = 11*xyz/(1-xyz), its equation is this cubic.
w = symbols("w")
critical_expression = 13*w**3 + 387*w**2 + 1490*w - 24024
critical_poly = Poly(critical_expression, w)
critical_check = critical_poly.count_roots(0, oo) == 1
print("Integral kernel has exactly one positive critical w:", critical_check)
assert critical_check
assert critical_poly.count_roots(5, 6) == 1

# The signed exponential base at that point is -saddle_num/saddle_den.
saddle_num = (w+11)**11 * (w+12)**12 * (w+13)**13 * (w+14)**14
saddle_den = (w+20)**20 * (w+21)**21 * (w+22)**22
saddle_rate_reduced = rem(
    -rem(saddle_num, critical_expression, w)
    * invert(rem(saddle_den, critical_expression, w), critical_expression, w),
    critical_expression,
    w,
)

# Evaluate the limiting characteristic polynomial modulo the critical
# cubic. Zero remainder certifies the matching root algebraically.
remainder = 0
for coefficient in P_infinity.all_coeffs():
    remainder = rem(
        remainder * saddle_rate_reduced + coefficient, critical_expression, w
    )
saddle_check = remainder == 0
print("Integral exponential base satisfies P_infinity exactly:", saddle_check)
assert saddle_check
assert P_infinity.count_roots(-oo, oo) == 1

w0 = next(root for root in critical_poly.real_roots(radicals=False) if root > 0)
w_numeric = w0.evalf(80)
saddle_rate = -saddle_num.subs({w: w_numeric}) / saddle_den.subs({w: w_numeric})
print("Integral critical w:", w_numeric.evalf(40))
print("Integral exponential base:", saddle_rate.evalf(40))
