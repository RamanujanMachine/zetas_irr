"""Exact transcription checks for the all-pairs arithmetic explanation.

Finite checks are diagnostics, not a proof for arbitrary n or A,B.
"""
from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial, gcd, lcm, prod
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'work/meijerg5255_arithmetic/arithmetic'))
from partial_fractions import pf_fast, kernel_readout
from sympy import primerange

OUT = ROOT / 'results/pfq54_all_pairs_readout'
OUT.mkdir(exist_ok=True)

def valuation_integer(x, p):
    answer = 0
    while x % p == 0:
        answer += 1
        x //= p
    return answer

def valuation(x, p):
    return valuation_integer(abs(x.numerator), p) - valuation_integer(x.denominator, p)

def hypergeom(a, b, degree):
    term = F(1)
    total = term
    for k in range(1, degree + 1):
        term *= prod(F(x+k-1) for x in a)
        term /= k * prod(F(x+k-1) for x in b)
        total += term
    return total

records = []
for n in (1, 2, 3, 5):
    a = [1+13*n, 1+14*n, -14*n, -15*n, 1+12*n]
    b = [1+n, 1+2*n, 1+3*n, 1+4*n]
    rho = (-1)**n * F(factorial(12*n)*factorial(13*n),
        prod(factorial(k*n) for k in (1,2,3,4,15)))
    C = F(factorial(15*n)**2, factorial(10*n)**3)
    D = lcm(*range(1,19*n+1))
    E = C * abs(rho)
    assert E.denominator == 1
    moments = [F(0)] * 4
    term = F(1)
    for k in range(14*n+1):
        if k:
            term *= F(prod(x+k-1 for x in a), k*prod(x+k-1 for x in b))
        integer = prod(comb((12+u)*n+k,10*n) for u in range(3))
        integer *= comb(15*n,n+k)*comb(15*n,k)
        assert E*term == integer
        for r in range(4):
            moments[r] += k**r*term
    Q, P3, P4 = map(lambda x:F(str(x)),kernel_readout(n))
    assert Q == rho*moments[0]
    cs = pf_fast(n)
    assert all((C*F(str(aa))).denominator == 1 and
               (D*C*F(str(bb))).denominator == 1 for aa,bb in cs.values())
    X = [6*C*D**4*x for x in (Q,P3,P4)]
    assert all(x.denominator == 1 for x in X)
    X = [int(x) for x in X]
    norms = set()
    for perm in permutations((-2,-1,0,1,2)):
        lengths = [10+i+perm[i] for i in range(3)]
        ends = [16-perm[3],17-perm[4]]
        norms.add(F(prod(factorial(e*n) for e in ends),
                    prod(factorial(ell*n) for ell in lengths)))
    G = 1
    for p in primerange(2,19*n+1):
        exponent = max([0]+[valuation(C/Cb,p) for Cb in norms])
        G *= int(p)**exponent
    assert all(x % G == 0 for x in X)
    K = F(prod(a),prod(b))
    # 2 theta + 3 theta^2 is the genuine 6F5 column observable.
    value6 = 5*K*hypergeom([x+1 for x in a]+[F(8,3)],
                          [x+1 for x in b]+[F(5,3)],14*n-1)
    assert value6 == 2*moments[1]+3*moments[2]
    for A,B in ((0,0),(1,0),(0,1),(15,1),(-2,3),(1,-1)):
        assert gcd(abs(X[0]), A*X[1]+B*X[2]) % G == 0
        P = A*P3+B*P4
        assert (P/Q).denominator <= abs(X[0])//G
        # Three shifted 5F4s express the column polynomial for all A,B,
        # without singular auxiliary parameters.
        c = [-3*A-2*B,3*A-6*B,3*A-2*B]
        shifted = F(0)
        for s in (1,2,3):
            Ks = F(prod(prod(x+j for j in range(s)) for x in a),
                   prod(prod(x+j for j in range(s)) for x in b))
            shifted += c[s-1]*Ks*hypergeom([x+s for x in a],
                                         [x+s for x in b],14*n-s)
        assert shifted == -6*A*moments[2]+(3*A-2*B)*moments[3]
    records.append(dict(n=n, factorial_normalizations=len(norms),
        group_divisor=str(G), normalized_triple=list(map(str,X)),
        F=str(moments[0]), theta3=str(moments[3]),
        W30=str(-6*P4/rho), coefficient_clearing_integer=str(E)))

result = dict(status='KNOWN_EXAMPLE', records=records,
    scope='Exact finite transcription checks; all-depth arithmetic is proved in the accompanying note.',
    rejected_identity='The initial row (0,0,-6A,3A-2B) is not the observable -6A theta^2 F+(3A-2B) theta^3 F.')
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('Exact coefficient, shifted-series, harmonic-integrality and all-prime divisor checks passed at n=1,2,3,5.')
