"""Check the direct binomial value/derivative presentation exactly."""
from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial, lcm, prod
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'work/meijerg5255_arithmetic/arithmetic'))
from partial_fractions import pf_fast, kernel_readout

def harmonic(m):
    return sum((F(1,k) for k in range(1,m+1)),F(0))

def upper_jet(N,M):
    """Value and epsilon derivative of binomial(N-epsilon,M)."""
    if N>=M:
        value=comb(N,M)
        return F(value),-value*(harmonic(N)-harmonic(N-M))
    return F(0),F((-1)**(M-N)*factorial(N)*factorial(M-1-N),factorial(M))

def lower_jet(M,m):
    """Value and epsilon derivative of Gamma-binomial(M,m-epsilon)."""
    if 0<=m<=M:
        value=comb(M,m)
        return F(value),value*(harmonic(m)-harmonic(M-m))
    r=-m if m<0 else m-M
    sign=(-1)**r if m<0 else (-1)**(r-1)
    return F(0),F(sign*factorial(M)*factorial(r-1),factorial(M+r))

def coefficient_jet(n,j,b):
    factors=[upper_jet(j+(10+i)*n,(10+i+b[i])*n) for i in range(3)]
    factors.extend([lower_jet((16-b[3])*n,j-b[3]*n),
                    lower_jet((17-b[4])*n,j-b[4]*n)])
    value=prod(x[0] for x in factors)
    derivative=sum((x[1]*prod(y[0] for k,y in enumerate(factors) if k!=i)
                    for i,x in enumerate(factors)),F(0))
    return value,derivative

records=[]
for n in (1,2,3):
    C=F(factorial(15*n)**2,factorial(10*n)**3)
    D=lcm(*range(1,19*n+1))
    old=pf_fast(n)
    reference=[coefficient_jet(n,j,(0,-1,-2,1,2)) for j in range(17*n+3)]
    for j,(u,v) in enumerate(reference):
        a,b=map(lambda x:F(str(x)),old.get(j,(0,0)))
        assert u==(-1)**n*C*a and v==(-1)**n*C*b
    checks=0
    for b in permutations((-2,-1,0,1,2)):
        Cb=F(factorial((16-b[3])*n)*factorial((17-b[4])*n),
             prod(factorial((10+i+b[i])*n) for i in range(3)))
        for j,(u,v) in enumerate(reference):
            ub,vb=coefficient_jet(n,j,b)
            assert ub==Cb/C*u and vb==Cb/C*v
            assert ub.denominator==1 and (D*vb).denominator==1
            checks+=1
    hs={r:[F(0)] for r in (2,3,4)}
    for k in range(1,19*n+3):
        for r in hs:hs[r].append(hs[r][-1]+F(1,k**r))
    direct=[sum((u for u,v in reference),F(0))]
    for r in (3,4):
        direct.append(sum((u*hs[r][j+2*n]+v*hs[r-1][j+2*n]/(r-1)
                           for j,(u,v) in enumerate(reference)),F(0)))
    assert direct==[(-1)**n*C*F(str(x)) for x in kernel_readout(n)]
    records.append(dict(n=n,permutation_coefficient_checks=checks,
                        common_scaled_readouts=list(map(str,direct))))
out=ROOT/'results/pfq54_all_pairs_readout/direct_binomial_checks.json'
out.write_text(json.dumps(dict(status='KNOWN_EXAMPLE',records=records,
    scope='Exact finite transcription checks; general identities are derived in the LaTeX note.'),indent=2)+'\n')
print('All binomial jets, boundary coefficients, 120 permutation identities and harmonic readouts agree exactly.')
