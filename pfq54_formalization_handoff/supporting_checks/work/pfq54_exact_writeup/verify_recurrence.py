"""Rebuild the native CMF and check its exact companion certificate.

Kernel identification is proved by contour functionals in the manuscript;
this script verifies the separate rational-matrix and nonvanishing facts.
"""
import json,sys,time
from pathlib import Path
import sympy as s
from functools import lru_cache
from flint import fmpq,fmpq_poly
from ramanujantools import Matrix,Position
from ramanujantools.cmf import MeijerG,pFq
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[2];OUT=ROOT/'results/pfq54_exact_writeup'
n=s.Symbol('n');axes=s.symbols('a0:5')+s.symbols('b0:5')
started=time.perf_counter()
M=MeijerG(5,2,5,5,1).trajectory_matrix(
    Position(dict(zip(axes,(16,17,-11,-12,-10,2,1,0,-1,-2)))),
    Position(dict(zip(axes,(1,1,0,0,0,0,0,0,0,0)))))
print('Trajectory obtained.',flush=True)
C=M.as_companion();U=M.companion_coboundary_matrix()[:,:3]
print('Companion obtained.',flush=True)
assert C.shape==(3,3)
assert C[:,:2]==Matrix([[0,0],[1,0],[0,1]])
# Use exact polynomial arithmetic instead of distributing hundreds of
# SymPy factors into intermediate symbolic sums.
class RF:
    def __init__(self,p,q=None):
        self.p=p;self.q=fmpq_poly([1]) if q is None else q
        assert self.q!=0
        g=self.p.gcd(self.q)
        self.p=self.p//g;self.q=self.q//g
    def __add__(self,o):return RF(self.p*o.q+o.p*self.q,self.q*o.q)
    def __mul__(self,o):return RF(self.p*o.p,self.q*o.q)
    def __neg__(self):return RF(-self.p,self.q)
    def __sub__(self,o):return self+-o
    def __pow__(self,k):
        if k<0:return RF(self.q**(-k),self.p**(-k))
        return RF(self.p**k,self.q**k)
@lru_cache(None)
def rf(x):
    if x==n:return RF(fmpq_poly([0,1]))
    if x.is_Rational:return RF(fmpq_poly([fmpq(int(x.p),int(x.q))]))
    if x.is_Add:
        v=rf(s.S.Zero)
        for a in x.args:v=v+rf(a)
        return v
    if x.is_Mul:
        v=rf(s.S.One)
        for a in x.args:v=v*rf(a)
        return v
    if x.is_Pow and x.exp.is_Integer:return rf(x.base)**int(x.exp)
    raise ValueError(x)
V=U.subs({n:n+1})
for i in range(4):
    for j in range(3):
        a=rf(s.S.Zero);b=rf(s.S.Zero)
        for k in range(4):a=a+rf(M[i,k])*rf(V[k,j])
        for k in range(3):b=b+rf(U[i,k])*rf(C[k,j])
        assert (a-b).p==0,(i,j)
print('Coboundary identity checked.',flush=True)
assert U[:,0]==Matrix([1,0,0,0])
R=Matrix([[1,0,0,0],[0,0,-s.Rational(1,2),s.Rational(1,4)],[0,0,0,-s.Rational(1,6)]])
T=R*U.subs({n:0});det=T.det();assert det!=0
checks=[]
for i in range(3):
    a,b=C[i,2].as_numer_denom()
    for name,z in ([('numerator',a)] if i==0 else [])+[('denominator',b)]:
        ds=[]
        for f in s.Mul.make_args(s.factor(z)):
            if f.is_Pow:
                assert f.exp.is_Integer and f.exp>0
                f=f.base
            p=s.Poly(f,n);cs=p.all_coeffs()
            assert p.eval(0)!=0 and (all(v>=0 for v in cs) or all(v<=0 for v in cs))
            ds.append(int(p.degree()))
        checks.append(dict(coefficient=i,part=name,factor_degrees=ds))
axes_h=s.symbols('x0:5')+s.symbols('y0:4')
H=pFq(5,4,1).trajectory_matrix(
    Position(dict(zip(axes_h,(13,14,-14,-15,12,1,2,3,4)))),
    Position(dict(zip(axes_h,(1,1,0,0,1,1,1,1,1)))))
K=Matrix(4,4,lambda i,j:s.binomial(j,i)*(2*n)**(j-i) if j>=i else 0)
Kplus=K.subs({n:n+1})
scalar=416*(6*n+1)*(6*n+5)*s.prod(12*n+j for j in(1,5,7,11))*s.prod(13*n+j for j in range(1,13))
scalar/=1125*(n+1)**3*(2*n+1)*(3*n+1)*(3*n+2)*s.prod(5*n+j for j in range(1,5))*s.prod(15*n+j for j in(1,2,4,7,8,11,13,14))
for i in range(4):
    for j in range(4):
        a=rf(s.S.Zero);b=rf(s.S.Zero)
        for k in range(4):
            a=a+rf(K[i,k])*rf(M[k,j])
            b=b+rf(H[i,k])*rf(Kplus[k,j])
        assert (a-rf(scalar)*b).p==0,(i,j)
print('All 16 Meijer-G / 5F4 gauge entries checked.',flush=True)
data=dict(status='NUMERICAL_CANDIDATE',reconstructed_from_cmf=True,
    exact_coboundary_identity_zero_entries=12,companion_dimension=3,
    C_last_column=[str(s.factor(C[i,2])) for i in range(3)],
    U0=str(U.subs({n:0})),T=str(T),detT=str(det),nonvanishing_checks=checks,
    pfq_gauge=dict(symbolic_zero_entries=16,scalar=str(scalar),K=str(K)),
    elapsed_seconds=time.perf_counter()-started,
    scope='Exact rational matrix facts. The manuscript separately supplies the contour-functional identification.')
(OUT/'native_recurrence.json').write_text(json.dumps(data,indent=2)+'\n')
print('Exact companion identity, initial rank, and all-index nonvanishing checks passed.',flush=True)
print('det(T) =',det,flush=True)
print('seconds =',data['elapsed_seconds'],flush=True)
