"""Exact limiting matrix data for the user's supplied dual-convergence route."""
import sys,json
from pathlib import Path
from functools import lru_cache
import sympy as s
from flint import fmpq,fmpq_poly,arb,ctx
from ramanujantools import Position
from ramanujantools.cmf import MeijerG
n=s.Symbol('n');axes=s.symbols('a0:5')+s.symbols('b0:5')
G=MeijerG(5,2,5,5,1).trajectory_matrix(
    Position(dict(zip(axes,(-16,-17,11,12,10,-2,-1,0,1,2)))),
    Position(dict(zip(axes,(0,0,1,1,2,0,0,0,0,0)))))
assert list(G[3,:].factor())==[0,0,0,-1]
class RF:
    def __init__(self,p,q=None):
        self.p=p;self.q=fmpq_poly([1]) if q is None else q
        g=self.p.gcd(self.q);self.p=self.p//g;self.q=self.q//g
    def __add__(self,o):return RF(self.p*o.q+o.p*self.q,self.q*o.q)
    def __mul__(self,o):return RF(self.p*o.p,self.q*o.q)
    def __pow__(self,k):return RF(self.p**k,self.q**k) if k>=0 else RF(self.q**(-k),self.p**(-k))
@lru_cache(None)
def rf(x):
    if x==n:return RF(fmpq_poly([0,1]))
    if x.is_Rational:return RF(fmpq_poly([fmpq(int(x.p),int(x.q))]))
    if x.is_Add:
        z=rf(s.S.Zero)
        for a in x.args:z=z+rf(a)
        return z
    if x.is_Mul:
        z=rf(s.S.One)
        for a in x.args:z=z*rf(a)
        return z
    if x.is_Pow and x.exp.is_Integer:return rf(x.base)**int(x.exp)
    raise ValueError(x)
def asymptotic(i,j):
    z=rf(G[i,j]);degree=z.p.degree()-z.q.degree()+i-j
    assert degree<=0
    return s.Rational(str(z.p.leading_coefficient()/z.q.leading_coefficient())) if degree==0 else s.S.Zero
Q=s.Matrix(3,3,asymptotic)
x=s.Symbol('x');poly=Q.charpoly(x).as_expr();w=s.Matrix([1,10,100]);V=Q.inv().T
cyclic=s.det(s.Matrix.hstack(w,V*w,V**2*w))
assert cyclic!=0
assert s.discriminant(poly,x)!=0
roots=[r.evalf(50) for r in s.Poly(poly,x).all_roots(radicals=False)]
upper=s.Rational(7203,10**27)
eps=s.Rational(102,10**51)
c0=s.Poly(poly,x).nth(0)
assert s.discriminant(poly,x)<0
assert c0<0 and poly.subs(x,upper)>0
assert upper**3/(-c0)<eps**2
# Exact dyadic log-series certificate for -log(eps)>112.8.
from fractions import Fraction as Fr
def logunit(z):
    u=(z-1)/(z+1)
    lo=2*sum((u**(2*j+1)/Fr(2*j+1) for j in range(35)),Fr(0))
    return lo,lo+2*u**71/(71*(1-u*u))
z=Fr(10**51,102);k=0
while z>=2:z/=2;k+=1
lo=logunit(z)[0]+k*logunit(Fr(2))[0]
assert lo>Fr(564,5)
data={'status':'NUMERICAL_CANDIDATE','scope':'Exact limiting matrix and cyclic determinant; not a proof of the nonautonomous modal-basis theorem.',
'Q_infinity':str(Q),'characteristic_polynomial':str(poly),'characteristic_coefficients':[str(x) for x in s.Poly(poly,x).all_coeffs()],
'cyclic_determinant':str(cyclic),'discriminant':str(s.discriminant(poly,x)),
'roots_display_only':[str(x) for x in roots], 'rational_root_upper':str(upper), 'tau_upper':str(eps), 'log_rate_rational_lower':str(lo), 'certified_rate_exceeds':'112.8'}
out=Path(__file__).resolve().parents[1]/'certificates/spectral_data.json';out.write_text(json.dumps(data,indent=2)+'\n')
print('Characteristic polynomial:',poly)
print('Exact discriminant, root bracket, cyclicity, and tau < 1.02e-49 checks passed.')
