"""Generic exact coefficient-level certificate for the adjoint pairing."""
import sympy as s,json,sys
from pathlib import Path
from math import comb
x,r=s.symbols('x r')
u=s.symbols('u:4');q=s.symbols('q:5')
U=s.Poly(x**4+sum(u[i]*x**i for i in range(4)),x)
Q=s.Poly(x**5+sum(q[i]*x**i for i in range(5)),x)

def jmat(P,Q):
 def coeff(poly,k):return poly.nth(k)
 return s.Matrix(4,4,lambda a,b:(-1)**b*(coeff(P,a+b+1)-coeff(Q,a+b+1)+sum((-1)**ell*comb(b+ell,ell)*coeff(P,a+b+ell+1) for ell in range(1,5-a-b))))

def theta(P,Q):
 C=P-Q;d=C.nth(4)
 T=s.zeros(4)
 for i in range(3):T[i+1,i]=1
 for i in range(4):T[i,3]=-C.nth(i)/d
 return T

def dual(P,Q):return s.Poly(-P.as_expr().subs(x,-x-1),x),s.Poly(-Q.as_expr().subs(x,-x),x)

def assertzero(Z):
 coeffs=[s.cancel(z) for z in Z]
 assert all(z==0 for z in coeffs),coeffs

# An upper decrement: P=(x-r)U changes to Pnew=(x-r+1)U.
P=s.Poly((x-r)*U.as_expr(),x);Pn=P+U
Pd,Qd=dual(Pn,Q)
assertzero((theta(P,Q)-r*s.eye(4))*jmat(Pn,Q)+jmat(P,Q)*(theta(Pd,Qd).T+r*s.eye(4)))
print('generic upper decrement pairing: verified',flush=True)
# A lower increment: Q=(x-r)U changes to Qnew=(x-r-1)U.
P=Q;Q=s.Poly((x-r)*U.as_expr(),x);Qn=Q-U
Pd,Qd=dual(P,Qn)
assertzero((theta(P,Q)-r*s.eye(4))*jmat(P,Qn)+jmat(P,Q)*(theta(Pd,Qd).T+(r+1)*s.eye(4)))
print('generic lower increment pairing: verified',flush=True)
Path(sys.argv[1] if len(sys.argv)>1 else 'pairing_certificate.json').write_text(json.dumps({'upper_decrement_identity':True,'lower_increment_identity':True,'method':'Exact SymPy rational simplification of all16entries withgenericmonicpolynomialcoefficients; inversestepsfollowbyinversion.'},indent=2))
