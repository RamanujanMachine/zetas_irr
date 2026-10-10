"""Independent Q(n) reconstruction of the complete72-step MG55 trajectory.
Uses only FLINT polynomial arithmetic and a hand-written companion inverse,
not RT axis construction, trajectory_matrix, or symbolic matrix operations.
"""
import time,json
from pathlib import Path
from flint import fmpq_poly as Poly,fmpq
import sympy as s
zero=Poly([]);one=Poly([1]);n=Poly([0,1])

def eye():return [[one if i==j else zero for j in range(4)]for i in range(4)]
def rootpoly(roots):
 coeff=[one]
 for r in roots:
  new=[zero for _ in range(len(coeff)+1)]
  for i,c in enumerate(coeff):new[i]-=r*c;new[i+1]+=c
  coeff=new
 return coeff

def theta_coeff(p):
 P=rootpoly([a-1 for a in p[:5]]);Q=rootpoly(p[5:])
 C=[a-b for a,b in zip(P,Q)]
 assert C[5]==0 and C[4].degree()==0 and C[4]!=0
 return [c/C[4][0] for c in C[:4]]

def step(p,ax,d):
 pp=p[:];is_a=ax<5;direct=(d==-1 if is_a else d==1)
 if not direct:pp[ax]+=d
 c0,c1,c2,c3=theta_coeff(pp)
 r=pp[ax]-1 if is_a else pp[ax]
 sign=(1 if ax<2 else -1) if is_a else -1
 if direct:
  A=[[zero for _ in range(4)]for _ in range(4)]
  for i in range(3):A[i+1][i]=one
  for i,c in enumerate((c0,c1,c2,c3)):A[i][3]=-c
  for i in range(4):A[i][i]-=r
  den=one
 else:
  A=[[-c1-c2*r-c3*r*r-r**3,c0,c0*r,c0*r*r],
     [-c2-c3*r-r*r,-r*(c2+c3*r+r*r),c0+c1*r,r*(c0+c1*r)],
     [-c3-r,-r*(c3+r),-r*r*(c3+r),c0+c1*r+c2*r*r],
     [-one,-r,-r*r,-r**3]]
  den=c0+c1*r+c2*r*r+c3*r**3+r**4
  assert den!=0
 return [[sign*x for x in row]for row in A],den

def mul(A,B):return [[sum((A[i][k]*B[k][j]for k in range(4)),zero)for j in range(4)]for i in range(4)]
def sympoly(expr):
 P=s.Poly(expr,s.Symbol('n'));return Poly([fmpq(int(P.nth(i).p),int(P.nth(i).q))for i in range(P.degree()+1)]) if expr!=0 else zero

def build_trajectory():
    start=(1,1,0,0,2,0,0,0,0,0);v=(11,12,-16,-17,10,0,1,2,-1,-2)
    p=[Poly([a,b])for a,b in zip(start,v)];W=eye();den=one
    order=(2,3,0,1,4,6,7,8,9);count=0;t0=time.monotonic()
    for ax in order:
     d=1 if v[ax]>0 else -1
     for _ in range(abs(v[ax])):
      A,ad=step(p,ax,d);W=mul(W,A);den*=ad
      common=den
      for row in W:
       for w in row:
        common=common.gcd(w)
        if common.degree()==0:break
       if common.degree()==0:break
      if common.degree()>0:
       W=[[w/common for w in row]for row in W];den/=common
      p[ax]+=d;count+=1
    assert count==72
    return W,den


def export(path):
    W,den=build_trajectory()
    A=s.zeros(3)
    for i in range(3):
        for j in range(3):
            if W[i][j]==0:continue
            degree=W[i][j].degree()-den.degree()+i-j
            assert degree<=0
            if degree==0:
                r=W[i][j].leading_coefficient()/den.leading_coefficient()
                A[i,j]=s.Rational(int(r.numerator),int(r.denominator))
    assert all(W[3][j]==0 for j in range(3)) and W[3][3]==-den
    neg=(16,17,18,15,14,17,18,19,16,15)
    pos=(11,10,9,12,13,12,11,10,13,14)
    extra=(10,9,8,11,12)
    fnum=fden=one
    for k in neg:
        for j in range(1,k+1):fnum*=k*n+j
    for k in pos:
        for j in range(1,k+1):fden*=k*n+j
    for k in extra:
        for j in range(2,k+2):fden*=k*n+j
    detnum=sum((W[0][j]*(W[1][(j+1)%3]*W[2][(j+2)%3]-W[1][(j+2)%3]*W[2][(j+1)%3]) for j in range(3)),zero)
    assert detnum*fden==fnum*den**3
    ell=s.Symbol('ell')
    char=A.charpoly(ell).as_expr()
    lo=s.Rational(3601360636638255963141132005273498479,500000000000000000000000000000000000000000000000000000000000)
    hi=s.Rational(7202721273276511926282264010546996959,1000000000000000000000000000000000000000000000000000000000000)
    assert s.Poly(char,ell).eval(lo)<0<s.Poly(char,ell).eval(hi)
    assert s.discriminant(char,ell)<0
    from flint import arb,ctx
    ctx.dps=80
    rootball=arb(fmpq(int(lo.p),int(lo.q))).union(arb(fmpq(int(hi.p),int(hi.q))))
    a=-rootball.log()
    det=A.det()
    b=(arb(fmpq(int(det.p),int(det.q))).log()+a)/2
    assert arb('53.28758332262')<a<arb('53.28758332263')
    assert arb('59.51995592483')<b<arb('59.51995592484')
    result={'method':'Independent 72-step Q(n) reconstruction; no RT or cached matrix input.',
            'block_form_verified':True,'factorial_determinant_identity_verified':True,
            'variable':'n','coefficient_order':'ascending powers',
            'common_denominator_coefficients':[str(c) for c in den.coeffs()],
            'numerator_coefficients':[[[str(c)for c in entry.coeffs()]for entry in row]for row in W],
            'limiting_matrix':[[str(A[i,j])for j in range(3)]for i in range(3)],
            'characteristic_polynomial':str(char),
            'positive_root_bracket':[str(lo),str(hi)],
            'discriminant_negative_verified':True,
            'growth_a':a.str(45),'decay_b':b.str(45)}
    Path(path).write_text(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    import sys
    export(sys.argv[1] if len(sys.argv)>1 else 'independent_matrix.json')
