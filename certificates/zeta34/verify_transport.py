"""Check the dual formal-functional path and pairing at every small-N step."""
import json
import pickle
from pathlib import Path
import sympy as sp
from flint import fmpq, fmpq_mat
from functools import lru_cache
from flint import fmpq_poly

ROOT=Path(__file__).resolve().parent

@lru_cache(None)
def harmonic(k,s):
    return sum((fmpq(1,i**s) for i in range(1,k+1)),fmpq(0))

@lru_cache(None)
def bernoulli(m,K):
    b=sp.bernoulli(m,K+1)
    return fmpq(int(b.p),int(b.q))

def linear_poly(h):
    return fmpq_poly([-h,1])

def theta_matrix(a,b):
    pa=fmpq_poly([1]);pb=fmpq_poly([1])
    for x in a: pa*=linear_poly(x-1)
    for x in b: pb*=linear_poly(x)
    d=pa-pb
    assert d.degree()==4 and d[4]>0
    T=fmpq_mat(4,4)
    for j in range(3): T[j+1,j]=1
    for j in range(4): T[j,3]=-d[j]/d[4]
    return T

def eye():
    return fmpq_mat([[int(i==j) for j in range(4)] for i in range(4)])


data=json.loads((ROOT/'independent_matrix_certificate.json').read_text())
def rational(text):
    a=str(text).split('/')
    return fmpq(int(a[0]),int(a[1]) if len(a)>1 else 1)
def evaluate(coeffs,n):
    q=fmpq(0)
    for c in reversed(coeffs):q=q*n+rational(c)
    return q
def walk(N):
    W=eye()
    for n in range(N):
        den=evaluate(data['common_denominator_coefficients'],n)
        W=W*fmpq_mat([[evaluate(data['numerator_coefficients'][i][j],n)/den for j in range(4)] for i in range(4)])
    return W

def coefficients(roots,sign,K):
    cols=[]
    for j in range(4):
        rr=roots.copy();rr[0]=rr.get(0,0)+j;rr={h:e for h,e in rr.items() if e}
        num=fmpq_poly([sign*(-1)**j]);den=fmpq_poly([1])
        for h,e in rr.items():
            if e>0:num*=linear_poly(h)**e
            else:den*=linear_poly(h)**(-e)
        poly,_=divmod(num,den)
        result=[fmpq(0)]*4
        result[2]=-sum((m*poly[m]*bernoulli(m-1,K) for m in range(1,len(poly))),fmpq(0))
        for h,e in rr.items():
            if e>=0:continue
            d=-e;assert d<=2 and h<=K
            top=fmpq(sign*(-1)**j);ell1=fmpq(0)
            for r,exponent in rr.items():
                if r==h:continue
                top*=fmpq(h-r)**exponent;ell1+=fmpq(exponent,h-r)
            cs={d:top}
            if d==2:cs[1]=top*ell1
            for order,c in cs.items():
                result[2-order]+=order*(order+1)*c
                result[2]-=order*(order+1)*c*harmonic(K-h,order+2)
        cols.append(result)
    return fmpq_mat([[cols[j][i] for j in range(4)] for i in range(4)])

def J(N):
    return fmpq_mat([
        [4*N*N*(13725*N*N+2389*N+103),-6*N*(275*N*N+150*N+11),-450*N*N-43*N+2,3],
        [N*(5*N+1)*(330*N+23),N*(450*N+43),-2,0],
        [-(18*N+1)*(25*N+1),1,0,0],
        [0,0,0,0],
    ])

def run(N):
    a=[0,0,1,1,-1];b=[0]*5;roots={0:-2,1:1};sign=1;K=0
    C=coefficients(roots,sign,K)
    C0=fmpq_mat([[-6,0,0,0],[2,2,0,0],[0,0,-1,0],[0,0,0,0]])
    assert C==C0
    D=eye();steps=0;min_leading=4
    actions=[('a',0,-1,11*N),('a',1,-1,12*N),('a',4,-1,10*N),
             ('K',0,0,1),('a',2,1,16*N),('a',3,1,17*N),
             ('b',3,1,N),('b',4,1,2*N),('b',1,-1,N),('b',2,-1,2*N)]
    for kind,i,direction,count in actions:
        if kind=='K':
            K=2*N
            assert coefficients(roots,sign,K)==C
            continue
        for _ in range(count):
            oldT=theta_matrix(a,b)
            if kind=='a':
                old=a[i];a[i]+=direction;s=1 if i<2 else -1
                if direction==-1:
                    factor=s*(oldT-(old-1)*eye())
                    h=1-old;exponent=1;sign*=-s
                else:
                    factor=(s*(theta_matrix(a,b)-(a[i]-1)*eye())).inv()
                    h=-old;exponent=-1;sign*=-s
            else:
                old=b[i];b[i]+=direction
                if direction==1:
                    factor=-(oldT-old*eye());h=-old;exponent=1
                else:
                    factor=(-(theta_matrix(a,b)-b[i]*eye())).inv()
                    h=-b[i];exponent=-1
            roots[h]=roots.get(h,0)+exponent
            if not roots[h]:del roots[h]
            C=C*factor;D=D*factor;steps+=1
            assert roots.get(K,0)+sum(bb==-K for bb in b)>=3
            exact=coefficients(roots,sign,K)
            assert C==exact,(N,steps,C-exact)
            min_leading=min(min_leading,5-sum(a)+sum(b))
    ww=walk(N)
    W=ww
    assert W*J(N)*D.transpose()==J(0)
    V=fmpq_mat([[ww[i,j] for j in range(3)] for i in range(3)])
    T=V.inv().transpose()
    u=fmpq_mat([[2,-2,0]])*T;v=fmpq_mat([[0,0,6]])*T
    J3=fmpq_mat([[J(N)[i,j] for j in range(4)] for i in range(3)])
    target=fmpq_mat([[v[0,j] for j in range(3)],[0]*3,[-u[0,j] for j in range(3)],[0]*3])
    assert C*J3.transpose()==target
    assert sign==(-1)**N
    return dict(N=N,checked_axis_steps=steps,all_formal_coefficient_steps_match=True,
                exact_pairing_identity=True,all_three_readout_columns_match=True,
                minimum_theta4_coefficient=min_leading,cutoff_unshifted=K,
                cutoff_shifted_first_summand=-10*N,all_g_boundary_zeros_have_order_at_least_three=True)

if __name__=='__main__':
    results=[run(N) for N in [1,2]]
    print(json.dumps(results,indent=2))
    (ROOT/'second_functional_transport_checks.json').write_text(json.dumps(results,indent=2)+'\n')
