"""Exact coefficient audit for the second-derivative dual identity."""
from pathlib import Path
import math,json,pickle
from flint import fmpq,fmpq_mat
import sympy as s
ROOT=Path(__file__).resolve().parent

def coefficients(N):
 t=s.Symbol('t');c=450*N*N+55*N+2;K=-10*N-1
 J=[[4*N*N*(13725*N*N+2389*N+103),-6*N*(275*N*N+150*N+11),-450*N*N-43*N+2,3],
 [N*(5*N+1)*(330*N+23),N*(450*N+43),-2,0],[-(18*N+1)*(25*N+1),1,0,0]]
 Q=[s.Poly(sum(a*(-t-12*N-1)**r for r,a in enumerate(row)),t) for row in J]
 H3=[fmpq(0)];H4=[fmpq(0)]
 for k in range(1,19*N+1):
  H3.append(H3[-1]+fmpq(1,k**3));H4.append(H4[-1]+fmpq(1,k**4))
 C=[fmpq(int(q.nth(3)*(c-2*K-1)-q.nth(2))) for q in Q]
 A=[fmpq(0) for _ in range(3)];Z3=A.copy()
 zeros=list(range(N+1,12*N+1))+list(range(1,11*N+1))+list(range(2*N,10*N+1))
 iv=[(13*N+1,28*N+1),(14*N+1,29*N+1)]
 for k in range(13*N+1,29*N+2):
  num=[r-k for r in zeros];den=[r-k for a,b in iv for r in range(a,b+1) if r!=k]
  top=fmpq(math.prod(num),math.prod(den));m=sum(a<=k<=b for a,b in iv)
  log1=sum((fmpq(1,r) for r in num),fmpq(0))-sum((fmpq(1,r) for r in den),fmpq(0))
  for j,q in enumerate(Q):
   h=int(q.eval(-k));hd=int(q.diff().eval(-k))
   if m==2:c2=h*top;c1=hd*top+h*top*log1
   else:c2=fmpq(0);c1=h*top
   A[j]+=6*c2;Z3[j]+=2*c1
   C[j]-=2*c1*H3[k-10*N-1]+6*c2*H4[k-10*N-1]
 assert Z3==[0,0,0]
 return A,C

data=json.loads((ROOT/'independent_matrix_certificate.json').read_text())
def rational(text):
 parts=str(text).split('/')
 return fmpq(int(parts[0]),int(parts[1]) if len(parts)>1 else 1)
def evaluate(coeffs,n):
 result=fmpq(0)
 for c in reversed(coeffs):result=result*n+rational(c)
 return result
def step(n):
 den=evaluate(data['common_denominator_coefficients'],n)
 return fmpq_mat([[evaluate(data['numerator_coefficients'][i][j],n)/den for j in range(4)] for i in range(4)])
Ns=[0,1,2,4,8,12,20]
walks=[];W=fmpq_mat([[int(i==j) for j in range(4)] for i in range(4)])
for N in range(max(Ns)+1):
 if N in Ns:walks.append(fmpq_mat(W))
 if N<max(Ns):W=W*step(N)
rows=[]
for N,W in zip(Ns,walks):
 A,C=coefficients(N);I=W.inv()
 checks=[A[j]==(-1)**N*6*I[j,2] and C[j]==(-1)**N*(-2)*(I[j,0]-I[j,1]) for j in range(3)]
 assert all(checks),(N,checks)
 print('N',N,'all3 zeta4/rational coefficient identities PASS',flush=True)
 rows.append({'N':N,'all_three_columns_exact':True})
(ROOT/'second_dual_checks.json').write_text(json.dumps(rows,indent=2))
