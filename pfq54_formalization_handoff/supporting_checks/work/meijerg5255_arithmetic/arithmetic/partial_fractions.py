"""Exact rational kernel coefficients for the MeijerG5255 arithmetic audit."""
import sys, math,json
from pathlib import Path
from flint import fmpq
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def pf(n):
    # F(t)=prod_{u=0,1,2}(t-(10+u)n)_{10n}/[(t+n)_{16n+1}(t+2n)_{14n+1}]
    numerator=[k for u in (0,1,2) for k in range(u*n+1,(10+u)*n+1)]
    den=[*range(n,17*n+1),*range(2*n,16*n+1)]
    result={}
    for j in range(n,17*n+1):
      multiplicity=den.count(j)
      c=fmpq(1)
      for k in numerator:c*=(-j-k)
      for h in den:
       if h!=j:c/=h-j
      if multiplicity==1:result[j]=(fmpq(0),c)
      else:
       L=sum((fmpq(1,-j-k)for k in numerator),fmpq(0))-sum((fmpq(1,h-j)for h in den if h!=j),fmpq(0))
       result[j]=(c,c*L)
    assert sum((b for a,b in result.values()),fmpq(0))==0
    return result

def readout(n,eta=0):
    cs=pf(n);H={r:[fmpq(0)]for r in (2,3,4)}
    for k in range(1,17*n+eta+1):
      for r in H:H[r].append(H[r][-1]+fmpq(1,k**r))
    Q=sum((a for a,b in cs.values()),fmpq(0))
    P3=sum((a*H[3][j+eta]+b*H[2][j+eta]/2 for j,(a,b)in cs.items()),fmpq(0))
    P4=sum((a*H[4][j+eta]+b*H[3][j+eta]/3 for j,(a,b)in cs.items()),fmpq(0))
    return Q,P3,P4
if __name__=='__main__':
 for n in (1,2):
  for eta in (0,2*n,3*n):
   Q,P3,P4=readout(n,eta);print(n,eta,str(P3/Q),str(P4/Q))

def pf_fast(n):
    if n==0:return {0:(fmpq(1),fmpq(0))}
    f=[1];H=[fmpq(0)]
    for k in range(1,29*n+1):f.append(f[-1]*k);H.append(H[-1]+fmpq(1,k))
    cs={}
    for j in range(n,17*n+1):
      numer=f[j+10*n]*f[j+11*n]*f[j+12*n]
      denom=f[j]*f[j+n]*f[j+2*n]*f[j-n]*f[17*n-j]
      if j<2*n:
       a=fmpq(0);b=(-1)**(j-n)*fmpq(numer*f[2*n-j-1],denom*f[16*n-j])
      elif j>16*n:
       a=fmpq(0);b=(-1)**(j-n+1)*fmpq(numer*f[j-16*n-1],denom*f[j-2*n])
      else:
       a=(-1)**n*fmpq(numer,denom*f[j-2*n]*f[16*n-j])
       L=sum((H[j+u*n]-H[j+(10+u)*n] for u in(0,1,2)),fmpq(0))+H[j-n]-H[17*n-j]+H[j-2*n]-H[16*n-j]
       b=a*L
      cs[j]=(a,b)
    assert sum((b for a,b in cs.values()),fmpq(0))==0
    return cs

def kernel_readout(n,eta=None):
    if eta is None:eta=2*n
    cs=pf_fast(n);H={r:[fmpq(0)]for r in (2,3,4)}
    for k in range(1,17*n+eta+1):
      for r in H:H[r].append(H[r][-1]+fmpq(1,k**r))
    Q=sum((a for a,b in cs.values()),fmpq(0))
    P3=sum((a*H[3][j+eta]+b*H[2][j+eta]/2 for j,(a,b)in cs.items()),fmpq(0))
    P4=sum((a*H[4][j+eta]+b*H[3][j+eta]/3 for j,(a,b)in cs.items()),fmpq(0))
    return Q,P3,P4
