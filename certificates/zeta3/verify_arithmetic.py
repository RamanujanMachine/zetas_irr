"""Include all one-integer offsets at floor walls using exact infinitesimals.

A pair (q,c) denotes q+c*epsilon, epsilon>0 infinitesimal. Floors and interval
membership are evaluated lexicographically, so no finite p sampling is used.
"""
from fractions import Fraction as F
import json
NEG=(16,17,18,15,14,17,18,19,16,15)
POS=(11,10,9,12,13,12,11,10,13,14)
EXTRA=(10,9,8,11,12)
def fl(x):return x.numerator//x.denominator

def add(a,b):return a[0]+b[0],a[1]+b[1]
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def floor(a):return fl(a[0])-(a[0].denominator==1 and a[1]<0)
def candidates(x,lo,hi,slopes):
    walls={lo*x,hi*x}
    for c in slopes:
        for j in range(fl((lo+c)*x)-1,fl((hi+c)*x)+2):
            y=F(j)-c*x
            if lo*x<=y<=hi*x:walls.add(y)
    walls=sorted(walls)
    return [(y,s) for y in walls for s in range(-3,4)]+[((a+b)/2,0) for a,b in zip(walls,walls[1:])]

def top(x,y,intervals,nums):
    v=sum(s*floor(add(y,(c*x,d))) for c,d,s in nums)
    m=0
    for a,b in intervals:
        if a<=y<=b:v-=floor(sub(y,a))+floor(sub(b,y));m+=1
        elif y<a:v-=floor(sub(b,y))-floor(add(sub(a,y),(F(0),-1)))
        else:v-=floor(sub(y,a))-floor(add(sub(y,b),(F(0),-1)))
    return v,m

def original_eps(x):
    iv=[((F(0),0),(10*x,1)),((x,0),(11*x,0)),((2*x,0),(12*x,0))]
    am=10**6;cm=10**6
    for y in candidates(x,0,12,(17,16,2,1,0,-1,-2,-10,-11,-12)):
        if not (F(0),0)<=y<=(12*x,0):continue
        v,m=top(x,y,iv,[(17,0,1),(16,0,1),(2,0,-1),(1,0,-1)])
        if m==3:am=min(am,v)
        loss=(m-1)*(add(y,(17*x,0))>=(F(1),0))+2*(add(y,(2*x,0))>=(F(1),0))
        cm=min(cm,v-loss)
    det=sum(floor((k*x,0)) for k in NEG)-sum(floor((k*x,0)) for k in POS)-sum(floor((k*x,1)) for k in EXTRA)
    return max(0,det-am-cm),(am,cm,det)

def dual_eps(x):
    iv=[((13*x,1),(28*x,1)),((14*x,1),(29*x,1))]
    e=0
    for y in candidates(x,13,29,(-1,0,-2,-12,-11,-10,-13,-28,-14,-29)):
        if not (13*x,1)<=y<=(29*x,1):continue
        v,m=top(x,y,iv,[(-1,-1,1),(0,-1,1),(-2,0,1),(-12,-1,-1),(-11,-1,-1),(-10,-1,-1)])
        derivative_max=max(add(y,(F(0),-1)),sub((29*x,1),y))
        loss=(m-1)*(derivative_max>=(F(1),0))+2*(add(y,(-11*x,-1))>=(F(1),0))
        e=max(e,loss-v)
    return e

def main():
    walls=sorted({F(i,d) for d in range(1,30) for i in range(d+1)})
    cells=[]
    for a,b in zip(walls,walls[1:]):
        x=(a+b)/2
        e0=min(original_eps(x)[0],dual_eps(x))
        ep=min(original_eps(x+1)[0],dual_eps(x+1))
        if cells and cells[-1][2:]==(e0,ep):cells[-1]=(cells[-1][0],b,e0,ep)
        else:cells.append((a,b,e0,ep))
    initial=sum((e0*(1/a-1/b) for a,b,e0,ep in cells if e0),F(0))
    mean=sum((ep*(b-a) for a,b,e0,ep in cells),F(0))
    assert len(cells)==56 and initial==F(9967051,272272) and mean==F(1313791,604656)
    K=4096;D=10**16
    def ceil_units(q):return (q.numerator*D+q.denominator-1)//q.denominator
    units=ceil_units(initial)
    for k in range(1,K+1):
        for a,b,e0,ep in cells:
            units+=ceil_units(ep*(1/(k+a)-1/(k+b)))
    units+=ceil_units(mean/K)
    assert units==387839934501989356
    assert F(units,D)<F(4848,125)
    print(json.dumps(dict(status='PASS',farey_chambers=len(walls)-1,merged_cells=len(cells),
          initial_integral=str(initial),periodic_mean=str(mean),periods_summed=K,
          certified_upper=f'{units//D}.{units%D:016d}',target='38.784'),indent=2))

if __name__=='__main__':main()
