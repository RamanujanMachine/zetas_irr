"""Exact finite certificates accompanying the explicit uniform gcd argument.

Chamber enumeration covers real parameter cells, not sampled trajectory
depths. Small-n coefficient checks are separate implementation checks.
"""
from fractions import Fraction as F
from itertools import permutations, combinations
from pathlib import Path
import json, sys, math

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/pfq54_uniform_gcd'
OUT.mkdir(exist_ok=True)
NORMS=[((8,13,13),(17,17)),((11,11,11),(14,19)),
       ((9,9,14),(16,16)),((12,12,12),(18,18)),
       ((11,11,14),(18,18)),((9,9,12),(14,16)),
       ((10,10,10),(14,16)),((9,11,14),(17,17))]

def floor(x):return x.numerator//x.denominator
def c0(x):return 2*floor(15*x)-3*floor(10*x)
def phi(x):
    return max([0]+[c0(x)-sum(floor(d*x) for d in D)+sum(floor(l*x) for l in L) for L,D in NORMS])

witnesses=[]
for norm in NORMS:
    b=next(b for b in permutations((-2,-1,0,1,2))
           if (tuple(sorted((10+b[0],11+b[1],12+b[2]))),tuple(sorted((16-b[3],17-b[4]))))==norm)
    witnesses.append(dict(L=norm[0],D=norm[1],pairing=b))
cuts=sorted({F(i,j) for j in range(1,20) for i in range(j+1)})
cells=[(a,b,phi((a+b)/2)) for a,b in zip(cuts,cuts[1:])]
assert all(0<=v<=3 for a,b,v in cells)
assert all(v==0 for a,b,v in cells if b<=F(1,16))
assert all(v<=c0((a+b)/2)+1 for a,b,v in cells if a>=F(1,11) and b<=F(1,8))
merged=[]
for a,b,v in cells:
    if merged and merged[-1][2]==v:merged[-1]=(merged[-1][0],b,v)
    else:merged.append((a,b,v))
S=sum(v*(1/(k+a)-1/(k+b)) for a,b,v in cells if v for k in range(8))
assert S>F(20004,1000)>20

# All root-count break lines y=a*x+b. Include the lines defining the support.
lines=[(0,0),(0,1),(1,0),(2,0),(10,0),(-1,1),(-2,1),
       (10,-1),(11,-1),(12,-1),(-17,2),(-16,2),(-17,3)]
xcuts={F(1,11),F(1,8)}
for (a,b),(c,d) in combinations(lines,2):
    if a!=c:
        x=F(d-b,a-c)
        if F(1,11)<x<F(1,8):xcuts.add(x)
xcuts=sorted(xcuts)
xpoints=xcuts[1:-1]+[(a+b)/2 for a,b in zip(xcuts,xcuts[1:])]
count=0
for x in xpoints:
    ycuts=sorted({F(0),F(1)}|{a*x+b for a,b in lines if 0<a*x+b<1})
    ys=ycuts[1:-1]+[(a+b)/2 for a,b in zip(ycuts,ycuts[1:])]
    for y in ys:
        c=int(y<=10*x)+int(y>x)+int(y>2*x)+sum(int(y<=a*x-1) for a in (10,11,12))
        d=int(y<=1-x)+int(y<=1-2*x)+int(y>=2-17*x)+int(y>=2-16*x)+int(y>=3-17*x)
        support=(y>12*x-1 and y>=2-16*x and y<=1-2*x)
        assert c-d>=-1
        assert (c-d==-1)==support
        if support:
            assert c==3 and d==4 and y>2*x
            assert y<=10*x and y>2*x and y>12*x-1
            assert y<=1-2*x and y>=2-16*x and y<3-17*x
        count+=1
    # The residue k=0 is separate: roots at p or 2p.
    c=1+int(1<=10*x)+int(1<=11*x)
    d=2+int(2<=17*x)
    assert c>=d

result=dict(status='NUMERICAL_CANDIDATE',scope='Exact finite ingredients for the accompanying arithmetic proof, not a final independence claim',
            normalizations=witnesses,profile=[dict(lo=str(a),hi=str(b),gain=v) for a,b,v in merged],
            eight_period_density=str(S),eight_period_density_decimal=float(S),strict_density_lower='29.004',
            root_count_x_chambers=len(xcuts)-1,root_count_cell_checks=count,
            excluded_primes='p<=29 or p*p<=30*n or p divides n')

# A rational interval proof of the required height bound, using concavity.
def log_unit(z):
    assert 1<=z<=2
    v=(z-1)/(z+1);M=35
    a=2*sum(v**(2*j+1)/F(2*j+1) for j in range(M))
    return a,a+2*v**(2*M+1)/(F(2*M+1)*(1-v*v))
L2=log_unit(F(2))
def log_interval(z):
    z=F(z);k=0
    while z>=2:z/=2;k+=1
    while z<1:z*=2;k-=1
    a,b=log_unit(z)
    return (a+k*L2[0],b+k*L2[1]) if k>=0 else (a+k*L2[1],b+k*L2[0])
def polynomial(y):return 15*y**3+55*y**2-1830*y-11968
a,b=F(12014,1000),F(12015,1000)
assert polynomial(a)<0<polynomial(b)
y=(a+b)/2
plus=[y+10,y+11,y+12]
minus=[y,y+1,y+2,y-1,y-2,16-y,17-y]
upper=sum(t*log_interval(t)[1] for t in plus)-sum(t*log_interval(t)[0] for t in minus)
der=log_interval((y+10)*(y+11)*(y+12)*(16-y)*(17-y)/(y*(y+1)*(y+2)*(y-1)*(y-2)))
upper+=(b-a)/2*max(abs(v) for v in der)+30*log_interval(F(3,2))[1]
assert upper<F(6546,100)
assert F(6546,100)+76-(S+9)<F(225,2)
result['height']=dict(root_bracket=[str(a),str(b)],rational_interval_upper_decimal=float(upper),
                      chosen_upper='65.46',reduced_denominator_limsup_upper_decimal=float(F(6546,100)+76-S-9),
                      eventual_reduced_denominator_exponent='112.5')

# Separate exact implementation checks of the coefficient/readout formulas.
if '--finite' in sys.argv:
    sys.path.insert(0,str(ROOT/'work/meijerg5255_arithmetic/arithmetic'))
    from partial_fractions import pf,pf_fast,kernel_readout
    from flint import fmpq, fmpq_mat
    from sympy import primerange
    import sympy as sp
    sys.path.insert(0,str(ROOT/'work/pfq54_row_prime'))
    from search import segment, START, DIRECTION, ROWS
    gauge=json.loads((ROOT/'results/pfq54_exact_writeup/native_recurrence.json').read_text())['pfq_gauge']
    z=sp.Symbol('n')
    kratio=sp.prod(12*z+i for i in range(1,13))*sp.prod(13*z+i for i in range(1,14))
    kratio/=sp.prod(sp.prod(k*z+i for i in range(1,k+1)) for k in (1,2,3,4,15))
    assert sp.cancel(kratio-sp.sympify(gauge['scalar']))==0
    result['gauge_scalar_factorial_identity']=True
    Ws=[segment(START,tuple(s+k*d for s,d in zip(START,DIRECTION))) for k in (0,1,2)]
    U=fmpq_mat([[W[i,0] for W in Ws] for i in range(4)])
    R=fmpq_mat([[1,0,0,0],[0,0,fmpq(-1,2),fmpq(1,4)],[0,0,0,fmpq(-1,6)]])
    T=R*U
    assert all(int(T[i,j].denominator)%101 for i in range(3) for j in range(3))
    Tmod=[[int(T[i,j].numerator)%101*pow(int(T[i,j].denominator)%101,-1,101)%101 for j in range(3)] for i in range(3)]
    assert Tmod==[[1,89,15],[0,35,64],[0,98,61]]
    assert int(fmpq_mat(Tmod).det())%101==4
    saved_U=sp.sympify(json.loads((ROOT/'results/candidates/MG5255_FORWARD_PFQ54_EQUIVALENT/companion_readout.json').read_text())['U0'])
    assert all(fmpq(str(saved_U[i,j]))==U[i,j] for i in range(4) for j in range(3))
    result['rational_initial_rows_basis']=dict(modulus=101,reduced_matrix=Tmod,determinant_mod_101=4,
                                              fresh_columns_equal_saved_companion_U0=True)
    def vp(q,p):
        if not q:return 10**8
        out=0
        for sign,a in ((1,abs(int(q.numerator))),(-1,int(q.denominator))):
            while a%p==0:out+=sign;a//=p
        return out
    tests=[]
    for n in (1,2,3,4,5,8,12,20,40):
        cs=pf_fast(n)
        if n<=4:assert cs==pf(n)
        Q,P3,P4=kernel_readout(n)
        kappa=fmpq(math.factorial(12*n)*math.factorial(13*n),math.prod(math.factorial(k*n) for k in (1,2,3,4,15)))
        W=segment(START,tuple(s+n*d for s,d in zip(START,DIRECTION)))
        Y=ROWS*W
        assert tuple((-1)**n*kappa*Y[i,0]/12 for i in (2,0,1))==(Q,P3,P4)
        C=fmpq(math.factorial(15*n)**2,math.factorial(10*n)**3)
        D=math.lcm(*range(1,19*n+1))
        X=[6*C*D**4*z for z in (Q,P3,P4)]
        assert all(z.denominator==1 for z in X)
        for L,ds in NORMS:
            Cb=fmpq(math.prod(math.factorial(d*n) for d in ds),math.prod(math.factorial(l*n) for l in L))
            assert all((Cb*a).denominator==1 and (D*Cb*b).denominator==1 for a,b in cs.values())
        checked=0
        for p in primerange(30,19*n+1):
            if p*p<=30*n or n%p==0:continue
            h=3 if 18*n<p<19*n else 2 if 17*n<p<18*n else 1 if 16*n<p<17*n else 0
            s=int(8*n<p<11*n)
            g=phi(F(n,p))+h+s
            assert min(vp(z,p) for z in X)>=g,(n,p,g)
            if s:assert vp(Q,p)>=1 and vp(P3,p)>=-1 and vp(P4,p)>=-2
            checked+=1
        tests.append(dict(n=n,prime_checks=checked,all_three_forward_readouts_equal=True))
    result['finite_checks']=tests

(OUT/'exact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
table='\n'.join(f'{a} & {b} & {v} \\\\' for a,b,v in merged if v)
(OUT/'profile_rows.tex').write_text(table+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('profile','normalizations')},indent=2))
print('Pairings:',witnesses)
