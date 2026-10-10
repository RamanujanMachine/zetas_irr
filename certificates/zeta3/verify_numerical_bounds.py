"""Integer/rational certificate for the spectral and final numerical bounds.
Python standard library only. The cubic is independently reconstructed by
verify_matrix.py; the arithmetic upper bound is proved by verify_arithmetic.py.
"""
from fractions import Fraction as F
import json
import sys

c2=F(83220721427294106907399200607730930785765129529801897078934559,1484577825190137274336280508756918272)
c1=F(731334801243107466089356596505717853275074571608716447379201100334794667003154611901941573810757,146466868948884247884332915718530654652342544)
c0=F(76623012348334313797938377862237790794460627983667564193521662995163373351121226574589853696,2130520759189220333584634002331004844478493702212809977860478179)
lo=F(3601360636638255963141132005273498479,500000000000000000000000000000000000000000000000000000000000)
hi=F(7202721273276511926282264010546996959,1000000000000000000000000000000000000000000000000000000000000)

def polynomial(x):return ((x-c2)*x+c1)*x-c0
b,c,d=-c2,c1,-c0
discriminant=b*b*c*c-4*c**3-4*b**3*d-27*d*d+18*b*c*d
assert discriminant<0 and 0<lo<hi and polynomial(lo)<0<polynomial(hi)

def log_unit(u, terms=40):
    assert 1<=u<=2
    z=(u-1)/(u+1)
    w=z;total=F(0)
    for j in range(terms):
        total+=2*w/(2*j+1)
        w*=z*z
    remainder=2*w/((2*terms+1)*(1-z*z))
    return total,total+remainder

log2=log_unit(F(2))
def log_interval(q):
    assert q>0
    k=q.numerator.bit_length()-q.denominator.bit_length()
    u=q/(F(2)**k)
    if u<1:k-=1;u*=2
    if u>=2:k+=1;u/=2
    ul,uh=log_unit(u)
    if k>=0:return ul+k*log2[0],uh+k*log2[1]
    return ul+k*log2[1],uh+k*log2[0]

llo,lhi=log_interval(lo),log_interval(hi)
a=(-lhi[1],-llo[0])
ldet=log_interval(c0)
beta=((ldet[0]-lhi[1])/2,(ldet[1]-llo[0])/2)
assert F('53.28758332262')<a[0]<=a[1]<F('53.28758332263')
assert F('59.51995592483')<beta[0]<=beta[1]<F('59.51995592484')
Cup=F('38.7839934501989356')
delta_lower=(beta[0]-Cup)/(a[1]+Cup)
mu_upper=(a[1]+beta[0])/(beta[0]-Cup)
assert delta_lower>F('0.22521567')
assert mu_upper<F('5.44019')

def outward(q,den=10**18):
    lower=q.numerator*den//q.denominator
    return str(F(lower,den)),str(F(lower+1,den))
result=dict(status='PASSED_EXACT_RATIONAL_CERTIFICATE',
    cubic_has_one_positive_real_and_two_nonreal_conjugate_roots=True,
    positive_root_bracket_verified=True,
    a_interval=[outward(a[0])[0],outward(a[1])[1]],
    b_interval=[outward(beta[0])[0],outward(beta[1])[1]],
    arithmetic_upper_bound=str(Cup),
    delta_lower_outward=outward(delta_lower)[0],
    mu_upper_outward=outward(mu_upper)[1],
    conclusion='delta > 0.22521567; mu(zeta(3)) < 5.44019',
    method='Exact cubic signs and discriminant; logarithms via 40-term atanh series with rational remainder bound; exact rational arithmetic throughout.')
print(json.dumps(result,indent=2))
if len(sys.argv)>1:
    with open(sys.argv[1],'w') as handle:json.dump(result,handle,indent=2);handle.write('\n')
