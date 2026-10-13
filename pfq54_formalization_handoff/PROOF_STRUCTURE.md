# Mathematical structure for formalization

This document specifies mathematical objects and lemmas. It contains no Lean
code. All assertions must refer to the same original forward approximants.
The primary source is `manuscript.tex`; exact matrix data are attached.

## A. Conceptual theorem: integer normalization plus a smaller error

Given rational q_n>0,p_3,n,p_4,n, construct a positive rational multiplier m_n
and a positive integer g_n such that

    m_n (q_n,p_3,n,p_4,n) is an integer vector,
    g_n divides its three coordinates.

Then u_n=m_n*q_n/g_n is a positive integer and
v_n(A,B)=m_n*(A*p_3,n+B*p_4,n)/g_n is an integer for every integer pair.
The ratio is unchanged. Assume, for each fixed nonzero pair,

    u_n <= exp(sigma*n+o(n)),
    |alpha-r_n| <= exp(-beta*n+o(n)), beta>sigma,
    alpha != r_n for infinitely many n.

Prove irrationality by the nonzero integer a*u_n-b*v_n if alpha=a/b.
The constants and o(n) in the analytic bound may depend on the fixed pair.
No assertion for varying pairs A(n),B(n) is required. Clear rational
coefficients to deduce independence of 1,zeta(3),zeta(4).

This theorem is independent of hypergeometric identities or matrix fields.

## B. Forward trajectory and finite hypergeometric polynomial

Use exactly the supplied coordinate order:

    pFq(5,4,1)
    x0=(0,0,1,1,1;1,1,1,1)
    vF=(-14,-15,13,14,12;1,2,3,4).

Let F(n) be its native 4-by-4 matrix, W_F(N)=F(0)...F(N-1), W_F(0)=I.
Use the row matrix and column

    I_F = [[0,0,-6A,3A-2B],[12,0,0,0]], projection=(1,0,0,0)^T.

Define the ratio using its two projected entries. Permuting the upper
parameters simultaneously recovers the earlier trajectory order.
The scalar polynomial is the terminating 5F4 with upper parameters
(-14n,-15n,1+13n,1+14n,1+12n) and lower parameters
(1+n,1+2n,1+3n,1+4n), truncated at 14n.

Prove the denominator readout equals 12*F_n(1). For any integer polynomial
P, theta(z^k)=k*z^k implies P(theta)F_n(1)=sum_k P(k)t_n,k.
The DLMF shifted-parameter derivative identity is supporting notation.
The original numerator is r_AB*W_F*e0. Do not replace it by
`e0^T*W_F*r_AB^T`; these are different matrix contractions.

## C. Finite harmonic readouts and integer coefficients

E_n is the four-binomial integer in the paper, and B_n,k=E_n*t_n,k is the
five-binomial integer. Prove the equality by factorial cancellation.
Define U_n,j,V_n,j as the value and first epsilon derivative of the five
binomial factors printed in the paper. For formalization one can instead
use the explicit rational jets below, avoiding Gamma altogether.

Upper jet, for nonnegative N,M:

    N>=M: (choose(N,M), -choose(N,M)*(H_N-H_(N-M)))
    N<M:  (0, (-1)^(M-N)*N!*(M-1-N)!/M!)

Lower jet, with M>=0 and integer m:

    0<=m<=M: (choose(M,m), choose(M,m)*(H_m-H_(M-m)))
    m=-r, r>=1: (0, (-1)^r*M!*(r-1)!/(M+r)!)
    m=M+r, r>=1: (0, (-1)^(r-1)*M!*(r-1)!/(M+r)!)

Multiply jets by (a,a')*(b,b')=(ab,a'b+ab'). Sum over 0<=j<=17n.
The value and derivative both vanish outside n<=j<=17n. Single vanishing
factors must retain their derivatives; otherwise the boundary readouts change.
Define

    S0=sum U,
    S3=sum [U*H_(j+2n)^(3) + V*H_(j+2n)^(2)/2],
    S4=sum [U*H_(j+2n)^(4) + V*H_(j+2n)^(3)/3].

D_n=lcm(1,...,19n) clears the harmonic denominators:
D_n^r H_m^(r) is integral for m<=19n. Prove U integral and D_n*V integral,
then Z_i=6*D_n^4*S_i integral. Prove S0>0.

Required bridge, for all n:

    rQ W_F(n)e0 = 12*S0/E_n,
    rAB W_F(n)e0 = 12*(A*S3+B*S4)/E_n.

The appendix gives the contour/contiguity derivation and its exact gauge.
Finite readout comparisons do not replace this universally quantified bridge.

## D. Uniform divisor and height

1. Prove each permutation of (-2,-1,0,1,2) yields the displayed relative
   factorial multiplier lambda_b for both U and V.
2. Prove integrality of every permuted normalization. At each prime, this
   yields v_p(Z_i)>=max(0,max_b -v_p(lambda_b)). For prime-power sums the
   maximum is taken after summing, not before.
3. For the stronger divisor, restrict to eligible primes p>29,
   p^2>30n, p not dividing n, and use the appendix's eight pairings.
4. Establish the upper harmonic ranges: gains 3,2,1 on respectively
   (18n,19n),(17n,18n),(16n,17n). The permutation profile is zero there.
5. Establish the complete-residue lemma on 8n<p<11n. The root deficit is at
   most one. Hence T=(X^p-X)*Nbar/Dbar is a polynomial of degree p-2 over F_p.
   Compute the local pole coefficients and sum T over all residues to obtain
   v_p(Q)>=1,v_p(P3)>=-1,v_p(P4)>=-2.
6. The latter implies a bound c(n/p)+2>=phi(n/p)+1. This justifies adding
   the extra one on that range. Independent valuation lower bounds cannot
   simply be added. The two extra prime ranges are disjoint.
7. Prove G_n divides all three Z_i. This is simultaneous for all integer A,B.
8. Use the exact finite profile sum S8>20.004, the prime number theorem,
   and the extra contributions 6+3 to obtain liminf log(G_n)/n>=S8+9.
   Excluded primes contribute o(n).
9. Uniform Stirling plus the concavity/rational-log certificate bounds
   limsup log(S0)/n<=65.46. Since log(D_n)/n ->19,

       limsup log(6*D_n^4*S0/G_n)/n <=65.46+76-(S8+9)<112.5.

Bound this integer denominator itself, not merely a common matrix scaling.
The reduced denominator is at most this integer.

The partial-fraction notation in the appendix translates by
E_n=C_n*abs(rho_n), (S0,S3,S4)=(-1)^n*C_n*(Q,P3,P4), and Z=(-1)^n*X.
Here C_n and rho_n are rational scalar normalizations, not spectral roots.

## E. Limit construction: exact objects

The auxiliary analytic matrix G(n) comes from MeijerG(5,2,5,5,1), with

    y0=(0,0,1,1,2;0,0,0,0,0),
    vG=(-16,-17,11,12,10;-2,-1,0,1,2).

Its leading block is Q(n). Establish
G(n)=[[Q(n),b(n)],[0,-1]], so rows whose fourth coordinate is zero remain
there under inverse transpose. The retained eigenvalues are rho1,rho2,rho4.
Do not retain the extraneous -1 mode when stating the error factor.

The paper now prints E(n), L, H(n), and the scalar R(n) explicitly from the
supplied 5F4 script. E(n) is a 4-by-3 basis matrix; it is unrelated to the
coefficient-clearing integer E_n. Prove

    L E(n)=I,
    F(n)E(n+1)=E(n) Fhat(n),
    Fhat(n)H(n+1)Q(n)^T=R(n)H(n),
    det H(n)=2*product_(j=8..12)(jn+1).

The inverse-free identity avoids unnecessary inverses in certificate checks.
Set J=[I3 0] and K(n)=E(n)H(n)J. Prove rank(K)=3, not four, and

    F(n)K(n+1)G(n)^T=R(n)K(n).

Telescoping gives W_F(N)K(N)=(product R)*K(0)*W_G(N)^(-T).
This requires no inverse of K.

## F. Initial values and decay

For the actual Meijer-G state prove by the n=0 Mellin-Barnes residue calculation

    S_G(0)=(1-2*zeta3+3*zeta4, 1-2*zeta3, 1, 1-zeta2).

With the stated I_G, I_G*S_G(0)^T=6*(A*zeta3+B*zeta4,1)^T.
Prove I_F*E(0)*H(0)=2*I_G_hat. The denominator pairing is exactly 6
(or 12 after forward transport), hence nonzero without any independence claim.

For n>=1 derive the positive four-variable integral using the three beta
integrals, the fourth beta integral and Mellin inversion. Check each real
part condition, absolute integrability before Fubini, and domination for
z-differentiation in a neighborhood of z=1. The original contour changes by
substitution s=2n+w; it is not a contour shift across poles.

The factorial upper bound is denoted mathfrak-d_n in the manuscript, distinct
from the harmonic lcm D_n. Prove its successive ratio is at most

    eta = [16^16*15^30*2^2*3^3*4^4/(13^13*12^12*30^30)]*(3/2)^55 <1

for n>=2. This is an exact rational comparison. For k=0,1,2,3, use the explicit
nonnegative rising-factorial expansions now printed in the manuscript to prove

    |theta^k G_n(1)| <= (16n+1)^k*mathfrak-d_n = O(n^k*eta^n).

At n=0 use the separate residue computation. Prove the restricted state obeys
s(n+1)=s(n)Q(n), by the contiguous equations for the actual functions.

## G. The general asymptotic dependency and elementary transfer

This is the precise meaning needed for the two general asymptotic theorems
referenced but not supplied in the pasted section.

Let T_n=diag(1,n,n^2), n>=1, and A_n=T_n Q(n) T_(n+1)^(-1).
The matrices have rational entries in n and tend to an invertible A_infinity
with three distinct eigenvalues. The requested modal-basis theorem must
provide independent row solutions f_i(n) and scalars a_i(n)!=0 such that

    f_i(n) T_n^(-1)/a_i(n) -> y_i,
    |a_i(n)|^(1/n) -> |rho_i|,

where the y_i form a basis of left eigenvectors of A_infinity. Use the root
ordering with the unique small modulus first. A theorem only about a constant
matrix or only about individual eigenvalues does not suffice. The rational
matrix entries supply full asymptotic expansions at infinity; the hypotheses
of the chosen difference-system theorem must be verified explicitly.

Once this modal-basis assertion is available, the rest is proved in the paper's
`Dual mode transfer` lemma, without further asymptotic theorems:

- the decaying actual state is a nonzero multiple of the unique recessive row;
- the balanced transported terminal column tends to w=(1,10,100)^T;
- det[w,A_infinity^(-T)w,(A_infinity^(-T))^2 w]!=0 implies its component along
  the dominant dual mode is nonzero;
- a row-basis factorization of W_Q(N)^(-T) gives an error of exponential rate
  |rho4|/|rho1|; the denominator pairing tends to a nonzero value.

T_0 is singular and must never be inverted. Balancing is only for n>=1;
initial state data at n=0 are transported separately by the exact walk.
The leading conjugate roots have equal modulus; do not assume distinct moduli
for all three roots when invoking a modal-basis result.

## H. Exact spectral comparison, independent of decimal approximations

`certificates/spectral_data.json` supplies Q_infinity, its exact monic cubic
chi(X)=X^3-aX^2+bX-c, and the exact cyclic determinant.
Its discriminant is negative. For u=7203/10^27 and epsilon=102/10^51, verify

    c>0, chi(0)<0<chi(u), u^3<c*epsilon^2.

The unique real root r lies between 0 and u. The conjugate roots have common
modulus sqrt(c/r), so vartheta^2=r^3/c<epsilon^2.
An exact rational log-series lower bound gives -log(epsilon)>112.8.
The displayed root decimals are unnecessary for this argument.

The spectral comparison supplies the numerical margin only after Section G
has supplied the nonautonomous asymptotics and Sections E-F identify the state.

## I. Nonvanishing for all pairs, including a possibly zero target

The arithmetic companion certificate uses a different auxiliary forward
Meijer-G trajectory, called M_G(n) in the manuscript:

    start=(1,1,0,0,0;0,0,0,0,0),
    direction=(16,17,-11,-12,-10;2,1,0,-1,-2).

Do not confuse it with the analytic G(n) in Section E. Its 3-by-3 companion has
c0(n)!=0 and no poles at every integer n>=0. Its exact initial readout matrix
S=R*U(0) is invertible. For THIS Meijer-G matrix the reduction modulo 101 is

    [[1,1,56],[0,56,10],[0,76,19]], determinant 1.

The forward 5F4 initial matrix has a DIFFERENT reduction,
[[1,89,15],[0,35,64],[0,98,61]], determinant 4. Both are invertible; do not
substitute one numerical certificate for the other without its scalar gauge.

The readout bridge gives z_n=(-1)^n*(alpha*Q_n-A*P3_n-B*P4_n) as a solution
of the companion recurrence with initial three scalar values (alpha,-A,-B)S.
Eventual zero propagates backwards because c0 never vanishes. Invertibility
then forces alpha=A=B=0. This is impossible for a nonzero pair (A,B).
No prior assertion alpha!=0 is used.

## J. Final assembly and acceptance condition

Sections C-D provide the integers and exponent sigma=112.5. Sections E-H
provide the zeta limit and beta=112.8, subject to the stated modal-basis theorem.
Section I gives infinitely many nonzero errors. Apply Section A to obtain
irrationality for every fixed nonzero pair, hence rational linear independence,
and liminf delta>=1/375 for the reduced denominators.

The final theorem must refer to the actual forward initial rows in Section B.
If any matrix identity, harmonic-readout bridge, prime lemma, or modal-basis
statement is left as an assumption, label the result conditional on exactly
that assumption. Do not promote a finite-depth computational check to an
all-depth mathematical statement.
