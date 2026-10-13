"""Direct forward 5F4: exact two-block, row/prime-adaptive finite bounds.

No cancellation across the final four-term contraction is used. Exact
arithmetic inside each whole block is retained. Finite tests, not asymptotics.
"""
import argparse, csv, json, math, sys, time
from itertools import combinations, product
from pathlib import Path
from flint import fmpq, fmpq_mat, arb, ctx

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/pfq54_row_prime'
OUT.mkdir(exist_ok=True)
START = (1,1,0,0,1,1,1,1,1)
DIRECTION = (13,14,-14,-15,12,1,2,3,4)
ORDER = (0,1,4,5,6,7,8,2,3)
SPARSE = {(1,3,0),(2,2,0),(3,3,3),(1,1,0)}
USE_SPARSE = False
I = fmpq_mat([[int(i==j) for j in range(4)] for i in range(4)])
ROWS = fmpq_mat([[0,0,-6,3],[0,0,0,-2],[12,0,0,0]])

def elementary(xs, k):
    return sum(math.prod(ts) for ts in combinations(xs,k))

def theta(w):
    x=w[:5]; y=[v-1 for v in w[5:]]
    a=[-elementary(x,5)] + [elementary(y,5-k)-elementary(x,5-k) for k in range(1,5)]
    if not a[4]: raise ZeroDivisionError(('singular vertex',w))
    return fmpq_mat([[int(i==j+1) if j<3 else fmpq(-a[i],a[4]) for j in range(4)] for i in range(4)])

def move(w,axis,sign):
    z=list(w); z[axis]+=sign; z=tuple(z)
    if axis<5 and sign==1: E=I+theta(w)*fmpq(1,w[axis])
    elif axis<5: E=(I+theta(z)*fmpq(1,z[axis])).inv()
    elif sign==1: E=(I+theta(z)*fmpq(1,w[axis])).inv()
    else: E=I+theta(w)*fmpq(1,z[axis])
    return z,E

def segment(start,stop,order=ORDER):
    w=start; blocks=[]
    for ax in order:
        d=stop[ax]-w[ax]
        for _ in range(abs(d)):
            w,E=move(w,ax,1 if d>0 else -1); blocks.append(E)
    assert w==stop
    if not blocks:return I
    while len(blocks)>1:
        blocks=[blocks[i]*blocks[i+1] if i+1<len(blocks) else blocks[i] for i in range(0,len(blocks),2)]
    return blocks[0]

def qgcd(a,b):
    return fmpq(math.gcd(int(a.numerator),int(b.numerator)), math.lcm(int(a.denominator),int(b.denominator)))
def qlcm(a,b):
    if not a:return abs(b)
    if not b:return abs(a)
    return fmpq(math.lcm(int(a.numerator),int(b.numerator)),math.gcd(int(a.denominator),int(b.denominator)))
def content(xs):
    c=fmpq(0)
    for x in xs:c=qgcd(c,x)
    return c
def logabs(x):return math.log(abs(int(x.numerator)))-math.log(int(x.denominator))
def encode(A):return [[str(A[i,j]) for j in range(A.ncols())] for i in range(A.nrows())]
def decode(a):return fmpq_mat([[fmpq(v) for v in row] for row in a])

def grid(n):
    for pos,low,neg in product(range(1,5),range(5),range(4)):
        if USE_SPARSE and (pos,low,neg) not in SPARSE:continue
        ds=tuple(n*d*(pos if i in (0,1,4) else low if i>=5 else neg)//4 for i,d in enumerate(DIRECTION))
        cut=tuple(s+d for s,d in zip(START,ds))
        if min(cut[i] for i in (0,1,4))<=max(cut[5:])-1:continue
        if sum(cut[:5])-sum(cut[5:])+4<3:continue
        # Keep an extensive, nonempty suffix: no endpoint-only certificate.
        if sum(abs(n*d-v) for d,v in zip(DIRECTION,ds))<4*n:continue
        yield f'positive{pos}_lower{low}_negative{neg}',cut

def validate_library():
    import pickle
    from sympy.abc import n
    cache=ROOT/'results/candidates/MG5255_FORWARD_PFQ54_EQUIVALENT/PFQ54.pickle'
    H=pickle.loads(cache.read_bytes())
    for k in (0,1,2):
        start=tuple(s+k*d for s,d in zip(START,DIRECTION))
        stop=tuple(s+(k+1)*d for s,d in zip(START,DIRECTION))
        expected=H.subs({n:k})
        expected=fmpq_mat([[fmpq(str(v)) for v in row] for row in expected.tolist()])
        assert segment(start,stop)==expected
    (OUT/'library_check.json').write_text(json.dumps(dict(status='KNOWN_EXAMPLE',all_16_entries_equal=True,step_indices=[0,1,2],reference=str(cache)))+'\n')

def run(n):
    began=time.perf_counter();stop=tuple(s+n*d for s,d in zip(START,DIRECTION))
    W=segment(START,stop);Y=ROWS*W
    cp=OUT/f'paths_n{n}.jsonl'
    done={d['name']:d for d in map(json.loads,cp.read_text().splitlines())} if cp.exists() else {}
    env=[fmpq(0)]*3;same=fmpq(0);best=fmpq(0);bestname=None;count=0;failed=0
    for name,cut in grid(n):
        if name in done:z=done[name]
        else:
            try:A=segment(START,cut); B=segment(cut,stop)
            except (ZeroDivisionError,ValueError) as exc:z=dict(name=name,status='COMPUTATION_FAILED',error=str(exc))
            else:
                assert A*B==W,name
                Z=ROWS*A; b=[B[i,0] for i in range(4)]
                cs=[content(Z[r,i]*b[i] for i in range(4)) for r in range(3)]
                assert all((Y[r,0]/cs[r]).denominator==1 for r in range(3))
                z=dict(name=name,status='NUMERICAL_CANDIDATE',cut=cut,prefix_rows=encode(Z),
                       suffix_column=list(map(str,b)),row_contents=list(map(str,cs)),all_16_endpoint_entries_equal=True)
            with cp.open('a') as f:f.write(json.dumps(z)+'\n')
        if z['status']=='COMPUTATION_FAILED':failed+=1;continue
        count+=1;cs=list(map(fmpq,z['row_contents']))
        env=[qlcm(a,b) for a,b in zip(env,cs)]
        common=content(cs);same=qlcm(same,common)
        if common>best:best=common;bestname=name
    G=content(env);actual=content(Y[r,0] for r in range(3))
    assert (actual/G).denominator==1
    bound=logabs(Y[2,0]/G)
    q_bound=abs(Y[2,0]/G)
    assert q_bound.denominator==1
    targets=[]
    for aa,bb in ((1,0),(0,1),(1,1),(15,1)):
        r=(aa*Y[0,0]+bb*Y[1,0])/Y[2,0];p=int(r.numerator);q=int(r.denominator)
        assert q>1
        vals=[]
        for precision in (2*len(str(q))+100,2*len(str(q))+300):
            ctx.dps=precision
            error=abs(aa*arb(3).zeta()+bb*arb(4).zeta()-arb(p)/q)
            assert not error.contains(0)
            delta=-1-error.log()/arb(q).log()
            score=-1-error.log()/arb(int(q_bound)).log()
            vals.append(dict(precision=precision,error=error.str(25),delta=delta.str(25),delta_float=float(delta.mid()),
                             bound_score=float(score.mid()),digits_correct=float((-error.log()/arb(10).log()).mid()),E=float((-error.log()).mid())))
        assert abs(vals[0]['delta_float']-vals[1]['delta_float'])<1e-12
        targets.append(dict(A=aa,B=bb,p=str(p),q=str(q),log_q=math.log(q),q_digits=len(str(q)),checks=vals))
    summary=dict(status='NUMERICAL_CANDIDATE',n=n,N=n+1,path_count=count,failed_paths=failed,
                 row_envelopes=list(map(str,env)),common_content=str(G),actual_common_content=str(actual),
                 best_fixed_name=bestname,best_fixed_log_q=logabs(Y[2,0]/best),
                 same_path_prime_log_q=logabs(Y[2,0]/same),row_prime_log_q_bound=bound,
                 integer_denominator_bound=str(q_bound),
                 actual_universal_log_q=logabs(Y[2,0]/actual),row_choice_gain=str(G/same),
                 matrix_entry_height_bits=max(max(abs(int(W[i,j].numerator)).bit_length(),int(W[i,j].denominator).bit_length()) for i in range(4) for j in range(4)),
                 targets=targets,runtime_seconds=time.perf_counter()-began)
    (OUT/f'depth_n{n}.json').write_text(json.dumps(summary,indent=2)+'\n')
    report={k:summary[k] for k in ('n','path_count','failed_paths','best_fixed_log_q','same_path_prime_log_q','row_prime_log_q_bound','actual_universal_log_q','runtime_seconds')}
    report['mixed_delta']=targets[-1]['checks'][-1]['delta_float'];report['mixed_bound_score']=targets[-1]['checks'][-1]['bound_score']
    msg=json.dumps(report);print(msg,flush=True)
    with (OUT/'run.log').open('a') as f:f.write(msg+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('depths',nargs='*',type=int,default=[20,40,80,160,320]);ap.add_argument('--check-library',action='store_true');ap.add_argument('--sparse',action='store_true')
    args=ap.parse_args()
    if args.sparse:
        USE_SPARSE=True;OUT=OUT/'four_cuts';OUT.mkdir(exist_ok=True)
    if args.check_library:validate_library()
    for n in args.depths:run(n)
