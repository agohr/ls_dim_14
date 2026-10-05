"""Exact checks of transcribed manuscript identities and the bundled Lean witnesses.

Standard library only. Polynomial keys are partitions, representing products
of power sums p_j. This checks printed rational algebra, not its geometric
interpretation. The local helper modules reconstruct the density and orbital polynomials
independently. See README.md for the manuscript snapshot and scope.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from math import factorial, prod
from collections import Counter
from pathlib import Path
import re, json, hashlib, argparse
import adjacent_density as rr
import orbital_polynomials as orb

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / 'lean'
checks = []
def clean(a): return {p: Q(c) for p,c in a.items() if c}
def add(*args):
    out = {}
    for a in args:
        for p,c in a.items(): out[p] = out.get(p,Q(0)) + c
    return clean(out)
def scale(a,c): return clean({p:v*c for p,v in a.items()})
def mul(a,b):
    out = {}
    for p,c in a.items():
        for q,d in b.items():
            k=tuple(sorted(p+q,reverse=True)); out[k]=out.get(k,Q(0))+c*d
    return clean(out)
def equal(name,a,b):
    assert clean(a)==clean(b), (name,add(a,scale(b,-1)))
    checks.append({'check':name,'result':'PASS'})
def schur(lam):
    return clean({mu:Q(orb.character(lam,mu),orb.z(mu)) for mu in rr.partitions(sum(lam))})
def schur_ones(lam,r):
    return prod(Q(r+j-i,lam[i]-j+sum(row>j for row in lam[i+1:]))
                for i,row in enumerate(lam) for j in range(row))
def moment(n,k,l):
    r=2*n+2
    return add(*(scale({mu:c*2**len(mu) for mu,c in schur(lam).items()},
               Q(orb.character(lam,(1,)*k))*schur_ones(lam,l)/schur_ones(lam,r))
               for lam in rr.partitions(k)))
def orbital(n,k,a):
    v=orb.orbital(n,k,a,k)
    return {tuple(j for j in range(k,0,-1) for _ in range(e[j])):c for e,c in v.items()}
def gaussian(k):
    a={j:2*(-1)**j*rr.log_f(k)[j] for j in range(1,k+1)}
    return {mu:prod(a[j]**count/factorial(count) for j,count in Counter(mu).items())
            for mu in rr.partitions(k)}
def M(n,terms): return add(*(scale(moment(n,k,l),Q(c)) for k,l,c in terms))

def main():
    global LEAN
    if not __debug__:
        raise RuntimeError("Verification requires assertions; do not run Python with -O.")
    checks.clear()
    parser=argparse.ArgumentParser()
    parser.add_argument('--lean-root',type=Path,default=LEAN)
    parser.add_argument('--output-dir', type=Path, help='Optionally write JSON reports here.')
    args=parser.parse_args()
    LEAN=args.lean_root.resolve()
    for k in range(1,7):
        parts=list(rr.partitions(k))
        for a in parts:
            for b in parts:
                assert sum(Q(orb.character(a,c)*orb.character(b,c),orb.z(c))
                           for c in parts)==int(a==b)
    checks.append({'check':'character orthogonality S1 through S6','result':'PASS'})
    data={
      5:(45,3240,[(1,12,268),(2,12,3),(2,1,312)]),
      6:(45,4320,[(1,14,416),(2,14,6),(2,1,840)]),
      7:(1890,241920,[(1,16,28080),(2,16,668),(2,1,100096),(3,16,3),(3,1,6528),(3,2,4080)]),
      8:(4725,756000,[(1,18,96720),(2,18,2710),(2,1,485640),(3,18,15),(3,1,43320),(3,2,29070)]),
      9:(1,200,[(1,1,'180512/315'),(2,1,'8752/45'),(2,20,'14704/14175'),(3,1,'2992/405'),(3,2,'2090/81'),(3,20,'239/28350')]),
      10:(1,240,[(1,1,'182336/225'),(2,1,'1495736/4725'),(2,22,'21278/14175'),(3,1,'4048/4725'),(3,2,'23276/405'),(3,22,'194/14175')]),
      11:(1,288,[(1,24,'2482652/51975'),(2,1,'3094720/6237'),(2,24,'214814/93555'),(3,2,'164360/2673'),(3,3,'10048/891'),(3,4,'922051/93555')]),
      12:(1,336,[(1,26,'3050776/51975'),(2,1,'12506936/17325'),(2,26,'1445966/467775'),(3,1,'472784/155925'),(3,2,'152711/18711'),(3,3,'1771432/18711')])}
    quartic={
      11:[('1008851484437/2142693',[1,1]),('151204920425/714231',[2,1,1]),('10770035384/714231',[5,1,1,1,1]),('51654964/6428079',[10]+[1]*8),('252882056/1530495',[10]+[1]*10)],
      12:[('2298362246/9933',[1,1]),('194400388184/148995',[1,1,1]),('7327263802/9933',[2,1,1]),('178334456/148995',[10]+[1]*8),('4485216/3311',[10]+[1]*9)]}
    for n,(d,c,terms) in data.items():
        rhs=add({():Q(c)},M(n,terms))
        if n in (9,10): rhs=add(rhs,scale(gaussian(4),2**(n+2)))
        if n in (11,12):
            q4=add(*(scale(orbital(n,4,a),Q(w)) for w,a in quartic[n]))
            equal(f'printed quartic orbital replacement n={n}',q4,
                  {p:v for p,v in rr.reduced_density(n).items() if sum(p)==4})
            rhs=add(rhs,q4,scale(gaussian(5),2**(n+2)))
        equal(f'printed full density n={n}',rhs,scale(rr.reduced_density(n),d))
    for n in range(2,15):
        for l in range(1,2*n+3):
            A=Q(l*n*(6*l*n+7*l+4*n*n+6*n-2),2*(2*n+3))
            B=Q(l*(2*n-1)*(4*l*n+5*l-2*n-4),2*(n+1)*(2*n+3))
            equal(f'printed quadratic projection conversion n={n}, l={l}',
                  moment(n,2,l),add(scale(orbital(n,2,[1]),A),scale(orbital(n,2,[1]*n),B)))
        equal(f'printed F2 orbital conversion n={n}',gaussian(2),
              add(scale(orbital(n,2,[1]),Q(n*(n+1)*(2*n+1)*(2*n+11),2880)),
                  scale(orbital(n,2,[1]*n),Q((2*n-1)*(2*n+1),720))))
    for n in range(5,15):
        D1=Q(n*(2*n+1)*(4*n**4-36*n**3+463*n*n+161*n+108),161280)
        D2=Q(n*(n-1)*(2*n-1)*(2*n+1)*(-8*n*n+160*n-57),967680)
        D4=Q(n*(n-1)*(n-2)*(2*n-3)*(2*n-1)*(2*n+1),645120)
        assert min(D1,D2,D4)>0
        equal(f'printed positive F3 conversion n={n}',gaussian(3),
              add(scale(orbital(n,3,[1]),D1),scale(orbital(n,3,[1,1]),D2),scale(orbital(n,3,[1]*4),D4)))
    basis=[(1,1,1,1),(2,1,1),(2,2),(3,1),(4,)]
    zonal=[list(map(Q,row.split())) for row in [
      '2/15 2/5 1/10 4/15 1/10', '8/15 4/15 -4/15 -4/15 -4/15',
      '2/15 -2/15 7/30 -4/15 1/30', '4/21 -10/21 -2/21 4/21 4/21',
      '1/105 -2/35 1/35 8/105 -2/35']]
    for n,vals,t,b,den,neg in [
      (11,[2695,-4585,25339,-1295,4361],9,4,55,Q(-67336,93555)),
      (12,[15138,-26651,150977,-6873,23971],7,3,8,Q(-245414,17325))]:
        symbolic=add(*(scale(dict(zip(basis,row)),
           sum(x*y for x,y in zip(vals,row))/sum(c*n**len(p) for p,c in zip(basis,row)))
           for row in zonal))
        equal(f'PSD separator in quaternionic-trace normalization n={n}',symbolic,
              {(2,2):Q(t*t,den),(2,1,1):Q(-2*t*b,den),(1,1,1,1):Q(b*b,den)})
        equal(f'printed PSD negative target n={n}',
              {():sum(v*rr.reduced_density(n).get(p,0) for p,v in zip(basis,vals))},{():neg})
        normalized_value=Q((t*n-b*n*n)**2,den)
        assert normalized_value==vals[0] and 16*normalized_value!=normalized_value
        checks.append({'check':f'PSD trace normalization diagnostic n={n}',
          'result':'FACTOR_16_IF_COMPLEX_TRACE', 'printed_identity_at_I':str(normalized_value),
          'complex_trace_moment_at_I':str(16*normalized_value)})
    duals={13:([32231,-53169,301931,-19969,81681],3,221130),
           14:([33248,-94256,878742,-28008,227741],4,246645)}
    negative={}
    for n,(vals,t,den) in duals.items():
        lamcoef=[]
        for lam in rr.partitions(4):
            rho=prod(Q(factorial(2*(n-i-1)+1),factorial(2*(n-i-1+a)+1)) for i,a in enumerate(lam))
            sp=schur(lam)
            lamcoef.append(scale(sp,256*rho*sum(v*sp.get(p,0) for p,v in zip(basis,vals))))
        equal(f'printed orbital separator polynomial n={n}',add(*lamcoef),
              {(2,2):Q(t*t,den),(2,1,1):Q(-2*t,den),(1,1,1,1):Q(1,den)})
        negative[n]=sum(v*rr.reduced_density(n).get(p,0) for p,v in zip(basis,vals))
        assert negative[n]<0
    rows=[]
    for n,name in [(13,'Thirteen'),(14,'Fourteen')]:
        path=LEAN/f'QuaternionicSymmetry/H2Witness{name}.lean'
        source=path.read_text(); terms=[]; total={():Q(392 if n==13 else 448)}
        for k in range(1,7):
            block=re.search(rf'def w{k} : P :=(.*?)(?=\n(?:def|private theorem))',source,re.S).group(1)
            for num,den,rank,degree,profile in re.findall(r'C \((\d+) / (\d+) : ℚ\) \* orbital (\d+) (\d+) \[([\d, ]+)\]',block):
                c=Q(int(num),int(den)); a=list(map(int,profile.split(',')))
                assert int(rank)==n and int(degree)==k and c>0
                total=add(total,scale(orbital(n,k,a),c))
                terms.append({'degree':k,'coefficient':str(c),'profile':a})
        f={(1,):Q(999999993,10**9) if n==13 else Q(1),
           (3,):Q(29552 if n==13 else 88656,10**9),
           (2,1):Q(83790 if n==13 else 251370,10**9),
           (1,1,1):Q(74653 if n==13 else 223959,10**9)}
        total=add(total,scale(mul(f,f),18 if n==13 else 20))
        equal(f'production one-square certificate n={n}',total,rr.reduced_density(n))
        rows.append({'n':n,'scalar':392 if n==13 else 448,'square_coefficient':18 if n==13 else 20,
          'homogenize_factor_to_weight':3,'factor':{','.join(map(str,p)):str(c) for p,c in f.items()},
          'orbital_terms':terms,'source':path.relative_to(LEAN).as_posix(),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    output={'status':'PASS_WITH_NORMALIZATION_NOTE','arithmetic':'fractions.Fraction; no numerical tolerance',
      'manuscript_snapshot':json.loads((HERE/'data/provenance.json').read_text())['manuscript_snapshot'],
      'checks':checks,'orbital_separator_target_values':{n:str(v) for n,v in negative.items()},
      'limitations':['Not a fresh Lean kernel build.','No reconstruction of the omitted seven-square n=14 certificate.',
       'The analytic Haar interpretation of the zonal polynomials and the analytic geometry are not checked by this script.']}
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        (args.output_dir/'exact_checks.json').write_text(json.dumps(output,indent=2)+'\n')
        (args.output_dir/'verified_one_square_certificates.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(f'Completed {len(checks)} exact checks/diagnostics. Polynomial identities pass; two PSD diagnostics require the stated trace normalization.')
    print('Separator target values:',negative)
    print('Production certificate orbital counts:',[(r['n'],len(r['orbital_terms'])) for r in rows])

if __name__=='__main__': main()
