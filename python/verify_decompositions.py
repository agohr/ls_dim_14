"""Complete exact check of the dimension-fourteen paper's finite calculation.

Standard library only. Every RR density is reconstructed from its own
finite-difference character; the odd identities are then checked separately.
Orbital coefficients use Murnaghan--Nakayama/Frobenius. Search code and
numerical tolerances play no role. Pass an optional certificate JSON path.
"""
from fractions import Fraction as F
from functools import lru_cache
from collections import Counter
from math import factorial,comb,prod
from pathlib import Path
import json,sys,hashlib

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run Python with -O.')

def partitions(n,bound=None):
    if not n:
        yield ();return
    for a in range(min(n,n if bound is None else bound),0,-1):
        for p in partitions(n-a,a):yield (a,)+p

def series_mul(a,b,N):
    return [sum(a[i]*b[j-i] for i in range(max(0,j-len(b)+1),min(j+1,len(a)))) for j in range(N+1)]

def series_power(a,m,N):
    out=[F(1)]+[F(0)]*N
    for _ in range(m):out=series_mul(out,a,N)
    return out

def exponent(part,K):
    e=[K-sum(part)]+[0]*K
    for a in part:e[a]+=1
    return tuple(e)

def rr_density(n):
    K=(n-1)//2;m=n-K
    den=[F(1,4**j*factorial(2*j+1)) for j in range(n+1)]
    f=[F(1)]
    for j in range(1,n+1):f.append(-sum(den[t]*f[j-t] for t in range(1,j+1)))
    log=[F(0)]
    for j in range(1,n+1):log.append(f[j]-sum(F(t,j)*log[t]*f[j-t] for t in range(1,j)))
    if n%2==0:
        T=[sum(F((-1)**a*comb(n+2,a)*(n+2-2*a)**(2*j),factorial(2*j))
               for a in range(n+3)) for j in range(n+1)]
    else:
        T=[sum(F((-1)**a*comb(n+1,a)*((n+2-2*a)**(2*j)+(n-2*a)**(2*j)),factorial(2*j))
               for a in range(n+2)) for j in range(n+1)]
    assert all(T[j]==0 for j in range(m)) and T[m]==2**(n+2)
    correction=[F(1,factorial(2*j+1)) for j in range(n+1)]
    scalar=series_mul(series_power(f,2*n+2,n),series_mul(T,correction,n),n)
    A={j:[2*(-1)**j*log[j+s]*comb(2*(j+s),2*j) for s in range(n-j+1)] for j in range(1,n+1)}
    out={}
    for k in range(K+1):
        d=n-k
        for mu in partitions(k):
            p=[F(1)]+[F(0)]*d
            for j,count in Counter(mu).items():
                p=series_mul(p,series_power(A[j][:d+1],count,d),d)
                p=[v/factorial(count) for v in p]
            value=sum(p[t]*scalar[d-t] for t in range(d+1))
            if value:out[exponent(mu,K)]=value
    return out

def cells(part):return {(i,j) for i,a in enumerate(part) for j in range(a)}

@lru_cache(None)
def character(lam,mu):
    if not mu:return int(not lam)
    size=mu[0];big=cells(lam);answer=0
    for smallpart in partitions(sum(lam)-size):
        small=cells(smallpart)
        if not small<=big:continue
        strip=big-small
        if any({(i+1,j),(i,j+1),(i+1,j+1)}<=strip for i,j in strip):continue
        seen={next(iter(strip))}
        while True:
            nxt=seen|{b for a in seen for b in strip if abs(a[0]-b[0])+abs(a[1]-b[1])==1}
            if nxt==seen:break
            seen=nxt
        if seen==strip:answer+=(-1)**(len({i for i,j in strip})-1)*character(smallpart,mu[1:])
    return answer

def z(mu):return prod(a**m*factorial(m) for a,m in Counter(mu).items())

def orbital(R,k,profile,K):
    assert len(profile)<=R and all(isinstance(v,int) and v>0 for v in profile)
    parts=list(partitions(k));power={j:sum(F(x)**j for x in profile) for j in range(1,k+1)}
    result={p:F(0) for p in parts}
    for lam in parts:
        schur=sum(F(character(lam,mu),z(mu))*prod(power[j] for j in mu) for mu in parts)
        coefficient=4**k*prod(F(factorial(2*(R-i-1)+1),factorial(2*(R-i-1+a)+1)) for i,a in enumerate(lam))
        for mu in parts:result[mu]+=coefficient*schur*F(character(lam,mu),z(mu))
    return {exponent(p,K):v for p,v in result.items() if v}

def solve(A,b):
    N=len(b);assert len(A)==N and all(len(row)==N for row in A)
    a=[[F(x) for x in row]+[F(y)] for row,y in zip(A,b)]
    determinant=F(1)
    for j in range(N):
        pivot=next((i for i in range(j,N) if a[i][j]),None)
        assert pivot is not None,'singular prescribed moment matrix'
        if pivot!=j:a[j],a[pivot]=a[pivot],a[j];determinant=-determinant
        v=a[j][j];determinant*=v;a[j]=[x/v for x in a[j]]
        for i in range(N):
            if i==j:continue
            c=a[i][j]
            if c:a[i]=[x-c*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a],determinant


def add(p,q,c=F(1)):
    out=p.copy()
    for e,v in q.items():out[e]=out.get(e,F(0))+c*v
    return {e:v for e,v in out.items() if v}


def square(p):
    out={}
    for e,a in p.items():
        for f,b in p.items():
            g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,F(0))+a*b
    return out


def main(source=None):
    source=Path(source) if source else Path(__file__).resolve().parent/'data/decompositions_certificate.json'
    data=json.loads(source.read_text());R=data['rank'];assert R==14
    profiles=data['profiles'];assert len(profiles)==12
    assert all(1<=len(p)<=14 and set(p)<={1,4,16} for p in profiles)
    spec=data['eta'];a=profiles[spec['profile_index']]
    assert a==[1,4] and F(spec['outside'])==192 and F(spec['ratio'])==1
    # The numerical proposal is discarded: rebuild the square from its definition.
    eta=add(orbital(R,1,a,3),orbital(R,3,a,3),F(spec['ratio']))
    eta={e:F(spec['outside'])*v for e,v in eta.items()}
    eta2={e+(0,0,0):v for e,v in square(eta).items()}
    # A normalization check independent of any stored coefficient.
    for k in range(1,7):
        P=list(partitions(k))
        for lam in P:
            for nu in P:assert sum(F(character(lam,mu)*character(nu,mu),z(mu)) for mu in P)==int(lam==nu)
    densities={n:rr_density(n) for n in range(2,15)}
    for n in range(3,14,2):
        lower={(e[0]+1,)+e[1:]+(0,):v for e,v in densities[n-1].items()}
        assert densities[n]=={e:v/2 for e,v in add(densities[n+1],lower).items()}
    expected={(n,k) for n in range(4,15,2) for k in range(1,(n-2)//2+1)}
    rows={(row['n'],row['k']):row for row in data['rows']}
    assert len(rows)==len(data['rows'])==21 and set(rows)==expected
    assert len(data['groups'])==7
    grouped=[(n,g['k'],g['support']) for g in data['groups'] for n in g['dimensions']]
    assert len(grouped)==21 and {(n,k) for n,k,s in grouped}==expected
    assert all(rows[n,k]['support']==support for n,k,support in grouped)
    report=[]
    for n in range(2,15,2):
        K=(n-2)//2;target=densities[n]
        residual=add(target,eta2,F(-1)) if n==14 else target
        scalar=(K,)+(0,)*K;assert residual[scalar]==2*n*(n+2)
        actual={scalar:residual[scalar]}
        if n==14:actual=add(actual,eta2)
        for k in range(1,K+1):
            row=rows[n,k];support=row['support'];keys=[exponent(mu,K) for mu in partitions(k)]
            assert len(support)==len(keys) and len(set(support))==len(support)
            leading=(K-k,k)+(0,)*(K-1);b=residual[leading];assert b>0
            columns=[orbital(R,k,profiles[j],K) for j in support]
            scales=[p[leading] for p in columns];assert min(scales)>0
            matrix=[[p.get(e,F(0))/s for p,s in zip(columns,scales)] for e in keys]
            weights,det=solve(matrix,[residual.get(e,F(0))/b for e in keys])
            bound=F(row['strict_lower_bound']);assert bound==F(1,131072)
            assert bound<min(weights) and sum(weights)==1 and det
            for p,s,w in zip(columns,scales,weights):actual=add(actual,p,b*w/s)
            report.append({'n':n,'k':k,'minimum_normalized_weight':str(min(weights))})
        assert actual==target
    result={'status':'PASS','source':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'profiles':len(profiles),'support_groups':len(data['groups']),'systems':len(report),
            'checks':'All RR densities2..14, all six adjacent identities, symmetric-group orthogonality1..6, exact positive moment systems, full polynomial reconstruction',
            'minimum_normalized_weight':str(min(F(row['minimum_normalized_weight']) for row in report))}
    print(json.dumps(result,indent=2))


if __name__=='__main__':main(sys.argv[1] if len(sys.argv)>1 else None)
