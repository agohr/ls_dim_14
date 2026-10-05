"""Exact rational orbital polynomials via Murnaghan--Nakayama and Frobenius.

Helper module for check_printed_identities.py; no external data or packages.
Adapted from the independent uniform Sp(14) verifier.
"""
from fractions import Fraction as F
from functools import lru_cache
from collections import Counter
from math import factorial,comb,prod
from pathlib import Path
import json

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
    K=(n-2)//2;m=(n+2)//2
    den=[F(1,4**j*factorial(2*j+1)) for j in range(n+1)]
    f=[F(1)]
    for j in range(1,n+1):f.append(-sum(den[t]*f[j-t] for t in range(1,j+1)))
    log=[F(0)]
    for j in range(1,n+1):log.append(f[j]-sum(F(t,j)*log[t]*f[j-t] for t in range(1,j)))
    T=[sum(F((-1)**a*comb(n+2,a)*(n+2-2*a)**(2*j),factorial(2*j))
           for a in range(n+3)) for j in range(n+1)]
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
