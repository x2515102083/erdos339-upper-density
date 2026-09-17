"""Certify all n,m and common dilations for every generator subset up to N.
Exact Python certificates, NOT formal Lean proofs or a solution of arbitrary A.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from fractions import Fraction
from math import lcm

def primitive(A):
    result=[]
    for a in sorted(set(A)):
        if not any(a%b==0 for b in result):result.append(a)
    return tuple(result)

def families(N,A=(),remaining=None):
    if remaining is None:remaining=tuple(range(2,N+1))
    if A:yield A
    for i,a in enumerate(remaining):
        yield from families(N,A+(a,),tuple(b for b in remaining[i+1:] if b%a))

def coverage(A,upper):
    flags=bytearray(upper+1)
    for a in A:
        for t in range(a,upper+1,a):flags[t]=1
    C=[0]*(upper+1)
    for t in range(1,upper+1):C[t]=C[t-1]+flags[t]
    return C

def coefficients(A):
    c={}
    for a in A:
        new=c.copy();new[a]=new.get(a,0)+1
        for q,v in c.items():
            r=lcm(q,a);new[r]=new.get(r,0)-v
        c={q:v for q,v in new.items() if v}
    return c

def self_test():
    from itertools import combinations
    from math import lcm
    for N in range(2,15):
        expected={tuple(primitive([a for a in range(2,N+1) if mask & (1<<(a-2))])) for mask in range(1,1<<(N-1))}
        actual=list(families(N))
        assert len(actual)==len(set(actual)) and set(actual)==expected
    for A in families(12):
        c={}
        for k in range(1,len(A)+1):
            for S in combinations(A,k):
                q=lcm(*S);c[q]=c.get(q,0)+(1 if k%2 else -1)
        assert coefficients(A)=={q:v for q,v in c.items() if v}
    print("Independent enumeration and coefficient self-tests passed.")

def ceil_fraction(x):return -(-x.numerator//x.denominator)

def certify(A):
    A=primitive(A)
    if not A or A[0]<2:raise ValueError('Nonempty positive generators >=2 required')
    c=coefficients(A)
    delta=sum((Fraction(v,q) for q,v in c.items()),Fraction())
    Wp=sum(v for v in c.values() if v>0)
    Wm=sum(-v for v in c.values() if v<0)
    assert sum(c.values())==1 and delta>0
    # For n>=N0: 2F(n)-(n+1)F(m)/m > delta*(n-1)-2Wp-Wm >=0.
    N0=max(A[-1],ceil_fraction(1+Fraction(2*Wp+Wm)/delta))
    small=coverage(A,N0)
    rhos=[Fraction(2*small[n],n+1) for n in range(A[-1],N0)]
    rho=min(rhos,default=2*delta)
    gap=rho-delta
    if gap<0:raise RuntimeError(('Nonpositive tail gap',A,rho,delta))
    if gap==0:
        if Wm:raise RuntimeError(('Zero gap needs sharper tail',A))
        T=1
    else:T=max(1,ceil_fraction(Fraction(Wm)/gap))
    assert gap*T>=Wm
    C=coverage(A,max(N0,T))
    # An independently computed count for every finite prefix used by the certificate.
    for x in range(len(C)):
        assert C[x]==sum(v*(x//q) for q,v in c.items())
    best_m=None;prefixes=equalities=0;worst=None
    # Suffix maximum of F(m)/m checks ALL finite m without a quadratic pair loop.
    for n in range(T-2,A[-1]-1,-1):
        m=n+1
        if best_m is None or C[m]*best_m>=C[best_m]*m:best_m=m
        if n>=N0:continue
        slack=2*best_m*C[n]-(n+1)*C[best_m]
        if slack<0:raise RuntimeError(('Rounded counterexample',A,n,best_m,C[n],C[best_m]))
        prefixes+=1
        equalities+=slack==0
        if worst is None or slack<worst[0]:worst=(slack,n,best_m)
    return dict(A=list(A),density=str(delta),positive_weight=Wp,negative_weight=Wm,n_tail=N0,
                rho=str(rho),gap=str(gap),m_tail=T,finite_prefix_comparisons=prefixes,
                exact_count_cross_checks=len(C),equalities_at_suffix_max=equalities,worst_finite=worst)

def tests():
    self_test()
    # Direct finite pairs and dilation formula, independent of the tail proof.
    pairs=dilations=0
    for A in families(10):
        cert=certify(A)
        C=coverage(A,120)
        for n in range(max(A),61):
            for m in range(n+1,121):
                assert (n+1)*C[m]<=2*m*C[n]
                pairs+=1
        for d in (1,2,3,7):
            D=coverage([d*a for a in A],d*120)
            for x in range(d*120+1):
                assert D[x]==C[x//d]
                dilations+=1
    return dict(direct_rounded_pairs=pairs,direct_dilation_counts=dilations)

def main():
    p=argparse.ArgumentParser();p.add_argument('--n-max',type=int,default=20);p.add_argument('--output',default='all-scales-n20.json');p.add_argument('--certificates',default='all-scales-n20-certificates.jsonl');p.add_argument('--self-test',action='store_true');a=p.parse_args()
    if not 2<=a.n_max<=24:raise ValueError('Software guard: 2<=N<=24')
    if not __debug__:raise RuntimeError('Do not use -O or PYTHONOPTIMIZE: assertions are required')
    started=time.monotonic();checks=tests() if a.self_test else None
    digest=hashlib.sha256();count=prefixes=identities=equalities=0;maxn=maxm=0;maxncase=maxmcase=None
    with open(a.certificates,'w',encoding='utf-8') as f:
        for A in families(a.n_max):
            r=certify(A);s=json.dumps(r,sort_keys=True,separators=(',',':'))+'\n';f.write(s);digest.update(s.encode())
            count+=1;prefixes+=r['finite_prefix_comparisons'];identities+=r['exact_count_cross_checks'];equalities+=r['equalities_at_suffix_max']
            if r['n_tail']>maxn:maxn=r['n_tail'];maxncase=r['A']
            if r['m_tail']>maxm:maxm=r['m_tail'];maxmcase=r['A']
    result=dict(kind='all_n_m_and_common_scales_for_bounded_normalized_generators',normalized_max=a.n_max,
        nonempty_primitive_sets=count,finite_prefix_comparisons=prefixes,exact_count_cross_checks=identities,
        equalities_at_suffix_max=equalities,maximum_n_tail=maxn,maximum_n_tail_A=maxncase,
        maximum_m_tail=maxm,maximum_m_tail_A=maxmcase,certificate_sha256=digest.hexdigest(),self_tests=checks,
        seconds=round(time.monotonic()-started,3),
        scope='Every nonempty A subset {2,...,N}, every integer d>=1, every m>n>=d*max(A)',
        limitations='Exact Python enumeration plus mathematical tail reduction; not Lean-checked; arbitrary normalized generators remain outside scope; no novelty or prize claim.')
    s=json.dumps(result,indent=2);print(s);open(a.output,'w',encoding='utf-8').write(s+'\n')
if __name__=='__main__':main()
