"""Independent certificate consumer for all-scales checks.
Uses raw subsets, subsetwise inclusion-exclusion, and prefix minima.
No code from the certificate producer is imported.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from math import lcm
from bisect import bisect_right
import hashlib,json,sys,time

def verify(path,N):
    if not __debug__:raise RuntimeError('Do not use -O or PYTHONOPTIMIZE: assertions are required')
    start=time.monotonic()
    raw=open(path,'rb').read();records=[json.loads(s) for s in raw.splitlines()]
    expected=set()
    for bits in range(1,1<<(N-1)):
        A=tuple(a for a in range(2,N+1) if bits & (1<<(a-2)))
        if all(b%a for a,b in combinations(A,2)):expected.add(A)
    actual=[tuple(r['A']) for r in records]
    assert len(actual)==len(set(actual)) and set(actual)==expected
    comparisons=identities=0
    for r in records:
        A=r['A'];c={}
        for k in range(1,len(A)+1):
            for S in combinations(A,k):
                q=lcm(*S);c[q]=c.get(q,0)+(1 if k%2 else -1)
        c={q:v for q,v in c.items() if v}
        delta=sum((Fraction(v,q) for q,v in c.items()),Fraction())
        wp=sum(v for v in c.values() if v>0);wm=-sum(v for v in c.values() if v<0)
        assert delta==Fraction(r['density'])>0 and wp==r['positive_weight'] and wm==r['negative_weight']
        N0,T=r['n_tail'],r['m_tail']
        assert N0>=max(A) and delta*(N0-1)>=2*wp+wm
        bound=max(N0,T)
        hits=sorted({a*k for a in A for k in range(1,bound//a+1)})
        F=[bisect_right(hits,x) for x in range(bound+1)]
        for x in range(bound+1):
            assert F[x]==sum(v*(x//q) for q,v in c.items());identities+=1
        rho=min((Fraction(2*F[n],n+1) for n in range(max(A),N0)),default=2*delta)
        assert rho==Fraction(r['rho']) and rho-delta==Fraction(r['gap'])>=0
        assert T>=1 and T*(rho-delta)>=wm
        # Sweep future m upward; retain the MINIMUM earlier 2F(n)/(n+1).
        best=None
        for m in range(max(A)+1,T):
            n=m-1
            if n<N0 and (best is None or F[n]*(best+1)<=F[best]*(n+1)):best=n
            if best is not None:
                assert (best+1)*F[m]<=2*m*F[best];comparisons+=1
    out=dict(verified=True,normalized_max=N,nonempty_primitive_sets=len(records),
        all_subsets_screened=(1<<(N-1))-1,finite_prefix_minimum_checks=comparisons,
        independent_exact_count_checks=identities,certificate_sha256=hashlib.sha256(raw).hexdigest(),
        seconds=round(time.monotonic()-start,3),
        limitations='A separately implemented exact Python check, not independent human review or Lean verification.')
    print(json.dumps(out,indent=2));return out
if __name__=='__main__':verify(sys.argv[1],int(sys.argv[2]))
