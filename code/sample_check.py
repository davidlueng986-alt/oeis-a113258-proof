# Independent spot checks in Python:
# (1) for n<=11, compare a(n) mod q computed from the EXACT big integer a(n) with the modular formula;
# (2) random (ell,q,n) triples from certificate files: recompute with Python pow and math.factorial.
import random, sys, math, gmpy2
from math import factorial
exact={}
def a_exact(n):
    if n not in exact: exact[n]=sum(gmpy2.mpz(factorial(i))**factorial(n-i+1) for i in range(1,n+1))
    return exact[n]
def a_mod(n,q):
    s=0
    for i in range(1,n+1):
        s=(s+pow(factorial(i)%q, factorial(n-i+1)%(q-1), q))%q
    return s
lines=[l.split() for l in open(sys.argv[1])]
random.seed(int(sys.argv[2]) if len(sys.argv)>2 else 1)
ok=0
# (1) exact comparison for small n
for l in lines[:200]:
    ell,q=int(l[0]),int(l[1])
    for n in map(int,l[2:]):
        if n<=11:
            A=int(a_exact(n)%q)
            assert A==a_mod(n,q), (ell,q,n)
            assert A!=0 and pow(A,(q-1)//ell,q)!=1
            ok+=1
print('exact small-n checks:',ok)
# (2) random sample
cnt=0
for _ in range(int(sys.argv[3]) if len(sys.argv)>3 else 300):
    l=random.choice(lines); ell,q=int(l[0]),int(l[1]); ns=list(map(int,l[2:]))
    if not ns: continue
    n=random.choice(ns)
    A=a_mod(n,q)
    assert gmpy2.is_prime(q) and (q-1)%ell==0
    assert A!=0 and pow(A,(q-1)//ell,q)!=1, (ell,q,n)
    cnt+=1
print('random sample checks passed:',cnt)
