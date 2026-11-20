# Threshold from Laurent (2008) Cor. 2 with (C,m)=(25.2,10), D=1:
# log Lambda >= -C * max(log b' + 0.38, m)^2 * H1 * H2, H1=1 (alpha1=2), H2=ln Y.
# Upper: log Lambda <= ln(n-1) + N ln6/(n-1) - N ln2.
# ln Y <= (N ln2 + 1)/ell ; b' <= ell*(1+1/ln2).
# Contradiction iff ell > C*M(ell)^2*(N ln2+1)/(N ln2 - N ln6/(n-1) - ln(n-1)).
from mpmath import mp, mpf, log, factorial
mp.dps=50
def T(n,ell,C=mpf('25.2'),m=10,c38=mpf('0.38')):
    N=factorial(n-1)
    bprime=ell*(1+1/log(2))
    M=max(log(bprime)+c38, m)
    den=N*log(2)-N*log(6)/(n-1)-log(n-1)
    return C*M**2*(N*log(2)+1)/den
for n in list(range(7,16))+[20,50,100]:
    print(n, float(T(n,4464)), float(T(n,10**5)))
# find minimal ell0 working for n=7 (worst case), check all ell>=ell0 up to large bound
def ok(n,ell,**kw): return ell > T(n,ell,**kw)
ell0=None
for ell in range(4000,5000):
    if ok(7,ell) and all(ok(7,e) for e in [ell, ell*2, ell*10, 10**6, 10**9, 10**15]):
        ell0=ell;break
print('ell0 for n=7 (C=25.2,m=10):',ell0)
# alternative constant pairs for robustness
for (C,m) in [(mpf('20.3'),18),(mpf('17.9'),30)]:
    for ell in range(1000,40000,1):
        if ell>T(7,ell,C=C,m=m): print('pair',C,m,'ell0(n=7)=',ell, ' n=12:', [e for e in range(1000,40000) if e>T(12,e,C=C,m=m)][0]); break
