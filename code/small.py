import gmpy2, math, time
from math import factorial
def a(n):
    return sum(gmpy2.mpz(factorial(i))**factorial(n-i+1) for i in range(1,n+1))
for n in range(1,12):
    t=time.time()
    v=a(n)
    N=factorial(n-1)
    R=v-gmpy2.mpz(2)**N
    ip=gmpy2.is_power(v)
    info=f"bits={v.bit_length()}"
    if n<=6: info+=f" a={v}"
    # R < 2^(N/2) check for n>=7
    gap = (R.bit_length() <= N//2) if n>=7 else None
    print(n, 'is_power=',ip, info, 'R<2^(N/2):',gap, 'Rbits=',R.bit_length(), 'N/2=',N/2, f"{time.time()-t:.1f}s", flush=True)
