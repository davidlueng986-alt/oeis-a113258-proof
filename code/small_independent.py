# Independent check (no gmpy2): a(n) for n=5,6 (and 7,8) is not a perfect power,
# by testing every prime exponent l <= log2(a(n)) with exact integer l-th roots (sympy.integer_nthroot).
from math import factorial
from sympy import integer_nthroot, primerange, perfect_power
def a(n): return sum(factorial(i)**factorial(n-i+1) for i in range(1,n+1))
for n in [4,5,6,7,8]:
    v=a(n); B=v.bit_length()
    hits=[l for l in primerange(2,B+1) if integer_nthroot(v,l)[1]]
    print(n, 'bits',B,'prime exponents l with exact root:',hits, ' sympy.perfect_power ->', perfect_power(v))
