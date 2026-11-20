# OEIS-A113258 — Run 001 — verification log (2026-11-08)

Environment: Linux VM, gcc 13.3.0 (-O3 -march=native), Python 3.13.18, gmpy2 2.3.2, sympy 1.14.0, mpmath 1.3.0, PARI 2.17.2 (cypari2; not needed for the proof).
Sources: `code/` (cert_dlog.c, verify_direct.c, compact.py, small.py, small_independent.py, sample_check.py, laurent.py).

## A. Direct exact checks (small n)
`python3 small.py` (gmpy2 `is_power`, exact big integers):
```
1 is_power=True   a=1
2 is_power=False  a=3
3 is_power=False  a=11
4 is_power=True   a=125
5 is_power=False  a=16824569
6 is_power=False  a=1329227995784915877642188398793079569
7..11 is_power=False   (bit lengths 721, 5041, 40321, 362881, 3628801)
R < 2^(N/2) for n=7..11: True (Rbits 311, 1862, 13029, 104226, 938032 vs N/2 360, 2520, 20160, 181440, 1814400)
```
`python3 small_independent.py` (sympy only; every prime exponent l <= bitlength tested by exact integer roots):
```
4: exact root only for l=3 (5^3);  5,6,7,8: no prime exponent has an exact root; sympy.perfect_power -> False
```

## B. Laurent thresholds
`python3 laurent.py` (mpmath 50 digits): T(7,4464)=4464.51, T(12,4464)=3294.10, decreasing in n.
Minimal excluded prime: 4465 for (m,C)=(10,25.2); 11653 for (18,20.3); 28541..28543 for (30,17.9).
(The written proof uses the uniform bound rho(n) <= rho* = 1.7717 for all n >= 7.)

## C. Modular certificates — all primes 7 <= l <= 4500, all 7 <= n <= l
Generator: `./cert_dlog 7 4500 7 > certs_4500.txt` (7.3 s) → `pairs=1264003 q_used=1031 max_q_per_ell=3`
sha256(certs_4500.txt) = 743f9cc292a1962ef0e28137f19ed5256f706ca3eccd42b68ba23658f98c8067
Compact form (`certificates/certificates_l_le_4500.txt`): sha256 8f637852547236f8944a9293fe636d1048ab15c34ecf8af3902e0cf841ec511d; `compact.py expand` round-trip re-verified (0 bad).

Independent verifier (plain modular exponentiation; trial-division primality of l and q; coverage of every prime l and every n):
`./verify_direct 7 4500 7 certs_4500.txt`
```
ells=607 verified_pairs=1264003 bad=0
elapsed 208s
```
Python spot checks `python3 sample_check.py certs_4500.txt 7 400`:
```
exact small-n checks: 606      (a(n) mod q from the EXACT big integer equals the modular formula, n<=11)
random sample checks passed: 400
```

## D. Robustness extension (all primes l <= 28600; covers the weakest quoted Laurent pair (30,17.9))
The robustness addendum is not included in this repository; the proof does not depend on it.

## Reproduce
```
gcc -O3 -march=native -o cert_dlog cert_dlog.c && gcc -O3 -march=native -o verify_direct verify_direct.c
./cert_dlog 7 4500 7 > certs_4500.txt && sha256sum certs_4500.txt
./verify_direct 7 4500 7 certs_4500.txt
python3 small.py; python3 small_independent.py; python3 laurent.py; python3 sample_check.py certs_4500.txt 7 400
```
