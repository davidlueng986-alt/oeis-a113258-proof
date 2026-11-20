# A113258 has no perfect powers beyond a(4) = 5^3

**Statement.** Let a(n) = sum_{i=1..n} (i!)^((n-i+1)!) ([OEIS A113258](https://oeis.org/A113258)). For every n >= 5, a(n) is not a perfect power: there are no integers b > 1, e > 1 with a(n) = b^e. Together with a(1) = 1 and a(4) = 125 = 5^3, the only n for which a(n) is a perfect power b^e (b, e > 1) is n = 4. This answers the OEIS question "Is there a nontrivial power after a(4) = 5^3?" in the negative, so the formal statement `OeisA113258.conjecture` in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/113258.lean) is false.

Author: Wan Yiu David Liang

## Proof sketch (4 lines)

a(n) = 2^N + R with N = (n-1)! and R <= (n-1)·6^((n-2)!) < 2^(N/2) (n >= 7). For a prime exponent l:

1. l <= n-1 => l | N => Y >= 2^(N/l) + 1 => R >= 2·2^(N/2), impossible;
2. l >= 4465 => Laurent (2008, Cor. 2, (m, C) = (10, 25.2)) for Λ = l·log Y - N·log 2 = log(1 + R/2^N) gives l < 4464.7, impossible;
3. n <= l <= 4463 => exact certificate q ≡ 1 (mod l) with a(n) mod q a nonzero non-l-th power (1,264,003 pairs);
4. n = 5, 6 by exact computation.

The complete argument is in [`proof/PROOF.md`](proof/PROOF.md).

## Imported theorem

The only result used without proof is M. Laurent, *Acta Arith.* **133** (2008) 325–348, Corollary 2 (a lower bound for linear forms in two logarithms). The constants used are (m, C) = (10, 25.2), and for robustness also (18, 20.3) and (30, 17.9); they are taken as quoted in arXiv:2604.18991 and arXiv:2411.12009, as recorded in `proof/PROOF.md` §5.

## Verification scope (stated honestly)

- **Finite certificate:** 1,264,003 (l, q) pairs, covering every prime 7 <= l <= 4500 and every 7 <= n <= l, with **0 failures** on independent re-check. The certificates were produced with a discrete-log generator (`code/cert_dlog.c`) and re-checked by a separate verifier that uses plain modular exponentiation and trial-division primality tests, plus a coverage check (`code/verify_direct.c`).
- **Small cases:** n = 1..11 checked with exact big-integer arithmetic (`code/small.py`, `code/small_independent.py`).
- **Lean 4 formalization, relative to two trusted pieces (`lean/`).** The whole argument is checked in Lean 4 + Mathlib with no `sorry`: `A113258.conjecture_false : ¬ ∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e`. It depends on (1) **Laurent's theorem, stated as an axiom** (`A113258.laurent_cor2`, not proved in Lean) and (2) **`native_decide`** for the finite certificate table, which trusts Lean's compiler rather than only the kernel. It is therefore *not* an axiom-free formalization. See [`lean/README.md`](lean/README.md).
- **Not externally reviewed.** The proof was read through step by step, but no outside referee has checked it, and priority has not been assessed. The Laurent constants have not been re-checked against the original paper.

Full details are in [`logs/VERIFICATION_LOG.md`](logs/VERIFICATION_LOG.md).

## Provenance

Developed with AI assistance (derivation, code, computational verification and the Lean formalization). The independent verifier is deterministic C code and uses no AI at runtime.

## Repository layout

| Path | Contents |
| --- | --- |
| `proof/PROOF.md` | Complete proof |
| `certificates/certificates_l_le_4500.txt` | Compact certificates for all primes 7 <= l <= 4500 |
| `code/` | Certificate generator, independent verifier, compaction tool and checks |
| `logs/VERIFICATION_LOG.md` | Verification log |
| `lean/` | Lean 4 + Mathlib formalization (see its README for exactly what is axiomatized) |
| `LICENSE`, `LICENSE-CC-BY-4.0.txt` | MIT (code) and CC BY 4.0 (proof text) |
| `CITATION.cff` | Citation metadata |

## How to reproduce

Requires `gcc` and Python 3. Run from the repository root:

```bash
# 1. Build the independent verifier (and the generator)
gcc -O3 -march=native -o verify_direct code/verify_direct.c
gcc -O3 -march=native -o cert_dlog code/cert_dlog.c

# 2. Expand the compact certificate file to one line per (l, q)
grep -v '^#' certificates/certificates_l_le_4500.txt | tr ';' '\n' | python3 code/compact.py expand /dev/stdin > certs_4500.txt

# 3. Run the independent verifier (about 3-4 minutes)
./verify_direct 7 4500 7 certs_4500.txt
```

Expected final line:

```
ells=607 verified_pairs=1264003 bad=0
```

Lean formalization (Lean `v4.36.0`, Mathlib `v4.36.0`):

```bash
cd lean && lake exe cache get && lake build   # includes the native_decide table check (about 5 extra minutes)
```

Optional extra checks (need `gmpy2`, `sympy` and `mpmath`):

```bash
./cert_dlog 7 4500 7 > certs_regenerated.txt     # regenerate the certificates (about 10 s)
python3 code/small.py
python3 code/small_independent.py
python3 code/laurent.py
python3 code/sample_check.py certs_4500.txt 7 400
```

## Licenses

- Code (`code/`, `lean/`): [MIT](LICENSE)
- Proof text, logs and certificate data (`proof/`, `logs/`, `certificates/`, this README): [CC BY 4.0](LICENSE-CC-BY-4.0.txt)

## Citation

See [`CITATION.cff`](CITATION.cff).
