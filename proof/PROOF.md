# OEIS A113258 — There is no perfect power after a(4) = 5³ (complete negative answer)

**Status:** CLOSED (project-internal). Complete proof = elementary lemmas + one published theorem (Laurent 2008, linear forms in two logarithms) + an exact finite modular certificate, checked by two independent implementations.
**Provenance:** 2026-11-08. Developed with AI assistance (derivation, code, computational verification and the Lean formalization). Lean-checked only relative to Laurent's theorem (an axiom) and `native_decide` for the certificate table; see `lean/README.md`. External acceptance / priority: not assessed (see §9).

## 1. The question

A113258 (Jonathan Vos Post, 2006): a(n) = Σ_{i=1}^{n} (i!)^{(n−i+1)!}, so a(1..6) = 1, 3, 11, 125, 16824569, 1329227995784915877642188398793079569.
The OEIS entry asks: *"Is there a nontrivial power after a(4) = 5^3?"*
The DeepMind formal-conjectures file `FormalConjectures/OEIS/113258.lean` (category `research open`) states it as

    def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + 1)! ^ (n - i)!
    theorem conjecture : ∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e

(identical sequence: index i ↦ i+1).

**Theorem.** For every n ≥ 5, a(n) is not a perfect power: there are no integers b > 1, e > 1 with a(n) = b^e.
Consequently the answer to the OEIS question is **No**, the formal statement above is **false**, and the complete set of n ≥ 1 for which a(n) is a perfect power b^e (b, e > 1) is {4}.

## 2. Notation

N := (n−1)!.  The i = 2 term is 2^N.  Put R := a(n) − 2^N = 1 + Σ_{i=3}^{n} (i!)^{(n−i+1)!}.
For n ≥ 2 every term with i ≥ 2 is even, so a(n) is odd.

It suffices to show a(n) is not an ℓ-th power for every **prime** ℓ (if a(n) = b^e, e ≥ 2, and ℓ | e is prime, then a(n) = (b^{e/ℓ})^ℓ).

## 3. Lemma 1 (R is tiny compared with 2^N)

(a) For n ≥ 4 and 3 ≤ i ≤ n: (i!)^{(n−i+1)!} ≤ 6^{(n−2)!}.  Hence R ≤ 1 + (n−2)·6^{(n−2)!} ≤ (n−1)·6^{N/(n−1)}.
(b) For n ≥ 7: R < 2^{N/2}.

*Proof.* (a) Let f(i) = (n−i+1)!·log(i!). For 3 ≤ i ≤ n−1,
f(i+1)/f(i) = log((i+1)!) / ((n−i+1)·log(i!)) = (1 + log(i+1)/log(i!)) / (n−i+1) ≤ (1 + log 4/log 6)/2 < 0.89,
because n−i+1 ≥ 2 and log(i+1)/log(i!) is ≤ log 4/log 6 for i ≥ 3 (it decreases in i). So f is decreasing on {3,…,n} and f(i) ≤ f(3) = (n−2)!·log 6.
(b) In base-2 logarithms we need log₂(n−1) + (n−2)!·log₂6 < (n−1)!/2, i.e. log₂(n−1) < (n−2)!·((n−1)/2 − log₂6). For n = 7 the right side is 120·(3 − 2.585) ≈ 49.8 > log₂6; for n ≥ 7 the right side is ≥ 0.415·(n−2)! ≥ 1.2n > log₂(n−1). ∎
(Exact numerics for n = 7..11: bit-length of R is 311, 1862, 13029, 104226, 938032 versus N/2 = 360, 2520, 20160, 181440, 1814400.)

## 4. Lemma 2 (exponents dividing N — the "gap" argument)

Let n ≥ 7 and let k ≥ 2 divide N. Then a(n) is not a k-th power. In particular a(n) is not an ℓ-th power for any prime ℓ ≤ n−1 (all such ℓ divide (n−1)!).

*Proof.* z := 2^{N/k} is an integer and z^k = 2^N < a(n). If a(n) = Y^k then Y ≥ z+1, so
a(n) ≥ (z+1)^k ≥ z^k + k·z^{k−1} = 2^N + k·2^{N(k−1)/k} ≥ 2^N + 2·2^{N/2},
i.e. R ≥ 2·2^{N/2}, contradicting Lemma 1(b). ∎

## 5. Large prime exponents ℓ ≥ n: Baker–Laurent

**Theorem (M. Laurent, Acta Arith. 133 (2008) 325–348, Corollary 2).** Let α₁, α₂ be multiplicatively independent positive real algebraic numbers, b₁, b₂ positive integers, Λ = b₂ log α₂ − b₁ log α₁ ≠ 0, D = [ℚ(α₁,α₂):ℚ]/[ℝ(α₁,α₂):ℝ], log A_i ≥ max{h(α_i), |log α_i|/D, 1/D}, b' = b₁/(D log A₂) + b₂/(D log A₁). Then
log|Λ| ≥ −C·D⁴·(max{log b' + 0.38, m/D, 1})²·log A₁·log A₂
for each tabulated pair (m, C); we use (m, C) = (10, 25.2) and, for robustness, also (18, 20.3) and (30, 17.9).
(These three pairs are quoted from Laurent's Corollary 2 in, e.g., arXiv:2604.18991 §6 [(10, 25.2)] and Bennett et al., arXiv:2411.12009, Cor. 2.21 [(18, 20.3), (30, 17.9)].)

**Proposition 3.** Let n ≥ 7 and let ℓ ≥ n be prime. If a(n) = Y^ℓ then ℓ < C·M(ℓ)²·ρ*, where
M(ℓ) = max{log(ℓ(1 + 1/log 2)) + 0.38, m} and ρ* = 1.7717.
Hence: with (10, 25.2) no prime ℓ ≥ 4465 is possible; with (18, 20.3) none ≥ 11653; with (30, 17.9) none ≥ 28543.

*Proof.* Y is odd and ≥ 3 (a(n) is odd and > 1), so 2 and Y are multiplicatively independent. Take α₁ = 2, b₁ = N, α₂ = Y, b₂ = ℓ, D = 1, log A₁ = 1, log A₂ = log Y (≥ 1, ≥ h(Y) = log Y). Then
Λ = ℓ log Y − N log 2 = log(1 + R/2^N) ∈ (0, R/2^N), so by Lemma 1(a)
 log Λ < log(n−1) + (N/(n−1))·log 6 − N log 2.          (1)
From Y^ℓ > 2^N: log Y > N log 2/ℓ, hence b' = N/log Y + ℓ < ℓ(1 + 1/log 2); and log Y = (N log 2 + Λ)/ℓ < (N log 2 + 1)/ℓ. Laurent gives
 log Λ ≥ −C·M(ℓ)²·log Y > −C·M(ℓ)²·(N log 2 + 1)/ℓ.        (2)
Combining (1),(2): ℓ < C·M(ℓ)²·ρ(n), ρ(n) := (N log 2 + 1)/(N log 2 − (N/(n−1)) log 6 − log(n−1)).
For n ≥ 7, termwise (1/N ≤ 1/720, log 6/(n−1) ≤ log 6/6, log(n−1)/N ≤ log 6/720):
ρ(n) ≤ (log 2 + 1/720)/(log 2 − (log 6)/6 − (log 6)/720) = 0.694536/0.392031 < 1.7717 = ρ*.
With (m, C) = (10, 25.2): for ℓ ≤ 6166, M = 10 and ℓ < 2520·1.7717 = 4464.7; for ℓ > 6166, ℓ/(log(2.4427ℓ)+0.38)² is increasing and already equals ≈ 61.7 > 25.2·1.7717 = 44.65 at ℓ = 6166. So every prime ℓ ≥ 4465 is excluded. The other two pairs are identical computations (M = 18 for ℓ ≤ 1.8·10⁷, M = 30 for ℓ ≤ 2.9·10¹²). ∎

## 6. Middle range n ≤ ℓ < 4465: exact modular certificates

**Proposition 4 (finite certificate).** For every prime ℓ with 7 ≤ ℓ ≤ 4463 and every n with 7 ≤ n ≤ ℓ there is a prime q ≡ 1 (mod ℓ) such that A := a(n) mod q ≠ 0 and A^{(q−1)/ℓ} ≢ 1 (mod q). Then A is not an ℓ-th power residue mod q, so a(n) is not an ℓ-th power.
(Robust extension computed in the same way for all primes ℓ ≤ 28600, see §8.)

a(n) mod q is computed exactly as Σ_{i=1}^{n} (i! mod q)^{((n−i+1)! mod (q−1))} mod q (Fermat; i ≤ n ≤ ℓ < q so i! is a unit mod q).
Counts (ℓ ≤ 4500): 1,264,003 pairs (n, ℓ), 1,031 primes q used, at most 3 values of q per ℓ.

## 7. Proof of the Theorem

Let n ≥ 5 and suppose a(n) = Y^ℓ with ℓ prime.
* n = 5, 6: exact computation, a(5) = 16824569 and a(6) above are not perfect powers (checked with GMP `mpz_perfect_power_p` and independently by integer roots). (Also checked directly for n = 7..11.)
* n ≥ 7, ℓ ≤ n−1: impossible by Lemma 2.
* n ≥ 7, ℓ ≥ n, ℓ ≥ 4465: impossible by Proposition 3.
* n ≥ 7, n ≤ ℓ ≤ 4463: impossible by Proposition 4.
These cases are exhaustive. ∎

## 8. Verification performed (this session)

1. **Direct exact check** n = 1..11 (`small.py`, gmpy2): powers only at n = 1 (=1) and n = 4 (=5³).
2. **Certificate generator** `cert_dlog.c` (discrete logarithms base a verified primitive root; O(ℓ²) per ℓ).
3. **Independent verifier** `verify_direct.c` — no discrete logs, plain modular exponentiation, trial-division primality of ℓ and q, and a coverage check that every prime ℓ in range and every n ∈ [7, ℓ] is certified.
4. **Python spot checks** `sample_check.py`: for n ≤ 11 compares the modular formula with the *exact* big integer a(n) mod q (606 cases), plus random (ℓ, q, n) samples.
5. **Threshold computation** `laurent.py` (mpmath, 50 digits) reproducing 4465 / 11653 / 28541 thresholds.
6. **Robustness run** over all primes ℓ ≤ 28600 (covers the most conservative tabulated Laurent constant pair (30, 17.9)); the addendum is not included in this repository. The proof above needs only ℓ ≤ 4463, which is fully verified by items 2–4.

## 9. External status / attribution (checked 2026-11-08)

* OEIS A113258 page: question still posed, no answer recorded.
* DeepMind formal-conjectures: `OeisA113258.conjecture` tagged `research open`.
* Epoch AI "OEIS Open" benchmark (Adamczewski, arXiv:2608.11941): `oeis_a113258_conjecture_0` unsolved by all four full-set runs (Claude Opus 4.8, GPT-5.5, Gemini 3.5 Flash, Gemini 3.1 Pro).
* No literature resolution found. Priority not established; not externally reviewed; Lean formalization in `lean/` takes Laurent's theorem as an axiom (it is not proved in Lean) and uses `native_decide` for the finite certificate table.

## 10. Remarks

* The same method (dominant 2^{(n−1)!} term + gap lemma + two-logarithm bound + modular sieve) applies to other "ascending descending base exponent transforms" whose dominant term is a power of a fixed integer with factorial exponent.
* Only the step ℓ ≥ n needs Baker theory; the cases ℓ < n are elementary.
