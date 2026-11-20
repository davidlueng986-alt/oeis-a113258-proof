/-!
# Executable certificate checker (no Mathlib dependency)

This module only uses `Init`, so that it can be compiled to native code
(`precompileModules`) and run by `native_decide`.  Its soundness is proved in
`A113258.CertCore` and `A113258.Cert`.
-/

namespace A113258

/-! ### Modular exponentiation -/

/-- Square-and-multiply with a fuel parameter. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e = 0 then acc
    else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

/-- `powMod b e m = b ^ e % m`, computed by square-and-multiply. -/
def powMod (b e m : Nat) : Nat := powModAux m (e + 1) b e 1 % m

/-! ### Factorial tables -/

/-- `factTable M k = #[0! % M, 1! % M, …, k! % M]`. -/
def factTable (M : Nat) : Nat → Array Nat
  | 0 => #[1 % M]
  | k + 1 => (factTable M k).push ((factTable M k)[k]! * (k + 1) % M)

/-! ### Primality by trial division -/

/-- `isPrimeAux n fuel d`: no `e ≥ d` with `e * e ≤ n` (and `e < d + fuel`) divides `n`. -/
def isPrimeAux (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => if d * d ≤ n then (n % d != 0 && isPrimeAux n fuel (d + 1)) else true

/-- Primality test by trial division up to `√n`. -/
def isPrimeB (n : Nat) : Bool := decide (2 ≤ n) && isPrimeAux n n 2

/-! ### The checker -/

/-- `a(n) mod q` computed from the tables `F[j] = j! mod q`, `E[k] = k! mod (q-1)`;
sums the terms `j = 1, …, m`. -/
def aModAux (q n : Nat) (F E : Array Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (aModAux q n F E j + powMod F[j + 1]! E[n - (j + 1) + 1]! q) % q

/-- Check one pair `(ℓ, q, n)` given the two tables. -/
def pairOK (ell q n : Nat) (F E : Array Nat) : Bool :=
  let A := aModAux q n F E n
  (A % q != 0) && (powMod A ((q - 1) / ell) q != 1)

/-- Check that `q` certifies every `n ∈ ns` for `ℓ`. -/
def qOK (ell q : Nat) (ns : List Nat) : Bool :=
  isPrimeB q && (q % ell == 1) &&
    (let F := factTable q ell
     let E := factTable (q - 1) ell
     ns.all fun n => n ≤ ell && pairOK ell q n F E)

/-- Check the entry `ℓ ↦ (q₁, exceptions)`: `q₁` certifies all `n ∈ [7, ℓ]` not listed among the
exceptions, and each exception `(q, ns)` certifies the `n ∈ ns`. -/
def entryOK (ell q1 : Nat) (exc : List (Nat × List Nat)) : Bool :=
  decide (7 ≤ ell) && isPrimeB ell &&
    qOK ell q1 ((List.range' 7 (ell - 6)).filter fun n => !(exc.any fun p => p.2.contains n)) &&
    exc.all fun p => qOK ell p.1 p.2

/-- The whole certificate table. -/
def tableOK (tbl : List (Nat × Nat × List (Nat × List Nat))) : Bool :=
  tbl.all fun e => entryOK e.1 e.2.1 e.2.2

/-- Every prime `ℓ ∈ [7, L]` occurs in the table. -/
def coverOK (tbl : List (Nat × Nat × List (Nat × List Nat))) (L : Nat) : Bool :=
  (List.range (L + 1)).all fun ell =>
    !(decide (7 ≤ ell) && isPrimeB ell) || tbl.any fun e => e.1 == ell

end A113258
