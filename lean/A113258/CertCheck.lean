import A113258.Cert
import A113258Check

/-!
# The middle range `n ≤ ℓ ≤ 4463`

The certificate table `certTable` is checked by `native_decide` (this uses the axiom
`Lean.ofReduceBool`, i.e. it trusts Lean's compiler/evaluator for the executable
checker in `A113258Check.Checker`).  The soundness of the checker is proved in `A113258.Cert`.
-/

namespace A113258

theorem certTable_tableOK : tableOK certTable = true := by native_decide

theorem certTable_coverOK : coverOK certTable 4463 = true := by native_decide

/-- Proposition 4: for primes `ℓ ≤ 4463` and `7 ≤ n ≤ ℓ`, `a n` is not an `ℓ`-th power. -/
theorem middle_range {ell n : ℕ} (hp : ell.Prime) (hn : 7 ≤ n) (hnl : n ≤ ell) (hL : ell ≤ 4463) :
    ¬ ∃ Y : ℕ, a n = Y ^ ell :=
  table_sound certTable_tableOK certTable_coverOK ell n hp hn hnl hL

end A113258
