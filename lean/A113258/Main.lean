import A113258.CertCheck
import A113258.Laurent
import A113258.Small

/-!
# Main theorem

For every `n ≥ 5`, `a n = ∑_{i=1}^{n} (i!)^((n-i+1)!)` is not a perfect power, so the
formal statement `OeisA113258.conjecture` of google-deepmind/formal-conjectures,
`∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e`, is false.

Dependencies beyond Lean core and Mathlib: the axiom `A113258.laurent_cor2` (a specialisation of
Laurent 2008, Cor. 2), and `Lean.ofReduceBool` (from `native_decide`, used for the finite
certificate table).
-/

namespace A113258

open Nat

theorem a_not_perfect_power {n : ℕ} (hn : 5 ≤ n) : ∀ b e : ℕ, 2 ≤ e → a n ≠ b ^ e := by
  intro b e he hab
  by_cases h5 : n = 5
  · subst h5; exact a_five_not_pow b e he hab
  by_cases h6 : n = 6
  · subst h6; exact a_six_not_pow b e he hab
  have hn7 : 7 ≤ n := by omega
  obtain ⟨ell, hell, hdvd⟩ := Nat.exists_prime_and_dvd (show e ≠ 1 by omega)
  obtain ⟨k, hk⟩ := hdvd
  have hab' : a n = (b ^ k) ^ ell := by rw [hab, hk, ← pow_mul, mul_comm]
  have hell2 := hell.two_le
  by_cases h1 : ell ≤ n - 1
  · exact not_pow_of_dvd hn7 hell2 (Nat.dvd_factorial hell.pos h1) hab'
  · by_cases h2 : 4465 ≤ ell
    · exact no_large_exponent hn7 h2 hab'
    · have h3 : ell ≠ 4464 := by
        rintro rfl
        norm_num at hell
      exact middle_range hell hn7 (by omega) (by omega) ⟨b ^ k, hab'⟩

/-- The formal-conjectures statement `OeisA113258.conjecture` is false. -/
theorem conjecture_false : ¬ ∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e := by
  rintro ⟨n, hn, b, hb, e, he, h⟩
  exact a_not_perfect_power (by omega) b e (by omega) h

end A113258
