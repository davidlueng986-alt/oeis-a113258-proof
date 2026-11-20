import Mathlib

/-!
# OEIS A113258: definitions

`a n = ∑_{i=1}^{n} (i!)^((n-i+1)!)`, stated exactly as in
google-deepmind/formal-conjectures (`OeisA113258.a`), plus a 1-based form.
-/

namespace A113258

open Nat

/-- `a n = ∑ i ∈ range n, (i+1)! ^ (n-i)!` (same definition as `OeisA113258.a`). -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + 1)! ^ (n - i)!

/-- The `j`-th summand, `j = 1, …, n`. -/
def term (n j : ℕ) : ℕ := j ! ^ (n - j + 1)!

lemma a_eq_Icc (n : ℕ) : a n = ∑ j ∈ Finset.Icc 1 n, term n j := by
  unfold a term
  have h1 : ∑ i ∈ Finset.range n, (i + 1)! ^ (n - i)!
      = ∑ i ∈ Finset.range n, (i + 1)! ^ (n - (i + 1) + 1)! := by
    apply Finset.sum_congr rfl
    intro i hi
    have : i < n := Finset.mem_range.mp hi
    have h : n - i = n - (i + 1) + 1 := by omega
    rw [h]
  rw [h1, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => j ! ^ (n - j + 1)!) 0 n 1]
  rfl

end A113258
