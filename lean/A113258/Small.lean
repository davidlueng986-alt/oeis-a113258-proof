import A113258.Defs

/-!
# The small cases `n = 5, 6`

`a 5 = 16824569` and `a 6 = 1329227995784915877642188398793079569` are not perfect powers:
for every exponent `2 ≤ e ≤ B` an explicit integer `c` with `c^e < a n < (c+1)^e` is given,
and for `e > B` the bound `a n < 2^(B+1)` rules out every base.
-/

namespace A113258

open Nat

lemma no_power_small (x B : ℕ) (cs : List ℕ) (hB : x < 2 ^ (B + 1)) (hx1 : 1 < x)
    (hcs : (List.range (B - 1)).all
      (fun i => cs[i]! ^ (i + 2) < x && x < (cs[i]! + 1) ^ (i + 2)) = true) :
    ∀ b e : ℕ, 2 ≤ e → x ≠ b ^ e := by
  intro b e he hx
  by_cases hle : e ≤ B
  · have hi : e - 2 ∈ List.range (B - 1) := by rw [List.mem_range]; omega
    have h := (List.all_eq_true.1 hcs) (e - 2) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have he2 : e - 2 + 2 = e := by omega
    rw [he2] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hbc : b ≤ cs[e - 2]!
    · have : b ^ e ≤ cs[e - 2]! ^ e := Nat.pow_le_pow_left hbc e
      omega
    · have : (cs[e - 2]! + 1) ^ e ≤ b ^ e := Nat.pow_le_pow_left (by omega) e
      omega
  · have hBe : B < e := not_le.mp hle
    by_cases hb : b ≤ 1
    · have hb' : b = 0 ∨ b = 1 := by omega
      rcases hb' with rfl | rfl
      · rw [zero_pow (by omega)] at hx; omega
      · rw [one_pow] at hx; omega
    · have h2 : 2 ^ e ≤ b ^ e := Nat.pow_le_pow_left (by omega) e
      have h3 : 2 ^ (B + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

lemma a_four : a 4 = 5 ^ 3 := by decide

lemma a_five : a 5 = 16824569 := by decide

lemma a_six : a 6 = 1329227995784915877642188398793079569 := by
  norm_num [a, Finset.sum_range_succ, Nat.factorial]

theorem a_five_not_pow : ∀ b e : ℕ, 2 ≤ e → a 5 ≠ b ^ e := by
  rw [a_five]
  exact no_power_small 16824569 24 [4101, 256, 64, 27, 16, 10, 8, 6, 5, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2] (by norm_num) (by norm_num) (by decide)

theorem a_six_not_pow : ∀ b e : ℕ, 2 ≤ e → a 6 ≠ b ^ e := by
  rw [a_six]
  exact no_power_small 1329227995784915877642188398793079569 120 [1152921504606846978, 1099511627776, 1073741824, 16777216, 1048576, 144715, 32768, 10321, 4096, 1922, 1024, 600, 380, 256, 181, 133, 101, 79, 64, 52, 43, 37, 32, 27, 24, 21, 19, 17, 16, 14, 13, 12, 11, 10, 10, 9, 8, 8, 8, 7, 7, 6, 6, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] (by norm_num) (by norm_num)
    (by decide)

end A113258
