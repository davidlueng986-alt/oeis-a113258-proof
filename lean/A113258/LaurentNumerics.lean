import A113258.Elementary

/-!
# Real-number inequalities for the Baker–Laurent step

* `key_ineq`: `N log 2 + 1 ≤ ρ* · (N log 2 − m log 6 − log (n-1))` with `ρ* = 1.7717`,
  where `N = (n-1)!`, `m = (n-2)!`, `n ≥ 7`.
* `final_ineq`: for real `x ≥ 4465`, `25.2·ρ*·(max (log (2.4427 x) + 0.38) 10)^2 ≤ x`.
-/

namespace A113258

open Nat Real

lemma log6_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

lemma log6_lt : Real.log 6 < 1.7917594696 := by
  rw [log6_eq]; linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

lemma log6_gt : 1.79 < Real.log 6 := by
  rw [log6_eq]; linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

lemma fact_ge {n : ℕ} (hn : 7 ≤ n) : 720 * (n - 6) ≤ (n - 1)! := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : n + 1 - 1 = n := by omega
    have h2 : n = (n - 1) + 1 := by omega
    have hf : n ! = n * (n - 1)! := by
      conv_lhs => rw [h2]
      rw [Nat.factorial_succ, ← h2]
    rw [h1, hf]
    have h3 : 720 * (n - 6) * n ≤ (n - 1)! * n := Nat.mul_le_mul_right _ ih
    have h4 : 720 * (n + 1 - 6) ≤ 720 * (n - 6) * n := by
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 7 := ⟨n - 7, by omega⟩
      have : t + 7 + 1 - 6 = t + 2 := by omega
      have h5 : t + 7 - 6 = t + 1 := by omega
      rw [this, h5]
      nlinarith
    calc 720 * (n + 1 - 6) ≤ 720 * (n - 6) * n := h4
      _ ≤ (n - 1)! * n := h3
      _ = n * (n - 1)! := Nat.mul_comm _ _

lemma factorial_ge_720 {n : ℕ} (hn : 7 ≤ n) : 720 ≤ (n - 1)! := by
  have := fact_ge hn
  omega

lemma key_ineq {n : ℕ} (hn : 7 ≤ n) :
    ((n - 1)! : ℝ) * Real.log 2 + 1 ≤
      1.7717 * (((n - 1)! : ℝ) * Real.log 2 - ((n - 2)! : ℝ) * Real.log 6
        - Real.log ((n - 1 : ℕ) : ℝ)) := by
  have hfac : (n - 1)! = (n - 1) * (n - 2)! := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, Nat.factorial_succ]
  have h720 : (720 : ℝ) ≤ ((n - 1)! : ℝ) := by exact_mod_cast factorial_ge_720 hn
  have h6m : 6 * ((n - 2)! : ℝ) ≤ ((n - 1)! : ℝ) := by
    have : 6 * (n - 2)! ≤ (n - 1)! := by rw [hfac]; exact Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast this
  have hNge : (720 : ℝ) * ((n - 6 : ℕ) : ℝ) ≤ ((n - 1)! : ℝ) := by
    exact_mod_cast fact_ge hn
  have hL := log6_gt
  have hlog : Real.log ((n - 1 : ℕ) : ℝ) ≤ ((n - 1)! : ℝ) * Real.log 6 / 720 := by
    have hn6 : (6 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have : 6 ≤ n - 1 := by omega
      exact_mod_cast this
    have hsplit : Real.log ((n - 1 : ℕ) : ℝ) =
        Real.log 6 + Real.log (((n - 1 : ℕ) : ℝ) / 6) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1; ring
    have hle : Real.log (((n - 1 : ℕ) : ℝ) / 6) ≤ ((n - 1 : ℕ) : ℝ) / 6 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hcast : ((n - 1 : ℕ) : ℝ) = ((n - 6 : ℕ) : ℝ) + 5 := by
      have : n - 1 = (n - 6) + 5 := by omega
      rw [this]; push_cast; ring
    have hn6' : (1 : ℝ) ≤ ((n - 6 : ℕ) : ℝ) := by
      have : 1 ≤ n - 6 := by omega
      exact_mod_cast this
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hNge (le_of_lt (by linarith : (0:ℝ) < Real.log 6))]
  have hL2l := Real.log_two_gt_d9
  have hL6u := log6_lt
  have hL2u := Real.log_two_lt_d9
  have hbr : 0 ≤ 1.7717 * (Real.log 2 - 121 * Real.log 6 / 720) - Real.log 2 - 1 / 720 := by
    linarith
  generalize ((n - 1)! : ℝ) = N at *
  generalize ((n - 2)! : ℝ) = m at *
  have hN0 : 0 ≤ N := by linarith
  have hm6 : m * Real.log 6 ≤ N * Real.log 6 / 6 := by
    have := mul_le_mul_of_nonneg_right h6m (le_of_lt (by linarith : (0:ℝ) < Real.log 6))
    linarith
  nlinarith [mul_nonneg hN0 hbr, hlog, hm6]

/-- For `x ≥ 4465`: `25.2 * 1.7717 * (max (log (2.4427 x) + 0.38) 10)^2 ≤ x`. -/
lemma final_ineq {x : ℝ} (hx : 4465 ≤ x) :
    25.2 * 1.7717 * (max (Real.log (2.4427 * x) + 0.38) 10) ^ 2 ≤ x := by
  rcases le_total (Real.log (2.4427 * x) + 0.38) 10 with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]
    set y : ℝ := 2.4427 * x with hy
    have hy0 : 10906 ≤ y := by rw [hy]; nlinarith
    set s : ℝ := Real.sqrt y with hs
    have hss : s * s = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs104 : 104.4 ≤ s := by nlinarith
    have hlogy : Real.log y = 2 * Real.log s := by
      rw [hs, Real.log_sqrt (by linarith)]; ring
    have hle : Real.log (s / 128) ≤ s / 128 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (s / 128) = Real.log s - 7 * Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num)]
      have : (128 : ℝ) = 2 ^ 7 := by norm_num
      rw [this, Real.log_pow]; norm_num
    have hL2u := Real.log_two_lt_d9
    have hlogs : Real.log s ≤ 7 * Real.log 2 + s / 128 - 1 := by linarith
    have hU : Real.log y + 0.38 ≤ 8.0841 + s / 64 := by rw [hlogy]; linarith
    have hpos : 0 ≤ Real.log y + 0.38 := by linarith
    have hw : 8.0841 + s / 64 ≤ s * (2 / 21) := by linarith
    have hsq : (Real.log y + 0.38) ^ 2 ≤ (s * (2 / 21)) ^ 2 := by
      apply pow_le_pow_left₀ hpos
      linarith
    have hx' : x = y / 2.4427 := by rw [hy]; field_simp
    have key : 25.2 * 1.7717 * (s * (2 / 21)) ^ 2 ≤ x := by
      rw [hx', ← hss, le_div_iff₀ (by norm_num)]
      nlinarith [mul_self_nonneg s]
    calc 25.2 * 1.7717 * (Real.log y + 0.38) ^ 2 ≤ 25.2 * 1.7717 * (s * (2 / 21)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsq; norm_num
      _ ≤ x := key

end A113258
