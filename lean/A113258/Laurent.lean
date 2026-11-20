import A113258.LaurentNumerics

/-!
# Large prime exponents: the Baker–Laurent step (Proposition 3)

The only imported (unproved) result is a specialisation of
M. Laurent, *Acta Arith.* **133** (2008) 325–348, Corollary 2, stated as the axiom
`laurent_cor2`.  Everything else is proved.
-/

namespace A113258

open Nat Real

/-- **Imported theorem** (M. Laurent, Acta Arith. 133 (2008) 325–348, Corollary 2), in the
instance `(m, C) = (10, 25.2)`, `D = 1`, `α₁ = 2`, `α₂ = Y` (an odd integer `≥ 3`, so `2` and `Y`
are multiplicatively independent), `log A₁ = 1`, `log A₂ = log Y`:
for positive integers `b₁, b₂` and `Λ = b₂ log Y - b₁ log 2 ≠ 0`,
`log |Λ| ≥ -25.2 · (max {log b' + 0.38, 10})² · log Y`, where `b' = b₁ / log Y + b₂`.
The constants `(10, 25.2)` are taken as quoted in arXiv:2604.18991 §6. -/
axiom laurent_cor2 (Y b1 b2 : ℕ) (hY3 : 3 ≤ Y) (hYodd : Odd Y) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hΛ : (b2 : ℝ) * Real.log Y - (b1 : ℝ) * Real.log 2 ≠ 0) :
    -(25.2 * (max (Real.log ((b1 : ℝ) / Real.log Y + b2) + 0.38) 10) ^ 2 * Real.log Y) ≤
      Real.log |(b2 : ℝ) * Real.log Y - (b1 : ℝ) * Real.log 2|

lemma term_even {n j : ℕ} (hj : 2 ≤ j) : Even (term n j) := by
  unfold term
  rw [Nat.even_pow]
  exact ⟨(even_iff_two_dvd).2 (Nat.dvd_factorial (by norm_num) hj),
    (Nat.factorial_pos _).ne'⟩

lemma a_odd {n : ℕ} (hn : 3 ≤ n) : Odd (a n) := by
  rw [a_eq_pow_add_R hn]
  have hN : 0 < (n - 1)! := Nat.factorial_pos _
  have h2 : Even (2 ^ (n - 1)!) := (Nat.even_pow).2 ⟨even_two, hN.ne'⟩
  have hsum : Even (∑ j ∈ Finset.Icc 3 n, term n j) := by
    rw [even_iff_two_dvd]
    exact Finset.dvd_sum fun j hj => by
      rw [← even_iff_two_dvd]
      exact term_even (by rw [Finset.mem_Icc] at hj; omega)
  have hR : Odd (R n) := by
    unfold R
    rw [add_comm]
    exact hsum.add_one
  exact h2.add_odd hR

set_option maxHeartbeats 2000000 in
-- long chain of real-number estimates with several `positivity`/`nlinarith` calls
/-- **Proposition 3.** For `n ≥ 7` and `ℓ ≥ 4465`, `a n` is not an `ℓ`-th power. -/
theorem no_large_exponent {n ell Y : ℕ} (hn : 7 ≤ n) (hell : 4465 ≤ ell) : a n ≠ Y ^ ell := by
  intro hY
  have hn3 : 3 ≤ n := by omega
  have hdecomp := a_eq_pow_add_R hn3
  have hRlt := R_lt hn
  have hR1 := one_le_R n
  have hRle := R_le hn3
  have hfac : (n - 1)! = (n - 1) * (n - 2)! := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, Nat.factorial_succ]
  have hR6 : R n ≤ (n - 1) * 6 ^ (n - 2)! := by
    have h6 : 1 ≤ 6 ^ (n - 2)! := Nat.one_le_pow _ _ (by norm_num)
    have h : n - 1 = (n - 2) + 1 := by omega
    calc R n ≤ 1 + (n - 2) * 6 ^ (n - 2)! := hRle
      _ ≤ (n - 1) * 6 ^ (n - 2)! := by rw [h, add_mul, one_mul]; omega
  have hRN : R n < 2 ^ (n - 1)! :=
    lt_of_lt_of_le hRlt (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _))
  have hodd : Odd Y := by
    have h : Odd (Y ^ ell) := hY ▸ a_odd hn3
    exact (Nat.odd_pow_iff (by omega)).1 h
  have hY3 : 3 ≤ Y := by
    by_contra hlt
    obtain ⟨t, ht⟩ := hodd
    have hY1 : Y = 1 := by omega
    have h1 : a n = 1 := by rw [hY, hY1, one_pow]
    have h2 : 0 < 2 ^ (n - 1)! := by positivity
    omega
  have hNpos : 0 < (n - 1)! := Nat.factorial_pos _
  -- real-number facts
  have hYr : (Y : ℝ) ^ ell = (a n : ℝ) := by exact_mod_cast hY.symm
  have hanr : (a n : ℝ) = 2 ^ (n - 1)! + (R n : ℝ) := by exact_mod_cast hdecomp
  have hRpos : (0 : ℝ) < (R n : ℝ) := by exact_mod_cast hR1
  have hRltN : (R n : ℝ) < 2 ^ (n - 1)! := by exact_mod_cast hRN
  have hY1r : (1 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 1 < Y)
  have hLYpos : 0 < Real.log (Y : ℝ) := Real.log_pos hY1r
  have h2N : (0 : ℝ) < 2 ^ (n - 1)! := by positivity
  have hR6r : (R n : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * 6 ^ (n - 2)! := by exact_mod_cast hR6
  have hn1pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 0 < n - 1 := by omega
    exact_mod_cast this
  -- Λ
  have hΛeq : (ell : ℝ) * Real.log Y - ((n - 1)! : ℝ) * Real.log 2
      = Real.log ((a n : ℝ) / 2 ^ (n - 1)!) := by
    rw [Real.log_div (by rw [hanr]; positivity) (by positivity), ← hYr, Real.log_pow, Real.log_pow]
  have hxdef : (a n : ℝ) / 2 ^ (n - 1)! = 1 + (R n : ℝ) / 2 ^ (n - 1)! := by
    rw [hanr]; field_simp
  have hx1 : 1 < (a n : ℝ) / 2 ^ (n - 1)! := by
    rw [hxdef]; have : 0 < (R n : ℝ) / 2 ^ (n - 1)! := by positivity
    linarith
  have hΛpos : 0 < (ell : ℝ) * Real.log Y - ((n - 1)! : ℝ) * Real.log 2 := by
    rw [hΛeq]; exact Real.log_pos hx1
  have hΛle : (ell : ℝ) * Real.log Y - ((n - 1)! : ℝ) * Real.log 2 ≤ (R n : ℝ) / 2 ^ (n - 1)! := by
    rw [hΛeq]
    have := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hx1)
    rw [hxdef] at this ⊢
    linarith
  have hΛlt1 : (ell : ℝ) * Real.log Y - ((n - 1)! : ℝ) * Real.log 2 < 1 := by
    have : (R n : ℝ) / 2 ^ (n - 1)! < 1 := (div_lt_one h2N).2 hRltN
    linarith
  -- upper bound for log Λ
  have hlogΛ : Real.log ((ell : ℝ) * Real.log Y - ((n - 1)! : ℝ) * Real.log 2) ≤
      Real.log ((n - 1 : ℕ) : ℝ) + ((n - 2)! : ℝ) * Real.log 6 - ((n - 1)! : ℝ) * Real.log 2 := by
    have h1 := Real.log_le_log hΛpos hΛle
    have h2 : Real.log ((R n : ℝ) / 2 ^ (n - 1)!) = Real.log (R n : ℝ) - ((n - 1)! : ℝ) * Real.log 2 := by
      rw [Real.log_div hRpos.ne' h2N.ne', Real.log_pow]
    have h3 : Real.log (R n : ℝ) ≤ Real.log (((n - 1 : ℕ) : ℝ) * 6 ^ (n - 2)!) :=
      Real.log_le_log hRpos hR6r
    have h4 : Real.log (((n - 1 : ℕ) : ℝ) * 6 ^ (n - 2)!) =
        Real.log ((n - 1 : ℕ) : ℝ) + ((n - 2)! : ℝ) * Real.log 6 := by
      rw [Real.log_mul hn1pos.ne' (by positivity), Real.log_pow]
    linarith
  -- lower bound from Laurent
  have hlaur := laurent_cor2 Y ((n - 1)!) ell hY3 hodd hNpos (by omega) hΛpos.ne'
  rw [abs_of_pos hΛpos] at hlaur
  -- b' ≤ 2.4427 ell
  have hL2 := Real.log_two_gt_d9
  have hNle : ((n - 1)! : ℝ) ≤ 1.4427 * (ell : ℝ) * Real.log Y := by
    have h1 : ((n - 1)! : ℝ) * Real.log 2 < (ell : ℝ) * Real.log Y := by linarith
    have hN0 : (0 : ℝ) ≤ ((n - 1)! : ℝ) := by positivity
    nlinarith
  have hbpr : ((n - 1)! : ℝ) / Real.log Y ≤ 1.4427 * (ell : ℝ) := by
    rw [div_le_iff₀ hLYpos]; linarith
  have hellpos : (0 : ℝ) < (ell : ℝ) := by
    have : 0 < ell := by omega
    exact_mod_cast this
  have hb'pos : 0 < ((n - 1)! : ℝ) / Real.log Y + (ell : ℝ) := by positivity
  have hb'le : ((n - 1)! : ℝ) / Real.log Y + (ell : ℝ) ≤ 2.4427 * (ell : ℝ) := by linarith
  have hlogb' : Real.log (((n - 1)! : ℝ) / Real.log Y + (ell : ℝ)) ≤ Real.log (2.4427 * (ell : ℝ)) :=
    Real.log_le_log hb'pos hb'le
  set Mℓ : ℝ := max (Real.log (2.4427 * (ell : ℝ)) + 0.38) 10 with hMℓ
  have hMle : max (Real.log (((n - 1)! : ℝ) / Real.log Y + (ell : ℝ)) + 0.38) 10 ≤ Mℓ :=
    max_le_max (by linarith) le_rfl
  have hM10 : (10 : ℝ) ≤ max (Real.log (((n - 1)! : ℝ) / Real.log Y + (ell : ℝ)) + 0.38) 10 :=
    le_max_right _ _
  have hMsq : (max (Real.log (((n - 1)! : ℝ) / Real.log Y + (ell : ℝ)) + 0.38) 10) ^ 2 ≤ Mℓ ^ 2 :=
    pow_le_pow_left₀ (by linarith) hMle 2
  have hMℓ10 : (10 : ℝ) ≤ Mℓ := le_max_right _ _
  -- combine
  have hkey := key_ineq hn
  set den : ℝ := ((n - 1)! : ℝ) * Real.log 2 - ((n - 2)! : ℝ) * Real.log 6
    - Real.log ((n - 1 : ℕ) : ℝ) with hden
  have hdenpos : 0 < den := by
    have : (0 : ℝ) < ((n - 1)! : ℝ) * Real.log 2 + 1 := by positivity
    linarith
  have h1 : den ≤ 25.2 * Mℓ ^ 2 * Real.log Y := by
    have hLYnn := hLYpos.le
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMsq (by norm_num : (0:ℝ) ≤ 25.2)) hLYnn
    linarith
  have h2 : (ell : ℝ) * Real.log Y < 1.7717 * den := by linarith
  have hP : (0 : ℝ) < 25.2 * Mℓ ^ 2 := by positivity
  have hfin := final_ineq (x := (ell : ℝ)) (by exact_mod_cast hell)
  rw [← hMℓ] at hfin
  have h3 : (ell : ℝ) * den ≤ 25.2 * Mℓ ^ 2 * ((ell : ℝ) * Real.log Y) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hellpos.le]
  have h4 : 25.2 * Mℓ ^ 2 * ((ell : ℝ) * Real.log Y) < 25.2 * Mℓ ^ 2 * (1.7717 * den) :=
    mul_lt_mul_of_pos_left h2 hP
  have h5 : 25.2 * 1.7717 * Mℓ ^ 2 * den ≤ (ell : ℝ) * den :=
    mul_le_mul_of_nonneg_right hfin hdenpos.le
  nlinarith

end A113258
