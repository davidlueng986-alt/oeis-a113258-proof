import A113258.Defs

/-!
# Elementary lemmas (Lemma 1 and Lemma 2 of the proof)

* `R n := a n - 2^((n-1)!)`, and `R n < 2^((n-1)!/2)` for `n ≥ 7` (Lemma 1);
* `a n` is not a `k`-th power if `k ≥ 2` and `k ∣ (n-1)!` (Lemma 2, `n ≥ 7`).
-/

namespace A113258

open Nat

/-- The remainder `R n = 1 + ∑_{j=3}^{n} (j!)^((n-j+1)!)`, so that `a n = 2^((n-1)!) + R n`. -/
def R (n : ℕ) : ℕ := 1 + ∑ j ∈ Finset.Icc 3 n, term n j

lemma a_eq_pow_add_R {n : ℕ} (hn : 3 ≤ n) : a n = 2 ^ (n - 1)! + R n := by
  rw [a_eq_Icc]
  have hI : Finset.Icc 1 n = insert 1 (insert 2 (Finset.Icc 3 n)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ insert 2 (Finset.Icc 3 n) := by simp
  have h2 : (2 : ℕ) ∉ Finset.Icc 3 n := by simp
  rw [hI, Finset.sum_insert h1, Finset.sum_insert h2]
  have t1 : term n 1 = 1 := by simp [term]
  have t2 : term n 2 = 2 ^ (n - 1)! := by
    have : n - 2 + 1 = n - 1 := by omega
    simp [term, this]
  rw [t1, t2, R]
  ring

lemma term_succ_le {n j : ℕ} (hj : 3 ≤ j) (hn : j + 1 ≤ n) : term n (j + 1) ≤ term n j := by
  unfold term
  have e1 : n - (j + 1) + 1 = n - j := by omega
  rw [e1]
  have h1 : (j + 1)! ≤ (j !) ^ (n - j + 1) := by
    have hj1 : j + 1 ≤ j ! := Nat.lt_factorial_self hj
    calc (j + 1)! = (j + 1) * j ! := Nat.factorial_succ j
      _ ≤ j ! * j ! := Nat.mul_le_mul_right _ hj1
      _ = (j !) ^ 2 := (sq _).symm
      _ ≤ (j !) ^ (n - j + 1) := Nat.pow_le_pow_right (Nat.factorial_pos j) (by omega)
  calc (j + 1)! ^ (n - j)! ≤ ((j !) ^ (n - j + 1)) ^ (n - j)! := Nat.pow_le_pow_left h1 _
    _ = j ! ^ ((n - j + 1) * (n - j)!) := (pow_mul _ _ _).symm
    _ = j ! ^ (n - j + 1)! := by rw [Nat.factorial_succ (n - j)]

lemma term_le_six {n j : ℕ} (hj : 3 ≤ j) (hjn : j ≤ n) : term n j ≤ 6 ^ (n - 2)! := by
  induction j, hj using Nat.le_induction with
  | base =>
    have h2 : n - 3 + 1 = n - 2 := by omega
    have h3 : (3 : ℕ)! = 6 := by decide
    exact le_of_eq (by unfold term; rw [h2, h3])
  | succ j hj ih =>
    exact (term_succ_le hj hjn).trans (ih (by omega))

lemma R_le {n : ℕ} (hn : 3 ≤ n) : R n ≤ 1 + (n - 2) * 6 ^ (n - 2)! := by
  unfold R
  have : ∑ j ∈ Finset.Icc 3 n, term n j ≤ (Finset.Icc 3 n).card • 6 ^ (n - 2)! :=
    Finset.sum_le_card_nsmul _ _ _ (fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact term_le_six hj.1 hj.2)
  rw [Nat.card_Icc, smul_eq_mul] at this
  have h3 : n + 1 - 3 = n - 2 := by omega
  rw [h3] at this
  omega

lemma one_add_mul_six_pow_lt (m : ℕ) (hm : 10 ≤ m) : 1 + m * 6 ^ m < 8 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hx : 0 < 6 ^ m := by positivity
    rw [pow_succ, pow_succ]
    nlinarith [ih, hx, hm]

/-- Lemma 1(b): `R n < 2^(N/2)` for `n ≥ 7`, where `N = (n-1)!`. -/
lemma R_lt {n : ℕ} (hn : 7 ≤ n) : R n < 2 ^ ((n - 1)! / 2) := by
  have hm : 10 ≤ (n - 2)! := by
    have : 5 ! ≤ (n - 2)! := Nat.factorial_le (by omega)
    have h5 : 5 ! = 120 := by decide
    omega
  have hle := R_le (n := n) (by omega)
  have hn2 : n - 2 ≤ (n - 2)! := Nat.self_le_factorial _
  have h6 : 1 ≤ 6 ^ (n - 2)! := Nat.one_le_pow _ _ (by norm_num)
  have hfac : (n - 1)! = (n - 1) * (n - 2)! := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, Nat.factorial_succ]
  have hN : 6 * (n - 2)! ≤ (n - 1)! := by
    rw [hfac]; exact Nat.mul_le_mul_right _ (by omega)
  have hdiv : 3 * (n - 2)! ≤ (n - 1)! / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2; omega
  have h8 : 8 ^ (n - 2)! = 2 ^ (3 * (n - 2)!) := by
    rw [pow_mul]; norm_num
  have key : 1 + (n - 2) * 6 ^ (n - 2)! < 8 ^ (n - 2)! :=
    lt_of_le_of_lt (by nlinarith [hn2, h6]) (one_add_mul_six_pow_lt _ hm)
  calc R n ≤ 1 + (n - 2) * 6 ^ (n - 2)! := hle
    _ < 8 ^ (n - 2)! := key
    _ = 2 ^ (3 * (n - 2)!) := h8
    _ ≤ 2 ^ ((n - 1)! / 2) := Nat.pow_le_pow_right (by norm_num) hdiv

lemma one_le_R (n : ℕ) : 1 ≤ R n := by
  unfold R; omega

lemma add_one_pow_ge (z j : ℕ) : z ^ (j + 1) + (j + 1) * z ^ j ≤ (z + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.mul_le_mul_right (z + 1) ih
    have hP : 0 ≤ (j + 1) * z ^ j := Nat.zero_le _
    calc z ^ (j + 1 + 1) + (j + 1 + 1) * z ^ (j + 1)
        = z ^ (j + 1) * z + (j + 1 + 1) * (z ^ j * z) := by ring
      _ ≤ (z ^ (j + 1) + (j + 1) * z ^ j) * (z + 1) := by
          ring_nf; nlinarith [Nat.zero_le (z ^ j), Nat.zero_le (j * z ^ j)]
      _ ≤ (z + 1) ^ (j + 1) * (z + 1) := h
      _ = (z + 1) ^ (j + 1 + 1) := (pow_succ _ _).symm

/-- Lemma 2: for `n ≥ 7` and `k ≥ 2` dividing `(n-1)!`, `a n` is not a `k`-th power. -/
theorem not_pow_of_dvd {n k Y : ℕ} (hn : 7 ≤ n) (hk : 2 ≤ k) (hkN : k ∣ (n - 1)!) :
    a n ≠ Y ^ k := by
  intro hY
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ht⟩ := hkN
  set N := (n - 1)! with hNdef
  have hdecomp := a_eq_pow_add_R (n := n) (by omega)
  have hRlt := R_lt hn
  have hR1 := one_le_R n
  rw [← hNdef] at hdecomp hRlt
  have ht' : N / (k' + 1) = t := by
    rw [ht]; exact Nat.mul_div_cancel_left _ (by omega)
  set z := 2 ^ t with hz
  have hzk : z ^ (k' + 1) = 2 ^ N := by
    rw [hz, ← pow_mul, ht]; ring_nf
  have hlt : z < Y := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have : Y ^ (k' + 1) ≤ z ^ (k' + 1) := Nat.pow_le_pow_left hcon _
    omega
  have hbern := add_one_pow_ge z k'
  have hYk : (z + 1) ^ (k' + 1) ≤ Y ^ (k' + 1) := Nat.pow_le_pow_left hlt _
  -- N / 2 ≤ t * k'
  have hk1 : 1 ≤ k' := by omega
  have hN2 : N / 2 ≤ t * k' := by
    apply Nat.div_le_of_le_mul
    rw [ht]; nlinarith [Nat.zero_le t]
  have hzpow : 2 ^ (N / 2) ≤ z ^ k' := by
    rw [hz, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) hN2
  have hmul : 2 * 2 ^ (N / 2) ≤ (k' + 1) * z ^ k' := by
    nlinarith [hzpow, hk1]
  omega

end A113258
