import A113258.CertCore

/-!
# Certificate checker (executable) and its soundness theorem

`tableOK tbl = true` and `coverOK tbl L = true` imply: for every prime `ℓ` with `7 ≤ ℓ ≤ L`
and every `7 ≤ n ≤ ℓ`, `a n` is not an `ℓ`-th power.
-/

namespace A113258

open Nat

lemma isPrimeAux_sound {n : ℕ} : ∀ fuel d, isPrimeAux n fuel d = true →
    ∀ e, d ≤ e → e < d + fuel → e * e ≤ n → n % e ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro d _ e h1 h2; omega
  | succ fuel ih =>
    intro d h e hde hef hen
    simp only [isPrimeAux] at h
    by_cases hdd : d * d ≤ n
    · rw [if_pos hdd] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hde with rfl | hlt
      · exact h.1
      · exact ih (d + 1) h.2 e hlt (by omega) hen
    · exfalso
      have := Nat.mul_le_mul hde hde
      omega

lemma isPrimeAux_complete {n : ℕ} : ∀ fuel d,
    (∀ e, d ≤ e → e < d + fuel → e * e ≤ n → n % e ≠ 0) → isPrimeAux n fuel d = true := by
  intro fuel
  induction fuel with
  | zero => intro d _; simp [isPrimeAux]
  | succ fuel ih =>
    intro d h
    simp only [isPrimeAux]
    by_cases hdd : d * d ≤ n
    · rw [if_pos hdd]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨h d le_rfl (by omega) hdd,
        ih (d + 1) (fun e he1 he2 he3 => h e (by omega) (by omega) he3)⟩
    · rw [if_neg hdd]

lemma isPrimeB_sound {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hp⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, ?_⟩
  intro m hm hms hdvd
  have hmm : m * m ≤ n := Nat.le_sqrt.1 hms
  have hmn : m < 2 + n := by nlinarith
  exact isPrimeAux_sound n 2 hp m hm hmn hmm (Nat.mod_eq_zero_of_dvd hdvd)

lemma isPrimeB_complete {n : ℕ} (h : n.Prime) : isPrimeB n = true := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h.two_le, isPrimeAux_complete _ _ ?_⟩
  intro e he1 _ he3 hmod
  have hdvd : e ∣ n := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.dvd_prime h).1 hdvd with rfl | rfl
  · omega
  · have := h.two_le
    nlinarith

lemma pow_mod_card_sub_one {q : ℕ} [Fact q.Prime] {x : ZMod q} (hx : x ≠ 0) (e : ℕ) :
    x ^ (e % (q - 1)) = x ^ e := by
  conv_rhs => rw [← Nat.div_add_mod e (q - 1), pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx,
    one_pow, one_mul]

lemma factorial_cast_ne_zero {q : ℕ} [hq : Fact q.Prime] {j : ℕ} (hj : j < q) :
    ((j ! : ℕ) : ZMod q) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := (Nat.Prime.dvd_factorial hq.out).1 h
  omega

lemma aModAux_cast {q : ℕ} [Fact q.Prime] {ell n : ℕ} (hnl : n ≤ ell) (hq : ell < q)
    {F E : Array ℕ} (hF : ∀ j ≤ ell, F[j]! = j ! % q) (hE : ∀ k ≤ ell, E[k]! = k ! % (q - 1)) :
    ∀ m, m ≤ n →
      ((aModAux q n F E m : ℕ) : ZMod q) = ∑ j ∈ Finset.Icc 1 m, ((j ! : ℕ) : ZMod q) ^ (n - j + 1)! := by
  intro m
  induction m with
  | zero => intro _; simp [aModAux]
  | succ m ih =>
    intro hm
    rw [Finset.sum_Icc_succ_top (by omega), ← ih (by omega)]
    simp only [aModAux, ZMod.natCast_mod, Nat.cast_add]
    congr 1
    rw [powMod_eq, ZMod.natCast_mod, Nat.cast_pow, hF (m + 1) (by omega),
      hE (n - (m + 1) + 1) (by omega), ZMod.natCast_mod, 
      pow_mod_card_sub_one (factorial_cast_ne_zero (by omega)) _]

lemma qOK_sound {ell q : ℕ} {ns : List ℕ} (hell : 2 ≤ ell) (h : qOK ell q ns = true) :
    ∀ n ∈ ns, n ≤ ell ∧ ¬ ∃ Y : ℕ, a n = Y ^ ell := by
  intro n hn
  simp only [qOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hqpB, hqmod⟩, hall⟩ := h
  have hqp := isPrimeB_sound hqpB
  have h1 := hall n hn
  obtain ⟨hnl, hpair⟩ := h1
  refine ⟨hnl, ?_⟩
  haveI : Fact q.Prime := ⟨hqp⟩
  have hq2 : 2 ≤ q := hqp.two_le
  have hdm := Nat.div_add_mod q ell
  obtain ⟨d, hd⟩ : ∃ d, q / ell = d := ⟨_, rfl⟩
  rw [hd] at hdm
  have hqdiv : 1 ≤ d := by
    by_contra hc
    have h0 : d = 0 := by omega
    rw [h0] at hdm
    omega
  have hlt : ell < q := by
    have : ell * 1 ≤ ell * d := Nat.mul_le_mul_left _ hqdiv
    omega
  have hq1 : q - 1 = ell * (q / ell) := by rw [hd]; omega
  set F := factTable q ell with hFdef
  set E := factTable (q - 1) ell with hEdef
  have hF : ∀ j ≤ ell, F[j]! = j ! % q := fun j hj => factTable_get q ell j hj
  have hE : ∀ k ≤ ell, E[k]! = k ! % (q - 1) := fun k hk => factTable_get (q - 1) ell k hk
  simp only [pairOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hpair
  obtain ⟨hA, hB⟩ := hpair
  rintro ⟨Y, hY⟩
  set A := aModAux q n F E n with hAdef
  have hcast : ((A : ℕ) : ZMod q) = ((Y : ℕ) : ZMod q) ^ ell := by
    have := aModAux_cast hnl hlt hF hE n le_rfl
    rw [← hAdef] at this
    rw [this, ← Nat.cast_pow, ← hY, a_eq_Icc]
    push_cast
    simp only [term, Nat.cast_pow]
  have hA0 : ((A : ℕ) : ZMod q) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact hA (Nat.mod_eq_zero_of_dvd h0)
  have hY0 : ((Y : ℕ) : ZMod q) ≠ 0 := by
    intro hy
    rw [hy, zero_pow (by omega)] at hcast
    exact hA0 hcast
  have hone : ((A : ℕ) : ZMod q) ^ ((q - 1) / ell) = 1 := by
    rw [hcast, ← pow_mul, hq1, Nat.mul_div_cancel_left _ (by omega), ← hq1]
    exact ZMod.pow_card_sub_one_eq_one hY0
  apply hB
  rw [powMod_eq]
  have h2 : ((A ^ ((q - 1) / ell) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    push_cast
    exact hone
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2
  rw [this]
  exact Nat.mod_eq_of_lt (by omega)

lemma entryOK_sound {ell q1 : ℕ} {exc : List (ℕ × List ℕ)} (h : entryOK ell q1 exc = true) :
    ell.Prime ∧ 7 ≤ ell ∧ ∀ n, 7 ≤ n → n ≤ ell → ¬ ∃ Y : ℕ, a n = Y ^ ell := by
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h7, hp⟩, hq1⟩, hexc⟩ := h
  have hp' := isPrimeB_sound hp
  refine ⟨hp', h7, ?_⟩
  intro n hn7 hnl
  by_cases hex : ∃ p ∈ exc, n ∈ p.2
  · obtain ⟨p, hp', hnp⟩ := hex
    exact (qOK_sound (by omega) (hexc p hp') n hnp).2
  · push Not at hex
    have hmem : n ∈ (List.range' 7 (ell - 6)).filter
        fun n => !(exc.any fun p => p.2.contains n) := by
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [List.mem_range'_1]; omega
      · have hfalse : (exc.any fun p => p.2.contains n) = false := by
          rw [List.any_eq_false]
          intro p hp'
          simpa using hex p hp'
        show (!(exc.any fun p => p.2.contains n)) = true
        rw [hfalse]; rfl
    exact (qOK_sound (by omega) hq1 n hmem).2

theorem table_sound {tbl : List (ℕ × ℕ × List (ℕ × List ℕ))} {L : ℕ}
    (h1 : tableOK tbl = true) (h2 : coverOK tbl L = true) :
    ∀ ell n : ℕ, ell.Prime → 7 ≤ n → n ≤ ell → ell ≤ L → ¬ ∃ Y : ℕ, a n = Y ^ ell := by
  intro ell n hp hn7 hnl hL
  have hcov := (List.all_eq_true.1 h2) ell (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_true, beq_iff_eq] at hcov
  rcases hcov with hbad | ⟨e, he, hee⟩
  · rcases hbad with hbad | hbad
    · omega
    · rw [isPrimeB_complete hp] at hbad
      exact absurd hbad (by decide)
  · have := entryOK_sound ((List.all_eq_true.1 h1) e he)
    rw [hee] at this
    exact this.2.2 n hn7 hnl

end A113258
