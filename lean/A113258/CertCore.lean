import A113258.Elementary
import A113258Check.Checker

/-!
# Modular certificates: executable checker and its soundness proof

For a prime `ℓ` and `n ≤ ℓ`, a certificate is a prime `q ≡ 1 (mod ℓ)` such that
`A := a(n) mod q` is nonzero and `A^((q-1)/ℓ) ≢ 1 (mod q)`.  Then `a(n)` is not an `ℓ`-th power.
The checker computes `a(n) mod q` by `∑_{j=1}^n (j! mod q)^((n-j+1)! mod (q-1)) mod q`.
-/

namespace A113258

open Nat

/-! ### Modular exponentiation -/

lemma powModAux_modEq (m : ℕ) : ∀ (fuel b e acc : ℕ), e ≤ fuel →
    powModAux m fuel b e acc ≡ acc * b ^ e [MOD m] := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by omega
    subst this
    simp [powModAux]
    exact Nat.ModEq.refl _
  | succ fuel ih =>
    intro b e acc he
    by_cases h0 : e = 0
    · subst h0
      simp [powModAux]
      exact Nat.ModEq.refl _
    · simp only [powModAux, h0, ite_false]
      have he2 : e / 2 ≤ fuel := by omega
      have hih := ih (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc) he2
      refine hih.trans ?_
      have hb : (b * b % m) ≡ b * b [MOD m] := Nat.mod_modEq _ _
      have hpow : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] := hb.pow _
      obtain ⟨k, hk⟩ : ∃ k, e / 2 = k := ⟨_, rfl⟩
      rw [hk] at hpow ⊢
      by_cases hodd : e % 2 = 1
      · simp only [hodd, ite_true]
        have hacc : acc * b % m ≡ acc * b [MOD m] := Nat.mod_modEq _ _
        have hek : e = 2 * k + 1 := by omega
        have : acc * b * (b * b) ^ k = acc * b ^ e := by
          rw [hek, pow_succ, pow_mul]; ring
        exact (hacc.mul hpow).trans (this ▸ Nat.ModEq.refl _)
      · have hek : e = 2 * k := by omega
        simp only [hodd, ite_false]
        have : acc * (b * b) ^ k = acc * b ^ e := by
          rw [hek, pow_mul]; ring
        exact (Nat.ModEq.refl acc |>.mul hpow).trans (this ▸ Nat.ModEq.refl _)

lemma powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  have h := powModAux_modEq m (e + 1) b e 1 (by omega)
  unfold powMod
  have : powModAux m (e + 1) b e 1 % m = 1 * b ^ e % m := h
  rw [this, one_mul]

/-! ### Factorial tables -/

lemma factTable_size (M k : ℕ) : (factTable M k).size = k + 1 := by
  induction k with
  | zero => simp [factTable]
  | succ k ih => simp [factTable, ih]

lemma factTable_get (M : ℕ) : ∀ k i, i ≤ k → (factTable M k)[i]! = i ! % M := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst this
    simp [factTable]
  | succ k ih =>
    intro i hi
    simp only [factTable, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_push, factTable_size]
    by_cases hik : i = k + 1
    · subst hik
      simp only [ite_true, Option.getD_some]
      have hk := ih k le_rfl
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hk
      rw [hk, Nat.factorial_succ]
      rw [Nat.mul_comm (k + 1), Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    · have hik' : i ≤ k := by omega
      simp only [hik, ite_false]
      have hk := ih i hik'
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hk
      exact hk

end A113258
