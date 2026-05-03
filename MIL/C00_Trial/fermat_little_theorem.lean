import Mathlib

/- 费马小定理：若 p 是素数且 a 是整数，则 a^p ≡ a (mod p)
   等价地，若 p ∤ a，则 a^(p-1) ≡ 1 (mod p) -/

-- 证明思路：利用 (ℤ/pℤ)* 乘法群的阶为 p-1，由拉格朗日定理得 a^(p-1) ≡ 1 (mod p)

open Nat

-- 核心引理：若 p 是素数且 p ∤ a，则 a^(p-1) ≡ 1 [MOD p]
theorem my_fermat_little_theorem {p : ℕ} (hp : Nat.Prime p) {a : ℕ} (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  have ha' : (a : ZMod p) ≠ 0 := by
    intro h0
    have : p ∣ a := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact h0
    contradiction
  have h1 : (a : ZMod p) ^ (p - 1) = 1 := by
    apply ZMod.pow_card_sub_one_eq_one
    exact ha'
  simpa using h1

-- 等价形式：a^p ≡ a [MOD p]（对所有整数 a 成立）
theorem my_fermat_little_theorem' {p : ℕ} (hp : Nat.Prime p) (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  by_cases h : p ∣ a
  · -- 若 p | a，则 a ≡ 0 [MOD p]，所以 a^p ≡ 0 ≡ a [MOD p]
    have h1 : a ≡ 0 [MOD p] := by
      exact Nat.modEq_zero_iff_dvd.mpr h
    have h2 : a ^ p ≡ 0 [MOD p] := by
      have : a ^ p % p = 0 := by
        have : p ∣ a ^ p := by
          apply dvd_pow h
          exact Nat.Prime.pos hp
        exact Nat.dvd_iff_mod_eq_zero.mp this
      exact Nat.modEq_iff_dvd.mpr (by simp [this])
    exact Nat.ModEq.trans h2 (Nat.ModEq.symm h1)
  · -- 若 p ∤ a，利用上面的定理
    have h1 : a ^ (p - 1) ≡ 1 [MOD p] := my_fermat_little_theorem hp h
    calc
      a ^ p ≡ a ^ (p - 1) * a [MOD p] := by
        rw [show p = p - 1 + 1 by omega]
        rw [pow_succ]
        rfl
      _ ≡ 1 * a [MOD p] := by
        apply Nat.ModEq.mul h1
        rfl
      _ ≡ a [MOD p] := by
        simp

-- 欧拉定理
theorem my_euler_theorem {n : ℕ} (hn : n ≠ 0) {a : ℕ} (ha : Nat.Coprime a n) :
    a ^ φ n ≡ 1 [MOD n] := by
  have h : Fact (0 < n) := ⟨Nat.zero_lt_of_ne_zero hn⟩
  rw [← ZMod.eq_iff_modEq_nat n]
  have ha' : IsUnit (a : ZMod n) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ha
  have h1 : (a : ZMod n) ^ φ n = 1 := by
    apply ZMod.pow_totient
    exact ha'
  simpa using h1

-- 费马小定理作为欧拉定理的推论
theorem my_fermat_little_theorem_euler {p : ℕ} (hp : Nat.Prime p) {a : ℕ} (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h_coprime : Nat.Coprime a p := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have h_gcd : a.gcd p = 1 := by
      have h1 : a.gcd p ∣ p := Nat.gcd_dvd_right a p
      have h2 : a.gcd p ∣ a := Nat.gcd_dvd_left a p
      have h3 : a.gcd p = 1 ∨ a.gcd p = p := by
        have h4 : Nat.Prime (a.gcd p) ∨ a.gcd p = 1 := by
          apply (Nat.dvd_prime hp).mp h1
        cases h4 with
        | inl h5 =>
          have : a.gcd p = p := by
            exact Nat.Prime.eq_of_dvd_of_prime hp h5 h1
          exact Or.inr this
        | inr h5 => exact Or.inl h5
      cases h3 with
      | inl h => exact h
      | inr h =>
        have : p ∣ a := by
          rw [← h]
          exact h2
        contradiction
    exact h_gcd
  have h_phi : φ p = p - 1 := by
    exact Nat.totient_prime hp
  rw [← h_phi]
  apply my_euler_theorem (by linarith [Nat.Prime.pos hp]) h_coprime
