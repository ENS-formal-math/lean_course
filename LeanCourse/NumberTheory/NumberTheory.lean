import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Associated.Basic
import Mathlib.Tactic

open Nat

#print Nat.Coprime

#print Nat.factors

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have two_dvd_m : 2 ∣ m := by
    have := Nat.dvd_mul_right 2 (n ^ 2)
    rw [← sqr_eq, Nat.pow_two] at this
    rw [Nat.prime_two.dvd_mul] at this
    cases this <;> assumption
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp two_dvd_m
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    rw [Nat.mul_right_inj (by norm_num : 2 ≠ 0)] at this
    assumption
  have two_dvd_n : 2 ∣ n := by
    have this' := Nat.dvd_mul_right 2 (k ^ 2)
    rw [this, Nat.pow_two] at this'
    rw [Nat.prime_two.dvd_mul] at this'
    cases this' <;> assumption
  have : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd two_dvd_m two_dvd_n
  have : 2 ∣ 1 := by
    rw [coprime_mn] at this
    assumption
  norm_num at this
