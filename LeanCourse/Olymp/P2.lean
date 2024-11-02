import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Digits
import Mathlib.NumberTheory.Divisors

/-
Problem 4:
Find the three-digit number n such that writing any other
three-digit number 10^2024 times in a row and 10^2024+2 times
in a row results in two numbers divisible by n.

Answer: 143
-/
def repeat_number (a M : ℕ) := Nat.ofDigits 10 (List.join (List.replicate M (Nat.digits 10 a)))

def three_digit (a : ℕ) := (Nat.digits 10 a).length = 3

def M_def := 10^1024

def sat_problem (n : ℕ) (_ : three_digit n) :=
  ∀ a, three_digit a → n ∣ repeat_number a M_def ∧ n ∣ repeat_number a (M_def + 2)

/-
Let `M = 10^1024`. Let `a` be any three-digit number. Writing
`M` copies of `a` in a row results in a number `X` where
    `X = a × 100100100…1001001`
and there are `M` copies of the digit one in the long number.
-/
def repeat_mul (digit_num M : ℕ) :=
  match M with
  | 0 => 0
  | Nat.succ M' =>
    let part := List.replicate digit_num.pred 0 ++ [1]
    Nat.ofDigits 10 ([1] ++ List.join (List.replicate M' part))

theorem repeat_rewrite (a M : ℕ) : repeat_number a M = a * repeat_mul (Nat.digits 10 a).length M := by
  induction M with
  | zero =>
    unfold repeat_number repeat_mul; simp
  | succ M' ih =>
    unfold repeat_number repeat_mul; simp
    unfold repeat_number repeat_mul at ih
    rw [List.replicate_succ, List.join_cons, Nat.ofDigits_append]
    cases M' with
    | zero => simp; apply Nat.ofDigits_digits
    | succ M'' =>
      simp at ih; nth_rw 2 [List.replicate_succ]
      simp; rw [← List.cons_append, Nat.ofDigits_append]
      simp; rw [Nat.ofDigits_digits, mul_add, ← mul_assoc]
      nth_rw 2 [mul_comm a]
      rw [mul_assoc, Nat.ofDigits_cons]
      have (n : ℕ): Nat.ofDigits 10 (List.replicate n 0) = 0 := by
        induction n with
        | zero => simp
        | succ n' ih =>
          rw [List.replicate_succ, Nat.ofDigits_cons, ih]
      rw [this]; simp; rw [← ih]
      cases a with
      | zero => simp
      | succ a' =>
        have : (Nat.digits 10 a'.succ).length ≠ 0 := by
          rw [Nat.digits_len _ _ (by linarith) (by linarith)]
          exact Ne.symm (Nat.zero_ne_add_one (Nat.log 10 a'.succ))
        rw [Nat.sub_one_add_one this]

/-
If instead we wrote `M + 2` copies of `a` in a row, the resulting
number would be `10^6 X + 1001 a`.
-/
lemma l1 (a M : ℕ) (h : three_digit a): repeat_number a (M + 2) = 10^6 * repeat_number a M + 1001 * a := by
  rw [repeat_rewrite, repeat_rewrite, repeat_mul, h]
  cases M with
  | zero =>
    unfold repeat_mul; simp
    have : Nat.digits 10 1001 = [1, 0, 0, 1] := by simp
    rw [← this, Nat.ofDigits_digits, mul_comm]
  | succ M' =>
    rw [repeat_mul, Nat.ofDigits_append]
    have : Nat.digits 10 100 = [0, 0, 1] := by simp
    rw [List.replicate_succ, List.join_cons, Nat.ofDigits_append]; simp
    nth_rw 1 [← this, Nat.ofDigits_digits]
    rw [List.replicate_succ, List.join_cons, Nat.ofDigits_append]; simp
    nth_rw 1 [← this, Nat.ofDigits_digits]
    rw [Nat.ofDigits_cons]; ring

/-
We use the notation `(u, v)` to denote the greatest common
divisor of two integers `u` and `v` which are not both 0.
We apply Euclid's algorithm so
    `(10^6 X + 1001 a, X) = (1001 a, X)`
-/
lemma l2 (a M : ℕ) (h : three_digit a) :
    Nat.gcd (repeat_number a (M + 2)) (repeat_number a M) = Nat.gcd (1001 * a) (repeat_number a M) := by
  rw [l1, Nat.gcd_mul_right_add_left]
  exact h

/-
It is therefore a necessary condition that our three-digit
number `n` should divide `(1001 a, X)` for all three-digit
numbers `a`. By considering `a = 100` and `a = 101`.
-/
lemma l3 (n a : ℕ) (hn : three_digit n) (ha : three_digit a) (hs : sat_problem n hn) :
    n ∣ Nat.gcd (1001 * a) (repeat_number a M_def) := by
  unfold sat_problem at hs
  specialize hs a ha
  rw [←l2, Nat.dvd_gcd_iff]
  exact ⟨hs.2, hs.1⟩
  repeat exact ha

/-
By considering `a = 100` and `a = 101`, we see that any
candidate for `n` must divide `1001 × 101 - 1001 × 100 = 1001`.
-/
lemma l4 (n : ℕ) (hn : three_digit n) (hs : sat_problem n hn) :
    n ∣ 1001 := by
  have h100 := l3 n 100 hn (by rw [three_digit]; simp) hs
  rw [Nat.dvd_gcd_iff] at h100
  have h101 := l3 n 101 hn (by rw [three_digit]; simp) hs
  rw [Nat.dvd_gcd_iff] at h101
  have := Nat.dvd_sub (by norm_num) h101.1 h100.1
  simp at this; exact this

/-
Moreover, if `n` is a divisor of `1001`, then `n` will divide `X`
because `1001` divides `10010010010…01001001` which is
    `1001 × 10000010000010…01000001`
The second factor involves `M / 2` copies of the digit one.
-/
theorem repeat_factor (M : ℕ) : repeat_mul 3 (2 * M) = 1001 * repeat_mul 6 M := by
  induction M with
  | zero => unfold repeat_mul; simp
  | succ M' ih =>
    have (n : ℕ) : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    unfold repeat_mul; rw [this]
    simp; rw [List.replicate_succ]; simp
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp; cases M' with
    | zero => simp
    | succ M'' =>
      rw [this] at ih; unfold repeat_mul at ih; simp at ih
      rw [this, List.replicate_succ]
      rw [(by simp : 1 :: ([0, 0, 1] :: List.replicate (2 * M'' + 1) [0, 0, 1]).join = [1, 0, 0] ++ 1 :: (List.replicate (2 * M'' + 1) [0, 0, 1]).join)]
      rw [Nat.ofDigits_append, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_nil]
      simp; rw [ih, List.replicate_succ]
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons, List.join_cons, Nat.ofDigits_append]
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_nil]
      simp; ring

lemma l5 (n a : ℕ) (hn : n ∣ 1001) (ha : three_digit a) : n ∣ repeat_number a M_def := by
  rw [repeat_rewrite]
  apply dvd_mul_of_dvd_right
  have : M_def = 2 * (5 * 10^1023) := by rw [M_def]; norm_num
  unfold three_digit at ha; rw [ha, this, repeat_factor]
  apply dvd_mul_of_dvd_left hn

/-
Such an `n` will also divide `10^6 X + 1001 a`.
-/
lemma l6 (n a : ℕ) (hn : n ∣ 1001) (ha : three_digit a) : n ∣ repeat_number a (M_def + 2) := by
  rw [l1 _ _ ha]
  apply dvd_add
  . apply dvd_mul_of_dvd_right
    apply l5 _ _ hn ha
  . apply dvd_mul_of_dvd_left hn

/-
Thus it is a necessary and sufficient condition for `n`
to satisfy the conditions of the problem that `n` be
a three-digit divisor of `1001 (= 7 × 11 × 13)`. There is
a unique such number: `143`.
-/
lemma l7 (n : ℕ) (hn : three_digit n) : sat_problem n hn ↔ n ∣ 1001 := by
  constructor
  . intro hs; exact l4 n hn hs
  . intro hdiv; unfold sat_problem; intro a ha
    exact ⟨l5 n a hdiv ha, l6 n a hdiv ha⟩

theorem Problem4 (n : ℕ) (hn : three_digit n) : sat_problem n hn ↔ n = 143 := by
  rw [l7]
  constructor
  . intro hdiv
    set div := List.filter (fun x ↦ x ∣ 1001) (List.range 1002)
    set_option maxRecDepth 3000 in have div_simp : div = [1, 7, 11, 13, 77, 91, 143, 1001] := by unfold_let div; rfl
    have div_mem : n ∈ div := by
      unfold_let div; simp
      constructor
      . apply Nat.lt_succ_of_le
        exact Nat.le_of_dvd (by linarith) hdiv
      . exact hdiv
    set div' := List.filter (fun x ↦ (Nat.digits 10 x).length = 3) div with div_def'
    have div_simp' : div' = [143] := by
      rw [div_simp] at div_def'
      simp at div_def'; exact div_def'
    have div_mem' : n ∈ div' := by
      rw [div_def']; simp; exact ⟨div_mem, hn⟩
    rw [div_simp', List.mem_singleton] at div_mem'
    exact div_mem'
  . intro hn; rw [hn]; norm_num
