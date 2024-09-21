import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Notation

-- Solve exercises similar to Calc.lean --

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

/-
Informal-to-Formal

This is probably the most important skill I want you to have, to be able
formalize any informal statement you can think of. We'll start slow, but
soon you will see how scope of your abilities increases exponentially.

Plese write your formalization in the corresponding sections. You can use
whatever means necessary.
-/

/-
Formalize the following problem and prove it.

Let x, y be real numbers (ℝ) such that a - b = 5 and ab = 2. Prove that
(a + b)² = 33.
-/

section problem1

end problem1

/-
Formalize the following problem and prove it.

Let x, y be real numbers (ℝ). Solve the following system of linear equations
  x + y = 6
  2x + 4y = 20
-/

section problem2

end problem2

/-
Formalize the following problem and prove it.

Let a, b, m, n be integers (ℤ), suppose that b² = 2a² and am + bn = 2.
Show that (2an + bm)² = 8. Hint: use Brahmagupta’s identity.
-/

section problem3

end problem3
