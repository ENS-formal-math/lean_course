import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm, mul_comm c b]
  rw [← mul_assoc, ← mul_assoc, mul_comm b a]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [mul_comm] at hyp'
  rw [← hyp'] at hyp
  rw [hyp]
  exact sub_eq_zero_of_eq rfl

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      ring
    _ = a * a + (b * a + a * b) + b * b := by
      ring
    _ = a * a + 2 * (a * b) + b * b := by
      ring

end

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  ring

section

variable (a b c : ℝ)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

end
