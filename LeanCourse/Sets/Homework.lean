import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

-- Prove set identities --

variable {α I : Type*}
variable (A : I → Set α)
variable (s t : Set α)

example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

-- you need classical logic here --
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

/-
Informal problems

Formalize the following problems and prove them.
-/

-- Show that {x : ℤ | x is odd} = {a : ℤ | ∃ k, a = 2k - 1} --
section problem1

end problem1

-- Prove that {x : ℝ | x² - x - 2 = 0} = {-1, 2} --
section problem2

end problem2
