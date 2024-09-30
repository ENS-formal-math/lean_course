import Mathlib.Tactic
import Mathlib.Data.Nat.Notation

-- Exercises on logic --

example (P : Prop) : ¬(P ∧ ¬ P) := by sorry

example (P Q R : Prop) (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by sorry

-- one of De Morgan's laws --
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by sorry

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by sorry

example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by sorry

-- Here you need law of excluded middle or `by_contra` tactic --
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by sorry

-- Here also, another of De Morgan's laws --
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by sorry

/-
Informal problems

Formalize the following problems and prove them.
-/

/-
Show that there doesn't exist a natural number (n : ℕ) such that n² = 2.

Hint: you can split as in last example from Logic.lean
on `le_or_succ_le` or `le_or_gt` theorems
-/

section problem1

end problem1

/-
Show that 5 is not even.
-/

section problem2

end problem2
