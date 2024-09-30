import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

/-
Theorems can be used with tactic `exact` and `apply`. Tactic `exact`
requires exact match of theorem premise with the goal. Tactic `apply`
tries to find match, and if there're any additional hypotheses needed to be proven,
it adds them as goals.

Consider axioms of total order for ℝ
-/

variable (a b c : ℝ)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

-- We can prove the following example in different ways --

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀ h₁

-- Tactic `linarith` can solve linear arithmetic goals --

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b :=
  calc
    _ ≤ 2 * a + a := by
      sorry
    _ ≤ 3 * a := by
      sorry
    _ ≤ 5 * b := by
      sorry

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

-- You can subsitute theorems into `linarith` --

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + Real.exp b ≤ 3 * a + Real.exp c := by
  have h := Real.exp_le_exp.mpr h'
  linarith [h]

/-
There are a number of strategies you can use to find theorems:
1. You can browse Mathlib in its GitHub repository.

2. You can use the API documentation on the Mathlib web pages.
(https://leanprover-community.github.io/mathlib4_docs/)

3. You can rely on Mathlib naming conventions and Ctrl-space completion
in the editor to guess a theorem name (or Cmd-space on a Mac keyboard).
In Lean, a theorem named A_of_B_of_C establishes something of the
form A from hypotheses of the form B and C, where A, B, and C approximate
the way we might read the goals out loud. So a theorem establishing
something like x + y ≤ ... will probably start with add_le.
Typing add_le and hitting Ctrl-space will give you some helpful choices.
Note that hitting Ctrl-space twice displays more information about
the available completions.

4. If you right-click on an existing theorem name in VS Code,
the editor will show a menu with the option to jump to the file
where the theorem is defined, and you can find similar theorems nearby.

5. You can use the apply? tactic, which tries to find the relevant
theorem in the library.
-/

/-
Implicit arguments are introduced with {}, with careful design they can
ease using theorems
-/

theorem add_left_cancel_implicit {a b c : ℝ} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  rw [neg_add_cancel_left, neg_add_cancel_left] at this
  exact this

example (a b : ℝ) (h : 1 + a = 1 + b) : a = b := by
  apply add_left_cancel_implicit h

/-
Lean infers implicit arguments from the hypothesis, when all arguments are
present in hypotheses, you can make them implicit. You can always use full
statement with all arguments made explicit by appending @ to theorem's name.
-/

example (a b : ℝ) (h : 1 + a = 1 + b) : a = b := by
  -- apply @add_left_cancel_implicit h : type error, now it expects a b c first --
  apply @add_left_cancel_implicit 1 a b h
  -- You can make `apply` tactic to try infering arguments with underscore --
  -- apply @add_left_cancel_implicit _ _ _ h --
