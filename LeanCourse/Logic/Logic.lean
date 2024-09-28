import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Implication --

example (a : ℝ) : a ≥ 1 → a ≥ 0 := by
  intro h
  linarith

-- Universal quantifier --

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

-- Existential quantifier --

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  -- `norm_num` can normalize numeric expressions and prove simple goals --
  norm_num

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

variable {f g : ℝ → ℝ}

-- There are multiple ways of working with existential hypotheses --

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  -- Tactic `rcases` can unpack ∃, ∧, ∨ statements, we will see it later --
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  -- Tactic `obtain` is like `rcases` but can work with proof terms --
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  -- Tactic `cases` does pattern matching, but you need to write out constructors --
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  -- Match is a keyword for pattern matching --
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

-- You can use match inside proof mode, compare with --
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

-- Negation --
/-
Negated statement h : ¬P is just h : P → False. False is a special type without
a constructor, so you can't create x : False, that would be absurd.
-/

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

/-
In the third one, we need a tactic from classical logic `by_contra`. It allows
to prove goal P by assuming ¬P and deriving a contradiction.
-/
