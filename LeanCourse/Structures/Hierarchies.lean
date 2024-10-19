import Mathlib.Data.Nat.Notation

-- Here we discuss how to build hierarchy of algebraic structures --

--This is just a class for a type containing a distinguished element one --
class One₁ (α : Type) where
  /-- The element one -/
  one : α

@[inherit_doc]
notation "𝟙" => One₁.one

instance : One₁ ℕ where
  one := 1

example : 𝟙 = 1 := by rfl

-- Next we define a binary operation --
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia

-- Suppose we want to define a semigroup that has an associative binary operation --
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

-- example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b --
/-
If you uncomment, you're going to get an error:
  failed to synthesize Dia₁ α

The problem is that we didn't tell that Semigroup also holds Dia₁,
so we need to add it
-/

/-
example {α : Type} [Dia₁ α] [Semigroup₁ α] (a b c : α) :
    a ⋄ b ⋄ c = a ⋄ (b ⋄ c) := by
  apply Semigroup₁.dia_assoc
-/

/-
If you uncomment, then the problem is that operation from
[Dia₁ α] instance and [Semigroup₁ α] are different, so we can't
unify them.

Hopefully, we can solve this mess by declaring that we synthesise
Dia₁ in Semigroup₁ as
-/

attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

example {α : Type} [Semigroup₁ α] (a b c : α) :
    a ⋄ b ⋄ c = a ⋄ (b ⋄ c) := by
  apply Semigroup₁.dia_assoc

/-
But this is still cumbersome because we need to define instance
attributes each time. Instead, use keyword `extends`
-/

class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

-- We can extend from two classes --
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- We can just extend --
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
