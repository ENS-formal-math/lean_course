import Mathlib.Algebra.Group.Defs

instance {I: Type*} {β : I → Type*}
    [∀ i, Monoid (β i)] : Monoid ((i : I) → β i) where
  mul f g := fun i ↦ (f i) * (g i)
  one := fun i ↦ 1
  one_mul f := by ext i; apply one_mul
  mul_one f := by ext i; apply mul_one
  mul_assoc := by intro f g h; ext i; apply mul_assoc
