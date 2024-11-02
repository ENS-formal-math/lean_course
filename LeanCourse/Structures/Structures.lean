import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs

-- 1. Plain structures --

-- When we want to bundle data in a unique way, we can use structure --
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

/-
It's convenient to put all defenitions and theorems
into a namespace called as the type
-/

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

end Point

#check Point.add

-- You can define structures parameterized on something --
structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

-- Subtype is a type of object with a proof --
def PReal :=
  { y : ℝ // 0 < y }

def one : PReal := ⟨1, by norm_num⟩

-- 2. Classes --

/-
Typical algebraic structure is defined on some carrier set
(or type) and introduces additional data and some axioms that
the elements satisfy. Then it makes sense to define this in Lean
through a structure parameterized with the carrier type.
-/

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

-- Let us define an example group of equivalence maps --
def permGroup {α : Type*} : Group₁ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

/-
Additionally, we want:
1. To prove general theorems about groups
2. Use them for a particular one
3. Use notation
Lean needs a way to find notation and implicit group
structure for a particular group.
-/

/-
First part is done by changing structure -> class, that allows
to write [grp: Group₂ α] or [Group₂ α], meaning:

"Please synthesise instance of this class for type α"
or
"Let's assume that α is of this class"
-/

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

example {α : Type*} [Group₂ α] (x : α) : Group₂.mul x Group₂.one = x := Group₂.mul_one x

/-
Second part is done by defining instance of this class
for a particular type
-/

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

section

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end
