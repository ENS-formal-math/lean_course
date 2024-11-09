import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs
import Mathlib.Algebra.Ring.Int
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Tactic

-- Here we discuss how to build hierarchy of algebraic structures --

--This is just a class for a type containing a distinguished element one --
class One₁ (α : Type) where
  /-- The element one -/
  one : α

@[inherit_doc]
notation "𝟙" => One₁.one

example (α : Type) [One₁ α] : (One₁.one : α) = 𝟙 := by rfl

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

class Monoid₂ (α : Type) [Semigroup₁ α] extends DiaOneClass₁ α

class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

export AddSemigroup₃ (add_assoc₃)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

export Semigroup₃ (mul_assoc₃)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/- Prove this! -/
instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    sorry }

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

-- Now we discuss how to define classes with multiple types --

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul

-- Define module over a ring --
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

/-
class Module₂ (R : Type) [Ring R] (M : Type) extends SMul₃ R M, AddCommGroup M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

Note that if we uncomment block above, we will get an error. The problem is that
AddCommGroup M instance is going to be part of Module₂ R M instance and we won't
be able to infer type R from AddCommGroup M.

The rule is to extend from classes that have all type parameters like SMul₃ R M
-/

-- Let's define an instances of the module - ring over itself --
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

-- Another instance is an abelian group over ℤ --

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

-- The problem is that now Module₁ ℤ ℤ is ambiguous --
#synth Module₁ ℤ ℤ

/-
The solution is to define data needed to define Module₁ ℤ A
inside AddMonoid A from the start

General rule: when going from rich (Module R M)
to poor structure (Module ℤ M) never define, but forget
-/

#check AddMonoid

#synth Module ℤ ℤ

variable (R: Type) [Ring R]
#synth Module R R

class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

-- Morphisms --
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

-- morphism = bundled function + axioms
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- Coercion --
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun

example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one

-- Define Ring morphism --

@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

/-
When there are several monoid-like morphisms (monoids, rings),
we would like to have same lemmas for them

The way is to define abstract MonoidHomClass
-/
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

/-
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun

bad coercion instance : Lean needs to simultaneously infer F M N, while
M and N can be clearly extracted from F
-/

class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

-- Now we can apply abstract lemma --
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

-- Substructure --

@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext

/-
Since N is SetLike, there's a coercion and (x : N) means
the subtype {x : M // x ∈ N}. The same happens for any Set M,
it's not unique to Submonoid M only.
-/
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property

-- Let's equip the submonoid with monoid class instance --
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  /-
  We can prove that m₁ := x * (y * z) and m₂ := (x * y) * z in M
  Thus, these elements are equal in N also because proofs are definitionally equal
  m₁ = m₂ → ⟨m₁, p m₁⟩ = ⟨m₂, p m₂⟩
  -/
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)

/-
To apply lemmas about submonoids to subgroups we introduce
abstract class just like for monoid morphism and state
lemmas for it
-/
class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

/-
Submonoids have a lattice structure: intersection as ⊓
and closure of a union as ⊔
-/
instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

-- Quotient --

/- Setoid is just a relation and a proof that it's an equivalence -/
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z ⟨a, ha, b, hb, h⟩ ⟨a', ha', b', hb', h'⟩
      use a * a', Submonoid.mul_mem N ha ha'
      use b * b', Submonoid.mul_mem N hb hb'
      rw [← mul_assoc, h, mul_assoc, mul_comm b, ← mul_assoc, h', mul_assoc, mul_comm b']
  }

-- Allows to write M ⧸ (N : Submonoid M) --
instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      -- introduce hypotheses that a ≃ a' and b ≃ b' defined at N.Setoid.r --
      intro a a' ⟨wa, hwa, za, hza, ha⟩
      intro b b' ⟨wb, hwb, zb, hzb, hb⟩
      simp
      -- now we prove that a * b ≃ a' * b' --
      use wa * wb, Submonoid.mul_mem N hwa hwb
      use za * zb, Submonoid.mul_mem N hza hzb
      rw [← mul_assoc, mul_comm _ wa, ← mul_assoc, mul_comm wa, ha]
      rw [mul_assoc, hb, ← mul_assoc, mul_assoc a', mul_comm za, ← mul_assoc, ← mul_assoc]
  )
  mul_assoc := by
      sorry
  one := QuotientMonoid.mk N 1
  one_mul := by
      sorry
  mul_one := by
      sorry
