import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

-- Monoids --

/-
There's a hierarchy Monoid M -> CommMonoid M
There's no difference between Monoid and AddMonoid except
one uses * and another + to denote binary operation. Typically,
we use Monoid and AddCommMonoid because it's unusual to denote
non-commutative operation by +
-/
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

-- Monoid morphisms are denoted as M →* N, AddMonoid as M →+ N
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

-- Morphisms are composed with AddMonoidHom.comp --
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

-- Groups --

-- Groups are monoids with inverse --
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

-- Group morphisms are the same as monoid ones --
example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

/-
Group isomorphisms are denoted as ≃*
Here we state that f ∘ f⁻¹ = id
-/
example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

-- Subgroups --

/-
Subgroup is a Submonoid with an additional hypothesis that
it's closed under inversion operation. Submonoid M is
a carrier : Set M with 1 ∈ carrier, closed under multiplication
-/
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx

-- Here's an example on how to define a concrete subgroup ℤ ⊆ ℚ --
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

-- Subgroup is a group. First we write explicitly with subtyping --
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

-- This can be coerced into --
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

-- Lattice structure is similar to Submonoid case --
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

-- G itself is not of Subgroup G type, but ⊤ element of the lattice is G as a subgroup of G --
example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

-- On the other hand, ⊥ is the trivial subgroup {1} --
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

-- Exercise: define conjugate group --
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    sorry
  inv_mem' := by
    dsimp
    sorry
  mul_mem' := by
    dsimp
    sorry

-- There are pushforward and direct image maps between subgroups --
example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

-- Kernel is a preimage of the ⊥ subgroup --
example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

-- Range is an image of the ⊤ subgroup
example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

-- Group action --

-- Use SMul for notation + axioms --
example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm

-- Morphism from group to the permutation group of X --
example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  MulAction.toPermHom G X

-- Partition X into orbits --
example {G X : Type*} [Group G] [MulAction G X] : Setoid X := MulAction.orbitRel G X

noncomputable example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

-- Exercise: define action of group on its subgroups by conjugation --
variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  sorry

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    sorry
  mul_smul := by
    sorry

-- Quotient groups --

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

noncomputable example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ
