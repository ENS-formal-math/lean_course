import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Units
import Mathlib.Tactic

-- Rings --

-- Ring is a class of rings, CommRing is Ring with commutative multiplication --
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

-- Tactic `ring` can also prove identities about CommSemiring --
example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

-- Every multiplicative monoid has a predicate checking if element is a unit --
#check IsUnit

/-
Underhood, it checks if you can coerce type Units into the element.
Structure Units consists of element, its inverse and hypotheses
that they're left/right inverses. Notation is (x : Mˣ)
-/
#check Units

example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

-- Ring homomorphism is denoted as →+* --
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f

-- Ideals --

/-
Ideal is a Submodule of Module R R. Submodule is AddSubmonoid + SubMulAction.
AddSubmonoid is carrier set and hypothesis that 0 is in the set
SubMulAction is carrier set and hypothesis that it's closed under multiplication
-/
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H
