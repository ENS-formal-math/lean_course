import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Quotient
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Basic

-- Vector spaces --

-- Let K be a field and let V be a vector space over K --
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-
We need to tell that V has both AddCommGroup and Module,
while the first can be inferred from the later. The reason
is that whenever we tell that V is [Module K V] and would
like to infer [AddCommGroup V], Lean will go over all
Module K V instances with an unspecified K.
-/

example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

-- Linear maps --

variable {W : Type*} [AddCommGroup W] [Module K W]

-- Linear map is a bundled structure of a map and axioms --
variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

variable (θ : W →ₗ[K] V)

-- Composition of LinearMaps is done with comp --
#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)

-- Linear map is defined as any structure --
example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- Notation ≃ₗ denotes linear isomorphism, ≪≫ₗ denotes a composition of equivalences --
example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm

-- Sum and product of linear spaces --
section family
open DirectSum

variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-
The universal property of the direct sum assembles maps
from the summands to build a map from the direct sum
-/
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ

/-
The universal property of the direct product assembles
maps into the factors to build a map into the direct product
-/
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

end family

-- Subspaces --

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx

-- ℝ is a ℝ-submodule of ℂ --
noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp

def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    dsimp
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    dsimp
    sorry

-- Submodule K V has a lattice structure --
example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

-- Span of a (s : Set V) is a minimal Submodule K V containing it --
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

-- One can pushforward and pullback subspaces --
variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

-- Quotient spaces --

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

variable (E : Submodule K V)

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun := fun F ↦ ⟨Submodule.comap E.mkQ F, by sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

-- Matrices --

-- Vectors are denoted as !![...] --
#eval !![1, 2] + !![3, 4]  -- !![4, 6]

-- Matrices are denoted as !![...; ...; …] --
-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

open Matrix
-- matrices acting on vectors on the left
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- matrices acting on vectors on the left, resulting in a size one matrix
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- matrices acting on vectors on the right
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]

-- Bases --

/-
Basis is a linear equivalence with a module of functions
with a finite support ι →₀ K
-/
variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)
