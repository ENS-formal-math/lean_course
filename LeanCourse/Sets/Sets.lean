import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Associated.Basic

-- For any type α, Set α is a type of sets consisting of elements of type α --
#check Set ℕ

-- It's defined as `def Set (α : Type u) := α → Prop` --
#check ((fun x => Even x) : Set ℕ)

def Set_ours (α : Type u) := α → Prop

-- Membership of element x is simply application of set's predicate to this element --
def Mem_ours (s : Set_ours α) (a : α) : Prop := s a

example : Mem_ours (fun x => Even x) 2 := by
  unfold Mem_ours
  dsimp
  use 1

-- There's a typical notation x ∈ s, s ∩ t, s ∪ t, s \ t --
variable {α : Type*}
variable (s t u : Set α)
open Set

#check Set.Subset

-- For example, view ⊆ in Set.Subset and ∩ in Set.inter --
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  -- goal : ∀ x, x ∈ s ∩ u → x ∈ t ∩ u --
  -- h : ∀ x, x ∈ s → x ∈ t --
  intro x
  intro hx
  simp at hx -- x ∈ s ∩ u is the same as x ∈ s ∧ x ∈ u --
  simp
  exact ⟨h hx.1, hx.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

-- x ∈ s ∪ t expands to x ∈ s ∨ x ∈ t, x ∈ s \ t expands to x ∈ s ∧ x ∉ t --
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

-- Exercise --
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

/-
To prove that two sets A, B are equal, use tactic `ext`, which stands for
extensionality and then prove that x ∈ A ↔ x ∈ B
-/
example : s ∩ t = t ∩ s := by
  ext x
  exact ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

-- Alternatively, you can use `Subset.antisymm` --
#check Subset.antisymm

-- There's a set builder notation --
def evens : Set ℕ := { n | Even n }

def odds : Set ℕ := { n | Odd n }

-- { x | P x } is equivalent to (fun x ↦ P x) --

-- univ is the set of all elements of this type --
-- univ := {x | True} and ∅ := {x | False} --
example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp[← Nat.not_even_iff_odd]
  apply Classical.em

-- Bounded quantifier ∀ x ∈ s, ... means ∀ x, x ∈ s → ... --
variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

-- Indexed union / intersection --
-- We can index sets Aᵢ with members of other type i : I --

variable {α I : Type*}
variable (A : I → Set α)
variable (s : Set α)

example : (s ∩ (⋃ i, A i)) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩
