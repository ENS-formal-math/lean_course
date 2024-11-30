import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
Finset is a Multiset without any duplicates.
Multiset is a List that is (noncomputably) quotiened by
the order of the elements.
-/
#check Finset

-- Finset can be created manually --
def A := ({1, 2, 3, 4} : Finset ℕ)
#eval A

-- You can sum/product all elements in the Finset --
#eval Finset.sum A id

-- Cardinality --
#eval A.card

example : Finset.sum A id = 10 := by
  rfl

example : Finset.sum (Finset.range 10) id = 45 := by
  native_decide

-- Finset can be mapped into another Finset via embeddings (function + proof of injectivity) --
def B := Finset.map ⟨fun x ↦ x^2, Nat.pow_left_injective (by norm_num)⟩ A
#eval B

-- Finset can be filtered by some (decidable) predicate --
def C := Finset.filter (fun x ↦ x ≤ 10) B
#eval C

-- It's often useful to attach information to the element that it's a member of the set --
def D := Finset.attach C
#eval D
