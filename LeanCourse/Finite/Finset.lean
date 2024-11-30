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

-- Finset can be mapped into another Finset via embeddings (function + proof of injectivity) --
def B := Finset.map ⟨fun x ↦ x^2, Nat.pow_left_injective (by norm_num)⟩ A
#eval B

-- You can sum/product all elements in the Finset --
