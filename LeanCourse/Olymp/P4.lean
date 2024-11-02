import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

/-
Problem: Let \( S = \{1, 2, \cdots, 100\} \). If a three-element
subset \( A = \{a, b, c\} \) of \( S \) satisfies
\( a + b = 3c \), then \( A \) is said to have Property \( P \).
Determine the number of three-element subsets of \( S \) that
have Property \( P \).
Answer: $\boxed{1600}$
-/
def S := Finset.map (⟨fun x ↦ x + 1, by exact add_left_injective 1⟩) (Finset.range 100)

def P (t : Finset ℕ) := ∃ a b c, t.card = 3 ∧ t = {a, b, c} ∧ a + b = 3 * c

instance : DecidablePred P := fun t => by
  by_cases hcard : t.card = 3
  . choose a b c hval using Multiset.card_eq_three.mp hcard
    have hnodup : Multiset.Nodup {a, b, c} := by rw [← hval]; apply Finset.nodup
    simp at hnodup
    have heq : t = {a, b, c} := by
      apply Finset.eq_of_veq; rw [hval]; symm; simp
      have : Multiset.ndinsert b {c} = b ::ₘ {c} := by
        apply Multiset.ndinsert_of_not_mem; simp; exact hnodup.2
      rw [this]; apply Multiset.ndinsert_of_not_mem; simp; exact hnodup.1
    if hs : a + b = 3 * c ∨ c + a = 3 * b ∨ b + c = 3 * a then
      have : P t := by
        unfold P
        rcases hs with hab | hca | hbc
        . exact ⟨a, b, c, hcard, heq, hab⟩
        . have : t = {c, a, b} := by sorry
          exact ⟨c, a, b, hcard, this, hca⟩
        . have : t = {b, c, a} := by sorry
          exact ⟨b, c, a, hcard, this, hbc⟩
      exact Decidable.isTrue this
    else
      have : ¬ P t := by
        rintro ⟨a', b', c', hcard', heq', hs'⟩
        sorry
      exact Decidable.isFalse this
  . have : ¬ P t := by
      unfold P; rintro ⟨a, b, c, ⟨hcard', ht, hsum⟩⟩
      apply hcard hcard'
    exact Decidable.isFalse this

def X := Finset.filter P (Finset.powersetCard 3 S)
