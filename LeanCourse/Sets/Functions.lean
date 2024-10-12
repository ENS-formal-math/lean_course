import Mathlib.Data.Set.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

variable {α β γ : Type*}
variable (f : α → β) (g : β → γ)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set
open Real

/-
Function of type α → β acts on elements of type α and
returns an element of type β.

If p : Set β, its preimage is written as `preimage f p` or `f⁻¹' p`.
It's defined as `f⁻¹' p = {x | f x ∈ p}`.
Lean can simplify `x ∈ f⁻¹' p` to `f x ∈ p`.
-/

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

/-
For s : Set α, its image is written as `image f s` or `f '' s`.
It's defined as `f '' s = {y | ∃ x, x ∈ s ∧ f x = y}`.
We can decompose `y ∈ f '' s` into triple `⟨x, hx : x ∈ s, heq : f x = y⟩`.
-/

-- Here when we write rfl in rintro, it automatically uses f x = y to substitute --
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

-- exercise --
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry

-- Some properties of functions like injectivity are already defined in Mathlib --
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x ⟨x', hx, heq⟩
  rw [h heq] at hx
  exact hx

-- library defines also injectivity on given set --
#check InjOn f s

/-
`Injective f` is (provably) equivalent to `InjOn f univ`. There's a pattern
when you define some property or mapping only on given set and then substitute `univ`.

For example, you can define range as `range f = {y | ∃ x, f x = y}` that
is equivalent to `f '' univ`.
-/

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry
