-- Lean has one line --

/-
and multiple line
comments
-/

/-!
## Documentation

You can write markdown inside comments with ! included on top like that
```
/-!
this is a comment inside a comment
-/
```
It can be compiled into docs with [doc-gen4](https://github.com/leanprover/doc-gen4).
Just run
```
lake -R -Kenv=dev build LeanCourse:docs
```
to update the docs and they will be built in `.lake/build/doc`.
Docs are useful when you're writing a proof for a large theorem. More on this workflow later.
-/

/-!
## Codestyle

To write readable and maintainable code people agree on a set of rules called
the codestyle that is going to be applied for each file in the project.

Lean project Mathlib has its own
[codestyle](https://leanprover-community.github.io/contribute/style.html),
that we will try to adhere to. You can read it when you have time, but important
rules are:
-/

/-! 1. Lines should contain less than 100 characters. -/

-- You can use indentation to turn this --
example (x y z a b c : Nat) (h1 : x + y + z = a + b + c) (h2 : x + y = a + b) (h3 : x = a) : x * y * z = a * b * c := by sorry

-- into this --
example (x y z a b c : Nat) (h1 : x + y + z = a + b + c)
    (h2 : x + y = a + b) (h3 : x = a) : x * y * z = a * b * c := by sorry

/-!
2. Indentation rules.

a) Keywords like theorem/lemma/example have to flush-left in the document.

b) Proof has to be indented with 2 spaces (one tab push).

c) If theorem statement doesn't fit, as in previous rule you indent it with 4 spaces.

d) Keywords by/calc have to be on the same line as the statement
-/
-- Here's the example: --
example (x y z a b c : Nat) (h1 : x + y + z = a + b + c)
    (h2 : x + y = a + b) (h3 : x = a) : x * y * z = a * b * c := by
  rw [h3] at h2
  have h4 : y = b := by exact Nat.add_left_cancel h2
  rw [h3, h4] at h1
  have h5 : z = c := by
    -- you can go to the next line too --
    exact Nat.add_left_cancel h1
  rw [h3, h4, h5]

/-!
3. Use VSCode typing capabilities.

You can type math characters with \ symbol. For example, type \g to see γ,
or \neq to get ≠. When you see a new symbol, you can always hover over it
and see how it's typed. Now guess yourself how to type \ itself.
-/

/-!
4. Hypotheses to the left.

a) Try to replace general quantifier with explicit variable declaration

b) Try to replace implication with explicit hypotheses declaration
-/
-- Here's the example: --
example (n : Nat) : n = n := by rfl

example (a : Nat) (h : ∀ n, n + a = n) : a = 0 := by
  have h' := h 0
  rw [Nat.zero_add] at h'
  exact h'

-- is better than --
example : ∀ (n : Nat), n = n := by
  intro n
  rfl
-- even the proof is longer now --

-- Here's the example for hypothesis usage: --
example (n : Nat) (h : n > 0) : n ≠ 0 := by exact Nat.not_eq_zero_of_lt h

-- is better than --
example (n : Nat) : n > 0 → n ≠ 0 := by
  intro h
  exact Nat.not_eq_zero_of_lt h
