-- Attention! This might blow your mind! --
import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Group.Even

/-
In Lean each expression has a type that can be found with #check.
To see type you can hover over it or open Infoview: Toggle Infoview in VSCode
that opens Lean Infoview, it will be very useful later when we do the proofs.
-/
#check 2 + 2
-- Here ℕ is a type of natural numbers

/-
If a function f takes value of type A and outputs B, its type is A → B
You can define functions as
-/
def f(n : ℕ) := 2 * n
#check f
-- equivalent type of f is ℕ → ℕ --

def g(_ _ : ℕ) := 0
#check g
-- type ℕ → ℕ → ℕ --

#eval f (g 0 1)
-- evaluate expressions --

-- Everything has a type, even types themselves! --
#check ℕ
#check Type
-- You can notice that type of Type n is Type n+1. This is done to prevent Russell-like paradoxes. --

/-
One of the most important types is called Prop (for proposition).
Typical theorem statement that you write will have this type
-/
def first_theorem := ∀ n, Even (f n)

#check False

#check first_theorem

/-
Here comes the killer, called the Curry-Howard correspondence:

Informal side:    Proof ---> Theorem
                  |             |
                  |             |
Lean side:        Expr  ---> Type ---> Prop

You have to read A ---> B as A is of type B.

For example, what is f? It's an expression of type ℕ → ℕ, or, in other words,
a proof of ℕ → ℕ, a proof that elements of this type exist.

This is very clever, because now to prove something you need just to build
an expression that has the theorem's type. What Lean does is type checking.

For example:
-/
theorem proof_object : first_theorem :=
  fun n => ⟨n, Nat.two_mul n⟩

#check Nat.two_mul 0

/-
You don't need to understand everything but type of first_theorem is ∀ n, Even (f n),
meaning that for each n we need to provide proof of type Even (f n). This is exactly,
what we're doing with `fun n => ...`. To prove Even m, we need to provide a number k and
give a proof that m = k + k. Since f n = 2 * n, we provide number n and Nat.two_mul n is
a proof that 2 * n = n + n.
-/

/- Constructing proofs like that can be very hard, as they grow in complexity. Lean provides
what's called the tactic mode. You start with keyword by and use handful of human-understandable tactics.
In the end Lean constructs an analog of proof_object automatically -/
theorem proof_with_tactics : first_theorem := by
  -- Introduce n --
  intro n
  -- Even k is defined as ∃ m, k = m + m. We use n as an example of m --
  use n
  -- Prove that 2 * n = n + n. Lean unfolds f n = 2 * n automatically.
  exact Nat.two_mul n
-- You can view the proof's state in Lean Infoview, trying clicking on different lines --

-- Typically, you name proof by the theorem's name. So something more mathlib-like would look like --
theorem even_f (n : ℕ) : Even (f n) := ⟨n, Nat.two_mul n⟩

def even_f_def (n: ℕ) : 2 * n = n + n := Nat.two_mul n

#check even_f_def

/-
Tactical proofs are simple to write and understand, but functional proofs constantly remind us of
the Curry-Howard correspondance. So, final example of it is proving that if P ∧ Q, then Q ∧ P,
where ∧ is logical and. We want to prove a general theorem that it's true for any Prop.
-/
theorem and_symmetric (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
/-
Premise of theorem is that P ∧ Q is true, so we're given a hypothesis - something of type P ∧ Q.
Logically, P ∧ Q is true if P and Q is true (more tautologies incoming), so in fact we're given
a proof of P and a proof of Q. In Lean h is essentially a tuple and individual proofs can be
found at h.1 and h.2, respectively. Then to prove Q ∧ P, we have to provide proof of this type.
We can compose a tuple from a proof of Q and a proof of P. But hey! We already have them at
h.2 and h.1, respectively, so let's compose them at ⟨h.2, h.1⟩
-/
