import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-
From Wikipedia, the free encyclopedia [1](https://en.wikipedia.org/wiki/Taxicab_number)

In mathematics, the nth taxicab number, typically denoted Ta(n) or Taxicab(n),
is defined as the smallest integer that can be expressed as a sum of two positive
integer cubes in n distinct ways. The most famous taxicab number is
1729 = Ta(2) = 1^3 + 12^3 = 9^3 + 10^3, also known as the Hardy-Ramanujan number.
-/

/-
We're going to follow [2](https://web.archive.org/web/20050215201136/http://www.cs.uwaterloo.ca/journals/JIS/wilson10.html)
and define two cube sum for number s as pair (a, b) such that s = a^3 + b^3 and a ≤ b.
-/

inductive TwoCubesExpression (s : ℕ)
  | mk (a b : ℕ) (hs : s = a^3 + b^3) (hord : a ≤ b)
  deriving Repr, DecidableEq
/-
An n-way sum is an integer s which can be expressed as the sum of two cubes in
exactly n different ways. Without loss of generality we can assume that a₁ < a₂ < ... < aₙ.
-/

def lt {s : ℕ} (left right : TwoCubesExpression s) : Prop :=
  match left, right with
  | ⟨a, _, _, _⟩, ⟨a', _, _, _⟩ => a < a'

/-instance : Decidable (lt left right) :=
  match left, right with
  | ⟨a, _, _, _⟩, ⟨a', _, _, _⟩ => Nat.decLt a a'-/

def way_sum (n s : ℕ) : Prop :=
  ∃ l : List (TwoCubesExpression s), l.length = n ∧ List.Sorted lt l

-- Let's prove that 1729 is 2-way sum --

def hardy_ramanujan_expr := [
  @TwoCubesExpression.mk 1729 1 12 (by norm_num) (by norm_num),
  @TwoCubesExpression.mk 1729 9 10 (by norm_num) (by norm_num),
]

theorem twoWaySum_hardy_ramanujan : way_sum 2 1729 := by
  use hardy_ramanujan_expr
  constructor
  . rfl
  . apply List.Pairwise.cons
    . unfold lt
      simp
    . apply List.Pairwise.cons
      . simp
      . apply List.Pairwise.nil

/-
The nth taxicab number is the least integer which can be expressed as a sum of
two positive cubes in (at least) n distinct ways, up to order of summands.
-/

def Taxicab (n s : ℕ) : Prop := way_sum n s ∧ ∀ s' < s, ¬ way_sum n s'

theorem hardy_ramanujan_is_taxicab_two : Taxicab 2 1729 := by sorry

/-
This is a hard theorem to prove by hand! The strategy is the following:
1. Provide an algorithm that computes some artifact, for example, list of ways
one can express all integers up to 1729 as a sum of two cubes.
2. Prove that the computed artifact satisfying some simple property implies theorem.
This is of course the hardest part because we need to prove correctness of the algorithm,
in other words it computes `something` and this is actually useful to us.
3. Prove simple property by explicit computation with rfl.
-/

/-
We're going to start modular by building a function that computes `maximal` number of
ways the number s can be expressed as a sum of two cubes and proving it's correctness.

Since this is an educational example, we're going to use a simple brute-force implementation.
Reference [2] provides a much more efficient algorithm involving prime factorization of a number
and finding two factors, corresponding to the factors a^3 + b^3 = (a + b)(a^2 - ab + b^2).
-/

-- max : ℕ is a limit on how large cube we consider --
def get_way_sum_expr (s max : ℕ) : List (TwoCubesExpression s) :=
  go s max max max (by linarith)
where
  go (s max a b : ℕ) (hord : a ≤ b) : List (TwoCubesExpression s) :=
    match a, b with
    | _, 0 => []
    | 0, Nat.succ b' => go s max b' b' (by linarith)
    | Nat.succ a', b =>
      if hs : s = a'.succ^3 + b^3 then
        @TwoCubesExpression.mk s a'.succ b hs hord :: go s max a' b (by linarith[hord])
      else
        go s max a' b (by linarith[hord])

def get_way_sum (s max : ℕ) := (get_way_sum_expr s max).length

-- Some minimal tests, but of course this is not enough for a mathematician! --

#eval get_way_sum_expr 1729 12
#eval get_way_sum_expr 1729 10
#eval get_way_sum_expr 1729 9

-- Now let's prove the correctness of the algorithm using induction --

/-
Log: I've started by defining way_sum as List.Sorted lt l, where lt compared
a by < operator. I wanted to prove that by sorting get_way_sum one can get
a List.Sorted lt list. The problem is that List.Sorted lt implies that
the list doesn't have duplicates, which is quite hard to prove.

I decided that the most elegant way is to prove that get_way_sum_expr
is sorted in a from the start.
-/

lemma go_sorted (s max a b : ℕ) (hord: a ≤ b) :
    List.Sorted lt (get_way_sum_expr.go s max a b hord) := by sorry

theorem get_way_sum_expr_sorted (s max : ℕ) :
    List.Sorted lt (get_way_sum_expr s max) := by
  unfold get_way_sum_expr
  apply go_sorted

theorem get_way_sum_expr_maximal {s max : ℕ} (x : TwoCubesExpression s)
    (hmax : s ≤ max^3) : x ∈ get_way_sum_expr s max := by sorry

-- Lemma that take first n elements operation doesn't break sorting --
lemma take_sorted (n : ℕ) (l : List α) (h : List.Sorted r l) : List.Sorted r (List.take n l) := by
  induction n generalizing l with
  | zero =>
    unfold List.take
    simp
  | succ n' ih =>
    unfold List.take
    cases l with
    | nil => simp
    | cons hd tl =>
      simp
      simp at h
      rcases h with ⟨hmem, hsort⟩
      constructor
      . intro b hb
        apply hmem
        apply List.mem_of_mem_take
        apply hb
      . exact ih tl hsort

-- Lemma that if no duplicate subset of a list can't have larger length than the list itself --
lemma nodup_subset_le_length [DecidableEq α] {l l' : List α} (hnodup : l'.Nodup) (hmem: ∀ x ∈ l', x ∈ l) :
    l'.length ≤ l.length := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simp
    | cons hd tl =>
      simp at hmem
      have := (hmem hd).1
      contradiction
  | cons hd tl ih =>
    simp at hmem
    set l'' := List.filter (fun x => decide ¬(x == hd)) l' with l''_def
    have hlen : l'.length = List.count hd l' + l''.length := by
      rw [l''_def, List.length_eq_countP_add_countP (fun x => x == hd)]
      rw [← List.countP_eq_length_filter]
      unfold List.count
      rfl
    have hmem' : ∀ x ∈ l'', x ∈ tl := by
      intro x hx
      rw [l''_def] at hx
      simp at hx
      rcases hx with ⟨hxl', hnhd⟩
      specialize hmem x hxl'
      rcases hmem with hhd | hxl
      . contradiction
      . exact hxl
    have hnodup' : l''.Nodup := by
      apply List.Nodup.filter
      exact hnodup
    have hlen' := ih hnodup' hmem'
    have hcount := List.nodup_iff_count_le_one.mp hnodup hd
    rw [hlen]
    simp
    linarith

-- Lemma that any list of two cube expressions sorted with lt has no duplicates --
lemma sorted_nodup {l : List (TwoCubesExpression s)} (h : List.Sorted lt l) : l.Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp at h
    rcases h with ⟨hhd, htl⟩
    simp
    constructor
    . intro hin
      specialize hhd hd hin
      unfold lt at hhd
      exact (lt_self_iff_false hd.1).mp hhd
    . exact ih htl

-- Theorem that get_way_sum has correct behavior --
theorem get_way_sum_correct (s max : ℕ) (hmax : s ≤ max^3) :
    (∀ n ≤ get_way_sum s max, way_sum n s) ∧ (∀ n > get_way_sum s max, ¬ way_sum n s) := by
  constructor
  . intro n hn
    set way := List.take n (get_way_sum_expr s max) with way_def
    use way
    rw [way_def]
    constructor
    . apply List.length_take_of_le
      assumption
    . apply take_sorted
      apply get_way_sum_expr_sorted
  . rintro n hn ⟨l, ⟨hlen, hsort⟩⟩
    have hnodup := sorted_nodup hsort
    have hbound := nodup_subset_le_length hnodup (fun x _ => get_way_sum_expr_maximal x hmax)
    rw [hlen] at hbound
    unfold get_way_sum at hn
    linarith
