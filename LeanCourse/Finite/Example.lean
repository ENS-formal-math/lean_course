import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/--
2002 AIME II Problem 5

Problem: Find the sum of all positive integers $a=2^n3^m$ where $n$ and $m$ are
non-negative integers, for which $a^6$ is not a divisor of $6^a$.

Solution: Substitute $a=2^n3^m$ into $a^6$ and $6^a$, and find all pairs of
non-negative integers (n,m) for which $(2^n3^m)^{6}$ is not a divisor of $6^{2^n3^m}$

Simplifying both expressions:
$2^{6n} \\cdot 3^{6m}$ is not a divisor of $2^{2^n3^m} \\cdot 3^{2^n3^m}$
Comparing both exponents (noting that there must be either extra powers of 2 or
extra powers of 3 in the left expression):
$6n > 2^n3^m$  OR  $6m > 2^n3^m$

Using the first inequality $6n > 2^n3^m$ and going case by case starting with n
$\\in$ {0, 1, 2, 3...}:
  n=0:
    $0>1 \\cdot 3^m$ which has no solution for non-negative integers m
  n=1:
    $6 > 2 \\cdot 3^m$ which is true for m=0 but fails for higher integers $\\Rightarrow (1,0)$
  n=2:
    $12 > 4 \\cdot 3^m$ which is true for m=0 but fails for higher integers $\\Rightarrow (2,0)$
  n=3:
    $18 > 8 \\cdot 3^m$ which is true for m=0 but fails for higher integers $\\Rightarrow (3,0)$
  n=4:
    $24 > 16 \\cdot 3^m$ which is true for m=0 but fails for higher integers $\\Rightarrow (4,0)$
  n=5:
    $30 > 32 \\cdot 3^m$ which has no solution for non-negative integers m
There are no more solutions for higher $n$, as polynomials like $6n$ grow slower than exponentials like $2^n$.

Using the second inequality $6m > 2^n3^m$ and going case by case starting with
m $\\in$ {0, 1, 2, 3...}:
  m=0:
    $0>2^n \\cdot 1$ which has no solution for non-negative integers n
  m=1:
    $6>2^n \\cdot 3$ which is true for n=0 but fails for higher integers $\\Rightarrow (0,1)$
  m=2:
    $12>2^n \\cdot 9$ which is true for n=0 but fails for higher integers $\\Rightarrow (0,2)$
  m=3:
    $18>2^n \\cdot 27$ which has no solution for non-negative integers n
  There are no more solutions for higher $m$, as polynomials like $6m$ grow slower than exponentials like $3^m$.

Thus there are six numbers corresponding to (1,0), (2,0), (3,0), (4,0), (0,1), and (0,2).
Plugging them back into the original expression, these numbers are 2, 4, 8, 16, 3, and 9,
respectively. Their sum is $\\framebox{042}$.

Notice that the condition is equivalent to saying
\\[v_2(a^6) \\geq v_2(6^a) \\implies 6n \\geq a\\]\n\\[v_3(a^6) \\geq v_3(6^a) \\implies 6m \\geq a.\\]
Notice that we cannot have both expressions to be equality state, as that would result in $a^6 = 6^a.$
Testing, we see the possible pairs $(n, m)$ are $(1, 0), (2, 0), (3, 0), (4, 0), (0, 1), (0, 2).$

Since the $a$ grows much faster than the left-hand side of the above inequalities, these are all possible solutions.
Adding, we get $\\framebox{042}$.
-/
theorem numbertheory_721 (x : Finset ℕ)
    (h : ∀ a, a ∈ x ↔ (∃ n m, a = 2^n * 3^m) ∧ ¬a^6 ∣ 6^a) : ∑ a ∈ x, a = 42 := by
  -- Simplify both expressions --
  have h₁ (a n m : ℕ) (ha : a = 2^n * 3^m) :
      ¬a^6 ∣ 6^a ↔ (6 * n > 2^n * 3^m ∨ 6 * m > 2^n * 3^m) := by
    -- a^6 = 2^{6n} \\cdot 3^{6m}
    have h₁ : a^6 = 2^(6 * n) * 3^(6 * m) := by
      rw [ha]; ring
    -- $2^{2^n3^m} \\cdot 3^{2^n3^m}$ --
    have h₂ : 6^a = 2^(2^n * 3^m) * 3^(2^n * 3^m) := by
      rw [ha, (by norm_num : 6 = (2 * 3)), mul_pow]
    -- Comparing both exponents (noting that there must be either extra powers of 2 or extra powers of 3 in the left expression) --
    constructor
    . intro hdiv
      rw [h₁, h₂] at hdiv
      -- Suppose contrary that 6 * n ≤ 2^n * 3^m and 6 * m ≤ 2^n * 3^m --
      by_contra h; rw [not_or] at h
      obtain ⟨i, hni⟩ := Nat.le.dest (le_of_not_lt h.1)
      obtain ⟨k, hnk⟩ := Nat.le.dest (le_of_not_lt h.2)
      -- Then 2^(6 * n) * 3^(6 * m) divides 2^(2^n * 3^m) * 3^(2^n * 3^m) --
      nth_rw 1 [← hni] at hdiv; rw [← hnk] at hdiv
      exact hdiv (mul_dvd_mul
        (pow_dvd_pow 2 (by linarith) : 2 ^ (6 * n) ∣ 2 ^ (6 * n + i))
        (pow_dvd_pow 3 (by linarith) : 3 ^ (6 * m) ∣ 3 ^ (6 * m + k))
      )
    . intro hdiv hcontra
      rw [h₁, h₂] at hcontra
      -- a ∣ b is equivalent to all powers of primes in factorization of `a` being less or equal to that of `b` --
      rw [← Nat.factorization_le_iff_dvd (by norm_num) (by norm_num)] at hcontra
      simp [Nat.factorization_mul, Nat.factorization_pow, Finsupp.le_def] at hcontra
      -- Powers of 2 give 6 * n ≤ 2 ^ n * 3 ^ m --
      have h₃ := hcontra 2
      rw [(Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr rfl) : (Nat.factorization 3) 2 = 0),
        (Nat.Prime.factorization_self Nat.prime_two : (Nat.factorization 2) 2 = 1)] at h₃
      simp at h₃
      -- Powers of 3 give 6 * m ≤ 2 ^ n * 3 ^ m --
      have h₄ := hcontra 3
      rw [(Nat.factorization_eq_zero_of_not_dvd (by decide): (Nat.factorization 2) 3 = 0),
        (Nat.Prime.factorization_self Nat.prime_three : (Nat.factorization 3) 3 = 1)] at h₄
      simp at h₄
      rcases hdiv with hdiv₁ | hdiv₂ <;> linarith
  have h₂ (n m : ℕ) (hn : 6 * n > 2^n * 3 ^ m) : n ≤ 4 := by
    sorry
  have h₃ (n m : ℕ) (hm : 6 * m > 2^n * 3^m) : m ≤ 2 := by
    sorry
  let y := Finset.filter
    (fun ⟨n, m⟩ ↦ 6 * n > 2^n * 3 ^ m ∧ 6 * m > 2^n * 3^m)
    (Finset.range 5 ×ˢ Finset.range 3)
  let x' := Finset.map ⟨fun ⟨n, m⟩ ↦ 2^n * 3^m, by
    intro ⟨n, m⟩ ⟨n', m'⟩ h
    simp at h; apply congrArg Nat.factorization at h
    have ha := congrFun (congrArg DFunLike.coe h) 2
    have hb := congrFun (congrArg DFunLike.coe h) 3
    simp [Nat.factorization_mul, Nat.factorization_pow] at ha
    rw [(Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr rfl) : (Nat.factorization 3) 2 = 0),
        (Nat.Prime.factorization_self Nat.prime_two : (Nat.factorization 2) 2 = 1)] at ha
    simp at ha
    simp [Nat.factorization_mul, Nat.factorization_pow] at hb
    rw [(Nat.factorization_eq_zero_of_not_dvd (by decide): (Nat.factorization 2) 3 = 0),
        (Nat.Prime.factorization_self Nat.prime_three : (Nat.factorization 3) 3 = 1)] at hb
    simp at hb
    exact Prod.ext ha hb
  ⟩ y
  have h₄ : x = x' := by sorry
  -- Testing, we see the possible pairs $(n, m)$ are $(1, 0), (2, 0), (3, 0), (4, 0), (0, 1), (0, 2).$ --
  have h₅ : y = {⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩} := by
    unfold_let; sorry
  rw [h₄]; unfold_let x; rw [Finset.sum_map, h₅]; simp
