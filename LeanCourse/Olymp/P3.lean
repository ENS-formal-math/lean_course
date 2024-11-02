import Mathlib.Tactic

/-A function $f: \mathbb N \to \mathbb N$ satisfies the following two conditions
for all positive integers $n$:$f(f(f(n)))=8n-7$ and $f(2n)=2f(n)+1$. Calculate $f(100)$.-/

theorem solution (f: ℤ → ℤ) (h1: ∀ n, n > 0 → f (f (f n)) = 8 * n - 7)
  (h2: ∀ n, n > 0 → f (2 * n) = 2 * (f n) + 1) (h3: ∀ n, n > 0 → f n > 0) : f 100 = 199 := by
  /- 1. Analyze the first condition
    $$ f(f(f(n))) = 8n - 7 $$
    Apply $f$ to both sides of this equation:
    $$ f(f(f(f(n)))) = f(8n - 7) $$ -/
  have eq1: ∀ n, n > 0 → f (f (f (f n))) = f (8 * n - 7) := by
    intro n hpos
    rw [h1 n hpos]

  /- 2. Utilize the given property:
    From the original property, we know
    $$ f(f(f(f(n)))) = 8f(n) - 7 $$
    Hence, we equate:
    8f(n) - 7 = f(8n - 7) -/
  have eq2: ∀ n, n > 0 → 8 * (f n) - 7 = f (8 * n - 7) := by
    intro n hpos
    rw [← h1 (f n) (h3 n hpos), eq1 n hpos]

  /- 3. Evaluate for n = 1:
    $$ 8 f(1) - 7 = f(1) \Rightarrow 7 f(1) = 7 \Rightarrow f(1) = 1 $$ -/
  have eq3: f 1 = 1 := by
    specialize eq2 1 (by simp)
    simp at eq2
    rw [sub_eq_neg_add, neg_add_eq_iff_eq_add, add_comm, ← neg_add_eq_iff_eq_add] at eq2
    ring_nf at eq2
    nth_rw 2 [← one_mul 7] at eq2
    apply Int.ediv_eq_of_eq_mul_left at eq2
    rw [Int.mul_ediv_cancel] at eq2
    exact eq2
    repeat linarith

  /- 4. Inductive Hypothesis:
    Using the second condition, $f(2n) = 2f(n) + 1$, we will prove by induction that:
    $$ f(2^kn) = 2^kf(n) + (2^k - 1) $$ -/
  have eq4: ∀ n k, n > 0 → f (2^k * n) = 2^k * (f n) + 2^k - 1 := by
    intro n k hpos
    induction k with
    /- Base Case:
      For $k = 0$, $f(2^0n) = f(n) = 2^0f(n) + (2^0 - 1) = f(n) $-/
    | zero =>
      simp
    /- Inductive Step:
      Assume the hypothesis holds for $k = m$, i.e.
      $$ f(2^m n) = 2^m f(n) + (2^m - 1) $$
      We need to show it holds for $k = m + 1$:
      $$ f(2^{m+1}n) = f(2\cdot 2^m n) = 2f(2^mn) + 1
      By the inductive hypothesis:
      $$f(2\cdot 2^mn) = 2[2^m f(n) + (2^m - 1)] + 1
      Simplify:
      $$ = 2^{m+1}f(n) + 2^{m+1} - 2 + 1 = 2^{m+1}f(n) + 2^{m+1} - 1
      Thus, the hypothesis holds -/
    | succ m ih =>
      have h: (2: ℤ) ^ Nat.succ m = 2 * 2^m := by
        rw [mul_comm]
        exact Int.pow_succ 2 m
      rw [h, mul_assoc, h2, ih]
      ring
      apply mul_pos
      . apply pow_pos
        simp
      . exact hpos

  /- 5. Finding $f(25)$
    We need $f(100)$, and from our induction formula
    $$ f(100) = f(2^2\cdot 25) = 2^2 f(25) + (2^2 - 1) = 4f(25) + 3 $$ -/
  have eq5: f 100 = 4 * (f 25) + 3 := by
    specialize eq4 25 2 (by linarith)
    ring_nf at eq4
    rw [add_comm, mul_comm]
    exact eq4

  /- 6. Determine $f(25)$:
    Notice that $25 = 8\cdot 3 + 1$. We use $f(f(f(n))) = 8n-7$ repeatedly until we get $f(25)$.
    We start with $n = 4$:
    $$ f(25) = f(8\cdot 3 + 1) = f(8\cdot 4 - 7) = 8 f(4) - 7 $$ -/
  have eq6a: f 25 = 8 * (f 4) - 7 := by
    specialize eq2 4 (by linarith)
    ring_nf at eq2
    rw [mul_comm, sub_eq_neg_add, eq2]

  /- Evaluate $f(4)$ using induction formula
    $$ f(4) = f(2^2\cdot 1) = 2^2 f(1) + (2^2 - 1) = 4f(1) + 3 $$
    Since $f(1) = 1$, $f(4) = 4\cdot 1 + 3 = 7$ -/
  have eq6b: f 4 = 7 := by
    specialize eq4 1 2 (by linarith)
    rw [eq3] at eq4
    ring_nf at eq4
    exact eq4

  -- Hence $$ f(25) = 8 f(4) - 7 = 8\cdot 7 - 7 = 49 $$ --
  have eq6: f 25 = 49 := by
    rw [eq6b] at eq6a
    ring_nf at eq6a
    exact eq6a

  /- 7. Calculate $f(100)$:
    $$ f(100) = 4f(25) + 3 = 4\cdot 49 + 3 = 196 + 3 = 199 $$ -/
  rw [eq5, eq6]
  ring
