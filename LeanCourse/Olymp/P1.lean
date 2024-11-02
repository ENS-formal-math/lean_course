import Mathlib.Tactic

/-
Problem: Dad, Masha, and Yasha are walking to school. While Dad takes
3 steps, Masha takes 5 steps. While Masha takes 3 steps, Yasha
takes 5 steps. Masha and Yasha counted that together they took
400 steps. How many steps did Dad take?
Answer: $\boxed{90}$.
-/
theorem problem (dad masha yasha : ℕ) (h₁ : ∃ k, dad = 3 * k ∧ masha = 5 * k)
    (h₂ : ∃ m, masha = 3 * m ∧ yasha = 5 * m) (h₃ : masha + yasha = 400) : dad = 90 := by
  rcases h₁ with ⟨k, ⟨hdad, hmasha₁⟩⟩
  rcases h₂ with ⟨m, ⟨hmasha₂, hyasha⟩⟩
  rw [hmasha₂, hyasha] at h₃
  have : m * 8 = 400 := by ring_nf at h₃; exact h₃
  have : m = 50 := by
    rw [← Nat.mul_div_cancel m (by linarith : 0 < 8)]
    rw [this]
  rw [this] at hmasha₂; norm_num at hmasha₂; rw [hmasha₂] at hmasha₁
  have : k = 30 := by
    rw [← Nat.mul_div_cancel_left k (by linarith : 0 < 5)]
    rw [← hmasha₁]
  rw [this] at hdad; norm_num at hdad; exact hdad
