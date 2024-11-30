import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pi

/--
Bijection Rule. Two nonempty finite sets A and B have
the same number of elements if and only if there exists
a bijection f : A → B
-/
theorem bijection_rule
    {A : Finset α} {B : Finset β}
    (f : α → β) (hf : Function.Bijective f)
    (hAB : ∀ x, x ∈ A ↔ f x ∈ B) : A.card = B.card := by
  exact Finset.card_bijective f hf hAB

/--
Sum Rule. If A is a finite set, and A = A₁ ∪ A₂ ∪ … ∪ Aₙ,
where Aᵢ ∩ Aⱼ = ∅ for all i ≠ j, then
    |A| = |A₁| + |A₂| + … + |Aₙ|
-/
theorem sum_rule {I : Finset ι} {𝒜 : ι → Finset α}
    (h : Set.PairwiseDisjoint I 𝒜)
    (hA : A = Finset.disjiUnion I 𝒜 h):
    A.card = ∑ i ∈ I, (𝒜 i).card := by
  induction I using Finset.cons_induction
  next => simp; simp at hA; exact hA
  next => rw [Finset.sum_cons, hA, Finset.disjiUnion_cons]; simp

/--
Multiplication Rule. Let A and B be finite sets and
f : A → B a function such that, for any element b ∈ B,
there exist exactly k elements from set A whose image is
equal to b. Then |A| = k ⬝ |B|
-/
theorem multiplication_rule [DecidableEq β]
    {A : Finset α} {B : Finset β} (f : α → β) (k : ℕ)
    (hAB : ∀ x, x ∈ A ↔ f x ∈ B)
    (hf : ∀ b ∈ B, (Finset.filter (fun a ↦ f a = b) A).card = k) :
    A.card = k * B.card := by
  let 𝒜 := fun b ↦ Finset.filter (fun a ↦ f a = b) A
  have h : Set.PairwiseDisjoint B 𝒜 := by
    intro x _ y _ hneq; unfold_let; unfold Disjoint Function.onFun; simp
    intro A' hAx hAy
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_not_mem]
    intro z hz
    obtain ⟨_, hfz⟩ := Finset.mem_filter.mp (hAx hz)
    obtain ⟨_, hfz'⟩ := Finset.mem_filter.mp (hAy hz)
    rw [← hfz, ← hfz'] at hneq; contradiction
  have hA : A = Finset.disjiUnion B 𝒜 h := by
    ext x; unfold_let; constructor
    . intro hx; simp; exact ⟨hx, (hAB x).mp hx⟩
    . intro hx; simp at hx; exact hx.1
  rw [sum_rule h hA]; unfold_let; simp
  rw [Finset.sum_congr (by rfl) hf]; simp; rw [mul_comm]

/--
Product Rule. Let A₁, A₂, …, Aₙ be finite sets that consist
of k₁, k₂, …, kₙ elements, respectively. Then, the Cartesian
product A₁ × A₂ × … × Aₙ is a k₁k₂…kₙ-set, i.e
    |A₁ × A₂ × … × Aₙ| = |A₁| ⬝ |A₂| ⬝ … ⬝ |Aₙ|
Particularly, |Aⁿ| = |A|ⁿ.
-/
theorem product_rule [DecidableEq ι] {α : ι -> Type*}
    [(i : ι) → DecidableEq (α i)] (I : Finset ι) (𝒜 : (i : ι) → Finset (α i)) :
    (Finset.pi I 𝒜).card = ∏ i ∈ I, (𝒜 i).card := by
  induction I using Finset.induction
  next => simp
  next i I' hi hind =>
    rw [Finset.pi_insert hi]
    /- Product consists of maps (i : ι) → α i, inserting new element i is
    equivalent to taking all maps z and going over all variants z i = b ∈ 𝒜 i.
    We partition maps into buckets per b. -/
    have hdisj : Set.PairwiseDisjoint (𝒜 i) (fun b ↦ Finset.image (Finset.Pi.cons I' i b) (I'.pi 𝒜)) := by
      intro x _ y _ hneq; unfold Disjoint Function.onFun; simp
      intro A hAx hAy
      rw [Finset.subset_empty, Finset.eq_empty_iff_forall_not_mem]
      -- Introduce map that is simultaneously in bucket x and bucket y (x ≠ y) --
      intro z hz
      have : i ∈ insert i I' := Finset.mem_insert_self i I'
      -- We get contradiction because z i = x ≠ y = z i --
      have hzx : z i this = x := by
        obtain ⟨zx, _, heqzx⟩ := Finset.mem_image.mp (hAx hz)
        rw [← heqzx]; simp
      have hzy : z i this = y := by
        obtain ⟨zy, _, heqzy⟩ := Finset.mem_image.mp (hAy hz)
        rw [← heqzy]; simp
      rw [← hzx, ← hzy] at hneq
      contradiction
    rw [← Finset.disjiUnion_eq_biUnion _ _ hdisj, sum_rule hdisj]
    have hcard : ∀ b ∈ 𝒜 i, (Finset.image (Finset.Pi.cons I' i b) (I'.pi 𝒜)).card = (I'.pi 𝒜).card := by
      intro b _
      rw [Finset.card_image_of_injective _ (Finset.Pi.cons_injective hi)]
    rw [Finset.sum_congr (by rfl) hcard, Finset.sum_const]
    rw [Finset.prod_insert hi, ← hind]; simp; rfl

instance [Fintype α] [DecidableEq α] [Fintype β] : Fintype (α → β) where
  elems := Finset.map
    ⟨fun f ↦ fun a ↦ f a (Finset.mem_univ a), by
      intro f g h; ext x hx
      have := congr h (by rfl : x = x); simp at this
      rw [this]
    ⟩
    (Finset.pi (@Finset.univ α _) (fun _ ↦ (@Finset.univ β _)))
  complete := by intro f; simp; use (fun a _ ↦ f a)

theorem function_card [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  unfold Fintype.card Finset.univ Fintype.elems instFintypeForallOfDecidableEq_leanCourse; dsimp
  rw [Finset.card_map, product_rule]; simp; rfl
