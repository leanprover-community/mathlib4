/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Grade

/-!
# Kőnig's infinity lemma

Kőnig's infinity lemma is most often stated as a graph theory result :
every infinite, locally finite connected graph contains an infinite path.
It has links to computability and proof theory, and
is often applied when the graph is a tree whose vertices encode some other types of object.

For applications of this form, it is convenient to state the lemma
in terms of covers in a strongly atomic order rather than a graph;
in this setting, the proof is almost trivial.
In this file, we prove the lemma in this order-theoretic way,
and also give a formulation that is convenient for applications in Ramsey theory.
We defer the graph-theoretic version of the statement for future work.

## Main Results

* `exists_seq_covby_of_forall_covby_finite` : Kőnig's lemma for strongly atomic orders.

* `exists_orderEmbedding_covby_of_forall_covby_finite` : Kőnig's lemma, where the sequence
    is given as an `OrderEmbedding` instead of a function.

* `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot` : Kőnig's lemma where the sequence
    starts at the minimum of an infinite type.

* `exist_seq_forall_proj_of_forall_finite` : Kőnig's lemma applied to an order on a sigma-type
  `(i : ℕ) × α i`. Useful for applications in Ramsey theory.

## TODO

Actually formulate the lemma as a statement about graphs.

-/

open Set
section Sequence

variable {α : Type*} [PartialOrder α] [IsStronglyAtomic α] {a b : α}

/-- **Kőnig's infinity lemma** : if each element in a strongly atomic order
is covered by only finitely many others, and `b` is an element with infinitely many things above it,
then there is a sequence starting with `b` in which each element is covered by the next. -/
theorem exists_seq_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ → α, f 0 = b ∧ ∀ i, f i ⋖ f (i+1) :=
  let h := fun a : {a : α // (Ici a).Infinite} ↦
    exists_covby_infinite_Ici_of_infinite_Ici a.2 (hfin a)
  let ks : ℕ → {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩ fun _ a ↦ ⟨_, (h a).choose_spec.2⟩
  ⟨fun i ↦ (ks i).1, by simp [ks], fun i ↦ by simpa using (h (ks i)).choose_spec.1⟩

/-- The sequence given by Kőnig's lemma as an order embedding -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ ↪o α, f 0 = b ∧ ∀ i, f i ⋖ f (i+1) := by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i ↦ (hf.2 i).lt)), hf⟩

/-- A version of Kőnig's lemma where the sequence starts at the minimum of an infinite order.  -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite_of_bot [OrderBot α] [Infinite α]
    (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) : ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ ∀ i, f i ⋖ f (i+1) :=
  exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

theorem GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite
    [GradeMinOrder ℕ α] [OrderBot α] [Infinite α] (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) :
    ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ (∀ i, f i ⋖ f (i+1)) ∧ ∀ i, grade ℕ (f i) = i := by
  obtain ⟨f, h0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  refine ⟨f, h0, hf, fun i ↦ ?_⟩
  induction' i with i ih; simp [h0]
  simpa [Nat.covBy_iff_succ_eq, ih, eq_comm] using CovBy.grade ℕ <| hf i

end Sequence

section Graded

/-- A formulation of Kőnig's infinity lemma, useful in applications.
Given a sequence `α 0, α 1, ...` of nonempty types with `α 0` a subsingleton,
and a well-behaved family of projections `π : α j → α i` for all `i ≤ j`,
if each term in each `α i` is the projection of only finitely many terms in `α (i+1)`,
then we can find a sequence `(f 0 : α 0), (f 1 : α 1), ...`
where `f i` is the projection of `f j` for all `i ≤ j`.

In a typical application, the `α i` are function types with increasingly large domains,
and `π hij (f : α j)` is the restriction of the domain of `f` to that of `α i`.
In this case, the sequence given by the lemma is essentially a function whose domain
is the limit of the `α i`. -/
theorem exists_seq_forall_proj_of_forall_finite {α : ℕ → Type*} [Subsingleton (α 0)]
    [∀ i, Nonempty (α i)] (π : {i j : ℕ} → (hij : i ≤ j) → α j → α i)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a, (π hij) (π hjk a) = π (hij.trans hjk) a)
    (π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a)
    (hfin : ∀ i a, {b : α (i+1) | π (Nat.le_add_right i 1) b = a}.Finite ) :
    ∃ f : (i : ℕ) → α i, ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by

  set αs := (i : ℕ) × α i

  let _ : PartialOrder (αs) := {
    le := fun a b ↦ ∃ h, π h b.2 = a.2
    le_refl := fun a ↦ ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' ↦ ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by
      rintro ⟨i,a⟩ ⟨j,b⟩ ⟨hij : i ≤ j, hab : π hij b = a⟩ ⟨hji : j ≤ i, hba : π hji a = b⟩
      obtain rfl := hij.antisymm hji
      rw [show a = b by rwa [π_refl] at hba] }

  have hcovby : ∀ {a b : αs}, a ⋖ b ↔ a ≤ b ∧ a.1 + 1 = b.1 := by
    simp only [covBy_iff_lt_and_eq_or_eq, lt_iff_le_and_ne, ne_eq, Sigma.forall, and_assoc,
      and_congr_right_iff, or_iff_not_imp_left]
    rintro i a j b ⟨h : i ≤ j, rfl : π h b = a⟩
    refine ⟨fun ⟨hne, h'⟩ ↦ ?_, ?_⟩
    · have hle' : i + 1 ≤ j := h.lt_of_ne <| by rintro rfl; simp [π_refl] at hne
      exact congr_arg Sigma.fst <| h' (i+1) (π hle' b) ⟨by simp, by rw [π_trans]⟩ ⟨hle', by simp⟩
        (fun h ↦ by apply_fun Sigma.fst at h; simp at h)
    rintro rfl
    refine ⟨fun h ↦ by apply_fun Sigma.fst at h; simp at h, ?_⟩
    rintro j c ⟨hij : i ≤ j, hcb : π _ c = π _ b⟩ ⟨hji : j ≤ i + 1, rfl : π hji b = c⟩ hne
    replace hne := show i ≠ j by rintro rfl; exact hne rfl
    obtain rfl := hji.antisymm (hij.lt_of_ne hne)
    rw [π_refl]

  have _ : IsStronglyAtomic αs := by
    simp_rw [isStronglyAtomic_iff, lt_iff_le_and_ne, hcovby]
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨⟨hij : i ≤ j, h2 : π hij b = a⟩, hne⟩
    have hle : i + 1 ≤ j := hij.lt_of_ne (by rintro rfl; simp [← h2, π_refl] at hne)
    refine ⟨⟨_, π hle b⟩, ⟨⟨by simp, by rw [π_trans, ← h2]⟩,by simp⟩, ⟨hle, by simp⟩⟩

  let _ : OrderBot αs := OrderBot.mk (toBot := ⟨0, Classical.arbitrary _⟩)
    fun _ ↦ ⟨Nat.zero_le _, Subsingleton.elim _ _⟩

  have hfin : ∀ (a : αs), {x | a ⋖ x}.Finite := by
    refine fun ⟨i,a⟩ ↦ ((hfin i a).image (fun b ↦ ⟨_,b⟩)).subset ?_
    simp only [hcovby, subset_def, mem_setOf_eq, mem_image, and_imp, Sigma.forall]
    exact fun j b ⟨_, _⟩ hj ↦ ⟨π hj.le b, by rwa [π_trans], by cases hj; rw [π_refl]⟩

  obtain ⟨f, hf0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  have hr : ∀ i, (f i).1 = i :=
    Nat.rec (by rw [hf0]; rfl) (fun i ih ↦ by rw [← (hcovby.1 (hf i)).2, ih])

  refine ⟨fun i ↦ by rw [← hr i]; exact (f i).2, fun i j hij ↦ ?_⟩
  convert (f.monotone hij).2 <;>
  simp [hr]

end Graded
