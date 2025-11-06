/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Grade
import Mathlib.Tactic.ApplyFun

/-!
# Kőnig's infinity lemma

Kőnig's infinity lemma is most often stated as a graph theory result:
every infinite, locally finite connected graph contains an infinite path.
It has links to computability and proof theory, and it has a number of formulations.

In practice, most applications are not to an abstract graph,
but to a concrete collection of objects that are organized in a graph-like way,
often where the graph is a rooted tree representing a graded order.
In fact, the lemma is most easily stated and proved
in terms of covers in a strongly atomic order rather than a graph;
in this setting, the proof is almost trivial.

A common formulation of Kőnig's lemma is in terms of directed systems,
with the grading explicitly represented using an `ℕ`-indexed family of types,
which we also provide in this module.
This is a specialization of the much more general `nonempty_sections_of_finite_cofiltered_system`,
which goes through topology and category theory,
but here it is stated and proved independently with much fewer dependencies.

We leave the explicitly graph-theoretic version of the statement as TODO.

## Main Results

* `exists_seq_covby_of_forall_covby_finite` : Kőnig's lemma for strongly atomic orders.

* `exists_orderEmbedding_covby_of_forall_covby_finite` : Kőnig's lemma, where the sequence
  is given as an `OrderEmbedding` instead of a function.

* `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot` : Kőnig's lemma where the sequence
  starts at the minimum of an infinite type.

* `exist_seq_forall_proj_of_forall_finite` : Kőnig's lemma for inverse systems,
  proved using the above applied to an order on a sigma-type `(i : ℕ) × α i`.

## TODO

Formulate the lemma as a statement about graphs.

-/

open Set
section Sequence

variable {α : Type*} [PartialOrder α] [IsStronglyAtomic α] {b : α}

/-- **Kőnig's infinity lemma** : if each element in a strongly atomic order
is covered by only finitely many others, and `b` is an element with infinitely many things above it,
then there is a sequence starting with `b` in which each element is covered by the next. -/
theorem exists_seq_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ → α, f 0 = b ∧ ∀ i, f i ⋖ f (i + 1) :=
  let h := fun a : {a : α // (Ici a).Infinite} ↦
    exists_covby_infinite_Ici_of_infinite_Ici a.2 (hfin a)
  let ks : ℕ → {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩ fun _ a ↦ ⟨_, (h a).choose_spec.2⟩
  ⟨fun i ↦ (ks i).1, by simp [ks], fun i ↦ by simpa using (h (ks i)).choose_spec.1⟩

/-- The sequence given by Kőnig's lemma as an order embedding -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ ↪o α, f 0 = b ∧ ∀ i, f i ⋖ f (i + 1) := by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i ↦ (hf.2 i).lt)), hf⟩

/-- A version of Kőnig's lemma where the sequence starts at the minimum of an infinite order. -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite_of_bot [OrderBot α] [Infinite α]
    (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) : ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ ∀ i, f i ⋖ f (i + 1) :=
  exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

theorem GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite
    [GradeMinOrder ℕ α] [OrderBot α] [Infinite α] (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) :
    ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ (∀ i, f i ⋖ f (i + 1)) ∧ ∀ i, grade ℕ (f i) = i := by
  obtain ⟨f, h0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  refine ⟨f, h0, hf, fun i ↦ ?_⟩
  induction i with
  | zero => simp [h0]
  | succ i ih => simpa [Order.covBy_iff_add_one_eq, ih, eq_comm] using CovBy.grade ℕ <| hf i

end Sequence

section Graded

/-- A formulation of Kőnig's infinity lemma, useful in applications.
Given a sequence `α 0, α 1, ...` of nonempty types with `α 0` finite,
and a well-behaved family of projections `π : α j → α i` for all `i ≤ j`,
if each term in each `α i` is the projection of only finitely many terms in `α (i+1)`,
then we can find a sequence `(f 0 : α 0), (f 1 : α 1), ...`
where `f i` is the projection of `f j` for all `i ≤ j`.

In a typical application, the `α i` are function types with increasingly large domains,
and `π hij (f : α j)` is the restriction of the domain of `f` to that of `α i`.
In this case, the sequence given by the lemma is essentially a function whose domain
is the limit of the `α i`.

See also `nonempty_sections_of_finite_cofiltered_system`. -/
theorem exists_seq_forall_proj_of_forall_finite {α : ℕ → Type*} [Finite (α 0)] [∀ i, Nonempty (α i)]
    (π : {i j : ℕ} → (hij : i ≤ j) → α j → α i)
    (π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a, π hij (π hjk a) = π (hij.trans hjk) a)
    (hfin : ∀ i a, {b : α (i+1) | π (Nat.le_add_right i 1) b = a}.Finite) :
    ∃ f : (i : ℕ) → α i, ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by
  set αs := (i : ℕ) × α i
  let _ : PartialOrder αs := {
    le := fun a b ↦ ∃ h, π h b.2 = a.2
    le_refl := fun a ↦ ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' ↦ ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by
      rintro ⟨i, a⟩ ⟨j, b⟩ ⟨hij : i ≤ j, hab : π hij b = a⟩ ⟨hji : j ≤ i, hba : π hji a = b⟩
      obtain rfl := hij.antisymm hji
      rw [show a = b by rwa [π_refl] at hba] }
  have hcovby : ∀ {a b : αs}, a ⋖ b ↔ a ≤ b ∧ a.1 + 1 = b.1 := by
    simp only [αs, covBy_iff_lt_and_eq_or_eq, lt_iff_le_and_ne, ne_eq, Sigma.forall, and_assoc,
      and_congr_right_iff, or_iff_not_imp_left]
    rintro i a j b ⟨h : i ≤ j, rfl : π h b = a⟩
    refine ⟨fun ⟨hne, h'⟩ ↦ ?_, ?_⟩
    · have hle' : i + 1 ≤ j := h.lt_of_ne <| by rintro rfl; simp [π_refl] at hne
      exact congr_arg Sigma.fst <| h' (i + 1) (π hle' b) ⟨by simp, by rw [π_trans]⟩ ⟨hle', by simp⟩
        (fun h ↦ by simp at h)
    rintro rfl
    refine ⟨fun h ↦ by simp at h, ?_⟩
    rintro j c ⟨hij : i ≤ j, hcb : π _ c = π _ b⟩ ⟨hji : j ≤ i + 1, rfl : π hji b = c⟩ hne
    replace hne := show i ≠ j by rintro rfl; contradiction
    obtain rfl := hji.antisymm (hij.lt_of_ne hne)
    rw [π_refl]
  have : IsStronglyAtomic αs := by
    simp_rw [isStronglyAtomic_iff, lt_iff_le_and_ne, hcovby]
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨⟨hij : i ≤ j, h2 : π hij b = a⟩, hne⟩
    have hle : i + 1 ≤ j := hij.lt_of_ne (by rintro rfl; simp [← h2, π_refl] at hne)
    exact ⟨⟨_, π hle b⟩, ⟨⟨by simp, by rw [π_trans, ← h2]⟩, by simp⟩, ⟨hle, by simp⟩⟩
  obtain ⟨a₀, ha₀, ha₀inf⟩ : ∃ a₀ : αs, a₀.1 = 0 ∧ (Ici a₀).Infinite := by
    obtain ⟨a₀, ha₀⟩ := Finite.exists_infinite_fiber (fun (a : αs) ↦ π (zero_le a.1) a.2)
    refine ⟨⟨0, a₀⟩, rfl, (infinite_coe_iff.1 ha₀).mono ?_⟩
    simp only [αs, subset_def, mem_preimage, mem_singleton_iff, mem_Ici, Sigma.forall]
    exact fun i x h ↦ ⟨zero_le i, h⟩
  have hfin : ∀ (a : αs), {x | a ⋖ x}.Finite := by
    refine fun ⟨i, a⟩ ↦ ((hfin i a).image (fun b ↦ ⟨_, b⟩)).subset ?_
    simp only [αs, hcovby, subset_def, mem_setOf_eq, mem_image, and_imp, Sigma.forall]
    exact fun j b ⟨_, _⟩ hj ↦ ⟨π hj.le b, by rwa [π_trans], by cases hj; rw [π_refl]⟩
  obtain ⟨f, hf0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite hfin ha₀inf
  have hr : ∀ i, (f i).1 = i :=
    Nat.rec (by rw [hf0, ha₀]) (fun i ih ↦ by rw [← (hcovby.1 (hf i)).2, ih])
  refine ⟨fun i ↦ by rw [← hr i]; exact (f i).2, fun i j hij ↦ ?_⟩
  convert (f.monotone hij).2 <;>
  simp [hr]

end Graded
