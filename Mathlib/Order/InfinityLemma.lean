/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Order.Cover
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Finite.Set

/-!
# Kőnig's infinity lemma

Kőnig's infinity lemma is most often stated as a graph theory result :
every infinite, locally finite connected graph contains an infinite path.
It has links to computability and proof theory, and
is often applied when the graph is a tree whose vertices encode some other types of object.

For applications of this form, it is convenient to state the lemma
in terms of covers in a well-founded order rather than a graph;
in this setting, the proof is almost trivial.
In this file, we prove the lemma in this order-theoretic way,
and also give a formulation that is convenient for applications in Ramsey theory.
We defer the graph-theoretic version of the statement for future work.

## Main Results

- `exists_seq_covby_of_forall_covby_finite` : Kőnig's lemma for well-founded orders.

- `exists_orderEmbedding_covby_of_forall_covby_finite` : Kőnig's lemma, where the sequence
    is given as an `OrderEmbedding` instead of a function.

- `exist_seq_forall_proj_of_forall_finite` : Kőnig's lemma applied to an order on a sigma-type
  `(i : ℕ) × (α i)`. Useful for applications in Ramsey theory.

TODO - Actually formulate the lemma as a statement about graphs.

-/

open Set

variable {α : Type*} [PartialOrder α] [WellFoundedLT α] {a b : α}

theorem exists_covby_of_lt (hab : a < b) : ∃ x, a ⋖ x ∧ x ≤ b := by
  refine ⟨WellFounded.min wellFounded_lt (Ioc a b) ⟨b, hab,rfl.le⟩, ?_⟩
  have hmem := (WellFounded.min_mem wellFounded_lt (Ioc a b) ⟨b, hab,rfl.le⟩)
  exact ⟨⟨hmem.1,fun c hac hlt ↦ WellFounded.not_lt_min wellFounded_lt
    (Ioc a b) ⟨b, hab,rfl.le⟩ ⟨hac, hlt.le.trans hmem.2⟩ hlt ⟩, hmem.2⟩

theorem exists_covby_infinite_Ici_of_infinite_Ici (ha : (Ici a).Infinite)
    (hfin : {x | a ⋖ x}.Finite) : ∃ b, a ⋖ b ∧ (Ici b).Infinite := by
  by_contra! h
  refine ((hfin.biUnion (t := Ici) (by simpa using h)).subset (fun b hb ↦ ?_)).not_infinite
    (ha.diff (finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := exists_covby_of_lt (hb.1.lt_of_ne (Ne.symm hb.2))
  exact mem_biUnion hax hxb

/-- The sequence proving the infinity lemma: each term is a pair `⟨a,h⟩`,
  where `h` is a proof that `Ici a` is infinite, and `a` covers the previous term. -/
noncomputable def konigSeq [OrderBot α] [Infinite α] (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (n : ℕ) : {a : α // (Ici a).Infinite } := match n with
  | 0    => ⟨⊥, by simp only [Ici_bot, infinite_univ]⟩
  | n+1  => let p := konigSeq hfin n
    ⟨_, ((exists_covby_infinite_Ici_of_infinite_Ici p.2 (hfin p.1)).choose_spec).2 ⟩

/-- Kőnig's infinity lemma : if each element in an infinite well-founded order with minimum
  is covered by only finitely many terms,
  then there is an infinite chain in which each element is covered by the next. -/
theorem exists_seq_covby_of_forall_covby_finite [OrderBot α] [Infinite α]
    (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) : ∃ f : ℕ → α, f 0 = ⊥ ∧ ∀ i, f i ⋖ f (i+1) :=
  ⟨fun i ↦ konigSeq hfin i, rfl, fun i ↦
    (exists_covby_infinite_Ici_of_infinite_Ici ((konigSeq hfin i).2 ) (hfin _)).choose_spec.1⟩

/-- The sequence given by Kőnig's lemma as an order embedding -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite [OrderBot α] [Infinite α]
    (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) : ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ ∀ i, f i ⋖ f (i+1) := by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i ↦ (hf.2 i).lt)), hf⟩

/-- A formulation of Kőnig's infinity lemma, useful in applications.
  Given a sequence `α 0, α 1, ...` of nonempty types with `α 0` a subsingleton,
  and a well-behaved family of projections `π : α j → α i` for all `i ≤ j`,
  if each term in each `α i` is the projection of only finitely many terms in `α (i+1)`,
  then we can find a sequence `(f 0 : α 0), (f 1 : α 1), ...`
  where `f i` is the projection of `f j` for all `i ≤ j`.

  In a typical application, the `α i` are function types with increasingly large domains,
  and `π hij (f : α j)` is the restriction of the domain of `f` to `α i`.
  In this case, the sequence given by the lemma is essentially a function whose domain
  is the limit of the `α i`.
  -/
theorem exist_seq_forall_proj_of_forall_finite {α : ℕ → Type*} [Subsingleton (α 0)]
    [∀ i, Nonempty (α i)] (π : {i j : ℕ} → (hij : i ≤ j) → α j → α i)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a, (π hij) (π hjk a) = π (hij.trans hjk) a)
    (π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a)
    (hfin : ∀ i a, {b : α (i+1) | π (Nat.le_add_right i 1) b = a}.Finite ):
    ∃ f : (i : ℕ) → (α i), ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by

  set αs := (i : ℕ) × (α i)

  let _ : PartialOrder (αs) := {
    le := fun a b ↦ ∃ h, π h b.2 = a.2
    le_refl := fun a ↦ ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' ↦ ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by
      rintro ⟨i,a⟩ ⟨j,b⟩ ⟨hij : i ≤ j, hab : π hij b = a⟩ ⟨hji : j ≤ i, hba : π hji a = b⟩
      cases hij.antisymm hji
      ext; rfl
      simp only [heq_eq_eq]
      rwa [← π_refl a] }

  have hsm : StrictMono (fun (x : αs) ↦ x.1) := by
    rintro ⟨i,a⟩ ⟨j,b⟩
    simp only [lt_iff_le_and_ne, forall_exists_index, ne_eq, and_imp,
      (show ∀ a b : αs, a ≤ b ↔ ∃ h, π h b.2 = a.2 from fun _ _ ↦ Iff.rfl)]
    rintro h (rfl : π h b = a) hne; refine ⟨h, ?_⟩
    rintro rfl
    simp [π_refl] at hne

  have _ := WellFoundedLT.of_strictMono hsm

  have hcovby : ∀ {a b : αs}, a ⋖ b ↔ a ≤ b ∧ a.1 + 1 = b.1 := by
    simp_rw [covBy_iff_lt_and_eq_or_eq]
    refine @fun a b ↦ ⟨fun ⟨h,h'⟩ ↦ ⟨h.le, ?_⟩, fun ⟨h,h'⟩ ↦ ⟨h.lt_of_ne ?_, fun c hac hcb ↦ ?_⟩⟩
    · obtain (h1 | h1) := h'
        ⟨_, π (hsm h) b.2⟩ ⟨Nat.le_add_right a.1 1, by simp [π_trans, h.le.2]⟩ ⟨hsm h, by simp⟩
      · apply_fun (fun x ↦ x.1) at h1; simp at h1
      rw [← h1]
    · rintro rfl; simp at h'
    obtain (h_eq | hlt) := (hsm.monotone hac).eq_or_lt
    · exact .inl <| hac.antisymm' ⟨h_eq.symm.le, by simp [← hac.2, π_refl, π_trans]⟩
    have hbc := (h'.symm.le.trans <| Nat.add_one_le_iff.2 hlt)
    exact .inr <| hcb.antisymm ⟨hbc, by simp [← hcb.2, π_trans, π_refl]⟩

  let _ : OrderBot αs := {
    bot := ⟨0, Classical.arbitrary _⟩
    bot_le := fun a ↦ by
      rw [← Subsingleton.elim (α := α 0) (π (zero_le _) a.2) (Classical.arbitrary _)]
      exact ⟨zero_le _, by simp [π_refl]⟩ }

  have hfin : ∀ (a : αs), {x | a ⋖ x}.Finite := fun a ↦ by
    simp_rw [hcovby]
    set f : {x // a ≤ x ∧ a.1 + 1 = x.1} → α (a.1+1) := fun x ↦ π x.2.2.le x.1.2
    have : Finite (range f) := by
      refine (hfin a.1 a.2).subset ?_
      rintro _ ⟨⟨⟨i,x⟩,hx,(rfl : a.1 + 1 = i)⟩,h,rfl⟩
      simp [f, π_refl, hx.2]
    apply Finite.of_injective_finite_range (f := f)
    rintro ⟨⟨i,b⟩, ⟨hb, (rfl : a.1 + 1 = i)⟩⟩ ⟨⟨j,c⟩, ⟨hc, (rfl : a.1 +1 = j)⟩⟩ h
    ext; rfl
    simpa [π_refl, f] using h

  obtain ⟨f, hf0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite hfin
  have hr : ∀ i, (f i).1 = i :=
    Nat.recAux (by rw [hf0]; rfl) (fun i ih ↦ by rw [← (hcovby.1 (hf i)).2, ih])

  refine ⟨fun i ↦ by rw [← hr i]; exact (f i).2, fun i j hij ↦ ?_⟩
  convert (f.monotone hij).2 <;>
  simp [hr]
