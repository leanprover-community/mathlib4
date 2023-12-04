/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Separation
/-!

# Clopen subsets in cartesian products

In general, a clopen subset in a cartesian product of topological spaces cannot be written as a
union of "clopen boxes", i.e. products of clopen subsets of the components (see
[buzyakovaClopenBox] for counterexamples).

However, when one of the factors is compact, a clopen subset can be written as such a union.
Our argument in `exists_clopen_box` follows the one given in [buzyakovaClopenBox].

We deduce that in a product of compact spaces, a clopen subset is a finite union of clopen boxes,
and use that to prove that the property of having finitely many clopens is preserved by taking
cartesian products of compact spaces (this is relevant to the theory of light profinite sets).

## References

- [buzyakovaClopenBox]: *On clopen sets in Cartesian products*, 2001.
- [engelking1989]: *General Topology*, 1989.

-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace Y] (W : Set (X × Y)) (hW : IsClopen W)

theorem exists_clopen_box (a : X) (b : Y) (h : (a, b) ∈ W) :
    ∃ (U : Set X) (V : Set Y) (_ : IsClopen U) (_ : IsClopen V),
    a ∈ U ∧ b ∈ V ∧ (U ×ˢ V : Set (X × Y)) ⊆ W := by
  let V : Set Y := {y | (a, y) ∈ W}
  let U : Set X := {x | ({x} : Set X) ×ˢ V ⊆ W}
  have hp : Continuous (fun (y : Y) ↦ (a, y)) := Continuous.Prod.mk _
  have hVC : IsCompact V := (hW.2.preimage hp).isCompact
  have hUV : U ×ˢ V ⊆ W := by
    intro ⟨w₁, w₂⟩ hw
    rw [Set.prod_mk_mem_set_prod_eq] at hw
    simp only [Set.mem_setOf_eq] at hw
    apply hw.1
    simp only [Set.singleton_prod, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq, true_and,
      exists_eq_right]
    exact hw.2
  -- The hard part of the proof is to show that `U` is clopen. The fact that it is closed is proved
  -- in [buzyakovaClopenBox], Lemma 2, and the fact that it is open can be deduced from the proof of
  -- [engelking1989], Lemma 3.1.15.
  refine ⟨U, V, ⟨?_, ?_⟩, ⟨hW.1.preimage hp, hW.2.preimage hp⟩, ?_, h, hUV⟩
  -- `U` is open:
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [mem_nhds_iff]
    -- We show that `U` contains an open neighbourhood of each of its points.
    have := hW.1
    rw [isOpen_prod_iff] at this
    -- The fact that `W` is open gives an open cover of the compact set `V`, together with a
    -- collection of open neighbourhoods of `x`, such that the collection of products is contained
    -- in `W`. We extract a finite subcover and the desired open neighbourhood of `x` is the
    -- (finite, thus open) intersection of the corresponding neighbourhoods.
    rw [isCompact_iff_finite_subcover] at hVC
    specialize @hVC V
      (fun (v : V) ↦ (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose) ?_ ?_
    · intro v
      exact (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose_spec.2.1
    · intro v hv
      rw [Set.mem_iUnion]
      exact ⟨⟨v, hv⟩, (this x v (hUV (Set.mk_mem_prod hx hv))).choose_spec.choose_spec.2.2.2.1⟩
    obtain ⟨I, hI⟩ := hVC
    let t := ⋂ i ∈ I, (fun v ↦ (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose) i
    refine ⟨t, ?_, ?_, ?_⟩
    · intro x' hx'
      have hxt : {x'} ×ˢ V ⊆ t ×ˢ V := by
        rw [Set.prod_subset_prod_iff]
        left
        exact ⟨Set.singleton_subset_iff.mpr hx' , subset_refl _⟩
      refine subset_trans hxt ?_
      intro ⟨z, w⟩ hz
      rw [Set.mem_prod] at hz
      have hz' := hI hz.2
      rw [Set.mem_iUnion] at hz'
      obtain ⟨i, hi⟩ := hz'
      rw [Set.mem_iUnion] at hi
      obtain ⟨hhi, hi⟩ := hi
      apply (this x i.val (hUV (Set.mk_mem_prod hx i.prop))).choose_spec.choose_spec.2.2.2.2
      rw [Set.mem_prod]
      refine ⟨?_, hi⟩
      rw [Set.mem_iInter] at hz
      have hhz := hz.1 i
      rw [Set.mem_iInter] at hhz
      exact hhz hhi
    · apply Set.Finite.isOpen_biInter (Set.Finite.ofFinset I (fun _ ↦ Iff.rfl))
      intro v _
      exact (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose_spec.1
    · rw [Set.mem_iInter]
      intro v
      rw [Set.mem_iInter]
      intro
      exact (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose_spec.2.2.1
  -- `U` is closed. This is a fairly simple calculation using the fact that `W` is closed and the
  -- definition of `U`.
  · apply isClosed_of_closure_subset
    intro x hx
    have hhx : {x} ×ˢ V ⊆ (closure U) ×ˢ V := by
      rw [Set.prod_subset_prod_iff]
      left
      exact ⟨Set.singleton_subset_iff.mpr hx , subset_refl _⟩
    refine subset_trans hhx ?_
    have hU : (closure U) ×ˢ V ⊆ closure (U ×ˢ V) := by
      rw [closure_prod_eq, Set.prod_subset_prod_iff]
      left
      exact ⟨subset_refl _, subset_closure⟩
    refine subset_trans hU ?_
    refine subset_trans ?_ hW.2.closure_subset
    exact closure_mono hUV
  -- `a ∈ U`
  · intro ⟨w₁, w₂⟩ hw
    rw [Set.prod_mk_mem_set_prod_eq] at hw
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hw
    rw [hw.1]
    exact hw.2

variable [CompactSpace X]

open Classical in
theorem exists_finset_clopen_box :
    ∃ (I : Finset ({s : Set X // IsClopen s} × {t : Set Y // IsClopen t})),
    W = ⋃ (i ∈ I), i.1.val ×ˢ i.2.val := by
  have hW' := hW.2.isCompact
  rw [isCompact_iff_finite_subcover] at hW'
  specialize hW' (fun (⟨⟨a, b⟩, hab⟩ : W) ↦ (exists_clopen_box W hW a b hab).choose ×ˢ
    (exists_clopen_box W hW a b hab).choose_spec.choose) ?_ ?_
  · intro ⟨⟨a, b⟩, hab⟩
    exact IsOpen.prod (exists_clopen_box W hW a b hab).choose_spec.choose_spec.1.1
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.1.1
  · intro ⟨a, b⟩ hab
    rw [Set.mem_iUnion]
    use ⟨⟨a, b⟩, hab⟩
    rw [Set.mem_prod]
    exact ⟨(exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.2.1,
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.2.2.1⟩
  · obtain ⟨I, hI⟩ := hW'
    let fI : W → {s : Set X // IsClopen s} × {t : Set Y // IsClopen t} :=
      fun (⟨⟨a, b⟩, hab⟩ : W) ↦ (⟨(exists_clopen_box W hW a b hab).choose,
        (exists_clopen_box W hW a b hab).choose_spec.choose_spec.1⟩,
        ⟨(exists_clopen_box W hW a b hab).choose_spec.choose,
        (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.1⟩)
    use (fI '' I).toFinset
    ext x
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · replace h := hI h
      rw [Set.mem_iUnion] at h ⊢
      obtain ⟨i, hi⟩ := h
      use fI i
      rw [Set.mem_iUnion] at hi ⊢
      obtain ⟨hi, hi'⟩ := hi
      have hfi : fI i ∈ (fI '' I).toFinset := by
        rw [Set.mem_toFinset]
        exact Set.mem_image_of_mem fI hi
      use hfi
    · rw [Set.mem_iUnion] at h
      obtain ⟨i, hi⟩ := h
      rw [Set.mem_iUnion] at hi
      obtain ⟨hi, h⟩ := hi
      rw [Set.mem_toFinset] at hi
      obtain ⟨w, hw⟩ := hi
      apply (exists_clopen_box W hW w.val.1 w.val.2 w.prop).choose_spec.choose_spec.2.2.2.2
      rw [← hw.2] at h
      exact h

instance countable_clopens_prod [Countable {s : Set X // IsClopen s}]
    [Countable {t : Set Y // IsClopen t}] : Countable {w : Set (X × Y) // IsClopen w} := by
  refine @Function.Surjective.countable
    (Finset ({s : Set X // IsClopen s} × {t : Set Y // IsClopen t})) _ _
    (fun I ↦ ⟨⋃ (i ∈ I), i.1.val ×ˢ i.2.val, ?_⟩) ?_
  · apply Set.Finite.isClopen_biUnion (Set.Finite.ofFinset I (fun _ ↦ Iff.rfl))
    intro i _
    exact IsClopen.prod i.1.2 i.2.2
  · intro ⟨W, hW⟩
    simp only [Subtype.mk.injEq]
    exact ⟨(exists_finset_clopen_box W hW).choose, (exists_finset_clopen_box W hW).choose_spec.symm⟩
