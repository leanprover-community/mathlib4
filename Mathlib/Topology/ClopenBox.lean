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
and use that to prove that the property of having countably many clopens is preserved by taking
cartesian products of compact spaces (this is relevant to the theory of light profinite sets).

## References

- [buzyakovaClopenBox]: *On clopen sets in Cartesian products*, 2001.
- [engelking1989]: *General Topology*, 1989.

-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isOpen_set_of_singleton_prod_contained {V : Set Y} (hV : IsCompact V) {W : Set (X × Y)}
    (hW : IsOpen W) : IsOpen {x : X | {x} ×ˢ V ⊆ W} := by
  -- This argument is a version of [engelking1989], Lemma 3.1.15
  let U := {x : X | {x} ×ˢ V ⊆ W}
  have hUV : U ×ˢ V ⊆ W := fun ⟨_, _⟩ hw ↦ hw.1 (by simpa using hw.2)
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds_iff]
  -- We show that `U` contains an open neighbourhood of each of its points.
  rw [isOpen_prod_iff] at hW
  -- The fact that `W` is open gives an open cover of the compact set `V`, together with a
  -- collection of open neighbourhoods of `x`, such that the collection of products is contained
  -- in `W`. We extract a finite subcover and the desired open neighbourhood of `x` is the
  -- (finite, thus open) intersection of the corresponding neighbourhoods.
  rw [isCompact_iff_finite_subcover] at hV
  obtain ⟨I, hI⟩ := hV
    (fun (v : V) ↦ (hW x v.val (hUV ⟨hx, v.prop⟩)).choose_spec.choose)
    (fun v ↦ (hW x v.val (hUV ⟨hx, v.prop⟩)).choose_spec.choose_spec.2.1)
    (fun v hv ↦ Set.mem_iUnion.mpr ⟨⟨v, hv⟩,
      (hW x v (hUV ⟨hx, hv⟩)).choose_spec.choose_spec.2.2.2.1⟩)
  let t := ⋂ i ∈ I, (fun v ↦ (hW x v.val (hUV ⟨hx, v.prop⟩)).choose) i
  refine ⟨t, ?_, ?_, ?_⟩
  -- The intersection is indeed contained in `U`:
  · intro x' hx'
    have hxt : {x'} ×ˢ V ⊆ t ×ˢ V := fun _ h ↦ ⟨Set.singleton_subset_iff.mpr hx' h.1, h.2⟩
    refine subset_trans hxt ?_
    intro ⟨z, w⟩ ⟨hz, hw⟩
    replace hw := hI hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨i, hi, hw⟩ := hw
    apply (hW x i.val (hUV ⟨hx, i.prop⟩)).choose_spec.choose_spec.2.2.2.2
    refine ⟨?_, hw⟩
    simp only [Set.mem_iInter] at hz
    exact hz _ hi
  -- The intersection is open:
  · exact Set.Finite.isOpen_biInter (Set.Finite.ofFinset I (fun _ ↦ Iff.rfl))
      fun v _ ↦ (hW x v.val (hUV ⟨hx, v.prop⟩)).choose_spec.choose_spec.1
  -- The intersection contains `x`
  · simp only [Set.mem_iInter]
    exact fun v _ ↦ (hW x v.val (hUV ⟨hx, v.prop⟩)).choose_spec.choose_spec.2.2.1

variable [CompactSpace Y] (W : Set (X × Y)) (hW : IsClopen W)

theorem exists_clopen_box (a : X) (b : Y) (h : (a, b) ∈ W) :
    ∃ (U : Set X) (V : Set Y) (_ : IsClopen U) (_ : IsClopen V),
    a ∈ U ∧ b ∈ V ∧ (U ×ˢ V : Set (X × Y)) ⊆ W := by
  let V : Set Y := {y | (a, y) ∈ W}
  let U : Set X := {x | {x} ×ˢ V ⊆ W}
  have hp : Continuous (fun (y : Y) ↦ (a, y)) := Continuous.Prod.mk _
  have hUV : U ×ˢ V ⊆ W := fun ⟨_, _⟩ hw ↦ hw.1 (by simpa using hw.2)
  refine ⟨U, V, ⟨isOpen_set_of_singleton_prod_contained (hW.2.preimage hp).isCompact hW.1, ?_⟩,
    ⟨hW.1.preimage hp, hW.2.preimage hp⟩, fun ⟨_, _⟩ hw ↦ ?_, h, hUV⟩
  -- `U` is closed. This is a fairly simple calculation using the fact that `W` is closed and the
  -- definition of `U`. It is the proof of [buzyakovaClopenBox], Lemma 2.
  · apply isClosed_of_closure_subset
    intro x hx
    have hxV : {x} ×ˢ V ⊆ (closure U) ×ˢ V :=  fun _ h ↦ ⟨Set.singleton_subset_iff.mpr hx h.1, h.2⟩
    have hU : (closure U) ×ˢ V ⊆ closure (U ×ˢ V) := fun _ h ↦ by
      rw [closure_prod_eq]
      exact ⟨h.1, subset_closure h.2⟩
    exact subset_trans hxV (subset_trans hU (subset_trans (closure_mono hUV) hW.2.closure_subset))
  · simp only [Set.prod_mk_mem_set_prod_eq, Set.mem_singleton_iff, Set.mem_setOf_eq] at hw
    simpa [hw.1] using hw

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
    exact ⟨⟨⟨a, b⟩, hab⟩, ⟨(exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.2.1,
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.2.2.1⟩⟩
  obtain ⟨I, hI⟩ := hW'
  let fI : W → {s : Set X // IsClopen s} × {t : Set Y // IsClopen t} :=
    fun (⟨⟨a, b⟩, hab⟩ : W) ↦ (⟨(exists_clopen_box W hW a b hab).choose,
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.1⟩,
      ⟨(exists_clopen_box W hW a b hab).choose_spec.choose,
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.1⟩)
  refine ⟨(fI '' I).toFinset, ?_⟩
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · replace h := hI h
    simp only [Set.mem_iUnion] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    refine ⟨fI i, ?_, h⟩
    rw [Set.mem_toFinset]
    exact Set.mem_image_of_mem fI hi
  · simp only [Set.mem_iUnion, Set.mem_toFinset] at h
    obtain ⟨s, ⟨w, hw⟩, h⟩ := h
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
