/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Closeds

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

open Function Set Filter TopologicalSpace
open scoped Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma isOpen_setOf_mapsTo_isCompact {f : X → Y → Z} (hf : Continuous (uncurry f))
    {K : Set Y} (hK : IsCompact K) {W : Set Z} (hW : IsOpen W) : IsOpen {x | MapsTo (f x) K W} := by
  simpa only [mapsTo']
    using (ContinuousMap.isOpen_gen hK hW).preimage (ContinuousMap.curry ⟨_, hf⟩).continuous

lemma isClosed_setOf_mapsTo {f : X → Y → Z} (hf : ∀ y, Continuous (f · y)) (s : Set Y) {t : Set Z}
    (ht : IsClosed t) : IsClosed {x | MapsTo (f x) s t} := by
  simpa only [MapsTo, setOf_forall] using isClosed_biInter fun y _ ↦ ht.preimage (hf y)

lemma isClopen_setOf_mapsTo_isCompact {f : X → Y → Z} (hf : Continuous (uncurry f))
    {K : Set Y} (hK : IsCompact K) {U : Set Z} (hU : IsClopen U) :
    IsClopen {x | MapsTo (f x) K U} :=
  ⟨isOpen_setOf_mapsTo_isCompact hf hK hU.isOpen,
    isClosed_setOf_mapsTo (fun y ↦ hf.comp (Continuous.Prod.mk_left y)) K hU.isClosed⟩

variable [CompactSpace Y]

theorem TopologicalSpace.Clopens.exists_prod_subset (W : Clopens (X × Y)) {a : X × Y} (h : a ∈ W) :
    ∃ U : Clopens X, a.1 ∈ U ∧ ∃ V : Clopens Y, a.2 ∈ V ∧ U ×ˢ V ≤ W := by
  have hp : Continuous (fun y : Y ↦ (a.1, y)) := Continuous.Prod.mk _
  let V : Set Y := {y | (a.1, y) ∈ W}
  have hV : IsCompact V := (W.2.2.preimage hp).isCompact
  let U : Set X := {x | MapsTo (Prod.mk x) V W}
  have hUV : U ×ˢ V ⊆ W := fun ⟨_, _⟩ hw ↦ hw.1 hw.2
  exact ⟨⟨U, isClopen_setOf_mapsTo_isCompact (f := Prod.mk) continuous_id hV W.2⟩,
    by simp [MapsTo], ⟨V, W.2.preimage hp⟩, h, hUV⟩

variable [CompactSpace X]

/-- Every clopen set in a product of two compact spaces
is a union of finitely many clopen boxes. -/
theorem TopologicalSpace.Clopens.exists_finset_eq_sup_prod (W : Clopens (X × Y)) :
    ∃ (I : Finset (Clopens X × Clopens Y)), W = I.sup fun i ↦ i.1 ×ˢ i.2 := by
  choose! U hxU V hxV hUV using fun x ↦ W.exists_prod_subset (a := x)
  rcases W.2.2.isCompact.elim_nhds_subcover (fun x ↦ U x ×ˢ V x) (fun x hx ↦
    (U x ×ˢ V x).2.isOpen.mem_nhds ⟨hxU x hx, hxV x hx⟩) with ⟨I, hIW, hWI⟩
  classical
  use I.image fun x ↦ (U x, V x)
  rw [Finset.sup_image]
  refine le_antisymm (fun x hx ↦ ?_) (Finset.sup_le fun x hx ↦ ?_)
  · rcases Set.mem_iUnion₂.1 (hWI hx) with ⟨i, hi, hxi⟩
    exact SetLike.le_def.1 (Finset.le_sup hi) hxi
  · exact hUV _ <| hIW _ hx

instance TopologicalSpace.Clopens.countable_prod [Countable (Clopens X)]
    [Countable (Clopens Y)] : Countable (Clopens (X × Y)) :=
  have : Surjective fun I : Finset (Clopens X × Clopens Y) ↦ I.sup fun i ↦ i.1 ×ˢ i.2 := fun W ↦ by
    simpa only [eq_comm] using W.exists_finset_eq_sup_prod
  this.countable
