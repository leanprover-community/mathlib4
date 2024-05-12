/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Small.Basic

/-!
# Results about `Small` on coerced sets
-/

universe u v w

theorem small_subset {α : Type v} {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  let f : t → s := fun x => ⟨x, hts x.prop⟩
  @small_of_injective _ _ _ f fun _ _ hxy => Subtype.ext (Subtype.mk.inj hxy)
#align small_subset small_subset

instance small_range {α : Type v} {β : Type w} (f : α → β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.surjective_onto_range
#align small_range small_range

instance small_image {α : Type v} {β : Type w} (f : α → β) (S : Set α) [Small.{u} S] :
    Small.{u} (f '' S) :=
  small_of_surjective Set.surjective_onto_image
#align small_image small_image

instance small_union {α : Type v} (s t : Set α) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s ∪ t : Set α) := by
  rw [← Subtype.range_val (s := s), ← Subtype.range_val (s := t), ← Set.Sum.elim_range]
  infer_instance

instance small_iUnion {α : Type v} {ι : Type w} [Small.{u} ι] (s : ι → Set α)
    [∀ i, Small.{u} (s i)] : Small.{u} (⋃ i, s i) :=
  small_of_surjective <| Set.sigmaToiUnion_surjective _

instance small_sUnion {α : Type v} (s : Set (Set α)) [Small.{u} s] [∀ t : s, Small.{u} t] :
    Small.{u} (⋃₀ s) :=
  Set.sUnion_eq_iUnion ▸ small_iUnion _
