/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Timothy Carlin-Burns
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Logic.Small.Basic

/-!
# Results about `Small` on coerced sets
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u u1 u2 u3 u4

variable {α : Type u1} {β : Type u2} {γ : Type u3} {ι : Type u4}

theorem small_subset {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  small_of_injective (Set.inclusion_injective hts)

instance small_powerset (s : Set α) [Small.{u} s] : Small.{u} (𝒫 s) :=
  small_map (Equiv.Set.powerset s)

instance small_setProd (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s ×ˢ t : Set (α × β)) :=
  small_of_injective (Equiv.Set.prod s t).injective

instance small_setPi {β : α → Type u2} (s : (a : α) → Set (β a))
    [Small.{u} α] [∀ a, Small.{u} (s a)] : Small.{u} (Set.pi Set.univ s) :=
  small_of_injective (Equiv.Set.univPi s).injective

instance small_range (f : α → β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.rangeFactorization_surjective

instance small_image (f : α → β) (s : Set α) [Small.{u} s] :
    Small.{u} (f '' s) :=
  small_of_surjective Set.imageFactorization_surjective

instance small_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] :
    Small.{u} (Set.image2 f s t) := by
  rw [← Set.image_uncurry_prod]
  infer_instance

theorem small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α :=
  small_congr <| Equiv.Set.univ α

instance small_univ [h : Small.{u} α] : Small.{u} (@Set.univ α) :=
  small_univ_iff.2 h

instance small_union (s t : Set α) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s ∪ t : Set α) := by
  rw [← Subtype.range_val (s := s), ← Subtype.range_val (s := t), ← Set.Sum.elim_range]
  infer_instance

instance small_iUnion [Small.{u} ι] (s : ι → Set α)
    [∀ i, Small.{u} (s i)] : Small.{u} (⋃ i, s i) :=
  small_of_surjective <| Set.sigmaToiUnion_surjective _

instance small_sUnion (s : Set (Set α)) [Small.{u} s] [∀ t : s, Small.{u} t] :
    Small.{u} (⋃₀ s) :=
  Set.sUnion_eq_iUnion ▸ small_iUnion _

instance small_biUnion (s : Set ι) [Small.{u} s]
    (f : (i : ι) → i ∈ s → Set α) [∀ i hi, Small.{u} (f i hi)] : Small.{u} (⋃ i, ⋃ hi, f i hi) :=
  Set.biUnion_eq_iUnion s f ▸ small_iUnion _

instance small_insert (x : α) (s : Set α) [Small.{u} s] :
    Small.{u} (insert x s : Set α) :=
  Set.insert_eq x s ▸ small_union.{u} {x} s

instance small_diff (s t : Set α) [Small.{u} s] : Small.{u} (s \ t : Set α) :=
  small_subset (Set.diff_subset)

instance small_sep (s : Set α) (P : α → Prop) [Small.{u} s] :
    Small.{u} { x | x ∈ s ∧ P x} :=
  small_subset (Set.sep_subset s P)

instance small_inter_of_left (s t : Set α) [Small.{u} s] :
    Small.{u} (s ∩ t : Set α) :=
  small_subset Set.inter_subset_left

instance small_inter_of_right (s t : Set α) [Small.{u} t] :
    Small.{u} (s ∩ t : Set α) :=
  small_subset Set.inter_subset_right

theorem small_iInter (s : ι → Set α) (i : ι)
    [Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  small_subset (Set.iInter_subset s i)

instance small_iInter' [Nonempty ι] (s : ι → Set α)
    [∀ i, Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  let ⟨i⟩ : Nonempty ι := inferInstance
  small_iInter s i

theorem small_sInter {s : Set (Set α)} {t : Set α} (ht : t ∈ s)
    [Small.{u} t] : Small.{u} (⋂₀ s) :=
  Set.sInter_eq_iInter ▸ small_iInter _ ⟨t, ht⟩

instance small_sInter' {s : Set (Set α)} [Nonempty s]
    [∀ t : s, Small.{u} t] : Small.{u} (⋂₀ s) :=
  let ⟨t⟩ : Nonempty s := inferInstance
  small_sInter t.prop

theorem small_biInter {s : Set ι} {i : ι} (hi : i ∈ s)
    (f : (i : ι) → i ∈ s → Set α) [Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  Set.biInter_eq_iInter s f ▸ small_iInter _ ⟨i, hi⟩

instance small_biInter' (s : Set ι) [Nonempty s]
    (f : (i : ι) → i ∈ s → Set α) [∀ i hi, Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  let ⟨t⟩ : Nonempty s := inferInstance
  small_biInter t.prop f

theorem small_empty : Small.{u} (∅ : Set α) :=
  inferInstance

theorem small_single (x : α) : Small.{u} ({x} : Set α) :=
  inferInstance

theorem small_pair (x y : α) : Small.{u} ({x, y} : Set α) :=
  inferInstance
