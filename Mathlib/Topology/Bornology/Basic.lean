/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Order.Filter.Cofinite

#align_import topology.bornology.basic from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Basic theory of bornology

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter.  This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `Bornology.ofBounded`,
`IsBounded.union`, `IsBounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `Bornology α`: a class consisting of `cobounded : Filter α` and a proof that this filter
  contains the `cofinite` filter.
- `Bornology.IsCobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : Set α`, one should prefer `Bornology.IsCobounded s` over `s ∈ cobounded α`.
- `bornology.IsBounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `Bornology.IsBounded s` over `sᶜ ∈ cobounded α`.
- `BoundedSpace α`: a class extending `Bornology α` with the condition
  `Bornology.IsBounded (Set.univ : Set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/


open Set Filter

variable {ι α β : Type*}

/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `Bornology.ofBounded`
and `Bornology.ext_iff_isBounded`-/
class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. This is a field of the structure, but one
  should always prefer `Bornology.cobounded` because it makes the `α` argument explciit. -/
  cobounded' : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. This is a field of
  the structure, but one should always prefer `Bornology.le_cofinite` because it makes the `α`
  argument explciit. -/
  le_cofinite' : cobounded' ≤ cofinite
#align bornology Bornology

/- porting note: Because Lean 4 doesn't accept the `[]` syntax to make arguments of structure
fields explicit, we have to define these separately, prove the `ext` lemmas manually, and
initialize new `simps` projections. -/

/-- The filter of cobounded sets in a bornology. -/
def Bornology.cobounded (α : Type*) [Bornology α] : Filter α := Bornology.cobounded'
#align bornology.cobounded Bornology.cobounded

alias Bornology.Simps.cobounded := Bornology.cobounded

lemma Bornology.le_cofinite (α : Type*) [Bornology α] : cobounded α ≤ cofinite :=
Bornology.le_cofinite'
#align bornology.le_cofinite Bornology.le_cofinite

initialize_simps_projections Bornology (cobounded' → cobounded)

@[ext]
lemma Bornology.ext (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  -- ⊢ { cobounded' := cobounded'✝, le_cofinite' := le_cofinite'✝ } = t'
  cases t'
  -- ⊢ { cobounded' := cobounded'✝¹, le_cofinite' := le_cofinite'✝¹ } = { cobounded …
  congr
  -- 🎉 no goals
#align bornology.ext Bornology.ext

lemma Bornology.ext_iff (t t' : Bornology α) :
    t = t' ↔ @Bornology.cobounded α t = @Bornology.cobounded α t' :=
⟨congrArg _, Bornology.ext _ _⟩
#align bornology.ext_iff Bornology.ext_iff

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps]
def Bornology.ofBounded {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ (_ : s₁ ∈ B) s₂, s₂ ⊆ s₁ → s₂ ∈ B)
    (union_mem : ∀ s₁ (_ : s₁ ∈ B) s₂ (_ : s₂ ∈ B), s₁ ∪ s₂ ∈ B)
    (singleton_mem : ∀ x, {x} ∈ B) : Bornology α
    where
  cobounded' :=
    { sets := { s : Set α | sᶜ ∈ B }
      univ_sets := by rwa [← compl_univ] at empty_mem
                      -- 🎉 no goals
      sets_of_superset := fun hx hy => subset_mem _ hx _ (compl_subset_compl.mpr hy)
      inter_sets := fun hx hy => by simpa [compl_inter] using union_mem _ hx _ hy }
                                    -- 🎉 no goals
  le_cofinite' := by
    rw [le_cofinite_iff_compl_singleton_mem]
    -- ⊢ ∀ (x : α), {x}ᶜ ∈ { sets := {s | sᶜ ∈ B}, univ_sets := (_ : univᶜ ∈ B), sets …
    intro x
    -- ⊢ {x}ᶜ ∈ { sets := {s | sᶜ ∈ B}, univ_sets := (_ : univᶜ ∈ B), sets_of_superse …
    change {x}ᶜᶜ ∈ B
    -- ⊢ {x}ᶜᶜ ∈ B
    rw [compl_compl]
    -- ⊢ {x} ∈ B
    exact singleton_mem x
    -- 🎉 no goals
#align bornology.of_bounded Bornology.ofBounded
#align bornology.of_bounded_cobounded_sets Bornology.ofBounded_cobounded_sets

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps!]
def Bornology.ofBounded' {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ (_ : s₁ ∈ B) s₂, s₂ ⊆ s₁ → s₂ ∈ B)
    (union_mem : ∀ s₁ (_ : s₁ ∈ B) s₂ (_ : s₂ ∈ B), s₁ ∪ s₂ ∈ B)
    (sUnion_univ : ⋃₀ B = univ) :
    Bornology α :=
  Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    -- ⊢ {x} ∈ B
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    -- ⊢ {x} ∈ B
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
    -- 🎉 no goals
#align bornology.of_bounded' Bornology.ofBounded'
#align bornology.of_bounded'_cobounded_sets Bornology.ofBounded'_cobounded_sets
namespace Bornology

section

variable [Bornology α] {s t : Set α} {x : α}

/-- `IsCobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
def IsCobounded (s : Set α) : Prop :=
  s ∈ cobounded α
#align bornology.is_cobounded Bornology.IsCobounded

/-- `IsBounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def IsBounded (s : Set α) : Prop :=
  IsCobounded sᶜ
#align bornology.is_bounded Bornology.IsBounded

theorem isCobounded_def {s : Set α} : IsCobounded s ↔ s ∈ cobounded α :=
  Iff.rfl
#align bornology.is_cobounded_def Bornology.isCobounded_def

theorem isBounded_def {s : Set α} : IsBounded s ↔ sᶜ ∈ cobounded α :=
  Iff.rfl
#align bornology.is_bounded_def Bornology.isBounded_def

@[simp]
theorem isBounded_compl_iff : IsBounded sᶜ ↔ IsCobounded s := by
  rw [isBounded_def, isCobounded_def, compl_compl]
  -- 🎉 no goals
#align bornology.is_bounded_compl_iff Bornology.isBounded_compl_iff

@[simp]
theorem isCobounded_compl_iff : IsCobounded sᶜ ↔ IsBounded s :=
  Iff.rfl
#align bornology.is_cobounded_compl_iff Bornology.isCobounded_compl_iff

alias ⟨IsBounded.of_compl, IsCobounded.compl⟩ := isBounded_compl_iff
#align bornology.is_bounded.of_compl Bornology.IsBounded.of_compl
#align bornology.is_cobounded.compl Bornology.IsCobounded.compl

alias ⟨IsCobounded.of_compl, IsBounded.compl⟩ := isCobounded_compl_iff
#align bornology.is_cobounded.of_compl Bornology.IsCobounded.of_compl
#align bornology.is_bounded.compl Bornology.IsBounded.compl

@[simp]
theorem isBounded_empty : IsBounded (∅ : Set α) := by
  rw [isBounded_def, compl_empty]
  -- ⊢ univ ∈ cobounded α
  exact univ_mem
  -- 🎉 no goals
#align bornology.is_bounded_empty Bornology.isBounded_empty

@[simp]
theorem isBounded_singleton : IsBounded ({x} : Set α) := by
  rw [isBounded_def]
  -- ⊢ {x}ᶜ ∈ cobounded α
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite
  -- 🎉 no goals
#align bornology.is_bounded_singleton Bornology.isBounded_singleton

@[simp]
theorem isCobounded_univ : IsCobounded (univ : Set α) :=
  univ_mem
#align bornology.is_cobounded_univ Bornology.isCobounded_univ

@[simp]
theorem isCobounded_inter : IsCobounded (s ∩ t) ↔ IsCobounded s ∧ IsCobounded t :=
  inter_mem_iff
#align bornology.is_cobounded_inter Bornology.isCobounded_inter

theorem IsCobounded.inter (hs : IsCobounded s) (ht : IsCobounded t) : IsCobounded (s ∩ t) :=
  isCobounded_inter.2 ⟨hs, ht⟩
#align bornology.is_cobounded.inter Bornology.IsCobounded.inter

@[simp]
theorem isBounded_union : IsBounded (s ∪ t) ↔ IsBounded s ∧ IsBounded t := by
  simp only [← isCobounded_compl_iff, compl_union, isCobounded_inter]
  -- 🎉 no goals
#align bornology.is_bounded_union Bornology.isBounded_union

theorem IsBounded.union (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ∪ t) :=
  isBounded_union.2 ⟨hs, ht⟩
#align bornology.is_bounded.union Bornology.IsBounded.union

theorem IsCobounded.superset (hs : IsCobounded s) (ht : s ⊆ t) : IsCobounded t :=
  mem_of_superset hs ht
#align bornology.is_cobounded.superset Bornology.IsCobounded.superset

theorem IsBounded.subset (ht : IsBounded t) (hs : s ⊆ t) : IsBounded s :=
  ht.superset (compl_subset_compl.mpr hs)
#align bornology.is_bounded.subset Bornology.IsBounded.subset

@[simp]
theorem sUnion_bounded_univ : ⋃₀ { s : Set α | IsBounded s } = univ :=
  sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩
#align bornology.sUnion_bounded_univ Bornology.sUnion_bounded_univ

theorem comap_cobounded_le_iff [Bornology β] {f : α → β} :
    (cobounded β).comap f ≤ cobounded α ↔ ∀ ⦃s⦄, IsBounded s → IsBounded (f '' s) := by
  refine'
    ⟨fun h s hs => _, fun h t ht =>
      ⟨(f '' tᶜ)ᶜ, h <| IsCobounded.compl ht, compl_subset_comm.1 <| subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  -- ⊢ IsBounded (f '' s)
  rw [subset_compl_comm, ← preimage_compl] at hts
  -- ⊢ IsBounded (f '' s)
  exact (IsCobounded.compl ht).subset ((image_subset f hts).trans <| image_preimage_subset _ _)
  -- 🎉 no goals
#align bornology.comap_cobounded_le_iff Bornology.comap_cobounded_le_iff

end

theorem ext_iff' {t t' : Bornology α} :
    t = t' ↔ ∀ s, (@cobounded α t).sets s ↔ (@cobounded α t').sets s :=
  (Bornology.ext_iff _ _).trans Filter.ext_iff
#align bornology.ext_iff' Bornology.ext_iff'

theorem ext_iff_isBounded {t t' : Bornology α} :
    t = t' ↔ ∀ s, @IsBounded α t s ↔ @IsBounded α t' s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by
    ext s
    -- ⊢ s ∈ cobounded α ↔ s ∈ cobounded α
    simpa [@isBounded_def _ t, isBounded_def, compl_compl] using h sᶜ⟩
    -- 🎉 no goals
-- porting note: Lean 3 could do this without `@isBounded_def _ t`
#align bornology.ext_iff_is_bounded Bornology.ext_iff_isBounded

variable {s : Set α}

theorem isCobounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsCobounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ sᶜ ∈ B :=
  Iff.rfl
#align bornology.is_cobounded_of_bounded_iff Bornology.isCobounded_ofBounded_iff

theorem isBounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsBounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ s ∈ B := by
  rw [@isBounded_def _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ), ← Filter.mem_sets,
   ofBounded_cobounded_sets, Set.mem_setOf_eq, compl_compl]
-- porting note: again had to use `@isBounded_def _` and feed Lean the instance
#align bornology.is_bounded_of_bounded_iff Bornology.isBounded_ofBounded_iff

variable [Bornology α]

theorem isCobounded_biInter {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_mem hs
#align bornology.is_cobounded_bInter Bornology.isCobounded_biInter

@[simp]
theorem isCobounded_biInter_finset (s : Finset ι) {f : ι → Set α} :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_finset_mem s
#align bornology.is_cobounded_bInter_finset Bornology.isCobounded_biInter_finset

@[simp]
theorem isCobounded_iInter [Finite ι] {f : ι → Set α} :
    IsCobounded (⋂ i, f i) ↔ ∀ i, IsCobounded (f i) :=
  iInter_mem
#align bornology.is_cobounded_Inter Bornology.isCobounded_iInter

theorem isCobounded_sInter {S : Set (Set α)} (hs : S.Finite) :
    IsCobounded (⋂₀ S) ↔ ∀ s ∈ S, IsCobounded s :=
  sInter_mem hs
#align bornology.is_cobounded_sInter Bornology.isCobounded_sInter

theorem isBounded_biUnion {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) := by
  simp only [← isCobounded_compl_iff, compl_iUnion, isCobounded_biInter hs]
  -- 🎉 no goals
#align bornology.is_bounded_bUnion Bornology.isBounded_biUnion

theorem isBounded_biUnion_finset (s : Finset ι) {f : ι → Set α} :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) :=
  isBounded_biUnion s.finite_toSet
#align bornology.is_bounded_bUnion_finset Bornology.isBounded_biUnion_finset

theorem isBounded_sUnion {S : Set (Set α)} (hs : S.Finite) :
    IsBounded (⋃₀ S) ↔ ∀ s ∈ S, IsBounded s := by rw [sUnion_eq_biUnion, isBounded_biUnion hs]
                                                  -- 🎉 no goals
#align bornology.is_bounded_sUnion Bornology.isBounded_sUnion

@[simp]
theorem isBounded_iUnion [Finite ι] {s : ι → Set α} : IsBounded (⋃ i, s i) ↔ ∀ i, IsBounded (s i) :=
  by rw [← sUnion_range, isBounded_sUnion (finite_range s), forall_range_iff]
     -- 🎉 no goals
#align bornology.is_bounded_Union Bornology.isBounded_iUnion

end Bornology

open Bornology

theorem Set.Finite.isBounded [Bornology α] {s : Set α} (hs : s.Finite) : IsBounded s :=
  Bornology.le_cofinite α hs.compl_mem_cofinite
#align set.finite.is_bounded Set.Finite.isBounded

instance : Bornology PUnit :=
  ⟨⊥, bot_le⟩

/-- The cofinite filter as a bornology -/
@[reducible]
def Bornology.cofinite : Bornology α
    where
  cobounded' := Filter.cofinite
  le_cofinite' := le_rfl
#align bornology.cofinite Bornology.cofinite

/-- A space with a `Bornology` is a **bounded space** if `Set.univ : Set α` is bounded. -/
class BoundedSpace (α : Type*) [Bornology α] : Prop where
  /-- The `Set.univ` is bounded. -/
  bounded_univ : Bornology.IsBounded (univ : Set α)
#align bounded_space BoundedSpace

namespace Bornology

variable [Bornology α]

theorem isBounded_univ : IsBounded (univ : Set α) ↔ BoundedSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
#align bornology.is_bounded_univ Bornology.isBounded_univ

theorem cobounded_eq_bot_iff : cobounded α = ⊥ ↔ BoundedSpace α := by
  rw [← isBounded_univ, isBounded_def, compl_univ, empty_mem_iff_bot]
  -- 🎉 no goals
#align bornology.cobounded_eq_bot_iff Bornology.cobounded_eq_bot_iff

variable [BoundedSpace α]

theorem IsBounded.all (s : Set α) : IsBounded s :=
  BoundedSpace.bounded_univ.subset s.subset_univ
#align bornology.is_bounded.all Bornology.IsBounded.all

theorem IsCobounded.all (s : Set α) : IsCobounded s :=
  compl_compl s ▸ IsBounded.all sᶜ
#align bornology.is_cobounded.all Bornology.IsCobounded.all

variable (α)

@[simp]
theorem cobounded_eq_bot : cobounded α = ⊥ :=
  cobounded_eq_bot_iff.2 ‹_›
#align bornology.cobounded_eq_bot Bornology.cobounded_eq_bot

end Bornology
