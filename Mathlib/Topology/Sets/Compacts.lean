/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.QuasiSeparated

#align_import topology.sets.compacts from "leanprover-community/mathlib"@"8c1b484d6a214e059531e22f1be9898ed6c1fd47"

/-!
# Compact sets

We define a few types of compact sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Compacts α`: The type of compact sets.
* `TopologicalSpace.NonemptyCompacts α`: The type of non-empty compact sets.
* `TopologicalSpace.PositiveCompacts α`: The type of compact sets with non-empty interior.
* `TopologicalSpace.CompactOpens α`: The type of compact open sets. This is a central object in the
  study of spectral spaces.
-/


open Set

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

/-! ### Compact sets -/

/-- The type of compact sets of a topological space. -/
structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier
#align topological_space.compacts TopologicalSpace.Compacts

namespace Compacts

instance : SetLike (Compacts α) α where
  coe := Compacts.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier → coe)

protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.compacts.is_compact TopologicalSpace.Compacts.isCompact

instance (K : Compacts α) : CompactSpace K :=
  isCompact_iff_compactSpace.1 K.isCompact

instance : CanLift (Set α) (Compacts α) (↑) IsCompact where prf K hK := ⟨⟨K, hK⟩, rfl⟩

@[ext]
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.compacts.ext TopologicalSpace.Compacts.ext

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.compacts.coe_mk TopologicalSpace.Compacts.coe_mk

@[simp]
theorem carrier_eq_coe (s : Compacts α) : s.carrier = s :=
  rfl
#align topological_space.compacts.carrier_eq_coe TopologicalSpace.Compacts.carrier_eq_coe

instance : Sup (Compacts α) :=
  ⟨fun s t => ⟨s ∪ t, s.isCompact.union t.isCompact⟩⟩

instance [T2Space α] : Inf (Compacts α) :=
  ⟨fun s t => ⟨s ∩ t, s.isCompact.inter t.isCompact⟩⟩

instance [CompactSpace α] : Top (Compacts α) :=
  ⟨⟨univ, isCompact_univ⟩⟩

instance : Bot (Compacts α) :=
  ⟨⟨∅, isCompact_empty⟩⟩

instance : SemilatticeSup (Compacts α) :=
  SetLike.coe_injective.semilatticeSup _ fun _ _ => rfl

instance [T2Space α] : DistribLattice (Compacts α) :=
  SetLike.coe_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : OrderBot (Compacts α) :=
  OrderBot.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

instance [CompactSpace α] : BoundedOrder (Compacts α) :=
  BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of compact sets is inhabited, with default element the empty set. -/
instance : Inhabited (Compacts α) := ⟨⊥⟩

@[simp]
theorem coe_sup (s t : Compacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl
#align topological_space.compacts.coe_sup TopologicalSpace.Compacts.coe_sup

@[simp]
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl
#align topological_space.compacts.coe_inf TopologicalSpace.Compacts.coe_inf

@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl
#align topological_space.compacts.coe_top TopologicalSpace.Compacts.coe_top

@[simp]
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl
#align topological_space.compacts.coe_bot TopologicalSpace.Compacts.coe_bot

@[simp]
theorem coe_finset_sup {ι : Type*} {s : Finset ι} {f : ι → Compacts α} :
    (↑(s.sup f) : Set α) = s.sup fun i => ↑(f i) := by
  refine Finset.cons_induction_on s rfl fun a s _ h => ?_
  simp_rw [Finset.sup_cons, coe_sup, sup_eq_union]
  congr
#align topological_space.compacts.coe_finset_sup TopologicalSpace.Compacts.coe_finset_sup

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.image hf⟩
#align topological_space.compacts.map TopologicalSpace.Compacts.map

@[simp, norm_cast]
theorem coe_map {f : α → β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl
#align topological_space.compacts.coe_map TopologicalSpace.Compacts.coe_map

@[simp]
theorem map_id (K : Compacts α) : K.map id continuous_id = K :=
  Compacts.ext <| Set.image_id _
#align topological_space.compacts.map_id TopologicalSpace.Compacts.map_id

theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (K : Compacts α) :
    K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf :=
  Compacts.ext <| Set.image_comp _ _ _
#align topological_space.compacts.map_comp TopologicalSpace.Compacts.map_comp

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simps]
protected def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β where
  toFun := Compacts.map f f.continuous
  invFun := Compacts.map _ f.symm.continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]
#align topological_space.compacts.equiv TopologicalSpace.Compacts.equiv

@[simp]
theorem equiv_refl : Compacts.equiv (Homeomorph.refl α) = Equiv.refl _ :=
  Equiv.ext map_id
#align topological_space.compacts.equiv_refl TopologicalSpace.Compacts.equiv_refl

@[simp]
theorem equiv_trans (f : α ≃ₜ β) (g : β ≃ₜ γ) :
    Compacts.equiv (f.trans g) = (Compacts.equiv f).trans (Compacts.equiv g) :=
  -- Porting note: can no longer write `map_comp _ _ _ _` and unify
  Equiv.ext <| map_comp g f g.continuous f.continuous
#align topological_space.compacts.equiv_trans TopologicalSpace.Compacts.equiv_trans

@[simp]
theorem equiv_symm (f : α ≃ₜ β) : Compacts.equiv f.symm = (Compacts.equiv f).symm :=
  rfl
#align topological_space.compacts.equiv_symm TopologicalSpace.Compacts.equiv_symm

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem coe_equiv_apply_eq_preimage (f : α ≃ₜ β) (K : Compacts α) :
    (Compacts.equiv f K : Set β) = f.symm ⁻¹' (K : Set α) :=
  f.toEquiv.image_eq_preimage K
#align topological_space.compacts.coe_equiv_apply_eq_preimage TopologicalSpace.Compacts.coe_equiv_apply_eq_preimage

/-- The product of two `TopologicalSpace.Compacts`, as a `TopologicalSpace.Compacts` in the product
space. -/
protected def prod (K : Compacts α) (L : Compacts β) : Compacts (α × β) where
  carrier := K ×ˢ L
  isCompact' := IsCompact.prod K.2 L.2
#align topological_space.compacts.prod TopologicalSpace.Compacts.prod

@[simp]
theorem coe_prod (K : Compacts α) (L : Compacts β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl
#align topological_space.compacts.coe_prod TopologicalSpace.Compacts.coe_prod

-- todo: add `pi`

end Compacts

/-! ### Nonempty compact sets -/

/-- The type of nonempty compact sets of a topological space. -/
structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty
#align topological_space.nonempty_compacts TopologicalSpace.NonemptyCompacts

namespace NonemptyCompacts

instance : SetLike (NonemptyCompacts α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : NonemptyCompacts α) : Set α := s

initialize_simps_projections NonemptyCompacts (carrier → coe)

protected theorem isCompact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.nonempty_compacts.is_compact TopologicalSpace.NonemptyCompacts.isCompact

protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'
#align topological_space.nonempty_compacts.nonempty TopologicalSpace.NonemptyCompacts.nonempty

/-- Reinterpret a nonempty compact as a closed set. -/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩
#align topological_space.nonempty_compacts.to_closeds TopologicalSpace.NonemptyCompacts.toCloseds

@[ext]
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.nonempty_compacts.ext TopologicalSpace.NonemptyCompacts.ext

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.nonempty_compacts.coe_mk TopologicalSpace.NonemptyCompacts.coe_mk

-- Porting note: `@[simp]` moved to `coe_toCompacts`
theorem carrier_eq_coe (s : NonemptyCompacts α) : s.carrier = s :=
  rfl
#align topological_space.nonempty_compacts.carrier_eq_coe TopologicalSpace.NonemptyCompacts.carrier_eq_coe

@[simp] -- Porting note (#10756): new lemma
theorem coe_toCompacts (s : NonemptyCompacts α) : (s.toCompacts : Set α) = s := rfl

instance : Sup (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.nonempty.mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : Top (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩

instance : SemilatticeSup (NonemptyCompacts α) :=
  SetLike.coe_injective.semilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  OrderTop.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl
#align topological_space.nonempty_compacts.coe_sup TopologicalSpace.NonemptyCompacts.coe_sup

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl
#align topological_space.nonempty_compacts.coe_top TopologicalSpace.NonemptyCompacts.coe_top

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{  carrier := {default}
      isCompact' := isCompact_singleton
      nonempty' := singleton_nonempty _ }⟩

instance toCompactSpace {s : NonemptyCompacts α} : CompactSpace s :=
  isCompact_iff_compactSpace.1 s.isCompact
#align topological_space.nonempty_compacts.to_compact_space TopologicalSpace.NonemptyCompacts.toCompactSpace

instance toNonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.nonempty.to_subtype
#align topological_space.nonempty_compacts.to_nonempty TopologicalSpace.NonemptyCompacts.toNonempty

/-- The product of two `TopologicalSpace.NonemptyCompacts`, as a `TopologicalSpace.NonemptyCompacts`
in the product space. -/
protected def prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : NonemptyCompacts (α × β) :=
  { K.toCompacts.prod L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }
#align topological_space.nonempty_compacts.prod TopologicalSpace.NonemptyCompacts.prod

@[simp]
theorem coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl
#align topological_space.nonempty_compacts.coe_prod TopologicalSpace.NonemptyCompacts.coe_prod

end NonemptyCompacts

/-! ### Positive compact sets -/

/-- The type of compact sets with nonempty interior of a topological space.
See also `TopologicalSpace.Compacts` and `TopologicalSpace.NonemptyCompacts`. -/
structure PositiveCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty
#align topological_space.positive_compacts TopologicalSpace.PositiveCompacts

namespace PositiveCompacts

instance : SetLike (PositiveCompacts α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : PositiveCompacts α) : Set α := s

initialize_simps_projections PositiveCompacts (carrier → coe)

protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.positive_compacts.is_compact TopologicalSpace.PositiveCompacts.isCompact

theorem interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonempty :=
  s.interior_nonempty'
#align topological_space.positive_compacts.interior_nonempty TopologicalSpace.PositiveCompacts.interior_nonempty

protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset
#align topological_space.positive_compacts.nonempty TopologicalSpace.PositiveCompacts.nonempty

/-- Reinterpret a positive compact as a nonempty compact. -/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.nonempty⟩
#align topological_space.positive_compacts.to_nonempty_compacts TopologicalSpace.PositiveCompacts.toNonemptyCompacts

@[ext]
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.positive_compacts.ext TopologicalSpace.PositiveCompacts.ext

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.positive_compacts.coe_mk TopologicalSpace.PositiveCompacts.coe_mk

-- Porting note: `@[simp]` moved to a new lemma
theorem carrier_eq_coe (s : PositiveCompacts α) : s.carrier = s :=
  rfl
#align topological_space.positive_compacts.carrier_eq_coe TopologicalSpace.PositiveCompacts.carrier_eq_coe

@[simp]
theorem coe_toCompacts (s : PositiveCompacts α) : (s.toCompacts : Set α) = s :=
  rfl

instance : Sup (PositiveCompacts α) :=
  ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
      s.interior_nonempty.mono <| interior_mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : Top (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

instance : SemilatticeSup (PositiveCompacts α) :=
  SetLike.coe_injective.semilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  OrderTop.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : PositiveCompacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl
#align topological_space.positive_compacts.coe_sup TopologicalSpace.PositiveCompacts.coe_sup

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl
#align topological_space.positive_compacts.coe_top TopologicalSpace.PositiveCompacts.coe_top

/-- The image of a positive compact set under a continuous open map. -/
protected def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (K : PositiveCompacts α) :
    PositiveCompacts β :=
  { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }
#align topological_space.positive_compacts.map TopologicalSpace.PositiveCompacts.map

@[simp, norm_cast]
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : PositiveCompacts α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl
#align topological_space.positive_compacts.coe_map TopologicalSpace.PositiveCompacts.coe_map

@[simp]
theorem map_id (K : PositiveCompacts α) : K.map id continuous_id IsOpenMap.id = K :=
  PositiveCompacts.ext <| Set.image_id _
#align topological_space.positive_compacts.map_id TopologicalSpace.PositiveCompacts.map_id

theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : PositiveCompacts α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
  PositiveCompacts.ext <| Set.image_comp _ _ _
#align topological_space.positive_compacts.map_comp TopologicalSpace.PositiveCompacts.map_comp

theorem _root_.exists_positiveCompacts_subset [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U)
    (hn : U.Nonempty) : ∃ K : PositiveCompacts α, ↑K ⊆ U :=
  let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩
#align exists_positive_compacts_subset exists_positiveCompacts_subset

theorem _root_.IsOpen.exists_positiveCompacts_closure_subset [R1Space α] [LocallyCompactSpace α]
    {U : Set α} (ho : IsOpen U) (hn : U.Nonempty) : ∃ K : PositiveCompacts α, closure ↑K ⊆ U :=
  let ⟨K, hKU⟩ := exists_positiveCompacts_subset ho hn
  ⟨K, K.isCompact.closure_subset_of_isOpen ho hKU⟩

instance [CompactSpace α] [Nonempty α] : Inhabited (PositiveCompacts α) :=
  ⟨⊤⟩

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance nonempty' [WeaklyLocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveCompacts α) := by
  inhabit α
  rcases exists_compact_mem_nhds (default : α) with ⟨K, hKc, hK⟩
  exact ⟨⟨K, hKc⟩, _, mem_interior_iff_mem_nhds.2 hK⟩
#align topological_space.positive_compacts.nonempty' TopologicalSpace.PositiveCompacts.nonempty'

/-- The product of two `TopologicalSpace.PositiveCompacts`, as a `TopologicalSpace.PositiveCompacts`
in the product space. -/
protected def prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    PositiveCompacts (α × β) where
  toCompacts := K.toCompacts.prod L.toCompacts
  interior_nonempty' := by
    simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
    exact K.interior_nonempty.prod L.interior_nonempty
#align topological_space.positive_compacts.prod TopologicalSpace.PositiveCompacts.prod

@[simp]
theorem coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl
#align topological_space.positive_compacts.coe_prod TopologicalSpace.PositiveCompacts.coe_prod

end PositiveCompacts

/-! ### Compact open sets -/

/-- The type of compact open sets of a topological space. This is useful in non Hausdorff contexts,
in particular spectral spaces. -/
structure CompactOpens (α : Type*) [TopologicalSpace α] extends Compacts α where
  isOpen' : IsOpen carrier
#align topological_space.compact_opens TopologicalSpace.CompactOpens

namespace CompactOpens

instance : SetLike (CompactOpens α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : CompactOpens α) : Set α := s

initialize_simps_projections CompactOpens (carrier → coe)

protected theorem isCompact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.compact_opens.is_compact TopologicalSpace.CompactOpens.isCompact

protected theorem isOpen (s : CompactOpens α) : IsOpen (s : Set α) :=
  s.isOpen'
#align topological_space.compact_opens.is_open TopologicalSpace.CompactOpens.isOpen

/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : CompactOpens α) : Opens α := ⟨s, s.isOpen⟩
#align topological_space.compact_opens.to_opens TopologicalSpace.CompactOpens.toOpens

/-- Reinterpret a compact open as a clopen. -/
@[simps]
def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.isCompact.isClosed, s.isOpen⟩
#align topological_space.compact_opens.to_clopens TopologicalSpace.CompactOpens.toClopens

@[ext]
protected theorem ext {s t : CompactOpens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.compact_opens.ext TopologicalSpace.CompactOpens.ext

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.compact_opens.coe_mk TopologicalSpace.CompactOpens.coe_mk

instance : Sup (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.isOpen.union t.isOpen⟩⟩

instance [QuasiSeparatedSpace α] : Inf (CompactOpens α) :=
  ⟨fun U V =>
    ⟨⟨(U : Set α) ∩ (V : Set α),
        QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩,
      U.2.inter V.2⟩⟩

instance [QuasiSeparatedSpace α] : SemilatticeInf (CompactOpens α) :=
  SetLike.coe_injective.semilatticeInf _ fun _ _ => rfl

instance [CompactSpace α] : Top (CompactOpens α) :=
  ⟨⟨⊤, isOpen_univ⟩⟩

instance : Bot (CompactOpens α) :=
  ⟨⟨⊥, isOpen_empty⟩⟩

instance [T2Space α] : SDiff (CompactOpens α) :=
  ⟨fun s t => ⟨⟨s \ t, s.isCompact.diff t.isOpen⟩, s.isOpen.sdiff t.isCompact.isClosed⟩⟩

instance [T2Space α] [CompactSpace α] : HasCompl (CompactOpens α) :=
  ⟨fun s => ⟨⟨sᶜ, s.isOpen.isClosed_compl.isCompact⟩, s.isCompact.isClosed.isOpen_compl⟩⟩

instance : SemilatticeSup (CompactOpens α) :=
  SetLike.coe_injective.semilatticeSup _ fun _ _ => rfl

instance : OrderBot (CompactOpens α) :=
  OrderBot.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

instance [T2Space α] : GeneralizedBooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.generalizedBooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl fun _ _ =>
    rfl

instance [CompactSpace α] : BoundedOrder (CompactOpens α) :=
  BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) rfl rfl

instance [T2Space α] [CompactSpace α] : BooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.booleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
    fun _ _ => rfl

@[simp]
theorem coe_sup (s t : CompactOpens α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl
#align topological_space.compact_opens.coe_sup TopologicalSpace.CompactOpens.coe_sup

@[simp]
theorem coe_inf [T2Space α] (s t : CompactOpens α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl
#align topological_space.compact_opens.coe_inf TopologicalSpace.CompactOpens.coe_inf

@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : CompactOpens α) : Set α) = univ :=
  rfl
#align topological_space.compact_opens.coe_top TopologicalSpace.CompactOpens.coe_top

@[simp]
theorem coe_bot : (↑(⊥ : CompactOpens α) : Set α) = ∅ :=
  rfl
#align topological_space.compact_opens.coe_bot TopologicalSpace.CompactOpens.coe_bot

@[simp]
theorem coe_sdiff [T2Space α] (s t : CompactOpens α) : (↑(s \ t) : Set α) = ↑s \ ↑t :=
  rfl
#align topological_space.compact_opens.coe_sdiff TopologicalSpace.CompactOpens.coe_sdiff

@[simp]
theorem coe_compl [T2Space α] [CompactSpace α] (s : CompactOpens α) : (↑sᶜ : Set α) = (↑s)ᶜ :=
  rfl
#align topological_space.compact_opens.coe_compl TopologicalSpace.CompactOpens.coe_compl

instance : Inhabited (CompactOpens α) :=
  ⟨⊥⟩

/-- The image of a compact open under a continuous open map. -/
@[simps toCompacts]
def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩
#align topological_space.compact_opens.map TopologicalSpace.CompactOpens.map

@[simp, norm_cast]
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl
#align topological_space.compact_opens.coe_map TopologicalSpace.CompactOpens.coe_map

@[simp]
theorem map_id (K : CompactOpens α) : K.map id continuous_id IsOpenMap.id = K :=
  CompactOpens.ext <| Set.image_id _
#align topological_space.compact_opens.map_id TopologicalSpace.CompactOpens.map_id

theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : CompactOpens α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
  CompactOpens.ext <| Set.image_comp _ _ _
#align topological_space.compact_opens.map_comp TopologicalSpace.CompactOpens.map_comp

/-- The product of two `TopologicalSpace.CompactOpens`, as a `TopologicalSpace.CompactOpens` in the
product space. -/
protected def prod (K : CompactOpens α) (L : CompactOpens β) : CompactOpens (α × β) :=
  { K.toCompacts.prod L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }
#align topological_space.compact_opens.prod TopologicalSpace.CompactOpens.prod

@[simp]
theorem coe_prod (K : CompactOpens α) (L : CompactOpens β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl
#align topological_space.compact_opens.coe_prod TopologicalSpace.CompactOpens.coe_prod

end CompactOpens

end TopologicalSpace
