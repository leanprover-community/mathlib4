/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.QuasiSeparated

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

namespace Compacts

instance : SetLike (Compacts α) α where
  coe := Compacts.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier → coe, as_prefix coe)

protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'

instance (K : Compacts α) : CompactSpace K :=
  isCompact_iff_compactSpace.1 K.isCompact

instance : CanLift (Set α) (Compacts α) (↑) IsCompact where prf K hK := ⟨⟨K, hK⟩, rfl⟩

@[ext]
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
theorem carrier_eq_coe (s : Compacts α) : s.carrier = s :=
  rfl

instance : Max (Compacts α) :=
  ⟨fun s t => ⟨s ∪ t, s.isCompact.union t.isCompact⟩⟩

instance [T2Space α] : Min (Compacts α) :=
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

@[simp]
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_finset_sup {ι : Type*} {s : Finset ι} {f : ι → Compacts α} :
    (↑(s.sup f) : Set α) = s.sup fun i => ↑(f i) := by
  refine Finset.cons_induction_on s rfl fun a s _ h => ?_
  simp_rw [Finset.sup_cons, coe_sup, sup_eq_union]
  congr

@[simps]
instance : Singleton α (Compacts α) where
  singleton x := ⟨{x}, isCompact_singleton⟩

@[simp]
theorem mem_singleton (x y : α) : x ∈ ({y} : Compacts α) ↔ x = y :=
  Iff.rfl

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.image hf⟩

@[simp, norm_cast]
theorem coe_map {f : α → β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl

@[simp]
theorem map_id (K : Compacts α) : K.map id continuous_id = K :=
  Compacts.ext <| Set.image_id _

theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (K : Compacts α) :
    K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf :=
  Compacts.ext <| Set.image_comp _ _ _

@[simp]
theorem map_singleton {f : α → β} (hf : Continuous f) (x : α) : Compacts.map f hf {x} = {f x} :=
  Compacts.ext Set.image_singleton

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

@[simp]
theorem equiv_refl : Compacts.equiv (Homeomorph.refl α) = Equiv.refl _ :=
  Equiv.ext map_id

@[simp]
theorem equiv_trans (f : α ≃ₜ β) (g : β ≃ₜ γ) :
    Compacts.equiv (f.trans g) = (Compacts.equiv f).trans (Compacts.equiv g) :=
  Equiv.ext <| map_comp g f g.continuous f.continuous

@[simp]
theorem equiv_symm (f : α ≃ₜ β) : Compacts.equiv f.symm = (Compacts.equiv f).symm :=
  rfl

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem coe_equiv_apply_eq_preimage (f : α ≃ₜ β) (K : Compacts α) :
    (Compacts.equiv f K : Set β) = f.symm ⁻¹' (K : Set α) :=
  f.toEquiv.image_eq_preimage K

/-- The product of two `TopologicalSpace.Compacts`, as a `TopologicalSpace.Compacts` in the product
space. -/
protected def prod (K : Compacts α) (L : Compacts β) : Compacts (α × β) where
  carrier := K ×ˢ L
  isCompact' := IsCompact.prod K.2 L.2

@[simp]
theorem coe_prod (K : Compacts α) (L : Compacts β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

@[simp]
theorem singleton_prod_singleton (x : α) (y : β) :
    Compacts.prod {x} {y} = {(x, y)} :=
  Compacts.ext Set.singleton_prod_singleton

-- todo: add `pi`

end Compacts

/-! ### Nonempty compact sets -/

/-- The type of nonempty compact sets of a topological space. -/
structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty

namespace NonemptyCompacts

instance : SetLike (NonemptyCompacts α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : NonemptyCompacts α) : Set α := s

initialize_simps_projections NonemptyCompacts (carrier → coe, as_prefix coe)

protected theorem isCompact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'

protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'

/-- Reinterpret a nonempty compact as a closed set. -/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩

@[ext]
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

theorem carrier_eq_coe (s : NonemptyCompacts α) : s.carrier = s :=
  rfl

@[simp]
theorem coe_toCompacts (s : NonemptyCompacts α) : (s.toCompacts : Set α) = s := rfl

instance : Max (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.nonempty.mono subset_union_left⟩⟩

instance [CompactSpace α] [Nonempty α] : Top (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩

instance : SemilatticeSup (NonemptyCompacts α) :=
  SetLike.coe_injective.semilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  OrderTop.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl

@[simps!]
instance : Singleton α (NonemptyCompacts α) where
  singleton x := ⟨{x}, singleton_nonempty x⟩

@[simp]
theorem mem_singleton (x y : α) : x ∈ ({y} : NonemptyCompacts α) ↔ x = y :=
  Iff.rfl

@[simp]
theorem toCompacts_singleton (x : α) : toCompacts {x} = {x} :=
  rfl

@[simp]
theorem toCloseds_singleton [T2Space α] (x : α) : toCloseds {x} = Closeds.singleton x :=
  rfl

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{default}⟩

instance toCompactSpace {s : NonemptyCompacts α} : CompactSpace s :=
  isCompact_iff_compactSpace.1 s.isCompact

instance toNonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.nonempty.to_subtype

/-- The product of two `TopologicalSpace.NonemptyCompacts`, as a `TopologicalSpace.NonemptyCompacts`
in the product space. -/
protected def prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : NonemptyCompacts (α × β) :=
  { K.toCompacts.prod L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }

@[simp]
theorem coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

@[simp]
theorem singleton_prod_singleton (x : α) (y : β) :
    NonemptyCompacts.prod {x} {y} = {(x, y)} :=
  NonemptyCompacts.ext Set.singleton_prod_singleton

end NonemptyCompacts

/-! ### Positive compact sets -/

/-- The type of compact sets with nonempty interior of a topological space.
See also `TopologicalSpace.Compacts` and `TopologicalSpace.NonemptyCompacts`. -/
structure PositiveCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty

namespace PositiveCompacts

instance : SetLike (PositiveCompacts α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : PositiveCompacts α) : Set α := s

initialize_simps_projections PositiveCompacts (carrier → coe, as_prefix coe)

protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'

theorem interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonempty :=
  s.interior_nonempty'

protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset

/-- Reinterpret a positive compact as a nonempty compact. -/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.nonempty⟩

@[ext]
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

theorem carrier_eq_coe (s : PositiveCompacts α) : s.carrier = s :=
  rfl

@[simp]
theorem coe_toCompacts (s : PositiveCompacts α) : (s.toCompacts : Set α) = s :=
  rfl

instance : Max (PositiveCompacts α) :=
  ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
      s.interior_nonempty.mono <| interior_mono subset_union_left⟩⟩

instance [CompactSpace α] [Nonempty α] : Top (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

instance : SemilatticeSup (PositiveCompacts α) :=
  SetLike.coe_injective.semilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  OrderTop.lift ((↑) : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : PositiveCompacts α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl

/-- The image of a positive compact set under a continuous open map. -/
protected def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (K : PositiveCompacts α) :
    PositiveCompacts β :=
  { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }

@[simp, norm_cast]
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : PositiveCompacts α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

@[simp]
theorem map_id (K : PositiveCompacts α) : K.map id continuous_id IsOpenMap.id = K :=
  PositiveCompacts.ext <| Set.image_id _

theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : PositiveCompacts α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
  PositiveCompacts.ext <| Set.image_comp _ _ _

theorem _root_.exists_positiveCompacts_subset [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U)
    (hn : U.Nonempty) : ∃ K : PositiveCompacts α, ↑K ⊆ U :=
  let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩

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

/-- The product of two `TopologicalSpace.PositiveCompacts`, as a `TopologicalSpace.PositiveCompacts`
in the product space. -/
protected def prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    PositiveCompacts (α × β) where
  toCompacts := K.toCompacts.prod L.toCompacts
  interior_nonempty' := by
    simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
    exact K.interior_nonempty.prod L.interior_nonempty

@[simp]
theorem coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end PositiveCompacts

/-! ### Compact open sets -/

/-- The type of compact open sets of a topological space. This is useful in non-Hausdorff contexts,
in particular spectral spaces. -/
structure CompactOpens (α : Type*) [TopologicalSpace α] extends Compacts α where
  isOpen' : IsOpen carrier

namespace CompactOpens

instance : SetLike (CompactOpens α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : CompactOpens α) : Set α := s

initialize_simps_projections CompactOpens (carrier → coe, as_prefix coe)

protected theorem isCompact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.isCompact'

protected theorem isOpen (s : CompactOpens α) : IsOpen (s : Set α) :=
  s.isOpen'

/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : CompactOpens α) : Opens α := ⟨s, s.isOpen⟩

/-- Reinterpret a compact open as a clopen. -/
@[simps]
def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.isCompact.isClosed, s.isOpen⟩

@[ext]
protected theorem ext {s t : CompactOpens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

instance : Max (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.isOpen.union t.isOpen⟩⟩

instance : Bot (CompactOpens α) where bot := ⟨⊥, isOpen_empty⟩

@[simp, norm_cast] lemma coe_sup (s t : CompactOpens α) : ↑(s ⊔ t) = (s ∪ t : Set α) := rfl
@[simp, norm_cast] lemma coe_bot : ↑(⊥ : CompactOpens α) = (∅ : Set α) := rfl

instance : SemilatticeSup (CompactOpens α) := SetLike.coe_injective.semilatticeSup _ coe_sup
instance : OrderBot (CompactOpens α) := OrderBot.lift ((↑) : _ → Set α) (fun _ _ => id) coe_bot

@[simp]
lemma coe_finsetSup {ι : Type*} {f : ι → CompactOpens α} {s : Finset ι} :
    (↑(s.sup f) : Set α) = ⋃ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on <;> simp [*]

instance : Inhabited (CompactOpens α) :=
  ⟨⊥⟩

section Inf
variable [QuasiSeparatedSpace α]

instance instInf : Min (CompactOpens α) where
  min U V :=
    ⟨⟨U ∩ V, QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩, U.2.inter V.2⟩

@[simp, norm_cast] lemma coe_inf (s t : CompactOpens α) : ↑(s ⊓ t) = (s ∩ t : Set α) := rfl

instance instSemilatticeInf : SemilatticeInf (CompactOpens α) :=
  SetLike.coe_injective.semilatticeInf _ coe_inf

end Inf

section SDiff
variable [T2Space α]

instance instSDiff : SDiff (CompactOpens α) where
  sdiff s t := ⟨⟨s \ t, s.isCompact.diff t.isOpen⟩, s.isOpen.sdiff t.isCompact.isClosed⟩

@[simp, norm_cast] lemma coe_sdiff (s t : CompactOpens α) : ↑(s \ t) = (s \ t : Set α) := rfl

instance instGeneralizedBooleanAlgebra : GeneralizedBooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.generalizedBooleanAlgebra _ coe_sup coe_inf coe_bot coe_sdiff

end SDiff

section Top
variable [CompactSpace α]

instance instTop : Top (CompactOpens α) where top := ⟨⊤, isOpen_univ⟩

@[simp, norm_cast] lemma coe_top : ↑(⊤ : CompactOpens α) = (univ : Set α) := rfl

instance instBoundedOrder : BoundedOrder (CompactOpens α) :=
  BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) coe_top coe_bot

section Compl
variable [T2Space α]

instance instHasCompl : HasCompl (CompactOpens α) where
  compl s := ⟨⟨sᶜ, s.isOpen.isClosed_compl.isCompact⟩, s.isCompact.isClosed.isOpen_compl⟩

instance instHImp : HImp (CompactOpens α) where
  himp s t := ⟨⟨s ⇨ t, IsClosed.isCompact
    (by simpa [himp_eq] using t.isCompact.isClosed.union s.isOpen.isClosed_compl)⟩,
    by simpa [himp_eq] using t.isOpen.union s.isCompact.isClosed.isOpen_compl⟩

@[simp, norm_cast] lemma coe_compl (s : CompactOpens α) : ↑sᶜ = (sᶜ : Set α) := rfl
@[simp, norm_cast] lemma coe_himp (s t : CompactOpens α) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl

instance instBooleanAlgebra : BooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.booleanAlgebra _ coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff
    coe_himp

end Top.Compl

/-- The image of a compact open under a continuous open map. -/
@[simps toCompacts]
def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩

@[simp, norm_cast]
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

@[simp]
theorem map_id (K : CompactOpens α) : K.map id continuous_id IsOpenMap.id = K :=
  CompactOpens.ext <| Set.image_id _

theorem map_comp (f : β → γ) (g : α → β) (hf : Continuous f) (hg : Continuous g) (hf' : IsOpenMap f)
    (hg' : IsOpenMap g) (K : CompactOpens α) :
    K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf' :=
  CompactOpens.ext <| Set.image_comp _ _ _

/-- The product of two `TopologicalSpace.CompactOpens`, as a `TopologicalSpace.CompactOpens` in the
product space. -/
protected def prod (K : CompactOpens α) (L : CompactOpens β) : CompactOpens (α × β) :=
  { K.toCompacts.prod L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }

@[simp]
theorem coe_prod (K : CompactOpens α) (L : CompactOpens β) :
    (K.prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end CompactOpens

end TopologicalSpace
