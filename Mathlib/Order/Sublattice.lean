/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.SupClosed

/-!
# Sublattices

This file defines sublattices.

## TODO

Subsemilattices, if people care about them.

## Tags

sublattice
-/

open Function Set

variable {ι : Sort*} (α β γ : Type*) [Lattice α] [Lattice β] [Lattice γ]

/-- A sublattice of a lattice is a set containing the suprema and infima of any of its elements. -/
structure Sublattice where
  /-- The underlying set of a sublattice. **Do not use directly**. Instead, use the coercion
  `Sublattice α → Set α`, which Lean should automatically insert for you in most cases. -/
  carrier : Set α
  supClosed' : SupClosed carrier
  infClosed' : InfClosed carrier

variable {α β γ}

namespace Sublattice
variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a : α}

initialize_simps_projections Sublattice (carrier → coe)

instance instSetLike : SetLike (Sublattice α) α where
  coe L := L.carrier
  coe_injective' L M h := by cases L; congr

/-- Turn a set closed under supremum and infimum into a sublattice. -/
abbrev ofIsSublattice (s : Set α) (hs : IsSublattice s) : Sublattice α := ⟨s, hs.1, hs.2⟩

lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq

@[simp] lemma supClosed (L : Sublattice α) : SupClosed (L : Set α) := L.supClosed'
@[simp] lemma infClosed (L : Sublattice α) : InfClosed (L : Set α) := L.infClosed'
@[simp] lemma isSublattice (L : Sublattice α) : IsSublattice (L : Set α) :=
  ⟨L.supClosed, L.infClosed⟩

@[simp] lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := Iff.rfl
@[simp] lemma mem_mk (h_sup h_inf) : a ∈ mk s h_sup h_inf ↔ a ∈ s := Iff.rfl
@[simp, norm_cast] lemma coe_mk (h_sup h_inf) : mk s h_sup h_inf = s := rfl
@[simp] lemma mk_le_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf ≤ mk t ht_sup ht_inf ↔ s ⊆ t := Iff.rfl
@[simp] lemma mk_lt_mk (hs_sup hs_inf ht_sup ht_inf) :
    mk s hs_sup hs_inf < mk t ht_sup ht_inf ↔ s ⊂ t := Iff.rfl

/-- Copy of a sublattice with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (L : Sublattice α) (s : Set α) (hs : s = L) : Sublattice α where
  carrier := s
  supClosed' := hs.symm ▸ L.supClosed'
  infClosed' := hs.symm ▸ L.infClosed'

@[simp, norm_cast] lemma coe_copy (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = s := rfl

lemma copy_eq (L : Sublattice α) (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

/-- Two sublattices are equal if they have the same elements. -/
lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext

/-- A sublattice of a lattice inherits a supremum. -/
instance instSupCoe : Sup L where
  sup a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/-- A sublattice of a lattice inherits an infimum. -/
instance instInfCoe : Inf L where
  inf a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩

@[simp, norm_cast] lemma coe_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
@[simp, norm_cast] lemma coe_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl

/-- A sublattice of a lattice inherits a lattice structure. -/
instance instLatticeCoe (L : Sublattice α) : Lattice L :=
  Subtype.coe_injective.lattice _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- A sublattice of a distributive lattice inherits a distributive lattice structure. -/
instance instDistribLatticeCoe {α : Type*} [DistribLattice α] (L : Sublattice α) :
    DistribLattice L :=
  Subtype.coe_injective.distribLattice _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The natural lattice hom from a sublattice to the original lattice. -/
def subtype (L : Sublattice α) : LatticeHom L α where
  toFun := ((↑) : L → α)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp, norm_cast] lemma coe_subtype (L : Sublattice α) : L.subtype = ((↑) : L → α) := rfl
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl

lemma subtype_injective (L : Sublattice α) : Injective <| subtype L := Subtype.coe_injective

/-- The inclusion homomorphism from a sublattice `L` to a bigger sublattice `M`. -/
def inclusion (h : L ≤ M) : LatticeHom L M where
  toFun := Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp] lemma coe_inclusion (h : L ≤ M) : inclusion h = Set.inclusion h := rfl
lemma inclusion_apply (h : L ≤ M) (a : L) : inclusion h a = Set.inclusion h a := rfl

lemma inclusion_injective (h : L ≤ M) : Injective <| inclusion h := Set.inclusion_injective h

@[simp] lemma inclusion_rfl (L : Sublattice α) : inclusion le_rfl = LatticeHom.id L := rfl
@[simp] lemma subtype_comp_inclusion (h : L ≤ M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/-- The maximum sublattice of a lattice. -/
instance instTop : Top (Sublattice α) where
  top.carrier := univ
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/-- The empty sublattice of a lattice. -/
instance instBot : Bot (Sublattice α) where
  bot.carrier := ∅
  bot.supClosed' := supClosed_empty
  bot.infClosed' := infClosed_empty

/-- The inf of two sublattices is their intersection. -/
instance instInf : Inf (Sublattice α) where
  inf L M := { carrier := L ∩ M
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

/-- The inf of sublattices is their intersection. -/
instance instInfSet : InfSet (Sublattice α) where
  sInf S := { carrier := ⨅ L ∈ S, L
              supClosed' := supClosed_sInter <| forall_mem_range.2 fun L ↦ supClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.supClosed
              infClosed' := infClosed_sInter <| forall_mem_range.2 fun L ↦ infClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.infClosed }

instance instInhabited : Inhabited (Sublattice α) := ⟨⊥⟩

/-- The top sublattice is isomorphic to the lattice.

This is the sublattice version of `Equiv.Set.univ α`. -/
def topEquiv : (⊤ : Sublattice α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := Iff.rfl

@[simp, norm_cast] lemma coe_top : (⊤ : Sublattice α) = (univ : Set α) := rfl
@[simp, norm_cast] lemma coe_bot : (⊥ : Sublattice α) = (∅ : Set α) := rfl
@[simp, norm_cast] lemma coe_inf' (L M : Sublattice α) : L ⊓ M = (L : Set α) ∩ M := rfl
@[simp, norm_cast] lemma coe_sInf (S : Set (Sublattice α)) : sInf S = ⋂ L ∈ S, (L : Set α) := rfl
@[simp, norm_cast] lemma coe_iInf (f : ι → Sublattice α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by
  simp [iInf]

@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [← coe_top, coe_inj]
@[simp, norm_cast] lemma coe_eq_empty : L = (∅ : Set α) ↔ L = ⊥ := by rw [← coe_bot, coe_inj]

@[simp] lemma not_mem_bot (a : α) : a ∉ (⊥ : Sublattice α) := id
@[simp] lemma mem_top (a : α) : a ∈ (⊤ : Sublattice α) := mem_univ _
@[simp] lemma mem_inf : a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M := Iff.rfl
@[simp] lemma mem_sInf {S : Set (Sublattice α)} : a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L := by
  rw [← SetLike.mem_coe]; simp
@[simp] lemma mem_iInf {f : ι → Sublattice α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe]; simp

/-- Sublattices of a lattice form a complete lattice. -/
instance instCompleteLattice : CompleteLattice (Sublattice α) where
  bot := ⊥
  bot_le := fun _S _a ↦ False.elim
  top := ⊤
  le_top := fun _S a _ha ↦ mem_top a
  inf := (· ⊓ ·)
  le_inf := fun _L _M _N hM hN _a ha ↦ ⟨hM ha, hN ha⟩
  inf_le_left := fun _L _M _a ↦ And.left
  inf_le_right := fun _L _M _a ↦ And.right
  __ := completeLatticeOfInf (Sublattice α)
      fun _s ↦ IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf

lemma subsingleton_iff : Subsingleton (Sublattice α) ↔ IsEmpty α :=
  ⟨fun _ ↦ univ_eq_empty_iff.1 <| coe_inj.2 <| Subsingleton.elim ⊤ ⊥,
    fun _ ↦ SetLike.coe_injective.subsingleton⟩

instance [IsEmpty α] : Unique (Sublattice α) where
  uniq _ := @Subsingleton.elim _ (subsingleton_iff.2 ‹_›) _ _

/-- The preimage of a sublattice along a lattice homomorphism. -/
def comap (f : LatticeHom α β) (L : Sublattice β) : Sublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast] lemma coe_comap (L : Sublattice β) (f : LatticeHom α β) : L.comap f = f ⁻¹' L :=
  rfl

@[simp] lemma mem_comap {L : Sublattice β} : a ∈ L.comap f ↔ f a ∈ L := Iff.rfl

lemma comap_mono : Monotone (comap f) := fun _ _ ↦ preimage_mono

@[simp] lemma comap_id (L : Sublattice α) : L.comap (LatticeHom.id _) = L := rfl

@[simp] lemma comap_comap (L : Sublattice γ) (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.comap g).comap f = L.comap (g.comp f) := rfl

/-- The image of a sublattice along a monoid homomorphism is a sublattice. -/
def map (f : LatticeHom α β) (L : Sublattice α) : Sublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

@[simp] lemma coe_map (f : LatticeHom α β) (L : Sublattice α) : (L.map f : Set β) = f '' L := rfl
@[simp] lemma mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := Iff.rfl

lemma mem_map_of_mem (f : LatticeHom α β) {a : α} : a ∈ L → f a ∈ L.map f := mem_image_of_mem f
lemma apply_coe_mem_map (f : LatticeHom α β) (a : L) : f a ∈ L.map f := mem_map_of_mem f a.prop

lemma map_mono : Monotone (map f) := fun _ _ ↦ image_subset _

@[simp] lemma map_id : L.map (LatticeHom.id α) = L := SetLike.coe_injective <| image_id _

@[simp] lemma map_map (g : LatticeHom β γ) (f : LatticeHom α β) :
    (L.map f).map g = L.map (g.comp f) := SetLike.coe_injective <| image_image _ _ _

lemma mem_map_equiv {f : α ≃o β} {a : β} : a ∈ L.map f ↔ f.symm a ∈ L := Set.mem_image_equiv

lemma apply_mem_map_iff (hf : Injective f) : f a ∈ L.map f ↔ a ∈ L := hf.mem_set_image

lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : Sublattice α) :
    L.map f = L.comap (f.symm : LatticeHom β α) :=
  SetLike.coe_injective <| f.toEquiv.image_eq_preimage L

lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : Sublattice α) :
    L.comap f = L.map (f.symm : LatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm

lemma map_symm_eq_iff_eq_map {M : Sublattice β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

lemma map_le_iff_le_comap {f : LatticeHom α β} {M : Sublattice β} : L.map f ≤ M ↔ L ≤ M.comap f :=
  image_subset_iff

lemma gc_map_comap (f : LatticeHom α β) : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ map_le_iff_le_comap

@[simp] lemma map_bot (f : LatticeHom α β) : (⊥ : Sublattice α).map f = ⊥ := (gc_map_comap f).l_bot

lemma map_sup (f : LatticeHom α β) (L M : Sublattice α) : (L ⊔ M).map f = L.map f ⊔ M.map f :=
  (gc_map_comap f).l_sup

lemma map_iSup (f : LatticeHom α β) (L : ι → Sublattice α) : (⨆ i, L i).map f = ⨆ i, (L i).map f :=
  (gc_map_comap f).l_iSup

@[simp] lemma comap_top (f : LatticeHom α β) : (⊤ : Sublattice β).comap f = ⊤ :=
  (gc_map_comap f).u_top

lemma comap_inf (L M : Sublattice β) (f : LatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf

lemma comap_iInf (f : LatticeHom α β) (s : ι → Sublattice β) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (gc_map_comap f).u_iInf

lemma map_inf_le (L M : Sublattice α) (f : LatticeHom α β) : map f (L ⊓ M) ≤ map f L ⊓ map f M :=
  map_mono.map_inf_le _ _

lemma le_comap_sup (L M : Sublattice β) (f : LatticeHom α β) :
    comap f L ⊔ comap f M ≤ comap f (L ⊔ M) := comap_mono.le_map_sup _ _

lemma le_comap_iSup (f : LatticeHom α β) (L : ι → Sublattice β) :
    ⨆ i, (L i).comap f ≤ (⨆ i, L i).comap f := comap_mono.le_map_iSup

lemma map_inf (L M : Sublattice α) (f : LatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

lemma map_top (f : LatticeHom α β) (h : Surjective f) : Sublattice.map f ⊤ = ⊤ :=
  SetLike.coe_injective <| by simp [h.range_eq]

end Sublattice
