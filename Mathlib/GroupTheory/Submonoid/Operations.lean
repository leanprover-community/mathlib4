/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.submonoid.operations
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Monoid.Cancel.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Submonoid.Basic
import Mathlib.GroupTheory.Subsemigroup.Operations

/-!
# Operations on `submonoid`s

In this file we define various operations on `submonoid`s and `monoid_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `Submonoid.toAddSubmonoid`, `Submonoid.toAddSubmonoid'`, `AddSubmonoid.toSubmonoid`,
  `AddSubmonoid.toSubmonoid'`: convert between multiplicative and additive submonoids of `M`,
  `Multiplicative M`, and `Additive M`. These are stated as `OrderIso`s.

### (Commutative) monoid structure on a submonoid

* `Submonoid.toMonoid`, `Submonoid.toCommMonoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `Submonoid.MulAction`, `Submonoid.DistribMulAction`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `Submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `Submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `Submonoid.prod`: product of two submonoids `s : Submonoid M` and `t : Submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `Submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `Submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `MulEquiv.submonoidCongr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `Submonoid.prodEquiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `monoid_hom`s

* `MonoidHom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `MonoidHom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `MonoidHom.restrict`: restrict a monoid homomorphism to a submonoid;
* `MonoidHom.codRestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `MonoidHom.mrangeRestrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/


variable {M N P : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
@[simps]
def Submonoid.toAddSubmonoid :
    Submonoid M ≃o
      AddSubmonoid
        (Additive
          M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb}
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
#align submonoid.to_add_submonoid Submonoid.toAddSubmonoid

/-- Additive submonoids of an additive monoid `Additive M` are isomorphic to submonoids of `M`. -/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm
#align add_submonoid.to_submonoid' AddSubmonoid.toSubmonoid'

-- Porting note: TODO simplify the proof below, this used to be a single proof term
theorem Submonoid.to_add_submonoid_closure (S : Set M) :
    Submonoid.toAddSubmonoid (Submonoid.closure S)
      = AddSubmonoid.closure (Additive.toMul ⁻¹' S) := by
    apply le_antisymm
      (Submonoid.toAddSubmonoid.le_symm_apply.mp (Submonoid.closure_le.mpr _))
      (AddSubmonoid.closure_le.mpr _)
    exact @AddSubmonoid.subset_closure (Additive M) _ S
    exact @Submonoid.subset_closure M _ S

-- Porting note: TODO simplify the proof below, this used to be a single proof term
theorem AddSubmonoid.to_submonoid'_closure (S : Set (Additive M)) :
    AddSubmonoid.toSubmonoid' (AddSubmonoid.closure S)
      = Submonoid.closure (Multiplicative.ofAdd ⁻¹' S) := by
    apply le_antisymm
      (AddSubmonoid.toSubmonoid'.le_symm_apply.mp (AddSubmonoid.closure_le.mpr _))
      (Submonoid.closure_le.mpr _)
    exact @Submonoid.subset_closure M _ S
    exact @AddSubmonoid.subset_closure (Additive M) _ S
#align add_submonoid.to_submonoid'_closure AddSubmonoid.to_submonoid'_closure

end

section

variable {A : Type _} [AddZeroClass A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `Multiplicative A`. -/
@[simps]
def AddSubmonoid.toSubmonoid :
    AddSubmonoid A ≃o
      Submonoid
        (Multiplicative
          A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb}
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
#align add_submonoid.to_submonoid AddSubmonoid.toSubmonoid

/-- Submonoids of a monoid `Multiplicative A` are isomorphic to additive submonoids of `A`. -/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm
#align submonoid.to_add_submonoid' Submonoid.toAddSubmonoid'

-- Porting note: TODO simplify the proof below, this used to be a single proof term
theorem AddSubmonoid.to_submonoid_closure (S : Set A) :
    (AddSubmonoid.toSubmonoid) (AddSubmonoid.closure S)
      = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) := by
  apply le_antisymm
    (AddSubmonoid.toSubmonoid.to_galoisConnection.l_le <|
      AddSubmonoid.closure_le.mpr _)
    (Submonoid.closure_le.mpr _)
  exact @Submonoid.subset_closure (Multiplicative A) _ S
  exact @AddSubmonoid.subset_closure A _ S
#align add_submonoid.to_submonoid_closure AddSubmonoid.to_submonoid_closure

-- Porting note: TODO simplify the proof below, this used to be a single proof term
theorem Submonoid.to_add_submonoid'_closure (S : Set (Multiplicative A)) :
    Submonoid.toAddSubmonoid' (Submonoid.closure S)
      = AddSubmonoid.closure (Additive.ofMul ⁻¹' S) := by
  apply le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
      Submonoid.closure_le.2 _)
    (AddSubmonoid.closure_le.2 _)
  exact @AddSubmonoid.subset_closure A _ S
  exact @Submonoid.subset_closure (Multiplicative A) _ S
#align submonoid.to_add_submonoid'_closure Submonoid.to_add_submonoid'_closure

end

namespace Submonoid

variable {F : Type _} [mc : MonoidHomClass F M N]

open Set

/-!
### `comap` and `map`
-/

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive
      "The preimage of an `AddSubmonoid` along an `AddMonoid` homomorphism is an `AddSubmonoid`."]
def comap (f : F) (S : Submonoid N) :
    Submonoid M where
  carrier := f ⁻¹' S
  one_mem' := show f 1 ∈ S by rw [map_one]; exact S.one_mem
  mul_mem' ha hb := show f (_ * _) ∈ S by rw [map_mul]; exact S.mul_mem ha hb
#align submonoid.comap Submonoid.comap

@[simp, to_additive]
theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl
#align submonoid.coe_comap Submonoid.coe_comap

@[simp, to_additive]
theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align submonoid.mem_comap Submonoid.mem_comap

@[to_additive]
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
#align submonoid.comap_comap Submonoid.comap_comap

@[simp, to_additive]
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S :=
  ext (by simp)
#align submonoid.comap_id Submonoid.comap_id

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive
      "The image of an `AddSubmonoid` along an `AddMonoid` homomorphism is an `AddSubmonoid`."]
def map (f : F) (S : Submonoid M) :
    Submonoid N where
  carrier := f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩;
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul]⟩
#align submonoid.map Submonoid.map

@[simp, to_additive]
theorem coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl
#align submonoid.coe_map Submonoid.coe_map

@[simp, to_additive]
theorem mem_map {f : F} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y := by
  rw [← bex_def]
  exact mem_image_iff_bex
#align submonoid.mem_map Submonoid.mem_map

@[to_additive]
theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
#align submonoid.mem_map_of_mem Submonoid.mem_map_of_mem

@[to_additive]
theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.2
#align submonoid.apply_coe_mem_map Submonoid.apply_coe_mem_map

@[to_additive]
theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
#align submonoid.map_map Submonoid.map_map

@[to_additive]
theorem mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image
#align submonoid.mem_map_iff_mem Submonoid.mem_map_iff_mem

@[to_additive]
theorem map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
#align submonoid.map_le_iff_le_comap Submonoid.map_le_iff_le_comap

@[to_additive]
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap
#align submonoid.gc_map_comap Submonoid.gc_map_comap

@[to_additive]
theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
#align submonoid.map_le_of_le_comap Submonoid.map_le_of_le_comap

@[to_additive]
theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
#align submonoid.le_comap_of_map_le Submonoid.le_comap_of_map_le

@[to_additive]
theorem le_comap_map {f : F} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align submonoid.le_comap_map Submonoid.le_comap_map

@[to_additive]
theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
#align submonoid.map_comap_le Submonoid.map_comap_le

@[to_additive]
theorem monotone_map {f : F} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
#align submonoid.monotone_map Submonoid.monotone_map

@[to_additive]
theorem monotone_comap {f : F} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u
#align submonoid.monotone_comap Submonoid.monotone_comap

@[simp, to_additive]
theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _
#align submonoid.map_comap_map Submonoid.map_comap_map

@[simp, to_additive]
theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
#align submonoid.comap_map_comap Submonoid.comap_map_comap

@[to_additive]
theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align submonoid.map_sup Submonoid.map_sup

@[to_additive]
theorem map_supr {ι : Sort _} (f : F) (s : ι → Submonoid M) : (supᵢ s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_supᵢ
#align submonoid.map_supr Submonoid.map_supr

@[to_additive]
theorem comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf
#align submonoid.comap_inf Submonoid.comap_inf

@[to_additive]
theorem comap_infi {ι : Sort _} (f : F) (s : ι → Submonoid N) :
    (infᵢ s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_infᵢ
#align submonoid.comap_infi Submonoid.comap_infi

@[simp, to_additive]
theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align submonoid.map_bot Submonoid.map_bot

@[simp, to_additive]
theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align submonoid.comap_top Submonoid.comap_top

@[simp, to_additive]
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
#align submonoid.map_id Submonoid.map_id

section GaloisCoinsertion

variable {ι : Type _} {f : F} (hf : Function.Injective f)

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align submonoid.gci_map_comap Submonoid.gciMapComap

@[to_additive]
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
#align submonoid.comap_map_eq_of_injective Submonoid.comap_map_eq_of_injective

@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align submonoid.comap_surjective_of_injective Submonoid.comap_surjective_of_injective

@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align submonoid.map_injective_of_injective Submonoid.map_injective_of_injective

@[to_additive]
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
#align submonoid.comap_inf_map_of_injective Submonoid.comap_inf_map_of_injective

@[to_additive]
theorem comap_infi_map_of_injective (S : ι → Submonoid M) : (⨅ i, (S i).map f).comap f = infᵢ S :=
  (gciMapComap hf).u_infᵢ_l _
#align submonoid.comap_infi_map_of_injective Submonoid.comap_infi_map_of_injective

@[to_additive]
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
#align submonoid.comap_sup_map_of_injective Submonoid.comap_sup_map_of_injective

@[to_additive]
theorem comap_supr_map_of_injective (S : ι → Submonoid M) : (⨆ i, (S i).map f).comap f = supᵢ S :=
  (gciMapComap hf).u_supᵢ_l _
#align submonoid.comap_supr_map_of_injective Submonoid.comap_supr_map_of_injective

@[to_additive]
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
#align submonoid.map_le_map_iff_of_injective Submonoid.map_le_map_iff_of_injective

@[to_additive]
theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
#align submonoid.map_strict_mono_of_injective Submonoid.map_strict_mono_of_injective

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : F} (hf : Function.Surjective f)

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align submonoid.gi_map_comap Submonoid.giMapComap

@[to_additive]
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
#align submonoid.map_comap_eq_of_surjective Submonoid.map_comap_eq_of_surjective

@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align submonoid.map_surjective_of_surjective Submonoid.map_surjective_of_surjective

@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align submonoid.comap_injective_of_surjective Submonoid.comap_injective_of_surjective

@[to_additive]
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
#align submonoid.map_inf_comap_of_surjective Submonoid.map_inf_comap_of_surjective

@[to_additive]
theorem map_infi_comap_of_surjective (S : ι → Submonoid N) : (⨅ i, (S i).comap f).map f = infᵢ S :=
  (giMapComap hf).l_infᵢ_u _
#align submonoid.map_infi_comap_of_surjective Submonoid.map_infi_comap_of_surjective

@[to_additive]
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
#align submonoid.map_sup_comap_of_surjective Submonoid.map_sup_comap_of_surjective

@[to_additive]
theorem map_supr_comap_of_surjective (S : ι → Submonoid N) : (⨆ i, (S i).comap f).map f = supᵢ S :=
  (giMapComap hf).l_supᵢ_u _
#align submonoid.map_supr_comap_of_surjective Submonoid.map_supr_comap_of_surjective

@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
#align submonoid.comap_le_comap_iff_of_surjective Submonoid.comap_le_comap_iff_of_surjective

@[to_additive]
theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u
#align submonoid.comap_strict_mono_of_surjective Submonoid.comap_strict_mono_of_surjective

end GaloisInsertion

end Submonoid

namespace OneMemClass

variable {A M₁ : Type _} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance hasOne : One S' :=
  ⟨⟨1, OneMemClass.one_mem S'⟩⟩
#align one_mem_class.has_one OneMemClass.hasOne

@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : S') : M₁) = 1 :=
  rfl
#align one_mem_class.coe_one OneMemClass.coe_one

variable {S'}

@[simp, norm_cast, to_additive]
theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)
#align one_mem_class.coe_eq_one OneMemClass.coe_eq_one

variable (S')

@[to_additive]
theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl
#align one_mem_class.one_def OneMemClass.one_def

end OneMemClass

variable {A : Type _} [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

/-- An `AddSubmonoid` of an `AddMonoid` inherits a scalar multiplication. -/
instance AddSubmonoidClass.SMul {M} [AddMonoid M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : SMul ℕ S :=
  ⟨fun n a => ⟨n • a.1, smul_mem a.2 n⟩⟩
#align add_submonoid_class.has_nsmul AddSubmonoidClass.SMul

namespace SubmonoidClass

/-- A submonoid of a monoid inherits a power operator. -/
instance Pow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩
#align submonoid_class.has_pow SubmonoidClass.Pow

attribute [to_additive] Pow

@[simp, norm_cast, to_additive]
theorem coe_pow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : ℕ) : (x ^ n : M) = (x : M) ^ n :=
  rfl
#align submonoid_class.coe_pow SubmonoidClass.coe_pow

@[simp, to_additive]
theorem mk_pow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x ∈ S) (n : ℕ) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl
#align submonoid_class.mk_pow SubmonoidClass.mk_pow

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `AddSubmonoid` of an unital additive magma inherits an unital additive magma
      structure."]
instance (priority := 75) toMulOneClass {M : Type _} [MulOneClass M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S :=
    Subtype.coe_injective.mulOneClass (↑) rfl (fun _ _ => rfl)

#align submonoid_class.to_mul_one_class SubmonoidClass.toMulOneClass

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance (priority := 75) toMonoid {M : Type _} [Monoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S :=
  Subtype.coe_injective.monoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
#align submonoid_class.to_monoid SubmonoidClass.toMonoid

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance (priority := 75) toCommMonoid {M} [CommMonoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : CommMonoid S :=
  Subtype.coe_injective.commMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_comm_monoid SubmonoidClass.toCommMonoid

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an `OrderedCommMonoid` is an `OrderedCommMonoid`. -/
@[to_additive
      "An `add_submonoid` of an `ordered_add_comm_monoid` is\nan `ordered_add_comm_monoid`."]
instance (priority := 75) toOrderedCommMonoid {M} [OrderedCommMonoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : OrderedCommMonoid S :=
  Subtype.coe_injective.orderedCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_ordered_comm_monoid SubmonoidClass.toOrderedCommMonoid

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `LinearOrderedCommMonoid` is a `LinearOrderedCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of a `LinearOrderedAddCommMonoid` is a `LinearOrderedAddCommMonoid`."]
instance (priority := 75) toLinearOrderedCommMonoid {M} [LinearOrderedCommMonoid M] {A : Type _}
    [SetLike A M] [SubmonoidClass A M] (S : A) : LinearOrderedCommMonoid S :=
  Subtype.coe_injective.linearOrderedCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_linear_ordered_comm_monoid SubmonoidClass.toLinearOrderedCommMonoid

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an `OrderedCancelCommMonoid` is an `OrderedCancelCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of an `OrderedCancelAddCommMonoid` is an `OrderedCancelAddCommMonoid`."]
instance (priority := 75) toOrderedCancelCommMonoid {M} [OrderedCancelCommMonoid M] {A : Type _}
    [SetLike A M] [SubmonoidClass A M] (S : A) : OrderedCancelCommMonoid S :=
  Subtype.coe_injective.orderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_ordered_cancel_comm_monoid SubmonoidClass.toOrderedCancelCommMonoid

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `LinearOrderedCancelCommMonoid` is a `LinearOrderedCancelCommMonoid`.
-/
@[to_additive
      "An `AddSubmonoid` of a `LinearOrderedCancelAddCommMonoid` is
      a `LinearOrderedCancelAddCommMonoid`."]
instance (priority := 75) toLinearOrderedCancelCommMonoid {M} [LinearOrderedCancelCommMonoid M]
    {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) : LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.linearOrderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align
  submonoid_class.to_linear_ordered_cancel_comm_monoid
  SubmonoidClass.toLinearOrderedCancelCommMonoid

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def Subtype : S' →* M := by
  use (⟨Subtype.val, rfl ⟩ : OneHom S' M)
  simp
#align submonoid_class.subtype SubmonoidClass.Subtype

-- porting note: TODO not necessary anymore?
-- @[simp, to_additive]
-- theorem coe_subtype : (SubmonoidClass.Subtype S' : S' → M) = Subtype.val :=
--   rfl
-- #noalign submonoid_class.coe_subtype

end SubmonoidClass

namespace Submonoid

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance hasMul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩
#align submonoid.has_mul Submonoid.hasMul

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance hasOne : One S :=
  ⟨⟨_, S.one_mem⟩⟩
#align submonoid.has_one Submonoid.hasOne

-- porting note: TODO not necessary anymore?
-- @[simp, norm_cast, to_additive]
-- theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
--   rfl
-- #align submonoid.coe_mul Submonoid.coe_mul

-- porting note: TODO not necessary anymore?
-- @[simp, norm_cast, to_additive]
-- theorem coe_one : ((1 : S) : M) = 1 :=
--   rfl
-- #align submonoid.coe_one Submonoid.coe_one

@[simp, to_additive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl
#align submonoid.mk_mul_mk Submonoid.mk_mul_mk

@[to_additive]
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl
#align submonoid.mul_def Submonoid.mul_def

@[to_additive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl
#align submonoid.one_def Submonoid.one_def

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `AddSubmonoid` of an unital additive magma inherits an unital additive magma structure."]
instance toMulOneClass {M : Type _} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  Subtype.coe_injective.mulOneClass (↑) rfl fun _ _ => rfl
#align submonoid.to_mul_one_class Submonoid.toMulOneClass

@[to_additive]
protected theorem pow_mem {M : Type _} [Monoid M] (S : Submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) :
    x ^ n ∈ S :=
  pow_mem hx n
#align submonoid.pow_mem Submonoid.pow_mem

-- porting note: TODO not necessary anymore?
-- @[simp, norm_cast, to_additive]
-- theorem coe_pow {M : Type _} [Monoid M] {S : Submonoid M} (x : S) (n : ℕ) :
--     ↑(x ^ n) = (x ^ n : M) :=
--   rfl
#noalign submonoid.coe_pow

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance toMonoid {M : Type _} [Monoid M] (S : Submonoid M) : Monoid S :=
  Subtype.coe_injective.monoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_monoid Submonoid.toMonoid

/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S :=
  Subtype.coe_injective.commMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_comm_monoid Submonoid.toCommMonoid

/-- A submonoid of an `OrderedCommMonoid` is an `OrderedCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of an `OrderedAddCommMonoid` is an `OrderedAddCommMonoid`."]
instance toOrderedCommMonoid {M} [OrderedCommMonoid M] (S : Submonoid M) : OrderedCommMonoid S :=
  Subtype.coe_injective.orderedCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_ordered_comm_monoid Submonoid.toOrderedCommMonoid

/-- A submonoid of a `LinearOrderedCommMonoid` is a `LinearOrderedCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of a `LinearOrderedAddCommMonoid` is a `LinearOrderedAddCommMonoid`."]
instance toLinearOrderedCommMonoid {M} [LinearOrderedCommMonoid M] (S : Submonoid M) :
    LinearOrderedCommMonoid S :=
  Subtype.coe_injective.linearOrderedCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_linear_ordered_comm_monoid Submonoid.toLinearOrderedCommMonoid

/-- A submonoid of an `OrderedCancelCommMonoid` is an `OrderedCancelCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of an `OrderedCancelAddCommMonoid` is an `OrderedCancelAddCommMonoid`."]
instance toOrderedCancelCommMonoid {M} [OrderedCancelCommMonoid M] (S : Submonoid M) :
    OrderedCancelCommMonoid S :=
  Subtype.coe_injective.orderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_ordered_cancel_comm_monoid Submonoid.toOrderedCancelCommMonoid

/-- A submonoid of a `LinearOrderedCancelCommMonoid` is a `LinearOrderedCancelCommMonoid`.
-/
@[to_additive
      "An `AddSubmonoid` of a `LinearOrderedCancelAddCommMonoid` is
      a `LinearOrderedCancelAddCommMonoid`."]
instance toLinearOrderedCancelCommMonoid {M} [LinearOrderedCancelCommMonoid M] (S : Submonoid M) :
    LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.linearOrderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_linear_ordered_cancel_comm_monoid Submonoid.toLinearOrderedCancelCommMonoid

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def Subtype : S →* M := by
  use (⟨Subtype.val, rfl ⟩ : OneHom S M)
  simp
#align submonoid.subtype Submonoid.Subtype

-- porting note: TODO not necessary anymore?
-- @[simp, to_additive]
-- theorem coe_subtype : ⇑S.Subtype = coe :=
--   rfl
#noalign submonoid.coe_subtype

/-- The top submonoid is isomorphic to the monoid. -/
@[to_additive "The top additive submonoid is isomorphic to the additive monoid.", simps]
def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align submonoid.top_equiv Submonoid.topEquiv

@[simp, to_additive]
theorem top_equiv_to_monoid_hom : (topEquiv : _ ≃* M).toMonoidHom = (⊤ : Submonoid M).Subtype :=
  rfl
#align submonoid.top_equiv_to_monoid_hom Submonoid.top_equiv_to_monoid_hom

/-- A submonoid is isomorphic to its image under an injective function -/
@[to_additive "An additive submonoid is isomorphic to its image under an injective function"]
noncomputable def equivMapOfInjective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }
#align submonoid.equiv_map_of_injective Submonoid.equivMapOfInjective

@[simp, to_additive]
theorem coe_equiv_map_of_injective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl
#align submonoid.coe_equiv_map_of_injective_apply Submonoid.coe_equiv_map_of_injective_apply

@[simp, to_additive]
theorem closure_closure_coe_preimage {s : Set M} : closure (((↑) : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    Subtype.recOn x fun x hx _ => by
      refine' closure_induction' _ (fun g hg => subset_closure hg) _ (fun g₁ g₂ hg₁ hg₂ => _) hx
      · exact Submonoid.one_mem _
      · exact Submonoid.mul_mem _
#align submonoid.closure_closure_coe_preimage Submonoid.closure_closure_coe_preimage

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given submonoids `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive Prod
      "Given `AddSubmonoid`s `s`, `t` of `AddMonoid`s `A`, `B` respectively, `s × t`
      as an `AddSubmonoid` of `A × B`."]
def prod (s : Submonoid M) (t : Submonoid N) :
    Submonoid (M × N) where
  carrier := s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩
#align submonoid.prod Submonoid.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- porting note: TODO not necessary anymore?
@[to_additive coe_prod]
theorem coe_prod (s : Submonoid M) (t : Submonoid N) : (s.prod t : Set (M × N)) = s ×ˢ t :=
  rfl
#align submonoid.coe_prod Submonoid.coe_prod

@[to_additive mem_prod]
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align submonoid.mem_prod Submonoid.mem_prod

@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
#align submonoid.prod_mono Submonoid.prod_mono

@[to_additive prod_top]
theorem prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]
#align submonoid.prod_top Submonoid.prod_top

@[to_additive top_prod]
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod s = s.comap (MonoidHom.snd M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
#align submonoid.top_prod Submonoid.top_prod

@[simp, to_additive top_prod_top]
theorem top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align submonoid.top_prod_top Submonoid.top_prod_top

@[to_additive]
theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod, Prod.one_eq_mk]
#align submonoid.bot_prod_bot Submonoid.bot_prod_bot

/-- The product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prod_equiv
      "The product of additive submonoids is isomorphic to their product as additive monoids"]
def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }
#align submonoid.prod_equiv Submonoid.prodEquiv

open MonoidHom

@[to_additive]
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥ :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
      ⟨p.1, hps, Prod.ext rfl <| (Set.eq_of_mem_singleton hp1).symm⟩⟩
#align submonoid.map_inl Submonoid.map_inl

@[to_additive]
theorem map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩
#align submonoid.map_inr Submonoid.map_inr

-- porting note: TODO currently times out
-- @[simp, to_additive]
-- theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
--     (prod s ⊥) ⊔ (prod ⊥ t) = prod s t :=
--   (le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t)))) fun p hp =>
--     Prod.fst_mul_snd p ▸
--       mul_mem ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
--         ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)
-- #align submonoid.prod_bot_sup_bot_prod Submonoid.prod_bot_sup_bot_prod

@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
    Set.mem_image_equiv
#align submonoid.mem_map_equiv Submonoid.mem_map_equiv

@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align submonoid.map_equiv_eq_comap_symm Submonoid.map_equiv_eq_comap_symm

@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align submonoid.comap_equiv_eq_map_symm Submonoid.comap_equiv_eq_map_symm

@[simp, to_additive]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f.toMonoidHom = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans (Function.Surjective.range_eq f.surjective)
#align submonoid.map_equiv_top Submonoid.map_equiv_top

@[to_additive le_prod_iff]
theorem le_prod_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    u ≤ s.prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩
#align submonoid.le_prod_iff Submonoid.le_prod_iff

@[to_additive prod_le_iff]
theorem prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    s.prod t ≤ u ↔ s.map (inl M N) ≤ u ∧ t.map (inr M N) ≤ u := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 ∈ u := by
      apply hH
      simpa using h1
    have h2' : inr M N x2 ∈ u := by
      apply hK
      simpa using h2
    simpa using Submonoid.mul_mem _ h1' h2'
#align submonoid.prod_le_iff Submonoid.prod_le_iff

end Submonoid

namespace MonoidHom

variable {F : Type _} [mc : MonoidHomClass F M N]

open Submonoid

library_note "range copy pattern"/--
For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`Set.range f`. In particular this means that the types `↥(Set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`Set.range` could have been defined as `f '' Set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `Set.range`, and that it introduces a redudant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`MonoidHom.mrange` would be `(⊤ : Submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `Submonoid.copy` as follows:
```lean
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M :=
{ carrier  := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : Submonoid N :=
((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
```
-/

/-- The range of a monoid homomorphism is a submonoid. See Note [range copy pattern]. -/
@[to_additive "The range of an `AddMonoidHom` is an `AddSubmonoid`."]
def mrange (f : F) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
#align monoid_hom.mrange MonoidHom.mrange

-- porting note: TODO not necessary anymore?
@[simp, to_additive]
theorem coe_mrange (f : F) : (mrange f : Set N) = Set.range f :=
  rfl
#align monoid_hom.coe_mrange MonoidHom.coe_mrange

@[simp, to_additive]
theorem mem_mrange {f : F} {y : N} : y ∈ mrange f ↔ ∃ x, f x = y :=
  Iff.rfl
#align monoid_hom.mem_mrange MonoidHom.mem_mrange

@[to_additive]
theorem mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f :=
  Submonoid.copy_eq _
#align monoid_hom.mrange_eq_map MonoidHom.mrange_eq_map

@[to_additive]
theorem map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = mrange (comp g f) := by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f
#align monoid_hom.map_mrange MonoidHom.map_mrange

@[to_additive]
theorem mrange_top_iff_surjective {f : F} : mrange f = (⊤ : Submonoid N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_mrange, coe_top]) Set.range_iff_surjective
#align monoid_hom.mrange_top_iff_surjective MonoidHom.mrange_top_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive
      "The range of a surjective `AddMonoid` hom is the whole of the codomain."]
theorem mrange_top_of_surjective (f : F) (hf : Function.Surjective f) :
    mrange f = (⊤ : Submonoid N) :=
  mrange_top_iff_surjective.2 hf
#align monoid_hom.mrange_top_of_surjective MonoidHom.mrange_top_of_surjective

@[to_additive]
theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align monoid_hom.mclosure_preimage_le MonoidHom.mclosure_preimage_le

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive
      "The image under an `AddMonoid` hom of the `AddSubmonoid` generated by a set equals
      the `AddSubmonoid` generated by the image of the set."]
theorem map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align monoid_hom.map_mclosure MonoidHom.map_mclosure

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive
      "Restriction of an `AddMonoid` hom to an `AddSubmonoid` of the domain."]
def restrict {N S : Type _} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M →* N)
    (s : S) : s →* N :=
  f.comp (SubmonoidClass.Subtype _)
#align monoid_hom.restrict MonoidHom.restrict

@[simp, to_additive]
theorem restrict_apply {N S : Type _} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
    (f : M →* N) (s : S) (x : s) : f.restrict s x = f x :=
  rfl
#align monoid_hom.restrict_apply MonoidHom.restrict_apply

@[simp, to_additive]
theorem restrict_mrange (f : M →* N) : mrange (f.restrict S) = S.map f := by
  simp [SetLike.ext_iff]
#align monoid_hom.restrict_mrange MonoidHom.restrict_mrange

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an `AddMonoid` hom to an `AddSubmonoid` of the codomain.",
  simps apply]
def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) :
    M →* s where
  toFun n := ⟨f n, h n⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.cod_restrict MonoidHom.codRestrict

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[to_additive
      "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrangeRestrict {N} [MulOneClass N] (f : M →* N) : M →* (mrange f) :=
  (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict MonoidHom.mrangeRestrict

@[simp, to_additive]
theorem coe_mrange_restrict {N} [MulOneClass N] (f : M →* N) (x : M) :
    (f.mrangeRestrict x : N) = f x :=
  rfl
#align monoid_hom.coe_mrange_restrict MonoidHom.coe_mrange_restrict

@[to_additive]
theorem mrange_restrict_surjective (f : M →* N) : Function.Surjective f.mrangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict_surjective MonoidHom.mrange_restrict_surjective

/-- The multiplicative kernel of a monoid hom is the submonoid of elements `x : G` such
that `f x = 1` -/
@[to_additive
      "The additive kernel of an `AddMonoid` hom is the `AddSubmonoid` of
      elements such that `f x = 0`"]
def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f
#align monoid_hom.mker MonoidHom.mker

@[to_additive]
theorem mem_mker (f : F) {x : M} : x ∈ mker f ↔ f x = 1 :=
  Iff.rfl
#align monoid_hom.mem_mker MonoidHom.mem_mker

@[to_additive]
theorem coe_mker (f : F) : (mker f : Set M) = (f : M → N) ⁻¹' {1} :=
  rfl
#align monoid_hom.coe_mker MonoidHom.coe_mker

@[to_additive]
instance decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· ∈ mker f) := fun x =>
  decidable_of_iff (f x = 1) (mem_mker f)
#align monoid_hom.decidable_mem_mker MonoidHom.decidableMemMker

@[to_additive]
theorem comap_mker (g : N →* P) (f : M →* N) : g.mker.comap f = mker (comp g f) :=
  rfl
#align monoid_hom.comap_mker MonoidHom.comap_mker

@[simp, to_additive]
theorem comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f :=
  rfl
#align monoid_hom.comap_bot' MonoidHom.comap_bot'

@[simp, to_additive]
theorem restrict_mker (f : M →* N) : mker (f.restrict S) = f.mker.comap S.Subtype :=
  rfl
#align monoid_hom.restrict_mker MonoidHom.restrict_mker

@[to_additive]
theorem range_restrict_mker (f : M →* N) : mker (mrangeRestrict f) = mker f := by
  ext x
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp
#align monoid_hom.range_restrict_mker MonoidHom.range_restrict_mker

@[simp, to_additive]
theorem mker_one : mker (1 : M →* N) = ⊤ := by
  ext
  simp [mem_mker]
#align monoid_hom.mker_one MonoidHom.mker_one

@[to_additive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N']
    (f : M →* N) (g : M' →* N') (S : Submonoid N) (S' : Submonoid N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _
#align monoid_hom.prod_map_comap_prod' MonoidHom.prod_map_comap_prod'

@[to_additive]
theorem mker_prod_map {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N'] (f : M →* N)
    (g : M' →* N') : mker (prodMap f g) = f.mker.prod (mker g) := by
  rw [← comap_bot', ← comap_bot', ← comap_bot', ← prod_map_comap_prod', bot_prod_bot]
#align monoid_hom.mker_prod_map MonoidHom.mker_prod_map

@[simp, to_additive]
theorem mker_inl : mker (inl M N) = ⊥ := by
  ext x
  simp [mem_mker]
#align monoid_hom.mker_inl MonoidHom.mker_inl

@[simp, to_additive]
theorem mker_inr : mker (inr M N) = ⊥ := by
  ext x
  simp [mem_mker]
#align monoid_hom.mker_inr MonoidHom.mker_inr

/-- The `MonoidHom` from the preimage of a submonoid to itself. -/
@[to_additive "the `add_monoid_hom` from the preimage of an additive submonoid to itself.", simps]
def submonoidComap (f : M →* N) (N' : Submonoid N) :
    N'.comap f →* N' where
  toFun x := ⟨f x, x.2⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.submonoid_comap MonoidHom.submonoidComap

/-- The `MonoidHom` from a submonoid to its image.
See `MulEquiv.SubmonoidMap` for a variant for `MulEquiv`s. -/
@[to_additive
      "the `AddMonoidHom` from an additive submonoid to its image. See
      `AddEquiv.AddSubmonoidMap` for a variant for `AddEquiv`s.",
  simps]
def submonoidMap (f : M →* N) (M' : Submonoid M) :
    M' →* M'.map f where
  toFun x := ⟨f x, ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.eq <| f.map_one
  map_mul' x y := Subtype.eq <| f.map_mul x y
#align monoid_hom.submonoid_map MonoidHom.submonoidMap

@[to_additive]
theorem submonoidMap_surjective (f : M →* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩
#align monoid_hom.submonoid_map_surjective MonoidHom.submonoidMap_surjective

end MonoidHom

namespace Submonoid

open MonoidHom

@[to_additive]
theorem mrange_inl : mrange (inl M N) = prod ⊤ ⊥ := by simpa only [mrange_eq_map] using map_inl ⊤
#align submonoid.mrange_inl Submonoid.mrange_inl

@[to_additive]
theorem mrange_inr : mrange (inr M N) = prod ⊥ ⊤ := by simpa only [mrange_eq_map] using map_inr ⊤
#align submonoid.mrange_inr Submonoid.mrange_inr

@[to_additive]
theorem mrange_inl' : mrange (inl M N) = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)
#align submonoid.mrange_inl' Submonoid.mrange_inl'

@[to_additive]
theorem mrange_inr' : mrange (inr M N) = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)
#align submonoid.mrange_inr' Submonoid.mrange_inr'

@[simp, to_additive]
theorem mrange_fst : mrange (fst M N) = ⊤ :=
  mrange_top_of_surjective (fst M N) <| @Prod.fst_surjective _ _ ⟨1⟩
#align submonoid.mrange_fst Submonoid.mrange_fst

@[simp, to_additive]
theorem mrange_snd : mrange (snd M N) = ⊤ :=
  mrange_top_of_surjective (snd M N) <| @Prod.snd_surjective _ _ ⟨1⟩
#align submonoid.mrange_snd Submonoid.mrange_snd

@[to_additive]
theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]
#align submonoid.prod_eq_bot_iff Submonoid.prod_eq_bot_iff

@[to_additive]
theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← mrange_eq_map, mrange_fst,
    mrange_snd]
#align submonoid.prod_eq_top_iff Submonoid.prod_eq_top_iff

@[simp, to_additive]
theorem mrange_inl_sup_mrange_inr : mrange (inl M N) ⊔ mrange (inr M N) = ⊤ := by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]
#align submonoid.mrange_inl_sup_mrange_inr Submonoid.mrange_inl_sup_mrange_inr

/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive "The `AddMonoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.Subtype.codRestrict _ fun x => h x.2
#align submonoid.inclusion Submonoid.inclusion

@[simp, to_additive]
theorem range_subtype (s : Submonoid M) : mrange s.Subtype = s :=
  SetLike.coe_injective <| (coe_mrange _).trans <| Subtype.range_coe
#align submonoid.range_subtype Submonoid.range_subtype

@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align submonoid.eq_top_iff' Submonoid.eq_top_iff'

@[to_additive]
theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) :=
  SetLike.ext_iff.trans <| by simp (config := { contextual := true }) [iff_def, S.one_mem]
#align submonoid.eq_bot_iff_forall Submonoid.eq_bot_iff_forall

@[to_additive]
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) :=
  calc
    Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _)(hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ ∃ x ∈ S, x ≠ (1 : M) := by simp [Ne.def]

#align submonoid.nontrivial_iff_exists_ne_one Submonoid.nontrivial_iff_exists_ne_one

-- porting note: TODO this proof might need golfing
/-- A submonoid is either the trivial submonoid or nontrivial. -/
@[to_additive
      "An additive submonoid is either the trivial additive submonoid or nontrivial."]
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  have := Classical.em (∀ (x : M), x ∈ S → x = 1)
  simp_rw [not_forall, not_imp, bex_def] at this
  simp [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, this]

#align submonoid.bot_or_nontrivial Submonoid.bot_or_nontrivial

/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
@[to_additive
      "An additive submonoid is either the trivial additive submonoid or contains a nonzero
      element."]
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp
#align submonoid.bot_or_exists_ne_one Submonoid.bot_or_exists_ne_one

end Submonoid

namespace MulEquiv

variable {S} {T : Submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive
      "Makes the identity additive isomorphism from a proof two
      submonoids of an additive monoid are equal."]
def submonoidCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.submonoid_congr MulEquiv.submonoidCongr

-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.
This is a bidirectional version of `MonoidHom.mrange_restrict`. -/
@[to_additive
      "An additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M`
      defines an additive equivalence between `M` and `f.mrange`.
      This is a bidirectional version of `AddMonoidHom.mrange_restrict`. ",
  simps (config := { simpRhs := true })]
def ofLeftInverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) :
    M ≃* MonoidHom.mrange f :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ f.mrange.Subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse' MulEquiv.ofLeftInverse'

/-- A `MulEquiv` `φ` between two monoids `M` and `N` induces a `MulEquiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`.
See `MonoidHom.submonoidMap` for a variant for `MonoidHom`s. -/
@[to_additive
      "An `AddEquiv` `φ` between two additive monoids `M` and `N` induces an `AddEquiv`
      between a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. See
      `AddMonoidHom.addSubmonoidMap` for a variant for `AddMonoidHom`s.",
  simps]
def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e.toMonoidHom :=
  {
    -- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
    e.toMonoidHom.submonoidMap S,
    e.toEquiv.image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }
#align mul_equiv.submonoid_map MulEquiv.submonoidMap

end MulEquiv

section Actions

/-! ### Actions by `submonoid`s

These instances tranfer the action by an element `m : M` of a monoid `M` written as `m • a` onto the
action by an element `s : S` of a submonoid `S : Submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `Monoid.toMulAction`, enabling
`s • m` as an alias for `↑s * m`.
-/


namespace Submonoid

variable {M' : Type _} {α β : Type _}

section MulOneClass

variable [MulOneClass M']

@[to_additive]
instance [SMul M' α] (S : Submonoid M') : SMul S α :=
  SMul.comp _ S.Subtype

@[to_additive]
instance smul_comm_class_left [SMul M' β] [SMul α β] [SMulCommClass M' α β]
    (S : Submonoid M') : SMulCommClass S α β :=
  ⟨fun a _ _ => (smul_comm (a : M') _ _ : _)⟩
#align submonoid.smul_comm_class_left Submonoid.smul_comm_class_left

@[to_additive]
instance smul_comm_class_right [SMul α β] [SMul M' β] [SMulCommClass α M' β]
    (S : Submonoid M') : SMulCommClass α S β :=
  ⟨fun a s => (smul_comm a (s : M') : _)⟩
#align submonoid.smul_comm_class_right Submonoid.smul_comm_class_right

/-- Note that this provides `IsScalarTower S M' M'` which is needed by `SMulMulAssoc`. -/
instance [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β] (S : Submonoid M') :
    IsScalarTower S α β :=
  ⟨fun a => (smul_assoc (a : M') : _)⟩

@[to_additive]
theorem smul_def [SMul M' α] {S : Submonoid M'} (g : S) (m : α) : g • m = (g : M') • m :=
  rfl
#align submonoid.smul_def Submonoid.smul_def

instance [SMul M' α] [FaithfulSMul M' α] (S : Submonoid M') : FaithfulSMul S α :=
  ⟨fun h => Subtype.ext <| eq_of_smul_eq_smul h⟩

end MulOneClass

variable [Monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      "The additive action by an `AddSubmonoid` is the action by the underlying `AddMonoid`. "]
instance [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  MulAction.compHom _ S.Subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [AddMonoid α] [DistribMulAction M' α] (S : Submonoid M') : DistribMulAction S α :=
  DistribMulAction.compHom _ S.Subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [Monoid α] [MulDistribMulAction M' α] (S : Submonoid M') : MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.Subtype

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance
