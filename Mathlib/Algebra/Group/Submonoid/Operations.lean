/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.Algebra.Group.Nat
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.submonoid.operations from "leanprover-community/mathlib"@"cf8e77c636317b059a8ce20807a29cf3772a0640"

/-!
# Operations on `Submonoid`s

In this file we define various operations on `Submonoid`s and `MonoidHom`s.

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

### Operations on `MonoidHom`s

* `MonoidHom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `MonoidHom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `MonoidHom.restrict`: restrict a monoid homomorphism to a submonoid;
* `MonoidHom.codRestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `MonoidHom.mrangeRestrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/

assert_not_exists MonoidWithZero

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


section

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `Additive M`. -/
@[simps]
def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) where
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
#align submonoid.to_add_submonoid_symm_apply_coe Submonoid.toAddSubmonoid_symm_apply_coe
#align submonoid.to_add_submonoid_apply_coe Submonoid.toAddSubmonoid_apply_coe

/-- Additive submonoids of an additive monoid `Additive M` are isomorphic to submonoids of `M`. -/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm
#align add_submonoid.to_submonoid' AddSubmonoid.toSubmonoid'

theorem Submonoid.toAddSubmonoid_closure (S : Set M) :
    Submonoid.toAddSubmonoid (Submonoid.closure S)
      = AddSubmonoid.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid.le_symm_apply.1 <|
      Submonoid.closure_le.2 (AddSubmonoid.subset_closure (M := Additive M)))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := M))
#align submonoid.to_add_submonoid_closure Submonoid.toAddSubmonoid_closure

theorem AddSubmonoid.toSubmonoid'_closure (S : Set (Additive M)) :
    AddSubmonoid.toSubmonoid' (AddSubmonoid.closure S)
      = Submonoid.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <|
      AddSubmonoid.closure_le.2 (Submonoid.subset_closure (M := M)))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := Additive M))
#align add_submonoid.to_submonoid'_closure AddSubmonoid.toSubmonoid'_closure

end

section

variable {A : Type*} [AddZeroClass A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `Multiplicative A`. -/
@[simps]
def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) where
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
#align add_submonoid.to_submonoid_symm_apply_coe AddSubmonoid.toSubmonoid_symm_apply_coe
#align add_submonoid.to_submonoid_apply_coe AddSubmonoid.toSubmonoid_apply_coe

/-- Submonoids of a monoid `Multiplicative A` are isomorphic to additive submonoids of `A`. -/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm
#align submonoid.to_add_submonoid' Submonoid.toAddSubmonoid'

theorem AddSubmonoid.toSubmonoid_closure (S : Set A) :
    (AddSubmonoid.toSubmonoid) (AddSubmonoid.closure S)
      = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid.to_galoisConnection.l_le <|
      AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))
#align add_submonoid.to_submonoid_closure AddSubmonoid.toSubmonoid_closure

theorem Submonoid.toAddSubmonoid'_closure (S : Set (Multiplicative A)) :
    Submonoid.toAddSubmonoid' (Submonoid.closure S)
      = AddSubmonoid.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
      Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))
#align submonoid.to_add_submonoid'_closure Submonoid.toAddSubmonoid'_closure

end

namespace Submonoid

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

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
#align add_submonoid.comap AddSubmonoid.comap

@[to_additive (attr := simp)]
theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl
#align submonoid.coe_comap Submonoid.coe_comap
#align add_submonoid.coe_comap AddSubmonoid.coe_comap

@[to_additive (attr := simp)]
theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align submonoid.mem_comap Submonoid.mem_comap
#align add_submonoid.mem_comap AddSubmonoid.mem_comap

@[to_additive]
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
#align submonoid.comap_comap Submonoid.comap_comap
#align add_submonoid.comap_comap AddSubmonoid.comap_comap

@[to_additive (attr := simp)]
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S :=
  ext (by simp)
#align submonoid.comap_id Submonoid.comap_id
#align add_submonoid.comap_id AddSubmonoid.comap_id

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
#align add_submonoid.map AddSubmonoid.map

@[to_additive (attr := simp)]
theorem coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl
#align submonoid.coe_map Submonoid.coe_map
#align add_submonoid.coe_map AddSubmonoid.coe_map

@[to_additive (attr := simp)]
theorem mem_map {f : F} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y := Iff.rfl
#align submonoid.mem_map Submonoid.mem_map
#align add_submonoid.mem_map AddSubmonoid.mem_map

@[to_additive]
theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
#align submonoid.mem_map_of_mem Submonoid.mem_map_of_mem
#align add_submonoid.mem_map_of_mem AddSubmonoid.mem_map_of_mem

@[to_additive]
theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.2
#align submonoid.apply_coe_mem_map Submonoid.apply_coe_mem_map
#align add_submonoid.apply_coe_mem_map AddSubmonoid.apply_coe_mem_map

@[to_additive]
theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
#align submonoid.map_map Submonoid.map_map
#align add_submonoid.map_map AddSubmonoid.map_map

-- The simpNF linter says that the LHS can be simplified via `Submonoid.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[to_additive (attr := simp 1100, nolint simpNF)]
theorem mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image
#align submonoid.mem_map_iff_mem Submonoid.mem_map_iff_mem
#align add_submonoid.mem_map_iff_mem AddSubmonoid.mem_map_iff_mem

@[to_additive]
theorem map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
#align submonoid.map_le_iff_le_comap Submonoid.map_le_iff_le_comap
#align add_submonoid.map_le_iff_le_comap AddSubmonoid.map_le_iff_le_comap

@[to_additive]
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap
#align submonoid.gc_map_comap Submonoid.gc_map_comap
#align add_submonoid.gc_map_comap AddSubmonoid.gc_map_comap

@[to_additive]
theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
#align submonoid.map_le_of_le_comap Submonoid.map_le_of_le_comap
#align add_submonoid.map_le_of_le_comap AddSubmonoid.map_le_of_le_comap

@[to_additive]
theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
#align submonoid.le_comap_of_map_le Submonoid.le_comap_of_map_le
#align add_submonoid.le_comap_of_map_le AddSubmonoid.le_comap_of_map_le

@[to_additive]
theorem le_comap_map {f : F} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align submonoid.le_comap_map Submonoid.le_comap_map
#align add_submonoid.le_comap_map AddSubmonoid.le_comap_map

@[to_additive]
theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
#align submonoid.map_comap_le Submonoid.map_comap_le
#align add_submonoid.map_comap_le AddSubmonoid.map_comap_le

@[to_additive]
theorem monotone_map {f : F} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
#align submonoid.monotone_map Submonoid.monotone_map
#align add_submonoid.monotone_map AddSubmonoid.monotone_map

@[to_additive]
theorem monotone_comap {f : F} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u
#align submonoid.monotone_comap Submonoid.monotone_comap
#align add_submonoid.monotone_comap AddSubmonoid.monotone_comap

@[to_additive (attr := simp)]
theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _
#align submonoid.map_comap_map Submonoid.map_comap_map
#align add_submonoid.map_comap_map AddSubmonoid.map_comap_map

@[to_additive (attr := simp)]
theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
#align submonoid.comap_map_comap Submonoid.comap_map_comap
#align add_submonoid.comap_map_comap AddSubmonoid.comap_map_comap

@[to_additive]
theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align submonoid.map_sup Submonoid.map_sup
#align add_submonoid.map_sup AddSubmonoid.map_sup

@[to_additive]
theorem map_iSup {ι : Sort*} (f : F) (s : ι → Submonoid M) : (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
#align submonoid.map_supr Submonoid.map_iSup
#align add_submonoid.map_supr AddSubmonoid.map_iSup

@[to_additive]
theorem comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf
#align submonoid.comap_inf Submonoid.comap_inf
#align add_submonoid.comap_inf AddSubmonoid.comap_inf

@[to_additive]
theorem comap_iInf {ι : Sort*} (f : F) (s : ι → Submonoid N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf
#align submonoid.comap_infi Submonoid.comap_iInf
#align add_submonoid.comap_infi AddSubmonoid.comap_iInf

@[to_additive (attr := simp)]
theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align submonoid.map_bot Submonoid.map_bot
#align add_submonoid.map_bot AddSubmonoid.map_bot

@[to_additive (attr := simp)]
theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align submonoid.comap_top Submonoid.comap_top
#align add_submonoid.comap_top AddSubmonoid.comap_top

@[to_additive (attr := simp)]
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
#align submonoid.map_id Submonoid.map_id
#align add_submonoid.map_id AddSubmonoid.map_id

section GaloisCoinsertion

variable {ι : Type*} {f : F} (hf : Function.Injective f)

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align submonoid.gci_map_comap Submonoid.gciMapComap
#align add_submonoid.gci_map_comap AddSubmonoid.gciMapComap

@[to_additive]
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
#align submonoid.comap_map_eq_of_injective Submonoid.comap_map_eq_of_injective
#align add_submonoid.comap_map_eq_of_injective AddSubmonoid.comap_map_eq_of_injective

@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align submonoid.comap_surjective_of_injective Submonoid.comap_surjective_of_injective
#align add_submonoid.comap_surjective_of_injective AddSubmonoid.comap_surjective_of_injective

@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align submonoid.map_injective_of_injective Submonoid.map_injective_of_injective
#align add_submonoid.map_injective_of_injective AddSubmonoid.map_injective_of_injective

@[to_additive]
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
#align submonoid.comap_inf_map_of_injective Submonoid.comap_inf_map_of_injective
#align add_submonoid.comap_inf_map_of_injective AddSubmonoid.comap_inf_map_of_injective

@[to_additive]
theorem comap_iInf_map_of_injective (S : ι → Submonoid M) : (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _
#align submonoid.comap_infi_map_of_injective Submonoid.comap_iInf_map_of_injective
#align add_submonoid.comap_infi_map_of_injective AddSubmonoid.comap_iInf_map_of_injective

@[to_additive]
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
#align submonoid.comap_sup_map_of_injective Submonoid.comap_sup_map_of_injective
#align add_submonoid.comap_sup_map_of_injective AddSubmonoid.comap_sup_map_of_injective

@[to_additive]
theorem comap_iSup_map_of_injective (S : ι → Submonoid M) : (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _
#align submonoid.comap_supr_map_of_injective Submonoid.comap_iSup_map_of_injective
#align add_submonoid.comap_supr_map_of_injective AddSubmonoid.comap_iSup_map_of_injective

@[to_additive]
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
#align submonoid.map_le_map_iff_of_injective Submonoid.map_le_map_iff_of_injective
#align add_submonoid.map_le_map_iff_of_injective AddSubmonoid.map_le_map_iff_of_injective

@[to_additive]
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
#align submonoid.map_strict_mono_of_injective Submonoid.map_strictMono_of_injective
#align add_submonoid.map_strict_mono_of_injective AddSubmonoid.map_strictMono_of_injective

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : F} (hf : Function.Surjective f)

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align submonoid.gi_map_comap Submonoid.giMapComap
#align add_submonoid.gi_map_comap AddSubmonoid.giMapComap

@[to_additive]
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
#align submonoid.map_comap_eq_of_surjective Submonoid.map_comap_eq_of_surjective
#align add_submonoid.map_comap_eq_of_surjective AddSubmonoid.map_comap_eq_of_surjective

@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align submonoid.map_surjective_of_surjective Submonoid.map_surjective_of_surjective
#align add_submonoid.map_surjective_of_surjective AddSubmonoid.map_surjective_of_surjective

@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align submonoid.comap_injective_of_surjective Submonoid.comap_injective_of_surjective
#align add_submonoid.comap_injective_of_surjective AddSubmonoid.comap_injective_of_surjective

@[to_additive]
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
#align submonoid.map_inf_comap_of_surjective Submonoid.map_inf_comap_of_surjective
#align add_submonoid.map_inf_comap_of_surjective AddSubmonoid.map_inf_comap_of_surjective

@[to_additive]
theorem map_iInf_comap_of_surjective (S : ι → Submonoid N) : (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _
#align submonoid.map_infi_comap_of_surjective Submonoid.map_iInf_comap_of_surjective
#align add_submonoid.map_infi_comap_of_surjective AddSubmonoid.map_iInf_comap_of_surjective

@[to_additive]
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
#align submonoid.map_sup_comap_of_surjective Submonoid.map_sup_comap_of_surjective
#align add_submonoid.map_sup_comap_of_surjective AddSubmonoid.map_sup_comap_of_surjective

@[to_additive]
theorem map_iSup_comap_of_surjective (S : ι → Submonoid N) : (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _
#align submonoid.map_supr_comap_of_surjective Submonoid.map_iSup_comap_of_surjective
#align add_submonoid.map_supr_comap_of_surjective AddSubmonoid.map_iSup_comap_of_surjective

@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
#align submonoid.comap_le_comap_iff_of_surjective Submonoid.comap_le_comap_iff_of_surjective
#align add_submonoid.comap_le_comap_iff_of_surjective AddSubmonoid.comap_le_comap_iff_of_surjective

@[to_additive]
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u
#align submonoid.comap_strict_mono_of_surjective Submonoid.comap_strictMono_of_surjective
#align add_submonoid.comap_strict_mono_of_surjective AddSubmonoid.comap_strictMono_of_surjective

end GaloisInsertion

end Submonoid

namespace OneMemClass

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `AddSubmonoid` of an `AddMonoid` inherits a zero."]
instance one : One S' :=
  ⟨⟨1, OneMemClass.one_mem S'⟩⟩
#align one_mem_class.has_one OneMemClass.one
#align zero_mem_class.has_zero ZeroMemClass.zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : S') : M₁) = 1 :=
  rfl
#align one_mem_class.coe_one OneMemClass.coe_one
#align zero_mem_class.coe_zero ZeroMemClass.coe_zero

variable {S'}

@[to_additive (attr := simp, norm_cast)]
theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)
#align one_mem_class.coe_eq_one OneMemClass.coe_eq_one
#align zero_mem_class.coe_eq_zero ZeroMemClass.coe_eq_zero

variable (S')

@[to_additive]
theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl
#align one_mem_class.one_def OneMemClass.one_def
#align zero_mem_class.zero_def ZeroMemClass.zero_def

end OneMemClass

variable {A : Type*} [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

/-- An `AddSubmonoid` of an `AddMonoid` inherits a scalar multiplication. -/
instance AddSubmonoidClass.nSMul {M} [AddMonoid M] {A : Type*} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : SMul ℕ S :=
  ⟨fun n a => ⟨n • a.1, nsmul_mem a.2 n⟩⟩
#align add_submonoid_class.has_nsmul AddSubmonoidClass.nSMul

namespace SubmonoidClass

/-- A submonoid of a monoid inherits a power operator. -/
instance nPow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩
#align submonoid_class.has_pow SubmonoidClass.nPow

attribute [to_additive existing nSMul] nPow

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : ℕ) : ↑(x ^ n) = (x : M) ^ n :=
  rfl
#align submonoid_class.coe_pow SubmonoidClass.coe_pow
#align add_submonoid_class.coe_nsmul AddSubmonoidClass.coe_nsmul

@[to_additive (attr := simp)]
theorem mk_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x ∈ S) (n : ℕ) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl
#align submonoid_class.mk_pow SubmonoidClass.mk_pow
#align add_submonoid_class.mk_nsmul AddSubmonoidClass.mk_nsmul

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure."]
instance (priority := 75) toMulOneClass {M : Type*} [MulOneClass M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S :=
    Subtype.coe_injective.mulOneClass (↑) rfl (fun _ _ => rfl)
#align submonoid_class.to_mul_one_class SubmonoidClass.toMulOneClass
#align add_submonoid_class.to_add_zero_class AddSubmonoidClass.toAddZeroClass

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure."]
instance (priority := 75) toMonoid {M : Type*} [Monoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S :=
  Subtype.coe_injective.monoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
#align submonoid_class.to_monoid SubmonoidClass.toMonoid
#align add_submonoid_class.to_add_monoid AddSubmonoidClass.toAddMonoid

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive "An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`."]
instance (priority := 75) toCommMonoid {M} [CommMonoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : CommMonoid S :=
  Subtype.coe_injective.commMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_comm_monoid SubmonoidClass.toCommMonoid
#align add_submonoid_class.to_add_comm_monoid AddSubmonoidClass.toAddCommMonoid

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`."]
def subtype : S' →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp
#align submonoid_class.subtype SubmonoidClass.subtype
#align add_submonoid_class.subtype AddSubmonoidClass.subtype

@[to_additive (attr := simp)]
theorem coe_subtype : (SubmonoidClass.subtype S' : S' → M) = Subtype.val :=
  rfl
#align submonoid_class.coe_subtype SubmonoidClass.coe_subtype
#align add_submonoid_class.coe_subtype AddSubmonoidClass.coe_subtype

end SubmonoidClass

namespace Submonoid

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `AddSubmonoid` of an `AddMonoid` inherits an addition."]
instance mul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩
#align submonoid.has_mul Submonoid.mul
#align add_submonoid.has_add AddSubmonoid.add

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `AddSubmonoid` of an `AddMonoid` inherits a zero."]
instance one : One S :=
  ⟨⟨_, S.one_mem⟩⟩
#align submonoid.has_one Submonoid.one
#align add_submonoid.has_zero AddSubmonoid.zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
  rfl
#align submonoid.coe_mul Submonoid.coe_mul
#align add_submonoid.coe_add AddSubmonoid.coe_add

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl
#align submonoid.coe_one Submonoid.coe_one
#align add_submonoid.coe_zero AddSubmonoid.coe_zero

@[to_additive (attr := simp)]
lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 := by simp [← SetLike.coe_eq_coe]

@[to_additive (attr := simp)]
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl
#align submonoid.mk_mul_mk Submonoid.mk_mul_mk
#align add_submonoid.mk_add_mk AddSubmonoid.mk_add_mk

@[to_additive]
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl
#align submonoid.mul_def Submonoid.mul_def
#align add_submonoid.add_def AddSubmonoid.add_def

@[to_additive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl
#align submonoid.one_def Submonoid.one_def
#align add_submonoid.zero_def AddSubmonoid.zero_def

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure."]
instance toMulOneClass {M : Type*} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  Subtype.coe_injective.mulOneClass (↑) rfl fun _ _ => rfl
#align submonoid.to_mul_one_class Submonoid.toMulOneClass
#align add_submonoid.to_add_zero_class AddSubmonoid.toAddZeroClass

@[to_additive]
protected theorem pow_mem {M : Type*} [Monoid M] (S : Submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) :
    x ^ n ∈ S :=
  pow_mem hx n
#align submonoid.pow_mem Submonoid.pow_mem
#align add_submonoid.nsmul_mem AddSubmonoid.nsmul_mem

-- Porting note: coe_pow removed, syntactic tautology
#noalign submonoid.coe_pow
#noalign add_submonoid.coe_smul

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure."]
instance toMonoid {M : Type*} [Monoid M] (S : Submonoid M) : Monoid S :=
  Subtype.coe_injective.monoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_monoid Submonoid.toMonoid
#align add_submonoid.to_add_monoid AddSubmonoid.toAddMonoid

/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive "An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`."]
instance toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S :=
  Subtype.coe_injective.commMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_comm_monoid Submonoid.toCommMonoid
#align add_submonoid.to_add_comm_monoid AddSubmonoid.toAddCommMonoid

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`."]
def subtype : S →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp
#align submonoid.subtype Submonoid.subtype
#align add_submonoid.subtype AddSubmonoid.subtype

@[to_additive (attr := simp)]
theorem coe_subtype : ⇑S.subtype = Subtype.val :=
  rfl
#align submonoid.coe_subtype Submonoid.coe_subtype
#align add_submonoid.coe_subtype AddSubmonoid.coe_subtype

/-- The top submonoid is isomorphic to the monoid. -/
@[to_additive (attr := simps) "The top additive submonoid is isomorphic to the additive monoid."]
def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align submonoid.top_equiv Submonoid.topEquiv
#align add_submonoid.top_equiv AddSubmonoid.topEquiv
#align submonoid.top_equiv_apply Submonoid.topEquiv_apply
#align submonoid.top_equiv_symm_apply_coe Submonoid.topEquiv_symm_apply_coe

@[to_additive (attr := simp)]
theorem topEquiv_toMonoidHom : ((topEquiv : _ ≃* M) : _ →* M) = (⊤ : Submonoid M).subtype :=
  rfl
#align submonoid.top_equiv_to_monoid_hom Submonoid.topEquiv_toMonoidHom
#align add_submonoid.top_equiv_to_add_monoid_hom AddSubmonoid.topEquiv_toAddMonoidHom

/-- A subgroup is isomorphic to its image under an injective function. If you have an isomorphism,
use `MulEquiv.submonoidMap` for better definitional equalities. -/
@[to_additive "An additive subgroup is isomorphic to its image under an injective function. If you
have an isomorphism, use `AddEquiv.addSubmonoidMap` for better definitional equalities."]
noncomputable def equivMapOfInjective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }
#align submonoid.equiv_map_of_injective Submonoid.equivMapOfInjective
#align add_submonoid.equiv_map_of_injective AddSubmonoid.equivMapOfInjective

@[to_additive (attr := simp)]
theorem coe_equivMapOfInjective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl
#align submonoid.coe_equiv_map_of_injective_apply Submonoid.coe_equivMapOfInjective_apply
#align add_submonoid.coe_equiv_map_of_injective_apply AddSubmonoid.coe_equivMapOfInjective_apply

@[to_additive (attr := simp)]
theorem closure_closure_coe_preimage {s : Set M} : closure (((↑) : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    Subtype.recOn x fun x hx _ => by
      refine closure_induction' (p := fun y hy ↦ ⟨y, hy⟩ ∈ closure (((↑) : closure s → M) ⁻¹' s))
        (fun g hg => subset_closure hg) ?_ (fun g₁ g₂ hg₁ hg₂ => ?_) hx
      · exact Submonoid.one_mem _
      · exact Submonoid.mul_mem _
#align submonoid.closure_closure_coe_preimage Submonoid.closure_closure_coe_preimage
#align add_submonoid.closure_closure_coe_preimage AddSubmonoid.closure_closure_coe_preimage

/-- Given submonoids `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive prod
      "Given `AddSubmonoid`s `s`, `t` of `AddMonoid`s `A`, `B` respectively, `s × t`
      as an `AddSubmonoid` of `A × B`."]
def prod (s : Submonoid M) (t : Submonoid N) :
    Submonoid (M × N) where
  carrier := s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩
#align submonoid.prod Submonoid.prod
#align add_submonoid.prod AddSubmonoid.prod

@[to_additive coe_prod]
theorem coe_prod (s : Submonoid M) (t : Submonoid N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl
#align submonoid.coe_prod Submonoid.coe_prod
#align add_submonoid.coe_prod AddSubmonoid.coe_prod

@[to_additive mem_prod]
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align submonoid.mem_prod Submonoid.mem_prod
#align add_submonoid.mem_prod AddSubmonoid.mem_prod

@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
#align submonoid.prod_mono Submonoid.prod_mono
#align add_submonoid.prod_mono AddSubmonoid.prod_mono

@[to_additive prod_top]
theorem prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]
#align submonoid.prod_top Submonoid.prod_top
#align add_submonoid.prod_top AddSubmonoid.prod_top

@[to_additive top_prod]
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod s = s.comap (MonoidHom.snd M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
#align submonoid.top_prod Submonoid.top_prod
#align add_submonoid.top_prod AddSubmonoid.top_prod

@[to_additive (attr := simp) top_prod_top]
theorem top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align submonoid.top_prod_top Submonoid.top_prod_top
#align add_submonoid.top_prod_top AddSubmonoid.top_prod_top

@[to_additive bot_prod_bot]
theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod, Prod.one_eq_mk]
#align submonoid.bot_prod_bot Submonoid.bot_prod_bot
-- Porting note: to_additive translated the name incorrectly in mathlib 3.
#align add_submonoid.bot_sum_bot AddSubmonoid.bot_prod_bot

/-- The product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prodEquiv
      "The product of additive submonoids is isomorphic to their product as additive monoids"]
def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }
#align submonoid.prod_equiv Submonoid.prodEquiv
#align add_submonoid.prod_equiv AddSubmonoid.prodEquiv

open MonoidHom

@[to_additive]
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥ :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
      ⟨p.1, hps, Prod.ext rfl <| (Set.eq_of_mem_singleton hp1).symm⟩⟩
#align submonoid.map_inl Submonoid.map_inl
#align add_submonoid.map_inl AddSubmonoid.map_inl

@[to_additive]
theorem map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩
#align submonoid.map_inr Submonoid.map_inr
#align add_submonoid.map_inr AddSubmonoid.map_inr

@[to_additive (attr := simp) prod_bot_sup_bot_prod]
theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    (prod s ⊥) ⊔ (prod ⊥ t) = prod s t :=
  (le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : prod s ⊥ ≤ prod s ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t ≤ prod s ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)
#align submonoid.prod_bot_sup_bot_prod Submonoid.prod_bot_sup_bot_prod
#align add_submonoid.prod_bot_sup_bot_prod AddSubmonoid.prod_bot_sup_bot_prod

@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
  Set.mem_image_equiv
#align submonoid.mem_map_equiv Submonoid.mem_map_equiv
#align add_submonoid.mem_map_equiv AddSubmonoid.mem_map_equiv

@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align submonoid.map_equiv_eq_comap_symm Submonoid.map_equiv_eq_comap_symm
#align add_submonoid.map_equiv_eq_comap_symm AddSubmonoid.map_equiv_eq_comap_symm

@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align submonoid.comap_equiv_eq_map_symm Submonoid.comap_equiv_eq_map_symm
#align add_submonoid.comap_equiv_eq_map_symm AddSubmonoid.comap_equiv_eq_map_symm

@[to_additive (attr := simp)]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq
#align submonoid.map_equiv_top Submonoid.map_equiv_top
#align add_submonoid.map_equiv_top AddSubmonoid.map_equiv_top

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
#align add_submonoid.le_prod_iff AddSubmonoid.le_prod_iff

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
#align add_submonoid.prod_le_iff AddSubmonoid.prod_le_iff

end Submonoid

namespace MonoidHom

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

open Submonoid

library_note "range copy pattern"/--
For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`Set.range f`. In particular this means that the types `↥(Set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`Set.range` could have been defined as `f '' Set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `Set.range`, and that it introduces a redundant `x ∈ ⊤`
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
#align add_monoid_hom.mrange AddMonoidHom.mrange

@[to_additive (attr := simp)]
theorem coe_mrange (f : F) : (mrange f : Set N) = Set.range f :=
  rfl
#align monoid_hom.coe_mrange MonoidHom.coe_mrange
#align add_monoid_hom.coe_mrange AddMonoidHom.coe_mrange

@[to_additive (attr := simp)]
theorem mem_mrange {f : F} {y : N} : y ∈ mrange f ↔ ∃ x, f x = y :=
  Iff.rfl
#align monoid_hom.mem_mrange MonoidHom.mem_mrange
#align add_monoid_hom.mem_mrange AddMonoidHom.mem_mrange

@[to_additive]
theorem mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f :=
  Submonoid.copy_eq _
#align monoid_hom.mrange_eq_map MonoidHom.mrange_eq_map
#align add_monoid_hom.mrange_eq_map AddMonoidHom.mrange_eq_map

@[to_additive (attr := simp)]
theorem mrange_id : mrange (MonoidHom.id M) = ⊤ := by
  simp [mrange_eq_map]

@[to_additive]
theorem map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = mrange (comp g f) := by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f
#align monoid_hom.map_mrange MonoidHom.map_mrange
#align add_monoid_hom.map_mrange AddMonoidHom.map_mrange

@[to_additive]
theorem mrange_top_iff_surjective {f : F} : mrange f = (⊤ : Submonoid N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_mrange, coe_top]) Set.range_iff_surjective
#align monoid_hom.mrange_top_iff_surjective MonoidHom.mrange_top_iff_surjective
#align add_monoid_hom.mrange_top_iff_surjective AddMonoidHom.mrange_top_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive (attr := simp)
  "The range of a surjective `AddMonoid` hom is the whole of the codomain."]
theorem mrange_top_of_surjective (f : F) (hf : Function.Surjective f) :
    mrange f = (⊤ : Submonoid N) :=
  mrange_top_iff_surjective.2 hf
#align monoid_hom.mrange_top_of_surjective MonoidHom.mrange_top_of_surjective
#align add_monoid_hom.mrange_top_of_surjective AddMonoidHom.mrange_top_of_surjective

@[to_additive]
theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align monoid_hom.mclosure_preimage_le MonoidHom.mclosure_preimage_le
#align add_monoid_hom.mclosure_preimage_le AddMonoidHom.mclosure_preimage_le

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
#align add_monoid_hom.map_mclosure AddMonoidHom.map_mclosure

@[to_additive (attr := simp)]
theorem mclosure_range (f : F) : closure (Set.range f) = mrange f := by
  rw [← Set.image_univ, ← map_mclosure, mrange_eq_map, closure_univ]

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive "Restriction of an `AddMonoid` hom to an `AddSubmonoid` of the domain."]
def restrict {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M →* N)
    (s : S) : s →* N :=
  f.comp (SubmonoidClass.subtype _)
#align monoid_hom.restrict MonoidHom.restrict
#align add_monoid_hom.restrict AddMonoidHom.restrict

@[to_additive (attr := simp)]
theorem restrict_apply {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
    (f : M →* N) (s : S) (x : s) : f.restrict s x = f x :=
  rfl
#align monoid_hom.restrict_apply MonoidHom.restrict_apply
#align add_monoid_hom.restrict_apply AddMonoidHom.restrict_apply

@[to_additive (attr := simp)]
theorem restrict_mrange (f : M →* N) : mrange (f.restrict S) = S.map f := by
  simp [SetLike.ext_iff]
#align monoid_hom.restrict_mrange MonoidHom.restrict_mrange
#align add_monoid_hom.restrict_mrange AddMonoidHom.restrict_mrange

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive (attr := simps apply)
  "Restriction of an `AddMonoid` hom to an `AddSubmonoid` of the codomain."]
def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) :
    M →* s where
  toFun n := ⟨f n, h n⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.cod_restrict MonoidHom.codRestrict
#align add_monoid_hom.cod_restrict AddMonoidHom.codRestrict
#align monoid_hom.cod_restrict_apply MonoidHom.codRestrict_apply

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[to_additive "Restriction of an `AddMonoid` hom to its range interpreted as a submonoid."]
def mrangeRestrict {N} [MulOneClass N] (f : M →* N) : M →* (mrange f) :=
  (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict MonoidHom.mrangeRestrict
#align add_monoid_hom.mrange_restrict AddMonoidHom.mrangeRestrict

@[to_additive (attr := simp)]
theorem coe_mrangeRestrict {N} [MulOneClass N] (f : M →* N) (x : M) :
    (f.mrangeRestrict x : N) = f x :=
  rfl
#align monoid_hom.coe_mrange_restrict MonoidHom.coe_mrangeRestrict
#align add_monoid_hom.coe_mrange_restrict AddMonoidHom.coe_mrangeRestrict

@[to_additive]
theorem mrangeRestrict_surjective (f : M →* N) : Function.Surjective f.mrangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict_surjective MonoidHom.mrangeRestrict_surjective
#align add_monoid_hom.mrange_restrict_surjective AddMonoidHom.mrangeRestrict_surjective

/-- The multiplicative kernel of a monoid hom is the submonoid of elements `x : G` such
that `f x = 1` -/
@[to_additive
      "The additive kernel of an `AddMonoid` hom is the `AddSubmonoid` of
      elements such that `f x = 0`"]
def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f
#align monoid_hom.mker MonoidHom.mker
#align add_monoid_hom.mker AddMonoidHom.mker

@[to_additive]
theorem mem_mker (f : F) {x : M} : x ∈ mker f ↔ f x = 1 :=
  Iff.rfl
#align monoid_hom.mem_mker MonoidHom.mem_mker
#align add_monoid_hom.mem_mker AddMonoidHom.mem_mker

@[to_additive]
theorem coe_mker (f : F) : (mker f : Set M) = (f : M → N) ⁻¹' {1} :=
  rfl
#align monoid_hom.coe_mker MonoidHom.coe_mker
#align add_monoid_hom.coe_mker AddMonoidHom.coe_mker

@[to_additive]
instance decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· ∈ mker f) := fun x =>
  decidable_of_iff (f x = 1) (mem_mker f)
#align monoid_hom.decidable_mem_mker MonoidHom.decidableMemMker
#align add_monoid_hom.decidable_mem_mker AddMonoidHom.decidableMemMker

@[to_additive]
theorem comap_mker (g : N →* P) (f : M →* N) : g.mker.comap f = mker (comp g f) :=
  rfl
#align monoid_hom.comap_mker MonoidHom.comap_mker
#align add_monoid_hom.comap_mker AddMonoidHom.comap_mker

@[to_additive (attr := simp)]
theorem comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f :=
  rfl
#align monoid_hom.comap_bot' MonoidHom.comap_bot'
#align add_monoid_hom.comap_bot' AddMonoidHom.comap_bot'

@[to_additive (attr := simp)]
theorem restrict_mker (f : M →* N) : mker (f.restrict S) = f.mker.comap S.subtype :=
  rfl
#align monoid_hom.restrict_mker MonoidHom.restrict_mker
#align add_monoid_hom.restrict_mker AddMonoidHom.restrict_mker

@[to_additive]
theorem mrangeRestrict_mker (f : M →* N) : mker (mrangeRestrict f) = mker f := by
  ext x
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp
#align monoid_hom.range_restrict_mker MonoidHom.mrangeRestrict_mker
#align add_monoid_hom.range_restrict_mker AddMonoidHom.mrangeRestrict_mker

@[to_additive (attr := simp)]
theorem mker_one : mker (1 : M →* N) = ⊤ := by
  ext
  simp [mem_mker]
#align monoid_hom.mker_one MonoidHom.mker_one
#align add_monoid_hom.mker_zero AddMonoidHom.mker_zero

@[to_additive prod_map_comap_prod']
theorem prod_map_comap_prod' {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N']
    (f : M →* N) (g : M' →* N') (S : Submonoid N) (S' : Submonoid N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _
#align monoid_hom.prod_map_comap_prod' MonoidHom.prod_map_comap_prod'
-- Porting note: to_additive translated the name incorrectly in mathlib 3.
#align add_monoid_hom.sum_map_comap_sum' AddMonoidHom.prod_map_comap_prod'

@[to_additive mker_prod_map]
theorem mker_prod_map {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M →* N)
    (g : M' →* N') : mker (prodMap f g) = f.mker.prod (mker g) := by
  rw [← comap_bot', ← comap_bot', ← comap_bot', ← prod_map_comap_prod', bot_prod_bot]
#align monoid_hom.mker_prod_map MonoidHom.mker_prod_map
-- Porting note: to_additive translated the name incorrectly in mathlib 3.
#align add_monoid_hom.mker_sum_map AddMonoidHom.mker_prod_map

@[to_additive (attr := simp)]
theorem mker_inl : mker (inl M N) = ⊥ := by
  ext x
  simp [mem_mker]
#align monoid_hom.mker_inl MonoidHom.mker_inl
#align add_monoid_hom.mker_inl AddMonoidHom.mker_inl

@[to_additive (attr := simp)]
theorem mker_inr : mker (inr M N) = ⊥ := by
  ext x
  simp [mem_mker]
#align monoid_hom.mker_inr MonoidHom.mker_inr
#align add_monoid_hom.mker_inr AddMonoidHom.mker_inr

@[to_additive (attr := simp)]
lemma mker_fst : mker (fst M N) = .prod ⊥ ⊤ := SetLike.ext fun _ => (and_true_iff _).symm

@[to_additive (attr := simp)]
lemma mker_snd : mker (snd M N) = .prod ⊤ ⊥ := SetLike.ext fun _ => (true_and_iff _).symm

/-- The `MonoidHom` from the preimage of a submonoid to itself. -/
@[to_additive (attr := simps)
      "the `AddMonoidHom` from the preimage of an additive submonoid to itself."]
def submonoidComap (f : M →* N) (N' : Submonoid N) :
    N'.comap f →* N' where
  toFun x := ⟨f x, x.2⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.submonoid_comap MonoidHom.submonoidComap
#align add_monoid_hom.add_submonoid_comap AddMonoidHom.addSubmonoidComap
#align monoid_hom.submonoid_comap_apply_coe MonoidHom.submonoidComap_apply_coe
#align add_monoid_hom.submonoid_comap_apply_coe AddMonoidHom.addSubmonoidComap_apply_coe

/-- The `MonoidHom` from a submonoid to its image.
See `MulEquiv.SubmonoidMap` for a variant for `MulEquiv`s. -/
@[to_additive (attr := simps)
      "the `AddMonoidHom` from an additive submonoid to its image. See
      `AddEquiv.AddSubmonoidMap` for a variant for `AddEquiv`s."]
def submonoidMap (f : M →* N) (M' : Submonoid M) : M' →* M'.map f where
  toFun x := ⟨f x, ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.eq <| f.map_one
  map_mul' x y := Subtype.eq <| f.map_mul x y
#align monoid_hom.submonoid_map MonoidHom.submonoidMap
#align add_monoid_hom.add_submonoid_map AddMonoidHom.addSubmonoidMap
#align monoid_hom.submonoid_map_apply_coe MonoidHom.submonoidMap_apply_coe
#align add_monoid_hom.submonoid_map_apply_coe AddMonoidHom.addSubmonoidMap_apply_coe

@[to_additive]
theorem submonoidMap_surjective (f : M →* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩
#align monoid_hom.submonoid_map_surjective MonoidHom.submonoidMap_surjective
#align add_monoid_hom.add_submonoid_map_surjective AddMonoidHom.addSubmonoidMap_surjective

end MonoidHom

namespace Submonoid

open MonoidHom

@[to_additive]
theorem mrange_inl : mrange (inl M N) = prod ⊤ ⊥ := by simpa only [mrange_eq_map] using map_inl ⊤
#align submonoid.mrange_inl Submonoid.mrange_inl
#align add_submonoid.mrange_inl AddSubmonoid.mrange_inl

@[to_additive]
theorem mrange_inr : mrange (inr M N) = prod ⊥ ⊤ := by simpa only [mrange_eq_map] using map_inr ⊤
#align submonoid.mrange_inr Submonoid.mrange_inr
#align add_submonoid.mrange_inr AddSubmonoid.mrange_inr

@[to_additive]
theorem mrange_inl' : mrange (inl M N) = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)
#align submonoid.mrange_inl' Submonoid.mrange_inl'
#align add_submonoid.mrange_inl' AddSubmonoid.mrange_inl'

@[to_additive]
theorem mrange_inr' : mrange (inr M N) = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)
#align submonoid.mrange_inr' Submonoid.mrange_inr'
#align add_submonoid.mrange_inr' AddSubmonoid.mrange_inr'

@[to_additive (attr := simp)]
theorem mrange_fst : mrange (fst M N) = ⊤ :=
  mrange_top_of_surjective (fst M N) <| @Prod.fst_surjective _ _ ⟨1⟩
#align submonoid.mrange_fst Submonoid.mrange_fst
#align add_submonoid.mrange_fst AddSubmonoid.mrange_fst

@[to_additive (attr := simp)]
theorem mrange_snd : mrange (snd M N) = ⊤ :=
  mrange_top_of_surjective (snd M N) <| @Prod.snd_surjective _ _ ⟨1⟩
#align submonoid.mrange_snd Submonoid.mrange_snd
#align add_submonoid.mrange_snd AddSubmonoid.mrange_snd

@[to_additive prod_eq_bot_iff]
theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]
#align submonoid.prod_eq_bot_iff Submonoid.prod_eq_bot_iff
-- Porting note: to_additive translated the name incorrectly in mathlib 3.
#align add_submonoid.sum_eq_bot_iff AddSubmonoid.prod_eq_bot_iff

@[to_additive prod_eq_top_iff]
theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← mrange_eq_map, mrange_fst,
    mrange_snd]
#align submonoid.prod_eq_top_iff Submonoid.prod_eq_top_iff
-- Porting note: to_additive translated the name incorrectly in mathlib 3.
#align add_submonoid.sum_eq_top_iff AddSubmonoid.prod_eq_top_iff

@[to_additive (attr := simp)]
theorem mrange_inl_sup_mrange_inr : mrange (inl M N) ⊔ mrange (inr M N) = ⊤ := by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]
#align submonoid.mrange_inl_sup_mrange_inr Submonoid.mrange_inl_sup_mrange_inr
#align add_submonoid.mrange_inl_sup_mrange_inr AddSubmonoid.mrange_inl_sup_mrange_inr

/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive
      "The `AddMonoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align submonoid.inclusion Submonoid.inclusion
#align add_submonoid.inclusion AddSubmonoid.inclusion

@[to_additive (attr := simp)]
theorem range_subtype (s : Submonoid M) : mrange s.subtype = s :=
  SetLike.coe_injective <| (coe_mrange _).trans <| Subtype.range_coe
#align submonoid.range_subtype Submonoid.range_subtype
#align add_submonoid.range_subtype AddSubmonoid.range_subtype

@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align submonoid.eq_top_iff' Submonoid.eq_top_iff'
#align add_submonoid.eq_top_iff' AddSubmonoid.eq_top_iff'

@[to_additive]
theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) :=
  SetLike.ext_iff.trans <| by simp (config := { contextual := true }) [iff_def, S.one_mem]
#align submonoid.eq_bot_iff_forall Submonoid.eq_bot_iff_forall
#align add_submonoid.eq_bot_iff_forall AddSubmonoid.eq_bot_iff_forall

@[to_additive]
theorem eq_bot_of_subsingleton [Subsingleton S] : S = ⊥ := by
  rw [eq_bot_iff_forall]
  intro y hy
  simpa using _root_.congr_arg ((↑) : S → M) <| Subsingleton.elim (⟨y, hy⟩ : S) 1

@[to_additive]
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) :=
  calc
    Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _) (hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ ∃ x ∈ S, x ≠ (1 : M) := by simp [Ne]
#align submonoid.nontrivial_iff_exists_ne_one Submonoid.nontrivial_iff_exists_ne_one
#align add_submonoid.nontrivial_iff_exists_ne_zero AddSubmonoid.nontrivial_iff_exists_ne_zero

/-- A submonoid is either the trivial submonoid or nontrivial. -/
@[to_additive "An additive submonoid is either the trivial additive submonoid or nontrivial."]
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]
#align submonoid.bot_or_nontrivial Submonoid.bot_or_nontrivial
#align add_submonoid.bot_or_nontrivial AddSubmonoid.bot_or_nontrivial

/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
@[to_additive
      "An additive submonoid is either the trivial additive submonoid or contains a nonzero
      element."]
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp
#align submonoid.bot_or_exists_ne_one Submonoid.bot_or_exists_ne_one
#align add_submonoid.bot_or_exists_ne_zero AddSubmonoid.bot_or_exists_ne_zero

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
#align add_equiv.add_submonoid_congr AddEquiv.addSubmonoidCongr

-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.
This is a bidirectional version of `MonoidHom.mrange_restrict`. -/
@[to_additive (attr := simps (config := { simpRhs := true }))
      "An additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M`
      defines an additive equivalence between `M` and `f.mrange`.
      This is a bidirectional version of `AddMonoidHom.mrange_restrict`. "]
def ofLeftInverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) :
    M ≃* MonoidHom.mrange f :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ f.mrange.subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse' MulEquiv.ofLeftInverse'
#align add_equiv.of_left_inverse' AddEquiv.ofLeftInverse'
#align mul_equiv.of_left_inverse'_apply MulEquiv.ofLeftInverse'_apply
#align add_equiv.of_left_inverse'_apply AddEquiv.ofLeftInverse'_apply
#align mul_equiv.of_left_inverse'_symm_apply MulEquiv.ofLeftInverse'_symm_apply
#align add_equiv.of_left_inverse'_symm_apply AddEquiv.ofLeftInverse'_symm_apply

/-- A `MulEquiv` `φ` between two monoids `M` and `N` induces a `MulEquiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`.
See `MonoidHom.submonoidMap` for a variant for `MonoidHom`s. -/
@[to_additive
      "An `AddEquiv` `φ` between two additive monoids `M` and `N` induces an `AddEquiv`
      between a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. See
      `AddMonoidHom.addSubmonoidMap` for a variant for `AddMonoidHom`s."]
def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e :=
  { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }
#align mul_equiv.submonoid_map MulEquiv.submonoidMap
#align add_equiv.add_submonoid_map AddEquiv.addSubmonoidMap

@[to_additive (attr := simp)]
theorem coe_submonoidMap_apply (e : M ≃* N) (S : Submonoid M) (g : S) :
    ((submonoidMap e S g : S.map (e : M →* N)) : N) = e g :=
  rfl
#align mul_equiv.coe_submonoid_map_apply MulEquiv.coe_submonoidMap_apply
#align add_equiv.coe_add_submonoid_map_apply AddEquiv.coe_addSubmonoidMap_apply

@[to_additive (attr := simp) AddEquiv.add_submonoid_map_symm_apply]
theorem submonoidMap_symm_apply (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M →* N)) :
    (e.submonoidMap S).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ :=
  rfl
#align mul_equiv.submonoid_map_symm_apply MulEquiv.submonoidMap_symm_apply
#align add_equiv.add_submonoid_map_symm_apply AddEquiv.add_submonoid_map_symm_apply

end MulEquiv

@[to_additive (attr := simp)]
theorem Submonoid.equivMapOfInjective_coe_mulEquiv (e : M ≃* N) :
    S.equivMapOfInjective (e : M →* N) (EquivLike.injective e) = e.submonoidMap S := by
  ext
  rfl
#align submonoid.equiv_map_of_injective_coe_mul_equiv Submonoid.equivMapOfInjective_coe_mulEquiv
#align add_submonoid.equiv_map_of_injective_coe_add_equiv AddSubmonoid.equivMapOfInjective_coe_addEquiv

section Actions

/-! ### Actions by `Submonoid`s

These instances transfer the action by an element `m : M` of a monoid `M` written as `m • a` onto
the action by an element `s : S` of a submonoid `S : Submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `Monoid.toMulAction`, enabling
`s • m` as an alias for `↑s * m`.
-/


namespace Submonoid

variable {M' : Type*} {α β : Type*}

section MulOneClass

variable [MulOneClass M']

@[to_additive]
instance smul [SMul M' α] (S : Submonoid M') : SMul S α :=
  SMul.comp _ S.subtype

@[to_additive]
instance smulCommClass_left [SMul M' β] [SMul α β] [SMulCommClass M' α β]
    (S : Submonoid M') : SMulCommClass S α β :=
  ⟨fun a _ _ => (smul_comm (a : M') _ _ : _)⟩
#align submonoid.smul_comm_class_left Submonoid.smulCommClass_left
#align add_submonoid.vadd_comm_class_left AddSubmonoid.vaddCommClass_left

@[to_additive]
instance smulCommClass_right [SMul α β] [SMul M' β] [SMulCommClass α M' β]
    (S : Submonoid M') : SMulCommClass α S β :=
  ⟨fun a s => (smul_comm a (s : M') : _)⟩
#align submonoid.smul_comm_class_right Submonoid.smulCommClass_right
#align add_submonoid.vadd_comm_class_right AddSubmonoid.vaddCommClass_right

/-- Note that this provides `IsScalarTower S M' M'` which is needed by `SMulMulAssoc`. -/
instance isScalarTower [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β]
      (S : Submonoid M') :
    IsScalarTower S α β :=
  ⟨fun a => (smul_assoc (a : M') : _)⟩

section SMul
variable [SMul M' α] {S : Submonoid M'}

@[to_additive] lemma smul_def (g : S) (a : α) : g • a = (g : M') • a := rfl
#align submonoid.smul_def Submonoid.smul_def
#align add_submonoid.vadd_def AddSubmonoid.vadd_def

@[to_additive (attr := simp)]
lemma mk_smul (g : M') (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

instance faithfulSMul [FaithfulSMul M' α] : FaithfulSMul S α :=
  ⟨fun h => Subtype.ext <| eq_of_smul_eq_smul h⟩

end SMul
end MulOneClass

variable [Monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      "The additive action by an `AddSubmonoid` is the action by the underlying `AddMonoid`. "]
instance mulAction [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  MulAction.compHom _ S.subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance distribMulAction [AddMonoid α] [DistribMulAction M' α] (S : Submonoid M') :
    DistribMulAction S α :=
  DistribMulAction.compHom _ S.subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction M' α] (S : Submonoid M') :
    MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.subtype

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance


end Submonoid

end Actions

section Units

namespace Submonoid

/-- The multiplicative equivalence between the type of units of `M` and the submonoid of unit
elements of `M`. -/
@[to_additive (attr := simps!) " The additive equivalence between the type of additive units of `M`
  and the additive submonoid whose elements are the additive units of `M`. "]
noncomputable def unitsTypeEquivIsUnitSubmonoid [Monoid M] : Mˣ ≃* IsUnit.submonoid M where
  toFun x := ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv x := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

end Submonoid

end Units

open AddSubmonoid Set

namespace Nat

@[simp] lemma addSubmonoid_closure_one : closure ({1} : Set ℕ) = ⊤ := by
  refine (eq_top_iff' _).2 <| Nat.rec (zero_mem _) ?_
  simp_rw [Nat.succ_eq_add_one]
  exact fun n hn ↦ AddSubmonoid.add_mem _ hn <| subset_closure <| Set.mem_singleton _

end Nat
