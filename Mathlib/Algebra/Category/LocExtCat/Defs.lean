/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Extension.Basic

/-!
# The Category of Local extension over a Fixed Residue Field

This file adds definitions and basic lemmas about the category of local extensions
with base algebra `Λ` over a fixed residue field `k`, which serves as
an ambient environment for formal deformation theory.

## Main Definitions

* `LocExtCat Λ k` : The type of objects in the category of local extensions with base algebra `Λ`
  over a fixed residue field `k`.

* `LocExtCat.Hom` : The type of morphisms between objects in `LocAlgCat Λ k`.
  A morphism `f : A ⟶ B` is an extension homomorphism between the underlying extensions.

* `LocExtCat.isoMk`, `LocExtCat.ofIso` : Canonical translations between algebra
  equivalences and categorical isomorphisms.

-/

universe v u

@[expose] public section

noncomputable section

open IsLocalRing CategoryTheory Function Algebra

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The category of local extensions of a fixed residue field `k`. -/
structure LocExtCat (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] extends
    Extension.{u} Λ k where
  of (Λ k) ::
  [localRing : IsLocalRing Ring]

namespace Algebra.Extension

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S] :
    IsLocalRing (Extension.self R S).Ring :=
  inferInstanceAs <| IsLocalRing S

end Algebra.Extension

namespace LocExtCat

variable {A B C : LocExtCat Λ k} {X Y Z : Extension.{u} Λ k}
variable [IsLocalRing X.Ring] [IsLocalRing Y.Ring] [IsLocalRing Z.Ring]

attribute [instance] localRing

initialize_simps_projections LocExtCat (-localRing)

instance coeExtension : CoeOut (LocExtCat Λ k) (Extension.{u} Λ k) where
  coe A := A.toExtension

instance coeRing : CoeSort (LocExtCat Λ k) (Type u) where
  coe A := A.Ring

variable (X) in
lemma coe_of : (of Λ k X : Type u) = X.Ring := rfl

@[simp]
lemma ker_extension : A.ker = maximalIdeal A :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ A.algebraMap_surjective)

/-- The canonical residue map from the underlying ring of an object `A` to `k`.
This is a prefered way to apply residue maps in `LocExtCat`. -/
def residue (A : LocExtCat Λ k) : A →ₐ[Λ] k :=
  IsScalarTower.toAlgHom Λ A k

lemma residue_toRingHom : A.residue = algebraMap A k := rfl

lemma residue_apply {a : A} : A.residue a = algebraMap A k a := rfl

@[simp]
lemma ker_residue : RingHom.ker (residue A) = maximalIdeal A := ker_extension

lemma residue_surjective : Surjective (residue A) := A.algebraMap_surjective

lemma residue_eq_zero_iff {x : A} : residue A x = 0 ↔ x ∈ maximalIdeal A := by
  rw [← RingHom.mem_ker, ker_residue]

/-- The canonical equivalence between the residue field of
the underlying local ring of an object and `k`. -/
def residueEquiv (A : LocExtCat Λ k) : ResidueField A ≃ₐ[Λ] k where
  __ := (Ideal.quotEquivOfEq (ker_residue (A := A)).symm).trans
    (RingHom.quotientKerEquivOfSurjective A.residue_surjective)
  commutes' r := (IsScalarTower.algebraMap_apply Λ A k r).symm

@[simp]
lemma residueEquiv_residue_apply {x : A} :
    A.residueEquiv (IsLocalRing.residue A x) = A.residue x := rfl

/-- The type of morphisms in `LocExtCat` is the same as morphisms of the underlying extensions. -/
@[ext]
structure Hom (A B : LocExtCat Λ k) : Type u where
  hom' : A.toExtension.Hom B.toExtension

instance : Category (LocExtCat Λ k) where
  Hom A B := Hom A B
  id A := ⟨Extension.Hom.id A.toExtension⟩
  comp {A B C} f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (LocExtCat Λ k) (fun A B ↦ A.toExtension.Hom B.toExtension) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `LocExtCat` back into an extension homomorphism. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := LocExtCat Λ k) f

/-- Typecheck an extension homomorphism as a morphism in `LocExtCat`. -/
abbrev ofHom (f : X.Hom Y) : of Λ k X ⟶ of Λ k Y := ConcreteCategory.ofHom (C := LocExtCat Λ k) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : LocExtCat Λ k) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-- The underlying algebra homomorphism of a morphism in `LocExtCat`. -/
abbrev Hom.toAlgHom (f : A ⟶ B) : A.Ring →ₐ[Λ] B.Ring := f.hom.toAlgHom

@[simp]
lemma Hom.residue_comp (f : A ⟶ B) : B.residue.comp f.toAlgHom = A.residue := by
  ext x
  exact f.hom.algebraMap_toRingHom x

lemma Hom.comap_maximalIdeal_eq (f : A ⟶ B) :
    (maximalIdeal B).comap f.toAlgHom = maximalIdeal A := by
  rw [← ker_residue, RingHom.ker, Ideal.comap_comapₐ, residue_comp, ← RingHom.ker, ker_residue]

lemma Hom.isLocalHom_toAlgHom (f : A ⟶ B) : IsLocalHom f.toAlgHom := by
  have := (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 4).mpr (by
    rw [Ideal.comap_coe, f.comap_maximalIdeal_eq]))
  exact ⟨this.map_nonunit⟩

lemma Hom.map_maximalIdeal_le (f : A ⟶ B) :
    (maximalIdeal A).map f.toAlgHom ≤ maximalIdeal B := by
  have := (local_hom_TFAE f.toAlgHom.toRingHom).out 4 2
  rw [AlgHom.toRingHom_eq_coe, Ideal.comap_coe, Ideal.map_coe] at this
  rw [← this, f.comap_maximalIdeal_eq]

/-- The relative algebra structure on `B` canonically induced by a morphism `f : A ⟶ B`. -/
abbrev Hom.relativeAlgebra (f : A ⟶ B) : Algebra A B :=
  fast_instance% f.hom.toRingHom.toAlgebra

lemma Hom.isScalarTower_relativeAlgebra (f : A ⟶ B) :
    @IsScalarTower Λ A B _ f.relativeAlgebra.toSMul _ := .of_algHom f.toAlgHom

lemma Hom.isScalarTower'_relativeAlgebra (f : A ⟶ B) :
    @IsScalarTower A B k f.relativeAlgebra.toSMul _ _ :=
  letI := f.relativeAlgebra
  .of_algebraMap_eq (fun a ↦ (DFunLike.congr_fun f.residue_comp a).symm)

@[simp]
lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp]
lemma ofHom_comp (f : X.Hom Y) (g : Y.Hom Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g:= rfl

@[simp]
lemma ofHom_id : ofHom (Extension.Hom.id X) = 𝟙 (of Λ k X) := rfl

@[ext]
lemma hom_ext {f g : A ⟶ B} (h : f.hom = g.hom) : f = g := Hom.ext h

lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[simp]
lemma toAlghom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp]
lemma toAlgHom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  rfl

@[ext]
lemma toAlgHom_ext {f g : A ⟶ B} (h : f.toAlgHom = g.toAlgHom) : f = g := by
  ext x
  exact DFunLike.congr_fun h x

lemma ofHom_toAlgHom_apply (f : X.Hom Y) (x : X.Ring) : (ofHom f).toAlgHom x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

instance : Unique (A ⟶ (of Λ k (Extension.self Λ k))) where
  default := ofHom default
  uniq f := by rw [← ofHom_hom f, Unique.eq_default (Hom.hom f)]

variable (Λ k) in
/-- The terminal object in `LocExtCat` is the trivial extension of `k`. -/
def isTerminalOfSelf : Limits.IsTerminal (of Λ k (Extension.self Λ k)) := .ofUnique _

/-- Build an isomorphism in the category `LocExtCat` from a bijective extension homomorphism
between the underlying extensions. -/
@[simps]
def isoMk {X Y : Extension.{u} Λ k} {_ : IsLocalRing X.Ring} {_ : IsLocalRing Y.Ring}
    (e : X.Hom Y) (he : Bijective e.toAlgHom) : of Λ k X ≅ of Λ k Y where
  hom := ofHom e
  inv := ofHom <| .ofAlgHom (AlgEquiv.ofBijective e.toAlgHom he).symm (AlgHom.ext fun r ↦ by
    obtain ⟨r, rfl⟩ := he.surjective r
    nth_rw 1 [AlgHom.comp_apply, AlgEquiv.coe_algHom, ← AlgEquiv.coe_ofBijective e.toAlgHom he,
      AlgEquiv.symm_apply_apply]
    simp)
  inv_hom_id := by
    ext r
    suffices e.toAlgHom ((AlgEquiv.ofBijective e.toAlgHom he).symm r) = r by simpa
    rw [← AlgEquiv.coe_ofBijective e.toAlgHom he, AlgEquiv.apply_symm_apply]
  hom_inv_id := by
    ext r
    suffices (AlgEquiv.ofBijective e.toAlgHom he).symm (e.toAlgHom r) = r by simpa
    rw [← AlgEquiv.coe_ofBijective e.toAlgHom he, AlgEquiv.symm_apply_apply]

/-- Build an `AlgEquiv` from an isomorphism in the category `LocAlgCat Λ k`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[Λ] B where
  __ := i.hom.toAlgHom
  toFun := i.hom.toAlgHom
  invFun := i.inv.toAlgHom
  left_inv _ := inv_hom_apply ..
  right_inv _ := hom_inv_apply ..

@[simp]
lemma residue_comp_coe_ofIso (i : A ≅ B) : B.residue.comp (ofIso i) = A.residue :=
  i.hom.residue_comp

@[simp]
lemma residue_comp_coe_ifIso_symm (i : A ≅ B) : A.residue.comp (ofIso i).symm = B.residue :=
  i.inv.residue_comp

end LocExtCat
