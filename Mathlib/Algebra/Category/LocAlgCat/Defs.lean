/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Group.Units.ULift
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The Category of Local Algebras with a Fixed Residue Field

This file defines the category of local algebras over a base commutative ring `Λ`
with a fixed residue field `k`. This category serves as the ambient environment
for formal deformation theory.

## Main Definitions

* `LocAlgCat Λ k` : The type of objects in the category of local `Λ`-algebras with
  residue field `k`. An object consists of a local `Λ`-algebra `A` equipped with
  a surjective residue map to `k`.

* `LocAlgCat.Hom` : The type of morphisms between objects in `LocAlgCat Λ k`.
  A morphism `f : A ⟶ B` is a local `Λ`-algebra homomorphism compatible with the
  residue maps.

* `LocAlgCat.isoMk`, `LocAlgCat.ofIso` : Canonical translations between algebra
  equivalences and categorical isomorphisms.

* `LocAlgCat.uliftFunctor` : The universe lift functor for `LocAlgCat`.

-/

universe w w' v u

@[expose] public section

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ]
variable {k : Type v} [Field k] [Algebra Λ k]

/-- The category of local `Λ`-algebras with residue field `k` and their morphisms. An object of
`LocAlgCat` consists of a local `Λ`-algebra `A` equipped with a surjective map to `k`. -/
structure LocAlgCat (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] : Type _ where
  /-- The object in `LocAlgCat` associated to a type equipped with the appropriate typeclasses. -/
  of (Λ k) ::
  /-- The underlying type of the local `Λ`-algebras. -/
  carrier : Type w
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [baseAlgebra : Algebra Λ carrier]
  [residueAlgebra : Algebra carrier k]
  [scalarTower : IsScalarTower Λ carrier k]
  isSurjective : Surjective (algebraMap carrier k)

namespace LocAlgCat

variable {A B C : LocAlgCat.{w} Λ k} {X Y Z : Type w}
variable [CommRing X] [IsLocalRing X] [Algebra Λ X] [Algebra X k] [IsScalarTower Λ X k]
variable [CommRing Y] [IsLocalRing Y] [Algebra Λ Y] [Algebra Y k] [IsScalarTower Λ Y k]
variable [CommRing Z] [IsLocalRing Z] [Algebra Λ Z] [Algebra Z k] [IsScalarTower Λ Z k]
variable {hX : Surjective (algebraMap X k)} {hY : Surjective (algebraMap Y k)}
  {hZ : Surjective (algebraMap Z k)}

attribute [instance] localRing commRing baseAlgebra scalarTower residueAlgebra

initialize_simps_projections LocAlgCat (-localRing, -commRing, -baseAlgebra, -residueAlgebra,
-scalarTower)

instance : CoeSort (LocAlgCat Λ k) (Type w) := ⟨carrier⟩

attribute [coe] carrier

variable (X) in
lemma coe_of : (of Λ k X hX : Type w) = X := rfl

/-- The canonical residue map from an object `A` to `k`.
This is a prefered way to apply residue maps in `LocAlgCat`. -/
def residue (A : LocAlgCat Λ k) : A →ₐ[Λ] k :=
  IsScalarTower.toAlgHom Λ A k

lemma residue_toRingHom : A.residue = algebraMap A k := rfl

lemma residue_apply {a : A} : A.residue a = algebraMap A k a := rfl

lemma ker_residue : RingHom.ker (residue A) = maximalIdeal A :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ A.isSurjective)

lemma residue_surjective : Surjective (residue A) := A.isSurjective

lemma residue_eq_zero_iff {x : A} : residue A x = 0 ↔ x ∈ maximalIdeal A := by
  rw [← RingHom.mem_ker, ker_residue]

@[simp]
lemma residue_of_apply {x : (of Λ k X hX)} : (of Λ k X hX).residue x = algebraMap X k x := rfl

/-- The canonical equivalence between the residue field of an object and `k`. -/
noncomputable def residueEquiv (A : LocAlgCat Λ k) : ResidueField A ≃ₐ[Λ] k where
  __ := (Ideal.quotEquivOfEq (ker_residue (A := A)).symm).trans
    (RingHom.quotientKerEquivOfSurjective A.residue_surjective)
  commutes' r := (IsScalarTower.algebraMap_apply Λ A k r).symm

@[simp]
lemma residueEquiv_residue_apply {x : A} :
    A.residueEquiv (IsLocalRing.residue A x) = A.residue x := rfl

/-- The type of morphisms in `LocAlgCat`. A morphism consists of a local algebra map
compatible with the residue maps. -/
@[ext]
structure Hom (A B : LocAlgCat.{w} Λ k) : Type w where
  /-- The underlying algebra map. -/
  toAlgHom : A →ₐ[Λ] B
  -- We do not use `IsLocalHom` in order to avoid introducing `IsLocalHom` instances for `AlgHom`.
  comap_maximalIdeal_eq : (maximalIdeal B).comap toAlgHom = maximalIdeal A
  residue_comp : B.residue.comp toAlgHom = A.residue

instance : Category (LocAlgCat.{w} Λ k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id Λ A, by simp, by simp⟩
  comp {A B C} f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [← Ideal.comap_comapₐ, g.comap_maximalIdeal_eq, f.comap_maximalIdeal_eq], by
    rw [← AlgHom.comp_assoc, g.residue_comp, f.residue_comp]⟩

lemma Hom.isLocalHom_toAlgHom (f : A ⟶ B) : IsLocalHom f.toAlgHom := by
  have := (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 4).mpr (by
    rw [Ideal.comap_coe, f.comap_maximalIdeal_eq]))
  exact ⟨this.map_nonunit⟩

lemma Hom.map_maximalIdeal_le (f : A ⟶ B) :
    (maximalIdeal A).map f.toAlgHom ≤ maximalIdeal B := by
  have := (local_hom_TFAE f.toAlgHom.toRingHom).out 4 2
  rw [AlgHom.toRingHom_eq_coe, Ideal.comap_coe, Ideal.map_coe] at this
  rw [← this]; exact f.comap_maximalIdeal_eq

/-- Typecheck an `AlgHom` compatible with residue maps as a morphism in `LocAlgCat`. -/
abbrev ofHom (f : X →ₐ[Λ] Y) (h : (maximalIdeal Y).comap f = maximalIdeal X)
    (h' : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) : of Λ k X hX ⟶ of Λ k Y hY :=
  ⟨f, h, h'⟩

@[simp]
lemma ofhom_toAlgHom (f : A ⟶ B) : ofHom f.toAlgHom f.comap_maximalIdeal_eq f.residue_comp = f :=
  rfl

@[simp]
lemma toAlgHom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp]
lemma toAlgHom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  rfl

@[simp]
lemma ofHom_id : ofHom (.id Λ X) (by simp) (by simp) = 𝟙 (of Λ k X hX) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐ[Λ] Y) (hf : (maximalIdeal Y).comap f = maximalIdeal X)
    (hf' : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) (g : Y →ₐ[Λ] Z)
    (hg : (maximalIdeal Z).comap g = maximalIdeal Y)
    (hg' : (of Λ k Z hZ).residue.comp g = (of Λ k Y hY).residue) : ofHom (g.comp f)
      (by rw [← Ideal.comap_comapₐ, hg, hf] ) (by rw [← AlgHom.comp_assoc, hg', hf']) =
        ofHom f hf hf' ≫ ofHom g hg hg' := rfl

lemma ofHom_toAlgHom_apply (f : X →ₐ[Λ] Y) (h : (maximalIdeal Y).comap f = maximalIdeal X)
    (h' : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) (x : X) :
    (ofHom f h h').toAlgHom x = f x := rfl

@[simp]
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.toAlgHom (e.hom.toAlgHom x) = x := by
  simp [← AlgHom.comp_apply, ← toAlgHom_comp]

@[simp]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.toAlgHom (e.inv.toAlgHom x) = x := by
  simp [← AlgHom.comp_apply, ← toAlgHom_comp]

/-- Build an isomorphism in the category `LocAlgCat` from an `AlgEquiv` between `Λ`-algebras. -/
@[simps]
def isoMk {X Y : Type w} {_ : CommRing X} {_ : IsLocalRing X} {_ : Algebra Λ X} {_ : CommRing Y}
    {_ : IsLocalRing Y} {_ : Algebra Λ Y} {_ : Algebra X k} {_ : Algebra Y k}
    {_ : IsScalarTower Λ X k} {_ : IsScalarTower Λ Y k} {hX : Surjective (algebraMap X k)}
    {hY : Surjective (algebraMap Y k)} (e : X ≃ₐ[Λ] Y) (he : (of Λ k Y hY).residue.comp e =
      (of Λ k X hX).residue) : of Λ k X hX ≅ of Λ k Y hY where
  hom := ofHom (e : X →ₐ[Λ] Y) (by ext; simp) (by rw [← he])
  inv := ofHom (e.symm : Y →ₐ[Λ] X) (by ext; simp) (by ext; simp [← he])
  inv_hom_id := by simp [← ofHom_comp]
  hom_inv_id := by simp [← ofHom_comp]

/-- Build an `AlgEquiv` from an isomorphism in the category `LocAlgCat Λ k`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[Λ] B where
  __ := i.hom.toAlgHom
  toFun := i.hom.toAlgHom
  invFun := i.inv.toAlgHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]
lemma residue_comp_coe_ofIso (i : A ≅ B) : B.residue.comp (ofIso i) = A.residue :=
  i.hom.residue_comp

/-- Algebra equivalences compatible with residue maps are the same as
isomorphisms in `LocAlgCat`. -/
@[simps]
def isoEquivSubtypeAlgEquiv : (of Λ k X hX ≅ of Λ k Y hY) ≃
    { e : X ≃ₐ[Λ] Y // (of Λ k Y hY).residue.comp e = (of Λ k X hX).residue } where
  toFun i := ⟨ofIso i, residue_comp_coe_ofIso i⟩
  invFun f := isoMk f.val f.prop

instance uliftResidueAlgebra : Algebra (ULift.{w'} A) k := ULift.algebra' ..

instance isScalarTower_uliftResidueAlgebra : IsScalarTower Λ (ULift.{w'} A) k :=
  ULift.isScalarTower' ..

variable (Λ k) in
/-- Universe lift functor for `LocAlgCat`. -/
def uliftFunctor : LocAlgCat.{w} Λ k ⥤ LocAlgCat.{max w w'} Λ k where
  obj A := of Λ k (ULift.{w'} A) (fun r ↦ by simpa using A.isSurjective r)
  map {A B} f :=
    ofHom (ULift.algEquiv.symm.toAlgHom.comp <| f.toAlgHom.comp ULift.algEquiv.toAlgHom) (by
      have := f.isLocalHom_toAlgHom
      ext; simp) (by ext x; simpa using DFunLike.congr_fun f.residue_comp x.down)

variable (Λ k) in
/-- The universe lift functor for `LocAlgCat` is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor Λ k).FullyFaithful where
  preimage {A B} f :=
    letI F : ULift A →ₐ[Λ] ULift B := f.toAlgHom
    ofHom (ULift.algEquiv.toAlgHom.comp <| F.comp ULift.algEquiv.symm.toAlgHom) (by
      have : IsLocalHom F := f.isLocalHom_toAlgHom
      ext; simp) (AlgHom.ext fun x ↦ by
        have := DFunLike.congr_fun f.residue_comp
        simp only [uliftFunctor, AlgEquiv.toAlgHom_eq_coe, coe_of, ULift.forall] at this
        exact this x)

instance : (uliftFunctor Λ k).Full := (fullyFaithfulUliftFunctor Λ k).full

instance : (uliftFunctor Λ k).Faithful := (fullyFaithfulUliftFunctor Λ k).faithful

end LocAlgCat
