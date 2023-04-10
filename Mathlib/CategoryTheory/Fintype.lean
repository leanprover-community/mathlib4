/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz

! This file was ported from Lean 3 source module category_theory.Fintype
! leanprover-community/mathlib commit c3019c79074b0619edb4b27553a91b2e82242395
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Skeletal
import Mathbin.CategoryTheory.Elementwise
import Mathbin.Data.Fintype.Card

/-!
# The category of finite types.

We define the category of finite types, denoted `Fintype` as
(bundled) types with a `fintype` instance.

We also define `Fintype.skeleton`, the standard skeleton of `Fintype` whose objects are `fin n`
for `n : ℕ`. We prove that the obvious inclusion functor `Fintype.skeleton ⥤ Fintype` is an
equivalence of categories in `Fintype.skeleton.equivalence`.
We prove that `Fintype.skeleton` is a skeleton of `Fintype` in `Fintype.is_skeleton`.
-/


open Classical

open CategoryTheory

/-- The category of finite types. -/
def FintypeCat :=
  Bundled Fintype
#align Fintype FintypeCat

namespace FintypeCat

instance : CoeSort FintypeCat (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled `Fintype` from the underlying type and typeclass. -/
def of (X : Type _) [Fintype X] : FintypeCat :=
  Bundled.of X
#align Fintype.of FintypeCat.of

instance : Inhabited FintypeCat :=
  ⟨⟨PEmpty⟩⟩

instance {X : FintypeCat} : Fintype X :=
  X.2

instance : Category FintypeCat :=
  InducedCategory.category Bundled.α

/-- The fully faithful embedding of `Fintype` into the category of types. -/
@[simps]
def incl : FintypeCat ⥤ Type _ :=
  inducedFunctor _ deriving Full, Faithful
#align Fintype.incl FintypeCat.incl

instance concreteCategoryFintype : ConcreteCategory FintypeCat :=
  ⟨incl⟩
#align Fintype.concrete_category_Fintype FintypeCat.concreteCategoryFintype

@[simp]
theorem id_apply (X : FintypeCat) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
#align Fintype.id_apply FintypeCat.id_apply

@[simp]
theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl
#align Fintype.comp_apply FintypeCat.comp_apply

-- See `equiv_equiv_iso` in the root namespace for the analogue in `Type`.
/-- Equivalences between finite types are the same as isomorphisms in `Fintype`. -/
@[simps]
def equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B)
    where
  toFun e :=
    { Hom := e
      inv := e.symm }
  invFun i :=
    { toFun := i.Hom
      invFun := i.inv
      left_inv := Iso.hom_inv_id_apply i
      right_inv := Iso.inv_hom_id_apply i }
  left_inv := by tidy
  right_inv := by tidy
#align Fintype.equiv_equiv_iso FintypeCat.equivEquivIso

universe u

/--
The "standard" skeleton for `Fintype`. This is the full subcategory of `Fintype` spanned by objects
of the form `ulift (fin n)` for `n : ℕ`. We parameterize the objects of `Fintype.skeleton`
directly as `ulift ℕ`, as the type `ulift (fin m) ≃ ulift (fin n)` is
nonempty if and only if `n = m`. Specifying universes, `skeleton : Type u` is a small
skeletal category equivalent to `Fintype.{u}`.
-/
def Skeleton : Type u :=
  ULift ℕ
#align Fintype.skeleton FintypeCat.Skeleton

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `Fintype.skeleton`. -/
def mk : ℕ → Skeleton :=
  ULift.up
#align Fintype.skeleton.mk FintypeCat.Skeleton.mk

instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/-- Given any object of `Fintype.skeleton`, this returns the associated natural number. -/
def len : Skeleton → ℕ :=
  ULift.down
#align Fintype.skeleton.len FintypeCat.Skeleton.len

@[ext]
theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
  ULift.ext _ _
#align Fintype.skeleton.ext FintypeCat.Skeleton.ext

instance : SmallCategory Skeleton.{u}
    where
  Hom X Y := ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)
  id _ := id
  comp _ _ _ f g := g ∘ f

theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
  ext _ _ <|
    Fin.equiv_iff_eq.mp <|
      Nonempty.intro <|
        { toFun := fun x => (h.Hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simpa
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simpa }
#align Fintype.skeleton.is_skeletal FintypeCat.Skeleton.is_skeletal

/-- The canonical fully faithful embedding of `Fintype.skeleton` into `Fintype`. -/
def incl : Skeleton.{u} ⥤ FintypeCat.{u}
    where
  obj X := FintypeCat.of (ULift (Fin X.len))
  map _ _ f := f
#align Fintype.skeleton.incl FintypeCat.Skeleton.incl

instance : Full incl where preimage _ _ f := f

instance : Faithful incl where

instance : EssSurj incl :=
  EssSurj.mk fun X =>
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { Hom := F.symm ∘ ULift.down
          inv := ULift.up ∘ F }⟩

noncomputable instance : IsEquivalence incl :=
  Equivalence.ofFullyFaithfullyEssSurj _

/-- The equivalence between `Fintype.skeleton` and `Fintype`. -/
noncomputable def equivalence : Skeleton ≌ FintypeCat :=
  incl.asEquivalence
#align Fintype.skeleton.equivalence FintypeCat.Skeleton.equivalence

@[simp]
theorem incl_mk_nat_card (n : ℕ) : Fintype.card (incl.obj (mk n)) = n :=
  by
  convert Finset.card_fin n
  apply Fintype.ofEquiv_card
#align Fintype.skeleton.incl_mk_nat_card FintypeCat.Skeleton.incl_mk_nat_card

end Skeleton

/-- `Fintype.skeleton` is a skeleton of `Fintype`. -/
noncomputable def isSkeleton : IsSkeletonOf FintypeCat Skeleton Skeleton.incl
    where
  skel := Skeleton.is_skeletal
  eqv := by infer_instance
#align Fintype.is_skeleton FintypeCat.isSkeleton

end FintypeCat

