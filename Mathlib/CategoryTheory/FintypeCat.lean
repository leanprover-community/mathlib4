/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Card

#align_import category_theory.Fintype from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# The category of finite types.

We define the category of finite types, denoted `FintypeCat` as
(bundled) types with a `Fintype` instance.

We also define `FintypeCat.Skeleton`, the standard skeleton of `FintypeCat` whose objects
are `Fin n` for `n : ℕ`. We prove that the obvious inclusion functor
`FintypeCat.Skeleton ⥤ FintypeCat` is an equivalence of categories in
`FintypeCat.Skeleton.equivalence`.
We prove that `FintypeCat.Skeleton` is a skeleton of `FintypeCat` in `FintypeCat.isSkeleton`.
-/


open scoped Classical

open CategoryTheory

/-- The category of finite types. -/
def FintypeCat :=
  Bundled Fintype
set_option linter.uppercaseLean3 false in
#align Fintype FintypeCat

namespace FintypeCat

instance : CoeSort FintypeCat Type* :=
  Bundled.coeSort

/-- Construct a bundled `FintypeCat` from the underlying type and typeclass. -/
def of (X : Type*) [Fintype X] : FintypeCat :=
  Bundled.of X
set_option linter.uppercaseLean3 false in
#align Fintype.of FintypeCat.of

instance : Inhabited FintypeCat :=
  ⟨of PEmpty⟩

instance {X : FintypeCat} : Fintype X :=
  X.2

instance : Category FintypeCat :=
  InducedCategory.category Bundled.α

/-- The fully faithful embedding of `FintypeCat` into the category of types. -/
@[simps!]
def incl : FintypeCat ⥤ Type* :=
  inducedFunctor _
set_option linter.uppercaseLean3 false in
#align Fintype.incl FintypeCat.incl

instance : incl.Full := InducedCategory.full _
instance : incl.Faithful := InducedCategory.faithful _

instance concreteCategoryFintype : ConcreteCategory FintypeCat :=
  ⟨incl⟩
set_option linter.uppercaseLean3 false in
#align Fintype.concrete_category_Fintype FintypeCat.concreteCategoryFintype

/- Help typeclass inference infer fullness of forgetful functor. -/
instance : (forget FintypeCat).Full := inferInstanceAs <| FintypeCat.incl.Full

@[simp]
theorem id_apply (X : FintypeCat) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Fintype.id_apply FintypeCat.id_apply

@[simp]
theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Fintype.comp_apply FintypeCat.comp_apply

@[simp]
lemma hom_inv_id_apply {X Y : FintypeCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : FintypeCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  congr_fun f.inv_hom_id y

-- Porting note (#10688): added to ease automation
@[ext]
lemma hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  funext
  apply h

-- See `equivEquivIso` in the root namespace for the analogue in `Type`.
/-- Equivalences between finite types are the same as isomorphisms in `FintypeCat`. -/
@[simps]
def equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B) where
  toFun e :=
    { hom := e
      inv := e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := congr_fun i.hom_inv_id
      right_inv := congr_fun i.inv_hom_id }
  left_inv := by aesop_cat
  right_inv := by aesop_cat
set_option linter.uppercaseLean3 false in
#align Fintype.equiv_equiv_iso FintypeCat.equivEquivIso

universe u

/--
The "standard" skeleton for `FintypeCat`. This is the full subcategory of `FintypeCat`
spanned by objects of the form `ULift (Fin n)` for `n : ℕ`. We parameterize the objects
of `Fintype.Skeleton` directly as `ULift ℕ`, as the type `ULift (Fin m) ≃ ULift (Fin n)`
is nonempty if and only if `n = m`. Specifying universes, `Skeleton : Type u` is a small
skeletal category equivalent to `Fintype.{u}`.
-/
def Skeleton : Type u :=
  ULift ℕ
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton FintypeCat.Skeleton

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `Fintype.Skeleton`. -/
def mk : ℕ → Skeleton :=
  ULift.up
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.mk FintypeCat.Skeleton.mk

instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/-- Given any object of `Fintype.Skeleton`, this returns the associated natural number. -/
def len : Skeleton → ℕ :=
  ULift.down
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.len FintypeCat.Skeleton.len

@[ext]
theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
  ULift.ext _ _
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.ext FintypeCat.Skeleton.ext

instance : SmallCategory Skeleton.{u} where
  Hom X Y := ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f

theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
  ext _ _ <|
    Fin.equiv_iff_eq.mp <|
      Nonempty.intro <|
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simp
            rfl
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simp
            rfl }
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.is_skeletal FintypeCat.Skeleton.is_skeletal

/-- The canonical fully faithful embedding of `Fintype.Skeleton` into `FintypeCat`. -/
def incl : Skeleton.{u} ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of (ULift (Fin X.len))
  map f := f
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.incl FintypeCat.Skeleton.incl

instance : incl.Full where map_surjective f := ⟨f, rfl⟩

instance : incl.Faithful where

instance : incl.EssSurj :=
  Functor.EssSurj.mk fun X =>
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := F.symm ∘ ULift.down
          inv := ULift.up ∘ F }⟩

noncomputable instance : incl.IsEquivalence where

/-- The equivalence between `Fintype.Skeleton` and `Fintype`. -/
noncomputable def equivalence : Skeleton ≌ FintypeCat :=
  incl.asEquivalence
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.equivalence FintypeCat.Skeleton.equivalence

@[simp]
theorem incl_mk_nat_card (n : ℕ) : Fintype.card (incl.obj (mk n)) = n := by
  convert Finset.card_fin n
  apply Fintype.ofEquiv_card
set_option linter.uppercaseLean3 false in
#align Fintype.skeleton.incl_mk_nat_card FintypeCat.Skeleton.incl_mk_nat_card

end Skeleton

/-- `Fintype.Skeleton` is a skeleton of `Fintype`. -/
lemma isSkeleton : IsSkeletonOf FintypeCat Skeleton Skeleton.incl where
  skel := Skeleton.is_skeletal
  eqv := by infer_instance
set_option linter.uppercaseLean3 false in
#align Fintype.is_skeleton FintypeCat.isSkeleton


end FintypeCat
