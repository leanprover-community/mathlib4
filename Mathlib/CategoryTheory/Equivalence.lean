/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.Tactic.CategoryTheory.Slice

#align_import category_theory.equivalence from "leanprover-community/mathlib"@"9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef"
/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphism of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `Equivalence`: bundled (half-)adjoint equivalences of categories
* `IsEquivalence`: type class on a functor `F` containing the data of the inverse `G` as well as
  the natural isomorphisms `η` and `ε`.
* `EssSurj`: type class on a functor `F` containing the data of the preimages and the isomorphisms
  `F.obj (preimage d) ≅ d`.

## Main results

* `Equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `IsEquivalence.equivOfIso`: when `F` and `G` are isomorphic functors, `F` is an equivalence
iff `G` is.
* `Equivalence.ofFullyFaithfullyEssSurj`: a fully faithful essentially surjective functor is an
  equivalence.

## Notations

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- We define an equivalence as a (half)-adjoint equivalence, a pair of functors with
  a unit and counit which are natural isomorphisms and the triangle law `Fη ≫ εF = 1`, or in other
  words the composite `F ⟶ FGF ⟶ F` is the identity.

  In `unit_inverse_comp`, we show that this is actually an adjoint equivalence, i.e., that the
  composite `G ⟶ GFG ⟶ G` is also the identity.

  The triangle equation is written as a family of equalities between morphisms, it is more
  complicated if we write it as an equality of natural transformations, because then we would have
  to insert natural transformations like `F ⟶ F1`.

See <https://stacks.math.columbia.edu/tag/001J>
-/
structure Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where mk' ::
  /-- A functor in one direction -/
  functor : C ⥤ D
  /-- A functor in the other direction -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is isomorphic to the identity -/
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is also isomorphic to the identity -/
  counitIso : inverse ⋙ functor ≅ 𝟭 D
  /-- The natural isomorphisms compose to the identity. -/
  functor_unitIso_comp :
    ∀ X : C, functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functor.obj X) =
      𝟙 (functor.obj X) := by aesop_cat
#align category_theory.equivalence CategoryTheory.Equivalence
#align category_theory.equivalence.unit_iso CategoryTheory.Equivalence.unitIso
#align category_theory.equivalence.counit_iso CategoryTheory.Equivalence.counitIso
#align category_theory.equivalence.functor_unit_iso_comp CategoryTheory.Equivalence.functor_unitIso_comp

/-- We infix the usual notation for an equivalence -/
infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

attribute [pp_dot] functor inverse unitIso counitIso

/-- The unit of an equivalence of categories. -/
@[pp_dot] abbrev unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse :=
  e.unitIso.hom
#align category_theory.equivalence.unit CategoryTheory.Equivalence.unit

/-- The counit of an equivalence of categories. -/
@[pp_dot] abbrev counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D :=
  e.counitIso.hom
#align category_theory.equivalence.counit CategoryTheory.Equivalence.counit

/-- The inverse of the unit of an equivalence of categories. -/
@[pp_dot] abbrev unitInv (e : C ≌ D) : e.functor ⋙ e.inverse ⟶ 𝟭 C :=
  e.unitIso.inv
#align category_theory.equivalence.unit_inv CategoryTheory.Equivalence.unitInv

/-- The inverse of the counit of an equivalence of categories. -/
@[pp_dot] abbrev counitInv (e : C ≌ D) : 𝟭 D ⟶ e.inverse ⋙ e.functor :=
  e.counitIso.inv
#align category_theory.equivalence.counit_inv CategoryTheory.Equivalence.counitInv

/- While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/
@[simp]
theorem Equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom :=
  rfl
#align category_theory.equivalence.equivalence_mk'_unit CategoryTheory.Equivalence.Equivalence_mk'_unit

@[simp]
theorem Equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom :=
  rfl
#align category_theory.equivalence.equivalence_mk'_counit CategoryTheory.Equivalence.Equivalence_mk'_counit

@[simp]
theorem Equivalence_mk'_unitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unitInv = unit_iso.inv :=
  rfl
#align category_theory.equivalence.equivalence_mk'_unit_inv CategoryTheory.Equivalence.Equivalence_mk'_unitInv

@[simp]
theorem Equivalence_mk'_counitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counitInv = counit_iso.inv :=
  rfl
#align category_theory.equivalence.equivalence_mk'_counit_inv CategoryTheory.Equivalence.Equivalence_mk'_counitInv

@[simp]
theorem functor_unit_comp (e : C ≌ D) (X : C) :
    e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
  e.functor_unitIso_comp X
#align category_theory.equivalence.functor_unit_comp CategoryTheory.Equivalence.functor_unit_comp

@[simp]
theorem counitInv_functor_comp (e : C ≌ D) (X : C) :
    e.counitInv.app (e.functor.obj X) ≫ e.functor.map (e.unitInv.app X) = 𝟙 (e.functor.obj X) := by
  erw [Iso.inv_eq_inv (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X))
      (Iso.refl _)]
  exact e.functor_unit_comp X
#align category_theory.equivalence.counit_inv_functor_comp CategoryTheory.Equivalence.counitInv_functor_comp

theorem counitInv_app_functor (e : C ≌ D) (X : C) :
    e.counitInv.app (e.functor.obj X) = e.functor.map (e.unit.app X) := by
  symm
  erw [← Iso.comp_hom_eq_id (e.counitIso.app _), functor_unit_comp]
  rfl
#align category_theory.equivalence.counit_inv_app_functor CategoryTheory.Equivalence.counitInv_app_functor

theorem counit_app_functor (e : C ≌ D) (X : C) :
    e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X) := by
  erw [← Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)), functor_unit_comp]
  rfl
#align category_theory.equivalence.counit_app_functor CategoryTheory.Equivalence.counit_app_functor

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[simp]
theorem unit_inverse_comp (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) := by
  rw [← id_comp (e.inverse.map _), ← map_id e.inverse, ← counitInv_functor_comp, map_comp]
  dsimp
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _)), app_hom, app_inv]
  slice_lhs 2 3 => erw [e.unit.naturality]
  slice_lhs 1 2 => erw [e.unit.naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    erw [← map_comp e.inverse, e.counit.naturality]
    erw [(e.counitIso.app _).hom_inv_id, map_id]
  erw [id_comp]
  slice_lhs 2 3 => erw [← map_comp e.inverse, e.counitIso.inv.naturality, map_comp]
  slice_lhs 3 4 => erw [e.unitInv.naturality]
  slice_lhs 4 5 => erw [← map_comp (e.functor ⋙ e.inverse), (e.unitIso.app _).hom_inv_id, map_id]
  erw [id_comp]
  slice_lhs 3 4 => erw [← e.unitInv.naturality]
  slice_lhs 2 3 =>
    erw [← map_comp e.inverse, ← e.counitIso.inv.naturality, (e.counitIso.app _).hom_inv_id,
      map_id]
  erw [id_comp, (e.unitIso.app _).hom_inv_id]; rfl
#align category_theory.equivalence.unit_inverse_comp CategoryTheory.Equivalence.unit_inverse_comp

@[simp]
theorem inverse_counitInv_comp (e : C ≌ D) (Y : D) :
    e.inverse.map (e.counitInv.app Y) ≫ e.unitInv.app (e.inverse.obj Y) = 𝟙 (e.inverse.obj Y) := by
  erw [Iso.inv_eq_inv (e.unitIso.app (e.inverse.obj Y) ≪≫ e.inverse.mapIso (e.counitIso.app Y))
      (Iso.refl _)]
  exact e.unit_inverse_comp Y
#align category_theory.equivalence.inverse_counit_inv_comp CategoryTheory.Equivalence.inverse_counitInv_comp

theorem unit_app_inverse (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y) := by
  erw [← Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)), unit_inverse_comp]
  dsimp
#align category_theory.equivalence.unit_app_inverse CategoryTheory.Equivalence.unit_app_inverse

theorem unitInv_app_inverse (e : C ≌ D) (Y : D) :
    e.unitInv.app (e.inverse.obj Y) = e.inverse.map (e.counit.app Y) := by
  symm
  erw [← Iso.hom_comp_eq_id (e.unitIso.app _), unit_inverse_comp]
  rfl
#align category_theory.equivalence.unit_inv_app_inverse CategoryTheory.Equivalence.unitInv_app_inverse

@[simp]
theorem fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitInv.app Y :=
  (NatIso.naturality_2 e.counitIso f).symm
#align category_theory.equivalence.fun_inv_map CategoryTheory.Equivalence.fun_inv_map

@[simp]
theorem inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
    e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.app Y :=
  (NatIso.naturality_1 e.unitIso f).symm
#align category_theory.equivalence.inv_fun_map CategoryTheory.Equivalence.inv_fun_map

section

-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

/-- If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we can upgrade it
to a refined natural isomorphism `adjointifyη η : 𝟭 C ≅ F ⋙ G` which exhibits the properties
required for a half-adjoint equivalence. See `Equivalence.mk`. -/
def adjointifyη : 𝟭 C ≅ F ⋙ G := by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)
#align category_theory.equivalence.adjointify_η CategoryTheory.Equivalence.adjointifyη

theorem adjointify_η_ε (X : C) :
    F.map ((adjointifyη η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  dsimp [adjointifyη,Trans.trans]
  simp
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]
#align category_theory.equivalence.adjointify_η_ε CategoryTheory.Equivalence.adjointify_η_ε

end

/-- Every equivalence of categories consisting of functors `F` and `G` such that `F ⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed into a half-adjoint
    equivalence without changing `F` or `G`. -/
protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩
#align category_theory.equivalence.mk CategoryTheory.Equivalence.mk

/-- Equivalence of categories is reflexive. -/
@[refl, simps]
def refl : C ≌ C :=
  ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩
#align category_theory.equivalence.refl CategoryTheory.Equivalence.refl

instance : Inhabited (C ≌ C) :=
  ⟨refl⟩

/-- Equivalence of categories is symmetric. -/
@[symm, simps, pp_dot]
def symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩
#align category_theory.equivalence.symm CategoryTheory.Equivalence.symm

variable {E : Type u₃} [Category.{v₃} E]

/-- Equivalence of categories is transitive. -/
@[trans, simps, pp_dot]
def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E
    where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := by
    refine' Iso.trans e.unitIso _
    exact isoWhiskerLeft e.functor (isoWhiskerRight f.unitIso e.inverse)
  counitIso := by
    refine' Iso.trans _ f.counitIso
    exact isoWhiskerLeft f.inverse (isoWhiskerRight e.counitIso f.functor)
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    rw [← f.functor.map_comp_assoc, e.functor.map_comp, ← counitInv_app_functor, fun_inv_map,
      Iso.inv_hom_id_app_assoc, assoc, Iso.inv_hom_id_app, counit_app_functor, ← Functor.map_comp]
    erw [comp_id, Iso.hom_inv_id_app, Functor.map_id]
#align category_theory.equivalence.trans CategoryTheory.Equivalence.trans

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor
#align category_theory.equivalence.fun_inv_id_assoc CategoryTheory.Equivalence.funInvIdAssoc

@[simp]
theorem funInvIdAssoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).hom.app X = F.map (e.unitInv.app X) := by
  dsimp [funInvIdAssoc]
  aesop_cat
#align category_theory.equivalence.fun_inv_id_assoc_hom_app CategoryTheory.Equivalence.funInvIdAssoc_hom_app

@[simp]
theorem funInvIdAssoc_inv_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).inv.app X = F.map (e.unit.app X) := by
  dsimp [funInvIdAssoc]
  aesop_cat
#align category_theory.equivalence.fun_inv_id_assoc_inv_app CategoryTheory.Equivalence.funInvIdAssoc_inv_app

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor
#align category_theory.equivalence.inv_fun_id_assoc CategoryTheory.Equivalence.invFunIdAssoc

@[simp]
theorem invFunIdAssoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).hom.app X = F.map (e.counit.app X) := by
  dsimp [invFunIdAssoc]
  aesop_cat
#align category_theory.equivalence.inv_fun_id_assoc_hom_app CategoryTheory.Equivalence.invFunIdAssoc_hom_app

@[simp]
theorem invFunIdAssoc_inv_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).inv.app X = F.map (e.counitInv.app X) := by
  dsimp [invFunIdAssoc]
  aesop_cat
#align category_theory.equivalence.inv_fun_id_assoc_inv_app CategoryTheory.Equivalence.invFunIdAssoc_inv_app

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simps! functor inverse unitIso counitIso]
def congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E :=
  Equivalence.mk ((whiskeringLeft _ _ _).obj e.inverse) ((whiskeringLeft _ _ _).obj e.functor)
    (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
    (NatIso.ofComponents fun F => e.invFunIdAssoc F)
#align category_theory.equivalence.congr_left CategoryTheory.Equivalence.congrLeft

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simps! functor inverse unitIso counitIso]
def congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D :=
  Equivalence.mk ((whiskeringRight _ _ _).obj e.functor) ((whiskeringRight _ _ _).obj e.inverse)
    (NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _)
    (NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor)
#align category_theory.equivalence.congr_right CategoryTheory.Equivalence.congrRight

section CancellationLemmas

variable (e : C ≌ D)

/- We need special forms of `cancel_natIso_hom_right(_assoc)` and
`cancel_natIso_inv_right(_assoc)` for units and counits, because neither `simp` or `rw` will apply
those lemmas in this setting without providing `e.unitIso` (or similar) as an explicit argument.
We also provide the lemmas for length four compositions, since they're occasionally useful.
(e.g. in proving that equivalences take monos to monos) -/
@[simp]
theorem cancel_unit_right {X Y : C} (f f' : X ⟶ Y) :
    f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' := by simp only [cancel_mono]
#align category_theory.equivalence.cancel_unit_right CategoryTheory.Equivalence.cancel_unit_right

@[simp]
theorem cancel_unitInv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y)) :
    f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f' := by simp only [cancel_mono]
#align category_theory.equivalence.cancel_unit_inv_right CategoryTheory.Equivalence.cancel_unitInv_right

@[simp]
theorem cancel_counit_right {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y)) :
    f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' := by simp only [cancel_mono]
#align category_theory.equivalence.cancel_counit_right CategoryTheory.Equivalence.cancel_counit_right

@[simp]
theorem cancel_counitInv_right {X Y : D} (f f' : X ⟶ Y) :
    f ≫ e.counitInv.app Y = f' ≫ e.counitInv.app Y ↔ f = f' := by simp only [cancel_mono]
#align category_theory.equivalence.cancel_counit_inv_right CategoryTheory.Equivalence.cancel_counitInv_right

@[simp]
theorem cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]
#align category_theory.equivalence.cancel_unit_right_assoc CategoryTheory.Equivalence.cancel_unit_right_assoc

@[simp]
theorem cancel_counitInv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) : f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]
#align category_theory.equivalence.cancel_counit_inv_right_assoc CategoryTheory.Equivalence.cancel_counitInv_right_assoc

@[simp]
theorem cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [← Category.assoc, cancel_mono]
#align category_theory.equivalence.cancel_unit_right_assoc' CategoryTheory.Equivalence.cancel_unit_right_assoc'

@[simp]
theorem cancel_counitInv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.counitInv.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
  by simp only [← Category.assoc, cancel_mono]
#align category_theory.equivalence.cancel_counit_inv_right_assoc' CategoryTheory.Equivalence.cancel_counitInv_right_assoc'

end CancellationLemmas

section

-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.
/-- Natural number powers of an auto-equivalence.  Use `(^)` instead. -/
def powNat (e : C ≌ C) : ℕ → (C ≌ C)
  | 0 => Equivalence.refl
  | 1 => e
  | n + 2 => e.trans (powNat e (n + 1))
#align category_theory.equivalence.pow_nat CategoryTheory.Equivalence.powNat

/-- Powers of an auto-equivalence.  Use `(^)` instead. -/
def pow (e : C ≌ C) : ℤ → (C ≌ C)
  | Int.ofNat n => e.powNat n
  | Int.negSucc n => e.symm.powNat (n + 1)
#align category_theory.equivalence.pow CategoryTheory.Equivalence.pow

instance : Pow (C ≌ C) ℤ :=
  ⟨pow⟩

@[simp]
theorem pow_zero (e : C ≌ C) : e ^ (0 : ℤ) = Equivalence.refl :=
  rfl
#align category_theory.equivalence.pow_zero CategoryTheory.Equivalence.pow_zero

@[simp]
theorem pow_one (e : C ≌ C) : e ^ (1 : ℤ) = e :=
  rfl
#align category_theory.equivalence.pow_one CategoryTheory.Equivalence.pow_one

@[simp]
theorem pow_neg_one (e : C ≌ C) : e ^ (-1 : ℤ) = e.symm :=
  rfl
#align category_theory.equivalence.pow_neg_one CategoryTheory.Equivalence.pow_neg_one

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.
end

end Equivalence

/-- A functor that is part of a (half) adjoint equivalence -/
class IsEquivalence (F : C ⥤ D) where mk' ::
  /-- The inverse functor to `F` -/
  inverse : D ⥤ C
  /-- Composition `F ⋙ inverse` is isomorphic to the identity. -/
  unitIso : 𝟭 C ≅ F ⋙ inverse
  /-- Composition `inverse ⋙ F` is isomorphic to the identity. -/
  counitIso : inverse ⋙ F ≅ 𝟭 D
  /-- The natural isomorphisms are inverse. -/
  functor_unitIso_comp :
    ∀ X : C,
      F.map ((unitIso.hom : 𝟭 C ⟶ F ⋙ inverse).app X) ≫ counitIso.hom.app (F.obj X) =
        𝟙 (F.obj X) := by
    aesop_cat
#align category_theory.is_equivalence CategoryTheory.IsEquivalence
#align category_theory.is_equivalence.unit_iso CategoryTheory.IsEquivalence.unitIso
#align category_theory.is_equivalence.counit_iso CategoryTheory.IsEquivalence.counitIso
#align category_theory.is_equivalence.functor_unit_iso_comp CategoryTheory.IsEquivalence.functor_unitIso_comp

attribute [reassoc (attr := simp)] IsEquivalence.functor_unitIso_comp

namespace IsEquivalence

instance ofEquivalence (F : C ≌ D) : IsEquivalence F.functor :=
  { F with }
#align category_theory.is_equivalence.of_equivalence CategoryTheory.IsEquivalence.ofEquivalence

instance ofEquivalenceInverse (F : C ≌ D) : IsEquivalence F.inverse :=
  IsEquivalence.ofEquivalence F.symm
#align category_theory.is_equivalence.of_equivalence_inverse CategoryTheory.IsEquivalence.ofEquivalenceInverse

open Equivalence

/-- To see that a functor is an equivalence, it suffices to provide an inverse functor `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors. -/
protected def mk {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : IsEquivalence F :=
  ⟨G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩
#align category_theory.is_equivalence.mk CategoryTheory.IsEquivalence.mk

end IsEquivalence

namespace Functor

/-- Interpret a functor that is an equivalence as an equivalence. -/
def asEquivalence (F : C ⥤ D) [IsEquivalence F] : C ≌ D :=
  ⟨F, IsEquivalence.inverse F, IsEquivalence.unitIso, IsEquivalence.counitIso,
    IsEquivalence.functor_unitIso_comp⟩
#align category_theory.functor.as_equivalence CategoryTheory.Functor.asEquivalence

instance isEquivalenceRefl : IsEquivalence (𝟭 C) :=
  IsEquivalence.ofEquivalence Equivalence.refl
#align category_theory.functor.is_equivalence_refl CategoryTheory.Functor.isEquivalenceRefl

/-- The inverse functor of a functor that is an equivalence. -/
def inv (F : C ⥤ D) [IsEquivalence F] : D ⥤ C :=
  IsEquivalence.inverse F
#align category_theory.functor.inv CategoryTheory.Functor.inv

instance isEquivalenceInv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv :=
  IsEquivalence.ofEquivalence F.asEquivalence.symm
#align category_theory.functor.is_equivalence_inv CategoryTheory.Functor.isEquivalenceInv

@[simp]
theorem asEquivalence_functor (F : C ⥤ D) [IsEquivalence F] : F.asEquivalence.functor = F :=
  rfl
#align category_theory.functor.as_equivalence_functor CategoryTheory.Functor.asEquivalence_functor

@[simp]
theorem asEquivalence_inverse (F : C ⥤ D) [IsEquivalence F] : F.asEquivalence.inverse = inv F :=
  rfl
#align category_theory.functor.as_equivalence_inverse CategoryTheory.Functor.asEquivalence_inverse

@[simp]
theorem asEquivalence_unit {F : C ⥤ D} [IsEquivalence F] :
    F.asEquivalence.unitIso = IsEquivalence.unitIso :=
  rfl
#align category_theory.functor.as_equivalence_unit CategoryTheory.Functor.asEquivalence_unit

@[simp]
theorem asEquivalence_counit {F : C ⥤ D} [IsEquivalence F] :
    F.asEquivalence.counitIso = IsEquivalence.counitIso :=
  rfl
#align category_theory.functor.as_equivalence_counit CategoryTheory.Functor.asEquivalence_counit

@[simp]
theorem inv_inv (F : C ⥤ D) [IsEquivalence F] : inv (inv F) = F :=
  rfl
#align category_theory.functor.inv_inv CategoryTheory.Functor.inv_inv

variable {E : Type u₃} [Category.{v₃} E]

instance isEquivalenceTrans (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G] :
    IsEquivalence (F ⋙ G) :=
  IsEquivalence.ofEquivalence (Equivalence.trans (asEquivalence F) (asEquivalence G))
#align category_theory.functor.is_equivalence_trans CategoryTheory.Functor.isEquivalenceTrans

end Functor

namespace Equivalence

@[simp]
theorem functor_inv (E : C ≌ D) : E.functor.inv = E.inverse :=
  rfl
#align category_theory.equivalence.functor_inv CategoryTheory.Equivalence.functor_inv

@[simp]
theorem inverse_inv (E : C ≌ D) : E.inverse.inv = E.functor :=
  rfl
#align category_theory.equivalence.inverse_inv CategoryTheory.Equivalence.inverse_inv

@[simp]
theorem functor_asEquivalence (E : C ≌ D) : E.functor.asEquivalence = E := by
  cases E
  congr
#align category_theory.equivalence.functor_as_equivalence CategoryTheory.Equivalence.functor_asEquivalence

@[simp]
theorem inverse_asEquivalence (E : C ≌ D) : E.inverse.asEquivalence = E.symm := by
  cases E
  congr
#align category_theory.equivalence.inverse_as_equivalence CategoryTheory.Equivalence.inverse_asEquivalence

end Equivalence

namespace IsEquivalence

@[simp]
theorem fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) :
    F.map (F.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y := by
  erw [NatIso.naturality_2]
  rfl
#align category_theory.is_equivalence.fun_inv_map CategoryTheory.IsEquivalence.fun_inv_map

@[simp]
theorem inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) :
    F.inv.map (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.unit.app Y := by
  erw [NatIso.naturality_1]
  rfl
#align category_theory.is_equivalence.inv_fun_map CategoryTheory.IsEquivalence.inv_fun_map

/-- When a functor `F` is an equivalence of categories, and `G` is isomorphic to `F`, then
`G` is also an equivalence of categories. -/
@[simps!]
def ofIso {F G : C ⥤ D} (e : F ≅ G) (hF : IsEquivalence F) : IsEquivalence G
    where
  inverse := hF.inverse
  unitIso := hF.unitIso ≪≫ NatIso.hcomp e (Iso.refl hF.inverse)
  counitIso := NatIso.hcomp (Iso.refl hF.inverse) e.symm ≪≫ hF.counitIso
  functor_unitIso_comp X := by
    dsimp [NatIso.hcomp]
    erw [id_comp, F.map_id, comp_id]
    apply (cancel_epi (e.hom.app X)).mp
    slice_lhs 1 2 => rw [← e.hom.naturality]
    slice_lhs 2 3 => rw [← NatTrans.vcomp_app', e.hom_inv_id]
    simp only [NatTrans.id_app, id_comp, comp_id, F.map_comp, assoc]
    erw [hF.counitIso.hom.naturality]
    slice_lhs 1 2 => rw [functor_unitIso_comp]
    simp only [Functor.id_map, id_comp]
#align category_theory.is_equivalence.of_iso CategoryTheory.IsEquivalence.ofIso

/-- Compatibility of `ofIso` with the composition of isomorphisms of functors -/
theorem ofIso_trans {F G H : C ⥤ D} (e : F ≅ G) (e' : G ≅ H) (hF : IsEquivalence F) :
    ofIso e' (ofIso e hF) = ofIso (e ≪≫ e') hF := by
  dsimp [ofIso]
  congr 1 <;> ext X <;> dsimp [NatIso.hcomp]
  · simp only [id_comp, assoc, Functor.map_comp]
  · simp only [Functor.map_id, comp_id, id_comp, assoc]
#align category_theory.is_equivalence.of_iso_trans CategoryTheory.IsEquivalence.ofIso_trans

/-- Compatibility of `ofIso` with identity isomorphisms of functors -/
theorem ofIso_refl (F : C ⥤ D) (hF : IsEquivalence F) : ofIso (Iso.refl F) hF = hF := by
  rcases hF with ⟨Finv, Funit, Fcounit, Fcomp⟩
  dsimp [ofIso]
  congr 1 <;> ext X <;> dsimp [NatIso.hcomp]
  · simp only [comp_id, map_id]
  · simp only [id_comp, map_id]
#align category_theory.is_equivalence.of_iso_refl CategoryTheory.IsEquivalence.ofIso_refl

/-- When `F` and `G` are two isomorphic functors, then `F` is an equivalence iff `G` is. -/
@[simps]
def equivOfIso {F G : C ⥤ D} (e : F ≅ G) : IsEquivalence F ≃ IsEquivalence G
    where
  toFun := ofIso e
  invFun := ofIso e.symm
  left_inv hF := by rw [ofIso_trans, Iso.self_symm_id, ofIso_refl]
  right_inv hF := by rw [ofIso_trans, Iso.symm_self_id, ofIso_refl]
#align category_theory.is_equivalence.equiv_of_iso CategoryTheory.IsEquivalence.equivOfIso

/-- If `G` and `F ⋙ G` are equivalence of categories, then `F` is also an equivalence. -/
@[simp]
def cancelCompRight {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E) (hG : IsEquivalence G)
    (_ : IsEquivalence (F ⋙ G)) : IsEquivalence F :=
  ofIso (Functor.associator F G G.inv ≪≫ NatIso.hcomp (Iso.refl F) hG.unitIso.symm ≪≫ rightUnitor F)
    (Functor.isEquivalenceTrans (F ⋙ G) G.inv)
#align category_theory.is_equivalence.cancel_comp_right CategoryTheory.IsEquivalence.cancelCompRight

/-- If `F` and `F ⋙ G` are equivalence of categories, then `G` is also an equivalence. -/
@[simp]
def cancelCompLeft {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E) (hF : IsEquivalence F)
    (_ : IsEquivalence (F ⋙ G)) : IsEquivalence G :=
  ofIso
    ((Functor.associator F.inv F G).symm ≪≫ NatIso.hcomp hF.counitIso (Iso.refl G) ≪≫ leftUnitor G)
    (Functor.isEquivalenceTrans F.inv (F ⋙ G))
#align category_theory.is_equivalence.cancel_comp_left CategoryTheory.IsEquivalence.cancelCompLeft

end IsEquivalence

namespace Equivalence

/-- An equivalence is essentially surjective.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
theorem essSurj_of_equivalence (F : C ⥤ D) [IsEquivalence F] : EssSurj F :=
  ⟨fun Y => ⟨F.inv.obj Y, ⟨F.asEquivalence.counitIso.app Y⟩⟩⟩
#align category_theory.equivalence.ess_surj_of_equivalence CategoryTheory.Equivalence.essSurj_of_equivalence

-- see Note [lower instance priority]
/-- An equivalence is faithful.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
instance (priority := 100) faithfulOfEquivalence (F : C ⥤ D) [IsEquivalence F] : Faithful F where
  map_injective := @fun X Y f g h => by
    have p : F.inv.map (F.map f) = F.inv.map (F.map g) := congrArg F.inv.map h
    simpa only [cancel_epi, cancel_mono, IsEquivalence.inv_fun_map] using p
#align category_theory.equivalence.faithful_of_equivalence CategoryTheory.Equivalence.faithfulOfEquivalence

-- see Note [lower instance priority]
/-- An equivalence is full.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
instance (priority := 100) fullOfEquivalence (F : C ⥤ D) [IsEquivalence F] : Full F
    where
  preimage {X Y} f := F.asEquivalence.unit.app X ≫ F.inv.map f ≫ F.asEquivalence.unitInv.app Y
  witness {X Y} f :=
    F.inv.map_injective <| by
      simpa only [IsEquivalence.inv_fun_map, assoc, Iso.inv_hom_id_app_assoc,
        Iso.inv_hom_id_app] using comp_id _
#align category_theory.equivalence.full_of_equivalence CategoryTheory.Equivalence.fullOfEquivalence

@[simps]
private noncomputable def equivalenceInverse (F : C ⥤ D) [Full F] [Faithful F] [EssSurj F] : D ⥤ C
    where
  obj X := F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; aesop_cat
  map_comp {X Y Z} f g := by apply F.map_injective; simp
-- #align category_theory.equivalence.equivalence_inverse CategoryTheory.Equivalence.equivalenceInverse
/- Porting note: this is a private def in mathlib -/

--
/-- A functor which is full, faithful, and essentially surjective is an equivalence.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
noncomputable def ofFullyFaithfullyEssSurj (F : C ⥤ D) [Full F] [Faithful F] [EssSurj F] :
    IsEquivalence F :=
  IsEquivalence.mk (equivalenceInverse F)
    (NatIso.ofComponents (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      fun f => by
        apply F.map_injective
        aesop_cat)
    (NatIso.ofComponents F.objObjPreimageIso)
#align category_theory.equivalence.of_fully_faithfully_ess_surj CategoryTheory.Equivalence.ofFullyFaithfullyEssSurj

@[simp]
theorem functor_map_inj_iff (e : C ≌ D) {X Y : C} (f g : X ⟶ Y) :
    e.functor.map f = e.functor.map g ↔ f = g :=
  ⟨fun h => e.functor.map_injective h, fun h => h ▸ rfl⟩
#align category_theory.equivalence.functor_map_inj_iff CategoryTheory.Equivalence.functor_map_inj_iff

@[simp]
theorem inverse_map_inj_iff (e : C ≌ D) {X Y : D} (f g : X ⟶ Y) :
    e.inverse.map f = e.inverse.map g ↔ f = g :=
  functor_map_inj_iff e.symm f g
#align category_theory.equivalence.inverse_map_inj_iff CategoryTheory.Equivalence.inverse_map_inj_iff

instance essSurjInducedFunctor {C' : Type*} (e : C' ≃ D) : EssSurj (inducedFunctor e) where
  mem_essImage Y := ⟨e.symm Y, by simpa using ⟨default⟩⟩
#align category_theory.equivalence.ess_surj_induced_functor CategoryTheory.Equivalence.essSurjInducedFunctor

noncomputable instance inducedFunctorOfEquiv {C' : Type*} (e : C' ≃ D) :
    IsEquivalence (inducedFunctor e) :=
  Equivalence.ofFullyFaithfullyEssSurj _
#align category_theory.equivalence.induced_functor_of_equiv CategoryTheory.Equivalence.inducedFunctorOfEquiv

noncomputable instance fullyFaithfulToEssImage (F : C ⥤ D) [Full F] [Faithful F] :
    IsEquivalence F.toEssImage :=
  ofFullyFaithfullyEssSurj F.toEssImage
#align category_theory.equivalence.fully_faithful_to_ess_image CategoryTheory.Equivalence.fullyFaithfulToEssImage

end Equivalence

end CategoryTheory
