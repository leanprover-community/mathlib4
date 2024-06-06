/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

#align_import algebraic_geometry.presheafed_space from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

variable (C : Type*) [Category C]

-- Porting note: we used to have:
-- local attribute [tidy] tactic.auto_cases_opens
-- We would replace this by:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

-- Porting note: we used to have:
-- local attribute [tidy] tactic.op_induction'
-- A possible replacement would be:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opposite
-- but this would probably require https://github.com/JLimperg/aesop/issues/59
-- In any case, it doesn't seem necessary here.

namespace AlgebraicGeometry

-- Porting note: `PresheafSpace.{w} C` is the type of topological spaces in `Type w` equipped
-- with a presheaf with values in `C`; then there is a total of three universe parameters
-- in `PresheafSpace.{w, v, u} C`, where `C : Type u` and `Category.{v} C`.
-- In mathlib3, some definitions in this file unnecessarily assumed `w=v`. This restriction
-- has been removed.

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace where
  carrier : TopCat
  protected presheaf : carrier.Presheaf C
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace AlgebraicGeometry.PresheafedSpace

variable {C}

namespace PresheafedSpace

-- Porting note: using `Coe` here triggers an error, `CoeOut` seems an acceptable alternative
instance coeCarrier : CoeOut (PresheafedSpace C) TopCat where coe X := X.carrier
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.coe_carrier AlgebraicGeometry.PresheafedSpace.coeCarrier

attribute [coe] PresheafedSpace.carrier

-- Porting note: we add this instance, as Lean does not reliably use the `CoeOut` instance above
-- in downstream files.
instance : CoeSort (PresheafedSpace C) Type* where coe := fun X => X.carrier

-- Porting note: the following lemma is removed because it is a syntactic tauto
/-@[simp]
theorem as_coe (X : PresheafedSpace.{w, v, u} C) : X.carrier = (X : TopCat.{w}) :=
  rfl-/
set_option linter.uppercaseLean3 false in
#noalign algebraic_geometry.PresheafedSpace.as_coe

-- Porting note: removed @[simp] as the `simpVarHead` linter complains
-- @[simp]
theorem mk_coe (carrier) (presheaf) :
    (({ carrier
        presheaf } : PresheafedSpace C) : TopCat) = carrier :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.mk_coe AlgebraicGeometry.PresheafedSpace.mk_coe

instance (X : PresheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : TopCat) (Z : C) : PresheafedSpace C where
  carrier := X
  presheaf := (Functor.const _).obj Z
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.const AlgebraicGeometry.PresheafedSpace.const

instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (TopCat.of PEmpty) default⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure Hom (X Y : PresheafedSpace C) where
  base : (X : TopCat) ⟶ (Y : TopCat)
  c : Y.presheaf ⟶ base _* X.presheaf
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.hom AlgebraicGeometry.PresheafedSpace.Hom

-- Porting note: eventually, the ext lemma shall be applied to terms in `X ⟶ Y`
-- rather than `Hom X Y`, this one was renamed `Hom.ext` instead of `ext`,
-- and the more practical lemma `ext` is defined just after the definition
-- of the `Category` instance
@[ext]
theorem Hom.ext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β := by
  rcases α with ⟨base, c⟩
  rcases β with ⟨base', c'⟩
  dsimp at w
  subst w
  dsimp at h
  erw [whiskerRight_id', comp_id] at h
  subst h
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.ext AlgebraicGeometry.PresheafedSpace.Hom.ext

-- TODO including `injections` would make tidy work earlier.
theorem hext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : HEq α.c β.c) :
    α = β := by
  cases α
  cases β
  congr
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.hext AlgebraicGeometry.PresheafedSpace.hext

-- Porting note: `eqToHom` is no longer necessary in the definition of `c`
/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace C) : Hom X X where
  base := 𝟙 (X : TopCat)
  c := 𝟙 _
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id AlgebraicGeometry.PresheafedSpace.id

instance homInhabited (X : PresheafedSpace C) : Inhabited (Hom X X) :=
  ⟨id X⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.hom_inhabited AlgebraicGeometry.PresheafedSpace.homInhabited

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  base := α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.comp AlgebraicGeometry.PresheafedSpace.comp

theorem comp_c {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) :
    (comp α β).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.comp_c AlgebraicGeometry.PresheafedSpace.comp_c

variable (C)

section

attribute [local simp] id comp

-- Porting note: in mathlib3, `tidy` could (almost) prove the category axioms, but proofs
-- were included because `tidy` was slow. Here, `aesop_cat` succeeds reasonably quickly
-- for `comp_id` and `assoc`
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance categoryOfPresheafedSpaces : Category (PresheafedSpace C) where
  Hom := Hom
  id := id
  comp := comp
  id_comp _ := by
    dsimp
    ext
    · dsimp
      simp
    · dsimp
      simp only [map_id, whiskerRight_id', assoc]
      erw [comp_id, comp_id]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.category_of_PresheafedSpaces AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces

variable {C}

-- Porting note: adding an ext lemma.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
theorem ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  Hom.ext α β w h

end

variable {C}

attribute [local simp] eqToHom_map

@[simp]
theorem id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id_base AlgebraicGeometry.PresheafedSpace.id_base

-- Porting note: `eqToHom` is no longer needed in the statements of `id_c` and `id_c_app`
theorem id_c (X : PresheafedSpace C) :
    (𝟙 X : X ⟶ X).c = 𝟙 X.presheaf :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id_c AlgebraicGeometry.PresheafedSpace.id_c

@[simp]
theorem id_c_app (X : PresheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U) := by
  rw [id_c, map_id]
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id_c_app AlgebraicGeometry.PresheafedSpace.id_c_app

@[simp]
theorem comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.comp_base AlgebraicGeometry.PresheafedSpace.comp_base

instance (X Y : PresheafedSpace C) : CoeFun (X ⟶ Y) fun _ => (↑X → ↑Y) :=
  ⟨fun f => f.base⟩

-- Porting note: removed as this is a syntactic tauto
--theorem coe_to_fun_eq {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) : (f : ↑X → ↑Y) = f.base :=
--  rfl
#noalign algebraic_geometry.PresheafedSpace.coe_to_fun_eq

-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
-- Porting note: as there is no composition in the LHS it is purposely `@[reassoc, simp]` rather
-- than `@[reassoc (attr := simp)]`
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
theorem comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.comp_c_app AlgebraicGeometry.PresheafedSpace.comp_c_app

theorem congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) := by
  subst h
  simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.congr_app AlgebraicGeometry.PresheafedSpace.congr_app

section

variable (C)

/-- The forgetful functor from `PresheafedSpace` to `TopCat`. -/
@[simps]
def forget : PresheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map f := f.base
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.forget AlgebraicGeometry.PresheafedSpace.forget

end

section Iso

variable {X Y : PresheafedSpace C}

/-- An isomorphism of `PresheafedSpace`s is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps hom inv]
def isoOfComponents (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y where
  hom :=
    { base := H.hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.hom }
  hom_inv_id := by
    ext
    · simp only [comp_base, Iso.hom_inv_id, FunctorToTypes.map_id_apply, id_base]
    rw [NatTrans.comp_app]
    simp only [id_base, comp_obj, op_obj, comp_base, Presheaf.pushforwardObj_obj,
      Opens.map_comp_obj, comp_c_app, unop_op, Presheaf.toPushforwardOfIso_app, assoc,
      Iso.hom_inv_id_app, comp_id, whiskerRight_app, eqToHom_app, id_c_app, map_id,
      ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
  inv_hom_id := by
    ext
    · dsimp
      rw [H.inv_hom_id]
    dsimp
    simp only [Presheaf.pushforwardObj_obj, op_obj, Opens.map_comp_obj, comp_obj,
      comp_c_app, unop_op, Presheaf.toPushforwardOfIso_app, whiskerRight_app, eqToHom_app,
      assoc, id_c_app, map_id]
    rw [← α.hom.naturality, Presheaf.pushforwardObj_map, eqToHom_map, eqToHom_map,
      eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    apply Iso.inv_hom_id_app
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.iso_of_components AlgebraicGeometry.PresheafedSpace.isoOfComponents

/-- Isomorphic `PresheafedSpace`s have naturally isomorphic presheaves. -/
@[simps]
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 where
  hom := H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    ext U
    rw [NatTrans.comp_app]
    simpa using congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id (op U))
  inv_hom_id := by
    ext U
    dsimp
    rw [NatTrans.id_app]
    simp only [Presheaf.pushforwardObj_obj, op_obj, Presheaf.pushforwardToOfIso_app,
      Iso.symm_inv, mapIso_hom, forget_map, Iso.symm_hom, mapIso_inv,
      unop_op, eqToHom_map, assoc]
    have eq₁ := congr_app H.hom_inv_id (op ((Opens.map H.hom.base).obj U))
    have eq₂ := H.hom.c.naturality (eqToHom (congr_obj (congr_arg Opens.map
      ((forget C).congr_map H.inv_hom_id.symm)) U)).op
    rw [id_c, NatTrans.id_app, id_comp, eqToHom_map, comp_c_app] at eq₁
    rw [eqToHom_op, eqToHom_map] at eq₂
    erw [eq₂, reassoc_of% eq₁]
    simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.sheaf_iso_of_iso AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso

instance base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  ((forget _).mapIso (asIso f)).isIso_hom
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.base_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.base_isIso_of_iso

instance c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  (sheafIsoOfIso (asIso f)).isIso_hom
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.c_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.c_isIso_of_iso

/-- This could be used in conjunction with `CategoryTheory.NatIso.isIso_of_isIso_app`. -/
theorem isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f :=
  (isoOfComponents (asIso f.base) (asIso f.c).symm).isIso_hom
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.is_iso_of_components AlgebraicGeometry.PresheafedSpace.isIso_of_components

end Iso

section Restrict

/-- The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : OpenEmbedding f) : PresheafedSpace C where
  carrier := U
  presheaf := h.isOpenMap.functor.op ⋙ X.presheaf
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict AlgebraicGeometry.PresheafedSpace.restrict

/-- The map from the restriction of a presheafed space.
-/
@[simps]
def ofRestrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : OpenEmbedding f) : X.restrict h ⟶ X where
  base := f
  c :=
    { app := fun V => X.presheaf.map (h.isOpenMap.adjunction.counit.app V.unop).op
      naturality := fun U V f =>
        show _ = _ ≫ X.presheaf.map _ by
          rw [← map_comp, ← map_comp]
          rfl }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.of_restrict AlgebraicGeometry.PresheafedSpace.ofRestrict

instance ofRestrict_mono {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1) (hf : OpenEmbedding f) :
    Mono (X.ofRestrict hf) := by
  haveI : Mono f := (TopCat.mono_iff_injective _).mpr hf.inj
  constructor
  intro Z g₁ g₂ eq
  ext1
  · have := congr_arg PresheafedSpace.Hom.base eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base] at this
    rw [cancel_mono] at this
    exact this
  · ext V
    have hV : (Opens.map (X.ofRestrict hf).base).obj (hf.isOpenMap.functor.obj V) = V := by
      ext1
      exact Set.preimage_image_eq _ hf.inj
    haveI :
      IsIso (hf.isOpenMap.adjunction.counit.app (unop (op (hf.isOpenMap.functor.obj V)))) :=
        NatIso.isIso_app_of_isIso
          (whiskerLeft hf.isOpenMap.functor hf.isOpenMap.adjunction.counit) V
    have := PresheafedSpace.congr_app eq (op (hf.isOpenMap.functor.obj V))
    simp only [PresheafedSpace.comp_c_app, PresheafedSpace.ofRestrict_c_app, Category.assoc,
      cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).presheaf.map (eqToHom hV).op ≫ f) this
    erw [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [Presheaf.pushforwardObj_map, eqToHom_op, Category.assoc, eqToHom_map,
      eqToHom_trans] at h
    rw [← IsIso.comp_inv_eq, inv_eqToHom, Category.assoc, eqToHom_trans] at h
    rw [NatTrans.comp_app]
    simpa using h

set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.of_restrict_mono AlgebraicGeometry.PresheafedSpace.ofRestrict_mono

theorem restrict_top_presheaf (X : PresheafedSpace C) :
    (X.restrict (Opens.openEmbedding ⊤)).presheaf =
      (Opens.inclusionTopIso X.carrier).inv _* X.presheaf := by
  dsimp
  rw [Opens.inclusion_top_functor X.carrier]
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_top_presheaf AlgebraicGeometry.PresheafedSpace.restrict_top_presheaf

theorem ofRestrict_top_c (X : PresheafedSpace C) :
    (X.ofRestrict (Opens.openEmbedding ⊤)).c =
      eqToHom
        (by
          rw [restrict_top_presheaf, ← Presheaf.Pushforward.comp_eq]
          erw [Iso.inv_hom_id]
          rw [Presheaf.Pushforward.id_eq]) := by
  /- another approach would be to prove the left hand side
       is a natural isomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  ext
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.of_restrict_top_c AlgebraicGeometry.PresheafedSpace.ofRestrict_top_c

/-- The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def toRestrictTop (X : PresheafedSpace C) : X ⟶ X.restrict (Opens.openEmbedding ⊤) where
  base := (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.to_restrict_top AlgebraicGeometry.PresheafedSpace.toRestrictTop

/-- The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrictTopIso (X : PresheafedSpace C) : X.restrict (Opens.openEmbedding ⊤) ≅ X where
  hom := X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id := by
    ext
    · rfl
    · erw [comp_c, toRestrictTop_c, whiskerRight_id',
        comp_id, ofRestrict_top_c, eqToHom_map, eqToHom_trans, eqToHom_refl]
      rfl
  inv_hom_id := by
    ext
    · rfl
    · erw [comp_c, ofRestrict_top_c, toRestrictTop_c, eqToHom_map, whiskerRight_id', comp_id,
        eqToHom_trans, eqToHom_refl]
      rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_top_iso AlgebraicGeometry.PresheafedSpace.restrictTopIso

end Restrict

/-- The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C where
  obj X := (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.Γ AlgebraicGeometry.PresheafedSpace.Γ

theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.Γ_obj_op AlgebraicGeometry.PresheafedSpace.Γ_obj_op

theorem Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.Γ_map_op AlgebraicGeometry.PresheafedSpace.Γ_map_op

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type*} [Category D]

attribute [local simp] Presheaf.pushforwardObj

namespace Functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def mapPresheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- Porting note: these proofs were automatic in mathlib3
  map_id X := by
    ext U
    · rfl
    · simp
  map_comp f g := by
    ext U
    · rfl
    · simp
#align category_theory.functor.map_presheaf CategoryTheory.Functor.mapPresheaf

@[simp]
theorem mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X : TopCat) = (X : TopCat) :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_presheaf_obj_X CategoryTheory.Functor.mapPresheaf_obj_X

@[simp]
theorem mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl
#align category_theory.functor.map_presheaf_obj_presheaf CategoryTheory.Functor.mapPresheaf_obj_presheaf

@[simp]
theorem mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl
#align category_theory.functor.map_presheaf_map_f CategoryTheory.Functor.mapPresheaf_map_f

@[simp]
theorem mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).c = whiskerRight f.c F :=
  rfl
#align category_theory.functor.map_presheaf_map_c CategoryTheory.Functor.mapPresheaf_map_c

end Functor

namespace NatTrans

/-- A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def onPresheaf {F G : C ⥤ D} (α : F ⟶ G) : G.mapPresheaf ⟶ F.mapPresheaf where
  app X :=
    { base := 𝟙 _
      c := whiskerLeft X.presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }
#align category_theory.nat_trans.on_presheaf CategoryTheory.NatTrans.onPresheaf

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end NatTrans

end CategoryTheory
