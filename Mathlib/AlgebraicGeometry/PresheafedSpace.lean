/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.presheafed_space
! leanprover-community/mathlib commit d39590fc8728fbf6743249802486f8c91ffe07bc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe w v u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

--attribute [local tidy] tactic.op_induction' tactic.auto_cases_opens

namespace AlgebraicGeometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace where
  carrier : TopCat.{w}
  protected presheaf : carrier.Presheaf C
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace AlgebraicGeometry.PresheafedSpace

variable {C}

namespace PresheafedSpace

-- porting note: using `Coe` here triggers an error, `CoeOut` seems a better choice
instance coeCarrier : CoeOut (PresheafedSpace.{w, v, u} C) TopCat.{w} where coe X := X.carrier
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.coe_carrier AlgebraicGeometry.PresheafedSpace.coeCarrier


-- porting note: the following lemma is removed because it is a syntatic tauto
/-@[simp]
theorem as_coe (X : PresheafedSpace.{w, v, u} C) : X.carrier = (X : TopCat.{w}) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.as_coe AlgebraicGeometry.PresheafedSpace.as_coe-/

-- porting note: removed @[simp] as the `simpVarHead` linter complains
-- were the restrictions on the universes done purposely here? (TODO: check whether
-- this compiles without these restrictions at the end of the port of this file)
--@[simp]
theorem mk_coe (carrier) (presheaf) :
    (({ carrier
        presheaf } : PresheafedSpace.{v} C) : TopCat.{v}) = carrier :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.mk_coe AlgebraicGeometry.PresheafedSpace.mk_coe

instance (X : PresheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : TopCat) (Z : C) : PresheafedSpace C where
  carrier := X
  presheaf :=
    { obj := fun _ => Z
      map := fun _ => 𝟙 Z }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.const AlgebraicGeometry.PresheafedSpace.const

instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (TopCat.of PEmpty) default⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure Hom (X Y : PresheafedSpace.{w, v, u} C) where
  base : (X : TopCat.{w}) ⟶ (Y : TopCat.{w})
  c : Y.presheaf ⟶ base _* X.presheaf
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.hom AlgebraicGeometry.PresheafedSpace.Hom

-- porting note: eventually, the ext lemma has to apply to terms of `X ⟶ Y` rather than `Hom X Y`,
-- this one was renamed `Hom.ext` instead of `ext`, and the more practical lemma `ext` is defined
-- just after the construction of the `Category` instance
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

-- porting note: `eqToHom` is no longer necessary in the definition of `c`
/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace.{w, v, u} C) : Hom X X where
  base := 𝟙 (X : TopCat.{w})
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

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance categoryOfPresheafedSpaces : Category (PresheafedSpace.{v, v, u} C) where
  Hom := Hom
  id := id
  comp := comp
  id_comp _ := by
    apply Hom.ext
    . dsimp
      simp only [map_id, whiskerRight_id', assoc]
      dsimp
      erw [comp_id, comp_id]
    . apply id_comp
  comp_id _ := by
    apply Hom.ext
    . dsimp
      simp only [id_comp, whiskerRight_id']
      erw [comp_id]
      rfl
    . apply comp_id
  assoc f g h := by
    apply Hom.ext
    . dsimp
      simp only [map_comp, whiskerRight_id', assoc]
      erw [comp_id]
      rfl
    . rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.category_of_PresheafedSpaces AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces

@[ext]
theorem ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  Hom.ext α β w h

end

variable {C}

attribute [local simp] eqToHom_map

@[simp]
theorem id_base (X : PresheafedSpace.{v, v, u} C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat.{v}) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id_base AlgebraicGeometry.PresheafedSpace.id_base

-- porting note: `eqToHom` is no longer needed in the statements of `id_c` and `id_c_app`
theorem id_c (X : PresheafedSpace.{v, v, u} C) :
    (𝟙 X : X ⟶ X).c = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id_c AlgebraicGeometry.PresheafedSpace.id_c

@[simp]
theorem id_c_app (X : PresheafedSpace.{v, v, u} C) (U) :
    (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U) := by
  rw [id_c, map_id]
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.id_c_app AlgebraicGeometry.PresheafedSpace.id_c_app

@[simp]
theorem comp_base {X Y Z : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.comp_base AlgebraicGeometry.PresheafedSpace.comp_base

instance (X Y : PresheafedSpace.{v, v, u} C) : CoeFun (X ⟶ Y) fun _ => (↑X → ↑Y) :=
  ⟨fun f => f.base⟩

-- porting note: removed as this is a syntactic tauto
--theorem coe_to_fun_eq {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) : (f : ↑X → ↑Y) = f.base :=
--  rfl
--#align algebraic_geometry.PresheafedSpace.coe_to_fun_eq AlgebraicGeometry.PresheafedSpace.coe_to_fun_eq

-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
theorem comp_c_app {X Y Z : PresheafedSpace.{v, v, u} C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.comp_c_app AlgebraicGeometry.PresheafedSpace.comp_c_app

theorem congr_app {X Y : PresheafedSpace.{v, v, u} C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h ; rfl)) := by
  subst h
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.congr_app AlgebraicGeometry.PresheafedSpace.congr_app

section

variable (C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace.{v, v, u} C ⥤ TopCat where
  obj X := (X : TopCat.{v})
  map f := f.base
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.forget AlgebraicGeometry.PresheafedSpace.forget

end

section Iso

variable {X Y : PresheafedSpace.{v, v, u} C}

/-- An isomorphism of PresheafedSpaces is a homeomorphism of the underlying space, and a
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
    · apply NatTrans.ext
      ext U
      rw [NatTrans.comp_app]
      simp only [id_base, comp_obj, op_obj, comp_base, Presheaf.pushforwardObj_obj,
        Opens.map_comp_obj, comp_c_app, unop_op, Presheaf.toPushforwardOfIso_app, assoc,
        Iso.hom_inv_id_app, comp_id, whiskerRight_app, eqToHom_app, id_c_app, map_id,
        ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
      dsimp
      rw [Iso.hom_inv_id]
  inv_hom_id := by
    ext
    . apply NatTrans.ext
      ext U
      dsimp
      rw [NatTrans.comp_app]
      simp only [Presheaf.pushforwardObj_obj, op_obj, Opens.map_comp_obj, comp_obj,
        comp_c_app, unop_op, Presheaf.toPushforwardOfIso_app, whiskerRight_app, eqToHom_app,
        assoc, id_c_app, map_id]
      rw [← α.hom.naturality, Presheaf.pushforwardObj_map, eqToHom_map, eqToHom_map,
        eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, id_comp]
      apply Iso.inv_hom_id_app
      dsimp
      rw [H.inv_hom_id]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.iso_of_components AlgebraicGeometry.PresheafedSpace.isoOfComponents

/-- Isomorphic PresheafedSpaces have natural isomorphic presheaves. -/
@[simps]
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 where
  hom := H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    apply NatTrans.ext
    ext U
    rw [NatTrans.comp_app]
    simpa using congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id U)
  inv_hom_id := by
    sorry
    --ext U
    --simp only [presheaf.pushforward_to_of_iso_app, nat_trans.comp_app, category.assoc,
    --  nat_trans.id_app, H.hom.c.naturality]
    --have := congr_app H.hom_inv_id ((opens.map H.hom.base).op.obj U)
    --generalize_proofs h  at this
    --simpa using congr_arg (fun f => f ≫ X.presheaf.map (eq_to_hom h.symm)) this
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.sheaf_iso_of_iso AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso

instance base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  IsIso.of_iso ((forget _).mapIso (asIso f))
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.base_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.base_isIso_of_iso

instance c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  IsIso.of_iso (sheafIsoOfIso (asIso f))
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.c_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.c_isIso_of_iso

/-- This could be used in conjunction with `CategoryTheory.NatIso.isIso_of_isIso_app`. -/
theorem isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f :=
  IsIso.of_iso (isoOfComponents (asIso f.base) (asIso f.c).symm)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.is_iso_of_components AlgebraicGeometry.PresheafedSpace.isIso_of_components

end Iso

section Restrict

/-- The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : TopCat} (X : PresheafedSpace.{v, v, u} C) {f : U ⟶ (X : TopCat.{v})}
    (h : OpenEmbedding f) : PresheafedSpace C where
  carrier := U
  presheaf := h.isOpenMap.functor.op ⋙ X.presheaf
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict AlgebraicGeometry.PresheafedSpace.restrict

/-- The map from the restriction of a presheafed space.
-/
@[simps]
def ofRestrict {U : TopCat} (X : PresheafedSpace.{v, v, u} C) {f : U ⟶ (X : TopCat.{v})}
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
  sorry
  --ext V
  --· induction V using Opposite.rec'
  --  have hV : (opens.map (X.of_restrict hf).base).obj (hf.is_open_map.functor.obj V) = V := by
  --    ext1
  --    exact Set.preimage_image_eq _ hf.inj
  --  haveI :
  --    is_iso (hf.is_open_map.adjunction.counit.app (unop (op (hf.is_open_map.functor.obj V)))) :=
  --    (nat_iso.is_iso_app_of_is_iso
  --        (whisker_left hf.is_open_map.functor hf.is_open_map.adjunction.counit) V :
  --      _)
  --  have := PresheafedSpace.congr_app Eq (op (hf.is_open_map.functor.obj V))
  --  simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, category.assoc,
  --    cancel_epi] at this
  --  have h : _ ≫ _ = _ ≫ _ ≫ _ :=
  --    congr_arg (fun f => (X.restrict hf).Presheaf.map (eq_to_hom hV).op ≫ f) this
  --  erw [g₁.c.naturality, g₂.c.naturality_assoc] at h
  --  simp only [presheaf.pushforward_obj_map, eq_to_hom_op, category.assoc, eq_to_hom_map,
  --    eq_to_hom_trans] at h
  --  rw [← is_iso.comp_inv_eq] at h
  --  simpa using h
  --· have := congr_arg PresheafedSpace.hom.base Eq
  --  simp only [PresheafedSpace.comp_base, PresheafedSpace.of_restrict_base] at this
  --  rw [cancel_mono] at this
  --  exact this
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
       is a natural isoomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  apply NatTrans.ext
  ext1 U
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.of_restrict_top_c AlgebraicGeometry.PresheafedSpace.ofRestrict_top_c

/- or `rw [opens.inclusion_top_functor, ←comp_obj, ←opens.map_comp_eq],
         erw iso.inv_hom_id, cases U, refl` after `dsimp` -/
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
  hom_inv_id :=
    sorry
    --ext _ _ (ConcreteCategory.hom_ext _ _ fun ⟨x, _⟩ => rfl) <| by
    --  erw [comp_c]
    --  rw [X.of_restrict_top_c]
    --  ext
    --  simp
  inv_hom_id :=
    sorry
    --ext _ _ rfl <| by
    --  erw [comp_c]
    --  rw [X.of_restrict_top_c]
    --  ext
    --  simpa [-eq_to_hom_refl]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.restrict_top_iso AlgebraicGeometry.PresheafedSpace.restrictTopIso

end Restrict

/-- The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace.{v, v, u} C)ᵒᵖ ⥤ C where
  obj X := (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.Γ AlgebraicGeometry.PresheafedSpace.Γ

theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.Γ_obj_op AlgebraicGeometry.PresheafedSpace.Γ_obj_op

theorem Γ_map_op {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.Γ_map_op AlgebraicGeometry.PresheafedSpace.Γ_map_op

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

attribute [local simp] Presheaf.pushforwardObj

namespace Functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def mapPresheaf (F : C ⥤ D) : PresheafedSpace.{v, v, u} C ⥤ PresheafedSpace.{v, v, u} D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- porting note: these proofs were automatic in mathlib3
  map_id := sorry
  map_comp := sorry
#align category_theory.functor.map_presheaf CategoryTheory.Functor.mapPresheaf

@[simp]
theorem mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X : TopCat.{v}) = (X : TopCat.{v}) :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_presheaf_obj_X CategoryTheory.Functor.mapPresheaf_obj_X

@[simp]
theorem mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl
#align category_theory.functor.map_presheaf_obj_presheaf CategoryTheory.Functor.mapPresheaf_obj_presheaf

@[simp]
theorem mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl
#align category_theory.functor.map_presheaf_map_f CategoryTheory.Functor.mapPresheaf_map_f

@[simp]
theorem mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) :
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
  -- porting note: this proof was automatic in mathlib3
  naturality := sorry
#align category_theory.nat_trans.on_presheaf CategoryTheory.NatTrans.onPresheaf

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end NatTrans

end CategoryTheory
