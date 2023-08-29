/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.AlgebraicGeometry.LocallyRingedSpace

#align_import algebraic_geometry.open_immersion.basic from "leanprover-community/mathlib"@"533f62f4dd62a5aad24a04326e6e787c8f7e98b1"

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersion if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `AlgebraicGeometry.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`: Any morphism whose range is
  contained in an open immersion factors though the open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `to_SheafedSpace_hom`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `to_LocallyRingedSpace_hom`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp`: The composition of two open
  immersions is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso`: An iso is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `TopCat` preserves it).
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft`: Open immersions
  are stable under pullbacks.
* `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso` An (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/

-- Porting note : due to `PresheafedSpace`, `SheafedSpace` and `LocallyRingedSpace`
set_option linter.uppercaseLean3 false

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type*} [Category C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  /-- the underlying continuous map of underlying spaces from the source to an open subset of the
    target. -/
  base_open : OpenEmbedding f.base
  /-- the underlying sheaf morphism is an isomorphism on each open subset-/
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.isOpenMap.functor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f
#align algebraic_geometry.SheafedSpace.is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

section

variable {X Y : PresheafedSpace C} {f : X ⟶ Y} (H : IsOpenImmersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev openFunctor :=
  H.base_open.isOpenMap.functor
#align algebraic_geometry.PresheafedSpace.is_open_immersion.open_functor AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.openFunctor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _) <| by
    symm
    -- ⊢ (restrict Y (_ : OpenEmbedding ↑f.base)).presheaf ≅ (Iso.refl ↑X).hom _* X.p …
    fapply NatIso.ofComponents
    -- ⊢ (X_1 : (Opens ↑↑(restrict Y (_ : OpenEmbedding ↑f.base)))ᵒᵖ) → (restrict Y ( …
    · intro U
      -- ⊢ (restrict Y (_ : OpenEmbedding ↑f.base)).presheaf.obj U ≅ ((Iso.refl ↑X).hom …
      refine' asIso (f.c.app (op (H.openFunctor.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso _)
      -- ⊢ (Opens.map f.base).op.obj (op ((openFunctor H).obj U.unop)) = U
      · induction U using Opposite.rec' with | h U => ?_
        -- ⊢ (Opens.map f.base).op.obj (op ((openFunctor H).obj (op U).unop)) = op U
        -- ⊢ (Opens.map f.base).op.obj (op ((openFunctor H).obj U.unop)) = U
        cases U
        -- ⊢ (Opens.map f.base).op.obj (op ((openFunctor H).obj (op { carrier := carrier✝ …
        dsimp only [IsOpenMap.functor, Functor.op, Opens.map]
        -- ⊢ op { carrier := ↑f.base ⁻¹' ↑(op ((openFunctor H).obj (op { carrier := carri …
        congr 2
        -- ⊢ ↑f.base ⁻¹' ↑(op ((openFunctor H).obj (op { carrier := carrier✝, is_open' := …
        erw [Set.preimage_image_eq _ H.base_open.inj]
        -- ⊢ ↑(op { carrier := carrier✝, is_open' := is_open'✝ }).unop = carrier✝
        rfl
        -- 🎉 no goals
    · intro U V i
      -- ⊢ (restrict Y (_ : OpenEmbedding ↑f.base)).presheaf.map i ≫ (asIso (NatTrans.a …
      simp only [CategoryTheory.eqToIso.hom, TopCat.Presheaf.pushforwardObj_map, Category.assoc,
        Functor.op_map, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, ← X.presheaf.map_comp]
      erw [f.c.naturality_assoc, ← X.presheaf.map_comp]
      -- ⊢ NatTrans.app f.c ((IsOpenMap.functor (_ : IsOpenMap ↑f.base)).op.obj U) ≫ X. …
      congr 1
      -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict

@[simp]
theorem isoRestrict_hom_ofRestrict : H.isoRestrict.hom ≫ Y.ofRestrict _ = f := by
  -- Porting note : `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ rfl <| NatTrans.ext _ _ <| funext fun x => ?_
  -- ⊢ NatTrans.app (((isoRestrict H).hom ≫ ofRestrict Y (_ : OpenEmbedding ↑f.base …
  · simp only [isoRestrict_hom_c_app, NatTrans.comp_app, eqToHom_refl,
      ofRestrict_c_app, Category.assoc, whiskerRight_id']
    erw [Category.comp_id, comp_c_app, f.c.naturality_assoc, ← X.presheaf.map_comp]
    -- ⊢ NatTrans.app f.c x ≫ X.presheaf.map ((Opens.map f.base).op.map (NatTrans.app …
    trans f.c.app x ≫ X.presheaf.map (𝟙 _)
    -- ⊢ NatTrans.app f.c x ≫ X.presheaf.map ((Opens.map f.base).op.map (NatTrans.app …
    · congr 1
      -- 🎉 no goals
    · erw [X.presheaf.map_id, Category.comp_id]
      -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_hom_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict

@[simp]
theorem isoRestrict_inv_ofRestrict : H.isoRestrict.inv ≫ f = Y.ofRestrict _ := by
  rw [Iso.inv_comp_eq, isoRestrict_hom_ofRestrict]
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_inv_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict

instance mono [H : IsOpenImmersion f] : Mono f := by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp
  -- ⊢ Mono ((isoRestrict H).hom ≫ ofRestrict Y (_ : OpenEmbedding ↑f.base))
                                       -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.mono AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : IsOpenImmersion f] (g : Y ⟶ Z)
    [hg : IsOpenImmersion g] : IsOpenImmersion (f ≫ g) where
  base_open := hg.base_open.comp hf.base_open
  c_iso U := by
    generalize_proofs h
    -- ⊢ IsIso (NatTrans.app (f ≫ g).c (op ((IsOpenMap.functor h).obj U)))
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      TopCat.Presheaf.pushforwardObj_obj, Opens.map_comp_obj]
    -- Porting note : was `apply (config := { instances := False }) ...`
    -- See https://github.com/leanprover/lean4/issues/2273
    have : IsIso (g.c.app (op <| (h.functor).obj U))
    -- ⊢ IsIso (NatTrans.app g.c (op ((IsOpenMap.functor h).obj U)))
    · have : h.functor.obj U = hg.openFunctor.obj (hf.openFunctor.obj U) := by
        ext1
        dsimp only [IsOpenMap.functor_obj_coe]
        -- Porting note : slightly more hand holding here: `g ∘ f` and `fun x => g (f x)`
        rw [comp_base, coe_comp, show g.base ∘ f.base = fun x => g.base (f.base x) from rfl,
          ← Set.image_image]
      rw [this]
      -- ⊢ IsIso (NatTrans.app g.c (op ((openFunctor hg).obj ((openFunctor hf).obj U))))
      infer_instance
      -- 🎉 no goals
    have : IsIso (f.c.app (op <| (Opens.map g.base).obj ((IsOpenMap.functor h).obj U)))
    -- ⊢ IsIso (NatTrans.app f.c (op ((Opens.map g.base).obj ((IsOpenMap.functor h).o …
    · have : (Opens.map g.base).obj (h.functor.obj U) = hf.openFunctor.obj U := by
        ext1
        dsimp only [Opens.map_coe, IsOpenMap.functor_obj_coe, comp_base]
        -- Porting note : slightly more hand holding here: `g ∘ f` and `fun x => g (f x)`
        rw [coe_comp, show g.base ∘ f.base = fun x => g.base (f.base x) from rfl,
          ← Set.image_image g.base f.base, Set.preimage_image_eq _ hg.base_open.inj]
      rw [this]
      -- ⊢ IsIso (NatTrans.app f.c (op ((openFunctor hf).obj U)))
      infer_instance
      -- 🎉 no goals
    apply IsIso.comp_isIso
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.comp AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (H.openFunctor.obj U)) :=
  X.presheaf.map (eqToHom (by
    -- Porting note : was just `simp [opens.map, Set.preimage_image_eq _ H.base_open.inj]`
    -- See https://github.com/leanprover-community/mathlib4/issues/5026
    -- I think this is because `Set.preimage_image_eq _ H.base_open.inj` can't see through a
    -- structure
    congr; ext
    -- ⊢ U = (Opens.map f.base).obj (op ((openFunctor H).obj U)).unop
           -- ⊢ x✝ ∈ ↑U ↔ x✝ ∈ ↑((Opens.map f.base).obj (op ((openFunctor H).obj U)).unop)
    dsimp [openFunctor, IsOpenMap.functor]
    -- ⊢ x✝ ∈ ↑U ↔ x✝ ∈ ↑f.base ⁻¹' (↑f.base '' ↑U)
    rw [Set.preimage_image_eq _ H.base_open.inj])) ≫
    -- 🎉 no goals
    inv (f.c.app (op (H.openFunctor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp

@[simp, reassoc]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp (unop V) =
      H.invApp (unop U) ≫ Y.presheaf.map (H.openFunctor.op.map i) := by
  simp only [invApp, ← Category.assoc]
  -- ⊢ (X.presheaf.map i ≫ X.presheaf.map (eqToHom (_ : op V.unop = op ((Opens.map  …
  rw [IsIso.comp_inv_eq]
  -- ⊢ X.presheaf.map i ≫ X.presheaf.map (eqToHom (_ : op V.unop = op ((Opens.map f …
  -- Porting note : `simp` can't pick up `f.c.naturality`
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  simp only [Category.assoc, ← X.presheaf.map_comp]
  -- ⊢ X.presheaf.map (i ≫ eqToHom (_ : op V.unop = op ((Opens.map f.base).obj (op  …
  erw [f.c.naturality]
  -- ⊢ X.presheaf.map (i ≫ eqToHom (_ : op V.unop = op ((Opens.map f.base).obj (op  …
  simp only [IsIso.inv_hom_id_assoc, ← X.presheaf.map_comp]
  -- ⊢ X.presheaf.map (i ≫ eqToHom (_ : op V.unop = op ((Opens.map f.base).obj (op  …
  erw [← X.presheaf.map_comp]
  -- ⊢ X.presheaf.map (i ≫ eqToHom (_ : op V.unop = op ((Opens.map f.base).obj (op  …
  congr 1
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_naturality AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality

instance (U : Opens X) : IsIso (H.invApp U) := by delta invApp; infer_instance
                                                  -- ⊢ IsIso (X.presheaf.map (eqToHom (_ : op U = op ((Opens.map f.base).obj (op (( …
                                                                -- 🎉 no goals

theorem inv_invApp (U : Opens X) :
    inv (H.invApp U) =
      f.c.app (op (H.openFunctor.obj U)) ≫
        X.presheaf.map (eqToHom (by
          -- Porting note : was just `simp [opens.map, Set.preimage_image_eq _ H.base_open.inj]`
          -- See https://github.com/leanprover-community/mathlib4/issues/5026
          -- I think this is because `Set.preimage_image_eq _ H.base_open.inj` can't see through a
          -- structure
          apply congr_arg (op ·); ext
          -- ⊢ (Opens.map f.base).obj (op ((openFunctor H).obj U)).unop = U
                                  -- ⊢ x✝ ∈ ↑((Opens.map f.base).obj (op ((openFunctor H).obj U)).unop) ↔ x✝ ∈ ↑U
          dsimp [openFunctor, IsOpenMap.functor]
          -- ⊢ x✝ ∈ ↑f.base ⁻¹' (↑f.base '' ↑U) ↔ x✝ ∈ ↑U
          rw [Set.preimage_image_eq _ H.base_open.inj])) := by
          -- 🎉 no goals
  rw [← cancel_epi (H.invApp U), IsIso.hom_inv_id]
  -- ⊢ 𝟙 (X.presheaf.obj (op U)) = invApp H U ≫ NatTrans.app f.c (op ((openFunctor  …
  delta invApp
  -- ⊢ 𝟙 (X.presheaf.obj (op U)) = (X.presheaf.map (eqToHom (_ : op U = op ((Opens. …
  simp [← Functor.map_comp]
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp

@[simp, reassoc, elementwise]
theorem invApp_app (U : Opens X) :
    H.invApp U ≫ f.c.app (op (H.openFunctor.obj U)) =
      X.presheaf.map (eqToHom (by
        -- Porting note : was just `simp [opens.map, Set.preimage_image_eq _ H.base_open.inj]`
        -- See https://github.com/leanprover-community/mathlib4/issues/5026
        -- I think this is because `Set.preimage_image_eq _ H.base_open.inj` can't see through a
        -- structure
        apply congr_arg (op ·); ext
        -- ⊢ U = (Opens.map f.base).obj (op ((openFunctor H).obj U)).unop
                                -- ⊢ x✝ ∈ ↑U ↔ x✝ ∈ ↑((Opens.map f.base).obj (op ((openFunctor H).obj U)).unop)
        dsimp [openFunctor, IsOpenMap.functor]
        -- ⊢ x✝ ∈ ↑U ↔ x✝ ∈ ↑f.base ⁻¹' (↑f.base '' ↑U)
        rw [Set.preimage_image_eq _ H.base_open.inj])) :=
        -- 🎉 no goals
  by rw [invApp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
     -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app

@[simp, reassoc]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (H.openFunctor.obj ((Opens.map f.base).obj U))) :=
  by erw [← Category.assoc]; rw [IsIso.comp_inv_eq, f.c.naturality]; congr
     -- ⊢ (NatTrans.app f.c (op U) ≫ X.presheaf.map (eqToHom (_ : op ((Opens.map f.bas …
                             -- ⊢ NatTrans.app f.c (op U) ≫ X.presheaf.map (eqToHom (_ : op ((Opens.map f.base …
                                                                     -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp

/-- A variant of `app_inv_app` that gives an `eq_to_hom` instead of `hom_of_le`. -/
@[reassoc]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom
            (by
              apply le_antisymm
              -- ⊢ (openFunctor H).obj ((Opens.map f.base).obj U) ≤ U
              · exact Set.image_preimage_subset f.base U.1
                -- 🎉 no goals
              · rw [← SetLike.coe_subset_coe]
                -- ⊢ ↑U ⊆ ↑((openFunctor H).obj ((Opens.map f.base).obj U))
                refine' LE.le.trans_eq _ (@Set.image_preimage_eq_inter_range _ _ f.base U.1).symm
                -- ⊢ ↑U ≤ U.carrier ∩ Set.range ↑f.base
                exact Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op :=
                -- 🎉 no goals
  by erw [← Category.assoc]; rw [IsIso.comp_inv_eq, f.c.naturality]; congr
     -- ⊢ (NatTrans.app f.c (op U) ≫ X.presheaf.map (eqToHom (_ : op ((Opens.map f.bas …
                             -- ⊢ NatTrans.app f.c (op U) ≫ X.presheaf.map (eqToHom (_ : op ((Opens.map f.base …
                                                                     -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app' AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_inv_app'

/-- An isomorphism is an open immersion. -/
instance ofIso {X Y : PresheafedSpace C} (H : X ≅ Y) : IsOpenImmersion H.hom where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).openEmbedding
  -- Porting note : `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := c_isIso_of_iso H.hom; inferInstance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso

instance (priority := 100) ofIsIso {X Y : PresheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsOpenImmersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIsIso

instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : OpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) where
  base_open := hf
  c_iso U := by
    dsimp
    -- ⊢ IsIso (Y.presheaf.map (NatTrans.app (IsOpenMap.adjunction (_ : IsOpenMap ↑f) …
    have : (Opens.map f).obj (hf.isOpenMap.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.inj
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
      -- 🎉 no goals
    · -- Porting note : was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/leanprover/lean4/issues/2273
      congr
      -- ⊢ (IsOpenMap.functor (_ : IsOpenMap ↑f)).obj ((Opens.map f).obj ((IsOpenMap.fu …
      simp only [unop_op]
      -- ⊢ (IsOpenMap.functor (_ : IsOpenMap ↑f)).obj ((Opens.map f).obj ((IsOpenMap.fu …
      congr
      -- ⊢ HEq (NatTrans.app (IsOpenMap.adjunction (_ : IsOpenMap ↑f)).counit ((IsOpenM …
      apply Subsingleton.helim
      -- ⊢ ((IsOpenMap.functor (_ : IsOpenMap ↑f)).obj ((Opens.map f).obj ((IsOpenMap.f …
      rw [this]
      -- ⊢ ((IsOpenMap.functor (_ : IsOpenMap ↑f)).obj U ⟶ (IsOpenMap.functor (_ : IsOp …
      rfl
      -- 🎉 no goals
    · infer_instance
      -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict

@[elementwise, simp]
theorem ofRestrict_invApp {C : Type*} [Category C] (X : PresheafedSpace C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp U = 𝟙 _ := by
  delta invApp
  -- ⊢ (restrict X h).presheaf.map (eqToHom (_ : op U = op ((Opens.map (PresheafedS …
  rw [IsIso.comp_inv_eq, Category.id_comp]
  -- ⊢ (restrict X h).presheaf.map (eqToHom (_ : op U = op ((Opens.map (PresheafedS …
  change X.presheaf.map _ = X.presheaf.map _
  -- ⊢ X.presheaf.map ((IsOpenMap.functor (_ : IsOpenMap ↑f)).op.map (eqToHom (_ :  …
  congr 1
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso (f : X ⟶ Y) [h : IsOpenImmersion f] [h' : Epi f.base] : IsIso f := by
  -- Porting Note : was `apply (config := { instances := False }) ...`
  -- See https://github.com/leanprover/lean4/issues/2273
  have : ∀ (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U)
  -- ⊢ ∀ (U : (Opens ↑↑Y)ᵒᵖ), IsIso (NatTrans.app f.c U)
  · intro U
    -- ⊢ IsIso (NatTrans.app f.c U)
    have : U = op (h.openFunctor.obj ((Opens.map f.base).obj (unop U))) := by
      induction U using Opposite.rec' with | h U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert @IsOpenImmersion.c_iso _ _ _ _ _ h ((Opens.map f.base).obj (unop U))
    -- 🎉 no goals
  have : IsIso f.base
  -- ⊢ IsIso f.base
  · let t : X ≃ₜ Y :=
      (Homeomorph.ofEmbedding _ h.base_open.toEmbedding).trans
        { toFun := Subtype.val
          invFun := fun x =>
            ⟨x, by rw [Set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp h')]; trivial⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
    convert IsIso.of_iso (TopCat.isoOfHomeo t)
    -- 🎉 no goals
  have : IsIso f.c := by apply NatIso.isIso_of_isIso_app
  -- ⊢ IsIso f
  apply isIso_of_components
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso

instance stalk_iso [HasColimits C] [H : IsOpenImmersion f] (x : X) : IsIso (stalkMap f x) := by
  rw [← H.isoRestrict_hom_ofRestrict]
  -- ⊢ IsIso (stalkMap ((isoRestrict H).hom ≫ PresheafedSpace.ofRestrict Y (_ : Ope …
  rw [PresheafedSpace.stalkMap.comp]
  -- ⊢ IsIso (stalkMap (PresheafedSpace.ofRestrict Y (_ : OpenEmbedding ↑f.base)) ( …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso

end

noncomputable section Pullback

variable {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : IsOpenImmersion f] (g : Y ⟶ Z)

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base) ⟶ X where
  base := pullback.fst
  c :=
    { app := fun U =>
        hf.invApp (unop U) ≫
          g.c.app (op (hf.base_open.isOpenMap.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, Subtype.mk_eq_mk, unop_op, op_inj_iff, Opens.map,
                    Subtype.coe_mk, Functor.op_obj]
                  apply LE.le.antisymm
                  -- ⊢ { carrier := ↑g.base ⁻¹' ↑{ carrier := ↑f.base '' ↑U.unop, is_open' := (_ :  …
                  · rintro _ ⟨_, h₁, h₂⟩
                    -- ⊢ a✝ ∈ ↑{ carrier := ↑pullback.snd '' ↑{ carrier := ↑pullback.fst ⁻¹' ↑U.unop, …
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    -- ⊢ ↑(TopCat.pullbackIsoProdSubtype f.base g.base).inv { val := (w✝, a✝), proper …
                    -- Porting note : need a slight hand holding
                    change _ ∈ _ ⁻¹' _ ∧ _
                    -- ⊢ ↑(TopCat.pullbackIsoProdSubtype f.base g.base).inv { val := (w✝, a✝), proper …
                    simpa using h₁
                    -- 🎉 no goals
                  · rintro _ ⟨x, h₁, rfl⟩
                    -- ⊢ ↑pullback.snd x ∈ ↑{ carrier := ↑g.base ⁻¹' ↑{ carrier := ↑f.base '' ↑U.unop …
                    exact ⟨_, h₁, ConcreteCategory.congr_hom pullback.condition x⟩))
                    -- 🎉 no goals
      naturality := by
        intro U V i
        -- ⊢ X.presheaf.map i ≫ (fun U => invApp hf U.unop ≫ NatTrans.app g.c (op ((IsOpe …
        induction U using Opposite.rec'
        -- ⊢ X.presheaf.map i ≫ (fun U => invApp hf U.unop ≫ NatTrans.app g.c (op ((IsOpe …
        induction V using Opposite.rec'
        -- ⊢ X.presheaf.map i ≫ (fun U => invApp hf U.unop ≫ NatTrans.app g.c (op ((IsOpe …
        simp only [Quiver.Hom.unop_op, Category.assoc, Functor.op_map, inv_naturality_assoc]
        -- ⊢ invApp hf (op X✝¹).unop ≫ Z.presheaf.map ((openFunctor hf).map i.unop).op ≫  …
        -- Porting note : the following lemmas are not picked up by `simp`
        -- See https://github.com/leanprover-community/mathlib4/issues/5026
        erw [g.c.naturality_assoc, TopCat.Presheaf.pushforwardObj_map, ← Y.presheaf.map_comp,
          ← Y.presheaf.map_comp]
        congr 1 }
        -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g := by
  -- Porting note : `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext _ _ <| funext fun U => ?_
  -- ⊢ (pullbackConeOfLeftFst f g ≫ f).base = (PresheafedSpace.ofRestrict Y (_ : Op …
  · simpa using pullback.condition
    -- 🎉 no goals
  · induction U using Opposite.rec'
    -- ⊢ NatTrans.app ((pullbackConeOfLeftFst f g ≫ f).c ≫ whiskerRight (eqToHom (_ : …
    -- Porting note : `NatTrans.comp_app` is not picked up by `dsimp`
    -- Perhaps see : https://github.com/leanprover-community/mathlib4/issues/5026
    rw [NatTrans.comp_app]
    -- ⊢ NatTrans.app (pullbackConeOfLeftFst f g ≫ f).c (op X✝) ≫ NatTrans.app (whisk …
    dsimp only [comp_c_app, unop_op, whiskerRight_app, pullbackConeOfLeftFst]
    -- ⊢ (NatTrans.app f.c (op X✝) ≫ invApp hf ((Opens.map f.base).obj X✝) ≫ NatTrans …
    -- simp only [ofRestrict_c_app, NatTrans.comp_app]
    simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforwardObj_map, app_invApp_assoc,
      eqToHom_app, eqToHom_unop, Category.assoc, NatTrans.naturality_assoc, Functor.op_map]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    -- ⊢ NatTrans.app g.c (op X✝) ≫ Y.presheaf.map (((Opens.map g.base).map (homOfLE  …
    congr 1
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft

variable (s : PullbackCone f g)

/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullbackConeOfLeftLift : s.pt ⟶ (pullbackConeOfLeft f g).pt where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map, IsOpenMap.functor, Functor.op]
                -- ⊢ op { carrier := ↑(PullbackCone.snd s).base ⁻¹' ↑(op { carrier := ↑pullback.s …
                congr 2
                -- ⊢ ↑(PullbackCone.snd s).base ⁻¹' ↑(op { carrier := ↑pullback.snd '' ↑U.unop, i …
                let s' : PullbackCone f.base g.base := PullbackCone.mk s.fst.base s.snd.base
                  -- Porting note : in mathlib3, this is just an underscore
                  (congr_arg Hom.base s.condition)

                have : _ = s.snd.base := limit.lift_π s' WalkingCospan.right
                -- ⊢ ↑(PullbackCone.snd s).base ⁻¹' ↑(op { carrier := ↑pullback.snd '' ↑U.unop, i …
                conv_lhs =>
                  erw [← this]
                  dsimp
                  -- Porting note : need a bit more hand holding here about function composition
                  rw [coe_comp, show ∀ f g, f ∘ g = fun x => f (g x) from fun _ _ => rfl]
                  erw [← Set.preimage_preimage]
                erw [Set.preimage_image_eq _
                    (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base).inj]
                rfl))
                -- 🎉 no goals
      naturality := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        -- ⊢ NatTrans.app (PullbackCone.snd s).c ((IsOpenMap.functor (_ : IsOpenMap ↑pull …
        rw [Category.assoc]
        -- ⊢ NatTrans.app (PullbackCone.snd s).c ((IsOpenMap.functor (_ : IsOpenMap ↑pull …
        erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
        -- ⊢ NatTrans.app (PullbackCone.snd s).c ((IsOpenMap.functor (_ : IsOpenMap ↑pull …
        congr 1 }
        -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst := by
  -- Porting note : `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext _ _ <| funext fun x => ?_
  -- ⊢ (pullbackConeOfLeftLift f g s ≫ PullbackCone.fst (pullbackConeOfLeft f g)).b …
  · change pullback.lift _ _ _ ≫ pullback.fst = _
    -- ⊢ pullback.lift (PullbackCone.fst s).base (PullbackCone.snd s).base (_ : (Pull …
    simp
    -- 🎉 no goals
  · induction x using Opposite.rec' with | h x => ?_
    -- ⊢ NatTrans.app ((pullbackConeOfLeftLift f g s ≫ PullbackCone.fst (pullbackCone …
    -- ⊢ NatTrans.app ((pullbackConeOfLeftLift f g s ≫ PullbackCone.fst (pullbackCone …
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    -- ⊢ ((invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOp …
    simp_rw [Category.assoc]
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    erw [← s.pt.presheaf.map_comp]
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    erw [s.snd.c.naturality_assoc]
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    have := congr_app s.condition (op (hf.openFunctor.obj x))
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    dsimp only [comp_c_app, unop_op] at this
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    rw [← IsIso.comp_inv_eq] at this
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    replace this := reassoc_of% this
    -- ⊢ invApp hf (op x).unop ≫ NatTrans.app g.c (op ((IsOpenMap.functor (_ : IsOpen …
    erw [← this, hf.invApp_app_assoc, s.fst.c.naturality_assoc]
    -- ⊢ NatTrans.app (PullbackCone.fst s).c (op (op x).unop) ≫ ((PullbackCone.fst s) …
    simp [eqToHom_map]
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd := by
  -- Porting note : `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext _ _ <| funext fun x => ?_
  -- ⊢ (pullbackConeOfLeftLift f g s ≫ PullbackCone.snd (pullbackConeOfLeft f g)).b …
  · change pullback.lift _ _ _ ≫ pullback.snd = _
    -- ⊢ pullback.lift (PullbackCone.fst s).base (PullbackCone.snd s).base (_ : (Pull …
    simp
    -- 🎉 no goals
  · change (_ ≫ _ ≫ _) ≫ _ = _
    -- ⊢ (NatTrans.app (PullbackCone.snd (pullbackConeOfLeft f g)).c x ≫ NatTrans.app …
    simp_rw [Category.assoc]
    -- ⊢ NatTrans.app (PullbackCone.snd (pullbackConeOfLeft f g)).c x ≫ NatTrans.app  …
    erw [s.snd.c.naturality_assoc]
    -- ⊢ NatTrans.app (PullbackCone.snd s).c x ≫ ((PullbackCone.snd s).base _* s.pt.p …
    erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
    -- ⊢ NatTrans.app (PullbackCone.snd s).c x ≫ s.pt.presheaf.map ((Opens.map (Pullb …
    trans s.snd.c.app x ≫ s.pt.presheaf.map (𝟙 _)
    -- ⊢ NatTrans.app (PullbackCone.snd s).c x ≫ s.pt.presheaf.map ((Opens.map (Pullb …
    · congr 1
      -- 🎉 no goals
    · rw [s.pt.presheaf.map_id]; erw [Category.comp_id]
      -- ⊢ NatTrans.app (PullbackCone.snd s).c x ≫ 𝟙 (s.pt.presheaf.obj ((Opens.map (Pu …
                                 -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd

instance pullbackConeSndIsOpenImmersion : IsOpenImmersion (pullbackConeOfLeft f g).snd := by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  -- ⊢ IsOpenImmersion (PresheafedSpace.ofRestrict Y (_ : OpenEmbedding ↑pullback.s …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_snd_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeSndIsOpenImmersion

/-- The constructed pullback cone is indeed the pullback. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) := by
  apply PullbackCone.isLimitAux'
  -- ⊢ (s : PullbackCone f g) → { l // l ≫ PullbackCone.fst (pullbackConeOfLeft f g …
  intro s
  -- ⊢ { l // l ≫ PullbackCone.fst (pullbackConeOfLeft f g) = PullbackCone.fst s ∧  …
  use pullbackConeOfLeftLift f g s
  -- ⊢ pullbackConeOfLeftLift f g s ≫ PullbackCone.fst (pullbackConeOfLeft f g) = P …
  use pullbackConeOfLeftLift_fst f g s
  -- ⊢ pullbackConeOfLeftLift f g s ≫ PullbackCone.snd (pullbackConeOfLeft f g) = P …
  use pullbackConeOfLeftLift_snd f g s
  -- ⊢ ∀ {m : s.pt ⟶ (pullbackConeOfLeft f g).pt}, m ≫ PullbackCone.fst (pullbackCo …
  intro m _ h₂
  -- ⊢ m = pullbackConeOfLeftLift f g s
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  -- ⊢ m ≫ PullbackCone.snd (pullbackConeOfLeft f g) = pullbackConeOfLeftLift f g s …
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullbackSndOfLeft : IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta pullback.snd
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) WalkingCospan.right)
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  -- ⊢ IsOpenImmersion ((limit.isoLimitCone { cone := pullbackConeOfLeft f g, isLim …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft

/-- Open immersions are stable under base-change. -/
instance pullbackFstOfRight : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  -- ⊢ IsOpenImmersion ((pullbackSymmetry g f).hom ≫ pullback.snd)
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackFstOfRight

instance pullbackToBaseIsOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) WalkingCospan.left ≫ f)
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackToBaseIsOpenImmersion

instance forgetPreservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan _) _).toFun
      -- ⊢ IsLimit ((Cones.postcompose (diagramIsoCospan (cospan f g ⋙ forget C)).hom). …
      refine' (IsLimit.equivIsoLimit _).toFun (limit.isLimit (cospan f.base g.base))
      -- ⊢ limit.cone (cospan f.base g.base) ≅ (Cones.postcompose (diagramIsoCospan (co …
      fapply Cones.ext
      -- ⊢ (limit.cone (cospan f.base g.base)).pt ≅ ((Cones.postcompose (diagramIsoCosp …
      · exact Iso.refl _
        -- 🎉 no goals
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      -- ⊢ ∀ (j : WalkingCospan), NatTrans.app (limit.cone (cospan f.base g.base)).π j  …
      simp_rw [Category.id_comp]
      -- ⊢ ∀ (j : WalkingCospan), NatTrans.app (limit.cone (cospan f.base g.base)).π j  …
      rintro (_ | _ | _) <;> symm
                             -- ⊢ NatTrans.app ((forget C).mapCone (pullbackConeOfLeft f g)).π none ≫ NatTrans …
                             -- ⊢ NatTrans.app ((forget C).mapCone (pullbackConeOfLeft f g)).π (some WalkingPa …
                             -- ⊢ NatTrans.app ((forget C).mapCone (pullbackConeOfLeft f g)).π (some WalkingPa …
      · erw [Category.comp_id]
        -- ⊢ NatTrans.app ((forget C).mapCone (pullbackConeOfLeft f g)).π none = NatTrans …
        exact limit.w (cospan f.base g.base) WalkingCospan.Hom.inl
        -- 🎉 no goals
      · exact Category.comp_id _
        -- 🎉 no goals
      · exact Category.comp_id _)
        -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfLeft

instance forgetPreservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullbackSymmetry (forget C) f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfRight

theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) := by
  haveI := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.toEmbedding g.base H
  -- ⊢ IsIso pullback.snd
  have : IsIso (pullback.snd : pullback f g ⟶ _).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd)
    infer_instance
  apply to_iso
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g := by
  -- Porting note : this instance was automatic
  letI := pullback_snd_isIso_of_range_subset _ _ H
  -- ⊢ lift f g H ≫ f = g
  erw [Category.assoc]; rw [IsIso.inv_comp_eq]; exact pullback.condition
  -- ⊢ inv pullback.snd ≫ pullback.fst ≫ f = g
                        -- ⊢ pullback.fst ≫ f = pullback.snd ≫ g
                                                -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_fac AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]
                         -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
                   -- ⊢ (lift g f (_ : Set.range ↑f.base ≤ Set.range ↑g.base) ≫ lift f g (_ : Set.ra …
                                         -- 🎉 no goals
  inv_hom_id := by rw [← cancel_mono g]; simp
                   -- ⊢ (lift f g (_ : Set.range ↑g.base ≤ Set.range ↑f.base) ≫ lift g f (_ : Set.ra …
                                         -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_of_range_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace C} (Y : SheafedSpace C)

variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace : SheafedSpace C where
  IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso H.isoRestrict.symm).symm
    -- ⊢ TopCat.Presheaf.IsSheaf ((isoRestrict H).symm.hom.base _* (restrict Y.toPres …
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    -- ⊢ TopCat.Presheaf.IsSheaf (restrict Y.toPresheafedSpace (_ : OpenEmbedding ↑f. …
    exact (Y.restrict H.base_open).IsSheaf
    -- 🎉 no goals
  toPresheafedSpace := X
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace

@[simp]
theorem toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_to_PresheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_toPresheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom

@[simp]
theorem toSheafedSpaceHom_base : (toSheafedSpaceHom Y f).base = f.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_base AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_base

@[simp]
theorem toSheafedSpaceHom_c : (toSheafedSpaceHom Y f).c = f.c :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_c AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_c

instance toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_isOpenImmersion

@[simp]
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y) [IsOpenImmersion f] :
    toSheafedSpace Y f = X := by cases X; rfl
                                 -- ⊢ toSheafedSpace Y f = { toPresheafedSpace := toPresheafedSpace✝, IsSheaf := I …
                                          -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.SheafedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.sheafedSpace_toSheafedSpace

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace CommRingCat} (Y : LocallyRingedSpace)

variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  localRing x :=
    haveI : LocalRing (Y.stalk (f.base x)) := Y.localRing _
    (asIso (stalkMap f x)).commRingCatIsoToRingEquiv.localRing
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace

@[simp]
theorem toLocallyRingedSpace_toSheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_toSheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun _ => inferInstance⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom

@[simp]
theorem toLocallyRingedSpaceHom_val : (toLocallyRingedSpaceHom Y f).val = f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom_val AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom_val

instance toLocallyRingedSpace_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_isOpenImmersion

@[simp]
theorem locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.1 = X := by
    cases X; delta toLocallyRingedSpace; simp
    -- ⊢ toLocallyRingedSpace Y f.val = { toSheafedSpace := toSheafedSpace✝, localRin …
             -- ⊢ { toSheafedSpace := toSheafedSpace Y.toSheafedSpace f.val, localRing := (_ : …
                                         -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.LocallyRingedSpace_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.locallyRingedSpace_toLocallyRingedSpace

end ToLocallyRingedSpace

theorem isIso_of_subset {X Y : PresheafedSpace C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) := by
  have : U = H.base_open.isOpenMap.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left_iff_subset.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert H.c_iso ((Opens.map f.base).obj U)
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.is_open_immersion.is_iso_of_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isIso_of_subset

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

instance (priority := 100) of_isIso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ f
    (SheafedSpace.forgetToPresheafedSpace.map_isIso _)
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_isIso

instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f g
#align algebraic_geometry.SheafedSpace.is_open_immersion.comp AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp

noncomputable section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : SheafedSpace.IsOpenImmersion f]

-- Porting note : in mathlib3, this local notation is often followed by a space to avoid confusion
-- with the forgetful functor, now it is often wrapped in a parenthesis
local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

instance : Mono f :=
  (forget).mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f by infer_instance)
                                                                       -- 🎉 no goals

instance forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion

instance hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) := by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr))
  -- ⊢ HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget). …
  · change HasLimit (cospan ((forget).map f) ((forget).map g))
    -- ⊢ HasLimit (cospan (forget.map f) (forget.map g))
    infer_instance
    -- 🎉 no goals
  apply hasLimitOfIso (diagramIsoCospan _).symm
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left

instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left'

instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr))
  -- ⊢ HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget). …
  · change HasLimit (cospan ((forget).map g) ((forget).map f))
    -- ⊢ HasLimit (cospan (forget.map g) (forget.map f))
    infer_instance
    -- 🎉 no goals
  apply hasLimitOfIso (diagramIsoCospan _).symm
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right

instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right'

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
                                                  -- 🎉 no goals
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfLeft

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
                                                  -- 🎉 no goals
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfRight

instance sheafedSpaceForgetPreservesOfLeft : PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.compPreservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
    inferInstance <| by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C)
      · dsimp
        -- ⊢ PreservesLimit (cospan f g) (PresheafedSpace.forget C)
        infer_instance
        -- 🎉 no goals
      apply preservesLimitOfIsoDiagram _ (diagramIsoCospan _).symm
      -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpaceForgetPreservesOfLeft

instance sheafedSpaceForgetPreservesOfRight : PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpaceForgetPreservesOfRight

instance sheafedSpace_hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_left

instance sheafedSpace_hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance sheafedSpace_pullback_snd_of_left :
    SheafedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta pullback.snd
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) right)
  have : _ = limit.π (cospan f g) right := preservesLimitsIso_hom_π forget (cospan f g) right
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) right)
  rw [← this]
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan f g)).hom ≫ limit.π (cosp …
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan f g)).hom ≫ limit.π (cosp …
  erw [Category.comp_id] at this
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan f g)).hom ≫ limit.π (cosp …
  rw [← this]
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan f g)).hom ≫ (HasLimit.iso …
  dsimp
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan f g)).hom ≫ (HasLimit.iso …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_snd_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_snd_of_left

instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  delta pullback.fst
  -- ⊢ IsOpenImmersion (limit.π (cospan g f) left)
  have : _ = limit.π (cospan g f) left := preservesLimitsIso_hom_π forget (cospan g f) left
  -- ⊢ IsOpenImmersion (limit.π (cospan g f) left)
  rw [← this]
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan g f)).hom ≫ limit.π (cosp …
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan g f)).hom ≫ limit.π (cosp …
  erw [Category.comp_id] at this
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan g f)).hom ≫ limit.π (cosp …
  rw [← this]
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan g f)).hom ≫ (HasLimit.iso …
  dsimp
  -- ⊢ IsOpenImmersion ((preservesLimitIso forget (cospan g f)).hom ≫ (HasLimit.iso …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_fst_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_right

instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) := by
  rw [← limit.w (cospan f g) Hom.inl, cospan_map_inl]
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) left ≫ f)
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_to_base_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_to_base_isOpenImmersion

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] [ConcreteCategory C]

variable [ReflectsIsomorphisms (CategoryTheory.forget C)]
  [PreservesLimits (CategoryTheory.forget C)]

variable [PreservesFilteredColimits (CategoryTheory.forget C)]

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : OpenEmbedding f.base)
    [H : ∀ x : X.1, IsIso (PresheafedSpace.stalkMap f x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U => by
      -- Porting note : was `apply (config := { instances := False }) ...`
      -- See https://github.com/leanprover/lean4/issues/2273
      have h := TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward f.base).obj X.sheaf from ⟨f.c⟩)
      refine @h _ ?_
      -- ⊢ ∀ (x : { x // x ∈ (IsOpenMap.functor (_ : IsOpenMap ↑f.base)).obj U }),
      rintro ⟨_, y, hy, rfl⟩
      -- ⊢ IsIso
      specialize H y
      -- ⊢ IsIso
      delta PresheafedSpace.stalkMap at H
      -- ⊢ IsIso
      haveI H' :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_openEmbedding C hf X.presheaf y
      have := @IsIso.comp_isIso _ _ _ _ _ _ _ H (@IsIso.inv_isIso _ _ _ _ _ H')
      -- ⊢ IsIso
      rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this }
      -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso

end OfStalkIso

section Prod

-- Porting note : here `ι` should have same universe level as morphism of `C`, so needs explicit
-- universe level now
variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F]
  (i : Discrete ι)

theorem sigma_ι_openEmbedding : OpenEmbedding (colimit.ι F i).base := by
  rw [← show _ = (colimit.ι F i).base from ι_preservesColimitsIso_inv (SheafedSpace.forget C) F i]
  -- ⊢ OpenEmbedding ↑(colimit.ι (F ⋙ forget C) i ≫ (preservesColimitIso (forget C) …
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
  -- ⊢ OpenEmbedding ↑(colimit.ι (F ⋙ forget C) i ≫ (preservesColimitIso (forget C) …
  rw [this]
  -- ⊢ OpenEmbedding ↑(((NatTrans.app Discrete.natIsoFunctor.hom i ≫ colimit.ι (Dis …
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk) i.as
  rw [← Iso.eq_comp_inv] at this
  -- ⊢ OpenEmbedding ↑(((NatTrans.app Discrete.natIsoFunctor.hom i ≫ colimit.ι (Dis …
  cases i
  -- ⊢ OpenEmbedding ↑(((NatTrans.app Discrete.natIsoFunctor.hom { as := as✝ } ≫ co …
  rw [this, ← Category.assoc]
  -- ⊢ OpenEmbedding ↑((((NatTrans.app Discrete.natIsoFunctor.hom { as := as✝ } ≫ T …
  -- Porting note : `simp_rw` can't use `TopCat.openEmbedding_iff_comp_isIso` and
  -- `TopCat.openEmbedding_iff_isIso_comp`.
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  erw [TopCat.openEmbedding_iff_comp_isIso, TopCat.openEmbedding_iff_comp_isIso,
    TopCat.openEmbedding_iff_comp_isIso, TopCat.openEmbedding_iff_isIso_comp]
  exact openEmbedding_sigmaMk
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_open_embedding AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_openEmbedding

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_openEmbedding F i).isOpenMap.functor.obj U)) =
      ⊥ := by
  ext x
  -- ⊢ x ∈ ↑((Opens.map (colimit.ι (F ⋙ forgetToPresheafedSpace) j).base).obj ((Ope …
  apply iff_false_intro
  -- ⊢ ¬x ∈ ↑((Opens.map (colimit.ι (F ⋙ forgetToPresheafedSpace) j).base).obj ((Op …
  rintro ⟨y, hy, eq⟩
  -- ⊢ False
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  -- ⊢ False
  rw [ι_preservesColimitsIso_inv] at eq
  -- ⊢ False
  -- Porting note : without this `erw`, change does not work
  erw [←comp_apply, ←comp_apply] at eq
  -- ⊢ False
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at eq
  cases i; cases j
  -- ⊢ False
           -- ⊢ False
  rw [ι_preservesColimitsIso_hom_assoc, ι_preservesColimitsIso_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    TopCat.sigmaIsoSigma_hom_ι, TopCat.sigmaIsoSigma_hom_ι] at eq
  exact h (congr_arg Discrete.mk (congr_arg Sigma.fst eq))
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.image_preimage_is_empty AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty

instance sigma_ι_isOpenImmersion [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) where
  base_open := sigma_ι_openEmbedding F i
  c_iso U := by
    have e : colimit.ι F i = _ :=
      (ι_preservesColimitsIso_inv SheafedSpace.forgetToPresheafedSpace F i).symm
    have H :
      OpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
            (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).base :=
      e ▸ sigma_ι_openEmbedding F i
    suffices IsIso <| (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).c.app <|
      op (H.isOpenMap.functor.obj U) by
      -- Porting note : just `convert` is very slow, so helps it a bit
      convert this using 2 <;> congr
    rw [PresheafedSpace.comp_c_app,
      ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    -- Porting note : this instance created manually to make the `inferInstance` below work
    have inst1 : IsIso (preservesColimitIso forgetToPresheafedSpace F).inv.c :=
      PresheafedSpace.c_isIso_of_iso _
    rsuffices : IsIso
        (limit.π
          (PresheafedSpace.componentwiseDiagram (F ⋙ SheafedSpace.forgetToPresheafedSpace)
            ((Opens.map
                  (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
              (unop <| op <| H.isOpenMap.functor.obj U)))
          (op i))
    · infer_instance
      -- 🎉 no goals
    apply limit_π_isIso_of_is_strict_terminal
    -- ⊢ (j : (Discrete ι)ᵒᵖ) → j ≠ op i → IsTerminal ((PresheafedSpace.componentwise …
    intro j hj
    -- ⊢ IsTerminal ((PresheafedSpace.componentwiseDiagram (F ⋙ forgetToPresheafedSpa …
    induction j using Opposite.rec' with | h j => ?_
    -- ⊢ IsTerminal ((PresheafedSpace.componentwiseDiagram (F ⋙ forgetToPresheafedSpa …
    -- ⊢ IsTerminal ((PresheafedSpace.componentwiseDiagram (F ⋙ forgetToPresheafedSpa …
    dsimp
    -- ⊢ IsTerminal ((F.obj j).presheaf.obj (op ((Opens.map (colimit.ι (F ⋙ forgetToP …
    convert (F.obj j).sheaf.isTerminalOfEmpty using 3
    -- ⊢ (Opens.map (colimit.ι (F ⋙ forgetToPresheafedSpace) j).base).obj ((Opens.map …
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U using 6
    -- ⊢ (colimit.ι (F ⋙ forgetToPresheafedSpace) i).base ≫ (preservesColimitIso forg …
    exact (congr_arg PresheafedSpace.Hom.base e).symm
    -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

noncomputable section Pullback

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_val]; rw [IsIso.hom_inv_id]
        -- ⊢ (g ≫ inv g).val = 𝟙 Y.toPresheafedSpace ∧ (inv g).val ≫ g.val = 𝟙 Z.toPreshe …
                                             -- ⊢ (𝟙 Y).val = 𝟙 Y.toPresheafedSpace ∧ (inv g).val ≫ g.val = 𝟙 Z.toPresheafedSp …
        erw [← LocallyRingedSpace.comp_val]; rw [IsIso.inv_hom_id]; constructor <;> rfl⟩⟩
        -- ⊢ (𝟙 Y).val = 𝟙 Y.toPresheafedSpace ∧ (inv g ≫ g).val = 𝟙 Z.toPresheafedSpace
                                             -- ⊢ (𝟙 Y).val = 𝟙 Y.toPresheafedSpace ∧ (𝟙 Z).val = 𝟙 Z.toPresheafedSpace
                                                                    -- ⊢ (𝟙 Y).val = 𝟙 Y.toPresheafedSpace
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso

instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.comp AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp

instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.1 by infer_instance)
                                                                             -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.mono AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono

instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullbackConeOfLeft : PullbackCone f g := by
  refine' PullbackCone.mk _
      (Y.ofRestrict (TopCat.snd_openEmbedding_of_left_openEmbedding H.base_open g.1.base)) _
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    -- ⊢ ∀ (x : ↑↑(restrict Y (_ : OpenEmbedding ↑pullback.snd)).toSheafedSpace.toPre …
    intro x
    -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (PresheafedSpace.IsOpenImmersion.pu …
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at this
    -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (PresheafedSpace.IsOpenImmersion.pu …
    rw [← IsIso.eq_inv_comp] at this
    -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (PresheafedSpace.IsOpenImmersion.pu …
    rw [this]
    -- ⊢ IsLocalRingHom (inv (PresheafedSpace.stalkMap f.val (↑(PresheafedSpace.IsOpe …
    infer_instance
    -- 🎉 no goals
  · exact LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition _ _)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeft

instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance
                                                                             -- 🎉 no goals

/-- The constructed `pullbackConeOfLeft` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine' ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.val s.condition))) _,
      LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst f.1 g.1 _),
      LocallyRingedSpace.Hom.ext _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 _), _⟩
    · intro x
      -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (PresheafedSpace.IsOpenImmersion.pu …
      have :=
        PresheafedSpace.stalkMap.congr_hom _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
            (PullbackCone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.Hom.val s.condition)))
          x
      change _ = _ ≫ PresheafedSpace.stalkMap s.snd.1 x at this
      -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (PresheafedSpace.IsOpenImmersion.pu …
      rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_inv_comp] at this
      -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (PresheafedSpace.IsOpenImmersion.pu …
      rw [this]
      -- ⊢ IsLocalRingHom (inv (PresheafedSpace.stalkMap (PullbackCone.snd (PresheafedS …
      infer_instance
      -- 🎉 no goals
    · intro m _ h₂
      -- ⊢ m = { val := PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift f.val g. …
      rw [← cancel_mono (pullbackConeOfLeft f g).snd]
      -- ⊢ m ≫ PullbackCone.snd (pullbackConeOfLeft f g) = { val := PresheafedSpace.IsO …
      exact h₂.trans <| LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 <|
          PullbackCone.mk s.fst.1 s.snd.1 <| congr_arg LocallyRingedSpace.Hom.val s.condition).symm
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta pullback.snd
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) WalkingCospan.right)
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  -- ⊢ IsOpenImmersion ((limit.isoLimitCone { cone := pullbackConeOfLeft f g, isLim …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  -- ⊢ IsOpenImmersion ((pullbackSymmetry g f).hom ≫ pullback.snd)
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  -- ⊢ IsOpenImmersion (limit.π (cospan f g) WalkingCospan.left ≫ f)
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_to_base_isOpenImmersion

instance forgetPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    -- ⊢ IsLimit (PullbackCone.mk (forgetToSheafedSpace.map { val := PresheafedSpace. …
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    -- ⊢ IsLimit (PullbackCone.mk (SheafedSpace.forgetToPresheafedSpace.map (forgetTo …
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1
    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    -- ⊢ IsLimit (PullbackCone.mk ((forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresh …
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1
    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_preserves_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesOpenImmersion

instance forgetToTopPreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) := by
  change PreservesLimit _ <|
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
    PresheafedSpace.forget _
  -- Porting note : was `apply (config := { instances := False }) ...`
  -- See https://github.com/leanprover/lean4/issues/2273
  have : PreservesLimit
      (cospan ((cospan f g ⋙ forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
        WalkingCospan.Hom.inl)
      ((cospan f g ⋙ forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
        WalkingCospan.Hom.inr)) (PresheafedSpace.forget CommRingCat)
  · dsimp; infer_instance
    -- ⊢ PreservesLimit (cospan f.val g.val) (PresheafedSpace.forget CommRingCat)
           -- 🎉 no goals
  have : PreservesLimit (cospan f g ⋙ forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (PresheafedSpace.forget CommRingCat)
  · apply preservesLimitOfIsoDiagram _ (diagramIsoCospan _).symm
    -- 🎉 no goals
  apply Limits.compPreservesLimit
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_Top_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToTopPreservesPullbackOfLeft

instance forgetReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfLeft

instance forgetPreservesPullbackOfRight :
    PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfRight

instance forgetToPresheafedSpacePreservesPullbackOfRight :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfRight

instance forgetReflectsPullbackOfRight :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfRight

instance forgetToPresheafedSpaceReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfLeft

instance forgetToPresheafedSpaceReflectsPullbackOfRight :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forgetToPresheafedSpace_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfRight

theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) := by
  -- Porting note : was `apply (config := { instances := False }) ...`
  -- See https://github.com/leanprover/lean4/issues/2273
  have h1 := @ReflectsIsomorphisms.reflects (F := LocallyRingedSpace.forgetToSheafedSpace) _ _ _
  -- ⊢ IsIso pullback.snd
  refine @h1 _ _ _ ?_; clear h1
  -- ⊢ IsIso (forgetToSheafedSpace.map pullback.snd)
                       -- ⊢ IsIso (forgetToSheafedSpace.map pullback.snd)
  -- Porting note : was `apply (config := { instances := False }) ...`
  -- See https://github.com/leanprover/lean4/issues/2273
  have h2 := @ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)) _ _ _
  refine @h2 _ _ _ ?_; clear h2
  -- ⊢ IsIso (SheafedSpace.forgetToPresheafedSpace.map (forgetToSheafedSpace.map pu …
                       -- ⊢ IsIso (SheafedSpace.forgetToPresheafedSpace.map (forgetToSheafedSpace.map pu …
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) f g]
  -- Porting note : was `inferInstance`
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ _ <|
    PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ H'
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  -- Porting note : added instance manually
  have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift

@[simp, reassoc]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g := by
  -- Porting note : added instance manually
  haveI := pullback_snd_isIso_of_range_subset f g H'
  -- ⊢ lift f g H' ≫ f = g
  erw [Category.assoc]; rw [IsIso.inv_comp_eq]; exact pullback.condition
  -- ⊢ inv pullback.snd ≫ pullback.fst ≫ f = g
                        -- ⊢ pullback.fst ≫ f = pullback.snd ≫ g
                                                -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_fac AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]
                          -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq

theorem lift_range (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    Set.range (lift f g H').1.base = f.1.base ⁻¹' Set.range g.1.base := by
  -- Porting note : added instance manually
  have := pullback_snd_isIso_of_range_subset f g H'
  -- ⊢ Set.range ↑(lift f g H').val.base = ↑f.val.base ⁻¹' Set.range ↑g.val.base
  dsimp only [lift]
  -- ⊢ Set.range ↑(inv pullback.snd ≫ pullback.fst).val.base = ↑f.val.base ⁻¹' Set. …
  have : _ = (pullback.fst : pullback f g ⟶ _).val.base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_val, SheafedSpace.comp_base, ← this, ← Category.assoc, coe_comp]
  -- ⊢ Set.range (↑pullback.fst ∘ ↑((inv pullback.snd).val.base ≫ (PreservesPullbac …
  rw [Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
  -- ⊢ Set.range ↑pullback.fst = ↑f.val.base ⁻¹' Set.range ↑g.val.base
  -- Porting note : change `rw` to `erw` on this lemma
  erw [TopCat.pullback_fst_range]
  -- ⊢ {x | ∃ y, ↑((forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat).map f)  …
  ext
  -- ⊢ x✝ ∈ {x | ∃ y, ↑((forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat).ma …
  constructor
  · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
    -- ⊢ x✝ ∈ ↑f.val.base ⁻¹' Set.range ↑g.val.base
                    -- 🎉 no goals
  · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
    -- ⊢ x✝ ∈ {x | ∃ y, ↑((forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat).ma …
                    -- 🎉 no goals
  · rw [← TopCat.epi_iff_surjective]
    -- ⊢ Epi ((inv pullback.snd).val.base ≫ (PreservesPullback.iso (forgetToSheafedSp …
    rw [show (inv (pullback.snd : pullback f g ⟶ _)).val.base = _ from
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance
    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_range AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_range

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
noncomputable def isoRestrict {X Y : LocallyRingedSpace} {f : X ⟶ Y}
    (H : LocallyRingedSpace.IsOpenImmersion f) :
    X ≅ Y.restrict H.base_open := by
  apply LocallyRingedSpace.isoOfSheafedSpaceIso
  -- ⊢ X.toSheafedSpace ≅ (restrict Y (_ : OpenEmbedding ↑f.val.base)).toSheafedSpace
  refine' SheafedSpace.forgetToPresheafedSpace.preimageIso _
  -- ⊢ SheafedSpace.forgetToPresheafedSpace.obj X.toSheafedSpace ≅ SheafedSpace.for …
  exact PresheafedSpace.IsOpenImmersion.isoRestrict H
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict

end LocallyRingedSpace.IsOpenImmersion

end AlgebraicGeometry
