/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Sheaf

#align_import category_theory.sites.plus from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# The plus construction for presheaves.

This file contains the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`
where `C` is endowed with a grothendieck topology `J`.

See <https://stacks.math.columbia.edu/tag/00W1> for details.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w} [Category.{max v u} D]

noncomputable section

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

variable (P : Cᵒᵖ ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : (J.Cover X)ᵒᵖ ⥤ D where
  obj S := multiequalizer (S.unop.index P)
  map {S _} f :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) (I.map f.unop)) fun I =>
      Multiequalizer.condition (S.unop.index P) (I.map f.unop)
#align category_theory.grothendieck_topology.diagram CategoryTheory.GrothendieckTopology.diagram

/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
def diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X where
  app S :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) I.base) fun I =>
      Multiequalizer.condition (S.unop.index P) I.base
  naturality S T f := Multiequalizer.hom_ext _ _ _ (fun I => by dsimp; simp; rfl)
                                                                -- ⊢ (Multiequalizer.lift (Cover.index T.unop P) (multiequalizer (Cover.index S.u …
                                                                       -- ⊢ Multiequalizer.ι (Cover.index S.unop P) (Cover.Arrow.map (Cover.Arrow.base I …
                                                                             -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_pullback CategoryTheory.GrothendieckTopology.diagramPullback

/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
def diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X where
  app W :=
    Multiequalizer.lift _ _ (fun i => Multiequalizer.ι _ _ ≫ η.app _) (fun i => by
      dsimp only
      -- ⊢ (Multiequalizer.ι (Cover.index W.unop P) (MulticospanIndex.fstTo (Cover.inde …
      erw [Category.assoc, Category.assoc, ← η.naturality, ← η.naturality,
        Multiequalizer.condition_assoc]
      rfl)
      -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_nat_trans CategoryTheory.GrothendieckTopology.diagramNatTrans

@[simp]
theorem diagramNatTrans_id (X : C) (P : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X) := by
  ext : 2
  -- ⊢ NatTrans.app (diagramNatTrans J (𝟙 P) X) x✝ = NatTrans.app (𝟙 (diagram J P X …
  refine' Multiequalizer.hom_ext _ _ _ (fun i => _)
  -- ⊢ NatTrans.app (diagramNatTrans J (𝟙 P) X) x✝ ≫ Multiequalizer.ι (Cover.index  …
  dsimp
  -- ⊢ Multiequalizer.lift (Cover.index x✝.unop P) (multiequalizer (Cover.index x✝. …
  simp only [limit.lift_π, Multifork.ofι_pt, Multifork.ofι_π_app, Category.id_comp]
  -- ⊢ Multiequalizer.ι (Cover.index x✝.unop P) i ≫ 𝟙 (P.obj (op i.Y)) = Multiequal …
  erw [Category.comp_id]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_nat_trans_id CategoryTheory.GrothendieckTopology.diagramNatTrans_id

@[simp]
theorem diagramNatTrans_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (0 : P ⟶ Q) X = 0 := by
  ext : 2
  -- ⊢ NatTrans.app (diagramNatTrans J 0 X) x✝ = NatTrans.app 0 x✝
  refine' Multiequalizer.hom_ext _ _ _ (fun i => _)
  -- ⊢ NatTrans.app (diagramNatTrans J 0 X) x✝ ≫ Multiequalizer.ι (Cover.index x✝.u …
  dsimp
  -- ⊢ Multiequalizer.lift (Cover.index x✝.unop Q) (multiequalizer (Cover.index x✝. …
  rw [zero_comp, Multiequalizer.lift_ι, comp_zero]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_nat_trans_zero CategoryTheory.GrothendieckTopology.diagramNatTrans_zero

@[simp]
theorem diagramNatTrans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
    J.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X := by
  ext : 2
  -- ⊢ NatTrans.app (diagramNatTrans J (η ≫ γ) X) x✝ = NatTrans.app (diagramNatTran …
  refine' Multiequalizer.hom_ext _ _ _ (fun i => _)
  -- ⊢ NatTrans.app (diagramNatTrans J (η ≫ γ) X) x✝ ≫ Multiequalizer.ι (Cover.inde …
  dsimp
  -- ⊢ Multiequalizer.lift (Cover.index x✝.unop R) (multiequalizer (Cover.index x✝. …
  simp
  -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_nat_trans_comp CategoryTheory.GrothendieckTopology.diagramNatTrans_comp

variable (D)

/-- `J.diagram P`, as a functor in `P`. -/
@[simps]
def diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.Cover X)ᵒᵖ ⥤ D where
  obj P := J.diagram P X
  map η := J.diagramNatTrans η X
#align category_theory.grothendieck_topology.diagram_functor CategoryTheory.GrothendieckTopology.diagramFunctor

variable {D}

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plusFunctor` below for a functorial version. -/
def plusObj : Cᵒᵖ ⥤ D where
  obj X := colimit (J.diagram P X.unop)
  map f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id := by
    intro X
    -- ⊢ { obj := fun X => colimit (diagram J P X.unop), map := fun {X Y} f => colimM …
    refine' colimit.hom_ext (fun S => _)
    -- ⊢ colimit.ι (diagram J P X.unop) S ≫ { obj := fun X => colimit (diagram J P X. …
    dsimp
    -- ⊢ colimit.ι (diagram J P X.unop) S ≫ colimMap (diagramPullback J P (𝟙 X.unop)) …
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.comp_id]
    -- ⊢ Multiequalizer.lift (Cover.index ((pullback J (𝟙 X.unop)).op.obj S).unop P)  …
    let e := S.unop.pullbackId
    -- ⊢ Multiequalizer.lift (Cover.index ((pullback J (𝟙 X.unop)).op.obj S).unop P)  …
    dsimp only [Functor.op, pullback_obj]
    -- ⊢ Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (𝟙 X.unop))).uno …
    erw [← colimit.w _ e.inv.op, ← Category.assoc]
    -- ⊢ (Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (𝟙 X.unop))).un …
    convert Category.id_comp (colimit.ι (diagram J P (unop X)) S)
    -- ⊢ Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (𝟙 X.unop))).uno …
    refine' Multiequalizer.hom_ext _ _ _ (fun I => _)
    -- ⊢ (Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (𝟙 X.unop))).un …
    dsimp
    -- ⊢ (Multiequalizer.lift (Cover.index (Cover.pullback S.unop (𝟙 X.unop)) P) (mul …
    simp only [Multiequalizer.lift_ι, Category.id_comp, Category.assoc]
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) (Cover.Arrow.base (Cover.Arrow.map I …
    dsimp [Cover.Arrow.map, Cover.Arrow.base]
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) { Y := I.Y, f := I.f ≫ 𝟙 X.unop, hf  …
    cases I
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) { Y := { Y := Y✝, f := f✝, hf := hf✝ …
    congr
    -- ⊢ { Y := Y✝, f := f✝, hf := hf✝ }.f ≫ 𝟙 X.unop = f✝
    simp
    -- 🎉 no goals
  map_comp := by
    intro X Y Z f g
    -- ⊢ { obj := fun X => colimit (diagram J P X.unop), map := fun {X Y} f => colimM …
    refine' colimit.hom_ext (fun S => _)
    -- ⊢ colimit.ι (diagram J P X.unop) S ≫ { obj := fun X => colimit (diagram J P X. …
    dsimp
    -- ⊢ colimit.ι (diagram J P X.unop) S ≫ colimMap (diagramPullback J P (g.unop ≫ f …
    simp only [diagramPullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colimMap_assoc,
      Category.assoc]
    let e := S.unop.pullbackComp g.unop f.unop
    -- ⊢ Multiequalizer.lift (Cover.index ((pullback J (g.unop ≫ f.unop)).op.obj S).u …
    dsimp only [Functor.op, pullback_obj]
    -- ⊢ Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (g.unop ≫ f.unop …
    erw [← colimit.w _ e.inv.op, ← Category.assoc, ← Category.assoc]
    -- ⊢ (Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (g.unop ≫ f.uno …
    congr 1
    -- ⊢ Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (g.unop ≫ f.unop …
    refine' Multiequalizer.hom_ext _ _ _ (fun I => _)
    -- ⊢ (Multiequalizer.lift (Cover.index (op (Cover.pullback S.unop (g.unop ≫ f.uno …
    dsimp
    -- ⊢ (Multiequalizer.lift (Cover.index (Cover.pullback S.unop (g.unop ≫ f.unop))  …
    simp only [Multiequalizer.lift_ι, Category.assoc]
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) (Cover.Arrow.base (Cover.Arrow.map I …
    cases I
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) (Cover.Arrow.base (Cover.Arrow.map { …
    dsimp only [Cover.Arrow.base, Cover.Arrow.map]
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) { Y := Y✝, f := f✝ ≫ g.unop ≫ f.unop …
    congr 2
    -- ⊢ f✝ ≫ g.unop ≫ f.unop = (f✝ ≫ g.unop) ≫ f.unop
    simp
    -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_obj CategoryTheory.GrothendieckTopology.plusObj

/-- An auxiliary definition used in `plus` below. -/
def plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q where
  app X := colimMap (J.diagramNatTrans η X.unop)
  naturality := by
    intro X Y f
    -- ⊢ (plusObj J P).map f ≫ (fun X => colimMap (diagramNatTrans J η X.unop)) Y = ( …
    dsimp [plusObj]
    -- ⊢ (colimMap (diagramPullback J P f.unop) ≫ colimit.pre (diagram J P Y.unop) (p …
    ext
    -- ⊢ colimit.ι (diagram J P X.unop) j✝ ≫ (colimMap (diagramPullback J P f.unop) ≫ …
    simp only [diagramPullback_app, ι_colimMap, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colimMap_assoc, Category.assoc]
    simp_rw [← Category.assoc]
    -- ⊢ (Multiequalizer.lift (Cover.index ((pullback J f.unop).op.obj j✝).unop P) (( …
    congr 1
    -- ⊢ Multiequalizer.lift (Cover.index ((pullback J f.unop).op.obj j✝).unop P) ((d …
    exact Multiequalizer.hom_ext _ _ _ (fun I => by dsimp; simp)
    -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_map CategoryTheory.GrothendieckTopology.plusMap

@[simp]
theorem plusMap_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _ := by
  ext : 2
  -- ⊢ NatTrans.app (plusMap J (𝟙 P)) x✝ = NatTrans.app (𝟙 (plusObj J P)) x✝
  dsimp only [plusMap, plusObj]
  -- ⊢ colimMap (diagramNatTrans J (𝟙 P) x✝.unop) = NatTrans.app (𝟙 (Functor.mk { o …
  rw [J.diagramNatTrans_id, NatTrans.id_app]
  -- ⊢ colimMap (𝟙 (diagram J P x✝.unop)) = 𝟙 ((Functor.mk { obj := fun X => colimi …
  ext
  -- ⊢ colimit.ι (diagram J P x✝.unop) j✝ ≫ colimMap (𝟙 (diagram J P x✝.unop)) = co …
  dsimp
  -- ⊢ colimit.ι (diagram J P x✝.unop) j✝ ≫ colimMap (𝟙 (diagram J P x✝.unop)) = co …
  simp
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_map_id CategoryTheory.GrothendieckTopology.plusMap_id

@[simp]
theorem plusMap_zero [Preadditive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0 := by
  ext : 2
  -- ⊢ NatTrans.app (plusMap J 0) x✝ = NatTrans.app 0 x✝
  refine' colimit.hom_ext (fun S => _)
  -- ⊢ colimit.ι (diagram J P x✝.unop) S ≫ NatTrans.app (plusMap J 0) x✝ = colimit. …
  erw [comp_zero, colimit.ι_map, J.diagramNatTrans_zero, zero_comp]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_map_zero CategoryTheory.GrothendieckTopology.plusMap_zero

@[simp]
theorem plusMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ := by
  ext : 2
  -- ⊢ NatTrans.app (plusMap J (η ≫ γ)) x✝ = NatTrans.app (plusMap J η ≫ plusMap J  …
  refine' colimit.hom_ext (fun S => _)
  -- ⊢ colimit.ι (diagram J P x✝.unop) S ≫ NatTrans.app (plusMap J (η ≫ γ)) x✝ = co …
  simp [plusMap, J.diagramNatTrans_comp]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_map_comp CategoryTheory.GrothendieckTopology.plusMap_comp

variable (D)

/-- The plus construction, a functor sending `P` to `J.plusObj P`. -/
@[simps]
def plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  obj P := J.plusObj P
  map η := J.plusMap η
#align category_theory.grothendieck_topology.plus_functor CategoryTheory.GrothendieckTopology.plusFunctor

variable {D}

/-- The canonical map from `P` to `J.plusObj P`.
See `toPlusNatTrans` for a functorial version. -/
def toPlus : P ⟶ J.plusObj P where
  app X := Cover.toMultiequalizer (⊤ : J.Cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality := by
    intro X Y f
    -- ⊢ P.map f ≫ (fun X => Cover.toMultiequalizer ⊤ P ≫ colimit.ι (diagram J P X.un …
    dsimp [plusObj]
    -- ⊢ P.map f ≫ Cover.toMultiequalizer ⊤ P ≫ colimit.ι (diagram J P Y.unop) (op ⊤) …
    delta Cover.toMultiequalizer
    -- ⊢ P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I = …
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.assoc]
    -- ⊢ P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I = …
    dsimp only [Functor.op, unop_op]
    -- ⊢ P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I = …
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := homOfLE (OrderTop.le_top _)
    -- ⊢ P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I = …
    rw [← colimit.w _ e.op, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    -- ⊢ ((P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I …
    congr 1
    -- ⊢ (P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I  …
    refine' Multiequalizer.hom_ext _ _ _ (fun I => _)
    -- ⊢ ((P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I …
    simp only [Multiequalizer.lift_ι, Category.assoc]
    -- ⊢ P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj (op Y.unop)) (fun I = …
    dsimp [Cover.Arrow.base]
    -- ⊢ P.map f ≫ Multiequalizer.lift (Cover.index ⊤ P) (P.obj Y) (fun I => P.map I. …
    simp
    -- 🎉 no goals
#align category_theory.grothendieck_topology.to_plus CategoryTheory.GrothendieckTopology.toPlus

@[reassoc (attr := simp)]
theorem toPlus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η := by
  ext
  -- ⊢ NatTrans.app (η ≫ toPlus J Q) x✝ = NatTrans.app (toPlus J P ≫ plusMap J η) x✝
  dsimp [toPlus, plusMap]
  -- ⊢ NatTrans.app η x✝ ≫ Cover.toMultiequalizer ⊤ Q ≫ colimit.ι (diagram J Q x✝.u …
  delta Cover.toMultiequalizer
  -- ⊢ NatTrans.app η x✝ ≫ Multiequalizer.lift (Cover.index ⊤ Q) (Q.obj (op x✝.unop …
  simp only [ι_colimMap, Category.assoc]
  -- ⊢ NatTrans.app η x✝ ≫ Multiequalizer.lift (Cover.index ⊤ Q) (Q.obj (op x✝.unop …
  simp_rw [← Category.assoc]
  -- ⊢ (NatTrans.app η x✝ ≫ Multiequalizer.lift (Cover.index ⊤ Q) (Q.obj (op x✝.uno …
  congr 1
  -- ⊢ NatTrans.app η x✝ ≫ Multiequalizer.lift (Cover.index ⊤ Q) (Q.obj (op x✝.unop …
  exact Multiequalizer.hom_ext _ _ _ (fun I => by dsimp; simp)
  -- 🎉 no goals
#align category_theory.grothendieck_topology.to_plus_naturality CategoryTheory.GrothendieckTopology.toPlus_naturality

variable (D)

/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  app P := J.toPlus P
#align category_theory.grothendieck_topology.to_plus_nat_trans CategoryTheory.GrothendieckTopology.toPlusNatTrans

variable {D}

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
theorem plusMap_toPlus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) := by
  ext X : 2
  -- ⊢ NatTrans.app (plusMap J (toPlus J P)) X = NatTrans.app (toPlus J (plusObj J  …
  refine' colimit.hom_ext (fun S => _)
  -- ⊢ colimit.ι (diagram J P X.unop) S ≫ NatTrans.app (plusMap J (toPlus J P)) X = …
  dsimp only [plusMap, toPlus]
  -- ⊢ colimit.ι (diagram J P X.unop) S ≫ colimMap (diagramNatTrans J (NatTrans.mk  …
  let e : S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  -- ⊢ colimit.ι (diagram J P X.unop) S ≫ colimMap (diagramNatTrans J (NatTrans.mk  …
  rw [ι_colimMap, ← colimit.w _ e.op, ← Category.assoc, ← Category.assoc]
  -- ⊢ NatTrans.app (diagramNatTrans J (NatTrans.mk fun X => Cover.toMultiequalizer …
  congr 1
  -- ⊢ NatTrans.app (diagramNatTrans J (NatTrans.mk fun X => Cover.toMultiequalizer …
  refine' Multiequalizer.hom_ext _ _ _ (fun I => _)
  -- ⊢ NatTrans.app (diagramNatTrans J (NatTrans.mk fun X => Cover.toMultiequalizer …
  erw [Multiequalizer.lift_ι]
  -- ⊢ Multiequalizer.ι (Cover.index S.unop P) I ≫ NatTrans.app (NatTrans.mk fun X  …
  simp only [unop_op, op_unop, diagram_map, Category.assoc, limit.lift_π,
    Multifork.ofι_π_app]
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  -- ⊢ Multiequalizer.ι (Cover.index S.unop P) I ≫ Cover.toMultiequalizer ⊤ P ≫ col …
  erw [← colimit.w _ ee.op, ι_colimMap_assoc, colimit.ι_pre, diagramPullback_app,
    ← Category.assoc, ← Category.assoc]
  congr 1
  -- ⊢ (Multiequalizer.ι (Cover.index S.unop P) I ≫ Cover.toMultiequalizer ⊤ P) ≫ ( …
  refine' Multiequalizer.hom_ext _ _ _ (fun II => _)
  -- ⊢ ((Multiequalizer.ι (Cover.index S.unop P) I ≫ Cover.toMultiequalizer ⊤ P) ≫  …
  convert (Multiequalizer.condition (S.unop.index P)
      ⟨_, _, _, II.f, 𝟙 _, I.f, II.f ≫ I.f, I.hf,
        Sieve.downward_closed _ I.hf _, by simp⟩) using 1
  · dsimp [diagram]
    -- ⊢ ((Multiequalizer.ι (Cover.index S.unop P) I ≫ Cover.toMultiequalizer ⊤ P) ≫  …
    cases I
    -- ⊢ ((Multiequalizer.ι (Cover.index S.unop P) { Y := Y✝, f := f✝, hf := hf✝ } ≫  …
    simp only [Category.assoc, limit.lift_π, Multifork.ofι_pt, Multifork.ofι_π_app,
      Cover.Arrow.map_Y, Cover.Arrow.map_f]
    rfl
    -- 🎉 no goals
  · erw [Multiequalizer.lift_ι]
    -- ⊢ Multiequalizer.ι (Cover.index S.unop P) (Cover.Arrow.base II) = Multiequaliz …
    dsimp [Cover.index]
    -- ⊢ Multiequalizer.ι { L := Cover.Arrow S.unop, R := Cover.Relation S.unop, fstT …
    simp only [Functor.map_id, Category.comp_id]
    -- ⊢ Multiequalizer.ι { L := Cover.Arrow S.unop, R := Cover.Relation S.unop, fstT …
    rfl
    -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_map_to_plus CategoryTheory.GrothendieckTopology.plusMap_toPlus

theorem isIso_toPlus_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer] at hP
  -- ⊢ IsIso (toPlus J P)
  suffices : ∀ X, IsIso ((J.toPlus P).app X)
  -- ⊢ IsIso (toPlus J P)
  · apply NatIso.isIso_of_isIso_app
    -- 🎉 no goals
  intro X
  -- ⊢ IsIso (NatTrans.app (toPlus J P) X)
  suffices : IsIso (colimit.ι (J.diagram P X.unop) (op ⊤))
  -- ⊢ IsIso (NatTrans.app (toPlus J P) X)
  · apply IsIso.comp_isIso
    -- 🎉 no goals
  suffices : ∀ (S T : (J.Cover X.unop)ᵒᵖ) (f : S ⟶ T), IsIso ((J.diagram P X.unop).map f)
  -- ⊢ IsIso (colimit.ι (diagram J P X.unop) (op ⊤))
  · apply isIso_ι_of_isInitial (initialOpOfTerminal isTerminalTop)
    -- 🎉 no goals
  intro S T e
  -- ⊢ IsIso ((diagram J P X.unop).map e)
  have : S.unop.toMultiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.toMultiequalizer P :=
    Multiequalizer.hom_ext _ _ _ (fun II => by dsimp; simp)
  have :
    (J.diagram P X.unop).map e = inv (S.unop.toMultiequalizer P) ≫ T.unop.toMultiequalizer P := by
    simp [← this]
  rw [this]
  -- ⊢ IsIso (inv (Cover.toMultiequalizer S.unop P) ≫ Cover.toMultiequalizer T.unop …
  infer_instance
  -- 🎉 no goals
#align category_theory.grothendieck_topology.is_iso_to_plus_of_is_sheaf CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P :=
  letI := isIso_toPlus_of_isSheaf J P hP
  asIso (J.toPlus P)
#align category_theory.grothendieck_topology.iso_to_plus CategoryTheory.GrothendieckTopology.isoToPlus

@[simp]
theorem isoToPlus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).hom = J.toPlus P :=
  rfl
#align category_theory.grothendieck_topology.iso_to_plus_hom CategoryTheory.GrothendieckTopology.isoToPlus_hom

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusObj P ⟶ Q :=
  J.plusMap η ≫ (J.isoToPlus Q hQ).inv
#align category_theory.grothendieck_topology.plus_lift CategoryTheory.GrothendieckTopology.plusLift

@[reassoc (attr := simp)]
theorem toPlus_plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η := by
  dsimp [plusLift]
  -- ⊢ toPlus J P ≫ plusMap J η ≫ (isoToPlus J Q hQ).inv = η
  rw [← Category.assoc]
  -- ⊢ (toPlus J P ≫ plusMap J η) ≫ (isoToPlus J Q hQ).inv = η
  rw [Iso.comp_inv_eq]
  -- ⊢ toPlus J P ≫ plusMap J η = η ≫ (isoToPlus J Q hQ).hom
  dsimp only [isoToPlus, asIso]
  -- ⊢ toPlus J P ≫ plusMap J η = η ≫ toPlus J Q
  rw [toPlus_naturality]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.to_plus_plus_lift CategoryTheory.GrothendieckTopology.toPlus_plusLift

theorem plusLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.plusObj P ⟶ Q) (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ := by
  dsimp only [plusLift]
  -- ⊢ γ = plusMap J η ≫ (isoToPlus J Q hQ).inv
  rw [Iso.eq_comp_inv, ← hγ, plusMap_comp]
  -- ⊢ γ ≫ (isoToPlus J Q hQ).hom = plusMap J (toPlus J P) ≫ plusMap J γ
  simp
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_lift_unique CategoryTheory.GrothendieckTopology.plusLift_unique

theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ := by
  have : γ = J.plusLift (J.toPlus P ≫ γ) hQ := by
    apply plusLift_unique
    rfl
  rw [this]
  -- ⊢ η = plusLift J (toPlus J P ≫ γ) hQ
  apply plusLift_unique
  -- ⊢ toPlus J P ≫ η = toPlus J P ≫ γ
  exact h
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_hom_ext CategoryTheory.GrothendieckTopology.plus_hom_ext

@[simp]
theorem isoToPlus_inv (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).inv = J.plusLift (𝟙 _) hP := by
  apply J.plusLift_unique
  -- ⊢ toPlus J P ≫ (isoToPlus J P hP).inv = 𝟙 P
  rw [Iso.comp_inv_eq, Category.id_comp]
  -- ⊢ toPlus J P = (isoToPlus J P hP).hom
  rfl
  -- 🎉 no goals
#align category_theory.grothendieck_topology.iso_to_plus_inv CategoryTheory.GrothendieckTopology.isoToPlus_inv

@[simp]
theorem plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR := by
  apply J.plusLift_unique
  -- ⊢ toPlus J P ≫ plusMap J η ≫ plusLift J γ hR = η ≫ γ
  rw [← Category.assoc, ← J.toPlus_naturality, Category.assoc, J.toPlus_plusLift]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_map_plus_lift CategoryTheory.GrothendieckTopology.plusMap_plusLift

instance plusFunctor_preservesZeroMorphisms [Preadditive D] :
    (plusFunctor J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext
    -- ⊢ NatTrans.app ((plusFunctor J D).map 0) x✝ = NatTrans.app 0 x✝
    dsimp
    -- ⊢ NatTrans.app (plusMap J 0) x✝ = 0
    rw [J.plusMap_zero, NatTrans.app_zero]
    -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_functor_preserves_zero_morphisms CategoryTheory.GrothendieckTopology.plusFunctor_preservesZeroMorphisms

end

end CategoryTheory.GrothendieckTopology
