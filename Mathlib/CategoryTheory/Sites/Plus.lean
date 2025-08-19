/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Sheaf

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

universe w' w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w} [Category.{w'} D]

noncomputable section

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable (P : Cᵒᵖ ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : (J.Cover X)ᵒᵖ ⥤ D where
  obj S := multiequalizer (S.unop.index P)
  map {S _} f :=
    Multiequalizer.lift _ _ (fun I ↦ Multiequalizer.ι (S.unop.index P) (I.map f.unop))
      (fun I ↦ Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' (I.r.map f.unop)))

/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
def diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X where
  app S :=
    Multiequalizer.lift _ _ (fun I ↦ Multiequalizer.ι (S.unop.index P) I.base) fun I ↦
      Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' I.r.base)
  naturality S T f := Multiequalizer.hom_ext _ _ _ (fun I ↦ by simp; rfl)

/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
def diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X where
  app W :=
    Multiequalizer.lift _ _ (fun _ ↦ Multiequalizer.ι _ _ ≫ η.app _) (fun i ↦ by
      dsimp only
      erw [Category.assoc, Category.assoc, ← η.naturality, ← η.naturality,
        Multiequalizer.condition_assoc]
      rfl)

@[simp]
theorem diagramNatTrans_id (X : C) (P : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X) := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i ↦ ?_)
  simp

@[simp]
theorem diagramNatTrans_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (0 : P ⟶ Q) X = 0 := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i ↦ ?_)
  simp

@[simp]
theorem diagramNatTrans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
    J.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i ↦ ?_)
  simp

variable (D) in
/-- `J.diagram P`, as a functor in `P`. -/
@[simps]
def diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.Cover X)ᵒᵖ ⥤ D where
  obj P := J.diagram P X
  map η := J.diagramNatTrans η X

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plusFunctor` below for a functorial version. -/
def plusObj : Cᵒᵖ ⥤ D where
  obj X := colimit (J.diagram P X.unop)
  map f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id := by
    intro X
    refine colimit.hom_ext (fun S ↦ ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.comp_id]
    let e := S.unop.pullbackId
    dsimp only [Functor.op, pullback_obj]
    rw [← colimit.w _ e.inv.op, ← Category.assoc]
    convert Category.id_comp (colimit.ι (diagram J P (unop X)) S)
    refine Multiequalizer.hom_ext _ _ _ (fun I ↦ ?_)
    dsimp
    simp only [Multiequalizer.lift_ι, Category.id_comp, Category.assoc]
    dsimp [Cover.Arrow.map, Cover.Arrow.base]
    cases I
    congr
    simp
  map_comp := by
    intro X Y Z f g
    refine colimit.hom_ext (fun S ↦ ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colimMap_assoc,
      Category.assoc]
    let e := S.unop.pullbackComp g.unop f.unop
    dsimp only [Functor.op, pullback_obj]
    rw [← colimit.w _ e.inv.op, ← Category.assoc, ← Category.assoc]
    congr 1
    refine Multiequalizer.hom_ext _ _ _ (fun I ↦ ?_)
    dsimp
    simp only [Multiequalizer.lift_ι, Category.assoc]
    cases I
    dsimp only [Cover.Arrow.base, Cover.Arrow.map]
    congr 2
    simp

/-- An auxiliary definition used in `plus` below. -/
def plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q where
  app X := colimMap (J.diagramNatTrans η X.unop)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    ext
    simp only [diagramPullback_app, ι_colimMap, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colimMap_assoc, Category.assoc]
    simp_rw [← Category.assoc]
    congr 1
    exact Multiequalizer.hom_ext _ _ _ (fun I ↦ by simp)

@[simp]
theorem plusMap_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _ := by
  ext : 2
  dsimp only [plusMap, plusObj]
  rw [J.diagramNatTrans_id, NatTrans.id_app]
  ext
  simp

@[simp]
theorem plusMap_zero [Preadditive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0 := by
  ext : 2
  refine colimit.hom_ext (fun S ↦ ?_)
  erw [comp_zero, colimit.ι_map, J.diagramNatTrans_zero, zero_comp]

@[simp, reassoc]
theorem plusMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ := by
  ext : 2
  refine colimit.hom_ext (fun S ↦ ?_)
  simp [plusMap, J.diagramNatTrans_comp]

variable (D) in
/-- The plus construction, a functor sending `P` to `J.plusObj P`. -/
@[simps]
def plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  obj P := J.plusObj P
  map η := J.plusMap η

/-- The canonical map from `P` to `J.plusObj P`.
See `toPlusNatTrans` for a functorial version. -/
def toPlus : P ⟶ J.plusObj P where
  app X := Cover.toMultiequalizer (⊤ : J.Cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    delta Cover.toMultiequalizer
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.assoc]
    dsimp only [Functor.op, unop_op]
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := homOfLE (OrderTop.le_top _)
    rw [← colimit.w _ e.op, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    refine Multiequalizer.hom_ext _ _ _ (fun I ↦ ?_)
    simp only [Category.assoc]
    dsimp [Cover.Arrow.base]
    simp

@[reassoc (attr := simp)]
theorem toPlus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η := by
  ext
  dsimp [toPlus, plusMap]
  delta Cover.toMultiequalizer
  simp only [ι_colimMap, Category.assoc]
  simp_rw [← Category.assoc]
  congr 1
  exact Multiequalizer.hom_ext _ _ _ (fun I ↦ by simp)

variable (D) in
/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  app P := J.toPlus P

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
theorem plusMap_toPlus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) := by
  ext X : 2
  refine colimit.hom_ext (fun S ↦ ?_)
  dsimp only [plusMap, toPlus]
  let e : S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [ι_colimMap, ← colimit.w _ e.op, ← Category.assoc, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun I ↦ ?_)
  erw [Multiequalizer.lift_ι]
  simp only [unop_op, op_unop, diagram_map, Category.assoc, limit.lift_π,
    Multifork.ofι_π_app]
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  erw [← colimit.w _ ee.op, ι_colimMap_assoc, colimit.ι_pre, diagramPullback_app,
    ← Category.assoc, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun II ↦ ?_)
  convert Multiequalizer.condition (S.unop.index P)
    { fst := I, snd := II.base, r.Z := II.Y, r.g₁ := II.f, r.g₂ := 𝟙 II.Y } using 1
  all_goals simp

theorem isIso_toPlus_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer] at hP
  suffices ∀ X, IsIso ((J.toPlus P).app X) from NatIso.isIso_of_isIso_app _
  intro X
  refine IsIso.comp_isIso' inferInstance ?_
  suffices ∀ (S T : (J.Cover X.unop)ᵒᵖ) (f : S ⟶ T), IsIso ((J.diagram P X.unop).map f) from
    isIso_ι_of_isInitial (initialOpOfTerminal isTerminalTop) _
  intro S T e
  have : S.unop.toMultiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.toMultiequalizer P :=
    Multiequalizer.hom_ext _ _ _ (fun II ↦ by simp)
  have :
    (J.diagram P X.unop).map e = inv (S.unop.toMultiequalizer P) ≫ T.unop.toMultiequalizer P := by
    simp [← this]
  rw [this]
  infer_instance

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P :=
  letI := isIso_toPlus_of_isSheaf J P hP
  asIso (J.toPlus P)

@[simp]
theorem isoToPlus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).hom = J.toPlus P :=
  rfl

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusObj P ⟶ Q :=
  J.plusMap η ≫ (J.isoToPlus Q hQ).inv

@[reassoc (attr := simp)]
theorem toPlus_plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η := by
  dsimp [plusLift]
  rw [← Category.assoc]
  rw [Iso.comp_inv_eq]
  dsimp only [isoToPlus, asIso]
  rw [toPlus_naturality]

theorem plusLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.plusObj P ⟶ Q) (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ := by
  dsimp only [plusLift]
  rw [Iso.eq_comp_inv, ← hγ, plusMap_comp]
  simp

theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ := by
  have : γ = J.plusLift (J.toPlus P ≫ γ) hQ := by
    apply plusLift_unique
    rfl
  rw [this]
  apply plusLift_unique
  exact h

@[simp]
theorem isoToPlus_inv (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).inv = J.plusLift (𝟙 _) hP := by
  apply J.plusLift_unique
  rw [Iso.comp_inv_eq, Category.id_comp]
  rfl

@[simp]
theorem plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR := by
  apply J.plusLift_unique
  rw [← Category.assoc, ← J.toPlus_naturality, Category.assoc, J.toPlus_plusLift]

instance plusFunctor_preservesZeroMorphisms [Preadditive D] :
    (plusFunctor J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext
    dsimp
    rw [J.plusMap_zero, NatTrans.app_zero]

end

end CategoryTheory.GrothendieckTopology
