/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.plus
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.Sheaf

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

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]

variable (P : Cᵒᵖ ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : (J.cover X)ᵒᵖ ⥤ D
    where
  obj S := multiequalizer (S.unop.index P)
  map S T f :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) (I.map f.unop)) fun I =>
      Multiequalizer.condition (S.unop.index P) (I.map f.unop)
  map_id' S := by
    ext I
    cases I
    simpa
  map_comp' S T W f g := by
    ext I
    simpa
#align category_theory.grothendieck_topology.diagram CategoryTheory.GrothendieckTopology.diagram

/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
def diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X
    where
  app S :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) I.base) fun I =>
      Multiequalizer.condition (S.unop.index P) I.base
  naturality' S T f := by
    ext
    dsimp
    simpa
#align category_theory.grothendieck_topology.diagram_pullback CategoryTheory.GrothendieckTopology.diagramPullback

/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
def diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X
    where
  app W :=
    Multiequalizer.lift _ _ (fun i => Multiequalizer.ι _ i ≫ η.app _)
      (by
        intro i
        erw [category.assoc, category.assoc, ← η.naturality, ← η.naturality, ← category.assoc, ←
          category.assoc, multiequalizer.condition]
        rfl)
  naturality' _ _ _ := by
    dsimp
    ext
    simpa
#align category_theory.grothendieck_topology.diagram_nat_trans CategoryTheory.GrothendieckTopology.diagramNatTrans

@[simp]
theorem diagramNatTrans_id (X : C) (P : Cᵒᵖ ⥤ D) : J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X) :=
  by
  ext
  dsimp
  simp only [multiequalizer.lift_ι, category.id_comp]
  erw [category.comp_id]
#align category_theory.grothendieck_topology.diagram_nat_trans_id CategoryTheory.GrothendieckTopology.diagramNatTrans_id

@[simp]
theorem diagramNatTrans_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (0 : P ⟶ Q) X = 0 := by
  ext (j x)
  dsimp
  rw [zero_comp, multiequalizer.lift_ι, comp_zero]
#align category_theory.grothendieck_topology.diagram_nat_trans_zero CategoryTheory.GrothendieckTopology.diagramNatTrans_zero

@[simp]
theorem diagramNatTrans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
    J.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X :=
  by
  ext
  dsimp
  simp
#align category_theory.grothendieck_topology.diagram_nat_trans_comp CategoryTheory.GrothendieckTopology.diagramNatTrans_comp

variable (D)

/-- `J.diagram P`, as a functor in `P`. -/
@[simps]
def diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.cover X)ᵒᵖ ⥤ D
    where
  obj P := J.diagram P X
  map P Q η := J.diagramNatTrans η X
  map_id' P := J.diagramNatTrans_id _ _
  map_comp' P Q R η γ := J.diagramNatTrans_comp _ _ _
#align category_theory.grothendieck_topology.diagram_functor CategoryTheory.GrothendieckTopology.diagramFunctor

variable {D}

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plus_functor` below for a functorial version. -/
def plusObj : Cᵒᵖ ⥤ D where
  obj X := colimit (J.diagram P X.unop)
  map X Y f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id' := by
    intro X
    ext S
    dsimp
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.comp_id]
    let e := S.unop.pullback_id
    dsimp only [functor.op, pullback_obj]
    erw [← colimit.w _ e.inv.op, ← category.assoc]
    convert category.id_comp _
    ext I
    dsimp
    simp only [multiequalizer.lift_ι, category.id_comp, category.assoc]
    dsimp [cover.arrow.map, cover.arrow.base]
    cases I
    congr
    simp
  map_comp' := by
    intro X Y Z f g
    ext S
    dsimp
    simp only [diagram_pullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc,
      category.assoc]
    let e := S.unop.pullback_comp g.unop f.unop
    dsimp only [functor.op, pullback_obj]
    erw [← colimit.w _ e.inv.op, ← category.assoc, ← category.assoc]
    congr 1
    ext I
    dsimp
    simp only [multiequalizer.lift_ι, category.assoc]
    cases I
    dsimp only [cover.arrow.base, cover.arrow.map]
    congr 2
    simp
#align category_theory.grothendieck_topology.plus_obj CategoryTheory.GrothendieckTopology.plusObj

/-- An auxiliary definition used in `plus` below. -/
def plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q
    where
  app X := colimMap (J.diagramNatTrans η X.unop)
  naturality' := by
    intro X Y f
    dsimp [plus_obj]
    ext
    simp only [diagram_pullback_app, ι_colim_map, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colim_map_assoc, category.assoc]
    simp_rw [← category.assoc]
    congr 1
    ext
    dsimp
    simpa
#align category_theory.grothendieck_topology.plus_map CategoryTheory.GrothendieckTopology.plusMap

@[simp]
theorem plusMap_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _ :=
  by
  ext x : 2
  dsimp only [plus_map, plus_obj]
  rw [J.diagram_nat_trans_id, nat_trans.id_app]
  ext
  dsimp
  simp
#align category_theory.grothendieck_topology.plus_map_id CategoryTheory.GrothendieckTopology.plusMap_id

@[simp]
theorem plusMap_zero [Preadditive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0 :=
  by
  ext
  erw [comp_zero, colimit.ι_map, J.diagram_nat_trans_zero, zero_comp]
#align category_theory.grothendieck_topology.plus_map_zero CategoryTheory.GrothendieckTopology.plusMap_zero

@[simp]
theorem plusMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ :=
  by
  ext : 2
  dsimp only [plus_map]
  rw [J.diagram_nat_trans_comp]
  ext
  dsimp
  simp
#align category_theory.grothendieck_topology.plus_map_comp CategoryTheory.GrothendieckTopology.plusMap_comp

variable (D)

/-- The plus construction, a functor sending `P` to `J.plus_obj P`. -/
@[simps]
def plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
    where
  obj P := J.plusObj P
  map P Q η := J.plusMap η
  map_id' _ := plusMap_id _ _
  map_comp' _ _ _ _ _ := plusMap_comp _ _ _
#align category_theory.grothendieck_topology.plus_functor CategoryTheory.GrothendieckTopology.plusFunctor

variable {D}

/-- The canonical map from `P` to `J.plus.obj P`.
See `to_plus` for a functorial version. -/
def toPlus : P ⟶ J.plusObj P
    where
  app X := Cover.toMultiequalizer (⊤ : J.cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality' := by
    intro X Y f
    dsimp [plus_obj]
    delta cover.to_multiequalizer
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.assoc]
    dsimp only [functor.op, unop_op]
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
    rw [← colimit.w _ e.op, ← category.assoc, ← category.assoc, ← category.assoc]
    congr 1
    ext
    dsimp
    simp only [multiequalizer.lift_ι, category.assoc]
    dsimp [cover.arrow.base]
    simp
#align category_theory.grothendieck_topology.to_plus CategoryTheory.GrothendieckTopology.toPlus

@[simp, reassoc.1]
theorem toPlus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η :=
  by
  ext
  dsimp [to_plus, plus_map]
  delta cover.to_multiequalizer
  simp only [ι_colim_map, category.assoc]
  simp_rw [← category.assoc]
  congr 1
  ext
  dsimp
  simp
#align category_theory.grothendieck_topology.to_plus_naturality CategoryTheory.GrothendieckTopology.toPlus_naturality

variable (D)

/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D
    where
  app P := J.toPlus P
  naturality' _ _ _ := toPlus_naturality _ _
#align category_theory.grothendieck_topology.to_plus_nat_trans CategoryTheory.GrothendieckTopology.toPlusNatTrans

variable {D}

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
theorem plusMap_toPlus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) :=
  by
  ext (X S)
  dsimp [to_plus, plus_obj, plus_map]
  delta cover.to_multiequalizer
  simp only [ι_colim_map]
  let e : S.unop ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
  simp_rw [← colimit.w _ e.op, ← category.assoc]
  congr 1
  ext I
  dsimp
  simp only [diagram_pullback_app, colimit.ι_pre, multiequalizer.lift_ι, ι_colim_map_assoc,
    category.assoc]
  dsimp only [functor.op]
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
  simp_rw [← colimit.w _ ee.op, ← category.assoc]
  congr 1
  ext II
  dsimp
  simp only [limit.lift_π, multifork.of_ι_π_app, multiequalizer.lift_ι, category.assoc]
  dsimp [multifork.of_ι]
  convert multiequalizer.condition (S.unop.index P)
      ⟨_, _, _, II.f, 𝟙 _, I.f, II.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _, by simp⟩
  · cases I
    rfl
  · dsimp [cover.index]
    erw [P.map_id, category.comp_id]
    rfl
#align category_theory.grothendieck_topology.plus_map_to_plus CategoryTheory.GrothendieckTopology.plusMap_toPlus

theorem isIso_toPlus_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) :=
  by
  rw [presheaf.is_sheaf_iff_multiequalizer] at hP
  rsuffices : ∀ X, is_iso ((J.to_plus P).app X)
  · apply nat_iso.is_iso_of_is_iso_app
  intro X
  dsimp
  rsuffices : is_iso (colimit.ι (J.diagram P X.unop) (op ⊤))
  · apply is_iso.comp_is_iso
  rsuffices : ∀ (S T : (J.cover X.unop)ᵒᵖ) (f : S ⟶ T), is_iso ((J.diagram P X.unop).map f)
  · apply is_iso_ι_of_is_initial (initial_op_of_terminal is_terminal_top)
  intro S T e
  have : S.unop.to_multiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.to_multiequalizer P :=
    by
    ext
    dsimp
    simpa
  have :
    (J.diagram P X.unop).map e = inv (S.unop.to_multiequalizer P) ≫ T.unop.to_multiequalizer P := by
    simp [← this]
  rw [this]
  infer_instance
#align category_theory.grothendieck_topology.is_iso_to_plus_of_is_sheaf CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P :=
  letI := is_iso_to_plus_of_is_sheaf J P hP
  as_iso (J.to_plus P)
#align category_theory.grothendieck_topology.iso_to_plus CategoryTheory.GrothendieckTopology.isoToPlus

@[simp]
theorem isoToPlus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).Hom = J.toPlus P :=
  rfl
#align category_theory.grothendieck_topology.iso_to_plus_hom CategoryTheory.GrothendieckTopology.isoToPlus_hom

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusObj P ⟶ Q :=
  J.plusMap η ≫ (J.isoToPlus Q hQ).inv
#align category_theory.grothendieck_topology.plus_lift CategoryTheory.GrothendieckTopology.plusLift

@[simp, reassoc.1]
theorem toPlus_plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η := by
  dsimp [plus_lift]
  rw [← category.assoc]
  rw [iso.comp_inv_eq]
  dsimp only [iso_to_plus, as_iso]
  rw [to_plus_naturality]
#align category_theory.grothendieck_topology.to_plus_plus_lift CategoryTheory.GrothendieckTopology.toPlus_plusLift

theorem plusLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.plusObj P ⟶ Q) (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ :=
  by
  dsimp only [plus_lift]
  rw [iso.eq_comp_inv, ← hγ, plus_map_comp]
  dsimp
  simp
#align category_theory.grothendieck_topology.plus_lift_unique CategoryTheory.GrothendieckTopology.plusLift_unique

theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ :=
  by
  have : γ = J.plus_lift (J.to_plus P ≫ γ) hQ :=
    by
    apply plus_lift_unique
    rfl
  rw [this]
  apply plus_lift_unique
  exact h
#align category_theory.grothendieck_topology.plus_hom_ext CategoryTheory.GrothendieckTopology.plus_hom_ext

@[simp]
theorem isoToPlus_inv (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).inv = J.plusLift (𝟙 _) hP :=
  by
  apply J.plus_lift_unique
  rw [iso.comp_inv_eq, category.id_comp]
  rfl
#align category_theory.grothendieck_topology.iso_to_plus_inv CategoryTheory.GrothendieckTopology.isoToPlus_inv

@[simp]
theorem plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR :=
  by
  apply J.plus_lift_unique
  rw [← category.assoc, ← J.to_plus_naturality, category.assoc, J.to_plus_plus_lift]
#align category_theory.grothendieck_topology.plus_map_plus_lift CategoryTheory.GrothendieckTopology.plusMap_plusLift

instance plusFunctor_preservesZeroMorphisms [Preadditive D] :
    (plusFunctor J D).PreservesZeroMorphisms
    where map_zero' F G := by
    ext
    dsimp
    rw [J.plus_map_zero, nat_trans.app_zero]
#align category_theory.grothendieck_topology.plus_functor_preserves_zero_morphisms CategoryTheory.GrothendieckTopology.plusFunctor_preservesZeroMorphisms

end CategoryTheory.GrothendieckTopology

