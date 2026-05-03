/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Subfunctor.Sieves
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# ???

-/

@[expose] public section

universe w t v v' v'' u u' u''

open AlgebraicTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

open Opposite Limits

-- to be moved
noncomputable def isTerminalShrinkYonedaObj [LocallySmall.{w} C]
    {T : C} (hT : IsTerminal T) :
    IsTerminal (shrinkYoneda.{w}.obj T) :=
  Functor.isTerminal (fun _ ↦ (Types.isTerminalEquivUnique _).2
    { default := shrinkYonedaObjObjEquiv.symm (hT.from _)
      uniq _ := shrinkYonedaObjObjEquiv.injective (hT.hom_ext _ _)})

namespace Subfunctor

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {ι : Type*} (U : ι → C)

set_option backward.isDefEq.respectTransparency false in
-- to be moved
def ofObjectsIsoOfAdj :
    F.op ⋙ (ofObjects U).toFunctor ≅
      (ofObjects (G.obj ∘ U)).toFunctor :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso ((Equiv.refl _).subtypeEquiv (fun _ ↦ by
    simp only [Functor.op_obj, Functor.const_obj_obj, ofObjects, Set.mem_setOf_eq,
      Function.comp_apply, Equiv.refl_apply]
    constructor
    · rintro ⟨i, ⟨f⟩⟩
      exact ⟨i, ⟨adj.homEquiv _ _ f⟩⟩
    · rintro ⟨i, ⟨f⟩⟩
      exact ⟨i, ⟨(adj.homEquiv _ _).symm f⟩⟩))) (fun _ ↦ rfl)

end Subfunctor

namespace Adjunction

variable [LocallySmall.{w} C] [LocallySmall.{w} D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
noncomputable def shrinkYonedaIso :
    (shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj F.op) ≅
      G ⋙ shrinkYoneda.{w} :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ Equiv.toIso (
        shrinkYonedaObjObjEquiv.trans ((adj.homEquiv Y.unop X).trans
          shrinkYonedaObjObjEquiv.symm))) (fun f ↦ by
            ext g
            obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
            dsimp
            rw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm,
              shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm]
            simp [adj.homEquiv_naturality_left])) (fun f ↦ by
            ext _ g
            obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
            dsimp
            rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm,
              shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm,
              Equiv.apply_symm_apply, Equiv.apply_symm_apply,
              adj.homEquiv_naturality_right])

end Adjunction

namespace Limits.FormalCoproduct

variable {E : Type u''} [Category.{v''} E]

set_option backward.isDefEq.respectTransparency false in
noncomputable def evalObjCompIso [HasCoproducts.{w} D] [HasCoproducts.{w} E] (F : C ⥤ D)
    (G : D ⥤ E)
    [∀ (α : Type w), PreservesColimitsOfShape (Discrete α) G] :
    (eval.{w} C E).obj (F ⋙ G) ≅
      (eval.{w} C D).obj F ⋙ G :=
  NatIso.ofComponents (fun _ ↦ (PreservesCoproduct.iso G _).symm) (fun {U V} f ↦ by
    dsimp
    ext i
    simpa [-ι_comp_sigmaComparison] using
      G.map (F.map (f.φ i)) ≫= ι_comp_sigmaComparison G (fun i ↦ F.obj (V.obj i)) (f.f i))

variable [LocallySmall.{w} C] [LocallySmall.{w} D]

open Functor

section

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)

noncomputable def evalShrinkYonedaCompIsoOfAdj :
    (eval C _).obj shrinkYoneda.{w} ⋙ (whiskeringLeft _ _ _).obj F.op ≅
      G.mapFormalCoproduct ⋙ (eval _ _).obj shrinkYoneda :=
  (evalObjCompIso _ _).symm ≪≫ (eval C _).mapIso adj.shrinkYonedaIso

end

variable (U : FormalCoproduct.{w} C)

@[simps!]
noncomputable def mapFormalCoproductObjPowerIso
    (G : C ⥤ D) (α : Type t) [HasProductsOfShape α C]
    [HasProductsOfShape α D] [PreservesLimitsOfShape (Discrete α) G] :
    G.mapFormalCoproduct.obj (U.power α) ≅
      (G.mapFormalCoproduct.obj U).power α :=
  FormalCoproduct.isoOfComponents (Equiv.refl _)
    (fun _ ↦ PreservesProduct.iso _ _)

set_option backward.isDefEq.respectTransparency false in
noncomputable def cechCompMapFormalCoproductIso
    [HasFiniteProducts C] [HasFiniteProducts D] (G : C ⥤ D)
    [PreservesFiniteProducts G] :
    U.cech ⋙ G.mapFormalCoproduct ≅ (G.mapFormalCoproduct.obj U).cech :=
  NatIso.ofComponents (fun _ ↦ mapFormalCoproductObjPowerIso _ _ _) (fun f ↦ by
    ext g
    · dsimp
    · dsimp
      ext i
      simp only [map_lift_piComparison, Function.comp_apply, Category.comp_id,
        Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
      exact (Pi.lift_π ..).trans (piComparison_comp_π _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The augmented simplicial Cech presheaf of types attached to `U : FormalCoproduct.{w} C`,
the target of the augmentation is the subfunctor of the constant functor `Cᵒᵖ ⥤ Type w`
with value `PUnit` that is generated by the objects `U.obj`. -/
noncomputable def shrinkYonedaCech [HasFiniteProducts C] :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w) where
  left := ((SimplicialObject.whiskering _ _).obj
      ((FormalCoproduct.eval C _).obj shrinkYoneda)).obj U.cech
  right := (Subfunctor.ofObjects.{w} U.obj).toFunctor
  hom :=
    { app n :=
      { app V v := ⟨.unit, by
          obtain ⟨⟨i⟩, v, rfl⟩ := Types.jointly_surjective_of_isColimit
            (isColimitOfPreserves ((evaluation _ _).obj V) (coproductIsCoproduct _)) v
          let φ : Opposite.unop V ⟶ U.obj (i 0) :=
            shrinkYonedaObjObjEquiv v ≫ Pi.π _ 0
          simp [Subfunctor.ofObjects_obj_eq_univ φ]⟩ } }

set_option backward.isDefEq.respectTransparency false in
lemma isEmpty_shrinkYonedaCechRightObj [HasFiniteProducts C]
    (X : Cᵒᵖ) (hX : ∀ (i : U.I), IsEmpty (X.unop ⟶ U.obj i)) :
    IsEmpty (U.shrinkYonedaCech.right.obj X) := by
  simp [shrinkYonedaCech, Subfunctor.ofObjects_obj_eq_empty]

set_option backward.isDefEq.respectTransparency false in
noncomputable def extraDegeneracyShrinkYonedaCech
    [HasFiniteProducts C] {T : C} {i : U.I} (f : T ⟶ U.obj i) (hT : IsTerminal T) :
    U.shrinkYonedaCech.ExtraDegeneracy := by
  refine .ofIso ?_ ((U.extraDegeneracyCech hT f).map
    ((FormalCoproduct.eval C _).obj shrinkYoneda))
  refine Comma.isoMk (Iso.refl _)
    (IsTerminal.uniqueUpToIso ?_
      (Subfunctor.isTerminalOfObjectsToFunctor _ f hT)) ?_
  · exact IsTerminal.ofIso (isTerminalShrinkYonedaObj hT)
      { hom := Sigma.ι (fun _ ↦ _) PUnit.unit
        inv := Sigma.desc (fun _ ↦ 𝟙 _) }
  · ext : 1
    apply (Subfunctor.isTerminalOfObjectsToFunctor _ f hT).hom_ext

section

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [HasFiniteProducts C]
  [HasFiniteProducts D]

noncomputable def shrinkYonedaCechIsoOfAdj :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      ((whiskeringLeft _ _ _).obj F.op)).obj U.shrinkYonedaCech ≅
    (G.mapFormalCoproduct.obj U).shrinkYonedaCech :=
  haveI := adj.isRightAdjoint
  Comma.isoMk ((whiskeringRightObjCompIso _ _).app _ ≪≫
      isoWhiskerLeft _
        (FormalCoproduct.evalShrinkYonedaCompIsoOfAdj adj) ≪≫
        (associator _ _ _).symm ≪≫
      isoWhiskerRight (U.cechCompMapFormalCoproductIso G) _)
    (Subfunctor.ofObjectsIsoOfAdj adj _) rfl

end

variable [HasFiniteLimits C]

set_option backward.isDefEq.respectTransparency false in
instance nonempty_extraDegeneracy_shrinkYonedaCech_evaluation (X : Cᵒᵖ) :
    Nonempty (((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation _ _).obj X)).obj U.shrinkYonedaCech).ExtraDegeneracy := by
  by_cases hX : ∃ i, Nonempty (X.unop ⟶ U.obj i)
  · obtain ⟨i, ⟨f⟩⟩ := hX
    exact ⟨.ofIso (((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation _ _).obj (op (Over.mk (𝟙 _))))).mapIso
        (U.shrinkYonedaCechIsoOfAdj (Over.forgetAdjStar X.unop))).symm
          (SimplicialObject.Augmented.ExtraDegeneracy.map
            (extraDegeneracyShrinkYonedaCech _ (Over.homMk (prod.lift (𝟙 _) f))
              Over.mkIdTerminal) _)⟩
  · have := U.isEmpty_shrinkYonedaCechRightObj X (by simpa using hX)
    exact ⟨.ofIso (Comma.isoMk (NatIso.ofComponents
      (fun n ↦ Types.isInitialPEmpty.uniqueUpToIso (Nonempty.some (by
        rw [Types.initial_iff_empty]
        exact Function.isEmpty (β := U.shrinkYonedaCech.right.obj X)
          ((U.shrinkYonedaCech.hom.app n).app X)))) (fun _ ↦ by ext ⟨⟩))
      (Types.isInitialPEmpty.uniqueUpToIso (Nonempty.some (by rwa [Types.initial_iff_empty])))
        (by ext : 1; apply Types.isInitialPEmpty.hom_ext)) (.const PEmpty.{w + 1})⟩

variable {A : Type u'} [Category.{v'} A] [∀ (α : Type w), HasColimitsOfShape (Discrete α) A]
  [Abelian A] (M : A)

set_option backward.isDefEq.respectTransparency false in
instance :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskeringObj
        ((whiskeringRight Cᵒᵖ _ _).obj (sigmaFunctor.obj M))).obj U.shrinkYonedaCech))) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro X
  obtain ⟨ed⟩ := U.nonempty_extraDegeneracy_shrinkYonedaCech_evaluation X
  refine ((HomologicalComplex.quasiIso A (.down ℕ)).arrow_mk_iso_iff ?_).1
    (ed.map (sigmaFunctor.obj M)).homotopyEquiv.quasiIso_hom
  refine NatTrans.arrowMkAppIso (AlternatingFaceMapComplex.ε) ?_ ≪≫
    (AlternatingFaceMapComplex.arrowMkεAppWhiskeringObjIso _ _).symm
  exact (SimplicialObject.Augmented.whiskeringObjCompIso ..).app _ ≪≫ by rfl ≪≫
    (SimplicialObject.Augmented.whiskeringObjCompIso ..).symm.app _

end Limits.FormalCoproduct

end CategoryTheory
