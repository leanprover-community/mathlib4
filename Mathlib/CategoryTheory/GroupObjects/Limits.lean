import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.GroupObjects.FunctorCategory
import Mathlib.CategoryTheory.GroupObjects.PreservesFiniteProducts
import Mathlib.CategoryTheory.GroupObjects.Bicategory
import Mathlib.CategoryTheory.Bicategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Tactic.CategoryTheory.BicategoryCoherence

universe u v u' v' u'' v''

open CategoryTheory Limits

noncomputable section

variable {C : Type u} [Category.{v, u} C] [HasFiniteProducts C]

variable {J : Type u'} [Category.{v',u'} J] [HasLimitsOfShape J C]

variable {K : Type u''} [Category.{v'', u''} K] [HasLimitsOfShape K C]

namespace CategoryTheory.Limits

@[simp]
def limPreservesLimitsOfShape_lift (F : K ⥤ (J ⥤ C)) {c : Cone F} (limc : IsLimit c)
    (d : Cone (F ⋙ lim)) : d.pt ⟶ (lim.mapCone c).pt := by
  simp only [Functor.mapCone_pt, lim_obj]
  refine (limit.isLimit c.pt).lift {pt := d.pt, π := ?_}
  refine limc.lift {pt := (Functor.const J).obj d.pt, π := ⟨?_, ?_⟩}
  · refine fun k ↦ {app := fun j ↦ d.π.app k ≫ limit.π (F.obj k) j, naturality := ?_}
    · intro j j' u
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj, lim_obj,
        Category.id_comp, Category.assoc, limit.w]
  · intro k k' u
    ext j
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj, lim_obj,
      Category.id_comp, NatTrans.comp_app, Category.assoc]
    have := d.π.naturality u
    simp only [Functor.const_obj_obj, Functor.comp_obj, lim_obj, Functor.const_obj_map,
      Category.id_comp, Functor.comp_map, lim_map] at this
    rw [this]
    simp only [Category.assoc, limMap_π]

lemma limPreservesLimitsOfShape_fac (F : K ⥤ (J ⥤ C)) {c : Cone F} (limc : IsLimit c)
    (d : Cone (F ⋙ lim)) (k : K) :
    limPreservesLimitsOfShape_lift F limc d ≫ (lim.mapCone c).π.app k = d.π.app k := by
  refine limit.hom_ext ?_
  intro j
  simp only [Functor.mapCone_pt, lim_obj, Functor.comp_obj, limPreservesLimitsOfShape_lift,
    Functor.const_obj_obj, limit.isLimit_lift, id_eq, Functor.mapCone_π_app, lim_map,
    limit.lift_map, limit.lift_π, Cones.postcompose_obj_pt, Cones.postcompose_obj_π, IsLimit.fac]

lemma limPreservesLimitsOfShape_uniq (F : K ⥤ (J ⥤ C)) {c : Cone F} (limc : IsLimit c)
    (d : Cone (F ⋙ lim)) (u : d.pt ⟶ (lim.mapCone c).pt)
    (eq : ∀ (k : K), u ≫(lim.mapCone c).π.app k = d.π.app k) :
    u = limPreservesLimitsOfShape_lift F limc d := by
  simp only [Functor.mapCone_pt, lim_obj] at u
  refine limit.hom_ext ?_
  intro j
  simp only [limPreservesLimitsOfShape_lift, Functor.mapCone_pt, lim_obj, Functor.const_obj_obj,
    Functor.comp_obj, limit.isLimit_lift, id_eq, limit.lift_π]
  set e := preservesLimitIso ((evaluation J C).obj j) F with edef
  simp only [evaluation_obj_obj] at e
  set f := IsLimit.conePointUniqueUpToIso limc (limit.isLimit F) with fdef
  simp only [limit.cone_x] at f
  refine Mono.right_cancellation (f := ((f.app j).trans e).hom) _ _ (limit.hom_ext ?_)
  intro k
  simp only [Functor.comp_obj, evaluation_obj_obj, fdef, edef, Iso.trans_hom, Iso.app_hom,
    Category.assoc, preservesLimitsIso_hom_π, evaluation_obj_map]
  simp only [Functor.comp_obj, lim_obj, Functor.mapCone_pt, Functor.mapCone_π_app, lim_map] at eq
  rw [← NatTrans.comp_app]
  erw [IsLimit.conePointUniqueUpToIso_hom_comp, ← limMap_π (c.π.app k) j]
  rw [← Category.assoc, eq k, ← NatTrans.comp_app, limc.fac]

variable (C J K)

def limPreservesLimitsOfShape : PreservesLimitsOfShape K (lim : (J ⥤ C) ⥤ C) where
  preservesLimit := by
    intro F
    refine {preserves := ?_}
    intro c limc
    exact
    {
     lift := limPreservesLimitsOfShape_lift F limc
     fac := limPreservesLimitsOfShape_fac F limc
     uniq := limPreservesLimitsOfShape_uniq F limc
    }

/-- If `C` has finite products and limits of shape `J`, then the functor `lim` from `J ⥤ C`
to `C` preserves finite products.-/
def limPreservesFiniteProducts : PreservesFiniteProducts (lim : (J ⥤ C) ⥤ C) where
  preserves K _ := limPreservesLimitsOfShape C J (Discrete K)

end CategoryTheory.Limits

namespace Bicategory

variable {J' : Type} [SmallCategory J'] [HasLimitsOfShape J' C]

local instance : PreservesFiniteProducts (lim : (J' ⥤ C) ⥤ C) := limPreservesFiniteProducts C J'

variable (C J')

@[simp]
abbrev FunctorsAsObj : {C : Cat // HasFiniteProducts C} :=
  ⟨Cat.of (J' ⥤ C), functorCategoryHasFiniteProducts⟩

@[simp]
abbrev CatAsObj : {C : Cat // HasFiniteProducts C} :=
  ⟨Cat.of (ULift.{max u v} C),
  { out := fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence ULift.equivalence.inverse}⟩

abbrev LimAs1Map : FunctorsAsObj C J' ⟶ CatAsObj C := by
  have : PreservesFiniteProducts (lim : (J' ⥤ C) ⥤ C) := inferInstance
  exact ⟨lim (J := J') (C := C) ⋙ ULift.equivalence.functor, Nonempty.intro
  (Limits.compPreservesFiniteProducts _ _)⟩

@[simp]
abbrev ConstAs1Map : CatAsObj C ⟶ FunctorsAsObj C J' := by
  have : PreservesFiniteProducts (Functor.const J' (C := C)) := inferInstance
  refine ⟨ULift.equivalence.inverse ⋙ Functor.const J', Nonempty.intro
  (Limits.compPreservesFiniteProducts _ _)⟩

def constLimAdj : Bicategory.Adjunction (B := {C : Cat // HasFiniteProducts C})
    (a := ⟨Cat.of (ULift.{max u v} C),
    {out := fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence ULift.equivalence.inverse}⟩)
    (b := ⟨Cat.of (J' ⥤ C), functorCategoryHasFiniteProducts⟩)
    (ConstAs1Map C J') (LimAs1Map C J') where
  unit := (Adjunction.comp ULift.equivalence.symm.toAdjunction Limits.constLimAdj).unit
  counit := (Adjunction.comp ULift.equivalence.symm.toAdjunction Limits.constLimAdj).counit
  left_triangle := by
    simp only [CatAsObj, FunctorsAsObj, ConstAs1Map,
      Bicategory.leftZigzag, Equivalence.symm_functor, Equivalence.symm_inverse]
    simp only [Mathlib.Tactic.BicategoryCoherence.bicategoricalComp,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom', Bicategory.whiskerRight_comp,
      Bicategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    simp only [Bicategory.whiskerRight, Bicategory.associator, FullSubcategory.isoOfAmbientIso,
      FunctorsAsObj, CatAsObj, Bicategory.whiskerLeft,
      Bicategory.leftUnitor, Bicategory.rightUnitor]
    simp only [Functor.associator, Functor.comp_obj, Functor.leftUnitor, Functor.rightUnitor]
    erw [Category.id_comp]
    erw [Adjunction.left_triangle (Adjunction.comp ULift.equivalence.symm.toAdjunction
      Limits.constLimAdj)]
    change (_ : NatTrans _ _) = _
    ext
    erw [NatTrans.comp_app, Category.id_comp]; rfl
  right_triangle := by
    simp only [CatAsObj, FunctorsAsObj, ConstAs1Map,
      Bicategory.rightZigzag, Equivalence.symm_functor, Equivalence.symm_inverse]
    simp only [Mathlib.Tactic.BicategoryCoherence.bicategoricalComp,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom', Bicategory.whiskerRight_comp,
      Bicategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    simp only [Bicategory.whiskerRight, Bicategory.associator, FullSubcategory.isoOfAmbientIso,
      FunctorsAsObj, CatAsObj, Bicategory.whiskerLeft,
      Bicategory.leftUnitor, Bicategory.rightUnitor]
    simp only [Functor.associator, Functor.comp_obj, Functor.leftUnitor, Functor.rightUnitor]
    erw [Category.id_comp]
    erw [Adjunction.right_triangle (Adjunction.comp ULift.equivalence.symm.toAdjunction
      Limits.constLimAdj)]
    change (_ : NatTrans _ _) = _
    ext
    erw [NatTrans.comp_app, Category.id_comp]; rfl



end Bicategory





#exit



/- Limits of group objects.-/

variable {J : Type*} [Category J] [HasLimitsOfShape J C]
  [HasLimitsOfShape (Discrete WalkingPair × J) C] [HasLimitsOfShape (J × Discrete WalkingPair) C]

example (F : J ⥤ GroupObject C) : Cone F where
  pt :=
  {
    X := limit (F ⋙ forget C)
    one := sorry
    mul := by
      set e := limitFlipCompLimIsoLimitCompLim (pair (F ⋙ forget C) (F ⋙ forget C))
      set f := HasLimit.isoOfNatIso (pairComp (F ⋙ forget C) (F ⋙ forget C)
        (lim : (J ⥤ C) ⥤ C))
      refine (f.symm.trans e.symm).hom ≫ limMap ?_
      have g : ∀ (j : J),
          (pair (F ⋙ forget C) (F ⋙ forget C)).flip.obj j ≅ pair (F.obj j).X (F.obj j).X :=
        fun _ ↦ mapPairIso (Iso.refl _) (Iso.refl _)
      exact
      {
        app := fun j ↦ (HasLimit.isoOfNatIso (g j)).hom ≫ (F.obj j).mul
        naturality := by
          intro j j' f
          simp only [Functor.comp_obj, lim_obj, forget_obj, Functor.comp_map, lim_map, forget_map,
            Category.assoc, Hom.mul_hom]
          sorry
      }
    inv := sorry
  }
  π := sorry
