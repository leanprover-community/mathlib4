import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.GroupObjects.FunctorCategory
import Mathlib.CategoryTheory.GroupObjects.PreservesFiniteProducts

universe u v u' v' u'' v''

open CategoryTheory Limits

noncomputable section

variable {C : Type u} [Category.{v, u} C] [HasFiniteProducts C]

variable {J : Type u'} [Category.{v',u'} J] [HasLimitsOfShape J C]
  [HasLimitsOfShape (Discrete WalkingPair × J) C] [HasLimitsOfShape (J × Discrete WalkingPair) C]

variable {K : Type u''} [Category.{v'', u''} K] [HasLimitsOfShape K C]

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
  preserves J _ := by
    sorry




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
