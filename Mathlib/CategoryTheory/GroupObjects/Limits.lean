import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.GroupObjects.FunctorEquivalence
import Mathlib.CategoryTheory.GroupObjects.GroupObjectFunctor
--import Mathlib.CategoryTheory.GroupObjects.Bicategory
--import Mathlib.CategoryTheory.Bicategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
--import Mathlib.Tactic.CategoryTheory.BicategoryCoherence
import Mathlib.CategoryTheory.Adjunction.Unique

set_option linter.unreachableTactic false

universe u v u' v' u'' v''

open CategoryTheory Limits GroupObject

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v, u} C] [HasFiniteProducts C]
variable {J : Type u'} [Category.{v',u'} J] [HasLimitsOfShape J C]
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
  preserves K _ := limPreservesLimitsOfShape C J (Discrete K)

end CategoryTheory.Limits

namespace GroupObject

variable {C : Type u} [Category.{v, u} C] [HasFiniteProducts C]
variable {J : Type u'} [Category.{v',u'} J]
variable (F : J ⥤ GroupObject C) [HasLimit (F ⋙ forget C)]

open GroupObjectFunctor CategoryTheory.Functor

@[simp]
def candidate_cone_pt : GroupObject C where
  X := Limits.limit (F ⋙ forget C)
  one := (limit.isLimit (F ⋙ forget C)).lift
    {pt := ⊤_ C, π := {app := fun j ↦ (F.obj j).one}}
  mul := (limit.isLimit (F ⋙ forget C)).lift
    {pt := Limits.prod (Limits.limit (F ⋙ forget C)) (Limits.limit (F ⋙ forget C))
     π := { app := fun j ↦
             (prod.map (limit.π (F ⋙ forget C) j) (limit.π (F ⋙ forget C) j)) ≫ (F.obj j).mul
            naturality := by
              intro _ _ u
              simp only [const_obj_obj, postcomp, comp_obj, forget_obj, const_obj_map,
                Category.id_comp, Functor.comp_map, forget_map, Category.assoc, Hom.mul_hom,
                prod.map_map_assoc]
              rw [← Limits.limit.w _ u, ← prod.map_map, ← prod.map_map]; rfl}}
  inv := (limit.isLimit (F ⋙ forget C)).lift
    {pt := Limits.limit (F ⋙ forget C)
     π := {app := fun j ↦ (limit.π (F ⋙ forget C) j) ≫ (F.obj j).inv
           naturality := by
             intro _ _ u
             simp only [const_obj_obj, postcomp, comp_obj, forget_obj, const_obj_map,
               Category.id_comp, Functor.comp_map, forget_map, Category.assoc]
             rw [← Limits.limit.w _ u, (F.map u).inv_hom, Category.assoc]; rfl}}
  mul_assoc := by
    refine (limit.isLimit (F ⋙ forget C)).hom_ext (fun j ↦ ?_)
    simp only [comp_obj, forget_obj, limit.cone_x, postcomp, const_obj_obj, const_obj_map,
      Functor.comp_map, forget_map, id_eq, eq_mpr_eq_cast, limit.isLimit_lift, limit.cone_π,
      Category.assoc, limit.lift_π, prod.map_map_assoc, Category.id_comp, prod.associator_hom,
      prod.lift_map_assoc, Category.comp_id, prod.lift_fst_comp_snd_comp]
    rw [prod_map_comp_left, Category.assoc, (F.obj j).mul_assoc]
    simp only [prod.associator_hom, prod.lift_map_assoc, Category.comp_id]
    rw [← Category.assoc]
    congr 1
    ext
    · simp only [prod.comp_lift, prod.map_fst_assoc, prod.map_fst, limit.lift_π, BinaryFan.mk_pt,
      BinaryFan.π_app_left, BinaryFan.mk_fst]
    · simp only [prod.comp_lift, prod.map_fst_assoc, prod.map_fst, limit.lift_π, BinaryFan.mk_pt,
      BinaryFan.π_app_right, BinaryFan.mk_snd]
      rw [← Category.assoc]
      congr 1
      simp only [prod.comp_lift, prod.map_fst_assoc, prod.map_snd, prod.lift_fst_comp_snd_comp]
  mul_left_inv := by
    refine (limit.isLimit (F ⋙ forget C)).hom_ext (fun j ↦ ?_)
    simp only [comp_obj, forget_obj, limit.cone_x, postcomp, const_obj_obj, const_obj_map,
      Functor.comp_map, forget_map, id_eq, eq_mpr_eq_cast, limit.isLimit_lift, limit.cone_π,
      Category.assoc, limit.lift_π, prod.lift_map_assoc, Category.id_comp]
    have : (default : limit (F ⋙ forget C) ⟶ ⊤_ C) = limit.π (F ⋙ forget C) j ≫ default :=
      Subsingleton.elim _ _
    rw [this, Category.assoc, ← (F.obj j).mul_left_inv, ← Category.assoc]
    congr 1
    simp only [comp_obj, forget_obj, prod.comp_lift, Category.comp_id]

@[simp]
def candidate_cone_π : (Functor.const J).obj (candidate_cone_pt F) ⟶ F where
  app j := {hom := limit.π (F ⋙ forget C) j}
  naturality := by
    intro _ _ u
    ext
    simp only [candidate_cone_pt, postcomp, limit.isLimit_lift, const_obj_obj, comp_obj,
      forget_obj, const_obj_map, Category.id_comp, comp_hom']
    rw [← Limits.limit.w _ u]
    rfl

@[simp]
def candidate_cone : Cone F where
  pt := candidate_cone_pt F
  π := candidate_cone_π F

def candidate_cone_isLimit : IsLimit (candidate_cone F) where
  lift s := by
    simp only [candidate_cone, candidate_cone_pt, limit.isLimit_lift, const_obj_obj, comp_obj,
      forget_obj, candidate_cone_π]
    refine {hom := (limit.isLimit (F ⋙ forget C)).lift ((forget C).mapCone s),
            one_hom := ?_, inv_hom := ?_, mul_hom := ?_}
    · refine (limit.isLimit (F ⋙ forget C)).hom_ext (fun j ↦ ?_)
      simp only [comp_obj, forget_obj, limit.cone_x, limit.isLimit_lift, limit.cone_π,
        Category.assoc, limit.lift_π, mapCone_pt, mapCone_π_app, forget_map, Hom.one_hom]
    · refine (limit.isLimit (F ⋙ forget C)).hom_ext (fun j ↦ ?_)
      simp only [comp_obj, forget_obj, limit.cone_x, limit.isLimit_lift, limit.cone_π,
        Category.assoc, limit.lift_π, mapCone_pt, mapCone_π_app, forget_map, Hom.mul_hom,
        prod.map_map_assoc]
    · refine (limit.isLimit (F ⋙ forget C)).hom_ext (fun j ↦ ?_)
      simp only [comp_obj, forget_obj, limit.cone_x, limit.isLimit_lift, limit.cone_π,
        Category.assoc, limit.lift_π, mapCone_pt, mapCone_π_app, forget_map, limit.lift_π_assoc]
      exact (s.π.app j).inv_hom
  fac s j := by aesop_cat
  uniq s u h := by
    ext
    simp only [candidate_cone, candidate_cone_pt, limit.isLimit_lift, const_obj_obj, comp_obj,
      forget_obj, candidate_cone_π, id_eq]
    refine (limit.isLimit (F ⋙ forget C)).hom_ext (fun j ↦ ?_)
    simp only [comp_obj, forget_obj, limit.cone_x, limit.cone_π, limit.lift_π, mapCone_pt,
      mapCone_π_app, forget_map]
    have := h j
    apply_fun (fun T ↦ T.hom) at this
    exact this

def forget_candidate_cone :
    limit.cone (F ⋙ forget C) ≅ (forget C).mapCone (candidate_cone F) := by
  refine Cones.ext (Iso.refl _) (fun j ↦ ?_)
  simp only [candidate_cone, candidate_cone_pt, limit.isLimit_lift, const_obj_obj, comp_obj,
    forget_obj, candidate_cone_π, mapCone_pt, mapCone_π_app, forget_map, limit.cone_x,
    Iso.refl_hom, limit.cone_π, Category.id_comp]

instance groupObjectHasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape J (GroupObject C)
    where
  has_limit F := HasLimit.mk {cone := candidate_cone F, isLimit := candidate_cone_isLimit F}

instance forgetPreservesLimitsOfShape [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (forget C) where
  preservesLimit := preservesLimitOfPreservesLimitCone (candidate_cone_isLimit _)
    (IsLimit.ofIsoLimit (limit.isLimit (_ ⋙ forget C)) (forget_candidate_cone _))

instance forgetPreservesLimits [HasLimits C] : PreservesLimits (forget C) where
  preservesLimitsOfShape := inferInstance
