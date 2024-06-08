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

variable {C : Type u} [Category.{v, u} C] [HasFiniteProducts C]

variable {J : Type u'} [Category.{v',u'} J] [HasLimitsOfShape J C]

variable {K : Type u''} [Category.{v'', u''} K] [HasLimitsOfShape K C]

variable {J' : Type} [SmallCategory J'] [HasLimitsOfShape J' C]

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

namespace GroupObject

open GroupObjectFunctor CategoryTheory.Functor

variable (C J)

def constAdj'_core : Adjunction.CoreUnitCounit
    (map (Functor.const J : C ⥤ J ⥤ C)) (map (lim : (J ⥤ C) ⥤ C)) where
  unit := (mapId C).inv ≫ (map₂ Limits.constLimAdj.unit) ≫ (mapComp (const J) lim).hom
  counit := (mapComp lim (const J)).inv ≫ (map₂ Limits.constLimAdj.counit) ≫
    (mapId (J ⥤ C)).hom
  left_triangle := by
    ext
    simp only [GroupObjectFunctor.map, comp_obj, id_obj, map_obj_X, const_obj_obj, map₂, id_eq,
      whiskerRight_comp, whiskerLeft_comp, Category.assoc, NatTrans.comp_app, whiskerRight_app,
      associator_hom_app, whiskerLeft_app, Category.id_comp, comp_hom', map_map_hom,
      mapId_inv_app_hom, CategoryTheory.Functor.map_id, lim_obj, mapComp_hom_app_hom,
      mapComp_inv_app_hom, mapId_hom_app_hom, Category.comp_id,
      Adjunction.left_triangle_components, NatTrans.id_app, NatTrans.id_app', id_hom']
  right_triangle := by
    ext X
    simp only [GroupObjectFunctor.map, comp_obj, id_obj, map_obj_X, lim_obj, map₂, id_eq,
      whiskerLeft_comp, whiskerRight_comp, Category.assoc, NatTrans.comp_app, whiskerLeft_app,
      associator_inv_app, whiskerRight_app, Category.id_comp, comp_hom', mapId_inv_app_hom,
      mapComp_hom_app_hom, map_map_hom, mapComp_inv_app_hom, mapId_hom_app_hom,
      NatTrans.id_app', id_hom']
    rw [CategoryTheory.Functor.map_id]; erw [Category.id_comp]
    rw [CategoryTheory.Functor.map_id]; erw [Category.comp_id]
    have := (Limits.constLimAdj (J := J) (C := C)).right_triangle
    apply_fun (fun α ↦ α.app X.X) at this
    simp only [comp_obj, lim_obj, id_obj, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      NatTrans.id_app] at this
    exact this

def constAdj' := Adjunction.mkOfUnitCounit (constAdj'_core C J)

@[simp]
def constIsConst_app (X : GroupObject C) :
    (FunctorEquivalence J C).functor.obj ((map (Functor.const J (C := C))).obj X) ≅
    (Functor.const J).obj X := by
  refine NatIso.ofComponents ?_ ?_
  · intro j
    refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_ <;> simp only [const_obj_obj,
      FunctorEquivalence, FunctorEquivalence.functor, FunctorEquivalence.functor.obj,
      FunctorEquivalence.functor.obj_obj, FunctorEquivalence.functor.obj_obj_one,
      evaluation_obj_obj, FunctorEquivalence.functor.obj_obj_mul, FunctorEquivalence.functor.map,
      id_eq, FunctorEquivalence.inverse, FunctorEquivalence.unitIso, id_obj, comp_obj,
      FunctorEquivalence.inverse.obj, FunctorEquivalence.inverse.obj_X,
      FunctorEquivalence.inverse.obj_one, FunctorEquivalence.inverse.obj_mul,
      FunctorEquivalence.inverse.obj_inv, FunctorEquivalence.counitIso, map, map_obj_X, map_obj_one,
      NatTrans.comp_app, const_map_app, map_obj_mul, map_obj_inv, const_obj_map,
      PreservesTerminal.iso_inv, NatIso.isIso_inv_app, Iso.refl_hom, Category.comp_id,
      IsIso.inv_comp_eq]
    · rw [← Category.assoc, Subsingleton.elim ((terminalComparison (const J)).app j ≫
      terminalComparison ((evaluation J C).obj j)) (𝟙 _)]; erw [Category.id_comp]
    · rw [← Category.assoc _ _ X.mul]
      congr 1
      ext
      · simp only [PreservesLimitPair.iso_inv, evaluation_obj_obj, const_obj_obj,
        NatIso.isIso_inv_app, Category.assoc, prod.map_id_id, Category.id_comp, IsIso.inv_comp_eq]
        erw [prodComparison_fst, evaluation_obj_map]
        rw [← NatTrans.comp_app, prodComparison_fst]
        simp only [const_map_app]
      · simp only [PreservesLimitPair.iso_inv, evaluation_obj_obj, const_obj_obj,
        NatIso.isIso_inv_app, Category.assoc, prod.map_id_id, Category.id_comp, IsIso.inv_comp_eq]
        erw [prodComparison_snd, evaluation_obj_map]
        rw [← NatTrans.comp_app, prodComparison_snd]
        simp only [const_map_app]
    · simp only [Category.id_comp]
  · intro j j' u
    ext
    simp only [FunctorEquivalence, FunctorEquivalence.functor, FunctorEquivalence.functor.obj,
      FunctorEquivalence.functor.obj_obj, FunctorEquivalence.functor.obj_obj_one,
      evaluation_obj_obj, FunctorEquivalence.functor.obj_obj_mul, FunctorEquivalence.functor.map,
      id_eq, FunctorEquivalence.inverse, FunctorEquivalence.unitIso, id_obj, comp_obj,
      FunctorEquivalence.inverse.obj, FunctorEquivalence.inverse.obj_X,
      FunctorEquivalence.inverse.obj_one, FunctorEquivalence.inverse.obj_mul,
      FunctorEquivalence.inverse.obj_inv, FunctorEquivalence.counitIso, map, map_obj_X,
      const_obj_obj, map_obj_one, NatTrans.comp_app, const_map_app, map_obj_mul, map_obj_inv,
      const_obj_map, comp_hom', isoOfIso_hom_hom, Iso.refl_hom, Category.comp_id]

def constIsConst : map (Functor.const J (C := C)) ⋙ (FunctorEquivalence J C).functor ≅
    Functor.const J (C := GroupObject C) := by
  refine NatIso.ofComponents (constIsConst_app C J) (by aesop_cat)

def constAdj : Adjunction (Functor.const J (C := GroupObject C))
    ((FunctorEquivalence J C).inverse ⋙ map lim) :=
  Adjunction.ofNatIsoLeft (Adjunction.comp (constAdj' C J)
  (FunctorEquivalence J C).toAdjunction) (constIsConst C J)

instance instHasLimitsOfShape : HasLimitsOfShape J (GroupObject C) where
  has_limit :=
    fun F ↦ Limits.HasLimit.mk {cone := Limits.coneOfAdj (constAdj C J) F,
                                isLimit := Limits.isLimitConeOfAdj (constAdj C J) F}

def forget_comp_lim : (lim : (J ⥤ GroupObject C) ⥤ GroupObject C) ⋙ GroupObject.forget C ≅
    (GroupObject.forget C).postcomp ⋙ lim := by
  refine (NatIso.hcomp (Adjunction.rightAdjointUniq (Limits.constLimAdj (J := J)
    (C := GroupObject C)) (GroupObject.constAdj C J)) (Iso.refl (GroupObject.forget C))).trans ?_
  refine (Functor.associator _ _ _).trans ?_
  refine (NatIso.hcomp (Iso.refl ((FunctorEquivalence J C).inverse))
    (GroupObjectFunctor.map_comp_forget (lim (J := J) (C := C)))).trans ?_
  exact (Functor.associator _ _ _).symm.trans (NatIso.hcomp
    (FunctorEquivalence.forget_postcomp J C) (Iso.refl lim))

end GroupObject
