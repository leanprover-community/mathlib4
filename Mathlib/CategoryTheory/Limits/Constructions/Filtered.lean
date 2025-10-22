/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Constructing colimits from finite colimits and filtered colimits

We construct colimits of size `w` from finite colimits and filtered colimits of size `w`. Since
`w`-sized colimits are constructed from coequalizers and `w`-sized coproducts, it suffices to
construct `w`-sized coproducts from finite coproducts and `w`-sized filtered colimits.

The idea is simple: to construct coproducts of shape `α`, we take the colimit of the filtered
diagram of all coproducts of finite subsets of `α`.

We also deduce the dual statement by invoking the original statement in `Cᵒᵖ`.
-/


universe w v u

noncomputable section

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {α : Type w}

namespace CategoryTheory.Limits

namespace CoproductsFromFiniteFiltered

variable [HasFiniteCoproducts C]

/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
def liftToFinsetObj (F : Discrete α ⥤ C) : Finset (Discrete α) ⥤ C where
  obj s := ∐ fun x : s => F.obj x
  map {_ Y} h := Sigma.desc fun y =>
    Sigma.ι (fun (x : { x // x ∈ Y }) => F.obj x) ⟨y, h.down.down y.2⟩

/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over the indexing type. -/
@[simps!]
def liftToFinsetColimitCocone [HasColimitsOfShape (Finset (Discrete α)) C]
    (F : Discrete α ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := colimit (liftToFinsetObj F)
      ι :=
        Discrete.natTrans fun j =>
          Sigma.ι (fun x : ({j} : Finset (Discrete α)) => F.obj x) ⟨j, by simp⟩ ≫
            colimit.ι (liftToFinsetObj F) {j} }
  isColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinsetObj F)
          { pt := s.pt
            ι := { app := fun _ => Sigma.desc fun x => s.ι.app x } }
      uniq := fun s m h => by
        apply colimit.hom_ext
        rintro t
        dsimp [liftToFinsetObj]
        apply colimit.hom_ext
        rintro ⟨⟨j, hj⟩⟩
        convert h j using 1
        · simp [← colimit.w (liftToFinsetObj F) ⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩]
          rfl
        · simp }

variable (C) (α) in
/-- The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) ⥤ C` by taking
coproducts. -/
@[simps!]
def liftToFinset : (Discrete α ⥤ C) ⥤ (Finset (Discrete α) ⥤ C) where
  obj := liftToFinsetObj
  map := fun β => { app := fun _ => Sigma.map (fun x => β.app x.val) }

/-- The converse of the construction in `liftToFinsetColimitCocone`: we can form a cocone on the
coproduct of `f` whose legs are the coproducts over the finite subsets of `α`. -/
@[simps!]
def finiteSubcoproductsCocone (f : α → C) [HasCoproduct f] :
    Cocone (liftToFinsetObj (Discrete.functor f)) where
  pt := ∐ f
  ι := { app S := Sigma.desc fun s => Sigma.ι f _ }

/-- The cocone `finiteSubcoproductsCocone` is a colimit cocone. -/
def isColimitFiniteSubproductsCocone (f : α → C) [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasCoproduct f] : IsColimit (finiteSubcoproductsCocone f) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (IsColimit.coconePointUniqueUpToIso
      (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) :) (by
    intro S
    simp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
      colimit.cocone_x, Functor.const_obj_obj, colimit.cocone_ι, finiteSubcoproductsCocone_ι_app]
    ext j
    rw [← Category.assoc]
    convert IsColimit.comp_coconePointUniqueUpToIso_hom
      (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) j
    · simp [← colimit.w (liftToFinsetObj _) (homOfLE (x := {j.1}) (y := S) (by simp))]
    · simp))

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

theorem hasCoproducts_of_finite_and_filtered [HasFiniteCoproducts C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasCoproducts.{w} C := fun α => by
  classical exact ⟨fun F => HasColimit.mk (liftToFinsetColimitCocone F)⟩

theorem has_colimits_of_finite_and_filtered [HasFiniteColimits C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C :=
  have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_hasCoequalizers_and_coproducts

theorem hasProducts_of_finite_and_cofiltered [HasFiniteProducts C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasProducts.{w} C :=
  have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  hasProducts_of_opposite

theorem has_limits_of_finite_and_cofiltered [HasFiniteLimits C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} C :=
  have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_hasEqualizers_and_products

namespace CoproductsFromFiniteFiltered

section

variable [HasFiniteCoproducts C] [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasColimitsOfShape (Discrete α) C]

/-- Helper construction for `liftToFinsetColimIso`. -/
@[reassoc]
theorem liftToFinsetColimIso_aux (F : Discrete α ⥤ C) {J : Finset (Discrete α)} (j : J) :
    Sigma.ι (F.obj ·.val) j ≫ colimit.ι (liftToFinsetObj F) J ≫
      (colimit.isoColimitCocone (liftToFinsetColimitCocone F)).inv
    = colimit.ι F j := by
  simp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]

/-- The `liftToFinset` functor, precomposed with forming a colimit, is a coproduct on the original
functor. -/
def liftToFinsetColimIso : liftToFinset C α ⋙ colim ≅ colim :=
  NatIso.ofComponents
    (fun F => Iso.symm <| colimit.isoColimitCocone (liftToFinsetColimitCocone F))
    (fun β => by
      simp only [Functor.comp_obj, colim_obj, Functor.comp_map, colim_map, Iso.symm_hom]
      ext J
      simp only [liftToFinset_obj_obj]
      ext j
      simp only [liftToFinset, ι_colimMap_assoc, liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
        Discrete.natTrans_app, liftToFinsetColimIso_aux, liftToFinsetColimIso_aux_assoc,
        ι_colimMap])

end

/-- `liftToFinset`, when composed with the evaluation functor, results in the whiskering composed
with `colim`. -/
def liftToFinsetEvaluationIso [HasFiniteCoproducts C] (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj I ≅
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ colim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp

end CoproductsFromFiniteFiltered

namespace ProductsFromFiniteCofiltered

variable [HasFiniteProducts C]

/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
def liftToFinsetObj (F : Discrete α ⥤ C) : (Finset (Discrete α))ᵒᵖ ⥤ C where
  obj s := ∏ᶜ (fun x : s.unop => F.obj x)
  map {Y _} h := Pi.lift fun y =>
    Pi.π (fun (x : { x // x ∈ Y.unop }) => F.obj x) ⟨y, h.unop.down.down y.2⟩


/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over the indexing type. -/
@[simps!]
def liftToFinsetLimitCone [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    (F : Discrete α ⥤ C) : LimitCone F where
  cone :=
    { pt := limit (liftToFinsetObj F)
      π := Discrete.natTrans fun j =>
        limit.π (liftToFinsetObj F) ⟨{j}⟩ ≫ Pi.π _ (⟨j, by simp⟩ : ({j} : Finset (Discrete α))) }
  isLimit :=
    { lift := fun s =>
        limit.lift (liftToFinsetObj F)
          { pt := s.pt
            π := { app := fun _ => Pi.lift fun x => s.π.app x } }
      uniq := fun s m h => by
        apply limit.hom_ext
        rintro t
        dsimp [liftToFinsetObj]
        apply limit.hom_ext
        rintro ⟨⟨j, hj⟩⟩
        convert h j using 1
        · simp [← limit.w (liftToFinsetObj F) ⟨⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩⟩]
          rfl
        · simp }

/-- The converse of the construction in `liftToFinsetLimitCone`: we can form a cone on the
product of `f` whose legs are the products over the finite subsets of `α`. -/
@[simps!]
def finiteSubproductsCone (f : α → C) [HasProduct f] :
    Cone (liftToFinsetObj (Discrete.functor f)) where
  pt := ∏ᶜ f
  π := { app S := Pi.lift fun s => Pi.π f _ }

/-- The cone `finiteSubproductsCone` is a limit cone. -/
def isLimitFiniteSubproductsCone (f : α → C) [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    [HasProduct f] : IsLimit (finiteSubproductsCone f) :=
  IsLimit.ofIsoLimit (limit.isLimit _)
    (Cones.ext (IsLimit.conePointUniqueUpToIso
      (liftToFinsetLimitCone (Discrete.functor f)).isLimit (limit.isLimit _) :) (by
    intro S
    simp only [limit.cone_x, Functor.const_obj_obj, liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
      limit.cone_π, finiteSubproductsCone_pt, finiteSubproductsCone_π_app]
    ext j
    simp only [Discrete.functor_obj_eq_as, Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
      limit.conePointUniqueUpToIso_hom_comp, liftToFinsetLimitCone_cone_pt, Discrete.mk_as,
      liftToFinsetLimitCone_cone_π_app]
    simp [← limit.w (liftToFinsetObj _)
      (Quiver.Hom.op (homOfLE (x := {j.1}) (y := S.unop) (by simp)))]))

variable (C) (α)

/-- The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) ⥤ C` by taking
coproducts. -/
@[simps!]
def liftToFinset : (Discrete α ⥤ C) ⥤ ((Finset (Discrete α))ᵒᵖ ⥤ C) where
  obj := liftToFinsetObj
  map := fun β => { app := fun _ => Pi.map (fun x => β.app x.val) }

/-- The `liftToFinset` functor, precomposed with forming a colimit, is a coproduct on the original
functor. -/
def liftToFinsetLimIso [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    [HasLimitsOfShape (Discrete α) C] : liftToFinset C α ⋙ lim ≅ lim :=
  NatIso.ofComponents
    (fun F => Iso.symm <| limit.isoLimitCone (liftToFinsetLimitCone F))
    (fun β => by
      simp only [Functor.comp_obj, lim_obj, Functor.comp_map, lim_map, Iso.symm_hom]
      ext J
      simp [liftToFinset])

/-- `liftToFinset`, when composed with the evaluation functor, results in the whiskering composed
with `colim`. -/
def liftToFinsetEvaluationIso (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj ⟨I⟩ ≅
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ lim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasLimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp

end ProductsFromFiniteCofiltered

end CategoryTheory.Limits
