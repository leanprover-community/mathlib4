/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

#align_import topology.sheaves.sheaf_condition.equalizer_products from "leanprover-community/mathlib"@"85d6221d32c37e68f05b2e42cde6cee658dae5e9"

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ F.obj (U i)` and `∏ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the `pairwise_intersections` sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/


universe v' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]

variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

/-- The product of the sections of a presheaf over a family of open sets. -/
def piOpens : C :=
  ∏ fun i : ι => F.obj (op (U i))
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.pi_opens TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens

/-- The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def piInters : C :=
  ∏ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.pi_inters TopCat.Presheaf.SheafConditionEqualizerProducts.piInters

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.left_res TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.right_res TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes

/-- The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.res TopCat.Presheaf.SheafConditionEqualizerProducts.res

@[simp, elementwise]
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res, limit.lift_π, Fan.mk_π_app]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.res_π TopCat.Presheaf.SheafConditionEqualizerProducts.res_π

@[elementwise]
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U := by
  dsimp [res, leftRes, rightRes]
  -- ⊢ ((Pi.lift fun i => F.map (leSupr U i).op) ≫ Pi.lift fun p => Pi.π (fun i =>  …
  -- Porting note : `ext` can't see `limit.hom_ext` applies here:
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  refine limit.hom_ext (fun _ => ?_)
  -- ⊢ ((Pi.lift fun i => F.map (leSupr U i).op) ≫ Pi.lift fun p => Pi.π (fun i =>  …
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  -- ⊢ F.map (leSupr U x✝.as.fst).op ≫ F.map (infLELeft (U x✝.as.fst) (U x✝.as.snd) …
  rw [← F.map_comp]
  -- ⊢ F.map ((leSupr U x✝.as.fst).op ≫ (infLELeft (U x✝.as.fst) (U x✝.as.snd)).op) …
  rw [← F.map_comp]
  -- ⊢ F.map ((leSupr U x✝.as.fst).op ≫ (infLELeft (U x✝.as.fst) (U x✝.as.snd)).op) …
  congr 1
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.w TopCat.Presheaf.SheafConditionEqualizerProducts.w

/-- The equalizer diagram for the sheaf condition.
-/
@[reducible]
def diagram : WalkingParallelPair ⥤ C :=
  parallelPair (leftRes.{v'} F U) (rightRes F U)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.diagram TopCat.Presheaf.SheafConditionEqualizerProducts.diagram

/-- The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.fork TopCat.Presheaf.SheafConditionEqualizerProducts.fork

@[simp]
theorem fork_pt : (fork F U).pt = F.obj (op (iSup U)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.fork_X TopCat.Presheaf.SheafConditionEqualizerProducts.fork_pt

@[simp]
theorem fork_ι : (fork F U).ι = res F U :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.fork_ι TopCat.Presheaf.SheafConditionEqualizerProducts.fork_ι

@[simp]
theorem fork_π_app_walkingParallelPair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_zero TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_zero

-- Porting note : Shortcut simplifier
@[simp (high)]
theorem fork_π_app_walkingParallelPair_one :
    (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_one TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_one

variable {F} {G : Presheaf C X}

/-- Isomorphic presheaves have isomorphic `piOpens` for any cover `U`. -/
@[simp]
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens.{v'} G U :=
  Pi.mapIso fun _ => α.app _
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.pi_opens.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIso

/-- Isomorphic presheaves have isomorphic `piInters` for any cover `U`. -/
@[simp]
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters.{v'} G U :=
  Pi.mapIso fun _ => α.app _
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.pi_inters.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIso

/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
  NatIso.ofComponents (by rintro ⟨⟩; exact piOpens.isoOfIso U α; exact piInters.isoOfIso U α)
                          -- ⊢ (diagram F U).obj WalkingParallelPair.zero ≅ (diagram G U).obj WalkingParall …
                                     -- ⊢ (diagram F U).obj WalkingParallelPair.one ≅ (diagram G U).obj WalkingParalle …
                                                                 -- 🎉 no goals
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
        -- 🎉 no goals
      · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
        -- See https://github.com/leanprover-community/mathlib4/issues/5229
        refine limit.hom_ext (fun _ => ?_)
        -- ⊢ ((diagram F U).map WalkingParallelPairHom.left ≫ (WalkingParallelPair.casesO …
        simp only [leftRes, piOpens.isoOfIso, piInters.isoOfIso, parallelPair_map_left,
          Functor.mapIso_hom, lim_map, limit.lift_map, limit.lift_π, Cones.postcompose_obj_π,
          NatTrans.comp_app, Fan.mk_π_app, Discrete.natIso_hom_app, Iso.app_hom, Category.assoc,
          NatTrans.naturality, limMap_π_assoc]
      · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
        -- See https://github.com/leanprover-community/mathlib4/issues/5229
        refine limit.hom_ext (fun _ => ?_)
        -- ⊢ ((diagram F U).map WalkingParallelPairHom.right ≫ (WalkingParallelPair.cases …
        simp only [rightRes, piOpens.isoOfIso, piInters.isoOfIso, parallelPair_map_right,
          Functor.mapIso_hom, lim_map, limit.lift_map, limit.lift_π, Cones.postcompose_obj_π,
          NatTrans.comp_app, Fan.mk_π_app, Discrete.natIso_hom_app, Iso.app_hom, Category.assoc,
          NatTrans.naturality, limMap_π_assoc]
      · simp)
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.diagram.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso

/-- If `F G : presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.isoOfIso (α : F ≅ G) :
    fork F U ≅ (Cones.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) := by
  fapply Fork.ext
  -- ⊢ (fork F U).pt ≅ ((Cones.postcompose (diagram.isoOfIso U α).inv).obj (fork G  …
  · apply α.app
    -- 🎉 no goals
  · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
    -- See https://github.com/leanprover-community/mathlib4/issues/5229
    refine limit.hom_ext (fun _ => ?_)
    -- ⊢ ((α.app (op (iSup U))).hom ≫ Fork.ι ((Cones.postcompose (diagram.isoOfIso U  …
    dsimp only [Fork.ι]
    -- ⊢ ((α.app (op (iSup U))).hom ≫ NatTrans.app ((Cones.postcompose (diagram.isoOf …
    -- Ugh, `simp` can't unfold abbreviations.
    simp only [res, diagram.isoOfIso, Iso.app_hom, piOpens.isoOfIso, Cones.postcompose_obj_π,
      NatTrans.comp_app, fork_π_app_walkingParallelPair_zero, NatIso.ofComponents_inv_app,
      Functor.mapIso_inv, lim_map, limit.lift_map, Category.assoc, limit.lift_π, Fan.mk_π_app,
      Discrete.natIso_inv_app, Iso.app_inv, NatTrans.naturality, Iso.hom_inv_id_app_assoc]
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_equalizer_products.fork.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.fork.isoOfIso

end SheafConditionEqualizerProducts

/-- The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  ∀ ⦃ι : Type v'⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_equalizer_products TopCat.Presheaf.IsSheafEqualizerProducts

/-!
The remainder of this file shows that the equalizer_products sheaf condition is equivalent
to the pairwise_intersections sheaf condition.
-/


namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
def coneEquivFunctorObj (c : Cone ((diagram U).op ⋙ F)) :
    Cone (SheafConditionEqualizerProducts.diagram F U) where
  pt := c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        -- ⊢ ((Functor.const WalkingParallelPair).obj c.pt).map f ≫ (fun Z => WalkingPara …
                    -- ⊢ ((Functor.const WalkingParallelPair).obj c.pt).map f ≫ (fun Z => WalkingPara …
                    -- ⊢ ((Functor.const WalkingParallelPair).obj c.pt).map f ≫ (fun Z => WalkingPara …
                                -- ⊢ ((Functor.const WalkingParallelPair).obj c.pt).map (WalkingParallelPairHom.i …
                                -- ⊢ ((Functor.const WalkingParallelPair).obj c.pt).map WalkingParallelPairHom.le …
                                -- 🎉 no goals
                                -- ⊢ ((Functor.const WalkingParallelPair).obj c.pt).map (WalkingParallelPairHom.i …
        · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
          -- See https://github.com/leanprover-community/mathlib4/issues/5229
          refine limit.hom_ext fun i => ?_
          -- ⊢ (((Functor.const WalkingParallelPair).obj c.pt).map (WalkingParallelPairHom. …
          dsimp
          -- ⊢ (𝟙 c.pt ≫ Pi.lift fun i => NatTrans.app c.π (op (single i))) ≫ limit.π (Disc …
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app, CategoryTheory.Functor.map_id,
            Category.assoc]
          dsimp
          -- ⊢ NatTrans.app c.π (op (single i.as)) = (Pi.lift fun i => NatTrans.app c.π (op …
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app]
          -- 🎉 no goals
        · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
          -- See https://github.com/leanprover-community/mathlib4/issues/5229
          refine limit.hom_ext fun ⟨i, j⟩ => ?_
          -- ⊢ (((Functor.const WalkingParallelPair).obj c.pt).map WalkingParallelPairHom.l …
          dsimp [SheafConditionEqualizerProducts.leftRes]
          -- ⊢ (𝟙 c.pt ≫ Pi.lift fun b => NatTrans.app c.π (op (Pairwise.pair b.fst b.snd)) …
          simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
            Category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (Hom.left i j))
          -- ⊢ NatTrans.app c.π (op (Pairwise.pair i j)) = NatTrans.app c.π (op (single i)) …
          dsimp at h
          -- ⊢ NatTrans.app c.π (op (Pairwise.pair i j)) = NatTrans.app c.π (op (single i)) …
          simpa using h
          -- 🎉 no goals
        · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
          -- See https://github.com/leanprover-community/mathlib4/issues/5229
          refine limit.hom_ext fun ⟨i, j⟩ => ?_
          -- ⊢ (((Functor.const WalkingParallelPair).obj c.pt).map WalkingParallelPairHom.r …
          dsimp [SheafConditionEqualizerProducts.rightRes]
          -- ⊢ (𝟙 c.pt ≫ Pi.lift fun b => NatTrans.app c.π (op (Pairwise.pair b.fst b.snd)) …
          simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
            Category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (Hom.right i j))
          -- ⊢ NatTrans.app c.π (op (Pairwise.pair i j)) = NatTrans.app c.π (op (single j)) …
          dsimp at h
          -- ⊢ NatTrans.app c.π (op (Pairwise.pair i j)) = NatTrans.app c.π (op (single j)) …
          simpa using h
          -- 🎉 no goals
        · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
          -- See https://github.com/leanprover-community/mathlib4/issues/5229
          refine limit.hom_ext fun i => ?_
          -- ⊢ (((Functor.const WalkingParallelPair).obj c.pt).map (WalkingParallelPairHom. …
          dsimp
          -- ⊢ (𝟙 c.pt ≫ Pi.lift fun b => NatTrans.app c.π (op (Pairwise.pair b.fst b.snd)) …
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app, CategoryTheory.Functor.map_id,
            Category.assoc]
          dsimp
          -- ⊢ NatTrans.app c.π (op (Pairwise.pair i.as.fst i.as.snd)) = (Pi.lift fun b =>  …
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app] }
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor_obj TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctorObj

section

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivFunctor :
    Limits.Cone ((diagram U).op ⋙ F) ⥤ Limits.Cone (SheafConditionEqualizerProducts.diagram F U)
    where
  obj c := coneEquivFunctorObj F U c
  map {c c'} f :=
    { Hom := f.Hom
      w := fun j => by
        cases j <;>
        -- ⊢ f.Hom ≫ NatTrans.app ((fun c => coneEquivFunctorObj F U c) c').π WalkingPara …
          · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
            -- See https://github.com/leanprover-community/mathlib4/issues/5229
            refine limit.hom_ext fun i => ?_
            -- ⊢ (f.Hom ≫ NatTrans.app ((fun c => coneEquivFunctorObj F U c) c').π WalkingPar …
            -- ⊢ (f.Hom ≫ NatTrans.app ((fun c => coneEquivFunctorObj F U c) c').π WalkingPar …
            simp only [Limits.Fan.mk_π_app, Limits.ConeMorphism.w, Limits.limit.lift_π,
              Category.assoc, coneEquivFunctorObj_π_app] }
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctor

end

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
def coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :
    Limits.Cone ((diagram U).op ⋙ F) where
  pt := c.pt
  π :=
    { app := by
        intro x
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).obj x ⟶ ((diagram U …
        induction x using Opposite.rec' with | h x => ?_
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).obj (op x) ⟶ ((diag …
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).obj x ⟶ ((diagram U …
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).obj (op (single i)) …
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
          -- 🎉 no goals
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
          -- 🎉 no goals
      naturality := by
        intro x y f
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ Opposite.re …
        induction x using Opposite.rec' with | h x => ?_
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ Opposite.re …
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ Opposite.re …
        induction y using Opposite.rec' with | h y => ?_
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ Opposite.re …
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ Opposite.re …
        have ef : f = f.unop.op := rfl
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ Opposite.re …
        revert ef
        -- ⊢ f = f.unop.op → ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map …
        generalize f.unop = f'
        -- ⊢ f = f'.op → ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f ≫ …
        rintro rfl
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f'.op ≫ Opposit …
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f'.op ≫ Opposit …
                                     -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f'.op ≫ Opposit …
                                     -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map f'.op ≫ Opposit …
                                                                     -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map (id_single i).o …
                                                                     -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map (left i j).op ≫ …
                                                                     -- 🎉 no goals
                                                                     -- ⊢ ((Functor.const (CategoryTheory.Pairwise ι)ᵒᵖ).obj c.pt).map (id_pair a✝¹ a✝ …
        · dsimp
          -- ⊢ 𝟙 c.pt ≫ Fork.ι c ≫ Pi.π (fun i => F.obj (op (U i))) i = (Fork.ι c ≫ Pi.π (f …
          erw [F.map_id]
          -- ⊢ 𝟙 c.pt ≫ Fork.ι c ≫ Pi.π (fun i => F.obj (op (U i))) i = (Fork.ι c ≫ Pi.π (f …
          simp
          -- 🎉 no goals
        · dsimp
          -- ⊢ 𝟙 c.pt ≫ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op …
          simp only [Category.id_comp, Category.assoc]
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          have h := c.π.naturality WalkingParallelPairHom.left
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          simp only [Category.id_comp] at h
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          have h' := h =≫ Pi.π _ (i, j)
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          rw [h']
          -- ⊢ (Fork.ι c ≫ Pi.lift fun p => Pi.π (fun i => F.obj (op (U i))) p.fst ≫ F.map  …
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          -- ⊢ Fork.ι c ≫ Pi.π (fun i => F.obj (op (U i))) i ≫ F.map (infLELeft (U i) (U j) …
          rfl
          -- 🎉 no goals
        · dsimp
          -- ⊢ 𝟙 c.pt ≫ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op …
          simp only [Category.id_comp, Category.assoc]
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          have h := c.π.naturality WalkingParallelPairHom.right
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          simp only [Category.id_comp] at h
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          have h' := h =≫ Pi.π _ (j, i)
          -- ⊢ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op (U p.fst …
          rw [h']
          -- ⊢ (Fork.ι c ≫ Pi.lift fun p => Pi.π (fun i => F.obj (op (U i))) p.snd ≫ F.map  …
          simp
          -- ⊢ Fork.ι c ≫ Pi.π (fun i => F.obj (op (U i))) i ≫ F.map (infLERight (U j) (U i …
          rfl
          -- 🎉 no goals
        · dsimp
          -- ⊢ 𝟙 c.pt ≫ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op …
          erw [F.map_id]
          -- ⊢ 𝟙 c.pt ≫ NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op …
          simp }
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse_obj TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverseObj

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivInverse :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤ Limits.Cone ((diagram U).op ⋙ F)
    where
  obj c := coneEquivInverseObj F U c
  map {c c'} f :=
    { Hom := f.Hom
      w := by
        intro x
        -- ⊢ f.Hom ≫ NatTrans.app ((fun c => coneEquivInverseObj F U c) c').π x = NatTran …
        induction x using Opposite.rec' with | h x => ?_
        -- ⊢ f.Hom ≫ NatTrans.app ((fun c => coneEquivInverseObj F U c) c').π (op x) = Na …
        -- ⊢ f.Hom ≫ NatTrans.app ((fun c => coneEquivInverseObj F U c) c').π x = NatTran …
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        -- ⊢ f.Hom ≫ NatTrans.app ((fun c => coneEquivInverseObj F U c) c').π (op (single …
        · dsimp
          -- ⊢ f.Hom ≫ Fork.ι c' ≫ Pi.π (fun i => F.obj (op (U i))) i = Fork.ι c ≫ Pi.π (fu …
          dsimp only [Fork.ι]
          -- ⊢ f.Hom ≫ NatTrans.app c'.π WalkingParallelPair.zero ≫ Pi.π (fun i => F.obj (o …
          rw [← f.w WalkingParallelPair.zero, Category.assoc]
          -- 🎉 no goals
        · dsimp
          -- ⊢ f.Hom ≫ NatTrans.app c'.π WalkingParallelPair.one ≫ Pi.π (fun p => F.obj (op …
          rw [← f.w WalkingParallelPair.one, Category.assoc] }
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverse

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
def coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅ (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c
    where
  hom :=
    { Hom := 𝟙 _
      w := fun j => by
        induction j using Opposite.rec' with | h j => ?_;
        -- ⊢ 𝟙 ((𝟭 (Cone ((diagram U).op ⋙ F))).obj c).pt ≫ NatTrans.app ((coneEquivFunct …
        -- ⊢ 𝟙 ((𝟭 (Cone ((diagram U).op ⋙ F))).obj c).pt ≫ NatTrans.app ((coneEquivFunct …
        rcases j with ⟨⟩ <;>
        -- ⊢ 𝟙 ((𝟭 (Cone ((diagram U).op ⋙ F))).obj c).pt ≫ NatTrans.app ((coneEquivFunct …
        · dsimp [coneEquivInverse]
          -- ⊢ 𝟙 c.pt ≫ (Pi.lift fun i => NatTrans.app c.π (op (single i))) ≫ Pi.π (fun i = …
          -- ⊢ 𝟙 c.pt ≫ (Pi.lift fun b => NatTrans.app c.π (op (Pairwise.pair b.fst b.snd)) …
          -- 🎉 no goals
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
          -- 🎉 no goals
  inv :=
    { Hom := 𝟙 _
      w := fun j => by
        induction j using Opposite.rec' with | h j => ?_;
        -- ⊢ 𝟙 ((coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c).pt ≫ NatTrans.app (( …
        -- ⊢ 𝟙 ((coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c).pt ≫ NatTrans.app (( …
        rcases j with ⟨⟩ <;>
        -- ⊢ 𝟙 ((coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c).pt ≫ NatTrans.app (( …
        · dsimp [coneEquivInverse]
          -- ⊢ 𝟙 c.pt ≫ NatTrans.app c.π (op (single a✝)) = (Pi.lift fun i => NatTrans.app  …
          -- ⊢ 𝟙 c.pt ≫ NatTrans.app c.π (op (Pairwise.pair a✝¹ a✝)) = (Pi.lift fun b => Na …
          -- 🎉 no goals
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso_app TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIsoApp

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivUnitIso :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIso

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivCounitIso :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅
      𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { hom :=
          { Hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              -- ⊢ 𝟙 ((coneEquivInverse F U ⋙ coneEquivFunctor F U).obj c).pt ≫ NatTrans.app (( …
              · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
                -- See https://github.com/leanprover-community/mathlib4/issues/5229
                refine limit.hom_ext fun ⟨j⟩ => ?_
                -- ⊢ (𝟙 ((coneEquivInverse F U ⋙ coneEquivFunctor F U).obj c).pt ≫ NatTrans.app ( …
                dsimp [coneEquivInverse]
                -- ⊢ (𝟙 c.pt ≫ Fork.ι c) ≫ limit.π (Discrete.functor fun i => F.obj (op (U i))) { …
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π]
                -- 🎉 no goals
              · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
                -- See https://github.com/leanprover-community/mathlib4/issues/5229
                refine limit.hom_ext fun ⟨i, j⟩ => ?_
                -- ⊢ (𝟙 ((coneEquivInverse F U ⋙ coneEquivFunctor F U).obj c).pt ≫ NatTrans.app ( …
                dsimp [coneEquivInverse]
                -- ⊢ (𝟙 c.pt ≫ NatTrans.app c.π WalkingParallelPair.one) ≫ limit.π (Discrete.func …
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
                -- 🎉 no goals
        inv :=
          { Hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              -- ⊢ 𝟙 ((𝟭 (Cone (SheafConditionEqualizerProducts.diagram F U))).obj c).pt ≫ NatT …
              · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
                -- See https://github.com/leanprover-community/mathlib4/issues/5229
                refine limit.hom_ext fun ⟨j⟩ => ?_
                -- ⊢ (𝟙 ((𝟭 (Cone (SheafConditionEqualizerProducts.diagram F U))).obj c).pt ≫ Nat …
                dsimp [coneEquivInverse]
                -- ⊢ (𝟙 c.pt ≫ Pi.lift fun i => Fork.ι c ≫ Pi.π (fun i => F.obj (op (U i))) i) ≫  …
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π]
                -- 🎉 no goals
              · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
                -- See https://github.com/leanprover-community/mathlib4/issues/5229
                refine limit.hom_ext fun ⟨i, j⟩ => ?_
                -- ⊢ (𝟙 ((𝟭 (Cone (SheafConditionEqualizerProducts.diagram F U))).obj c).pt ≫ Nat …
                dsimp [coneEquivInverse]
                -- ⊢ (𝟙 c.pt ≫ Pi.lift fun b => NatTrans.app c.π WalkingParallelPair.one ≫ Pi.π ( …
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] } })
                -- 🎉 no goals
    fun {c d} f => by
    ext
    -- ⊢ ((coneEquivInverse F U ⋙ coneEquivFunctor F U).map f ≫ ((fun c => Iso.mk (Co …
    dsimp
    -- ⊢ f.Hom ≫ 𝟙 d.pt = 𝟙 c.pt ≫ f.Hom
    simp only [Category.comp_id, Category.id_comp]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_counit_iso TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivCounitIso

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def coneEquiv :
    Limits.Cone ((diagram U).op ⋙ F) ≌ Limits.Cone (SheafConditionEqualizerProducts.diagram F U)
    where
  functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquiv

-- Porting note: not supported in Lean 4
-- attribute [local reducible]
--   SheafConditionEqualizerProducts.res SheafConditionEqualizerProducts.leftRes

/-- If `SheafConditionEqualizerProducts.fork` is an equalizer,
then `F.mapCone (cone U)` is a limit cone.
-/
def isLimitMapConeOfIsLimitSheafConditionFork
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { Hom := 𝟙 _
          w := by
            intro x
            -- ⊢ 𝟙 ((CategoryTheory.Equivalence.symm (coneEquiv F U)).functor.obj (SheafCondi …
            induction x with | h x => ?_
            -- ⊢ 𝟙 ((CategoryTheory.Equivalence.symm (coneEquiv F U)).functor.obj (SheafCondi …
            -- ⊢ 𝟙 ((CategoryTheory.Equivalence.symm (coneEquiv F U)).functor.obj (SheafCondi …
            rcases x with ⟨⟩
            -- ⊢ 𝟙 ((CategoryTheory.Equivalence.symm (coneEquiv F U)).functor.obj (SheafCondi …
            · simp
              -- ⊢ F.map (coconeιApp U (single a✝)).op = F.map (leSupr U a✝).op
              rfl
              -- 🎉 no goals
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              -- ⊢ F.map (coconeιApp U (Pairwise.pair a✝¹ a✝)).op = F.map ((leSupr U a✝¹).op ≫  …
              rfl }
              -- 🎉 no goals
      inv :=
        { Hom := 𝟙 _
          w := by
            intro x
            -- ⊢ 𝟙 (F.mapCone (Cocone.op (cocone U))).pt ≫ NatTrans.app ((CategoryTheory.Equi …
            induction x with | h x => ?_
            -- ⊢ 𝟙 (F.mapCone (Cocone.op (cocone U))).pt ≫ NatTrans.app ((CategoryTheory.Equi …
            -- ⊢ 𝟙 (F.mapCone (Cocone.op (cocone U))).pt ≫ NatTrans.app ((CategoryTheory.Equi …
            rcases x with ⟨⟩
            -- ⊢ 𝟙 (F.mapCone (Cocone.op (cocone U))).pt ≫ NatTrans.app ((CategoryTheory.Equi …
            · simp
              -- ⊢ F.map (leSupr U a✝).op = F.map (coconeιApp U (single a✝)).op
              rfl
              -- 🎉 no goals
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              -- ⊢ F.map ((leSupr U a✝¹).op ≫ (infLELeft (U a✝¹) (U a✝)).op) = F.map (coconeιAp …
              rfl } }
              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_map_cone_of_is_limit_sheaf_condition_fork TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitMapConeOfIsLimitSheafConditionFork

/-- If `F.mapCone (cone U)` is a limit cone,
then `SheafConditionEqualizerProducts.fork` is an equalizer.
-/
def isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone U).op)) :
    IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { Hom := 𝟙 _
          w := by
            rintro ⟨⟩
            -- ⊢ 𝟙 ((coneEquiv F U).functor.obj (F.mapCone (Cocone.op (cocone U)))).pt ≫ NatT …
            · simp
              -- ⊢ SheafConditionEqualizerProducts.res F U = Pi.lift fun i => F.map (coconeιApp …
              rfl
              -- 🎉 no goals
            · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
              -- See https://github.com/leanprover-community/mathlib4/issues/5229
              refine limit.hom_ext fun ⟨i, j⟩ => ?_
              -- ⊢ (𝟙 ((coneEquiv F U).functor.obj (F.mapCone (Cocone.op (cocone U)))).pt ≫ Nat …
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              -- ⊢ F.map ((leSupr U i).op ≫ (infLELeft (U i) (U j)).op) = F.map (coconeιApp U ( …
              rfl }
              -- 🎉 no goals
      inv :=
        { Hom := 𝟙 _
          w := by
            rintro ⟨⟩
            -- ⊢ 𝟙 (SheafConditionEqualizerProducts.fork F U).pt ≫ NatTrans.app ((coneEquiv F …
            · simp
              -- ⊢ (Pi.lift fun i => F.map (coconeιApp U (single i)).op) = SheafConditionEquali …
              rfl
              -- 🎉 no goals
            · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
              -- See https://github.com/leanprover-community/mathlib4/issues/5229
              refine limit.hom_ext fun ⟨i, j⟩ => ?_
              -- ⊢ (𝟙 (SheafConditionEqualizerProducts.fork F U).pt ≫ NatTrans.app ((coneEquiv  …
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              -- ⊢ F.map (coconeιApp U (Pairwise.pair i j)).op = F.map ((leSupr U i).op ≫ (infL …
              rfl } }
              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_sheaf_condition_fork_of_is_limit_map_cone TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitSheafConditionForkOfIsLimitMapCone

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the default sheaf condition.
-/
theorem isSheaf_iff_isSheafEqualizerProducts (F : Presheaf C X) :
    F.IsSheaf ↔ F.IsSheafEqualizerProducts :=
  (isSheaf_iff_isSheafPairwiseIntersections F).trans <|
    Iff.intro (fun h _ U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h _ U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_iff_is_sheaf_equalizer_products TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts

end Presheaf

end TopCat
