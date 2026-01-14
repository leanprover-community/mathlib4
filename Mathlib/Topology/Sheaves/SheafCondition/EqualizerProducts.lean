/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ᶜ F.obj (U i)` and `∏ᶜ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the "pairwise intersections" sheaf condition when
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
  ∏ᶜ fun i : ι => F.obj (op (U i))

/-- The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def piInters : C :=
  ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

/-- The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

@[simp, elementwise]
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res, limit.lift_π, Fan.mk_π_app]

/-- Copy of `limit.hom_ext`, specialized to `piOpens` for use by the `ext` tactic. -/
@[ext] theorem piOpens.hom_ext
    {X : C} {f f' : X ⟶ piOpens F U} (w : ∀ j, f ≫ limit.π _ j = f' ≫ limit.π _ j) : f = f' :=
  limit.hom_ext w

/-- Copy of `limit.hom_ext`, specialized to `piInters` for use by the `ext` tactic. -/
@[ext] theorem piInters.hom_ext
    {X : C} {f f' : X ⟶ piInters F U} (w : ∀ j, f ≫ limit.π _ j = f' ≫ limit.π _ j) : f = f' :=
  limit.hom_ext w

@[elementwise]
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U := by
  dsimp [res, leftRes, rightRes]
  ext
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr 1

/-- The equalizer diagram for the sheaf condition.
-/
abbrev diagram : WalkingParallelPair ⥤ C :=
  parallelPair (leftRes.{v'} F U) (rightRes F U)

/-- The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)

@[simp]
theorem fork_pt : (fork F U).pt = F.obj (op (iSup U)) :=
  rfl

@[simp]
theorem fork_ι : (fork F U).ι = res F U :=
  rfl

@[simp]
theorem fork_π_app_walkingParallelPair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl

@[simp]
theorem fork_π_app_walkingParallelPair_one :
    (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl

variable {F} {G : Presheaf C X}

/-- Isomorphic presheaves have isomorphic `piOpens` for any cover `U`. -/
@[simp]
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens.{v'} G U :=
  Pi.mapIso fun _ => α.app _

/-- Isomorphic presheaves have isomorphic `piInters` for any cover `U`. -/
@[simp]
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters.{v'} G U :=
  Pi.mapIso fun _ => α.app _

/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
  NatIso.ofComponents (by
    rintro ⟨⟩
    · exact piOpens.isoOfIso U α
    · exact piInters.isoOfIso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · dsimp
        ext
        simp only [leftRes, limit.lift_map, limit.lift_π, Cones.postcompose_obj_π,
          NatTrans.comp_app, Fan.mk_π_app, Discrete.natIso_hom_app, Iso.app_hom, Category.assoc,
          NatTrans.naturality, limMap_π_assoc]
      · dsimp [diagram]
        ext
        simp only [rightRes, limit.lift_map, limit.lift_π, Cones.postcompose_obj_π,
          NatTrans.comp_app, Fan.mk_π_app, Discrete.natIso_hom_app, Iso.app_hom, Category.assoc,
          NatTrans.naturality, limMap_π_assoc]
      · simp)

/-- If `F G : Presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.isoOfIso (α : F ≅ G) :
    fork F U ≅ (Cones.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) := by
  fapply Fork.ext
  · apply α.app
  · dsimp
    ext
    dsimp only [Fork.ι]
    -- Ugh, `simp` can't unfold abbreviations.
    simp only [res, diagram.isoOfIso, piOpens.isoOfIso, Cones.postcompose_obj_π,
      NatTrans.comp_app, fork_π_app_walkingParallelPair_zero, NatIso.ofComponents_inv_app,
      Functor.mapIso_inv, lim_map, limit.lift_map, Category.assoc, limit.lift_π, Fan.mk_π_app,
      Discrete.natIso_inv_app, Iso.app_inv, NatTrans.naturality, Iso.hom_inv_id_app_assoc]

end SheafConditionEqualizerProducts

/-- The sheaf condition for a `F : Presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ᶜ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ᶜ F.obj (U i) ⟶ ∏ᶜ F.obj (U i) ⊓ (U j)`.
-/
def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  ∀ ⦃ι : Type v'⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

/-!
The remainder of this file shows that the "equalizer products" sheaf condition is equivalent
to the "pairwise intersections" sheaf condition.
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
        · dsimp
          ext
          simp
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.leftRes]
            using c.π.naturality (Quiver.Hom.op (Hom.left i j))
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.rightRes]
            using c.π.naturality (Quiver.Hom.op (Hom.right i j))
        · dsimp
          ext
          simp }

section

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivFunctor :
    Limits.Cone ((diagram U).op ⋙ F) ⥤
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  obj c := coneEquivFunctorObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := fun j => by
        cases j <;>
          · dsimp
            ext
            simp }

end

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
def coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :
    Limits.Cone ((diagram U).op ⋙ F) where
  pt := c.pt
  π :=
    { app := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
      naturality := by
        intro x y f
        induction x with | op x => ?_
        induction y with | op y => ?_
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          rw [F.map_id]
          simp
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.left
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (i, j)
          rw [h']
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          rfl
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.right
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          rw [F.map_id]
          simp }

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivInverse :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤
      Limits.Cone ((diagram U).op ⋙ F) where
  obj c := coneEquivInverseObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [Fork.ι]
          rw [← f.w WalkingParallelPair.zero, Category.assoc]
        · dsimp
          rw [← f.w WalkingParallelPair.one, Category.assoc] }

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
def coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅
      (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c where
  hom :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
  inv :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivUnitIso :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U)

/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
def coneEquivCounitIso :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅
      𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { hom :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp }
        inv :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp } })
    fun {c d} f => by
    ext
    dsimp
    simp only [Category.comp_id, Category.id_comp]

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def coneEquiv :
    Limits.Cone ((diagram U).op ⋙ F) ≌
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

/-- If `SheafConditionEqualizerProducts.fork` is an equalizer,
then `F.mapCone (cone U)` is a limit cone.
-/
def isLimitMapConeOfIsLimitSheafConditionFork
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

/-- If `F.mapCone (cone U)` is a limit cone,
then `SheafConditionEqualizerProducts.fork` is an equalizer.
-/
def isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone U).op)) :
    IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

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

end Presheaf

end TopCat
