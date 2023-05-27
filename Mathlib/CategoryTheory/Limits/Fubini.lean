/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.fubini
! leanprover-community/mathlib commit 59382264386afdbaf1727e617f5fdda511992eb9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Products.Basic
import Mathbin.CategoryTheory.Functor.Currying

/-!
# A Fubini theorem for categorical limits

We prove that $lim_{J × K} G = lim_J (lim_K G(j, -))$ for a functor `G : J × K ⥤ C`,
when all the appropriate limits exist.

We begin working with a functor `F : J ⥤ K ⥤ C`. We'll write `G : J × K ⥤ C` for the associated
"uncurried" functor.

In the first part, given a coherent family `D` of limit cones over the functors `F.obj j`,
and a cone `c` over `G`, we construct a cone over the cone points of `D`.
We then show that if `c` is a limit cone, the constructed cone is also a limit cone.

In the second part, we state the Fubini theorem in the setting where limits are
provided by suitable `has_limit` classes.

We construct
`limit_uncurry_iso_limit_comp_lim F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`
and give simp lemmas characterising it.
For convenience, we also provide
`limit_iso_limit_curry_comp_lim G : limit G ≅ limit ((curry.obj G) ⋙ lim)`
in terms of the uncurried functor.

## Future work

The dual statement.
-/


universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {J K : Type v} [SmallCategory J] [SmallCategory K]

variable {C : Type u} [Category.{v} C]

variable (F : J ⥤ K ⥤ C)

-- We could try introducing a "dependent functor type" to handle this?
/-- A structure carrying a diagram of cones over the functors `F.obj j`.
-/
structure DiagramOfCones where
  obj : ∀ j : J, Cone (F.obj j)
  map : ∀ {j j' : J} (f : j ⟶ j'), (Cones.postcompose (F.map f)).obj (obj j) ⟶ obj j'
  id : ∀ j : J, (map (𝟙 j)).Hom = 𝟙 _ := by obviously
  comp :
    ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
      (map (f ≫ g)).Hom = (map f).Hom ≫ (map g).Hom := by
    obviously
#align category_theory.limits.diagram_of_cones CategoryTheory.Limits.DiagramOfCones

variable {F}

/-- Extract the functor `J ⥤ C` consisting of the cone points and the maps between them,
from a `diagram_of_cones`.
-/
@[simps]
def DiagramOfCones.conePoints (D : DiagramOfCones F) : J ⥤ C
    where
  obj j := (D.obj j).pt
  map j j' f := (D.map f).Hom
  map_id' j := D.id j
  map_comp' j₁ j₂ j₃ f g := D.comp f g
#align category_theory.limits.diagram_of_cones.cone_points CategoryTheory.Limits.DiagramOfCones.conePoints

/-- Given a diagram `D` of limit cones over the `F.obj j`, and a cone over `uncurry.obj F`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
def coneOfConeUncurry {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    (c : Cone (uncurry.obj F)) : Cone D.conePoints
    where
  pt := c.pt
  π :=
    { app := fun j =>
        (Q j).lift
          { pt := c.pt
            π :=
              { app := fun k => c.π.app (j, k)
                naturality' := fun k k' f => by
                  dsimp; simp only [category.id_comp]
                  have := @nat_trans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f)
                  dsimp at this
                  simp only [category.id_comp, CategoryTheory.Functor.map_id, nat_trans.id_app] at
                    this
                  exact this } }
      naturality' := fun j j' f =>
        (Q j').hom_ext
          (by
            dsimp
            intro k
            simp only [limits.cone_morphism.w, limits.cones.postcompose_obj_π,
              limits.is_limit.fac_assoc, limits.is_limit.fac, nat_trans.comp_app, category.id_comp,
              category.assoc]
            have := @nat_trans.naturality _ _ _ _ _ _ c.π (j, k) (j', k) (f, 𝟙 k)
            dsimp at this
            simp only [category.id_comp, category.comp_id, CategoryTheory.Functor.map_id,
              nat_trans.id_app] at this
            exact this) }
#align category_theory.limits.cone_of_cone_uncurry CategoryTheory.Limits.coneOfConeUncurry

/-- `cone_of_cone_uncurry Q c` is a limit cone when `c` is a limit cone.`
-/
def coneOfConeUncurryIsLimit {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    {c : Cone (uncurry.obj F)} (P : IsLimit c) : IsLimit (coneOfConeUncurry Q c)
    where
  lift s :=
    P.lift
      { pt := s.pt
        π :=
          { app := fun p => s.π.app p.1 ≫ (D.obj p.1).π.app p.2
            naturality' := fun p p' f => by
              dsimp; simp only [category.id_comp, category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, fk⟩
              dsimp
              slice_rhs 3 4 => rw [← nat_trans.naturality]
              slice_rhs 2 3 => rw [← (D.obj j).π.naturality]
              simp only [functor.const_obj_map, category.id_comp, category.assoc]
              have w := (D.map fj).w k'
              dsimp at w
              rw [← w]
              have n := s.π.naturality fj
              dsimp at n
              simp only [category.id_comp] at n
              rw [n]
              simp } }
  fac s j := by
    apply (Q j).hom_ext
    intro k
    simp
  uniq s m w :=
    by
    refine'
      P.uniq
        { pt := s.X
          π := _ } m _
    rintro ⟨j, k⟩
    dsimp
    rw [← w j]
    simp
#align category_theory.limits.cone_of_cone_uncurry_is_limit CategoryTheory.Limits.coneOfConeUncurryIsLimit

section

variable (F)

variable [HasLimitsOfShape K C]

/-- Given a functor `F : J ⥤ K ⥤ C`, with all needed limits,
we can construct a diagram consisting of the limit cone over each functor `F.obj j`,
and the universal cone morphisms between these.
-/
@[simps]
noncomputable def DiagramOfCones.mkOfHasLimits : DiagramOfCones F
    where
  obj j := limit.cone (F.obj j)
  map j j' f := { Hom := lim.map (F.map f) }
#align category_theory.limits.diagram_of_cones.mk_of_has_limits CategoryTheory.Limits.DiagramOfCones.mkOfHasLimits

-- Satisfying the inhabited linter.
noncomputable instance diagramOfConesInhabited : Inhabited (DiagramOfCones F) :=
  ⟨DiagramOfCones.mkOfHasLimits F⟩
#align category_theory.limits.diagram_of_cones_inhabited CategoryTheory.Limits.diagramOfConesInhabited

@[simp]
theorem DiagramOfCones.mkOfHasLimits_conePoints :
    (DiagramOfCones.mkOfHasLimits F).conePoints = F ⋙ lim :=
  rfl
#align category_theory.limits.diagram_of_cones.mk_of_has_limits_cone_points CategoryTheory.Limits.DiagramOfCones.mkOfHasLimits_conePoints

variable [HasLimit (uncurry.obj F)]

variable [HasLimit (F ⋙ lim)]

/-- The Fubini theorem for a functor `F : J ⥤ K ⥤ C`,
showing that the limit of `uncurry.obj F` can be computed as
the limit of the limits of the functors `F.obj j`.
-/
noncomputable def limitUncurryIsoLimitCompLim : limit (uncurry.obj F) ≅ limit (F ⋙ lim) :=
  by
  let c := limit.cone (uncurry.obj F)
  let P : is_limit c := limit.is_limit _
  let G := diagram_of_cones.mk_of_has_limits F
  let Q : ∀ j, is_limit (G.obj j) := fun j => limit.is_limit _
  have Q' := cone_of_cone_uncurry_is_limit Q P
  have Q'' := limit.is_limit (F ⋙ limUnder)
  exact is_limit.cone_point_unique_up_to_iso Q' Q''
#align category_theory.limits.limit_uncurry_iso_limit_comp_lim CategoryTheory.Limits.limitUncurryIsoLimitCompLim

@[simp, reassoc]
theorem limitUncurryIsoLimitCompLim_hom_π_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).Hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) :=
  by
  dsimp [limit_uncurry_iso_limit_comp_lim, is_limit.cone_point_unique_up_to_iso,
    is_limit.unique_up_to_iso]
  simp
#align category_theory.limits.limit_uncurry_iso_limit_comp_lim_hom_π_π CategoryTheory.Limits.limitUncurryIsoLimitCompLim_hom_π_π

@[simp, reassoc]
theorem limitUncurryIsoLimitCompLim_inv_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).inv ≫ limit.π _ (j, k) = limit.π _ j ≫ limit.π _ k :=
  by
  rw [← cancel_epi (limit_uncurry_iso_limit_comp_lim F).Hom]
  simp
#align category_theory.limits.limit_uncurry_iso_limit_comp_lim_inv_π CategoryTheory.Limits.limitUncurryIsoLimitCompLim_inv_π

end

section

variable (F) [HasLimitsOfShape J C] [HasLimitsOfShape K C]

-- With only moderate effort these could be derived if needed:
variable [HasLimitsOfShape (J × K) C] [HasLimitsOfShape (K × J) C]

/-- The limit of `F.flip ⋙ lim` is isomorphic to the limit of `F ⋙ lim`. -/
noncomputable def limitFlipCompLimIsoLimitCompLim : limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim) :=
  (limitUncurryIsoLimitCompLim _).symm ≪≫
    HasLimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasLimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents (fun _ => by rfl) (by tidy)) ≪≫
        limitUncurryIsoLimitCompLim _
#align category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim

@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim_hom_π_π (j) (k) :
    (limitFlipCompLimIsoLimitCompLim F).Hom ≫ limit.π _ j ≫ limit.π _ k =
      limit.π _ k ≫ limit.π _ j :=
  by
  dsimp [limit_flip_comp_lim_iso_limit_comp_lim]
  simp
  dsimp
  simp
#align category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim_hom_π_π CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim_hom_π_π

-- See note [dsimp, simp]
@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim_inv_π_π (k) (j) :
    (limitFlipCompLimIsoLimitCompLim F).inv ≫ limit.π _ k ≫ limit.π _ j =
      limit.π _ j ≫ limit.π _ k :=
  by
  dsimp [limit_flip_comp_lim_iso_limit_comp_lim]
  simp
  dsimp
  simp
  dsimp
  simp
#align category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim_inv_π_π CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim_inv_π_π

end

section

variable (G : J × K ⥤ C)

section

variable [HasLimitsOfShape K C]

variable [HasLimit G]

variable [HasLimit (curry.obj G ⋙ lim)]

/-- The Fubini theorem for a functor `G : J × K ⥤ C`,
showing that the limit of `G` can be computed as
the limit of the limits of the functors `G.obj (j, _)`.
-/
noncomputable def limitIsoLimitCurryCompLim : limit G ≅ limit (curry.obj G ⋙ lim) :=
  by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unit_iso.app G
  haveI : limits.has_limit (uncurry.obj ((@curry J _ K _ C _).obj G)) := has_limit_of_iso i
  trans limit (uncurry.obj ((@curry J _ K _ C _).obj G))
  apply has_limit.iso_of_nat_iso i
  exact limit_uncurry_iso_limit_comp_lim ((@curry J _ K _ C _).obj G)
#align category_theory.limits.limit_iso_limit_curry_comp_lim CategoryTheory.Limits.limitIsoLimitCurryCompLim

@[simp, reassoc]
theorem limitIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitIsoLimitCurryCompLim G).Hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  simp [limit_iso_limit_curry_comp_lim, is_limit.cone_point_unique_up_to_iso,
    is_limit.unique_up_to_iso]
#align category_theory.limits.limit_iso_limit_curry_comp_lim_hom_π_π CategoryTheory.Limits.limitIsoLimitCurryCompLim_hom_π_π

@[simp, reassoc]
theorem limitIsoLimitCurryCompLim_inv_π {j} {k} :
    (limitIsoLimitCurryCompLim G).inv ≫ limit.π _ (j, k) = limit.π _ j ≫ limit.π _ k :=
  by
  rw [← cancel_epi (limit_iso_limit_curry_comp_lim G).Hom]
  simp
#align category_theory.limits.limit_iso_limit_curry_comp_lim_inv_π CategoryTheory.Limits.limitIsoLimitCurryCompLim_inv_π

end

section

variable [HasLimits C]

-- Certainly one could weaken the hypotheses here.
open CategoryTheory.prod

/-- A variant of the Fubini theorem for a functor `G : J × K ⥤ C`,
showing that $\lim_k \lim_j G(j,k) ≅ \lim_j \lim_k G(j,k)$.
-/
noncomputable def limitCurrySwapCompLimIsoLimitCurryCompLim :
    limit (curry.obj (swap K J ⋙ G) ⋙ lim) ≅ limit (curry.obj G ⋙ lim) :=
  calc
    limit (curry.obj (swap K J ⋙ G) ⋙ lim) ≅ limit (swap K J ⋙ G) :=
      (limitIsoLimitCurryCompLim _).symm
    _ ≅ limit G := (HasLimit.isoOfEquivalence (braiding K J) (Iso.refl _))
    _ ≅ limit (curry.obj G ⋙ lim) := limitIsoLimitCurryCompLim _
    
#align category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim

@[simp]
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).Hom ≫ limit.π _ j ≫ limit.π _ k =
      limit.π _ k ≫ limit.π _ j :=
  by
  dsimp [limit_curry_swap_comp_lim_iso_limit_curry_comp_lim]
  simp only [iso.refl_hom, braiding_counit_iso_hom_app, limits.has_limit.iso_of_equivalence_hom_π,
    iso.refl_inv, limit_iso_limit_curry_comp_lim_hom_π_π, eq_to_iso_refl, category.assoc]
  erw [nat_trans.id_app]
  -- Why can't `simp` do this`?
  dsimp;
  simp
#align category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_hom_π_π CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π

@[simp]
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).inv ≫ limit.π _ k ≫ limit.π _ j =
      limit.π _ j ≫ limit.π _ k :=
  by
  dsimp [limit_curry_swap_comp_lim_iso_limit_curry_comp_lim]
  simp only [iso.refl_hom, braiding_counit_iso_hom_app, limits.has_limit.iso_of_equivalence_inv_π,
    iso.refl_inv, limit_iso_limit_curry_comp_lim_hom_π_π, eq_to_iso_refl, category.assoc]
  erw [nat_trans.id_app]
  -- Why can't `simp` do this`?
  dsimp;
  simp
#align category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_inv_π_π CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π

end

end

end CategoryTheory.Limits

