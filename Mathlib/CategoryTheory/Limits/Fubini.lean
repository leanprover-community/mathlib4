/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Functor.Currying

#align_import category_theory.limits.fubini from "leanprover-community/mathlib"@"59382264386afdbaf1727e617f5fdda511992eb9"

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
provided by suitable `HasLimit` classes.

We construct
`limitUncurryIsoLimitCompLim F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`
and give simp lemmas characterising it.
For convenience, we also provide
`limitIsoLimitCurryCompLim G : limit G ≅ limit ((curry.obj G) ⋙ lim)`
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
  id : ∀ j : J, (map (𝟙 j)).Hom = 𝟙 _ := by aesop_cat
  comp : ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).Hom = (map f).Hom ≫ (map g).Hom := by aesop_cat
#align category_theory.limits.diagram_of_cones CategoryTheory.Limits.DiagramOfCones

variable {F}

/-- Extract the functor `J ⥤ C` consisting of the cone points and the maps between them,
from a `DiagramOfCones`.
-/
@[simps]
def DiagramOfCones.conePoints (D : DiagramOfCones F) : J ⥤ C where
  obj j := (D.obj j).pt
  map f := (D.map f).Hom
  map_id j := D.id j
  map_comp f g := D.comp f g
#align category_theory.limits.diagram_of_cones.cone_points CategoryTheory.Limits.DiagramOfCones.conePoints

/-- Given a diagram `D` of limit cones over the `F.obj j`, and a cone over `uncurry.obj F`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
def coneOfConeUncurry {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    (c : Cone (uncurry.obj F)) : Cone D.conePoints where
  pt := c.pt
  π :=
    { app := fun j =>
        (Q j).lift
          { pt := c.pt
            π :=
              { app := fun k => c.π.app (j, k)
                naturality := fun k k' f => by
                  dsimp; simp only [Category.id_comp]
                  have := @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f)
                  dsimp at this
                  simp? at this says
                    simp only [Category.id_comp, Functor.map_id, NatTrans.id_app] at this
                  exact this } }
      naturality := fun j j' f =>
        (Q j').hom_ext
          (by
            dsimp
            intro k
            simp only [Limits.ConeMorphism.w, Limits.Cones.postcompose_obj_π,
              Limits.IsLimit.fac_assoc, Limits.IsLimit.fac, NatTrans.comp_app, Category.id_comp,
              Category.assoc]
            have := @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j', k) (f, 𝟙 k)
            dsimp at this
            simp only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
              NatTrans.id_app] at this
            exact this) }
#align category_theory.limits.cone_of_cone_uncurry CategoryTheory.Limits.coneOfConeUncurry

/-- `coneOfConeUncurry Q c` is a limit cone when `c` is a limit cone.
-/
def coneOfConeUncurryIsLimit {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    {c : Cone (uncurry.obj F)} (P : IsLimit c) : IsLimit (coneOfConeUncurry Q c) where
  lift s :=
    P.lift
      { pt := s.pt
        π :=
          { app := fun p => s.π.app p.1 ≫ (D.obj p.1).π.app p.2
            naturality := fun p p' f => by
              dsimp; simp only [Category.id_comp, Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, fk⟩
              dsimp
              slice_rhs 3 4 => rw [← NatTrans.naturality]
              slice_rhs 2 3 => rw [← (D.obj j).π.naturality]
              simp only [Functor.const_obj_map, Category.id_comp, Category.assoc]
              have w := (D.map fj).w k'
              dsimp at w
              rw [← w]
              have n := s.π.naturality fj
              dsimp at n
              simp only [Category.id_comp] at n
              rw [n]
              simp } }
  fac s j := by
    apply (Q j).hom_ext
    intro k
    simp
  uniq s m w := by
    refine' P.uniq
      { pt := s.pt
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
noncomputable def DiagramOfCones.mkOfHasLimits : DiagramOfCones F where
  obj j := limit.cone (F.obj j)
  map f := { Hom := lim.map (F.map f) }
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
noncomputable def limitUncurryIsoLimitCompLim : limit (uncurry.obj F) ≅ limit (F ⋙ lim) := by
  let c := limit.cone (uncurry.obj F)
  let P : IsLimit c := limit.isLimit _
  let G := DiagramOfCones.mkOfHasLimits F
  let Q : ∀ j, IsLimit (G.obj j) := fun j => limit.isLimit _
  have Q' := coneOfConeUncurryIsLimit Q P
  have Q'' := limit.isLimit (F ⋙ lim)
  exact IsLimit.conePointUniqueUpToIso Q' Q''
#align category_theory.limits.limit_uncurry_iso_limit_comp_lim CategoryTheory.Limits.limitUncurryIsoLimitCompLim

@[simp, reassoc]
theorem limitUncurryIsoLimitCompLim_hom_π_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  dsimp [limitUncurryIsoLimitCompLim, IsLimit.conePointUniqueUpToIso, IsLimit.uniqueUpToIso]
  simp
#align category_theory.limits.limit_uncurry_iso_limit_comp_lim_hom_π_π CategoryTheory.Limits.limitUncurryIsoLimitCompLim_hom_π_π

-- Porting note: Added type annotation `limit (_ ⋙ lim) ⟶ _`
@[simp, reassoc]
theorem limitUncurryIsoLimitCompLim_inv_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).inv ≫ limit.π _ (j, k) =
      (limit.π _ j ≫ limit.π _ k : limit (_ ⋙ lim) ⟶ _) := by
  rw [← cancel_epi (limitUncurryIsoLimitCompLim F).hom]
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
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        limitUncurryIsoLimitCompLim _
#align category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim

-- Porting note: Added type annotation `limit (_ ⋙ lim) ⟶ _`
@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim_hom_π_π (j) (k) :
    (limitFlipCompLimIsoLimitCompLim F).hom ≫ limit.π _ j ≫ limit.π _ k =
      (limit.π _ k ≫ limit.π _ j : limit (_ ⋙ lim) ⟶ _) := by
  dsimp [limitFlipCompLimIsoLimitCompLim]
  simp
#align category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim_hom_π_π CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim_hom_π_π

-- Porting note: Added type annotation `limit (_ ⋙ lim) ⟶ _`
-- See note [dsimp, simp]
@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim_inv_π_π (k) (j) :
    (limitFlipCompLimIsoLimitCompLim F).inv ≫ limit.π _ k ≫ limit.π _ j =
      (limit.π _ j ≫ limit.π _ k : limit (_ ⋙ lim) ⟶ _) := by
  dsimp [limitFlipCompLimIsoLimitCompLim]
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
noncomputable def limitIsoLimitCurryCompLim : limit G ≅ limit (curry.obj G ⋙ lim) := by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasLimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasLimitOfIso i
  trans limit (uncurry.obj ((@curry J _ K _ C _).obj G))
  apply HasLimit.isoOfNatIso i
  exact limitUncurryIsoLimitCompLim ((@curry J _ K _ C _).obj G)
#align category_theory.limits.limit_iso_limit_curry_comp_lim CategoryTheory.Limits.limitIsoLimitCurryCompLim

@[simp, reassoc]
theorem limitIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitIsoLimitCurryCompLim G).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  simp [limitIsoLimitCurryCompLim, Trans.simple, HasLimit.isoOfNatIso, limitUncurryIsoLimitCompLim]
#align category_theory.limits.limit_iso_limit_curry_comp_lim_hom_π_π CategoryTheory.Limits.limitIsoLimitCurryCompLim_hom_π_π

-- Porting note: Added type annotation `limit (_ ⋙ lim) ⟶ _`
@[simp, reassoc]
theorem limitIsoLimitCurryCompLim_inv_π {j} {k} :
    (limitIsoLimitCurryCompLim G).inv ≫ limit.π _ (j, k) =
      (limit.π _ j ≫ limit.π _ k : limit (_ ⋙ lim) ⟶ _) := by
  rw [← cancel_epi (limitIsoLimitCurryCompLim G).hom]
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
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (curry.obj G ⋙ lim) :=
  calc
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (Prod.swap K J ⋙ G) :=
      (limitIsoLimitCurryCompLim _).symm
    _ ≅ limit G := (HasLimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _))
    _ ≅ limit (curry.obj G ⋙ lim) := limitIsoLimitCurryCompLim _
#align category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim

-- Porting note: Added type annotation `limit (_ ⋙ lim) ⟶ _`
@[simp]
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).hom ≫ limit.π _ j ≫ limit.π _ k =
      (limit.π _ k ≫ limit.π _ j : limit (_ ⋙ lim) ⟶ _) := by
  dsimp [limitCurrySwapCompLimIsoLimitCurryCompLim]
  simp only [Iso.refl_hom, Prod.braiding_counitIso_hom_app, Limits.HasLimit.isoOfEquivalence_hom_π,
    Iso.refl_inv, limitIsoLimitCurryCompLim_hom_π_π, eqToIso_refl, Category.assoc]
  erw [NatTrans.id_app]
  -- Why can't `simp` do this?
  dsimp
  -- porting note: the original proof only had `simp`.
  -- However, now `CategoryTheory.Bifunctor.map_id` does not get used by `simp`
  rw [CategoryTheory.Bifunctor.map_id]
  simp

#align category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_hom_π_π CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π

-- Porting note: Added type annotation `limit (_ ⋙ lim) ⟶ _`
@[simp]
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).inv ≫ limit.π _ k ≫ limit.π _ j =
      (limit.π _ j ≫ limit.π _ k : limit (_ ⋙ lim) ⟶ _) := by
  dsimp [limitCurrySwapCompLimIsoLimitCurryCompLim]
  simp only [Iso.refl_hom, Prod.braiding_counitIso_hom_app, Limits.HasLimit.isoOfEquivalence_inv_π,
    Iso.refl_inv, limitIsoLimitCurryCompLim_hom_π_π, eqToIso_refl, Category.assoc]
  erw [NatTrans.id_app]
  -- Porting note: `simp` can do this in lean 4.
  simp
#align category_theory.limits.limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_inv_π_π CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π

end

end

end CategoryTheory.Limits
