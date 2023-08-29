/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

#align_import algebraic_geometry.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# Fibred products of schemes

In this file we construct the fibred product of schemes via gluing.
We roughly follow [har77] Theorem 3.3.

In particular, the main construction is to show that for an open cover `{ Uᵢ }` of `X`, if there
exist fibred products `Uᵢ ×[Z] Y` for each `i`, then there exists a fibred product `X ×[Z] Y`.

Then, for constructing the fibred product for arbitrary schemes `X, Y, Z`, we can use the
construction to reduce to the case where `X, Y, Z` are all affine, where fibred products are
constructed via tensor products.

-/

set_option linter.uppercaseLean3 false

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

namespace Pullback

variable {C : Type u} [Category.{v} C]

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover.{u} X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ i, HasPullback (𝒰.map i ≫ f) g]

/-- The intersection of `Uᵢ ×[Z] Y` and `Uⱼ ×[Z] Y` is given by (Uᵢ ×[Z] Y) ×[X] Uⱼ -/
def v (i j : 𝒰.J) : Scheme :=
  pullback ((pullback.fst : pullback (𝒰.map i ≫ f) g ⟶ _) ≫ 𝒰.map i) (𝒰.map j)
#align algebraic_geometry.Scheme.pullback.V AlgebraicGeometry.Scheme.Pullback.v

/-- The canonical transition map `(Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ` given by the fact
that pullbacks are associative and symmetric. -/
def t (i j : 𝒰.J) : v 𝒰 f g i j ⟶ v 𝒰 f g j i := by
  haveI : HasPullback (pullback.snd ≫ 𝒰.map i ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map j) (𝒰.map i) (𝒰.map i ≫ f) g
  haveI : HasPullback (pullback.snd ≫ 𝒰.map j ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map i) (𝒰.map j) (𝒰.map j ≫ f) g
  refine' (pullbackSymmetry _ _).hom ≫ _
  -- ⊢ pullback (OpenCover.map 𝒰 j) (pullback.fst ≫ OpenCover.map 𝒰 i) ⟶ v 𝒰 f g j i
  refine' (pullbackAssoc _ _ _ _).inv ≫ _
  -- ⊢ pullback (pullback.snd ≫ OpenCover.map 𝒰 i ≫ f) g ⟶ v 𝒰 f g j i
  change pullback _ _ ⟶ pullback _ _
  -- ⊢ pullback (pullback.snd ≫ OpenCover.map 𝒰 i ≫ f) g ⟶ pullback (pullback.fst ≫ …
  refine' _ ≫ (pullbackSymmetry _ _).hom
  -- ⊢ pullback (pullback.snd ≫ OpenCover.map 𝒰 i ≫ f) g ⟶ pullback (OpenCover.map  …
  refine' _ ≫ (pullbackAssoc _ _ _ _).hom
  -- ⊢ pullback (pullback.snd ≫ OpenCover.map 𝒰 i ≫ f) g ⟶ pullback (pullback.snd ≫ …
  refine' pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) _ _
  -- ⊢ (pullback.snd ≫ OpenCover.map 𝒰 i ≫ f) ≫ 𝟙 Z = (pullbackSymmetry (OpenCover. …
  rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition_assoc, Category.comp_id]
  -- ⊢ g ≫ 𝟙 Z = 𝟙 Y ≫ g
  rw [Category.comp_id, Category.id_comp]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.t AlgebraicGeometry.Scheme.Pullback.t

@[simp, reassoc]
theorem t_fst_fst (i j : 𝒰.J) : t 𝒰 f g i j ≫ pullback.fst ≫ pullback.fst = pullback.snd := by
  delta t
  -- ⊢ ((pullbackSymmetry (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover.map 𝒰 j)).h …
  -- Porting note : copied from previous definition, otherwise `simp` wouldn't work
  haveI : HasPullback (pullback.snd ≫ 𝒰.map i ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map j) (𝒰.map i) (𝒰.map i ≫ f) g
  haveI : HasPullback (pullback.snd ≫ 𝒰.map j ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map i) (𝒰.map j) (𝒰.map j ≫ f) g
  simp only [Category.assoc, id.def, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackAssoc_hom_snd_fst, pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_snd,
    pullbackAssoc_inv_fst_fst, pullbackSymmetry_hom_comp_fst]
#align algebraic_geometry.Scheme.pullback.t_fst_fst AlgebraicGeometry.Scheme.Pullback.t_fst_fst

@[simp, reassoc]
theorem t_fst_snd (i j : 𝒰.J) :
    t 𝒰 f g i j ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd := by
  delta t
  -- ⊢ ((pullbackSymmetry (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover.map 𝒰 j)).h …
  -- Porting note : copied from previous definition, otherwise `simp` wouldn't work
  haveI : HasPullback (pullback.snd ≫ 𝒰.map i ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map j) (𝒰.map i) (𝒰.map i ≫ f) g
  haveI : HasPullback (pullback.snd ≫ 𝒰.map j ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map i) (𝒰.map j) (𝒰.map j ≫ f) g
  simp only [pullbackSymmetry_hom_comp_snd_assoc, Category.comp_id, Category.assoc, id.def,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_snd, pullback.lift_snd,
    pullbackAssoc_inv_snd]
#align algebraic_geometry.Scheme.pullback.t_fst_snd AlgebraicGeometry.Scheme.Pullback.t_fst_snd

@[simp, reassoc]
theorem t_snd (i j : 𝒰.J) : t 𝒰 f g i j ≫ pullback.snd = pullback.fst ≫ pullback.fst := by
  delta t
  -- ⊢ ((pullbackSymmetry (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover.map 𝒰 j)).h …
  -- Porting note : copied from previous definition, otherwise `simp` wouldn't work
  haveI : HasPullback (pullback.snd ≫ 𝒰.map i ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map j) (𝒰.map i) (𝒰.map i ≫ f) g
  haveI : HasPullback (pullback.snd ≫ 𝒰.map j ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map i) (𝒰.map j) (𝒰.map j ≫ f) g
  simp only [pullbackSymmetry_hom_comp_snd_assoc, Category.assoc, id.def,
    pullbackSymmetry_hom_comp_snd, pullbackAssoc_hom_fst, pullback.lift_fst_assoc,
    pullbackSymmetry_hom_comp_fst, pullbackAssoc_inv_fst_snd]
#align algebraic_geometry.Scheme.pullback.t_snd AlgebraicGeometry.Scheme.Pullback.t_snd

theorem t_id (i : 𝒰.J) : t 𝒰 f g i i = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  -- ⊢ t 𝒰 f g i i ≫ pullback.fst = 𝟙 (v 𝒰 f g i i) ≫ pullback.fst
                             -- ⊢ t 𝒰 f g i i ≫ pullback.fst = pullback.fst
                             -- ⊢ t 𝒰 f g i i ≫ pullback.snd = pullback.snd
  apply pullback.hom_ext
  · rw [← cancel_mono (𝒰.map i)]; simp only [pullback.condition, Category.assoc, t_fst_fst]
    -- ⊢ ((t 𝒰 f g i i ≫ pullback.fst) ≫ pullback.fst) ≫ OpenCover.map 𝒰 i = (pullbac …
                                  -- 🎉 no goals
  · simp only [Category.assoc, t_fst_snd]
    -- 🎉 no goals
  · rw [← cancel_mono (𝒰.map i)]; simp only [pullback.condition, t_snd, Category.assoc]
    -- ⊢ (t 𝒰 f g i i ≫ pullback.snd) ≫ OpenCover.map 𝒰 i = pullback.snd ≫ OpenCover. …
                                  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.t_id AlgebraicGeometry.Scheme.Pullback.t_id

/-- The inclusion map of `V i j = (Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ Uᵢ ×[Z] Y`-/
abbrev fV (i j : 𝒰.J) : v 𝒰 f g i j ⟶ pullback (𝒰.map i ≫ f) g :=
  pullback.fst
#align algebraic_geometry.Scheme.pullback.fV AlgebraicGeometry.Scheme.Pullback.fV

/-- The map `((Xᵢ ×[Z] Y) ×[X] Xⱼ) ×[Xᵢ ×[Z] Y] ((Xᵢ ×[Z] Y) ×[X] Xₖ)` ⟶
  `((Xⱼ ×[Z] Y) ×[X] Xₖ) ×[Xⱼ ×[Z] Y] ((Xⱼ ×[Z] Y) ×[X] Xᵢ)` needed for gluing   -/
def t' (i j k : 𝒰.J) :
    pullback (fV 𝒰 f g i j) (fV 𝒰 f g i k) ⟶ pullback (fV 𝒰 f g j k) (fV 𝒰 f g j i) := by
  refine' (pullbackRightPullbackFstIso _ _ _).hom ≫ _
  -- ⊢ pullback (fV 𝒰 f g i j ≫ pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover.map 𝒰  …
  refine' _ ≫ (pullbackSymmetry _ _).hom
  -- ⊢ pullback (fV 𝒰 f g i j ≫ pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover.map 𝒰  …
  refine' _ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  -- ⊢ pullback (fV 𝒰 f g i j ≫ pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover.map 𝒰  …
  refine' pullback.map _ _ _ _ (t 𝒰 f g i j) (𝟙 _) (𝟙 _) _ _
  -- ⊢ (fV 𝒰 f g i j ≫ pullback.fst ≫ OpenCover.map 𝒰 i) ≫ 𝟙 X = t 𝒰 f g i j ≫ fV 𝒰 …
  · simp only [← pullback.condition, Category.comp_id, t_fst_fst_assoc]
    -- 🎉 no goals
  · simp only [Category.comp_id, Category.id_comp]
    -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.t' AlgebraicGeometry.Scheme.Pullback.t'

@[simp, reassoc]
theorem t'_fst_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta t'
  -- ⊢ ((pullbackRightPullbackFstIso (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover. …
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_fst_fst_fst AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_fst

@[simp, reassoc]
theorem t'_fst_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst ≫ pullback.snd := by
  delta t'
  -- ⊢ ((pullbackRightPullbackFstIso (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover. …
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_fst_fst_snd AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_snd

@[simp, reassoc]
theorem t'_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta t'
  -- ⊢ ((pullbackRightPullbackFstIso (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover. …
  simp only [Category.comp_id, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd,
    pullbackRightPullbackFstIso_hom_snd]
#align algebraic_geometry.Scheme.pullback.t'_fst_snd AlgebraicGeometry.Scheme.Pullback.t'_fst_snd

@[simp, reassoc]
theorem t'_snd_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta t'
  -- ⊢ ((pullbackRightPullbackFstIso (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover. …
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_snd_fst_fst AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_fst

@[simp, reassoc]
theorem t'_snd_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst ≫ pullback.snd := by
  delta t'
  -- ⊢ ((pullbackRightPullbackFstIso (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover. …
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_snd_fst_snd AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_snd

@[simp, reassoc]
theorem t'_snd_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst := by
  delta t'
  -- ⊢ ((pullbackRightPullbackFstIso (pullback.fst ≫ OpenCover.map 𝒰 i) (OpenCover. …
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_snd_snd AlgebraicGeometry.Scheme.Pullback.t'_snd_snd

theorem cocycle_fst_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst =
      pullback.fst ≫ pullback.fst ≫ pullback.fst :=
  by simp only [t'_fst_fst_fst, t'_fst_snd, t'_snd_snd]
     -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle_fst_fst_fst AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_fst

theorem cocycle_fst_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst ≫ pullback.snd :=
  by simp only [t'_fst_fst_snd]
     -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle_fst_fst_snd AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_snd

theorem cocycle_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.snd :=
  by simp only [t'_fst_snd, t'_snd_snd, t'_fst_fst_fst]
     -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle_fst_snd AlgebraicGeometry.Scheme.Pullback.cocycle_fst_snd

theorem cocycle_snd_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst =
      pullback.snd ≫ pullback.fst ≫ pullback.fst := by
  rw [← cancel_mono (𝒰.map i)]
  -- ⊢ (t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback. …
  simp only [pullback.condition_assoc, t'_snd_fst_fst, t'_fst_snd, t'_snd_snd]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle_snd_fst_fst AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_fst

theorem cocycle_snd_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
      pullback.snd ≫ pullback.fst ≫ pullback.snd :=
  by simp only [pullback.condition_assoc, t'_snd_fst_snd]
     -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle_snd_fst_snd AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_snd

theorem cocycle_snd_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.snd =
      pullback.snd ≫ pullback.snd :=
  by simp only [t'_snd_snd, t'_fst_fst_fst, t'_fst_snd]
     -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle_snd_snd AlgebraicGeometry.Scheme.Pullback.cocycle_snd_snd

-- `by tidy` should solve it, but it times out.
theorem cocycle (i j k : 𝒰.J) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  -- ⊢ (t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.fst = 𝟙 (pullb …
                             -- ⊢ (t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.fst = pullback …
                             -- ⊢ (t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.snd = pullback …
  · apply pullback.hom_ext
    -- ⊢ ((t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.fst) ≫ pullba …
    · apply pullback.hom_ext
      -- ⊢ (((t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.fst) ≫ pullb …
      · simp_rw [Category.assoc]
        -- ⊢ t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.f …
        exact cocycle_fst_fst_fst 𝒰 f g i j k
        -- 🎉 no goals
      · simp_rw [Category.assoc]
        -- ⊢ t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.f …
        exact cocycle_fst_fst_snd 𝒰 f g i j k
        -- 🎉 no goals
    · simp_rw [Category.assoc]
      -- ⊢ t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.s …
      exact cocycle_fst_snd 𝒰 f g i j k
      -- 🎉 no goals
  · apply pullback.hom_ext
    -- ⊢ ((t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.snd) ≫ pullba …
    · apply pullback.hom_ext
      -- ⊢ (((t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j) ≫ pullback.snd) ≫ pullb …
      · simp_rw [Category.assoc]
        -- ⊢ t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.f …
        exact cocycle_snd_fst_fst 𝒰 f g i j k
        -- 🎉 no goals
      · simp_rw [Category.assoc]
        -- ⊢ t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.f …
        exact cocycle_snd_fst_snd 𝒰 f g i j k
        -- 🎉 no goals
    · simp_rw [Category.assoc]
      -- ⊢ t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.s …
      exact cocycle_snd_snd 𝒰 f g i j k
      -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.cocycle AlgebraicGeometry.Scheme.Pullback.cocycle

/-- Given `Uᵢ ×[Z] Y`, this is the glued fibered product `X ×[Z] Y`. -/
@[simps]
def gluing : Scheme.GlueData.{u} where
  J := 𝒰.J
  U i := pullback (𝒰.map i ≫ f) g
  V := fun ⟨i, j⟩ => v 𝒰 f g i j
  -- `p⁻¹(Uᵢ ∩ Uⱼ)` where `p : Uᵢ ×[Z] Y ⟶ Uᵢ ⟶ X`.
  f i j := pullback.fst
  f_id i := inferInstance
  f_open := inferInstance
  t i j := t 𝒰 f g i j
  t_id i := t_id 𝒰 f g i
  t' i j k := t' 𝒰 f g i j k
  t_fac i j k := by
    apply pullback.hom_ext
    -- ⊢ ((fun i j k => t' 𝒰 f g i j k) i j k ≫ pullback.snd) ≫ pullback.fst = (pullb …
    apply pullback.hom_ext
    all_goals
      simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd, t_fst_fst, t_fst_snd, t_snd,
        Category.assoc]
  cocycle i j k := cocycle 𝒰 f g i j k
#align algebraic_geometry.Scheme.pullback.gluing AlgebraicGeometry.Scheme.Pullback.gluing

/-- The first projection from the glued scheme into `X`. -/
def p1 : (gluing 𝒰 f g).glued ⟶ X := by
  fapply Multicoequalizer.desc
  -- ⊢ (b : (GlueData.diagram (gluing 𝒰 f g).toGlueData).R) → MultispanIndex.right  …
  exact fun i => pullback.fst ≫ 𝒰.map i
  -- ⊢ ∀ (a : (GlueData.diagram (gluing 𝒰 f g).toGlueData).L), MultispanIndex.fst ( …
  rintro ⟨i, j⟩
  -- ⊢ MultispanIndex.fst (GlueData.diagram (gluing 𝒰 f g).toGlueData) (i, j) ≫ pul …
  change pullback.fst ≫ _ ≫ 𝒰.map i = (_ ≫ _) ≫ _ ≫ 𝒰.map j
  -- ⊢ pullback.fst ≫ pullback.fst ≫ OpenCover.map 𝒰 i = (GlueData.t (gluing 𝒰 f g) …
  -- Porting note : change `rw` to `erw`
  erw [pullback.condition]
  -- ⊢ pullback.snd ≫ OpenCover.map 𝒰 j = (GlueData.t (gluing 𝒰 f g).toGlueData i j …
  rw [← Category.assoc]
  -- ⊢ pullback.snd ≫ OpenCover.map 𝒰 j = ((GlueData.t (gluing 𝒰 f g).toGlueData i  …
  congr 1
  -- ⊢ pullback.snd = (GlueData.t (gluing 𝒰 f g).toGlueData i j ≫ GlueData.f (gluin …
  rw [Category.assoc]
  -- ⊢ pullback.snd = GlueData.t (gluing 𝒰 f g).toGlueData i j ≫ GlueData.f (gluing …
  exact (t_fst_fst _ _ _ _ _).symm
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.p1 AlgebraicGeometry.Scheme.Pullback.p1

/-- The second projection from the glued scheme into `Y`. -/
def p2 : (gluing 𝒰 f g).glued ⟶ Y := by
  fapply Multicoequalizer.desc
  -- ⊢ (b : (GlueData.diagram (gluing 𝒰 f g).toGlueData).R) → MultispanIndex.right  …
  exact fun i => pullback.snd
  -- ⊢ ∀ (a : (GlueData.diagram (gluing 𝒰 f g).toGlueData).L), MultispanIndex.fst ( …
  rintro ⟨i, j⟩
  -- ⊢ MultispanIndex.fst (GlueData.diagram (gluing 𝒰 f g).toGlueData) (i, j) ≫ pul …
  change pullback.fst ≫ _ = (_ ≫ _) ≫ _
  -- ⊢ pullback.fst ≫ pullback.snd = (GlueData.t (gluing 𝒰 f g).toGlueData i j ≫ Gl …
  rw [Category.assoc]
  -- ⊢ pullback.fst ≫ pullback.snd = GlueData.t (gluing 𝒰 f g).toGlueData i j ≫ Glu …
  exact (t_fst_snd _ _ _ _ _).symm
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.p2 AlgebraicGeometry.Scheme.Pullback.p2

theorem p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g := by
  apply Multicoequalizer.hom_ext
  -- ⊢ ∀ (b : (GlueData.diagram (gluing 𝒰 f g).toGlueData).R), Multicoequalizer.π ( …
  intro i
  -- ⊢ Multicoequalizer.π (GlueData.diagram (gluing 𝒰 f g).toGlueData) i ≫ p1 𝒰 f g …
  erw [Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  -- ⊢ (pullback.fst ≫ OpenCover.map 𝒰 i) ≫ f = pullback.snd ≫ g
  rw [Category.assoc, pullback.condition]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.p_comm AlgebraicGeometry.Scheme.Pullback.p_comm

variable (s : PullbackCone f g)

/-- (Implementation)
The canonical map `(s.X ×[X] Uᵢ) ×[s.X] (s.X ×[X] Uⱼ) ⟶ (Uᵢ ×[Z] Y) ×[X] Uⱼ`

This is used in `gluedLift`. -/
def gluedLiftPullbackMap (i j : 𝒰.J) :
    pullback ((𝒰.pullbackCover s.fst).map i) ((𝒰.pullbackCover s.fst).map j) ⟶
      (gluing 𝒰 f g).V ⟨i, j⟩ := by
  change pullback pullback.fst pullback.fst ⟶ pullback _ _
  -- ⊢ pullback pullback.fst pullback.fst ⟶ pullback (pullback.fst ≫ OpenCover.map  …
  refine' (pullbackRightPullbackFstIso _ _ _).hom ≫ _
  -- ⊢ pullback (pullback.fst ≫ PullbackCone.fst s) (OpenCover.map 𝒰 j) ⟶ pullback  …
  refine' pullback.map _ _ _ _ _ (𝟙 _) (𝟙 _) _ _
  · exact (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition
  · simpa using pullback.condition
    -- 🎉 no goals
  · simp only [Category.comp_id, Category.id_comp]
    -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_lift_pullback_map AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap

@[reassoc]
theorem gluedLiftPullbackMap_fst (i j : 𝒰.J) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.fst =
      pullback.fst ≫
        (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition := by
  delta gluedLiftPullbackMap
  -- ⊢ (let_fun this := (pullbackRightPullbackFstIso (PullbackCone.fst s) (OpenCove …
  -- Porting note : the original set of simp lemma is not sufficient, but as this is terminal
  -- I just let `simp` do its work
  simp
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_lift_pullback_map_fst AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap_fst

@[reassoc]
theorem gluedLiftPullbackMap_snd (i j : 𝒰.J) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta gluedLiftPullbackMap
  -- ⊢ (let_fun this := (pullbackRightPullbackFstIso (PullbackCone.fst s) (OpenCove …
  -- Porting note : the original set of simp lemma is not sufficient, but as this is terminal
  -- I just let `simp` do its work
  simp
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_lift_pullback_map_snd AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap_snd

/-- The lifted map `s.X ⟶ (gluing 𝒰 f g).glued` in order to show that `(gluing 𝒰 f g).glued` is
indeed the pullback.

Given a pullback cone `s`, we have the maps `s.fst ⁻¹' Uᵢ ⟶ Uᵢ` and
`s.fst ⁻¹' Uᵢ ⟶ s.X ⟶ Y` that we may lift to a map `s.fst ⁻¹' Uᵢ ⟶ Uᵢ ×[Z] Y`.

to glue these into a map `s.X ⟶ Uᵢ ×[Z] Y`, we need to show that the maps agree on
`(s.fst ⁻¹' Uᵢ) ×[s.X] (s.fst ⁻¹' Uⱼ) ⟶ Uᵢ ×[Z] Y`. This is achieved by showing that both of these
maps factors through `gluedLiftPullbackMap`.
-/
def gluedLift : s.pt ⟶ (gluing 𝒰 f g).glued := by
  fapply (𝒰.pullbackCover s.fst).glueMorphisms
  -- ⊢ (x : (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)).J) → OpenCover.obj (Op …
  · exact fun i => (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition ≫
        (gluing 𝒰 f g).ι i
  intro i j
  -- ⊢ pullback.fst ≫ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 i)).h …
  rw [← gluedLiftPullbackMap_fst_assoc]
  -- ⊢ gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.fst ≫ GlueData.ι (gluing 𝒰 f g)  …
  have : _ = pullback.fst ≫ _ := (gluing 𝒰 f g).glue_condition i j
  -- ⊢ gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.fst ≫ GlueData.ι (gluing 𝒰 f g)  …
  rw [← this, gluing_t, gluing_f]
  -- ⊢ gluedLiftPullbackMap 𝒰 f g s i j ≫ t 𝒰 f g i j ≫ pullback.fst ≫ GlueData.ι ( …
  simp_rw [← Category.assoc]
  -- ⊢ ((gluedLiftPullbackMap 𝒰 f g s i j ≫ t 𝒰 f g i j) ≫ pullback.fst) ≫ GlueData …
  congr 1
  -- ⊢ (gluedLiftPullbackMap 𝒰 f g s i j ≫ t 𝒰 f g i j) ≫ pullback.fst = (pullback. …
  apply pullback.hom_ext <;> simp_rw [Category.assoc]
  -- ⊢ ((gluedLiftPullbackMap 𝒰 f g s i j ≫ t 𝒰 f g i j) ≫ pullback.fst) ≫ pullback …
                             -- ⊢ gluedLiftPullbackMap 𝒰 f g s i j ≫ t 𝒰 f g i j ≫ pullback.fst ≫ pullback.fst …
                             -- ⊢ gluedLiftPullbackMap 𝒰 f g s i j ≫ t 𝒰 f g i j ≫ pullback.fst ≫ pullback.snd …
  · rw [t_fst_fst, gluedLiftPullbackMap_snd]
    -- ⊢ pullback.snd ≫ pullback.snd = pullback.snd ≫ (pullbackSymmetry (PullbackCone …
    congr 1
    -- ⊢ pullback.snd = (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 j)).h …
    rw [← Iso.inv_comp_eq, pullbackSymmetry_inv_comp_snd]
    -- ⊢ pullback.fst = pullback.map (OpenCover.map 𝒰 j) (PullbackCone.fst s) (OpenCo …
    erw [pullback.lift_fst]
    -- ⊢ pullback.fst = pullback.fst ≫ 𝟙 (OpenCover.obj 𝒰 j)
    rw [Category.comp_id]
    -- 🎉 no goals
  · rw [t_fst_snd, gluedLiftPullbackMap_fst_assoc]
    -- ⊢ pullback.fst ≫ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 i)).h …
    erw [pullback.lift_snd, pullback.lift_snd]
    -- ⊢ pullback.fst ≫ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 i)).h …
    rw [pullbackSymmetry_hom_comp_snd_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    -- ⊢ pullback.fst ≫ pullback.fst ≫ PullbackCone.snd s = pullback.snd ≫ pullback.f …
    exact pullback.condition_assoc _
    -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_lift AlgebraicGeometry.Scheme.Pullback.gluedLift

theorem gluedLift_p1 : gluedLift 𝒰 f g s ≫ p1 𝒰 f g = s.fst := by
  rw [← cancel_epi (𝒰.pullbackCover s.fst).fromGlued]
  -- ⊢ OpenCover.fromGlued (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) ≫ glued …
  apply Multicoequalizer.hom_ext
  -- ⊢ ∀ (b : (GlueData.diagram (OpenCover.gluedCover (OpenCover.pullbackCover 𝒰 (P …
  intro b
  -- ⊢ Multicoequalizer.π (GlueData.diagram (OpenCover.gluedCover (OpenCover.pullba …
  erw [Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  -- ⊢ OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) b ≫ gluedLift …
  delta gluedLift
  -- ⊢ OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) b ≫ OpenCover …
  simp_rw [← Category.assoc]
  -- ⊢ (OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) b ≫ OpenCove …
  rw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  -- ⊢ (((pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 b)).hom ≫ pullback …
  simp_rw [Category.assoc]
  -- ⊢ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 b)).hom ≫ pullback.m …
  -- Porting note : `Category.comp_id` is no longer necessary, don't know where `𝟙 _` has gone
  erw [Multicoequalizer.π_desc, pullback.lift_fst_assoc, pullback.condition]
  -- ⊢ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 b)).hom ≫ pullback.s …
  rw [pullbackSymmetry_hom_comp_snd_assoc]
  -- ⊢ pullback.fst ≫ PullbackCone.fst s = OpenCover.map (OpenCover.pullbackCover 𝒰 …
  rfl
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_lift_p1 AlgebraicGeometry.Scheme.Pullback.gluedLift_p1

theorem gluedLift_p2 : gluedLift 𝒰 f g s ≫ p2 𝒰 f g = s.snd := by
  rw [← cancel_epi (𝒰.pullbackCover s.fst).fromGlued]
  -- ⊢ OpenCover.fromGlued (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) ≫ glued …
  apply Multicoequalizer.hom_ext
  -- ⊢ ∀ (b : (GlueData.diagram (OpenCover.gluedCover (OpenCover.pullbackCover 𝒰 (P …
  intro b
  -- ⊢ Multicoequalizer.π (GlueData.diagram (OpenCover.gluedCover (OpenCover.pullba …
  erw [Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  -- ⊢ OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) b ≫ gluedLift …
  delta gluedLift
  -- ⊢ OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) b ≫ OpenCover …
  simp_rw [← Category.assoc]
  -- ⊢ (OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) b ≫ OpenCove …
  rw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  -- ⊢ (((pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 b)).hom ≫ pullback …
  simp_rw [Category.assoc]
  -- ⊢ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 b)).hom ≫ pullback.m …
  erw [Multicoequalizer.π_desc, pullback.lift_snd]
  -- ⊢ (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 b)).hom ≫ pullback.s …
  rw [pullbackSymmetry_hom_comp_snd_assoc]
  -- ⊢ pullback.fst ≫ PullbackCone.snd s = OpenCover.map (OpenCover.pullbackCover 𝒰 …
  rfl
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_lift_p2 AlgebraicGeometry.Scheme.Pullback.gluedLift_p2

/-- (Implementation)
The canonical map `(W ×[X] Uᵢ) ×[W] (Uⱼ ×[Z] Y) ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ = V j i` where `W` is
the glued fibred product.

This is used in `lift_comp_ι`. -/
def pullbackFstιToV (i j : 𝒰.J) :
    pullback (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map i) ⟶ _) ((gluing 𝒰 f g).ι j) ⟶
      v 𝒰 f g j i :=
  (pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) _).hom ≫
    (pullback.congrHom (Multicoequalizer.π_desc _ _ _ _ _) rfl).hom
#align algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V AlgebraicGeometry.Scheme.Pullback.pullbackFstιToV

@[simp, reassoc]
theorem pullbackFstιToV_fst (i j : 𝒰.J) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.fst = pullback.snd := by
  delta pullbackFstιToV
  -- ⊢ ((pullbackSymmetry pullback.fst (GlueData.ι (gluing 𝒰 f g) j) ≪≫ pullbackRig …
  simp only [Iso.trans_hom, pullback.congrHom_hom, Category.assoc, pullback.lift_fst,
    Category.comp_id]
  -- Porting note : `pullbackRightPullbackFstIso_hom_fst` is not used in `simp` even though
  -- instructed, forcing `pullbackSymmetry_hom_comp_fst` to be manually `rw`ed as well.
  erw [pullbackRightPullbackFstIso_hom_fst]
  -- ⊢ (pullbackSymmetry pullback.fst (GlueData.ι (gluing 𝒰 f g) j)).hom ≫ pullback …
  rw [pullbackSymmetry_hom_comp_fst]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V_fst AlgebraicGeometry.Scheme.Pullback.pullbackFstιToV_fst

@[simp, reassoc]
theorem pullbackFstιToV_snd (i j : 𝒰.J) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.snd = pullback.fst ≫ pullback.snd := by
  delta pullbackFstιToV
  -- ⊢ ((pullbackSymmetry pullback.fst (GlueData.ι (gluing 𝒰 f g) j) ≪≫ pullbackRig …
  simp only [Iso.trans_hom, pullback.congrHom_hom, Category.assoc, pullback.lift_snd,
    Category.comp_id]
  -- Porting note : `pullbackRightPullbackFstIso_hom_snd` is not used in `simp` even though
  -- instructed, forcing `pullbackSymmetry_hom_comp_snd_assoc` to be manually `rw`ed as well.
  erw [pullbackRightPullbackFstIso_hom_snd]
  -- ⊢ (pullbackSymmetry pullback.fst (GlueData.ι (gluing 𝒰 f g) j)).hom ≫ pullback …
  rw [pullbackSymmetry_hom_comp_snd_assoc]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V_snd AlgebraicGeometry.Scheme.Pullback.pullbackFstιToV_snd

/-- We show that the map `W ×[X] Uᵢ ⟶ Uᵢ ×[Z] Y ⟶ W` is the first projection, where the
first map is given by the lift of `W ×[X] Uᵢ ⟶ Uᵢ` and `W ×[X] Uᵢ ⟶ W ⟶ Y`.

It suffices to show that the two map agrees when restricted onto `Uⱼ ×[Z] Y`. In this case,
both maps factor through `V j i` via `pullback_fst_ι_to_V` -/
theorem lift_comp_ι (i : 𝒰.J) :
    pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
          (by rw [← pullback.condition_assoc, Category.assoc, p_comm]) ≫
              -- 🎉 no goals
        (gluing 𝒰 f g).ι i =
      (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map i) ⟶ _) := by
  apply ((gluing 𝒰 f g).openCover.pullbackCover pullback.fst).hom_ext
  -- ⊢ ∀ (x : (OpenCover.pullbackCover (GlueData.openCover (gluing 𝒰 f g)) pullback …
  intro j
  -- ⊢ OpenCover.map (OpenCover.pullbackCover (GlueData.openCover (gluing 𝒰 f g)) p …
  dsimp only [OpenCover.pullbackCover]
  -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
  trans pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i ≫ (gluing 𝒰 f g).ι _
  -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
  · rw [← show _ = fV 𝒰 f g j i ≫ _ from (gluing 𝒰 f g).glue_condition j i]
    -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
    simp_rw [← Category.assoc]
    -- ⊢ (pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pu …
    congr 1
    -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
    rw [gluing_f, gluing_t]
    -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
    apply pullback.hom_ext <;> simp_rw [Category.assoc]
    -- ⊢ (pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pu …
                               -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
                               -- ⊢ pullback.fst ≫ pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pul …
    -- Porting note : in the following two bullet points, `rfl` was not necessary
    · rw [t_fst_fst, pullback.lift_fst, pullbackFstιToV_snd]; rfl
      -- ⊢ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd
                                                              -- 🎉 no goals
    · rw [t_fst_snd, pullback.lift_snd, pullbackFstιToV_fst_assoc, pullback.condition_assoc]
      -- ⊢ pullback.snd ≫ OpenCover.map (GlueData.openCover (gluing 𝒰 f g)) j ≫ p2 𝒰 f  …
      erw [Multicoequalizer.π_desc]
      -- ⊢ pullback.snd ≫ pullback.snd = pullback.snd ≫ pullback.snd
      rfl
      -- 🎉 no goals
  · rw [pullback.condition, ← Category.assoc]
    -- ⊢ (pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i) ≫ GlueData.ι (gluing 𝒰 f g) j = p …
    congr 1
    -- ⊢ pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i = pullback.snd
    apply pullback.hom_ext
    -- ⊢ (pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i) ≫ pullback.fst = pullback.snd ≫ p …
    -- Porting note : in the following two bullet points, `rfl` was not necessary
    · simp only [pullbackFstιToV_fst]; rfl
      -- ⊢ pullback.snd ≫ pullback.fst = pullback.snd ≫ pullback.fst
                                       -- 🎉 no goals
    · simp only [pullbackFstιToV_fst]; rfl
      -- ⊢ pullback.snd ≫ pullback.snd = pullback.snd ≫ pullback.snd
                                       -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.lift_comp_ι AlgebraicGeometry.Scheme.Pullback.lift_comp_ι

/-- The canonical isomorphism between `W ×[X] Uᵢ` and `Uᵢ ×[X] Y`. That is, the preimage of `Uᵢ` in
`W` along `p1` is indeed `Uᵢ ×[X] Y`. -/
def pullbackP1Iso (i : 𝒰.J) : pullback (p1 𝒰 f g) (𝒰.map i) ≅ pullback (𝒰.map i ≫ f) g := by
  fconstructor
  exact
    pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
      (by rw [← pullback.condition_assoc, Category.assoc, p_comm])
  refine' pullback.lift ((gluing 𝒰 f g).ι i) pullback.fst (by erw [Multicoequalizer.π_desc])
  -- ⊢ autoParam (pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pullbac …
  · apply pullback.hom_ext
    -- ⊢ (pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pullback.snd ≫ Op …
    · simpa using lift_comp_ι 𝒰 f g i
      -- 🎉 no goals
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
      -- 🎉 no goals
  · apply pullback.hom_ext
    -- ⊢ (pullback.lift (GlueData.ι (gluing 𝒰 f g) i) pullback.fst (_ : GlueData.ι (g …
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
      -- 🎉 no goals
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc, Category.id_comp]
      -- ⊢ GlueData.ι (gluing 𝒰 f g) i ≫ p2 𝒰 f g = pullback.snd
      erw [Multicoequalizer.π_desc]
      -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso

@[simp, reassoc]
theorem pullbackP1Iso_hom_fst (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.fst = pullback.snd := by
  delta pullbackP1Iso
  -- ⊢ (Iso.mk (pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pullback. …
  simp only [pullback.lift_fst]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_fst AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_fst

@[simp, reassoc]
theorem pullbackP1Iso_hom_snd (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.snd = pullback.fst ≫ p2 𝒰 f g := by
  delta pullbackP1Iso; simp only [pullback.lift_snd]
  -- ⊢ (Iso.mk (pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pullback. …
                       -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_snd AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_snd

@[simp, reassoc]
theorem pullbackP1Iso_inv_fst (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.fst = (gluing 𝒰 f g).ι i := by
  delta pullbackP1Iso; simp only [pullback.lift_fst]
  -- ⊢ (Iso.mk (pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pullback. …
                       -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_inv_fst AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_inv_fst

@[simp, reassoc]
theorem pullbackP1Iso_inv_snd (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.snd = pullback.fst := by
  delta pullbackP1Iso; simp only [pullback.lift_snd]
  -- ⊢ (Iso.mk (pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g) (_ : pullback. …
                       -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_inv_snd AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_inv_snd

@[simp, reassoc]
theorem pullbackP1Iso_hom_ι (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ (gluing 𝒰 f g).ι i = pullback.fst := by
  rw [← pullbackP1Iso_inv_fst, Iso.hom_inv_id_assoc]
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_ι AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_ι

/-- The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`. -/
def gluedIsLimit : IsLimit (PullbackCone.mk _ _ (p_comm 𝒰 f g)) := by
  apply PullbackCone.isLimitAux'
  -- ⊢ (s : PullbackCone f g) → { l // l ≫ PullbackCone.fst (PullbackCone.mk (p1 𝒰  …
  intro s
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (p1 𝒰 f g) (p2 𝒰 f g) (_ : p1 𝒰 …
  refine' ⟨gluedLift 𝒰 f g s, gluedLift_p1 𝒰 f g s, gluedLift_p2 𝒰 f g s, _⟩
  -- ⊢ ∀ {m : s.pt ⟶ (PullbackCone.mk (p1 𝒰 f g) (p2 𝒰 f g) (_ : p1 𝒰 f g ≫ f = p2  …
  intro m h₁ h₂
  -- ⊢ m = gluedLift 𝒰 f g s
  change m ≫ p1 𝒰 f g = _ at h₁
  -- ⊢ m = gluedLift 𝒰 f g s
  change m ≫ p2 𝒰 f g = _ at h₂
  -- ⊢ m = gluedLift 𝒰 f g s
  apply (𝒰.pullbackCover s.fst).hom_ext
  -- ⊢ ∀ (x : (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)).J), OpenCover.map (O …
  intro i
  -- ⊢ OpenCover.map (OpenCover.pullbackCover 𝒰 (PullbackCone.fst s)) i ≫ m = OpenC …
  rw [OpenCover.pullbackCover_map]
  -- ⊢ pullback.fst ≫ m = pullback.fst ≫ gluedLift 𝒰 f g s
  have := pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) m ≪≫ pullback.congrHom h₁ rfl
  -- ⊢ pullback.fst ≫ m = pullback.fst ≫ gluedLift 𝒰 f g s
  erw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  -- ⊢ pullback.fst ≫ m = (pullbackSymmetry (PullbackCone.fst s) (OpenCover.map 𝒰 i …
  rw [←
    cancel_epi
      (pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) m ≪≫ pullback.congrHom h₁ rfl).hom,
    Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
    Category.comp_id, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  trans pullback.snd ≫ (pullbackP1Iso 𝒰 f g _).hom ≫ (gluing 𝒰 f g).ι _
  -- ⊢ pullback.snd ≫ pullback.fst = pullback.snd ≫ (pullbackP1Iso 𝒰 f g i).hom ≫ G …
  · congr 1; rw [← pullbackP1Iso_hom_ι]
    -- ⊢ pullback.fst = (pullbackP1Iso 𝒰 f g i).hom ≫ GlueData.ι (gluing 𝒰 f g) i
             -- 🎉 no goals
  simp_rw [← Category.assoc]
  -- ⊢ (pullback.snd ≫ (pullbackP1Iso 𝒰 f g i).hom) ≫ GlueData.ι (gluing 𝒰 f g) i = …
  congr 1
  -- ⊢ pullback.snd ≫ (pullbackP1Iso 𝒰 f g i).hom = (((pullbackRightPullbackFstIso  …
  apply pullback.hom_ext
  -- ⊢ (pullback.snd ≫ (pullbackP1Iso 𝒰 f g i).hom) ≫ pullback.fst = ((((pullbackRi …
  · simp only [Category.comp_id, pullbackRightPullbackFstIso_hom_snd, Category.assoc,
      pullbackP1Iso_hom_fst, pullback.lift_snd, pullback.lift_fst, pullbackSymmetry_hom_comp_fst]
  · simp only [Category.comp_id, pullbackRightPullbackFstIso_hom_fst_assoc,
      pullbackP1Iso_hom_snd, Category.assoc, pullback.lift_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_snd]
    rw [← pullback.condition_assoc, h₂]
    -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.glued_is_limit AlgebraicGeometry.Scheme.Pullback.gluedIsLimit

theorem hasPullback_of_cover : HasPullback f g :=
  ⟨⟨⟨_, gluedIsLimit 𝒰 f g⟩⟩⟩
#align algebraic_geometry.Scheme.pullback.has_pullback_of_cover AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover

instance affine_hasPullback {A B C : CommRingCat}
    (f : Spec.obj (Opposite.op A) ⟶ Spec.obj (Opposite.op C))
    (g : Spec.obj (Opposite.op B) ⟶ Spec.obj (Opposite.op C)) : HasPullback f g := by
  rw [← Spec.image_preimage f, ← Spec.image_preimage g]
  -- ⊢ HasPullback (Spec.map (Spec.preimage f)) (Spec.map (Spec.preimage g))
  exact
    ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit Spec (Spec.preimage f) (Spec.preimage g)⟩⟩⟩
#align algebraic_geometry.Scheme.pullback.affine_has_pullback AlgebraicGeometry.Scheme.Pullback.affine_hasPullback

theorem affine_affine_hasPullback {B C : CommRingCat} {X : Scheme}
    (f : X ⟶ Spec.obj (Opposite.op C)) (g : Spec.obj (Opposite.op B) ⟶ Spec.obj (Opposite.op C)) :
    HasPullback f g :=
  hasPullback_of_cover X.affineCover f g
#align algebraic_geometry.Scheme.pullback.affine_affine_has_pullback AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback

instance base_affine_hasPullback {C : CommRingCat} {X Y : Scheme} (f : X ⟶ Spec.obj (Opposite.op C))
    (g : Y ⟶ Spec.obj (Opposite.op C)) : HasPullback f g :=
  @hasPullback_symmetry _ _ _ _ _ _ _
    (@hasPullback_of_cover _ _ _ Y.affineCover g f fun _ =>
      @hasPullback_symmetry _ _ _ _ _ _ _ <| affine_affine_hasPullback _ _)
#align algebraic_geometry.Scheme.pullback.base_affine_has_pullback AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback

instance left_affine_comp_pullback_hasPullback {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (i : Z.affineCover.J) : HasPullback ((Z.affineCover.pullbackCover f).map i ≫ f) g := by
  let Xᵢ := pullback f (Z.affineCover.map i)
  -- ⊢ HasPullback (OpenCover.map (OpenCover.pullbackCover (affineCover Z) f) i ≫ f …
  let Yᵢ := pullback g (Z.affineCover.map i)
  -- ⊢ HasPullback (OpenCover.map (OpenCover.pullbackCover (affineCover Z) f) i ≫ f …
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
  -- ⊢ HasPullback (OpenCover.map (OpenCover.pullbackCover (affineCover Z) f) i ≫ f …
  have :=
    bigSquareIsPullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
      (Z.affineCover.map i) pullback.snd pullback.snd g pullback.condition.symm
      pullback.condition.symm (PullbackCone.flipIsLimit <| pullbackIsPullback _ _)
      (PullbackCone.flipIsLimit <| pullbackIsPullback _ _)
  have : HasPullback (pullback.snd ≫ Z.affineCover.map i : Xᵢ ⟶ _) g := ⟨⟨⟨_, this⟩⟩⟩
  -- ⊢ HasPullback (OpenCover.map (OpenCover.pullbackCover (affineCover Z) f) i ≫ f …
  rw [← pullback.condition] at this
  -- ⊢ HasPullback (OpenCover.map (OpenCover.pullbackCover (affineCover Z) f) i ≫ f …
  exact this
  -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.left_affine_comp_pullback_HasPullback AlgebraicGeometry.Scheme.Pullback.left_affine_comp_pullback_hasPullback

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  hasPullback_of_cover (Z.affineCover.pullbackCover f) f g

instance : HasPullbacks Scheme :=
  hasPullbacks_of_hasLimit_cospan _

instance isAffine_of_isAffine_isAffine_isAffine {X Y Z : Scheme}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback f g) :=
  isAffineOfIso
    (pullback.map f g (Spec.map (Γ.map f.op).op) (Spec.map (Γ.map g.op).op)
        (ΓSpec.adjunction.unit.app X) (ΓSpec.adjunction.unit.app Y) (ΓSpec.adjunction.unit.app Z)
        (ΓSpec.adjunction.unit.naturality f) (ΓSpec.adjunction.unit.naturality g) ≫
      (PreservesPullback.iso Spec _ _).inv)

/-- Given an open cover `{ Xᵢ }` of `X`, then `X ×[Z] Y` is covered by `Xᵢ ×[Z] Y`. -/
@[simps! J obj map]
def openCoverOfLeft (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  fapply
    ((gluing 𝒰 f g).openCover.pushforwardIso
          (limit.isoLimitCone ⟨_, gluedIsLimit 𝒰 f g⟩).inv).copy
      𝒰.J (fun i => pullback (𝒰.map i ≫ f) g)
      (fun i => pullback.map _ _ _ _ (𝒰.map i) (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp))
      (Equiv.refl 𝒰.J) fun _ => Iso.refl _
  rintro (i : 𝒰.J)
  -- ⊢ pullback.map (OpenCover.map 𝒰 i ≫ f) g f g (OpenCover.map 𝒰 i) (𝟙 Y) (𝟙 Z) ( …
  change pullback.map _ _ _ _ _ _ _ _ _ = 𝟙 _ ≫ (gluing 𝒰 f g).ι i ≫ _
  -- ⊢ pullback.map (OpenCover.map 𝒰 i ≫ f) g f g (OpenCover.map 𝒰 i) (𝟙 Y) (𝟙 Z) ( …
  refine' Eq.trans _ (Category.id_comp _).symm
  -- ⊢ pullback.map (OpenCover.map 𝒰 i ≫ f) g f g (OpenCover.map 𝒰 i) (𝟙 Y) (𝟙 Z) ( …
  apply pullback.hom_ext
  -- ⊢ pullback.map (OpenCover.map 𝒰 i ≫ f) g f g (OpenCover.map 𝒰 i) (𝟙 Y) (𝟙 Z) ( …
  all_goals
    dsimp
    simp only [limit.isoLimitCone_inv_π, PullbackCone.mk_π_app_left, Category.comp_id,
      PullbackCone.mk_π_app_right, Category.assoc, pullback.lift_fst, pullback.lift_snd]
    symm
    exact Multicoequalizer.π_desc _ _ _ _ _
#align algebraic_geometry.Scheme.pullback.open_cover_of_left AlgebraicGeometry.Scheme.Pullback.openCoverOfLeft

/-- Given an open cover `{ Yᵢ }` of `Y`, then `X ×[Z] Y` is covered by `X ×[Z] Yᵢ`. -/
@[simps! J obj map]
def openCoverOfRight (𝒰 : OpenCover Y) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  fapply
    ((openCoverOfLeft 𝒰 g f).pushforwardIso (pullbackSymmetry _ _).hom).copy 𝒰.J
      (fun i => pullback f (𝒰.map i ≫ g))
      (fun i => pullback.map _ _ _ _ (𝟙 _) (𝒰.map i) (𝟙 _) (by simp) (Category.comp_id _))
      (Equiv.refl _) fun i => pullbackSymmetry _ _
  intro i
  -- ⊢ pullback.map f (OpenCover.map 𝒰 i ≫ g) f g (𝟙 X) (OpenCover.map 𝒰 i) (𝟙 Z) ( …
  dsimp [OpenCover.bind]
  -- ⊢ pullback.map f (OpenCover.map 𝒰 i ≫ g) f g (𝟙 X) (OpenCover.map 𝒰 i) (𝟙 Z) ( …
  apply pullback.hom_ext <;> simp
  -- ⊢ pullback.map f (OpenCover.map 𝒰 i ≫ g) f g (𝟙 X) (OpenCover.map 𝒰 i) (𝟙 Z) ( …
                             -- 🎉 no goals
                             -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.open_cover_of_right AlgebraicGeometry.Scheme.Pullback.openCoverOfRight

/-- Given an open cover `{ Xᵢ }` of `X` and an open cover `{ Yⱼ }` of `Y`, then
`X ×[Z] Y` is covered by `Xᵢ ×[Z] Yⱼ`. -/
@[simps! J obj map]
def openCoverOfLeftRight (𝒰X : X.OpenCover) (𝒰Y : Y.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).OpenCover := by
  fapply
    ((openCoverOfLeft 𝒰X f g).bind fun x => openCoverOfRight 𝒰Y (𝒰X.map x ≫ f) g).copy
      (𝒰X.J × 𝒰Y.J) (fun ij => pullback (𝒰X.map ij.1 ≫ f) (𝒰Y.map ij.2 ≫ g))
      (fun ij =>
        pullback.map _ _ _ _ (𝒰X.map ij.1) (𝒰Y.map ij.2) (𝟙 _) (Category.comp_id _)
          (Category.comp_id _))
      (Equiv.sigmaEquivProd _ _).symm fun _ => Iso.refl _
  rintro ⟨i, j⟩
  -- ⊢ pullback.map (OpenCover.map 𝒰X (i, j).fst ≫ f) (OpenCover.map 𝒰Y (i, j).snd  …
  apply pullback.hom_ext <;> simp
  -- ⊢ pullback.map (OpenCover.map 𝒰X (i, j).fst ≫ f) (OpenCover.map 𝒰Y (i, j).snd  …
                             -- 🎉 no goals
                             -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.open_cover_of_left_right AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight

/-- (Implementation). Use `openCoverOfBase` instead. -/
@[simps! map]
def openCoverOfBase' (𝒰 : OpenCover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  apply (openCoverOfLeft (𝒰.pullbackCover f) f g).bind
  -- ⊢ (x : (openCoverOfLeft (OpenCover.pullbackCover 𝒰 f) f g).J) → OpenCover (Ope …
  intro i
  -- ⊢ OpenCover (OpenCover.obj (openCoverOfLeft (OpenCover.pullbackCover 𝒰 f) f g) …
  let Xᵢ := pullback f (𝒰.map i)
  -- ⊢ OpenCover (OpenCover.obj (openCoverOfLeft (OpenCover.pullbackCover 𝒰 f) f g) …
  let Yᵢ := pullback g (𝒰.map i)
  -- ⊢ OpenCover (OpenCover.obj (openCoverOfLeft (OpenCover.pullbackCover 𝒰 f) f g) …
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
  -- ⊢ OpenCover (OpenCover.obj (openCoverOfLeft (OpenCover.pullbackCover 𝒰 f) f g) …
  have :=
    bigSquareIsPullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
      (𝒰.map i) pullback.snd pullback.snd g pullback.condition.symm pullback.condition.symm
      (PullbackCone.flipIsLimit <| pullbackIsPullback _ _)
      (PullbackCone.flipIsLimit <| pullbackIsPullback _ _)
  refine'
    @openCoverOfIsIso
      (f := (pullbackSymmetry _ _).hom ≫
        (limit.isoLimitCone ⟨_, this⟩).inv ≫ pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _) ?_
  · simp only [Category.comp_id, Category.id_comp, ← pullback.condition]
    -- ⊢ pullback.fst ≫ f = OpenCover.map (OpenCover.pullbackCover 𝒰 f) i ≫ f
    -- Porting note : `simpa` failed, but this is indeed `rfl`
    rfl
    -- 🎉 no goals
  · simp only [Category.comp_id, Category.id_comp]
    -- 🎉 no goals
  -- Porting note : this `IsIso` instance was `inferInstance`
  · apply IsIso.comp_isIso
    -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.open_cover_of_base' AlgebraicGeometry.Scheme.Pullback.openCoverOfBase'

/-- Given an open cover `{ Zᵢ }` of `Z`, then `X ×[Z] Y` is covered by `Xᵢ ×[Zᵢ] Yᵢ`, where
  `Xᵢ = X ×[Z] Zᵢ` and `Yᵢ = Y ×[Z] Zᵢ` is the preimage of `Zᵢ` in `X` and `Y`. -/
@[simps! J obj map]
def openCoverOfBase (𝒰 : OpenCover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  apply
    (openCoverOfBase'.{u, u} 𝒰 f g).copy 𝒰.J
      (fun i =>
        pullback (pullback.snd : pullback f (𝒰.map i) ⟶ _)
          (pullback.snd : pullback g (𝒰.map i) ⟶ _))
      (fun i =>
        pullback.map _ _ _ _ pullback.fst pullback.fst (𝒰.map i) pullback.condition.symm
          pullback.condition.symm)
      ((Equiv.prodPUnit 𝒰.J).symm.trans (Equiv.sigmaEquivProd 𝒰.J PUnit).symm) fun _ => Iso.refl _
  intro i
  -- ⊢ pullback.map pullback.snd pullback.snd f g pullback.fst pullback.fst (OpenCo …
  -- Porting note : deviated from original proof a bit so that it won't timeout.
  rw [Iso.refl_hom, Category.id_comp, openCoverOfBase'_map]
  -- ⊢ pullback.map pullback.snd pullback.snd f g pullback.fst pullback.fst (OpenCo …
  apply pullback.hom_ext <;> dsimp <;>
  -- ⊢ pullback.map pullback.snd pullback.snd f g pullback.fst pullback.fst (OpenCo …
                             -- ⊢ pullback.map pullback.snd pullback.snd f g pullback.fst pullback.fst (OpenCo …
                             -- ⊢ pullback.map pullback.snd pullback.snd f g pullback.fst pullback.fst (OpenCo …
  · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.assoc,
      limit.lift_π_assoc, cospan_left, Category.comp_id, limit.isoLimitCone_inv_π,
      limit.isoLimitCone_inv_π_assoc, pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc]
    rfl
    -- 🎉 no goals
    -- 🎉 no goals
#align algebraic_geometry.Scheme.pullback.open_cover_of_base AlgebraicGeometry.Scheme.Pullback.openCoverOfBase

end Pullback

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

instance Scheme.pullback_map_isOpenImmersion {X Y S X' Y' S' : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] [Mono i₃] :
    IsOpenImmersion (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) := by
  rw [pullback_map_eq_pullbackFstFstIso_inv]
  -- ⊢ IsOpenImmersion ((pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback …
  -- Porting note : was automatic
  exact PresheafedSpace.IsOpenImmersion.comp _ (hg := PresheafedSpace.IsOpenImmersion.comp _ _)
  -- 🎉 no goals

end AlgebraicGeometry
