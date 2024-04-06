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
  refine' (pullbackAssoc _ _ _ _).inv ≫ _
  change pullback _ _ ⟶ pullback _ _
  refine' _ ≫ (pullbackSymmetry _ _).hom
  refine' _ ≫ (pullbackAssoc _ _ _ _).hom
  refine' pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) _ _
  rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition_assoc, Category.comp_id]
  rw [Category.comp_id, Category.id_comp]
#align algebraic_geometry.Scheme.pullback.t AlgebraicGeometry.Scheme.Pullback.t

@[simp, reassoc]
theorem t_fst_fst (i j : 𝒰.J) : t 𝒰 f g i j ≫ pullback.fst ≫ pullback.fst = pullback.snd := by
  delta t
  -- Porting note: copied from previous definition, otherwise `simp` wouldn't work
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
  -- Porting note: copied from previous definition, otherwise `simp` wouldn't work
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
  -- Porting note: copied from previous definition, otherwise `simp` wouldn't work
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
  apply pullback.hom_ext
  · rw [← cancel_mono (𝒰.map i)]; simp only [pullback.condition, Category.assoc, t_fst_fst]
  · simp only [Category.assoc, t_fst_snd]
  · rw [← cancel_mono (𝒰.map i)]; simp only [pullback.condition, t_snd, Category.assoc]
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
  refine' _ ≫ (pullbackSymmetry _ _).hom
  refine' _ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine' pullback.map _ _ _ _ (t 𝒰 f g i j) (𝟙 _) (𝟙 _) _ _
  · simp only [← pullback.condition, Category.comp_id, t_fst_fst_assoc]
  · simp only [Category.comp_id, Category.id_comp]
#align algebraic_geometry.Scheme.pullback.t' AlgebraicGeometry.Scheme.Pullback.t'

@[simp, reassoc]
theorem t'_fst_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta t'
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_fst_fst_fst AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_fst

@[simp, reassoc]
theorem t'_fst_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst ≫ pullback.snd := by
  delta t'
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_fst_fst_snd AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_snd

@[simp, reassoc]
theorem t'_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta t'
  simp only [Category.comp_id, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd,
    pullbackRightPullbackFstIso_hom_snd]
#align algebraic_geometry.Scheme.pullback.t'_fst_snd AlgebraicGeometry.Scheme.Pullback.t'_fst_snd

@[simp, reassoc]
theorem t'_snd_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta t'
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_snd_fst_fst AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_fst

@[simp, reassoc]
theorem t'_snd_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst ≫ pullback.snd := by
  delta t'
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_snd_fst_snd AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_snd

@[simp, reassoc]
theorem t'_snd_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst := by
  delta t'
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
#align algebraic_geometry.Scheme.pullback.t'_snd_snd AlgebraicGeometry.Scheme.Pullback.t'_snd_snd

theorem cocycle_fst_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst =
      pullback.fst ≫ pullback.fst ≫ pullback.fst :=
  by simp only [t'_fst_fst_fst, t'_fst_snd, t'_snd_snd]
#align algebraic_geometry.Scheme.pullback.cocycle_fst_fst_fst AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_fst

theorem cocycle_fst_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.fst ≫ pullback.snd :=
  by simp only [t'_fst_fst_snd]
#align algebraic_geometry.Scheme.pullback.cocycle_fst_fst_snd AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_snd

theorem cocycle_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.snd =
      pullback.fst ≫ pullback.snd :=
  by simp only [t'_fst_snd, t'_snd_snd, t'_fst_fst_fst]
#align algebraic_geometry.Scheme.pullback.cocycle_fst_snd AlgebraicGeometry.Scheme.Pullback.cocycle_fst_snd

theorem cocycle_snd_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst =
      pullback.snd ≫ pullback.fst ≫ pullback.fst := by
  rw [← cancel_mono (𝒰.map i)]
  simp only [pullback.condition_assoc, t'_snd_fst_fst, t'_fst_snd, t'_snd_snd]
#align algebraic_geometry.Scheme.pullback.cocycle_snd_fst_fst AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_fst

theorem cocycle_snd_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
      pullback.snd ≫ pullback.fst ≫ pullback.snd :=
  by simp only [pullback.condition_assoc, t'_snd_fst_snd]
#align algebraic_geometry.Scheme.pullback.cocycle_snd_fst_snd AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_snd

theorem cocycle_snd_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.snd =
      pullback.snd ≫ pullback.snd :=
  by simp only [t'_snd_snd, t'_fst_fst_fst, t'_fst_snd]
#align algebraic_geometry.Scheme.pullback.cocycle_snd_snd AlgebraicGeometry.Scheme.Pullback.cocycle_snd_snd

-- `by tidy` should solve it, but it times out.
theorem cocycle (i j k : 𝒰.J) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc]
        exact cocycle_fst_fst_fst 𝒰 f g i j k
      · simp_rw [Category.assoc]
        exact cocycle_fst_fst_snd 𝒰 f g i j k
    · simp_rw [Category.assoc]
      exact cocycle_fst_snd 𝒰 f g i j k
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc]
        exact cocycle_snd_fst_fst 𝒰 f g i j k
      · simp_rw [Category.assoc]
        exact cocycle_snd_fst_snd 𝒰 f g i j k
    · simp_rw [Category.assoc]
      exact cocycle_snd_snd 𝒰 f g i j k
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
    apply pullback.hom_ext
    all_goals
      simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd, t_fst_fst, t_fst_snd, t_snd,
        Category.assoc]
  cocycle i j k := cocycle 𝒰 f g i j k
#align algebraic_geometry.Scheme.pullback.gluing AlgebraicGeometry.Scheme.Pullback.gluing

/-- The first projection from the glued scheme into `X`. -/
def p1 : (gluing 𝒰 f g).glued ⟶ X := by
  fapply Multicoequalizer.desc
  exact fun i => pullback.fst ≫ 𝒰.map i
  rintro ⟨i, j⟩
  change pullback.fst ≫ _ ≫ 𝒰.map i = (_ ≫ _) ≫ _ ≫ 𝒰.map j
  -- Porting note (#11224): change `rw` to `erw`
  erw [pullback.condition]
  rw [← Category.assoc]
  congr 1
  rw [Category.assoc]
  exact (t_fst_fst _ _ _ _ _).symm
#align algebraic_geometry.Scheme.pullback.p1 AlgebraicGeometry.Scheme.Pullback.p1

/-- The second projection from the glued scheme into `Y`. -/
def p2 : (gluing 𝒰 f g).glued ⟶ Y := by
  fapply Multicoequalizer.desc
  exact fun i => pullback.snd
  rintro ⟨i, j⟩
  change pullback.fst ≫ _ = (_ ≫ _) ≫ _
  rw [Category.assoc]
  exact (t_fst_snd _ _ _ _ _).symm
#align algebraic_geometry.Scheme.pullback.p2 AlgebraicGeometry.Scheme.Pullback.p2

theorem p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g := by
  apply Multicoequalizer.hom_ext
  intro i
  erw [Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  rw [Category.assoc, pullback.condition]
#align algebraic_geometry.Scheme.pullback.p_comm AlgebraicGeometry.Scheme.Pullback.p_comm

variable (s : PullbackCone f g)

/-- (Implementation)
The canonical map `(s.X ×[X] Uᵢ) ×[s.X] (s.X ×[X] Uⱼ) ⟶ (Uᵢ ×[Z] Y) ×[X] Uⱼ`

This is used in `gluedLift`. -/
def gluedLiftPullbackMap (i j : 𝒰.J) :
    pullback ((𝒰.pullbackCover s.fst).map i) ((𝒰.pullbackCover s.fst).map j) ⟶
      (gluing 𝒰 f g).V ⟨i, j⟩ := by
  change pullback pullback.fst pullback.fst ⟶ pullback _ _
  refine' (pullbackRightPullbackFstIso _ _ _).hom ≫ _
  refine' pullback.map _ _ _ _ _ (𝟙 _) (𝟙 _) _ _
  · exact (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition
  · simpa using pullback.condition
  · simp only [Category.comp_id, Category.id_comp]
#align algebraic_geometry.Scheme.pullback.glued_lift_pullback_map AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap

@[reassoc]
theorem gluedLiftPullbackMap_fst (i j : 𝒰.J) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.fst =
      pullback.fst ≫
        (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition := by
  delta gluedLiftPullbackMap
  -- Porting note: the original set of simp lemma is not sufficient, but as this is terminal
  -- I just let `simp` do its work
  simp
#align algebraic_geometry.Scheme.pullback.glued_lift_pullback_map_fst AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap_fst

@[reassoc]
theorem gluedLiftPullbackMap_snd (i j : 𝒰.J) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta gluedLiftPullbackMap
  -- Porting note: the original set of simp lemma is not sufficient, but as this is terminal
  -- I just let `simp` do its work
  simp
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
  · exact fun i => (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition ≫
        (gluing 𝒰 f g).ι i
  intro i j
  rw [← gluedLiftPullbackMap_fst_assoc]
  have : _ = pullback.fst ≫ _ := (gluing 𝒰 f g).glue_condition i j
  rw [← this, gluing_t, gluing_f]
  simp_rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp_rw [Category.assoc]
  · rw [t_fst_fst, gluedLiftPullbackMap_snd]
    congr 1
    rw [← Iso.inv_comp_eq, pullbackSymmetry_inv_comp_snd]
    erw [pullback.lift_fst]
    rw [Category.comp_id]
  · rw [t_fst_snd, gluedLiftPullbackMap_fst_assoc]
    erw [pullback.lift_snd, pullback.lift_snd]
    rw [pullbackSymmetry_hom_comp_snd_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    exact pullback.condition_assoc _
#align algebraic_geometry.Scheme.pullback.glued_lift AlgebraicGeometry.Scheme.Pullback.gluedLift

theorem gluedLift_p1 : gluedLift 𝒰 f g s ≫ p1 𝒰 f g = s.fst := by
  rw [← cancel_epi (𝒰.pullbackCover s.fst).fromGlued]
  apply Multicoequalizer.hom_ext
  intro b
  erw [Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  delta gluedLift
  simp_rw [← Category.assoc]
  rw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  simp_rw [Category.assoc]
  -- Porting note: `Category.comp_id` is no longer necessary, don't know where `𝟙 _` has gone
  erw [Multicoequalizer.π_desc, pullback.lift_fst_assoc, pullback.condition]
  rw [pullbackSymmetry_hom_comp_snd_assoc]
  rfl
#align algebraic_geometry.Scheme.pullback.glued_lift_p1 AlgebraicGeometry.Scheme.Pullback.gluedLift_p1

theorem gluedLift_p2 : gluedLift 𝒰 f g s ≫ p2 𝒰 f g = s.snd := by
  rw [← cancel_epi (𝒰.pullbackCover s.fst).fromGlued]
  apply Multicoequalizer.hom_ext
  intro b
  erw [Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc_assoc]
  delta gluedLift
  simp_rw [← Category.assoc]
  rw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  simp_rw [Category.assoc]
  erw [Multicoequalizer.π_desc, pullback.lift_snd]
  rw [pullbackSymmetry_hom_comp_snd_assoc]
  rfl
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
  simp only [Iso.trans_hom, pullback.congrHom_hom, Category.assoc, pullback.lift_fst,
    Category.comp_id]
  -- Porting note: `pullbackRightPullbackFstIso_hom_fst` is not used in `simp` even though
  -- instructed, forcing `pullbackSymmetry_hom_comp_fst` to be manually `rw`ed as well.
  erw [pullbackRightPullbackFstIso_hom_fst]
  rw [pullbackSymmetry_hom_comp_fst]
#align algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V_fst AlgebraicGeometry.Scheme.Pullback.pullbackFstιToV_fst

@[simp, reassoc]
theorem pullbackFstιToV_snd (i j : 𝒰.J) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.snd = pullback.fst ≫ pullback.snd := by
  delta pullbackFstιToV
  simp only [Iso.trans_hom, pullback.congrHom_hom, Category.assoc, pullback.lift_snd,
    Category.comp_id]
  -- Porting note: `pullbackRightPullbackFstIso_hom_snd` is not used in `simp` even though
  -- instructed, forcing `pullbackSymmetry_hom_comp_snd_assoc` to be manually `rw`ed as well.
  erw [pullbackRightPullbackFstIso_hom_snd]
  rw [pullbackSymmetry_hom_comp_snd_assoc]
#align algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V_snd AlgebraicGeometry.Scheme.Pullback.pullbackFstιToV_snd

/-- We show that the map `W ×[X] Uᵢ ⟶ Uᵢ ×[Z] Y ⟶ W` is the first projection, where the
first map is given by the lift of `W ×[X] Uᵢ ⟶ Uᵢ` and `W ×[X] Uᵢ ⟶ W ⟶ Y`.

It suffices to show that the two map agrees when restricted onto `Uⱼ ×[Z] Y`. In this case,
both maps factor through `V j i` via `pullback_fst_ι_to_V` -/
theorem lift_comp_ι (i : 𝒰.J) :
    pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
          (by rw [← pullback.condition_assoc, Category.assoc, p_comm]) ≫
        (gluing 𝒰 f g).ι i =
      (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map i) ⟶ _) := by
  apply ((gluing 𝒰 f g).openCover.pullbackCover pullback.fst).hom_ext
  intro j
  dsimp only [OpenCover.pullbackCover]
  trans pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i ≫ (gluing 𝒰 f g).ι _
  · rw [← show _ = fV 𝒰 f g j i ≫ _ from (gluing 𝒰 f g).glue_condition j i]
    simp_rw [← Category.assoc]
    congr 1
    rw [gluing_f, gluing_t]
    apply pullback.hom_ext <;> simp_rw [Category.assoc]
    -- Porting note: in the following two bullet points, `rfl` was not necessary
    · rw [t_fst_fst, pullback.lift_fst, pullbackFstιToV_snd]; rfl
    · rw [t_fst_snd, pullback.lift_snd, pullbackFstιToV_fst_assoc, pullback.condition_assoc]
      erw [Multicoequalizer.π_desc]
      rfl
  · rw [pullback.condition, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    -- Porting note: in the following two bullet points, `rfl` was not necessary
    · simp only [pullbackFstιToV_fst]; rfl
    · simp only [pullbackFstιToV_fst]; rfl
#align algebraic_geometry.Scheme.pullback.lift_comp_ι AlgebraicGeometry.Scheme.Pullback.lift_comp_ι

/-- The canonical isomorphism between `W ×[X] Uᵢ` and `Uᵢ ×[X] Y`. That is, the preimage of `Uᵢ` in
`W` along `p1` is indeed `Uᵢ ×[X] Y`. -/
def pullbackP1Iso (i : 𝒰.J) : pullback (p1 𝒰 f g) (𝒰.map i) ≅ pullback (𝒰.map i ≫ f) g := by
  fconstructor
  exact
    pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
      (by rw [← pullback.condition_assoc, Category.assoc, p_comm])
  refine' pullback.lift ((gluing 𝒰 f g).ι i) pullback.fst (by erw [Multicoequalizer.π_desc])
  · apply pullback.hom_ext
    · simpa using lift_comp_ι 𝒰 f g i
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc, Category.id_comp]
      erw [Multicoequalizer.π_desc]
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso

@[simp, reassoc]
theorem pullbackP1Iso_hom_fst (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.fst = pullback.snd := by
  delta pullbackP1Iso
  simp only [pullback.lift_fst]
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_fst AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_fst

@[simp, reassoc]
theorem pullbackP1Iso_hom_snd (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.snd = pullback.fst ≫ p2 𝒰 f g := by
  delta pullbackP1Iso; simp only [pullback.lift_snd]
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_snd AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_snd

@[simp, reassoc]
theorem pullbackP1Iso_inv_fst (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.fst = (gluing 𝒰 f g).ι i := by
  delta pullbackP1Iso; simp only [pullback.lift_fst]
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_inv_fst AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_inv_fst

@[simp, reassoc]
theorem pullbackP1Iso_inv_snd (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.snd = pullback.fst := by
  delta pullbackP1Iso; simp only [pullback.lift_snd]
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_inv_snd AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_inv_snd

@[simp, reassoc]
theorem pullbackP1Iso_hom_ι (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ (gluing 𝒰 f g).ι i = pullback.fst := by
  rw [← pullbackP1Iso_inv_fst, Iso.hom_inv_id_assoc]
#align algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_ι AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_ι

/-- The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`. -/
def gluedIsLimit : IsLimit (PullbackCone.mk _ _ (p_comm 𝒰 f g)) := by
  apply PullbackCone.isLimitAux'
  intro s
  refine' ⟨gluedLift 𝒰 f g s, gluedLift_p1 𝒰 f g s, gluedLift_p2 𝒰 f g s, _⟩
  intro m h₁ h₂
  change m ≫ p1 𝒰 f g = _ at h₁
  change m ≫ p2 𝒰 f g = _ at h₂
  apply (𝒰.pullbackCover s.fst).hom_ext
  intro i
  rw [OpenCover.pullbackCover_map]
  have := pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) m ≪≫ pullback.congrHom h₁ rfl
  erw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  rw [←
    cancel_epi
      (pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) m ≪≫ pullback.congrHom h₁ rfl).hom,
    Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
    Category.comp_id, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  trans pullback.snd ≫ (pullbackP1Iso 𝒰 f g _).hom ≫ (gluing 𝒰 f g).ι _
  · congr 1; rw [← pullbackP1Iso_hom_ι]
  simp_rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.comp_id, pullbackRightPullbackFstIso_hom_snd, Category.assoc,
      pullbackP1Iso_hom_fst, pullback.lift_snd, pullback.lift_fst, pullbackSymmetry_hom_comp_fst]
  · simp only [Category.comp_id, pullbackRightPullbackFstIso_hom_fst_assoc,
      pullbackP1Iso_hom_snd, Category.assoc, pullback.lift_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_snd]
    rw [← pullback.condition_assoc, h₂]
#align algebraic_geometry.Scheme.pullback.glued_is_limit AlgebraicGeometry.Scheme.Pullback.gluedIsLimit

theorem hasPullback_of_cover : HasPullback f g :=
  ⟨⟨⟨_, gluedIsLimit 𝒰 f g⟩⟩⟩
#align algebraic_geometry.Scheme.pullback.has_pullback_of_cover AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover

instance affine_hasPullback {A B C : CommRingCat}
    (f : Spec.obj (Opposite.op A) ⟶ Spec.obj (Opposite.op C))
    (g : Spec.obj (Opposite.op B) ⟶ Spec.obj (Opposite.op C)) : HasPullback f g := by
  rw [← Spec.image_preimage f, ← Spec.image_preimage g]
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
  let Yᵢ := pullback g (Z.affineCover.map i)
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
  have :=
    bigSquareIsPullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
      (Z.affineCover.map i) pullback.snd pullback.snd g pullback.condition.symm
      pullback.condition.symm (PullbackCone.isLimitOfFlip <| pullbackIsPullback _ _)
      (PullbackCone.isLimitOfFlip <| pullbackIsPullback _ _)
  have : HasPullback (pullback.snd ≫ Z.affineCover.map i : Xᵢ ⟶ _) g := ⟨⟨⟨_, this⟩⟩⟩
  rw [← pullback.condition] at this
  exact this
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
  change pullback.map _ _ _ _ _ _ _ _ _ = 𝟙 _ ≫ (gluing 𝒰 f g).ι i ≫ _
  refine' Eq.trans _ (Category.id_comp _).symm
  apply pullback.hom_ext
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
  dsimp [OpenCover.bind]
  apply pullback.hom_ext <;> simp
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
  apply pullback.hom_ext <;> simp
#align algebraic_geometry.Scheme.pullback.open_cover_of_left_right AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight

/-- (Implementation). Use `openCoverOfBase` instead. -/
@[simps! map]
def openCoverOfBase' (𝒰 : OpenCover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  apply (openCoverOfLeft (𝒰.pullbackCover f) f g).bind
  intro i
  let Xᵢ := pullback f (𝒰.map i)
  let Yᵢ := pullback g (𝒰.map i)
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
  have :=
    bigSquareIsPullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _)
      (𝒰.map i) pullback.snd pullback.snd g pullback.condition.symm pullback.condition.symm
      (PullbackCone.isLimitOfFlip <| pullbackIsPullback _ _)
      (PullbackCone.isLimitOfFlip <| pullbackIsPullback _ _)
  refine'
    @openCoverOfIsIso
      (f := (pullbackSymmetry _ _).hom ≫
        (limit.isoLimitCone ⟨_, this⟩).inv ≫ pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _) ?_
  · simp only [Category.comp_id, Category.id_comp, ← pullback.condition]
    -- Porting note: `simpa` failed, but this is indeed `rfl`
    rfl
  · simp only [Category.comp_id, Category.id_comp]
  -- Porting note: this `IsIso` instance was `inferInstance`
  · apply IsIso.comp_isIso
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
  -- Porting note: deviated from original proof a bit so that it won't timeout.
  rw [Iso.refl_hom, Category.id_comp, openCoverOfBase'_map]
  apply pullback.hom_ext <;> dsimp <;>
  · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.assoc,
      limit.lift_π_assoc, cospan_left, Category.comp_id, limit.isoLimitCone_inv_π,
      limit.isoLimitCone_inv_π_assoc, pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc]
    rfl
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
  -- Porting note: was automatic
  exact PresheafedSpace.IsOpenImmersion.comp _ (hg := PresheafedSpace.IsOpenImmersion.comp _ _)

end AlgebraicGeometry
